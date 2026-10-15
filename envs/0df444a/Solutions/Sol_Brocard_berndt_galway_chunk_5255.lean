-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5255
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:15:44.986167+00:00
-- url     : https://prove2.me/submissions/4f1dc0c7-bbfd-4e0c-b374-3e5f5d452ed2

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 944964028 ≤ n < 945143884 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 944965278 1250 944964028 944964073
    0x610140403030516060e0c0f030f0601090b060706092d050c011404030210020709050c0f04051c021005130f08251a0309120c1b130203040b1008 63
    0x41c100f00340060750501445454400452803984417800b00000c24480ca0500c0d25011441c43ca80e1141100c3c48090140307180c0010802c0a002044001d40035036480d2031032550082c0001e202c80c942100003031203500c012840d2482884212070044081001040210100100e5000803c0069100d07022040c0414046040001c200d000c40c403003800c01c6078807031000741c440001500640c0d00003544402c0c50300c8200501075010134003400300c7d01d4080d014032a03a1501c201d101c101d4018100c0800890808cc00100300600d00020940030000da14150b10a101c1c509030045408062404920004258009101d020105032071002000611a40206000c05401c01038002c0e04c0701c3c4600c4d6144c2c0c5041c0402c0c80c004020400e0003400009001c0c151003290b80715036103e220170081d0402c64180c0240c1c02629a0500700317401c408116002802c102015103002c400c024042074001c06a1071610b6040080c10034010340d03080c200c2c802140503c1c090500b00200c0e142800201240c01c880d900700d000395800400d0403818a0011400c0013 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 944966528 1250 944965278 944965283
    0xa03110a0914151f0e0102010e010b010c020609060c070e04110303070809060904060503030c330112240911030705090606090607061b140a080a0e0c030d03050610140403 74
    0xe2a50940000d04004c81e40305041085001c203108080d001d07034200700b085480b5102170b0000d01002c0c2c10300740c9072400c03509000400e034003282092a29000526100c0d004007030071000180b0b442c0c140064241500e06c1c00a241d04640c0850f0700c000b0512060040705190b404100d030f01140251301d0051540d0303030200079000d0076400382c1c064100841c2c40211030707840360000341c01343c5400380403a5220101045000d03502e11320306008202084007004248045240d032210101420110b030075a0846900e0a650300c1c04c035540120003070f54515410000c00a90710b814440c40714601c1207032100400d40640c2d03810218001001002132030301c02c1c0d004100030000c81d16081c203d998004406c0340c40c1e0341c4615040001c81c846102d000c6c070061005203019290082c030014011034841c2c44100d50b660b042c4c2a40d51400c06074840c400d08a130040418403040026802c0291a0040600301480e58140c0f00b40700780c0080820325001c010414640821746550401000f814194400a40300d4074178500f00c02940c01c140c1c40c1c5010380c403072400301 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 944967778 1250 944966528 944966551
    0x2a1802090f030d20120301121a0c0702131b1b0f080d0b10021f1d0604030305130305161e05062715150a03110a0914 51
    0x110840e58502420003000720000d41030710071080c410000101108030820414002000c0d106900b9240d010001e50025881c2034107224501d16400c040480747c100014600480e0a440105403000c00d44c0210001580180c0041d0016a00d4018610421080352044051031124902d00703c0c00f404800c0407101410309021490902082d050700080c0c2d0065042c0141c20040d02c04010300034294204644500101141310079400c0800040080d0010018490082e5240e60700507401843d000300d01e0003032000e011034030400b05070001030820407554105800c03c0c10400c0c901010b0f00650100405e06405008550f441611150301c1e0050300c3c4244e0700078006001c0d44540403481d1600022031020001101d03041a1040d107126026a400d40ea180351450b520141200c1d0400c0d0310329010341c1030750000c50b584082c20240b00004007515807018880c81c0f15024078401007110032078503140140c0702255102c0b00070340c001031400350884032450f481207800e1007500841584007200161a00c8510070391030f1291624280c1080c41c2c40d94 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 944969028 1250 944967778 944967787
    0x3020f10053714013303020f13030317090c03070608100801051303020f010902130c09090203090309090f090604170409020a031e0509030a1b050102072a1802 69
    0x1981e0070080380b4202ca0003240c54143e80501e0704046400c00b42c104d54500811810f00c0108011150350304104008405020224403000020b8a0090700a07200c01000c4202c194284003c856521a0000440c5d006030301141544041091082c1d0b000141039009850200525658844801107690b44002c0d02c40c032070400c4804004144041c0c181015074008128440007031026050000440010323010840017140503201d0b041c15030602035010b0013941e14107a0000c00307001082200841d0302000d41017805040b81080007500002c5800718051000c2e5009403050340c0116141c46204091202c0c0130000b40941c800d20f0245020407002c0390000a41d59409540080a0001010f02981c40d9101c3e010360382140c800c441c00480d41c00201a030642c007034000030820306108000c4112024191044071800d440130300b4990800c0001c035034030a0081c0c2c80e4002a400303242480006000988481d82241c0001030200c607a5650901500380044c1d95080400101491802005041c2d00c0e0641241c0c50200c0304010405e00754002c103 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 944970278 1250 944969028 944969101
    0x11206030b06100e19060f020c3601090608120c0d030207141507080601050901091406091f021c080a0915052e06121107020d03020f1005 60
    0x4c494510403400a001c1c2c624030040180314440015050196500041c401c0e8940c0c0b40085c4000b6942484600282903900c5416004040020000d1214980b03008842e0075144d6050b580d4a030403002d8004c041c10400080c0c5641007014003414070540305403401c1c602c24203005600389240c02003941c1030010043d003001a901d80303451034400200141550501d040c1c0c0a0506800c1d0a0b4911580a0703110b20000e949640ca903035101c000550b014001c58805900040b000d200030700095014840020040c00010189410002c000b80002e00a488642400080301c0c40c02c01c80148a503010000c5d480440c5112419107030786900e440c0300518204000f081010180e0325000789409101d0b04d00021600c10380008070078042ca01c0d0811181c01840d00301c82c0758a08860030ba400c845400c0314010251b400361001c980c0d44641c0003c4000740700b0013800c48085203045100c001c001240c0140ea4501000304803510036000340450030f110f04401c0342020008064a001e0701e00781020400e07000d4800340411002c1901c4414000c4055014 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 944971528 1250 944970278 944970287
    0x90f070803120a230601030b09370e011b051c050a270302121c020903070f030b07080a06050f040c0c0b010603140105060a0206130809060a030506011206030b0610 71
    0x61038030b13502c104404c03100d04840841500ea100d0103085e28148044034100040c840014002c484c100700707480440420282008070700c1001d9500b459018180d00e0180349009203030003100c201d84681c4441e40c0d9540b4501c140c038060f03507600c0c030940c1a260800604003003400d5281e801e0303a07011107060000da503a02c8001940480d4154070411051110124004008078101085507028038a06419405482072540001c030302c030710100890b13500c249510004403960120301d440c040a03401c00024160f06002d009408910f0002040c10b0b600198001c0041c0c4815080054001d8009440503280d056000d0a108050009481d0040c4c900d2081c032050310700041900024501311005030100c4401051801640700001c0c0440d03168001280c83c0710400c51441e443d0b60b840b03007005802c0c4503860a180c0560401c070002011030311045071345a40c150045111a14009540300098540e0780542840804203a80e03a061001c0c950f4071010498140454400400403a402c41c0c07620324881e40c0c020100c0d80711f103901c140c01325200740c443e = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 944972778 1250 944971528 944971541
    0x70302071d0103050606121213180c0807030c02030906030603010b1302030a0b1207061b0b010303031416020a08031005190e0705031b03040204020c060f090f070803120a 74
    0x3110000c0344030066180122070906003840107035218030400d004a1114a8a0f00f81c90030142c412030020000c00c10a00003a00c0d03643c20448064100c0c2001c040001a441d150209210891422400001c0d80e464200c8000e02103203400750410040500d00340d40900303040e400108403000300c0800c41da00c40c0c59554540019000d4240030071216001078071820021340342c1c68640c015502441c3c010f601807209828420a000c0e00c02c40072031b4460351540c8003200800146002e01c02d402a02e4602140c0d0554412643d01c0c0d2421035042a8002c90000c3d40e901132070080c0007003001105400800b0602523201100201d00c0c000d69980500700e01410140000020900c005400d5544a0091001400039036140c4c0305001e460803981c0c0148180b445c48007941e0009204184218212889421403100218120122581c8131a01c4c2c4c10081049030050760801c65079aa0701010000b16100d2110000078841514040400741d00b410810070800080b90311141040c4003840d000f00039036100010118400c2c580d5a50680440c018128 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 944974028 1250 944972778 944972789
    0x3101d04060f0b130912210b010c051609050105060a02061b04050d0501090b130803131109041b05040606021509070b070812010f0e041217090312010b0f0403020607030207 75
    0x16144c40340f03051107030700304100c0c85024032020f48041c401c80c1410b03a000400300b0000d100030680068552100200e5600c0102d4440041c075201d41801c055070b0b1007625084182130840303901b4003c0031342042080100d00455003d02410f0381e6030b84c00c00300b841c240a5030341c960242c5281d286400150385c1c28000c08507d4103072001000010414130070060b80e42003090080201d008150ba503502441c00041110380110a24604254020512031a5a44980744041c48942c2558102c510304900c0480d13002d41d036101c00103103010302d0107240c2e11803881c0081c05030055034000a601c02070207142404000c001c0d468000c50b0103041030a910040381c03c1903940c00390260500c0c0080c0c00c0300c00d00d0070002c00c4080038400160080d1140c070070350f40f07190141c40e603c3e0303030861810580a104113407212001c0720014000880f245850010f109403410445078245103840c0e000400307002119041a19400402c609a01e20501c01d0203e0040041c40a483d1400303540e102d00e0301c60380c812030101a00032500001d100d4209407082052600411 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 944975278 1250 944974028 944974039
    0x30e010e1609110a09050909071a0306040f05060306011202010c06061e1d072d0e1509030a08030c040b04090203060114391203101d04060f0b 62
    0x401c0c0070610000c00000e0240390000b500c0c00d4030700c81c000381d9200e040341d0b501c00c0307a03881c1c02e01010b00d490304000c00000002d00561035800b17050000500c901010014030070072a04054215104e02c8c0c10b40c2400202c59104c80140c05140c106414090700703031000b213801c80c15242d007050340c103120075410300050b0350701c02c003d043c014481450040c0000d207000310801207000c010f00f910008100b0554804030001c0348150090100f0b107403201c180209038401d010f980654aa0710702031088400c59a2458204e002d40c0c40801c4c064804511a0251317080603180035414814607814010301541000c95507404660380f484034441c020f10070030000000c10304030001082a00e0080c5101042180e07100d446410642c0030707400c107442050210300b490312842020961502034075440407181e1415005104100f2000d4110800599a50341b030810b207401760f11005a081c88280c500000000300b05507a405c0881244209001c0c961000c8102d44051a005030a01c010390031154010b500b0040204a04400454500090142c0c5881c41d6014 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 944976528 1250 944975278 944975293
    0xe130c02120c0102130812030a1e0f0911060f0928030f051911011d0a09091e02010503011a16031806140f160803070c0606060512040201030e010e 64
    0x840b070540040c40d00134004100d0907003142e40c0b010016981c0000281d004115482400003625000c61540b10440b0b6030300b041c0c0a01c0d400a20041d80c0002c40303840060180e44103884918200521504e612000400b0005442041c0742126401c0707608014050700b10a18441c0a0b01c02d2480c9171906c540e00049412115099189441a5030b4230307000b800c0c058501011a03607070059805810a01c0100100080099042190000218410001180c204505915031704580c202980107082c80d0305d03145a0344000d02103c00f00001e9414a905091240500d003160000c5280c0504c2d20b5000183da108040c0d07411644030140300a60106002c4940513540502c01c0d01400d1706507144864008d056000b0400010600320303101c60f42429072501c804440c4140c5010400909080c100100c141285c400d8000340504048a01011000a02550f070080a94401e0381c004000030305a044900074026948240d800904060600c180740081c03003d0250300400d002400a414143d45201c03d4103210005e401841c40611880180c07040c0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 944977778 1250 944976528 944976547
    0x14160c1a0304060b0415090e1e0d080a02090f130902060a051218061504091202070312050a020c04090f0c0303081807080a0b0c04080307030e100e130c0212 68
    0x55400450b41994003505010700c540c80da09041c03080780858030303180e106820742508044003000a0040c402030000c02d03118401d82c80b084a041c43d24207110402c0b00c00e01400e464020709070010a036080180400308083c0c0b042040749060340d6032402c10072021105a40c0c2540407000c0c205180d005000055007c1d4025100141120f8060391010051120100d106c100700d4094483d08003450140034810a501a564801004200310465142030f000c6141c40c01803022a001304165200c0000300305c2805d41c4005640a031400b0300070070107190140100d0841d10700d8542c0c1822405080295110a0038404500941da2a03480c3c605120440c042c41c41c01640180141c4003047da80d160003403000070210340b0842d60680c0c40100c900e0402011030345800701c4040724000c0001d011961203142800c071018062040c20301007013200050724001407020300301c000c0c000d03100c500d00e96031440c040c4808103000d0249801004407200081016580307241035081107494140002500b0181c0b40000c1e4904035032402c86004080010921916 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 944979028 1250 944977778 944977829
    0xb0d0b0a0b040b250c05090903070602070c05010801060f0206131a070c0c08010b03060a0b010915050c1606050a180801090809030c0d08030403050a03152414160c 71
    0x29040c281c4c8501c001c40d03120003a4404040506450020004200840104003a143c416140e0760040c1050041d60b16001e91030780c419040b81d204520440394140c142d0001c100d5036030848512401000309042401c800b009002d0000c0d03c4020040c10716171421a050f002c1000e01845140b4102014070490b502c0d039072070420490240c10340080c008200c4c0c0c0b0480003800032401300018000d0504030b0718041c000700000d494401e00100a002c0442199040044c528030000f48913182c510444400d20582d101c4a90381c45401540c1c038204218803400008241c40c120080140562200440e12180d0b610310301107594500140030160040c103c0e6100000c90b40c02c1031044410300940000138050498210202c3d443d600fa114103000c4030314441c7c10040d002c14001d200003030120340124014030b40b0032500d150000d02480120440104204190040484c5a402c81c0c0c0175220b0512861540c40208541e050059116400701031110403440781032201002d88a0b2000075404111003405150301524200302003248001c5c3c48100c642 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 944980278 1250 944979028 944979037
    0x207120311010b0118030b0a020702030a150e030a1e090f0f060e040c090308070c0302041d010507090810360309090c2010111306090b0d0b0a0b040b 65
    0x2440c1d07500e09096006103600a0700c0c12640102007580d2042d4440c55500c501a81c2000148103241841e000c1200500507581480f800301014461101a5000f8010701b054a040361070300e6002000c290700820000030059045001020007130003600045035104000302c42101c0f0191213500a4144241d50030340031885400700041101a41d11030395800c01e8a690340c40400007074980111207000480c0d0300c0c81c414008035440400400d0412302806021a940381d80e5408542200c0404007070944808440000c0c048155003800b486c0e400c240300d85040c0c41d40078100031803980c0340c106014100c000e05a803a0681105458840e0030384d20603808030042c0d10040c1c8000c00d40c91058010300c00382200010901c400110f0103844512407072003e02c01aa90301245040300f202101c0d01058003089030301e9030388140140580081030718092103c018031034111700c03501c0701065200c0707111880e0950000c405000106005203d18103d070420b4601d024a9011b02180c0e003003501002c24441035144c0c00055800000180100c1c00300400360052 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 944981528 1250 944980278 944980307
    0x1c0b1f0f0206150105090102070b220503010c1d0307051c02030607020609060106030f0209061c050703020a0c0f0f020901060201140112050316022b020f030a080a030c02071203 77
    0x3462003484a50803a103850040341c2c101624294903540440c10b500c1080941055081070048074411500c504a03801c0035003106a0320300c103603e1410440114068500003a03401020185e0090002e441e10080c0901014585004048550f00007401d03054565000c2240310010301000e410b081035140c12401b00c0481c0709459109034082e22840c4007248101d403000812610609100028081b66400c16004402030320500c0b8903102519000e1080322845c0e44c901c2d0040c40032501c1c20070324600044101c0e4410301a01c60082c0040705161040c800d400e201ca0308580306608007944100e03a40400c2c985e42c40c12040507450301a010303401ca85810004030b0307050340541c01580c090f010407602480f20f0381d0790400340c58922403150b001003e603041030100c10142a44100803847c0288001c0099003205c0c00d04540f0007249502c0301d01800101010142c5c030381582450096003420440076405000c51050340c0e19804514402da49000c001c0541e90707030980000700c3c42070000502a1100741300e40202c01c8580e080c0180308800c2e84c61b40 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 944982778 1250 944981528 944981537
    0x9100b04091a1c0f0201170c070203012a110a050307051f1a0d050c0405091f020a09050d060605090f010914090d11190b2202061c0b1f 59
    0x100c0d101441c0c0071051280c803482d0444a5403ca82c0755645500d4000d2044004905104004075185800340368008510301c950b03c0c1c901019120f0322507004060940d50011020b681c450441c1501c00802090010b10144180c02420400550580c0d0761340c0c1460044130600140c03807400040740c2c8004116002c1159100001d0804928050440410b50817084420310400d0004140160380070b40c0040c20240c101a940e10b00542c1039034080c60700d440120f810b41d10700b20340c1021a50401c0c1040442d6202e610002500612442d2046042c81c4480c180a007040e003540c050144246001c1201204102554000801030240a4a8101c1d54100b12020215852007030003840c0c0c0242c18610071108241d56002c00c1e5100b260fa850007400b0f00c10880c20f080d541300c0340410514443e805440e240e40042d031480302c040d00601c0c0c443c6003000350b1464010316041f201415030320500c0081c0d00c01c4a0b107102603540c14098501c40310030140c101e650110b02142d240002d0017103045951b0000d460141a07801050703556440021074215032038 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 944984028 1250 944982778 944982821
    0x15092018040605040b090c030a060f0b040504030f030c020f060c0702060d06032603040f03030f060816031208160302090a051c050d0e0a090933062309100b0409 70
    0xa01a1560a000a47c94240d0700c41491207010030140d4210f10f00c3e9040708038000800294038008074041c1c400403075099020a4000040c28410b941c18402e50312803000b92700c0a00886000c0300813040c0c48001c0900000301d110710206d00c1360199a04d24045070702202280c681003050b103580b0700d0150400c3c661084000c221018600d902e1050f192041c045038030480e030004120b140c0c0002c40d50140c00500d100954640312940d120404200100c0400281e103c1d81c01c440d00c8005190316600d001d5110903001e084000070003510f1410b00c40302035140d02d90080f052040342409030f10703103000d0004106040c2c500d6100661001c40250706030750614504c031011000c07034010341c10744081402c0010140d4465184002064004200d000c2c1008103c2940e0b00c0b00820340d2085204d028045071008100200b20801964007001c524403e03000c0c40619124400c40c4010400c8001e0480c0000500c02c0000002144860786402101c0c0b00001503440240c03551502c01600c91a0740e0191035544803080324004050380460184554040c0b207 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 944985278 1250 944984028 944984041
    0xf050405060a0809010209040e0a020a060e0102101a090c07110a06090e2205100b0a0b07031d040e0a063b032515092018040605040b 58
    0x85405466001d4400c03072030986102012640c0c064010315004855500b0b005407400b40ea1035014000c0c00902540041c01d081d0418010000c50702c2c210b03400740040c011085211507843c1d0700800d5288060443e00302c0021028001c070584043e10110981c4142e2080c0102c040084204048020345003590056105008a080c0b00092003030b82e000074046d89020480c100800c00422040c02c041030340c81a8041e82c0c46d81070701c6072a42040d0794030202c841d0840e02c42e0007c00c03448981d96028840c10710740079021104034580c0c51030112100914480e20602600300100010300e00e2078010020201e40c52a05c003c3d10030802d90300341201300d070740b80c80f2040804c4441c0d509044440350880e80c0320600da0303081c1c044c0712003020304440b481014814040c440004043d541c00184001802007806242e00c078440c9026500b046548040c43c0f07000d205d0721103501e0480c01c1c10703803828550001241c01c842040c50051111308600b070554082000040c14442810194040f40b40690104010010309820003402288620315010325621400c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 944986528 1250 944985278 944985287
    0x90314070501050d020c15040b0603060f060f040209120607030203100501080606220e09210a08151801090b030609030403260409141617010e0405031215010f 69
    0x5100d40760020320300b405100326000305907006112101940080383c400c00d451240941014404803026580050b0440801c0040c0c1014040241c0c8542e0003483c001c0c0c80c0c41c1041c00922407291200007580a0307a40450300220395201d09040018440070042142c040c8d2508602c010043e5004554080e019888030300001003d5000d9208a03000d2100141200c0c10486414200c805460b01d400e040503031a00040310004002c05403444c4e080c02880c40002425400100181c00a5408071101100107000c4080001d45507050348051201d4002d507862108200307514040c00000d2100100c03200c80e280e440040c100000314041740c0d2740444007450003034041d40c070b850b51403101c0c5a0f1240503e01c0080c02c44ca0200d01d841801c1119000b85c041c0500e80e10056609040e190f4040710200c0b031000b00c942502d001960f0074081c8921403180040c80182030b0340740c00511081c040140c408410018403c1700c7c41c1d059084c0c007207401c0040070f1099422169520760034141500d094a5204c2c0d143e5454000c407804a0b07040600d03112054070a = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 944987778 1250 944986528 944986543
    0x40203010f1a040c030b0a0b0705011401030312050a060b0d051501020d0f03021c29040618050405010e0f0706140f090603040c031401064b0e07090314 66
    0x24404408031442c000d03028003010b85920059201059034503848111190384941075a400380c604a807250713490b80380500e04142150160700204604004003001080000c0c1c1c00003c0c0800801101d00c0807910307440b041d070300501904d42504464004c090225100251103259442a40b180c0c1c5420b810b003942017409001640c03600d03c608d4401c00001c1d03480300e00307203000b60090f001810000d115007200268211a001142c048a040c50300d14160f1100700801241201d107101d00359552010101d40810038145481038072100c0c008465004010161110001014048203612000c00080600c081d00ca0f00a00e403500346444d4016030003000045495003548000044030700c170075100b0203040c000c040c40c030f006606010000c01e908000d2046491503003e9070b003c000101c0c1c51304481c806a19001c0041501400e1020341d0402c01c407500402110510304182e01050409401242e480170f550f400102074032803806000c0310440058540000d490070440c1c005001c00c1c10b50003845901220300038200650340100042c0405c0e180c119 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 944989028 1250 944987778 944987801
    0x40204030b071b05060f040b070f050d09030201110f1b060f061e0a06020106060f1403060f0604031b03030f1b14030d050c07060e0334080c0105040203010f 68
    0x105400010b90482c06401a0001c20002c0044102c841d106962040d00d06182196035206100c01d01c024003003000f45140000350002c616080845404105001c020018000c04444041e1b064855100b0300903d0f0003076200b8001c208400c0403042c2d407050340c40c4988a85600550242e140080c2c08402d1100c010790110340341c1e001d00007201954845031121010400100f40d002c103060880046a0880182070303444680d140020320140d000030404919005026218445400241003032081416001c00406000c0c801c407944880d04480d4031809000e0840400d1450080d41c000820310000200209241042060320a0440e4030039980c00c924440c01300d904955280a00d0000302e10f00806455110000754001a040b00701503803181224181358a681140041d01c50941d5100c041007400101001440f10340e00400c641c0355141c3d0021407510807003112101105110320302c0c00c081c00d100001107508011a14000c0001c0ca0741106040c3e450351038882500e03008003400d0341c0480c4690b00e0604550740858040c003c0f5042c01c407 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 944990278 1250 944989028 944989043
    0x1908070204020f2511010507030522080d022d15070210061d0601050a020d031a04090821061809011d03031902031308070c03150f060504020403 63
    0x2281642400060340001c03458a8010009101d1010301060b400c1040c20502c28040c002c0c1e0181d070303141c14000181d0049024140c104402086103002080d000800c4074080c060309029800007003600c407008580740c80c1c5c0c0d410001c0607005202c0c81d0304109900240700b0ba00c0201e034200014104240d5100071144140069076012281c20070b21648000600c040307910fa41c040000d005541c800b002c072420300d10032203040350484a041c6100b4010418465000d95200e544810b080c24918603040a108002e0342d60500714941c2d008058a074580200c05c51304441c501100b034100513000340521941031506581c55007107020b80001d41100b022900d1f00030021161814014000030342914061a14200300c1d0382605002000b5556035900c41000086102c4000110f19030240200061034503410003204038082c0c01410b0b101072030417500600c00c0c0519404200c1c108080356610505590b0707501514680b9a044151a0740302600c640c882150108a0740c0d9140c01003a61842c03e01420404d00c0d03102c800b000124011800040c120b04c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 944991528 1250 944990278 944990287
    0x324061306121104170106150206040b090708011e05070c1205091906110d020a1e03030f0c0201020a0e03011e020306060c0a030c02040b010c1a0c090901080706021908 73
    0x180c041c000307100c50b00502007404200303c022520100043d43c03041d0700141c103640d15001c01080c881001c0c455000600005a02c03162414014000203642c1d085c00380c805000154403e0100b130301d19030704111400040c81d03203400920880d144004070342d0481180c002c3c01d00b5800c3c10034000070415231144500e1000503a11032240d880038140030200300d07803a8010048098004201046102c0c80868500d400802000241d40d60070011501085090410014000810a41d4080c4180d4030004107040a00c10540307a07500b1840007100d0550904401812140001c0800d4a142c808100c42143d4190000d005032120380d29055030100290701810700320368100402e01c0c416000c6000f1a0104101e503001550001c070010402801c001c1714005103818021000003c40229495410303400850903d4014040034110900700004110381580700e9104958211320841c0106924500003a00028000141c0c0d4030000d018264800035a1a8088140e40b61742c0d6000f01405441035100b44c3c2e041c0aa03003641ea03072903254080c51140c1070 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 944992778 1250 944991528 944991539
    0x801051002060f070c0215030106180e1b07060218010206100303021b040b120c04060b0c0615060c070e0108060c030105010c1e0f0f020906120d08090106030803240613 73
    0x5282c8042c1c6000104140d125605e809641e0f4480e03070140c07844104010343d580354035004020340000400082a0004003a1181c1003110091200c0c809621502501400810a080c00c58607101761003400f80040400b1701c082054440c01d10030320038409140320203030220350194594003d442c03016030f0544030060050703004403180340c08152003e0980700c500301301803c00306003400840c0014901c3d0b070318221000b0082e03001c202055650301e040e00410000706a180802441c1c068040541d07501c0b024002c11107062050103c4600c0f6050320703588200c801c00002c0000340e274a001e440d4004954450401e01c40e9266a12894005c210039040100450b03048403016110340c0548841541c41e07207401500d0214008415942245100100c1c0075480e25034200c9100755402c0228082e20710401c81080341c0500300a0244041490f80b41d840200010f0411450909081c244256500c640d0400d0140603290030040200d0008418021368000594069800e903042007001c40410b10040c05018840c0a0010f01422504a8401c200300c0c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 944994028 1250 944992778 944992801
    0x5010618031707050d05250803060f0f04020c07140a05100f0c0c061e1e051b01021b100b01050406031a03011d19381303080105100206 59
    0x81c11035440d803500c1c1030040359214907090030503400d08034011070303c001f07003041d500085100c4c050004120814000c220240545600d4020300005000901659110a0b00304081d0f40d003291442c40304100074015561003414003541c40d122040703840b070000350104c9450304564620700b01044a0075594042c1005561392104030301111400e040c1718007d01480010602c80003c070b4040344040c0c014003019118180389100602126540c80541e07071441040049600d02c034000c041c00c00c4040d001d468464581a07840e40c403407010106000042d9900c180c020340c40003c001400b440c4212070300100100350300030703030b015054041c07842c50039240c5290565001810400041c010725029078000407001805d0390240103000e0030710000c64211031400f40407d0250b25140443d0340302d0b04003000700300182061504100c00030300140c0e88540100211410381d000c0100082415040ba01c0203100f04408141c0310b03901951141043d000000a41031003200540008140c1d90010070182030626a00128012950062000e6a210b60107001e = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 944995278 1250 944994028 944994053
    0x15110a02090712050a090c091b030c050c160311150706090f1a01050a0b18100519050306030c09071e200f010e0601180b010210060909060501061803 65
    0x181031061000743c2481000081c0304039031181c0703d220400074645800e400c0c4101d0b00d495981c08515468140740030030b04031705004200010308450750b080201d071075004100152a1070003160030031403852043e00498000101581400001c490094007070310090784803141030111251000c0d00d288000c1608005c0b00d130000d8080d6003c800424000c4140301c01820a0340d40311400b00310040d80200303010103c48014081c0b071400015101c000c2c642d11006620305251607100302458584040c04038802d0343e40450004959010b0030032520541900d4a05602040d12a88040e040350800c2d22004d001e4400c00304850401e00301184d0b083d008246030f4985468440800c03d51403202d14100e42403000300902c42912030003020f40031242c8aa00800340740034054102880c0081421500d412201100ca580001c00400c807103111f0380c48025443c2151400442e40d038120100503464034180d40c2810450915200c0002262606030780030a400394426502405180d0f61420304841001010090000b092140c0b10204002105001c0c0c04 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 944996528 1250 944995278 944995291
    0x1c0e0c150d11030106020f06060901080a110a0f06051e1e03040609020405010b120f0402011413210201030b04111c0605030f060106020708060405070312031d030415110a0209 76
    0xb06655070302160b600801c1e042a4021005603200b580c001007030342403d10000e68000400c0d100041c4c02e606d40000c7d1652400100405400c41e40f20b001c0c0c1121540f40e6140c000081c01c01c0f5002420f08030b0342e507003005009030700140d0084c2c500709010b80312141130340001044914100402c0281d104c06051542c8241c800e51000c1d004444040d5203c0801e00140c41d14041c441c000d007141e040281c1c50755031505c0000488140205170603030504e240e00800c00180e80101030380c3c2d03038034107030040023030719016028003007412040d403600001c89650140750600c00704803117010280d0016200381e034180841d403240c000b840b05035948042200c010250600a0541c0c0c0c0c0c06200000303400040100022079182e81d91808241071801400050f405a0407180061110342d40401c06603004000035802030445180c0794072415291081d502006240c003000b60040900c180c4a82c1080d0410346441803803240d017081741040315690f039010348a40b80d0148420035408045901811211140c00003903406418034402650030000f0030341000340bc4 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 944997778 1250 944996528 944996531
    0xb0708030601210e03041404090816030c0611190f0906030b0a0504091a07111b1203160308090a0302071517090304030204110306030309040c141c0e0c150d 68
    0x50f0208603076140030710b10110100c900070b583d541303013410804001e843c469a44140550b060034184c02c00192900100d40c884071444d1131307200f541502d6140131254816038010140c0602d0600302c07007441d900019001410800303031030040c0034485100810140c0c0c4003403c000b9682c011071202e0004002c0c04c0e00a400054032a0002000300105c552244002000c0b1040d0b05c030146c52840d160a21a02c2550b04009069000842824441c0c000300050001a03510742d8070105441e0b040d4190803030321281e5190100d0f01950040035a098a1f02c494245828040c0c0100c040419000034080002088198a000c604511800d416a0103080d200f803c03c00201121080d00c41c5400403c074032a0128a1940090f42259000f10342030030255949030b01d180100b00c1a9030140c0400100c0c001c0070824000c007541d001003240c0f0311b000700b550007240c910141c0b0801d45101001413512506c08d01d0011300203509244580c4807101d00301440a08202c00030b02200324a95407948102101c0d0408200494206414034000240c81d569010910 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 944999028 1250 944997778 944997827
    0x140718150513050102070e01091a0d060c0e040c0c2628030203061c02030f030a030c03140103050304031b120c0303020c011e0c030509180f010b0708030601 68
    0x1050040c400104540d00000360740892140520250011654000c20091004059460a0540c410030420b010321038501c80c0c035a103802c040146940e214949410107401031107110740b280c41303041c0a8003400c210804800000d10490b5510f685141601c600e14100d451941d0307134201e10b031450f6030310203405c80042c0340d1400000c0d40a030b90400440000001b05911159040c034044035426601c8002c01078604900c024040c14018401c0000586038815020350040050700c0004d0b1355421800032034148901403003012098000050312807031030368244c2c20121040025a4007044508010905000c1c0032500f070200401c0c45c0c0042204202061040c01c02a80d685080320001d43c1295488800d00c100e5045110101c075031140242c810810b264041c1700c5031000c41c20a092441104880d20008800128908489018840c0303003034450007071501c0380044d680202c8014008942d140382d41120301903a0a02100d171143d980614000100c2e070f0240c072905030780c001540119100e0031030f20307090019a0b04801540b0f000901d4610580d = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 945000278 1250 944999028 944999039
    0x190207030512040515100803030c180d03050c0d030204030f0204150e010603051803091005130306050405070f0518040b060607021f090512120901170c040e0a140718 72
    0x1448500452152004103204424101c45c406a20070040c0400d503085440642000300c0701c000310849600c10301c1496036580d81c1241c0302c00e154595040d800c00c1ca0708060803021120030103410900415803058148101c840c044caa4100850070f900c200d010080c001c103180c040500044c2080d401800c40c02095811a84881d500d03032000f100000130903840400026126024044039071003200302c3c140040c1404013b18504280640450651102c0315002000c0100014020316000307141240c0001460b0b0081c01031019092070b050003035490300280a104c3d06131140d250000760501d80351225000c4005031007002d505503903482d19880b86024000300700603040f4408000c2c1e03c0060741c9146c218000c50a0fa00401a081006130400805d40042c0d50401402119550076062112038000760854074080c160041543e94807822004035001446076103151600c061401c02e0010341d05200c0040c0054910b889140c41c502ea44048606043c0d03231440a41500460720500441c000700e105100e5544031a00c04010742202da030340c91 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 945001528 1250 945000278 945000307
    0x150d1d071a21040510060e1512010b04020703051b03041208092b11010504060512060303370c080405090703090c090c1106010f180e070e0402090f1902070305 69
    0x32103048036650029003000640e02501d01c2034002030070b80040045140e2810114114502480614080c45403401c40275a0f012039000350400b400c40702c40a04259298012450003420581180c00d103191042240303803005080c2d00c0004152011aa00c0c640214102c40c002c0d11100c5140e8040c03a070035a08100010541c00a0f00c0030004191021801e0000d0000031012600b40300d0124a602204181000780420003004030541c40010380d581070215942c1110319481e508000303032643c42036171304c0812148035610b5600103414444040c503030310a4404258000e240003031101141c58500d0510000c002c03090501080c405402e10003120340c1d109419003000a14101c90307490350801014640c8c848808681c0f2246202150342d4854040c4c589201c0100040c50a94113041850455500502408204540070084440380d40c2607034001c180440151401d5894807519840090414a4100d4060b0f0060b03110740b01140e40d80e004196894454041d0011103c82d00c018410110041c8d401000306504000d02800000f0b03640010 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 945002778 1250 945001528 945001531
    0x105031303020109051509010c020c5509090203030d020c19110a09140a09020612010603061502150c09040e01021602030f2a150d1d071a21 61
    0x1003200e91b003040c039011003030302d080d14000c4080c0030854002d480c600c0e4240c0c4a44050150009900581003520742c003245542c00103004c0c0b07101011401904414250b40c03441450008425140480c28030518039442e81e2412090721a804402905580308001042d000001c0e40e024010b003035440c0042d24001036800131101e40b1040c414000ba40e0900b041450a5039030314011030480c004082115007803000c0080c2100c860b0f880b10001b0324041c0b40549580c2014210b507540000c50304e1045050341c03d0718030f070750715688028003c0c80c05004032907580d60300c3c450004050780001031b01461005089041e60440c0c2e078101f81c00720140c000e02c000c140c0040d150b0420192828080c005000c943c000361600204240d01401018070301408010003842903084001078003664415201140030107142e08040c003810a4844002c541128450f1300380841c6440003143d1070b410280c1540021403060240c0e0742600282c0c0c60402c410380c031410144104060210f0036205c0c848a4820507003d000d110b5030340d09011001e10030b09003000c41070303400 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 945004028 1250 945002778 945002803
    0x9010f12020309072108040306051305160e1012032a03030e0c0f03120319020a021f1a091e0f0103060510120609020a0305010e1e0c010503130302010905 67
    0x4131103014045402d0041c158484c1c4101c03840040440055602d41c0c90142c482c9000151103103482d0320026140c00704481c44400d00d5039014044a41e2000459000407681344107006407000000004003003641450304120450a07103010401c03901c11000d10360703000c1d545154110300c41c00c903500c2440812030071003801281d2020342c18001c0d1404644007940c640114104010101c000d8410320140b0b01c24034054600190144441420705401550780c2c607810024041c2d02d05010300c000e156400011540c840550100341203013885100710690800d440522240c1064540a103247c0742584110b08800141d03240203116036400200c0d0740800000308980e902041b000c154115103004150950500410400001e40711f002e60188100e402150a281410000700b2009600c0c0c102400f02500c5400d00030565607000302d40703030003107900c036000b003040c03082074101c860719043d440d80c100001c02d820200c2070140950115000306420740595506295030389400504401490281041e021990307141070200004d0010070090b000e002 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 945005278 1250 945004028 945004033
    0xf070609030309050604060e0d060f0f06031118060f1f03051f0e070309030e030a051b0405040c030206071a0a052d07030f090b180c030706020309010f12020309 70
    0x60039402c01411410032540f042d0b0041008000420a55520400c4002000c200f1500c1603030009207410b2040151405400900020340b07010b035501024030307955100100300c0c0c0c425850f20219175810802c1041c024145550510054064800070340c1c189406550415039082c0103000c4090140150300d280e805a41103107010307002c20764440a01160880058030060301604012509241c90304040a00e80b00c2c0801414400505440c2d03440002018010340c400700c0f03000700181c00c582c114040350500c6941c403041242c052054507070288144145003450700955102d030341c000039405580391555091080355800078201362000d00c003004444042d4601d4002e56802002001004030741030074100111040200240506c01c40d9010384184030644000d0380e10003a502844038100007411031001a00c1c4d201a00059000500e80c01d0f072a410000b80c070008500960142c10481c0840384102c80c0c007028986c1e19083d50103020096407080c0840c01d6503603c00c4162002c98403603450131801d0410640c00301001d0380c01c2a2080002038 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 945006528 1250 945005278 945005297
    0x50312040309170a170d0e010501090f11090f040e0f060103020310050906060907140403030c0b10080718060f18050c270301021917010605031e04050f0706 68
    0x1541c0040d90102902070b00790b50700c64034803004001d00ea589115000c000c20000303d0417000182031640794280d03060215408003d02035440302c0040765000307107424007032a0f507118035045802c110341d003c0348030342000900904121882c0602040c108081d0310500708460b5882600c030080e1200c0c0c0c01d0203001e0030f0314802e62000185041c1d41075104050074419140c0035514001d1504042042c50784c3c000440540014050702c1e58103142c0c844040c00c690031800c1c00040b105000d000075000003010341c03186026100300c0c0141400704503030716600000003104107503105c0e500d4a42c4c0001c1c000d00a21868000e8200410340c107100024060365240c10b1480781d407102e5485000380c1c04c40c9a4041680029034020503034014010b00d203c6103003c000c07540c00c1d100340f0012514128072607800a24806140c03001d5044800c0d81070b80720310640d01c44030b4407640103004a002c1c2d4008110401c1c41e000005900f0b0207841628012041010040d81b240114881208090340003030042e1040c1c0311f0419210390b00b00d4180641c0024081c141e0341d00c042c1 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 945007778 1250 945006528 945006533
    0x220212090607020d0e1210060f0905060a030b010506030a090609060c0225061803051504021507031b020619050c0d0c0c09150b0415110606090c0307050705031204 71
    0x4200c0010402c1041d03402080350441c3c5a0b60048085d030340c01c05c0441d541a002c8814070541ca20306008030814022013440d101000c12154096018141290500882480b0940d40c1c941402039074170b40c5210040202c00d40d2001400a4641403000d0740e84020308110001304941a45c66441c1500e4400341c0a07104641e44140305040c0a906110070302000d403052100340310003000144002c01080321032003044100a8022030713081e4004080641c82c3c0c000d58000c0c0807204840b101c04081588001e040d58103e00c104e2007901c6a40340708040000307803860640c0644402542c0b000381d54450114400030b40381240c0c005801c20900c104401c40c04403030b1038542d00c41c4d502e841d1244a00006107103440c590b0354000c4140540c9030089030008041104950640e0398000c80452010500c0c945010940801e1300002c911400205020550f0202c1203c4c4150341c0b60355503504408806018101c584502c000e0343c055401c01c01d150b0004d0540c001810045411050503d842840c3c94040d4481c0c0742035410201100c101d111910301400709 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 945009028 1250 945007778 945007783
    0x60207080406090b0316080c130305010501051f0906120902030307051e0a020d150e190c060f02030304021e04110d0e01020a1704020a1a070510020f0922021209 70
    0x13615100d40054614104942c20815440e0075a03081d204206001c80001e95250b0030a050341c1c18034480c500d04028180d124941035001e03100c03d002d8940910b01c0034074100f224803003000c44050009503a032030750f003003207424044116010b42d5401c00911802b074a848884005840070001004054013980c01b4140c41e6020034020501143c5a428025040c0d0000da40d450159444d40a40f41c0d40ca91701c04804c000d050799000c01c2d20040c14403200c80c00d00b01c3c00740300f40d8140004180700480b128507210300c40b4001460344031002641d4420183c180301005a00900005005052140700788420108a805441000042c040068141c4050003502041c0c044080750100d050101405552103050046d4008c3d403d0001c8501d00400e10304621603030111414072480444c040d900c42c103041c1006000c1c404a4410351061009600707103c1d0740100b104491602c501c8041011105043c42a198032208241c2c08a03d4101e00701d00b040007548000141c0565903c051414210581e094030082090035100766a48001d860b0170b888450 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 945010278 1250 945009028 945009047
    0x110c1806041505030c2202070b041505040c0312090b0d06081506010e0d080c03031e07032d0b030106080c01110304061b050c0d20060f070618060207080406 68
    0x2c0201c00300242030000c1d03a0042080c00070a603041c4c0ea00550035030810840592041c0039a00607000d584009038020500000d603043c90f104a000d00c0d04203240c40c2c288444d0104036041100c0c003500c4000c40c008244000b403072041e01da0544041c1c502d08600d10301d854602581c441d034040c00801d0580e65a81d0f40030030071808103011098514603030740780d82031580c54200300182120304515440303807041190521140800081800b920390804040b0b0444e5200d140403c0e88440c03c05060a0700444804050b00056a0601c42c0c000d00c801021210001c0c459001200718024040500780b8114040d03944601d40d0f4152624248a0140200710140081c10045c45000c0090412241014a03031440e8000308004e0044503000210b11000461805e220402c04000d0f0410700d06201d007101400b0b0344084200380600a124184070401c690108003070001d00b42c50312910400005108407000e0000014090001401041e441c1d802041651060b1408a0070340d00503580f9a012603010f008220740c41e08011a05000b5540d20a1255 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 945011528 1250 945010278 945010301
    0x3150108011b05070c050105030712020328050603071502071e03062009010c02130203070801050301050c070203060c031008152517060a0b1605100516110c180604 71
    0x1d1345071076566118036030000580d018482c1400800804158400d2003200c5050100781c40031011500c0b800c4c482000a04e100124401e41c100780740c081d8420300e41c10410701c2894041d1314000c0081c24128a089903e108000145c001c8505500030503100013800340c02844400c60201140401184450541c5400c5049507070a4a80d019a00700030f00e031602c1020360020807240d00700c0003403d01c1080b4142a100084d03084940c06000800e490010051106441d0030401140c1650b104034000d2029a135009400e40050081c2c01000e5403560152000c0307901c82800c00011034100c0802d09514000d40c3e00c89031082c0c0f50548400070703401c3e03a10a440420000d941e820210f1000014906009120b0310040c44008007070500081c0c550080d400c1490104913030b0365941c080c000081114901060725030410203405c00a00315003500664181c00b030b40c800c6403a11005880b50600c03462611428489124070400d0840d0030703c140b444480481d00c00c00724500034581d100b50160019410580d1001800e20341201808107540304090034 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 945012778 1250 945011528 945011537
    0x7060e0907180e0424020d0f0e030a140927060102190201051804110a0201060f03030903080d090f06020301261b0109090c020c0306100b0a0c0203150108011b 69
    0x20040710409461401d000c80f01c003120300304825180d13030800708501c1000d140fa0b203144071440c0fa80410486000d401800c1080092401040101416546141501c1010052640baa0410000014082e00502ca68488030036120182410042d006010071a00b6590000c10343c0100c03520541c1200c1c46444202480d4072203028400b43c40079420001d840c170b03c14908604002d041c890007007004400310b10700e00d42280c42c3c1540108203100c6140500626429a0710240040c0010750801001044a40d081c030f90081c100c95141e81d611094520b581c562506c182c100500b50400180c03507d1640010079846044c140000307001d881c0050f600d502d84428400e1925103001500401c0b90340014241011101180241c000350350f040c64181802d4820004032603542d180e80240f41c9003850454031050280d40041d08411000307040d011a241030f120812420b4001ca490b204001d0445802c001083e503540c030809441d22110b20203000c47e1400409290b0303030300d821b040903001103103160340d00c1040940031842603500c905485010f050 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 945014028 1250 945012778 945012797
    0x3070305032d03270607050a1218140304031712070e011d01090e090f0d0216050f060403021314061507060b0d0506010b040816180b011107060e0907 65
    0xc0031103940001040c0700c41d040342019031035407104d50000105510754000302c03e50781203242c803560240180e001440c039180003c000300c82c40511400c0500c201c0545a1070240d850620403407e81c1c44404401951480709a240418400000000d0702944a090103401c01c000c11910f038502c0ba03841c2c0f148808002c0080d420841c090051844903600503006510100209901e0284ea900002c0140d424898a44c001d014805842c010026a49008074187c0c118000b017005846c0c85a4005c401280d50b80c4401010442c220b402d00020401803400c03c83c15044148003420890030603540b500024404904000441d40c8542c1752640030702e146500d412100e51240d01103800812400d0858800d01003030050b8030005110556461511501340d81d4103035100721003917125040390419030b194161f0004a0300709110700c156500c114011000c10035004004502a64102c20310200e14031940902030000d0f044070016181400340e1111b4203001c0542c04d025100c05031900361107415606040905011050038000e26441c1000410764 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 945015278 1250 945014028 945014107
    0x3070e060f071407120302010e16050102060106050a03140112141b090a0b06070804150806091f080d05040608010b130b1e0d09051507050d020703030b0307030503 71
    0x350356669420089a902c00007800d414589003d8040e040410030036840d60b011710400da03054000070040d5058034140c1c1e2000761100955003002145010700c1d0f0141c0c2000b40148451446200901070501c0a4a00841c5035409070ba14402104000e1f0408080c481c0178001203824402d0400d071a203a46030200c0018058030285801a041c000c45400486108250320f00c00f04070041003941000241900082555645950515048410794401e00c11038410000745603415040c03900a0070020b12544014002c40e040742e0303404041d41c4000d0100221850000350110022a80200030003502142030255101c46691300d08040c8040c1c03041c0c405a1007682000e100300300501004100341909011610a041e4031600c0b55280c40c0507208506031000019600c240c0801e04207002000758000c0c2400d40d028505a074603001035460080d2405000721070383d41c0402d8040041e91201c020a50041c0801400707890001000d0744400b0000341001610703841521154004581e0000406400c500401d080c040c10700c90004007400c06 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 945016528 1250 945015278 945015307
    0x5041a0405030738060a15020705190510020604050a020f1f0f18150c1e111e03070e1902120714041401030b0109030204020c150903120103080c0313090203070e06 71
    0x2030280321b800800408007da030301402001584040e110040c80c0350503043d12160300d594541c510780b0409205107101100011b601e400852003d015036008406000700da0f000350240120f011020f5190b40e04100c4d040b03400c0a03500544840ba4010640ba940c80940070800008001c04c01b22001915014080205000b0009114892401d18280303a2900708015041e1305803c043e82d940d456002180805a000d070001343c1000251080340e96115412100c241d94405d458989082103070300c5220207600341d404103c040c00024004225190b00441c0d8820464a02c00302d003142400342d801445401c0316013075a0406106c01d072074100290443c002510940e80381032a00e09801401608187d100c5641450b0340c1d01c1c81c0c140d0f030f42d00c00d5078040051a0080c2040d513072020711002e0030b9503402e2200041038034041c41c000898048040407044072400582d4090f8241182d080d51900034441c4c1c41040801c3c081e1204208184250303a070a00d101008180ba01e00040c2c484c503003880058400003080d102c2034856041000310100e200100c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 945017778 1250 945016528 945016549
    0x90a020607020a0e0a0b51040f080706030207081b0f01180506060d03140906070609050303040231110712020d0207050604060503270303161205041a040503073806 71
    0x30040c403190303c5906032001f40c1c082c0081d80c200c1000b4a40000740400c00840f81e05604088800031811201603d0751240118204d0048100041c829042002a0101c040001060401c40200c00042e03907000d56840e08c02500312075500311849a0600c2c1c072503224060080501c81d056005c0b030141c64036462400e02d50342c010100c9000402d000086100072401c42c03000e445142c2035076103855100c2c40c1006180b500c0c4c10301595a400031141280714484544180b4a4094070742c51a0070081c8010201d80d0620407100d603a08064800005112a2841c0a01800001c1016001550801c0d14103801404d4135000e031400081c10503c0c2c0360031640c0526000c09c001c0240c554420112a8000120940000d0f0240e0700c41c0c400a1036010540500898072010050000c001003461001907032a809448a081d400c5403007840d201614003c0b40c01415000150031442401f14a4801e150340c0140718a050724600901075460311040500c04a001894038103a0364010488000b01420440d4040c0e0a9114040b074504107000456000d070 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 945019028 1250 945017778 945017869
    0xc17070506060108070c1725081b010b130b03100c1d012f0c1503070c0201120e010902090c0c0a030e150c160e090a020607020a0e0a0b 59
    0x80314030002e40818401c2042a1b40039500401d501c0d18003100e480c1d1592150804142c8044500c4030300702d0703041521030803906405070300c0e800032145080142100e0b12102c1d503a681460b0078800d5480f80e01540540d6506880b407007618000240c0010406038540c01d051600c040c0840604c810340c90102210b201c0c03600070407059890b107007442a804040c21801e004031a5000d480c040e800c846103500c010717180805e1130220721000c1a40080d048990b401c0502042018480c000d03500d0210b01082040483c4060388100415403003075006041440c24a10384001c0ca0302111b81d400402c15059640e0300c00c0404524100b40c40030307003010000e14494200303603901600350b4543c248000002c003409805e01415001d5110045000c50301100f840450761140551030311143c5941c2c404402c082035040c1d8040200d030f110400c0003803602a220420080018030150b03405c1c407265610000007640d0045064000091032a03520700020700c07c4400440200b010103078581406588804403051804000307281424400c1c001e0400300740c1c01c4040 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 945020278 1250 945019028 945019037
    0x60306041a0a0605060d060501020f1207080a0207030c0807050405010603091a07020f0d3617010b0901260c010c060209040e010e210901120b040b100c170705060601 72
    0x211200c1c81e010007807519134080b94000030040b4520002041c103a003c0400c94900703030240c491107224110070645810342c2442d9159800d4082c80301070003150000001d042c1e00742c614012641603d4032503c580c00440c04a902600182d400b054040c4070605050040e035004062500f02401540032541c1c2e450354490310b110002105040303003400644141e20070409211082490420748000f00100d0000801072010014000f010b800300c0c00e80a0718031070b01e0525070205400d25200300d14143c5c0c18090148080040b10042ea143c40d034171550030f10362130b90380e110780750340240380e00800c443c100d501c18094101c04001071481120141c21039800c045186c1d0300038000c0b120342c40c0e10090050781c03066481c1c001001440080040011586413540346116113600041740d07595003c10104001c2408840c5807030f4100b03403007940040e6000498400030a590107050307801602c0e58001c000c0c0049840003910020a26441c001101580040c6480c80e40c102402035201c501d04078003004035415071400c1c0840e164199290300c054400c1d410007 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 945021528 1250 945020278 945020281
    0xa060809070302090a0b090114010503010317040e0f0601020c0307050f210102041d0f220f061103060418050c151309020a030b01021605191802070605060306041a 71
    0x44040c0070420107160b00500d5900d040c04c1c428207003030040c03644902603405081c9400010640e0500034000d10f5807140142e5903503103581e09580e03e02030310b00220540e040700101d0902c00820b4544448a28501c20f4600050410b001d01c0c00c0000245482e0007429154020b411400e0180940c1d107500501c00c1528406450780d100070000c106c203040c1c0145045c031101e181d035440441c2c00b180181c49180200c1240410001410494451038440541c00800740e41c40004008440b205411180c411701c034580f4444e0103243c080502440030703203441d000e88030305001442e200840001048042d180c0b5108081803080695110100301c0f50680c0c90301d66540d82e8082c86880350001000104280d034000048809240e444604050701310f5841c4041c002035004281468086820004045660351001070482c0c05461155110149145440240300b11203544621415420044c103030041180c001c58940e048070a4050440140d0380c1d16141005001c0b1003003d03201c54441d400480a01000c10031800340750080303018400700700703007075 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 945022778 1250 945021528 945021541
    0x4030818030f12060a05060c0d08061309060501080d03020a05040b13051009090f0e250801141006021c26010308030f01270209030109020d0b22020a0608 67
    0xd5002d880050150440000303108a801c0f0111018503000303410680301150241d031600100540c60180c5044128264814407004001d54407804044c0e070020b101030324480780d0214508552066514044042d00c2458841e130040180050070041d00742021024076007181084c125500081040c8107a00c10114691000b08000c10b014068402440041400800c812100245000b0203444080b840c443c1020581c40d015021718400e03254080c1410300c26001000d090020b55070804c05081c41c046c0e03910512a085c1075480424000000d10a444d0040700030f90308070300b5601e880c940c0c2800f4802250001c10840d0440b03090840340014101002908004600300009c21360790455010784540c5070704109410180303220000205000543d002540941d600b01008010350380c80e030903405018444800c0c42d4203000909105d0324081d20303540e4050045100000d001041c3c0d20f9032500052503038581a9029211f01d0742c030340c061184091241124242041a09240c10300c85002d507000180c10030051303c076807420300130301310000f450 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 945024028 1250 945022778 945022783
    0x50f0a1103090301150801050903160209070c0506010609051906140d090b01150e0306040309170a0b01061e0207060507121101111e03190b0d0f0b0f010b0304030818 72
    0x8800c60083c00800281042c10b14040e001c480900c54400036503c0c00010032900308021080f03c581120801080b10184041da090000049000307201c00200031003003030070708002402031055600070200b503520b41c0c01382410700007004140e6900700c800c07901c002c0c6410740820040f03401010890360032002e0035541c0d4a600c2c1000500e03002d0001e02030b008080e00311020010460f41d144039002c0500500c95502c60540c1d440c16014175980f00010350f40980400c40e810340420083c0c40140f004261721400e0019aa2031003001d69808050100030382003c400b154681051600558515100790098802071004002c45843c00c0c9010b0441d02c42c030b140c0584110840e5007813405907070007680c1440d007444411008000006100e8040c02c89030700054030846d5100e060b0f901c104003642c82c1c0010303030340aa00b42d00c0e0003e10006842c4e231014000e009071240d15410800f1038803501c020881903040c020000340560795240a91400b8200000d0154058200300795000060040c040481d0f40500e003580d000b11901d002d60351241d08558a180b = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 945025278 1250 945024028 945024037
    0x30d0930060204260d0206180c06180f0307060c120e0306040b0601030f0c09050409060b100801050310020c1e010608030d060e1305120a030605060d0c0807050f0a1103 73
    0x140180d00024001500810b02c09000e940c00c01801c10300d80c0e1031141040c166171036149407900000164441c0c2c0c081111070000d1452000b0f01d8010380100c030207115892010904540000520a2444000003403444d654140700580100051007240176103400e605002000d86640300000002d40450700c2030f82001070250040c0890740c40342c5801422210300f40342c1490b000300c1110f0204d5100c0e000a06040303211074541e14030b000d07455403610310341c964001c51130500d41403000921002c04140c0e841c0361910113040d29038484400c44c502280c0280c1c4c41840a605290034985064862103418000130710402821981403000300f6403103a029040d90003c898501080d0b1f086d8050070141e00000454000010030140f42c169962183c002c8800380b0420410981da0201c2c180700c520148940500680c000c0003406400700b0340701c0010401e406a07802c1c0010440d44a002280c0c0300c0d000341d82d549403c260349400303d4510035001901244e00100ba03241a078985400340030400c1d840d01541001e00240101100002568101802030740c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 945026528 1250 945025278 945025283
    0x2a030d180f0608190f1118040b01090b031308040806011706071b020a15020318030c0108042405070e041b0e12150408030103031b05120d1508010b030d0930 68
    0x3c6c010071a101a814015501c07030728071000ba00c82c50a606030b41e00c2c1014041e18240d40b605031981c41c0454908500e11441c0e610007020a001030403003401d0b8400188106000e00003074903c21000304019070425540c03120041196001c0b84c040c1c1d2100d400c00c01e015070722200e00902031546440c001c1c007690052000c58003011017900a046183c400302800002c596000000d082110030303940c420010960300e00e040c10780fa100414a6a800900d484001034080f809000381e0303051031010325070b90000440344d544003501112001d0f14058000f6150150a40080ca458004c007906aa20904040d04608078584042c140c030303400c07901a5000384130a40c51100000710902509846180e40c404900d0b130307840c4c0f901d88641a5402408118042100c0040041c1055514620700000300c0e840300007007011429a03211650341b0340105220b20f55082c0c83c0d041e010f28801103003100c1c000811504001103109103040c0101402d0152403c904020070425000810009503410746010400720000d004407104e083d4070704d10b03d045018110f4003 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 945027778 1250 945026528 945026531
    0x6090102030715051e010e010e040507030b070504060807080906190608010f06080f15070302071e050a11010e030c0f030102210403030b122a030d180f0608190f 70
    0x10900801c403d0f8102ca8400d407038a103101e080480d860380e03030440c10103028001e00d6680480c500c010700640640c0400c4c0b41d001401003040799040d80d582da8501c2034152007250441d00050b0f000c01c042004a030004060368000e01c0b98201210382e4a40b0070040d60303072a040200003c1d20100501040300d09000c4a90204015012120082c0090709400d07103082c01404051180030158882c0c081c0040d64000c0c0402d40da4043c0c24459241d01080c1c9440070104c02039081620250340a0090065410280c595030f40901152481074020385100d100c5030801100310401d0b4004541030140c004000503265a010400c0d003000d460441d00343d1070b51420940030034024003500c1c55500e802014100c40409065480080901c20f51199909024502480083c011504c420031240e000b0b42d13004913014090000e0740c801c0e1000114082950380088401032000070700c1c7c01188008500861f1110107041c0381503481080fa20094a0800b616098081c5011001010726400400b02c0c58446100d4200c2c010410300c036041182c0c1e24110000 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 945029028 1250 945027778 945027803
    0xc010c09081006060203040311060d0903120c02010501080a0b1824010f1d360c0f060f031b0418050708150f031e0109120c11060901020307 61
    0x1521080c12070045400d18418001c4a50490001e8041c080c25681564051410240703159580362039095000c501e00c0d4029001c1c4102e08022800c1c0c4a00007006001f99102c40d4200a0360b000501200c80a0f8504811039040c03500500c040074002540c141c0c456808450390b02d1983c1c820282c9017442e69803c402c002e0502a001401346803038203404010308151110a071440140e6070312800d080381a040f030302c1914074840d0034006800f604280d400342c440c0d001c0300ba4413158030300f040c3c550719901201c034010a8182c00d207580801544000701013000442c44800c8107030b5401c1564454180021001c0c000d1102440c0c000c000000003e2601c0851041c24590012803940d490f01d85440e400e42011202c00900e8501229281000003030760180b20b611500d0141503c02810243c1c1d080c100c05020008281d05400d07031b011310500c230011801060b19910b075407568251000019005610b0710740b185455400c41c826208208403c8a480041803042445400d121304c101d44071941c604266006070b040d03018412002c0d03c51869500f = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 945030278 1250 945029028 945029051
    0x51f0b0f070515070c021203030f04080a030219110c030a0803060904020114041d07050a090306270602041401050c0309010315090f0506030105100605030115051b0d0806090601020a03080402060c01 86
    0x584120917540300310380c1d0310710004c021501c0641d603020031280c5102c040604004103002c2001c0750000c1c52901c245141c0980707003070602855045a1441c00c83c1610001e075a40f5000400c200c0240046040218200c3c040c000d43c000e0707a12422414000130f05154403829134407001c103045a024030310760220b1681c039915958503566282d01000410320700c0701c2a074030410f124000052a0500c03030011105e043c00070391604142e807400c54544000074204154048005c10102494542c000400c450503100b4500c00d07080980d07100d06190b041840a0300320b0385070b941808400d100507000d0880100548007134003000c1c0f80c0003c40a2801080716007882d199070050400514140c1d15800c1011182c00082c42040c0650090005031244800c401c40c00b0818401c0e8000100c0900060000b2a200402040752940a282c801e0402d000d9010268900000c81c020a01982c4084003107440f00b600480d80703a6005008803a114164079017500042d4650940d400000c0404c019900090210741c0c8803000c1d01c012540b00002040a26001c0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 945031528 1250 945030278 945030287
    0x1060e061e0c190b04031b050604150e19060b03010c1719020d0221010f0b09030a0602160302010f0204050603162120070c05190302060a03051f0b0f07051507 69
    0x40c1d85c242c000848003140e1040e03101a14501004c0b20754000000c3c01d055646032100724654002c1034141444a03100e903600c5101400c1044503500d07132444a82e0300701c503200040c03403c0011242c2d65071200740603905088015a040360028036440a4820103110140c0a6075280c40c48002016205142d1031500e20114515082101d0380e409002079886c60510303140741c001051245c0320080b00134855043c0d41c551017034060210500c010090110601c004d4200d582e451000c2c0e0318072041e6082802d2382d11284070000c50303220916a090250740400d00303903020214a01030138000030038500d200040c5002154003900388422250f5100d52600350303652408a000b0041901c1030070318034005d0240ea10748013200d0581c05030400d034888404000c841445610140d1241918605400c0c0040d0b007283c65200caa0201f245c4c200000980c49917401071401800c1c40c3d800060303e141901d42c0d801741c1c8440c0c0220400800780c4142c240010140c200450383e00d207400d410031030381718070342ea2401e185014010030070300b00e06404813000d101803181c00 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 945032778 1250 945031528 945031531
    0x41a07050a230a020f010c0f0503030103030309052a06160c08010b03150c09190b0403050312012903100504060b25030e012303070801060e061e0c190b 66
    0x1102c041801568504028a948440000001e5803203c140c0c0b0f19100b0541c003c12061084901caa0044010300d415030311b40e036045800036401640802d84a05a0608002041c00b41e10440d1500840c11a010440086280307461107a0014031805a0320014500188244104210f852254082c14807100d140d00d80300c2c41c501a24040000e01e005e0710840c080090350500712a01a48200041c980c014144491a03040101c603001404140c00350354007050020461113030000040014500460055958440c12030000c102048140c0c0015095468140204040a14455007000c0325451f6440c15440b42c445910207004524140e004603446442c0c10000141f40c1c9108d00500703800526498021190b07946005903130b040b1100c540e4010001096801c84043c02c1d802003114104000c022044400d030a6060341002e41507030310594000000c5000100100080d0381d100c0000100340d007003a0b40050410505846102d11807050000b2040050000304024810b008200115602800c410101e54032132041c0d0b0070070300c014020 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 945034028 1250 945032778 945032813
    0xa020f120a1a04021c0908090d06060501170f0f070e030114100504090812070c0c061808030f09120c040c090303140304023106060909050108010b0105041a07050a 71
    0x514a002d5611468540b0a4816042e89000d131505402207000107070f8020724402400b281e00c2e00702401220010340b283d2900c004490f100f079100180c0c507424540013400320b1440400d11120100c6030700402400301c0e0542d0b165900118503680801d050740b594001a00c0801c00c241d00207030158038041c288207106c8a41e02040e0700944e89404c482c990162504284002c0d60701503080a04117600800604041e5030424104582c031140510304000d105d41a940c90440401c501d40c801c0002030380c031014250f031000f9020390150050802d040111729000070558483c0140c011003114a118421401401c00b20038414001c156404a00a204128070300c1c44020103003055040b8001a80011740e0140d8413018a0740d00011a03001d40d8008041c8040200740c04100700c6101000100140c0c2054040c40031301e000341c041c1c000c200260007c2d40b60303000d00303600f01443c010031642c0507401443c4980c10b01d2030f24649a40c0201c2120150b5410400ea00e5440c2c0040440d1000c1c0e104401e4000c14a00c00c900ea40018040c01d241c040b4401c60 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 945035278 1250 945034028 945034061
    0x230a11060405010203070b0702010b060d0605010e092710110a023a0302070f030e0117010e040b0601140a0f0e0619110c130b010201050105030609060a020f120a 70
    0x40609040c408980190701030503015901c10408200480c10040b0020f81c03049042c0f0021840c8000d00011415a030030640003c88115250745081c8890740c0c10140b10500000305542c05d004520389010042d030003401541d60103424080882018040c96070034000680d6052900c1d0b01400300c803110141011465118100000060003a5584641035001040d418120783c610504401282e40e07041c2e1141100030954800c000c145542040090001038a00d0800e1904030f0094030b803040c6040c020000907261031802c204a2000b0705065006000c0d16907205101c0b0b03003040e00007281103004c1d541d403401130780c02d582420104803140760007241b10184240d125900c01500d07070003a52108010f40c08682840040d020b2a0307941314071507166039a40b22207180314202c45452400d0050031544103a10f4040492130001d10801c10b0381d82e0b540c07298010b00065809028403401441c06800030101454880c030425110b07100684001c409513000159080070000301c0c41507031109000c0036003c0000c1c4c144070584100401e01d4400c981c07400d0 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 945036528 1250 945035278 945035303
    0x2009010201060b070515071224060c1e17030a0501150f021c050f040b04091505060f0309100e0a02010f0e010210181a0103111005090607230a 62
    0x4030324100341c4d0001e65002e002040c104506003c01404404010003503001c022450720a105445003500070040c03c038030380401800c2001c00c060302c141031811183d00814240b041001c42c040000b13100c0090301000f500c0c000541c1e102840d07540b52189485100300c81d803440e05c20380071060020410f0594000f904841211480007c903060b01c101c1507648282540100d00540c001c5000d006858664126102100d401c41c600785161051050141025400c2a00482c0c0c0340b1001050030b00c008801807240000c40c101c59026442141c2c40d160000d540361041000040d0ba8010100120300a80400c00ec2d100e8101e500040038401100da20f841d02c0c2d9030b914201000c0e80041c100c0118440e00501514160381d20b000c0c1a8046c1582c42c16a03540d010140204401c1c054550520700400c034040fa0030111009200e000858014000e54510305042208050fa454168810846406a0124160450212022446c06503541c54a481d4a401c1c01030031140f0810614001d0303640c1c2c5410051860001c1101440759200c2c090030b1454 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 945037778 1250 945036528 945036539
    0x41e080105220308060d05012f09030c0d1a010e0402030c0901031e08130807080708010522022d0a230111031e0403170a0819200901020106 61
    0x10088410340544070b01120441c40040f9102e203161980c00760000d0b00304801007a0658540b421284040281c1c2c40140d017440d0107010188180c20109a40d211807003846040c40f4408002a40351404180c0d903911440040307000c8030800c4061010790450741b41b20082c0f2041580c1d44d12840d0500901114224800d0140200c110768a1030000b007100d058a820013103c1015100303240c1481c2c2c800c00b251006852800707060081010303800d600708441e0045c1c0b141c403000d098102d01e464000d62030310b29581c00080403a414102088900280d58000b003265003400d03004400410850300118010582004070408039072502d00340903a00401c800302c600440602583c1c0084019640e0034950303e0010050010f1445003840d140d00c0184d0344c4616550084401104150380ca000f090100d41d0300c030f940092101501d10f0402150800500c22544101600160aa5042c030701d01144800020b000b001e00500c04c90079140f080a00d0350b40146140d0142001c46045210010b0744000882c6843c0035400c5004028010744c01c0c04000b044 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 945039028 1250 945037778 945037801
    0x90a1503050403121b030f090506040c0f0812030c0f071406010f0b09030c060c01150e04051c05030a090c080a0b060f0a03050607120b060a0c0507090b01020d0c08041e080105 76
    0x2d068417002c2a21851160210302140a071028a5400c40050388904845e000b082e010301c18140038601c01d014030041c2d18074100c814002400310b2785c8010015000001e00c0e0103042101001c0725800f40f9201c2450303984001b2003080b00414011180094041c0009803212202d40000207080ca06030341c0010b9a43e0592070382d40c2d0208400b4811841d9464050f04042c03c44a1a401c120010704012518040042000092102010600c84040d03000350381c02e01c000d205010507c041801002d9640800c400d230a0440340160364058841d01c80a441c0403001c0e66965441414448041e58010142040905941000d11141041c403003911007a503490344100711408080400d0325000b02c1c40011240e11070080c2800d0340e90341e442918018162803040070899207a00d2032184075031300c00c0e008104803800b03074640030326103503d50512501e891a29003082510500e000701c000c4031030303800161034240ca8042e0304c3c0044643c045403a1829181c0922362200c00410030183d00d070310a03082401440401d843d4008002c01940d41c81205095 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 945040278 1250 945039028 945039041
    0x105090c15070206070f2a0f270606051b16030311070509072c030303130302070b0f0c0d050918070c021f020d020c03070b090a150305040312 62
    0xd5100784818072524001c803110001d025890300007020141041c0d0705803600c0c03c01d4a02c1210803074030040c03c54141d040415825200850188120240301307183c50804004014004041c0140300340307074420400161920054a56403400c0c5201c490701030002d00c1d908d050103800b50b0402e40c400307040304450184012010900042c40090106d0394031141056901d0740c0c0301501c44030b0b1301180c120141d000b9001c01103415154843d01074025011961900d00d5021003d0081903487c010801240b40e00380400c0038034656039000000d43e6004441b00f503622a5101061805a1a00842c0da000810030100400e0004038080a0700191110194110644201c545450000c4035039103e212400707644034402d010000000c0010b8a0200e901c41124140090030491a4000840106401c40b9210f00309000740701007131155034140b001001010312800140b40c0c20a800c00003a85444207406120b01912021598200a903614407288000b4030542c00b8a281004001030010080e042c2101d0540109000c50540c0d42144803500c64030 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 945041528 1250 945040278 945040303
    0xf0e0d0906050c060a05040c080a050c01090b0a0c03050f220f0e190906020f0310050418030c060b0409080a0c03030b09160845060405060a05040c0e0106030e010509 72
    0x20265640d60741749001c000d0001034002d481040d003403000460301902c03c020507400580100001c005820254000500c0b0704803e030020810b0200501a100340c0b00d0300071243c840e0960341801d205481f44090b81d03405103640607181483d0302032600900d88141c0586510000e1050303441038000043c4c1a5120008484000c40984048144140b081c0b298400055103038001d07010b0304d12852003d840e05055211076440c641080d629101881e0141c00200990f01c6e0600c03c2d4031405903201201050100c2c03c0c1c030301a02c800d1101070050f1205868a400b1600b40d0f07034980c0f181050a6000d15050b8540c000324000400420004508a0210341380002009540c50107410f014440c8000c0e48660a1b40460250101d0f9150b00190003140d60380803200101d08040421f40d4483d06e40156100421300e0303c10040c0c0c680c440c0396581100080a508400184808100003003042903220a5040300401d09031200d2a01c960840703d00c0c0e00410306060709400110f01c1f29450b8226121610080f0f00078005601d0348946192642e41ea00080b = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 945042778 1250 945041528 945041533
    0x207030215031906090209031006060918060506030408220308030a02070c0801060b0d0501120305040b0f0d0507030515030606090712090501180201200a02130f0e0d0906050c 76
    0x20425202000000c1da88030743c4000f10301c0036505140c5242030994900341c012241c104e802040c1d60b001800c08102c0d4070a0210035500c140609868104098602c40090241304c4002c07580550710440290140c0194000340400b4210070341ea4034150409481c01d400400e043d10101000c101ca03034001007484055901981e8010208600d1612201012030007075015040c00c0340d030f980c1d400c0c00004005c0c00a02c81c0300010800198510356403203d282000c01242c805820031020000b010b042759002c42e502905440540780f5040059a9070030340103420400c00c2c0181d503503402e1641e041c0010090815810382089000e001c00318040709003002482c08054882c03208545692704401c4d08030008508234402e104540042e881d070000015141d50300d0700c806082da16495452040402a404070b0011940e00000560070000043c0c52046144000b210240c1c95203032171700d006440351070482141e100305c641550040e1f40008095508004490503d00c1140e2200800c0380c4407408a900c40b00000761840c010340403150b280c80311101 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 945044028 1250 945042778 945042799
    0x81e060609010e03060c190201060f06050903160306140601050c060402040b0406081005070e010f0f210504050a020307050f01270302030a0819050f0a2001092102070302 74
    0x18020660403804407541003294240d004038880d24280205400395105000895031940910300d00fa0003100d450f40c07120b045a16003101000080d150f0b090704003d551701490215075440382140024503000d00c2080c02d01000800e41000070411566078803260f0301c02c0c00c0e5450705803a9642c141c010b46242c051030300880348075003106001030010316150f80090381240d4002c20005038140c86014261a0a0b90000349089a030b070b4030005e121109410000c1124084000d20704098684c0a40d800201501608060001885450002034491349499901015805100541045240381c1420029a9400c51590a80c003d000c0c156020440e802d0010030024500320603140d0102e004190502080a0a504012984822548240400180c0d014003640c0302040c0500b0a032030321841e08900660341e0090410701c500900200b00100c00151a84006450700485c150030801c1d0348512036000c2c07211584981b40910015441c14a80c4002c026a560540c084840c40000400c100925054160399944040c000654454031000 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 945045278 1250 945044028 945044041
    0x403020c010e0f0f06040f090209120d090603050a060b071109090c010516050a050102030705030f0709062c03030a110c18060d080f0d06030201080f041203090602040b0c070501081e 79
    0x1940b82040c130b5070260a4a142640d038056500c40c04071550021000d080c0c000490154038a0421618001082038070040d100311078030740c203015140d1b002900c07031074090646600c0020300f02400e6500250040038000b103a10713030303443d81d0746001c5200056055000c1c0c880c2c4440700c08200007120000b22503801c100180c40d81c40c40e0585150800844c41c07819041150103106044180b00022404e0002d507000c2d444585811f0740782d00300009010390320000240b84004002550703c0812020780d20040320403002c1d02c0810140300c40d172000c0d500d070003da01c94002015003504c800900740e50704c1c607801041500c3d0552108246c487c0c80c113a81c410072615000e07070f0a50508000f8590085825484c0c045a101c260074410f40e506490184e94030300d000082e13006000041078031a91440300301f00303558110701c0c2d40d40d0080c80008000c680340350030f07a10f0f050001c4a5900900801d9500c0000108128065045401800c181c403841500d920800500316641c0c0844e0040c42d000035070490100e0310401644584601400d0001d0203040c0035642e40 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 945046528 1250 945045278 945045289
    0x7020f070b07051006030b060a0e071b030c0209010b030916180c02030412080711180a0518100506100c030509060a03020d051311011d0d02010519080403020c010e0f 72
    0xd0b60299881e00035941104d0400900d48100401517109420800040c94014100403160304540d00480700150f4610400030a0350b8070030703112030000c2c0f0503056280504a1504040715043c03003c0d980290062050b030004074103560b42201451003024818102c902801c08103815255440c0c0520413503d003a15181c44003801c05078180c0040c541d081c0b0b140f04903030800d40c0d913160088440410460903110102c001498000b172048968410010310b000742c88503082846041d0b010240000d00824500b4074503030b03a10210709140800c5a144d030144400d0303000c0b00c100e8900c3e04000307001850203440e014030503d0344d030038110241801988000300050b0941c40d01030910040800b40f01c91039000004de20200f40d800c002d50f804c0343c2e540d80b00b135a024012010001103003e42501d0f11144203030802c09003174140480300c00b642462014440d08000513000aa40c1020304844a10050311140648049068004806000b440d00710b60700c924101c0c441d5001e5400c0300d41c80210040103583d041c0700f01240941080c01070384005100c0c2441d = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 945047778 1250 945046528 945046537
    0x40905100b0f0d060c0318120215190b0f040e011a0d05030304111f050c2a060c01141305070f1a0a17131a0708011512090b0603010507020f070b 63
    0x26080100391105002131601d4107201c81c00084842290552341c840c021a41080319034a00c500d000c00024803411f140070213001c501c0540d00788051035615014000c003070341c40b0345007080039924029005110603212400c0482c00b911160f1070941003a8082d04000000740380c8440c0090340d00b9044006540746446a03181d42441405111405820100e030f40856401004074a002218501d141d83e00d076904c5640d0f02c40f1039401c14926450040c626a864071300000c7d01c0c1d01401c0403c200708000c44001d607840041c8511240988080750080e46510700c0e0404004a0046103151040d100388600d00361014541c82c0c2b41d1301600841c2d21700582207000c0c8070003008110311b4030349c10007058614040c0c01c0c995015540861440b02c00c0030112106a43c1080d50100401004800c1c078034102c1719100c0ca150180c403881e00c1e0200504c030041c1441205030022070350401d10a20340c0540b0350003401e420206c1d424000100b850400101c8a403054903e02d001e91302e8040051802071010031020800301000c4090044649003207501d2aa5810 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 945049028 1250 945047778 945047801
    0x20612090106050d120314010b09040b0102101104030201110d05070b091903030c02070512120a05040f2c1501050f0d050109060603110301140d11040905100b0f0d06 72
    0x41e00c02001c103d603620702c5080c0d10308500c6080a95085130144400805562080340220010805076006000502811082c0c403070341041568005111308503080102e1078010a0030b022520146049960981c1709204002071051780d0007030700d4004440400c00755850740c0780304d2404524000341c4144500c40018078030000c0181c001d4041e0003183e0442103444001d400d0046500821008a507503200381c1080c0503011f10a060040104803010031022045041144d200c81c02d0f428441940b0000007030b50f100a82c0100c0584015002c0818402d0340903803034132650410884081400c01c18404c0446203050400403142e9018403a400344e03071480b510a00c41c000155001c0c1c104641040041b00144050a28031841d48205402000da0b030001042040c0790000150850b2002162040303050b2040005000c00204d19000c0d0a10202c03d54a0100180680c1001042c0e0f80d282918a6030250403e820b030800d21030300103680202c0d40c800e1b803000c2284003074080822200e41d5a642d0095003003205008000080707841c61341321912020 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 945050278 1250 945049028 945049031
    0xf0227180a1a091e0c0a080c0d110703120605041e0b040e010c02010518030705030a12090b01080a0201080108010c0e121018031d0a03020d02130204090221040206120901 74
    0x182d00d00c00116a003004a813400c464150481503540b010f001025142d402103841040e451502441d81c4004111000040582c9074101d000200040d012015901000300b40c10040c081a807606075030302d0001c121120102015074441c1c10301c1c901103090f103002d00c5441c4900403c0c62060b500080b0180907003014000150380b0703551007581ca000304801007000f130166280810071540001001c0c03510800c00007400302e41525140341ca62041c4184000104000b04030fa91a51113810042d8613250111038a0001c1d00030084001c00f4100d0b4000001501d0130006042c440c010b100b41c0b5101c01aa8883c03d0340fa0813110350f8941071740003483e03a883c40700b56030a0001c05517400c540c4103000c1c3c07030b000c0d40802c0c6440c081d0303040e090110500554804030b000030306503c0b101d41a441d5003401c008114280040000419103045e6000c0070f445001c07a000e00d1821503444a00c41e034070000c1c03032340c0c002d40d1559640c400361002500103414480409034180c0c101100d1405481b4143c0c486c0e41c0c01800c641c141102e84809020442d00101250500e6 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 945051528 1250 945050278 945050321
    0xf1a0316080a1d0717060c04051e06070c0810110313140a24020909010330020d02010c021204092409051005010314070f030f0227180a 59
    0x14039010440c20f40020741001040180c0c50800300740401c1c0105141e40341140c00c008248a100c2c1481800c4800b11881290402030848059000c4d6120034410040583d104500103809810800d01c04440f40031241d14406403800e4411001090098034400b0303442141c2c500c41000003032a408580c10b071103560140280e03d000400d00d020780c0594a4402c02da0025161800b00d0201c261400350102d0448540c200900300960600303005801050010304103001c003c10f98482c09540c255000d0300c0b8980403114401d000000c81c82c1e4072043e0000b0b511070310707080000d100550030000c8420000d0300000700344011304000d101c3c0d11300c0c2514003003000c001000c03c2a26000c1c1c40040c0000916103141b80c0601d5006841c1400c8001414108504100f005902c15031100303041c1410011454500e00350860443d070b01400600b4051040725002c3c200700c001b0301040c18040d141c80c2c03010444880883ca00560740c200f0f458020700c150b1910100c2d40402c03035070309085c42c070741d004002c0346c440043d0030500550060300034264103100380c8940 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 945052778 1250 945051528 945051551
    0xb07050901320d060e071719020c03120603120414060304030c080415030f060501080f270f07090e0a140c060a051e0307141b070f1a0316080a 62
    0x1561000c4003280561391503001c1401702540c0000e460380c005001c0d08000750491710360308030031403080c0d0020600c812213031581e0007951200100d50100c5004550940580b40e0b0303601d00000c020302a103810f5034401d001e0b00c01c545c0d441d580301c0303910302c00c8034142c90048203d40b04502c0000d0800015500c000c20031401c11140c002c480c00000d0070345000e00040e202d0000c0444000f45a050018100c030340e40e02400e9519418204100315590300001c4003031304042c54a25400039941e5107483c0004442119452400c214642c06c4102e41004020412038652030500090b02c1e0751507555800c40d0160b460f59000c605182d0007205c828800a204820060321117000390f41540c0f503541480001580c65080701c06110b022820000d0440d580000f681800740c0c1c848100a801c90440c20051030040c26803045400f856070546000170b040e541c403a401950841c440310584100c1b07030029150403e103e42c4080d5072051011100b40d10721440c01d001743c01e0040d64454100e10020702102502d43c0c10898a00501408404d074142c0d4039001401b9 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 945054028 1250 945052778 945052877
    0x905190305040801110702010e1009030506011401110d02060c0d0e0327030f03030a0207021207060f2d121d0d09080705130207020a18090b07050901 65
    0x415030003526956202c0e8030b4466000d0940304030705449101c0000401030480141c0c1c0140c010764100e00165810413110903041819213a1005030b4202a000344a40300001030015030303121402c4203288003a0b031a103000d00100c4501c01d0343c90b03c45442c00c8015030008000181035691101c040d002c40185100040380d5100b4101c1e040d42198426072261060f100f810b0341c507141210581d40c20f00880d0206600800c03500700e02c128019141d000c041c0030410304a80000e265410341d03403030548000d41d20006a05507609a6a1014068499645281e0010114030104400e0405803003804100e2504a550510803481c0b03c140d48040302c1c2c48106902c180007443d41c030f041d514501d080c2c49915682c0c10507910014104140040c9020300b02401c160b1000b60282e001450912854941d4144400800761f82d040140c0c6440310382c4005001c600d09a040800d076441d040210a120308840d403c03540b00715001d4103c0e0091034a0310103003150b041c0f08400c400e9021a15038010100c0da030801c8180082d083d445024110001d0241c0000102c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 945055278 1250 945054028 945054073
    0x302130c26011706091509010b270112110103020d09140d020f0304080c1e0d08090f060703020a0212070b040906090e03070c06030c0207030b0a05191e0905 68
    0x4a00c01d0010014031051481c00d03150a00c80e0303282d5004102600c0d0407400b8a5540b8011780211441d040c2e81030201c0c6203080d00350800e00211100400410414050071041012100059645102803d003070000082c1c070030342450807619107900315811003001e02203440190080c0d8010302c0c00208071a07072040841e0101c3c40c0c095400d03840042c6a005800000c001c0800240b41c00e20140c0b442c11036070400c100420842e4800580b07c241100140ca80201c0001021603c5c03103e001010342c015000022800800100002d030401444c11042c2214440c00c22144401403060b1800f4401000340581e001507810300151921600e12004284104c04460000c0d403140e080e45400d403c0340e48800c1d2400e071102d0040c010b1810b41d000301c2005083d0400118203001d034070b0301d500340d450302d083c0320300c10a15596042204100340b00703022070005150000030a4030207007002030754080206400c6072101902000c0801c21400d901030317030145075661a130001c00c020000107015901d00c0148402c1804446a2040c0000001c80da2120141103 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 945056528 1250 945055278 945055337
    0x11040c030e3706050a0509071202010e0604090606050301090c0804082506020a020a030306050d0c1703040509012c071409030a05060f0402090702060601021b0303071a0115090302130c 80
    0x8900d9040c10179098060740d4024001407900d4124000902690b9407552070800b48907024640421209021400f0a0fa6403050b500486181814500301281041e0003500450480710800e504202c0707500b015000300c030405130175900145614010040301c1071103004c201d580d05002c1c03103084c42a424032100355038941c200e0307200750601d0300941c102c425904141501486000300503c016192184101401d640c0c5c20080d8a241c0a5450b180912440f1031040000401c2620003502000d0415070780f65845484000c519200c40d002c40030442000c101c0c0495169103c01d2040c02904241c483d24260b0440c1a0410f64580040d01010780512408001c04080f13842080628001c0400344004c241c0da007482c0c014070003803080041a41041d941311505216190340d002803c09503845414a950337240f403150800007030451056020203081e4811151042c02440c1520f18501d040b12010258001501d400c800103903805003480c40040d6004215800b516a56076072a0405040e00c030162508003100131440c0d401304040341c440c1041 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 945057778 1250 945056528 945056531
    0x2070b0a050604291201110307110f240a0e0d030b04020903060a050610020601061d0a03050f0d080112082d030405100f090210140f0711040c030e3706 66
    0x507040a0070005c42c0403d94940034402807002c0c1801c0c102050840c480500703454100000d070002220103a200b0701c03001c0d0041d650941034070303070300702484000d140120030114040041d84402808100d49051900c40d403615868460007400382d990b0603180c25002007240280c03483d0015020441d159640d5414802d0318402c3c2811030700054242071900038000b0000210750500195400035005000c0140c024002d00d03901402074040001403c07400e0007060303103070904d03a10040c103500c5007102d081c11299000c01c44221030010b6030380d03850061303984404c9080a008400c001802e040c80401602c0d00800f041074a602c4504e0408148661454100c402642c1d55030040f6825203950700b000c03400c000000114020342060005281c41404002c0081e0001892201c44403610000d0101c0900c0500e442000c449c25111150041c01080f0348513140f41c205a59460300c2040740b40e00c12494901c0b00b01c20765002c2d1040c01d90b401600002002e440c09103c0700300125100e00c0904501c1d5807400c0c0801950304000228219015205000 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 945059028 1250 945057778 945057851
    0x1915150f06050a2019080703030b03071404051f030c0609050307030b15031c050c0601051206180a0c030305071a010b0d021c02120412020102070b0a050604 68
    0x405103404039402500400000304602e640050f4826002d400781c18030604d9425020809210b1103140c44012004200004840310031102403082c2d010141c600d0b2402528184401311100081513240c00c4240141d03071071307061541c017040e40500342540540e0780855040d0030300002c1010b4844482104401d0ba204980e0043c051340203206e038582c066406d01c000d00b400c1d4003d000c0303103003541d45d1f2240b5820010800c5051300180580d86005940070081c800754928516013246001c00c1101c0c00800551141d0300c0d40399288030310000000c0c181071800c0105a0017a0034000b60059031101d02c0002417003108006c55003e28482e0706100c0e4003046140d4500313801544aa00d605982c0c03442842c1101141d84124098503a1411302070040020b61041c904031400011000b400580d259645246030341001000c614003030b8030b20f05c086001008000d44507042409203004a211a41c01080081d049003130303110b807420041c00704c51000041a20081c803904040d400030402000452011140610307202080380140c00340c03888580491 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 945060278 1250 945059028 945059039
    0x19080c120309160803030a0c0c0b0c181e271306050106020303040f021017040507081203040c03061a04050910060506040f0b0703050c03030f0702010b1002191515 71
    0x111003c00c0b007002c000c030112149044e00c280c0d1240402090342110a444103604507000f40318082a91481d64491004c0030745040c05032a03002c041c0c000403140c60b400c000a1580e0354042ca8181d100b0580e0240064644000107609070920060b200b50500c2c403400c030460011003c90902c45050a90301c62440c98a045034807500c07d0070640b064038030603402340c0159001001800041000087c0404203190180c85100c101d500300201100c00030b0340a002003803040207090502041060224000c0116134841d811590080482040d4032030710f11081c2c4004040d4442860200001b50aa8201d0f41170361020407200f80d014a0504082030035540b086440300203a0300014940d034185a4184242805041c09030348241c101402d11000f030801507000d00540c503c202d00811884101032042c800c83c0c42512250041da030700c9040c8242c52a242400507115580035509101110100382070200403c00c81080d0b9500422581c02c81004040680c1a011004c3d6228916071031718541c00b40080c041c00140c01003180d2200c0d000b40c5000c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 945061528 1250 945060278 945060283
    0x80c0a050c0a03150c0207080a06140a140a09020402120406021e090d0b09071a0a0801090203060a1205010b060412020909240703020702090a0b1201060819080c120309 73
    0x6801c4148100c9501805101240c00c20008031096040c1c00e60002e0015444001613140c03da1503130249090340b2803ca20a01000045c0d00401c046504d11408440c40b901e940c18120191051000002803a11074180000c40d00003e40c0c20942401e400948010300e0540412102e1140040c101c1d4265640d540005010640d10303c1410000d0031000000041c904120350100042c00e001d001c488080e10000840d00421007400090040600400385e41a98502084004103450416005410b4840110b8130260002401d240e550003120701c1071600030301d08560503040001900380040708050a17582d130743d40c503001c0b09900c5d1103840082000c4d0030000740340344140d40c03944100165010010845100c5030408d238800c00c0a191200651001d440705003509510381e645000044009004404029601403114800c1c040c054034154030070b18005105440e04009034a01104290a9459611902e4819404001c070100c400480c045c0304a110b81c440c1c1103003898680c00328070940c40c10b241c082c0d01d044007840006c140136a08104 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 945062778 1250 945061528 945061543
    0x80303100e060102060910020703110a120206090601140409083c090d0b0c0c01050705040906090902010c03120e0a0b0a1b0c021011160312030216060e010207080c0a05 73
    0x1340b0041c6490700d0840412602d407622040c1c008002600410385404050040c400400c00407001f1040b070303038038203d242007008107502c0030121000036003d0300002c03c1d40d20304c2c0415268141d841030b00c0c0d0318402442d520244002814807920645900d40d040c001030313030128900241005822403845410b003c410515564105022103070417502d1b150481000140810348071062014480c41d007040c40c542c6e1030781c0c0700002d062151049000050195180008001c2555001400b61090702c410440401406480308100400c0300c61000006c1d0119006440c9600064442c00324079495212500c804030716010040702d4149800048042112164002c4003040b0300c58482e4458006007040801303058031010b00c1359101404644608a01a00400d400d03261510380c140920590f800c206c00c20b8046441d280f100010105801840c1e0100300c580f0b00310f0980d0200e1203403081c000d17220715844001d900c916008280d995000100b101d80f88041d0195024480103010a030444013921a440c0c07040003420a2508926040341007000 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 945064028 1250 945062778 945062791
    0xf03170a0f1817030a1803020f0715021b130e0729070305090102031306030e0f0601080304120611031f05150a030b04140907030209010f080d0c0c080303100e 69
    0x249140500c001c5490440c3d405821401c0704407060340c903103490350440c0c00b40042c1d6940c0d81e90041c180c800407080546c0080c108032a0b840402c01d8a849640390008050040486440303400103a00c080741c001512001c0c00d10304242024014095048000c0c400c3c201e40030f0391340000c44001c880d00040300030480c0007100c0092070a201c50441340620300b00410001e500f03290050100c05010040d001c51a4006a402041154400900c2c00441040d0704c2d40c0e0040140a4008060214913a005048002c2030341c031000102d044c161201000a5030501d030800b08042d40c601004079043c0c8140d40c80320b0400c1e00301d00364000154025000c041280c1c128501240081c031550401d54011030064850480c41000c1200c0c0310283c03440c1206d18640482c100f07845000290240404040e8100b40414440500034008800078840341103d20035100071415a80c2c8415451180e0f1580c822b0b40c085400201012100ea8800c0540080e040d12481a400c0b0154440660078a141c204950520b110400e161091013000385030b019143d407044 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 945065278 1250 945064028 945064061
    0x90509070c060b1c0b0901060302091303020d110c120a080a05190207050306071b140105061504050d02090718090c091712161e060606090806040f03170a0f 68
    0xd40002c04c60000c1d001c0160003400c0e01201c030002c0340e0140020f40125000f1500204901511704242c14540510300141101f1005407041d04019100103000c2c0b000e82c0f481c056244080c0400c24000424040c070000381070b0540080e80914144980000e6464000e800e15041c40d170380d29030701c80e1891107000000c02440b0318040250f600004d41048641e600042d11584041d1030b14106411920031140b1854882001a0003403e6590100d100c3c00100343c15803045105040843c2c6c0500c2d4000d441c0540b144c42e2243d4001c40d90400d9082e1542005030a00308155078004055203081400ca0a829801e00301c0c501d80c2d40c01c110500c41d02c85412a1520303038000349840180c07100000c0d0700c6119041c0d0440d1030b524507100075407418200c800310340e41d08200001807948050f550091207040400c0b0f203280420502d0707079441c1c1d002c548151030601c021840904ca03d1904058880050081060751030340d440c2c1400c3d07800003040c11010042c0f01d02000307080560503849540071700700b080e0021940090034200c1c0015101e1f020803064106 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 945066528 1250 945065278 945065299
    0x30412080d11041203030f0902031b0103050606090306042d24062d1203020307021230130b0a080f0c0a030209191701050603010c0e010f090509070c060b 67
    0xa80e000d0744020136298107090001345a0640c011381006008200e00203980f600035038080a58450003050440d01c0032074241e804006a5440c4410854503000380c1c40c5070303134042e80090002000548244079040c82c0001c4400001000f4021929000620440700d40884800c000d880c03a13003e18100c4d070040700701080702844042c480207080042d050044d41030020065862241480400d404070040be0022010340501032926400d0180341c14082d66940c4906c500b02c4c0500701c6a08540b107001d20110f6281480ca00e1012001c1e4082c040300444801d48040490002d1954820401e5000903194120381d140280740340031000b0b448049982001e862031100030101d500000071030040104018542c41100c50030101400c2c0142c0362107804000c9005100141a0030b0308100409101146003040071a4107005180c1c540c0007800f00303586407010700d426600f40f480d84401054603c000302d86150b020311409002141c1915124151568600008040602c10354240303003c181701304980c40521036a805030310710b00750f81030710544103c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 945067778 1250 945066528 945066539
    0x1b0f0807050606100e1e0a0f050f0303070b0708100f2402070806070f02073302030a09120f0210030203070207091107060e1e101a0f060a02030412080d1104 68
    0x4c407500503130030b84100a5000c0d02c613041c0700c00090380044410047c0c14828056201d07805460f020707550b4000c0301d20400002407540131500d4000102c41440fa405041c002c201d0b00d410009446002020f0000c07049a64041e801150f0424940c00030300060101040e1100003410b2010b0305404461590150300441d044070f07800b400549d0f00001c04136000729191500680141c011401242814102d400c00901c81c850344800744207451860fa203410015201060652200c00b14080a0742e0b01e1140c15041004510000400c2240d0b038503032811549107030301070a6003001082450b4001850a8100d403102c5011075804000d00022940c1041200c01620284200b00300041c503103440c115907070240c241e004103083d80b82d411070181d01030203014203402d00350340c0748000d4580b103000c6111070380303a50b0f040c5601000549006403070801180ca0b0540c11101c100c002c2d10306100c0125010621a00342d01000f504000c0d448104400100c070003c441410103428050000513407505007841c016000d0350020301800c003040c02c1c28803042c0b01 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 945069028 1250 945067778 945067787
    0x10050910141c0c0815160c080d181502040509040602030903070506010803040524180102030915070c12030f08130804030506090106090216031b0f080705060610 70
    0x25200007200c4400012100000945410180c10861222507201c2c0d00010030025042048000c0e035410380f055580740c029140010880032400c550103407a2080c030f0300b00030300024040c080e604000b602485060b0314090541a484040d914884000e1246110310161001488035181040440e03032212401503213020302d40400201202c80c09040501050b5000001c00c110080400c02c403041c09034084141c2e14190ba40d4844c0e00d44903005032045a00607500b080c1400a9071080c400169404079500404905051f481c01e10070341d00b1101d02e5000ca055100401c400c002d141d40f26103852586480d40e00c0c0469860030b4034070309038021302e0099002c0c06400700c0c2003446100180e041241158228410300d84810240c2d40da45555868408210014140010005002c03050040200c1c65500c1841040e00a00c0140c2da200807440803441801199901c041450303429000191041410741240701c0c0d035401801500320281c444400c9400d90400443c0e00305c03c001885406c014007400b289600c40d2003100c0085219041c4d000103030 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 945070278 1250 945069028 945069061
    0x50108031306031104030c06050a02010b0906010804080703090b0301080c040e01050c07030c082506180201050f0a020f061501090617060f27060a08030304021516050d0503100509 78
    0x78182c60b404d02c10036042034074042d20021900003940ba8943d071350b24107010b400c96000305403040055003004540340342070401d1b0110074003030001a50f6080303803070341c880c2ca030b109080e0800b4008904104c02c038040041e202d00340328080d601030418900034100d045070b07000401c0100c40540c10740c85440e90500003000b511103481800e41d02e250f80c06050080703c800d560310f000502c1e40302d009074549804201d10460409140000c0415855a00c501d404120381000c0008841888070f06002c000d000610800c03002030b000d4a0b84015198000c042d00486441c1c560f050116810a403007203a00741c00f00121484010400d6a000d040d020090115042c1000181c4240c071580d01030f49401070a06000340100702c48600c1300c1e01c81c1c508120b4601f80030f02003d0200b008180010f05010001d80d03210744256412800400d200c900402100e0142e607004014412164008901c58000c0e001000d9555441c0d20007075802c0301103241031100380810709180e6989540d07072502d075001c243c0c6c070300080d0442400340c00d100d400c10100c01c04051004 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 945071528 1250 945070278 945070289
    0x90f0a0b160c0501020a0804060e21092d0a0e10231806030606120307060504050a0b010326030402060d1505040e0312090a050d0f05090d03050a030501080313 69
    0x30030240465041658102c480e500010b10541c400142c1d4401980d00010181c040e038840c2409000380030001e1016661004161104149071011140c1d80c04480341c142c1c0106084100500342c2c501c04014031040b09030201091442c0d05a000b2041d11100031881c24008050281c50a8840040c45040c003480001500d02c0d82d000e50b0280300350031140e07041003003e0301801512100d80100304902d814a006102e422034801034901d00d01071b100f0321003c80e259241c51440c1e4485203035008015802c000c2c2586511000d8603002c3c0099455010741d18106000c590700c90f00c1140a103000c1c500c228030841e0a0001c03044400a50700d040384200d4428403d100c0160f540004403000c0540c028070208203003219000400348900a5884580d00c00e10b8510030300c40710800400903000c00841841444425a02d64080d6920780e2080e401c010210341016490750309190240c0400c11407020f0034500b260901090001064026500000c242c020800202d0b14400c00c60b0f05001e194050032010002d10304201341c80342540e03030300c03007980c001c1 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 945072778 1250 945071528 945071551
    0xe04050c03070c110301090606060309061d03120411030f0a031101060b0a030f140132060f0a17040b040b160914010c05010c0809070e01080307060513050601030308090f0a0b 76
    0x50b41c40645d000d4012840c030350f4014604000c0d280d940e04001e8000c0181034012070394941000d41b0707031900c25001440e003c94144548082e5240800318451082c518400400c200ca400040c04500c1c01651000c0011603841c142c080300520390300225003406000d010603400f8020703003a03040003014000016880e098400c0e9030f200c0d08011405000081e514400b4005420b0504c03d01c2c554000001018801001d482e0049a80c0c140103d80c43c05030074010341c505492008149030000410040c4428040640c8014080480145041803026800d01030007a44000103507402c1d00c0c0b00c00000c0921052185040d082a040017255501d8003048801190140c146442442200306600c51443d852b000b0782d008400c43e5416a03401402044682068040505024029030b0b12002c0c0344500c00380414030b401898a43c074140e643c034100030740c14840103a9070170b005801c004000c00301442c56820107a00050081008a010311710a480e0452145024140d461034500c041c031451a159001d1a60400860010540140c00c012031090 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 945074028 1250 945072778 945072803
    0x607141602011d04050906010612020306030c0f180103060902090a0c0c060f090803090a0b0c0c1b310b060f040e04170f120105010c1e02130204060e04050c03070c 71
    0x1680710005031100b40d40f0350458208810403c50080c04200141a07900d540c41d98140000001514422800b080750055015803018010700520300d4a0329007541041d100030000c84003014500070200e0800381c281d1089480350f480d05d107084114505101055440000c1c2d201c00c0001401c0302800803e03008801304042e0040da5100200d02d602000394100e02011038005000507a41c0c2130102c00d10b0781e02c0c02c8812003512040c3d001000703d000609460212401030a40400925294a180e04c85910141e00da0701c1c160b034409040171590000301003445040040c070340b0100c842c00044402900c0501603803030802d82d540c451f580800000041a54800545095030041c140744440d664961410021101050705401100d40c00418490b621300703840700080a82c00310700c00444c00c0c60790b41c0e10010f55024484990090207810768117044441c40303241e100e0701e0031141d0000300809100c00703800b004c0320200d82c02074000c100042d04009440700c4900b001e010741c2d40c000300c400000d43c2c82c620341400c00804c90b00941000070000d00340e924 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 945075278 1250 945074028 945074057
    0x7080d0306031a3d06021608060124120f021903020a050715020c03070804090e070e010e070207231c05120a030b03010230010803190203041502060714160201 69
    0x1010030740c0420300301410004d10354603030701d01941d11130400b5915001044003050206025502040c158121000381180711011002c00140400420004078050300300314503c0e051a031008002d003d20403803416640c000598031816074040e02d0481000c00e4150084c14010888459180e034090100c2e050240c02c03801d01100311440042c188041d20030160010041c2c40082204000e0000c03550050085440341c060401002c481280e5482c3c441c0070780c0c4200034811204c50010020902165052a803000851040d0f0ba0001e440d0102900810301d425803110324002403006035500c2c0e041ca00410f0303102240304c0e006c000050040d6620750b6a6900900c0156041d8031001c9401443c0d0350007031700080c0c503134500140250b459413001d60000c2482440c00f030100440d2551815400a4400700740c007142c2c10307030f8a0758002e145070401451103000c0981072015030000b18030040000154007104100d0205992210317601801081c101900000d021603000251000103150403c400007070036006103544580301d642800c1541d030320382010 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 945076528 1250 945075278 945075361
    0x70c0b25260106081e010b03040305032a0406030f1a06160b04060917270604090e0606030d11070317040e04030e19030309051207080d0306031a 63
    0x220040c0c103040007440c004100307140c00403003144c840c12140b1003208035000300ca010310308104400c0c403411201c00410404100800e20420045610040080c154072011400c0800718480d0450b861026030030b485c0200c3c0c01c0c00300540c1070052548200c0751a40c203110000396941415103217144c5030700140c410346000891f82d80d00320405034071241d09130f040070131107029141c81d00340b440180150360380840f24404031003d4255001100c105803034610f4a00b98507000c050f83e0130851440b01e0510719624030341c0020b0500c070004940714140152422009920094141d078201602810b01c0c2c5440d030383c03042050045a9030480c0c0e00d2030300010a081102e070484090810801101b5010081d845260015184900785008100c01d1503001000000e01c1441961080281a045000c21f5070001da107000003000130741c0c001420440e80c07400c850740fa000d080c4d550003510301103551071840301e1602e030704034141001282d110071080060007440f01f9448212185150381000519000802e02140300c4c4000601100d01008041d016800c1d045 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 945077778 1250 945076528 945076577
    0x240c02120a0915111c0e090402010917010603020f030705030d120f060311180105060a111203040521120f0a0608160302041d0c27070c0b25 61
    0x1c02803035001c44043c41c1d41c0280040d0010456000500c9141c0080901c0030782d081c0343c46190105a0750300354811444104102140c040640140d040100d500b02c007061502c441c540700c0c0c203075009980002884c10f1451040c801c0d60200c090b00e0b00e210b030304210401c21258070b0224032420300481038500b0700a042c0342d2107440b5000703240c51904005101d140142c0402000409004c3c1025000c0807984040070308100340d180c08402c1400d00403580c00540c03e00504529134000c44106440c00d10f042e0540768041c6018014034015001144c00381d4242d07129141c1065121959903202c0c01c01e9052100b1589002c0c80c6414070034414001070118110440e0b01d4001035400d82140d40000f024200d104192014410101d0603040401d00501050340f2840c40c22070801340101000152020403403254000e4502401e920081003090340c0079203045070051101c00000b6038040c0030103801d20310942658944413110822410502c040401c01404d2132000c1c080388904508070208052001c2c11810103113803140c44115581c026a00b45240c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 945079028 1250 945077778 945077789
    0x60507020d1406040311011d07050609060d0e0304050a060309031e020a020406080606010e0103020405091501050c0607030f0b120715111903030e0615010309060e0604240c02120a09 79
    0x2a007030a103c10168810100b403118601c071b80c02400454004140081c003142800101c1640d039001820401c80e6040c041c000d040189130051129003044200e03000c060075a10315204801a071340000405014a29110a40c40090801441d04000d80341c07143d680500300b41c0f005021541a0031420381c2c0c0040303252007009030300034099000d0024040c103030360f40c241c8940d1681c0645005021a800b240d1002d415440791081d641100c900070420105510742c2c0f16220141c0c0c140b0500c450400800300036181100d40200402c80c042d682580d00000d505096116440460750308100f007a02c140c00303001d00038641d00800100d180c00e88045140300700c41e00d05003940c10390303038165040d44103801030080b103a00240d17055030703241100c00c414001d480620030b804251605541303c160844110341c05018007031085070a54071980c01024400d12440d00041c0540f0720b100351074508041240c0445400c1d64102411500301a510003c2038002c01002091200a5200e90080c0d01c5a60b2860714014225000c0b882600c443d1150114000810 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 945080278 1250 945079028 945079033
    0x30b18030a031b0f171f060801060e18041103100606090f0602010207260405180415060503100b040b09040309082a01050a21090219060507020d14 64
    0x1030520401034094140e4680ca659510b81452803000440c0c058984c021008a0b81e03039911045010740e03004002c1181001d0704944000d00b1140e25030030010480d4034a540540312541711804558502103005280007500140c0a0090407003140403103081c070741d43d00013581240c0d01002801c1c50885c508082880c2001c280c02d000e410031f05001c40010019040480d500c02c0d102c0810b0304503481511508140d0913403083e994000d0422130501486018074203c002146103030040c04407168603042c1d440300080d920401c083c405010444164061208100c111103c448270001c43c80014087c0a1810340080d4a41d402d4903e801d02451711001003481a96669008888101000f03001c15030b60306140c01c00902040c51401040c0b0345119030100b070003070301d03800490040c140540e001420320012161801110750340c01c00703101c25003408013a02c01c5041c00c0d840310441c8010412034800010300e00c040341c0100513183e0f41c5c103032480d0220b080403541400b40543c450200d07145e182d016117240390200083c1c54028008501c44514104a0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 945081528 1250 945080278 945080287
    0x11806030f12020c19170d0504170a020901060503160306050f0415180b120c0a05010507050313080d02010b04020405031009081306080f010510080a0c2f070e0c04030b1803 75
    0x3d017044840d140a9030120f00340c00d80d48120101541da84c0d00c5c0140d0900020920601041284140c66000c10503035403408820786100c0000390b0701140c00c114080c0c0081d0302141010082021110080d0b014601c2d8414170f183c05d200b514900400700341c12190502c00c040c012030711b40e060a0350749018083c0e082c00903c400d4003074102c0c0113800c001c0d006c01050741e800d51501c50080d20340c002803444000a14190380380d030001e029a0590b031503c00159525444040e084602e0300051110550141010030084010514600580078480c0c21040003800c448401c1c0025124900c144014400c0d030300c001400d6410610034110016000865007450703080c80c00741c0d0724148240f01640e00c000c01c0082e48110094000c0c03c011008a81a90f264400c00940411003580d500011310300c000091780031041d030340103c072a41e406400c108411130058058001d00201e811144c070400405038a5501019400304100310003860400d4070f01c0d240341040c0301003c0a6108170702c405420a49002c0100302d400c0002000c42602d2040340003201d60340c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 945082778 1250 945081528 945081559
    0x306030f12070507050d05070b03040f0f11090a02040f0b03370f0207020d12180803070c080606090a0c05092d040e03090618090106020303011806030f12020c 69
    0x50b511460040b40c0901a210000a40c1d04050b0504504160300c44081c10b80345c0d05081c0044102c1c1c00c024001e5502400801000e00403c42146288240034000c100801c160b80c9040c051007504a0b020345000b000e5407041104100800c200ca490b803080e01c120340f00701079603030302d520355072460529080010f040034003481e502c00c0041c9520b0001101b0030002800061000089018461049000e02580a03403c1720780c09004800281d441400c25151100c141003090b00c040507882044a44c44468000710603e900000d0420140700d01c1c540300340010f00e46280202420b01d08179022940120300070b45580b01923501c4420494096018505503040d02c0405018001940300d1032180080291403806d000c80507412104072840c407820306002c3e680000c03500c00025480d1105002c14001154401e08882e400800d4558422480e0f956502c84e450083c559940190b8407541041d507488a4a40602c034805101c2c1e1820400f000000d460900d003843d0a500400100755a1000500690070195540c00a80c0c0c000500fa185011 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 945084028 1250 945082778 945082813
    0xc0e030d051e070c15081303050406050a12020a03020c010b03030301030c0512011e05011d040b06010c0c050d050f061012080c0c040504050714090c04171f0504210903080306030f 78
    0x170302d403a05070782e5040d0341d80f40c0c0780c450107441c4000f0b240900051130410051103600c0c0204014061a042440d2044a1054882c03514040380c0001c030140000940000e110940383c4800d000c2c074102c601c000c4010f075245515656900c0040342080c49207500941d42402c00d40005c0c0001c0d1f00034081d21414500031126841040ba181004280900070901e0440000340000b480b0290415420710503680b2012034070207a11001c00541d0040c211201c2102c44040003140803910751a070f1402990350910071001002a03990402c02c0c2420104010708022080444030010000d840c3c0145c3e8908206800c400056580d0504498060802440103102500103003032805000030404001740d1002210100e00c002010355042c01c0030070003400400c1e00c9074040780740103200c140030303203a81102514003580c4181e0840d0402c110034807840806400030712070703450f03110364450400040c000382500c2d486c000581030040b0000001c00364009410a1491702010b004000e000c800600d040d1420094a41c030390145104480c140d0f88440c45190 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 945085278 1250 945084028 945084059
    0x3070f180e071b1a090f150103031b0c030602070c05032401081204090b0d0515060a05040b030d031d1e2512081b010c0e030d051e070c 59
    0xa002035051003010324042070098101441641c0011519a02220340007131300820440039103210300030302412112005542013000300700040c1105d208400260341c51030502030050504601d80c240c103022302c21054400201c400c11140160303540501d005031a441a0b06140c8104552030b08003941611074110310b0200c0d0303045021440050b012191240c0b030260b0b00c1d0100240c132840c414501082840c001d00c0184a41c2c07a040e0032030300d400000900450310b500c0158480a10380100001c001c600465808148202420940040c1d800f03840d041c0d500307108000c0e140e00880c0d5114200c0400104050390740c1100700d6201500600d003c01d1028882c21038840a44401e00e0148030f01c4403a2104c01d90384941c140d103200039401c0c001c602004100451036240c94514181c940c1c20340c0c4a512000301e402c20010002911030800c40109803c800701c00d44000201002641c102414006802040303d01c254401c4084104040c2d02a0854040380300d47d82c085900304000b00003854450186030b4004110042c0c031400400c0400c01e82520703d = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 945086528 1250 945085278 945085291
    0x411041d0606270912040605040f09050103080d0518120d050a05090319110105040309052716030b0d080717040608010905060105130b090a051503070f180e 68
    0x120303200c0d00c2d00c1c000c11515141c0503041c110190826640d500140040c060350781e03071282400040d0352041d124140c40c60199800b5800030070201d080407134140240c0710184160405814844400c014950454035160501d0040040c1c0845c0c65840d000020502c80d100c046600e40b4480d00310450310144000d44400e180da4000c00c00014600e0b14200c0001c403a11140d001c0d0300e0065071410061490250600c40408100c2c0b8600d006a05000c01044003041e185400d21410740310324000d0355114841c6040c07604114030300100d06102e4411100c800c0580f07070f8100e00c0d0886682c1040100d4012002c034103046a007034024040541074140d205d403401d407940081c44420002043c13102d02c140c22865624144240c03100c081e010303030701032030f40016445801486000100d130b0040d504031805050542c02d100346006450f03480c203250b8105a584a1010440300c92a081c070480d0300000d003038203d1b00511000b4000c6184155400000c00d20801c200455040d040e60a006600c4200b49190803040e80c030243c0e4480840e50324401c0e040d91792 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 945087778 1250 945086528 945086533
    0x14090325060221060f09041a0c0c1603121110150b0f04030515010e06040b010e0306270d0c062f03060a0603140601030507021e0f0c0a03051002030411041d 68
    0x9440149000f06c0340c20300c50341d4460218541c061518060b03600d00c0c2d200409103400080c04100a5000b0402044012130071070802d13850a450030f08514001c2c94030310728501b160b0240700e501c00381c2d445894030100c1d103059800c8103c0c000042c0d8000c0040f40390081c0006520000d41d0788800158440103003da80c004105482c019012541d58408118203403050036001d204503100c11441c1004135006103055002440c64074014500017000311200f000203800d00304107550402c83c41d4110038240030301080c01140012031000d40ca019200c0d1280900e400b60034065104801003d0b141e40b003007072042c001d00c004008155807140b61207034642601c0c6100c447d48942d1099030002c0c0b280e440e41000164852181c0250040d10f800101c1101c2e0a441303090064005d4000500750000794081d06002d000300c2043c1f9003480c884111030100510b000100811124200140a04210f0060010000c24008a040003840341440011300d000144e8982da1400c03e0043c00308690602a8400e090100c1c0d006007000c241c14020008000c4000d = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 945089028 1250 945087778 945087799
    0x5120304021c0c0b0c03091e010206070309080403080a050d06090e03121803040b0406030501080606060409091a0a0c1116030b131209062d050f19031409032506022106 73
    0x2304003007460f142c0c180c0140140e0004001a48043c404c0d040000c495114207082e609054aa071740e181051b41040c081f110020b01d0100d06424002000d015000080868600401c085c0d61b00259060322031142030304686404400101052900448200e41c6014298100c1920b8485446000d020541d40c800d204120009050000108150fa0040b0710940a0b520042c9401d1a0a14106440c00a000041d2065900d90383d103e1480d0341c00d01039248250312540b251980010905100b10000d07082c0208500c00601650125280c0550050001d90510540b078020f9502641581d501c840b040110140d49001000038503000c5194194641180040c0d060381d0303481e04c0704003401d664190000000001c141908080302200c003800d4100c01d028800030a410480c62001c240703007070903120920072404e01d2503200c2c03800a07a0b075100e000c0c6160b061412154220621001440c40c082d03c0210004481c0d419030410700100c441400c1007420080035604440b148980c50812000c5001c4c213605600e403014003121814002c44401c0e1 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 945090278 1250 945089028 945089059
    0x210212010b01050427050a06170f030304260706060e0106031a04050c0d0207050601090c0f0503070e0a051e090c04051f0905130905120304021c0c0b0c0309 68
    0x24030715540006a5900f418946400210a40300c20100300171048101c0e02245069603401a00805200e20058500410000d160594500016070307010103101c25a007000104c20000e40c030200440e13400035089106240c1286d08820410000c0b02903501c1440944000030700e090400ca15070f00a00c0c111101c140007004107a80c0d0705400d0f130503910480010000c444508040207014545940184d03005a0b201c0300381c0d410b010742c0b40c0641c0d080f0b9000420544113980104c00401405100780203410703c000f1586010303969090441c4000c0c00a0102030095010300c0b00d030300301d440b0168803030200040040800030660000c21580219036007c07030380400d24150050440e800003942c001034000c01c0f58102c90000e04580d04802e0320b8145948030a0000302014100250044000b401d40e82c0c074042d000c03c0042d41034001515008501d0301d00c1c40d0402003040e41440790402c0c004c00c00566a0f0118102c0d000d0003140c41c0b9030300c02e441864481ca070540d440d00303c83d40b69040800e940c5c20100001010b400d10600a542d13015818500303d = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 945091528 1250 945090278 945090281
    0x60304030c1217270304030c03050d0f050d0b0d02101805010f020a03081504020c030c070509130f030315060903110301090c0b0c0c06071a0604060e1f21021201 70
    0x42d102180c203880c078030301040490350010650349402d10782c03507040c40c00700413220002810f42d031081e4010f5036040f25403802401885003d208490501d65203060003d41c100062070050654020207181e10a601d5407041000d0f01c0351a0701e00040d000540c02440800c0c8000c1013a006054201c0d10070800b007802d44101c0005c101755000718080014030800b80c0040101c641c05950440311064010038940340103e00305400c1d003035504d41e03001070582c07451920007658441259a0441d860070a59a00443c41100340005005880b00081d6200f00034a800048001041055082c01d43c0504804c840b0491070500481c0001b0340e03240d10881c4841681d100314841c00018540000f01800c0c5c1d0710b600c0c80504445101c040030081240e1903070042c41443c0011003a03544001d42400096550707003005100381c1c2c048801644030446000118501c1b64002402c982c200416030410366140e49002004148a081551030f2214440495452000e02c006100f4008010701d0202040614800c50003d00c50484c003c000d1000d4003004400103 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 945092778 1250 945091528 945091547
    0x609010c3005181e060a180507030b070f021606080a090b04121409060d0b01020a05100606033c060905090f0624090a060306020d0905070801020702130b0609060304030c12 75
    0x42402031034292201c1243c1b400030b002d104002040d18030201c0591001410510403080158000e4190b4910340c030706150060840c4504c03a1541d82190080070700c424543c0044409074050b10583c0c504450695129640e8030b00600180c5000b40011081030108406c00650303c9800080d9000c0b079030341c554040c4000100c40b000f4041c2c2140668000300a21426089500c2c41d4040445014144100c0f2032021503621418208403100d021507080585501081c0112030b050300405461403c900c0c071101751000403000f555100f80841c0c1280305006845c07001c5000c9003655400c143d015010701d200410039411310080e03641d074420181556080c00c0c06880c00244000740340710f40c52084604256200d1400ca041c01c070800244042c014055070304195a40d02c0480031800901c050451390010901c0001da10803181840b503d0285294841260b41c0e00410801c00140c0701c05a042102107851640403852580c048006032040c00f0300608184c0201700401040103050b404200d121515008131100c80d182c3d180d114003200c1c0102c0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 945094028 1250 945092778 945092833
    0xe0a0201020f19020f060417070920030f06061b060f011410051c0e0a0c081b0f0d0f03082401091403010f0c020c030609010c300518 58
    0x4043c0300801500b0310f55400081444014482454207031610b00c0401001c20240364010168090b03c400d018003400c501c00e44281c102c42548420000c00700e03440d410b005200082000c1844846003020500d66180e00d0103507441c2085903180103840c050803200d0350b80e0b640c0d400c0f00d42d00c80140c50360000085809030b00701d21840c80750b40a1300005901004100a0310385501242100800341c410014014116460348100f5286110030b1010b0174001240742407203500c0d000c4ca50040d4481e41c00a0140c1d03582041c2e108200d0200c044261007184d009496640002c450001410b400f030034a0484901d100101a0700245952003880b030050740100c424907a4140c48651031400d083c032804191410410f2100d041030038034004000100034000310740e07401c0301142607080d510000040e074003585c4001c0340c0200038034084c880a0340c081c00d084002c0088260480c1c000344000407460100c80072005420358412070403161520100b110103001c0080c010340c03e10042c542c1d1000d50304140d10549002c2c0b903129214603030140b03898032209107 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 945095278 1250 945094028 945094063
    0xa11100306030b093007030c080409050c09100f021b03070314210702010c020402161703090c1e09061f0906110d090b090303070c090b0f09010e0403050a090503010e0a0201020f 77
    0x91b100c0d503050f2102e40720134009407095041030000290701c0099014013840744885602c1280c031803007158184044110044500410310a00d0740082006640c000b607240c40300c2921400f41140034800101090814410ba00060310710840803512043c1d102d80020300c0c90b9807045601c801c0050360000c4800215502138040c2c000c1c0010178241800300940703020f07006824809890030341140da07a07607943e0728055081d800711015502e40030040100444003200b032041c103d51280a0711a40d10f9241e04074000b040480c02d2510b014130a0221101042180d00e6140045c9540c0c604001e8544040b600c1c0c5070042c2640c0d03154070804000a007000c807176505191010502040e6a1204d4075000c81d07031400e00c042e0082ca50400c0101035014402804035a012403542850078000300000c010000d00703019040700740600c03c41c0c5001d58034001c0071000700404c5244581c0c45496401501458029241c0109000440d982c2d007156200070790543c240300860003440000301d00301c42c0581c130136001c070381400e8101c680e0152141840d102091100c0c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 945096528 1250 945095278 945095287
    0x919030506040813080a030c02030106060507050a0602070f080a0201050103021f02061923060f0904050316030c0b09100624030e1c0c140a11100306030b0930 69
    0x3184075001d0581d5000103205100613503250507101b860060f100e8015130009031404042801c3d400c080c03007144060140b6250083c6004510340f02c0941c0c03065100c1d030090109600040807000e00c040c8001280069a12080c01070760745003440c000a01910080c0016071150700740d0b2500011103040c6440d040015000382d005060142d0303070b262a1200482038a40c403442d21a840350010007510303000051900f00e0a607107002c100c0250810742c007401005e030640c510f036a0150012806000c0424000020f551014920440104442080b450308a9151010f400c00030f00c0c0c1b0742c4050a000b1090004600c0e00b81e01c07200540c081140781d6441101310448134203146000b58642080441c2284103100390070039030a8030108400c1f141503006000000c580d001210104000041050b1415801c202d000302090814012050084c8824642c9485980c4510a04d4419030b10034022504031003840d81c0070750010300003150402c6001400b0301e05140c609841d92581c60714003079001180d1940c4c40b043d9200d06801481c04011403042400c1 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 945097778 1250 945096528 945096533
    0xf010303031505060c01061a0a2f07120b1e0105060c011b030b0a080d080711010f060308090a1d0105010302070510020c1c0507150b12030f091903050604 67
    0xb080085540d080e4900d030302c040802c0c0354a510005148608444000092a038a80200035100c000e0a184580101d101080980c443c00d03880301d441d083c2c15284903441010040c0c0350310302c0c250041e00101d04600c9401403110000308440c50001c180c0c10f040c0964498030303883d03841032000c20140c0d100c0042d048120640100502c4207007003500c042c00c640742008000140d81c0c0e502810101004000e895070740c00282d03c6101c660441e0810510840c014802c102c001c020361b01c2e50b0360b409401940d0081c211810030240842ea0700800ca42500250080c461144c0100000340e06c90401403807650160003614003a030b204440000302c803c1c5142491081d0510440c0d1401c05074240001100079601c200c0095a881c4900c003021080000e1505c003c000c4040302100400c4130981d044590006560070b2039010081c80000c0c0030b00c01c040345150b150194210840307440040c865400c2000110240203680040754180300201e0981c040218003c020f01e008201141d403a21100c044256410b070b5141c0d140401001c541002021500 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 945099028 1250 945097778 945097781
    0xf0306040b0a0b28050607081e070618140d0c06020f1b0c040606030e0604150f02120402091003150504030e0d03081e15010c050309060f0304030909050f01030303 71
    0x20800c0540c2c20114401c4202e00c0000d03140180342039041c1851520141c80d0b000108040000001800c05448184c10095142c41e60442c602440c54070060f00a01e803000c1185900110342160003031075220000700b0101031001881c0b130f440481e542040b01c130038044001c841202c2000017200c41c05900156a2180080c002e540c07520041e400c010f141c1900d140c8240400b191045400c4001032444000c24024403017180c22a0810042c0e4103150b1043c400d262800744082842000410110350154100c00187c110b10b5a45400200605c14070042690483c401302d1280d0b0310450f1070071502e01450088840108603141c280405400b42200c2c40002e00c2e00000c2c0500b00e000c441c860700000c0d40140641030180480c83c0701804100015401c8900b00c2c00a0019030812021000045111400001602d09c43c0e01914150300b5503500c0e0355000260a052084c01d00c0404d040020030800c8403141003002d00740680343d000e1459032100340d07041510708401042170b02c2d00100741603042d84500e80c4100181c07010001c00382d195440a80 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 945100278 1250 945099028 945099031
    0x4050402070c03170d0f0b1018030606151101051005090a06080a03030f0c08010602070b0f0904061202030f03091c02210303240a170703140105010303030b0f0306040b 73
    0x4500da0314191000020626403044140340030401c8840300d9440170b00c0f2071440304a90101d02507203049450059501ca15031244800806540745a00f0603080c50007400d491415060002c0e4030043c0304604000700418003002585e20382400c1c41058032000101800801c0007401d030b903812103500c1100640c00c502000a441d0804031580c00c40601c240003c1c903a626081414106206480d081c1e0100351201d82c076003d65001803180c0040c100152428014070b5042240080d15007201c5d00c00c005800c0c0000c00c1c4d00000c4a03003032084400f000780c002c10030410580e881c00401030810141100381e100340030701c00302d0789484d107008011254051001032419900c00d681d40305805000c50400c0c0180e8110807104602c5a03e02024030481003984c0c0804001e503201d01e13103c6c000c01c41c142070011441e0010306009500c480261074802c2d0400c10359000d100c9500074001c030242164584242c0341c0c40a041540300c0717002d00e003ca0006500a9060385e0007642c05001e40304041050011459164441d47d4041d4032000000b0042000c840340c59 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 945101528 1250 945100278 945100283
    0x3031e04080d061d061e040c050c0a0b1e101e051806030f010c0c0b0a200414061837050a08010c02071221080f070e060405040207 57
    0x8605200088002e00100c0d8a25040220f040100100100c814150340305540d5004100700d0348880c3c00503070030081c400307185000c85035a40120703140c485040c0031901503000d4580b640d102804540c9070300da46003480040c0c1c000613130318000108081080450b526200047c0e0a03c00c0d4070fa0424225090b00c5c184800010b0410041280c40c24100240d010590390b85e0500c030710b50b40040b1008d54011a040200405041030ba0740501c07855030f03a252000490b1410340080c0d14118282d0000101d0809075070b902c8144004c0c0c0340c07030f05401c0403003040a203e8011910944c40503109880c1030050a4520546560611900780710318101c2000f0380b00000c02c900c100b480c1010102d0603015501414040b980c851051841401000a480303c01140c0703003032010703c1310707042c038070301440003040c028000b030014441c0f100c801703526000c070350040510018904204000340306100c000720041120840d20036200020401c1c000b014038005654000d204400d1402040c0114803941c0e0035800014010826407400703107450100002940070300c004 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 945102778 1250 945101528 945101543
    0x2040905060d051e1002031317030907030b040206040312080718030c0e5b0b07030504051801080118150e01110d0204080d080408090409030324051203031e04 69
    0x17440101c5001d0000d0341c001c40c1c2e10501340301d030061b0038980040c0741041c1780007002290206200704200c0420000d0000d08580d00042c454484c0d803154000700b009445075030009000303004a403050b00d003110303031080c03256102c0c0c80705544407070310110000c16403442c1c06083d11020b02003103070107039050019248a40100ba00aa10381c1780880c41402076407200c007440d9844c140d01c1500b0015090040090082c0d00340d01c4541c10403080d91343c548266042500d1104890140202d00302600e01090b100201070043c03048038080c01004150004041e004c0030100d8038400c1c02d0003485415403c1007078160100a2640e108810039500c00c2c42084c6103103d851b01c0c2c00091807804800340140d902e815001603403040c44801010140303015440940e031581030101003442c1c065420b10440400402c10b04110109038800c003604c1c40c0d0b280446011400714a1400e088006e040d04101e200b00344404100d05854a4034004240c0048800944024903095881d682d015101d010858070110540312002c641c8110100094207640e00c00d02c0381c5075 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 945104028 1250 945102778 945102793
    0x509010902120601080115080601121502031f092003060406030213090b095101090614011e05160503130b0a170604110d02040905060d051e 61
    0x850301c1802d01d0389081c840d00800c005001500081c042c0c200c1c0c2e001321303200c0998018034040c4490394611052242c185880003904091040044001c001040c0003c1c1340401d54603030514040d0354038821110044184000e18150001030300b04510300036640e41004880c1591905003010700500c0c080c3e48005c3c000c1354050790700d81e000310041c0d4484002040c00e01e00c00c2c1000900c1c00382498444040b42c80501251303010707401416201401000d03540240c020005010a04104404101c90600c50700b1006d01c0d0310011081d02c800c44c610000f800c110b524100c59002d8000c0c00616500c140071209078040780d12540c0060502845070400c0140008070044540091820703514001c4080700c10701303441000c1030040f00c007600b000070402c1d5680c1101e1500005803907a00c40c1c1918200030a2000340009941d110b060640c503003044009041c41c0d6982c0e0201205143d0011075079038502d00c944060b00258424042d494043d45843d01003203050a05030420055070358001d00403d200131003001000300320340312032002d81c0c894441c3d001c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 945105278 1250 945104028 945104033
    0x906050d11011416110307060804120309050c09090f12040b0d0513080c030c0c090c07060506031c0e0103180f020915060a030e2505150d05100303181805090109 70
    0x202c40c0d4881368000d00c80900c07540c2122081604004c0c40b5445003040041d41000c0c08046a007000c4001c800140b24200000c0010261424506102c0d454036035907441500d910400c0000386c00418491501c002d201c060719117076041d5014240c01400345019500313a00005100c1840c00102644c09185c200d00c1c00d14000305000115600d034a40c03540290180c2c0d107507403c082401c0342c000b0303400c015013000060100c440b0303045807a004106803510b018900340070f4440c0d5100c4001c0380650300e0602a0070403038071550101e1440c444d0400000b03401a000b42601c14004bd20b84403400d07284038906110101c149a205c0c1c0750502e010002d8003000860940074208030076074800100b45549954400000700445d0405423030104055103046e494034241044540801198000e90300800c0000da5512020011b91300100c1c0e80784001025402580740c02c1c003410300340e000c402e450300050103408820b1008034421a44070b903503129642c074072070002c2056029085c416070030180b9480c0032210215940f50070996200442c1c4e8000114400240c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 945106528 1250 945105278 945105307
    0x270b091f0210090510541109010608011401050c07030f080f21010512100e070b04090213060f02030a030f0b03150f150a0b0d140c040906050d110114 65
    0x50102043c0c920b1030301c3d100d40381c4081d1500c81d62240740c400c0751081d40d058110704c01c3c1550340d14800c0d44848070706d0481d5201005c11010381e003940f05e01d00c0301820a140560f11604060030803e02802903451003140d011080d000c0e0343c0710b82c0072258110b8039900030f081c0c3c040c6140e54040071046000741c100c4a070401407243c0110903e40c080070302081040704464040c46590744c000e0703079070035803040c2c211130302a10000c0c800c05107040000550f60440c604840c2d0000c9c081c504094414200320f1550841241c402e0700040c0020039100302d4026015280c200303c0410422607a130f01d000e03114214880c86110168105001014215000350700040641c0045000425007542140000f42010002c501109080c10b80d401032200c031181c0007c06680c0003c3c038840141d011041c070000141254824400c050b605400020407000884c91a008140844254420321100e414409481d20694101d80685100c0c1450400300107043d01d0140007002905c0d81100c8001543c0140c40011202d480d000300489004186c100104611141c00 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 945107778 1250 945106528 945106541
    0x14120307090f050901121103030918010e071b080309010f020a050a27051e042a0311090904020a0b0f0703030f0e060106270b091f0210090510 62
    0x155807540c0109042681d2018505003e80040d030207000c2202c01400b02c0c40c15805441c80c4150010403040100b08200c001a19500c40c0d5070429400604002a6895240751085038505a50058188405ca580c40000031100900400c41c41c4101000c00008400443c40110007160003409400001c116148900b180c0d8080c1da20800408001600c00507d00b20041d5100044400a050361100040349440102085c041c1000502500340701303401c1d00e0440e410156944491076900030f40604144418450782a900503003181c150650900c0450003031410f50003e1291040e02314400041d640c844c04c3c10f160394203000039076000500890304140a09000b02d500043c02014081c04000000c1065540c506490001c058404002c10042010304002025540140201c0c65505489182c9400c0b2980799400900380740c0c420a04106c161a0f82d140314010541d40021001002d00c070405599007100c402c080c4000c0407080e62000407400040c0c01180311843c1e02200741d00302000140c05141110034070700d01c816691046914 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 945109028 1250 945107778 945107791
    0x507111c05060901450804210b0a1e060b0301090b19060327030302030f0f1e0c04031a31060f0603060504060f0b100507141203 56
    0x10000440c204000041101c40d0340180058024015210300300e071111440d218104048014600461540070000c00300c0c000380e4002c00d0b44480b032807004011428054040d0b030107800313072003405000710410400300e10b44521000c9040c0d5200301074100c42e43d01d60721083c00600034605000102d908207420000c005050340035100180142d03804140e641c4d4541080801203c808041d6240106064907000b42c0202000c1007000807100c050402150007491040342010321084020140d9104480880355400d05500d64007a5106080d0182c0e1100c80e80c54008080d46041400c4030341e00c40d11000540e10401d5259994044c0780c00000d40056a81413540365505d86003211100c070034804900a900c01000020040b0481581c400c000703074007000346119402115089000030090000d80600e4450642d0034504003d03034010f40055400c0706c020040e47c1044d18060028010b613503200c807866400c4c540c01851a140030440400520344076102c8916107170056440e0306104908015502d13072405a80c0845982c1c0d4810802503101d00c0 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 945110278 1250 945109028 945109069
    0x1c15050607030f110a03050717130b0405090c07050c101e0305041203020a1d060d0e0a0c0b03160843051c0b0a03120e0301060b031303050711 62
    0x700320040c640313001c032440181d89520926032480400e812000300c40d00f8542224071b0613180d1100c80d250305002e03c1120380c0c490880002000000c1c0b200008070190050710411240c0418a44605d151141c60707010b03544019089400019140380d8a203081c021403000a1231074180b190349004c00d51903c0b040301000351101d00200b51204c0401041103001c051003400441c007802c00b10700b0702500b40c0005019017a10300d14594a06c2c4030b0143c07001c49503103080940340000300581c4140001c000c1d0400b05500e40114a03401c8401c481017000204d2101503c6040e244076465031515080d0341081301e2411119040098a41c8076450000280d8890040070341c110204055121261940c000040c015043c2c50701c0d070307029480301c2000001d0040c001030841c07103841e018000c41444004910141240c000460329005544014032200001e4588020940c000020ba004e202c0300300c00802900741d8440700d20b13946200445500c0b0300e50052070010340001e030080015201080c0a6801404e031a0b80080109038003429a15000c00c0c4031 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 945111528 1250 945110278 945110297
    0x10030c150e03030a020a03110f010501092705100b0103020d050708011a12181c02070f0e0609040201051b0601030506040210020d17150a0f080c061c1505060703 70
    0x45401041480801000b50011807500540c920001d4541e291100001d08000180b544058410800c00c40424030b010b0f0203000b0440c65a503945100c0c000c1040360140c80384503000380a0044402401110740c42640d8010b4040d1100310341d01d004644c02018008001418564240903441200320300780b0502e442005941c41c4c0300ba083d41410343d000500490800c0900c4c2d003d80401c01c1c1149030000f01c840300d070001c80150601c03030310108000b0b0050403c0c05442201650440501034005c0055002548074112402810480c0b00c098030303040c03502403019040305c9558200d0741a4011070015449a80285030410304103403c9002e074070f0102c0c00070303007000008e03801a12a03a001d0380c01d100a6144c0500714420380d08840c001004201030272000584020450320300e001031848442c00203810807a410441c413000700b030020b003e0f4014a8494814054000041c01000c0703640c0b084005200301800d210040701c0103440c2d006040b80039101c0c488401e4000e000c1150342d01006600c0b0040010701a11150044c1c50114030a0f1584910b1 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 945112778 1250 945111528 945111569
    0x10050912180f190504091410140702070f0b07170403030503150a15110f0706020a0c08060f0c091906050306090609071710080f06090d0311040e10030c 66
    0x460b0049090700c650307902c90107400b9144010391804102c2d44180e42c08505044103052101d0075200620780407030b85000701031000010200d030782e00425100003243d58111682d20307080c008aa803049980251000c5040d4100248800044440035040e0701d44500c0c2140000303040c1e400c180c01590050350084000c00d4012050102d18503078000d8a000728030043c0c4015002c58030b0040602207410301c2034003002c1481038a80071100012070a0040c04450f0950703030122552155110307c0295241075000d4150b980450385030000c11600c902040040c0540c60044407401d03c1d455246049046510445480e40e001054958165081103928241c10080c00130703842d17090701c4e45402000c2c0a813038040180380724405e10341c1d4010880260f03040803041c401c14949040000181d40ea0076140011500e960700450380310b1040c074441070b4061034001340c07651040d6102c00c2900c940c2c401c4c8a800f54284c1e081d0704840e010508051006201c0c444a55000c1644113607950140d5002d55642d8482d9078a03406c03c3d4001130720803140181000310 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 945114028 1250 945112778 945112789
    0xd050406020f031c3303140102160210171003120c0203030301060c052812090303020d11150a0b0f030c0607081303060509150f07021005091218 63
    0x3034003460b032001c0d628220250215100e013010400c2601d8200b40d80c0c4184510300c1d0041103092829010b00518000c2a0824040301c500301000d6200071076030f0516044814800940c18000d843c82c030103686100a031040c401e070f400c112840b00c441700780d98200300003010003e8006d240452403034007400b4001c44031451b1030704505103244418845104e441c01e01440820007001610000100c0381110890300d0444000764852808900741082002c000d42940d0420300d50310994078100310400980c41c403c070148000c0040d0000240c400a100d4400600940c00c2100e980d060240a1440c04004480d491b0644020043c4400001009982540c14004803941c032080110b1605003070301d10050f00c6030128014044045041c000840511a600b402800302c14003180c2008009001c05908024584c018024070551811109082d50392495110020640324a10003007480e50481d03821680c003030150b9030301800400c0c01b10b080040280c40050200e50480c0708490b184032010a04902800c030b0f614045880700c0400498204010 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 945115278 1250 945114028 945114043
    0x2030903071b260c0108100e010b03060109080708070e0a27050d03060509060d0201050408071d0604182a03060608012a0804020d06020d0f050108011112060d02030d05040602 76
    0x12910600c43c86070720070903140020104560701091905c00d0075547d40c1240710111001c1a440303007200174120000450305817190000383d07104d0038080e61410310407543c40702030742d40d900070521411440b0b4200c070743e040c4220551020015481203c401010848041d808140c0483c185400c0d50000b100d20f05580b40c0007040720134400c00030010120315042c40f41c01c2c00c06000490030b1001400c0030b0710a060514600d003c59014000b61801000100262691140d81f41c200c070280710724140c64030b10440d000c0d400042952510f80b00b03000600c1880800007205105076590480b00806040c1004040701c1d032900d80e469081669a031030005148a00d40101c3e80e00c0c40d05400900355011012084000d00102c003080441c05442061320506403c9407511054035121400820302a584a00010301214000606007905070680d4001425860400c10104100d80c1c1e241e24581c220340c040721800380b02b00e0041201400110410482035001000140040c48101c03203a400a440d16a2100084004c1000800c04010080c0c05002d01d4 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 945116528 1250 945115278 945115319
    0xb0109021c020a020d110f1606021504120e0301090203100b090109060b09010507060b040f020c060601180b0c01180c030215090607120c06091110110c010302030903071b 74
    0x950034000450f601a407030f9a80c031481d0404004203a1024196404100300004a0300d050701e081d2031080500e07552001807071a80d80503890240c420900c1c07203201c100d08194804c0c403440d040120740d001d200c0d03c1701c0100c500c00d8160303600e641d1543d201d100c8900541c0d8103214170384180417000c00000703519030780740f080c0880d1600590012514034a8008108415080320084074a0640d00346411603075003645142c81802807040600c00b6400603d818158030707200050782e000b415031160540885810340d844100460302e90502c1c100492211085600401c02464560041c1408404540010a00da076110904d0780c88400030f10405d4409401b107000400940c242803820382c0b05945400203003171034a10103402064441c8900728000780105c02e290300c0107464600c254481d01015622103414041d682450500000820100520600c595100c3c40340003603080c0104030160401703800201501c0e42c5240c443c0150025000100314102c47e000130030200001a2811081c0540c014002c441090554104498810860303d1140301 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 945117778 1250 945116528 945116531
    0x40605031f020f120702210a140a0c0807081306020a0b13030c0b091006050409030c0807020301020f0c1f11220503030705011d0c24070b0109021c 64
    0x200d001d911820500d20000c40381a050159031204203842d80a22031203034030340100c240e10340d400520181540c0403445500e11140600c1144018489100c3e05c510380c4591403445020403000c041403091900d024001c0d020100c910304000f510301300d032038035440d40c6075018040c202c64104c03001480000703000d4078641c140060302a07840204880c0b4100e07914100d96140142c521a003240003c810107042500c41c0c005140e50a900c50011001e900b083d043c0c403995180e00c2210300c0703106410702c0c00102d15410244612004184c0581c0d981c418203616441f204825404400146c0c1c155400f0401c000001001c040240b071500500c07070050500e0340d0042e041c0d0560606900044000038181303645401d4131072501082c0c4107095540b1301101c1a056203c00800d000d004554416601400302084420910406611000760004210176132482d142138191050740391040403007041e03400600c20001d807907064203a00499483c3f4546d068440e00e01852612044d80c9178200340c0c0140394264001600018030900314500c040d20400c0880c0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 945119028 1250 945117778 945117793
    0x100e0a081f0c0f120218040c0806040c180512070f03050d08010f0e01030b070309201801060f080702010e0106031103010b0f0901090e0309090403030b15040e07111e060604060503 78
    0x101000c241807011101c145c0c01003248801e0182c0e6040802d0f00c048001d00400c0243c1900c8006040940c00700ca40d14031441c03170103180083e840e000f040c0c0e00044081c19a4810121810501004070800c3e20030507020052082e46000303d00d030240f031040f910245000f00000d1a415800c400010000c410581062960684140c01000503458000025055aa06c400040540e23030710703031804400805120401070242e0700901d0b1405030414001c40e108419050580b22401044060b0384400040d0340c081c828907000500103a40b58100c24402c0242582100a620001c2019068001c0c0a42500d220342c0081d119440400c0804000713107000d00c560001da4400b40d941400c6803500c03500003804142c0511504108980306d160711140c1d0141402102c00c1c0c40402418081281424200100100051000140101100c043d800da0b00c5a40100782c0f82200c0d0340e885224100ea03540041102c2c0404100040a1a44034109290070180c10700280c1c034010240d234200034811864000100810b488540e40454026044400e = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 945120278 1250 945119028 945119057
    0x31e03020405060a030209130c09050f010e10030209010207031203231b0a03090c030b0603010b0114041e0b120702120405180c070804060c051b100e0a081f0c 69
    0xf520001807042c20b0047e1507014000c04541a03006207842034041301e01d04000c0f001d800303400a0001c800e6810545480c00b000c40c0c04030041d01d02c8418450442d0340078091400e1020414800d0b0010012050180306036107041d80d0366610030030081d00766a20707040070030f844120303440d070078420070f596a6124810700102035890b08005a5003444400c00c8044110401030005135140040e010703800441d0115480790840c0039503694ec0c00c0140140e08152141c0b48694203060545005610440c6c00d5020300d442d941e0703070926261412a50a104502c501b11a40c5417200b000000a11050389401600ca02e80310054000003500d00f0800c000d00b0100d01051004042c80c05002c00d01c02a1503c0520f41c0d0300c1d4035407090890183d1a070104062242c019440014112080010082001507204618040d0f0511030011588008510306100d40f50724440340d1001c3c1c000480d01500d401c20761080c580101640e41c050141081d094844445904000450340b110300001d00b0381100c40d103070040512034a0b83c40000c500e01030f0760708070300d50 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 945121528 1250 945120278 945120289
    0xc040c1b020108091f020c070b2809090e030903070602070f06030f090503040b251e1a16090b040305062404060914090a0302030d09030509030a031e03020405 69
    0x400a4100180d001c000b920004040045d0680040744051117020f001c3c01e11107140c080d51040c10202c181d8050300b42c001a201d4402c4041d030b003002069000682444c881f000001413920000d01c0c512040201031040003038591180c0c818041000502d01c041c40d42d07040c0544c145450990298880402c640c00070030200000400307000c4190554906203000309112440c0c4003404007400711500c4c058228000040c00240340361a010052115242d45001d10075841070b148106000d032154894040c1500c2d0a10040050358a61860741d6081c40303106041054007030b200850880e003c810b007150b15040c4030010b074050841c801d402c494104020100111030501c2c2c20308596503291604006010506100c070a02c05c038540c003a40d010186501540c01a0040016540d601041009003e600d290301c4142d01b115404580c1d003440100d0300304259a0540c008610b03000707040d8005d400030444801c09400f0414140002e26003641c060000303035030340c0c1c1c025592842106c6500c03600e016150261840d003400d141c410001084641c0f541c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 945122778 1250 945121528 945121577
    0x11406091314030c0a0b0709211b080615092a04030602030a0c0305070c0203060403210207060b010e03060108071512020d06080c060a02100504230c040c 67
    0x18000040141d000925200203107022641d40d81c5010b01012501c44000a00050021120340c007410b003c1c0032544441e031381941c00030054011440350600c02c29007039030103508103100112014070904a441d47d103003410b0407000010340355402580e800d400c0320050000702c540e81e04020801500485603ca40c074184002110190b049030b550302420b1044040001c001d5003802000d4400464000c072040d9542d10b0100f94034030042406152283c04280342201007031116110b08040300e80075a01400034000d6481d16102643d2803034603403851081742511070180010f5403071a0b00141c60010720900c0046148940c40002610381d2540b10341c094041da00c040010001190005000001c460324641e00b1110b0b800f00348070403030f081c030744107d00f00d03c1044c0009040340741403840798080c0013190741c0401920054104a410004c00e8490920b4880041e40241e5488141d03664983c422900507100d130314113580c00c840d0b204811710080c00e031160000c43d0b500066051005410a40a0810f40104600e00300e00041120408412140780 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 945124028 1250 945122778 945122791
    0x161806050f041505130204091508150a020405030a050c0f2d03120a0c02030f010c020c0906130504030c0303061a0d0915060b0a14030105010804240510030501140609 72
    0x1258403d414401000f040d10b07001600003c1c1c240c6042181100001c006548603203e90fa1003180342c125805410120740b12100140c3d0450005407000a1111421600c10640501040c002d2a420417001889075001c200b80c0481c24440ca02420070013184008102d5610882c00301d080c0100110f40e00d05814030301904114540c03401e00c0c901a16524a107001080ca40350b60340e030700a075a208000030503584041e0005410000507101300c04848028803082c49090a980d040340b100c0000d0f0b4081900080c1c1c501d0a501031075801140606600080540f040c154000d41728180c2d400d1b0080350700a20804245581030080740040c04031850b20a0600d1054071030300409121b2008003d100582d1081d40804024140d030740c3e035444649849060003225194100000306500425030039010600c1c001e070ba90100300001c02070700e0403980161510031290740c1e16141c4850415040c91403041c4243e006120007a004070501c20280640810140e0342d45d006d05514209084401403050300038103403041c030300300005a50b4004a02d90b000c04d = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 945125278 1250 945124028 945124031
    0x605010f1508040305121905240d03110304060f0206070c0803010b16051b01021b0a051507050d020606040c020102090f130605030304090906140108031e0c161806050f04 74
    0x96a6044c1203459001d50018800f000b103107002800b43c403542440d5490344071090403034200126101e40d098158100080001c03078149034070b00c520800d8203140110842050600030b050182e07039a583c0504032400d55010b40c00080101b081030f24008801a0704100b00390740710060b400c042180d24100c1d00d4200c0039000501c61402c0c0c8484c0018902c7e007414400216242d03480e48082103c0518061200e114000c61007071200c14010b200c2c8000495903003202203100c2e02e0200b0050a014180d50410003401410200c0d4112096860310820a40c400a00b00300f0250040580c81d038041e00c0c25091510401068860810b011000c5a0050046c113050b56551079400c40d40c00c41c1201e9144203040725403c0000038006580c0441c0c1d240c00085000154140903030090124203125403010425030810010a0041100c00c1c0500000c40e40103001c05180b54502c01c40b004034086034800c4180c01d09114485543c40d0000030300080782120040b5404100401c240010054403042441e403d0080906110102e00c0000004403001e03c160f = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 945126528 1250 945125278 945125281
    0x50601031e020d0b012309040b060f06121f08060f090c031014160503040f02030c0d14060a1a04022101030804150f140c010b0a09090605010f1508 64
    0x52010440d4040c0303507000e0090b0341001154181188080e01c2441801701081d0a000c0c680060071340e807a10780000e1b11000b01800d400da02c450700e0707181451070001c15080d009070060b86c089500740c1d54480904079a0300201d00c0b03510240341401da4070b030b12090300c41d00b800c1003c042c0701c0c8144486400815210b9008503e0b2a51003030344d6403514070303041c500080141043d07003600668000030b100116541010320003207010411160b0039290005403020288140c2c94200c00207400344049400201d0304000712003003e00050450300351101c4034000642004003400200c0c0c805812130000c017412241400031a80c450301da030b03904205001003428080c41d03214484004922071540010207681180030303020200d81d03030a00000035641c55a142e150122181e801402455801c0300000800c0070042c0c03090100d5080d02c0948d980310400d80400802403840d03030b0031007400c6030565500e030212180d45403036101d8280000d080c4d030309003c2050740041c24076008039881a040b4406d04070344d9030b1040c000e0302880e101c9444d21030102d180c40d0707031107 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 945127778 1250 945126528 945126563
    0xe030a0504060f0c0227010503160e0a020705030d050103150504240905030406092303030708030a0207050a05010c030c02210304050718061404090f0209070306080102310305060103 79
    0x207100070101c001d61140d0340c6c800d40c040e014801000402c18144c0c0c074228240b01d90300c1e281090380d640103002c00c080a11310303064420f000362446007500a40051880001504061499940714103541080b4102c040b034694800c0100140520134010008090304c40b00100312a00301600c0c1d00f0340d09411414242040d551101040008134000c1c1c0c080400b00c2d410005503034a0302e80f9154000c00c40b10b45840b95070a03003c0140c140da212940309217403071440c1020040003036140181d0340d0769103e0325420090040c0302103a070900c004804140d0922400a400b03108000000d20004d60300800380880360780c102054110b42c8030380c0c0d03d50224084094481188020f281800e51030359203914003140341c41156000600b034203074240411404120703140c11070816034802d2607840710f58a0154007840112007240401030150180304080e5400f504004400a400c45124900401c0480e121a00f140c02e82c1d100c0303070552407084c1041c0c0b940403501c0c0c1100ca0f4849110010012010300700c0c595224280e5500301804060540c41300c085074a1b00707 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 945129028 1250 945127778 945127787
    0x501030902130e1009050109050601170c150705030c0705090c0408030301210f21031806090309260d080f160e0901060f0906030606020307030810031a04060e030a0504060f 75
    0x203500880003420302c80c1703225030310304140640f40750b4504540c00d1085130008500136000316048468160208000c00c95100d00b0410018540164814100111401c00c100c602060040c801032040038900701c0200703601c9151400348646000010b1080418180501c02405031100c040216170443c1c600c259035081d0b144a03400c0340310f2104480007002382030301c2105000c0010424043c0a004c1c001c108034101010401d440f0f08103400b0343d142e1007811100e030303072401002c3c2d00058000d900c440c414900a1505a171801d858985014500c1050140503800e0b003010301407401c144a01b0448000086128500380515080c0803034510385190b0094801d02200d141e0452840c0410310800100301c0100d002000980c031969030b4140a03001c0c1401034a84000a00e400c074011a10780d00138010398080f03a609078020362911b076160304e0031940710a01809403140214100340000c04070f40080d0390104c4e110b0154003844030070708091401c84126208442c0a008076001841041e4002e5001002d44007100c1541c100702c0494034200b04103d5 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 945130278 1250 945129028 945129043
    0xf05091206070801090c09050907053a1506050a1103160b040506160212070c0e0a06061107050a03150f09080301091d030d0b12100212010501030902130e 67
    0x5803a12606041080d02a071040d0322034100d8007080e200b000f0721507079048100d0340a5041e000341508003065401041e42148103c005000080281307060481100c00b8a450714241c90500d844012080078444145544181302d00c5041142c20940e1070a03441c8070700d000710140550180d911b5500501481f070008040701181802101c4080c603c1c40328641c112030480c640240200c5040d075080d44e09100d00c0c000625031105607201035500261940040c54940b401c11036400060f4840d4004a42c0d5980340000090303801101000180561180c82d40490a603040500007045a502c10910b40ba2552161008018546907003541c401501d07006184070f0703413007440728102501030f051414030142902e1030204000188420302000d14140e401840c02440034000c640f04107070700403c0717040d10102c072074204000140700d0307100783d6201040700c50000d82100c1203004108400ca0a0802840201d1480754000030041c48036841002000c0c05800e090804000d00c0e009600441c0c0da490003e85801c00003641c0e064200c103034850400051 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 945131528 1250 945130278 945130309
    0x150c0507050304030b0a1a0904060b0f1f0225050d03050c06180705010302040e0f06011103130f05011b0605040303110c10050a0b0130020f0310150f0509 67
    0x1207607101c0e940d01e000301201c5c400300e42c2e2010451500381d900f1800047c03100c00740805000101210360580356a02d951004000021100740c1c0040348080380070658841104200d40c1d690485420138444550f02c3c0d020381041c042c51300e03910b0002416403186038948080c1d201001902c809890305000d0070700c90300d0180c07182e01c1103107041140c92091000700402850000040d445010300c484c140c8070041d64640041d0140e009034012407a4901075440040c00550a00300040d5010005150588610308541075081c15680001c603e0721803542c01400034025a070302000c3c110028a801e01c3e00c801c211541760b2560780c1074842ca620040007640c981e00440d09041c82a0024640703160b600d00000d039140c1352000f480380d40d18460004082210f040600040002840303200310501040181c540c004007845a02034901545501041d0301307010f1842c00c1101130140f810748080d1000d1031340841c0d50f544c1ea091051000c00e5980440d400708004c0648881d40288040d8080b9050700c400c2c24609100d92101c481d4000104d0395065810345 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 945132778 1250 945131528 945131533
    0x150402070b0a021c050702031c090204021c0b010e01050702061b120c07090213031b030503120f06030706141c02070302010207030f0c0b060d0602070f0309080c030604150c050705 78
    0x920050340c0280d030013414401e13440c02d0386035080b81d4403000501c26120200c81800168000b0b2000031400c110740700d0f540d41c00074130740034000942400c2c903030002d0120303041010408001c200009928004103854030509141c0a02400c209003a210881e000a1031403048202c02070084002060045441280d0741c07010101c00030f40c0c400d40d0340ba101c10403841c0000d40c0100b0700180b0148502c0500149214152086901090340310100c002c00c40c0c156113030954204d10440040c05d9100c0c0c105400004980107202030411076610018680460500e141488007891014001a20941284c402041074540010711072030f10004080f091500c2e8860b20b101c2d620000649185000002d000041c800308050b4103500a100781ca210b80c5851102c0001f00303070101c8141c91020001086c001c0404c001c12031a24003081d200b8409845101e000d8949241d60342c40460384d104d00b05048010581c0c40da024000280240164940100198020402498039840c0d000101540c0b89102e01c441e50303100541603105210b40201c0f07d10980000c01c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 945134028 1250 945132778 945132781
    0x1090b131103100f0f0b1c020301090204030b07080f0420090a05180a2607080c0105100501110c090c360a050d15061a0301031502070209150402070b 65
    0x41600441d84103d0303455036260051240072030981d511030481403d6441185940d80c2d41d5040c43c001108650003d9800040070642502840401d0141d000450185c40440d10143c2c4440ca10314040c0c0442c04e014101c01c0c20f0100311000c2007403209000c0303000f03a401a0400001c811060040c1b0780031481c0008400c01031b802c002c081d03040080081c02da411042c000c004070201c2180b11040c01108030b0711908942d000800310b101c540d008550904402c0c0003500c55104207104189042c400b644c980c1e4165020140c1080c25075161020083d07038080b00d0104d100100000c0c01c0c41d0540302c151002840d184d2282429043c4903150080200baa628500c5054900f0480303171b04035480880b290b400c41a07001c002c4c00b0640ca2400b0001076000c1c019410520001011100c0c09401c40e924029640e56020102550402d01c41c2502ea66010016401c50b5050421092403c15803403180d6a5055080403454403041d164810a000d00420955005846003440154040000501c40c8600c004803c0004c010748680b200c0030340407203040c00 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 945135278 1250 945134028 945134051
    0x510020609060f0402061c020405090a09021e060d090f0503031305280b1803130617011a0c1015170601061b06180308010501090e04020901090b13 64
    0x4103140600045801c4031019030328072200329510030b03044a000f5080b860501007035521031030307031146102081402c074000b40c24242c40d030010640040c1d04840201712641c0b16070081d01942020061860311a04c20498400d26200c0300000c01c2592080d9014140603542e00c1080740144080044520700c0550b01c0000d507551f90800d8200022085203100040d20340303010f20b08111800b01d90710700382e490303054446504150380c001c1e290711981c01109000f801c000c407850040b1900407800f041840202150015404035101c1c25090403801030000480c04038081c8543c2c90840180101e20011b1695900f5482c03524450340e441c2544021942480f4000d4060b0341c071a420840d014881790050a013070000d0b10506078034800c000e102c403148695114020f1280794080b0b0100090008038180551201200305d000e8100800d11f5005d80105003c1c0145400d0140c0002d0320700f90044c00b00f5a07001c1d25800c0140300b20401d040c2c2504040e00042e91204041c40758030050760761602050440d444216078442c0f000c4465204010500c1c404 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 945136528 1250 945135278 945135283
    0x206090405100f0914070302030702010e0d210b0a050d17040b0306131a09060a0b0414090c12060d1a07020a05100623060c031305130203040308070c0c051002 69
    0x9010f1480103603034500700810340455501c9003030010400c88400c024a03031a855002d4009500c050031404c01c5540fa8014081607000c10400a102800b15644903401581c9142c5002c0c101035540e250101141d05005c00c0c0d90b4141c2d00c2c1e03c400b40540340700702c0303d07a20300c24607620b040700b00001003445d1034541c40c0740850002040e10801000e50f01c629030540d2103c500000505801040316002503244c003c94003011000302c00c5051403204268401805085440d141d52544482d05090704030340d00c02c3c10710181c2281c0f1a5014140140150b80103882c0b55103c0c1e090001c0c00c0b1081c00d001000404040c054041c04400a052105500c8640340141158072440001d09101d0030007505c1e1076240a081e522842802c400400d2515a485010101d65001c0c5ca40070301c04c28203031845050041200086a80b000d001c1c86040c0d5081400c1c4014010300c00c0030b980320156540b030714081c4205e4800c000000b8140701c5c410320030080400d407c03880459200e01d281c980030300c00811902d041c0030b00c508036401c56038001e00071014808005800 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 945137778 1250 945136528 945136561
    0x14012003241c05060c0a0827100b030f070612020a121d0705010519051b0706200d1d01020a05030f070309080f121602030a0809040c02010501210206090405 68
    0x99001e482107591600350b6031510f4406c5403404000590400005207001481e10840c074541f0080c004410f002d4042c2e9012585080c80c80c00a5510256882207091228070782001003001016140002e0a1760b540340120281100e804020680c0e1481d4000403a0000c192242c0c054615108950008200030f00701c148100d4194040d048420907240b14a000120305136001d4010b9800c080900da0060f401101003190441c0d154010481294000080103800103007003006001810190400e40c2d521649040e0140d407601c04035510080ca031125410407001e80e100c02e80d115000c20004240306a0b940c02d580003440040746041003800002d0007500003c52a21014000ba200400a040c025600c41407526200d420403500c3e03e10b4010000802c0c0d01501d00011690284c0700540301c441040740a450514565402207070034008a11003c40b0440c4000611005a16107403052b4032403201c943c0300070001c42d810302080740350209c056400000844203180a420444d903401084542c4840040c00a00c46400c14ec98654801c058 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 945139028 1250 945137778 945137783
    0x90403170a0207140115120c050904050a0201091202132301030506100b0c0304030f0f06020c03030a0c050903070509060402040801240b0c07121a0414012003241c 71
    0x5200c0680390305941c05004203503200a24449190350145000347c0e4002d85103601104540c3c085956000055903035540700400d210380d000780c1c0600316030708082c40010118203003604103003144c4105101c4000942c484004086c420398a00900041280da907114031045580320607034040505441f00004001c01030f000c101140200000c040c0340d806203071070700400ca500e80140619401294021b1000f0404200305520b941c00c3c0301d02802c105410490143c440e4000c0c1d80c04403190240d0341d8800018011002500d12a00c0301e5145d0f40d04d4030f581015840b00000b40c54107204e2040500c03c680d590b0200c1c0251355075034121002032000780005c21000307000050312560196990303c1d420341800c42c640000761020443c001c490240c80c1c00005855800e0500d0703c110002d0303400200698040d00117184002d0803000e060030150243d4083c9050b9507004401c551800d081d16003440041e104444441034140410301c030742041c3e0750803055104800400c2c51200d1100391350585400c519541c04907501e400140440c2441140510490 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 945140278 1250 945139028 945139043
    0xa0f020405070c02130b22050402031b060306040f11040801050103110a0e0118060315200a020307030509030319080a0e070f060f0c0503040b180a050f090403170a0207 73
    0x41c1d80c80020b40b0060440800a03403c85c03804040203405030202c4c0d01c00c10000d0f2006060007648007038080d0102c0722080b140501060b2581c0c0d1000e000c15854104089078010a80780c1c0703580d40054030540842d500d800060303c05406680c84040104012503a80c00c0064031a89403800e05440f07507070b00c0e96014049d001c280710a95010a1051401d0076600300802d4050960315040b0540c06a6480e00d003103410700307918149140020301da49000100010311851002d255400c81c206011a1080442011400d41c410911480e44007200070000302c1c010a0f004020359080c0b81d05070030201c3d142d010040109056201d80700c5080d0b54528413120203000c00303400c84039890003010304e50820000300300c80740c04c069528102c501800203400b801c0c034010485644038035000801054580341c048040c130441e80e504c6246030801e0b040b0f90b0084201051103400529004040b10b8540300403200c8150041c82e08011442114100e552031303005c0c4154a00040a242c0500000075103048445d0424010746010541c900094120407811201ca0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 945141528 1250 945140278 945140281
    0xb090312010902090604150509030a0606061116060e13060303051e030103020d0b07021606020f0c0906090109050c0705190309081501090509010f0e0c091003030c021e030a0f020405 79
    0x110b419100396800e03204090803443c541418282d1507201b00200040079001c20104010b21012903e00f4000c901c000303840340102103a07007404e169025110b564100c5d011500c55207e50407031a110740c2c1e0340700540106c4180707007440da051041100c08510325010b02c0c81c0313048031181025000002c141c0d011004041d01c00f910b229401e40e00c03081c4404110f4610081c84003039030003040c140031076010450b0401c8540e00040640115a1041d402d041c0f91480300380258400d20140e0051046445525018030082c1c01c59101201e81d2520b6103002c2002403200b0206014014040b80c0e241c0000e620038034240304640ca01600441115002002480c002c400c40001410441c0001c0d0703001e8000a604c00006800044008611841c035503136802c00d0500030080000800c00c0f4125900d46007418140c08103880b80d0103a42c58444040c0410140039400d004040d4000b50000d40b0285070030104101080d44070001c003899a0741241d041800c2d1850f88540d1001c510803010040e458011188140c00300540c01c58a0310803588250707018080b6 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 945142778 1250 945141528 945141539
    0x50a050c0906150d020307030212040506040210020f1e0a08043012030f061a1e0f041e0b1b060f150d060612030503042f1c0b09031201 59
    0xb00c001c0c1c24035940220000780001c0c544e402c2daa03000381d1351006040c03034018245170401c0340185030301d10103076001d4529030044810700040d41022110030305503040702c1c0018030255020841342d0303550b00e403008120a960000c50003400d007844814000d00103e5034010300c0507038031103807a010105082e06445074071209155881c809404602c40c1c01c28a030420340c3d0088401c228050341e00c1700941c00340803440000343c201580c504010a032030744150609001c18202c80001c640310002849a921800c20741d200c800d603141c4050045000c8140c0135011141560780d2002c680a890382180300c2901c4420098201c00820712000c18140ca01d62040700107441084069000c50744180c507042040b81701114141c658104402d1050110012404c1441c610b880103807082c500090029910300c01d8203141602c042d803c800280e40002030200b4004010000c2c100c0c140b803000c0782400040000500c180c41c0c244a400d0034002ca240d85601c1600704100041d0300b1140e07421034100b9001d071a05042141e100c1d80142880c0c0010175102c0c001144 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 945143884 1106 945142778 945142789
    0x9070b2710090806060406030b182119140a140d0501090e060a060803030f090f01092604030812180d03020d0c02061b0c0109050a050c0906 61
    0x480703d05010000381041ca020b440d445c0709605014040c40030810003070005810520034000c04801071004520329041a0300920481c0031044400485c145403c0c0140051501c503000001d50000c2c0c2d01d500b2000d031004504010105110315040c0b000701c141074001c0c0c00040c80402d85943c018207000d0034440c1c0ca020781d9026003000c04000c0d00d407009003448600801265030040c08003e0b043c4029400c040f9642c3d940e0100034480400171582e0000b150040c203040c482d180000b68040c00070b01100c82c107800c00c06110039080c8040141e140c03121007140c4c219102c08090702d0039643e100b00c05c9403a04604400e03018204401806021135050400148181886c080010b17207a4039820b910301584594038001c400c030403140500050810b54219000308000d00c2c0942c403805048900a000883c0c8400410020600500e2850401021841100c4450062000001d02c1c20701c4210111800382682e40c2c1c1106000307 = true := by decide +kernel

theorem cover : BRFrame.Cov 944964028 945143884 := by
  have h0 := BRFrame.cov_init 944964028
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944964028 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944964028 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944964028 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944964028 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944964028 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944964028 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944964028 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944964028 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944964028 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944964028 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944964028 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944964028 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944964028 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944964028 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944964028 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944964028 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944964028 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944964028 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944964028 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944964028 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944964028 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944964028 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944964028 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944964028 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944964028 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944964028 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944964028 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944964028 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944964028 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944964028 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944964028 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944964028 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944964028 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944964028 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944964028 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944964028 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944964028 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944964028 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944964028 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944964028 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944964028 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944964028 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944964028 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944964028 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944964028 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944964028 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944964028 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944964028 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944964028 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944964028 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944964028 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944964028 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944964028 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944964028 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944964028 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944964028 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944964028 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944964028 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944964028 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944964028 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944964028 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944964028 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944964028 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944964028 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944964028 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944964028 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944964028 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944964028 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944964028 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944964028 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944964028 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944964028 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944964028 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944964028 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944964028 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944964028 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944964028 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944964028 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944964028 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944964028 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944964028 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944964028 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944964028 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944964028 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944964028 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944964028 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944964028 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944964028 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944964028 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944964028 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944964028 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944964028 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944964028 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944964028 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944964028 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944964028 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944964028 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944964028 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944964028 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944964028 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944964028 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944964028 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944964028 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944964028 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944964028 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944964028 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944964028 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944964028 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944964028 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944964028 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944964028 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944964028 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944964028 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944964028 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944964028 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944964028 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944964028 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944964028 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944964028 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944964028 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944964028 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944964028 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944964028 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944964028 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944964028 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944964028 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944964028 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944964028 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944964028 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944964028 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944964028 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944964028 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944964028 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944964028 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944964028 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944964028 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944964028 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944964028 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944964028 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944964028 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944964028 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944964028 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944964028 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 944964028 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 944964028 ≤ n) (h2 : n < 945143884) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
