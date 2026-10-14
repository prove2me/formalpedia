-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2224
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:03:06.786272+00:00
-- url     : https://prove2.me/submissions/cf4b76b5-b2a9-4e04-9e0a-c91de4904aae

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 399820143 ≤ n < 400000000 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 399821393 1250 399820143 399820153
    0xc030d050702240406110903060f07020c04061508060303070b0406020a0c06181502040501082208030c0901022404061d010e1b01030b06031b0f0d090204060806060f060309 75
    0x415043c140f2401060b5000401a00744200310070070543d4080e90380d0321105400c1d000d09011800000c079075120005060107208821a20001c3c0f50180700f0008a444160020014040349650360340e8040201640c05c078400028000034005801424000215030788603901540c507025a40c1e441e04c0f904003d4004109413403c002e400d0115102203242406000003802207184240040c5001c0d1805c0d021f4501035501c81040a40107000400982c1e800800c6258008034070b00142c01b090003400154018010711120007032005801000340880d81000c00b0150225800031307000c0f9009440c11090050350080c013292009020303682400002c0c00144079401150401c9e603d03018090400082c0b1001900392200b40820010710f5124010004c600141580071702d0810700d0a0804201140003100400c4107444000d042c00c040500040d160390301c140b00315040341d020000b035100b980c0d2621042a0444d0140a040c00c00f64032517400c10b80041070010020030414001d08001305503500102e80c0d2030511046800c0140081f030340b4094 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 399822643 1250 399821393 399821413
    0xd0c1205030c0912030307080105120c12011409070e0108071a0d1b02010b0405060d0201020c100c05010903111b0604060c03030f060605030610090506250f060c020c0103020c030d050702 81
    0x8004c450b0000b0b0500002442c2c403440d01801c018400c1c24142d015900c1000124404521084041004441c0540580b0201140801c0070340150245c11030400c0c150700100500c08210300320001003503040030794005001130019039030385060303050b55019280504c10002d8641c50012104442c000010b2102c030301c01080100700101d80b03403050000d5012001d00c0f500585d440d4a100380962805100f0351707a00a1049503007103001d20190300000e55402d030205c80b550150f1008031503038142c1c60058801d900300c980e00000078040403101303140040107680c3d000e503240c40318030071801851f10078420034118040240c4050038040c1414a828000c4480e0342d5016820340c141551136085e00901043c038050a000b03004140c807182e03500e0034881d050094034017401070b110b401c10203c0c4409100e155920411070307102c0c0108000b00d840416008095104e17100c2d11040084c00c0c0640c0e507006408100454001b01c0c16141c1d59020389001c0c001034001901a031088003c062003a400403c83c030010307000240d1007185c00002c1362040340c0304d40703074 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 399823893 1250 399822643 399822649
    0x3070e0118090b0312070f080306060f2a031e091201020408030702122e0e010c080a0e010603030903060e0106050604080a0507120f0204110910030501080d0c1205030c09 74
    0x2000b80c001c911020b0710382401d00450304007003101c840c1d041506594039240c10141c1e110302c039001000c1e9100030501800040803034856680c04082c3c4494110100c040c950f81c52840001c56042807d81d100e00703901c008002c2d034680021202005591004446400c080e184040034083e44040382d11030b41c0603603030051111202d03082041d001d01c017502c0600b603004001d66a0b9505c0c2d00400030b41c1d13456000000e210f507002c400da40c03442008280800c2d520003031407131b41c01d5040d00d2622442000741c012902c0300c50036503190203070b040e10072a88035a58a00450081100300000304c00421f842d82a02d0280c04040c004c0740203e001000010303100d9111035402c10089000207801c5445000141c141d030704c030381d10100c01c5a000600e000700380701040c80800d000788000500d0350400c10700c80c1d640d140c040308000d202074440c95483d407801d540c40007210200d446110004100708010342e001d03180070b8000c140130b00030741c0d41500c18082211100381c0108109905a43c00c0b0250503c800c1d004d440c00c03a0f041e80300400022a803030f0184110300b0356031 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 399825143 1250 399823893 399823937
    0xf0c04050441010b0a0b03090d0c03230904111e090f04050118050f1501050901020c04060609030618050a020910080a06020c1005160e01030b0d05031e090603070e01 72
    0x849030800401d0382e04c8058100246011160048284488100240907001100050100000b251828041c8103a04603090946140c03000c0302da00d68541c0d1206580d0000180d2807001010104012501003180c0092180c4030703d83c44c0109600b42051554403030313030002d404a020024094107000181600105100300000c2000e460080c1c0c402096803298659501121070300b401450f52160b00c0301c055011030700e404c01c000901c103000080f00c0c0c0d052003070010b014400e17a442031154202c00032015105000c05559110300904a24552100346d60b00b5103080d41d00c1ca880300c60f441c10001081c0d0480000d00c2c148482c0c0c2c00b0082c00320780c054080118407013195000121510140b03c0c0030240c6009440041c0c0355002001e5440c1441c0c003641c40300b81c0281c900020084110f110981f9103040a0b5140340040b0100d03030082c0182c006081000d04a60301c8035010503480200040040101200115040d030401000c003914030408060198a40c420b92000c014400108079622a400e180541d81052420610040240421404c21 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 399826393 1250 399825143 399825263
    0xc020604030c060503010305280b1f0e06010e0a080303041b09050c0304030e09040f080307110f0a0501150b16030c0b09010b040c0903231c020f0c040504 67
    0xc500c005c00104203106082c0302c110048001e440c04411464122403003004400c031a20300c0100840e01c4203011400041c0c1c445c618642d0800059160403c0d00e4513001d468512100880c0c03018001903081d000c00e10241440c00c00c0c00100c5074107070011815501c03247d698407188408032403066031a0503808030005a035001070240e43d0181d071084c1070f003603600c4c1041e040c01800720756003805180c0603c2c580d07428040001e10410705140d40541200800752603031a21032044441d81a0f00c800c24920384241c04c030440e40c0d60008074440c01454412402040480c03140f101610a03850a4401c843c00d0180500200f01c0102d002200c60a000d40b0a15250400e204581e58405c1031441c04c1da0440900e1303641c0c9280d034501e8105440b60509451040c108154210300c0c540e40c050740035075600c5c410440b94015407502c2c640709000b0418000f1000030240c4042602c103c1c684d000707686a81d9080c007030045124103d81c0c0d0782c55052600c9502e0090750400329003600900d0511003001624100203034031094400d014406d2100d404103800c40038003 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 399827643 1250 399826393 399826397
    0x1c0302070c0509070807110c031e060a0e07210227010503071a070515160201050609011401050a12020309030c0c27040c050a030804170a080a0c020604030c06 69
    0x150359450070a03003504503890300003d020b070b00070000b44031500744c21122141c4e0241c40c52078580300c41e1644442d010308018112007541d4162194201c41030540f540840c00e440c00c07408910842d031036540c6100c2c4d45001d4a04184000829800408084c46000181c2041000790807080c00c0c03140c03550000d640030503c44001c0c0d8040000c58408908074a01d5000c1c408006401004101d004202c2e580c18a40c81a64584251003060940b400015100040010500034a00f4518031006502c0039458440c1105550b070710040740503401540303800c2c00030740d080c90304050440c10788204010a9040c842c17007100540d5181c2c8515044424000e105210700007c80940c0002d601c99201c0300085c41d11000e05038601440c24040460315881a00c40d10a00481e0490700c00034018601a001c0d40030f28562541c3c10078503030984071508295040050460080f05000c01d000013401140d40403088510129a10310803281c0301d0041c1d80d0010000701d400c10212442e507118110004509000030605881c2c180e403680e42d041420b007241c0c01080 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 399828893 1250 399827643 399827647
    0x3020d0807050708060c0910021204090b0f06030a150906060813050102091504061b0f020402090607050a06050414030304030f050f090a09060603060512060109090f060903030b03070605120109020c1c0302 89
    0x8490801101500301d10406000524071465115001e2b400d500960003030a0150396103c0d0b20000700e654003410102d29000180600782c1d00d0800180d541d02030040c0c1040e0000407040240d0004200613584a03407011111180c2d034014003920360800d17619054020300302c1620113640a002004959880c0328a100c0180d10802c151640d6614110001d0031040680b8820402c842003100a14041410030124a81d10f65040b640181d03160b01d1840001e401d8055200007a046102c3c51803540100640c40e8409401103008010b880621808500000d55034402117600800050040c071003002c20a0041d0301404005c08101d01950801c0c0f1140003142d0180c2c500c1c2d200750030043d00c51404200042c0c143c40b401d000380805440241d102462a072110740d440c80306226000b406a03940110005120100c0c5c4449a042e0b8071203401d22810040d030600030082c02c4c047c0c0c1c03294030a008019000410502450441305403182000015440360300e4400c00d00e00035000710b00c000129008490102c620007002903411801102c060700e0050b = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 399830143 1250 399828893 399828907
    0x50c0319020f0d150305010c020f0705150c0d08011e031109060319061e1b05030901060b1b06070f0207090b060f0a050c1612020904020f03010f0b01030e0703020d0807050708060c 78
    0x80e0940f1076516008d020f41d00b0800034803100c05000704222007a94401c1d111006003110400e000d0401e0b00c140454400e29000e80036201c4d0349598007402d8141241d060b0b1020964508154a4410036114144001450589a81403c20032400e006800580c8420000c05840001c00003125442000c1c03520f020803038034940c0d41c40341d0030f20265079210b0038003040303000140c1080b8184100c1205404100307015021014004040000740401c070094000601034106440700c0340d11520229074040316083c005000b80e038140280c0b400925a035102d03290201306400f080d8010000a842c06c2003490041119006013030f081101005404d1114645000520525070b960751019903600040058904010030400760984002103180c0c2000001042c22031840c1c0d05070125443d4030030362901c1c80012408004880c10325059420a969a05004000d9100f044030002c00c0e24144140703000d6100660700c914403400300030b600c07402c0c0c01c0b10240031031108030207813080d6840f4070111802c031798403480070a103001800c07a95002d942c10001045 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 399831393 1250 399830143 399830153
    0xc020f030718090204050a111b010e011b030e1f1104030b070e0306010803070b01062d05030108190f0602071a100609080a050c09060312071104050c0319020f0d1503 72
    0x1b00d030300c202400001c000940342c0d05030710b245074462115413042c04a803070016840c0e448001c5d03004c40c1412610740002c002d401c1c100b291455040031300420403004613140030640a00141e0101e400c0040003408072140e0103030007c0100c44401488031000c0510154400d2101000040e481d5200c03034060106601c8a9211341314103030800d403074000f0507008490b241c0c1040c402c0c80c0016482c4001d407419035500d4200341460303002c0c50314002100244401e004450050005808038a00e8001c00154140c450060648001d58043c51402c0c860b11410322004181601000003140441c14540c06003480c203200d2681c407100b50325007130307417180c040e0901350350f121080c0e03030710020030402c4940042e0140014130209000d03004e5406141c0b5139503121059030160a00031151400020420380d02403040705040045002029103403281ca00b00070440301c0744064214015403400010405461665003924810f051556440c2902d2007403002070300107034205001400b41c600060200441c412800d004a8580d20303010100c1c0d8517098558200 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 399832643 1250 399831393 399831401
    0x1b0213020909010b0f18011e031406030c0604031b030b0103050102130905091009110409050606040b0a032103140108010b0405101a0f040e0108160509070c020f030718090204 76
    0x2c6441c00f410064600c4802000c8141d51050742e0203c4012107007861080103a840280c4c0c60320008c085802d15020a610313681680c018010382240288082c2a543c503807091540c0e030300c0c25581041e40320f60b00b030204000180070f500c05080b096030311081c9075021658964890022100c00e03001181c5a94000c81c1000c0c01c050001141c100600c4003032014044c0341002124076480340000d16121540940721741d4218217010803d2440140b0401c0a4000c100c09101400d11a4803144e0544004d84100e0a00e8107140442c9002010300c07060380e8101030220784610380c0258010748264001c01107424103486800c5482d01c240c0005c072042c020701036600003140e00b112030000c22040302c0008090581c105030000c4248401880f00b410105201d40c441c0b13559a0300c0305900340300c2203280201e9106115a82101c0000314118602062100c1c2200b240301451604544a03800c1000c5548100c0e401070018001c2c003070300409407900900c0c00f0710034040507050b03801c0716882c0e01d40355280740d00c1e0000fa62016502d41554004504061003 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 399833893 1250 399832643 399832649
    0x5060f031011120133050403060504020109051320040b0f0307090305010f050915010f051c061b02160b09040c030228090509010e0403050a090909030c210207061b021302090901 77
    0xd03011108845e0380c0e000740c018040c5000140c8940d551380000340859004d01803160203041e000b04044000c010700600b4001030002610345544144100f05441030b03101c11181500c0a84818004403810101c810b4110040d0707420040008080101030140000400c5003842039020041705444042214500740c0892032400c8039003591503500100d014010000181c40011070015900c0c2150048400707605a0800ea84c100d00c01e100260043d03144c0040c950320080304e000000d03114003007902079980c4000482c402e0001241180b2030040c6458007040790b0a05413074150300c4446060543d00740141001d814100b41c07060b524451209000806a80c1e00c0c020b450390308900030b900141401c40b0305840c01e40c100381c0001d60f820806031004051103800708032400254040c0900700050108141c041004450303d040c000c18080802034181d030702c09990035400000ca54108088500d581003078005119144ca030030303412038100903440e841640c451a1080c510b4016910104540020020b0940161729543c05500308010210182c0c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 399835143 1250 399833893 399833969
    0x40c050904020a030215040515070c120b01030201030c050705160f090b01051818190b011e0e060c0d0c0203070e1306052706070305060f0310111201 65
    0x30100001a600c80301044241c81d41524009002e9400425440541c00f4a401c4903038000c0b140030362082050481000340584601400c500e98200ba035800380e40c015100041800380c03880d801900140059402030300024020990703854810b24014040e15824280840b4070055901201084000c0000d400c00060402c050404a541045070259210010340507119904440e00402e0028048540c02d0340d40c0701c202e0031083c14101c0c82c140c091030411004158000000c01d0500d840d445d110140701b0340d5114582409080c01001d95201d8039003070342d01382550a1000701852a80c00f01c01000b20f0f1a01c22000d0041d824615066122035400442900c101400d1180c1070704030798041c0382c01d8001c00c43c40b05100301c9040c03a0180c00c008006100c2c1c40e1808684050158682c5204000740f0b0402115040f42e00080d40e640300d0a80c580e8104500e469800810003094160601e0b03d40c190b2200900d18902010b9031322014840400c011014a00030230a1b900351ba099109a00c00c0c4d80210702241d6801d4000f5050400940303001c0ca030 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 399836393 1250 399835143 399835159
    0x306020a12050f09010518100f06030204060e070f0e090112020d080c0109110411090d060e0a080d1a0603190f09050d110106060f110a0512090a0501020106080a02280b03040c05 77
    0x547c0d640c2d0f5100c00b0180089441350302ca51845031880b00aa001501840d0054414082640c440507100501d4000b52010b800140c1483d6030345181c207105000d4486954001020782c2c0699203025035070188019454002d99110740c4a83c8000000390014004103020920131b800170035800c49500740801c80e410958402e80c0070390f042600c03084d00d10034800219240b1240440322001103403500d00b001740c002d03d080d00c540f6490381316500001040c011524054408006c9884090149501e24094220318808060076650000d20038404640014104251a2100b905441c800540c507868030500109542900500391800c0d00440285400c040e07014250306284050300e0000d010a41c0f41400040c000424420032200b00070300302c4040c0c10180e000340302c407c2c05503400170229208080d81c814180c10030f5001d03c07501807140c42851070001c1d0550040c0034102c12a000b410103032440c0782c520b400384103440d5034021a41c0013004e0070507000c600d0b41100003940d0380a03004803a109a142d103820b14000a41c06e641c1d400241c0300b01c0d92 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 399837643 1250 399836393 399836431
    0x2092e0513030212150708011a120109050613061d0f100506090105041e08190201090e09030415050c1615141c0e06060d0209010306020a12050f090105 66
    0x241d169200c044a0341038810203001c900d441d9003141441d030194550315192441805100d199a84680c5440c10f0703c40b80d502c0c00c2d0f50340c620345060140b176100e001454401c40403160300400151099038460340d0320102c0030388031038030f1540400c0e1a041141c1040d0048030041e4004205403941110f840c00c0168004c020074050311407814105054011811148603643c820700c030009614007544d1251080d58002c0007481c1414102c0d007120903e20022001d1401403038490710410070180b4800c0c0b00701451110036601070b1502d80d015414034001c824400e00c000d02a81d840d100030000002c400130440c55901401003a44d035140d486a40848985081c10713010841d04566808116050103400a50721105030661128146400c040003400c2412055005040160302c600c0040c1c0f62641000f80d503500f00c0f41000c2ea0240560799039589410401c240710800d0600030750402c079000010f1000072102d90081c004460740c7d042840311b02440c285148142c0349e046816a140c500e294085c4083d1307a00034041c1c2a005075901200517000c0c19 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 399838893 1250 399837643 399837667
    0x411010908060a020d1128031b110309060708130b03011d07031b0203070b010b0f1b01090213061805330303070602070b010611070b03070302092e05 65
    0x2030060f2484a0700d030b900103000702080005511034500303911001403164070b84052442000688003442440324421404d00001510144203200d180704442d00030352803030074104801508980313150000c0d00101c2684010005802aa034500c00a08403a500c1b46c601c05a03104d0304200005001c1340036a108116940082c8010304c41e40718141402500d60385400f109916a59808008034040d000c900440c4060000c0d1a401c1324525a0100080032110b0040d40c4403226640d9800c1d040613580b092f25400040c99505200c8406c0440c0511002c42040c1116000440c0c40c0909400040003440801010300505640c1c003410400c080707542d05030309000c0408082c2044140f0f0b000d0b1a01c000f148884e00111164041900360110b00b1040c583d01001903100a0304503034072942c241c0750000095101030b4080e0303080820742000007580752203140501220315100f40038040c00c518005a55078190805000003051680a024500c800d8480e004450302500ca410000f00d1400070f604d82d00e007108541c04130080100202000283d0150b1 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 399840143 1250 399838893 399838903
    0x1f060302030a030f05070c0b04090b1815030f06090303060a0801090308010b1b030c0a021804030c02090a060b132c13140a0503040905060a180f0b06120411010908 71
    0x10f8150800d0185480c20140031291445040d038000d1101c0c11499000c52544100c80140c41078800f41801088006904020000e25551851095880c6000080010941410036115801421010b812940c60a074051302403400c11400b15500b0421758004401c1212034a080000e820042c00003800811038940c203070304d0007130003a001400394100c000c41c0004d10000840103680e42c1c025461055007580e449500403601e41d515000202026841240c00c110310007920209980c2d554011135164480b69018541c1d6400e111041310018440c034003031a554880098035554030300080c042c00c82d4202a08080da41840c90039001000c182407201820045158507003140c20520510703035000b0244500c001315010742482d0030100d031703c0c2c55090054140201c0308140b0401100102a2065900004c8280b045585940a20603480c110344244e03014204204400c5243e0400b580c8010500a0710b24400719143c1d080034080b408a901000d40c002544840c1c004010900ca01c5651552001c1c1c001d180c004402894100029511 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 399841393 1250 399840143 399840163
    0x5040605180a080703050606040b10080a0f02131d0f010f06050f071a0f090a0f0305091807110f0f0d12060e01030605060102010f090302030a0e010c06020301081f06030203 75
    0x40c070303000005954550314201d07008018841c0c0c00c111480c240d203034940341e0749074141694441d0195042030702483d80792404c481c80300f4251f04c1d10741c3c1d140c0940d901c40e40300c84080d054115109012940c00c1000710706100b280d00040018100d04450309600301008100000b1406004003e9982e44083d54014842c00440489643c1164030314540540c4900381d0a000580700d1051000040105495003060701c5840d0032684032502c0340e030035210000c9499950b07608442d180d000d01c240080440c400c801e440380000c2d00540140102d03240203040000c500d071080742e0040340c504040da41c40300480d84000403e4100c00c1c00300501c2d2058404d00d000b50401c1590150825501e00d0404212020300020801c20520b4208a900220003403d20942d09109035075a410041c0041000303a0320140103500301007101c1c8042c0340f9805417000d280c1d803540c015450001c03240d00c1206d00594680805040042c03200341c0601141d42d60001d14080c01003213018140010000c100e1030001200301171000c40090403e041080542e8001c504036810b = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 399842643 1250 399841393 399841417
    0x1215030d0828050f010f06030908090120011d0c121509030c1b01141305131113090501060908030414040605030a0c0303020c06120402060703110a0f050c0105040605 72
    0x41c2050200802e002e81190300b078058a0b200030426480196180541214100181c0322405505c40c002201594460075000d40800c0c03081000c4180c5500c00c145c2000911900724070a010069044541801e40d44141c407504590903c5482d0342812070300030f01154800c0d11045600441400080c840140c89000803100d00791003d1070710000403000803082c0101c2e0f406000074800d865845400c0c001002c5c0b0b0300d200a04441c00100e0010900b440141401d04590742e00e202c41d007262081915100801c07039002c8003400340344041a04c42c0032001401d030071000034004c040d00703000b80406460b0619904c4000c0b40c40580c000e2080060706101003083c141c01104407402d503426004030f00b0210104101203400b82105e5880303581c05101d45004507080c000002520b20940b403096095864402e0b00c07108011090081c44507101c0108580c3c004240186400d900826250f840fa007402c845240d2030b554401e040c944000700503619499241c1c01d08040010a00000186000909205050504041e0b00404030f00036003900c040 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 399843893 1250 399842643 399842671
    0xf010e0603070908070605030f010905070e0411040801060e01081011030f04020301060e0108030a0207080d05180d020a0e04060501060f1713120f02100e03030609070e03031215030d08 80
    0x7081c80c4960006000b40c071320030302281e91103036841070020300c00d60003120303036100c24102c05001181c6101c5500840d4060300e09a5074503070307115004004000003090b18038207441025038200300020300b99400b03004040040400d03d82d43d008540c5802c040504149200e0240b0703407624505100c9001389119801901c4d040100780001d907800c1d03a80c52021a004180075000381c4a10781c04800000351510000009001101d5590309856100f943d41c04602c1d6982115684540800c40032711000480780305102e0b8680c98894020006402c003102a0042417030b03080f403a008604807a10756410842401000d000700d60060006162035008454140d01c020051260405800d007100c441c4404100700b05c1d00040c03003010107504016154001180c449000d08a1005410100054064042e20b8180c200c01881010f1403044440c018500d103a4030b070700070842c0904008100d00c007480a02180000e0584041019010240c180c001904079810301040741806241400e90300c910a9110100e08010107074010800c58000490300c0300d4507 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 399845143 1250 399843893 399843901
    0xb1609050f03210d0f051816061d09040309030302151e0402062205041503080f0903070b0c070501031d0c1e0409120f18140d02040510140f010e0603 65
    0x1403030340d10841056241c413a0404010b82c000442c07a50105004049401000c00480e8410780990740320581d039103010003c010224000c025150003256090801c0f0070716140846108008c0e03000039106101a20180c002485022041c000c0503010031403402440e4814072400d40500d40129080f1003141c2c0c0d0408505841c0d5404042021074403404140c5413100c2643c4482d8860f0084920071001c013480a111b1280b00354200b80900440f450708182080c00c0d0780e0011156071500c0100c403a460250780c00415070302d4251203211000600b1070003450113001c90358440030160250b40d1401e4001410313240196101307d5010944140c0c00d500c09400580307034204000c29a0111140d0b496200407030047c500c000c1481c1e400c68240703030010003004110440b041001600b03440d284100440b803141283c01030342040713071000201003e035003d1201c8500b14420351010340303008082c10310150300d50740441c1c01e591080d00c941162441288090200300c10030845d000e1100020f54010310385001c4a0002094491015101d41c05440000702003 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 399846393 1250 399845143 399845203
    0x302030d0215011e0801020304140105010522020307300b040c120b0102120d0204030c0e070504031b0306090b100902090a03020607060f0c020d020d0305010e0c030a06030b1609050f03 80
    0x104e0700402c00c110085461345080e040c1031080c11046c2e01050130742e502e4000041028030f8290210410701034070b040b06580b1058101308080c025407001c0c041c0c10070320521174884402110450644500030f0b0040b9580c50226401c0c0c02020241d400c0403080e07500c200e013001c0c241034445520000203203000d800100e020070904034000050303007080c98110703903040034100000c0d415850303480503001170085a100b030280d800310702d542c0c6190441502013a146000000d40420041000c207da503200041e400014440702903a0316a00c0ea02c00f0122642c091003120442668800c100c4448408008140107180e40c04040d883d003410348001902d010154003009200d08000306000b42800711541c00a68000e0508408101600c5080300c080e40c0e9034801ca41c0701c0b0040c410a50840401c0344680210350481d03900302c3c0000c0894407030000056180d0001044410403070b035144000408511003001e583c1c0148020303040704c010f00400c0c0c5401031449095420507030284203c0610540b403610f002620128003031841120340c891700078901c08 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 399847643 1250 399846393 399846449
    0x1401051311190911040807050607080f0d060b07030c14070806070f0203090307060903020a0b0c03031303030e100b100311030105060304050a0b24040524010c06060f0302030d021501 79
    0x20441080c0d1130100d4604050001400500c15625090211007006a8032410880c09214151004080718400d00c03007503100e28180750191400854607003002ca8502d031260110886038004103004d80018612a1001d000e00c0810030344801c55152400c0900001e1b41000c11301a40d410000d41000100840941440389040c420303c00e540186000a059400d459a100c10040244505001c02e0344604049000010303520010412101100541d1000d9400c558070100c0d002d05441c1d8030030080d0180f45c4c0303420161102c113806000707008200c10241c000141a4035203006001c00d050003102110141444c00d082e4848003081c5030192811102c04031103440d5039560361301d0031904080e24080b00a00700d01d0380405111103110f009a0720346c90318041c00440086c40502d80104015a1015100c4003000c02c0c1034200025688a031012080103002c041c1000d031103185d81907403140105c400c0756010000d82c2e201d21106008500e000d0046034130400c0c00b4401401144810001c22545000600c10303081140e40c031001c56079040c0c520681c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 399848893 1250 399847643 399847649
    0xc060415110d0e0c01020303070f080c0d051006020f0c0d060c180b0a02061e04030804021507030903020306160f0c02210a022d091008060103140105131119 68
    0x140c40e5203500408420700041c085445034040140a040108800ba5200002307907441049699039802088101402c20350380030001901c20010340c00e04000105071000e0a001d8075004180c452079a00364a40383c550000e0600214481149031604001040000703562500c80d500400ca400c1700d400540000862401d035030001a2806282003000e500c0000110220020094044c01c000c0d502514519620824001c4500d043c60038401001d103240070200307010a1081485a510a04c054a404891840341c5908121a0401c100c05c03400604510340a00071410184034841c0c200e8011215003081011110740a03025400351000841041400b01c0540300b5035035000e1107144040006220100c81c040c104982c940c0b106045001030340940c52900320995040062500305900b000d448d44d101c1205082c55040060000019280e0891140c01e04804121000d0500490780214401c00308440b1040c19015042d00390746004141d901940014002d010101e10328a0000081c5442229040c0401c690301d40ba500758808550 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 399850143 1250 399848893 399848921
    0x50f090603060f0405040506070e0108060a060f0207050a0b0d110739090b1206190209010e0603070c0b0f04030206040609030309061410090513060c020f1f06050103020c060415 77
    0x41c01b1b00c400d00c000031400e030b0302910180c0d6898114982c6000159150982921416044032004a0802c1164810f1f8032403001c0c0c107610b205072110300c0d03070340d000082c01d801d169000004151800220b403069160703148500302e031900315a00c07190b08200705a203499041c2c0b4540d880090142c1c0503000c800a0f105a003050f402500013000003a5544e894070381540038008e100c4600c00c00e00549100c0300b500c05000d000202d40d072090000800b410b5580307070340c4400c02c03021790001d40c0c88a040c4101c14911002541d01e0801843c451007180c0e82e00c00a0042720308140381005000307002c90001030207081c2400081303680441d99690041e040b58000c1203103086071a040f0024042c07010040d0905290141c0d40603240722001c5080e003c0c6141c2c654942c829502c85120740215881941d0650700800d901c0c40d41e20000f1015005600601aa40199100c42050b80d03803082c24007119041c058401d4030321840c1006119100d10810016040c2840c0450400302c0001c030160713131500064000751030091040d003201c006402e41d030040c03c031b503540700 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 399851393 1250 399850143 399850151
    0x1d010b121009060801061401020307050c1203090d0b0a0c05040303080f100b0705010504050f0708060103120203070c0909060f0504050a0605220b190c050304030f14040321050f090603060f04 83
    0x55544170300070f0031280502615080c406100c5a825840081503800258000c0c002d003501c43c40b000b0400c20a00100d524000050006000c040035076a40c003540d02c042140122a106143d04d442d100e007000301c602c008480b10034000f0610050000c41e5002c1e90f010740c00581d2203034620658554501d14181c01c2280d0f48201d80038840010028204041904280e018903c03e00444214240795000c6a444030130038042c80b02250b2001300101302088000030700700001c4410b401541d18105543d03d810f0f555813000e42140044540ba02852000c008151250350b0400700051010002410f2607903034070352240020341015040c0e94031100410030315101d0480c000e0b100000600403a0700302000f4506020380102c1194044a030848003001d504404505000b5903050150b1991031a2641e516690f00b03a07030104401610404000e510070aa070f1240b0040001400914052044400350855030322685201400c4c5040182c2045030900200742c4013050344080c3c91103070030102d0300b0ada00d0f03554203808103103804605038407a5440b44c20 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 399852643 1250 399851393 399851399
    0x109030c0311030c041e020f1b071a030c160204060803131701050c1608041211100e01021002091f030e06010b030705180f0d0b011d010b12100906 64
    0x4039410500c22550540658403030782c84c00000c002c1161448001c03a884038040c43d0380c822005035964003c0840a05c54042e43d8141601112403084180038550054800d61102034144580002440c0703141c024030961021901d14036000f06200010b010310303c4115080e40c207070411a021903842d034001c040500340c010100c0340c40d84402000141c48085d1445030030f0b03402d2034010314034001c107806002d05031046500c41a154904060302c03240700c846460b41c410648100500740004610303001508060305041e4003038103000144040b540100801e2a81ea51140c0e420707c000701d1071406143e40c0205450307100400e0b4560040c1c6580eaa81d0114a00400c102102d81c1c0c0100706524040c461501a4440c184e8481480c0450307485a890700380884d16807205403040b001280c1c0601c2160280351074417241d101d011001034214080207a403000861005505040102ea11107958001401080302440941c00c88100b000d0a4030b046501d0210307192174510138034022608024815000404001c0642240700c010020b0130401c01059079 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 399853893 1250 399852643 399852653
    0xc0a0e25120c020a0228090903050901030b09100b0a1101050c0a0e09040b04150f0e0c0f03010c050d0c031d1006150e040b150a18050102070305060c090109030c03 71
    0xa5906100800d261a01c0c901c1c02c1d0141c800241c0d00310480c0c0c068100280c0803506c0d0310f004084811640b460322580030001001c01c43c07240d80d02440c802588a0340b1102e4a8140381400501500d0b1812240e81c0a001100204421440c8a45048040350024851140c1d5503045640031a41c800c0e4035180c0c82919800c2c1011b000c0845100070007040c05a1181d6030301d001c0c508038601040b540900036030700901000040b04c04500400e00030781d00b000c40c05080c80c000040e40d401040714001640c51070000ba45481d000348000800c14285050720044491080300200701554151401916034021190384201c1240e0364805068654001d50160341b5020000592403502212268181d5845c4020308440b94010b00382840054070485039060300004214075110034408944180c1403000a01803408416804402850115520f503e440001e00081a50303646800001c861882100041003043c4d105a045602c03071102040030030400328405401c2201240916a52458580100c1d8851569003001d00844035080340001006 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 399855143 1250 399853893 399853907
    0xf040209030f0c0a242a050d030506120709051302120601060306060905090705090a09020d020c06090a08160c03080a080103150c09150201020d05010914090c0a0e25 72
    0x120480c0c2c00030199803105d07103129442c40810100c20380702402c6000c0e040c00341d024011900428506c0401100007040000e070480e00078a03240415140394214241043e01039915000301580008152944013910f920404016900c41041c811100c0b2555980007195621007201c02500300c483d0000c00a403c1c0301d441914060301e4200a1140d5008a4a0040300090300341c042c000040c00c50310010040000c0b1b49c2c07a40002d848581c4003030a4554010031081c0003280101e070703501c06032a04900c514401a190360f40201100d140000291064a196204201d09400141050111142c50450092078494128685003104123240a500011700c5040c1c04600d410b501948071000d03a0480e40a03812860640214100000407100c0705142e0000007441524144600c007032024410004130494800145001d1000c2003000c2101d800383c0041001710b07102c084d6481070703614081e40141c0103c41c0d4000350005440d8440000c50624052007000c8488003240002134041c5c0b203010100091060003880003c8042d0400e1000b4244 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 399856393 1250 399855143 399855163
    0xb13020307120504020a1404091209051905150c030f1603031803020606040e030913090201080f010f050904030504050d030f020f0d0804300c05100b09060f040209030f 73
    0x24801c1c040b0000c405000b4003c5030301590300075059000c080d050101000c01841a21041604151a04c540c04005a003840304204841c50f159100103899080404001c1c45070701310216003048040300c00c814000b40e510f06d0300180340301d0f200210b070030f54580c4d113126018290300940240f001c40041c0424002c0428041c51440d5401d103200755000c01c000701d000c040803203584406000150050f8042400507d59083c10303405100d000f41c100080300c2c100210b20b000120041d22101045280c1707915000c980b8119600310460bd504840924a0b0307031802e6042000b410701c0c448041c410144220100c10128080c5800342003114081c0102900000800c0360361b007005031000c0c800140300c1c0d005100301c000540e03071a100440d00c01030558982da621002e82e20b070740e220344640202c03400054041c449600c03041100b000d1104603c28103a01c1303680701c0004460245c01c006041c00c034003100c013800090602c81d02084a50701c5100050b4400d404039010803541441c80c01060080c050641030039014450720365082c2c0d44034000240303c055 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 399857643 1250 399856393 399856397
    0x2031504050709140f070f030e0d0513090e061506042312010209150304060b03030c060f0c070f08030709030b01140f030a020913080c01060605030f0915010501120b13020307 76
    0x13000d90700a01c42c1d0100103089501c00383c94220000441c0c4128400c0300007244081d0303d0310f40400d410403100042e60400403a07075078501c0410030008030b11002030284d0913000c0040c5180c0800b040b01c1145014000c0c0c40b40d800406031400e9091015401c0c103603940d848207881c00b505842600314140c92101121861104a0000705442800e010381c0040480005008a54039908045c0015098002c080a81e1240741c2001d80116082070300c800042e105034904201402d0801107100040100b42400c0c22400b8007041c024003e4040030404100140c04140d00e000041c0615900c4904135030341b540c820340d04554030701e502d4000410741c1c1303444000011f0a40103041e111250603821551804004484e600301550f40303d4014000b0340180304440000c040c103003441c0c03000b040075008240e454504485404181d08440e1681c12030000f00b54040180000003c86202c0a90311000400003003000400c0702ca00c620301d0741414403d60b81041740205038000c94400f41c0c0c000c910803500142104d1413804040d07240e200030303410031255000 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 399858893 1250 399857643 399857651
    0xf07050304060f27060c020301060512030a09090903050304030f180906053c03071203051201141e0d0501020706060302030d1b120e03060906090606010f0203031302031504050709 78
    0x8500c0394005022900002100089028203217000341c1030720850100d02059905559803003000550b80ca03804032101d0203105100143d03648103c08a0058803400144d040344105500c0c1440150000785c0100840ba0840e03054208880c070b0b4128808222042c80c000148440508450100000d9401c1c180e040001941c1048130400400d40e25401c510000e55082c2d801040e516403050104070750802800203112003e000582607521590310782d40b04000300c61041000b1000250000f48940358103800c0c490031409844c840c82c0c503d000204403800503400703646042112050a00b03040d104e140d580e0b1094174410456510600070b64407144581041d000a02103440240c1c001d016202c3c0845409228010a980c05665000c1540d803640c0207450300c4c0400d01c071041800d0180701100304101700c5943c042040d03a204140c7c01340280340b11f192140c0f0007030400d04c010f45140d060054611040d42072a4002c4140d980c00b07071f9060811448141c0c6400081d25200030030040c031451140500a0100340319010070444292003030048140 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 399860143 1250 399858893 399858917
    0x319060f020a02060a0b010e06030c0d060501051c0507090f06110d02190b0406061d07020c09100e090a080307090f21020f150406020304090e0c150f07050304060f 71
    0x3a84a09000140160004c90000b50380341d81d5540303e01c40380c12040c546141c000d450100420748941c0151507c4220550116a00454480da800340c180034003000c0c6001c0c0d05001c88481c1030201c0300b00365040c0b588055120340c0041ca51134400c40a00008000700e030880794845a6a00c3c0290881162280d40c82c0103005950350380d81e4150002600b403003103c00c2d056403041260f4150f03e41e000344031000b4001715603441e224040013400040602c0d1025581c80711008d010214188082c010749040303900701c4282c6c041e08468040051a180030170000e0100c0c0c2c1141403940d081d82c1ca0114507820b081702541e0003080c0003008000c0c03000880e40401071109940491180940c11507c1301c0302c85086041419001280000c505600300060400e030020880452002d042d031108400e104803009c00c1074101e600314800507400800c0070444240d80340103421612170200003802da140322070000300301150280d5081501220340001e403441482002c4049402894220b0252074540f6250300f0020300b180d24000c5000001103040141e8 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 399861393 1250 399860143 399860171
    0x70c05040506030619060b03040c06030f0903141303021002060702120403050a06180609031107060c020312030702030d020a08070801081506040e030d020d02030f24011d031906 77
    0x50040c08003d0050416640e010406200d41003016170011201d07850740c5000880d4080440950f0055109180740245141001801402c6804611a41c11102d04068019020070340112421000761810750640380e6549402c3c003113113507442076648000e4001d8203955403600400d82c040b54590056101e94260b03002d5030031300c99284a5900445c00040d1140d0803403030822000440302e901103080c00b81c18001d01c05108030f0345e1302c0d00d1040340c2c0d2051094010841d500b0700d440740c035141480044094812420b18080158182d0003183c0c2d03484440303410360190900007020502c1c0314000c0040c0c40c0b03810001c0d0710030756451000e41d20007803901e2360a40c1e110000c03401c1c00001181301e4202290881c812410303000b001e02566038600821000d820454070303a14007404100b20000120800d80010111507029480150307070703401c0a00c036003a1103940c02060001034016480780c0005070048090503111412013464125100b035007283c1c0200c8050f100082d540d0f07152285000c0c1100d440b641d820b658144030300540081100741a50000 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 399862643 1250 399861393 399861401
    0x2120f190b060a060e01030b010c021008070305090a030e060d06030c091e110a030b211b24090f0a080105040b07050c300309160602011a04090f02090c070c0504 70
    0x108004611704030100d4446511a0344044504c2c0414034041c24401240d0700403d0a00303008844c070f20001413841c1c0800022070303010f028041e04055214014000000f840d14010300000261503035606c80d00000802c0101005207402c10005990065040e46d1b0341a91440c2040051078905c81081c03902d102c540140701e00083c244505032096803046140d514113040700c4c030114002c1c10200145940420342200002c1c6a844c03075204229175800160041140381d644201098408400425241c451a4900340142501c4d444a1115141c0107061034003540707a522010005680005014003590041c0c0804000501c0301015005580114014103084030a83c840c01c41c12141d9100d8141012119802803601c110b516100000680398481c1001c08452500c81c00d03c500282a4406c2e40c81510b82d61002e551401c80710030b0001400010151360000b000985181c0a000540301e1001c0c007824071555441c0c000ba0705000b050308584048580c0106800701c580b42c2000302220680120006a50701d2140071070106640c102445 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 399863893 1250 399862643 399862649
    0x10c060b1c110d020901180f0507110f030906042303030a0c1b0b0421060905250f09091b03030906090504020f0405090c040e0c0403171602120f190b060a 67
    0x30015141e60301f4000240e10311100d0342c40507104665141e038002914a154410b4a010382400e0380c075441043d04090003249880010f419a41c2c841e001000160907540e1140201c0f0100d9860724840e4500301104200524910136500c2a190180400203000440c194056400c840a9100e1101c403042000c14100e030150001e4240201603c10f14100700502c190150303103681400242c906070307020106031003030f035915170076103100c0b52007220168031030360320180606010303030b43e0724000034100101180c41481c3c8034200342501c1d41d0b80320b0280032a0382c544c950028404002102d1a80c1c1e02000f101d0201244d5900e00100580780a20403040080c010310f030007081a26103402150f2102d034480380503a00f042d041c0000c204007d81c0150200c4c205030420440040c94100e1040c655100745003040304191154510300b4080810204e121901d90900401c10001103007a0011901c11303c800d4041c0d9040b918009050000ca00d41485104003040c24400d1500e026000c0c800103a005040c0d91140c1103804d895110711041c4240391038240 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 399865143 1250 399863893 399863899
    0xd1709010e1203090c0429010c0b010509150d1101030515280e0702030304021c2a0b0409060503010e0604120305100312020313061409010c060b1c110d02 67
    0x2403200a00540080619006001314080d1010021504002401c586441003480b261803407800d045004105140381c4e032009244203080211240c0031030740e02d603d044101401031a00c2179404001244c5202030303449402541141c00f03454403d0034500b50500304440080c0380348580c0002d051400150803000f500403074524000340a0b01440d07403003c0d4042001c01d80d9000c051038003018240143c0010b10140484c403094099003ca030013450f6070f42000e0052114098940300806d510103d254440703800200c038005401d1000c050a12003120a0b0145c41075030300142d82c15802403055150114012510f1035580e80014101d40049000b00714101c216041c0c2a11810100c502030714524413680c0d0710048500940207541d11040075480364030041c0e12079a510f51400b110500c2d0300016400030628a40703851002146401074002c0d800c081d0700cc84d0b80240245c44a00c2040c01d034904111203900503034100a5140c204826050004240d0038034074050844e448509100301509440d04515400c03012550f041031504580c0454004e = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 399866393 1250 399865143 399865153
    0x60e06220308090f07120516050a260d031e05010303140c0c030312011716090c2303061011061329010503010b04020f19110d1709010e 59
    0x151010b903400709008200740300304e01440b40400c0740d0040921080e00503100d440c0340d41752181c5140c10600e24181c00307444030140c0940751080c14042c42e070343d00d44100b0843c0d060507500b050706070f21617441181860710389070040d0036072059881700c407034083d05038203d0008400818000244d049603410400c003075550a00c4054007042081613080002ca008a000300858048041115030245480d40803e1456000d0411440c800c01400010f02000906111b05848458400010400c042c5800d40c0302990f5410b51181d00d40880d62541030003003160103200400018031004054599590382000c1d40190f42d40f04541c02c5105800c40400c0b9201140144086003140466070000d180580d0303000d019260070020084140c2d050b030302240d402188541034214403040d4810705021581316500d041c0626007507800d07032800c2502c203d0051040e6a81240110142c4803029000308580300e050481841c2502d002002d0b500c07405060062400c3c0c0503c0e6508122203524032010b5202120044e40d650401a00300d824000042e134958100c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 399867643 1250 399866393 399866461
    0x601120b0f040b06070c090515010e03060718090e07240206070f050706021306090503070503060c030a02120112020f0f0d0611040503071e0608040b0a1512060e06 71
    0x2c16480312034242c2000e0020b41ca0040c0d00d880d1000d11410690095040c561100e0400c0119001402c0c103122810080c00c1c003c0071005018000b03600d070704008143d901008219200e004003d03540b081a035004000c841000c000050410720700c207441d400c260280140c0c80e580303010f5a200b400036050070031030611031690141c0301d145c44a0108440c2d40110210420410070288038040c0031074a00e100030b0684660b1103c0d0000313200d01d0030070003620403001a0f0103103219130000442004aa01c0c0440e00d01d6000c7c4800c40000c0d92551110307264002402040b40d2011243c039800008144c9100c0850400c0d10903000b141c3c1c82c90102c02900412000c8802280f1450304840121a40f9001800640284030411340c480a0203003080e494101191400d11980d01c21072003d100d903110b40c4c41c920512001c1d0005001d0519103a14241b92a4440d4504007201914021120380c4da0002c80c040c480204080308040c2c090042345000e9490f85081800250901016000031402014086070050740e42000660020300229405a580c1c04 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 399868893 1250 399867643 399867649
    0xc070203061b0f030a050411030105070504120c0801151a0f040b0705013c1515090b0d0b120703031b140307080a020f0109030519020109020d08030601120b0f 69
    0x56442441e80c40e40801c3c0a030311014921500907510903101c0e680005141d21785401d0040315498007400e128001d0745082d00707104149500c07900701c5e410354515840b50401030800d0300c0c1490024030300b0342c04000c1951920a402d07664480440401c0304580301d21030713000b812000e5143c500c003062146103c40c0c0c1000600f0441005280445005010242d0140000048500c1c0018080c0b4904101c250007032604122050781120030410211b00c0038800150002c1041500a401c001081c1c2000700d000700d00b004045100003e800740d00c02d50301800605001e1107001e80700e07802442c4480c050a03002c1c40c16445000c41451407142e0341c1d0000b54480c1140c2e099a00c140901d0070b21440307180071003100c55041c1c3c1d0160580040300c44540d0704000401e8294403030750706d49a4800c03840e03070001c0c10048c20060042143e41010702c00ca002c6035105c0c080d5074905000341c5100001034951441030f401012980802500541d41040810a221514001c0e41c840c1d1800c0e29440ba043c05004681c00480396103010b1290f100c1906500b01406007 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 399870143 1250 399868893 399868921
    0x80309070f0902180112020d4805070203121309060522200c0d2307020108070e030a03030b03010b0613090203040201020307050a11030c0f03060a1509090605010e0c07020306 76
    0x1013480d4001032920089420b0081900d401d0707802030000815062761081d02555a510b280078101caa0700281c840302d10703410341c1ca5211036040300c0b070242088404103003042550740c03d0250003440100003103865502c1c9245411411161a00d00c544544649407000c00201400d10320b130021400042494940c842105040ca080c00519030030302000c2e0030152460101c0b00c0303010500010f200d14030051005003600c00c171010f001442103c1000804105a842c00e0941e25150300420907240c0349a42400d144502d90b951300411260755000480c0940d01d441440458014941c2507030000c80170010990080c007124035884c0622146209042e0154494140030000f0410000c90750301844c0c10610510550340740080315182c191614a20407001d0303c80c816000c40324402840c0030040c803440c4150039520341c421114070300d00103074a6400080c03410b445180c885d690812412032520510020301082e034810031820a1038100800202024050ad041c142840008914000c6100c030a4400c815030041c01042c07142d540ca50041120703 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 399871393 1250 399870143 399870167
    0x1170d0c05100911060a230408060a09020612040819020c030307030309080903070608010810091e0c082505040603020d081c021b060718061b080309070f09021801 71
    0x504e2000480496490340010500e001c5140e481e1307048400781c0030a443c18540b08a00e02801084100001c000704000450031903400003e8500000380d01c6011300204e50300c1d11030520076885844480302048100105d1602a2031101c1c900503055210003440c1d4020b0b40d03a070180300b035402d90541c403d0216000291003034011490745403059201d58185100070020900c0c0c04080d41020f00031070000c0780181f200c000c1c10003108074040b0006100303103e004000d4030f614029204500707402c0041007007544e114040c0151501210010140d6008403507540c280031000d04540150318035030703241d0311071343e0038002801d441c01f070080c403055070340083c580308000e01140c2d1484100c4c0c2c44132101c2100c2c4000000009001811031020b051250300c0b025459200c40c501c0e2031340c01d080141c010154400d000991011048120207203100c0c4065a00c85c0c14010554005508210f010440e45070009020383c07000005c021800f8008078240003180c1c0c4955464005580b2880c0d1641a409488a22003903203205c207680c0c0360030f50310405c90031040c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 399872643 1250 399871393 399871403
    0x30607053114150c342c09033105091b0307090513021c0203092104050301060f060f05130314010c091406030103020f040209060301170d0c051009 64
    0x401c3d4003403021a450f6002404e0010460b00101200c03800c0020a103903000c22001c01c07511800c0d400380444454024102c850082d003203c0e846000d00d00392200e400c2561410520110551004686084001c0d141c0e03e52004081c2800300c500d401990030350342c9801c00c850fa1061482869409900d05020038040e1b81107000b01365420640c188800340740c508003080d00079409070710f150781e404100c64100341c00e0010341ca442c00700b20b100e003520412000c0fa5100b00840d0001032001c4c14000507075203880c0e00355902e28080f042c940d5540110703084020780c1030100403407000b082100c405500901121b5a0342c20801d040d41c007103100d2140410454400420514402c00c0142a40d482e0351030309403811038403601c45000e000e512401c2481141c1d501ca103030a603143d8100320000014552041600062190000420340500040c4402805508013483d4407440d503480c1d406039009810050903150301c0307694507600641c2c90344401070b81c05070394010051700811680c410114540c145070440d006003078540c0440009001030030380f6a0b054071 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 399873893 1250 399872643 399872659
    0xb0a081203062107081203070807030b030c061b0f0102040503120a021c050c0105101206020f07140a030905060a081609030c090209042906030c0405030607053114 71
    0x241d518440e03040c0708000c00031200209140d60608041700d2030b162801c20f000008010600c100a8102d078002e10041d8405454603002c100484003001003858108480a021740c021004079942c04003882c09a2851040480e00084440034486e500500c0d00701c0c0b00b10b014454141d0405c000107682800341400500d24918984115000000081d5a0003030095070b94580e04002040010b001541030004d002c1c594010500358101c0641525003540c3d542d0000e0310843c018407071a0081040002c400d03525007034174100b0f500034544080d85802481030940724060740303000710302207654000d001c2002d0600d1416208a1001c40e16640229101e00312031440f1301c01400c601c00204419000003000040402d5400070040107924405038440c0c2c10703201044142d52251403121244d15234000300780c541e400c0d01c500f592100b0b10240c0e0003583c0c0b0746442c20740001c54400e07604000d8051294006109003e0382c000028118240034410408064614401030141407201c183d034103002148101c42030000146007079100100000c01001c4c04 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 399875143 1250 399873893 399873919
    0x406020c0d17041517070e100504080d0504030b070201052a0d1b0e030c030a060c0909060810050109090f0215070f0c050f03211c05130201030b0a08120306 68
    0x42d5140e4050741180b0740c80106038160703504d560b820400e00d4000c103800c115100b085207803c1d0001081074000c11810ba00c18141210441c190714040c0c802c40d401b400e150000c0c1da120b20b1485a0161882c4d01ca884101c50020801002409086c410301c2610700998150540400506140500c0f0045c00180481e220340c0d41c1d13042215606a88051081c3c02400c01c004600020110321000f028100d1041f680025010f80c00c00b64a000c42e99401188c255002e46e4440740019802801401c1142c2e03081c29031b003019a0f4075203060804a50b01c03000040c0000200701200060280380c0e22040490107444000c00002c0001348981c00d0340b401480d00c41c1249820817040400f250038403030310381c99000030405413807801c0e10030700604581405241420f03c1e624401c0d03c0e082c0d008144441a0000c40400c80c2d8444e000d404009402140f50821600b40d02104034640c4c0311301c1010f0016051100e1620b140940d007120407030100f49040c004a4142c24062640c0c011280401d01410021101d11990400782c3e1000b00a2075011484038850 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 399876393 1250 399875143 399875183
    0x1827090d02101e1a040b04090503091c0b180709020403020d11151315020109021c0f020a03060b0301050a060b0414040b09040305031605040e01030f05100216170406020c0d 75
    0xb21142840c0880c1c003542c10013401040c402291001180c540c012820606100d021850000072112020000ea1707180040c00b249410961a015005400520004011003405080441c11590307501050303440e02a035a525903078103591000c13481248002500a2081160480803801092060302076020190607001e01c0300c02d0703884c0d00609a100244da8240c0c1084000184080c07404c00d5601c80301120302d40020801d503080f0f50002005048030819203124408002c003500c00b0451803401101a080e030240180b502c1035203a00e4440c2c05442c0c1148008c0c003e601c0e000001c0e483c40c82e1809010110b4408140746817409040c01c4d00a0031110000c034105410030303207840c1440c8450310b40500d094890760280c0c0c0d85540300c0c1001407002c01c501d40000061400c00000b800300b400048070061109044a920400d000100f8450345400760804040000740d00f021840401e8414020003402d80d01000b41d4440c45810035035100e490354800450095000b0100180d001d174032115024200f056208000c18003840c44078510b2440c60f07000c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 399877643 1250 399876393 399876401
    0xb06130b09130c090c08010e181912170a0f110f070201080c0405060405060901020c1306140604080c010e0105120a02040e0609040b040303021827090d02101e 69
    0x1040784140d4405990409100d000e031a000c01070000e599040c8880c0181350401032088070180605d020642000c400305d030440b149e6814805401c80390344c0070b950003040081601e08080000703e009580c1d1076111800300c0b280c0391264552400118009110700f200da111202d03100c00030722820750203100c242e0366400388000b160440c43c060499450047c06c11940d9089600c001005400c01406164450740140402d000a03038540003500c00380ea0098986980b02d021910040b403509034540201e640041e100b1400c080c2403546070704110151091455282c40301402d4005003c450702c00e41c4101e80d0143c0100c0d005640541c89828038800320101494030f00e0030141c25031001403903c94155000c488950b40010100b1544070300204040d40100c04540c40c1c3c1e0140340039103c094164000a100400b01b580c0006c03503040e00541d1407071440307582c00d01416103001201d22010540e5140715404016002c080032100246828500007104a041151a0f0242c4154526480614040c00c254028030f4240e05600e2404569110f961007 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 399878893 1250 399877643 399877651
    0x203070e0a0608070b09090604020f030a0501030c061d191a09091602030a2307080304060f0605280b12151009030f0f0b13050114040b06130b09 63
    0x200c94000d0a10201d0031040b07032100c0e401402d054001810400040e100700701580e0422009542002e001ea48240004d00280700700c08540c02c55400200a001c014840ec1d07220318140da100700c442c100442d40350703202910f00503d00e0006400c1b01c00221040180e50505148840b00d5040099520002c242c91700c0007050ba0307001c0ca07960000c2e901808200d0041500d0700c81d05441d04000984051625940d0b007060007516031050440510078000d03c2d540c2c00700702805542042c1070b5421400340040d1519000d20384000264810354041c0c42441c240307206401245158400c40d402c179000200840c601c907058406609822624001540000300a018005003071040c0ba001401c0d0b1080e01000c804407850590b405507103600c94822010b000741904c0b07240f8038506800a101d4010b0326000100c403212809980b070484154508214018103445c160404d00c041102062130300080c0c244210001d00011004075680d500c502021100505120703489000704000d8101025a01e13548882030b9004511072961902055005005071 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 399880143 1250 399878893 399878909
    0x204090e030c0d08040b0106030509102f0c340603050906130c06030b06070c0305150f040b01030b060301090203060c0d11030f15130f14090105040f031803020307 71
    0x1004850074106100c2d90f030065020742000300c0c450030151500b41000505001d15420b2603a0b401c00b043c034120302086007001d0f62892160921410552401c0c081060301c08240d029420361000302e105155503c1081a2270f5400000002451051103150020b1046050100c082c1c2d0000903c044009421761720300e002d41e024140c1030302c000c509404d040019610700f9000800031101440e0015060b00002c940a8007001103c0492030003150000742000003455900c90224010001045a4000002c100010902284032030038882401c04d81d954490303d81c02c52003030445006113001d108070f005000049101c0010358002070060000140390a0301d601107490280103a407804026500030a42074080f0019000e29039a16888240381411410004a08403401101604104011004525115040c0c8560302d24550000c84c0d444280282d07108450804000e001032031802000c3c500c500005048403605001d0940921340c442103034514028140c0301250020790101421807a41455140000983e408014040140c03c0030 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 399881393 1250 399880143 399880147
    0x1f1806020d0506011403160e011116050405160206010e0406090f150b04020a0207050f0607080d0207030e101706060408030a020c0901140a06050703170c130503010209220204090e03 79
    0x1440007401c05e4a18a015101000c0100f00b08440803001c42c03030480111055040031107268008400681c1d4156200400b80311a10540f0400301d505007605e03400d84c084a030166030400c55500c4209000d00145090548000503910100041041d4280781381e0203a0701c107001d242c00080030581d5940300d00590074100400c4d5203228007181d0707500341c1c1c031103910882108200c00c0310114a000c42c0004084d48403000e522445200b508030305003c1c07005484031800c07503601c44d07030050000359160407140c0a10300035088008240c000071028001c4041a04058281c80080c8501d5141c0c01f40d070b000f03100c02049000e20014001c9070428070510002581d040c0400c0603008612045d0060b104100040060003e5924141c0c0482000000d460b40300d5820703211440440b060b1412031501c59a103400e54142139558001c0301601ea0141c005420070800c0302500e003c041d00e4402c40c2c55014991150740c0340304040c240d0140c002901d0740840010155420f0181100e0b134a81d01c010383c4080942484d9540c0c000808503641000d41c2211a040 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 399882643 1250 399881393 399881401
    0x403060e030d05180d26042004270327090e030702010f14090a032108190f1e06030c060807020a020609030f101d1f1806020d05 56
    0x40d5003c0c0551081d00702c10950349840806101658682c2c004260800b0701c0584440b60442c0c8200010008030900c85111510403070526252000703121f00c4103068086406021080c80c0264500350088100160f0501c55402117100e440d0f54003140742488000803014003119018810340b800c11983c401484030129180c101000b45020201c1c001da803004c01003204244c0007001800700503a00206074041c01c0c501c030f283c421840742d04003175203044c103109079800d485d800140f0303490002c10000350002c405409200c0c0301d030200d0f109004500c00e440d0100705660400c00c495218042207035501d03d940c809102120401030210380300c000da810240303003910281a04149141c440e5002e00074408004490030080c00b480c41c0201d09460181402515401000c40c003e02c00c24000079000940da40400c411000c100501c1c0a0f41c0e2401040c440c1000209402c41001014000c0b15030340045407440454020650070740000001e61861003200d00200401050b050000e19404810b200c4010070803038405095603c010714000180c500f0 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 399883893 1250 399882643 399882667
    0xb0306010924210e2803080f060a0f090518030711060d0b040c0201090b010603140f0a15030c0e01090b010c060c031805100605060705030a0f03020403060e03 69
    0x51a04051014034100449010842151440e11080d004602c0d12900c840d60300b002d00307110000f1000d0407020300c600b05a520045004041807200d0114081e10181c400072007080303c1e103503882110304030103070100703180400050180c2a9030f081a50704c00310041807030300c6654a6007501001e410740e68100c1185030f50741d10100304034412a890010305081d03404005506002242d581d401880400100d03d0703000b4080400c1c4510130071416081000c1140005000f03024118081c02c000307000340199402541c1c00c244078000000c61600074410951000414000c1d101c55070b542140790940c1d0170000e4622200180d42c2c00c8004400414080340c207001e14480e03620740c3c15051130805454243c20040e000354142e03519143d40800d1a0784c00c40e040701c1a203580308102041e4049000000e074001c081048100003000b0105840c10100701d00403a0780e01550305440380400032244c0b41d5050084500820100900310740c070801000d80380c280140200c910186449c0742c0035242607125518002520035400c40c002c411380c408901c003d4151 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 399885143 1250 399883893 399883907
    0x903050d0201050405030316030603120206060a0e13031125031505070503130515011202130b0904030c140a080c012405130623030607020606030607031a09010b030601 73
    0x80c28a200030700040c2016122591030b07100240c041072140f0011320700e039107040d8001d4100000440e0000b0780500c0320f02c003c070000381d140c1e001192543e00c11019401c1c00709005092107100c034003610141062400802496405a07031568149003100b00500c030301586c0040b0354441508204801c24001040c041080c84c5150481d10b252400402d903612506003c10007140c40e42c088241ca5100b41d841c40d06d801031044508080d420212401091280301c6021800400c44804c903a242c4c0304000e00c25a002e0f00884000e40d1620210f800390605968000200004200868883c8000c034250078094083c0c41e40c05440700004600d031810048086500c004045405085c0b50000e01c94114009d06a60628543d0400d00e90081c0c002c52050084510603e0311595003084000154442400350400b07035141e80404280010800030840c0c1c01c59058803901c2180c0001d0506840440c0d43d6014080c064014480380e100c03c2c0042d8080c00d1403150b10001404040009006540c45000c0fa41c000c02071710320319a942e8240074000400d0f032 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 399886393 1250 399885143 399885163
    0x10602060709030b16030207152304030e06070222020316050903120c0f01020a02010504060f090308010506180402031915270b04021602240f03062e090509060d02010f02100606090305 80
    0xd405200410000c40c5cdc1140c070340b401c1200e00725206644c8031202e200007400d075086a51235070134171030280088403141c0040758001c40c01504107125a5440c00003070f140490f5248100310107140c05400040c6180700000c6010301074018030000d030003035604016811561508980004094500503911101800184603807480f0303414040d201d4139000d00c055441501d01400b00780041c454540a9030b030008000d04001410701c40e801e00f00000800640d41e17030419003851b407103c05000b4465202107203000480c00519614a075100c04403010782d001c0203c090900308854106100760344105214503101c048a4004e65240d20080580400c001003112a2503180d0052052485051120321080210a4141529460f10000f5100c01c0d0401c503501d01e589a0318040820000022039034841c1245100e41d9581c405842c00c0a000e101900003503482035045a03446040100c448416500d15401c56250307020100954410158012004650b0040301c0280c85010300b62000c89180364048000180a01c1040c030400c201808150b0306 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 399887643 1250 399886393 399886451
    0x60c060a0209090c09010c14010b030115030209010f050a060e030307080a030207050106050a18051807030320030f04030201051806040801020a0806030a1208100b04060305010602060709030b1603020715 88
    0x80031001780019140818210300504442c1c08020b0842d400c0409400403c4000c002400a200605030310500010000160104901c0342c5a142d00202d0003c0b04290340c1405c580c0000e007050f1f810792400600b03844101c000042c051b054082001903001003981d0384020300060703145540042e40d0709510304002d800c40e5640d0b00f0640c8118401c0070f0400613020103101562413010750000000b600d488010100315405002c2c3d00081e80740c041e9180000505401070138451803032038201d61200f4481c50581000c0e880c0d21800d10003079101d800501050015500c40c00241000ca0340c041c254a840141d0700c000100300740c2107076020400b10fa400241c1418080d601c0380c401d642000342a03008044400260703a0300d003e181d2030040000204944800000c0f10300c021000305000400050b195195525151380005018000034000c0f40090302c15174012501340f40c452043d940c200c9030000b42068058681443d062444400906c0c603008158080c0321a0703010948038002e00d18520b030784e4100042c41e2030107150701c102d1541680040c092 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 399888893 1250 399887643 399887647
    0xe030703030f1b020301062d05030a030305070e12030919050d080f16050a0c0b03070914010e0a17011d060402040f020c0a0b01080f032106060c060a0209090c 69
    0x26080791610342403000d0307802e040400d048206240003e50644a0000e0350560921400041103c0c0050b00301300b0703d00750f82e4040148030700176407e1442c0c1c9000764440c0907096440000004003280c882d82c040345d00038075503141c0b110a0941c01d000080043c00e5000d100b200300d8000103032007201450410000700c943c440b000182d405607407074030300019201da006800151031031070000303100c180000d040d4040310a01200c50300402c2c4100b8090400550750303071408408071580380c040000400d400c42d03c1c1c0d06880c481e51032543d0b00186903051a05080c00c2b40c034035006103414005940c540400307503586c004288000d400d0b481d500360920b80413050b8050030340d80114144a030782910450452900e801c0444c8240e801070301a1000b044075034085220750024421aa12410305000c8c0c6038406082081040306d041c100e038403441c201c9041e840540030340d0741c50f40704503a1000c0b00140e0104e480d10300880491001c50303124500130002c40c00c1804004005090a100711040d005060b03002a0008251a1100005400402d000c460074 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 399890143 1250 399888893 399888899
    0x3060409051e0d03290a030b07090305010c17040609112e1b0b10050a0e060406080f030d2028090e0a02030a1d0708060603030a0e150705120a0e0307 65
    0x30304641646114083c4105c9550811102e41c1310721261000a50b4000c0b2850600d2502d00c2e001060180c030750004444650803d0040c468091007200140c0071551040c01d0030f04244c81d07503135520f8010140d043c0100e030b41d103249540181003641e0744000b10a20700c44c1c060700c0205440810011b0b1603d9001c2003103000902110600c41c4000c21100100206030302d80c019036186850b01c6980785581d10680340d030f1146510502d2060045895054103041034081c00e41038805010303040c0c440d00c8654640783d2021083c0320903881403060341940c07802c54201d00004009501c2e440807800c0c85800c0d0000d154007100c4001c1141d00140d0341000c07003100106505078006003915024501030300f4490144c59148004c0c00a0304150b8000c004921082800c0e4495030b00c001d0302802030700480e554030074015201e00c140d201e2007581c2d029110019426040200480c0c84d1185103a03034180510140c001004260715030491041c5000d402071004000142d4100007401030b645408060a880d02c020603c0141a0007040c21424040e4010703090030 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 399891393 1250 399890143 399890171
    0x80a0606050f0c010b100e01021506011e0c020907020604020108010e070c060f0e0703200411040603090807060f05040b0a1a01050d0f020f090108130807020603060409051e0d03 77
    0x142c0c484002d04401d440d6510010b4007110f02500c800400c86902030300c03250035030342c0c1e10390030441c0c20b00350716401c0c0c0139500c0002e0b03d01c814186007842261100c1c08140400d2017000442c243c00000c01940700303241459503607001c1a0300031408581c8111001380160780028103100c159078020298500420725440075641516040f400240071000d0140020809900da066500305265580c1202c0c2c40805106d045a1a440d642e05040c1e10740e402030a06010b142510584030340042c202405440b0b030440320f0803070051404d80383c03882c11401044428030540300440244820400142c5034041d40b01c0e40d8036031030408209402c00d418130b5008404080d1840703401a02c0e29801c012401d0348100311440c10102400c0c000e8960f040c19401c84064000c07003120140c59072001850102818042d400741c451283d00b80e07161103059036000c0100441000800020f0005101440b0304030061072320380300541d8022400380c4040f5584425640385403400458116100850419101d0394400350000c20800c0103459035403034144901d1240c03200b4 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 399892643 1250 399891393 399891397
    0x1060203070b13140a06060504020403030e0f0f060313110f1309030e03010903080f01090207021f0c020a080d0f020d170402060c0607020f0d1e1b120f080a060605 71
    0x80108690444000180c0340300c04000036150f202d4001c40d080350380c0c2611480554075540100c1c0101e031303034034a02180428113050a00c00e42e42500c0d0325440d400f40721089541040400e0404040e2154400101d40c01d13032020341c40303040186025103040c44010004415501d0848641d9601041141c0582c2c6038040d6044107540307446060000c828280400900280b683c102110070300d0f15500d0711030b010b600b040b80003c01c040d80310740540e1240d00104900c451691300e40071040d09034428000d0107035100c40c100c5500640304584420590031403c180c242a540040582c0c04a14101c049600c0003407103800440903050b0360342d04010002803410b00c0b8406040742c40c2107020042c0044041411000c04d8030203a00000e01191690011600e44416030012030360030b40f809041c0290345500782d945002c0140070318076005c0300050141c1c1c80c554859052072003a482840080d2411580904d0304d1820703220300d036902640075020400e0761001c4404100b1540d04c000c8045d00b880742c080c182440c003520f070705041e5240400401125070300c041 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 399893893 1250 399892643 399892657
    0x906151b0b0103080c1c020f06060d03020a0b07020307060603030c110a08120c0f010218031606020c0904030215090d030b0604140907050408121b06100b0a05160804050307050901060203 81
    0xc0e460b51116112445c0600c0d04168001700c02512071803613400b403141600000d528100314000c20441d0481d546010a020780c00003501c45c010003690041074440d000802613059981d10080720710413a81800380c15160f100940b004c0780c0c0706502050503600440240300c10300301c0c0030540c0070040d40c2c11900c841c9421407060f1340e07101c14601d101c2510804220845445418080551541500030080d901c030341f0514008540740788581c2210740320b481800400c04240407110031100444120b90003821503088048107001c541d0600074011011806408203d10281c1c0c0120f41a5000348421401020650321542018007200c01c03465002d0302c1044144000c100d0220380031004410460295905040c80e110020150364902581d00450303d14081c002e10903412510f103030060a07850541204035070128524030708054440030700b540c00d01481d00900ca8140b1113061303070200614080c50789241040ca040740404c01c0000c100040341c42194400c00000f81040b5511b802c008a01c090b01c0b080713840506d03135450040c000e0f44e6031090318 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 399895143 1250 399893893 399893903
    0x110904120f17040b070816053a06090513020901050d020103111603021501050f0d020307091d010f150608060f09010306050610030509150c040906151b0b0103 69
    0x18885164416290369101124504910394642010300d488034040b00700b2601742001404080010300320040c8044104074184030350310703842c0c90031200c000010091402d10102401d2408142c00307003023410100e13500303001851420010020700c050030101c006041c0c40000d0508600507489540ba05d01590b03410b615141180c4044400d840d4200c0c05200503000f601492008000301d98010074081083c8088000c07203070956101e54240d4402c46540000108007000c20f0051940080c0346200c40072a23400d1400211540f28001000c0300d00c0c00744da400030541521503080c03e104002880180c40c120308002402511000c14082c40180045401c0c001d080310310bc001172069008128a01001c500d40d5213483c0620202c00c00003801e155907a6840b4107142d40078000584546000f500e001440a03d03075031180c801c460003070101102030710700707044410a042186a8060b00030240010300b00800520a0350501c210001403901c1e001410100401c83d102602b01c94509140781c5e9810910421100091075504020341541d41c00 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 399896393 1250 399895143 399895157
    0x2031f05010203042d060203040801050f0c0306090a09061a091605030705070f0b0c0304140a150f020c01050f0f070305060d0f1b1e2c06120607030911090412 69
    0x600725020100700c01c02000d00706526801c05c00300e0003d0303012008100b6601007000030f204d584c452140c0e1f103003045d004907100345883c4000c4c030100f5200d01c1c0000c50781d078111003010342c0032661818070b8440300d00300c8103100c0301d80900c2941d418111a141c18415a03070b582c415104510010100000b20015140f848010044000c000000801d0000c106040f08035141d40b941001d8030240b075180524800b05107500a55041e00c0c3c1c0d1f18001c011000c41400010041c5101e03901240840203d098000080060a0344014108041e5028084a040c0300024440c01d031240c40000e4070102a4180701c480d04450810103002c030010181001c00b0041c7c55258914841c481c0c03a845209922140c6081c00e001c45509007603542805d000446640c0042e0000700c003a8200d0700d160350010500b511541e1040100500800302c0c000b1006a00c02001502045960540542e4400005012003600d50480340204d4208101120b841c03000c665115184410300c800022200703c01c0c00242c0301540c050900e074544c0c00f000803030704400307a0802c094 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 399897643 1250 399896393 399896429
    0x32709011205150f070e040b01020c090601120e06010e1015050703050c030307020f100209090103060f020c03040608070f0c352808100e060105190302031f0501020304 73
    0x20081042411440c3d81c0c000540d050000d03800045032001d03600400051348000c4604001e02e894032450074514070580062228041c014144901d42000502e000e043c000342c0c8500304c98890700c0d40241a0f1003d0030349c010b4000340d818400d059105500190180e035400e40ea07032805111800b801a00420b03040824200309450f04e00b14a03003200c0318071410001c0f104a003c04000c0c481c03c80e40000e202c0804400300301c25100802005107540c012405001710f4250b0141020b8010400701d4070719840b00b07562110740d01b0058505074000344103d285038020b0b8480000036001c0020002007a51164003400440c15034540300c124908143c8890303903031841445034030301510502c900d086181c0c0c0c04100d11800754151000c1c41900c40e50940c0914103d505000014080c0c403110520100c2194840c80c40b01d482075001040c10a0340504004400305000001004203061100c100848943c040e1911105001d030623546e9000742c5c6d2854110042211440390b0a140f840380401d668041c010750303030040b0070380c4d05440c000d11703841d0700c0185 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 399898893 1250 399897643 399897653
    0x9010902060a020c0109060201150b16050304260105010b0a03051509160206092d030705010609020d0b0f0f010e030712030801080d02030a020705040513140327090112 73
    0x84408001d51186000940582c500c1d0085564051404240c80740b001c0c46a64180580c04d13181400120055910104010302c41009641d01501180a0a5102106000c0700742c0c0e666156070f2041d003010142c44400c4030201564500006841d40429404000b400b05502d8603090300d40b207008505500c0241030300c230030010b2820220303403001c03046580c1700401c00c000c141000d046031850340d00038a00400040c040c3c1800103510180000710f110000103400c82004055648001d48100080409128607090200700040004660309024240103003207040001a5645c00340c10f000d0080f5178861b00348034041c147d080c85100300d95407204040900203900303081a143c0b01da00b00380001e0801d00d058201000c100030b0742607079009040d8804c0345c140c140c49200e000c54030304100704841a6035a004078903944d40140e10621080c070003030030300b07811594028495103c2078109480031340d034050703042080a070b81c40e10543c0041405015106c07c1020b0600d502001a40881c8444050005c10010041401110f560004426a51042003 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 399900143 1250 399898893 399898901
    0x30c0a02150706090b010602190b0f100e01180b010201090209180106090e030a030b010206040c03081305031c080c04061b050a1202010c02010b0f060706050c090a14210304030602030901 81
    0x155103c0e81c10042580a481c01101e070140a0080000510404100c5414034a241d800c4564140e008044141c0c90b60700d0030340ca100541da004003040c10302000d08000040c01480450058041c0c01701c44d8900100d84c070b0103222482204d1100040e181107a052140350070142e10781d6108150440e2081000c2c611401d9158521805062142d00004080d440e11030304419048020020741001c002079030f400d20441c407400d0012a5030311019600034010308141e5400b007000840c80740c0142402da140340708450800355a580000c2c180280e2918002c017030041000c0c9441030340e5001c2103281d4040210018141002d0805000410186911021111500600c00c50600b40300302044102c0403954082d00407aa220402c10000740a040f403d14107001560130180e42c090b070341c585402007110400e005001d1b40e00304200c80d06c0300b8028103000741501d0044002000907032890784510924101822102e20440c200350005030600c00904103183c5840780400c41502c041818000c0801101d007242c0e003141003d0384a46038400654014 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 399901393 1250 399900143 399900157
    0x2705191409042406050f0f0102030301092304030e0102011104080307060b190b19020105010e07030b01090e07050c150106170903040e04240c1e170c120108030c0a0215 73
    0x496000d0b03040034502c01c0c0031381001017550b4054820f00030f034448a8050140141405204a000da0410700041c84014225031000200303080340c00b40440c950384c1e0403214030b1058109450a8000a0181c24168076650702401000c2450209001542c074003403501c440c4d59144e0040000045c01d264540c204050a6134a003035840305501620f103442d55620f59940c5034007010f0361100002800341c031403601d401c1041600602c1000d04a55140c8121009540c42000450081c1140f80007103050046140c00400c50341c0a1b02c119600c40e020319244d25070340e003504100981c9070010780d50402200704013100c0140140c0344d00c210307015030010407881040000e03102c43d82014110300594200082e0031003601d0412003406002400c502e61150203402d40d218181c503c03038890068540600b44c010106001000080c4034440854030a03450b00503134a000c88071030013a044402c0201c8402c1c1d40c6896030280c00310703007100c02044840741c0f035006240200c0210314042107501d013180c03034444040c40a8466141001c0d05c03002e0b5100701d0101c0c1d0700 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 399902643 1250 399901393 399901433
    0x140f01060e0303041a0901171303030203091603060f0b04090c0e1915030b070c03091a12090a1109092d1608120909010b0307270519140904 61
    0x3911322212106442904011951b40c0010f18807030001c04079564141141380908540e0180c0b101e044903584040c1c01039440900f00c401c1e00e110304000110050300b018102005107101d01404100404081138410036a90070721841351003a40391141c030b04006810065210f0899582018103401c030303500c1d45900a90a580411100c0c519030810180103000030502c0680802d0b03e00c6140b00843c1600c1d801030880b4505140c010050110740006030901c10945030310b992400d13000f521004030b450440c0c81a91034001083c2940c82420a82c00f0100d00c9081010301040c42500329000c0e2640202c52070705111441c0d807600b0008080e40740e440441600c80241c403e00d106498a207443d6400c413000002560401000303407101c1d1051046a004d811034546d190010041192000180202185c1459003000e040c000d40e030348050300403018400a1407040104051803143c003003941d01c1d01c2c0a802c42d0680b500090185a00c0307000c50121004042c07000600c5414030610309101e62a405440100d00b40c2d030340349045e00c1d8030503203030148c0f1706 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 399903893 1250 399902643 399902669
    0x70e01080a06050a060503030d0f020d1113080d21060b040605070b07140a03020306031905031e030f0112050a15150f030308040b040303020405060d020c01140f01060e030304 76
    0x10090300018644580030300c5400104034558681c51240100c80e0305000c1c1d40c1d8950420060300420f0504c90b0000c0c06031920851005103071081606009080b00d450304804e03865290007280c251703001003c080c10040100701d500060b0803940c0107403500800521200122121450108035030b000c0d00c40d1036501c40030107007004810131991355403590707000717800c40d0032185d4220f4440f5003000005400c1e5110b5410602d00c2c07110b04540c141404042d5a00b903000c0d400c000c0c11a42c00d841035079000021069070051200c80350740650091603a440282101d0013071018081c40045250100704103001d5004d4261041e00e0456101d00c482d00301c07030b140600d0301d9806d0041c0e03018080c16410103e103860301d40400e10380c409040c4088900e41241003554881c4581c0c5840030620015000c0352030400007a01044030b414049078054403d03e00140740c180c07202c5c0012616000602c4500341c5e0365001c610718815003000d03c2144800c0e1601080a205850080030119039010b0502546c0104002d00440c0f0382d081d2010001d540123040782c140450 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 399905143 1250 399903893 399903899
    0x6060503090c0d03140f090a0303091805070c0f02180403031b0e031209030304240905120706030b04020f0429070302030405040c0e13050f01090b0f0909070e01 70
    0x1012600306503803050441c010b44900044a103000780c0300102c0316505499640040c48075061000b03054000050144103030703c0410034030340140e5a20480002a610a03200c0401090274801401c505158107090b06034114904001e008a0641020004071682c0d07110414603a200210720104909422401200740140d09034000c1c0010580c1540224042804001071007070745610544040b200d0231b002e5201c40b0340540094943c03000e400080d03c000c08100c1e07000740482c1c0c80c0c02c3d0317148049040b0b644400e03001c458180084a8040355154050030120042000302d131150000c020740384089844400c248100d009040d501d5030021220740710390b015a003604880e14030007a16903580d803590020000c5100b01340618011102000100d180034002074421085d051f030700440c182418030b01404010211400c03950244018407100300201d81c1d416080804084e41c100e008190360400c081146071030300c1d06802141c0050705012401003aa01c50340d880080601041f0380761940c039210640041d080c504e180c1c11006c100e4031108008 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 399906393 1250 399905143 399905147
    0x3060203040b060f04061d040c0833010b12091f0504060b0607030203070b0606090409080c010e03041404241214030a0c0807060e1e010f06050a0b1605010606 69
    0xd10f00c1403009075402d030120721003182008101c42071406000810500d442c00011240c030541c051651007445048986691900c80380002c1c0792040000002071070800d00c604103d0001c1d11901d0b41c00928a2024151240c1c0d414a204e0404500940c2d42d0081d8060064001901e150004c100004049003100c4010744003a4491515202502003250295103150a092804001c1d040071405c458840740c165001d14144442c0d59941c095152018140e903070302400074010300540307582c1d42c429004618031030703256156034003041040b0302d003076820345801042d0b603400070720080000c0040480306481c81901100d00003411b4010851081070070900c2c2d850404035110081c3c000c42c0b81c000c154030000045004502541012046000d10780e524400c40a00344000b520205240340000c816502601906110700070214881d42d510990b685000b280c1401c204072181503200310142c1c0b410a100c0c03491018420001400854284000f0814030541480f07032002e203c0000400c0c0802480c003803620f00300300380e100c1c00905c486c40c0e40e2400 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 399907643 1250 399906393 399906413
    0xb0106032309240106050702120f15160f080a15030c09150f05061b01020702041401140901030803180304031703010302011103180f030f2b020f0c0f01090306020304 72
    0x801070080a60070560003c0710264080316040300c2080d514940b5010150307091014035260410800c2c07080c4103030510b0410f0500705000c4090180340700000043d0a15201c0309600307682c1484035000e4284040d0106081c0015409801d490b80060001004206006048001d0090041561000d041c51140420100d04111039401c6a10944141c0d103c0b10b01c5143c4488000300540325620505038003010801540086ca90403005808105004030001400e0001540100742a01c88207049540040c1c540d40052103141441d101600350341000b03031183c031155810b41d6a04600c511020744241101c00f0761840c101c82d00d250410848025591000e20760000418500043c20f145e00280800c80c0410036030828085501e0300042503480b41703030b82c41d80c2513608141d03094180909407450070550358050040c02c2c4813640484081002403c10648000e0000b001100b45650034160410a25510115000415810808a40003e92001411048030301c0300054035480c00696802c0c82c580c0c8021f11190022003003109110a10b40c1c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 399908893 1250 399907643 399907663
    0x6030a140601330c020f0d11010305010603020a020604110f030f06090c040209062d07030c02030f0c030703121e021609110409020d021e070c0f030b0106032309 70
    0x129450000702c4208024006100c1c0400020181407104544010745100c0d00704c2d001c40f540090448180c807244400820034103c1080c406031150701880000703105a59151246600520a52504605203c8413460083d2a49000b0303001030f0100c84c0550f548510ba0390383ea8a286a151402012200c090180e407110a888103011903012615009042c61178a60341040d000b00c03204504020b0000303140000104030681d03e50942e40b05020402c14080d2030034891420a0010003505009072070368240e260591040600e09041c4a50808803600000e0301381120340c4002810300c00703a942c0900c040955811031201105c0c0c0052002404035a200003520646505da00880c84010780000391103107185841d00d071030040742501c17070940d100e0b00b020388100f104200208813036020746450540c00030090b1030801d2107a01501e183e03951014189080600007446002c203c1c4860b00d11000b820f01c203140040031895502e030a20039a07414800d00c018103454443c0509070300c0c210f0900301c0d1007020640301e00d012400e000b111907a803820415 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 399910143 1250 399908893 399908909
    0xe0f0105010b04050a060f020c040e0f10060b0304151506090303081008073b060a14010c0308041a18070605030606070314040906031b060c11040506030a140601 70
    0xa000418200c0b0a6800c0702d054074409884803003883d10b00a8122020484020303014114050301c90086981d60355030080d203105040480041000c0100240381d00d0401c590f540c090b90342e0f9490810108080c00c2d0a43c140e80c2e005800c8115548000800a045000303415a02020701e02d4244210b0003081d095044442541601e0080ea120400c0d0b40d100e1091401100747d5020310703401607000780410881c1103450901186101a070710306130340c129000b4500c1c21503004c038000c2c41015842c400c00d080141c03508107204990300402c80070710f11040c6515007200103000070100c540c010b020484114000b4042c00091140d40080703141d40c04482e440391400c4811002c00300925516084603008103900014058031034825207020f004004c0046161080301e45d819a008000d0b12121034980400381310025903a070707607449140c0081d070150030303003018810400300a02001801b64024500b03000710720b1b0320320021640e503403591607050000b600c0000d040d82b40c1000003031078944040c03001840ea8030741800d201841407000c20140e040361284 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 399911393 1250 399910143 399910151
    0x30a02180906030a020405090307060207050102041e06171305031602040e0c031213150503010513021207031113081b010908030d020a090918020a0e070923040e0f01 72
    0x100040c45000369011540759100000304009846d05a0017a0b401c008280b0849180250715907484c0b0036a00035903400d5a076658042030801500c1e0900c142c00440f40f5040c0c20100305581404806044061400003603804035081ea4002403c01c0030390780d10b0048a64000c0100c070384801c030384030700404116003d200490040d130801104c03100b80c0a00042d048440036004020b001403182030100d1407000d8104590032092260068000101001c10050850280702d142ea56240d40f58140000d00c071100e03208800c00c2014034030402001e00701c0d6581003466078000c0340501c2c000c2a0480c08034610b040b240101c011f00b00f2003001c1c909000078172000000d200041c200341c1c40708030074200700d00034011343d115009841000706581040010701021101d503801005201c02a041a0259548901440085510080408503848445810780301035107401200540180903004c0c00d0b469525100200a0084409105e01c070b0700c907810307110701251102c1000c112459282d0b019104102181552050310396030384004295800951034 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 399912643 1250 399911393 399911437
    0x2709070506090d030c020d02100f080f04080a18150201060f090203071e090806070c051b0a05010e0d02090c12070201090b07110f060f070210090c0902130b030a02 71
    0x2000d000c2c2d64050708000d0900c000f0030803a03141543e020103c00c030201d0b8401c0c003010382072006a503030111005002ea6640e6826403494441c3d071000d00841c001a2016644d95032a00400001410403030844003102250300c1c1201000075409003000300c1c2d007401e03001000084aa6030303901458542c158414030131614a4071049804950700c400d80e0040784019a12400021101c0705240070a8803960445031580440b031a0007002c241e91110724a06004003501c2c180000ba80150b168800d200041080c020302401d01c030104540106035500045400c5240d10589040c010300c0e00c08a900740d40c4503441031288030b8010304001107619008240415692004100d20a041c500d80041054107105100e80b12036070b40c0c004240c0b4490340740e40c80d0035100c8240d03400712801d15200c3c6001e803c0c41c400382840081d029600c02d02c40400c2604203a000607007040384140410308503500c1c003400032002c0344425000208803020745c0801a42c4600c0c800f45e01e840c1c01059000031036054400414082c03e441a40d004080c200301c8154244100d8003 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 399913893 1250 399912643 399912649
    0x1030c03020f0706110d020309011437060806090a0317090309040504020a05030a0f020103390215070e0307141806130c1d0f03070e0627090705 63
    0x1a01c582882201c00c1840840f00156a0b6807181995080c1c014007a410080d403100702900740d07801250741e00da550f51501c58091040000011483e040842c60804400d030405078041c036860410b901801c031030241d413582e44107591100c503684050b005e4440d02c0b041e00d0303807898006e00085d52110003490480018086120f029000904888154041c001217000b440c070f060b12030400c100c05400060801d0340d028586003400201603404000074068284160504c882001080c0005011a40d02d58281031000201e0179090000100d00c5020100c104000701080c09400c294550882c507150305648010040e080e10418040c60542040c903803000a1011400c413007030140c0b80c141c1558481003641c14503402031142e04002c016440c66140159200101034501120705200c0040102581c0d5285d44410108250780c00742e40390170300001c9040303000071403d8401081102400d400b00b41d0724905482a606111a800c010511644e1002e40000b0354400002ca44102d585e40c024100e403100c00281c5403c04288076521001800341 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 399915143 1250 399913893 399913897
    0x3615020d050409050603100501080a02150901050f0c031909170102040b0403030f020a050102041d1008030906070303140421020d020c01050708090d0b1009020f0a030c0e030708060601030c0302 84
    0x5901c0c0d8800b802d1901e401c207090090f140c09400c165142c011242074000c00c84039442550300a113941c2000342118811401400340c400340038207010708801c408100c101c0781c40e43c02404841c01824106030390703507807807003a081804d00b5030040528500c88020b10341010708803140c1c0910610203540000c036124550070b908cc1e45042c201d00c500c1c0300352075082200740000c0010a01404071402c0c1814103005071020300c03040b60345580c220391050700300f24200c40706200f000c04060b1140407021b5008440000030303a1500e081540d42581e034018442c200b8400c01001540c00c08061094000c40b14003560001001003a003414900500d0007103807030203150828a100400e03040064400911141490295009407a08072960001100d41c1e600c0300c901074980d080204214403441d110b10038980a00e5015034503d0446051050403c2d00c40d030042e900c80340342a07005111040d400b6107424112112040581030000b04504806c81c280c43c0000c0e01e0483d9a0b050080c8040010301d04070115440d4490b000c260b0342005a84000d0005808074 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 399916393 1250 399915143 399915163
    0x1002030403200c0d05010e01050a0c0201060b07020a031e0b01060503071e0f030e031b0709230105060a0909140906070207060c060f0213090614010519361502 69
    0xb90740303c45103603521070421003440e88510b0b020301c0c004111f02101100071800d42c0c030280c0e80e130000c8a546406007101e030303a82841490040d01e0079001c1c642c0740c050160000360701c0d10351600000c0e041140f4000c030319214443c0c3c0c1040c1003174a540842005442e43c0c0d00c80c0090142d4000301d9074400864000040e1100b200400660707014210a42e440d0580240d0504800710014034410a840415101c100900e04088150100c3c21302c92801c1200100340c0c45041080c04000c0c0c1d000049018143c0e140d84002640b034900c00c0350b9080c1540c4c020340b40ca0741c6840c61014100c0340e51129500101180c0d1401850405010008841071f03c6400103404a80710b584501c0c0d4200d9407001e00f441001d00081c0361200d1480000d10320707003180700181e4610074094102200302c0d060800460b41c581c003101c00070382e03103035401c1060320388406040111017001d0a00f1410300417004510716101c16081d5a07102007110b803000391204d400d841e400c0082e0341ca022040515142e418003aa034002a140c40c01400682ca8074854000d0101e80b0000300d007482 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 399917643 1250 399916393 399916457
    0x2e0303080414010f060323030301060801060309060902060a080405010b06031302010c21020304030c0905040206070803040c0f180501090c2a0210080115020f060c0f0c1002030403 78
    0x21a607281e440703580c031500601249038034a5489900307001c80c040b464010b00018600541c0c5049513084441d040103905143d0801088054005200402840c0c0d0403042c024111890f134100440c10310040e1a2050060040e800b000b90b1149002c5000204036511000301c42c0701e148074a001f0041048914108003540c0403c4a10500e410120a00400107503c550b25206005207c0e2034012080301c400425604840d0300385c120f404c0181c1c000306041080c070602c1d0079003000400c0d58840030441e5061580208080e40300d50000038003c00400008201007002c01d1040c1c100501416103c0034802d0b80304c013088140c07040741c2848030394002d040500228400c40e03a403107803003074144003138440c05c00b4110081e840c2c242c641442c0410b2210203400c51001e0001d40c44089508c0401d10304d90340e41c220150f042c00c40078110205080b0911007154468140440314050016940b5008a604244941c0b120800c801311549886a4108020f00740515048036161050607000307180901e229445602e42c5041c4490030040f4165a03a10001d0 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 399918893 1250 399917643 399917657
    0xa020d2009011101020c0f06041509020307030803091e03130501092607090f0b09010803120103110f04090f0506010b071a2707060f180b0c030c062e0303 67
    0x11903001e0303070100a240c0e20203c00903041012100c2840d0404c52020203400994020134101301c00c21059514028a031506000104605000c0d90046172f5070f11711902000340301d0040000421112882040000b82c0e401030015100150050341e00c14680302c1d042001315045104002c130f40418503600078014203003580e042c1d481110000c072081c25802846802c8000b004143c0c011068046504400c3d40500c0b11041030075100440c80440c08810f001194005074040c0c00d868005110b400c0040000d8040d207411682c04c6983c00c10200034240c0060324070304da4200040d5005142044d100104050220b1840c00280540b0039580a41c0e6280000c076010b1140103c0148000885041766484ca80744c600c500d0f41083e55000851100c0454510b042d402e40c484544600695020180811846912980380c030091f0280e845c241c5004030016595211044190141115030140411b4810754040100251641b01c14418120396407810841901c0505501100b1084868103c401c030703c1c00003e50001114085a5055551074 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 399920143 1250 399918893 399918907
    0x6150a170a0204020a0c050601140a0e04030203121b04030606211e050102210405010501080c060a030504020d1a1812030a09020d0c06110609010603050727050a020d20 73
    0x800203503c00c4d02c1704020b00c0440c00c00382c1e000c10301c2084900d0103000078519030300f04068008108003541c155540682160f1511008000000e540802500c48800040c0031030351081e2075920302070501c540140a86001140003007400000d02440390052012940ba9414042e0550025000c407041040c031a40003401c1d01c0000300030202c980c840c00c0365440c5002e005a00040c01c01000682d800c1c15400780b600d40400524030a014401802400e10500340100310000061800d844130f0b00100c2c0c194090400b07107a042c550b035140010295141c661540b044c0c0303580140703844040c8642d05010085444261400080701f072400e081c1e0024a00b00180c05812941d85000d094215610204102c000d00500041246c200d9081d8958070001026804102c0181480d0b4aa102c08131404d241e4243c6001001040711890344c0c109082000415401b040c502c082d10b817914100c0700420301d0125001d0040040c00d483d448101e241c4820000422140d0303024207584080b049007803112180b081120183c0c081411060550342038100880 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 399921393 1250 399920143 399920149
    0x6010e0d03121a0f040606080c0904110309030a0908030406023c0706350702120a08070801051801090b010c050f0106050f091003200306150a170a02 65
    0x4451038070a20303115014a800b5141401524a8014540f1410030310748030500051501102000c00711200351030030444149401c00080402d2000781c00b5204c8148001081022520340341c0110844000d20803090ba6203090000706550f41c1e9100e07003201c04c000741c1880300209070540080202c8040b281158024480202d00c1400c282d9003881c1c0c845074034080f4144484010a00001419800030705544401410f60703240303081005411022030140c00c0f260201010716001c038144424810311903410f828040e071101952425016841e16a2018607500e0010000c140b1411484d4030920071132080050f641c0704445c40c0d82c0e44c014040d90400e000303c011f180c1c8042e08018801e2620300d9001d030102c12014901040251b085845031070130b000403400c4916a59445903c20f00c003c3c2007007403250864081c1541d4407000f500d8a0011900c5112060000810100040300c1718900b038504d2090907410160000e064404600f0842861920714925800380c41c000c605001c800110901201851010364000c80f000e050030b410760380c0c20 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 399922643 1250 399921393 399921409
    0xf0d0503031909141b010c080708090103110403050115051008070f020c100519050c030406050901051902060f0f060f0121020a0c0507050a031a0a060806240906010e 72
    0x10081c00c1e640c3c8220000206441400f1007150341e603040e015120303040c1820b03140c00c00b802c00312140e2414440390b90500303c000380310072040f945000c0d081030540307444000e50001200640400d2603560b00300e10000c00d02205114043d0300c90698540d552030212a5550b42d04180040c40e99030b17919000126105d01c001403a01402140016501304440c410350f80c2e1603140c5c0001400720881071011030002100480c0224046160303032000d4580d0301c22418030904003c5003078001d5903244210f0241c0d1080120104e40d03606030307034085c0b0241d90103605175071134007489101c291000030369402040303a841d005240c110010640550109442d1406600080e2103144225400d2005503107414a41480c241e211034402804142d503100c80c40600181181c0c1d13552010032400904084e4940502d60b0010b130b128a4961703408200080c1e1324001c0d114035040380b41601840740d07a0100d541c1c3c0241620740c4070f0119400360208211f05407a03180c85940394520190039911003040c501c0288888164102d070f5083c0454440c11800c0314030700e080f0030 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 399923893 1250 399922643 399922681
    0x1030602130810060503070b07020a0b252103060b1602030c030304151413091109090c040504150f05010e12070b09040f02030f0414030702030a08090f0d050303 70
    0x152619541e1409090700e0315203c1103810840e550340e144244090700d424840c100c020a078243c012402d14a0a800081158000b885024008a000111242c158585540b02c0d4404c0300c815128250021080c10100c140440b0034848041c44550303151001e144501900c61179042d604860500390400820201c1813003809001641079074144a016428641560200014005049003100d00300c141407070305c0c4000d40f800007a6810000e034403400344252a91414520080002c80764401004105c01001e140307610702c0c40c0303d001e07803d6810210340350400050515641c010001c40d4401e80b0108146007220200458265440c0203c10b440030144004005540c4144546001e2110003000070070500980c40c1254517040a0ba8042d404403540030030000c9007854284501050310603c0b5205500e586002e0103108072400c0d0090004190401c2589141c12401080080c0d400d5030b0340c0982215800c41050400380415003200034100d00c584202c8001c02c1c00d03400d14146007400941e005000f5419034945006034000a0300410b = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 399925143 1250 399923893 399923917
    0xa030204030f260703020606091009020c0607020606062b180b0402010f090e13051e0601091512060e011107030302030405010b042f09100906080108010b010801030602 73
    0xc480400440c26400c4625620303482000d0803d50800b00040e40f180508080c0c03544040040c0c1801a040804d070003203451a84184100c03095101d96a038040c200f620404580c02c12030701c103031020442192000001901c01c0c0921410307002c948661f903810080019520559820b0300020f440702e1403415008010750308100a10500040200d200c4002c40c0848072030340c051400580b9188696000e110540d6080300c0340d1a1400602d04c0c00c0c00146061a10350444c503c0041c091410100c00d20894005000041c400c10312110714041600501f02141c05180790f95031401e020780c0e0703c0d96191941c0300d0055010516610100d600c104004007611400b034890308002d00c54211868119500d410400500707042417001444a54030a8500580f00d04003803d007182120541e01da1140203614202d0b4042c50307c1c280081150b03204c1080f441114150352004208000340c0911076403143c00008100011468540100c40b034415070b107081d42e07240c0203a030740d41e891182607500b16a90507001c01c8880c2c0c018004118660010f100c1100d540b = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 399926393 1250 399925143 399925147
    0x706021b0307051512060103060e06060315040c0e030f030403030e060c0114270a03050306060a09050901030f050615090a020f1c0524060316020a0f0312050601050703090b0a0302 78
    0xa00100348200f070f41342c10340e401d110f8000400e0f02c0f40c0141d119032540c02c90000e207000c106072070070011800750302c4001a006034810b0b2804400250021248071040710079070005401480006480c0001601ea14403000e1464482e0040b007290300103080c000010307101160b8141d540c2c11004c0c0c0f400802e00104c0d070300079009064907540310b840304c00610101e404014040c240d00e03210500c84420400d60001050b0f50f125403a011038010764440f10100b5844020b89800000460f00d07503075500c0700c4034403c5e5010681c5500490300300381448000070610005e030051210942c010010b884450f0f82d0590200303440e44455899560210301c140210b020340e100c1c0c0c1d0180125601100640d0714000409450703002008805110307045890b02c440c2004620b1100c21401d0507040d00d41b0010f030480d08240c00002d14917000080c28861362041e00200030300254402c00442d80f0051700181d4217109480c0d42d0070010810000d98050180c11424880425490f5103d1012244100d815568a00b407603800d100860b030455010b6441e4404154003 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 399927643 1250 399926393 399926399
    0xe0622080607210c08040b06190f03021206070804030c0606030506131209030807060902062106090f07020607030f200c070b04050d082a010c020c030706021b0307 71
    0x20000c442c0107060646907400c041c1050440b4800406001c800d22161908148841000075006400541c0141d84060031071110f54414011aa20301c2211240303d1880c490010002546030441044d141074a0091b12041c032000014051180c1d5001d09850b5480010070344000100800d00c40c0085100781c622a500100d20681d0320380b2842c2c85d04100790780034030800000030031090030031008400c203c007041042d0412803440c038034540b5492024040d412000d000aa100c900c024210765507074048071842c40980c65440d8001c880002018003444045a0303550007040144085648103161081c4103129991a034014101c0d542c03100e00440c09880c005035402c261a0702d40400c260802c1000b8241c0346034036203da40f035075141e42c00f010030a454010250b0141c04030799002c01081c810384d240d544444036401d42011886545841c080003048600301140c03e030010b91900c507120b00543c140c6c10f4004200d12482e55084582c000c80300000c264a0300d8051080d10003507413040d4210789042c00610f10903165208002d043e40c2c04196 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 399928893 1250 399927643 399927659
    0x1c0902040c020c01020d03200708090301090c2904060302210910060f0e040206070309120f022d10170106020102070506091204170a020414090c010e0622 67
    0x440e041450158001110b40c4030f055904104170300d90103802e40f405006d1094420810068445101c0910708541d00018030b080c10720100e442150716101028008000c80c3d200c1e801c0c00ba02ca102e9a00035015024886540e80950306802d0041030403550045084a1400d86040300035002903011051003000c500180711000c40030541c2d000c00e10f1161100101070440c1100e2001c0d01c4e022910560003065500000a006020034490580c880394455030580d9545d68502580c2400c0c0d030121103d83c001c1580030310415190007000703d14204009594804d50341c14120180500c1440040580e2044a60045001060364501445c264250040d112080c1c1410f6004441d503c0850030141800d030800c0000d40e400040340010000c0c20040f096003c12070308061300200c01d030b07082d19221900c1244203100d904005118104034800c81404000c2400741c0c000c00403c00302c010411180000070301159101102d00a24a00440784d5000d1085543e58680c000c02031858010703180d21440b00c9080c603d210700713502e00c10420085810b403 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 399930143 1250 399928893 399928901
    0x70b030c0a26060f040203010807030209132f040506030a081e2205031f020a1413050f15040b13030b040602071b0e04120311040e06040c050f1c090204 66
    0x80390440b1032205251920612002d0341c11442601d020b00c0c810401045003040210300c02058a50440e5000100e0710756050342d1108541c004000382042c040c02c00c45081d07000358040302c000d0b00309450345000341000c401c008100490b80100c5006816030452450800020032060003020b07180c28215213211112a0803111074002d401070301907511a0f0308041c401c030355401c0a0004c200020001100102800da01c6420300301070a07444100341030341143d004070b6028080c40c0200d0035609840d0040d041c581d224a180808000308458034414280900303511800070501e402c18a0088941c64103100c02103160a00c2c01c00310f1030856015030595240c0074203412002c400554044d5005003e50702030300015031203c4035070402401c6051401e03079880920151240c100f004440d0b14079048c0d4002e4000640f100d80410301d400980c09401da0366040c0e00c99000004020922900b0718a040f802008182e80030041c6500a65054880780700394800c07080182d0092003905a46165400180c1205c07144810200305240ca9501003011f82e = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 399931393 1250 399930143 399930197
    0x16080601020f1005060a1202061602061b1006060305012913060903060509011b0c0303060312090617040203121804060f053f030f03070302030f09070b030c0a 69
    0x1a9413100148505851704810f828054035101c000301100011032303400512207100300b8100c0750000d10b0f088401010341d40e034502990b05030b8080c81c042d41d4001c02c15124440d1a04902c101804500d407800101059141c400d20070f442c10b07100340900740341ea11010700000740691039019042a10614040088044102c003d03481c4c1c3c1c0c000c1c0b80d00c2c0c8620a07824111324000701a1040182000303620313031401c6000e056220004013090745544260030035210200c4141001c40142c42150400340250001d2000010200e1784445444200c600c540e03100c03622840c9442501e00c3c0b08100755801796050344a19180018a00b0820003025801d040780600b40304603402c080840d0540761158420f00c040130901c0410044c40c20546034504a01d1010350410140c15051280d01c0300d080e0101284681c5680c2a0721003034100441002140c0c41c00000c808010303120b1401d540010081c1d402104c2168000c1d401e000810307169500019150180d078110601c0304d007145d484903041c02050b005008004100041486000c00c3d02964a501d000a = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 399932643 1250 399931393 399931423
    0x11b05071e060e0d0b180a05060a15030b010902281806020303040c090c1106180d0203032806050d050604030e1212090f180f0a020316080601020f 64
    0x656a04440e0344441c40c0156102c4024000c2158040c40300760790721072500c59400c2e03025010180a0701c0350310940c520f0f1404042d4525844c41104041030a101000500600c1070010003014441d0348021012007a0750384851000900c044100001400460010707000707468400315507843c40d140c404c803a80c0715083d907040c0e2401d14004070f600c0e404002a10180c40f02200027900a50004503d075041c20b550b44880b11803144100000517039542da00040c428841d0403c8025524507904490440c24440030340c01e0741e490450002c20355449010000007142d0b0020059038880c0c1071804c481800c4d0480c0d46103d258800e1020700554205598101c081001d580f03240180c050680550018081440c0c580741c007600e000002d0200f0780c4141a440e181103100740001681030507200540c081591903140a00100f10714481044505074010001e1942401000807002294420584516800156119014164101c0c40203445644030000402d26483e41c0314001d1004541001d810310458004810000c55541095070414100b09 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 399933893 1250 399932643 399932669
    0x1b0c070e150a0e0105010315060503070c0c0b0d06080105010812250c03060e0c060313020d0203010b0918120a0c060c20070602070f3002030a060e16080c011b0507 71
    0x2c0031b5649482405c0810034100280c048160030554003400301d01005084e0010011056000e60411402c1d2203500003c0c002c4a213000c0e03c07020409001c2000d00258090911a0340c41c0c44000940140c0010380d08002c0c2c0081e42d200c80c54061a0a03070712202442901d4400d80d1011000a150000380d500301c051402140208400208001c042047c5410700140103145445001c040c000d0110b000900c401c054403595046801d06140c121500c0403a004d019021442a0300000c0d030300801c021440306403408036170740b038001007603c0c40e10100c0358940e03500f4001c0e05076810000f1280b100220004000c1c2e171010698405900342a0500f00b0507002e020b085480300307034001d21301da008040100f00242d01049440064500303180401a41401c1c03108460280c0d44444807025003007090705c0e10760441c981c000e41e4840c0d03250b00601a0f95040e08282000300203054441d2040c2c880307108040d10444940981170340c072810b40e1044405400c0040c2d4000045030914110342d4180b15002851089000088042001c1401010072580c120 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 399935143 1250 399933893 399933899
    0x181802151e0a17060306071112070320011e0218102309090a0c1421060d12050309150f0609010f060f050a0302040e0a051b0c070e150a0e01 61
    0x30b010802074084651903890103c103004003954081007865011600d80380c0148008005254603203030104d441c20558850800040050a00d80e00000000b4040030480d89a0301c1e0305110360b110790880d05040700c1d14101c030032030000c00d082402980c0c00400307080007040030400180815030001a0040702030a020700c00300f810f4a01c1000c518048410106904011428403820110300750b0104144840c020400c0011950703911114480b14002c00d0f808a07070400d0300440741d48031101300c0840d000c418000c1c5150560032003442c0020350249041c1b0580c00045a1000306030480400c150320136501c980003d0040e08450195069101c00c0081e03559010f80320302120707100ea01050502d0028070800b0101a04101d0365220746110501c000c60f000f044a895207038140c51304642d1403c4044084009015540160000801c1702c0213115000d002c1d030308414020700c40d1035003200d803c160104005903144100d00c0742c2c20003038210b40010800e1406503011607038404003100b10b401e2048580300009134500c0c40d50700304c0100454248018 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 399936393 1250 399935143 399935147
    0x171603020a140a110c0d0201020a1b080a030203032719022209021216031106070f060507020d03151e03020301050403020f0c091b03130b010906181802151e0a 69
    0x151040031030943d10302c1b400380c0450300002c1d11001064009800342000c080144600101c1c4845600240b500d44151403401c2c410f450000d46a500c161905c800c00020b40c0e0501829044600301d5140c00000b040c010b01c0c001c22564000305090105140603a44100301301803030a0780000c0081e04400b0320741c04401c0003a041d095841049503121030300e03c07509113960101902e20381401e10750440c401038a07080f40c80d030f0326542048400904144204030000340a04551390300c2508211300c0350021809100680c0031b8400c05103000c0022402c4407403500507560301682c004810011403107200540c1e40c1c1c1e6010108242000c54803034000c41e00b035aa0079103046006a10110003000c0c402d000b0b1003404401002140d4501890405008540c0c0d0b220b0502000c3d254240e000012482a03460b0480184131594042c5800304070b90f0391016400020f00e00fa00c1281180500c1900d000780c2e480540c03007104000d18401c0e840440ca0384c1c068003880056100c482e16404046420400355200c8640f581e0200c0c115a02e05241aa98540041c00 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 399937643 1250 399936393 399936403
    0x907050d0b150301061e0e01030c12080d0212010611160b0a120905030418050c0901030c02030c0d0207261e03070602070803070e060705150705070b1006171603020a140a11 75
    0x41800001f01b500014400204541080000c55119030410455013004c0c0c1081109846910481c01440e4400204840c84610864940c2c0c101c56040e19400100c030300407542c0c1900c0d0940d03174a40d090410b004103030500041000d030020300310729803a034909009000340f003588030412111050400c0d545a440400c04103c09802c0748411094460501d40c00d00643c10444085007441c0180100103040c5030b02d0700c2104c06040d01c01c0050390210440141103801c00b40210001a40300d91003400f548044039a01a0007651000d040c040314150740d404600108110400354002202501d01100070b042640820001600410098005010380354011045140d481c2400789000d00582950083d041c0504c50a00c10003000c07030380c00b00e4000804400750000720955510f280045803244101b002c010000b170001e40c1808004210810340d1030580b9201d45500d10036603025821500100741c1150600d104500c9280074183c420b03c41d4001c0c111100c1ea50a0890742d421141e03403070101a41200d080e5400046104021801d00101081 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 399938893 1250 399937643 399937649
    0x60601120b1518030f07060302071113050f0106022a0a0503060a06140d050307060f020d0c0203040503060c03010e04030c02010212030a0926040608090a02030718050907050d0b150301061e 82
    0x140580c4514242e0135071200861307c00c030010b059000c1100c4050010030700e072103890700d00010141c00b01c00702d203101c02400074901030320400e00c4034011100101e48d10340000390029400050881030503000b5130464061008403008401e280d080b0040707c00005094400300312240c05a079035520080703034090030000811000400007000d01e20070070700c00700e040380400e8000c011650800e400040108203c034011382d404029205601d0351221840c43d0204984155601202a0095900450a4940b552500a140c1c66140020700a05000745c3c0250042400640a0414064258410300580b8100d016200008002e601300725a01c4065588919030042048400c429807001c004144005c605601042079180200d8040e034014101444040001703e860200200540c0105d980e0050450740d010b83c8074900d5483c4c42072201582d44030241008042804800c020803100d0546501801c00c20000349140c85001e0241405410503451228400b284000d0b51820300601018000d04012001061000c0c080a82e040380e071a8 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 399940143 1250 399938893 399938899
    0x40315020c1c08250503060d140309240a2001061502060a06141023130e0112081812070f08030301180e031210150e03060601120b1518 59
    0x1058038411508818804c40900c0580e2034683c0d103a9031042c011800301e440301c1c1001f4002201100f1040d500c0384001008000422040c0c450803903a00c02c0b1006000b07a0b8401c690340c4040000c06002030b08040c0e100e401c4540c244e02c4040c00c040022000314035030b07900311001a045806426104994000c038541c04020003500142042001c000342c600d0160718000004a1110540c03007106140f41d9480fa803849221400b4404c1e041c402c50f5205074a8040403854294030000001c49101008980000c4e008099048507040b00c140f00c0c08012545c205503102c10040e801860003800d070001290500c81d43d03440705140c03040740f0300034540103154241c2041c0019035502d61950000081754020030051085100c4940c0504044030000c5021488010994101c1d0a50041c0752058141c2c2c1b00000c1007141100030a40c00908039100141c44030142c0203007210481d000b002144180350158454008192603502c14072206c0c0120603141800208129480002414400d5890840003505c8000c144040007203c003051044502c9011 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 399941393 1250 399940143 399940171
    0x4090b030c0a0302100905030f1b060c0c1302070609030c140a0317060301110d0c030f0203070f0e0a090c050d0507110a0f050304050603040f2105040315020c1c08 71
    0x2160001d078102c041400000c0c055444a40060703406405042c010002e85801825558050000d90b130359a541c0020041c9509101c0709087c844041c3d040a82c2221341000015000d030100c008084280881e03880344928102009600300050400318045205251f000d038480d0b900c422061541e82841c0a41600304460251540c00c201441c000280c3c02c04400301b00107030108460010b030340e20700001a00602003107054103641c01c000160000c1241c96a8803044016940380c40400c04000e48144c04030490000300c2d50240880c10701d8000803071290061004070601c45000740741c5e21240340c564048209660700000410042074009c903500c00d42220303900403564131412a24101100c480d0048074980d8a010014001d00110300843c10748003808000d0045801400010781520354a081a00d0304096902101c18140d5151801e04030749150140800c0c1d06860b012a02d5854504240c1941c07904080e48041140e00440a135081200030341242d010700130204205109189402144103086c006402072000030130f60a00c0c8020 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 399942643 1250 399941393 399941413
    0x140606090f040b0301022206020106031509020406090f021e03070806010c080409090c0518010b0f090303040f03140d02010b0619110f06150603040c0504020a09030c0b04090b03 77
    0x1a00162021488116030303190a00400c0400300d0020043e030400caa41550000644915454000d12010680312142e0074008000e942c4072000c07801c07a455408005c24076180c8452010580400380c0141341c040f0300091000965590351513003501150420407221412a401068100311040c0301a4201c080b0a0310450043c614941481c005041da035008021906005070102040203000106040d900a0045654200301000741030030001c00d10f0085201e000e106000306825044030169400e01c49040716400601c03582003001110746000f460300140d9180f81c040c402444000340c0300442c128804021400b03000c610414002174003000382480d036a01c10705002d580c1407415071030668a84c07808584542c07907905c2901c00607100115044a6000803030034082401e20030300c602d20280d064040345080c001c0750380c440c00103001c10750a81840784600040704c000c0c2c003081e0000420411802c15400506120041c0d00d421291281c5a6a9040c06a2021f8001501d0900c01085c240107000b458881d400340e40c40200e00034000d07160 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 399943893 1250 399942643 399942649
    0x105120c06030c0a09080106030b06121507120e010f0b0f01051309050c0405040f0b0102160501080103321b01030203011410030f11090418050d05161707061406 70
    0x30015141d10140540013604007101c0c0e2080c0301e40c0001d05034807402406000d40d04d040c58003142c001910580e1007000f0307980c4441280c850000305003188980d50714815886954102041e01c6050000030002d00b00e50300c4445c2c6502e020400e1054108440044400040c0c2522501c01e1084244c00035070030b0b42c140030040182003e00c1880010600440340d01c41c0002c10155180c10004129028542c4500e07080ba08100d21111815119000a58004400e030b0845a400c1c9582c1c07000c00440045108070b038040350f80100140301049511030688010135111401b040d000e00c01c00088007990b102a00c4400c001d4000725401742d011403d03e40b080000c42000d01c3c3c1542503504040140d5500c21110200341d2060107201d41ca8130a030350084c0c00100c0c2403000641e08108440d500301c6103025a0307009520446c4640d00e4854424400b0300c103c40e807800a20340000040500180019040c1d40e1680f00f055007941c0c8200c80310b001c100082c1a0322800388400210080c6586036102460001c00340c0d40c5030210441d0003404c83c420099152 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 399945143 1250 399943893 399943897
    0x2031e09120d0519140a050603100c0f0806060a0e2b052125050109080d0902030f0a031e021c05041701110f1c050907080d0806010503010324050a050105120c06 70
    0x221100c032000403240c48d0000064549480307900d884200c50f09060404140541103a1100842c0100d900c41a0390b80d40c6110400c115849040d51040106007031164210301810010703101c182440a484c80d82459103641803002624810710f51080342c4c2c0d86d0040e5040020b455914040000c4840d2001c0030506000b00030b006442c5c209540004650031182140f82442800400d401184176582c000705d600b6510007461079180003410400c6807d90082c0304403080743c41c1ca17000c0014100e2030301d9090340d0354a41c800384110b0505040c211441c0c0c21000c500c101d501c801c0f2041031000030420140e1080d20703072503a11481e10107a001903030700f42c0405e000c031649030202001242248904803556481e80c41001907071440c90340e035401e201ca130360000b80e8201c240c074000801494040c0090060244c9254a085414000203000308a030300d0101161202c2c0010014001080000c00c0d11408400c102c03170030740403043c823080f500342c46070300721641110440840d40d1184010402810201d05100240c1d1420b03001e0602e005045010603014 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 399946393 1250 399945143 399945151
    0xc0504140103152c1e07080708030304050606062a030318011a01030e150108070914040c090f0216030c14070e0c0a05070203031303060c0302031e09120d051914 70
    0x14400c0802d070140b200e003405898002e4004a00380c00b4030701c1c05d890a1070740e10100313400381c040c15204130075011409a40010990388101c1c2d0020050036181e540030103010b055000000c3d901240100180c4600101c1801031030480b00100031801140c03a80313840d480e004074502d10b841d1440000c0e4508260000e41802414030284681d0003801c0104441d0104d01c1c10303d2502c0c03041c41c512800340e601c21001103094500414202c045070000d01080c41841742d410054044184d09683c01060030410402c00c100001d42c0341c10408449170782840050400c0d862100c41502d0f844003001c12000114841414002c00951449003904030b41c1e158018194941028a0000d8410015201d00c0711502d000c1907031125144500216034445601800385c9440301c2c51540341950030099030108840b454101008880824800e2090b28401c1c604402455106550700310300c141c81d8540940031084038010140c4010740c0e141140028180805a0b050000300c43c50041206000291900c140300e40303540c1040408000941030000072908 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 399947643 1250 399946393 399946451
    0x207080a0806030309042c010b0a150519030b091015030209040b1009030b010b0a1707122f1602120f151504060f120c050414010315 58
    0x25442d0711000901c0c5000c0d141038a41e105003810b00020310048100084282204686a0f040400ca000e0854500340e40042d0f0419802c218460300410600d11118560740030030342d0700e0800916220302c3c2c4810145c000b0110036070802003901c03200084104c0c20125400b9501030344d2854020f40c55070404030b04008180003d85403138105078000c21500d07903540d0ba03540000411800245400140961254050f01d5201288019190700082200000b00c0806010885000307141360390b40c04c40040c18401075202c0c4038001600e0321007003040d10800601120750510030030b82c035030303001c000d00b03128803a1f00c400a441c5001a8480c00b0b0046803040c4812036150304c20704000b840301e40d4102c0c2c1442e421a02c111032549026500c000c0940107114242555240c0c00604480c11301501120540001000074481808156040781c4200007800103d10000c104802a80b00c4445125124801d58100d40f80d071280080c05540e21101c2c000400d181d03410040040028090321003403541141001031000d16128002030b440102e0300c0c03160b451 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 399948893 1250 399947643 399947657
    0x301063f0213050303070308090d0309050604170c07090f1503080d020705030d0c05090108090c0907140f040902030906220b060d050a030206010302030709060f0915050d0f02040506040207080a 84
    0x40c5210b0080e0501014200c09401c494560b1070b03a0070000c002075020b0f21503007002d0083c80002e42c60248280607141c2499001801420b0341d4886660f070108a88580e203303200c220300b00b4058083c2d111814001c040043c030544d103006c1004401c40000d402241d100c912902a6910101c10420018605205403040301000010058843c11141402c0f400c44c8669501e00700303840d01d00040c082401d900f000140003600740c01e90742d180190351911610355070398410101e060381c0302d024080000c0ea00c81c4110690050704a40410107800d00115116041e01c942264103e01540c5801008120404104000c1c40740d00515032403444c0a5468101100d801d4002c410f00d001d0101106440010020f841f0179460321201a84036080302c018000500f0000e403200c100b80412031180c00790070300c0082c8820541c0a00401d89030b09441c5850180d107800e1548000300307401021860142d994403070000c5d03207a603803800800070240114180001c41409104010880380c005001520403407040c44843d010034503c0c026140c0c2c4a00d2420511 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 399950143 1250 399948893 399948907
    0xc021f1821020d03030905100504150b0619091205060415050601050f0306190305010507090509070516020a0801020c0303010f0506130302010f1e0903060b0904021819020301063f02 79
    0x100030304040c046c06062849000c8000f264560a80c0c00144a240580400b8244c1c60041c04808251030030504c520341d11403c10701685610782d01c2a0248031010b0214202802c941d582c0d5284041c41c03c86020060b01d142d08a40200814000d82012103c00041c0c40c3c0010003141c9028070010f041ca0141004c0b440115001100040040e1900c500e50100c0740d50a03a43c45203c82d51300c1c98454040c06007111a07070700003400c280d00026181030214055014500541303c66080c00460340d032040c5024000c4070103030303480b0489502c00a242182817000780081040310000e59641c0d0705002d50808030308196801540a944c041004d82840f044120b01001566824a041307180049076150480344c00d80d4403080c0c012000c400c020748200c40e5403c80c10080c21240b00f914140400a0640300b08590396400b06d4019410001c9860100c890b0344113455181d501c07001d10001c041c041c403d104900e0040340c000340c00140c049a1441030b101d00c0f00c3c541903484050155032001c00d200d0320106441c404d40c03e100e03440b46051460307000728400b = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 399951393 1250 399950143 399950147
    0xb0a050a020c030106150e03010510091e0f0c0f0e010203031501020a140102041e03020306010603200c1b06030415150305060f010609080a030e010c021f1821020d03 72
    0xb900003040014024441c49454060ba460700c0003000c0010b2002c00d5031901d80200d079080600a89208041d2140d41030011441d09413924060701078480840c0c11501078906201d1407801d02c0c415a030b184154201c0c0000c105584400290020001100380d405000001d0715840c240e03039001003145c1d4001110800150302c0e00c901e40040c0d1400540f11070042a4200003410b40c1c00c21701d4150b028004481800d08803000f80b146000300260304203c24000a034061f0800b000601c00203000e0b1b0401410250071005204100e015401c00d80c0346c1c0e402c20000904076800c414500701c40c9415040c001091a007089071920701c3c6041c9a42c911a04400d00b04a039050241c460260105120040304d070300000719000f0003500c1440c540006210300718002401940c1c082a071502000c50314140010304068855815110801e105041e4001075440201109080343e10202511030004200d0046c501c0000700c64180d2036581c0191800744021550141c140c1151000d80c205082e900e02c011154290110440e270183c0d200315806801d4201 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 399952643 1250 399951393 399951403
    0xa05060a0c171306150602121303020d06050403170601120b0622080f01020a1b060b04020d0c020d020f0c01120207050f03031005031b190801060902070501060e010b0a050a02 76
    0x4800c4010181104201e980c0c5182c40319800c3c1c00d8130900b0308209a41c103c0120b00300c051103501480c001a4008486000c01d50300c2840180001003003074500858103941c030742c002440100c2003075040b56916100c40c248403c15810911100e174000680008003091b1900c100028800c1c0c0004060001043d140d24091800d500d03070008880c0401c540d05688180e0b6181c200d201c089415861007a40143d110f008043e81401c203040c0309a810100845d41d60342d000042070110109030014140e020f9642540c0c459941641c0d55991008104803d20030fa40401c81001a87d000781c01c1814450007030040d904100c440003590400403609100480c02424104d504d441e00d0740000000380500c1d2001401071180310071721a00c10710004040c40c881e548210001c00c201e6200d0007450340b1040504081c942102c044002040300d403400440c03841980c121180541f00c0c081d641c41165007900d10315400002035950000b084020b02c442030113144041c040c0d41c0c2e140038665262011961151090180c100c081003c04140b40701354901c2805 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 399953893 1250 399952643 399952667
    0x81c080705070b13120f08151807030f0c091d04052a181803040608070c11090a0b011202040b0a0509130608070e0f0f011802040305031206040606020a05060a0c 70
    0xc1e1745c1c490b900358100c080c00d51104080f411010030348842c0040c1030719030600119028600003510b030105103190344020018070240900044141600d034120082d10041078420341c1080308250392551500743c1350282246108034080075140218443c041040045030000071400c5203101e40c0701c45810045e1012a0725013070300c181442e60550214202c165440c404443c81c0030036000300100c0002e081030000031000c640d40c9209070320a00000c25200c40016003172500400504543e603015180c4031049010710710000741a0f8404640b402000d030740e034203100519941c2c0084200b000121900007140fa09082680d8070980e80100180101004000501550301e52251581500a2240583c003404256260790307500b6200c0415000d4560207003100c9000802c5240205040b500440b04024215042d900b0107406640c07a00c1c4200d2500106c80d020880000080d80410080c02d107c03400c0316018130a41004410801a41d081d0f0744908215401914484d01142c0041041c03900801c0318a00041e1002e80101d0581c0c40f0883c0d1a = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 399955143 1250 399953893 399953903
    0x5060a060e0613090603020f0303070b06090c07051f0b040903020a0b04170c010c081509070e0307080f0307020a05090103020306130c030206030112020a06090f0e040c080601081c080705070b13 84
    0x10703030004829084d0381003032054900c200d4903003030440d01c56030905a483c0140300c009044201c2e2030011490a00f000200d154110241300b8a1620b881410b88031a4a0030415501100b800d08480050000104140c400e000c40008200c80c00d10039100c190310025650304a000c00500040a07010106081110100251108481400905854840d001791650007402707941000310201c1c04907000603810944e08940071003c283d004024a13200d4071141e0085894010740e00205030144101030002c284401c013000414005110140103540c1c66030300744144003014005600c66400341e401c0750010f1006070b4001c501c031688000900c00c042d940550b141403000340310702a50300180d0481c2001001246151500c505c89505a0007500c03d58004d42c0c1d5400300b01c1d0710404500c18160b150b4070a100c02d008071800c914005070868005c0c2c0d5003410303094a554070141000c600f85c3c07080c0d042c5d5000c0000c450040940080004c0707001c3c4103080c40c002a1900d19070140152140f40da00500d12490600042d51001e02303039180c1d001540e040 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 399956393 1250 399955143 399955177
    0x9031b0d21080609041721270114130309050a2c040201140c010204091103060310200d02190503180a1502091203131805060a060e06 58
    0xd06a01040340418800c848001541c00000500500301481020b00171380d40200141e80c030300301d51039400820341c03c0035080d0b804802c0241700d10042021614002e502403030881140c0801240130011102c0d023411690001507950f410300e550350740c0d4641e1910501e80e0007040200303c40318000440c030f0101d9001e09580c00c0654040000e1a01003680d9050007001261203038250143e903c00956981034a0000c10111402400a484044800180143c000240001c40050707c0098106a182da6002054400100f000034180101000300212882c0800094180c1590200100418504405190280ca0000000748194140003604041e01d00d61380d4111650020100c03503400c03561165038401400360340143c034510544088031700715403004078000c10408112079111140380c80c0381c16051a054040e401251036690700081c240c0001c00c441000703000400c48180c0e4100180520790403c8041404031420345803202442c0e1902d01082a5a1103500d1000c05403003080c203000d0750b04294140018814030418036500011441 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 399957643 1250 399956393 399956423
    0x411090405060a08030d0c030c0e030c011805040608030901020d2606130c020109030201150b032706040807020907080408030a1a0604030606050406060305041e02030106050612090607020309031b0d 86
    0x660200c00310442d507a405000e04842a0000c841cac038020455400ea041d0030011b90307860258042da083c240000b0000004000d080c1c1d59000140440e1030944c06aa2281c1001501c0c0d0010f40c2d0501403001c0e81c0c134a60401400780789444024189866411800640da421440301113240d030382c0c9600d10306540080000061002c2c0103d81d9000f80030340030441084002d0343c00c141070024000d4a02c0c0c150740a90b000101041d041d0340e114992002215071041c0400800b012051994448050a11150f841540616610303a075802c080d1040c0803480c4001040707281040b44c00c100740710004000004403508260890404503610080302010203002c0b03413425070503600450004d00007040008540100044500c121010483d1503079912050b020b81c0c0781110001c1c01c0720301000e50400c58080305012110554009000010710070744a50100303407660301c24079000035003082503020025000c108100031a07000d5541e1003d1030614080d280400d9846d5030100391030910300b2a0b80d09040c91621030442920306590419810007100325 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 399958893 1250 399957643 399957667
    0x3090b09010b0109081c230c250b1b1608070806090714060c1005130501150e220f0b0405070f0302010504090b010210090b090c0411090405060a0803 65
    0x2d01c8038149070105210400c0000d0780340380410340c14040304d01d074070f44001042c4540ba02210080d0005480b4110b600c41c01c1c4400510090744000381100c5001c1100034070a46081d4151540c00500d24221004c0f0003c20785410700400e800b150070340d140d4000070800d00031400d407240561030a1450704050741c540c5140b003040c00508100001641003c40d41c007201610b1481c2c41e100c402d551902301c2c601800040b181e68440619242c105a401003141c180c070241601c1b4001030945100b8162002a91078268041c524040c160602c4028844e460600e00c0d07480044000500c1e1241c60001180b0091083c0010705000e81000703003094400f00c82807025680004040d010104a140a00350020151002c2d00c46105422001c07034009100d0400c030301079a8058441a04003850001c250018046c136015250450146052407d40720b0224010f070700740d4500c9a0410002c0d4a001034111f454100400c9007688690305200c1486010310003541113415504c07003541d0208080c0d586801144801d441680020194480084d502d450f1071 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 399960143 1250 399958893 399958901
    0x20403080702042a2312060907050c0f0c100e0d0b09070b07050a0605060a0b040e070504081c0e060f04050411040b0a0e0f010e13051506070c091113031203090b0901 72
    0x10141902c1c18514010318404800c500481d211b07109103244101c0402d40c2c81c98400c403842e5105105241c0b1600d0118441449400e2103101c510789a22341d071005e900f2000610344090500d400c0c0c0018a841800450407400040b010405c604002e0030300400030012620040303013400000060500c1d00c090642c2c440c0540f4060790381c0c00d0315540650300b00d480c0c440411564944280d10f1400c44088071805410141803000c80c031081c41d0040d05c41024050308000014080106010940d40f641c141b020f6890420740c0a0345c0505244244822180306150403c00340c496200c580301500d00395402035400060154407041040d505118a4101c85402d10011680c0455075038000890741004a090324211524040c2d82c0040d50104080030045a001c040d0598640301ea4525a0000380d100b0800c44000e490b42c3c1d804000b10340c695001c034000b603a8001d8101002c4c00185418058040441c1088010328070b007000050110300e2080d607601000b044002c158a501d4000e1380710750408082d154009880003007074144000349034024 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 399961393 1250 399960143 399960167
    0x8070e120a110f090c030a09021017010e0105100c050f060f100803070201050702040209010309080c1b03030903192a15022a01051e030118020403080702042a 69
    0x78024061240307441e051072040844084006004c1e1006919503007103410039504014051401c042d0750f0780f512009a0b540c1c1284031029040ca4441d410b5800381d910a0b0b0350300f440b05806c01130740b0040c0300c0300400c0191102181030a07582c242e441c190580c40c1051910508240041c845080c0c54030411051000ca0940214098040c4c00e031413156000569071094101e44900a060010340820024030042c0e0140c1026001001d26100500d40003031040600d40e1080c02681000310b41c903086034040e09032044010000e0040100ca440d08030002c0d4101b030814000603983e56024648050310a81140d400741c1002140c814100f400085180e008070424003560f110203080041c1c5c414050840c4a00303c4800070300d8004030b00f260011121154054501d06c1c1012180f01c1c12140d064031904000007049103801220901d500c3c0039169402041180d030b65490480d9034418020740f1076804504500c1080304000046064040380c0b034855060390007146603004141c940c00341c01e054104900d0b00e88030180001c0a0658045404454 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 399962643 1250 399961393 399961403
    0x6061a04080706020604110402030a0b040e030a020c03010b0609061c09060f06090216022106040f060b030d1218080711100c020603270d02060702070e0c0a08070e120a 73
    0x12007903890320f081381d80f80010784020b08003d00590704100e0506064000b16406183e103003010541c004420701180c01c8400c05141104550004107c02444035414054615142000c40c000e0100d6481c0000140703062003149101c0d44180c00020b24002d00204d4031007242503c030071490003008040d0710750030440041c04009100781400c0c0d2410001141a42c0715200303882060707200b40040110400150700307000240016030030243c2e019004140c01001f498040008a05c0349104c2d2844405c4003140303160042c00e59040105c0741d4230941002c084042819031244603952400601724000c249408c0c525a1203803d10940b0700050040c200009503a070500090564400d402002941c1c540c4101c06100d07011503010082c1d00c00254482401c0000c641c8890000600250680c0d1010380410204000300c40107180a12140400300541c001104000c501034040c0180001481d0f041c12103030182c40d00483c0300d50503105609000091003e400041102a440b0361a0106c0404010f0541d44800703240f1410581d4908910704201e603 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 399963893 1250 399962643 399962653
    0x9050f1c030204151404091806150617060f090705070b0105040b0607021e120d09091e091b0801060905010b1206240d02030a0e0601030c1206061a0408 66
    0xc568440d02c00c980c212080c43d1056050981c2d510fa045130929146228008100d41c00c0c030005c600d042203071003003060f003c1d0500c42e00703111000c2c54580f02007a01c800042c1c2e00325004007030a0400260743c100c8860600c141a90405100c4c0303544000c001040486c0c00c40c0800d030131240207410130444541246c01007000d180186128440fa03030b640d02c100002d5680d044800c94210600740020001400c00203007080b65180070010b2088480742d80380202c1c0741499044109100e550100403d40d05440e007141800d0042c024400e0184581c51005072003030009812044015007a0341d8902c1804140010a03500a82c5090305074402c00d401951900d07014041c204a00030802081d01d080c0001489100004c1103440200c2c88421500b2107646003c10000080c001901c0280003010b200a000c0326182c0b1a0b00030040c444403880e005860742400c035450400c40301c200d052180075900080041c000301e6000034085c0c04485860490000c58025880c0040240100d41c0c0480513102030040c0f248180440403010340166007901b0200c81c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 399965143 1250 399963893 399963943
    0x6040605040b0604110f0c01110307050415080601080c0a120914011802100503060d0510020a0e0607020d060c050d050115020f120f181017090a030503060d0609050f 72
    0x8000c507400217580154540c000c00c101150b2003000006400c494a086000007451012005804070700e030300803520030002580005090040c880b140d840d6034104200351070a0440703440d04100181008a01400c0c600303082101090350084c00c3d10804d184501d640148405001c4e50026140958912030b09400c8154a5420029151a10010143c80c20a02e90b001005c1401c4620014026185940040c103043d810042901d90a40415070410420000a16403000180d5404081034010107030100c1c250a1031050004200260242c2c1c0c40c1210b500f0401e8203c2c0740092080307050202600e044c420a00c01d88009801d0400020300c000802036a10554001b54090700d180c030100c0c9610907200c44c1c10222035100000140400103803032040c0801350100c001040d20600c020110100001d50f0500f075200f04000190740d9201d0795041c03200701ca90f15608080074038002c0407007040c1e694019046000003042c1501038000760a8080a00c07282e500590042c68000082d15424082034004c4c40c0ca60440820080c004070000d0480 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 399966393 1250 399965143 399965149
    0x41404140d050d0504061407020706020106050a080d08090c180a0f050709060e0f0d060b01030c03110a03020708040e01030506150108060f09091509070302040609150512010e06040605040b06 83
    0x80c0d074071a00707661114074045840c1c04480040c1001303481500c041d596000300840c402c1c590200d0364010f08007a0003c040702e03032801900900b541c10b10780000d4001c1c09101c004000c084000644510303442000c0c2008421036807145409440d218180e94260b0b401030200c00b800440c11082c1112a001c1d801d854002c0c8524010900c0c840c040d1034003601d10400040030414104070301841400c0d403a000413030040c416820300c0d051500284202d040044243c40c8256901d842043e29178040c40f031040125090f080a02030340244004150890284d09031110074160001005401c020700c840480d4040c02d80d40c40341e0191940c5906000755146c0c0d0440c2c604881f4802c0c4482420b041d8000e1484900c81e00d0300914005e4091450001d11a01d582c000e802013030f00d07224503d0031400b20f61300345031014400c00340d0f47e00801b2000d10350300401042e43c403191321074002c031450190608950344282d2400402c1d50f00a94107218082d45030f151107401007c82c10180801400356805101c2045900d4100e031f8000c82c0103100d64203082d181c0d8410 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 399967643 1250 399966393 399966403
    0xc070801061a070501060e0f0a05090d08010b090109030c0608090d14031b090909010c02100203160309050307060204030303021b01021c11070f0f020103200313020f04140414 76
    0x7082d400c0e403046150340040041e6030004081052040c00040303180d175643c12801400f4442034a00301d40e40c424a40800c03010050034440e5a03440401d410090222801d041400b40507400107010341e241840c00002d00e40303641c0e4060301d10803000310f0388007210700c251301e94411000b0f20f460ba00341e0f10165a4001c01d41800c0143e4854802501e20000a016461464036120300400ca104090705c0d0801c45110240728900312691146100d1348500c0c012400801c40d0495542d00a003849540c0343c0c07a1103030600c1801444140030359105008c2e40700902d81400030b01a111342c205580b41d4040c520f0000c00c80c1c3d00000d0003108040d4150054241040b04d0060518144c1c0303400d04486c282c3c01186603d204c080200307281815000b03e00d4200303c0c4000144180103180000e039850308003000c180410183c0340da9503590750203c1103581c18410222240c1000d40c2c91840c0f20a081000041e5110152100d1381d1340c074000f1100340940d9a00302681c040382d01c00510800200c84010500582050201c5023034a0780015042101207142d00440c0e = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 399968893 1250 399967643 399967649
    0x30804030c08030c1f06030818120f07051e0604060933031e090311120301051c0201120609050a111e0d0207050607050d0c020d140714060c0c07080106 66
    0x2404403452503030459000c105c1c11248410070a61a03100000c0400c1351007009001090076400c0320340c245c2c0c3e18201400300510703807416481d42550001c441703000c0d00000803c0310340903a83c0894016100c007110030710340c00088403c0030b900c0b640040c00250000d03281e500280e80700211694a509012404404544a0010001c1c400a111000c0c88003038400c40750391007070b4403d11810184100c038030301000300004400c049a850360700460225826406000540108012880a01044d0240d8a10350f40c100070200310003800f404a201801c0341602d8501d8210380c019401200342d108d82e414100700c0103541d0b4040d107002d80700c165805849645082103e69144428078112060300c0100610f00344100880c80b0221982ea01084180101941c2405514001082403044501030315940d9900d603107030a00c84e01164202c03110a846041075622940041c4102d9030806800700c40444cc0300e0b102500c0341c2c0b5a0901100c8012580107041041c00b90008004007540110050a80015608200c41c40303d0346550043c0d00701c40b0240 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 399970143 1250 399968893 399968917
    0x14090f0d0c081801140d0603020906040b0a03030f050d050a06031406010e16110604121d150901020a05070303020d11070b0306190e07080402090601050702130203060301090c030804030c0803 83
    0x42980d4020380084615009040c540b400b580070b800c18455415401c03601101b1032107174481508105503d8a04030b8181c210030101c0e020464540b10b8000a10044180c1c44014280150382c080031000303e003d0b40a4410360b01d00d10400703000c0c41c902820254020b082e1070100f2910408550a444000800024854141c610400c01c0c0d1502d40c41d03c2c400490070307103c0201820104400301c41d50b03a00303000b07051103400e0250b4899040003060803007018010740200d41000a0301e040c1c040f100382070b548664916500b00e80d000c144507052a41c81d886c02004034244044904007420b10700c194100002011760010304024104004e035544101c2c0c01c1103051307454545c001841903214241e800e1010070b215150030020010741c8035a000c000790003d942c0310000d46c05001308440c2c000c00310740755004000541c10041080c65002c076007460582d1400c0707000e5000440c480c40e1005004801035010000a1039070b1025840034000da03422644003001c840d600e00c0c24030440d03406404115440c1403940e00002f02584000305450748100c0c62 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 399971393 1250 399970143 399970147
    0xd0605150a0e07171308040e2212050d0609090f120c030c0210030212070801180b010f081005060f071218032a1d06010f050d09050114090f0d0c08 64
    0x90140c40c4d0744144054071151000a081400c03100090601d03008000400748402868424075080c4c0c00c17581080e852240b003011000c410b180100c00500c00401894202c4401d003001d03501c0711510364089004100700e0300084102c518151484045c004c58011040e0340510811076100072040c8400c0480702036410303140c010b0200d5030144d100c030014030b081100045480d91901d070050400744075415100e1101030581e1580c0120789183c0050000205401480200303a05070f14003444200340c000c0009000c440310002181c01c11001c00041028030071340d0750807007000b004010304c0507450b008501804101c543c0b05140869410ad0905400621540121420312540b9910300c540c0c2c04951440d2210700741c903200307402c02c404802501c0c9540800c00040140b20401b0782070303d010155522481c0715030fa0a2400d0003030001030620441074007004582e64440d0440f2032501c01e1040100702c10754545400c5014040442e40c00b0114087c900422014410018841c00310901860485e0780602c02a2403e031180140380402504400e01 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 399972643 1250 399971393 399971417
    0x29040f090203060d06090c140303120a15080d05130e06030c060c0c031204030b07030e1207030311030a0209031b1e1804061a0411180d0605150a0e07 65
    0x89a805954000310141c100850304c10300759260707012240c2c80d140c211443c50b1030007024003400d02020202055900190002c615042c0c0e02003580203000d50040c840f81000d0307229405054140c0380810301c0320040100c0d408070b4000e50051440900b081d0028000e140d0741c54241c800001d80c5410b034895150081d00f000c1c001d890036a40c0b0300c003404242d5200a1000045228002403250203443c10814032400c044106000d0740c6a43c00d61078240d000c20006003010081500305480b01034241340c00b02c0c040300b04060300301c2079581d81c1c0307014541075028003c034400300c41c41284044208060618150001c21aa00303040701176036040000003819444c0031a4a900e800d40100d01031603024603085551007901402d20b001840f40d4229101d032080302880c4482198119540c40c2c40e100c0d02c0d051440c1c0c041e5030800a200c211010300c10b0359003090030b42e40e007406948141001c031071064046003c0c0c1e840f80b0450202440d008501485585021040b4007510a0034000090142810b12350000d20303001300c07007807660254107195500e4105001c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 399973893 1250 399972643 399972659
    0xd1a10080705190c030e010206090c010818030316030608071208030408160f02040e0f0a060221040326010605070b270c09010f0303120510030c29040f 66
    0x80200000c040c004100036203014212501d03041410700e09140d40313000c85030780d0520340103011654594215040d0340c0b2001c14807520a40200300e1b074852610a00c0c0032406c50f954002100703c906d0a140c01225240800014428456030303828203031a124800740c40900c50669031f00303410b56032100244034002c9a00030412040c000900940000c64025000c1c600e520308003070011440c7c50140341c1200c001c0383c0c107450210344c20045007418001e0784a92001c0b03070050040c5c1403540e02d0107074a0340301c08140144031640c00140c205604c201007003089141c40f0150740d0b86046180038030307002c0c010450003045000c01e0705052801c1076600c0043d21095040c1c4445949143c00d184442d82c0e4003100120140050a40c1d140503d18410b416100c07603180d0001800e558024880e041410080c042401b8060f0050303140da0003501010700129411240c00e1030900201c6c100041d15660b030201d024044201500014240f100462002510b05240140f140d5404c0b02401d149000482400c0071403854130a51003402c115202c41103080000790 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 399975143 1250 399973893 399973907
    0x50108040b0a020f0f0c1b03070f050418061b03050a020f090d06090506240901030f020d030c051903020609010c210209130501030311010203100323060a020d1a10 71
    0xc4e01c0b40701c409081401e045546811600311001841042d40019100e15035507505a6004c4c1c090042a8007500c80e15042401c000e542c030303030607002d0709010315103807a1012210300c00d01220000180d0401d0f0100a0010300b1128070700b51000300403200001a040c040800c91201e2240708440c030800100c00124a03008401c01801000c0003d47c3d8250b81e0281c1d5240c08201040c0c05111681c4100d440d40c03c01240111003071448600041c00520f00380c0212034820040c00018941005a892039404aa5904400c450351804031081368031040001d0107401958000c00e1620307c41284c8548061094007516521f0f5585012030742203030744142c004030000d100356040c805403004041014290085080c40545030a0354080440d02d0500d04c40d4000c00c000d41d0301d1004200303140d442400c03024408070007002586107080004102006c20704901015041900c03108a40c0c48000445c5100400210100151455440d080b06a00002d421001021811a040c0b21008400d10541e040031072404400510040111804044c229031314 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 399976393 1250 399975143 399975157
    0x13030c050f070602010c020115050906041104090603060b0a091506080c0c010501080a03180e060f01030b0904050f0706090602030d0506010207030c08010b150313260a0810050108040b0a02 82
    0x140c0111180c4411465050004901500041c4c0001c00c0c90042540000d0071503444201081070030014410a2003181e45d00e02407140c00001c120703001324140400303800c51705041c401c03036105803c603a290030300010030000744d40c20144240704111340600400d640d48046006a490003100700614951060080c0001c50080e03c540340c010740394400150074040da02915900710703082a00308003016445520003008042d0305c10009801c80340e6112840080d6450000360449250019007501c0c41500d08500030b600c9271b4400e5200a423035100040c03007880c03142024141552611910313801c0c0010b1f07002d10040402d5441c044e003044d0040b0350a075030045180402c10040f190007410003410035070441c003c0400010100780c1c8940028040c01001c00001240c000070402c02c00001981940252490000e00801c0f030807450400d0032102007038015002c80c1a00c0c0413081e0901445418ac0103203d403000c00451007441181e4800c1c107441c820044481d00c00c03000c03900e0b60300654846800b10790040003104100000b46040c07110783c003d0005 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 399977643 1250 399976393 399976403
    0x151a040e030903010c0c05060912040b0a0c0f0b0a0e030f0a03020d06031a100e060d0b190204170114062121030910090b01050f060405040c05041d13030c 67
    0xb880003840009080d54440411400010301c0e01c5425428003030188041900200710400a0074120060407421100d4000c610405005600214220124a004080c90b03410310341d0200d078011555000c3d00d0701d0700ca0b101c0d042e208a58a14035000ca03040c0704d40800800c6030302d0a035050400b281041d010400031406940980c40302c031191034681c1c3c4008002140c00e00e40200b02c1c010240e2840322071801c440c181341c8003801a44046c00280750708091103182d84402c040e030031402c1e030002e040610507075401041c0c01100b01c110100c0c448151001030001145046101181c40e020340b140028003004003641e1600b01101000d60300075a2200b0031502804003001c65000c1150220741c100c041d02c00c944401c02026a40803880c520380c0710034130000800c00003200e0301442201c3c0840d070180c1080000c8486a1a0510904014002d0601401716000e220241c0e542d51030507070700203000041c41440b04240810340100355030054070070340c04401d50300702c8508030704444130303820902c10100d441d90603441881c1528100c40102d03500c42c060f68 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 399978893 1250 399977643 399977647
    0x603020609120a02040e0102030618190507050c1b01020f0106050a12140607050414010f081f180c0305070c120516020306070c120f02030910020312040b04151a040e03 73
    0x3c01621703140100e1140080180c001030726440c01d6418403101c0101c644032034040620240c01c02600342d1078031b10b030310440068440d0f002a155455800640b0a84240780b80b400c0c891040e1032103402c0d0300c0a507003c01081240700382c0c00c1e00d1105805807800c1d42030700e6103401401d520000c2c201007801480508244403100d0b9014540070002c8400c01124581015001e4412500048000400317200c210010b800d880443c110030310b81000c000d10008401001c041001d89014484c40003c0208421030181c0340c40807015043e1030961112040c41c0c2841c410040c0b00344001000840c0c20040022015400b03a092010629003100002c0c840701c90a207000c407450b5001e0425402c1c007055400c1c500026031410401c880c03050b1110b0b103921401260740d081202d06a5042c20b0740204200d18640741d8001c0300d50100a498009005030b40c0401e48446400c2c3c00e03815030240310040520740e68a4000c000500003590710701c0e80203a010341250440c89010145220549040c440c001890140d18290380c0003904107039000c03e41c3c1c1c1c0c81c00e80030b680c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 399980143 1250 399978893 399978913
    0x120111031306110f0c12031e25120c02030f0d0b030a21030501090b182d070f0e0906061308010627060302010f080c0706020f0a12060302060912 63
    0x40d03a00d400010445904d6400421041000d00e41000500018400c603003800b0708502d000904904a81003c00180404901040100d006500450007000c043c0f00381c407484031404003600b0f8008041c0c4201051020310303e0305104203001d6070750001c011100160b408105c500d243c4000c0c03581d07080260500701c9019805118001d544400700d6503a075800484024542109880460541402829110107804c02d6060514120381e40c9140e540b9050000241d28496085562595906c210840c28941c00c80c04030f04c0c403201c500391030031011039051074a40c803e0100d40c45e505410f030040030701101c0c0d070000b868142e90040140d002243c85071400c0b0010f070400f82a143c003554030715912002305d10701756081940424810074902d6103c400703000f681390420040c0045141e0420029265400080c1514981507819041c03100d11000700c0c00d00104a021941181d8110105654800482c0c0045040d40d10889005000480061411a0080440c0500c00840c0e4005004a08041c1503004000c02c1c0131707140c00345d0b110902c100d04000b = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 399981393 1250 399980143 399980171
    0x6061e0521060a020a0323060f1807051908161209120908070506130909020316030321020c070e09010f2316080c0f0d1406120111031306 60
    0x45803003501c81203001340c1c0b144a00c2e1000303410ba41c00032141c171030342d400640507002868581c1a1400d0f4460011105480c21385604404079074100960050030700d9403030411080001c02604000149481d003011b114466600c2d00000003120041d030181c548001c000386001d103540d046413050280c120401c1c0741c0540001e8020b840e9640c6e40510786940f02c2140803503020081000400c4082c400c04009200c00e031101d80ca48104105010329019aa0042050b181d6841505c2c0701503440c108107030640d0176145081c00d03500b152681005094455400034107103a0015810721076260141600a580c1c0905030000200b000b6800d04c0010321005a004145004540d40d8010250000d4464003c2c51241020785100f00209100c040e010588501c004220828030540c42c88403808095101c240b441e400703642c407245141c844c2c5120b508001503200c4c001151080900305500301ca625440e025950b0b021369411900c480d2505249a1038034260b40f051a40b42e6421801400003404081d483c80c40709180d10300c20140095054528012 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 399982643 1250 399981393 399981403
    0x41e080604390905010902042103210f05011403030d051b0a200102040b0a080403030b040e060f180c1203040801020309060114030610030204020702030f030f0706061e0521 75
    0x1074540d4600705090401c226040d900ca039901601d1000b1043d8500350809c804130705c0f00c00c00344403008032108401d580407040c584550004c03000d4a180c086010040440040000b0181001750040c1320380e185403200004802428003101e020600001c1c020b942006000b90b402c00c002c0c90010039440040a20500c0c00210740a03c40080c00e201c000e9032200004002d0716403c2c5114828020442555a84104001d01c0b0004285003900d4495000745042c009070740c0d40e49000c902826038001c400382c0060404500c01c0044001050700f6204c0c65040d8000d07204c07681c0d50b403200340c1c4d82245d40d042070002e900240d0203100719040c40140300b07000036856400c0782c0c9016940c3d002982241d10403280510715403c8200188458210248000b040d042c08900030b11407402d00d6074a407002c40c40f0030b00c0000d02c25a4000b030800215101802503209241288056075214212822410140d6118403400c8440360301e0040081004012402c1c00540a0b66092408203020b05010900c00c00c0c0c100111749031510180484010345d54141000 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 399983893 1250 399982643 399982733
    0x60a02040905150603010b0c070807120308060406140d141005061503071407021c0303150906030c0605030c16030203090117060306060f010509060f041e080604 70
    0x1000503696071034000000210742c40a44801000c08007104820165a900e5041d070303054030300692515a03030300c005070f0840d480e010850344500e641c6e004852001483d030a101c4924420f0701d00948500c1d00079626041040221b650382c0c0105903164031540d41c85506410b0131004001141d00c41c010340f00081d2951380f81240380c07014221540a900e0340352420400b0340d04088032021250b020003101d0f941981000c40c0c003d006920b59410b000c1d07810070049921000d43d030314140a5540301a00c003070300144040359810001c0190018401c1074014032400c00e40011000140e00c075440850350000d1444100d03a0806408860690011300200c0d080d0308103221000f40a0311050300c00d0104c910980040d5900ca841100242c6551120b8281407080582d07882080440d0700c0104503541e00000803248500545944401a0b81c0f50003070414140d00f22a01041d00b04019030707140020415502c001042c0d8890380200b0000c0d03180c0d1602c900070500142c000380c020400181010355102ea4108000c0284c1d0007281c005405001013a00c0d641c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 399985143 1250 399983893 399983911
    0x30e07030b0c0a0e100f08060105040b120601020f1b060a0507080d02090906040b1e0a1e0503010b1009090905030405150726070314040e0106090602010e0c0901090207031106 76
    0x80d03d60303580380c00903601a480e01c0c080d00c0c030603206036141070003038030510705603805c5024804944000341c41d5038407410403900a4080744001503103078080351200c85c580e81e004651040c0503104441d502d1900c00000540094128902d8400d004c01c2c1400d082807100d00d80016035590203000c003e210070342c0011100c030080c2504024904006884070300c600200010710034041d140e07501440c03511802c40001e844404160320b10088040241c0a1640c2c44000b061112180d6440380386910020407a256088041c1c910840845204900a01c01d18403481c08100120f84d180e640d0700085450403004000c1c0a03202d40010312414001c40c02d81e4105640d40d070104983c50f207a09641c41c101d000002d985c00801941c00001d2403211020094001c03101c071030703081c207480303030720840901606028030b08140d86c02d091490801c80c0d002c0d00e40801c08007075550f07440401500c03101c80c501864001d5401d0604140b806000041d40c014202d00c0100011246d0746881751500c0203500c101c80c103a04000c0145202c0000020801425028502d09 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 399986393 1250 399985143 399985147
    0x60318140f060109051605030601021518060a0c1e0c0f060b18010812090d12020a031e05030c070516170c030601050609280f0f06030b010c03030e07030b0c 68
    0x207002401d0400034160000303035001d80b800060008003107040488000031056410041d5594441c0d50040c0c1c50030341c42107001944c3c04964001c2091120100710100300611115084414548408050000317849280c0300340070000c3c3c00c91031100304022400c442419488414100400c640c0c0480e100d01e031222282c224140c9415481e1841c000c40c0781070020302543c00350f113050741e40031407541440b016640340c0a101455044904000c5403400e00b5540c1c018880070840c8c1c0c040322010b48030303a41c9240652600780420381503010a004401c2c100ca02010008240230841c02079464074510754410039a00340e141c215850550f020310488120710504900d0b031422a000d4580a60a0004a01c11498441c07500c3d4000e0705150181c0c0180d001084251918026108111000c46050400c100c241485694070000f980c00884124142c0703000040309810003c200c01501da0b403c001c0306a503071311a03c00340c082d1091141410f0003c0d08408480c80800c2c480d5022542e40000c09003078078201c0b980d81e1aaa050000c05a40344940d81c080 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 399987643 1250 399986393 399986413
    0x180102040305150105010c0201080610170103110315041e080c010f06051002070b04030822061e0c0b04170904090305040f0807050a030b09010207150c02070608010f06031814 76
    0x83d42e03481d94014132003444c19680c110042c0d8002440003c000e001302d40900750603171500e0311107030180c2e802246045c004010301c03190f580d50307003000d0700c1e15804020a140240120010101116280d0410314801c0341c000c41c0340101d9030350700844d085900601b000280e42d1031206024003040c0c0e100130b0107820300d030149484002c141e0b030341030200f0400d40310b07000601001998400340040000a42007010340d021650401c00c01f5031140154001200110082c0c0b00051306807440240c0030039195001080f12080340000606e1901340400510161075100d00c0d1000901140c9070358000030005112200c22a8118904c40c03107403410081080007050980b000001d00301e000c08c60109080c01a0172082c0108001803075400300030f00070b00381b0300307130100d51462403c0c040074040002d18400100a82d000350100c5401c154010519032660019002d0796006000d900c40340da0040c0100100007401a00c200300c2141a0740d4010344090a403450403005a00070100d1038070340054002d1140041000c5084000c1c0200580c145c8000b801103048 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 399988893 1250 399987643 399987673
    0x20301030b15040204080c1201020d020c030310050a05010e040e070503011e0e06010f1a04030f0c08060f010612020a020c030a06060602060a020a0203040905061306030c05130e03070209180102040305 87
    0x60b0310000075001d18030601040001b10b40003d460102c07500305440c010650042d1b590214003a11401141c01051400000d41008100000004500c590b0000340d64200e081e40303c0c0e040008400e81032181a000644100302c4c079229160941c030400d406075252084600d0f81d5559000309003501c06c0b1244420710702d00918186a0461402e0060b01106038042e006040558105801114020138034043c20190141c0130050302c0e181180b10003202c01954200c0f092910b5040c031071074504d070b1812203401044040e0003a01c0200d00306036010690030341680d02a85408946201c02c0311800025013014100c201140b1414864019640381480030158035401030704e000c1809c0f07048c000003903e40100940030b07000941c810803050b14555804003e40d400d49041341c2000c1000e4440500042c901000000392111451400f04d00000704450b0101030012a80f068445001d6103004422a80880f00405030000003a0030400045c030042c6480407039a50b1041c1030030b001403020030001a9890890304507800c119441c0d4009a2982d01c0340c4 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 399990143 1250 399988893 399988921
    0x4121b0507060e01021203090c040c0c0302120903011409010509150c04050d0c09021909050312030a0209010c140601081b011e0e15130b040518060310020301030b 71
    0x8094110000116802580d5035541c6035424403620301009403c00030b8240d1a0700c00e1240c1800480800c0303035162a0304042508a40f5428102c403a144038502d0003401108840c001c1040441c000c0c0c00d03030080e0040181c0340803a0115079000800c441c0c1d15540e100c592008000620415a0043c00001c0c00000d1a1409040e40c0b45030101204402c0c03254000d4a0401000c4111407007101c0507510240d6071100c1d0f40c001807801007100c010070303007044000b24004030f000441c00c040c80d04012442900c5a40380e007520f075510028151142c40c0c035030300700032105010030000b000003507103400400715408185084000f4442c00c0c2ca80003040c0d244944a01d4136504020700412005008000803141190302001c1d5420140c11b820000c1c1400c40b100d600101d0690085e1030905195000c2c811154a02d6006030210340f02c03524114080425a00012490018807044400420516100320548050b110050214140602405080c540c2076600500f082d501d440b5601c0c90485103d980c0c0007075402148200c1400398182040080b4007028 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 399991393 1250 399990143 399990167
    0x9040f020301051302070305090405070f1e020c0f0f030102041e090b130506032b17040f1425030302010c17071103070b01080609060a0b011409040f050412 68
    0x59401440103001ca41e843e80000f1082002c4410300603902c2c44c182c0303401c1d40c01c1d000b140e954030b034000c0c03904d010051500e030010880e0405261a90300d034440c205070120b050500b13142031951000168040e108400b01810200f07501c50240d0402404081c00301c0c2d04000003403c0e0fa20580040784041141c1d40c07074040b0004440310204c00f51103c001c0500504122902181c84800e03a0300400100a072920040f4110b80c4050159403070360160901c007100c051005010322203820003414003400005013020764000c660040c1d11181400f59030300880d2980846160f898050307443c480c4c010b0204440c0501480030040c80d84c0c6441da4080e0b00300001c107144c5800d1950402908548039480c0c0c010034080340140210002d60803902c1e150b030240c0d050815580e00280e00c8455881c0d4051400020403400f4910004100c10400207003051080550000b1a4001e94403104184161100b10b05980c0c003181c1c1c80981e031089001400c0241c003502c40c02900000e554540e08041c0c405030340041d07400f6a00b4217445440c00c2c040d04c0d0310036002210307 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 399992643 1250 399991393 399991421
    0x111041502060103030e090c09040627090c0312020f0d02010c08010b120402040e010b0612160c0b0c09010e060a030c08011d1303200615011d10020106080709020904 72
    0xf903166450107003c600c52a2040c1c2e01c100c0100000480c04078090342900e00620020748204503503130300c4101031003001141210a14414540c104180d0082000d40580c000ca2a441440544814559a6404024460703564254154080d0749511031100600708030f00e002040040d4004511912910406005244180c210000c840d504005010076404000401a0465415140000e44800403545507004210440c10395030300a00004008512504044400340150f10f901405800e00d418020700381e480041e68500240852050300c0056100c52441c800343c40e10b0081810880148003400d80000c2c40c03a480a039040740400d956808250b00c256200c402c460142c00d440284000c40115140b15a103103c40040072041c1507412a5944010180300715401d01711340c0810088885d8910317225406517100c00c01100c2d0210800c0d0341d03014a12281d0300ca0030340e0b1040390355841c4e8030303c008051004c00d000c00310741c40c5074141c010366403a810001610f000c1080745078000c124000b030045e1600704010800c401c1da0464066034030 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 399993893 1250 399992643 399992653
    0x1d0c0a06030c02031b010e030403060e0d0314070e0d080c0f010c090522060b1b011407080103031d030d030f390c17040501020d03051b0a110111041502 66
    0x282e600042141c40c0d80c0e68444e92041c07480c9924000340e01416007085100340301e0001090000070080c1030b801c2400c4110540050f01d2501800c4042101110045c0740312400392400308000c81e206600454541c040305030040e04a103400744142d100c03011a640000e151604a5008003034206a400c400c2c86500b04a40300c510b403039a10249000000f0380808215407280d47c0d12914a05105e42c2104641d201000510100081649a1203810b1040d502202c030072460754415400d00d12041240900061b040f8031500e0079481c4c3e10000d0742561070803540e0740e1400c107110041c00300100307459120382d404104810082e1130030b90740070401e00c0d0302003072800c25206c0303c6401c540445992806e0442c10906500c0300041c0c8000c401c03001c041c520b024031044031045c2505402600d20307035694032424110040340b001801a00d80a8089910b1388090100460848a044070f141540040380c44503c41d40120703d20080400c40b250b450904500031480303151030308450002a012021120000d030412080d044000700001103002400949 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 399995143 1250 399993893 399993911
    0xa0e0f0f0303031f1221080402010903150b090412170112030302031b0406020304030b061c15020708120f07081b1c050f07140a14030405011d0c0a0603 66
    0xa0754034000a068002d0915058001c0d207809884c0403a00001440c50110002d425015420020505010070007500c0d035041082c2c0007050340f240581e0b07429000d40c0c0d042e5624030000d8a143c40d0034144c20721091170b601c006a01c03000b5001161f555031640074021750140c0c1d0b4a25110106a00203040203460748202e403584a90540100f040d0705000d10702160b5603406007005a620754501e003019401c1001c010b00039101d11808030f00856801d90000282054a05c12200303800c40383c984200300221980884a003120440d2800c0032013000601025504101640d080c401600380406a6034070004d90b0440802c0100c44885182005a2a00308849041d0800300908150fa410305050b40c0c2e600b10b25642c601071281c8044000b8220401c048009011001c00700c44040c20403040c140090090100f1a00340c40d200d0000c1c04e501202009800400f080710440c4007640c90300400c0c0c2d030545840000c0c54000600644465503922031600000d10f01d160800720742c0000201a1040e10341100811203840340c180c00080415203410a41 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 399996393 1250 399995143 399995149
    0xf040905031b15040f030201060f0302130b011b050606180c0d1e020a050c1002090102150a09060504080a02010c0e0906130608011d010b040209091909080a0e0f0f 71
    0xc4040c0045942000c03506001d500400385060f000010a8210704036210420044c0400080c1d0b00c46890300c41da00034011190f0b108028540c0c5503140c00060b50014880348118416101a403084444201c181030042131a24500f40e680b200a15000e0260ba031900002c00704611850b00e184849141000554200d0300750822010081d00da0103128500d40c8032590300d041c01d0021050b40340c10003160b03001c0c00d4002d5648600251004002d038000418071005481204420020080795000761001c40c041a401807090b080081d8010309424405442c00d07440c80d0f980d1820001041d03c42c09018851030198100b00d80e248842e0f4402404c40e8031200840d8108071403002582a56900d082c0c2680c2c00c101c1c1102c8049602c001e00502c8001495550300900296280414043d03900651035415240080c15070003c1100c030380303e0713010320040c0d1051401c52507000d40380c01c0005410240c0643e81002100c414a07001a00d6100e81da40d01065031b105840101c003245405440c48403d24000180c094443c0d005d0359110300c016031003004 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 399997643 1250 399996393 399996397
    0x3120f040503070b0a06031407080d0311070c2d080309010302070311010c18120503030703020310090c121107030801050f040e1b0a060206010806161205070801050f04090503 76
    0x884485090900042418403100300256001c05412072800301e86070034000c1c40f040040c10749200c01c640700c4032801410800890013040320b80803103100001074461008006403c230000d0200c0726200b1a421400d014607000b15405d480030b01b01425044085810104140c600c80201c07120149001e0884d840501040c400c00034007005480c41c0210a003005a100c0007585030940340091100d0500710958030b000001000ca0344d01003081104900c2002940f12034a4503810044810080903102038a640c1c820008a040c0c0d610a0b80150380c08060302d4040c8030307526202e1100c0000d0310940f42590780042c20303000056140121340d200386a14200002038a625041c006d6401515001d0140301b560310650030450540d0301900c0366000280b03210344010503101c88240c03544d10f4030113420070000350300e01a070078040001c203400c0d0002400c41c0c103170b402c404024800c039035450103426404003504240c1420040303881417201c081c804130f000b50360050345a80c0300d2803400e604210500c686400b1f03850358a4440d07401e0804c40f0300441c0c40441 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 399998893 1250 399997643 399997651
    0x607091203030b0d1b170304030b0c0f0711040f0618050601050f04080f0c010e030a0807032d1e1403060301110406021605030d090608190509010b0102010e0312 70
    0x118641a89103181829802000068441a0403400c0700c90350408100344021001c8800014010b0300d00025181c1101200070900b0100c00d80d07503648200014000310340410101755000209020f624503200000302d000005402c103c03001c80d00040c51010182043c0303468081c62a0483d100901000401d240104d0004000210302804503803959a1020404a1b44100300f1983c95903110a280f0b90307134503600d04103141d0f6118400e110030300600540ea19800300d584904420f40328518020010040c031a119141e81c40c5540c486201101400f600000150400d0440b0040480c02c3c4030b403001840d0455240b05c0050310404034104030550802c840c07002c0c0303503403a82c1204124100392a4451002d4580d43e0305c2000c071380104600350b21070002c00b070003180018410b03600165260910600c580018099940c59003496511110121140c0101e4503404042c40654030807000180c0c0640d48800801c8040d0a45001c201204d20980300843c450351910800c180c55602402414101c1c20114011807907e80c2070318040c809160094 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 400000000 1107 399998893 399998909
    0x60609031119050105030c070c060905010215160e01090902070c060923040b010c0b09060a0606090e010303230a03020327060a0f090b04081b060709 65
    0x9002d4120310040e8800c0e00c00e54103040064406800082c5500382107501032080b00d01052281c4801c40061581da00ca00d10028108000242003030900c1c0c40881c0c2c601055020300c40501070b280d07240c0b0ba006c1d03054038014a650f801280101c5502c0155884108920700100d40f001c140007182c81d80604846543e221911990f07503c0751044000784d00c00340c80e0302e1021130407808188941482d0300106140c510500d0095903d404543d1440d010036801e440d03011040d80004200000c420f824403504001d000e0a0078a60403092500c0c5450014000501005041100d00d00d00300781140e10b80001c110000c40c5031a500d039210008080010007e40044800c22010311b03001c140c225580c0c05406152403e25000307409096035aa842046001400c000405001c01071380c0d07800440045201421070380d008034414801c2540d50345043c4000311500c41c0c900c94882d140c1e0441c2d018800e41c0d6400600f510210f0f5418 = true := by decide +kernel

theorem cover : BRFrame.Cov 399820143 400000000 := by
  have h0 := BRFrame.cov_init 399820143
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399820143 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399820143 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399820143 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399820143 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399820143 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399820143 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399820143 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399820143 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399820143 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399820143 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399820143 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399820143 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399820143 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399820143 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399820143 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399820143 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399820143 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399820143 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399820143 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399820143 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399820143 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399820143 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399820143 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399820143 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399820143 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399820143 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399820143 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399820143 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399820143 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399820143 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399820143 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399820143 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399820143 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399820143 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399820143 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399820143 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399820143 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399820143 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399820143 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399820143 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399820143 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399820143 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399820143 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399820143 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399820143 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399820143 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399820143 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399820143 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399820143 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399820143 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399820143 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399820143 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399820143 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399820143 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399820143 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399820143 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399820143 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399820143 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399820143 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399820143 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399820143 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399820143 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399820143 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399820143 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399820143 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399820143 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399820143 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399820143 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399820143 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399820143 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399820143 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399820143 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399820143 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399820143 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399820143 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399820143 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399820143 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399820143 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399820143 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399820143 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399820143 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399820143 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399820143 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399820143 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399820143 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399820143 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399820143 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399820143 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399820143 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399820143 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399820143 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399820143 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399820143 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399820143 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399820143 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399820143 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399820143 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399820143 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399820143 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399820143 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399820143 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399820143 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399820143 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399820143 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399820143 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399820143 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399820143 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399820143 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399820143 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399820143 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399820143 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399820143 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399820143 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399820143 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399820143 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399820143 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399820143 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399820143 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399820143 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399820143 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399820143 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399820143 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399820143 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399820143 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399820143 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399820143 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399820143 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399820143 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399820143 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399820143 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399820143 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399820143 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399820143 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399820143 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399820143 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399820143 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399820143 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399820143 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399820143 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399820143 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399820143 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399820143 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399820143 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399820143 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 399820143 ≤ n) (h2 : n < 400000000) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
