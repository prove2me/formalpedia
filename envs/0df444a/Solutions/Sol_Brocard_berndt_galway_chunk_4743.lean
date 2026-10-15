-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4743
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:35:37.238351+00:00
-- url     : https://prove2.me/submissions/8e32ff09-1cc2-4166-aee2-703bfb2f306e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 852877697 ≤ n < 853057553 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 852878947 1250 852877697 852877721
    0x302070503030a05040606080309061c09050f070305010513020f090402040209040e010e0c1207140105090d140d051e0304060912080a2406050306040609051f0b070c0e0a 74
    0x7081004810f4198003251040d8440c1e5400c000007501c1314900355480c019880e5554001504019220b0002a12042d604e40200c480b01c0104000a040d030b100303400d0407801c1c10004003070340c440d500500801000303028265210b69482d40c540c100c5069a0001116400d1031014180107000113808607007035403a140c040350014200a0800e00001c10388040041c000c01080070220403600503e40284a10702e08400005440d030440002094141d044c11380d031190f00441c03500c069041c0725040ac0001015150510400c0d00e243c01248840005c1c00c503801054200740c0410b600307900300001040140c0c0180d00500c01204080c1405d008580c6075079135494004001c101d05500a4010050ba40d0131102ca40d50185a4034440c1d10724040500c14821b1400b0030f502c08048030300440500001c1d03194107104140c8030760043d6602140c01400440c20755551007984080320300684000c15150020164000d90b450320b00204401854043d81091034800d680e00c0e0606480440d0082000c00151440810742e89503d641202d10000d01b = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 852880197 1250 852878947 852878953
    0x90903140c1f02040f0512010204031209051207080318150f07031b1509030309140d0908030f092107150809210d090b01261605010c0303020705 63
    0x1d50780400c55680b00c070708a409542c2d265070221820008034900980302100c1541c01e500d1605401c10b020850f0b040c0303035090b0803403040d0b6080c8800000f080042105d80365000c007980703d581d042401c05050103450100c41c00669025801301038100310355003000040307038003941d0140703240300c0c0b0380321004002142c1030800d0038003c0c0c3d02c610115116101181120080ca0320343c0c42912041a03110740301c3c4018100520303548020302680c038409081c00300b600c001d0b0441c0359114802d01d00000c580246680d01c440a904405c000340496010b04100c3c44c40c03a4100d03c0750740180680d0340c015800c0ca4010170f10340c0014403441d0070b20b5000d81d66019415902c004401e40580350f207244081a10001c0f9100c5060803a20042200c03800e001480300800f251044c1e001140e0156a2080307140c030316103448000480c00c80705900c41850076586a640f10040070200c2c0710510824003a101c071100c2d1038031451041c0c8011105017000c1072024441e401510f007480c006001d003120441128000e00f00100c500d417807400d060f0700134081d007a000760081c0 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 852881447 1250 852880197 852880207
    0xc030608060c030f092b0512040507180902060313032006070210020f070609020f1008040204050a060807140d0b0a05060a06090f0504021c060b0a08011208030109090314 74
    0x815214003842c401c1300c050800c01ca150780c3d400c0401d951600c44160301268054880007400c000b6a01c199101c25040070340c1440340c605012102c0001c101d02c01183c00741da4942111400f8011144001000c840041d00d90405201c00e1131342da00080d6841c0300280203000700b10700e03403070102041502170700b0040d6044980034154590101ca06070320903200d40045840b0001401a030312607544421305d5100303480004044410060414841e0369800d0018048410103903402804002e54030708941d00e06c4882d40303000da22559000c0301400d0520600c4181d41d000350040052a080203c01d00032880300050f000c0803181c0401e02d20545039440b074042040c4074400320b4003500004032001081501203803500034a005000036107030018a00e641d48004c50b01403e00d402881d1140d982c00c41c08105524007a006041d018078882201c0003181d190b004500115003e60b4400841c4503008118500d500d80c01040d514010314659082c5d02120856039a511400d11050165004541e036900d00c040905210b030210300210b11841c8091503980c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 852882697 1250 852881447 852881461
    0x60114030901231f0b0d2a05041d0c0327010923061009090512031501090902030702030403080f160516090209030304090c050d060b1306030b01120c03060806 69
    0x40c00041301c0c0341900300c00004101242d0b8005000d4601203458a0308502d042101010040001c0c01204000720000151940b404940350070502110308140e80f95150155501d20b8106190f80190100c489000070000742c4040150248855040300c2d40518030442034181d1141c0b0040c00759880c2142400880d05620744045501081320402503417101e02e64101c080c040c00c1c0c148608082d61001c089487d1200000652020041c68001d5005503218a00c80c41c144d803c0540c22101080207a00100c501e0142a650000c031054296080324400740a48080f030f1096246107081d1001a40e17034441d0344001040801d000038840440f10204080d122001c0e100525800140d8241c180b5595071902c100107140f10003517000340090003503000d100700d031803400002d0051428146011315200042584812400c2807180802c502001c211003481110b002d48041d69402d502e032025000100c80a400c1c681106c01454604040108680e802140712500a0307000030011500512410085018044590210f0342030b00c02e0000b4001d00f = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 852883947 1250 852882697 852882761
    0x1060e120717120409020711030d0c060e030c030310050405010501090b030708131211010c030603020f1306031502030405160b070f061d0c03010e1c050a0e0d1b060503060114030901 79
    0x81f4034090403040c0c110b2040101015140d00ea80e150303840100340400769040018071036070030145007040108142c900700300d102c0b2107a0b42143d0080364421000d407200b00c0107002615251146038003400082c40c040910782d09001400e4031350700c0041c1c084018031040c000003d9080300c090307006d214031640c404265042189101006041c007481e4081c1d00640f5420075505a000303620034803402d03044a400505c0d82c5190491503007842104c0f00348003a02e07c04180c84010100104403903101448691801d4000160340b440d16082180c10072a400c0802201da040c41241040030803a00810394001c0b9401c4168108801601d1400400500703056014403400d400d074101e151001e120124860380110400d174004d00c09903006925403611008501e005421200e890510604031905c43d0026040c070030901d040200369040742070009100e480b62148126020a1078420b030146034042821040001d00380303800c0490542c00c2c0500042c0a00c2d1016020110588000c40001c41c1c1e88400d400400c84504002882c02d1020f500c8810002 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 852885197 1250 852883947 852883957
    0x308100902070b190e03040521031207080c0315010815041e051312080703090f0b160f050f0702130c03140702060f0c031f0e01060e12071712040902 65
    0x984c40c500340341411500080c1d0050402030802500a5403a150512040201d8085586c2d039400320700d200340383c0034490108200020302d41d00e10900f4003850f20303241015000f002504000c0403142440780600c240025640d9a00d90390003100400d00b03264507680d50b9816280b4198110400159110382004d800382900b00f6400e0140641790002c6000340031980d80e5502c0055414442000140441c124880080c1a244900c03032a540240e101c1c603000c5219440f81d119035400341c003240800d075000d1890301e052101203070006002480702d00540c2070081c1092003105025115000f00e40340002203040004c1c851045644030004483c0008104104012000b40301b00028010001a984404c1c4022464003165029000107605481103402610018807540d42c94618130040e0809070003007002c00c00c1d6201a01c40720054209540c041e05600315098502d41c0351903401098a07450580440c000c2651840c8040e1001000c5010015500c00584103221100740900c864904804009080a102d00200d0013055003115a00104 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 852886447 1250 852885197 852885211
    0x9180903281407150519090506060f040b0a0b09040e011d01060e09030304021c050102070b040605011703040510021207080a0e040506300d031b0203160308100902070b 73
    0xd0150700c81100c000c000d104040000d05461100b200c084d000e180503402c010b9011000002100f400304600304040d09036881040202c9254100340c0400401d0b05106a00c41c04100341150b003032108004940100e0f425040900400c202d240c000100d1603d140c0b6250802114045004020000054501c0000d0502d030303019841d040e11b5501f41800005d01c1d100c1444000d001d640c0c524095403468503940c0c00c11054141c00c00101d564068904c03210700201c2da080c0b0113080e13441c2c0103200e0b4550618280c5001c034115170b81608030607800f40c03001245044405001013078505542094507a0300f0500d2092805174900b46800c55521034060f4001100c0c410490b400019043c40c10311a01c9200400c00d15100f00002c0d20001c48620750451503141c001c030f4842c02c04a504909824000014050040c1800c40990502c229103d954020036100c02441c0440c074181c0d103804550403007502c069400c0c0f200140d02c443c0301c1088203030003904121903100499020442d2100750002402100c004550f07584941c03401101680d0216102 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 852887697 1250 852886447 852886457
    0x1080c1b0105061306180507092301080612031b0a0203250f0b090618060a110f07030317151003050405010c0f0915050904020d05010312050918090328 66
    0x2101034139081780201415900000700d0380c641201d01080300c00007040700410407010000803600c0003e50100341c0103d10340e0482204882c40301c600314440090726800c0301620290003102c03a04e00392070349070a01106885018a005d500a00780448000907030b0f00d80511008040c6d4035000340d4010009404040703907800801c0048200380c40300316590f00356500c0040307000e1040b003d4490041080e9256403602d04d004144044034441c00420400d00c2001181081d04401800004074408100180e030a5804010b0105202d04482c01010140e043d039400802403005d204078000030112282c0800d204040f181e152010b0807070064205001c0d4605c42710b008010740400c0ea020f5803154a011003658805200f42400074031416144c4600d6402e80c6840c482d2681078881c0c0d00c40c641003100030300900e861a078547c0000c01c0c0c901c1c1140d0002c10507505604100103038410701d51906050003001c0002a1268607100500010b103a100d98159542c1e07520340c80719504612584c01103a480d85c084102c5440d90700b280004c122404c088c1a078032 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 852888947 1250 852887697 852887719
    0x903101d0102070b0112150f0c170c0405010c1401020c0109031d012c031f0e06010e01090504080705162103050304060e03130f09050c1801080c1b010506 67
    0x110600b00d00c580781002e44820010001440315088064095494501c02c0000c1042d00050b000c080049076490702e0003141780f9449400900c1401e0b4801600d10b840b0034209290905401c25000341102413040c1c2c1f01e8941880322001c46074091000130b594119006800c08025551451100851402082c0001c0b013103012542c1846000201100040c400f9810340d8103840f503e080c080c646031034404280b10b00c0d01908044083c0b40030500031391400c0c0040e400000c0f009a0900611014540010035288031583c050540c0d406000100580a10881020b046803042400013681d40c40c0c50825025a1041b440702410b03d106c1c500c02546465045414041107840711108064005042c12444d580d40003030074809400108140085004100c85034861500c2c0400d5504880c505419010018445403047c0e2001e0003100c403601c1d0802c0502c0e0a03006055008014101c5189850b0041080e400000c0c0d50142c494104111040002d00900305030044907a40001d181034100300c0603034440d6080c003030a006c42d1164090840640 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 852890197 1250 852888947 852889001
    0x7180501050609040504060605121006090b0904110a030804030809040c0807050d0e0726100c1b0201020c061801020f01050408030103260418051e070e0105090310 71
    0x20496059600081002d85804151010403001d4000038105a402603540d02002074941c0d1030280c0c5510844454014100c140003d10402c4c0444203660301821005090083c95401907461002c1250312640c011200c02c0002c2608021408500c8260030003065040d00082c08024001031720041c1c138841804490a0003500300000e01100d0341e10003590200003082052041d0401041107130014459031104008840b41665140005034180100c96411100f13080302c0791040e0f54000041c0100400f62800000174800b11070107620052580c106002487d60182d8021103104c01c581c030a00400310921001003040f9222488451031401d0bd440d03948140c1c5c00351141c480901c1003601d040c020360f84981c0d042140503045a18603221010300341038841030b010703050703150344180a03c4034000c5d001342000e040c0c440c0701c003850480c803189200d04a90003c0c1170310001c0062444140c440c9010190400da0040c0303a480c00300c810900ca0001a519070041b40c024607818003d01200f5240340d0200c0d840040030002c1c11201c040c1c0c900380c0503 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 852891447 1250 852890197 852890201
    0xd0c0207030206091323040201180b09120102130b1b0114040206070807060207080d05060f0307060e01020106030804080c010f05030c04061b08272b020a050a080718 72
    0x72000940207001849942ca49141966041029004d14000840c01510504c3c04d8000074003040350345010100712005020540d40c1c007080d0041020764101e5441d01d0710b420301c8159400e5001c1d83d510300e44191074120300c1c0c82403054290151643c0c00035141c0003920060b1103540544170360b040034041d441e03181c101d21a140c554510500038000c0441b90203c0042c80b41e103a0340c090101a034440041520a8001000358900085a078402007180314001d01d1f43c2a140c5108041a13800d454016080d544078100081025090340d402161010440b81d00b4101f2501c400d074808010f0307000d0003480d4009846000081800108000042000e42c01c02409a807262101056240261f4150209442c02e1030500e005003c01e10015008624407000c0301075001019510031060307502c04072942e00c103c0f80004a10f07001c8900386900407030340c1074000401c0d02c00c980031b03101d81203407002524206e220010aa83c031303540300d94152401e540b140310700d240140a019124135030390350306c8521943ea80d0010f03120f614046d07845c1c01c103c034030044114 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 852892697 1250 852891447 852891449
    0xc0302040b030115030e060a06050901091406010c060e15040b222a1412030307020c01030b15040b0a02060108030702010903021011101d0105090c010809031903020d0c0207 75
    0x805100e509503404c05006500340844040c60500b81030b920710a00e094440c08001c018801c01401d900810458200303018001a61410b9005090035410551039144503020b42c44003035480364085c41c105220070164104000a443e10b00240c0d05a4091032485840c0081030f00c0615218074041c010101e0652280c0044070050301d0724400001d0900040804080003550110351700ca4030b003c0e034000144010ba02e03281c0f8032035503020580c030805442c5019907024132141801003001050042d800f025500711700d0300c6200a512042e465045604041c1c6d5548500c1c1503907a20032450700007031884c3c0241502d40e52110504000c90b4420030806e0058410b0100007d0100000802c46000c140d06a5480703844d00d2445c6d00303000000c50301407400c90900a100c1e10001c0c1b150400c100d850584c0040c00c001098039886100002c1401100c81d2710800964100420801c1018002480c6180800f0a20300380c2e00c60f5990300310450560040351510104c6008243e01c0a52082e0b054028100100210900300041100d1030310076aa13800317003 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 852893947 1250 852892697 852892709
    0x20a0615050303073c02040b2209061b0806010206012c090a020d0627020306040f2108011a030403020607030b03030d0f050109050105090c030f040f1211010c030204 72
    0x4200000c0000a403140b03074892030b01001481da0345e891464002c00d04400040400340540b150051a5141d080d482d16000c0d41107117030800e9400100c1c2614990301130f210801500e18525403151240850341c01c029295200030344800c500080702020300c040d0240149404019900a4018483c440011442c02c14244150110354240c410100078110720107400244070000811204107809803044000250b21001e900298451090b000025856040b440b884e01084c6142003036110315411b0414a001620001901d036001070b005442700042c0a524a0100c0444030040f41c03443d411502403410f10100b07038000150754180d44009242d0164240314885100b034a01017101c0244c01a0f000a0100390014000d91240107000c0d0050141da103401181160f40d02a40d503580000e8943c141e552004000d0100d89100c1c1501500c81125082241c0c201403202e5590f501026002040100c007170408642004000542801000d5101c1041141002c003a41d0207010070092000c0c1145550074005ca620f1072a129101325419540 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 852895197 1250 852893947 852893953
    0x50c190507170c010804112106070c0f020d061d0c0405010501030b10030b130606020f06131205160204060e1b0a0c0314130b040812090603010605090d020907020a06150503 75
    0x10026004441c82000648150ba88840d0a44441c040742c80312303010114201c4901d890030502c15081d0700054603124000b860345080152a40702040000c40020340e00c40401d4040701d01c82150009418220024040c0c1c1441c82788510700d1036844906404046240b10760710400300c50800540c2c2e80e8000550503904041440380c0c1c0b01c00717501d0700b039084c01e0b000354000d282c0902c1c00350140814080f55010321086540340d0b00210003607030204101160800e420000d0365800380d0b215a5040380120140d84034185244690841c4c8280304000c91501d00d02109141450b480c150010400e1200d140d540b2020b110a402c00c4d0b40e03c1440c1a503000840f40a031000301c044440f00c02013a920050840a20740302240d481210320103c41c203002003008000505000801014080e0184491180e606d40c94101e90625140d04204100900d01050080c0b900c1542c40f002a80d04640c0c090501560311000d01001910401001d980298000c0082c82032040c10790380010010070040c4610810461549050108004003407036115603a4554 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 852896447 1250 852895197 852895213
    0x10605090a020a031d030c1b061902010207050d09260304050103020903120304060605030f06010b1801020f07030303230115030c200607320901050c19050717 69
    0x10355034000c003ca9116803400107900744000318046184104065614001d84c00804c42280d0310b4000d1000100054041088110000d02d14010807000c0c025410120150300126000c8680725000790111094150700034113591400040d841c0203415000036000d98003c00d0144400038403e0459004000c040c580e01000940c1018944801180658001c1d04000d4050140c1c00d100b800c40c4043e1005140603504c0755501060705401c10b0181442d20a80002c045060b80c001c0d001008115803420444002d0803022800c074400000c0080180c1c071340300311303005034604a00c1600400814594154000844c8803070700c07002024800712a00d00240d20010a00a48110698441501c9080c40c0298001309403480141040710100c00b0848096038903201c2c0c0041d4003c0d540100c000c000b501507020500042040038480c40750340e000215208106c070300000410800080364000340f0701002da80031b001659003032031209003100c0038000c100c00d50301b4600d000e18004540c0b620480c4400300341d95000001602420a01d040284865 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 852897697 1250 852896447 852896461
    0x10b03070903021e220b030d0c06150b03070e030c010f170403230a0e0d0b0711070b04080304140d02090c070c050a061e181e1e06090801060509 63
    0x328524843c4d88545104107801c102c054449910a102d03854810f8540c21000001d90a804240c4507800f411500c0303508224401c94002c1c0e008020400456040341e00042e0038511405110400c00d0250826000401c011081107034440e800700580c6441402a0203440300300d500344005440d00c04842c0d5940010034284400c8003401d00c104050190f009019282c0140c24901c0810b0b0803984088466003042e698000040401ca000e4100c1c2140d00d441c00c081d0340030200c190807510b440c80702c880c025100c20100600c0c80085441c3c01400c02c2814060314003e21075640d105d40d5000d6541eaa40e106104a021500035501b65554525001c49042e1489401802d5286140e40b40c2c0b100d49040c0c1c2c00324004458000d454100400c658680b81d08032006461507403291640d00141c4040400000d00f00103c04041012040c00c0c040302c00d00107440d02c0115280d103100b2448280804841d0303c6a6081d60700822401801300c1c104a00403071900942804403001d81d29190080381d03c405006003030f80c42c80e00600c0c2e044880c3d00003203891 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 852898947 1250 852897697 852897709
    0xa0504031704050d0506010905010f03080a0f020c130e0c030601030308060105031f091410150e01050c0f0616020f03040501050901020c09070504080d0504082503120f08010b0307090302 81
    0x1904041c280400e1802c1d482d80c00041c140101203409540c1c940c000300040c043e0343c3c2d140c400c00c0e0140440306c21a4422510b195a140054030940442804102d0462282c94006000708000e440c00c40008102c8c03070440c203a10000c48010b1484081c084824894200202a00e04010030b0a9060300d07055a0780311103d5440c030300103480590000e41a010403c0b02e100c201c01400049810341005004030010118000e8a0b00d545c500180304060300c046441403a20303104004c01610400e003100d50b01c0c0d160805203207602354400103a8280c081d44044200c1400b4442d0a0242c256000c52000d00c902030001260904041445040b40d4901d466000c220b170540c8200010b211035800348000d04001c03a814411909903003448d00c040384d4024400d682400200780d001c11300f4008141c0902401c42c80034828074109060514250326140d440501a0180c102100c96080c209407000380628850003440d08010400100c401e42c8100403c000329800300b0400140182001090b0400c2210460740511031959030710b03c28501b160200305c2 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 852900197 1250 852898947 852898973
    0x15091b300319030626150a0b0d0507050306090d0c1719080a0b030c01080a0914030712030f060302060a030f0e100920011d030102070b0406050a0b060a050403 69
    0x409100600ca0040400d40b540c20100001120f42d0b004190140342178036541c0304141429400385070030120b200410784008006117242e444040707000b10301004d495a090100c01008502c01e102d0b080019182c0b0b41c41841000110781044540c29000c50303600c4d0740c62562041c2c071054802e407140c0002c1c041c0312070a00030552040d03407080940d1488035414981500008000328015021050307102107415a42080510f904621a807189400d058010f000c68440810000307001043c010a40b8000c643d030b0707801d40803e0255110390341041c50300c04d0080320703900c0b06181400c002c244481202440004e090100021080040d030084400700e81c1e0207040c0d81d0503d250304405030040c00041d120868219a01c4010742d20b00041040044103480301541c0004410b8814200040380c00c404109604500c8503a01c041e440590780071146500c4260803c203c01c00145454002901a1049010280c40340c0b25030014402403050a030b01190040000c4142004a00408070034410140182d28406021403801d110410120b400029004 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 852901447 1250 852900197 852900289
    0x9010e150402071a010803031e04050c0901082107021c02010e030d050a02010e03090105160c080105270c01020c040f0e030f2d0a0f0215091b 62
    0x550010304101080c100c0c0c000c04803e440c00526141e10541c440c100d024a54050300041014500e10b203040380d0081211614050704000b0078221200240a00c041407003000000c0c08020007204543d40d48441e043c0e595141000301c0c2c0c942e0664100100c03c4900250100c405180d406414100d481103030200e110380d9610b00c1d42d416410710008002044503070f81c0030b201001001e0519119244c807505108002421250900e0800e2140d80c003c014481302a80c0010a64207540d011804ad02e43d1400e0524080d0f4100645510100d115820a0280440400000364005803144408020742c0e178101c0850701e088d510002e82c1c05243c056049180e581c0c0e0141840d4001c020242c8040c10b01060f2040941d203043e18543c00120b41000e0301d1030105110742c00c200c00c0304004c80031749540104060024000302d65402248176401e01c0c1d406009092000020880c0280000250321000c021010f8a6103043c12140d40c450b0b9250b41a004c2d8014142c02020183c0390846e00041c10b01e05613010720f1030280e686202050007505000c911 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 852902697 1250 852901447 852901471
    0x715030207021807030b18041b17060412080412031a180a0c140d0f060b1b100614060d180804061e080417160309050f06040509010e 58
    0x3201c0943c40e8414812498100360740e544000d482c1440c0010201e6500081c22485441c030003450061030040503100c0b43e00660041d1904400c240000d244000180c2c00d0b43c40113141502c2295110785182000c2120340c030460113403c03503003c183d201007402c07107810743c3c1110001c3c1020b0341c289030034154611075031110b580c85025108480b450881c140c0000c107965410781c6094100d000d0b0200300070b107071012070080a01c1d441e100c0c00c0000c0e0596050b004065180142c08400e5100d0b965105502c40c6c04001e03400c52070041402007042550752036004030120708845070003000c0d0180d00c03401175401410221845694116401c00c030480000800c21070030800f1030b500002420554903140c25005400012080041c00068458210155654903246001e880c450721031b02120b45071084005002c08054100921692250713022541d54000109803101c03e4440c0156107000840101e959403070700403d508134039100203540041300e04400101d80301c000c0016500c2513014494128aa03640104032000784100043c1d0448901e601e4 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 852903947 1250 852902697 852902707
    0xc052d06040f09150b03070c0b13060c2622110603010b0705060a110703030b0102070b04180e0604020d080705011e05010312020105090d0f0207170c09150307150302 72
    0x820400700540d0441001c544e5243e8098241d1407065004100500d19264258298901804090aa19040d02000d060042c46c0300c002200010103511142005510078003c00c030310001740c44010030040449440c9000c03200c20a40c682903990706d6601c568421050702041502c4001142c01c0b8410400c0409070803100d01001d5a052091607840101641c0600300161100b0f40343c2c00b4605010f031518038003412110b1464982000080420b0741002115105505400c010808516034030040389406030540c814079101d4070100703000c1500b186400c2c0d01152004900828400d01c004040195100c0f40240d6000354007000000e8150001078540b00034250182c02540002140568810503059190f150404045440c2d0380e540103104110484454200340c10f003c1c40200f04d20700e8402c0c0c540d41e582507110f906000744000e22031201c0c8410f03c01c000c04d001400144100c10041d040e40c13085156600120b180c41c40c450745d040d0000503104400101d00208120009000746109440c3c1220180900e211510380e40c2055000c1107 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 852905197 1250 852903947 852903959
    0xf0d05160b070e1e1c05031201060e010f030b09270714010908010b0906060310032102010b0105070510180609031806091a21040b01030c052d0604 64
    0x6052150015443e03034007207114160f00f04075007008a40c40264940c21142c4071210325031900c10040700d0301c0d019400e1610503d1128100079156001d03240308800c00c058134400200345c07690301a101240381d900a03259901e254290390015400da582c0c1e00703d00f035080030420380002d4540c801101301d001038040300c6003c2d03400c050380540090708150803038100703140300100c40148480d0f550b0703c00e084070020900440200810001c1d00c0008201c10400340070527104120200c04190b101490340000030080d03622644108a43e00e2030506981c2400205841c0790140d488c01200d220554040c1c8100c540c030a40c85805003480803102c0400307e0060030604841c4d145203a030460040000b440c58401c20280900035110803560f640d6107580b000316810036030881410880000070411481d644c912020345004060710783c640c0c446c0d40c1814449403c1000c00000c19040c0b2004c02844144455100c865058030300480c000481103032a01c042c022035445440401114140f809215401a108251343c48c440d007000415044c035160b80d5072 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 852906447 1250 852905197 852905213
    0x9070512090a03090b09010c020d03030e0a150b03120d0905011e0509060610020705010e060d1b14070b010905060a03020604060921110603070306080625020f0d0516 72
    0x444061042d808540c0c0c00d000d1507007259581000741000f0341d200d4584030110000a0005501c90b00c028007034466840200d08041c001e80103408000700c040c044a0b1040c11a080030340c0101081040380007068502040c1c0152401c020406011040b052401140381000703070764a140050048800641c0c09550340c1030320a00401c00b0b20110203c1c0e00b00820045000d0508179009410101c014007900d00c103501c080000c00f0740a40104030501200d0003400c251000700c10310804a210392081120808c0d8452902c403000020342d030710040c5000d80006555070210f1119203280440c071700e403250382c4000d08204000c1004001a95007a00200d40c000406401c548002d9078984c040380160304244c0050b8045400548103001d0013618035802d00c120034401c011042c06070544d84a5824200c06c17440100d003e460000000381085020360040f400404c646001c6a402e49070542ca5070003110700c404021506a454403a0041c8024400100b030360601910f1005440100c3c050781c01503603654090210200110f0112001002090a403 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 852907697 1250 852906447 852906451
    0xf020409080a080a2a1103041710020304150b120f1b03120a03240b0702010314090d1b020d05070311060a052508031504110a0e09070512 60
    0x184015034442d12219005000c2c0000100800c1840749455203010100300010300b01c101001c444504505486122001111440101060425940300004002420301565421204a21a100c003511043c625801c640740a0340b10540d0041d14a001034070310300710150a603030f008080c01d890080401032004072540c1010700740501e0302d24601003508800d0540c0318106030420318a8089030110b028002255035941c41c02e2550003035030100c01c10543e5030280b41000390850030720680e050401e4a800d03185107664041e044070310361083c0c030700300d001038180500d00105c4603501d1052030103484524041c00314941c0c511011180401404254001840c81003001030258803401002c44a180c000d5001e00722207821410154900c0c44809a07040c00740c04104460f0010503405429603120803040010601c4044548030784040380f0f4000440500801c00010900410a20000d510350741000f060310103100c0c81d5560300c45c502050113000c3c042004958080410411071400c107400507031000160a2140c00d0960340b201c42c82c221101 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 852908947 1250 852907697 852907703
    0x8061003021c090c12020306041e1a0406110a0e0f01141209010513050303070807090510051801032009120307050607140304030e06070606031e11030d08040b040f020409 74
    0xb850a189083c0142008100040d1170360072100c5504209660100340d0314900103001500700c000f60700101004207511902d0702c81941d004140c00c102c0202d80d1030800e4850105031821074070a8982001514000886015036200e0022030f103070420a1060a028802038078907a0300c3c024104524410218808502ca00103421200000b10480119280107002c1a007102c001602400450b0500c0d414000015400004c80c6c1e40107609107800d0f809626220b00c00c1d5a1340d12560021507004010324020f400342640503002d410394a61900c24a0342080300000150100d0303c04048240c01900051900320060b440d00005100b2250040c1400240c400c8801001d81542c02c66403049850350801c10501c020310394080c20081c14140c1c140c079600d19504003a03401500800b8104152402220301107825400c1c455035034000340c021908940d002a07082140c034216920012143c80864800c1d4145400d03805a040008100f45826483e0310b80c1007164907661102c0d40d11007002442140c020000100041c0142c9960040080a40c8 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 852910197 1250 852908947 852908951
    0xb0a0c0908030307050a02010e010203061525080d140601080711030f040803090118050a05040c031b08011e08060a050903040f0902030402090f072007050a030c0504050c0a08061003021c 81
    0x250346c1002800e556035419016142d81c01801405501c0e510070229425000300450401e590b50304031103a401c40447c032030444085044100007400c00340064000100141c0d180310784100200341800f401c101002d20141d54880c0014072104c00901480d000e121480740d0245280e0840e030a041e40680010344c181d120390820690707600f0200d48074000c3c4d6041200003080f00300c3e0f199140c104504004c0440c040c071a0707921540f403045890781085100075010368011980494451200707901d04019000103801c40c00e003841104e0042c0e0820a002d1100d010404444003911149409400d480d10f8820002000d450302400e40d2455000c1000b0008010f60040c241500501c1644405a16841c050040000c1543d000b4107440b10202c00c0e0040120440e40580f840103203413000c02d1202094080c50008031b2525650b0b40001c0d80140030f0784070100c2480904240304085072001c4a0910140d034803503010b895640039001041c40801c00b068081085460301d6061100194014500141800d1111200441041c0c18a1249a60503 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 852911447 1250 852910197 852910207
    0xb0705030c0d1b030e06120a09020a06141b030417010606020d0311030f0403030605031203090c011b12050d06090911190303030504020f0315090d0c0b0a0c090803030705 74
    0x84040c0121488601c080c200205003005980c6510b264211903c4000e0810162a0003006030703035950000e1318904240095048100d10b0400300c3c0308010404c22070180d1140e8401000051103d04c031745440e10320013000314081800d00041c910801a40c1340300d012811002e02007800041080441640945182c448150020070a1482d1080113400d207007804c03040e4000c00d400c0072002d1102d428010100c94100c000000405510750312400c00300c0051503543c120315414055058900c41d0090213002960040381c6030001d99608400b00c10040d1150480300d81c102312400b8030030b01d100300030940c0805640001d15050034928904181000b0700c50864219400402c1842d560340c03209802d03c00810441200b00c41d0582c1d003d404240342c1850f260982e5401d11004040503160741c001411516840b940f03840c000390240c111603880f010041c0805801d40d04481000080c0f150000c0c408030036100b03008501e0390701c1c0c010a03050310a0315803030140000f8105840380708080c080e42ca800004d62000400007584500c600d552215107035 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 852912697 1250 852911447 852911467
    0x90c12040c090615052d0409090312060317180406030f1a190b120601090209120606010c02060d141f0f080304150c12080a0c020a03080711070b070503 66
    0x65501d90400386460f0081c2540a02c0390b40c000c4d0444a40b092806c51501d4032142a0f0248081c5028603040c50b4012200800d0004402c80d060704008940743c0b203a2100181c0c800384294072070451b12a4880074102008506102181c8107100006002c100d00c00040c00000c3e43c5404040790960710282c2c011184004640e401400780503814201e0000245140042a09420b00b1440c0111460401c1d04c0e0940b82580da900e8880203582d40280915994810016110550b07505d480440094006d1580da500560a104903c0b462174004038032184a800142c40d0b4444808080e004c2c04500c0d0050703001c003020103a6550342d0200c0002144001807140d50090082600f40e504550600c1031450250f01c038201d0840500740500100c03501100b27072340a0790710f80450a01c803240c24400803110401440300240c007000d503841206006c540c4c044c49140c4203400c5050180104080c190b0100da1b502d08100c0c020f070000740f45001090000344151041341c6501d0180003141c40d00c1b5156052016560f00c4003200300e450f5440002c0300058 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 852913947 1250 852912697 852912701
    0x30f0b100b0c0705040509190c0e090a0f06020d0f2a050a091401031b0e0a0f050d030309081e03040203060105101e02100612051203060f090c12040c09 66
    0x24186070381d50700b820721540c659442e6407111240202e40c4a99120400907900b46410485064400c20b039030554000390f08641805501d803c0386005038010000391100080c1d03945c9000507148011580300000040c803892940b1030398001c0d00311458400e8500d44800d8890820a244c0c001d4061903c811150f5035100b080c036810f1025208209a281401c0c044180446000c3c260084492003c4800c0e200045018001c13180048006007107081c407100c52190f040c0c5541610365032004900040041c2554050408d544170040200111218030070170303a01030b0380343c03811000080c072981060000b180716642090130400a0400581c40c4d03c2e000052085150011040200b5842d08001c2580144070556030000800581d0a00501c41002108010308009103603041d051060300c00c00505440c0700b0b041c5010401103840d0902c1041008244100343c4407403144213445048800c440040728064800200b41036407490b400c2c000c0c480c5181d0b00400c061300c0740c00d05010f0307200c1030001001c011341318a00c03d950581c80e084c10708500c881 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 852915197 1250 852913947 852913949
    0x32703130e0108120f09060c06070e030615010513170a0c0506070c050616021825020303060d02060918010e070e060a05161b170105220c030f0b10 64
    0x40120640c0d80100720101d0042209550243e4681d84c2c159101d21110b101e00c801d202e03641c2c825030003000c0000c1c1c181c26040302065503402401b442d901c0386007442c160020076503910b100369a034088a41d80d5684009175036004400401981590001190701d80e940c1c7c0c060380b80c20441020b100440c83d00204481d10400c032106200e00043c0c1021280d40b81445042d86550302c000e00c582c0038281c02040d0009100c01c01c4650140c0d082d603d290b0082c50350300104003915520082d04000c0d44c0c03000300804c0c04986841e1850494005082e0401103900071415036a9038001c03c00e21103a2401c09a070081020005040e5684a40d40a40b000300c050400c40070041d40350070030b00c81290100905107020401d40000341c1d0065904c25084614140f40c510b08607440742c58402e45400805a03005008080c071000210308000060b103801484202c880c0d40d04c0d264402c54141c10841d00741d40c0200c0d4405098000d80c8440f00b0800d402001f00240f040c0140d81c000744075602c9548904060709211420b940c040e40d0913040218030300070051418 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 852916447 1250 852915197 852915209
    0x100f0c020f160902070206040f09020d230c0f071709030d0206010605120604060e040302012412021002150a0b091b030f09120a080f010b040b03040803270313 69
    0xc0e08840d440750381c042c501c00ca4002c0003a110b80000c0c1040a41da02d002c00c0c1c4010300002c5030041070301c9a441024a009500180091181034100740d40720200d8035000b030007411a150b450b0407009480d07644c81d807644003941c01301ca1081d540a80034424140804e18032212010a0140b800344280e0fa42d44010070503180c1100074101030115130109005004603131740311013a1800140340d004608c1043c2c0b41c100003c2c1c00303041c080d0000d581c1c46102a0400092650540207020394250414010710361a030801007110b100b071001d000380c0510706054012a4014249940e00b003d803961644182c0d90800c5969071a509444800c1c3d44581c40c0a4641c48030b0a1103151182c0016000256400c5482a20f0300d545480d26441c000203240d07141d010000c0e000100c1180c0c040c040400d410440c0001d555480c080d51501511031a400e4a0300614420b401c03001241080304282200c003600d11401c0305508658440e81d03049030b44c0e400103080c4055035440c00c40103040b0312480050440f08003035480c041c58582e00d100740c0c01700b07104680e64481 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 852917697 1250 852916447 852916453
    0xf21060303030108070b070501020f0c01150801020313020f0a09050403110f2a0f1c0606050d0203060c0d1116110d080a030908040b0d020c070b070b18100f0c020f 71
    0x401084800160400c100c6d0179441c1c2040c0c90b20f0003400c100e402400344905940f442600040c0e00d40300503406502c40d040c2002c1c200c04004609445074002401c0380411030f07039004000c01c490744075000352600c486228074801d0010109800c05440354141c80903a401074504501060101140d44101c40d0b00740f01c10180c1c460f02400030304103e4540410588101003251800c01d40c00040641d031b600340d440d08044a944d44201520b01c12010341d0072055881d002d480041709498061500d00082018501240700a46207500100100307001e85808869406036406007400701040e075580d98524018000d06000340142902900301d003003040c1141d045c22121a01c4031064541304420b1401c030000014440d0054079400100ea03d0001a015030320314107800d0f03034420380d000024101c1011804202c0d044103a00109045410402640d5800d560713480014814015600300400700800e00703000035100d044142110b040300c440d0404480b50034a04d1004003003152901041e4034541c940f203503260b81c05560100b00f00c5a80392843c09c01 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 852918947 1250 852917697 852917699
    0x80a0c02090c0a0207030b04030c060c120c03090c0b37110a02090703050a0b04050a0204090608070b040b07032010060605040e190e0316050105010b0c03070303110f210603030301 78
    0x100940395400c0340002070087d0706038004981450301ca803402c03200041d88207000b00b0a280300d80502408041c141100f10300e0b000c0c204807035600201d02c280900718101d640084514940e500703100400700507801900a500480d00d6901403080903c000c08540a060559511841e07559080e040c802040c0356501ca200d001c4550001801c80d0040e00e80920b52070b4001124034000072140c807030a040102512030071026580c01802c1005014141009074010011601ca000d01080710319900c802c1503480c0d0129100705440d50700103100400c944600500103040040c824076003021070f40e43c26030548c41c180c1580c000c01c1d04d4a500c043c0f85c95200d00943e1084602170201400c1c1542818035107200310b09414002021881c204032444014108104103030480303401840c070102602c0d19007a00c01903101150030305c1a41607420758242030001035101003400854082c0716404003d103281000c1c81d182030f406050001018029100108030801c0a02a248050980c0f0055503c012494400501d210380303041d00046d160314420341003040 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 852920197 1250 852918947 852918967
    0x81012031b0309080f07051905010801030f060908030c070c08011a010e030111160b0709050a03020405150a090f05011e030b1015080106032f070f080a0c02090c 70
    0x10990515040101c110304034105914044908008a40c4148018803a40038071400035a008a070000a5407000d5840c2d00c103a034031843c02c104183d031817807103824085055400144045080c2c030201c1c010f0346010b50030100c0ca102140d84c8000c0c05600c1100c04070960807000c2604d0080040138006480200a108001d0103a6101050480710603c1d043d250903051000c1d02d80e400c6015242034000110300360888030010b854184100c0d501c030030b9140809088984400460006198034040c00489069420140c016000181954240001814050107017100140203021003809644c8100301c040c064a11070310041000607110760310f50162101178000d810790514108800c1041001045d8850850750414070186032901c925500a604849542040e00303200307403449940100c5a080200c86040325050f580400803161001c21740c441c4203081244000e0f400012480201915424038060602c0a010305070011000c07450b03586201d51580103801103c0464881c002403003c0d89450321145a0007585203003c0c03490034030030007 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 852921447 1250 852920197 852920207
    0x1806140a08121c06034b050f07080c01030612110f011e2a02010c060b0103020f0c163618050609070909080d050601021c08101203 57
    0x200c2582c0301604041403c00006410480140040031200b034204400b50300d90070000f05104584c000c04034040315001525490b0f2030743d0240030a1401d605501c01103441220b900f0007080c02d030401010703a42d500c1501c00140d00749405000110081c0840c0d00140958552600090300f621110b078890303c203d12881c400203010884452240100318000c645103010008042c2c01a144100c119420f079042d0010503c0c00c181d030580000405200070380c0b03c0d021001d4000d140f0410400d012407620028009180b00280400080036900301000345c2105050140c00d00318903003212000c1e0341060141d158107034848102071450180d4100648043d100c058409526039411000414540b0104840000d000700b002c0c0214902c100903a011103000c90101000c454070000d10b0906a035224030507101c0311103d0084110000d6024840c0c81110720040e4050800c9043c845405106001400001c2140e810f6011308402d0f03c021040c04986d80c1c441e900242c59104047c14405c20450070312004e501300c0ca480d940408003180c080b0f9001 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 852922697 1250 852921447 852921463
    0x3061809300f160b01090b040f020a05120411030d050301150801060912030306031a15030c130e0a0602032a090d0f0c0306050702030408010f050708160302041806140a08 74
    0x8150740e565044055500c2c5000b0143c0c00001d00040c40c1c240000c00d0198058000313095017101107405111000113146088200e118010511012a00402820304150079106130b4a501a009011400c510303011000401d05000c080c5245200240002006010800c02c680864001d2191460442c599605100d4058490341d4140a09220040300d05a50400c15119800200203168000d903040403c000c542d200240100b01a142c1c0200060001c00303001c01c2c1e00f000690340c1c140c1080203000c400b4040c1d030400c140c401080c8086000035240107040ea244042102400218014040707400190703c01e045101030000400001e841c2503000200800c11051180e440c10000980c4503001060812440c0303080c0f424101ca0342240e84020700f89800c0c50304201c110758011024108907a2128024084444000540812030b00101c40e41000709a0b070201207200440364404408050300f113400d00611301a142c00441c0c079445081e106800415841e180c05118841d0744119024043d482541c0000019083c880c01b0358885100c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 852923947 1250 852922697 852922717
    0x41e14180a020c0d120b0d0804051002030c010e0606011403040503030c160f050105090d050f040b1e040e011809052e151a030106080c0306180930 64
    0x40401280c95480141c2c1294509600a011075030301e46101e040103000814400ca40c0781c041407030184420f445042034459104019845009545050700b0641080250300500210408500c1b007444500581130092040c4030000c03680350002d08442c0b0b04100010022042e03030407141d608140610520001840000a82c0e40050341001c05903101e8031070510292441c0c18558014080007440301d209400d201c01035004600480102c400d5408112200360150b815104062418101400c10481000760200311b0001e07140308038040a00325080310740000c01049580254005809c0f5400c25001005051000e1407108000d940041090010b0321890b220240c407041100c443d007404603140e55540c03111041b07041c0360010004131248100540036040403614140302c2a40507154016409a90f003044030060441942d040728400e0b035491090380d0390340080080c541c2025041c203400442320294070000c0380304820340303520680000004017050f0f00922100341c6400c200c0e6480c407034400ba402161042d544070301c00849594500b = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 852925197 1250 852923947 852923989
    0xf0d0f0e0d0f0318050604050a03150209060301030503090405012c07050405031006050a09090210030f0f050412120605101808011803090b090109090b040b06041e14 72
    0x60300c0004103091010010008200001250907a070030903422400e001500c40150302149022a150800d00000703105a010b41039001c1400c480400029103208030041240e103522101609140706403000c1046504280c00032203003030300040381c0e5115a0a1a205141c01810b010748407403001c9008030414817102d000c0180104a0702c021000007241207028001300c600600010381203507482c0140610040042ca0307240101d5100b41d03100480001d015a80b4002e805000303800409202c08040c05000c142d00414059440644143d121a02070140c0038003481110f11440c000c410403030034100319183c000e1171225900607484410b0b2034000c3c14880d5403140c04008117001e200342090390851a552400001c482010750103400c0e90740c24a030103003195000799154443c06038442d884080c462610360004095a00580110a0000d50041c904000152885d004180c0e500340140000414081010104e07002c0d034040e42201030628689407180c440c590700402d2800013040010011400b284020000500c03600c003030301c0e880352521 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 852926447 1250 852925197 852925217
    0x2121821190306080d0201021b03040302032a130902031e072106020c0a03090e0415050c07061b1202030609060405091e16090c080403120f0f05090f0d0f 67
    0x10b0003544840b000c0c0101390101c0e0000c06200d24001d01035884440c0c01e40c0811f0035500c4030b407840d02c0004242d50580e5401000303098190001c07c42c0c101000580701c4910f010001c503040c9112240c50b02880c1f61801100d0b00d030080341952150060500e0802e040b85c800d00800d4080301100790307550020542d01c0c00d0340c04204e0749001c2e040da904c3e10a004a03030f035944003074652440060078002c1f1103000100386038a28030903140c841c40d1603a42c516a10348918100c8001c0c1101c1d001c0c403515040300326680c0c440d540c018481d0f004242003070881c2e158841210481d0030720081c84005281c4400ca680e42140d0280031030381c2481ca065165103800340210318402d80c0038050602a07512200840c1c0100010302540d011200d6800302002d180c03007080780341c1d03995941c1c00203989140c405003180420002941d02424200448903200d81c940c0b510b40350b5040328980e080143d5030781d440395101c0c00001883c4060250300c0648819000101d26030803e400641e00740b00003580310102546c0310181c00780c01079030010060480924141070490b485 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 852927697 1250 852926447 852926497
    0x903020913080c0601050a0e131b2c060a0b0f0a0918090b070305040b1503120d0b0406050102150f1e07051207090f03021302121821 58
    0x420380030381c802080054003141c540c070701450018010f8100c4008480c0f8610950fa038030a081040f031070940300d00da02a0300413460000420b0300e020925520710352b00e03405807029640c0e9902003a106000c41901c121204c44e03000d60b214004800d20311640d0405003c94510b49864176016900c40244035090109001000104112050030f008000a2006040406c1e07071103113049a0342d45160040c00c03005001c485400b004030120342c00e60710a100303661203907921011041d6581c4800c034080030031021003001c1039454482c954959070841005405480101e4203140c0126480026174100030598955030032030b034110341c00501c0c4815200b08003421550800d21428031003040d600d031081d40b61880d0110403d00c1420a0100050041c1942d001000709007403100c49510248544030150112600c50503807103802243c80b070020041c00035141002039051a400c07501d000501c0c0400256604041080440d0a101b410080740448440880c0521100701d01d024003541c84007000d4007600401185018070600421854652a564110 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 852928947 1250 852927697 852927721
    0x3030b0a0503030f07061a0603010509040f05100b09010b130e04030905040216202209051c020607020606011e0201091a011509030206070212120703020d0e030a0309030209 75
    0x141c40e01809496035514a003000020a50161030112038903407901c000b0058100340c7c54201c0f54a0b040040c81c45107144d19001c200460403101a0080e6004c42c0d0362030440001800400809268901c0154081010844001004420301c416400380c41159420003501d0382085810300ca00c010344410f0b070414500c40e00c880c1422251001c80303400007500240b00241e00074401c02000b0401c40b140703101c2c201000c006030300751140e54600c4881c040806d0301f140605c8800c080d8400040035160480c14008000a200c0085031125440c1902051010340701d100c1c0a12803211080c1d0620071690700c40160b0004020a041410008060200704a00039105101034010740c0310032403017034010200d103503000945e01500442010380100c0100c000e105080d00d5401d00400b00800038084c00c080c0d0300b2030360000d10300d03400c1a43d02d130280178801031a801c40000074058850107030001042e01d07010340700a078060f03030080c00b542540500c00b03420310f044035161600c81d81c0010f055900081e8000d040c00c060342c1d410b039818140d03500d80c0c01d91000 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 852930197 1250 852928947 852928949
    0x10203126306090304090b060a08010303210219020114010e2805070225050105180a080312240907110705100c1104090b04170d0203090102090f06031303030b0a 70
    0x41c1401248140311442600001510075a46400c404201c0c80d80ca1004102c254420100c8910100e440e1000400100c1d00030006500c4480754250300c1c00b05000780d61f0102080b81c0c8000b54018005080040320b00800ba424400d10858800144040d8420350400c40c006130300140003090102c1d041a001c400411140c0c8401040c4404040f00d0400d01184c10a002c0194980441c0039000a400d07008031904054645240c844004407401a1601072401d20401c0e0a110311000d16210903802198801c000513040404000801c1c070000140c100100c1030600c680c489603248810100e10340101c114004c2641c00350b42c0c0312000c40c0c200d03a10b070a20034418804e400d000c0303003044c0c00c1d13610083c0e10043e01a1a4402c45030014414100f980c482c1c292550300108010400c03049a80040018019600c000001b038001a00440803068003a40c0c09400c13400c01c0c00c0c020209051740e0040380c802050b650042518002400d100c1d03060181c0c00403c85605045150200c100e0701c070b603420700c0d90103002c040e10b498031000c05490f002e074410 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 852931447 1250 852930197 852930391
    0x50309060d0b03060606180409060b0604120b100513020c070915030203430e010f03050d0206010302011d041103090f0d21020901020312 60
    0x95152070354070701c07000001c1c51000011406070140b400040c0c50f62520320111600c402c6003500c20099507005806000c01420142d00031590617a54180300c0410350358101c080c0c0020071038903243c1010071501d45000c480d0084083d2603002000c900341801e100d50741c0c991001c110340141100c0010380741c50248e10781380e00c0c02029034005034065207010081e500099101c401641641c6c000d900701c449444225072242a0700001003c0ca440c0c40105c0315404d24142c4005c02005180300740b403490260000d8a40f600011300501c01c0e0300c800304070701c17203000300300b04002003804820700030300050001e820150724503000a0725141c40c000702560039080700c0340005e0040c0e40d00c0d4445444900306040d03840e164501b110046580d00b101520882061181107144420607114108480c00550400e00400103140c00c042c48074040c2d0410340806040d40401d224070303042c41150140c050320601048052034015640c40362040310f9440c07000d0b110040e03410008891a00c80d03151b009150042070020320440100c4111280c20628551100303c04 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 852932697 1250 852931447 852931459
    0x605041b030b1e0105100e01121b030e010e1b0a091107060b0a0312081005040504051509190f06090f120305070c02030607030f0b030307151d0316050309 67
    0x2100b800707502a8210b00c00c004500140745501c085102d4286030000034402d050b401441100c4010600e4801d207899103141c40107041100718144640440c5050f2803a6401ca4021002004400708605c1d070b16001f0401c48814400023008421003001410303413110b242085550b501c20a55001010300d856060119000300110b480400500304e100c400c05005078808101943d001d41002440340781d0307140c0040d0034821650300a8600f4012020601d0030b90f00c501004040e0000a420000b000034181c50301d00900303120711b02c078002a100355814500c4040101343d0151409590b940b0402c1d518803d0240110030311071068011851542c0981d4500d0720b035010305941000100300e18000c0302c0440400010310b030b802c020701e81203450600c40c540c3c6481045031218202100a545a400f03240458030240c043e034040450103061500200b0110318100100b46103901030f04049890583d207440f181100a464402d601e4841d0407401240381280d101d4035000c0e03407070080c0c0b9842c0302c803008000c0400082050400440d9245003000e094 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 852933947 1250 852932697 852932699
    0x225080312100f051806010203070b07210e1902130c1101060603020702100f030e0607110705030f0a171e030103140a0209011a0405040e0304060207060e0105070605041b 74
    0x46007480207854409810000c1100880c2c1e00a100b8a40c07000d4a0300038069222411100d90980904007004c0c0105065000410640d40030414a4008030301c01c0ba2641c0f03506500100d011407014494000380c200d82c00451610b481c4282c0008080b69000682040c84440202c0002900000f0346201c04400f101c0c024038988041c0c1640c043e00b04c0c04505a0703d40c01002080380c0303aa07807181902031307200302c810003944811018414854030f40a1640714510043c1c0e803800041d1603207805c031500c0c5407100a440c904040f0b030707900c01c0d1000003040811450f00605015000303000034001300c0e6002c6950311130224000b4064040020031400800c1b105003603440080c00c003080050070a800303440301c0310300e5802800161188182542d1804883c10002200030919502500300c08050b842c150360320fa0100c3c800303914040342071401c01001600783d072507008511103480e036200a035a075203140500203460929075134400c0c801d103c0d4039889444282c1e007080c240c3c1c100d541c101c84040b40e1030307a0f285008648907842da14500d04140711414 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 852935197 1250 852933947 852933967
    0xe070b0c010e0601060c0521090103020c0c0a0b030907060c0b0705030414010c0c020f100c2d0b07020c010903032f0d0306090b01113016050d030c02250803 68
    0xd0348060b1b103005506558001200880ea86c42103011140c003441080030421814500354841d034028445590366070161181c2c1030103540050103241d80d5078040d0000c14004018000110b80c01e1081d02d005004604100d66203813003581c0c400c0502c03200200310b0030030300c0b1001c00007506011203c2d80c0750030700c54404002004050202a0b001c1c0c1001c000501c10783c041c1c03510181a0b1218103000040440c0c5151503100c580e103020180d0340303400791144065880040b82d14070b09000c02c850300c0e0200030840903e10035545030300d05103000381b4024600300300010380c241040000d03001000484d411151052019052381c44ca132400201d500161203041d005400d224005128144185428a9059000b81c003500c00140040c407030075103500011100030070360000c604c0075030300180f46004e030700c440220340c0e403100702a09400c0c00d007202510809501d080e0080f00303100034034201d041007a0f03042000a110000c2019094103040018180395000295070700750104040c01c10384102c1e964a21100c10040b4400c00501201007100c0c0c1d1039030911 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 852936447 1250 852935197 852935207
    0x5150c0c040c052517120a0f0b03010f091109070c080705010914010507111606030506150f04030309081209040b0d14160506210a0209100e01020607030e070b0c010e060106 75
    0x840070b4417980c1d8407411003034002c3c0d20a03045942c0e40e1001c00d0324035815111201544c005110001d0401c860550782e0090000d81e89080c090f20400c2006030a0003d4a1842424030501410807071036098820902441001640c541080c15681040d130414000c07922600d161803e81d00601800501401b480f03468442c4410a000541210344a5201592902a0780e00008101c907910400554100052070540509100c044d2090b80100d074800c00080c00e0b0b0170562104440d00e03026a204904020300c404c00041c05006141e0024810402003e280000b0032282c020f01041441c14090b48141600c80d544030129840340d50b0714a07a482e10322541008940b01c0a07128540c0c5160344a0040b1b81d55900030071548000103c5140c95400e0394045005c1c5802d0020440030340480c0320302410018504860261300b4030000802d9100c00d0184544511036441d9014003040000019140c500e000b03049404040c10844408002c01c8080b4000d412520106405505d4042000000f40904501407003000b41e48508800028413035405 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 852937697 1250 852936447 852936517
    0xd111614030c0301090c09110415020c09010609030b0c0703030e12090f06030610050f04080a0602041a3c190806010f02060112060f0f0605150c0c040c05 67
    0x48003218501c10741c900034036085e18460080a400701208100810028a072904444244460140c005d4582500e916a41240c1402d8100210059000d800d1599071400d00c8050540074055500b03100b090030b440c59842d000d1038400108000c480300c00c00305000042502940200c11030082e204260b95103900440e20941e01c80d00700d01c40c030350710030800c4618070742e000d0504004513402604080c040d05e56080101400b07803803540c480450042802410400054600801d0001150380c910901000d691185000c10820b03c0341014280302000d42c904005485190f0019030303444045020240c1041c0d540300d61440745241d0704041c040b00252040c0005107441c421034003e109a4000d0340c0c0c40e15000c916031568001100c00c0399041c0c80305405640882c005020b4800803055200d0064410180883d048007495103040c144c3e888111107010458a0703801c1400503290482d0081d0551224420550812a2007418250380f0759100010314000d0360340311001d17110113104d003081341d11091540c3c802c070f9454000c407018001e2324450 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 852938947 1250 852937697 852937699
    0x20f21040501050c0a021510030b0a051902031e0c0f040905040b090a050d030b15040612052203080408092d040203070c0b09151602100507020d111614 66
    0x2030000081c0b229404c4800b80c4044c94150707401007010001d01e1942c2c80c065100680020b00d5090310000010009288618240c451012420086900e05060082213503090300c40c48031100c858011300800401c1000c160400c200000f000800e2041c5489405040246202d0b480800d822400c1c009008500810550000d0780500d00c01c450030103041c2d0740e030341e0440c1d21964511001000c9401100e10500c48c64400e41041da80e03000018018a04d0303400d12921480d46900030303402103001c41c800200e03981916181d4807902d03500c64076440410880402c2c0300d41e020f050041581000302407140c44d6001ca0706100101064800c030302e0001d005040440c0b0040b00100c002818001544d08000e4205d0a02e010740c2054001d480c0582d1441c1c4074440c1a000580d40ca804401d40148603181c5446907018403804a0303c03070301110340030394141800151617184072000242000312110904511600340400c4c400c58981c009012409403c0c0ea1034000800c2e2844541c0c0da04004607007000281c00c4003061004540d0350300b5a0001c00003080 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 852940197 1250 852938947 852938951
    0x50a0e010f1a0402130b28170601211104030c0b070c0605070203070320100f0908070b030105040c023306030c030a14160b070204150e0a020f21040501 66
    0xd04082000380c0c8110008171601003821101040340e07440344030240c85d0320030007001e070f00600303d600b54128034440008425100000b1050140080103c4808541c1d40d0444000c0c07030407070401140c0b0a4441c4541960b141440c14285d40c880d00130800035200f00035200515070048420a0044da41c0c40412060340100e24255030201041c2c10000700c1900071400c1ba440f142e03001d00541441495a103585180022406041c0c12007081c0030644050342d40d80307400d00f0290003080d03103c041002c5620080280140a603030048051a031103c50b050001503c603005607411107000300c1e00420006d6000d00224241000038801d4140e8454076500d14140d904600851202290100071481542d501d000425560382820010b00703030540c10110100f401b080c086a84544445e04080c1100c0c0c5c40c800f4480041c00f0034003980e20a90380c11102080b50380440c505401580307000381c0340a0f584007006081c5083d99042031070103800702d00303042d42c00101c8440d1907150f60107860342c00548054007404450180200c40d100901118120b0b0154 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 852941447 1250 852940197 852940241
    0x231050a0f0e0906090d0819021207030e010b01051909030f031d15030415020f0706050604110a080f06400c0203070f05010e01090807060501050a06050d050a0e010f 72
    0x9000101320380728944a50060403881d640200a540051006e804800181d000d0421035403220064001007111008142281e8118980010000d080381c510080c8895103034180b014060045ea848002e17203c4e015229a000e1f0008840103105075004070a0354002044400c0c403020010505030440540070400040c003800502d012409010495400c100100340040f0341410720108010400300e00705c510300100c102c24014030702142480401c1180e04202011204a07845000b000070728245400386141d04201890214140341c2520800b9000b004000c2803080041c1812000803003963300e200030200b03105182e100001c0700380d10154111120594000e4041a5001d141e9003910b5400b219120f414100b140c550701650a20000750340303004500e05030440684840d074a404804129410a00c0761511444c801e008441e80c4018603c0c01600b51501648528403402100004000603074102084605075000c0d900001059074030241000010401d003500d04440350b207089120500c100c02a40802d8041625000c440406 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 852942697 1250 852941447 852941461
    0xb09040f110720150a0207030212010902030c041512150c090e0f07051c1409061b0c19031101050708061905060702040903050c0d090302040b040231050a0f0e 69
    0x7005903c459800425040b44941c14000c030710043d090803901d520580340c44590742c1d000200030000304050074072141d643c0c1c5807080442c49c0801c0361400c2c54000b6241400101c141d8418050844000d01c185085840984508410040310801e2000340c03110b0450100030619560400403d01c4029008200c90301e803500c004190f01e0b000702c07083c1c1d034429252540d4040ca00280b08250075040c440c002507001201e40c403512100f01a10b00900071910401c20a4001e08540c5054038010810705d01080c1c0d00840c02404001911100901140c1c5210502d100d0034440c2c403500c4a80360464041036a00d441d4003041d4600800d2111503030340901c205005040071116005007a1425440c0f000954461241c1c03640141c3c10450040181072070303040300d80f8541c000c1c1441404c21100c1148207040400314100880003580c10101401103140c14840e6042c4100d0a8038118201181c24152108800c446448486070b400c00c40704d076001c0d0b1040914000302400e0003030302c4019103681e220030040031482c517802141100c0c0841000541c00b = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 852943947 1250 852942697 852942743
    0x108061819020415050301020c03090a0f06050301120f0501090b16050c061324050105180f1b09040c02031306021903030905030f0309100b03070f0b09040f1107 70
    0x10041403074048002240e4941d08000080c041c50300142c00c00c904260000a0f0380e9400c0c4054184041040041c0d40e6900c905000c200300e421180c0c2007202503408403401440400e074070030181c9055600b04442c003805040c241c02c01820b1192200d00042540d8285500041000b100b8403100d40200024280007240e03486012064540c2d019040e40d4600a07072060340010000416a100700320064040c2401c3d40911243c000e0b5040b02030800c5050b030201c10f03118030040116040ca140308802035a0340d0800e50140b81020f0307981c1031006102410045003a820309041041c0c041c00c0307204032000804002c3c010480f80c0485000a5141e4110f08254001d501e004100051075600225681e05484100c140a1080c40900e5500f40c004120089003500c01d4442440388107003403001e10340154000c1d50078200521400d0300d00000841626186d1291601917004600100040c50100d8401015104000245a1201c0c015008100180360188000149a04101002006c654101c0090100900441110303030800009804104 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 852945197 1250 852943947 852943963
    0x50603010812091906021f06030803012d15080a090c15030603060903050c060a0c02120a020c040f0e100c0203030a050402040b03070806160801030f080c10020301080618 74
    0x1146400040010b425010800002c185002000f00040303800042078502e100b00701c0e40f64100001607804070382907a44405550362040304001c0200420310060707045a8410040340018032591802e200040007824004c100501d2080140342c000d180c0c00150f039951920365060428091081021401c01400304004140301e000714103440390400d00048009140c40003403015010b289140108040d560310300070000520a01807070000500a95440c0d40b203001380040c0c40d0078842c1c0135218400c880e00d0080111400d82e0041119806d50300c486940a840350b0030b0840903424201d1182c110355026240c40b04030350301c4270920740c0541121101c5000b11640c00084603d014221303080c03808503901607030042c000101004a19080658018400707000400c1c0d180c800070100c1e10384021900041d14a8101104111341651044641011022280303814186545161600f140d10211044040c2c088440000c00d85140340c010401051814220b89045580390b039142400d640380c000c1a104850301c00d43c0c01c4040c0102c6100040c2c00d0b4 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 852946447 1250 852945197 852945209
    0x6091f23101815120305040306090302070e0603031303150e060117010b15030141010813031b0501110c15070503010302011d030c060d0510120b010b0c1207061505060301 74
    0xc40c2c860f0800f18a080d013038904910490410008010100010380c443c081c41500a1098000f4500c2da4200f01c650041120010040c80c000c0d8002c1c4880711012000302002400c60707030842450105400d21103240406025070382c14019441c0b084c4400052000b988200500e40d5810301002084251030f5681008000181100340342c807100010300050107001018040302c0c036003c10304004449080b604140d0041d078000381601000c0c0503011860005a2543c01c1402e03164400d001c0ca80010a04200d55005803115020340c5031080c1c060119009102048025848200c10203005441a5105c220642c002c6035a06c01240d0480823240401010944039170141c0701350707416070b541610307002900c4090780811040503408043d070503450702c00c007030264541b03840704002440042e051802c04100c07850482003080380d03403015501c040d02c0d0801040010700030500302c038103090564102c41030b416640c035490840145071402d02c105140030f61100181100401ca0b8660210400c00c8207032580071981e6959800304101408240709203 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 852947697 1250 852946447 852946481
    0xf010603140610080607110c121b0919051e090d121407031802060301060c0501051005090708070e0a091407030c020c2205010b0c06091f231018 63
    0x10808003406451f500340030320840e20441e00134048820004101c1001460980140c0c2c0180e2400e0701801081d10000300c1c400000c1d9500055402d009440d42e1031000c105d080549516a0b950104d8180d0014000d0028108803010310541c082c2880005151121403a40031280491a0302081c0380d1f07090f03854022650840760364069a42160b0750420158054250103010140403404c04008400590700d20000c0c40c060005560b44001002c3e5601d407190031a2005894a18012a185410412543c4940e1525440070440c9402069915624000c1c0d5070001c07002c6100e540082101e00108105005610225441090b0500ea203600e48035103c4c103a0803141c2c84101300006030002c82a2038428180003c00d110700c500401440c25038580c000c4078020498000fa00301d0500103000140b000341c0041e003045034981000081d4042c00346000d4420311403082090a130301a11000b5120903801740e00451f040c0100000c90048000c090040c03820100580d503000341c0c2d0080070b01180b1a4581d2620116252080003005140e10181e = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 852948947 1250 852947697 852947701
    0xa030e060a051309020c0c0411041e03050613151404021504050a030c05040608030424030603060905010506091608010e0a090f0b15150a0305090f0106031406100806 72
    0x34080998004006402441020042200042c403103008070401004410380060f107841004070068281701c401c250540c407030b81c10071609541c80b40245d0200c0d400c8901081160300341a4402d107d0a4031218140d2001c0c146004031810003003c01110089440070b180314061040840c0c41c50015281101c0c01000d580000340f4032400080c0060804503403c6165600d008407450a03c0e030b03144001001c0415541040b5100304d124003081003141483d0081c2e03006003c110300914180b40c242080309403018101030388d444400c0417400120031800d010394003000281d03070842d505000c2811103050081c060701041c0c540901941042000403402802c185541400200c280d0f076050080c1d00c2c00c000b84210340c101030000060955035038208000035a1018600000d54440e244c100e0180c0b4103400d18000c0100c0240d0083c1c010301200c0c075028498a582411200d0100903801c000455450322225a498149084045080c6610b0030303e000c0b082c00000c1007800c06c20f500c4070086030750b55a140328056502e000c441c4070b007030030541c40880 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 852950197 1250 852948947 852948949
    0x703153c050a020c0f07151e030b01120207080903070b0a0f08091c0207060f02160510020703150f05060d0c2303030f030a0c020d0906031d150708090a030e 68
    0x1c219006119900090700300710340300b0030560030324040740250081680444000c1184841c0701a80b46626012824140ca0380d02400128217102444d810300b241c109a03940b40c0c0d80516a006402842e0350f181c20090441d1900f42d146804a0640c0c400030540e4413034407401d0742c00a80096003104807003007040140c1c1c9042250320f4585099920000c064044040b60285030740c4100700314045c52290303510450550050911038039007907000d03200028a0314020110b4001c03a4003040341143c45140709040b110300b550310300380c5031161103412800c0c20215040105440411503141a6528440d08015184d1071003100401c41911040c00b040351034400a4401030540426010422a4000340b001c00740d10050400408200b440e9494002411944003800d1031a40400100034070a55030264490440307440349a000800c0c0d4003c8846000c1d00e1041584294410503880e4180c00f41090920010010203001e0301d400c4884042000581c072130080d0048078044001040480060420440000c02865164250702e881250a02401c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 852951447 1250 852950197 852950201
    0xc061b020712050f1024030b0403050319050916060e0906100c060e01051012031e050c030408030405090f13060f020f0c01050411030109050319020703153c 68
    0x2c005076024000c00f00c07031140032503080c00b103c8069030081e41c00142c40310190484245041c640550f603080c68111420500c0002c10344400d0070b03040b83d09414610384a40d81c12401d4070b06800103c00751021503017801c0038000500000138071242400c0302d1000c0340c0075150711803c00b100c000c00245402680b00c0001c030f01195903418038070310340b100c1d1045500d840b01048a09441c2c100641d002c001d80c001c3c06a65403c108000244265030a40c054201000105c0d00310107191002030412810700003408980850000a1079168001d2040b1010444032034240c940340c1366990300d0383d0f86981140c8640d60045000c0340004010107500c4a40d68400d0721080038240000081d41c031000000c0241d200469403050f4204405034850030807202a00f5010a0100013041511302442e00c0010701c5e5a003201d6900036810418804000f030404401d0703d6200c02c070411081e0f0000c0541d9000c03481c04c1802d50002d00310071202400c0028018181c0c00240300d03c045024460440071403000003851650300101e14001500b0310460360506171842d5 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 852952697 1250 852951447 852951479
    0x5090f0a11011412040b0c040b03070e0a1701060315110a030504110a0b03060f031617031608041a090f0f040603120c020910050a121b060c061b0207 65
    0x10324240d122143c8906075035a19501158464402400102c20171040100e031b07002440c0e0040301e1a400134205840c014174aa1b241c04058122001d1007056034043d40241c8910b1180c4000f000c4070100c0c45085881203050500802e502d000941d012100080002c400c1c0040c0d002d104032864403400d10314509030807082c0450083c0700140003100c10385031079001c80c00503944e9916080041c3c00ba140400e540c0e410002c1c00c00c01d62950315107007240250080944041034010090142d0101d070a80c10b444011001d900c1d500d00e040d8401e81c3e803c41442071014851406000880000d00f0a842001c5009070105881d44003145541c01400e64050340905202034469240c01c1c0801d001d010342c00701400115119440c1c0e036580105e03441030301e1124005054100c00b001076107070000c3c515800032082d2b82c40078a554105004107140d56014001c5215010400c44110100059002040a640c03215900b07004403d48408004107940e688000540705103042103c0a180056549003501c00440c1c0c0360001d040d403504e4917810400580d11 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 852953947 1250 852952697 852952699
    0x8061602010b03010c1215061b0f0f080705150f0415020c120c0c0a0e07051b100b13150e09070b0304080a03140c0703051c14060405090f0a11 62
    0x9038603891002c3d0318240103a88854136180c0f940c009208a080b4400c1c01c5403420100c0c124806544c0e081003288a41180004a0003100e000c022080000345040c20184001c190000615003940c80900b84181310300603000c3c0004600c1541035980c100b42110458620400590b611408020040e01040c0040c2001c441ca00460f0150030025040c4142d00c400c4505101c10501104400c880c0003c1003800c039041071200b141e45110403200c880115040407408042080010300e08418008000342420400b801d000b0011059030003041140c40383c9030b04e80e4200f0040e00c1c041041d1070254002c08000c1c60840d410740580b0a09003205207040c00711914240036001d82500203007109c0c141d400b0340c240114228001900440c883c9000364000e540d102041d000c01400c4403000a88085e410003040e0622000a1101c0100e8030f01c0b941502e06580ca0340043c020540d0f540031084000402d152802a200c450030141140c0e0358464401200e0800c8a59603104441e0744451404c03c41c10502e801400b41c540010300315210861003004 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 852955197 1250 852953947 852953951
    0x10609030b07080612030a0c060605010c080d020a031409010608070b1602010c1401060b180d021503060402040e04030c031d0a211202030310050d08030c0c101802040b0a0806160201 79
    0x840c40b50703040c15580010345442c0083d254103c40e20a02983cae00403100202000c2c601180e030305600da02d501001e8001c10403172030039668002900d15080c034460f80050420b00c1c85414086c2d6a8100414880d000340300600c9009a54002c07420700041c49944801038883d04201c0f4080031940320400e03030044806a10308202140c8000c00b981259a110000b4882c0801a003c00c10176070b03985034401900ca09020b0000d55505216514480b184801078803050107030112101c01e818240d03203e07141c01c0c00040103809640c102c84440218001000240756001403100740c0c4501075152410f80301c0d00c0245200d441200100c02c01d41220290320300700518218103039000e01c007650700014183c600c040d541c0c039050424141840640180d00c04424024001c9030b1040f9403004046c122556070302020166a0484540001802e00000b100b0200b0065a101c1080c07103000c84807212903c04008003401c0c2c80840d82a00320f010800d900845c603210b155000790610030424015560258018500c694034948081c0904001e8154401155 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 852956447 1250 852955197 852955219
    0x21e01091a041e260a021e0117010302091302040e1c0801080304060f0e0303130b0a0e06090603011719050d081f0512150408030906010609030b070806 66
    0x94014100d40e4a801286540b0341d518030740302403003455440006003900900360300c01e0100401d0302c1031070102c40f4812280000043c0c10700708122080c10100d4045001e034228542984019010481e42d0810000035000d0300c40b8204c00b6150751118203000b41c01d00009400c4420403001c00c0e102c3e4071505407400c985100034004607040769104207203820601014840400b15140c0c400c10307021030350409201405091408011400c1a280c401c3c02441c190f00a0341d07101c01e11260300d0b0311142d00e450600c210340c000000440707100030036030b139950903245180e010421000009588410407000c44c9404001c41e0207042000b03003003d00316401c02501000329920350fa02800c5c41e20503441d2440511710b130810a0015a4000e00107004050507092000d00342482c0145640c3c0800a028a115021010385803000c041d01c105807010f10b100000000d60764504010f98000c0c0c1d420044610412013004a00b40007184200d40c0c140944110366a1003000703440c10101400010130000080c40000c03c0284a406a03541c010f800800c3c041c002 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 852957697 1250 852956447 852956459
    0x703080109050a09171c02220e220c05120d0908070509010306110c0d050903060601050408210f0417070801020408060403030b040b0a0303031406010819020304080c010203071101050703050103021e0109 88
    0x340c0c820324805001c00a01c003c0c0804850700c0c61340c0d681c018078180a540c427a602e00782411400c10706490b203011400d4040d0f1a1514240410006560080c260242802c1e0801122200c1e050350b039442c0240882c0002c148407000309070400041002ca04654000e050342c1c0d1241d080da50380c000680604083c4900004080c02491000c020030010b241032884640c4a547e0b031400c8007014542485402011103052081c00c010070003c19a0020307000d2011684250700182c501024180f02040d840307290b01e010226280494003085075030900c05541c41040500c02142d00003690b6403109400e03801607105200c0e041c0c02560009000c40d0280d0411000400e0041000421480c4440002e02c2914960401d600080d9501e00c0d4140e11014222619000b02d070900b0720b00000d261a12001200004100620f801035401001080400000005403150b44a104000755200e1810703803001041c03510118010b810319030030100403c82540c0244549410b991b00580300013240004002d061117461403840d001c6d410881a81c6000a503 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 852958947 1250 852957697 852957701
    0x330e01021005061c1410061d0a0e0607022b17070203040b0304030f081f26070308070b070f020a080702010e0a0e1602120d0504170703080109050a09171c 67
    0x903480c4101c6007810520785c0a002245002680a05a00d10a2030070006001d40c00c0d00d4200664407421100320646240e81c1c0c0056071000d8501c3ca90300d11401d00c507107802d03c07601d039801060130100070001303035075201410294101c00d098144c610280840800c0c2c403944070b440b8081d513045005a00000b03078012240341942e0750190b9101035000311811303030000b0014800c7e03245030782d03012806603003003407081d103207115a00d0742000d41403c1301c00709100c1c5000d4040c07103461074010340355281401c040c84211002901e1230b4075a80e051030034469119001c2128a54007610026000c24003c50400d2514201e5600400aa50451355103881036846030500368180910004031001613603030807144501030300746144400031a080c420b021241802080c1000c03000d54121480c40c65125210406541c90290a9203010071603803240d0a10000106808800014082002070f10340280b5030000c0115040303800e0768108000383d0340c0d4a550202103c100c044000c0241c8404091043d941d045ca8010709100c542e86000c01600400c11803076602 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 852960197 1250 852958947 852958999
    0xf0d0902030a120f0e040911091f030506090f030711060304061d2a0607060914100506190602100c0504080a0501090506060d0b0a020d0204330e0102100506 68
    0xd0713030315041d41400070752003103000d45103da06403000e02c00310041d41c0ea5000c40c01000c8400c10701440060380081c0105110083d0002c4074854556034040c100e450f4105143c076041c1c1261240e040b03204001c540440c9001c000111290b00c0c0e0070200c0e94014400400400c08258000760080d1181c1d6122040115030201520001641d040180010145420002d89001820500726840044100103058650076600d411080302e494030342c007910006803d0b8042c07810314410501245035201d148180c070315111120304907901c464001c3d1021a5601108085030812503030f04071281c010040103070400b01c202c1c04d07600b080740c004034840c8295081040c140f5454401d06842d180164000f5146a1345520500c010b114060000981042d426140700100360081c5d1290041440301034400c0c0d450a50000e80300466843c80da0544000d0103201071007030b0300343c0301d158180744c0c00100c125002d004036000712500724085070281c1c034540c51100b410f8004d00314038900b1510440080000a003100c2e0404000c040c02c0f04903a18004001c5 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 852961447 1250 852960197 852960233
    0xa031506020c030705060a1709010f020f040f091503080a0c0b0c04030c090510030201110c0d030c050c0928062c1501020307060906021c050117030f0d0902030a 70
    0xc42e005400105841c0070502c0c0c1c01180203c104200500078241d100982c40000d00c1000800c405603154940e29a00400640000b5141244040f440100301300140005000310f500e500c02d280c401b40c3c1c0303441c1c1080071a03215004a81d44142c0c0f0781004c1000410040260540c00600e00307224010002c01e4031110078290003201e416502a000040610402c0801c2c041c1030007629050b10100000d00d0644040d10540d015404081d05000307050b8270321860b4074001c0244915290024021521f0441c0d00e00c1c01401e0180300b000100c2b103501a1071101c503d03600700301c00780a21030150425001d0103841010281e64020303042c0e40444491944505010038a0078088060f07840825400049424041c9404000828908054040c090692500340258030582e40002610b4030f2581101c0c000400b04d0b91858820000d03c6a41c601e0355510101d80650981002c295001e107040714640101500c81201203000c00d5240c0c0702d003c104811b045020700c00754640981961003800718601c064100d80483c1c41a480c0d2905d8100c030b000300300c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 852962697 1250 852961447 852961453
    0x4021207031d01090f140307080c2410031e0501051f170303010603020315030109050d02210313020a171b010e01022e090b090d0c170a03150602 63
    0x803000700e501d0354031040e6401c0b00c10b5000300600c0007255608170703810b54110b0020f091480c030740441c0260b0860500c100c81500382e2202c2d50307942e501c0644075403507117a8a45d0340039a62030000c055400800200e080c82403030b201c2c00142e1007c580d1241907568941078032860326400c0d5541c014041c440c0002900920903507001e02d0714109003a561002d07000c018910a5a150803142c900f0a0a00302001000000410b8070306484050502507141d80e224415104042036511095034150b0901c840c40b81448808903e00111820b07503400d0301c0000d00d02c408450981f51040c0c40c40c4203d61010400034040c0c42800419030441d0303100400e814812569499003610105109803801d619422480044200c41a0204058944070003800c00d411a149030f0030020b174403048280c041900c00000000030100c421182d101c10f00ba150b42c19641027003045180d050656003810b0444401a00f0301c40d119035501c41c00d0286180e4009130341d2088140064040d400d20b80105d940007c034855040c035880c0c1d8000d035418005908000080c000d1a801 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 852963947 1250 852962697 852962711
    0x50a08150604020c1009110a030f020103060b0306030d1214010b13080c0f121e03070c0b040b04120f290a14070f050403060c0e15120f060402120703 65
    0x10011040c08040c0c0028400c82c410800c03821000c0c03011609180e07041030820001850802420030380c82d400f011488607039210b01c2c1150007008010b81984100c10360b90003039900300403460f00d4141110030b500c0282d0348154954005030a4030403203881000c0c039150f481c441280c0400c002d1040c1402414452085e041075800400102d00000344510f009201001820200020314412814038086001c00001c441d06c42d00680b460181c2d11068141040030350139400004008000424640034081d849402c540b0040703503864041e040000c1c0c9483c061040d5400d503081d017616603203400d182c242507102803103580e0000c550505002e5036000100b24502080340201c15a40499440300c190f1540e0740e40341c010024500d1050034a4014498240203004000c03580c008903d00700082980c107011400d842e503016a0740018241410203c184120560119107108400c0c8191010780907500b61481c0e420780340c0039070348400420481d0300c0001280b0710740c46005150000f9024100600c1c0c4260204801360ba5002150403d010a4a44603 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 852965197 1250 852963947 852963973
    0x20c0f2b120614030f010209060307080c070209010e06030f06094c050f1b0a03060305030313051e100b0604081501181505040207030201152405030f0708040606050a08 73
    0x1c290045405d40c030003146041c0d9241c1c0051071900000e0900001c00c801c4070300140e0b00500d40c1e800ca9150079002045c3ca030b169070703448035403034080c01c0f04580316030007800340960341d251201000444074080c0c80e842c00a803840c103088052000d041d070500f05034140032008405207050078201355001d110715411410390200030030001c42c101d2819210007526002010710b05030200403003c243c5031085030f18081c0b40c0c170300b0580e11400303001d04902510280d000078181d40400424031082c00043c40035840807d10607020b03602421054443c0700c1d540d075030381c6100501a400401101510303100952111526100041682d400c0c2600d441c1c0d0700b45800e4400f01580110700718034005101d86184c18124450040302c1080030310500c1e0012146030301504ca64441d05015a40110740f100401d070003900000d9040310000e484210040c0e64440d148014190305038a140d00034000501c59a0041c41082100d10a180100f040102d6407502c000884901d02c00900603282155581000303d00b0340c2c0d502442d08001c1664100074880d21074004 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 852966447 1250 852965197 852965203
    0xa0e070905041d06180c13020403060e0a030203030a020d06031e0507050913030e15160b15060307081f1d150f090414030409020c0f2b12061403 63
    0x88640d140716280301c0c2190b0f890388400681503520003506507182000c1ca080c903007410f05c4c042640400aa10000ba1f203043c3c9000c2c0000d9024204030303800f481d000d011442c6030078807003900c40f5080d003c054010303002000000c4602d021900144482404854001a4903a60707450700340420a00c003840040c00320040c0f505100780141080a03101401c821181c510460406140c00507060020010040a01c03001d81100350a44d503400c0e840c002c1d00704000c3d64007036403280b103d00c0f92042c0f1032a6400458846400c00302080b2000c11600002c2030f0110050a00c41c0f030f54507026010346100718001d0640269a200450085e00c0410704049400241410146148480c0c45c00c0100c0d42664030040810700e03041010078008000e56100c4865540584082c1c4071021103032658144092900c50000b00301d1424403001800252a4031030782d0090014004070130a941700c0040070050303191200c0c2d900c60f250098003440411000c882200d4444524540010304150030084107250103002070303e0f441d601c4122691761a4840c98206e08040c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 852967697 1250 852966447 852966461
    0x6081003200415180c05130603061502010c0e063a110f0a03111e07030801060c0b060105030718030c030c0e1605070609060f05060f04090f0b060a0e07090504 69
    0xb00001464681c200740f01681c62000d113079003c0c2041034480c02440c0c6458090022503038154410001400265107412024020389824803401890908808240a90f20b1061291718213820ba2991819240480041044016001134180360f40c042150602c06039039140c1d204100b045e8441d001a954000862000c1e07020440314a0f004200351300c0300030809030545812072000c07202800298100051284441d020a14441c05200e45c5440070301903071420840c042403c1340192047c00c0c0310713994401d900da0301c0d403c01722b402415800303009004503092804034000d0342c01440990f500507500e2400f2880355035a81846a4445080d60056850303000548040c0180300c0c8050840c400341a401441916078180203c0c010005020f01c083d0b0420010041030807001c125458001d06001508079078184420108148124014001034450074451494030440b0030340d906090003110300c0950040c941014008850715405201c102c0100020340c4410316a0000c107100091801d00b50013203019544075002d440c10182480700f16806 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 852968947 1250 852967697 852967721
    0x8010b301e130213020a09180f0c0f0f0c1115030618040f0b0411060304050c130b010e04090c050307061d0306040b070c23012c0304060810032004 64
    0x82031000d0300140e10b9500c0c3d10344d8400c00b00d060042e501c40707074103800b150b09114076044071a001c58603040c2462840c02ca9008240d81e181d00d22010000c40c40c0444c42500c0941802d581c0501040303c14401c0321955001c0e4086000040c020341540000700f841d117000440c0c11a07010900c644511000c020710400707080c1310904d49030800e03c0901002003401c003038558160030754818a000700390028680c0020f04000502c3c3e8010f14121000e001c454984c00d091a1485e10f6444885441e0b001d07a41e020700f603401e1541c090144410303840041c1c4400a5414507002070001074000c0801c151000943c02d540003401c1d031000c0001c240281120790344d00070f000b21944000c18030b460100e01054070030341c808403e000106028029140c7c200c20b25042002041c5810b203400d031003222500b089040e00008031011800100810b401030425421451a14440050740000f0a015107001c903ca4490a03407051000380702c41e0f401130020070340010001280d10b0f01150740f83d03100220701c100008004160b04140740404401e0505c0d0041641c00b00c0 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 852970197 1250 852968947 852968971
    0x9020a09050d030912050a050d0504051906080a0f0605182205070b0a020a050708061e0108060f06010207120c0e010e06010f1404030c03140d08010b301e 67
    0x410348008005444c1c0d8001c0304808080e010440e002c02c90100080600c096001e4141c0307249816411002d00f994004d03214036409100d00c00351040302c51108092540513140140c4400f180ba03101d403542140101a02c90700c6998096a504001ca40ca6440c00c8200c2d080441014061140e454500700c10103018002e40455801e00d00c00040c80800694003244075025245840c004640b1640300e01c0c0101d04c0d045400700041c041c1c3c0103e07040411820004100f940c0704a080f400707104807950304403682c8543c0540900c101001c64100c0b2000c40c03640f40c42c1e4400e140d0484014030454000079120440780d480c1c01c0c3c00c1c060480f18140d10aa041009011002005004240d1800c0001d0300e8a441c00002c2e00c0f8000140001082000360a09054a2483c80e01550301640e0840c1000720b4035034032441c00b041d00d006003180200303261007070203c005138440c46100e969040c1e4030407810301130600d4000301a00d659071240300f403482d20b520140114149252201c94010703204500c03460503284141d1034807511008580000d022015116 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 852971447 1250 852970197 852970219
    0x60b041a03040602160c050f0f030303011205030c0d0905040518031602130c050706050a15060810090e1b0303040f1a0c010e0d080f010501091e0b0409020a0905 70
    0xa08004104418204482155030741c1d50312454540001e1041031002c01c00c5e452140600f83c14043c20b400c040c1c0c01e83d2801d840a03444002a903040120000c212846c6035856841040140445110803408115151094081b2420444450125820f0195200c011b000040301c44100700210301c2c280c0103490700440f4200528403500c154225540d241e02c581b41c04a10882d810190030000c54542c143e2440d4281a0300000f04034000c104075000300b60f0780c4905420307928a81064007141c003030b010314469814100e103520701c652101442c1075829980c2c050700a0000590307a50503080041d405081d40192038400002801902006050740f900ba51307914640a019400303984140414860346c007080895600713071000051000d90340650300800a21034486e00c0603503c0a5401e04001180218002400d08a0312500b52291843c50fa0340304401a003640c030901c0741a00003110844200241e45403070000208903030400076484a802d465103420159980194031018070564005141001c40d0b034807100543c080c0c03108643c514030307035 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 852972697 1250 852971447 852971459
    0xc07020604030822081005100f0509040303090b0f061f0503010627080c12030f1207021006080304051005030105030d1407050d030f050606030601120c021e030d060b04 73
    0x2401a80402044880300140750700a45007160700030652080b10205a5201303a403242440303500c07505107190030703207180341040c1c00304035121030700c2100350290b8407003080c6072200d40e2404c02048030020002c0c0c02075003410b640e1180e14011950180c074240c45000a201c2041c694103001007131000b00700380901001e0486207a907a1101c01c503540702c0112811603444e80340c060111440c142500884c0c942d07040e007030240d8a100c800000b450754030114880c3c040c0c2004480c00d0000345002180941c172403080c1002c0020140d402c10031520b03401c041d03401403600110244102c413900d800c81d510180849140360042c450319803010030104142d1401050744005101145020b034195450100800c2e51583e1040e01c01d0140180c68081e80309080d03812042d542025004411600c00c0c102ca650b0180040040e000303080c4c4420700f0600022102d08040302143d0040506942c0c0a460090031a890341c024422700c1c1c542003c43c0200c00b5680300c7c45985492182041c141c05c0003855503a0640f40014003120000d600580f01140305000030044 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 852973947 1250 852972697 852972709
    0xb0111010b0d02010e0f03010207061407050f041a070605040f02101d122104060905010f02100f020c0703060b03100506032109040903031e0b0d060b0619020f060c0702 73
    0xe12542802c0c09288010301400241070006c0601100d074041d0b01c00300381c21084c8007080e008035100e6000030310580b8568a0b417000440e114825001c1009001d98104400c000c011021182035424000e40e040c60760038808940c0d6175106079401610183e0f1704404103a1400b007075182c03100c400d0582d000d850800404168030811000b02122040c81554450707000740400010b40c0f10248115420000d61160386080300404000c00c00c0c0c550460300034000050003030300c0302242e154000c1c0d101b8000b0198035001007a1030183ca0612001070100c002e03502e00402e0b001d0141da4035603e0200300000c0550311403139002ca040040c880078035241008907100c04844030700b041c084c0b01c03076a00c0114072801042c40701001d002005410840100b12427252020290700540303010070075814154103502c042e1000c05501d03039401c107003803420030300303400352441400455400b00d818440038000a0440c3e01600d1000740103040e09040220718000700021141c600c140d000907070802042e54410520900200e544100c040480d24101002c5c1d40200e25 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 852975197 1250 852973947 852973969
    0x4181a0f0d11061213033e0a0605010609030212070b03221b32010302090d0b0f0402030d081902030711071503060b070f020d030c06020403060b0111010b 67
    0x800520442c0001c4400d445001c02c642c0d209444031104a0241404650103803002c2c40d10005400140343d040d151035075200100442d10306030855208000014560030a408130703100f00c0010301001c0e8496044401e0001d50b150144038001c090640b1000095032840c010703c0354a012070400c100f00d58200607002e0207290038a1060301e800c040b5540748120664051000c02d03c004081e2100a4054040a4064010103010701d01c80000d440ad14001d040c101c0f010002e0482c9040030191000603015005030036490154420307400b4040712907000340748803c003d200d51121144600c080d50500c00d110042010030007981000c0080030301c2e650542c58031048a18200078154143c070030101003a055140c0000100c0c01083c0700d8501e000c0400c3c0e0760419160001d41c0d6100640001d48025100c001017418001d001940ea440345007561116504401e620510681541c2081060701007a00114284500440001c020402a1004e00b01541c400c40000030302c4200b082c0054142620001c40c400b032607050900746d005a88448500350 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 852976447 1250 852975197 852975203
    0x5030303010e0705070c0305030d0f020c06190f050115020706080c0301140402040305010c0c0c06021506060d060e15010210020304201c050a0218070f1404181a0f0d 72
    0x2d045512610001c9805104c2d1031805840508034a6000c42030040c0440200340308190070f01d04020203100804680c05902440c6803410340e5410032800206040504c03500891303400c00d07030384d4001085021555210308489003038105600d2121007c400c00507042d010011140035182a05098a680c45c0140740e800044c40140034100f82a4000700019201d034031103030162005958007000920205188074001445007928903815600740d0f520110000700c041c0041510b60000da8881d0000d58a82e0790641031001591026841c140d02603542c42d40010303010706018030306004155440010704810303030210009142002403d07046100a1041083c04000b50122441030050024070f44000c000300044000595001d0801e04184401c040c15030f1400b00300071010442c008503130320071201e105030006524035401c00031004803225400b01d0002da002140b46401510800701004110309001c1c5041d456132080c20300ca400002d503814030a619405201c042c0212010b141c80050810f42d005500004802c0c005480c5400380f02010f = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 852977697 1250 852976447 852976469
    0x1060f060c050717100501031a0c25051e07170316030c0201020708161d040203120c07031a09060a0c0e01030f06120507180504200f0a1e0f0503030301 66
    0x180c001c112060105c8100d0030b24101d0300708039642e528149114030700d5074045c01550610100c00020800f08400c0151052b00c040d07880c07696414140749515264800e6000310591b1240304000440745000600503060710b51a150304007800b501840c1030002100200b01d010041c2040d001481030801d90840541841840d90309441c2c04c0c0340303140640c00140e0030304003560840d02c0c2600800e41e011a03c4551a62031000306e54036213024044440d40906140110441650002d6150700803800c2c07e00b0750724009000d03054100143c82500d54480d5680d903030a40045400c4404496000700c40f081141c800c1c0c0500550b03a000142413020720030100e0152000b0b0500d0701200484d814595501400790201c15164041c0c0e0103400c0e025940355524800d410000d03039914081c4281c0c100f0a20214a00361125a1800b541d030180c0c2c1d20402ea0703036203008410003d10125964080c49a0020303041d82000c00c01d03540b4421904000c040c0e0100041c180710350700d100c400c1b0f80f02640d04007e07a9109003074400c02031038a0000c00c49046600160a03 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 852978947 1250 852977697 852977729
    0xf0b120f0f070e0d06060611070503011104030f08121f0806060a05011805030105090a02190f12021804060603050c0118230d0605310b0405010f020a0201060f060c0507 73
    0xd81da092280c01e0103017243c0e00d0000c0100d0700c25013051000000c0c01d031000854050a80e11410103085c1d98035010801c5440314240030400c0003403018000050114032400c81c483c05c0050502c41c003000c40c2c40880d584034420403c0311882620003801e02c1009c000d4100040079152511704000811202032591040504101c0a0a11859024120172074400980401002230115050451056603610342c0001c0580c4500205008800311b101a5070184080b03400c0c04200c00ca81030710705130ba055102c0c143c0c004266000001140d40c545400080c00c4080d1245100d031200151080c02c5052551078040c3d445c06e076506210520241d5842c2c540849050301c22100a80a02174036510540e06c08072801102503031481e00501c0c2a80c01d1704c200007964200c1c91080f201003109007070008031800030490803020158030030300031840a50500d004c14a11040290711501940003c1051200e08861004031ba0101c400e0000507507441034140a0581748440c0b1000134099450591500b044a840741a1640b240b4070032054500c0e09208 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 852980197 1250 852978947 852978949
    0x19050f0d080d11090a06090509070c030207050603040303050f0f1512070f08241e0403180b040303031b02030a0c1707121112030a0b01090f0b120f0f070e 67
    0x2040b41c08071403203810203000e01c0d008200814042e030030520000d4442e09080c800454087c0c8a17a04d1102100c0c0014648001522610800d0300c00031040e190590440c00740150104036902c91200850103644a550000741901d04820401c0d00000b000e032000c00d046d4441c070140a00105818414105000304131000c1c5c0c4620300303070740056103480c0c0e680d0302c44c01c00c0e400c03203803c00120440041603100385001d141c40e200c1601c01c941611417240c0d80088685104002c0ba03545440d60100c0d0450b4050707806882401e0180c14425500591a6035000c55072001840c624001400d00816a050150300e0340788001e52100004a1100100a0745038040d262451003080000c040240038402c1c0040c550b0a04001d059256580e8415824a18186c00c0c01c076188034003041128402403100200084c45000c201040d00010781551240c401c0d0401a00400d10701904021324158085408400482c005000b0007041e01c1142d5a020000c0c0070b10004c20005280541640fa001c0401c0103000005002a5000f4a035180040200c80414 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 852981447 1250 852980197 852980213
    0x1210091404020f040b2e090e0402090c0c0309090406020a02010b030303060d060b0109230909060708012d0902030402090606031302040f110c01140a02040602120d111819050f0d 77
    0x40300c0b82c03c0120054251904080c0240e22900c40030780d0702d5941c87d00c007985900061050741010341d4000d40100e070409c00100c0015609019095030b0941d2016680f03400380c010002036040c00280d4040e0f50305039000500819841e02481801e18145003a00950308500e4048001012589082d0020f00303d69120704140351260320448005c006030080180080540e10f80c801120007038540341c01030501070800c0d680480ca40500004455104940c5907403070070007682c20b000541e60801e00301030148145111702941030118124042c0140040c2071050001a10f0380340c50b004001b0040d01c060b21682c0500010805d01c560044120000e000d200e80640b40852038400743c070440780061801e1085148414004110b0344010b03101034000d407402d84264000c80c0c1254441201c6a800c91141c0c0c0f040d0340260344420380090714014000d0203400c5d00351200e100084c40c48080e9011580ca82e103c2001881c5d80300b94200c034464146041380039809081c164903030140d102400e00c00400c10042600380046d2152000c442648100040c1c0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 852982697 1250 852981447 852981469
    0xc090b16020f03070b030a2009280e041101050403020d110a030b0a0e070e0910090c03050105010816060512041b080d0210050f06031c02031210091404020f040b 70
    0x2508664400e503854000d40703041e4100392a0980310504090404400b03005849051540c000d90440c02854548a4001c0241601014840030a20900882d0a012800fa0789900d02b00030050700c1c8403225189054a000d0707807055040c1d2480341c18490188030500142e1208000d005601c2c1d03114014070790a0345844000ac0754a0b4169100400701110501080200105901f190045c00c1e00b500c119160f280d11060740760b01c040c00031101c0000c41d5000f0008805001001d40041141c2c502980d000d0b03001035102d445690030360700243c0000802d64040009490b1019000101c28014440ca2601c00e041c002c5d82c1032908a040e00c0944090f08103002184000154281c4048002c000c105510884403151040c01c006034491141280e0702c40424501380c0001c0030285400e01140c030444000b009000f403000042c1e905a4105a40c400203004c40c403061080031504074051403101d006416617690351405618010107801035450100301034144030002000d00006889040f044201000300300c030041501c25060380410200401 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 852983947 1250 852982697 852982699
    0x1a01050307030f020a111b0f1c0b07032903070e150a080607030f0908041203020f07092027040906020d05070908070e0606030709150e01030c090b16020f 67
    0x20010b00e143c01c05c0d400c48001b08001180a041d209842120310113160100050701c1c0a603049420b00c000c1008070310b0000d0760480700b803808812000e01c51f5401e40311040901d0007161001c0109950344003544480b8080d40c051594101441e401c05590309803032001c261a107540c5c1c45034100120101e0041800708800c0c40c1942603004016141d6110580c0c0c8055084d070360002654410003284c038010b60040d19030002c0c02582219034000c1156450b2918045482d510308112581c190114050108040581c00041c4401002400d840c0c85c0403e000034242000c003070820764080c1c0a0500042084078211640742240f011040700d07096081d440c1c0d208020000b14004c4c3c510303550001c00d44c61001603214074026065000e60302661655860964198a40c14401c0e580c0d5441e00400c0c04a414200005590340b0345100110f501107200e2401c0c0203070390740d2100b500c075000480c0304100700418117400e0203002a5030306204160903414249401d41c04540b801c60480117600c2500c22120354500d40c5d25030081951281c400906540c40 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 852985197 1250 852983947 852983951
    0x20a0509130303050108010b0a0e060609091305370819110c220b011b050d020d02070f211b180b01090618090c020c0102010506041a01050307030f 64
    0x507040520040310038410030101e000c246400008101746005204052030340a02815500005081070020140000000c2545501600400c84242c05498803554580210303c500d666030500c00d201e250003400d0008020001c688a11400890015800302080c01d50040c8080540c5003014061400d0020080c818050503103400449440080313540d035840014281003107503080584000c0e9410004015501003180300301c81c0020841e0050040c0081d03a82c5c040362072540c05041002010000500088d003604951106580c660410340920f502c8507014816034610368017610182007410b091a00c1102082240c0c0109910001d04000f1580c002c180c001c49854810340211800700a0340c00c4550003074a000075405030324140200c80c02c1c5843c48200e1801113100c2c268050312071003280c5007001800c0740c02c107039010002c101310300401c02c00003442c004500c900e400c1c10042e94082c10300001d41a00190039100007502140c001c03441c1098041d02c840030414803c0f100102440e10503030780e80b00e18070100c0190409802481c8414 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 852986447 1250 852985197 852985201
    0x9052118060d2d0b03030c031c02070f12030c140414031002040905041202070e01050111190c090b06030c0d0507090806090705040e010216110d0510060e010b1c09020a0509 75
    0x2108a0350000c200d415003d10600003090164180342d240d004811100384654800d12120300d028001403800942020507060060510400780c60703424039100c009a05898034518501d0800352164103000f1040d1407a01030900c0511030003140e0103051580720b01d20130420414003070781480406603000e100c9a400c4041510301075460315101c0100e030008280c1038070b044603220b080d20a00300419001052a20488442070001c01f080d07864040195050160302c01c1c2a00240560001a03418902d05903031000e11500480100112030300304042c003011101c000b108144a52028000c11581d80c101808a070521001400c001c601c2da29094019100b09038150041c18190050100700607142034000b034030f08101c40303088a050119215a8050a00300e101d09483d01d40d1841c1c1c1c0035a00b8020940440c0011105c02000d07094901445443c2c58007410801440007051001e91540010003030705007010180741c058030200c1c1107146010001c03130341500ca4021050b205000710740c554500c002036503241d104007401410050005400c1d4 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 852987697 1250 852986447 852986501
    0x19081603150f081b010f020a03030c050c0a03092c041203200304110a030b1305100c0e1009050d150603020402030a0b030d1803150605030109052118060d 67
    0x1e0f00d00c4452654000d901e0800c50304c3c2d5604c103004103055005980c02404061419850481c0500985101c40080c450100a41c01445000b08040011140643d03500401d003401c02a03038280040c4082020740300b40581d03c00320522400661549600300d54807001e15101100090b000b94080d051500301d020541e0040044603100150f6a4000c506c00c6100c0c41215080311010713400c010501003140409001030340c9550000d5017400f6590030b0400d185004104840242146040c000e090782da02c02c220384001441080242c15a042410388150050902c1c201080e1040c108070202d40c5903000c1000103000610f240c405d80650034a2070340008050760b0094001d5641e8a0304240ca070020f0511200f00c140079100321a004000c0920a200011549c4042515100c03594510784440700801c07400354110044944d66200080d95075824464060054071900c043d00100e02c20b400c0300e10100d01c851046103416041001480d0840321002c0200407548812510740381c440c0d07000d413001002040d0802100e140031505a11b45291 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 852988947 1250 852987697 852987703
    0x5070308060a300f120314270c3109051203041403213102030c0301141b041a0c0309030111090a08190602090d050604060219081603150f08 61
    0xb019501e1b84041c0844108070045185240c4102d41484401c0c1c00c22050440c020709002010341041d2240086816801c95640007803414050781c0c03120b041c01c0c0d0300d80e01001a00145d91064074841c000c5604100700c094419120789840c3c3c1c00d0419214092040000024100a0241e50000110031000c0407030b61112000c42e140500300847c4429004403916020009414100401b00d001d0b42004024909103101070f030381140c40d024040d505040380d05006038a0700d148592402d11402440c2201d8200c91100b90600d40c8520034051040e085004821204010502199210300050103884498985051307030740711003200d550701310b0040300d042d56403550030b060b0341081074141440501803031075089610940e1250f03034a00300380e035640840d008001c041c0703400a4030201007405175016040e00300000c0c0c070a110180466a0707107410036000304c904944040d030229034100005181d0005034811411400c04510504080c00d20700402c00e00000c0340e01c02c00d13441d00034040e03500d8816030010004006400400340d03401e4441c110307951 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 852990197 1250 852988947 852988973
    0x11130903030f060803072a030b09030307140a0e0d02010c141015030f02060d02041a0a030501050a050102030d0c020316060e010b0f0a1e120305070308060a300f 70
    0xa04040c3c02250103a004000c541c1390f207500003c410a03020051460a40f14071142d402c4002070b000c00c9000101180280800078440c0350200003442d07881c60303c1c00018101e42503002c07000c04101c0b024400d071850740750041d81148080e0022940c03040c50400e00c3c80100d41c82480c0c09170040450b020503000040da0440090900418000f015050080130300130010254000c000d403102410151030344000c00c0c09400d00400403c45455040b001514090b20746415010320082000701529074030000034600081a414402c45000d0a01111200c17002d0340f070240000d54034000d40981c90b0740c0558440035046031034020000c480d42c64003500c22184030406241080d0001b01251000303881c0d01e5080c50620101c40c075000a4040c0940c03001080118280d080c016029030116030150100c01c100000d070408600740c2c00740300b100c28895209a80302a45c071015460010141d18028000d54061000e0840900a8000f0b03030b400c408900c9540d189900007904180300009032070812003805004441c0c14504001400780c1584110 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 852991447 1250 852990197 852990221
    0xc08072010051e030c160c2102090f070c06060611100b092811090f01080c1801020c06070c0f06090f180b0a2c040503071113090303 58
    0x140068000c0202540c80c0d1003511481e8001003800c0c2089990f0b907000380c015540156850705598106a84080110f02d9070303481442c15038817180d198a0800100d008032000f004c0915641c00070059281e0154049000c0c44000342112903095113002c001030343c03540f242950300189a0420300c02d119060b03a405003c2d0811604030011403180c02a01903854099406000303240309e00402400b060381541e10101d401c04100a100d81c41e0b41d40700c101001a16a81156000781c1c224600c2c1c20400c40e82d01c3c10b0301b03401c0040d2002882c0c0c0080c140f12412082250084040c13007902c6260034001c3c90802e0100840c00100e003444000140e05900c5032010480e4400c3c03150f000101d0381900d0054041b000d402c0d813038042c261079a5650388036614408820540078801009406540f000781741c20320b800840c0700056003000440c550410f130001040c00d041e0446c0451140041c0e0501e402c07200904003414100c2c1425129541c0b03030300c1100d030040c1558201f40c40000c1d40342ca4a4240f004100b0701186d0070801422030345802405401441c00344 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 852992697 1250 852991447 852991459
    0x60f120c19030510031101110d121d06010303050c0f1902030c1203390a0c05060703090504050408071a060307052d0a081f0c03090804060c080720 64
    0x1c40d03020703200d258050700c40c1d003d04a8401e851652116140560301181c141080084950070065540070040c60300c042d0150380301c0320b40540700c0302d41502c2110500007651908580250301403940110104182d0305403605813410f6a91000e420045a203006280d04116070306205030048500d040e21000441c0924500c01c6080c0c0d00710184903010481e440c03090114202d02c03034008000d402031811810300c80d0740707085800580d5170388103205800d8409442800301041480a400c00a42d41d001c2102c001c450ba405000c0840e90141082c21984000303284444c213009542c0070b2903640000c01d040c4440c0300181c85403d0343c80080686d030a481e0902c6e00d40c504905464071401303485080c0700030680e490324811100c940382c0111050300075840b4034455201d140c9840344199400c074408036804601110203200120744080991039181c21642200c405008031b8200d0300c0c1c1c3c001094941544100024115011242140c6645c07408032078244142c01c0581c0d1501c2001801403000740c18000c16000d01d81e00d0049020300080c1140c00c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 852993947 1250 852992697 852992737
    0x303081009020c071206060509070c02150c070515130308071203020a05030a0f060f1e050301060303020c12070918060506090c0d0c11010e0309090c120402060f120c 72
    0xa901d0070307030041d0307442001c150f00290350a110102c6254060104207006100114105544901180104009032148800a0078441c1d40209509041c810650905103041c0f4480c40c0c200c1d11079003240c41d2600b0340609803051030041050f00c0300f081001c098660501d002d51125038101d43d286440a220360191710300315084d012a8142c000c4040c028801c0e0f400c200c404e9141c035840c5a88a50801d4010910078440d4044143d68820228801444403035402c040c1c071a2003d0b400240c2d80014026041d22055441039201c0da044c180180f00095002ca151030614a041c1e8100807c00c6c40d402c285420011580c0104040d2460a401c091410718901c0041401c80c2c0151410411501c0c2c00c0140101501c1c1181c4a4000740c1081000302d41e089003541c00350001010782d1400c2d0398a29040224a42502da121031800181c1d4004035000e6810700d0604030b5036070450340c000d410030b2411088041209184100038406840f41c60041103c0d8603105461084a801140e00040594140b82c108003110150f04520300012101030041c00b = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 852995197 1250 852993947 852993959
    0xa03021b0610170606091806010e06041a1003021c05150f1c080307050708180a061809022b061809020310050601030212040b2d070c050c030703030810 66
    0x81881400d050803c00340c4800d9840406000040401500c01c1009103440c3c0c8128144100500401d8046d000043d04c2c4903190030058204400c1d43c4840818150b4603101c042c00700c0b003030f80c0c03042041c50703a00d0410305015848620705070744c4505d0032585000042c415810714081000b4444000d0b01055a0b62044900581c01b006904c180a50405040d0f950008039140c0034070711020a244202641c3d004802d1301d425442c03c416030f903030b01e402a004400c101c0c044852603480e6900310310344008100098246c0740752031501511044003821004400e0300c14201c56550000f034026030305028a00880c102d4800400691050790040304203c01008580b0800301803007104092448c8100c61070140d0004c142e0010004e00c050350121000f00020030014000d541495400c200f0348a4100045052910584c0601814a0f40f458841c007540c0d56645241030305214103142d0701406041d201c0368050341da007008582c40d001200082a103050b40c540558954503d50600c40c0304c100100f019440158984200c1601d0008410b1030740c4c40d2 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 852996447 1250 852995197 852995219
    0x30f0c1e080714061602151b06180d0809070f180c0f0c0212101112070c08181503091011040f030201080403230702120a0c0b0a03021b0610 61
    0x30420b51340c001010012000c036104032024000040d40020711900c400079400c8014074440d440000c0390031280ca400407a942d01900284656980009845680131102510403051f580754034403a4043d605000400c1e0100e0403144007003107050007038501d41183d01d0b0119225001139582e1040000710030f03400b500340702c0d109501a2140350020000b00440e2a1900c8212042d401c1218803182c02c6928400c038450114000d00c1d001c00d500410800d0807942210981d02c0c0240c02009884800040504060181303092011001800e4442200e04008440300c10f0401e101c80c520004440040b1f150714490000404010300035000f402240d841036000101e101040101e0050000c051103004601c1481c059510001c17003040035500400b81540c2c0940311349007002c8c5120712104d1340340e940394100d0000c1410080208a607011814803120a030804c1081c01d00070175240304a96650340224110380504c0300d10301c0e4049a040407541c0280c064904284120514005240c144a0b00d00d07501c0030101d42109000700d0f21000002c42c07010304 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 852997697 1250 852996447 852996479
    0x111503061f090b1b0307080c0d03020405060706020d020702031002191e03021e070b01030303060905040b0c090310060e0717041509020111010f0507030b030102090a030f0c1e0807 78
    0x141c03100c02646103014205140d9400c03002c1e05031130440c0718000e486010b2400340010844a03105001081c0ca5100c60601680b50040b5001d8002c14103204000034440780c0e440109840010354805000360b41d401030080c00700c01034000d085000f0740504c94201c071000d410510741c000e050001c03d4000e02c5144000300c0c0c0000c850540316110038840200da40262211201d00c07039002080c07680025200b0f20300c00003010a29540c07070792016009a540000140c0148105581800340c28001c02152b0014400c905080e1544203450102501ea104981000519400d007900c0a000211718000c044800f04111070f40d8601d0341c81d0360340040300d480d40004e440d0000760341c071902a125000d002d20341081c0072469071248107c1d0007000304046c81050f4140405114482c08030030003400fa00340000c00e014408102400c1480d8042c00307842c6c401c0c1596109900521616405456003a8a0400c483d00042400a402203038203107100241245d030046102c0342c420007242c0c1c0322032007110035075802c40e2503000444503020395407100345218100b5 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 852998947 1250 852997697 852997759
    0x3010b061b191406010b0309370807051c0507060b0d1202010b0906120a02010503130609140d020a030905010c050f0f0a06061703120411150306 63
    0x105022651038290700c00d4054011110031030407a4406444003855406526103110211001c1402800481020070700744203e13801000901d09190039802d064000e41d4999010100b411030261a00d4102c220560300481c0100080006d010b0b111b40c1180301d420324401503401660181c03803078410040a0096001ca001c610411000c2c5642c81c1810086507544030b070050031102c940158403042880503038000c140441c194103903003a016000050030480443c240210110000c10300391051002c81083e0717501410126080b107031594240f80ca140c2e00e989541481882c0c0036030800141c8020301d4801e070b000820003542a481e0080b070010044800503400344500320703659018550014001905003608001079409515940fa03024402c0090300c4000c5803001003541340c05480d882082c6a80c3c00141d52505000321441208041c00ca45074400c00c88280354891150759100302507070f4840015041c0002024031080029078010254018400d10304a00864820100741d003040d20030702d02c211004d41101101c500c0c00c0741c9850010385 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 853000197 1250 852998947 852998959
    0x5070b0a051e0405130c0f0207030c091805120405010801090501050a1205010b031c14120f07021002040905010905060907020a0320061e07050412020f0103022106090603010b 76
    0x4103070070000c0210ba50104030341080c09070502c004030719682c445112980400f00c07440001584d60038000004e15034146c020050095400844013400401d0504200d4801c0e030b40303140c20100d29202041d0b0f642c802a02c0b2510081c1031030103000340313103500c40da0504004c00c100d900c00d0740c80e0962642c903200c2d10011103000703116881c0c0c0903400b0030b401c00804885410150001d0301400c00001d804d1080c00109081c8407502601628040752003c01c0f03065150030440c0c01101920445e050303818641d0110030000b0904014107052440d41020000824040c402c020400c005a1480c0055403102e640b1449000035140c00c3c010204503904101c001407c509050040510401540d03000300715071061500c003507039110311011400d00c0750780311008640c2c0501410009603016403000c00d880b40200408108148044502502ca01c040160801007004000d0841d0444503260703804441084035050700c42d0069000348546500c03110b0104a0ba441541200301c144103c41c4940c00580b9a410150b44202c10035080783d26003c4c065034046 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 853001447 1250 853000197 853000207
    0x90115061d040204090e06010e0c0c070e0424021207050703052d1602032b050d060f0b07020f010e100302090f120307060c0306060801050d0c180905070b0a05 69
    0x74a200681012414002e840145025103c142290a480704e510100026034011401000341d0340d410a05a580046418000703410a400503207520b0316035030948501041c1c6407440b0045003d0065429049a440c410941d28241c103111002014007c3e412210307010303070f140d140c031000120050b010f80d086502041d4103540d00c9251468031100131000c881c500c800040c0c8440603106441c4640f900f50005c0074803d100340311a528040c0385104251820040105841404960342c0344680b0410b9a40c100820040d680d0902640b5501d00c040d181005194661081c01a1414946d00141c0180c45400910341e282c001d075070100400752118015501d00400c403030701c2500040312201030540c40d4803030303070280800741c0e8010110220401d180c030000f0044c8039040c0010f509908001501010884036114103890150642010300c181843c0c0240517024590522552b40540c01d42c0302d0f01810041003a0180c000380a1410f0b0011010740d080c400d820041480c010b040390517204108000c509405100d065444406059860516007 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 853002697 1250 853001447 853001477
    0x6030b030610030b07120e0a05071202060714010216030305060f01020604120f050910170906090c0603041514090d0528090806150a1401021203100b0301030b09011506 73
    0x25044c0204003404011850144040c0122103000d0303150b07850341b414024201070402d420014105a0790394458611b0034102040140181c40311405d07030b20303490740001410741c1440702178807041c0c060302c100c02040001c14120342d1b03a4002c044d015071051307010700400c0e14410034035964070b0b006aa5400042d100901040800b51071169940e01c600d80c00381540106140503420f040031640417a51905000c1c4445000c00d07061f892900b5000008011194414030040c014405030034210000747c0c40300204110940940780c0000001c080c00100903035610760383c15132032040152105c45c0c42040b820352001d41e030300a500c1c050144801c124510880a40c0c0c0124102024007940c10a200c1c2c1014000000c000064103110b4070a02c00112880140500340c400c0c0b200e1400401040700382800c02c01129141e42110071a084644503000d00760741d00003031004c0c1800c0110f044035a2521040c2c8003803440103260303000b4800c0000000020080140c0c07640c1044c01000c0c40300003409800046010b0060582140c00f0320800211107800c2c010341 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 853003947 1250 853002697 853002713
    0x2130302040e0705031c1b081e2203030e0607020f0d0f12020a1101031b180b042606041a0a02040b0d0b1e0d020f04230106030b03061003 60
    0xb602d910000315102c803580c0302c0100342000c0c01602900c011044c9012918655904000b0140600c021a10f404180c40c0c02642c4180d13860241a05958400003846242554a544101291a401d03000b08a0000360b02c1e08542034400300300b0034041140002c07964444040c0d2810194140e4481c1c47d4020040f01451502c40700b4441c51841580043d03440320156030944002c1941c01c2d8503082a00320583c00340443d09801d0a08a0396044510900c070b04040c41d110841000c4c90a046804000b2402854030b800303210500c800c1445000342a4018000302600040c002a000c45040f0708002c140e04009070120302aa00c041c107598a6400c1240c019210801100304281c2c85d41c46508441e5121004140c014282901d510100c0041d40010078001d4079243d03203000e51419898403120440c03d07800c00110700d450404c161008280c05080c2280000d0084020207810320040c1e80e80d4020460700c1000c400b080400c40320744c04078880800f0003031243c980400d140034108001410080b80750b500c5581161a02030352580f0750f940b2550703 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 853005197 1250 853003947 853003961
    0xc040504020d020a03031701051807110f0f25060504030f030909051303020f01052a09030a03030b10030504080a05181210060602032d250b0a0213030204 67
    0x70b840460005854010394840344500f000d10302907911120340700385c02d03482c040703200700c060308124805c3e4500220007404d08496046660700c191249000541c04800c80e00607480c050900c24100500e0003220992200c6880006561411204150100f4100304045484000c0b045140c000c10001840030003042c8046000340c103a00c004c1a20030b03d0000041e66032422803104580c404d036a414070302c00f542c0b0188400c0c5a4104046403000d01c05200801c01c030308160300010182c0c406461040d180500c807205000c42c0c506480160fa0f420b2401805491403d48140f80040c010440304000901c1800a0480449414480c1c4105c62082d98040c0e4158a42500d143c1c0a44031904071843c0300c141700c0d850304405c892644032042c0c3e10b03c030a10368100405096090f0b240380401d4403187d4102030119407050010200d0303891001001108031003840c60034600c503518110103244030b00c2501000c03804031014184140c422400008640d12103401000d8011407034031741c00b40d140d059104084445003403c50440060015141030b83c4100 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 853006447 1250 853005197 853005199
    0x5010305060a0b03040b0a0e0606090129132c0112020406080109051006061701050402030915240109030305070b0603010204120302161a1801032a1706030c04050402 72
    0x9403103d9a45681c04104d074400c43c0c0403114900e4030007e0001001d11402003012100600e0081d20503403805802081188405210b0300441011280c8074841c1c2050980d5518072052030307038250365a12070403170b104920514118428608544260910315401c00314070308010381c590340a504c0c0607a1691074041c120074505d003e07140c20b81e40280c1d01c07140041c800e1401d10581f00710310310403406000d100c403d039503d0504440070b0758405000e0003c00e030031105a1810050046066407022500180c680c0c59a40006280800c00c1303500002840406003401855020303004118400a02e040714104101020030044400702c51500c00140491024450800012460b84415500c14009400141055580d0b0791511071003c1c949000c0c0d01607000180c60800824419000304080c00c0c0e803020000d20b90706001c140c03805a01c90420001c2c1600c1c801c000c80c90050384240c201103130800002d104403954032503603040071607881650b022802c0803542150809840e402c611080c0f0713109040c0100a44840c1d802d060511001d008001c00403 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 853007697 1250 853006447 853006459
    0xc0907020a171305040501120308011e270507080a0f0c0f1b080d021804020403020d02090403030b090a1e0b150a1704060903080c070f1403190513090b03070501030506 73
    0x13103443e0b01c440c0f1425008213001c4110b80c803051290300b0003030202d07601a003000508001c0740e00c041442c00358907201c040846070030f51200404801c02521001d03004003400d4082501c50f0070310051105a640c410081c0380105400030b002c02800341000c58103800c440111048d00041118100c2c2e14280364098420400c2d981107080005821110555035141c04d41e0082c40740382c3e8041d602107031038422001140100204000305480031032605085d42c0001e0300c01206044000c2c411100c04001030308051117608000c0c0301440180100c0028284a1840c4019101391000030600c0d080610500c080000c0d00e000b01c1070031100151120400c02d8001105114540c0300d0000032048c44240208140c400b101c0d43d841521860084070002010f4000e458020803c54000d0844215a0b806001840204034070614107051f440d405003011a4150342640d00e1825401103100e00d8140703005089520180e80e400031700400d5a2101840110103080d1103035045004c030744244180c140c055004541c00e01c4035500960229811000003452 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 853008947 1250 853007697 853007699
    0x30206180f0d02010e0c120c060702030715170703051005190b130602060106020304140d33051605041806080d050d0b06040b0313061d0c0907020a1713 66
    0x106180502c14011080140e64509000007101024441650703880c004071340140038050080442540c68008509951103240c000614004650341003002c44000c0c4082c6c0b100107a000f0b00100003034404003203a06034600d40d03209880043d208511a202d09845002c81d141500c82c421f060a00703200c4d40c074807004031709500403800071008141326001d0b102030464114600f0104164a003040b100900300780301a401a0195032045c4014088011000001701d0400da083d90540b0052785d20342810b9030640380c2da143c4402c0004900d0780b202d40e06000d410650940461800060013a6150340300c03091442014405c6c62000547c2c107120500000c14030304854040000c85003404201252200340042c10441007403d0500813610002e01d00d0300e9000140258807524808031002403c10b890140301c1c0b03004d44801001c3d40c981000c40034400342040002d50041044044506070f108104c00ba01d02c80c159039101d446025489502c503500010742d001c0c4005817000141350300500301562120301101c9a1200e80218000003507501304110 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 853010197 1250 853008947 853008973
    0x3080a0902040f060e0117030c10020f09060f09033315031606020601050a03110907032702040e1b33120a0603121803020a09052203020618 61
    0x6984064205d0098030300340c55240940d072407503005841072420059081801050500c02c40400d4424001d0703150b000140e40c64500c0a50035642e80300351480d29501030408900d00007250040001b815462806400f1503808071201505407200200c1c104602c0c0481c6620b03540c10f400541d440400c0c680101030019411a44040d000029080c0440c4c144402c015001481d01000b00f00c5c0d040141c03e0040c1001d58141c1e2181b030460f1103da902d44181100640685042808aa4060720a6118200005c00030492092100008050450141442a050340f19134244110030303181c01c00c003040030414103c515100015100102d418482d150303050103440d14038034421500d800e2120200009400d00c426100c103030249d45031042000904510320107010004898901242480042c10740040000f80c03a205003400764861041c00d4548020307680715000250080c1403031400085148082d00082d0045940d0b01c041401d0070b41c0030602180702c5a8604028005900510100e884004c1c05444101d00740911004d8508401e501c078 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 853011447 1250 853010197 853010201
    0x1b02012c16030b061c080a0f051605031c0506130c021f060905131a0604020d091401050105011e0e0f12070509090d050d0f0b1309170703080a0902040f 66
    0x1502c16102a42118200545440c001e03551040b9602e03441201c1c007034080e003501e0b550720900413100e0324010b100b00e00c40703a100b15a0160007603030131028920074440d4415005103002034413604040c1034200964419010540d031541d0b83c2c000d81e841030b500902007a041c1c03440d250150018090044840c01036000e4501408115501d080c44041034080b09540420240c0c079010740002144c100402c803c0006a8045c503440005802180c11030000000d40740c3d4803100d48a100000d00244140e0f840e07401003070714000030182003004e41d15194a0104034071001300003d80c0d81d10019a9640e00814111410940c00c201f8032407403900940c94854603003405440c00d15001302c2d032000301f05001b03c400d184039020b41c450301c4101f142e03150840282e41c2c016600c20242080040c00d60700030380780b0f00440075480070907503c840071009003c00351742c001381000d400100344140011b10b01c481d410003050305041c00e071940c0760050841101015142c0440d21410350540d541105581c0d461007210003010b4096041303911903222034000c2c01403280c0b8 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 853012697 1250 853011447 853011449
    0xe120904021908010e0c070302060a0c180815072a1707051b04020a1d0f0d1b06170103110a09020a030e1536060106031b02012c16 57
    0x2c0c1c3c40b101c080354184031860105800041c11410894000c100280001b41c0c085030203500000c07880d4000c13404a48480b07056822103070390440d2a0f000c1c0f115150010b442040020f100c0c41d51105c101c001e1070345d40c0301c0e180210341c01154441501481c05030003c1804038001004c0c1c2074078105000c1c10b01800c0018505983c5246079110362410342d280d90105001c0103490342c120440c0c00090108840031071910200754005400445040c1058030580e040c0218016603484400b240f143e941c1004000302d14540045c5446100c60700c40900307422313210b820b085d80861880d0141c94003160752504080040d006a280d0382e9101c145040c1e0f0560f841e007004182c1c000140102403400038000c0602d0300d4401050080b60702008038a801d000600e13080245c0200c8060000c50303007504074100a1800e42d16200900e00105958080f110b0840d054460140c1c86007600000711258540d01c41e9480105181d2034032022a1540c4049003a01c0c1c401c404007089040c40159032030741c4c04a8144200b60045920240c4230032008a8400c50030140756 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 853013947 1250 853012697 853012747
    0x405060316030b0405060f12101524210f060e0106030b090f040b130503040e06011205071e140f070b0f0903040605090109031b0314010e12090402 64
    0x12229621810b03054000c840140000f6242000b9518103d000200711814460510740100c0c50781109845405013171044a142c00d03041706090084140c111003c10b16440d23070744110700c0c145030407451409101c0c4509503101c03031003c03050b0703140d040c041c000c03505054903c20098100f5040c25a0344066042800050080034000d0140e1710916090b07604d0083c0141c103940400e13400c24400c48080303041109410184200c941c201d03030400410b1031030703648084511503180301c1d800c805801071201103000201e030204840e806109030400e80c0c40000d10407003a1090030956506851403000715103c00544c80c48031100700030108101003986812041017404615441480d031001c405615810400aa40c1003400341c61508540c21001d00100c004551801d90300d07164890080740560420018000351140c0140e100300c02c034402a503004086c90300110f5190760461a00780c10361000302e846060089000300341307450621801041803d501d002c0c054040743d03080094482d80c8100c0d035040d80280d083c052180e0f52401c00c0c0204210f421 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 853015197 1250 853013947 853013971
    0x200904081c06080a0501060f1a040909050a02061b01060614090f0303041d0f013002010302040513050f09030301050a0501080a020403050f0609010e010605151b01020d1401051512090304050603 84
    0x401c01c0d5041223183c246401c42042c880e0803690740c0601090302e004503000c880c00c0c0d14000132a048140b0b400c0c0d06080d4500406940f0003004518425420014148100c3d0340d44040c000300600d560b1070a06403000440500c420108510602540b0309a0400799841401a100142502c2c5840d859020020030443e0400094005000f070808004001c00808101d6005d1701c0030890201f410048042c54041c02c003d0f07450095422101c0691800c03c59009405071400781000070401208401030031800030007000100d55410f81c00b0031040100f460f1072030110440b8182c8034094500800d02d81400019100c060000c2d1210500c50340c20040000400c60070b0105149a039992000381c41c045c01c040c1d030b8050070740d25100c206002d564501a0108080e41d01e904810010340d034100e200c15201c41a80304d0804c0c0c0c0c1940b01a520132554000565104c04408070780c0006000d49000000c4803107070b41c86030203201640180c0c3c120135459043c01c020800112038031407040f40e84521903000302c1c1e00d000e49620102d0040c1d0801d0b00c944d25100 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 853016447 1250 853015197 853015199
    0x3060f120a06050f010305121312060b0418120549050709140102010b0904081e070210030b0d060c051207020f07050f040e0604200904081c06080a050106 67
    0x10780102900805030300c81162465040d03841d1a23031919002000d1041e248000030354080004078050300350f801800c803141900e0340250a424040054812a02c18510440c0b034402c07482c1c03487e5194032009011580002030000d4a40700c0d01c0040d01e6a9000608e0100303155081e814238441d11808070b84450395407a108517840d000d503031949440320b103420840b000a00f456080c141000b940c00d0b4007030385c400c0072150705081610031000d500c00103030b0042241d00344103500405468204070600a1200080015108030101100607558522208505008000d00290700a82c9a05c8071400c003482600710f50340d800c1000b460410709036160b13503601c41118510030304030340031841c0442c04075000cac200440e0b03240c1e10020a0014082d481c441c4a405a102d00707550140610491070520710b10103549440d805003031107600c0719044610b1410f1a00780603036003001c0010003003101c40c03e01985000a09241503880e009a034800384c031a04104e2028510b0280040c00e50402c85a540c0d60310000407104410007880702c9082c0114000a206 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 853017697 1250 853016447 853016453
    0xb04090f06050f1e0c16030f0207061803020d0305130e0718060e10050d060b0403061b0c2402030112020f0a26030d0606020d030c17060603060f120a 65
    0x561002055100203185007010810082500900c0800d002c000307443c28029076076058610381150241c00081b00e20010002c0e4540f0030581c214010340b102404035000c0b9512143d94030340850305003600440c55940503034080350400c01810500d1041d82441c1c404d08000317090448428894184144030340c051500c441240040c0706d581e84d04803092510310703403807000e00b41c52247c10028041c20000368142c0d698060584412039800861240041c0c030301072802c040e418410769a40c0c00300c80009410031302054410340c1c5004068a80c110607c6200400d0031007680300c004120006894444080180c07404070081200001c09030f0044001500c01180a000040c040c0c1138018081d0052050080c80c5502590298205a1080c0850164202010103101089540c9481562800617240c00c6000e004012820302d400c280b0302144003a00454040310740c24084d50100030395004403000b20349021110a645000d044444080b45041c1403820080d54881070180c6002070311207640c40804d82c01d04100d20080d0003034004030817003c10 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 853018947 1250 853017697 853017701
    0x18120315030d0f09050a0b0f180910030215040e06010c080d020304080304060f1a041505030a050706080a0c0c02040911030d0908010627050603120d1a0108090c0f040b04090f06 77
    0x17610f829902518030508003456071411703119038040d50030034900200303100001100c207004c60188644043d04171032035400c0695150860090300e000c12841031031000001c0441481c1101a85c1c1101c0c040086125152034000040d0783c03d50040d581500c0100d01040707031407803400e107500046004501c64443d41e545d0b4078082c20003004452007101100d12040c1080c10814518071058103542c803c400c21140040c1203009100c07180644e0480703a0000da05409540260010711902017004404c460858440c140d86039142c0e070303a490441e07002c80f00544c04a01c1500011015040c10303403124910500c10380740411920394400009142210f040f809400223514544244003c000c00c0c0501d0009055007003141c031040180d20500880c070325002205e154020341c0c44001072031a0f40d0401446d10307090f0b5020340003650780108903e00c40140121402803d803100184007084515441040710071b10034241d4030040c114185504081020102d149000d0035442600c0c0d2001c841c00780c0e10340c800e00019511500098580601d180f4103d41 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 853020197 1250 853018947 853018949
    0x50309040e0a111e03011803020d080112030c021302030a1e090201050f091804050a110a05030d0c03180602030715060302060f0729090618120315030d0f09 68
    0x1c0c1038000501000000e010080c00c01c0034803d080b250710b42c850a6034182043c0e00c0040300c800d43d40c99800d054480c032001c29145242400744d40650300366001002d600d85d09480301842032259141038120b41d1040d9010900c07404200c400a80300511006170480c0702d0080c5016030304107a8004101540d41c0e404c10300d20841421a82d003032044c60441c1807247c84050f400181040c0160040c135461894001046801607480810600040c5031280098010341000d0525a95414420741c0450314120482045c2505140c50260101201e400800070801514480d50032035000b541c002049046c48610140c80750b400c45074511000141110358019030300c4800324244280301040142c0d4541201c0e207080410b101581f600c030700315007a480e500301816a441100c0d10300903201c01c0c216002810592800301d910b4501d40e10304001140628101d4040361844e4036101d04034400801c0c46100540c0c141d006807414484003540001650340b080051490300081111b8001280c1043c981e060490300080c400c88100064541029a81c8 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 853021447 1250 853020197 853020221
    0x6030c030f100209040905011e060503062202012a0218090601030818030105070801170f1c020c130501030311370609050c240a080702030f0705030904 66
    0x85244400714020588074101c0168000381c480c0c0001d03040007140c039941c102c40c686030360050003006003884012020021000f14490384003924109400002c0d1850000707041402940b000c004005084001d030152080c603040440e080741031208008805650044204c01c0c0c0f60301c648000c1800021160358410000034506c004c49082000243c00c080c0303c200c0c2c40010b00c680c107596000b64a140d440c94881d4101030710300b1050000c40d62641c02c010030442c0c0190311089143c101c9070724155520b8624400c0c161152101d0b0f0461050b00c00e94011343c469282900000b108804190b80c50041e90126001c01c0003180220b003944e038010801c5600e42d1b00400c1015801720041c0495401113028080f00180d2540008403003485080501e4180c00b01c035481d43e0340d8889811508130032a4000f40402c4003000a1400d40e4441401400403841180c3d0621002d00903803060f40c0c043c1490400100944c60528503100a580d0000003401a5085100522010000903440401480c00b180240700841e00c036a502420002a139250b64900 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 853022697 1250 853021447 853021453
    0xb040f060510020f0d081b03131109070c0204020310030803040b15030a03080f042112060f180c020a0203060a060f06050f1c0b180f070305090a11062106030c03 70
    0x11907070950000c50800317482c003400d1070000b01a0b100c2c0e81e440c3c0090792014020340810b81000041c003039518030000900c18170600c900301910803240008100076114a00710755440100d41c0107032460b001032503e6030046500a2528030300c54007843d22602c03549080d80003106c1c101c406100780402c8c0810384041a0658042103021402400310550591b002042180d004c0c002805001d4484003050400412041108480c101c80361031100c8102c2c3c405000b4860103464142c4a100c0d4035255010402c1a90881d42c001620551170f4084500701c800d01d5a00f0080900c59007541c1140039200c1c0a01c0141c2d0140b207010700441a0740d502080c0300d41884603003203140569503c0310341400400c0002c0e02400c5440d0040ea0100b25000305000078818000d2007400141c01c0440307040c0d5100014222189000c101280494012114541c800e01c2c1590303441e43c10b07003c075102aa0407080719880411003400040500161000085016180d01d05106000c01040030b8410001014402c201e003031420400582020001d03120400c03800c8000b = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 853023947 1250 853022697 853022713
    0x308070b01050f0a140102280b2415070f03090e070804231c0918410a0b01110c10030903110d02010209030d03060803120a0b040f06051002 61
    0x6510b134100c034810810401450003042445a00a100b408044031004e420b01c10701006101803c444c00d0840c120845031510a00045281c02d590a060b0070300d6445a850040e000c24035541c100808400100030030915a003040264038000340d0100300c2e1420301440394580f18507903410980f0007540307424000e10b503400b0454036004000215200d4611603510b008902003178180e55a0301c80d07a03507007000b60001c1200320b400c1032403c08000300c80e80a82420205d81481d048040001c1d200c80300d00041e100442c10500f043e0525229401071001c3d020301403480700d5240030200600c440000c00e91105a441203425041007503580d18184100d58015518000c00003d0001504c1d02c00d0034031000407a01c6402d0300484003015903440380c0324201400741180d458681156400c9995014001000a002c1e5101c1e1074140c0c024001c40b0151242c03180240160400d560350b610141d420007074802c001000b8080000d007402d41c440d4460420790301545844c841d44c6405095002e02081241c1801c09012941d00024096000c651000308 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 853025197 1250 853023947 853023949
    0x20040e3a0c020d061b0807030e01050405030409020c07090608070e010506030723160501060801110340060912050403050a061109030f1c09060807030e01150308070b01050f 75
    0x2030081d010303541150340003415034003420b0800040041140d04103040d040a0b1449480d40d0300004d0552250790343d60740511200070445201400e841d4103485c01005580140800e20007280140c002c4c0410181d84000c0310412903031100d00c03000362003299200b44415000310034284040b440c4406414013401c8161035035459800c4c01c02c3c1c01866185400c42c5240c1805010941544c4010400112000003480480800b2200c2090a185000307150b64400c401c43c4d0743c03810341c000000c40c0400342624480c9240d0300d4030360a1700c105002c06d010329141c5000304c00c0450712000d040b540001c1c80d61008506042c0120000500c0c41803a02e00218884035005200003804024481000050b1000940c480790075032061000c0b90540c50584500341c00d0054040c0c40364140941c480000307030f010b00041c085c1800360080004448c609020503080e14501e00d01d002e0301d40020482e44c000b81006000e5040001c8088244000007450440e0224509141585400844134000005141020f004580525a01604044903a0240f060500b0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 853026447 1250 853025197 853025207
    0xe04200d0c03181401051005060a0804020301090f080714061909021c080307020d080c04091d01050c0c010f0b010f0f03020f0418150320040e3a 63
    0x20081802203501c078046550214401d4001100320030900d041040304803010320303007000104070004400806606e044c2c0029940f880003400c080c11184040e0003207251541141040b1407100c80140180c2c0c1664854410000013400250311100960051100b2a101c0c41c0925082004407a0341155541d01e03848401031012458640a15030012130300fa030000038000341a40301203401545c11242c05009084400303010b205104440340114459091740c0e0a64801da41e5521065030800c20640c0c45010506060009000b500380c95030042c41c440a000320301042032000212003030b0a40d00115095401d0000100d00341502110034050030101c02090442884070703910200000740329002d0500c10108114460f114000858060b81c12168406241400f0542ea1a21020420034405190912000481c540119a644054503000034810350381c0c0901281c1c100c03981d0081c0d042405c0280e20107140d01c9651014090791041c0c00700720390300c3c0b0b003002095204c2c42c0d401c1640481e00300b078190114801c45030880030980007642e5440 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 853027697 1250 853026447 853026457
    0x108060f01050d0b0a150206010b1c09020f030d0504060e0307240c1a060f01180308090f1e0a05030f03030f0a02041508042d020907020a0c060e0420 65
    0xb8039099480700440004800a8040701d40459013002c1441c2c400303d80a5810314170807410340c6440e022600140d0b0780d000c1c0000720f842003c3c5206030102003035841e0f044070585a00920034031030004203000301c800343d0100000d0800d4114003032a000b0580010b8100032203604010f000d070180204034050000c151030001c12003100c4000b041030340c40341400260107441c0707d80206885552aa0864032a10a000034070101c4103941d101660120301c05c003d003070000b40440d0f20411507403114010110003080468075640d90015290440e42420f45d0004030f407000410307aa00c44180741c0e014040d911806241c10700b0030005010403c0e000740c1019000e038004589068a40c4030001c00c4030381001041140710002d5036000200002409180c001c0301c401501001544821907000800714004d50044244060080014410440c01850b40c400342e00600401c0c40390201502e40348600e91780c030107e1030059608000035991744c001401060b03000340700800c0c0d0864010800d81001d00c00d03842058540f0401801a6054060b01101c2e4024 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 853028947 1250 853027697 853027699
    0xc06040809030715020303010602011a0d061512052a03030a0f050f0301080c09010920030a060815011523071a0a090201111b09041e060504020f0108060f 67
    0x9070300304241c03000c020740e82c020000a0b404400300d440c41c5100948942c400c0c45640010340c2400a10390341500411903918420308000c0002407001c00380d41c0c0d41400b42881010500c245070788507000142811490100302c0d099489440030703024140f41001ca8614400800070103050000500310034010b43d4900004850827607015041c040300c8904261001c071100d114541b03c0042d40c00d40400000350721400051500302d07580d0101c5104182c0e0380c07524070382c1c1c00300d4211010300c8034424440800d0307020f45040a0000e5070014000b010200c0d81c15200e2012502c1d0648214040d10398600d0320b0300401814004102d0314442d02d24501d4140c2e0f200390461030200c0c411200d455a0300403408005929001c200d8030221140e00c4160081c0c1600300f5107042d82d00b000c020505d04030161302158421032011101c800c041094080c807a540c0f500f070310010785170505004405a00a00460f0680301061001c1f903800c0a001080d40454428000865140b400e481880802c0c00948481c5042c014180184002c655440c070b441f40da00c00e0 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 853030197 1250 853028947 853028963
    0x402010e130618020304061820010201090804140a090e0312060310050901150e010819030504350607090e091e03040503011b080406021b191103030c0604 67
    0x3101d109034002800a035001811001c1031510044210300356070040d522450083d502081040c5d81d81d003005140e099180401020418409400c01c5052001e03010000164018800068507803595a02d044d02a4055040101318144141c2c21100502e001e8003000c0290105031024400d11072051140e6039240030703030049003200d43c92040000b5500d0701c1c200604d1513869980c08080c0064100f60311000e0007800d145c404460300251007071020512491009060781207510704001012261441804814107516221b0100e04011007000001080409030455240480c0c5800c61013110502d544590a045d80413280f0840749500140700704032030035412401520449582001000c0c059880a070f60b00e040481030300201d02000100107040421200000280c8185c52055000300100961410b00d00144c962850003030001a404000280000d2580d4024141c0140729641a200315244440c0c0e040c1007090991841c040039440103c06c0040c0103400211082e00602079000d5460302d40c041082c280c456200400c0905151 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 853031447 1250 853030197 853030219
    0x60e0601020a031b1e0c060306050f0102070306050c0702060d0b0a09111e0c0f030702180103050d0f0903060e060405010b0103020c0316020d02060f0d1524032702180402010e 76
    0x1443c000740001039641700e0000448000c191a2a001c0c10040340a000006494030301d02050f0390038506203070004000160020724000f4a160b442c0805054010311425000b0810700c000001a200c07031000e010110302c2503a001c1400d041107824080d80e10384c690701c103012490910408074104000f0108880c0844156840f041401440d83c0540380544200f070101d00280c4030b040d01e0340d220105c01102400906108640d081d8212004c149101c020186c01c2c0000340603078105402e4916003900800300242122903500b82031070034969035120001112006900c00c60240c000c070302000108007003841203202c850002d007030840c02c0042e0b04480301d80c0e0340a1100c20b0441003012940c00019035481003141c1e4200d03075008040569903801814140d840c1d4020101e8075001d00c3c2000184100d0080c5440060300f6070ba4010a2440064290415401c0c1c520410418074103060351603441212465444036610455006c2da000c140b0350ac2000d105211602c0f4a100340d00680303c0b1350700d00b4080140c3c0e019451041e01c000440c0d034401c5030 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 853032697 1250 853031447 853031453
    0xf18091611160803040303170609010b071505010608160c0506062403090705090a1a090c09030109230102040b0301091d070306060509150d0b2206060e0601020a031b 72
    0x40b042d08920389109501c1c50000402c0080000100309aa100380d45640a4001c1800941c2441d40e003600c9103640000ca040041c42945018000390075164054501c0842e60414524001e088038003e0300b0520005841d6010400d40c07504800a0a180001500e1706c100c010a00303490b01511441d02901441c4181c42000f540c4a0241c05030102001c46000c03200811341c2d9081803586107588000508c030765809034840310000380350000c1c10f2003001d071080c0c0c05500c3c1c081b02c0d60220341040058000140400d41d210307001c1c0300c903060f1600c0903c41c42c05420301c12522150342140c00008607200010078130746031040741e004200a000da03c0003001940d046070408007000c100410007991070742e01040340010808803441260800418000150403880c1111380581364a5101d48a40b4914110840d80030070072504821081c081500080b0040c3c945940900c9150404d44581c08610703514100740d4940740140c9017907898503000e12529541d5400141c0069007400109042030303450740c0190940c0303040c0c0d1140c1c111400c511064014 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 853033947 1250 853032697 853032703
    0x10206060f120f0706020c030d020a120c080309070504150f0b13030503120703060914040f020f0607050f011802091b04091e1401061416080f18091611 66
    0x5100c0360703241a80c01c2540b00d42c404659484c0e162090701e0052040d02c1610026081c0880c0130640041964080c0c2441304a5803513031070809080b00f50050030010724582c0c803030110340040d0145020b0f2005001070301c1d156242c0307802c1009840c6c05440310050222416001c000241000041e07200321203840303005d16100c51105a5404c0c1060381c0c1d45c0050154003002509034a4190800303a1035104950a4a0800c49103071130b00124070032a0a00380003240115009404613005c03400c41f00c16028960710052242c92640140004124035410016044600b54001ca5900d459400300b0b024070a62241090b5080300c082e0629000104c4c43e02019088103016411b0385404841408400100c8001e8030b0800030a12940001120315000a0760f4220004a0540f404c003216a5045000d0340d180d049a0240d5141c807040305903a05606625071008a84600310700d101c89001d0000781d44140a80810fa003108030180e1100810380c42c3d81088031075404110b12401d58402009455600d01002010b1103c035480d0002203800a4280301c0d103 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 853035197 1250 853033947 853033969
    0x1606030e0a03081b0307110607180501082701091a04030e06070f0204051008061b030115030e07030f05061b070623190c02010510061b0f05030a110c010206060f 70
    0x344e064000200482140c200c0c180c241d040141c036045844603070318500c0890303400003c2e50118190140c032081c200440e40c820004590040c2620300c0c0400108000c0c880d1102a0304050042c41a5075150342c40741c0c060084c0d81d00e2442112002c0150b03994540f500303580040c0280704905090348903040100310b0300c00b48204942049071142d4060f004100030304045041c1a4801e030f881c803600e031041c0f14440000f00e425036010300c07000d2038824502c803660541e404d01d40c075104498607419188042607a2902041b800313440400c5a440258007611000310184c0300c6060290070004000c00080000c18008040c2031300303031040c100301d0760020f812990000b81c1480c4901c092603050901d03003800010b940700009105545950b4480e51a022642520402400460711016800d07102d04032a000c01e2040300110801c4090b010750440c032118020380a001524501d13542d03070314003220b04a0805070307441d81c00402d844162940015031002c010481d0f03030040c03418019200000759908801480e00340511402d442004058486003410740b = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 853036447 1250 853035197 853035241
    0x1002010e0706030911280303020a02090a09020f01080711101505030a0c0603020d0209120d02010b0307050f040c050c0303070f0e0402030c09210a0807020a0605040b0711010513081606030e0a0308 85
    0x40445030747c0d0400a6a400782c0c801c05911420b005000f285426030240b06404c0203a5025143c64000c07440c60005441c0307060020000c04c248915a280380380e50400900c0402c4c41e50f0031070840040c40b101581824003040c40d41d5045140a039200140900101c0c11a004180803100b5a2070056990000e60b000c00001c2e010304c2e2003071074000d800c962680341c100741d0109107200300c0102d0b54020400d00c00d0f880201986c44425124450f080102c01c0901c2d80c06042542002c60614182e0810525008425003810b2a6510482c0c1e60b00020b48101c90118403a40c1c81800541d60040443c0c003503003103041000311540c252143c0d0007000d1082c0c8054203004852036000804d4a50b0038030110964028011604240c5504e600c08003040380f0548120601240140c011030540f8190303440220701c942410826035901941d008034022003418800144040100e012680a000d0090301910002c0c0040301032910415040c001150040c4060504200604081001c00220494010341510703002d2000c2c0c0300d155102c128102042c13486 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 853037697 1250 853036447 853036519
    0xa02060a0e090615180303040f060816170109020912160e2202130e030d1b1103191403010801090c0902070201020c15091002010e0706030911 62
    0x2401450340141070501200700a803456451692000204034000980c000303060140b80d420711040407403082440c285840301801404a03450035807540c084130045d8a65901000000711450200100c51001035028000503465081c000301c030b07401e00c0d2000b0307403c80b005000305240903901107801005565841d2400840800341d005603411440221201c031801100d42c02030b60104c0c14058045904074a5803030141d10940710034207148440401c1a030030800400d00d00c0c840340014503100e10048046107011701c0204514903d03ca000601d0b08100700c80000c04485140221041c003964100450400c00d001c012038141e804d5410000312090300002d401d0350010041740c0c0d500e10001c400303c008103003060158081450705010301900307200f507607032a4100d0048c0d01c04c14000031300580080011514600b8441c0b400813162449231b80484c10800381b94007082510594411881c0180e4461190348034181c024020310019000c2482d0521030459651114145c10f15402c481c10302640040f203c5110740302d05201c900a0406605401d = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 853038947 1250 853037697 853037707
    0x114091005160b0f0106110609030703050708040b030c0315040c020703030f030623040e0a030e130b04050406050a051005180c090a0306021801080108060a0b03031308011d1f0209030a0206 82
    0x113030a000410074020000411054550182d803208000b500500c2400c52500035841c045107075404481c00d1b048180e0441d5a24028400415450404c41c091489098500c8406483e450500701c040805029842040e0141e4a07029001c3c20055011514205490f0541002c1250201c03000c402c03030080c4201c0d0320640c905005070302d080c507620143e0040c04040d660121030600118202c0000941c580620b400c008002c20300100e4966011708210000400002c0700d800001604030150001c101511012603003260030396500d10400041d01220b2181d1600b02400002d040210342c280400b04602c01c1803441c088560342d003a640010701e81510b07601120250074024080c41d542c15a030f40b6050020b500302e580c13903004020310803080e00d442e540309208860407201408000d080d60b0b05c6e080c2101c0000c280c859007032501800200f004001d154030001d501e40080c0000c00c000150341d070240c28010076024007182070b035025400800a0342d610b0340b50a9505c00d0580c640740300045c1c2c0c07100d08100103446d102c5032100080d0441c1000c03072 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 853040197 1250 853038947 853038961
    0x240a09030c20031e07140603012d030b0603010501080c180411120601030c0510050d0b18091e0c0d330506010e03010e060a0f06030f0606050114091005160b 68
    0x10704c03404404498821640c6030742d1a41003031a500d90f240d98070140c100005000400c0b82d039100d0141d10081c81c8001c1300400d80050300d501c0038691002c130780e081a500d01c0a50130a2160340e040910655005002c3c00c000741c0500d0054400251441c0c10841550300c0c45004035010600b480400002c1505400b00100424088a4032034007032a00c1e5030003440103880c104e0040c03600242c2030400e590f103a030740c0020550300c46c0d1078100a0041900108400341080f90014804000040c084a607600c00f54000c012900060105044061005500c40501d501ea1207142d0032412442e18a600d5140c04a41042da001c0a0701695041400c114103402094039080e200c3c40709402c03601068450701c0d07402107010301c1081ea01c0071605032061080c9420b03106a1000b040f81d95100400195642700d80e6030090f00003c0c0d060340049070055403510b03500090216204e064a20982d01e600070001982c004a1085501610941c041d00b00041c84000a41c4242c2003440031050242c0000c51743c0401c40c11003481050b0703035802401404c0300d0034200 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 853041447 1250 853040197 853040233
    0x2706080d08100302090105060c1f02040807050616080a050f07030f110c09040b1503010e011a0a12080a0302090405040308160c081812240a09030c2003 66
    0x110040100d200380e00420450b4500d5010003003526000f82003c0a540d01e86006d00c8415400440e1944c103900403111888444d08030340083c6040e250301c604000d070b190350800c0781c40d6043c0b40d1746910041c0704000800c4504945c10b440b0703110560464200c0040d030313104c5960f110251124800d4410000760403000244110070140c0080880f520500c0c1682c038400310881041c0a03d9880e049040c030b05a21903076aa00040002d110a91102d6024401101c140b00264140340428250340b2041108010307a5154886071340d40c021a9042c11550b000215000300e0000d140505c0c00015400420300034003500d10019406a03214021f4045138940c20b0301074402c2003580340070b080040c410349040d141d1120b8600d0a07592910b00c1845807040031280c0d908150b841e4500301d044060072090900c00b110144d00043c13030200340e070003542d005d1055128914040d6801c1900c1c1528072550040310400500003020145480804d80109500a40b10000c0f1544400550016905c003281d05400490480c00305a06101c1c129460503a04120 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 853042697 1250 853041447 853041463
    0x90a0b240d05011e0f0b06161202010b0a030b012301050703080c0f0d0e010c020607300e0f0c0102070e0c2b020a030f0204212904050c01090f270608 65
    0xb178207040010b100b00c0000c000c0e80744180e000d04094000f0911455001c00d250060146d58034940f4000003e8003c03000c804a04048440ea105a5050b42c1800c010040000c10a0448111048018a00101544090020700b40d401204005020032840c04c0000f000c407c0340303004440c815124842010b03225503002070039502400d2110762658865007071203200c0d1100750000074a20b0060b00c2d01d4a60404152109600034101d501406190401c0ca00c1504691121030051113040c500722551f1010300040d000300391349180340c07015040c0c0c3c0504540c80403c08100c00030701d001000760080e0200e411180e0301c3d24500c00d21172003c9814101080c5508151894020310740303595004041c5c540c5c4030348051165403007201005049003c0c503c20710080700001c020f80b000d100d40c0b03a1219000f0394412080c40c0210104034449420361400d0380c404281543e1a00c052106000c800c1021591458003482c040100da400c000001d002c0700302178403c81c0384180c0928440540074100030703400c42c2c11403d40c0404200c5035640c0c84525643d0150 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 853043947 1250 853042697 853042721
    0xf0b0d0c030c0e1c120c12020304050a060305090a05070b0a0e011e08091501120c0933030b0f0703051f0e061206090a0b240d05011e 58
    0x601110035026500038040c0541d5900c042d110341010b000d491080c0803a0f09400440d200b20541802c0000307000860a02010369214201d0ba9006241b030030300d00d080005001092003800130355009000c20011a030702c0410a00c21341e641454041400d80700e0804076858203403041001406800342450202d00b4980c0380f4041e002503020b954403090698240300040d18045106000398154080e480c138058140c5010b5181c003034002640d0011111212803070000d501d210402030300940c004000b0040088280100d000c2c0741030141070411000c0040040d0881b40380c02000409420200031071100c404011003c040303407030240085402c0700c0c680380903240180e00203201c0d54080b946000400c1c0741c003000c60340d20802030003900e1a061211920754181810540c0c54403a084000b002907901a58410118809410a1241038001c5003820000c282d08107083c0350180503c10300a0400d41d03420f8034000505c411007010342d011819200d0a40c1c090388000c1c0141846d0780901400075018400068009403284c0c122079130b91100b2a40b0309 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 853045197 1250 853043947 853043951
    0x60d0303110a1d1c08090102031c06091119082502071802040806011a0f0a02060601120e0d0c080705030309070305010f05070909180b010b0d0513020306010e0403090f0b0d 75
    0x2001c00070801041018600713030795400d45400d200c00000748448014a88610140100c2e8100303880060060041c015000c449000181c685104021194003030090301d182800c0000fa960401030720383e0f2010600c014003105841000010808503004c07245585078050218480e1a005007880407501c800b95131440c8078400c0800c40009241c86d207141e840b8030301c00d441c16181003001030a2640d20700a80c8100814140d80c543c6001e12042005e000c48600a03c0101007001c0d254001d084645021000074092014184881c0341d07580c1050540040c440003c50320504511090130300720660491424504514052080018042c1c44000140080c3c02800541941180d01c1603001b4040d011210320780000b650400d80e06800414480d807000d20403502d0b1504011281c04a03004410140742c103a803584c0503020b03820313803205180701c40018800100620a00400d03a02c88040d0349030082c00405580400d82e03031001486000750b09050b0340041400c240c4201310300001400c8420810100076282d003080c1e00107512542d2030030190b40c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 853046447 1250 853045197 853045247
    0x411040e010f080307080d0e010f0c030b04200a030b10030501080d1d061803060c0a1206050d080702180f06013f110f091207030b060d0303110a 63
    0x10714804410b0703040d203140c0800b0b1418113006556080706034000028034031b951601c6168a010460b000d20403441204240034010694020450b8040c0445100c144042e0190741044070090351850f5502901002c0084d204c04550381e41c0c2406011001085c02907100c0d075104504103102000300d503041d0440c90580f003078007094a00c22901e00ea4155000c0f5080f0000b20804070440c3c01a007041d00d804006004c0304080341a12044074090000000d082c41c00482e034201c0c2c20440881c180183d50b0f48500791030913000110708100a5241001d0000704441c4e00f0510003081070300300141800071505c82c444451503070000c02018403140c0c10b00f8007422303460040032141c85000951025000141c0c000d10080c0301c401c030040000720040448621500100a070f00000c44541c555103440d03890f204541c00c080100f1503170b400c0065141d2503441d94010004207000713912034641a54461102400840c010a1580da0000710480300502042c01a16054010308400200006030b044041840c958294005160006003400008422500 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 853047697 1250 853046447 853046459
    0xa021305130b131d0a0c05011b020301020304120807050403080414210304051504050f091b2b060503100e0109080c01021305030708030f0f0409150e0106020304031e110411040e01 78
    0x2460800400b802c00141b0190400540d40a141b52051a01c0315040c1c07107440c180b0980100e82643d000792412110408a40340c0034051a900a02c0c1c83c2c1c006c65640b07000e916081c40d41d100c1c54030700e0145000750307184442140d003091002d40d1450080a504034540003035082d4108d00e0314401d5166082841064021490f40da41501b40b0440348040300c041c0e860040c101c002d0801114180b20344048018195621030b05040703080c103803c0700c83c80050000d0040302c1d82d070325a86d0324030414548488a0080802d850080c00d08000b40510b82d00410103511110059100113013100c62207541d580507010005010700700080000d018281e42d081900144034484001c41414085c0e44d6400a25581d581d01e80701d4070400741c100b484400c0306007040c13800409032110605151814641c540220000312813461184d205200c0e04441c040000b006020000c60041000d40043d6003001e140d03840b04081c81d0050316860b00c1d005609040102045842e6419501140c1d000d8000c01c58582003100a020340d80c0140a20040610014000156 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 853048947 1250 853047697 853047703
    0x8090a0c03032613120c05160f080a0b1b1e030a0b0907050406051305090708010e090309130c020a0b01090501050a080c0f0907020f0a06020d050a021305130b131d 71
    0x40c1c941c116440b01c403202c59151009003a20380e10301c0d482003151865104010410030230a044140c04c040d0b081d900f00b5480c104104802154540c40700013282c00c06a8840080398641172038a0f440b07400541c0d508450710702c950324004c0b140b00700d00b034841e40351117a229405010b0f215035026601c40c45030b911003003020205d0a400c000c1000c00c00c5030075400240040006011170361060003d04105502000d06080186c0c072080041c5d130114044401030300184415004101074000c0408094000c803c0d200078520340100321006c00c2c1c0521800c0c003032660885c5c950040002051081003030201e9580c1001100700a5616413000c5070141c502032150034811f03a4007120202d115000422641c1e40c0400c000c0c41d09220540034003c1c810700d00c00040031181507005081e03500ca16036900b40540ca48980c031401c07006945880010b40300c011a840600015159803040c045c00c50101c01030b11520b01600d50845040e800c00944c683d0700c1c006020f0021100d41c0105101c24045042fa201d40c00c40b10401e48030400d0070b059400042a11a5 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 853050197 1250 853048947 853048951
    0x7210c15030b01111b040917073f200a05010c030b03030d0f06080f010906051302090f0a0204080718051f1e1203020d0807020c0a0608090a0c030326 65
    0x4640d410603170500440d070703010011001814a0240010640025940300e4090455581480c00c091070000100d080800040803440e20300200034903d140720107540040d02e907070004010800d0305800c030045024100700600800025003a003041c2c484003c03039805114901e41e107034050044200c80c15800d10150520032800703800f618480c0c0b0340250003581408620702c902c0000d40620800000004c4d51560003041c0c0310300c14483c5c0d40c100302141001040a205a29241e0f0880341c0040c5207940c0210414600d800581d03e14010755003051001604034101d884001da0032000b44a15480700c545480b5460b4005400c4c1c10a805901000c40081d4040006640f81c5012440c80300e056520910f00350202270302072004010203089243d40d0036100f030782e000096840c2c01c1f03200000e01e030240050340546d0041c100500056401078841c0c0d80314010b131010703104009501011914520a50003200180001600015411681000190070403900811540c21042d500d0070054082009402c07a09010210f030724075001c0604500d80303614 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 853051447 1250 853050197 853050227
    0x3011b020a050d0305010b120402061308071e050603040311011407020a02010201110405031207141f0e0a03021207061506050304231e0a06140a06050306060307210c15030b01 76
    0x524207005659580f604032300080040fa402041409030103207a4102040540145c05844014410541061001000b02041d019490258090355800340500e40301c00069a4200d43e141c1408800820f40001980c0900800f07001c42c1d0100d541c80042040f42c540c0003ca44850301d0007a0001c002d50b50311180f0b1480751340705a00903250541d0001282c200c503140e10303500070031103140112182800107411884141c10300b1421400030280139810403a190500030306116000724506004024080c43c00d5594000e500c601c3c0110700c000b22031300085519000c0c0a041d810940e942c4081d90124201151a20030140441d08146c40c156542d02c1010112303190b0200b00c00075490718603914002001030b400344050844041580102c00c4000b0b01440c1e0303542c400070710f1600482600800e00208044185880b64103c4101c600c1036000a110707511171028840d45460108038281a5a904030300c2d0b5071004602d0402c9543e140c13801c1c0e0000c2000e1000140081e007880c4101034205070340301c41d60b400c1c01400300442c011520b984e1010500 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 853052697 1250 853051447 853051469
    0x5252a14060702120d02060103060605091e1b0403050d030501080708060a0c0516120f02150604051e070c0b010b09130e010612050c1318030e03011b020a050d030501 72
    0x40d19142180242811a100a08104010260241d03180c10802a0a02080542d1120006000300984c41c02280080d000c10f41d429103445c50301d042d103011055131058000b0a582c103074102081400c10601d0f200c21426a464550640d070703956901d41140d90b45101c072055400a031619002082c8202c0214400c8200c8400c10028116a21030390a50300013045c88180b0b120a1003001c001c0004001c0d000198040c1c614002d0080100314071320b1840140800480030002d4086400010700240b200400f00d5482da001001074070002181d035564103109140d0000030000c0030202e088071041141c01c540c403034030407280f49119004c00b07482a41d0f15480c10300320340516460a6070000c0452015464150b8581c0107182001c5814004148a81e4543c03000d501c40342401425141c0741c2010aa18000381420821100222203081041011034a035001e10980c0d40461000101000711940422000355004d4202c62156815440078000f050750b8140060b40c0d80c01c00c4601140d10703000f10f0080c1e10078203000f481941d0490351501c10b6 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 853053947 1250 853052697 853052729
    0x60807060504031e02041103100b0405011215092a05030c0a030e150702070914090a140307020619030b100801120201090306061d160c0305252a 63
    0x1130007081c10118190514400d209004c01c00140c4e980d4007c2d00c00904101d0744d060398a0500c12502c1110b81c1194100c116149030400007000184d0b441005968400c0e00044e0028003031682c003890b07095004490784600c4d009800c0041c007800982ea0599415031a4071400a1000350025185c8140e9080c0070450340440910400d01c02e4444c0c0354000d8024103500c0341400300391442060f0352400b0540d6070100b03684076001031388061803e001000e40e91007980900384003103c00156501e400388440707694071910b0000a0000c454050000d9100001300142d44d5003d40c01400a80c803142c03c4028200f240c4029074030480003070700b0300c0c0d488011401d140403640702c074807496601c0021aa09000c294848082260000ca04000103a8000401702d40a071041a01a2400100c030017001604c0d00f81200072504007400c000a40440002c5095041d41c0082c9440e51031a814140651a4042103404480441c000784010040c1c0b2408030ba20410007a5280f21600104017035000b00400c8075012607002c0503000300c1d004001408802801c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 853055197 1250 853053947 853053953
    0x3040506071b091e15171e010b1f080c0c070e0f250915140705010516140405120102090d0b1b19030f060503070b030a06080706050403 59
    0x40c2841c034020510324107800c42000b00d18503019020b92140d25800c0d600c0500c02c4c110f1100a6078200203c0c82800c0034000b00351000c60328031115126104810100c9210040284000b8040c0300150f400c4040440320901c80c0e6100703130080d01071701c9c0c101c1d600d070b1144051072860703140440555170303183c0001c1c242e40c1e0308020b42c1e40f8141306001c41d40c014030803a201c0703121360080000c50f403102c078101c07910606024208142a00b0b03d640c10042d40c10700401c0303801c00344030844110507000d5440200c400458407016603c0380208406001a82d010116044110303050000056035414444c05410107806803902c00f2800780c01c80b845010403030300c6d0003601d150300000d104108400c101500e040503903117008680380c6000626003481c1c1e000140282816201c122441c024a500700402c0d0b1940d4440d841c140d840d1003046501d4140780301000111078100703085ea0700a1540d02c002800d102c81040e8402c1c0081c2002030100c0d03060b00c0c0c4598071407103136401c02c480e04280582811030200b240c0d400407076040c044916a0315842c0c20b0a0850f5 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 853056447 1250 853055197 853055209
    0x501090e13023109050f0307031e14030f040311010636140a0b010f0f0809070302090702010b091b0304030c0f0213060311420a090f0609030302030405 66
    0x501c000101d03e66428088924040c1c0307a040d04181101c024002644015450268105a0084100b540c60741062201c64003082d08078014034607101c842144081c110072140300a8400d8000b1010303440d40a03001204001c008090291240d0045020391119201303246c034003191500f6640039028104081039911128462030f020004400c0100201038050925595000382030b00803511a481c002e010b0081c41d0041c80960401c91050001d001000e181000d5200319810001e007981c0900c400c0744040040f2140080c0450206000c80c4011310750050500140f03007002c100080c0a8035000010798800e0304040e001c01d151840c0d00003aa00341d4030407406003d04641e80c5880035540940c03012001d5a00961050000005a443c101e01401c1103000d15000031300c6a0460421004201c15400502c2c084d00a860f200b03280c818103041161007480c1000300711f050141843c500081c4540c03088100124901000c0391001442da00720030001c4c00e444d6180d00005101d075440c0c5044650a02c0c038400034026801c10081480141480 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 853057553 1106 853056447 853056469
    0x8040f09090209010506070f062c06060a140109090e0d0e010804020a05060a0507050109140c060406050a030903050408030315010e03030a050316020f060c040501090e1302 75
    0x42d601050703000f00180241445943c001c80c46c4403c0200e611036940c80d50768003d80038060030445e05400c038052903c1184003152007000d1b0300081444c810000b6403e00c1840300503c0d20480030710b0111040d101e46071110380681003003e101c0010031300c400c00d8020006c9032180b8070000c01e40b290120600401240d0010043d504001c000006d1102595510060b078054480c200c1d82c00e541d4024041040e6403030b10880c0401007455007080f205c00207004041c81a00c20542088003035414115001c0c0c10032605200c3c41c041c0c4401b181041c01070b605014480c0d40b0007080740d8841d0070004d192503100c0310f07210f245810440c0c03001003100c1d04000c1c41c1c0c09564002c1040749422029001581004940d080240113400018480d60340c5a00a03140c0c0c0d04051301c00c100310442843d000040d03e801e82802c0024500940c003d0140703034046a080440001d1440301c1303484180c40f85200b1103056155420541c04c0056013404 = true := by decide +kernel

theorem cover : BRFrame.Cov 852877697 853057553 := by
  have h0 := BRFrame.cov_init 852877697
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852877697 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852877697 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852877697 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852877697 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852877697 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852877697 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852877697 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852877697 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852877697 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852877697 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852877697 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852877697 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852877697 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852877697 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852877697 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852877697 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852877697 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852877697 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852877697 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852877697 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852877697 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852877697 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852877697 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852877697 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852877697 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852877697 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852877697 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852877697 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852877697 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852877697 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852877697 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852877697 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852877697 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852877697 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852877697 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852877697 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852877697 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852877697 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852877697 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852877697 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852877697 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852877697 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852877697 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852877697 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852877697 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852877697 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852877697 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852877697 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852877697 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852877697 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852877697 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852877697 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852877697 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852877697 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852877697 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852877697 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852877697 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852877697 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852877697 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852877697 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852877697 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852877697 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852877697 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852877697 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852877697 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852877697 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852877697 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852877697 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852877697 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852877697 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852877697 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852877697 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852877697 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852877697 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852877697 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852877697 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852877697 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852877697 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852877697 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852877697 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852877697 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852877697 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852877697 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852877697 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852877697 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852877697 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852877697 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852877697 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852877697 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852877697 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852877697 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852877697 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852877697 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852877697 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852877697 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852877697 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852877697 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852877697 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852877697 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852877697 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852877697 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852877697 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852877697 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852877697 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852877697 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852877697 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852877697 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852877697 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852877697 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852877697 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852877697 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852877697 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852877697 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852877697 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852877697 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852877697 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852877697 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852877697 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852877697 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852877697 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852877697 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852877697 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852877697 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852877697 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852877697 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852877697 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852877697 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852877697 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852877697 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852877697 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852877697 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852877697 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852877697 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852877697 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852877697 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852877697 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852877697 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852877697 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852877697 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852877697 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852877697 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852877697 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852877697 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852877697 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 852877697 ≤ n) (h2 : n < 853057553) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
