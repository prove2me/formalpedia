-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1425
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T02:55:11.885729+00:00
-- url     : https://prove2.me/submissions/ec28b683-de67-43de-b775-45796dfa2a2e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 256115107 ≤ n < 256294964 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 256116357 1250 256115107 256115113
    0x30b012a020d1b08010605040b06070308070311040f1d090a0b040204020715020a090807080307020f040b0307120302010e06011401021c03021b030414010c02030706051e070303140c0c 80
    0x6410390a1000d000e144140071100c00c01c003802490f200c0883e812140c00142095000032039017526160910040394140c04001c0c2c01542c00700801e80c042600940f4041d0400d01c0c510b000102d14021180080342400745030001d40198000c00303000100a805040000c800070103d4903007040c10340716a0309407a40c2d140c0c50b04004000c403000000250152409030b001c3c0110707a00400701130061488400e151000c907030105c040240030412031101846901c1c4100a400301500030f0f10011403038050a6000034400c400c1c1103650f40e00c29602c503100b1034a00e40302804210001c210203014011480c0f038918004c1e02034070320080c07190718a01c919800041c0d0040111404c042002042e0090801203224a04170480440402c00041c107242d000c003c03807003104010600481860701480b000d5a201c5007071650042d426824040300b0740c10000c1940030200565400302e800c0d42103c1d000e090071680c0703259000800302c4202d41c00040c100310541c04100f02e001d15801d5044545030200b2520340160650315003c485449000703044d41518103078 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 256117607 1250 256116357 256116437
    0x9010806040b060a091416030e1207050a0210120b031903050703020f03041d0105120d0804050705061206090f0405030a0c020102031b010b1c11090c0c060403030b01 72
    0x41d4103010620b400001c00380400d404e60f5202d840d8403080c1c585c00b500540c81d1082c2130342084107066809000081c00005840c082c40480c030021075469817100b000004100d00324002421004020701040000406940500241c1c81d1060000c0c01034900034200001084950405e520a8258034021a104010310390b11404c0f42a400010340781103645030000b4400300c0c25441101c03c0800364402c10005131000303042d600d240f00c42218803911702c2c0011400682c00b180c003484540c1c902044005000c00d880c4845060303490411040d42e25030804500d4600c13294441c1e5006400000e61010759140d01d40200d100b2201030750180310545801003040215002190080e0554105014070341203035110315440400e29005104403410980d1791011441d12020390342d000c0c00145c0d500c070b145022a040504c040050220040b0a0802e240c4003520b0340c25020b070b80c004840748031348818400035207155140300607641e00004031000c0718118030f05442c000e4003c056100e0f9241c00f0884031040c4024085640c140d109030174150202c604804 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 256118857 1250 256117607 256117613
    0x50c1908120a1401030b090f0615060a09090903020109020405071b060f09080c0d180e0f10151823060906161217150f011e020102040e060901080604 65
    0x155a015200810641d1522030690b00c03c08071012241c043c40c01800c4d00310442c100790001524012681a2003080358000500f0403020954500342c00481d06001d8403e25542c1810680468062009801c1046800d240006501c10b150f030540c0030460301740c400e440c02c106a44803001c041d200d0400700c010b086035001009040c01d0000703440760040f00301c86004580100c1c0080749590b490389a9007108144500d076a1003665a00e014580c4200001c0c421008800090744007802c18031159001c0c400144007030b00002114001c168001c002154a50050070340c20074220121114440c0180300010030404c5034140d5541190100e415450351441034443e0810303841d4102c40c0300c640d40511100d900003c001d5a48400288280c2c000124000031010f109803044000c00500860364034060942c10340342140302c0c1030b80e40030420002c003035101038005030001e80308842d0115445036940c0100d854101e140c007104000c418031230101841c581c054000d4030036901c0b4030031044400d6459005205000d8800d1007a0225640204003080c08 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 256120107 1250 256118857 256118887
    0x29010c03180e0406050a05010b030f04020f101d03070b0724090c0e07020a020604050f360a0c050a050a090f030b0403081f060f02150106050c1908 64
    0x211511a08044414032000800528000c60310b03840002403510074000c000420640344a62a48600009000c101a5050490000b0070b80001081a0411590f0402084c01c0d0b5594100d941d5031300c440108038010246009100401c01101214013104284060f10380c10030311325001c228401030b2002400814102412078650204000d9007a0b50100d50b00c15041c0c1d00040d040b090b000340082c0c18001d1805801c3c103884c0903269041010014900011500200741c0d00c80180c0c2c3c6e0404507821160308807241170f0350000d440c00080d280140c5031204544406d01c1d106004809030155507641c00c098110700000301e5661546c460340306030b522140841000801c108144000c503406040030b80061605032404083e96620340d00540c1038107440340c20585d030f6a421038081008060b802601940d0007803102100c0f0804a510005011079070038203002d1007081c455408407900c50240308000404103a18107201188880d42c0d52030000d0055030000f10b4601841c0540c14100c1c000c104218a43c81c0c0781640804654540325005a040760 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 256121357 1250 256120107 256120127
    0x3051c0509030708010c0f020a020f040c020c040923150a021b070b120a020c070611030f070c0602060108030307081902040803070b0609090c010914010e09010b030a2901 74
    0x41403000612102000e6241084028042d0450500000344c5001500016140350304900c0c44d8411903020899040041e11009402c000d00c801c00d44011a14201d076034016814100f220031540d80103032604042d04140822004000c401d03c050315640c122045e0f4441072503464801c8103400340b001c3c14154000c200300301c1442c1d000b4420001400d4002e04215001e01d040d43c20034401da845035078001e4011400058000b6112452a00700a01180845c13509106c00034854840301c25100d040280680101441000c800c00d20481d40078040701c8003407540e0350340c81c0d181105001482d0b008020040c42440e001045101001040741e000c0c0748070352204440ba0740c59040f4050384050156008039142e809110000c0c00c1d1b40c4c2000a082210710454100382d05187c40818845074510041c21a08194001c8820509598000000348166801c0c0c103034107901c40300d6040050f10006107260303c80360000392420000401c0105070000c4c5000741c4c0301620034800002c542040030700018826440400340d004a07002c10003150b018100d104 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 256122607 1250 256121357 256121413
    0x50309060904150303081501110a02040c03020912100e0606010512070216080114070e0f0f06090d050706020c060301061e2a03020106090204060818070306110a0f08010305 75
    0x700ea0f04400000b84908210564821004206c03d00709204c03d00441c1010402078820030701e042c2d0f0f036500c81001e0700c41d0b6842c0c50312006030041c0e950b034804a2203644603404032052124007038100f05c9000440216243d680c00140d802e65079451034040c95034140e0304013241160040c50140e41c3c0a003010b03a00d0681151074034014120300258825005000020001c05c0c0f242c10003003228000014811804040ca103824000c0105040c0030820501146003260b80ea001e03074104207840a40b0310811084100000c10789a11940a031168040c0c0c03540b40c0f02c0200100000d41d0300c1a54001d50030303100d8a00700780c07080c0103450100703000344804174414484080a002026032650001c1d81c7d6850310010014040e030f019100341e0303d2081c0a0040440440b07810003070540900516000342001e000461074549808401840301c1805000480c16000c0c4000500c0128000c010441c05160041d20400190003002d00ea0600c9a00150618010030404828010303001c1c002c2004e10304803034110b0302038641b9004208102001c6400b82c1089 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 256123857 1250 256122607 256122611
    0x70e0c0418060504140105010e01020609060a200c010e12180d02030c04060e0610050301080303010501050304051e01140a1407081003060e03091f02120906190c020a060903050309060904 81
    0x8580d501c83c01010401d1044103145c00003541080001401445507140035419980100306020350000000f49203640810070304e10001d45514420800d60a90601060340007840308080b419014013241035110a940306156400ca5003210442c104410507406034a4250800280223a5410014140045a402c0b02440101031710280880300d00000d00700d070540c4d00031003480092801040400d040209412115490f1424150706543c901406250f8038481400350303d040000100216040060401446540d1a05482401c80c00710f0344241050013040c100140301d084643c1d034000724162207030310b100d2080240300040c2009000c0d951980b066813001000340c0304220308241d180000000c64405e2095840220409024640c1c422104007040005401121780c1110000b4040e0358248454000402140524020742016110400365000030043e000301d40c01d0642c0701d000c0b02e80c2c0d020710640c4406250384140c42280c861529039141c01e02110094102d00000b007a0b64800c00400d8a03510301000608000f01d401800 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 256125107 1250 256123857 256123859
    0x10c1b061a04150504061a030a0c0212040b03090705060c2505150405030c041b0804030c150e011a0102150405190b070905031c05070c210203070e0c041806 68
    0x104045071864801109440d092210600132407409000b000010580e47d40d01c569440a148501030031440040c10310341c000d940c2c1d030919004080c0244402c00d410080d480c2056103e59662948005507402100c40303101c280101d85c40400d640c68550180c1d002803c94034010308800302d609201c0d140b00000440907500342c1001a000003003940d1520440c00c0842d0001400b1a20b480c6003906062400f4007040f5801c0c8520700340414081e45110441c3c02c0c5041a51900e0a14415115410b040e00c44402001e005004d10082e410340550b5550749030405002d1801c0e65000f0000a10b80d42454080740d4640704080e80140c0091010100c404082d601c0540c2080c0500c080d20300d145a09c24410175010801c50703085440c1d0021200300443c09030000d2820000304404c1d0040c1581e8082c04a00f0b94540290900e013109021000c84c01c0004d00c40d034510500c015002e45e440494090418803041f80c203100722948101d1180c0b08600c80824440d83c00300b00e25004184407010582401d091110140c003c024440e03909884070340d2410 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 256126357 1250 256125107 256125109
    0x603120406030c08060a0302060712050d09031e0c0804051201021909060909020a0203040605031512030310290918070801050a0501050a0210020c120705030309010c1b061a 75
    0x240000c00d202e03200003a2010002101800c42c100062903a44141c0790a0300400240c1c8038a0200c0e4419503220600c00d154405550080ea00c0b8091103002c507244030300c0e11449008268000030b460310500383d500361500c80d0078040c0c0c50440364603030300c1040100104000c1c4420001818950848420528010700250a040111104c1800c803007200d044c0c040040e0410008003d41a00701041201030404043e0541c5030410000020f941da01c00d600c244000c2100010024982d0303500310006601442c4018420600c521010303242039600d404c290396502c0c620a625400180b511683c2d00c2110b0b02d2004c1811841c008011207103c1080340d005001c40e15080481350b0489460900c0807403840e807041d1540d48441c050703541410f083c0b0000b07441540065041c8201000a00e802e15000215a03250a0b880701c2c0150b0f54480200343d05040201c0300c95880b50b0b52a010030135030104500440554841c60707441340200029048004211a01070ba030f0351003083c4000108041e40e0104046422086c0c82c1d1080088050303607a100c0c04 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 256127607 1250 256126357 256126393
    0xa1106090d060c030b0a030503070320030a030b04150303080f070201140903030a0b0d021e030c10050309010e07030f08130e04080a0305060102240604060306050c030406060501021609050603 83
    0x141c0c0803a41160b031004040e403019058860f00d40324100948500800a0641c1d0301d1550303912074588007078140710a03099802414565810049400c81aa505072501c9924400c1d019000c0c0c420301500c28440c070706208811380f90742000a01c5c082181d03096a1000d90580719100a03142007130b0003a00c800e0455403149500e0049400c0c1c01c6506000301204001035541e03181448280f030403180180e140d0b5106074000b490810140e078440c070120b07259820900400c0441221900080d251501d450b0b14103400c481d0403a0021071303658100b4090b603c2140142e0007809080d40c6283c1082c2c40b04001c0c00020b203606465112100031078a400c02400340d070a03080f00801541c2d1b4460210700c0f040c0204490444407014000380c03a5000b00d40c14061150090130a000928800074007500d044101041c0c0e0f51000c00200441000585698507904610000c40d000102041582001d054400e80da600c1200c0a0b074000d4140100000c05510001c2e01280110070444c1d0400080e0401c0c60303540142c0b40c054510f55051080e01e00d0030640001740c2c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 256128857 1250 256127607 256127629
    0x10081308031f0509010b030a1d010501090906050a0c020304031203090515190c0207150306050904060e120f0306040902040b030d3207080a05250b06040e0a110609 71
    0xb041c8004040d07000444002646485030055030040b0002d90040140003084c505a940201d004c01c1c0100341d18040d050180040d210101e0304900c950b00300800000c208107036501440c181c038002d25091103c4d68032007c0940603181d170b0305458001684200810404500742e802540c210900301c0c900440c0b41d01090302c4542c540400c004503141e1071010f045c10320880700f455101e000c0c5540388444091160b1203007040040e460303c14502c6180030445000c6000750449200b980402d014150051030300c6a01e0600d07050201c0180140b0510f9401c03481000702c1e00031400c8040d000c5d28141c00c100c520071455942d41c4001d200141c600110200e8006851300b10140c45580e040c41381902ca0b50300741d9507800c403041c08000c400070506404944090f00c0c1c403015040c1d503240751034502107542207600400301079a21441254111664403801c038104104000c820204001c10580c0c2615446150084910031800e4950f001008101c4034100c50342e207103540c04841694001500c00700c14100c40c3c20001d00302824000c030712011072000048 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 256130107 1250 256128857 256128871
    0x40f03050106090c0f090b0c0114010801020406201218060703031a0f030606041d12040807060807080f062706040e1609020d020f0406030902031002091008130803 71
    0x64802c01d020040d4584107081c3c884450f841d06034900d950500f000f030107030720040c011040c0c0c3c2040080c03100d440c0f000c2500441c00511601000c202c0d10b41c0d4805a40d4001c0d041401060002071012804400301130520110425040ba250013420170700c20195080b86841d0721180841140c5039070002800155a00c00700980784880c06a140030840d401450700301000f04402c0c0310a00d2140c0c184041480e81510001003869210605450001d64400302c00440c41280a000005000c81d21030b41031007003050a2524040c00840b9400307821104440d85a481c1510110404c50702000020200400111403a40c10111300d03800030001f5050071038400f140c0201901d01d03800d10310103490350a180001d101d614102446003000d50b00102010702001c030480e4094042d601007511070700000707030340200d01c1034603021a560455542040314551035907250f5841e40081d020b05a2404181c2c881d000320207440c11076492a008558401a0040c0000d11b401d8010b60305690003c4003800c84072940c42020701d10000120040000c6019441c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 256131357 1250 256130107 256130111
    0x403050d090902031501080c16080c210a0c0204060905010b0c19020d0201051e070c030b0a0501031101050a0309080c0c090903130303030b060706090b0108161a03040206040f030501 79
    0x80545409010306240b544488941441041001003080314142c0400070042c003440d047c0c0f11030710344020040d014040c2c41d51140080e88404508010440264000c0c500b2050000686203480070800d020004035524502801114404100c0040c4c3c180c4241c0780b00080900c01040000e01c2601c401c419070440300240c0214000d02c20000704c0c010105d4080226040042d4040800100b90300b043d4003140722102006d45c028140040803c4512000d0b0700c00c4141c0c20000f00028a298907214507041502a2a1142c8803e40e40070310007002080354175a0340c0c056541a40d40040703254004000d06001101c0d2035100915000c01c02d99a8039603d4001400c200041150350100030041954032820002c102c582d5101501080c03199000304140c1c41c0074450054000100c80c0c25050002c0d43c00e0035400480d003240b0440100074a42c900d4440280300700841115803505843d44501152800582c05421040301c039518061904161811410a00c1c0c1200b0b04004640c03161000d0580e50a00c5d50301e4007030313000441c4181c1048500f65 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 256132607 1250 256131357 256131373
    0x605030105040b0303030603070e041a04120f0e030a03180e130204050603070f050402070212061f06050702010c1b0503030d0e19020f040905250f1703030106110a08040305 75
    0x460b1a00640307080c04402c0b0007641c40e40c14460002580ca41d054407405003d9041c0307e000230180305680000740c0190b401d01d801131500e840d00f490500b040500da09404004180542e09c0000624454503009002c1040a001025600402e89080c0c0c1c0b000b0707891303020141c510056540801d01070081a440d501a041e0032445415040181c130400c0207459009014034040e038420f000030070225420070355541c100c0304107940043e44d52a031400070a4003814684452044e520918050240f05040503803400802102280382451681c1c03143c2c41191181701d40716000e4002158900b100d03001c02c2803c40c2036003008100505800c01c042c1c0c2c840120342580c0081c4600704a80f40e542c2c9544207550014070600110405488403548101e4165001984200700300c0010340c0a10340d24450388040010030481c03007001746038040a040c1907034035640e08100000c031540584001258498000200f1041c0e2400740d800d0342410002071030031603003030080880b0700b4148621040b4191040014080108003844014005980200c0281600c1 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 256133857 1250 256132607 256132609
    0x809100603051c080903070311010b091306060504061802031e010f0e0f01050a0308090406030804090209040b0607020307050904150c03050603010e0a020306010b18060406030504050610030b042a0605030105 90
    0xf11800c0700c80750030302c40d036131041040302030b400300403101d40c03d9050400054100d6108851401004901d034420f0300041c40d03c082c00841c0c0311680d48456124810101400394589800512050720018410403880e00d002c42e43c900c102154903000345038040e03010448415509280064070411001c00e074000e8201c1d460010052001e134010340c0c00c81c0da1102903170301c11101c02e5140401090a261541c4009009c5480102d02480d8640c0e82c0d0300001c0045402c01c48007500c940c0c903011800029844030500038800c510b404902043d0303040c0801501c00d1550002c01405081c0d00d810305000e410240200202c42e001e41e483c841035420020391144564681003554006a107242580a260856a01d0f0300c2301d0b000d07580598400f5005a07400102c40307041d11001203485494a40204850106200312202298002800b007008111607905900582c801d43c0980103c40390381c0c071307003110030940351480e80000351820756050001030221711204080001e80e0f0801840c2e82c074003110f910000b10720302d4260708010001a0000010007035 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 256135107 1250 256133857 256133893
    0xc17010b0a1403210d0f0e0f0c100c0809060a020a060f061530020d0603060b0a050a0f06031d06070306050f100503060d080f0c2d030703080910060305 66
    0x84c0150b041d00c042c810240c00c510540380e901a00242090060304c4c1c8418005480c0140c000641c1c00f40d900d0101da188090074070788607456141b080f0480c0c1c040c0c440c41e0320459860344a0b8046015007500001c103145820304c150f007030040691003c8446030542c030514241d41c0c00104148200d120500c1d08110001d03d082c14240190302500b0340c021b2170b004000c6c0414013200129544000700d404203100d000751400021443d0503035000303402841005d06030689018000814019182c02c2400c07102c404880140d00c180c2ca600c20005004c0301801000c2520004080074000c450190340400400542940c00300307202030f142c2d1500c5140050881e0802c0000b0b4032160204000d040c50100e8000741803007251031020084100d44000e10b54040145018400c400c6240e046090060410844003d0640001210780d43c0400f101e070a0340d103031088a503590302c203034201c24241c40521400702000c8800d913280015503e0f06070350342c4080b10ba034940642542514041e41c56103d11440041c8103001c020341c400c20140503030411007005418 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 256136357 1250 256135107 256135123
    0x306010914010b0a21150803030406110403050304061107090615030606030219031814070f05010e0d060b121e010509070e010612090b070e04180c17010b0a1403 70
    0x21a0348284041003c4d13a400c0008801302c0d2a4150310301410401c4980c842016080c0300c001001010b50029000c2414440480150f100b180100800d01c0036008445040c210b074400e03444050000d401c00d02003845098400d028000302e541c501d80864401c261170300c884500325491944040058082140c030015403a07090f001d0b010083c01d00341000c5040243d07040e00740d440b071981d0f001140b00701552800c040019203201002150515000030329040620100341c25185c1c1c88001c1d008a6a1030f8001d01000143ca42c40340303201045446002d04151070b101e041d941c0d8200a007100320038a59000c907980c8010810030341e003080030200d601443c5e50b24500c00103004100c682101d074003504410058002d0b200a0012509042c559411166207244c01c000c0400d000c0b1701e407801090120002400f00c551038052180803603206203901520302c4112010000380742d4030028603000740400000100700d070448c0c2c0130400294202140382425174100600101e41c0c80038000000f241c03406c5a8001214400c40b0780402031241c02d0404c0800 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 256137607 1250 256136357 256136369
    0x3071d1e01030c080f060d0807060504050a1a0105150d091a01051c0c06110a080d090c0e0702061609050405040c210b06210d02070501030c0201020f0423030601091401 73
    0x201c81c4e080000d081005c00300020302e400d0084098460f000d0410507245c1c200d500a035080503081009041500d171960302c0b00c2c0c800302c041c0c803403e513400042030025000d5010030303048410040802e0043d4020710400d400b560002e50141c4902035407046208041102c50755021515011090301420660502080050b801c0760030340c07a0010090a2044080000c10348000c000580341d0a04103240c0c64503042c04200d1514061282c010250b100110307100c429503c10784c101c103d441d4030604225240036180c2d905e004007070401f101d46000582c401c0d0082905071100e000b40440b5421180307807654449490702d002c507040c5c0320140c0d8201c2c0c3c0040c1e400d5040046d90030780121903a80380210794a00b9403141450710362116559010b451030b4460244030a41100000700003404586100802c1c040c0c941d0b4500312107010351511341511031076010a08020382e801100344103200310341c061581c0e0100c07a800c0c103042400340241c640c000c5111140c88550f0138982c1c02d0380d50b010088a8001d114032b09000c0380d60900001c0c404100001030303000c1 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 256138857 1250 256137607 256137617
    0x6070906110727060f09090201030b0405070f1419020708010b060a050403150f051603050f100b310f0807060e0d020312040b0a020f1203071d1e01030c 66
    0x18840910b441c0800001c031041e20300e000700301c010b812040d14020315240e4480001c104003010000340400f41078114051648c002d8900300f04000a1009000544200701c4541001072628040015450f019086190640102c01c80a030b0402060b41c0c00d01c0101d10040c8018000769000b4041000340000074018158a000c0c05d0300c0b850700304100010702400b07501550100070711329211416200785841c0991301c40c60302c42070107a500f8041c3d801e00a01200144032010909000241000009801071310020051400727000405100d920062520340341c00140d81102000300c11501c0b9509005544000c001545045a0516989204c1951803c102008484190f600401c2c81d50085070040003015080552130f0104c480c1130f20158420042ca2000074140940c0820146090101003008140c4403041000303420310701541c0d000c0307413550200c0b03894195440404010402c003140d800c00008090a1162030401c607442aa034031405041481d4000040d10841c1000721440045108680e90501e036a05000c4c005400300c8500300 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 256140107 1250 256138857 256138859
    0x6051203041a031305070608040201030f1401050607030e130605010f0201110906070519080901030b030303151c0c03152403060c14040b1b031204020108060a0305060709061107 77
    0xc0320b540c80d44411a0740c421080b0220016991030030020011180c6944081a00e2071242c90300c4014000b448251001d07400246041c4003604104080d105030301d414035084203c12101da180808210160b8440c0c00c0440800a00c072142e9407842e02d840d624007030005001e580100c1d41c2800c1400040ca400e00d41e4004e2011681842030f02e090042c200812100200300c1641c0a42d644e0000341400741c6402049003100100700e40a12042c0305001c081009024105c0d4240d906100211106040540c3c0380025680f401031501084004220352a000d118050782e0201c100b0070300b50400d4152103100403090603a10980e07003840304000d6400140018440ca041c215600c00c00c110410401e900c0b0780619880900000703261698921542a8040c003611306203031404003003207010380c1e515107030000030210f074001485021020941075400c902d441000700c16107600100e84450948681d9594004584416001d003031260400781c1e81c800071000c1a0140045032081505407510320b48a1b1500f4001001c034250420842e09940180320 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 256141357 1250 256140107 256140119
    0x1503040309050415080d0306060f0f1706010c0c0303090504050c030f07080c1b01091e0305071704090603050109021816030908040503030403140d03020403030e061b010f0605120304 79
    0x803420054482c1034400007002c0d10041003c0101c01d015030846032451192041c0e445645600d5041501034a0090f5180d250301500082c0070b0702c0c29549a5544404108030070b0310001852900b0780b01641c4194145400e100d401e01c2ea0300c1c2d40240401e1a0416400103c1c525410301079404c0c01e000b101e80207204d0542c4107142d413518410300550444054101020070610784045600d440c040000e0f1100f0709030364001038540c3d404044203940207108c03081e801c540e84406460b80e8003045000d8003c12a259802d40c5801c1e18000d00c641d101150b13003207200f1060081d548148004114180b40b0300c80d80010310300ca60000582d846443c01003014454008a9141840b000d0a040094901104101c082051506d0601048400e4030346403500c8075004075007240c0e41502c03000c24008244040b4600044944500c81d050740c00342e1b54002c00407802c1e03104901000e404112020104009410007400401080c210904c0440c0d030700ca82911140d0075203080c000008216500c80f4828010b600c2d2010120301200133842c02145000d103451 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 256142607 1250 256141357 256141367
    0x418060b041223010509010618052a0d0203040c1d0601140703020f0607080f010b03060603010605180316050a0501050c0a120207081207060615120b03150c03040215030403 75
    0x340008190020409491140000003400144a40683d00c0280b00c5843e146407441c4c02414030703200d0109174420b003110b184440803061040c18080c0c0a130070744880046c00c5800111590030140c5800d0641c0c03203400c22101044001d030344051400350b403041143c0d84401c5e24000d489803000c2c2030305940080c100500800c3c0600751b0780200399240c0080490380d40b0780c0c8504282c10142c0c104900c40c00c202008d8001d000c200007001d64003d05040c031503461802160004d17600e52851200038041100c44030340003071040005200300c5010ba0b018104141507109000040940304000c00e09000e55000404225071001900b4407142c40c2c0b40030024080d140c20710301b850500815102035071f900d5420300301c0034207101495903102c00418824030011010b0700c0b1402c200c840e00c511241203440075600420040c0c0d0360504d8803801007007000c2c0a400300d15134000306a903903146406140d607911008065400350254584911840c0030841b200320030500c1d100d004420748158980c6454018404402042c0c0b46a00c206041001003100080d009 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 256143857 1250 256142607 256142639
    0x3020334080601050706110316021614040f0e0a03030e0c0d1106160305090406060f0f1805031e1002040b1b0307080c010b180105030307031110020418060b04 69
    0x585000c1c40c0d5501c0d0040161814440c4c00009082ca40c14800400c0188800c00000c60044920800c0c500c0d1529484100700e8070755042c15a0342c80d40c0200d00c81c00304201c0019140d01d80303001500400005945c0c0d139034002201101c045d00e440d00240c0d0006807800c4245074240c492001140003500250000114003400141da21240c140028031041c652380d059465610b601080d00c0300001c0c001d240400681c8541406021600305034a424411810030101194a611407885010341e03040940f104210034010400950320b20200c0200400811a0020002070315501000301884100140000c01e201c66441084142804400303812041401c2c0104001c0005505c0b8100301c0700c8a4401050480c00c403000c06151034110311400c903002d88240e40206148141c0c0106500c01d1810707240403250502e00740c006000a016000e2309205040c1d25070000c0c0b100201090003019102c0202400340c0c251070074002046814000c981180d000313170520b880560007030410100b5620411024200742490b05003068035100e501d281503189 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 256145107 1250 256143857 256143961
    0x4080d1b02070501020313090207080702041e11040e270115180501060915050903011103090f01051b07022b14011a01030c170f070906031b0c02061306030203 69
    0x10008602b814081c0b98403d640510354003c00c10712280c9854010882c035412040a04035542d0320301410001e68a007400102c400f140c518003c5000e640e0b9800600e00c0c0010b054800c0c2803001c0d882c1500e4101955001c0c895224200007900c00d040380941030440d142d03801200f000ba0007540341d00d400c0050054a80005424046419003511802400040c68003200c450242d02c503040d42542c05c02640c0c012100130344002e14403c0e000c500807107400819080d102404c1c1c0e4400d4841030405581c00050f1100c00e014040102580b900240c684120b04041c20742c016064420103024400030210007034100d00304049e83c5181d049500220b00240841c000d0b92161030004c036002c645e9581407681d28602c40a0f058011081e0b00c6413191211400300e80e500d801e804088030034900302d82010016118240100703115001c1d00c145100b40e620f0f5401c091180703d0307000040d50326220b4224181e17400720061102c0f44940d0710a0764900302030100c1c2e580240e142d0504e14034031480101210f0b0300c1c08034000b4a6a209008640014903040c485038 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 256146357 1250 256145107 256145111
    0x809131a041a1c081603122c0a1e0302010c0804110603071e0906020c0102070e040b07020a0203160303081503060403140c071d010f0305100504080d1b0207050102031309 74
    0x2800703800b1185075211a030b0080c03544074003146011714243c1814080038120f0080d201c811401c0524134043c01102c0c200c9200c2c1c0d120100000810b02c0d22054604202d1213000080100c6154441075100c2400d603415a051800010303d000d41d50f0030401d542802120010b60940c1400307881c42c100381c0d9034031540040a440d541d005140101c001070440e8461079400586e80710700c5221090692001704000c207625420300446c005031141040c030b00440d5100040600488841c00044201a1900d0b82c03490084030010b00f04804510603504603c0140e58140010916201600c1020200034a1480e02170945100281001c070780041c1c0300c1503045c468802145096000d9418540844141d89031510314100e401100c0403103610b44501c01005c88c000b01020748842c102141202d208506a0361180d4203040f82ca4a40030040c107503080b010402401030010340000b034105104504043c2040880c0c0d40c0d510444201540c000003000080301180300c0c1070740510821002d071000388003551404924043c0b841031070030b69100303d5110716 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 256147607 1250 256146357 256146379
    0x602071104051306150602100f0207050105010f0f0603090807020603070201110406030212090118080703030b191508090316031202070503120109020c0a0f0809131a041a 74
    0x30119215a03030800500030010015801e1071040810354050900c821140301e850640c40c8201e0603241000b1208551559004165600b9075265840180032000d069040503034091100d4000201c0a010301e07030182c080c0d080f101030301615203c0d5070016185180d0001e806d041c81c0c1008880030486d036104680b41c65030150f0b00565a40c03100b100403801072207950002d0a08081c0441c1c046280d543c03580003000c05400c0840c0c101450786070305d0100ca00720f0301031070240e90040c088007201e03900180117000075064050003420009080c100440215181c000c02524000d180300340076006004600c0c0302c01700d090403040c492a052909141058041e5600d100346034480c001c12810094a004051044003000521990004c09544442441c50995900d4200400d0f0300702c401000000071070410042d1095450110307140d0024898400300752100e8000c803526200540341801c1c200300c81c5040f5142e500070301034031610010001070010040301e048144211408205803161b03041c0f607002d0030003490240d1413a48802040301e9035030600c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 256148857 1250 256147607 256147613
    0x70e040302032b0e0c010e0f092d1e09010b0f19050301090b0108010501060f0c0308060a12050a02091f050609031f090201020c0a0312030b031204030605240904060207 73
    0x5a80605921507040075024005504086000d50303111700c003030300c1d0150181e50b25001c104242018000a40d0802c1c050710002d62007030401c00e80600c590901d5180f0704e00141035801400901c640c00c48001d1044400901d0036484c1d0a24680041d501c030071003100811643c5140c0c800200c410000007031042c410f00c0b0850507150b010288096910042900a008110780c880c5071520308540c2c20240300d106078035440e0100015066000d00c002c43c800c4040da03507604003450b140307503000d6440240c090512034004540400c0415064810a00d200d0745600070700081c840301510b4410003900c500e00601c40c0c1d130002d4030f06071101d11102c03441c405a410342e501190b000780c40c0c00a02d4003091901040007140c000c416101113a400340041b290b400800680d00070381c02d41300b03040480418010002030700e10004201280e40810040894070a611400100d1002030a2711504d004882920800341c000d5002999219510402c0c007011a0105d0000200d03d05140403104400f200c2d03100117905680010300207030015400007240010 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 256150107 1250 256148857 256148917
    0xa050a0e040f020d050f0603030c0d031505060d020c1002090604060c02041404080403050c1c020f0307030501061706100501050313030509060a08090c0d021e01050409110903070e04030203 82
    0x2070400c0700011920342030f21303a5000c80a00019152030140b09032100c0811100e05003c401c581190621500a10300d01030f051404800070070b514010655542c50030b00780424079584090013001e030340340c8c40c4130050303100c1070241ea40303c1c00c0c41035500d1440519031040104e0902911600241c0e0122840b5003401080c43e1284d001050182441c4500001c045500c001000100150800604140c9015400b21078440700c8040c14071010540d101c444076182d22000002e01d0051a004c003840b01184000760650b51400d03074a90ba41802d5500503003001a545810108100c10700504215403903204e03400540010200f031800c0d0000c3c1051002400445115110410f64410b1501450860711503190141c0442d0703a585802100a20600e000c1e00c2882d05809000078070380c050301e044420b4941d031680050841c41c1005400500f200001c0425110f40d05002c001e0000280d160300c00d105a114080710715000300e5a07218088205400e01659400c03801d1034050403014080030950020541d400d00038862000740100d0454080901 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 256151357 1250 256150107 256150121
    0x513110d060b0a1806050405040c0c0b10050319020904060c090812030709090b0f120a0807052b0207050d02040905030c1b0a0b09100306051806090c0a050a0e04 70
    0x1505070400000103410031102e001081a1912583d603540d403030b009007181c095603d1581c45041c002803001d01050046107010380c8030004200c250b0030f1000003031180396501d24480701d04440440600c0c5c0600c00800c8075040c18040550b0911143e04030010075440790740025441000035001600484e60364080000c01070141c40d1741d00240c03000d0b00450392943c0b0841c9110300700c0d5008503040300016900241c005040c401d140940800d00c030005150b00380303200d03148080c0155480c002c640800c2c1ea101e08103419010855443c000c00005010300c0181801a90a003402d07443c1e1700d890a407131908012340c0c03a8419041940032a9110945504039010641220b60b0300004002e4501c090000c1d01ea0b000c0000c080b11500d50000340e807165640c00601000c00741c50320608101500300140709080c65a4001c1001d07252629003035240444007038803401c00103102c0351102c000c195103102c11885400401c3c80300062200320719000348910340c0004000103480c5007200c40d01c4001d05030b00425031848184820b04408107104e95544e00044c0c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 256152607 1250 256151357 256151377
    0xc0607120e06130f0501030903020319030b0d050a05010c0c05061501020c0402210903040b0a0503062106090c1f0507030903060c050a12061a0304060207021507060f06051311 76
    0x40d8484410490b290301032103c43c4641c804151206a001950f0350190060130f00701e0b070b0550080c6d42081514861151a0310b03075001c0b8841019550b581c001c840d660340202e018140c44c0510000d00c0f41000c41d2901c00c1c02c4a2802414100703101c07407401d100000850000d02681e01c00c001404000c1255420700050b480c080080c0805940203001044115000d280d17030a0303280c4c1d844100000c61039540c4641180c5502e03489140110401d200c0c3c200504070001d030099000310b80100010b0030761940e048801c607942d42c11070074104a445158014009000022800700007659400a04454011051040404440054a403181c00760203110000c6070100a140c0540307180c070300540d04071400f8090b07070909800040455001d29104004110303206600d0000c40124030810042c0e60101c5c84985010402c011a484280c20040c41118825007c0100e000140c840a1500078031001c1148040d464000c98500070081e40d5140600c4416680303001c104101554483d032204048985011002500e48001107203000c8030f10400f407440b = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 256153857 1250 256152607 256152619
    0xa0e16020f03391e0a080706050f0a0501080a03030b06070b0f1e0103080405240706020d0605040b21010216110a17070330080a05090c0607120e 63
    0x4280300303860743c03038002c0454005003054602c01c1c1c40c481c4550001ca08003450304041d5912040310007000e088400d041000f1804200112139104030b456844840d90350000d841240c981d40c9030018004500f01000403a42c22460454007413001d5814140c40f01e0351080306608c05020140c684510150a8a444049415158100900507640d14201032010f00d45002540d11134a402303001c0d0007069504510300c81c0c0d9410b0740e601110462410b271801080100407400c1c4401ea6a0b0301c01c01c01c03030121010030124003c1000611501c000740c1c452846080c440201c0e0303203d500c498010350801031121907030340c1c2e0442d2241242842803c9100d13a500070240d03041c02405601440c001c4807080c120146c0501c0700d99640d140c0000300440c0c04500c007a8860040d0150610084011007a0744d003c84e40500006001400104e0007207003800000d0080d0b5584401000711548203921400440c03034420502c80c100c84240110f582c0518800018035441e120800452254460788002925a0802c69507540d0a81e106410001d9060f0004110f = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 256155107 1250 256153857 256153867
    0x210708070501050f011202030a17130f06080709120204050411131a010c0c0b0306010201020d050a051801050903180307170f01050702120306090712020a0f0e0a0e16020f03 75
    0x81402031500303540c05130007003030008000136500080444a917926640038010b414402a01e9640d0b0203a40c6100061000b210414446028007002c01e0f0305100050440d1100d45100321702c2d040d0003034580f05001d400742e002c0102c900000e10140c6940b030300d80300d90303181d0646000031990741d1030514241c00e9100209141c0d00c45150003d68251020315000740e052102e0402003400c141c44818015101040940801003542c40e6081c400c03c10851002d02070b550012042c00090701c1c04950107088011507404843c22002240e541c01404000c288500c1c03055102c41070306008101d00e09002e5010350f41e90054000c0703181c04904584060341d003a1000d101c003030000c0903c00c5401c83d101000304e800c0e23510b0364400313180c6000a601c0c0400280415100041c00c51001c041d4449462560b02c80c48148841d010004000c00c0901c500041e182d14020f580d40b008001845d0541d0302c10901649946005240a40700d4400078030603035030820140070108090200301d8004041b441e01d0341c4070001d580b5040e82402c120035162041c1d0702000c25 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 256156357 1250 256155107 256155113
    0x605030f010609061202030703080d0b09131e1e020303040e15090c03070c02060703020c180105031002030609010506090a0b07080d05010b03040308180a02120714030304060221070807 80
    0x740c2510f40e0602c06201ea41e468041500d84003011950207980340d40083d07000c1020440040c01408541201040461340900d02c80c0440c8402109a0b01c100c07200300e50714580010f0001d4890000280f118403051162370f064191103d00c20f409100f0383e00d041d03406045145500315941082210024000031003890285d1811002074803581080c0c8450601417175906000451a01070103085a02c11081c3d40c0b652010381c1d24503000c0c01201d4101c101c0171804d522440c0c2592040f43c0d0b4964402109a40c0300503a903030150704010a160411180c2c0e07000700207090061050056941d03e0561850564038166455903c0705000400108442201d80c4005046500040c40d1404d003c60316000f010b181c00048414031542c0d030707140c042241520045030080e00042c500c00215104c421050030011014001c1e80894960580640000f03241c000c41e0400140168040b07a0100034400000e40c01c0245030780304401a41c200361038660b020351103000b0f01c203040286214050b402c00340e40307072118191420281c0040c60261511010f107 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 256157607 1250 256156357 256156361
    0x60406080c2b0203060a0b03010b0d030f05030a0f02161203020c28080f0a170105030c041508030a0309152307051204030e0f0613031112061003060b10090b0d0605030f01 74
    0x400c405019500f012b0701c0c04d5042c1000d241d139800f07a50b416a1201c80741c009407082107415800c00b810455072180c80320075000408001c1c3c00504035039617240c0d45a0450011034a40841d00d0030501d91540c040c5030050090350640000491810703c0b8200c1c0480a440702100007192068401c081040100222800718070b5141e9980042c0280c01250791507140c0466501d14121103104e0000c0922417554190310a0034449040d0920b5081000b10f6075032507968600440e107901030f09003550081514100005c2d0790f0075580c420302840c12034041d0001007a02c0108109010303404403502d11758807000801c500d220044003154156220314211104910b24922031681d07800c2a241c010030b130f000c10712843c91141103103007001e643d04d00d8000300311181c0b00804075100e81e0141c03560f9240c0da00c143c4042d2150342e02620200d01c40b08955803d2180c984141503880c1003516075411460080100c510351450140242c019989040708030350461502000c1d0780540c205a6112050342c00f41401502e010f4001a415008100040e141c2c85415 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 256158857 1250 256157607 256157621
    0x90606071a18120d0915061404060b040b09150c1501150207050604180f020a030902030d09060215040f1202010f0c02030702030312100909050303060406080c2b0203060a 74
    0x8110b001080d410789503042039403600c1403000d80c2c0d5404410000498030307070400d500c00c4000d54403441642c903000040101c24811118682d008800e90420361302c806200b440c1a10600000d440385040ea1410503041c0a207c0d03800d80129005107000c0c0c02003843c4881b00d48206004c9e9031031180100101c4482012000501c1c034550400e10502e0000d1040c0445a0909400890030300280c0d0b0020300355500305072500403081c00d070348010035500103807030303620440520302240a0000704169201d5490100741d8044a1042c1840d204050401c00e0821a15003020b000c0b683e40030880040c4010750035000b4210340c440b400c10200407200360100a0000301da8000c0106c1e03464042d0441c0c0480d41410404004e0014828400c1e070303c9105940703009505401c1000104a8501c080310103075001381100c0087c0941d69100e06002085803d8102d05907803da00201c1000f800b0314041c040d03540030f44000006024011154070111304800c2c2c6441c00c0d024041d6818650303120038012a04401100c1c1e8001301210001e013000640312005200e1 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 256160107 1250 256158857 256158871
    0x306060c100f2f090d051554010203040f0219140409080f0a0302090a12030c140309061c051f06030e0703140d020d140405090606071a 59
    0x400c1d802c201c0700d05841e2003034400c010100020303006074150300c0f4010105078880680d00d64810707160001c0c400070940402209428102d6000c0038101ca040100401c0e01c0101085003008201c10004103c5940d43c071f00307210048a050561884642c2d002c100403d142964072803960807902903102004010074030111554090a10780255401046020020740c103241701e07402070143d0780c1d244085200c248981d0070250300003c0300c980985402800c2001003441d01c0ba84d5841f07500035200082d004245a4907626111080e400144601084003841c0340c0310b076a004d804901215005444201640300c82041c0c00024411a8103c03180101450303034500c0008004144a29001c50401e074a84c03411001a545903421550381162103c4900305001c2203107006002c1740980300307202a10181d40130b0100d00000107249080340090b0400c04070060010300640c0e15009103880d840405550820415800010201303400500301c50540c2c0d402d842002256035a8800b20703619100e01c60000f800300c4030b0b4042400444103140f07110340c05000 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 256161357 1250 256160107 256160111
    0x7020d0819090b091e040e0109080408100204050f010f030906060b0417010603051507020a020303040b071a061e010e150a1b20120607090513110f0306060c100f 70
    0x9240c035a40c00d0113006510a80341c00c5903544d40e01342070318a945041a02c2c00040208082901408800340600b0344035806800c460b030380f00103d030a20102300140241200030691250850510346000e00144a80203140c01c041d040c4080ca0003440006031003600702c4d21031650040d0041c0032040da41c20740e01c02503610030310410700b5120522205054000c018040c00c011650041c0c02410742079100c0c80030301e5452030302500380802d40c0305100d0803100503103007800a40000c2100e0708009440d60710038240414044c15a58440d40701c2c8940c101000724580c0c0303811040540c4910252031000500d01d03038005880c41c440b2800030b03960100020701356141c0000844c000b003c40b41d400d5511000441c1c1c1101d0b909068201d05a4001d04a01505408000c10b4500d41e0b0341c02d2100400606071640800d01c200f0103410701e5402c1e2120340000748840b8060000c0e00380541541c44090395910308004540100030b41c4c8030540034100030074a07044070000124000f0f607203500a650040035040300781c8007075102ca00c0d0070780010700ea15645210350fa4 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 256162607 1250 256161357 256161359
    0x1021b0f160812090a0e0702010f05060118032409140d0504030305040e07050d020d06060806010e030709020901020705150304020a05040204080a0b0402030f030a111203041707020d081909 82
    0x44061201000c6403454001810302c2003c6003490f200b2030300a40030882e00400171400018a8400c1c0184080c002e0034183c0000174411850701a15083e90703402000c85040c010041c184030015001007a9640441c2e412454050059024088000841010612a608040c01c0402501c144200300d071609581c0166032088442c001c061000a0302c0900942c40f000c0c01080d003e20041081d03030980940c041c1e04c03112602e011468039412075403680480c3c01500401c051160350700d4003408016000400c468115000b400c14401c0000311000103903484105004000d40b264002c9240400340e402006048040d000c01407904400458440ea0308a56420456040e0710441d202c40300010700741018421101661182c0000d01480311194a550b40c507440d01800490701031284551040c0c0800052001e0140031441d039540400384090211b159140c000b81c8000084904800c10030b1200240c204480c08841c01d0407030603040d455858a000007514007030300c14405032010a000030b03414181d4034030300c004801d082520f440c0c3c04646 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 256163857 1250 256162607 256162633
    0x5041e03021c0201061a09030c09010308071101030612030e04060e01120c090903092315070b1b070f2103020406020607020721150f020306181605070501021b0f 70
    0xe10745d81d2180f40b0441c03081c121840264055440200a1840c01034201c400c0c480400d0086142030000740e10640c2c0326030002c1024801c11450ba5004241100c0c24682801401c0c2403480314584441000030003000d0040c4002a440700351a250012002020f0101100c1031560359805001400396400c80204c1d01d0640440b40400c640d4810f10801c3c0d1803d815a82c1e0041060810003040f0031980b130311840c4801030700080c2141404daa036400400b2025119007000030346690700ea20380754042000152008580030701108000880e0031a00055401d10740c0c00c40d00150f10715640c1e0a0094101d80111410102c460b85c0d40c2c5101c0c14180c00d41c004008907201a821140e0654640b08202c4e204d010b903001e50124000c070a2001002030020300c1d01c60806901404034442c1955030700c40024100c3c0c2c50400e41c2140340340c01004000c00740c5401314007102d078001c49611b040003514144103000300410245160500344400800c800083c0003003507058032109602c488074005466080001c1554a600c4e18046140131301c00e03828140c0038 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 256165107 1250 256163857 256163861
    0x15140109060813080703030e0601030303230f04060b12030309030901090506030708010b0c070506160c05150f031e0a06030b010b0a0905060a1701090501030c141305041e03021c0201 79
    0x2181900f0714402e655154035546802142e441042d05404150720b8050b0401030035824003c9034021446900d00080c4550036808018447e000109580742c016078807001c01c4032080d95074001640c0294000c2000501b0352043e40001ca991b409428016040d100110400c60850000070042480600176290b14041c15034890800c2031303501c001c40f500f0300052052001004107100383d070050410f14111500f034440c0c058641c808100d07950030500e02c540420004100740350074080380384001c0000d81010b440c102d0360860040c0c240a05131280a4080c0151030340000000c2a4443c580f07250038034034408801b40d40090030190000d00c00b0f00340070f000c00d51700c2c0b5403c040000f4101c3c40b0136049800c415001d44401101034130303003003c0060941000114030305008004810402d500448072500340a06240540011594190705044002048980042d10001e160b00c1200303c10f44e076502191940d03000383c18004516039071070385040101d514007203010000440c05070b51284c04150300820100c5651240100d030002d8003140130301c1242 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 256166357 1250 256165107 256165111
    0xd0303140a051f1508090f0a0c09050a02040f030b07210515030606011b050304050a030302030c012702041806020c0c030c090103020f01120e0607050d0b042d151401090608 75
    0x30b45400d035000c2c084c006000c0e41c130066101000006544e40b040403400c3c502c0c2809503240701118002120170f028080c2e80e0361031107580e03040501c019046082c1820207040d4a0700050310301001d0314043c2c40348005210603200d151024120082e075400d90307106080b00b0580c40c002e00402d6420b068152108803003400301d0300300050318500c1003205070340301d00841b01c401007065501c6c04240c20a0b102e5020412011032640c644101400045200741d0007541c7d200c040047c180d0850395a0411000c030300b05030300d56220b0040c207030009030f5168a0301100d0001d01c0800c1c1d000101c0b180c00c000e60b4000e000d1400826440000302011505441c002026000c2e2600120800b0070002c4540c0240130081d4801c03500d040400b025480b500c41002c0c41208024000340021425002070b03c0d14400b02c40203000039400043d0004001803030b00600090103800c0ea002c0c8000e03512002c0036407820410180d4000ca11100c40c17114800c0000c40e403c641c0200031509070320141161586800071808440804050110344d5040300040c1d41380c45284100c3c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 256167607 1250 256166357 256166369
    0xc010f0e040b041d0f06010803030103050714010e031204050109060e030a0609080c06040627050616020102091e091b0d020702060d15051512060d0303140a051f 70
    0xd40200d0300141080300912104030b1054125980305070582034505841c0c207540030b5268030700c020030303074119200003081c5009416004444940c005000420015000003010010f5609002844a000031050012280320226228003030703043c400c1000d012814080e10000b442611000e9031051070b43c035200c06054820011404503541c0681c020440540800d9990303108600c900c2c41002e000340b40001d81c268551406409131403e80e42e03030340d43d00592811035816a6401500c41408840c010b41c030328240d117855481d0840144852901c03182140e050031110710030350458582a0740140b8003000c1203400c00c02d2501800c0e00450322401104400f01113034241c401d0f8540041e0800000319440e00d0704c503107140800003a4102000c100d82100c4203100705140a01940551200c02002440c020b1600c2e182408220030303a0107255280f002004108000a44c202c014081aa40031005441e6842ea120951508a00800d40b1118007035401500005121910480d0b8000783e0060201c03151191140c00480042840e030641d5101340 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 256168857 1250 256167607 256167617
    0x270105040b04121e060501060801090c0507030c0507181a03031e0f070c0803090102120a09210c0b030103050c01020c012109061e05011401080105152203050c010f 71
    0x400c4008910044940f8441c8a854802e82403089a0800881c0c00c140389000c0350040c1d03c400050000c240d211070900d004181c000d609100d110007a14020700548180c2501a040103180b20500040c49010041000209000c0350141c4842d032190710142c004211094500d4110364889203441c4107482e0000039120070701902900c05641c00c04a140b074000580c0b1880500b07480c41c0d41803020310f02003580190f62000804c60417014554451a04000a0070324880d0300d40d642840a060040200c002d9000c00b060013528501090302071804c0810640b0030343c4112044000f480700d038205101080907205040918100c9106a003180c00341e900d82c03001a030b1903842540c10300e03000400f0640301c0c1c0d03481008040c40100d409104517001420446e00c0d2a42825500c0c507100700815285a40002100596180700f564010325030310174042c0d0103907200c4000a09040040c45080d119403a40c113804807844030303018102c400d00f102c0e007060b003070240300401207200003c0d000b0300c001c3d50035006a210140e150750040410540050160b070315 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 256170107 1250 256168857 256168859
    0x70c14010b120c0f0f150a03090f03050a0e0a0f050103021e040621021905031909030e011404050a090908120403090302011e080105040c02120706061e080d030b0d0503270105040b04 79
    0xc02c61b8180c20580c2c24104040c0c8405130707900460a40c4400740a1180030f5035030b15543d1301001d84040c1141d43e51019850041c03140c004100100b101c10308601c0300352082481c000d41d603008079280885600d503d9002c049007900700000c0c002181c42d001b1050b01002d11603000100f88081206280e88220b000b4a00103100c000042d5800782101c40c0b040006542c045a00707030101c070a00070b81c80110380c121608180f00302c01180c2100c5040c02d0544e04805c9140c1019540c3d601945024104070108100c2c207128800c1c1100161502d280790304200700003003a1440710b0104c0310341038400d15143c180140740024521003680441d40750b518118554100318448000e000454071403d115900c1c15007444010400d1400c183c0c218041c0c02e5201b4907002d40341d80184140e50041101003411401c06903210300706416004504910710051a0801c8079000101e90000b0081803030a0018081900070041014044005c0000f0082c3c0000505d100c41020b0400150803d255510307526005240a1001502c5521aa000786030000a080c08 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 256171357 1250 256170107 256170139
    0x70c0201141b100b0a05030705090403090b0a0305040b0c0403050a24020a020304180c120e070b0712020106051e060706020904020406210203070c14010b120c0f0f 71
    0x240707403400c0081e4090924084240001d0344103207003240c00d484180d41042501100030f1803540500a00700c20201c41c0f1695aa19013000a0f076908414400c0d40e00412600340002c090600403481c000c0140312018240750360b03801c0c0400040042c101150704032244030f03c19002c951440b080000765400d8a910200810b061a0140c841c2410460303545072851848114502c14000300d9003600142c05115010340003151200d041081489011010100d40215039150442e10f03145245d00848410003603c84900000300ca5000001072428442c0b107410150011000084600c20054201109a80e0783e240340d008100080d190810172081800c51105a41400c00e0080d07140401d140000080c0212446510018078000340c0401140aa03006903200201045c940c4441010081007003141082481005204519500d0700c0b00b40500400503950780500074002d8004e080034001e8095029440314034000302145807840c120400c003079480702c064041c9030040c003a80c518200316081c0603c240300080e10080c86100b8516000c4 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 256172607 1250 256171357 256171367
    0x90b1e010e070c111918022506090203010603080301090f06060806010e0f090f063309010c0204050406020c0d030204140108100b030f1510120b0d0209010f030308010509070c0201 78
    0x440240d900c0c58480b010700040360b03900700100300f20012a001e11044a45040902c1c001005080501c1110a0042180a50301c196000c46a0107161202c008e0310610011814840c0040c0300c80c0300001d42643c6005804024070810401850480c2c003251000e0200892202689003918814030070200071461100c0401c14640c0a18501308ac683c03c05404c42c80200c0c0b50500064030130f603081c2e030802424901c8601b44412400d00b608881c044503800300003021881c202d00c1c0f00c010390400040900c105001d011070340c0ad02c26031003000c444480c5c5030002c005019030305240c00c0401c003d501c280d003003223820702c52100780d213104c030380607000790b4040301c4003403807081151b07011400151483c82e001403038512020360a0b0b0000c90f01f503220740301035409003406440d600050315103002100c00d50012649242c0c400d8148280401d4044d612518144424400303070000f040c461408000f09503110064a8020740c040000000422401000d8002c071046902a507580d403441d990301c0050001030401528454001000c504806c00503501030 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 256173857 1250 256172607 256172627
    0xc0706051c110a0f080f0103020f28140d03090e0a020f0a0c0201030510030f020d050c031b040c080631050a020c0d14041e09090b1e010e07 61
    0x740c000800c4401c181d81524003191081003050314600c0c00441c2841c0140d50208108610301c1117801e0841c41c50418012103002c840b01403000070b01c11002845d5903000c030b0f10340701c91704c2c1c10709400446a180c2c000301c0300b14044516511030003000c2d5400c001201c4144580b904402011005816441d03007032103281080071444110720010200c07144582c08028040701c4d0112100100042c403410341d2110301c0856140700040c181d410141c182001c114000c9000c1c0003040d6a41140d04a240d41201c070399042c806031307103000360401352501d0403070703500d07020341001107154002402c00c000d864201241c04104500640d00251090700047e180550448200404448420f8855010503070200900410001c0f04041d203403013030701361034048070400150341d00450360303043c0000b013040b20030415411070034404504400c50202d10700501980c03203000a440e2074088034000e0302203001c030700c031020342031140c0b0070701800040e0704008a0b0884290740050780d0a0b11a02a4900c10f042c500b41c0c81d06891203002858030913100c5450458403e010 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 256175107 1250 256173857 256173877
    0x30c04080601030f1428060f1508100507021c0504031704030210020a0512090d050d020327013608010b03010e01090807140a0b0f0f06060c070605 64
    0x41008081006082007000030300840c8240440600369481d4038080c2d0640d4842e0407060240c6c0d0000c100f41001d10410304d0b554140b80030300000c6240300042d50918801500e074143c00c082c0d02d149401240e4480c40009051001a0b819100407544400708005003541100c90845034040140c1216000d854081900039103188003d150349002030605440342c456015104800c9072003048014001010030440c01c0a9112007141203150001d0000000746d0740310f2603100c110018400d03e050703c00048040c0b0359595010400f0030b49800c81e085884d80c3e0f1240c8006540c0764440c0010340c2c442d4401e05464103d988803070305111035806043c5d480a00c82e0402e0107800e01000742c042083c0c001e00c1d0740f00c0100d0603514035001c01d81c001400d880002007180d14401052608480070344418000030b0341003c020708041200c007412158a6644400d1160300748400c204800d0030508601c1000705255941030600082d039440c00030701c070b000d8000d00081c80e0085d1a40802c2041c50720968a1000407600b02403420070406000704090903020301 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 256176357 1250 256175107 256175131
    0x170f0c0616060203010806070f031401030816150b0301061e150509090412030c0906050318120a02010c02060f090a301107090b2209060e060f0f010b0a030203 69
    0x903440c2c1e142c0090384c000346c100c1800b9a011030104a140d5520800306407084000b820f007017000d050510400d218020050202600c0810001181d1050308031021501c6003168002444180700d40c20308903500701808102d01200c0c4690b08000000c00c10044110703c440341e07940454905200705242038000e040703480540103000188070081c4407182480e280d01084a1055218901a940c002460303080507003100c061004039810007040d5001400781d0b9802104480e0003c80c480d0230f8060036140418210300d003000445052140f10b00115000c0aa0380d0150819005e007603281e000d940c003503624860802401001220302d01c44070392003035001c00f0100310030b41c900103d004e00c1019201c014403440f60340c507500b088002d204540010b956441038240c01d00d041c000e600203010790440038081c4009030800a80f120070903007030042103c9407104083e820702c540c5500000400741c1c0110140080700d610201d1a0300d40e0812642008140c1002d0000b0b860a0000c000f01810380c1d240441160600410b203030102c0c001d410003041c0c080040c0c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 256177607 1250 256176357 256176397
    0x606130902040b1e0114031308130f0b0d27060b0d05030f0c010b0906010c0b07120f0c030b090702060a0c02031e0a140a08010603020d1404030207170f0c06 68
    0x1803207100980000113020b4040040840c960400142038400c1c01032031071106c2000380140481c0c2c3c018100000306042c0c0064403591201c1c2c804802c0900103006512002620300005400140c000f1488042c0c131303802e8070f101402c0000c07441ea120b00651003084450103014008040030660b0003d1003941c08450802c1002d8000074034000d04d60345d10b500c2c5074030003941402c0510300440c07000b400090900540c0080c4000380d078141241d00381080007a10300c0300d000600820403415070000601c1203200e070b1200e60484940b50414000944802190801071400c607a4600000342060307511041030074440c0c8100c0c050b4902b82c0c0100304907906ca1145e04000c0203100411000c6000c10017802c1001401c103e50000c140e50001e5460b50f5403440d1036400380140d0104450744245406c1446056100c580140d0001e0448030182005651007000e0b00760300c001012405510200c01c030814080c0420b05500141c1d14003620101c0c00b10103040c48403514002e03625114800120310692007690781400c03504254019000942030340400070011 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 256178857 1250 256177607 256177609
    0x140105031f14030d0212090d051906020909070305040c0b1c0f0e1e0a1b1203090302040b01050c07030f030c0210230a02032a15060f030606130902040b 66
    0x508001d902c0108800500203029280c1e103410321109024000a00080c40074406e4408422072034042c01c030441d803041c01c8000450081c070809000c46134801024400c0c2e01008281e038503082c002504070301180c901a00c21100000c50752801ba1044a0050707402c4082d1151442c501a0781040591101135040e12441c04110300031443e5880e4000d60801a208140200f00c080090310302500e4013000c2000501c1140740c03c240c03640e0303001c0086007a03120b032500841f01c00c8000c250310100007410446a03001c400f0312040704603905c00780b541c49903d0f41c0a030b03842140c0c00d201c00c3c840790004652901407103440b65000d812008007003001642004620003514440e04100c00c3d011225000602144035040e0b44802003011200b0950865a04011540c10141e03101c0155080c5020300f40029581e00800d210103c0351701d0404240c0b2103000c0410888450780c46040c040300c05441d00e50b107444c4100002650070600402204440c50b400b8503011412510822010b02050a641d000705c5c0418081c0c00160300983c1c000b5581c000000315 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 256180107 1250 256178857 256178911
    0x20a0504090c0e0a2d090f0b0f01060e010e0409020f0604030503070b0c27120304060203040f09020a020307020907030e1207020907090608061003060e07020606030d080114010503 78
    0xc1070340980082401c0624101890410301001004205a10314200001d03442e0101c441800740d44000c8440c10351840c2c5243c0980740000d040802e0050103046011480c081046401040390344a603182c80315404003640d07540016294039280810803400b2a01402691010782010303840300c200301d0700041550040081034008030b22107904c2500306036020303007001842805000d03070356045940149510100d1407801806000554143d80e0108a1007180820f40340714907050341d03545002c0320203608014152565a591068042c2d540d070f10601c51800c146032241000690340700103200740c0707001310713126000b45180038095400c01491007002000701c6c2c01d040c0d030745000d0910b2000400c1441d1462541c480b42542d240e29030300401c025041d00611702c504002030190306110302540300049a411507002e030740d1111114207009080e0b007c0d01842d0800e803170303898a400c1003181c0c0c25030000d60350b401100158280c0380001140e1038111349030340c003d0080d001d0001050030702c010594400c00c01035903c042100d4640798001707400048404 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 256181357 1250 256180107 256180121
    0x90e0114070e0907020303060906040c02010917030114030a0510150f030b2e0306050c070f3f0c110d030804030311180402030c0c0d0801061202030c090d020a0504 71
    0x400940300b4a6440182e040c6030000a400c8001400118150300c1c0000c0000c51010004210031701a41c2c4031110450024001d4120062035644013011007280a41d02103403054a420901c18039003511074100c0420000d04011411707410382500100505058601c0c2d40e45c55020700780c1006c440c043c1148070800000d0003041c00c26450007440c81204a080c55007084040c10303480074021141f07031603140010b914204240b4103800c5103108890f402080030907240e0f034102c0c0940c0d0b01d02402402400c000300e815010740420208a60b000c00a181313284001080035003454003c651810038201c50030a40e141d07107010a00e02c1d40244505400d1510854400e0740182c0c03400049403401d1542c24007240402c0e0b101c014001015010301030202112406a00380e400e00c00e5030303034039101000c0d44040180d01550b80000481d1040c00300380102c0c1c0000b40841c00301c42d046003142100401080b0f00f48103480000340701101840c0709495174000c6074000d408120005081c41c808008202d0078903c0040201d92040c00124000b40588403401184 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 256182607 1250 256181357 256181371
    0x29010801090606050105030c1b0102040915180902030d0311090d050c101103090118030b0f040b06010c12080601020a0b07020705031006080a140f060c0c1507020304090e0114 76
    0x420841d06a00c0c0c91000d94560383c00080c1405800e0040068a5004a095900380c4582c058058107014000560600a00c01d41d086180e489051030420a03401e2031a85602c0112803122407080401d803000e030820700441d082110000d601d41c21500c041c0100910039005a0fa011110a0003c0c1c0740c00f1414002614442243d00111842c1c4c00014840f070061070f15800681ca1803820f8108240160001e0726599128828404600c3c1442006205294008000a0542d010f1640f00c8000390240c14105921007180360110750445001882600184155219803008a0b01590140710041d84c83c00c1c804c0d080e0380c074200003444c460441c807a400b0010081029003090600400e0240c01074144141400281410305605283c6498800c0c02c146080111140c0018010104c9411201104640004007425410180070b8444081e6500c1103e0034807901911b06c2005020b004a8541264000c2390b0354000f03550503050482d17042e00941c2041c0410010032102e42c000d001c4141518000085032142107111040710741d0141e43c11 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 256183857 1250 256182607 256182611
    0x10030c0206070e060a050f19020102190306030c030803090a2102070801050903180118030b060a0e0601091502030c06010e0708180c0f0103060e0a050405190f29010801 73
    0x12940003901403208981000d80ca00c0c0000301a1a03100c042880e030320410060800b0031100140e000403554504041c2c9000c140685803030340e40103c0040c4002e0107900140000010122500003846a503400b034814101140c1d031100c00c404903185591515011070b00000c180260314082e00b0441d1001030b01c410048900760103000c030028280ca04440e0001d1618443e90001d114584c5000203001ca501030000035100c0810900e10140402000b020040b540a00100807005194103d404c021007084071680c1c0c0503200c0c0c031003910784121955640214060180701580c6440c0401e06440041c84403180ba50700100e10003040340122450020380d00702c013a1400348240e00c118850101c1c3c070180504107600400c82030f004000024011040011054005e07181c2e00009000c030310611550500340000c2c0d020387c200300001e004901100e410742c500038404001038442140c0403a0140222542100b0801e074407140d044d0700319041036010700c02c0311544d500d180f0603003c582081c0508030705c60000d1030142c1502c210814081c120503000 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 256185107 1250 256183857 256183871
    0x3350705070e0603150a050405030c1f0c1e140c100905010b030c031902131a04060503030a090e19020304080a0305010f03020d080319060f08070807060504231003 71
    0x240e40c1c0e5a00c409450f141c465080340307140c0404e01d8014000d1a4000803100030002d219103da140051a5105141d00b94006002e9a00344000c8042d2000500c0110005401c00303109017150010101c44428074008003000d1101000c0d241c000b454466480c1c1040b0ba4000e4012503e00051001d82d9881d00d205441054440c640320744405003040720038020307118066010350082c072407c0400c20000341c5581030b41d05441007026504e1040c6c01036641e120f01e802c1e810200c540c3c04002e03c9610841c4000e24a003501512801213040840c009a107007400021544156219601c0d42c401c0c5060108015002c031000d4403825030607182469118503007a440c4025030180e84a0000590303504260304026043d210f05a00061265200740c00070405a2a6403144a84959210711041c3d52541e49000d00220707501d58050b5608218603241d00440c0ca65000c0c8422000c2e15900c01c2202ca80395921090740d90784c0d446034002c09000503000e000803c520355800109440c26aa0800c1c0080b40d1010100420002600f084a190010780c886213 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 256186357 1250 256185107 256185119
    0x30d09020301141b0d0b190501110d020d32031e090d03051e010e070921060b0d120801030c06030209030d120908030f010801150335070507 61
    0x200f0040c1d240030f1103140035841d00d80f1030001c5076094540400c21040340d0b0005003100d11040250b20a485040c1c0003040d0166003d03444420200345000c034029a800300d00d2101d481003503090001500c02201e2b80c02da0041c411940c4c508000c803140365020356a4598035251502c04600c400c500c19a2040303003205203000c40c0c0c43e481c100c0d48035003034070443d04401181101c0c0c202c10b0005003840403c5d40c085075102420045010785a000c8500d8641184e15115010410100004584d4140c0d2051190140c0301700da5070003d619884d0440304c184000120081c0d43c00c589013010f610001f880c59044000e07000c100400c1030140300800c0d160300070148103402c1548001580300b80140200484540d40b030000e000c10389001c50525000402003543c514120784207109210306039002c9910003000e134108182e840d9200315019207900b00740540c02c100c0e030420b02841d2410f50030212904800c07448080480201c0303030000850012008410461105104856140d21210b000000e000700074040f034500500d801d0348120010005689811 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 256187607 1250 256186357 256186361
    0x405010902160212030d090b271203040c03050d0207080c060901020703020f03010207080a0819021801080a1d0105060306060409021005030c19050706050708070c060b03010219051e070803220203030d09020301 91
    0x1201c034003c0c001500e0950409e4000c006000d50003040c008400580d030352504d0500190500295000070407610840c007240d002e040c0d0200b28101101e001d4400c5801452072101040f4036400b80041050040e172180008101500d02170b034500300c80d500d015000501c0d15625403034811a42c3d010503c0c0b00049814201480403014458003c144030140340c110450600d04240403d0440e210340901c4a03040040789004500030302c4180e0b1180074454002180c42c0b004440a861140c060241111200e102e4014280098100c1c2000e00030320b520ba507401060044004851703041a241d540024100804d282030501c00102c1c44100e5904484000d040c0d070711555101c0705186010000e0340c3d0010000b004000704442800a5203801a0805980c01d6001c3d42c082100c14000002c3b03802801800021005903118058400c9142d80100044c10394501844e58840034081300c24011034135104442c80100303540c80420000314130440501c80d081d8501e0a83c486d414440700300c0d4000030b256810110100c40201da5400c08082107140074 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 256188857 1250 256187607 256187641
    0x313170a080301090504020307050303040909061b0233010f03020907030b03280605040f0c08010603020f09040203150a0e07050d0c0b0f0d11090405010902160212030d090b 75
    0x5801040380316603a540c1d80060b80010300c03410b0522600c0d0700c003190441d5030034408140a040040c041f26210b42d511202600030303104950064030f1082ca0000f10b510038080c2c11000d98081c01080d00107181900079400340c0341001003d90a64681082e404100313000e8401d150742c072240240380ca0a040c03980142107004020030a6070241c9054180743c508070500e000380c0c40c045404400700050720241c0d0000c1a24400d80d03111080304100007004c2c2c070310b00350800041081c1d10800c00c03181c030b0040c035110078000d489035605403c8440501001e507000420000d500c8052525102841e4840e01c0542680c0d00c40d050700700106000f607400e4820288050b25165640d030340d008104040001843c040b5000313071214a0584860340b407440213020307c0d02000800903045060050346c00c2160300500341c0300d00400c04180b2074554980650041c00420340324504100000481248070b0007070781c0c441c600c4800d00b05185181503081200c00c5642c64644412030000b8448150041150301c61144c481c0d025180412443c0f60400085034402e0301 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 256190107 1250 256188857 256188899
    0x8060a0f0e0f0f090a02100201110c0f0c060a0212090f130b01030b240c0120090a0902070201170417071b080a0506241002031309051303031d0313 64
    0x1010f420000141d00001d1403800d2240c0607222a48030602d01c5400700c3c00341003400450a28204001a03080c2e10308400140d603000c010710b00301602e40404100040000c40e110304014040141e009218007000640494003d2500d03c2000b8030625070889035401040d02141078214000385036564601d005002d503014020144201e00c1101c00c000d80302e0081d0032500042d0000700385988901c0740031505e070000c0d540952291800c4130401291a00c20700c0c2d03850b19207075585d024104142c014004240c00080d100000c0c02a50007681d4144c5400e1003a04d100c0e603018444400003001174400300428440c2d65920b10541004040c45030103020316144e11141e10720003441c14401075201014941c012010040826800701c0c540d500720703c41d170420a80c002460000d00801844e10401c0d10360002d420007003c284e6a03000002090940d011101104400b80d480c2e41d0242141e1044440c5030b035165142c8001070000344207500c400c803c0f0007081c0351001b881047c1200c980c5190000d130101d01116030317401c40621030340c02042600f026080b0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 256191357 1250 256190107 256190131
    0xf11030606061b0a0507151106011410020a1502090301141303081b040603020d0e010605030d03150306020412020909012304210315050604050f0108060a0f0e0f 70
    0x300721022075018480e503039201d481078000c4180f500e4201e400380561030b2007507046001c80b600151240c0340360700a41301c1c00c00320b0404591403a034036a03003045021900604236400880f21b2084015164144524403003802502421401440c81000018000b0b901800d0074120340c042c01615200220b00340750031a0ba445040143d000391140070016090003403240040c0382617141c0b416080360303200d01440c41d510616069140c210302ca80810081145507060380909006c00d80220103114034444010320900300d80c09401340c03e806420420401d080740d4000e4109915900f10b44581c50324141d682d403105d0080760840c0d04030300c0c1500240070400003507241c0010391a0b040f8032a00020440d08135000340c21912681c2e05020020710310300810004080c4040400281e034500b0b11111001140108403c000700200000c2403456510100d4100108041c1080d1059030305070f07000a4086041e00b034510b40155103050000340704680c044500351010526400780314090004080d4210540310328100660401400b4500500241c0d1000e = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 256192607 1250 256191357 256191361
    0x80f070c0f080f03090604121a090607170f0a1104080303090d14030f0f0c0906030f04060501060f080c0309011503030c0507090216060b060f070b041208011a0906070f0f110306 77
    0x555031b4801c0740c0031030b59414424070981009240a40c1e4420381c00709402d0f251034117042040045000807400718800e1030760340e6030080d4a400080c0800440f650580f444500c200c981000100038450550110b94420701c5c503611141001d42d0780300030514503401250340130074075006151102c120308e0f040200411180d80b5000180d08528001e41c0c1081001c2e00100b8080c000110300b0b002c02d144800000132600c01c0320300a400140d8920f08610590012081900c2c2245c090b8a0078000044541c4078a0000d04601703801c0d078aa080c69116040340600f41d400240420302c4c0d6569900e02007212144844607c00110b10a072103115003454070781411403c14120b07a1244040c14010414000c1540c8810305100c1c0003580800300150f01c17050080401c1180c09242074030b040840c2c2c002803400601c000903001510071803040b01c00801840c11841c084400f400c003071080d803445124461040c2c0748440e00300003610410742d018054a013403000f5070701c1d00703200804610030544071484c5000b891001e0103021882c1d110120700a4004040300c0c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 256193857 1250 256192607 256192609
    0x9210e010c060903180b031801020901050f0309120a1e09060507080a18080a051207080909070507080711100f020c0402130f0e0118090b04080f070c0f080f0309 70
    0x26140364100180070595610300743c800c042c0241d465140914010401c400e102d62030305803200e02d0307901c284c5250b003100f00c01d03d860f114100f00500071514010030603520310b41080e00c50500c1e03407156000a00380820314000c51691150b1220365202030071135212a03503a180300749038464080129401d00310400c2c00800400400501000d0340250480e40e4a5911000719903480c000310608940070606c202c203001613a80058000111080009000b81043d03004005896001c880e400d0a560184a01c4000401e060018400c0c1c0380e0034a0b003500d40a5000c00c0c1410070510380300490340e85044a522130002103801030100541c1c1055418280120030011245003000c907859450480065a154145c00f9901d11564000950360750700404841034800400050944200068440c03144120062090041c10300412004a0034806001a8001d055041d90844041100da4495031107102550380030b180c0c02c00e0100e01c2088490001032050384002c0c000c02c0c0030185580340e6810180c080f4203001d1002e89220719944240001001 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 256195107 1250 256193857 256193867
    0x1020c0f060417120a200f0c01080a0b0d060e01061e050f01050c0d0801170604050a0b060f15070506060603160c080f0c060114030a150e0f0d03141b030402010c02060d09210e01 77
    0xa200ad00b000040c80d52140c3c002e2020305030f0350b07100310340110300c0c039420b441000300a8000120000c800701c0240300c1c1648844912094002c6c8804100034080d0900c0308018a080c8443d00c0704140106140141c58420101125894a02c18001801c005a000401048441d400100e036034030304910400501300908158440036a00d10074060081c1448440c0c03400324280d070b51183e507100d0b0b00d07440250608000910301c81d8000c03143d412010082d1540d0040c3c0001981610300b980480b4883c9103020340141d1240240c2000b02c0311500c11550490303455204014203120201c080018054000980b0002c050715810003842824480e8402c188502035803202200c03000140018820090030601800000b9102403c00d4010b4602141c1d11100c80b224018101941c07400365142e0840040f40107540f030303502c04548484440352072550181c2880000c1c25000d00100d230040d07100d40036480072079000600407818840f11581e00b4003281c10f000c000312191040c4081012107a51a1034008004060605042e6840c450341000641 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 256196357 1250 256195107 256195123
    0x1140306040c0905101e081006260a021b030903072309010305030c1204240c05100b0f0904020a0b130e100501020c0f060417120a200f 59
    0xc419a182d00e00100e5080c45811000010300703004003c084554482d00001e40a2030346c002e058000c000d095603100403101d0003401058000c414400b02e40c0d01c15851302c902105c00c9607400305418190410082c4030140b2440303524000b070141750500070041c0e07030f1f0003803690198207025a884e1407000e60304140007400300c56502085060131100e810900a1101d0f0714607041001906000c1d4403560702804502c0007209102c000809800c450380003404403002c8140031020300c1040d0043e881a2a0030580f02044645941c024440c0154043c40c2800e060186814658400e4203201c10280340e03544080c0d0320100080306250018403030f0745004c0f060300e810a190402d900407a1400394540154000048005000d20b800c182c4154800020401441e80c1512818001c411345409041486214018896800b2603000c600d00031000c4810203800400481c50a440c154461552082d500b2201e052405007454503c103002c541001800d061a0a94991a42919115000010281e00108070321107a01a400d503040180001500302 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 256197607 1250 256196357 256196359
    0x11118030c09130201030b09040f0515010f0303030e1c0206061305060603060f0d15151508010e0612070b04030303180309060318061506020618030d0b04060e1f0501140306 75
    0x6040f02e2050006902a1001c01d10240d003001c1007400708002c1c001350310031090105100c0c0065920520380701c0e81920003c2000e008019480441040030400240a80c3c02101d40034a1001a56140d40210700c00e100b00800070b640300005601b0102c10000c09183c103503241042d0380e042c0802004181001c0000c588180001460b190080310751410b100d04940c0ca800a000e00103a10a02400c4044150680780b0301500850301141420b14087c03e01040c40000642c0a0304804a00d50319802c40f68a17041c107400a0183c040c0038207400a441d58440041950244105000350a0704031186568074914a0300908030369000501da4104030340d42500c840000e5000c0c664000711075092401181346202c020710a001c130405004018091450711400300060444040c100d4125040c507000c1c3c42c280e81d00d022000f012448000d911000729081040f0300700307800b65182d2041003c0500904001015619805d5910410300180d8048c0415012100780c228000840c80240c07001d80b2007840c207042000c488200e00491400040d0030a = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 256198857 1250 256197607 256197631
    0x30503070807081e0901020606010806090601080402011e05090306090109171e07030809010b0402040f0303110a06060f03170f03130512030c0a1b0c05060318011118030c09 75
    0x62091083d41d005445003141d0515502082c40140c1568900da5032000c0c12480c007501070f000c0021550741c007074035482d4401c50000d04041444e58403580110303031000008000300e05021603c070000c100032040c0401490f900c402602c901c2e503120248800c00d0b151a400412400e82c5a040030300b001c0000e9441200051451030840b0b1071912000340c241110f40c0d854200c1c103010301e000c001080c010305244e030103015940140c0492000b007080c0d00501c402e01c4103900c241e004a001c1d401200804100092050b0b41400981094000303036a48040240d07140403c0c0e9080340e000c001820000c038824010310200c151061110941079851901e40700d003900d111030040c00024081c1d0a0100c107444003006000090200c51480911048080e41c1c030718020265601c2ca412102038140020089040d650500b0102500d031000c4e00d8009000a2456190a0402180e6403000b842c0001260007250700c404c10380401d00a0407500110407550381e490311050507508483e20714820344144203911403141040700340c40b03803010607400102803404 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 256200107 1250 256198857 256198867
    0x3031505100503130f150f11030601050a050c013615050c070b1f09060503070b0903070905010f03140303101a07052406030604080a030c0e030a0312060503070305030708 74
    0x42c4480404c5150103011881e417200b02c0c00c10814030300082101000300200c10030000e507075038804604654403141c0f041b03507003042000410034070740c005e10191100c0e0780f05140080c500b807074076103802c0d0a40e100070300c2c260b420b103002001e0244964801ca042500400050b4203081d030b803813100c1c1c0300c01c0d00313010010809807211541d80c000b14015a010f84d049990043d0001d62045190402071103000c4000d0f400341c041c2d620004100030102d5041c0441c050b41044074001401020940c0c108036080301e25a00074140e1560600c128813001501d030350b8900519000b011904500030b24145541000a80129440e0038201c09070020420040e044a4800c0164240c0e800c0c10700c602580744440b400c00c0440d208060010385a8400c2c03032038000c0b0b90030034001c0b400c03445404629001955103401d001d00d695104281c8005010b48414002e80100510944c0650011100e1f80b5190900c601040b020900b020441c000640c0040d052081540324071707195010710302c01450264020302e800e618685640c0d0304c81c0034000e0018104100060 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 256201357 1250 256200107 256200121
    0x531052428020c07050a0812030103080d06050d050106140405040b04030c02010504091a03010c0302030705070807051006080a1a150d061116030e040b180703060905090a03031505100503 81
    0x708500100040c1c803000c5545210b183d038499901d0140d8400d403842819a0800030a55500100b0b03000c0e03003140e40078030050451342180d4807207142d030708200502c0d90b000340d441000080c42d41c1e6250070004840e008a00008245090105c40d0858044242d01c0500840c106400d000024000105080c2d1141c1c240c50b14509601c0783e40f004032281e201c0c030b510000143e402c007000c2c2e950100106241c441c1609040f8001c003c43c0411341c2d406c0e0280c0c042101c112001c03400c2480500b0205a10f00010517585228401b0389094040e80c48198040f55125000041147d00290f554002c104a403032852080003032080303045013103140c4500b00c030308849103040400703000700c204998400421020b5005103100d00c003000d0540e41c0314030132140002c004600780c05041c0c0006018400884403402e00d4400c04a0802c40500103010f82840ca1022402d44100030300207004150b40da643c0080c070341d200c0c3e00c2a14050713100e42c400380c100195181002005d035003602e00e28480043c2420810032140e500d0000184142c2c0403410500d4030380c2e07a10702d = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 256202607 1250 256201357 256201411
    0x702040f15060f090f08070512010f151d090d030b0d120f1409010507060209062b060501110a060b210601031403180405310524 56
    0xc024404541d84400d00800c645800c942051192412940c820140300e0780d4040c251080912031141441c2c54025041c00d10440c09c0613001040f940400600205600a00700d020380300b1680d10760415071f4030307151140042c02800c01005008450685686c513020460418044158a4400c2a4601c501f030540d120400800303900c44e054204020f68000d03040582e004040800074100004124100c000103c43c9610384500038107103016a00c80501c181d40d0941805520b1359000029800b060800c0d90200090280b40c210322240c50a201c9201c01680d6a140d48240b09138079201950038540189051110718489503854600001c0e0a0038096000000810000f09000c08140402c00d1000c910444104050700c843e0351441c00510603040f24490100140b100000d080440c0d12800303500c0d1206003d0454040d4101903142c50341004d0f802200d440301d00c04007040803038540c07220404141c010481e014455000350b07080c0f041c2401021039aa0081d074000d002400d001d550443c00310300050202500c10600300e4422070f0400c3e50 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 256203857 1250 256202607 256202621
    0x1401090f09060e0616020307110108060a09050a1a12100b061308030c07050a060507120e03011e140c0301090906060e09030d0c020f150a0921080703050c0702040f 71
    0x80c1c2c2041110031002c0301a0b2103002c01c441c14442d81d15106070540301e40d0710010440d907032250007a80c0c4103403490a0000444d4480d80280c042503000d015808041400480c600c5042e016032418103002903880f01c20031085001c00c80f0070700110f214404100780c9051580c0c001c0b580250102400c880005c0c04000100054140d0090044c0c1c610022542500407a00c049c00000030f0292090a008030b0300c4141c2c0e2803040107040a020700400340000ca050011400041e00c803082010004190f0402a544051200202c0d0071244508600d100440400c0000c0903992800d1282c01303a03403a464110058103242c00030a11000b44018030400f280140e4464400c4180b040719440352000c0d05500c040f4014505159403103039074907040340d07200b112103d01e01f500601c101800010910f2003001001c020b04038012010140504460000380b44840c583d032500312901c00100405058841a40203074800e0500c640c129030014418000144244141440c007814000546000010764100c80e60441c0d01080150075000d2780d0340030b0508 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 256205107 1250 256203857 256203863
    0x702030a0f030512010f0617130506070c0c09060806010b0c07050306010605030405011d0c0105090103060e01030803010608010605250204090c03120f080408090f0a030c0b0d0605041401090f09 84
    0xca05180d07000c00d035204006000e610031061241c200c0d42d884001c4d0030004c0b0181d103e000049088899130703a035007400c5200c0207540301000c1c60490318640c1041c0c4680f810104201c403124002103180c1424810407a00c000d40d000500718125007003041c40e0401088a03641c40042c01240d0300d417040802e0074150b8880c104498409001c01505032115569034120141c104c0d0030640d0211180d50038104188081c0041210f0003146003c10002002c000e04464010341d9140d00031b0038918109600c0c0d620110f1001c2d411502d1600940c40340015658075803406100038036000c4180c10039000c09c80308210031040c0c100e10710030414144100702070043e120380f801d100180041c200d0a2005142d02c02c242d00c00000c2c000d10303210319210001551a80000e11540c400121481d0302c003110010080caa061201020500780743e5041c040041c07010701043e8845e6100e84824290090740d07441283c04181c00520351141002900826005003070940c4c00b4802c1240141d460158107005000b0103c0c101c1c0d481740782c440d5107061600301c1850503030 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 256206357 1250 256205107 256205123
    0x30320071206060603180209090a082a070312180504051905010b1309090f140c150a0c0605060f0402070503030a0b150d0c0512090607180b0d020702030a 67
    0x81d4540315840d0504081000b07540c034a01c2c0000001e8014020f025101ca042065540801d01295a50800003a41c20281032001d1504c00e41d20803c0029820030000c09070b80c42ea8002c648082e04c0c0d802c059034441c0800760b0181220350050704007040040c05611042e01e05c400503040038000424820802024035501c0da00940d40107080005002d410100c420340303c02648207004080c80035a803185888445403051801075051920f440e07000300b00c41d120a40c40300b0f1210340705480c003e903120070b941c465580310110260500f20641080103841c0c014640886078419140e008901a41851480b000242182c6181c5201030041600c8100091141e43c40060b036003007200006008540360445030030016074a030030490f07840c10828941a5560082d141828550400d000100e03070440c40c10304001c04c6c19001d02004020141888014490303415098000f44003244540004401000300b0716040341d004000303c1010401944500101f0b17410701403202c03841d003101e1401000710005030b0b551403c0e1000c240340800c102000341184c8 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 256207607 1250 256206357 256206359
    0x8010c05070606120f0b2505091f0212070c0902072001020a020f0d02031e0717030405030715050403022706040e060114130509010203010521030a0f0e0d08091503010e0103032007 78
    0x1e41040280c427905100f541c0c0c0c2e100c081d0410002240c03020181c06800050303400b00802e41d2403010040d0041034003521030701e600c10041e80c2c1e88110500780d810404088403410741c100265002000b0f6000d00c3e4002000910080000030307400d401040e0200c0f10394a44078002c40c50203540c0302c19034130304000000040c0e40c0d404001060500f1031070515128038a0b4040c01e441036000c0104090540c1d000025501503800c0140036212030f0303142c4244d91b94000d8050348818207000003440004090307034640b0b284201c3d800f20340310403495544840c2c3c22607040303a9000341440d116030701e403001c41d01c0d00c80f42c000345103070650703038044100056140301c03100203100c490180318140820b904000030001040c6c010b4000d141200c800703030f51018103e07401c41b0703d004c10400c04540f601c0190780244041008035109842c00b6044540d2360a0000d00c1c1c11a10000c03c0b07007034405d11000d94640b000003681000b2824080014404044411002421035043c015060300c0f85d441031002500f0030510390280c0c081001000180c3c9503a1024000f210006 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 256208857 1250 256207607 256207681
    0x70503090a03140d030509070621050907060e1c020609060d0e010204050f03060405150a060503010f0b13021206090402040e03030117100c08070f0908010c05070606120f0b 75
    0x1251036600f03440464010400283c520600030300940c6d0041074004054030059061150488001340e540b03c0d401500f000140744206401924401c95000341c10501c003a22031315003800f0020342000340e201c01c81c5024202103a41c4541156020b03035905000c90341190b40aa0320440c0c007002601c00c0c001e034851040b4040c68445906c008420540c003c2084070303c10b0301c640c0d200d0001101096250081220082e00719040140c07501000140d001c642c40c2d20040b203000026041e51508082401c44c0c0e082149000015030300c4400a480d45031880403000c000e00c03900000e6107008602ea20044030701101400c03442c01062440007240031036076260003030510f122100080300d440b5a07444948845000520001c40780900a09603030081c1c0a16600564001d40ba00b13403141111a00d421178115a5090003120303500421882e01008241040b0178065051182c60076540ea1362213260504081045400c10351182071811240084440003460200c200101660452058005543c0310100150410458400c803484c500c0d000c0903071009 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 256210107 1250 256208857 256208873
    0xf0503210c030d0f05060405010e040b070315030308070320070206070c1d160f0504060e03120310050a140906010c1401090807030809070e06060c0f030c030301061101090b040602070503090a03 84
    0x180144c03022061000d07840c0c050501007194404c1c0034041040003548002004600c1e100a90754014440380b0703001860b001d001001c0740c01410990800c90001e9030070000d11500d503500d03016280303145445212180000b1000c0030028540c0c444d5142c028010900420101d06114050702d180004040d0b40316401c00c06440510b01000d40181102c1d01a0301510402050940500c82d58503e1200301d440d85500f4985401c1845c2501d0282c0c07180c00b01a4944141403110f0a80c01013540514010b0207001c6210f6845410081003141184407900f04c60708616614110009170f5440d5100a604142c0a082c250b04030402810401c0da0110020b41480d034642c01d18002d0010401194001c00c41680680d032821207a840d4034002544030b0005200c0d2180c424061004903e040c5010710080150080300b1044940601035003505a0554000c2d19003400781d50008001017101079040002d031440360207a040200f110300c4160f640c203800d0f1400a400600800d502042003000c022040044a41001005086070b110070395070310301008 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 256211357 1250 256210107 256210121
    0xb2b0f151b0f0f2616090801060e01092a09331407050f06010e0c030402090f0c09190302090702120a03151809061803090e04050a1e05070f0503210c030d 67
    0x1005040c6c00180d1120610801064460a40003034225901c1c20441703001030100100c0144001c9910034844140704041d2030f220a1006458032003404082c039040000300c94400c00c2c002041802d14000c01d80d081c990651180b00d603601550300703001d4140310951035248018010202c0007007041c4641c41d92210b283c000000c885049030311408a026165841085050350b600058400941120440c00403501c910454007103554000c48418480b420150400c0c00119040803054001d942007039414018015410f10909040d480b2039180028100c0b8a86c0c510001014400c602d00b00c0b080540d02c5400241c00003580e200d810082000026800c0c04031a1032007410010b0051280480e01a45004e14085c80e07945024130341041990582c58003050b4510704414030341c9040c07005004840e50301503142c140c80080c444007000d002c003422040c0c40c000c20003058a003052034034020b80c122006910310030b20200810340d0700040c40c1160344d84034081d1051b40d800c510b28003890f030300501d182c41d901801301244005140100d50b0000d0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 256212607 1250 256211357 256211401
    0x708030d0632010e030c04090609020f04020906040603090807060c022b0c02010e13050c0a0206070e0a0b0a020a051f0b2b0f151b0f0f26 60
    0xb685401c20240022034000c520160801c1d6a01c4499100110350f0141c0c800c42005080502a9600e80c100f007000101103845200084596607171b642071090540c1800151024540000d890440c03a001c000000034030b16015911500c0209900c40e003d260420440c18291003515034848400d00000c03006d4a0065164003410740c0180c2c0078406210b0044418615007000160907a894903240f8840145400441c4c05000c2c00e518180c014038051003050b00f0180d544110781c0700d00400d40c1c1c034a8491000d950020f00700b0001910074002c200d8441c0818407603a450083c05401c41e0f465019042e520317000003205071f08002c4135031005491806400141c5400414041da104141608401d04015409001c0b0410080794010f51185003580403281011048004403d100c64401380101e20f07503c0d41141e180c0c0e80c1401d00c5440da2000c10724a49410b01c06500360101090f51126100e40d0a00c2444000741550003012000c1c810030702c5003041038038102825403130242c0803a540c68142c40c030311080032403511100303024510341d49482c10 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 256213857 1250 256212607 256212629
    0x3030204060e15030109020a090807080708070902090a14120d080912030f070e030a20010e03030702010c080a11070314060c040e0103030f05090d0b0901180f0f03020708030d06 77
    0x81100d841c2480b00d00a40e1030f0300580036801c41c0d0a2406174802034101483c80000c0c81003100d07011500c540100a803c006044007170007015030504042007941044416488901d900c0d00500240749203540d0016104240d0b800714004042c210058000a00056401c50081505000302d9902c011013960154080d07105500c50011601c400c0010003014040c0d2000f01c8030107c0b09200000400c210f14424004120020f1b801003c03aa8a41080d0310b0f116202030307000b40c0c0c21484200740e056130282542c1009040d031198504078099418510703039800282c00e81602d07180c000d1003a1400500c0051880c002c0800e903000d8202e59049800b1203440349808211080c0408a01c5030b10710560b00001c0702002c000c0d04607810b880500c6440310040c0d00e19903050f26000010300710442884001d00030b42c5c955444000066448030300465052190f1708000c1c0c4842e0031240f41190b812042d018000460000c07541c4403810010381540200c0050303640b041410308a0a00f04c0c1d41d0131190a50000052400750300b10582c103c4400d0714090811 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 256215107 1250 256213857 256213877
    0x230105011a0a08010510020708100b030613111012060603090614070f0809011b020307020f041b08040503120903031503010c0e12010b0406060f0206060409020105090d0c030209040303020406 83
    0x8108014001c03000390348000ba9030030b00180a21b00b8600e005098011250045038040c1b500d4008850500b183d8085a842310703503031214601d045280400400c1d401c9510701303101d4001d8039426250b4503488100d460840380110705000b40810114401c204910340c200d9181001c01c000c5031211001405428020340c01e03110b0398100240810130403400700030640a9091600d5500c4a2900d444095030086001402030340070707544e01c04144031040e8624000038020050343d400f03140d54504d140b04011001d444100030501817882c01300c80c0d41a481071480c0c10200f40c025814000c0f6560380d94138006245100d8100c04440403131511003401007603200040614050146c07685003141050744401070600b00c2c0d49e012450b4000445603010749a66003000b4000c1006848401c0020500c01d01717035800f044c01d40d00154001340004692504121281d039061200c0c40d001401200c050202e8549078000800d135000d200f0f80d080c419120440c5000400100102180085501521000d40c0d40740c941005002500f00d4030130300010404d2405 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 256216357 1250 256215107 256215149
    0x151a061b120f0301051507020604090608060f070206010611070f0b03010302120a11090a0b04060303270e0a0b0303070f030507020901080607080703051e040503130e040f03030923010501 81
    0x942d55105951140d06085130f190204001d403211024281000b02402007081e9800342c2c8402c0010000341180d5440030410902d001c00c49890607070002c154140000c2d01c07e062140e441d40c049481c0703044071788034a051282c1400c009506d50904400e035004003030718902d1686c00607200340703104069030481c0e00840e070364103541d0b150341c65040d16560079841c000d0005034100c55044891030070b071200c150410099400092450b905102040448909400a0300411860f01d0703600043c440400c062013203886903040c0c41005519191b10010410400751410304244c0d11014040c0164404005581003540c0003e1002c00407181810040c02c9079012640a03409032110b6400896076000001c2c1c000c1c0181e6140c3e494110320343d20300004400400004e050446544401519032101045010b031003401386010f800a0365490000f458141c510300c05d01d50000c07004803400c40400c40810108210055083d400d0b003000b051452080c50409003180d0f0b240100a0703030b07101042426840e6a015030125040e1078210103520a8148402c0b = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 256217607 1250 256216357 256216393
    0x60a0c140c0d080a06050303030403020a11011803080702180114010e010809060f04060e0f0f010606110d180e07110609160909080903030307050703090b030103151a061b 74
    0x4515070010b030b219401d0100024410b40c01503a11907074451000980700d0715000000e09661042d1000c0d001640b003005140188480d4025143c29044242801c1c0d84107551610068039940007484041c001c0c0070080307040340554036101307000c10004000c1009200c1d6583c4551a17110349207244040580020208140302d00c007035006012441c0180d00200040c0000c2d928054040345d00302006008544044d150a10414044401c000c0c21100614020252050130f000d0360030f80707085964580c03104c810846120000d410134080030501c600c452a0b14075209101601c2c142103c1242546603101c0030281410754200000c03141e005e109201003041090540300c1d941c40e50619999140300d90107441c0347c07042c100e84040200c07020743d0340030b1941548039505481c104036402c000a415500102c4d543d10100c1d070001408410154040900b2010f018004035150843d41940c039500200c1c140311000007162907640d0314003540c41c0170110136000d081f2002013815a50300d110440724880c20804016200390351040aa20080c440011 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 256218857 1250 256217607 256217617
    0x5070b03040b16020a1401140a1109091015080702011b1b1a040b0105100f0e060a111f0e010e0a08030705130306052e03140f060a0c14 59
    0x2216820207483c2c0305881c00c8581e58945551080d80724146503240042c80105a481024182100026400354481c51400034000f0082c002c3c00300d14a0107154405049180c2c0a48024030070945402c1040c0c0c2e98900303108800710082c1c01101c02c41c0d42031040c036038846520050487c45500c144c0d009104403407030004000e00d002004010500419a0311004005c1007502e0000c0001443c0a03400744415016000307a00a40600c00f41d03020384a140c18034005220324248410a5264000640b80813a884111904014050b980c440410b910034080010010500d911400a030108410000241c07040400d610329404e84c50307054030020008003070504025030340644041c0300e00300e40741c2c40c035002030003001102da502c14989a00c000e15100600400788100013401405004500185100d60000207490a1801000b040c80315204140796603c1c21001b0002d0501c50410032103001c07264004060b01c804502070b40b20301d042860011b6554918400ea000b0480407a429400101320700c0119160b104041c0e40c2002010194415 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 256220107 1250 256218857 256218863
    0x1809010923150717010b0903010b06040308030a0f0207060f05040501051b0415020f0d030b01080f04020d0b100b0d06030c06020309060301031101140c060f10080c0621010303080405070b0304 83
    0x1c04600104040c00340101c3d404800342c5083c001128814140004140003070308614007a0101040142007401c0c01d1003098001042258800d003001d1660307495121a02c001010511083c1e1039050140c481c114a8050301d1030716900c4007060000b099603501c00b50041208480070750b10b40d800c0101240c2c50034544115043d40d00d003042e411624180c205000007614201c00e001c944114403581202d108000024082c118010841d550081000001c01c800103080b00000303030480c28440328040a20005a9400030074042550b030089114007150340e0b050501e4101d07090395019582420000a15500001c070503444141940e00c6400f5030300146440328800c030396034001d5848180c0c00c09010001070001c1841000410700c540d00500d4040704078807885448d85026000341007011065400703801402422040328146950101024614142c440c5c0b900031030a03501c41c203c0c1c80180c0a4440040c9a905d004080c922400740003d102401c120a940e40b40780041000340101c07030641c1e285c096100c02081000400c01228061a0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 256221357 1250 256220107 256220113
    0x902150904050114060403030c15050708040b0108012706060506180a0b0403051f060302130c110f0d0c0201050412050c030f0118060b01111501060909020708040b091809010923 77
    0xb003123035030590303000b50410380642d00109140c4001001c41114010a0320442040e1342e107880506040c0b078014610101a042584140d050014060003c901c0c0c0004480c1c46c1c5500140101c009924144003005020036082550810030014440340201c0c070000c4541e084420503203202c09141e42d80c0025110a009a000090603034002070f99149a02e441130001080c402450714000907041e9480d800900d40c401c0301e18440252503110103d10304c143c1d4204100c1e01c10050800c01403c00d140c0c0c001d42c1540c0341c103103229a44061219a14210055900c52810ba03000382920000381400e154880c20b040d6a1080d007091114440d01c5085070010b081d0106005403c2c90a0b07000d48041c00c4030850740c0d201000703002c11006503030410240ca040301444030802c000140c41c0000c4095140004c0d410514010200304d4141c00c00c80307003940100050400582824202e03412142e800b1204c98035400101c0000d00d4a00207500b52001031a500c0051010f03901c01940400c800314418080c2d51043c4540342002031074014004285050340e0 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 256222607 1250 256221357 256221359
    0x40506070302070503120103051f1803080c0906030903220f0b0307110a03081b0403022209021f0e01140a0c050c03030c0a05070b040b0d0f09021509040501140604 71
    0x18082c1d000f9200f00f5100348140c80c10500340d80d43d2140f054009070300a40b400d82c003001c0820400c0006c0020300022003c1c40400307108400008101481d46c80b1400d81c000c0800c0645c400289194002c1000e8442e56040184101e55a051a0070304030781d641c1003003a030004407904401c2500c04404512040310b00b01d5145221481c801c0e0714009085c10181c000130010700c02d020180300c0400c103144041c450350321711610940b5002554201820305002040d0007504200700e0110410040c009a5100d590a0800280b01001c00383d15030b0900100a0140014000007900603940030b103018a50203004a101c00041015500d243c60710081500448803500f40ca222428024010000a200c46209550f02081c4074012070440341c00100c03140200389158010201d401e11078104180600400c074080c41008000d18620034242d08143c2030210303203292032045064140f05155100d071072070082100c45d0009801150010300a907017100075003074440d00f5a8808120180300b40d10300400450041c1d40d031018161047d04c007070425030400d = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 256223857 1250 256222607 256222621
    0x7080d050c0715080a05070e010c020405060f12070303230a080a09170706050f09060105010c15060b03010e102d051c031149050903070905040506 64
    0x25a018004101c82030080007030108440700d1280d601d6042d039000f41d540552a14000901100300e5034050303c20801c1000300354011030242e80c0700c20307410350aa404440000d19621080c0001c0d400e0001c0510060b00051002010880082d001c6000b1044034025202d000031014102030100310352002c8600700c0c810760b105100c0c00c13444070304c01d0342801c0d8811410900080c0303021442c2c80c0d201c6601c0b10949084045100090384408210a902501f0342041e10340040c0c1726507040c200e450584841050046504020b0006000710500031403800d44541e8101402c400c0140c5a1a6050103100350300c01d003d104080303204000407603404402401840708450321040980044600c00b041c1c1030800c581890765062552030440080382030740e10b40703120507002e00b500f81c0c042800045500d40070700b010404d0040840d85400c00a07039441c01843c001c205502d0350059842048041511103050450090300c03128042c40302c5500343c0b43c002071a40003c0202410482101140d0a01d55100c14420030354101325402485a00808046810307 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 256225107 1250 256223857 256223867
    0x10c080705010f061e0501020105100504150b28020606030a031b0203030d0f1d0706210c17090d090e07051c061a0c1e030412080705010e07080d 63
    0x14551007040045440f600c0e035220403042c0c0d00540c20480341c0f0b65403008107503104004204080020002800284904c0c500f460f078000c000403e0b485001c2c040e42d02c650103001c0034031141200c000505001c040543e1254040900c544181d1805000c5480340f901e0325244c0880340707000045c014418030004000701403601043d0b40444000358821500ca80700c01d07900621f640140e070240003070700c0b010030110300004003000041c1034081510700d401d4200094112005204180300400314050094030117034140b048004004202c5035848040b5400c10541c542d207070400c2c110703065034003110441c0c5c10040e4500c203948035203582c401d2689441b2642014400700300c1c42c62040184c51000d40d221a032040030350500a0420342498828170140c0c500189408215075a200d0602141d0b48400c10f0b101828403a00c100d84c10410540241552110300d2415481d44510600040050850410854010b0000804202c88a05003413401020640090702c0c2120341d0b500700301d484844403400281400031600304038010009280c1a000a0b10703 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 256226357 1250 256225107 256225117
    0xb030402010f030e03070f0c050d0c06030203090c04050a0e010b01050f040915170601061404031a06041b02011a040e0a0b1003081912050105010909020d06080118030815010c08 77
    0xd254039154031609050382400079090079400b64182160002c081d00d48071048c94101d800580c0b244900342125030100c2e9078080e528055882c3c600300143d994031815004d03481d01c1300b40211a50301509080400400741181d0300400c02c0350000798020f100301003140b40150380601507200000c0b40b420082c0000c000c04441a04040b61002008811000702c03901c9000441d100b101c0c417010513689a120b14010400d15501850050055032034856032410305045a0350201c0401e26402001c0b050f44180d00407512581d5103920003d0046c00913184000e1135401c12601034082e10020b200b02c00380e4010918a5400d908090180c0b429854149000c0c00382c16843d0381e03481c01c1c5000043d0030624400450b100c0807000900c104010140404081c403108040d090b2071741e0041003c0044003440031600e040c403004000590304041074106407a454100541c07214280e0019000400340743e40019002d6080100b0f41d0042c04101d103810b80350354040e0360f400d070303655481124080c1c90312000c5050600043c0c5081d0420046020030b80608 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 256227607 1250 256226357 256226387
    0x503060d0f02150403030914010f2a03030b030111030402030a03080702120a0201141e070f14070f020103060503060405060f19140603012702241305030d03060b03040201 74
    0x81c03041070032500031403011602c10003003100106000405106041e040711707000d402003c0848040803d80c1041e00020008014040b001c001d001c903c0d86505003907540d03011808008910300804403110b008a00f4010040e14031228054080d520342104040c5841c1d00400300c1c0d10568003e00148030b824072580d41100c08000003400c03001180107000122084000910042190301d00aa0020a544000b55641124480068040c1f4003101d0460101c007160f2010314002176021350f0078140006408010003041e01c40005440b4070001041d000544881004400c01c00018007034001e990400c255038440052550390841901e003e0603c4d480030000840401c1002c020980c40050803100c00d603251281540001510301c03405030721103d0303408074040201c581024800c01c00000f03c3c1c66103180c5407201e400d003000c50590000c040603000d642c00d66400c0140140e0485801c14200004561968406a507880301c030b000f40041c050684680a280c08200700b0f103110340a18810b032212050400d145071901c1d401900c201148000030 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 256228857 1250 256227607 256227623
    0x170a021c0c0e040b060301141603090201090803120a0f09020901140a0506043309030b250903030f020a0803060f040609050a0c03050105030115060c060b03060a0902030606030a030503060d 82
    0x202e140240e41e1500ca020b00e104036003000d040c0c01c1c29010182951034401c0e450b001350440c1e1081103071107114580da140c0280711504001501c0d07551400100d036458881e80201c80f540c8030014800c00d5200607428a02e1140c01c04810403c04000e5002e0042c065415020010f94006103883c01440642c000c0c803602560208010101c5074400d0380c503800704070a0341040d030003c5220510039207103100074403070f014540403180256105d201300d410400f0750142c0340301058040038045081d81d1000540e404c0a4602d6911003009001901705110f04e603a000404400e02408114000303500c1c0340c0c1c040e070100c1c00041c0c000d0080e40c0c04a0f0603415035640c00300303204045141424480e80141c0341c0d82e002564100034031076503005000401c804295412050340207403d80b041a44814044da141c071a110f8039000c0d80c007500c4400d8900b9440d185030350b1103ca06024000d00f06107070380c05602d805044103101d0b0b01e2400c0d80c000c2c2a014401e0301a65000e40d85c0300304260310b40100700c50103404900700b00000340c51480c003012000100c074030420307903 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 256230107 1250 256228857 256228859
    0x3040308250b04020f0f09070e030a050106080607020f0604080d020a0e0a060e19080d050306031c0e04063c0e0f090c0306090c040c0309080a0801170a021c0c 69
    0x5404110303001c194041e102102900c080c4002e6040020740ea4203080419104403030f07502032820200e00b202c05d00504420401140244181c6036075030078004601c0791a041300083c020141c076100340381c4d210042510640094403d55a81d040c50f4032010a601d84140c0d0881c485904095610141401952000302018100012109451040e598101c0c00780301414095660788030000546050003025081d2100b20f9214039600c00d410070440d50b00280c1d20392030800524105483c0c4e182c0d0004240740c01e620745010442101c00d800d100b40b0082e404503080544400884080c000c140e03a0f0340302418100200d00300304910307041c17414654030f4100c10b19036004001964440b142603681d80c0c0d020b90001c80305060355030720604200c44042c0910150100503510342201c08030090945400c00442c22940c5107241110386005d5602ea101211804d8000e6121804498000c0180c41d643c0041d160002d02c0103c0900640c8017214084003d08901d40000075006086540980445410160380150319081c440b0488203c0300d051580c60 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 256231357 1250 256230107 256230157
    0xd0c0b1302130e0601091a0d020105070f03031b111e1608070f05010e0306070c060b0603010602030a300509070506040303050c070b070804120203070816210503040308 73
    0xa041c0c2c1c9659484074001580e035003042041424400181e1010b00c042c1d04141ca02c1900148003d004500c00100702d8000307104810034801600e183c02240005002d1441070035400007410b801d0f400c00a49000a201095005140c043c403d8840d01d20414a510059102110590b5205002441201c0c40c450740340c00c490340506181d01c161014460760704420820307089200200280000c002100c00a40424200510340400200100e41d58a000812100c2004000004030003400f00640c4046131440000d8400c65030b0b50b841d081e019542c2d0340300791440300c00138036210a80d1030420041e55000410b1980d440303804030307000032013115600038003006000b0440c04e02401c07500181079640c900c0140000c500ca41c03510364030340c00c103d400a414291554014015032030208000c900141c1c00c8000c17103003625444101e402d02c03688907001092412040703400072042841440300b1501621031440a80044070031a16113000f07900030b14609004030000d960700041142c2c0c028041030001071780c84400b030700040074192103e80a41c901c1003 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 256232607 1250 256231357 256231369
    0x121305010f09031205010e072003030429060310020702013f0501050a0b070f1a1504060e0a09051f0203151914060d020705070f06020d0c0b1302 63
    0x19040d4021070b555440c0708402c2640000c1100e01c1103100f000d04219942c07410b0356621440e01c0042c4072000b001402c40c0d031448001c07806c030703000e16581800348201c9889160500d0100900712825850850010042c00070100c608400c040e0b45108500c0a0040d017a80c41c1194042c0e0081e40000310b04a05000855640c1819071000c2d0350780740960039079035407045110344040c60107030740750034038040700c04034080c2002d0040c052034842c03c052000321051001c80694400590425000c0412040380050141444807112116950320105481c0952807101c1c1800103650140c0422085403046d1013031002d00104400000c0382142d540d403050400c203009800340d404c40b11407000a100045c5103180f521040e540d0102c103102e14400242c0040b034a40b90180c0e40124010300510070b07070400342514031a51082c07144a20f050000354031410156401107030320540954440d02c0910748035803941e10354091440b41056900000451030700c00035008040180075200c12081c0001070316141e44c10070000300326005510701141c0480058580b1 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 256233857 1250 256232607 256232621
    0x102070c06350606120f010e0f01061403040204020d18021f02071403070806070203070312050712050a06080304030312050c0307080103080a03060320030f030a021e070b04031401050a02040b12130501 87
    0x400c4046c0c090b604108049495040280182003031421040c0103106058000b4500803c140220b8060b17900c0350f0b602d00c0082c01910a44507031880150030300603000b81a80f0b80c2101c210340c680c4203d41c250500c000c040d1103074600b603070520001070051340301070b004019117401c0400081034004090306403911640c07140c03942880c0031025615030707005034800a03d4405066100000d07200c50045044203000742d041c0094024043d182c4409a0b6918550f101c0105480410a500c0340c0c009115400960351219500d050140c8110300c094008020a03090800082c02500210202e0f48200c5558940c5001d0780d0035500e0f0500130b9000105040c007450b580e141d0110108261101002401c00412a04455070185505150800e4503203011300a01e03501c240424000c547c0c003c2601e2026607072482c40b29100e0302c942c441c42c03454804568488040701c1c40025001c82413204003180c000440e454030000b4031850300c4841555040384910300c201c0760705610900c001c6038110707100401c40c0e4002d061148590141100341e1a040e00319100 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 256235107 1250 256233857 256233871
    0x40e0606090402070f0c05040b060301060f0e190611031204080a030e030f0301081c0e0103021e030901021b03180906010e0a0b03010f0e15040e030c0102070c0635060612 74
    0x510174030710040001c0420310101038001a07405216469140001c039280f4001030051106029040440c000c00520401401e601c0b61002071000070400c0e0060780c60b0a299103a4000c010010350052a40107443da000400c5661880b07803036070200d14a5540c0d49880c0d1498011030440c1c000c06441e80040c10130340000704040c0803101e540c050030a66075450b01540c1850204440320480f40301144003074548e0035541003c03403903c0d030807000e090250340c4607941030540712003c5400c101c200546002100b07001a684055010f44180340b1814890506802c0740c041555890151801c0d17940c0103485a20240f41a080c10452550000d40c1810b01c241700d8030710f2100050840407190030411100c02c0c0880100900e40451102c039000f0311403812201044e00f4154a05441c01c40107000b418096621003441c42c400724020070451700000c4551000710348031030461401000c118040d01c14400001c1032200c85290684490303820510302581c46807107200c54440d6032400d03002503c000380350030740c08030040c001c5000f5203400e40c080a00c0340301 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 256236357 1250 256235107 256235123
    0x280305060f0103050708060f0406030804091d120a030c0504090e0d0201050705071502030423010203060405061503070f02071815240c2d020a06050c03040e060609040207 74
    0x5091424032081e180707100070882c10103041405011115801010081e0024001c1c1d070440c2c4209642008580900f07640d601c020407951001400003003240559100700a210420b6001d485200716254050b41d0743e1041420403001c0e01e80c00c00190040c50300a5108032100d9140342442820300303586025001c2110f112511102d03003070300302c10190b841c155030a100b030700e900c42181e0502d1420300a40340c45030b00600e0b20401041b100c8590020202c0c05005603150760040d0300b01d00c160030881920302101038501079042615042d0185003040702041c1c0724500078046140034842184510308560342d103482110310444940440c0c0560203030460115000465044480d00c560701c290b80400c08007c0310000124001c1d90b5800018080c40300c90030540c0d0000d01b40c04d50340d0b00714401e00c0c001c01103046a080c0003403194a141c802020320003400d0f903c0100916001c1701d402d5194022100300d00c0b01075480038192040e00c0345000b615030300e030810001400140148414180c00080c007401c11403c2c9103041e40410101c0e4088c50050390465 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 256237607 1250 256236357 256236361
    0xc122205060901060b250f050109030c061104120813030c291e0d02160c1401080910090f08030a020309070b04060906030b0105090405010b030108160e010605280305 72
    0x440c09006640c010146888500c2c5041000c80903c1ca03000540706070900c02840c540080020700520f001c0907c5481d801c41c00820194816203070141042003400c0e81194864203020070074060145039804e8404403109044c0f010b01c00300341582c031103c2940c48010803003c290f01c1c215000c00498064540200070b400751014a10b06003c0000c4400c003150442e08103c034a0200800c404040d10f1007081c40d8035081c0b80108402519a070183c1c0b094006130151060300882440c1080303506090041902d044400c542044040345406c0700000011110701204a804500580c019030031100210f2a0340c0c041e05080c0d01454200d4003400c8c030782d52003403110340c420b45690140d41d8010061000441c1c05008980040c00b010300000d01d450301d4041c000c0d00100980c4200d10515a0703959070801e80d64010740498041c042c00810811030ba6840f4195035100c0c0d0428010380d8030b68400c418842503a440c03401c041760169208480c81003001c0c0c1c43c05004645a500015500d1070300302c100440038403c03211404003411500110b85003ca814 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 256238857 1250 256237607 256237621
    0xe0d02010b041404110907050c0316021f1d011407050d02011d0a0b060109080d080f0c0702060904022107080105090f07080a0f0b03070b03010f0e0c12220506 69
    0x280e00d00d81c01403a510181c00f001d02c0002160940811807010041c1c607140d40507a40d4600c00d0706c0c10301401031284258080090400340065611224a901c00c1c0300311058004420b41a0b000f1080c0041c01c904200031500030500c2d400d250280001106036048145030219950011030329503c619000040112904d500c501040d062458080c000c107805c0264544001959001d120304560f40e03044c0e000702c0601581e10200c041607603a403090403440c0291092004441e40b0702c003802001000664111070308000d40ca400f00108481041c900119100140c00420503030030025444108402503200071000440b0001207640300b1210181100c055110707992a407140c01707840d850407061202501d0000c15060080c5424000c102c0c0c101e800c8040c1980088071a840054408000032011009100d4400b00517850b10405000240b00d103801c00045041c0d0b10361110b07600400355540f0b10440c1000c0c0664103214404018048a11a80d0b503920010794002c04000011230985402c20711300d90501103a610035106030300480104414 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 256240107 1250 256238857 256238861
    0x15090b03070b0705031204050a0209090303071d0a2c090a060c03020319150504021b1006140114040b04090c0f0801060e010c020301150f03031d01050a11010e0d02010b04 74
    0x9200b00d0111a2030048140d0312162a44503101e81001c0300c1c1c28042c041001c4c804100210704065601030300d1007140713082509a040d030b40c1c0c00448800000030b07094034081c0051416001e909200b000702800140d074060038039180c1420380e069844803840b030641c4040805200c007a602101c41c01060301c2005404119644d04102d0b09030307000d40c9800702c00d043c01041030107081d0f59111030380f0548084d092000140300c45035407074110505038540d00c0b10b5801800802d5040f0000038000c141e058080c148405c85616405850015056074041d05c80d1104030740040f00020043d5000e10710602c400306011302511b281545a03c0440c3c0c041e00b01d6000544015510449480c006d5002901c01c1341e90440b905020a0039807401078000c1551019a05039130400c0481e4052504544013500481040315103000c55a102c50744540040031029858130003500003070345031440c03146504420410b04034448010b9503154a000e880f400e007614060141c0074072240d03565850b01400c04411080c016041944450750001c41e602d0381000c02c11003 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 256241357 1250 256240107 256240109
    0x1a07060b0432010f0e09010f090503030601090501140f2a0705090708270111070b0603070f030b0106050f0f03040506070e0406050603041401020c07060c230a020409020415090b0307 79
    0x500c18450011310090400c0b610700700c02c03220070b00f0100300c441e51600d491602400e0340080c0941a2400c00c8441d104100c0080041c51140d4400c0c0d8510420340da6440c011520444004403d055200080014681c1d10107213a00032310f8070404c1d10010076600800e012484d000d80ca44400007083c2500b05540234459841c0140000e40c01c021945040f2400c0e0425000d010343d411001c440b80780a98020b0301130620204402c5d082900c0c820000402d0350b403200f44904160580503812150300703110b80036508020401a100c4071001c020743e5000104c0f1000b0f60708150b02610381d0360082550201c0e59205120460189807045d00451113980b007180980641c0c142107202601072000f1044152190341000002c0c0100d40b210b40550384d00a0304491120100090500814028402c1c041d034400140a1810081a859000700e104d801e0244141100e22020701c1d111503505e0352011140070940184c000c0c502000141c90a40c1050510030700003880080c007480071a0726044c101100c4d5020329a0140c903028401104d18040c49000 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 256242607 1250 256241357 256241441
    0xa02060610050a03090c091812020102030f011509030c031505090708280c121707030e22020a0306091a030705130b131a0a1a07060b04 59
    0x600d0490079031001030b207103008070041c140415644188000500021804175401400c880000f080010300b8907004900040304e03090291a141c0f4081d4070302d05800c0c030500c2101d22485540d007981d070b030590074000c41c582907812003080503080141085012000c00c41c5402900e00661140068040400000c88140b060328070080c43c40046401c102d0007003046640c04101c10000d1000b102d2200301044a00c08051400000391201502c55401c0b8a0042940a050400e4040040c0581c0561b450614001d209100d03502c2100b44c000c00213011441c0240c0c0c2820000400d0b0000314080c0c6400700000c02c03000d002002c9030041404680003079142d410811108907103100360b4041d40150b160440490f00342e1008260759044a2103064000c1c00190181d10030602d0941c4500300150008040a50b20314500381d07040040d200100d00c6080200c0b6a2039010480d190940c00751086550300c58022244280c4e00e04007245c01d4100e00c405941c400d458094980541d5910b1068000041d0b07242d10341006c05025008815204014031486 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 256243857 1250 256242607 256242619
    0xd02250510020f041206020c1219051605010903020105070e011418060403240e0a21050c06010b030a05010e0f0613021204111009050915030c0a06050a020606 69
    0x50404228082406840007594120250340c0d0003900181020368495544800b1003000d813101100c04003c0c054004150140540c0c084401c2880c01e4201840d09109965003000d00d00c150700d600c00410350080300900354a0020500021030944c20351200c500352102d400044006075503400803c2443c5811440c1c80140007400e281c020403011001560402503c40c0c142011080c5402e08217486040c0c2d911400c80e00a0760340000c1281c0b00c0030700400354462100d042002011518240300300600401c3c400104030341240d400840c0c0f06c050742c0c2c11900800024100c648958100a81084500070741641041194024081307114800e91b2490035984240c1102c030306030008240d014480c0b003842258400300300340e10b421000c02c172203041038240a540460000d101e0a140c0491080340c5c5006c01c810b001801070021802802903940c25140600503030b04403080c00c6c00c1e00606030700003c0c0030041040e5161125404100070005003c8401c0710440b000026074032495607005100164000445200440c0d061042300d8000c1030075104 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 256245107 1250 256243857 256243927
    0xc0a061a011205060f06040f090b0409150504060f020f07120503010e01061b15020d110a020706270e10090b09010306020a090b03070c0c0f03030c080319020d02 70
    0x280b0755129070054404442e280d001103280703580c58a80000c02c4810013009140e403255030309804008000c1510940c816645012105801400c080c0240303088154010107450b040d20141c00f100c8020f10700608140d5040e565291040c030719110340e20040c0305044009840588949552800c0704000c84040c6804c002c10005000402036141c540280314150f819901b442001901d054004a050480d204002341006800d044000341900059004204c102c6178241c00380021585068036510030b108520a81c00180c0c0500400c000080c4070b40c12000c4030094903061b10101c2c1c81c2848040c0a1380960740c11089621014605100300c100011100c800184103d14060080416410000d80000014403003e05810780009411f03d01c41d2084c01198050304101910584038100140c0040056074030003812075100c41c50004c08559043d1200e0800107d9502d035448842e06411580d03440b5694002420542900c4840b046c20216510540040d01c14a2410400141caa0000d64010000d80c2a407100e510000348803941 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 256246357 1250 256245107 256245109
    0x90c0b12061c020631080c030f030405040f060806070e121903030e010e01150611070f060f050f220506030f2205100203010602070605030c090d06110c0a061a 69
    0xc5020b0060b4044441e140c417000401c580c0071180f50b1110745510328072601e4100e1740001e8485803140081c0c0324543c08507080003008106045e500c40c3d030604040401e03070090004105901e40b58201c5a840d411440002c101c403565003401c0d510b04002500c03800d0108102401c04c076198104105100f50364502080104028491031181030589514040058105a00c4041c3c441a0a4003500001c20944031000200241c41d142c0c07000c5400c0241030f005030800204600f00c0c958040c94005005070541e05992241407920f440c02c581580c00e00226000c06c4e05019040c004810080440c02c003030304a65400094100c1a207030b00e0100d404404485801184c0714103800c0c4144406464a4100c0741d0f802880140055114800d8000b181340e007400c07880300100144914200b650160b0155000396040f41c1041e000c0300c4103e5243c40041d01c050008a4011010f030f00300f8002c44405290900030109402c0c0220000181010007a01c1d002d040d41c8403020010156000b200281c081040c11f1103112000c580c410100c4440242e0b0380 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 256247607 1250 256246357 256246399
    0xb01081e0103020f06070209040b06090a0902030c06090307150e04060e040503070311010e0a050c09071b0b040c1518050105090f060c070510021005060102061b0c01090c0b1206 77
    0x808068051800b07403d6091550710303800129803886d130f00200301118500e0a0b01d0800700c42030f000c03070307046000c0d15215012404510a5000d40100154024098007521816905201c055000000425858451394800154810010711004589500e50765040c44c200300c0d800a11040e1a125070041103000761140800020900100588161560500d0050005c40180ea4032502400904000c0c203030134022010710700100080000e607081d1540c42640d040c8000d42d02e982042d2800709a0b101840849050040c0b5038000510244282d6070107071080079100c10382c2c0d45950105410b1030300d014a60002c00d95101c016140083c180c4182c0008040c24604140390030080404550041011082540200f43c045010780d600182449941c018000191003529990b41c2c00500030750781d01000303c00b181d00c01e18000200d0425480440c40c20310940084a1f16a00c440c0c2031817004020f81c0c410460055695a980a100000780d65605080f00820303500d100c2940300d502400520400903000b6003440d1160950002d0704040710100 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 256248857 1250 256247607 256247609
    0x206060307210201090b0a05120105090105150c0312100503101a12211306020d0509010507030c021f021005040519020a030b0c03070809010b0a0905070908100b01081e01 74
    0x4100c203480c5095440103039034400254000082c44070012540c109100e0340280039200d900d045c9c0340c009405907695404d0002c10700c020700540d6040440e40100c450b1803c0c180d0014000041c80720100e902d004001c9520140140058075400c4158800c03903001c00c00c61400704102060070807410703020003a5914403038211103001d02400119004850140000300704800c10b000c43c0588071400945014a900e05e024041015800700e400840c02000b035604c041501031000a20748000100c90700c41e6403074130dc051801960315812401040701009044200403005031142d00c0e0114078001800c1d0058082101e07024043d00381b030064041014072525020410020400000b18102981e0211681c020348000d1400400d10030043c5c1c3d00041c00404805007400701d1114002c00441c4201800e941d01905c580720612103c0c01c3c0c418850303480d0703031040c4100c1c4144444001a413015801c481d180c1042004155103007442400d11403400340c082d10880e07076203070104c480396040302440d50310400d80c1c1e074096056808200c0e150150241 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 256250107 1250 256248857 256248899
    0x9060f10080612030c0607230a0c02040e01180c050d0503120405010b0306040c060f14030612010b040e0a02090717011701111206041413110303090414070206060307 72
    0x1000c000b08010351640d90100c2c0707a2144040c00d417980d90b0860100940e60304001d699a0000483c07610f80001039207002c0514400d1845690000da182c4469503200b203034040c41c24801664450b81d102c0000016100920806402102c0c1c40c0c112103007c42c0c14106441c0c0040c041c1d00c1140580d51804280d80000e00c088200c0300100401c5280c90700f95200e0b0b09080d401002d0724900c81c1d0701485414180000d10403401c3c41e51303080310b220341d0303800841c1d10000004507000c0e541d0b0221540340c00030601c0403880501e05a41e514071038141010000448a1001000509591800d10303040ca4682004440e6015810641c10041d400005030030003030710409049002240c05441440761002d840034103610072694982c02c1d08039643c5c02500120f040e48a01141d03171071000c0e10310240c03105481103142060104448015800c2c641c031a0b4511a0050094680c0d9198080c80d602c1044c105030b0305000800102c07200b59194454541d40340301008804495241042010f4900000a401e42e0301c264060700301008022100340a1541e0001 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 256251357 1250 256250107 256250117
    0x31706030c0102030706180c0f15020c09060d03020f06011409010506031e070c020a27090503040b07020409141606081317090d051c03020f040501051b0a0302030909060f10 75
    0x65021a41d0045211f640007090b152075428002021f0798601207206c1504c1500d41c00503440c85480c030090341c3c1c842294941079080255140051060300d030840d000c410701402401a02e056200d041c151505021090308440c62074000f180c1625414240380e0b440901500007503403140c2ca07600f030844800c0e500d03580d0b800006c4840d103200c07400070301039602c14680c0116a40c0d0203011088196195084102c2d031200d11046040f50b11a548006800041d4a0007a95000e0b50003c01552505040c5402e80c0340c103522008083e03800c96125050400020243c0c5c40300308034008d2a402811320404981c1a034002511594801c03000c00258006001c5442e1074056151002a404032041c181034104880740d020501804013803540c095100e515560030307c1004079102d480102000802c2921940c0c0c540294100d000d034248072504088244028040c55006800401150920707806a44c054820031148601c0c013610000110300507040450401220b0409210303507500400c0454168624198000c04103541c41510404042082 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 256252607 1250 256251357 256251371
    0x302070206030f0c0412030806040b030c1f02010e030408030702040e06040c0e040201120507020607080c0708070b0703020708070807052a090c0c010603060b0f0402030103080a030e01060f03031706030c0102030706 93
    0x404d8944c11540242401e0035444004006c9040241082c40120f44180c0264101042c8490910300400c02e180041c00c0204010b03102030100d1194081300c3c420144071810f565880b0ba545000d00380c00c0000d440145004401182e40e4216841400192060030700c200c801903000304280800222080d080031b042c0c83c0d040400c00c0040e038031800100e480d28858028110560320340400d2200c66580030a01500c9010141c070307500025240c0300c0c0188801c1c0f040102c0603000386001c3c802100000c402003281d5030020101d24002d8103101107500d0750143d50b4401c20080340c5103400000c00b039040001c184500c0d00e5549a4034400340e012011108240700205909640521440700703140040c403031543c01c1c41603801d6007000e50001c10600c0d4a914081c002003488280d001d1141400552818481c0781c40d000b01c90581e0b50055409041c40c02210b8140c01510b070b80c00e00040310b5503c2c0d840210f280031075000350300011130103543d5500070301001d03c1340c007000d002000d4200750003138100300007040c49039800100b241c004550002c1c1c001401 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 256253857 1250 256252607 256252621
    0x1915080907090f060f0b03040c060221130503030c03030a060e10050105090a0e13061d070302010c03020703050a0c05010f0201091709012c091602070b0a03020c060a06150302070206030f 81
    0xb8184d075000508036030680c1e800810a40d03064005148681c1c1b2a9001c103454030b44844007a6524107036001030b000c40c1840c01989a240030405809800310580160314040c5007600e0302e00080c00c0d500b041100703546640c000303c1045a4041e40780100780013011800900400c60422252070328852030b01b4054a41407042c0001da401d03003a103801068800038640301e05080002d00780801d07903903910084100207a407854180002c82d41540608401031541000c404001e0418038915070054038501d049810580542c01424000004101d00740018407007184030700c031540509401c08002400e40300b0744801d20300c1103a140c901c03850005a48603203680030112040f000360b80c80d5400364004130b0b0158000483c0d455032410844540d0712400313003044040d0300e5440840b50407038075684803d14095540349203075001c0f005901074181000464100d00003004801c2d4586009880d00144040304e0303203854415204650701940d2000d0800104201c4d12003807079800000c1c60154334182c460f400107003041c000604100c40d580c035004049119 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 256255107 1250 256253857 256253861
    0x702010f03060b0406110c100f09050618190e0405010b0108011410110a0c120501060512060402131b0e090c0f0f090a050d03080f0a050403020a060b0f1915080907090f 73
    0x40004001c8c560f900380d1052160080000300c5100310880400c1a00030b020540345014016105101c0f00c0c00101c907500b09019081040340d8054480440910007518004502000d0b020801d0b407246000b000041003c85814000504140050780710101c0c68083e030f14a091199900c140d403d64004c82c900c1c00081004c450080709046c004080c2c0300802040d012400005c60481401190700034501840080051070f50703403000e1009500c0c4500640800d90888000500186001548904204101b03240022040c54005204007030106000d10f000100d00350303030200001880d11030310080c0c1c0500005285405d000c40980d080340c1c1d034010013034045003031130010812050700c1d1180d5401070001e05000781040b514400f507043c041c10700041500c4400a9103501c0b40010748000c5079004060240394183d0050404402a032940c80040440001590b80301c4030030190007616640b204551015041545004204c044c601500c58030b08009450340340d428000306404000c04904045031200446032107450101d0040007041280c3c1c0 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 256256357 1250 256255107 256255123
    0x13090501051e01030b10081005060a02030d11040e0c120901020906070f15020318070b07030801060c0201030f05012601090b070f050706020a030911010212040b0705070306090501020702010f03060b040611 89
    0x60446d0b04058007040c4560310a20703441c01088203403c0e4140c02070b1900140201e0780300324a60080941e10800140440f42000e40c019a02c0004e10a00d0303d007480d44643c8410085101900d4501c44800d02042d0307000d01b80f24a032891a04072014130021440c050f0010041249402039040c042c1806038040c001d44180110404c0c0325000c00d1490800310340e64130b44140c0340340900003e10303840c0f005441200c2c004110070704c01c2c034121101d16805440300c401907031800c03000b207a0300003000c2000c904054580c1d5624a100440d0b000d8507020f8020f070103a003c0f620048688405123118410110701090b810b02e04100c010584121509820103080c0c0303041c1c0040104644185c459115040e0300801d5584000750603641030fa41035000d001201d1041440c50010110900120703078407030006000d03950f41d150800c001c206207003143c002044498864810ba81031180d40345c40304000c49403110310a4400e40d4002401e041150b80c407103d4680c5041c4281810041c4030304108511105028600840d02800760401c1401c0e03682c5001c01442c1 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 256257607 1250 256256357 256256359
    0x604081509070b040f0b032703190903020d0f050f030c06010302090c12010519080106080303071404030b010501121803090f0b12150105120c13090501051e01030b 71
    0x240540404100444800030031925859940600440800d50b81900001c43c2d007110740c2d00c10342c01d01312418142800d0590780041e00b10a00c110601a0308001030b03001c100c84240502d500d10185031a603200110854681c81000084400c2152040c0c09000607501d2030000a8925048144454501c9207850031903d40480751080110501c000318604c80c0b2540c000440a050300d00c26150403d142e01d071000b07000c1d403a0040183e200d550340c0d10301006200c141883c090003040790010040c0f40c2d404a58a410040c00c40ea01900310920f142c00000801080c5a0800381d000c1c0901d501100f01450680380d81c031035866054040c09168108100c0c80e031403d5021040750440c12003440e90b0091401048403a1402030012100c900ca2080182c510100010795141c0300821741d4298241041f01d04150781e5044a041c1241c82465071950500c01c05110b410440418000200e00c10b58110b8600c0b60f5071544080c002c6a075014507800303140c4a0b4140001032089441e001001c7e842c2070807000703021035a80400e4005034041c21034842c0407 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 256258857 1250 256257607 256257613
    0x3070b1e0c0408120c0c043b010e1f0b061b15070305130b130507060203070c092d0b031b0909060105010906120b220e0703030914060408 60
    0x702607aa80d035a4000e10443e1110303021541501c080454407907050140043c85d0240c0c3d041580b8509150410b41c06c428507081108507050191a080c5442c52404d580c40c01000c41c0d100b4241c800400c1062003441007214030000c010040c060a465450081300b01d04c0600840c1c10ba40352034019030400c030f441d02001d807403e030980c68541e0308030f00d0a2441103541d218039078000740341d20340c1c55000407500e0540640714140c01040440010300b104030b01c0342c0314801d031444d000d82401c03810301158404c0b5000c20402e0002c14013404507580a90b9071a1000c0c102442c0303241650708010300062030048078118208090b0381040018a0140711400440010007142008000c0e4052654160055446005544481d031108105d05901204c28034031545512010580c3c41409000d003901003102400c00380212805112868400800e00e6030200303c82c1c80c8280802c1d140c00c0c54028001c000c50403688540c030a00454001d82040c94031040040c01401d14688000b0400b003198070407054800c10825a03000b03141c85050403540640742040c12 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 256260107 1250 256258857 256258861
    0x80a1b02040c0e010f08010e0c1b0a050a0309060f051e070b0406021e0702101416030503040b0c03070807030e1203010f140a18050a0e0a0b04121103070b1e 68
    0x1c09020300f940c0f600034600260900072000c02403402a20000d050350f282040042c1160303107806c3d980b089940645d0040e600c004c200c0c88105a0844100840d1804e90700c10000b405e00c0701c6607490041c11814441d0040720511180e080800901390303120094607003004a0041c0380e18920310300001f420191180e140701615a1480380c04220511185400400c80c5444081c41492404101c1031071440314001da00009501000c030750b800c080803500ca0b11800d400c6103400e4011510344815103c00a90925550134110003243c0c01008000a110030085800d80c40861074130701a2070341c0340405008202e204001c1620082c1551040090340650341009040e400e6102803207641c0c1d0701d584580400326035003c40d108580604043c3c505221080c101080a1411181c1c080c8120010300001c0c0350181c041e29000f400034444981e12080b02d4250389007041505002c9010325a004603a007040d0030400e14101046510a06102d10304070b900605a01c000122500160090030462007070311055180404c0d07a41000d000c02e020050341e81 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 256261357 1250 256260107 256260131
    0x414030c0c0a2106020307090f03030e010318051c02160f0f05010504260a0209010306090b06010e0a1e0801020c0f010e070e04060b01140c0c031504080a1b0204 70
    0x50115104002201e014102640d18640e1401190910102240c80308100383c00c000082c5664003c0c40e04022982004102075403120f00b4040d4105142e403055000408020111900d9609480f0382038003008031000030307840d20406d134031100c4d80d5104c0c0308440c2c9080d078031040c0c9040e00684244610620002c07034100310000c0981d1091160020406401010000b504c0c0c1080003640d50f000300210360489002d026030306009208032507903095603049011000000c0c004e001180c001a40e40c0103160307029512a5400180b824840c0c2402007140d10300524550510040070b0075480550744003901c05040f41c01c10580505000b000200202c82011240d0202c1310a40c001f0a41000089012422220510320200200644409601d5041e80c595007403081400044034035000c00c01091a60b004035240000604210b088802d44850000f450351096a064155402c03200c4d40401d6464140001d4069500001224085090988518000c1d10a065001d41031090381c60009034200e184103c001c654a400800400030305000c04 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 256262607 1250 256261357 256261363
    0xc0603061e03050c0613031a0708090f030f0f130b0913020a050d0b01020f0a0b01050f0f0f04050702070f09050a14071e02030d0207050106060906110d080414030c 71
    0x10107501c540c40c0c0c10400e91248086801681c004480c0c00034010901c10200b4000e101641c5d0045410950030480c00c1c4010001c03540201098420002d04071202d040c9150000009180030006888072005401c42c05180c9800100001524054902c2c1400703255101c00d02d00044949110b0b901d990f240e0402c8402d00041d0881e644e5010f0003410b4400d40c1d1035010000c600442800324861581184042001445188042680740e44100c11141d018011640d040e0f03040d010f40c900c0c100a10004440c060701e404010b01c8135007021070890042010640b101c54070410210b0005d0180c800390444180075559903030000d80c00c035108100c000c009210f02015070303116a13280d1041c600500811101c014505092032000582c03081d6591045104030440d039100c2d40414490107410b40d40c40044103a880031032000303000100b141985c510003024064414000003e80600d4100c0140c48100c182d03000b081840607031900d040f43c0e0440410040302c03050003442c0c544000e5899107003100d241612800c86841c04c2c0710200701503480d84000 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 256263857 1250 256262607 256262609
    0xf0b090c03070f0c050d0516210e040b1e030c06030103050607081312030504140714130903120c12050702030a030510050d08030c0c030a050d060e130209040501090c060306 75
    0x1e960f440d0a1a650000558000b152548010080e905c5a0b8401400324801c001801201610040d4110b082900d07440b902c0e90440702c040a08411040700b5007028621703400c50303d40c2d03034400c006807000d0011820340c0000404010f40c050a03651944070030002c0c0d2002e40d4060051004012000b400540c40356104d0904aa88003000c642e010081540180403400e00c10101e051560542e030720042c0300e000d904107550100c0c041c100141007120380c0b8035050301c400c980200078021340c0c01806940b45010314280180041002e203110b5400035040151030040c4000100e54030000c01140b0200404000c01d14120104080350102c6103440a81425031800d0700b8031038a658080010a010340703c0380d07070521840c0c84800ca03030f02c20000c1920440340d101c0842080303035000402400265034040100782402e0308113810205a1411980803d0a080004000094204030b40440e4440d481c0500b40405540603180340180c010711041f02e41442c06071080c09180001010407070b09420070030009500a10040741169038010245c068005 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 256265107 1250 256263857 256263871
    0x608270a0b012904030209010323010c211406060a0903080f180414070323070801030507080606030a141e01021815030a111b030a030f0c0806040f0b090c03 68
    0x444212801d0f00d100e0b42c010388040c0c81d0010040c5000b6403956403940f11040300b41c001481c80c0710034081c0724200d0000a100300c500b10a02903e07010340e680c41c4207442c1c031940111514104140380c94501d0042039403100c40b16036070740003006417480c503500d280100c6c00703550b200e40030380c401010301d45d000030954010312410010700302d022180104644010700c00410001618a1100139030840014440000c03191803281d00310000444002c200c1d905142c16000004500b04000c40310400460440001001044000c0080c04001d00f507507000f03001d090078080b0000703803602c410480241c103c010601480002210910082c4e1192000031131400900d40a5500c4a000c3d403c0310b24169480248141500035034100740030920626800d5000c09840d41e50307181d90f03950007004035280c0f45a0080c020b1000c1100b845e01d16a8080d2030b001d0041c0111340705ea071600700c0141906c850340801d48501e400c1882540c0c006401106141e0081e4048802091b5003042d0344075040140b00c00b1060b980d00482d40c0040c85112600a4021402941 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 256266357 1250 256265107 256265159
    0x12050709050f04230c0405040204030807020901080f03070206131221050901080105061e030a0905010c0509100e01120c05040f06110d0f020c0d03030e070608270a0b01 73
    0x44001d04000882d141d4074a03924200b90095914103451803030310640c0768171001d4244594101031b100c0004c80d04a801c140c0048401c040002401d03030070340c41d04034195401401040000d1004500c0700711207036201c0c0181c040007030140070003184841c140a0300c1003401c0061302c200301601c83c90641d1070401000101810129491003296500040c082c14031950850314100c0044c1c60b004116480c0505009003036002c04142c4c0c1e20350007251700c214000100c04000794050040032101244008107820b00500315a00d04d40c80509100c8100440e0070543c5888900428940c0e050916900006503900140c0e0024582c2c96481045c5140c030725121086a005009041a5500c030b0070b44070700e44d540341c46081e2a08901100c0c1e8105c268070580768510100c0c85901c218081320720303510560703055500184c0031900030320300000c044010a032124140c40c1c00c650204000c10003803140b0b1818110704d081c00f41041c0002e4200e0f190882c080c0c601c40007203454903201000466030300303540403c003c0410342c2d442040d11180f115022010f01500 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 256267607 1250 256266357 256266379
    0x12050709050c130b3115050304200f060d0e12180406260102160b01030209090a0312110c120301080d02070308090906040f0c020606040c0912020d02011205070905 71
    0x42407016a40310591901c0503000c8248004440d0b04a03500c40f0682d2880d03900171034008198410f08000741c3c85030400d145c8a613a26420586018038001150440700e816801c44412407021710b036150080ca500c1818143c440075030301d1189200d99406020800d42c913038124480c81004c590240300c102c2c0140301041503100c200c0030710483d02d0104015581240300700f807800280c0d02c0c0d040c8103640d4a00c81801515400000052800c0340c558900802c88144030720030f07100c10711141c00400544c1445a4041c1d072121030400908410711056078050700018544810b040003a43d50303200301000c1c1c566102255101b068120856170b001d10381030b8255040780e009000b6070b0074070b014040c1d041070150700000d2038100381c1e5170203000c2600f40b495000c184402c040c401481395038455140c48100c150700610b40b064020054180d8041c00706031401030148400c4e1101c1400c980100204000e0411480100c00c3c50038010540c100e4800c9018502400100c4100801d241c141510b1490002884082070704883c040c0e08840c015620300c1181 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 256268857 1250 256267607 256267619
    0x20309030d030501030b0f090312010b09090a0c08010b0a0c020904080a020f0d0504140a150806010f2303041a1321020312060a08010e06060f10020712050709050c13 72
    0x2e0f800030320004040340c4007500811400e59000440c140d20000d800103e03418040d07054903007646110283c2c03100e5014440011042c005040000c40650311420000080c0a042e51800000b072041505220341c00c4202c10210b07022000c01e108074200340000d0740007445000c0c4e505160030f2003100e40d400b12065802610910841c40d0400b6004144e00703020404a80b181400c0c0b926021500840c1e2200707070940380e8001c203980c4011452018141a1943c00303c243d64a08001d0702d0300400141c400c1c04140d08103410300000ca2140c241d4804481904504a005422a151039450318034015054018420321181d420140724100480310184003c13102695004800c2015454400c08018220000d84854500107800c10021a15448503110485030403540240440041c1d940d21900e42d42111581c03032040000d6006142403044d246066000f850014404440f00a0303414180c0c00041d64403003a5103d03450512400100d4a03050100501c0741400401e24008180800d20740715100d402c1651103100d028030840c01480000c514 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 256270107 1250 256268857 256268861
    0x2160b0f01060839040305010504060b0303040f0b0705031605030a0311030f0703051f080d140c06011206090602030408030906100e1801020c010608070612150308090d060903020309030d03 82
    0x140310b0200e52151603640d184010004142901d041e030b52040c2034040321340708002220004000443c024400040c140c1041c2c0f410106950112804070b210760300900c802c0c050690800c0748181207450f000c0e44d4039600d00b1640b604500b52300a0364034140300001050f42a0041c40345c0030008050b103442c150717020000c40744e0000b1240712600003612400001c01c412000190200e01030b40c0840d8000c144c070940b29140d0107840c0d1001d50b0010464020f030203142c00103000caa400e0384c0c01080c2c1c480c8101070041002e0624184038016030351004141b00301d4504850130341d1b000c420b1200c1c5500101d002d98010500395500d2406003400d8045500036680b001a80c8280c0b0002000c0c0e2122802c402c05940b10080402e01680f2200b00f105007201d26080300001c155030803c00750f041414244039050040c9401e038040c00c00c962409001801000d452220100d420741489002c3c081c0d0b540d6140c010307041e00d070700c280701d5901c0d40c140301d01050421905140c0141420b01d405503c40c00c0c90b030000081c08008104508841481c4031507602101 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 256271357 1250 256270107 256270111
    0x30c05011821020d050f101a0303030a050c0705010c080f15150d0b0d0f0b0903120a09030c140601050901080d02030304060513020d0b0405070905010b160602160b0f010608 75
    0x1405080c01c8040c00a040500d68042c0c0c82c01c0c0024401c01079401aa00c40381d05040b84110500ca650344840b4044070466001c6c021815840103803c00d0034204034154001c02d0316840002c000600aa58036030000f811192070b40142c071081a0400f008114048811001915102003643d40c82000c0340070400054080c0d511400c0c81e4034211000c1d05030b07070000c120215000000d0f04521041340d825501c4140d900c4403a00e908541102071030141d407058101ca25142010008410003921000b0990401c100300781d481110303200701075080170949900043c4800e90341001c030782070412400002c0110060882c051641f040000e9414181d8000302d52150841e660345164603554040314018401603042400001c0c040b8046074415a40600b1414100c880c0d52295030021350002c01d00c2d682202e0115109042c4802d11008019203409015551420045541000f62100190050030b17001d45000c6203c0000d4001c000d03840d01900d001d500e00200da40c05903402450450345002044441c60f503a002030b0800050114400c0801034 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 256272607 1250 256271357 256271369
    0x3120c02100c02071206020304021e1c0c0b1206040606031820060301030503070b0c09182a0403140a0c0b0f070c030b09010b0301050411040e0c04020301030c050118 72
    0x5001000045080081d214204440b01503002d848000a00320362100111103c03144500c0300165686030602c10420b41000f1580104403042c5000b860701c2031511600c0c0420b96100d2881d0741d10b580d0460305c0c80e00b48030494075500420704144002c18844100400d4490483c091181151305202c25622240200c040703582400d0f001170940444103501c2c3c0030079102006224180700162036005812014400728a140d8800c5e0f0003242c0356032000840e00c0c00d002c07810b0f00343d41c0c2010400214a1402d8520b0001501000b90003610104543d203c80101e6030754a2008104100b8248001c0009880c60b07440301604050780143c4825922940c8881f90f060500e00082440e0b041d442e40200550411800c000b92600c07560009409035245c00002c0201c80c1c0880c464100b0030f0000c5100c0c41c0312080600c1c03e5040f0780d0130341f1800200c1074000c0e030400041c080024081c98041c014040161000114003015084c0d241ca0b05200082c42500300d0320000c000f01c24400c2c8a01040d041d6202078039000c0118000084821440909100309 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 256273857 1250 256272607 256272613
    0x307030554240903010f18120c020a031e0b040507050307050301050c040b09010908010e0d030f090b04030e030304120f021014180d080a08010f14211603080703120c02 73
    0x41c82d1141101038007129101600002d412007a038166403007100c4005030080551500c140150041281050030078480b4403440c9402010103400c0d034040307071048100e80002420f4080569180d9207122448584014680d041024510070742490f05210b9142c0303196008050181c001c500e00840c0e0b0f403c05014281c0039540d1440940d00e07061510400c0010350f00300c41c0ca69810007034151400180401c00b4007441503100c0300d0001030034900c40401806421141d140d14242c6d1994140006100070441307200340e05a002d50107044c80900d1100c2000001d0540c0300301d030002e0b80300541c4088006c044c854080c541c10409842a2a1018045008c071000c0d1a00c440703000550940c2001041111809202e180b0511003e510160030012041d2032030766080e40d59000710f502d150015030604010027402030629400c400505c0303c900c8005d01c000d0303100046525101c1070310015905907041c044412001e04c0801c07480a00c1d0302d030346090310411a213170300c0d04440d207511001042e4001815030600310a100c0340ca1049545d41545034000b = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 256275107 1250 256273857 256273909
    0x40221010b270f0303040902091e01050306010315080d03050405010c0207150e0402120f0703060f1211130501030311010e160608090c0907090305010e0307030554 71
    0xd9090301c21100ea4000f07410001840841c80562400c02c040d0021701a04100540c0326407403c0203001000100300480f2651500d43c052a02e45039030000e00722074108100b072801040e1071849041164060b54260b11403001d80c800d5040c040030071641035000c203005522410080c00011003030740040b640c0e80c03400d001c0d1041920214904204450040c807007107000c18000f42c400b6050940c8141e012000302002c0310322403401c50004040003603080e854443c0d2405040c001c0200c41c911400c107a800c00752202d0070580200100c8981481c28025075030003a080850131903112050100c0d41e1a031070018055004403110040c150b003403030342d41030f810b28001c50b07191541201050800079040c90088115203120f0302070000c90f4240a4034040d039145d9103a880880d40f081200d511000305444c5107240c031508548100390034400302d40040c0800000680d0203811600c80706580c0135500c480d11590803d0948182c103424030030b5000a140891003902410001804511104802004084900c05811b2261010342c000001c503e64a413880 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 256276357 1250 256275107 256275157
    0x6050102061003020609122b020f010c020c041508010f060f0f080d0806061e041a042d090c0c06050c07030c1e0512030405070605040f05010c0f02040221010b 69
    0x450310b0001c0341f00c104603140501044c2d1005503040200c604075800c031179444003000c040303501004505030060f2040002c2051020402c4001d460303102140707445101307a0721509a9a00401d1040c4a4005402800002c001606c40c940c20b100c01454284a02d03d5480380e400c10001d1190b21940b180d0089413030040c0505450303031520324201d4440e480100010f500003170622807902c5210f83c0d10700f00d91071119902810341e5642c0c1000310030560a102c02c03410b800c0c0700300100401c1c0000c02090b498000162401c4c0d400c0c88460268024900c66083c0035044600e8043c83c1c402c4095019501c8130900b204180a540c0422058a0300c901c885128419217101501288892020000080d0f0060085080075000003203000b250700c079a039420b030411941254510100c60b000c4140818401d0030702090000744440e0400c1841c0c549016003442c0c0300f4003c2d220b03444c1803068180d0f01505000c0f000a5601d05183e0007003085644078200d2a04110781500003200102c1034003640d0001c03401131a2a070480ba440340c0c4030f20501c64542e014203 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 256277607 1250 256276357 256276369
    0x20a0308040807021203030f06120106080a080304061b05071e11130e01020406020f070f05090c0a020106181a01081519120f0b0f070c030809070b040906050102061003020609 76
    0x3260491704107500030b1601030034103418005503014251042e80880d26043c400204442402001070910036645444001c100c60300c40080c0c01c0382095401350b14240c607a070311030500c2001003061b039401a03041074080b145004066807010080c02001c0c4107841c03404401002403031034018020f020740010401c85002596225a1520780c1b0f406404801040d00420001c0300903a5003420390300513521020144c1e00910240300c044d1006e001400207042c4e00c440c01801b052416000504e90303c409401c04451010020701852900d200b03400c0741c00500b44403010362700c40c01809005400200745040980d1120044c075041d43c0d260b580706084d854061550b000740d00121224140404c800c4440ca0045094040c074031942c0060b64801842d06002518001c03002c3c9a081443c07070802c44501c0c0300040124030310b01c454078100815260400820400345030140740851880e43e5240c03003d80f421f003143e0000701d4005408a8001845401c94200b10281c4500303900759116500ca500b640c05002d130807030100035407100d42404140c0d00c42c00d0903 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 256278857 1250 256277607 256277617
    0x1205010b030a20040b04050f0423040305070204060e01060815010203090f04060f0611100624020c03120d11040302030d050c1608010c1d031e160f090c020a03080408 72
    0x1204008903144003c0c0d42c20300c40c2e0340f00c2c2e4064401942d01050801282c40e1900c140d042808003503070144a4a00d0a1043c2c01c00d1f0100201c0003040342c0840d8003c1030a052140c0305803843d03107601820801c6007585031a032403401c10700248500c40005607a0000a1909035140701d280c41c5031f1806030000c60425100c4401c0000038015851000e40103681d17040001421340c10341106000914503512a03011015041c078940e400d080100c8240400380c0d08001040180c03c2d00d507007030b40ea0b0520b04444004da40d0f020035034040381401c428040b15036151146024080201490701c000308454112600d04210003e03550f16100000d009074132010b540341d0807a1030044c007041d00410060680034890700070b44820046191107088405001e0f0044411699a01d130f040030203a8100d00800060444800000c10b40251900004d69416480008900c80c1020f20701003448a40708001d40b0246025001d180f00b2095162080c0e8140c3d400140701d41d1543c9420080d40845560010900e040d010740c05694003a4195196101c000241d480 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 256280107 1250 256278857 256278881
    0x30a030815060f030a09060c0203042921100801060305070b031005030d020f06011d190204050301020f0309060c070308240604030302030706050c36030a030f1205010b030a 75
    0x2080041d07901945030f510003580701e500403840024800c84181001c6048840c0444202c0c2990310400090020807040d070410702030f036490003120008440d0149000030340c50003850090b520300c1c125820f5516501101d012181c2c803400c5007201e0b45d4002c2c3e555140310b80c00d03174615210207400c6401544050011307440000007560b0010981c100e00c2080c03640d803004a841c022250030641c0c01a08429609161070300148400d13030040190700942c0301c0c69055a0007955a04001402c1e81300c005845100710a00c940894041d01d0003408018021516001c2c6041d6405095108072413114550183c440018480c01c41d290a46440a8042d52040d02583d103a06a04840382075000d160200402c151015600f250b07105801040038610a6011b07680310480d61134603405580014100022100040c0308002d00b881080c003500c5070380e808401401c52a0b00040b07000900700010102c0c82d0350140100f0101509064000b401e00031001101d550b9000354400500c8103c0403180d0a02424218001c04c001098001c0400d42014480d221 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 256281357 1250 256280107 256280119
    0x1208070f0203160f06030c0509010509030a050115141c0b102403051510030c03140109090b01080a03050a080c13060e0a0801060f060302070309090c02070302040b030a030815 76
    0x2450700043d180225000641220f1589038106205a841d1100624010229818148480c1c0807005001d4028040c1e44ca074a810040041742054032030354204286078103a90403100070040103110000406682803d409a0200c542440f2200511401c1036502c14051444001ca030910520550352218040003019249420a4800210100d08124000740300d6210300d11480c4031010810036000042d059810003040710549100e00380c2410b00c2c684407452120001c0016103400203601004441c00c1d0010030500c02c8401c141307800b11001040c071800c15807190320b680e40280c5c0c0000c100c0c1e0303880007125aa41c9804d280140050001c0c4480d01c0068021551645c000070607048090604041801448000842d40d01680c0028a000d0b01a48103040940100c009003498400a100305400c100b205803500314280f10b400105603000980380c2c24336120740008030180c003803000c090080503840d00000b5030780c010701c0c00140d202c2c80c60008a03801902d000034030340e41c11076816103590841d6036402080080d801262452035070404 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 256282607 1250 256281357 256281383
    0x40203030d1e11070c1d060111030409110705010513112b0501060306050108030708071202010608030a030c030c2625110601170318041508100f06120807 67
    0x42d00c140981000d00e22070b075001a03291101d034100390074064404d502c021000c0b0058140120803031040c01c01e9660003502070034400700702042c4610726441c3d840303250b00811403649404001c000d81c00800c00103102c0540208024071160f118010b103031f00f0944003480d000f0410503062040c0039540c148090304410340c050b83e0641d0500b019200766036010403c400341c41101d40780d44da50006d1007040711038840d243c0076002010045090545c19603418219106410001d450f007400b0440001109100f5082600a8455041a29203410140c0c0015000d0011007601d040440c0c106030403444501e20617001001184048207070707003c0312107001180c9590301502800545c02e588440340c0f18800000800c0504800c1442a5071305120800308802550a069040c0c205410100003d1b00c0c0c0e112011000003030302c1c044104185606201c071035100008004200d00c541c102451054010f0001c1c03030450101c0c1100072680401e405001c1d0000c042d2410046401a0140060314030820080c2d40c04250502c019048445c42240c07010044 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 256283857 1250 256282607 256282661
    0x50307021c18030f05060a111803160b03070311090a0e0901090602180307090c0203070b0c1204141c1d04020708070503030612030405030604020108040f0c08100b0108040203030d 78
    0xb800250419200c10303410b41007920401408100c00340d809803005030100078851020040050500c140f200c00009640000120b40c86568240b07d080a4181c031004440c000d155158025411900f00311142d0010919184010b6007081c004411201000300003030044000c5410001e45c01e44030813015280d80d0240d90380d0f051100000b2224801458102d581403410030700742500d5000c042ca0b0407515000b1010807800e0004051640c3d40000c10345004d035500680c0f030112641c2c2c00c44040668004d6001250a1810b80c005010a02030410a505954602001030782c5000b0f40004d0b003100c09000360b2502e40c00040034180080c80c01c020207201d10391450b00c0240058600f0840f81c5804403150003142e4190b91a820000600c8418584241c4618150100e074014500309481d040010340c8900700200080c0c140803202d00011f0030004000a403c490b154019130301d034040390310b0b410b00355078a02030441e040082601d0003820010642c05075062034884c80d0b00400961800ca410b94a80c005409044002c0214000e4082e2301020 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 256285107 1250 256283857 256283897
    0x1090f0e033001180504081e09040e0313120f05030a03050f0c090109140f0402070c050306070c080a030b01120218030609151302060906070f0b061503150f0307060206010503010c050307021c 83
    0x10158000142c5071614070180c2000b080f01d881c5041c00310550700c200444071f5011044800134007140e20400090040001d9401c03f81e2409904010061890100081d0700110b5030301680032034090860550300051a0382e82405000e5a0b200d5014064040b41840314100688011800d040c5c0440c0d03005014800307031310141c401150503a04103031400c5445001034441846941001c005a65000c012403420600c410301c0350b20342001a1040d13088600c105600c030b00110710607900a140941d402440404119610451309ca0740000341480515494400d01411003c01c02e0700030005102c6002080780901f4000c241c0307a0411940e51400780000898002d0000d0252511307560340c440152110071300481c0d00190200d940c0c5801e02c141c04004100c548180f007042e83d191a140c00d010281c5c0e50080c040c3d80745550401801000031071072218141129418030034200d0200b0701e140d005c24a0740c1290400d80007400034043c51101941d142c0421184440143d00c281c294a03404207035102c00400500f21414036282d000048000708013 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 256286357 1250 256285107 256285147
    0xb04020102122704020304170904090812100b09030d08090705191a04270e010501080109061a0904022707030207121701090f0e03300118050408 63
    0x100010401e0022840307043c040d0507403940307840100c81c21131641c0703032960769409428200203110403035010104100115444550141c9001a0080c140300d032100a498840c103622041183d080707807801411107001844105081c280e0340081802000780c4201145004210f0b80000000c06004852040040004803500d405821a480402508100c1c00c823030b007050181c1d011001d85a6400700c0043d000c002c10412482504a10540008800c00044090803078501c0d100203004401442e000c25468040006005a8154081c01c3c40703522031001400102103110010304142c00c0e0040351900710010f403000a0041c0b078406140f004a0300c14074080050103040c228607402c4035908039140c0b00825400188942401004040d030800e00b1294900303407404100d00003544a410030103100d24407201381c984616000140300e68022030000e402d10000c998130349104000c0c03000003110030b00b080c4205a41104254441c25012010981070343c1c050084109006111840740e00182401441070703800c50707020f211b04002141c810030481 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 256287607 1250 256286357 256286377
    0x14030705011b0c3f0305030c0901021e0c0f040b0d06090503070b04060603031b0317090102250c050a0608010b0304111909050114030703120c0b0a05010f0e01030803040b0402010212 79
    0x188015081003200022001c40ca40c031140348000c140840b00c0006d07403201c21260b200c60100400d51311004403100503403402104d903822202c4000c1c0210180d240d43e00004450300211400c4842d00c0f01d140c10b00044c031044840140b0120380101a130852040843d509802c140c1c01e82d07118400701c80c503141007920341c010a00000c0e40c040354850784640c410018568451007000c98041c0382d00c8141d5011f1101e03540500000e90013041801040c0d1000002040e1000031b50540b0103010321500c0f0714000c40040345980d05a440e0900c4101c445204007140801c85040c41e42c480e0082c0d0341396440e8540c0e16403c120a0030826000200201c0e0055817210198080d610303048081e2146600f00da41c000c065605140e225015114140c100d12203030400d000024209076800180c07038081700d4009010780e008454007902254111000704000c1d000c5604c00c0d080c0880f984140d80028102c1c2c0c02d105c004e541d40c903107071002c14000410a106c003804242046c004140071500400003603811610500494107a581c01030345022050304045114 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 256288857 1250 256287607 256287659
    0x14040507020712110108070e030a02090405071802120c0f04090207020f0d060b01020f0c0a0314070e071e02031309050a0605030d03090b10030f120e06040f14030705011b0c 75
    0x1082d070b5540c20464180e00131f1181c1c100107404112020100c0d1b076425110601920842c41e100119090000502c03414001c0c18007440094103c441d5004001c010303610500000903103619010006200c074076041f007603a405030f0302650017610345403030210890043d4105182c00d99000c40080650116540c8498a0000c0c5620524020524003a0500007900308811107803d070f9510740005242545943d50203101030190b03907102507020344000e0f8004402e4500ba200d600300c0c0c8551040a4140544503410804400184140709510030501050719070880c0c59000300340c0d11640400036190284040b01c0d4940203a07600800390100010f040fa40c80703000a00d0510000b102d02d021076600ca11082c140300c40d509180c1d50004070700909480d101e01c1d41c1d480640e000386442e4046e160b03807a51340354000413a10640e07101030320300301c000c200d941c4440d100c2c1100758440b0101d2145126034070b0050410102c42c00c000c149a41100d0050f12513840510903451601e1404054010444150540680c00710310380024110451000ca45a605 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 256290107 1250 256288857 256288883
    0x408010c03050f0a1b1d0406120b090a03020c0f0105091917210703050c06010f060306291c15030c050a14041805060f0f010f14040507020712 62
    0x34500e400440a0007400b80c440c208144032174003810034041c1c461015200e00c1c000f0b000400140b42c9840b004210100c0300d900508080700007d401d010022021a0607014450800c1540c542c00922030350790b1000a00100035030040200e940080c5000380c005a95050103040152501140900190030341944000c0d01300c400d01200014400348581c4200d45405030001c07c018004981e168181100741001c107110312016007800120981014801c00c246d0b42d9941c0c0c54000c0350f0507961182c0d21103c49030514060b080000b8941800051070803901e6001c0c40100c1d00101080c001d0503050020b020041d03004152017140088010b160a008490a1251003800078020a0725080581903181c100c11104007035205521445074040c0a2103440d5500303c0d030403840c03801102d0009441500000d090700e90075503140064864000c010410034100b80b041c5480744246041140f22149a882d2200c0c2542e00403140900c912261503031060742c42c241460703400300307403c071060340100c5501c9940c9614910721000b00c040d0403144455101a = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 256291357 1250 256290107 256290121
    0x60207061d0706053a0c0e01030203010620030c07061e0906210b10020d030f06080a030315080601080a050d090311040f240e060a0303020304030b0c0408010c0305 71
    0x440181e22444030000761031458900000140355000d50042c4c46030960100904d038065811003003c00340d084000200030301c1820581180d4400074404030b40a100824100c030751980196100340708030b0341614881d480c0c030321024020700d1003055045c001150704034046c842008500f0560790704210f5400200120741d5400c141451459445001d02c2c00448400c00780a0f00b03010500842d40c2004090134001100b1010340c00c150180c034014405001450b19650300810207140d20a0226408140245040496201804050310300070080c01104c0d181c1c03284e040544c02c00c4400c0d600082c420b070011108042840b0501600e180c40c1c80310b1604064081e4044080b80d48110382c0101004801e0040094101e92070608412a51540d19004c920030b41120b40984195622160380d141e07070807158042040e040e07010440701030802c1c8200189800d0150fa000c0e903401011980c8c0019520300e0010b007a1000d503030741980614142841d50351a01079060014215001c103241c02e12001c16154024403400c0d0700d070015945e01180a007040a = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 256292607 1250 256291357 256291391
    0x91113091a3303040521070f03080106030b03060606090112060e070e030d05030709060c0206070b15031002091f0219080d060519050f041508030c07120c06081306020706 74
    0x108620440d000500c100400f180000c110300711000c11200804000011004452002c0c7c421003100800304c41c499120303241455440368202d816900310b602c3c02c0011038500404c159840300b041702c140d9403046007004882911352042281c01081210008041070480d204c000400c4848011500000000c40e40c0c0440c4003140b8081100c400c0303020840c14041c1c07031030400b0079000303210500c01e00402e02804440801d03041192603c4085401c0290020350081d99030910980d11440304250419040c4244600309008082e03402c42e1088461409008140304000aa5120490030090701c150440d41940160003406a40b112460800c034030542c86084010740e504012940ca400300c40064120070b01428068085040d11855620b1040a4a8044400c40300c4040c4410000380500303010b0144403a41d1070b0f191000a0000ea000014100e00c00c03151041d11449034981d100610b105042400150560b200c102c0100480d40c02a0219500059040c00701088545140c48140a9a00c650720886039a641d504294140400b05 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 256293857 1250 256292607 256292689
    0x608010e150c130b03180313080115080a1e020603130213050601021f0e100207060b0f091f17030304030f020c130b04060915091113091a 60
    0x103a060b03142000c0c842c40d0100d0030044031340984207400d0b070000041001e024000340a8040794090104076030342c8003080302800d00704005a00c2800b00c03a60034940d00100a00e025241c3c1c0c0217844803400209002070603a1514030170800030080b4203680010800884c00581c940c18020761082040518000c2410802e00c184020540040c0701d000e4442d1501060003c40d03030b800f08003030f01c031440b11014140c184113800741044024103e024080003540b25614000e0005120f0f90058800180104020017007480020140704034039140c1c8480540c42891500001d0310900b005070b0040442d11103441c4000c840c0d440e0585412520340c020f664141943c008404c00042582c8030240c250800b1443c805804000320071004920400c8100c80f0407070703005031035040610042e204c5500c5140240003029040c400740460414034000c0500c0e9000320f480141c1080b066000e6039007a80200c640001303102c0c0c404045240750032034100c000c000c8501d65001b00c5c03c202c0c401c50b82507500e0072420881d1242c1c105200d00f4500d074490b51070b00c3d00c00c03034 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 256294964 1107 256293857 256293871
    0xe030601120303060e15010c06090503040e0f060414070f0e0306100e0f040f030302030c09040609020a12090b040b0601120c0504150c20040608010e15 66
    0x7405006091034041e441c100141c030307154036242850b010111090040150850340400c0c80754441c1008009071400751000156102e03456940f1030841c9d0041c1d00c01e4002034128020700c10010480c01006801c194121410422001e03001003a20200ea0001c04607000e1040345100d105429010300e440040745070b07004003542c0951030b18031450030110100d40142105604610005188000500c10860055400605940560702680d8045000e9440204001c15004051200c0c0c40141c81e0740c0200800380000b001b02584030280b107100100180708804000780810300700320070b541c003082c59480740c580c0140d00884110007941d03548006954080e115101104010b1400300041c0070580c0c05800381082c0c82c006010714400985504007102e110742903c4003e0404401e10301d2860039910784100314070304024041d0000c07420170750340d40d12542124821203c1e1079581d0480c1c1c3c0c0324400ca60451090540c8541c2c = true := by decide +kernel

theorem cover : BRFrame.Cov 256115107 256294964 := by
  have h0 := BRFrame.cov_init 256115107
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256115107 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256115107 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256115107 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256115107 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256115107 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256115107 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256115107 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256115107 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256115107 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256115107 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256115107 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256115107 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256115107 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256115107 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256115107 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256115107 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256115107 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256115107 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256115107 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256115107 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256115107 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256115107 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256115107 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256115107 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256115107 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256115107 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256115107 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256115107 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256115107 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256115107 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256115107 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256115107 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256115107 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256115107 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256115107 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256115107 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256115107 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256115107 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256115107 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256115107 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256115107 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256115107 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256115107 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256115107 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256115107 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256115107 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256115107 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256115107 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256115107 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256115107 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256115107 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256115107 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256115107 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256115107 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256115107 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256115107 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256115107 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256115107 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256115107 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256115107 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256115107 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256115107 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256115107 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256115107 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256115107 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256115107 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256115107 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256115107 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256115107 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256115107 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256115107 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256115107 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256115107 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256115107 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256115107 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256115107 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256115107 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256115107 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256115107 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256115107 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256115107 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256115107 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256115107 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256115107 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256115107 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256115107 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256115107 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256115107 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256115107 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256115107 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256115107 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256115107 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256115107 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256115107 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256115107 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256115107 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256115107 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256115107 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256115107 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256115107 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256115107 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256115107 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256115107 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256115107 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256115107 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256115107 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256115107 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256115107 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256115107 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256115107 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256115107 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256115107 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256115107 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256115107 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256115107 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256115107 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256115107 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256115107 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256115107 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256115107 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256115107 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256115107 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256115107 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256115107 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256115107 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256115107 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256115107 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256115107 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256115107 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256115107 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256115107 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256115107 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256115107 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256115107 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256115107 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256115107 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256115107 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256115107 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256115107 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256115107 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256115107 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256115107 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256115107 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 256115107 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 256115107 ≤ n) (h2 : n < 256294964) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
