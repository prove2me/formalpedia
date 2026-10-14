-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2236
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:04:49.037925+00:00
-- url     : https://prove2.me/submissions/b4084bee-f88c-4ae8-a4ed-93f2be679a67

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 401978417 ≤ n < 402158273 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 401979667 1250 401978417 401978431
    0x40e161202010804020603040510020f0909090a12140d0903030c0210050c0901030b1f03200309300301060203030103020901081605040c090314062a040513020702040c0e0405 76
    0x14946903240103030b90001080754040c1c1d06991180c1c8a407907502d001031400201c0c01c903240260307001040c01c040c0600c2c03840103414141c9084070304110301e8954417661515001c03007400c041c16003961001803801d0700c3d001d13281c464031600011120900d031a128549034800c032682004114002511186010042541000904201361691200700101d0034030505285061013192082818036071510030760411030f510b50582c8600c80c0d01c030101c900802c4080401c020300500010300010f91040046201c58024050141a2486511400000d081171010540e0303892030403107000085960b00d8210b2041f80b40501100e005180240002d400171078603941980b04002c0c4c43c45050300031115541c4440d0503981c0c02121010b6420448100751000a040206000d046030500140e401c00703403411501d130780b030482c07801030002e5004d20407040c01130410700020505c07001e010003941b0b02c2e07043c0100901c240000d00440c60305140401100340b40240040c41d18500e9030120702982c50106d0640f010400d8501c00c1c042c1c3d41071034003480c0d6010b00b03 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 401980917 1250 401979667 401979689
    0x150b091311010905041d060a0b010e040510050d0308310f0201031107030207031109060d11031f0e1203090a0b0a060819060b0d031e020705040e16 64
    0x2a00180d40315403000d00c580068501d14289080e0304059005424032405010302030f00030321852280100d0000c2c1c42c2c940c0700f0395906522940c0300290161800740b0070348100030340580d141c000300043c60040101801001c3d0040506028980c0000760b241da903040c0f000e14042c4603460345440d80c13415003c4191082c03000c4480c51401d1a101601010200c81490311001d52540203540d0307a240080c1e800101c0040041d6004441c06c404001080d20038190000b4114003140e105205407444000180240305500800313403500340c1c001c40b404c02040001200190821181d10b070203000c64074465600c4e03072810107900072040841c000950b500c950084046050080707107440c940000600e4914101000e000740e550800e03041c0a082c0780c540c0300200d00360505a401240040c05100c0880304c0743c0700450100142c81040d8401101c4152070000c0d0200a8188540440a0307a50542c455420240781e5a10384510021020ba441d0114010705c0b001084d1030703807903100c1d55003112801001494038400e1aa401083d80bc8190440b4510070 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 401982167 1250 401980917 401980921
    0x190c0f0509010b2b0204080606040b0619020c0402030f1614040b0c0703020a140117010b040b18030708062a030a090804120f06051614090f060403150b09 67
    0x7441e50030001c0c0c1125441040a9680d59a044c903400c00c0e14403025065103071030111403400007030042c40d4010b40266039841041e1100ca8031303001d08000480d0702042146811041c06d0000c0c6000b140f4903c0000c031500030500641c0c2494a55800103412070703000b2143c0052940305103043c080c1e40e13901b204a4034020703546803e01d4003007010401c1c040419030244e0304c0f60005890780041c0074030402030280003440095501402080c101912140304242c030848240300e0314000f07055000d502c80044506e07161503040300d014601c003528140c144144402d03190700c0b806003400003800e07d208042d0709407000c00106008295180c058003113410700800806010612009520726842d20701c00d000070075001401100c3d00051034100c00580c880c214a000d000f03500071075002d45a07040b4620146d0301840b00840082c0c2509101c0c0b54208084d40c0e424a5000ca2400b40c0c05c9003d00203010340c1d10720404005c052004185411000304080000141c036000218164030a400c1261144000c0c2c17035000f014020b6004107820b032107007242c0b510303968 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 401983417 1250 401982167 401982169
    0x3030709031209120c080c0607200114070302010b121b1011030a030e07060507111e030a06020909100302061c0b120109030807020d05040512030c190c0f05 68
    0x380c2500001c0c1401e1a40061154403030b00507100c1d00014144500075100c41d0314030b0f050107411582c3c14441c00345035016000103600c5520344807040b01d0000b83c1c80013041000285601110715020380c446045414007240c0d140c02c413089280600a014805c0c829800400c0501882050001c440d220f401202d0690703105500318480301c2e0800b0204651003a054400216060401030b0071a00700844102c151520301000848180c01c07503054003c034801d41001e070100d4904c0e03640c6000072110b81c41541006001d55000c04070a010340d20b0a103150b51100c0b01c22610b0450054a00c6000070309041c00e40c14202c6050340d000901840a0030100302d020361005612221203031040c40c64010890170700c610005100e0321080c00280481c4480b25078465007140303401030207902c55407582d012514020036040c0c400f0f80102e41040c1c001400c0610000c1c25110402c0d0a6075541c5c180b514044c144040e642c5011281c90040c0414400031200003c10410061640146410b10050310a5420184051000e5401244840356032960500103 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 401984667 1250 401983417 401983427
    0x4172107060b06071406040c05010203190e18090a0c081204050907020a05190203060f10060507020a0b0a090e0c030106080f130218090c0409050c06210a050103030f02030307 76
    0x905078100c607001c00d001c182480010302c107214a0134001d00049144140c18903007400016001c0c800d91040d100e820500c1d454900590f6207004503265880705094030300c840083c032849004040000500074140c68181c3e00385401c80c0481c00000c94080c2c070554003078031040050001c6043d21030700604100d00078100d01400001440310324440c4d40515030050b00000701240700e0b58820480301c5c000360b1f041410340300d1494031000e14900080c10340e00c05134801d100305004a1100442070715079a00803820500c2c0c0700d0320301d4078000c02518250003510007aa403003d0000c00001c1d541820100a00030b0304030399510214083d007041c211102e03854024000020390f2a06000501c8601e820182c007a4101382d1004030765407d581d400c90002e0400000c041c00a401041c105001040d81c0e0070031003801d0250400728107490007046500203101c00c0b50386001000d8a142e004a100d80124245200141210840078031081211000f0740c044200c0c42c081520303403008003642d40c001042499884040d003188a00741344041d515500f026500201 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 401985917 1250 401984667 401984677
    0xc0f0906040b130905031207021b1c05060f061912080714010e1e010b090402090a110715150605090907110d030203040215032703070206041721 63
    0x200a581d901c2428510740c0e145410f00b50300e08581c0405101400721071034400d4a94018410001190b000000030444142c00818019009030101060004084d0100c0400800d61200011345502c1c0c000402e00b800420800d00c001e40c0b0030003d800c0550102c1c140740080c016000d0494481e800305600941c41402581106d4000f01003441e04260181d0702e642003810211000c01c040420100c507903203852464054003201180d03041b2040c03c0d001541c8055218080d01e0790981e16105519940704c0100d03000940140b40c1140419000007110800040848041c0681c10f21a8084401900c0e168020381a00c10461564015110303481d078a1001d410600303141040140c030364083c3ca61100d21074040b40340045c1d020380c440e00c07410340a107030200d0442d0010070803072102400940c815901640038140a03003c425400202d80100e03400340801c08004819226502440c043d0100041780314901400100b042d00b000d66103c0d130142000c1e140c1c445554040e51358244440b490058040394042c2581424244440b44640f01400d4403 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 401987167 1250 401985917 401985919
    0x305030112020102010f020d050f0903090d0303021c050c0705010510050904030309032a1502070b06010813050d11010f06241715010f08090c0418060507110c0f0906 72
    0xc40d03202664070060f4050070007074040e102c82d21f102240030800c0c094030380c1003180208440700e8905625200c40030742a03124400d1720052078200503580102c10010f0320a6006201c44640e15400d882c0e400322884c0104255202076070840c2040f8000b0681c5014070000b84902e0707411030401605558a04d28004c08070346079550060001d400d15a50b2203400c0c040c580030301d0010344000c003030343c001c180c0c10310201f04074001e04510340c2e42c1541d404045090f442140d4040b0705c2101e11054010b104008255240c0300110b500e0880248030584492018200b40c0004100b04440b140c4c0f8102d6889000700441d905181ca421190100c0f411840d10307003012020483d00c00d9400c551505004891036006104c951100180c0b0745040c03460290400340c134040304001080500c60341007290601c0907a1201c1020b0107180701221006c2081e02d0180d440d8000c039420b0078843c17030980d1100800d6801c040814032805015128501240c00481d0640040b462001c0c1c0064400420301c281c25003614115140030a00780301001098500d01d00074045 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 401988417 1250 401987167 401987189
    0xe041415010620011407030c020601050f091009020d09061b081b040b03010b1b0307030e0d0f1a070201052d0a0e030d0902010909060b03070e15160b09010903050301 72
    0x30070141103083e01010354030702640c0c0090001d00c00302485200400b0381210b000d00000e142036801120f0030b20128405040314801003108040300760060411840c800060700c41446665a0b4400090105840c0083c0810003035446d400503a049040c01d008041d95032281000042d4004221000300e040e07040442650441c01d8281c11a08100c042c00b030b07450551245401080315080084000265502ca8600415101a460b0380e110080d00c21841c44903500e010345c0800030086243c014421885040414420f24110b0080c1c040d41041291500c440e003015014a0081100c1c01c004001c004e14650240240390f0455020410401c0782c8840c48680240a44c018003100c900402e03210124910344150b800c070007101420300095a981d40d2002d20307901c00410b40c9400407404614498000100d10f00c20b40300c2c260494010701c01880c0307590790f43d4208841c20303810324100c0b540c0404000c00703514141c4226005003264a0554950003c1e051060802159403075000301205400d0381003027482c0340000da214054034111101e0741e00c9 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 401989667 1250 401988417 401988437
    0xd08090304051206060a0b0c0319050d05010e180f19020a030c0e1506030423010f1a09090f03040501180321030f06080c0609010302040f0e0414150106 66
    0x11640c218071459006990029491030700b10700e051808034109000d44022248141c0b016507518001925004501050046030001d004543d4440c0e41151a240741480c20f19090346021348441c3c0c14000c680080e0401600306600c1c01c2000081000d030705001082e241010003c0001060392041c186d511040c00e020b14040b1f407079010444046413212200b1034007941c0e00c600a6148151102d1040000c4035044505204108100c1001d5803d4188441104e0040b0341090307410401c01107001c003c0000740c00c081130603041ca6507a03100c4407aa10380584681c0700710b9120f140c04100c0a180500c100325200001a00d005010b0704594500e003e0305100008a03000c1751801c1c2811848400c002403e00c14908035175001030300514443c400d001c20000e04c3d1000c0c1c900c44e46242c07000c029a0b1721b01c0c2031800848085004d120f80703582c0050740f0301a243c54024046d2070401c0781407401500e49502c4800350fa14031815540701652800322601400100417407075503441414100a001402650700401825400e444c0600c2100c040c0b06160361 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 401990917 1250 401989667 401989681
    0xc0218160c020f03030403030206220f0201050304110a0b040602010b01092102011e0f030507081006050c0f011103010e0c2b180c060801153905060a0b10020d08 70
    0x4840c1c20840004c0170749440d80e6507410081e441d201d044800c06030320000b0403251a40799400603440f240a5404c291485208111580195080d51000d40b00ba04c3e01d04005d5500a0301d503407924031075000f80840010454481d0b1a000010742520440800f80d4180000c1e84028000c52084002070756070010a4009480c3d441e140b400141c40c40ca01406410081107030291a80004640003c205460044981c1c2c0c104603e50391860202d84030700042d5101c002100c0d05110800255204074050080031860500b96804044404041c508403200140a194850340110040250828008076964042e654078809807400c007030320403040a550400d0600410820300d00076441c0e00c14000b070b80400040c000409280f01020351504250058054500c00d000c0090304c400008a03415450001c10705100712070327498034906070b480342c0e00341500004100100c2803e0300701e040c014a21050000c07a11641c4501581c09800c090601d00c820350f060324003032520540185000104c626038581c1c006540784580c401c070728005040b921004 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 401992167 1250 401990917 401990929
    0x6050f2203080a051c02030403020606010c1407060809070602010507170405010b040906051b18040b0f030d090e06010302130e1503010c09050118080c2e0c0218160c02 73
    0x2030005041d100003c9000740e06590000f000303240c140c0300300b21010058060305202c0c0f030a034032040783c00a0042c0c02c000c000c01c10950003070b0843c5140300c0c40313416080c50341201d02400da40f45c2101c0d41c1c040030000f400e16090010601080c001200601020701c02400140f90045000c1c10f0a818071591240d4114501c0c001000c2c00f07003e500262100d5070040051040609905200e0050201954160405134001909441014403201201e00008403100044034081408040000800500c060103400c80300030400550710307503001e104504601e180394031950b900380d06003a42c0d029241350003000c050501d4810042003920003c52075180302150307a5444c0c072840c030b641d510f0302000846101c00040c2c1d4066003445618102d468001084d4426a00281c0e12480550008075094031410b2a0b032045507541e40040c88191205d08000a0b021a14404088441500400c0c05412601c0140180d10440000c5a5070190801c5103005200034a0a02140c0300c100c0e86410403900c03c0d12034451020841d130602620322000030440d1504 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 401993417 1250 401992167 401992169
    0x7050304080607030b0405070201273801060f05031b070606080105092505122a2d0103050a060806040c0f080303040503070b0601032a02010606050f22 66
    0x5003551118240480080c02900040c205c0c1403150b401c003c0059034080c4144101181c401d60701100c0914586a5407490100b89884c2c1340642d2401456035003211726a5040f41d41d18203103801d03256002082c911010b2052811801030f00154100807038850a80309241e80300f07064031b401c00d0304060390034001011104216114401c010700180a2410101c0003d42880190300c03aa110348681c60666a0b241d02022614007201050311900c4040009030009010300c3c1406001003c0b1045450101ea00740086032a0407039545402e40e000c0b008148461802c1912414003243d880045c8003144d00c640141035080d40e031400046003807040f80e4105581c07440013701c811171641000000300b0001e024ac5102c1d042504180c84090b6490142000d00400240000742138600081100e01c1103800101660424080b0f5462000c0c001001d03050034101502c8103550b809890324114103160f010818000194460703403d42020f030a540f00c5611003000e010060105801c103210f110304031103185ca02c0e4580c1c0c2400c40420414020800f0307503 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 401994667 1250 401993417 401993429
    0x21803060907060305010501210504050c1c12050304110904080409020a1106070e060720040c050a1107060f140d0509030a09050a05131a030d02010207110301050c0f07050304 76
    0x2901092180580012510300291983e641c0c003070181c3d0384c80340015a1451a20210a0b401150072015110f5411a0f544021b801c00d1043c0b0a0303c82450007540000d05c200e200d0401c6041001000540c1004c00100706000340c0491058100346044d40b41503102c2d1192903050240f054000c0700c260000404100100e400c03940507211319501107444a824010080a040300048220b003507101d0b12000c41c0c0c516003d500821135102e4001c040c0b600c1c1070703020340e9070450920aa41001c112a0f0910852190907070301c41c080c1c1083e0f071800381d564075115200c00900410758188003a00c98025002100c0c14041c040c1e008c5180d08100c56641415409621015001030203407150812001c1481c0c070f81401e00440c000040018a0303040025a03601c4050340e211010800e9210740d83c411182e00040e251504500c40c003494100c400c220640d00e008107562046132001c40c7c10f060b0346000510050b58001800010001d0851800c00384000c1036000f00224a040b03c0c015186110b8a40e000c24080300116106007013000404c119409444 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 401995917 1250 401994667 401994673
    0x28050705030c0c0f032a030412120905060a0f0314060907050a02150103030f09090e03030f1512010b01090b070206030103080c10061e1d010323190c0803040315021803 73
    0x6c46207058241101005403103481130810301c180802c0010000180c031f058540d04175410208504540c2d41c40c0030051480104010f02007075001c0050300369503080c003600c000b44040d11280c0a02d80b60324030007400c550880031140000c940071410301286844803074059500c00d2580c1001582c940e686201685845400c0c00c60b460811361110002c400c241e030100020856421036112107444035100c0341d001040d80c0d1040c094501d284d00500000c0c55000c10800d5481d002103104107a085109a410045203020400301e4800d85969119483e0390150350703011422400410320701c0030765410320103580e00059031440113204c080c0141070b011649c61402c1d00d0a000400d1101200c52081000d565951140c1ca0403134056649650b1903407019800003144000d081084040400d815030b204540d0f03003956a0401940c08030407040c00c402104241d40000350a003000f00130350001407681c01c00100c1c100c80c58041d002070415000700c40e05400500040000035690010b040b03242c40711441c0580c5543c091401c0c1c80c0c2c00280040c1e2640d02d88 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 401997167 1250 401995917 401995927
    0x1704211404080a06050f090604020d0804080f07140607050a1b05090a0609050a090210231b0717070b0304020f0915040b0f0102070302060304061428050705030c0c0f03 73
    0x2c98009441c076403441c46210300384441e03500d83c10310042c40740003100c0520705d41c2c00030300c0041d00501d44042c640c10741520030708105043c00d440312911440c0c0855100f860b40d00358030070701040c00080000b0f0150449180200c0c0d9407840d00140c1e0f61a10740714800c1c21401441d021041502c0b40c910701c0710784a50400ba0030041d01000c9a4038009035a10090003040c403071083c2051400d40860030354640b81c0500100740ba00a4004100a00d100310300301c0b01440a65182030754518090950b8100090300c000406001c0d1042c0140004000c40d010001d085c03190315400340f600b03062903c82e40e00c04c861303001c16440c0c1250a0300c3e580540360740e0b850001c075003000b51399801141c2c080e00e1001042900503812250b1940407005641c2002020408001e01603948503202e401409680520ba08000501c1e0410055030301a1080c80c0103e48048041c2078480d040c0d000707030b8008840d46a00603038004030059468620f65040b09050040c4928100300101415a1001900c0600804000604040c840c41700b0408054100e481c00200e90f075271 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 401998417 1250 401997167 401997179
    0x1150534030203030411180420100906091719050c060409090b090c014a090702010204050a09090516060306090e0319050313120903031704211404 64
    0xf81d402164100c4001c44400c0c406d42c180d00b0114030065941030411402181e64403162500c03c3c0700760480300f10490300f00e00300000c8074a544403c1540c1e0410840354030341c01011824034401801c059101e81014640055180c500082e0b113800044140030041c01c180e0b001c0b4203050364204507003402d520342c101c181c200c01d000400256000040e40a001c00f10b0159a0451154640001c001e85a650711104140003801a000081c4410501550460000c581c568003950740300550303c043d400c560018286105185042120076520300740b9055084c4d01c4180d0344000c5140134207085c001400407516001f0000c0c5180d843c402081086400c0064000044024819032401e650360340c0002c1c00b5010500844102c2424084440c1034580008182e903001c440d44d40c40800303003802100046403550001846c5014a552a0108501107071f103038065501c0e03105c0c00b552100c43e141e0441c10301820051101c0d09020f046040d007402c20011920000c0c14444518a819404000c050709107000c642d00e8807004528a200f82d80001c0000d04 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 401999667 1250 401998417 401998423
    0x30f0a0504090509030a0c081c0f0c03050f07090b0f04180e0f030901020606131103071d01210c030b0a08030702150301030308011401051b060906011505340302 70
    0x1180d01c814000d01007650307076001c04c40e01d0340a007185a03c081080c04220400291040002c0c10040940d000c5500d0485050000c01c41507480041c44640c420359180e481041596043c0079443e070190725a49070340142d041c00c44000380002c0442c030960383c800070041180300d030a480d050100d40080a054010f0b044520b44090000c00900c0028201c2a080c0708410150500c01004010340c1c20551058014142c81e9881030240014401900b01e410b59882c3c0ea03401d0100720360700321302c081d502079056652040391071841c0d543d041c5d080d40404403450307040c032651540b00f100042600c0a02c2d200c1c0c3c1c1d030140010880d88805401600541121110143d001500c0c140100e00c0c054000301402107a8000c0b10301c4c48c000192003462b46110302c000e000c040e00041c203141c01400200d9910560705403121040c9000b0b80341c505071189a00040707501d4416528550000340a0003541c1508000311800340076843ea91030b5080030078401c090018800c1d091911440f00c8200e070415071203a1a84861940c400040d21600300242c40f524009403 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 402000917 1250 401999667 401999669
    0x120e06090c100f0302030a0608030c0a141203390d1a01020a0206070c0902030403050403150614040c0311070c080d08010303020304030213021608030105041805030d0e030f0a0504 78
    0x1403098039101c1e6a9071a01408003412002c1c983c446118002e4260001c502070340c0020040301d40d0039161040043c2e41801040140b0380d010400c8050910a074031894100c841030700420700502c0540c00f100c58040c14a001c1403c80390004084580104220030580e5403d06900428040721040d000c40552064514080002002e17110340c0700c0400c001000c2c824a8031000703d8405000f190060340684800001410514002d2941d1400b0b00c084815042e0341d41c585005136807044a08400040300880c040040200502c00b02c4602b10300c1310b5045c4456410080080d0078090102e02d1144501d40380c40304070041c00d00a46c020101c02c40554031141d507601403410306283c540b000340300700d1041e0b204500071100d4191140071a203040c0c1b90325034040c501e05490368013007002d80000c2c80c0762030308080c0c0c0c208500c4034207244040510001074820807000c0e80729850b0004100840d1110542e0900b5520881c0910f000a07001104950110650b000001112000003012034a9402014003583e03542c1d00015264503410303000030240c0 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 402002167 1250 402000917 402000931
    0x90c070f0b0a020a11060906071b050607030c11010504020f040f140411120f0a12050c0d021c030207020603040b07230c0c0109030f062f070b060901030c060807120e06 73
    0x2012020348a05c49a645180031669034003290080c03808031341c20500c11161130f1485040580502018020341d02d0b01410251b05a07031844c0880c1c0d0380c90000c5584c0c0e800a0062480246505c001c010a00d05034001c15800c00d0ba5014451045644901165524181303500100008a584803c3c040c1031606143c401c00c030000204c94907101d940c8440100c600000005440d1101411000c06450008510340e184080c090100a04c40f00b84a030601000a0046081024a1180d14a5401081c80344222602c82c0f00380507900344a0001c05004000450168031a5007c498015500041030215951130500c202d80c0b800b10721103c100d02480510384d0340c50300140c030700c09001c403024120282d44403090b41c440195900d0f900d9220007050b040100d0f1040c000b0400380d500c0700b40c00144005c20098800300c0302544c6144034141c12021003d0700000718880c402e001012100301e0b03004009450648265045882c1c580303810146210b52800c102d08100000c81c0640b041c4507202d0351101101c0280420200d002e20340f51100c404031218 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 402003417 1250 402002167 402002177
    0x101106150a0b131e051516170306120f030711190608040507050102060f060607020f0907020706030e0102040b04051002010b040518010e01092d05060a020a120902090c070f0b0a020a 79
    0x40c13440603203268030004440307000f00700030140c510114507508560419420030812100c400524800f160110711000b05070f40c03012041d6540da2070204108150000c541005206e10f501043c00e519410b0740000441707483d81c0d045001990b1840c3d400c0d00003400041001500444103214180001346a50414840b40c0264402d00c1941d40c0603403a030b401280d469008880b07000700c04840802082981c1010001030511a0024084403004842c501c046108510140c5154005a00584003003101c41e034035220300007070f4001040c003d40c0350610302446040540198050144146030088031108054000d505c01c1d410003070084c00c180700500d001e91070410b82c0c4130f0004d5160a9542824510040440107100384205075600c20007800120702040740740800305041c43d2204030940154566107020074000c1201070b202e5030040d0760240e95909051402404441004052004e545c201781c142c40040e0f0b02e40e00340660009082c0326042c3c9030186800c2103038035203445510140852002a05000081d122500180800d040c01e07151 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 402004667 1250 402003417 402003449
    0x6060c14060402030c0402031e010b0a09050f0907030e070906030c090c0f09033e010f08070801030b060a03080c0d0305100506120a111305101106150a0b13 68
    0x4903071546011640254560408000b61040c2c0c6006da0196402450f441d60100c01034108030580d48050310700380c1001c800200046107000d841070344046058090320081d5200790000048001149500101405c404e0602d516441c100e4001e600c03c104c0440203000506041c0400f43c0d407820700c014152254041c89049508022250f51901d0140780c5000e0000c0440c5e0350281e10a1868941c0380c55440351400402214100e03030102d005c00d13500080034182201d01104914803a50f02e540004d804642d4201c0c17254203200b944800c00c0b2030180c0041c4441e04403900b02c5070010751580c8403400284002d0454100420400022900c40725142e00015952005620390310b040044c1c1d16600b5000050802e580300c0c00b17504c154200008040c1107c41d184158110b0000100071030b00303800c0c81c0c0c0054025000300142100e0a488130004205034034052042e1862a420b03804c00603907402c41c444420740c41e858000c080c2c480d52020300226802c1500c0704c940380402403101000003a150035021180080c03a900c10b10804041c90b07c5012 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 402005917 1250 402004667 402004703
    0x71a0c130e090a120201020c12030f01050307030f0303092105070b06060f0405011101090212030d1a011d010215150906040c0c030c08070611070203100b0109171006060c 74
    0x41610301401c190001030040f1051540c072041180000580c0c4001c40d50240201d03030301c01d00100155941d14502034a000d4807480c204034101e0340351405a001c6442580910400c0012584804400c51881e425150219075204142800c031086100e10f110303c0c440c1780000c2a0101c40c650300c040074021300c5214000500301e94844004020241c026119140003d02c02000300b00230543c0508c610ba1803a5080d440042941e16894000075141d04403c803030000590030014610003004018820350441100769020720004a01e031900080c40301503400f00f45007101d000700301d07801d0b50742e8001c1148600764045034060340784e0751810400822010001150f45c60240c00c1140100c5c005251600510000c80307080d60702c0c080e0594450300d040310b440480c014141c4036134408126010203c3c05074001d1050510110203103503610700d024030506103070098030a282454185814100c00c4160b9214038040202c46196000107000949040b4260501d04000301d0102440c0c43c0c90000035416810118851403280280002004203d0f525 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 402007167 1250 402005917 402005939
    0x1202010e090c04170c0901080a05071505040302060706180503090102070e0405030304110a0f121e1511120f090c0a0b030a0903031107030903170c0c0402071a0c13 71
    0x28502d811038040a100c140a880c40b83c681e10180d260000741169107116440e80400c0b5000801c0e08101700640002071450240030303040100c0f0b0010708421404040b0601c0e0508000c00b80e02031030000a2154000050000a001240c0c11840356170101444410401c1810716101d0b41c1c0b64058080a400f50040550010f1850480d41100c2d22654114010f545503581c0c0c0c0e80d40805401d001103005038010000071010510f0300c4840082409080c0c1c48080d4800650f06040801100e0261840c0c00c5030188581c105000152011245411000f40d81c1d102142a01d02c5503242000c030702914804002c850130580401030784460480c08180104808400e03160051203400610200723984c1130054500c0108104081504035056900078908140280340020703407080c14154030b0345103174003804061303001613903031041813090041c220402204c00c03882c02c520794900f940014030389460701a13940d002032146602250040500840b80c00c940718641811001c9102c0b4900740382d10030b2550300903621240224240d00404030b080f850b64 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 402008417 1250 402007167 402007171
    0x19200a050a02091b070303020307020111031311040f0f151a18030a06091202120a0e280f092909040c0b0f1804330305071202010e09 58
    0x160004804503000d212a445004e08038400c100b00115010303002c901100098051140b00b42e40240e0341c0d080103e0003d094417042541854102001c00904c0210b40c0d0001e0000081390b0b00441d07001441c2c0b00000050300401d440c00d21a00c140707007002540401c0c448140d0040703c450200e03224600d200b0740c44816444a00404000e0317220f9000c1b00300007481c04422100200e40d04100c000b400c498211003942c0d202c605440540c00c080300c4020304680701e0207560760103002e080041a101a100c500701281e8210050900e0040c422550198242c203840045d41400c000300e0304032f140c540e01e590800b4560307955040c800e9015140705440c030751032030607448140410841503c1c1420007180744980b2601181c40040154400016204961440750410005512003040000d800100040000d0725240d06500d60b4202840400e00d19485c807661030500d504000f1004202410004c0308010031a0310b0800d0068284400d100480c0c1002d40341c2d100d610800030f45030345034018070b509181c030030303a038404601030844140203960200b = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 402009667 1250 402008417 402008423
    0xb04030305120c09031207030f020f12090103060305010c0c0c06170a05060117070e100809032a0303131505100b03090a0f11030105160801060c02040219200a 69
    0x410000c048103208000e22460f007081006204a1400000c800001d01d08801040e0000865001040244c181504900500709060a03400900400d407165455552564407106081ca1f441c07402042c003d505034429030014014560010080200c0f030072003040604003041044003207960302400301002c11481d20403074210450080050341812140c4074030200c54060000144418108240d01d180e40c101141e24000003070007051145c03600400c4035188003c2c030101e5a19001000140320700101481425440082161400f1020200c0004140c0100d5088489440301c1082111144804020300000d01d0f00848403d0303c0c2e500c070b1b40c19540e00840211001c800c1d03d00407036103503a18900e094410402005214000c3d07034801040d20540d400e507090f41d43c40000d02c5041443c29038407000320031007541007810244241a002035071000c000d441100301041c001c200740b205024a0f020480300d00200da003107440b01e40540302842070b804040b0b029007052007001040c1e25103840c2000405a00c0c9603030b03440e00c1c0f840462080c00d400c2d0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 402010917 1250 402009667 402009677
    0x705010f17130b040609050601170304091d0718060906030b070c031803060b030d0302030105100c051e030c1605010c061104080f2401060e01080a0b030f10060b040303 73
    0xc001820303281c200c04000c01c1c04502d0340001c9182c400049502d00101d200b20b208260002d4a800242069881e00300e05030840e06000322102552541c0c035030004151400c4074544040410390882d480f58480c0c91080c07411540714948034805011807096028141e07a109104039610400075595141c8140c0182c0300a80701c081d05614045010840c40d038455110f40c62818024244062540117031440d000792014550303c00e403080c5940d059000d5003031406003c00d01520540b031406508550421000036215040603604200b0300404504030000c02c00244a4002403c0c00c011051011103c00c102c010340781e0b40100888480c1d800f03034102c40311205142c10300c0c0d0015928180d6540300d0842850355560024a90484034000c0b0020030301c40007401d28000c02c001e54003401a0400b40c0b0740d40401c0004850204000e82c00e822041014000610034168486450354a00000746040051f988401c810440189501440e9640502400581d04c24a1400181440424031611020001103996200340480307401035000c0100010703 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 402012167 1250 402010917 402010937
    0x311010216030b060102250f0e06061605010e0303042a0e06040e0102070c0b040f0806040222020d0603032f190201050c0706081e130201030e120304050703050705010f 73
    0x54180203d2903407003c0c0c10f00468000e0a603d40941416500240c59042d580c41d4501090090000c1d03000b14400a00c0060321850150401c000001d515001e07034004050071151131514002404000d40140e13440c0d46600c41a81c0e40d80c00c00d4104007003405011100b40444802011016003404480d21006c0304a981c0100082d40b00e403954070402c00a441d01c0b400400166409110407000325509400c040018110320060f513989a280121a22110f0300a52082ca82a04088100170160b1150f6040d080d5120300c5080e51a0020610032158000f4001c0b8441e0000542c0340a801104045d004404240e40c0488503124000c030740401e0300400c0407000308030034500791a00729200b007085c0b00c4040056100fa251050400d503040c181e00001e07152400318254404c00000b8809024080a8042801c503c0d203040424003003000c0c20310f0000d1030302078070321803032603000781015520145040c08100a00c901103901c0b0155503042e6490070f050a007582c2c0e803400c80c00196524010300000041540c0140d503001418070039911041066 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 402013417 1250 402012167 402012173
    0x40506011a04030602040f15020a11090a060306091203050604060f170a12090f090603110f0f0d0b15040e12070c090e010e060c040b1204050307020d0309031101021603 73
    0x4a6141c4061514040030700002c4005a01800a080640a1714031861816894040486090f41100c0351081c2950050b5003030300040b0b240c01d144803061038006d4481c01669140d02c03103102c0007403119a101803d00c40c607280c1c19108120b0a1018240050303c6903800f0f0046440c0c00c070401c000c1764441d00c1546400007c80100b00328486410458000001a070300c160740c03a2140d00e880b4a81c80110345802c6500040010006010b80c10700c2d0001413000d05840d1070204501c90455407409100c0818917455882004440c1da4081565280400da5240c00c102511541c4081420314240e0305401d0180c90700c244481018040e510b01d030915104045561007110700800b034203044200030140716449071100355400b8040ca031020640305094013502c01e0400c18030000103100120540000d0620700094840d19441900b00020030000d41400c054504500340c00b80742040395180e9142492661080000003900013030002207038400c0c590040740d00700840c2d000f0f259150003401040012a12070284070b001d602039030b08840050000c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 402014667 1250 402013417 402013439
    0xa0b0607030e04090204330b0a05091201180b09060708040f030207080105010605031e01050f01032307090510030c0c0b06270a06080708070b0f1308030301170604050601 74
    0xba030000504001040d8600d41c010400341d40d1000030040f900d102e4044254402e4a4043c104030701c4450603103d011403a030402031045141d00c21011314008000300800e240c43c080c1d07205c0300c0b84000c1741c8402000304000c1804403c80c0750701414081c0d05481003442800090301c002804140c452041c0070035510250300d50345954500d1011251528213400314030070000c0208840b14248a00c6000e01001d858690b283e203000f0301401c101062502048051150440040005482d1400c401030814003d00b0301003010044070b5400c40f1000e002007081c7c09400600c0c4107000340c1b250407007449015108195102400f8100b0310388194141e8500f6154400014011680e030004910105165a00140028005600001d05002084122078490b103504e00e404402c03003d00845d114680f084200801c9040058100185400003003601c1c0c007024880c0403081000000c07110004606407084480e801e20390103441120a0710f60340099500c1e00b090042110a0b1144089030424640028810384507036800070040c506a0700344114180 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 402015917 1250 402014667 402014687
    0xe0a0b1008070f05090705130b1b0102040906060f0801080d030207060b040207060507030b01090e16140a0e0405060d200f030f0309040516050d0c0c0f050309090a0b060703 75
    0x105000000c80c012421039414008500204036040b03005040f01d003008108203000b80003421107000d10004000080c40004036000c49412540d5880721036071101a03041908a00000c007205459040d440010045803040c00c81c0c1c406400d40b0b0843c0d4950b00b2113085000d081e12001020300401240c1e0b07000e68212100981f00c1d40003490054420074010540e101440301140a0360807811044850036218802c10056039414410743c08010400d2074101d140c68644400209401c6000d4407451511309514000481240a401c02a04c1d40282140301c81e95021841401004403a0704800a40f0075402c20010516914020000341390712a04205400003100450111241701c00741d01ca45aa000143d02510030300235a01403205640108401020715500c90301d00302000100c070802006141d20f00c10000309040403907841401c0e2a543c075240d00f00083c602d040200300342d5054907900001440102019031a00401101201518a621040d00e000c1801d444020250040d241e4080d062038000070700f406403102191103400084 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 402017167 1250 402015917 402015931
    0x9060a0f0b0405010608071e0f11031201080f010f0203011503020901020a081c050604090f020607060603051204170607050a031e021603020708190609050f1f0f0e0a0b 73
    0xe151400007000c5030039a04264040800309410301c08000e41c01c0d8008408607281c0c0180034032181c5480448202a00141010440c9010000c22000d104990401041150300030f01d203503841e071200c40da950303541d00d6603e1b4135100340100c1c59420002c003442030002a000741c9040c1c500704010841d2070018200124003d4005020040c1144100c940000c0031a494000030001c40504091002c000c0d00e500e40354100344c40c00178050740d0080b846c0040c810080349540e41061501503045039490750702c8800d411300300c025002d1500041c00c103006001c683d4000884050090045030508141c0c000c1d14500d4040c0a0740743c40007182c868000c01c07020000d2043d281c0c4282d125082b0f607004c54030004000d688100c0c01e80200d070000b00c0106a8462002d5007003080c9601008100b00900a010007002c10002840003071500002007400100040d84407101801000814080400860751010449001881c40c015a188070a00100e12611480c6400303031f002c05000480c061064102c2d222001080e41100c959104188408014110 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 402018417 1250 402017167 402017171
    0x20a0e090403170f0a0b01020c0d030c021302030f1504090c05090a11070812060907050d09080906070b240a17010b060a02030903070605070b160201150e09100509060a0f 74
    0x1440c041905483d01da0040703541d15651032251074041c13882002c891081c640903040d580a0502c04081c1d6682030702400e80c6a80c1803820f400724241c0c1d0702c04140082c12245441d044c041c004400c21800c28521071041e886951a4440c0c44116903034242408100d440c5960050f04000030038400384005e041401d003440e0054000750002408540081e811441340c2c0041400315515900000d0782a42e01c1e4034003114540140d030840d48800359052550015159104e100c0f80c2c0c5900a840c2c004d00c00c00d1050003400d4928244028050039510380c0940340c00600c600f81103507041003800884004111000f01c1101441c44290042d007003900c91420801c4808036003011107000070700f540d00c0304d40c43ca01e181c8682c80900700d0303500c0c550002c5407969035503001c150800381c1c1d580040007080320510003000400c0040c4045038101032400b80710050038111a0049025081c0340010000e8034a0750000050607410214030948610101c005868208400300100f0003507480c20f4459034082d9128a010039003080c0c0d00c0c0c3c001788006480c1c804c0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 402019667 1250 402018417 402018437
    0x90f06010e04111201080303011503110906121006030506011202130b0a05030901290409110406080a0302011b0c2406090b040516050409020a050c0f031903020a0e090403 74
    0x25080c0c0f00d501c40e48200705400440c412001005145070380c1d0240041001131400d642c1054000e80031401d80e145c0500c101a21071400003100e6580b0001c40c0c0741c5032800f03040b055071008003214000c03a248045e107280b029800c810710000703440c0c0d129111f1b0354001c600c142d65014802c002c80c0d109001a4102d481c135100c5848030701e000060b40d081e01d04010241c00c1c2003a212036480b0b10b00740e03d015007140c0c000480c6000c0a80b03803481403841400c0e0b00703005500828088500103030034011030070401060840505025007180c40e010000c0b40750080001c640d41d0041c4254001d0011581080e00408041800305003031003c5607850750a0000030b80c0740300c1c0003c141c2c2c4000700e8940802c005410f040d8103a80d141d9100d9170010756100018042820207020702a03004138070003035070b40c0311700080e02c070040c564441d611501c801a070b80424403e82191003101280c204455807011190408004405642c0380c0d80445c3c010300340d5003107200035500014002d00a440500300395840b94451010700070107015a862006200b14200000c0c421 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 402020917 1250 402019667 402019669
    0x304060509150301081509060103030504050402031e0103140c0117010b0a1b080d0b0607050a030509040f06030602030105210a03030207020424082505040e010615020a020f0f090f06010e 81
    0xb0140d8000c20b01c50b0000d241006500c00d201c041e506003e8915200c83d04004014070110750480c040350200d400c1030354016500d41c1c900c00a040e4401d260040300326100d41a600010605c0881402040c40c040c0b01002e95a446424000556000b128103544145022082c4010030074500020094200100e1500b02001e018600030100c2e0b4407248441e500700d941e00b90200e01c040d0012094403d0b00030a01040d0381c2e00380381c9005070b08c0c2c0075a111880b4200404004001400140340c0d161170300251007400c0d0305401448042e032a8941000a0340007409054040c041000103074010880b000303501003540c100a80035000104842e02c0480203503000f00c0050781c10a840d110340360b844546145054100490301c01c1d1700c0800301e060006042c2400b245512003981d0341100c0c000381c0c45503542100010111a001c6070002030f500e1800034020302420603540407005070300385403003041581034002c00d05551251085648809020350720080028a94081440c1a00039101d0070000352010325120015800080506203800100d000c04 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 402022167 1250 402020917 402020959
    0x20a0207051c0b010929190b12060307030f030c020d0f1b050316060323070f08070c0c210b01231c0305031905010902091903050304060509 61
    0x1e02c501d8100b02c00d49090703802d01420f54040c2e030140850000920039510000410803529001802c22820403102d0f250700840d542d2444040070840d50300d050f19448066a80001c181e071038005c8040084240150310001c0c00c20700e004180700080e03903440070782c1d41d983c0183da4504030303003000301c80b1804c91b00320100400110204032200e1003564000d1103290b12440700298003007200e54803010742d44024041e42c062a0860386a00c2d41b0031541054508603e000a0058086500714950818025203444c0707015049051008107070b40b284041a00c40881d803036050481d02e80200442d000d09003500d01810f0901cad0080e09100100c401c1040d00441d08416051114850860702c03104000202a40000b0340c80014034030b0a408581c824620341c151081c1180c01001601120024424040c0d090f04001c04005c0000000340031100c0d4611000d2001910801c1041b8171368644190000070350049200c24440e680401e05104420a240c59130410740b42d00202850419181410030344180e000b0755002d0b640410f2144c91a40c54048c81 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 402023417 1250 402022167 402022189
    0xa061103091c060b030601032006090d03050408060c0a050f093706030209061e0708070b010e010b0c0c1908030f0310150e0108060d0209070f0809010204060909020a020705 75
    0x140a03410024442d441c00c80110340045200a001741c221500400200d003c20003c407407000a0380c14035a08446100700022403030322070b9000081c1c0c4050284480780a255022000d802941da00c0800c44074241c654a50110140c000c43c10f007803001031020407008141c0010076010745081c00e000380c03030840d110504107090b501e503038011803210446030390222001401c00e0300210703888020001c0d800c04619110001007c10164420b01d038502020050401201200c441403000310780816411100e010340b80c40d028580031403402800c0c403a0491018010300082003c903007020444840408140041c41151525400c2c80301740d0144000502c0380800d0004002503001c41440140942c94007200104c1d524035154111440c8030340c1c00c3d0802e45080c40c4044000c101c99410285610807000d007400c200d0021f5513544005024512900710003074001070140180b045480d00080e0007010f056007606d48041079610513040608034002e03403040000081c0002c20400c420903450303004052500311481650b03d201d40f40c102188441044e = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 402024667 1250 402023417 402023449
    0x11010c0503070b0a110408030f070c170f12160b060105040f030302031309060513091110020a02011706010c02130f060b130902032707051003020a09080604020a06110309 74
    0x43c1c181080003040403845040003003103440300c02504090030000f1150341c9010700c8403a80088140000d040c0c0901c080e44440e031004203400808010034078000c41c10651a05141883d945041c8a0070766110745524001c0151900381d41121081b2803403000c140c5510b2030302080a042d01d410b0020421002c28002c00100f441c901650013600290390301c01c66404001c1000442c0d520041c1110700e0140b0500a5940315080c01c415640c040718086090b4040e41000e0203500c41c2070703041661100c90040c40044868011407019902c03030003601c8030591110351214215003000200d40d4030740003d02e4552201d005207862040002c0101e03040000007142c9803516180e40c1210019007110104250100d00c0380e160110000d03801024051206c0d0a5085040080d05000300072010304606c500e4818501c0503500c0c0150802c449002046c0c000c0400482181c0036801134000d51007a0311000008140d1200406d00c10000503640c0e0090b0781c0034241001180c5451001c44400c020f10490710120700003008204415941d0b44007007800009 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 402025917 1250 402024667 402024683
    0xa121d0f0d121115011d0a0f0f052703030c0c0a0507170613080a1110110a1214070e031c0207061205240604030602041205012711010c050307 62
    0x1280141c071450310304d4804c0340b07001c101c1545005001110039107054400c0c2c3c50f03002c07040b24440c0d20392211400203419031a000c054014a0100d81916402d4a600814095041700c02140c80707800d040700d8602c21110035222180c0d0264010404502c074610b08000a101b0820907400342d03110b100d4a03685070790030b0410a9100891001c1400c4171040c0c403150500100381c002508502c88091151076941d0312103c3e009150000b020b20244500c20004100244030805180c0c4800740104081d101541c880c2189030001c1c00c0d1080017403a002598009840c062003040c1603403c05c2c000754103841e42c82007401c50f40b0150041107540c26005050680810003440044000c242c1d1544d0064402c180c10038100901250340d00720b58010710380c01c4c00107020740075441201039405c507800304403d024003040d84400324603a8400c960004024500c0010002140c040000d200c18555200740f00034005440351781c2c03002c060004680315001c5003c1401903c00005414050b1a02d040e19060602c4100314240340c40310f5081d80c00c00c0c001965524 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 402027167 1250 402025917 402025937
    0x102070618050604060c12020c0d091d0c09041d07030201080f0115180b0c0a2303030f0a06050a09020307021c0903020402070c0e04050a121d0f0d12 65
    0x3a0255102006610074540740d00c0e94941c4a441c0d8074034000c3d101511280d600c0c091050b000788612040032682e11003504c10340d1b0310304040000ca581ea9290002c43d60010b00e20500100e80c41e200e20303000003444192900011595128880005455885014100e502c9560b9044004070038651503041c00390b4441c02c101401d03070503142d03000240c203281c80180f03121200040f00e401800300494603100710200313440a15086059160160003800001902d40001c413051201146200d5250400203450b050342d80f08103126a40d64900340d80c01c2e4030741c50500c010300c03440360010b0000950382c0c414551116800358444901080c4a030b0341e0804505640c2250700040485c540001c01c1000942e010000f44c20740400341826030310201064a0014170402041c000244a0754002a4840510500400c40006000c1c4140103207a14140307850300340d03030380d090403241150a00c48819141202c54003a107044d0025004840008510712710307080800a071240e44e581d0607a400f400e443e45075400f1406140c500c18003c04581c80c1e84d802d00d = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 402028417 1250 402027167 402027173
    0xc0d0c08070b12070c0201021f0e16060806090424051e0f0c0a0908070e040302120306060301050402160c0f05030c0603130803040309030b100905090d0c1101050f0c010207 75
    0x745881e0020221980108411543c02900103031582c0c0c032a0152822158151483c40102d041001d1115540c0170301045030000c1c4001a626130041c00c20560740300456803442172107407a117480c0c800280b0848010480074400640300d410050340c2d065105109850207818401e610070740c1e101140d59500341d400c015960700c0c104502c44150440880ba10300701006828018030740086da034201c200000f481c1088074003010400c0d00e55540246041c5c0003618003c002c0d00c268130788608080e013a910701280c0c1030b40188540941c001c040040f410480c0d00401c00540301c14550781c00d0005020181d4403d1900c418807074a4071030b4000104a540c092000589103190381c00c040c8a140500705441c044054030503034030401c0104240402e01c2c524241c003c4180e51321645d202c0d160341d01d82c10151a01e05042c2c1c070241c0025105410030042421303810860042c2d41d0900c800b004075442d2000c8090741c0e04031050070f110109956a8042c00400d101914107501c00f241458022b02c0e140821400c03034525046540c3c44134442c2e402092542c20 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 402029667 1250 402028417 402028423
    0x80312090309030a230303040605151c0b0c1b0f0106050a0b03180a021507150e0618030f0d061502011e0216080325020f0304090b030c0d0c08 62
    0x12590540045051002680000e510b6955a207002001e940e10031745090782580f03000312095054403042c41030b0fa807245041d0034000090b0404542082c501a15690b4200b0246000b0521501070461003056044000c101d58400c008000041c0a190303220b00d0a00035040414185030390181444c49031030141034070320031001119083d550f00f500518401c9500341d50520800c9514829680c0c4075003a0114006c03c024080c28450034805107540183d041003180341c0025001003290001c0100500c2a035017041d0486004003004111840e0460700001d50704010041022041c8003041c5107942030714201904d02e064850400100c56501c001c4d40980d0300b94844508020306044040450a0261107000a00c0310300340020034054186204551000c0d0315901003003240e84084603035680d41d0031130f43c04400a66242080400040c1d0441e00c1340c1c001d40e11b024400d00a00081d0310215200c0400c6d18440010750030141004004009045140f00040d050b2040c821480426502d21100071821400307464108100ca06068a41d81 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 402030917 1250 402029667 402029671
    0x60c070816122c21010203070818010501051f030e061503120903070501050d0e071721250507030f03140a020a080711040504060e0d081006030c021006080312 69
    0x492400f01d0703c0e00018944041482030b10000308070341c031039000d82d410645454a4216400c1605030340d8800300c02c0200494000800038051030701e15042d060500d03104002035007a40d4007400740d10780020f10541c0d01070880c01ca002c1c403088459940d09010604074000a07200f40741c408121030740c0d54040c110307110006007810f050006204060340c0885c803070f1401c4809008a641d5038864030640d4100440001d283c034840d80140d04c141c543d801d18600790360744941d68045540e200c58003041c852407280101440121441259102030040c000a10700c0c80b41440798540c4440c440c0400110080075481305140c440e400100c0500282c07003c2e600c1184480354249145c24020107820201d20301050f543c0f0300304000c0ca4100d0b00000d84228903548070304090350710121032500260b81e1144080064005007003c0612040217015006840101c170290704450009081d44011542e041c0d00b07650960311508848418084030307109421030b203003003c141d00481d00c154104d49041e804803003090307220300602c0c0c0002c100e10202c0802404241d0b = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 402032167 1250 402030917 402030947
    0x11011b0e09010806010522050a0501050a060c050601050f0307120b0907120807080307031812030c05120f04020a0e0c0d0b01090815071b05070801050a060305060c07081612 75
    0x407103250b0400320500c0e61204117003e4148911003640066182c40904040800c4e203007207140080c00141030105058001e0308082c00703164400c06040b00007081031481f884004c40519045401400300d41d00c1d01c03041c422040000a81c0c00d415008840c000302d055690b40452170a501d208015607103151170301c940441c1c01c240e80d940100c456001e0100c41e00010a80e000c060350307511030b04541c00ba55251140101a0010640c54030301d902c1c5c0310b506035402820b200e02d0300802c41200205440c14800c9182c800b50403512840b8200d5625014500d07507002c100f1280000526039800b80c800707085040003607200c0e009421a5001158002e104e69400120320300c041c845400340c01514042030901684250806201035240e0031214a00c80d4120107030000104001c0c80b4043d0030410003054038003030b0406a51420801d0311203107140540d252543c02c200108100e0015071041004490304400540000d172542d130812450343d80018025a0800c1c020301c00c407032034000010003041e2054030560401b98003000303409014102880724080c0e4 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 402033417 1250 402032167 402032179
    0xb040e04170309030711040212070c020406080f0a0636050f0102030705090105070c05100203040e0f0717310b0a0c05030a0902031005090120070201020a060c11011b0e 73
    0xf00c1440080001682c503142d134002001070f40d050542e8040380081c0610700d01c80d4075400b00b06c802d22004c10740010125065a00980d01804480d44442034a44e81da5190714000d00e040e070005c1e0b1404042142c03035021000c0b1401c01c1038810003124000f00580044008442c14402c110040c100c00002c10604000e01021070b110b0b44003c0d41507207000c0c0c002404a02911202c01d05002000600c80c003000802c03140132010b03050040050f040c00d005440300a690780c00a0041e20550400840800d04146004a1151160074182e4801c02a18000303c0c0c09100b598002d842c0f40f24020180c03100407000b500c8400c02e1803401c96100b035101d061200a091513100c2c0d51018002205c141d26141c0a0541154441c0440368440711240011072040071a1000c030340f52070604101d403041c040c5000240304030400306400249042c81c03000304012800e0014275102c50320348142030000380543c2c04812460006216600500080da450342442008221412000b90035580351082c6922601d00d281078010089800c01d048d089010025200c0c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 402034667 1250 402033417 402033421
    0x70f0801060503181f05061c1101030905031201120308010e061e06040b12160801120303150305030a0e010306140a03060b030f0d0e0913110111070b040e041703 70
    0x40d080340300c05060070b4003281513040884041d007000c05c90400c124500121a0100481c90b84403070004040a480461142d890b183c081c20b00c403490300811014968121012064080090006400030100d00b06c0441c0c146c0424403501c0d10030300348000000e008081a2003644012807641c03034010003841050308041e103c03410f03240520401da10380c2d496213054002854900140380e40e06000041a40c021503002038580007000885c11140245803440501401d41d01100fa281085420300644180c0700074081c50545c5903680c606180402c2c4a42c10071a40364050307072454505075803a07880b00d50960740091150800324a11a034040d6844d41e152060758010444401030508582c076000c001074bc07020030742c1300103000c41c4e80300c140000c001e5a0600022840c600300604640124003040e0000d4400e0346030185840c4203404087c0019800500c1000701c1c4210341e806200e1944103160900151098400c100c041443c5104880b4081070703c00e13042005001400082184003854581172800034201c0c0d412400310100d0020030300c1 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 402035917 1250 402034667 402034679
    0xa15020c2110111e1312020d121e020114010b13050d1106211b04060c1a010801020c0c0301090804180b04060e0118050f130303060902040e070f0801 65
    0x81c2c03010450300c030300800b203600210500300001a02a8040ba0420704480f425a1850310240b40010710088810454205219a82e031102178020010200082d42180c243c81134400028000040341140055504181e200b40140c0c0103c0f0040030034480303400d07005d030390340f115038840d007900e01c4a605004152014a00c5e142c04001c0552050480d0144030700340c003401c41200840e04202d914101c8109100000c1c10458482c928030f9900501c50f081074600840e16001d940101c1d0b910036a031030344604640b80100c02c1601d03203441d200003104d01506056058803454600c064081c03240c940e450070903000f03240707035400903131a107002c110700605024005510500c01d0380340c0454580010000700a40e0300322040703203506c03504610182003020042c00aa200c955402481c000c1e01040c26040008124107803010701c41091415000242100112401500d208020030440c80000e180031900824a203111031080c640401d005950318990000c0e600507420104c1d402900b03804000d40309900c0b0f602441c400005142c95102545424 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 402037167 1250 402035917 402035923
    0xc0d0201050a0c1106190f050403321203060a080601120b1b0703081e06130b01020c0301020c011406010c1110050403140703020f0609010e040b0a15020c21 68
    0x11000d0b030501c50302070404002e02404c9054070528a02c0035140d641d4403c0081501c5040c01030000d1364002103400c0038908584688540180c0e01601d920250403051207480d6040c040381881d1135601c0005101038410010219481031025240798030300700c0c800319201e0030507200300b1138448600e401c0720b5615440741004000014140c440c09801c19004010300c0e01035286c100d00084a4800402070241c00140040e40c81c0406a00a8650f0321804501d40a0b560051407201846804101a240c0c02d911480d003a408110000050307100803980e00c414011104010380c507002080c2640c00c140d44800c030996481200e030710303289400c082196001000f440c0c9202c8003170407580d030103120301d040d2010b1600804414000104039801042160044c42d0000880000707400c0c01d101c0741e9a520018041207000d410400c088424604000c0b06403508000143c617140212400e8200380070090810211076917021451400c000b41950002c0f0f000844421168007500480001c03d09108030000c05a2034101e460048000c41e0110000c04 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 402038417 1250 402037167 402037177
    0x1009080c1b03072c130b091c0905010e040c0203220e0106030c020618070f08030a0e0a141c0803131a040209010302060307090b0f0d150807030b04060212010905090c0d020105 76
    0x280c1c02c502c810b171104043d1000311403004100a003183c465205210136108000780d60f40c040100c0414100e0300a007162030032a185c120340d05c90f090100380c4c1c07090140624981a0407840098051f40304036420811040e10026410415242d80ca00a1140d10070512080500d41840c07400741610782410700200350078210003961200e0052070002006106448001150814010b0300020402d0300c00c64170207191107401c030b9501c80e440000c2c140080350806140c0002c07401c03c1603801c0b08550840c1e5003284503080b010181303c01da5030401710303000002c1070a4480e20009803900000d58041c1c1e01800180d400e040b41840c10401c40c2c01c2e07010865a1700b4030741108000050b61500002415640d05075034890712615009802d0f150034103d5000b0062465012071801d4010701e03a0b10250400303550280b010b00c441c0d1282c02d0310084445503409110301c1c039000700304103001150901214540041c803c010062030089403103482c052190b001e03005a0084e40c2c46105020040783e08100b0382203000001c584440ea68002640040e00b24030034 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 402039667 1250 402038417 402038489
    0x50f01060e0909120a052208071401030603060606090326030403051803060403180506031005010f1b0b011a16030e01090503011407140406021009080c1b0307 69
    0x40c2c6400644090400d200184101c58000591921454103460240543e0070014810028143c0c441380181307a2004035683c9011200c0c44d40c050024a03092510f400c1c0c2e000201001c2d18181912190000b00103150b41c4101c1c0700034003007a910a0101421450850398a00044501002c964034042050b00301000d05000c41b41c12079030500b440e6980c4c0242c100003ca040c03030030344205541030040f00d08010606400a907044034206560400540843d110001c002090005132a82c80c100075002e05c0a04c00c0d540100801c01844201d07080c1480c80d810468000c07101c0c40d0b00c40c0c0d000c84244180c2e10042051032100d0040e5072a410f06010000e08000d448866150f0801c51402d0190802030094030304902a400780035098098100507009105118010390020410401503504500064422900125590009003624160344980d40a400300e0001685880080c2101c00c0055911881c01c00c50109201c0d0204201200e0407010145a03041c41c00c4e100416041100325400b030461000300040c0d005180344607116080020070 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 402040917 1250 402039667 402039679
    0x50106020f190218090606040606020a080405040b010c0804150e04020f07030309081309020c120405090103030804150203010e0411090c070602070f0f03050d0b041a010f020f1609050f01060e 83
    0x195000240728140c02c5025002c0960143c130904c4400f59021aa031403103050107403018000716541c0d0f4412030b61688014006089800107010500c81480e0036007240102810500d08006004d12540b92294a507106501c800e0180520041144140d904080d00402e0150111001c50403c081040c0400c040c0c420214000d0070140d94842040805c00d43c4420703a80c0c08082522078040c03a0781c540c44480e009600170340f125580d5200360301a0f07484001d42d6004850036104042d0004420307901e5a50180da461402900c2258001c0c0c0c0107110745c41c070340650b2010398000c2160740039042c0c15003890b00b00414599103886980380504000d00402c581c000e80c401c12103181d02c3d44000010307a03503a241c0c14209038250f0f108100030800d40d01170181000b03041d8404060001503008131010040e00c04014100400c071400c100749030417a95100346011460758003513450a0703030b01c01423801039036100c621550240d82000aaa020040034182e8150700f800702c949240f1550354004441d13051003406504000010384090380300d80b02644546 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 402042167 1250 402040917 402040963
    0x150f180705011d04060b040909020102160515031305010207030e0108070212180d020a09090b0109020703120e0a120503271009020d080f030f060d0f030f02191203050106020f 76
    0x18686a018000400021b80f01a4450b42ca5000450160501710010b0340188141450020b00300c072100400e02c00c80380020802c800082500303002e68165000280303a20000c80c0d0103045035000c03078828001050b6080c0701e551540207540c0c0c800005400082e001d080001150310401001070780904400488520b0703843c20501c800a00f421307200103104807000740d100030340086032035a0019131800d141d005241c1d40344c440c1e0550303c220303a2224001d400b203000c1d00c400600064001025800800030f10341c40503120b03014040a50701e0320709140c0c540e648400141401d0200140300001000700b204200d074a9046045000401e103080c011001c051a940d034000500e68101c2d6903569110101150383d80160110030030781c00786285840d51302c080840000c07070300704580300f40d0442a104005151b600d000030f42d840440398015001d101c1c02243c0d803021034403550001418400d61080081150003214040c12100c1c4051041e020203621610180000341500c0301a030081055501c1822003038030824004c51455a901810f5030142c07004 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 402043417 1250 402042167 402042169
    0x230a0b0f060f041d0d020a0308010e0c0d140103200d14070f1517070203220f03080904140118020d1107050d02330405150f180705011d 59
    0x400440b0421a8018540410f4820304450320303140b04880b285041c15101c0d1010b51340c1040e622014070820080000e84042e0043c050302107840d070440e4003c500b44840c2c3e0b0130702c05507070f4540c0f003200c20b02c240306a1000340c0301c07004100700605002c42c0c4070407031501c002b1880142102c03c0860390010100c20000c006511140c5481b00c00102009800010100ac0c60700001c0181d40342108844ca440240c28080011603402840e03007490b002600e298002c8586074000d51a08417122800242040782c0550180c1086121000280d6480010f804c0310285010360303510b40c0e03580e03c48000c00003100c450b80c001604003844c1d0401000a40d96a4182070710001d501d000250795042280c0c1020001c0c100d4949065000e50040f90003000c2c0b100010380d401c0304c030380c042d005c50307818102c01030010240c0300307070710f407500e40002611440510085444040a50818400d00484125100024480128010480d42411203c0c01c08080000004040a000755503119041c003411559040200003401003080e81c241603061919021b00c5559 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 402044667 1250 402043417 402043429
    0x903031b030702090117060c030c0f0307030b130609060806040c0302100c0c030b061305061005090a090903080405120319091b0f080f07050d06050408070c03230a0b0f06 74
    0xc2c070340d0f00620105896840d480c40c4c810030701c0501c0f940c2c0a41c0c0301c2c1400040c4d492241400700d03800b601503010041d0600040030721014803540024100001c01d9218100038803a03450740500000c41d04c0b00550040f40340307410020040229010303540300c0d40340f50f0b00c001c0c288004140b0f0704101c601a650151882c0458145964040c3c41c030071b402c1040181111441c9a000042c0b103440040a80181c4041f50100456011f030030058059a200380c1b030807035100704141040d58140307004200421124401900b5100120b9482458904503900d003801580800c64840c104400c01000b88401480042076855480c01d60400840740342c00e102c0402d506054865a1b000b01001b4845070a000e00b480180140b5440e4460b42c035005802181d45a920581d107071480740c69151220302e80041041800d4480c00b6190040c0c420340c03500c0310409088043c0c01036542140821803440440c0000304003074040c43c010348084080420400b2494a044001004218260085182040011004c1c00c2a035000b4110780000c3c0b190b42c45d81d00000304 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 402045917 1250 402044667 402044677
    0x1908030f1003080406030b1e0306190e0105010906150206090316060b0924040e0c0607060b15071109040308040f02031c030e0601170604120507021005120a020903031b03 74
    0xe0f030200031a0000f042a41b5070008101107006131160703160002e50f407209000415010160f90741c16002a800242030451700c0851815640301c1110118104940b0145c140c2111002c0c0c1095503510b80340d40052110210080340c00a503a5403501c010442840c2c00a00c8541307070b000e41c1c03a00000071000c800000f0300744501030300201c032491030003040203000b81000302140039014284844440030041428414001e031419200d410000040c00c005401c21042680c03c00c80035a1100e041211260383c2c0f2000f91003652114141c0300442410000340990b100030508041401800048183d032095806004000000e603201c215203400c2680400d025004040741c1c40042d090445042c641c07101541869481030301c01e0341c56080300c141c1c406990190381071662210540c2c0c2910b450040300181343d41c03090021230006880389042d00651001840d046040243c1a4001015240c4014035200020000301b01c407803030318000c4079046030481c1c0c000504501d009514008a600da014402c904014221078888009080d041441224 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 402047167 1250 402045917 402045923
    0xc07020604090903030f020f0a03110d05010f0603050901020f0d150e0705070c080109080f0c120706050403020f0a120c03030605040f140f06010806120307061d1908030f1003 76
    0x907215611108404001c242802e01603002030b00741061810304103150b108440300070700c9503d246454540030507401c2e0040e001403000d0001b9070030100f050000c0005c1c1442220701901030103010040d01c910780311004098940241ca000d03160f03441049005400d003440421203140d05200303072011030021050490034840032101d50151030403d88403000c0192440c0d0000c024503920b44104441110180c80b83c80e030908a450301d8400030803841701045100001c0008801070100b594078942254090384010b0b08244451300300c0b00003214900d0722801408100350b011f00c4150704c00203100000f8002c9102c51b40350072450340c581064100c10b100d04407420000345032190300510090710000d4014000711800d00304010061500b940c1c001c4c10f80c0030742004940c100280c3d08101d80218130594032400390740c480d0700420401d00e40e407440000f0588400c000300000104180600388045c14043e403800c203152074108100742400401d8005d880d50071041d02c1e0200010360030206498000e101a40c2d6400035985400e804a0b1201c1c183c0c0000d = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 402048417 1250 402047167 402047179
    0xe01030e060c041707052b0f03030f0c030b01141803061003050606090c07080912160e09030a0c14160b090109050603011805040501021c1d03070b0a050c0702 69
    0xa199034606005104662041c0b1030303920344041e04c5088039113444442c010a0b5014840c00c000b508030541c00443e003400504048568001c0c2100c035503800612400180b03044001c01d0716100380d40d01440b45445020614480c0b0705050218512480000306900c200046101e000c000c003041c248546195040391101c02c140190407038050741840204a0603d44d91840211490f01c541000504141050483d190007412826855420f10a4a590b40b648030b800c00b1418640144000b01050761100342003189281460700f49030302c0708040e03040c4486105000d00041201401d50f00030480110030795070001c0807549064000120130135180c40b402a10703003001040c3c0f05080c42134500700c00100701080450300400c00c04000340c90b4a14895582d04c01d00078580001d1240030a941c11640400b0381d1358020b82c01641d4424400c0000500e0514600349801300f400c520040501d00c0743c0d442084a00001c010b002c0694070002c5080110704000c0b01703540b03031030341d41100a01c8052119111804100b000e4140c5090700c1c60180c0c0100b603 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 402049667 1250 402048417 402048421
    0x250918230a18030203031618060f0e06071a0919200a0f0602160308161505010b090307050405090d0c0503040902030a05061e0102100c0c050601080a031e0f0e01030e06 73
    0xc001e5aa1b00155a1080d0031082117101c41c0f401409071140100c5040c81d040c2e1864070514100c0241e401d40506810711040c00080c010390816540d51100605149102d00540c1c040c0d41d945019540c8a01d00081c440c00090340203500c2c8081c807542800e80702e03003190382c03020703100b101031045520411b8108030350b49c41d454100c60510f0307010171031042c6809070310140c800907400c5540c9482ca40e0201c0d04100d0b040c0c40302900701242000710400907a000100c081c031207809000001031440300001e2030b03811150309038002400e40002248444092506202e414000d00045600340001e04165001300d44940121b4405001d108a1040306801c0000501c02c0c0d8000302201c2d1811501ca02e07081c100003015200c100c4010b80f10f01080d400d504c901c6000e00381d48194503001a8014a46900d85100c0500200500c000c10000d204030080c080300000e408014550290000b0006003000d0301184c50301602520b02181c02c008100694600820404d81c040502203041e1000c0c909000c2c481c0101c401a001041034410030401406000c003 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 402050917 1250 402049667 402049673
    0xd0b03060403110f060c031b0c07060201021b011103011401120510060e061c0510030606080a02040b0618060a050d0905010507020d030908040905250918230a18 70
    0x8800d424503100381c0c1c1510000340144d90000d1710740408503860000001c080c004615038511410344140844c060501040c60984e041054038a40340700ba504c40e00040c2e40004509010000491450b049961074030028824031446140d01c0c0d00a010501800b00281449046102140c1c890702080340b600440c08410003890400d02082511082d55002b0b800128120191211040c24440103d90186c00c0401100d00b55086240201000d007002a101249031000d003000880813030203a1180c01c0041014100810b805110b500c107001c150b420041e10380744075880a22001c4000d040500160340000411602540e85070395981e02601d141c0601e650302010140307808510420014158040c03030040850b0303000c9580420000100714280c1d00301610050010a09000c01c200000c943c0d04600e07001000e0140301200b20001d0250302e50400e40381c00081c4000380300c00d401007007009441150300c08000c0002e0424030548180d202801e6210500c07101020f401c0c01d0100025814104c2641308408110324001540a100c0b100c0c2 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 402052167 1250 402050917 402050927
    0x2120a0804050106061403040f020301110d050f010b0408030a050708040f0314070801110409050903040312021c03090b01030201230a05041d0402010f0f090e0a060602010b240d0b03060403 82
    0x29411900c0b03610700000400d440f03004070340d5031841044402d40d547c910350301c07580e4003480300710250b800300e0b0150749404903401c0701304ca454040d0038a0041d0a50004592500448030b1103020410303800b0044204003003000340700003540482140c00d070090304d007485d0380c0ea0001e61600305002d10070740e4020f010051401ea0040100540c5e01048000303000600100c0e50029203c80c0c1362801c130354482c036120aa800080000300807822407a004540d02c10b10280582e03050542d6234403080f0804604205650050b041040c0c02d0740b070740c0c0c054029501d04200350316081001c03c803255254140c0b00c1040c007029050001c1856042100c1c1007012030261114500f8035035036100c8451000c00360003508a4010340c4902043c400b008184000d0b10310b010380c80b0303580507510301e20f403855900803d84003035070029066010002c0b065008118076105110b414001e1000e035500182c880e00d440002400c56020064052103081c0380040c804890108210709a40d000c200c1e40f1941e5500d404008031801030600c22500c0d5058040c010810040c03503081 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 402053417 1250 402052167 402052171
    0x3010609151706150702150301170706021e1006090b0411030408180607050607020a020f1f03020d06080a050a022106130201121401060f090605030c0a02120a08 70
    0xe07100c030048020206006640300c0342c0d00da01c008074803070191002890790b140251080d000c181d443c0100d0381c5042d0040d0082940c0701740d203800c0d040503038000200400984003440c4100317a0780d4007108003814102c0c0c04c2c410000d496103031600c0043c800e20762114039040d900c0418445014481c0c1071200811200360760314a1b54002e440280c40c0948110b20f81301c540100e2003c40e804503481154851101481e0035a5440041c00d40e10402c0d00b001e400040034844000040d50070007000303000c0c4c40305800401030040144100407441c1c1c0c178002d0f05401944039030101610802c924850641c0f440442c00c0140e1149441c0812000606844e848041c3d1442052140b070240600440c94101e02d500076190310704000911444280144114030884000c1d520480003d001e0308012460300c000c05105260114000c10040e04040a1300e804130503030481540c3c4000100a03203a0045c45811101c46c5909000140514024024056000c01000f0398005040000d220307420b03130b01c04d0015505459106030556128004140300403e500e5003 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 402054667 1250 402053417 402053429
    0x61203032702150309010b0a03060603060f0b1008180a060203060301150e01060509060409090501020a08071112090613170c0105070209041103010e190b0a0c080c030c09030303010609 80
    0x141c40012140c002922807203601d10703900504020083e510030228101e0f107500040c8003200c25503a44065039074903583c4805200046024803000703d005030443c1807130340c00c0f100708201441440c2e2030444890304a1b01c076220030220f031042307508000544d40d484600141c0b903030b51803046982640c0203c0d03240d0307010071103180d02542c029002a002004480c1140401040040043c015080070452000c010840284108000e1035101c40c0070300f041c0e0a080d170710054442615801c03401121240d402140002140d9440500c5c0342d8044007924000c030b40818401401901c42c2c18400c0307107800d4107000203461400c5072960030407544201ca40b20984045165102d036465154500f0407484640c0340503680302e40e516903100744207890103180c00a004003c25180c56842400304101c49003216050f54031000d01d03103110b450601581203c100103141809403415107103071200b101d002c02000b003e07402c4e240140985102c0e9000c0c0032158404800e440c1a5a2501e60b5000d5400601442500940c184000000400e0040c0c2c07118000040b145 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 402055917 1250 402054667 402054701
    0x305010f0c030605060a02060103080f07330b0f0f040920010f1d011b0215090f1804060b030f1b18061f03060e0c0405120d020c1306120303 61
    0x41c0b65001c025030340c406e5420300c0d80180e0007400140041002c0a0040640740702464129151200e0340d903400040c1a90782941492800700540345540240a01020342c5482d220aa03042000c0011000041c0741400c405000500481d0200803002c0f00740c60302c1d440502803d42015030381d41c0d50f407818800700a448074010760707060000354642c2c01d0326031940c0100d5910840410450300b00800c070380c462004417000320b030440c00e210800300750810440140c0c45006a200d076481015480981c1c0380401d80602109956545903140501940b81400d5007000c054191503410681c440804542d81000100103460004420701941060140342000f48401003101c101043c0c16001340da440881c0a00b01c2198419201c040310400c0c0c000040240d400d0410064a0000060f1406410000b030700307d4840a188624150881d0b0442c40360314001801e01c6181360000610100d525118010710107140c107140029201c2c040f1180360b6004000800ca088102d5440b0741207078000d4254441206030385c01c0c2c68280100548044085601c0000c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 402057167 1250 402055917 402055919
    0x9180207110315061e060304200d1e0201090b040b040e0c0403050d0f0212121503070303170627040c080601060203090d061404030c060c050418020d060305010f0c0306 73
    0x802c01050345100c0d4141c110060700349580780020301059500000e00b5150072800d18190090366074914000c4d40c01280224181c001c4214501d40c0139142440b005200c2d4403607651245020300003010207900e40c584690154104200590510043e1400a5590000d80d041c40c07002c24003144140300d941c050400c681284040c030b900341d1180300d81d09a4034803e5000140445d0001440880303e18040c880b140e022070074903c11118103031000840c1e00c038517030031402002003401500c2d0180002d000b44680b00130840d0101710046c200d000e10f50b0b980900341001c0d0b408a488035510300d41c0003640a590718120001c0040c0c0b49665020000511710502c041c49004540441e1803104010b0041119500050f0550681d41075030000c61420b14000200803100810100c1100c9088e1105411155a101800c24a0281c1e00c203884001045c8880d280600644058490200070040240400c00450040c140d02c00e500526844e00103903281840090f0b42c000d0803198002820b00c2d82403914111056030140d01044900c1503d07a0204911 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 402058417 1250 402057167 402057169
    0xd022206050f0406030902030c0a090b0f0a15210606050324090105060d020c0d020a020907031506030903020f01050c19080c07080c0a140109060501140d0b06010918020711 75
    0x24003034241c4220180c181484240400c5000b0741c40b842c406c50008040b00c001281e010002188042260000d000554640501a40c541002c00010030f02d040201c0780c040c100f030300f4140590640b90a25030b00c0c2e003c0000f4004080325404414074012315080f02c1c40b40500070b084d25001c0240c40e43d4015103841154950402110540803041601c041401500130320b442503603403a03c0208040c070382054044d00300c450750070010302c80002e6003003001d99208071460700900b824040c14010000301100050002050500702500044002290110f04060b1049418001015000c90800703d2500c40e4104d1821919844c0074140010036031003d01030150500100c4902c0540707400f00a00b180c59000980c3c40419011040c0100f20000f840e41c1c01520701c03a61200c2c1155030303030fa415032520b448010300b004030700c0a1650744850f603c05000d128002d4501614110807064442074004c40030a4800300080c2025003048400d00100b0f43c940e10aa1461000703104014420711110f03140d4401c4002580180340440d1500e0047c1c500d0081 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 402059667 1250 402058417 402058427
    0x803010e010617040206030a0605060712170928062d060b0d1a130b01080a090816110d11030c0415120f08030405010903020105010608061509060d022206 67
    0x40c0811450303041184e4440d42e09214040e0400760426080a8807502d010030b26450341c8001d406030714010081e00004400c24003014004404007854605480d130040200320440307000052075000d455410704c14820540c24403048140104031400014507140c2071003500d2802060548045407080c405510300700b44124801d540004840c2079200322041401f0034003044000b196598082031414000c0c0e41090702c89902000000c40d8418100480030000366240c2032170010b1359101034581d51203c10b19204010440598550944501418010700050350621000382d04102019400c0d001d111000b130032000b040c43c5149400090b04040180d0a03009e84508a11a00c052500d40518840394900c003020802c0c0c42d0504454400c61241c3c202c0544d000c0e001da0f02d1550000c0c099200540c81640a100001980781d16031500a0a6072010780c804410840e6840c03e0241d2990b0318501c207a80c03031110700c0360740b03075105140c102040f100d0050880b81c1030880d2020840e200d020381610081c0101100980b0000100c43e00d44800f960 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 402060917 1250 402059667 402059687
    0x60c060f0705040f290a0507141b0910050a0821030606160f021003050f10060815030115080a140d120906180501060501030612021c0c030c030803010e0106 68
    0x211030f4032401c4d0308000c02000e09038288910344402c01c002ca000102e00c80c9032030442d03010a0031500000c20000300003080c03180100690820824110103412020401c40c0d2070020040940100d80c850b4107200080707244411640301080c02010041e0100d2410b42e03071507681c140c4170700b0019888035080b44040401d40c40403184400302c9204400003081c00b810b16000445081004c66800f00468410142d01201e00c0941d60310481c3c0302c0c000d44103035004145807421241c42c0b00170010143c0100409070300352030288101c2e500f10240e51381c080d40303020311070f101b61a1120009015024803460382103c9031420502050400020850380078403030003542e10300c400390fa00e0140300e0790758000c0401c120001004030340e50829850301c2d9042660443c1c080c0e40302003540c1000503414156841c400400b29144c0e95644c00801c160350305801a46c004081700740310000c0c1d004250f00411f242104070140700d400000004100820415003041d54000745403c04583e81001e0340741c0c60720314041e41c42800f48200700800b14000044913441207000c0c0d0 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 402062167 1250 402060917 402060929
    0x3110f03090d120504030b0a0b0a0e090c0111010f06150f020d0e010f0e1003060501030b0a0f03122705031204030f060b0a081506040c080c1602030c060c060f070504 72
    0x20b104051a6242c8003403075541c401d01481080400c11000010070044006030b4002c410301e290000c0c40d43c1041d000c110320030360f45900009009003000d00700649148045400078a0350303400e00700784018203010071425005002e96072211001a02d011004070b0318042c54007482c0340d01856a207880000703904026040e40e6441c00403d520700050820012001154490074400d036a074480340c01c0c0301c10090180b030000b85095414819000000359645d404103d0741d80d050048000014080e20361504003800c10f40707506d140e50f10901028140c004a40700c0448200d1040380c03030050803c40d040e021004101c00005504e005849841039034403070f11401440b024030110100031a01241d6000035a501785000031758a102c00f5000790110151301aa0142c0001200e0800707000596443c482120441c055142a100700800c0f00c480c3c0c4209010072509004002c080c5040c00d0031100103075640c14506240108920000e468150358400440e04003801141000700341000103440341c050901c1c40e4512045079180c1c141103407a80107900c690 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 402063417 1250 402062167 402062179
    0x908090301110d060e0f1b16030806030d03050903160f0506040c091103270f0d02011508160e0c070f080301061112040911040801061502060106021507050901031803110f0309 76
    0x845c1d0f00c20781a25404039441f0280131a142822a180301803030402c150900242c001c070f400002000494541481111020307c17660508100c01e00305002c0596981c09010103c506038104400c3e0141884010481b9540140d842400c0715014502803034030001da4803040c4203a0210714100401125100707102404d9070721030810001c2059003188032201031690500b0450803941d42d402041d0081094070300611a14029185035000425942005180c038084d05249903c2501e11b60031070f00d140b840c0e01c80c2d103030842e6007103c0c400303d08024562581035449a69124041c8000d14480c0c040e09c122040007006030240d41242e140f5215005402e02d44400f0640300e0b84039031440c0c003000134100818421500e46921100c00e0102000d00a8102510781e51034600719003040d040102800200401c805444d030f810040a40504210700c082c003143c18052903586101c0401401d414280403000c180306107981d00c642c0c03020710188001ea11200f01d241b503500b800350041c1c0c4044082d40c801d0042418550748900300104881e80305001a100b = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 402064667 1250 402063417 402063421
    0xc070303020d0221071b0203060f091006030c24120e010605030f0c1f020d050a0e0301021803010f09083007020615010c03020309040908090301110d060e0f 68
    0x4600a500040300c0d10b034403503803c1c84200305152000140c1103121164601c0c41d001e50605410140040d1300141d0050000c0740524080401600c0200b0020b8005022683c2c407102615400c1030b00d41080c8550800c0c42c0c40c0784c40c00000000b880400c00b2058111078221b40410300e2181c044545c1d80860252083d5203010440300c9a0405d45020135910801c40c845052000040041e102e00029081501e5030f07208003d00e1f408043d10700b4552a00345484074050311080399118040b98003072006503c402d507400180c01800f2003c1580c8080c1801503403075204824004008555804100b00c0c5640388100350391044d4080e40c80c1100c0c0280b48078036841800d81260b003025005080131440d407041c41e015038510740200c1c9a00e0051580c1d503a400b0081000d81e000340000c3c0c01502a602d008a0140e031103103c2507110f1810024003018440110707070080704642074101c05441c00306040d0698242187c05118952045415618210800d0100c064241c090283c403003a202080c401d140d5104003107079040350240c1d01003005640c0170380 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 402065917 1250 402064667 402064673
    0x30702011425060b030706180506030f041e0b040b0406141504020f12010f060219021e18010f06030b0a1518090906021206030d300e01020408150c07 65
    0x1c0082d901c92140d030001c02e14014980201e401c00030a68061400b00d60401145a03440314403203103090242c04107403029815481d1070860441c110502602c0a0805803003881c0050480e085890300c1101c05130480c0b482e1507181401e01d4100c14406c8110f40c00c0d40c03554030f0400c107030a1140d20416154011111400d280e5140a442c1080000950280401010440d010000c0b00c84242203090041c0c000c02c421400d0341c140d17a1500001038246002e101134514074142d148221401a41c0c3d0808061010b840c10701c1910f003c00c6100042541004950364048581442000000e0200039020703040e0103543c0d450341c052001496110501200c0262401540342141c8034030700f1440301c240305040c04a507005008040c0c501c040e0360b910310710302225845103041d0380160300058880441c201d40303840281c01000541c0140b00400c001c88005001d14103003401990341d480044502c801403600384428200707214050100b0415540c002002d02c5c000e601500c2191041e00407082800001c0c0000241c040c4204007502c52070345001015a = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 402067167 1250 402065917 402065977
    0x480307021e10110415050702180601050d0c0302160809030c12060703150b04120b0c0306030601031e05030d0501030308060a141c05010509010504030909181e050f0307020114 76
    0x3c4846414080c0c140000141e20381d4405401410000d00c0d22403075580d1003a0b00511203949128140711610075440b50074466940d030f04c0b100300c8440164100e00012003010409048010744a00004088480303e40c07110f100910400e03000510440760121b04a036000700384417050140100391907101c02400e030000030003d6400b601a400402030121090500d1902076212801c40b160364100d40c1140242161204c00001004445000150800e09100c003441c2140382c058002f82d40c031101404018280140c5410102c482440ca1070340100030341d4002d00750381d19050b10300541c3e001003009210030f03000514164003107851420403400203020795000b81d100800c101168010700c222800281c4880c194040846020004501c0a02c1842c0c090901c200c004245030a09080c000d00c40700f229000360314000d10700814078039650350354180780b000190b118100c0d82c184294684010f403001111752001d0000d001343c160468100700080020104240700340c803805c0f02e140a6800a900314040d41400c82c2031142d489803069030501d411 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 402068417 1250 402067167 402067181
    0xc020c060a0c020d0803070201050c0f0a03110f1c0c1701090b0112090803060f01110316060213030503030405010c0305150906030a05010f0e010e0105480307021e10 72
    0xd0920001c002d40350740c0070501650340628183c030491000f0003170001455081c02000d07044050005d00702d0401d005400c41d000288102200b0b0014155108603140e0710810b101d041d1021229040c44c180d455041035a0400c904494041078880c40e2440c10500c0603c05001d4110100b00241241ca403080581c02c1040790030041a81e18080741c1400340a0550b0804c85c41c290042100061083e4884da440382031520900183c034004030302c402d0500c0603207400441d1100700081558030403903800d100d024440d510307800c21200a100e501c120861042c20400c0100a00c2000001980260702c520001c005942078400c0840484405551040c101c5003465051192803504d001c803540c025100800344e903146010765440d2401c4503039410481030480d803181805407100c5801e02c108070881c0f407120001d102c2c91a0a4100309981c1d0406c91a00c40105019502101d20f4620b070280f0380c0498000b050501c1c0319008040c000d18144e042200c04000500c44c0f4030450146040e500d01581240a07100000c101a04407480140b02034100 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 402069667 1250 402068417 402068437
    0x4060305060d1a070c021012140c0f0f0c0a03030501030c0e0402090c0307030b0a23220509121c1107030f0806040f1a040e030313080d0605061201090f0c020c06 70
    0x100318405e40582e07500e0681030400d103002d8a030ba60b603144060310300c482a290700030366052070403502c0784c1085219440481201d540703030041444180ea46503c41e40000d04e0b0f0003000802c50302031107070501c9041055099404641602e00408031000920b0361002d00c60034440003110000e42080e03441021420500c0d116002c0c6411000e141404202504244007081521049c0d60000304420020244c4c5120194207400141401500340c5402c00c42078036441500e2010a00c0c1a40c0c00c01080e5200000b800422080c4802440388080e4890660b880812030044550450040c0b105054a45400c0442c9420750040c0d003101c4c1e000e07505440c0c03107410740c2c4c00000c00e42d5003400080c05150041d443c2d00301510884028443c0c880c0411000100303042d82d1400c101480304452180c1100d24031a8420424042000068440c0520312135000000aa5600418403001d0103442168465070b0408400710709485510000b5075982d058400c0400c0812105000950f001c0980344082e01000c050380000c40da080050903c08010103070404 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 402070917 1250 402069667 402069677
    0x27030c030f030f141008010e15070509090103060c2c010309031101060b0403050f031e210a090210080112060207020f03060c071b1401110705030303070504060305060d1a07 75
    0x20003c4030fa501628001e646800071441803204200c03010b0301c032004c2c5002503c010f1000300211300088200f00d544440070720325603941d055100700203400c00c1e115a0403540400c2d405004a115565a860a41c018012030580c400100d608642d51403012101d8842da410010340104082c0165144c040054005211104c03040d01042070f100c1d103c1c00600700c02d02544004000c54100595182d207075040140c00d0511606401100e0740041084d480b0f0800420701d1901c01e2030001c5800e035034034051100628801003410358141c56002d00402040318041d4160b000c0d074a4030303000356010801815a000220790b100d900340178030844500b4004600010443c3c030f50250410f81d10190020260810420000c0c0c03400c9011541000c08103c0000c94104000c245131030400002640d006d00da0800382002d51210501607581181c604001c450359220300726100c10400f40c4000d0402409803550b070b051945008120754824010700021900b820081060340c10a010500d014980080b001d540030944446624030b03000c4080c07c2c410401c8 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 402072167 1250 402070917 402070931
    0x30310031e0503040f030510050f06100c020415081014070c021c26041202040f0f0905031b06090c040e101503020906010507030c03030510030f0627030c030f03 70
    0x180100001c0000c0c145c00364207400028990720f4041d141c41004040c1340040307030070a028014000c214400380c5030402001c441018040c1c1d030309036044840515000c40650311606002c801c6040c2d05503c0044801d44464005880007283c51300c91920981d0214081d44410084410005000e0380c82101d0080c00c09100034144d03d04100022040042011408002d40e881c1d9070510f403d04e44081e0354160347d0321240c403a5148034101441e014244285820703054010703001d142c451006413800111a444980d20b000f81d4041001200118200141e07660020180004d400440071010008604001100d520400050005151039241d100c14407014001c02080303040c040c45102d441c82d0108010f809144000040004019425451801008854200a0b1000d4180041042a880440d170b0110848413040d8240c100440c490303e409980e42e0079112150702c00307011803102c1c40c090740400416811a1926002ca147c090b844808015007020b95216040c5009002c551807981e440000707409071131499081d102034280000c0301 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 402073417 1250 402072167 402072173
    0x3a060c0e031005130f0b06030105070219080310150c03020c0103200a02030f030a050a0c030507050909181f05090106060c140114090c041401061209081603050c01050108030310031e 79
    0x5c0070855000b02c481169101c10410241024440c0545c040d0310352004102c2c0400a00c40d61040d00f144001c040c1007810004001801c001e03000d03100100074034403200f01000850f18008020814000708404500500039004034001640c071a0280d01c28800710401040403050310100d20101d1070f03004406450942c0014008540942032110245124142160700451549407602024007195400e100c044141880c1c0014070000c90381c09019108070010030740380c00c4001d844040c1d861001d54121003140c10144150082d400c0c1e50080612144010180a1810304c00b076180c40140509848442c005c840c000b4041c00348038804541c48000b12400001c6900c000030301e42550715000c0103000740417203501c645944842003090950030107100e0703030881c0900e02c0d0f0040700360350420200820208003ea2444813040d200d00b803d40c01d120b40702080f0340d504121219011401c406e43d14000e0556040510011042e5103004000100c007c008412a03109541d100010742d442e034219900c4214040e880024101c0c1d0300c102412280c00 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 402074667 1250 402073417 402073433
    0x1a060625050f0d0215070806010503190608010c09050a0b0909130231140c070501061203081906050d151e02180607050c3a060c0e03100513 61
    0x111102c9540502040c0b000108060714182000c66001d8110114400300300420364892626904202c6c2460941d0b40c0f51540200a15103000c94103440885510b040b81c0000c0301041584a16284030341c540304c0d020002d0740c4500308040407036a4803030f050040000304980a00c619240500c0c07036228000403840c071030584a54000ca9650351851006400e20103090507041450500c00e400400400d205607000e0164940412002c103c046019100d044004804101d0108100c400e4120001401204900c03003881030706810002c00404040e25034641140d0b0490070075070f1a02c030310300800e0269a00686503000544043e540c1c142e21440c103c1841d00b001c0d640714441c0340448200480c60301a40310b4040d0161701d0700b0002442d01848010512000e2084504008400000700c001c6060707114004200e1301000300302c240c80240085008003804540c401c0080c41201c80500d140149844042406200108521801c0700010b480714103280548550581c0b01171b0b01e560f540101500180d03071208081c145101403030110342c0c80000b = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 402075917 1250 402074667 402074683
    0x111030a050a030f0504111201090503130501170c0708070f020d03030b0909071805040606122d020d11060c030d02030609060a0e0106030c0905060f071a06062505 71
    0x203500051440400f82d160148046a01400c2820401c505055450000649519054500800c60281400f41c150402c2d4000e121f100d4000d4181c90784c4240f61901c2d400d804180d030160070302140010440401c4101200e03800c40c8501c0505040c42e14080c820384480c8100c0e08802c0d0220f41c0c92001665080060b110708001c062a00d11030b0f01c001c11040d03800010000c100c4002000703202d041e4081a4200303c0240c0550079548000e001110000e8162140d090850241845801406032221110701960401010401c83c852250034070048a0000c825103016844500031070a0196000c1c07404040d08021030400445c11036000c800400386450b20125002103421508190070b14103c0c29404010808107040c0141d85c942e11050441e614200300d82409204400400103000e404101070750380c020111810f002da9000c0c03014240c024291519113000900060003544828000c0340c40b02020707440038108000348400907000d40030007880345061000203807001240c1011240410544250300800c2404140f041c01104 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 402077167 1250 402075917 402075937
    0xb10020102120f0712050606160c150201020f0f09120615130c021c0905061603030b1e04093f140403171207030b030706050c0a02010509011103 63
    0x542c550100040c00a052440105084000c410120421444540c030030b403107080c401280140020103458940100d000c501941c04c0c28142c0580c46150142444000c0b0500c90407201115040c10b01c02c0c0c4001412400d03405540c7c47c0030614070301409074050150460019098940e000f0701407240400c02c843c0b040349000c800756602c0c2c5480ca203212700300450b4104910110407500700e00305c05101d400c00356900203544500c01213600c13444000050560038040d104440c44402004014629174a4098034070a00c40700f030b280d0400440200e483e00c094051705003800341c04114503e0100c1e01071000070340300c0340c1071101078901d80b2812180300443c2d51908403208860412400c25448501a0ba5824901c10070500056000ca0310b411092140c01541000003100d001c0c1100c0540f81d001c1010b034813254209450141900900c480500c0e5080300200700859a41c1c168001040303031074210101e4107116075880f03055405108002c620462900101ca003840954003910042003e000e040c9050300c0c802102005113811504012010 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 402078417 1250 402077167 402077171
    0x1c020402071b150c0506010b0c0a0b010902120106030c08062106150a050117010b070c05210705060705070905220308010f060806090f0405010213030f02090901020403080307120b100201 81
    0x144010b5080f400c4441d40c240c01070a2042050b14a526100d1345c5102c140b241d441400e600103141d2a00794030912540030841e600c29101d1005585404185c0040d400c0445000700d801c3c0001d00005480d4828000c000b01c446190300e0380700e801e41303031130042c40750444103414507402c2c0c054283d51030107002300c040080d540f0522a00000c0c841b00580b0500300211540b141e0300c114104039404151030000308481c4070080c110f031a205090350340c0d07880c180307494840340301580d00c12039200b002c24101032003101406603110340085144054604864079101040203501074008040c2c01c540c4006828081607810754007103500084880300141c1030100c1c4884440c500f1103070341822400036405030010806080318001c480301030300d184e003000c119034940840481e011904c01000c0c80c0040c5c1628010405200e001e41c100e0b0310100040848034061904d90401a40350f0659020490040c41d40d0b10001394102e006200b910241c95211210b1441c5844280d01182c0b611800b0542c05603041d503d01c0e04050750341d0b6102020140b0300c442c0d000 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 402079667 1250 402078417 402078419
    0x10e01111c081008060106081329060405091f050417041814040f201903110405060105401403120a18030b07090302090a09021c020402071b 61
    0x41030654040340d4002c1c00d160b4005c90040c03080c036410110440d400405034201c401041030b1410880e00c0102c14869002034841615030321442000004001e9200e030f50145c905108540380e0038481c959032118074030180090125181c284141703c03c075422594126010b0741404040e0b03001100b0083c1264040d900004800601d03c00c108003078096405540418505004010300030301d8a43c841c02d04440895400034510010000000e120950004481050b500040e05070340b00c1080c4207001c0581e136206408140c50a4250503201c64a40c9400d015451140c441a56810b090400700e04040074030683ca009040d040d180c94818502c0c0341e007121a942030480e2004000c041c6810718102030001800c190781c0700c09009401105482c031050344900c0884602d659a45400c200c0d4801c1c0c002c204448108e907400080c000d100c20014842c07800e0b4401074000642c2e0007140c5040b84c0740ca410a1000440d07000d040c0007500410700706090300295500c0c0746060070150001d403003d480d00304660703150341503c030f4076000c994010012018 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 402080917 1250 402079667 402079681
    0x30109060212070906090303020606060a050c01050106260c180310020703030501030b060306040b0c0a020109051f0c050418020703051c0905070b0a02060a020711090c0717040302010e01111c08 84
    0x2400000300f0050401b80320503400c41c1c41c000e459200003450180542c20024402c040d01c0d201c0c0d000c0b5448101100300070031041d6140c040042900c524030022058a01c81107090f07806280d2050404c601030108031060515040801d6042096100d02c805543c2d8140601c10a014480d05207000610a0034801e40c0d0002e419811441d15000b01030014102500030351081003080002171001400541100c002d001c082c1c0c40f100098012800341c190910018802d004104200d16440ca00141c4010009800c441c00d002e1001c42640c212820b000c1c9114a0a001004140b4002c00c004164000c0903681e00a241c0305140840b03800c0da03c5100c0c1c0b01c001106e24203039a13810030201072000500965010300342011001e46440304100d0029a52440038000041050380024103804018240ca102066860090035003112850111396043c041d070401001a1003498209003141d502c07032003045c210340689a0584885c14038110130001110003010706900c1643d24800c0c5e107003210407100300c600e80403414080d9584420852078200 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 402082167 1250 402080917 402080927
    0x303050402181603050a1b0201060e011502210702060f090103050a02030c1b0a0507031a06060715050a09150207020f240a05040b03010b190e090c0903010906021207 72
    0x50140b14804014040354219202c88050f00c51040d00c1c1c042216140d0001c1c003001440704102c042d000c050083c01841003150190402c07030807a8080030b000105682c1c7c42280002800e480403071400140c020305d502d580c1d401300d90000c00714068460941c050030180b1075400309000d9400b003040c0d55891312000c1341001088da030600816510400d440030643c00c1d8140455503241030300a80425040b840000858400100401c008248a807a004421901c2c504d9030703420074034102812940b4111000d040280000c2090606200721140d49503c22a0046045c142c0601702c0001d09003d440c14514035150b44605000ca401c1d5016001e0046181a0040e996005841088402c080c403002c010b01605140c04240500c216090400e6030348405c4401c100c0d52410b502000726154481c98010619680c5c02000108801b1401005400818984540b8101e032070750f8140c040d80c42d10022025154040c402070000707170b0b1000303004029144141c00600080340711815645c0b0802aa0030007015608000c0c100c0c0f00704403945900c0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 402083417 1250 402082167 402082189
    0x207050d060e010b010c020a1a0c2d150f181225080412080d09050105010509010509090723121015080a0305090a2106110405011d01050c07030303050402 67
    0x2401c10f040c1c4400c0c0d135804100195118803c16030389d99034071b0031554103550004086605580080058500c0504d80b9450141c0207828480f207103000680b001c0301c0c030906010004da01c91407802215958400303640c41c10205400514000e02444040c1001c001c0c02403041004c02501d03168407418648aa2104d10483c0c10a5500790b642000d0000a40f01c070036660040384c09001100c085c1e0f0b06002c5004121040c40c2460780b26441121645a44036203001600024000c040d40103505a030022548402d00d03036a00d2042002a07201035071380540b01c0d0024179081200e805d40345d51414060311010080701100720104006003580031408410500c0303401100c1a0301e00c100700b901c01e250250320a11001c09001d8103003419548c2d108821503000b014060005500c1003555076005401e0024440524600d81014141c2444940c01e551142d08071141403d049a074050080008259000d540c03040e5180401c0b42c10301c903c1c2ca5000c0984904490600c03404100c0c5000404052001c40041c5020f03440c041550300381481404042e010b8 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 402084667 1250 402083417 402083419
    0x9040b090c030a0305180307030213060e1602060601030c0905061209070501050a0c03030b060f07051c0801120b040c0806090a0c05060a0c080918070c1a0405030306060a0207050d060e010b 82
    0x11100d54a00081e1708030041d0b611780c0c41e0120340d189140d045080420f10307103c6540c001a6100060264082c3e072185107800060070b40d41e00700891601d81d114006050040310b001110754015811010024072294803e502444400d909131910b17000d4250794102007036180d40905202d5114818030700400034100340820502005007400e2a150b440c14003a040e00614012640301d000b000c00d034403800140c1081e42c0d03c200790b501810861100310396034000d034a441a95104451050303040c114526568a14150053307922070b04903004009420814040c40e511020704400050084403c0d181e081c43c086400f400800000344a00040001481c140031541004040280144e01952140b28104840001164001c01c1c8984050f444141180c5131076180f0300085031045814014039600e0b0a000400058582c00f82d1f6040005000d40810031007040c0640d560201040100c901401c650710401c0231808a041c90030081060881900c1500e065a40320000900300c2d0070703404429a81c094880302e404c043c0c3c8100788590912800 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 402085917 1250 402084667 402084673
    0xe0f030307020105070308250c201f02030d0e0a1505011401080403050c0f01051f0f0501081306180308011706060f060f0f070c1205151509040b090c03 66
    0x1d6281d000911521840c0300080c2006014004600c44401045003c035002da10300b4481c2256208050004004c4000407000307507529582d01060307012004545884490b50003005d010400c4035200c182c5c1414a5080403188407046101c1001800a58006031085240d0342608801a1602d01040e06046420048413407100494034503000040000c410441807803a08803c00303007010a00d030b0b62a410252960301440c00030340c0c414001c55015140c288010b5019070711840c030b43d50710594000071104403061044c140d4015081e0310740c00040d09220542c06000802d510a40e00d90341c0d800c2280300d90380c0340402d0f07969618400c542221031020344810541c220b200603001d03044088061050000030415903070b8561000d0b280c64012000070890700450748490044038620a81030752080e540d01c080a803419146e50210109482103015034a001c110350110034030300007610f90031400070a0802d80001c00b0610700389015151b038030101000011503049444044565200e14011450a422481c08900d401c4c10700302c0c0d20100c0d5120350 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 402087167 1250 402085917 402085927
    0x30c030312131502070b07021002042d2102040516080402010f050d06080c0a0b0f041e05120102090102011b0f1413080a1b03020901031103010906020a0e0f0303 70
    0x407401500303a507001c00c030401c26445810050420048842c0303005400c18159000184000030b00c13500502d5103010760201e40c05c494081800301c000310100d014500450407008600303060040d21500b00c0c484810b1a444845021116569a00c1e514120003000c608080c55030182d009050305528007071069591001100c910040c4598174580c0040c06842c00404c02410312a52804c01501107220780b0654004400040d030030014240c6521003140d44d0440c1100e11480741520401c08180320440000351640440c801c1d2802d8101420a140340e042019401c4c918051900c86440002e070a07030b144202ea141e00316100f4001a9030328040b82c0024207440030f02d21040c0c1c4c61000c05004403080c686c07000c06442d0b070010b18900207480e20030b0420407001921525440120540e43c012002c5016200410315200562041c281e001c2d22016101c60802d582d0729a1001079400414640100085102c805d8619103881c0d0050000800c0c004a41c2c81000701c2c0c0046c548280051030302c0e144003815041030f21007040e240da002c4000398102 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 402088417 1250 402087167 402087187
    0x6020c06090604061b0602131410080c0d0902040501090605010e030d0203090105070f230610182f0d0606030e0c1c080c15060f0a03030807090302061305030c0303 71
    0x83d108601c20b400170030074908410141e40c400e4034108400c940e84910306650302c0c40d45950a882d40031260282c03200905200b201c811403890705084803041c09106440d0903505030b071001c0c800600303904009114800642c13140d0610005070ba80713105181c007801c14080c00044942c2803900041c45880c0a00d1034501a07170051002a4039a41c0002c2914404c910900e0180d603150014604207020381d454500007040b00c200242028400036602031941701a81e08041110303400d5480c4c8500349540b164512a03913500e20780e000d440c170741c02c0f6009400c03d021030b00d884801808200090070484825403035140c4401800c503401700d1041a03072651801280700512140c03605025030a0f20b500d120751200e46144080344500a460228404401c071038428030038454010002540300c0b149000040c4c2c5034040c03482c406070202040740001d141071500c00c01c5100126400b818010300345046583c00e460145000d08140c0520181c68030000043e0344e09001400c0101383c0d401c580700840e10b04030502d0300d04440c0d00146072298000f07103c04004 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 402089667 1250 402088417 402088429
    0x614060a020604170f070b1609060c02191701090c09060b0d02030402031204120c090606051207021204060306080f122d07030309020f01080603101e02040e0106020c0609 74
    0x1c1500062004d99100510440e8042c5101d0002c4086400402081c8030301480340008216205400d4004550b0321400401d0003181d1503a1940039035808500d055601c1d0b03000d81400c92803c0590200c8103482525a40c0742d007006940d007540107812402c0c0380e44695011040022480744440107086441c0140980d9050001e60441d40c080c48001c844002e5002c400101555010815030342c6c4c5e8905030000c03580da203459000c1d080c0c0300c1c001094180c1d0054503452001800c42a00d21400080700e0040e507560b0700b4800c00380b0091151400141080c42180311380101c028031008000010700c01840f003a14006000e83c03416040c5820045c203000075070a40c4d08409480c03074080480b042110b242000203450102c40c4060002e02c440007007541101800040c2c00410808101900755020400c40790003142c840e0712200d5680300469801900b114019015080b4841e00c503001c44260f00b2042c004c01c880d074116680c103007d0860560483c1c02a5120340c46420324040100701c40c40d0148600000a101600c000d450196480f0208117 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 402090917 1250 402089667 402089671
    0x9090a021f050d0b03010b0a1e0506030c040e0421090806010b03070c150204090617010506032a2e08130f0311010906110a090602010e1b030f010f0614060a0206 70
    0x18151384038104504241d170294084e03000b00100410030306413641c4940a803050060031584003c91504100300201d02460110160792103a05400c45080c906802c20102140089010300211070900a11a0070420210046020302080303007141d8651407041d20305041249401c0041e072100100f41c1e4100140f016040e88290440003054010711401e03045400251440009e100d55032100d9025854001d020070340301201088a2602ca404600a00054032070340205a01d0301b0301c007000786107075031403110304444805401d803d00a00418020480b24032500c05040003504d1440c80e41840c20001c0328811803102a980040113a5001629085258144600b075034520001800d01e075800b90a0103024800194864400d4011000d59a88220700b0700c880e00d9008200c1815800442400001c91501c6030301241c2d80d441446440580c0440c41c2c01031460f08041200c00280d443c88034006605030085a0440340e80303460902443c1007084441303100080749807500521942c030700c03415845103200703000400c40650944c1d800038001da = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 402092167 1250 402090917 402090937
    0x120216030c120c0b0a020309010905033f070b0a0516020a0f080c1c0305010503030906030a0e010902060a020303090d0e030a060b0a23130908040317070209090a021f05 73
    0x808407408a08028200c80d6144d44401e881c1d10000416284166020002d4501e03104280c0354000013a4a4404050300d5515204500e64010302030140d40c8000d400d5028030b070b24030701040d00b0411441c5c1410741c3c0110142e0710661007035645c3c201107010b0108000c07007442000d0313000c80d01c071480c5403c0000d03400c0029201d20292a01a0090110740c195106100c1002c0850b02c00c2c0880c1c40c2212455866280030301c010a13051018070380030134986400014035003804403c40d000150000e15040c038564501712280c2c0108031106642003103660325004040140c40301d900426075494290001c40d200c0c80c01d00e0100e850325140040d640b04100041402e558070303481c00106d2400d0305a000c4000310b041d41081c03021442c00740040e03225140c1802c4404860440760055a000c0c00300f0b20f0300340c5015150100702c038003441c19294500700003046034404001c10000324014501001808400650180c6441c185070002000c5950036202c44800d604421910821854100c58204030b28551100c000030082d90b0f410044c1c0309004a0b43c401c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 402093417 1250 402092167 402092189
    0x121080c07050d14210915091801090605010f140a14030a0c09051009060f02010b1302030a0b01031b14041203081b07120c02130504120216030c 63
    0x1000c241052140c00042d107006444070301842e010b402c102c0c40442d0600b04180d040d0081c10a1030412507034034044403007281102c040342031500c115032050041d80300b039440150320345080c203000c1460640e4400e007140c1c0340f01c002c0620301481541801404022a0011b52203c0e041c021b03500b01c2e40d0403d58221000c130458403070000c043c54a5039840d4005440701c3d1340d1982d40a100190000800c81600f41561205540e0030040c0e442200c403586820611004400c0900f060011880c5c3c0502001a280300d4440f0803041c0c0d42c0c0e80300119890944070003142070407211001406241e90088100002c02803148141c107502c240902e010300041540c0c5054007441074461400e0400c10405481001c01c0b41c414404480060100151214401e842400c004200d0301c0180d60902c000c004940d01044044602c4040d00c1d607051300642280b0b000341e103201c81034400e007900b0041203800c801c00140a0348652802c1c4120b41c4203078040c40d820340c00022044c0c8001e04003001e07401e60706c5078500301210074400305452400c29005d031030059000e = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 402094667 1250 402093417 402093427
    0x1e06040809120601090f060602060c030a020c0f07080c040f090b010b030901090512070201080c03041a15060705010605010206130b010e044e05090904020103110f04030b012108 77
    0x441e2a2440b0081c1180491086100010702600c10350700003024001c2082041100c0c1d5220740c0c1c00c90312200251800782a094041c00850490f00681c1d006146015100b0101c5804100741c1c40c105050400c00c0d031203003c25411513100342e086814070780208100c0700e41c0b805040160132800e9940d007080074418050601c0340c0002000041a0a0095101442d269000b01c100c4007658420410000541d00011080b4000b9841c1c0e4080f407007a20400341030f42d01a0b644140386401444500000901603d07004005100d03502900c0103c000302d888200040110364010000401d07640c0c1400c00291411038080e040c41301c04544040c046c40414070304e190031815031382240c1d1000e4481c0c41d1350800e00700c0b100d807142c420394000c0c8080301d00903040400c1c000910034180341101c9090024581070b00351032031107078a548841e02040c3e00304607000440c80c0450089620510506001800b14858031105640750400c41c5007141140000405106100134030400c41d0042c6040c40601d4091024445518a80c0c040c10704020180c001c0494 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 402095917 1250 402094667 402094669
    0x105031501120f15090c02031804110a05030403230d0513020a0f0e0a050402010e0d021206011d0a0b030d200616030e0a330f020c1e06040809 62
    0x42010544040c01c00d0160076169445000140b0004c20342a8001c03c524400107182101c50103800107008a5801440c01c3c055070f182d41200117900b8031001540181c0c1e820f100741c0c2c5621440050b02110280343e56164880c9810700c4d01400e4518501030005826200d1036841c3d440700b014501300c4c2e20340e841490300440c4d00d40312550f03030301520030581900942c0080e04650200b01c0941d2040708008880340e9901e01c0796140c5881e008101102d60948010340060b420b007286170540c0c2840c0400c000700610240c00303034500b00d00c04080b41c0c0c100780d000e0f00810160300000c00301040500800c091982c20800c01801003280e20a214006070751b45401390440010300c050040d00e10014a110300010601031212800d075003003442c10a540e100c200c00c101140c0c9012038948111a12200340000b401c1403011351041e05400503c80241d0101303001c450404151180c181e4032207070303001401601c0c0034150f1141c0f80e0303581c00b684502d00c11000a0a040c0b415282c220030303402c105040e0400050029015401030b401800d000e68941c0000 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 402097167 1250 402095917 402095927
    0x171614090307060c0203371b0b0a2a020607150f060501020f0303010b18060d11070b0a0b0d02011b1b030201080610020d03020306011b0b22020108061512040c080115050105031501 78
    0x1030882d1100700b04984001919009d0395004180b0403845d90340e00840d07402c08110300e8070a0383c0c0c900820100114000301d03000c01400c0c03140080503641c0c044c0d180600017441607076000050700c0d07844180c140b08907142c0b04104515601003080090700840c40700954155030400708415421b02036000e5144103604c5074401c8140549600307003119160311106005020f003d250010704003903940801070840300060450000b940c002014412050000e40040041c51940b009400464803c007420171011296032640003050000342114200300d506c010303919845801e441c0340d800054603942004044500440d941ca8040420a5000c51268014425030600686a4450000494001c5102d06080361042d000441001c103001801d9001032013420400c1040d60100500d004032144c4500760b5038002c1c0410750200115440740360490440080007201070310303982016040703010109040c00c2078a0968400287d50424484040c080c0543c2c81903c250716034400c945480d201c0002d155100003441c0b012028117180344880968490 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 402098417 1250 402097167 402097193
    0xc090f091802040f061d150103020f160201121a03060c0a17040302071d060307170c04020d110304080a0201140105010926100c171614090307060c020337 67
    0x110040d01c8410080780c4c2d5060011750166429a05003407e030001d0384480d03201c0d00031109070104102c24076082c518503040f08040041d00070400c9043c00071907448400f42d84414410303024020141aa01000c3e2580d03602070604201c00500806a000400c0148076502a0082081040c62080303100c125100d0f41d0700d041c200d00342010340d00301208100580d8001c2000c0038500c0041030141c1c41c00c1b0142c40400c4d946068034046541d4a9512180541204c41004014a0241d01034052a82e00840c003144c4018140d83c01c0b82c0541c012901100c0d1148046034054400b13a0912070b03d142e06002c0b103100c0c041941884000b9006d203d0318810654448031000e044c0064603081d454828030000140100c907220201088801c0c05000c4000200000034051300c01c41c0310110110541d603020710f203442c40020818200c6070b01215015410700c82d500f100c2c0000c01c0b00884949041007020010a01561100d66544c0d683c4101414002c5040e014298504004e070003036082c40050600241d5030981d1442d5a0040300240b0303040c0079000709 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 402099667 1250 402098417 402098429
    0x603100b03040323031f060831031e050405030a110d0515070f0309080a20030301031203050901090308060126041a0906131209090c090f091802040f06 66
    0xb13019090111012409140a60501d003120307000900315803100d440710340d114481c240000310030708041200481e00c20b1010268209050008152040b41d071450b0444a500030000c400041042c4502d003031800c6840068001034042d0b181180c130301481e0100282d5903240102c00a040f1408801e10007180340c3d0780c031404c8a04c06602809517000324080b21640303151407401311900404140380c2081480981e200780f041c42000b43d0b0010301d050030009011002c598040001205402c0c101c1a2000e204d103240e41003014500841c811100b18411010000d002000e840340500648082e81c181070555001903041825564070203420703e81410002003c0040440b20340b178050350b21501072000028082480a002d544003540c0902c8045d510054030b0380010b0541c1d45100310703411228411070504090004032400c02e01d100c4200b445c40c0100d009920707403810108a9040441c0365000c2058207a0030810749818540610003441c403c0810402034800010070b03680008500d20081c070403580d80c941c2e070301d0440d022345c440f001a1107 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 402100917 1250 402099667 402099707
    0x201030c03020702130b030712082a0709050901110a0c0b0606040f0f051c0f1104060306061e0503070501020c09060301020c060403020a0302160f0b0a0e03060a02180603100b030403 79
    0x8170780d51034900280550f4140740d0190242202c04030341088a03144a5020550010300a450040510015280a5861011114018030016480e554080300b00100d2020307040c0a40001f841d414210280b90855250196107640c01c50148060324000707070842c03190780541d60000c0c42802c0d1aa14500080d00320b10564100c0422410f0350030300400c40042845a840c2500c0068031a003605001d244802506000e03540d00c004d00c2090003043d660f0010350003400d902441c44000d40082a1180c483d030340c4a00703681c1d007500012108400da03260350801c000120f0000d00100800d601401540c3e08180c0002c4d100d1a049900c24010100701020075940e481c03d5045405070f06c0070328240c9505041c40d1400030346807801101e0a90052040103842090b0581502050741122403030303c0e458800720300d0f01c5440861900815009014000744d400286c2281d141070240c0e074884d80d05460010790b13405d90180160440075002075041c2c092a018020003903c55050100d910560310f403180e0180e00d960b03d45ca0100c1714040300c0c441c0058554 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 402102167 1250 402100917 402100939
    0x1b0a0f0605090409060c050c060f132003060a0c180e061909050403020102130b0408030706111603080615090f1c050703060f05090604021509030705060c0f0705010c0f0201030c03020702 81
    0x199002000d41180c40040058030b01d40d465148107030a1020060302c117221b8001c0500e55040010318a10640b2082000cc2d004d0604241c4000300080d05000f02181da03600829100c03210000c40300c0e404022441010204051a2210381c14992403880910004014a00401d01c00c2c044000c40b01e50b030341c034410091003401c0042c000c074901494000d0203504264900d00401ea5620004914021a0402d880030307500c28600a50801100340c5603000a0254080e003004422010406100c4140c0030322050b00c201400b82e11360003c1030908000f0320104060000c1307160400002400550810b607100b260f43c0391007000c101d0b9480b81f81700410700c0f500c8050912420061040c413944c1400400c000340f540010007138808d0401c040243d50f56009265480300b004860007507004a5460a4125040c500e0024100902c800380c216014140ca40340422030643c0314260b400c50560040741c1e141d149000c10400c9002400c000e10b41003001c00301c41c0da15407103202810390000b8149901c846811611501ca035041d0ba842c107400401c020101 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 402103417 1250 402102167 402102191
    0x17090f0f030c0118120305060402090d030f1407020a120c0b0a020a0c0b090f0d1502071103100b240904090311010f0204050d06050604020c010504051b0a0f060509040906 74
    0xc2e88290440481c650030184850516111446054400b9800809800c400781103100114010200100310070741c025400d00c101e07003080d00c4556404000c1c520030f807100c0c546000d0304d40300642007040c00a80b250401340104402c000586800165008840005c0c0180e000380c500b0f031802000380d40842d00000c0015001284d9443c00c194005803c1c205503000f03188803924140c4a09100030340c1c0c0700b100002600800031000504250405040600c09140520f040f40d0402214507107250981c4d10807a01500c44034002c03140c100c03162500340000703100010b5841040000b054100c0200d070307803580038842c1460302c08800b000030066900782c81e0403915440e1005100f040b8000061401404110030030101540c55882c1403059200f881840c0308607001d91300020440800c82e5410741d5443c01034540104401c1e0803075004d01401045010074024203004900c68030240121094803104034006000300541c0314456180d4001c1000b00c0c0561420050564003a80b03401950f418a13203010402400090700018850351419000a0791 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 402104667 1250 402103417 402103423
    0x92205091b06030411130b0909010b0909070e070c05010f09030807030e12091e030a0f1202030301180b0321030118021c0b030a0b1302090a050717090f0f 67
    0x6000c1c582481103200030035000500025000c101d41c000c0506041d1141c0d000349207404d0403001420f214403c1c010854034801008295608410381e5020143c0e03444515540303240ca0b00c1d10019920240c1b401c0280149442c02d401c0c0c007800307000900f1510500030710140e0f0713105102c02900a80100c1e01050780c10b2011007281e2900030081070007124408000f80c0b41108045c60a00c0c085004261a401d802c00c01d403d001030034080007401c0d00c40019240d500e130480d10051405480a00c00240c0740d6000d03140710a1401102d0504100e19555602960b0071034004100500c00114040342c41140301c20b0216000403c01c841d14086880d0003d101c0071105001003180c242262070000c1c400031070680d5001142407942000445d111000da00621254540c0441c25150021645003039074010070904c100142190001e0449441d1401b000b8410303146804060b200100311010740c1403441a180d0401e405038800c002c1c92400c0800241004446101041c00604081c0810304201703081148004800c00d83d8252200300740040c80c0187c0e = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 402105917 1250 402104667 402104683
    0x513120b150105030424020d150303021207080d0f020c030c013606022104030f03152403020408030d050a0b0102060c12070504031e020414090309220509 67
    0x206509a800d0040240d5120f00b0a5a014a41c4028204941d581403600500c102600d90020345165500744401c1c0600c0352030f40a40d0400d400c040c24124660b50035030500a0400c0b4249164081da00b008010283c0043c441c3d40440784010403030880020103100d2900108080c0c4036892200540e4800410441c1c0585019442070210680309008140c0040917041c0c00301c075451003038a4646007200814401c0e404509550000c006100b00d40c246070180d12040380b41c59241c135400350b400341c3c001440b085098011940501c5904200344000c0b40d58140b091404445480c0b074005401c1c0d051a40c2203924489006074040d406880c0508401c5090341d46030030030b2a150900921040301d8500401d401c00380e041d023080d40081003141c020682403011500e0318440c3c01c90411460000707411481081800c000010100340450394070312440702d040850504200081c0100400c0c0c4142c01d0f26645021100800e001004900008440980d8416107c0b141c982c0315807200055514503a10310740340503d00700f0080103c010404034030700d0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 402107167 1250 402105917 402105931
    0x12080606040b040605031f0f030318080a15050c120a0c090e18060f060906060a090e01260708071509030b0c0406020d110705010813020d1b050d11010513120b 69
    0x160303404131400a408414007640c823070800c410510002c28030120f4071583e18080c0320030503058400d0000e503940b809545070441e5031a0917034400d5405508150201040e000340ca81254480180b18204240004214140e0700f000d00844505555540288138240c001d8540200030003c60044d65941e2400300b48604174204c010142c05c03650701806000520041001c25280c0c01400e02514203072040e82c66905219180c3d0003401a8000d003e150003000440341e0030010341c240a0b1202e6007041580200218543c10300c10151a075030421908190810703c05400005084001c94148204441c03105c06070850540b8160310903000680041c150030100110600c100340244115482035003217500c002c0d052300f8121486684841c8402003900440000c05c0076612400b096034020541c41700d6200180e01550020b0905410114101c42545094401b600e184010000c90401814155a544000e10031075032162448050b030804941441004541000c0c0e0084034180400031f0b120780c4140902641709428410742144048a0700 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 402108417 1250 402107167 402107191
    0xc05010614031e0309090910050a0c0305010e040308040201080c0906040305010603170f18220504020f0a0608011502030c070605090306130213270c0807060201060312080606040b04060503 82
    0x82d01103d40300f040c00b4580d507545440a18107000580c001c02078203840242441d41244111583c810004d05a441614000e0302100000103141d442c5010207003d03641c05070f0011503941d030501c0400c40460307007140026038016424030303005550b40d541481d1300016001c3d0105080d0072410108012040003015804201604d02031207110600e00300b2800509000c9c0705254031100102001d10034a0680c01d01c5c43c0441d60600b43c01050786110a100f00e03080d0302d0749090441d00003102a11182440154146040010401300b03064803500040781c00d025010748440b00620800d8400803400000843c114400d00035540c070308481030b00b034a00c6250384001c020300c55040445258400d000b1000840c03604c04011584000d00f61f8041d140c4240019049511801840419500b070348054109612400c8007510140548a0910a02c017001c045800e0140d2203290090b1a0440025a8900713134040c000701340811490700c03880e10580381c480401e5550102107500c60091b6803040d00c1c104c0c004540442d00a8025019501c6510b940c004 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 402109667 1250 402108417 402108433
    0x203060a0203090d030b0409080d020306090609011202010c060e070e040605070513030b1504020c030c1e0c09091c0f03051b2a030304050a02091302011e0c0501061403 73
    0xd000c030b00c000d4a0f010069031000a50584041c001c2d0009031820500900010380045c0c647c03183d01241e417107040b06511059000040140038540710402c150040d500f91510310380c80d0b0404d04250210403c1420180c14031409809560820125070403c1c00060100000d40d80c0b0b595556800a09141d01a94100c0c0e125007031500003100548554103403200307a03203aa00c0702c0d00b81c103245841d1854045c1014141c001d20383c4148805603d291181d0009141040e103030401140d6a841752640c46e4101034404d01d240c03070b110101c0c06964102c001c0000306a18810300c122040001c0b501d50055503407401c0d60070000102d00e00e01d0200c000410307076000308500300480d1280e03c0c20b001c0ea6541018031080e2a04450341600c0030700e014801c00340e0031a140d00c0a490f1002ca02c04021000202c0c0307412040c51030b0402c8134101c0e02d9500017250002103040882c012508081041450001c00341181c0c0041c000d80c1110003091030900716001c5d218040c0c3d122740084103203590000000c2002a85601c4210100710354034940324024803600c00 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 402110917 1250 402109667 402109681
    0x30f01090b0307270e0d0f1706100c060908090406140306040818040906020310120503030f2203030e0d0903030e0f0a030b0a02090f09070e040905030d090f020306 71
    0x1a4001c0c046008002e460407604101542d46916034060400c00c40101c2e030301d2281485400c44c402d00140750401001001011030004005108000b10362014040041d6980e00882584803001101c1e04003900721401507109804c0c42044030841011701025004a003807103d8001441465001420359443c180d03030a001c0161154407041e01c0322201211203405501c0000040c01140341c04015210a020005035854901c00d5407000506032486180180c074519400410701c5000e028996150000f007000ca80c681c0b940d00c88507280d298503400000d0204034000d4039040090341c040c0303007500410103414041d00c0a564001d40341c01c0003030040011442e454000e1044000103440c3c54011842e07e4200ca40c0342e69440c400110034411310500e29800302207103030801d0006c2c101100140e001040c4501c1601040001a1581244010032034401180c1a520b0b0091066006010340340e603001d11041d80202d400c0e00d010408007681d2428a1a40c0310316000413141c01d11b005818005c11061400b05003c02c0c0c0210121000c54807856 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 402112167 1250 402110917 402110921
    0x935030402011e020c0d0305030a06090506010903060b0f0924120712050a0b0103030203130902090d02090712020a0504060e19051207080106060c0510050105010503151f05030f0109 79
    0x5a03020340410b00801c00038203944036001c2c600702400400c0c41902e2841000001040c030743e0310316040c00c40200d000401003200c450014400c44000f803260000038401d5040001c0040e00da51218000900240d458005180158942015041604102400350b40300c41c034058400410050340341c01110140750220300d0030340d1903150024001d030042c003c0c4005440c030140fa01c10401b040410042085961340605103c1c140401d1070400694000c40c001d4024565402c188580310b40c00031615004451103900c184646040e940b10010b0098100342d0684e034924840d11091004e9500310003841d013010300c80b0f000052000c125507001024104640307464803480c0110106030b003001410a11f00ca031b1202581c8071504104881d1038440b480c2030b04000d585041c5c40140703403a404c0080c25900755400844c0865880d4400c03c0c10030400300690304281030080d80400655060000080652002505507404552203800380780b070b51380e250307101d81552074091101004001f0b115200030b00a504112411000709071940000a1424994 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 402113417 1250 402112167 402112171
    0x1c06090e07030305190e090903370e04020903010e0d0f0806060f070f08031003030e011106061005040503010f0f0b0324070908060711100209010206010b0c01093503 72
    0x3d901c0b0203051010868811071611805000c550400461341e13012510b548a18500c5402108040302841e5103020404040f026401d000e204100c611a611100807030007400100d01c511000d00e245407a0781c4840d0400c000502a0160f808529450b51030310b10011042440021201d0340108140c49811001e100381d40b040d9903070001140c1d069000343c000c104a00c00340a04c0380090000d01c0c800d81d02c0c43c800d06442d450b002400c4c0c000700c542c6041030550410500900d600001400550b0509184ca4034603034000c07120b0261503480240007140608080d51500003401d02071002e580150001600030001440240306403c0600010380c100303800249000101c80f110304000c00d980c4030410b40c008100720304120550f22603a5861004100100700000307403001061200d004d0103854012046503445c2d400b443c1e0700f641034505000e030b110190300c902441000f03203180c140d0300410b4850448191280e0240c4a8401c07890681c090480480001d0958198029502000200300d01e035800c0200c02c0c1a60390308071071094040045a01c02 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 402114667 1250 402113417 402113423
    0x303110102090f0f0a1d0103030306090903020a0308100b070501020301170a05030f030a090b040506090d050301051011030c01150f0603062d050603011202011106040b0412051c06090e0703 82
    0x51400b00c060f1400c0013129400c914070040c240c0021203981e282c0703500c526424407214514480b03488004000703069140c0140c1c40a859900410040170506a40203990751003c004002d0a01460f000041d08442c0b801840000078500f0003e5a40d0342c030803500e4400d000f51700c240541b0700408104480d1840d42e02000600c800a0741c0d0120003107141c220481c1c020070650700000e00110a07192140d051500003007040c2c000c14081d511640081100e41042e81c2a01d050108a040b01030400c0b009200402080d611030843d48510301444c1008000350505940c01c41c21885030b045001c1c03c1c2d41c20103848003515000c4500600c119024204010840c903115207040381958110f01c100010030b1102c00301c00b004104201640080317920703d0742880c0030b1142e9541c0401e80031b4000740d211400444105c11041c0c19540c005d440001031070504009486a0b150650340c002015101600c007600d440b40340024a0780d003600801c05c41c0c090189107071480d4042120136048a000d0016801840c150a00704422010b1150000030301b0301c25294 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 402115917 1250 402114667 402114679
    0x320030708090106031a090105060409110f1302160b090f03040e090309030d09061403040f06090812010b091e151602210114150d0c1e030311010209 65
    0x103614a08541d2110050103154580d541e42c44000001002030302c145c401c01007a0b0071248501e02d0251151421039800074400341c0580e050203003140020794a55100d40c0a0b6201b280d0300c03600c406403840401c4000c541070710349030081840010304220f881030070800d04524500c81c80e1007021998074800400c0e25440c8680e41445264030911092001039a12050a5440102c00080f00c2c141042035000910b4560b0201c40c103c080741d0107640030b0010700d500030125520190317000c900c1440c500b81a903c040a015642c0340c00b80200d0340e607021040400c4907102c21214040009105003c0c2175868406080040c0c2c0b1502d5514820300b0392812002035122040c100c040c521400620000034460341449030401903020011240080740600590401070791040b0f2803000f030b81103031030300000e12040388481c107801c40b0a10050342a41800e0300b001c01c015000c024400c40000801503d003000c0d0301c203051030814048182d540000e1404010b844404d40103100302d0394a8411030f400f13945c900408140c3c14048608038482c12407a19007040e = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 402117167 1250 402115917 402115921
    0xb040609230c0d02010c1a160309170a03060e070e0414011d040602041805040606120203070b0d02070602120f0f22080d020a050406030b030c060315041409010c032003 73
    0x12416499090901d40103041c02e18940301c2c5644e440745201071107120b2643c2054080c09000b01060546403050240c0c1440c1810080c12024be160324001c00254503100d1700311600054000700c9a1300c250008001090f82110040c0325003008080a00143e02c05c20505000d185003141001c24100500d80d464103c8061066010300c214688400414002004100340e60403a000c00001812542c0ba210b00c5006c850a010300041508003450201c040c1c500541c00f0302030001400e90003c015a60104540d01151170544096981e4488091008082c2c001c1c02e07c060b11161000c170b000840c645043e61650701ca926030182d4801d281d03071100488050542305484e07103032540319001900030fa100c10082d01145002e025491090405a40c04160800d170307440102d500b00040e0011408000e03041d010b0083e00c1914030100c0c040c1505e031440b00d012075880e000040c130108800380d07010400716460310341d075100c08084450b036031007610756140c010040ea001c9c00a80e00001c0c0001d161441c021411f215002a1031990040c0d0100300d441c0d5 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 402118417 1250 402117167 402117169
    0x30309060a15030609020d05070807060e0301330509010e071101200d060f0314070e06030a110d05100204050f060408060a09021f02010519020a0f12090b040609230c 72
    0x52172a0f090480e00b05800c04401404100100000001800c00800900c0301d039080c580c004040500f0a84100d00a81c1407850380b80407810306a054070280c80c1b4070901e9000701719401100d0008490203912950304400040c002289064555540c1d134821003a41d120a4910310580d01d101c2d00b228005041a1400844d005d200380c080001103006126030500664049040760311800064100105039100322914980d4540c46070702201c09220310350082086080350303011031070712402082c0c40b00d0320203400400c0f000e00c1240d00113080d0340c0c002c14001169009012983e000b5543da00500003544a4000c640c0300b503000050240503850300300c003120f003920441005007036540c8960381c0380320207400401402c1760711080040d92100c1d13101d12081c03099600c504a13400441d181c205915440e409102c618001800103004114405d009908482480c100f4038552411401c3d0400050280c001032451860081c0313511352820500c001e0080c03640110340b07600d004101d03512003140440c04000b0032500d446030380300868024680340d09203 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 402119667 1250 402118417 402118421
    0xe0c0d060c1e0e1c0b0a0c1107080d02121201140105040b0a080a0605030c1806043c0603031e0216030f050f160b0d110c01020c070b270409050d02030309060a150306 72
    0x4801f840e2300341540f10340e00e21024a81003240c6500003101d01e45c000d510240c090341d41002aa10313113400c04132103e854150400c840c0030505405000d040d05440d01c0d8040420545d200d20304030380040801d01070050302c86800c941d0048c01ca0805480d00d6000a041c0301004c6518540400d6020719000700500000401c88030840340021450002c1440c1d0740035a031007900c21400740f002d03183c403a80485816040580100b06810410f80c030030088500e40741480c0b070b1210a000103038100100000e1081c4004000344100d08141c0200c0c913100c840400f05070104440d210020402140ba80c8a4110300e10807400c0c0c03921414038480d00c0382d8610010a0545032114401030400c80403c2c400002c001034200020007199080400c0b074001440c1c0c2c002142081d65a5000484195016080c0005000380100c8502180f40c034400014000c641d00d48020808960481000c0c8500300daa02c550011f620303e94840b0580302c90100c00800a900ca80041b14850001c4c011600010b940c1c0c5100c0c82010300103201400c100220504603200c0c580 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 402120917 1250 402119667 402119681
    0x80a052707050402070302060403080903030f010b0304260409060e0606090616050105040c090b0102010507050901030c0c0507030602040f06080105130b21060a0e0c0d060c1e0e1c0b0a 80
    0x92140121200071402d6151800240403880c040d8005140070309103850700a0031084000c0481500380c0052003485400340080308001d045400d040d502584a072a1424501c0083c0c2d80b159103c11401c103285960140207540754060b0003202c2c0030b00d00c100240e40d95890044070002089541d994811010810055146418000340001503146410307000015425500e0710700316030b419202036030248800003003000030345d0540c01003a40308007085c4024000c9041a1001070040c0c010700d5482c1d8149611003403c001210b100c1c40d01060400d410200701c03603a0980c3ea04148000303601600a10b07202a051086c0800c0c46030140340ca40b4100c40015081811404200c0d034103500402d80000c0b81d9501c00c1c40d0301140c00440c0381c090002031030241d10001600300c50800121240888420a007180516003200140c82d1075551028510007005030051400309031452841421214880011520320030b64103e01204614182e1080903440359150a98140d03a5140f0141c0403502a001d90b808024030482d855000a00090900c1e00001 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 402122167 1250 402120917 402120991
    0x906090c040f061e030c0801050108090f01050c18030a08040504110f0c010c0908070e041106071209050117010803030a151206020304110f1302070218090c01080a05 72
    0x19003415110500d0b444030110603400340001a060807001e941201060f480c0c0301c120212814100042901e103203014001c468140f090f40e061181140009960314028403440b1801082e01c4000c124174075109000101c10340014030703241c05542c81d4502441c00c03030500180000c002900301c4081814580313840200030161101c205001540803003404000803180282003e003080891031030000c103140718107603001014030b44542d00c120605e40c0112010016443c0c0030303600301e42154001c9410f618054100300801c0040c03207451001041010003030340880390b4651144402d07060f0340007640d407903580030100440b808145a0a009261b2079420400218000d000640d00500e121003412031110041907488603160035110b0803520903500306800000b0030081050701000901514011580300b1072620481d4007051b84180d403040c001c050320343d00052590543d9113515001d003c84124810b80c60151030091100d9458220040d0711078082a040408120803415a0080304d11440075400d580c0800c080400c82c1c00041c00d80a8220 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 402123417 1250 402122167 402122191
    0x9011209081b0f151501180509010b04080c0103020415051e0c010603060b0607050d180e34021009020604080303093910050c070306051b0405090609 65
    0xb900c08000100c0d1014001c2c00c0b00c050060512a6150340342014905180c04803a44001410081002c240d05442c00c079132a030a01e41500c55000810301071180780c85a40243d1780c000c40c50400019200150001002520203010070760f003981c50300c040190203070300540c0900c0c0d082e0b074001e0498001440c490800b0746001e8251825071407207010f2400b80801c4c540d2003420014480d94480b201842802003900501c200148103a5000b4503144054070307410b450300107984200c004c002c03030f481c00d0341c41303d000000c1c40da8043c11a98811030500d00340b070b0003002007241c0b01566444600512001440340032400400850104080e900600010710b05494000001c0180850032030380035030140401300f0010002c102541c450000b400084c00c5603070800d03000070a10b407681d18103555200c50a8500b00070740c0303a00c07000140b10102d060f520702c03840c00c1078400706841c03034007540040b0125440f50000c00802d002075608164040c9040c002c40300b11049480c0f041c01004c3c859400384c41e03040b21805e400b00e4185c0c204201c070503602441c0f15000e = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 402124667 1250 402123417 402123427
    0x5040b090315150414060d080c0f010203070c03030c030c0e0f01030608010f0504050c0d050715031107030801050f0a05090f1503030309010605010f03020a021009080f0c031b030901120908 82
    0x3505410501c141c030416865070f450040c00280c0e007014443c042d00c102c1c612484e0a014507080303002840c8081c0420000b000d1080c0072503100a03e180802c40d1400c00f00480c07000790748074034141000800b6136025030b90036000a4105401d0320f0344980030b44214032841c907503580d45448600821050102403080b003440181055540c100c00210f0040a10030079000c452039081c00b05050500e800c04a10300102240030510802030408800001000001e0301d20843d20940546103001d20340640541c02002c40304c802d101c0491000a04008242e4800c050f2410703200100c0e040c400501010b801e1145141880c01042e800c000b20030301081d21030000700d059903800207103012460459069000030034150b4005507503c01007603460305400e01080d80c00c04002d412000ba245401c6003003480101c0029179a1105541c00f26240d660b8140401c10b102414080741c0700c050010f107403036546101e0000003e40e20792008070110030503a0000700586e025a4048115454107005a40e21f694050202e80c006000f8201880111400e0300c04000c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 402125917 1250 402124667 402124693
    0xc02120109030c02030705030d050a4506020d09060c080d0603050a03030f0b090109092f0a0906030503030f070c050d090501020c0906090c0a050708030f010302030d030c05040b0903 79
    0x1601d0200781c402d9948440040311441450724145840d04414829001390761030040c001d60010556041c0c14061070079010314401218469140350380b03900c00500c14211034501000400c600398031342c0c448102c041500011079a48aa0490f2641d14030000d000c00140740000410a40f80704452aa55250003100e41d1854194001400c00880d6a968402c4a16070050f520341c8043c140c05100c0c04800641c4102c0c24401564107100051806405000380c04140f41c2d15100d840c140440718116000350441d0705042d038161400403403022940005403100e18807409007041c021031015100d019100803290b000000314119101c907035410345c03800c80044ca83c004010b21000100040349040040c05040922608c54199113400c240009040c1b030a020102d034014130f100401d01c40c2644921598a9204110030303003ea40390450090200c60520030541e001d454543c012003444166074140000604881c400c13401c0300d42e1070909040960585420a004102096052004125090003d8001c2030300301d400805460610040c00 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 402127167 1250 402125917 402125921
    0x1050c0304260708030310260f100e300c0a0c1401080603100b041509060f061818020d140403030506041e09030509120a0309060905090402010c021201 66
    0x145072030b07407960180e040c4800742c848288981e80c041c11050340558a0743c6402800c03800e42e510244070b0000c2c076032505c0002ca41c11188011002c052020007000f501d05011000785e207565a0014170507240b0602d45000740710301d01c540700060740c050143e002c58251a007009102d42d8058544038512041035071210200506004441c003400410030301c03481042c17040281c0741440c11503d1845000c0d0700307260511100c941440031b01d42e030020b06801c0b10018090081050702805d00410041d0607564240d601d040c907861404100c06050303030041010389040c6940800c8240c0e940c0c500f11036008004210290600020340c040c0680b405294244c030080e00000f00c0585072000068440d401c407500b402d40a107410b903000c001d020805a15010347e80d04100700f1074080c006480e031a4504103403940820441c05c0400e650304400c034205409031003034650004c40201041c1d008404c81d20545d44178000e200c011400129264000305445009000341419101e02408075060741c2c0c2c81d44d0043d0307911740d088ca000782c0e8800d61040c1c41c030040c40e00c24 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 402128417 1250 402127167 402127199
    0xc020a03060e060c090105120a020f040902030f0c0a050703080601020705130e0d0302091e040603080c2503030905010807090e100618030b1f050d061b08070e01050c0304 74
    0x1d10300c00200107604408060a02d10007600081104a003000444c4260307038000103032490802c03004c600c20411b0700e0308002030300284110450841c2910b8086400100b0b4985070380a188a5003803100000c5141e034030200c135990184202c1c40000c002c141c041c45490b0209118a00071682302a06004450742076071160f0016040ce003102c0c4d041510300e41c80e281c060190560610800c0448025800d080d410410100001410f413001a40e2881415908084000455580342c01c143c0003140c011040c0c6656131400300007a41c0324151215000304080140b480f07091070100b2108100c080329013503503580480d03d0400d80111505800900207508201c039680021860f0303401150018040e83e00d035010800c04520700400509049540d40e0759008150308080d0804c0400e0b09081c060341c1c00b6241c0d0f800d038048070701c0610440c41240001d410141d0481d9080f0002002c004241c0d100e5001035022a9102500000111080368000401c41d04400000c10311928800c09501550190041c44901001d9a050684405200c003004480b = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 402129667 1250 402128417 402128423
    0x50106081b032401061b0212010507090b0414060f070c0906050315040b0106030203100f0605040e0a09050c1320071205040608070f0302040905042f1806010c020a03 72
    0x407030000403480c0c03800300901c00380d142c560b81d05211582e035038501a9101c01c0c014450310003444007059031003240d2a505180e055074143c2c020101c21944c00c44103081c1c0e00810b0304030340e6480410140e450200e0380d404400d040d54101c45a01c03d11403484201d1000f880b00e030b41c000d5119030721448402c0c003500307001500c200c0c0b461000c1c180c80000003600750302c1c04040600c0c0c4800100f03580d241122044c1031101040d444d81c000b9054500794140980c1daa21404003a403921481070f03201d0101058000b901160807548680207200f11040c544684503280c94031701d0404200c428410b00101254081602c05110b4100400d5031080c12107140c4000031944408901c000409500d600000e155407000580b100801c513008d100080301c9000382c58000c0c04c01d424a44c02078801d40b005071140302403102c2800d071110104d01c280c04480c0901620304081c4220b04003072404c0307440d82d00101903a01d07420b24000c51002c0e480341c040240d1203c00c0001417410348242d41640301c15000001c040d00301810007020340010030141c0c982072403003c01144 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 402130917 1250 402129667 402129703
    0x601081011210a0501090c1d01021f0c0207090b030a110103021606090b0c07020307030b1003060f09020a0501020d050412020402041710051b0a03151e0e0f01060507080705010608 78
    0x83c00d50740150464405030003c0079501d107000d003d10501039200c40d42c1603541b07980c405030f8102054140010b030320741445510404c0d040c4000140c401c0c021001c3c0c2c0c00a450021068003129841612420b0040c142e5200c500030741e41542c03007040c1c088003003600d505c00030300c03001010b04006160081c407001c02c500c101403c0c1d20940e400c5803940c05000410079509400d540c0400e42401060411b01c0590021b9102c024911000d17018403103c0002c00c284500c203003044802035601205c104000e101514640c00a80000c0e0805c0c0e01c1003202c40b02c002095400842c0543c0954807a80e542c038030349800c0c512070824207802d580060b0f81240c1e0a10001c6a47d5080748440d40d04500f8800c02011074415a100c0141618001052207400710710040540c0c044165440c00c0e6080c81d0500c5c1030108881c4c44052601c117104450750300946102c56804081030a040080c02d021060311000385023041c1e180d94024800c1d91000c020301c201d80002d103082000202040400025000b020310440000c9001a5140081480c02446400200c4101 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 402132167 1250 402130917 402130921
    0x506070e090a2a110606090405062a280f08190f020c010203010f090b061903290102012304020409030c050d0302030115020a030f200601030c090e060108101121 70
    0x340081240c40d40c08481120700c03031390350300d07249e40d690b607c03020058a84103c00440341c4410080094084c21418800050006aa102d0440801002a0316100d01407212141400038140150611074041d6001c031680c1515611602e03207540710442c0050400c144080704e410355614190540381083e00007000e010030f02c1000942c903941810364480e000c240da86d22400d4074500d44103c000366a118041074800c0307012a03100c0180c0c980500b91054001c0e0680031601c0c091050010b84281e01d00455814940709100b081e80200046010580d00301c2c0ca09020406c015107042c101c0c00020018542a004107040c01c2c424540803d0b9800c135540d95500c0c0c4500307140114046500800140030b00110442c4218803940544010300c11401e05440282441e000d84a03184100044100c458018590180018071390035000e4003210b13182d42c0d4a05012a01c4800760203080b09407401c00f4070b120080c000000c2c0c81c0c3d043e5a002c81c040c100c10059444e515008115030220f10014074000c2c4001006060149805e0010f80261800b00c580e40c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 402133417 1250 402132167 402132197
    0x10e06010621022205030318060d1107030215070203090306011202010203070b10030219031101080c0906042301090e0718151d03061302040e0109020d030c0506070e090a2a 75
    0x80c030b4132900440d000354020300010306140075841122425603011b40721290340d02c60030300b111405402d40c1d48200040f0080060114101907000071503130f42000b1117904040b41900d401404076103a1040f440c005034103600660062000907007583c21503d02d144140116407402c02c0f41e59400300c0402080741c860202c01e1a9200400950818071034a000d900070a402e100050f50465844a501486400c18141001003110001c0d841100e60021106040002004541c82c0d654581c46d410009030100b8101050a01030018030505500442046050b505202e81c0780c4d40c25a1084403ca0f610040300382051402c010741d042c002103151854280c012011101d60b91000c01602c01d9040c404405c01c4059003501a5015004210040c880c1c0c8590070320195044802083d1440d003420600e0146c00345c40320113548180c201ea005d400b0140c100f41500c425910407030595600d40e84040080e180c42c0d042070001a00425800000b581c42100f903030004003110070408a01c40826500151402411b60a421810100e0f00358000f00c80b03d = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 402134667 1250 402133417 402133477
    0x31109090403020d0e030616050a2718050907030f03020312010f0e100609050f06090319020312040b072a2c09070e100e091e010e0601062102 62
    0x200040d0001c0c0307c6804d01d4621500a000c40c4540f0000700440400c80032170491140301c5219444000c0c503402407410b4400782002a20f1201da1080c513032310b64540010100c052405020309403158a00e0800f5160300c0c0d180d503da05403189580b510031000c40c001001f0327568035900d0303940f41980a0650908803400c0750782000e0300c1c1c80c8080b0000d0034000301c406503070100b085040d60021490f01602d03429681804041090400300c2c00c1405140000c950500545100910b6006c0000e41c0c1c40881c0d0003182264404031203002d030215544910701884d2503d900421000020a00c4003545041c140c418030301110440044680003001c04000d504644d04640d0500c2c1e0a2030041480d2030360030311003018030780c40d0801c0342841024141c6e990351a01c80d60b44440b40880004100300e801c451014024040048451450700d4002001611b41d0703402404070b1645110300711040001281486a407005402c407800030201a4204102920720051490403120340300000d204541c2e60b808540043c2804007040001c2c7c0c0c181040700240c11031 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 402135917 1250 402134667 402134687
    0x306020d05060f0f030c060d09080313030f1706060313080313050d0e0901031b0b0a02100f050628050303070305070c0b03040317060112060e0a0b04060b0406031109090403020d 77
    0x321454041100e1042a5408200c044408000b2507810b907645090100c007201030103489002504800c00030bc20003c1d01401d45001e0a0307010312a84c1d03aa00c0f00c00e0500000c0c0c40c041c0885000e1482d5000043c0019610b00700400115080206600070003150031a90307440c0c03881070303008407030040010b94640035200420004214490f1f481149050034425004503601081802d9014440984580f07090110240b40c0408500144090510f00f8201079540e48541000303560354005130701c095000352808040c281c205056200301402a08000d008c0804042a800c1c299801da540320b0300c180881404403000034107a50200700a02c0068465156151100d0035410b180c90800581e81c84140604020010400042e43c8405881d2518a00c001315881315101c0d10012030b0f44da001c0446030b600843c640880481c01e8280e455641c2e11440c2034403410b014007502c0390b041c403007903d07a180304901c004103081c002445524029000a17401c159000c8444c0d060000742d80c00603100c0901543e042c1d0150304864660010254886680d40c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 402137167 1250 402135917 402135919
    0x801090308010b190302030c04030b01170f0607050a030b03010b0616020906090106020c0d170d06140f0109180f0609060614030f0103021e10030501061d09040b0606040306020d05060f 80
    0x5803c21680c00341302107010011460560425a00000107090f040b6000262405141c03c00140102c560711071004074808003014001d000584144411000c04a031b0000e110740c0f181c941c645d5624148500c82d2029009000103155640d459500d80f02c0800341c42e20b608018007071032541d110f95460421880e0050040c04500946a9801200c1c0700700140000c40d00010404403241041d41c0e11440c00c506400d160314140311210a114909030000740003940801141c00c88401c0d10072040e01c007000491300f002005450781036480420302180075200100004060a0351030714004481181c0440d628050b02c60300b100b12002c80d0401e00005a907250700740309155000e0b901c0c00031400c0303e028980c91402c00b001e00c6205c1540510000303200b41400c44040050074520078400c452900040e00c6512030285021001e40541004d0042100142181c401d0f880e002d040c602c1215140003020305103d25641b0b0b180c40c5c0d44002e070401001e040c1c0003c0100000070005896100402c1c8011440c580058141081010040c0c1d10342556000e03 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 402138417 1250 402137167 402137189
    0x180702060a0e0c150f0f0c06040b070e090a0e0708121209151302010504090f0e0616050d0f02041503060501030c1103120a0e0a0c0e0702060702070b1303020a080109030801 75
    0x1005900c4000344002d01510130124030383c03205a444503001191290200e40d50205202240750020340c03a0003d6050b0107030384905104007607540e600c07404440310626030002960114880000c10b1070750101da030052506c10380d50b5045da102e213a210600c01c0c0c0740040001c8400700f40e0b0800504600050980c2e2045034204030b1040160142102c0c0c000300400b0218064042000b40001c022001d08580c0100b003100c1c002e1080283c280000e011050860008200340480900c20f4094040025004980b0700340038048428582c50765030500c0700440214000f0100032010038030080e401c10004c218816110450128420075603030105010342071800060a848601401d28103109000300c19140858003c07090f44d601020340c2c1289106a80c68400e4800501450140ba090600403050440306124080180c03070140e4075a03001243d10360700c8002049a0300d42041b920b14006030000c100511a031440100200007410106040a004e070303490780c00041055545070300c402c0c150303992441e03072008144d0400d4540d13005240c56009 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 402139667 1250 402138417 402138433
    0x120d0f201c05041512020d06060c02132003180f0d02100c12020a090308030a02040e0c0c151b0414011e1407060e0a03211811180702060a0e 61
    0x1c190442c407140c1320382001c0c000903050018103211198182c402034a18000148012592202c011300385002041041e070040c070406005a070042c4250103012028446000c1e030301e40c8200e0151120400350000b030110000b401c1900300302001e000301042903031900700d105406406e0314000071501a10b000c006201c90b075826802d000c94030a005420400f09881070003200c0c00566134500d0b109084034644030f9508020500103000c418003807155000e82c060015a0201011180c954540203c0f42c0b266000398208100160310140c2088a04801c410040e6003001000444029100148451044030340094100340ea50f441011205540c0d0343e03201c00c6449082c04170b079a03101c0072a035003980b0042402e1a100d9a544403130740c00003a204104211580030380280900b2340e040c0e0305a401680b600402d0f4901d404100c3c0c01c140e105c000c4141c6403010b244112402260850104400740d860b42d40c58888190790350300116840300c0c0c0071208060302d02c8043c0c0c80a100349090303406481c1030f1510f521541d04a0791034511030b000302e03030240c10 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 402140917 1250 402139667 402139679
    0x20d0e06010623030a021303030e04200304021203040e0f100506070510020309030d020403060912051204031407080c0f0f03070c0909080f0d05070e120d0f201c0504 72
    0xf0300c00f691040c0d128a40c0c0d03559454101c1c0040c2c4100da800280c0c40d43c101c0d000205041d48036041c601024011241885100c60b000c2310400d011010b40300b905800350081001c0360040c904056854451042c1105990402c5c0c0c0d034001d0f00c1a1160100d8494440f01c54001c20000c00c003c90704400e0010700344c100c440f281031081ca61a40b40d59014070000c07018100f5070000106e06540c03030801c16942c855801402c195a07070360312842c0070005052140d0741118415100b46507110214050020350340c1c900e000d98043e90240e902e584003102e200d101340ca07045010a00c20800781c0d010405d500c000344120742003540181a000c03403400c0341610707007550710f002249036800c24030410700001e10401c400411140c007500040790483c50b03400c21100318400d80711420b10001002030780240c480100c2c3c006a00c102ca0070303100d2042103000c18003440556681540d601c05160400088240c81d18000c01250203821060320309090320030328040b0044500000da04403992030f0350003403400103640400c0a13520300f201249441c242c0d0034646015 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 402142167 1250 402140917 402140957
    0xf06020c0c0d051c030618020c0106050301020403260708031f061e0311040806091005150f0d03030b1309060b0a210302030c030315030d0c0203032506020d0e060106 72
    0x1c1e08904043c4000510152681709401190241031080158458010122601002507012082c89400c81d420000700140d03514042c0b090b038040b6508030120001c1207080c4032124981038880950070400f000d042c42408003040b40300e400745129000e98030120700200703040c10b04400c43d030300d10b607002d1703400c0001c000c0044030914484c80203004a0580c6040119903494624583c150711b01858104481d988540001c0009c1a5400120907181d03982107001040541c0b50140840040d180100000c0c1d0170408204480507a03040c0911040c680c10b000e03290000e1503c00810000d07088d042d51180d5985856180c83c0840c041c420140305142c9814001c5608032681881e182e6581c4a14880b4070b89485003d00c1100320790107060080c0121902d10b150b440aa0b680c0340340c1a1015088102035154840c000e00c0f9003249240068000c030368640100e80c004000390f080c040040d1400c400460311181d030a045111500600c0001030745c40c000361010004003c800700e403030b2511010440c42c041050340001d00f004480c4208443c007010369 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 402143417 1250 402142167 402142183
    0x7110405040c150c021206060108221419030522030510020f1306031406040510091a0409060225030906050f09090f0f0a060609140103090f06020c0c0d05 67
    0x380d00086107905880d9040d513400806400c0a03420030904c80754070800c42d1010810510500090700c565550780c480c03000b0200c0300501d04034503601c0035050008540c0811131440560707212032100e404481e007041a509101d00f50f0405080304030085000412490f883d48544e9441d07049080d095400080564a1501c0b0715544550100204102d180c0c0040c40d01c1174400d1103422580078014107000344030b059644c0c60005004103564240502d042002801090441c0ba180c042e041c02040380c4100d1500150502050600821000b041202e108124a215121686603402a000c0c034900a000060f02c0360841910740403400490b9205488154120034148000382d04940310f20182c2d90103141080d12000c0145803048144980e04030583d20003582820410300b5440034900601c40d80d0407880c030000c00c0e15403802c0ea41c00c4e100107000c0c5001054045100b0701028000d400c4040b040e250500d00890b1a540e19120304001e090702d014152034041d00010300480742801000000b004c00c10a0310501d1080810342c5504d9194001 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 402144667 1250 402143417 402143429
    0x81207051507030902060c070f090b06070311030c070602100b0d0203061612050a0c0f090621060b0408071a040e04020904050f031603030b09130210022107110405040c 73
    0x40008075038041c1c0f00398030203002240e02409541d03890802c1c90b443d594078100d81c8114841e410040c140031844000702d002e100c1c1d5007034018160500300000d03540c050741c11030030b80246041d90303100901420442c404200481c10042c101c94026080701078014034110140e8040f81750f01406410455401c0005880009403594800a00381002148949540c801c48141c141c03800001c41e65410328060064464166000300e1002419440e0500e00d40052501554260164811003020400d01020180c6410113040c2440410a000b2400144507844e40300e01649600550041c00d01640640024041301e602c00110558000d04c0001c8142000e140407411071546a000380003c0c0220301203c0807408015040202d046580034600640e502e45101c2c101c0c41003030796068042900000d0409644801d5070a181c0d11081c0181c1020106001c0516140c00707000c0c4480040e10031004601c105402c18401c0801c5a2601080420490002e075444041303003804010b10611014030b91141c0d1404040c4000076034103170880c00c21105 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 402145917 1250 402144667 402144703
    0x30f05011401050307110c130218040603020f04020f0c0106091b050301080316060f05011e170c010c0c0305070807060f02061302040b0103060504021204121115060d081308120705 78
    0x14100c404078200b02007c954250803502006148801c0201c0fa00039054a01403841d0340b2212041550801c03040c1d41e024072000c0e411201c002c4c0340e40343e00e052903002021500341071101146040d121032140d90031910903510215400d607a402583e0000c1350401c1c500908400c05107002411941422180e07500c13441110010350124141c80c20000411030660060615800c0e2003504101c1e96a44403040d5441c0a0400d48400c00300030820004600d04a2900305510460310342002051105d0b004001900c1484280909498052a0180000004c0e40030803140d0050300c0120044c001240c07030850007902222059010f1070954100008002d04411142d03024404540c04131000b09120135580016002407445801064100340000b038070302c0018070201c903280e0045118080c01211052081d804554500d01422454815040b4030310584c2203190196007280c00c0394004114151070000c540c0c5481e600c3c0c2c00a007200324000c056840802c180c0c40c080c001d0010b139004240c0c0d52440d01c13040d81c0c0c455031222491800d1808001c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 402147167 1250 402145917 402145937
    0x603040308150a051f0207060309050616230a08160804030c02190902090f030d091818060516180e0405030f040803041505090a14041b030f05011401050307 68
    0x5a6502c84a000800d80a0402e49642417220120040e00002e00d140c1000b504c0760560004119100c0e108144c03610350448007905460301c40f0003400c0000b03c2c0402c001020012408400011a2110480d2543c07004c40c44811681ea40c00c0701d000900800401030500480c0004d5041355105240c00020b0b0703a41c05941403920302540c414610000c0c000405680c1250f51941011b000401c81140326030003040d48400132648820010f240380c04055a4440002924001491400042124095903e1201039669034940c0c0414040b1300701d07000710308061075420161006038a610a000e040311840b0102c0d521200701d45003140c2d0005140caa50300041c0401d20070010045403001c00036085c41814016182549601ea100340e03035903a1b403042c1080d6a90010700a1312076624284881151681c055401c4400b50180941043e500341e11b0084c2000889082407640c2d6001500c61842d052080408003441d00c40252075100000c40a140007038520480308142c104041130307450004105542ea03006415030b6886980c0c0d1130400c001e0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 402148417 1250 402147167 402147169
    0x141e0103080a030518010213051804120c03030603060510060806030c063015100219080c19150b040209063708010303031a0a0b0307030b12100605060304030815 70
    0x44024200c40c1d500c40e5101192018582300c280341c2400c101d54044030606101c0d51392000c0414081810746000b001240c0002e4030722074541c020710b590309a0900a040004171180e0703a840b06425504d0444018202190340c040900c11113820213513054100005500500d50079001d00081080c501c03a0b07582c0b5808665007859a00502c00e41c01507040e4801e219881907460707a007042910044443d50414410303200f240301c207000d0030a00e44001501d9900c0c03203c44506070601c0c8640c0e11540ea10390b0000c042c04400d800758100c080317020403030f10740c4406481c0d10480303001d080d00300c0c09043d241c1190403601b030b098031903801080740c0c54840da1840141d4403141038140d482800c007110301440066080201c1103a100710301d08055070a45044c3c1060b0514100d030701a4809010145040d001203995882c4c0b0100c0d958018009075041c091441c2e898051540070209041c0004e01042c0c1c1000901d02c05c0c1d008181da201c5030b0006081c201c141142c1e02400300100410360310700742542015a40586000c00060505804010b000721354030b42 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 402149667 1250 402148417 402148441
    0x2031e12011a0c01020c010e06070c0308040b0402040f0e060a0c090303020304031509050d020c0a060306080d080a02040b0c1609140c070305120c07021f0504060e0604030204141e0103080a0305 84
    0x402d43c940402155134041c03600105001e0030284040503883e001d01e4000402080c01810b4256559030715581d0001c8903038503a52a203481a0000c1c0c000ea030841d1380c4150421144103a40710346100c20349100010400c03460480c4900d401e0300c0c1c4c02c3c0c0fa844200060340c40d0400001c0d80020699054a03400039100d075005601203d403000a14010002a2072441000c5036110503680114507020170040030303200c90f4903003621104c055081d101c05120b111000d9201900b4598210310544178070340c0201d17403581c005d45820f81d00d0030300c940b40d9048000744800b2074015946078810b030180c03000300384c009100c15041070062207031501c00c04481c1c1100030701b0381e00ea03072030f00054040070036224208031405000b08296120303442c200720320748440750380050100700d0041c0041030700901c1c00340008449103001d10180da40d0b580b4050034001c04032000010101220340184003804080010303940d601803081041086803480403145060f03040c0e0b0061125011083c0200850080140003044035881101c0c0404a41e040202c3c80b0740b124041000e07 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 402150917 1250 402149667 402149677
    0x19050705030f0f13090507080a020903011517280f0809030706090e0a050c09011b02060d05070219020f040203060102030d0e011b140d0504021f02031e12011a 69
    0x2400c00800070341080792000d00d0f8060f1009505910a1080a649a400350012118252400c00c04a9000f90010720300340000d40003030511120180010034900d441221144c60720074240c0015040d0b40c5506d1001250100c20041d01c0700c0d44005410400307500c1143c404a0903102d0291030041c150081130f4611200744100c2c034084035550780f400f070b0854070199918000200711403002c0c014140c034026420080b500c0031070940982c078012406d40c1011460f000241f8015201203015a07044070301e20444901d000b02503a00c4c0c201500e60450a60008104c91801000080c2450000c00c0789200b40c104034030646000d6110702d122801490002ea400582c3c87d1207400050b0301c0c0d40201b101d40210103042c4181c1d00d00015040d00280e1080c01e48d01c9001200400e0200f090b185c9521080a203030585d4010301c0510848103d582006810500107015101c81410000400200c40c9400c2034180259000152044003400120703504000c55a5001c503050600312805001c0014004c10300ca4507040c20410503510300e0a5607818201c503 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 402152167 1250 402150917 402150937
    0x109030506070201050a06050108041a09070b070b060f0a0807050d0c05030d030902040501060f1d010306031a0609070c050a060e0102040f0e01050a0e13080c030f030403080f0c1905070503 82
    0x407540e10307180d00001c3c040c1030200c400c0d4021a0400781c0000b40c95010300120f0f406654015103c4104054030501c5030360180009001100600c900c80700001d07100802002030800304e003d4000702e07429141c0141400081c0f2043c1d0503541c010784040204000382a03000c213040040e91401c44000d8480b0b00c42e03003800240345602d81c01469142c024580000a0950141c1c0035907038036482590b040c88240c0e40d402043d558140d00c0710030b800c080340040e59102d92803901500403082124050500003003068a0f61181074140d01102071002892a02605001d41850030380411640100e0724604110303445c00550751980ca40090350303401802c841d01c17000c480c030803c642034058a014161041680c42c6140d035512817540e010000f03101e814003514030014046010548400d526200303001c1500100c0303000030799544107011030b8482e40c3c004089000c203010140c1e540d02a4801180214020340d82da0002c0d00380944409480100503010000080302007241d00d00000700c42210a80c4000181031980d01c804460800e60304608c102d040131 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 402153417 1250 402152167 402152173
    0xf1b080604140c120303040b0f060d021c0f140105010f050f01050a020a0206030c0a12090f0f03140f0a020d08151002030f07030816090803191206080d1106100b0901090305 75
    0x130703a440761001000d10311940c005c100f03e400e6602e9651004001080a5443c01d0704641c020700d042015050880401c0681084004460310f081001d4a48162408405000302e0b844a0008090300080b1803d0207501c0c0542a4500e80701c005904e4900011980801e450502d4144907000c80d640181500902c803404c2404d4028018503071344d1406000586059202d40c0094012aa10495075410308005201e04070300360b81e00681c200e200b06859162452003102569045042243d803034490000c611071a405000761050b03ca07100e41c1c580f400c03e8000b03401c0c06186084201080070800811103020b0f081003214042c003000b66489035281182c0003040341036200e089200380c1360420000742c0718105036101c05020b00c5020401400c0c40c02e03180811049038411141c1c4140020f07544188440222140c000c02c45058500c01030404520840c0d44131442d1043d00c0c06640114550740040802d00c8009401110034110092294090b207441d04e40000a40c880707210501034284603a00201e00c10489900450b0610040e40d048021 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 402154667 1250 402153417 402153439
    0x3200d0203030702190c050127080106030212010c12020c03090411090907020a03080a05060109050310052a070605040512070c0302010f05070b0f061302070f1b080604140c 75
    0x41d58a0b44166030400051251072034802e050041180560030700c60b0b108548a40551030303c0700446071050729613188641ca02d903049450a006150a400400400b03c6a0000c80c20915600420824050392184104242d0404a501d44104d500c102005059448400e0050321000104446441c50141e03587c41900130f450205501d40525820024000041c02220340070324556810b2002c0340c9580b80510010089400303040850310720b10f500c0c1c001981c0101c06240c16240e040d550700000e0300e80001d50411800d560782d1502072006020303080d45040364620340303418109102e040b040182c91091040703a02c00750080d0741d94008982084418481400b00078042e001c5280c0355205400c0241c0d144980703100072804154031111344852280120151101660410814062607135031400e4916100c000030500c961211220350f00b2a82c001c02440030b054002c0c0250000c0cac4501c0540e00d480042041d035420b010412030030441c81000340b5180012010341c0241c2c0451032040303001d00030882c1494403010303c55496200350f100b81 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 402155917 1250 402154667 402154693
    0x6190e0406031b0501230904091e06060b091008090a06020304050d0e030a08220302030708030c010f020c0601060c0f0213090203060717071b061104030c0905070c0320 73
    0x100490303100b0f81c60303100d0f8664142c0c3d035001569032810300310030b43c0300038a101e844441401c07044401816121501500c0820b0340c09055550b104034000782c1f0030005c01c200780c1807858010700c01c03036104450181407112111813910002500085204000f0100710b0200400340300041c0200409100544e0559072040041d5101d0070640703441038444808505c600700007000c0c05000c3c1c404e45000900103245642041c2002d151609200c2d08220209851401d1004561140c00000041e10200b18240003071090601440c1c80b0720340d030031500e829511000c180601450040c04100307207011001c29618115a0b0509043d81e5000c12403500c05210450303140d0181d40001413543c4485140804d4110000b101d00c22015120719903a08480bd88102d44000d40c11074003814070100058446000f030b401280c041007a2005102d001c90f059507614103940d454400314049601c080740400c03c03c1442d0400760003400e42d09100388454541034800500748000300c900501003000c01a02030040e03459001c01600e060104805450484107480 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 402157167 1250 402155917 402155933
    0xd0312021b0a11030d0c0b27060a02210606033105010501180e0a0803091608010902030f0a150b0a12062405220e160608010b03010506190e040603 64
    0xc610307400ba0040c080582c06891141000601386e603805180380d00c45882e800034400c21954006555002c25162100701541c0341c004026480c440c1513030314405a80ea1001c0100100621240b0303968000c0488202c00303001d09583c6410580390702101e00060750881d142c1d504c1c01d0001c0c09035000d1040c50989003280c40c42d001c1c0304040d003000303042e1401100d4001d25020500b031207000700e07000c000e0082c015400030b41c0c4010000305004010340e0003c8481084604040ca490480d503900301017940845002d07036549070002c0c1142400d008100300388600d02d0240c40208620348407129214141010031288503652400000540d644d04c0400018080814071220704282c0342c900300004242842080d40440320500e810441000101c07545000d542010b442c0d58410340055040c08809410500a4600386031102c0c80aa1400d10411200800d0058942008e840b9032800e40090820707041a00111032044041005102c2a102c00040700d900c1d0380030500750b1041c000c004904072120816622001d600509001002041c40880 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 402158273 1106 402157167 402157193
    0x601051204051018020306090d1b051906150b0a0f030b04060504020c1b0102010c08070c021906020d260601110c0603011203030b0d0312021b0a 63
    0x101d020300151400440c541e04ca030030300d100d008010b514041140365006200000a020100407002005213146800d0400d201202c418803210800c102c410000066101800340c03000003c22010300e08070010b000d00d40b1801411101090010810107403143c11103080600580362040c0da4960608181c001c3d101701c0001300da11590310000050951030310300081c0511100e007006440010803508034825500f46280700d69045a241a00300c3d9200d90300a58040e800008074180188829201e02c00503600c0710704681101405c0202c9900051000e4001414410a0f2050f031103040e440c00340c480414400011103400660012001000300390554002c600b08122240841d0598072049a00000b01794181c0c000e030310035650b44007403401250905070b251180355401c03401120341804010203510010441c544c896420501c01b6030000e40270b01c480000d6801500c103040f4210540d04141200c1c104a0751220703030 = true := by decide +kernel

theorem cover : BRFrame.Cov 401978417 402158273 := by
  have h0 := BRFrame.cov_init 401978417
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401978417 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401978417 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401978417 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401978417 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401978417 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401978417 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401978417 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401978417 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401978417 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401978417 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401978417 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401978417 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401978417 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401978417 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401978417 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401978417 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401978417 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401978417 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401978417 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401978417 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401978417 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401978417 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401978417 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401978417 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401978417 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401978417 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401978417 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401978417 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401978417 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401978417 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401978417 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401978417 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401978417 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401978417 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401978417 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401978417 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401978417 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401978417 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401978417 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401978417 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401978417 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401978417 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401978417 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401978417 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401978417 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401978417 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401978417 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401978417 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401978417 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401978417 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401978417 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401978417 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401978417 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401978417 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401978417 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401978417 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401978417 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401978417 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401978417 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401978417 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401978417 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401978417 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401978417 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401978417 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401978417 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401978417 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401978417 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401978417 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401978417 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401978417 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401978417 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401978417 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401978417 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401978417 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401978417 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401978417 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401978417 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401978417 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401978417 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401978417 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401978417 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401978417 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401978417 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401978417 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401978417 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401978417 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401978417 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401978417 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401978417 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401978417 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401978417 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401978417 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401978417 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401978417 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401978417 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401978417 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401978417 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401978417 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401978417 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401978417 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401978417 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401978417 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401978417 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401978417 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401978417 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401978417 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401978417 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401978417 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401978417 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401978417 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401978417 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401978417 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401978417 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401978417 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401978417 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401978417 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401978417 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401978417 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401978417 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401978417 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401978417 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401978417 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401978417 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401978417 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401978417 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401978417 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401978417 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401978417 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401978417 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401978417 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401978417 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401978417 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401978417 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401978417 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401978417 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401978417 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401978417 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401978417 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401978417 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401978417 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401978417 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401978417 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401978417 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 401978417 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 401978417 ≤ n) (h2 : n < 402158273) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
