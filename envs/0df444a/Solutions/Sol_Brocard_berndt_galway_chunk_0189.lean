-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0189
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T18:20:24.905864+00:00
-- url     : https://prove2.me/submissions/7ba9ad49-5132-4e11-b3b6-3743683554f3

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 33812954 ≤ n < 33992811 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 33814204 1250 33812954 33813019
    0xb040503060a05162303040c030b0f090c0105130815010314030705061612050c0301080f03030f0105041d070306060905070f1706121009060b061c020304020609 70
    0xd860700c02e078080c1a00c2003200d07510f01d548103131100700001030b1040248240200c9203151410b5280c80800c215001a0300480307048e80c1c2900480003c00800000320050b5034040c8085656510504051010544400c0817921182c100704011645062610501c940e82c4014880f00048603820b100c070282800c1001001d20058802c82c180d11030031070410801208442400b5408006401541d840b07041110703480704100382d0ba4081290044044003e40b00c28030480340100d004418007501c940c54040b2040c03a1904a90304000c04e40c20070300c140007080060500b86c0d81551011100440c80c041c1010111960190750304943c0745c6440b4583c000400d010040c1d000c4426034494400030302c050350b150380040d11155000003541000950300400d003c045d40c4201c0031903030802c0e0001d040c6140309418001d82c0e403a00203009072a0b40c409a0301d40960341040ba09128000706400161059410030001c4c4100514408070500c005013070580000015085580f50f000b100c1ca00500280100101b03030103030380200440d1410101060 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 33815454 1250 33814204 33814213
    0xe0303040b190315060203040b03070908010504030206040506090d1d030a080a0e19050108041103010b03030703080603070f0303080403050705100509030d05010b04050d060207060e010c02030d060b040303080109051b040b040503 99
    0x4c04201d0002c2400203590550700114541440d00401408030740c0700901610401c9461000400c003201d01303020b8140628041e034020102c1d810182443c504010010300a803c2c50780c03080c1c940b80e25040e041000c00d003107414002143c064001c20140800d003803081c8048020003c22000803400012900300510807498001510b81180003030200c031000211060307600995020800b040b0019000802d183d01c803000d42c0030007500105900c501c1c580842c0c95904140310880210720440b08008150900300310b40303c000e00304410042c503040e00d980c5001d40a000041e01c050200a400682503050080c2002440d01c0000d080004004c02d145c0b0040b400e8994014200908902d403c140c00010746040402c19201910001006850050000d40e03d000096001b4102255014ac41e00f010101c0000b0a1140311201041c1d070b00955a603078650410802110055040100034a070140802d102081d0301910f9141550580350000a00b41c840643c038100d45110f4400d01d0361b030700300005000b01c0e000e11100042d004960041d41100c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 33816704 1250 33815454 33815471
    0x90f0209060c0a0b31060e06010f060305100b040506030405010b030d090305010e060f07030209011202040b12010e070c0206070303180302030a1205040f080702060706060b090906060901020c010e0303040b1903 91
    0x1449120651090f02c6521a002c040203110280d2030317204c0d101c10b520460002441140d120781d1207081403800d82c482c071101c41c1e02010401a0326010b00900741d100c660028032001040c144141000a8007030303806024080d22000c0005030402400354044007040750028100e541d12004000028000c40883c0400c40e101d50a010415401240000740f06001740c602c1d0840d102a81d40b40c00044000350006001c07141000800f40440c4400000c502c010805041c1ea404040da8410101c2010140503406034488402114048200040070b6807280c41d840c80150304642290fa10707000c5050031006011a000c0b400b0000c0c01c2c81c0c00080800d40c0000c0140000080e40e26008100c0009610040446404880c050b15850440800c2000036412030014044180300800c40c50130545240c4804045401e250001454200009000742043c541801ca1a130701180440340ba918102020740000c0d01c2d11103508109051000d00000209156400d205a601034820781c840341b0384410307684103200071140c3d41c0840c0300c0102c3d10f0150360 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 33817954 1250 33816704 33816721
    0x8030901050103060f05070801181d0604030e01050c0309010c0c050301020d050a0c0306030308010314070803030a14010906031a31020406050a0e04030e0105160503070201080601050c07090f0209060c0a0b 89
    0x1c06e07102d0320154848080030f07840c0080c0d03460f92648030b254480c3c0d280c3e40c0d50340400803000529480720b40010311000400c510318103442c0c0900443c0001c036006041c0803050043d95070411001045420200081c64001042202032403c800a1003a0f604942c2c1d15500101e0744203000a1341703611903842409107210034050b000d29440143c0032107001e804040c002030109401413000c40c101610140242a240f01101d00041c0e1391000340741550416500b50040c0c54860028160314668445140e015041100080007400d20b155190012a20304401031380e02c4c07803189000159401500349000c0a4507001a09604c0b01021103540040e0310030181208900c22072a01d07402050a007040b0700d80206a640c058102110307519030ba107094416083c04040e40381005420800184845608a0788140d6540300d0710080d0f032508124800901082d2006000704d0420100748640d8050400001c1c0110444040d0500000c225020500305800703441030025440d0000e4002414100c04200050001c1003540980074415854031580003 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 33819204 1250 33817954 33817961
    0xa0c03030f08062202030c040f0b03010801060801140103060c17070908070906080613050703080708030103061404020f040e030906070b06090c09010806010807170403050901020106170304031e08030901050103060f 93
    0xd002c204d1001c10049040d075036041c1d1740116007000399003c0003414942c1d035500c0d4a10903074480d0001540381d0300c084010003941c60240100405880c0e04d038000e1103900d03002c280140b96000e0510000e000356403a2150001200d00400740041c0c000d040000081d420b2030480000750080c0d07054410070301c070b5104032540040c2010091044605540180c009401c0580b070300c0400c00740d14404040306907a07900074050004005500c12008188203440391411540307945c59810140c040320a491203441c00301e0664020880180c2d1000341c1500c213140b084800003218071901003814a58000d03250301d2a08464005103000501075544081486240d0442d418403041c4c0c0c0d801c0b18120103000e00c1c866240810048000700304590702481d021903100c10945403640004044010000045500b81d4003640030410018250f202c559081c040e00005c4e02001c2507100400380c290712502d03070340c0c840c0e44005050303854411245000d80c42000007100d06660404c60047e02c03402c220760031500030070003131004031506403504803150078046c034901 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 33820454 1250 33819204 33819229
    0x6031b080c070615080d02100b010201051303050a030b06031510020a030c0609060f0c0801050a0b040614030702120c030306130504080703120b0406060903020306061503180a0c03030f0806 82
    0x681d058207044032076444402404192040d8403400a0040000c038900d44100a0010f4000c6170b940240000e404810040003102d40040405046904210400a441e117000245511032503140c58425503400c140041200148622002e042e442240002401024040380c1248a04c401c03084483e80901d50100c1001d030790b18082c87d100200816521860300e0003182c119400100c800b40100b10124481d0400040e540458800180990200c1e03140e43c010b0202d03041094032507018010b02c620252a0a04200001e07080b400e00341c4007024085000000210039520a01c02c0c401e044020140d180d442c1d103405036880d5181e8100b00d9800780541d820050505081e141e90044a005642110506150540c0c0d5103003110b00034002e03602900e160791518488020f6448030b214010050800d43d0703d0400320b90951041508015014041d54170400d4202c1e040201d64041c28110780e0050011203400c00710200315102c682c00c00440c0c0d0006004019046000010315812104034125045103946044140d52101d040004150560 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 33821704 1250 33820454 33820471
    0x3070c06081b1e0403061e060501021213050d05060103030e03030702060f03070c020a090209040e01020f0a18030501020a110f0a03050315040204030213090b090304050d0b06120706031b08 82
    0x301542c42071524441c0050001c00b508807400c05800742040d80d2441e00c1d0b40590300071500155541840160804000e1011481401e001c10a0003450f2038240001d40d160100c02880118600004100001500d4004868000c05000c1c100482d0b41e0007074103046444120901c016004510f200f540e2108030300e4080120750b801c540c01403c0034100f0b40520400e21841c0c00041260041c0407107482400050390b504c00390480107091031480944d07550102c02c01d200940d0200364040c0d605a005010402c81218aa0161001d8888038504130b03c0001000c040c0d0760b510900ca600260065200055084e10140c1c00095034441119910441e000b00703078400416039580040d4030010340000c9050020603c405031740a00102100c100500c05401c1a46030b400054000010000d46041180e0b80d045c000100590001c0e45540903070a40080e504041c07604002c1103070385000600c02800d070061900010829600c20a0b00400d0340c150104642c0c0da5900c0e02400b03401005e4101c01800d10082e003203074a80c0c83d54414103a1030b04c2501030 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 33822954 1250 33821704 33821731
    0x20304060807020f012a0e060f070f0b040b010302040501140a0e0a0905010609050609010e0115030203040f08030403110c04020a02030d0903020a0b0702060703060b0304050a0f061b0203070c0608 85
    0x201102141c444101402c24000c6005007900e00b64680c00c24004e05c03180301c2c1c0c18015070b51084808012950000c0c10303c1d900b01e05200100d0800981541c3c0c000a46c1c40300b0580d07069095a800c6a483c06040aa141c2c40c0020840d0741003105201c1801502180035040c1d070f01c2501d0420490741c1700c4200204001d40001e1081c1e00080070f6509026094a0000c0d281e00819900d00c042510140c595800c1d094901039006480c00c56503980400149103000408240100b000c441c034203100c1e50505241c1c40c100011200510300340340d0008080b41c108800b01105e041074680001e08251242454a00206110904602000640300b1400404030b6407030280f08881325000c0d682c0046160403c0306145134080c04894a0680c01c0d40510090000418110584a8481e0105a001d0000c0d464422004ad00700c5034290030400d4100d009104120010b20009a1030f0316440d0009000c000300322551400700e0240070348004440300f06402c05446810180c000024010f42d0344250117000f5015142c460031100030314119598010282c9 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 33824204 1250 33822954 33822959
    0x10905060a120b03030c0a050606091e06030a080304060f06060f020706181a281202091513050102010b0603060102070302060a0309060c0818070b0901030b0d060f0921020304 76
    0x41c901d6080740c0b000e911408640c01d4543e20001e130550300310b10140e5996401502d00c403410490184185944901c045a1050a03130614060500314107030210541ea00704410400841c04966080242079440da620079107107981c3e0f19080c5405800b40500d0710440c01a20b0410001182280c003c504240c1d030409240c0c02803202500c2d200c803c440380c03c102c400050609803139400c00b05070304010200414005950446850740d5035041500178641a0304e5500c003940c411400c1d030008058a500003401c5102016403000541c4034640c00001911403025803810702e100340785c000784280d80b20b5504c42072542211800d800030040c0ea0499000e000c4540300c125000350061700254403d00051070814054462500d030362034000f5500b00c841e40d41070308a40a01441d4404660200108080c00460717481905441009001405506281064290303ea0203944411818142c48040808054030b825102400043d003090702031095241ea0810030f03000701419a0140c40e580308441400102c1c1c1e855415180c2d11500660055141c5403 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 33825454 1250 33824204 33824207
    0x3170901091707020d020301111306090f1401050d09030f03060e010f12140102040303080f01050303071203020306030109020d0c0915030f0f020609030f060a061d0103020d0c0315050f06010905060a 86
    0x107108190407640021088217040150701c3c240704021100954007400b503603500494031503001c03940c81079010740200074a485052240108501400d0119241c012810944980c5000140c59500031441e00002181c40c003d00c46080c503502c4600750001c440315403003c12006468600204252009000d07034072184440a904101881c02c040b1585400d500a940c0b07000b103d25443d1850342641d11642c411703000143c100e81481000110481954010f00c0120003c51400d0420b5030703098080c140a0310030b441407541c08400907507592029008554415401810111420580d00c1c1403000401240550f0030030504c5c0101007102c03004803c0c0c6803c1502e1f0480c602d90120850b45d0380e000a040000e5a080b0b800c000140042d52540d02d0401c029110241d602c3e0103408903150000892044078001e0f40207004020141802035000e04124003004e05690301130741c5281076901142440100d20b40c0270340c0300410f200180d0322004079070b4805600560207a102c449068841e80c548500454002d4028080d69902c182c1c20031011446a = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 33826704 1250 33825454 33825457
    0x3060b0f16050102040b0c070602060105040e1b03070906031a0604090b1321050703020c0102070f0611070b040b040807090507080106051317030705010b04140610050d050103031709010917 82
    0x300d2082d03002500d8540c8800e030350703d490380150314001180c5d40710b0b0320280300c0c5035010b1203100e0150000740d03400c1040001c080c2d101e90b920802090842d0090800c80b4801029840c01d01006014001d000018000c0903580e160840070710704103c07515002000c200001c240649414000c074000260000e00840050f125403007080d0301c05185001c1160841414441d60300440030aaa040c685c070982901d8081d214102403d01a04008201d551981150810781c01406030301810280300c0140d40c2d02e458031000c3e0910710f000d40c41c5410807a0f0001c804900e40494001800030b0040000c20a82d20800c041d1200c05580342e00b1072056810645014010843c018018802c451040c0050101c8080320342c000c0125035514a6040865103c030441d007050340d04005078610901909001d220760500702501c00301b0801702c515100420328880038020354811103038000d11081491042081d40c46079038200200300801e503528940503001c1940e0306d1500d000d188811001070b0b04250180300c0d400c50607811100035200030b9001c0404000c103 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 33827954 1250 33826704 33826747
    0x30d08071d150304061d0d0e040f02030414120418050702010207120e0411030402090a0207080d0c090e09061302040e121201051203190c1a0a090303060b0f 68
    0x403220304682500075903464507505904454095041d035543d04090800702c040d15800709001d0aa408501810701c0c644000050010203c141c074584030710b014000c0030004024107a10340400c0e000e18000700c10f100c00c0c01600841c058044e08507404580f64286140340701c9280340100d100705100004400c54086618105400c80d942c02400703480010b01d80340c480e0f81c0b0031001000d902c240c200041d8904080040354109440b42601c00340304880340354210700e017540c0040c0c02540d00402e14155250086041010043c03204107692015100c4542804508109800109080e2a41c42280e040d110a00086a00d4641c0421614054410b15440b000925580c0e001e00016010340c50b032800301803003400f00501442800101909014a40142800c0300394980020450001d020300f0041e2015002000840c401e2003444e000d89201292034101281680720350304012441d42c1006e40980c400351710704001c021480c085644a802861f11940301000070f183c1301d280c2c1551ba8060941421a6040b042003441685d66030760885012 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 33829204 1250 33827954 33827987
    0x609060714040e100909060e010c020307020f0f041d0105160306120219081f0c0305070807080a02070602160201030c0e01020d0c05070b160312050c09041508010c0518030d0807 77
    0x1504d5603103080c2082210f4140c94291112507554500a10300c0c5000e000b40d90b00001c00344025070510038590001030310703c0e01c486110b86c8a906001c20903286925160041c500750428840c1c60071602c2c01910f201030103000c0485503403108142d0b8048200065009100c0c18041d01e4075000c040e40100d0540e424000050b20302c10040f81d9800c01c40900050721541000130412000406803401c0781032545016003820703161250390900a242c2401e0800018a5105408581c005294a4414001c0d00d5802d500d030003e00c07481c034026001d203000040782c3c1c0c2e114182c01c028913070b4207200b0780e800c000c40c4907802d034102d803441c0c6400e000e0b500503040b400900d81c2d201c0c42005180b09160007541a03601481d5184113030585d50f48080740328540342e54101001c80c14160482c1901010312500340040c0a94076044110380f4240c46410740c0c0500c0f0b40e0f07640d49101b0844d01340c045041c000d8241c0e080204140e51440002401d00d8010a0744c1c680b42c04848409000c5500700880e62280b510160b031a50b60580e02d030302e90241c07900984100c1414 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 33830454 1250 33829204 33829231
    0x80a02010b061813140610030b0402070602040512010603031202070c05120a031409010c0f05030d0603030809010612080d020901110601060c0b09210d020d0504050609060714040e 78
    0xd01e40da450004040d100e8081101c815039100e1442403210f5948800c092001d114517010b943d0300c0500310007480350b034058001c80703054029002c41d80040d0014002c00c98180e4101d440840c0a00400c1031941c02481030794400c51740c07450f00122071350b401ca00740c1e125070000500045020030304002041f265000340c40000e208400382c1e9402d60321140440d02080090131204041d500409101003450b4110151400c13029418405524011540b030028045181da102d0042c20350b008a00b500c0701340302d424425254510510036091110035074900b0001d040d080c082d550031840e03510348500011598400e69408804a40c011030250a100c0180304000003504000031160622100703500b2004604c0052240764003800c100d403158024441070b81030503004104010241c500903480390003400000080c2011032400114002003681d503c0aa1038075030030103406602d6102c0c2c5440d0414050100300310b404a4464800d80e46241107030800e41d2800012100030300f40010311010090108810702541e101c404480d0342c020f07807600d9445c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 33831704 1250 33830454 33830471
    0x51201260307030e2709100b03030711130207060f0902031204050a090216020a090c0320030f041407080106090b0603060d0b090a020904030f090f060210021c09050a1b0e0103080a0201 80
    0x40780b605e04550009141d00104c110785e40980581c410f1711702061081d0011418203800d81e803a00520414000e0040c4104c40820120300108003a40440c0c854503405002404048416042c2002a04122404a01c2401500700c0030010a08001c10744003120300003070250122a1401240384020742c4a480030500d800111070206c1d002d6140c10740f401000b03084c0240001a41129030b240141102c5000e030002401503410031403002c04a29481c1038035080488002140d8080d10340d860448a01001002c05500c10300a24a001451300c1d4103500c61000c48898100601c040d011241c02c00906110803160168403040852001011855110095610114000440d640a201a0006804141c04a07001c9002a030f900850030601e0f54041c0d03a075401808543c00100d080c0e41410030107500c5514100c40c02612a42c00305120900101c08004c000b1440314029040000b4151810007907210011301600340c50301180a442a184044901c02100880743e0540c00880703c2e90a5948610881d032114210b0001c42d900c0f000038 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 33832954 1250 33831704 33831769
    0x607050106032603010f05061812030c0708010b01021e011e0b040c030c083702041a040807090c050706050f01080106060201140402040c051201260307030e 68
    0x407140910f0060000d40c3c200d840d000200c42d620f00d810000342444a000f80010031103040c020b00c1d0081501c2040300c0c4503131100400d00300f04ea41c0c8201591000e60180d00c02c40322440006010009113201207100050701c0071542c45e9409503080c1c0c0c0301020f40a00603407109903003260070b140702d00c1c00524104080001044a40d41c003c003d4841c82a81e04400d24555922610540c1d2440c044c41400207505030360405020440350100c018100308002043d0100c1040900341007003039404d008041040703000480c4860103805044c0c1c65080000d410a004440c1c41c09610070407070101d07101f44015102155450002400ca40e4101a8014050039541619000f400028409400040d10301d0160328496001040d140202d507142100c003070b003500c025030f010005592601d441403060154482e8820341c881d0701954041a800000401180c0303520982440c0440c502003400003290b00302120179008050040e20540102894080300103030b48a129030301c030080c0842d801940041880c14080c00329003101d8181040e182c40c0d1101c460f02c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 33834204 1250 33832954 33832961
    0xc030409020d05070e010f020703060216020402041401020105010f0e06011d04020c0f0d14030f07170f09061006020604060b030102040b0c03030105090705090303040e0603030d09050a03230409050606070501 90
    0xa1100910340b2401000012540100710a11722a001d180c1040c3c0386140307282c061b403581c6080c00081d140f180c002450350714034401e0745081c41410380d01030400c543d5140d468407810b21207a8201101030043d42030100005009205100c91010b49016207401103494a0f05001901c031070301e1407008001d48140c1c017446240e040e92548040d01400750190091b101e13199100020600305036015112405004210303144000036820030080e03c1e840710402014005585594405a586080750302c003100554080d14204000140c030704444502a0b428041140c1641d2682415a650b232107031402340200683c0202c000401080b1190802c62400c1e2024000528198840795803940319030000311000c2c4035a1001004010b541030060704e01d981308c901d40c030f0301034108898600003944a103e01c1c41681c0d03031522504007140c190b5506000312004070080450130800300140380ba0298454003500b405034003213281110611400e40b800708040130804c001051803490603007400e07450b02c02007c000e810542c00071000d01143d00024400d22 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 33835454 1250 33834204 33834217
    0x1401052214150909061501031806060b071b060e0904030306081606020f0c030a0b040309050627010806010f0c0c081506030601120201020705130f09120e0303030411060c03040902 78
    0x4009180c1010940030721004800282c000c03182541700780304014600d8402d582804460409190110300715082e400b040801c490311103409030102d842c1c10b80024040c41c0d441d00030404c0034407440071000d40c0001d055684020120030720580004c244002d00c5a01103107841c00340260b2052181c01c2c002006c2e5103ca8040c0d00e81099560030703200d810008141401207079010082c0114061002c1c0041c202286a5400f098a842c8808070080003d0001c2c00030404060144c00944064900645104c0e00c1d00e035000314010101240003015503a00303400845610155100d500c0703545c4204c8046e120001d032058000005c40d01c03c0e52058003507441485407540030a032054140041607450f400c1d102c10f400355003401c1d402c040c03d0001c103900c04001c00a28458800040c0d80100d003500850740126046504500109000c1c8080c00c0c803180c42c440318618242c0c7c400c0030443d00d160900041c42c2240d81c1e0307164105040b418075a90340b0050b00c000c1c00d00c0c02074070680c116514080004101c10b23032201050328100f0f691104070700305980128 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 33836704 1250 33835454 33835471
    0x90c080c011d0604052b030e04050f040b0c0f040e0901050105010906020a050d0e010e12060406050109060305060c070812130314030103080901080705040f0303050304061401052214 79
    0x3008058480d81c0c03100e00d0300385002c00b600d042d214010440c00050b05a1103944141405586c0c810000e088188401e000101e1a00032100403000c90034483c80c009100422240c000b61040b0320300004600ba1400c0f0080452140b5403000020095490b0700ea070003070140d0880c5902c00055201004003148004910304100d000e00740312000030a16505040c0050034089041d0040d50440d400600500c0200e02d00107003120501c0a5420a00042982c10004a413800d014444007a0840c0c12207072070840090002a002d4130440c0941c42c100001e90303c0341e41c40d00a0760014807001d000ba62040e00454a0b56891000070300249111707640b00740c03904440103204100c4020407500009010703040e005c0300b4103041d000b00c80001c3e2100740d02c2c0454510360443d40c60450354003600c0241c9040244070f10000c0c10860041084501a01d501c1c030148480c1079581c83c000b00b0a90007164101e604508000030810394040480c14581070f17540003400d07018410000300c0800040ba00000d00343c0401a11504840301c1000310804050044091 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 33837954 1250 33836704 33836713
    0x1f09030204050603010203040f110102011404080d06080c0d020609130501030503030714030708152107050a080a172b0e010b0d020a05010c0503040b030a0e0706030c09061101090c08 79
    0xa500402086074002816103010343d00400030400000c201185548005602041320b0761082c00c0c0f500100e00509002e9a048046141402807100303021486000e0320138100700c00818401561580c1c0d1854a0340160b540da1130b040f0071044812401450500040c002030400175065124072404006444144d4000b81c0c02526a40c1000003400901c551104554000c61520000b80740385050040e001042c1d03a000410072880300e40c000303040300815500c10444c09048910144401c0c034401d140d650207502d80c052442941d1103100c03c80b80002d064940420000c940070340041c007184156101800650443d8480c080142e59503031201e0400c415504002102c0d00b84107000c0500140b03407065181164210760549030114883e62901c081c000040e030b2079401c0302e01611401c0c41c3c2000d202460780b03481c5166006640000c45180b4020040090091481d480a0700105016085401c0165101c2c0e007941290007210001000034403400080c42454001c071690b4404032401400002e515a20362102603c4512130b80009805800 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 33839204 1250 33837954 33837959
    0x70c030302070b07020f040e1504060c0f140703030c11010f09030e0d020f0f01030e0109050a02090c03040510020306011209030210050114030709090807020a030c080607030c120b1f09 80
    0x207042041c44042c05244a1013413a02000e038000a0701c0440d400c00b800d00c15500e50040c80c2040d0018001d0b09902155041c1c503401d0f80c01c1c9482e00300042d1446031001000101c0c5048040449031051842022401c00040414940b04080c1c81c102d01030f00000c480302040c041c40b0900b1180d40c02092098403081640d41e40c000071340e0300d0b8a02d002400c1c1c803003110701c040c440c00e5a0200c2c1d9016a90b08204c0e91031a10b401c94903a484025040c006901034081c029150304154600354540041c4000410300f040d0340c41c401c40c0c0d032a580342d0312120034030064001514003900f02d03400b801c4001100a44e581c0119004201410151920000030003481c00750b0350b100d401100140c0042c81c00314954003150240d01d015000181d242d141c00402040482e640d14090310071a08190b4681c00000140400c80d030895a40741d402502032074803140c5038240521040c03490701c1418074a100d40000200c10500c46c2c440c204146a459691249016580048030050071303441012540c001412a10038040d8040f00030380c0881c18455842d0b8810b05d91 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 33840454 1250 33839204 33839207
    0x10f050604090201020d030c140d0905070611060403030902030705040e0c0a05151c090b040b01080f030a080105060a110d020a0c080102070f0b0a11030103111f050306010f1202070c0303 81
    0x1200548440c1c003440c01c1955a000503a00461800b008240c0703032400223103031000748500721a0980c03401e80e02d0703204c1400010700120007072103608107481890050044a0300240d8910040310104c014900c150703c01d42041010400180c441d030028500c007030000f411a4a034948902c000b9080751010707861100d1039401481d101d100350810140f60802132404580c0c64402d6401c0c40411541441444030428000381d2100c119040c50b2a0b0743e201c0d10059404c03003520700062400e031a002c01321210078010a401f61045815007400b240700001201c803c100a5500c0c100c2a034038010500c6103075000a010403080c0316142c0c01208072303010700f004229000f204d00c1d801040060003600304040e6540791900080401d174010046031000c55010300352411210307030026528900343e0301c00e021320000f00040786c43d40c003a40000200000501000c84074000e00c0032811150b01c4004403e80090128800c0560512342c04a00240300282c220760140007181c980c0074940c2042e800c003800d507a5061080b82e000b0300045546e111051005d00615 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 33841704 1250 33840454 33840461
    0x2010b01020c03100b0103020408030a03020408060a0209060703080402180a05011e030c0509070512010b07061a010801030605090102130305030a09080303010803070f020a0305060711010b010201020a0e04091b08010f 94
    0x1080a0014100452160000ca0703103038030304003820201554581594181e1644030780d0440c2c0003809a401626214019040014085d50091081052034072918020a010780118400c58039a990024159881c0c68036554054842300001441a42d000301002c13042c948600c401c0202c1c61260140e140d0015082d0306141c040340c079002550b0860890b10622090510000703900c070840742e0654100f15040070607036590502c1142c1030b2040c808501175a4030710078000180c5d040c01001030300f145441028140662803003000800080c0994094590008508100400100d4115417101c0e41290312040094500900000e01c81030a60a9174002c403519440080c41300d5001ea44400c2e4100a40710040c040d601d154507000c5c403165203004200c1c02030140440304c3c1c000007c641d90111198015a44003058411f10303e0803a01c00380c03041d1440d0740381c441e295080610504556206208441020702d282d110017030340c03440c140203104c0104018807003205c00c110480001040e003610205034000401140700041542007500724628241d = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 33842954 1250 33841704 33841721
    0x1804060801150509090a142107020906010f0315080c041103060a15180b030a0c0302090307030f02040207050102070f060b0d0804060c11040e01240509010b0f04240201 73
    0xc5034036040e141e24000c000d410b01d60741142c20445071319506858065280b402e0170400d4030b006080804d0f160351400d0300f0754085400a08140c0b440d800300d0804154442d6034000c0e208076031000398004600400a19598000e66107503c2201c00c616000454204410305661605105e40281d59158421100030441e0b14141c001c01c103142c1510341c5034604500304480844d10440c01e500911407441010011103201d103224001c03480a2200e2460741100070742d92281e441250368810b41d4240900b505081c190120580030303008941c0d06120184c003c0001d40e2a64991002e00311041c08202c0e4400d0b0200920785c0811406d0014241d840c1c01204581e101080a14242080340c986d2008075000308603100e8008007207113010050f1070443e1710314203043c4004206864004400e402840c450340d40245803541e0056020301c154019140c0d040780c480c450004550841c00e0b210304402502c00e559101c41d9080c014041c9140010141015600c01c442650906455182c1c1c040042441761644020b003989003910b882c0300340d090180400 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 33844204 1250 33842954 33842969
    0x9090a090803010e0405011e0b010809010c0206071b0c060e0a080a170c01090501060303120c080112080a0c060603150f0216080a020703020307030b0a27060b0d08180406 74
    0x409016640740d62890005100c1d0580700b105010000303050200a412141e03d07521903070b01954074001c010201000074201749008a0018412200040c0070040501c201180c41a103500206000c2e950000100d4000810003800106c000e005030080c000030313240c000200702070a0292942e03a00600d0300c1051021420032a4000c0c02d05502c821030004c00306200444401448000c0c1d005a55609104a010b5000d0024410010055840d16100106050348600025948103c49070180011031030b0060031600c2034020f0044a02001c44181001c0c00207500f20010408e0206a04292820310003a445c0c0900702c0320f0650060740c0da0014500c1c0316082c00800d108007110000e620200310b040c04007900805416102c0c24800800010001805081d454000c01c800e8000716402021150015164500701403a81c2090b01d0540c01d082c00c0040400b42d502c150400800000da16411107140f10405850b000080e200e40c460882e00a140c0b41d0303403180881d05400090900003443d1400480c540040300c1440b003113411641c0046c8 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 33845454 1250 33844204 33844211
    0x605011403120a050d0504030903020d06090209070c0c152f100516140f0a1e0c152004060e030601080601061b02030f150a0605010503010f091505031209090a 69
    0x4003c40e0000d007030740c00521020000007402d540d68502174036103290a40010f5446800c11060104000b1690000c070206031007030720820002d44070b000c42594a2111030000810020180405008030281e00e00c100c402482c040c0740c48412003c101524055141b880e91454020131848501e07480184010401c50780d031078580101c100003070b00d808001e40030400c940841650420071030b1000e0001100541d015203200d101080b406964400314404090248600c2e040b01e042c2d80d890f03881400d59041d00810020001030303008443e0b441c0983d0080c14060080c00410691350043ca0101c180ca641c07a064800a0805000d05440320161084035400305460000c0503844003041d0b51200c1e00501c6440c0d842031000c9d0001142c1d40c120444051648006800c100c41440342c00310500c10040c07580d4113041710081e85170040340d0304d0f4010070170b090b202c0004644c913210074041c440180e4640401089007002903807041c5004003010071a030150584440001c0d007000c100c1c420304401c003980030580c1a603910f0f00000450300a01c1400040 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 33846704 1250 33845454 33845467
    0x60504050a11010c08090f01030e07060504031e050c1003060816080f0d02120903010f050f010302090709080307030c02120d020609070b18121203040803070305060402091806010507060501140312 85
    0x41480c1c42000b1b441d6004401c68440300c0b056034040d0308403508081400007a50640740c0c690700d008040d17030424441600c3e8081c11403040303281e011401400042d5260000007a0003911034540c240b00c02408007494000030540d0310303a80007640d414240014000c000303442c003004420342d260030384440ca0b00145c80303500c103c40e80003002c0300c1840c1d81d000215031011290b2214140d4848000740c000074010310340110074844160600b0100020300e203c2c00304450580e84200c40c15182d039250203008690340c680e18010304090fa03004211850209010f10304681c80548014200130340711107442c0c802c500346503c039a13840c0050781c40f020620020220a000c260040c8c46004107960600045401350f903002c044200e400707400703088481320351100104240054514841e200c204c650ba40d041c9858001510381c003c45a4800207072401d40482c0307582c5024001c40e076102074024210740c00d040c2c101d40514040071014014030305210f01046240005000c0e03002e800d00030300c84c100301540e181c2160001d050506a40c0c001e500c07003250040159 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 33847954 1250 33846704 33846713
    0x1020d0f08060310050a0501050117040c0b0702150705061008011109040f0e06040f15060b120901060510020609071703040918080d0b0a210b0a09060504050a11010c 72
    0x246040300c65481c1207051038607803501007130500c1c103180500400c1500300320802c907000c0c5107500010b040b94020b9a0700030a500080441c912015000c0e81d0041105850420421102980364003515110307000514850f4144500c02002005501100c030407110340c0c001c035082103000391306406040000e0803001e009000300e020041c4a40c0f4035118070740009118640e1a501b0010000280d8007802c00b0360f46407421a01c181c206824421403841d2071007001c17103104c0100ca810042d0340c0043e004074012186049102d42c10201103000d00e003c81e6100410b030304055940d13010001081c0d0f42e051003524142d000b0760050210fa0030429580d0f070801106800c81d00164000c03d031206c4181d4000011102100d01d0300d0030005a02000369524484171002e01c0c0050721010b00070851489810b03c541c01209004070484850b42c003c0d69600c465030342c40000001481d249500c00e00503102150042c61180e81c456110300f0005280b8160f95201421203030140c5003914540d000d84850b0b420007240e088038603201e420900300000c0c06042c036502c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 33849204 1250 33847954 33847967
    0x5100f0510110f062509050a06030906090803270307051f18030306080f0f030d090305090a030606050a0e06030607110c030609060702070906030b0408090a1805040b0601020d 76
    0x14042015102141c8481c2e18140300e03041120511509540c43d60a004203014100c6034100c00c2c84440700342c21903032501c50900418001d82180d001078411101c0030f02d821810750041c2446001690003c2d01c4500007400640c81000851090560b02c0c1d40440c60080c5450b100100c0e540070540003502d0788204001d50104100049601c2103031b12340901402900c2e90401c00d5005842d20464028690045401510400d40c00d50002000e4440e054111000a40722401495a80b441075000b0403450701b00308a010450310f00b5800000c440d50181c10240c0c600b00306400030030214555644107517001c2d95184018002440c000d0010802054032501000c00c41c2000c80000c0d450342d902070950410710441c04404d4000361014000c1c0d28580800600350b90345858019502a21048116030820060140c200301285030b141d18420f05042c0c980085802c440e0f941d071565a04000d5102e0720030f01d41d205407c480001021240c0540d1148105a5640d02207200d05161801c0c41c24000d0180909041d0b4200c0009151040c0d48400c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 33850454 1250 33849204 33849229
    0x2d060103020f09040507150201050f070c11060a050903030409231e13020405040309090608030403050a14010608070305071a12060120030d1401090e0d0804020a0504020d05100f05 78
    0x199a40b80d02e0300d842c617116160280d20b030300400c1241400a00c041d04950190702c050321a074a0031f00c0e013017220750380e2039000c64285150500017864218081044205420f0200c041d00000303846013020340c0f17415031105c002807075504140d01464a554451180500a040c280c0485c440702800322400c0c07001e07045c220b0511096443c00d840c6281000ca11800040c00b90f60160502540c070340d00a4800c00c6a4103207401c1c010600b461501894403840d00344500000d02038000011501100c3d04200130701240c100b42e50306c15040c4101703075103811825926244082464203052003480c00862082000305039862811114004c40e801805c501181c0c26014801c480e174116200b00c00d182d001c0400d2801060488030b42c0000704100040c070b08150180e11003c50b07640c130240d00507808800282494030900501e40c0c3d0b00e004003020798450018400d99900000b401b0385e4420701a040303a84d000f9100500c542d10054460300030800302e802c0403405040c440d481d041405400220550003a02601400030049641401d0501181031400400c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 33851704 1250 33850454 33850459
    0x913050f070c0204060906290307020c09130506090d020606010c020f04090c0e010801020705070b0702030703021011030307031b0f050a18090c0503060310020301060206010b0c0f2d060103020f 84
    0x540c02e04542d034941c000d2020b0a0840402c0000580300ca0018500d6050040c0d201c45105018000e464815040c80503030b4400d408c154010014000140184900e64a014103003000d00070203003d280000450501141d4400c051000003041c0c0b0b0410710400a240c604007600b05814040310150322005078603610419074410000340c50204410703916250108800030150b02c0b00000824510011485e0a01900207140c4140188100c59005464404c0403050788215200254554071801c030070401400c04075203911444180c0e0a000140204010780d4508692080b110400003076641e035100ba00440c0780711401c4101c07074460b20b480204903100b010050003070b100703000000e42440701c240b4a03045600c40541c0c403980036016501061140140011024100e90000c1c0d40c1d9070302ca03000d200340b00800d5800d14030a507412900395074014001c50b4680065098140c2c040e040d400e0b0f882c0140401700e604028108181011000701d4070343c0680403030b17008221b1800141511a10041500700e80c1c0104090782e1019254983c08004 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 33852954 1250 33851704 33851717
    0x30f080f0414031902070501020c03070b120903040b030406020a0305071806030b03160e010603050106050310051003180b040c0603020408031806130f0f0e0402010f0f1b05030913050f07 81
    0x30102c02e1450050103607103441c1100c050050143e560380468000e0032500c0a0302241ca00d050a45c04060321100303507000304000314005002040c81360481c008141d80009801094a1915071240c0c0d581b43c2c0e82e4011101541c101e900001e04010b16036051045c541d00092502c1c0c54048482444501f4003070751840d01c119410551541030030011a901841245200600c17040c443c1d402e180d840020412b68002403142d000840c1c40c2100005440d4014422030b4400c0c00c44803140b495140c2040108480484002508820580e070b84d660140355000c2800c040d08600d0140d07145003070a2a052920711440003240e0041010980103004c2088681c20000990719200442d8400c90f0800c099100881c5141c06454540c0013014400c820001c0c0c4083c08000311400c0e10700005c1c0c503503c9140c65501c54054090280c80003800911030700c04030224144144024280d01e0b03810b01e8080f010740c6400c081564407490303080b81550590400a10101c00c5d207001400140000c450b01000d1009203400022502d00d2130b0011301c844144280c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 33854204 1250 33852954 33852983
    0x4020909070f030b09060901090c0308030403090315090c05040b0f0f130c050301180b0108010501030f0b0301060b040905180c0607030203072001120902030712050705130207030f080f04 81
    0xc2070052402034088280c18244807039a90600640414082e00c458a00b4054030010030000001170140b02000398002044070100d91450751034a0746584002c3c02501007002c803c0340400000c01c83c95001c0040d80328000082000380090420030010812075000c0c2d40320314580a50034003191512200011200002c030303110b080c52042d01020070305003440c2800c0c000010b80303400060000c0b581c112028505840c2000d94000900301c01c0300c0d6010485414110f140c1c04101c0c500e0041191398440d800181002c40d07811000304440d403d8601003400c0d60515005070080c40d0011a050115074180c0c8161a400b20740403040182540441c00303083e031a8004030401a00a46c80000d10f80103060003003040342c4405511600c10404940c2e400c0b170703044c02001c102d03400c2c500044200c541d000704c500090054100640e0010b025100282c900f502d04442c0c9420307404110742c1c6018002c0d0000d00c07556224250f540c41c862491007d039481c80c1ca40750040c00d1a1071000c0d85001e0080c00d005000e20042442c0d0581da04c503034000c1c09443c0282 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 33855454 1250 33854204 33854221
    0x5040503010908070b0f2401110109050105090f06010b07080c0c03120c120f04030201200d02011a0102030c0c060306030703021e0a1d06011803060c02070510030e030712030b03070b130f030308040209 87
    0x4810061409c615030030b000a070350400c80c0c1544554407841c800c0b401c0d40c40c101100b441c029102d01f020320641c0e0900720140300c8078001c60035403402061071a0907202150204429080801c0c103201d00c1510300000407601082e1603004501c24001c0c0300c41c03200c5812000f86820600700d50a1030900550001a04006040300854010000c080c1110b103ca0034036000c580500c0d0150400902030b0441404810000c07010002000c082c3d40000252507442c5819005014500400f00506c902030708000d204642c1172260860000c090b8454101da4500e842d0702482405841c05140c0501c0303203219003580100316002174a1010701c44180c2d1500c440b5040703103007480d000c0c074420324400c84610505215000070340740302ccc54200101c1d00c140d000542c0302c0c115002954a040004c40102040c1e044959040b007408580c2c00c10050b40b000240300303000d00b01d118810b40c100010004142400300c0d203040c1c4141c000c840219400540c400c40440701c260302c0d10040264946040da601d09583d401002e03000c01500c000e006800030741c0803c2104 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 33856704 1250 33855454 33855467
    0x140702030c0a08030408010c0f080a0b13090b01051009080304060302070305040e010b09040b0103020301080d08041704180605091e06031c030902010801090c020703030c0305040503010908070b0f2401 87
    0x2500002c20001210392030340d051035260b500c11300c5840b01640c40d01d102c8440311801081c2d040d81001032a2100308540d82e6420440e40a080340001580d03109100d0f014000700e81d4810b114000c0c113680948610b1900d507040206004142030301c0b02900d0180201c0000030055680b00200320341c252811840c01503120300c01868155460700494000f00e444501d07040021403001403100241c20861402c4800344002c1c04407500540c200d200a004480e680d40110751081c4d1103a00031044650000c0c412402e051f204c2000c001404100c0e00107400ca4203074046130312451040e80002e4060000034100c1150002d0315810408807145400700c1d1411b02e4113220103480e0014611b66030034000d040c60031004650b5018094040100140102104901280030404140010811020b10300c40c24071504050340042042c2d07400c54805032403400c960307503080741000005c000201d241c0c0c50a0023419515032181c1580b5441d0f18891401da4100100208041c2c0748800d05010000a084c1001d00070302094100c5c1c590310000440e00c0012550f2 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 33857954 1250 33856704 33856723
    0x1803020307180b0f030606010e030c06040312020708121c0b0a06051c1a06090604080703050601052706060c1603080306040e1209060a09030510060f09060614070203 72
    0x60007600d8002914200c02402d00031034154604040004140620400102070701511a160305944600000b40d22940280907403031502d080181210759181840d000079074964020740003141d503035103200301c900b090940402804010740102c00c003400b855170b61a42d017100c440c09440d1564015410011510030346000e20703401035100030740180080b1070880d15504041c041e60302001600c51844440009603040d03000724840c1403518030038091021501802241000301c5604403540f40741e4031040c100400100f0070720400c42d00d00110302c0341000c0c041e05e604d09020080303085801840881c130032280d0100310800901c45658242c0c020400c0341c05948038403071b03a00410f18100002c01c40469903031801c4008014030015002030340c41130208540a0100d00540e20207181ca86200c1d082500c103092041c002040b81380791441c042c06051107546030a941c0070340c1c3c0c2d4991515141c0d030750506c1c00500c0e82c1d40806008400f00d022008028001500c02071065902c0d001e0000d100340184090030414100c042124411540c0c1489058107 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 33859204 1250 33857954 33857959
    0x30c090e040b01061115060405060402210403021006050f0907020106080d080603010605010507031407020319080a080603010510030602030a1b120609060e060603060406090c03020408150f0403180302 87
    0x1841d2030145044850302d1028040c1350082041e20a0588101e00c1c001174100ba00d2024809040850315000144030280901802e801d50041d0240081880441c0d0980d41050902c105e0f01003000508050501a0078a15200c0c40700e0790403410074205115940b101e6a080c4087c03e410b81d90401160b54442040b4010300480d0002c00c5540250003440c8110340e44040246e001d22000c030020040c4580d21070064a40b4464104010041000d0614524a958146000d00b60580c00941980c40043c03158a8115100d582408100c61544000c9000c1307080c140e01c904160b51121080d0020045400c3c00744804482c18102d21000780f0007500000010324951003500503020a407405500c000c05124088005800488540b12101d01b41d4a48480090f00f9016401600102c6050300803110054a03118140011503000804250300152142c1c0000b60781010341c451400381c0040c40e0740041e121410301a0311810140341300a00720024009074207103c0d40c00454014a90055410306221070118032030760040b50b140301207610182d07 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 33860454 1250 33859204 33859229
    0x100f0c050708010911040e06070c0309030c0605120901050f180f011103090610050f04020903011407030204050f01141206010c0807030c06050a0203250e130c020c0d030c0201030c09 79
    0x511410540007040c403580300304a1200c0851028051001f2604c00c105e41c0000ca1740140f020a015034028411811030324001d2074a2071030180c0300c0d1291040c604941c0d1084000810000d003021a400c050f140c040d80002c6100d000b032065052980704046001e00c06404000c0702622264600b00d560020031130824160607100091010401c0200c1940c500e40044a03451740c0350065400060910869596000c02c2c0c582c003c184a0040880a051100940001032515015943c500204800140c0d00d0b8046c2c3c0714440c696400f41e5214100400c0c00201001072500c141800070201d45a01e500e500781090760f181c503140441c1c1010580c0c680e401214160711101021308080000190101030640c0042c03154a4076025003018806903e450004008920003290450310624200c441040ba0480014450207912038601d000110745d0946000603001e41e48191041905541d00c0c14160f6030190140100d40781c004e411103100c40046802c0d01e02802c404108400281095994125128014028041c9c2c0c009403a2075031004 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 33861704 1250 33860454 33860459
    0xa120504120c05011e080708070909140a0c03060501020a02040f020702060f09010f090506030609040c090606030b040b0102030301030b040807150207050109020114030c0417120a090e06090402100f0c0507 89
    0x441010724074040c084c0015a000c01c1000c006440401c4920b1102c1690349000302c5540d51001100c1304400a84010200802c142000540161354040d22441c602022101d48007400c010103040210364400c614103051504201082001c1e0b0b03008541095000e805440110340414038030120b0700280700701203000f94010004600903981407103c4c4041c0c03542c060280c039582d0f030102a8510176204800c41c2c1c401c681e8000400c000064070f905000d50039079009441a00d6111a0a850b104800181d07251500180002556807a00540b5844c0038041c0120b105401e0002c0c5245504640307441c01c8884000388064031503000040d0032400c02c482524442d020354502d100c215100d6031146841c074013810301e00300141c0c006082d030700c4410204521403041328080c81002c1500b5250500d850041c03110821018480119406503480703541c22806404000c09091200380e65040b8400e040c440c0c0c1030840c45024044500400c040e608000040e00d52806201d011001810300f64000818100d00701d0b04c3d600d20840041030382c0a06c4200 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 33862954 1250 33861704 33861713
    0xc030403050d081801110706020a09171005160206010b1e0301030309140306010e0a150b0408010615020a0309030b04150f020903120c07120203210a0801090b030a12050412 75
    0x254012120301400203120549900d01074284c07207504850706c9040504101a50015203e5030091012201a003021481031350f85400c0340d0421900740318203000c0c50700003003212814416240b19032644101400d172460150200300318020341d1140c0501415010307107000100c0c582d9801303100071030b07c5a000c60000100c0c1c0d60340e101d140080584038684145600310b2006034441c0c43d20716000c22280d050322501c0f5a00d101590f11f200600000c1c0c03410a89500c43d100c401c2d0400b02e034082021004001900c0c195001150451401400b0784030a940c0040843c21500036088010020b50b0240c014021240c0201003200c8546035401c01c031400f0000743c17818060f15454150b2450301081c050300a010359000880a43c2d480c00103201180015102d5280300c074869400040f400d2101c0030b850f10301c4041c02d0340050700303c8200304004440d9030320385200e02400611070a80404e00100f000e502041990140507003c400380101069500400e581d10911180142688111811900302520900c01d40b00107225482d86000c0b00c2c00e05061 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 33864204 1250 33862954 33862967
    0xc060f04080c0303010f170609120f0f0c03030609010608010e061306090c02070603050c0a05070210020106050306090c100903020d030f032c010c0e0603042a03120e01180603020c030403050d 83
    0x268403000b80c60307c040201810b402041e6540700c1c00c0d4100190046100117091039602d1f030300c40304d10314a003103100784000c4880c44298006894080201d074001d60f41c904007101001b101c41c0d0140c7c44001085800d100521081806000050704900d003900c0a01c1485c0c00115030764040c011a03000352204525080880459650005400c4111134080e10100143e4443c074100b50400d100c2d6144580200d82c00b0412800103041c06c010140b100c20891000088a0b621200041d040100540340c56600b40d03c03a80e2040d000e4503007a8001c640500e000d003000d0f0326062560b4003041d001c0f5040d01c4041c0c18000c140c00e074651b94600075000080c0c103040d039103000b206d41030300210004d03c0c030700320314005400395864494a04001801401d95040c050310040c2843d08660312990f82c1784e030030056008611b1030181804a04240b8003042c1030808040c41c030494501c030b014040c001c0d0040410042e1001281004220400c0d1710164003c01c824070142d6070b1500d409030351001c05000c0c5625600c11507000504502c19205620841c03039214a = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 33865454 1250 33864204 33864209
    0x804180b0916030f0b0604031104180c030c081b010309020406030506090f07090506060f0a03020f0f0316080c090d0507030503030a020c061003020a050904020f03010608061504020c060f04080c0303010f 88
    0x46041015491825450782103401e4540206c2d00104200401e03c04140c42890480c40c0175030041c0003141c5145241040809181266000c0b01e10b201405418400c1003200f80700d03100500000d070001d04048003a0049e00410121520b0701605050b40c0c1e04190040d0f4403203401920140d0342080c21a1001d0500c4601c03140d80d6181c044043c8420b000d0002c2c00300c0d40c240c031801101c0c02480024410750030264011a2510742ea400100c2e020185a403c2100a80864040028001c205480741e00c540c0c5900d0070000543c0b03040c0c81d400300e003001c00c0f071258108502c019a000c240c0781c9502054960380d03d070100510b495480d1280c0c90700040c00d203210210810021034a00c0d001881d41c61a500251411925002c2c00032210102600000b0740c0a0722258003845181031002c0c802d44e03ca80014406071650040b040842d08588241c1c0202400350005400c00c0305403a2205000d4441003010340c0c046207440b860b040b4641c3c9800c07000d0656440c401c0c5250110341408809020384a03054405410b1b01d90302c0d40c1d1400003118000c4a031 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 33866704 1250 33865454 33865457
    0x31606180b10091107140709050c0904061202011d0102190606050f010507030824180a05150618030f030a080103020a0b0307020303150109120305091c0804180b0916 72
    0x10400419201e00381d0288010313040c3c0e0300305124284007903a902c401204000240051191192100006255030b0a000310740c00389400300ca102d030b84c4d40c1c08141070105980064104220340b49242c1ea00303000607603010101072408851030700302c8a4441402d000403828040080b02403248883e0360301640301440505e034480e070200c0b8030454030044d941014034019030f0240501c910181c082608000014800d1006050744c005000008100f0b0f40510034100000702042e109001e1003070294404003c00c407140d131843c8261600041c00a5580c116890b5410006449203d0058000034440c1d4a14021607203403400c00684081d0f04924042c2d0781c07240310303070710000b848100240b1069208500c04000000c80d10200790482e405900030394050342c07869607042e01845503003d40c0c0340801d0401c100c00c07070001610045071000c800440c1c071982e2550303520107000c01041407200c1c1d401114020010014459000036000c003044a040b00d0710b20034541c290901204a0000400d07603a9551504404204100041410721807a20713071078603015 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 33867954 1250 33866704 33866731
    0x31002030114030606010f05070314030403050d0f0219050705010b0603250309080403030e0a0e0702100e0c0109031b08060a0501030516030c060c02030109060606020708070605030603031606180b 85
    0x4002c10103640d1842601c60502140d20450600e200d6449030006103460b0b03003c0c1c10000e918914a04c581840b90303104803800e500040004c2100d001c9001c0500500c00a06001107040d0b08200c40d442007111a03000184802d07090000020f12603040250a40000303078a950300400e546c0d100d01c0c041c500c24201a403101440803840c0310f4170a9111081e4000c0c0f1424250075008031105c1e00300f83c2199000d440c6003112401c5c00d4750000c2c545000041861980c2d01c4907200f41900d1740541030f03035040c1030360b06020f891451030041540d4000d60340700000380c1d038080144011260840b1840120103c41090f00e1291020340e000340d03102c2e018241c100b110000050b04283d0403244100c1c03c07510700107800035035040070000303501000740301c003511201c1000340c24416141082c00703d000800000b942840c966900f81203804c554409009070304070ba0b104205c0780d2000e201d001d00410407824140d00e54a49140069182e00c81c0140310044e140d072000c00c4109103c1d2035070183c42401c0060840c074403059100c1c01c00b40480f02c0c4c125194603143c03a2 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 33869204 1250 33867954 33867989
    0x20703111e12070305040e0a021b0102190c0b040605060a0b04090b0f010c020310050a0209030102030a06031b0806130f08030703060e0108010905070302060c0a1e120809030304020d0804050310020301 87
    0x910000701c940c0a50155642c5d1300f410b00f0400b1039254004058240340340941c00340030001e0b2144404800428074051075000603a2074045e8040b151061901107240c40621003c4010f10021071403420900e50b106900c1200096641d80303110006480600710b400100d0900c901180108510440e50f000e601d441d001106d0036440c801c125001103c50204100c40250035030801400c04c1b806120350f811068000d0340c884030250905240341c000c0313800ca800403100c030280582c98240400501840100650790340c0418244050840c4c01c140c40c0742e0399140041c010b4500c0d20003e1030f03120103100020040300c132541c0d40003100780e54900700700300010701030500750146023000e403203900001501210502ca21000740d503120029080440c5150200080d0b6001048c41504901503000c008002460043c030401c00080500d0403086101c4071814600d02c4211102078501c10320818070f0501070101380000981c1d41c815812100d0910b5a07805d4a0b040d10940150341c410754040c41031a0140c80d01001c507030050f6040c3c440b81c0246040505 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 33870454 1250 33869204 33869233
    0x2060a06060507060b010302042c0702010203060a1703070209151e0112050402062107021606090510030f0c020304080f0312061302070c03060b01080a1a0103020703111e 74
    0x15441c0c818440425000c01079a000100c3d0f50b00b02c0c00502c801410010b06082d1365807000d00f04900000f0320032102284643c5803803140c21107404d041c0c4d00440f151000318110303d0203802181072170030140100140723045c0074612140c00c020200100c62000354060912001e6017007240e2660300c0c1440c45211a40318a40c85410340c8800344002440d0900c0880c140c0d101d00141c0c0300504654028130001d401603800403402c200d006129070002043c2070f100c1e80e071a00385403110b18100304c0080c101480b102c031045034400001c404000c0154001102404d44004407503c0804804014040c0c0003088903409040410303081c41c9d0030a200c5900400036000f01d909800981d081c8410001100741c407442951400da07148040000407038403038200314003007034200d0107030754401450008140c5916105901c240d00444440361100e070400400d59001c501190000e10700102445444c0340a594240980c06801400e4105a40411100e007454450301078003e902041c1010f075521a1844d020024411607007a540301d51502c6008640002c0d030 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 33871704 1250 33870454 33870461
    0x70906060c0b0415140a05062d060f0a0e0a090504050d1b0f200301021213020a1205031e0c1b01090317030103050d110706031e021c0b0609130207020409050a0302070602060a 76
    0x40540c60204c9c0d180b104499407012805008001e50800b0051100603202d9848400030002407285844107c0016801030401540c82c460f50081c81440d0b00300002d1000003a0006504420042c2c50b0a0484404440c09507403600302c914a0005071000b01d00764840000c0c02060b04407400c01880381c004407025103c1c120141801c3c0d2103440240d034000c01d5000f00141d1445012028110501c1c0700400c06104c495807019092440c08030b558050b1816000028001c038184200c051030740c41054058400d50074400290042d60f1030f46c01c5070210680e04010301c1c400e030446a1003603d54001443d40300b0a40c11003400d0010480340581c00c06d0104440c0c07403081c022419007d80c0202981c0303040c03090071001824103a08101d4124060b20480c00d01d903000c4c2d50b11441400c00401980040c01011501001007001c02c014110070106541c0c0e56540c1c58010700c4208200c81c2641c4035250015a405906240944d40700c03401d201080c01410282070140c0140202001d0a04065021686c101150303690707403c403159a142c044205084 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 33872954 1250 33871704 33871729
    0x3021212041704050d030201062603090d020f040603050a060506030307051e100c0201150f0503150c040503120c010506011404030f050f0609070503070906060c0b0415140a0506 77
    0x109030541000038001000707945660742c60a9151001414190b80320040740303010340000d2084015035107620301801644400b41c0c103000c1c030704101d54285c071105000003091902d0348525060140520f10020f2004150344a03a80c5843c1805400b0f442008415034900300b054840d6a007140845066080030040350507440c00200759082180c201c00a04410301c0500140104034980100c0da4920b406103112080c2c0c620418031604004079982d4001060300c2407007c80080c1001040d81004003c8000100103001c40c0e100000c120910400d0200750311100e032502400e0001c40e004650105034148a6680914903003900d41c80a04000d080d02c0000f40515110000107440701d103818084400d245d90300f80002c0000c01c01d0340402d01101c4e40118260f5120304004c0d0881c5060803821210741c200c0c0d60180c48108454201045400c00608038900100541410040020941c070b9403001c0191000c1e00f207201203401d0002d181d60700042d081807284100700d840110a007085200c1000c888280b03032246440009040d50801002c2c4121 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 33874204 1250 33872954 33872977
    0x3010b09040c05060a0c0615080f01060602030301060e01051309060e09060403050d090311010501060e0a1406071b1e15050c0a030305070e090103050f06060a15050d0906090f030212 79
    0x3402e0741400d007400125003004e50280104040701c2802000300f00c0f03520407001d600600c4401e00d0300c86414502110720341b032000d956640b510ba240c410100803440e4003000383d9041d500a840d008014120600048845024620384001c0403006a07000151421f03042e0300030401c44503603640710080c3c0e41e00c0580c016140c1000300c0300900407440800c000c5621003215401803e00a10908012506000c08540e081c2121826005100402c3d00c0860b00401e07464005200c4004100d65044103520503d60710100d50f103030080b01801405000e080c0c265000c8285070107055000f904090340c103100c0c0005090340c001d109100c0c0e480740103c0352540d54031011000784144121070002000358001d040c215100e9038110000c00300200b50700c0810944101c445199503a11074914006c5000d10020415800f114600500301400075195030701c00d06420004000885011f0001c401e0b00da91800e011380c4070009808140c02401010900928030351a1100110400056140b0030b490180642d007141c4040c40003100c1c8210030f1050a00f40722 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 33875454 1250 33874204 33874223
    0x5100504030f151107060504020310150b09010525030e01080403050306090a0b040e1b0108010810020703020705220501060504180f0204030b09030304060507020a0201052502060a030b03010b0904 85
    0xc40c04507140300003100d600c1030f40050400d5607074403800819002460106c1e0303d19280e505100039403078100075803202e01c0c2000c842004401000030744107045003150b110b0103a44a802103484140b5a0140d815603100400c00d0200ba00c09000c400300d07021509607084000c8001c2a03159070451899445400d405100b240c1c141c481030f141da2581070411014040c010a040d151548480c01e9655903281c600580f01e1040092004041120341030803401c083c11100020309040216140041011000c0080c0350f60f8002242e8800617540d41140c20200e04158007508550340000b5039440b4212119004030200101c401100e0017001980d0703c920301140d040c855841201048803140c0c031440c855004603880032226450100005181c159203a0303030f900b080310302140c0c0c002d0035801c040f0400003440580d001d0740c3d50045c043e1014001c401140c2d800a0303c0e50213040e003606600e500381d0402000d03602403002343c10050342c2c00038104e9466000115000740031b80b82c1c00c00c0b654000d50802100e0b101a050194a02e0702855000c2440c2 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 33876704 1250 33875454 33875483
    0x90601030b0612010605030304140f0907090e190501032109050a0b0c0c0d0303050103050d09030206030c03090115080f1006050303160302070e01090b0a051008070806030f03030a060510050403 84
    0x4031030003c4000124600c0d5681d50070000d002e0350300b000188010b01720300d0840282505000c0821000741000300540b03009003102d004100400c0d0340280050142d425002c81c1d60030b142c4400140f80090380450b00a404403a00c0c00b0004014000143c203401c20141181d0400d506802d070409045540441c507104182e005044c10a0a1080600060141002c904040704a5824030b0246e40026180049224281d0109079100010b10500105000700700f100342e0a8101000c2d5603145501084840c8002001d0001e10040403000c10f0320003400b90001e402c0c2e03045502917050840e4580324020780f600c54002254030340b032141c0f200c83c80d89040f450107001d0072540010051070810001401034403602003403040440860080d2a008902c0c41e00744d8032002c3c0070380852030001072a2940042131010301d20041d000103110720018000c4c00d072001c0c0d100003000d41c4040075160503d003645aa00200380341001c80301d00b064142c0000300400103881d2050340098201e500444a51301141c8580806903001e10407800003601da0100080e20 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 33877954 1250 33876704 33876709
    0xc110609030717030d02030a0c031503080d0908040b0a031e0c090b07060b06030103030c020109090504020d02130608030d150501090501050406030b0f1c030f05190e0607050102030403080f090601030b06 88
    0x8003c0752031207a40680340b41601074001c1c03d00300e84c42128581540c2d552a0380f02000d007503151050080c40d070382000960802900b1038a0309102d40c060342024204042c1c544006008006c0c2c60419070b0024001d03c074040383c03140f00803180500034084d10b0b003100f100743e204400f0b03c00001c0c1d45030043c451a80f810b83c0300e151085040c101c0c12072096100c0141660960380780c3e4a110215180c00c0021030003103000b60344069208289100040112842d90302486905084c2030a000151b5248200241c51a5044414100c1d01011039144401f800d902d521054490002140c2103240107020741116141486000d0780028950705d42d00159080300355802002e00107602448240400d0703020b07a0111003820b1f40242101840e42c0500300068205c0b251200400e134982c42003840d0010143c01007801443c058040c1080341c2003e003000d00400341c50600700c2c1d488082001d407030110b40c5540c072090708884100d0b80010007075681c0d00d42810b01400b91002076a00322518080000050b4425a0104400f81a240e101070f040a131501c2c1c80b401c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 33879204 1250 33877954 33877979
    0x6050412020f0a0b0307020d0207050a060f0210050c070606150e130b06030420101211040e090c09010b090306063c04060504060f091d0106060c1106090307 68
    0x4080703821800e60068a0203ea44404000c00107024070140e20b0703a40e141c0442c000b81024a28003182041d98004007042c0410b40ea002d102d18280d0300d0b107141c5001d9035110000c04901e800e02c54915064814500f90038003d2888500b4014400980109405d20481d44e65050702c400711489590b8200019104251340c099610b842c0300541c488100c991004105403616500060850340b0541d800c40c0d407d0700622940d5144441e01c040c2c3d0742812421224541c2c0b02e0107411014068031164a4400c51590342c4034401d20611070410305540107054491001116460940c0381582d4820303480081c1031084110b10300008122004070708a4102e9500900541466100e103070600c810080401c02801c0140c4c0101100341c001020368414000020302e400c803220f219903449051004071501500800c0c01a42011418001d002604c1d51200c2201d140243c0094810703003c08609160780030146c11520603500b0b0003800113907183e201c00d004100d0303070090088111103a0380c0004c10240c0e10a80360780681640140c0401c01080d6071140313 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 33880454 1250 33879204 33879239
    0x1060809030c030307020309011214010b0a02070f080703030305011e0509040305070506090604060b031203191d030301050126060906040f020a0c1b0305120c010b0901080604020f040204060504 84
    0x42201c0c18000031a4a4500f160001c449440040c0c0c40820f010140e5a07000b40e4003900075141850401090754984102c0003111814081e6010101e40024603460841c030030030007003004040400846040c2c9884007000c40c0c03243c0340e520054001905013400402c002c460b2455050000901000090200b0314020510004000042003074040c404284500b0001c10000d201d40341c0310342c21150142c6080e00d0706e0b02d012002c407002d600516020768014181e1050780d13030344071049a8211501c0c0b04c48c3c80300d140e00000c88001a00280d0010004009040d4a4155026000000d5070603154240c03200900502c0e9100001c00c450303d10f0280d12021100e11010400c0350400f07240058005101810201790a06840c259109980c410940140010200c60590080c0007000658000060f009502e5a540b01d00d075454042d690451300440b07600364500092034280b031340002d500c01c002070760015201c002150b80d907100d6183ca8a60481d4164003d0580086100c0103203498800c03501591180d40314142410b00300280b100d0300034040d1 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 33881704 1250 33880454 33880471
    0xc0406050d0b0402120c07150209012705030a0c030b072a0c0f1205010501050315070810030b0106030f05090a0b07050d06030f060e1203090c0d021906030204061403040506010608 78
    0x82019118085c0c00518681c825003101c00d040e6942c0c005880c000480e4070140311100707101c82c81072048620503039100d10b644100e0102c00f44114012400c000c1000042c04e6280e1040c0e41c14402c8000c2542000703075498051088a004088160700c0760b41b5504182c6180d4003941188801064003600024403114070503452280c00c0c00b0307030011003039192164100c0426103203030381203d81c52060b075607003140400c1002d009480c050002500034121020001c14010300050003d04036070140301c11440018161712502c0d24100080d0340015141c54996900e010150003019034001e08103201d4200000070352007883c000fa86403a00d6611000800d420745c0d0344201107455410000703802c0d00d00b5032681c20001c0410340e82480324515030b000c0d6800003640c4491134906481d0402e01e40360740210204c14400c0042da00004925800a208103031072104a9060174400110481040780e0042c0789241c1b00720010480c1d9505a02038019a049904c0780440c50840c5580d441680c0803c6034020441d038000c0d001401720350b11a041064020600c0c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 33882954 1250 33881704 33881707
    0x210020f090306010f050423010e07020f0d090501031d060412030603060e0607090e04050a0602030a0f020c010c0e062506020c03030103030507020406050607050d080702030d06030503030f0c0406050d0b0402 90
    0x81e040003a04260080e4451100c5c0d03036000c2004d0145181c02d00c500c0051024203092008011241098202d0340741e41407140440380032001001415440c024050190798854040c107480700c401c1d8008014140240d02d001b02c500091421004056035080c405603009030404c148000c0103d55203568646907098022100c00c4101500d60000200094550090524071102c1c000640303503a1a2074040248110100c0d032109d000d000c405810302020038408107680c504150404005a5a9501c03200441d002d8041102001d0219100254000b100c0c3c0065100c2d04400c0819030352010545d02001c01c000560040c0003481c030400441843c0420340707081c20074400d100e042c81480090b003003101410f2580e041d03801c268803e601003480080c1e401c04600c4c0600ca0003001c1d080456095003068015150399a50b00400101c01043c00311900c01b14061034020819110100d5803402c0c280943e68907494090f03102c3e0003d950244000d0300010210312034403c03404c16141500c14035554a4200041c0d4900b03034024280081426422071707070 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 33884204 1250 33882954 33882967
    0x60c06050421020304030512190c0303020f04080d020606030c060a1b0602040f08010f060303050423031006090506040603020f13020f040905010302031903050f0d0e01020a020a0b090a030210020f 85
    0x7003061610303079040b0454015507155451401e2203070600d9550301001055490800905500b00646a00f202d40301100745810315151203145400d900a1140e000c00040320350000c1400910a00b00049500b42c90b840c03a42500d2064403414240360780d40340c1a645141d84030200f0f00c40301c00e046104e00094031503004c0004040c4015801601e842c2c08a80c0903410030b2450608000003801095800d0080c03280500c3c11203810400f0f80e01e03545008246005070300609440055602c500c800b1142010004802d5a00042c241e96101c0340300d141240090586100b4656442d082c00e00052881c074143c03040b801100d40290070080442000d1003040581d004980010038880c1d030a2040c2c40c01020700d007024102400b100c120005c0e41e541103004140c986034828083c128001c0ca1450303400d00080d403143c252240d8904050b40c05071038a0b5020001c1300900100741107a035146d0f2001c05c440e1895540041c107a500e040c010150720425032503c52500d91214203000001d07000d40e2048043c004002142e6000f0480303103c06048181c00c080 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 33885454 1250 33884204 33884243
    0x130609060e06060111060405070b0a02030912010203011e03080d05251d091b090312070503071b060207060c061407020c0a08011a041a03030d020304061104060c060504 73
    0xd03500c41e41c01200d940140304200403543c203e03030040000c856280040c0003030314103691002e564240c24000c3e03060396100400c503201c00b54020001e8588200d80204504404900b05005074000c2d0024841d801c003510400c0380540e0424560780d070000c242c4c0c0d0070040b01440c12840c011010003805000d0003617243e403042c00c2440c1518404c02d4220442000359656a080d4051108415243c202641c0d032074903100b0700154060001d0b12202c060390424488418807401d407101100e000082c05c007002d407954001a5080041c045080200100c010000b143c81000c106012903890200c00f01002c1a502804c400b42c1c1c0144d8040c0302041c090065903000e50311030b25010a50301201c0d042101c54003400e407613040c050390050004e9022480c0c410800000381c119a0001c20192003280782401c2c1001b90042241e00850317941118540180031405c9440c58100043e0849a803040804001c100950003100c1c182e80080c46d203815210040815001c803070071214181c1e43c07202000c0351034642000410016104442c2c11804000840c15813 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 33886704 1250 33885454 33885461
    0xb0903120c06010f090b030318010210060b0408100c050708070f020406030506090d0e010905011809020f03090c03030403020108010918150c090906050114071502071101030c140313060906 82
    0x3601c1e010181c1125490240c4d98680180316800010703140b420b10500c51500d440000075a807510010075501c10209005d080145d00300b03640c180540390410f007442000300b00920140000c000b12003604044841c1c603c0e02400b450206c501000c01100000d00400038080420702c0c090241c06854043c8520300d9a5424030f41c00501210502ea00071180c940103442000700d41202401941800c200e1814281890b8010b580000c100c140703140035160600841190000901141c0c2c8094805010b40341e40440d80d8408012002c1e260fa04201c0781c9400324460407040716042e003008420342d8112981a1140c1030365034204500c1d80b001e00301c400340380280210102d0b803060210b00d0b04040350107064800d039000100640525002010100d00c0e4100075419030804e441000706e2f07688143c60301481c4074072000068840b0b1461400814440e00d0861150003140041800700903c064000781c0b400304602601c04121240349140300b6a2201080c0314280b412060510004416000542081000c0c1c0e2003114000780300d2030f4543c0c441048 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 33887954 1250 33886704 33886717
    0x8150a060305090606010305060609130209061809070f090612020c010906050613020708040b0307020708070312030c030c0c0201030b0123030108010c0908120d09020607030c050d03020a05040b090312 87
    0x340c0742d0b0103000d0aaa0288000754010b002880c050010f0324007040030445070b1040083c2d650045c040c1085050b0052020350541e910361100401c0503a0364001101c41c0c40c102c04030004550b12640b155070101d02d01c0c030b01510090518907102d480710300c0d00c6890040e086c1c99800250700c040f80b00035000c010800140100380314940220784591000609801c1c1201803201c9184c060b01d080c0700080c41008174801282a08043e2021a248512816526034070000700f2410240d81e6407040d41e071480b802001004000d150584e101003000640d8041249503c4044214255140d42c1120000704494403540009548a07412491705840103040c1140d508091500141c2002e92810a2001c440d00100c0103100001c0b0a0041d001d445400e4501a01d4840c180b003aa95200c03140b400046007480b00002d400c180600403900302054543d001801c0b5a142c03d041c0c10098883e070b54450b806c80d400d00808410000e11800391082e101840d100d659003500301414084441c6a0754031020b041e50b03040c8125282600d945035200000e000 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 33889204 1250 33887954 33887957
    0xc100c02180f06010e13090c080703081206060304030f1101021e0c12031012020a030f050102070b010509090a0201030e0111030106020d030f0c082a0a02010b0a080c06040608150a06 79
    0x40702d1400d4022070000c00740142c01d071810800c00011400490380c42404001c2a0105940001451030451900300d440380c40e950711801070390081c00c400000348401c20000c1c04294000d450314401d15a5440c00b0041244001c9a00901041e0001902c00013244907500c6a03105080450005203044100f403003c4480034282810700c0780b000300005d8680d841c06c00a002101031030340054206410341c10400707a007503118501400303112464a502070102c2e0655803000b107000b00568028410380310390415130800a007c0c4d4481201a10070040071000011039003045461940714405c8100900642c0c14031350700440107000a01a030b15101d6480d0120301151001c80390046009001940007086200040711014050b600410304088815103081821000f054221445641c0620301c4800b86c03c1001c142d92a1600d5403010561001d4111000f143d54007146405500ca2440e03544125140c0c4105503480d201e0950751030007180942c1d0401d40c140410007070b0340d0040c041560031158400105691042c08030225400c02541e521920 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 33890454 1250 33889204 33889249
    0x9130b130c1214010e1c1202040b0307110601050307060507032a02090a0b01140901120501030c170f031801021504080d0501050102030309071e030209040c030c0608090c100c02 77
    0xb0800c0f800c800105034040501000340301081080c42c18a0311500d0030070070f0390949440d081e0150b120500c10b584000b04070100b042c08545451700ca00952540e50000c840c1e901c045080e40166018043e00000e589040f130f03800600420342d140c14400100c4a680105070b01f207050022820500d0918030700d1920307940140141c251002200764403801000a608130151180c810f0034544980041966400b1010750140301207512196642c04041004a41c0160504c12800c0710700c1c0380100220130040c1c501c0b410811141016000d0720f40313082c491a45d64650701150303880d0314139510801c40c1c1400b0850340b0004001540050040d6489609500c0d040135040300b084a00701c80101002690344101c000d24410740340541000e01c0110700f103180140c2c001e540c40e60140900f50614100301d5030010707103419812140c005140d01810450840c2040e00d000c84261040740812280c41586c10808510203128141c46441031000303900502081555000340a941d1a58055050030041445461310144c2c95248405130403000c0e04050380c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 33891704 1250 33890454 33890489
    0xd0311091309020f120604031b120305060f0616021215011205060f04020d060e0c060c0307060501050607170306030102210702010e030408070303051309090c1409130b130c 75
    0x42a44614074070441e00c502001d81445d0404900003642c640e010340d141c1810024a514a40304110241c945c580c0240468402d001e0380d100c141d8036403c200e0080f00d09554039036040700c000081042c0c1e40191a121100210042849d00c05854174203042d14540e03201c0015621a00d18524005d40d91100c04d8002d6140d1460444485003082020071907140d210041184030042820716900042c461520761001070841c1d81ca03895a00c115003402e1005204501c40240038a03950350043d40c4050322504407480c2510164580000081c543c00c1036403c07102441d034000d480030700d072032440e003000000c941014000c590150350078484001d0700d80d80403051111841011418401c940b07000c1400a00f52681449084040e03001400100440e0000043d90f000f940c1d03050510949074401500349501080c1568400035100d82007111010030b10003560603140036a48400e1350140d01d54600350501817105020b40f406007407184403900c1e4a02140054211640068a005843e00140c0031501c80230b14200325a00095408001010700f0f = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 33892954 1250 33891704 33891709
    0x60c020604110301020403120804050f071d01080303010501020606150f13090b040c050a110c0a0f06080703050403020d030906140405030405040b03060c03010311120303090c011d030d031109130902 86
    0x10b0b5800481103000f0340c034181c00c540d520b003d0300f5100c4480b0030a00c01d090000c241008010300101b505407403241e08513a40c2c2591500d1019903a46503042708080300c944000041090b02000c401c60b416217106030010b240a44030102444001070b00c030805a050f200041c800c0a0250b01003400804843c100110003203412401e1401d01c00484500005c07042c45185015032000c14290001c0a561182c02c1c0c5083c51640e0745040c049160410b80038454041e80940000ba01143c81602c0610000544204d42c0e640041682c4483c0190100c48043c0c2c0c015000d039110001c102207151190300042141d9100c0c080108801000d81e242410b4602c064138221955000802d05200314100740c4036480040c101200101058241514aa401d42c801808094049481e106c44070b809515040d140c001c14841007012640d6070f02e00800d500c0c1c0c0301c0e590056000c3c0065410306032220461417100d070040c8600d030010b01820201a005406a004107510342c4509003080c800d01400038540c2c3c40150b03138851041442d10211f5100f40b030f40304 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 33894204 1250 33892954 33892973
    0x7060f0209010e011805091005040609020a020f2407110109110102060901090206090402070201050f0f120105010c0305030703200706060e1012030503040312020d0c0e10170a0603060c020604 83
    0x409410400e2003003d1708401c130745441c000e108592080d80c00070556241e641e030b440d0076460f0f250021500300b401c054001841102aa0003082a0105c44d401c0c0e510092000740c203951a0b201e010381004d1920445406002440c24003ca403a0704800c0da23050945002c8c4a0b002c00901b07450755510241e03541c600d90300a00080d0b50b014004503521000c1003000300035202d6103900040d0031b409048145402180e0200700c103800c40e4090000c50704290800410306403150203000ca43c800c254004110380c503078200f0080001030194000c0c0c5401904035810303114981565a110300c00c42c0144049040c0200740054990f0041c003d8074040c004000240c05503c01280c42030601c181000c1c1d800001d41015542c03c203d80081010b1030703c58000f004c10b10b51610380180e4988403810100e5034080c038910030b940e00c1e61000079843c02080321a4400000700229445001e224043c0f50300308501c0742c010703070034803030100e03960050100303801c0c03071000c28583d00100b081400600a602c0b6251102183d0708485600e015a00130414071050000081c0d = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 33895454 1250 33894204 33894227
    0x30216090209060409020c03160f120503070e040e0c0a06030606090e04030207031203020409060b0403031d010806010e1c12090902070309050f01122903060f04080f07060f020901 78
    0x900c01d40c504600540495203d100c0c81c0f00c0c07201400e902141c1101840382c14000c07202c00a0b02e21902c1c00d80742c0c06c0c0781402603100c0a20b200480d089089481c0c040c80c0c0324060320a0303a100d02520b40b41d95414031040003d200241c4842441001a0301980804180e0b03a5510030220020301a03c0c0d034006210740c10034802800c031344010340120800b1074100b0108000254006900c0d002d0360382c8000508001c02460f0f030141c000e03000780d03009402850306210020a401001c1c0c806007080b43d006e40d41d054802c0d01c10400b1004d12420440495000411903400141c107940102e60200302c210001c0c00d000380d80401c026460700c1401071203070121000034550180c0d960543d4000c141d0000303441841d800314509001c41d9006421040d061083c01d000b5159190018131980c0928440d5008240090050202c1c2209220107038503c02000d000108903129900300c4902810300103142441107460068401c0d0544481d00e56000c1504a1018803000403c01c01440000554034020500c101074123220168543d41c0c2a07001500c0042043d = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 33896704 1250 33895454 33895469
    0x9060c081512100207080c030a030207030306140906040507050c030708070b0f190c260703050703020405060d09020f10020d0806010c031e021c0206060411030115080a0f09030216 78
    0xa080b0780035255400b2400c1c900480c2801c2c0010307592170482c03914108038019000c449415010208680c070200d50907400402c0202e220341e070104041e540710f2410303004141804d28100d1700544100c0005001c1d042a0344119040251410441d00748007442c1c42c85440d50b4000715046583c44408203440c1d007007246900c400b0f1f800c040211006841c5260080d40b032120070051300044404192036049000700c180c09004070b9072000c500c00000180d0403180c1c81d1801e1410b8019928100021b140000050342c00340321f4801d0f1011b42d00700801240c0b8001031001034901800b8205070603030b400340c5400c000c0740f610b5440808240c0c29483c1c40c0c000d002420211035015002c03084c0209034505008606a45c00f00083d48003034941800702c04e1350307411043c6543c81401240791030325a000c4210f5119401c00b041c046030ba000920180704201c220743c10310244040c00d078800274030b000c03c0c800c804a940181321502da07080e004414150384001c4207200000d500040004500c1661440030040c5c000d0780001c041c1b044104541c08506000d040c41 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 33897954 1250 33896704 33896719
    0x11220501050c03030c03130b04062003010501050d0b040f020408150603010207030903240507052706030c030a02070f0804091803020c01051612110f0a030801061209060c0815 76
    0x200010b40d900c0b8403004111040c1c800002002807940302e884251045526004003440c161490300c0c0c608100288003042e401544c00854100d08400720700c03070800b00e074140c031010394400b1700303000384150110701030001d5815040d4031035120710344003c01584900c0a007005000880003800340c440c6098540c000041c0c0a030042e4041e0b40100000004a6001480340c3c040701d44c440b40703901120041000c1c800c25590711401901c0e003541800207100c01c069001d00540440c2c070b50034144485494403041c04074078006110034010b070003020600c0002ca28106020140d54009110340c030140c5040080e0380c407604050309040044549020200c0d05014450042c890421002d510940d100105d0305540c070040d50340e1519802240c10003c0005e2201d80481c6800c2c802f418540d4000e00486080c500d6100c054501d000f801590580c6c2e1141e20b80d6241c8440000410b02c0c0041d070940c4a40c2c07002d9003081d800320b80016680007440344003500c401e00e0000003000c40c810700004180b16034402e10103043c100310860104e1855080d0520075400c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 33899204 1250 33897954 33897967
    0x31e05040b03040b061210021b030412060513120206070f03020903070905060102010b040f06060f18180221010e0603070303020c0f0118061205010e070c060b03011122050105 76
    0x1e905084940054100683c10580d9a0710303000154080c00300d10b590440382c01100c18101d04099244c0281a5100b040ea007042a0580501d0401e40e490055205442c4440040031204010850607030246802c1a4207000415035000240c65901c4103140c6d075401c0b44010b034007150422a8070f9034050024004900700c0d00e015481c0944c4c00d00041d41d0b944050040030b0714190f4400c003140725a8000d61040c400540090400e00c00914000002d0004084900c44d81021400c07480d07240d440540300c2e80340014044410815400080d040140411401c42d01046000b105076080000e40d540107202071500d40d1600d1444072001d0303158102903002e07560743c4001e000a80aa07210580500011790080b41090598900360740f51813410802c0300c012500c1441c0c0c7c4c650000034480c03540340032628640c070807040900d0005e83c0c801403001f1390784c90a02039401441140c003080001ea03040d148a0014100f60490030b01d10900400204151600703000942c4d55038058865088199040d8510200990508640e40024042402c0540c01c040 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 33900454 1250 33899204 33899219
    0xa05120d03050c0a0e0f0f040f0b0f030102091f0c020a0b0a090602120f07080403060203190e0a02090c0901230703030e0601060203160609060f0504050c090108100c0e03010207031e0504 81
    0x51451407102e100d072215885010b1b00351140400a858603134001c2041c04010b6014005400501060014601400024003090580c0c201402268031080010f006403060400d40c002d4940f40c403064000308030411008a240102503a180c0c102800036108070307140c031a1b403640810b00c007411300907682c0c0c014030035900b10f43d81da4076840140030144c0b03e8540d1003110782c80e5201840e1400a10f188241c0c0c0008051a10200c1845690080303210442d040e107807000c008109001c2140c50285d50780c20030100095001560304001605201140041d120503003060505d00314140841205680f011031001c0401904403000c40c08400381941401001c8185442e10301401d4654100000251603200d50410070081c03514004407102040b40f203521149030706402940c1044000424024100901000da5040d01c0901c25448450000c0c5070144802c1c2c104c4460700002c00c4d80309441a40c0d030002d002100108410700420607107003440750300c00313000800845101c0c0c1d481280c2c1100380c165003410701d00034818950404c2024002800401c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 33901704 1250 33900454 33900467
    0x2e050f0c0d020903010605030312060310021306050a17090606010f0c05030a0e0612040501060e090102090916030207050109080c2107030e060702030d090f0b090303030408090a05120d03050c0a 84
    0x1c0c5108080943e6031195000031074050002c50340b100750103100001c2c103200c1031b110814016015a40880941362440c01083c1488183d001e0fa884031083c0640d188000c1148c0b502507401003004c2020360034401030075814088e040180c400304481c820190f80003001003100540c4d10981d0810120158140400d10f2180341c0c036216664014180c4503014000c41041000c0580c0d251820f81d000f03105808001d4809180c20324089029062034030406140c05401c5000c2080d007641802a5602503e020b0240342c0c160780c030141c12910790415100000141a402c104c01001b046c1d080c007407030105e68001c03015241e9888992140a2600c0d2402c1d8422100880e1454030f200800d0000e003c4845280d050b203000e080d10f030b422500084182c41070322002036051048010f80020320340c0015240c0116650031440401c0d6958a00183e003103071080141651341a0802c00000b000108807101400003000302410390444192254041140ca1406a00c3d51480364040143c0c2107900c1c0d8140540340d031000810858908007008900c000d41038 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 33902954 1250 33901704 33901717
    0xa09110114041a0405030a080d0c110c090402010e030d0c0b0a05011211010302040e18010608030c0a0f0507090908031807120f0510021305180601090b0307022e050f0c 73
    0x12004400a840b41c43c003100c090781c1c007405009040d11a5400c840c500380c0481d13031109131080300700ca08050841e0034942c020481007504550303003030142c80325840c01c0042001c080e40080040707062180b0303484c920100d82c03410089410250f403da260340000c000b20381403040c1c3ca00700c01023034160518107040040c070103500314001c103140b0280c2c0001c102c020403181c140140c01900940e0055000c1040f02010013042c0322b43d01c19100c130030504913402080065100d1070556101d2150641176242c0b9409200c0d080002203c81012200c0035000c0c0051700d0320b80d510f9611031020b131940c0c3c04050300d110002009102281d04018000d00d11a084078004005051420032200146040c01c400030703060413100d180e0300040c840244400d100300410441300715910103032400c05010703c0c0040e000300c5019003210011241035100c0c1442c8580140e030140c6680d8003161424040307403020392000b0b00c8101103014030a00800031121440c9002c41e00c03403441034241080b80400d54a4400c403580203140307070b1580c03040c1018040f07808640b0007101c81 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 33904204 1250 33902954 33902969
    0x30406050a02030f03250c080910020106050907030b0112050f060409020d0f0507080708010203101215060e040b060603150405150901030515090703030e0103090f08030a0911011404 79
    0x1151001d41c803050b825401054a1900303000c5000081003048000715021030f40e0521584222011502c40b448112503114242400a04000007000801890700e82030f01621041101840081036841e15030000c103010003420303965840070035100c901103802980c0158600c090002490001c005c00e142900c0e940c10003c0006d0318260217542d45440301000d40d2180c00c0c25218203600040450f0301d0356010310340195036040343d2050701d10300e000310680800d142e2418001c4074011020208038541050826100d0b0080300c5042204455503d2500c0d9400c0c4003ca43c3d0207014010850390b002c00045180a051108001310001c007003500c10300c400c104000c07182408440e20380f001803060b1000152a0f030703040c2c040d0510b110765888841e808400380b000041080000214070f4003012038060080c006403a40011b15641d03180900005021030745042d0502450f500c03a40c04005080d008510351501c00023140c9824400b0340c029221400c40e1034840f5000e60a11000144046445800b0310309060303034000d03500c010351003030180d400341c0030 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 33905454 1250 33904204 33904207
    0x30a0b060c0c0d020f060c0c19030b011e1d01030c0504091e0804170a140109020607030c0602190c030206060319110d050d0f0206160c030807140a0315090e03040605 72
    0x1403e5444403043c0e81c00005025102e00e41e5054a40003842d03440c02c841142510549c52031420313502641f0340701c0d442c03400c036680406144820303402e0804d071070450f007464002c0c21100c040d138240000d81d100e5541c100421070409010741810950560410743c1034054150003140c090b60410b8084000202454403201b005240c00190514030416441c140310300b40300d507a00821402e54608071510700c2d007001150307803e8480e21440e0a03081c600101200d403800d8880614000c1d60110082c880c82012a005100d4450901e103d42d07001458458056070b61001401d250441000040c4071100c100201a010024143c110100314020102241c481080d035541c4070080d07100401c290444603140c20b09484044e0401c8000c1e50180c143c5204048101c0000c02113240c90300030074014841e05022a400e126100807207038404003140e407404200c29090300d007500e03180300180645041021170a01400c1750030251002d0510103800b9940403c004440caa01e0f048034651540080c64402c0c64034011246000001003250304444c01420681d = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 33906704 1250 33905454 33905479
    0x2070e0a0e012409050f01060f0c06020d0c080f0a050f0112030207050a060e03060f0106120914060a0c0f030e0307110310020f040302010305010b031302190909050102030a0b060c0c 79
    0x354050102c01c3c42143d0740100d460100144107544048800503502150805c000a980341c41c4415000031082c0301e41d07804540100248082248264407031030041d0f010b40c2c030140ca403d251626000072561030001c4c184c00211880c00703004200109480c40c3d80c11540c0988140001c0c100407481820008040c4280c0b083c00d0581c1c0c9041742058000d1204a000b0200240b0300c1c0716481da51040074003450601404603102c0d00611001460955948441a0603144666a60b0783d01003113520900c402001c00744401d980e00c00045031500f00e520010400c00c0c0c0306019619010880501d080000350041c441c180302c9a00341414140c0395042070768004141e445050700b14019030f1001d21050042810079090140c10b03450f942c00022994180c00910004100f00c1e4401ea0302040760341c3c0d075958444154001078a60281c0c20301041700b04009450700d07800b01900540c02c28101422950f03074017500300403903607400c104490301d9402000300880350707841d403145e80c028070341c03c0d142c0700d00d4010345892641e191104004031070320542424490 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 33907954 1250 33906704 33906731
    0x80417030a110c0102040302040b0d03020c06030408040902031603060909170703090b040314060a09080d0f0f090b1807030302061605071a0f010501051804091425050102070e0a 77
    0x400b04080740b814003d40d210480c1e807200f07010b0b50040c001a801541848080030301c9003040032101e0040d68065000d488110354a404202440d4400b0700152149e030070a00010865a6a80c80194000e5140d90440101684070301e4020f01501c445a01801055140040b80b401194144d81c0580191410401d800d40c1c50b032442c0340580c2c0d5405103402c40b03008094040380220400c420f80405a90035003020007140c240303a64030400e100695800100042181c0e60030b00804550035026040922040c2c08118081095075840b01a03600702c80910b42c05540c020030120078040700e6441c0c119541c05038a0204041d1424509581380a0b5603220041c0c8442e940304c0480700208001031151058440301c1e64411003a212006c100c0000d0103501c902a035072018004465000040c581d8062805c590044045030b48040e03110b00c1c10000c001c02072901c45410750721032501a0400491220520100d0407107003005520413042216540000b10381c0210750040390655010b24000c0c05003140e4441c01c9070b40414064404a220400040f4 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 33909204 1250 33907954 33907961
    0xa050d06060806010e040b1f09091109190f020901050304020904030c02030a03091707081e100905010e0d030b030304090e15010f1502011104031e0c0602060105010e01080417030a 78
    0x100c002c0d00d0003044000b00762000302c014401d0065001d00b0300d4412039160b5404030803a019072903c403020f4180c2904003c000d00e5403990040121a07000b43c419924030300184010498004040f80e41c04290740ba12001d00ca46102540f00d000800101c6c5481182401c915400180c0a40300243c0040c0c41003c440002604040c4a0ba200052190740038058032001d25180c5070103050012240140d4480c000702c0c0e0040300380c0050011b40301e803c4a14450081a4800300da1000c001d0600328941281c1650160614010b0404154082e18000c0c81c0305600006051070102181c0d82003403244010300080500b85000200640e07000401c0e2019a10301140c000f42140014ac0070515008010004405c642100c400015400c0302003820542100c0062919092011250300c00328201c600c01110307030f90301c208144014030100c0c00d00c1c0684040d4601d60b8004448105298442180b2000c141c1c4c06038006038411001030206580c01509e5410722002800e10b40b900c0d050076960004010b44107007612015210120004000311602d42 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 33910454 1250 33909204 33909209
    0xa030c0c12180f08030306040b0f0109150908070b04081203010e010e07031803081b070506180a05030c070303030b0402030c16030219030c050706020609070e0a0b06030106080a06090b0a050d0606 85
    0x100e00c0300c43e9503030710130780c40351039800c11220710b40700d9841d001c7c1c0e450041c10051810140c450341691031503482d904002c0c0b0441c4c09031011905c981006264100070816200400126019001300800309450b00e281040203803402254090340a0103513000c0c00104540ca241584050560703884010002c0b882c1d0b00d00c00e0480060004400003c9810702c0004400c050642155641d40907400e814a0420604040c19080b81c040c0303d1890010500ea000c2c60000388001d02e21401035191182c20810f461085a2646039a071464011502c0b0340b5081e008010208201609445071461030716054605500b5071600e04587ea01c0c80c091849048840e0325400b1120040610030300400e488607803003284034281145c0c2401c0c020640c0020180444041c07003246030206a482c000608184070f0b2603e02d0082041c1030030500c01040c0d4080c050b001e074020700c0d100c4070056815030750b00740130394081c3c411541c401d1044d10b01a1015000d0310705035800101c00718588486403440d91191560503050302c4c003d841c0b410842500e4a4614020070b100d5 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 33911704 1250 33910454 33910469
    0x120209031006090203090606090106020309060702030111130801050609010506070b0702070f0f0e0c030f0403110a0203010203010914070e09061e030105010602010b1002070806010e1312050a030c0c1218 88
    0x2c0e4001c100002c2a6018500035245d0381e0480302140e558106001c05190b082c0103000150744140595801464010000d01ea0f0700e2001d1300114034846030065803400c90f005000401c4003c1c0c20f2000c1801b003076100344541c6a0015003250b040070b00d5458140441e10b90320a10101508840d1410700040c0c11500801060307008222641e041c851807651040da541006009000d040300c0c030004040403610341482c150030303280075100d220701442c46525070307540c10f8600e035608444690190150300c0322400966000c0c8055802020460008210104126a40d55002e08014420f00c10700010072004140394031000d07543c075800042581c01c1d101b00c13020040c00a0345204c122055a900d5800c0c0b10020030b1455064018030043c40c01510142500328401000b603858120324000c50000c3d0384484010401382d24808031050b0006200c00c10110064000d440c0c52600f1000b0b80340f480f012600006072092140c0e0b0620a402c80301c015441e080301c00e83c07801d50754185050740030304107801001130403038603070081c003d04503103030700c001c00c4034 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 33912954 1250 33911704 33911711
    0x3030219180902090f04020310090e01020406080106020f15060607020d0f02010201060506210402010507020d0c06080123040c02070806100306050f0903030615090a0e040b15011202090310 82
    0x1180c2004015805030700e034054a08211800c00900d08056000781d0780c40a0000b070180d000c180317040041c0002500b00800700040700100350400a0705003820b01c1200d0a2400c0300e4005640e985c28074034040c0008406038000ca003150311281c2131107042c11303001c81e402100c1d884500c0c2c50b8a01d5203c400006038a406040d501a42c4000245d210100304001c114084900c240b00b078000b80500340d511000c002c244d0041c140c07101d581c040021070034070418000d070700c015a0161050501c681866459000709826803180394017110702c2d0f10f0400003800078175040840300d401070000070810350010000d031000c1e05004458040075806243c550412802182c000d0000750041c0c0300100c2101c0440c60300d5220284516a40c1c44142e610350326150200b01c2c082c4e10011010322401c0c411000711b00d551515000c1c4100714030301301e112460300e0f00c0034442851960307548900d04000b88400d4220f403003a030400d0301742004101009003a45640c00c191100c1d4a455980280c21141d264402c0a030041e1246c550001003801d181000c00c580d0a081d15 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 33914204 1250 33912954 33912997
    0x7051005040c0f0f0807050a18020c03160605040605010e1012140102030f0a2313020406080d05070201080a09020307050d06020c0712030f0201141308131410030b01080106030504030302 81
    0x105804d8502164a4001140c50003a520014084403041d640101807007a030300003c4c4801810344d190012b245221011007103c1c80c04a6100c8840403201c0c2e008021911a9141d00510003801058065140034101426a1110b18100400302000250b41c510035a4005100740d00d5103801c0c00b2080e1001560503510000940d541c0c0382c400d03024000b030324080b0b42500446140105007900c0007620350855101e00c4103402c074400c16817142102c004d94442d04c5003040364055125080803d07400c0c020301400a02c0106034844503120b00880c4005000040d0040c454100b5925084401d00560360004400e030480324107650312520130b000c908000000c2e1207400b8640049104100d0005144951a80a901c545003e40c0c0e034080c00c0503403188100e090701e22900408401d15451400305a00d030560204040d00310f44a0b20060303140101e004d111804003105036110790032034103090207500003a0a0404010706d44c00f041e8502009501860380010305075600600031441050b5555000408141c00b03070341100c40f5a4620380200c410003c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 33915454 1250 33914204 33914219
    0x302012c12010b040e01090c06050c0304030b0c070c03030e01120b030c010302030402010203070b071701060f09170f070f0501140f070b04140a050604020a06030c0815010c1709031207051005040c0f 86
    0x1c04442c2108c086130307401d000041440c0300c0d01c01d45003104039103806035113803901d5600d403c500c017800541980200341007000040300050780a2000317001540309485150034121041c001400450307050306803031076040c00c0c0b1101800d140d402186000000009007070058407a150360004070305c0c4d8000c2c0080100062072510030b0002842e0061301000391510441181c22280e80c03120700c03c4444410b0404904080307035040c42c6c2402100200382783d0035040c00340270044840f4000101d00061400e409030f4404c54464800b00744c02e222035603100f800c881080180c2d01440d4540810403890914074400c1c0744001d00484d0b0400007003030070000040b000200c40d0403c034040390110061401c120351a0182038a0892103080801c00010f0381c20701a0140402c5114162100038461740e500f488003c0e4481215090344c10041074800590014280e04451440c014555105544800303407241814178018a00212680c024402e03c18100010000546241c920500103004101a140c1d441c0102c80000c05c2c0e003120543c543c0b45640800c18a = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 33916704 1250 33915454 33915461
    0xa180e0304120f020f0f0d0303050417040f140301021306030f0b0d05010506010e0109080703080c0f031306020714060703030f09050f010b09010f081510090f060302012c12010b040e01 80
    0x1240201c0342440103444150800c280b810706084011703041f100700050200402d0080e488241d00502481c00d181c650080842c0003141c56000782c11034054000001c00c184600fa43c1c01c1c0b510218038105034000c61a1040707000b007010950905208030002c0586410040883c01025007103801c4500014060a407068910301c0c0041c007030002103420302c0c005034101101c008035600c942d03009400c40c1d809130064000c0c07604584a200c400d51088035a84207502c40e022040c86082e90401c000c00c100c4900a103000c0c085802c04100a0405401d5481082d42d4080c031814503216641c0e000489440395414100050f0285080a04070090182138902030442d0159580308401d2038019017060420f104e0803942c0d08900e81c7c807040107511888480c0140c0103503a00c07901c2c13029402c0c00304074603c54000302605440d51702240d4078036640302620700d82c482c084038003612680d0030421942c0005840c8400180380101480c13000010480014094120440501c545010500808806400c1d8081728003494041d0050044060105055018 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 33917954 1250 33916704 33916733
    0x30b060a030f14061f110d0c02010801080102122706040503040504060e0408070f08040801050702031e19120603050610050907021c03020a0e10020d0207050a180e030412 74
    0x1e650a1110940343c00c000e141a00d4071413003000b06000300300c40d400b5043c0c03418012500e42280030300100024004004000304850f035001041c55891081c03050440c4001810010306a000980c0744c0e00510811303158215400b082940710055141c591521a861601104400900d060f210003038001c080074001406030200091003995020f90f82800941d070703036015000408404440c00b47c01640188030705000a0102c845074520306004c2c1d159241419100d400660031104103541520140e03000040c0e405120b04409000039400000c20b030400d0405451400300102d4606034001c0300100300810820460b00c007920f0b8000700107550030104942c02483c16403e00403492025014903071049500c0303000600b48501c0040c00f600104400c0044c0e500100c00a04250042d4222003c2201403100c010f00705992611007004954820482d9402400c01c44241d0740080d003008110380000303001f2000c0100600000c50a0350701c1100814030580005488000c42e40740d40d085000da5000040f0700e011180c800001c0c020040d1501c0300c0b = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 33919204 1250 33917954 33917981
    0x4050f010c090602030301181401060504090c30020c010608010501031103010b01051b0a021203091305010b0724020309160803030105010e06090a05041112010e07020616030b060a03 79
    0x820106102650302144900c00d800059100300014030140f1070303001c50b4035803a9020700303030110307427545c00304280b000c804026044000083c41c00700301040041100e00a40c1c82020703450615400ca110b1079400c24220302141c81e911010085418800540c42c00369504071071001400750020040e8584900819010300340c00c2c0b009640c90440030b2100440c510301842001d2101105848062400c001e0180d22120b05000940c03480840c0285c2c003840015899540c1d080b60640d5021010710345c0da9584100700042900f0307010505070b01c0d41c40e08006011458502040b100041d41142690303a20114242c5141091041c80b08a140114008424030250100004030605015049540800f60756111102c803652804244203090004003004103030011803e00302c0042c9550724010381001491625400401e05448080c03403003498244001800c0580040c4aa605da03014100c2404145643d0603c481c00030340d2460301900300c0420141c41d5281b010280e0080c1d00402d0480c5015003d147c07030b501041c03005402002500f00c8200b = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 33920454 1250 33919204 33919211
    0x501080a0b060303030121081210030b16050d09060b031501050109091a120c0405070e100804050d08090a0b010602010606090816060f0309020d060603020a05030d090501030b0609040504050f01 84
    0x2c0071464040b080d00d0503070324855002a0b520031030f141194000300308884199980380d0b04100c080c09841011410b944120006030761000710918628111001c058000d00884228890004503000c80350f021040b28901019850042084061400c02e400105182c010840c1d16102d090a841c921400d100c0c9081d0480e85c0c242ca074040941d60344c68a5006842282c1880310850101e0345221001d4604145955040882030041320800d2107880041021104155070110106203500181d00341c3d0b01e403080d5002c203075032642d01d001141802d0a58411b5910803610b040002481000000140e0881c2c04008280800780c000801c4015560740f50b001134000d0041d400f9403400103040c848003040d09540007506810b50603201101c0e40f10b8624240307045078000740f02105581059110307520390300543d640d9402003090a00905c030000c0c240d4694410404c10032441d901150280c2c1214441c074035026000039400084800030308000c11000354020002d0194404c0b0551030364014a44014002030150014220703001902c0b400003003 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 33921704 1250 33920454 33920461
    0x90b0609040b061005390c0102070506070f051507030510051c03090803040816080a021e010507021003050a0506010516061104090c0215010603050c030a09050f010501080a0b 76
    0x4044490115805001c00072000003060080c2055010110324241c2c07803508900b4100d00314085d60f45001030010301d40721030141b034084c001c15021000f103003002c4c05000b000130b000c81500c000010f510f6080c02d01c00d440c4205008120082840314060390300b44108d034800161640c400245003040a00102951800d0010b032920000604080c84141d4510079114000c00300502c003002184458001c0b00c680200300c041042ca10030016440e070041018002038903001024042c1d10741443c1c101c031408000755102c08456404500c2a41c05a11281080d400c15070100a401100d44014030040c1c0d00d41c852444020740140303808070001144c55140d0300850080e56108030601ca00c0d16404011138003400b6007030034003200d204008240800a0030940c00040242c01c2c190030301e07050035629a03108044990319034813403000d60000180300d4101c40411503010b0260a450600300304d68249141c11007601c1c00020180c1c12860355a1540d0818000304110304000484414000d100707560f12624030a0720b17a028850111410390600010 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 33922954 1250 33921704 33921709
    0x30406030e0613020904020307050415030201030e0c0109210218041e05060a1d0601030302030415080709090207030c020d0c0f0902090f15040b0403060b01080901020a08010b090f13090b06 82
    0x12280188100c00d5140c3e10794900c0e80811448802c0070f44100da141c0f0031400005510b8445000310340480c00f001c81034011052031800054140c0e20825112078564000c811800c003d44e8000c2152010359084001240c808030000051441d40d1003c094065841608004840b00c420710341803445d8842c5101d0b010503004103001581e1091030b586d074408018016004900062051440ea80c800f0450801294140d000803801c0400715003440001e81081e40140c100103000e000300f0841c00010000e8281510340b0262a250a0320020401c01140c052102203d400240e03840c149031144855408054000f04881e60002c030b01d10b420780c4500002e2240c6030002112250001d01a00715200340c402101000c5e2480360b01807101020005904140704c50346000e41010b10002c98010801c0740030300007a501c1140c00046012a200000d05240c0c0c00a1220102e40e00401c1035144007644400784904551407032443e10f886561000015601201e00041c858000c00e404901003680030684d044041c0b018091030054100e500c1d504103 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 33924204 1250 33922954 33922963
    0x30c08060405060403030218090903070b060a0f18020c0d0e011e0509040213030b040606030606050d081c06080102070302030904060b030112141005010e2e050409060b0d05030406030e 80
    0xa0180043e0440000540401c0c0030390010300d0001034540d00310000c040030340e000414101c0140e0702c4151552000c6001410000a01502d54101900715028443d0929000000442081d04d0240c20104a44d54011210410307003501a121148000e0044e110421440e800c000e000410202d0082e0015062405003101d00c62142d10351003402d440396654900d003403003803800c1c840a58030602e100c0075110742114000010801c00385080340558420031010810901c0c6040c280e06039079103600220311880160000e0310005a42d04111000c015500400c0c0350001d031507074900c00c001d081c02c0e1710500749540001103071001c165020000302807101c821101049016201c0303d071101940400d0040f10002c030000d88180001c070b5a064503001107000c22400702ea000c0c1010301e5118040c0e0344280d0056440350441800d00000c210080b00145a018424072410060190801d003640010b005104440c0641c0c4d580e0059000e01000d900400482c0da000340c00e0b0000700c8818a010380e500c1d4480d2054200091070b100044804010100c3d = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 33925454 1250 33924204 33924211
    0x9030210141b070c05040501180609140412090807080109060f0209010e06130302180601080601020c061605070302040e0304050a0807080304140d300302070209040b0403050f0c07030c0806 82
    0x1030b001c00e0b00300c04103800c0a28560050f0420ba8007400c8450b00020995214040c9a000c0c1031219003021880005c040b0600903664942c0082030310038203051901100a54401c01e547d80715070400e619404184280314140d81916241e00b145140b4011181c0c04103015805401081c0da0903c920410007280d00c10790103140480c01003407070a0b8000b80e455414486981740c000c004d0035804142104046280d542c0f0b90018100d8003526041003c01481d080400c0095a04800078039800f420a002500f1410181c5002900920407184030441010500400b802070200400c83c10024540c090006c1104100894000360703660001d00c6001e210708080e0601140001d0042008402c81e5130320f000442c18282800402c074901051a884643c200000c0c04101d00410a03007850b80b2000100d00b40c0c00d07451036501440e0007115010a840f02400e250040285070016219071001703d51103034100c44071010741d4482d0303c1e00300d5081c8520f00c018803240002082c0c51070321a4001c20348504682c4038030350941c011507642d010140c8415045 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 33926704 1250 33925454 33925471
    0xe01090f05060306010336030e190e090307061404050105130b0a050a0b13050118020909010306020903031207080106020607140313050309031002090928090203010605040903021014 79
    0x280041344465010340c1007010914502511442c0585141080c112482d681c0c1803051008805010007406042d0002d404d00d41d00342041d40d0000b12a06081c10f4401c4c2c880181c41481c2c605228140028291001417041c2c410140c1e01131001d2002d440c11583c001505441070ba0705941c903518217400314441092030081d00c0d00c695031121000e100f0ba52290f4807038004210081582410640b1108400201e646066400c1c22080c2c1000000a9a504018120201e80710900041b0191841000050120350f41d42c7c0b01941140c3c0d200d0b201589d683d0b1484046400d50055a01d9840305900c0c0740c0511a00c240c0000d1024180d8203281c0c00c4070381070743e9001c8040300c031800d5816880c2804502000461880540142d61491907401a800c40f4500b90314030b40804d10300444840c60030103059021540c070009262030402140c005010903900203080050903103000c40611414807401500c0d43d5000f400e81151020f400c0754005250040041081c1442c1d410065200c19000c904a103000349411b4207061203445480d8080d0054082 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 33927954 1250 33926704 33926707
    0x9060409150b091f090b0d0509060603060c120405030412050f010b0306101401110609010e01050105040903020c01050a11030307030501060305071d0f0102070e011203180302031207140a030e01090f0506 88
    0x41158005420000303118003004840341000c0780748006c440081c03501e17180000c00050140f410b030300d242d03050010241c5942d12070b4202000780182070000100fa542c5002111150760b0503611189001441e41c0b040750300c10070121918040d104c1c180134000c105401003900082c024800922010f04041d02c2e008200c58020b50b581040d2000c8c0700c20107a40104429800e410305000600d44008940ba40c1b07440c5003292014070a03074490100349001c100078000c2e107004044c103030303020300002c48107580c00ba460703110b240130791410048040341c100e001620a41000780b8043c81c40007582c1d071f08d0078582d0004024050034010800442c0c100030128031054890340304600084482c0c240509800514400c10080c0e4049a1006045108031400414050310180300c06000b459100b0f28403816200c5850040e00c0b0220400e5a881e11034050781041001d03841c08a041d0105025481980b9078030070044c81c1c042c0e070265007480d4004c09481340c130b185e2070200760b0007038500c0400382d401340c80c2e014400d50380703107400488001c550050780d400c03400 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 33929204 1250 33927954 33927979
    0x1030c03060203040302010e0a110406080307050d08070c06060b1e030f04020f1206010806041a09030a0302070804092d0209011e051e041a19110309060409150b09 71
    0x90b40a99000b610a2002003443d68010100f28980143d041095a1110440d0000d140618143c42594020111800510706140164590035203c0d540c6681d40804c5c4400440050384903071003030a0105185500c890300700441511006103042a40101c400c42403001d01035810180100c1103101568482c00541480d2025a61582c4c00d00c50b050117200c00064001d204001c014504038030900180740a080c0880080015107000d04000044420002c0b02a03400107100060180c0f44002000b2500b232012181000342e520001407500b100c0911031640042c011078a090903401540040003603000385250320640407400b24182d14500f9080388100d211040c04120302c030441502040110166209580c910b042c4a0306140000400c000c0b03d5110301d81e1111a0440010107000b81c00c40400c002da404040e600d03100382416002c02510040341100e54282003484811041c2281c0e0300d800300102c4800660142825840d01e581d9944840074240901032828070b40c1c180b03000401d241c6013820035a040600010031801c090b40 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 33930454 1250 33929204 33929213
    0x801051e01020316050312131a070e042306040c09060804020f03010c0807021204050a140d08040f0911070c030305130801110c0607110309010f050c060c04030203060a0501030c03 78
    0x428841840d410350000b0f2042e00034003022002c0800c4041d02920155a40380c0c2d0484d0ba078400048000c10042102010302c0242001c5524500301d18461914a80504030340d0f16003400c1a9880000c045070799078030604110f0300020740b9940358081d580b94103000202800d030b41c44200c00c10096074049004d580001c0c01c594402c101a62196100c42d0308107002070325038010703968040e0210742034a004400100c00318401400384444954100081c0c5040f80c0101c000b00c2c1441e003071500144003082140f042c442d1030f001d090200e0354296220f1200c1e8801c147e0202c3c85c942e85581d20600e01d006002140b0900e8100c500d40000564601400320451703880b15030003a940388050303003183e40c25102500008100b44030301210100200d4201400d200301d0102051b4403070099100d41c40c0a004514103040100080200001c0840e00300c138408000064610540302420014074400c03110104640038010340d07102c0c0a0f203129a0f030500c915503503000000d1095900940c260350710f40c0e60b45551785060350801c2c40001c145408400d42080441c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 33931704 1250 33930454 33930499
    0x906060105180406031407180212130501140709051005030903040b0a02070807030309091b02060408160b040c06020d021b0d020105120703050a0f1a0909070b0304050d020706080105 79
    0x2c64010000101c0f151281c403101040110800c00c1c2d4101c1e801180180f000314141849a0380300e14001c02c0561402c2141d031003231421240e001e4507c2d00089107543c0464204082904101c0030010b881da50b050542c0340000c0011715101252165074011a84500700c206e81c6407083e000c807445408500f0003540303890703c2e14084075280c0e80500d2550003180152600800e20300c000f40701280055010341d4800350078508041e0107100712100c00756441d0840894841d140003098012a10303640c0141c01562054070741d400041110041104848001c2032240800b04010404c0b041b41c0307010003900d03101d50031683c01c526580b50980c0e460380d0140840700304001070100703c8050725000058060b01c0744180740c9141072100d6003298000404051700ca40c804291620b0801c250320352948540040304110030414840281600b40100100c103142d500d00b80205c06140001d079036800c04001240c0180080d2079210b03034034074007401c1c02c0b504c03448061040c20044c000e0180008440d481400142e050f03800091920030766185010075840d28 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 33932954 1250 33931704 33931747
    0x20a0b01050d0c030c030516061d040507031d030301150903020102070b090d060c020d0e0406050604030f020f0901180c081504050a060f06090f080a0b0c0f09150406080906060105 78
    0xf81c403803000c00001c032051540d4000b144140018a0b2012110442c11504030540d04407400b00209240c50b90800e0701444c80a08048600b0f0f00e002445445183c404c13801b030140c2800e00c445020380d5100c02624410000000c604941c681850340c1c008080b02c80c4211505555440060f0059000706020700880c880700006114403280203080c90003000395603851405552005038603c0268100c040021400358014840704140502206c0402c195820b10002403003a0040d40005444000b030100f9076411526200d400910044e40180580020740c0e44003c1c404100340e4460b00b0311a9181040071b0200058014008030340581010400f030403848034142c5c240b10092070000c00112041d07403507810004001012038806400751035039944110041d401c3c0403d001c0c014925520402c1694054568500420900b84c1d0907900300c451440c550382d0b500c2c60400d030f4408a0007800c0c64180d00103048000c40310b4101d4528010421910b1350b40300c00c0d01d5583c070084543e4950740c0c112001400304e038007001018070f22030360307204440007 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 33934204 1250 33932954 33932963
    0xa0302090a1b09050f120601180b040203100612021c020c0c1e04060e0919020a1a0d0506010e1503060a03150603050f0a0302030d0b060d1515020a0b01050d 68
    0x81a030b001c1a00c0014090b221150b04011908500c0240b2141c209200c5041c0034020075112291240d00c0000042e5031508148940070415a203101c01484860700e0750009081c1020040c000d41d101c4c1819006240324044030f11402c408601103800c0440100317454000d46000c0c1200b0101c50300c00710b80300300d1020065440403e100440b4020003030220055030301c41c40105171807031704004803030382d8400c0900a2204a4a13241c10200440c40500c0c20080c0000c0300013072100000b407050814101280d50761021030300e08981c5030804142403030030742d008a41c40c0c03141101404007508001ca0608c001e845000054945601c031148094008614001c903a9024442100440d0080c0b0041c0180203820b81d6502c032802c207249002105810b0540781d903c10420f00c102040f59034180c165041c0500000305a40d43c01941d0380c401c0c50060103020340c84d141001c049540340010b68292104901c810320400300d03c4101c10340040e4440c000c01003191000707002c06510600c0000c21410b0190700403400c8500da4280070400002d031105400444 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 33935454 1250 33934204 33934211
    0x80c030c120a06180204080703120302070b01080a1104020a050a080c0913090501050601110d030f061a1e0915030a11070c0603050c030c030f0723070302010b06090a0302090a 76
    0x30707041c040c031082040c0b140c0d02864000903040d0410f40124102e490b1428808034a03401070005001c1c0c80307008107001c01181da000f4500300204884640990284c06500d90280c9400c1c1010000100702401141d0100700c54851280324100d110051700700b008038040c454607103001072010f101601606001e010160f401021592100341044540400294851144510312a0250b2203480c410704114003402001c1e00324509080608440c08281a02c940c1d5816281828040549484000d14008090350005d0040e0800b0080c1021400045a440d10154031035080d66104444e10090401c00455003c25100301500c0108408840b100d96110700200d6000501005482c03a5580d288507038000180c0d0040480a2007a16a04c03143d501e445009011540018502c0321680000c208200c85c0410340001c5030b0340859204040c111a031581c400403203c46800c0c1988202c8070341d443c82940e04803040c0e40c001d000e03800c0c8260b00a02c00102d07030034180501030040169494208a442c0400d10040c9072000c02c2c43c0c0e10180009001 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 33936704 1250 33935454 33935467
    0x10519030803070c1a0705070807060e0a080702090f06030705040b01030e0102070b010e0c0403050307030804031b05030315030109020a05100c0b0a0902010e09090d030e03070605010f090615080c030c 87
    0xe162a0b4400d44075400428100c0340c04004101c5442180d5900a00e04c203003010182c903052102034014410000e0040c10840001003043c1000116030000407006242c0003102c0b15a225441c103580b56903c010000c0e0301c035140480008481c4c0d5120241c02d8401c1001030068424146400f043c00042e015010546060503103401c05c2c020030002c00d1000c2c02216000c0c0000b003209525050b00307070700002c00107040b800c2580c03030400040c0003107a4000115440707140d00d890001c41c159668201283d099042d580c2014901070400040b4040c4840040030310b001e100d6040c0034007a0020b50004140c00c0702e6000b100250860003c080c00c00080c50f0448411003034900e241000614002155a0310340036400c204c84a501c920303079490b108025540c1c00106030100c01401d64140b0038034100116203c0d41c803000c4030511010907450b91b0848224020034820b40310780c5980040d0900103961203003070000f0190920300500002900d0702c800010030303c9206000c0d90b102550b5440f6806d003604c810601c0d400d950b00041c04580e1039071081014 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 33937954 1250 33936704 33936713
    0x509010c08030c09100507080a0e0f030d11010e0d020a02061806070c030c1a220b0c01052a0301030b060307030212060f0711030f0903010b180907060c0b01051903 71
    0x190f1003448110b2000c2c2d9220700f000d00304540111610305840411038140303c41400104080c00b15040c81c101c5081100c41c050243e000982c82200b19a420358050085840120000d5007028007400041d5102000b4480c0043c04120300ea540e0b1400750400005a204400d10409800c0c00c100810b40d041d07400d051071110045031800310300c3c10340c0441022510240c45c400104244075054614030b01030040f004c1d2600c4201e0900142080c02e0003a61740304991603004e99502000e8240d281d82113002481e000c50820380b00c468511f4564028001104c07400b41c00c20b0113002120b4038400c94a651401071900c840121300b181d0030340d03c1d010301c0424009e002e2a098840e910001c00075986548490340d200c540361004026601e07103401d00e590001c201506075014406c905a4551900d54084240e03030642c01c1d4440308540360004440060f01400090b41120381205c0c1c501650b066041442d0072240c8a180c460086078134842c0d4134071045a02442444001c0c1c5944034801c018449441c24111007030440004000d8601c07026280d8a5 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 33939204 1250 33937954 33937957
    0x607090605030c130e0103030f050901080c09040f050c0d2003070f09080709051806010503030405100219060203070f0809030910050c0f0c0f03070b030103080f0408030409060603110702100509010c08 87
    0x403025101050350010008c040d8031020040f140340c40c610300f050424448000190140101900400180718041904c13201521268032400500d10018000d000074102600444042d0f4010200e0031035442c180310f20300e42004596110120840100500c0500d140d82d00300c0c04885000b8416901810800c03502400201240108034080142043d80c1002906040092001c00070800b07080000001d80c210384010025a5808015039048030001e903024203003507001030030407800c10504030740b6985101c0c0b80c0980c1100340700c5070b81c0c0035502c035220945600098140703650341511140c1048078040907a5108012060560a22403240c00e0641c002e0305220f403e0804840030a407c2c01c1d010701114400f60b10800c99420305203030080b0303008401541038003d404454103108000c0007900c81400042d148840000d0701030b00c0a03040b10300303c81c01000010180d9480c0d9445008081c094922445240300103420021511915900d0300e04880300c4170390013059a0103481c0d4030301081d16960000a170190501c8036223018600030410410 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 33940454 1250 33939204 33939209
    0x5040e07030f06021b1c0f03020f03010f0f050102060c09060a030b06030703050406150308041a0405100305060103150b07032a0308090f01020c12030c04030f0308040c080607090605030c13 82
    0x82c00942c589005440c020014907400c2d400c0c440c0c691010440c9140f5030300000040814006c40c2c80d00710240382e41164181e010b8490740740000440e0800000000300c04510b0091001920900382c801082c169a5400490780c2d850b082e90010110b40c8100a0f1019078a840401040804028140401c003510070360001949504122542d07000300b40c945040100700303d102d03c55103aa0b080d42c00704c8098810300b144c480071007030b00583c041e40d981101d490101c001c1044454003658010240106030100401624030018040d1800307841140c00b090904404807020040810f01e902502d505201071401c098007a01c00701d5210005003040c40c3c1d00000800d0003000070003c4000d68003954040d442c0d210070303820602080c03490022801e88000440e441403001d03a1945401144100b115800f401c03100d512911010390441c10f503c20b03580010708e00d55180500e401055084041244160300400b25040515031f901400d64440608480000000f10081014031450307004001440d0450f81b48100d43d81860100b13609100c100d20f854 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 33941704 1250 33940454 33940463
    0x2401021609051005120a0f0c0503061006090e3d0902040e0c0304020102070501110f060a0c0e03071505070c080109081e040e040308130b07050301060f090f05040e07030f 74
    0x18020840a2540c62040d0f400030f0005907058695200d09400d0a505c40050b182c000344004184900340c418402c003014030002a0200500f55841401c03d8000042c0c81074091268002007002c3c14000a9184800e01c8414411141c0030203a00d2100042c6082180344910303414034240420704039080140000104030524094540360400598072814040c4003c1d41903401003e104291604108100061340d020910108980007803c00c0c04c050640541c515080c0103002d01c919900d44601e4013009200c9119800c0b0111540c07603a100e81030024135103c2403540704d440900964031034006010a891070b1610410003001e08034041c46581d0006034030354203e10f0035031386444c00030303903da150101d225a0030402074180c11042820b0a40070500d0301d85402c03a0b510710010024009000d0040341400152000311562501003030b03550148c0c1c5a2003900e01007501400c25042070007440002055455500030103401a038207841914401d04003a18001c5c41e050801000e00411851f68205000b0b07048000001150604081c045034401d = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 33942954 1250 33941704 33941711
    0xd1106063304090e0307020a051207090e06040c08060615160204180201030c05161101050d0203070903030e0409030207090504081e0909060a03020907030b0301150b130602062401021609 81
    0x40ca00c00700184d0f00b500d403030a0ba894004000040069031175a81040440d0426951541002c1c1d0020189042195039880020322505107009001049400300e1070798444c41c8035020816250f501c8120a9680d0942103902e15044400c081e02c803aa00c0141d08054070440d07000000700c4800101e9170b404501075502087c0d42828030645448000e0071580c050003003104081c0c00345016400c0190f410307118011404141c00281c4180c10030340e00144681d00c1102241c1c151032045205650301d003000c0100a0400c94180b10a03030004401c0d030001171030303880c1501136183d8007a01640200901c40c00c01c40035800802010300300705e40440081000c00c100c040e189030b4480e014072190030040c0e1513002c51002c0c040042801442c0c10300c40c00e07040d00d0600040e031b551250395420003907910f400500d0301d822501181c01411010100705180c00d1a000001d94215134000800340308021441a40e02d69950306c0c81640d64240540740000b800031810990a00c1c00c500391000c0050580502c101d400011054180c511207038169000f040c0d110b0b4a = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 33944204 1250 33942954 33942959
    0x10f0e360102070b0901090c090f090b040f0b06040e0d030e030c01050106110610030b070503130204020c07090b0a03031e0915050d0c0e10180e07030e0d1106063304 72
    0x60440b0000d0344802181c00074051280b03903540745400c1c03a4803030003400d10300d594034ac0c58050310311003e900c10400642d018034003d016040a0502c3c1c41882d040480464110341f865000441343e04281c000c1200c0404228000c260301100c030581500070780417456800d9940c0c807043c80308210754042401114000e11064883d1540807019000d40d905182004044603440c8030a80c4c81000060205d54070507610082a1503c181c5a40320050302d030429581d2500040c0d4858000704500700c41203070203c1c80d403040f105024000c0104d16107000500240c440d4610015012902c0314800a0f408050b54400c003400400d1460115078482d101c21825415128440440b8001070000c0f0f04206000494807032840c404142e4140090601c3c1031030002541c401307202006c03000300600c0f6820f071001051440a02c0c00a001401540c4256241584004000b050140400205480b800030341c1c0c410382d8005ca03d1440c1c64034409028041c0b81c0d5032182840340416920354109610b402e03250b1420340a41c15403401084645102149a540d80e1 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 33945454 1250 33944204 33944213
    0x70206090301020a0f11030a09030303020a05130e01051008040203060a02030702190b0117010e210c0601080c090f01060c03030b060d0903020a02030610050105030a2004120b010f0e36010207 83
    0x101c0059046c40b40b41e00070000d030012140c02110340004c881d4186005641c80403900c0040302d10380a1764420f80710070345a80b003001c11000d0010740030a0595106550301c00c0d20700c05141040303651050503540a50150081c8000c511140e1a0703400469100303d40e4011501158010414917014a81495043c0e82c0c040c811001401030301c204101d0801c2c61304550b002070088645110705562540d00b903002d46061212401d2100c0848201801600c841881e01c0059a04139a541c0c96801e484100910b0304510503540980080e401c800c0080065060f07403145c0c0d9403602000880d0741e081d001803189401c0b80c2c2c0d0109082c04000c1100b006401410b1541c4e00c030354098000d850b000d106052506e4130192105c1d040c00d0584a0900c000c0e64888141c95021110400c08140c00304640c0803080310b50b0041503101c86c0c03144001804544003030f1400540e086144a0240c84400341ea94500786c520141c15409080683c9240c500881c9403803045000d41c0700410514030000b801541c46182540220040b200d100c1c1c42a500800e8490910 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 33946704 1250 33945454 33945467
    0xe060c060709090c0e04090201140a030501080c010309051c03090c1403010c09060212070206130b03011503090b0612070806180606040501030503041514030a0207020f04060e0c070206090301020a0f 86
    0x504901c20248656072103c2c40141c48140904005c50181d607890502805680c4100819100c0d100c0010707109507a451700020041c09040c0901031941c440c420740c2c4041055510a200e00180b01c0d80180280c1090100340580c51141000d45040e072003010384a54400010905120707040d00104071072103085034412009424036087d108482c4d1324000f4041805c004000261f008621039160b1550803005607940c041c00d10000c0c0540c02517940603c05124844404030700585040001d6040c2d50340c420402c100701008002c21010b945110000030a410a000042501828410700720407001c02204141d5240a0300c815109180c0f150450b0368085421140f84003181031501403102c113400400941d014072880d030468807104e60b20310903813040500c011100ea04615806103c1d09290078058804420f46589045c2441d943d0080c2d0421102a44601001d4201000300d10b010710404040300d40c406056402ca50306c40d03034143d00c29004080145c0e003007981008040200c1d03030203100518882d4802c1d10f856254a24004c4020b049 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 33947954 1250 33946704 33946709
    0x90705030d0f1803080301061103071202060910050106050a030509010f0f020d0b06040803031612091a090c010906030209030f06040b04050c09010608040602071119060318020105040b0a0e060c060709 87
    0xf0700303805081030001c2054501100e055a9050030440c1e0100008108075145100d00701014098040c0d0160040e0241d9010030b459000301c159408a415020307843c070001c0101d410a21500011480810500d01c2043c020b03040182d2100f0314000000d1010704422290b010b95030100059001c980d40040c580396600d0b41c9104840481c042070716410300f090308000038a59030b840090072500440441c034900c80100792150211941c1c456034a10140301c110160304d4a0130f100d003041050150a50148000203400240c0065581981e50050350781d8040503240a030282e0096004035440354041c010304104001940040050328025449074401180c1d91074136051244c02d0005d4026910b20814900004102160780200710715003182c0c0200d001643c0c5c14651420190b20000d01c0c51b401c0d04841602c061601420f1440c5085046450707075141404902c00c0c3d114280308103d00140024040707001403100b0f1200310282000b44c0a0b0341e1130383c11701c3d0f002c2c41da4200029010790050f80071002c03281e2290040001c00d540c4444c58200 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 33949204 1250 33947954 33947987
    0x1e081906080a0b0a0902030708030901020c06210403110d08090708010b1302090d02041406030706020705010f0302251202010e060105010801050927030a03050610090608090705030d0f 80
    0xc1a051140c103603180d040c8404042d01000c040030124802c13141e20340c402008158002d0403240c1d11940c5102a41d1603811044005015006420031a42241007031000c81e5120a40e94800c150410901c50461507402800380040d002c0010b05840342c2c1030b40704200800f651580c0643c0703600001d841c004901d070f45049204d40000300c01c0e9040c46a0651652504811034400143c0c00c000941c0310014640440c40315485100060f6010f81080580e000c0360410707503801d9002e8207090b0180c40440b03407101b200780c0e0b9504045c4211400184480d82d601c030303214820780c050300280c000c04650000590030700000d80c9450000c06000d0716a6101e551411680381c2c0c0910a100d0303210b4020303019085540c50b00b00080c240d032605100d907070300032108900001c03201d601ea040d00218212100b1b143c1002400009902592904012031510101c1d141c40e000c50041c0c900f5001545502401d507949505141c01e0290803508290b01815448040c07088403400b10303141d607050240110307041c19607460481f04014104000c0120b00c64084010 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 33950454 1250 33949204 33949211
    0x12030b09160807320702130504050325050f06061023070302010b09040305090a05040b090403030e0f120a09050d0c03020f03030d0e0706080c0c07090c1e0819 69
    0x12941034012810540c4000a0f080540c44000900560203680d4511a1302c014074074405042a0721911040000d400d5090003564007005261155010008440303003603801904650044c014010800342e161407800110003000e030302000d51152607407190b150458211104419420030310800403c2d08003c00682042c45491030600040d20f04000000070250403000704030110080041d5000500d4001d400419a001c4003511540b91440c050074010160b40060303040a2007038241741d900007101c0c40d15000704000c1500c01880008681c54507642940146100c200c2c0d07180d00e02815107084038440c001c0c0304007500c10a20911035503541180389401040700308203030080c0f031268100d0015a0081100010004150703a0305942040400d004800080d10758002d041010b45200d0411490281c00840401c01804882e8a6100d844454607604204541d501460a0005265001c21400c00c40c81c8019007200e509152142402c07101d03041c0305449450310245941d100404501540c007404000c0750b01c282007008001a0742e6042 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 33951704 1250 33950454 33950491
    0x50f15040305070c170d03060506070b060603060f0d060902100f20011503060609050a0b180a020d110a0216050303040620010e070306061a0403030c050a12030b09 71
    0x116044068805002c120000c1800030800405403800c0010300340481c00965402c0011490715030760b04100504400090503e94005050304003281650b42c0d4552002140d8019919801807000d503800060520340d010100960181c0b00d904c441c4805002a8041c1c1c0d40410105c400e070041c030101c114580300c040100000320091f0f601c043d41c4510f00000c0300380042d9806051001c000201030140007000304002d100041640c2c004104051548220103c403841c09041c42075a0303d00c0381100032070708480110b580000301d5105003880000700454669105000010040c2030260341c81d10070302240d00c0e00711440c4501e000066003c41031038040110406181c0ea140c1c41c41241800c28000c04e80702e01551040205205c545200b28610301002690026a110140002c011408008a20710380d10407891000b03032011031411801203422910381006000344a40181c1803454117103542e0b4219420301980d9010388a0f406001812000200c8114103d048980e20380c4e07003c200c1141060802c1010784024250010041984059 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 33952954 1250 33951704 33951733
    0x604030219140a0e18010608061509150603061203041a09130b031207050f030304050a0308090f2109181006050c0703030309080f0301080616020318041d1009050f 71
    0x130b10b5030040700da085100e030480001050501601c01034000010b18084c000800c03080c1c180d9081c103d400070070216600e000c1340d203800201444103a40000c1e00c50704280b040000607144e040c5005500c1104c1e83c0359080328505070b9219100c41030784c010310000d40102c000014524000e440c100a42a2000e1029901000b90100200019030303101e11003040c910510401080001c24420b0078000900b401c81044c00b901d640c2c1c1307050715025480b40e4954800300c0c082070300000869185c3d80b0002d489403071044901c0040a00300000f41d03030044a20310301c42403041004c030300300411040390719480da4070300242020300980307051400e0800030b4456541c1244c01c041e08209003840100ca0300e03000040e00008594060600003400070a6041580d040e210703092a041081d00000300000361250700241c242d101d4120390305103040440c1c40c06812a1207110303d40c050b506000c00156842c405203019400003070442204080c00154080f040400ea0034612000c04c00d00303503181c2d60080001031040620150489880c40c9001c0e102640c1d40c03040 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 33954204 1250 33952954 33952979
    0x180b010206010509191b080906010608190f0207060b1c03120c050c031206030106050907020d11030c010c12060501140d0506010c02090f040c080303010b040b090604030219140a 77
    0x80320304c601c41c0070b00458010344080c100e00740b4154000d4818011800c208100441100c103004660000865900018403010b030082a100e042c0c6001d5690343c12203032a15050301a0301020001040c851941d42d0003800603000143c4010040a80314403400300f803803a1903100300441c61000041590030328412842c45800603038004031113100001c42c0440000d00326414881101d0078003d080f03150801d0300c03002509104515800200c603100340400c038000e1004030788810030300140b04000d0712000056402020140032440c0198a440504104981200d0800d07016040315400c0d191070144071000700361140241c2c078150125024540c00b4120a0800c500d6003694000a01098400c0700390405445030380f0400302e0030580c402c0b1106078105030010904413050412641c0c1c108080070588003181d203c408140300103000d11011090364100c40090366142e01b07052400c1181041e651145507103a5014400704400300040c1e80754140900d480100840c020000f81c1400c482d08245010507820501c0768803444410041c00d40f0111 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 33955454 1250 33954204 33954209
    0x10f03021c05010204030f0b01080109020f04021e0d0c0e0d030c03080712050103290f130c0504050103050d14040b04060e040f0504060b010f08010311010f11010c0504180b01020601 79
    0x540c0e0024007072100c168180315410210004000c1d500008000092003001c85c150007559005030050b40d85641c1e41c01c503d50813075160100094000c640f01280000030718056000e404500d001244980900ea622030444c80c07aa80303c084481c441d20780d6030132401c0020b44d0042910300314050540b9194051001038401802c9951250700040404c241c5100007030101d03124006002203c48085000c3c005543c5900d071600b05014903201e001145007640c004e074030351400070244030b030b0007a8009013480300d003070721050340194440b071090a0a5486504035a0700003140c0c0c03202d1042d80e008600800240c00c5480f5000402840704410040880100380309000610100c0c080c4003c4408039481400c1801146200e80082809812000e9803d15128648010081032200b55080500e120302d0990325000425014802991400c45c08c0c00003400c0402c0c2d020310340304294052a1044044001800c082040c444444406800d440520112900080c0003040030024002100105001c40c4403c050502000c522000001d6030340741c051 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 33956704 1250 33955454 33955459
    0x50102210c2d0d0204150309020108011a041707090c0206010b040e0a0902030d031a010311031915080705090a022701050408010606050315040b01050d09020105120403081e010f0302 79
    0x44468002d034900094001400780969800b094960004011890094101c0d10034581040000c520b0601003038482c0c0300c0c40e500e0682c140c4960710340380d0030700c41040c01c1c80311148583c5601f14010003000c51000380514940c030081d10100010480f03581004829420341d1060380580055601032070043c000025a5801e480940d40b881070700c11041d640b6140c40c4000b61210150182d010b000301c2010741403040d816000300c101015003500d00c41040303100400450888611009040b031080003480420740b44000b841040340c024041c400046818209000030040c03080403039200040303d0f804108100b207241042040b03158015806c0c9000c5060614041d41c6500e0b8158020350301c0001c90000f6010300c00c0b40c1c02071058801400c0c0c80b0000300012600c078400039280b0fa000741c8984e401e0f00d1414a21000a1400d07010701891282e042c3e44160401c40ea0805980251a407150308038148030017070200e04038540c1d5805480d48610300954030155641045503200c0700355071650180c000181c400030b0040c0404201c8208000c1100e505 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 33957954 1250 33956704 33956737
    0x20d0308090c09010303050309010c0f0203070809030304030206210c07030f0e0310060603020a020f030f070b04170307030603061406090601050a021002131806080c01030e01140103050102210c 84
    0x10720010904100501112541c400c08610000c0207056210018521130300d81d840080185400200054544400340b0701c1110060b8070400064000440e50307405807900d03060180c100d90806880e035002440a0300700a10b10503105281030504401c204120b8401c0b6045540d105110f45442071a0300d004007182d100c991404103004450070340c0380a5032020003951001540c6c000042200c0c5444210003400f070742c02058000018419032070810390070b08000c000c0310600700b41c4140051a02c1c0c40e5550303940c02d4010060050f42c58102806001143c1c0c02d10070000d5205154541d0005070301030651a01d50121361130103420360100c0e0a54802c1120301d0b201c0c04001900704600b402d01e10f40b51035503014128501310103d00da0251050000c641c0000b6074144005646c151501801c140c4000080482e22408a5081e807146c2c940c20f60101e221a0307080e500940c800c0499401020004c2200105500c900190070000c0c0e0003180c03039030350000b146040090b50017024003003100c018045140c0c6091101c103500142c080e90072841d0700d0000 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 33959204 1250 33957954 33957961
    0x121606050c19030b031203090d082512060b070b060906040914070536040201090512060411040b090609060a120c06120b240c01060902190c020d0308 65
    0x11040c1524031482c4961161082c02101a0b402401343c034810740c54500038400c1c425a41c000ba2003400959110740209030003402e0086100b0021142000050b1241c030303071080383c6242014003440e681c1260042000c643c0300e03204201312140342e030300072641c29900080c00c0c51024049000060900e1414a0300071000b01c0e590035094444030002001405400070080084e503001031103090420020903c84201c0d081140c003441100c050410080c40090202580d401c400d01e000b10b640060315002c0401504640103140c030845998031100803c10281e4001003d400ca41c1c4403030100001c10181040ca4000240c0554044c0051401c0c000440c1031010003a0840748100840d2000a46a4441298100080028800c0c00c0d8130714146040643d04000310b8002d140000d4410062400f0b078480a0203440600300025100f0703030200a2400e20400e001c840d4186038054010104162502c04c202402100c0107055090001131340c9403c10500e0006502c107200000c414815241c030b403540540e071485115040940c00d81084022941d = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 33960454 1250 33959204 33959221
    0x50c0909030d02130f050603060102070603091703190c09060c0201080a02070206070807050c0402070c0303050304060906050a06080c0f03030f210420030a0503040b0a0201020405031b0312160605 85
    0x40c01e0011245603101003648805054011402c8045410344179030243c0c0a500d50007840510f1000315201800360b84941000c001091090f8803643c440d40c043c0740320040401060114505e107503c2a04c5c28181300980b40700c030b410400828070a5520301303405800d00080c064500707240038101030343c401e2000c0d041c48001030009d1451007094049a44050740101410343c2c820852030520b85c01d0f0010b000503074103407003041c55600141c2818070865800036004440141c1c402d15641c3c0843d4181c0c001803045802d941c9401290303000510a0040368024202c460002c6074140c20b20740f03068034200d020700d80c180c41640104c2540c2410b460100448004420060640395a03015a0203003c010140300b460b0040d002020340c08010a0141358420268542d60800d483c403441603001e010950380740b0f00c180014140e90001c01c410001c18044100401d011000782c0005030802e81d4410001c2d007440c10400750700b810f8004141c1d0904440c0f030b0074070800f8068140c000303280c1d00b00012908480800101050010100780d0b40d840401d03a0103 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 33961704 1250 33960454 33960457
    0x5011505031b0316080303071b1523250309170304020604080a030306050a0b0307090510022a01020609070b09040f0e1b13060605030a050406060b030903180105030103050c090903 78
    0x12940c03072940c03990751205900d46c0ca5004440b40e41c00242c0c0050b98050180c261454021940c0d00000805a50a00c1c0016540185002c601c044003074004c032402c4995480c03035486118802c408206090300e02c950302d9006d60410b1440c48e4040c0003014038020301c0d2400034818000c4c0341088550603030705545996851011030020f11079034000725014400d5425074000c05516802035000d40e50103554040900d0764440f4120342c0c600050380d0540c0821041c0c0014071040c1080101c030120f0307140900c12240720a070111074554803d02d0090958286140307600720703080196010041c15800500200040c00d41520b0802900d62a02801c100140304544541128030005003c2c0c1080351080d480800f41c5213122040e505225100540e1000d041c0a27a0b01d000703110b010000c0d5803140004641250300c41c1031543e5102c018580c01480020302c01c9500545d140c80100e0340c80d50302006540300361a92402503a80d030304440a40783c0302200c1c041002d410050108010700008001003269855070300c0c269005102030302c1d07000d4400c0c00c6 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 33962954 1250 33961704 33961723
    0x2010c020604150306060f0203070f030504120c05040c080708010e04150c0509040b0405060105040603020304020406030501140411091b130812210402010c0b041703040803010305011505031b03 84
    0x100001250200d843c524a0004507200029600e08204203551500b003583c000b865000c4403000343e001030084e40040340300c100b2103860551080c50902d02d42034444081041d4990722800680d0f241185613000c0c040c0b81030901c28040349141d40d040c007100030720f8080002400200c0500030a50b501b204100070a0420172040620b488882c0e4051003800a01d000c540c00400c0745d003003810000c0c0b069080000d0b032180c60501c0c3c414a13000d4001070752942d2410781002400e9020b03500280080f604695501c05c000085003080c41000c6100801e648034607013908080c2840e4030480c00c003035030742c3d4814807954051040c03e00c07036622040700c420f284605154407003032810884528a600c036405445280241e01802c00030541c9803004016085c140421b20f80c80c1041c00b4600e859030f0004a030004d0208541020000c04150b24082140d4458469003420b625200000c101078140d40065034125041c200100050041044c28018441704241c0c002d05600308a1900002075600c08001030081c14040020300401d8664400340008101e = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 33964204 1250 33962954 33962959
    0xf0204021207080a051618050d0506040b011a07030e01020a02031608070e090303060111030409020f12060301020c1f060b030108030415020303010f0b13120c0603051302180402010c02 80
    0x1101c103210040740c00a01c1c802c0300d900b000140207200041c505021881424000d8110030076400c0c3c42c81c481d80f41542c00c031034050103d0494503e010784c0040e0070b0303882c04d0f21540c00d130784a4005450b00d8242454450302c5e5450681103241c032407003140700901c0041780b560b00b541d10b110340602c1c2a040c04200350300140d0910700c20b510060b4150040c2003601800509840e0f942084070200300c2141c40180e130b035201d041c1e0358440503103c00ea032030303002000420290341c440d8a00c0748070204480d00352407820359200c4441040b640038298030072070b01001181c107a0300082c000d54207907404401900258941000005190f850303100b50448a641c0340e1111800202c461440d5024001400d41d002d03901e5a05c0d61280c125954a030080c0c802da58032050b041d0300040103a4408000e5078125491044d41004541c20800d0519882e046100681840082c0e01c2001806a07690468110030368024407850000c01c4c1015802015140000d000c83d12480d80c04c09100010384079104c0720600c00040c0041c1182d40c0d1503503c01215840d14501c4003a6 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 33965454 1250 33964204 33964207
    0xf0b0904060c020c0d03170604060b0301090e1009030503040f050102130311031606080a0e030910050a0314130b0402030705030d020d0f0e010507080d09080a020f120c190f020402 78
    0x1080441e610036500741c1c1c1160216094a18001c1c00c1201540c10001e0040c0050301c4c9600307c1c000e00c0c004406454101e00020300c0800c1007038560300c08906540090380081440364480039280c4c1c04000a1001114600468a0900c06030b0f00300c2c4c030040c0a40c800171700000c01c08070020362420140a005e40c151040c1100c4010945e904640ea0f01308400c6008000307070b20300d210703000c0c00300394008608004901c1c1e811600f0584070101035641e600c400300014894803018409500041041000131340c0d80110b007540782003907a2a080c1e185d40b151b40b0002c044884069007507001500311818005400c140600a41d419548000601095074981c80841e0a003c039130b80c0881c2e01407240103041e2201503000314503000c03810510742d1040140b072040c610845207035070b0f103c1c20300d03011403020000c440101d1b41e03040061003100d00a038008607400d6900d90300c40106a021180100c010707040f404a250f01103205221500043c090001c10504086903002c80e96283d4281803244407541481c0c40c0c456081049005030012070310b0f0001e00c1103 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 33966704 1250 33965454 33965461
    0x9050306070f110312010506070c030203190506102301020111070b1e0f0a0203071803060519090c06050306010207180209040b01020303090d08150301060b0409180302030304060f0b09 80
    0x80c0c014120300b002040450900b042c40b01c945000081035400180760507490003916440c10040c401264096482600c441c030b00ca01c0b0100260f241007003d801c13940350600b64420440c0543c240a07080000c0544901c0003030100b103804000f06180200701d6010f580ea1205100c0c000705580c4010b03401801040c41c45200a02c0c085008001d0000e11007115115603655801c000c940764000034001c000043c1200e001807040311101c00706000c0310281e809954814024100400c444d090b240c040c251a0800786e104842c0980c54400b00304102506d4201d060090041d4601804602801c0d526002214424000e5504004001c00011002d0b8401c00c441c00080840c91245040c89140c1d51082029500c034141480c000d070300388074403040294030002c2280e00c54588607012703200951444900315620b410290140c120f54102d80c5030480316680031712071680200803010403076076520f262444020641e003290030224107070388507800c43e403001c250080f040740e034466440600052031000c4080000c00401185a000c2e0f0403204000c01c1 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 33967954 1250 33966704 33966707
    0x3180f03030109110c10020304060f0228020a170c03040b070c0302150f1804110c0601140303030115030506030307060c0e0315010f090f02070b090a03080708010e160905030607 77
    0x71030503a0942c080c18000c000d116401d000c01441905004c0c10705038004c441600c100590b80d4061508240b05090110b0308054a440e184280c2c4c00540c0d4110340c1c030800b14030179144030300c11000b1204181014000b03411010400c0e2114640f105913072103104248080000c00e401000c1041c07049802030071140c3c041070744030072040c00c003200e101e001400704030300855040c25112000603501090768a200a48090180742000c08402c1d40e031015034440f01150050b840c2e0a6000c2e0700c41d00f100142c6900722080b80240300542c03402c043c7c42d00c405d4181003042d0007030b0800c00040c084c070300d1030201c0400410a241404030742e40d1a0790022a280d4455150060111840e240c0f055207a0303540403c030720041d8a022401ca80c0a0007e0f00390814080741c0a2092843e03112480804011502d1590440030f074460484100608045442d10f51a88412044a000340150080b081c03100400d900000b520b50003a295103007013071030781d810040c41030740c0300201505080032140032080ad640c000e03104d8038080f005010094141c8a103400c00900 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 33969204 1250 33967954 33967957
    0xd050103051507080610180504051302030120030f070c0b0703090b07090f05010e1302030408090a14090106030b030307060c02010f060915050d14010e0c130c020a0803180f03 76
    0x20300105003a4094007182030039200e640c01ca80641750051040654589402e0140c490441c4440c503850b4001c00340f4000a5180d070742d440744d503126094001d1103218001c490b1040608403035000460001c042440c01e5190411501d40050301c2d031051070b0312482003841c0c460403000d483e582c2c0300000082403028070340d0400206940c141c0001c2c8666100f8441d242441e01d030300798103a801c407903123000c1d8681500500d10200080d40c81643c0072a00c0a1020703080c88044140402c1080982e401200c09a40e03c450000e00c41c4e120f0b040160700e0200902d80305210040c43ea00082c0014403000c010300c1220700300350300c4281c0708800b940d081c0708460316158042c1c401c20240520300c50203400f90901440b80d5001e10300d041c10005003000c00b07000d080240e606080c00b8000642c02c2600f0002e10110801e401d984403002500d030b601002c07000340719120401e60508005e16a420044041000d0508894524400d09051a00d403800840d0000354202c2c0003680088150384a40d90148506031010075410044103621800940c000f81010200 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 33970454 1250 33969204 33969223
    0x1c05070c0309050414161107031a07020a030806060f0c01090605150a06020a1203020c030d0608010b010c0b180c0607030306031a04080f0f0d020a020c01030b1905060f0d05010305 78
    0x1200d1018180d40c070400c00c0101d40c00d202210307802200a17000a0940701c0200c805181c0b000403401d00d40e20031074040c0a118a0041030f90403c45080049200700c10308004040201e40c2e04c410203100424242105580c010490f00002e440702e4050080032071940042e6800c04141c83e213191445008001e04089828210b000d4002601e210900d00300c0d080070404035003414444001518500c1d0014081014550340c0c05018401c03c464483c00c140d400e0221003d5102c0910003041c2005108002040d500c0c10b01032400c6c02c640c1c240d400941801440940000000c1050380b0b510390003005016280c44104000784000d06121400100b19403002001915004051f0150b105905483c040c0030751456448210000f11000790060700d000d00402c9040c40350f10400440700004002000460780c40a082c150540010700076600000743c4480507070401644003400396498400c1d541c000c48211006410b0802c10301901d0b4000b41d65014040c0980c0f00016201034500d580022141d149a40820400481d03940781001502c0b40c0281 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 33971704 1250 33970454 33970457
    0xc06020313020f030105240a0f030b071202070c0605031003060510080c040b0102031b0c0406030b01050f01021209010e0a05060d020403300806010309050d030b0a09060803070201051c05070c03 84
    0x4603030f99014141441042e11032800e58444066038010080b00090200c0e0300040568482244900880d02e8081c64202c03000071441007184d0411802d0130100580b8864054071114845071062055002144149842c6422070b00242007441e0b8a485504001102d507a5540000c1c0110b810603041c480b10f07001140a40c0c044402a0050715000f41100701080181e50061403a1401a0f00920080ca0101710010302c3d114842c1100b8111003140c415480400c06907001c560058902e000070200401850901d818107035240c81007480548461701c6880013103c440e01030030001c2070410400341122801034407156900000703083c0080c545030b01c1d0b45440c40b0749030107503101e800304661034408030100b100346000b60030400301d00b00703510003a942800642000807100c101005101a0415460b000030341c0204400b8882d420035016195004250311a1f5401400504140d6902c80303002140740c03003801c02103442d01109807849558240380c100c0e41c60030507400010784181075030b45010046107020203201480d500301d507004039018405d = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 33972954 1250 33971704 33971719
    0x31d120d0e0102040e060609030712030c0204050702060f0106031e0e0105091204030804051c080d0905070f06050409090302010207120201091a0702060601030e031b03030f01080c030307080a0c0602031302 89
    0x1001d2095090b80240c0c803c900d94240e0080115846141410140c03986180140c211915a596541c0d0031040020904050700468155070b00746042d8102801010342c003c0c1c450000300900d0808030781d080003080c0c052003101c0805a4a465900401c466241001020a45001c05002141041e500f4500030081901c1d80350040c0f098803104c6000307240da10242c504480d041601321341014500004d005110102401a1488800340d9940302d00040c49003024200300406404005060007103440e140e03240c420786070481c000341c10710400c04200c8941d02c2003c90302911802d000204d500e4440d4035043c1e029006442c07004101255801d403a0306141d41c1544042a0540698107900070690034580b50440b161040e01c0840041c4c001f0400a030310765010383c00c05004202c03102c0841e03141000c1d4502031100035244880480300340d0800000d00140000d28107403607001d05480c0e4050404140c455000a58030b2140b02e000911000022521000d0785008001303071001070fa0040c00640d40d83c41c007414610040c05900400701e200d00d40d03 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 33974204 1250 33972954 33972971
    0x13090b010201060302180a0204090e0d02071e091a03070303110d030b0604060806010905060a09050906030705010f120e01050f0603010c0c111302070503070b040201082401031d120d 79
    0x8140030b0780003180c0c3c01a00b198199000515248803150001308907d480c1c9800b00800148580c0920913070341410300e0b02020b8140d008048000030700303100c10707076200200701c2c400810800501c0400319040c000301c0d2420380e0300180f404c0d00c50a142c0d8441c07440541040d890702a4070000010b041d0400a0104031504440c181d032040c84039400d0036021901c0710760001c1c2e0042400d0105000b0350340100802c41d00560305050514403a0b58a90024103e648146841c40008060708001c00643c14071a103180d40029046014109a1b820100024010500fa9802d0420061b03002254581c2d007041380e100420700149000284424901020800c8101100f03550300b90281d0710746441203404038491000c2032210b0317034042c40d480541440e6204014040341c4c10500c50708850303400c12002002420400003070510038440ea01c0c090061509000141c11024000c1c4000031203903016081842d400041144042c03141000d0030b0014084051480c0010076900d02c2290800074801c3d804605c401c4c0c1d00c1380029101c4113940e0309041c410030f1b2 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 33975454 1250 33974204 33974207
    0x2106090f140702070602070e06011b06020d0b010c020f0f06130303020a030f020a03021e03040e10030605060607030c02010c0f050613120e010e061806030a0e010c0302070201080a0e1213090b01 84
    0x4d900c1c030a020068001200501456103080c0c003607500204145440c51210800008140010100e50002c544450f8009110700c03084031940078004a03801c003400c0456407a01e190300400c5290040c140800e220b100907506038a8203075110411b46030811300c4101d46d0010f06460b0710b0084e540d1032906000380c000c50714070302108103254400117039110202e61503400f5100c8000b07601421814640380000146440c0400d04c070200719003488a020300d200704412046200201e2941c1040300c1240c0d4098211030040c041000004003081d00000c0744d848a59081c07915015401c0d1034201407007010030304a0014164010705083c021546400c200c0c0044c032500400c68200400e03107100064851303804030041c41d40440d0710400a00b03460b18008000e072201ca034240f03854100031018840042c20960086442c0780c0115034600b01d410b00c1e854244580458841c2e0781c00e00b107142000076000600340010040404100613100d84a05211200501c10440607601c1411026225100003c28001e05d120034060311400c1880c1c940d1400306503 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 33976704 1250 33975454 33975463
    0x31e011514100c02060d020f030105090612030f13090509010207030f0504080d0c020d082209020901082d0108010207021305010506090d05030c060123102106090f140702 74
    0x44000801058020031080b006440b10346860f142a80c0c000c005000c40e070b4120100d030000b0940700310745440e06580c0e036041404000303048002400d803d008441e000021040138000008a807078080124034041d445640d4015085507241c10b5401c0300f040e9500742000c0c48810b500540240103064800e49900d8420041d02d0000c40e0300b4095071060070002d500c0040c00c40581e600610b480c5595500140c1588050800b0b41c40f1074001d90310600d4207080a22162030070880c00000d0000a01c05080b141d0020751034560b62800007440c0c0080039100401001111100140c000d1107070f40d42142c510703041400910b0703569403045414006e402240b0164001d412421000f5600c0d8600d00c02d450580d00014156810100400203200c80560b000303000701d9882c4010010594200070422015008012000350b05d03411a024804d81d10b1514901d01800307001d0001800010141a0070842c103d507502100d0200905859444410a028080c2941700c07119940c82c1c58a40b03100da031300c40d4001d840852819a9058007644425004a81e10b = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 33977954 1250 33976704 33976739
    0xd0801080606041407030b010507060c0903020a09090b0f1e0103050102040501090e06090c0a0512011401090e060102060403030b0a0504050103080d0e0a050d0e010e060c0105070f05090f060702031e0115 88
    0xf131121a0000500f424084e50100f07910020615005041c24200d82c0c5031812600701a038000081510841c040085203800c1c107050000e03050455082c440b04400742d40d00e5505200250150400504080029130b550341910280460a5000ca07411210b6582d64280ba074002d6101c0d00035240007500311174010031115500d1030501c0c003990000c4d1406119a551703134140792094021000310310070000c5c00c21280c50f0a0140190540c060544400e0741c0f81565403810025108800b192310960110039083c00300703c0da80e81c01190301544a9018240420b131810003c000408071082c0b074126075401490040040140007000c0080e04010500a900300181001c0c0075001d03645000681005156038004c9a980c0b00c410300c140002e6580400c18180130b40d81d0182400000d40e640c00855681c59580e54030b07010051138540c40241e440c100441410a180340802130300c041054a07000d400741f140030300400900340046440c100f290186002074141c8550050b61003003c024060113481e030807002503001ca00303c04501e800000141002 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 33979204 1250 33977954 33977981
    0x80726061c02010905060f04030203060f091501051f02071d04060b010c0b190f0c1d0f060f0c2803020705060405061606090506090a06050115200106080d080108060604 73
    0x1914038007001c011b400e03400720341c7e001c000c49814080000140c5003000724074010a10003003070440f14a0421060b03494480300543c140d0000314002c004011586170301e018480340542102c40340f8040311186030284d240c484030b03a1090320a88020345103101520401c2c000c80b409248944401d100d1503400000442e0008820407014011620040120b81c1444440c10301080359103082d54045030200e07042d00c4c12001c0b01c5030000032001003800c20580640303d000511175208204400c40704084488407a030b006c5041c0c3d000b41d5001080c20400007801c070706041000c1112107040300002c1040c0c1c141c1042520011458036080c00110050b1095030740100c0c007441c21000f076605450024041c00d08011000c460402c101c29000420b651072603a940c10800860820311000303100328405ea00501d800c400618141040300c0050f4000d001c400810010b2000351036104090702c0707501d080d0f0901440040d002003155030040180c1d6003e4a4603200314045130140c3ca80201c01e05040b18101401d65039140e40b818107100c20344841d80041c1c40c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 33980454 1250 33979204 33979217
    0x1060302010224012610020901110109110409020609100e130204081c0e031e0c030601030506041412030a05040606090e0a060f0207150204050306130c06080726061c0201 74
    0x4418021142290303182003844d12054661440030785c50a00340703a203100c0f045044640000b40388140e56000a0512a144a8400200001c40703035a218140c07082c1c17080b49074502c91500d9542071419592a00240c03003000f4001420504481038022000d01780c00c000800e80380c00340c20500c0201c0c661880c24405d0302d04442e000c1d006010482c03000b04003803040e051041c42d03200500c444d1001d0304900b5182008140b414404100f084003450840f01413862400c000b0b827401622980c04080107100103480481c0558000740c0c0881704031220810025001d06040802010840741040441040300d0110350303400c054001d40c00f0340010880c0940796024001071f120040b084c49000e80c000803558000503060703400b2413003402414400500f0040c0710340e20400088401801c0d1881c0603000b003000d20803840c00b4001240c001c66061105404c0310010703a600000703009903206000512044c1800a01900d004a610034a80c102c0071002c00013440d88441500440e11064600900072132159141c0801141141e09440c2150340586031078 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 33981704 1250 33980454 33980459
    0x408061302011101021207020c19090f020c0604050c0913050c0108070e0607030c05100c080c03090705120d0305010621050c0903010603030f080708011503090218090106030201022401 80
    0x2003821249000481c108012621440c508000a1010f054240d680c5980908181040e00c0c00030324203282142018811801e108541d402500c4020760101103d1000c44007003060508085001f0080c05a002c40c3d0b079160142e00c04010400030040f80c04000880102c4401860b03840d03d0b110300413108030380d0f000140640e110481136980c0b5030040611a600c41d80034545080f070302250002081c0207800407803084011a1030b1001c00002c008051043c100303030f40300801040000303004100c4028180200900213800080c0c000020529100c024481a000741c07602814003240c09000300040d0384ea4820782c04541c80000d183c00004103074a4420412070880c0d081c6201020141e08140d510900100009002c1f402c8aa8041040d550a51400c1c011040158003980b10301c000300007103003000b4000803002000d0f00c0400482c203006000c044010300d9049800031480c030b40082c00f87c81034400306410201040b104001c0c1459103040040d848015000702066a00c03ea01760f801a02c9e00482803c404500c50b40348000d121910f0006 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 33982954 1250 33981704 33981721
    0xa1406010f090509070801061706180c010c060f050c041e0b0a050d060e090f071e090504020607060614040f09020901120507030606030503040603050601020a1101080705120a050417040806 82
    0x4c0e00685030a05468100d6a11b072403040c21243e450307012000442c01d46644665a43c4140700e180d0740850030a8150036492014400c1d0b80d1a640c0298a03141413101c0c590666040c8100c43e80f10b80500554998104064100007586030201e401610500c0300901c044d843c070faa80b40c203030410382208442c1c0d54902b40c0d0130a10f008805682c140c102014103541555581c10002e0520001d07884070b80100b69070809400f58001034074546042c0013281e00314189180303861844001c580c2c1920702000840e1906a00021642c075903100084240c42400800b03031915082400100301d610220004071030f01c4d5011101003102d5119000c6100590344140006580000c10800400203084501c1c200c0c0002440703034060b03a8240340c90f6981c2c5412214250000e448607440401c0500c00950103108040d00401d0900040c03041c0c100c150340e09400b0001d03030034080c0d04101641020906282c0200291015142510100d01c0c4524040b20b40000601c001c8909842d9424002c04004510051300d00312410f07144010081c0c51281c0e50400d0 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 33984204 1250 33982954 33982961
    0x9030207050f030c0402160c17120a030e0a060b0f0301140103060504030c14070801140f16050d0603050309090f040f0305071502030a0b03070501112d0303090a1406010f09 75
    0x2c0c29405001c2e0141d0050180d54a00c007c141080662070120845004e07801c142041103125041081411008a10b031703004414002401d054a10400d01c44960b075109444045004c0c1920a90300c903418402e5480a40410000340c001d40342036041500d81011a000510400d800d0307a020f000d5002a8203060001440031400a0700900c1d8000d0103130400c0f02002885945c1d43c000c02082d0901603020b50405903061001040a0041005950344440b0355415800c01c01200076003064094882002c1c103156030012200c0c0e0b405001940d801c8200d1980c1080a44e603642040d540320b500515100348508200e50005010360406001203024503000040540400740030b42d0261081c0e0302044050380d0352011844444503220701400114807a901c07001d408901c0100c040c06240c50b142c1c041c0c100ca03040c810314020701107a00600080000c4408640c01c8083c440f00721281117080320794441c03e820340c11030100004025220f54002140c3d0f9110b8410360031020010030302e408003511854203008a68034031000725820084038002d5003 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 33985454 1250 33984204 33984229
    0x60703030b150403200904030e06090406080610030506010e01150804050309130c020c030109021e010e03070b0a02060108010606080123030d0905030c0d0b0403210f060314010903020705 81
    0x2044030401030011107440381d143d000f03035004440141070028204e14003000400520500d2000742c4a0320079909003a0703400351400c16040c0c8150f01901000c070301003050740d0310754000c43c1c014004503080d10759604100c40d840c01018250b002c00d4820b0701c1100c00000308610940c00c0d1034102c03040c44814001c006040c1800301c03660074018009984510062200e8004c0c3c0e9900d440c100f60b0500119000560540c6002002e41080700c41c0c12018843d900d03100d0348501607100c1040e00400a49a58842102da1074003c00583d84a044505080c0d003512600d200800c03402e2244000388000c0046400701d54440e84d0301d0400c0e03401d0303a90768003038180060000c2004000e040c5028076804039900c801350084020b112410042840c0035a400c405000140f0034910407c41410103000b0b119100c001512000151111516846040140a0300042c100200303044110456298808402101101c1070028004072110302d502d60040c0c0001e0100b0b480d00544c0801040244070140300d00c0300c0581e8136402608025280c4010000d0081035038 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 33986704 1250 33985454 33985459
    0x60406051c0c0201061410120e0109080d02030103050606060304030906030216080c0d080705040e010e09010b030a060507141804051012062403080d091b081e0c060703030b 75
    0x341c0c18890720007014054100142c01e1a4000200c0900c1e100f48511103055048009000d0382c0000340c0715010b90f03480402450310819140300400d414044802103401803014050181c40717030201140040c0454071580086040b6400703034003118210348903241040810b100541d4001c001c584080c3d0300304882802038024240c4004982c0c480c10046d8810780b19400642e0060411031841d8001c0d01c502c03074040e60880c00040d000030261038194106400c0c030042c030443d0807040c0560644140f9030400200348400942040081d100060203882e61114a8a41180900030170341e20340010039460b1900150058100f000c2d03600740400100c030748c000751000c5424400185030160441000c09940c0030701003055170f1955501901d5074825000090030908030281030f10840710140c1c03400b044201843c020070100e010f00c815140800c0e18100005010007840c80c05590180c0300003a1106240b00440000510080202c0c00d480260900071070042d900040c60a00c90711429802200b0303030302080038050840424807a0740400c0307100750003 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 33987954 1250 33986704 33986737
    0x605090c06040605030906070203030105030312040204020f0f030403030b031504061e061514040b070b0c0d0f020403020909010c0f0e01020708061015050405010203030a0906090c030501020a18030206040605 90
    0x42800310307005521907049500450350000c140300c030380c000030002154402c9039031014608650514000076100d215112826810a4415000c5401c0d562194112a00041c400401ca80d480402c0040300d40b054000711002c0d00070901e026494403081c1004203180f801d101201c043c02c1c41550311075561400034500b0201c06502403601c0c5106084080c0395101d5000680f11401e0301d4500504440402044c01c1010443c1b2992014140010001c1d0503220b010f640b401c0d0b610264020079661042208a4107018040688009034106042c655840c40945e0003001502d001341e03030000c550341d88c5880b980d0070b1b81c00c1c105401001504d24402094002d2250103043c004071014410b445030346a1720041c0920704070303003640c0f00c01c03030110040d40402820100076000e100011180c00d020342031a07e0800007030b4890000804a01146848090400c10082164080d6151650024007040d11640709c0c00d00c18000e4100b1461a00852080650405a400a01c0d00d26081340d500070702040c034007400c00b10220b0b07007600140f0320f003040e4652 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 33989204 1250 33987954 33987973
    0x10020a0e1e030a030207210209040809010c0503210105041515020109020405010815090a11010c0606090504030305040b100806041104090c080a060516020604120e030d090f090506030604060509 84
    0x302800003000f014000e41c020030100c0d0a11019000b052240104849115410040d40005840d910840c2c0e03032068000c11101d4842d8802001a1101000001c0040c01404001401c048046070300b11808512070500b040f040d4241c0e00c4a0600003290700701c1e960b0019411040408210f401d0705078110203511a0340c2d100106880c521640814103440080e000300d1341d1034010271518108800c00180b601d07848070202c001008406119101e0b080748403416140c0c0c0307041081c90160031090240700e0f000784006000300d03041000300385040d042c0100100070994040320b640c1400000f28450a0709001c14a0030703503900402400117604c0d40e6980145050480101941003a15410880007285100703011000904465018000500c901e103001d0080707402c0144075941201160302a0030601d40e0004515038001e5102c3c81c2600442d02440c0c081c0d40a030303240d0b20003c1c4c0c1445076018001d55a41d00a030190201d40c078001701c0c0445241c40e40740c07440c1502c004a030900c1e09684420300003404035003150013085d0801d24140c1600c62400 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 33990454 1250 33989204 33989209
    0x105090d0204180503030405010b01050a050a030e0a080c03030601020f0d0e09040f081b0d0302070f0803040c030606320904030c0c05090a020304030806090903040909060b130b0310020a0e1e 83
    0x3002001607426800100411023885003c1c0100d425070301003464181d1034a0701030300c1d0140103401030340340c0d0904042c2c1d160f2007190540e8041110986580c0c10141032a2517042a550565507540102c0c2d0050050080300707003080c03880e20700003801b052260043d04e485585040c203400303100004000900903180542d0321b030040c00101d15010000c2080c03012920340072444002c0d62071558035000b1089585c3d0209481000b0b410003050001d020800c0b0305a00410b09666601caa0030000103604180d003001e000e00c1d241c05000178040b030b800724070b80c030301c1030810b041410b49a410b50264400803d600c10003290010031940004000074465001550700610a001c5031075000c0d01c1c0c20108902400c00c0f104034039400e0340041807005242c0c2002a191303210b541122044128985403070303040c1e1a4000e910034503a0440d10b4907100001c002c8541c01070300c9200c40180c240c1c403c00707103010a460040c1a03a01c030640c0c024041c1b890481940c040c14003c4071140c21042d111810925405e60070300110075508000c07170818100052902c855507 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 33991704 1250 33990454 33990491
    0x1c0c1401060305150c19120641090408040801060803030a06120201020a150b090f180304060804020f0a0302030a0303050406060503070303081302010207120b0114010e0105090d0204 79
    0x8400400018001d425441e08038074002c40d031064440390340075130002c21800301c513180110744081640030165011009641e9096508500004405514500384840440c191243e14400f41c40020884403002648207450410741300d0000301d12250001070b81480655800d402c0403120590072a1244495900c1c00d07a681a0f2542141d1040d000341405400000501542109500400c4080d2030300134000b80710a14181d00207540c407407584500810465040f401c1c4602c1d51034550102109a60180034452103280041c0e101a20640488205003600d01d030703400810440381e00006a600762011912018110b8980ea02080008007190380b441b03912035210b140200050b2024044000b095100380c90104a50074945000d00982c1d026404c640c0c02648151400c002096110030740d550001c4811142c03c14080035400100d050104d1074000003100070b284e05001d0104044120707031a0403184150030404a1004410046461030040e0100c00c1c005042031284c40d00c0c5280400000c022948024000a148030060f107030308000 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 33992811 1107 33991704 33991733
    0x609010f0e0a0305030c060f0610050c010204030606080303070e040b0109060302180603090d020c040912120f150314030f0712020a080d020a020c0f031c0c 68
    0x400e8000c4810407a40400540820700d090f0322810400d95a61200620007100e214400000760282c40c040c00080c05018020136580c202c1d203290030100e4058001400c1c602a6540c05c0000000190b400e109200041044d81d0146443c1d14016101819029000035240e000d142480c07009822680d0080401003034400600740141c6902458100d41e400d09110b004144d00101d000007401800d141c00540c4074000f8445138201c440080179101408103a03040c1c010028101241001c840c120b43d401080300004100041e207000038142c40350b10124040d600c45003011001d60218200c203100307105a20240420780100a002185082c40c000303c1030107948114100900085400380c3c0c4240c1c00c900c2030201c0310159420265240c0c480842403109c034000e50146010314054459101c81d0445402c0c02000318142ea00000c010b403410412503c44907009400226030001044011110b120000b03800f029070060 = true := by decide +kernel

theorem cover : BRFrame.Cov 33812954 33992811 := by
  have h0 := BRFrame.cov_init 33812954
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33812954 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33812954 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33812954 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33812954 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33812954 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33812954 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33812954 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33812954 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33812954 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33812954 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33812954 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33812954 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33812954 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33812954 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33812954 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33812954 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33812954 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33812954 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33812954 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33812954 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33812954 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33812954 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33812954 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33812954 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33812954 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33812954 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33812954 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33812954 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33812954 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33812954 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33812954 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33812954 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33812954 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33812954 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33812954 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33812954 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33812954 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33812954 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33812954 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33812954 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33812954 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33812954 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33812954 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33812954 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33812954 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33812954 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33812954 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33812954 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33812954 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33812954 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33812954 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33812954 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33812954 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33812954 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33812954 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33812954 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33812954 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33812954 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33812954 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33812954 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33812954 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33812954 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33812954 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33812954 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33812954 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33812954 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33812954 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33812954 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33812954 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33812954 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33812954 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33812954 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33812954 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33812954 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33812954 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33812954 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33812954 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33812954 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33812954 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33812954 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33812954 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33812954 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33812954 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33812954 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33812954 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33812954 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33812954 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33812954 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33812954 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33812954 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33812954 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33812954 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33812954 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33812954 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33812954 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33812954 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33812954 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33812954 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33812954 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33812954 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33812954 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33812954 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33812954 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33812954 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33812954 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33812954 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33812954 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33812954 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33812954 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33812954 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33812954 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33812954 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33812954 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33812954 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33812954 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33812954 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33812954 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33812954 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33812954 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33812954 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33812954 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33812954 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33812954 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33812954 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33812954 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33812954 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33812954 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33812954 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33812954 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33812954 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33812954 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33812954 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33812954 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33812954 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33812954 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33812954 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33812954 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33812954 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33812954 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33812954 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33812954 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33812954 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33812954 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33812954 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 33812954 ≤ n) (h2 : n < 33992811) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
