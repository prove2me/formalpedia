-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0831
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T23:02:38.364981+00:00
-- url     : https://prove2.me/submissions/bc18e543-f4bc-41f3-8f93-3be730f54bbe

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 149280575 ≤ n < 149460431 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 149281825 1250 149280575 149280577
    0x60e16110d020a15090f0f030f0201050c0a0c050c060a18150c0303230123010c020a0e060d080f04050103050a020c0c01080718170f0a0b070305071b0c0602010b0303 72
    0x444141c010382041c441540d01c1d459411305040c03208130080c0e992002200407500c621101d5540700d10802c0c0d240c04d001964140a040c10300071520075401c580c180010001c0b0000c01100b5501e102881d820400111202460f00b54100000390095542150b40410041000c0398008030000c1d001c6a90401130810700d450b40c43c4448000c986400710008603c50341c4113030002a01c280e005804582d5900000c3d110a80000c500c98415070007a4010712008030b207070741c00302d01d40c2040b145501c0c4045824201203a000110b580403505850380f81c86a28404000440010041c1d00d40c90521b00402d544280d4440d541d01080c01e100040d43c016001e00345c0003c0c0380c400051203400300d9200300c40d242c4e050a0003c203502d90300c0e00011038188030700a19440400c001d443c0f0702c1640518a180d4800a80f400401c12002055076006061070700c0c02c0c1c50100e040300d03403141c101b20001c2401000c83e203130451868a404901c9944850050358500c14070b44a502d40002c51000640c1804000064641075840c0c540c000c1c800f000e0540201592 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 149283075 1250 149281825 149281843
    0x60a180e0102030a15061e0507080f07051f09050601030f060e0601120c05010c02010522050d030509120d140d0207020a060c0c05041b030506190e010e0f040c09020d060e1611 76
    0x6200384100350540300b07501903006000c0c0c503440364510520b015002f1942c11160742004504503043d0303029210b152500e010800d8190101100303148204819200d81d200c05030340e20418070000d40300c0c01d114080e00c0144440c80c0c00850544400314103d443c0e03940d4980c0b40c1d45640c548800140d132808443d0b2404143c43d0311624000d90b00d180c05030341e518108a0214180d0317010407060030711540340a444010026040d110110340107030613800385c0c4680d5124403c90050181c016800d40c2644800c0c1c000d181c410035140d4104000d0140c4500c4004c01c241c94680c2640b2038402803060318006584400c170410000760a9a010700005c0800f40704040b140111340c0d68209100640d55070011191039061222340711862188254001540540b0040c688e0007904008007050030841c24035040071208141d0b41005010220301484407940100034141b4640d0f2170310705a21008010f5446000b071f00307070460300041c407191818a5608076101601c0030502c11131107410642506106240601551008940c0c98189d140005c82c001c596221 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 149284325 1250 149283075 149283107
    0x2120306130b01030b03060109020d050109020f0a050714100516021b10021501030602030610080f0103060b030a151a04021201090506061b010221060a180e0102030a1506 74
    0x15541644101c010058022010801d040583d581d05842d416501008501d00900e60440010713510b01a00e4409819164145c0140d0400e82c0104014400e00710801c5c1151141107661074800d898444600e0450501360041d4841c204605c41d40391912105801980a140945510803940d08401a40c00082c0d07158000c00c0c030514a00c018041592015003003039520100d0001091040d11560803881d614001120030a2b00151807055003c0200034143c282000d103030074084611308200083d8079050404806d0310f841400002c24650b1150701015081c0c5041200303000090b44480c0e00038a44811150f600010004c1100c0c500c100604a80c0204160520744220f4404070602582241c4036070038107112002606010381038607080601040062203442c1003001800345c03591803000159a40d1028041d0282c000c108c2d110004c030542d9944e060001c0d550b41e59020404540b1620075040642d030760807400303c004150042c6891030315400042085481c144690001c80100481114009025101c4404a8140c1c4010b41c1c0d1030 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 149285575 1250 149284325 149284339
    0xf06100206070e01031505030313030512070b16031b020f0c0a0803041a09060705010b040c08090a03030b010315060c02120d080708060303040302060d05040c051203071704050a080d02120306 83
    0x143d0341e54400e420420030801880c01e01303d000d66503000801c0c556440030729280f42d800c4c080030701030081080600c0000104035003014803a041c00e44540341d40340216005007540c085039286d00c140c610b2441c000d410191050440071084c0440500000700a9190700d04040b081e038141c080d0100400d05031400c134a0802c29207410708020b5041904140c503c200c0c58807104e030403d00301141400710381e2065031004014425248030310004a1002004003d000030354140840c0e103824003010f801000710304c42c0c4c00140f07045001c7e00b6140125400d400e030700c01030340102004502621403103800000861050303040b2148400840c4203540359110b009008000c9a201e22008103c0e10008110002140c02c1c180710300501c903007009000b000d0b40e2505a49031300190583d0300211034050303509d883d41c080109010341c250b040002000701365104941e000c02c820a058481c82010f200401d450300301150034425102c807105440140a028140802603500d0340d00c8507a03500b10106c814001803080039001407000d1684401d50b809000d01410031 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 149286825 1250 149285575 149285597
    0x301091b020118260a020703060c03180609030905040218030f0303040c05010f1e030e060601110705040c11060a1b091a0a030f050c0a0e1e060c030d050f0610020607 72
    0x81302c0c031000b14080e541c8a0012080d910260400400501a04840c0d0f00140401891403401c0c0c0150390b0907150002c00e1525280b0040802030005a000c8101a40700c50000f0780000c451506a0b500d0480340c0080ba045031000c641022400c00d0303a240400104011001ca42081e42c050342c200d42d4911080b01c0091040300144420805540a02805440c4400780d06000d42460071900300325030755008001710000041d464040c1c04c0000c0b0010701540c0d403c10000e10f417182e514290752522950f0355846104813130241d82e81d18041903019204054106400c0001d2090301c0c5107003030500d001005000780903445074000060b10a2015041c0c010300c94101194842580d80e111a40105030b2104540c0040b02007106264454588240301d4140c1c0c81010711400140a07403540711203803071100404124000c40181e00079600785c1070350395074a80c10000c0a904540c046582c203549410b151045030440c0210a800800310341070005110b4000d50041c100c6104050a42d140c412240c40344500300d035030750800d49480012034800040 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 149288075 1250 149286825 149286833
    0x40e04030207180213151d03010207020d050604030306050a030b0415020f1b0d050406050306040902030c0d0606030215090f01030b27010302040c03110d0c0201110301091b020118 78
    0x50a510900a005a841d400e5407a8015000c0d6a01c110000410384e90004903410f50001c0c00f0041000b521b540c051401004e03100d024046d110381044008100501f00c1c01c418940385a50940403a50540d50140810a85641d5860314640d03810094a084011a04120001c2000c3c20b06940f10703c212500b0400c03038501074a175a00e070000001d80d1031445510b0b05408024100010b02c04100414840720628001d0603c074200c2c031161030902801c0b420003402c2010800040020aa0240c2a0380c2c000c40c0481d000a091190741c80040d180c181d00f00310080d08058450b800e8424440d440d4403600480f070003030b2002c0000c0078408030450036a04c0351402250f0300906410343c028140d480f0742d020091290001e4004041c1d080d41041c099101c5c074414054410307110707803000107004504003070140b003022104a003030610280e426880b41a480c1e004c1c0050100380b50740d652000b401498401d4105106a01888810740c0d0703203584805075030000d45001d140d260141100b4000a5615034414441c88441903103d407a1000c0070350881c0d403 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 149289325 1250 149288075 149288099
    0xd0206070308060a0b0f07063803030403210306080c10180e150301180b010e0c1e041d06010504090921020a030801060e03100207140a110a0b040b04 65
    0x1240b0b03a0044132800c2d01040000242006007201c801950211303440d070309286408411795000c44d81c3c2070243c2130600600740e0b610b8204207410301c01c11051400f1464034000350340480c0c41d502665102410071040106d0b2014948010480304008440c29503051010640340e000c3c10b0359800e02c00500540050703000404611b801e22420505500c0e05016000000487c6d5a2404642000b41502c0c12003030842100302003485c600d002d00c1040c10305a8052800180c0b103c46464118006105104452108440000040d04c2d407101034107e0301c5842030504a010b0701c000171044450b8503009400781040443d03080c2c040c00c0800b02d048015038481d140c1656980d1a160030618140054944403c1c111003100c1c40c0c500c4480140d444280b4580c01e0401580146004021424002d20300d15044e4403480520011101c40c800644001c561039011481171ba4002d0baa42d252841e20b80ca01d45d40c1000b0880e01400b42d4000502040325000041c60040c03c101c40210000d038445603c0b0629204a202d071f0001c07440100401c100b40000c400c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 149290575 1250 149289325 149289331
    0x418120903082b0f02090f0108010b0304020d021201090528120e130f0b090f07080408180301050f040507140306040f03050c070f050a06050a050d090519140c0d0206070308 75
    0xb841c0032200f40000841010354425070025910b154010030004c0003420022400500c10109183c03483c00c80d450200e01d9442440f01a1020b4040c070580e802400942d101c03601c3c0300c950340841200803c401d000c0e82c01c0040d00c548010842c4159070308402110b0f20740c407400c83d001052582c0c00000d0a120180158400d98070300c0481000c041d00711801c41080f0022040d50301c20844003411001c00401c2c00f40c029000c202e914035000b04030b8074007114082e00f0b0013603031580040800d41c03103903211810a075101c00420102813140c49510b40f2950542c203020400c2a0303507000b280c1d007501942c8a882200c00d440d80720281c134850401c0e8920b81a030180e11540003d80810024080d0105c01c500074280700345820b0740480074134101003442d0480d030b800c0381e903406d000c00c01781c280004540014001490032500f4504035440041243c800c819200319074946400c3c2c2001403000a01a192218066008018040c1c00c2da18110b07842d02c40803105c0f48814020200c0c0300f4a10f003040c110059003940c0c000d05c40c1d850f0032031a64090390341d10b8000e = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 149291825 1250 149290575 149290627
    0x303120c052a01110306090105031204031203060e13050c090121140607050a2a02010804111f110f0307080309070e04060f05060d02061b010902041812090308 69
    0x144036049800a205001000003184c1c03c25960b480c1c48028881e80e0350040c0d1007180030340d2000c1f00605125a00347d055505595010700b155056240c4c1c0041140030b0f00e199005058408503080030b200c3d0132045141c0302d07035000b0711410560b00107808a104200c2001000d1207864601810b4103180d007181c0c00b129460803403551251040c00d84c0003540c420000d241002c11501003010803000160f10303800d079400c90016010103100150684d0b61118030406524400d01400c0002c0c1400309050100702000382e800c1c4080140400680540c40415200b0200d6a44204840e122404903414128103101c102012501c5500160342070011450001c49644070030440c1d0000300003010301d010b03035040491a01d18108043c3d0250703004003030121f601410f01c2c000008950b00548800e100d0a9080b407650010f03241e079001c0d80e60381c0301c1e40c101e89810f400c280c0c080c01e03000d000c0150300258030604e4207012920405a42c014080d10034010000030035a044541401d407415811400081c050310b1080c4001080050311840584281d602 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 149293075 1250 149291825 149291887
    0xf0504050c12010f0c0f0207080a050c010c020102010b04150f05040e060c0c072c090c0102070314010216080301090c0203030f0f1305061006030c09050d0b04020607020d0501060303120c05 82
    0x200d401301100f141c4a2080d00000122600c00c2d8005440d8101f210304d020f40101801b40c040c84120341c0c0c4080e5104800204541845802b90b40c038425603000394000c192220005c1c00a100010104502545e520303064020f400100010302c0c808110fa0420340302e0b80c200e03011290000d000c181ca5001c400e0582d030b000003106003400d1003101b0300450440c280c4400f0030300c00b0b111a480c006141c3d0305800412604c41d80209600520b500200400402d03070f9000407000c2c01c4a82199103800c581024070310310b601a100380404100e0707480c0310420742001c1101100045040b19a5900c0800c940d00d404042280c881c07106440070001602c10f040418144603c140324030b43c000c10041440c5160a10903643c450900c841102c00c050700001503102001000d40500894a8119041ca004d07402d10341060300060030741c00e40322400307403984880500103011521104101c91489070010300c140c004205525240e400380c003850008038005002989181d01d84980f5000f00409000320340c45060030034019550650b101c000c502503035502004 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 149294325 1250 149293075 149293091
    0x1120c031403120c07020d0210020106090c0207080d0e030a030e04060e0703020d1a01140f0405030105100f0603020306010c0f05100c03090b1b0301030803070302040801110403060f0504050c1201 85
    0x194128034014074600c0c01c0050750300c4402000510380e200c0c4000f0201c800c0c1c1d6000704000001692403c0e0300d142e90381c2d41120303150f0090291141c12401094243c1003688002c1c609131740e4100b2160002030301001c481ca11405c0b1050111448c4040791506603680170950164444040d4200182c020b03e80d8400240c2c010b00300081c0c45644040da8071500c00142c50040100ea40001c40640300f418074041c2c0c0c1e0f68840d444003441040e400400000b0700500c1950710141c4685404600000004d076600c08603001440c00600a00041c1444004122900214031840c0031050369141d0015010380039001ba00c2c8a003105031910902c0103a1625801207034200032000b2a19070207280d03c1514991a036200c0c070103011045590010343c1d100286001c5044180c054115600c1790040107032559014074410031a03056a0340300060a0b00d82d00c500b00d0aa010740180c3e001407090754204400900d8500b21603016200f22406400244101152103000e0821030302c1c02e5030054060b41244818046900700400241c00394002e010000072200 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 149295575 1250 149294325 149294333
    0x16060503190207020319020906042009040209300d02030d0c05120a02040f05030606031207140601080307030305011e090c0e210c010f021b22050708090a0b01120c03 72
    0x100d81c803c440c8000800d5021b4030425420841c410079807141c800d0700c080280080e40c42c00043c428001c500981c00b6890300041040c2a07807255015140d20980180610141004101d444000700c43c041100e003d0b144801913540c2004c01001aa019100d0060340140d881c0015010003000906207030a14801882020064010700c09044c1d090184507056800006882da0300b0240d425140000c0c644c4500d1080c0d124600b4009070f81c0c1e02081c5048034803c9490802c1c1d171030403107151621039000001424030140c00360a00020359541c0100c002c1c20700324031036941009030b6070300c030101c2018540241c00500da00b100d1001041c03103490743c03d61051005a0301c9080c0f802034241c5c404005032121110700c1d0359a071a0104103401c184000130030000a040c03e48242010718100d074410400139031762385c414405d624040156811001e05904c8041c6130050107010300f1184249115200340103009448180d44010019460300002104c816020456583c0300d58042c188640692800c030281c5540380c02c82c2c00c140e40207048204004001 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 149296825 1250 149295575 149295583
    0x20f0a03150501060201180512070f05030403050c010e0a03050309120106050303041e09020a121503080a08090f030f0a030b0f03150702010501060323040501090c08010905160605031902070203 84
    0x41040d07050108296050040003030039525050310a180c04082c2c201040700040001c20031b04010100601d1640e02c2d01480d0030003692000e003400000c0c0840c040000c02009000002c9030741703003034070b46d0a0722610b00b020fa540d818000c819080b440050407603003044c00101500c2c941803000c070065629107000030407017075101c90000341151711a0b03111040c103229425019010400210801004100b8031008504120310b82c13201401441c100c1600300d10f1180c0d60301f0410b80761880c44264001450304464003a48a920025011749105026204140349200390a140c0c1c4604400104840c040200d55104500b00300400f02c00368058203c0760300341039000c6000c00207090a600c041290045001740d05604002a04048101a0031035034103030080c2c82014240756a20b1300c60070b40111200140c00710451084503958450a02c50f00601c8050300041c4107405100e00091802415040307005414001d806440804ea4080d0348220020418803410020480500c001880500000d04420000a90348005464003280b54002820 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 149298075 1250 149296825 149296853
    0x1a0a1416050106180e030313080f1903090b13050c040f060315061e06201014010f060305040c06030c020709090b0a0606030e0721080418180b04020f0a03 67
    0x3409085682581212149005c0c2810a243d540081d6107181014060900c00c8454004054021000080d8210229900e0320807100700490000d6507030541903802000401400941c1d90584405070390030b01090440c3c82d000b030000b070300c190710000510700d1020b480d003400060180714a545c1d040542d074080000118034601e520705e40e41c0c000000001045400d05200d0002202c08502e0a0700d021440c2d0f80c240030a03900300903161540e5403000498006404881d814901c1c1c04456900300301035a051100d41c01345844600304481c161004e01030010a00341d00d4010440840303900300d4000c2c10100190381c007086098000d605c510058185403055800b03607921303074106600359403002c04101c1e401000c1000700080d102c0715208030341c0581010300d000c3c0800110180c80580e10403590113149204110b50a005241d1000c2850040c68a03501548a5407256071b0749514418441547c42e002c02c07000e040031496420818914000410030764010f5103e0303050703165502405040d024209043d500105c200b14040003081c040108010 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 149299325 1250 149298075 149298089
    0xc06010305010b0405011d040b270d11030a0503060405040512070c0302010e0901050d060c030609060608012303060f04020102101a030c0306012706050a0e011a0a1416050106 76
    0x29603c6220018401140c01c1644410316400e1010011400040400c44a54106402c191005180d86444120ba400c80381803041340748520400f00c00d417205680700458801850303d1645c480038a501010b03900e441e180e10502900f00001078003000000c202d0318155000c150401d00601c12249614604d00040c179482d80a0b172005d481003034048070b08200b1503a0084000d0a0200b00740c0309090903500d00404103200d242840001802a51510350422610344241d0084000b00040c0c80d080c45030b141e482c00094160314082c09426811038042030228055070344116103040900e03000d40104402d0b52405801c0c40d907814050001c03030450003101c2d000810300c4e0550082c0c0310402180700610b9211008141010300c0d024a01c1c44890207500100700400120284030200c4000c48210542454a10360000318140203080a40040354040c1d96101c0103e40b03101d1031250b03117058880600c18200300303e40120030941c0500902c3d503d0ae00040301c45c4422440303041c440029200100e40903200e0008801d190380c0c0d45003541d0081e00160 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 149300575 1250 149299325 149299331
    0x703140a08041d06060913020702010e060a050c011a01021c0306050604030b010e0906040302100b060403080301083313060b0a15030c0e0a120213020f031e060f090c0c0601030501 78
    0xb5610f80040362001d6080f40f0100c660a250141600c013003030a51281c0d040400791280c0c046141002e5900605560344088002441c0f00e54480f1605005031131a0000c0810010715071807c1c14607181d4a80300e01c140500e50360142c00400182026030300c0c0b0025418081d0440c010076444140000700f50301e603140508065481a04038612546c14070114080c1c0c1300000701000080c0d03000c1e00c1800040380d000724103e4503c0040e880c000c01c44c9800c2c9404100300e486603910007440c0050000000030852400f140b03103d450100c0071441e4548000181c26100b64a01310242c41e80905191808218590b502c02e112443c1d0f98456807000c114040c0100c0010b2010443c1e900640d60101c01241c48490305a140c4900924041c20f400c0c00459480131340081141c0c0d1a40d405100e06545982071440c0640d956042860600061400f00b90f6481c40a25000e10103900181d070a00c0c1440d03908a541c90f030801c0416000e0344502006000010703040354002c2049002c40e00170302a007010708001c01040e488003406115440c00303580108008 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 149301825 1250 149300575 149300609
    0x1e050703030b0306070905041a0d080306031c0215060d080c060103020913080d020a0203070b040302070501080714030a110f04060315050904150509070e04030e0109170703140a0804 79
    0x54142c0710750440580c440e40083c0708002119030021046810f4803015070340018020034030454118240c00c000700c51580580041c03100c10030030100b10300651040348140d0542d12450025022000c4803070030f4080100158005001a005160714910269482103006000309404011605e64150302d074816400300b00140c028400500960420b80800d50b044403407001c2d01d1a07014080c0c0c5580c215405a124814400c6170001807003042e9030310810503100d155401032000f114a0803d441d020350b071049a44a1a404281300c0000508614003074a08003c18028a10907030b0302c0d40d81d80c04030640041c511400380d40e1900c00e0500240b07200d03200c1680035101421310340e2400502e00070b000c041501e011200c3c0c2d01042c0308480030b81c1000002603d60040c40d00340010031308041480c0e02c4d20300c1240d0400c0c000350070540494910b4070401061561042c60505e54038401c4e00c8031301c407440e182c200c00001d1880b220b110840d1039004510810005420144030207049407030300c1c140e8200a1040d41c80d00e0055125034855982c4800406070 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 149303075 1250 149301825 149301827
    0xc0604060b01050301151103040302150403060b0418030309051204080f0105310c03021806011e0e12031c050405070e0106020c01050f0c01140a0e0105010e060d031e050703 75
    0x82024900c02420f000b41507616002c001c511121482991904000d00110101000c0307004000303032400b03180e000f0158190014441d00380c01c200d400512054880500300035000d81d0a0826220300d1010004000e01d00c2d040c24080e890507405400762141c03c07995489947d41603c030047d4000081c1010300340c031601400f5407140007401603081d10f0020f04804021a413840e07001401e242d07520059181c861003000c0d500350401190a0200820b841070740080e4000200440d8140364142a09110741324200980381e142004180c41100700c00c0b1088481e03440081400110000114a489080d00e2140704141d4102e03032801482030f041e000303050041c107058810f4503103440c184820000300f0301c41d02010780311801c11044298900f6400964407040c40002e2818031000062022a0980030012070b2100c20115009110a4000c3e002c40095140211044d8122910705035100c48401e106008250485000340d024428503112401000345001d2907240850034800c4110390018010b072440f420b00c80d0030040d51649500e600320303420 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 149304325 1250 149303075 149303081
    0x6020f030c0a030f0c0f26130e151c0507051203030c07060209030d020a06050901060308071e0203151f0b03040f06061a0d15030203030a0e0d080c060406 67
    0x981202a50400d11903541d2038440090003901e034940502d000e800b5108146411388a001340528042c003a0750800300c804041c4071100511403403406030701da410300420440d0201e50400c2d0181d03c040350b104640000c0704214400009200a030800012020104800100000189450016001c2981d21508083e210703081c8241032103103800400e01a1001c00c804980d07040056203030710008007121203400002c00d0410501115a040e0780c41c0c2c200190845407103c0006070003a6a5021244040303c40600f0700000580c001c1c018094402280da100009c60704100543d90340050000302e42c1d86a604000c250b11012000d81d604000384075001043c4000030781c0b60300b4103040402580740074060040c8032000101041040074050400c0301c0c1d1054000c01a0141442149009806030960364003024a004280c5005002d0b2061940101078001d0175400030011810324a4101d94402d20034400039605400511001c2d411a001e604a04030040000300154038070b03c16035407440510340000c82221000c0d441881004200240c0348 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 149305575 1250 149304325 149304343
    0x60506031005060603010e070207120b1906060912080d1503050d05030609010308131a0d0f0b0102150a09050601030303020a0f1701060507030e040603060b0a0b0a08041103031e040602 80
    0x60341c20b10652400e00c0214500d0312040c410703100d107040148005101a0720074800000a020f01c24000c071420b204904095440700c2080d1151030ba29080c03584070741400d01c128460071045072415200c00415500e49212140001c41c0c217403045e1805c0008021107420040ac901c5285d002c1903024035007810703090031030800341e18105100c1044070903c00b08005010055941c10708081c1101e80c040c0d1034070707912805510014110150f5600004118000980c0f0ba588900504007403c09070700100400c02c00c16403000c201c90705550388021036902580103c0641c003610006076030b00b564807090020340400d409405548071440c01009034030603000a9030100301440308680c4014820881034040c6802c01150012500255141c20184980c209004001641104060149400c000d141074014000c010407540d82c10814050a00444c0c500c0c0300e0480044003284038a0380c042541c0c0d43c45103139030b64209103586039aa80308034460010b05659140c401072043d00304d10311303041d0350780c041a108441d1110740395031a0001c041d01c0c145240c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 149306825 1250 149305575 149305603
    0x6020a150b060d0c030e0610050f09011a0f04030f05160e09060f060a030b04150e030a020c15040504021605010f0207031409010e06030405030a0e0901030f0b0a0b04060306050603 78
    0x1090048156448000350f4a20f003003c102c0c0040c0d8044c029405400800b080c0f0301d103014034081c1c0f0040260440c040c56080080340d8041d50310300a001401000c000008c0001d018501c3c00f10050320244403980d5404018001c101b0103200300a01d05916604c50403440c0a14000444450303111282c120300403041c2030489002001849075210150819a035601c1e00c2d203100a20b00050006c401c00014101c1d503a08408070b0086401141ba100c580c10182400185a0b5412710020744040c2801100c0124110000882d09602c0056000e071000b04006010014042410300c604a1011401d1001140f180c1d104e2001340b628403044001540c084920f440c02c0c3d800e440c40c2c40e01c103500e01d61041c03204c40c010a801101000f482c0000000030ba58a441c5000103807200e144540c900d03a0060030110401041200000081070105055220001c120031040700301310140d50709000040104069850f02d800090001c501640c01c444444c0f8003107070f20401c010104003212125401130f80c55640f110103010080c103090140039955648 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 149308075 1250 149306825 149306831
    0x32e09080f030c13060509010206040f020109180b09070f0f0c0204060e092a01050403080d02040803040b0a180b1b010605030303130b0a05070512090109080d05160905011215050a06020a15 82
    0x40300e800030351150300c0180086c11400903440cc00e811684200d02e010050403074139210038441c2c40803005040050000100c1c007802000702c00e000c40c030308034000c200d50211000c2c070741d131182c0150343c01d0794044604049101c0c0885e0095241c0074049010892411490310860302d6100505071401c1800f41714090220644001d00000000c081c00460b03a644801143e040d00c3d080b558940e42c6100c1d01c528007000348160352000c03055000110300840c00781091401040154590713621904a40e2046d48a4203c1c0c0c032851082d03030306030070040100e800e0303400040c41c3c603401e6401c1c071324000540c2aaa86020a0956100303d83c1c1d40394080d140d003943c00400105846941e00060340b0030b070410051078108030180c5207100e10685107910007031040018000900940007900c505500070708054407001513007400d0300603100070b883c024082d050703080d04030341d480c7d210301c16000c120b83c0141c1d2a60f00c00300ea1400d520b0001d05802c801079a510184010100795510b807442d501c4001c10303103540102450070310340c10440608020402c0710301000342 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 149309325 1250 149308075 149308087
    0x8010303080a0b01020a14152d04020102100606051918030813030c09020d0e010b0d0b0603120301030803042105040303120f050906010302032e09080f030c130605 71
    0x740c000c440719802510600000307079500c55600140c1c0303018080c3d040100f0f1802d5150b064031035004046115040d0341d15042014080c0e49906124107281c601081179411075810345120210300c441e40c1e2074442d400030f0040c0184c614002d103140c03920b810340301d07035410410200d10300250001d140c8001800031a1250024a00000b204081080450407210745100c040e152480100b0001004498411014003c590002260600321360b1005094069001a13440c1181b1900d4402c0b800403265040c0101440d6200041c201040030541b543e42203901213000d09039a400d442070246103105000301d04004c40c0614094640c6544030702d030510305014882080600c6004441c81407075034504140c3c000c42641c0660b5410b081c220890100012030b000281200c654214506041c501032250b040c1c00450440d042e17070b00a4040c0c60a20030078a00d40400ea502c0864100c1d070104442c64043d060b030b4026400071445520414890b4074048480f84118500d070025104c0c009001400180f98041c4480d0a03440001084c1c1403d140382070603 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 149310575 1250 149309325 149309327
    0xf041101091406091809070f060305010311010c05031b010e0c010c080406080a380f0a0b070804120b0f01140604090c11010c030e070906050a0302061e1206010e0108010303 75
    0x107221001d8007a01010034204c0303a55030351480e0200440407140103101d580c9408448660344482030710595480b0303a820a804200c040c0f00b030003002d06881c0c02c074000b030b070000f8404401140c0c04000c4000c251030174042480094800610301d004203052251050002c101d4607903128089013861424241103040c0021000542c0c0040c23040c0307041c0e400b20b8850b411b0240e880d9451500b11030240540c0320581940488943d402ca180018040750084400002c007580c0424003024800e004681221196442c1c1c408441402000700160f80001844034501c0344610b1401c00d540c42002d2614074548540c222000e80c450420820220a882070490042450f8540b20003100814004503606208074080c4104051f100d4040450b51401000481d01001c03425008000305405400010000d04108000c600706019209001400903800c0c00380e081501c0c5c0040000811a1459003003140039848001103d034039141e165440340080311020068040c000c090221000c007890030070001040c0503011140c141c1070140c00c40040c0007213 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 149311825 1250 149310575 149310599
    0x30c0306040f1104032102151003060c11100b13091106040b09090705090d0305071410020d06050607110405040f0c0b0418140f090703210305060303040305150406140f04110109 77
    0x181c0d00c120030b5441a5164272184490300340c0c15403c050252414404001001588181c84184541035582519200180c2c20006026516040d25480c3e01065020003080441039590100c01d07824171604200300400c1c0ca000200b103140c0c10a81c066103c46401151941035414015003081c0c0c00b8955161042c41c0c82039034030018940d6204c502024081200c04540d0b030081183c6000804120801e82e0220341d031440401c042c1d60003a50041c417001c100b181c00d0100009a07802c0200654802e5a80540114505040741c8184801010b00070419942102910450360114010300b8a00d000303001440e000c1a03817030741841e0948e9078404600e0000c00440d071600e00d507503481d03911070b6840341d81028820701c7c54504c503116011402e18001a0350009800d440c4840207603115540c085418040b0b4840702e4405000c0340e034911042588900681c8000b401540100c21004c194510240440d07600c41d20403500001c0104106a400080e400210780010200d0043d50070f00c0240328034138440c0b11034941c1c2440e14004032801c01c000e80200e = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 149313075 1250 149311825 149311843
    0x1214030708041a1b0609190b0a0c0314010f0602162103140c060912030103031d1f08040b180a0b060f04050403090e0714030c0306040f1104032102 64
    0x4505000403091180101030040302c02807840d80707030003400513100203600030b44406081c1d0701b40409124444035117200c1501440c44001d419008280b0301d2595071a10445005418090607420401d035560b02035040050001003c00d001e40b007034406c43c2c5035890821801078500744070700f4140c524402c2c094000f0000180c0d0a80750207504401d408a025080281e442c045c4c1c3e4009901c0141e244503400464944000080011510700c00da801c0d104542e582080350303403880841c0c8002c0c00050006050442542c548070f4981c2da2454040c1c03006003415814100c081c1c0c281e122103a10303c802000248038a000c1c04180305241131141c6d000303074298101d001c40007202040349984550102e030003810300000100281d49075885d118440442000a04140014a010f1034018201d103118011402c45c800b68002040b2803500c2080300c22916510000c0c01441c6480d52070f0895065000145070b20743c015210a0710b030755145171034090840928000c80c0c4480e11941180b408000c68084120440c0301c0b20034681118880640c0041c0d6004 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 149314325 1250 149313075 149313089
    0x903021e1b100905041a13020703140a02070f060f0201050f0705090f0301060302040e0102041a070503090108150a0605040f050103140109020a11030705210313030e0d050601121403070804 82
    0x2c0304030003810341943c2d030780e44981c0001e902c14a0030080c2c0d41001c410584015041c1c0d011200e0001904803a0700c4203080b4001d168020700040ca496a1f0040d07804c10900090100f41d040713004684000c3d2750b54401821760314a87d0080c2000072007900180d00c055409004143d0403da100909200514127900b00030001c2c05503c2045100380156812a10151000c0d4004000b81d5009002481a603d0240d5005d006c0e5009119400800c0b000c031500b44c40d80d0002005880100d548100910719140586004540322030b0080d06180c3d006003800c41503c259900d48491000400f003540301c01d6143c030300d0300f04000014200c0368499418503040003815802e103c090b00403141907440d40c620041e1503030441c28045403840212801c01c0c1140c880007600c803007170210000e0000700040d030080c00120001d440e00100c101070b00003524031403481c2904901110000340260070000c050840034041004800e400e0b16400d10f404000ea0150030078009520100c0180011001c05030f1001da4a900118580b664a0742c0744c1156102d42d2007015 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 149315575 1250 149314325 149314339
    0x60e0d0209100803030c0a0f02150c131206060906060c0305030f070e15040e1803030708090c030a060504050709060f0b03042618040615051c0903021e1b 67
    0x200900320800c0510058007003030f41203c0d10384c603220340782030b0069002004005c0400c20101c01105050310006444522100580e010035103500c60310030a005a400c40d503006129040303a0304001c16100d20030700c001c001017800b4020104102e86000b04840481c3c0070350b00141c0800106400035404030742c000089a40150543c062246a5900c48008841d04000d0710f00d005d50220020700c211207012000c074040d000784c0d110760301c408000e600d0b50040000d40e8004448403421075001480021009030090780c02d00e9201441409031800701d00000300007030070801e0344901202c00c141d80c0c5050000f807120420051000d00564030040010070300780055000758148034840c0390003003440000003d00f00049010f00a904152550744822031414640c40c00c851a0001c1c480c05882d144c00302e07008440c0c1d141070302400080380d52511030101d21013403824040b1841c2c5e0144142c160799034000300c1d4201e070780d490503c11001c0090184c2c0c050b03c403c0e40c020510b031540d207000d12a502841d6016079400c40781c08100c60209401800202e40f02 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 149316825 1250 149315575 149315581
    0xc010c020f090103030518010206130609020102070504061205010b0f0901050d05100504061d0c0105040b0d06030218071e0807050304020d17091203040e01060507051c050a09060e0d0209 81
    0x61281244101e92038010302c82c08000800c054000b4050300001074a041e11441031040c00d001240d03075a00486d003810385000c0d0304200d04085441355102000450061059400c1c803034903074003c10b0540c0d06561180e0000c8900159420500c10284201074919000321144c04001c0c1e0700b031000400c0d000c810302642e48510300c9108000c00b0003100b0002421001c45580b4180032038506030410600400d1441086d056000d803005c0d00141d01c0b070f408140d404d600c103070586601d41002d045c1020281e01d078000303a04402d950ba5030740740003201503030740c1703680c510101c41007410391242c2881d010000429046c440f0030210003440c41ca0304814862500103910a920141e64507080d91aa621400040e00b001c0f18410f0251881e00743c0010a0007403680c110082030900381c03e840346002f60074034072001340c0c0e20301c0340d4462440219034584c01070100b90301c2100202941030150381121440003115903001d00d00207003092030300049103000075000c100da0b80080f07800d40105960f08084000310000300c0803038550842650000d208039084000 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 149318075 1250 149316825 149316829
    0x61305090316030e01030b06030f0f132109051503130305070b0f070207060f05030f0405010e0303070504091404050d1107150509041109011202071e0605100b0c0c010c02 74
    0x10b40c1c5401d60050140304580441c2d003000707003940c6400100c0170700080c14807641041609004048a0251100602e02c54590307036140c40708030f10084081d0840c2e0444050001003c08a122091003012000e82e1007408040800002409490509244d1040303003c0c0e02d520320802080705440d01900d074001034481c044550000340b45422074140c460301d40000c3c0007041560070310050400c3c000e4024480c02c855000c84a074940c481d10151442600c1c00b00440000303208100040000c110355054a821030b12070000482c40c008130100305411900f041b901c0e54000b43d000b02e42044910000e0003540f510fa403003580320303042d80d0509803501d586805c200d01a103001d004e0110b81c1030b6015181001038000030107040821103488000050000d142e41c3c04010074500c642d05000c220f401d49a1550201e03150000144c48103421140308403180c601a420101b0b003a503030000c7e901c4001e03580020304980400e03d180b140e140002d0a01d07006080200c080115080260100000c0c800d91944103c00103c041c00c051007424903802c41e07185440 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 149319325 1250 149318075 149318077
    0x4140f0105150103061a1c1a10020f1b030a06020708180d0804030204240605091302090a1a0706060f06031b0206240406060f080a090b0105090c0c0601030507050a0902030613050903 79
    0x140d1600380340c0fa2420500941010140801c4007041762071800b254000e0034120b03900c02c1c5042010b00660011481003610350750000030b000c90003602034240d03403b030611a1a11022604884000c1d41c0300c1000007821091940101c041c40c42d012003c651011000f04d55440340c400d24003d030300000340100c3c2d030f5900340038045003611588034181503504c46050130030380c490b03400808941203416414011602114542c20710711030ba009407104448050410f8250710b1801c801059800c0018000100c4007804200c10404503e1038010300014000307183c0322a0484d480d11600504694075881441c80d03594079440c1d90380f40c0541c08140300740c02156401c4040300d40b0641700084005441c260b4100c940c82441d14070300140b2190800030041003920152079001090361801158030556410010042060040c0300042c0900c4c94403008a0b034210840200c581d09204600310564034010f42a0820303030f5244d0012008029600d000e42d00e01001c1d01c2c1844065095003810004607002041d16011145041d0f2910001412081c00700 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 149320575 1250 149319325 149319367
    0xf0102220f23031614031e030f09060d0203040303050708010b1e0d02040e3c0a09060b03010504050f100b0616020103021c02030406180b04020904140f0105150103061a 73
    0x20a00c4c201155658404100007242e590f0303414000d00400041c2e00800300c0200f499025600c0da00c025500e0000d0007000801c0c030b54800c1ea803d96100d4001e02c600110000e8910155105900c82d45001455003850035003c1c1841c10140c0c401440030342c0410444800321030212512010075132030441e11783c640b0311844440020f03014030741240d0b080101c000e0800c000c00c00c420004032494501810032081c034001c000341c0c0e894002c00014021402007000700200f030711840340390302070041e907401141c00003400d12074000007a081d110280c03400d6641782e005150014541304144074038048980c01510410441590102084007801039850105c0450090000e040559010790126048041c0700c45c1c043c2e03226056522524000d400580e8142c88440c40c2010600740d0400c4144600202c0360084d90000309640c8030703402c010352940014022240d0700750360441c401d00700c1e004021000c0910f4800f000030666161407010b07181da07406503034462070402d81464001c000306082c03c4003842d500d03060030030b103640e9601220501d1105c02e0024 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 149321825 1250 149320575 149320603
    0x1e02060f0a0201060f06090b3c03090f0304080a02090907091407090f0f031b0e01080d080604050606030f100b0a0e04050603150a0c020f0102220f2303 66
    0x709108000e41c19480b02d0250b41c0d100d0b140e000390301c0c1c450004541580e10ba00503005030040422040c0d10b01e448240c1000405a0046005085031861114100b035600b06043d00c440914000300a010b0240014802c503600c4000304001141441c2c035100a03940c0d601a1800b01034003840121003c5000d000081c44014060480c010301401601c051311080d4130000b00899504000480415012502c0041401c0c0d02c4101d034140500811918119205c0b00100320420310002c40041c290200022041e00074914980208440382c05800320a100324805004c030140280350f54402c602d403204014042d41c45e101640e4101c521900905056510034400300004e00300d40c0c000184102001c20610113007903010520440340300c8240c6003844035845410515944002d00007807914a24015400a003091074a035014050880c114411200c580350054221400c90f404640707a14a03a941da4046076a040f50100204001414404249401c8a05d40b0f4a413544007804040710600384145016140000c0d07404120f0501c4441030 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 149323075 1250 149321825 149321827
    0x90c020a050a0b010510020304080c0103111605010203060a120b150a1d0412110c0103110708160606060507031409040b1008010807060c02060414012a05191e02060f 72
    0xc2c0c0d0400803141d100910545204907440030407507082c4c1d480442a94119691400201032100d5503500640151401d804100034581c0309000901380c060403503591200d282e019070001a96420a80140600401640c02111041c1e4251101c880092000342c10268001c2c809844904400d050600180d0613035000d511095001c0da865201e40440d400050701c141c041c1e4030070004ca20107114001d00c20f860350300940e0701c1c0078078503000b203145032029500130340012a44004840d40d070b80c6428882e940c1d07440640c1180c865495205101f1840904101c0307d80b1030000505500c3c1003080c14541e1507900213103854003074207010038420300c01f055142c815121034105807075214000700034502c00802c0c200b004202c2d0300248070344c1003184103849000031064020b40c00f01c04401d07000b030300f414a050306110100000c24803420249041029150845910390f80210262107841c803c02140ca0440450741070851a120a000700000304550404005000070a8944230850b025080d203940340c2071507002d00020321280518800782c1e000c040 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 149324325 1250 149323075 149323093
    0x90a12031d040c020a0308040311071403010c020f030a0c061401090504050d0e01121a0a1205010e031c2307020c0111030a080712060506070804081510090c020a05 71
    0xd0428a04480340100003051010070401d5020401510a0210703510056004201201c011030b1107940c00940c42402420440c42c0c06001490051030111b60f0752250303810100c10300940115203801c0c040c0e075000049034402030205400010410303440b446590a01818466084c410b681040090340207100140c42d80c540300b6410f50394031203480c40540421503003255503000f090789010341030b806003040c4011404d06950b90308545162905807402080200c4400b01c0143c2e6040a100ca02d50301e00354454091b003021380076152035a071329181490a44200b01c150000903041400011200f10f41341d080041c0d074036841c840c0072542c00b1580a1003150205100711000250413000b040002c01500043c1c0d400da182030a80e550580307544c15095041d10380c010302004d000000c0480c03010515a92140c404050720743da15100c00900700e0780e5400000d0582c1d1102c1000c80346000003040802000105212104200d00b11000441d0b052503c615050a044070600651802a40d01c032440d041c964402c11104842652210407101044 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 149325575 1250 149324325 149324327
    0x30d050a0e0301050702030d090f1b060215010e07200a2607021e0121050a06080109020a05060c0a1a04050601050d0503070b04110d060c1d06040b090a1203 68
    0x58080a8004081011001c0440c420300381485954491000e13035004d141095001090000034202445007601c913090320344054000301302c03074440c0c800c0d091180c48a80101c10b8986140a42808080a032554191250b0001003000113103207010a03901c403d0b24902a6144032240c00d00c8600c017030781c032404040c1e180b05810310a801c01240d015503462090544040000c00340140b0855082c0c0d101d2104d000f5000750350070f005d9046003804034180c0b82c070080f0141442211151001c1d40c04688903c00700488a04644071010700c40749100341c0c40b40b00c2c040d1014600a03c84041d0a8000c207010492510403a80a0540040d6203040050240b1420384665800b40d4040032440c0c1d1269043ca1600c0c0039542681c83c0d020f481d00004640c9010b282c0d00c508641d1041c09142001d2168543e4610060028025581e1180c0d1468070510741e82c824041d0384049104000004a180411a000308120f0328000d050115401d00c0301c044007199948c1e41506c0440304440031a5503220040700118a00d20340a90207045081d0910310000d00301 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 149326825 1250 149325575 149325577
    0xd1403040c2d053a050607030207030e0a0834090b10032c070b0d15050109060c140f0106030c0e07030b06040608060d020303030702071e0f06120605030d05 68
    0x41541000070b020034548a40800c06064007032041c002c20301801c1507112041c0f105009920302580b00c00d8102c2d00307500c0750a4945a040034000c95128000988c0010420101900701e500ba0840c00410342c1c041c20000d04008007160b40e41c2d5120300b40340f00c602007083c40e0f51449020003508400d44681d141003040c402c0e580c60f940340103030445200c1d9512030804040c00200713061080c420319261424407080220341c2d40840e92610845010200c03400a6030040c8800410311420b23803801041002c0c0e54101c001103001c01948040340b249005d40019040040c0c1d02c208006807640010140d003140d03040710401c4000f68103c04c485280c8092a800b0f80700341d500380340d400010301603110301d480300301c07100c55890707941d240d850150460845000024050384150140b00c18000c051250140c1c40c0e01c80317009800c2078428007040d000203186800032244400180e20039641803104040007140c0313528130461009040c034030506001e201600c542e0907028500c01c0050411f03110407000d0031038200c1001050050280c4100d0302030180000e00c5 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 149328075 1250 149326825 149326889
    0x904021f050c1b0604030f030216031112010c0519091716080c1503040203010b090a1a0904050304030201110709050405030405040501080319141314010e030d1403040c 73
    0x594001d1400e051401c24510000c43c4a604000781010f14042c10b42c1d4800055aa500005804600c1610ac1640201d4040364204018500610710461030502e200c003004500103070000502da403641400600c0e0361090700f0800351100003000d840c0300c215070b03100341c481240c00280c06e03030081c401d2801e01c01c40c00700c8136500400e2010026412504900300710b44c031024900e07611044000d4240e0001003040c81003510294003405107801c2403004001046082e40540000c0d440d101c06e68180c014155154400040c0d40c1421807900e0000030305540e084100d01d071a03213660b03407280660300c8040d05211460f0020b200440c1c042c81004040c101001080102381014104241d0365085800b61038051854080046001070b0700100703480707442c800700c40410f030b0780008003000701c540d88880070340070309182018044140e007580d241101001030300c1c0e00b8280c42d85001c8100001424252039064003806038003c015100c0742203501c104110f007409a19100c0036500d8489191002d1103a8050707000f50f900c50720600115040c8640d200f07004031 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 149329325 1250 149328075 149328097
    0x5090612011b090e01060807080a0f05151e060d1802060a0203090a050105120a15050604120c0f050d0303020702060f0705010c0801080f0705190812030a061a07020904021f05 76
    0xd09502c601300d0b54043c103001c1c0291008140280006008540320382106a8025585040032503182d00d84c07039106090301e80c161904045201d6030b240c41c0f0414100f00f401c3c00001e005204420008039440400700e2090310441c0c1802c988151200100440e44c080329034410002036018040f01d5641140e00e00c000d48940001d40f580303200d0882c45d940040d180d8032030760a4030b2001031803c50000441e250000403c0007010707690340640d07002ca9403c400190a41d41c02d0050002040809040e01c060441e40c03505002c0b01e546030f0480714a4030301c0d4840501c01e42d111810f0151600e907240c100103070f030340c00c0c0d03800011018001c10000701c0034000c00184460820206401c00c091952841e1644181a40c0351443c2e544c94020f07084102603154000141008103103440c03411a5083c04011000400880c1c5607280030342000e4003110001d80c42c0400000340501c0348164417800000302051032000d010080003c40d0418680700e40e070000303846003294001017003e558907a071a0404000352540101e41c075030880240640103400c003009541c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 149330575 1250 149329325 149329337
    0x705030f070c12020609010807020c1002030a0206090106140105071a0a090501050601020c010e1c080c07180b0a0501050306060d09050d020d02060405190312020a030b0a05010e0a05090612011b 84
    0x40d08003000c4040f4a200b58000c1c0180d042503094401140c440d14000c2482c0b04501c566a035211564551000300e900740b400f2603002d540d1762181814040e152610140c141a400d070700d040402c01c07103070306440250050101c0928055940f08054200049019200e03c0148100181c40041c03290b1144651710014000e8880e43c000c0c86240d95113001a42c840ba4900f00842c04284c6044070180907142c016141030341c5942e4040761005820305519925482e401c09a0601a42d5100c410280543c50820900d0802e14125a60078481e0710003520110300c84c14954031406050080200201e0410fa0340c2c2d0060300c60143e41e0250810244019050403581d0304a15001035002d030081d46103e162051007ca0160b00c03980e0085c0040610000f0031609007842201c0c118181c0401c0045200680507108900040c403200035503927808201e030341d41282000310300041a40080c0c184481d03070301c00358280e40b540c0348620f04450085440703002c03c2c1c0d640d00101710600050402842c05510f00301800c104490740301e00480e07601c1100e139208 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 149331825 1250 149330575 149330579
    0x207171c0507180905060a12060906060b1c05060402040305030705010902010f03021e0d090203030a020c090a0227010302190503041a070207030605040c0f03050c01031401050a030213020705030f070c 87
    0x682d0b0f02d0745560150b200311240c6103018056031038076401850b00404040c082003078581d914021180901000e80c82107400c0d54541e2114820311000d806820064090900981d10704500b071460343c01190210300c4200003140e180c01c005183c82c1e4481d03042e01d00a58114040c2c035600d0010b0b2800074020000190124080380d2400d8600200b1440b03442a1150034100500009d0b500d03c8010302405141c0044110590107a03d0380904001620180f000d01680350340d5400074821150480f0401c80d021000074003000d0002d2060000741204140481c48440c106009021803120002c2080101c002c1d100b00c03131000b0320003000000207040d00c81c0c0c80002144510f00400c440640314030342d10103d041c550025904a001a8000c41c0c05002150b4103611a40c0c006100b40f0200100990715800b03d8400c00c000da0050759690403807403000d0135a5801d40541341594a0032102c0403059070400c0001102d51203103000c003a000d0000d0798443c44035203a20b541241c0d081138000c0112038451101644a4919030b00c00a406c071500c080034840 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 149333075 1250 149331825 149331827
    0xc1403072a03060e01020405060408030a03060803190e0a050307060e040509070605030c0a0c06051008150403020715090e130227040b0606070c08010b18100501030207171c0507 77
    0x1021010381414040e5071064a1601d0720405042c11010801079554200000107150f601c5800400c002c3c0b0038031015545510740d00030040c085030825800003125400421850482054000c808203070744465040200e083c900d40e0011505441203a0446c58040c8203580d40880e1854001041504081080b601444941e80b52616261128414421440811070034000b04002d8218030006e4003944000e45408034500b28151110019540d00780c0d100c0121842085c02484403c0e4240650704030702020301003146480c18940c0c1c0080d0381d883ea510030b82d010b107000462060003042c4200340500040c80300f0500c458581c02c003e11150500340700294101d10035101c8442d00483c42d114405080310a007401c081c0d404144c0d0312a02d90921028000b04002c0d0f00c040d08001560000b040420303100b000e001503000000f03400d6544001c0c44094960443c140702c40809410812006070714000f1020103640082c80c5c0503842d4040741c80c050300060518031003440043c41c0442e6900b80d9001c0410021603e0046003024403403a00c0700c040c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 149334325 1250 149333075 149333123
    0x10030506030c0d0c0605031906061805220c020109060204090e0606090405060703150509040308041106070c05060721210c0f3207050d03060503030304120c140307 71
    0x2e00600500c1211303820010030740520040d680c005400d030304030700341b490a0380d07929001c90b2200d401400109200110f0400340e60a1803218601a000690324020402d1844107920035440d449078114141c2c1b92a00d41030300380180700303411109040764010003d5407030f41e86400300d944c060070316032410f0305c030900c10003001805903d00184445d0107660080081d0207240c0f54400200c0c058241030304a4140884080c1c8000341c2612040003040c81075000366500d41c400d0810349804681100b800301d0503481500c0c244061004900003860306000c42d1400c0764800c2d84c4106500c0c12242c0c2020000040780d00c16a00150319084507002680002d11104100c02108032840c0c103000c00013102c0c4041c01000010b000217000359003540c022a0340402c4103d88004505c0c0c284c8a4244150b0043d80c1c01d41c92180c450320102e6000b0800c00c041000147d61034680c1001d002c400c0c18103010980c0c1c3c2c08002c10140482200d260340002c4075004070213000c80340c2d80003152007481c50003008050340d40b540440000c07640c9048284402d4a0940811 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 149335575 1250 149334325 149334349
    0x130209010507060b0a0312171005062205030a08180d0f11120304090603020f04050702030a120e0318120c150c01020c030d060513050112020907050910030506030c 71
    0x185660382042c00b40e8680d50000c1022000031904a803a1207404004202c00004c9141c1e030b03400960f030301c450038141c140c0042000700024014548400385090240005d5a4080a131b492041032014040801c1080b0100703150410f50503032140382c25000301071802090022201c01021030b1626070028611441541c02402001b203000980500a01040104880081c54071082e45811040042c8001480302c840d0b65041e0850703009501c5034441540d01d91081003142231104c40d4800840044030100300610704850040d445c2d2080d81e19850411810000380280e010f01030f8040224148c1d50000c0ba522224908c8400d14168403444500d407144d06010030318220260009429110001c01400f442503200e00403070130761a9a0029091081d00755005d010801c0e00e000104041c0c004800c502c034000c01d038a45814140064400b59060385800182030030300510010040c0515007008540c142c0d040c01450b43c0c0d4000442d402d018008107903900020100118640313590607000b2500030702048003603a1109000108210010b108030f = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 149336825 1250 149335575 149335577
    0x90a0f05030705090703020c01050f090c0402270d080c03032202030c01110f0105160305070809030301030f06090605070315080a020f06030a200c120901120e01020904090803040213020901 82
    0x842c00611990800e10701194015880b400e0242c2000301d170f040300e1030030b5840890301045610000e0b8100701c1c00d500200106682c0400a41e021450010380e0182004801124901c4014803101e8080011036a11512120404250070510107501c3d40c4a615200f40c43c0d900c2038071403484a1300a80503088441101001c50728030f160740180106881c220100055600c003000a04d8139005001d000ba603018200001e0251500c0703000466104072440452803409801c0700c001510840c10849000108400d4000020490f81502d40002004079052240c0c98841c01a10103010001c001c0d5042c9000d1094081e00341d0841482c4c587c50048058446869501e11684c80308980c030040c0d8040c0c1300001d8010942040740095400a180f0074002c262400980300c0904070700a140c07000c00c1c0300c2c800000d1000600c04240085c018004c40481b09030301d40a001e200003400c610341c103034400156969480c0f41e200d0746002541160403152000e007062140c5220341c240a141e41e08200c400741c3c01006200c005860f928a14030803290b0032481 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 149338075 1250 149336825 149336833
    0xb030a0c0509060909060a0b0403030206040b0709050a17120a020d09150f0e0a0302100c031205010e0a020a021c020706021002030c03130609061a01020f0703051e120708090a0f0503 79
    0x4e42000c11088035005480c045c1c100c4500e01003c140e40f0340c1440104003840c040d400500503410079150100d5108030043c90141003042d200c109108903a504810074023121000c440b04226110012269800c1084e13548508412800c006100c1c49499000f15000c800002c0c03d071031301c0309817650300c8401001ea25030953700c00c0000b80000c0e110102941c000c41035002c6c3c000000d040d01003003944aa01080c0310850300001d8030085002c0d400b58104050f804801079094900044080c02554545240b206021401801344c4890380c0d0041240042c0c02c0c400c200d20b4420402d000700c4003544100122001c0d40703a1142c3d01469005004280d19041c1890050007203a00588041c90078600c1c40e5601d41841c202c00e010600201c0700140c0358421000450080e0090b40030351920440c0c20303480920b5050029150594850307541c00203070004082000071640124010700403e00450b2000600310042581c18100700e4400b0452415030b0001c1241024008444040c06451780b040e95052202c54a070305101d0b000c110700c2d00c079165160348 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 149339325 1250 149338075 149338087
    0x151a060d060509090106050a0f0302010e13150e0a0c09050603060103150806040c090c03050f160c080f0408060906090a0809042a0e100905090c0906040b030a0c050906 73
    0x80190003800c2262034114000354880d01c8000148100d44140c602d001c01340e455240500ca18501b2052203c0180825960420520314550010f02000e000180c0f036481080c2480d40b03d04520455040f140801103c034007031204080e190031101e5407040c001d403078102403a40707072003a060402401203007001c05803540100700a0440e40d90000441c042d00c60082c1c0c07007080c540c800e840003a010b07404002e0540101e200e01c0d060030800d4180380e144011904a42d040908040c1000140016194038840c3d07070307401ca4641450510918003c04040d80d00c804811401441d940000078080f4001140d50007410903102d6400030b40f0780603207401220700da440c003040c1c400e903982d500610500da000504400040a40303450280012444603201015103201c2c80741403115510070031448100c03240e11030f40000504400c400450321501d00c2e810f8480010101d09150050314001e050060200303000303003688405d40722000c0000b02201d0752240c403030703400c18880c0d082071b01c030904141e0401c0c1203151428050010b482e2007581c0a083d05040007 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 149340575 1250 149339325 149339329
    0x4080703080a170708070219080a12060503030703020309180609011217040303020d030e1216020f15180a0e0c1602100e0102191707050102090405070903151a 69
    0x1d80300c1c2c22035200b4000c01d0315502843e99080c10503d403141c0c503d6240c0a24500d840380e00070341055851004804410040400c41000039048010358400c10003920306191010280c500040040101d504804c0d494800071440320209a4000000c007020282a1041000c01009a028107040c0700145d91450384502c50301e00511001d41c0d01c628403420b079405552161303403011809901c07401991080e0000d400507081003503880e0b159501402902c801d0444003008001002000711100da0324050703440d440700c056a0002511003503540f903202107254004000c0555401302c4442c02400300c0c580c0011441401d602c0c1d507007800f032501d10f450414a000c60f4000091f001c107a40d41c00c0100c081e2503003d82c0c40100c61500400e40d007c096100c0e040c10142d600b86070b4803508004c2101d00c0c00a854038070407139913000170038500c1200280011100da08568040c1c284030340c555241c9405191070b50182c000d202066400c9440c05040081c440e90041003a0226401101d0004442c1501c210700016181e00707a8807501c2d15014829440d14034 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 149341825 1250 149340575 149340577
    0xc0e04050118080c0f0d1211090406060810080f0a06090303090b04030f02150105100302090d060905061e10031103030d061511030a090b2503030603050f01020408070308 74
    0x103218000015982145440d0208088401c00c000d4541440c0800c8080b800e81c4100301210b00c0003d1040102083c00112500034506112001031440c2c854490560f400c07101491001c0c0d404510000340144032850311140001d1034240c0803501103010403004280000d54040c003203807001c944003003000a0000300003a5201c01014103c0c0e441c0840c00c055440d40c1d100c01060304030707448500944c483d548040000703010030070091170502a001c1c42102c604099004100e1a07840c850000c0c0305080e076040c09030321419901c00040c1140b03881200540401c0c1031401420810102041c0d09210b20141001e60072902091108032640c460b08031040030400d01004020300111b1881540744e545808018101d80c501241d1241203800d0f02c07016403103070010018000d0480c0c110380c2c100341103015010101b00154100454090001c090514600c03840018140c0000c011000e4810b44603844064440000c40844146151074014010f05481c41705407524010000444403074541802281d085901370b1009200071819500c0d40401 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 149343075 1250 149341825 149341831
    0xc040b0118060c0f0218040309050a05011b0302011d030703140711040b150d0203090f0f030315040605040e0d12060f03150e010501080f0c01030c12020903070b03090106061106040c0e 80
    0x3e01d0b04a03a4180340103075144101b45581000f2a19035149904140c078000c0c1c185402ca40242d449080e03412810f000590744810781074041c102c18030b203008100300c19003802d0f8018410715412450303030140f40c20500c403151800402000114860b545485c203e4100340355184040c010380800410030040c07104241058946600080c0300f4000050100000401d03820640c01c155000e01c02d4004150707004403c02c80704250900100d805038105001401088030001001516880300502c40c60303070410841c00030800c903243c1d81d208102900e4090000c1110303103130380c155403640d6800000c40400002d4986807410001c20b000d000314000c07500410000300119045903a01000010302c0d201415025030750b13541c11009a03409016032070091000002400b880e10516032842c2c1032420410740c05046c181001c0891450075072142182502c00500e120043c0c849444030000b03810122140d1010b40035032030100a03c03504000640c06403048546580710b04603150b000603138407500c070316040b24050900c049001c020002490311010241e4 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 149344325 1250 149343075 149343083
    0x409060b06030a0b03060a090201020c01050d060b0a17090706090504020a0c0215031603020c0c1e030105010308030901060602070b030c07021503070503040210020307022404090e0c040b0118060c 85
    0x806414030000301d100c07908210b558031901601c0343c0c640f0350346081c1401307260b820000d42c1909009051403600042c3d920703480944810704100e8001003400c03425040b68031003000741021400450b81c540707101e10014484440b0361100c1c40c0200c581c002255403e000010800119242c603140e41003201d01c0c0c0001c01000390050f0110f00d041c00f05601003040142e465400c040b100704445200d294882c246001111603600407024480285441005400116000082d61600d981c20480700c03d519001c0f031143e108143c0b000320415540640c02c1000100400001502031880780c00040020040c032640c1d040101d039542d017a803007032404015040020541c2c08d1034040041040d980046c001d40e0f21040401400c10080e4012680c8200050340401848114030f0855070440c403c004c184003d6080c000d01d81c0020b5490a01145441e00380607110140c05c2010044074142c03002407022050070008407481140c20f50303d40c0c00704045280700f146013040d1100150300840d030584c443c100104a4408075800c10030300740e8981790342e41d605075 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 149345575 1250 149344325 149344331
    0x61701170111070507090c021207020904030c02040213060305070f0c060e16080a0b07090819030e130e070504090b0a02031b07111807051e16030c0b09030a0806040906 73
    0x20b16400c0c19030091400c94401c2c2d00800c45945480703081001c9400f0a040c07401150814034612407010100340503a102030307804484400140d1514134058805010101d802904107001090619283c040004820101c0305d50340c50078001591450812038680c007450000c240400c9440c4a40300200e60507902c003250020008003212003004495144880c1c030307c1e00d40d010100ca48d021020310b00820200d0404c41d504080342c0e09061207501c0c10010000e07111030484003002c2e15511100510700c181031150b9500d182e40354025040e60f007082a135985c0310024040c00c04001485206858000035181420b20a10300466004642c400d03858030f80c5030140c400f961010701190030121b0312585e21912032100c480281045881000b11042a000c00310900102050001c00c200d0041e14610404c480e03690003604580a00d4880281c14200000e1a040200b09010f50741c10483c100310546101c004140d0041114503109005003050f6025076914000c00342c3c2d03072041c28003a500203254540800c400d030910b500032890381c41c07081c0008 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 149346825 1250 149345575 149345591
    0x501090b2508030c040303030c020106031106072a081507020a020d170f0405010813080301060f18060224060102070311011205070906110c0901050d170d090c0617011701 74
    0x1202c80d0341c0040d910001c886000060800401da00362043c48442201400244402071950710b03444251039803400c0503400b482d00020036000301708005001c40780900030b12082e01d104080c2d5a042c959036069501410400d80b0549503000c0403030003251000c510811071036000f8490044907600b03104451243d510111142d0002d81310000718400998040c092084115003059151464035000601c90300000d400540d248109141c041d01007030024084038150307506d40c1000c100d8894515003c6400502c500301e00041402040d90102e811035000c00c0c2121540c407401d0290116182c1008040e00c80201502c3c1c2d107016a200d00c504000042100c020072807400c1050401d11080007284105c882564400c4940c03400003610340206110b92604000b440d001078a1180041c0070802a50011506141c0180259072003007807008248400c000c0307101d415109501022000c1929200000c8800003c4c0214881c1201c0d405500540810f005120b00d00510744c250943c80143c8a0f42d10341a45078200050300c07000c4420741d54030b074254 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 149348075 1250 149346825 149346833
    0x80708070c180209010f0804030804062412021005040803030a0f020d0e060f0a06180510030f050312060d02091915030c05030601060503010f2706060503100501090b25 73
    0x3048038840b080800140c2c1c4c1d1132103400010a80010380348000b007031021220620010a600c4585654020385c006000034100c503401070200c4058048040d514500d03014008045500132151280074001c0d40b09031041020000c000d24190303001e002e40d0054030311a600600c0020b920345000c0e001a00560004100185058030403601c003001c1d904400c1d241d01180d0b002e581409903015482440590001136040c0130002c1605008042059244c0840c030349c5103481d2620007103200c800f40010000000e59100d40e0300d910540151410640382e400840311014102c2240c030000d046400c0550b9041d03c030560082ca0608a07681e684000031a441701e46803000020355880d000101c0d101c0014500381c009d540144a400301035440d0100705454038505800c07442c100141803004011350300050521074142d80442e00d0507907940c0e07030aa8030600b04151111162102034144040024880d400900441c01041d9a81087c625691550019518110248200040705004100b5111680e050f0311a8129480074121160f03100215919 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 149349325 1250 149348075 149348099
    0x6130c03060b0304060212070509030d0804050304080a0c0f0b0f0403120e1003020409150303020a12020111030c0304050c1206240405010605030601170106050a0f0318080a020c0d080708070c 83
    0xf4007256021b5001602d040304001e0000b040e0350010492404516011180001c25160341480d5061020320041074081001c000040c419100604000c03401c40b8504011800c1400000d0f503144a444942800101d0100e1031100070012203040a006860726841d06265070350ba8100755101850301c0007000000c09030b078281e40d90780b540c07035208960640e42c01603180d5003800000b5049a04501c180c5501136802d040800000b90085100e80c0000d421120509c88041e010be020380c050580307043c840005100c00000c00070103d003058007540c001d5014100301c490440d000014002c8a007410002c00030340344d0194002508400b1110140003852900303d2081d0006001d50300810151f4400703030070000205030040200100c550744040c807143c280d01d14503183c10f055450300c00080e00c03a105443c80c01007085030403e500900d881c02604680f49411209070b81c0d030800c0d41c480c207043d05c0a80042e03d510005000c0d52000080710f02e4400c1c01419080d4105101d240381c09803071b80c0c0c1d500c01c41d8000c200440b0a0400c0c000001074200c0307502 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 149350575 1250 149349325 149349331
    0x1030b060d1a070f080f0a0903120608011e0203090717070803071104051b090118170604060c030c14090a1e150c032705031015050301020306130c03060b03 68
    0x2c081580e1810b0035000035003038400c20f011610403c0051400c100700a10901c2c0301907003062004e5000150b140395410103c641c80d2505e10040303070f0f65051020008090205500c0221000201110310640e040d070f244600301648000c0e07420b03000d203074001c107011700101195501d00e103150221031044801c0c0c5942eaa00b400e0135a00074040684500c2c0c000070950b849811316010316903024003008a48480d25440203440400d074011680c6103410400e080804046440d01c03c0a1140a88080c9202e214407a050003003482d0344240031601281c109007403964040040340203005503110481a516a0801c41640c4802d03504240c100b444150351003030b10f902d000540c0001c10a60700d88220340942680031418180845602c03440c210030000010000060a00300c003082d4031444105200380756444018400c1540c00e241ea80e080c0f2950026a0305001b40c401c0603224201c141d2000903040c0c2c0420b0032441256a94082600702d020846a103500301415204400b1215100e80c008651603006007000070b242a101c1011500641040b = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 149351825 1250 149350575 149350613
    0x50d06030c0527070f051309020c010b012a0602070c06081803070209041506150509011101150302100201020d06270b0f04020714030a0f140405030601030b060d 70
    0x2002d000358200201001c2d0003d01c148455000c0c05001019052480b0000b01150108404a09240e4410340318204960100d0100e0440307009071900c9581b41030003076109020011247d032800340003130010f501514480032000d40007108940401e031045407240c000640d01d0740496800d5420022100000c00f4a02d04202034401c540e2658028680b4004206c2462120b150003441c9034001d021210050f602c10502640c059400070710110755021070140038015100640200500c080c40e411610a07680d404001780017501d009994858071420601059800ca0354903110481820400b901c3c14805401c15040803910942c0d1480010701d411868000d1a04480b115000b694114042c0402c104108008020004050039903080801c882c00c01ea100041200ca200960b15024039000f292810511683c03c0700b404d13890381d2144c140d9980b4914000024214107403090076501140c2c41111004a60101206880c241e51002d0300412050b42907456070b0084100050030b01b540502031140c0741e0b000a2001045154012007 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 149353075 1250 149351825 149351843
    0x206010302030f0303191a030a081c05010f0e0c12130311010b090a0b0112060f0e09030a0c030e150c060f06030c0d020d0807080c03030919020f010e01050d0603 70
    0x441c4105414150089080c840f60360042c0280001040c14440c2c0f000800103014001400b401e001460500a400301d041c034961602031407082c441400300c030800803c520004071080c610844004003145044030b10a000b5011402c5c81030b4410b00c40d080c1c0c0075007626000a00c11410034181a040403144004090485805098014035600c040030140c100e0040f040301d00c5180b0003840a0407040700401c48510004004140070780c0c44100e8006582d0081d40c061414007444503050140b141c803020300d0b2010ba1001d115104900c0300e0b00740010076000e404025140c5850140d900e002d580d000340c2c2c0341214a0059010015403105c031020148503080d165400902e003080b15180030700064500518801480c1d040205001e001b0b07008011030705403e5860040c03081d035035a41100c81c580104103505003500d0a01030014000c10b0064000b60342c1099810000155125030561000c0340c0071815081e03000541481001c000075009402e0890f090200e600035110040183da043c5003c60920441481850a480d40359106540180c0 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 149354325 1250 149353075 149353079
    0x10e0607030203250f1115161202010b0109030b0c040e0702010905010b030601080d080a110c0318060f0702040b0f1f1d0904080d0b04020a03050906070c120c150507020601 75
    0x4500f9125040c01004001000002458136072555144117690010030824451000c502580c0e03414101e0703164125443c070140c2e21000c10801e90500601150400c0da01c21103c00705512203a8030501410500d50010380d2026003652559641d0710007801c000d007426001d800140400b15001c03028580c0c003171107590185d0010407907041030b050207800c4a0104c2002c9000f0f400600061041c91400207404071501030340c1c500465070755a01c0f0304103c001d0001181c6a084c22800140c0c1c5043c4490010190110388007951070a04940001820820280300d103405130070b02224140081c0b0090b00e095403100f6803111000d816891001080d2000440c24038014010303195001c078108181d00200c1e40720080141512019021111500141002031504e001c01800140010000103800b030340c03130f905500018030012025000b5034aa000c0020007802524084491130350380c5c403440f00001d1105105121030500c0c0d6400030386000343d20400c1101203903072031000c01003682c2c203903600701c20090704c242d8520810b0710030340d40341d800303084154 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 149355575 1250 149354325 149354347
    0x5090705160b0a18030504180204030f030e190e06060f07020a03150f050f0609270604030806101707020102120a0504020108010602060f0a0b0d05030307120b010318060b010e0607030203 81
    0x95031404104d5a40d002c0400340c0b50000c2d401208a4042c0d480d0024448032040c4501c034000c0107440b440e0170080003036510300140020075800c440400021801251801d44401d40c8039070890740c0700320324415092202083d4010940f1804d04500030940f007220f103443e4926020302a00400c81045050340220b030ba0480d080b40042158080f8403480310301c03600c0c02d4014005410102854a2000000350a19200d074404101040c642065181e070080c001c03d9040e040c0307400c3c03070b10f84492640354401101c068000c030300c5000000e0300718a000701c00c619a105aa444403c11001c0c0991094031155000b0405411356500f00414030004000301c41c01440750700031000200701442e00b072000500c0b034030042c1c0c40381007903511002c28051030b114068a01c0ea44030072103e50001da1211100005860030400c2c2c000508a070100106010074540e01030400c1000c5414004140043d844070f000440c200e0385036036082c000b049840d502110002e9410b030400d000174401458000300c0402024002802d0f0303886441c040300582c2c00080c2400c00c0e1 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 149356825 1250 149355575 149355581
    0x30908163014150a0f05070905100f09080703050a050f030901091701060b03070f0206090c0607080306040b0a0b030a050a0207150506040e0f01090c051905090705160b0a 74
    0x461100108034200e0440c01c0c06020010034400184420303060003444030914010010910b01e40f850580080c401e080c03c00b941401000e2404110007213078144400511481c0c082c001010886901405500f881c5d05840380c01c4802c1c01c090b446240410148010001c1e04580401901010754060005001441541c0c90850302d081640d400d207081c503400c00d0154600c180c1e00480c0f21821101381240701081d084038521118018805500f00c110105408414401d03406d0780004810442c0d41c650702100e1080c0c64801d44242e44011020015074071400800c690700008943e40055608650040c0c400705000f895440011212801034100c207200b48804020000c0c0400d06000c0e076034110905000441c40c0102036100c021041c030103191785c403103507a0300e5102090040c0c48652081d11416920429220042c00d05440c541c041d0500a034242d03050403002038049a24582034030030700000c041650101c99214906001d008142c03100800340310501c0414408407001000b81161107920710b1040b8040d0255103000040c100c11 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 149358075 1250 149356825 149356859
    0x6150816080a0314090a0306050105091005030606060a02070e01080d0206100b0706110d090b0a060801050c0a0305040f0b04030206070906050903060403031508120325090b0703090816 80
    0x8440001402000001c0010032410702c20368041c0303058a0943d030980c0a00c1024820428410b400c08038403d0004240040d03540418187d60040b1861217113030703c81512810a6600034001c140e40743e04190081160361806000400380080e050054503140c1c0c0d0303074800494500d0003d911000e055000100085a9941c1c107000155001c401034640504e02c0d810121506124050820b00600255a405850035800790310816244940340b02d68051202c2600351030080d42401090750340072903241c00c003c03001c590904107002d410710a503038402050382400c5400d4021405010040d10a44030a9840403c3c13201055509000f80e1090307000360014050b40c149600c0084c0006215881502003000a0011100da03941c04508070313400903054074010030f042640e180070040f403d47d1544000c0b11031040509031200c1150130405503200c0c074200b0080801040c02d160314051901035641029000400c0307410140125611100501440703070080c41e00030140d6864000880c90446c031a1184120180c03410302c1000980c1d10a000081 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 149359325 1250 149358075 149358103
    0x6050a03060b0a06260c0c031303020102070b09010c0b04030e1003090b0601110d0305070e030a06140a05060307090504080f030106020a050f010e030a03050a02070b0408040f050306070504170a061508 87
    0xa0301d00d00416250301e6048461444002c2039041c0340c0465550005042601c1403d60910203803039544042700d032003010603483c07840b0407409030203145c00014160b401d4105580c946071f01a150389445a4955480a400100062040342402015018024140c940d00a00d903050072058600080e84400350801012a840041c903882c10440c9181000e42d0700000464218480700c11414040780319241d181c0243c071201c0c400d80ba0b0a4041c85041400c0381442107603000151804200c203181f00c10358480b8030030f40301513a01c01c5440b1501a0b000c1c040c100030030f8006512030741d030284c01040345505040f10034803c82a43e0744203038040e00c0181c0c8003c680710144541803124070341001d14940204282c0c800400c0c40c544070300504190200341580c500000b030311076200d07804984105034056a005040d29262a000c40c258104e80140344223000ca2110104d11800c001034564000c1e00151601400c0c01e140c03c6001c084080f08072190320b0240102d030400d900181060081d40c20700850f4000d800031803410055818a00000004030390 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 149360575 1250 149359325 149359337
    0x71104020405063009070e010801020403120c0507091a01020d02060609010521241012060c0c0f060501180911010f1e030c090618050105030a06050a03060b0a06 70
    0x840341c0d0f105400c50b606880f00c403100c804950034107802c82000403241405480c40e00b454600300301e0354980c049452415100786810b00701d03c990b204c11200d4201c0c010b46c00000d02840c0070040e50508140541c1c3d014040a01c104200d620103a100d10040b000c3e078019400000c801c03144007494007040d40c0c05021008400c070282c07005084500d05100040e040c500c041c42441d010340341c0c0702500d1440a221005d443c0a20a11201b110141860254111900b01c02c07586e130540c114040c80e02298400d904802904111290350a080100c0c480c1501c40900400c99000c45005110894041c0000136100301581c0510b03c0c041c041c0041c0c0d41d8504000c0a0300e038402030342d030084800d02e0020301e803001030b0200400308441d080a103006295018102400d490030b0040c01240031004c185004c041b603140b54190440d944508040d594003001c15560142901d04452003500b003102c5408864060105520850146078001d02c8850046030300c0b5503400c04513132220041e0300140c81d099201e11195145040c101c214a0040510345008 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 149361825 1250 149360575 149360579
    0x6020706080703290301110309100b1002060412030209100f090f120b1b182409041e060e04060e1f05271621030507050102040902040b0711040204 64
    0xd5000e0b00390202241364401d440000b032089034800f5880381c0b4030b244540020594906201c42810382c0c8006170000c00001c20f00b00510600d10b400c00d002406158440d640040102d61107594580041d030020f103586008240d401c1c0028025540d07500020a0010420b0700c81c0340f458101000001d2a012541c1c000241d00034103200d080100f5030304c000c2e50720b46054200200100a88070b12203950035040c00039030400c0794800c011581c02a412801030f51a001490210350300ba880c0b00d20000480901d100e028030b469107075041448440380d1802c140e00710a502d010401460704603c0c000e00210011103405410846010803160208820840c80d880b070001710215450040c0605807089400461409014401103070300d58030f074404640c1012201c0c92030002400034400003030300d03541010f031501d0303503000600c00b20b44c2c2d03d02600400181c00600603040314040d82d000b40342062140219201030f0385a9200000071138082d9400c000005103502507102800281c1008890b90b0307030b40c080500b807450a2142c1000704600c41c42c810401 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 149363075 1250 149361825 149361851
    0x1020309041a06030103210e090402040e0a0804080c0103050606040e0c07060b18091005070e0f010207090c03021914070b06030a02100810080a0f081c0606020706080703 74
    0x1600e030320344400c407408296207511500745120b51550b002070030340100c030101c0003104000812060350078900c107580031500d41e0088910704541440d01481c540b81c12080b0b14010a0140c1020b4002c03461910a0100b00da0410442d0394940080c0e5102e580300a18682240342c83d8000c03583d00d4003c3c940c01c00811181076003004d06010101400c030300050302810b0031000c0090040d081000c50b40008500d068018248200006c0f107007007001c80c00c1001c036441d0025000c0c0005141080c1020f100341409412540c0c0c44110383d03102101481010b40d03e03050b465042d0b03c1a0080024003410601400c52911190760340561209010350042501c24031070f80307102d024080781d00c0c51851140c05200954901c07941000305031030640c4822000c81e08125443c140a50440e0b0242c50000c2d4030350300321594170300440015014555450b80d03040081d4032414089402402c03152103603003080200f0514000b80ca00d80c0c8071181a260100c0c038034034140d001c40761207030b2003000540c00000c800c025158201d0030700d83c1d004825040a100c60400880c0d = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 149364325 1250 149363075 149363077
    0x9070609050f130b030709090b0103030923060a0302070804080106030c080f031603090308030412090902071109070201270308070302040b0a1103040f140306070509130513210305010b0306010203 85
    0x1d03800078655590300005031307542c040000000801810000308176500403418007442d070b03010074042540071640c00b10001515080c00300036040715680030120a541180300c4020094158444005c0c9400c05400740444401f2a440000400c0104400c8000050325880c5140c0561429042d6000c805280c000c1003174207542842c0401215418451980c820b5843c241c0c40c50f041d0388c2c44109401c080c00110f4040200410061a1045090034035065101e0100307160752800e00d001640318232034004102c4c40f07a2032070515403070410b00780d5180c0280b00c0b40004100100004446490703c08a00030030142e03660b1a460420070301d90810301a03070b004403251806600e4181481e0200c440f03845903a40d90320401c42d07a5000411040011701c1036501138004160002c100c0c540d1808107811802d016150b0a220f40240b01c0802e03000c134002c80c00c5a285600c080d0444040307445400c4140010540101480440c0004000100005000d82000252180c4030051480303241d41000300103084980581050324444420014040907a030004 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 149365575 1250 149364325 149364349
    0x4090e01112a070306020703030b0a0510050f090f030607120b010c0c061b050d0e04060b07030c02060d06050d0b150a030b010515090303040609031a31020909070609050f 74
    0xe54884000070320701d5038a03d0001681d0018080b144040356000805925801080b2100001c0f900c3d030760b51030b44440400180c59451510600880c0c003c001d50512034902c940035107078000c0010100071940b01b480012900f810406c99490700000e154054018051000d07204c1c48d04421021320303190100c0e100c2940d03401c10409507401018203214440d00f9031010210b01c040e02c25003a560080542d031060515150240c900e9400d504180d1280d41803c001090400c603401c19610711035003603541c41c004010517400380090f03603003e400d02c084600d898032380108558a681305590310640c480c1c2d002078100c1c90300c422640c802c4104034858911402d100b80c02040070170401c12900b4103440381150311180c0c1e262084c100c042c480c031600484a806000126001800580200d25442242c0c0150a203640c18104a8403011008408035032000400b412142a00f140d1201407419561044200f600304582d034100c0d03000070740c5a800031501ca14640c0e2028105000065010115400a0509950201e000841c01d80043c1b8044451 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 149366825 1250 149365575 149365627
    0x3090b03060906060c0a230708060408040501030c1e020313080a170a0c020d08210708131e0c090b040e1e0a020a06111903170a0b0604090e0111 63
    0x1040310b25824901b44116200e0700c1d800001d808100c0c1c12004004c40d8603400700c25043c1c00d40030b180000030b40400d021410500ca00e9001c0c40c0c041c80d10782800b005400401001e0306e0079041201e0460b9409540d92448500a07015185400071505e40344585403118102140e82c000c40710130b4200401701c100143c4514a400841d44103242016110303c0550800c440d40c52080d01c1c084d60044044400c0390502a80c40010f20110108414403c0d4203c500582c1000708001038a42c0740018a00000044000c9081a851031119105003196003400c95512800114a0301c052000d40302c44c040711804010102c0d461283c0c44141074180c0741448100940e038010b0b6246c44880b1070440e002035182110800220301808403071b105941c0201070b100c41c1a11004024540c0d502c3c400d1001c014440c00085400c1c190510072503803040c0e581699044c1c0a54840414001d8910000d030a16040c56290305100d0400d50301c220150024012610000035001402d54402c1d094441e03030f00f4074904040041018141080c82c0013800c29440b20b032 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 149368075 1250 149366825 149366827
    0xa021c0c0302100f02130b09040c030902030607050d020f030c030a0e010c05040b07080702041415030105040c151e020a05070b040506160f05060a0903080702070602061602030c0706020a03090b0306090606 89
    0xc0300541c140a842203205c50744e162140418042003e400c01c8028149280c0149d0302004503501c0e5100903001c654030044080d44c1039001c0c10000341c03014802d4000349400e550303102c07000d414040c0346001c0c011147c00a40d80c0c00d0030072201004000041100b4400d003440028602c00a00080d030f400381e00079001c1c3c400c1d8080d00d5079542c40003500f041444510411260203a502a0081201c0e12050483c04260002610003a20100100080368030074541401014011500045c00c901c5a9190030103141e0507040c4200e10300244074074040700e042d8250080000503600005a005001e00070081e01e8401c0c142880da0b0032158112005100c140b1075515403001351800f0f1260001c486905c000d450400360700303c05141c00004c0461180004001e00300c503a54002d11566032081d19011140d807154403041c0e8513900030717004410040e444100015503448980c4d0807200c0b58030075401905d18288403242150f007091303c01d400160141c0d001700080410158082c0b1814003c1c0803060343d20b41542000303000240e0642c80907090900c5410 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 149369325 1250 149368075 149368091
    0xc270501120b060a02071e030302030a030b01121109120624010c06090602120c0c0a0201050d091506080d020a0807080304030e090a0504021f052d0a021c0c030210 71
    0x211a501c542e1040310000e100d152121901c0034025510103290040b41000f60f044803444c02c1c41560500d5001c1038a9054001d1400e009160700120000c0c1040c0105504100b960400c5c80400c140d42c0c030079044500f25062005554100c0c610070b10465505560f20000c0e0303580080104030040340c18001201d034408400f501d40380203142101c0100d030000080900030700b01c00d1428090380208200c0394020600341c4541015072009039141e0005940d54006c1e200701040c142c000c140007900541c07207075004207030607030044c00c1c0001d401100d41c03141d140000c019940c80300d066640d007030144004001000a01d81c400c40c20720040141380601e60714005203026101d0001e000000100221b41050b0082c10a02a600c0019100d146c152803d1000b5001070402954203074040d04c158002c0c45142d41991083c00b500b9400c40e1100d81c64a1000321035030482e4440082c0d0121104004035000400038a030384d00502c10301c1c01c41c2d8010402059615003803064941100620014404c0005d107030000a50085a4031748060100100010301300 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 149370575 1250 149369325 149369357
    0xc110c030a0803090312070e0a050108070507020411190e120a05070b0a0203040504020a0e040c08060117061c050f011103100905090a060609020a1715090c1c0c270501 73
    0x40110111b103054608034000304400260b20040c0543c40200403161440201d5544005640b50382041e074503d40050030420104001d401c103900240520802502c800c0d1a0404e1182070b2220020140001400104100301e110083d00c3c1c00c41001c0b11240340c96014181c558000d03902d007035035100300340302d00c01103100b010490090f40b90081c400d07100148405401995218103c80d0001d2000c81c01030b40d518440c0d860100155101c1d44940c2019129a0040c0c407200c8150300c089001c090070401c010701c40c1d5400710a0404207a041f4940c45240b00740180b00d2001401e2070203650524900f074529030707a00d501421005108101681e010041402d04039104030368001100c1d100c49881c02d0400e04500806002c1c0e500386880000c540d00241d0003440b90024554810400c95204c001d01100c40070140d95240e084200751684030321a00d440c070009a0001c0c42c650b080e80c90204c103400704404c100b09020280e601182c3c0e501c0c6040804da0005240c007004140490090381442a000c86500152110300885040140d512000142c00d = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 149371825 1250 149370575 149370577
    0x180e0303070c120c0b01030804050103151401030e010e0a081b060c0f0306010e031c1206030804032405010f031101030b0a1403032b110f040603020f04050d060c110c030a08030903 78
    0xa1700002c01080e1503859081c03441803580b0038411a4002460f003644180070703000745400d91054458500f002101c02661000440241c0362a412410640d580c4401d4440001c1d410444030501c203103c0e00c48aa15010110744204102586660100b02030f04404e0070000e141d000d510454000c20a543c1c201500c80c1c40305001200c14408200b00190144203030310310300d100b40751f8164581004800580d294050144120480401ea400500c002040c4c01070038801800000c4208050035035850740c15401030814550320540e6001e84400ba8018208003007920000d00c00d010058600000c081000e080c00e01100140c5804502c81c1480e5104030101000b8685e40e00c0c255580920480385c143d29288009680d4420714841d1400c00240e21103844109032500da808007023694581c05480540303000c881080d0a162411205038060350000381403840c0d0b42c1c401c000105150f5030340d0840a0006000d1880007842c2ca203150f202400b440d41d006114010b640c01000c081680d07540004261038003c1c1c0c0480448d40b41e80318645040e1035 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 149373075 1250 149371825 149371847
    0x6022509090b0a05180a0807051f0b04050a0212180f01090605010807060206070c030e030a0804030f0515060a05010507170a08070801090516050a110106180e0303070c12 74
    0x1040d081c05040024009030310b9480e40290010310080026803990b00360903501078540c810480380c3e0b802c01140b140225440c0300c064201d65016500752043c445024204c1d1007040282d00460b1080f0341e442e0a40300f52810075200b03295000380c84403021498800c040f2030311098403030000c150006140b00c4585002242d0004d112030080f9015680003400340c07441c0c03441d001014010034010644117100341100050814030000b0540c1c040c2c8a2034640000d1483d80343c8086441c5c0814000458251203a0503101e80000c0000004000442c000e000d03603464101740d454001d080101240f20150711280b4041031299581d21100b2080481e102420300759a55409454103204040c1c083d0b0603215200000700e0511b03002601b060303e291160109507100241c90303803a500b0400855005441d4200000d000404c1460440e00507002000c050100d802c10064121010241d0360942d00b6030780210200c40c0c103024010360a801030f8014083d1000c0000702a42c1140b0f420400100100e40b00c400241441803000d41c0d60300c00c45d0042c3d40403d4 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 149374325 1250 149373075 149373089
    0x80c220b0d020d0b0603010b032703070609150b0102032d1305030d031b0311120901060801060b0c060c03040305070c0609050f060a0f050903100f0c0e0109060225 71
    0x7844400d0103003680d0081d0000c4840c3c645036400c1018000140c94050112416a1120003405027151203216403c521314480c400606491074111200f9115035002304090300d0b0741c41c40360001054030141b5160501440700c007028280c0138107041015140003030307030007100740c40c0146200c242805400868492000408050308444094400300054502096070600c0901e02581c40c243c0c00c503074142680070401c40444040210641081c0c02c1d030b00c15034100a01c01d030014480482c00c00140da080c1a075208100c0041c000079108580c09a40d240c03000c03c54108203028060003000d690501d03174201201808031a484641c014101d030071070900080010209400740c4103449550790003454a11115860307003006481d00d8071030b0150521031246100451901d00e00700c002c0318006101e03030b5aa2030348401e424106070750319080030a00710b41c14050420341d04d007009403a00c0741e00807a4a4425002c65210181c0c40080c2000d4141140305041100c010f000740041c0d82c0000ba0032140104005068040c0092030550f46110306890304002 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 149375575 1250 149374325 149374327
    0x110d1e18080d020606030304030803011401030608010c0315050a0e0a15080304120302011815050402011b0c1403030307050a050d02040f0e070810081509070504050708010305010606080c220b 83
    0x8103032004000b410081240d0903408641e00ca880b09420145d80c1d02661100410460302000140006c03464042540b15075181814040354030303501c501e000c0c0e080d202500a10000030341c1d1000515a250a40e982d004010705040e542d1039981d605140021801074002084050700a03212011062014000000d81c0001d0080e00140e948a50701d60b58001307034003055a5000e40041d800e2a02007014a8860b098010351190b02944601d8035114403882000a004003c00503070501250400c080107541c1441d4203051a680b00b010440540c0b0b081012480003000c100301d00324002e5200b80104943e0640240c100d6020440328240141c60303443c20381c85400680305039042001c5900c02e000000805280c50f00c0d940340a10030340e844070901c0c2d950f40008036004032950312580c000750f405003410000c1000c0c020070440d040645103041d00e4002c2c1e01d440104040e1101501c45800103610500100700744a000c1c4a0b8134094215840c28400900b000c1e11030f10268014114100281d003144c4284940031307030701000300c14006c2a00c0300c003c1d = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 149376825 1250 149375575 149375579
    0x608040c230f0d02030a0309081501230f15090102010e06060105070f08040b1c0b0301111e04090603140613050601060f031407020f15090706050f0403060e030a110d1e18 74
    0x510843ea242724a200d18481c42d054074510750440ca0819050360b40c80f401c00002c422401c104240040e82041005801c900003c0d800304680c0c0324481d2300c1e0300d901501d4583c6943c4400b010002401c448806410340d070310750090700c1444196039004040310f00030b54001003100681401424072000be8450b0364450302914800052052981c21000e0800f00b618505401c20008880007100345030031798668145030701600b4000c020708080e00080d030700b9010b01c40024001c92800c00e03032960310391000c072085a041034444998100400350700b014100540c662240150010040d01301c3c4682d99250b07181418062035040c0a401002e41000720f109600c5900b007040c0740301a4200c0790030320203000303512500c6081e10f01c6524010b04120002201814000c6405a1448402000c00e1485d021044405402091081d103400404010001c0840c50b180a030641198007035000d0755403540c031002c014000390503aa203201c0f0307150025200c02030070035003082a108458201592940580028090456405440961520000c00c3c11a00 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 149378075 1250 149376825 149376827
    0xb06030f0a0b0402040606020a0f1209091a040506011b0b040201030e0d0c0c080f030f031503120a2309040f180312050f06130b0402130608040c230f0d02030a03 70
    0x11030b50243d030080e0782c00c010864071450101c3c1c0740e160586000c0d000e0960990514000703000f100c21501000c00c28640684480d45920f1480c0c181d0301300301e05074118070044105d040c0a03468903114054016109091020300e00318001e42c440703103112140d84094510403100c4001020359020ba00130507400c160000950b0b91a420503a03000d410144000f4003540e2000b10f1003004243d20304006100c1e148804500011801c04403001d40901e4150f200800c10070400c0180501340116071030421044404903c0b904410707444640d9050018070a0f41c030300c0ca902c5c0d902409070845100034a05101100d001003020340740070030704804020035800a40322003524031001407070000c0d8807800d02da80030710f1201c2d205805041c10701c6182c80c0c2809130900c052050f50b01e0790b84108140800d031405030403a800709420042c081c00c00b6040043c64030a0117200000c0364080300100701060300b0481003184030380c0039202401404c840c0200780048503003807200518100e41800d014002c21450440c0c00d50303031085140181070707004080300c00c00f0401e4a4 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 149379325 1250 149378075 149378093
    0x30c030509150c01020c07170a0b06030f011d0d0201020403083a09030e090402010f0f09080d0503010303021501031203090614011e090c020d050a0e1009080d050f04030b06030f0a 78
    0x46c80200b8010702e03502040456000d02c0c110400c4011030002e104082c400d44500c00c1c040d00142409902d403085091400e045082070061500c03415411008000d200c0710301400c0d2341880c41c0400100f0131a40304003c1800001c6c810340541d42407131403003941e2111401c6008a0f9203000b941a011580000d406103c0503084040c0c02d421000840c1d100c1c6d0359095002c001d450611103100c4040d01d00a010640300b05244003143d20900c03044080b05140d103000c5800c2c6aa0b42d0740380713081043c10014040068800001402490780402c00302c42d040701b9418a400c500d61442d00c81c20210810054100304140d00e48603240c0030310487c1d40190001c1d03581b44030400041d5035144000075607030002810758111100d82071000102d14020744240c1403400b0719a0050122104400e00848040e03000400000900c5415014a003058464403101c0c0a40070040d101c2a0b88103040100a61a0a07034100d004c4e0100300f401c00c1400b100c4807a0074142c034101c0e030748180403e00c2c1b070322041c0010b810080001c0380403981e407040b20464000c0c005048 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 149380575 1250 149379325 149379337
    0x901020c0405010509010603020306011b20060c120c0f1203010611030c0303010902091804030e04060b0a200102070f0f021e03061323100c0507030c030509150c0102 72
    0x6000c603240951035006100c16607a003445415401860320004101882c000d80007580d00080514100f400e404030700c04140c40c0101c03901c0050740d03047d01580caa104001d0707520302541413509048400c6824080306211496541100c03400007007000c00c002c688480002c2041003400160b00908094030308006203a003c80d05913030001d1284400180b141a01111400c4020046072401c40c48800034501e1603080c10000006503020b507a400340c04c102c01c03180c0c044a0f03c020500c034a01451180e698406e002c242d0f6000c000c00d0b540d03640c10510785043d0401510407443d401c002065200c1c03440300219000781c21414185802402034880152a105034141c5100400080a645a00b501d00c00c07070f4200c4180f00303805e0500c201d488501640c40c0d095440140800e44140703203966201050781c440c0d51000000002c401e4245030380745105140a002d540414051500d087c0ea03806008111105450f02e642020b01a071801440001d02400c00750501c0000250901c80c2c3d2280202d03100050301000440d541d66000c606418001e40c480 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 149381825 1250 149380575 149380577
    0x907030b0a023a06090f0f0e03030403081302090c0c061f170109050d09090606020c18040c150c03021009020303090d080c072d0513020f0c01090309080d09030c0b030606090d06020901 80
    0x200c01d80b12080e11441000f48c41036075400290704503074495170240e032142c00103440703441c900048851400050b071f10b401d0998070500b07a44034029203802701d11550500d07248014110404060717109080103030102c1c4040f040c40445403000e10f9030545403095024103004103407036113000c0d049002e2010241e4045400080c0c010444401c0c05c01003101c10342d101c0040b42c03181c0101100942c009040104000001c201c68141a0014001d103420b106a694403144079111161184800f0049030b0f0340b0044905151b01440b0030b4521207070424060180e15050340c0001d4403072080001e5a40b090303030113210600c14403180f0812b5880f00c112042c21103580c0c6031500c0c02e02202861801c8003407104044032044815601ca90140c40040300c00c0074102044000c421302c00580a504031209481a0000600c40300c0e401e038400f4001c101c1c00034003a4580d072130001d04201c030b8142071078003e856100620a03240d604000140303642100004072001942100e4498039140c0006007030344202118181d00581c03828000081c0045940240684032003 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 149383075 1250 149381825 149381831
    0x3071202220815070203180111060108010f0608060402090c160c030809040528020d0209031b180106080a050a110a090602010c021902061e030907030b0a023a06090f 72
    0x412204600f50380c04440e030700016041800a215180c50301801d001121605041c00101d20300b019040760700d81007003680301c00c2050b910b9160314081d07a80940b14480107081030602901c1c851603d50007044c0414000350032725002c0d25000400441c02c4000d600e160165070f610040c91001c07242c5e2803c2005181d00700c1031007188100c1c98440800c031320300308190486d07410743c0c4070350884c80300100e51401d03140c025001400704400c415001c000c10001580c060042c405016580727021900b5140f007410501212000030400351040a9401c4018007010340c200c441250700900c54400441c00e5035803480290042c1c110101c40d41e01000740420000c00c02600440c079001079445030341c02040420210907040380d032050040c49a1000c5c60721506c0940150414034000c00002d0001d4602d030143c6071100030742200750340c001c0b03620400d507810000091081100101c512a0015260300342581003400d010302588045204640e07211103018441d10146a1641142d201891190005400c010300760780d96200ea0090a001410382c0740f0249 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 149384325 1250 149383075 149383093
    0x3402010e060301060e0d0204020d0c091403010b0a030b1f08010f050906102309091f0204030b06040504050c1002031818040323042c010b030712022208 66
    0x806000b030703904a0703103e0754680c000301141c5801c1c4030000399034107400d0f80c125808205014481d981c0d4083c0d55004003d651b5103403041c034900700c00310841207026010071f40310380d040c40b5079090300796246181041a690800405001d50700c038081c0d0910103000098508a4a428403880024080010f42c000c225100c4588002d0155a695800040c0c0740c00081700c1c3c030f91410455003800d0080c1844040303c0222101659001942d80384101c0000d0100e0710b049601c2c0c0c005a1024400c00b030040e40700700e441070009007484400d600345401d555421400100041c0482c4c01a5610301c009024044200406144c084000d0b0182100284410000307440381d01c4641c1c0d11058551416200c5840c2c1840e41c043d44043c03400d462440d1aa4681d65030860b07400b1111400e6203111200c051888020542840040c0020240b580c84880c0da144461034403c41c01107800b21036201310024200400030002d0ac84100d0368001050b01c6c00c07a009044015074540240507030083c0700e24102e00000956210480f242c20300040c1c1d282581101c0b1201 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 149385575 1250 149384325 149384329
    0x30609231305060c0906070c0f03170a08180c0d060e010606080912030603071e030c08010b012703200108010519090c0c061e0e1603083402010e 63
    0x101d0080c2000308181d0004000450b00960800601034480d0f00602083c5801d11644600e80700b10420382000410a03003071003040082013080407414003042d4000464605006803e000641424401400321207050907221a44100740810f00c0042d000c52402030100c0000400707030620400511b103400d403c11081d0b10740100480c08600a0a540d441546d617a4014040240760500340080c640028100c0354251051850100342080e52400081022041c1480e0804191840c2005115441654840c04150345410b403000c2c0140d07484100a0b125809507010040c0e201125007240e00c02d000b181e40058032100004451700b0204027000c1910b2401e040036a580300060340c070f0304100003411280d010104440b81c00d5020800210000747c02c03481003140307103080c4690b0540f403c3e1140c000f80c0c0c941010341c080d1002c0300c00a6840c00e0b4035a20071942c101008800070070b802807a01b0040c0e907103440580070240c0101c001080a085028209038110341c5e00c031071a070103504005501a0a201c0c00046100201e0101d02100b090450034 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 149386825 1250 149385575 149385601
    0x103031805030a14030f071103100b0603070c0c081b132d0f020309011508070b0f160503040609090c140921190b06030109050c0105030703060923 64
    0x24075402000741180803126a2009084281c40c4030104543c0030a201000040c09958003070504170f801040b0102d1256902c10426040602d00000080403601c4c1600700482503c40d0ba040e29484080c0c2c2c10020390407402801c0249421006030b210446911410b00100e501c0b10f15030007611340003107040e105900d18a9210510304191800c00b030b403181000c4403500164001030a00c020300d4801103046940000c01d030f20f541803490103a9204640c02e0100b6911070240a10343c0f55403128910007007413008003804c07200d801c088a00d0361a02c81c200c90140f0508022416011005000b44103c034a030744c2c4401100d949640e01c01f00580700a80903c11a0b0074549000311001101307000c1c82000c8550f04082c5101c900e0b0003196010003000c9040301c290300400440f034985030b100442e001c000c0b461102e0b940d80404007005000703191280742e59000921f032034041c0e418842c8078000200700041140c030400007402e1450710b035980c03050114001c05040c3d0101003c5401d00802241107940c4031038000d4410035812a8544a54074010800305c0 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 149388075 1250 149386825 149386829
    0x120b010812090d0c210b070806030d0507050c0607050f0708070f06110c040e0609010e0a0c0603050c070c03060501050112020a0e220e0304051f020a0213020705100501030318 76
    0x403108000540c410b00e445914299070364412404025441c0c0c841c0c41d800c1d01c40709404240403640c01c098150700144031106c1102a40440f071882c0540c6145001400310f0340340c3c0940c28440050080100b0340c01c00b004070510800c024804064611900d48041e410704036615041e4180c003202038002c110004c1021080480c840701139503e50340a0340b820f1392400004462004c18041a494240100c84805206a131203001700040218050014140c504040500f1801c441940342403c12903800044044001070008014034102da01078103000805607900d58035420f25108810380103244c48101000031042010941c02070b8141c030021380e81e201c00c40704500078035000c81c0309680d41d20f0080b42510103004c0307440c60807220a03228001c070710140e80c0d444030074031002200f518000e034040e00803078201040521039030818616000c00e03440c00c0499039034412802c1c9000307900c0b00002d000280c0a81d4003403000c0c0c9a000078540499050950003000c90345402419100b44004210070302040340058100d442c109404080c83c104902 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 149389325 1250 149388075 149388103
    0xd030606140a080a0f0504050c0a05010e0f0609150a0807020106050609011e05040513051f0f060503092802010e03070605270904150e03030f0402010e040b0901120b0108 74
    0x450720301000303429030f600c001c01000311204a48801c100b0b48205410701841c2c0c0150f00c02c000500c1d0b06102d030010081101d40c9608074504010090820369010340d2101c0410400c81d005031207056960408201081e03001e0350592020710114000915201c58607400100540f1a90169000f080380310786038000c20005204220318a40020543d040310600800c20711203040c441681800c05521381541c03a8045114440d03000350041000e0317618000c00007082e04010b24000000b044d4049000b0003030419291a43e075108500604040040100000701040c10800004c1840100c0c0060022079011505a10a000d550b2801c01c17400106010003a138150b041c00980b1405949140d1916820000d507540041c040c5918a4058821240f03102c101c070310f00b502c03000318250013140652044444071264420020a507604108642d055074010010042004a14096681c00590918000c111585042c0005000d010007291841d403003601e4500008114014051a4245508ca801d6142d043c0c1c0e40d4030110b03a141c014100703402d5 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 149390575 1250 149389325 149389327
    0x15070c0e040c0b04230316080a03180b1e0403060f02032d1f0504051005120f07030b0711010c020c040c03020313170d1803030e0303150103050a0f0207050d03060614 72
    0x510404c0b0f030b030f0103d15000e52015081f07540840407540c22054000565020f00c1d1140c004d40d280b6130625602c0111403810140784510015054a0001e080b0070074403401d090740c185540080214840300b00310204540c002d46e04203400307204006003920036800070f41c01502c1d440e42100c07802c1c4200c01452840140c00610030030b880c01e50b4080d80c1e1032540c800a6582102c42d60031101c600f980012683e0350303031441160700428205120070409401d0206000500e800044070119a07803100081680d203c1001600009a83d07101800d031001d82c6444a0540e00c0e400040c03880c40c519401d00808020050380010812040d220441e800d020300c0600840690407444181c0e00521700ca0030000c60500420600c0c41101c0744002012421481d22682d01c00c1901161a8414034010301c84144640c441815410300409468a00d680055807035400c08e41c0708070500f04850a070365414941c4900004048802c0c0c0e90041d040002444029552030740249002d075211040214404e001c00e1030141c02046052161402c1c844a102c4601c4079 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 149391825 1250 149390575 149390609
    0xc1804020108040b09010902060f040303020601060513091508010c0216050d020f040507020f1c080a020307170a0f09031709010903050304060908090a03030206040b070206070504030215070c0e040c0b04 88
    0x4d41001000030001d88140d03407107040031401038840b400184921120307400803945407821460000d0900c481a4820130030040b041c84034400741361766611510201d510111002402400460280f030700140c0983c032280c4036510b4008903007031464000c100c01c50303220b1030030600c00c02150305c8100701300743d00c543c215000c0c0d0401710b91300c4403040c0c80c181075108030380110050040707440c07084855040c280703000311f190b01d0b01c2400080c90100f9116981c21480280e080b4810000540c1145054040203011400c9111040c281c503e200003c1148034040b0f5104000003103c0c1c0905000c030b440a810054203811086024000001c03a030000500904018414041c0d03403581695a81d2650b01c0b5511100041e102c14071054500c02e60030441e1103c25038403088034030021446038014100b00d241500700450080c80c002e010070150b4120368100b22115078028100d070152036044815060000c6c205441e00a240141d90380140088641000444c019170a081c0c031501c5140705140c41d0703503a0f80e10307500c0c0d030740c031500a900c070311884041d865101d = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 149393075 1250 149391825 149391833
    0x10605040b03041a010305070305010e06250c200108060f01020a02130e0d0c060b0103090201021e030408030f070215070b0604110c0105010320190603021b0303090c180402010804 78
    0x1c0da00320740075100500040c5051903440c44d048000380e1040722158072038201003003041400c0c001d180c2040c3c3d264000c2d08061402d881d100d80541400340600300c2c41e0500c1002941c003103000d00c84448400c3d810480600a02410f1001ea00c02e100c60500c0450105200c000003c5252800c441d42100000060740501480341a0b5070900462402070682d52a4407600c45003a0301d030310f030030402441c1d040e409180c2c3c40300c100c5442c0f800d04900b114850800030b4101030510440c600940d800040d0903030050107501e22415810039640242d4118003c64101440f070340400074105c20704c1501c46010b803001c1d50003101c050f5002e89241ca68940c80f4424420014821403000f00020042d04e820340c8054420205841c002d460604030b02d5070395003166000d820403584540300388919401280300c0c01d100595183c0580c1e5005a4002d00f01000026001034070030a41015000035528041c4100301092036020240768040b00c0d05c0342401c0b0000c5840c0c009040c0d003c0d00807005100f0302c204040000040d0ba000f02c3d0117841e01c035000d48941e25 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 149394325 1250 149393075 149393077
    0x408070305031023090a09050604170c01020309070806010f08070b0d0e0d02010f0b040b0a09020702010905090103050d1d0d120212070807021807120506010c1205030a0b0108010605040b 81
    0x1c4010000100d100c070000d421600c80c12001300c0d81804060f031001560300f00c000c0044a01c00a000350a105d45402c500381c4c009200048c3c060380150304020895182c0b201c254082d4005d104a10040070039500100a100a84c400000c1c64001d64610743d043d540d20b03a803650b21070118016144503583c141d80c4202001c10005041c00f0062500440c2c9031408a40b040302c00c0e8450349080503d0750f5a20040c0e56540c141c5078403400700d210349043c0c484111024400d0300602400640a00002c2c0114000300b580020700604581c00380e05528010075020301722900941e0b69052150700d80f03869000d80782c08145101070a400f42c44501d5210b1401c0c640060110010700c040d078482e262201d000c21056000e41c41060304000c0030b404050082c0680610400e9425a1031030584144101c28140c50241a100341e0322500b4070600036040321112034001d880d03400c009190340e5807a004075815001da55014201250580743d00d820941e02034000c40c414415407605010303071b03810f00c401119100c0c0f09100d0003000a2080c401803212400d80f40c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 149395575 1250 149394325 149394331
    0xd05041202010e210105070e0130092303210414100c09080d02060106080a090b010306022d03011203020c060a09050307060503132907030e0c09040807030503 69
    0x315102c43c1d010700380d07408141000584845040800c050305440c0ea180d01090040c0e5a10001343e00d4051500d0014100113410601c0541003d00007812a4145805080d8030644140100100c50350a200b0000a414041451581001c001890001803041d44458100c00012030b401480100c450005c038940060713601c107040740040d100f04e5943c024074101035190741d402c00048040140024002556590240d00500041420380c0041d8442d0444140c00c3c0945402180c3d060440e4464244901e01d80e546807041c100819a111005140f1810b910001c024040c0940c0a04060b28a000a0b04020f82c500c03114490207000e44a00038861040410040c0400d0358090a2505040d1080c011a6048100900000c1d420741007940224005002c840d030402030f910b020802c040007800c240c10000e14601741844640715a00d540200544142040c0e62040d504580d658450720b4544491048103400381003044004000d0840a500c40301148206203150085240444405020f80d600015492a0180030355064809070002 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 149396825 1250 149395575 149395577
    0x5030f011d160c020a0e010f0e01030506010e071106040f030813021003111b10060e01060903020f011119050105420d06050901050a06080a15020417010b03010506030d0504120201 78
    0x443c0220058581401107005030000c4030510407190b0400e1040c29240b842a80150b840c1030801004001260703001c1040c0d419151102d01c3d2a0070b0761f41e4240251b40601408112000c07512400b0108014050b904400348141da101e591040115103c6024402e0f28010300d286c086c1d48420aa000c0840d0a1b0095100c4c072400c00301e403864541000305c200590030716004051965000c6411401c109020325015200740e2010f888508100b011950400800500c450500c0c000240a180a402800b11680c0110440d03c44820360004407900d00340034111111210a0072013040301c8960034440071a00300c9148242848081d00e481c20901030007602e180440da00b003240b100340c2c100c1502490100c11000e0712000e180c00c030003602400000c00d41d410038002181c00c640c2e00802d410009450101d040c840b88402140140ca080d0f0071040164030580481d000600034031541d40038091000c2c004d00340021043d410f400400703168901b100200403d07a104000d1686134043c50a04d10001601000140080b10b81d071905102c00b5401 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 149398075 1250 149396825 149396837
    0xf0c03090f0603090203060718030b0a0207210201110a0c02040213080304080f0601240f030b030105101805060d120c0b0a241512091205030f011d16 65
    0x248404115050381e50350031040000740c640008005604081202c40d80055040c50107070751254102100754280000d03408020100f040040114080180c20740580e1641740e00b180c41480b0b0407803010410754070649155a640095401d06070000c0364034140000f50340010303c640c2c550740520b20b2558208002544000f000c42d503540307282c1202045092040000c0c0000c3e0003890020708410480c0880d1340d2a04405034060345d031400c0404001c0c46404806202c80c1c945600600349034004003290101540606036892001c2d406610b00b90420031010b1440319104d088490141c004c0d00410010040e400c02c2d107a080390840d811000907040320b00045c5202c0040b191144040c40c000694140a642d266910a01611000c00b1151601e942006490704c90085140f20b8a07000d4040880314680002c0004440c007425160301803210840c00740524404580000c0c0101354081c4c40c09511020fa141d000c1c2140c0c000350761080348030740201d0000c01c43e242c10304603903600502e0801c0c1e00c115030756510000a41c2c00407a40d28003810811 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 149399325 1250 149398075 149398079
    0xf04060902030709030308090111040e040515040507061211040311011b08030f071b0803221a0106020a0f0204090822030b060409080315030a020a090203010e060607030f0c0309 77
    0x140c03440a14096400c0e0340e1004e0300305165040040980b040030386040d00c0e503490412029000c00540701107400303d805100125046a0b203504007107050080601072019200014410407080010101b00041603030344a80342c100f510006083c65804580d0315446070131040000300020f00100f8080e007240007400c001403400c1c0440704110b481c007002d0702503090030465010b40c000c410f100441a40f850010707404026460b11400e0a200c0d009094a1607440c50000f400c080d80001c041800402c45111456101d500045400002020341c58030510300300001c0c1800941c070740741d0300011074040e00c0420418445a0000b215140111480d003c01c0b004104a400407920500200b00072051514201e5010032410512903c048505203141032103681c4110080100d40310314034091100c400a003034541540d030019083c024403821424000b021900d4910080c0f00a9800303015480c000855030696002103040e21040c1014401e1500c420040c0029030280c5040180403404004054189c81d10401158940714000d2a00c441a10b0b = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 149400575 1250 149399325 149399339
    0xf09080705060d092a170a110a050a0303020a05240c220b0a0906020c011b0f0f050622020d060b150d021201050a0e070f050c061302012c0f0406 63
    0x2140075640c141800740f442e5009540c080c2c00100013086500400000601030f845800e0300c0b0349260b40c0040006001380d031030234026203460b1510405400c01510a003410754690170007a541c1c62101104591511414048101c0c4041c1140500005074000710901110b4803042394440f070b0b6422200c100010081303420f40702e40e04400c04034120401031040441040c1da0b602d0790f11000b40401000e800c16815075002401c4852540d0340a9003481c0054491000701c205c004141c07510022007840c4103006494214005013050900402140960050005020203010a4140c0840b1a4240c40ea200e0103540300130f6441d00c1c6004142d080d0020b1001c000014860b610b00ca10481d4100201c0e0410001204402e90101c1c2015040044028441c090801121103000f8240741c2501400c5042c1c00801c1e02e0200401d0320403401080d070086050b40e1640324040c00740d5005160a0180700c500880c0d10a00740e00049503210003030f001121404407899502d11000440c52a48041410300011045c000b01040c1c0041d030300c1100003802 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 149401825 1250 149400575 149400593
    0xf1409041e050a0608030301090b1924020c030309060306030c1503070e040204050d02040c0912060b210d1103040905150301110a020a022e08070f09080705060d09 71
    0x11159000c1c18030054050785150504585008108100d81894241c0500001c2000000d50781110031000010035210252401b095800004006010810b007d41d400800d612000c400352842c0b54810011032483c0c07490107041240d441c0d94180f00c054143c1c01c100a40105400c0000043d82e0001c0301604031203900105c680407c80e40410075251110b448004414040c040794044c0303165603e0300d000c940c207505050800d40024a0f0088031240280b1859440600e000800d0091070030350010291902003400040c0c050422030060a000214144100c0c90300b8003c0f01000c006000500074181f0910040054408140054408010054015155110074000020500c000d801042e208000d9040e64183d03c5101b24281070a580d141240341d0400c6030f090000044840d030000d54242d8031034040782d80528055802d41184903440150100d0800a080e18401925050300401e040340514410356888416401c0d9047c11556922207000f05c0d0803035002244200315528012010741142281e20000044c4410315035118440 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 149403075 1250 149401825 149401841
    0x405031c0e0307030803131a01120b010e010e0a0e0106050d0c1a1905030705191e09080a0201030905010f050103050d02190b070f020c03030412020a090603030f140904 73
    0x5654606040e1040395034000c03010040104203a00400c501c0e07081d039560f4441c0d40001460900b20030320140b40c001c2803220911055207881100c1082083c1543c42c0e55002d418603002e448191034540420b0b000180d0b42100c40d40442c12240c03e40080102901c83d01c000501600140000d440f00390340300d09000c0340c41d0740d07802e00720321540303104400c51000140b801410b2444142c141900118511007400000c0d00484003512602142da070910f805a0b8943d10140290380d20700840481e40300c04103a218a54002d81e4000c80b0100c64a0101c030b000c1030311031008100440b059100ea014000890300035011180c0154020b801c40d003a0781d8400c00000c20045030040300300080729400d910958840c1c6c04500c50401c0e8170b805002c05164803900f54032401708040503840c0c00c030580c1d4000c0d10386803c204d05640500350b180d20a1101284040c001030640380e4035a41c841c0742100d40403003404160b00c203451070400003d50800a12808088030b0303141d06c4418000640c00010f0710368032400713003402c601c00c170007000300c81c04c9a0745c0c1d0b201d0703444 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 149404325 1250 149403075 149403103
    0xe161b060c0e0306090a050c01180b040603091e11040f0b061303120c111e040e06090c030f10020f130902030a050601020c091f09020f0a0f08070c020411040503 70
    0xb80024010101450110040c000c040603030445524103010400104030040e40d28400c0c20041c003080e4040728070a0032062540d100414220001c40c000c1116545500040300c2d490141c10525484000c40c0100c642500d02d44000401103000391540810504164020500140502c48005180740305680450030f907610058100e00c0740650004d040c020003c00710540d40300c10101d441e2030743c2c03203120075a03c40741d400c0005119240300d03c014950300b040c040c0b140521000040c0025100303204901454007034660b124410b6604042034002c3c4034030341c403a42c280005c0768282e1030f0b081d8000741103011408140c20b00941c401030301181400001c024400d04200c88500e100b00800b90741c0741c01640d81c90000035503400c6480143c64641150400c4040240c0c540d07a80c00c0b85030b00040030400c10788178126106482c0e05203210940c4800c01d414004030b010103912280b08081c2c002d40e00580c0300c940c0d07610785440d011952514101c1c0e820002c24200548500035090a03409000300d15a148005860640c9800c00203203010590744000c9 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 149405575 1250 149404325 149404337
    0xf0e0907090626010f032604050d06020706020a020a020f1c120207081203040302010f0908090909030d06030c141009140613030501050718080c0607060212100801060e161b060c 77
    0x308000f01001c0070420400100e50074184800402c1c2c280c00e9a11841c2700b980c0c4265036205440043c8a010f604071448164000c0381150340c0d0b6403009010303440d1042d01ea01a881000c03008a803110354149000b60b81c51070003071240c1d400c80903070082d0740f0300c0107009241c10310030218443d0700000310700b01c5410006003940c805040c0760076450b80303014a00242510000510590500c2c07c003600b01000425010a40f005140704485407446035440f80512459401400b10b007802503414200e0000030300c403080c400755043d107076211079070504a02c0031000d0069411655007400b002605401041000c01004140110b0090b40104003a03c0c00c041c2c0e4856600014070381d0001c1e120f0781d5580050000c02508010b00c4818004100c41c028007907803820742071036152052112114042c2200050306020008540d040b03030100da10406210045080c0b190038000c50310500e0191501b250b1800201060517a401a1134610441c003080c420f14004040580440c0c103001ca5100c540e0000406405002c00a0003500500f5050601e5036148 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 149406825 1250 149405575 149405579
    0x801271a10170d05090904030c08030a0b0a05190515090402030a020c0c0109080d050d150e0711010203101202010309060507030209030c270606040e01060f0e0907090626010f 76
    0x440102103007800b0148050340446001c040c55030300301050390184c1800300c0301c882843c5d0703030380c01d0603a20745560400c020f106100010420003025581e5020516403d0140c0714114440e4640091000c40790310b001c4003d8500d00b9540c030030092840c0c9a6070300356650324141d00150500b00d02c0008242680c2003664a0014244c011074203100d41a820030805d490601c00746000c204451502c41c015407988002e09002c01004000140007010040c25005600c1122026051a021a5885d00c0c50320f0300d5003042d1641c1c4000341050040c0c40540a050003580c4c0111120321a148500346404003900e80400e80d02c00c12814542c840500300b001c10a01d108113889800240ca0140c0e031150200101410a810601041d100c0c1513051722203141d21500305074000c1030380020880003c0c540c40381c60004a45020360340c4030925111603080045821a40140c24186003026621180c1ca500407860400241c501c0484c6c0790000900e500340200504d611801d802803030610040c1450007051100fa5055401d05800d0300446c800c225040704c1 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 149408075 1250 149406825 149406839
    0xc040504050c03071e051e0409050705040f060c062a020609030f040504050c09030d0c02011d100c0606090c0810140105071407050901090b09010801271a10 68
    0x6031070b600110b40c00d09545946816100030745202c160704541a483d80001010081d0580680c0072941c01899000002c0c00d480145000f0380e1490707010303000382407070541003001084000d170160003660241d4002503030b8803d1580c20301a044810381101081078401d10340700c00039100c00200072582170901e01d10780328860901e110039003c040c2c98180058400c450765841000101c15410703c107002c5e01c081d90000c8402040686a40d00c520070a030040106442d0f00d03005145682d200c00d03410403450240c082c402c0c2ca0308500c01e03141c0c2c02d08219906112904030780008440c80c0700345625110b5a5024002449008009052a103800d4810308450b4204060408100c0e0701d028802e2a0100e05c0403c402020b03075414020101054600080403802194001840e10485210000e4200020320500014000141c2042d541e903035140b5101c3c010301400c01040c0c0c0192107100000c10041018000c1c0000303030024070070041c1050190310442441c00036402c41614130121016460011407144a016800781c0d022540018240b814010 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 149409325 1250 149408075 149408081
    0xb040204060608100501080402150c061906050d0b0a09050304080c150703022d011401050f0a0302030601140607020612100603090c0303052a01290d060c0203120c040504 74
    0x66014030403074104104c40d8081a05400c801e980c1c0030f280900254403070748046294a41d01842100046070003007030580d9171044c0094200d108201410099864904088040d003c80e0194001c89400400420402c00483c02c11289250000c501c81000995a040e54440c40e0564019810a40d2b403034101b10024040c52a01055555006100c41c603500e01c0c1405030340e000f0350345034842100341daa090200c1c0340c556005429144032200340c1e04070600900c90801d02042c40401001d09000d410701c6003804034502201400e120120303605483e400740c0204032036400d00148001ea2a081752401740d10910401541d401611920050701c0c880c61166440b00043c00c0c09004107480c1181a04110101882d20041801041d6800c407903808407a01400c00c2d0341d4806807a085100c81d8a142c1340031030140034031000f080b2400801544042142000b00308210310180f4000125840c12201e01d04065010350100062070206030140c0c4940380c01006e50040f070340b601070901402c4103018003c485070005540041020041800c143c0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 149410575 1250 149409325 149409329
    0xc160507031b090621021302210f0412030f020403140109020901081902130f090c090c05040501120c1b060e01050a0c0c0b0a060810021308070602031206010207120b04020406 76
    0x7440c1408134600b4081407400c0041c0901199140318902d4400c6825911191074640e543c40210f08150743d40e0801214003c800c6017084c9068805407a0480040c140c1d105442d00c0c030b800703664000031003003001d031160404401801c41d00c20080683c583c02c000020010358168550b015602c603840020070401610300401440f501d050703102140980128640d4040b80d0200c021202032a0760407102d84054030307080134140d801061804c0c4451a0617140c14208014007950b1030f0303900d003103490031034050100f0345052000700e48502072403042c40c0c0424107c125010a81c1e806402c441401c0c941854002c0954081e0904401c1c07030f44101c10207031a00c55644c401d0f410603e10070f0080c5540410740f0b4006000100841a0003015021250070140c00c007408040400d0034000c25400c0304008100704000c5038440103100921100a6209110019115102020004510303c0110304c010441c3e42e1900554100002c07000300285801c0020700081c11401441004100405828031610115000c2c0165444501c0c184c0f041c002260700e55 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 149411825 1250 149410575 149410589
    0xa080108070f06050f130e0c0c100e0c0909240702012016050114090d11060103030905090c04150e030d0e06041a0f030c030402180f0c160507031b 64
    0x3142042c0001d0f40c20800b00c1321707078103030464489644820b2000c0070320821300281c02c0800c524040b80f051103440c1d4a0300005d40584080d880036202c844031104481070846410800c00301190f005091411000e2030485400d40c2d20541d11402d440700c0130100080589408910042104940a150f040c05405a424030609071903041c400503c0103e44940d180a0310300340a10b21403440b000070030860a01c1000070a401c810851240d01c101a0f140741005006161901c04014a40d030002c1d114001c07007103401800040c2c140c1241c0c0c01da25400441030400c03090148078a0014144c03001410208800500d91507a16881780301c013021a80c07141c843d030707040908150501c803070390030183d04003d00f00217008000e41d15035044400b207a18071818880e451210740840c3c1c00c2030013000c00b40e15102d8004020403038000c2c1d0030801180302ea8401c40c1e91100c220182141c0041c660350a6501c011511202c1c0c0c0003035441442500101080348001d1820154500780713560b41c0c1c1c600404c41d001220740400d42c0404030070314403d40c07000d00058801 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 149413075 1250 149411825 149411849
    0x102303100c02161a070213050708011409040b0a020708130f0905160806010e0f0402040b03010503010b09010b03040b07090509070306060806040c020a060b040b090406021309090b070e12030a08010807 87
    0x140406203298140c422041321543d01000a20708115501ca80c960640088040b10030700403491b040001510350341c000d200d0800e00d0442c0f6903900000e80350035602c03d40714079408004036100c1c0d1111702e0500c009400c14401190445400c120800601c1d4446012000810010091420700c0f0b05060b1200250345024010f00400b0120180d245549a00690b440745d0040d002e10302880c0200240300040c0b444503000b2103264000f44001408100d004142d40114107840c4154000c0c09103034148020702540d18001d01c162406a0014004240001d0414006139000115894041006074540c00090440038003690500301003a603480080049a4009910592001c4112410441e00321a082c000c0c1d1610703c2e00f00010481c41c1d0390244000555a158440001da0714040d1003a41940f5003854100002d600202c10240e0741042d41c0070001c1c81000328018a91115400141d0b03405649078040300b5518401c140c6040e2790310076412499440c10117001c04c05007024850703135542c0c0300c161b51402007507504144081d0070109510308 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 149414325 1250 149413075 149413079
    0x140402030c0d1b0e01030c0501080f13051c1d01020705030d11011404150f060b0405040b01090513061703030105010906050d0b030a0605041505102303100c0216 70
    0x94007041c014001c0d802981c01e104004210728104007048110b1141c810f43c80940700e004940d042c140031079141030b248100c20040e00680c07540015500810300302c0d103910200e40881d0019421040d40c8a4042c3c0c0188508202e5040c00000c550111040400a5682d0002130308268480c801d10000c1301800c0084000f030010f005ca080c1000e012030388402c01c85141c4010311421981440e5440c00135809424030300d411180714401410689001c1c000000324004103031400c0d04000e400c0350b142c152480384408031440c0790f6550b4941440d0409020181c0310301c08500d0b0512610078030019041c0c440c040c0529801b508100001001401c01101c0c1101d00d8a16900785003d0b0b00510051007540d0b004048001994528100540c582c0d0aa40d0000003400700c551810f82c05009000d0b01c0300c1000a150815802075205034410712049000002c00022200100c0320b4881400101c14100000e483c074002c4400f0001445406416002c6500e000c43e2800701d6440e456071080b0354980c4044c04490f03051042c101c0c0c040701c5000e65100d00f4 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 149415575 1250 149414325 149414329
    0x4021e090604020901020a0b090d0207080d09090e150114031006150c0507080a051006080336040612030908030a0e040c050405210f0304030b010909030e090903030a140402 75
    0x80040007980100da00041d421020381c020006560945d502c08054042c92a00d40c1d8103c0d100e021124174000980310318800070a038090301180c002000030540c0d80e5014032030b01e0300d050707507014002d1b010000005005800c400002409000700003806016070000409180b081ca900345440c090701c100099100901d00407043c071040a84611030f076045402032600c80000e8000703007440c03400e00075251301c01c004911405882104000b000b00c0c101c02d00b8412028104561980c3e00d41d402d03142c2c440d1060b0600c4032074000803403100c0762200e407490010f0184421910100d49001d80c000c101200c00c560048032072851080d44640400d940144a00041d00c031413400303581031408451b4060444000d800d90303280308603100c5454146240c85001502c00401d0000c5c940b1940090070951a1402c2ca40980c103008540580034003109520400001c40302100c0d03001c51800e0341686003401c0780009181c607140c21804c0080940c4403150365601c003540c0c01e0241c410b0741c01440c1d9a080107444081102c442000d5000315120003401c100140e = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 149416825 1250 149415575 149415589
    0x130e0703020405040516060f03050708061815030111090406060c030915120c050a1413170102090d0b010906050415090b0d050f0a03180311060c030904110304021e 71
    0xd07541682c010900303407168503105003048200c10300c0e5000d9071650100010020f40c80800d030074012910340c40030889070702c0f084030454011008a6040d82c105d00c184451075080050758040d01c1d40465204041991503842c000020b00f035581903082d403281d81c6408240c00300146007502c981c500074201e034100104036000554014003400440d21429006400e00002601018000c55901448442e40718040010328002c040140941d0404c00f000000210519011890f0250380303012200c46111001c28030880602e003200200626011803000c0c6c3c11550203016542c025160442e0302c0001c00d10a130302c7c1403095810f01c070703004088500c2640142c0c0f00e41d0a010810500380304110040040d202031000106070034100c078001c242032821b124801002d034032402c040303140030b060003003540c4a170b0f10311039681c10100b4400c3d240c1c01088800c080c000980138904450f840205454036000402cad0700c9840b2010b0b01d04216902e400101107a50240c81522003e100100b00800c5103400002080c1071880351a0840c02128081c1c013081035 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 149418075 1250 149416825 149416829
    0x5150904110c1207260c0606040606020c060a18030b1602010203070c0618172706030f06030a06020d050a0c020102130506090a08010905010b03062215060806070e130e07 74
    0x15154002428405021101c0d010078203a24680c2d000e04c580300d6901c409401d442d0b00c1b4045c0d8560500412010501d540380c14041e17801199000e030300a00c001d408001c1005025402104107400380501c2019425200b0003030840c0c3c03802503000c0d072800d442c180b038229916034210480317094560469104104000e0140e82106000c40e810360402c030001162480d50350903402580f04010098150038407104030400c0c40d44444002c1802456034000c034628100150390065503411640e9107250300110030f0002920140c41446c51640c030400080c102c035003414080e00c1b5a001c9070300001d0920700064540f004c01000710014010304404090600c021031410301c03001b84c40010403940c0e0090910031400001d007510195100b111040107030040b20004c000e41d07402c41c5007490003094611800d60181c0580c00001d1180341c00716100ca815501020300011104180b6503035800715103001440030402c00d58a100209500000300f0a862144410303844d5540b90185690401c160f55041403406101135050501804d010440840e414013 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 149419325 1250 149418075 149418103
    0x40302010b1807080c040b03100602071a040306050c0f0a090f0e01080a15021b06100501030204080613050114090c0102060a200d060503030c0a030810050105030c031005150904110c 79
    0x20ba54590305280015807089600031f41c0c1d03000020050040031031450400310210340036502203518107961a1341001440103281c42140034298188030800c0410800d0b000a60f0108202006a00d016203621807490103400444070300d4002040900300f444092900428080941101401e807802985813106480e034618806074003c03c2c4c10142011906035007426015030f8035508440201640726a8140e00c1142d07122011035840d42e100301105000620b40d400b82c402c44081d03c41c0380019065a940d0a2803103200c0e009004811201c40d1368482d112076040340c0c8aa5514050211400540700101040700028039000028125402452510190340504c02c1050101000245003a1019880304000204e0b80000e02c10f030751109401d07000001f0240c24150000c9840d00549110341c031081041d48031380e200c20518503007501485000ca507040000c51044041000696800690414143e022607150004100a00356100c03404421b920089400c41042c0b40c14000c25140b0b0b03024117105401e2a07450500305503195400800c0c80 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 149420575 1250 149419325 149419337
    0x9050c03010e0411120d0c030914011e050403151d0607020c0d020105040f08071a19031e0c090602010f02070b0106080c040f0b0304140115091806060e040302010b1807 73
    0x103a0541701c500c041c0001810890580c0d0400c8080e407800741c03805001e81d00490005009503400b00350b240b80d000c00103807180c406031b54608030100b14070351001044520302007190a0010611001002660804c0402c02c0c1c17100700a00801c0740030740c000003920700f40c00402d41aa05c9401090070420410ba001800d804982000c60f48540807405500059429105a400076035141d500b500340031030508800502c0b60304454901580c0788103140121000b6070103002c0d81801c1446445403101515640d84642c01c1319000103800316080700c007103c0e503488007000c480c18070700d4900c00324031455001c010032a028480c041140c5c1240c40b082d480d2540030380e030748890a2014040d01c8c040c4030241000c60404003002007510040d140c0984d8039a0a1a1961840b03455a0001c4808480d40c420148000b0321082040c002d1260741110341c00c1e401e410340c5c184820300300500310103400484150b0407402e046022401030f0280000a00c2c44059070405801c041c20002d094842481606e40500040e1409550000045280c2e507804441481d000c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 149421825 1250 149420575 149420603
    0x602030c0408060906010302120d080a02250302070e0105060c0c0907050f0d06150518010e03010e1609050a0203060102100b01050d0e15070e0d060902030703081309050c03010e04 78
    0x1140da140195004618188221000c00120740300c0015418141c900031695241c042502003040d40d0756020002c081e50000f03418002043c214507068010341101072484035000116042e40c00c0a2680c5201c00909800580c0054010048501c1c003501640c0036007011303500d60b4a00701007814101c2d03580c02d00e803940384d002e004070b000042d02d00c0d8410029901003c04114885a998076820880c1001d010b40703016021a09140ca0400e6807814051400c031001498054140c1d40088122070040d1043c1400842c80340d00755485810781c0b02001000e00c2044000b9010003104c503c154200801142280c0004010981c20742c030400071b0001683c0c001411180c204030164002c02e40c641c81000481782070003074652200e01d05090005514000002291801c40d80b40130343e011411315070315120115944106219034580100c1c000750b1110200300c0c69086210340310300180c00c86070050f6480d650184607912401d50110b407111024414460310711540100da1700010528021410b6504040c41411040c00261000380b80c03020310140 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 149423075 1250 149421825 149421841
    0x804020d0f081206030102070c061b0b0702010c0305010b0f0919030c060806120c150a0306031b05031b030d0c06180b070210050c0403030f1b05030d060819060203 71
    0x240c0410079806201c03200301e14940e20700703441c02e50082e0440760000c40325680050000e042c14402d07112155045100210314501e08002521250900280c0d48111030b01384101720041100241c009000c5d6060354000900001000401000c40300181c01c0172500407420032104084030310f0007013602e0501c3d20450741c0c081b1408109072100000c40d00c5a00041c15000c00050009003590030000c8140f1901d4240d60722104802c558502c15201c010310074400c1c0c1e1044d004180c0003444000c001c0a49500e0b02141000150242c4945900461141c1e0721440c100101011206001c0e030308007030101c4402940d000c0c41e034500c600d00b407030f001a8032100510300300d508010031501d4180a00a0980021074460000d03904141c108101d07041054039200211011800351240c1940d21118100c01e00c5414800c80c4840003c60600e8156642180c44460045245007040300600500b0036584410b981164010702c0b0b200115074901e021890b0800f03030b030401e070b00603c3e03c0e0700a0480700001210715800c03640029484500180d0300c0d601e40030 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 149424325 1250 149423075 149423089
    0x607080724060303030b130e070b0c1501080706020706230702010507020402070f031803020a0b0906040e09060405071d0604090305160f02040513121209020d08070b0603061303080402 80
    0x1545950a00b019400000d25805510038040303400151024000824501d00076402c0c0e55500d10048140d90180034108400442e04000e482980310800959007034003c1d41400303041c242400c0e00049800d0304030000403c08180c042003003000410b0f050030300001000181c0c070b00b160000c0044030503804000c400500701d011688208221100154000c0045454802c40e05004130800d070242c01c1100440c04540600c140e1002c80b14490080b41d90080941d02e80b02d007402d2000366241c101c1e0400f90b401a4050202040200b00c082c410b52043c2d0f403a4008000324500303401c241c8c0c9400f110350300c03240c0100303031600001d0b60000c2880080d0b5030014090302c000c00c0d500e0381440c04544912441500c550000d002810041c10402070300200c45540e80221810701050b202c1c24540700c00002401070050962070103400034188140075142808074aa02d50360300285480d10b5401040200c90440800c803a01e50000600f00100902c91001e240c100c01c1c15402401640313404402d40000f00c0e06000081c2c02c5c03105c43c600145c219a2a40323 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 149425575 1250 149424325 149424383
    0x70504060e0f1302030f090f28081b10060e06060304030207030818190b090111010e03070b070f02010b090112111009060807020303100e1e07050406030b06070807 71
    0x54031480300e1003c8200140000d4006460032400c2014810119140c08000078000e460400d41e18080e1030481d83d0b50100444010030504007102a1141403102c801194840018054107a180f1484d10010706e00000160709160404030035180720b51501c03006002560075201d6250340300000b0b86a2a40d01d880d1800c0c144c0c504551039200800c01b00000903a40800c1c90310031080204142c040d161141942016a1900301c030340304a006e503240203039061000c00c48541c4030f50307800c00301c0d14441000003d6281d03e41d54817500b03540c00002c00750ba888502400b40025107601c00d1040402000070710007041010602400101a148107102e03500304401e450502e907090111010a1207402c40c40101400440100c41902070201c2125104020100e5540360026400d07900200c1140d1040500c80b52880c5041d0030250490840880603002c840032414000c15002c02d807160b1010140507040e02d85420f912076140501c010203940c800c1c91110301807102400b6400001d090385045c0c6504590159a24004641d242e080c0140181a0 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 149426825 1250 149425575 149425579
    0x160b09100507052b020a0b063006010509090f0a06020c01021308060402030715050d020a1e03060807090c05030402060705010b03030a050408010b040207080a1d040e010501150305070504060e0f 84
    0xc840441c0c1800700240304407820800072048403003d4505184180d07120010702c1c0000c1e1201545d8000a10b1520b4041c03045400710440035010310411580803000f409c0c0094101032202c8550207040188024505411f83c1603102c07801c03200030b010003445c4400701603c5042c105c00080001e500811182d441003000c0d0103980c2c0f0301c116010b050130b0090fa107130305c0143d6a4000f52000e034081c0c0500c00011400800c07280c0c03000c0c4039130002d8032500d00d0300380b90b403503c000254402e038120f4040001c95a040c0c81250030400d00c206101c01f07140d402190140c10315840c141014481da200042c483c1c40d200c5c9006c410380e013083c296680306404a440e2500c41c14a401c115002d4a14800303015414080050a907010a40010203003081c1c40c90302008101c040001028482244202c1e88042c0c4024002d11680c80c07818441c0700c1515401d02c0f078504040d00b45d96080302103015601140e42d060070a0b512400140044009640d43c02050841c0303240501c0181420840075045203d24010701040000000081d54a51180480c1c482c0711480 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 149428075 1250 149426825 149426833
    0xb04061d01090b0409170a0309080c0d0909020c12030405010612150501080a082704111e031e040524041202060106080a0e010b030106060203070302160b0910050705 72
    0x5030340e10508042401a070450303514101c828025400c0034070494403201d0348482c3d91115541c60360f5466840750007440070081003607210880c00340010702d00405426200210700040520104800300a88803010070f8100c87e249920510003d5445140050611007020032110304a41e286c65074200b05001d040c0c1500203014103500309080100300400c0b100018100d050104082040766254000701d622041e0f00a80a0900d00c030a01c000c909010900c044808a0800d101040d9003000c800303000700f030954681245008041202041c800807100302001155140e450481c400e030315600d040030801c1000703034003101104500c141100005041140c1003100c69503407800c10807040340b11511148c4442a40000300c400b19070b0580780d01e03e0840c04071700006109050f1000c17031f11040c0c4280d44c2d0091050081019441503081c564032504008103a850038072400c40507001c103a01655640c0c07028240a840c003110b4203036040030f00e440984100080045201560442402212010094104d10348101c4540c0582c00001e421405 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 149429325 1250 149428075 149428109
    0x12030e010e0708032101050306040210020a02030d020d0f050408062a03190606030b13050a060b070c090b030307170702040204050402030f15031501031b240e040207150b0406 76
    0x18000010380003041c03071080700c0b01983e2007010255001110a101f1340f034165003d54041001450006a17011900c1010301c11100c14803803075000a0300d04520342c1130010141e00024451100c055124100c5607611020342015482c29184c1001c041e0f4a16005040c01ca00f046042c0380c1190030001d140c40298150100240700d03840313040207030a5a50f01500d6100d50f031021450302e000065414041c2c02560080c98000344140c00c0344195114141c05007000901c0d030104541c0e6a10045a000e4900c00a442d20500a0b83c1030349200b0305000b90078007101da0030000d69210b58421b121110008000c041100d1400c18005d18090f201c01081c40450040c0c040d43c1c009940c020700201c1044241072681150f43c1c0b00d1075441013a14240b20360744043c1510b0380c640503030130a015940c400040c0702180740f400d4a0003480054000c007001c160f0b80e030780012102c205075030703040e1100380e03810f132413a91903607521030b603030488407031301160304601d0041e00340e4a50003a2181480560682515454040c905949503070140006000d40c05075041d0084c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 149430575 1250 149429325 149429339
    0xb01060f021506060a11030d0f050604050a180303020c030d09140d08100b070c0b120a050709050105040e1b0c0a02090a060b090108090f0d030504050c0d12030e010e07 73
    0x180c0910050062080c240100c010003101c284443c0605405001149040c051003022611250344c00003c50b402d101c06c010304510912184500d01c000100c040c4000740508180302004252113024110232107e03820080303c0b01c1c0c046c0c1842e41103105113905050050f500c40c11070320314601350300950356034100b403a00d440f0a2205012610f4078100c4d520b80c1030001c1c2c80d0040c5c0d41d00402d031840031094550010032500c4e0b55050080081d00d00003030042c1c1c1c1c0508020f800c0b559a41100c2e00366603200d03070640001400140305000080c8154040c1d550881c0e60303428202103403800d100008001d0300403881180d6800e42518042413001c2e4a078800c4095070342020343c2060381c401200245541e1003001480c22801078823480d0024100683c81d00ca80c400750b40301c034954103150107205001181c1440c0c014200d0403042c0640c00d2441700d905400c100c0c0e00c459168948010409140034240319080c105c0c1007110074022524420f070600084c86490242d40c59a0700c60800045041e0080500703401010a068501d075148208200403c000c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 149431825 1250 149430575 149430587
    0x70e22150612060b090d0f020405100f170318010c050607030c1116090c09120b041703040c030b18061e1006020c0f01050f070c050103051f0b03090102070b0106 70
    0x9200305840b14450000e812a00b07078120380c003501c5054101c8070b05003c403040d0740c544140140c3c24103000340300004403076503a60000340890f041503e0f000310340001c11004001030b003000d0710120010444840f01707481c840c40d401111500c03032242803020035501c4d544140c000ea05d6030180c14110080354000e0211403030303460400c0000c1c000704202c3c041c4102003084824101d00c4100000b6000909080300010405260301c1c2822600c040d100342c488134070a2181e607d1000c503800c0c81000581c106280902848030300b600301400c0c1800524002c0d100140201000c004210101d98000321f9503040341e6010070522540e47d03941c00e500c840d0101c20510b940ca503000d0841806448021003104241003405c054120360940c039100328a80c1804440d10407040543c200c4285241503162840c2800114281030500310714200707d00c508004030783e1010a0848900700b8140302030006507814400c80c0d40c44540d4078040905034400451461381c1c071216210380f51002900000045031500300390140c580517580454200600d58542c0307000740c00c2c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 149433075 1250 149431825 149431829
    0x10b09131a1908030403120207171c030204050913050c12010f050601020d02060a050a0f020d05150603011d090c0a080d080a060e06040b0414090307060b0306070e2215 73
    0x100b44210304003155050b1800040004803410710004515203443d41d551621040c054071088010750150440000790989040d02c50070040c07100c000a410b8144003c1c10f100180300c0d07441241030405105100600c11510341c682e00e181c010f8104019821045030a2402a1030078203852002a044016090210051141508041040d6100c20740030f001958984004a99400c1543e0f258030060f40070b03a0108503603131a075a02c82c5401581c9080041110000c101c0044145d070b00c82071408071299645d02c100154282c06410300080c035407040b52000e19551410041c0141c0c2c0103010f840c00c142c80b81403404100c84071b01c00c0102c000310600140100386429507846183d615811514030183c082030307a820001e458007649120390816141c071565645126240e541c01e10006103d0202c0003500559030b1a000901c20309146851481101c00308000c42d0756010500d03090702501d2426240c01d00992041062215441d040850784005076001d481c41485840d28500c020280703100308050720344a911340700c8451385a1200b00540701c1 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 149434325 1250 149433075 149433079
    0xe041b0903210e13090f0803040303050603011109060d02041706040c06020a120f0e0405010306060819020f0f0604030b0702061803070f110307030b010803220b03010b09131a 76
    0x2d1000c0012034003100000b400c0e40800b0000d01c4010441105282401c07a91a0b01100c83e240080c4404403569140005a16407030280c51829000c806c0004050303050103880c1c0d010f0410b40013409517016903928510709000e00d800d85807156030040f0f0700360540010b95060b40e00031300c0350351813a9110b20010305285071908800d0710140e81a08a80e04045201400041d6403100e40d81e00c40c00301c2203903213180d01040720b4003078503003102e141000700302440c03901c807543c1782c1c0100d6029502a81c400141d01e40341134801c5c5d103070005403210750582a03501d06851003d40e851503021340d002a4150340d02c0c917a401f000e42c005030451249400081111407050140600c1a5000a4452240801a0318480100c6e4603a0445a41e0b02450310010304030a02c230902d41c0002040034a50086011020701114200f80d1666540c13805100241c00201d980d610100b5000c504903101d102066110164a1107943c64030b05242d541c2145110500070300e12018000034911249849142c1c074120750040d0b802041000e182ca40c0c4802c5011002c1c810218 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 149435575 1250 149434325 149434343
    0x130b0603010f24120b1807020f06070e01050409050a0b03030a05091804050606010c080d02071a07090f06110309090103120e060906161103150103120206010f060e041b0903 75
    0x118024a42603000340010f2454131002d43c0c00180310031100140480e10b00d942d07004451504204d002c2c03482c1811080c0a00090b0f0060044030b03c1890203240b034008024050307803c000816000c442c050340c00000711030540d00303031800209181d074980c60804081c0042e0f01159400d88400101c00b060030303500201500c0309010440e040130019403d848101400e040039030300a40550010004900035600490382d003a821440388e503082c0c3c140b00032001d1100c101d800001050307600114102c0454000d4102d0301c8540d60041c601d091900e1a070b8104071092046101600945007800301d0311400020200042081d5900407070000c1070307444550307181e160081c020080e0750f20b001c1c041083d10258100900d002400d86a000710b01915407820045406030304145a027180c8002d40300c14099900c680580e80f400c1c00044441e02c5080c0f001044c551661510a8051340740e080002e04542042005000c1c3c01d044c0410001100e40b285001013100349800001401010126000c44440c80c00d89256506250804480400c40b07024190103 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 149436825 1250 149435575 149435609
    0x2030a020f060402060d02070f0c0b04051f0207030209040c151e020109020603130f050d0f14040303090b28030e071d1b070b0c03060a06030b01020c130b0603010f 71
    0x2c0e92080140e400070760114080c40b10140c000d42d142c0c05412000e00580036525649015110b00e95002d04641002c0301050700010207000c00d0402c00442c01060303084181f007940c1c918909030003d48580e400c0c000244500c81e010086030034403801080071409010340d000c0d40b80650003008c90103440e03001340175440300020300f4082c0c0c0c1e901c045006200c2e0101c140d40107803001d07165917680c54179603007000503a20301101d40207002070004000c2501084090081c00c15a2180d085181d400c0c01d01400702410700040e1070030f08000b00003e100080d07000084a0481d004010038549071902e003500d9201d0b1180c080010b0380c80000c00d005980705554550081c8500040c1c01f42138645581d00c0c8c5a00003d82540703044014806461240800d00c400800340d180420b281c00c00701c1c51803c1108503500d50081c0402698214560030340482400354624207070300003500803c3e03075041c04c000c0e800c1c0c2c8a00203901c803440d2000c102e12403507400507080c3e401e00c0260000003d200e4020041d540d43e68440040c1a9502002d01030004184851100 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 149438075 1250 149436825 149436853
    0x50a08030a020406090506070c031202031b0a05062203030c120c0206070e15030c0f04030f061a09011508090304090c050403051203010b0301030602090406090c2c0f0105030a15030302030a02 83
    0x80b170340c01d640c11009e050107040c110f4484110400e5020403c1c021848200110040c0c11307603254601400d901c0741e038054200c9180a0414616100d03010b84500d41308a45146081c64036a143e1604020345a890305011030004036685d41541c1c0d1445041184072601e08002520015580c0418030910400c065201d40000414503c14014626040304c04854103071810004250360200083c041c1100082c4611310520b0a600e035070b0f0300402541c0c6400112996515500341d801650000041504481030a4550441d20743c0b5144090805606d81143c92043c007082001082440c001032044030040d121a000c28881a40b203600c0042003a8440d04c000e5803140500500701c83c040c803031001100c0c102c0b10302100b01e50450b425920b400d0b000b58040182c07070703070710540d140c4001810501174011031103442ea403512505911586c00c2c1020f060464840c4060840c50300900018405a9a02c68204401c900a00e031035600e81d503448441d28014403407401e171041c0e11000340350700208055001006101e070403210b07420b541610340c00000c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 149439325 1250 149438075 149438077
    0x70201050c0d0e030d060b031008010c0807030207020a051c050c091314100c1d03070f09020d020f07111311030c030406240f08060c03040609050a08030a020406090506 73
    0x4804403001c504000c498090300c0590008a040381c880d00940e0f01e40951402c00901b01d0305e50b540041c1010f8008420031900803440c40301c040c01420418000d010b20103130038000800290000707000c14280350380404d1303800a45d1a1030030400701900c0058420955085c001a030010314200001d0101d0311441400229541400d00c0341d0a05d020b401c01072081074001006507510f181c50340c1c20240851003442042e6010300c42501c0c40c0070b0264805d00b6900c41440ba04960171074040030b18608101c150080d1300460701040840e001d444400100c420352040161a40003803d00348020340f2408070241803680c40480c50f07906000b01c20884028000b011941942000f90700700001081c0d5201c0c407003002d0060000c2c000560701100d800001c5902c1407190300001105100300060508400c1340710003c0c026510312102c24406101c00803603040c081c1c811100281a40e10306292a50a9840005c1c0020080c80e00d41ca0380d10704110080012030700040c0d10003c429143c0c40e15039240d01c02504a80310740800034102080004103030810300 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 149440575 1250 149439325 149439331
    0x100207050607030c020a050105010e01030b0601081b090a0509011d0f01080303240907120c02010e03160f080d0209210c0d020111030f03090d020d0f0c1104110a0807020105 75
    0x40281400d42d544400c1600201a000140c0342540510090480061803c1c41400d000c1d100040d281010340d410341c14030010360080144007506000e109000e0120640101c02000c0c085404414010395862800002c6624005194130032600400c0170400444c4000301c000b14007403c0c200d0215004425901e48602550168081c0701c0c080d5960010400700c0c5407294a0604900d14900c0001d28065440320381000c224800012a20040080c201d003c05080000c4517009440b000340c00c27407000340660415841d50f983c03603215030284841d00c075180040301030410542c814061002500f0011442c0c448d60010400c034065401441c0759441381c0040541c80d074200103c0d8152910074500400203181c0803441005104070114411807d0b8140280e0340d8014241c140e04200414000342440d81d12920703818200051441c220b909202041990071006c4407010703040e0f0098201c038140b807032440c0c0000710400b582481401c40e0b0008140d1500315050040600b0344c0f0341c0c928001c0030001c034503589840709590b0311501242280e03010b0b = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 149441825 1250 149440575 149440583
    0x7090e060604020a171b04090c0206151c05010e011506020106061d0918060112031101050c03040206030a1b1d0d0b0c0a050d0c080609090f0703060e0102070204090501050108100207 79
    0x50810502044170000b0b140c0e40c0030707040a40500041c044009000348039041580711581030f584403005103104550600420340c006102d0b24403480601a1000001c0260070f0b90385900c801c0d1a80b80310403109201c401d400800c140c094000007004000b2002004400c42c65450003070b403001d507080c1040000c28074428a4800c5c41c22055414110300c112001c8200441c03074102501048000201000e0040000c0041c40f03440c0c001d0140784003031003500c900e03071a028080c0340c06c0c01840f403580e914180420407035081100c1100d80c4030394100c940560702c1c2d44225841c8002d10190076001700c003202810b40c03c84c0c1560009480c59420003054030003540d114490017001048440d4660043c02c5044900201302c1403d1000042e1074058004d04000b414642c11040b0780048510035500c11001034189428000d06080c070510307160300710002202601010110294040d9185100e00c07000382840d035151034080300104203605864110f80d0041040c804054142005401382400f801801c419004900294100342600d108440310700d544 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 149443075 1250 149441825 149441837
    0x11713020a0b0f090d08070c0f060e030a05030d0504081608070b01090239030319050108070305060610030624080907140909071a0d0b062701090807090e060604020a 72
    0x111130240070b01005089801c03942c40c00203108020020705455041c5015280303800803550300602e03102008140e50340944609002e60400b040600105102004a40a02040820101d01e5886500d00103205204001c004e5001c0000c0301000d20800803d04010490a0301483c002000da0362142c1c2010304030b220350300c640107400daa022001d0405c0110076140d04c902481c1070350215610a19100f10500350f5104032030403000c840c440c4400200051a40c4125405011884010501141103640311681c0705070151a5511a4603400f1407900fa0300e10036000320000d002c001801003060076507a80c03945140054802c0c1c07000420f80342400150515000500081100d00e035500081d591000b20051000703101001d8015042801100d402003002c4191500d119107220718100004d6842240040e51006c82c0c80c0c40e01650711540f000c218800591f52091841d60b4124000c80721402d59001c4800140c07180e00e02a801828580034070760b40064004002c0d4098020042039000f0b69410b591a50100000c030b20481d9600c1c0040340c1 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 149444325 1250 149443075 149443087
    0x10c03020c0a110303130807050a0801060f09020d02042d06110a021e0402040b0403050709061d07020c130f050117070e0a0b030a0f05100b0a1202011713020a0b0f 71
    0x3809982c903e0b503070002d0181d900e84100d000c07814243c1502900503140503402010b0070032980c18046140c2c4028414180200001d41c1096030522036a420391050000c0c294000c541c501d80802d01e64121001018007410140e241e41c400d01943c0b04007803002a0788291002c1d80400011400d0003201072810018600000c0d10603050642d080000007403029810300390f000703045c0705141d00e162620b2004101400c0070b0380b903403a126865450058a020000d41000b200c43c2e0402104101403003a441c213030b0075441005405c0722115540d8541c101c2c945185100b09980c001403002e13010301d18602c29800401d13888400750050040342c0e01c48070140030340a188062160250b00c4442c04107e82e030065001190040720001c0c01045003091000024500740c1c00708405e0b1845110880c60313a0800c103041140c090004e526460520800880800050745802c481c0701da01110709810107640c085a102c1d48105401c801203000c002144d0070700c0707420144003c5400c0f03012070003074103140000f0807060319117802d4885840d81e406130076260203 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 149445575 1250 149444325 149444333
    0x5090a0b100c0c080f0f070b0f030c0d020d110306040b0a050d060b0a08030a03020a09050d1203020c150c18030a08090409020112021b01050106050403030e0402070c030506070302040602010c03020c0a 87
    0x20754046001e0b141091881000710300d0b002c0c14090085c0e442c4030340c2e00405291091524150404120703a201450b4100108041c1c40350055203815a5402401c82d400750b82c0759070000d40d030301003c0e00c203c0c91304d0100d103443c0c031a80d2400c2c250141c000c2d5000d040192001c0004100403410311a40003030358010365511204844145001807820380100c3c3c0b040c2d00c003070440180300b0364035602c0360701d980c03c03440721540402e0300400c12003012540200804000d2504403034906003c44691100c0624000e4401c00034100760f0009001c2186020400c07000401812078660380c00f181c079000250209541252018010842095a02244c0d0f480c001540241c0036400c0010300d40b41c203821a04000007040412000c83c103000340c810801006440500c040c0c4850408820440311241c0300041d030a0840b13105801004c103001040c4000c0c80880d600100d66000802c003901c00603039641450401c9074450800d80c0c0700a00d94804c0b641003014441d81038000e44216185600240604400315101713805074010740840c0f8041d540449944d402007 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 149446825 1250 149445575 149445587
    0xc020f0a020d02150f0a0804061a01080a0e160b130504051918021203030f0f0c0d020d1506090602070501090e040b070c2009061509010807090905040c05090a0b10 71
    0x3800e40004d05494030005842c254520f403c100c482c0d0f000f048640301040103200b40ca0003400d1540c0c42d50b801d0b840d14400c0c0c2c24000b07458428050319480c0490b035110034040e41040100300080c2d542d0704180c00c0404c02613482410b00055442645500c0c80e4448050000420341814055207028840c003141203c54903880d44a840000c080c849071020b1a0352030300060030050b85a0180c00700d00048280c000c2c507942c0c5407201c0a401c0581c4068410703040307205180c0400c000300d52140142c2c3d40e542c454580140e43c44807115213110203002d00c0091415038901b11000040c01640060349241280c2e582d4003680c02180c2e4400064400e6502c2d84a0705007a0a5400009030014100c01d403c0c1d0317401655420207481003602d640340d2031900d4002070014440b410350114008507a1400760a110b9015104030352140c040d130303159032240303425001e88407611341400992408102d49074003c410a40203096509001c101e149000d08103003441c8412b07441424015282c04010421a03011070082c200c05000240007080c003074004003811100 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 149448075 1250 149446825 149446849
    0x6010605041205070905010306051509090d0522090501030312020702060d0e030714010c110c030c040b030319120501120f0803100b03010b0301060f020d09060e120d02010c020f0a020d02 81
    0x3c2d02407500040303032640d040d21030300e400385004500018140c82d02d003900654005000854a1046204004101c1ca208000824a000200500c3d2050300c8008900c561580d82112203251030740d0800c44200400c0d43c1c202988164100c900968412000c041d4015034042248980d040281d0070910401c16a000062583c010701000c4071040100c920b066030b280c03070781c64202e890301d80c0e0020b00780d44030000081344a41c40300d9400d0f040c92405010700500744100000030b030b48038199510a4002c6840c1c00f0080d909540038020f0303c041e1144080806a01285103030028600c81c0c04200f210100d44c5000000301c2d408002d00c84d18101154481034074100d180c030a451303035070700303604010030240b8414180381d0040380c80c000328005540240303020000252294144070000e45442400d9610504550140c2c2d03d001d19158803034441001c031112401c00f203241c49040008a0300d01019445c031086c0600c100220710b101264154000f1803040202d5080e03400103400ba5403032a4540c0c2449001030f47c84640d0250800c05482c03c1140e50314 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 149449325 1250 149448075 149448083
    0x13050d0c0501081e04050106080f190f030c08070b040203062217040902211b0f0703050d020705150903041a03090a0606030b040312020a0c03031a1917060106050412 72
    0x824513180c3c2c5035030901c03600112000c9036142d465007130401c050641044000b001c203070307003030041c04400c641c2283c800d08a42200501401003007901c0342c90b0b410302d40110713940d075070041e00a580d1030340d01c14182c1024451524240c80c100d002e4441c80340001ca099981840d05e151205a40d0700003280841e10742c0721416000003405038070085840810000400d442188000c050000f0102181002c200c1c5064580c2d4084c1c000074486960200f29285071301c0340d500540b04454441000c20360382c5840e0703122810101e465024007142024030074400a1008140500012a11907000920405407030b6582d48007140347d1240214844c4c141403400b0311030300d20a040c00d40f101030359110840f1411100282d40341c0e124002610003540c020f454071841e00301803000381a0b2014508601d021840c1d425898480410030081510300348a8000e03081540d181d80b5601606010000340f05146001045004011228084c65129080b01e02c03440c02e20310746042143c52980740208d042c0d8100c0320b240d22140c1c2400d1400512400c5c121290a08070307 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 149450575 1250 149449325 149449351
    0xb040611030a15141f180f08010e010b030618031635030c090d060e1e0708070311010903060f0f1a09010302011206080307050313050d0c050108 63
    0x48040c10402019502c505544640481c0704000750303240c1c00e08510381d904840d200038240c98481d03010b42c648400c81042040042d2901903503141501342215030700b00419404801120310000024003c40d056945000c1d1040c1c0310080110607200c1c40070500300c581c0d400c0210f400d9008000010904104480f003000701e40c448038140c0e49005030342005681d00080681d412268100007090882400b9003003040c1801d0b006a2301c80300302c1481203d847d2500ca0b03010040c480c440713003440000e180000d900c607a202c1101a69000740f09010300820000c4d130a856440c3c0300c1032640c0d20800b40c207000c0d20a00c0001001c100b21b1f04000c001d040c0450a40d2107011244944104480c14400403210010001da968810420402055403001500e40c403001040c6e4140c4503603d208448103144c0801c000155030315101c50380e0450b50f09003403200403240a900003001401041d801031035180070100d008414043c02100402d0401891220168605e844808001c01e0660201014003c0e11400030b00340400e5005100381d40c2c011b00404114 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 149451825 1250 149450575 149450591
    0x906090a06050d0807051c05040911040918031b0c05040905010b0904060b0310060311010e0a1805040c120b01090b0f04110d060b09010e1509060403030503011503180b0406 75
    0xc40c2503000780003000c0721072480010354203042c00f0b03080c0120311f81d07a8501489404141c0c0d00c58001802400b07107004200009584590b9400a4180c04041364018044604113105030b54441500c441d080031000300a0f00801e850050014903c6004065560309a5200b8540a43c0d5424002400014000040125035a6503280c009400658030320401c0c0b4441e910400000c1600c04201d401d02d0705221401e90100c130301074185902070000270709100000c0308070326003803a002c00c0b160082800140d00b4081e03548a044075000245041e4810001e941204d4882c5001d01c2e080d02d603244d13031204000c01da50b45801d4060690000d2500505c240001900b08003144c5000030700f54010001c142c00001c0884c0c1e0006504001108006180c40340b24606000d201d0080c040340042034201003007840080c200139030010040d48900f43c0d016500b6800c10045c4199088054082c0c50581c44a8581c503026082e0790003030143c03044400c0e40701001c03600e662081c040c42c51200a580031608010300190340340e200810016000f114a6034039884c0d2 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 149453075 1250 149451825 149451829
    0xc0f120509151810021603030b0d0c0b22050d17070210110d0e01020613050703080310170601060c03030e0c10030f0b122e020408011e0207020906090a0605 68
    0x82c440c000c1c03420114204100059040480c07504084c0040704d00700718018450700c41445000c0c54101c101640600340803131140400c5d00011000384d444c2c20014030a012700301300420f800c0c9401d00900030044040c1e150400e00180d0800001e0285014410b8640c00900b100d040d40001e4016103081409415031490141042069400506020382d80d1442000041208a51442010b400c000341007500d01d007400c2281d80320240b980000e441e543d00820903d02410f135160860200141000745800840c0c00090160305ca043c42c5110318a0302110784507507200211841c82031905200c000c01c01070304036015a20740d00b00c1a009540d0560190100107a04d11881c000c0e055207a0070340c0c480c2402c0900d40142e0f42d0b070028a88500180e10812a4003454500340244402d1049500c2c2e0341d80041d14219421600500e0901c015200960002955a200786c07402885c0c0003003000508a1415008500c4c40500c411031454a03000b480101e5049026116001e0361100c1c00c1804545a4103082e4103064002402d010045900e91721100 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 149454325 1250 149453075 149453113
    0xf2505012d051b090315150312040e011a0d0e01050105130204050307170106081603030215070f0f03271b030203060403031802090a020703030c0f120509 67
    0x100e4407076001008514120019400200d60040d600103040801050505a034484840b8004003081d10040c000004c481980c3e544c108041c031141500320074405818546208144551720003079904074007905c111072043c0c114032034000c141c03000e8454000403003040c2c2e882d103003200200c64030910a18a840c007042009840c2c0080f84e0042e600c0000080b0008580e0354074103410310138915030b0300c0401e90065106000074401c61394007044010484603002c0140c207040d214a284a80140030a07407051a09104038007010980a06014988007100c0c066000d4903491303103051900c403520480840d001c00006840d014020b411602541008036100c5a034070f000640001d04400003a10054200c0034101c140102c03000000400200700c049104850301f45400e406030078076590200340d43e00b00150000b418582c403582001c40110341c521084000d150003c00a80170b40c10540c3c4081c00952140c002540040d04111804068500132107814900c90b5480c1e994005002058030100010704016052004602400b03010005c0c292100ca = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 149455575 1250 149454325 149454341
    0x60f0421120f211a0406181e06060809161406070c0e07020a20150315090103150b100801050130020901080703060b040e09030702120705150f250501 65
    0x2280014050361000c0340c2100d070800c9160b84511440c2010706c10320102101c18030300c003507400c8940008030307046607146110140e076129070406124480c0f50140004045a2107402c2030300804a03c010703558811080d81c840c601c0b0030b1007405031998142c1c1b001e901100701d0410400070818207002e0890150f03001d80350540466610410386121005a01c64400c038130074814100c032014401000034420000009141c404201d8000d00e070584465501404000284046040c0c11844480d080041c43c1d03618541e100e10300300006440c0e8a84da203c2c0e0343e02e48000742245045c040e0ba0108121300741e865058240e0b29100044940c5585004000b2180141c41010402e00700200d601e24461280041c0c0540c403210342c4c100040c0024402481c800405003003a104000d51004002160b007039035401c0c1542d40d210b03524000700341d1540c1300300180250000c0f142e48106032102d00c0800c030703a800c0c0d5000700c0f00881e0400d1150a603006074000d15000c40c0000c142080b4440c51507000c600588032014619002d410308800707a4490508641c014 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 149456825 1250 149455575 149455637
    0x3121e081503070f090903050d15061103090d08090301090501110903150f0a09020d0b1003061107030816140313060b09070507030c020a05060f0421120f 67
    0x38405100c03984110a5105107612001c0d00200295454440e000240186a101380d803c10760391800000e043c144190129004004941001e100b181d86014102c00391400c0c5101d1500012489904051004004001c039007a11400800d00101405c0648407a1020741c001c001c1c903549513580f50300315000104280140510318203c000c0850b100e95003101494242081000003c0d00c03c0802c0c42002210b0042d50422508002c0080000030440c0180c40814148000301d400034000d007203010100704240700c0f0b01030380c0415603202c1c010501500c0c8401821030f039180555480100450a43c0300060b11219850001c0d00c1c0242503850045051101e1a590b03a80550099951840582201a0840600c00700b8001c85580150076501e4034903610b0151401031050040640040030031542c81c000805665500f03a020000d0f010080c00b040e81c9a05401e000e0900e030f4800e00c00e5840e0515850b20380740409000c42c96400e01d030382d044009000525548070301161940e425116800c14060200c1e80d0950758091914500038040b07103 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 149458075 1250 149456825 149456837
    0x130902090301110c0a0b061503090606030708030f0703050c0a02041805060907050901050d060f0213090b0603010308090603040305041505030105040b0a0602030d1806020d050f1f03121e 81
    0xc0a01410b0a64451200042072141d0412040c00c82c02c40003d442843c10307401002c4641c50b40c42c1d0700002040d4a00420418001400120a10131101d40101d4860b000f500110100c03145241e49464503500d0b802804421800c0a601307000c203201007409100240b200020000c19580003d079594000f03030031500c200e43d4401d00c00480300c0340141004402c008080c2c101c04200c008040551401c400100490414000d06000d0003000c407074030f0100000e1341c02152902142c248150340310b1010500080341c511403481030400d00350800705018071500340941124117032600801d07080d1400f0110818800d02d42d0000d4030440401004000020b100d000a4011455544d060b079901a40c7c1d5240800308000d03120840c08840c0304510303900341000940d8000003200c1c4004401700d07010401d140c1d0201140c10011014002400031400010600301d071211a91045218007000c405c02040381e11000750510301c114003003240c07801141e10310314140003042c400200421001800d01c0c0c1030750203000b00b120103002110b0607200c0c80c010504e = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 149459325 1250 149458075 149458087
    0x50106180b15031621060b03071205060901120f05010603030e0f011704060c110703080307031508030906030c0f07050a060606050c03070210140c0303090705010f1e05130902 76
    0x251440d4900b01404401d81c1050071410702450700b4a8252115800009110b07441e08028003a461001601d21040c0e5040b50400c5401c0c0e030343c491184150702c11901d020000300b035400249490307107981c42198010f04000d0407081da145e00b480d0701c1144040d040f02e0180d0b84041440607140c00181709000744009140310740d65060643e246101844010800007107800d0600c401e8028440f101e280b030300c0b400caa2240c0c116001064480116000340d481a075030b110001e1700d6024000c8007009002c10203004600031012a50104141c0000398000e1078020001c0c0100c45c925001002074040610b02540135580080c40a2205885d216030007402d2070483d400700408440c81c0e00984a004148215442000002c14990425a02e0106210421612449044d1000784148407092102004920480b005a4201100380c000c903501e650a0fa00d06980780c0044803036a206114606010680794401d07901001c203d105601c4800c0045c4d0810500940500c1d840011400c03c9002d1004805500d081c02003113006041c08400160703190 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 149460431 1106 149459325 149459329
    0xe0a05031203100626040c090e010e0105060306100b0c190c1401020321061f121805070501110115090501060807140412050106180b 58
    0xc4200800041c0041c15080294050294000084000c075038414040b907040b0041542035406018450b400c8008018240680760842d119062010340d136525001800100d503003031014980d090f91550008150043c0078803e554010300150301900040c470709100110165072491141c480c0040b000140c0350648402840004400410b0481012102c0511700f00805800d03140d01422102d104580341404d100d6000004032100340020307110b070701c06204401104281600d802806542c01032001109980d00080c60301a10001101d1a02e8596040b00c44401c41411100c201002c421400304092031003002c144000381c500102e0b4004d00e4511050520a11110302510655040b55a0003611080101d00395101d5041b160580d00389031b842c0d1700c190b51003c13001c8030b401442a500b085035041c1000f007801481c4a03094040c980b82e024900200790b0a90301c020800604007410b045010b203e540c1c3d01044494 = true := by decide +kernel

theorem cover : BRFrame.Cov 149280575 149460431 := by
  have h0 := BRFrame.cov_init 149280575
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149280575 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149280575 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149280575 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149280575 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149280575 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149280575 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149280575 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149280575 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149280575 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149280575 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149280575 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149280575 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149280575 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149280575 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149280575 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149280575 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149280575 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149280575 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149280575 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149280575 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149280575 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149280575 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149280575 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149280575 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149280575 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149280575 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149280575 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149280575 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149280575 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149280575 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149280575 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149280575 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149280575 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149280575 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149280575 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149280575 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149280575 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149280575 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149280575 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149280575 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149280575 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149280575 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149280575 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149280575 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149280575 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149280575 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149280575 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149280575 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149280575 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149280575 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149280575 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149280575 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149280575 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149280575 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149280575 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149280575 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149280575 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149280575 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149280575 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149280575 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149280575 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149280575 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149280575 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149280575 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149280575 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149280575 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149280575 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149280575 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149280575 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149280575 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149280575 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149280575 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149280575 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149280575 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149280575 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149280575 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149280575 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149280575 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149280575 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149280575 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149280575 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149280575 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149280575 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149280575 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149280575 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149280575 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149280575 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149280575 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149280575 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149280575 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149280575 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149280575 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149280575 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149280575 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149280575 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149280575 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149280575 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149280575 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149280575 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149280575 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149280575 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149280575 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149280575 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149280575 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149280575 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149280575 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149280575 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149280575 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149280575 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149280575 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149280575 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149280575 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149280575 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149280575 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149280575 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149280575 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149280575 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149280575 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149280575 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149280575 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149280575 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149280575 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149280575 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149280575 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149280575 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149280575 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149280575 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149280575 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149280575 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149280575 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149280575 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149280575 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149280575 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149280575 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149280575 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149280575 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149280575 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149280575 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149280575 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149280575 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149280575 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149280575 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149280575 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149280575 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 149280575 ≤ n) (h2 : n < 149460431) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
