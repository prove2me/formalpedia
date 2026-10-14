-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0818
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T22:58:21.063379+00:00
-- url     : https://prove2.me/submissions/f977fb66-8f5f-4842-82e3-ab2f86a9d757

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 146942446 ≤ n < 147122302 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 146943696 1250 146942446 146942461
    0x30e03071d090f0607050f130612060b090904020f031c05122d33010306060206070c060b0109030f1b211203020705190b1005061b030c01090b010e 64
    0x41401c0c0360324042c2c5501c138102048410744101d000300035a2a14002d054200700c504440c80300410362a500010010b0185002520b00d94020300c10400105a007000207840c0855410200c0e046c224001c201034444c40c48550b01e11041c0d01c041c0001c00c11100c0550f82c0c00380e9101031b40806043d0f900111241081000060300045424620400c00c0c3c840010b5110300340140031482d440001400320050032003000d84940300750385000c0d140d040f405000d464442070324458400442070004080f10550f038001021075002d007051080654200c4c10540e01141c20848c0840e075401283c0040e2072054944d800141000b40c13032000003040c45582203140b0040d1070324441c0c40703400035034880032401d034034040b00c5000d18a600031a9030b420008200d240c0003040310406003000741c24a5165210300c0d040681c54180041d03072280b1100c0d2841040030304040c4580c800700380c40609a4243c20500811800e0081c08118080d0320002094590b03205d00400a0383c005400510080c00b00c003080e880e002d031420100303104100d0550b2019000c03c180 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 146944946 1250 146943696 146943703
    0x709090e06060405090c0a080604050105070801180c0e061803010510060f0507051e030a0801050406120b0406091b030204060504050702030a14090301141501020109021309030e03071d09 81
    0x280c00944000c01c0d41e51a110108001024064003814a070b20a510101155843e161030030b00c001c4c2400320250001d460142802401e45100a1100d000c110740d480041c03040180c040824bc50022a42d20001580041000f00360385001c0190344103680154003040702500408021481c1003008000e80081c005519010f00e5011903091500684001c9420040c8016045220340081c0a07041d006000f1904d003401c012508001c03145500e490f0395155000060400d8015802c00504c41c0180401c1e40c08000c11454664110111135a2110080c00030b070b400000310301884800c0d0820000b00e5081150404190301c18003000304100300038030040740503d062100026240c81c05225a5100301c0c202d402461400350351840444404528000b0040c8085d41400b400030075442c02d20401d11350240101402446040405900e08822207006409046a0400c80a800103171142900b007505260100703400300d011036462506444400d200644107070144103414000520621426580f1050316a05400d500d241d01e49048160301c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 146946196 1250 146944946 146944961
    0x30e010c05160606051003020a090e010e04022101050907090e2a01050705100b1f0c0602090109031403030714030112030804020d021003060501080603070f14030111030106020303070909 81
    0x4a10305100c8900c507070520b0a090540036210b6000015440d46440000d0f100c001c0c14654480020307400306191501681100707030b034406014210b51561041d8501f0440e0320101740004d000070300420640c103128420b490740c07203036095140e060003000307120380e15000207520f0751201c40e40f03e40040c9500b0036000341d100803004201042454440483d00000c400021030b6401c0212002d5a0181003000c1004140702103801403020842c40003042c500403c0d130904070400c11444013207400701004807040b0201da510105402608200310a54070075405621056885d0050302d00c0b81441d4801703841e0680d054515080680b000c00210b00c210450740350b010700c1d19200340c240d0b101800309000342101201070082e0700b00424012280594018402807969100d64400d5011540030144084440c01098442800b44001d40c1c020160991240b41a002401c00a18013481864001302c03030310481a40503070401014406482c00c0d081181c95020402d020f23070703803075030b54510080d135942c01210f4900005a41d40004558011580240d00 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 146947446 1250 146946196 146946221
    0x106090b01140a021f0b18010503032a0706050c070b0403081233010e030f250503010914060108030f0301030809181602010f021312060e011b030e01 65
    0x4002220200000700d079000f61a0070b82544604130340c1517040300400000c054032444564011030500b481c0e409010843e009040f0000b0b060320b0800050115450010a0b19001640100100746442c242c80e0700704110541c0c0c09aa00650042e0385012034050f1304880100000710070903007211070041d510300480900b40079500000b003000d5010020b40c03c0c0c0b1801c45200703035040702038542c034034500550803e420841d04140e048140310800321007620000365030b0803072000205504160041d141c4612044500c580b2407a070380502c1000c0d5001c0c03030142540c050f031100b2904054000035000700b00030500c80c00d1110350740300c04411b0b902c00c074407400002060007900070050700c520085820203141913074295500c000313903a049048481e8110104800f002140900905118019441d254080010702542d4100900359100e414004104c40c1c0100301424044400000c800215141c01403003160840003440c114018042900000402c0c0d8201019119250400002e608144825450401c8032901e410031950903074200c0304010 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 146948696 1250 146947446 146947457
    0x20d06091e1b030c05010f02030408030d0b100f080c0a030f110301030b0c040807060e19030b06100c17030711031818070806060f090909071e03210e120c01020106090b01 74
    0x100719950180f842d0004000c51f60048e64200794a40e21450300d50340251006a910f69110100c02009081030408003070132941d03030b1409194201c0d050300081d110200160074007640c01800513215140030310a0380100b4228070104000d2150040d0401e902d44a50800c1c017065404449005c0030940d210114000c440c05c071440000540000740c94440117450560141000391f4000880e00d000300c018000d20350001740914482d00c2c041d001400d020061120f483d1014021005200380001c088000c11800b60b8040d0b0340d8980200144da032641d540d0012070f20a2001c2c04031607041d100100341801401071643c2000000d41d410350f0200703aa8074104001013191503040c0d0718900882d05000104034181003160040c8102130000149a260044a40110f04041822110f03c0e510340c10540c018040540003198a07800d0b40700b141c80c2421642d040d500c902d03502c000c00b80200f0781c941d40b00315880600680140d1084d540400d0083c06080f1908131b4100c041e4540c0980b650141c01546080700214200b40c1c0c91188001e03011040c0e40e80d = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 146949946 1250 146948696 146948699
    0x20c06040f060e191e2405010b0c0c0d08040509010b030f070804120309050c060406020609060c0405010906080a150305030d050f01080c0f06070b190c0201020f07020d06091e1b030c 79
    0x48080070b4546000e0111113486017440a0702040d05002e0881008002418032240c280784245c2d15021104103030016450040b0400c15001c50307450003d0000343c03104080351420750000341454412054403a560025402c40d2080000203007092100e00a58812204407402003034650311810100d450340c00c1203c1c0280801c0780307500290301c26813080e8080d1042c24032a408481c40c8106000014826421980c0980c005900c5281005050001031043c1d035048000c030011305040c01c0c14000040c14500250083c030003044600750007d0750207031054100b4201e04107014a003140040e140c0c20500c1e2680c2c0700007141d084217400d01c1e01054a8090100d60203040342e44482c043c0c079640580108001038100c0a03001c456004e0703c1440040049148074a2803400741e9070382c0385001c0c401d442e50b40342c40c8181c0d64106008029a4418080314444207044421141003a0f0304640610303402c0e0151800c00001c0c00d6807000a04211b00c00b01c0b001e020a800100c440074104c1c01581214589075618000039042e6843d030000510703090750f4910 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 146951196 1250 146949946 146949953
    0x61406030a020a03060305010203180c060301050619030609090809010e0910060309060207020a0e07020d080103030203030f040f05060705091503060a0302010309021c0305040e07020d081504020c06040f060e19 91
    0x90300800243c0d240c04a042c40e9203454446c2660400d440490400f240c90680001c0000b0030001001c0d0070005072400ca05540c5410001031080c0075125441045208015920000707504c130398081400f400c21444200a00340c3c480c203104002d600f108001d28089400401030030081d1924140003031283e55000d92209003142403941c1100500b004e044200d078069028021400140e44005015024100030209400b5600e00f10303100030702c2e1400c00c3d4820020b102c0324600510202c0c1d0b01204aa030702001480407154962994582500c44a80c8c15101424501814003440070310350b440001800620350440baa100300d0030003200701c002140b01c10344803954410401c0c64208015400b81c2c209141c811f000070a02191055020a50301042200c884d0840004600050030f0000c50072032035440ea0071095500c000c002080c01e51070b0150503da009025031f80028541c840e1612660b48580440d90805200380947d0264200b41c0303072283d2101048082290024140180000110b000107480504c0c0c40340e030340c40c4054000d040c4c1c8 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 146952446 1250 146951196 146951201
    0x1009110306271218091807140d0605040302071401020c0315100b0403030c060507030221060301021308060a060b09030a03050904110f13090605010c0813080a080d061406030a 76
    0x100110941c09007800405015078440054840d1840e00a030f01c40741880d1070020405c003407a006048900b40011284424100c00700042c00d01c0035104011080c52020fa146070004548448070100288001e00b401c0c01c000400d40e0105105048654041e0300c1804940040010798640080444503038041e400400c04d80a507500c0c21701315a410001c2d61811400c9192144c2c03041c1c11984c0150030035400b0401c008491000c200262090f20f500c240549002c504209469005695030010289100100c900d4030000c510203681c20750485001100b4a03840408859440d800507880d104112052112507141040c0040c3d643c29150071108031100041c0a40580d40c601d580a9401d50042215203400503078038545920007030b901b00010240196034403d800c1d00c0e150404d40101d02c10001d504290350b007038241401007003d0798220ba031500c0c0d10359000d030000e07440d1604031500da502c0c0e00440e07025141c00d12441850805000b1150024600b072040903106019460700d955480c003130a54000d503095001042000018040300d4140e = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 146953696 1250 146952446 146952511
    0x15081b12070e070909050609040201030917041401020c0d080f1c06090212130b1519030308040317010b031b0903070e010f120503070602030601020f1009110306 70
    0x1845400510198034800e4505a507940210b12000328500c1807002c110b80003128180200044c1c107041c0a2440c3c0760012500c091130242c8000c0c181621401c240f810090000a81c40c036500b9155102511240d4a4154041003128004420b0260040340050840f900b4081d904200b80b507008020103260282505504e085640a0b41e60f01004a040d5007117a4911a07440c01048010070001c2c00c00b6895104100d94206440005482120b2190380781d00f05d2070012b081e0700010381d400500301d810801e441d4640804100c05951229511406804900b0701104140e0880f07100c60145006c1d81e211121189000502d2030310701d00030700a50381c0006040c000105a2a444c1802c111010140e00810781880b0903200441d00c2c2c1081d640200160000c100c00621089000c50714620060141d44580075242e0702a031202600c0f440b901c05d000d4406500000041c183d0f90081141c140d4034842241201c105c090b010388000020541c100c0e040300d04187c0b18440d0741c0d482c540060020b0050850011500080505049a841140c41c5 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 146954946 1250 146953696 146953699
    0x1110c19080111030105010e01020a03090603051003020628020303010e1b1c060501120207020604090207170a080405010c030e0d0c060608030d09060e070f03080c03090405090a0615081b 81
    0x540c0411400000e015111245509020068503941860005000034103a0030b4020b04643c0071603003c07004254449030403c1202c1c91400e0004003500c8650300d9140b0014180c0029420100000d604260030101e04a1804402c035500362000519401000403070f01e0788002c0c81030705440b20080d070204000540380d40004140c0c20061001d1440d02d40342141010011200002c91020706d955030004020079600603520095801d00450304618005c0580c3c0024140e005602803995080e902080c00e400b00481d1520301c00f400d01090031a40c3d00c0741030909009100c80b90407a800c8a0550801310131002150290041c4420951090045e002c1d02c0c80c3d00d4801c544d501c0b0103540903205140c8840d00001c032100144010404003c102030f01043d00091402c118060701c1d032100d510200f81d48004410450361031740b126040c0659a000f14002d685040400d403203032445c01900d98080c0e01c180361005000d402c080001d0f84400c410b11841d002d0005060b8800000c1c10040307603106850081c0c104850070b03807440078a5100e003002d1000 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 146956196 1250 146954946 146954989
    0x1217090609040c02060414030f04140303040b070c031502090a06051606050c042c19020f04171006080c060a090b0a020105010e0a0c020a381501110c 65
    0x403480020742036840c20180d880140e00b000c8141300522001f480311100f103850100041d45001c003005144446031049104842c9840e61800710f0707013031958081c421640181000e18040ba1201c0150074140c00e420500d100443c1c0c6252142941c00c03804141d8002d0f120202401000c00c10101e00e004800d0710554040382e8802861840402c0c94000a021446218028100c0c80a200e07241d078104050003601c405040010710403080c200030800900901400c4250340f001071846e102c0f2040c0d440103c1e0030040e00414428102c58080030802051102d03040f40c030021103400913821282c01c2060014944100d0344030740180d0101e80c01150120311603050240061882d81c0d694500309115130342d5401c3d11201500b01400c002c0c0180d44440042080320b1542c20080e4116400a00802903446d000e007000c0d6841000010080503000381012031043c55a515180491050121181e103072441c5191a80843c40c000071074032464403150320007001709035511507107a503041c01032400d0042c051081c0d001c040050810441039084041d01 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 146957446 1250 146956196 146956207
    0x3021f050909070f020f01021317031c150605210903090402070b0426070201120e1006051c170d020f0a020d03060e070503040308060406090c02060103020a12170906 72
    0x3190000810300c00c80c3c10780e0b1078a0801c640040c0090426030240f5449620340e0050202c100310a8100b610b00045610000c014501004114015411030040f41200407203511004141300a40401b0341009202c1580d1000150070b40c0d4441e2420f84d281d004440c1140480000344e0410f58115034070103025504004007c2c2105d0030b2202c1c0c00002001e0740d1241c4070844092900c0004e0104112070b05101003041880d400035206c501d07021184003400380c09000170282c104a54103102150740e090581c060812100c1d12130644285251090740140505523078410180034a8030088050546940307240040d00440d4481c80c00c1c00114503034a04000103030440c640454045a081104081c2903400400800820140d82c01810781280c1d8914054111140359004041102400042000c081d40c0503040780c2d405641818440c2c003580f030b0318010800070501342d00810042803802241140d6039800180c02070407280300b00c900a00060710303102c580d0320b4406001310090200a424542081b80e42c0310380060480030001900090802 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 146958696 1250 146957446 146957449
    0x30f01020a210203011a030c040e010611070b0a05040b0d1823060606120a090804120c080313060518060d020a030c0c080412020d0609060e0f010603021f0509 69
    0x268044092807001c50304001c2d1004014821800c48041c84030302010031815585064080746180400007000c0071701c40f130300000058100c00f0800650340504100c1480d55520f40e121040a04400320744520340c221031081c4840050300e50810012100800d00c1e90b601c4a08091074210504c110340c0111a660100c103441e00709a40c0700210300155850744a000e04002d80d00f02014032506004003030b5000410711140c218000704000e94503603400701c408200d02c0c6040707441903076540c9020074000e01e4a0200204640e00000700022002c404081000034640680072145203207136240300c0160359120384101141c410003550301c00c02900c0d00880c0a49441c1c81c03080d00c0006d40425040006d099580004180711885602007071015005501d0b100d0768031900710604103e880016aa1240b1885019503c991800783c1054160401103481e1030984000c030750780c003031010f00005001d880c180c0042c00b40808004068410941455104101406404110380e000380c0160b4284c1c0601c1d0b6404441031103000842d06012041000d800035 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 146959946 1250 146958696 146958701
    0x30f01020d2c0d08091006060201050a0b01020604021804150501060507151a0f01032301030b10030c0918140606030709020702060d020304030e0d0c05100801140f030f01 74
    0x2821a038500082d4509001d16000445450101d040d07070800202071511096000005011480c410641014901070740d42078540c618040120000008081c20102d0000340c1c036805412207400703008004400c0c0584580e500049036640f2040383c010f58840460850350b856428080c0c103140d00280240c00c0242504003540502094840a074480400600d0004545041c840040410100400c00c180f0502c2012100100304401c80d01d0380c034840b48100c032045402c41c150f038060b41c8040c1040505070400035908000000384d54101c4030911060300c0c410034501c0021442001e4803401025682e02107512900a42807414200080520340c1180d003103034220802d840c020402400100ca0402100c0340100a90b1515005041c01e2a100d81c0c895460317180103000213401a51204140e07100701c002164010b03280c0c0d441d41404c0b14040da120320f07035682186028039010140044040c850080d82d4081c1e802c80100440c0312000c6864036000d100c1e0300c0c40302c403c2e060b00840741d10304030703000b040d031602c000b4111540b01901c8000c0a08 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 146961196 1250 146959946 146959957
    0xb06041502030a0906030204050f040e0c030111190807140a020705130c02010f05090d0e0303040905010f060915170402011e0302090f030321071106010b040e06030601050a050f030f0102 81
    0x759101003002041244d204c0c080d0409003009203015800d25251101055641012a0940307115907142c1e80d0002c004074007002084502d03080100244100c0c0110703d411186070380007001c080e41c0c200b40000c54080d40340c080c45000b40140d031103503614010002c55501095140d00700b010503500714041c0350301c00034040e6160621800c038180c020000190040700f0500c044d0031140980101a03056050200304030b2170351400303e0842d4010a883c20041d50326104040040d0541c49650464008246024000325192500030a00410b03251aa00d90302d0304d05880b00e40421041d559402c0400004490135074080e075401ca10b5010581251041c10043e02d00e80d542c5c82040040a803241c281e10000e0381c082005003291511407072440b400241500514504030020f0003078480c0a00e00c4024144800d004001320f80e20602c01c124988081580314142c81007941c650840c15440d0348588560303246504100c000c68164540454401d0403908003c141400003480d010034030035940b05800c0c00700c3c1d00d40950030020b000325000707000509 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 146962446 1250 146961196 146961239
    0x308071e0b070503060111010b01020c0d03020f010c020a03120b241c020901090b030118180606080d0905042306010203090414040b010605031006030b15120f0a1e0b0604 74
    0xf0f403249403507000104007028540802c401f580c10300c0c401d603020b640c01013214082914140ca802c00c081c25142026071400021022042856190820101035640d0228540e088240b1940c5d0703581c429040e00800c94241c5042140403030b0300c8a885d0709110803600028881c15803000d80200142e0400d8107101c49800c54442c1c183c4880c10707031900000e0746520303907a00001c4100a400d06140e0107007103505111074035202c0044007042030382107a618401c1411200f441ca450000c05503119a00344482d94079902242d407104804800070010038000b44000c241e82c503048c000c441310304a00b1061568030302d0302c0c125030203804003000d0100c50550104101101aa86450054400e0300785c5030207143d0914100791030180c2002405920a004100b0140300744000c4180d04003d91088904602e00822408184000902c485082440e040004040002e0a0100c1d950b13507400b41780f180c101d0b049050166540d00100009694001d50340c1030f02500e00611520300314100c1e5000781004032000d041c090401d40c450004030340041c0c7c1d41d036214 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 146963696 1250 146962446 146962457
    0x15051e03070306410307031b03030f0f0e0d020a0911040815100303080405070906060807020f030a05070602031803070302030316020a021c020103091704030c0504060308071e0b07 78
    0xd200c0d0854400f0100c11040280698614070b0740704c40940840010a000301c0307a54090120f2003640c241c2d400f00141d001950f04000c045120400c02c0c2d481d000320001c2440210041008035124400c0a0f028203034244800036503441c1ca40009003c03408001c10040a20300c1281d00c010441000f25201603179106600d580311700601d900c0d40d5642409401440c0c0048080704040980c0c540c4200140f48019107001001c0320703031504005009442c0c0d0b15125042550036080406000e01e849000070b4410b80c0304161901810407a0260b42c0035002500101c0d0b00c900c505056040801c208008410010703259600645d80581c4240da4180064520a4001d0841c0c0c0141003e6006a07c080203006420764072a40b03100700c05104d80010417589407181c1c0496091000040c0b1550742d100a007000d01d0942e40aa0025107071140d100c0c0821000b45582a1030800720781190006070780307441e00c420000c140c030f00303152042d0f800faa600010640c0c1070101982c0c8401d0f5684402415407901c504140050000407481c0b0316007401070011b40c450 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 146964946 1250 146963696 146963699
    0x150f120c20060601050921151509040506010b090d060e0c130e0d0507110904051c0305040816050f0a08030109050f100303030203070509221515051e03070306 69
    0x240d0300c0003107610381000807541065050284582e00002112502c041c03e4038586005003a020030552100908800c210f11030291200f40101d00101c802120710400010016210765400c100504c0b4004804071402419a40842d00500c8040c100f440a40b040700c0002300b060090880036614201070700c042080c0360303000d0303404425003c0d82c1740b910221076041003504285c204132102d050350b1003e035a8400461281c060100c00503241080c8040e01e00d4403285148090040c0da1642841d2030f2071940c1e84da4410076a0680380505003140a02031007405014045c40d00100c4030740c02c000d1500c00c17a401d2031000d510111900d1241c00c9121030000c1d414084103d11030301a240c413907101d602d840d48907801d551000f0618030060034448108506d9800701d00110007034a0b011320b40141c0f00d5680d41008d448034410845a00c0e48485051440010b0a030030300480401844611828801c1000b07421001d139444820303010b086005406502601c10b490f204801922040404c0a0740440c08017401d02c0007003c9034001c0c0e4240d400207840700c20 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 146966196 1250 146964946 146964977
    0xe040221070f030f050d0c030909020a09030807050606031c0503012c0f09070504020c0616050c0703050319170c030712050c071b060f05031302040219030e0106150f120c 74
    0x14035104046d4604103501072806941d401032143c0c849016422000c0d5002c6500406c0c0d62050054002640d0300129250307544925040c220f50702e00c01181c0280c0300b0302c200c19201c05007c2021040604102041c2c80345800c40e406c1008180c07086c0382ea040d0805000b0000c3e005003440c500c2d001845401502e80c00802e402c9400c144003020306000b03568100703d004600400030700303141640020701542e001e100d6507403089a480c0c1c3c2e0f00044400d40b145545110a80c13103003110200600c4000300c001d210003940d2074080c0781d032a03000300780c19104d20580d020119202103010000a000c648480b000350b5018099203810071843d103485484004440c01034410b500c0748035020610400300310708001c4000c1e0480e5600d8861740134070701e045801003881425452000c1081808004207e50044800080584070b80c000c10075905e80502c07850111401d1501e0211400207402c10413044501e00b01840754001345c0302180b80c00c45045024031002c0d50320000d0400c100c410800c40c4100c2482c0810300d441000c412140b942d5404070034180c081e0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 146967446 1250 146966196 146966203
    0x1020304080a1812390819020d1203020d1a1003090b0a0b01050702031b090a06050108130203031207180b09091803040803040f030b010e040221070f030f05 68
    0xa141e20b510204548040c001c0c98880044c0c4000a603000400c0f642400c124202410181c11140c0c0d1001001c80f41c00400c0851107103038407180145d600080032144000080b02c69180d9050060b003020f03400060f80c00c464008110b19a00c04002101d40d4180903140c10050040340046070f6400c84100358003a1113007034054a0789442c161390060b244482c0f4043c0030a10441e12400d140ca0710180c050084c0d1070380e40d001b120311640907109480c400b540041c142c1c1c4000d181c2240d0b00310005005c0368442d02c100e0549000815402c0b20340719500c01e481040e982c0d0306244d520601521001c07010798a00366414481401801c245122418125105880381e0f034401829101d41044d0b01101c05564000407103a890910991007a80c41e4105d02a6001010001e002c200e902580c103100c0c01c0d40f0441d081611540030000303020501101000c00e020443e44698203440b01c03030380d03124804540088181c2d402507101c0040480641800e41c0e118651200c4d40000d01550b1445907140c0c040808000103500454139903103074520300c1e42444000d0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 146968696 1250 146967446 146967467
    0x30c0310080c0a091d030d060801061d06040506010302040b0705100b040207110d0206070b0702011a0402092d030712020306130f03030903051e0c01050115120f0b0301020304080a 78
    0x1d004114200c00800040c00540e018003a03024115950b4025054202c0c1c4215000d180510200503a0741d0703007000c00c10b200e0250140d80101ca130b8660a05000040854603180c0903000a1000122260300340c80f0790f4104000b90102034085410903800381700c0404c880b01100d0040688600c00c0005240c1c0405c101c8100c81a1506611114443c0d4414000c000108494a03180c0f03013032101c1200ca015002d1054400140a402038030f00203801e0604100030803c0b09501580a5919180301c0c0d4841c1400f400d40008100580c451035482c50740001c0080e543d0841011106158035840803a0b6008004086000b00868503201141d481405601d100744891010340c00c090000030780120b20700041c06800d8189880c0c24514046000700201055030700c0749404d05052081043d1444030b08600c4004002c80702d80981100240c11028500c0000c1d407a1000005400d40d100c00320ec500c0c260345484411131483c2c1da1742ca82004180e200c0d115203265858a9990300a59420b10013944514810840c0d5034440750001c6000b01a84d148 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 146969946 1250 146968696 146968709
    0x30c090905070f0b04030201030905030d0203041a13120c05070305100b091501080103021318081b01050609130f06020708071203270302011b0f030b0109050607020909030f030c0310 79
    0x3d032002070142e841404212000e4075021300b40850056458074240d8518482c800020a80510100900040100c4005181c0000503c200d1a0a00b038480070318181c44469006001040020020b0310b10788031034002d0600541180c05034080d0350b01e172541c0e0703120581000c14040c05140141e0341c1c5c0d2098003040c5805064690401c0310006450012245040064007003a01804003912842c5019030044403210070741c028011004c982c000c0c801c2d2644540c0303440c11040d00400c41c00078031801414940340c2054414410305104840c01003440809031034100c680d135014410b4940540d10f00c1c00011400c00030400700d00003405054410303080d09a8800752801c04c4100c08148125072010181072945a113603100b501a111008000c0d00702c581905040a45000c3c0d004000406e26a8201c000c550700c11029280c00c410b84449104842d107007401614450310045820046e50301030b480c0c0c415014440c0c01c0c0581445030721958400c43e4002201d02d41602e01840110540040303541401102000003040f800c10032205240008059 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 146971196 1250 146969946 146969969
    0x730020f0d030f120917250803070f020604020d231e010b1014091309030809010b040c0503130812040503040501140301030803040609051c02060109180305041e030c09090507 76
    0x245640f007005034540078080074541070b00420442031501006500e00a03811080c40714410681c07c1d0318241a090f04101c6014000c90500d060307544a1900108100740701c4c6a0040054841691554502460f5851080e0002140b0766121444448174010480c808c00705072051481e0340e1441380013104074250741c1c5504000e402150740c400d07501c4031180c1041d000a00b40040d503040c0d0303444101171f8020850039125910070000b81805c0103162028590800c500310300950148000b8005540c18006200903250301d400e041c40000d100b000002e1003030a40c03c0d030300041a40724605940c54040c2d4001030201104040d601554a6000000c0400076903810031904080440380c04209400e541c0b46407a1510309010040020345002e0711080a44100681030050310351114000351004444440094000e640b10424012890654501584444460030407540740780101e900d560b489150508106411104080726001811608640c04d40032002800000b565006005408000038480e0101d061152600d00154444e510644 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 146972446 1250 146971196 146971211
    0x60901050406060f03020705010b13020909010506131701060f06020717010515040e10230907030b07200d050a0f110d0c03020c120c030730020f0d030f12 67
    0x44d00941c0c151402c01d418100162201e005062442c0901000c5589680c843c526050b400081c03400c2380d0142c02c00042c00d41d048005d5a0f02d92040c0400c910401e6402100792646000030030000c03d00310300640080210314004149280e494441440700c00c4150862409170300201c0003801101d0200c1c0e0450302c2520198001e12160400340c1c0101000300401c541c80780101d489540c14182120b08100a989204000c0c400300402c0d840f10b51100007001d00d14252100ca82c5600010450400b4000380c403070290b0341c02074800b85480c0c45921098490200341400011040000e102c007926640062001f00d10410b015140c241e034503400c901d4001c00c11046c54003410240041c1c118141d5284400013403007800e560060606404044603030505900c2c0043d00325020354060b4060800c2481800c01041e001c00c018000c0d411651515292400100780f94455015514143c0c61005520358442020720b54803074041c000f070000c600100c03c8002080c08580c00c01b406030046016540c0c0090155841140c401881141020421111 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 146973696 1250 146972446 146972459
    0x405090a0212150915061c051024110a050607020c0f1f030f0b090406140106020a08030f04020d0503030406050412090f0b031807080c040c050309030909040305090301060806060901050406 82
    0x4030002c0c111001c80820303900304050711b80f40c00e0100c4c0c402d80c5c03600c0301650385a840d1a041d400a8201121f0071102800052000251000546e40342524600700c0401005140100101107642080328003d11855108408001001c43c509012040c0124643c0d4090309902030324805004140207201481402000c045505c149c51a0158180303051806161401191091a041d84800079000341c0c208958007e40c0030040c80300300241e07a4402c80e0f1018400b50441016a80c0d042c05a8a80462800c090610282040000c8859218044803076015200800c01d21101405480d607030f1030350300105c40803900c0c60398a030f0500083c40000c42c02580c9921a901e84046164102070b017100741002d6900c2000104840400400c0b9814001c0041703402000a00c4220343c0001d6851600c10340d94450303d40003d0040d071502c095101068800c504591040354a08000d61400b1a00d80074410003500061042e070400c041030018041598080c042c84000380301803401081c450501c9402c116108034180d120912a918089041060 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 146974946 1250 146973696 146973709
    0x31b0804020d02012c040e0c03100b0a23030106050f01171b0a020307060f050402060a050c1615030609021204030f050c01150e130302030301090902060405090a021215 73
    0x30364151103100c422441d9200590702140e08000b41c05040b80c1c443d680c0b10601c84854005403160104480510821456480450712419003400031601908442840b08103400f294100c130198100151101c954107507205204011100014001249850304140700542803900340590006002d0850307426001ca01c1000c0040d00c400000c48140141521600001d03640406030303074002c0b01e59444c0b60f80741a0b5800c81084003e40702d5014400031a055442c000400582401038810688119070203020701e4900240300381c0a80380ca4000c3e0b6803039041d500c42c08038540e194003014020348004041c056203030072400034060b001a003036501540202c008a4414401105904004000355802c6234150a0040d00140a400b04980c14424442c2c0d0b09455824100054118103414000100320303070a001c0420342545500c05260f5070350400590190041c1e10620051200c800c85134050450a44000d10880c5420390760408500710040841b0151000e5138080340f48804c1c00080314040754071140900001f01c0000032203000406 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 146976196 1250 146974946 146974951
    0x30203010e0f07290315030d02010c050904111c1a030109020a090b060d140109060803071a131a0108011d0a03031a031603051e03040905070315080706031b08 69
    0x10750601000080c0c514401d00b81380321035070307460364002590700e00c1d10520421020000c0c12010f80244228100a01118410b104aa100c0e204ca81d90b800c1c60070a190003048043c08035940c1c0b4140d007500800c40450310340020016101907100e14800850112102108082c0078424020303444d0090341000041070041c0e403505042003d5a910550003c0c0c609800c0010405500a100d1481d40300c1d0b1514030200c0d0001204948681241d4850406008454841c90019201e0181c1400107103c2040c0101780d48400551501c2c10743d00810544841d41701541b503469048103582c070740300c52180e0504a00b005200d003182c28002c5801510400161105005508806941e82c3d10500c2010f0308040d031740c070fa100e9a04541ea6200145420004044610505004610240007201d030b110813121480341702d034010b400702001030555034a1240710025501b07040c545042c03440907240007020f01080554400382c490511151000c11400303008148020a112800d0500141c12114801d0b0070180780100c10b960004170300e0b4041c03040c55 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 146977446 1250 146976196 146976209
    0x304031e0c02010f090e011e0b030a1a040e0d0e220e060a05040302030715020913050a14090a032d0f02070906031119030209010803070201031d12071502030c04030203010e0f07 77
    0x103821507231015070481ca82c0e0380e080260701000000c1071004a00864102c02101030142600708042c010240804c002ca0340b481440130015000541102005c170b005070004a2102c001505900e00c035504840f100e40780446102e01469080e5031020f1040041004200c401d074403081e00d040400250400b41c402039640d00602200038400302c10261402c03110f007065019203160701c90181580004a082d4809100504000c49050a645140c100184110140703a401d0f54060880d1402070802c904603070324112052132803a04000229400b02c81d0502445503202146418000c4554684680449040000b42010929442480601e0500d00d0500200b4040070410761a00780483c1c2a1400040080b03402c0303081c002035403003e0b500c00030703020001500601c044002d00269200b40d0707080150001c1c15091103541407081090202641c01091404505000304005110b82c1e40a14060600d00d007054014205a034002c50300c055a40c0303004541042182003d00aa01070307104904060320422129803015503661090f1b10505 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 146978696 1250 146977446 146977469
    0x5030a0b09010209100306030b0615030a0b0a0308030a020306011b05100b01030b040903050301050a060804050a0624081509011407050906070f06060311060a0806060304031e0c02010f090e01 83
    0x550024003d504840c490000641409000121301c00080c0041503144015180c0810503000110207241042c410030110780203100c640e081da00d410004400a20700440d4803500020f80001c0407000c1801e0501442c8114280c0001603903031b2800c03500040041010461000940400c1c0685000296012810a441c002e40030b800061801e82000102c000c0e04215002c01e401070f140c0010102450b0f4480c00840c141e07441965404030003a036510b81144c00143c1100d001c3c10541000d01c81c3c000098590700114401c400c0c6045001c1034240144422041021030791000300d03580d00140c2d50094102030a07409542c80500c401c02045204010056607140b1070000b0664010401c3c001500c101fa070f81c1d10800d86024a0b045100407040355094039206005251500007900c4c103c05502c0440c58600d80a4100c0d000001d01c0e0f550859030ba01e4040c02d00800b0b4201800c110f0510070040c410321904000440d0451105025076a0301100f040a4000074041100428444040000095051120807159001941142c2c1c030010007 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 146979946 1250 146978696 146978701
    0xa150b07110d080703110f03040f05090a200406020606060304050604020f1203070803010f080705060403111f02010504170306011706040908161502130302040b12010e01020d1505030a0b 81
    0x42e45004581c2e800404603040864500185a402903082d00d0042c807101c100c400034126004015903038050381c0302e51280d00c242c00078103009c90300b8140140754021110040c04684100910030f0f00c106880c0920100c15642004a001c00100364100300303260304004144d503442d1550910740c41707090304c40100070301c003070301070f00303054039503c1e4151030b8070003101840300d210b005407030321214540360a1a2070341c006e01ca10101c42038140130104040308041299421100002d100305d10340f525582d6801200e0103009280c96011076000d0100c41700c00c1150402c25044501a4000034140c5011300d03090240030003204a004400d82d0900c10810140d0300301c000300000e211914191140741e607030580010040c0841d00001840b1542c0425099242150800303607550103480350101e080d0650100303840300124061084a0300c1c4080114000300054101540300000451002d00403642648910072614255034864001c0700144c0c2d800603030715684040700d1040d140b200003003603480d050891070440080d640b0016001c0150441044a02 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 146981196 1250 146979946 146979949
    0x130b0a081b04050603091e010f05060a050d03080c21160c0c06031805030703080601081f09020a02010b1e04060905040b040201111606080a050f07020601030809010c1a0a150b0711 78
    0x111003100522500380c0701c03011f44079500f540609900070b20a01c019051001140c007a00d040e0601c4402c1d2000500062220300041e102103d4042c006048034a11070002c0200d1400729294120303481d00088840700c5407806043c0b005221440052504020b02000303401d0003100700181c51020001c04460721854040381424034125080400c08440000030601e106c0041c4400070107410a610501c41c9800340c880c0c9080f40d40b6003100081c2c1c0c2801003030b4404060080e003028003040e501075019180c01546440001405100140490707005014400403003010001e26031203d0007481c050050350082c2c0131054080c4000e04040c0c2d1504e00505004d00000d06000018201c4101d80200700300d070075000c082c1d0400c0028140d6861b41c0240080500355050000a410b0000181102c0e80c10745800f4041c0d1619070081c581c0d030b0720b1907c030440303d60050b00000d810000c1942401000c034201064265814203030060610720750400da00c24030100d030201d4035484419442c2c0d44081000035490001c3d6440150415000c840b50b080000 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 146982446 1250 146981196 146981203
    0x1416030611120109090c17100908090607050609010c140931020301030501110403020d030e011206090209030106080a0b010b0c01020d050c0a02060f010506041703130b0a081b0405060309 81
    0x20b210300c24018140000040d10030f00d0b50402d02c0362900451659a86548403034404504001c2c1140000040e4420780b20109a01082e50101c0c8805004040782c50a04a00e1800115164010001610230754000c4040c040c031040d007803144040402460400a030800e000304041e024074000d90441d10710800e44402c003060030801440d5051400c00f20348a511140d102c1d1070543c14020f410a000a03280d40d03103400c0c2d681d030085064000b01c0d020b5030f07001041c40d0841c0003d540c00b00c80080c061105103041110b06c07400807044000c603000d0071000c0e00c20071101580f074914103010f15003180d41d0b03903004c02e4030350307102d81107200104051180190544501d080c89039950300e888015180a4412403000c0341200f4900400c215101c01c01c04090b0840308456403c0e50011744030000e441001034000c0c00b506034031000401003045014001c568950301610740d8070a5a0404000700c60f0f4000807840ca6004144031075001808914169000c4403096025050900302403c803580e20b80341c90214002c60084501036080000410003014040 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 146983696 1250 146982446 146982457
    0xd030518030d0206040c0506090d02040515040e0a050f010606051204050a020303070b0f06093612091503090309040902030a05101a0d0b1f120b041416030611 69
    0x9021900a0340001c1402544d0b0002182d0540e0030881e141d1011441d1f1a0074001c40d802070500408088070010b080d000c01008200c00b4145207003000f0842005692605ca82c050710341d5003039548000c0d00504c05681025030070408280c00300102a4902403060081c1c5801c40301384d6412401130344480c4059500c074a00b03e454038040c100301a600d803001040c00000c000c00107905612441e03128214095548452060040ca1318040d0b4200c19981d40186203070710564107030301001814800c1d0300340c031190000c400c0b0403043c2400f6034a440c0350040b03040040d8910103401c010800307082d40301c0441d00040c030390b10700340c00590b07103e0051841c00ca00c115210300c103100540d43c0401800c181b80b50003005a82d03a0a100c421400d00130040c460b4518201803c17030794440294604503018455090700120a07640d40d5542109074490581c11301c0c51180290b118030804510111102000655584150081d00160815040c1018188c103050540c04040d4059200e018010519419000407268428000318806a580f1708002d05401035 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 146984946 1250 146983696 146983699
    0x20f03010e09031308060601030b040c021203070e13050106030b0306040f020906130507031b1403040204020f070c060309020306010906080a0311030d0e070302090f010f0b0306010e0405070e040c0206060d030518 92
    0x130000204081c1e001190441c00740c0ca09807810460301440d44c3c18030003521310038107010016800032007805030f00a01c000000e40e4400071518221103201d404000203883c49005105051341c01e540c580042c003482d509482201d015000440040c805444c0507500c1d1150000083d50007401030524a012900340d86604001d1040c5070031241042c00241340c540c0d0001e000344489940101d481d09108000072203031340105011402d58001422461039503445800b800040d42c494804015052020046e2202261140d208c81c4058441c6a0b008034083e2900d004041c50700030b0682240c0f120501e0035600b04034141000a074852000da1505041440401d8032a0117801e500806480303040380c50802591350005400890039409881c406c60720600c041c0c03a0300103100003101c0d00b4060750700802ca488005100720041d070030203160320260500d8408154690080460180c2c3c0c4156045000300b5100044000a8541401a00806a124801050130b031400e1000200900300a0700041d05024001501c046402e82a040ca803994040 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 146986196 1250 146984946 146984977
    0x20a180f02030916050103270c050306010312170f070e0109030b180105250507060204090911040e0109020f01031a191a0901170c0d06031410020f03010e0903 69
    0x1400105191650007004215140c218030343c80c0805d0341d42c024490034080d91030480650480780c44e0112200c804903001e07081a2507c0f5100c8000040b180d40c01c00585000c0d601c00c3d41c042e20905540000541042d4620301007091998141081048440400c04090b40c8520507250558040b400a001611841700d80c0e0005401c940c14501001503450800c840703800c280c59180020003085e0748102c50008001e08400c00c141d1001403030502800b24910030307005072106a01035180149403d40c2e41064408075040540100c8010032050400042440c2512900c3d0881c4006002400501d4082d40001c44032041440045d06140e17032280d9041d88440c40c0800c1014050014042420f4001d0301041d0919040c003c1c4100384680c041c1c101d40146075440c16040e10080c02060312003000a441c480d92615030408014414040c00f07100f40094420034000340100401140211409044036000c014894181005c1c2c01042441c1801000489080e8682804490440d0040302c0c1c4405540c0728031444a04520480e800c1c6000c212 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 146987446 1250 146986196 146986201
    0x9080c0f010c151d0c0d0b04020a0905070e010f0c050c090a110414120714090c0c0d0905030706020304062003120a02041514030403180503030a260103020a180f0203 72
    0x8021380c040d038001d154540c0c2148941c102c8819040d91381ea4100da120340c02652030030000000503074009050790803500c001e009801c1107458107101d101700e03132044440700c001400140d00c1d0f800340d507000411114455003e1038080160103154030b80d42da540e001900c103940a142601c000440b2100158443e0030402d003107003405680c55a540200c10308080c4824003480c03040452281c020615440000c8660845101d0003c00c0b074400b01390070400100c200002c1204005010820115440000c140107a0074600c1c50350b100c94400c0c6003080c044c0f6140c40c04940000055500400042c440d103038001840c08111115040b44060806440d030700141140140c83e5101091400c842c1403003d0714051350040c1056618501031082c69011b407100880b0b1000b140b00c2000c103005020804280802e1080300840e580c035929469000419658001280c916480301007100000381c80507405060300c80110100315036607202d2540c1395a19506503000980c1000d0680301d4010121002d1010018004c06031300200c1d030864800c68219100d1 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 146988696 1250 146987446 146987483
    0x6070c060b0d0503120903090d0f0c090c050304060606080c09040b031006180c0c03050304110409150212010b04080309100210020301030c06230301270609140709080c0f010c 76
    0xa80001038110401401180010b0b9140400000c2c8d542070b88008040d145011003503215448101d03500807095504061040002c508004e00e401a0204075400317507101766507482e2604010049841c107070404020003920710140701c0015113a8094502c206804c0303e000400e121004002841c081092540191361030500c07170002070866405295514113903d5010a205802640703000304e803c4141c40e900200400c0050002c0380124101624081a113080a00005035540c2e850f1039815810356035414421a00c0d0b000a039910b02102c504c0c01380c5006090842c41c80c0d0419040100842d01c900178150598050071101c0384103a0b8092082200d8607001b0401d1000310b43da543c603810058086e1100d4041c110115100354140001140e40c2440000c1c00030010101900310303420100303005a0144001508a40f001c28460b00794101300780c2c1d03c074503402081c000c84002500c0b913011103d4060341000034911000c0c080c50700c0c0100401c0c200031900403100c09040f075004200c0e0038400012b9951008426000c1d14482c2c0502c04030000 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 146989946 1250 146988696 146988703
    0xc0907200601080a12080103030c03080a0e10050a0b0a05030312190515010905030c010909020a020f0f010b0f03030703081f0b0d0603030306120f0f02150705070e0f010806070c060b0d05 81
    0x703050084001d4558034011741380607111310310300b884002c002503032203600d52011912a006040d00700400400c00318680105078087d40c0380940c2510110416070ba91028031034416010310810f014038109550480341145088006900c03405101524040119003100180c406c0c030310240540058240450b040000742000900c50607206624080b090124103683d00104188c030740000c444400240c141e40e940c127100c0c00d003a0020041d4000a0101c019845040031040400805000010b2505504400014040a82010007641caa44441c021303000b5003040040c0b40c0070a502c9a01c10303610134100101c080342452107402c5010307040560ba00071280e110000c03544030403c1d80030f03400020449010355002c1c010683c64040070046d640115100802450041003204001250480510b103601d00040a0001c1504200c80049030b5a1224504480c00d0300900d000340721205a624034960801010300b14003500d5030400e4440341c2d0354513026100c50280002184800c0030000141c0015a0318540580085081c007076a190041c5e4 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 146991196 1250 146989946 146989963
    0x402030717031605030f0a08090d05030f040f11060a031d030a021f0f1407090e06090109051305240c0c0d0f03060504051e0601020c090720060108 64
    0x424040c5100004440118804090441d0500d5024600d040380c0201100c403042d00a6908032118002440f460710340008480c0a40b4900780541c81d809190300e000c000301404d100b04028a141800024424051000c6044c0030050303025034408c1e88640c0e031032058103012031b61004148020740d200d4400070342070b80c0b1144e2540001071088003404d58911000c500c16203140d00e03405104200f80050f403101440c20046c80d2101f20741c0d072054160040008203141445100016a02d1700f02840030200101c005210301954403100d0300c0c00410710502c0390038a0f13042260004040b030406105000c1c0d5281c5800200741c440e081c03030307103003603003141d806012101c0f42c8a00070308211504518007072240d501030341140001e1081c19914101d40408519401070805520b0351402a62502d141d042003108240d9110008160b0343c80e14030403d8080e00352194030300702002c0107540e00002d90300002d145904541101a842025841d4541d00b542c0005d401c1c01c000035800b504c80c0c1b103002e04609043c0d0a903a01d100c0c075400047c441001040041 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 146992446 1250 146991196 146991199
    0x151201060c020405060d020907050703050d1d10061202060d0b120f010e0627070312020c090604090b0a0b030c0a0312020f030a080610050c030c011514010509040c110f060402 76
    0x4170b80d50340080041e44c1d41440c0c40030b5000705090b000941c0c018480c1005180480c031a040407402c4c49102e5060703034100c400c0316503000e0201c0f06024080400b030408015401d0000121070091003072500f020302e44040c07070f100e01c80001c0c01020080b44ca40207043c1c49030455604135601a11003801c4881d10300b10140e86d110b480501c0c3c00701c5c2d460540034113100d510101d00e152041004c038038040c9164407884640c0c01c04582c1140362101c2800b030041d011000400f00100e240d0024001d0740203051050300402000301412000d410984920718114180e000541903103d202d45c80018190001118421940800d00381103100d494581d00c500710f0f034000b00400601ca00710b164032240a6003142c0c000030484400319a00d03c9014010390116001c040020840d1400011103080b0200d02c0c0f50031401d00072004005881d50300846104031880e5180d40c44114015600c490f110020a54945c0c4009005103880002e00544204089c80303000316101d2954161040c021000d18884c000000221044401e25000e41d0344c03140d200b034404a = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 146993696 1250 146992446 146992451
    0xd050a06050906010f0203250b0901020a080a0902010c060b0307120606030506060316031e0807050c040507051c0b040212190506010e300303010b1b06090c151201060c0204 75
    0x9802c3c1c0d40f040341454941e030801d800030f40c134003281e060042c04280741241464100088081002d400500c29502ca2802000e644001585800d600c2201900100c0010640304050380b41142e101c001d40e07802824a01c070300d0f801031000140c01d001500840c0c10080550458584400d040c0094030410a607548120101c034042c00541301c25444100030184c4403010030002c50704050f801c500900207d0480015440500498013482d4045007151780c84a9403600210800d844681181c1e02d0300740c80707042c2805216131000c0240b40031450540000c0040c4405003164414180250b6101d0900b0310585442c0c2c12604036207841c4040c1c92840c544980004040516405100c003100c1c240b4021841550080d442c1c0682d40a0003469102d03210780040d0080c90342150a141b5660f4500c8881c4605018002031005601801e1800025941c5030310100b4010301003a60806081d2095001e28104a040070300131422861604080780c24403110f0b11401103424440c011a502c015200103448000900507400010b07050080703109581c103 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 146994946 1250 146993696 146993701
    0x507120e0714032b020a1203021206010804050607050a021002120601180b03040f03120e0606010e030a0503030c0a05041d0106030f020c070b030711161a1c02070204020d050a060509 79
    0xd01da01ca000c0111000c400703c0e030f40c59000100301085040c002c1004d01c644121140444291504080d4401124030300c4003096001585510f01038130100d50941c00042802d003070301c4a00b0940e0b02c00c0d603640340003002c201c200500407070880b401c14420300c00030526150502c0259256040c90843d004e90090586525010600190120f0343d147d281c03012003011103554404090441d61241c4502c0b0035401001c50803010400c002400007c0c4080704d10030b803840310203050000c0c078080c0b811400142c01d080021010030720a0740000320b508000350b0000204e07603000d0345094495840710040103054909002da81c1003805840294200c5c01d1440c00550038050480d001c0d0340c0c041c05108915002201244a40420750704141c10174001404482d0320700c0019030f044001c502e0f11100600d03802001500b884940300c0d08180b03101c44a40108624600001d04c807001e4001c0750420fa20f064080c1c00c4c89140142090b40e1404030640103e4008155611075055543e5281520030600c6145001381c0404c00070b00160140303038401c080c00000b = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 146996196 1250 146994946 146994949
    0x3010e01050111070501050304110d061b0e240702030601090e1902010c060b0a0503010e0303040501231b0d050f06030f0f030901030207060b0d050d02010c0318060507120e0714 77
    0x51003040042450f02503c0b41d2401e0a0045a09038001841647d1100040e44c400b03102e9204c50600c0045c1c0d902400000426845005100d444034802e40009800c0010f80c0304041044c1e65101c00581d142c002c0c0800010280e000703600040031a004d45000654103006400001600507859040f031540005d08009071075a0f00f02c0b03425480c0d8441031082d40640020098200c020020321194002540f000005002c4d0300300603a01c0b030000c0c2c00c0d21055103200c40250000300c2030000700402402031031283c0c0141c00ea075a184900c040211214041c000300b02c44154010905800310000028080b104000b6075400140b206182510410007414402e4030054000d04c90916000444880401d04001c81103541029501d429600750044020b900000700949a90b40d45030141c0c04540d42d04000359a80500c10f00142070b0100c0d8008002e42195444034001c802d041c10040072480d0b4036504049003c1840d4840000540340c2c44081d003c4aa0484020300b02c0b8105140080e8010085000a02082151625030491120034410710 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 146997446 1250 146996196 146996207
    0x1050406050304060f150902040501090f0e07050f0904060909030e09010609060c141005010e0c03040b06040f1404030e030106060203040f0b0903150f04060e0f060402040b030a1703010e010501 84
    0x114040001c0c8080c004a0002051604901300440b132105000c218130180c040d241d803201d00a036010144a0382d00180400072960444115001002d00040100300245008000010850014501010414002040f001850006082d52034404024108000e5551911034900c014907140c0d0b000d40100700c070740501504030300c7e00d607103040e060302d4041d500d006005280440503109606e2203401150144200b411031000103904200ca42051a80c0c00408101545856041c2d4064200070b010012a81010002c2001107658420315179000401901c00180000f150030080004002d401540d008c40c102040c1403006141c2d2010b140b40c12214118020000700d556444240ea59205610680203001c440d40e504010140810300036200640015081d100c001c0800404007120300310450700c00d03070840c900d20148030074005d03980310b070324242004200240405000740d0282d5680d0031004000074840c070b8580714034000c00c0e103040c080c401d0320f80d911008610b8503d44600c450540781c2c000340598100500d0300400055250f1188 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 146998696 1250 146997446 146997449
    0x603010209310504110f030a0f0f0206040b1804110901080408090103021e040f090911091503030c0102030402040510030201050f0d02090d210306062708011103040c05010504 76
    0x308000b103107040503104080c0c00b8036000d4240b46090b0280764500000e81c0c0601805119500c1a046400c000203081c0410044d040000c0001e17000c0c6c2d014070503210014080001c0c8141464201c2d0144400701402d1002540910660300006250708020a88100045010902d5900214100c800f80310701850b0300c0340d100741c50041d0342c00d072800922102e0100d00840c082c0c90042803001c9043c5005880c10110401e800380c0700691200340b6445010016007004658a4200420301416130301d4400c0c03100c03c03010b40352000c10300500300d50a441400d40101003500d0700c0e0b50b030f24007000c807100203015252140e050030307500380c000c0d0404c940c01e900444c00c102c0010fa000301410729540503258140c448a040c00051080c0390070b2908880c0031851101c0c0c1c00c0142e00b1080c3c1d100d0042401c41031190711041c10040c0c1c6004500440e40c2006544014075061560a01c940390300100454550403500032464243c04141d0010102c2a5055014040c15468041c81644010341c4600031807045000341030400e43c1c16552401160070b8400d5 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 146999946 1250 146998696 146998699
    0xc0503060a1703120f011502010c090b0c010b0a18150303020a1e021906030e01051504180f06090c0e0c0702210706050a030e0c0a05060c07030c0803040e0603010209 72
    0x52203001c1c041c4403025000b108182e005401103e08001034131219403a1054181e940c00c00d100045001040829030340c1c883e200a02c1e40d2071000b0301c40716103031032405000350380c1da802a407143d03200109440140d03070380950008050071001400c01d00c14580c0c2d03201204101003000c882400d20b5050021207501142c0b82d008a5084a50590003040903500c0d1340c41d02111010710a14075100b4102c41c80c80030025981d0081161003100765084640161440d020000c0c040714551141e0030350a90410301000403445100e0070380d0110340403c0d14045038401000b4407895150444c154024114000080a0018020140c0c4180021481982c3d4a141c26886e4010504000c0040720071030710240c0c08000504c01820240580c1905445076941c02c0c11a400c802555400d100300340d00200c1c001180440d04c102116814007680c0d00c01801c04010340000c0305900301103103100351507001d80c0d4010080091502c001e07205c00c02c1140b00458001700b4050310140c54500036a1282d100703108001d27506800da00403e0f100d02c0d042c402c03200c41410 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 147001196 1250 146999946 146999959
    0x30b130603151104090c0e2b12020109081309060506070503030a18021c030207050a080303040b0403090b0d0c35090c10020c120607051e160f05010c050306 68
    0x1155a208006060784440082803103d040c040000c191246000380324014a90ba103441018101042c03d2103902000c41c0c400000c0c401c00d0a408000c100c0003840d985061580203645981051f60426041e03015000c0341d000104071250000328a080d210b00c0503014810f80d07800315814860796036034000f00b2500e40103200028004ac0c01c00c101140340240c940d4040c40c10b2140c01d2078109010400360f00000c0100b0100e01c1d840009600c140f0a141c20180d040c4201c4002e80702c200c480e100310f1418420b4056032404002c02c000d04090030180800e0525006000c64401481e801c000c203075032503000300b001c03202600c170324981d82005c01c0c151000b00e40a06500801080b10402600036003400d480e042001c8680200040c050f20540d001e801c141c4a1182c40c0c0c07283d19407540300603400a04903842ea100c01d004850031584001c9455802074000e210580340e100382140c5e450440403030786031071856280e0540e03a620320680080454021901d842082040500b03a1429181c50140c0700802202c100c80900340c4d090300c0101c1e48258400b5 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 147002446 1250 147001196 147001223
    0x5030301140a0504020c03090a0503032703030d0603080c1018291e01090501050108070f26010611010c1e020717031c02091804030c0210030b130603 65
    0x2000c1c0340c40d00c141100d0060468416a50340d40c00308003241d101402d4600310380c0002500d41d00300d083c1889281c00801c0160011880d2100c0000070b01d00c410701d03c0000d000140042c0080c00125902013040d155a01c0200300100034255072480e00360110f600c0140c6400030f41c000c400810164101318458a070810540003001042205182d4900b200354080d0b9019100804c10000c01d0207032a42c0c0d0200c92071080020781d500b0110114080b0382d10170341a105a201c03520b0b01d414500144038a9911219064016925003844100d04082c068103a401803a146003080380c400740403044520503031007d2040ba040303400ca038035500e01c24111050310301d00380c1d030781c02000401140e65069a00da10034002c240c1d40d200b414407403043e00c0059461b0b46586d20908495149206c0300d5002054000c5280d0749610349400e035020030750003180340141040100d410038540030039120400384084002400d25014ad0010469161f004089010000070079030090020840c002509000c0c003410391440e203800d0740c0d500c80d000903603402110344100714 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 147003696 1250 147002446 147002459
    0x61315060e010e0a150f0f0b07021021090605040c150e0121050903040608060d0c090c03020c030c070e0907180e010608070609080c09130f140a0605040b0a0905030301 73
    0x80c03d0241288034440e07030318900403c0c0c40940d10a120003500c0041410403001c1d24110000081c90260340250450360f004000c00801a0ba4071640405141304030306095004180d8101c41c45216207000d171490f48100c1c00e0584201c04c110503580311300d200c0c0f4400c6d9202070071a5104c0d52210300c03001d018410040481c001c1711044402d580209008800d003040080100b40a1891040650a4400a50b000601c5034008682031028075002412950b004000340e810000084098a0f296214500b5109030051a0b41d9541c03107200f294800c1e011a608292040122607541c5d62114030302d036071080c1511454150600d00000f1802106010502e20300303c810030400440310a10262880740103012a6030800020340d038a0000207840481882048014a442d80300e6001c01843c048003903052400d507070181841507080008010080d150760506400c2640c000c2303c1c1c418807840925200b188400f0b418451012481601c01b51400c010b40c3d80c10151040c2e00c41c450400c115100c0003060416503d10003c000c0050304107000600c45d1 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 147004946 1250 147003696 147003719
    0x10060e0405180706020307020411190f0203040e010b07060e1b01110f06010f062d0e040605040e010e0c03190209101214010e0708030a051803061315060e01 68
    0xb1a150080c0b60b5480800c1c190b1542c5481035940c010400b5030000305200c0c083d441c00344160000142503800c039074580440d0300820400d4400c0d070000380060242411084032420320030810340d006422202040f0032996101e20b4042c1c400e4004031000c6a0060400c2040c02d0300c80b8000c45d0300887ca00d21005180089080d040064540101d14111a001c0341f1401101445007001008124001d008851101108900b030020081420516036502a15041c0c183d640c035441c0298522510b03a1410146004001040c41e400010080c1c10154000c540c00307418240c210030000410361011024040031300860f0b0148641400b03154071580c1d4140ca0425215140c030400e0003608007019420b07807209220441d04c107443d403900c00038105001c465034180c5050f200319400792442c803400d11409142262140084c1401494003d440f643c03031241d200c142c41044030100b2415846d1480034007040d41808000c0c20345404e0315042c00e0030300742c0000c072407029181242101000714002100784207403419600700c40070b408003a03804e01d040c4405 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 147006196 1250 147004946 147004951
    0x15080d20010606050933032511160b03060f0604030f0b0708060f15090604030609060e010513080703030b121605120304060905130e0607050d0510060e0405 68
    0x151200c91022100300c282846034401500c001e485444c0c0301c40341030082c0901c0b02c01240d44001c070503400c071001c0c86080c088400c0c0e0448101124000300d98940d03c0c0742e0090b07500301111140c0e030154030b40d03c40303083c00d07068202c00220300340030b1b201080b907030102c1c04000500e02c408203500c5807a84040302003001c200070742445038451b00c414001500b02480c2c25625612180d1030503039a10107842400300b1005002c41580c0c0041c03110741060b0308581600e0304155103000100c61a485950140e00050001045046501c56000341d400450300303c0c6041150600e142040720240540d00d007100ea05502e01400101c40c0c0501d90f0384031040a4112804600b845603940d02500201100035489901c141042c17452000c55004120f0b0182100c01015032584031841c150521000c0c2c81c1003c1200c0c150b8000380410310003541d200c80101e00721081214035282000d140d22480000b40742a0500810303a02a03401044002e6400c50024040c84801540070012561807100b450391410711401404c0003d084052095064502030308580c0c2c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 147007446 1250 147006196 147006227
    0x914100309020d060b180601050a030c031b090f0603050702070b03060a030804030f02040b01140702090411041d06060303091804110418030806030c1804030c200415080d 74
    0x10700001541c0005446101c40d190480320f41c1c1e1103403030f000400c1c00c0044025189130701c046491a00d034140040040d00501484c40c04c80109680c40507240b10307242c0329420800c07100fa204825114200d5400344000e05c020058001c0039801e40c4260000a0586c0c401d104080c4030b0380c8030740e01900700e00c1d0400c0d015018a070b00240019a22036034018000c00402e40150080006600c59209081108024030620050700c00001c281c9040c00000c1840180c4a1070040444035015070403900a0402c0d510b0b441c00041c585011090346400516017407061515103211101a030151814034210340442d5a601c003016500d00c10142c031607420030303a43d04103c070446c50880341c102d030010710800f820f074400c5042c03402003030031940342d011a50002080e441c0d819040c1a0880c46e0160056000c1d13024052014a06002c0746078844d09012105603c40758000107010b05109401c2125030641c17102c0302c80c0125551024018801c0c7d034040505204130700d0810650750001c40d107040300d81262a010003401010101c260b040c1d486840e100c2c1d0744d0 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 147008696 1250 147007446 147007451
    0x702010e06012c0f1611150405150610121811040b04050903090d030c0b040b01030c0501050307140a260a0b0306010305031c0b030109050d03050709141003 68
    0x51504030003400000d000e414000c50f4003003101406904103206076545500c524105a10005101c1c40020700403420741e0100e9040161040400300c09000c41321520300032564410741c0200d01c031412031258042451790095015404650a40146007100c19108005a03104e03940240045404145540070320741007210850f2100f8001032000b04151014107001000702d00b240e08001038401e0702c4051629108045c1e100f502a03d042102c2e25100200759070f01e105004882d40f1400b40005a00101803007a0111105070354403111041c0982068580747c007510b103082c001110b001029207004201035100f81c060301e00c038503600c1ea50101c0380400e5080201c1c1c0d5500c20707107001c0d00b000000c00760030705901c04480c8c40d8040c445142241d2080e510700301e112041102c2600c101e9034404e0700224010000b003040002981c00f03205102d04d04140c50304008621600400d00c1d4131602c1d4042d421300300300e80c051000101c0e1810301d006050b00c040c04a540c9000303003100d00401a02402d5030700d81441e06800d0706410300c09041022100c550600 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 147009946 1250 147008696 147008711
    0x190f02010306030f0f050106080703111c14030a0e0d11010c050c040e0c030d05190503060402121608101505030405030d0e1c030b010801092d02250201020705010503070201 75
    0x204031402c41c0b81300f0152201c03030001884008000091040c10000d0001101510126003540e890320504481c1c0300c4508d2040d50804400305844280d1503200c114136a02617001d4101c0365440c40d542e40c0747d03000059242d001c1a1f506404800900b005102441c4040d07100103044601c150640c01505e4105003801c05035100c0c4034501283c6042e0b2220302c910070406903500c0080109a0000c02010315224200c2410403c000c1d060000d0807a118210b5151415a0050300302544c403996414040340080c05803460484000340303000140041c1c20751a1807400f4050a540c1d442e5645a611800160b890854a22400c1c1c01c4111591400350560721480245030490b20400a481c40c000f00348002900762141d102095007641c21420011141181c804a801c0c01081642002d1100c2082c8600107404040144502120716444800d0a0f03070480101c1c0d101e94030060701c2240303038120141c4c0f5128200250810364001c10f800d90a1280001c02c078906000c84001240e05030b009020a0342003100449168101078840019903496610 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 147011196 1250 147009946 147009953
    0x40915080613060b06070b0f0c0c120c1509030f09041104030302011e0915090302031e03060112060b041511060108060720070b0a0509060d0902030609190f0201030603 73
    0x69035009800160030081d44450b54103210003290549030b202c0340b09050070004134000521490085070f1101e0444da5000081d5110940388043d40b103405a20040c40c003811110010703290350107000c2c0601e5402c1d00c01310fa0110058000000d45600c0595900405034801d0101d001c5400c1090014103120308090000b00c0c0c1340782244040941ea030825041140541d4440766414035500414a200c00500703418038040c85203c0058071801d0310f600d418801001d540d80c40307008030020b150080013243c0d81c2150031440351301945148a0010110b41058032464001075980b040180100c0f01c500030310083d00d40c02001c0d5440c1c64a0540352054542c801c921400c24001005080a01c11030f05114482c000c3c6001405451700349080741004011100000708148005c0071500c50801c090341c0092842c056506c045c80c0140d4030a88036a081d141801001c103e1640498000b0740040c40f5650341d000581103520a41c21030340240c03550b1a4494981007402550104201c5508080c00800c1040418a211038018100081c4268807903d = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 147012446 1250 147011196 147011203
    0x150a0306030b0f0109051b0306010c0c050d06150605070c050d030c0f031d01050a020c150c0d0914010201050106120b0d0b0c03040311060c070219080303070210060b03060604091508 79
    0x1c65819404250300f00400a041a40c003c0a40c00a92181024100903100769080c00e54080904020f041045800c04e0404001d0ba08103940c026110003024024910303a18942280944001c9005130b05803107041078001519401141500c1ca000c3c1c6c8100c004003d50b05100601c5880d802c0d1070b00c180c0c104403440c24000301048000c5a41c4a9003030107a6213000c1c0800c032a00080c1c1eaa81052010030f4104441040034000b241c0e8040380d62240c03410203c80700d03204042030803007006050040754440d038860300409900502d01500450b251045a0b46001c1c03004990140400590803144240300d5400072840d148a81c01001030320394401030036518010408202140c507500d6181005404681c10b42c0c039020000280820315401902c40c050440f03200c00240300b1450020132003213041c01011402405204154021119041d000c1486000750083d1811a5100c1c90240300c000e548503001d401c80e9820341e1a000300461014801d2044901c1081d000e01514070b000c1c500034801c402010100320500c00079003034a00101d4a0795051 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 147013696 1250 147012446 147012451
    0x30e150c1011040506040b030403030e0d02010903020c0405011401050f0c0105010914060906010e012105090304060f050906030712020c0d050318010e0c0d050712030302030a060501050702150a0306030b 88
    0x44010800c1000008121085481c07810800ba11104184404c11040d40c034070b01141c2c29a010045410380b2a103641c0f42c00d501420202400c0f020fa40140c44e0441540350b8154030044410b8060390032140300c030030088107010441e0302c02c0c01880a00900308991055950107000140040500400c24a10b0300301102c11183c2142c100703810402c10b03141c841641801509111801c0c7e900050100c0b0b040b005420068000b0b003400c05900300d8241841107020b116003911920a103049030460440c03006102c245042222940c403a8041c4c01080c0224601d54421030102d445503096907241d143c05130145113182c0320203030306581c8600c0001d00070030043e401304603680646105100d410380b00d2500b51500e94803410014a40c8117100030850081400740e2501c846040010ba00046214000b142036440c3e80141e602400e2040c02e004140c0c008181030b03000c0102030401c00d907259000314407414009604200d91911400111010311501e40080d40c4298100e071640b4610607110300404030101d42e0300300043d02075965911015541c108 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 147014946 1250 147013696 147013717
    0x60f0908030c03040e010510021b0a050402180411032206020720030d02012304020f03030313020102070e0c03040312060f0315050a02090a0311060d020309101a01020703030e15 77
    0x1203020024005e400b101075000d4442220641d10b8241d14a01c001d640e0f06008482313850360310400142d41029160b400000c0094180030b0000d56076140c04081b44c0c00e4000010365140c0c0101d00e01020704040103203c0d0213490144005111046c0c00d980e0195004035440c0c4120801da881d42d60070080a000194601d450925050b050f080d0095060f012104060070b1103401e841410559040800151031124500f03078540008100400440c3c06849a0002c10355a03400722031200e41512000080c40711040308040e0b40300700300b8800da080b10f01079620303410000e2000754203880c40807800500740041000240540c080c0d0480c04072400000810700e0740e8461a01102c00b159000b910006014003444404003214041c9075032009a146003545400400760204081c0003003803002400b640000288003002d41c0d0740320121400000c000001307544a040594140c0d48071244c200f50047c103245072a039175540c1c40e0300780d40801c0390320913058025200151443c1ca0a560548a0b071702c105034020343c0034001a0800c05843c024148a541 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 147016196 1250 147014946 147014953
    0x30417091c0b060a1d090106080303091501080a081213020a121a010e190207020918162103090b0307090609082107050c0d11040605040510060f0908030c 67
    0x245080c21200007102800d060f0003203243e00d0003405417003140381d801030f04080408030558081c1d031141407440c01006039410a8620780400000e1011500c0001000941c40c00081b441c2006a640c0e0006941d440b4080c203001480c448007400242611080c411080e54800035600700d40c5950b80081d40091807140a03500b0900303400d590424088240841c05848261403042628091019410841d43c0110240700800749185a211a0200c1c0b8884440781c0640e0705040e0302500c503844c01d042500b140060040101d69520441c0300b040c050f80b00703440340006003034200c0341200300710703026038a08070a24003030303c00c810b242030b41440501c080025040b100080114032a902c03d64808415605000004109455960211280f1740c0202e03021202c3d001d4102a80201420000c26140e441080745800d60800030020b4200ea03220740c62041d07500510940621045140f5811181009000c1e00c0e9002c0004a98042e9540840078403618024407101d070048031030310000307449800d0150310142e458103500d181d58803902400b00c4641 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 147017446 1250 147016196 147016249
    0x305090a0b0a030e0a0c14031213060e0402030f07120b0d140705090f070f0e0907020c040509010c0c0807060603021207060801050d02030a0b1f0b030114010306080303041709 76
    0x50341803051484c1040d111010340814109511071030520030980c0101000800440c900ea500c541d02041445440b00c0701d110040d0701c0c0c0b203c0d10807003003d20016101c2e04021a14104040d01e1a00d031610071244075500070820304c00d41da1181481100c40061940d5060080b0b0b548075524441e543d030340d00300c407007415110f1344090032f8103400081d45034240103040d481907000d2b00e190b0003845044134203004d089a000c1c6480c03a00c025482c1c0d03500000c032105c031880003405820946003014082c98580c0031510070304407282038506010b181c4817018498222545400000009098680f500300001c00ca00c00400a03e4005c0030003040b0280c07203800040c8644501440807025070f0000604100160b04070000500401d811039a800d0144180e401081d203d40034240000c0150040f407000030a00c84414141c03103143c2d00801c45449e00c0d2a160f07480400030760b1080c020040940d4045111a54540c4640a24030a440d031280296040d40c40d159200340480000150000754a00c040c0701c01e180a441d84640d9a005a9030210b1824116 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 147018696 1250 147017446 147017467
    0x22103030a060b04030b04060b010e040c0c230a17120c071406190917040801090506010503010203060d030c030504051804061406010516020f0405010906080d020a020a0504090305090a0b 81
    0x82ea01c55000c140c2806050000b0004500e80300c03000c85c2c6c4250454402300314000171100480d0406441c8584c66405072034101c5031340308560720115808856101d60580740d1402c4036207100404035400750f0001c1e000e40d4024000c80c0b000514802144008400001c1c5040c100030002c40a204c0c0c1501c22107200c1c1c504000460440280100700c000303010700c440f2080240240d41002c070200e6110b20701c00d986005005803181515010081141244441000012400c40d201c640f43c0b0800c4d03001c0c0c0900401650755204050012946140601c00c403801003600614800030402c0e150380a13103521a4201341901030206c18800040c95440b00042e04884105052804446240518001c422500802c0e043d6101903034800410065980240803030340075080b62001942401c4c034600c0040c0118001d42501504981010000110300074941c02c0981a0754400c0c043e1a4141c01c103400490740d0350b64442020b0340c0020805420061810258442210107000c2d03d04140f41c2150800824100040c41d80090054900015200c00a = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 147019946 1250 147018696 147018701
    0x20c030a03230108150612010504320304050405071209050106060f0215060609042904060e090601030b060a091404020102070611031c02160b01080606040c0516022103030a 75
    0x2e0054840c0301e04180d41400081603454039074400364100442d055000c10044d41d95001020708640d0050001c0c4498502032805200400c000c0510800340381000c03000d1207000898458505281d225034000b94142880c2c442000080c02010345500e00384105860603040a4400d40200d4078401c1c0900004a1045c2c5059001080302c1407081045003150401403110351102142908290800c108444c800c0c2c6500d42480001c004114138031441d500791005148003180410b04000a10745040d0403541003041e00d6030703080b04900d9040100c0d100302c4150065401800010980c503900341d0407007000303000302d55042c0c1c44050480440301c442c0d4a4400e8460240200011176a042054002409182c5880c03041c0211120740141e6902450704001c4110304000170310303c200d105580c181c1e03001e0700740384070160949001414000740b059001c1c003840919025a000080190400d4045c521400d06980d80b05031425040b400b0202030400380020803640203080300c82c2106071106400701445885014801786940381060003100f002c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 147021196 1250 147019946 147019991
    0x3051c02060c03280b032a030c0d030f031401030b04060b0301021602132a11121207120e011a0d050d0c0606050409060b03190b0c0a03020c030a03 64
    0x104440400411010039001c24003413445442c80004502000e0b01a00f0f071101a00a01810720f40500c00e500b44001030011100a80803482c1d00d074450941e61559550901d40c0301c044401c90290040301c4018007500103445441808500e80103071400040c0e042c0ca201c0c0381a0621420f07407042e140e0070340f194144007e02103d80b15458890104400031440e00007180c0d120512071500c95001303480342098020403500c0d201c1541248003540c00100c20941611845085000680d041c10b2214000410900c1c0356401c0135800a89100107034044000300d030034078401258100d62410010400d90400c9000316280b28000100e010b103003014183e80001058035541c1041d00f800e901121041203200c0c0c04030646c4000801c6c4081401ca0300103a1901d0b003604403184900b4400c014012a0f4422a007191408451030180205640a007600030300c00c90070b450a0006101c00c402e030540b030381d04020b400429098081030303a02003100020b00160f4074904002d81000c2002c0070507030440d0890306480c00030913100c2d5001082100020380c1d020 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 147022446 1250 147021196 147021211
    0x2010507020d080a0e0f0106030f170301030f080d0b03010509010204090b030a02100e0a15020102040614180f21010b031c050307050703031803020a110301020a0804020402090a03051c0206 82
    0x58003901c1e0250003480c80030042e200400d141d41d945c004003120241404212200b806600007031141c02d60f03c1c549501140b241d5441903400000c02d62502004c04003007021a07040f69041480c1c61020350302501c680042d50f005c4120f0140c0d66549401c10340850300c0c00c1c000c55214521010005071901c0c1b400c100d041c01e55800c980880c0c0309402ca10780d0302005985002c1c408031035207064580810010380361008140f00b80c440d60816004d101c012460003440a80c150001e0049d03410960700d03a5242d2010145c805918001d4002c82110030760320032855086410910407160245900602225220341d010700d03051050804280261186d9460340d0780d0240c0380c103040100000280341d1403244440c2600c48107004140b400040c08440400100141400506100740c105504640440c240004045180d290195980360102c000315200303240c03603140400b503103418800d4441c2d40095407100c40183d913541c1d017000000d40c04190b50303d0344a40041e4000c400310b80104200d580b13060a40560008540e59072901a180c11740040190 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 147023696 1250 147022446 147022453
    0x804050f010b01021506030712050601030c060801060c02010c060609090501200f03130f080a02010b01090b130303051e03090a110f0a14010c120509040b0d03090e0c040503030301060503070201050702 87
    0x80d202e030740e002850039040b040c40b1031400d610742c40c0c00c0c0c002410000d19500c10314403403103a03002200074080c001c01d1150480b803040b0b01d06071080e40c0d201c0302030711035800c24400d42010404000ca60310140d40150680901e2900c1104001f03a41c0351141800d40481c2e2030003005440e10ba644000703400100034034003000c84d20810038414403801e015814400e01040d100c001d040c41c04c202000d5016100b082240c200102c00c1c668810700c1d4070307190070072190024001c0c00390684032070000d064000001900c00d040000c5558031001080300c215610300b16182a190b0b984405d141810301d040c4401e40002d00c003640b030041d501660b00d05001e001000302030b052420600b68501001c7e80304491002d441c0d00c469461020000440704036110104101c080308005850110340300c1c202030408040007001c1c0040903480002800040000c603420420350145c0000c1c07206407c50880000c000c5080300c40203002c1c10b200440b0156100080c40000fa1515444402082c1190401ea000901050b80803051017409502030107065484411072005 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 147024946 1250 147023696 147023711
    0x60f0b03040b061c060f09020108060a0f1502030405100f080705120103030c0302100614030f070b220306090c0f05030d200a0606031a070f020a0201051c0c0804050f01 73
    0x21081c01c2c0e40c0203006107216a1000c0c4001c0400700c41a0901c03c21103030420001c00c000300d644c1e000403028014031841240003400c44000101c40e40b034640d14180688264110566034641021102c84141e1079080403441035110030b001c006040d59030701150181d01c120555803c0d00d0382c1d543c44c401404200000e0b20502c00e01009008a8442e9640005020b0449070940b4080e210300c20f41c0e040c10790400d4120383c01d10140364104880440d00b001c01000390b2500c950140d0131140c8012030020f07401d8444210b400369a01102e010440c10b03411141c0f42c2c0e00c20004081701802c0b03000e40c0e5070304da03504000c035003210b001210700f15600c500400420640307a0b1800005c16095014195071746480800a141e0f85103036400b20300004508200d01680e4504000c1e070190640d1082040240984a091050000160022080001000000240f4803621540009820034a990004e01c4d11241590041d54160002422a90640c0c60700307025540d641010300035441d00600301c0d11040001d003400c0c02c0c07060414400f0079070b003070150307040044 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 147026196 1250 147024946 147024953
    0x160819050c061309020c0c1f0c0f0804080601300209130312021201261c020a061e1a1005030a06030206070302240c03040b04051f060f0b0304 62
    0x541031034041080b1003690340d45038200b80d14184110a900600300341c52000c82c801e80321070000101c40401d0320044a00c0c003908200080c40c050000e000d01d04400020310240f01003000500003058443c00349104000007810242c07540039091030201d09034412804a02c0801c5070048103074981c1150312050007502e100d0342d0b240c03040d41c000c2103e00c080a030070845512950b0b200c0d102031621039040d01544281001c020b540c0c0d00c00c005103824040b4130030700078840039118006d03607218011505426000201c1241000e03119500f10034820590441114030f0380303400e5000c1d006d0b500000070300c903108070740031030b082c020010018944103000b40e01220050000c0c3d600380841c80c1a2407000e5601c138548008494401d02d0210ba40303544200c40032001e40144e60009400c0007000c2100401c164010407003800b00f00010807815800b480c580002d02d0140020390312003110403001c1010074041804501043d42c441d00036801c40b14165810004455000c5413005030b03026060742d03142c0a100b44030a0606240c010700c03201e100355056041940703 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 147027446 1250 147026196 147026203
    0x4050601031101050724090210020a0302100b0a050907020f060a0e3009030102040806070c1b140409030302091806010f093c06030f050a0203090604060213030516081905 74
    0x280a411080745c071b1600c1410b1003240d810000d201940902140418411100065038800c1c19100490140c0218200083c0c01c2c4114400c03030b41d640f44001e01c4034041e64509014044481c10240249007140100f000048138000c0401900d40145841c3c2d50004556607103000701e6040885403403141c0c221380860107184120184000d21801c3c0080441c01d4265680c1e12100007034024400d0764090300580c01441c0030081000d4001680c0c2c0030b800d0180400c14043d1300009581c40740c250241c0907405c0309541040d000c400608041e03118080a44c468100149001440000601d29003588214606440e80c1107041046559000b0070040210100703041a4aa1504040c0c040f2100071201d01c48940c00c06542801c4004060f4a4508140021422403880d10594031214014040d1908541c2228070500780340100742e41031560b2003168840c0721044090103050f25681d8922019600441d1170513031400d007000e0301002040c0107000e083c044089110398411000d1400d0191230804080f40042a0a55480c4802d60007052001c03 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 147028696 1250 147027446 147027473
    0x709140609040b07050c0a050106060206090a050304060807030608011803020c030123061504080a0201020106050d0f030c05010e030a030207110f060403031809020412021302041d1e040506010311010507 88
    0x105800000b61340f2a04100c07498080d0740040602ca20450401c08244141903000d071060741c85503800d860306030b40c500301000d0340c0301c0200d03c0041803039004000400259210b8103856400c03001c01c3c80c0210b0388076070740e00d101800c0d580c1c49c4807603d4014100134080f03400c0540400801d40c5c80e60040d0000e00000d1880400c1000076a1100d50a04240005100089040c0d46103032400b4900e00201c056640c4460704c1d1007441d9a540740240f000c902561802d00302040f85d140001007a2010360f403000f0014072146a60340c0807101000c500b00116034541d01d580b001901c0b81000e202070801414580c2d80180c13100b01c1810405a0714505e0000e8034060310364403180112680ba010104d8050329014217166984106284407000b541144d0707404414118808034000c5084441443c00c1008030f40201c40e100c0c007015001d07620744201d101c0e42c0700d03d0540c0131b0344801418103000143d0071030b40c0c0140c0e44c145900d005030981d19901010300080342c04840580041e0b00504c204008a8039403a9042801c3c60101d042002640d035081c42c1c07910742d = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 147029946 1250 147028696 147028703
    0x711070306110c0a050f070801090816050c090c090a0909111c02180601030c02010515010c0206040302030313080f010b131a220b0102161205030d0905070914060904 72
    0x840c4403040150202c50112250f01031400100c9a5051880c00c01d5500c4204001e82014580501c582c009010941401800211604001000c1c82c00c403c0102e140c4920416050489440c05443c1044480d47d4810035010b20590303035030212542c1c0d610940104a003841040d0882070b186882c1608a9006c610190010b1520000640d88980b0050304014060034103411588001e40c01442c0d005802005090502e585021701800c4c3c905015451030b001c000d03400c0c0c03181182c1c08101c0305200a10680707607600c0f81481502540c005046180b800d5100c0c2c021a023940d1148501501440c035242041105400030420b0821414584008101c0860070b140094501000102c0b28031066407660300302d13500d2401121050580c2c450040082c61070f8100c13010324403c00040119090342c00c902d040307100031841d4008545036001c4101034000b503680b507007040d800b0204112414029540352105009404112443d84034103607080d4000c40050609902c0c2010540648441200031300554140c042400700c5074407401c0e4902d4019a0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 147031196 1250 147029946 147029951
    0xa020103051305010504050109060b0906030a08031003060e0303090f070803040e0a0f09030f020706020c0d08030c040e01030f1101030c0c11011211040f0b030c0a052208060f0711070306 81
    0x942c00a0741140d0705100d00094125441c0c10180020000154055040da910503082804040282000c005c51414120b03a90358150b001601e00e000021b4842c802075603c0a032009d90a03400c580c5070b44902c81210001c0c05034104603840002444000201003002040c40d02c9100d0050407130340d08000301c0c84e40700c1c0103038400d001d0404181c00c0400c062400b40c0e0070040184542070010030851308a400d00900704510308180c240540184000420300c24400701764000c0340d07000980383d1001c2401554400086a200401404541100741b0000c10385a890020300c80c02503000c2d543c0501001c0003030410300074039050b03064401e06251515400042c89074000c01c40c0d08100f60040340311010200a100141c849400740d180c1d01d4441031612000a03002100781000c0c1059850550190b1143c90300c03440d0304031642c44183d542502d01c510500154005500c1080280011080d039941d284941c100040c03140c82c3d0f80801d801400241e00908200810b83e00314640555009041d03161400140500458150721161180005004e654 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 147032446 1250 147031196 147031201
    0x4120305060f090c09130b011403061f0801030c091b05070c0503070603060f05060403111207080d0801171b01050c03090d0f0b4006090501020d0b120a02010305 70
    0x1601e409035082c0c0e050002e00700c1483c900e0f00d00142c0300d0940c00070500d50f02c1501642010030b0080198852004031510684034420840d2110404081c0703030308000d01e0150301000c04042d201c4c01e403850007408900940e48d40c80c0c0313130308550541c03411a5401010750030840c0442c6c50102c541a0000701100c1007014182d0605200e43d1b00d00403810688010b5516411985c0c02d445543e400083c1294581e00c400c04850003502600300035501c800801c5124451880058620340c40503000991078600104031518030aa07410032160140c1e611031016080032004e10854021401e070100411a4041e15020521680e401101030030585e4410202d000d00030b049065591704000c0040b0365035010b400c1c100102c440245005080420210103450403024000000300200c8030154110003107040c500c490000c0c2c0801d42441c0102124540c541d40900c0202228820302003492202581c0740c0003c20f4441c8038a40c01c250007400056030f01c2d03940d85070a000782c41000c5043c41c010030b074440c4c40a0707602c01e001c00c2600340b6175424a000308403038 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 147033696 1250 147032446 147032449
    0x2c150a02060f070815040e1209040612023f0a030909090b010b0a020c030307050f0f0601030f0204050c04051c02190b0304110d05030406030204090c03020903030307030c11030c07080f01050412030506 87
    0x800f41c0b1401f03e0041e11801c980020711104c1907002d04001402242c05202c8143c07141014040101240302c000d4002140c0e5400c00d01c190b0001e100e02411f1003201034036040c5040030315042e8055083c1c04041c6083c40d0000c4214009050344540040080c2412850502440146588490101d0014801e0000105010407442c000b14401e0107902d041c110000d040740c0c1c44180c5420250340b16a41aa2940e20500c070b40b491a05130340c003010441904070f0ba0001140c400c50b0340d00f902404081c060042c101c1d042400c0400c0042255510b190005503a80416520b28140c180c0610500102420183c6030641144404000300424041401201c2c2d1190b072100322004c4885025002c030f80200c024120041207400007207000b081343c0360303d42d01910844121250501025031628016022031003081040b5400d900300708002005680031b50081c45100c001840d00d141214028400c035400c41e0405850601a0f8210100420a184080103104026240d480081081d8101a03a40c3c1c01500100b18044081c17684403400240d06 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 147034946 1250 147033696 147033701
    0x4050603030c07030c08011b021207030e10032018040e07030f08070501060906030206070303200f12010515071205040504020406050c06162c150a02060f07081504 71
    0x201d4420100e560300c80d03d80c5816070784d05449025806c403a40c80c00b00300d600c04140000d8031182d0003810350050081b0440b0b494049107640c0c402c1c0d0054052005201e550049511021303100041004a541d002a0000100d000291400111b02410f030440100340300c00d954004640519002c0d000c004c860000d003101400300c00500388285036002034121a2a1120310017803001c40f42c000c0400e58447c0000b001146c0d200d6120204845141c0006504607100b480071400003406540118801409184034a03030a90640075041c055522009080c54100c070003048125181804a188078050b040803a040f852050042a1a400c10b018090740501046442c20a00702c616000d0340443c1c2c082c20000d0801d5585d2501d809003e41158464200e916040c4650303000a205181c41610740c0d0041804d5a03100e130f01100d2140c590115a51100380802d5036044080c01c0720020343d0b81d00d0007809907880d00710002038903030106601c080e0520360000c00e00c5000c80400e6040002d8160302500d05540b03d4201d0b61a00340c0c034403040011400 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 147036196 1250 147034946 147034957
    0x2190510050403031b1107030f030314010803090321071101090b0304030815030303041211010e1606020607051e030a1107050106080c010f0206160e1801050a05090103020108060405060303 82
    0x1080e91520080c40107056050700a07101c0d9080072454258000e08801c0c084401c0c442880720404290000102440058141035250000b680240f80100d80f040c1c1300030340244420400c0c0c0c0600d031264000a5840064101030000030898402c1d11a00b02000603403c0c000c1900c0c1c0300d1813100608041703503503003803640316801580460041e015444032503480b40360520b0090000700d003d560200c01c0d003000501040c0744d89400400c4921030b5a101100001c1c0500900080d1040d0b80641c0e10700d4855500c8522420210750100b20800100c1d0943c8004450701c1c7c0360890203810b0010241c45402008400c10042421110080c1421074034007103c0b03002580c0340c0d611341100c40285801001080c40c440c0001d400c0c400c0c030805400c644242c036103c0d0140c80c2c40c030442e41f0065034031144d02403440c80903800000c0016a40a009000c00a00d18082d05044042e01910381c001031105003d880c141004281311401884181003220048019200a54010078254190b40000c0c2002e000145980d200d50744400002d800c5480600c283d0301c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 147037446 1250 147036196 147036223
    0x3030c070c15030b0301271203063309030314180a03050a0c05040b0307091107020604030b0a1503080706051b041d06040b09041403040b0a03050103051b01021905 71
    0x30b40040380c10a00030301030500035103601d20030742c2021814408000f0107040c2682c4481003070031440149050755140b1002a2803540f11006050382c41c4400102451251400b120070703a2004690080c1d00c00c1180d445192003025610307002003194480703040c03000a403c4030940c20007013a0442d50135250100410411845250304110300d0708aa860340c0c000080200c00620110b11a1184c0401d10141e0b803200d050000b2035400d240540c1e416407108100704035100590f03105100b107003001c0342d40501d001410380110304603a00c06d070700c1120000c1c452020459410f034ac03807080c80b6a544401b000198214915140d600300d50240c0b9002520340b43e5100c010034844004080c8040c1502e400c03c0740c2079201c60b40c0c0d04d04825441941c40011070f00c940e484000035040e2600e485049288000104003410710b03101c41c2c64091440048030780c1e4442a2004110109504000c039001d8005041d0980d8003141660440c5410303818021f403414a49a1000d5000300c032034182ea0080740001c0d4422085840c0b4000800c03a04141b8035050b164403008 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 147038696 1250 147037446 147037469
    0x9060706020903190201091401020708120703090609080709020f09040e0303090c09010803040306111c051602150c0a03091a0106090e04030905011202070209130c06050c03030c070c 79
    0x40100165900a48420b0204030191640d54205840740d00010030400310003070020f0395801c0f090050401210350140b81d08018411541810f8903103c41e2482c14524900c804901a0045603060415034082884806007507613282c1400c0c1d052030328014030f90b603d07041d004000c800b68010481c10700c0c200c4d05600b541e26440000b0814003501d45025050740d1258000d907500011801109034580b05810682c80550403105402c000b54505855511503000601d40c0301030008040e40104140c050050301102c2d14514032500550010301ea090036030010115520355081d20047d03402188144411b00130303400d00c19901081d92601e0a642e5419a4001c0307009145030b19005007446128140111303208150100a4162800d5440b90641039454203075101426608030750003000103d41010500c05940f18a803480e00c21102400098140416a800500c00441c04c55081c1d10038030300030700d40106009901600800510182c181645001061101a5240d1100911000030b1032000150b000c20090041d4102000707047d6032014 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 147039946 1250 147038696 147038707
    0x1f0e06060d09021909050c0f0409050a0605061803010507031e1e090302011a12190f02060c1b0f01200703060213140603010b07060504020301062d0f030209060d06020906 74
    0x31006500600071541c12910b4000040c1c80e080c25401108e480c044031380d48490401d850002141c0103482c005054204250302c4003000506522030401400555241c805010750b06c52080c07040c1801c4400080040d020942040c0003590800701500703843d4440c0008c2003000c600c80395040d00b849082070100d000d8881c850f00d8a0035160a01d43e040d07001c4030701e113a6668074000140c0c0326041045074258200c01000e080b0b40054000010021302d081c0c05040e1a4852008815103134200c1d00000c0d03094010051901c0c5031303040001c081414508c1e1221480806600f1510700f03103104400e00008000018100384011000c66020106540c0441008543c0003540d11000956035845030100b0350240e0301c0188168415100c2103000e91485192203c140e03810395054120080c20710b14503485202c0503000c041d00582c0c055598140c0461480c0141d0b4811020084410040b40084101c44202e82282440e61200e40e0300d406901007400160307994a11a60020011141207903101c0c07613401c15600034420240b2099000e02d001a0 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 147041196 1250 147039946 147039979
    0x203040302030c12062217040503211603030f1b09150e1c020901030501240b0f03040305120106080402010f02011802040c090e01030602031f0e06060d0902 68
    0x104140c920a4040d180c014200320140003142401400714070158000400042110ba00c80300181c50030324849aa10410a1094899500c0541c402003030a4042d00000ba0510840c101009031905800000141095414100415171442d0003414900d0b0841c00040ba40300c01410710940040003100c64480041021518261030b060213100c000d94818041038181e5070004400004081c88011031240380c54620502884104000030380c005880c3e200d003001500d03011000542c0b202410b9034045d512600001072020755200c2c21101801c101045010000740011060000b9024801907a0200707a0b03241c002703903c1c0c0e15245804d42d02d80c0940c5e1132403c0268441c00000072a00c5e4040d402d9405a4000e8a5103a52214200003c9081e10326008902140480d1050804010305003544280f07860000361400005482d280d00c61040000802c0e8002c0c1c448075004400e001d0360030780072119403e2482043c05124405071034056460304902d401030600f0b10480010411444a074850b410900034258020b2000c116000c281d01c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 147042446 1250 147041196 147041203
    0x3010b0405040615020a0303090201110105040c0503061501050d0209210a03081608070e0a081501030204180b01030b0a020412050a0b060411091315170c0301140406020703140a02 78
    0x400d50780b0440c00d15400041020701c21034250743d02003295020780f41c07000281d102031f0050700010400303d041103a82c804030404e069081c032039030380103610074680742c9442403504040519180020701081640c06242c1da00a46980e08241101c000d420810301c056190341070040022042c20f070341250030341c010b4100b04c40485201004911010418032135190002d490b1506003031026602035035206400890580c4010500150146d040f400c01c030b003402401340303180c3c98403269442d01705034180d5804070768898991b005004514086c0540710b40001d542d100c020050ba496200c00c041140e042c80041c000c0000340000c01d090081a40440c1e000c1c02c04030150036001340702d81c98090390b12060150181d4050000700042242842d042c0604c504005d4483c1c400c034208441d100800c0012240a103030b001d100b41c4d07a914280501500701030080000d0000328074001c050301c0001c0e8054200120101014401c1c1d01d405500b544400310701d4900c0e80c000e0f80004005071a22107604d015039240d6010072056800c0c1c403020032500c01050703000 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 147043696 1250 147042446 147042449
    0x1f091b060311030f01031e020406150801080a051e0309060708090f040614040b0f0d05030705060c0901020601030f0317041b0b03060612220803100503060907030206030601031103010b04 81
    0x55404100c0d40042c21040419400140c0740002d6001c0000c004001244e0001d000011a010000310540719016650001d0308840b406e41c86101d070f05ca2115008241243c00c40c40340c0d801400d01502520400689589554507010308401161440d07242c3c11000c40303030fa003041041e681a40f0340a0710b6540d54000b00d052501c6542c21007907a051184421103d221103d041900665044078450f5445c07c08841e034200402c4054070f4508142c94103c060451a02e41d641c1d1a40f00208006020344061513549460f81440ca080c8080201200182c610800010304240d0340000e0a41c112a00704512290845091400b150341c0301d209030241e410a074480b002d1005000544a603610580c2d01001d1070341e1007550700c4c1020720086c0403c88005a100d1000d01204407101000101c146d4041d22000300300220302010300c030100c1035140301c2d1000c0d1010f50000c0704000c2010b807640c200e5005050110010a25403034185c40d115a107108030300000780200c40110109144d83d00a80010082106c101e8080b41c0b2581c548000a81d540c005 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 147044946 1250 147043696 147043709
    0x304030503031f05030d020c0906010507020303271c02010807050403050d030e0d02070b07020613050a12060501050f0303070609150c03020c01141e0c1e03040501140106021f091b 78
    0xf945000541460002100c1400201c05e4001d8402c42e000c080c2000390824004060398103210b402c00800700142d605100034100c820000d000031981e007424182e0052442d07685000c4e1800b401007511310010040400d40640d020300d40c2442c0a01e483c3e40c0315070049400c0e0080781e20003011841842d05da00000c54040d081100c001e20601d040715110700980604a95442e028850142c0b284030400c0024007500784003000304501203100110500e92030790341d000300e0701c610040c1c0c0c844505524002c59076000c11410b80190340c0145000c030748401c9501c140b440001d859126550340200710329500c205c00c20400c441318000d82c2d0004045c00042041e0b0100a001401a45c003035020806254070301409455540352200c6000e000f05d201c00110385542c0d001004161000710003501c41310161409214000160002e50b8490480c0103179a01807030b4036400d19103080ca00351602da1309040448103c2e840180552680064103120402141140603120071202c0840702c000d101039000541211040b89500d05103403600c99009045450 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 147046196 1250 147044946 147045001
    0x312130201080f010b04170708240f040201080a020a1709340b071103070902040305100c2703020a0602010504140d0c0807080d0f0e0d0201020c0a0b09030403050303 72
    0x200c00443c920340c00000d004801000d18288404c4c0501000b0507000c0c642442100c08a440c81910342e81c0d01490941041c4082000a42d40c0e144032030380400200034203805c8150315544c2c010300c0c205540040c01d00400142503c644641c041480d600a51103009403101040107181c0d51003160401c0e02c0c801d070301d4a80180d40400c90410322564500a84021010f1703080ac2420141070200060918140f03113004da01c0008242d5508007001241d9185a03410f0001c82c0080c0410b00c0c005940700d156107041810425811010109a0b00c0e1401c5034004940040c03460340041d1480c10001c20507010216000b600c00100c0e000a074004c13069a4002c56200d405502c2a800345005407102902070302d41a50555130351280c10030013800581900019000a41c408000d0720160b132181421505020740c0a030305008503480c40441050742038039881e54543c1b0b80c40c203000c40d0140f08407520003903280c0300601d5841035903450030070001815810b00d040082e1140760103200b9a4007555000007904d80c1da0808890881007402c264114400c0c001c03 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 147047446 1250 147046196 147046201
    0x1605070b10090c050c19020a03081903110a0c02190815150d150c030e061306050603010212041202030903030c0c190501021f0b03030403060f050f090a0f05031213020108 74
    0x207002c4c406440b031509600c802454030400b032403c0511440d5002e207049820105422003c4000750b01c00000d400321040100501c2c1800e8207185000741507a00400c6041107500c01000220705442d8840000134041e50180c0302560f013140504200383c404406030744800050701070041c443c091261210740d414061a0782c985054200713079100042101e014140c41000301200d02407900c101e4104025080f000c0c1d800850b04000131803084003401c0605056003150b00311141d04580810b1420441d0034402c00b074000905038000c5051039081c0b40460303001c0c080601f0240408140c10069041540b0030000c48419207806415a9214200b40e0610369a52940d040c2c8284101d54508240302c094030722598490486030140d0080103c41079840703252080c0c00440480700c2d03680b9126603680700c11751001c000406c000c5205070b200060543c00d0b001c4080440b42d01400e6900038005103401d20031404c500207045002617420413941ca1001041d4901a89584103486003d14082c01040130092502b50300901c0b540e440f8000e803104602036 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 147048696 1250 147047446 147047471
    0x3060509030f1905042105061f090b040605030102130905160e0108060d02060a20070b1c060e01090b0f040e100b0d020a0e01180902091605070b1009 65
    0x3030240d0180c0550040b0244041200c1d400d040303480314002009400c00600c1c01391510a62000c41506c034084519003c0c4004541d410050100300e45a84a0a002c503004054803403c0005c0d00e01c1d01d40c6200c0d8001c015200da8040e52940e99651008009100080c021548c5001d1a494440c0165042c402c80d11031514100001d41c101fa5950402d05c461412541d401c2008815840199400800074203504d81101c080c0c803200c00143c403040d000302012403050316103d5003203200b03001a0a8042d4032058218017034018900400240e0944000e507060028440300b41804560405807600040505a006448a00c1742d0320000408030071507400900c1807801550f81034582d03904070b000e0005444100100154942c030070200743c0c0803034215600c45c414400c8000c10f0b4041e030501c03070340001d048000d4a81201095001050041102940790103070758480c850030030400d10102c10b0316000a0311404000b031440d00c0400792604c00c21104c520480c00c0fa0f9078160300400440b8603003801142c403910036140740103a06c005441c0c4a00030682 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 147049946 1250 147048696 147048703
    0xf0d091205060c030c0d09030e0301200f031e0c0702090702031216020c03011b110604080a0e0402091809060c12010504020702030f06090109050d050c210f120103060509 74
    0x81d070801d0040c102500c4030918041140d10050030300f4075142044c0000c16510100303001b842e2115001c8c0c0d03a20b103000c2150030101400c40d0100c010301d8071000d03006502480302c2071002c0107507140223400c282100e40344e940e1001d00900043c403201e001094008003d040210800d00c40c2d000c2d0103014004d4400c601190341c2c2c0031060340d90340f1030321482c1c00307940095000041d004501c11281002c1064544155003082c40d91801082c00d6844092a15041e00c3c07800d030040b00b68952014002041e80f050800038086401e05403a95032152183c08a441d080000d0101180801c1e201c640450314034082c040c007009409142c0906d81100082d007a10159083c4c0554004202240c1d0054103451080650407580000c903460801040025849000201d803d80503881150b01e40100502c103c501c10789181001040c0c5042501c1d200d030918044482a0701480020b01c01c5d4020300400184818000003910000818001d0004c050102c5005146201720301c0c1c000021020004480211a141224410741c0b081c0441d45a482e10300d5103 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 147051196 1250 147049946 147049979
    0x9060603141f0915050301140103020904030e0d0c1d010e0108030f090d21020105090303040b01050103150801150503070503030412080310030827040c0912020109080f0d09 75
    0x1c41d510140042000300801038010100c0300c41400c0b14408240c0c1d21940c0000b912800d99100d040c0300c4101a003044141030a00070303c3d0480ba1000282c81c015811036001032861403000e0009801c100c96480b07060025200c1d04546801e40d600a0040c1c804150388610800011103101ea41240812540c4000590600b0340c8810b103051300c400101440c10320401190018444e044411903030303800050354a2060110300451604032004000050103040c6d940c03803480203820748801400d0511340780d200300100404a808900c000741920002d29001c01c0050520014455154007908481c1383c0c2d500c0d006221000003d04d40043e0110750f0180d06560085903a4004c040d101c2c0650701c904110711703403002c0da000c00081c03610008644c4079468210031201c0c6910317a140c0d60050740014a030340c00e60f13003c10343c00089044891040003d5603031040360103112801d80500c1c005c00032410313803141c80140c4028a014604681c011424103010b40070090880c0c052001c410344842c0c2d00c40b02014003401048800001181c0d542541c0005403 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 147052446 1250 147051196 147051221
    0xb1f032310092411040803190c0f08030703140f090f0a08030c0a140403150f05060f0108060607020d0506011e060504060503062e0e030a02031507031404030909060603 73
    0x450f0361040c011112400d018050301c803200d490307445241e095130f4206000034002a106d4180115154448030300c1e00550b0040b800c1248046c010542d0044d4001000c41040c000a49d0b07200501d144c41f074440d40003c1e40580805000c0310a8001da170707401c210354034401c41030643c8200300d07440444102003180d01e6001d4507086441409130215004000040072540600010700d400700c0346207401031303034400030400d030031200d0708150000c41e80e070140b20340d1080784404a4026606101e41121003080641042d030300040c0c2e51500409294148070880000500a07991442556103180d0050f0480d24442c2040c50300e582c4441c424014041500306440007250010151913801c01aa18180c41e41c0b49880d04140c42603c140c6c0004017005c1c4d01801c501e4484441505080180c688405040c0310814405540103016243d00d402c42c20701c0d4000c0c1d00c10b60000c40582c1e40028400a03900924441d0800c0f0f8031144c40440c0034001400840140c45c0c0e442c810703c410903500200303c1c02100d65503c010003100c1e40703c2c14100c0503901c0d00c200b8034 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 147053696 1250 147052446 147052463
    0x13080d020d020a11070f05031b0a050303070605040606141c06020d090f02040c0c02010906080c041d09070621050402041805070306050903120403120e010f0c1b0b1f03231009 76
    0x90b00c0b2781101349244000320000518007903080750350b5000246594428101103905030b4481c1d00b404100000f0b0700452000d400b104400136881c0000002080801012050325800c3e024815444000c0c014540d04450a081000f2002e00c840c40040c2002d42d46c1d01e4600c603089010320310b0f01605c1c20480344241c500e01e514940c140d45004545261401c12110381401a080b184691420000060900c0c0c2c1480c07043c03c10103c0d141c000c41c49140c6a842a030805401d0752091342030040c045400e0310381d01ca0040c100c44441c40002000129a201d50011600408110864100566040c0044400d02400040880c01c403032180d002030103550341b00a40641c50340500c03245020b6050040021400203800ba40e11aa40400024800500100c0020b01ca50070360304030300c03404429240e030381200c06a03042d03005c1d140081401c4080411b083e95000e6980da8800560700500711100003000075507110204613600b90701801140c201c03651000600025800841280e485d010600107485189003454940301207000e0b002c0d800fa00210304 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 147054946 1250 147053696 147053713
    0x3061f0302090c04090504030905011e021c0c080a021515030604080313060f1b080405070b090d05030409020d140402030601030311150c0310060813080d020d020a11070f0503 76
    0xa10040d100301030003903030110009000c00305d10a0490f100f0644598020303030307079019160701d400005441031034040b42c00500320700c0c03c148c5000d44a80005022050303803000d1008030800f464080007221030981d490f90081c0f101c00009080680182e0005510840c60704400030304490b40c441078003a541503210f181f0b040341c01d41c11a1000401007812500030b1607000c0c004200b0b42000e038000d5603d602c02c89444c41030305010075990b40017030369003801c213505400c1e201403141c10541e0319400d10b03498860b561100c511403400c25010002d070b000400d84503404810f4a141c0d00070304494849407100c02d940007a4100c0b141025500b440e01003e25083d04164462074000c41d0003030054800c0c1e0f425524111140150040d00c0c7e8194840d00802c3c588107403028101e144a075000300d828648a0034111000b400da05855404041001742070410f0115400038178246000403503200441c030b81d5030007032105890041d004840e041d000d40c51000c26080e402c0d0780c100407020031904031007094030801070b240c0030f015052540d07074014550150b00c14280c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 147056196 1250 147054946 147054949
    0x20616030504020d02130608010b1c14030906040311090a0209100e04020f0c06061207051f0207090c02060a0b120a021306050603090d020d1706061b0f0a0203061f0302 73
    0xc907802c940050021110001c564012079001c01045d12072542d06940d030790041041c403c0a20560000d214112540640c50308241c150702c401c3d0343c5806010b0882d5140481042c6227560420840740a00800382c42103464640d641024403125440000035806501040001680c40099108070740510700300408100307145509a5045800e0101c038015650403940c00c0002d4202211848040d0580003c81d50003013050303141c10404d111050440159498166011520900c0f2603961012400441041c00c1100102010425004c82c80c1c038000341e00080c500d43c5802c00000220354081074152044114076070501c00900e59005000c0c3d010b002034034194860b00044155401840c084c3d490b5024581a01c00c081000358031000002d281ea4026201440103038051001030038613580500450304810003506060b4202882d5850700c40200c0c07001420039101c1d08001035880e40300794084078a4003c1c0480c0000311801c041c044640c15079502d211100c180e1007441854005004005045030040007000c200b500c00d4140ca1540c2d0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 147057446 1250 147056196 147056201
    0xc090c030106020f0304030c1502070f080109051501150c030201020f04061d010f050301050f0f1c1a0105030d030e0f0f030d5a0f06050409390803180102061603 70
    0x801504500440c40e0018001201d050330101400b541d10001034000b0007071420a01c0d004030754281c0c0c0c201610f4080100700500c0e02c40c42c003031013035999800c152402d403544d490100d0080c41503910b80550400003140118070a94050340b82041a0503007801501501040001950f45240390721441000840800050042c1c0c10018006981200003401c0c060f000081000000ca141000400c00740000206104038030622555400c88006000e06505801c00c550502001c070303480d07444030350f9081b0905840349869101c54004100e5903164032007003070503250308601040f10b0304d807030f58031000450590034202144120a0440f00002c10410042c03c0c00c60502812440a05208101d442d40c3d03140c00c05847c1a02c05214402c81e05002c02d4440c400728000401503a00c02aa004a80706600054025441c21840400280001407860031030249084840400c1000c008801d080a100b944401c10b4141507420020308030100002405021f07800709405158002d144004907039420049a07030f0041e004078003000d503a080d070080c4d = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 147058696 1250 147057446 147057479
    0x302161e0204020706140718140d0f140c2b03020f060f0703061205030a0c0501021e070b1b04060c060f0c02030a030c0207050f040b030c090c030106020f0304030c 71
    0x9200e040000c40031900000d00301d8004c1c0343c06580054584480d6010048404d81c141d60200303e038285030303000b262540f11003600301e4141d0181081d4584010191941699041101603600798050000100c5007102e160000443da803c1440d03181a109104502030180b030311811100607015003c44c0500302071101c1c0c0c404000021840c4094055000b103003106280311105112992294104005042c82810320850080032a6100d5020b400c0b0030300700005903000035501104540c1020034900d82003041c0d0400e400d00a009120b1650012103080c1c008200100280120024100282c01803070042c031150385001003242c18011180ca20281c40d5400c00c0b0611015002d43d025844071400351100048100244820b942154130f2090204003581c004100c61042c1d42d0326000b040f00100301d520152061516140100b440c02c1c0c544151b843c42691540002c4809480411113840010002010540c1c5400d00b802c030343e1404e034001e002c1c1d2340c01805005551106200c00104803004c4940c440e252001c158903266140501c0d0404 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 147059946 1250 147058696 147058733
    0x61208180409030c051002030408091009150f031a011416060c2d080a020a020114040f050706080603060a0209040e0a030822080403020103020901090909081207030216 73
    0x24008100a40c5542c4181c009140c443d499034040b0000500708185000c0c000703840500c403036004208000c0014455816a1300c01c000c15035a0849c182c0c8800b03410399101c1141d030008200c01140c50040d00e000c0e41d004403600e90800441c0ca00700b102c51518000d0b9410040c2c140ba59901091005680d01d030321112040c02800d41c06217103800b0810406040c0c1d41e00c0260b54030600c58400003241001241561240e0503e070151001c00142c4220346021424030142c001e003001044106815404558000c100f03000703401100101321000e1880c1882c2c586842d1580d89209119015580c030b200b01c0201103034660003548200c0c00380000600070301d41548d80c600320074041c0d84080c00c980e81050319410081050030f0100050800700d031280d00c80740c00f40d1815105210200ca032000c104004030820b01808030106800d10110340590f9028a030140c2c1e06c00300500180c494280a90003a00c0e45440c06170214140b15050001d40b168240b8061070355038a0311340340405c81c00d80c0690480341ca0030820007041700000030102049442c0704a02e = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 147061196 1250 147059946 147059977
    0x7020a0e04080c030a020304030201080c03160e03160906060f0f02030706090812070e0f041401030f03230702153604150905010602070e0a05070302090d050309010909061208 76
    0x82c001040f9041d50000402c440140c1c0c0049818411580c001c0d0b2003592240d640c2503510306501d403030404901c01d800301c1c010003424081000c00c4045292010310020304500c41a11031841c50300c0d41c44e91400010101c600c02c10000a0030358180f080210f01c58214840010029802981400c0c1d003030f00c8000003400303202821162400c2c208203210704002c529256034441d80103a100c501810100400340001c400c000c0c00d4080c400c03450684021032070702c201e081c0d2a054075004414810208201c0c0b07400d0b11101c03140001003400301c030306904e49010303c2e0822005004151007176403420b5450444221070f107802c0c00b5041800c41500b07406042e0000100000e244294508041021094103a4440d808a002c0f00c080e44d0480c5072600c01c00c08280b200c00e4aa0007130900600b2680300525503140740040810101c14080c0c003c1a100362100082220a4801d40680300012001405e6038849401031400f00c0e900e600001001c0d000c91003034840010070b026184200320451b034903140907490b801c2c03641d5a10507142c1d0105555480400703 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 147062446 1250 147061196 147061207
    0xa1e02031e01030803190b18060a03061d070902030106090311041103010612060e0714070606030b0f0901051005030c151b071703180103090f02030d02030a0306060507020a0e0408 78
    0x1d07400740d8098025030190603100e80d01c0c2403038409100309031511890500682c1c10041c242c1825107a1801c1d01c100c08162221004840d200c032400a4901042540003510080c10403802484c003030b0700c500c054602c1d9608801210456030b03850305104141d01091160b4404108402010800300e1001070144003800c100400000e0807002d010f00c401d2580d0000c2c0c12010005050703e00b40071220049224840c003074406001c03003941c24a01001d000305408a00303640740300381c250081440010408c680e04000c000c2c560041c0a11307a01c1c5000c0b0101240e00c0d00480da001841c0d0308080104500d6002030041c40195135001e0044c0070802c541d1000e0051540c1c2441c1c004140500410807540c92100c45411850041d400381c01401c01c0500d0012000d41d01ca816140c000460b130410000544485001000f40039540700c01c0c00e01280e001c00b941051004940c09607000303501030081d072039101591a03000c0001e14081e16030707032003c002c4030b0307203810b0100d070030b07000e0580000e4101d2607040c1d003172205958242050768024481d02a151810 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 147063696 1250 147062446 147062491
    0xe04060f05031603030905060c010e060702010c02120301050f01050c070f0905040605130c0605030c0904151403070605070b0613020d0b0102011a060d02030604060f0609180506090a05150303130e0a1e0203 89
    0x40cc044600030b006075903c41d00400300d180e040c00450300d0701c0e42010301c04c0c1c00c550408001072250800c00080c503050100c0040d150064483c1401400c000700502c01d40804c07001e903946100ca000e050210f80880310240f400b0001582c445c3c4050400680c0c03a081040d881115090801c03c0d55140e001a280c040e082038280684039880d80c403801181012400a13540611080c6415a4080402c6601c01c45500c01c0d044544c044c409640d000059a05171504441a545640c071100c000c02c0f46901c4201110a0843c0005041716071a252500540ea000b0401c0c4e00802a000340901c0f410303035410380d00700c03c01d03401501017180c40d10614180d0080e41d040f0000520011300316550314a941c1d41c18503960700c803102041440f08200b090710404200700c0a40c054514060140f490404005006403100500e02c0050544d40c1e0081608078040100d840d045120190840c4e40c1c0b02140992a605003145101c0e18551290340340006004030510300a80721406050501d451074110290384520203508001e000811009600c00b144025 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 147064946 1250 147063696 147063703
    0x12050a110f0a12050714010c031b0f030c020907050f120a0b0607200a0f0b070317090708011d0a031412070302090103050709080d0507030e04060f05031603030905060c010e 75
    0x801107031414100c0d4810602c0c299085c83c0003035010100302d44555040840903604410414402035043c60304040b05100020402244051840080c05c2c101c41c6001400030140c010080050160007290940300c17598800004858520940078000c1d07240f601840300139403072000c4100c41340d000004240081a007000c1c40d4080b17180d0b6004400c0541e0300d5001080250000003e0884119113180d0a0f03078480200d9040c11000c0440c50320320711039418548070004654080c144900794040700d50384482490a40e9040c806200742c0d40b92218041d900c500e51a00c002d00011020303403160810600c1016014007940403803610199910350081604424110040048034031560340d8404103485009079441c0182c40d820081c00043c00c90300001c7c41e00d0180030b1840001d12003031a00082c941d0444240b4039009585607240e03e0216035a5000080c200d4000d030400d4404911561102d0340f140a4400c154111008812206a02c1410156502c0050003090000300e0511850400b04010221102031070004500b45114005103843e = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 147066196 1250 147064946 147064949
    0x60405030d020c0c10030b09130302030319020c06040309170303060f090403110d0f080c0a0c060b040e0a0606050f01051c02030a0e0a14060105010504030b06060307170109090c12050a110f0a 83
    0x1f5990380484138217181180455401420312500340c810b1801964019581e0711000c2d00c000b0030041009000d0040c0081501201c0c080100c12003510380604052801506064190090142d440c8080350506c8841300300200740c0c0d1191030300500c07413440d214400050201801c0007500950410006c03011207019064100f105802d101d01c55903038540420b030500c00c02403c001000d403800d04050010816030202c02d605c40c0010300d8241d004500010303a4000381d40083c00074040c81101c045603000e914007160503c04158000e008460040d10507502e0743d0380070030044400c1d10412401180b0003410007850f0031110020b82c040e40d40181151000101c0050741400c2c3d80c5003841a0314110b85000140d5900c0744014014007400b40105428282107003041d086984174841d416000b402180121404400038030f0507841021076002a0110381c00c650103c0d6100c1c40e00c4406820424002c3d900c41000348000210001d81c84602d2070b0803074103e405048400401e60701e0056035510746503000e500034240d21b41c03d00c81e56200c5c0800700 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 147067446 1250 147066196 147066229
    0x120904060f030f0c05121b01021603060207200d06180f0602070507050907090504150906060503070e0f0a050904060b0406091a0d05070b0d0e060a050711060405030d020c0c 75
    0x400f021014a4016520010340d0031607401204090398a8050f08400510b942c0c640211410b541d0070300d420780c80100d2a010078001994000e0306040380001c18010b842c2d006014550191080c1a05107400079040558020145003032034106c0c40d00000b61002c40c990354000c0b540740c4201c4450700e068812a403a40a82582d283c00706485060340040c81c041001010813403003004101c15212001c141ca000040905007282e64807881d0701881d15110419241901418420064081c40c0e000b001090b4440b04001c00c9500119043c10200d03190320481c440600d005050003c0c0710384c009088404280c2040103003c1c0803040034000301c07802601c1d44010340a550340e50240c03030003400c807c14001590004040940e4145040120000e000e05009500200400d001054030410307100c090036256550384501c0d41000042400c00b424810070b000744024814690040e400107405405c5070b41d6280b01040310036209a0311903200761001441584200301c4905900800e03005456415404000e4619030380088001c55038110400c4e0481 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 147068696 1250 147067446 147067463
    0x90a02031507051e091804031b030311031e010806060604090c050715020c0106050111030d050702031207090f060f0801060e060f07060917070804180207060c090e0a020c120904060f03 80
    0x40705c1c5802c040307002d9102c403100800940182d040544000c1c002d00d40d09009142481000d450010916000b038000c6400761303820003a2a0360340c2c5407070443c0070b09801c40116100007400c0c1401c00018003140c0080c00600400c0000c0c0954501442d02301003100a10203159810b05125081c003100001c602c10a5000081c415581d03805a5070b01a0002c41c282141c007150013650500000d0300d43c0c2c00000c00c3c008141e07160388000000020f070039116284243d03d075024907000703906220b268108020b06103510031049011a144007510390003a54503400152180b40600d040c0c14000780920f001000742a00c03910808544040103007055152a180210ba5036042c0e000420550705107403100068010410210300c0e48030450515941b40e4200145540c4e095854844c81c8924412112031481d044035005040e811100400e038408410058a810800090310703806c0305205111410074510001952040369008440b8148400c40c05040401001c44484a054000d0020070b50890fa8600004c28441052500d4102650068080 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 147069946 1250 147068696 147068707
    0x207030c06020a05031903110301080c03011109010806041104090204080102040f080703050303070806040b09090d030b0a05011718060702030712030b06090d05010b090c0a0305090a02031507051e 85
    0x504600c0c4150350010742150f00a40e41c3c400424004426511103080e501c0f000400526400b001320040c011804c10078841203000000001c40400c001502c114a404c02c1d4001e112107490041601d0f22405150000d9020071003010000b1114900303984480407502c4c0342c00d6107504050320356905204130381086d00520b2050b035000600b40b000d20150400300005040c4000205413290441d1307106622804040c0c00802800602008034900d0f40da01c1e044415012406482c0381c019203003da0300300f03598410000558020a28214911449003010b903141404e840c0c060b151b04410600d100c0c003401c4644070080540840780c42000c00c0c10000c1d641400258000d030010b0340259215038031400d2401c1041d42c9900c0440515260924440058448609507591800115151186101781303050450140170f0502020b079100c1041810071444004400140900f07070341c10fa800700442c1d502c0280581c0e54680140010350b1550103052820131900484030342a80c00f2001d07180450400e01010304086140300c08d0482d014150303001044 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 147071196 1250 147069946 147069953
    0x60901090b0301200c0f0304080a03050d0e030a05070303051e180109050a120212041d0601020a0f0c0f0509011217070506010e040605072f0304050d0b0a0506030f030306060d1b020703 80
    0xc11106c04103002c0142d0728184c82c000c0816680c203018035000741440f0020074521003222140c1e102440502030f0605903540c13803a203020010301945c030211007100440e01d0240840d62082c1144a9202038120120a203076041d01c410031100031007817686402d05029904c0b5a0b400b0002542485070040462040d6480b4070b07800c030900b00c0a0f0501c8070f0340c150408401c80510040000d01344158240410100ca00c810348095101d4000403410302d85007104c042d01c001d10119440041102d600c2e5003008035171000240c1c0034603544481c20010100c20030304c07442e0040310800c01c150b004141454210b158401d0b0102c0c04900c1d00a46a40d45814400d09130f109001c2d2413800410001401102e0080320b42c001c8586c500100340c1d0b1142c140e41542044018520145003c2c04103c1c0e10501604000311000380c44001d1901054800b00e02e00513a0007402144d400c039030542444081117450a0002d00c1108502201010710306641d00c10041c00f03140d8010020b0085526141e90205c503019030b1840d041191200701da4040e220303a904505 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 147072446 1250 147071196 147071203
    0x10020f21010504060e0c090f0a0e0f0703050106030603051b040603021507030807080424020c0f01060f0501031523060403060c020f0f0a0609050c1f17060901090b0301200c 75
    0x6104003071742244c420810040e11401012a004c0e000111803141d1640309080100d02c2e03050b0070b90441c00e1048007a034140000ca40301c15003000e21582d8240e44c00d00c4070342e0300c5a504505a40440c48000c08981c00a8040180c0825019060046c4480640002006ca6036600002e480c4242c641420a0038103001400400703140c0c2c0108001d038082135030304009405d410980d4a5a181150400c074080c40174001030f1201058030100c0c0c04503811740441000311401d59102142ca14000c0c22544204071100001450015495000b400b840c0c05e8648403080790b20003e0310700010a030ba0342007045440c1034090200c0005144654403040504041c43c0141000034010011300030103032400c803844114038040d62040c000146550000641c03022802da1000010442e042c00d403810b00c0ca000210101d4640c0031000030480c1455261007001c148200c03859980304003030030301c11307005145400d20305846498100300d442c0c0061000d906d840e00f10290313040b400f5000040340e4485210183c03002c0340300c284245241c640040e000d01c0703403135041 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 147073696 1250 147072446 147072449
    0x40501060902120c0318010e160f060206010b1809010605031515090103110405040c0509010801060305072a06050408090307050402030f2a0a030603060e06040510020f2101050406 78
    0x2841145480840b40c8042040f02c00280100c40c0309034004000f0b88058001d96140a0b00140b100092160005a5a400d903c40800b542e152301c205440c42400560040f070032510b04115400740d005000146d0030300150b60001d9001e45081440701c280c2c00a02002502d175842001d0080c00791b60360303a90312414000781c1b0452150289000300e1003400c1260f030b07c04910341410125640c106003420300080141c095509095a80220307403200343d12a02e050a0a201150020010b00b0121405d903252500380e0b80700c22050302112420345140000442c02c41d444041c0440388048040550084002c4000c0c81c620b582c3c640040e1441107030219030b04040070901c91240d080c200a51400350104540c19810b61600c5281e000c0b002c40001c260780401c114100d40745c84880302c5c0301e100791030480078011107959030404158083c000d0680c0b07210841d500303842d01c44c00b1062002e01044150140c2d5220014214200c0c0c28400180690445543c04403c0c2d24108040424070b203407480d03c1900500748074600822580740008200c2210082d = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 147074946 1250 147073696 147073709
    0x60801060c0209070e0423010303020f0a0f080f04081006060306051e061803060c07050c0a21030509040606021006050613330507020306060613091107021804050106 72
    0x1c80c84400c0107903240e682d1294081d10a2900d686050604400035000d030244041d582d15404035071044032659207648807028143c80c0079400301c0300e11030803400e6001d9072100040e10180c0f00c0441089004001000140102594948501c505040c20340341c5d4401c50806a803004a54801583d0710010000c0c03641500600b0000c0004aa0b221060b8010782c41403071100600303041d103500ca40300000701112201018002d04052200103022207030a03217400300e04005a9440707000156454814090b0810b1540350089910080c0c0d21039000e65205148020021409401c10340802c4040c000144000c900c581c072144100c200030440c0d1b42c01001000d420961407011281c030754111500401c0c041040c040002460405c0d802100c0c031541900c50003840d0785403500209010644101c400018099030748044642c4400074241c418022003e4030301d2511020708200c054402c0104070074041102d0709080280182c2580b10640d009100c04205203400015400612074850600b0300858140fa100103002c14007400b481854041c095 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 147076196 1250 147074946 147074957
    0xa031701150c0f06060e0106030513031b05010906050c040302040615050702060d0b1c060507210c030b182406040b0a020115090b010f02011b0305040507080f0706080106 74
    0x40040a841c401d09507007401080c4281c0d8a120002c2101c000840070b001904603800301300311504c5003060180d09200307204a1b00024181004035541c43c3c0201d84000400e90b050301e41808000f2030164580d20403045000c1a07e40d03550f101d54210100d805030190f1361040d840c02040650352800c510402c421114941c10640301440382d00100d001c00f82c8c104080383d4450703404075461611410703d034000070043c00280e50129000640344d20032030000901455900140c62241c0000d0000da62407a100b00c54021138800035905454000c00c50304100401c90740217281c0204140340100e80b01e40c1c0480815001c032601e25184101d0791400c81002084429084072600014107118100c1a864034007000038210f020718014010b0250b40002c07110300303040c000d500c000500c10041e0a0b00e413005030f0340d6441100070101c14140d60b02140c0f032012402e207494418131401c44486014074281c4174045c62807204030300622006000b1200d034400c00c1000f04441d2030400884000c041aa0011301c03819040200080200d101030707210009008 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 147077446 1250 147076196 147076199
    0x510030218010e060403060e1b031603030305130602030c0903070509040302030909101701060312050a120b0315040b060a060c080a0f18120b070503190b180106020a031701 75
    0x4100800c0381c074504424684822400301540000e41284100c0d8401001903140466040c0040780100c0c20300c2d0103180441100b10706001d14018182c5580d04443c0704c6c01007c24038030052001a01950019070000794064110207854010350780e0300207da02c04d8030108144100854600080d140401c540300291005840b41c0b00b4a0900350303806540d0340606146c451142800c1c00c0080e50744000b440302e94000b0204001e070b0321407001c4802a030368024890b501007950740c8208614680031060284003101c0000c0400d030b0726043c0110040e001c40c0024088080810382c035004043c17915060350311003180075015900400e40a002403c140c1d0400c0560303891a8451414410180c0701000411040c1c0141d0382d0b41e00b070500340490132808a0004580020014210548030a00311130007044006002c1040d08100d482105500507584400b181074500740022560541034025280e041411b5030b14540150340c10440241c9a04003c0403030b4091000ca61100760400401030307124644900034103a01243d40740d416503144100a0165 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 147078696 1250 147077446 147077467
    0xa0611040605040902160c03031e0e0109030f05120406090e0a0644010204140d05070612180b070813021f090b0a03061e0602060609041104060f05100302 67
    0x1d000c2c03803140c1c0b030285034080341b01c610108484214889040d84401c443c88060307100d18010b4903405054409107001c9019882800d0f20f9402a21807030302d0383c00142c461030708042c5107699880c00d0054100c400c9a0354025500462031175043e403405807016103482d455038a42a424074032200d104072030081c041e400840c1003000c100100011600c142000d4101100c05044946c01d2a002e9255945901c2d00f035070601d04411009003600c6019800b410030344840d003481c80400d1410034200180c001c44100050b0080e0404441041141e000d41c440302c030468486d1401081900c14400000245410448140d449411000c10403072484d42c840809070b03100904030119000d075203942e0042036483c400b00d000c0101c54544409003d5101c7d01800207440282451481290395450882d1b00030050001e900c1518046000743d0300301d41c00744600040c00300540308140e004240369a104010450301c1d00002d801aa89840c1c3c3e21021100c640350b5004505c050150352004c81e0340c01c5d140800703001c0c60840302e913114400c2500c140860f03c1c00 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 147079946 1250 147078696 147078707
    0x105040b01050622031104150302030c040507020f010903020a030e01050a0c060f0b03030d020a0305090a030c110d051501080709060803030a0f1410050f0105120703050405010219020a06110406 84
    0x159041a00e0071a203c000120b40f60b0503982c15813012480300d010824000041201c2c441c261001c1204c00d6074203004030b54000041c804489081e000096064100443d120803d0910742d2106910100b41d1044480b41d0200b00001c90840d0a44881034006070003141c0380e07809250300701c11100404036083ca4000c3c5413458007000100510180c0c04010040f91b00d0718050340c50341440713803c0551080001016179540341d0f0410b219400030f5004e60307045000703c1c2c200340004000b6580460340c8003803030f41c064480070300c10040b0780e8804940204024400f40e22108034000500821002c0000610b44240c140050b9860350615844074503001d801d03840342d11594203042c4180859000401549c1c0c2182d510000802c5d04d404494902c4050410108007650000b20700b03040104038031131402e109048403420303280c05886c10440b100440b41031113528415500c00100d0008501110b10a80c440d507440742c0240001401c10b0086818030702c030074101550101c01a413112450342e0070f205561140ca01200f080401c40e07860b29142c030710013420 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 147081196 1250 147079946 147079949
    0xf12080f01181113060801030203060606160b04060612050d08010b0408070314120f040e0108150103260d0e0106090b0a030215040b0a080f0702010b030c060c01110c010b030f0105040b01 81
    0x70b200d915100d000c4425450305003515940075540d038901c0b202e40e0310707003400611640d42440181d02c6071103031402040403414060103c400100341c100c4e12b040105031944a0130038412000c5c0046400300c0d5178400000d401040e9402c01d42d003040c41500034200b500000c50000f07164000c182c2003441e0300301342044104000d410025090701101c0d8021550140b0078880040039040527218581c220301d40e42c0c002004003010901c10f0003030054030600e011080360399803181002d07a500d6a2220089010547c5a001400482c1d0311041400000ca8195255602c007920352880003240e810580d2155465901d6425100980c80d017070141310054000e0a50400101d920000060184250b505c00a40140524441d000c03911403000200c0d0701802c103800c00c29903030b000403200040c40084102d81001c0c072150580c0104803018810f000f005c1d18400c000b4005c0c681110040c3c1005881c3d805090b600020b0340d40d0704800c02c910713401e51016201341c1c1800000051142030750000d060901005900d04900e99140c04100b03c00034805400090 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 147082446 1250 147081196 147081239
    0x10e0a0e01020f0316020709020a140c0309100906020c090903192d0801050f0d150b04180203070e0415020304170c010504060b0a061407050a0f12080f01 67
    0x5840032900c84036402803086840201c45a80000100400034000840722010f02c0c031244e0841300354a9841080500724020805408001450b190b6070083d0048a10082c2122761840c2040e245000c503a0400074508035441080ea401180f030740c44d410030840d5014003410340c40703140c02c0e22880c00070301e07041e000c1c151a482075802c82c1025400f209004000301d4440e0f83c4000d18405030001081283d24442d4688400540310042d250000700140d00118141c14a2002603000e11000341160700800784e503546616034030120070b00082c0b50395940c0100c070000c0d980c2c034050f1000c0007000300800032201c2c030b490050609007a1160050a01e0410b200140f00000341c0c2400b40015061414000686a4480b440e1180e40f0854204050002107400b1800218440042d0b11a6010314424a4104121111001031241c0d080c07042c49800c02007080c544508419400d10784c0200844c03446a400c1d101c01c04a290380c7c10b5141403480c90195031070b0244403002c15050360421041078200c0c078030b030880301d806600d40f0441c0b6209030407600005 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 147083696 1250 147082446 147082451
    0x90304032f0913050d14091315180c0c02010203040e13060e100b0307060c030305060a090e0601030b0c16030c020301090b01080d0e06040e04020d0503070602070602120906010e0a 78
    0x12032a202003992a550a03100a08050150410203401d203084100303503006132420b02580310341000142c00b80d5079082c0c03081203100401741815400b004205507004c0740d0080c2c102051f214110758070f0b60711051001001800031030f2580a010111085060200d4414114480600070003000190150b030300001078078211420b10f070a0b60712070b54a03241001c12000482100034503207810a100301498003008586000d90380900c0004000c514000010503540d480c0703501c51030340811011107000011a1081d0001540164041c19501a4640e51007401003202c050411700b0700300760042e80043c010410300c016a80e03044011100114200884686002d11a2698505c02030601500701c400c0c2c41151000e400100000d03030841072100c0d0303a603913980340d1a40b80d140d03442005000885031045107a030f0b840c0090a0700c06894002050210030350f1a5800c0c03206010816000341c519120510042000920070700003003824a100d0440541c0b507100316215500801030240040070140c00c071030014441c0c00103800c18141d0208202001 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 147084946 1250 147083696 147083753
    0xc150c0f0c0102041e090506010f05190507051603120305010f0b0315191406190305060a030602030702031206030a0b0a180b0103050f063312032109030403 68
    0x16140207226540c000f03010b489605403000911051902e090044914486d014031a170b984400046800b480e10107a82008140280162000c2108401028582181a082c018904800742d210307180f60200c8070600c420540c0f02c41d80144200840070040c0e20b203180c401c0c1001d03c450b5060080184104810f030180700401c803408800540035011620368002012005082142907a490003150034901d51b00b2b0040200d48003035610300c0e401c2c03420494100c540c8201e00340566045040785007421000f0380000750910f9400300e80c6203408404284988011809030205400031951034080480c10601d010005010610135006100b0355000f04090195055210340c8404c40081d1a554411544102140003417002d003040042000110800c40300185070040340840400b283c8895450301044001c074642c00340c0380c42d138042c02c2002c4010941300b072500d10b403414030004044c202441d281c070244038a16040807100d4410071559810000d903442e02c11007016008007014014524060568481d04002e403403183c41c1300ca001894204 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 147086196 1250 147084946 147084967
    0x50a020307030f051c05010302030c030c0a050d050c090702030c060a14070e06190e1302090117100b0d0506040e01020a0e09041406041a01080a021f0201200c150c0f 72
    0x2100c02d50001d5100c1174401c040000200c10040c042400228020f01c240c02d1041c12901e40050751040145000b801400018100410f0000e40d42c05c0903400c850310b00c15880c440300700d5901c0540440c82100c007a80116202c2480084031440c00c400034111791011440e25030100341112012003855808102410301401d00221000894814070400540780030781c03100c4030044c004455001d40d0030288020112001840c900300b130300c5e018080740b00381e0302c4242c00305200b0b040311942c0001c143c0307c00303a000311084408042d45646205c3d403402c0c0d07440620910903560b610410480c95140c284503e802c00403c950007107090100511014081c07003040c900b118412072084001508101e5480046007000401d2411340781c4900703203440d10400110b4020400c070415901100003056403000010050045500101280390705440f052490b5070901210303a01c44210b54032807c0c41d10050800402c400c0b8000600220740341e4921003904043d0420070785148880b0000203010501500e194600181c070165991400d410790303202580d60 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 147087446 1250 147086196 147086207
    0x60601090308042601020a11070e010503030702120a050a0303050603160f0b13030f0809011704080a0807020102120403020304050102100605151b010f150e040b0a0c0e090f0403030606050a020307030f 87
    0x50f13582299800014072010443e400710f160002d020704103044031212a04c400000383c5d586000d0107081c6d0540d0041c80181c000d4507010101e000f1901c00c0605a034050149a10b4560070881086c50a401083d1120280419400c2c00c01800c040e0b1024060340014450034504080c410403250300c030b4a552600049420305804d901303454501c00569000038445046042c51405c5841c40e0001c1514034085080420701150000d82600114800c0d90320040b080d10f811040d01050311010f40180860302150b600b4020381c4140c11070001c519001304e0282e00219106c0c2d18040009141548042200300b4007401c29004011589440c03880c0888400840705850300d40703c0c40701035403120046503c7c03000f01035801c2a10900300030407243d01c6900301c80104014043c8190700c0e0b220600c0102d60682d002800f003442000003805804940d030202050801c5490090380014100340004e204010940b42001c02002e02810f0004258040c440c000003000903041c030360f081c003080c050003a45900800c0030180c1485002031055090b1880381 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 147088696 1250 147087446 147087509
    0x30c14032a03030f04140a08070605030703020304060e0d02070e0c120609061f09080d080103050c01110c06040b0d0501080a030903150f0e0c090f010b0906090312031806060109030804 80
    0x3900c0c07926551b80da4680540341e018000c00500500c0402400f207841c44000c1612401e48a035601c0715888d40e02c566104500a51005105889040e0f683d81700c00010201403120501c07102c0e05500629031282012810540010054807407809298108154407501c011041e2146d40500126021500f0b03035501d03404200300e50904c8210101d00003048098054064100841206644c0190103c5990014800d41503034101d4081c04050041e40c04000c69070460341c403034101d0301c030041850402c2c3d0303a100122101065160300980c2000c0e41056000c5680f040c002414032400d401410200c009210494540d00c001e01100704900000d08034400b40042425242d0494210741c142004d984800c01103240288050340d1900c42088100d8814402c5002050749a4a1520b86d1410790f031295000d0b901d029815420131859034440203481d03405006054408002d884a1030140d88100010710309010310b44100c070341a80c11302d41d00501c01410300501d0a020310100c1c2501054034159134111070650190801182d140308181180e = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 147089946 1250 147088696 147088717
    0xc0f03010209040e070e070c1e020d060c0507150203160c030504030c0b04060f03060807150c020a030308060a06050304030f050315030604121205040f06090813030c14032a0303 77
    0x80100d070f82d0078a1400a085012960010a1a01c43d500c50b007c08440c1000711400190407290301600424840d4920038a50032140d100409090304036265943d85000d1703c0600c80da040c040389020a00310188450b0303041148030b000d80d94500314603610340058004030211100d01035204100c903280d288020140114216400707990801d41c04800560340d07100b01603c43c0e000e4054440000c0721405698540c600a01841d01603510440191007018240710078600c561080f140c4510800401c81c1d290030250f211100b50b200518000d55039103400e440c09001b070000019045c5d20400c20060104100300200341e111560481010f076920b0b10550ba40c03076280c1c001400004003090554140a003009000030400d000b50f101e4000304142d120414900780e068680401c592044401800b0b84604416000c00550594006003403c0e10804032035080040c0c1400c070b084088060b810482e080c1240c07800521024000340c0002c1c0d40b20100320001c01320041c00310340c4011b02e2506801c01d4078010359001d00c003030b85ca6038043c002d540b0004103 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 147091196 1250 147089946 147089951
    0x1208070c080604060f020306030a080c0a080c250303020c0d02131e06060306050102030910031503050106090f060302130905030c03070b0f060a0e150d1e03030b060c0c0f0301020904 79
    0xc44100721a182d403019902191294604068074062282c5402640d01c1420020058000307a0125221542244e11909c40c0a501e0301800070403900040c003001c05401800d1555005203040d4915071160140c00d04029241d85003035003d00c0080000a600182d4089200d000740d90890020312644085030314450091174501c009030501404203960074407401c0c0903810706200c101c01e012440c2d03a28415022104d6038001e4a0041e001000071801608200301c9104045549107000a0710494a005601c00d040140e002102c55035190481040300c00f4103405043d10b003640c0a902040242d20799400030f42d4030521420803105040d1560700010500c0804c0c4103440d1010726100a6986c1c540350361400981100c0c0c121001c0c80c034800d00c500815000d09007500454187d40d06d0030008503154807101c109034850003000074143c0d4820f50084c0703002c000a8003051050348004542258202000707040c5405010fa8601e00301841c00390b80144031416440034000b071080c800d80c50540c1d01904440b410b20200340a44684142c2541150 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 147092446 1250 147091196 147091199
    0x31b0a02031306020a020f091501050f0706110c2812090302060a05040e090109051e0c10170a1b230c060708070302070302030405121501060504060908070803041208070c 74
    0x1340c01044000c0702510032203117000340ca8081810048076940c103031101c0030300709804541011103501400c005c044800254181030700b040d52950303807882500c80c1c030100444a0340020a0480c1000801c0040221000d22a0082c1c0c4118800304485050008000c10140c40301c0c010140c2402028000c0f441040919005403840f555002e030000c028003030703500501c590714041e4100c1000950116040c440d6030851544840901551030084402070728200601e40594003d0140d00c44045403903403050940c500c2500c880d10703081c042640b40000c0e184442ca00400c000e2110341041211503600c003514843c0c00c075210b414141000340000d0350020709006030340000401000000050724400190340090210b00c200c13100d41d601403181e07841305800c8040c1e01a00300d001300907a009010511052410f03088000340300d030551044804140d90114040341055080c2d2000000c80e200003024400d00f51b10114640c00f031b00d54080140000c515018001c1d680b48168070421159000d0306c00800c0400003072604880200c1d4111009450a6 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 147093696 1250 147092446 147092459
    0xe0604150f2408030708030703021c050a09061d210412050a020f1507060c120203131b060203030109180f1401140402030604060c0e19140105031b0a020313 68
    0x201010380ba0940d601040075070002d402d0700c00004440c0e00d181d001309002c0c02c0d502d5000007076020790484401000ca070b08005444c0c619200d124480c80e88100f0700101c002c9840d20103801c00a080740e24003580040e07040c2d00072503440d246210005940003400c4a55400015030703480703503654142500860308003040300305002d503003c01401b9002908100240c02140c101c0e0006c5407003003c01c071200014440c3c2c1e142e241c00c207108441c08a0034640c04544001298100300c41e41c003403044070020407a4401ca840041c6403000802070030030f100c0007420300c0c0b15066050080750503860511401a40d2800148918202c25846118040b40c20544001c000112940046079200013081ca10f403803800344c0480b8100c0c031419172034803031000d6020b601c00003114011a00980506039644403031f11054007402c040c0043d00c00340000210954215120410044e8260301010b805501c2c00b8200f034202e1102c2c503d00000070381009400d00512240d00d88040302482d000c92844400c135030346c444011080c3e046005a012202c100c404141e03002404 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 147094946 1250 147093696 147093731
    0xb04060f1d18010c050913051b0a020106030f0b0405062d0411060712020607050306010f050c0a0213020a090e0606121005040f0509010e07031101180e0103030207030203100e0604150f 80
    0x2c40880341c80c415400791211f5041164402c498900030a03002c801c1c4204414844001090b102070b00b0300c008070304c0c1a260340b503184200000300c0081ba45540c070341c410030051120a02895800441d803c800f911402d810114030424442020342d0390b04070b14880400710302005000500401e8040d009001291100042c0c14100e921604d1030a040015000d41c4000905043c880d0003181c0c1f040c40161a002112008400112610317004070884412521456a1010150f951201e05501d02040350750056990700c9144001004071142e68002c2c0b035036842c910207220b4030b6628001070710014403003550740040941c6c50741d00040b4108103603406680c0081c07070071090501c0070f4502e420440c81842d0200c024481c0003060b010721039941c2c2983c440900024044d00c0302d035141e90f2040ba00412400710700c800781229035480e070092103c41c40e400e034001c40260307004010400441c1420700c1090700401ca007920800001081a070002e8640400810040c010a1511403140c0b220356254080c5901c2c1403004001c1120041a00c4d036880b0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 147096196 1250 147094946 147094957
    0x5040609140a0b031905031201080c0f0307030b040f0f1205070228090218041401060e0d05030405040209010c231c0e0603090c130b04060f1d18010c05 66
    0x80d8840701000210460340038000c031451104060014803260103d01c0014a48240c4410226014002004000b00703040c0032a0203640600240d40c003422002006104100c0c1c080c1601d95024001c0c1c1004071f0810100b10100d8103103501a400c000c141140441501d010040e1501c00700c002072420240400d4010125882009013074114421368181c000813001c80c0409035101d031440c1071103013800041181070040040030b8000d0100c41c10120b07000d00345003220400160079031396007500381d482e62500791004101d400d52100c001e0b03c0d40142603d607020001059211261648158041c26008540014509203d82d101c0c0000e001c031940c003c100801600036150100c20746a0a280545802c0e01c6410080c201304800402442900b900c1038031005003180104041c00b81c581c00080124070b1034000c2e45204003140e15520b48580c1c411400000000c2d1440400d000c00044030107e401050300c0d50704c0d0318414442c141440e1006202c1e040701c078030120040c1d5501080d954a0600d5155603090039400e000c484030301c140d0002c02405 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 147097446 1250 147096196 147096221
    0x3020a0e10092703200105041b060f03020702030c06040806040b070203030c1602030703060908040f0906050604030b0a090507090204170319050c0a0c1401020c01020114060103021305040609 83
    0x5424594a2070290305070b4008004800c05492000346690a00000d0145054003511900b0405c3d04002ca5500d00c1c402158000a4555965180c80803c400c200101e000c108052508110f1040142d043c9031004140781c003082103442c20700d0f500042003400d5543c10092861088001089140d81d0340e21010540e4035110184e9046500c040f0034404a0704540c004026284a8481041030b2800c090182016881c2250b0b00b2005903090300480d1008404a07116001300040e060141c1001c1d07554524008180080030066030240030a2403500800748110ba0b105403c660403241c1021088540d070f00c0f05403882004041e62900200144180d140028090550303802a0046a001500d45059808a182019100c0c8244098810305030665007041c0d04641c06200549150002c002c211f030f002113035a135180160301e0105c3c1c000d9810041030110400b495a4104000c02c0b903182c0030b02c02840b00f01c40000222004040182145043c942c0102e00031015054a0300000d00a1900030810721800707603160031a100500c0400c0307005 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 147098696 1250 147097446 147097471
    0x621041112070b0306040c0c060903030b01080112240f06090e010f0203090706110a080c073212010b0315060906060a02030f030a18050d11120306120703020a0e 70
    0xc0e503a030705000c5200000c0321020101c841c91503540e40200310040008000f08014401c40c0d10800c0c001c00d8840c812114801d00ca40c40000d070503200040054040c0c40168011501705500c0a414400140107001140c0300080f2462001c1600d00c01c00d00030b101400d02c0180c1c040c000c44c84c20030009814030003500010b11105000008200c0241c01441d02021381c8801c50328410568003210080218500c100c6107103111003132881c1503c0f0202c81e245d0315400315900048007984960b004c0c000620015004404001c0010769031140c3d0b01d0841c03a110342e1210624108082c3e2032240c003139000c0741d41c1c10260a41010000c0309008080d612000c40384e00c4000d40f01401680c40f980501c21200000b4810305014040b50522030441e00103505040f1450100c0c2c0d020f0b400202451007094035401d0130310401d01000d000b001c045105401921003061000300050000621807071482560b4400c408400040703c0d01c900322a004103090300e0010b0124403482a0602d403560940c8001c0d00216800400a88030b540e450440703000308141d1041 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 147099946 1250 147098696 147098719
    0x30c082704020c120315180901060b091e03100e070e0601090503100504020d14060a0e06010609030f0c0312020609011410060503060f04110a0201180302070506210411 73
    0x9000403030155441c0604554000d204d8803180c0403814010f0340e44441400c609064000402c00131444294401c00006540c81410003841070040c02070254070050981091807038207101039540025007400c0c07600008020100c034010080d007591000d0003500030581c102030090000e100c0d80c60489a4410091155407030413280c00012403031545c4a80409001c54070000c0042202007041d4803240010a400f0384202d070b12102c1c65010344005a1290f2040541c2c252510280c011490040025015140302c00b4030b41d5000e0b00610010306c0f01e240c00c9110001a01c0d081000c00c004007546241480104a00d03400c0178124084410b0030311a410780c000b4200388105100402440844074822030074900410a5411850b55850220184049441140a903500403070080c90f01c440c2103504008a0101e44021031518142e84001426aa4103902400b51a103001051001022003081a49000f503e450541c01054031a010008080d491058003240c600440405074600c002d0600340b80c501080503041400e0321b14010f0340e18019 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 147101196 1250 147099946 147099949
    0x717030403080f0a09020d0b190504200301090204020c0c120307050c0f19060201022d040302010809030417060a05010914152805042d09030c0827 64
    0x699019a6060311420b2a5890302c2d603080c0c608280044c4086422551100a0400760341c3c2d04a4040b81c0382d00450010110b03007800c17000515282c3c400021041d82d242000144000034a100d41c244000e04c00c68001540c00403182e8000038050111610040e5102c1d00100b80d450032482c0c080b5131816034000c1118146400d2131041440d80d240c3c000c051024145030000d00c52189503081500c59010081e0b0000c18002c03a5800140c00c600307a06d56560041d400503980410b40344814404042141c094501c0845100100718020f0445407030b921071400024104000e4601003060200100705172303009404100c1e51a0740c40e1560704250350303881004075520a60241003000004401046210300410300b8041d9200c510349070f582001064821010a444076041982c02625020042c0c82513150b000c1c42e05822400c03070511f071401c020002a1020b803105100003004820340e20445001d60a8100e03e06035a48002051070b0500b0305050340c2e024940c0b000500991000101442c1e00e4141a100f02c0d0300c2c101e0f0414102c4440800340 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 147102446 1250 147101196 147101243
    0x405120c010e01170f19050717060301020906032205070303020c1e010c120203040801110d0f0e030d110405040501030b07030e07060e060d06170f010608010b01080c07020a05041107 79
    0xa44030350000440c400445c1003e40d00410166004888a07040b08078880c28000701e504803441150700000244547c0c0848101c1000540402d403c0340d000ca00035801c0208900000d13013944805845a891410082d4101010748621031800c040e154014082e56411507076820040d494210481081c1d00c640e080c401d010600c514408080c110300344040c3c0d903082c1205240d99900b144800d100e410013040d403000340000500c90030240a906400f60f00e52240c40d032260a84107042007a14075100c001c04940341011308549541c0360004c103480c4212124600485d0803078200030722a42c0d5200e2904103a4100b4101303000413050114040806014501c659001c0000c54810291283c03104214010000001c4041d0607110740c0d4a4007101034100481c28500000e152642c030707440b4045101c0ca401c003550171500304041e1380e000c0700020b00c5000001d000700300090000c0c2a410340001c00071440145240e070030032800310b102c000b0364a8984001001c2c000c060420082c09c410142411150341000000711000c101000c1080d607a0000359 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 147103696 1250 147102446 147102467
    0xd15170c04061a03071107140f090714070609051204060e190b07031101090c03030f090602100903020c030d050409150b0711150403120e01050703140306060405120c010e01 75
    0x780c40305510782400c3c10364000740307502c05040c1d0020400390404131404400705114400040403413004034107500e4250710600005175041009103100b4184c0000704103c0030741110480490f0340d88040c900d030350783e54036140c0364004003407c200180c080c1c850300c000c00203a000f010005000365501510381c0b40b60807001c8820000d06e40d070451034882500410300d5041200703400100140640b58460f00f4825000e00360194290f00b100c904410070740b100b0b00d0f140d1081040c950040361400340e032891480c2c540800d60038260080c0d682c980190948c1703011030f0340740c0d01d05080c180b080c0525582c03100010f00b40c0e4004d41002000a2540d00f1034060302c8501c0340351101c40d0010a418484903002c4400b45050b807070901c809600e80d0a01000303001d4140780c000508c003014402d200c0212008002641c8115000602403401c0340004218484e00c203815414003504102070400310b608075030b07034600c404c240182c101d56a13540c601c0892814000c990110f03070000f0700c01c0c04140010301e01180c074040041080e0b84280703046075102d00454400410 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 147104946 1250 147103696 147103709
    0x111507240902010e090a02040e090109020f030a11010c150e0a020f0109060c021201090804030b10060914120f10020c010e01050f040f0206070803040b070806190b0d15170c0406 77
    0x408a04c00407420704103046503100340d040c01d0050619a9410614100300000c5642c001980d55540403a011450010500700314401309034000c1042030165030f540d4030819143c111240c144224400c443c030401060303080d090080d2800440a1200c0c190504155680b51690308040348101c42506d50072596500c2181d4100c21640c4a544041c9204610f07002d0021050030f05655150a5484089000104600c00f00500041d40314006000e0503103407100078964003209940100082190100b4200b001c01100702003160030303d20072500040d030b4540c510039881c50503079102d640d07906074018290880011403259014042c40001e401c009c1c0141c06c00540c0041c201d038801c4680c8440c81c42460701140c0410017072a01001c180c1d10180c0014541402c54a0f43d20450308100c070103c950510b90020040f1241c0c0c40031b0015080030381a42c2c0c494050319007465081c982a20307400b507843e1825001c5000c09014a07a030f04152481e50000760a801615180c0c01510381d110400c207946111889148810086824180300b100b088880 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 147106196 1250 147104946 147104957
    0x308090f070b03091e060f060402070807030e040605120a02030105011a0316050706050408040302030d030e0d12090b0103050109200303040e0a0b1503070912020d11150724090201 78
    0x2408802e107100e4101404504562083e4041851550010b04441010101034002482030b40f4001b48040f41036500140400d0140f401440040c001600711420b440a440c0c0c942081189070f90340001040007006590300c01c0d41d0040d0003510b00ca11210000ca01641301134000d500904c9680c0e00c60140003100c1c14a8003e400201c0010000294070304511000756600880510344680380c004191601d0f41074130015242070711410300000f01002185810489011061403a0406100080c100400c0c503889004e6007d4030000d100018003141c1c0079840075400840c50a5101503181c4c06540c40303050190080040000403a0030901036411480441504c100041d85e0f0140140110700d0309040200303101030888094500c00000c0e45800100403242c0d16003032040c0740b050a070240c1036103a1404100080207903005611403602d940c0542d00d00000368440d1342d072148407103030040301c401562003050300481d06155425400149442000c903e20040180021100100792408c01d2200858920340d044002140c003000c800901040 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 147107446 1250 147106196 147106199
    0xa060c12051b0c0304171c0e0135160e150306010c0c0b03150108010902040b0403020f01051e030603010614211c170c072d120c0308090f07 61
    0x808140080400603d6842030b2130610b41d07074170f800c60740c40e00c52a603244407140c000c07001803403c0090b2100341002050303030313482d00e030410409101c000f81c4075001184c800006602011404c01c1d102d4096540c452081401841c070480919180e07a0702000c20341451010300002c0c0b403001ea12840c1d450000b00c14150085601c1c1924030b591030344001074801d000850400c841c4c15141c04000202038401c0341c00b42d4806c000d100c0020001600340000180841016040b101032144144070030b104540130001030700c0a03a603056425403070701c60034040180c8042c02070380b07068540004014a84070311003181d00061401480160024089251035100002030996070b000040c0d00310301c1d0645050000b03100c25541c0a50400e203103055075020b602d101c5080c8011010480c40303001040000c01141080384520904592000034500f445040014aaa4800301e9008100001c2c4000114607450309030300c0131901055400c1075011030031810a01103200c000c1c01c45407021350260701007642300380000e0500c040803a483c00400d01c40c1e005805805e = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 147108696 1250 147107446 147107491
    0x6020d1b0503150f09131208091207110306040c030510050402130c09030203070605070b0a0b030a140712120305061927020a030213090204030203030d05180a060c1205 73
    0xa0b510441d4084e440e1100050300c2d484541c0481d004001c0e04001c070907860ba8034185180040c3d4054030660802c0841010401d05e4040401e0003903420443e100015130321b11705410003240d0f0b18000c0082e991306014642c103110400070001c40203000c50340308a0a584209a41009400490f4000c98020350000310910b601450700303019600c6030580d0001f0b800d0454240e912900400e103424580d8110711301080300000c54100b40503104120590140c0c10060a0015100040109072208000c00004280164500342c2120348541845880d001d0a011180c80c1440429424141007030f0b03034458050804640f600007c6202410b0014620740300c0800d070030302000420300d845502481086602e23105004207480e5a070301c154081c00c50000708030f2010300d0340d005070310b43c1d000c400070f122401d0042d80204e900c3c603c100810030050314041305492003402e041c0c0001036142d6800e907100c1804841003080a50b6030145001010812280f51300003600024503075100140992041404001c03104203480c42e24111205a50003240f0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 147109946 1250 147108696 147108721
    0x10030b03010e0106090203091504080f0a09080d0e09070c0c051504090f06060207170d031d0a0f050d091d04020607020a09051509041511040b0706020d1b0503 69
    0x10000034000080303003201c64214a084501c942c00c5a0041354001060000b242820000381c1d842545054120405040c9a42c4521943c450b4401c250218503001c1041809140200c03003c8000300030b0b500070f94a0040164000408007000d05420314460302c40e401c0490300852140c001081160b510120840b42030b420002001030412001104801401d0304007c007281000042c060956481b50f03001010840f58180788029050940a400045128030170002411940360300280c50340882e6400e00b00040c0100d040c4883c1000340d40d01c920040034070302c2212042000c018224007113044160048040d1203196408400c100c0f6081901c4c8036042e40c072100307080c100000b00c481c11107458001d44000c184903c0e20f00c4a0740400d0f2105110340c80180c81a99a03001c2203c48007a030b241034000d080d0125400741e01480c15980d480d9800d50007890301c8440d00d5075941d8400300c600d14034048802600090321000d403515414030b03101010707501c00032600c0603060800c04114100d42c00882e507a80d00c6411034803805d00310f03031714140130511 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 147111196 1250 147109946 147109961
    0x7080714041214011d0d05160f080a0f0806010c0305030a0204030c0e16020c0a0e04020114130501020f0115030201080403090905010e09160503060c16081902100b1003 73
    0x20204000a492980c0b4002d078241d980c450349401102c042d00c401d000342104c00314041c0b00e043e11010740700000000c0d0007181944003055142440e82d19016032500e0b40d801c41100d003000415081840c01c1800501c0b603003030007519401d1956551040155103100044458803815038001e400f06000d20605400a8080c1002d140d01002c2c8590040c01d19690b03071550950705c0100c0d03100c408045106c609020010443d00d1242e00180c2d02d500041100b0709a140104002c40d01600c5120052440e4401240031a07206800700c07401100f425031429201e00c0717504240060340b0214800d090142c03103120304a80004106009681041141c1340d40000700a1554006545001c00103000320708015901d440428503403050301c0303854040c0081d205451b04030301e806c0b981c0901d00b801041000801e20f030040c4080150360383c0041d0540d40111a00e0025460301c0d1590450301582c87c0711040140f011101045031500c1c0340b2490008001c05115a088900041c0d001401104a400702d000046d04050083c0390001c180380203401051 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 147112446 1250 147111196 147111227
    0x21c030e011224080601120b0112020102150a0f0605030a1709190e041104092303090405011712360409051e030a0806130e1906050c03070807 62
    0xb05220400035078070a000d2002c040b01c158910f081c40c1844030300c0040242d03601406040c07440c44540b91044d01c0e502c078204414409c98081c40020111401103901c01e01c038094546100f028407100d5420801142000340a1240c2403c88443c900701002030391303160009883c000c882c0c10002c5c0241800e100b03e004c80290b0300401c3d5244d00031001e05e56103510121039030141d00c010030080c0199030f29810145880e496059034400c030180300d2418007007800007142e0200d40006030b50260365001c0540303848522680f81180218450305030710030300e440000200303204402d00001c081c0c1001030560b030702a221180c8051f0340f070050603640012040c004004660550019482c0704080c4150900c0342c0c500c1071444001003d0ba0008102118603800403007039281c07103401344841044142c130070380301440c1005540c0701c1c01401050018101442220300c80107200d080c2c0303981e0b80700c032a41284203816205110b034100b202111085590740200c076641e283c900000c510703071000010360380070f00250799405440b5100c50340300310751864031a003810 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 147113696 1250 147112446 147112451
    0xa0f020405150a030b0f1303050a0e131515050f030f040203070504050705180604180f020405060304050304030512120c0c0f010204090914010506010207060804080706021204021c030e0112 82
    0x200300d42d54034040e02200940c415130303210784c07241b45c01005807010800103407a020403008080c8000c000a40c00c5015280d50b01c540e0303c0d20801c03201c2d0500c0001c204510103c00e21910500e40b030003441c101c80d09004600706594200020704030790086010121800c1c41036060080c800e583c10700c0482c4074070b02d0003005543c1090000302150304498580c030018040310815560031021980c0007400e1300e41c3c035400240b0142004804c84100b801d052030071408200c90b0205a290628195413084c11142c1d4085c6075042d0782c00b408019040f55101d14241c07030081d03607a42c4540402d0300c40e0b1050342c0c44021203021140c110b83c850500300b082803036a51940070141400c0e400000a12502c2d0283d603140308404c54091000e40020100c400020442080c00d00704120306010301e0001100b1039050400b008142c0e40c00142e41d0048440c04d292110700d5941d00e0408011070700800344000e0803a8000180c00740303006034402c1d41c2805175000716989a01c190f0300c250000202101060000d02044113007030074016645c0510302c0300d1544074961802 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 147114946 1250 147113696 147113731
    0x30f05010b030312070315030506180304080102070b07090e1009050408192001140c0a050708030708060a050405071202031306051905010b0315101106190e0a0f020405 73
    0x7400c50308090002c034141001c013000c1000c400c3e8180203103045100c5170615074801c00d085884041d11a02d000303151180c10040d401c10103581c40700400071180201a402c000b19181e0500e0319100804c0da2082e544140000c9103e04080707601002540624050700381c000c00340c010140f8112100024040040050301c03070120078482154000c0c030440d5918185015a5500d00500761240c40d0110f08030740c00ca00c0c5101e942c0c500050450070380c00c03140704da90f000402024055142c10b22a041101e0b144079000c001404050301005000c02a9003000045004080031a400710190f919101800119181150610001503040c240e0b032580d01c907264020364004031038031020010f440705a11171805448082d9000b8520b0900c0c4001300d1071034000b40c402c0034050250b01c0342640c40c5081c40380509081c643d41140e842c6c4070b034003401c07250300806002c0d41e202c5c82e205000da002c0d40c44529160040240441c9220b1014140300c0c02d2908804d880e1002140e1501060707403200c02d41038440100c1d0240070040400900214000701003405 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 147116196 1250 147114946 147114949
    0x30c0509090a0504020301051311120313090b090106030c050313030e0a170c03061b090120010c11060702120309010209030601030f030f020c011e1205010f0603060806070504030f05010b 81
    0x1400b0b2080d164501d001c98281014414582107620041170400074030349000650000500c4103000410109007210064001d034920405241144210300300322800c0c40d01600000b0f0504003075080640a00300c200c071000300b16a40c62406400341d800c030030300f0342c00080c504100080102c041401d5101ca0240640f918400081c440001b2406100321900003206418031055410f9104504000034500074005401825a40c1400390b0507005202d005000f60211000c02304410b11580d200e08800399010b0a003002d0230b82c01c1c0580c0d60565000b8080d03e105c1c00001180000c00340d50941e000aa4540100481d9004224092810718202c189400107402d02c006075400700308100c100d03a800c101c418040d60090f914210400d046240280203001c12501403030943d040131941021a81c2c000c6d000355408800e4080b066486103801c1070486000000d00702c400340007450200042000740801d22441e094a00e9078404001841d1100465665890201ca45900080007080148000340100354907452a6104400220f44088105c0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 147117446 1250 147116196 147116209
    0xf03030c090b040902040905100e0f090a020a09051504050f0703090204090210090f08061b1605010c2001020408190203150106080a0b0609150c070f08010e1e0c01030c0509 75
    0x14844404e82d41c010805000b019980c1c0304203034100c0c0d03507088a120f6062603c003140c003807444000d00c3e469010a9100001d150700c2c400340498400c4c10740c01003607100e02589980403000200010b88941202c141341920342651401d1070f1080502a51505c80d58411540da60741007140548400700d0308a80184c1c40b800c0210060310394030744481c08092240c03150403c0c00c4c2010800c1d40ca010441e40b103040e4a40c0004e00380881401018030610aa03505445000e560700380c4181c13000281141528000d00c1b035803800900f6054560302c0146000220760001380500c09141400410303090b4003413802241b0080d0040d0410502654421002660326440601510708010007049050fa941000741d00c114003103001c40c002c011508845201303802505404982940c14086240086010400300382d41071903800c00002103241c0301410410007000242080304143c1c614903140c0006501801e111000504c56108074001c01141c101f001c14140741e9400070307500078417110f40000e004401404032113018000303000040050311022345610 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 147118696 1250 147117446 147117449
    0x7020d12020a050a0507050411070804090207061e0c0206090a111c12030506040c050309060411130f09020f0301050f0403120b0901080f0f06070c06050411180109050f01030f03030c090b04 82
    0x1400035211071b5240ca820303c0251400c60025609516080140c1000141500306440640b000c1c14001a2919154945007000304142040201014101e0252108400f801d070441221100c0030b500360387c000d80394104002e503191800c0c040100719009810180c0494104141d08505140002c940070401d03a80544070b03500083d41c002d16100c00a5256000c000850038103020302c903249050342c90624030710700d03100b08629200c1070068030080c161990100d01c40383c1c0342d031400d0b03034220041f003110786c1000000a400c000400411900200720300804100091442a19061140381d00c104c8443e208841d450707840745d5040340c24024903c0405802c5690300c0c00048561144103000340640300b400c0050900c41481d21078545025001d07205080076512080801c0045a4000001d003440c50703118801140588a40c98000540c032142141c2c1e64124009112101280c4080f09040e8103e030003c80c0d040029481d0700242c51002034003404050024440c80c0c0c501cad000030788070360b0014a802003603241407205a601c0700c0d000201039205 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 147119946 1250 147118696 147118703
    0x5160c0f080601150e0603061809030d110708090909070905070f08090c0307061805060f07120504061707110609100f0e1504031205041b05040207020d12020a050a 71
    0x20036014840818104012805000c00c03500b011a001084040241200381042c03000380204c0010020640980ba020814944400c4440404059140800780556030b0b41000c88441710b410b0602080c2c040c403821071011101940e41200d0414540385100051100303c08015180003010302c03400724002074181d824403d41e400381c6407660314426041001403004020880c0a080c038007103078101010400d503e07138000a8410440d601130038209448800c3c00151a006049a444a0f40040001071481e080280170b0008001d01407040413084140c0380c0e40d110032941400f0301c1c018103010448809981200c2400909815407054051030000c8207a8003800c1100e04180c81512448820784c0920000a80c0701c245016002c800d09034200d040010342c0030b0703400407035841c0b0084a08007030a0116402003170615110340b8802d200e40348680000e0001d0704240c0f8140450461461041401209154001c9560310b8503000703c030170303e41c0c00804003a40d00038a9280c2114503c14801c55409612561407120002107050100c11101400f = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 147121196 1250 147119946 147119969
    0x1205040f1202011a010f020f060108211c020304110d051f0b01051603021e0304050405060405071e020718020304050c0108010806011701111209010b0a140105160c 71
    0x8451500742003001c20610104156410000321060b4400c072040190018402484c01805000b050321003a81442e00a1420030014064200045002c10b0f00003909002d1980d681d04000d54281c0034032245686001e0a046d4500c030b042000a508801d412607009140c00030302428104e0410b1003001e0004219410115040381e0325001250449469818000041c8220503800403c6c00060040ea000821521803c11084074905040101d0b00606100300954869200010300d000003003942c0481083d1740e60070611400d88107d080000041440c14a070050320300408080d1200c07000c5e0309004c41100e000304036401c040000c42c41008800074401c003002c4420501c032000080016076a0416007460703814158556a068140304404004004003400014064115844520040c83c04d100281166004d007100c0100c02401c1000420040c104100c244099400f6641c82c100810100389004c085c4030307003401d0750720450807501d02c02d43e00701c42d555004200620344082c0640c202c030f8050a01d95260410340da0030340c001c1c2c282440b = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 147122302 1106 147121196 147121223
    0xa06110702151b030f18030c1309060605040b091617040602030117010902060d0b0d0f0f030206010602060f01030311030909011719020f010f120504 65
    0x50380244085640386244412140310381004500c0404540c0707009603c2540c5600004544660041804040c1044860074000d1801c600246c80e0b40e405000345652007030300e540c0e10143c070086a00d41a50015030b0100c0e604103e0100d540e503402141c081c614107048403296039a0b00c000a039100e14580300c403100f006400031044946540860120750002800c100388801c01c0895001395040e40d0482000500805004050901780e82c228a4040c1d003041c2c0c100706c010440d040030b800000c50709001600c140b10303a88250395030034821516140d081d140c285880300114205641408a54010501d51000301a603003450020400c3c0c902041c0b02c020248099a040750a03015405d10039100c3ca01c44c000c0c0500e55a69481e00250f1910041081800380e074010500141501e85400050b0114142c015010105142c0c1c034000640300e140b143c18a840902860307500f0710b25031820901900d840365118290140019 = true := by decide +kernel

theorem cover : BRFrame.Cov 146942446 147122302 := by
  have h0 := BRFrame.cov_init 146942446
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146942446 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146942446 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146942446 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146942446 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146942446 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146942446 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146942446 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146942446 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146942446 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146942446 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146942446 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146942446 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146942446 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146942446 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146942446 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146942446 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146942446 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146942446 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146942446 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146942446 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146942446 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146942446 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146942446 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146942446 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146942446 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146942446 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146942446 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146942446 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146942446 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146942446 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146942446 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146942446 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146942446 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146942446 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146942446 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146942446 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146942446 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146942446 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146942446 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146942446 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146942446 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146942446 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146942446 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146942446 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146942446 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146942446 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146942446 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146942446 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146942446 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146942446 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146942446 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146942446 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146942446 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146942446 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146942446 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146942446 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146942446 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146942446 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146942446 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146942446 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146942446 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146942446 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146942446 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146942446 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146942446 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146942446 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146942446 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146942446 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146942446 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146942446 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146942446 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146942446 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146942446 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146942446 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146942446 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146942446 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146942446 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146942446 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146942446 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146942446 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146942446 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146942446 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146942446 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146942446 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146942446 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146942446 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146942446 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146942446 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146942446 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146942446 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146942446 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146942446 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146942446 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146942446 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146942446 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146942446 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146942446 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146942446 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146942446 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146942446 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146942446 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146942446 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146942446 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146942446 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146942446 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146942446 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146942446 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146942446 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146942446 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146942446 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146942446 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146942446 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146942446 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146942446 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146942446 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146942446 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146942446 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146942446 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146942446 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146942446 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146942446 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146942446 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146942446 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146942446 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146942446 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146942446 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146942446 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146942446 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146942446 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146942446 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146942446 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146942446 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146942446 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146942446 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146942446 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146942446 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146942446 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146942446 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146942446 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146942446 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146942446 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146942446 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146942446 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 146942446 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 146942446 ≤ n) (h2 : n < 147122302) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
