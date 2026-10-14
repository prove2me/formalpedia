-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0613
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T20:44:06.555736+00:00
-- url     : https://prove2.me/submissions/06ee08c1-6c89-4910-9977-3a169eff6326

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 110071942 ≤ n < 110251798 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 110073192 1250 110071942 110071961
    0x150e06120a0b012a06090503030708040507060905030a02100212030910050601050a020c100935071206181202012003011401050313050f0d030606090e040602070204060b0a03 76
    0x3145809614002d070352080c0d000c2a4500ca00c0001420f4042401e901881c2602103000c044803402c0d2150800c0c1300050003400650b000d80d5258844421504091510034148142908220200f04d100d07407081000c1c0c2d9000034230042d86030301903a90508141c800c1c14102d061008903100100844800018821120000030300144902000101003010b6280c1e2001114607104e40c01500005078840e80e00349086280c280260800f1501a013411132005a0b148c2460300030940e5505001203a035406507111342d03860280d02c0600d01d09010800600b05043c2010a04d203c05984404080e080f656142d09001e031042c61030039100c0d15240c01034500d0400c1040c150009001e04242c0c04050600d4402490080b141303840441076a040c4c5803101e044100c1d480200f001120710b034000030519080d4540620101000c40e0b4103010414425011101505a41680b01c9015040c0c0f40c2940c000303020407082c0e15080050b80c05e10119a41c015500901c0982d449455000007005448a50060703911400b0000d07a80d0b0fa019003642c006a000c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 110074442 1250 110073192 110073211
    0x1b01090302030406140403080405060c010902040f0207030206060307060203030c0c0109150e0c0901050f0d03020313030b0405060106050703090b090301141009060e0606120415060303020d11010213150e0612 90
    0x201e1741c0f03160051654091480020a0200301b0300c41400949058809000180011400000c0e03040700c640009099440d2209003046030303a0700164640038983d040c00103a80c010425801030081300e03d0400000e58902c00140325515a180101c0e0100c0040000e401540751130750441500b0b05003440420452004001d6440105c00b80d10800c2603e291a0406071800e0341240c40041120801d100030000703001c0e007130510704812800c5010820110781054103214090029600407020321f01c40f490a40f4005180c45ca040e00a502844403d00143d80026030200c0d0380b07002d4440c080d80c040d0f111155080846d024101581264032840d0100302000b118a00c2e032202c02c812070380c2d55641031101a5071961803c4581006030b6016401400070003104500100c3c44c10400c2e0040c0c0700301011400080b081065400f12149500201d005820503d42c5441207540304166000d40e06205000710701e00a240c1088607c82c15641c1719810400143c080850b0500c0d000700c2c50040060381c045c04d51075450480310b00c1400c1e0000c080b141d09a1 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 110075692 1250 110074442 110074457
    0x70b0a03020406030f05090d03020d02040f030b060f0117041709031f05070309030e06070c0803030408030105030d0f020a031413060806040e01060303080a0b0301061203050304020a05241b01090302030406 89
    0x690b441725008190084030001c02412004811150480195000500c5204201e8003000300040102c0144c1443c0015030044c081001c840c00e10b0b40030082001c00380999141084803410b650314540380042e1a0b19000b503846684218000d03201948140c040c000c052105a0600598000548038100d070310000c03a055034400b500300308a030f858040c103500700c4d80c10101c0038000030266210002c050070614020301645005030304410100c1c1d070f02d41140c1d01d10b038400c55040b22100c030048010400e5040402081440450314140b0801011108070000c0d0394a01c041d01c040c04021800b840108605e80e448101d03488400046400c03d16243c0703e50010b8039198007500e00c10f0055280c811003100040042c82140203030303039055646180b203407106190400681075000d14107525550381c1600103119901400d5070580c1521030703114182c8914103801040070840c03040c0d120a0181030401d0181c0c01002c5103101308401420f1455403d900c2d905c0c00c0300c81002d400e01150343c20f111586848403410515400001800448802e6a00c40d903 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 110076942 1250 110075692 110075711
    0x405090a020111060c0715110a0210060605040b27040213030209010911120705160f03082a070302030d23010b090d02010309080904050a05180606030d0503060102070b0a0302040603 79
    0x2030740e60070115400007012170706008070000180c1c06141c00600740c00790a4041441000d00400a04d5035012000c01c0c40540c0c002c0c4860000c1c122180030310300040c241c50604600301840c0c010810601d10507141028000c00c161070780c41c4a981e003032190041882a0240c0115168654421104841d10f0903000a0348201e11040000035408841c2c003e440c12031105408440c00c021082907890f00d0500050503180500009110031500003c1400c600c1d183c00340190030a80308035005080c042d0101c0c1d4003a2160041103904011421440120b8074005001814850116500e8856080803800c5014070380200082e141019400a400c41180113a4210400c0d41d00351010b6690341d03007810390300ea48541d095640e0400d80c58403144015600035804180c106001f0500d0a151480f01d0700000c003103800884460110580e12018000003243c100440c100d0411408020001400e041d80002d5035036680d14071030410400d0000c00140181d2081c07003020001e2540d000890788420910300301030080d4016009640000785000d9010 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 110078192 1250 110076942 110076977
    0x190609051b0c030d1107062904020703090608060f190509090a03020705010813050f161502030304061a030609060402040f05010e040f0302031e0405100201020906030f150405090a0201 80
    0x200c02d0790344450010b5140400c03903040b040281001d0201c80541e0b4000340480004105140141d0700010700020038004401020340032034540003052100d40b400b45105110401c000381d0000b9103407094035014203190015a88134400a28590200c1400b00e420030300700c0401040d611000d9101e4401e03074000b00e8000c0d54550f507040d0655562000c4d10300180051f448010200155401040c0705500101000000c1d000c01e0959200d651801d1030150100f41903610014115400707201c03120b000c00c050059902200402d80490390003d40e41c1c0000740c0041d00301d503920508023094010410f080b801d01500079090760607c1c40c0041c0882d449207002c84080e400b541c00c18503160110583c40c4699410703207a249101c005552500d85400c48940103066045056100c10088481c800c081200da01203418940000180c1e9181800280035207404c43d17041010640e130050002d01966078840d41525032114080032a00e0840d40c3d018140020311240201c80c40e0040c3c40c010501000c000040360b074100b080c0c001c0c0c03180c92074900c502c0f540 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 110079442 1250 110078192 110078197
    0x118080301090617060c030703020904230601020303011a0d0905070e0a06050303030402010804030f09050a0b04051f0c03180b04180e0a0201020c06070f050f0304180b0f010305190609051b 82
    0x2c1310150f403c4407001804801d0000065a001030741803a0060401e6a400c01040459241444490b8034072107030242500502d00b100350b03040c0d207d0802c0c8055400c65140000242e030903141ca21119100764000306024080e4884c80c2c3c070490000707800c50f0441e8481070340c0d00305000d030754003041e1242001c580c185400460745040c0001100d0107140e0681d00c030503440e6181d84049405203503042441c01044450800001c00c2d5a03054814070151404245c80c69489151400b00001005100c400310301c0d681480300000180c0c2d4000711601a0b854040c100303560400013035190802e0f005483e4100c6d22071248046004100c1c07401b0000c10551820440c24104408031b9106103066440c490782c840280140e01035100d6a100781000c0c0054103c10740700d80205454110340365121401c12910990b0203d140d0b03c04101003209011132220200ca84410300340801c82e032404480403a51400c0c000030628180340d1620040390031300d800400c1401d807095010001300f00407602c40c00b118000c0c0c042500c1800e204182d8920035402c20810608 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 110080692 1250 110079442 110079479
    0x10912050303040807022101050a0b0a080a0b1306050a0507030b01020c090604150504060b03070206161205040c0909110f0612040f030905060c010501060201051003020102060406050901180803010906 87
    0x30740c2180d41d2942c0d0040b80d075211020880c0c1102c2c0e400804c2c3c8152510000105080501000214184c9000c6152104a42000c00c00c588148042c0700700300300c88807022403050450360700301010240e00d5542c035080200b510003920000f85480c0c50310b030402000e005160301040c02031141e55400c1c412911501d0049030303258603507800746170b100d1440c502145841c546035110f50b42d4841e21340340c1c11401d0396460f400101266080d50001c100904000100308110b64144812a403010144c003000b4004503102500502c00079510445801565031440820709100b890614000240304840c0180f1446041e40781609480b18025442d07402400c203600d00010602c1c3c4403042d070381c00d60700002008540b90395507115542c0e80d4081c40c8060302480b03401c2c0c2002c02c0e107403941c0000784404541c1c1400030603294506000242114802040d00c0c0304407440c408240010f030780c0491a140c00a822800c081381c03d0701c402c1c2d542c9006016000c081044000092684070030001900043c43c1203451a480411a8907907030a0180060100300e131 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 110081942 1250 110080692 110080703
    0x6030e1002040b19110f0a140d0206040f110901032f030d0309020f0603010303090f06050418020a02010e0601080d021015050105070f1a040b1326070b070905010912 72
    0x204c0050424054101c000d640091300c1c0000b020040c420342c140c14001403481c0000683c12090201c01030140e0482e0400740000780100500c01d44c4181c4000945401019000610100d144440c2109100000058008102c8020300d20806942d5914000d02d24890401c8140c4a2a68040e02c01c000400f80522014400702e01401520498405800840c01450b410b00101d81c0850b24105941d0241c507143d025501a41c803a4440c40c00040c02d18001042d40308046d40300e030b42004400c06c0244014031130441046100d01e401c1a02580310310074880141c4c090042d514544420303115040000030184400241a03404040c960207441c900b103041c0d4500415580303203001180b11655007031410081540700c3d10013000aa130140c5c0d29004500904c0d698646400c7c10030341003481d484001c20034031040c4144070300c00540107035007906840340c0080b1586e610329a41085556005041100760401a45211110304031116a6401200e200c074910b0202c601030091225030048a00140c003040f00420108401071000b900d41e41c002 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 110083192 1250 110081942 110081947
    0x1020601081906140a02030907080307080d0b0d060c0e040f14010b1b07090902010806061309020901050715060305070b031003080f040801090b01050906061e1602030706030e1002040b 80
    0x20840d40b298002520040352210b5585143c0b04450080c000b5160103145440c202507a40d041c12300a042c5001100c2c0c103e140c09410030001e00e0300080c115802c0390800c0c8040180807450b1603010001880b00c4504074009800c0c207003003405984d039030380c2d00c500554204801200d042001c10b00d440500c0b022520f403140034080c5032081c080144843c0804402504698a40c0d560112140300c859051505064155000901071500c3c0c0c0c1c501421036030000f411030749c80107050300c4540c1440d08841100c02c181c1d40398807a204441e680083d04050991103042103030300706604500c1d0050140c0c81421004001d11080c48152114081d10401064039080d04089a01428400203510121400c584803455598040b40d0700d101400c804102c000307171081081c000e046070301c0c0c0100071000c4150b01d4042442010f450080400b4854503007003000300c002d02c2c820040081d00080050300140c60b45c0701041020306e640144c00c0c002e545480340f1a0001000c44d0f040d000015407020900c241d581040304180400b01b03074040e500818203490003d = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 110084442 1250 110083192 110083213
    0x306070c1e020a050603090102090a0303020d1707020616030b060f070b06090912210106030e0f070f170a1b080c010c08090108100b0c15060d0b1f09020f0309010b0102060108 76
    0x44091500052150001031810007001d000548010b0664022000f603000b12540244c082d0d0012071401c210b82c01d03051400d82510340705100a44a44005004211542c284c0f40d42170707000e500ca5400401d6110010b850695901c1c0c003041100016003103014111000c0c1c141d1000a0301078241814098042d120342001040088100c4181c928990003001003111382036081420b001c00d18498000c082d0003400d00d91000a042050401e41e60b0410391849642403082d880120100b1080750305502090884003049c2e01900d080300c0001020342002c00d10300c3c3c050b1040c030800403502c009030300500c07007841220780c0a01143d0302c2170884401950038904050010b080048180300c055251350080d44041e50180f40d80030901069910f40700783c0303400b82e000f42c1c14107212680b00e44000c490a214008203039801408c100c51010410030310740c5d1b801c0d02c0d41c400203105007040c010b02844442984429203032007020b404191410354035001052680c1c7d159030000c60b070480b095828510015150b500128a0b84d041e6001c90001e4100501e0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 110085692 1250 110084442 110084449
    0x1b0f010809010e120a0201150b04061d1e01080a0c080a1a12060603010c0206010b0403080f0403060c1d04090b040b06060d0213050a061425020306070c1e020a05 70
    0x40100001c5403552101c008045001d02400a0401c2c1c41c0e01c2090140c40e581d1600000b0708548041c60694060650340d0014000e104614042d5400c48856140132201303214414883c2d041d042170003003895040b0a001242c40e0382003000900c0c4403007054003030361000910351f10b860305038017030303c403c200300101140300d0001081010030b81d50042c0c66aa449a0010f41540c6031030320115046000140c548119900410300744822842d003070080004070705503031000305a10b50500e415070364248528032004011480000d03114102920070b04c1542c0003907800040c204014803c41001411000401610303c82d0070100001c0c8000701d2034103204104d4501d4000d0074900c3e2a03612907550070f8a0b6840980107039030080c01803000344d20b5094940020101c1140380006200698906028003003000481c1e005081030020019000d01d80c44021300685503080703400c1e40c00118032003000c18100380158460b00040d4050180340108210070f904409800b0700745220308007641d18510040d41039050300c030380303104000d40c00035080303004000361728 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 110086942 1250 110085692 110085707
    0x1202070201090305030313060b06040509060d030e03030c01020a020d0503090d030506040605060c0c090702030306090403030c0905090f0709060224041a040b07021501031a090708010f020403051b0f01 87
    0xa10604100c41095280d440705417440d0400c940d81d103500314980e8a882d0400c140e501400b41040e4040c0c5900d81060306100008651080c002c10403800b405200c05840241480781020729050300014055075034650403c00418081d50203074005402500c201c51a00500522030801c40b442030380d01c1c0f0054a503907200b00004501902e4081c204640c850340307030074012407140e403000c00509458101c8001000030782c00700d1051099400c0010902425134100340100142d40e00c1d804821940280e00d45800107490050a4090362904141c2e00016005207507002000b103111085841a8040c0b82d050f20365496071681d070030040f46d540108081c00e480404091104c000301034100120b441c1c000d071140c0c4d800c1c800b16030020340041c1e803404200d0f13007a6108400013061149080c1c05010741c40505c0c142c01c0007d2007130b40c11529152019000065444d0b400d0f0361940000300c0e02c05040c88040094018503009001070120308080c0000381d04140019075047c0246110b0030042c2c900c0b1107224081000240c1210b500100700300c0190307000f0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 110088192 1250 110086942 110086957
    0x3030c030e070602071a130314030408010207080901020f1204060f1e020a0b01060e0a0506030c190206070207050103090b1303050f0a080f060303030402030a060b06040504050408070605161202 84
    0x1503181c14560503244014000c1e500500665401002c000b440c1c840317007040c003d20701000045014001c021042e1003081d004204400da1381c000b12040001c40c0c07404000c070710354495507128000e82d501c081926000c00a40d4401003072501d90903802c0f90010080d48440b00d440703600f05d102c01c009141f8100020400b4074041c0c40e465107810300c1e03420100700c801c80705044c00301c500c880c2010f2100160024034540c0104802e0300380c8a8090011071038020745082055000c183c0c02c10281c007919110382d0740480000c03841c0500c0c1003105d13104003e080d6807200c40c1800c0c05000c1d52301c481c180d40f40707005402146c0010810f948288184100d142e000a040e040c69141c2c043da0750703180354180e5019030401104014080380e2183e400300174443c1d05450750329180d239854013042000c0092800303410ba5105c0c0d0400c105110260307900003004100113400c0280028001600000248a0b124a52000c2e0300981041c04000034410100c0141c06094019141400140e40c0c05000805102010103014003240c0515011041c21a0302d90180440 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 110089442 1250 110088192 110088197
    0x80607020a14160e0403030e24041e0c06030605030c0913080906120702060106030c0512100f0803030402100503010e0106050f07080f090f0301020a020703021c0b01080a0506070806010c03030c 84
    0xb59060801c10800010707854110404000003c4c0a100800d43d140c410010b800702c41c50b002c2c03c2865040b0f501050540200e10341b50030003280110203e02803120081e04241040305d521038a034281034003450041001c2210b846100d001c00d1819600245506003c00d1100c84024010b03d02d8450b0b644540b16006200c2c8c0c603003000e444d45030b42846103401070744034a00109200400360708145005e14051100a1502205800400800d400c0a5415034050b402c81c1c140c5424903d020021a588d0352811700402c108095540300064580704c0c45070000c2d8445000c001075008030700070b980c03d20030701075800300c1601c0510007071040b80c0040711940e004003c0203102d1030142034545d4148400500d03003101510b501e55983c00c1140045c0c445840003500101500d0903030600a4060420303002942418a4000f005e5180c422500c0003070300402c0c5002031610401d2910a003d20940d500501c159019611154490340c3d4490b08403040b1880e00c035103004076852a01603200c4510505e03059440c502c1250707440d64110060034500c01003106 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 110090692 1250 110089442 110089453
    0x30a050d09051207050304030b01050d0201050a0516020301061217040e010323060a05010503100e0601060c0309090603080901081b030a0e0309031c021203060f060c1009060b0406080607020a14 84
    0x40c10b12028001c01380c03c0d0162004581361801d40c1817405128006a01803072041c81e1002203040140d82000903551040c3c1141815a00c640c1c0e03a1080000c4940c071803400035415481e00b907002c603030130020102600100380140041001242c804540141e00e120f24020700448030095001040021880d0505d404180000e40e00c1c00c3d0f8045102140c4bd2070b0507402d440003004192150014030440c10204000380c20103c241c64140240718400d0345075521100180030703100c06c000031b07040d5000c18940110080d00080c07251140401035156207082194040e00038003002d42c0000c05c0040403880703407226498440000071f5103115a40c03954648403081001440400401480c0d07008c10710070344507295018050624000382800030745520900c3c220009040c0080c0c00403c40441c141882481003c0c2c8030220346402c40c54041c1c50031136941c501d4040d01407902038200c0707054110324288076405003048600d4029440e401002c1d24180072241c0c540708142d880e0101101c80d140181e02600000011a00084181030712035840c01c160388 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 110091942 1250 110090692 110090713
    0x6070b0709030605090a120305101509080f060105040501062a1403070c06030f0903020c0d0c0b0d020a09120f0b0606040b04090b0a150f0c05030f19030509030a050d0905 74
    0x30b0036114200c0d62128030307030411b001e00414800c8201580e54001243d01c3c08008924080c500300d00000c80e00c4c0030300c0011070310362030324070500300d006028040240081000b12040200c00001c020b503950313424098180610300700000064420f00400c0c1c04031016a171103440300d03000b440440b031416401000d00403d84030f10402d0003009a41c48010b20060038011300860020814505000700901581c071184500d10b0802d190201480100b50701284481703e03c0320444616001c0e20660601030ba0180789500704039180d85000910502a02c0e0a03401030200c0d00654986141c180c2d91210a020b00614052026200392a8070b01e8040000b01500341e400d5011000404060600342c50314200c1407281c205030481c01180e40e030b52641003543d107040d008901c004c0c1005c10080e2401c14003400001d0075802c01d80025401d20454000100400134140282e0740b02c003102d181507988410ba0b4401900144c0300902c540b401091420700810115000801190800f800a4440501c1d056034120054001c0161080948003070040117202e8 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 110093192 1250 110091942 110091953
    0x203070b18060d091205042105010f02031e0105010804211e1709120f0d0216030c0210030608120c07050907031b08010e0402040f090209040302030310120206070b070903 74
    0xb0310100b45a4000004c070410a4601542c0c0d040c80c0c02c5400f000e10509200800c585d4001ca428004655404442461580000c0c0f4040e030141106100100c0494004001c1000d000d050312880c082e03040400f651992140d85e507a0040d2030109081e6005013038100301080440000d950080b5420720307018a49020182079180c52180c2e070030811042407000000307a5412454022a404504050b00507100c10040c0c1828110000029114811003440c100141804107944d440390500354103032103220408038a40d55092580b80782c01000303044184001c81c440e00c1101c604402243c402d1040d54160f07001e05009001003e030075025a14a40c1000d0030119061161000100e299110180b201d40a0309041e240425130ba0504900a26401c3ca10341c08001004000d40041001c8254029440e0700a82c06803070015601e007000110b80301514104601a4002c5080410302003050741c008001c1d803103603024600d0f914403161608107560000740380400c081d520810600c404408a05418042500808141001c01d00b655481c3d889 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 110094442 1250 110093192 110093197
    0x50403110703121206050607030e0d050708011e0b01021f021b01020a0207060216030611071a070f020c061b160306140f0c0315150c06040c0e040203070b1806 69
    0x1183c0300d001c01074040c0c0f4041d401000c80001c40101c81c009012207420000031918078004d42070080d0400c034401c1d09034a4030340c43d0010714840f1503030018141d0785d4681c0c03103a00d041d000c0d051100140d41580010552540302c00e48922600c44030180590191071900554148110900210300701c805d49070368200180c120f405514254514202c008400150320f90340f4100d00641001a42c6c0e010f10190340101e074a41840c3d06c503407030040042d01c0d40144001b421900440c04078030640118880100041e400c444581d40341c040f1107040c244030b15401c0c1e641e800c41d107603c0d0304100d8481414203e5a508070000703101c0782c10038003481d5212991756580392080f10035000d1003900c0d01c100c11009a0061b86c200e0340e241188001d050f107604003241d11000b006541c450340e00b800203e80a0901c0010034680000c920301a56100030f9507610300103040d40441c80f1070315444130745000041c0e89402040c0c07022541e202c5502e50000754410f0791604a84201d8006028004c1149441030341c00480e408070380e0f00580c1d40b90400300c450f03541c2e80c0e8501 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 110095692 1250 110094442 110094449
    0x40f061805010b0a0603090b070f14030906040b0a0605031911030d110d0305070c020d020f060a030b040f0606020631080a020f01050903090d080909040f0201020706030506010e040504031107 83
    0x11480341040c10501c014513000390041c030b0405051000d00c0011070301e03600020b60030403413518046900d0150b034041110300000850280090913000800e12801100005560307010724041c07100f131101925041d810300c04484e0f103441001d4064010009400e0107002c0d5210541c58140170341100003000c0069000241805480388407100440d40040d03c0a100ca0700801c1100041301c1035040820040c1045800901140e80605000340709100c42c2e4a40011501e42c40f041c1030098030050f045644800c2118400303000342c143c030140c9600541c40d103408620021900d000c0c0e8021144a50042e0220341c80d0a0a180c3c0032020040c900c0800d00350200c1c82103e0410a840d0b18204580034542c0320b0340310306104034001d06140500f0030f003140c1a07041c28144080503002100312000a0340c1110421135601c014a81100c0d2809040300007a880801c1904100034411508804402140300341d080d6800c042e216001036048903002c0d0f030840d000401c41d07082da020508060388440d400034040d041244881d542048001d04d4100184c2 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 110096942 1250 110095692 110095703
    0xb090a06030b07020a0209060f1f05041703070f030e0a0f03080904061401020d200a0501060302090f04170904020d0c0216060f020a06020313020d03020303040312020909040f0618 78
    0xa1040040c040c2029203203030040c1070f500c050241d100254000504404c4003901485c032901c04402041c485944c0c800c0c00142d44940f000b0003883d030010000c805011600684501130301c1c0e9240981c42c040744074010003100c0040394441d000740c05502c0c86841c11180c101521a9840d0044a62007000c6080c0794800c03100c1004600c10035945039204560340600040d110140e12440185080c66240f45e41680c0204010780b032510a0300e086550705074004502100301c2e00c148080c0495015951410307007070000640000080c0c0b4000da50710011900d41c0c0c030100c050a0f500b181e010707009614501031301e170031000c1250082c400303c10001d0025003014030f41030b150780c04c0301e4042c1000d00142e800b801d00c0c41c48036441c209190004001500300845018480c000180d15103c42c07807401411b196000000035032401e0044600c03200d03990040d06003c080d100710301d80a5a05da1081c0c0b404d8005c03810540d6031480341d01560007101c05038180a000802c041e103030350f640e40c8441390740304034115809626804150030842a101c95048602d0061 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 110098192 1250 110096942 110096951
    0x609030305160201090e04082d0d0f020d0e06100b04060c17040f0b07020a0602010219050c0703050f15061507021210050a0207110f0307060f02030708030703060e06220b040b090a 78
    0x50000b10010411030079261400c1d285201c5640c90b4540f07103003a030306603d01d1210301141c1d0340340600c00003009210320375500c8221450a40d9440c080c01000071218400c9941708100188a03860303424060590046108030ba00041c00031072100000791841d5048a03241008400c00390a2070313118003e6880079040d5400011190300c002c10380c1030070b40c984510900001e08541c00214500003c1c201c5020703d16081c02540c0c010301000040040d4586e50800c00c00c0c0003550030809a4000c080e0081c00715866101694117200076203111008541c407480c06644101e0031001b4400c90320700e08030240e828001d04c200102080d98035801030606140c0d540d0000e0207002d1240e0303100783c001641c0b010f091502c070400084941a4500030054482e050720191000108003050b1912410480084c0304041d03012495849000e2008201c00c01c04814011103a4041e000182a9001d5661401080c0c0c2c0752802d01c560030014600f440011400011107210f1021a40c0c810054110007820101d041d14000700402d01c0322034143c034018030703060b070380d = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 110099442 1250 110098192 110098207
    0x110703051e0c0f090a0e03071202011b030e0a0201080702151006090603180b130501020c060a0b09060a03030e0f03120d1107080703080a09140d090609030305160201090e0408 76
    0x10b100011008030100e880540703520803903000c110410301c01042c2c1d15403e940c2d01c0141c02e621070308000740d409041d401540d58103680403120009018080c0c1200d10b00c80d000c1f4941c01c801c0500d000e40924987e5030036000040c1400e0000307400440b40288040e1a490030341c0101c00c015001d01d80ba1523034251080481c0b50100301034903e014401003800c100e9a201d441050301d000241c5103050b5210092145454102c40c6a1500361225201c044200c81e080350010030543c40017511280901002c110a807041629480401001c080b00301030250034002282e01c00c0d849101d40c030043c40002e004060a0b100b00300c002e0310103420032011034007003860b0841005030004143c0c4d0100b071060000f24103000d0314038030b4216503003002c0c10410203545011840c02031140060501c0b000100040c03410b040c03688202e14550b0800801286280c0700180291200c050f85404800100055801700c3e2a40c05101014120b0368583d451a1900f00380400e203149854240000302d04210542100150008018420900450003088142d540e42030 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 110100692 1250 110099442 110099503
    0xe070c0c080706091403070e070306320415080703150c0c030c061a0904080309010515030a06090f02030307080315040605090601120f11090102100203010e010611070305 74
    0x10141d001c01500c1d40040c1003070086a40c4000c0f048121108180e0000700c41c40b01c1000241800441c1d00000c03c40465041004101076058001804641c002d252580c0d020412807408c4014040c4a045a0010907100803c000c00d41002d40c812502e008a5a901c000101d480d40740c07031400d0500a42c030035148400300300e20100b41c1e6859841001c82d8441a420a814948c40540d00905004520100503205070f1355020380c400030030b20004c41d046000600502c1c400071441c0c18038001815030415541c910301980380800160001c00c0021907851003880003801400104d03919a01d0f1005080741c480c040b1960880100c50000580302000900f0f83e0754810b00a1a0b120700d800e452400a03020180045131103a81081c100308456291810740f50340180003841c1144141c02040c4500014103150940340b034165251543c4013201d84a904041e2025030340076401d64200b0051603102505900080c00740501d00c2c4403601c01008142d0184c0784000c0c1d5a24404151003403160341e0388640381000d0612000000005440e02021300000 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 110101942 1250 110100692 110100713
    0x30a0b040c18050a030f020d061803031b03050f060d06062411060c0304120302070c08030a030b1503060103020a170a1b020a050c010f020102070203010e0c0f030f0c01030507090e070c 80
    0x40242c400c04a40c17813941c1c0301c0803200184510301901480003205090240121604103800d8020008819100040b4030f1070020014000c0c0c0c00c0c000511a41d904442080c2c0e8800e004450040c074103640d507070790540c861000f00b1100000300001162031303d66402c4001f03031602801c0399258030b601d4103181c15640007400410180080c8014010282107400034010170042607030712020b40380c1040e0845550285c1c080b4034031082e0020b04ca920300141c056820a42c002500003000402005100900d940500c4181281c40a102040d900c401d520006ea030004e10000d103465202e03a0181110320b000e45003803620122400350b907600c1540d080c0d079400207142d22690b81c209103005000d044c00580e800c0d44010300c1c841c0829140c4030307100d610600d13045040048205009030818400d4060791601e6800a001b0044401103113241c5690700864908103014000b6001c00196502e0046020000094004007600518a02c0301c0110010304006022f0f43c14400715040206204007071400c25481070b111b80e10f583c2c03042c44c11403c1261500 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 110103192 1250 110101942 110101949
    0x70e09010e0613082113030e06070201050414181801111602040e21040807090b03030d02090103020d060801020304050111040f1208040b0c07171b06030a0b040c18 71
    0xd600503001e105000384603d0030f20358050b40110402e901d440041040400c05401182e090303241d411300100b8803108420031076000608a20a031101f0a51150003001e20495004128000c0c1c0441d00c103100070000501c1440f02350695140c014110392201001c42c00c540e602200c16254190034003c04070944110f404244035400140c1d9054000c0b906147c109180240c0b01207a6000081c060351321402004500a070810607070f1280c0300c4907881290381051104d039540198100e0301c104640c0c1d10690b180041c001c2c00314492244000d0000d0051490401e002d556a03019505c004102410942c1c20041100078034154802c641c080c1c1038810026959003000d0916900359525280085d8a030001000308104180d0310310030300801c55010803006004503210b82440803031400340c0d07800400440703800204e800404402113485400c0d84d100f80302181240040d10038250342c90b81200c03403000c00003903054101181407030300501840d0300010550000c5400035a00000ca42076410540441c0701160440201201203110030b140000074 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 110104442 1250 110103192 110103221
    0x80a0804081501120212010b04021914120106180f0e010303021e0d140c03070605040c0b0f0a030b13110405011b02090601030203040f05071d0c0a080a0209060408070e0901 75
    0xa941000c2c0c08a0303407842d044c00000e1041c1040135084c00607410a4100c08125107004004640300e07c2504840340c0e0810b04a003ca50011780c180000f441910201010340e10411030000b141c054981c21b189e010380c2c50076080c0c1407a080c407401041c0001004c0c03480511460103007000c0446104154034514010780381490801c1c422080400340c0c00b070041c44490005851091000a00d01705403c840100c0c1805094403401180207100c0c0000900340060103d00e4201e14010382c40340440c44c628071f031b540c02c88070301c1030260040c5082d00b1a410400384040300c3c03098101c2d21406c24024010f400120305458010121100143c1d0032090034070102d8204910341c0c000400e808501c2c0c1d503020010000c030040e03002404601000301218103040e4040080782c01d02151398407405405502104440140b510396200702d10000242003032591000240002549441805055a0040340140c487d00341e20b85400040e80c019400c80204160841b8050000044070364080001c01c0045c60070802c5103d140c100148290b00b91100755000d80303103 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 110105692 1250 110104442 110104483
    0xb0615040305011506030903020d05090a031e05071502100902060c0a0b01050f04020c100f0b030703030203040806060619080613021210080a050604080d1d0f0c01110c0118080a080408 80
    0x2280e00841d550304d40043c00e00e4030be03036a4201400081c11034a001d4001904034400750401d603180110044174450254090707012190b01c50303038500002814808201d0000c3c01a0440b0518a14418450700509011032009110504200d02e852001d0303e00203040c1c0b0141c4070141c450340100140d04140001c40e4908030191010751811940014180c0d0300e8200c20a8007065031740c1c4150344150409113601403807046000900761030f04182d40b81030084d074907041402010a90702070394000c60410701d4054112248213040b201031682803010340f0403ea83e010001040309410014040c40507007400464801444e062156800414060074142e0b0b0402c107454160308803d240360320232100400841c00020f20700e94413951006404d0740c2c806032511854050040e0200d180301101001c600b4499041c4c010419120b40f00d840300c11640c41000764401100d1961091928030040c3d0854210a19503510560b0030300503207034840a0402c1050743e6a04120700d0810040c030b090b161407201090600040c2c805119040700c1c052017907901107 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 110106942 1250 110105692 110105711
    0xb0c180f1e0303070204020f0a090b251a09011d0f03041a0d02040b0322020a0626130201090602010b01080a020702180106030b1009030803040b061504030501150603 72
    0x484000c1c01240004414540400a400d10b40c0c04008940707110340d028100350b456242e43c80109009410018006c800f20300e00b0840441c141c4030030401e403561102807113095030340c1160410025810500e0200c040c0d131200828020f041d170201203842c441703028004410000030700342d0760040c0410025000101400440c0c0281c2e842c241019000001d890544056100107101d00c0c1001d240c481d075512072201c0c1c5512a40c004140003607d8404280514420081f04101c1d01c40240d01000542141c58643c0c4000d51004200409204a51240301a000c085200750040841030328140702c54400041c044450a2816080301c88000443d60707c800810002d0500780001d101e005d001c2000640700c080c000300020001503020400000b03641e601c40a08100c00681e101c80111541c40b41001809040d00b46222030240c0842e01104910503c160144c07000c81e608580e0540c250b8036141d4403501900405010184d01403e100f69403009292144000c00085215000014140b0101d2a6180303440110340d2065003410b14000b02403 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 110108192 1250 110106942 110106949
    0xd24060e09040803040201031515050a112407030e06090a02011e0801060e0a0e070305060301230109020310080d0806091501020a1b08030a110601080304051302030a090b0c180f 77
    0xc4c0e401030350908001c6410980c0d0141d41107407104603402a4030701940507401142050b00701e4014180c0354140d43d103c500091407107104030f03a94034070200100d01f4540300e00240c0e001580007100440c1c101c6402e103004030703c071446200d0042c90300701d00b030f50f0481d01c0703410200503a0110742c0c11003040141c000c007044a545124440d014040c210b004144199401c0c4040c100c100c01c2e03156118034221002d4001f05000240e03500348024002c1c0242001c9943c1e40c0603600c0e22070300102c5401d0001c0d00c0300000001c006219220381c20010b50102a400207003003c20007903000311000c1140602070214004040065039403007410300d4014108002d02101600d981c20268800d098075500c0d0340c0c080b0307034030344901d8000b00c02004d100c0c25001603070002150340d0710041d258000032a00c07141050340007111a00c107001035011581240d0301c2d2103a2039181d00c03c52003140ea01c14003403100352442040d550080d40c2d00c014030f0760300002c1e0141d1a494400d05224103d41a20032460002030005000c610000c618800304c6055410703001d0210f03010b012 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 110109442 1250 110108192 110108197
    0x15080606041403010b0409050c15040b1c110c0a0b0604060f03061a030105090304090f050720010b0414061305070f0e040b0303041d0c030601020706050d24060e090408 73
    0x201c0e400036003500b00c120540d45094000312028400034200300400d0380c1e44c0c01e02a0300d4040f00710b007007440780c0040c20b0f991307000803806025541600d00407106280742c180c1180d40d42200c1c020103884542d042e0348a421100040e5507a01c041c200590004018080c503020314505680100b0006020034410341c90b10800b4882050441035900644c0e0f03005400180007445401c01c00c1d08001c804005039030640c00e140c208001484040080e0044880503d8103000e600c9800a0030411ba90381129000000b503035158245042800100d16048441c10322800008c80c400100e021800790b4080c03040610795010100207012403400d01e0860031601c1a40b80e0004c00c442c0c10003c0c4011300058101d4803d8041000860303c0c10401d5440d640314509185004089945e61540c500b01100440410b00d8050b00b107040d800001842d5a8849048030720828059000c0d100035820030700d09941c19003000c003015001c1a0f50705410401d0001c0c48603401854102c501c07234a90039a140c000c0081200030055000b9001d001d000062200180750f00e410f = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 110110692 1250 110109442 110109449
    0x20109210905100908120414040218030601081b04090b040b0402060403140105100605070b0103031d0901150201050718050d08091c020f0105070c03022b06060f0609030209150a080d0203041508060604 87
    0x4015a40e41e21202f800501d4002a0030a21741c103001c0d003000000c0d9041c00044403000111580c0d64900310b001288108000c40e940100081c00d809500310009000940700048907611620041420b410b207612070725008000303150108240c1d03490f0755170010300144502c0540c0c0000102035070324260b407402d0910b544410704904107210003001e100c0b0401c984410800030080703001c80480e001e4540303482980e4405201c5000019502040050b518084c04912a507100d1103c1c12180c01001010302d12240c0f40c0400d00c0031503120341c01d0565070b2071410320002080b5559685440e282c0100c1070300c40c0103a02060b00402105500243d0494180502084600000b90806a08500b03d9404031900030b082c20b486001814550441080318405158155103101005566800103059075610b00c43e051280780ca951081c0d403440d845000282d80464a82c0004024448061180840c0132001d0070815259940300003051820061440e0310001d038002090900045109a00d04600c2e00c2c89458805130350300700080804e0240c4a20301 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 110111942 1250 110110692 110110699
    0x9031603060545102405091608090a021c02130e0c010e03070306231e04060209041b090603050604020711060a0c0206030a050106020c01020109210905100908120414 72
    0x43c1400c50800903c00008034500030a400e2261107111110110191500c580e4051600e074030200100d41402e22084103880744500303030001e00b0381e074891007c1910030f0307040145850103a103c1c43c9100c50042e194090800400c03005c0204400070b401e680e10400c140030700c1c09029418400e20705028100c0301100024400d021000c00c1c203010504d0380c0700e880400d0619210b5080600181d0419810f0719050301140c00400500e45086514861134071004001c0d410341041804840220041101041c042043caa004201c0c40b0f10081c40011411154100504103c44d00d402c2000480c210050401c1603035018016554403542c111001c40c948460350347c80181d01c100403c20f80e030003403030003007104110f50b030080405070f80c20b54000b805580c40303281900364907000e00001d014210050084541e40c01c9154014018144603903801843d485aa901d06080307805210004a15130082110114000620303440348001c0d000480c20681d103008005041174101031400004500d4000364038001c02c41009026074a4003440c0c46098101c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 110113192 1250 110111942 110112061
    0x1b0b0c070303061a090a09090506010302010323010902030601170903030c0a140414010f080f0f10031e120203040f0605030c040b0a091401030e0a08090316030605 71
    0x5007000c40090400d130300807003e003290311003541c0c000c0503941029102c5004c04480060040b034541282c24151420110300500c50f61081005000544c000d40115104014642c18280c04180b0030800a90f911400c1e84001c2d40c507680041440215607000d6010130a071644c6090080445c148502c0550b82e0f8800104612000344010442544040c442c042600d108562501d040e07889507215021501c0c080c40304400c079408a5190106a40d1850103080700ea445646090301c2008150b5800c4060014480000d1100320b110729050404000900c040400040342d803180306800103901420300e04a04406510b003900b40965100344003c2040d036480008090a607002d0b032400c5600c03521900d070001c0850080d44c0201184810200e1500406540100303418200c0e0010b08803491070418000055080310520350010600e41c20010800b00071070142e400400ca00a8058200c0d034a42000540b400900b09094000302c4009403904c2c18405440140b0390500881e040e0801c007020700c911940007004416999240c0e629016400 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 110114442 1250 110113192 110113207
    0x30207090c05090909060108150106020a0201030902060903030d020705012a05070519140705011b021e150a0f03050c03060103150b0309010e01050108121c150605030402011b0b0c 78
    0x400541c3c0080f80050000051800d00da0020707500c1c1c040034021541a8418124142c080c1144d045040d4100c9905070007801c0d071440943c0044000d0301e19514280e80009081240303000a4034208020324041d80400f1005880e0b40b2a40b81c00c5083da00a900c078442174000100105003c0c038030002c00c0c8800056182401a512506480d0050410311100710400e8554108440401170101840d5030101c8512500c00340c4401d6901c6034015100c801210711032100d1081e68800c80001414919000640041d420681c44440400711002a03019a0254008002d0600105202c078500d5003200d1410407118081c01c3c140518900105141141e0000a000320704058981c02c020031122560f04601002d4803084e0040765a034548940e4842c060039003188d9075141c0e50700c2d20f80001011003020408080700d002040c10346207030030340040b014541701112020080c00355950704004140c03800185820320081001d41c1341d050b2a882c2900014240015820304260000503c102d50b034001102c807010240d01c0780d081d40c10941c6400d013 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 110115692 1250 110114442 110114447
    0xb09060c0f010f05040303051b03010501140d05070507210c020906061c0b0f010c0b04231b01030f1404060e030c0f0604021f0518040b09040b0612010207030207090c 72
    0x300c24010419441e00f0b003500401d81013130b0840392007980030b51014069600d90b40e404030720b040100c08a030307840490103200502c0a076108602d8032640080c082085424001c4005030300d0201c82003960b415010910010b030140c02c10040c01141c41654141542d002030340910100050840b51700000003e115801b00c43c0041c12030340e1900183c8580a01081c00300300e101c8800d201d1000200b80c5640c0042c880d51800300445069840b4400c200e0140f0b503c50401a410740300c568449181401003400390080d4003100a01088030101001011001d43c9024100100c4c5a07400001504441080f01e400b000c503800d1400c0c1c85070400281c00d660ba00103502590014100240029060540c01105c80d1010700d402071300310080d0038020001d0305d20b0250340200c8010350082030308180c0d0354036a841c0390040c1020031018442d070200307880c400c180002d1050011303102069503c203100010b003202d54221012a92141c1001c144101e60070201c4601c0348075030500b0021481c0a255071000b07550307080e080c8100034480d615401c010750030b04d1 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 110116942 1250 110115692 110115703
    0x7020d1704020f060f130503070909020303090906030a080a030f060501110a0b07020309040e010b03070605090a17070f0801050a050c04061706040605040e100e0c0117040c1a0c0f070b09060c 83
    0x104052545ca44850001101710030091442c81200d00c03910a071503001c07600d80d100c0c0c42404082540200114030304025801480b44c41600140501d03454004d11710b01c840407602030710040c04032001d20f940c0002c42180341843e0008a0344a40c201c281013101e0500d00008600c1d00141c217804454208480846581d43c00400300e185204029039150401d05040c661054070300150005442c0403030880c00c0d03464550300c417041111356003d6080450f60100c9146020000d40614600070001941d00d03005480d00103403140386404150300785a1161849a41d104200604441c003407140c41c0c0c00004009e0323042d14044c5008401480e07620515522000801e2107000304845a942c1c1e8003180080c40044c1c02800b183c40c2a4240d00c1e126403c284200388814103040c0c04901c842004a10b14940b030405854011100096110854443c01c00400899503034044072004075010300590a07080c2040c06034100b4560b109051860203080001054204d03600758000e58050203401e600a0a81e100b495065030100e0300c40300980002c52401 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 110118192 1250 110116942 110116957
    0x1407060b031603020a09110f21150f0316230301090501020a260103080c010e1e0709021801080403051201140f09040b01060305090a0c0b0307020d1704020f06 69
    0x6100d845103080e10b200e948402c0a080b24005c440b84c0c580350741d03944a190281e4228140c1503000300b001b0040c50f10000c031a2409012154400314088a5001104c440c415850304151100c01c40000580d443e580f052030b05123584003105401368042c00c22000030283c1c0482d1740895005241d40450b14071000340c04074844071010152920018002e0080006500f080340c000e5100801c0031001070740344060840514040d0084904031180030424405c20380c80c2d07481d80316060300a8200d00015549940c0d854990b05001c0045542001c01c030743c12840b030101e01d11100c1c2c0c035000c0c442e407001a13010300500114056100c0440500c03000c0c0030a0130300302015501e0303140c11240f03442400990ba2040b0040710002c14041c41c0d03051068000082550090000c00142d01001040d03501120b00500074a01c050040c80514841d030080c503003101510003111200621656032140418040d0440d5240980100c2001b104070340c100016640120b59081501c401104900b0101c280f2000400190240c0c264002030700d00c4d0f4551408a9a6a = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 110119442 1250 110118192 110118199
    0x9180303130b01050d0809060d020d0f0c090518011a070209073f1d0f030702040b0f0901140a09050a090203010e0309060a030b0a0803120403120c1407060b 68
    0xd07450302406100020031512802d440c1081c8210000c6024205680c1401d0740540000c40725060134560f10400c0706076842648904800350b001e1003462035100b09030091003401e841c0d000300480c201070206030081020a042c1d101c4d034403a02c0254105420300e038144c4951415a841c0c0c2d060b05065104018454507903200e071205c002d4220300c600041000d225440070203409403044208102c1030341801501682c00d965159915812042c1d900c00749a80c814082d9800103218041c1c504820900881e0300040c503043ca400031211040740d800008615086207401d10440303031308080c2210a072098038800404105142014094040b400c2e0080003180380d40ea4407248910010021715500340640c4c5401c038400c802409150038200c0c007a40c00c0c000340c44400000403040c0c805182000c3c1180703044c03803110f541c21009072500d20403035600701c2d40e071200100c1c0d50802800140741034504040414803c4c02c052070010070130f5580302ca804442d20f1412260281c00b0f903210071407081001c484900c0c40d0320340f00581010030003040d110511560 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 110120692 1250 110119442 110119447
    0x20a030b090706350619090608070519030201050d24030210110c041503050604030201060e090f0601050d03020c0a0626010b0405040216150207021518091803 69
    0xc1c0c00030009800020740b06155643d442143c0c1e100d09044c0c02e004a41c8050402c1c0e00c0369034002c400f4001d401d1100e54040300003820312102c101c520388003081b860f10310340100c03010f2034440340c05000d0740c0410480c0e80c00904042e908ac0c4aa1500144802204201c6000c0281080000a04040b03240e501d5004194030550300110b040d40c00c568154000c1c03141e00540310417806020906200700340e607800782c05480404c0c01c401b00900260705055013000700404034007200320500c24081d03002001050303041224612552181c1c00006106040002e8540c0903d4001c020755240d5100d080d04001101021803150304440058502c82101681441c06038203042d20100c00e5900302402d0280040e03178950010340007851010000c50145601031104440c4c911200c00d000d90100810104400c120b80d0902c1c0d4000d01450b00c090f09800780e606600c0e079949980180324078520300c6050b00421404e00390f140404410340d0f49046e0074030751840d0100e040b610000749003c3e4004640301e405540001a841d490814007400900280002d40340d = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 110121942 1250 110120692 110120701
    0xa030507090f08060a0e011a0907090306091a01150207050105030c120a091101020307050615030f0f03030103020f0a030b310305130e1b0f04270507091202040504020a030b 75
    0x21340e96002200c8142546042440c00401600d040c8503d81e2040d51514546c0c0310103c815080c0103d550001d0040c204100c1c2d1040008081107030b500c2001103051158400e42c01c01418440400c1c160703403060300141d507807003500200c038803c1a800098420131100c0c03c0c200310b5100e55076001044414001c00000d54104002c15080104031041c0d644000e1206100da1040b40742448100300490703803405643d0700148903a00a6021449100d03100c0c7c0a51140800101102c0e1500c06c5e80000071308010162180c00b0050344080014004c624040608803e000d4041d58010f5002d4910b032205881d40030090080280080d41e103400c2d021541d91580d54039807181002c101e01030a1102803500402d26444400300204991487c0d401042e8420302c0d1480d01d000d47c401a42c08113803484a14aa082e41c0e601900019007481010007002441c1950742c082c05200c540d110030841d04860700907801009588001b005c80c000c1105411046c044d1514000101429070340548000600d1303500c604c08a08161140e800241c04108040e0401 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 110123192 1250 110121942 110121959
    0x601050316120c110d0e03070e0919030906090801110a05030601090b0327010603030c021e0411030108060702010c1d221d060402030a03080405011404060c02010e070b0a030507090f 79
    0xd0100e4604c0300c0456008403450074048903d810002501c65054000301e60421500e00c1d01070140ba005110348081c1c48140e0f08003180030645214003082203000c0b4038103950070868143c114803034400030a854402407085c841e403c480603a00d4480c0d800d400381405008404161680d200701040300c007600c485105203603030342425a88444000116070000d64100342e80c0003400701e81c0700c2c18003902c0b0849a0546445040010302d60030042903081039000c1421b0b00d520701901c40c5981e80c50f405450300c4120103013415503895051858080c10064000c0000d015a81402a003200c0c26038030116540d40f14445101310000d10f1120030000e045051103085884058494190b045055445688500c0703071281520101c00042c0c510f04d1802c0d4503540120380c0694550030483c3c1c28008a40180a0305600500c1340b00005400e071501415001c800c4400d58050300d4403a503c606900c02213809200e680f8502c0040d80052a02038605140c0c2c40551140b40018000c16031508003241344140034051050241c03044100c502d00c01d50719035005 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 110124442 1250 110123192 110123207
    0x2210403051b1b0307030c0e25080a0b03010209030a0201050904020f0c0d090f06020706030f020903030307080a0c110c060705120d02090a06050711191205030d050f0601050316120c 79
    0x54120200300207008450301d01d00060054226a44031031f010711803c1c604104508500d4000340030200c3e0b0b0780b0394440300e458081c0d0110701003a02c2c2600e480780840c60400c00311100440c4c030031100f034500a030301c10004c100250303400184124107103034240317805582c5084100114011740070b1382c4440c541c2c5c1100400c80428502c0302249044d0240b0199603140e03502070f074500312124120700301c2c80740d040982c00c40e6006020152007904101000310741468054030700003104000c0391446d802110080d0000c3c00d01014800d21040e58050100c0c3c050081c80d02c2d5000100880c8480c0d00c4290364041d6031720032040020004104031080c0140160ba51071045815142d441c15845500a584032240b400e1080c001c1c1032012410500400541d010b95400c40c0e4412658004182031018466010034007644010f440000011084450003588c0c0c0458860005035403943e036002c524034245c0d0710103402400804005001c001099074040103495118200000000e40c1343c1c120300b8281c83c824040018500301908082d1909900c5410100 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 110125692 1250 110124442 110124463
    0xb13081c0b0306070302120f0408070b07020a03080105190e04020d0209010b030f0907060909021b0304090204030c0503150402062209020705100b010e040f02040902072402210403051b 80
    0x64800f10307600c4080450032846048920000f8014410106000840e01200603600070300c2885c11520380003881d01c461401410881c1d8a00060380b00004034030805a0003008a401000107885500404c84d01c039004410b0070a96009a000200c1260005800d555800a0051603d6001342c0002107950b11200304039100c0c7e200722080220100c00c00c005c2a000b401c001020000c0f250741d540d464004604060070709000e50300442001c58440b440c1640c81d41c02203000d00061004120541005907243d00c0c626260303885000d5940407901c030341c00080b241e00e00e1a07a0065580e0b801136044030600c0d0744044110049403100541d90101a001d0f8030b040010441d946141c0c000c0c0080b41c0642c0403039030800c0c01c0160001c02e54200511041c0002c22a00c5040705508050300690114100c009000d820103440b07485100403a00001029600348980181007260301801e2480e4070041d40000300107614100c089400d00729191030601d111003c0d01505c600013814148100251908144050140344141e1a0800c440303a841e05c440b003 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 110126942 1250 110125692 110125699
    0x50403050910022a12010608070f0e0408040603200301030510052409070e030604060903030e120405063016052d07021201090318030b13081c0b 63
    0x1c0c100809000080b40344c074602410703696455010340201d040c000d252918520325086004621400460780c020301400016064505c02403841034600b4030401c82c1c0f02c8040d48003581d050242c40030f02002c1020b120448059444505012a181c0c5492607440d004d03040c48201201c49040100020041103004904000580c580710418041038907007850840401e0f489460b00d9880f0100d8240701c1d0a135041920242da48150700d42000b04e601511080071a0a0520441d4125590380d580c920003802c01d50184500ca6160f18200300034049440d00d002d100c01c25109500500e0720031400441c020391501c0c034000480400310070b10980c40f82c0d911403520045907201ca080d1091400340c41c4203102082254840c005a0354009241c40c084004260f803100074901c04c403e90021610360450030060280035880e80101c1aa81d50104e80000032140c2090030300801942c00c0e00c1070340c4510302f01c1403020000310752202217680d0004240d04c0c0446850300580350001c0544917100c0902808442c00c15115a0a00298000c00c10044182c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 110128192 1250 110126942 110126959
    0x106030506040c0e1504080106260f030d1e02042301050c0c010e1f020313060819020c15010b07020301050105090c070f1410022505060105010c02040f0504030509 71
    0x707034204003c2c1d52000c1440c000281031064403e00928020900811a11805004a150035190740342c85094a440750400d20020105d00746a071f220655015924803902c050301c01402018000300c41550310707407040720348044520f030702d441c05082c140e842c0428412101000325403c542c1c4580e91583c0344024410000d001320b441540745c030300c0c03d0700b540154115121500d040d00036040340e034030600c015501c04100c2a440ca4201007a00c100403610710345402114041c443c650011912041b6661866030500c8194120904022074a002c2c480000c0844003000d034480d41c645000358440f040340c58a2440c0c014042420b02c1c103c00113800026071815020700030640907000f036009002c03607a02e80c1c0501000040980da801d40c450303c20440301021070418140b05010328400c0c1c122900718001924a5071910710190401200154002005080c8050309458100190b02e809480070748400142c80b441d860f4401440b071281400601020030301107540740c2d03011881036091244204090700305414001d0041d048581000d0042100 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 110129442 1250 110128192 110128201
    0x907090510061d0a062601030f0c080d0c1203020c07030c05031002070218090709020a120b010c0f030809101104050906180411010c02030f010509060c07111002030c0d0801060305 78
    0x3d5004202c91640050268500b203440c20308212a0701c2c00c0131500380600c46800b0110030b10070401304412402140100940603d0703a603e41405075601c82c0c580d00002441c0e00549203c00700a0304403081d10308540d08a6448401c25080c40d01c150084e21980c2d085400c01d000e0b082c0302000308001220040150b0341c0940450b03123450807218500c001c0744240304001c0d501400c0c002e50b078100d0341003112035180e211a00038203451090b5594484402a07030030184030369008c2503000110000358030180c4109444490240380c40b1009020701d42350034504403d258806400c2004990000708424401c006030000034245c44010020903c1042d082d4490b50424000d503481070000b6000b040c030900e80320310145c809120305440d8840e55150303940c419100c52024841c2505000c18544030801607039003401542c0a41841000228603803820031306440c180f0100520036441071400b0702400e404100010070b044203003081a280761010310001e20041c3c1c914007486640912900c02c11244071381c20f551180300103040f03484a4a051106888 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 110130692 1250 110129442 110129477
    0x10602060a061406090111060c07051504081207030e030a080a1d030a120b0604030b100501050a1713020301050118050601020114070c0309030203030406030608100510050108090709051006 82
    0x2c0e18851a1100f08208141040030726140c1c00600078400141043c0c629041c41e035540c00d092035421103500e90000300200f02c580912006003c912046090503a1421701707840c0542d901c403014050b8880c040074002403c0c0001d14140e0090340b1840c804000d00003241d455000c9240000c0001e0403c4034201e41170740c00c1031003240000d0520741302014a11404405035041c00c9804100700c900040d40441b002103151142d0700e180c01921054000c2010358002e540356134080c6003002041c081d5072103a900c01410000300708803c0780451b42c41101c444040c00e4034880001d00341c0303901c01c2e40280c03e88181c0300690706518101c000039004e904048681c50402042c04103100c0c40e40c0d0000168203d030410603050351aa80c2d00400101040d00c42e00c00401114400d04003c00c41e59200d4001c2441c64000b40c1208001c80d03034402040c44120340400c4443c0c00d003c01e0540178842481d04104000c4244580d200e00ea06010b10030340031950422003886501d0103001c0e4808104040c0c5010b50b456005181184509000b01d0741c0903914901d40300 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 110131942 1250 110130692 110130701
    0x160c0503070e0403080405070504020409020910020d050409021818071d090408090d0c0806060a09020408100b0102032110120b0c0c0307060203100e06091b03070e0d0b010602060a 78
    0x20210ba03010304030303035840e070300c055510703810003042140c1a000b140004103641c0d4a520142014103a800001030b143e450041c2400100d207110206282954050150a0301a80e4004115400d03207101c0480903880e0172000170760103200007020481c141e0000301040c213003c0540140d10424031494040c0d6402c45080000159816551a0150041e4110340c0a00006022032403500042601420240005510000070389502014440360340003003525400440074000707146001480f000180c940d5910442c0f8091800c0c0c00d82e551100007030301d0b402200d5160144400580c2c020300903912000b0321180c0b5080007124004d008034801408684480c0c580342c02e03150214520400c1c00300301d6031700790344000380d0f9515442d03184d403c5d01c498021051410040c84100202d1001a1190002d50700070f501d9020b0308602142071015000c40c801c0020002e034082d460250400540d040e1010601400c624500304080c0e0704e48480c0f00803242c0c00081503147d908004d0717903580d020130008940038850487e4555800c0d15400c3d11010810804d4a = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 110133192 1250 110131942 110131949
    0x60105070b0a09030c02031516050f0702130225051b010c03110c0a090509010e03190e0d020409030c050f01021e0f04080d0801090b0f09040b06040b06160c050307 71
    0xd001000110225040c3d03100500d114000d08041400c201c140e030000f86040406403001400050140510403440f40074080d034000030a00382025404d01c101000c170000e0700e018480000e4450341010304100041002c41e070460305400d40306441d82c00f100c1c10b106c3c2002c07001103003080c00701d1b11031040c3d103000302c3c0c40d84040441d8400064141d507510b00020907600d0403122850728a040c13100c0c50281918a140a9950384200b400800d607515001c036591900c01c1e115402c595013040e41d244d0642082101c0d41e83d000c4510518544c420282c00c2c840030903e00107001c55440092083c000790068035001c113030000d164000140710795a0b032282c802ca030030081020700d00c2803e034060160080c1400d69800050843d170020750000c3c00d070310f5020258a03414981e81d522000d1801c10390000520200e000e030401400580007500942d114840195548150710481d500800e00340d200c020005004440c0b1880070404655544d000240e080390010015901c4248908e220098032030341c450101c40c02c503107440e0001114200407500c2404c9 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 110134442 1250 110133192 110133203
    0x706150305240c040504050403141308060c0a0206070f1b06020c0615130c03090c0e040c120c1701020717180405040b0c0702060403140d0f020102120403140903190b06010507 76
    0xf0146820700b0306c0040c2a0280040f0705100705420350728604003894010340b5640320886007031040c1510700301501d03052800240000da88801d0810801e6141900002c40c2c58202c2e4440c50030790001c4e030506104580010740b07c404100c03152a500d100c4410b00c40c854002d042c1401001007034540581b201c40d07850700c140011066298102400381c0a909503101a5480260034105508010440300d03041d5035203644a02c000e0300141500d000120902051041810f0300714003070318a000303014030710190f2a12000000480c070310070211030400c440b100348401d5200390140d0700700560180c1c14a1811020100800c110707041207081400b644940a0850418646401020300480e00020031030b50a446580412105510515059801000400c00040000e154202a203020715220001c3c007111482d05070000e0125001440d0041107a0050103604943d02010107410b4006525050200c1c1c030448403031451005005000c00c0980c540111000c201507138a00c4100c05070598800d0614144690b03400d00152128014a68042d06c0b = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 110135692 1250 110134442 110134447
    0x216030201032c0304030309150503040b07051b0706022a0405060613090203061801031208091f0905010c0f020604060e0307080a02010c0908070b090103020706150305240c 75
    0x140d4026404100e82141201030040050004a22150110b240c0c0b880280d01c4d038400541003080c035510059500151008003c2030030b00c0565003200a04600015002030318400b2014041095580510200c03007a9004503d500d1180f01c22131110745031982c205d88254400b5016010b04015805a540f61140c11940c1e86032041c1310044250050200a15005100c02e03001681088991200d844001c43d0600820f00041c015a59103040c0051114072000000e120105508000c01400010790166000c2c502c00c02903e00040709956412285203002484161051041031085640945031004d80042c40001e005400038010030303180360340480b20242c0744d584907001078000001003000141a40c10800141e81c000303040341d0030841d080d2641e03841640242c1441d40985e548030206403886802c00c0c0030030020840c0740f010340030305441c20404031380318864900550704040c1c0c0060001e040003890b6210035089941400000c3c0003a80328501240d541050714120401500c80100c02c85c003140e640c10f201881108128412030 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 110136942 1250 110135692 110135699
    0x1206020f0408011103150103110909041505070201090317160c030e0a0b0711040507050a03020c011b023904020901020a050d031b08091209011103070501090c060216 72
    0xa40000ca010320895004000010300349100f406000c03500301c01d46407016a60b00306510f8510075020000e00c19030505080c0807601c02030143c900f055038039030365060f17039031a08903074451030802010310594a51510721482d103801d10110390f0f4154000301c8c141d440b90700d601f5006083c00035402c00d000002c46220584000e440000c03101036220741e00d00c460452182c18036514465800001400c1b400f1180c100030090180803840000388000405c61155849081c0c4041040342090b100c014040c0c45550703252414550002a950801203095200c0452980030254404100e800000c1c0291503021407240be1100d1070200f0b080c80e455000070b82002c2006c040c6401680c2560244200b408040c0d044000e100b4150300400c100302d00460428000a03c1d400b200b0b542c00210040140b42020b40222048054410051020100f1186d0040055a0100c0400006407161078000c401c00407070b2a403452241440090101148400070010150030080f900f41c4104100c6016580700c0c0d1040742d9812b42141c1042c1c10445252082 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 110138192 1250 110136942 110136953
    0xc1401110a0b01030311030708040b190c12050310050a030b0703050906070c030e0409060203070305190b0f0d020d020604060e0f040c02030a030504150606051c0501052b0b04050309010e0a12 83
    0x8103001001e001c07d4900344800d680b00c14000e41c0155010102e400c00011340c28800000c0c09062081da151103003070240720b00d000e036201d109104481745a032605211000000c100512806003619009080c000c220a0300d040d12840e04054030703a0207540c544046800c0034046040c0a501040151142d000c136034a47c202d03c031700703614102d400078503001001d900250703a2104440407486078001144944143d0b2000702d014102200c8042c3e210880d03046030107a05117400986090365403203000d060344035082203400444540081c00010807103480040000c1d40310708002000240d15801c64014442d01d54100c50700028907140905204c2500c0c40580900d0068108200c07408c03480c1c0c000e921054102d80118400c050201e41a5440400c944c0e25402c1440031600110710603602c05010302c02c201401c24500c1050046c0e501d0440464036545540144210a45080c2d8029489480059411511513001084c0d07668500700380c2000ea442e50f002d0340172030740025000409400c107410800c01c00c4003112044042101d48041325180c1 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 110139442 1250 110138192 110138207
    0x30305040201050d1a090601050301060e090606160b0a060504021602041d1905010f020f031611010f0e01050612030307051e03183a05070c1401110a0b010303 69
    0x3207043c80310500240c401c1e0700140c451003080f00c00c0203641d40142c100300f80070000002d200405850401a0400043c00700582c004400d8140301c106139091074964940700700103083c80c000d0011258005580c40f507044140a10043e03d20f024105142c1c08001c0d00e5140d1080c00264404c1c50071401201c400c0d03c444800606295100d502180b00400350390b80590100140355041c81c211031048000006001004424448284154a440d0181c8501180350064020072180c00c0e00004080d1030740001d422070042c1c038680c01041c0700584d02407010000c00c04c0c81c485a41800003003242901c440b0301980b920b00098150300b450400244405500c10066080d540c0ea490110369036400041081a44014000c25400c0c04c0450b00280d070140b540710b42c0d055000220048450b11301a00c902c0c00714030840c0c020f4048500c11005188580480001000402c085522a54142e80d0b5110358080202000350381100015039811054145521103000d90b03600d040002400b0301d00e683d8141ca10030141480c0c0341240100006070083e140c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 110140692 1250 110139442 110139451
    0xb04030503041b031110020a0b011e1701021b06191125020102060619060c0c050d21050f030a050604061805060301060e070203182214010603020313030305 68
    0x3d240881080c0307200d280390310081540c82120b02c0c440b049009000c6142180b1503114000580c80100100310b09615002d4251006201d0021121000078401c42d145214120090103030610741e04140e0301c1c4240d01c01c054001c0d0b20041028903c0e001c07141003030030203010100d20a4004c0d40c840c107940149040720745410f001041c5040c034440d070405003003240c07941d185145803d881c0c0012000d0b205520f0000b4500000e424440010041403081040c41d000f615141d89800030300c0d0940300646482c0c0400c2d5018034108488441c0c50300455800303404005605d003046200704403d00d504c192070f148100c550121003015a202e02608040255a40b81030001855a441c0c9511140d0b202c5001071010405658941e07480c02e084040c0d10440800c1510b800c1005a141424084c00f00207061094044403185000c0320300030340303d0003140201030b100080c043e86840035641b43e5403010500b0b2155504182014040601c4134020803641c2d201c400701007142000019403d0013882640e200c4c1198080749041e107a4181d03001c8001300380040 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 110141942 1250 110140692 110140703
    0xd0e04020d060b030414010b1302160c350a03120b0603100f120201082d011d0603010b0105070807061113051309080a0c03090503010c02071e030b0403050304 69
    0x380c409140c1c06406035000416203880d000d656414981040080f142520744001b10981c10401e00d1030a0f82c440130620107404485070340060b11514610000401c07100c031440081e18a0301049000719000c0f0104002c041c210203891104256481400400d5005c2e080001d801c2130190000c408800201b40210341c1c0b030034007858038880020200d1814001440c1e1303400c260b510318840c078085c02c030a000000880c401c2c00301414024a000c800031010340d00081c0042c0d0010030742200d224007900840011001d10403840d245000c8560520b11941c2c40d00c3c07080c0c0d0b160000c0c40300c40441f001d400010442500701842094400c42041c2c2d1054680103558580307102e2503004540441d482641c030302c42841c0b50055100901aa03105480c00d0410b86441c010820021000000402e030245103000d800000203502101103032481e6000d03040805201409041c10b0700c0c0910164843c68041d42000f42c11700300e041d80070072008142c070680301031604400b501e41000b5854039083d01005007045981ca0115012074014005158014400c4 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 110143192 1250 110141942 110141947
    0x1e06090a09020a030506150414060f0c0105010b18010801120f081314040f0b0d12022e0c02030a08070806061b070302040c0513050402090d0206030115020715020d0e0402 74
    0x80c480301c03040f81c0c40407205100190b03443d41481124500040002c01248040d14094203180c2400b1006a0084030a07825030700c16800000d2049089010406a80710101c050000b00071642e03507880c540c096544420441994404810511040c641c000c8241d40d0603a8864a241050768840e0380c0d80e2086e00c18003040940e10031805014000c0d07001a600c0c00320340035112024030001d172518000240000d6621269000c60403e04100c101c82e101e403102c07060b15010300c5e0400c0d2100c2c001c3c0300408050381480c0700b22181802043d6141290301208000300c242ca010408145401c1050f120018003ca0b01c0303000d4013020300006500000880e19152084058641028005000510f464542c049451003041c0341007141c007594118840c01c10039403a141c23080c0c21505120341030861a0072a60010022402240c1c013440d403003180d0115450074a40c8a10f01e01c0c2c0300e4907a018003899900e5031203882d15026405100d10850051090301d03000320b1b101d041c02c17116480d440040d400402054962800640310400c0001c5150b0700164203 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 110144442 1250 110143192 110143199
    0xa170c06073f0504140f040f090c1701052203020c0916090506040605090103150902070f060c03150501030b01020c04050a020405010305150315100807060f08061e06090a 74
    0x10403204140a02d032044048080c003403400d0310036062407060040002400400e100c1001280414010390600c84000c6450014489441c2d000a00924103400000c01c81c0d40f03450040310030845020501c40603107101c0500c400106a20003103003030903950211240c01e9213003c920119500960401008284940b29005031a030009541c0c0100381c583c1c0f81106e900f2400390950131002409a0050400c1c00503020698400e45418200300d009082c0703201d806a5941090350700d548641c80790940105000103000d04450942d80c070350a80c00c216144217441442512900e20384010140c0e02c030301074494040d40100420300440c00a29200064004044080005055014501e4541516034441c414a80704403200c0000686503820800010100e410081000441149040d05050785607000664019610480018964690b4400010329182c1510381c1c4050b5140c8a0071002091140c0c00918441042d541d966401400b9a140000c20014650252503a81c41c00800385446189080a10080c10000b1000d42502981c990f0b = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 110145692 1250 110144442 110144483
    0x180c120c0915070b0601030e210d09121b1121100609060e0108030304080f0c0a030503011a34051005070905030a03080c090f04020d05060a170c0607 65
    0x240044001d401c01c0c400100f940c10024540780c1150000e80a01e4100b00c001d0361110500d03956202000c400341c040c440201307980801c3da02107040361020200104140500403080c40d000304070030750f454481008240025030013007903c101d00b00007101654000b204840e07488a80720900211b0f41042c2c0b074001c0f16140759407280000c03070810005098800007041d4001203240c508540c0204491003070700041413140c6140c00400c02c4090000a0360340084d000304010340c1e1002070292180b140c0c4184c4800c442c0d03500812900da401c2c19000350145040381c15201c8001003405c00b2416540480c42804c0c0f01e0402c426240c0d040b003940e0b0020032a00c58204d544111602c7c850b01c002d49815240081192040001e1515181002900c42d070121021000300701c1070b00100b5042c6401d9070b0203440440b005160042074030001c40c6a004640e507103410f0b00c0c5442c2010b8021982c030f01c800c4030381c1d0010b01000c6540d1801910000170000f2913540d44010814019080c4005d44a02e5400e80200702003540128026101003145813110b90f103041d17 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 110146942 1250 110145692 110145709
    0x60f1903060e0c01090e220c050315010f0b0a0c0803090708070905070305010b04030203190201141b07060c020d1205070602040e0f01150504050d1112030a030e0a0b010e040201020f0607030b180c120c09 88
    0x5481980500c1d62408254100060f237541220101c0d07807007070280381203241d0841002c04031281d020f03140759140d954030b0b61403034500111036100c44550f100d05100001e01c4109a8000c2c0d00030000380ea02844580c2c0c80d0101c0301003d2203944802500f580c004d801c013035440342000441c0415a44145003299a400600422030707040c0c2c2101004a50980c02520001d1141d0410090440184401c5c244410a00c0780760b0004ed0845110381070203040c000704030380c2100001d48610121010705600c040c046442d152500c403c4242d640c41107841c059898a00c900101d005407941d0002040d450040c0c1d00c0524050800c81446144449074604403818002d540c491003030f42e0340d244080c10906c08004000c5883d0310540c803001b0f0075130308200c4800340c0701c4c0c1204032444045480c4c21072081c1540c4400d00e40301d41684031071004030b00d0950905c411004a020f0b16090010300ca5164022114804c1c0490703102115805003070481401440c00d45d110200a64208039019041c54030034441c0d54850703c0a41c407581010262404203d619 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 110148192 1250 110146942 110146963
    0x50a0b09010609091407090512030c01150e0f06090a020d0b0406121208090304050103020901020f01050a06060207050604140906010c05030a0905041103060f1903060e0c01090e220c0503 81
    0x100340c01014841d0358418070424076080d00c455484d41c8035080800000d0b0100c4448c5c001c1c1c80c01244030110060508004004482481080000801400a4500300000454802c3c06482c14148071600400d5845926854041c00b581c00181403101a485c2c54403084025400300b0045207000d9203401007112203a41d07600c6408020250700c980900610303d545040c01ca40b0300140c03100403d000780001881200c01000040e10140d50003800c00681c1c612000005038540000010f80300069800d1104000045070303035070000d1080b2000d5070201e40400352038908000c0103002c0d0f8024902096510480f480f86803500401040c0c0204e410706011100074010340f41c041c219413000d4290302c0071412a4408209a081c10f12a004200600c1202035045040440c0040c1c1c140e01c2c1c02c01c0b0b103072260030004c1240081d0102c4007001c20003181c1c401c5080142c410441c15258450015484c2c0d2804119206000101000c5102403a4130489000c1860740e02115216500302d03410302d00810540e00c803501e03590040b44580701000300070800c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 110149442 1250 110148192 110148197
    0x60c13081903030e030301081506040f020c010b0a080118060c090b04080102040509060f13050703020408030a02010e2404030f14030106051c06060203120405010902030118050c030c010909050a0b090106 88
    0x4580780c60030301605503581c0f2244660141d00400c01088230401c04074194400118040311310640b1707240c01c8005800b80803501c0d2003548940c4006584101001e056001e98040501910b0700154189d035004814221040c1c3c8400b40700303d164800c2d88000007062a4040203414080703042980138140c07900540c000f01d8209411118450394005030611007494044c502c160b001e10704031110341740040c550010948118080904518460300e80002c100c0042c041d1701034901503c20340c000c49848030044040240a0840034504100500400c2d107a000880b038990006013803149004d8286240f80c649607004c40d03050000028000c1007040800440200300742c01001903000b00030540d0303070680b100710101c10f07455040c0c0c4200325002140d240820811055801000b9a0980709640803200d059940302c1c10400c0c05040c6104009605508e0034003007500b141030400c119020340340140110f58001d1903040c24190303140a03403044503000c0b17200748a040120490f690081507100101d400b01288c06203049001c07444494080e000b2401 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 110150692 1250 110149442 110149483
    0x9030307050d0f0201060519180b100315090b030a0b0a11040311010206181e030904020c060f090304060207050f03030d1409160e01060309020a0f090605130905060c1308 74
    0x83e4950901941020307140c1120141c41e003890030102501403110501c1507501c00c400701c2910400300e0700a036200e42030040d4090b01c101c90703081c01c480e001001403c0c0b981d05202542d1600901041d0024984980d618035040600200021162a12902c00000b401090341a105071204100c81008407450003400c003c500c0364110355a4003c00400181c14940003e16144c2c8855920300f40500801002440d281d40700d119504070b0750411448428a41584140c403c03903600b00b0f00010359540c2c03141001900d00d11500710b990816030b1a40300d402c81c0d0b07612445244142c00c01a030203c0c400340641d00d0200b135443c207002401021a854180041e18000070303203c4581c038040c90745202c4001c00c414010144403414501d10500c0700981050708241c80154107140600031041096501e0441c0170440d2951b0b04038001800140e00c034105415900e6241d100900b5003801481d0080d0101c0541203101c000c1070007002c503516405030103014155101c0243c2c561130b4016400010403c00300c10700000b0826001c1c407896a04031082c504481 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 110151942 1250 110150692 110150717
    0x3040510090b0f0609090705091e1503010b12060703020a0c020405040c06080618041704080f0a120306050303090d02130f150f050117070509040f02180306010506040b09030307050d 79
    0x59001c00d00805640c000e82045c4204042c062000c0781c40400ea40701260010140d4481c22008401c80d0440c00328900460401c00600000d81c030600d900403034000b42107000744130a2107440140901c040946000262a40c031100109059501a0700030b040e22030100d213041c111055050b0005001da40301500d0644400708103181c140549548019515403203581980c050304003201c03104040c0c40c001ca0080015040052a0280f14804100e1404a60042404100321803c10f03c2c41d0b2000c42d05c0e050314010480301514a0300780c2086090003070240701c04450f402800b0718140280c080502820400303006040781c1c403204c00c20285114411921a840b400c0310030f9880010742e40e8103088880018000ca030032414045040d280c0400150f0ba00203c0400c48110b02d0118608548404005640f103000b443d0410360b00c0b60410000c0282c120455002d040b046000c445901c0104240c60281510ba40d000c0c05007540242042100703202c07841c2c00c18014004250b0250490f0b2600440f612414203241b42d44d40a10006035402c800b01c03 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 110153192 1250 110151942 110151961
    0x61603030903090927081b060702060a1e0e0109020a08030a0801090b060a050f040e1303170f07050708070606030c1d010b090906030a050604030816021b0603040510090b 74
    0x1c3c0040e1540c01070400984004e12181050340400c00001c100300e40c2a000d1520401c138204080d208208140c03102e54201c000da159070940c8802040320420700520403240080c00340e203018050b100720701000d1003050003044102542c80024009003440503029640712009940107171212450310f001010044041d43d00c4107100c00e002402840c06078403881c0d40600707006000c0c0c5240da4140440e003800c0d5840c1800b5503103075400c40c12108a400350b9440361003200702c2d90f400c0011210908018002c03882c4240d440641e02038941d48940310294081e155a100e25801e84005030f5940e002d071006100e4075001e039822a043c0300503603440d0000d584940e00211a1550003900070444400d1001000060103580d07203a0145540c100540c03d4028025071240511446140c404100251010720141308015005001d9800c180381a0a0140c00c15206444c40c5c500480398100c200c03a510320115500066a022201c10060704000b182000b02c1d07030b00b026006407018001c3c171221980d0603074240f14452426116001900c030914111560 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 110154442 1250 110153192 110153207
    0x190602040510030b0604050402070c0902070501060611011415010903052a180601081302031507021006030f1202030903030301080106080c01050301060c14010e012906040302010c060b061603030903 86
    0xe2030a060400e042c0713510655885098a0030b48006503001a124401d50501504400399a4070824009100145407800e00006401c410280c5800342c40703002498455007009400c8405410501101440031800b05442c0a2000444801440141f400e988038540303e486050920f8205a19070000e1140000c40301c18641c104980386520207021210420942c1c41c542c41c4045800004141a040004240005900112804d0ba10800c2d5802a0846481d40707084007450800e500162012000f612881340300040035a09800f8400669510000e00000c840c2617958800c40090079442c0d200543c00184081006610f041000d10300802695001269103454454414240701c01c207210141001b0003003006000345504070403544225980305000c012120040d201440c010034079203031502215420032080c4000c103402890300c1c491a400142500e42c51051780d03c10469144164031000b808105044210750105c1c196a1003002000c1c000381c40203180014089109802080901044010950300c00160082c107900c05131 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 110155692 1250 110154442 110154469
    0xf1505150a0503010b131203030c12020301080a02130905010507090312030b0a150309020307060509120106052115010b0403150504081803030906040b25020a171906020405 75
    0x1040c61034201a6480105144014007a00521400c001080d000c0024520b20f080001c14404407000c41d03207a56440e000b40a8042d114084c800250389246d40d84002600e03200700c0341210500030082100380000c0c0d080c4440c0d03036601080c403500c0998441e00c07038010030000e004176485500750303a503110151340c25484e14078404100102403008040c40d0030000900c5442c3d6041c1070b400d40710741d909210a5000100303030403006001c00c01002901130040c40d6000940a1f0800050141c0050807070300080d901c120301c20454201d41c07251040541c0b01c45500c400128814007106078000310501c41c3d058510048402c44c0c80165540282c2c00030503000000503040050112100030070b0490302800006200c24200b41e2a100100d0041c90210110242d5004456916a904004440741c0007400380c030701034607241c2d1492000f0003600a41042210411220b00e01004d4040070b400c581e908660003014442c1050034242204e181c01c1d020000d06100c0e22030b03005c04040d0b00c04007120b1401071034403403800541d071641001c0a00c0b0300c180d81d246 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 110156942 1250 110155692 110155729
    0xb040b01051302030103020d03050c1e1f09150207050304030b0411010807020a03020c0108091e0309030c0102070315180f050106051c020604150e1309120509180a0f1505 74
    0x46c401a07540c0051240104e416142c802e4403044003040c02c42c20302010154020317665111102071241c0c81804110070f180112001d21031102c038500c01c2d58138402d6074010342000b0808c01c40d200c071000141e84d665010705880d41c0641c0490341042d880b661503000c444415181910700384444410740c0380175030344102d03916440381461001c0c00c8180c2440e94082d50710075585c03800c58144107850000400f015000c03c1007080411007c00805562030b00007200c940c403076102200d598000c0c0140321202c6030650001404074200c950050328045442041d500400040c98607108141c0104150b02000021031006281c1c1e6840502130400000c50030f180508000c40d030404a01c140461007601c138030f4500541c0e91803003502d0071034280381c0000019a880107421221072010b80180e41e405081c00c21040441c0302207a104c80380385441600f4920300c0c4040080f00ba6554010745180ca030b4403d00d03104e04110180c050110075500328280b03100c0801e144031021592803c1d00c81c46080c00c4612030b01072a003009940f4002c8003005509100c2c0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 110158192 1250 110156942 110156947
    0x1020f1c17072c100305090c03011418150a0b0a03230601150f031d0d0906090501020604120e03010b04050c070303050117033001030809040528180b040b01051302 71
    0x43c04101625403408a40050690744e0700064070035003040c0100032600390014000c10580340a000c001113815001e480448541600c072046034000c0b00300241c17003c880e02000c105040d00356184000000600701c03c0301c02c1030700020415000030009048040181004460050741185150901d151070f20300320050f401911003580c0d44015140170341d08007158900381d59042c5408900340c5558111020f0b0080c2d045128441849204030714181c3d10381c0900303036400313484a070b542e102c0d51540d682004982d42c5006850240000780000032460f0750034040d001014600e580680040303207500d850000141222011203000540c3c2e84000382240408d5410301c170b240c0c05402d528990090200784003841640d030b409510854036640c98105409042c0c800e985001e0b1101c0c07400d85015064540e1a850080c0036904a03801340c0d030155043c8004210441881c1c0b41415410340e81c4211513a4800702502c0350000750862641030301c90190b400380105c4c0814a51442e041c4500d00480e1a0803055140805110800c81c0e8a5a440004c500c10b = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 110159442 1250 110158192 110158277
    0x30703240501051b030403050304060f1d030316050f0703050f0f0303011a03042a03170309061f090905030a08010e0c0d020f0f07050d0e01020f1c1707 66
    0xc41501e88004066844d12061031003a80740300d1862049800181182c880410001056030307200c040600d01094580e0ac04074038681030300c00189400300107030320380d0752681040c4024071904180d82120350700c3c1070051080312200c4450301900703401c1c00303910b0b0070030703100d641049440701c624040401c004000780c141c83d4019440c0d580341c01145079500d18a0b17100e0141c00c1c0d000002060600c1204c1c04840130340c082a0824007002d900840301c55982558611085400c040c0040c0507420b116481000c0e2881490070401402d61030341c401040070324503610840c00a244c8800c00034041480741c4184954401c0c1031060380199a0f070701034480c001d01020360580c014055207541314100b21000c0765480550300800c86040b030250711f42c0720144022401c2d00030045032481c000d2000c40c2c000244031000454840ca2001a01d440722601000c0004a031902003e400303504695003c100c0380400c0540040c0c50405d0800300f4a4807100101c00f102519090940a503880c034005411451909141400d807030107a1403006864480161820f003 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 110160692 1250 110159442 110159447
    0x607090f05010c080705010b270c040b12181e10050702121303240e01021327020408030c010c09030c03111906030614030601050a0b0a14030703240501 66
    0x200c50f800401640d03011602500f0040250091168410010004400760b5200452500c0801280310f01110030440000400c401c0036000007110155561240000d02d0401003000390f484d4540094150400004c62030000d2030108024440d5040d11a090401d4140c00d1600c550068645440207030705000d41442d0006000e02941c000030034080500040c64111b458080034001c1050b480c0695202600580d411805401c0042214500c41500c0e040001c0030031002c152814020b00301c0c050070716030383e840c419145000d00442180c0901a99005034400040340f6500071395100741c0507600182d129036815800070500b50a44003080c010300501c2c50240c03602c15902031464541c540340c00c0c6c90307200107400341540d405006081e4441034601c0c0404140c0c000c3c2008000e40c1c950340100204074a00c100e41c044d5200d151011070301d250108450f41203850003440341a186007048192486a0300070800e64050241d03046602855081c80c001a5228036015140003e18455004c072100e4050168107101080100305034090102ea038 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 110161942 1250 110160692 110160707
    0x5030601051306090f0e0609010b0603010915090903050c060106051611030102070c06020d0201060b0405181806070c030e0103090c0e0703090f0b04061811040c0314090607090f0501 79
    0x100101c50040c401201060b040b00104040d03002508040e092000b0201d402c14681c00c108013440240c0c0840c0c14507580e14208500b207841c03402480303500a00400c0104003c0141c5d07004003400112440c00007112950340c10a070401c0310038405007240400c1d004075600c0b03c040c07024850f9a005200341d05100380b41403072419948508005a8800410400180094100c1c584003507059615280d8012018a481911114040c2d518032000000074015806c00c2c0000c42e04002060079102111005004034040fa0702c0e290104141d01d000a260741c0750080310dc1015205c0c11410801c01303014400f10340720100c0c842c12506001340ba003d401c8014a0500d41450011301c0040e20030850700b0b04660307800380003900390b40711180100c0140c00c440d0390207400380705500c43d40c3d42800307503d0b02058020762140314200244440d1001c40c001c000c80d60403003d08021030100d580d0000b1f080035082074240b5411864000303020f42d082c140c0204095415152046140d00841c10405030641003014100900140780c816070009292800091004 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 110163192 1250 110161942 110161949
    0xc060f15170c101b0c0315051603060807030204020a0212030c030712020f030f040c0b0706050a0501051203031b040e0a0905010e010b0a05150d02030c0703170601080703050402030705091f0f05030601 87
    0x113000f0344c28030f40c0034049010600d80c041d65100a080c0007025061130f0020241c00181e5400c0c400d1410180b5080005010740300d04001ca4403a2006031031014556020440250042c441d0f05042d400f880d00c3c0b809554032400011845101c3d40d0130b41c0760320303404e003140b00815441ca40050424601d1040114085c282070040980c2c7c2d02c0600204a2004c5642c0c80c9848030080040c1c2e0700400304000040303441010040c2681041e8410840c210301003106a03650000c1011300500d0009180310b41d001040071135010560400d03a1040301200c00141c510b020355601c03800d106108202c94052401d90749420180c200a420701032918030644007002030007140001e8000442d569035a126881c85403a2a80e8070f410440c2402c42030b20240d0840390700c119280e242ca0f40d081d292a5002c03e030120001900700310101c110b400d50828a50281006a4503002c10341e58005080d801000040c1040c0d034944a41c00b0001184d5640312801d43c4240e1600510790314038045101c50480540742070700240f081c100003131014429501c0c0081c185046 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 110164442 1250 110163192 110163227
    0x3050c04030b07020c030d0201020405090f06010f2304030b01050301151511010e160812030106020c0d020f0a0f17030f0304020d0c1505070c090c0c060f15170c10 71
    0x40f9125800160300c1d207108003a20942500622070700245254040d4043c0c001c4480941c0c60300f8032a41c407455000d2201c4011184140810414544481c01038410200d003048981c0c01034600480c0e2148a8401c030035a0040d61003122107403c0440140600d00302030151451504403e0400310220741403820300d03006c840b0135030394940c200901d51603034000016003508400c202c00025029500c848004c091a101d003584540541c0f4045d02c81c8001607407440105100700c90407120b0540c0908031020404081201ca151000416a072002e030424108405503a0419440d005141c509880030001c1d14100071490720b419030b40e0080410f6001030007600c1c40102004226640f00360704441440c94000303a0300d070061110605401c09135a40110000e0b01c130225410a00038040c05000e8080b814500d5650b030f0810003a104c03803207078100000e50405120800186070340c11100d0b90840b5110082407003170202022603246061030b4003441c0c1005406000340380c910f006108901e04068161041c2509010111000d00784820102e4401030 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 110165692 1250 110164442 110164463
    0x1c0905040915020d15030506010e06030f060a0b060f0307030c020c0607030801090504035702090405012912060c03011208040510120c0807020a170421050105010603050c0403 76
    0x1904c80199110145141c0034030144c04140c1e859080159549400b401000d50810003940441d890f4a4001240441011800028401951400200400f40c114914400d030405c006012020181d500e02000e10b12844c0395503800501201d0f0441c0c001d191050036100c031805400104107040c040399204c8902811340b0b9417003a0104030360721503107012a03070b00a0f0704011078801e40015840ca00c0710546008003050b41039008403610140c0b1803405054020b260f92003a0300045241c100004c01c010704210200a0707020340220000101c80d814034012101850031406003c1c061542031940c40110324010100352000d010340741c010515807070a5030418074284418065041c0340221010044100242c0034126000780501a28486440209602c080d1100c2c446100d02c2130741604181d81c0103199841260310038815a031650041811172010703103961030400142c40d0960041d1904100101c0c0d01c02d030111f42000300e060400e01d04205d039200360a2041c00c549040c0c000c1c0c020142050b06106204041000351002e0341d400c0343d41d002 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 110166942 1250 110165692 110165707
    0xe310b0307210b060a050d0320030c210a0813080f0d0b0108090c010e06070f0c0e041205030624070204110309010b06040305060c070c081c090504091502 67
    0xe103031003403a40c8019401581d560340354419004070000360402c1445079040003150b84a41d82007220340b150030f018440c0c001421540318000300340b2501462001604c442c660442c0207825000c02c5d4119880000c0d50640340d4414407400910320410030040c90001d4544440c01c1c01d00c060b8403001004194081c0280050601c0c0d251103e090111200c103c8042c09241803003207560340007078803014000d0321000d0300d0640450a500005207400b00b0114010114a8050350381d405619a00010808160070014041d00d02c0001e01507841c001890ba0709404020b400c200320041500d10701440c000201700081120041002402e03c1030203216168186604e0071f2001403084a0b21580e00c0520440d801e0189840207540281888901462448518015400341c4807420003030107003440e884240300940c403c0d0300c4024401da01090015840040720805000c409100d020150520780e5508001440c010411070150320f003010141c08001e4054110340c0450003810b05a50078800548580c88186504500340a800880e50300010401e = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 110168192 1250 110166942 110166949
    0x81b0d0215130e060103050903090102070e101d01090b0d05070302151207030504050f01180602090a1502010c0f0f080f070504090603080d050603120409020c0703120e310b 75
    0x59010035803450300004942c3d510040e1483c00e0301e0030b4810720301080c0340c04040350303c084021040700c040c0c0350180c00505e40e503440c24000301081c0100502186000d100d0b000302003100c0461001c8034150070603007014900623506112855044404c0002c00070300c40c05d41008044006400854128101ca0301220a41c10080240700e0b00c224521501344a042c0401c0d080c0c0c02c014070150550301c840e0081d03000c3c2003151085280d141406080f83d0600c14501c8428041c106000000b0f8102c0c1c000b0104c440c0050075003090f0700e54a041c1221410400712141d000350f51248801044581d201000f00c800070328a14080916244a034000380c241c3c42d0140a610070300c100e007c0003c101c42c1c0038008403002030210041c10400182e40c1c1c01c0c841c105802c850008402d850030103006c954607250020300400103071004890706280a1421200c00e00035881012021410300410740e000003c21480e000f42c0c83c4184094075035000c200c01040801c1700c086034250300720005600c603044030040030a1521901400340e070441000544144281c001 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 110169442 1250 110168192 110168197
    0xb0a05041a040302150609010b0d0e1e10050a050115110106031403040602070e01260c130b040b0301090803060d06110a090f0b1e030a02070f0c081b0d0215 68
    0x1e01e41c03804888801d110030036600045044490103400b8120505490f00030400208101c20301c0740e02c91a01050022610740006544030082076007414040360585252400141040140a0701c80c00958001c0f0300254001f44460090680c40049143d0400c001c3d070503c280c1c0f2402c031042c1e00a8104001e02030f007410382412000d5016202441c1c01c10445c03665a50903c00d0309070f40c4e0b4418010540140a07000e0000780b07141100141e181a00d00c811480c44040340c600f0544c0c0b80e85aa1442c2d507030a00d104110601025403203810240c0c440841489005c40c04540800600056410b8440f50a020b80e00d8158800b020800e02025680c100c5070894546420954a0818a01a007101c000c0381c08500d10001d074440c0c2c015001210402100c015200b0b084000e80c0d5a5070000490080074a4120001000001c41d04054442c8000390f40c0502081001801d010f516140c0c0503540900c024211060b10119006010b00501000003180e52024000c0b81240d49024002040e2503c1001c1c00c0280280c0c98034100420a11400f0306 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 110170692 1250 110169442 110169473
    0x90f060905011a060403050a03260106050301030c1d150406030506010b07260904020304240c11070b18010e0909030901030c0c471b070b0a0504 63
    0x10600c248200350a20038000c3c00c050710380940079104140314156030304128054400b12a04003020702000c00d81c41e1801e541c0c10700300d08411480c1004100d103121400f0411400140030340b2040da249900e960462030325101c0004150415503500d1910301d030644012182c0311007103510030800382c407040d8a5401c241c0440c014007295000141035008100000c50500845130140580c03d0149a01c410301000840c0d031400103400100c0008003a450420042503136040175001075030040d124a1202c040068170540c241c402d44031001c1016030441e2590309401c92694004d601c03080101004c409803105524101070703c00507104010030388408013100414515168003c3c6102d40d21807001038011500d52030200e50080d01c1780d00107100ca90101c1e15280b117401c00c03680b1900f40701d90210391103041140b04402484500c1b51008603280c01040100d0842c00e0442a801d00081d104902c2107040440b004605240f40d46502c0030954200f030940311082400030038007090001c40e400303070071090800c00003034240c0311424403a650365807688 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 110171942 1250 110170692 110170703
    0xf060c040e0a0e014502010203070b060109050a06050a0f051602010e042c3c011d0318061303080a050d090812090a1119050901030b1f0b0706090f 64
    0x245045a02201c01c0e000c05003140d0003442001d20088000300075030003585d00daa0107801640280546c6000800000b00c00d900a041410200490341c4d80751300243c1c4040e1181c00c10320020303401251710103010740c20203c0d01c400c0011070b082040c100104d04e20034a4407101030400190410002d0cd0425500f030f295075000c0002c0031240d0040c0101030140369a03202c2400c0d440c0c0f44000d458421002d03210070401c1140c188902c6800001e03001180c1d007071010f809860000e25881103019a541c1ea040720400314a60900c0306201d00542c02c051905c82800411a0a84038451000c00740912000c100a0344010070384e0b450b5034160b950010040340c45125a07070044500b4091800e418140d20700e40300700c803401d209440f0050940001900c01c0c1c11020f0381c450100a4079441911402040c105100348404018a4074002041d03600034083c91480045683e9000988684400c1e442501c8460344107007480212038044143e081c0700c1700c02c0b42d401102076103009100d034a14031406001810442d0307503d90310320400960301c50000280d50440d = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 110173192 1250 110171942 110171981
    0x3070809030115030519060905060f06100e010e130e0a050d030b031b12070b04092901120e030d02030a06030b0601050a02071406090d0501050a0c260711030304050f060c040e0a0e01 79
    0xa915405807200243d400910500e00337803001824842c8264144042d1400694404040c2c443c1c0d0380502004500b140e1929070300c240c90b1000d0f9040700004100081e00709014030010f0840780d58914015084400821806000350040c6e950141480d41e1030303405c100c0b03002d025200e10403005400e4103a2420b1060540210540d00b100081c001303a201c400340c200421041001d4540b1910100798280c00a881d01003000450103e41119404814410258000c0ba41030400105403441c00800c1600c140413a4800c5035004801542c41001340140030001c401e031903111200b801e0045c81e12a444074065903884a42c415180b4a48400002c0402529501e00b501c0d01d4601c0034007006102007040c07401c2c1c1d018020459442400c146480d075a0902a03200b036450b04005002010f002058a2004516080c074000041a035010b00a03204c50329450550104000c510a90048000e001861068001541800300c0a820402203480601c824030213083c0344213200e604100c4103840000c1c009003840c0201d000d003109456102104c00301 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 110174442 1250 110173192 110173201
    0x8250e040b010305060a0209030c0112020d0f0f060603060503061501020106180903020d09051c0c03020d0b150d110d02031002130501020609070e13060b030307080903011503051906090506 82
    0xaa0700482c1a00d1003042034920580d1100300d42c0c0c04078050b6100c61603259210b03444018080d4015141e040466140100c0980f40607641c04c100810383c0c0400d08a00e0003a030703650301605517040c807510400028158616060140d149050f000030b0751403001411681d4800f005626115081e07000f544904000d000c030183c801900310301503403900010880814158054001c08095900c0e8074810101c100130f44030002c1c01c000c107640b14121107010b82e5207080c4045581c07540c290404070150b904c0110f11941caa101c1c03000340b032061400e0040c40c48107885540b4440e010300456484000050f40c0c2a00d4041942019202100304c0050390001a141101801031205162301c00140689055081000d40d4160b50b000e8080320b42607142c2c100705c16075074044d5204012000140c400466280302d030106c0d00f0103070349000d99004182c1d180000002410340d4450a011100c58000140001c0d503401c0c02c0c01000038030071030191914041403664031500c0d1602551081d210061044546080420005078080360f001d50300841124600d160 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 110175692 1250 110174442 110174453
    0xd2c09090a020a12050c100206161106181c090306020d020d110901020c010c0c17070911090406050d050606120a0609060603020306090a0305040e0705040504090c0905010f08250e04 79
    0x398440240c0d101c2c0141c41c201b1501c2d0900c0d5004003010150341e40100140e90f2011041c00311568807170601000c00100c00e0345000f25040c10481c00e40a80060f151406802c50070a000340c0c90b101c040c400d0401000c11904e680d00d000c030f0700400b941048a400c108096039602111902030000d105040c000c2c44424500005020355031850b4000d04004103080e000c0b01c0100389282c0040d5800214800c006088410020050064a00c01c403081c1201c6680141243c40d0039484a1003101902e04030001c443c0d00c14000310304c60500d86810301461004000960704c446a201080e00e60584402000309007e00868822540c2061071100b0060508100e40246040294104520b844400751040744000d034030078481ca602140301c081000c02d83d000010b030300d5110545414500711001341c4900005081b0800e1201c01d100004ea107850b2070094000c018810742034000401d04210105048030381c180c022a42d0608510000d0041307030381c0041c10084641010815008040340c9220401c0c5180d59a00300200c800080c1051004122 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 110176942 1250 110175692 110175719
    0xb0d0b04210807050a2003070b04111c0609061b0f03150303021e0705060f03010305280f020a030204050a0f060b0a09061404150f0f0c0b0f041703090d2c09090a020a 72
    0x42c407a8500c403802884850030480d00300c800040903460107202102040006437681e01a0040354820030012400811043e0001e00c224210030380308011500801000305220303410311801e907500000314040c407045415610029900e10b499460390500901c08400300180d00d10400504009050043c180d5644441d0314640100c00c2e0030030310003194544150460102841c07103100d581840f140c4a17400c403440c036140c0d40d122094086400307501a40c014218410110140c1c8450003014407401c00446d0100302c00540003903400887d00d25034845030785800b040c031580c0c5070182d010181e4021240c003860007080100d4094001d2415201d107038019083c49964048410744550410340c00d00d02c14452703482e528030743f660f0560b050701d141c6049ea00090101c505000052103018031040d0140d00940540c0d00c40d1005c3e0b10300401ca000f99481074070300c020b0381d0b4410079080003032a9010001c0c0d030111125119403030f1107802170140c4c03a80c1c1b1105003003d1889446a100080c0c3d012404115541c02075400034904051143e032141c0109060 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 110178192 1250 110176942 110176951
    0xc020706090902030c030402150721021b0102120c010204230a0605090d0308070c0b010602010e0f01141503160f0302090a050f0402040b0d0b04210807050a2003070b 72
    0x103042001c0090070080c90300c01d0724410106010442e01d5943c0f83e03803c02802c4100d4000301807184000344950f002080c600e0002c1100040c01c800011443ca003174034006482d001c1d4100001c0036100b0586804500c0d80d07808981c1c2c0340c40843c210580d580742c6964101302030190040b074021601c030040c0307890300c06508401c0e001c040c28400070680d19144025203442c0121514428002c10b242c1110110001d540024425410217611030461700d407468901044e030340c0e4100030302800e910000060b0f454203081c00c0e1100d020b1040d5800070102100030050403402004102510700d00510115540002e81800e025a840a00c1011501d02a44045019450301d414100600d0203481c04140d0040448400090b2188240c0c03150500500803181030a9803a501d503400c10000e03000000d100381c0c0001c20b00c101d8000054601803514000e9101e0700115001140b040e074034503000086000c039078040100d41c01c14080e1540d040350894a81243c140307040600501000300211600320b00c9410410180700000340e18050040410300103000c1d = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 110179442 1250 110178192 110178197
    0x209090a1725050309060702150c0d1e0909050403020718050106120b0d02150906180f01050702211204080f010b0306270f0102040e04031115010e0709090c020706 71
    0x8441d0b003040107094850b1040e20051443d80b0030030026009180036009410018401000140d503025054a00300035508882141442d40d400b03107a030400a00d4200c0243c2035001c0201001582e54610290f00822030b40c5940f080c0e0070515901c2000c41c05241c403d00400001d090203020703c10042110f0b4100c080200380c24451100014207800400e01c220340c0d203002d03020340c0610050581480010319004c20dd81c415100e800c0001d494405c000c1200d25440e600301070042d5040440360003003607140b01024008040590a01281004010025070b4016901c2c1d010300c0c0c40c200c80030344402404500c44030341c1f1440d24460b20342c0103101c43d102080024080a0001c2d00b1801e4804050090040301000000e06503501420364030034000310f0400d1404841c0000480c1c43e084504c0640003251001020b8107081801c80c1d10940044c0e0242070440100418550011041c050410b900c0e0020b00300068130100c0041c0400381030003000030501515002c107981620500c0707168081d0482410410142d0308040d0007a50320142032164402 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 110180692 1250 110179442 110179477
    0x90a112206020712030827030a14040308070b04030c020319021906090501050a050403020a03050c09090309030307020904030e0a0b0d0e03030f04111206010f1d130209090a17 76
    0x4100b880428628200c2d04456280725040b8042c1ea000d41d101c2c0d20041108000340c042d00308201c2c25100505400e60302c070084102669030342c0d03100c100041107020341c0c40da0144407010401040000503425001c03900300c035801c500011aa0307140d5103400c603100404148041e6040c03042c0c0010000200c00c1c4210700307407214402c84101803031451203005540140050300c14207011a0380450300708083d50040700200101009860110300c0c0980ba036000518a0800d42c001f13848aa00c0225601202e0a020b200c503904800200c00950400002c400020b680340305883c40203000d40003501c081810107008071030144900100800c1ea2072001e4079120002c000ba0404030001c04454106110019140320101c1103e0141e05a2203441d0003e5980b0b403034016041180c14039254210004480011000f5810320060740680300303c0485002140c0b5000070741c0f5841d283c4050202e00055008140f003500074580145a03445541658003004541e91030500d203061024840010300081c1d00710118090940d2401c0040c0800180b1040154 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 110181942 1250 110180692 110180699
    0xd0516030506030a0309050922050309030105010b0f04050d111807021905071421010204092901030b120d2604120c0c0b04091401140f090a1122 63
    0x140c1c0e0301314018002d07001c1243e044d801c3c00242000c0c15015440240c07030b101c50104200c0d10a10031039402140c0e00c2922230390404600c0b82414642801101c2c018400840d50700e06010070300e2100c11240c451881452701c00c8403108803000c108440e0400d404c0000c20010b041000d400c6080403a0b002002d81111818010300800112418441809007800592a000001802440e003001c01d1568a40700b03807a032181e070241c1c071581c601d03840c2c041409039031441042174000544c49600d020841c409945035000e41b00c0c1e0040035451803001d602d810303689a0304003032000d10b00400d2000d8100c020809001c0280e80052590045001ca04d450542111141c0c4c00b1110750b0740e10380c3c0031601a02600724055006c2d01c0080614506010016001d031240703400c1a80d0a0283e54112070066840c49032212a6205900500c50f494840f0f14900081512103581c5006040602500c0790590188001615051216411510624040c0d01081c0240015840100710005903194207aa40c0751210508000c003028501243c1c0c281004900070 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 110183192 1250 110181942 110181949
    0x2040e0a0f02040f030f02061b15010506031504020d0905010c05040f0503030c0a1217070c020315070504090207060e03070f021c050c091509010605030108010c0801080c01080603030d0516030506 85
    0x310b007111130280304100700c0b80c2141c2e81c0031000c800c9040d050768460800d00118660f200d659282c030201c0040c89008102580354500b045881d600160b120314896001402008010000c6100e0003c448004640c010303903505001052100904240101a0856180004c000105504070700204103490250108484807591107003010340e03c0c440c1000507041a0045441d250024594821036680003803e400c04c29030150300654820150355040b941240080d000d041480194102031204150100a101101c0715500d0700c03220240c4948601e01c035021883d54002851000c2c40003940c404a0180c03000c0c000c1d03942d03d08041c00d1040c40080c040300140c3c49a01400b5142d40700710201d0608901032940000a8000142d801e030800c01079000041c2440d01018075003182e100c8507903c80803e036019140688030a070f141d50401c0c0c0d01c142141d2402d40c010040c8500000140500ca03800900c0d6410400246810350195680c0c00c003090440c041c1130303a441036060602e41405500051070341c02e542c2c4900c039940c003080584d0380c801c01c1 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 110184442 1250 110183192 110183197
    0xf102f09040617070614040e0c0d0c180303110708010f051f031505060a08031b0f07061e050912030a021212040f050705060c0105010e070503010605030c0d0f02040e0a0f02 75
    0x1c0342200d9105032010840780d4010080c15015102c00d0714094200303941c0d2344241c00b18410485001c5210391001851812120302c9100790912103800e440c7c264180105802c810680304220300002d01800341850012201c802c08101c104090258803009000000081c640500640025207001d903468505400c0842ca040d4001c070400c0860f40c21000b0000301d60424400b1100511010303110a0b007014208802044e1040100b0050455140b0303200c00d203e954076034108040c103210707500c07a5031016074018400401685a2182e95450340750f0341c1d40d04881c00501512004c3d84c8611a507500726810803890038440c5000213010020300b58180b01e81c0c00b80c40174400c00c080200d4084c0f01d031040c250003229100000c280400c1c0baa0400c00155032081c0300f215080380e21000042c80c580c10280094005a45510051283c004140324035604040a42865810355040000c003900c82e000080035001103d0012500c1801e0900300d4101039030403040c084046580b00c1c0c4440c2941400602111029035442c10f1180079001241c40740308 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 110185692 1250 110184442 110184479
    0x2030c01020d09150201090204050f0402011103040f060509030c10020f150c04090c0c0c0b0d0b0402160803090c100804110a03021509010c060501090912020f102f090406 74
    0x140c10603503504113a075401e112520018200215965031240030010f8403680300c1e2a0046071260040f03a2245803e100041480e503601241c410603410a1104012605034906c07181c094032803a003000c589400400c400310349840040c69259601014070f00c100308807950041140c035010209101610710802d0007041c1d0f090100d0003030780d07524128081004100020a130341e42c44100d0707100e1300b480c02400d441c40f60303101c280040c201904031658081c00042d480658501d180308002e650801600c040d403c000b04d41ca001c40c80c02f0210324026002110000c009096480c041c00701c0c0358410401424141485880200140361000845003100c000808012102d1180351281220080329401408180d113010480d03031032680c54029400f2181440301e50070903200002ca06000d42c5020340b5a16500190549241c1000c42e20355200c07511800a540201140b480911000b140c03c17142c109041da008244500600103940312041c9941c42d2407045030500412840940c2111300801d800785e411102130040329100e26042c1300c0509401c0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 110186942 1250 110185692 110185697
    0x10303090302061c060905010f051801032402070501090b0109150302041a0a090c020606190308091203030405010e011b020a12020f07030804031e11040f0216050a02030c01020d 77
    0x40070001440c0900007001a01c402000c00346030001d65014140c16640780c0d07000f60050703a840b031005102c1e1840c00d060600051800306ca030002c4412440d5200128010180009000a20b00c070340080400210720034910704550b003520f011580c50307189060403402410205011104001802c0000410f283c00303000724218003180901285c1401d24542c20000106074a41da00e1140c00a200b01c003506907560019440010404641c2c08600e410400c100241001d034010326085c451100300003001c00070f0f94546020801c1c7c903804010250340d54031083c0020038504012182c21400d120005c01c00040100640161800c2c00305c2000a0100c010120040e10030b0001c0103500500607840b940702000410194001514010003031b0043c0e0304c403103421020302e6003085910703082501d820100140401c208168034000c1d0603070003010850000020429503441310340c54051242c0c03c1c41541c6428452400c1d0b003080e4101c512070b080c41d80e5201c1141015280240e01c178884440f00741c0c42802046030282e415400441d003a0200c14095 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 110188192 1250 110186942 110186957
    0x60e01090e0c040c02011b020703050607090807060f0203040306091a01060905030d051e03070206070e15220504020d06050f040b030c010c05030c0102030708011707081218040f060501080906010303 86
    0x250510000b01246a044d0702107640b5900000c50803060300030b01115a00d641c0c0c2c080c014440c2103041041c03030000098201c80c1082201030082003403400c0412180140e8441349401c9105c2e840c209002c918500071500064001d0749032070710040c00c01c0195004400000c0d400c080070101c1e6030782c800b015100381c0d407140b08864154005c4a035840d0880e1190000f003805900b60407901805000341c200d202840d420485240000d43d104800707102c50319400064807110381c0c0c0d00703c81413002000d840084008900a043c041d01a040f004244072086a44515009016080142086403074895508444c0050401441041e000d0722101090300d05604107030250810440000d401402d00140c0440111140e411085d0240c1e500c3c003080c0400508108280010740c001c8100c0e030b4075003203554108040f8020550240c5480c030707507560002c40100306030040407488820f099011484641c03a407040184141c003030307403d0008141e88146011040c0c03416401c10350003042030b41c0b42aa5454415a12a01010764500083c0009004a0f192 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 110189442 1250 110188192 110188213
    0x40303121a0d0204060b040803070201090e0402010c020d03020114190e15040b040804120f0210050313030509030a02180702010c08012304180501050f070306031a09030403080a03060e01090e 83
    0x240c01140b8a151024200090059903400c2110b03a5400c1783d0055803154100050220a66a01c0039000300034050030030031011141801c0d070001e844200e000c00000c0c01030300d00700400c00a1500079881a450214840030100c1c1c14a01002a03040c0d01e00d0b0010510740d400e16007503ca01c04110700044440d8684d07131001010189845540700c261031490000c004640c280e10811000c03c0850125654200040c403801e20022506070500c10440384008000d41c840400c070b400c1c0104203203012a115403010064050900c141c0d21a0300c1c80200341050303d10513010350400052040b0450f0300900c940e46611030541075008110640c03011344111111f4400380302d100c4510072022a00c07840010400c0340c072005040000c100203072030101001142c88104144109481d281d548400300040300c0a0b0010741ca81c040b015243c100070041c1940c0e03c4d510022200e0250381c10580c0180001070ba100c50030801c8801854110f08041d0701c510a0b4132004026000f240180300e145501900006130861060044104100c0306070041c0030354034203 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 110190692 1250 110189442 110189449
    0x80601050907110159070b0409060f1d06211e010b0405092509050405010e0714031018020303040803040f0623070606030b01090b09060303030609010e04030215010902040303121a 78
    0x45c10701000305400f40b1503002410314229001440102404603000c540306240c660a4440d8155a6205400445100407001c0c01c030b160058130f59034001812aa2082c0040301c0c43e40b80c166144801c002c541080c464114150040d0100c0c040015038000c0c00750003401055804418801524000c3e601c04029920031001c0c5d602c6541007080c4600d18400710000034018554401007081500c6043c0c07015034a5075511403144800550500a1201424120700490800e2040001007940c4031300041c01c1c04071040d994003021103801c0c1c0a408081c034241d00182142d4449444001b1581c480c0d015202c0c00708001c000c2d9400203800c50040352401c0d00d4003905d61115201c01c02020041e84107a100090440d442e0741c1d681c07400300c00298021942800b074000c001000801c44400310078080d003604003800300c074801c0d0b00601c20841c0c540da07480a442c1c15149103c000d01450745039450280c0ca050500740f2480100007205001048003122079024000f241d001b81d4800a1024802d20f6080403140108400151400001400c005604 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 110191942 1250 110190692 110190851
    0x3010e071404060306061106060906060901030f020c0303160801051503060d062a09050f0f010c050a03020a0b0109020c06060402030606040314030d0e0303010806010509071101 77
    0x580900303110038940c40050108886038803d80203240481d6942d1030510180703a00c6840005040c54a0000700424182a40080c0b008100184001d21072400003c0b020080d91084e0011810b100001000395126030110030b84913221b030800c490004100500c10b48045a40c1e101c0c006803030498002409640d058ac003c00b086d200d1a60000346003903008000c90b0515030024a00d80304141501503199001d100444460404031011407400d900e200c2002000042404075a41d040406440c0b600100d55210074452520010381c0d031904841c4024040e40200040c032001e0503004101c2d1000940b044258502c075a0722a84c4e020304a0091500f129402c3d445580029250300f4154000d542000008000908055480d80c5488804c1a00e4080c542c0a03080422400c42500c05402651800d828540256040d58107261178a80d440d2414418644a4000e10001c14100d0f8010300007020050302c4000280002e14010f004a042c1901035150260001c4880c406903402c0f40540c0e145c4800d0000d03a041c0c15006640d00032075a89440d = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 110193192 1250 110191942 110191951
    0x120307030503190902091f060e03031b071802070512120403081f090e01060503010c1e031104090902030c0102030a0912080433030b13020c1c030b12070b03010e 70
    0x181c0d550842c0720f026070b071070a2540b0721610801c0d0305d00740c1780c2802e1201d007c060103540c6d111f40d091194102800400740d60102c181c0300202c00f840c9001803805400f125942c54a403951780040b54191442d100d01d0081ca0903a0010208035001e5800c0326260001640e0b81c0c070301c0d031188641d007000c030000103808100003e120300c0038588c010120039002004080d1403410a48200c0060748900a4290384603841d14100c6001c0c01000e0052204500801041e6a500b40c068144c0c1407007038110544020509003004a1400f90f84004200104960219180c80d160158600109881442a8800e03c07a0024008003580300004550441c81e03e6030f10a4100c901e440d182403402402c0040c00c44d50309006000c0841e01051180072041c03070020507042c054521030070082c41d00d402c01d044403000007010f082000103c0e450f100c901c4c4054070036045200042e0303030790044004541031488481c40000d110740c61041c0e00d0320441d41508601441c40c01269910316900070303008100d6a85085d4440c0344001a0b060004020300c0184840c0140e00 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 110194442 1250 110193192 110193241
    0x308011503060e0903040305060c090d03050f0d02310b090f061c050403110f0c0d03050c010c02061f0e0c0a0207030c061806050c0601090e0a0f060b120307030503 71
    0x20143c4443c2c0080302d1440855010380310780e0001c5800c00c107001040052a400950b900c072003918241854000c1801082001c0c400b500b4448001010250741909104503113402074400c00c00c6480f41e4007081181101e140e4898585083c80c10003090955036041c100c500d070215904807100320b20f445150824003114402c20f840d03041c1e1109007488a0310002c1d0014148c802041401e02c0001a907141c5440c000c0d20004064000032804d03444000102e2803142d0010703002c068031404544a081000003803904441c1d501c2058426a000e5092101041040d0380000740305002c1c0d0040308410f20104180c60307090707021800034440c0101d0481c1000109036491110b80042000c401c151050b207142607101d4840741680a000d6101d800010984100a2a00f00041004c103026281c0e62900c00d223022090080701c1ea5900c0103008440340143d450311500e41d110402c01c503038041d40781d1107080f00404007180c0c14800000e005544440b4015001f030720400c002d00b0380110032200819071540310300d401c1d0b46500360412403055032118804031 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 110195692 1250 110194442 110194451
    0x16080603030c3706020304020307060212030f100b13060909090305040509100806040b0f07030506030604110604090e061b0705071403010b040f0207020f0f0a1a0d1805070807030308011503 82
    0x140c540c0c10100c40f4503100c1c02481d0150b0380381824410b044c640201540000f046411401001e040008020101c0c5e41001c1c5807100c01f80d84d51100c1c0103a4800d94125880417030351900008480d440c096195020404490090f210a4403040d521300c01c800907600003c8004001980c2000300344120b10f000c3d00902d400090840c0318001107901c03042414540300c07043d02c0684103803409038104180c03405064022a40b01c0ca4600e004c1c012030030003c000c0b940e03039080908020b1100c12040c50310b44080c0c0b01c80341600e00400003064140042c86000b240641c41e0301081c0e80242d400600e8280302e9188020307480c200c41200c0c7d0700100810b0002e2400e0340302d000d4401d420800030b034955240d100341d10781a619800380d40c1029a09100041c0da45d0468030411858841c2496600d0040041501401550f5070302007051003250000c900f4000e011409488440a501c940b032901c50f21140361503007803032035145600e204003801d500c9241201e0407503855044040c1c0d00c000c3c030b20000b0f000520000041c84180d00400358400201503a00700450b = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 110196942 1250 110195692 110195773
    0xa050f0313050f0a0501050112020d0303090203010902030102031006021c020d050304060624081608060609061e04080615060a0e01020c0a060e030c01050412020f031516080603030c 79
    0x5041940c070038400e5220f40d10140024017480f400b071107420f004000c540ba20945141c07103075000c0350300440c20081c050103042e55800e4560554900303404c82a40340e0f90080085590345448091011204024003880d80144141d2080400d00c003042506d0148000d2a07400a0603020301c2503800700c1e042c2d80020300c11244140c07159030001c0d84610380c5403d180c0302c28440d00405100c41203103000600074000100a01841d03210100d000c11007a400c13800980d0003d100399511b0740d9070100800403072464411402561912264804111219802100504103454a807816203201c5e8603400c684042c006a10340401d03a10590400c40c00642502a1181042039481801900d24020300d80e0b002500b030806540c000000b191042c19034088514060003d05440002400d0050400d8180101c2603440000d041000780201100c50307600c0345641c3c0400118105c0c0e28400903034070992400060748100e012043d242032011074880c1011595624001c0244d91081e0030060041c1140354007070a10000721114482c1e49080101e1680000307 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 110198192 1250 110196942 110196953
    0x1804020d080310210b0c13080303011508070518010c03170f0a0b010c110409060608030d1415030c1531080a08160206090409030c03080106050a050f0313 67
    0x1144078400310348151101d10300d0079a5040560402c0b50200c40300c90182c41c4d81070001440c0980050300b041e101c2480e1610703070307015280c2840890602d40107440c15110101c00003c0300340785402c0e0b6072012045503a4802054440000c00d907000e006541c1c00d03112080d01c20000c070440b0751140301440b04280c068980032070241c0903203620f800615070685440d1a0401d00d04104800172606010743d088501d8281380000c400022500e0303900c1071101066040d88200d0303c030741003c0c1c00d0040a030041c10183c6000b2044e0780d0f54143c2290000018494400b05001c400e61300c90015440007078056040c010180040c010b0400715602c4400c01c081c01c04001060303810410207000e1400e00c20312114109101c00d041c41c10800811071140301981e04444554030242c403a6001905580000306408182d452104611142c8000d0300494030000d0000d008009046800a142c103212800303041e0f1000c00405500d009885441c150390f00c50404449a105044000c2d0114000b04034030804401840b0007140e000040400c004540768140c7e854 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 110199442 1250 110198192 110198197
    0xf070804320c01080108070501080a1b0221040f030b07030f111209010e0c01121811180106080705090102161707090c0c020607021908030a0905010206061804020d08 72
    0xc103041c403a0000801e10805001c0080c031a03488000d0034416000e40c5409202a9581450300440d4104100d410108041d8942ca40200300700c1000c101d00040d5a040d40840255600842e00d1055400042c02c480310300c960201004a4064884148025502e1810360f1141e6842080c003806240c2019501d0840c409120554800c140000035502240e030b5498004900d10148404043c0c81c07500c0c0e42e407405c1c1c8214206800012106901d11081c00c0220304012031458100c01000d06081e039890810808408004129504080e801001e400700c410300c1103541c400103c1e0914030710900417034002c508107802140289000d100580480d140510442e8a2002c2048048030301c800d8980c003018010f1600742c0c504a05010900c003190150544c10810011100c00b507000500c40c14203448064005c28000400100f0340d1500e2106d401d251807a1707030440200b99a220202a52584038851010004156501c040345540c80802d925029110081500e5904001200349000502015204a0b4845140c1c58030000040b10b8101 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 110200692 1250 110199442 110199503
    0x9110c01110c0c01032705031201060905014a060f090406050907020a021302040806090c01020613020a180e06040507031b05011d040f0e010605030d080f070804 70
    0x21580d840b01045100381e494075002c00805810b05041c01a8000d00558403000c0300c0071000055400c03030301001789041c6281148118105149040b050500224407280c000e0050740490b4020b90b0380e01c440343e14450018484603402016001c2602c008400140522451074810702200c8211520000880100002a0740c590024003044e01c80480802d1294030751810b4454030000b000207640700282171410003002501d440301040001d1240c000700c982032040c07200d43d60590b405049540211142d909000303070600c1da10040084d502c1c1c01889420001840d10346030b10410f503052940a400b08031002e091008900c181c600d0070101655180d9034007480910b10f80c0401c0218091801000603004513401c50074944040403100302c03210242d00c885041000940d074400308101e040e10001c041c40743c1208030341c0300045c00307481c59203110500319042c104a41e00c0301506501c0b120071207200700c084901c0310b0000c131350540385940101c0e80c01c88003206600005030380c6405400c02c9039109100341080148014441c2022100700000e41 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 110201942 1250 110200692 110200721
    0x20c06070b04061b080a09110418021005191103070f0b100b0405090406091b1509120201091203050d0f050403110c090a15030f060203060a1d0109110c01 67
    0x42c001400f0301489042d1074100d420400d2203410203610009408110b01400002d61130703aaa4000d0803c1c400780c0451254000401031080c851075111140e01d02d0800b510001c02d034450f22544140c3d501d528003e0301100c1c41d0000b50100102c41b503054100985482442d44105c0082c0c0c08108a131300001500d03440c0c001f050030b21981d8480752038244044800102c4980b80c00182004204000910813030b901c00d042c040c1d11551020300403c2c031001d1480c001454461780c00c00f820030540703000d0001c1640c0c02d88014450f181d00850b52421200c07903448028090f2075070b031701030041e02044241400344080c3c90302d90f5020039807c0c001c5c1030651a000030304000e00102c03602129040d50540e40c0340180401c2692240f000e032040700880004108400101c0e0004d0f0800c54050242c0e00c0e229902c09102c441103000440c04002181c008128000e0a501d9090540c080e6000b210b2840c4103104c90000400c081010382e0301d407281c0318000c900c2241241c0c20f00070850020b1040320b0724141e08100038448603601d04000d0203080005150007 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 110203192 1250 110201942 110201963
    0x204060504060f02010e060c090d06111c050f06040221040606050a09020717090d1704031b06020a0303020d1b020709061202030c040b010521010503060a02040b19020c0607 75
    0x2142c010115080c0180074421a4100300c20b001d40758a0001d020783d000340390304031120381c3c9601e02000a5083c0010300720080025007400d065011250054015100c3c20080744c0b0410903849101c0c1045045510444842401d10800000b107150760610b60701030441d46490010b00c0340304207411700300143ea408084404883c0703192a80414001d80c00c108084000030b01081c0010750806070b844c1c0d1551020050312580390914040030031254403942c1d910403000401900003084140b940d40502c002c0807594028081900d040201c140fa031194441705001c034904841c5140c1c0545000135141e5000c5001c0d607c407000b915a10303620b99107440740b1034081a810440c2038015070014080c0b141340c07882d1b2000b40c0300351368491424040003c0c48100035840125007562040703400c176000606a9010300050741c140c0a0641d00e00000a60701e11800312038000403d200e41640c4080b003c5442c590b031100a0103042e0310840c0560031900e4000d00414800d00142d0305a01c1da00a500d0050741e850b8a46100860410b030000d010549040700300 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 110204442 1250 110203192 110203199
    0x40203070e0f060d0302031606060305070b0a1e020114010602010c030f020c070303050906040b0f0a0219080a030c09091a01031a15070f0206030c03041e021c0f060204060504 76
    0x2003000310010a400d10039032046240000503007041c190024011400b91140548500426100b40b080720a0742c801955410040c00746402c1c50300c010031983c0801c071134510803840c0100e5441d000800707480c007600c0c155591071000001c0e00e0f1843c00441d584184103040d50b4071402c071510140d84079050103010745115400002c60546c41d820050541e0741c070803403c2c40414410031000a0b5142d01150b130a0a076501810116984c218000c0460150702c00c41c4d0204010700004540c03095070035000c00091000441c00da0849244004000b101400144064001007000908010300140c06000380c1102d8103044013818080b01140c0d803040d40e03e0581d902039190f41014601c03048044480e42e0076100340f000c0300c65442c28001c211480c61010941c40d10f462060551a404041406400c02403a03001070800c0b41c0d4054500c0b5141c0c10440d801240c4e90b002030300d0484e101ca0409000c1030585904003040000740781c0041003031511034501c41e128604d007401c03c60103480c080d03101c001c1140414103600090000304016591159101d14 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 110205692 1250 110204442 110204449
    0x4030c03080a03140c0405010507050c0607050109140c0105090409020409020904050106060f0504030c061103071a0a050105010507050d050a03020c03040e010f0509010e060621090a0606050a03021305090120030402 93
    0xe5956071014151415040c0f03c80480000701b640d00f0b41d4003c0c24902da82e11050b0401e140b0301030182490741e87c8542c0010785d100c10420190052022903101c2d1030390941c8040c480d40c0e41c68032050110202800600d01b071180000c140f815403c2180c0c69400075000040d03403002a00032403945402280d0907289030707446210401c0041c0e841040e841056102d494070718180703801c40c0d544096101c0c291180038100003011b4944507901c035090048036078140d40310207030541e803940b40c00d140002d401c4100c8007108080d2a00000003059401441100d0034981c0c49000f400c031611000c2025141c83e00282920010142e00313100308180864100010400b03000c0f48a00e001081d89402580c113903403811134120074041c04028004204130900f1201041e08454111002131305d40007245c440711400500a114030410800b500140482403202041824041c0c1c000c04c81480240c0c1c840303042c0440304142e0720000750803800031000c10010005551180d908459041d0000c204c04800c0724104481da003e00003c0003030181e0010501c0214035 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 110206942 1250 110205692 110205701
    0x90203010f1a0a0303172203080f0c03091e07172112280501060e010e0f03030d05060d060501080d02061005010e2404140f04020702030601170304030c03080a03 70
    0x41283d80c49621804c55030003d04c082903240030380504170b02c0c90000c12280c04405105030300308000040500b40032142030030020b0440105985001d0440c5845000c60300031072074a01201e05c01c8040c50001d0642c6580074026a01c014607000150021b4080d07400c2c007250541840c5210182c0d2a2202d005202c40100101a489828500560203281c1c030420004446148905c2c0c0d19a640f02d0000440306044400300395030001c0c0c941d031440305058400c0c13514001003540307900003295050740d134001e03a210496445042c05001ca490034a507051581944148180004490640c2049510900c060084225046607039101000e03a03000ba00300700303529040140000d084941c10001907a2250030351952400c2a0f20b41400030b014040c005031540c0c050341607282a40907d04080021000070744048668950311551544aa40704201e02d0001358880c603020200d61034603103001e009484000b90000c0250100d640380c01d00040d03601015030f00b1328095020500c03002011544031078003900154010070700f49903690010040142180d = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 110208192 1250 110206942 110206991
    0x80601180b0a03020c01150617070309060207120f0206090304090c02030403050304031a070e0a0603020c010e06010305071802030f010509060109180b04050a020325110a050304050a060f021f090203010f 88
    0x821801c0c400c0000c258401000d24144d0900c010841c0582c68080301140533081d000d80251a050000030310700c00b000f5070017201141411407981c88540c0e00103c1c02089882d140d0603185005598402c1c0000d0004e004264462041c42c10a4012640340590760360b030b07203400c54005500c1554800e41c640703000b40c0382d9940c9034030455100c103841c6841d642640300310780042d502c1c010307501820301010741c007088490a83c4003d520609020f861f4a040312910360f9a8500f00c5e940302100e01401440500a951a20310b40c1400d0007500c0c06960b400d0720b00300c4c05a003000c081c03211010004181904101c101240014000340ba100b001c141040c04540c0400d00d402c0d04010b10056600180210740004d10400c00c001050b10281c420390b2522181c0101d28003030621100c400c03145007a03c140700c40d08900910000c0d6040200000c0200112101a5007054815540384070507103950f0a8102d0301c0c1c003d80c111084203420111003a819020100d4007880000305110b464011900f11070341400b101e000c076540e03218109204c81c041c80b03590144 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 110209442 1250 110208192 110208221
    0x71e0509070504030303150506030907060908010c020613301e120906150f08010f020c1c2a020109050901050d02010305060a09020c0a03030501080d080601180b0a03020c01 75
    0x314200540c00070030a00c01c03484090300309030350b5a03000f000d1440d001500b4001828010101910390825034480c580b1a032544c4070b15000f1504640d00050012018000d4803400c01254000d00850f07a500c1d0109220440b10b581c0c00ca0741003040c07c1880c080038012103007101c01c01d035000c01c60000b41580752070081c0c80c036003c0d00e101086a46115207103100325540800003034208290001e010520605514141000d00007400c0d205070715402030300000c81c6007509c00c540d0370110fa64100003030241d4031001030000300f284900422206540c01000c07030300300541c00d100d02c40140543e080c80e1484801c010a1a58640e04c95204164110040c12a010009541e400f104500c050301c4100e58050481d4904030004425480d501780081c1850346850000b1072545c0e4854541c401800d40000c199954807003e8401da44940744140220042440c05001103401140069100b42c03890035902d031240035031110001950102401c00c0890031400340c5941c08030b80006070341c014201b42c0045e1389004d615803101400a5007903491044601d440c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 110210692 1250 110209442 110209459
    0x61215050705040f090e0a05030d0b0114030f040201050a1214010501080612030d0b060403170301030212030405090402010e03030904090c05040e010b131d06071d180601030209040905071e05 83
    0x409055200c1801290310f21707500000c02c0441c8a009a0804410b01d801074000d00010a0340070310100160030152800e402661003a81c0040760000403041c81c0004c0d24680103020044c400240194000e01c000c2c100a1a541856000840140d00d68030036110f5005100102103400401000b640d60003640c89a003007a000c440840007092419141503884c0201c1103003c145980300e680380c4006464410403a00a160052030381c0070302d030311905801c86040e03000707100072402100d1006403111070603004420764080e0340c230003403510204e916142c004440300e00240700c240ea41030100300002601c560f43c0d44640e41c09284174042400c032061602c01040101c60101c148055241d0400c00c10800a0740d91024410f05a080c2e4070340068400004555844002c101e4a0000303103500c070780828800c41540200038941c01c6800c003540307600d1480752407003840300004541c0325244251502001041c2c0310340c0203030041c1648440240001844554540f207246c682010390348241e0b0a078290016034111401d0f500000700c00317020240c440c0e10 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 110211942 1250 110210692 110210699
    0x20418020108070e06090a150206010f270608060a06090b060903060c0705012c07050604051c020316120501050708100b0d022a0f07051509030106121505070504 70
    0x82c03800e980104110100500055042c003a55141c0341034551040d0041d001d020195201c10100702c0412142200a0162180a000007862010381d601c0c901034414106048010110318420305440032000120000007e031500760100e800003081140c1803042c004080041060340c60039610400301c46028240034001c6504211544603034a000a1440e001981e01005a80d1920302e42000b9004110310b400c1c640212100c000b81002046840302d44a41818110042e00c0f41c10303070346104019941c880c61040f0783d003002d12504c240004444c0301d40e000a904d80041c050343c00c44a0030203c59800c0000079042514041340110903001400170920400b944400c003410302000c6030400d060501120101441410002800040c000c07054030119010b464a45120306020440180c0b100483c007000c04110b446042d25100e25400c00045110005043c01143c1002d0410001301c2200c003032440d800da1102066507019921414005030448222100e907013500c0c01281d216548103454441407084d02c40280c150000c0190a000c1030 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 110213192 1250 110211942 110211947
    0x6080c090f0301090b040506010e011d130501110a030f150308040b0705010f05070c0201180b0904020706021c0209030f010903020c13090215031602010608030d020f070b010f030204180201 82
    0x1640c8022085442101d1680d0010000c1c0c0581200d640062004800340f0a0104100300020064166011840b482180740e03200c58038800e0110108610b001060681c0010460881d0360803605890b05000d90000701d621103034122181001d90008441000003643c0d80210284c00e2005d100700c5021181c00150602e0711842e50f16440176501983c00ba0404220b800507452041000c254480007828000f45428031442c42c015102406001140100b40c0c041507081d04440320749503951000c9401e4403803501c0082d080c401590280300c02500003030000c440c2e140d403c12008400e102004460300d42513403070640142c1e0300d0f042142032504141e10006400881d0381810050300000e500458400e06041c1c0030340e48460b104a51500b0440900010398010b50020301c035414070300442261100075445400f0200f401240c04041c01381c100d01b21011803040c0245070b0410712150138804800d40043c481c440640118a04228240e01d508102800a80c00000003000100c01002141028024500a5501c81a02224000554001 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 110214442 1250 110213192 110213197
    0x601060818060403111009021525030201060303030c0806030607050a050d06090504051504031d0a03140c091b04150509150702030d03091e2d02091503030706020d0915021306080c 78
    0x19411008004140c40c4580d1040b1020328000262b80103d500c269099410003900030100c0e4041500028141030419240b240180c1d8100c0c040e801c090010519541e41010482d40b540020031200100a000c0140c51039285050040001800c4415000100e40c24140342c81841c0c4030307485036024058101c0710708100c00300744c00400b8018a80007804185001d80ea0700c00c00220390700000c1d0002442281c040f03502082541d00000c80c110401015110407515489a88030500305191404680240e68410003052004803034045000da0318584a050107810072200c9400100c0302ea8210300b0210700c8150114005041d85410041c01483c018203041c00c000100301602c035180c030300c1c041d08891a40300c401200d0101c104881300720300000000040c200c1c0c4c0c0c6030284e400c20160302c108030148140e00c01d00500e00464890309400034440440c1c01e00500071032507c4401c2c0d1b00e20001e1740203030945107185070f035030759200300856030f0a4540001015000b40040c0d44e04109080c3c41c00c10445600220104101441045660100f1204 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 110215692 1250 110214442 110214469
    0x10c180f15080901140c03040c0509010f170a39050f04150902160510050c03040f14161503060819060204030c15140309060106081806040311100902 65
    0xc022065944210819015001741004c0c04c035482e805408100d0b10ba01c110010314003c40c4120381c4c0c80060b030368400030400c1c20311007030007606079010441a0400040f940c1024040b202025107050b2105005240c44078641c09000d403c0d81c00e280c002c080100204010b05490745205840e00e05c201840d66400d000c04500c14602d020076060080707507182090800302c40ca01025800401c143d403010355a50014150350206044034410840d50b07441950081070300020903004043c41401495201e03030640d96a51079a41e1113003a100c47c03d5403000702d54541c41c1620f900a0042813440140441f00110307803440c100c116000c821880002004051030100140a1000042980d03010316900ca0048201c004d42030800304003c1c0b049920003072030703400d100d80006030b280b05506640703408200b103403aa6a0f044007040d0301c690b1544000c81e41e0034603507080380005001c55030064420b25086400c80c070b00c450000c0041c10000d0303d041c0b01501e090380840c0c200840d00035203050411040c0e800c205020001d102c5c030300d40780d808a4030352801d201 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 110216942 1250 110215692 110215697
    0x210031808030c0c2b02010e06040f0c08011a0a0603051923010306060501020607020607171b030906060f03030a120203130c0303081501030b131d010c180f15 69
    0x20401e180050360030b660040c0c030000141c440245026100450540690710203a132901c0100c24205c44150061003120202c070f1001000d400280d45565801d64445658001200c1c03900e81080085142d1340309201d44c4d41042484e11003d00344d0040d02d4104170001a642e0300207001c25040404010780392051000310103400c00320601c01306581c0900c04211020780901c0c1c5c1400d403111030400001050003195000002103170000c0c0c0a542c60340d11054000c0362201c0342141d0510108030165600c210907041d90000c0eaa21540000380103403801c5440b106062241c0c01a0703030002c40c2c1e5004005010041c5046d000700034910404078010761030894500b90180c9092403203041c0100040d07010000030324031280c200340143c604d0f80c0000c47c9441d068032803038041c0c12542c054802041c412250b0f4001c1081d940031380318111200c40014007126601d0f074902c1d0030b02d020340400c40402c80641c10000c1041185a401d000e45016004944c0303803185074901121419082051300d80c481a884050f4480070440550401e9101d8040052403 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 110218192 1250 110216942 110216947
    0x20070501120207150b2409040509010623011b08130503031e0d090f0302030703030b040b06040302060306040603065907030f11090601020f030a1b0f0f0210031808 71
    0x20f17400603000301517214030201d50501c941040d40020100c075000b010040b000312010402903c400503080d080705e070140030f402000e0b0b00700300c000c400640440c4240e007140074051400352003a124840308044403e0b1001c0040b502e020022403210490701ca4980480e02400040d001141405400c036540310a10501901a5401c03603800580707401000810b4008012440d0000700000a07000b203454021350760740c00000189e00080c9002d51810581c5003074010b2080851009001e182013a045400b0000c5076840035111903445a5502000030004909015003495064900c1c0714628089220138000b410590600c40c0da4070000c041692030600160001010844091100c1140c8042c03e14a503901d1070941e1540002d4100141d602c1c00301e00308400b0620701400c040381501c40300b46503191140107a075140402521030545400034021b0412043c411010200c1040800c514100403540c5619204d007001d01401d030540d0101d00d0181a04254100030610107040a85442c1c05c01100082010b80c200c000206c1c031000349540d100 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 110219442 1250 110218192 110218211
    0xd0e0306180a050a031707032307030f24050d170a110312011a0309060a0c02010902040f050a110f040603020a0c0b090c0102120f030a09032007050112020715 69
    0x104202280b45a01800319514030728542005000d26407281604038964100a001525441c07280c058890050440201c42070203104002e134441c0801d100911003000c256494220880d090340d42d000e10000f88640d0540d0341c00043c100180c4540c82c10f48d0303410550040301450a40d03070018021728036900b00540c0004840d030b03c0301c00700102210480903a040b24003151202090243c044d201e0002c07140c1c12160745040395000403103a0f541c9000c0c14041266482510f8100500084204504d501b041103c03403850720001a8551351640081d0848590601e500c00c0715a6810400040c0700891003102c2c42c0201000c03446040443d040080d461038851809000c4c100341c0c0220f50300405078000c842c00504103a00400f80740c901d15007540c0d441c0d074506111000038010301c80c80170401201060304044a0810301d0442c0c0d1146560b842e42144405449012004c80810080c0c20b07003003108240700c54500162100c0782d0041c040140c50a00010b00e01c003a81840c1c608a0340c4100711280004007150343c00000b1404091002c034100c1c50 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 110220692 1250 110219442 110219491
    0x604140a050603070909050109060602060f07090f120c09291c0b0a0f0b06040504050915040311120a050405010f12020c0109031704051203100f090902030d0e0306 71
    0x31550040e40c1160003c414841c180b03401c8032400054601c181070802c101d0faa2000f160301618080c0c45800c0158000001007001c0c0d042e5080d40f40d5120f504c0b4100ba4400301c0c2d5071516000808a076074409146088a80e0400c010446540210801070440c82400d021055200c44680c0d41901c0b628000c0000f5030012068100c0368941e07a500c1001d4000107034080306514a5400c0c140300c400400c0ba209116941381030703200f080407046031041d40390b03000780a00f0300307410030f401c143c00d0100034a00075200b201c17180300744440c10b140112140211403255100340c1e60181501d05880005241009240302d5076500d4005018428060380e11070b0948081700d10910f0700c541c0d10102d50b0000c0d1a450b4402005074403e500000d441040c608054200c2481c8502c42d9448680116500c4c94660350090240e4000703140e50488649540041c081c2005541c000780c0903409000c0241d0313501800341200030079502c20290300b61200c4a41e425454140000c20410607a0f0030254104100c48000984481005082d5540c0420034010b4010080 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 110221942 1250 110220692 110220709
    0x207150207050a120204180b01050d030509030a1a0f040f171603030c020c060711060306031c02011509050f220206130906120309030b070512040317070e060414 70
    0x2c010380000704054aa460001030090540710990080b4200342001c10004025901d011015811007590719059092108003c01e030400d1038402d81c10072401340040e40d040d503028400c10741d21512600764204c2359031180240702c5a462008140001081c521410000416003000703405502a074451001000d03c0e10070742c14951b040c0602c1402c05034a4900603149030826801d9405141907545a400b12580c88280f0b01c1044218400e5440c01007040c90004400b4814cc113120004e0360304000001c0c10350f4481d100d0b03a80026048034001e00d45000503912654510700d140009107a02c00030342006030040c0400e18110307455040f0b04801510310310890701509003210380b240700b142d041c1e54030a44c014206951203489801c103017141d2900d40035900c0312501c1c00340b00185c1e0604145041c0e00c0241e050712404509032440d1a4002c0c400c0d0001d0072074003030020402c4466105d0401d0b08040307221300d2198a508035604200704840e0032400d4000e101d00140700c011061501c4a555103c00e40342291182c80c1100b0aa60320500031030440c0307 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 110223192 1250 110221942 110221949
    0x240306080d0903050c03010b0f0405040f02121501060c02030d0810050604032103020702090406090201050909010b0a020105160e0f04020c0d120f05100308071a01080d02060f070207150207 82
    0x9001d2155102000350b8010500310880f80644203c9034541c40c44002c06003255045410154010096107032045a410980c0195030700501440708030b45101c1180d0040b07825450b5140091405402504400e814861108481d501605003031a10981c012401d030b02180d69001c03e05421000d014890300003403542c106d02114100600801b40c441500c455032442e0040704480f98801d00d030307140c40301c0e00d0340d07464003910903c2a00d6000d90010080c40f0962101c0d00c0b52401072200342800ea0400c28100541c402c20345607010007600030600a04166554240ea1800a085480207031038000c040d464001605c055560020703500090910455051071038a04140005001788600d40c002001402040d4404034000d40043c1c01490780399101e07a0901030140040d45030340c210f507421240150124203512051010071581001741400c14810380048800c6c4090200208040c9001d900c04200d030751004003c80034103907050010070f80021040c40c000c007080c1855900039450764428050001e4108940c68003128051003000554002c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 110224442 1250 110223192 110223209
    0x7020a18020403210906050f070609080705010f060807170a050a0c051c080a050304030203120a05011409130b040305130303080a1406010905010e0117131a01240306 72
    0x880140030034000c1e401500c002d840f850b00082204081402200310b43d191100c556070b400f500c090402c2030030344e41908001c001500181050210100107a842c0c841c6407010b6005042c8261282c58a1a0540c00c0d10800402c0503d41410801c003000045400100c0c0c1d82a01c5a4503000710040d440740224614020079224081c0c41e500c0f44000340818800c0030a02c0341d098410a40b03c51440d0440782052220031000c000005051401c10488400c070103220710082d40c1c010340f113403054900d4021001c2ca0042c512506480703a00b140350f03444004004c1c0742e051107501c0350f140d24251124a22440d1526002e41e00e0007451401400c800c10300c000103010148100e049403600c4218085170360b0050b4813420014039110049407120710803450710316252841c0440000d518880c0324140d407081d402d28204801155a0306071000078a0500515003624506d8509400c800c03445403c5071a88065190114100b0900042c56014040108002400140702170018894500f40c4155106640c601031050540d04400a148a9008070346 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 110225692 1250 110224442 110224469
    0x10209031f0f0f090c0e1003030806010e0607050c0907020c0607300f080601050301080a020d050115121b060c031d1e040e06061012201b010c120207020a 67
    0x150424154130020348039028076500d01c891034868011550078081034852544035841e40b0030070000a8402c0350f50340d40c82071041c035100c64515080390114209401090381110b41d0382000300344800d603003482e2001d1548500300f4801400d400d10540d0104040380305015015100341031202c4001c013070a49591201500001401c1203010a01c072a44000b0000303520b10014900162400d0b01251482d071142c400e40c0d050307510510103032104140b540c1c20001410214074044845e5500c5da031514859a40c4616180b0003020400310103144404140b034030b550b40415141e6a094103081a400c14005140e000e002e0950340d60303050820304100d010340700c00a45440b1805000d03543c0305092140c0c07000c010a41c2101150f2402054800780000301440440c640c880030100c980c1e50708030100c000355a140742d104000d0b151140203030301c80c000340520f51501c0181000c40417014143c204000003540c4035111070904007030940c01402000070080400c90500003060f941d0480360a8401d80c6e00400c20f50b00359541e1208003030090107150010754 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 110226942 1250 110225692 110225711
    0x6011722050f07090204030b0a0f0e0322050603010b121801020310030308060301060501140714240912030601030b040e0d08100b090d0204051314030d0509010209031f0f 74
    0x1903581e1102010785086000356000010044e0707240c000c1d901500d81c0000c01c8078803a9030f00c807254030007400d400d0680683e4903100c0b2a01040c0701e40510061040c03034001039002090080341100840d24075425400301c1c0c0209410401000b90403040e4042e070300c0480f402803007525540c8600320803201070880c076181c03c0c22a500c00410300101d290204021406c40c0d00c42e445c0c3d0180e41d60f400c8100360803a403061003080d0103d26002c003002c810443c004014001540704030014268144c8450000d4540f10f40040c85c150101c4030b002c1105414200301c951258804c041d800146030940d4131120b0304289003c045c0c40141031645803075891080782d869820696040c1c10540c00c50741e142e0090344005204c0241910551421f202c0400c0100d110008041110440240504120384003034a0b80d0903c4001d147c018660711844484805200c0003070f03401c071030000c1281e20b481d004540b900310a0b0818400c441c00640302c6a40c5038410082540c16407008070342006000c9c44590042e0b49203c049002001415400019180161800b10b044 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 110228192 1250 110226942 110226953
    0x26030f030103172205040b0402070f030e0604080f010609150303020712081909090b01050406020303011701021902030c150601080601030e01060909150c051606110f03070e090f06011722 81
    0x100440317104503400d100140c0f4040910040340702d94070016004a10465111000c02e002d266003c480150213001030386011f40e0b40c2041818010008110b03c1240d466480400c0302c0c000900a0300324031304054003501034851843e030b0003039074a000521070f40001c1a03802c1d601100b8003180400782c90507150501030b080c1c00c0e06024140244648014080e030340c503851408221400710351050b402c0e50142c0b281a0020340ca50b0b428a50003080101505a10003940d40d020400c03880100702580c1d2030b0542031400d0f00295200c09110b01c0e20b5050135180029101c00ea0f11000800801c1d03030340300384482d030001d000382000206e80c070348140c03020b014044c0380d000400c00c50b0400b04e441003003003083c4044d030899001c084030800806c80d01102c00c9800f4400c580721524038404903102d6901140140d07201155018640e880b5a1404150111001c180e070021950744001c544580060381503403c1250311140e2021101c05003200320724200c1c001810350b0021400e280810001440013a000c1c1c808400d901181080460828544074140d142c407 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 110229442 1250 110228192 110228257
    0x60616060506030706020609100207050106030501020f0d060902210604090c080a020a08120318030403050a030327021e03161205150403021207030c06050126030f03010317 75
    0x189800fa100d180e0700002c0240c8089030942c044c9074100051300d04a841101c2d101e0294000c0c0c01c054405540e248000000183d0901c000c2c003046140c8020140c40741d00507810b010403034800f54002c189203030042207024952062100f9007061506404424011611048042401000d650300010f12481c4003000200d124040000d0400710207200301c0301180415100c40200d81c030340900242000d0400f90500104c1d40c0203a030810407609402040d07088a040c40e0b41c80d10b0b0140307424028202980071030341d00d003040482c1c20028021084125004404541501201d40c082840c440c40125900c0250b800c00e80c0000b150f9800303000070101000c00800c40005503407101000030540b0340005003240e07a80300d50500c1c07030031051a1849103849550950090020700400319190040355000e09001c90801041c079009100040d00f40c490503002e860300b40c07654545240159140001d010030042890080d034020b00440c2102c603030100c00c41c0d05503a40400c10b1000e400c0f002041c031001e400390404040001c2c20842011503000d40c032048 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 110230692 1250 110229442 110229451
    0x50d05190f060302030607261614030402032a0a510905030307110a0f21030203040e090a1b0303050a0315080d0c0b06090609040b0606160605 62
    0x10030841c00d10511001c2085400340d200c001d4050b0000c0300060030f224000c0301443e0401c0c0300181c6c404003000d2002a23190b68400126002c41442c010002401445076002082c21000200050400c0c510300705600000d5861068818044c103e0140e250407911300f0b05010b0b090703241b034440070340754a020546601c080c2c00102e0720455a040c0030001c075102260004603500c00f07440107480400098250010000444007503c1d4600229010700c00c1076035000038503440030002004a00e000390052000f6144210402052000c81c2e402109540c603035100510840301c210111801501010009480c401058501030341140030319403100d0080c03030481040140398480400d0402e01e02d442081841d100031009140c039840285c3c80c0c0009000a4002d01041e03008030b001c0e9108035270410104a1745a803881c3c1e10040b142c5040b4041003070b980001d210f000a18200041401c5003604400111041e940b00c0c0340000c0491130164008001905e561041004680aa00c0702c40031034080c0c401c01000c90542e0310080c10040094002138a = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 110231942 1250 110230692 110230741
    0x40b03011517070501050409051f030812100605090d0c0305070b0d0b100806040203040f080d0603031d0f060a03021e030402130905060a0902030f150f0a060311040c050d05 75
    0x450010004107600c0c3c15644142c6a841c1000d007810007076801007000500380841140451200c03400b2182901c00a001503204e0304510b0740e20300f0b100031101c21680380038040d075403e60070314038040c030000d84c0280a0354102c1e42c05071001800c400040c00c02003111440350b440904903024444011489405000082c00d828441e5541400f80f0340303800342403200c0303003410f0f140c103100003214940800c525287c1600150b070000d0094a29402010709a00c0314410365000003145079889964803020400c060300402440c800c011074162042d07012900da0042511380a4040310b10348100e00010b0802d0a031802039041d1020240c881c00400e484c0c13102107c82d8012a403041c2c070207070312820305d110401e40640b0391405142c40080c0e02c040900b1700d686030071645002a004100040f607040c020500c2c0d1a032035840c104500302519084d105603189034249800c403107030035180c0540b02e0b03032603d0705105045c0042110000c4c0248016001c6e01c002442c0c5000000840382030080034103540703550b4244014001e1030130210451500100c1c209 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 110233192 1250 110231942 110231969
    0xb040f031209080d0305040203010209041a0a05041a040509031204050304142d041e050601030e0f0a0b06060d0c0305160c0c03020f030102091008092a0f040b030115 72
    0x4400684010442d8850303000581d00c0908a40580c0e8460f0b008560071500c090000350501d4042c500003801c1d541c02440c1260703141d0707400c075040350b2900e401c1e82c00030020902a03400b0450150f140341c1c82c40c181181030841c280a16100e0011a20600041041710700003052031000440c5424546403d40d00c0f41e1040c801c1c4440381c01c90b41e0300751149240c00d00d070301d5518100f0200d1030144d884a4071000701030b450b04202000d610607038401c03201c0038040d807288580c0e0800700901c0c40013807540313445c0d00050b048070803403050a01c06a0105108144007140010250313038180e0012400d000542c0c0c1e1f00005000c0344501c00b140c2c0d44842c20100c086010310b400d07400c03490149691025a094007064400b04580c25580e48001801c0c1a00d0ac58040001d030502058000114401a00142c030303112500d40880c0c542c003000440e50000a00c00d400700a4002e006115410842e00b00102c403c5500980503180760880148000991040c0c4414800e4031051755243c1c08581d0310480a8000d111074200900407d002c12581d205085d08400724 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 110234442 1250 110233192 110233223
    0x207052805060c2b020415050913020304050d0507061b030e0607030c0903080f070209041b06020d120513060e030a02010b030114070c06060f0b0301050f0d020109060c0c0b040f03 78
    0x70402990031310310540754071078032001005000741000748601e40e030481d43d00d03801c001c0410004031041645010060644545640e03040c01401c3c0304441c070b41e16074180000c03803050050000003100400c10500e581c49a10340107880f10b0306030414a000f0107414030040307031048070303036034445089601900301600703882030041541c4455807030300020b4082d104c112104800043c2000740500c0000c800c0e00c0034081e40c8512064250070a96282d000c20a14072080d2010f0b161034800c044031000384154214441c000c0c108a00c003900c2c1070000b2400241ca90841c0100001800d40c941c80041d05107403d00440040082d000b080030b015080070041c505880360310a600c1980103500b0700075281468141406640c440d40380200c0c87c0100d540c0c41c00c004603200d10f51000211204c603119040010114003042015007e081211201642c0c1e5240400b0000303c5004e02040c1030040080882c0c03800982c0e00100258125a07040c20303c095004a01e14001c5456a40c075000340803c000040360210b100a611b941510549215041c1d02410030035 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 110235692 1250 110234442 110234461
    0xf030c0c3c050f060d02090405070c0212150604050403020a0f060b010e0904050607030b1311090915030a060203130206040e012c07030b06040b0d1a04090312020705280506 75
    0x655000b0183c0000060068511905240f8000d005c0300b200080011f081031903510000c4e00340c0320700791003160001700028041015440c0847c1071010102501009202410203002d440c0d94105d40103101c84e12071540c0c0c00011707040c180284922001640c4c00f85050040c90b0141c03a10074018030014014600164841502e60203600b0300e400c0c2d09004580000013400f21b0364a00400320080d00d0214903168110010b1000455050401d0058041440c60101c1ca00c6d03c440d001401c0c0301c10040010100300380d2689031302d1045403a442c0495003141c0541c100402603665542e00c410400004030306100290042000600001c541d40c0c05442c590603103000481c01181640e00850303070340000400c01c9003010f0226081002c50b401ca170080d800b0000850010b4006801c0076500d0f6000081904200302465051381c468019001c00d0200e0045c42103001c000f12001c0207654150b0f140105200d2040c0204074169a0004001c02481030800840b55075642d11a8000200c03400c2062030705101c4c40d8000c0c1140c00e4850000451003410 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 110236942 1250 110235692 110235809
    0x50601020f030f0a03090203070f0608060607020d030311310603050603060a09231b060a1b060e0a14010e030306010c03051e03070f021005040f030c0c 66
    0x2a0320100550602018503e0502e5039884445984c081c59582c000d420b0040e10f0038801c10006040480d008500c0340c0c0b074064082c019640060417113114140030049080140d46514032021480d405140004e592111010a95402c0c0305111401e9401404110807042d000c550160740041201880d02024031140e652609031b0035920144c1d4190b0f4582c00c0480090342c820180e07440070400b18000c0e40c441903511014558110f50212a10042d0302035000210300200b02c1ca14400000d94806c01600d1184c0391000c406402007003400904442c11403a40a65503034801c4c450f082d0007845030907a014003541e000380740d640361144031850b200c030841c103043d4285070501145410120a981c03203120180c481e032446d0101580d0403251035010b40400b000b60120f4020b1198107202c901c0155200ea181c1d80c54000f9502c0072210040c0c44c0441680800b10040d040c50204070001d12181c441e5000254142440e44242166180030f915003901c4c2e4100c50001c1001ea081042c01c1c1440d0380100380b0160107081016030390440e2241440c4c03401c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 110238192 1250 110236942 110236963
    0xa021b060304020607080702090a0b19060504090b03010b0303040b0c06011d010b03041b0e10090908040b031306390801061202040906031b0803040e06010309031202130905060102 78
    0x100c003400040c1c05400d10f04018a485407055034080d2421340caa900207040944140da005000a075a0100ca0460b801e1441480e00c2d103000c04d28000000038500240102980f00e24003d2880140c0c5816101800d030310709412005815000070185d0307444507225201a1071030b1300201080c1540e0302c60704d00001803801c0000c0c0c10001021002803013501d140e09040c0c14800e664030203001252050b8541d13a032552921801060403024109486044d9194140411055084041c5070130502d01c442c90300e0005c1c0c0c00500c2c0340701190101c0b440c5101690300c4c0c0c1d13035110948402140e150070251119081400340c120900c60310a07204180403002c01c41e01c82d01c21403554a40c084540c2c82401c080410800d80041c01541e0013504194003254094002524054555403024190b41341e80d1300c110b0f091801640700c0345d44104c16283d61005085010011030600c0e01e070511000c0c190303030040d00e40380c141a81c940309242030500c40d062448a03015000c10543d81e07142074090320503883c40d00307101c0c45035520702e04401b02c2da103584003051b1140321 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 110239442 1250 110238192 110238199
    0x1002100902010e120d02011a210a0b0405030421080702040915020a050301091b080403050a020a0605070c02010246140a030806150d0e010f020f0a021b 66
    0x80816004150020955210241e05000d548840d4501c65503d00100031522400003014110160000b000a0b003568241041c030b0b4a00a921300100d040d540340c00b0a02e440c0c101c030300f0404107490b040305e00e0300361300701007042d580a081c10034507008020901c5030010041c400c0300d6030410902558650203824403d4902101e0005282c0d2108020140240c981034001e1003000b80950000307001207c1c4255510200d070311011045c004690040700400c4504806c3c0300c0c120000c81603078500407400104140003400d29900400c020180407001c24200c803240c0c403c02c020718060358440300c10425410b0071040035000d000c40f814124010301c00d48104945101300700030049600640700c603081c5805913034545205004000000008035200160055001041400441e40e182d41d84800143c0102045424000d011080041400b4014480e201900c0d8800580a00700e80d20140032402c0040c0103049070fa545405005030340200366900d4004125aa0f0001511006188401d0380d60221001148400800200c103400ba502c0740341e0 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 110240692 1250 110239442 110239453
    0x8090303070f26070b06120f070302010e0f03190503120a1a0103090305091302070816230304140315010609090e060606030714070b040309030605060d02090703240e070e1002 76
    0x1076401782066041341000b45060142040c00c00700385c0c40c1030b00039420740400758000b084c10425546c00041600d81c0e81004c4e10380284000e61940425584c00840110f000b0b0f0300741e0842c0450900c102070054412864a001c958140d904008a911003e008070080031144030720a41400c1160390300074403c000f000c80e0705458003402d1500351010040400c0034040d408058a0b001c000582c002160540201680c04a11100030300b4074002d4149004402c80c4100d0607002003021201404440000000b80c404a4001c408030f44e41c5841d003400400c1c104005010b03441301c42c103400e400211315560001104400c1c0c8030000b00400c15446810301c1036585d03943c19030f44650045070410100e004d2a1140704020740025903904110b00c0c0103116035440d02124022501580015007880b002c0c401c0200310b002d9190070a5017150300490804a54001030b00c1d100015200d038040c1565020b140e8014881090f40101c0501c2030f8100002030b0341c0d95040c01300325580485280d0001030020000c1411454076030320203c0c881c1600c0d0700814 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 110241942 1250 110240692 110240707
    0x14010f030c110a0c0e13170304081c05150d0c1206060312050c0d09080309120c030d020c12070305100f020d020301140112020a0e06030408090303070f26 67
    0x2001071401485110400c21086410818104100f000050540c81000034110580c43c1c0108900c0d13140002e4501380030300404c07450841c04110404d10300d40260309443c041c030b0b50366200da00d440192485003200820492081c0d00698001c1e0307000394000e51140c1110b43c828942010243c0c20804641c144400050900242d11400d012507881001c002152070f100305000558540c5035103841d07823030300700600e80b460000d14001000100c7c4030381444a0f04640540d0b081610609080c00c070380c0c40d00d80c0204540240a51080410100c40190801500c1c080c200c02030b0a031801506801c00003501e0702c26044020b40566154412141701220001c1c074081106d0701f00d0064840184007036410000b4018014100910079020b01c092285800984011402461450380880c00402032000141c041c01c1240702c0c07240b0300c40c410301180e2103068202c500e091081e54107c507801d40d01d6036180352040640c0100c00c441a05440b020558178204000301c245101142d024001c140207030640da0690f00058051000340308002001480f41c0d5 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 110243192 1250 110241942 110241947
    0x80a061d090709111606140f180102030403090902030702011d01020406081302012102090306070c0510140a0b010c06090308060901080d140c0c03060406050115110a02090c040905040c050a14010f 85
    0x1250185c03107a200828132010201f10120300800564151802100c2101404001c94440800d41021002e2900039030841c9495103015000100a114450070325400100244030a8800c0d40620b842041400c2c1121244500d4017000b4000d400078024400800c0b01170b00440c02002e030400541c0f081950503035800c0c101c0900651490100300c15038488018894092250a9030313035030144203162103109150b94402944c2450304000c1d103040300c000e601d48821840c003181d22240c1c000500c18149d100c1044140462841510300040380c1c1200e00810140115290180e50020954450006406880219000003190745c0b00c00100b0f0320348042c04084008681050740c0a07484800c00806090240f08010030380d02c1e5070384a5000710b4102003085a0445055075510010301c44071648055103038031003003176181070004003404440c03c80d42e03010a00800780c0707c0d203101000550220407181c102c81c042c1031204401d001900305031070300039080e00090041034031421036040d010070300d040c0607159243d6540c030594520958a1481409 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 110244442 1250 110243192 110243227
    0x30109020916090b070308040b25200106080303010f06020f07051e030102030901050702061b1605190818011403040f020a05060703050403050d090506040303080a061d09070911 77
    0x1480500200f0140021513241900c0035180203800307512110028586032804c03d2001000402e0500000500d0340d0304490075014030f140101200307183c14886880c0f01000a4014101d1003896141c1082d801c0002c089004400800694121045011541c226503180c540c1641c4811411004101c00c0d4007100e0108500c0c03500d0a00307441c800311045a03911400e00302d07802084c2039900c11202c829440e0b4460061240c80c560400c40d007940090040c00f0000301c00c480a034400a184540c0300030075100c0103401c442c44140b000c2840400d058415a60100e40104540e161207801da400990300105030f042a01107007501e0f94000d0040b01240b510083c0d80030325603a80c56a4800041401c0300003070f81c0210b03020401040f140c5410004107078031402a10b800f5100d601d580740003841c00d40a14169410440e02c0300080029440d00005d4405403030b4181003a900a64030046103800501295000b00c004009540044500030000c3c902c5501074603014007511816600c562003c415112803100e0bc0c040900b0070001d00071302079008401c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 110245692 1250 110244442 110244481
    0xf020f270c070b010305030304020922020f060409050f0f010609120303020705100501230a1203080403020111040303030c0818070b130b030a020310090b030c15070b0108030a020c0301090209 83
    0x40c10742c1001141d40350400080c000342c0080f150303a4800000e0006508c0d0140b2010f900c07030006c440c50300c0c18261440c82c072690003146c8030000340540c1d00000c0306c0d41e15644c0c4000780c802071b0884002c10481c500d404820188491006d49042c0d1812100b800082900c07889508500281ea070010304c04801e154181d07400306c0003988903030300c169024062400c1d4111920040d01950b8024035074441102c070100004144401c540701c0880e0818440d041c05071040180351b000180c000445601401c21340c8441c2e480c0c1c10160b0252000c805021741103000002c0100405070036600c80b2841e40c00c995a0a2420758a404040642043c50503481e071199010680c10801c2003200d400511022220113a80c100083e03580d50001c4081d0000d032a0143c01e60340110070003441a01d40003055004080c1c242080c00720441c3e01020a071a200d0826256028111400c501020060500100c130310280e400207040e0415a17650703889603200c0c0c10074680c4000600400442e0300d06894140115042913030004d00120803516000c407021440c409462 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 110246942 1250 110245692 110245711
    0x105070804121133060307170304030507030305031006110709051b0c150c07151a030d020601030b090a02130506040608070e0708011a090d02120a0f020f27 68
    0x7582203c1114040c0700420a1a5071440c42c042e2003501d1303030951032141d640c88030038003000104042004900d139030005100f01151102040300000c03003411604241144100c0d08064017074860482d00108165205000310b105400030240b800e01d4a0301e8090407518070240006204042c0c0c00680c06101c181d5941e40003c0c0c020600041040c0c5110f003203240ca42503034018008200300e90708594580706027901e00245295019000c60040c1e0318006042d07842c080c440120021a1804903078460301618a801210901401c0020050403203c8100e08000001d560344024081140c1220110b80400d002180009058084950082c04481c640c2c072100c5542c8001d04006103003070ba0281c0c0324000021008020311079900a480b1003c510b440926194402030400310040c9c0c080c0c00c2e01c01c00041c040030340d10900d9040c0c42c000501150012400300180c0001061040c40701c088006a014000c0c200c0d0400070706420701003126109407030384802c0c20000c00c104001011240342000c032108a40c09003c030306902d65241540d014400d81e = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 110248192 1250 110246942 110246957
    0x150a020a0b0a02211609082e05041110080105010507080c0c060f0301031e020d12170108010204030507050315040b1b0d0e0610140d0c170309090702010507080412 71
    0x30b4404000c40c0d01d00800d04c000795a0600e090090042c1030109248140703015080210100b40f41081e640d5840000c41da05540b120300900207000103d03e0b03d0b41c0101454072020040c42076062506141d071000d160105558400c09414200c7e4400900440195040f941e050f150700c0c2c00c007815615001ca030340c1d10815400f003030341c0611001083c83d6520a0054000c100d104400076442c0e60440c42c1001607411b402070807412800000034100c00503610f0041c550344040d8002880040850149402d0343c82d20b6510501000c0c02100b01c001258081056015200300d034001c508a81100780c0e210245034a51003081480840001c10b030000034049904007400e035402010b00303a01d001c40102034258000103900101a901c0c80d42d5260240500030100412460b6005500101e5010b6050b14060365078180c031042c48800342c003405068003080b003400200d050140003031800d85a10040e904009201c0d03502d9074802500140b04aa0100100d45e5041c07051044500c18000d903110103e86440300c0d05c0b900709141c86e4005010810900 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 110249442 1250 110248192 110248207
    0xf01020a0305040b1b01050702010203040212010504050303240a0801020903010c03020f070b072a0c080c03071a091801030203070b0c0a020d0f02100908061b03180705120606150a020a0b0a02 83
    0x74802d0310300c00e103023a07400140c40c0d0910b481000100d1000c51040c04052781010240004140d0110480740c01658207980c40003034843d045d54501c40001503040300c03035102400820020310810190010181e8500481c020016002e042c0001c2d0202d028551664035021410f0004000281c1d540d40e078581c114445082042c011140d84c141c00c00c210520329240451403000358003c500300130400306207002416000c4050b01c040080c12021030707502d2101d4441c0701e442d0a000300400032a044010200c400d41c0c0005800040100711521002c0c40d48502844224028811140d000895010840507034480c10601d0000d03082402d5260200440342200100c01d45d1004449414100140c0d91081030011143d07443d10340c81c0c0410301e07000045060540040522002d0041d0440c00c80d0075416003030840e6444170009a0304460480481c070054030380030968000903003180800c1c0108548a0f00041c80300c2c411481162209040100004452040e004040403c00560322800030701001418000881c0ea0000030404011b04001c071 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 110250692 1250 110249442 110249497
    0x3020102040b04060e0a06030b010c0b04020f06210c0a090603020901050409230901110a0c110a030803090d0f080103030f030902210111040510050a0207081005060f01020a0305040b 79
    0x10760100c03011417180030019801d4184002081c0c0200610309041001001050020b880741521000050501c24044001811980e54010b110320b20503015144903140c444422804c00c00d081d141d03e05e024203403240c3c2c0000f4085c5d9013160803181001c3d840d6583c4409140361140035400b07500540541410300405000c04292500c841c464250302c61aa40910102e503480070156502101018060b408030ba41014036601c0d00e240e945048441d00782c420f1038400c843d80e0540c10500034021041c0d078404d522018202000007401641005140106500c00075518007050a2405031003800200001c14080f40d100d000400c0030074040c0c2a4158201c3d0320b410701003444112540007030460031b0b414010105003003030745941c0b59000c03000f40702d6a0350380d4045d01441c030b1502c4d06182c0011400c062070b0005000f00304000820050151082c020a001441118112528040c0540322030010b0102145c2c03640c011038504050755541d43c400502d183e80e82d03401d622014a0320f41004108a80341d403010301c90700703518030350745024000000 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 110251798 1106 110250692 110250697
    0x60102071a0702010306030b0a09030f0203031b0a021c0f020c011706060915030411090604150501030f0603210e0303040602060f070306030515010e0c1204080703020102040b 76
    0x42c00b840101c025218a0700300800700240f0b081072207608007603504200d00c62486034548803400b42d00e06004980e60702040b110401c845000440d0500c1402481000702185a51441501c0c0c001722207081d20b031220000b1144520000d5607200d04081ca040d414045003001510900c0d040d40c10612200500200c0d4102034900740c4580f40018000340c0700d80c2c80b0031389001c454400e81c0b00561603160a0600440900c6a4200b150164203202d0000d03a42d4034242c07244894169101074110001420321004400070514a207941e1101d40e6070b280084042900b5008130400952807007072440c060100c1c0d0301d005004400c0c0072240c900a900c00d00061140d90b4000c04ca4580c0441a440c00a00c50343e100d210882c05803500758009031890298146005c9500d40210303410b81607801c4002c0c9520203440e00070b05002e0a101e820040388400301c81401160000341d01c10010100315002e803002600709030300c0381d200e0390307159 = true := by decide +kernel

theorem cover : BRFrame.Cov 110071942 110251798 := by
  have h0 := BRFrame.cov_init 110071942
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110071942 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110071942 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110071942 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110071942 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110071942 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110071942 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110071942 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110071942 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110071942 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110071942 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110071942 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110071942 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110071942 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110071942 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110071942 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110071942 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110071942 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110071942 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110071942 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110071942 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110071942 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110071942 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110071942 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110071942 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110071942 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110071942 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110071942 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110071942 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110071942 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110071942 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110071942 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110071942 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110071942 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110071942 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110071942 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110071942 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110071942 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110071942 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110071942 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110071942 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110071942 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110071942 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110071942 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110071942 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110071942 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110071942 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110071942 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110071942 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110071942 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110071942 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110071942 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110071942 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110071942 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110071942 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110071942 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110071942 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110071942 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110071942 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110071942 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110071942 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110071942 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110071942 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110071942 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110071942 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110071942 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110071942 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110071942 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110071942 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110071942 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110071942 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110071942 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110071942 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110071942 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110071942 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110071942 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110071942 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110071942 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110071942 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110071942 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110071942 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110071942 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110071942 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110071942 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110071942 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110071942 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110071942 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110071942 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110071942 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110071942 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110071942 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110071942 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110071942 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110071942 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110071942 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110071942 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110071942 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110071942 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110071942 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110071942 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110071942 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110071942 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110071942 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110071942 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110071942 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110071942 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110071942 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110071942 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110071942 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110071942 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110071942 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110071942 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110071942 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110071942 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110071942 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110071942 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110071942 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110071942 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110071942 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110071942 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110071942 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110071942 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110071942 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110071942 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110071942 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110071942 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110071942 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110071942 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110071942 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110071942 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110071942 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110071942 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110071942 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110071942 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110071942 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110071942 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110071942 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110071942 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110071942 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110071942 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110071942 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110071942 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110071942 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110071942 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 110071942 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 110071942 ≤ n) (h2 : n < 110251798) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
