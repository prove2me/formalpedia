-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1905
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:06:25.749039+00:00
-- url     : https://prove2.me/submissions/8e1f4cf5-c243-4943-929d-f2cb325b9521

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 342446043 ≤ n < 342625899 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 342447293 1250 342446043 342446047
    0x50105090f151308010f05090c01080a1508031314130509031204030810090e1e010b0402040b0a030c0c151a04151e270f090b01090f110a030e03 63
    0x100b0307421050001c1c102a003100303c0300169203080002c89801c40b40f1350501d2100c002d1800c001c0c00860840090f107100084c0c0c0034a000703803a0b541c0c0d003800786000d0700c48000c02c200302c00083c03036001c03800e01c2c0e002c009040c0c0c08402d20780d200305145e038610400005552401d00f00b50820b400540c5020303100683d03007205612600d0881124902030740643c0403440710000312070640020b00d1040a2080b05854074032100000d0038124824040004059002d070b4860350300c01c00c101e0b5018808101c0c110411400c1d08000806200108210b4844da81c400d40103d640d0b021003041c4000070304e802c001e819402d00406940c149983c100002d00b03400181c0005a60007040c2d842c003a60020900c071007401d6000e98682c0111120b0142441c0e12000b1070f07240184510380c038542c02e40b201007196442a41804024414903014040c170742103a880d00d00c2c1d10004640100207203100f5a46c40e1103e0704084c1c0c02c10038007000c248014103c1c0e62516041004203200d104c42c00403291000c940c00d6900c4002c000000515100c2d81020500c0400842524 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 342448543 1250 342447293 342447319
    0x15030103172b0606110a020109060507030323190c120216150605180108060a020723030301170102280912050c0103060e1306090c0e07021b010207050105090f 69
    0xb00559003520000e0203143d01c81c0030502c01d49030b011400d4022149807600030041c0c1c0740c141d0b0018040f42018014481040400b16494080c1407080e0049a030f59100189000000704001101c030070004821944408801c0440300e00c0c0c901e26005100c1c5428200c596a248100044d034090084065800201c507100c0f9400600710460203d84601040d900c004600c2c3c034006052450700c4288112107842a4030340100712003581c0100304840000c81e600707038040302c403650040e5038400c246880d583c00d00e10800c00360802c807000b880c44a00701c10004000c5040c0c0e0f510240c078a480c0341900d40280c0c241d101d16a02104814504142c080301100d41e07100b0a80c0a0348542052008078ee03c407200032111550301070f402d55459000242040603960180304a0014008c5001101200d1514100c031604070352000c207004090340c0d6203e41c1c1d68140003010315824080c2c03d440e14020315900345203030300035038030307600f032482c20806280308915050591300000381c5504030349041e1502801d11108100700162400d02580c1d4030380003490741d1102 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 342449793 1250 342448543 342448597
    0xe190e15011a07030e04090507080304030501020903070e150405180a0c090506010f0804081e03090303160908210f0708040f060c0b13020409051b1503010317 69
    0x14820303444aa00c00a561400101d00e22103015540c032589840c8080050300b02081e80604a00001c00d010380700441ca4080c245840c516010381e0754001000b500001c500030041203c190010560100c00310221180f094403180c1c0c500a40c6001d880d03951a40481002034001410250170550348440004542c00c009003c2c0c40146d400d001c000324080703504c2c612031001031140c805d02c1e00c90550032540a18150101c6c683d113900280a440014001421054001c65103072007003d11001c43d1109500c07140142c03516801c08082d21035403038006451503030180305003281100c003c9109101c840c1c2110790040c002d00c0090343d1040308141e51049114040d840c0d00d000c1103180c0a400c1c5010003000624461000c00e40e07694601207602000d031080350040b10400840d02500404500d106012541120007141c0511a2440360710000700140785900c00103105001da48549401e00010b02c02420304410140e40040302a5160420b001113403001340030082c01414501000421928000080c094190742d4985200040c01c42c1406 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 342451043 1250 342449793 342449803
    0x6031d01060602071e050907120e03070311210306060a03091e0c08060714030a02070b090c0a0503011b0c0206040305010204090605040b0f031b010e0402030a0e060601090e190e 77
    0xb080c0050b0780724440c03c002e0403406468070000b0b50060f504001d0202d0920700040c120241c003402500800c80815100d141c07410310395015000d4101c290302101d50701c0840e0310b0082c241d1140c0d0301241001d400340e042c5110428031034154040540560955075403940e918882001040c0d04105050750405981d005202c1c001045007044070040b4405003c3d0005100a0707103004082c21404c0e0308900d07455000001070191403a0814403209500483d02c0c11580c8942e62640c000000b80203420300942282041c0c0d01f4003400100114680f8030704c01058481685143d118000d0600741c4a01030703200c840b0310100826182580d803260704541f00191004046600e42a500c0d15031600f681c0040d00165007a950350a010230041c9403500c20603941080540d149015220b18400003a03c82c0c00300384614147c042d0300703500490260700c42d0110059000700203002f1520303414059144030003008000b40c1c648142c032441020421a6014000704d0003111181d00140c0c0c0349546a020355090380540b00c1d40b0015854030b030742d9015401c00081c81 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 342452293 1250 342451043 342451049
    0x118020d0f0f050115050304020108150d15050901022a070e041b0f030302100c050c070b03041a040b071b020a081c0f020d08040503040506030c07030905040506010906031d0106 77
    0x1010070582c8038038401d40300b21101030303000c07924185080c0344800c20030307401c00f094079401070f024207080c0007550369031a07010141400b03913500c540c1c0300306100c2c0c0720020050100a05080400008410000c1c0e55852005030300301d20413000081c900c80c001c0c400710200c1c20a803071004024421903100756492580d071a401218821000d480c00c4410540680542000455090f0700300010400406001301080c9140c170080d44541039030881100706500c2e4030801002170b00030340c01c5a8100c0c460303200b07d84045a6800c1030000030340056908440240c00c4c509020300d000386c040082d170b0282da0000401111030b190701c9815121214100020240d2100d0001caa0000d0790300c888122009011102c040e01c402e100c90401e05417001c0d0340041c03002c00d000340070004800c043d170b00040802824845003401000c81d00d035410614514002d65200c254840b10001c204000303004035001a001080c480c0d22502181a103600421058450032075015001820b000810862184290440003014840c0ca020320440d65001417042d003503501c2a0 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 342453543 1250 342452293 342452321
    0x2070b0f040308071122110405102d0203070314070c18090f0c0e06150301120804150f12090f03030519060b0306030d180e1902030708040213050f0118020d 68
    0x180700c80c80394106c00d00540060a00e082c01c864a05070030100040c0d890004003040100700507510242121070300048020503041e141c4014200903000c40382d0070081d520f6000c008103c0026100c0680041c10f1304a04054407603803075000721040011b80c2029400502c410401009580c0e2584420010300441c810016041801c0e0150350601503540c2090b03d00d20703006200cd0451800b0300e0308a09e5803c0c0c46482c61081c1da054407203551104060013150f0a09202a020f03035001514840e6000d09000c1140c0d4004e050752948401589500b000000106041d03000c07a2010135000c3d0410080c00100c0002a209900140c0e0012421040301e44101040d1201c1007101c0307068000c0c1801010000a20005d85010000101c40180c00c3c505071550064080c130490302400d0074410003005550001c0421681507003060452100205d10508540f00d140031080104903401c262416409030b400f401c16488824440d000d07880c0f082c2c1c0f060306800380d585d20348050403c00c0e6800300d242e200c4440d420b0007858601c00880c01010b1080c4200 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 342454793 1250 342453543 342453589
    0x1802090a05010e1e030c060d06030c0812030a0b01050d090b040510180b070507050303150a090e1507021207061a030d080f070e0d1202070b0f0403080711 67
    0x608240300d2421099000780341030080c021100c3e040396692440450200501084e84003041004c2c0c0c0c040703031070003000c100c0241c2e200f41e02007544c81d6005413a5202c401102e00034030400e070300656a090020703100c80e04100c03018040d03042000010141842600070b0302ea100d038103251091a1040c1103226204940c01500210f420151002c00e120038884104124101071011410403c5560b07100349040040d40a4502c00801a1445d000014080d60003141a1070203550000143da9a91906041c1d560b070007581d81d4005071007485030003004100b02c01c180c400c1c52040046c0c00010030700144c084c030003442102401001501103100e200031151404492034060140796101e0f5001169001180d415407803841c84d01d03001c11b0301951210040c407113540e5020721038503009080a06905e00390344400c1011104c800c18100b803590844a115a014108007850030300d204802500c0c4d0945420350744a1450f05050302c12400d6269404100307000c01e201203618280203040c910320402458524031600c00118102506c4944195090501 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 342456043 1250 342454793 342454807
    0x30f0206070f09030303050903040b0f031b0703051204150617100207080906071506030b040515010515132d08030702030304060c0f02090f150901080d030207030203041802 75
    0x1000400d03080101400c2000c040444910b00410880c481e2201908154842c030220b1081c0b80140202c5024000c84490941d40e6211440c01001c10362042c0c8501d90501c58819640024007140816110801d616913100d43c40c00350031a8005140f140040d1080d144003600b000454448d00c4588070f901d0050000c00025504001310f064458101065004e100703120394010000388000030b07601ca01f19070303002100702d8042d0784501107400e04455520030040490465440e0030804420711411303400c0c05100b079200c0c200322140450b089900402d0724100788500d0b41c224a00c1000071003000d00b8680508040140c1a042500b40ca030383d05006080300c1c036071a419001580c10b40710071808500f00d2420981c042d00d8040021482e1910941c0860398030b110317034400d03102001012524030081054440c2005d00450300201096000c0c1410f00c0111001d0102769010310101050403a5102e290034107000b854104c0701040058990054410010340c040e41c0700348001c9085000401c00400c14010030581301a10021015005031580c113 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 342457293 1250 342456043 342456047
    0xb07020d0809120f130602100507180b030603010908040e06090c040f0504110d0f2c030d0e0a020d05150a0204050d0609080f040e0402030706030b01021c0c0807030f 72
    0xe000502004006181c402c101c4801800107103030806500300403076140c0d10005448000c10501690074132200c84800510001049980010756550041e6403034410422502e80c98416901e006a8000347d0b0059842d00d001000202940c0e000f550340444050004204603a4907076507145a580641c10000440441d2010b0102500b840c0d0108c503803046501007514a01810100b100d441e8140c03610a50744581c0d00c86c4000545d149485094815010018805100f44e01000111002600b1000c3d101104420b0340413174042280500402d154141c90790201030340c13802031080da00c2c0010302200c0e1140c0c200344c42214004001602c40c0c8001d007119600610142c2a0340040c45924401024003174400410280140021300c1f0b1941c40a035480902580402d0000c1d000d5080c1c50441c0c2e917030045c1d014480d9003a001050004d035400c0740340c40f243d1040b4400c50940700100e895950590403a0600c440740360040c0c0c401d0045c25103600e48001c1010281403181051b0381020081d42e20044240e01c500303003c40c0061090b40c080d50b041a = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 342458543 1250 342457293 342457303
    0x7020c1c110d02180606040f091409030f092103040e010905060a050f0f041103100303032301061407050304261f112203050f01050f01051003180b0702 66
    0x252003114402600590340c3c0004000080d900200d0311202c1da031002083c80359035201e0840700142002c0c011405c40c9541c0b001c00e1001040d820300d012040c58414070000300001d6001c81150300507884050b041741405c0340001131003800108140c480c508000101d1070000b0003807040002d80000d1140401d003501d40c2d0305242e410826214050a06801006034090501c00ca56070540400c1d40304506650405590a1031800540078001500031000094000400e000e40c50702280c03505426a40a80c07070512000c0003440a2444440d4510602d9510340c0f0180300502c005c2e0310171000441c0304100940614101038403512450305660240d44044140c84041890001d000c914090861144082c1005054204240b4081181e000151609000713815544c0f00d00c1d003480c132003510546040b901c0902420209242d0421802ca801d0021b00081d200791290b60f1000341d4000050042c94403510a030a041390959207864244022403003075a01d02c50078180c8482c80c070b055a052442030301c02c42c94014001c00c0c611b8106400047d00700 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 342459793 1250 342458543 342458573
    0x40b130e12090310020903010906050a0c0f020715050901020304180204030215130303120e120a030e031602011d13090b010b0703080613090b0901020a1704050c01030507020c1c 77
    0x6084248600b1030a65008074081d50314060762000541d6a803080800a1300501003404018240e0340f5200a000c0000e002d5070285124035215160f1542241c0b0240050341e4a82d4180301d8402c03000711450150f803402d40300d84007034641041c060040b01d01345a22200c82d0f560311010059070000341680820200709501e40b4078005004400400c110350310f0885103003644004040d45001c041c05010318103c034030480c8581e6a01c42c03895202c0d100f00b599940c48a43309001a164012280180000d08114000b08c0d506000b20850350700d50300340d02420501d1400d5170700650305c21041d9105801c20100d1000c00c17000030b03210196411410050800001000c1380f541c42c111040c0341e010380018502c41001d104d841d00194000c80c00301d4210804071815a12403e0982c5181c0c0502680540245401c0ca0142404070501c0150080c02c86079402e51100c4612104403200340001403021a0082d000358068440509035500079070015801c8003052042d1081c2c001c810700442c7c00c4840c0d1881c08200000d0750084c01040c014003195417008 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 342461043 1250 342459793 342459823
    0x411010201230a0902210c040b04090510090212030f0c0115050d0f080f0409020712020610140d050d0f0908011406040c11070803071a07090b0f0409050703140f0103080f09040b130e 79
    0x10500c10cc1d15802d9540004206041103503580d0070012040d5902c104004005110705402c4a42c0c40f0f5070712510b0009a0480390000c00396600705070402107008036102140c2c040e2240030f00340c1146a5403540311000d141c08001c00645101008006c101e0440410034000c0002d8200c5482c00742c0c0c0c5103110b142c110a1124000300310300464000c803041c010b0440c0151100001c0b04d45144011f50201d0400b80043c0440700308403030041c45845214420700402e900210415034118468030b0307100e100380d501d501c590f00b0381c0c091002e003c161211040020703140b072030598040c41d1034405e180342105013030880c07031450352420b803c07a008152650b0000c03400008200743d034049100d504d09a64805695818580c2e0081c0183c90107001302740d00c8038000b1500c0426051400141d60081501704000d01441c200760070094001c0c42a0070102d41c00809940003e1039038821540e801c0d0407650302c03960b0a4030300021a801e05501d904000e041c5075100d51140b20b407903120b540d02c0020814038280d815000400e000840045450030401c5014090 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 342462293 1250 342461043 342461051
    0xb1306031e0b190e070e0103020a08011a130209030a0b01170708060a0207081c0f0e060601120f060305160f0807080a0b040c030204050411010201230a0902210c040b04 73
    0x10018103040302075900f0a181611196120310044404030280c04404007030785a40c810035800103040b030b003c1995035048a0095034800101d49c3c55190f040e003651b02c000710030400c84810000611041c1410a10058000c505010040c180703500f03900001d0501c003a144042d2100e8101100610090101c52010110b100d000d9008004d0039103400071550304e40707400500c0715903855804210f036000e00004108a40108107520036880c008107212100344001c00784060081d10141c0f4001000030b000c1e000040c4240a40303016198402c022100f001e03588060039004401c0e5912503220200000002d104014450440c12070b1110b000718503003030514014203645d40741d01c151920b03440310b48100440c0360045480000716401010030b0965964a05155083d0076590340000e402c540f40c81d0130481030240000c82c6c2c00c0410303000d030700074441041c1101c03106804003903072141008041c4c03410000c41e11121541e48003004480c8058541c1c9082030132040c02001880c80e8000c010015048581942103e14180c0f10f24500c041d01110104 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 342463543 1250 342462293 342462353
    0x40c0909032d0e061303140d1b150e0f0d051c060513091a0103030519081005061803061603050708010e07050904060305100b0306060f030a0206030a0b130603 69
    0x107205410041516000b6880000c00c9089000741d0043c105c06940c2103c40c100e54007400300842079564508a10302000550054071411245402d04900700220f908131aa944c45940c0d98003045006000c4640c545043d803040811107031040c602030004181100e540d440d61501d60810220003182c0d4000081c01041d10b80c6030400910180c0d4a03801500207403201901e0004419150b40307071040c815884c039082003000d85020340000040503030100051001d664100503003003141b00b0040302920b51a00c169403600810b800450180a41d04140000c0d001c0031b000e5a8088809010290100c4d040910944d54040c0c50442050001e41494140c00342c25004645403a09540d03943c035200b18000070386409802ca41c00c00c0400030300c0e030b0050754640d040340028507000f030181c4140203480600c3d24010711403100014000d0041e000010164035100c0114205a0800f130068160300403158200491680014204414282e0780c1148000c25114806901d4100703110341d900098040c19070400c4181010850701402c14245506020 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 342464793 1250 342463543 342463547
    0x1d030a090801051303110f1902030d031103150a15080603120c0c01270f150e03071203050d0203010e0f0a051e10081b09100b030c03040c0909032d 64
    0xb061341c85d400d8940f4451811800f2101802c3c5400060088900d110341243c6640d001c40000d12451020b00c2241166201c05d0391140c2941a00c46003001c002c1e602d401840050f60a0f0030040c0820310481d401015809440d8903042d052001c5050000e20100103440341c000c2099500781000110794111191403428105402507150716500d60f801800c0a040119045090000194100441d41d0010407020701c50b01040d10f82480307010020041c0b090408030808940a01c4031a8010701540e10b0003000035000c1d1007407504058000b8043c1c420060f04404004003080708681d8180d00c2d101440c080c00f0360a442c10400c0c14000310b404601c41c0064003080b84189044144105c0801e4414074220510f80c2c102c40701840e0b80c03103200b14a0f11214541c081580c6d402030762401c500410070310f030303071204082001c64034150591540c903d994011451401006074038001007004c101c09420003000703107034002d100700003280c0c4660b1101203800590f4451031089021468640040e04007101000385000030008448075950301344240f03d40 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 342466043 1250 342464793 342464821
    0x10f0e070503030c03180402070203010c02060601030f0903080c0c0c0a150e1e09190f02090a0605090625120203070b0f091504060207050a05150105061810031d030a09080105 76
    0xd0318210f1541c548841c0a48488d0103540c24036400070700030880346440c0c8501035140d41c070881d5101d0009283c0050305141601d103200f06542d1941668501d10545d90b508011010707684501403c855611400c00d55401950fa042d12810140094040351317030f0000442e42e005002c81c400c01c10750710300c11803403115400e05800c01c40070b24983c46a41214200b8650700d03606500c49a00b2154110260418180711500150304101e4004151282059944402c96507444c14103c0c0d003030081520480e8411400c0059803070080c0c100a040e00904a4142c00a0180c0042d50b104a040c00d0300d0714080000da000800e103e42800710b1042000c4e84015092042901882c041c08120340b038a008043e0080c000402074003140a2141039415600d0240d400411102c4110340d03414030b591390381e004800101c0003001c0d010010920741050b400ba0b032492405242e505440c0d42c100350810424890a81005040540e900f40407904e1100f00c0f891800c810815101840c2d403000c1c1c007175008010503601e41011109a040409024416a18882c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 342467293 1250 342466043 342466057
    0xe0702120a05130312050715050c030f152e020703121202070b010902070b15060703080403020c09011806050a081c0903060507020123070c23010f0e070503030c03 71
    0x1500640e52002c0b00c000d251004103030780003e000c94078030a1842e0342030758200f4010700e040340c0550322300141680000b41c0c0c00c0036110103c820700f520903000d00c049440305059400c1550088407103e144009040081c010800301e8050b072185001c412b00c00e264185100003405011034003500980301600940341180c61307150a0407620b08102042002224030100c459119505882ca00359103d1480020380d695800608080e41100f801a5000b4004501003071040042da42900700b01e4001500f040e0409071107072800c0e60f41d4030001708103034250701415030503000581c2c80d080654040e0812402c8000750229000e403d80441e50141c0109000342110a02072119250019540c00014400a024018104180411035003a4002d03800188a41c1c142005d2049042e01900880140075a8005e01c2c0d01c031800c0510b1051002c441074805102161540d0030b04c0e0301180000b81040880103d5506440441c50b903400f0742801c42d503003000050241555441a0b12443c0c0d41401050000c01007140154200341450540a4480c82041 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 342468543 1250 342467293 342467297
    0x50402150c16080a0302241302040e030a030516020c01360f0302090c0918060f13140105011107180b040f050612070614090a090603030203040e0702120a 67
    0x401c1c01c50201c80204000700c810b6455141a500c16a0b4908445a640203021801c40140c01003002520034000c41c503808032541518080c4405031074841454000f01103400c02c070140d81058440715449d6802008000030180d500c00c941d00002c0600d006640d020100d03110800307000854100707883d1307134200b82c0e031290403100030140d0a03480b12112107100030400801240d080c07200c40070415000c0700080d40701e806c000706030403a03000f030364409202ea03600d070300c251041e1180c6150076500400f86540f8000d81d81b50343c44200d0303001002400d881d0199000f4800600c20700c05031130792054002c0e1100380444030381410f03968080c018142800c2406071a0703841c9103034584802460180003c400703030302c84410f4100c074505e8100300d0105c40060420080b85c407040c910381000c5c0c80c048030103901030512100e0444003d44005040400c4601340e0f0350740e0346640144450072102c0e902c13201c00700e5442403480f400071540d10814030805d001140709800541d507462500396190a901c10007055401590030031011044001007400849032420194 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 342469793 1250 342468543 342468547
    0x3012414121015050a020d02070605040e100e09010213050915011d1509011b021e180c040e070503040308010312200f0c040204050d0b0919060507090905040215 70
    0x582c44281942c280340c0d101c80220f812036040d022107641c0180090499204c140d0a4a0741e5102542040e03a89400510900c0d0005000b040200b10085100704070035040b108800444019642e1448034107880c200075240207000b80d600080a0410000082034a0010300c401e80785c0090901e045a420340f248e460150781c8a06001401401400d8209a2003541260840040c0b041601c3c0040c0300a080e1103801807819a404500c0c501031880d0341c1000e0700180d50419500600c1a640d021640381480088166100c20a4000c0050100d980c0c5401068400ca44110a000812030b00d0364a00400141c5580c80a000282031250030018000401d0307001001c2419241c00450140000d01c00140444140c824504215031006114140d00c0840401160401410aa100c12140f003a031500007084100d10036440307040e9110303075080700c6c50001840d9100a16480f86524064a404510300b28100310709002c10001103c0303480c3e0b04c01c02c01c02c02c0c070b40000d8008050a1104010001031600b5030228a2107070500c0b80700b40c203030680 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 342471043 1250 342469793 342469801
    0xb1c0b060904150908030703060503030304150c260906060613090b061c05060a08070605031504110307020102070201081305031204020303091c0c15020d030e03040302060301241412 79
    0x43c1d40007194541154a0100440c00322424204050f42040d141b20000a00f80840000c047c5070000580b8040d6800c40a02d031100e01c039650302400201041c180c00d030188080035190030742815040b902c201520010112100b101d02c2c000d0b400c513040000c018041841290140f000c201c4a1483c45221b0f410388030f1002000564100180015295010700912064405000d40380f03034030102c585401050180b20152000003003581c40d414055294950743c095800066000c4c000200005c0c6490740501d00d00102400c0040c80c0a2540e814803042d510449a500241c2e4001842c00300f1542d110110b0343d80702c4500420445030701c100ea903d4944902c10311040c1030030342c8100070115042d5a0305204642c3c1041000704048100c0400b00000a10f2a00e592016242c1420030000002c8a0001c400200d10400c2c590b070250546110040050b030082003150501ea40342c0c40140804030040c0c0b0386c0c0c1e000714040d02c944890094020241c08074a00494006600b0100300507240d400c031032000e803090301681c041e01042010f242840c2e035 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 342472293 1250 342471043 342471053
    0x70207030f061409030a02010c11031e070b0424020a053109060302040e010212010e09010615030b13091203020c010209030105011403060906010f0b22090b1c0b060904 73
    0x102000d0780082503c090420720414510020082c0200d5401d83c00034004003224280036240803086007809e040681041020300204a030210543c00c00f500c1c04815103040a926884490121004031004c07500314401ca400104511800401031150104a0300305524000b030000f401071060003200a03088559541d1868400490184044000c00e030462071500c00c0510341d41c16071080039050601c8107074044d52810085159018041c021a140241407000d50b280a900e082d018001c5071500604910f0319560b0360b00042244003003e00103a2041d58260380215001c2880402c000902d81e25450000c00c40d490304030740b6000600d104840c80d00e8104103080042e250810a400341c0d001e072085a0500c1d030b244d4a080c0001c074031940d20200c1310b20030140640440310595161300c07441756106001c5c050a1014040c0c00d82c2041580b0000e4000e0101c0c41d5460b0003039100c0728909102c1303080d106064100000701d0b92960244541070804049144226040c0641d00344600d800303850300d03c5880340150600380664000303000036051007 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 342473543 1250 342472293 342472301
    0x40e0f091b01031d0706030c0518120f01090317070f02060a02130e1906051005030a0203070c0609050f0f0102040e180106120f0c050f03100b221a0603070207030f06 72
    0x5519140c000c0c4004803250138036403180500d010f0200170910b44001520350b0b61042040e944150419040511600191740c20450300d00000020007400b07110398401c1c65100e100a00400c111a44292034004031784140b0910f00000d0b18004040b0310400c8624551031101a0340081c4a54000900e2031005030741c1ca9078081244005003054015402d47e640550500a00315500c3c0d002c00c0108141060421815444000f00103c034100c3e90760321030002d00240080744444141e54021500015203007020103a096040da5158203903100b00340c0c20790741a085145000360003e004e014040300400300000031442c003424140205202603015282e0800001440d07024040309000f5800100034085901c4c205154110070314042c0070f200130400085901c0d400c1c0340c2000a09040c5081d03021860140240a0004040e031070071880001d04240040a0f0f000c0c1d45022a0304452540302080d5244010003000481c546440c22650014490308a00d0280508000c10400610ba42d01041320001c0d01c0c0d00c400102000d14007801c0450140c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 342474793 1250 342473543 342473561
    0x207201003320a0b1c0b0a200903060f130f0804090608031c021213151826040e071101051003030810030206030c0a0903080a020102040e0f091b0103 65
    0x3004401e50300a8074803012040c1a4850228090203000215203101400020b103400b00800d2100d1707640402510009898406203a840b0741c0e0304200056000065280d000c101c51200b0704034100d030341f00041c030b0700041c102071244c20340c403d031840ca00b040642440c00780416031100c0018054407004012000c2001c00031a2403c46000b800c01d00d805114894481103507580f030f540925441c08040b821a941104201001d0080c1d94446850540c400c07103a030f4401e21101c0e45c6080f5500201c440404109400c410b65090340700d2040e001c0d070848420300883c8424648841c8114008040703251018002c2d2200341d440e00403038211004e9403180504100191031310f000944007030000007002d00b901d50819003040520580600c0c01b6080f6402a0703070384041c80c1c640c10030b10b40c24107640740030180d04224200001202a500000240052841482c082c407200c1d81d079031188170440d0480710300c040040c1d4000070200461204480200d400075500348068a950600c005507035a18103a8150004101074403070405442c1c0e03800b980c84a810 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 342476043 1250 342474793 342474851
    0x30f09080a020d0f0306080c040e0c0301050c030106031a03030406030903050c122110091a0316050909030a080a05060d081303031206080705151c0207201003 69
    0x2640381c4000040d440718036160801d070015110150380b80c1d90510138013465007120003103000340030702e40240024407001d0401c08422040d180b16400c6180700c182c81c01d21400e4891a010310000d0b840e9410561700405540c90044000b008031200500c00c1070990b030200854003203980e541030001d0078131420700d015a980e0180d030428401034058402003884081d0711400510090306202d01000f4041c50465800000c4c4206441c0c000004503e00d005009840383c80d4090714410054041c1212a0100e00c800640780c42200746074100c18407410344017000070342020341c1c21039080312000000d0750070400503d50040051070028030221610f621040070030001c0d10307098100e480040c1c00400241d41c9211031410f145100b42284401ca00181100b90381850303d400e24424101942c071018003802c80c0510704070400c00c00b824011f01c4203c0c4c1e4481000080441d14182d002c08107007000c80030026890307980d241800380341004881c5051f0b01c91030362071182c41020342d0b80c46903001e4820030908000452035100d20054490010340100c03080 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 342477293 1250 342476043 342476047
    0x513150302060706020711100e010f12020406050d0e010b2b12030b180106140d0e07060c03090801051902160b07120b030f030a050c03090406030b0723030601030f0908 73
    0x62104c01d80081060034010041124140007040903c00350940810291000941041c1c440360258482c11600080100d43d2401e02220700400410800f280e1050b030150020030710000e402440786003036009011981b4040c2e0001c01c4041c0240300070454001201c20090203034000d500b255404203440c805840c801035040482c0e545000e0003068080c0c0207100c840006485030b011030090b003442502060340c40e816104250348215900c05008010292500007004404d0010303265142e802d00c1603c00c02114005003865916510208071a05001e8105a02e9410954280c0d0404080240410841700e90340d01c203c20901780141c0e5151a403c108401425100c0c00801d0b5950348800e10101952104c41e040e01d0740c040000c2004566000800c0654440301c0500d29507041d0010700402c90510302900c06085640040380c1070300d1070300f04070400250494803250400c950080005042c0401e0700d6007c01d1010000c800001101c04211004a40c100f035800f004042e24100b58a88031111003101841d000042281c2c1d010314195 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 342478543 1250 342477293 342477307
    0x60905070309030e0a051f03232d01050f0607050109030e12010203090a03080709120303060603050702030c0c12070b0f03011401021504060c110d020601080d0207051315030206 77
    0x1009820492003d4001034592207680d400740c5088581181107420003000348048480c40301141545216088402050559403034103c45152035030b500d01181e1103020603075890b41786071204c0c406139284602d11010305440340d4080100504020b03204d801d03066030812684000220540b800141085c882d142c001446035091900380302c20960400d032840b0700c2c03080407900143c05091750502d0b03030700301d000860f5501000d0b4030110a410100740a030341450f4220b8207914211440c99185c402c0c801c08019007075030842c0001c2d5101410001c1c554140300d41c0341c02440e00d01c05549011200c441a583e80c10000d4142881800000f030700b01e0022004004000060419005d820b443d08035405840100b0b410034458900c50013402d41b8840754661003c140740070307605c0f440d40b0141140d80300c1e912007000038110342c1d0360303107041c4108150220807442041104e20407106007680140070741d40c184010315040c50310240724203041d50f2060f14107201d01e650700348541c08007403000e040c001813a00a441e83d4000811040d0701c003a4010b8400030f654 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 342479793 1250 342478543 342478547
    0x6040305100902011e0203040b0c150f070e0907080a05090c13020405030d03020301180203040213020c0307120912060f18050a1205030606030c030403020f07120506010b0301030c0b0d06090507 84
    0xb800118002d8032500380d00700d0250300c0c08018104803401140140c000700030a0148640d002c02505d100348110382102c0a46980d0f070581c1e400b81c2003e80f01e4945040d0480308200006500c03d034041030800f010341d1440900e04100002405244014040d0800365854000184035404200014481910014135451140e0303205240d80f030003581b003130140901074016602081d00150290080303074108d0700e005a16000124422031124029000944102e81c011a850080d820004050024000d00307010100915035410700c40c60409000000f06003100305004111200308a44070880900c5022150018008608141300300309960044c00c0c03080a210030607101d0f042960a102000545130806440340110345c00240792013905480038042182c6084e03114030204001610015070034003451700640f0900440c6e40c0d040200c1001410300f04140c10a041d080380f840c0c17441040c0901000b000f070040c0068a01c1b41e103554159128218212424001e80102c1703000001c03211140d610990000b4000d1550b28410000c50512602c0 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 342481043 1250 342479793 342479801
    0x3080408090d0b0132012a020301090605340302090102250e010f050a35010c090b0315190f030602040f15120c050c060903030601020f06040f0206090604030510 70
    0x82026802d00034441c1d5600900550707141e415010140c50314403080c041c200c4240300440307c00c00c1125485400b9a030200c01a24240103080304244070f182c0205240c40e00e601072501900381409618004000c04095080e00d842843c00704a440c25540340150f034404103000142e142011002a1030001c0581c0701ca0f9104504010190030140ea540c1c8078800b0441c2d03030b2048060f600c5105800f6603580129079050410036801046c82c00302012401041420b02d00076483d0340c01c0804140c8040b581c5869454010441070f01754000c442a000e008490380180c10360600e0304424504c842c82e810340c24041c1c81d42b810340446c145d22040c0983c000b40b002e802c0840c103903a1a0718011000c0e4205101d180603030008020b02191a08601d00d9140313080c1c440740e48625080c1201d44840c3e010b0400301a0b554107000c1d04001c103801000c01803110328450a00c40e00110390383c2c244200028540345048501c1a5180c000509020007d400f0020300c1d4485034040360400d0312400308000280e03e030700c2140d000400c58420280110004941900 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 342482293 1250 342481043 342481079
    0x118030b150f1f1d0d03020a0204150f03141203040c03060b0609010f080601050c010204060203041418010603020c1609090332070c05041514060703080408090d0b01 72
    0x7400b03490038400754180300f00c918403003000d01940c44800b4140d04400d07208100c414149180340c4000f80700480e014000c070f40c4841d01d003001600160054100c610950a01d4000c41000402c9041c400c14540e01d000c01c17850291003c0e01006100003002c142d04014000d0070024240c150700b45641a07640c9040ca031401118011041c80110380c401e05010040000b880c0800c01e484140a043e121086400120745080b07800c800000c22090500c9410700911000820900c0500007401068005640d154280544000c42000e440701483c4a01c4601c9c8456150040c45104241102c44038180036844010f02c3c245641491500c5961400d00582980d0002c1c844a103504081c0c0c1d03444c020b0312a200035913004910080c401c60020300c0c600c43d41410304e51040c3c01c111000300070010b00e402104400495505c601c000740643d440b0038228240c218443d2001c0c0000052030111409083e001c07140b49240840315500078044010081000d0034030350303021a10030015181c0415801c100d943c04806c00c90f45686500450303200c150202c03 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 342483543 1250 342482293 342482299
    0x120106080a0b010203031306152c01090209010203070807060207020603190b01140a0f0c080a08070801090212010506032701061703030f0f060102030c0f0d030b030d0e0118030b15 78
    0x458444070b9500110803203005505400c00c240e83c1c008161640e0f0007400c1c58184d00301d40000b090000141f401d100f000fa405140e9040c1d06a0038200c0b8403240d080d40042d8040c2c01070040d0306e00c10010480960303000012503591070b9221b141d030b030380700d98140c1050301c0240507410700079400040000070030110060086a0b407d40000a00c410800c4084d0a001100c0b88001c00581c6a9441360401014040b14050045d24003068211714040042c1c0911769900034603904070f40c05142c0400ca022050150154000008901406489074114100321100c00910000141803081e58050b82000001c9000841c9601450104400b59211081003100b90912240200b90341d00c90200210015503d04c400000e02004070385c0609030038100381c969600c2d040b01260f0300c4400500200e05600c01000340c0400502c00b80081414008404080d041c001ca81a070042c0c03e40c1c554a044900c01c0d00100018400709170003288000c0c0b610401e2800c48804100084840e2604000d80c0007e455982040d080100e0707a030012419259102e026 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 342484793 1250 342483543 342483551
    0xa050303030103240c120501080d0e060306060705030d1d1c0818030703080118060b090f0301020c0604030e180c190315080a0c08070602060f061912050d090503120708120106080a 78
    0x103407100d645450420ac06080046e20050300240a480c0c00009560041d10017421289440030a40e502441e5521188000041545460505c0403070843c005d05030f89010000c0014000f150502c44803521140d000070703c80e100348403030000800d044400c4021040c000b003120808a039601d88550030701510404007403180b19440116032000e183c42540e54020281194652030115080c040d0302c40400c00329001201605d9090342d801c1c403484406000800900c3d000d14001c0d19606070480f0541d00f03000403c88160410403042002105021310a007242d011505090300e450a05001c0c074110800032406860100c03000c0300000d0790018007080028002c80d4140d88288141481c20500799a00031080c2c48a4a620800015130081000140440100d208160380508001c0089048442144d002c20002e115078104529411801c5d09040c20483c0420100004010700d0802c0d0a01502d804002591507030000c40402c01440040344071410080c0c0001619011500b82c08422650740e143c0034024040300c011120084201d0030 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 342486043 1250 342484793 342484799
    0x5090a0e010b040b0d140a08040e0910020306010c0b07180b0d0e0d020a0f1119030515011412011d0d0f03140609090a0b07020d030b0a050303030103240c120501 70
    0x4540300d51913190201418006107030400383c551500e2001c0b10480015180625100000081c6030a00104060714014207102160304200300c0c054641000c01c04603400c098810401d02049a030011079070109164006007940c41560b510004a0f0966421070b50312030001002a80440c440001d18007030440e030300c2035080030441e100e04442200e940c0c02c64145e8003805600031601e6400403c105000130b40c00c050103840b072080003036442004152601000e0343c01007580c183c0d840d010f108000c02440003500065a4442040d44e80d418464a64030007940032503414842c07140d40c1c000d01a005002e40141d20074480045029220199820403c2e88600b41990500c00049600340d01c0c95095000f0f1142840d02c2d00000c4070802140d5502060000c0004090720030403891003041d041000141294200c640700301101c1d0b019040703100010a0141c150f4040c440814840c6041034400e00c0292070010981e411a608624100c0034019000c0c0301c0c4c0302003081c52101e20601820441e45000b01500090f83c080c00c803404039020800caa036 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 342487293 1250 342486043 342486049
    0x90b15012d2706050406080601081e060d05161d07050a0c03090509070309031d060315010509031b01090e0c031b0d090f1226040c05090a0e010b 63
    0x30009459000084540c000c0300c0aa124030580d07415025009440c11802c0414901100b02d00c12a80c0302c40d0000344000340078098507a02c044129040304080c2011101405d109009600056000340c0000c20300d035407a40014860ba4544040240340c039000030550f02013420f0014030b01869401401644401c501c51004a1704020001c1940e0303107e40314668805042058a007000c031001b0710ac4403001d500300301059030085155038850030810300031801510001084d490754503000c0c00ea040c0c8821100d0303034031b05c3d840022071898403010102ca9120740c0d001041e04001c0c003007000503107241c011450b22603014030a8585d1101140a028005044c41c2001d0700e84031704150b81c2c1c6000034031001080314841c003810001d2011629242031000550340c10001102d03141c3c2444403034480b41c0c0440f10b0354442561110841c1303a083c010700c541c0034403450808000c0c0c605200030440041c000190b2005034070700c0030382846103400010b041c40100300b40742025040c004c01d2001c3c6402c00100f02e401a2950f00c00d1500c4d1546803443d140e82c540f07 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 342488543 1250 342487293 342487337
    0x191212020a0302071a0403020901060201050702060105040e0a0201030b0415030506010314010911010e120d2a0210050c0307051c0f3f0e030a08010e01060801050d0303090b1501 77
    0xd626500600005040075480c01c4400210070818031794440c24070003c03006980d030103c824082c0078141d0002a1514106800a10744001a400540110710b0110841403008000c114600442d40a080c0490342440c000003040c024103003840802140b50f00c2190120800074081410b034101d034000c0d900740c0c550414013000c190032035084c034800074848405241070030700719401a4004680c400d00240310b20710031072104c05c0c628100007002c07401d42c00003545c028900c1003988152107160110206a56000308001c0aa80442c500107040c103416010310402152a140706c1004004807508541d01005071650070924684c0c5a1074200d40e00c13990070200b5110991808482d100b0482c2c00806801c400c801500000c504540444e43d0070103046441501b420f640c550b2110805500510031501030600c000c0d9134840c90b01c40300a01e094410f070400e2105008100041019a901c035260034190341c0121041c0c4e100f0130291406a008151100c0000c05101d5400100107407010400409010014284c0302c020141c100400200880c0d = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 342489793 1250 342488543 342488563
    0x1d07030203010e1602010b030d030615110d0810080703110109090209030c0915190503060c0c0c01140705011e051003080712030e070b0a0315121119121202 68
    0x140f1a10f200003000344450300301145106849000005e2000c0c7c03c040402e04101d07007200c0c2c3c440406d441e00c0c0100441c409142d903003458100e003031504d4517002010462203501c4040036030401c01000b0006000c504c507072110b240500000c21150045903200e507900d1806900101450b840c890102c2c10000000400315028000c40c5c00301c010080291a490622004005500e4009800da0070320303505e880c45820b0303540c4880c04210b000750380103025a018076140104151404000800880080500748590705031142d00007a13800c42e0200c24240b49034210310100c8540340a00840741e01030125130a1624215229108035080c0030386410004003440a075541c10780003042a00d2520008100107410080640422a102080b010a0520703103000300d40c0b210310361a4946858015040345450040001c1c540101503014821160315a041e205440032180c41e212000499217603404015061034004406411541d031103200e403c0c880b01003488262800c9403a000b02d0f007180700d006403088950040034841c0300c40300c0380006804252 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 342491043 1250 342489793 342489809
    0xd11030106052704030509030a0c0311040603030f050f07080a08041406011a0714010608060a0501090b0d060f110a0f09120f02120a0b130203010b0f1f0c020402041d0703020301 77
    0x40c0c0b41c100e550f040b0380018425000c100c4117101601d070310354040c0207904c80c450244080c080c040e411070070810b240c00c0b08041424071482c035044003000000d8014440c07110560550802603100d0800307030b60910340343c82a8140104210000610026040e0b000381d8124061801001041d207046000000075540300c0702070140c0c4200c583c1d0b24448510b04d00340e00d0000d281d598840c102c85400144d01c44001c45c25500e1682141c075158125400700030001c13000d44a02401006880c405104801c8201d01151400e40c5260010b0000c0391640c118030914030403500000c00d40040e0680e01d030358400700044000c200110a1800000007401000300003141c12240508444542d04050082c900207065800c00400040e005060a9540034003140400440d51813100ea511035110b2410200300300042c0d00c10107007140d002c60003c2d446060b0040e1a50300c83d07140d40944054039001c04062901c00c94266405641c90300048034001e50083c0000340c08118408240e0349003034480280003000141740c607140000c0d0f041c1e0109014481c4 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 342492293 1250 342491043 342491089
    0x9060106090506070201021005010b030711011e09020409120806030d140426152203021b0f0a08010e010c0504030807030c021314090613030207030b04110d1103010605 73
    0x580b0b0f24074010640b180c4140129001d201c402108801035a00990108401120100410880c0d94201000d50310440411000304035030800d14914030210b00c1c0302c500b103004643e51034400c3d80c00c64841e940220b11850300075500705003641080c030000340044011507000d4064000c429401c2e080324010702860000441d4562007504060400700403562441800100500506200311100e1110505004a01007800222400c080314904405100710040038444c40007540c1030403501039800710394003040780c1102d0346103e135803000341340b00d80360014841c440c10094031580000c610500040742c1c941584065000ca010f50002e001040b02c014058685002c4c501c0003a182400c10044480000e03c50f005100b038584c03000300500c000400e4081c000e01107407104010300c0300340b0800c003051004c420020095a81d00c114051400300d0400800d0742e00070b4680704d141c40010142c50040c0c0120303040144000740c0d40302c402406040d810703510182e41444e01d051003c4141050195107443d00c081940d003881907402e8040f0704241c00c422 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 342493543 1250 342492293 342492299
    0x2122715040503040f0b04060e09010b0d0b031e16090e03070b0714071101020f060105060d020c01020d020a09090606081e06040b0402191704020a0e041113050405060906010609 77
    0x103405503402802280e0034001048082044a2001420300107010544440707901d46090100142c8501c1c07a40d030440d40708010600c01000181000c4003100c00c0319051a102259030240403021030315140100b000302d40e540441e40c07608120900b000075103a5480000c14005045503039982c1700581204c1c402600252160010401e6202141c02040d01c19046140d40c900303c5003c10021303540407055001907404892440761822040b102c2c0d0b0341004800a140c0b02c0d48064000e5524000003c1d10314030485171204101c54001c14180c0382040294140c40f800c604422044d0744d1401b069500801744e141340c3c0a9107000c0792610f18041403052040d0320051041200500300013802180e000341d800355030310085c03145a0103910b550b142c5180e0340704c9001524410444018500150404c00750280161503501f0410039a0014403041101681d20052450100e40784c034500c00000c2d8072281000c2d031080203054021900021000003d003e0490182d00140c400c41c0108250b5841e600c42c0881162030350000c0c869003001030b40310f030030074 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 342494793 1250 342493543 342493573
    0x1c051f031b0312080405060a0b0a090906140f090d1119050c1815060c0c01050903031b0601050901090b0f010f110f010e0c01021513020a09021227 64
    0x9403612034280210700700710a81d00c0c0e845000c100400403514001840100920003000070400540d40c100c40d20b0001440b031307000f400000c00c00f0b841d281c0c4500300f65141c03120424424091a6030081145008015000000380741c0701020301198082512881c1c81d502c00d44043c0000c0310320601034075190700c69139000341c41044081d00d2108080700d010001641c03035010302c2113000000d59880c0700005d14031010080c060102d00c1c044140d5444070308008170030381c0125130403c050780000d40d000c20074001c94042400c1c11621103c0c0324001c00d103035000d00ba0340500b912194014a5802d424005106412600c08440324180c3d0b03030b00c075020401610192480507401004c0c03444880380c00d42c0110400b020070485443c1101c850705100003058605109007441010503591411024020a82482880103100080c0001c1151410340218902d550900500c25145461103007000c8045550f0045040020300d0013080035907c90040410b6100660b4041e0b413030300030640c2c980340c02e80440020114844070b107002113806020340300720300e18903 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 342496043 1250 342494793 342494813
    0x70c060503151c1202150402040c02190f051603080d0504050c041d1b0a090e0304030602180f011103070305030c070c031a06010815040c0c05031c051f03 67
    0x500c0340c10030004207940c0460711290882550035180c050300714540d2000b4103040c4a03424822010788119009281203002140316520580e400c0323030741520005030a00020100f28101104003a007461340c01d10032940c80e0103124030200d0003400180540e042e2100341d10a5540c04060b00800c0c480104039101c00c0c04007112410440c0e00141d0700500603015500043c1c1c40c540010219031020f04a5915190301d20495481880704100030340c034000400307240c104400c2c0c200d400200f8100752840380400c0f140c0c4030503100d1703410030052041d40d00031648000300b51344600c4600107080780074901b070b801c0c5409210f91400c0c1c60030541c404d401d155094070320350005c4d6103080065101150107520080a400c02000d042240344001000d04032030030002c50044041000c1480010203412aa15014204604103c2201c00b84440e0400070030115040c2d02c011540001c0c0d8040100040e40d41440340302000c1d000c1d020110b00b00c1070005c0690a11021581c04900810a48e41c80407950020b2898506441055044400c001d100180070645 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 342497293 1250 342496043 342496051
    0x309020103111615110913090c06050a020c01020624010318050d08150a09050601020a0c030309090b0a0308040902031017010c140a08042301020408060103020f06070c060503 76
    0x500802c0b20141da0035080d1680c0d01900306101c0d11400b9440344000d0002101c4540f100810038101400260b01c50540d400c014002c4c0344800d8810b0300da036014203c0034000c0354091000550702010103101c440c3c1d561400380998000c44081d5001d8025401d103541c0e0b540c030101b0040c2c841c0c52507200c0b0790080c040348100b00e0f0880100c08526410b141e03036001ca103500382018681071003105110308000c0990788038450000303082c0391b0045d110400c012046011500180d541c2c100001c01e45039091030000c0e11343c0d56100100c7c80d022942c01c0161039080201c8000c01410f9002075031000b92400244140b0520318030760240b100f1580c6501c03000d010194140000e00941c00507400441d00701001748000d494650322890400c1c40950b0f0908601100da554003007282210b900858078100300c0d50301040c1b803030800c540d034900901100d600901c0181031040645400d42040d5803032541d079503003241200c021501c450700c03240707415501d200030700040c0d21620400200c00c01a1400c10101e50700c40d0b900c0b6202205a501c0d048080e1081e41000e0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 342498543 1250 342497293 342497297
    0x3070e01030b100f080610060c172b0c0f261e041203050606040b040b031302121b090114010f03150608010806090d12050a02160503070606050603100b0c0a061503030f020309090703090201 82
    0x80040c2c2c2fa10280e45c50b40c03010503500c0000002d950400c250307010b001c1804074814003041c00341c00e5400707208074146024885030100c140c207090740781941e030b140c5200d490710b140c102003840445408c010702050010f001981410b02107030b0744040209803902d80c2044443d0140b44213050340c1d604100000e0180e404e03030f60082c682001e50001c081f4115851a030000e14001030300b220300aa10752040c1e5890781d01078484640f003002c1ca4002d0fa2648450350409010308000e507241c0441310b06016075001d0082c80c0310712907030000210b05c0f034003241c80840304c0c0c4074607006090440a00c504141c0f4415100032556a15010400100c201707481c0d1928041c0c40200708203c3c01603d001086907140070fa003409064410038281078840c682074402d9000d1580c07503455103403090440300c40c0d0b0405030141d5001d1040202080d041c2010f1826550006a1380382c0b24481e1f010020310f4000c800c3c000401030740c2402c8004000ea2034099000c020b0f28401c5d10350114814202104982c0d1380102c00c81c0e160b1105d054000b01d2000b50007a40024126030040c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 342499793 1250 342498543 342498577
    0x10030b030a0503040b131e1211041a03120313140a170316090b09011817150c18012105010b0a0e03070e01030b100f080610060c17 57
    0x54071182c3c11608940e0182c080800c000850980307507a07645100340003038416659561012411803101c03450000301c0c1d004600c081c03e0104403000a10010003000c944809008000b0b015100c184c440800d03240d400401d040e17000f032203012040d100152080701504d00c25181c0d1801034038005c215864160415141100b40491401040300c0007010a9129034001e03520201100b000f0398038100740b4651581d0781181c0c41504100900c2c910140002c180140031500c00305e40903c0d00031907a10f0460005514130324950301c42c0305400003a00c2603141440340410490410150325140e940b40d6543c1e10050812841150356039000705141c030901000e0b40d07002d90214403280300240038102814100112002c1150401e0b040fa03130b44000003081c2400c40aa00c801d684801c000107401070b142103450306a8000b5500c1381030200900c404481c10004086180d0000c500700200444042d41450980d50203405440d42002c2c1d1321442145100c500115079540501021410194001e2540b040b0300c1e4a2940440290400d1003000820000 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 342501043 1250 342499793 342499813
    0x20306060915071703040c06020c031b030304080102071101031116080d180615060201060608180313060305190207030509041104050406141e0a12150f09060507080610030b03 76
    0x101c90303144e210000701c9442c15541c1c1010708008200c64015030102c02154008a04c5007003580700032403040350407000c000c107101ea44ca02c5031001070300354001d98103e24020741c40458018103011080c3d42e2182c40300400e890411001801360b01d254101d2064482844150340303410b0301f40000075200710041c070800e44200070026060710241d0341e6140d80d0f018007209441c099103c9040b01ca0350640100f0280c020301d01800200000d0b450a1005828200024411460180d5100304401802e1003401100c1d2036500e08d200080159480b56070107001040c061b238026410300d4140b4040704544200d03100f180c4200d41c1584440b818110a03900b044040c091210001b14100030034880080d40c3e49860080001510510070100090007410081c4130038030400700780c0c140003440e51040e40c400300e031030b45041c0d20241d034a110500d45203405103040c00d2224210000650601c2480c01c041c3d0600c1219650000307041030310400c0180140d46640b10201d882c0502614040d5000c0701e03441310308071414000d6104001040000d802e03541c0b2542c03 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 342502293 1250 342501043 342501053
    0x3010905031e0f04081b010f02070501080c1318110f1210090204090914010b0a0e040804032111070501020712061503051606210203091f061802030606091507 69
    0x40382d840410180d100050b07802441b28864505e40d01d09070207181840e549584040001d5654040744541c0307060001960125050610150840d07007800b541080c0c16880c00d03a80c400030552025144916955a454111006041d4801c0c01c2260b10f41d480d603101d0305082c10340001d1100d02e1254080c12480081c15a940000394080c2c2c280068801006507110001e443c070550305180c0e018840c0b007041007529914084800180d95a00c541c440d064986480600e51955110314140f22284140e40002d803481b4062a040304980080e000d03503d141030720780e90342c0190011900c040a56500c80038003407540035070003208081c00700f514842c014490142c01014081381003070791103900d02001c0307400c1d800a0301e094000102e0305c030306101d0b801c4042c4001c020340d00e81118092800c4803501da16400c00348540d02207903000404541102000c2140d61400507401204054142c003001c02c003401008103100c0d03010340300c001e0b41c0800c2c8401002d200b980e1040b2006403065141c2001d04040010f104801c5400d4549c9a9080c440800820 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 342503543 1250 342502293 342502297
    0x90b18010e030d020c0a0b0301051c030203070501050406061409070e12030702040f021e0415140d141b090a090e16090209150f0a0e0406211103010905031e0f 69
    0x30f6059000744c60758449950902070101c44da60001900c10a0810041007143c950a0450b6001c0d660f904203142c0583c1e40d45422030a42c440e00d00040c100790300380405d12083c806558480300c1110020314403003403c0310011050001c068000c40381c04005c2407010141d501282010401884d81c0d0002c4000c0e286051000e600240884140c8001068042d9020820201c14241c0a81c3d03100d141510285680c109898111447e4041503000180340401c9005000e0740d1800f4207a0b02918041c03800c020302801140000140800654401c50b40d103404541101044440d108081086690f07a200140c080342c8442d042009040103004901c1e5100140c1c45940d10002d1640050384880313000e0b00304050b003d80c1ea20320000410180e25140380c01011280c004202c64003918406904682c03e02c5031a05140150141060002d401818585d028810a65074055810600070f4a58200e02c49148149031199a200d2580d090500b20f4120b800c0080551303100f000b28410b00390084102c06011500c2616251901015980041d52030f = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 342504793 1250 342503543 342503563
    0x5070e06090f1515070503040f08071505070c030b0c0309060c04080d0c020a080f03030103051b100e030c03010c030c110607090326070c0e0f060120010f05040f0b07090b18010e03 78
    0xd1f000410103010102c40450080000c000484c0104840f9082240b20008544401e4110045c4180080c1107000c0101c040a841c0065400542844403498542e0982e941d591081320b01e00038034040e1300005103200a0b55400d94050300c08050040c41d4011303009405076640c0c4d91484099900c010790000c0098801410070039103028145080255072254911f1404500d407a1000ca071010380030090b0600c018480d01c580c9620035120f00f15283c001061998200400d081c10082a000340c1c05500f81603610584030f805400841d085030700d913a01e05d450190101c10081c1c848074155041d400081041c6810000729560b00326174103408000b800e942c2c040009802040c0000d80c06000c08407400c0c1c8400c0c1d0f041055441500c6500d13407001041070000201d14280b0300081004050740ca52282720013014180c3c1c503855000350b20411011074a41405c1141c0c0c00c03e400c0c0a4801a00d00204403815045174000441c1c0c8c611414200048400721429031b401c1801c60080c00300c0f02c982100ca0300781081603104112403d658204154009 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 342506043 1250 342504793 342504803
    0x501050103110307090e030f21102c0a02071506030c0f1409010303050a0201090c1e06050c060f0a09020315010303020c100e060703091205070e06090f151507 69
    0x181c00001c0b018142010b80d40d82c44460310603d8200420100b10010040f00e000540584c072a03682c0d560350a9014190100c0240003000d9025080c041000503414903040c2d400b9a660001054001c01001e01010546204500c0d110755000c00311011400030f8000b82c020700f00c810f1082c507200110388944c04100c02194115132003560040e08c1d050040104007001822003000d07001825014056941d0300010644449041c0300082c100100002c00c1525540300f0741c44501c0700d940c040d203110000c1c1e9940a0000c290741e10100104882c00241c00002480b80c00343e0100c40c40740c100640a041c03250b5a80d8900b10100318001c0a0091890b1121b1102d0016a401e000c0d400c1480c010a2101500e5410342c10024940b03813003021218010740c1c103480700c40b0450307400c0301141c2e84d4900221344085e50b4861906d401c65402e0620391203400110304000078807007000b2000ca0744009803800e505401486549a50401404c0103080d28150ba040e0502004109070010039540380b18420409080071400204864840005500c2a901660 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 342507293 1250 342506043 342506063
    0x6020304020913050c151309061502161403010b0a1d06041104030807080f0a0507030305130f08070203070512010204090509060f0f13080703030b0316030b06120102070501050103 78
    0x4210315006140c65000900ea00c0c00e900d5003c050f5a03a9640c4580e0b0390b101034811440260b21407000e8a004084503001980c1c03090f200519a5610b000102078211401035801c08141e40001944c0140300041e00c22112580220414000b03107801c501403100e000000300e60707415540f641040101500c994006000401c00a15004020241203241c52208500500903500ca0340c00c0c403180c411545a200309450540c0d0b040382b40f280e55a401c6140c00180c9200741518511282001b00b521012150494007428106000b5201806035030f6a2050507540710804860040c5404085103181d4003144941d000b41002030b10207001c40b90015228030000e51a15021160302280340c0d00080c1c2404003110501480c1e030400b002360020042410b240001940151005200803006d50500b00050210107641072201f103010b421005080c0d4901050500030050042c0d030762154003900c26511219455a407005103441160340101d400b030b8250701c0780c81c104022000c4050484c0d603550340900c40840410002e00c02c09000b188100c0c100c5c2 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 342508543 1250 342507293 342507301
    0xc04050709051819020a090314070e150307380408191505130b07050304062a03020306040b040e01140c190311040e24040b0a03110607020d060203 64
    0x2001005040b0501409400000f040c0843c86103800750340c540c005285040540c4034030081d8000c0b40c14620030740c0041c14031500702e840306e20ba603d004a107071710076240343e4031042d621680c2e5455605003100c403500309160184d000000070450701030100000703c0d000c040306111340c58480514148061008030000300c0d04440ca0006000c2014000410241c1c08008003110040703500030541e100c510050b041d02282169903520b031000a50703a4200f5035a0b00209503401510311034581007160005045400840b0119980d40c5460200e100e15240da003d461a007200c54520303810395913600003080380650070150459030496102c0003c0790b1241e40302d004001c0700b42810b2000003130014039074030f440024000103440ba0b855407100300064002136031480800c2c00401c04905000c20303a5078803001c4020440c481c9502c4241003401d050280030541031243e40c0301c40da444125030f500705424103c9041004841405011035172100c030b4a141003000540a0901034043d0400402d59404c010340d940226400d80042a03080784c1e584c3d4000104 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 342509793 1250 342508543 342508549
    0x1b0b0a020f0c040905030f030603030c060703090c0609080604021318060e0111130b07020a0302100503240a060e1201023402060f030612031b19031b03020c0405070905 73
    0x40b80320350b0080b20244841e1003103131550390300d030700c508a1485000d003000000a0002c3d24200704803011460700d40304596a13440c000707200400070b010020f003c462296214500280c140c1c46803e450f030a49036030501814054a4550802003910101e500110010351100311b464100c98514140395113150103401d010821110318004907003150052030000850100510543c0341550354016040151005030304010303500c54050000840402d0f142e80029407002e4180d0070010125408405107024040e60000c00404100a0744124000c00111080c10381180034400c040240e1072013003036030b40d400e12005880b074440c0c10b40200740242640c2c88111442c0c030741407031a640800381c2030039407204001141517654910b00422166001801ca0310485d00002003442004c00400d000769580f80f200100b0081c29021640c0c0c03103100c80d0300c89164030101e4001009901418080c034440b48000b100d9004219456501d80d1180c000c0c1180c00700c480100414141c045115040040906e0f44445c0320356406610b00313441d40201c2c1c034508410 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 342511043 1250 342509793 342509803
    0x909070303090e090a170d0f0204030b0f0408090d03090b04031a010602160603090228181a010809071203020303010509060301090c0509130b0f06040c0503010609031b0b0a020f 77
    0x822071800142608000310080e010172401c2c03100f58400e8803042140381428028502c0e01a056084140e0342c81c01080c0700b43c009440e07004100300c0e481000c2c410016520031000d48859001100c0191514108000b160f0407464205604003400b4030900780f204451b5281d1108508681240d0022a40b440801241c03040000d16801041c5c01081c0c9803000701080280c90302050038080d401d2040400b0b15444502a030301719075452000f101da41000ba80300004051915100041e480c169104020494555806241c4080600e004020103141007900500301c28104500447d807c0340018110071150048890100d01c407403c0090410034039009900568503941000c04014056001811140c4240c2c5482110400034400421f06001c461040f624041c05036580c03a14128444414030004022580c07041c00c00c1a00d880d02610309000700701c140c8040101a090001c20b654920080c01501c0c04140b00e00010070004244094018014040035400c1500c00e0707581a09019580105201e900541c02503011028403541c1001 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 342512293 1250 342511043 342511049
    0x11060f0c040f0b0a17010b0904020d060e13020f030c010503130206040b030a090b071e0e0a051203030114060403050601120302030d0c0807080601031a09091203070f0801080111030c18090907030309 86
    0x10000100d5144c0b0047d1b8840d44240c0314140c0c0110340103d9000c0c5601c0c9e40e40e200707400134680003100e94001c0c038000c0344410002e0b401c100101d108544056900c1024200001d00807001041070719042c1c5152603804284012042c540c400301e034002d070100070200c0e800c0a14405140624048100484c1d02c2000d85402c40842400030321341e100b0814101d08012843c02e880000700c004586c10706080e0b82c008440d4002c925843d034960007060304155058498420030f05c0000085041b43d03100003c0c242d0644444040160510684c840a0700e40d510000c014043e141c0922100b403041c91003801128500b40c001c10860080d243c0c40b06580300402c0a00d001c0020450b0043c1a165010a0900e000c002110724916007c030100251000d80740151001c0c00012003680742001140000c1b859020080d490f450800380007030941c80c5008800f00050560800043e10403414020204040303a07a04240e81143c1e80c0e450205469000318072a0300c0c400311105e80400150f22001070040c02005068094000d030381c00e40c1006052030743e00d80c0c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 342513543 1250 342512293 342512327
    0x606091403190303090203070e07050c01110a050f0a03200901080f0f01090e0f06010e1906060504051005070c03050c181015020703050d0507021011060f0c040f0b0a 72
    0x24442c144034070010048040030340c1802e0000703840c2d03282d0000c01c1c600816a0411284000c545051100071604807010300703901c1445400a000d02103003140c1008681c095284170a010031024400b0031640300c0e81e80080c0c4415905882c0015000180440b09400300c0c10f034031540b104044002401c0d01c40ea5030b00c0640740d940441003441550b89403c040e030048400030014490070074402c0c2d5800a052100d82e081c03009031180b8014004844480d40c481541400a0703606441d45400c106000121010740202406110202c3c0c42a4540d181031901e03140901420240001505007000b03002c01c10040046e6010f980e0101031405070004108803144001031190a420041c200c500d698640740410454800009035002650b40084900241580100c01640740a14a4200070301c00e0007a2070710f420301c2d40c1c0d00002400e0614005c50b07040041030002c0c442070b919428441e244c444590455400901804148108641c0200c0810902072170203a50b0009040c990446822010000c40c0000e040e40465030321602c0b19003448420 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 342514793 1250 342513543 342513553
    0x140c1204060e031501031403070203031b0c0d0b0a020a03020702061204020f1c0807020f060403142413080c0a05030d060915060e040f0612170c0d0c0804090606091403 73
    0x1c1800d1a01303803001440002c02c02e074985460001015400e20980750303955805400c5171f459009030b00e2404142c040c001101c50082c412594110b034149001502c2030582c5070000c1d0720704410f4aa0720000c80203584041140741c203140c1c0800c12440141ca0310f100a022001d1180e260b4001c1c1c0c00c0910400000d40d845d4241e0314440d656001702a5500c0c92602c110b030404070ba000c00b44070f80da4107451002c20901184c48800c2070b444680440c0000a1055034120504060b002c0da00743c9540d018001c19506071406409681b0080c0401640003d070b49000503515405000c0c010240700e805c00b280e218010b80380810b1890200d6136500301040c05a010680d50041d24081d1404100510440b00d01e036040311004041403084204210149051803a25111540302000b0a901414103003c031544070000d0049260200c40201c800e00714050020741d000d84c802003035034001c02820001c2c000001198401f100c0c41041d1503400e651402003003000180e40380c1180314400040c201c07900d90811403803601621840360382d1030114243c001d82207 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 342516043 1250 342514793 342514813
    0x51603020114090d1d030c0603100f03050a140a0c09050403120204080c0a080c061c0b1309030e010c020a0b0f190f1103030f0a050c0705010908091905030706140c1204060e03 76
    0xc944a40001f50175030785582c5907034442c41d400890850f5584201410a909a4088280800400d0003907030b080c05004100c0502001e24480e030340c1d5071070b4800c001c0e040c0d010180382401460810b170040d54009022389810700260811800c4070f403c07030707109a200e404c80e68010f2101c4002e500b005480e0364002c20b030000c050071280c1050b90115030944100a081241c100350060844482c0b0100d0348000e030002005409110b4545481c408a001043c600200382c0c0440e0400c0b150290729031244004c1c0000030b50160490004502d00741e2400300c40e0304074403c03c0554403c01c4c050b12444005501134012000810341d00e003d50003950b400302030050b91131404103e0a03078104008010765480c03000f10058000841160009450381c2c0d5502441242c02081c100034030a5007043c000a060114140c0501039001c000c0390f200b024001003001510400e0032038400c094160f044210b0070450319000390a014550401c075080303580f50058841c6020300b000402204108081008102408060750025150a0410303059005000c9004 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 342517293 1250 342516043 342516049
    0xc08060f12030327010905070911090a14036703020d020d060e01080d0e060702061207050304120302030106020a06150803121b0406051603020114090d1d 67
    0x300c010704001100f000040c00e03070f510454101030742102513640002040301d0300091500544401c61031251004103420014680551056041141c2010344024004c1c401517180082c0100c40c001c003a40140c4e450f0140a900304002130b50310b00c0c00c030685612000002d494140d171200300302d00c40d02d44012101c000000016440040c07451025500070100c10042d089800b00881e4404601a01c43c1c11501104503001080880c1c1081c2d054202d44259800b0100d080416030705c4c0c4400680e10500c1c401044001780102c003d030292402c3c102c000345941800604407920300380c010003885d6111002500c443e00003c80000821042c09149103000100040620b4150710319450000020340c1e600850b80017800c110340d1340c040800c1d400503006d4103400400a5005982d10780e680503042c00c1003550221061601c2c544000030b80c0501c900c544003194181c84a07a2611410f00410070078910103c00020400c0b000e5659a0400312039182c800e500c0329103ea070800b0000c1150300c0c40d0310b50060040e2110740c01004540800c08103446d40399 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 342518543 1250 342517293 342517297
    0x120901020f0a0c080d020a05090f1f030203060406031b06030b0904030c020f0102011b110f0715120605040204171606120e0c060403030c0c0b030c07080307020109060c08060f1203 78
    0x210b10740070103c50f000703091412441c8181c400c8004194030000305440e4158008018200340741040700c80d00380c3c41030702409216000c18411402500c0701c40d01a10445024000e5010310f4008038040c00010389182c980c0e46030103c021150300413503085658500c08024150307050090038410501911090018141540c01078030a41e080300009108500c036020100e21a4030035130040004402d43c180180c680c000140000e012100c0014071240140142014101444400510903003207442d51035190420b00c0c030038241115941008450440074a448a8001035a5503c0b40050000340c40480c1e0f00d090902e02c441685444c00a91398480d2036448a8682c00704a619040000c404070800355101c0461031802c40d900c490b06010f02144440d0b0301c44000f050202c20316074016261011386100d0040341801c55120055000d150004440320095040200103a800003811a03000d140c200071240000700d00081c03659940c03030585007076203000310004640108000e190700e4403c20b82c04805200365104001e03201541c40b03c2c0c0d10780c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 342519793 1250 342518543 342518557
    0x302011d040f0b03071205210c070605030a0b1801050907180803030108060717060103090c03020319120509010e0f1809010f050a110a030905070515120901020f 70
    0x100940c01a0008020a854031001054a0040007006054036900401e0024020924800c0c0244201c400110344090070702101d0b40c070690045c00404110800901091417510245039800d101c3d0310a01100740d0700306040000102401c0c103070321519103d152111002040b0741c1d2148065108800e44d03000c4407505030b20007150780d05641013521120b10399034402d00283c401540301c1403100c5509800400c0095860710120255058031100341c1a82d0140d140d01d64101c4200030550f000e00e00c0046030360041040d546c005c1e4080c80f0a580700300028125603a4903000039013052090341d94040c100e4600b0440340104420200d100c50b07203003028144142003090020000f081131807030180c2103010fa6a0680030101d0769450040e4449000175a00b80030200f031400011460103851040411980d0905103000702d28408001c2c010404260343c0c9604290420030304c03480c110098400c3c0b0900f81d0380c5000d13445022030305460b141803805001d450750f00959551740d001c4e0310040c810704c4020620f0a05034818803810841c2d1942004032500 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 342521043 1250 342519793 342519797
    0xd0203100b011d100e1504030c0503010b0105072a03060f0c030c02010507020c060708070204050112060c091d1b030703060815040c1505040503150f13050607051602030307033204030201 81
    0xd0354500714040f5a600d415841d040c106e400d400f003000070070030121f1201202038980940003404903a4a8100540365405030010003089020891112411141080d00640900e0f4846015200c8036075a92140e00403641800d500548541d140c4203545401038140c09503214846041c4001c108515101d90000d440d00c6101c0461441124009540028001080140c81c82c0c150014410422540e550304074644442031004200c1e00740b07082603002c0010501440b0207030202c2d0404001c1d07400d45078044c0d24064440e80010110b0010042e1004005800305100d40a14451036030ba4400294032410309981c149010358198071003144501c02c40401001031040a0940111001024450f010040d207440c240d4a0b4011500410b405101d0901245407416454031458001c442c0c40b0b4400005888006c441e1040303425011000e0300d10f070300c040d01081500380318030700070a030403e900b41c1907c6258002d13500084c1582d0095406a0004541c0303072540d90213600c0050704200184c0d072000b00d096100c00846022482c1d0203140700c0641 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 342522293 1250 342521043 342521057
    0x308090f0a03120302130e01030f11031510050a1707061107080d170901020703020a0206030702010e120a0314151909090c0303140903100b0d0203100b011d10 69
    0x285441c0e100240015541c030040a20501d074111100030002d400c80048222007040e1244006043d0b00b03010025416260403880b60105c142d0251a1401585011b49010f038141c8940b940b040903100c91007882901813041c921306045024600b50411014030800d0708603070071a16140e00c4040c071484001800d20125080c0d810544901c0c5845e4981508200341e5500c901500d02510111260b400d502c0101222590091035041c80d198650103407a600300d004001c3c0003030159201041180161034180e0144d60300030b240e88000304090b40c4c403604060409100f072041b950b55102c04207403143d803e601406020151075a20b0b04012561130160072840881001000150040c0500007045003060603140300c48010306440031090100048602d0405500f000a00c03007a80094a6000300d015541c06080072614442c10040081c10040c041e810700c2c8008202d6810341951110b004003075480182c070180908000301d0f0481e800041c1f0304103480000b5144450305d45003050901d84070826092260b0b0b80750400c01d22141c852030407007 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 342523543 1250 342522293 342522319
    0x130e15070509091503150c09190303050a120e1905190302031e0d020a020307030905151209010902040e03070c0e06060a0807020c06130515181210020406110f07030809 73
    0x1900f0101b406146005640e001c07804c219892046030003e00000c0000e50b50705024000c4400c01c0f04405045010040020300304201c506c0005104003000302c501d0b940500b00281080301e4107580351900208001c0700205031540d28107142400f20a00601c1a0102440d00350103240e01e00f44c1d402510b80c455240140f914032681740d0201006c15a02041d10807100c4403040465882d5010f001c003035580c0d04411000c4000420140b0085100d041c901404a8940710001000741010f40d150040d00c2d1158004020444c03075980d810480015076103034020000f10f01719000c003440d502c616500300125214000d40000d0500706000c0140450307501c030f81040b1070155640b8500f405035915a130504038180300310401d0043d4484030108048a11b003030910242012100c084038001300b030244e48008950703180218501a40300c0300d071481000d5001e040207540c201c2c0c03c41a0000380c91240d10740c0500441281c20981010002540030700044003200c2042103440700606030b440040089610395500e001c124810300b43d5890241825215103 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 342524793 1250 342523543 342523549
    0x6020a022b03080a0e0c0108010504020c010225140a05030a03021b070f080f011e0b150408060f011d011e030602040b090102071205030307050306130e150705090915 72
    0x60400041c030a10341040c60340303850030020105282600c25602c1036240c0303005030200803c00512058000c0060f1503828145e0319100400000307410108507400c680d5002c100e40c050741140400070000411443e0014001e0b940281002c4840303c5804c0d00806260b8001c1d45000d01160000054070207228982c900544d807003601c1192010f007000d2a00c0c82c04601c2c030900d07101040301005a2800390a40e03441c40200d0700c88000c2104e0090984082d03424000107903106003200c5040c88006d400818030b144010b0100c3c0090f103640c44054907540d00ca540480d01a8001005020302c40503a841c820b4014001c2500211841c501110000000300c0103100b943c0d0210400301d188a03103a0406c2c0c4203c0c000b10b410010454682d5550440c0703900d25401054028014020303180007003440b0030916251410399030003200440c00e540c0c40d414296a9a4805024558400480c80406000c420107014820400ba2944050030503050b0844100c201003401908141c01c0c45002c0c00044626241d2240c0a40e11400c0541248961034a45c004 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 342526043 1250 342524793 342524839
    0x70309050d05060c1c23070207030804091154040b011e030f27172703010b0f0d030302030a0f29060316030903031b0e0a0503060106020a02 61
    0x3450045d03040000c21000c148860086125160710a441c0760416a42c808040344c880d116808024001041840f080c8107203081a4003800103076448004580c6002246841511940c0140141c2e54490503a01d1240c062840600c40b10300b03a4a1020040424001f4158001c4144801d148010f501641e6503400c0481241c0c8039200500014540011100c0c0200d80101c0c000c01a11b650800d910b9101d04007191080c0005481464400c0500c18070b0210030400342d603a03615082014550005403030503200744114403001d50500c0c010109a40c86003104040c500600c4103043c00e440c2e281485a12480134400c00800b41e4a5103a05450704c1a4186001640c0e03565036a6554020080310381c07840c10091400205100800d4a41040900c42c400c10b9080540890b0100030091503120884801a040062220300c0100740e019422070748903e84079090115034004483c03840141442403806520009141c28a1100c1c2410220000005800d041d0050b114a41c1071060107941d49048100080c0515101c140844100e5441c0030 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 342527293 1250 342526043 342526087
    0x20a03090605010618050603070f1101060b030a06171209100201110f0901110c1f05210106033923030420152a03070309050d05060c 58
    0x600b00410b5031643c0006003040c070755010425a080944601050b40d02d0b01c1019244201070b03940d140c207504205188100d844a040380205542592a0980031400b0b6100c84050b51040603500c0000400c11710300031701c3d8080b828144c52214170f550422110920008800345c100c4410f09026140d80c42c5440000c0001c034014600904c040444c00008074002e0baa04603a40d004101d000408d0b43c4030003c200050881d1500d0b00b86d51146680c1c080015140074140032840741d0190040980741c100581404c0c400200c104804080c040111203604002e401030000c0d41d0540700b42610701d81c00e51034256846162250a0b4461030b00030f20071241884800d02881c5407248118410b401c450440a0018050368a008446a0300d030407e58045609618031000a4141045024084401d0f00c00400201d5961100c0c0c90310907082d48400800c0c144010161082c0071040781d003e01c601c00d5100c2c010010f5545100d981401804800700383c100b00c0c4101000d03181117011800000741681c010f40101c507a1640c9800d18038442c00b111800309 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 342528543 1250 342527293 342527303
    0xa0b0c160606030c0503070f092a0e040e161703090307030506010f060c050c1e040e06010e070503010605040b0309010b090108030901080105060c0d0302090301060e1305100c090306020a0309 83
    0x4800001040001c1c1c0246080f40c0c4a001c0c1c49490079150000c26480340d101e800703070161a4419400c104603102c283d0300100690010000f140d803c1103e441401b60304441d01c200b000004c10148058141d480c00c007841244407101204000e064010b940078103040741405184250403031461700340903c3c14080400d00840c3c1090740000d084901e000d81c1d0b0301d0081d032900c000f48a180c2031180d0901d4002400c40c050000b0f19240781d40301024080381a4110100403a031800c1c10a41d4840d950046051411525031384101300014160300000c2c095903140c071003d020f40e0800108003000308501031004114494108041d0b0701620322408055840c0c1c0d440303100f850300502400c0e00850340564907000008484030007200402c400102030b41e035500c1d640e0b285c00030701c03206109854031540d141e40301c0709a0003c880d102c0c0d8058125810001c002040c000d03542c0711078421141c001d681c1d1008503d030000c80c090170004100003440402e00484010f0040b03204a00740601001c103079110280007642c00141c6402054804c1d0b2160445560003 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 342529793 1250 342528543 342528577
    0x80303010806011e050a03022403090a1112061311090709320409031407060c081e0f1f0e160c020a1a0c0a110907030b030a0b0c 56
    0x20712002541c801003885802e51204a4550002c1d044200341c040400340c038030140800035800c0c5158244207420001c1010040304410003000c42040704031181c002e50062441c4001003003c1c2400d070038511444000009164442c5d0f0203910680168000481c02549c000e2016101031001c40706401e20456510029540c143d003e01d10b1402c02100700d422130300200594a082c15101495050b41a44e618035000e4a070305100988119204240c1a15041d040071540c90b110b0710b4801044903000c2610112030300030200c2210259200e03990342d03a500760300c001d130303550b2000030781d030280e4450002100b0a03000f1540161890030921503c6000030b1065200014050301941a00c070707a281d00356983c40c901500f018060f0b4003c4600c1d0700b0200d00c00341013031143c0d824115894004180c613400c03900e48103d070041405616600c244848051180420b513484c00e01c541c980007030041003517005003080c060800041e11001040c201c181441c005080441d030f200000c690700c11603482010108542c94200c6001054050320030020264000303 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 342531043 1250 342529793 342529799
    0x1808091c080403030e030f1e1603050318011e1d031006150c05061501031416200c040c031b020f010f023103020414040203061503030901080a0608030301 67
    0x781c8010801c9a00036076803290501104020584c4411f145440040983e00003c03501408000303154030944803d12100880302e26202c40b0a03403654590b0350f580260b03600c0d040800c000304059204051b08132003400074688240340b007051b45200d802d03072423041410208020108910b14040c08460400c4030010100500b2101085640108078000d02005d020746000260004844c480003800340440c0401c2641c010301078029030780c90f808280310080011290604058483c116000c04059030310540303028451503035040b807907401d0840019044489800c80c035192400120140c03450000041020000c0e09000c8030b0210b01e40c03030300c000b0480c00740451141026032000c16940c0c909145d5000240f45410745640c1000780041030307589801d24106d001da40200b092241c1c2c40e9940394071030107403c80d4241c0c0118640c0c650741c40d400d44940104d8101c0d035400c590411140890002d000c01c1d8176081107055440207a11954000964011010903100e0081010190600810741c01103033202049800410203010f0b400c003126103941e5 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 342532293 1250 342531043 342531053
    0xb0408030403030605030606010e121207150605030309150d1103010801290906090c071703060310060b0d2703031b080105010503010302092a0414041808091c 69
    0x4000c0e50202c0101e0300e0b007140080e00d810040b85251049105849000b00b2050510038080003545150b50f407003041c05100c20343c818551090380501450360095200c01800c0446025000482e40e543d00064440d90082c4180c9003180e44080301e0814a01403151600d8950500c020382c2006020030948182c2482c0c800700011800030815031004003541c5c00803515012104a040343d0000b51201e00c4403440c0c201c2070140018020b400c1c020f030041d40108440400324500503080e11840342141c407056041c50b2074840001444402e20b81006009080c00741c0700f90400c40a45072030600c04580c03054118120440b0745501440740070f005d000701c044000d0280d081c070080d0303640e02c5490014000d00214170059581c100342040c0310707c85403144038424183c510603101d1301d02e580d0941e001c1241d81d08008011350a01d020005c2040c2030302c0c910789006003025940c0309849865900348000220301c20b58180d505400789141001d060300307400e22207124200c0c4079000311006640750721040c0801c85000300104401884d42e0b072261365004104c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 342533543 1250 342532293 342532297
    0x9031f0221100b16060234141501060e0103061a030a14040302190c03050a0b0603120906040b0708040308040612060501080702060708061c0309140108310b0408 70
    0x40081102c602c0b800d521000480c0a40c051a00d100030044940209100000c40c10341c01400c801070303000991620303030824505200242c0b014000407020101d0f20440841001258030ba14901004000c0180c000891140700b03091880b10140314900421540c0e080d0703c02507034003035446038000d80000e0784600c0c04481c1103003100005130300c240c40d4200c00601c1c0c0320100c20495a03050041d03014940c560701400b0b040b000d0f10b90504489000c000207840c6145018000800500c04020b003060140c80392441d8092031428008242c03c00100b208a41c3d2022000c1040c000c4035900c2c802220300780c581c8034800039141c0000d41400b419501840d08003d0101d1400940801c42c2600450400c940241008060024a0700c82c401162115800c0e1544005a480880403944481c0a014101c3d44540041c250000080c40d00500703c440b082c840ca01900440d180180c00e001a00010068407203290007070a1090a505041c84080c4030840c088017440580700382404142002c0348402d00440c5040e8204482c8200b505141c14903001036 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 342534793 1250 342533543 342533551
    0x42013090602030612070b03010b0a1e02010c1107080706050714060c0c0d2f0c13020d051602070e04050709020f220501050415030f0905011b020309031f0221 69
    0x1c00d1a001009170507030000400340b0a6a0044100ba421640380a01269064200850300018031941c9843d6a94501d4041c04100024440380d0010507644e003610780107030450304503001103902c5402c40403080c05003202c0014804204c811034609966150705505195801c904010030011450080d2428440c0ca00b6241d000340401ba5289415510041c00b604000c0e039010040100105082111404011000d1030080c52001301075201410b484254003a81c8c0050244044040d080f00741e07507400b044070100c1940c0c900c00c0c10362001100c824000782e030f0520a0060346d19000c07445100c03807110b1960002001c021b0180803507002002d0290302503458078803000f80080c01c0e0704150702d520300740710406004980301c0300e800c048802202c0381030312076600c1c0ca0f0400c5441c0320f9600c400310703050044c1502c6191441310b405071842000007140c060000001c0005d034444c12420000745203210314086600502031900700c0d135804110725800da102c2c0c84004108a0403415030038040e003e40c4e860784c00101d05482041030011280400c0c644a = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 342536043 1250 342534793 342534799
    0x20706020706170604090f120f0914060702060307050c0a05070302091509150303070b150a0f0617061c032102070804030605040206120a0e1002030420130906020306 72
    0x10842c0c4880b0201e401d0324080b080e440b42da00e1001c0c041800d60805902103072509001e0410130100314100c0d203441a41e1154031007500c0010b82c108003442c0d07150380e210440d20047e000c40300c1c070081e4482440e800105940600400640714280000200e41c4950042d0708072048480a6025280140158140310341c0f5441c09104c142e005901c0e24000800c0c03041070018078422402c004103e070541d51a00e100c00c0403150851201190184410442c017030200383c0100d900362144903520408401081c0000a1010b1201180d02c036540b14045074206215030394000c1c1c248940104140c4510360075654140004514002441c0c3c85140d00503500051418181d105040c062200040080072a0718000104074208034440c282000d014a2404e000910003c0c0b02600034a030400d000500c1c403402c140c810403180111031019503858103039542e14000c02d00c0e068802c2c00074054031441c00d078046080d4601621b0322101c801c043e40c2e801d480342c80d02d000c030210507543c0c00e8100031030b00c2c0b0784042c00c001d20001c51504c01e000354030613904a44 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 342537293 1250 342536043 342536053
    0x61b0a05060402010f082e170f010b040b0d110301090b09160602060114040213050301060b1306050310051210050a0603140c151312081812073302070602 67
    0xa9190040e961b190141125207151200303003007451080350462058480e510743d0070f40d181c0340005040b0521000f2510036107542c0b014182096400c0780f400e0840d910010503e014900388156030f413480c0d0340c1400707000503190440010101c910072070303000a005008008000701400c0001040c04800c006c00500915842c0030750301e290801c103403605001c1e82d846e002480342d0351642d81101c65030b0507075040a80190803020425110075001c40c0e1110006400d41e28250400d03c01c90101180480c101c810900e880c00007400d00703040080c070350f0621114050074488540115070007091170000004a41d2810001e410712000c94143c200040d0400e00c4860010344094070054403444000e00c40c1c1480d108012440d854a8417005010040c0b640941180c0f110a42041e010b404500c0d181860020340c05c0311400caa40d00c21032146d1078003540c2d0130a601500d1070203085d0501c0350380200e20101110f034016100203030a030309440003000c44203944007403525509107518191031007295070004c980e04400816000a00070f0103a60080d003d60b8 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 342538543 1250 342537293 342537317
    0x90a0c03080301051905030d0c050102040314061f0605030402040b180f1f0b091912081c050615090f04091a0c0a0c020f01091203020f12090a05061b0a0506040201 71
    0x2045c40c5a600034a54140c110280c07125141e030140c0750017401a4407400016003090350769110401400304004204078075401c02020491000d080092400c0c0e41c3d41503002d5020f00341e01304140140070340001030009004694039106544c142d6220030071400c1854400310340e618549440b55940c40c1c0c800068801d542c45140a911840e141e407581c1c0d0952090700e01031401182440c40725401c015800c01d400031601e84100e0010400b250340070001d000701108501510700190380303801821f09135100f250340b1040741c03041c036107032005120b499519640c403100c642c3d00110505446200010005420420107281240c3c000c1c58040440100710170082660060044440d104425503203401c0101c10134072900d920b103000118100c07002e60062405076200d1200d48010304d40115400e0f1681d4041610000b11b0750180d016900c220380300704114004000070f2144000300e00035141407040700c5000c6031030b0f01c0860040350b20460011a080554000c001d502c031445a202e00c04032622041582010341c1c0310007050f1b509900280c5501d40c61 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 342539793 1250 342538543 342538579
    0xd0b031b0108040803060a080601090506010912050c0d14010f1409010b01120e07090507050c0c1c030e1c1b0f030b0a0b0d1401061e0f0608090a0c0308030105 69
    0x111200300d0040e10303480b103070f03640d107035202e001d00d901c002c00070782e0f0042c4255808921400108035160190060800000e41800c1000000d407411106510018200c0c004a4115000406c04079010707982650039141c82d81c0c1ca800a10701308403900c841702c01560866282018031142020103421040e0744100265854496031260042c4500744c614200185002c2888085401d0000c060356210900078984481681d007180d0301c84c850401501c41c1600c2d0000000d101145c0845124014131404124045c111109010754441001d4241008903070300c0d000d828810304012010352612020083c400e01c0d039002190f0050301065240109002e00c40b800b43d0561107412034000b041c004039a45441003a00d0b00100d88501c280d450b5200030000d405040900c0d0b4100744403c098000003500b5070b1020315203219500020401034204107a0700c0d15035030140711140d01c107950a0700800000d02400c2051090329144c2c5401e10300d40e40d5841d40c0318035005150741c00812860810b0b0b000011302c00048091416a1021500003400a000c000e01c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 342541043 1250 342539793 342539833
    0x105130803060d2415210c0807030b09100e10020c210a0822121205100611030f07030e010c0b010f1701020a080601120608030c060109052d0402060c01020d0b03 70
    0xc9004030088201d206e51011003600d60f000041e80718a80310500703203031268000360821344158012203450f0400700921042910a010313107084080903400c1003200c8107003200001d580314510f080034040a90700042000c8202c00074803440490b1148078000307501011011038600c03100c2d41f11342b0310320001031010341c00f02d0032040380000007003940d4021080c1c100007604540c98030205220016002010f120349850f5100412410340907542c8140d4209030140300c1d4a1074480050450540c4510460f030720342080200f00d00350018102500c01d01509450446002e01944006844007905034801808042400e00000b9215182e641c0b0441602c01d2460b000c1d02c1d100f1100f803403600742d00a00100a0103d200a400605d55510070b61203400d11040004010503080c0d41c0307001c11390440d4003610700440ca9810030030051110b07100310b0042c19000711215140d12448402e19a11842c880310396036141c40050340b090003107020b6543d081c0c140d90f202c00410008541c2c1e900c06401c0d0a00400012031464003074002e08115040c00090444 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 342542293 1250 342541043 342541049
    0xf020706020a06111909030b0a060b030c09180405010501030c06050408100c0504121a0f04050a0b070e060c0f0d081006030f02040b07081b0105130803060d2415 70
    0x2011402c8450307076684003030070740b0505a03e401c440600c8100031031003842a040d40841c441d0f4541e24115419424840580301e8010070440c142d50a013101000800c2540c411258041c503504082601c40c0302070400a41d0b01800641122000342c031880034402440b0f0306502c114100c1e44070b8200c0106055440e1426600743c040c0b4401c00d00d10f500300742e5401341c6d401c903c2d030802e001100c2d00b450503e2415803680c1c400c1e07c0c0d03c03410072826207051260249600d05500c602880b00e40107012170607040740c41d15195481703a0340c4440e984801800082c0c2440829000340c018800b0000400000780726945982c0001c07a1300e50344d030300c2d0b0006c0c280d01e910580c0190300c1d00c0c0b4003900889000d5006469183c2d4828280035042e030182894410b60030b101035007000001610000d40016052052052401c5541c802000303c00b040503048141401840d0391400341070084040060003004662503000d070390f06460755200e200140e001000d52a0103440448410b0f11101c141101c111000c58003609008200080c03036440814002101040c0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 342543543 1250 342542293 342542297
    0xc0109080c0601050f15091801380f0c0111190f030b03030405011b0f030e120102041202041d01060603020910050403020906240c060105010e040203040c0302040b040908190f020706 79
    0xc3c6e944880f07a40315200400801d003002d800004442c0c00c86100d90160385c001d81c0042035107060301000c0c207465080364001180c4051131074001e200c0c01c3c09410302d0010714483c51900b20340500700090405031000082d0031103402c840741c0e2030b41c91352286503494015040c2c00504041d500000c048509004034039002e88114400031001400450415040400655180c0c2052400200d904540910040010390b035042041202d842603070742207a5003640b00c0511000c10080d91040c41c81e64010301c014026003c0e5400600c003581c0c1c044801007500150081c55030200e43e07403d50519450f5003030080204920350560001c0001c45800d590f105c141009441d01260a8003482c00020350204440000c2002807411500058203520300c401e070744644c9004024010a140d004101000068000900421540da048040d00e003a020302641d0a40c074500d09542c520801740f566000c000e01c9559509040f42c8076031a581d1118404590100405d540c0342c1040c40000b892070f1080c400c581c00a28025020083c440c408104103040750349603 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 342544793 1250 342543543 342543559
    0x504030e040c17180c04091b0524030c040312031b030e0304091d0303041b0b181005040515030406050603150c2206050a030609060f14060c0109080c0601050f 69
    0x541130b00c04c0395050512088903c00d070031100c541c0d0750707840c8101624144118200c924070050160b2856040d20301e03a2046119181c5030384000034950b0085050030151001d060819982d5440e8480388655010300e4001900c480ca4114000c81000e42640c0500d40d02d44816071006605a50003800b103081d100d502404900c550800e001c204000300c0d0304c1d006004a40b02c01d60b0108619a00c001007c2d155810480b0161000742651002103c0311040158100c041d040071390520b841d00001d54190295a0803000700c141c001e90242d485180400d10440c213440c050400240ba80e68200598101d0300126002030350151070942c60107001c11400e00d40050b210502201030b8240342c1055442010b4000c56811969070030380511000c501d003444002c181c00000c00605880e03154a070303e41c804218001c0c111200750300240c1180f03250100c180070050411002804880c041903400c0004020540031801030701030008001a02d60800c10080c0400900350f000d80004807045041351016a651000c0064001d4442d0400c0e03009899 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 342546043 1250 342544793 342544801
    0x130608060f0402222c060102070503010614031e07031b05100c1b030209011403030d05101712030f06030a0b090c03010c03090203060604020c100504030e040c17 70
    0x802549520010041000007500721580100e4140ea00c40102c0801c107414525000620400c241c08500283c2a8420009902800400140d508841c00d0071002503c500b5032001070256032003000b050001c0c10010b0003d00c01301e03a840804c940c1d00c01d511039009220380201078900c1180ca0208034581d00c050035170002001190310b184c4410782e0020070709051101d40a481c120200e080d0721444400122160306541c2d041600311981000d10310720841000c2c140c2103042482c0c0c101301590b00e070b4030242e0641d00b1a44c40c0301082d04201d800a440c0d8400e0038400d841e082c0c10078081201c030b0003044e00c03803400315252000d0300800102441e90f50707602c0e620440d43c0740802030405d102052013003401c140e405510800c00307000c840e200001c5403681c580b0504101e55010711070344655050801e5080c03e00941a641c10241014840761019500090310b9800c0207141e24010b0340c0c042140c10312900e04000f003810a00c6600010046402c3c5070038000c21008100108030301450521715103058480c4074150495007041c0d01085c0780c5e042c0d1a = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 342547293 1250 342546043 342546047
    0x81b061006210c0c140303010303120e0a060e030d0f1d0304060909110c030c0a0204060510080f130b0f040605010605090f1002030f0a0305010e06100210052502060f0604021306 77
    0x2100c2050400c00804d2880f200000304100000011140050003c50301c1750b145107070007407440303d0658601c50301a040141c40641c4403000101c00000e960f0040001c1603450f4248822131030340c0940b103080e442960400142c0c0081080ca0340c4012240c1c05204061401d0100c00680d450340c0c2d01c41d0b807003000d0002d500c40710100240c901982c40a4400030061100c0d501c1d06041d03182c40741c44e41d008888180025003254404c0011483d003813154030000e1409450180060000713003009422400c00130f044015001c2c04200188030445451403038070419900c43c40c803042d60b08000750f0481300048c0803075040f900c8515100000c540180500203079140c0c070304001c0c200d000c1d209104051050100a603140038095100510414540700c21000150620340000c0e0340006041d85000951444200082c09090040082c09042041250301003401850403000d40404a0b0585805001c0c03458440140c0c0c4c070144410a4210102c0130136404a10940030701c1e5528007840c0315880710300c04c0004030300c00c030703100030400c00440e0404106940c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 342548543 1250 342547293 342547301
    0x3030f050409021902010501080c03070e060d020901180f02090f240d150504091106030c0c03070b06011715040c02010b03030c0d120c1209081b06100621 67
    0x82028500355040c6540c40e14050180c1c1c000382c02c01c8110300308556140043c0ea40c2441a036004107010030003490500000000700e0780702e00481c042d102020010b01d00041590f10340140d0b00d00d0007a8023400031507807580e40c5d80001c850b81c3c003c041321803041401d0020300307050703030803036009480d00040c008001d004541c005108100c070740403216200441401001c805042195503150140c440790351880d00200368010024042d4079900da00d1f4000e00c1c800e40c5013070f201d240800c0507000794460380c0070300384c624540c1c984801e581e10b043c90207030300321103c03d07440001081d408001068000900404003a29600460f207040440d810100390100c0c3ca000b00c1c5105522461401e00d071680144000d8036260000080507801d0001080c10355110282000a96229203000700d040c40e8424079004c1841ea01b010104130b208020f00004008a542c054812043c6da1203820302c105000380f9504499030640d654038441715482c0c030a01e0458039140100e40301f071605500d50fa40007030500d001d684030003100c04030800907210344800304036610020 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 342549793 1250 342548543 342548567
    0xb0d0b1804051c03090506040c0812031504050408040909060207032a06272315040204022809030b010909050a150617062208161509080409050c0901090303 68
    0x40c2c4608413400451001c2c04454007031270140001000c99410011000d1030f0060054009081130020010061200054010510303201400c0740c0200701600d45080101250003140c0003802d0350342ca4030164408211040c0d0003030070a14400d465590080010041c41c01d4280c0c064005400d0b004981c00844001030080c0d070121182a1400e141c40350100f4891052030289803c5076821110014a02c2e42d44032011540e00144c0c44a03142503008010b140c1810320700344059240544024029a008078a400200c0d15845625040007042440c0c41200100b2030801003101941d803005541e000001c0d0b001003550700c080e01405200c281c2040c004d000520290741c84201c0100e00058801c28941ea4001c0070454a107a0314a64004007202d030003c18080c1800781403483c40c00e406070b00040d0344090182a600c001500791040c1e80030b40c0116090724209042d282030282c600e081804400e140d031840e1900ca403041102400240068400ca0041000075a41c0c096400343c541c0309003a81c0d9808035880000401c0041c0c4103400100350 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 342551043 1250 342549793 342549797
    0x6050607060b130204170c030304030f0f020d200103060803131707080a0311101401030303020c12030a09050f0d0c0f110907090303021504200102070b0d0b1804051c 72
    0x40e107400120f52908a8009400a111840e001702000e602510100220f107100081140654a401d203165a0389040e21031001004011f01c24100780c8000f59640d410309400c100b030308800f0308074000e45000710350b40101c0644803501303012030714190000ca051040002903910015283d4a00180203080c05a4409103651000b1030910a104040c004184454184101300d01d1034469100c690348022030580903414105884070068542e031070595651084803a620207281180d82604006a49030440f0600c2d604000300394000c004441d0002092184c920344a0317022000b075030b015106131170352040049512916081c0400d0b64000094982032014041141e401e40300c0700300d92184c1c00b600b098801001c0820b0000508440c1d181c08580b00850820070b040d0144420b0526100c4414403810510380740c0d40340134646201e00088124280039131404901a402045010090224690481e0310351442c600944054014141c02d180600c0d202091110084d480c85507540c01181d20101a10000c1101c16698900040d01984001 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 342552293 1250 342551043 342551059
    0x1806010b0c120a080f0a0203070206180f161514192109060501150c11010905030a050601030c0828060b040e0c03010506180412020304050306151306050607060b 70
    0xb0b90503656401072445400540f20304103c0d1408410400b0f441d04010b00c00015203004100b004051a40070580315844480c1d4030070900000b150b04000d91804001c003001601600c9811040100030504040b844100c4128244040c84c0c09490388044942801e11125219003e400780000304c20110303944104e1044519501c1e008030000810811008404071060400070703801d6a58045905010f1030f030081c9405061280e200703101000048078028540d18401e0302c00f42070034110030f04041c44d03680b0440210004180040444600c1ca03c11308120741c90301428842150440c40c03030403000441c0000402d02e100e05103084030fa90034088049646231008c145422104803a50b43e991540c54210395150303c41e540b03030000c3c104000c1000d022644181400c460026100c54840c90b0519443e680715018100070a9005034441c00f08031303181079950021303440c0d4025508215810301641c41081000a0782c903608051030901200c0f500300c8081e028600b28120764090240d2034210008000e880b0100b8016000720f9040240989145 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 342553543 1250 342552293 342552313
    0x602191b0f1a04060c03031a03030d0209031507050a032d0212011e270c08071e17190c0306140a0f150203120711061806010b0c 56
    0xd1100d4000d500803503204090760409128840e1621580c2542501c045142882e05007820000f9001c0040e480740201010380fa9003100c441510b546200040381a400b4007103c1d2140a8006040b01035081130400300e01070301c03c1d48100d4403203008079000b090003a20b40707499682c0b0342500110120090518600704510a00544c0d400076500c92002074a600341180c8440016100c1c00808079080c150075040c3d0000344064a600701d0107a00d070305548100022114543d0710100b15255402040e03a071182d1410011440d00d103070240c894851174004104510445143d5145e1070415032964520b1207030001807030080005080f001d01042d800600c5150140c014014900171105451000300c4003040e503039806036a0340000d40340c0c5001c0048140159140a940100b22612607000741011201135449250b880b81c50307038000020220314000d6000344220340c1e0340321344642968a1468420005480c62a034003180c0304841c460f140000f80481001c0c1041020714a00c4005401d10b64600801c281242e0008a189005c50003400100 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 342554793 1250 342553543 342553583
    0x6100513030b2a0f070f02030303011719120806041b05180913061e050405011505010203031e0702030f030a0506040506010f0f140c0d0c1b060219 64
    0x560041d84600c401c1242c51402504402e006454251904080701500f004a01d4544003001594061039001d52016180d82e00d50400080401c0c04820203505808000004500c0351000030b84009021008402c030b0b01015481c01c00c4002b840e54004018107100003514404074400e11a03100b50b40c1203e0000e02c04100c001503110b034098120090102c8101046000521034490305202001148643c0708688009061500380c58140000c101c840e0000d156a5a400085c84100750032204030000c4212800308221914051a06c2c50090540d0708200012502503107000400c1d41c80001241e00c00c1c400880c200490082c12084403041403405020b60341540003d00c4600300c00c2070a100903610075204860081014103101e401e10007255806091b480c10800c2e240b00040780c01d80c008001c5d00d0144114588840c0e402c0f124104d490a03400380342e240700b40c14000c1c0e1500c03504c0e03070341c1c000344840c1b606004401d14081c88203221541d01c0d620546204100141e0030910141c030705006891640d06009002e01ca112400a03086c03004 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 342556043 1250 342554793 342554827
    0x2090a0e0f0601020601080c1f05040803030106030902031c0509130216080318030901050a0f02010f06060e03010b0910050f0409020d03080103030f0906171b030c070303140f061005 79
    0xd00010050141c0030008a581d0401c001401072030403601802d10301c0036110210b0082c0407601e030843c100454046070f10310305a12550440c0e008044040640f03482e9611507100901400c020b480907442071140c549132000c0711501e4603030b0040e4903115864103441e1901030003c0c40308400d103003440000e045034203000000f403184118186080e01c602c40d400d1030b55030389458a8105820b90a218041e80141e000b808210482c0c0d800c8411034403034900c035051514260500c243c080303014140242e1184400350408000284498226400c1001c27a40d01710002e1290342203250501074960022194507004100d0014100b04500f40402c0d81b16181401400100303003000c09030042050020340d054200c00249421004106044d0b0101005510754418605550703110300c1d0800081c4800c0c181d03d0813989655003c408591b9882c40d000002103107840c8c0c52200c0351246044046d001c8030b6040601c098011a003002c120000d180908003006125510721b10003018184c6404080c842e500040402c1c7c0420322908000f60b800c540842c80c4 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 342557293 1250 342556043 342556051
    0x6010318051213091b0c050c03030d0501210215070302160b131d010e19290105070f030c020607050a0b060103110c0a0311070e09010b01021c090302010302090a0e 71
    0x20140d0390f1a012155035605a90703552080c4140ba140c03500c00600c4030105002180ca421080c03070000070b02c50060900358203294030341b0041681403000007001210328070f00d900018102c03000304214611800840e84149076030076484000950004030000140c1082e00300c13a02400c05980284101c8140113000559100e00003259040f900041001041031038151207800c0c0040041d0844200340c040c90040d100014550700c90602601c608009004001468403481040c1c04000b101c848805101c940440884075040440c2100304050506990209003004e50285c001c40d150b081d40280002010304203620101d40d415161101264094810401740020a504122000100b4024660501c1c5400c02400140480d4000d90003a40300c81c02c14000310b0300d14480440d10040c02601030900c50050605e00f4a0079051002d00d8100031060141d01d4140403080405510001404c002a02110f01c03401c40350308081c42030b0110044500008103540300c14001540320780c019010300f07800941050340142d260080c072440c0726802c403 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 342558543 1250 342557293 342557323
    0x408040503070b041a0912150103060e0c13020a02010236090c12070e1c0203070503030c0d0509060403021309060515030304060311090a03290f0601031805 68
    0x8142801507150a02c01c0c94010482c1281d0f241c5000d01d03181d2900c0c1d103410404040c2c0020301005c58580360b1500d50400c2c1034542c0c01c00700c050380c002c09141035114242d20380a020503a100d41c0b4141d820400d00c01c0014070b4080c2002e00800c0f940301c0003c091503403c06036000010240465400b070154171918840d082100079082414111700514102c23010120740004138205181d4854078001081c40503043c440000c581c41c160006c820b40000740e6400405131041c0102103541c0d17070407204100103d0200f22144044440c92803080702039502c0395a640d0101981d074025003901c903c054200d1144218058080d000500c851800a002c560610b42d80c0d0b00002c50702802811b904440c145c0b2041042e00f001001d00c00c15a005054014000d078247c02500881d50f02e002d603000e41c0c0281030f5104c002c205a4188070050386e1034240c0060a0385411512841c107020042000300300c916a03004041500e548600306408075910404510604400ca07544200c0118003130140c01040044400090a404021070750a00c480511540b082c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 342559793 1250 342558543 342558547
    0x11090408071205041508070201060308030108010207052112100504050a0e010c0f0807050706020904050a060501020f01050610080a0e011a03070504021201030b1801020c1615020729030408 82
    0x2a00b840303050501c1c0701d4045070400208010a01550314605407001050030300c0d03d0144940e6641e424268014900754101505444000c000001c00c034a054004241c2d4034415400d0b2400003505520500096020701c1c400c00e800003040c4468000c807184070425980c010b8066960344441981c94011030120703442030b00c14007801e60300c0d500001c89001c824000c03d1804095807821800c901d0a441004203007100203402c20041080008010060103030b00c0d01030f1102c0303000080c000c000609290341500014000ca00c107203400b602440190b080d6044061042910411014011340c40c184040402242d04c1040184140c030103543d0f440c3e820502200c248125440c2200007005407903003450405c105417a04840b54402440303180100102e5824042d40d604a80c1180d6010b91000201e403180192614a40206041604158404118204401c1c4000b0302030000140d0000100309264543d03081d0300d40489003910140260388501020401c02620b001c0e040200004c800728000511001010a0580c2d030007503405030f50750707400 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 342561043 1250 342559793 342559807
    0x30807110f0f01080c0903030d110702101b060f020c010f0c08010524030c07051212130f1b05030703030206100b040f0312180e0a0c0f0c0f11090408 65
    0x400200c00c169100b1580c2e2042c0006840000307090f03050040c800e1040c144045560049a10200281d8061007109441401200c41c02940c8503107503040703080140d00c6440e0252047c4ca00e24040c03144111210300c46445190a0001a159074010704250300c801030320075500b0000200018420700c50203241402c0c043c400300e80c1044d001b2008146c800181c111a00c0750400b10121100700d07a101c0c03546102401603403095526a03448203600c0c5168016030790050124020303074801c25092005000181102da23400419107080d5210309200540038404000f00a082c0300c28a000743d1b021904440440f940c0b0204984411650b5071902d000c01d042c8909030740100c01503804941484410004142000068500020303003500707113860182e01e2820101e003448054034190000d013034006014030a10036626041d0801001c2c044a50b5a01c0d603c500d628030444920139818038101004400512802c0304031014001c5585a05628400351a05240441d590390103c1d0100890143d8001907181c1440726031141c0e0103501044d840e005 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 342562293 1250 342561043 342561049
    0x21908030d0605013b06070b071404030807021c080c0a06050a0e1e030c01020307091403011b1209021305040308090a0512030a02160804090f02040e011e03080711 71
    0x40c2c10341001d814440c2c0480c55114207a43d00b00022100036480051241124000105140c0d203c400550070780c000d68001440c200388041d00860a0251070755540d0203442100801800c0d403203004900005001030030030003072032001d8940040901408031480703010010303000c1942d490380c55a9114503024065504051004400d11605225041d4070603519001407046072507482c180c0f40c540b400040c84400303003200704210003c480010000d442e0014040c0008542c2e90a010401803c008914440c030a50840e0044a0880702c0c10180500100d465140354025039452032020241c0b11a09840354207038600703130748182c1d40000d40d80d40d0000112a40008000003404d00309800d000300704d141c004003000d8040d8050b4590000056002504030040b0004006458903a200c0c041e001c0040d03c540303041d00c40003454604540c0c06010502000b80200c030408941042824006040003041e40900e204e0105022030403001000580d49292003081c402c0800440001c2d4186c884c1d0b41d08810390014407095480d041c80c0c0f60048030781e01b = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 342563543 1250 342562293 342562301
    0x1f060603150f050405190c0c02150720031006141801030f1104020d05250e030327191508060607030f02011b02060415090c0e04021908030d 61
    0x84501190881c401e82090102d6101907242e200d618000e036a6480007420703e50181c851014100103810382805509000a001400c80c1520780003a40310f0110f810018140d845050300300c452a0b0380c004c9100145d0030425442500080131080700c2c80c0c040c040c05002c03c005200620a4001900142c80d1003448414424140240011340d03000c001c0f94502c0341001440070400b41507200c0c05550b40301903100344111400f030114010f80101da201110701d0b401d001c01c8c408074006080c00300d265604c00d100c141e41081d6240004940401c0c0802d0215015081086644a80c9050b038111620070410403404500c014071b800082800728445080c003219400d0051402d004051521103407142c41e00c500d242405640c10002c000441c0d91082c0c13030006081c0802000d1202d0158001c1d080078040015101002e1140520003801030b407507610886007103a00310000142213611940520507035030015006a401a405824101019000c3e032000e00207a912440d42160003007070805c0c80c40d04501400c1e261020715184c0b08800ca601c8191 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 342564793 1250 342563543 342563561
    0x51b070c080f070e0c0306040908070308090c060a17060402070816030e010206101710060b070c05030610270c0507260f0a0e030f0606090903030702030a111f060603 72
    0x42c3d041a0810001d81d100e0060b07064100003910001ca50b00c0c1c49081c0090014801d10200a000600c041400e400340b540000c03000d84154907210581d14201462020401c03140304903402040450100000943c0a500380c050741e41d48180041d00040c5003003c96100c4c24102d07044881c000500da074115111400b0903074412440c2a54980a00003001241400b4090f00c070411158064191900540b2003c4001440c0400070341a0b0201c582804000c429141c10f0042c1c11031b40700e80819510410840c0b0001814140041c401d4030034154081002d0001d41415500d07010042c44d941c2c210100402c180155006121314411700001101c65103c8a0341c1d03045600d8200158982042886580ca4104c221004141e8581d011240305004035041541d94201c900c074155013890103800d2081c1c141c840c00c40c000c02c08035000076180303009400846030b2400d41c1d6030780b0542030344e6840115500c0e4016042800b0480509000e00004000601900305594040c40c469404003081e1a03d111490b0b869910f07003a04000b115054841c2d1040 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 342566043 1250 342564793 342564823
    0xe0d05222601020c060c0304061e05011d04020a05010305100e010e1b03070e01030c11240906150d0311160609060302090d0b0a06170a0b0a18020103051b070c08 70
    0x105882407944c180ca40c0001041e0381e05035480000003904025079036000541502142c1c00a103821483c104590000b00024050502d203140e840020380003904c5007484940c0702c0d41d030003414012454100710044000d001c02420805042020590114041c5078400d15140038202b0001c84154a03e4410189090382d42009490044204204180a0f10720340c464801440d1074800c1c240481e80e4450440700300c0b40c030038100320700071a00d008101c03040300c0c030400b8901424100c21154850f4200c5071510606151560004d8400715221303040200440705508001c0c104c184a02d00230705000c800402ca0740380f1142040070702427180840b0ba111040c2806400c2e00b000c020300191440345011820420400d021402d0903809038409403041940784002007032081103422000c040d0401c1d4020458503101c0b4003a650f0307030710421401210b40c14031b4140015204240c1d0700c1078207450003100c03844c07521080e169001503000305405002c1214169200b4904503080000500400815114607110f00000e4503103030401c1e042c511800c0f55101 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 342567293 1250 342566043 342566047
    0x20a080708071b02060c01060602070510030605090a050408040e09010e0f0c0303070215370c020a030b09010e0d02030d0624270609090f0e0d0522260102 67
    0x204080d800025804122900c054400b070503c02c0c0d0000656502416a901806600700741d000708040342d01158410840710140da510008401c000700980558606d4002e250b0000e2101d00014101e02c0700390821600540903180312803402d6122901d41503600070407203070205686e448002d48104880700700010780c3c580b184080074187d040314040000f41c581c0b090202c081c4c82034032105416020091400101c0303d0940794040290300712a10010031710072030815075011307009072000d041300c41d05410700910b45925110341c020030404801c2c0c2903980765001c0ca9009006840700d50b50340d507071040040500301300e60303102e0450a4005589800303101035241c0966046400c0043c07100c054241e0b22810300c0c5000b144011901c128200700c0004034100341084145412607420000c0f0740c0da1030900048840c0c00a0304401601c0c480c88040c8980d01000c6800800e5410544602945a001002203041c4500c2400603000c0041c01d05046c0c1c60b040c04a2041d4000010340e9000803c0706402c403070f0b00c0941c40d04c0c94544100d1366600c1d80c00070740c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 342568543 1250 342567293 342567301
    0x2d02030705010c06061e05090106090b07080c0316030e03010b0301020708030411120304091401060806180c1e0d0e0f0a030c080c0a0c050321041a0403021201020a080708 74
    0x65190081403281d503050000f03080f41203040051540000d0090301d03030300c3c403a6841032861406c102d0814031944078213030040c4090b00022030399038840c0f01e2040542d100001d019240c03607103540d038522065001c1e0304560b8042c001804070402d50440c603490318030803501135991100000602d41c101421a08240c3c2014403c0e88100840b000003003607132058a900540000c2d241000c04080000b09009121080032580c440c0800240852500f00d1544040400c0c510509182001da0303d511013690714410035560b0b80d500c0864a0305003401124902c05081d401140482c2543c208000302e01143d41d50b40288004102a10020131000c454407814403a40341c0210343c0a00805802c0d00f1480c04903101d903500340b400380400c0b4080e02c1100901072982c0407140100f40480c2104ca040180e0309003550301c0d1000d801801d10900501000b2041600740c0e800300b419004802040b40e02d000e00d00654451207240c092100903010005210000140e940d25841c030221984190000d40d0701d00c0030b69001001c07200020004814000c01801380 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 342569793 1250 342568543 342568549
    0x10605190305120c01090f060e01050f040317181009140c1804080f0a0c060c0e18060d080c030a0e010c0b160309080417060c0403080909130f2d02 64
    0x56440d0b58a0f041c9907035070341c507086411340d4003406040c003002e030444c025241480104401c6030702003c03c0b0308000d002007245480d40300c039036034140358142d81c003400045092589005400340d060406401c0400e5244181c2d906403101e1505050090b0304001c4411aa0365420600501060980c4050103141d040040e04940040360b0015518030f8840c01d03090240580c2c0c900040400c10329404a60200c402c0000e01c41d03c0b1001c958005020515030300088800d44c5c1001180a005401003c1745407019600400402109152101d190340c0090001d060307a520002070176190020a0145006100014081e07000e199510091400a0300e076484409081c4e040100d071884500126200c2050076030031010400c1329002040d403445044014100d8400090502d142c001000120240d0998841401142d18800e64485036114004104507025900c8060030100b0708025880092410b603584c95445200031402040034105925004e1045054110440d00394040c801d61030680740100961514402c0c48006d481e00c03d030090317404 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 342571043 1250 342569793 342569803
    0x50112030507060e0115090c02060705030a230109091a01260c18060102070518040201030513080406020115080109050a200d0503120c1201030803040303110c010605190305 75
    0x40035003086400b0501c582005903a400280a0400c0c0e08000d2010750107000401c02810084d2050742112454550180d078450b001280c494840c2c0300d561640c0d401c55a881c40c003d0301030480c1940807248071004003c2009112181c03c0c400340640110540001c4000452034000c80c0b00800004941d00086d801c0c004210351030442c05010316644004c030818900304c0c1c0f01c01e2060320702103440d101150310108449483c1003000e2030215892141c1026805c9070003142d075900a000320380e100e600c4840c1c02d107183c0500080140d40a50010354102e681c06d1504a00710042c0d803140c50039034005410400c0141d4450b4040c1542d0341d0006002800750020b60001c10440410f951001d54801e003c0c44e00901c40e90080407034450300d0b600d4000d030844544018003a1024a130b000c1c500701d42c480d80001d030313514407800942c00440d2803514030900340c0c0c044401c0c22a01040503420b64541c01204d4000a0040b800c054882c0d43d2034a01220303000c082c248400c0c401c40040b50241c282801c00c000c01010080c103c100e490351507420004a000090 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 342572293 1250 342571043 342571079
    0x105150a1805091612090816031e020c030105060906030303241c0c060c120c15060e0612030a27050d0f0c0509040f02040b030a02310501 60
    0x4022056040d4910301c6501d54001e5808564001c1c4103208000e030554412004100420f865a0340702c0144006071044821a403100d2009808588184000701e200b03521007036050301070740c024140280440c000507030480701030503034001080c010b8100740c0b140748903400d003401250340160007225004041d2400340046540d902004043d02038003c2012881c48840310703d0101194009070140c85625022140032229894204400d022500c2e40350001300013640304c0c410700442c2c1b170340d0354810800c2e0031014a07210226401c250701d5000341d880340d4100c01003040040d4240305140040c626000401c6803031905804001c0c10001d1035101700d106400c1044500705d1146d0121214034851200b0441d0110042900c6203070900600640000740c201c543c545100003840044140201c21901c02d1602c009895200c0c0203008000109aa004082d00c4039502c40d40014541504250b146082c00b0b01190502415500001c000740400001031f044411580310110081c0101501134110040c144000d100035450410b0403651821204 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 342573543 1250 342572293 342572297
    0x90507030c0e0d03031e020a0801080f19060605221a0a1511010504060645020d050103080c0d020c03061303020a06110a09050d02030a060f06050402030a0c02060105150a 74
    0x20710240030035001e50300020011508502200d0b0100005091b0300c000d40c0845854000300324113600005100c01c000a5403008020030300054500c2022013501d80b01141c2d06aa401c5462030740b00c050103c0ca40d110741186200c0c1e407031016039401c0d800340070b0f102007030807100e01c888885038180148030b0342516900d0b8124084102d41d80164065002c1404d00404c4814040f05070100b0f44550811044c001481600d40200c0b0548074940030319000d5a96102000b40900c101c0c8041c12416404000d4010941401c0031451410401109000d8a029251642a401c45500360000c6a41050210b50513410403010000c00c2c55040c040d0005045074043c250019590f48001000d50b020003070181c01081c20503100748102c0080c280c2c4904244440c42c00401040b01d030341c1201018100040031841c0c005050714107401004080394014000d17203512491500c4e14006841c403410506995900d40e0800612a02e0300c0c4000c6200740c0340c2e10300000702c0c0240408001d01300201039020030f1141010403036405900c04508202c0b01a1240c1e4 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 342574793 1250 342573543 342573559
    0x30201140a20101b14040e190204050d2d050a080705160e071b031d1c030201140a060b040e0919080306030d02190201030b15040f090507030c0e 63
    0x2c490b100e00e00315607010080d100c1818240342c0260070250311440414001075032118010b02800c01c05640c9107020300e100342585450388502203014411801e90341114005403800162503e502e039808240c3c100c4400d0011200080c000c420191403030107200710402a88000f10004c0503003d0141c0310155250030b0b40c0e101900b08100041c09034100307d0200041581c010400010900031581c80c11201c0070000c048a8401c041540c40d02002039207110741302d15402040e41030b110f00300ba02c3c1c0e03c60440c0d480200240d1600c0d4201140c070f5400b43c240c4645a031804000d502c00da001050380295401c03001c460747c0d00500b0a4140034200601031001290310010f03a410303100030004130040c680c1c4900c0b10034904560f113400702d82e030b400d40802a1010320000c20020b40c803030700099045405007140c0e800120381e135109038001d002030340100120000040d84070341c005114459004051641c101c044144440302c55201313034081e1a15801c103000402c801c04041c00307140e500c4403040c10200070094403840301814904490a030144200c0741 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 342576043 1250 342574793 342574847
    0x3050906040905010b0c12130608060a030b1602011a0603161710081b1c020d0506130c12020906060d090f081b161e0b03090304030201140a 61
    0x3522003510001c10842c030040c442542d454071642d00a90100030b00b040c060182e034129955a480f05407c548091a004411440b40d900c4c00c401210f0881014051640c0309950b010000081034081c1c220500600c01200c1108070300100501c080e00312101c5800d010b00e5007000c05a00f204d190748010030759030f12003041402e00c01e104c544a401142c1c03150074009892a1155800c00344010304140c1300354141940c07141001c8443c480600d90300080d00b030255161340c66002d030b80c3c81150000008484c0c40d03c1403c520241c13101c03040401d595121400e08908885840310403c00c0700c0c608042c4001d0030344079002040022a101030704081038001c03502c0d41e00e0041c0180d0041000003500c0c814081164400b451803504203504c018040d00740d14005100741d0101c03980448240c00460b15040d18500480c141d003520003c4004072000341d181c0103512860940b50201a20b0000810b10005100140c0100861044005034050365a440c10340c4009402450203204004622109014403000280c00c42c86403240b03414036081140310034403 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 342577293 1250 342576043 342576049
    0x3030301090e190503041d0f0403030e1002030906060306010b0307090510091d0402090a0e030301140607050d020607030c0905010221160309030c0806070f03051e090d080a0203010f03030509 83
    0x2200169a09a08000d14100018408040058010399808001c000c0820204407d03c180c0540c3c01d45800100c4504000440c0001740250b01c541c01e00c2d2801000e1311a10306108208400302d030011522040039400c07020820185290501095000d006400c40f25410b40c203040500074880c1c4110301826029503031720205050b070300c7e000307600d82c000414036010a5040814070780d1800c003070710005407000c070f0140d52102c020400700b101c2409030b00030511442004600307680c1780280050000526000c1207030095401c03c42a0040390081c400c002001c501c5800410b240e08143d07a004045800c0f1914400800440c0740c024044d9a0780421800d601090745e410480c4a440b0302040c0003414401c400c0036070b80300d840741c1e1503000170942c00001e10000c6a00860004002c1552210b11a8860408980c1d010020f6209001c40c40e550740244d2006401074150400010491411100207001440039036040c90b05901916100c005039602c048402c2e88243c4a05080d400c2d5490305549a035041481c0c0801424001c01040c4032600707417 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 342578543 1250 342577293 342577303
    0xe040c05040203070516080f030405030a020115051e04090501020a0203040e0f0402090f0a06090204060306031401020703080103030c050a0c1205190201200c1306051e0609060d1803031b08010503030301090e 90
    0x1142c032150f020327941c6c14940742c0540d580d401440c400001d0b5081c03034070803500c407008850b203042201c00141216020307103a00c00da00c18000040740c0c0900e0f07000c3e644078840c0700490001d10103032401e089075400655840c1c0c140400010484c50003450402030314a09020440182c80f40000340e9007021302c0080800840d102d02190b01c02601003500420f010714404075001442541c1504110111790140140720035101480704400d090b03208840c400340200d06500010000688901891011107000345c1c10b80f090507c071070342e4030540d10405901c00300450220f00c000c4800d08c0421f209402c01c81c55014400700b484001680041c003160094942e840c0302451403001501886028450340000e00030040107064803490a814907030092801e070090a02501450044d680c00b000c04c0300d01d941e06848000d2403141060b044a00300704559010440041c4c9150320b5084150b88190f69807040034030584070b501c01042401c81c05c03090b2160308038042815010000d041d03004000c22340340402240e0547d81800000308540428004540c076103 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 342579793 1250 342578543 342578557
    0x2060c18090a1d07051801030506011406120901090326010e1e04050d0908030f0f0702060903030d06030b060312070f14070312090b031909020301150e040c0504020307051608 76
    0x541c507071000c1c0e4040810042a130074240c40e000c03104d1008007203402032590301801090000401c103510903001400110070060a0480002e40109003d00d040821440340c0c1504030107440e10302d4a07130346624980007003542240c0c7e1035840d4090358140100300c4550b66910440682d042c41020ba603030108a0128203400e09100a83d0508050640c2c80043c1d410035241c1141c2c8c0d669101400d4000420740c103c00300360300f607010045032078404260b070b199810034510140400c3c582e80000022030340454100800038103500c082c006001e0840c0c40304000a110b61460800000c0f8020080511784281c10008005c418070340007002342c81500e034000388400701400451900205220700542928240c1c4101c0000000b04240c0c0c041c0329000300aa543c4030100305995018001050005a07000c00d42c0e0300304a00030202e0301006502118480d400200080351a1140c00340444004003039400038100006114204014401400109002840180c030708616514001c40300800780c2c05007500000700030035003840401c14403043d141a00c0034 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 342581043 1250 342579793 342579821
    0xf11070b101505040302090f04020a031205070606080a0c05060f040e040507030507180606030501060c02010807120f020c010b0a0f03080703140f0307020c0a0f06030c181502060c18090a 81
    0xb180288000d86141c0051100700d2040503c400090983da00118841d03004da0380c05040e003c182401c66030380c00d00c04049143c2d0301c0d007003000030b00c200b202003136983c02450001c00c2440050420b00c6d9407401d010203031401c10b42100d03000d014200046400401c4080c1205c08540c8860300000c1d0b030707071601d2422a04088260380094098407622101103541140040540381e1040841420481c29039500c10540035980e0034456071002c200741807100c0015500582c0c490354030041d60302e0310f94100300701d9207405000c41e0301d81d44802e000c032079020950704043e0100748581c1d038507043c0444011400d01d10b0004000c00003401400000c01107040070800608050003400050413140116140c103850394401460780009800c00c40d441001403103400411880ea0400415001c10317070354141034014034142841d8040e40503101ba10300307400810845184402c581104165801c0251240c14289141002d55450003842c00c6005440a010108100034407101c0d82010400540034000a41c1c80000c0f60b0f403050120301c01070040c0e12841c44 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 342582293 1250 342581043 342581069
    0x110114070c02040f110a1d0609010807030b09040c062d050702030f060a02030604050109050411010e0114072012070e040201050921012403020d0203031308060a0f11070b10 75
    0x801c0d21284170190001c0fa8040d69904d07071442603102521410300b48000c034543c01c0380042100f2103c55104000d03041d8490b00f1390a0100e0005c0460b80801c0680c07904580940700c0141d02c010501c609944400c00102c864651f8000e40c4000c494191841034610800c81c0e0801404000203410003151014010090300560050940c4c5c90b0f450000401c0003e9801110b0f40b5124074500030000c80e110329036120341d40c0201d400030f2442000081400c01510424610f548441c1804000c86841004802010003031850511900845080b620390b0b01d0066280340c580070f29588602ca0240c1000c09078800018200c04540b2414040c501c103813914001070744c00d8450280002e41000f801e5843d02ca480c0001d584403d403200c0107800030001c551141704448440040e6000001c00112030141c1000546403038040b002c0c01c80e0005081d41e24250300e400c40c0e0101d00340907501085964100301c00b040310240701391040700e100d2001007409104044007515562400d128070080285030810700400703c0c103618080024030380a444013882284c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 342583543 1250 342582293 342582311
    0x70b060d05070b03090f1207080a0806032a040e1203070315180c0e030304120204050a2c06070507080d050a110a020102041802040806220804090c110114070c02040f 72
    0xb504d0786c0c070042e00f0791000d00c2a03214142100c0130300c00803a00580d4001c0c14007406c16060000841d4485000b84c10540c0c107204030408e4229510381c019244a2a0080320501c0384903465000034007096404008400e005a00100010311803800024101c9902c070f020f620b40000c4e00d08a100007000449040d42100c021009400003480666038070f98406041b4160300d03100d0b1340d00d0032110010540d481c4038a010b001d50400650211400500746500803a03040b50541030085034844610707091312000010300080c00c0f0000110104002200b0007444503640201462404520b081c006807070f040918421620300202c08d80e5a500001c2e444401688414407000303c03128211341d039680d0f0709030013800b030340080c092402c00c0c40d00c20202852a0b0a01d10032501101d54180207401c2640d00d000310320580b07840f01d40d440b1a502a002c4840c0c800580300d0780041028041c01e00300022114510398004003c5e40d030343c1f0a0074010b680340003030f850003405000608030b50005048c5054412410144042006840d641c56400c01c01401c1c00b20314 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 342584793 1250 342583543 342583561
    0x30b18070c15110a031b0519050c0a03050301150c020108071b0c060315050f0310050601090308030c031009020304051c020f1b010e011b06050c070f110312070b060d05070b03 76
    0x20300c1000d44541e0f044c03002c0d0100c001024544c00034022806c0101b41d0400c02c0d000c1034000090400e02a01c15418200c0c00c2c5505203803958101280054120000f400c00401449480141041055411980e01e04841c20301c1d004d50001c2d09468019000805004030300001514450102134844026079112009004080c0d03103034009409885801e400022001407401d01003500e05082019900450b001030040101d482009a07003c0180700150486040241c507141c0403010a060314029401080c000400c29a649814108ca1315884213607040412071500410030711004c1480001c00e403841380403103c0c008800d241c8413a016460412549010681030042c84d2001040000200e00410901400e898150b8401035081c01120032a61444d0070a10041685000305c001c510242d110b80d511070100502d2900e02003046d01e8201c424455544100c4412038003448540c070034281800700c640034840201c04141042d07101d0f47c42000e42c4400402c0f0501544039078a60000703002c0d0800a48004000e65174296503241001501 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 342586043 1250 342584793 342584797
    0xb0a03080a0e030f0a03091814010605070506011413111b060406180209390c010b0901210f140a030e2b15110703030b18070c1511 57
    0xd040d109000d529507411340d800e00421103042d42503043d6150364605042480c110740061803c00c415034225594010305421102180030507000c4c01c22500c5081c0c80f640c10340b9200340351000c160041c00d140c51104040da40561914413000c1c8000050303035008280840807545160302806004600381010b1141c5d5450103a0300030103d10140502c1c09079806204180038090120441c8e00800c0009400c054460006010510088824899048146280d15968815260007101c02318501c08150840c400010401c5185409109040140031705440c1e100031907240c201c20342c00c540d15040407094881d40300e01702407081050004054041e130345e220f101218040e001c15602c650320105000100e01040505610ac2030310f00d0308100c8080c000ea03d0220780b0728401425008283e49500d0f0046c00c9130b10039813071040c09140d120302d4000c1c1c40108201207460b9480744002d0400509541443c01c4003805259460313000804a5001005030742d02504904207000c2441c01c5151101e818130f003480300c8140f140d2400c1c04100f400381100c40 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 342587293 1250 342586043 342586067
    0x9021c0606080111090909010921020c030f030d0213030602072d11010c0206090306010b030a1d10181a0601140c070302120708030d020406030c09180b0a03080a 70
    0x401c10801e926224420308a881034280c51985807400e0028203d0b030b107052119651f00c140c00702d001080000c1e06680c0c02c0c2540014103262418002407003400c41e209581003200c1c0c1c0c100d9a08400802c6100914080030344c59104503406114015000640d00c01c1c034841d000c01c180c0007140c0c002030840d03131590b460a01c40042001c100702c02c000003014074114220450401c00020704150080440049a58000b0055409551f000812600898140100c070010b80c3c0034002c9900a002c015000d956a00c1e19031292001c131551050b24142245103881201e000c41800103845482c102081c000240c0c0c04c41181e01e01080090149005140c40d0341ca9040400f90180056024000c032000c0e2602081008482c07403503d00e6014242c42c4280d030394001c440800261621458400ca03101c6400b007070303500d803d03201c842c0d803030a661000300075100042c0c000608009041d803503c03c482001d0b0032454046001810b040e0741c52600c21302d81d441c040000d07842c2c540a5069643e040140801142d100050701e5544030b0000c8040c0507800661 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 342588543 1250 342587293 342587303
    0xe0a08100b010513090203130b100504050c041a030619061701050d02060a030f0b060a080609060603240f0405042405010b040303050d0f1e05090106060e0d030309021c 73
    0x880e9541155000d4016281384504200030105201d08080700c1c100290001044107105003075100240010030701180000d030181500d2660402d140741444240020307160080d1401c66811000c01c005c015104440000c90001c01c40d003404161303a030301c455001400302d8640c1009003003150340140002904a402480300310100000203a13083c62a80d0310f000b0401e10000c2907401a401403000c010491440e4426030000b25085141240080c012810401040603500110341c03d07000705d00c01c8021b02c07045141202c07400e980b004c2c0440b0380f54610328020400c960b14040e403c01c3e030304d17401c069100d41c114160780303034110302d038035418041e0003003001b4505801c1c04019004e607007005403007200203545140012080c500589050301d40e00d1f84a41e240620b1582d00301d85552103e103107100e00c280c2e0b079403070111000128020010751031500c54820100a0544040e403044078005400410365a03d404020091260400b4101040031011039030b44440007040d0501340c000e230804845c0294841109005451b1684d8660302d070704800c500a0b = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 342589793 1250 342588543 342588551
    0x65704090507020102270a1e03060b042708040b0a080106081006020c221103010302031501080606010516120201021c140c0702060d1a0427120e0a0810 66
    0x5900b05900300d101d0400d1110a02090b030718500e40310300c451440c1c08041c58000e840000c8950f80e501c0000c1c1c098030307180f0048082c80307051001002407108038044c9105800c8202e030100480b0400a00f05007031507a8440c9820042400826401d080c001444c0a40e00201400d10915903201035000e00100503401c24060070020481040c0071445172001140d405040d108107400604046503404c0401ca40246d1050003003081d00200b980c102641002c1d0301030b078810314041100951320313541944101414407204000089510201c0c0c4010400d00b8400600c00d074100780d0030300705140c0d07401c1c004d000300d140380803103440280c40000c0310000781d800250705500070000240d00d1186003610f040c10302c4070b100c1171740e290000b010648101140440c00c0c13004120000d2a00380d1009209a141425000200007a42d85049400c035045226480c103a880e41000c3c00303800d408000c4641c481f08800c016202d0300c598030541550240075116640c810110690041c0e032280504030000780840e45107595542c4080d6075000c4104400d0f000c0c0e0070 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 342591043 1250 342589793 342589801
    0xc0313020a1a190807091406040f030c030201020c010809030a140c37050319051303060902040b040b1e01050904060f031b0501020a030e030102040302150c0657040905 73
    0x11882d481030003911a031b9658411103180100007000415200b190300d078003e608100001d040740781d10f0b10500040d441041405056417460002a06100c1c100102c50705002e1384108200240f6008400c070780c50560315003440344060320104023000c0c3c0c074059028814941c0c400c295035407050740c9000d10400d0460714524110f12594080c04920001400c81c604010700b00c0e4001c1c4030722440e1030128810341861500302d2620324102800c8204100c4039003900e62040e11016944d072084d50545c04e00e8000e0710010311098a040c8285140003020440b50131250090014112034001c480d0b240d60b00c1741c3c080b55082840103006000c219180c02800340c644000c0c1c0700031110b0f45c840c5c0300d508181e413805045100460700141c002e020f2000260310705850301c1800c01c8a5542c1954200000700060703070340402d460101c00150514580341c80400000030714203030b03000e0301030b84da074290804495492680c1e000e51200d001d10740c104c1092503007400d4035a0f10f0207440c102d60f213401d4a1032030b0f01207100040080e0b80070340700700c4004207804c0c401c940ba = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 342592293 1250 342591043 342591047
    0xb09010906021804051b0d1a03010501034202090a0e1e1f050907050c0607081f230d020d06050609070e0a0e040311071e0e0c0313020a1a19 61
    0xc08170b03000c0031000c14140540e01c943c032510b500c0400a80c1e023840c040c055115072600024210b0360240c0085a003c0d2060902c0781030903415500e00d6484890b900d032007240295403083d0000841c05611822251560005144e02107030319030f0070780100105043c1070301c16214200b040c6035107211060400071205811150001441e40c107448050105c4105820794611005c0b0b003050240110220010700346801d018007004116400c030710402c441445800b0f00d960300080c0707007400c1c1d00d07140d000080300d072140300079030000781040c00f20101c0001d10280d83c5001c00071840e0181d031405c0114100d1595510f020f58404401c600400600001d9041f6a04c1240e003116050401e0340c500c03605885540c2061b20051700519412000c2c03003080c00e51100c181d003050003410035004c02564221003a14215080d00300c807581440741c0804403016403c0d01158805043c01030307207040546c030305108003444da0b0200820700700c800d51340e01c0c0e180400c0d9101c0c03016080181400c40008000c0004601c1c005000350710080c001100701600321911400f0074 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 342593543 1250 342592293 342592321
    0x60a14040b0609220614060126070c02060d1a0603100603021804090f021009061209140303041a07080708040f14151008010b0a030b0901090602180405 66
    0x29408000550282c41e200d0500ca00710f40c006105003103844007401e10034030030751251008142c0300d80700d004003003500518502c100c032aa1001034100740c180070340740b00b201e18a0b5810340303c0649481d000880380c0e11360390f503604011292141c0318000070350450400075442c080400c40d908007a00440d030003601440e030076040741c0c18402d841c401100e072407121040e44141802041d202c0c0e0010940e52013048004141d10100394002801c80360b100c8011a030500e03050b01422b0460400400155075001c16042030480917190840145c90507100b4030001a04941d20110401041000001e00003060b0514003125201d00d0589000356150811a0a60520b03100ca0b10001d01440d02c541000ca100e8541c541d40c030b205545450750f508610031210181101d9140e10301494000c808010055a0450300d4298020768041c03c0c1440303601d82490168001c580f90303904100c140402e40c0c0302c1a481d02e0440c0c1d4040344100d550303600c903140d0a00410030042c004104500002d80450348241c1d11004280251040705c003040f0503250074103154600 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 342594793 1250 342593543 342593551
    0x1e060e09012102060c0a150506010903300801140f13180b07050a0905091b0c101e050f01030b1302030c04050a05040c0e040c0e09010b040905060a14 65
    0x105203801444944091030442c81c5000c0c94540b08902000d5690005206400c03440314001c45a010f001000240240d142d408159161030800800c1035007400030009000321501e010203002d0500c3c8102c100d1280c10702c105088201d00490114800c4500c4441c4010841c480a100d120a10a64019410a185440383c1400d6071a0801081c0e07414000c02d4280c494040c101c500400003c1e80708080c80040800c0400312807620a656640d15147c2d1090018405803148540c1d82207030f4003500315001007100f0700030003208002c5901c07992884141c8032203040d000e082c41c14901d109116506030070450012000d1402e9400300c030480080601c280103503641e550603181419024840070745600591008903181d59840c02d040580140060240d80000349444085016a00c0968052030042c0da190200420b000898040e507001d050200310943c22800c103600e442080c0d40c0c0d240520b500f00c801d08008145249000d600a15050303c2c0504140090100c034244503450740411158800014207002402c02c00c4500c81321002c0c41 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 342596043 1250 342594793 342594799
    0x170a0f1a010b0316031a030109050309040f09080f07080c07030809210705060f0409020f1b0a03050d021312030f0e100518010c02060304110f0409081206191e060e 71
    0x1c1e10300b8130320084018182c105040c05100d1a80c1c02000c4440d1800e000c1e216490b4000c400959540c20b00310300340011580200070304042145054500000a034100045891010480352640e482e140982410800c52040c076800070300f184154540002085416030142011082c2101c1c284190940003c001c6076484d503c0380c2d00301c400e070046407003400240750840142464034803080b45d40e400c19441d00c01000403607211940903145598003046039113116034854504182440c03d98040c103040c0020340d070094558003410b4104180160040342d12040d11401c0d14074040100325414810b42c81070704504010b440c100c0c21250701c0000407032a461040701801d100002850b0010140ea400e8504503060704000000c1405c1c420a81c1007000800b9641e025a40d00c40146010310300a200c0d49405203250001c0065403c4104102801107007840101000301d440d44058843d5000082d0344c90103580d031404001104d41080b0b1105801403c10780c080403c2c03041c070309056003141c09005c0015080d01d6840301c0003a2001c0c0c02808101394 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 342597293 1250 342596043 342596071
    0xb0f040506211e1f1d090c0a0e07030b0f091312030b0604120602040f030c0905091603140a060c03060608090606030d11010f092901030b01170a0f1a010b03 68
    0x412800540e078104580c000b040c0441c0251751280c01c50f08041a1880e02005184072040034000c000703030140440300352200c04540203d40940f0300545034140302c00c02018401070650729152030140e034580c0c107225180101c0061034643c1510b004032040d40c404e509030f07600342e480d00038001c0416403860285c402c80025500050005007454a4007449012001040200700c80c504e07028480041d401e882001d404001c0c51240d2442d030039543c02d100414041711001400c0f0102507000e40c03a004407044004900f40b040e25002603103802000300000d066031030000f00b510b00508680c80c15219030300c000e80c0360b8011402d8807201e9481c402c040e2503d800140d44c81c1410740341c1c0c40c0d0580180c03802c51031b40da0180281203101c40c02d41001181f803c20100c2c5502c100c81c44510f080c1c40c240b80e200070596071001060321580c0e0342c4650009110b01c0d941507490703e110104d4140180101144095800c0418400400103006015440f08981e418420149001011a0301c0b5085c000d010840b10301c00483e94200360000e072031090b0f80da00002c00c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 342598543 1250 342597293 342597301
    0x1206040509030316020708120c060702162c0a0218090402030319090e0a020703110a03020c01140906040803040e010510120506060403200f0109050a0b0f040506211e 72
    0x81200089040e283e4107504c500e41000038040c030280f110428800b00800c0964403020480189c9050900040c003200440d0070111405400e520700c3d124a800381c903040006401d90201c2000602642e0320411000c411025144040000700e904580080541110307000d0030902640548091000d24141942d00a605400a0000c0500940b43c12140950122549030254210b0398490080101030801d60351242d0181d000038030401803581040000c81c0a1148100410443d0301c540c80c025250028440b18a0402106102051a0410343c2090340d501c102c00408140e80c4554554005980e0351180c8584100b446804000040c01d00d0706440000c1c2010f49512400b111a01c461400c0000f404000c000560002050001002003050001000a032041d0b100000c001c0d04080700822014100c980031013410418480c1040c40107490307107001041240c221034601600c9045017110507070307280125040030350070034408100310f201e02e1094841c08031001c00442e0000c403e91a4019001c440c2581c8552182585000300301003 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 342599793 1250 342598543 342598561
    0xd08010b0d020f0a020f060f04020105121009060909020a0b121b1c0506091510050306040f020c030a08011a0301032a06030e060901150e07022112060405090303 70
    0x20704005644a00051600e5203611180b141c6400c0101000d0050b407107128080884c10341004000c0e0801c1508990001c03915103680024400e22030300004070b00025603240070611030b40b000071000380603060620b400c3c4a060f44410300d140040c000781c0010791040000c0640018482281f400700e500740101c81d0301d00c012668403442c042e640060b200c1c815030210a410041c5d8005900350050203100d00401c54400306440c205603081040084010f08130b14400020450710300b01c2a602e0b0042030912655a0500e140ca0b80d0b1441e00040041241c489071710382250001845480614020000b002110340f00d80310460141d0300c0e07805000e0044401000360511040410040c0082010b503011a401c080c0d040c004d12000281800c4459040200f661050300480d80342d000a1400103410701210342c0c09411070000304084480311262041e0b0f800140300c3c810346082c1324400318002c0d41c424440017041403903c05002802141d00d081501d002c0d407000e001e0501c444501c0000c12014034250081031b005044010007541580c07101024 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 342601043 1250 342599793 342599797
    0xb182806060c140a08030c0d0c0806030309010c021216080607050304050a1e0606081606020102131a1318050c07030c0308180105010f0819170d0e1504060c020d08010b 73
    0x41240fa44604810301000903014802180b00b024a00040d030b860790b213000421029941c5050000081c0a803010410071a9200041520401c00092a1996039946a070010070700701a1201d444070001e009031804d0018010304030f0420003c035001c250803034807565200c504c210703400e01040d6001070054004803200c0b4003003011104440176480170500a1a8450001c1c0c0d980c0080b034810740c2c803822258001810180245070401d030094010311060000b54902078040380a50307000b246a0007480184580c002000c0b0701780b1180400e6070780e02e10516140c00704c00b544610391045060000720700d000b0540e0402000902041000003610354099060700d45175103090b890341d030030f4480c017000900103828160500c2c0380e400d150b002409a00d009050703114862100c541000c42450410900004410b80079000c8507a4000086508002c00e800c3d80006000640b20101c040000c009000c0b0760950904920681c0300d23a812130420240854002c501c243c0b8208560b04074124140e0300c40c0c240c1001a40401c2122004000311001c00e80 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 342602293 1250 342601043 342601073
    0x80c09090f0606150f0307020106140a03030503060d030203040302180108071a1206120102070812070305060a09200a030c17010f05060d14040f06150302060d0b182806060c 75
    0x100c3d45e0074a50700250000351740c1c00440384040140c2d111502080b0f5000c01141d25030032950192281c801300d90660310040c103988000740c03c036405810400004400e0503c2032040c1c402950b8002d021b0152103002440c4010826401e018030500b07401803d0001455204c84080d80c132508010641c03060404c9a0409800e111000042001e80c11182440003101d2095081c0b009002c02840307140707010f40b07074100081036481401c001042001858541018040241c0d1086849030843c1c2c4c9110010070381700c1d024010781c00d0121030810140c1824102042c8214010b03011f4020864034001941c64a24600c10300040c81400c0800388a600b1646014850500040c01c10b1401070440d80a9031002081c0c0c1c07444c2d40512a0600d0f8215010355005400a542d1020062107029065081e28002e0081086a080d600040e00c544200e411840c0107a0340e5203603e4000e83c5407112002c16250380f40e4400c22142c0b170301103001c1700740c92a101e11100144d5440076201940c030300d091040d5400e4403c603907100c1c409003440d40d58070060840326030 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 342603543 1250 342602293 342602329
    0xe0319050d0b0303160b010b18060a030216060203040203010b030c0108130f020d0809011b0c09240303030c170103120e03280309080c010f050f1201080c09090f0606 72
    0x40b141040545080000340095051081c1800541803a400e180c0c100c58410703040440380c00d0341045240d1041e00c8200303207074000140481d401ca90307070041094264002e04c030301301c000c1154800a070002c0043c0002c1d80d004c0c510031402175000b403140b0b40030001055202c0044400103130105140c2408605d0384860030074520f11162144854180320012500010102007400300200e42d980c2e80020107800340e590103500d4a1084001c554a046901441d681d19030f4071501c0341c0141030086581e0709044098042040443c035601c410500c11041041d00c9044c020013901d40c2802c02000b007072034200513030f00b80000319038524100e1ba0400401c000c1d0103106c80d0200e0b81c070b1020000c2190315100b0b81a20707010b82d0844000c01480200444020347d0b9005040ca03001d030000207550f10180c1103400188c00ca030440d0360000c1910345824414a45642c0e90300c2d0420104140c1d0007258580b00d0034a08034000401c07104000201000044002c9680900c15a13a102c2c60907a602e031a000c82404903084003000c07400508241348900c2c90210b40c1 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 342604793 1250 342603543 342603551
    0x23011d16050d05040b160c08040b0d0617161e05040b01031410030314030103150c140403050304050f041e11090907080403120b010e06090f030105190e0319050d 70
    0x182e80c0c44141d840651301918199681c0052000c0b10b512079141d1540c241d11810b00103080030303040c0c03150849400751348218a800000011000009402a480f00c0080e180703514031442000707640c542041d0707500408620007820000d10040401d03104000f1000c1006000c1c103011002040d4103200030321028209491045052507203425030210b0b5030784103001c203902c80c0041158180704140786080c01092686c284c441006051030800c018008954041c13140f40c41c442c00100c000ca1000e810690031184107c0c0140d00348100400801c000c030400001000400c200e41046030404c000d1100c0c04200803c0361085104200e03070420040c040c8101c80305a030480d9041c40350150302241000d801c0310100b480c8075022a5044005040c0c5010030003090703001402e0201c03840800c4001c014100c00030001800b0481d010300807901c6240041100c00c0740d80d841070181814208094003e10003401c20600e480741c0f56007034055040c030b0710341130080d2000341c0365000068500419184504130081205a40c1c140d419a1141407040c40c07854075 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 342606043 1250 342604793 342604807
    0x2040f021b060403090509040b130c15030609060b090d290f01050306071107060c05010603050304060507030f14090f0607060905060703060603060e010501030c1223011d1605 76
    0x2401e030320a41004890040d01c960318042c90000c00846a60700b100d4402c081000074007021a1074101015071046c407170300200d181c4180508001d0384004a551040b20090001801402c019615400c00001c88111540910110f900d481e80d142c041d00442c40e50640010072940e501c0c0200303e030340884402c10350921641e407882c1c0b802c2c80b025414420044503c82c00039500c1c2001041a8181041032a9004e039107841e107494a40031419659440c0c5180d8410041044030121440c4240402075004a000755070001c00c6990301c50351140042c01c0c40d0400001030300860680b0000c2c20b00e840c0a0340d1400003240041004524011003441080280380e02d540d111501302c60244160f00c005559840780031803d0740540000c0c500c0d0310f00460b00505680d15900300c00c0c00c150a2050400c1000c0e1366111103410b454007401c0c0404d03c00c4050310308440b40d440c0c131001c10078400d05200101c2e600d001d2040440c01036002041c8410610703a01c481d24507840301c0250070340306003503143c000003c0c10041c500e541c0c45414040e180b0b801458192 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 342607293 1250 342606043 342606067
    0x12071101060b03062806051803010e0c03070f0602060c1803030a0c0b010503070303080406090201020f15040c09050906040210111002040509060d081803070308040801020309010509071202040f02 85
    0x107825000400072920000a2225902c0c0414658040381240c18110054000341700d11008183c02900c07902080c000d0100e1128a04103003c10300c440b214001800803c401511032000650310740d00c0c3c01c041c41c040c0c09051408202c89021441d0350056540c43e0300244060b8550500580d0a40d0043d00034549228140141c0d01560303805100412070400c255485a40c12102e904050050358810703403006100c3e504ca000c0400000360444100e543c056044840040c242a0900060f820548412020324203030281d203e11000c00026440a00c0c007490040004481e80c235180d1030701c841116800e443e1000140d018800041c0189010880c1c102000c02a1800003d00b041c205885864050305001d2074101a4000c1000c1c801801c0040c007181c3e011404846000081c040c980318004e40b071140c4100302e080520b600d801501c0548003000344400456005801c6582d46070340c0d00201d03000350001d441000440d420304000c2001c0d09800512001034440005e1989940034481d400c100c014109510040d0f0801c1d024001182501 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 342608543 1250 342607293 342607301
    0x1021c090506220f15080a060b0f0a1b032a05060108010c180509060111070b0708030406050915010605070c050a061709070b030a0905011e1a06070812071101 69
    0x41075040c5600340e141200f0180f030a403000903049007143e441d02010030440d4030780f8641410094038850900c0348041c0c9810041001606070340c0c11050505c0e5000034500070b80055040140700c2e42901d6070b13036840c414143c03101c001404c034042c0c48017400190b8034020903448209800001d03001c2c1c200300c07072031301c0ca0a0949139151810044241d2084029940d50720802c0000c40c1c1003204000b9010300a020003940a0412000412254000e8045810005018411000000104500c0d00075011744600700e82c5503400c502d8041207a42c001c541c21207949040c54041603e001c0b0020765250172070118051982d482e800e01c00c7c11181c4da082480213942c0d0f030b00d09090010380d946074000c4c3c80000d00340c140c1d40c44a0340d005107504c00300c064802038a026401c0e0b201c442d0400c0450390000503070b42c02004444003c90216018103006000d0042d0142e002c030860110380c11120010901c1d40041061074000c8285540704132040c0411803a409210300180800c0c1d0304012004041e0a0b508026501182034104030b0b1102081d291101c0c00c43d = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 342609793 1250 342608543 342608557
    0x80c0114090907091424030702070f08011d0a02030606010509032503050d08012312010528020a0c0b06120a0308040506060d151e02180a050105030601021c090506 71
    0x104d25400d000384006481e035038a01038450016a143c0726600c0070607210740c8440c1070345040c41002038008404100054800c0c4403240040c030076010f030030747c1d419295034607607000700307402c000310040c904280407001417500d804120103018540080c0130300ba0a0f51507100641340380d8401c2582039414001e466044042510380c42000204400405c0803990884c218581940307880410050720040c0040100104000d0740c005410b00b035004401008550321440c0000460b85c10302031000c20074010350902c0708202c821110b22030240c1e40054644500f51140031308403040400c0b48903241000b80081c504d02c0300d03407010503040300c0718680100001d01101180304038501e05901785006d00e03400b100060104400c2c00280407041089507000f01c011140c85800942aa645060301c0b025210003c103100c0d12803c20a40c2c80713000300421001ca80d40b408056650780d204103484203031840d000d10000d2007001c2d000300208081d48202c080e24841c08040e00102800c6000702114564540d2000f000000c01810401c0451140c0b0303448050101 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 342611043 1250 342609793 342609797
    0x1b03141803060901020c07032604060c02030c0405010819140708060403030c08060a0306091110090302090a061d10050411030103030219031d0a330504080c0114090907 73
    0x30144003541050300740300300a0541a81a030060000900442c1c01150b4581180c4d84200510b0030000c0d040304c00311210403854008228018085400191250007500d0000d00030700c02c43c240c2c0c80b440c0e030b11810041144c20a00072480c1c95800080c83e141c9241c0b9603110f00310003e002d1403821340100d07030001d45a86000c203a500f010800d40c000106100c20150103000c0c0f00180b07461821712014138030f032082c0841c0b4580c00b2803101800080d03c5514004c2400421001c422001c500078240f507044022506000e0142e03034403807000320300540c50a0001041c0250521030761007969039000745104811086c101140030040c000c4c148050103110800b00041c159154454a81c506502e0488103803650716500b0041c0c204407100001d0304c0c3c940e0610b0480e80000364400c0300000c920300e400300200d40c00c0f12110003281c40300030103800c07003500704056140703081c914400b6250807000c00c40300b8a280000da03440c5c00b208403002e009510850809501c01513401100b0341c0101300391500840181005400c108104002407040c540c243c0c5d2140c0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 342612293 1250 342611043 342611077
    0x90909031803240203060102062d180f12030403050703020708010609050402090915070f03090209010b0d0c0903080a08040611070c080c030a0203030405040e16081c09061b0314 77
    0x1012501800c1d03110265a0510f00440c1103162480010f500c40c070004107183c9a0b46101c0304810031007418800388189502149400c903050b4904100c11100100601d110f0002c1032046200d0104034220020360300c10065640d81e149800c585880d5415540340d040b00d213040b0f095024101012825900074803070032000b031801400c042001e05003070050266024019124031000e420a48507040d02c1c014443c107440d0010303ca8a8460302d510031561085006013500c031b400075809810040002810b855280140c00e41503030408040110000340390701a00d114071544802056580306000d40640d0740d0041040075403060007140b002c15007201700b5821650030b610200c01203071001070340501404141020000c00441000039001044210065000281d0301d0145108040c45179454480f0300a42410921044104c4400b5500300f651880e251240903854529109802da1515641040c1001c0d01d8407445d0040202c0d52035854254041c1501030b00440d0703c010f460015400c0c0000c0710000044240180014000c044a41c18410 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 342613543 1250 342612293 342612323
    0x2d03120905010f080609040f020f060c1005010609081002031f060225060509040e010902030d02030c010b0604061202091f020708120c0606090a0f09060b130507090909031803 76
    0xf40c040c92800f00020204051300c0e040100c43e803540106c00d9000364000100380340c20411071000504565104600d1904864003281d02e03242e45400017041100f400d078407602400182e80710384044881c47c1d041d2007410340ca03521604a541140308958001c5400543c0c025018991410308266000300e01c95507400200140d100402740452021100001c06525a8205035079040340d241201c020001e0040600300ca1007135650f039121040000b4258003c040f2a40c1c003a064602d40c003c121000307910398003e08800c0605500300601c0c50b099240c110211408e03203e04e52184034a4403112178212009401c05000b25411141c401c00350300208490822003a51115194000c149090a02039440d041008800410039a03131024041c5480000011981e00d03803003d020b8495007000c2d42d49401c818040e00920010034031403454107200308180400b540109642d1242582c4521004014034034141c102d900c121030120008520103c1072000340c049401c0400114020f00c0c09036030f0b009460182a01e81c029950085550f1503040d07000e1 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 342614793 1250 342613543 342613547
    0x706060b071a281503030801030b010b07020607062403080c1504080403020d0206120108030a110f0c0108090c04060b0a020c03070b070b13060c080109152d0312090501 73
    0x1142d03070016140c1140e941054000c83c500001041c41050301c840c40c1615500c1d41c00e041350701a250381d404a500300d034a116a00d040181100703900380800e4455401810020803030000031400c42e05055030261031070340f41c0206038a0f02e500a08100101c42c0f4107402c0c007808801e00320441002c140256005483c01c969590007101b01c5031030701860005280100741c0040420010413814402e172411039805403400c45070140c0a02c001010b62280903454580c00340b41d04004202188000b001d064903000702d441c0c0009a82c50750300391030b80d503030f18461406003540d00501342508607512a0400c5a042200f84085902c1c1540a800040940c0e0080e040781080c1803001c20118192035042044808004054010300203040c14030b0b248000d50f1007038140c040c3c160185080480c1d8100010200703c906180c1180c000c00410701d641c200200407010030721070b224106040034030042c011550060104111141c100c41050b40074000000000901100385580041681c1c0b00e4001000c41e6a04d90301440c9409141d1350340c03004030700342400 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 342616043 1250 342614793 342614813
    0x313140c01180b0403060f110c0703020109230411191101050c0a0c08131205011a01051309090206071406040b070525020a09020d1a1c1401020706060b07 67
    0x2840d01250b15801005011080402c44050b2904000d001c00d2007800d000301500900f000513107480d001080000d95100d01701d03011a035441034920076a40c41e95200d0392220407200c05000d40000043d05000765004050314a000c5d404013138110501c0c3c1c203950605040c44107404441c0b50100c1c004020070b40e00e0582046900c000e11a00342d011480d207100c6401c05284071130007410349d1410800104074410001e162441c410b002c100240040426402c2009100111b15016019100d05541a40380455440b003100a541c060425a000079517690f00320002e2910780095400504840c802c1a42c020038100400c4010a200c0c0c036811884540c0c550040220742002d283c10541160300910480421070709200c040641002100440c0024058031041c030032011090001480d83c0c1c1c2140e0141d011a440082c1c508946601900309070620407640c1000b0a040300504d003402041060000034460520506d00c03103034001486501c0c00c1170041c190400060400f401d5644403011510160041c020742c00020900700300708080006 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 342617293 1250 342616043 342616067
    0x31605010509031e0c0c030d030603030e1f1d181603090201090306050915010e10050a0e060625030512150d03080a0905010f02030907120807080313140c01 68
    0x1940780c0010f60710485001004c0c1d43d41d00300c5815000890b0000b9020422001e615224010103492140c403081c00043c004009501c0201d02040c1002500000343c50a000c0301c0c2c0306621640020101c0b110b0782e80c801c40e421024200382d0740c0070030145504440c081d201e013501402d100d5440ca818680a0400d0074040103070343c0c05000358604042c18441c01d280141d034416001d00c1100e6010601103410b03116030364540c1c104400144c0c0b00788a01404000041c09a9001120034051044c0c4010f03e00055141c10a00c05003d00c24021001c108100201050a6003800801018030700d08601d10f10f210180c110112601c1400802c40c00e5000a0000c940c40b8031650008114540210b407c1d0041140c449445c008101c0880c0e194102400348a40780c8001180c00509400990300980e21000070450180383e101c5c3e040003034105903030f106c1c014480c1e20310101d07540b100ca0701002403c035040417003682401c1b8140e6413006181d000414102c00181583c040c000042c1000c508440c14484084c09040d25a40f000c000420742e490300742c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 342618543 1250 342617293 342617311
    0x120f051b0307110d1a0a06030b040309060e0a0509010b0f0712020706030f0e060403080702010f15031a0108030f07060f060602100506031f0e031201030308070210020a05030c18030316050105 83
    0x10310310713000050f4500b00900a8111000b0700a00c10b0340c449030994014000ca50028103e00418010401013641c01740c00041030300c005407035041014a2040034000c0c403840b40e004042c1c10401100051002d825040081c20110482103201443c0c103800395501000007a0718010380c80541e10903c81880cc1035010f0103503503944245250108500002640c005640b0403002d0005401d1145040210300601c2c401c0d000160800105401445110f12001c000e44031005d032840140e86000e806003094440c140e5901d6294100d40000004500380884000c1100d12a1b011403021125596a18070300206a00301e8081e6000030040c940151143c1e1580d1810070b801d940340203015a109411030a42c0b02c5c181c01443c1c601c88101a8280da000074244180ba05592031803196103c1c0d103210032040400002010307032000905104529503400e403030305202d86062440c26401a008000040f030004e000113100c000004000d0b0000d00c543c0a40310441d0001c100c00b00b03043d940151841d8403518403001c210014070209019058010f1420 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 342619793 1250 342618543 342618559
    0x18150d0c1b03050d0b04061502061b0301030b190f02190207080322030203011406010f0503040f1e170405180f01030602071b09020d0b030604120f051b030711 69
    0x70038940c80403152801d0001c05200d03000c01c50030f031000e29640c498500d83c1c501510070040303e0b840301c10800f8298100820f00006104000c0014401050400804168908060440c0c1944d0071030399000c4624400a102c0c0459849822401d800440b990250084805a00200603500c030000ea04604180c103c00d40781c0025903004034420000084004100c9000310002c1e4800d88014a007600649003801981e070010754558202940b2009d000002e44c41c40c0d0188509803200c200b000c074054000d17031b4140000c81e0041c240280c04141d02d004640403506869030070401e4080c2a4144105a0358881900418407040008001c040740a0002c2d00308159810807082c1c00b4146221145070241e0801503034001400020700d0150082a404200510000d030710a101c81c0703000c001560b6644640d0607400a400c10301d401e031129420440c1143c200d08004c00d086001e241c101d066085a18440c060a541d2801070502d12410060200008540780101000d072443c1041e02130081c581c1c1c1c44690600720406807184100c40c1c403404203 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 342621043 1250 342619793 342619817
    0x4060c03060b031b03090f1002130f030807020103020f071a01060e0411090d020316080105061519270b0301150f020604170906070f051606020a060218150d0c 69
    0x9010100d21111311000c410503529a69014210705040080107031103050311070240d41d51242c1815801600011600449420745035954010440100030700b403201608818003000840050351013a0014000300c11500310f01450849281e40c0d08034504400c0c500654103207981070045c00740701d03449100743c004084112420300c81c0390400220721542d80b00f60f00f84140b0908411511008648013844402d01c0514804190498550388521260103801c0440b62548541e005106170301c40c008500090b2295081140c0404100070b46034181550100418540004103a0184044405802480f0024000b070414094529282c3d4900240e030003d10b101d00708040207021001072100401c5a00190705540310750040a1241c004035060380080140c81101e041c41d030818030000e0100c2c2401000301a0420701d612440445841002b0b00030340f02070280ca14001c0c103006800014041c00841c0c3c0705d8001c0e114883d1442091452800d005000685a40c0c02181404000717001180b2422003a2461085000500300d80c1056110216 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 342622293 1250 342621043 342621061
    0x9030f140a0e3c151c0f1b11012003040602130609240504050f03240603060a06030201090509040303020c060408041406070b06100c05010504060c03060b03 68
    0x4040641003005400321141280c0d5890360508070768811040031260301c2501c2408030101d9481c0c803018002504510980c40141030401c20207031840384203609640350410700c9041e074017880c039601c404500e50034035181c98102c174040141d485101848082e031f0107410314800c5031203406421001615002c0f00700d40d00d4900c1c4a58100744c240820802181c03640c44140e40e039a0340d458500003d01401115020038640d030b41d030100c0d489400003044015502007200c5c511000b0011040844031028614188001a005101c00c110743d00340156505c1e0800801000c3c1d81c00d208000b040c00c1c1c14124035440841c0c55602d034109000d45424144040c3c2d801400c401c509004890468001070180c082034810107014000b00e90004041c50312a078191b880d55000304054032114142810301e80c1158005002d4800040003002d0401e040340f4004040326262940310072000360036500c2e14200b24042140c6003940c3c1c06e0103a450010030014400b840350074480da2058038001145445000c000703084608541100a0302c144c00c10603c26014 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 342623543 1250 342622293 342622297
    0x2090105010f0216270c02280f0501150e0705160c0e100807080304050a0b0c010e030301031b09060b07020904052811040203070f050d0605090a09030f14 67
    0xc0003802c100540c0b90356071004902e80069050703103415140c2c99040104252070400b00414154441450703600b41000000e45100480c1e5055007050056444924602c0e10802c1c3c11030640c44141120f04104030f1a00075885550580b83c01d0036040710180d548d042542400d01e55142420301030901c5804200113454841c802034030f240300f134070429800960204075110030004000905030140c440c1c01440500c3c0c0c00c0c0031100034082620741c0a420180c0c000d045000c94500303400401c0d58100c0d030303004150299a914024001203a0b84c030030588c9005554a51a0710100850300b000218002c5200345021070589035542c840b00c0900c516600650421400e1200812600041006940d0211380490b81d580c2191101d152961400020103951941a4900107264030481d6010789084450f501401320b290260100504000491004a6400d40030400c103485010030782e48654090132107001c00900c001409030300c8200003040d490302220548070302915000304c10304141d0302225407402003015080c9003d060945e198454528 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 342624793 1250 342623543 342623549
    0x32405010819020f16060b0301050618041502041e0506190e0d021309050c030105010501053114130c0503011401140f0a170c0301032307090204090c030603020901 71
    0x24601c51102c891121082c0e604403240b48518600555031040d01d000c060041e108020025a40285062080005c0b8103040c00341e00d01c101c030014140083d244001c400c0301c0300e1200240c02a142c40c200301c032074400402c0051004001802090450b46c0c5081440031900d51200380c0d6070030003400340006021020080c042000c08111100040c02c110401c1305202c40418103040218001941c850104608075510100700e6000e104681d0203282a0350900c11030406041c01d0724000c4c8500c41c00200101700da40b40024082c3c03000314442421f0b100548ca840302c2d00d2500c80c1c248055402c2504000c600c0380d40b0a000d0300d0112000b0340b155032095030500600c00121006005404144140c040c40b010000c0002c815030311406140e02c03103030743c2c02040b5611003880f00c06503616a00102030040c00310350450701d40760301640e500388018450fa400c1c034002442d41c0e0035980c0381c0207550f0f451650a0030301000c8d1a00001010014010320340035000b6118010f85407031404a0050649c1da440341c000d02403500d010030600168461405075419 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 342625899 1106 342624793 342624811
    0x51909030516030c0606182a1107080f0c04050106020c0f060d061e030b06010918020729040638010203070c0f151d2209030324050108 59
    0x1f0381c1040380c0e088056400940d2380854141c46418082003000c0800183c0f0b880d15a04c0c10200e103010300807843c00020f41c12240700002d05040070300c5030070700402081c030040c00c400c0103000200b42119503070f802c6140036a200040c0c0074120100303504103500400c0484080d115024910402541103082800125814098100418565841031140300152031200d2441c20b280e056a0800c680207521190342180c441864800b15030503d00c05e00145115203181a002c00502e10301450040121280340c05102104065070f8200004114000120384010031919902e890001d030040050307140d801140c800900a004860021518402c00d24000f000c50b08a501c5801821000a6050702c08140822039008030461518000202d442c068161641601071500d095042d200e510807042c0c1a540d4609060f0042a00c4040c25486104090150300f201d4600c5213403050020304100008090740c0d40070384022a = true := by decide +kernel

theorem cover : BRFrame.Cov 342446043 342625899 := by
  have h0 := BRFrame.cov_init 342446043
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342446043 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342446043 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342446043 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342446043 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342446043 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342446043 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342446043 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342446043 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342446043 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342446043 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342446043 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342446043 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342446043 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342446043 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342446043 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342446043 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342446043 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342446043 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342446043 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342446043 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342446043 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342446043 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342446043 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342446043 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342446043 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342446043 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342446043 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342446043 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342446043 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342446043 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342446043 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342446043 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342446043 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342446043 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342446043 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342446043 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342446043 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342446043 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342446043 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342446043 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342446043 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342446043 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342446043 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342446043 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342446043 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342446043 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342446043 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342446043 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342446043 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342446043 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342446043 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342446043 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342446043 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342446043 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342446043 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342446043 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342446043 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342446043 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342446043 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342446043 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342446043 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342446043 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342446043 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342446043 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342446043 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342446043 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342446043 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342446043 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342446043 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342446043 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342446043 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342446043 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342446043 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342446043 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342446043 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342446043 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342446043 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342446043 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342446043 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342446043 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342446043 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342446043 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342446043 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342446043 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342446043 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342446043 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342446043 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342446043 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342446043 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342446043 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342446043 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342446043 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342446043 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342446043 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342446043 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342446043 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342446043 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342446043 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342446043 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342446043 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342446043 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342446043 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342446043 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342446043 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342446043 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342446043 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342446043 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342446043 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342446043 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342446043 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342446043 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342446043 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342446043 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342446043 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342446043 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342446043 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342446043 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342446043 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342446043 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342446043 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342446043 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342446043 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342446043 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342446043 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342446043 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342446043 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342446043 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342446043 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342446043 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342446043 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342446043 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342446043 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342446043 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342446043 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342446043 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342446043 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342446043 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342446043 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342446043 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342446043 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342446043 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342446043 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342446043 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342446043 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 342446043 ≤ n) (h2 : n < 342625899) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
