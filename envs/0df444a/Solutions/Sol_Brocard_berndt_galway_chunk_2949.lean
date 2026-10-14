-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2949
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:13:10.428815+00:00
-- url     : https://prove2.me/submissions/10adda47-b17c-4adc-9441-ccb404221d9d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 530215827 ≤ n < 530395683 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 530217077 1250 530215827 530215867
    0x30f0a0e0a0906091d030a091e030803040c0806060114091507050109061b0f0c030f050d1e0f060e040206031b0c1c1b021207090f0b030706080708041106 67
    0x40d003611120485810030304170109114103142c8030003842c0b801400d280000c010309040e0064a94814650540349005c1e0340042c032150145501403440382d980d0506007007111801d00c2c0303482094013a200e608002507955214011030781141101c551f04909009000d01000310200c100a070301d1071402e40500001c40400d00c2401104005d41c0100800180f0b0030102e0041048000d0f2244420f060020703e2001d6a080da070712403100c0f07200ca078140c030b84800d00e030650040840b03080c41000c0109240341d0038a000001d135040300303401d44120100d105504000b01c110010700399050301d80f1480f4143e5a100300c0d400103400740c20440001c0d81d02501003020303c0c0d58000300d04a2482e00d500306441018182d404200300000210448030360902c1c0445500f00b0402907040243e641c01840b40800c4d00900407035040e8040c09156108010342e50107091005400e1180c14540345141005114100180e403007840760700f20005060340204a180c0c020380c1c10741d5803e007039aa50f50311818a0034640008498118604008544142410320413a42e = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 530218327 1250 530217077 530217089
    0x3a060306060e01050604080622020d060507020d0314010902130302030304090b09180a031409180402090c0c0d030209010c080406121505011706030f0708060f010602030f0a0e0a0906 79
    0x501d01d420103810000c1c11405130861400b0b150200802e108600001881d0340d4008001101c0784070048403503503103840e60841100020341000d00707004120100030003600417500c10740032542254074103800c00c1800c9054451031101406000c03408001403205e03540a4008111b1078180590350802507940340e000c40e241d98026440410807e94550349050075152580906c1d80044a0f41100540444624400e03500e4603c80c6000078244294145802d0f2400706000903204001c000502005900e440603040d01c40184040b10101e1140c4150400119001c2c004826140641d42400041c006000c00c40c0e0709600a502a046460601000305d158000141c1d01100a101030981035880b0110302c101d12180006442d0003040304001021040402d0213941d070300011310005145400d2013010543c0700d8401003420304d0711601d10504680603140020400d0f800000c1c410303024440000c8151526070343c600080f03859004004190012034010040188141c0c0304000e06100c1c100300512036100e82d0f9030b6030b800f10304503186603100d2 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 530219577 1250 530218327 530218331
    0xe09090a050d1e0207060e0f0a03020301020316020114041a07030608011d010b010e01050d180b040602220f171c0201060602011a0d060c020a0b0405031206063a060306 73
    0x30803d030b0803090115240341c3d050009202c49424010050b0140e00c0481951380983d13426010900c0075a14546400c0c011a0050003c66807800c00e013044400318480c11014401660901c20b040820080036080244600e1308003c000030307030f4649000000d02181018240c00e040588406010034659401c1c840c4841c0c56184540c000c1c45401024006408d541c00c03030700134606101c031400c0c40702001d9070014225004003008120002d4004440d403a0b4042102d8001c5010340781030385020801040140b070f6070080c11110318240e058044809071034405003c0703030500c1c060300950316041a402c101240245d494102d484c1c1c1100c0c1544c1c518041807840c50078048110900c0b90050f0745550b810061140c081c450445180d24007081003a9106519001c41c54802c20480014100c40e80c0d01140e0300ca062080c800451040d07405070201841b810070381005035403a00b005104148a101c81c0700818080e00c0d000c0c04840c0c0c0c0000406504201d034282620303203150f501354680f2000c1017500d0030240e109800128410400503520034070300 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 530220827 1250 530219577 530219597
    0x170c0f0313210c05010e060d05040602071a0405070522140f0a0c0503160201090c030305090a06030615110c06041205010c080415051f03121e0e09090a050d 68
    0x200b5420032200244095030030245001c001140c142e560b400b050710000e0030300030303000c07070419012a2803842140311001102e07107084280010170145400800910b80106000d0035101849101d01402172011399006015038440c07001044641400b080040000441004100030008640c06d050706035151002003501c08895481000403d440c8034030395680110700c0307040820201e030003544050503500c40500401200c07824031180303e54a034401d40010075620b90000340c01d11341d40d0f40c916000d805608804520b41c81580300c05004140d42d4402d100b1003040b5404070002854030304501070241c0c1d00341c50a00018019001e0b13000d8200b102e0703c4900042c4010401c0103425038500140342015821102c021403c1410070840000348004201340d45a1020502150700d0001056241c1c185c2c1e090304184006a10b00850060520001c1400890b10202944400645078040031b000c4c92140021002c0c0d1003a01ea00101d4802c5114a8060400c4211260700490305c00072120403a2264803001d203400500b840940c000341500c00 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 530222077 1250 530220827 530220839
    0x60a0e0708090d0e0d030c02060c030408030c0106080102030708070c0615060c020f090601020303010510030f0f0605011805060d0c030f09060903020f032b1b08090c0904170c0f0313 79
    0x305a4400e418245003001c084e12960300041c0c008404444080c0c200054100381c407045d9642c4d131045520240191044aa4075030740d0709006501c9400c032101c4401c00c1d520300100042e4190043c02103d2103401c0c01d5407411510b503140d440a40c0d486c02520000e49015a0314103501d5140e24221107070002600c101c2c4c4413009500042d1040003030001c400c0061070b00072843d4800380318040c1d800005403415076104864500001e85c18040440c018111807188516650600e0009001c44040d540048203441702a80e44c600469130000c4103210000c0d8a20032240c1100c800c000440361700003e85e01041c00440340b4503021410404100c2000152880b51100341c44031940c0304070f00c44c2015010005814881c03d010003850030682400b007a0901c5a04464142e1540e840c3c7c03101610008450ba0700c0308c07007801646131064501075074900e001000042c04840c118500d11440348129260f15000c00c07040c0c455079202404600134511001000307400d81043ca005c901c14482c1d030800c0e1140c1e000500191031500203410140c9207a500e401 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 530223327 1250 530222077 530222083
    0x15050f090a090f0e0111030705090117070513170a11040b03100e0c1807080403030b03031207090605040506182b06050a0506030a0609030212040605120c090a030605060a0e070809 78
    0x41075401381e8907010512041c0c0441000b640d0b0721100d80d040643d110004000103840f03004050081d250b88401100410112580050103825004811581c0d072103650f855901600c00800903804154041e80480030b030300c0000b03141c84c01700100300b1005003000c01c41c0070714140403e00c0e010ad807841c01100991030300f070540c84002040002001c0241d049510340ba0303011310343c60008901900a440c880410903200000b506050003500320801d00c4034081c086a66500b2000c50070f00c440c50050b1f54540004080c0c04001803601d105e0b00c151001d0707907c01800c0c07516050f2103124911001040b8411550000c0b40801021902211030802090741034500c01c0300c00b24080f051410004480703006100c404d0403894941484466100001c01141072941b02400042986140c141685412a50940c500451070000741c00701303109500c84003800c02190041180c80309a103030402072880c14000d0950140c1c0200d02c669080000c1540d42c0c001642201014140c1291a0344031030034000003030021549640411801014003c03442020 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 530224577 1250 530223327 530223341
    0x51c0309021207062a020a0306021216020c0909160b0711060f040b130e070f0305090d02060c030c0f0406052208120a021014040b010f15050f090a090f 66
    0x1450181030f440d0300b0150301030801040c4d2012400381c02001c0c10408907000c0690302880300c40da0018140c45015030b030380c50840041c1d0b001c0071504040680280104640d00a00b19080d0306441ea1034010b4181d41040d141401440c841c020403c0c13045203d0140044102d6808407041c002501c00b80724201e6881c00b8609100f00100c44884005000d480304100e800003003290603098409582e50803e900d6550544400038410100b5550403c8142072042d4050052803600320401000018a9807800c0c49181c1d159401c607030f01c4807016119440540c2203400058810b035259001160702c404010717440c90400c40001c0921480ea0815080ba0000ca80c3c009614401074600d4204003a05000c4a104001c4081c10002c0741900c0c0c65004164030120030300070801a81c4d0324002e00241c0c100f07031840e56041140180c48603004109a509a07820b85056603954008910550b4040e402000c0e903030151060701c1c02c2d000301c44049a03d031307101200c034901a00c014890340300075681e103200840083c2162140411641c10b030034041011203481c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 530225827 1250 530224577 530224609
    0x7020d140c07091d01050a020315030f03090603041a100e09010e150606042d230d02060c0604060c030f02070309030206030406060b271008040b04051c030902 69
    0x3003800710359030140340000e00780191801090045408241e900345a4800d20b00000005619403c0c0010001401400d030b01452140d00c04114100741100b540007850748135810b1428034001032700100a03940c4681880300040d42c10a10400b038000c2c0b400500d042415079210251103060000d100014204402c100c40c05c0d83c00e405c081000001c2051a44001d14230b5520980504080c0c50400c101c0e000468542e500b00507500100704d0a01caa00241a008050260605c1340001c080340d65500c1400106507000101055101030401e2102c12480f81030312400c1105e003840c00d29049038010400c00a240340340c0740a016107401548241c0c030201c1d81414031203010b4242c84520442070613592060000034003096001c54514112901920000d40c0c80e110340c100300000c0c040c9900720030300761030000600e05030301d08413641c6004200d111010400421041e60040007080401d01c010403000a1014001c5004600351401c1103403c544500d0445030300820928990486407000041c81020a0b50f8081d09025070504407916000032030 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 530227077 1250 530225827 530225867
    0x303041a09100509070b07060e01060f0605070813050d030305040231050604020d09030f091a04151206080c0906040629040f0f050f030a020102060c160b07020d 70
    0x252210410781e442c480184001000c0ba01c85002c18030034082031150b48043c03c03440c40b002c2e80e02c80c12420213002074500303441551125860080700161880484070b840003a2107690f568a490414503031200703040f40d0880c050620f40110400300015990b031310001c0e541d071241d100340c4010074907103018010000181c210a4281c60b84401903090115074100c00074102581c1c9502c1c1e00001460b4450784007240c028020500c0d41c1c81a6031400504809058100c0342c00d00c84100503a80348850300c0e0b12185056031440580f085c0100c011320034401400704450034048016622110314150707120017407120410041c0c603000c0d0321251181d0050203103d682410659031090344000140c5041c00003034944600f001c50900d102c041c0c0c00c008445402031006001404080710300420300350180c10751240c0c452001201c0b18080340f081ba807050260900d90b01c503034200811480d5080360140c010308495610b0b8080d40e01c0303d9200e10100d0003600c400078444000a04030140d10b0f40284202e9000300892003070341c0400350a5002c0c59010300c01d102 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 530228327 1250 530227077 530227081
    0x3170f07060f0c0f08070f031b0804140705060901050a03021c1a040e03090108040515150f1e0f13110403060c0507050705061b01360b0103022107080303041a 69
    0x103500300401799000356191800d5003600e291200308500511130048031542008401c90b20407011030b402400580203502514502403152114a02240c2c0d078106403080d5a0402ca040c0030308013166008601502d0390701403d0a01501d070400da600b86601040900e955013929594a242c00460f80e102d18415003058001030341c007002042b648060f21507a030b001d0601494108024480007600b00704040c0110702c8081c400d11001146400c010b40f00c24910303400c40440070700510703080141910718034081075100c1108580440701e007076100809062040c4c1c0b1040d4691a038000301500270400242409103d0342e100d2400661481e83ca50b0700b180390070019140f0307501c1c5103010084140000404100b01113035803800c50b00115003076940c0f800000b094400004a80c03200c1c03815075181060b001d400b05002407103c0e400903400d02d01200540d01e02c07110f030b9400b2501204058400c0200c88014130040c200541038105044443c1a000c1007103010b00f824a19160707154018240ca50030100901080080580000360b0304405071a035144070f4 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 530229577 1250 530228327 530228357
    0xe030310030b091603021309050d0504080607080106080a0c0201060512011b112a040501121a10060c0c031e0308150105090108151e030601090b030703170f07060f0c 72
    0x1c201301d0002a04c583d90f81c0050040c40d034099801101e030b4640c080181d0712000200356010f000703074006200308107090040600081e40075110740442c0e41a1805900c2c1c028254880303040349001856481c0289080d59a2070b10082010754801841100c1d48411400128601c2006060350010443c800b203180b05018001078400e00080d008210100320400d01c070b2190045101038814104202081500b42d41c00514020000ca440c04490054040e054014800429903c582028155201c03408680036040010075840038082c0900c150a8100b02c140600b41c8404143c1d142d40326141000c044401d010352445004070440c0400d42c10400d0507501804d180940700e02d000e031010020341140704800e01181000551400114050716101c0401600c2030090705461038801c10301342c66101c0717506015000b44a0b1051800014881900380507101e20000d000d8003070306040d8910b949008004483d0750082e110b003507041c00310542e005002406030413010b010303000100d00080c00e0845c0390100c03000101101c0420181d1240c207200 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 530230827 1250 530229577 530229613
    0x11a030106080a0b070c0206070b0f060f030714060c0601060206010e070903201f050a02010e0316020f010c060c0e040b010e031510080f030a030522080d0e030310030b09 74
    0x50f0a400c951041000d6842c20400c0340ca45607890170080d0720000c003003600380901079403d149038400c1c84007a0402140303444240c01c0000300314000003003642c585d01018080c40807035624000400002000340580e41410309280e07445e82001c00c02d8103c040140c0c460001001540d103a5030302c00d50000d1040c20510962811901c800403882c3e0b5119041c110301d17141c440d03a04281d460300f0100703a00c032040d4a60301d005200319100006000380e124209990040d820a05240740c0030750040f0407a01c102c01c0c2454104d190038031541c01e02558020715240c85050003905407540c0c0200d4160b0069210146169a8090a0450000406c8100c13041c0513000c60412002c6051017445441c00038031500781d1f01050400100607a507850104000d09029000195240501382010a603041c002000c1c080f1143d4035181071185a41c0c21800c18000300712481048810480d2012103408600d001c0b004140aa8040c1ea001c1504980300188a00c5d50388142d40084211900c20020410301500011584e040307087c0723201404141800c4402481 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 530232077 1250 530230827 530230843
    0x901050a030f0602031510020f010c170402090c0f0301080c15030403051602030304090f0f0b1c060203070215161805010c060b0a0f0f0e0919060b21011a03010608 71
    0xf22090380040418010400d04503032443c4c41c0d40042c07005400d541102002502d4a0035980000c686609115044120900810740c403a004040d206070081140e641d502004101030010307200a0131200208204001c41000c14000c50103401c2d10002030041001d0203003403146100040c0a0846081c50520034400042d610030200e41c0524040e01260f080106d0310300009007507100d21342c850384885240000080b0010741b20341011042200c8510100b20a0055400380900c100c454040c1e04e0240b0700984003a4000f91450b070107107070004084c2c4111820704e22055080814140c064400000300741241c0e90700d00501d40c0c0841c0c04220081e42091428425240000290240a076908010f10040c1c44402903100c903114103100350014440104904403190791183c070a1aa1020360040002e80041a000140c0c50000000c09500c0d551203c51006400c074065100d800040070300c0d0100316030180c3c2d550440000d41401c07008103c1000c4041e0000910100c0302c170410b800c08101c1d002807500070307410544104140380c1d020946003 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 530233327 1250 530232077 530232083
    0xd0e06070b041b0f0501180609060c03090312031e0c1e0c05030a03020a110a02060304060504060213181a030304030b0c16030c02120102120402120f0a0f020901050a030f 74
    0x1191610741e80752450f00342c1c2080604540c200380c005800a034070b0203900300e600d08a83e400e0b22910307000a1506100d000760b0300540910000700e0841d94040190340c1c41441c4100000b402860721003449a100e40d21f0540300610141d02c1da00003500c8046059610000711648070002c40010400c00c80410120006014030b540740e080030040514201000700341c94052400c041d0380c1c80d4030600360780d92842ca000000d4002d4014811500018144005480412100158256031650010a124110ba85640d1400050400100101c542c99000e0084003d08000444ca001c050459450020400745581100000320f981c00482e40c80d00b040c910310214a181c501000f02c0e4143c94028460090590300c104841440340304024009180c021410070840905a1154120a802e407085501000740784900d80400d00340c2c003d90f0320b5140c0120006c004240180307003100c0000641210b61303040c2d6034904040c0140505020300d5080954260401443c0902141b03403000d00c0c240903100441d0038421550644d155144941c5c1542401 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 530234577 1250 530233327 530233343
    0x506040c060315150318050f0f0a05030f030a0b060705061f0e13020103180804150f1b032303180105011a07020114030c370c0f06060305030a020d0e0607 67
    0x4201400c2c17180c0c00801410f042c60640d110040d6a524101c1d60702d4003c403e65054070b000305c40805d200c07554082002012150040300031403c110806c00c2951107a400500400d1040b40e6482c000d40c01a111103002c3c00109000f8405810245403488011250501c0f80c1c131050700804104c0c4091081110350441c040d00601c0e05950910035000704d1005800034101140a074144a510603074590422401030003e00c107803201028252080042c81c3c1050b1100c211300701002c00412300c0814100444919000f2100f00c1502030b250050908182e0b15030150940301176514982840b00000800ca200c0790042500d40b946e005203c000c101c0e42d807415107842c10049280801050009001405805680c1304401004200030301542e201d0b6030b030030009014021984844801c900c51820401207020910b039228500304850045006e0b010760000c00b400c11503500035542011101d40307040d415580c001c00e1152003040c2c090741c416002140d0300d0598460107031401036040f01550400c00040361001058540000362013107582d00041c5 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 530235827 1250 530234577 530234609
    0x1090c050f090a260f0304030f080a090905090109110d0317090a021807030e0c010905010c0c0b07030201020705060f070e100c0f050606041116080c10090506040c060315 74
    0x15107110380e241d00c111a110000c12070921000501405284c12640c5a000c40700c082600340d21450700e9018a2001404414050390b091001c500c50b01c0050110b80614540070b4500c0751521003150407507100303580c40821031395240803003410800000c004d415809411203d003103810200d5a00140b0319000d10f446014100c0700038003c0380198074200710a00c42a603009000c403c00e500e40c0c5a075000600e004590b120001b03428072021a400800214a5401461041c1d54109070075017044015036201ca5000e9080341c000340041c0300019100281001b5003030345482507002580e41d041c1400d00c2da1800d04040c0c003203200c402200702800021600300e8180c1c0140c04064401d145601c2c60304100b0385466950b100d0150203220b4080d00070301048400702d2254070500040307804004200d492110b0b1011406032355050901c01042660b124003052001010b04000100001143c401e01c1c02400c1f003d064030070420b412207541c4c0c0700206100c00c000ca440b203410050f00b59480d040290641e2000325003403c6101c2e1149035900100d03290 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 530237077 1250 530235827 530235829
    0xa0b1c080d020c0f2509090b0f060105210105090702070f050409020a0504050a1409030906030f1506070f030f14070611090a17010b090636071701090c050f09 69
    0x1040300c410fa8001c060722450410041200050000303045030b1072600e02c54420100340d41407107106100c44030b41c000840580310790341d0309c150001c0c1d11400381c0102c2c1401821b0040c08040500c005050800c183e910030ba02509524080034082240c00c050045419900945000c0c80030034015807541c000c0f80c2d000c8401040b0030703100c7c1c00420480f41040d000150482d0030001088141c410300c0d00064014180c3c00c09100e007070755a42440306d459008001049501140410101e00440075684155820081000661540c41c082e800001c9040e400700c002203808040400000c0285134011000805110282c24103c903554421010700403144288400100f140e036072a06018585450b207070a64100d503c5c080d0107803001c03a8454400c2c1e00c0043d13031603503042865070a1890842075418200c6140c0d00851015100004070152030f013294419550010482d4401d038008081d129003d514039155502903189070711650451600c1007800d0385d610105802c40b512550401807850b071151703130042c120b82c00f44210201480c5c840380148 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 530238327 1250 530237077 530237083
    0x60906090408160c0605030612030429040801050f040c060905060a0305190e0703050712080405061e070305030702010e0c0a0b131206050907090501050307030206030c0d050a0b1c080d020c 82
    0x342000d0111a0f44c01c0c1c000c140660010015801807004035201204803c4814020b07a5a00c100e000c0c894000101c04c03443d4048809804101800d40c440c0c1a803503040a4440e4106400c44104807070070149403004009110602c0030366200304000e04800e00c0d00382045030410000c200540308652600c000c050303540000600d41080c02c580340740541038108003403001c483c5c012041603443d01140801e40b1030b8020700200080b40700302605405942684030042c2c0d030520b40f40c401009a1604805403aa50034800d039070310024610700d414028441d4038070903250103842c3e04119000034212001605c180c1007543c4214102a095655020010205c1d5206400240d940c1d80342c08001041404584c00804401c10440d1000f08024103900114424030b41c0c07604845035265160842c00a0700c4082c400c003901034016503001e00141c2012401582d10440f45a0340d035140401014103001110070403500018141d40e690310390700d0a846c02d0642100203440300c0890080b0031006841d002c009101781805a210254000b904980c0d00c1014 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 530239577 1250 530238327 530238367
    0xb03060d0b091f0506030a030315080d03232e0e0405101b0c0215160c060311120f071e0908010c0302040303170402011e090e060906090408 61
    0x2104079025503042985806648541100e000d01051950307403281d24480405202d007502c40c4200800a08a91034142c50580040c00511081000303c0d00c030313203404a42030300200f2851404662542e4002040011a015660f10210900c41132540c071140b9030a11002c221200d03010f942040c0742d04031070441030400200c80d40c51985250b001304448503040040000340000458414a0103100c2c0400344416854001e0320b64440794100224008959203085a501509081d81403198144541d60214a0848502c1c074880d03c0c2441300d0000c030740c8850552010701a29605015800e41c100c45208118140350010140b40c04010000303080004c2402c2c082e00180300c1510440c44c0e407a204c101d50070420906400018000d140707048600130180700390708108400356070500c01d1080b1000c490701503507200000404000c948100442c041c00a90400c07030b0a802410301c418098030700c070f528040aa110030340d00500e0b0464402d55000c00810651103840f001041003065100e56a10640c441e500011055440e000507032406492124 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 530240827 1250 530239577 530239583
    0x111e04050a0305010510050d030f05030a2706140112151812031103070c15060510020114010b0c0606010c1502030a05071b050c0f0f040911120114010b03060d 69
    0x30900703001007840b0041d8032040c0140b0000c640a110240c481d828000d409401c41030080c00284504604500c841c41030000d56080003040c400850162000d1056005003502e0f10902e5039030281591039a81004114440c0c9a00d803803550b60160203a6240c00110b01200301d0445c0080c1880368224070b0190911b4503903000640740340381c008203442584c849080800c4009c071a10492000302c1d24101d80c20102058800c2a07910958040e90b64010442182d51010341c6048800300c330180c51750700c914001c00d0994907024501c801c0319155000140f00405500d4007540c0b048c0c1a80311100e0031004001030300d0b030b140d00400c802c0c0e48004203007040c441003603203840c2402e441823407091944080742c03001c014400d66400c50340041e4056040d996803d24601a00b505228020790741c04002802544001c0601031f070f40c00c01c0821201002e81c0145105c68607500c007404181541c0220b4011202c504003c02c0c2c40c1d901d481c00d80e55a160455600c00204003450b088020804503542c18028102400b001200003a86580e900a078111440e40c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 530242077 1250 530240827 530240839
    0x80307030f0c090b070f0204050c1903060e0c09030a0c0b0c0c06090a0303031509181101020609060f060d02040f0b1903030c0303090c05030f0f0d03020a0e1003092310111e0405 77
    0x640024004003982040208040d01d40b50f0701c48108be020710038010141912500304403049652540703007204040354001c507041c58040c0035900d09103000c01c8440c08604010a040020580d440d21009611030a000710350081a200f10001d000000c0c1d00d0b217400c004070059950500380091103a0700d110f08040c0b0000503911424200782411058240c818024103410009403080039950398130710114005980b0340e48115000c01d4a54485030000f6950070707a520f082c0350001000b501501080355280c0100b0140c1c1d890000c00101c1ca030700ca44d00d68455007043d008071030031010482840c04e00d140c1990740c000c0890b00e007581c0c0030b02055159600602800a000500e40c000e000c010b0413105ca40425860302c40d00e03000d2b000c4440200c1e00900c40b003100014001d00844101d4080c0340c0d0340351901c6120f50200100080450202400c040d650b14000002070316030040480d100801503005d88c440f01003118101d1810307039401d00003144103003000311340002e00c84800181d800d08652007184003400040c1c69040009401a0350015038460 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 530243327 1250 530242077 530242081
    0xa150501211b0e0a0f0507142d0c1501081203010b0d1503061a090c0d0915090c0e0106090321110105100603050a0c0903080c07030f080307030f0c090b070f020405 71
    0x60510317031044005100b020340c01d05c0141c3d1a01801c1d50100b01420043d940f54000704a1009481d01560410440040c10a10700105030840e0303400d14003903004101c070481141d001c221901c0c00c6220200c00d075801064407030000c00da848240840c0f154940410310a03c43c40c40700100b0209a8590140c0004540a03030034041048440e03503a0a00b00090100300300408482c5a14140c1e01c0030509044010728882d88000e44030301d00d020010341e82c40009083c4502c0030344620101501542d0810200d004044045001302240c1c101c0504240c003070103100406910000c140b246140301040001d118249907640320f02e07035030000304084c5480781d011f0f24482078a1000c0b040715448d00c0100103041841e1081030b02a10003681e4200040e6454401500848842c04007030404104550b104100059070300b4000c00c4450450300907641d90320742c1e954440800a9807020110344101011080005250b41485503655140700388100340444140500c0103010f00000e4064812010b100203820018041250380154049030b02410400c094 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 530244577 1250 530243327 530243341
    0xb030406090b070801080316030c150903110307120f1b03120b041103060609060d0f020318060f04032709020403060608030a020304140a080a150501211b0e 68
    0x1e0200072000c49032080c503440880e00b12481345040394180ca0000740203600c2c1c5004035035041c50380654414102d0400021058080018010a544160b050145c4170302041805c2c03c2d2401070304030401c0760902489903000b4032000d0045000008141400d008504041001c0150054111442c000240390f138000c3c0c072031414048040581c484c9237100d003040e00c0402000042041002c0000f554142d900e103802030001031020442600c0d0400013442c002600921799440c10164200800550301c1c985600680a940030081002c0030000c4002056a140c289018080c90720b030200c0941c841c14800f401c003504003c00310f00e4252003904d821040f900d840c00c2c0d1031440c2400e140d4420700003000c0d6000e07010844940382002c000156644c0d002064076030022041d000346041c64148042001c140c4000150a94003003045400054806010300240548500903607105900101079201c4000346c5406a0104644000189d69200c00c03488000305000502e9100c041e135015802404c041e07803107061140d0000500d206040080c0524 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 530245827 1250 530244577 530244581
    0x8130809040c0e0102060c040305071401021905031908090604031d1206040c09060b040603050703230f06100f0804081908191109011206090501090b03060c09061b01060b030406 77
    0x1403d4002da08542c050f5455444200150180d888000c203590f2020340d0600c900003060581d1b00d0314101c10310407038002044141c4040d40087c0b1607034040e19290000110018001000c50000e800140141003029050130b040700c4055031020010f20103410096010140340003040e00d00002081ca240090100c0010200b109107a0344552098908803000d40146500095900440c09180e0480d43c92406890900d8500381d07090b4007810740103040710f0401d9030b02c00101c94443c0159468132069114102d01605600c0e0622400d440d404000d001c461040311100124091603500400c4100d00380c1c0c25103840101602c803480c042c01c030340c00b409401e0210030079031000d4101ca155111007134511400740c17031804c080040040c0a81c08201e0f0300c0d4504081c1101c02c2040084010f501898000007484032111000440c21b603940e8882003103403001c3c2c000243c1103032a8003098246150070040250007850102d4030500c0c0146a400080c02c3d8841c60303a65048182045a0b8401c110400798803c3c00140400d10310543c1e00e2420740790081c0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 530247077 1250 530245827 530245847
    0x30a08030c040f081b21031308010c02070b04090207021c050109121d010809160605030a1d19051f020306100216090218130c0806030d08130809040c 65
    0xc0e07040c5801800003451480050071500c003556401c0c0740920402000c0038004070a41b044a40b03003403407031700702d20039616210108014100d400d5000510380d410f50510303a0b82d43c2910001c00c050011580010801d002c22180001107408680e6540300040c1c6d10300c2d0320310104030341c40b44105150000450381607440003484810f4000d43d40d000d22034080406507840000c400c1c1d0301a401c00c8c480e41da40c11070822601d2100d502a0604a800040340d50854003d5030000d810900c00c2900c54101030001507001c401d11690718418012045200302801143e40031f55000082c0b1680d4505101aa20014440208072400c2c017005215070341a2000c2070000c0480384507100100383c0694000d4490703030702444112226613016031001c0f075101154100b04099a100d00c0c03420661001940240024a105180e06042018265a000141c1c09040b0500074085070707503104484080c1c80d0b114000c0101e80260041d400c1c043c030381548207501a511942a0942c65804002414030b006d450040310b0768030380c20600c2c242000400c40e8000210030 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 530248327 1250 530247077 530247089
    0x906020405011412010e1e07180501032d020c0607080403090e0103030e011805100806040e06010e04030f090e1519060507150b100c03120612060902030a08030c04 71
    0x941184469844042d4030440d1080d106a801132401442000051000726400240c000a01d80b506e00042000700700714503060340d899001c110210011030400a501131100010300e800d0800304840c100c90381c89410783e40f6495404904550384040d22114044040d8107803400105484200d038840e00d03116801900302c00081d9000d03408030b2050040020075148a00c1d2440c10b0b42c4d4165940c4501d14140f400644041051544201039280340c4070300420a92140408004001074a544250b02d506010040c081240ea01c0b0200001681002006108011242d000160802d9251800481100d1142c40071901c500085e0840401d221003601403040103080c08003450b540396802c0711001e03603a40c0f01d07042d0726030706800912403680411414410791000c1100c20320284000201c40d100480c9591050000465202c0c400d201d0743d000c03403a551400801c1c0342d8804020304100c0d030320080800c00d46083c200e1448228007400d000604a54523100c40d00d0454805228070444d2640c40402c664803410624000c050a80041c000c070 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 530249577 1250 530248327 530248337
    0xd090c0e0a1a0108040f080d021b2b020708060a020903010e07031104091112060f01080c0d14030d050103230c0a0509044b02100f0210090602040501 65
    0x104000d48440d21911282580002002c031440054000540e000c0380020020b80b040c01d801510309003c40c202c80d00a101d800d10f420001a5211100004101841c40d4185050b44a80c0a0200d000050300d107152840070510080c21507400103060800202e00e083c4d10342c1c001c2403131801340c0c10a03c400c1c061183c0160170306560450090000d9402c022030242c0c2c4011a200c050104001342800307200c1030600b60301c28030080b80030b041c84452000303840b004142081d075040d040c0c44940e0f1043d01008010720140384541e014194620242c101030f007414002807580120390300f02400810205030036440d90308041089a940d04c5c0300c043c09101f107681d6410000060025407010600d18050000a22035040020a0b1852111401460480c26505180c103120030250f000304101c070400c0c0303901c80310080e190402e981903021109069180613001d04140c14503481d15481d101d04d031031484d400e20300640140d4070b0794945c45c00b59600c0e107400b01240000540492401c0310407000701c541d051900740340600b400540d03001031003038031000c2e215 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 530250827 1250 530249577 530249581
    0x2220512070608090106031a01140a080309060d060305060403020d03051806011a040f090f0b100e090912040e010f0b03010501141c050a020d0506030c01230d090c0e 72
    0x180419811450650209504a52014840e081c09103820b513410a1032100001022600e84c0d0342d909000202001401051940c0c2c1c004000003030a1502013004040161342001240e8030b450b0390183e4034001c045089115a00115098850540c03d0748031600960308407084a1050811341000b940307500c418100d074800241408000340c40009000c41001c1d0300940c640c0209000e81c03a006041d4441c3c091246001aa4030081000140040c002850340c4003404012a0002d20740300d03440e01c04401c4525001172940644440c14065807000d412640e02c0d030844105880c2c4040c1a501d00800504140a0038171856030798201003070100300200f10302c440c20f0584104c0c00c02c808486032218035000041c042446038a00154980210b54031800301c00740507201c00024800442e0758000641c00940640303504440306002c2c0ca03800304402c0a218124058a07410500aa0283c40f02c6440300000921141e070040900c0803096419606549034014181140c00c2c0b0444840100013130a181d107000c090a60b801d01c1407980c1c969100e00 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 530252077 1250 530250827 530250829
    0x30c0c1202091f0e06041b0f02010e12090d020f130e060108071a07031206090225080d110d140627040b0a0b03100219050304020303040306020903030d022205 69
    0x4002c5003d880220b41c64000140b412241c240e048034003c18a0b40c00c41d440d650915a49100c9410030300e696036654480807020707141d0200080c210340790420068074540c416171821200c2c92098084440350704040d18885d49481460001c5041550f200300c2071a040b0b000e4003140815070000e9072010010840d2001601d40c0c0fa40e81e04469a40c0b10014040c4040d000280c0f05180c919103410b20051000c188641000b071803d4100d035040008450790741d0f020070320080c0c000500100b440c2d80d42c05039aa410a410824140c81d210303e4440c0d040754007941c2c1c5802c1100d0359034101404400040c00c1900c0d8000303c03d0000303100b590080050518190800d486150003001c0c0410102c0e10135209200c43e810356411080060440d0b521034a4003a4142000342260b100d02c1c1d610601190140c8050002c0e00ca078403080480583d41d0034680f19030070403030402c1c0c03d94001080414410301c00107940c040308031011260004000341c0c48240c0c0100113420351203960204030025100103104212000005043c60072420a49041000c55039160 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 530253327 1250 530252077 530252101
    0x6030b0111300403021c0213090503120108150106030b0604050a03060f06060f080408071e030309150b060403020d0204140405010e070b071a0702030c01060605031f060219030c0c120209 81
    0x200001b54048000a001d030045c000860303a400c40c2e00d00050a1010324550618031000703c60920005a401d9000001c0d12801200f01801c8079004046100041c541c410910051014111042c010704040640700e00e4607005030340d02c45040d0340c05001c0c0205a00f075010350328a4510028242d03010342c0010581001750015240d4002c080b45c01e51800d0540f944850399541d40d64501c0c00d98440721044400301034041d025034004031000d18041a091007510005080c0c030080c20f041e1444008105214403181c00c1507020807843d101d0300203444c100c941c1500d403488006014400600a80110788450044190032000c100a04c00150007200713200701c110059640c1141c03984412081d503c2403400250002f804032140803281205070568544c4000d0034419039003001010b5080b5420341c0c442d580064001030010040c01040c0e20744441c660a0031030f080401c180d080303103401c801035164040840d82d60380c46480300f40c4000c10706000f014003410160b071207903260407440e8481d0200040001c000c03109901441102d80000c0307081c01e4070 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 530254577 1250 530253327 530253329
    0x115090b01080a0b06040e1609140f0405090309060a050d052d04061e060f0e0610180308040e091506031b0f031e06091606030b01113004 60
    0x10b80d40e204080e610301c084500900050b511960304440c04010008011090031341e1580a845c540d00c03888804e801004e0000d100703c01c190081044c050000c0802a507654541d034a085201a05950100d0b80355219412141140070710348181d0b4100200050040500c1e912400520020519010400403612a2149008003210f100da05511540401003446841d60040b8841503100344200004695141c03c9004040e481004a445d64145519400c0c00d01089540f070818002034030b240c0d000c480ca02d02d00000001c90014030301640105005104443c802c843c605038801c00040c43d0004101c0350f07150341d12038492014100494201415001307140701da54404854841c0103000c2c1030b008000b007080001011101d502c41e000303841440c0d40211055404030198a0a01c05c0c4401c4d04a8104142d998100c1224024100341c00101140d600360000c0031811040100d41c412a0103440c0306140c001103604854005032541520f4104850042c07080f5101512aa003d494002d00d005480c8028803030f0707641400594079414091 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 530255827 1250 530254577 530254579
    0xc051e150114040b0d120503010f0506120f040317010b0d110304050d0e0a030c08010f0e0f0303041e05160609150909020706110f0903011a0f010f200115090b 69
    0x4240c50803443d00d402e41050760501401811101c5581e4a80d8545603441d030501d64110100d040031004000742c00811107800d00400d019074100d850200c8000e640c0805400041c02600b10396910b00208050500c986c0d0078840130074220010305180d58466a85840d140c000b01c02603910282810740461044030321009580c02180e02c8030003040000d0021409440f1120f000080680040f03030100c000012480a514020041440720000100a50300090f04001d85400201c04041035000030300d9000c200c2000022a94055040880c2007404818584032407041c01e00300034007402601c2a00c00c2d842042ca042c4001d0400c807074076034946201d140c4d92500020700c03181400344900701040c001d0004100000031a0000c010b034500c1801c0015030801d20344804003a682280302296000340b008180c100c0390f410248a5100701d000d40060041200b00c50100003600034090032502030401103290803030410309000b20345000b10680c540302170204e90083c2400f0350703000f405541c943d4148800a91000203030003845105d00c202c4e00714 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 530257077 1250 530255827 530255849
    0xd0629040c0306141e030a1109010501020601030c030f060914060f2802160c080d020d0503040f020d02011206090b150408060c03101d070e031b010f0c051e1501 70
    0x481502041780009070b11000140e28440c6400414580d9818012030301c12500c12614403a2070b071801c03400d014150720140c1209040d54807040050001c249000101c408981d8040054558a0894507010340034080301c03900100f40c17205540c1c0e00383c41c2100c085400c610400380091404c071181c0d101803e152002c0d0b42c480c00b104100c040c00f550b04e00c84094903001480710700d0046079022200d280307550b41e1888000d80c0303074480e5086403c840000b400980c3c0c140411041b01880d0b182603821400e0a0300c80610706002000001d101e64001c1780c818045901401803282154401c0300108586a0340c2c00c003000c0549080010703507108800300c100e1107078001010b0301914241c0e16000700401c150ba450301c00900081d0701c0500340100900c00c80d0b90000f410a4120159541c540003034001005034100024080d08088101c5801c920a8102d059800542089800f000c16200b400740303480c1242c05003061041c0c035104003600020b400c0303005200310120310400000149102e040c1e02005c80b4061044108440c244060070b000300e4050003 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 530258327 1250 530257077 530257109
    0x60c0311091207030804270b0a06050a120609020406030c021c200a050c0901080109050604111503040f0201110303090d0e0414090106091803020c0d0629040c0306 71
    0x2c1020a44103001041e1032084416042d00c03511400c08903040341d03200700312120010340e8004450700451082085014074420074401c3c400c2500c0001c021403400d0190b642000400728800580f54031440a803645000540d02c20400039482d051240040e5210340207480c0868188500c90f00002c3c030018240b079210f1004c10020081001014007110074002c2481c3d20004039001c182c640b40e4401050110590b0248100024200700d00403209004003100140c1c42601141d2510801501103200854015070059103e1803079081c040d41140020011000e10500e0070110b0310100c100001c20841100000602d4000d0325140348652008031400d64a1004448080041c1c11000c91001c40c507001c1d11001d80d683c50020b00100e0310903000c0c200751180d4602140c200000381c2d1240b104001d09169446224131742c41c0521080340c814041501c029540c1c55800350072900902c5804040428406c01d6405070040d408032000070458550310440380c40c00302c510201414030861801c140c00441c01e01034480d1100301e403a115580c00342c403 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 530259577 1250 530258327 530258329
    0x6030307110f040608060705031005092403010e0307050105010915290f0d0c0f080928020301060315140105010c150e16030c1a1c0905030313060c031109 67
    0x1564061014036082501c0f03540101720600d00f03105c582e01c510011340d100e079124a8004100d40180c012940003e020307483e030106018000c0b54008035910806484110180001400800320740100241075200d11a800701048540405c0019001641250401c6200344200c46186079542c902d949c0382d200b0711681011440d00040b00001c0c2002c901d202d180c130020014180561075400014641c0a001e01504407031b91120410003854024031994500365452400760940c0c03a115480f540c0c1d402d101c905640c2d8403e40000d0922464240480d000840c0703a015000307110483d541d290440e05200242c20400140b41400c1c0700002801891403014100c510580d074185800d40c064072203a25811090710b2135242203440b940e4600c0c4210007000491030010941001041c01c600d10304000b6101c2003c0c1d00200b036050a21001002011041d006a5204603c000101e071980d181007030010700145900366004055010200c04c0202280a40c100c58059030b000300d1050184268042d02101283c3d880750b010f0f030040f03900707000075041 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 530260827 1250 530259577 530259589
    0xf10020a031434060f020309060a050c0d0905030f0c0304050108090a1a0c0d0509061b070b012d060203040f06181a09090c0306010f0c0f0611220602060603030711 71
    0x80f80c24400d5040e803448581d0b440f4042502c1c0e00240f030310401500002400304402040100603880030041d2400c00003070074a03071070428844c0700e26001d05018644400305002404024411909022800409a683e483c0044446500c3e5049489914003049001000031008000841c045003840c0c2c1c0b068142940642500450014120150030842076078024040e584072014540300e568010040a002400703140342c0752152204105558940a840c501d041c410a0005002101941e040d50044d41d009400d81003a88081c10004a0702c3c0c4202c080c640314080e000801c1a004070040c0291104a080c0d840f0003501c50360281e4038204241e804800241c05400d04100080e100e0340404100c120814003c0c0c5855407180020342411020b0b03541d010f04850010a110340e9603085030030715250080303d080c050340d01e00d2513480f800300c1c40d040d092001c0c28494880c0300d5544000c116030210307415240e0b500005240c610045480300c43e11003450280c0d40c050710a01d0045540c910303000040d201c020b0b81c0008020503c05a00b001e00503 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 530262077 1250 530260827 530260897
    0x8010608070e04180b1503120306060f030406050f0a3305100302031509040507031205210f010e0c04030807140316060b010906140304020f10020a0314 66
    0x402105014800ca656240e002d403407600058550302d20341100760b909000b05c0058003d4030304500b00381003801420141d180422071140683c0010f9400d5100c1d0f6130030300030070450700c41c90a9007000c410300002080200032455205600603941036026107126074611400000300c0780c40314071420500e62110041c8075444c2a05484000c2a00e500303810058072a520400f01d203041d4102420380d00400e4004c4200061000400e06c8841c8141c0c08603440c034039a0425403107207600d1304064003000d0058440d02d140f10502d24010801c4480125002407060074440c103621481000d110142c070709040c8100c2c0c60000040c9214013103c5580158015a0740a1506145540304000ba5001c0340040760b0705000c10300e034100303890410300241070001c00b40103003e04c2100151070042c08855042c500281071041e0780740c041c05515440f0541e61100d480c0e09050580c0c0303413203c0c00050b00c4601111202c99102d003407104842c6000c0d0f400b15a000c60309200e61a14220301071005000c070482c0c0240720000d125035507808040078264480350740100e = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 530263327 1250 530262077 530262091
    0x3020306060909091e250302010806190b03071e0c0c050d02011403091f06140402160203010906021306030504080a0807110106031a0c072105041e14030d08010608 71
    0xc0c090003c0d80b80005c00e615148401075540c0d800030141000b418009000000030513110b84c614034450382c00c0d0b0340041c10410700907080750302a5070710190440040000c001c801d400351981c2440c680c1c0368135010360001e261146080104c140c1801d50f4030b200d99010b024112194240c0ea000c20000550760902081c04580f92403164181d04200001e68814240d20349400114094204503009d07001151a500e1048160900d13003081c0007929150070020003040c80d030315461a204000072580507a40e404c05170b07012000c51860043c041c0d0702d54a4195040d041004640c000c015201c001c500303100c8856550310050307040707510403540a4001c1104000076003101c0e129003c042e45c0701b107030713400c2c541c100e5070035603032a1402c4440941003155440e0324032145801001d813030f01d1556030100945508602e455000e981c1c130036140c240c0d41006c0100801e4402003003003040c085c00035100640046456540080d2620380d030410500e034544a0380b240e01000c50b40414240c02c000c5032010001c2e00540b500400c036442c0900854081d02c00030054 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 530264577 1250 530263327 530263333
    0xc070905130f0609050c0102150604050c07060c030b150405060714010e0a05030a0306230d21080a0b041407050702011404170c04020a0c0b06030c0909030d0c0302030606090909 77
    0x224002030104903040c5082c50150100148900c02c0b0703d4505d240c407500f88107540c1598060004052210200110300c3c0d0702c4103094801058030348a00e0074410050241e4000100781d241003d0160208640c540d0051400782811254007401c07001402d480302c03a9119501481c1d0304440c0030440100403171500f0301c01e00f07002480c0d03c000107003038840066001c0c01c0a020550860b0b45400000e684060103604d03000b038074050400121507843d00c2c2c412010030304403442406141c3d801000410703000010300850108008080c1ca0382d001c1c0d05000b2040796001060400c1c03c4070030b03a50807481c00410021905040c49440000c040c9c407a0501e0039901c0b015000d4480760003114080341044285040b00b00f004010f4405040103000084c0300c0300000d200404604d0510310407203407070350055106000302814540e0010a16400c00e4118950b08201d8450401003820301c50200091500410a9001c5c000702641c000010300c62400e24420400200e40702e084124164403040c1c940507809041072041428510703041d502c064110042c5070072 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 530265827 1250 530264577 530264611
    0x200a0813080102031023100c14190512090d03080c04030206190815030d14040b030124090b0301090f0f140a0c02070312080601020a060e0d0906050c070905 68
    0xc00ea080e44d0044540c46001c210f11501000040500800020500740c60307840505150034080c01316050391381031311544041107030341c0400c5401e009460005621003041a01a03511140c07110300c02290b0003540d0708085a040c410707030f8022202941e0b4042941c0405400900001c0d00e40f409031030031951044050420701354200200000401603481e100100a088074074003154114120b4518003424100b00180000394490780d03900904501d45d00801d10010340c0c0403600b00707800006000a14800d19001f82c0c1c0050034103020000010900001800a200c0e600550510541c50b80101ea1821504a039040c03140c2100c91030140014031216540713810100c1d46c5101c000d00000c04120000200f416504401e00e400030b2141003e00307006452180c2d00513050204168001003d0681ca16074582500c4404150034908010000300070a816a1003400412040340d0407100900c14840701c3d0740c50710381321900040300201045c00381c000010302e140681c0030b445152000c40040d0150078a07290071800601001010415a0134003000 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 530267077 1250 530265827 530265839
    0x150b0913050f0414030703090501030f090b040c0302030d17010522050708010e07090e0a0903021203181b010c1401110d140717070e0a1d07200a0813 65
    0x100300c500c00c0903581080c0529083c58140030289901003c41043c543d0810000500840e8028030312200b00e403420b190000f50007000440342002445480c100800328402401800309000c04112a1b100360390003202903030031903280c40609031035051040540481c43d9517942c0041285203408031744841071800c988459166541c05218040854030104d6029000c66003410042c4985054800801d80c04161403c0000000d0300f091780c110803003803005054440130707034031151800c042520034000c400d401e40042180300d8032420450f1100000780c0900c819000035104418125040301000c218000e440507043e101d0080005003900e8a220b5000d9080f462009076483c1d007200c1c055400000c0080c0310003004100002241e48140282618a010240c04003040110110014000104804015070020000d0030a034415000c0076000c02d1208800c2c0c0d1002c2c004038898820019029503c0341028890140c0340da0711200803a04464030176200c400481c900c0000d5202c140f400000407070000041846d803184100c4407840c1c0d5aa02 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 530268327 1250 530267077 530267081
    0x1f0302130602010c0905241324080a050c031f0806070f031b05090d03090b18042a050f0903010908220506120a0b030d031a0301150b0913 60
    0x307405500141c0d500c10a0707000e59507101c00281e014040403152811013000b8901807000c204002240c0e450445000182d003d40d030201c500f8018010200740a26020901202d102143c0846250807604080303032540700014000401c510038503104543c16900c660031600d4111500700c0e000590b68844190007042000070642020420403684201800e64800a504502440c000e09440c41e20404402a501884040c42d0044e0800241d5a00c001d0a81d160f0100300c0341418120b48514140c0c3c4501000d40300041d141d642c3e0b10014a19900030340d001c1c0c509004111810340407616000004401c0100b2008401c2d2108150b4400c0c002006a00303c9035139101d0030424540b000a0840322001030845040c480040c00140241c000395039110a4503400421000086c9010f000c201c15210380d0b401e00b64050701c0c040004038a1581907100c02140100581140e44800f41e03013070080c1c018440801c0300300e4011001414510303545014000d0344100208a6040c80c1000c0c0750840070746d0f035038006440031940400d0300030074079098190f64 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 530269577 1250 530268327 530268329
    0x1201050402100c050f15070f02010509071401120c030906060605070510050703090203150a150308181827010902060d09030504030b0c030f011202180402040b030d03020c0d020703021f030213 83
    0xa1b440300b1003e09001c08050702e00030002c1c140c0001d590425040120740329003c9201800c9840c21405188944000381c0103c442155007805500801d103099411420194140d00c0300301c000c1c0c85071800300181511440183d130305009070f800c000e09a500100c210154818550840c54000542d030074041017001c00d560000f41091000c042d02413040c981c0404002d41080680641c180c1c9600d0300002036555802c54540c0401480342010038401070810a0340c048443c3c4545e6030000100e400c180c0d00891034104075404120300441700c4007050a40d030090448140107041881501c006682c010b01c540c0c030300440020310b100038211008068003031103003d00c00080804c0007618460b100701c5000b03918568a1419071000c07188082c040c0c2007120940e0b80135903c13200507103419400d402000c00f4a1214502d03030b51103200080c0606020802c8541502695084294054041d0003500101700080c06032403900c0180360003240d60380c8003417001a500140b002010411511202100c009a00030b51030050324140611a01103051012 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 530270827 1250 530269577 530269603
    0x204030627021318030503061f05041e1703070b0718052218050615130209030a12050a1d090708040305071a091009031e1106010e061201050402100c050f 67
    0x4000308101031490711204a0200e20441383c0743e1010700e0f2700b1050044c500d0243d400f8a0034001c00519404460000070f07020741780240710b4000c0f04803030000c80e0682c1135180d400101c000c44030500388001041c0ca25000310003401028299114007028185440c0070407899452142c440c50031030307580c00c1030150b50410074041c1c507484990555161420a84a107413071450180000c017022960080307401c6a15040d0b072541d91912140800110241c1c4031388140c00003e00f400c078100401000340703440d01540d403080380c1c200c0c0240021001e40d07251012002c80401d045030341e0202c280c1205038803c401c0380c0051039440c050064580c2241c007900c1c00904040440e03440720005048030a6503010001901c0030000022020031100e0300009008400380010700e000e990150500c000300040c1c1e01c1c480c03055400b40d20010b1081c20b01c0e15119611070201e601c5942e6a07a02d00703206007002e07142c0d076001d010f46034030841c0c1032401405040e00682d4003402040b00714202480403550244200c1c42140d450003087e20407409144200400303006040 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 530272077 1250 530270827 530270837
    0xf0718030b070e10021f020a030b191806081011120109060e010602010c17150303070c05040509030c030d051503010905010e0f0712021c0503040603020403062702131803 74
    0x107440340400c6402000c0210081c1191700044400c0501c2103e03e100e524400c022000150702e03000c80f0f000a40c09013080462b000d0b0007035280303211b1520500f06001a00201c422401e01d04141509259104054031260f0240c502c45603c48807106401c503015502c02044808540d25a504150308200c0744c0840e00020f81c8208181901c0758414000043e985a0403030044c50540001c2000f204001c00c0501101f8400380550480801400080c002d440280013000d46e840c0001d041d079940f90a0b030701d4042c000c1195405014011440c0c140050600000001141c0045280134011400c1004120f901c7c0f01404000b003d1110a0a842484203c952024012003510760721901c00461044c00404440c1d00d00070f003103842034540ea801310008103c0c52000410140405406541d55107550001c05900e01416030031100040a900c00020001034559040c0c3c040d00590348100c1c01031208510420380c410351301001550b0007000d03c8880d12940c00600e40307074029003030011a80c4404200f1308510148480700c020880400d6001c22 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 530273327 1250 530272077 530272097
    0x1017010b011704030c020f2202070c0503030406050d1a1806030d030b06091201020f07050f0c0a14010302130f0807090b060403050a02010c050102070203070f0611060f0718030b07 78
    0x740e00724000b21801030000944480600e05074a0080803000500800390040350b02c94007030165030315590040d203800107050312450403c3c000b20400c440254400702c01502d504100401c081f03407074500442264101c800320f42c0c5007400c1c039450307071080001440c403050264070446800000c60410b40380e0341d02c44c43c8495014441c20b907a51402d6801c0c542050a009084002c0624002c07440d41640c1d551011b0303851202058034644001139920790264024410014174502e820004a840002c0200c00105411a0b60700041a500711075024000d00ca81080e035070180310700228030759045684c994420781c040c00ca0066249140030083e40d55900b4640301c15496004240c0d280c00034042400451160302550310f4410040c0e07101c2c0d01d40b614544501d502d6030310403a0024100f120040d020020b000003501035401c0319400900741c400c0d240d51044d50780c0040301c1503c00d040100c4c203101d0400590400204025104000641c90510030355a50316040304e64840c0e0a41c103010480d046c0c04084080796140e150144550040d0f00c5a1581c0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 530274577 1250 530273327 530273329
    0xf0314161211041208040914010510180311030c0d12030c020c0a0b07020a030c0b090f040c1d0d06050109050106020f1603110a0902070b0402090a0e060f1017010b 71
    0x60000c007262118510b081688504000001c41c04a41c00c4462026058608420710300e480e10071031066078000024207023042011210064802d187c141200c0c1f00300c503207240100d042d000580da40140c503411081078590043c403c001090798010b0180c51114024107071849000e130301c40050310560b02801c007900c0b0f00c1403154054600f15058030885507246035500040c07040054103800528a040709004418100c0d00114210313045482e41c82d5000069940000b5841182d5250040c201003900b10080a44c0302c0e90349000e4011443c1000d00c107000d1511603d40d90003140c15081a600e2054091440f00c00d5000300f501203441000c5613040c03044901900c51200c000c140c551504100901e054021240307094107401000d0740d03117108540c06140800716a0702c00c149040a52440780020002000e0f0f600c003101c11400044c24008001252040512691089555101a840d182c0c1c1a07800c60b241c40c9035000d45c0d940f2400209011b04000c010341a485014111b11501e01170b164100f040c1840d841041680d0940e45401300d4942c6 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 530275827 1250 530274577 530274587
    0x3050105030a0206030417071401050901060b21150301020a030e0c01032306040b130b0117060d02090907050406030b0708070203030c160302210c07080d0e010f031416 73
    0x1040d084000742542216600000c680d4480036000034407070a41d00c0101d4001076041d101380c0e0a21600300c003000c44001c141c200b6040c040c1600311161080c9518128007c1006529a400d490503050350645085900d0544020103084490150008840000c10702c0b080c0010703902400201301c0300c15a0341d00070488031980f00086103450740308010a41490708000d19081d07510110a0940c0e009051624011030a449140210703005009401c1c03443d41002150078801c40704402034210514401083c1d80d41c01c440c031a030079100b0700c0c001c00c25103c0e0355200311981c00e160098079010000e05d8120088000f0b407920150b40e20300050454003140c0c411038240400404111300541c000c451140d2010884c00038629506d0030074040381c114400d4000f04000c003201008050149803082210070b01c108141d0f05411481c40c511000c5e00300f1900704d060000078520905038081940ca071b0220300d4006200f0381d80c8416001c1c5a800c001510f800e0002032101040680c3d400f41c22004959408440c0e0040000d1103c4980c1000c4128000344 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 530277077 1250 530275827 530275829
    0x3100b0c0a1e1109070903150b010206100b09010c02040b0d0311250b07060f1109120307051e0a0506010b07062306011116030c0905060109030c050f130c0f030501 71
    0x20084081440118400e103581800c101c80c22604c0b02c042c1c1d55081c000381d07001c658503000076109980d0540004481d01c0580d005441071030091302100c5441c1d0342c103d41d03010242028002c0c08104a0b081c82140c489502422510f05458801040410496440c20221751030740b109240942c0041c0744101249500c400c14401401d04407414a07500710200300e0302203150b200c5030051181c8543c000d4002605030900049500c0881480580c44040c0138081c1c00007514081c0760006040c0030312503c540910f0039602000001140d10b03869000e40a00b0f0b4410003450800303100354401c2880c0f1410300500c0c407018006201403102e61301900703020510035168420340c1001d10807612606010940c4001a005800c2001e040345922540000246000100c101382e402814fc2000b100c02a21000c0040d0000040308025860b5680760a907811040e04000c6a40c40c01d0046403041d419220142c035204454000f40b0481c10941004070448001603e00c2a0a50b036034220390741200e802c41d401e0320004047e00d2644c400740d80d150040174 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 530278327 1250 530277077 530277113
    0x603030c191b030c0e0a09080c0601052d06090f031c17090a0b1f2d0510050d0b06040e0402030708010b0f04200f1207030903090b03100b0c0a 62
    0x106800d030442e035034614035a0b542d0048102c08484400054041e40c6d050308034401c19031b0704c00c1d2507a44641d0408501540c503002070041c140701328803840500c01d207160704a140b01d803562003243c0c48851200c210000d018050b44000461908640a040011034644040108003944003d800e421890381c0034510b0024007900b002c2585c0d01d0b4040b0018144890040002a030540b680e4000801040e1500e800b0000c500704141a94039000d0340d070008000090303a003140418106c48042e071801000500c05000d07400e1403011510701400383c0c0505510204520144a10082e00304a528a0800202c41020070b000801c40d0f001540800848000c1804000c2142001d00c80d4200400c0c81e60024403154140b41d000445543d1400f0030709019a030b545400c038560020341c034965003801c21070803043c80d074500510003203060720340c0008040302941d65408041001584244550000340742c0694420941c2804d1844405d6551710140161441401c031210100e2070000072401006204c5122004140800c0310740f80c03280d10703207802107058 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 530279577 1250 530278327 530278373
    0x31703010e0a090309050118170307060b04020301050102210c060a090201030e0106080303010504020906070f03050a20071203021509100b0405130b09101b031803090b030603030c19 79
    0x6040040c2d0040e0003030051b40c5007420846d003200c1d0f4000760b540c03407032041e03510103404003201c03545003095484003100811006000b42014058030701703a017060005922081c4a030b940144c2c4101c00354078a0340c4116841541002c040d000c000d150601020503285800c10584060240307543c2c4e0840c9000b19a0184180c045c1c0020400c001e102c428a00b5100c19128001481030a02840e00041c03180042c1d0358281c1121241c0c1c2d40b01d00c03030752403a01007814000c2241e0400d064860101d02c4040c0120244880e622240b02c040e004030005105003410301c0285081c81c2420392080b8198402c9d001c1c0f20901044001119116411001c000e00308100002080303025204070054a5000b2443c05050141d4065854400348106d07400a100c800a5180e60300e0701c5180540400001140b00e1900482c410790901d00503547d401c00145540600503a24407030b40a0400340a2000003c000c81c00c800300c1000800301c490b001e03542c4018021b043d00c5c1040c104009141c00d24844290160380c2d0744020f01d5080802c54110300c4404281442400 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 530280827 1250 530279577 530279591
    0x10b2a01231006110f240112170f04150221090306040f1e15050709060203070b250206100902030603190503300604180f020307031703010e0a 62
    0x20b80c400702e03041805140704204440d4000c40c80203400700300b400d041401c407800700d55aa85e00e901c2c081d41a00140030f030034144188140000501005001c140604e010b400c2200a82403010040c501c495640c40700410101400040c880014040642036425900c0c16242e0060030101042814001e644812040d002d0003404040c0000c0d01251400101d0301d62080c1d100081e95180e401a051812a4000c0d10301003900c69004494a441044480c404110020036000000e11050300c40d0350003070f00d015142d03000e07e0005a0060100034085429000d0702c070381042910740c5903460382d9644c0c1c41c00020075501442000259001c030061107610740712441000028041280110300314288200001c0d01d42c3c1d10b01c003440d41010b01d0b00b12240c082c000b0a10455000620040d1400301034040340150442c9400b016014030420702c503120001d05c490401d808ac07056030308204040c2e0f40c1561016903540c0c49401030300038180e0f094070a610b008000900710807181c0102241010f4010385070b43c0750101c82040c40000a000f100c0450803c0381c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 530282077 1250 530280827 530280841
    0x1c03080a150614130f0f0305010b0f09040809131b170f1612091101030f1a041d010504050c030d1106221a010501030609060b03010b2a0123 61
    0x40d0341070048048450b41907880e0b10581140513450b2140e04005024240d0340c1e00090b04510300103c4038210381c884e030005d01000070031404002a411881151940201c4c58500080000e0781d00b070010060184010a0003140070000c1e202d180c01caa9001040302510b801800607030a130241c000300d841070f6410f00b20702800780d03904c0c0120307a000309100081c0503021000c1c40c0c0c0d80c40d44416405100c0c0f0940781d42c1d100c141004101c1c1181070600059040140340e41c0403d1404440c859003081c1d0f801141c103e142e418030004407030701506060100922800707880c0c2c24207074504114504020801e018890145010700e00a0249003000c008050828000d40c04031402d0054101104035201c4000c64020740c08891444180d6141c1d41d00300061004803d4444c004001c00340b800561204215010840c50683d40281d8041052a84800c607140881d2814003c6003190041400104980d600c00d2001300485101e04041403a00418015659100881c071204458240d46407040c80c01603200c514078441d01d050046900d941d940c14410707 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 530283327 1250 530282077 530282087
    0x71e1b0512100b010504081504020411090d030513050a0902180307120209180a05060103061d031b0111180102060c09090f04031e090f0602030a17061c03080a1506 71
    0x1403070701c064a5156070070700070b444e13000300c055900a0040405a0f02800c04002d0884a00038003181c00724810752a10f01d0b414050b40001058604081c8040c14480c1c80320020f8800391456009100d5048410841240105098882168843c000c2c100c24501585641d80204030104400b03150361a18044e81c0420010488042e9036121000c1503501942c1d0700070740343c03a403540d030b065414084508566140718005102080110005500d41228040e007810829100c0034040c80f4105d48440707840102981c018400c0c130b08000f900b05030251070340502c207000150403110f102c02d036401504000301c2e641c04002000e10f128412750b014400158441e07400c0c40000e03c1c2402c542c0000c0c100340800707084813581c00d003040d00150805004084201030400307003a000e0342040b061654003c004200500803060440c14801002031a00c2c000000d0341c2d0701e02c80e01e03100c20b00d6511a04044e5117032104010041d41c0d000c6040c022803070300e40240f40d0002600e04c1c0039070342e18481c0b850702d200c0e2a002d4482882d10f0851415144008021040c3d00c0 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 530284577 1250 530283327 530283343
    0xf06030e070e13060501031407081f111306120506010c2301110d020405120c030303040b0910140402240d0c0309140105100603060614071e1b0512 64
    0x21540850141c5503060b4100f0a0441140028062803801c0d0012052016102c0c4d00d075a480000c6003290501c80e00e034030340540c407100510043e64007403440303a148009442047d0000d0700007607408a0000c3c20714842406120140715140d0280d80452060014903003200c816009080d0300c48820708002448058503540d07046c1c1c0e91400c061240d6004440d82c01e04454000c00c0d00111501c946e088480c0d601c6044c6030b90110025441481050322800c010700b08010210000300d0341c4942c80a0040c0514110765036503d600052030802001d03003240d80150342040560410700d1040d01c040c1155020400c042c2e19051060062080206144103081c0444001c0c0c051130400c80c5040b15a842d1100c0000715a42407030b108141c020f070828403001402180107070790301c028014055124074400e074160903000408030b41d00c1c01d06031700b2208140191000180201c0b07225424201c03100c010124544105100740c205a007074540d80400001d8690200c640c083d2041c0304440e042400503001c00a0881210441801040700700c691b551840c00d = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 530285827 1250 530284577 530284589
    0x903040303030c0e1302091305010323160305030a0806060328200d0612210e0607060608010c0f0206011e030c08030712030204030b040f061104060503010f06030e07 72
    0x2240c03d4100700d43e105120038109030101038210815008498000c001942006000f240100303103840c140702c07007461171b070045a0489820200d124600782e8001d40740b00541600c0c6d080c01155110f0341d400c1a0300c5284c1c40b41d1900003140a0406180c4499000a0041040c2c40180540f803152001303200788401f6460f105081e600b41506a0101ea81505946041c440a8074070303100c09000d800c008040e449003d8440c6801400c0000d4440001c124441d11103280640d400031800d40a440b024603480c07103558040703143d0b00c03040d0401224184803a49500e0000082e503168066007046030782e19150303902008030a03c00d0088142160850901c0e03209007d20100003550b840d01441940b000e0700c1d00280b0b0342100d0030020362031070296801886402d4126201e002180d43c0790b004950072104150101c2c4200f0015210f80b00b51803c0e81d034042d0010f48161a10b8840b0000c4240c1484262002c954a19250241c00c5110b030040c03008020b00d40f2115242e6140076135604200303005030b0200c0d0a043c100240c0d081445404260768054500c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 530287077 1250 530285827 530285831
    0x40f0608151009021611030303130602030a09170d0c0504081209120f070303080a0b0f010c031e0e211e1c0e09090c010219060e0604030f1106090304030303 68
    0x59101d10090541c8001da101881944c8005802054070714a00f0b85182c0301c40c064801111000248030516641344411038600e45c000901e40744403030008400782c00441c7c211003012000b0402c10760f40d4590484d403d844029164924400241c6c8502000c02801904458079003824440d09147c50700000544654038101818140c443c0000e18040ca0b41d58000c20040c0c040054049496404200e010b050340c45a990000b0f90101c0c9454000501a02d81805010300781c1102a01c203400c00302e8080010355240c020407000f28140407485030415045c02d045840d04441c0030140e510f2070740300b6008909100c51784143c60b8100603805e010a0b040242e45000280e6003d1158903002803040703e0881e005d1550402020720b1b0400203a9005000102e64503034008102c10b2500d008440b41e0310541ca400d04d01558070349080101c42d000da000152070403449284001012501805008085210b150803412542040c10817903003140441c850a100f000d019601525402c4103a00c048000e01450600035045a528040ca200040800d5 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 530288327 1250 530287077 530287081
    0x21203220b0c07140c030a03031821091a1206030f06250c030804172101080d39080c1b0a03032a12030902040f060815 52
    0x15690503030411501c1c0c024144065078204140c40d041664005001a9400782e0965001110100c1c04240781c1d0100340010010300800c2d0445d90280e0141400042d00c484000745a440c0b13001041da03045500f4070b02c0c07400801c041400404084c01519001b0143c01800c812042d060865019142c158101d8080c04820144540c8555900d0006407415103242e00c550070380e00032001442018030b0019150310442d01080300c4242c400030200d004542c09641041c01500191000300400c0c08540b040f18040c0032041300040341031410040304101c8400d03e94403490084041451001000b28400500a004117401c040c50a4100503001645065000d101d41865840c1080c07006c901d07004c81110319070954241a44440c003070b52506007040c402521066042e5114001c10340b41d0161919074030b0201d610f0800d030b83d80764490200380c010510f10840c44064000c480090006844420808079000c0e480b440c640544a980c045030307105581c8144426100e80c3e00480c8019070030f04c03405105555002c40c140f04003103034031040b00c429a = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 530289577 1250 530288327 530288371
    0x30201080c092805030d0801061b080d0c0e19080105010f051e010e0a09090506010b0a02100504020303120c13050a03030806063711070e0606070510060f080607021203 73
    0x3c030700c90380c08550301d0310078268195045500000040d040b40d00d01e0329010140c000c021828007591032120401008100204502c40708400d01e94415089070760140b0700291003561000104103003000700c1c10b650141c44089041004000001d00405015241a40d0b503c0034551900012810140301d150140c0915460592060003e912a0410b80b0010400801003103031290784485d0500101040441600c540c06140300104412155004031088908503500a100c03000e8148116002041c01410899143c0820000003c1d40b482085555026002c808180783d03482051a07026007045046610050044010b4142000032130f40009070583d1001040d9030345070392500d040d819446103200030741603404d10400c111171411102607488231403041e2901e5502c401100e54000e801c0030b540c80b1840c0c46000303110310350180010240d0034014064840c80303209000711881d00c40d110000764140d504136088240010491034080061440401c2400e821100c1030002c1c0000100b00062402c82d888014107040c801035101a080f488 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 530290827 1250 530289577 530289649
    0xf120903091f05130f0612050c09010f020f0604081201150203030703020a11060103050c1002010504020306060f01110d1d04020703020c091008060f101a070b07050405060c0106030201080c09 83
    0x3e0500740005101070545c590030140103000e00e5004100004595000c3e020000c900380c840c041c0aa80340005c3c107810210f01d08011a2003110045902085000d804100811244108600da00852103115030580740c02001d00c241540b80030580c000c04080344540c1c5501c0182c0d401000310b070307080701c13240c5070140c2d40e031000303070317820354401c003c00c451155144235070000041403003000f01d103e6215810845140a00c54001c06040342a240195006035064008001080040c68840449050358206051511340040800c6085041c0000200c2c54404904010700005502810302d01040048408071411030401c0304a450003907580107110040390007060201c002c21040c6004419800050080000321103807407801c00454692124256481108040c9400000c41c072420106440042c45098000711402d024041e1940758800402416060a1080030000801c081e1500d00050203513010401c00464014650b00c001072030004010285803c00005020420641d940c0e00011550740e200130303c8074110350005c048000c41d = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 530292077 1250 530290827 530290837
    0x1060804032a03030b031603020a0e1b030907080706030c02031b0721140109120509040207060612050d0e060a0e062215230a030b060f120903091f05 65
    0xc070305080c281070b0404042d0b045d00f00d502c0b0300c0c4081c0c0503030f8403c07159401e041c116907200707000003548010b8099091180c1300a440c0f8142d40802e03009001e08000d42034500c005203d61040c1d90700e9581e600949800e200f0b1900421028000345000c0c90104090107100400944038013035140c10388500d89003505004c1c0e0f200810010307140030700300e56204005525010000002c0d00041044101c0d00050400c900300d00d402030610900c0b602d80c1d08000981e01e58014200111020791090350f01c1644940e0038007105001c030f00d0b148a0600940b900d00d8180c100e480507810b04610702190701904008100c4ea003101c3c2c4a50340c80b00d40558100d02e4079420040181441c040000e04ad40c01341410410155607044189440d149102160000b00c2c0d880c40348807060541c81d10412207601c00884005002d14a8024501100000b04001031014681c0303071500280950400e00090303410761105186010074040801d545510207428100030b5040701a01c00110b181501b50f03004108103c56920b1900c0c68a0800c01043d98000d000b181212 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 530293327 1250 530292077 530292137
    0x6010e0d1203020408060c09060a0c171201170a0c1707091103070f0e0604030b040501150305010203100f0f0611150a09060501050906011e021009050d11060106080403 73
    0x1600703069100c1001070003504144159801807103003001044c6071604000480e101034401400241c07400f450ba880c02d9035210592070b411991a41c01b007040d41040501c40025001c3e690046c1c0c400325040d4541807000d03010310051541c18100343c1000d4544800220300721820702c00c80354030881140300d600c0720020b482c2c00e00a07641e00070041c560900e4114106864204000c2d8851002030f10f904005010814003100c541d5902d0241581002c0d00700801c1c000f0540851703601c0e83c403d03c90b000105c0c035a06141c00010303040c41543d00403120790b90080103002c056040804034101074040d00285514451400c0d20501c000c0655101d03030410b024416045d40900e51080c004d0103d40f0030384800030102401c1507407102009001d521400e580b202e01e02800481d2914241e50030070300940059543d48800c142c400c3e40300c4212201003011005510800c001c1d46801d0b542c0e40034103940c150041000c0c10341e902d0003030000b502070b03000070101d901c103074020b40e0050044e103401240c400d4109406162421102000c9035070181d1840440c0200c03 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 530294577 1250 530293327 530293343
    0x6030114150a061805061303060e060a0f14160e0a08060901110301051e0303090d0b0a0f050403200a1509060e010b0f040e010609020c160b030f06010e0d 67
    0x414107241d1005880002040c1c811001d1240d941404803050725164041d01d4a21080c180100080e10b0081e01a01d030001482107605040360340c07651031908580c042d02052040380c010030100036491080c1d1103054641c251802081c0903500b503038030b505031441c44018001155419044d1300e2000140c410b2009007000300c1c0107410b403517140742c5452181d0365a80f01280c080c5404e41c00d000311100010101001c2ea4102d880140641da09503441d1000d00d240701440385213007a054030090100c201d8039a10322482482460180e040140f15003440c48410007559900b4400000035401c00c401d100c0069405101d0b08450814642d01600308608080b00c0e030300748101710328040c1452019510b6405417522540c00603100d42e00c112810008490002c00130b90983e00207040117940044c0c04010300445003820b0300003034505101100000b45107038949071840105c0c1c0142c4510ba1480d07002c24401c020844e20489404c3c0640742c4680380505610b4021440b010b030250051030541045640b04280c1155110325000784000b40d030161403 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 530295827 1250 530294577 530294581
    0x16020303040b250b07050304020316060507051c0206070c060b130509060a060513020c0118050c1e06030115050c010f050a060b19050307020f01060e0109110c0c0906030114 75
    0x882c80c19002031491400000e0402d2200b440000c2e011004001035038070006000140e55403141c20744580c1c00c000c000341d0b018040c00c086034100400300350b01103010701600d403a13030303a11031195003030941c03074010121041c1030f5030206483c446040740e030000340c00ba40c0b1119500c2c1150b031209180c03801034081c2104203202178102e041c1040072105d03d4000e8205521810410084803501e42e40e04582d102607949a100390394000344a811503041041682d0010000d50b6050070001c905c012403da0200310b07800442a05030b602e40c0280300c80002c58a0007c884842429000c007502c0f02049004000402e24401846000c012005d50b4030b1600b80d140c055419100003c00c88002001103500303011203000503150403141c2c0b6502d10301d0400c010800411050a4907003104e0f44900e40c181d0a003c00c00f0540d407a60000c1e060805620032402100b08030070f002d00441026181207044082c4552500010b0415941c00b84403810100e5010b02000c04400c90015500142c80d9046031540825101c080c0400e00400102c01e0b02c0c0c2143c0d0309441 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 530297077 1250 530295827 530295839
    0x405190213050c121e010501030203060418050c010201050f191505060a082502030909060a03050a0c03120e0d0611301e0403030911060403050610140607081602030304 73
    0x1024003642001038100c4c9125582e91468402039946640d083c0b0101505000140401c1d482a40510741c414030140002582d422030340e060707040e8500c0c1800b00301d0f0158040c80e60b445881d40d0a0281d0b039084410a1400240303410954088034102c81403002070345004d03558881c0c2c040358820f421107120050070090001951507040c00c20003820702d40101d45006038806140494030440b090b15503003d03080f04851b4043c5007440005402c1100040c00070b41450f50022103010040003003a81404820300c540c3c402d0302e20804681ca5850488023101600b80c0300800c1c0200344002900944401202c01c6080e5071212001030580054000f640082c020344000c061007035180c0d040751001e10407130400b400c0c01c007600d1003c405841d0b951000300c150303050385030724640c121940d14030214001900a405c003c41c51845000406850600c01000c214980c100d0790058a060380b0001c1803024103482c000c0802c001d8001d100222103d04036200200e04a44141840200300101c0043c0e40700d83d029044001000d1568018140c81d9950303580c03c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 530298327 1250 530297077 530297101
    0x40312022b02030f090a03050102041805090a020109090903110118050106080d1b03050c0d0c1b0b0a18090204081f02070b130809030d080106090e040519021305 70
    0x15009800107401905002152910810200c20415980e07000710314045801c828100b050300241680c5030041402c14020002070828000380c40035100c182002e100d0350040481d00c10568402801005154200d15465230140c0d0b4000380300303c10707640d020354003003011030ba240b500300c0c1da5100d0345012520039441d00c10002200884010103c010354002c80090001d203032111801034440355810354a81c04603103994610b2410300c0302d41d44120202d601a0514138107180e10190010b041c80b402c4e00c60500003034807012801040008940c0300d5084514001d401400103030418004180c02e03c10940460280050b500f6659210265010032101403c007614056403030f10b0743c40045965502c410060044003115002003408891464400d699407543c10905d00da100e6180c400381203259440701c0009079612030b020000750b460794900300700140304000d0a81e43d1100380d43c540840101258000d030020002c2202c907100380300100d45d001502640c5805007642c140c224109a200285141c21841c148100c0c40e4284010040080205 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 530299577 1250 530298327 530298343
    0x2010060f0f090203010e060f060f040b030402120307050a1e0c0909050105070203030c1c0b041b03051602031902030c07030c060917191106070c080d11060c070804031202 74
    0x103141c805411030300c030b58116007607003c00d02841e4100303001500041c02d54035006004c04030544014045502d0803c44901203502c560168115008014000090208600b0314900609008051b140503500705065943c8103911480d1040313010700420700344051214095200f403800103500d644880c10020040e600c5c0521406820b0500c1e00341c90a500c2d100004041500101c1164440e0030481d8610b80790442d8443c0300d04800241c00c900b0b00c0403a9480900f040251100e205000803801c40c648400f00710825500000c082c0d41000f001680004100d1004402c00e075000401c2d14003000781089035900c1214030003000c0b07103903000782503091019104001c8000b0038000c107402c540083d14256941c101c44a0b0b1652410380e808540e0401164465204401c0360304074030801400300141070b1059011162000c8400c00042d299080f401043d50041c914003820130001000f00040d265242150512950310300140010a45881008010300c040044c0054820108140141124080c56100881e01c0442048442c000d41d10030718 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 530300827 1250 530299577 530299589
    0xe0112020f30010f230604060b1209120a110607020c0a0909020f0306070c210c120e0307230405060303120c07050303010f060e010309170a0302040803030c030618072010060f 76
    0xd0b10022541da401c107030088c01c060f9032401e000b0510707085d60020305e070800d2600104a075040c3e0203410352086482d58064010514000c01d41d8440200c0b221046c1107030700b481d2024000200790752000d006040c66864400c590350840741100c0d00020310120310700100300c81c0000515050f41c94003c0340d04229419400120400115001e032100c1d4800114072124100f04035108600e05c1c006c511109051350020759022413140740490303e80f03800700388108074034003003071600420f604000c42954800ca1010000340810001c2c1c01c40701d0046070300f8000c5003404004651244107030038185a2443c60a000210000020002c07204101c0d407000c00c036030b5250794039004010090480d01403080064500c0c01e65500941c800d00402100c690081c40304444c8540421a154480e40a0a0f010050640174000003072022018006140b08201c072440c42d0307030340b07142031010402064480e0b028101049001d50500091075403001c07050071412103501e0029032181c103003a180d924000d074154104483e1400e051010598076150882d040440ea0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 530302077 1250 530300827 530300891
    0xa150b0a0302040f0902160b06010e0904080a1404050a030803041a090307022701050f0109050a0f06020c01020f030f0a030e030a27060c02060703090e0112020f30010f 73
    0x501d94010300240c0c03003501c0d404d200103e0f5800c0c81f000803803016010f250f0441c0c0141041400950520041403d01c1350848013524458000b1501c4032403582c208410488101200b500c0515141c00c0c00700003540d808540c000600f10750301c040f0010b010043d1707038a9214107220901c289135490f49040c96101d07a0780c4d444450200d003e00c85450910b0000e02c1400200010045c2d900400740c40381e8201414803078030000010302e440c10440030103000621502d40c1080c82000d4071000518000c0d060a10300064941011260820b045501504030060203d102005592a40c14180002c55850101190460182c00b8111012036035020018000a559800000c1c4000041c4004880c0c4032000c0450204408410700e40700f4400426000f000450051614900901505200742400d42e901c94403004642c1e42013009800c40d2141481210402003903141496241a90010440b61020319038019000d12184846600c00f102100040302510034452400b074005045680240b14208000c82081001d90903401c044601814246 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 530303327 1250 530302077 530302079
    0xf0f0109051c0c11031009050601030605060f130507020307142409100216120f1205070f11010f0e15010504062402010f050c091305060102060a150b0a0302040f 70
    0x718800300034684090311915449226405510f130410451100380c40340d90726010b21120101c44580700c0c482c0304809070040c80180700c00d40c19450044200e52000d005148640c6210343c1129850f82d5102c02d900941c10f41c1e000102e800d0b20303403690613031175801040c4004080b090700c8060044003400000b0351603080c6200ba21104140704c03403110b9510b1801d0007681c0401c80760b0804d8241c0175011000350010f040036004045200e607426901d07103c44011a403110700350400981c1404000070503560210303414200341e130001020000e9080050001d88521802c0c0c91007014020b19502d03180f1180000e60007004080c880003400d0256010380c0500300d0710b84166401141540f144040041460b003800d1043d4015280d60981c1000d0716140340b09145481c034040c40760b2000719034035242c04901010325401541d01030b0400846107500c034661a01002118641c1c455006403443c07400041260ba070380d00003440c40c1c01454421000400c1034442450701900c5001d604000d40b070074000241e0710740f0241c2c198001c0003160401420b0701046 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 530304577 1250 530303327 530303353
    0xe01022a0f1c1704230a08030c0403030f031503030806010203120403050d0e0102070507061b1b0501110105060a03320a02040b090405030f0d180b070809070602070b0a020f0f010905 79
    0x140c082036030081c0c220385100c504010700118000f10120341600000c1213806c18485a0780e0894564400c4401c0080254045000c000301600540c496400d24450b0400f030003840e034450000c401f5a00144009410420701d88042111a4000c2c0b00b21038003444480c0a1211a01e4a41000352050f4043c07500052010314095245041000610950306090360007070140440302c0c60308808582c0417041c00010010740c442070454100158009044a460000500d04040254a420000b5000c480520306800150341018200009a0f80301d0303c418003625488042d40080001d00f5180010403243c0e501404035120042200320101030780050201d015074400c860901020b22030005002842e407094070020721940c4144a01d0030000c1c6104082e02030b061000038001100c07205801140d03003001100380280d0b00122000284941160301c4001140e102500301c0042040c2d61400340020b40c1e40002d445002c00c1c503000426556022882400110088910007045405203804004068003c2c00c0c1c00000300c4103441b0740410a156 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 530305827 1250 530304577 530304617
    0x6060f080d050f0c070b072405010308070f030e100806090a09080406081515030406060b04230a170619060e06061804060b09040e01022a0f1c 62
    0x2000150344860901081d00100f0b40d40c0e4010441d4060140116400460740000c1c0b00054041b1038081e0546048691a4400305542072a01030041b02615044c50018804600d9040c100c50300c0e9944240b000100c03d960f8181100e15045030566542c0c4a4884030800c101c041d440100f440c0541d9007160000030580303810340f903c000c41d400c101c0018900e00007400304200381e60007901c0f8254030031030050170001c2040000c1c0006240004a559001100c44080103001c14082c1038881c01020b00260f603521450070742400445400e140004c2c400d94140d8020443d00401503e508003010000c1146560001100400403044c544426040311891500d0b200160428002d4210b4083e40c401c4942110300c0ca04103494070024880c1c2c03a400903e400240030303160084074402c0c2d2100c3c07081a0080009a0405444489680c1044291420841000090782c018421004001e4100c1440141100e07021030120307201c1c100d052147d051909115a1030428050b0300c0101700c410150030541411046c49945419181c2c010602d2806 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 530307077 1250 530305827 530305843
    0x6030307050a03080c0903010c0306090b01090608010506071506030302010204061e08040221100204080c010804050d0e0d0f0807020f18041b05041b02190f060203130f06060f08 77
    0x4000d5101c09442000f290081c000550002da04003545464070000710046800c1d50100940040041d80d149810040b0448522407004101302c246401d40200389003107401001c03a08107020b501e200742c20020750507040141040980f100741c002103005002c2c09a890038081d00030b40040c85a140440c2c02e0f028a50544800c0240c6143d00d0f4116445020280d22180c0034406042400c100c11414000c402d01c3c03a00300c21808000c8604440380250002d03036641e0030260003038140641c24107143d05010305032040c00f0020314085114241c820301ca01e04400e0b44200000043c1288998501c054041c2ca10030100701c0c01d220784000207100c510300981c1da1040c50341c401d00502520440d001200c07050324540e803012030001104404440d07440320440c20f2941d80680ca901c0001c085920042d401d46041443d00c0541c05010340500c1a84404880307d0108031159101707454000d411801c5410040c016036000000814926140010407903140e0040307a40d00c0044402d1400200a040c41d001d6030750f02d4000381100203a10030001542e21 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 530308327 1250 530307077 530307083
    0x50d0b270714032403031602120109080d0903050913290f010e03010f18050106171f060909080c1005010602190c08060403020a060c0e01090b0a0c08040f03050606030307 74
    0xe442c5684184c1080b00300e00ba4800d03086400380e036100054480f65410000742c403414240031450076100e081841041350100c4003103130b90800359041100c04404240040305885080050100c0800c3c820354515045445100b03040c582540141100358225440d462a1300280c450000480021800b82424014070340144141d18030550260583c2a6140c081d44500a003850348500a00042101c1904143c0442552107110f80a012142c1040144092010034003d0000400c110340a040c200000b00d0703451515440c9020103d278100c0c9486440c042c4060fa02d501500080645080410804081d40b030840d6455015402c064890301c92100710b648400210300c5a94121032040d00108038494192842d00c030070b10360b202c00a45542d075803000009500c80080c44444d1195110f40d01402c0000084c0c507089045500701c400c03a070b04104020600c0705c1d10781d803c101041e06540c2c0d185400750320713000c1e141e60031a0800200ba000511071140410f0014280e0700e880251019240f00e03405603032941e0388503028036669015641001d = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 530309577 1250 530308327 530308367
    0x40f12181a031f080f0a03170f0601050f0d060e0405010c080105010f140c071707060c0804050d11031c110a080717120c25050d050d0b2707 61
    0x10450204812440740c540741c402d910014100c0c0e5a031002c250803d5645d03400960306410070074440b41059404280440321412662040c2680d083c41d41e46204e0500c0d0050184c2e0500030005104011221755400b95649006801018041162500c00301c107100381c03094800302c0d500d40c28500503641c41c500402140d8141d030b1040c0e642100c026a801c0f81150510020034204502a204000e51a0020000c5c8908400b4280c002020040c60050301030062905c2c030258040f80030014000070b8000010a5041200c0481d01d04980e541c01300402c034109480c11000c2d104102e0341c148070720440500d15035608003480401d42074035107941a0511214084540b1548200d400811102c0200000c1000804800c600007902901d00c03581e608000007480c038144202c4c8280c8034002c582c00f01144e04d2010030181140090454006510f140c041c041030b54800d542d42d40c40701801000e005010801180103125a070001c042c2c540f000304807401d01200c500f4850300301e030010311014651019507000103290780d001b040d590034030b2101c9000c6 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 530310827 1250 530309577 530309581
    0x70306151e0806010c0611041e0f030803041401090c06090b04120f03020f070e0a15060c0204050703110d050f01050301150303031109091905070f0512040f12181a03 72
    0x2040725418030042c0f81605016900b40240c2c00700709184200c000843c0381403030487d5503c0c1446010800b40308c02c401d0103103c0070b0f0710030420700c5240c40f1401e40504581d0700040c3d15499841f1458108401981840e8203c502e620342503070070062011f0080d01d20100d80942d200d41c071a058131841c41c8021449035009040c2d0a80b001204c0c04000784550b1401e8021320b000f803069800f41081c080109040c5034181e8880c40c1e01d03081c680240520080c25106001c07801c4200a920703040c0324a4144003600404101130060b10550350b402c000786c43d0380c1c000e4002c503022044040c682640c601e00446003100902058442c03003990350000c4000700725402c0511401c07980350700c0c607201d55021910b1541c003200036001a00c10040c101f00c0a001c03c8115403243d50806008600751201d4042c0541c41c07611110840300001e00300810860081d48801382c240d0000300721403107214024042c5255596904200445600f00751000386941c011984400641da4485908d0070f0100d01a0001061316665103421000840d0030301c5144101c01c42000 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 530312077 1250 530310827 530310887
    0x50a030e030c0d1107240207060819020c010e1c091208160804260607080f01051002011d06091e030d0b0d0507060e03101e020307050f0307030615 64
    0x2d1144c20400c2c0003002c80c5d5510351135108080140f1040340140100c6a1804009404c040c0c050100902401c00c0c2d00c1c0c407841d035203483d409448804c1034903800503c102c1da0005400e20003180a40003000442e04100441d0254aa120a80f4045500d0403607008001b608500c0086004459076000e002a00d802c030070303d9800d00da030200e10a00e21003101202114078450401000642c07201c0f1000c1c011003001540304510040c0841c1100a040c408001e01800400400f201005101302c0040d19445c19123809a50784c82c0380840299042e801031641100d018490301c80c00d1800808898001845442044108244d604c452850604503202c0303201004042100c3d0018040c0c000c0301c1816a000805802c03004000c4002041d007034481e1420009181c01c450700003280c1c0001c4401c9400c00308400c08907012044410021610a11365560044002010886815400202289840f840b0380103403040d16404040151313513828900c4000c3c2c01044e0030b1146c0102c440681c845a01e41c1800390807a8081c1c00f80d8615008000c0c50800 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 530313327 1250 530312077 530312087
    0x1e090f06030c190c06050a1509020c010608060a050619030803060402180d15050106050a0c0807021908030306011706010206151c111201021309050402011707050a030e030c0d 76
    0x2040303490040c0040c040c0300304400407160342002d542000e4462861a40103801c110f4150741b0002d1040c0201c030300f082524076141c0c0c0031300a25003c8a084110043c2c4a070840c4503000d000d040c907544000d16520504003408800100c80e8441030103154111070303a10100107002c159090340c0546200141102301c00748005910703400c040c1c000b01152000c500450342d401c0c4050002414031030348d2800035078440141442d81c01e6880d8a034401c0d035026281908105042100391000101150442c0c00000c11184000c0b90304001c43d00e0380d0201006c0c0c4d5507a00c107250404ae49032a406544c0c1d8008880c40e03800100780030040743c0b030301c821541c1c050301403501a400340400355200d0b050400581503041415422200c045480d030160407070111951085c40c8983c207880302c20301802080250508481c1c2c58100e05034410407003207007000117080d11702d003c0b1404000f010400b59200e00059035800120b500701c20b2041a0b400c00c0040490707101000f80401c0800f9142000340c84000b00859680e80110900c0c0300035a230001c0c9041420700c1c021 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 530314577 1250 530313327 530313331
    0xc0a0b0d0506180405102703140c03270904020109050d0302211b0c0306070807031806020a020114061003020702060c010f140112080d091406010303051e090f0603 71
    0x50183c000701c1c002c5180004801c142114151846e801500d10f4031000366150044a50303100502e460040b1140080c0602c203600c004850000f801d1000b480b0301e412007146101c0c10359010180c1d42040d2602e82e0076506d59032411a1442030b031180d52500d1403c080e8510710782441407138052501030b915030645a0805080c45101019050160103600c00c0d940030841002c0c1c90840c14481202d0b40e41843c2e115102012140244881c203040080c080d00241c001c000d01e030b2000584140d200490345001c3d800e540b0303401c1d0b09400a1108040c0030380c245c005080c46100303120403500180042e488640c02000100140c0b000e0061385003059030640d5005001d85001c202103071003500030300490b90000380018a0a001820860300711040d070445050840d0311800400b980023400f81610b40103040300792110340c485009940e0168984264070200d11043d903180d4205061040c8680c45039035640490045441c603586a040250158010045222449044242c002055111f031030580f0b50450340906035042e03102d07404d000c000850b000 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 530315827 1250 530314577 530314579
    0x170c01062c07080c03220203120d0c170a0c090f03050d08130f02150405040603060b0a1e0603201c0506220f0e1002120601050c06040b0a0615020c030c0a0b0d0506 71
    0x218841c06c0150f542404940c200e42e004100855664141c0c0340824259088a4030400c02d01c152726000315401c0999410042d488005070742c0005840906620a5400c8a040d4101044481c604030002c0200440043e1001c0c0c425000d4544042c2ca544845403c031035050000d60003403010040500c180018104003d14609009001041c07906044c1c80314042800c4580a03441510820780b04c000e14030240c1041a03414010704001c0a180085608202c1c881c0c100c04120b10600f003c066403448410f2400300310211003100c0c161101c0900d50350340c54091504c082c1d01c0150443c102814900400b0803028038000542000b00c50020201c01100c0f21003205a0f4001c1030941c50700b285a50312281c4c0c02d0003941050100d5001d009022400603120040e049000680b1600244114180801000700c040251000200d20340e02c903510204026066403403201d00d1002e007100b07078840405220aa00d90a5043c1e401203800c1c00070060a504a88901c5020400c01c1008402d81c4102c01c20175104008101c0214500e130855070f80070300 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 530317077 1250 530315827 530315881
    0x51006050712091728030917030d0c050903010b0105090d08030c07140f15010b030a02030604090c0f0e0a020f121f09020a0813170c01062c07080c03 65
    0x140c1c1e1300903540008002446854682c101400c1081011480f60303c1801c1004905d440c440810b00e607580c00fa101c42c89501502003502c5600469800c56031040040315003c000e408001e2000721030100c8040c11680000010301e2082d403c00c404eaa0943d44120b09442d003840c80140b01c1c801024060300c8156050344013602034a0790b90803c20044000c43c407502030b0203420110400040ca0344503100c409d01030401c6259488200c0000700d00d4010031146109005994100354110001030f540c0d140c3d0740009000381030440c401899801c0a03800052449080c250040803120f14001d40c107026600e50068808074411450b2031406a035040c010025801071245507a40c0c0983c03c02041c0104440e1018104a00500b0394000f140c0c5540028101c0b002c5540300c0c1025400c8400146101c45034006580c0d010000c4103c5001e4450001f0301144800200000b500500000d10a40010304408080740030200aa2901070516010071035410010860701407080207084e210340b20151039035042da190f80c0032010078094040f80b02d1035000 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 530318327 1250 530317077 530317079
    0x50f06100c02011808071505040f090e2a04060b0c071707030b1609080c0d08030c1201090902040509031e0a140a031e0b0a0e0c1309050a05100605071209 67
    0x1074240784d0031000e001c9080080c00c80b1341ca001c515070340031101000c00c5001c002d41440108241a014840441554044000842c41c544e040400d18a4680385d0a0890307044042d0f2083d8104080c0302450852005400b5202442155190700d074280c280c1c4039419044500ea0b010340d000f00040702801519512200042c1d054a03801036480e00c071807000542c00d03184818151180990f43d1f1400b50001c0c8028018407100c0d0103458011540c000007692900c8124010f0454800000000d00d160300c0e2804403541504c5090031098a941c45684040003410016800ca000d00e1504000c2403000b0000010b403011003459001c00e20050824002c03d000c2c40d080000141c0600141d9140343c541e003d06440501903881040e0360010329030108615001600241049400c40c01d881d010442005403134016141c810384004a245031142d803a102d904c115544900c154843c2d0703c072188580854010314640021740119a4140140b00e0764403240420104040d00d40716040c04100d00b04181d800040500e11004940441c43c01c00890603 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 530319577 1250 530318327 530318357
    0x81b06070507240f08010b0316050f07060902040f1e0e0c061b1203160311120907061701060503010909060f052707050607150b030a031101050f06100c0201 68
    0x254a050403e2074100c038025512620720b42d1003086403148103180c3c07400301801c0d4035003002003000d403001070104081c11801c8000710183e17500800032141500512007450740c0e1002d15041285c0140340c9520201d00c210f0411550300c402c100c5074010790342030049203600c0b20340c4806400d24020042441110f518002d01520009004c0f07a640c1c04043d208010f22100c0030049018804002400c2c01003103103000c111142c06009011324603006021149181c41103040029100e1044803104089019110100154007007000070020f04560208000d0300711941911105007046244010024207202401690000344062004100740d01154005480302030080d680000d512516240502c25280d0480f0803e4406120174807c241d80861100c8041c209041c42c000b03031400c2818000000c0b100e106008016100301074406600070f910b1295400300741d14ae00c0040454030201c00a00e0060100380740b400107003000f5440d11000408000050131403512481000f42212072050803140c0c1900d022094502c2607041003014200583c072 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 530320827 1250 530319577 530319599
    0xc0f0406080712090f0b160e150c0a050706020f0a110103052205010c1407021021050a090201120e0a0605090309060c030c071212030c1e110601081b06070507 69
    0x244d207014180034904880141002803084601401d0405040c00e040d0680c50b085501a1440c0a0748408035200c414038540003001c40031a0059041d0740b003a50041e40100c5041150003c0e042d021150a07800741e0740750840884511341c4406c03250708090170751403003140c183ca0303198421361101d90301400c000c20442d50701441d03132500400c80d984083e00308c5841e9581c1e00d06c9200542c0011951740c08141d442c040e20318100c50f0394007182c1c1000c81c58006130140205030340591003810350040b1710388901e14844010000c0b45407a0101001820410720140d001c10040c04040c0002e10050080c0c7c084c80d00b108009252051240d41d9110040000400f905120f000510040790250340d07140003040d0a8041d5030045440d50a05070207581130460035801a501d9400054a600004918020640d016261800e00103500c1d800741c03030181c1e503440c0d808001d44605018586510b20498000003001c0307044102c2c0c1c04444190780c852080ea6601c00c551040c04c801d55500202c40c454034030b4420001c104403842441914800d513511038140e05 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 530322077 1250 530320827 530320841
    0x30f060f0216060b04060504021e0315030307120e0406080303130c181a040b031002210103080a02010507030c1b06020c0d111218010c0f0503040b0d050c0f0406080712 73
    0x1078495101c1380b40e410130707203010701401c0c2c0600b004442c02c40c0780c00c11450714048040c0320000d512a40e13040110000300310102448c2c42540c60040a02520350324103140c03404200d80501107001d1004100800d000d09403905051117030f0001c0c0d602c00c03401146075480f200e00d0702c0011500e0140848101014800100f5079480d14a48011820300d01403022502c0c00315600115035071490444640d0240307103440a00401d55038009000358152141d0900182d841422003903822460700c1d440102e0511520840000041196a10080c049222594020082038581201c02c43c20781d00c1c0340c070340b07100001c40c150354030190b80e140f0f50580e601c40c40c030030100185401080c0d480f040c1044001500200800c200c80c10b07001c002c503024032030320301280340e04444186231010881c070300031a000d604d4284c64100003c01660100f00000c41c016010031542100850792103a54904002986a1000d890000c4031030800d0040340000c88041b00303541c04004c40c510441e04141c1061f200701d841c3d03500103120074100711600303044006980b82842002 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 530323327 1250 530322077 530322083
    0xd0f0231150e04050703062c0a0206040509070311072a06090b09061c02070c0f030206030f0c0705010603050318010809190302100e010b1503100b0a0201060819030e0901030f060f0216 80
    0x60b94201003400b041040165408c102c0186400605074480107a40307036811a016580100c0392030640da1608a005c0300208140c844980880000080c0c4a061009060140580002c9a2026019051200401100c0d01d4203441000c000c52100a030500c103024040029100184014040c58200310344050100400751440d84421002940000d6407024030020703a40da8000b411400c0c581e02959451940840c83c58800202021041c10500b00483e0700003115400b1160a41d801c94001e00805459081c126140c2e40040c11409012203000c00201665000341c59a42c401c002e100064040c81070407d401c040c1c0803109920071021800381d00100c808858803441182d01c500100c02c000500d80403081c060180c480da06410b06001c2030014420491652200180c907c00e442812002503200c03180004264090031543e00400d080f80a42c8441e090007180d01c0c10b69002441c000e50b140f0030041940070508c00000000c1c0406441c403030601c1a80800b24400d50060f446076501554014070b041001f140303840c200d00b0a03800403 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 530324577 1250 530323327 530323361
    0x1211010e0402090604143c3c030106030b1302030c0d0503040302041d1f06050d11040b040b030303150d1502071a060f0d0f0231150e0405070306 63
    0x1412141044c4044809600d1505266a1440300b140403003404041c401300030448000116190400708d4440460011f03151100f4003c003070550f0320808040c0507208034500c194042c034268419005041c9014010401101d4008a0904068a6943d03410616404041060340c061045000d84016074480020411205000360080c40c1c13100d0641c810081071f83c942d9016003804101500c0c0000101001140d44c007480a5401c2d038041880d4030382088140030303107007a03406540d0103080c03003100c5014890101070300c85900004841c1003050200d02020802100e190303401e000d8266205100052a8030102d0745800e80740c8000520301e00712022103594100c88640001c0c0da80058a0700800c9020400440d2410704400319021000035405240a402164070030a04143d81403083e1a0510081d040c816076840341c14004ea000b40c1501c40204081c10341940310380205508025140319180c40c2000d0300828854180d400600902448490b440c0014000000401400a550a005e8403074004000391390742c440d24550000100130 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 530325827 1250 530324577 530324609
    0x60c021525050607081e04030c061506020c18010605070c150c0b09060c270303030108070614030c09100512040c05030d02070515030c0d0e0a0605011211010e0402090604 74
    0xb6504281c0c02410a0040c0803524040c4100304103c003603d441206015002c2010b541d0703860078111002d5180043c0036040d546002c2502e0303410001070314203400361b81854007220b10340e8110405000c83d0318580e080d00244140101e0041c0505d0b0701c10402089918082c916165080c0d45400c0445c0d030085a03c001c1ea80401c1c036800600c010000034100031a1b000c04420050070032482c1001c0e000c0b060748074007103440d5021034129220000120003501001c268a0707000d0200ca0f103e45e11456642d41d01c542030f01456010490f020200c0c41d140800c5003c4074800c070b00c3d0b048102c3c140a0b484051015010b160180c1406001007441468801e40315066020710890003103641281311840e02c0181810040030211031402c41d0428841409142c03141a800c0c5004c42d006195550780356a645004913190103582d9002084500f07114030f440c042c9400040b03c00b541e034000c510801107a40ea91078000c0312481e03680002400c00002031030802c869802114484480b903800307040545066110400078880364041c1e000f03403500490b00c0310 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 530327077 1250 530325827 530325833
    0x9060806040b15010206010501110f0106151e020a0318030203030d0516030b030a0f02040b09101e051807052a0105090c030303040b06030c1509040c0504060c021525 72
    0x59803d4000304008400c0360310340d0f5941c000035100c1700305029070b0f4180044001c1b1220740350070400c01602c00c2d00c800d000800c4015101c010b24080c4d8814151054000307200d011001314600082201c213409880c998006140c03418541d601030b51010701424409240c00464100000941c13018402040c030602001c1c00001c80345003190f001400c0540e0304445204161400702000340585001840c2c40b00c1540042c1c0461440d40e00740700250261000000e8641c001e5410b0043c400034a500d40d43c1039066800c0c40780e1030706000008149024000741c1522030b603580008002282c2c3c5103042d1040419412030780900c5c110345860a2020035400314462032051607501050244d250100080c00c2c4141904015400b0141000724091400241d6900011f40003500726001000811466501040201a01030010b800b40144070000c100c2c01d44075401c10700d401c41c0078508204848291034402d0381100c05550302e607103075001c030303013889809100040c41d02c5100846844170802c0480422140010318000c5001203484020884915103 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 530328327 1250 530327077 530327093
    0xc04210201091509180b0a031a1501080a021b0304060207030302010b030102042904030213090b0f040201140d0b041104081905070311033a11071703040906080604 71
    0x644255808280b80e88421040355005110100700c0303210345c5c40164500c010001c050700402d40110341e00c6d0b01110340070b000000c0241180505d5440301e408201508241c0d90043c1c04180007032100421400246440001012080241e0103004003640c000d81d0460070104002140b441e55000381c10040150740a0501001010360900403455030403400e0b4000c2d42020b160900300c1070052400b1007202204603001c0500c10180d82010f0a8800454005000840d81031990310b150340188501d00c01034071580c1c0c070100050f07001c40d0341c406110300855044e0b4a0602c0305050402e200080d4102d0003c2181c0140c03500c018410b02d0381c49019603061a040c1103052030f9a285005809880d010384801d00701402a00b59018101080020420500322500600717604801e58040c07000a040480700c80d070b182144411008146a003200034000d0600040020303201c00e81c040c907014000e8406808140c0d01c40700d607074840a0180000041c407503540507030801c6201181d06194031071080105546068004d041c60ba4041000c03c000e228800c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 530329577 1250 530328327 530328329
    0x30f050c062802040b0307050915040e1b092b080d230903040506070f060203100f050102011413020111100c022b030b010e04090602040806060a060c03080c0421020109 73
    0x42c110b00d40791408003056080c0c0401421802070040214030ba000b5a10348032600480e589810300087d5079141c80301015040754006075102a04250b8a100d40425006210200d83c04e050006001e21000c03200b000c11050185800c040c10480022541d50762000180910007509008181080100c1e000801140440480d2682d08410b0030803150792050080202c2e0100859080d0382081d21500c1d500d01944c2446c0d055448201d078001c0210740300100b08022071400c0c00745502030300d240c45158400555164012405e1ba20000706512100079000c000c07610500c403a54200b0b0b0400e1041c101042d41465050034603091440001d1220a811b4680341c1740c4001a6040c000d20011003040d03080f0700c0d042c0c0d5a5014130211025820303146018103503911011425a80241c0c0340e0a50003030018001d110004581c500400070b074000c0d1288a90314400d0300301090561030b041c03c6030300c113a41244d0360707070030350760103251401c450a15000c4c00c1403007001010440420107881c0641e01d000103040503020301c40041e206200042c04034400f = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 530330827 1250 530329577 530329651
    0x160515090703030915090b0304060b0411090105340308010608010b040f03080306040912050d0b0414040f14070321020703030905130f0204060f0809011107030f050c06 73
    0x800082c00000e070481e80d200d00f900e00078a5005106010201c058440c500d0f55048403215000100070001040001c1e000100b4554090718117010800194406080b18000e121074180881da00340f0101d44091204210709503000c01c01e030440d01d448400c00c40c0f02602407082c08030950000f0f043d00010302038140c2048240e030050461308406403034581b9050114401a415010050850030b0002c081101580c2d0798011340001504090050008095040013509642c400e10f000c2a01d1410480d10130241d20b041c1c400c00307500200024110b5071b60b640d10380d41c0120010502c14100d0311410401718280e0350f41e80070003841c00994881e01c8510220f0810f0190320890400f410012011548204028400603038400540c1c01101c200b55000d18400310405a10009003010781c0350040c0b418400302d00003500c06c0d480444006550701c1512100d4070394035408000c5007a220207146000701031078100414800203100c0c6280b001244400c0c6800b030306080100048a0610b44103a6960491000340f503001d68450914602c90406040c0b = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 530332077 1250 530330827 530330833
    0x180303090402070b06151927090507020c19050405040512371e020309120312060102030a09030318150c05010c180515070b240103020a020604020f040216051509 70
    0x504020502c00320915200c448081109001c814144d1000c0e1000001e00844910401208e081d00c40d4940c0004240443e0040018402c800c034404a504020b0901e10a000305000380c1820300c0d08000038031014000140c001c94103445908414040b01c040400980042da000525000e8010850501d01540390b11146a9139142d89800390010140d80d001804103180301070350301c4d500d503094404640c2a8154040d4908164001f52101034031050004040005d048d15203469130504800e46824004aa40340280c1c030000c80032071540c001c20f10200e4020713840d9013501d80400c40c05501381c640302c00341074211050101d249400b094089401004007c402c0c010780c1d003d0b03181da203058003a40c041c83c00080403420141c802d403400390341d15019100020720108110340c14280c11100f40d1090b400c00d42c0302da0a900720b46a00c100c0c1c0b40c80c022805a20650700c84e000f00c56078010182d008000716180c039020041d408642105460788030b41d00b0081800c50480c5c0e040c030000c00e14050304c00b9141030404c00700c8103400c0c00402440c15801d50 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 530333327 1250 530332077 530332087
    0x5030f0c01082202090a020417010203040b090706050a030b0d061107330506060c06090f0609011b0e0a030506090705011106070c03050c010e1c030e12180303090402070b0615 76
    0x250307510b4298408181c0444c1d40c00e85a8441c8951b202c001d1045400400c01c0c0154144903e80b041015002580070354412406201c641e9140f08425841d0840f0b40601e9000440400c112249a4482d07002400c0424009150302c2c00703010146da03018115210511100c82904000c0f500c8410b228216003100013400800c84010905010b441c2c0b40e440740c03851104c5180c0309940e40c0011402d40c1d12260255165852100110703038041c24041202503945003170304000d00880c85803000103000808180201d40c000e1040e0070000b424501055004d850b242e030302402803908071003c0c0c500080415030400c8210300982c54600035061043c1814001003032404120b4070f01c507075940120240007565510500c11841c65405240454460303001200c054007401001c80e160080e80704403400020b010004070724035108010f5a131800c102c0389554502003a29039951004102d0290800c0c414007502100c4003020044584000f41541d182030003010005089800440003514881810020032a0038103098086000c440c4543e402c441c100 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 530334577 1250 530333327 530333371
    0x6020c01020d090612060b0309010209030d030e1c020a170418020906030a0b0d061125120e0103060b0412050d020a1e02060d0f0b0a0510020c04020c0705030f0c0108 72
    0x440301a119080c100b01d4042117404400e00558401c3d00a001d250890990b0ba00307003a20201d020390403030749810307109020b180c1643d020355020b0311610308841e4039400640040343c14030006c6d260704107200085001758042c107001c40001920805403680d501d03e40345000c607191400c1001c0d690380c0c0c0b03c0c8003620101e6a0f1041080c0b02c019603070074065940c03001e03000b2004100c4080d2040031039400841c2d20001080581004c0780c0e2405841400c0251845c0441d9034101c000d1090300c4545045002c074030301c00182501020340080c150061060040c1e070020f61040c100802da06d07907078694007011a40305074441c195070780d031800b80f400c10031800340300307159000d4020b10080c0b40707551017511140d008407a0715030b00302c0300d00b060200000d00b152030720420b9880f0412142e00410040c0d012400000141001044252003504482c0d0b0109540c07400b455a4a01048141d000307111280c1c5040c01e03c802540802c005440b50300c58076800180940e003c204000001d031001000e000c80750b03a92400900640e20181c0303c2c002c551494820003100c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 530335827 1250 530334577 530334587
    0xe10020109141906051b0f03010e0604091101081b040e060906060a0824060d09062a112e230412091e1d130b09010b0d0b0106020c01020d 60
    0x24144c00210000c1e89440b41591021442260740121411034400b04100600412003400f5504039100f80c0074070030144c0c1d600410082200c104040003045601903400c0ba07240c40d403291211507400490310900b9940300c00880e80c0042250082d602041101740c007a401c200da2418120615908aa41603440714105103480c54003400e1448001d081e5503603040c244044e03119400c21405d5522400d01c0261440f41d5035640950003c003d440f803000242c61440c1420110040c0050088100e0100f4082008000c038031115480100c40c1081a44500c2c4035621840c9141c50740000d001580b0b80b010302610303101c455a1000301ca12501034490b40c1c0f102100443c505100060790200d614080348e4407a0b403040052020080f841000e036215482c0d9003050000e150116040c200e07211f038028040041d10314441c0d0560000c44079291001510704122020141074035000980b000042d800604070b038003c0d0110001007644441309011410310642c0f15001d68400d046c40700100980783d0103101c1001d0300c090070b00c06405421410100680 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 530337077 1250 530335827 530335873
    0x90f0b0109060804081e0409050603070812090402041706040b0a0207031d0112050709080c0a03080d1104080102030406020a030b030a050d080a0e070f03020f0102070e01150e1002010914 81
    0x1050050a0002400300002c0c5012194410480c500403282c103003151b039801055400901171030311003034540400725089290000c1c0038002c4609a40081001c150075104041942d0010254280c1041d001d1201241d408001c00940d040490f01e940104102e03d01410070400d87c06000e000c1c04900303841041034001299200c08801100070141c800804601c20740c80040390618810500d074005145844107211001d070340b25028904450759241245c200014540030011100c14521000700085020000c1d00404519038020300006a41c0400241c202503485031500e003684c0c0b040303404a0703100b640021807001c541d0300751040703103503c4030190020581c3c00010340d24203070b460030803402220921030003100069024038039810082d42010380744207aa01896032031210b444074260900040340700740ba41e40121090355100103203481c104c8201142c00c6a06929142529180725910602c103010030201401a2500361280c858012200d83c842c1c0c000100d908041c01c0480900c00e45490042c4541c0141820341107a03505005051 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 530338327 1250 530337077 530337089
    0x91a0c2401060c2a051923120a08030105011b0f150e07060503040b0106140409090f060903080a050115140d1b051309110f030403121104090f0b0109 65
    0x514050080c1071000302c81319040c40040031100800b0046090464044048003241c40c01c0d10b4040165210b601e00d450800d02d40d02440c282c00428210000b28042201080004944081c04007402c211035448210b0070944504002c2d0b500810020040140d568132003800c100c3d001c031008003840c03075108683d07842c4103c100140014259455025280158030000e500c810150300b40b0404490086540e0700014002c3c0e00100c60544991050000010749a8050740448040c0000541018a17060810100800415034100f0a480c003c4080a004000400038414545500c0c0240c0703880f0100d151120f80201030303400c1604202d480300700245c1e109161a030003142e014000c8105030861610b5007409a012001400c190048507600415582c0d10030407250050010620081d02100d03541e944c2e5200d0b080b41c2c041d50807491010704144420820208100900d902450704203200380b13000d540d45290b02c1e1505040e139401c010001c0d89040000b0b02001a1080392148480c007543c3c0707070001c1c800100d020300041c0990301c06100708 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 530339577 1250 530338327 530338337
    0x18030c0d0f03090b030702150a090323070602030705040305011505060a113a0801030201020d03020c010f0603030906020114010b0409091401020a03091106030f01090c091a0c240106 79
    0x180c0c08042c01503a444016140c01c0040d0750b101c2c03800d1b0900a56800c0e00070761000c9090042d20120b100c0004901403503400d15019151180c00b84c1500c0d0404a00717050170038110303459200920010380042c505000a5004d4806a601c0d180c03501d0031414550300319440040d480e0200c00307001030104407d4071130109070b40c80711819052080c90b940d450740300d150414000640d0019028400d00e41a400c860104c100c24500118101a8100c00900620309440d901400c0c0030180c00b5074060344030001250700c0794008115846038100081030a45228102c001641c1c1660800c0340410b007544001d018056091060840c06018600703504d016501d460182d80545c421130040d1030000e5221400c001c1403248210003c40e0941141008554480d0000740042c001d0410400464104505a01480d02480c114081d68011009408191751592900d00c10f003005103601a0001e09002041c080010b200e001d80031005001c2c4080035030680e41d00105c07000541402031840d0019150180710007031202d14480c811a403819589103080c0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 530340827 1250 530339577 530339603
    0x81b0609010315030b18160b07150e06091b131503020a03080d06272a080f0108010204060f0f022a040e0105191107021518030c0d 57
    0x4901800040304400f003907512002000007003006000300c8a00c0360303080300003c5004154a000d526100c56101c1c1c01603641a00c20306040c01007144103401441c1c414416007003803003402c10066954080c1c0300448a499810340100082180b20003044c044195851819070030040103d064100151000c400400383c00d180c56914103415076248500080303a8040c5400030444030385d00740e42e46850360250340154000710019051040000300c0315880c0c030804202d00314041400704420010003400c0010060402e000740303900040a0566900034510f403030102c04440c169901080c5d4500403910650b4801c0680c0035404581c410401042455800b80405100303480c90319120764078000c00b020480ca0842d50601840b0490341c41c0d071003140c220a450b10301210001090f5014840084110402c0382280e030211132181c6800c0b540c0000d11801100b0b035002c0d02103161050b20260910310a60003094900c3c54280c1c2000c50400c0011f40d1840020030b1182c6400a904101c00502c44030901d072000c0b881e41645840b000f00344a0703200314 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 530342077 1250 530340827 530340829
    0x1229071709030721110a020904020111010b060d0923070b0c0f011b0e030a031b150e010b1807020307061107021302030714090a03020904021801120c081b0609 69
    0x201d8201c1c5800c00c248015a40c1c1300301c0007103280b20030900700354080340b141c03195445216004507504441d1a00149864070725a52a001540e4070244080400d900e95610512011030790341d001d001e4402c00741070b550000791414980c07410308004000d1010701c01d810b10201c204030100341c00004080081e02d2181000c561101c0c1710302104c42c1b41004d0070300000c02a50034042c0186030401030001c0c90742c502e81d85956200d0301c62080c0341855280d10b0082c0c0058001461042e105c0300345000b80c82c0e810345042c45807d4006100d150110340400b11100c2c51414220343c0d4442e503082541d0315145499090120001d9107801440c2403561006e50360348502000240303401d4031000c3d104100030340c81d81601c14003074018007454812507074061484000e41c4111480c1000c50011415443c0c80100713941590b200044c064290f0a10f42d0458003001030140b0001c2007240c3c0801210800c1c40c2c07800300c00034214000c1c91203c46982c81d469040c5400031000046400c03503d002e90000c4c010a058a505407840f107503140307041c1e56440d51200440 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 530343327 1250 530342077 530342083
    0x20414120f0604030c061109030a030f050c0a0b0103020405060618010c03030b0d1412040b0d050a18060203010801061d041101110111040801150b07080f041229071709 73
    0x5841c003840303015a104110625421080c44001c040c0304070810170040c0110a4a20020700890b00d00d0b80c5c00d5484031800000007401070024050b52140750038001d0405000400c698548010544100c410788003050040045052070b000d2a50024030444d490782c06c0001030061041e220410000481c100440041c0700400d060190b070220311080005050060b44111a09090802c014030010b00c0140380300c1c0016206450000c40107490030b9540c0c2816a91070980103e01c0f0001511010b001c0c0149140c0c0d0f000041509048060a0311320b8a100c0d00000d07032650300d411001400c40e035080e071110210000d00540e840030780c0e4070251001e80c0142e1040010b82e001d000c3c480100c40d0800301ca441031303005601e00140c406404940b80c001c4c00071903403410f009200744103080107068000e00d214455802c440303409000440004078080c0240100074400c5034800d00b03056945a031000342d440d1001080d540030344256110340a02d49425040040d60700a00d0b88924607040203c40100408210150141c000c500c01d8042444800c080c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 530344577 1250 530343327 530343343
    0x50f070f02060d0c1206080a0b04150507110c01030203010b030a0f0b03010c0507170a050a0516021807030506240702010e04020301060314090109110103050a2310050402041412 77
    0x78048030b40711103051041074018400000c4004c00726403044200140380d54540902402c2e9030142c4054003241010740c0d1280304a03203003d0001c840b400301110400703103049030360302c24544240c0040d600e030f210014100b21118108150b100f1103e0401d40104018000b40c91040201c035001602014001600340e01c2420a00c01440075841d20b60b410f50034040d4511405034000050aa014026034040380403c00c64180802213106088041c40403c00030b20400c5100c6000c1c6024010071400b40600d002d01e002c060b0300040007003114582c0000301c42035210034040000e901d48140b590180e005e4030680010f0b81c5c0c0c0790402030081c00148070305041290001e428000c591203944103030402c207009031066440b9615050041c000d80070310058842a08412000607280700d805000e4042e42580140480a10064480c0110042c210007001001401e46480d100710403d225461180d900c08203079482e0005030300b071500c6204202d005030ba00651040c0e0040c00b007030080c00340b40e59032552490b108403040340f02810425201c500303089203 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 530345827 1250 530344577 530344579
    0x601140d090305130e01120b04050f0609030304060b0909120903010605040f020d05450321010911160215070602040e0705070302060f060111070803130602010b01050f070f02 76
    0x40601d01c104243d040310262072420010401c445405440d0b07000003044130f00034400c22151101e194801c002150036010340d0780d0058014020344042081079a001d5240800a9403061060362000080109215007481005000002120116914280f66000075500c4510040740412050001a08800ea43c0c095201400900010300240400c03426034940704029002012841980e508210026079035181c1400c1d941140e40302069189010508018240015800b00702c454040f4110ba84002c5c04001042024000c118a08000400e154030303c0764800440140c1a170041c580715050010300c2221424410a988542c100300150b640055483d00001300d042c01c5061091000680014040060112580041054a007220b1b003020140e00d40c0c20040380d00d03114007100500142c100401040d003211502d019140c10480524180704170090307149805042c02404e03400b407011a440050801010449030202d2001841c00b40000c0211781007204c00a081481904501980c640d0002440410007042c90340f144506a0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 530347077 1250 530345827 530345831
    0xe010608012a020106051c0c0b27060c12030903041706070e0117060607111f0e0406061704060609020f121f0902071e080306120606090601140d 63
    0x2028a4080945001d02c240000040321284038519455005000d208101d4001500c4442102c03000540d0311981d481080086482c40390010001681c80030140c05410a40d9547c0f016a514503031300c94031030104071403c581060241000b4020314880c5100861214030010040c0c003180da50340e680819207829031083d80c000c01c0d00852035000d4410034240c0050310314820344a60325020f60841200006403005000181071000d00f0851000107403590a0000c06021070910422102d0749200c061000aa083c04a0a0300107444010740302c100c0c4981c40d4005c103102814007040e42c003080240d080001c01843c00c807103041640f2003c8812408902009090391001000700103001c1d0441d190714050031210000d0b40b1107032a400c4078814030030101d84030908a030b10a6000c1403c21480d41c07110361600c01848065042001c0a4a064444a001941d040d11094110042c2c510410302d46a0382e1402c40b0800007010b00110301c643d80360f4018401c00c00c03607807a25281d4680002c0d00b424142c0e200c94400e001208180b09175000120014 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 530348327 1250 530347077 530347091
    0x501110a020f100b030715020c0909060709060e0a0317160c060e19050415080601180e0a11060d090639090302060906120112060f09150e01060801 64
    0x103a0104200d21800d903008141c032500310102e80c2800c01e40d040702e41354030f5264110020400c04c02041d001200341340341c184e0050701c03414071a08000a00c4501c00b201d1213a03c07600a0010031850943c401c83d40b40140c01c2030b01b801c140000000010455100b100d0000400c1c10500b4401c00104656400070f03954404200c0c610944803101920340440144c0c1e01e0321805010a803c102510040d03c0c3c1099502c5520344411114410310b0314000407c400382004410008281d9003c0f01d020230403800900000b40a0312010482c42910003402100500722031041a02ca86290807020034500080c107030060001d44a101155150346a0b00700c41006401081d06880040c50366103000000050529642d03890035441c0c000800403501d07084000070b60078040c019608190009031071800d06000500d03041028020301c0f03070080d01c00745c2002207240404032451000c0c3c1002e0a411108a0350030704000080c0500c005481002c0018010380c8e0007a179504841c000c42c0c03030a01d001c407910341441d501441d00c250700c113000a00c40f0100a025007 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 530349577 1250 530348327 530348347
    0x17070215160506060904032c060703020a021c0f0821041a0a0501060e130204120f06050a0917090123270d140102070206030403031a01030504031209050111 68
    0x81d20785203000c5916004840001d80d413454404c000c01d1080e9007589030001031688141341c0102030b103410020311501c443c00074107624440d1216800341500703500c05d400500c0e118001e4010010580130384d45540702c0503c0805a01c0700060390310720048203410303402405540c8801c000007014900c20380681407ca081d021020420040c4212219650b0055a40c0064620740b5101d11340c00c60241c0d5024056800490f4805840c03003168205542c1148031500152030060a0a464410703140c1609401c20060761038800d01042142031001620803541c119140b0307142000220030603600c1d80c5400d01c10b08490200440081803124099003c1d0b6000948444444580c4455481140c030010840d00100c3c103a442219446907580c030721342c0000c4000030890000602c00d01105116aa841146600c0603500c6c00f2155003e2019000588034240914001d61103514040750290441c46414510f00e088800c09040600744001d10001c00d800120f8916801541400400c00c00f100381051805414194062441d10100040c12200 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 530350827 1250 530349577 530349607
    0x50c03010611060708060f0f090907060906050910080a1e1b0e0a1e0f1401030b010305040b0411030c030a0b0609090601030c0b0703140304030306050907050717070215 73
    0x1612815203a00c54201da002c0c003400c0d50b41c03800f00d0f410008581001c020440a141512109900d0000204030200d04641c84000c54000d10042c0c8094810364040d020030301402d40c200c81c25001030112854041d08002d2400009000451401907a00501c100e0ba030120b5440541604007101001b94903800180000c400c2c2c905400614559002c85203200a01070803400c01e51240040e504a01350080900181500b13100007071801c0c8141018466a40041d000300140007a0304880340001004592628940c904c0c10000140945400405040c100340c078010801c400100c040502c0c0390450f4100d01d040880055074070101b481c040141c13070356a40c1485020303d210704000c1d401c824580724290580360381e0020380f16000110341d070358001c1c000101086c2e040881801410a428050404c481c041e1a0402c045010100c0201c100c1d031080e1005d8000036107074041401981440b101c1503401064919105180102d82c3d114122040d0444248040032940041d2413402d40d980c6a00019800c050100941d640c0c0741c000803107440f = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 530352077 1250 530350827 530350829
    0xa030804110f030a080c0f0f06191424041806060909080d0207030c02040e0a030f0503010f0b0c010605150c10050105101b150903031803020c120c04050c0301 69
    0x148120300d141d00d80341181005410340c01046000740051a1880d041d9684070015008200c00c1c0c440780c0700e141b82450f05035404009180003090810302900850500c0311142c0702da80c0d10340d9062400c0d03504002400c10b00041c580721140d4000c01502501042010880a2421300d084204d0041d85c09418600209005154008403100041c481d20307081217120b903240f00307000035161003a5019120b1142031042205d941c840d0380007084603620038500300002000550000301215044010031845606c0000d4520416400070a0843d460006003000e07404c66242c41a0740e4070441c000d010718054240007054000c0389210941100c80135040007002c108415403014807213a07107500500f8910f2242c0c424881783c2c0c0b031030588601c00e05060703400c00340260050801c2c0050543d86444032410159200c0320404144020a00c078480c0d583c848820310a0114001c1c1c001e00300281590380c0010000840d111540c00d13000000c2d00090b10760b10b4a8029214040764842d60f6640c2824081d6110704950410304240c1080781d0211402c0040d4 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 530353327 1250 530352077 530352083
    0xf02011205071d0f01080103170d0501060806130b15090102030403050f0a15021e0903100c080702010b010207120b100b03010303020c1302090f15070609060603030e191401110a030804 80
    0x304040c80580200010b060130403030000d010800b62001840403801860400000e012488002440e200d00e6290304070850784240c0c0314200056840050101529240c081c0d0b4081c0c8580820921118100c00b0001703000050044600555440c000b4001d10164028001c4e20011600a416610030340700124290361241d148401c00c54212407100308482c2a20554402d90360f00c0c514614444124030303154030602509038480448903503d803007903a150405000480c000d074000410103540f5a5014108100c1c0617007507440f020441d5041d50082401888980c507005c2841c001075811078013a032844e40f40c19486160400598000001e0031074000000310516400103051000800c041e111603044440101c40507040b4082c1c85610342d400041038001c002d0618002e401c0803911914092220314042c403c0d0f4030b0000b1500ca03440200c40040e16000b04005060700300940c916000d2096400035040540f45428103103d4030740f4001c1c868215840b031030400d003c1e442003112200421a01045800000c00c41c1006030119104441c00c03 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 530354577 1250 530353327 530353367
    0x90203062e180903090b210117211b0a0302061503100e0304090207060e010e071505070f0804121401020901091a070b040f0b0619030f0201120507 64
    0x22002603190142103004850001c0300a03141180620748401c00f418150400350100940369402080440341c89000300f100000c4115807000003203514141500f0024164041c800c2070a82d403810284058002c00ca0710701c01d02201d410804104258010f65085000300901c1000341211002c0b080d900c03c500240141c0c4a9001c0c4c2c0840b0020f43da401180030620070881704498268011781c4103942c0018003038000f0140d1344000801c0d2404e29071140d1909c8200c0e0810303d0240c0743c80b51130b000c00c810000c10a2144030443c0c1d40101c00741800c0d40c00d040000a400c0740c0d24643d001006000618941400b0001440d112443e40c400f1690395184d80d0703000300743da1210407003a042e11040389815041c6100381051086131011981070316842030040c03402d0501711002c006000c00c00b030340010030004500083c603004c2c10580301d90b125010380c02d50041d8074145188111030007040791340078107108200700408420102c480d00071640d01800c2e2840c90192840102d41d040e90021440d25058113240034040403603007250503100c85070800004 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 530355827 1250 530354577 530354641
    0x3150e13141902060c0a05030d0221090a021c0c06050a031823010f0507020312070203040506090603060d050604050f0c0f060a0f110a030f0e0618040b030109020306 72
    0x1d00703031182620141d07012200e820680c4200141800c00c0600000c40241c0c2c1a100301a01030349940b070550f4407031004020f501d680040c1c0050705480448008510000806140b00e441c544514002e981c0e405c00e14020384039800103207094000200c2000f5261443d603100f40d1288045680d880301600c1a000900300101080c206519482da050200110101e070300c4d00140c1461880d510001c2070070303150b0f18004034083c65540b11a46c400c0401007501030940111100d600455032850b42e0208004103980150101c01103402c1004100b05c143d40d41030686226075070071a0a00d0b520717110040080d0f0f0544880000405900584042006000300030408028454520082c1c0700c24410307c0082042019413000e01075401079040c808026030701d00c00d0b8412031085c4140d083c440501c03854082401d26090007210200e00052000c45058010b942c001303101c1c0c51444d0141c3ea0b907030814144203052059290b00c90b010390700599680e610840c0c15902504aa103a064015081e10300c030f0304000300d540803820810300c0c09420404601032 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 530357077 1250 530355827 530355863
    0x1e0603050a0c0207031403041e03140318040f0f0906320c03040303060803160c06030203070507022b060603050c060906070b060f060a080a050c0405060a03150e13 71
    0x1420304081d82c9940602a0242107581d1001c802c14044403d43c01d82c1700c244004151406507203003c506d204200e03160038074600d1a614110590900742d20115801c0c0c4c10a0091080c650064440c0b040e4070030048801049803001104082e000301007220b02c1c0620b450402c0c3c0a441840741c00e0b48455030b024443c041040c0302d84075115041c40b00b140c00504000702030300050009440398401d00003441d0070a210f8680450782c00c2e56180a40c1c5950041e401d00500344140c0d201c14010403484c0b1210f0701c000d20490500f5401c500d014103025080c0e0080c2034000e8090b0341c407080411802100a184909a001d0084582c901012581002c00c0284041d00084a540c498402031405915049069403100000204818500f00c003e60340da6240103005811b15030002c100d403213038070441c1d914230018000422856a0310380c6245403503c140c82c1230b038034081c10320112034000300014002c41d1560400c0f28104062410082650384685041108100c11070784040c0c0b4580480c801e20040780422010030b4216402402405c0b02492020 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 530358327 1250 530357077 530357081
    0x307030b0405090c010c15050c25030813170a030c021b0d0f060b060304030f0e0a050901090c051e0a200717010209030706030509070e19090c1e0603050a 67
    0x80d40c520095400401300f40d241d58883e080010b07240744244d260350300c54002000460103480098441c00300d20701c404941051820f20f401800c885152103da8a14441c040c0d686002d020203c0141c59024604004105c4406203c07031030641a00283c51b903000d2039078807c81c034140100140036151840d030050240d0301091082401d0303d88400c103450401040010a2030882e41c0310701040c12100012505151900c1000d20550780c1e010185210b1806600d68030000090044024454407511f00c20a10920071010b05101d5034603504081815505000170004800c82401c0043d1000e009908030a054004040785007a44014860701070010f0100513150320003401117618440d0180e80e0345039949070595001d10740412492002c1900c0007200003005000500c0c080d0702c1c00210342060403640203000402d4488051107144082086260001e00c900c0b031265116041c50041072840e41904180e80304002d894036a4142803024006418000b4007111925403071442c0d950722070102d09862841544042860040080e591000ca4 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 530359577 1250 530358327 530358331
    0x20c0a09060b0a0e13180b01060c031d01090308041701140118051b1209120f0403020909150f0a1b0e04050a0e03070c0315020a1b0f170307030b0405 65
    0x1070741d011800c0c083c455104841c440007410b50645d0041d82d00d4250b060000052017032021240608130f0038407100804e81010002c407c01a402442040300403042e90002c070368407400300d500d00304410b508100d281c440301c401240d03042480c0d04083e1a8101c0010001100700d4030780107000800d000c02707000344a80c4400070240e181c540801d12411190000c819141c00705900d4950006900c1508003440006100800d0080b11301500081c2044180c0500c00040c8505601e00f00401e08000c598462107a1914800c101048030f24021888003d02900341c0d400410104102440400d4004140014034000f5180495020f407210000f655204241481c014000c070380307605803c7e43c10201800d10b480303c0c04801402014040101402494204180d0341d84c1038103a9003c80500003030148a001c3d0f400b5016207811402d00c02c1050741d00c03101c00c4017030038410441034003080e4112003032070b001e020300401030941c401e05400d0071500c0700f002d00c0000f04100862900c140c2105400c40c080c5016a0035603804021040c0580300b88403c80e142 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 530360827 1250 530359577 530359589
    0xa020918060f190e040305040e070c02031204050a0302040b0f0301050906160c0210051804021809010e01030210110c03070e01030308090601030506180a0c09141b0306010804020619020c0a0906 84
    0x540303001409140001c0c4e14940d00140310f850b2407480c2580e40c40201500d07035000e4480d0030004103001e008d10190320307080140c6200c0000940c11545460b00c1d050009628046500c4024001c98541c0308002c5696107055201a030341001600900c400e00c0c00807503a5440f40d1040b940c547c03961440c0c5062500b641d00c0b40c01c1510391664050402d0310124509501a64039070000c00b03005007200c0034111000d00f180c40d10300142c5522a85c00840319110004c1c1800c00160300c0f416002000412540700041000d40e0324142c01e449086628189407103a425071080d698140709512603050f805105128001440c24030005682b81264007980c1d881f2085c6c0c0325003110f41d44401003888003400c0c0e07600010100c1c404000c1c10400d07150301e514080440c3c000c55410358584015840b26480b00303005079594000e40c00300c2280c1e8146036074442162880c8a11664280010401c20b02020300002c0c10003403201c000808544a100031070340d0200d8410030212000b9040c1c10001d65652552200324020159594002504031a03405040c0c15603807 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 530362077 1250 530360827 530360869
    0x405100e0906090a150305060a2d02070804030b0f0a0605010201020712211e06050303191d130911010203120c0f120a0c17010602150a020918060f 64
    0xc84004010364034a000e03000056007036880c1d0300b412200a0f8012804011840f91015014601c0c000009808407285040100a20642b501142c1c0d40404800d81e403027004600d0f0000180c5072820f90410f101d00340034030303080107103010324540c14400c5000148003150b10032880b00b141402015203a2004900303174007030303401d004103204084040002c80c10f009164608143d0441d44420081614021122095403810703083e1800100c00640c101c1c8041d100c0d80982009810b05400861510f0042ca24850490958103c031408014115403802e01551101568480e6050000d090364040010340c48584001d0403070100403540001400460320455001105031076510441083c41c81440c1e403421040d0055501114005a1a260800685c0101441901601e00440d080700e0002030480c41220301a00c0b844100d002100d041c0f94010040010a0317002641c0d084e0300d0020390002c0030640710072114501038080c0140140d070120320405c0710b10840200b800a01c0c81417004942c06550144200e052222804174001e44200c2c01d4 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 530363327 1250 530362077 530362081
    0xe0601031a12030910031415010917100207060b090a05060a0302061b061e01121e110303040b2205010507021c061a130c1d120607050405100e09 63
    0xb00e400e02c000b0540e20012810343c0c0c5040d111500080c50f03141c0c010041d0700840d60740c03503509040c811050344442d8080c82007040170510b07824010028004894500c102141d035505610018000c4406105121a4040d1581d095403192414a05230015001c415155030003160504005800c80521740520340c041d2074043c110070045419a002e21006500c42c40c1c041d00201c89503159480007990400030b462041c00a155501208011480950702c2448180c0c044a60018956001310210b811048003540110a2541c1c0c0380c203c110a141080200942640c0c0c3e80d458000864009081200000108211380070301d40c85400c6010342e401034090102c818010240090004e000d4240141410035110340c520170352003402038407480c056a50f0340c00d44502000c2001c8155000c0120001fa00306201c0a29203100100b40901034402404401454810310300d140ea590800e18204200303e503210130039141080001e070000d4800c0317482c011130064080d60061180a004101c480c4080d03040d03e211719516085c808004108101503 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 530364577 1250 530363327 530363329
    0x106121419020c120711010207090b0f09040f060903051308030f07030c020112020a030204050f0102060f04171209030c07240503061f080906060d0f0b09030909010f0e0601031a 77
    0x290401010f10036240f19600020206520b03110290020f075214a070a010383c188420002810000b041d40040c0195041c43d51800b0241d841241914401c1c1c0b06441400080d0303514280300004171142103000c2c0c04c1914143c5280c09160740840107040034500c0101c40025240e80f003500d96070300c0c0b045180c2000c21040038042c0c0f4000a1207000c489980e2401454040000d039401020082282c0c8801101408607500042c100100c1c1012286404100307800d0000d0f0580f89400301444408900050005240720b08000e10000c07a4081301040d9a10580c0401d942e664620b403192036580e8035400205d4041c5030f841409000a92154400307550402e9940f007504501054180250984e00383e000039003011752001c404c03215251400d9440726004c0510300503960301030701c0b030500da520035040a0f8044c000724007940043c800000030035880204907560940c084007410f0107940c0c004925080d0301445184a5105100c64000501c1d0f80062070354a0540f50607002000c1c441d1035200c01541115000c602d590300404a0a00b25003813 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 530365827 1250 530364577 530364581
    0xc180b072a03051209040c080405150718060c020a300c090f02070201080f0c0f16050d09080114070c11010c0b130507050a05090c07030201090b0106121419 68
    0x2044055180340124035032207540d00c50424880b00c01d6440e03800000b084803200ca103441e0041f80e611400c80d0034080d101d420316440d220b13120315a0ba04450315451003d0b01080007030f44070380c695042555505004402d40d80d12074600400c07100c0303103603400da120380f0408030007040c0307005034102003c43d02e50751070924042940310181c2c800c48060014000c0c0c036018083c00000403c58214006c0042a004101d801695100d0780c0c80050421030019116084114a483c10003449400c000100c3d16828a84503150351510f40440b01002102e25620000789140191010f240e250346d0400c407140d0a80700c00f44000e01c1100c0c03d46402801b00c0008886000c0007a4103201d040020032032a515802518134180340a0032000415160801c031a0030a0714600c078003600311f6000c0d5041c0401400360f400505001c0700d40001b903c0c9003200040c98000c010f0f000d1651404005200c0b801c06000754491400290705c0302500241c0c7d0303522040505940c88452040c0000742c1070125050ba0300e071058146d03912030900fa01054205030284844800 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 530367077 1250 530365827 530365883
    0x203070215090309040c12050901090506010501050702040b10030501061b030e120a1a180f030307080910090b060901061817010e0604050304090e030a0509060d0f0c180b07 75
    0x1c0e9601041000d00d4080c5c543e4011201640115182c1c400340c0030203056604219000100001030707592414500c10009400803036018111142464140d840b40000d00004008000b2068010307030103064940d120300c0650f095000f00341210415142c591201141c030752440c041a04030b0310010001030400c080e5564034988900f2810a00e044030084850043c43c0d41d54820404240595000c44090a5410002e12981d41001c480101011801a01d040104080c400b0f640b400040c00c0f40d801d00494000007100700c58100600c84540c0040141800715603c00d0034584202c150668009004142410000c51203030300461600c19414650206616058038103031100070341c84d040c183c00720480e5480b2411080328003800c100450040f4060405103644501d401c620178100e51840362602c03441d070401e0120314041d54000d01560031070311069031402d070344a425814000003008141054148a4907044941124a82c44984940c3e16414040c5801c180da4036195011803a0044640040c140815030940340640070a00441030 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 530368327 1250 530367077 530367091
    0x3130816020409051b0604061e05070b011206140906160302041505040e09010509030403110f041d060f01180e0109020d0f030306050a0308070816020a0b04080c03010203070215 77
    0x1000c61102940003409684085000355420360129441d40f010103c1c104407050807240c211200303464180b80001c0038040240f4400b58040319075404003500c007414090310440b00741d2540040916102e603110801891251600c2c08103444031881e0007422024600c824941c28012115040109241e0f0b40341491307102078030200001c1400301a024400040c0810b04903621300d459047c10b80351640c0b0345d424244070320f100c0400180354541c168100f00a0140100022040b107054940140903203840c3d90030740001c111050218401d0301d41091504803c60a072605e2051107c02d48410310083e517507a91214503200f500702c0403e0040501c06081d0fa0940c0b481c4503015804074203044d003070f40008515161990001214040050030503284003078149004010554984600400360008031201c000c221300f10346505581d070190807070041201c44001140300e402060031038000f02460b40100341100007030322044400b0054202d07118040c064880d011026003140303018020b50f0700c0340707240350700400186100244100101c18090400 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 530369577 1250 530368327 530368357
    0x408090a15021f0c21021207030506030f010b0306072106030318091a010804060f06090209100207030809041d12031b03190f0204080f07060f05031308 66
    0x10780e001040e40c04100032000d07900680143c081d009980c12142500d001d040c83c916150803404d00070aa0424070464541e200020661030010300e000e90078009100300a001d080d621140010001410340c03540205114000a9059803c2c000101e02402d0a80b0034a400c2e155154001c0000034a46611883c015607040c1400914520840f1102d0040d0044030070030341040e400038640030750b50440340462003008070041a6800d010072035050030744586149411004142d504105041780418280403142d08100c1c0c00c1441690100b0075266203070fa90700001c1d8440a41ca60084018000304101a40045840b100f00c07a084010103180034a1030302084018111524044880d514112155281c0c0008000d08903180c1440b0b5262541ca0078078051540b1200318111004650103410820030900c082024205030f0f0015410402007403e24030081080c0c0603014942000c6078900c203580c0b006a80f82e00024503001114176603142c85040d01071019080380e03644000c940030804050341c6c420010009010900600b802e14002e1f1078 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 530370827 1250 530369577 530369579
    0xf08090a02150a090e070509150c01140405160f0909022403090705062b0e030c030403120f020703080d060506070506151210200f0a03060b07020105030408090a 70
    0x850030448070300c501c402c800c00490304043d07158024124002400d96000107203990318181200170031512820300c005002c1d03240a80d0320702d01f40042c1d000346d03801407060800034000010090800103007490100d4080d1513034414860700100c01e4903051030103015121034202107140075090112003030150000c070070100c2e0800c070b8001d03080c0007050f400e202c0c0c0007081050410580e502d0400ca141070f407801c0042e40000e407140200700300c0910700140201804a6000000c034080380601c2c4821050001400c60041d0380003280000200b00d40f4540020000b0010b03a4071400b00c80100009444044a504204100b92800b40e41320401c00d0000c14000009052244052003022070090b456502040c2960882c40049841e544408180b0045090710040c1c03143d0703494180d54134248144c80340c442a9075811405201e0305c44036500d800401d04210b964090100418018072030560301d400e0303024002140d6202030b80c1100064038001003c80d103138901da41103644064050352068195280d42e1180710480c0d101c2c121103680314010800c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 530372077 1250 530370827 530370829
    0x1e0804021503190605010201020f0d1a09090123100b03041b17010f0b15071a070903021f0f05030c090a030303050916180c02240114030d0f08090a02 65
    0x40110720580900c102c03c0b80021180c0c203c9000e45815400042c1564018015910701d01c7d1541c0a440c140d48248101280042030304010035252300440785580e400500d61400c000800a054000c51031446850304400c8038014604039450140c1801d882400300f625010310108840e088503000386800a014810754000340646c15150b44480070694400031560004200c01c10034001c00303100746c449040b0031080a10884a0410010b4000e650112040c180c90b03002003040018402503940401d454111a41100078a050022000c4c10081d002c1c40102c5c80350105c034850504503141d04204c001c4199654a800341c02050681007601c7c1c1d904001c000010100c02804801002d80e91b00c020b8500940c020340b0005020308000054900300300c41c2000f2401440c1d015802005507c804802481c240040040c00280d029000c00f0101d003001c0c80c41c180c502000800448140e0100b0002075128100c0b40f082c94040340c2d0f142e004d01415120004408400302044105204d034941c54000e0040641c0002040207a482503103a40e4 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 530373327 1250 530372077 530372119
    0x40902060c07080705090c0a08070f0c08070b091614040203180a060903030b0604051513030f05060a2016021c061a040605060313060f0f020a0f1e080402 67
    0x50311401c3e680d8041d400c04c1080d8180030f20543c0e001011041e02c2440d00010810284c031a01c0040e28800410250740403681080e072007040b040b080c050f4000c600740d03582c000d1b03414812802e00c07044d41c81c03840a0045031203c4060240000c140380483e03042c0882442c0b200704010403c002500f0081040240012100c09110310380828402d0100c13140c42100001481c1d035003801c0083c11501204d842c0ca004400070031007406165500211100c0c41401c80541555030688026140003c1c7c1413684010704031440c85181204000000c200c00d03101c0c072030a5104022002e420078000c3c14038900c0c485541e80c0c28504200440050030000c07001c0340c0e030a0000c2c1014151081c129100101150105820f0701c220b03956803c441d100d5080c400340c4901e00c2400701c4051101c0c82c203040008105220240030321403d407080c40818030070401a0340000c3d80740b82051000b040184a115400c2010b0b40c4503503040000074111007410140c07140214800303852046031070074500100c0d000c0305090718007100107042642d01141c02c0c1c189100c801009 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 530374577 1250 530373327 530373329
    0x3050a020906070605040302070906060c0206070618080a0e0a0b0301170a0512041e1a0c01060b040905150a081f090b1003031106010e0c161227080c040902060c07 71
    0x141307800681441c0a0900034100750301c9401108000382000700400030b40d540000c0d00e01d02542c040f243c0a03a108124600703000204074241c2c02050301c03844003d0500034084408003826041c100d0382c48106145c9941300811031401c40900541300345500030300051110004600240010240c18012a00d18206644a003450000c4602100c0320042c800103052000100d40303d0054401011050004d0102c0d052400010b4607500e00840d00203d41e1010681c140d000009400c00c00042070750780d4010f0368940d1101815005002c0807a84020346d22045800202e65080040343c16045aa00310060450304c2c0710040c400b621103c890f08140080d50711980d000c0003040c4203000d07031070049540d40e5a1102485c036600c0c2c040c1c04901142d50090860f005a0010007140021004c1940e0101d1513005640c0e48201c444170400d250200481d003c4c00d080d92084407001131743e80007401c800f40c0e10b90b00e00440886040d00c01c00c1c0408240300740200c2205030404418601e4906003038110f4101a88000d000500301044840894581001 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 530375827 1250 530374577 530374583
    0x12030c0303151e050405040b0f0709151205090c0f0f030a150207060518072105030c0601050310090c03080306150310030204110a021f110a02010f0606050705070603050a02090607 78
    0x404403d41200340303140c2011400901d410340d0144558079054403104d916410040201070050700d4000020040391040f01e02c80e002d0540041001204408200024600451855204442450000402c003c03100014060742501c5000300482c1c2040c0d010b4042c4002c42d401480d480f034051040c0c01410000a60000030142c01c001d0000f00144c40d40e442d801c000040e241c01511110322a180010480074126010603414180c8964050703144070149400f18044030300c0782190010300a40400300700c05022071004114a41207460480441d621010b0351103c0e802201c54590b0020000c0c0c40f0310400300005000880074552200300140703d41e0100ca004000c2100941c81241e0604180e41c03146400c0c000c510b841e2041c0b469200b12810000e0624900060280d0b841c3e2000d5003008000040800c040940100e5401c0089110265402e0a80714a07002c48064060301700100e06803c801d0401101041d0103200c3c10a80c2e81c0ca5030404007c2a44514211041d40100006030072580d000f07400b00503045851711740030020101244 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 530377077 1250 530375827 530375849
    0xc030a0507022403040807030e0d0605060a0602030a0225080106030312061d2703130302131406120a050318010e04050402130b011b0b1b030112030c030315 68
    0x20602c104224110490031001e0340e01003c09003c84850b03100425654403a138030911203030b80c408050900780c2e5400020412594040316a21400040207a9504640d000702d03001da815140b0140c0700c00040e0b03140d000d00324081c401a40301660742c254617050361050644648440d1140802c0c951222003003425200d480c0c2059001ca0206088039400b00028410f000003051075902c1029078030300101002800c01405130519100c00b00340070139090980d1001c010044d103a400c0c441120743d01c40d0002030744800c801c81c0f8070060b4032645140d16002c8102e141801054204c8034a0858400a43d9844040010319040310741044014401c22046a000070400c20003040c1d03501d80392103036403e04640c42000505100440040d0b03805075003401c06000045c0c854414003149405c402002041d0500740100490780c1102c8808034140480a03140360354103110040b82814010400140c1c00014015a000701381c03c5440300b84a00d00c5003409240306007011a10a44818840d240300c1d180228024411400e5041c42c0801d94000d10b048032 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 530378327 1250 530377077 530377087
    0x90b1201030c0e010303020a030c0312140a1802060306090912040810060501020f0c040522110f030a0f0f0c170606030c03011104090e070b03010803070b070806061e0c030a05 76
    0x100907030b24000307015443e0400120742c1195002915104195001014001455134440806006007405210365040315020009210612410100c0ca502541c085928501d031051a001304005021030401d0303144c020740b9203031640e10794805200407088014901c002c9401280c110124584404000340010046240103107126084201032004a6010b580924159808039100e0940700764041070005a103101201c4c005403e41d07541c2090140d0380e101e2200c01c444000a4080d00c4108a901011000d00302400e54803420b82719011760a0540c2c0703200c01d04000c0e001100241c2444009a081e16000c0451803049000d120a6a0340d05811407042080302180740d0316070803c500f000482e0604101020b42c002c2c0440c001c1c0013200b48c42154803068030850203101590354039600d00030b5a41c00100602c3c001008144103007641d80d07070340302d000a850b904000b000f03c4074100c1071804240000c1c400c01c2440e01840f00240013174502030203072015401c8100700c48140520004280f011001c410400d1010f04010081d40d01e43d030b6910 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 530379577 1250 530378327 530378333
    0x60207050f01050a140f0a0b040219050c070b27010c0f1a0a05160e060910120b04060b180109051207093b0a1727100f090b120103 57
    0x146444140071005000401c00f0014174007980c650301c85c3c108620540001e111000704021501902c030b00c003003c03486100d41c800000341c41da90000037428880c00d00c4044d900307180d403a030b030782c01269104e91988454400c110b0254203500480150305500b003144141001020208c00d07503a0184240d918601c281c2c2c1c103d5071400c5030b000c0d100c0000941a4405915030742080301e480c0085100c0c00700c2249000c82070420200f5120741c503158440c2c40071200a043d00903d0502000c0003460014885024000d81d50074542c280300711a040790030240030f50401c0e0b4164501c40307030801c0c821805642c114494501c0d15410084180e100007219102c02026001402e0030b480030301030300e6040002c0d503c140c4d000d05041c2042c054401c60390b8640410342c9040105105580810000d100e0814036009180c506419030242a010100500f99060301e0b0395001003064648040025503602c00000480c041d19900c581a41d410503100340000c03a840d8800c5040e00e19810507414020450798481c240c0303c24540084a1106605c200b0034014018 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 530380827 1250 530379577 530379581
    0x30204180212090a0c090b03160e1906030f08030403030f05090705010f020f0d05090d12020c0a06021605040b0414010905040c051002070504020322050d0e030304031e060207050f01050a 81
    0x4003c10043c000c0001614590710b580401025104180366143d80e54040000c983c3c080c0141041281e164003002c50441c0c4400f44e0402c81041907030900c1c01c43d040201a42011129405158212504010411040381040e125503404e0f0340028002c82c1090f07603411726043c1840701c0303200d0580501001001055040d041c20000b400c0403005211840555000360b0500c15070100024008002d000b2034600030343c030b403010a0041600e81044003c014910545200030004e680d50019008644900440701d44140561b80d0340d00f80e842e4141d08030840b080519802d13052081c0d0038540c02806011702d0141c000600c2440d482d0981c031045d030081e008802c981d03840798144028440640c01c0c0d00080c01c0215042001c07500444000f070340c1c8242c944620f82c0220b801100041b030300c5018804000402e0304900c00f030744481400c0e1900d00c0d02d400c10281030720081215a00e079850103040c000103407020785ea8040300101d0300200300411a140525502822104a80c00f0000d8070001078040c00740c1e1741045500030020038107040071060f15003 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 530382077 1250 530380827 530380831
    0xc030f1b121202071e230138010f05090a030b0a0614280302041b08180304090b0a09090305041401031103040803100b0316020f0c060a0f030204180212 66
    0x160302401400010046131401810017240c078885800851000414548100e08204115103100c22240401030041e030000190056460610344469107140b89030142032480480300b030500820402e000004400d402d95025110312881e00680b401c042c1c0c100000030380002e1040080340c0007264540701c2002803200b10902e41c0070340c001814038044540c000c0ca2000010503c6401450550110005400640311a150560305a14040c41e0007610601c04001c0d1850220040c8144150410002e08108006070340c6000003803414585100841c007540c030b0030f4584030b0858060558000d885a006100f80c9002800d002103104d1540b10320321a03111541c8032071801c040c1010006461a01701d05150411071910207101d089801c407540154403410003070300e0307881d002000c1403494140d800600f4100800010303c40c01c4080d01d10511441c00c1c0940c00c4854001066080b15201c601100703800f90003030414051010901d004182c04c050841262400501b01a90f44030b50050414503039144a81c4560f0000d41030403c2507485845075 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 530383327 1250 530382077 530382107
    0x7120e1219112103040c0306050408070210080412180f08011d01060503030a11100c0203131e050105071a0c09040b01030c140a031e0506090708070c030f1b12 69
    0x10034441c03c244034850b14248450b40026500c40300000003003c2164040d01c1d0400307180c211004200c1d0385001e2415842c10390201d041a031040b1400341095030418403031191548a1079000c6d00004100400d0641a144d08610000480e05800c90940201d481d440d0b41010100601660001142c032100c0c8a45003040402d40803104441641010400d000a880010031925400400e152503070200c0c404030305150078030b1040c510500c81d007400d101401d054658000003a00c4000100e80030313208101e40e5a0f84080c0030078007901091070307800001d44081019601910203000303014040c807207102d130500301d51030400720038181198030b441204408250403a80c1c1c04e1034801c54100c0c1000782020007082040300000f0780384003600001e440d0130450010760754180030300c00d0304a20880d061003c05138882e101403880d0b4001070202180c41d28003d00402d00054007007445052072a010340d42c59200c1d0381140c18192011030b407400300c41844400303005005000000040100440c200203e0107030741108241c0040c0c1c0c80c014242c80b00140c0348 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 530384577 1250 530383327 530383333
    0x1a0a0503030711060a050706020c150108070602100f02070b01270c050724020409060510020a08032415070c0503030306060f2a030403061407120e121911 67
    0x1500002c80e400028010800100c4c1c40725100c81c82914200d41c1e920a0000c001d18150002c2503266003500000f410301e0001a41004002c5a40e807600c8556980c2c01040c0b085030011380c412a40225000327440c2c1d101c200764601512025140000304e465640c0181c500703901010f06501100c91000044003441c1e11407030040ea0540703041c0010b5411190041540c000c0c2c00025000e8500408406403c0d00c0040a01110401101c415500d80f940c40916900030700042c4255030189100000308001c051010841030307065503110f2803050840c0c86420b400040840d0002e40030007200e42035004101c0940c0c0300d03031087e40304c0c50540300e40641d54809031400b403d550b851580140e011f603000348140030190b668081661700c008071204407a611603c1c02e1404c610706040e07141140f480b0f0300013580c0300803451401100420a490054606022014080380d16010000c3e00f00c0d50b0800090250354880c01100c140e81155000d59180b00843e81c102d14030703221005142d4000000c42c8042c0695445201301180c208080380e00c407104882c05 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 530385827 1250 530384577 530384587
    0x3090608060f010c0318090c030605030106090501050102070b071b03230c09130809040c030b03061b18040b1909060602060c0414010c060f060905132409061a0a050303 73
    0x68040c07038500704024113000c2001b148942ca0740c80401140000d1460f4402407045008852024005124901480303001c0d50811001046860041c00748038100d60701a8002c2c144e091808500012a0f000507400311200142480b0110124140d002c04001540c05004030401c4221161808005d050040701c08445581003d1102800d0769103802500e0782c80406883d103003003034400c0c619081a241c86440074941d44035142110171102d06a041c0c2c05250b000000760200d41d02d640b00d9510340d042c07440c511044014007042c108010030b11180c800c8040b00e0941005800030075405414070000e898840c001080b2440e503101c1c1d43c001c115030000b90168400400c42400902200d0800c0e410010300c40c4558011591050503140f0807107030591041121030081034001c1410071034501a0380b4440c0240040f44100c032069400e00d00465070781e101083c6840c0c0002c1d8081034441640b010400707a220400410042000000c0d03440c54050041b41460040c0c1180c9001c03001c1e041040c5901c03508100041007507030090b500a5100740300e = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 530387077 1250 530385827 530385829
    0xd0c030641070201020909160f020f0a110a0506210105101407030c0203070e0405070f0b070605041104020f040305010612080a08040507090204170709021c020f09030a03090608060f 79
    0x80c0a8841500e1207030701416a46600c000e80c06441000311135a0003071012070030001071851400d8500042016541c6140c054041d80804aa82d1803812508400d660400f443c80300c00142e01c0c08002804880207004c5c0070706181c0e00d1000490a40107403800031131280c1100251018540400e5120340580400c8a41800340503125900a01c010310040a0850440000803035800740f5005150b802604d5070300800301c440d02c0b9100c0d014407041f18016282110540724035600410049036034015103041c0c03548401554142040c80c0c9444002c0d00b40508181c45601e00c2030351184080c4c40380c0c001007240c0102d20080720ba8031440c500c0c19608403070803544040c0c65009005072600000c1c822400b29228210b41d440c04100607100c600b041802d0030100d0707101c200c496100013000504c4050610700f283c02004c41209540c0955a1411841e0a0340310f40300404034642e805600600303407007403550701800300914060350aa0911540b000880e01d064502002500400d40031501000081e07070200c000d0364000400d0b5140304803220580 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 530388327 1250 530387077 530387171
    0xa0203100515040513060c0f030f11031617010617011a03190209030d0804060b010e0619050c030406031e2a031823120301050904020d0c0306 62
    0x42c0d48034443c58589010422407101e48006003075294000c00c08202148031002c000c2c2200c4e01d80d405c6840464102854080c000245124085003019040360b424950703665a20241600b4004042c20b41c144005250915404c2c528912007502804458485040044070100903007844003050703222030101d80d189080039200c21100419240c011802c014000400070036000f200029000d03280700304c2d402d403050208810382140d001c20010700840c0a00b200301310000c280350044030700747d110740c02054001d0030030000141c102d00480455031180e8a945070407030405540e030010b2070456115500c0b8000180d186c0c80409050b9100c52140304030020103c000f0071050340d00c1100002c2440c3c0001c100032384114070b40c060924040c069040045941c480150b6a051420b0f40e28002ca000034100014405040150311882500c00700000c074101c08041204416003981c0c40c0204126000c48010800c03604011401d0f4034100099020030498080e611403680462000301c070003502030107039601c6092065050300e80c41c1c1c0900100800 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 530389577 1250 530388327 530388361
    0x11040303050c070816090e06060d0221192a0302012609060f130201020703140312010b0c0c040605060a030911150304020405060d200109170a02031005 66
    0x5040c10350700c0b080c1c10440c107400c0c40a40c1e8040c07583c5025440c001604081030907982416100d900070f042108602524080d41d076541c0403203025800c24240d440b58070240c9030100c0c5004170301e03103003c0c405036140d00c51264581c103003540562142400090410b85d035040107440c440360461409445500000c218500c064903062044601c03000c1d060082c0341c44c415400e0800150102255034024030402214103183d10038075174400040f00d1040b2007006450102c0d01c00300310300d0903850400360140c0c01065014115192881c90643d500008091480100801e00c001c50b0103c080341d008000d001c6055460700d00700e060345414501d0b00f99070544501c0c03600720140240ea661409843e0350302c120b032400080e2506e045c58001042012958003543c014a000c01540305800540021172146109443c00d10464850341c003401290a511000201030130708081c44401040041c503640403d070001454000341003542e6180c140c140e460700c903804680503000120f4043c25818104812424042006c20401c00d0340b0303244960780c070b200042c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 530390827 1250 530389577 530389583
    0xc09060105070b04030927240b13090507020f2b0302030a1d0102091507050a03120f151502070308030a0b0a1802090909160b03090f060c0418110403 65
    0x3c01c50114050611840d9081c0140801090101855030b030030b11544152811030b001c144060b0700740b801d9400d1011008440c00c01c0c80214801454680d400d003c0d00c4c4025070002c0c0d9031200904160080080c480c20320b401801d01500c802c0d0050302552a990a0300c90900c03946c4180320f00007501a46421041400c0c1e0307102c48881c0c070720501d40141c4a884840818000d4041d0758000c000d142e04071071403144050700641c01000302500440d210944040e0039500301d0b055000d05100944281c200d6100040400d001ea0f810750f00b0000b40d40c0d000500d200e0000854030460301a40d8040c0e40c81240d0380001e000c1584510718840c4040c0c1d0900041180078556510a0707000e02c4000c02110b0010345502c501415515807100340c002502401806407003810104e0305e074a00035084800074230710038056140882e18003000441d2049007840113803585082c0700e081902143d01ea41c0050452505817185860880102800b80100c07409015051131440e541e600c0d04907002450112020700300c01e45840c08888441402440c403c40d011254 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 530392077 1250 530390827 530390843
    0xc130b10020601150c0515010b0a0f020c030a1403120c0403060b0102031204030e0607080c25030f0f0c030206030f06040b1801050904050319090f06080103030e090604110a020c030c0906010507 84
    0xa245401410004015200d2002c1c0f07001c140046498271503480035100340c5909030343e000715403520740404a81d00c00326079200303076007603040f420391600442d800400720310f960721000007102e02e440c02d0004c4020032050200c03600240d401012800b0300401c013581c003846250000c24070007941070070b011404c6100745c00d10240005007440344091007050151030725410707035040e2504004003c0d1a002188078042c1c5070001c5814a01680383c14100c1c90406071400302440090300d4100c008800d49023042d0b075503001c040810302030965040106038000401039581900462242d101402c40100b2414108244419501034114480c0b0a5a00d8043c0320084a240c820060440381c0446203046941c0f598101103003103204200c107030308500c82c1984c246c14070943c202c1c64120440320280e80ca021000d50703c510450b6160020b000080002d40d41c003024000b1131900603442ca80018000307100003541d00c0d010111703901c02e510000a15000d82c1045480a20600d070510019245920696440c4032a00c1c00c44d000821520070074078000c0c1500 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 530393327 1250 530392077 530392097
    0x12080d0903030b030313030c1707141903050d021b03031204140102070f12050f0d0e010e060702010f050c030609060112090501110705061f0b0702030c130b1002060115 73
    0x35100340c001051034039002d8280c3e60fa801943c021b250383c2140d140400d581d00e9071107280000305694020310f40d010711a0000040d10405003001c5540c4910300020140c0b0780c2c0107050001c3c005810000d00100c500452040f4018403038010820f00107414a8142070940403180001313000f070307503c0351004030880e0042c607140c1c00038010a03510382ca011030103440e069261082a61010443c10f04010252003811060760003044800400c030482001140c041c03143d004007500c070741c00512100d1070042254002401c0b40c5108e20010810100610f4514540042218101d0042c2e45507050384081104502c9015040800da5410928518145e4082600007001518560400c2500303101551a442d0513441100d525500c90028000ca078819a01100107405c80c900c20b840038004c007004038206c5641642c0610241c0b0348015084041f0b4980844061190003a81d01130ba0980039108947c10142d8501c08a5031929415100c0047c410b02910700303014001703499080b00380a65205c500148110f03042183c401c0e5010000c1c7c5002c80802c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 530394577 1250 530393327 530393333
    0x4020f0609030115030803071d0d120e0d080d0609060b040e1f030b1501081510030207170406030e03070302060a0f060e270c0a031202150901140112080d09 68
    0x10300c0701c1607501000c1c04d044107011082001d080000e5004071020b9885030701c0131141d00c0500b4581c1e01481102070340040c80080030000210002a409040f040b0380c2000000c254042c0042203001c200071108484004000074120040e5249104081c05450005401c01425040884400e06441a80140f0b2100c1c0901000030b4004044880401902d00e625880340e540d403a0340385040c101c80074040d11002120110303c52440000d51082d0718240c401c01404c2d0152403003484000c00d200d61074069a148908141e001c016800200c0c0c0c1d0210140300044880201c507030355038504840101100d00d007841018064108010f4071001c2a070000b89a500048802c0300000d0110814030414000c008950211151010341c10420004c500c00d10201426010724052a0124440701c0315203076120308920325062b500513000d80061000c51022900c241040b10b10380100c4040b02d20a0268080b0b59a040380c901e20960b4481c550031444440c0c040c8014010680041c455812100035030700e182c160b018050350a410942d0360b402480c14 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 530395683 1106 530394577 530394581
    0x8060111061803090301230f0c0a0806040917030406061a0a4d010b0a03060f150f03050118111c08030c0d0e0604020f06090301 56
    0x480d60ba6a649a01001d1104460386410302c018420508291002d100322501c406260f080c0c3e140152080c5074a901c080f40c02024100d02816480601202080d982c090302d0b125851400c0c0b40016684160110f0000e044540d40508086100c1c00d00640c0c45804500031030080b4092001800500e0715060544241920340000700043c0d0320401004070340d184039884200e807004040e801400e00082d40d440010301880c1040c40c001505002111480b4500348515501050000f19030080c0072100302c180002d40204101e02c13001e0030254a5407021040f100c001d60200f00e07460103000d42c01c04416104d009051710060315000072183d81d0f19004e111a0554001c0e014200352aa0090480050398840e4084c0058020080d03e03400c105600c4050303140c00203100700c0c065403168404401054a81c641d2003009020354240e282c6030400741e00407206020251b22440f848090b1158150784096803904410040781c0 = true := by decide +kernel

theorem cover : BRFrame.Cov 530215827 530395683 := by
  have h0 := BRFrame.cov_init 530215827
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530215827 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530215827 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530215827 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530215827 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530215827 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530215827 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530215827 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530215827 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530215827 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530215827 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530215827 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530215827 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530215827 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530215827 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530215827 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530215827 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530215827 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530215827 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530215827 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530215827 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530215827 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530215827 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530215827 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530215827 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530215827 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530215827 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530215827 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530215827 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530215827 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530215827 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530215827 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530215827 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530215827 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530215827 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530215827 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530215827 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530215827 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530215827 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530215827 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530215827 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530215827 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530215827 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530215827 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530215827 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530215827 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530215827 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530215827 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530215827 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530215827 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530215827 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530215827 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530215827 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530215827 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530215827 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530215827 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530215827 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530215827 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530215827 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530215827 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530215827 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530215827 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530215827 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530215827 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530215827 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530215827 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530215827 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530215827 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530215827 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530215827 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530215827 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530215827 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530215827 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530215827 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530215827 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530215827 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530215827 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530215827 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530215827 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530215827 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530215827 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530215827 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530215827 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530215827 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530215827 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530215827 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530215827 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530215827 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530215827 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530215827 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530215827 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530215827 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530215827 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530215827 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530215827 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530215827 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530215827 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530215827 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530215827 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530215827 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530215827 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530215827 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530215827 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530215827 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530215827 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530215827 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530215827 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530215827 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530215827 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530215827 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530215827 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530215827 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530215827 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530215827 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530215827 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530215827 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530215827 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530215827 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530215827 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530215827 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530215827 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530215827 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530215827 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530215827 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530215827 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530215827 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530215827 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530215827 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530215827 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530215827 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530215827 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530215827 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530215827 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530215827 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530215827 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530215827 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530215827 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530215827 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530215827 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530215827 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530215827 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530215827 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530215827 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530215827 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 530215827 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 530215827 ≤ n) (h2 : n < 530395683) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
