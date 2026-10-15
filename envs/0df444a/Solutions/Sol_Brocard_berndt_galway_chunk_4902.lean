-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4902
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:06:17.358975+00:00
-- url     : https://prove2.me/submissions/3c4a720d-e41f-4087-a8f6-284039ca3a67

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 881474820 ≤ n < 881654676 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 881476070 1250 881474820 881474843
    0x1120e010902090f07020a06090602162a05060708090307050316080f0d05220b07060509010e07140d081303060204050310110a030c27170f03030a0b1903 67
    0x414043d01c44402000344044664400c100031406401240b01d00c1c0343d650040f40051140c0c5145401d070024000c0c9041c2041c00c0000404c80000c002c212284c0840d01c0c49000320705600c01501003146c01c100441ca00410390408028400c00f00060007809c040c240a480040945080710784680100e03142c0400d20420405011181000f045594400e00482c00c070103010102a0100790b448210181c154464403d45000c0c0008604000000030014241d02000d805c003810619660303145410144054681519a40d501c1c2d4a0940d01104259000490303104540011078007d260702140c00030086046c3c1c8062040c0c81c000000c2201d00f200c0e00f90b00c004e030400b8503c964001611103081100380b5142040007a0490705a9207058401c0e50024800020b6480e0030b0351502d07011812410b10041260340035403c0160310001006100c0400160038404440c40940340c2c0b031008002144503074100d169450b0503403a0542125002080403078444900c03034128020140002d00700c120202502076030b071480515140d0040d95201c4140c17 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 881477320 1250 881476070 881476073
    0x507021215221106131a030609010e090c060c0c0901031208010f0f0504051302220c0c03390c1a040506031819060b0f030d02031801120e0109 62
    0x100307a0111a1035800701070420441c00b82d803440340307000462a10303600c5600b010070150308100742c03158404003415001c81a041020080c0c6c0e8400c11a400c20b40e2581d02c10010b1800100c0c0ca42e2117985803c0c441c522000c000c0251203454024040582d01420f0b1024a50050000591158603008100da008510941742c1100c03030142c99000501c10310701038100019000c04520b0070401200c0982c04007040e1031041300c0010f0281c8401001e00380421901d90025001071906074280e05802141001940410000320240040c0c00000c10840c1c9002050340000e002c5258a503103510b6000070081c0c000f220036808079014240c03000d88103000285281c0d0100450b000040b0440600c40785951070f000c079211955190003036003440d003440c00045a50000a00c825480d490107845c089606004102203031300e210070703030300345c0083c9401d0390414a014001240086000d5030840d480488d20303090000b0054501800c580c040e50500300c0c18110041c05003804c0800504207e104407160441d10341d584602002032411000014000c0e40380e = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 881478570 1250 881477320 881477341
    0xb0a120903112e02040e04030e030a200907030c0c0609020301090c0e07120b0109090e01060302150405040e0f0a03110327030d0207050901060e1503010e06011d010207060507021215 79
    0x24102000d41540140801c1211b4001400402e4100b549410540d00c0c0c07035076100100380703458004c1c01b0161408074003141b014100100c201140c08408000ea07200c65540c0d0f15520f00307405884503070341080c0004040716204401f0a1a40d4081040700d88010300214103c11241c549003260140d40e041b2901c10100b200c203000c244c07500002910002c1a40706e0050140301c09520000e001005640b04945001e911750f400360315018820f41c802c002541c2c2c01407522520400e800765404c829001400703883e0040e81b42014940c465880016207031f0305605924014501c100c480e070b0f4200c81a004a0302c11003010f00c01440501081210655000d036102004000002c0945140d810103180c660310615480a40d0002c41040c0965151036004030305580a07424100300c0c1c01518404603581420480000e284118007100204601d82c00d4103100c0d010380c400360f80f00585659154800341954449c0045540540c0c0945030800c5840d0092029040c1c090008200c200480c804031043c030304180b540071b0f441c400e1560080070010704070b41 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 881479820 1250 881478570 881478643
    0xc1e0f0609070b0301090c030219110f0606061e04030b072a0b040b10050a08150c0c2a030d02060906070315140f06071203060b0a12090311 61
    0x2500720003460994a85001c1e400188818051400e207141c5441d0400d2005001c1d404603070088418441402404443e190000c2030300d824400c3c228454000d0031803001800c10009800c07806001c00800d103502c2e010101400c41501d0785405141c07911068240000800f084284008034451002034943c4014108103c0f40010b40c0e845507441c049003c80714481c48000b082020407060b034050750000b41c0205a85580745c100c7e4040340150701003540003003034040100e480d80d4041500b5007418615084042182c03641c0c10603409601828204840c2940194101820022060051010485610901121603080d000840c1c2888628500c950141e4400c0d014480007107030400101d07a0042e02e500d13040207806050f240100012503d0322500c01605c412109910f02651540800c481c3c0e0200144495611035492801002c1484a50703400c00101e403801c90700245010007441160ba486d519652204803044072410000e0041200600c01c0d82084619444007000710000c20240c0100700021041c04840c4a00d2806a42d0111 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 881481070 1250 881479820 881479831
    0x50106050c0a02130608030d06030501050903040614070312140f0141060703020d08010b1306080a09060e0c0f0a0311270109091103010507020709020c1e0f06 69
    0x5000c201c207840200020420510450b4115a6180c5280145031100c0160000d90412803007408001168041c1108590140b41101c1c03080c03000348240d9840ca01c109440b80114801c2101040040481040c1032580d4401404010300c0790034650002d0800c0d4452038201c800242c09103203402d18070f03018800c11111050595004020120120328030202c00511201c0a4200d44500384031010200380c650003241c1c0c801c1200101d0140034050740c0e1205d0b0b041c10002e50720040c01c0740510210702000000f00b000103070802103c14020201d0400c051540ca056011916098020100d818095407000c4200001c1c0681c004d00c0c01926006008004c10080c0a04000d103240d501c00c206480f414031400c0401c0050400c5503002007600046545192080110082600078440d01c2c921082c10306004002141e5800c05901c5120690f01440201d52407080c200c06050882d241500e100015a001041c10480c02d03041d90001e080c04c0c454401990030010380c9503020a060000c101d1180800d0f00a84a40310352180c0c01c0020980c000f = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 881482320 1250 881481070 881481077
    0x39050f030a060b0a0f1803032a06020307020303041e050a1202012301060909090b040f05030c100606090602032a100f06050405060a0b04060311160c2402071412150604050106 76
    0x14950f40d8007401d80481d00c00030212000074204a0486002589d000701c41075a00040155503c0c9082070b0001d440c1d500071501200c204002c207030030011071a2060341200c01254407500908036540162140c0c40c1c8542440e42c03841c00c5640f50381c844a9aa10b4446111041990408001d4001d504010004e04454600c0d0048010301d031500480b5000b040c0c0054035190070036000042c034003c1c00d21900b001d074218820b1011200c420f00c1049a4030b5000d4005a006004031456075640003051903e80c041240c0720701c40c0030100712207102c50607012000c0080b0f03608060348012034074044480d00712509820106031213240103101d420700e5981d40d040145080500403140e001004442444449082c0488092140039602603402010750b1840400c5088210600b116529a490406660031200307614088111105038004d201001d2406043c00c556200c1d80c6101810f4420a81c02403d406070424041e080780741b5522800507844038080308400c0400300306201c0140c00b00159102c02c034403444d042003070005840c0c041e03100d601003 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 881483570 1250 881482320 881482367
    0x12110c040b121c031a032a060708030709090908030f070207080a0308060a05010f0203180d060513050c0a08120c03040b030f250e060309070939050f030a060b0a0f 71
    0x103681c045003444c40300368800c7c1074a02050010b4207555103441c58075080d075003082001070000d00f40302500f006144201c826599480000703456102c11401d548150000034140d000a001242c1001102041d41e0f60000d01441120550b580c1c0f0110300c0d16004002a056000c590700b402484214101044003001030a82803c00fa2003801845400a549210b0380400292414070b4207088659652a021a0800c2503040b480a00160400c1c0d190010310503c0c10b00b0440e0700e0302c9050b144501c5410700680600c1290640800b8005200822a40341c0540e4010801001c44d07000070000400c0c3d420241002e503014800c44001d004040c40c0c41c9809940160000c2c280c0c0c0034282d01807c405420a0f4040406808141c0c2603d0203602d80d2510045c10b4980107240e0001c60a0f20708081e400400406628071048818003020202e0b010440103000c800050540c0855020000350100190022080300c1e60046403c10b1440034005101561401c5c0c142040e00123440b207400040f500c2c5056900541e121051804039040702220514 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 881484820 1250 881483570 881483621
    0x6160309150f050a030204030f060b010f0c0c210c09060602060a0207082b09060b0117100302090c1306020309090a18140102090d0f12110c040b121c03 66
    0x41000b01110280c100030000401c840c9051090301501c00559116100803800c0404d0f2810902924000848600041611024a010510038803c1c012055000704a5030841070a044a2803108890041c4c07942d00310304800d8050340051403c90713103100205002c5400150a9050280003401d040d0040c080c03d400b14014040e403004500700b03c0480d054070019220360303081852600001c0100005503086020301900e081c1c280e8080c88403a402551002d070b400d0362010051196000c00c8800e4a00907122660030013052401400103041072240c544c0c0100d01070705c00e94202180c0400240e51100390781c01c100c0041e0030104070944241005801c09406c42c0c2d81100910140c0384a98540341600034103e070180c66500c140301c0f0f070f9140d00d40030342c112840414050b094855000321801d086110a02500c0102c4800070791060760501c09210b00c2d850100c04407110301805028284808000180c40d0320343d0b1282d8000c00018040000a4041044089200050702d211662880c010006412500c0031240789007140e0204c0351514 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 881486070 1250 881484820 881484827
    0xc18150b0d060b13120f06090b090f0f070918080a0903030318030215190e0a140303070f0509031203090d081f1a1b100c0201022106030c0616030915 65
    0x2c185e0b01e102d41c1d0107400c1c5e4100d0920400b601c2040001074407aa01d8204902c0134480307030355200b070322070b00c03481c8221001100d418440c0750b6035140e5209074800d00d0b0001f40c0e00307104003103450300080d10051810202c0c2900001c3c0b616948141d43c08400074801180303070072030100101030301070040959468254150b9100038030103890182d203c01e8446440c0c41a145e01c20006425580364100c2009486240c5408201f40b0314880080f03a61201058400c1d03640321000d0740c03080901070002048070700c41c000c039540c3c11940e03540c410000e880c0c82d0041c10001398140140c03088020180a0700020b584982c3c2c1000082c03046106100d00500940c00c0580000d1000a0240030003490081600e814070072940310140c82c1e0f180125034140da490502a142c1d00007055050003142c020900b0000810076050b43c201401013103400c900c0101079080344a41c0111800c000843c440204000705d242c100d242e4061006015103050744c1d540c80014031154401410140c0c41040401480141a8828000700250004020a10803002060f8015 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 881487320 1250 881486070 881486107
    0x2a0d0e011b02120f1911060a020705060d020708030a06140d0506010b0901020132010807050a030f0503120a3e092103120703090c18150b0d060b 63
    0x1e4058418100300c616030709810801c0200c01c4a41c0307001d45201c3c502178a01e455002c0074010042d00c1c03075100800e110070b0b11714040c030440d25506415002090aa031802003800070341c1d04070741c806246007a4281b1071880810001c2d0000c500c81c0c1c003010800030712a41002141c0201800740b030380c241c1c01100c1d850521000503500285550648012541c120340318416100102d0142240c515110501c01c102c4201641001a04044080902d0580800d46c80742c0c1c4c0300d442d029699042c610900b50300c000500e0301080480e1012070311000060094080c0c928160b1208005011048241c0340100f080e95215400541003d000003c061180f015801d0403498030600100c4c4c0e107011b481e901c00001c4540c00001c80044641d25a104070540b00061042c008180180b282c0a03030b100c3d00705405000103040c450300040e61003446441507010007a4001ca00c085c0160a01c404045505400500b03192425a2000c0c54195030111401c0c4200034107441c505940d88110351b1114400fa6a00d56024400740c540c10300c1610340b0305081c0d0b02c00 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 881488570 1250 881487320 881487323
    0x31603140a150f0b07120206160503040c170c1f020303013006050402131107030810170304050a080c130c02150f0a1a13022a0d0e011b 59
    0x1003030190340c4042050b040d840703d40c4180e101c009200000070320a01004054003010b801602d154000e4840202c060b62a10000c0718418059015602d80040c40340c02200950b4001d8000c82c8000d5455440e002400b00c0c00c80790410240c125808407500110a2070b1510805400100302c1c00041c5100d445544041d58038001800f8041c0034014000e00a154240b40c4810140a6200b10550180b000c0180c14610020501510b040e809000621035940741c07902180641ca204c80c8200081d5480c012a40d18100e60343c4034080e181c00304240b03104500058142c140c1000c0801042d002018551303e42c81c05041103000f010039481443d45810003501144986d5902c9034075102d50b50060381c0803071840d8443e0400c909003541d482c2ca40c01925540c2c3d0600151250f41c00220384030304d046003400c104090001c1d8519004c0748161100c01d502000d2007241800000040d000760103001da0348d15840006428034038000ca0400c12540700d030607083d440f0f15000c03000300e54010005001042c003070819004030b07114090310070381b070307480c5c0480 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 881489820 1250 881488570 881488591
    0xc0e180f07051318080a0e030c092e080d170105010e15090a030308040b090109110f18010801021e0405030d0c050309220b010e1c080c010c020303160314 67
    0x1c80055004507a0055044c414030615000021159450710a01079080400030100040d50813403941c1305824001840c0400c003800a03c444840d170b4408920282c41c066103007180101c20301c1c13040c0100c0c403031801d01910005018098040c101c1d251035204002c0c4004040402003a01c070000c1c0e001040141d030402883c109580c0306032a00741c600812594191140d00c602544d168002021400c000241030344286194050343c890010700c815511103481d40d500707036608101c01420b00d40981c0d040b0304d0580b0b8268512a10b11001910100c948402d0420803050004240c0c454501c80e500081c088040c54001035441142e06021b4100a00342400c2001203941c1d85020620f0703005001d141d43c0084180501001554100d100040c010b144080f40c0c405803d140080740100242c04a05054081c440c0f907004203202014041c02514a159281128600c2c08088404c50b0069905010030441550711420030702aa031602d1a00350015035403800e0081c0907125404642083c4400c051034405450038105010b154207400002204 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 881491070 1250 881489820 881489839
    0x309040e0105060a0608070c08040603200a0905120703060923120f07110613090606022a0a030f0f050d090b070b060111010903170705070203100c020a0c0e180f0705 72
    0x7c01c20390310058814800742401c01e01181c00526542d05410890f96541034003000c2100230112822070803680900b41700c03030003c1941034101344042d06100544031801d224890846a280c1c2c1d480c0c84000072912000001e0b20302c1250240d014618024124440d45000f514000600c0074810186103e0f031213001e000d09800341d10078002280024004850688542c0c1880109410707a24184007012072603d88161007800c00c0541801c5001540718004550107108144404051003410100b248040350510421444c50f40314411190100100750b003210b034141d030b06110707201503c031015180c01c0c203601d0160300c01000740c02c02003481c90500101e1080002d5951855105070b150340e40c1d4070b4010040c0c2e07030306a6040341d0054540c41e0100000901da4488045a02d0300c2c0c045200d0091391f1500e8204071150f100310700c4003070342607440000961115282c90b0300101070351030b003441660000c029599031b220b034281c0d140c0c3c440b28910003010180100100c0b2003016040303c005800050040d444500c0d8003030740760381c550b226641c458420076 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 881492320 1250 881491070 881491081
    0xe0f1803030a1e050c0705060a1b12090506010f0e0c030115050c07051c03140f04030b040302150114011e020d0f0e10021e0a0c03120c0f03020309040e0105060a0608 72
    0x810720400f4202081414046031801c1c145113025508000d1060380e0510490022600e20394140c400d25a44201c084a10000c98005020507205216005080d400d82ca1f50f410034000400c03414440180079100c8164403141c02407400e01000011400a010007d0030b4400300300411008901c4544901d07038010900303040303840c1c0e045103030b900c2c1c02d02c20b031940a15002210b080c2c40050450301c1c0c1040c04081403090300c0e500c500c6003a010100c2c501c0d00030000c02e503080c110100018030106400d90350300c0e64054828811078016880240042503082001ea100421180b0108248030321580c000c0340300d480280308403a001a00f850120402552222111180c20500c4003850b41000e045210b5040a6030030903001e4040c80707450007103842c02507465514059901c500d88062141030500003010584c0c550860b0019400140f05003191298000d001d41c865401051140c00c1c00e080300092a100301d1118110300940203940c58807070490500c001c1d00c201a000c0c2c03040e41d142804000907503968030750704000d8412a00e460241c5580d00c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 881493570 1250 881492320 881492351
    0x30318030c070303020d0318080a0c05070819030801060507021807170c13080a0302060c130302031f1109060d0b04090f0f1505040816020105040f0e0f1803030a 70
    0x11200022a80c0c003680d60007205040d000038401e0034400740341c0c7e02000700c0366031102506040f05041b18024010501009022140c9200e86407000c40540202c3c1503400259407903490380d2a02e2030f422454a41a1840b10503102415003000b00d45004080c107003422403a01400341c7c001401d410680b00e803080b06846010100704141e2181c0303504002c16070035005c0c48100d800c1008401e6039036006021320400800c041ca5022803000c002240240041e60326400400e402d80700c51030206c405400100c0b880340c01c210340c68400009a0f0341044094644c0034a5054140c41845080404050304c4096401e40c130321400070040c0014644603881184c2c02c44601ca0740009044800c500040d011f001d80100140860000d100c3d20320500c40355400304021540f04280302550001780b2805030041d076004440242500070188001050013a40d054540302c2144145821460035803125020f001c118030942154100c0701b9007a04103d80030038007884494001c102c1169405a61901e955030300d03540d120044c220341d4900e8645500281c4080c0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 881494820 1250 881493570 881493577
    0x9120a02100c0e041d060114100503150a030615050604081005060a0518071b08091216060504180b1f0909090b190507020c060901020304080610081e03031803 69
    0x20300800900c1401c01300b00068040d5084044010903d01406d8000107950000f100302910444003d40802d95039442014251619040204418280c811203e5101d5640da43c2084103409180b103100009200d030504107903400d0360030141e081140034640c10401070048140004044007441a4110041010381d030740c601040d0100780c1c41c2d0000350412884c03400d05c00100c121310292407080040b6551310200503c0c101e810f1843c000761701c4015100c808200801c0300700703040c401d813280260150441240d21982c0107545140024031b81c1c0e40710100141c1d0100c0c0502c464551014030800c00d02400310300780004036010000400320800c1c800c90908103e0388211581d642c6029007040c00092402c08000c100900d400d04107a0410f2600712444080040c401c20342c001804101d11603140155120360084c0200000c51051101070b0b440f2030700e018151310081c800000c140b602085083d1103242c407000404034151906100c9440c1c4921071100c010a00b100502d00703000b484001066990060090b207941c50412a040320160940c0b0 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 881496070 1250 881494820 881494847
    0x1809061506050a120902010e040504050307050a0302030918060901260d020109020108280f021213050c061e0f0903010903200705030c060f09031509120a02100c 70
    0x400d03550014610b078115002c0e2510911a49034901c0310801c1c450550100d860222000380417502e031502084c1c40d402d1560000364018880e600b22232170000d864444621305114001c0c03c43c010703880051811001d0070201180000f500140100004c40e0502e1400604010814029400c600c1c038941d51415908092480e14030342c4030010425501c0003140417400070f020b4000820164080340e9840f0100750200403507120132008210b20a8442d920702d0480b041c000240c4011980b41d6007198091102c2c0920302c10024849010302c41014101140e80c0d0b56240ca03a06100c0300540c0d0300e10540e01801004203003002010031140a01c11041d00f81d907141c8041841ca4060301910141540640c43c000300d41c810903403c00c42416109092140b90004444e0000c6100c3d9200a1400ac03580c058110305605045030a2000190a40d01d0404e40c099042018000104c1c0c030304800a4205601c0d203560005000646d01e040c40503c040d90409020286407820b2420003942d200100183c404080b0755807000100840e11940d80c04d007548 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 881497320 1250 881496070 881496101
    0x1f050a0810230a060911070f0201030c0311040b0c07171b03070906080102090a0902131a0d050f160305040b06120708010501081b040e0c060714030f0a1701180906 71
    0x500b02183d402c8001c1969002d400e1402d07203441440c002c0010b0240c10744100c7c1d0303130102e10344c4201009540118040c0c1080078114050685543c085071051a24501420103014000325068613840c02284403881e00d44243d000601c0c0900848031207002120104111300d04560644541c07808101c00c40200740b8100d2241e00a0014914106001c0380003a01034000b06004c4030102c803c1600181c550180c14105c0c03244e40400d8021407c892400c02101c00b40f03d1740e0351058009848001c0c10a00c0e40c4486400b0344000701e0f120744a0114007420810a42021040c0200c60f00702ca181c20051440d05540d46080204003038002d6125100c0c0e020b0001c204a0208940e101810032030000f40002e580d82c02c2081da07100c0e21420140e04520001544522505151107400c07a448481c80c02013032600700c1d0000f441003a80c0400029035000408210158484108100804001801d03542c0300b6540c0d020b80d90300a0059290040b4018540c0c074401c0108000821344203082c1000c040d030700c00080c8800880c501000101468881c074642d5 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 881498570 1250 881497320 881497391
    0xe030a080307020c031c0e0d0203010f06030c0e040206070f061508060709060305040503040e370f05070c03030b06041e0501260103030f05121f050a0810 67
    0x2002010409180658101d40071941c4080014081507141c6162050300c6c825410030641c500182803042c2d000c559a00c4000d00041d0004c200741c1c02213403d482484501288040e00c440c01002040301100e42c00700100701301d202000e40c0b4240350340028003520030180702900d0000d600540205001840c1d0105030f05035062184040f50300da94495903500d4280865801001c20b40200000513142d000340a02c503c580d5101010758035190808a10030300408010300009074100c1002000f03031000e01c00c0710303007002c402c40080f41080c403071b00e070a03160175045c0c030001c064150000781884240100903801c6003c070500b1a03818200825114201c07404100c0d40e0050780c0c44415030041440040c4050324102800d0b50a0311001c1c1d07070705140c02f5800c0c010702c2410783c40d903400300c8c010345211030040010070b1141c0200081c1452911703001380b4044188486880c0313000182d44010f6140b51a40c7d081400c41c40e00c944c803100400c801c0c3c580c400900d203811020b0340c540001e0b428010400361112494408000b4074460800b040405102c0c0404 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 881499820 1250 881498570 881498573
    0x2111070b01091a060313050304082a0d110d020418080304050114010f060f03020f04090b040e06070210020f0906030f091506060412061401060f031b0e0d030e030a 71
    0x1180403080c4156129a440c02e80400f00c8020030060304005904081e100c80d1442d1198603165102400001060760140001e00c004584203400380f101030701c841c81020841c1c00310000300d00da21028480100c0a00c0c03003161407024a000086a81c2e00c03680b5201021070b4081c03482c0e80c5500105004d03000002040082e5400d80c0c41e03003030421403110007450107240900004c001c40c520034554600032910a0140390780301d0801150400c074080c401c1034540380c802914034000d030a02464440010b040c3d0815000f4000b8652a480d004030f41b030170144608603607946e18000805c164100003201039160005094442e05440e000101d40050302c4446003110240c11000d03100694034501001e822442c10300c20b640801d294055900c0d68813805a02408882c058a8000c0001d4a41860481c06a162007034100086800548131040c01040181c1c251415008041580307901807803182d41100113045039510115a03190541142c2101c80142d88840310510801065130180256001403e00352412858100302e40e074076200384181c000 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 881501070 1250 881499820 881499833
    0x19060c0915020f10050f062202030a060315091203020901030b12160e0610050a03090203012c010608060103020f0a0902040b0711060319180803010b03071e211107 71
    0x800d50f01800e0169803210f01d8501041d0151001a2015403154114501007401c9151500034554094520540400750514041828003030f608100c9944501c181d403400d081007404a4a000b00c08204400502080300303120381e41e9482803182150b10ba8404245e404181427820364081e502c44251341e40c00510001d03003c50b1070310056a540721190700c28001a0f01c861310004018500d1458075005950041644201c090030040c100c03440e812480c401c0c1c00709600c5403094005a2030a00c80d1501826060440a00040c031020015088203025544881d103a80341c044100030104020641c5419298103c0340c03120702c1c60004000a50801d6035401421066200107000250010700030300a00a00c0d104400300c001202e10241040710a001c11500f041c0003a004200345c0c044824294040381c00390f035844420b4190802e01d511490001d40003600100c00c1103a00006000070180c0110a1703860100f5145405035018103480d20090010b0400300e0419194000c0c1820410740741c1103030300400c10520100d81c00c645c84030171508025 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 881502320 1250 881501070 881501083
    0x90c0909020714010b0a06020a030e060d0518010b180f040501150801020a090504090210140d09030e0307050d030203120c0d050702100b1c080d0b09040804030309050319060c091502 79
    0xf800958a464907120b01800c0400c815401c40e000c0390054800c0c1c143c50388064640b05446100c040e4056401c000600da00040c0d8440c00d0300441d0020000040700f0b070424092400c50b56415440c40c4520403c41c4000944590f016a40b5400f09070015111420b0700c0f1490814094000094003681002d105400426a03010540c0901007544441c0d5880400301d99420a00044414001010f90461440307a85040c2007400340100c1e01c544000d000003103260217110100e80b030403240300000403000640c2a90a0a440d40350400028000c0c0000701d41901c581a069a000b80d41ea1080042d01d5010003144130001e0600760400c0d098481c58075090301d051143d443d00b003800a444140000311411140d2401801c1c0b442800d201414112618003403115452051441e22020303190307000b041d581c100e25a20703413000d0243c5031160080c5500943c403503d08240c0300d40c02d524018200505c4c58100c00d000703600c2030081410911400c8080d10341c042c0c008000003510351044201302c1e220200307900070586c82ca0340e41d07034104c40650740000c10 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 881503570 1250 881502320 881502353
    0x10e100c210810050123161704091b0504050112020c070b03040b240f0a210b090c030303070503090f070308041716090203070203041205010b0f01020c0307090c09090207 74
    0x4400c07543e502d58005680c813400000d900c0402c401048110101e0300a01401011069100e58680d00c42948990360380c030030b0001c00340c01010310b10408541000b00400d64050b0741d98102108084000b2030527126402002d031301603031040e03d0410101d2a04040c03007203c03a44c112508480580180c460315500d0310309403d071075802502c0803501d00040d20300003555030754008690b6030f010035903d42c055580c401c0e4008104406418104042e4004803108000a030500d01c051000040f55101c00702c420141d011b41000008184024070802c46038100d03082103540c50fa8080100c0368003240341d00f455600ca8480e80780d8246845030300c0710030380890b03c5204000b0050100c0c000c054421a060401501c144440d00d103c425256000591050841e01e0801d03010b00106001c0d0300034550240c2d061040b68100790b43d031795121440141101e8141c560b42d6481580121509002d0402d41d600e80303081c002424407005560202e60350700c443d8496403c1139681c5650b4455450312904400c401880c1b43c01040d03449407010704081440b0601d4198 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 881504820 1250 881503570 881503591
    0x70c06080702010c0905120304090f0518120708070f020d0303090b01050d0203030319020910050a1404031e14010905030316020a0803010e0703020403020a1403010b010e100c2108 78
    0x740495105001c1c010306110181d540b02009442e200c00c0c0101c0807072007048003510f40824003010590004038810b010110703800704000b040e43e007003003044446a030700c4070080d40b038041d040901d082501031000011142080e5001080c0d6a64001a04200407140820400258004071281180c001c0c5681070b04040e43d824000c489508050340d0311000c01c91581e42c8110000d405810501c0002e4201c10710300c42c1c0c1d500142c4420005440c120303061001820021030311400d5404034501003058a806540001100c00c000412241c2e50318150845c0c8801385801102100d004414a41d484200d04000341d0000c09406822004028800210245005034a83d042110180e603070030030111501c4802d61000982c3c1290b1034102e0342080c0b40d40d00340100c0b0445d0046c01071103d4145030b0204030000058840101d000c005029400803803203549070b003004060940e0210a4800d04100038130209501613541c1b03040c03204c613880c41401c021004001c40d140001d80ca480f8203201030010401040c0e6040303a99080003c0360b100721000302 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 881506070 1250 881504820 881504837
    0x50f030411011e0c060207021c0b1e060f040b0406090c0908011109090c2503090e09060402011e0306050d05061006080705040e061305070917070e06061c02070c06 71
    0x400c0f1141011010a110018110030304550114100b580142811800581104130010303003074401c01002c10076614121201d09503402040110910205255210781d030f0714044180504203040041c0b110619038480324412659840001d00903030329036206400034001c81c4030602800311008009480d400385449465015400c10302c030500403c2d00001140c40ac0d901c01407011495480340490300c10309420810101040c00c50102c0a4040c2c004001e90800416109903540da07170031428821510803024020b080000658011400d000040c2c1e081100801800802c40c1d800c4441c60000e10100c0c0501115801755070840a16160701d001c0c490049a40c510480c0d41303251b0f4000040d5180c104444a01c4125070001c00107001780028404011901005d80d00800000c000100c5440a00d000c0c2c41201c0382a591070b00440d200c407008010b241f224080480d420a88800542541303450035060321000c420081150341708180000d80c1480ca242d5001c508071003032070349400440d100e060510345100007c10601544002c2140c15 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 881507320 1250 881506070 881506097
    0xe01170105221b0e0411010807020c1e1210050c040605042304020c060907050102030c100513081207020c060c1902150d0615030203010b0f0a050f03041101 68
    0x5000d0a40600b14060030401092100307018051540e80e6000c044800300b540e0f0100486410704200294003070001c16414240324102860036078200c24049028505001c0f510040003101c940200741084c0201e000c0d100584111a042c180c84852101381030f906611442140c25814070002c009403d10801c580c4903002c0145803184244801d66001c0e5110704030015030b080001380b1041d20800341e090792844403603c0d540460301d41100042d0581e00605030314225130344181c00f0032031454000c2001d040203003030a0000c1d600c0d041c0514034142d2209032100000c2562a00c0d540800d1345188184448042141c03c240d0244d12501d0f04010030410000580c0d50300c00500c11552030512601d00308041340c020040220042c0301200409440c92400c100f4132200b6a40b07c5184070303403410070089410051019200384203000a05904102900ea80254a01544e80c01c040c814001402810180800c481d002c8603025030700c0c4d8031a11401412149441080d864407108070001c401d1100b00309c40c1c0f4101100d200001d80380c1618a040f503 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 881508570 1250 881507320 881507323
    0xa0e031908061302090d1515060309052a01032a090e0906100501030f09241109090711030913060e0703111801030912050a020f1b0f0402130e0117 64
    0x700c8002c00d034410186c0d0641000580080d0030100c91004c41f07440420640d2440220b2003003450958054001300c0d40b990403d600700b00c814041c2209009403400340040c3c013182c55079400e0b0001c6618104506241c2e803003038107074800e42e40b501c0e880b03110400c0e001250002042c2c40d42e00600c0e0920912610550b50110008070f4040701c400f06460b0b10034094250b2000d0740e0351030300b001100a02101a0384040c0540e9809500b8007040e00000b04401010b5025540c60a442c40005d03007408985512194209620042c05581d0051b500d40d219250040e00e58904000c040810ba000141180709030540144d10511030740400321456501e410410480d0000c0d40031884503540e184060b0195a900243c049940c1c0c001c001d1650003207a001c40824114206250020b00c04003a81d90380003540800010304000b161000c1030408000b941004094446010300d4080d01c0c0c80103000c003048800c48080c1c1c4100d031158412400d030107220b840e264142e03100d442009034a40c10702682c500342050070690030b0140218850341401c0b6011341010 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 881509820 1250 881508570 881508577
    0xb0105040f1e0c110715080c1c0e0d020c091b0d09120306050d12050a120603080304061805060f130506180f0706080f0912070602030f01090c080a0e031908061302 71
    0x50a030b44400100728a001c41f40404001c0881c000b07004184401c180844400300e030700084044040e0001840200718a07028600b0111543c15411076100700202c15141d112215030a820000942c2c4840d4421489225445240602040d081225240814143c180b05031004240f02202598608114080e2074105000f0b542c0d0f8482005011401081c06200301c041c4100700030b145009940c9170499141c0c0c281d40124054684613401502d80410100c10700c4144044e510401081100c035400f1590b2400da0359039110b0315618010201003000b540e0781e0000d45e00c8411403460180c3d00d544507040d40c0c8a49043c0380352900c05869051068071030b00c1100310704100d00380c00080701c4003039659070f842c0c1d031030907036a191480d92000c50028407260741030241c0d030880520028028007514003030344125009030304c0b46800c00c0340140100c0160f01540324141000c003a8101c803500000d0140d08202e1101d004101811401c42041c03961090b0448a02800692560710075400d9011110303501a0070b08554090f1000c0550a98205901 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 881511070 1250 881509820 881509829
    0xf0a0b0a05121303050702130e0d0c050c04050402011b080405220c1407020906060d0603150e0d0507080703110303100602160e011206060b0a0507030e030a0b0105040f1e0c1107 77
    0x45c000c0140c100507252054100440d0300c07102101164503124005002d040000c1e203140907010909800542003003090a00580c0400700701510100154078150300001c080c0305442034400e0301000d18a01d10001c0c0303c1d140c0222405448045c002d4943c0300c0c4003a8515081c00040d9a1000385249050b5000081c5880303100360218a138840b55030503040200700d03001c015420202800c1103500000801c0040f0b130b45407050140d14000d5000d004214800c2030503c814106480c8408071007640d80d08003c0342c81020710b40250540e822150030001c1c254440340e4a107400d032002d50015491544a2001100300103807000716104036019a4500d0342a9031500c03e1001250340302e0015402084040b00e02600180403001c40d040308240e50b21300400300441c0099a4082055042d03115034889000600d001501900303142c0c0012007540700c00c03400d4005014803007058940c41c25031001806414800c5860300c0e0440d00c142c4154000c1e09619121606040620001002050044c00d18514010105940318100caa802c1d60215203541101c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 881512320 1250 881511070 881511077
    0x9010501030c14030f0a0c051203090102060f06040b040e0601090605010c020a0e0912040f0510080411011b0204060902090405010f0803192c0a08030a0203090f0a0b0a05121303 77
    0xc83c1861145441e03116010480d075058070800c60a01c00000c4200980b0003d80c1c05000c24030145070030241880340007062075013030981e503030b1080140e942c181c0d9002804a5119241020781c116a840b42c00008000c0c000040c0400d60141c1043d40140c940c03140407030514120f41c0121000c11405641e54015100c1540300030010754404440f0a08028040e8450f001d00e6202c00e03842d0907030f000c00c0040040e01c40150000e400200200c0c0340302c1010302c010304100c15201019000f0b8105140140703030954410200c64020542c682c1041845000004040502040303221070941c010130078800c16484060360310083d001002c03024442e9040400000311016075a10704000ea40748000690301d01421440d6400c0406881c1c201c00e010002401c190081d40700000015050544000500761a80c010040402c4021170703554000301c03207517013080020030700060300081120801e19003501c40020302d051400000b16004801d82c403011020f0400914094040e0307207c00106545040c0c0d2550741040c1d2150303018648021042c90780103020 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 881513570 1250 881512320 881512343
    0xe0114100c023c1e030309061c1a0319110315090607110d030203100302060415120203091506190b0705010c0c11010804061d01020702010206060405040807030f052205090901050103 79
    0x641d0701309040d50b03a600014003100d281000c28400f155203540050501440c411841d04181d42c40c02d50ba004d2026105c5840c3c0ca00303043c010240d0b0000b611010307101100000c08000086c2182044010880800440c10080507074401000c95501e031280720404940464484c040d131000104100d0003200345525922419006085083c45883d00b54001e50028000070700a03200ca940000040e900d0320f0052026050340850710174100220300b006401c0d02380001d101c04010b070051040180448000035408503800e1001c3d601502619070030007003071030a9207001261399110000358021420341da41c080140040740c81803000700980b440401c0110351078058894000c0441c1c800c0700c01ca00c469032082c441503800c603014080024003202c80d07416000451105039407880705a500803070007800359a01030000c0c59115800740c030203011610345681c840e800b030701c210007000781440700034640900b0082c45002990442c009000381045400b900c0301881840e032038648940d0344607043c3c410028046010600803541240c0c6d020002001 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 881514820 1250 881513570 881513599
    0x5030103080a1b030309110f1c110303030106021c03060b09040911090906190e0d0309140601031b17060411060d1112010e0114100c023c 60
    0x71a54080381a190812103800b01c0321294441c03c1020103405032007030310005000943c03860503940d4000360721550742c41040146004005901e42090fa41600120550000b00c010081c1c074190906400041e907071a01031201200100d060f42d000518045006070080100400d403800c000110180c401a0203196881c50007440003019034103054001c8116140f003031307901d041c0951550001c941096404c5480050950150062200c865203a160340d1001807241407051011004040245964030051603083c41015500c50003501481a840b40395900c14884c48152552540c1d0381c00c10007080300540010301d418050741d2400064542040d180c001c103c0201c4405040d185d070313840d02c501348410708046645802941c20090a049030722a4810354080012401d0f0305511100d42d18680410400c05802000100960340300500080983c0010081540c1c8100c5500f06030b00d1102c1000c5612403035602c8000c0d040312610004002680c68046400d00842d41c241d5005103200d4500c0078000842d03480800c1c2c0f40c0081e8417940001 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 881516070 1250 881514820 881514833
    0x21b0f01060812190c0f150e010926040e150f0f090601080901062d060207050d0809150a051216050708030c0c0d110601090c090905060a05090a140f010605030103 71
    0xc481e243c14808030341180f075141c0210390404c6000440d01d10005200003451481c0724442c2c08e545249400080101d440c0700c0e524050955485d00740c1e9800c09010b40034507541403170583c0072036011b400e140006c483e031800c00f803901e8105001e0300f000c180d100b1203600c110480b150030503600052085400900240060701e40800540b09003102410341e0b1115502c4030300c081042040801c000c0d0400d0442c1c4692a80f010203c0d29182c0841d059030170120071500045420013460391064950350705242c000d0030740f0760758000440000d1094181800110107c0f0320208800340359540100140001458903035802e010303940c605c8000b070103030080c60003008040f030f00600c82000031589650265a1180c00025601c0c070300002c181189152141000326840069810402002d00913001d0203c10700400c1d00c6481400801a860005803061035940103201c1043e030740b180000c0d40ba540303000c1510003c14000c0c0059600741000020000580300c010a910800e545210100c1d440d000700b01103a40c120703503003a62581e00716425603a922 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 881517320 1250 881516070 881516107
    0x40e011a27011e0e27070f0c02030610050108161b080702030a050c01020d1103090103020708130611070b070f03030c090b0c16080c0d08030604021b0f01060812 70
    0x14100892002000c50003003e60648400e00c8010381c891800902030f103420008494950400c244040d48625030000c0401c040c092015080401803e0503840041010802c4540f01500d03580a03501d48104014011855040103514056407002c3c1c1c1c80c8500c03176440000000030100030800000004801c01c3d100c440c2c49040d100c1c03004904c6c1c810304006203080c0c850b40010340340880315003060394142c1047d11085041e42e0104415030010050341006482220310000701c0342c590094047c2d442c10706400180200400c80500200da000f50070b14030b41c8405042d204c081c001c0c601199914035042a200e038000105a440501090f40d002682c041c01404400002e580c044003c0c2111010a80500c1140ea0003c5842042c0c10040c200518100004010040581510a0300b9210540c40340700c0d641c00851099081d42c42e11020103000542102c4029030300d4480c400420000d12441c0842c00342c10f401d000101851210115a03c0f0f1041841c0b0028440d594548200c7d40e02e032114044014000d40d0100070f801d146001061a0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 881518570 1250 881517320 881517397
    0x4020405060418050601080d090608220510050403030c0c0c1404020f0c03180405010302180c04090c02150705040627091407030c050408030a0302160503040e011a 71
    0x204140342088043d030b4140d14030810840740c0c5d420080052240300d0301084200d190519078070340700c1290307894084090300340040580700144600b40245a03030340c05040c4801d150021b0f80d0250481d0b401100231031003c40100300541d000c40010b42446140304403948500070260b05c43d50416010300300d940c50440155901c000b014038154004d9002e125555060003410050141901d801c005150f5801d6240e03e010343c003c0c03550310b94074030031440c2c20010b2000d1b8469400b003005114060743c0440300b03138549212030306031402241c0c0200c442d40d042c441d0010006034080303200070310a0341d803030860740c0360342c0300c01c1070580e0540142e008040004084401c1e8000d541d4910040fa6501410101d151020640362a07040040d1540b041040c107410b8100f100b48410198140302d0140030010a02d00142054145505c09407248640301c000010103401041101034018016500756100d0b80c0a81282ea4440c0c0d82c5107030242005e001d1149818080c541c0c060b61010022540880b42c4448209082e500701d008040e0742c0d1042c01c081d9182 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 881519820 1250 881518570 881518579
    0x905031b0103240807030b0a02030f040206070c0801060f030219060206041b050913110904081b072d06020a0c06030c02030d09142b080726160e03060402040506 70
    0x5502c12150114030140c025144d00b9000e4203000e400e40c101200007103000380002d02c1491040040190b410144d158403900654102d032010350391a07070760400c0b4540366155003041c2c641e0b510303080c80003404007004000d4408036442904d100048800c07541100020503428843c1c000960448400035000448504601c0d103002d1034000b07100386040d101c10101e44800c1c0112040680c84416060380b1090010942c081d0310800401c0340e10001502d450f0382c13000c800c0e018104902c0c80d800700001c1d1034070140d00d090120310042d0881c502c0920b08401040382121440c401110b05911090740c13072002090042c40450030040a507003000c200d0500c2031034040c00324000c0440541c041c0c110700003032040d5204880c80d030140c01403c1c1d000b030390104652080d0341c1d40507060981a00b96000310300c8510741c640884d2078003023603800070200d5241800085a81c50310820381703d0010380c8862120380090364083d601d82c031441e055054050341d464201100107a06c0c84006407042034104908584c0740d07000174000380051500390446980041c0103403 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 881521070 1250 881519820 881519861
    0x1b05060403050906040b300411040b13091104150b2a010e010c0e061303060c050906071a15030a06051b0a17132315040f02010905031b0103 61
    0x40c201882500a560f900500c0403a41c7c2540c0c21003040c0a80a01c070741c40d9002c102c00da0900f0540d48014840d0913280069016540b600f001e18070310f40c2ca00000b406144039450b0203002654842c41c2c01e00040e00c10181c0a032099141c108040032111141c0901020b86441c160302c103103400d100d549000700701c804440c1480d500076071013000600ca580080c0186100c1c1000e0800105450f08044806040040e05c0b900c624014030084c00015460782048034110100c0c2e40040c0d0000c0c00c0d00306940110340c944101d850940d0015400604941000140c0310b01310360761000b02d603d402d082d80302d41ca1210300b0540a403e116a0652204000742c2c045120340d44201e410807103513080e200c1580d1044501070f0070398000308400004030300400000c0044030789904203940d1141d00c000c0321072443c003581c0d642c0e120b004000c0d01000e521003508a8411a0540080005206140f46507844961503e442d1503c0210290303951400c0b400035100c41b90010702e60074005008030f1520200d0282c001c0d40d80004004600510010005000c107900741c1 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 881522320 1250 881521070 881521079
    0x6090717010f18020a1403030403141015090c030c140307231b070807031b0302060d050105040f050403020613110405011e120f0f03050c01050a05071b0506040305090604 74
    0x18443c4450034940c500044040d1034040c01000300300529a48a02c4000740744940c54599598080308803816698001c002c04120010480070901c1c1007400514402c00501d0500e01404400700462a00101d4200030010300075041c0014003101520071600c28000070031171611980306001020b6000d50381c40146454a01107007400c0101d204040c00c404000000a640001500c003017440d185480c000c10030100d540100011031900209030742c1d628540c07102602e840368507501a150000b007504000011500101110f4840300e0488101000b42020f01c1050320551411301c1154682d1141e024082c440c0d40c154003c0c4c002035460040444040c01d112504031203c0c41c0c0c0041d491030a581e54800c05019284141a440c0100c802194000b2451015048111420540c244000c000b600301d0300032100761541f16004d0358440c6e210746400d40346c6001c0e210564015500300f0040090422441c1c1c00244a114541c2e500905600c122090b111211140d12002c0c0c82504a54002000301e402840101840080508003519080d641e = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 881523570 1250 881522320 881522351
    0x50a05010e18010e060f2719020408012a080c09010e061b010b01050705100b010e10020a030e0114160f0b1602161512020d0c02031b0609071701 63
    0x1d8108074132001c4032100707200050500540d040c0c0e180c6001d0711140c24800386580305080c0c290120001004910085000034200840c5940c1941d0b1451104010b6403201d8030349055038003a10f5140d554023044900394407082100c94078504001070765809610340c818075460b40e08101b1201c4d800105c000b030602081554034000340c0c8482c401008110051a40c1c00c1c0310141c2e00c0310003420b4038445006e05040000c04d02250010520200d0b0034940300c0c03811980080d418985100503035150b10f0b541040c84d8400c144000000103640c0124011140500c01d60320302e03075030301881001542d440810303120001d4401001c2c0011501e00d0600415501d03101d00415144001e0003140da40c00038880d400300d41c80459905100340e0f070910b81e90104109154034104444e0040300c0c505108403955011001400e604c1007200240841e19040b64642c1140c540118503442404070009454001e542c039841984840038840c80d00310044001070000c01c0301402140c0c01c0d00500810740c68040344a00d400704507408403441d9561030b04800d00c0c003100d = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 881524820 1250 881523570 881523619
    0x20f0402091c110102010902130b030a120503180102210606160503190302120f1905090d09090204120b041106040f060f0309051e0703051e0f0304050a05010e 69
    0x54140e15006a803146840700c41d402000f031403641507a05101484c001680d0b800d03105d81102561001c00581404040d000030f2a00c1c81003480508107011050044081940c003100640c0328855a1460380000079404a2540c201e00c1400307580e40030200b1030a5000741c0d6108981180340c000900405440c01d02e5181040344c0c00841440d40d00b101d55a00003d1f84103030800f0414685201c240382410300b1810070011700184120600000c0080c20f400c154800041c3c610b0140095000a503090101e04008500d0b01034100c0f0754900d07046040001050000000103000e1803d8022902542c031003d0551550070710590342c401900f00060700c02c40b550200c0712101c4125032141c60140004012030800b43d1307426441c100c4e01a01e030001d00315032801050308207219400484c0d40003c1e40507a500d00001550021104072166508040d03180e0001442405941000c1202ca0000044142d503801c020041d80c1030a10410b941d02d030382e48940c1c840e0300e401003019a0b04014542c00b407a0041121100030b0061311400b09010b000c60381801 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 881526070 1250 881524820 881524849
    0x92904080303070e01091e05090a020d0c0201020d11090307140d0501151a03040210050c1603110f0a060801180f050415110c0601050603070309050604050a12080f04020f040209 77
    0x41904c1e00700d01640d0381c4014003070006c2004d40c0361685207500503409101141c6003409241d0043d0800408618545665812206c0f01314109000b0421000ca070361009002c4c1d44217840110503070303080403c4100c0e10758944045840e00f801c0180101203152030310345407003626040c0c41070580d8007000d900103d40215070280500996081c2c120b007104246400c106240307410085540c0180c2d0100400e004100040c1ca0b0440c2030740e500f420b103041403900e036440f094030540303844e001d0202d520b1400b1481d0310000c108106840424459542194600e041001d054140f100c002c406202c3c6d0800910b120004001c40c000500030088101070910001c14500d814440a009403002030b00c08940005402098001d41e2240384156103641d101c4614451524058402e410f55031308060058070711401c000004100300a0099000c100041d42c00ba00360740740f03840d160401e075844038945101034a01b0a080000340c0803891140345110311440c08106070004c40e45803502030100d070500c100340f000d40003030342000040720a5588001c01101c01 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 881527320 1250 881526070 881526077
    0x30e2e05040201180b030f07030606020307110a0f090b0307050906181306090b150f10050d06031e0b070801030f140a050105150117062815120b0109290408030307 71
    0x241011f408504901000815030400c05281c940300340022507021044a134440e410a40a24010f01001300003900a4219801560140c0100000003141e18103900200805c040032010741e0010b81d504c00074040188812184154032110540401050160103038960f40c104c40342c851019428080d0b0707950001281c80c1c1076020748481c0030500402c041c2d06003202c400d000021003503d071201a2602c000108001e6031540f0038840503c240032581c0641c10403158030200c0110b40091501d078038100116820103501003041c009440b0112251b00041d000c070700801c4e03941e04a980c02580000085000d4544050284203500e41d4803c9001e8030740e801000c94004d026040c02005d00494440404141c000050325110300c00c01c921546441b031070304004181c0c2d600d9521a21526410001e280440c0208510a1055410b500108074003030b501036000504551000003588400c107441800c00c80d41250b00f0054590203014403490704c0128080141e600300303030000c1c6052240c82c51448902418961661481e9046030011100744000 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 881528570 1250 881527320 881527327
    0x32112050c0c01150312030e030904091b140d0201050d020d0e0d0f142b020a0509040e060f0a11090901152d0e0a0510030e2e05040201180b 61
    0x102d003c0c443c410ba400c0403180600002c51440c0d0300c88120b407404482503018555240500701020390305104580b4a088002d0080010503498a0080c940700500963341c1c000412009010407800c025483c05c0e0264080201140440551540111407540c000800021295002d1210503d02c3c03221f4014011001c50381e0700a803a050302084402820b811406101c1410021640501080c0610040c120b80c01142902d00d0310b0031901006248a01446020717003012919480000c403206402e52001c00ba190300c000450b4148211403842c12280da44040c2520b2418100c0040c80c0401da00050711740c80500c6102c400c00415052a2114000482d0b02c4002d90007903049104000407000101d03441079030104441b004001c0460050703141e10201301c040d090107a0003010b00c03501c41010072266945280c0c2d0360051100500900154000b21002405000d641c40c0d80200ca202d030100420500350006229290b00b03481d0440803480c400007620202c0a00341c081d105905000601030110141d0b4035242d03048001e0003446225603a03 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 881529820 1250 881528570 881528587
    0x41814010b120c0f09100810060e0105040603120804021f05030f1003030815011709010209030106090c0e0607020d050f0616030b0d0b1503061816032112050c 69
    0x324902030b0180301e100d50043d03428001c40d030307462132900045401d00f40c0d0051100d03079512180389180b840d00c6d0000d420a2203049100c0801000c560020016201450905645640c1e544107000a59105020091103030344003c007200340c440d224102c038a81c02400180a00d441d0215041c0d42c201c41518502c202000030800410013006800d1325048030f030021102103080885034030f1500c0007400e0020140a80e01810150150760708103038807521204407000304902c40d03a025428a4240c0600075480040e806019500745400060b10266510401003034000d20b07100c102c2148134007810010700e94029002240d000070340c00c4059020400402c400f2035040740120003001103050031080402a02204803160082505055003c1d2060312080c40c10800360360f02c600d42161540b103858241290042d00d41503503825204600403c06060340c0081001150101c050a8030703a00000784010001d0041c40c1d002c05410010f5002e503140d40040000c900074482900380c40c000e40700c112018100c4094940c00c2d9025114981e0100d00c058 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 881531070 1250 881529820 881529829
    0x150c12020f01050c0f1209010b030115050907090803180a0801021909120c050108150415170714060c07120602040311090f0601050307260109050708040809041814010b 73
    0x7034102e88220111802e01e000d02085d03c0c0a88212454040c01818800c040748840c1800d40000030036000040003071004c3d85c05290a10842c041d10310626100307100d100f022680d03032801a440c10083d40d000710b018518180c03000c0150796100c1040d2103615000700f030044e0001403c0701c4c00c0c8090642e10701520200b140117101900010400d51141e0020111240b40070301260028821030b000c1c1048460030b0812002d282d0b1510410050328510303201040c0c2180c10402d0301c414401c02100d6180030740340d550102d81e00882500000540d651107a004103034445001d0f400e090003502e003540161106800c4082143c41d4140c503040b004401d1070240c07104a41140e00407900707004103c5207500b518074020095030100304a180108444c14038a1001d40024140702c0000045070442d8460355105001d80c48405562510781e60035840664510710034803c0b0b005091030400401d280c0e80c410a40a405950000100c1c0e0410080342c3c10000102188007000710728062541441c0002004200e4400d82da40041c40001440344c0c40c0c03410302 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 881532320 1250 881531070 881531081
    0x80f0105150111061f030501090c090f0e0c090a0e120702010e01030218190b0408060f0601030e0604061104150c1518060f060e0907030606050108010f150c12020f01 72
    0x1c6060108510100007074481c00110540c2c030801d454a0130000c3c2e03a610301449003040864002503c2ca5003010324200612200c07116490803a100c0c0e4104010390301d500e0b6201000c40f2039110f10038820342c01034040358000b89007151784560007800440001410b0034540b080c0d54900031030001c0c48160298042550b200350b40c0c0000e8503007107681080c2030039071918044813103840c4500040481240308062400c0b0b50b0079030b502907000d0380c00a0300c254100ba070703580c0340c560040940d20941111102040b410078000242d1039442070113113441400c0120000e0500340c40e5940c81c003000d0003602c000a440c10100b8040010824484d400d038400030700c469200c03c00065020b00300a00030403001040700d951242080c0c031092010203070b03103466036005420442c0041c580803540c80d0394024006691204140044640911401a40104100007181e2142e0710030004180d0718001910082030034803034010034043d81d4008100d506010001490f141c0401c0c0340c218481c003d40e039251440541404600c0d00141d00801c181c644141091145 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 881533570 1250 881532320 881532361
    0x1801080916031a10030c0b03130219030c0506071101050c0f0106030b040b0f0609130609050d090815071409030c190602010f020c0304051216030f03080105100c110a080f0105 76
    0x304132401c40d00c81d44205100c603c00d2038405500003001400c0620340702c00200a240d4000c000f07482051080742132014001881c00b040e40c010342034600015452600d9070885810729489a08a01a80d9070320005540307a4112a1584179180182d100300c2c40307500c800707116070005507120700322140041c00c0c54104941c9800c0300524400072100c10205118060740c400300217035480108094412544c90591602d200604813a100081c128460010342d0860181c210b40d3b980c05a0340d4840403150748444015400307031440c009444410200f1103461001940712140b20041c0482c0b0000341c200c41d0800240380201d8201c40c1d80780800c10240b6803202d8103010b00c582c28026403d0500c0c10001c20b5060415241d4016203910552040512030b4a1000794100305031000d0019542103825031202c41c81c2d45640e8200704100b035014541c11000245081e002081c145881d854441c1c1004580e611540303601d140340c0d201c8484d401410b4080d903000c1901c000000382e400e002c10110001e0b801d40301c0007281c9800c01141c03912401c0c00300b518 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 881534820 1250 881533570 881533591
    0x50d020403380f060607050f071502150f04021c060b010905011d1e030a0609051606210f1107050c030703080d05150409110102121801080916031a 64
    0x81c03186420585103001d94210b00c03c165000c44940720b80c00018894824181e000b042e07809590b144040240001c1602e904543e050a5038111041d500082280c4070492801d907601900c100b103021501c0080e4420500f94031600c094100300707010b914440740400c0781235160300885566480c3c0ea40a0000c0d60310000d030300020102070a01004038030320410008000340c204810380e03016810340b503400001d00c0d0018074442005c1c800501030f26040b081d00e042050140000e00700c262424883c28240e081c032101039925010071203e03256904201c04004d0030710001d080e0030007824228410340303c1c40c05540c080b40501c1070018103180120890780d166114a066803c114001d02c0203403094002c0780007000420060350486269401c03d040002e442d40c4ca0326002546400a4180c0e590081c0c40c00c00c1c0300042100b2031100d4900d04070240c08a881e1010440d110304483d10640003480107011110500b14169405101c0441d000a4520180c848807451845024000c01c80d5034426690500603030f0740c1212084440a00c142c100101ca134 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 881536070 1250 881534820 881534903
    0x31a1b0c031b07050109030f0f0b09060a0c021204092a12050901020c061303030603150501140f1311070b0a0207170c0703032a2307050a0b0307050d020403 68
    0x140086c10700003091001070889154848450304001c0507ca03646481544250a103485061600c03805035a000300b10307aa82031461030440300f01078082c00058070341082a884d6a40c94913250400761040c0242490310815100d11004d2005103d1000d20100750b0140011a80c1e140900006080050310a03250003404a003c10b0348100a42d22002d800030820f198084001c824400035041c035850100d00800c0640d1026004190100003a486009d881d0001c604035030300c20f8250b20651303500004201c02400410102d07648031010400e0a014a1001e410440c41d0003d104482e0703081ca412a1102200040c08850b01a03415900140440c02c016260912080c0413240500305401c0001800025558606501005d0140011982d40098107415190f640350300c808000e1001c2d143c03240a2800140c1d242640c0441903c0e400d612000e5640782c0303800614941210f0000300084852841c20b840080382c2c0d8400703804101084002c01070740c90f44099a00081004605c100d41200c0e5582d4800f81c1100014030003489060f0741d11404 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 881537320 1250 881536070 881536079
    0x12060612110304081b0708070305010b040509010c080a05100b040306200a0804020405100902120123011215170c03010f090f0201110c0a030c0e010807031a1b0c031b07 73
    0x1041d00c141c804120210020521142c41186c40c10b0004d0b40003d04078030503c4008800c20406401c4101905020f441c1030040d51034200d602420b0342c00b0b01000100013540040000c040341c1e541c1d0041e0f50041404120f01c07062903100c05203208141d0094105850403030710740c0159001300c94a003c1e0440c10000350702d030450a201644400a00a035000740c4064441e94403840800d0614104c014403d004000c411030455449151850040c002042445010300003400001641c540708200b115403c44800160340d22020302071003448480c004d022220400d0700345207881c00e012402d48441c50841d10903001d04401407003001d04440415007036035201640300350f40d1403c100a020000704d0012240c0400c40d4242000346410b41390403001440e10740c000003850307401034488500100b44500c17104200284c500e0840f11051b03680e01c4080b400d07030b00c00c5284030040c041c0c2c801000c044560a10b5810040d0068520340e68001d4000c4042031440c2a41c1181110704c00301d400008007604c0d9628041070f54056907003280c001c0c01c003640c41c1 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 881538570 1250 881537320 881537333
    0x216060e06070611040f030f12140d0906141305010f1b03020304030c062306030102030601020a0f05070503030a030b01030e07050f150c060106080615040f0b0a12060612110304 77
    0x151000200303004d0720780c901165455140020b0703501900720384400c410b202d0343e241868622100801401d4901d40001ca000328420340c4a10349156414178001126440c04998154050003801c0c580b005075180c0e0360b2050320541100e880c40c03041c3d00610f5400402d503049100307810a64215440c19888004051410035089902c02d04481c0c0402e5280b40b42c180184c403552a42402c0c0d8a80000440003800e8a29000c203643c43c40511140c1a03000d4451000c20b40860fa803800d05141c01c030320090f00c0e90703405688004040c00008004481215020f88180c0641e006a03581303001107459900702581c1c03800820b8580c040300b0030550f414400c10a650b0103141c000c010041ca804046a94034074a080814003900144190100740d8820100b25082070b91100f0840d00e0540c1c2d1454010041807003a42d606101e44040c040c3c42941c030780002c0c1642d040d1122620000401c40c03426418420a030301c210303104001d02c4002007130981382183c0703842510000c0c50941c448054002c200f54402045803800384010220240a00034000450341 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 881539820 1250 881538570 881538577
    0x10606020c0915030a06020c0706090b220e0c030402120d0807080903220e070c170918150a0504060b190302070803130b0c040602100c110d0216060e06 66
    0x8041e1a4950b950f26401210385240c0e03400c110860300b5220b484203000804c00c1590040000300b50203425552800c1d200c1904540d64103d6209200c407004042c000c4817400500d4480c01d041c003424450100548555802400034419001c0f10030b01c0740c00001208000c1942032101d800e84540d0030002c0034010482e80010040d10004015100c4c000300004400041d8842c1380030011100702c0b54030000d490b2600700f003d10305400c05a9444c000c0340901031001c4081002c050040c13207801c00266000c950003490054500d0074040316040000c88a0b80036400e00c3c000030500c50040a82400742c1078102040c0c603840100020300c00100300c160f014074010b524080c81004440c000c04240c0c1d200700000f0766207001d5500c0d00d8078120040e000c1c20101810090000041c8288003400121013410144100d01c0e50409035642d041d1184940510b1045d0070140e00300d80c1074404040b4142c2d110007004002d9003403080c0f0100080c030141d441e0111440c0e144002d1f034410890855010305115518008090307501d02041e84486000c0030951902 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 881541070 1250 881539820 881539843
    0x21e0d060e130b07180e010315020a050a030b0307052707140405010c05030405040e030c1002070314090d050609070501021605030706050c010207080f0403060f050f01051c060e01140901060602 84
    0xc03428004900131034450418482e000307007989941c0030b0f01034a901096001171000c0c4411102d0507540c003c15900140c46000352221034140303032100341c1007040129094001d482c040b070215505000740140400c041e07070b0340b452240700c45003440890052608581d82142c82004042d14440030310500900306420400c00a08603010341d800ae19007007401e00c0e824600640346000d0340d009a58000c0c203104007901d030703480d001000d0a10304c00084221032441a0202e00d480403442040406000160b040b0312601604d00f20500500301c04d080904810380060050700c90340d007440c40560352a0100c0c0c114000c10041503904024560000001088240c10703207140000180d5260868401c80051000101d008002c0c00000e6054035111504006090b680c0c2085284400c2c0c154041e001c200d9540749803809004054200b4440c441c80b0b00b8928600300d1140c0d0901e01040921160329601c040305180007800c2c98001440c03805001c0024032060000308014003003000780202c03094000d04142080c0c4c5400c408010003940041d0542151 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 881542320 1250 881541070 881541083
    0xe030d0f0f1512030228030206100807092a020708011a060301030b061f030b15070308010509180114070801081204060806060d0e0a020a081603060f021e0d060e13 71
    0x554549010303414000c0d946075201b1500d00400410340065403841c10b60000b94440e50a840d459594040040e440403200c0c0146040d6500c900e10a01031000980e011050b8002400e2074200342d1110540e2040d005c4603030070007900050b04203180400074032400340a40300700f00034822400000840c820000c18a10f000c14070024002d403d01d00040350b2584c50304100c10360030340700d00c0080c072006860b035540260251074030101c240e0107402c40b03d0f094016056030a0a585649515548860030380c3d183c10708011400c01c0c0541074000700d041107040304907121400d01ca034001503054141340001c1854201d001400100c0142d0001d103040e040340300e54061000c0101e0440f0b040d140141441c00300d9894440110f0781e40c1c012241c000204c41c0c90030300122109100056900d0502e80700701c0d0b02010700c0c3c0d210301c0c4840e01c07182200030480d09010401c00034030009490b501726480342141505e0042c14401d8860240a9181410380a98035130310002030310300b4108002d402945e0180480400034241c83c10481c440c290030700c13104800688403 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 881543570 1250 881542320 881542349
    0x903020f0f0607141507080403020a121b14010b0a06051c0207061416020c012138030102030609061306030c08010c17010302010c02010c05010e030d0f0f15 68
    0x850b514802a070f48104c0e04418001000550803080960b01c1401c0c41d0108900b050150000340310034454450f051189074998042c024107501c0d5900c19111003000200c0c003003408500100140c9507981803101501c1e050152140014034224090310030f0031110000c103c1805503403205c10a106142e044412188002c0c10034a10030740e1071001c99078a02c001e00448030010001703818081607404218404060301e029a40f07080404c4003110309104161390301c00c01405400c0c04200d0703054000e0381d001510f007241030800c7c0c0b050801080c4540345000b105144500d03080d60501803100185017010040e00c000043c402034105400031031950801400007a0904c9005100300d00c2848554406420300741160850301c011070340075682c46c0015840341716840c003270700f4420300c2140000c0740104464410034490202d60b0480e901a1900220b4a129030011035a04824200130381d2a50f48a490600d042d1004100500020224050000d2a10b55803004a0141e81c5a004800b201c0d0342420703118000300740c1141c1404100c0b090280c080c101c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 881544820 1250 881543570 881543599
    0xc01020c0304030b150406051c020d0f05061603022104080c01060306020913050103121419020a06060b09030607030c140d021908071704141f0c0903020f 67
    0x1a1103403580305012408045400410008000441800b411100c0e54a00030b2510312000d01c002c4805904c21250720054800103119041909403203c90014009010302a40d1200380e110340e190030ad052441119103034885020800004001100e000001000e4070b001d40c40c1150510904203041242a4070380342201000002c0350402031a441250302c050402e50080c442c3c55601d007400d400035004078a000c0d009114004103041c2c804418822213040e29881807014410711581e07441200c41000141002e0340303d090420401d5840e1030602505807001c1c68030350081040f1080c1b803510303900b5541640e0007007a17122000c2c0082c140315500480d42e01c0d40006241340000304840e0001c0101c400b10410b4408410010f40040c0180070205290018004495180c0100c4c42499407540101e070070101c101c800b000010341040400703845a081141d200c1d005801400780700f0102e034a039003200b070400c1103820b4000d10248900c620001071001c0e901982041c51020b092040481e0b1442c0c0124440003c84081a44a04004c604901 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 881546070 1250 881544820 881544823
    0xc1014031b07120908120403020307091d120a0e1f0c0507090606032a0912020307150e030616022d0111040306060b030c18040b0301051302090c04060f050c 68
    0x102c902d604a520540100c032140c0015000c00300501510300580100803429030f051000300211021a0350250040ca201e038074002c01c070320080a8150005011800b5485d207c5881c190070070004c1107400340100101e07a94048100050241141102c4046c0a4608141c081100007020001d0401d00f142c1408c01510050062420f0b50804855400c600c5d4400c0c9444400301d0340c680d260f80806580c0200340c014034040000040030000c400413040481c0b000861004040c007140420003c0f10096034406802c5407101500c0740c07104d41004851500000004411200e40b08092504002e01900001ca540b080484510412002500c075122101130102e50000c01d0b040ba080380840d803200200503d90b05000b00160000b0005840460380940720030b45205003440400704100005204a9004440c1441004c0c40c00c046000e000c0d800a11888a00364030680d6070500056584081c000c40c1e00c584212806200351004074410050907070f40241c00c8102d03801c018801131142c90340007201c1c281d10329500d09000b82c90b242c800d12100d = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 881547320 1250 881546070 881546077
    0x40608010e130605070c021215101a0a0c0503030406051e070f1b06050f180606010206130f12050310080303190213170d120e0a030e030a060e0c1014031b 67
    0x29002603074408d010b0351905010422403901c07802c540c0b58200c1516403180c80000e0a10741d015040d40004120038420000c2c11000060182e060181062500c003040c60716080c3c21500111800c1da81c1d80e07140d000f0044060580014100510000c10314902c2c03a0511540003848810021114418452500c0203040380401ca0f036a1700541030381c07055045c40a4500804c540d0b00c120803c4d01c060004044240c000c41c070f48180401d0307440c85128103a000b03101555414001c2c0590515040f03003554030300d000e408036802080c2d0a4058374028851070301d0b0341c0d6581c1017002c440b2420b500e0980c03050081d5007080c030500400d08501e00c3d0803807046c00203090260719250901540807511615511100e0402d02890245030389601c0440e110a168000e41c94040c070814900307010b00103a0360074030481c5446800461030380b00020b0046080d803410300c1024040710a0f4617040e660f800100c8000311807a60322603002280032511454807070b1190f01c2e81140d07454120549140c0b030800c000d240c08003800011040c0240c050820031580f10b4400d8 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 881548570 1250 881547320 881547323
    0x1030605040e0114060102031611040e011b1404031515050d1505070c030c0b040809030f0c0420040314010b090c0904060609120305030a150b040608010e130605070c 72
    0x8000039440207403094000c040c02040700703094841c03244c00036026600101c1690810006403c9000307031081c03036655403400c4012080c071442c1e1040d075600d114070807403100b4414010741104104005030a409810710140c4405260092114017040800044c000a01c0b0f91403508200e201c5404049020403017841c0f824403000316508520f4000f1020f0340b002c402e020050070704107452042e140040265850305182102c0035400750801078082030300440c01c9000642e101b034070b05a00c14050058103080c0750101c400607050005c07024141080380c0c401d810030340943c500351155414108402c20071107021030000c43e07401854061803001820190307921514040c2c584080d00f220040c442d009010072828544008820705a030014101c8600580c41c001c8041a040c0c05910202e0a0726900440d40080d0841a03508031990740c401400d903411203071601464803244a8002c244000380810081c0300f45ca44c1e04040c0000d00f034030030507440101c4d50313180b45042c0509078044650103840c3c03030b0301f01801155030f60b03807900c0c180c07403240c0441750 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 881549820 1250 881548570 881548579
    0x20a03170307120203220309080d111204062a17180d020f04020703020f0304090903020d0513090903180e10240c0201020a0c0e190e0c060901030605 65
    0x1034520002903400461040380103450b14080c2450841c1543c0480c00201c1e060040da03941c041540e9403080d6260065644140300c4d14011914540380d03070480d0305003c241d12181c00402c149035a5110412000d100101c0b80d140303d110081d003086c6c034240c0014a500c45a15465100f2050341c1400030000030703010740780040c080e00314240c030000540c2004c08003030035405011110034101d41c20401caa040e181c40501c2a0307106400070310740d05800c0b4400c82017000a43c0144021029886000640140c0007000e0015000400154100143e60b180d9820f0107420301808100142c2000420005181c612805400c0392058075850034002804441514083d100300403031441ca9411202510303400a03824410440e143c0c46030800c950007602e0580e54582c3c56206507400004940120070103811038044a111f101d1000c4000d005104440103c0c1c080c0c1c40748000007113075800c4814401a4081004003040c0f8011407090440385501d801c1100a940000280c0c4405080c04e029100c0c00c0c0014520b0b40747d0f8400c0d084040503160050 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 881551070 1250 881549820 881549843
    0xc060106180306060824070c020108130b1918080f1b03032505091e040b060a050a14030106171b0f0702040c0302090913080d090318080615040504020a03 67
    0xa031700303a64440d0402d01080850f00016440551502a0084540551196160380c40c0e0172080354010346404900030424542c074141d0500c2c41001c649c213100c04034015500e200c801c15103500c035180c071002980ca0120810340791103a0161014000340100d0202c818260b103424a06407102050744490245002c0c910391103000344070105c01e020080d0303140140008180341420210400b001c0c4600151060b016154660380d1203204c2c4468084030740e00410450322000c5005000103140c56141340010450740240402e20000b50001c11421132030b6420800c88004041183d00607070441d0702d0010000c000c010441d0384400c0710f101940100700c6103005800c010400c5400c01c50a0303911682820507901580d008883d06a10030307810f100302c120285000384212a0040805420084655660101c0d11149078071001c0071074145070100403862806c4114071443c10f0b05072081d0364074090030001c0d010301e610300303101c0f50000c8915030001d0f0103210010394035038903079049008280c2c1d0124255640c0e000155100d846548003902900885 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 881552320 1250 881551070 881551079
    0xa0806070c081305270108010510060c0501020d02030103140606011d10020a02060c0d03060f05010e150f04180506032d150c190903080906220b1804020c06010618030606 74
    0x17010409030001c0c5209a981c0581ea01c40c07186003a124151140300042003a40f00c10b201107403042e00018511401540054a000c3c0c4250001341264000d038402d44954a00e01c1000e0a1454180105da410802c00d00c0e01500880348041040041007040048611810313120312122405c60091101c08445500148429100d202c04002242c4540c0041078200020f442c041010400c15440e0000000b650810784d079240142d0001024064400625611103081a000b0310003040c40c10401001400580811103600c11840c8030b41e000041900c1004d802d6a02c40d4014010807601e1a1b555035640d07440b06240900e0360171400a4191842c02c1030b0141a00c0c1c030a2403100d03001c218031105440010000d01c24640100030f00b201d644a803c48003072004d400002c000510411400e1854a002805490b0080c00b620300e6401221600d42d50222441042e4415912440041404505415010306080100d5401e840035803902590341e03400398580e00c0500401d418448552451440000c02d100701002440d4407100800409495 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 881553570 1250 881552320 881552359
    0x3020307091d0a081305120307030f051b0a020f0f150a030b1f080f070203030403031505060c010b030d0516060e0c13060f0b0c0d0f0e100309020a0806070c081305 71
    0x40d005c0c000f00813403100081d142092040e9400d40990070000e1030504906507002c48002603800c15803020480180110881d4282c0c10aa0f0440c80c0d14480007009284443e1040c0300141a214072081c4c81408640718040795920760140d03c60756007004c403109540d07a05202c601a00180300c200095900442c0d502503001003a03c45000205c044401030301c1d180c01965450580c0440d110303040740c1d80b1006820078004070300003a009030840c00040303070030002c03041d203d940f5080403071916080b0005100c03050391945000107540c1001e004c40c4900e140c80b8540245030440c2000d003e0100202d1000003407004e0307038072154030000c81d4080c00b0300450400000c004000300c03951180c820b00500301c50702540d003c45a0788440040c010914104a600c4031011030042c0c28400744001d030035180381142c1021390003884241c480d07080650f0b880c240c06004020568400145406103401882640b42660300310044650001e418810f40ca50454001c0d00856400a0400d540d005210500404031a00340d00c203e030010707514015031080341003 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 881554820 1250 881553570 881553577
    0x18170d090c0314190809180f100807050f1207030602120a0b10090905070903060c090602010617070308071403071109090604350a0504150201050103020307091d0a08 72
    0x1901c0c2c8403c050303903040c10268031040c4020100d05800070701014030001031009805040203003402410f110404029104c9440c2040017154154013260000d400c00c03840f03468020ba04c0014142c0440100030260808001c12440c01181000c50307c40c04c0c40c48003c002e003090810103500030715400041036486919040f400d114000060720010300322800e1100d0960641000c00380e41c2c81d00c040741d66820008900d000006001480050701c1d00040110890002c40400d080d0f005643d00074010355211812289018402400c55089802451607100504010600400001244c02c25a50042e844070784c0c440321407a20001104003513030200c08501011442e4802e000c40c03103842c0080c0410503140d5200594401a071540c0320ba038115801090021003030002244030b010765030000f103a034003850340044001d034148013414107903004040590001400002c00340701c800312258102c102100c1c5e0380006d0200b5411680042c1d155141800380e9034040c3d0359a05620560700b104900200740c550208140e8001003ca414100c42c10391 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 881556070 1250 881554820 881554823
    0x30c03041526010905091908040603061a1b1903051e1c02030604020d0510050102160315091104090606030303050108030a0219020607020910081018170d090c03 70
    0x2c92290381840054040b00218901809502c125100d42c3c0c01d080081005200103003514130207215192659040380541041014602c0c018040c5076101c031301e00f0000400380e0301160485030300e600b441403000d0113003249902a0f88103042201c42005000b6004d440d01c0b440c20034030580800540d190140c1d004203064010b40204480100000c40015500400810840500c43e103600c2c020b1342040d90422000d03480300c035400b540e04200c0c001e1001d4980130700304051406840c825070300c090300103c41440411080d81c04000100d1807516550b42c3c44015450343d00d5201d00364028880344100241c84103078080810a001d29103480082000b481045510360609202e0300401c0715000480c0800c0c9080c00104568500000341c2e250081c4d2580102904403002c00c4002442c010b0a10480c0c001d4018012040169203001e0624070500110201e4a0b08600c0c01c1d242e00d2504003d641d02140c090300c1d09010640700802080c02a40750360704410542c4c40c991840d50005450320a404203e404a8940440d40741000410f182d0321007160f = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 881557320 1250 881556070 881556077
    0x905031617040905040629040f0f140f0f07020d0e010c080304050c01080a15260601080a030807030c171015110f010b090601200106061110110f0705030c030415 70
    0x526110358903103030703502071f649020001000c4030840502840e19400511039120b5079800452000307181d00c0010151079208155000c00100c160422500c0c04a02c41000d6001c2c0302071144000a0814980107034464200140d000100078134180107601a0340500c4010210a42c01a0702c981c4d2441c1500b05507841d00720085190b800149403d001c074840341c91500070415034030104a41c04141c24a4651100040d1005100e0b808035010008100600d422040c48018001d00001c5c0c090540c0c1511450002c002c80d000512035403d0601d050300c0f00910303903400b450b4400c1038040102104600d8642c00030b1881880182e62140c101c0c800039401c0c0000050f4000d8500703400c2c200000454040007072040c40b40d130036642d041c00b450340c00115850010b0141c0d031190f20110200200d0341d481d40c020712090a0394a0940d54503401050118140c1003d00410348020001c410300c071541c8400412001c5c8a00420101d6071107541d0304501c400001083c1071080c020140100c82c510607032902243d550b1966410400c5901c200310700340e900030 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 881558570 1250 881557320 881557331
    0x10031a010c052509060611160807090216050609010c020c040e0c09130606080307150c0207090b04060807080c03060c250f020405040f11010309050316170409050406 72
    0x5540640003415515602502500071030390f0700002d030003011000c0443c10220140e00031000582031a1031281002420403035564810142c0185982450b080290f51005103000702504100032001d0b01140034826161803290150399003c004d403402240202920700030b4524000d00d0305000162405511250260b0003907000e860100080500b000202c0c0c0486001c1c07440d1b0703002030110f0b0103a841d0846032982e005852000040003013109444907012500950131030040d075070000440c0000e101c0c5800e2074112480d000c04061103030030300b8010000d4660081d03110f20301b40c00e030326850800b40300d982e103030003c0300500b1000084030809030360317021415501c1c0b01c1558418064000c1f072010810a00444080794400240815452040643d01d02c003048811000070003610035a0b8184503010041c1d80781c0c0103060145000d0b1600c5c214640c4141046966100702401841c181468006c800001940101c1990701c1c0c800c41204c14007903c0c0050a20350540301c00b20129810f207510000303000c06c4089050303002d6400341d4000d1008000 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 881559820 1250 881558570 881558621
    0x1200c0f040c05070624060e010e1c060b0a15091509050d1101120501080609121e1e0703080901050a090c17070504020c0705030f010203130f0c051003 66
    0x100c0d1040d4041500203401001340c240459659041714140944400300f210900203086402e11904000d42c224000090b1107196200441d0390202440d661800101d40d00100d43e00b12400c03c85a920000d030300100070640b181203080059540400d100d0081c03203007003040d10150044200082145405024603004854410607103562a03219410800a0300c3c0041d0000226282ca6200c1c0328112141008217070401c0030054002000000b00e0003914000c100c80070080556051202e0420304000c1c0b0304040c02900f642c00d020f040b103c420841c0b1401c02903c01d00308170f943d8a0bc030503c1b06603094484104150a01040002c1e1a410142c1c060345140c800c0d41141c00811003611400340d075a0503103100c40c40140c045441d1040600c0100e00094417600001c0c00442210b001c0c40e51200420300b40e801806001d072480c0c10800701040142018405410000d1487c8001c51451808d035101c0c500580c000c030806480c0b400084d0f110010012143e141c0c0001c0e0000404440e50000b40c0f04000300a890300454403020040f1310513040c01c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 881561070 1250 881559820 881559829
    0xf030709150e0f06130207020607120f08271018150905061501030917090a08060615091201020d020310120b060f0d0b0a02130806160e01200c0f 63
    0xa014103560583c83c0c8494a842c0c00704001c21940f4081c04a0640d8204200c00060762414003c0445510500c018180c142a0b40c10240c1540c40310502d1809020f01d001c01c0200081ca859002e0103042c048060000700000c488bc03606203046e0310a0b0120300075625200c0a42c00d109000300011031484e214101c1241e821603240414800c3c3c502d80c0c0801000c0d94450400710321113446950480c618640c040c1741c005400041c1e40c4924001e05200041141c0e10440010302c0f400508200c0640c00190015100400a80c03d0260210310000c100030845020768a000c14440b81c190707100b000c0e8600c03504e0100000d54403034980c8580440250b0065401e00220100304400003903003000303c0649440681c20003031201c0306a4410707060042d1a80a038031050303449400c201b4160b001845031032000d4080d200074400140c46040010011101d948a0713080a00c5540c006070406c4030882c003960a52140210f81d10708801d1071900c060060380c02e0780c84070755075031307190401150700e00090f04001a402da00d040b812904ad900b035082c00414030 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 881562320 1250 881561070 881561099
    0x50108011d07050636030c010c02010212070c0312050c1011030a05090102130314060105010206101505040504050408070b0703180f02030c0d1407140a140f03070915 72
    0x10800d07001603504109604d00b01c4040e00d00c2090f040c4030312a240e80340920302c5011494400b61081c2c3d0003140b154480c26400c0c00c101c1840410005c0c289694820b1881d00040e542d00311030040e41e02d4000002501401700b10040320207070000c1d60b21007a0755805001051020b48160024400d04d101407040154144050802d130040f90b80444c000a084c904c1c41c0c031340f400c44c04c000d040e00904c50302d00c96400300703e8101610400c1c0c0c08400194000c104140e00f0a1141031040c3c10681d043e400641194030803014001c075007079480081c404075054000902c40e200440a01038a6500a560050b5401450441000b0a01c00144014070200384620a0411181e880b10300c142d041f651a078a215030801210401000020803815000c000d082c0001d044550a074059030001d0458000301504950550406179480440b10040018a0141091504103025194001d000c103030151060300c502c0c0c8401824020f08019622150448502c0b0348018007590152501d0355204d102511003010519070400580c24002000c03003404a68 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 881563570 1250 881562320 881562371
    0x903031902160b0d05091510170105010e13110a0e010509070206070906050a02010f090f020a14030a020907180609300227100914060a15090b0c0105010801 68
    0x800381404140413400000781801000c03000f151085400c00081104010b80382481400e043c0502c3c854035040103210500700c108a401d079505a030400c001442508d070040209603101041e000714414150070703070410051154030281d00301d8110160300404a9200c080c1c04100f81a04c2007a10a000f407500e4040f0122780d10142200d0010001c1d10b0f5580c00e104062198004000c41c203000d01c000b01c0c90f150201d41c82401c90310540804c0f20364910710a549000c504140031407800030607400101c071b0000000354000c00d448200d02c0f00d00a210b40c1d00c0e44d0019041d5801a00031071150313840d0300d00410350241c6903140944006454040c2010f07000000d0802418251000600d541c44810344100382d29505c999402d0102d69102c9540a02008a1041c002d00c8100b0070b82164074410074030590140541e618090307078081100d601c6201e0350405510041085207a841d5440f10b14222418030f19084031b0040d41034000c0307609203139076003080816502c00030324a11405015007105040c0c0e119400204000f1003010111034103a150300b4007 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 881564820 1250 881563570 881563589
    0x105150306030d12140a0b040b1203090f06120403020a1b05060904020c030c0f0a0b011202011d042702040615080426040801091203060503030d11090303190216 70
    0x2485040140f05000c00d0b048001344400108420b4403113103030039040d20300c1240c520b4a800d940350f0b40e0f500d49242c24000c0c40346100007960400c2e18002900401d548a205030142107000b40712511549075a40c64070301c01ca0f203c0c4050480c0010603403c1c249802900c850000c9400c1e40e1454441d086105000800894503007280d6008001341c0c40c0c1044803051202940000240107403500044c841d000f543d040521140603c0c00b00340000d2703c00880145031100306c61506801c4070000745c505441c800c0040c0d0700320340c011400c407210182400c13081403628005030240401003060030031070004807201c0e20b44644141403070200314800c0740d003031082c50341b2615104072401c912901d46001030340401c04240403500c46a003501c010a11078034240110341201c008410607902c2503000c115075a545108200038448481c5001704100490300d0144112480c01000a6a9016001c641c0a606548110702d06541001c0c0b8202d80c1c1d20702020b0156600c880d40f400c401500c1c02c00080d00d2101500465001003c800700f00c2c03459600b5543c8191 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 881566070 1250 881564820 881564833
    0x3070e0a0927082505060a05100504021602101110020a0c1527030f0e0a060e0604090f022503050315031504060e1b0303030c03040206190305010515030603 68
    0xb821521500e80081054800000801a080c19003480054134802d20403450380c5000f903000c0078035216180410003010701129525040600c9441081040780c4002c0718404c4030090785605a80035520010103030074030000e500044089030401a2504130801c840b08412110503500d425540c0e4140005a114045074000000e28001c402d50000344800c2501c42c501010610001e24410300180504829030300148d403007001080c101c001c50070582e009030820822101440d08031030020100011070400d800b00e00445c0c0c28000141c0e041c681503126a800d80f00240031407401840200c1d0784094010080d07000001e452340a64900c00941050a404162075100d56030581e40c8506d169541d220024003403495410240d814000d00c0610980e2054014109014a001d10000603050512118840c9024804010203007070001c9680c041a0399940482942e9100301d440700425500d9890b440014042c5c819012000c00761000d06a031b81d09020f926a000701d046c2c1d007080e10395500040e2000500c031a580802c0b103015a0651110 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 881567320 1250 881566070 881566121
    0x70f080c07031407060e03070b0703231b0313060e03040f0b0a0512040606140f030601030b0a02220303021219230c1c08010e0c0c1203070e0a09 63
    0x180e1440b6261201d03002140d06081300e5a0756030b030503585815280b0b101584003042071001e01c0003078040750303410200d6400c08111350501680804102540b04c414002000f4144002440409448a4500102c40594040b950b64507010444107505501c441007a96040c0ca04205120030043c000111000d440000050292a52414500f0002988100801c1e000c201c400d203d04102c5a810b42d01d00c5003c2d910503134001c220942006c208580721000345001038415003100c03230040e2250300c000c03070600d042d6608004204213590792840000040c0c8560880880314400300c481178068140a0004074054038801e6080e1448902c980c401c02d041c0340103500e0418100e40035259440000d40c040c42d2000f0400300c45000a500c40f00c11898103403620b0f002a03039a10030541004407100d10400150410102c91070785420501215414030913542c00842000700042100c150014481e445c0c14420800c01001941c0343c41d0856072031070441c2c3d001308020300e404001801031902d04070120300346c5001d006400c1d694251072880400301101 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 881568570 1250 881567320 881567327
    0x60c0a0909020c071203030e010c030b1c0c0503030a0c1707020f040b1801171504110d0f02091e16080a1104050306040b16030504050616020f06010e070f080c0703 71
    0x41d9035491030342c425001d00051828001c917484c000039000707443c0012800788010302c09081d01c0d080900c4604151811594100d9030351030140c00720050348260020a030041580c0f81041c2c000c54241c004c1a851300c000318112070300503030040c1c0e21b40075103205e04a841c4080d10443e0001402c1e00805c14001d40c80200e015861420382031a41c82071000682c014104000c4600381141c0d001c94801c01e802c20302c4a0041c02c20100d03a40e0404010380c000010030807000781c0c2680b401e40c42d07006511071014400d0348929400070700310703003413007141c0190041081d001010b900c0c9a0038103820f0b0008181d2003030700005640040f0f000048071449112070070644401c0c81d071039031030311903481d000c0034801411003810000303a0300300c2404041086d890402180b807090780301d40301040017170819201c4400c084070600042810182040c04102c000b800c0031600c96040b900200e14081e6120540100340c0c10040310a0381c0106910500b070000030400303070502041d130064909480c1c0b154882c5400008517900101150411542d0074101300050008c1e21 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 881569820 1250 881568570 881568577
    0x9060e0f220908090f0a03111908031602010807020d1403100306060f0602060c03010b04090218060a020114090109080306130603050a06050f010e130303090c081e060c0a090902 77
    0x50140e807608002002001c12044940021003900d00c1c00c0b02103210b4401d410325a40003000c1d2001191440d12451559642081800300c07800c0040c010240b1400412001d09256407600107081180700380c030340383c3d20101c40c908035601c40000283c7c000f605160224a06a002041031040040c4a07610900020f19160341c00c15190300c0940051904041d0b03401c00408601070388a0040503152802100c400d40f441c14200a01d0514080c01c0daa404a600b0030042004d00c07201d00403102191f5181e800540c4652118141c0072000c0070040c00e10340c00c01d000055003000c0c00c0c2e065000c4100380302d0110300024241ca410b06450700722202c0700b030020440381c030400200c2c0c0907142803100b009410700c9130b2001045007601c944d1441d0603c52800d508665613621070003072201c0002030150503400b5015803003810000c0c0c03500900c40c011661140744041d00b03056031a0542c00900c5803507802c3c8805050110101c0b03905030801603c070421303040e40030a03022080c065240440c3d03d08441c2d5048640042865440c400c1090910803400025070 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 881571070 1250 881569820 881569849
    0x90807200d050c0d11030f0304090c0306182007050f010f0e0a02010c020613030c06110c1c14030c0d030e010510030206162003211e0c070b070309060e0f 67
    0x160348031007035170641da8100050203413008000d000d10b4603a4903000c1c1d20000d607400d4607218014141084400d0150511202074402e03200070000022445080141c8003e05480004102151540c00083d4850a105000404002d4503074541c008108030041c000310305044400000400303486070049410a8050343c45010594078240c00141440c1c5030103c0040b54259000003a8000c503000385d600c0108120554024001240c19096100640780040745440080c008440d1700d02507200f55500c04400c0c1040c0722003400803c0549460104981d618006070b14601e0340c1e0724a40342d204002908281140140c44818042c4d5406495510201080e09085600b0001c140d0405030450281100780990b41d008920111075451150141d040e503030031510b100e10141818124801c80c1000108101040440f4002065040790003d1130200943c0c840310100200210441c41088a58400b1740306000010504c0c07040c5400900345540b1945030b00e0541d640d035100a0740c179202c1d680301903131740100710550700105401d151505000c0e05 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 881572320 1250 881571070 881571083
    0x6060302071e1e1a090601030b1003030807050c0a050d02070f091401060e0102161d130c051e0a030818150f13032001021608060408090301090807200d050c0d 69
    0x350f80135042c40d221071802c81e820740150b40300000420521040e02c10f8190400e504219020801d4110b4070090324804000d41450108200010781240d007a01c14001c4000042d0300c9002d49000c20303e1800004c1d0380e1200da02074502441314408000806440383c0c82441164160003c1034400c5030f20740b0b041503528865628203941903004440c410884e21980d1100e20001d809035804520f8881000d1702902c5038004c005062580c41a40d8040c2000801e19204104044030030407240c0c282e100100b080d80b40ca80c081491a1f4540151041030040100841e440251180e1020080c0c00c152144410702000200200440404071403401000b840048a91907001403060030340c001090094180d4a544103c2d0340380c0340c8070b2148201c29102220b11130350340c0d0500800e250607900035507006001342440042d03601c80f00702038801440d9900010b802102c80e2001e421610950b85c0250000780c4984c041c6c1020281e401c54441c0e1400503807429441c0d40c1e05d52500085400c64146c100008025032002c403401c2c050f07600003184060b40d04 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 881573570 1250 881572320 881572343
    0x150f03031e020102160b0108190201121d030705030301080f0a1203020a1b050a0203120322021f05030403030c0801060f030f09170c010b030c010206161206060302071e1e 74
    0x4202c980381881d0717250380c86440544010340c50f2a01d402c2c14004009003008886088030410341c01f5070f901094042c50303e1905c02c0001400030108640d034100000111070003000340004641d140a00002001440c103c840e0102a10400a110740e000e90300ca00281c20000c1a690312040d40c0c40e0b0b0700780301c1c0c3d02402c4001803a0800d4000380840182070320080b200d0380b0701200d140c0d00c9400c51070708501301030100b188061524820300d030540c00c165403280860080805014220300121451006641e1031000351406011800d261144640e5070801c0100745900444050b0701083c00c0600c0b142c450b500c2075801c2030480b202990762a901f850060b40031409080d072500e02e0340032181ca880101d008184504841828010501545c9503107401c1c00784d0380c40c25550340c003205038032a400c501d01d04201640c0114003554801005200071011020503003090700d03901303c030000e240c007807900d01080812680c1d090b9006003080f500400b08844400140001341440c0e40000300018400c104200c5c0c41a06440c01440a041551050340044c1e01e = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 881574820 1250 881573570 881573587
    0x20d080309030705070f0501030b04050105130b041d06041a0f0a0b120d03020d1505090402100207150c030306090209030703060b1203120a050106020f120318030d150f03031e020102 79
    0x385c0840d80c1c124500c10040d8400402c140e40e014402c0002c2e0860548040c0010361405002a0850187c60601e107091a181c10810b010350b60b890707212200444040704d214030b80d00c0710b00c5103441d51084100d074125444403c03003000e510014003030000f0b60b208003266040400d0640d6000052409030004180f0350344c015080031607201c03081c80c0c10f000000315040a03640c0142c951198011450580f00d04d4918085001c400260a002503203400c0074141c0d125405845108490751810740803807800320160b101c000321383c110b4420821442d50041021000c40d0203540d09100c1aa01c4005000c2244212000281d041d03104046c2000018100d400c04c14010100401c00000c1c0d0184214817400d42d408499543d0140d10780000300044000c1c81e00c0340380d002d4901e92008020312000070341c10965078061001002c40502011001030100c003c4e0442c0301e58520401030582e602c695403044504040d00c40d42c07440d0300c2c018100b83c002007a030030601c1051000302c81d00740c0d4444031b84043c01c1e0b0400c003050248000410855408011568 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 881576070 1250 881574820 881574823
    0xf06070b0717060a0501020c100e03070f03060f0204080a1401110d020918010503060c0c0c1503240d060f02040b19030605101e021c050d0501080703020d080309030705 73
    0x900c1101d898031070340302d0222407030199000944010411072240c2d01101041c003c0ea44c2c001490314056006075441540d140300020140c03814001251450340c54866250040340045c41c11404000b104e11408040c4119a050300304041a40968060004680e018580400c00705212040c0d112803c00c1100000130b001e105090850b14940c4010302c544240c03030300002d40c0070540c1809000d8000b400d04114018015504050020b0740b1317840080d11044003804007180e007200c8040c09200c0f048403150020b256220020003e000c41245810854804510769003540d403250f130046010480b0b240101009000c200418020750346c2d10024009010036201440c0c1c244400305919640d800203065030313440f0707207c0b1030b004801040004081c1d401c3c0f5005035001b100b030889030020254010b6003c994034a002d814982c01807910000491915100d41d0400034508008100d400c601a0040003d0494007244401800a80e80f5003803030355982c10441c4030003500052548420808a0703040c0000c1c1d41c0002841041c1c0b8a0030f4015210740307 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 881577320 1250 881576070 881576093
    0x7031107170c0306010605090112020405102c090105210a0b0402240f0c0102130306050604060611030d0203130c0602010c0305150d0204020c0a0602072d050c0f0607 72
    0x8050600d0080a41040403070800003554120001c03401440190b0414000419a01070154201e050094803c2c02d1014041c0c160180c6025203409040321248a401c004001d0110f100c15071070146050302e000f41028005d50741c020003200210090284405a440c0c58140240642e81c3d084862500c2866171155030300383e08c24001049103500402d03210040d41407600400070004a020b0280d608448003441100b148807140040c1c640400b08840b1042c1c4070651074010781d0280c81071151400c1282d2010b03001000300440c030b9004501502056808000850b210541034501080311400310946a005002c6ca00058005400030356020440c4c1489201100569407480b46e4200d40c0c0d0001350140c0d468019400e4807952610902d0741c05100d641d1441807404044010074040300c4a0304000c0c0c080c030b4000800c207030905010080d00704070b2a40204115503031503850034030045d003100000c1030481a40c50400b0000569200c4d414200103140c00c0005032900710040b100b08500710400c0b81880303412401c207000b0300d4049080c04001 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 881578570 1250 881577320 881577329
    0xe04020711011d03060907080c030d211d010906110a02030702060903010603021201020a17040b1611030f0c010c02060c1c090f03020f070509091209040b0303041706011d0c07031107 79
    0x801e030150902074042d041c003a44c40c040034044d0f2f000b1140c2d0048594403480c44c0d8011907840380110b0706017245072241c00140c0810136141c640d0070802e401c80448808158010903003603008120400243e003101c02096100d2003a0041080180e0041c031540700545070103401131428040040001858035031303039400b007100780a40038004107080c2d50103d18078440ca504040d241100007480c0c1011910b51030a55a507824460300036104903520720500486030000d60049003080e200d54201d804031303030f112034003106c10f210305511610300103143d542029400103805000045841c091642c2100c01414001c0d100c4c2010300300c440006820020a8641c054a4003140e60282400790701400b0303034040d2001e00c5039410a9031405c0c0413503022901860b10701c01003188030200416134100480302031480999074150040060003078414644c4055040c0000240010000c01c90311142095000990a0382c515a0340c81c50402e820039003100b80310f401c0000801c00203030348483c500010b100c1d162081c10b10800c3c804055900c1482c10403150003 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 881579820 1250 881578570 881578573
    0x20c090114010324030c0f050a030206120a06170c1801120f0303020706050f0f10061407290108191e230c03101e05071b0c060e04020711011d030609 65
    0xa09107c0820440d00400c080c040075952804620300d5035010500c54454000f40d02c80c410380c030002241d140031450b00304200506c18498010310300030fa40401180c903007041d0716900d4440c00c40a0400b0075410040c0c09410704868481001c41803054dc01e864490181c0d0440d0390403020540d0820170000003446070304c00c0d0342c05101080345544052400c0c1035080700004014140030119071086208102081e4002e03103806603230036040c4d038094441c0954940000c1c0328061105038100000403880400480030f89131000c9040311b408408480501001c14040340040b608800041d110582c3e0f54124060401076114044885101701481070710000c001404a0082c024010a00d08640044d01c0310100d03442c0400c0400c00e02d0140ea83c0810100d0004008600203030401c0c030301e0340c10f0350303444200045515001c0d4840c007102a445484054103946685403000054070140a61808150f145030f901c5502d04252095071500da612482c0024641401001920544184050441c6050401011a055460034440140240310380c00 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 881581070 1250 881579820 881579843
    0x3030c0f060a0608030c0d18050901090b36150d140705010e013c0f1409010f11030405030d0215010506030c0d020c0a020901080d020c09011401032403 66
    0x2411802680c905500c0190290300c04c1c0300d500c1070521b02154442c815201420000180181507140178031052942c0e0049034880310203000041d04070599006480d101c401183d541200e1819104130815000d02a0800004141964040002c1d0800d010480c0c1d0402d00071040038480c80c0c905c00000b5604143e4031700c2240e00601d03840348001480401c1184602404003400e091102943c6100002c0943e0140640b000c8d0030300141c0c030130391908000282c1c0305402d07600303903c0d000c140c9150740e900181c21864034074545400682680600806104007009840500c01b050395100810701d07245104444581c0d401c415001c250104200c0050942d900b04480c04d1616a50340145c17038001c40f02c0f0885a0b110b4030591044d07014030420010802410113903400c0b103101e504064001a107400c9007682203440c02c11070b904002e4004592600204603101c00103003a800c40400c5608494840b40203005100e6400020f00c118200410035094180c023940c003a400c14024000d0b203100c1d10328220781030022281c01200070346c82a1220017942 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 881582320 1250 881581070 881581081
    0x2030a020d020f03160f0204020a05122d09070f15080105150910030603081c0b1012200a0f021009050a060903170a06090f050f1503030c0f06 62
    0x140300e9801807411034000743c0401244810199224890b9a4031380302103001c84030302c10003044221407015a107682c014104540711082c080f0050080d6200c640300c0400440c194000551034142d1030030903020401e011242001180020341c0d11080c209010f08441414042e4081c042800c01100d10440300800b81d80301070550400b0540405413650b501a00018050390104001303002034002901194420102035031603042551203081e00320000d04041c1c0006010503800550841d0b602420300124504c1070880c0010451540c00740d0070000000c201c40b16140100e2009194440100c103280e0240d881108100c0d06059a0160b040400e0a258450b00089010800c800640d400d625410030602641a82c0c04404005401d020740300d81d55158540c0a0003003400c5d4443c220f07881010310400c07001070411111044000141025034401c0081d2442e40030b0486142d15040707503100000c406010700360090325041903c0d0490344031050803104241f060841240c041c44104060754a03207000308144e080e00070000c0c0251820b42000d = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 881583570 1250 881582320 881582323
    0x6030305121509040b0618040b011a0d020c011d0a030c121704050d321308010207030c0b0c130512150702073f03020c060c01050f0906041e030504090c02030a02 70
    0x1f240034800f2110700b03c080100040342c40300e907141911000411070700e8100309030003080c03114031941c0200c0c0006400401c001840c00f005420041c800551003050f5140c103080c030f81d8455580e0190300806030000d146003c50a000c14040400c0c40c407202c0c0c01c0d240c40c203000c070b8585000130440328041e54112803e90003030f060f0040c6581e0104075541e48500a40108049541c103181d2002d84941e0914085002d000001d4800c84007041d01c0355507002401040c00075911005c05003405008100e581c0c40981e00f0081e14000030f41c03600902421100101ca01c01d500301511400d020030f20000e5041c401c1091800e100c2d410381e180d0911601d00b2140d108980b1580105411820300110300790050408910005c61084c442c602c0b9145500074070302e294a294403045800c20400f21381001c9242c5400e441880d9000b400014103815010f5064200d544503407480101040c80342c954950a41e0303140702c01c8a01418942c2c0311030204c1c5030160071480c103900700c9000785403c80c102900c546e11031084544180290000d80e1000035488601c1d82c0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 881584820 1250 881583570 881583589
    0x213030b0c12040605060a032321040b03090114010b03090d020a0c270f06080601080d0f1d03010f0207030305150a170307120503041506030305121509040b06 69
    0x5030800340780c0c10010b220b60701d05001d190180005121507141d90025182e81c960300200c000443d00104013003441c0c2c0d41c80c1e1142092102c86030441c000b60080c241d445d40c000568040c0c142341d5004407944280341919003158104950009460304059540b07a00442d00d070f80710140a110b01806d11865803603501d080c0860f00501e41408954107005540016a01802003070302100d012013100c4603e000c0c0390154031640400c007800694640480d1040d4076100f40104044c40d00c1d80b10800340d03184442120180e0344c0b12045150307100c22840800c0005418409400001403141002e00e040b05662007031054508000d60009095801400004410540c04110a4240750b81030140d543c01103c1c0494000803445040045428564640a00015440740c03100c1420148010812217034415000584000c8003d070104000b0180e5200b590300ba00c2d0000c280088410b8808107100e104112945a120585082d032011214103200d070008021107545802050314a801d52210320980384584d10880900b004c40c900203042002d03416 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 881586070 1250 881584820 881584831
    0x30106051b3909062e020d0905030705060d020c070317090a0b361305060a0806010b0a030c0c1a0a061e120203010b030d020c030d0516030e130213030b 66
    0x2e030b01003440d411500c45000b00d9402c16000da50030020360f80c4200151504591070441c0c104501c407401e200001c05a03000c503881400740c5065940c4040b07242d0714010140e49030458003e551780079008104004192043e40d004040c2c080d00c45c8183c3e05070596070780307078038501c0c8402448000b42c012000846070603501d007040d010b401400d8803006203414074032501011081003142c0200d01c4000aa480e00c1c1a00e0000c500c50070110680300106407088503141e07200c00700c000d05420390314203000300d480310404a402c0201190355416600c403030768a0741c109137000c00100d024142403e1540c0502c6060030700381c40420f108082031f6241c220700d5207440c503240c20144a2003040f18055030280020205111610000b0342c178000e264402c0b28171010720400e80341242e000203401440420070240d030501c40c149150742216000b28658800502c201c00360740c282045400c050390317a480358a0070524080c4003445240d00007405004842001140640304d41200c6501c80d003003000701d034841484494650300c03140f410801c0010b440c040c40d42c0301 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 881587320 1250 881586070 881586163
    0xd050c010b0922020604050d05100506040e0303150a0302100e0a090b010f08061810080c0306070c140106080f0a0606150804081c0c1e090b030106051b 66
    0x280740640c0f01607080e0035811030450320518180307801c50540d0b0b901c00c00d440103000010400001803005150450352380c2c003455101c441c56410000041c403186454803980c00510340c440040e41c41c0d651011800c2c480c6021000030707598015a910004805a00c900c55011402d0b0011344841501c42c0c40389080204003145a80450061070415001c18426640040030041078041c0d410302c0c0700f694540d10700151522002820b56507101e801041048002d64140c0c06d514200c41d407200a98840c401103906041d1155801c030303107800202e003242c0302540015411054540c02d8180748800050a66100c0880c030381001580b000c195400d03401944410103000142c45a500200103501c104024050141000f41c0100001800644081d5010803822105500340c41c0c4a189020040010040a000b40c200541500b840015410344081c0200060040c1c41c002d07400703030040d1149008040c0c11070f0302e480c40890b419400240c03443c04484015228081c0420100801188074204401c0b02c0d07441d0350814aa012109a011442d5914 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 881588570 1250 881587320 881587339
    0xc0e0a0803041a2710140403150e0703030305010510030510051c0b0103080403060b0301181205130b071a160f0c0506070c0506060a18050403110d050c010b 68
    0x200e6900204560883c0c03202500040a881d510074080400d01504415034038804000040203011448148040304520049450b540001d030f05481c1100ea2280201c0151041401000240042500c0200c1d0b8148000542ca003c07842044d0802090b090444580c41140401d44801c018001407511a410380b4443d20b051a04102620b04010500c08980c2c031803040e0380c00b5500040000045a2801090f03c1c0b2590b00007182100a5943e880d28040a40c05072006450803443c0180b007003402d25060151100903001c0c1c44900c07880f0041521183c528260301d000100c10311004100340e41000c1d21014100c4010122588110f4498455040104410601c850484040603081c0f00b0010752050001101c00700d80e44030700d00394080f03c600c0e040c142c50040c42250050403520070081040200750b84203400103541845101a1000b07070316403100303000c9002024007620200c0242c8001c4116880e410342d0201e0f6005009150450440303e003080e8090038184400303031240000b0300000311180044401d000c0d4554240c41914640702c2d = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 881589820 1250 881588570 881588579
    0x60f1b03051b270307060e0f0f09040b070905100e12070503190c030b0f1503060108030703030e0111071a010e0c0304030c1b060207032006090907030216060c0e0a 71
    0x182d5124080695005540c030541c0b1020000390710b000081c030800040c04680c41c0b01c1d00e9480c064114a45603c2852040c1051220b8261a0400d0021218082d80290081e21252100c0c0e84402c0d141d44014204010410445800141d59403000c0e548004240c017900e840d418104000180310800400c9130307107425641d0160400b00f1160314001040d40e2071080400310701c84e1a8030b50345800e000c5801194006800c605182c4107001ba4040c03d00403040c000c040c1e094020710308003c030005140e2035440920034050590401e210460100e4042c1c1c01c0400c0600203100000b50114086426800d070b600150000d03905622044022006495000021409460a0f0960301c440f441e200e2315140ca107120040004080042c41180b8404000d01403250030303840c40003440d0083c4a903450f40d000039610195480143c6094290007490b5a061401c0c0708100c480781005000c0b145490000c1082c4101008007902d84420550700b007101c1e00340314003a28800400c241c41240003149201040b00010480003e40c4e00d81d41c46800355440400 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 881591070 1250 881589820 881589871
    0xa030f1112010e180a0b060310110f0c0a0606090b1e0a03030c11092e2907320c010e040506120610150507030219060f1b0305 55
    0x90468410780180e000c913a44090081c21a401d0943e00104184074054540c0c040007080c120032442040c00707a0889000c82510012103040e91b004820710301300800e041000403441c16084000f000401014011a140c80c0c10341d036211021600141d0207a00c0b001e5481035a20201d2070007180300200842c14482c40102500d09000107400790095100040512003442c0b0100d081000011089151b5240288912068038141c0c203000047c034203550b0500e110000b4103010900a03e0010b1030b0b08103031181021001e103154081d0100403213081c0c1e00c0b00002e24100c0c0078000030000400b40c141303000c1c800c65441c41d003e04142038000340100030403030081121119004040e00d0f85150f603105005c01c3c28840100c601203060f480364404514158030303410703440c45103000b000108240752942c0c040780b1003161004481c0801581507114111001d014000d00140181c0280c0102002c4528462251001500842d80082d103828844101c0044504056018441c4d00d0988980b11843d81c144c4119540410141f010795030000c642001d01 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 881592320 1250 881591070 881591107
    0x161d01050d0201090803030406050f06180117031209070311010305060102031c110409051801090b07030e19061406010207050d02150d110309240411040b060a030f11 72
    0x360700a110100d515010b40e84111000d00c02000c00c501039a5032418103050440192204031000c11031070080c10301180d0a03040450342c400c03810600c030788402443e07400c2c65492034440d20039600094a40c401071200c010b4040600030b1403405078403d103005080f80c3d4907603d00840c40c181541c0800b4140751804080020070398010045810002d280036145850110080f5084010584000004480540810041904080e6501071801000000102c514850030b40e03100d6400c1e66421a002002d50401c000402c0c0e01341d002e80c002003403411001040e21401c0190b40807010210003003c40a80341141c4540c0c2020461950388401a00204203202401d01c2600702400310b0302c42c8a9242c4000e01501c2c030310821074803008010701074590103200110248400b80d15000500f00390740007995400d40030700685000610f08114000340c3c0840802c421040b95450b40d403a01c83d00c02c80101000d1264021791200040140c5658110041ca503000054070000b0328481c5a80550088454016100e81441800c00c1005900389000c00741 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 881593570 1250 881592320 881592329
    0x6060905220f0b011803030c0b10050916080f0c180406081203061201020307082e060206090d0309020d020d0201090e040606060311071218030c08161d01 67
    0xa5241030a03210119101072100384262440c1d40345042155581d40340c150b08400b140d41000d070f955002c1480145010254a80b41c2d12006000c01d0503983c0000008086041650740710540800380312140383e586000c990090310440d41404000841c004060070305410007070803600444000240315141c03130039001d00c00e818491032104400b070148901600c0003d54035038104a020300740700c005031240103255055018150b002500c0c0c59100e49907400c0e005994410501c00e591007903000d07668108540d110741014140b007411900464136a40b03180f0200c840000031401c2d00030028140760303000b010b2900d030a0138a507040c10111440e0000701410060020096901e41030040c041c1d940403203200b461400304d0310068515801d1903200304034001d0208200428060260b01120840e6400c4e10b0074000018100d0f007041d42c1c1c2c0b042200089c8241d018000b0082000e01c40c500b5810311841180c0408545a00c1c0c0d15801124015503025152942c40084810460146540300301c0080c00310303800c4090400046550b048001105005 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 881594820 1250 881593570 881593579
    0xe280f080c03071401050402120a0b070305061f08040c050a060206010512210414010512150a090914070605090a030605090102040b0703051306090b04030609020d300306060905 77
    0x34071a4500e075050048803542580203410740c81580100a105002c1d010440d4168426086000341500380c4402084082800798820005100307959451010b41c010200075002d0390708a96140b151803000c4d20740700c006941075000c1d5200d00d8640e00d41407600c13851030440c60300300e00d016000c00f1000b0000d49400042d400d055410450704e040a6035000c190036443c01140d5100030041c003a62115601075072100710028400d03200c007075007064800e4840d01d005551521881c11640c40d08060140007483c404c54102c00c1482003c0b0081c40c924201e680c0c1c030840c3c4155460f400c400c0c0d84240185807001140031007008948000d0001d070400340c1c101450180000e441c2002440041c0c011070321880083d61180e03084d411100a4103800d410a13417224880d0a00a016801010b00140e1801e080c0303070302003030300c03405800081c04807094880041c1c50315003140c0c0c0d0000500511076040380c1000c0800d101c240054200d0a8040309240c0786051040c004200080d07158040403221108800d05181c02400d00095a001c400ca1046c0d9a060780c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 881596070 1250 881594820 881594827
    0xa0507081b031210050a0603020f09102303130f02011707051201090501030206030c160203071706060405100b16082808040521070b04030e0f060412170d0e280f08 71
    0x1862114510400c02039a40c845d233412000310322107801441c02100101410186c0061000c0241c4418051005603500e6686011075224080020410000c000d000c3c1d00c1071520700e42070345080004054900041d1602d04c0401c03008140b40f520150045032090052039080014031480d455030300401c00c0751101400e55004600c0015032400103048035003003101207540c0501101c01c1d081e80d072000307880c600d9038850900503140110400300c1d55519243c01414060b04204903690940d5140049052443c1e0014010528100d425421003011a00010282000c4a048400326001c025504a4074150000140500c0244640c2000380000b0510000318066450190703495211b4000303d5004006c058050f070704006180303070a00000c00c410581e21005540796241d06035a40f130800400002005407074000c1d4019849501d0340c41100c100131403000c1a8041c0d402d201d1611591800468401030003c1d80c1da5215403d0381d55029500b569000007483d40b1403110380f40360018580540b88940d603183c00040085101500000700031 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 881597320 1250 881596070 881596087
    0x120a12050717041409060405040209010603150906080d080106020a08071b0909050a0c0f180506150f041a07080d0908090a12050706140a0507081b031210050a060302 72
    0x101d41c40b9a425601452551120b40e41d40381c0e491110f40342180f260040d1210b401085e00c6050030701482c0d0045030300418007a0039a0a14a0480083c005a41c0c1030780d000111340310001d014215071003100098a81c0e140501003410030864054000031042e880311045501c13480301600414140415140319952000c1311481c9568a28507034401149507820201c10585000304800030008000740c034001c03051280c3d00600c000340d96080c0e140c2040e0800d1084c1d40a054070a5000400d8003003681c0180d0780408014224590004020081c50185d080205c0c9000120130001e070500407210a20a1006003900e0809643e1030400e4590700e4450a0180d0790201202c03e80f01e4054104101112090302c40d0701c14085c00d0400707000c0d6a190f220000c80c1c1d01600550380760003204401705503607205030b070945c0d6000d8100d03030700d149000100c090440e0745034407818003070f9140201440800281c00d404807202805280b980000e42d11101400c5152461150280c60300107130390480c0000700308640360b4200c03060440312541401078640c85070 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 881598570 1250 881597320 881597333
    0x703080a0504050a170c010e030d0305130807080a0306140607060e011d010c0305130503090910120308060916210216080a0822350405120a120507 64
    0x850700416484038a80364085500080210f44000d415100c004031381032241184019110700800231101605508404950542da80c0203401090b046203a1442c8400c810722103031124101508248400c44480100182c607071002e0703615015050150440803584040c01d00c60100052140c8103500c002020a5240c1141c800e00001c00c2d88140140c039400d5400c1040c90a0080c803150007403010b000c3d170202080c0b418012401e8060800c81c1480c425030300000940c078008100301081042d80b00106130240e841c0251101058203003181e41c00c60541e034441c0d11511114101001003090b10400104400702407404170b8803450b00c03a64000e4090300e03a451894594415030307241c850008007901c0307028884111907181120b50030421511030000e100315901507031400e0302c41c1c9803a8101e07080c50701c80107446190300d00b414911001045d0200c07113000f02c1940500c000b1140e14480340c00f03402d00c0240015429004400460100142e0424000d1402e103400580041c2140c1e44031a61401d54252410301824100980400d120042210 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 881599820 1250 881598570 881598577
    0x10e1305010b030609071d010f1a0c030c0a030e0108040b0f0912180f0109031106160209090c0118060813032109021813141006060903060e0d020703080a05 68
    0x7406002c1c0c03241840d0050b407282e9501207d10810103082440c00c03114443c05c01141c00d841c165241c080780300e074426260049001045140d0b2840004070201040144034070f5a040000f8180c0e12522005820350fa00c84c2c2c10f0203403c140307403110581d060022450801002604114903c1d13803140401d01c0d86031a0f40c0b12036498500d0486c0b045001000c01c6030001d0800c0300000310040340c0740b21400443d0000541404113004680d060103901c402405802461405c0d940c520f01a17000d0a0010080d008052415000c0d40008181e042d0642c1c150245e90885081c841d06d80d41e0100070070314002ca46c00d0000844624024000741201001801200107000d92114141014810841d10201c04501c03800c0411100d03402c0c0700e00d401440c0c00f48080303100303003c00704d00140c1c0075800c2215280702e004404a1500f103000ca075120b5004025102808c6946030180808520541185100c2c03e40606541ea440030b00c0d40c0c2c11494a8800c48054408801c1c0b40e41c08800101c41d5103500003003000990b41d001e101542c4413a0008002c0d5035502 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 881601070 1250 881599820 881599841
    0x21216090204080c010e030304031212110909011502100504080c1e0f0a08091c0605010b090108100f050d0305130905060f090121050a05120703080708010e130501 71
    0x428008000341155207a000380050340c0d83c4070165556111002c0c0107450610035580081d80680091000300b002c100408540882241c00d4148003426203980002d10048503040c0d030540d464000301140304c1350503050180c03240e80589100c4034103140c0e10b100243d01955840000020025051700d4070005020002e1407030030f42c0c1e038a60315101210180b0141c00c203c00301010048030186860310424580c1e88203003c0024503000503940000701913140640b441d06001d0310f02030003811401082004110207002900911901e4020548064480d8031608040c000402015001e0809001340c0d010010a0045114002640048841c1158513105a494518054540f0301840c1484035100140d00c2000035034805a030007892041e44101c4000d824005c4180c20008000420300442d403070307122200340c280d1503c0106400300c1c1129021340200c070150481c0b41d942c5840c107034100101c500080c0c80490b0072000c040d082880306412001c9410010319641c1001203108080034000d10072400b105000c0041000d0240a600c0f040d00c14 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 881602320 1250 881601070 881601103
    0x40b040906090f02010f0807090b1813050601020114010503060604200a21051009050c0c03041d0f04050a230a140d020304080a2009100320010c0212 65
    0x180702810700800c0f0440c088002c4c1c1c0800d02201e440740d02c13030b44502c1c00035200d000c03540c444429043c02d2083d101d61035040b010703a14402c809642600e8080b5907441c0085a81a0b07228540402c40e890150002800d580510325a80b612400f00303001400395640205201e40c1c40402507500040c95290101c10310a0280c0441c039510380c1c003400003200d603013a9910a2440e10341074003034603010303035811040b088a074100c8104a4445002c40c00e00300050003000c007681c02c0745401003082d2840b907061844003c04541194001e503c9a003c001114007480c9030103111000e4140c0c081c61403940d0704c2042c50030b52513840d2504601e0400a0910840b1140140800221003074810015103031000c4501800311450301d01c0000025900d0600f075403003000c142011151000080b942900c4140000c0c1990f44030316910240a41025205510308040c40440c0140c980c8592509034402c5002800130b0348400e145060601d1140c0300944411141000814940d825981040409041541c1600c900d403003d032890b0800e0f0700b044401c28104420 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 881603570 1250 881602320 881602331
    0x70e0a0b0904060e040807060c090f09060f060c020603131b0b030f0c040f05090406240f0f050f2202030108250f330c05010513020a05040b040906 64
    0x46000400c0945948141075908001c1152543d0700320745003000c104c80040c0461010000c1d00000b0701341c0c0e0040301c012901801d04004258403482072900e581c075590409000143d880500300700301811102d030b0000900c1c1c5401c15856915094011412902c40203261170304008084100d8000c00c0841c03244a03905138940940700041c07170f880b140040e081e5442510707841024014000420120031000d400c68045070603051900c40740600d444103014001e040144190380b91691600c007900c81160080c101003000310640c041e00d55090410341b00014061807500b043c40a41080042805103031590201030b03204d240d04842c0d11548000180c0079001000d841c911520416002000010301d00e100005d84100c0452030108001c0035203449144104540c07118440d1007000600504100520b4005406001405220340e81210503207006200348841c100b080b0302883d0002c3c0130a0b2130801801000c1c841c0d903401c10094101c0b056002d8540d0002142d508031030045600c100d98400070701710b40759203d40c0100105076020704c00b8003a = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 881604820 1250 881603570 881603579
    0x100e272206020d050906280c03110c06010503070f0e0c07060e0109061a0904080f0c0a0f12080c090d030e030f2505011407060f090209240105070317070e0a 68
    0x4e010300b80d496002d14840e040c081026042c0140c4208110201d40f081512283c40300841e01c1c0241007101d01c0b07902495524021000e10141480007003056200020040ca641d514000c00c0c1481e05c40c09070300c10004101d191005214407104072012640000c3d8509410391035a00605103000181407804590b51990720703103828a010000c41e900154500042026001180d0800106010321480f0441300100301280800c80e08500c004121f01800003401c1600494580381407594440f500f0140595055440b10742750050100800da225074002c0c0d01100340701c441810300c06040003042d110000140000c09004183caaa1f1016460800c4410740e5258444212404884226041c02c5905a41202508810362400c00400d00d940251214404800c071101014500007450300c03440020300058554200070380d2104220805603541c0b80007140079048040011840c01400d82c48820003030b02c18116281840805d000711000f00fa000b20b9180c203c519034881c2c07a02c4a036118801107030000c07039460a481e80010240300125 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 881606070 1250 881604820 881604847
    0x2030a020a12110a11090109110301030215071221230603030d0c0e0a0609030302060c09041401030305030601091e03030309080d0e0d080a021e18100e27220602 70
    0x800030300146d400f1403080e601c1d241240305540c95981c0f410440c540c1000104010b08110000d050203140c1c482c04181480c8040e920403c03c03188500008000a0064aa2520307a543d0000785d00f00000d0256020020851241080040402c401ca0314004403000c100018480d9101401250400140e0722030401c14941413480107400e0208130740c0b00c2800b070385c50643e010882130b0188003032905998054000b0212680d5403100c540d4280e1101e00c186030000e4940c0c00707081c1c206010344a002d019500c613444441e10307450548001000d41480343e000154800c0944250b0368086148801038082d20781601d40820f40282c40e0804105501c986220280002d140c422140e103007000220700c0d84044482c60341c0f124042e07121481c55200380c0c01140f02102c06000c907099119003100303098000b00041c0b03c04034864036400003070100240c0024030b80c400d035802040008000311200d1a00200c039503c80201c12541e00002000030004440d4000c0042c211200e0031648822841c0c140c1604500304202640f02c6400e55a624071044100d = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 881607320 1250 881606070 881606093
    0x1704150e0a0e0c1e0a05040e060d080306100309021513060504050a090218090f160302070503090904050a0b042f030a0206161e02030c0102030a020a12110a 68
    0x1100000c40c04540d004403403901200c00070480b501e40010074503a84802100c00c00d140d000003400d04010390029030900711350034074a0141410141503103541e500c0d83e140011942c003480d001008a032003002d00540010020f41d8441c26a038010300c0569510310302000f82d6000394002c0c200410040c0d880111007290780c140e03c203003200620031590703101149040240d9948080c0c403180030390b020721940180d20790342c24446e841070faa0142140d060307044c804604400c005008a03002e000c043c0c40400c05034403034108016080d080f4000c14040701ca01e5250440c034081c2e094599a4890084081461055456101040902c0401c0100a9265400ca03000c00030710704191900e288160980e002c5107000d40003a20350080f12841c00c0d04900082d01d0041e001c5c0a4000c0349030700304600c540c880e480c1c1035510281e041c03d0340007003540d8000c0340c20500b140ca442c2703481c802d80070f00401d4a0001c80c00b0b085030442d88104502c082042c0c0c049440c40d9220790083d098448000340711416070340071016070b080898502c1513107a040306018408640c03 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 881608570 1250 881607320 881607359
    0xa050a17010b0a1a070807060c021c02070509041721060f01030c0804020114040b07110301050f1012020607020d061401080303090a031d030d0206240901030605041704 73
    0x20018040c000c0b081c041219002d2150305880780303001341c01e201150303503003801001c0791803086000034681100c687e10a4100c1d6600c552450048e0b02440107002a2414540c100903031038035038002040c42610b450300062007044018001031082c3c0030f4002091201003400c096484000e540c0c0700891031540103200421b8010002c9a409102d14042040d110741540644122800000599680c049030360b1550015605c80d55071241801420402f00000a1304e00c02045c003511505205510880c0c481d5500d500f01400d645010741400801c1041ca0103001d00181c03020703a01400c4070b0b4401c1049041c2c00c2c480c0000340b82405209006508201c00c055884104002a0b018003004a5002e1140800da40c03242081c503500d020480e650000303a84032901d01408a07004d00c02d200200e9081080644104602e800400c0c01c0c03400c80384a000140c6c0c80341c01400b41c2410042c07101170b0312880d12a209038603020340c5400a445854103200c0a8286a03888000c00c0030710103250819940551901c0810340d64595400f411503420740e40800 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 881609820 1250 881608570 881608573
    0x90509151504121a010b210631050f060d0f06021e09030d080402011d0319050304031a0702070303050a200d02070e0c03041704030606060305061c0c0608060a050a17 72
    0x7064100744641590700107c0c4503000760080d40300207040880d800d0b8001d884198808040003031004419450f4480b1011003040600119200651641610a03038101628081c0d20803444010800580c40d081039520456070010300d8184252035034200304000780305024951140f03100340009001c0b06003065000300490101502210341305030f4003807001c80b0485801d0700d00a00041e2502484100700605d06400c01c0100002000e0b10120012301c07408812400c011113007290a6003008c13400304144242000441d0711640781c100000141d06e49060000e45a5580c0e0000900340f260105070880058401c00550301010318030240c440200804604007644c4d1814100024014030130010302148040036543c00900078840d4100680c1103031500c1c0d440380007501e440303014214a15804c0c48004046407032400340e580200415200001c0d541880c01c24485504414200c01e054018280003000c0018001548030703088034010301d400d00b01e81c0c40d0040040c4e030482c0305a0000354800c1c2626800308140d8100700c130310701c2034a56510 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 881611070 1250 881609820 881609873
    0x6210a0203100603020705060c1308030409050402030115030c06030f02090402180306060d03050313060b031f061410121506021f0e06040f170a02010c09050915150412 73
    0x303c3c00c8041c0e2140701d00050064021704085420000d02002034512075005134600c20b4040d4450140e07a01c6e5400c240d00c82034416486505020950600b80710b0115251905208480c0303140c11078681040d00c10891103510109507550b05071498528003541503c8036101e008100f55170303400308914030b041e441010a034007074403900038100451200e02d00201c03200a01d0f54136864950459890400c400821141484203450554a07650414050f5406201d56200748652420480c028816058403d0454220750040c9104020950742c02829036500880807054407081d2401d01e00310846003040e0702c007070910f01c1c1c0324643c041c02d441c10200307480d038000c100740c0d16a409440d0010150300c0c00f03460007403d4a4003101165141d4010780003180100e600487d800d807140d800b0791030320b4480d84070944107104070340c0c000c0501c0c41c0180d40d01d86076009140c5d4403000703850087c00200c60741c24050070318003100d1058106049030706e0f1041004000050f5031120320010b0760000e105d60060312000d980107060420b0a40541001224510003e8 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 881612320 1250 881611070 881611079
    0x4060e0f180406053312060112120302041a07050a02120a03080c0a0e0111011401090204210203030d0c0e0a090b240301090906090b010f060f020c0f06210a020310 71
    0x1410342403030201040f10b1a113035044000010b405424111011550000e01b51080011340d1441005058000c0c20011504140041e26051495202210138030040425004100030001e110040c0300d140462690f5418155840303059180851070301c3c80c0c0303010080d004881c0c84504980701c04041001746c4035901035121420607544e800100140c0c0d04c10701144502182d400380414205502c941ccc500c43c0c03001050070001130701883c4801c0c04408800d090380006101030700001e051011001411a01c4c0404840880040c00e40f071030355001a80703d010303c502100c026036481882c80f0384c03944160000d11348000050500072265071250703003900c09020520ba41c60301801e4035240348404501c0707403100340380400401c0000c681540d00306404203010703290240041d0340d40b40d00c1e641039402296521a400b0700800c0d002c21a00740b41407802c4c0000d000802c44000801c155088010043c03041c0d1500ca0f80308041407412544695a0034002c1c4064030302e41039800448440e15000401c011611485600540c001ca4019209034003a0341c3c0d8 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 881613570 1250 881612320 881612341
    0x1a0d050319021c031113091505060313080a0e09040c06020105010b16031409130b03100b060405090a0e031603140703021c0e030a06050a110f04060e0f18040605 70
    0x303c0441521001c40340e0f100c000107500c00d0303101031898400e5403001403400340148604080c098481d000710502030341c0e640b0311103000400051040300501e000c0e2044e50561a050051405120707564401428441380061078000031807143e8110074600000070009222800c00d428407070700c02c142c2c42c0140405586400000315084c022003040e11000395810810b4a480c0c080e65600315600c81c0022040211594103200c24086c90361090b00526611109140015003610400105803078a90003005114015142c00c2d158102030f1503041c101d406642c401d0303811005070784411403840f00a00c50389081490b140801b190800598040303a402e40542406550361343c000c1c4651448042962141e007100401607405030f05000d01c00c103e0001300c0c401030039041c1401c0e03240c010814042070404180003400c8030b945a440302004140d9209105000c030082d00240308038102008640d040e1100d00c100d01810342030202100c0c0030f642ca80e841040c69615883c015118495040140142020039103041c2c804990032803c000000355003d06 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 881614820 1250 881613570 881613583
    0x18070f0e1f0915021c050d0b06030702210a020a080f0708030c0a02010c050909060111070806070e040e0d0c080d0b04022b0e0607050a02070e010b030118020f0d1a0d05031902 76
    0x314110340100e00c04145c03005886c10351003c1085001d0b00d440b00500d20b00d9a440801a500c940751a4005e01914000b1b1101d5100340d0f11240500703100c0203030911401c10350307a9000030700415241e030041000fa0b440d0010142e119a078020604010300300070002081040090109003e825140c000d0f4000b0f0004811400091b68240641c4d030f0155004440314000074109d43c8601d02001080320010f040d2003c1036240e545e07040c1020401c03681440880d00301c00b40300e031503420540324407030f19460103d01824060060100040041c2024100a444841d021412503040f40c55688645540c10004000315a541086015424415102e2a00300d482c5401d00b0401d00c0102000c3c0102c08014011801038500783c0d07195602611160080c07060642180315100700403940c18000b40b1014041c0c1a103955158032903140c1403500c5086080131140034030482c01403010320031001c10a82603d1070000340902c0415090000384600d60140100040d1341c1d4014900b050800621401100400c882c00343d05520502140c48e80c40141d90710130 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 881616070 1250 881614820 881614843
    0xe04050709050109090209090f04020d15020c0c0312040e0712090b04021e2103090603090a1202120d0209011115010501080a0b060d0506010903020d0b0618070f0e1f091502 75
    0x14100b9000589c00700f01074103e40d5001d0f200924041e80e003407664032500354401c180c04a020803581c0c001003460404d2001c00c850020f410b411401085070302c031a1208000c1a0240d44a00c4006c51044401300d04c065002c4c11040a200808803001c0103820080c0c2000c112002d0150340a90060071411001112220340110007114180301800b050038042142400740404071071980b19580d2030100b4014040315a9a0400560040c0030910050407003008900300442c00003502d070b10b52010755001004400f41000303080142da828810f007580068450840341c0058480c2c80c0030f2070a210316401003045007003800c1d19a08115060b03540030303613070720b41596a40c00c50141100c00c90104680e00510030b01c401c0d03609000c16001141d204206245c10321070b00d603403540400c0c01380304211000c0b60342360030300b0003007244074100031020000301c4050030450589401d1103000a040385841030001d100704003144145640c50b40b036030400114480070700418034043d09c41280380200001403a00420307280020b82542c2e480c1d5140700003450703080300 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 881617320 1250 881616070 881616079
    0x50708091b0609150409050a0509061f05151e091516020904050a0303050703050f04030804060e1609060b0702280e04030809011503170a0e04050709050109090209 71
    0x20700c4055440785034009610301684424200010f0700b40c2e0316000081410b5181c904042034441c4c0c105480b00003580c034002c040c40f82691a080410403a03040020381e581c2c01030301c0301030040040c205443c0b100218803040d07044241c0000b0390210420344900300b00020000c010000c10481c0d0246580c1c076030484203200c1d40c0ca40540c403550032030078120490800001440c0e90648005c6030203001140340c3c042000c042c01128281d035035404c9160608141601400383d0360f800304007440c04008a140c4612107602c0110060000360801009c00d000408100d82540311174003109200d0304940c00000c1c117500080c2e100740c05000d8044240d042034000160594003c080d902c20b980d0040c0301400e4044d60500d4050090f2810640542c40500014001160402095030b40e014038000e40e100482440c09040b00e5080d942407a42264116049100c204041070b41c0081440000c20039042e0719580b40d0044008803009400b800320140c0c850720b41820f00960980140106017111000c2c0c1f40c02c05660742d41c003240701c101c0c0191003046410 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 881618570 1250 881617320 881617333
    0xc081506030d0e0a0305010606030e0d05041212120627050c0f03100b0304050a02150913020d0608071202030d0906020309060901260a05090118110a08030a0504030605070809 76
    0x2524050403e441e0381250290a031400265a5110542910200e600600200f95141042c003450345062105c0010f80310310b0704107989030502d02042d100740704030b00030301c090482d1329031a407001d80c040d104078a00c8204c0b512220f814070500c5d442d04058031007181061550703045a45a00c00301641007240d401918403070b0201e508510301b44804003150420302d5100628002c2100d10500c00440c0d90350401010798000c500807002400503001610611034094142e40f0030191b586810b0000003810340e140030301104116000d900158554440c00d1003e03010700b0454001501c00d001d840e02c0818031090440304074146038021000c4404810142d40f003030316810700500420006800c2001000441e0520000030240e0000c185042030441000e4140d000e5040403024405603904126020711840020f035020b51900104900000c010700b0304d5540000e0400400c141008040034803042c1542c04030b40e50004a04000d100c00300c1a2559407001c440b00030425405800203d42452509011079030b2244a111168840c0c02c071400100003 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 881619820 1250 881618570 881618593
    0x703020d0f02090702010507090b070b16092315160b07050d060e04020f03120a11070909050d0201270201050310210b01080a030c2d0c08150603 63
    0x250392052141590030986005510740103889518140348640718680c00016a030030450f1004162040d80c0d8440781d0060740501c40040400c50207660542c004542c04808101c4620701c007001d42d40c0004030390040581c4c5038016520050007001185144200c401154880c403003204640c0e401031180111141405468201040c000020b41c0109035107400c00801c0c140203050100c03070a001030649219402000b02c0c02040e03410b10045051040c0d0f0100003000807406010000c03030302c4e60b07125075500800141000300845c04c0003084405005001c54400740040c0384050181e186241003584e6242c450b03c0c04900190b192190b10561144640500c5003058054000b03030b1002c50180d0011540e540020744038005041807044000741030052807a80240306070580b00ca203078003200c1d14100343d8145041640000390395044086141e0002c1c0e480100900141c1e0f01469450200900c008501d211452048444580324000a070300f800f44100c00049004440d00b800c104c3d21000c0c9a203811200d1360800740c4005400d43c2c0540303900907 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 881621070 1250 881619820 881619829
    0x9090e1018050304060f02013b0f03090d02010311030c0901080a05090a0b0705090415080d140a18030b01060806090604021c0c030e07030b040b010b0c150606040e15120a0302070302 79
    0x540080f07081c400170450782c40b009d4243c025400c0400c905000c42407440e110620f5403050300208550711440b9400707020000061002c03d5100e100d56000c2230b1103200031071503c2c421603000394017040e615a445d41d5021303168070b0300001119859208810742c0c1d02189040000412101003400340b903104142007400307091007028940d5032413141240a01007009000041c07103d00b501e03883d184104c810042c20035000c44c40c1c9174609210a0300b051100c4e81040100300525554200a081c03c0084410b104414503085030340101c0700c62840310803030840d00000e007502341d17210000510300e9004074214028141118a29100d854010804c4102d00c20741c1c884d00c1d42c0c54030010040e501000d0b1580300c508003050504011803001c249a05490030860540c008503840401542030209102403009520b024282d103800c0a0700e05100e078002d9550711444200c0b14400d82144800241168452005a400402c03503501d007544030742004901c00049400400206000d4a803e520030360b0b08080c00907600e04020b40503009040002c0c04c580910 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 881622320 1250 881621070 881621087
    0x60b040c1e110304080304063902040207050102181512041104140703060609060801030b1f090212160305010b030c0f28030c0206070e04180206190305060f060d0c09090e101805030406 80
    0x44c3d2f0b00c82d40c2440b00c1800b0440a000400c071120f00040c000128440340c0b800c0004903444280e00c5641e1f0300d1309005004400040d00f0040da00141c0118071006440c5180d00024050041c000703454903030070000c90502901e550503401c0501505c0d11611504552a15078504540e099400d1002500240c040c1c0b0114141015448104a1400503440d060450f1600d40c1401c0c02640e115400c080c0c964400c2004210b0a1104008007040400182c48c041c44154134010b1800c80324040501580f410200000d900104101c200049a81451009044d4041e030310f11a81c0001c500b003c80004c4801080c00c1c6050f020860344045030b01442004075445160b603521091041c000100b01076078070315501400e4a10180b001d80c0da060007401d049106074042c0c2c03e07145130381c002c0181030f900b0140010b0300504100d41003407050364580068454940311154002500041100219814005640280c00c100d20b401850300250101044055040030341c1300044c040c084100f4198100c0b005c0c194000b8201703800c2800b0a0294a1144010 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 881623570 1250 881622320 881622323
    0xf1615091e1704060c0b0c031b03090120040602010f0c0f05071e0c081606020607050703450f050103050606210103060b040c1e1103040803040639 64
    0xc0d0b14030044011151070b01c03980a0340100c0701252228280d0b0b0100b220564070241d01c4541c2d003030a14158103140341240001c40000c071000d14141408400201030503000d60060f042d007404128000a10018840da400c510380c0103001d0074005500b4410b4402c0000700501810500148a9075043d004400c4400115580d8100b06000c48188900460419560b03894090302c064080c000e0b14103442c2e4501d007040042c0307807007020030100c5c1901483e502c2c2040230307980115800340d02002d1030a1003903440e0740a140803181500c5840c00740300210054451402e69154201c1030304541a01105603100001c2d0a14198520365140c0c85414091440c09005008951094200c90f4009202a0119042c285401403540c20340100039142031200c03000000420510042d030003001302d400f1040e2400c114010415000501d101d00d040c001c1d0b0101e403240d03200c041d1064800d0000380b90304200786081e0303611181ca402205841c2d500c1881204002540e083c8283e80b500700d01d000740d110341030040d03408410f0740e48131081d10030500f07030b00180 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 881624820 1250 881623570 881623583
    0x91503060105070605090d030e0a0302030d0213032f031516020f060408070507140906040911041109030d02070501050a030506061308011b1806080406020f1615091e 72
    0x20300d01c009144c1d80505030003071001c0c0b00a0400484060002022240c40440221152348400ca242c1c01003900401107688412031030401507620707070720569024180722042e4001480c0ca440c404440c124201e03407405404101e075100085666040712a41055580c40c40c4185909007116020042140d05a01000901c841c004500548201000c0c60b442d240c1408000c07281540c200c400095a002049800d02981c005001d05030072031404000203001107010400010049401180c1c0da2104101340104198407004940c0020400d00580968010400007030704084000d034003030321508854a258a001080705826108103a403000d0920b1120381040700505409480590844020400f1061012054904002500c00c0c500086071103a03c1c0071500700c925890041c01d000b0000f444001c880c42815240c004022200e0394a0400c00d2a01c0300e041036002807180c0d0481780301d00307907000179001315034181c4485120319039000c1d140a4403081c9001962006941001500814088020032000800003300c1070015615002d200d = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 881626070 1250 881624820 881624827
    0x90504111c090b0c03090d080c03011202030111130306060518130f02030307061b09030c050609012610060e030616120c0518030714060703050f0711040b0303091503060105 75
    0x101c50700031101d42a41d0304e032501d000010800c40f081800300802c07001d40c0c03400d1070101c6c60361614140440035800180102114491482a07000540d0fa0940000070440c0f2100841ca598400039845d8801d1041340b403108942d520b04220001681d80b03401084054015110070907012155031780d2022051240102c0c0084520881000f01c2d0009038600b0005003032014030079107001403101e044100300482c000032101002c0410400d40c1d42400000d5900800000f203400c141d0b203140e00c401004005984411240305c90b08000c903444000004071908660f00366001d141c2d55000100043c1d01c402d001c540354410244043d030180d0001c40403070140345800c207035203048454615010361819100c00600040e40c04030990f00000410204001c082c04035001402241014200c00510280b803408072412401ca803000665486590046408014180034004075603181c141c2c9148150b99540b686080c07820040c2184103540501d2820390480032904002080319600c00c80244611040e5240051032000ca03031005100034100300e41070 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 881627320 1250 881626070 881626073
    0x24061119021c1e0303050906150103020c10051e010839120c0a050f1806030f070306091b031a04050c030106062601062304031406040201090504111c09 66
    0x140ea01c3d10048a1041d4014800e54240c24002d05442020700301c5c440d950407550500c14070310100603805038a80c1c0282005607c6104140110f03003405410500c1e129014200000c000d500c600000c00c101c4c01a1032120704041c0c1d80d0b00c403c0000d81e40e1801c034040d0344038804000c83c82410300c0c80d0300c003002c0c1e800f00d0b01c88070b02500040400c2c0451000010910725605540c060702500251b803030182041d0020308400d5078907070322000d06100010b50190814060031424411a000709201352401d204c1110002903c0b81211720056036803829800030040c1c000e0a480c0c8501105211460300700302200724045940048154209074000581c400c10010003500459080c81210b01c0400c0940b0280580030080026803a10b180c00000030001844030741c0e000510005400c101c1005000f25500840561405c0050385c001a95405246c00d800c0c845100703d1b000038100e0800d428103042a080000b825611403031003079886030407840d610424081a542d41164180401e98203004851740c0205905004040d080c00400c0828840042d = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 881628570 1250 881627320 881627333
    0x207020402120603060c090310020c07030209090a030801060305070c1b050a08010e1203270304080328090b0d090614100e070203030f04080d24061119021c 68
    0x10003951820b44440108002551405201c4154044641c00f0a2850940100006038540c81c10000c941c1c50194041100d0254070000c00007940510f9020b0f0401801d82440c031601ca681d13043d40d5000f100001d5070440082203140c802d02801e8041d15003a10b50031510000d5540354101c0b1700289403100f41c100810b19002400c1e603603003c1c1d6078000340700610000880030344a01810382000041250510010300400c180440458042c0041030186c0d00d041c104c005001c62085c859080d0b00c11036005041ca888003040203406956001221988181680e40030314a001a0303600c240c0743e041051040740c941140c20710414840e83d526801501d2203900c03030140000c210120001c2211180300a540322011400c42030014801c14103940500c0e40c10641a0000750700b1450001014240d20000820040c2032810200341c1c000742100ca9003010842d1507580c030f0409001542212108003d501c00d10443c030010307402d00400240c94401181f9140365000300c1451503036800c4182c080c404a1011460030f1100d0322142070b1020b0118a0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 881629820 1250 881628570 881628577
    0xa0b0a060b040b0f360117060906030a1a010501080702061e280501031e080f0a14030f06150c07150e0d05030904050c031e07200a060c090b0307120207020402 69
    0x3007001417001402c94004000e00384031380d42020207050002c41c110161030441c100c03015682c814421038072042c803951402c0100b42806a503220040400d00d00d84d918098640d54a401c1c01e040e11300c2a07844814030350762400101e03a1608283c3d0702c95180204403101d0088151000c2050382d210001822a00e014140c0020300400c2070b50410510702c285990b18010310804c900c8004a0320a03200c402c0840300e0301e02d201d403507081d141d1007407280c042c0d1000c000040c030200040c0031f07000c0c0c2d0700e00c00100707500030307850b807501d0b407440040d200c82264043c3c80350318401041899140072400b501d40c43c00c1301c2401040e2841c188411141c004e500c0c241c503a01403000c854043c0d40142d032100e45486c4ac5500c181c000d107440d1220325041c0b01c1580e4000e80442220981803041044240720083c0381c607004100402920f40320b44034181c0640d0f07041c1117496412845e010840c444a01c4000010b0a020344c0340c4503d01c10804035010070011182e0f403c0501424010460420110746600d1040e0300e44400c289890b28018070b0607440e41d000508071ba0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 881631070 1250 881629820 881629867
    0x1020712061a0102240a18060902030705060a020a061e1517150c0703120c021509150718080d09240509120705030f0a0b0a060b040b0f 59
    0xd84580b0349206000c080502120400820700081805420420a801074007002444141141c6005400650070b11101d0308072062000700507261030140e09080c00c01c0c00140008001c240d000c0e05c41d103040010241022811103000034003503409094406a60780d40d58000d00001e485030110003100f1616003552220300c1c819084a141c0310168103483c1490040c8a0220503907501030500a60041c600c494940d58403940350951020180840941d244102d14040e10000c0c001e8007111030f42803809172a004070940000340f44005203904150f688860350ad04000c0341d510202c80040120f025640c030301142c4c1c00750044024203000595010345050164a0b2554035180c48664100074002803400c40c002c106804010b00b50107040b1000c1c030150b130101940460058610702c0307400301c2240581c94040840c139002c1030520042000c0c02c401015119400445208942c1d01c1e11050815955003400c0743c00720f1001c5695220307110442d80142c038482d003440d281514400e00340e00000a840b4068000300440c8a240d0b401c01103228a40 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 881632320 1250 881631070 881631083
    0x40305060a0905070b03010605030a050702030c1c09050a0b0703050318011b0906030e07050f011713140d08061003180b010620030304120e0a060e040f0b06030a050601020712 76
    0xb00c06418407614148082d0f01c14607882404000501811703074024222039000d5003007140403c0c15100c80701c04910750311540052803550300446c40383d405a842c0d036100081524040343d40740f5a8098860041200110389440762600110301000030384006805000034503800106424128030f000b0039000744600b502e5518504190078850403800301390540e0840031150241c0068035040091044100301c00b03980f124140905449041c01400c5241d11703138401c5440310f2100741d00f1a100c401d00c0c00d00c0181c80c43c800b1260182140d11110040c8422201c82e00001e84494040c5281d40350b54132521504203101d09050036402000800d0380701c044c9804030f242002c00805035103110300e60403c015850824001c140d550b80103110a104448000c00c6a402035001007a680c015800ca810500300d20150346081d80c6465040891642000c01900d00154440c1c028040c400c1d40c16084e9020b115080c0e0000401c4211246240c0c6d040d4800818404103072003076a55405981c0c000c4041c0101d8458a45400e0100d448030101401155030 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 881633570 1250 881632320 881632331
    0x60417010f050a021206040504020f040207060b0301060506070302030d1806020a05030906091617030d1103100b0307050406030207020f09012705040c030201260c3c0f040305060a 78
    0x1103224031802e50b02241d41c100c21400c200101103210503441000e00002d03c034a8030707035002c2002c0d55244407a0782003c2c20002c0086603600703451b160280c0509842e508540c401e5117031540001e02824104201d64105505034040c6180c07000421007440101200c00301c000102000389140e0001440300e100034501030082d6144c0586903e0446d100a10300701004107a0b00042e04100d580c00d0601002c411501e09682d0f00d6010401110604541c0a183d8019000020140b07410200c058400c0600311009601071441a011400101e80380e1f8100141840181c8400c0d002071030070801044410702c03941c00b8008107403004090141190441c00001c0d40000280c202c024001c014809900f07269081c0080d116034206452414007481c681502c401e50b0001c494030000e4127101c2c480a09000c00340c44624203903c881400e4089840c0c4e41001c071000310680e00109050340307540c0c81040600203030400840d044100c3d548100021404000030001e44440c5800c1007546080d14081803001000040c001e00c00c1911030743c15007400050 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 881634820 1250 881633570 881633591
    0x70c09090b280e0f07090606020d080906070509010201091a01170c0a060804030909060f17032b0f0f020306041401060f0e01110a03091a0a020a02040b06041701 70
    0x1007100081d260a10001403190350b21031100c0110901d410840215000003030070100503840d641030515208006803e401040c4010504595541c01041628015401c6804144902d0819656003005403188909940110005210745104500800300804103100103d140e907215550107945182e030340e1110158052880060285110000344042c003c1801d1008120305035280000c030342e66020a01400c000c0108403030010782458000d481c0d000088c981c840b0204141c9903945261402c0350442e001d400d03001c586201c04411148000019070700c00f0740b0780320041118030808061700c1e5003441102c0180d000507901c60741980003001c82c074441c0d02c4c03280720b00c0d0b50b003d40d5031f1610404010444400100c0b29015100050060000760342c0b10081000050060410210b4007004d00f0050310b501c08001c0900b800c5e40710f5007490000b050740c8507402c042120701c1107680c1c070b080d80d04490100d040760140b0b0f0048801039000a17540400b616007504022104500948641e1425840d8403001624010015200c2c034282c0d1280380204 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 881636070 1250 881634820 881634833
    0x130c1710260303040311060603010903140d0612030c060b01031406010827030d0c14030703090c030c08030901030507030b031f0209090c0c07061b061e0213030203120705031e070c0909 80
    0x1a40480d040300208400744454ce00035101c107040702603a06a0171004104552200c283d5400103014000c209444031a201c000d103002006003030102c1003241e4980c103050203041c4550090040702800d850003034610b441e42e500c9200442c0c08000003010000400d03030b81c511010524038009070010041c1002e03c0074550300e403c0c0207511800d90340d06896100c1081910719001101040410a4942101c074624011603a0078076414860200a440c4d0405008000d034100e0018221400000078002c440e42030301d052010b41e684403800e808840031441c9880d055003100304400144004244140c0c0840d0741035100600740840d074400306010035403c488121a4041c00605100e0107102008203d0090031a880c01280280b4510098500c0f00140745004040c19101c0c00c041e180607038400140c070f4001509100454a52250800103030b0782070410f04c03003a40a40a030440c4512241c2180003251402c030f4102004601c1c203000001d0940802d08503000e0780c2e120300b00a100c4000041c034030160fa90024007030000b0104001e515402d00c00c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 881637320 1250 881636070 881636083
    0x90105221508071d07050c0a05010c05030403030b0301090b0c0c011d0a05121821101b0804020904141e0102072a09050604020405130c1710260303040311 67
    0x882d13058411001d5086150541e481d03103a40710106190550710340c000328184904e01640e116005255509140d0040d174065070050141d441075002c2d176000d0000d170400304245401c9420155015240d4078114000440e20348083d07000b0440c6d030401d030000207401c0400d2164004001500d541e5518190400d1007210184602040588e052008a403020784c0341c5280d40500400743d0a00320034a0703002e40c244100074000a0141c241280d14040707c6001e4a1003008014a81c40c0181000c0c40c854036158040d005040009201d01e440c00c0c801d5034040c0c030b00c2c0286d45a5450702c2c5141c0c40d608901c0704541c0b1503040d50943d01040000040c915209200000d40c8416031490040201c00301c42c1d01d4000ca410040e105d04100c0d158020140341220240300d4001025140d15000c98045d01c29a0440c98106c4214582410001516480403040301c400355a07100303244030800c100300c1140c074003507a2088408100140500000e22003258401c04900d412a02032141405001c4482c1550400c86041e0f01180064510ba62181010f0080 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 881638570 1250 881637320 881637329
    0x102060f040b1312092420010b0a14210303040320010c111506060f03070201022b110307090e19060b0c0c09040209010522150807 57
    0x2424040ca4110262a16680c008001614042040001c2281144483d500312159030b000f456051040c074007203c002c1c1c15003206100e0181d500040181c1802c841540ba40d1a0b01e03440026603402c02031079195030032011149003070b00b40c950607956552840d896a985081c00030f0b000b05014a190f03010030b1000001c100d441900c403003280d400003100c10715208803030741c01104481d405681800e04000c60151100c0104e51b40310000c1c0708441542c070f411840d840054024001c0070f4010b010100302d03007030100c85136000543e1517404c3d40d400360846000c1c4840b000b8140c61074040c0d648000c56100040c10122340500c200d000840f441e500040c1141503041841d41c2e40d1090080ca4401000610502c0c55400e00c1c1c50010100b4070241b080d2000756a101c004603242080380f146204070301901100520000d5118002c040d4240e000c0520b00c0118810202000990f0911590152156400070250b00e603036032034201400381c01c4e0302c11414510354a2804118681500752031107108019142c000d9524000b030300382340c151031070081c15411 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 881639820 1250 881638570 881638573
    0xb030319110c060a110a0203012f12010506070f02060a09170606090a020a0c0c26070b090f010507020a0e180105090303040f03180b1804090210031505120a030e0102 72
    0xa020700261150f80440d0519005460b101050b11409aa42030404040300c000940c154200410021409890fa0f0305440d0545291960310342503c803000030b259507209210000300f014040034010444c3c0d252000c0641105030240c140b580900c015a0b0009046900591207a03001c62000300081c45914400100000140d05807401002036080c442c00281c210391000307010f00f942d0707170b0001000c0b44413038170504a41110300d1340b0a15100003141c03603c82510308107542c000b04482c0200d00035010031021400080305411145050b1100e407604400d80d003440103a06c81c42010034140300c401c100c1c150040e120b50a0a400406840180480a00303180007068407c8204c1041c0c071150342c1c100003c3c000d80c0440882242d8003e980211004824009450300f86c960340500038204038180d85038000090103102601c0142131482e04050000700240d2000c0801c4201c50b80100080c3d00000640c900c034040a000e6230048440520080d251030000d0340d10340000c2c5d10405c400903000290341240400d141051740141e03480b22280000d00 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 881641070 1250 881639820 881639833
    0x4030c05032b0605100905130e030c06090d170109230709170309090c0d09150e070609150305061c030302070c060c1205070318031b06030c0207180b03031911 69
    0x170041c05205a40a25841070420150140c61071030316a02c030510a10904050b41c0d212281191015124441144e42500501412250301402c912854960303071402405034040e4416403c00300b8010007409801d2220752801002c40c080607100310711540e40d900c160f015a0304d0301c6200b0f05000d184210201e0b001c1031000c050303105010b05442580c503401d000e6448100c100b03446841c2c05c0740d40341e610054500b0b100c014002a0000c1154161083c041c0c0002e02605884000c54070426600c0104032058007141c4100e89201d00d406600000c41d9210f5049540c00580003001c007008040011b00130350b081c002e6913500314042a03001440804001d007413100b5500a21044c102003403200050345804101900c40c880c0c0d1810000c0004244c410103016401382c05014a0441c600d0090340d84921705260180100c550500440200210001d41640329000c0c900701200d0039409012140e141113040d2100e804283d4006d00141d45401c140030b040d031010030160007009400301c0840205904884003070254020711000102c00e41005c0b = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 881642320 1250 881641070 881641099
    0x1902070b07021302211503070b0304030806030114070504031b060207170313120201020114091b0126070f030e07050607061410060e0303040e04030c05032b0605 70
    0xe005860715260141c580c042103248280d0220028031465040b0100c40d207041c0d4211035050300d041c518600c40c811024141c8102d0340f14004240d95052640b1514403aa8000c000081c0040e01c10100b141c1c0003000070700003246205000c0303034080400303804540000000c0c0002c50108180401d0105074800942c14448554800d803e10742c000f0748860755401101c010180055124810900410854001c070b1541e0a980088545900345000c0810b48040184d00560038503405044048541074041e0140c2d00c40402048a40d8500c5050701000720740b0482503050100c0200200400844507221041303013906c0c0a8503c003203117030184018003c03412804102040500e0091041c04030980018443c3c00c1d031b8003c07102c580d01c1d607640e03241c0300300a484142c101c0b00000001109010680318144480803d03920326031aa520b9a2200c8406d144d0b03640698444c40f52090050408980400e0003622034038002d0f405502030340d261448107a46c00c6003803240684841c0300c6d581c11080754031151480d44107c1c009804104d65010703402140 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 881643570 1250 881642320 881642339
    0x3020616030e0a020607030513030302010b0922021c21030c090803072409050105090d14030610270509010e090309103f0e0307060b0103140903190207 66
    0xf020000340180c034001202c00c2070500800070740d95204003000e01065035940700c0c500280a0800d5200c44c0e80a401d410011480001e8590702484481841900c500c0403080103800f008603044282040c10811804000d00d2004900055103904e4100a0034803182e405000744030008044a10b21003005040001c248014800010003004407070400350883c00f55004900300d40c01100350002102c2c10441c4040c071f40f1042c202042011b410007445440304000f0740b03910030344154007602c0ca11006104044200e004000203016454091031548503c4400d1401002c3d82280252540b18194001c2e024511042d140404103c94902400c4050252074011185c000c541040f01c4101d54074007031214014801c844655204040501c03440300443e921142c1d0040ca005e2601c1000d00c10002003058043c035000f201c0c03000c0d0b0080654050b018000040c91158001c0d854006181c0f90800104246600c0604050726211894001850508441d000303252480c0a550782d0346103078807481404014013000c60b055401c0017108000d15400c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 881644820 1250 881643570 881643583
    0x1c080403111f0c032f010608030a2307080c030309010b041b0807021f1410050a0e0a1407030204140103090c05010e0a0806130c120b042d03020616030e 66
    0x10b2904201280c02ca5524003030310549580f82d809844102c044550800f8607200c00c20221a034003100c002005500e40390014951070703125141d07101d008102e103201110000c0070042da100040d50801d040c6203003800601d03030303541c03681e07520080502c1c00035400841800103601702031160b550400340496080000c2814041c58402c0002e1665006084c01241400242940d0007800350701c2c0001d0309604000c4850701c0303001851005111a10344c501688001c1c81c0001e6400c6030b050502815100b000b0b040c0481180f50402c00c0c03d409500178a1020b41a0319130001055024400c11094007440075030318050707266401d00d0210140880503061150401d130a00c00100003082c441100070341035580a107807038119500080f01194000d1042c3e07200c0c903d54401c00003000307014145a4032484800d44583e20f034800d0035075503181c41c4590708880d1101030035a04000b0003013000a040740300b04101c040c0e13246074103810781214885000f42d800070300841500540c00027820040060101c1001d0f040d041c0326400c040103110312a000050360f40e903 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 881646070 1250 881644820 881644879
    0x6050a050d020f031c03112a101e0b040b133803060709060206150d0b0a09110409030c06020306030a0c0b070b220609021c08040311 58
    0x2141e50620159114014000403004001e001c5a00d8032618048102e100c3c1402c10714407000a24102032a5a03030f03c011811102283d00440d0818002c6090180340c40303404800b4030400c1d00310b104001508010a000c0d00940c2242c0c000642140401189444008295901f81d4070b101d204600d018224602a514541d03900000d1000c00000a2088071800d04001d001c0540d88000c41d4400d14003102c03a062503c44c2ca48903400407001d8080d251191507140003030b90a00070602a040147c0c100c0e00c0000e150100003456280c103500000d0041c1c01d0041640c840d000110f02c20343d03061810f152181c055405000740c40c2d407a01030012094400304194000ea8800901c60404200001d14440d0000042a03040e034040245604154020444403481d66880441c07001d25401210102c486442e0740c800a40080c480112440c180f19441140007088103480d0794500041c040b11000301e0780110350b00092191040217903440c04d4024850568150748600710304003245030050105002e8442c01070b03c001003030f00c448085030b92640784c0c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 881647320 1250 881646070 881646079
    0x1b080103050d0e01030b061315030c02100c0203070b04050f010c0906020706180f170114070e0603130506090a1e05030a1202090d030f0e01020d05030c18150a1206050a05 74
    0x2110030701c0105c0c040c2540003285640b001011071a14404184030245000f110a40c88900650103503210040d03090320450886800940c01079010121050842e07009600110420300c10307a46009615035942040c40c1080d5010f8401d03900005540b8049402446000b150030882e040500c140341c03412400955620160141e8001c0041030b43d41c2c5a00201ca110780307070000d80b1592842140b1261245058400c0c0c4840c3c4019040b21360814a500d111154010212401841d240c0e486100180031074080c411130340c0c405010041880400032411000c100c050000900030140000a008032007281c0c00d003403880c0030440c003040020030712020903100018000000c0fa43c00041a00340392810f4604551400f009009199096420401149620b02055401588040085d50640710380081c24001d90049035505860382c03441000c13402c00c0000c81d44440700302c0c0181c0f0020301e810780c01126402041c00407900b40c00c3d01c100b5104c01c44802081c24640243c0001c80ca002c006401e40c0100005854030340041d80e400c400348101d0307006 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 881648570 1250 881647320 881647337
    0x405070206010510031109030316050d050c0c0d02120a0b070e03070b03180a15020405090901050405060c0c0304030203070f05010809030c0c011211070f1203020a0509311b080103050d 80
    0x81ba28903c1541c2d040c3c1c800405690321810248070310701c40c1e600c4441045940f806201d00404e0b00901400641d060122100004c004031403154003408540005090b00780d0307101c94814070040740e08004100d50600c40307102e04041c09140c284040050301580076804500e100f60048002803003542008019280d0102200c0080c030200c106100c0704031705044e0140400b50085400302d0003030001e1090754004104170394040d588904aa6645003100313080b5002610010b0190b08031034081180d420484014100b20125441541d03d45036a03903000030300e030107400d900090882e010740c0010400c075a081030074190310548010245140250200d0b4058071103540c1250345d030600401c0e044c0209070090550102c0f400c20307140ca82c42c44d541d0030503041007132901610950494003600d0701050700700d500d8428001d44203501c0c400e0f2030b414103108048080080c1c081c6181c120320b003030003d40e40034480c0031103002c0345440000401410014002001070700440c1541d03400d03505041400142001000001d000160300c8040110520384070f0b00 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 881649820 1250 881648570 881648591
    0x14070b04170c07060e01111f021306110c010201050103030206070809150a0209041109060a031d01060b120619060c0c0b1b010b1e060a0c0b04030905040507020601051003 74
    0x1032041c20070640328040304002c15050340c003000c0003d0700c00c00c0e120b440d11400310a42c2c0750f1004503200005030004800581000090b5203280c0304502e41c07410714107120600581065145060300d8004680d030b9000354001408814170040040c8140a440741070395013031000740001e60440d00c0103991260003070900010800340e180060014041800402585090b1007000c50003410801a9407021f90170604a1a00c15450418804800910441142c100c5007015007000d0524542c00f1003540100f899483c4040c40381d210f800440c5420000707200d020301402c100e02c0c82d55110021700820740c0c0c0c81d5400420b0743c0c2c0035280d01c000d240303800036115820000700c1d047c43c900b94150341800e1602c5426502d481c0d101e8081107001240010301000380c1d54140b00c0000355a4003c10003031a101c020010840031510001a0400513840303030783c040b4141080180040c0c42e075800c00321029050395440080750001142c040d000503c4411080c481403600f800f80681241061000303000c0355040030300003040041e1000400082c1030703403008643c0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 881651070 1250 881649820 881649833
    0x6080a1218090624020c06090103020418230103030c02040c030b040509060915060901120512030106031407020303060f040c030905100f0608031c050a11070507031214070b04 76
    0x5808400030303502a52031a940e418540c015060304d005800414500d0b40c010304c6a04030100c11904245490340c02000c0222405042c4003043e8015080300341016000c10010810fa0b42101e071a682c102c00001d800992201c203041d0a820000900810902845450004201180d03000b500c50300c0d0303075404442c001801004280160000c110101001c0c0e00702d41864200048a800450682e1182070700d20180c1d4109404090060310807038007280c0c23a5500040782001482402d14001c4520310092041c3e00b02d5819283d60001c880e00b641091b8000d400003074551359412200c02c84200c1050b0482203e000841c00c60605000083e2408014038490f40142d9480384208980791103600010095500320003a50340da40308050550014062a00c14900050700700000019403140001c2107690014907420b5204002000710501405000080c015018441d210315950380d2a0400c20000d21901e80b04600031300a446c950b161580000340e4658496050000051810340302d0083c1e10111964298000140640340d134440c038118 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 881652320 1250 881651070 881651087
    0x106051326060f0604050c0a140a050f1b0d0804050a020904080d0c05070b011202010c0b09120415090614090409081603120e06010f0e060307230f0406080a12 69
    0x540d0380e01c41c0c84184030401d10f8440140b401841e00b5901803105030740d8080d83c0707003540c4140400b0300000f0740812203886594600502401c6060070514140b80780c0900620240d000b50402c40d814840724004050045012500f0000000c2d180150305080100c1d02d401c0e240c50b6103494100e54040d000750b10020025080240440840e2030310000b40030304201c403034065440186550403a100490f40000c1c03d20000c03451904410b810170516a0580d6414a110401c1d6a0300788800c0300900038424903c225260440c0e15185200500013502d030308840c2c00540c5004160040c01000f040c0c3c400400d02c05808076048000c04800704450061101b40c80100704904c9a00d0860380030300c1080c0c1c0c065503482d0489801410580e00210080702d0822400051000c2c1010b100d4075500c40d0401c0c8590100404000f000300f02c2241e42003420740e441940141560102569002d000b02415548030481ca182d214004908080e4900f0b42c455800c0c610054a041001c6824010361a40e50300c14034401810008605520031411403081514 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 881653570 1250 881652320 881652389
    0x170105040816031103040b1b03120c13030c0b09040f050106120209031213030b09070b0306040b031e030d06080102071205072d06060b21220b070801060513 68
    0x4581e50340d60355000300c903842e0704101c001d002c0034044c0e40300e0142e2345070740001600c4484910700182e116a840754401022141c0c001c1003601403075035060701c000000c915428024401403000040196a03010510200000c1b01d0540c10090b80207440c000041c01200d52001158940300060840140e031600d20400107460000301c0002034070000c0002401e0320306c0342190607a850490740b0500d04016070707854401c145a00c900d214090319103c6c034020310002c1c2152826030000e41c60b400001d0180c07003a00c1c0d294a45282c082614810401560740006030035203101c0190700c01d0f5801020301000031070404040d66103050030300400404150401601040d0760b0148164400000c541c0701d400010240038180400294816881c0c5900c252040c0b403802c100013500da00c000044509a0003401c1138010408a407843c0c2408100e0090055079100c04c94480546a6502a0341003041da2405118070302e030b041c81c281200411084058000300c040040a0002c107010880c8041907030155003081c010348040c9004940140c031079244e003245 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 881654676 1106 881653570 881653573
    0x90f0a180f11070501140a060f03020603090106050a0f0f050a1805090304050d060516020f060403080613020a0309030e01030605180606221701050408160311 69
    0x4401031075800900e0034507007000c403011a000700c802120660b543e841c01c610344010840415a0000c13a28034203214190405864000c2d03000e0620009024540100c080b0300b110742e003034200d480500009444424015074511004100c00c4040c49040070070040c030320740819241000510b03042500e55500c10200010142400c00c0c0007800020004844e5000c1440045110381c0c4401070781c01510302414000c80c4070b0500304510428800604054000d56120385a00c0120001c0454125130007a0107040c034060544d00c80011a42070440464000040c51000885070b0310150107511246006019540c1e07150f80d4171001005608680e00d274022076038000300400c441c0c804100c80a0402d84d119002034441418034202c40d0450080d15007154240c4030244809209000503440e5092185d4042840350013444141420345a0034180e00c201c2c0480c3c0c0180580040100c14075020300e1014a0602e034040 = true := by decide +kernel

theorem cover : BRFrame.Cov 881474820 881654676 := by
  have h0 := BRFrame.cov_init 881474820
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881474820 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881474820 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881474820 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881474820 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881474820 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881474820 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881474820 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881474820 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881474820 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881474820 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881474820 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881474820 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881474820 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881474820 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881474820 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881474820 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881474820 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881474820 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881474820 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881474820 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881474820 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881474820 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881474820 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881474820 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881474820 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881474820 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881474820 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881474820 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881474820 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881474820 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881474820 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881474820 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881474820 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881474820 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881474820 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881474820 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881474820 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881474820 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881474820 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881474820 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881474820 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881474820 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881474820 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881474820 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881474820 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881474820 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881474820 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881474820 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881474820 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881474820 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881474820 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881474820 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881474820 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881474820 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881474820 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881474820 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881474820 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881474820 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881474820 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881474820 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881474820 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881474820 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881474820 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881474820 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881474820 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881474820 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881474820 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881474820 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881474820 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881474820 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881474820 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881474820 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881474820 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881474820 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881474820 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881474820 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881474820 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881474820 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881474820 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881474820 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881474820 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881474820 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881474820 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881474820 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881474820 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881474820 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881474820 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881474820 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881474820 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881474820 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881474820 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881474820 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881474820 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881474820 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881474820 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881474820 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881474820 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881474820 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881474820 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881474820 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881474820 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881474820 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881474820 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881474820 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881474820 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881474820 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881474820 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881474820 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881474820 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881474820 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881474820 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881474820 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881474820 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881474820 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881474820 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881474820 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881474820 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881474820 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881474820 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881474820 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881474820 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881474820 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881474820 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881474820 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881474820 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881474820 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881474820 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881474820 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881474820 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881474820 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881474820 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881474820 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881474820 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881474820 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881474820 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881474820 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881474820 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881474820 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881474820 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881474820 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881474820 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881474820 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881474820 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881474820 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 881474820 ≤ n) (h2 : n < 881654676) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
