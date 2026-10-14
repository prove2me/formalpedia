-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0309
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T19:07:08.446256+00:00
-- url     : https://prove2.me/submissions/4287dd3f-de28-43aa-ba96-dd72903480ca

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 55395687 ≤ n < 55575543 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 55396937 1250 55395687 55395701
    0x6020f12040f03060e0a0b10090b09010605090105030603070f060f03050c040303050403080705030d0914060609070e010c021815100c0507090b1909050106020c040902090c1c0f02030a 80
    0x403001103880c207801c00ca0080070701041c6001c0586a95501d030702c0c1e00c07601c020421102c4110354100081807064680303d1001100107020f4001c1c003440750f042c031800f21524100703840a00e05031a40c40d1646424079000100448483d0001001c8a40c148900e00b0300140007414084204003500c803d603501709d0a100c03241c00140c2600c90107041280081e030104400c2004c0f039481070545094a03031140049654031428140b0610b10700400c10050310441c50140c0c3c100801c80e611102c0141000307010203480050b030319282000300071107084421901007480c2403031a0020350301c19100d86402078402041c03420384412800302000c05400c11940705504000303172005450035207018005485100c0c0c03c0e1900d608032a110395039044d151101d61060303603803103503c40005004c01e41d2480020000d4503075808116503501c0c2e0300d02c0c084015240038400d19002d4000c0d080c1c3d4a82a003068040c1895880d0090180c01c0241c03950250329519038031027001407942400340a10311a0030b001501a00192031800d40c0c8c00360326810f0201c0e0501c111078807 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 55398187 1250 55396937 55396963
    0x11040b0306010803160503040b04060302130501020105070c26030c07020108010f1d06010309020613050901140d11041d0a0308060103021206010f0203090402070305041d01030302030d0b010306090606020f 89
    0x241c40104103070380c800400c5800c201441420308600840e940703460b514500490308003141c11840490041042d6a00d42e01420082280d00fa102c040360b03035501c0059007210002d80c4c090001410100e001d00124144400e001c0544d9001300c4005104904010f01540c50b820540303190b184000009040030642d07901c05030240c051300c8903803001c6846034603109a5100d0321000c003289102d400220000030342a607002e94403100c50181c02400d1103541d0b8469240c245841445c0f030007135900c2840c6142c0040b90402160801e901c0c030220141104845009a0700c4140f11008101d0382940e000e070301c454214403034004444007003200000a500070803e5500511300506a07000082402c0d0400d8818800b56003030026114030a9000307502800c160100b03090080040341184184945035422500010700382003010f60000040c8100c50110a05c040e41c122407040014441c1028440500140c4c01804101e0b078000c0c5c6548490700b038a82c14103002400a681d0b400002c140c075401c0e03201c20050380051560008140e81400600d03041e1324 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 55399437 1250 55398187 55398193
    0x2a0e100206071209020a03080304060213150906031a040908030709060206060a050f031c050a1d0d02190e01060918090c12050f160312030203060d0602160f11040b03 72
    0x40d00ba003004000155004000301d40c0c0391103840410035074885440340400785802500e107d95914060030105c02a500c40c400e00001240300c15400200390400c50110389040703226036980c84c06c151800000f100a04000003810040b03002c0c54a20807482d41d01d030700c2020b07c484e01c1860b000e520307807400c0caa0107484886035074012410b540100040203040e540c1c01005009950040301c01c20700b1400000d01081c50212502c0300549041200103c0a61241c0c0001c05060382158550f9080d418542d00850350381c000304680d12490300701614000c00c1d0300628020300d141d0842131010310320001c12643c074142089400c40c2170b80110046520303180c040c0400020350b44001c031040100d10342032150715010798620b400388d101c1e80b01c1d500c8008418005501000705c1809080c040042c514210f44044006041ca5600c0d0101032000711140205041c0e84104da174002d009480c4180e200030000f0400c4401038450344081d61150f504401d50404100c0c120000401c08048158140c0c00b81c02d002d071400c690807040c081220000c84c2d940307200e64 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 55400687 1250 55399437 55399441
    0x303090516030f0204111605030405030c0f09011505130b030601080c070c031401110d060609080f0303070804110d05060f13050a02060903160618090b01122a0e100206 73
    0x100e0f000390b1910100e50603500000e030052440207503c05805410f8543c41403010100700c040030701100102400640303008406444804942030108840c5402c0810784c55001281400108030400032172615480501940c03c09501e00f00599100020401241d04041a2004084107200607541d001d803400354004a9080221f2500e2195202e159000034144401011722200e03e0f010b04082c002900084494516041030390741346e0a2554581015108a000381c4000507038082d0005541680002c0c0300642c110030601451542d2a140740c100c4524400a00654048a010020704c0c11600e648031340361300c084d024030b016190f135090028480700201ca000d0225070f944007005442030080b0300c0200d154001c9a90440b0502d645104100110341090803060b035102003410f054a0005900741c229403400003005000d500450001d445a144030f04440d243c1c3c2c120b0340041e0282e00010009103c1d03502c0080c8200c9288540c2c2854501320027060841c81c0325207402000102c0300102e41005080000f11150050032030700182c2294 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 55401937 1250 55400687 55400693
    0x31209061211180102010605130518010c0816052109070503030f040519030204020a0207032a0b07030201110307050406090e0c0a0c0c0b0d3804020c120304030309051603 74
    0x60042c60498038400c3d04000c10004a60f000354000d02c02000084d110444100904032a500100070442d4044000c038122802c13602002418401c0040c4440706449030701146d202c9510022103131185140c26024410104950b06c110440c000460711407511001c0d440002e842c00011681c2080816030189009030f2047c00682c08169042d41690b0076210252440550444079844403200ba65580d07001a4006200107603030a4010f0b800303c0c4c1c11054900518002070201e00e0694003000f00302e44042000581e0b40941c200b030002c00c0c0400007c0c06064064400818942112038000c42564820744090b00030600002c0d04011135038210003000000e1407550001e1010b4035205203d801e451142d00302c04800c201c2c00369020800c22010600744000741040022168440010b400030100070140200c0742101c2034000c90711441500c03e4201c0e07003100c3c2c0390000c5002c10440b06038814417020b9003000c2482c00e01070141c0c02c140280c4070640800340d4801c50081ea0085040212414843d003004030303042819140303c002c181e060000c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 55403187 1250 55401937 55401971
    0x20706050f0a090f06080709060801030206030f04081b011b05040b0a080405070e0106030b011205090a0b09010e0f0c0a0608010f230d030806190302030c10090312090612 74
    0x14007080341400da0b99440c280c5100b100c5654664000030440c038050f80020891a9000040303038810340440d11240959031700d80c03006541500f000d205c000d50000341000001c92454500140e980c02a108041c40c03820301112040d400ca5010500c1581000b9031764031990429044d6020441c07100e1150507050043c03406050941901c1c5502c11040800e0511610034040b50030403904011031401000403010014095031520001800790022200890010345d032150344044aa0540c03150300d002d580902c0080456056954611800703280c006d0812820b55a1018580550306d0240400442010800e0142004e1a03c090401402d4180c1d50801c03401c04c0403000040c451400074102610944000d2841d8945601500c1240843e5920380c0764001d40020548010704101600060310500444007161005012403070120f1a030082201444040d60540c403408a15845042001d9114804400740c070f400040140c480e1540ca40b0300c8a020150f0000a41c01101007081030303072003a143c24022514a80034000740c0e16582504079 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 55404437 1250 55403187 55403197
    0x30b010309050c040e0a1a06032b030902010915080109051f0e0c070c120201090b09060405010309060209030a0b070206090a0b010509190c020f060906011d0a020403020411040602010b0102070605 85
    0x40502d0717445820030145141041b590101d1944134514440c01a040448004000c1064500b140240300e43d482c19007030b04546038181c41207a03940c480711240c02c031507202d800c0b070142540da00c083e414001c0d012000b04907512507440f4102d210a045d00c0c3c5082551504858600b1508001c00c0c10f142c161721a03103041c02045071161007400300c82d011704984400d0340340c29003001024031500308000c2900364002c400040185d50a401044454000d88900c0041d0f0f694040441305c0e84a0382c9081d60f40302d401004140402e40c066030080030b50600414005040040120200745000c400302030039101e07400104108171896a040110903440703215907000d000140095682c06030745840600504e407242600100140080f00041110360015442c0142440200707040302d8069103c41c4142c840d44018015600015141d2074001401c9048034590f040e45017100b026128003502168020701005c03030854003040000050f03552070050580c0410070075100d07581c035803030401c000c0c0c02c40344103030320701c906642112200f040f800360844180c0b0 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 55405687 1250 55404437 55404439
    0x1180f050d050c030706170a0c20030f040f1a07080301050f010c210f050306030706230a03060f091a0103020c01090807050307050111040803040612180b07030b010309050c 75
    0x101c01150580b0300103090080c3c041c29580c25101d9032000107081a441014000c602800c2c031401d00c10342d103820f80d21406a41c109850704000c05c40d1485a1211540405c1120012408036025241032890b025540c034a1940300b64095a60008400003d2059219100c4114001d0100500c01e034036250456940c00881e0105218062080c5103852244010385d00030080c480c00a40d100c0010104980f18491100e5111041c1184500083e0030b428001505401202128050040100100b107054501242100c1c0d010500314400e0407183c041d00215849100c503405004d2520003518045101400c200c800403551b64107a109807045410080704503d0740421000c0b01c03c1c1e000080c82c01503940d03001c1c0304866000d02003c0c80003c0a1007070004070744051080110241c1032891081000b401000d80c50042006070340070b1703801207803083d8104000400119001d28124260151507420224050107004036050305006080c0059590188080801c40003075814811120000b03001d003010841c0d80495201c0903580d070741ba001d0b02 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 55406937 1250 55405687 55405699
    0x3030c08070f050d0f030c170606040f0609140409020616020316090504261903110403030203090307080303010b070f062c0c03070315050a0b040e010b01180f05 70
    0x2050900a584040315150380d00000c090700390081e50f142550b51342c486510800b000880171400125501d200f030045030340400d01e503601c4000300d481c0c401d01000600320160a059103d1070800c00003074800e15a400a90043c1740c00d07112030720801d18010314030f07002c880c90099982c85036241441040c0160380300010303940000400921349500e0100c0d480401d2910104000c11a28103220741030020b02840d0035002030b0303c81d5100d680c6040024001c0e4641e42000602c1c020074111190303060000410f42c0040c4051560100418580400d070500d1814a030191a400303900203600603000007505109034202003003d02c005040c124015480c7d50b00d0708018060314040c43c0e4000380441d40d1070034030300140100c54011f0891b0409220200c40c00c4038000640740309418010824a049018504401c50345140c0421081e00f100e412a42c0760b40b8240704002e20a00500000b404041c445549144400e000d031561312a01406003414000010a81011000540220223500c03043c818018a814240f200486c04080d090881d1400e03544 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 55408187 1250 55406937 55406957
    0x3050406060b1303140307080a050a092301080906070203040501050703110124060507031e0c0f2d020d020d030207090207050c01030608011a091503120c010c0c03090303 74
    0x3214000d040503902009a0800100b074600380c2c0420b0381090b2013142e210b0116200301c040814001501c0740504030740a4018002406203000fa03034000e40051514a11034039002d1681c0d51913138103840781c01184603101303415004014251501942c111040507000040361009000c00d15000c8002940d034071541c02600e04209001c82c00b5401c06014240300107010480303000911542c0702410640034681e00c5241080f00400c1c00c0000010994000c030100ca5240e40c2503174812040740041e600061103075041030900c008104013010200040303803c0d650a03a90b15841814910b000300031185420400175080c9201c1c000c500411110540141c0d150025201e80e00e07410f0310301c1c03804042c1509060317042c00050750007012403034000503c6c07008011000c1003464614a098a003000119250705806013250f0a100c012107094085070342c00c022600d425024554800e010380f190310b04490b10b0501181c03d04029000c807291020001c07413240c200d240c080c0611420180d080c40e1588001103541c0f030080c1071051610016050200c01c2039 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 55409437 1250 55408187 55408193
    0x3080904060314060402011403040b0a051b03070206070e030c090a0c02011e1b030c050306041a190e01050d02010c0b06010c140307020102010b01050903150a0b03010c020f0606030d0f030504 83
    0x81c0010740d00a124528414551a01140c55030b00440d0200d0001d003498808401000030603041d07a00568005426484c01e0380c546048800514005c0d0095070345a03013800c409910038510800842c400d15066003e440c89081c151805011041c0211015200360451038010303180b901c03440006603100a0711800411652807814080c2d0051450000d002c4e061541003071403da00001c1d0b03420112110202d01030741e000034411400c0c21800c503081e108044000035001c00108004c0d1030150000305903135040e200030281586280f000100c1144281e5040d280754002000b0401c1050002c80c4400d005003002d0f61300720407200259000074040410034600070182c1c0c0600c00850140c0c0d21610648100c907034040e04800c042c0d18801c01050b62a00109000c030f0043d820000c1c14a181c2d48100262155124080c0003001d0142c011600d150000c007005001e00211035070b409940803940e030300340582d9924111640280014401301c1410500346a401441c041c0039900c0002807446040d40055480b829005c113150005007501c880c9 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 55410687 1250 55409437 55409441
    0x618011818180b010b0403050d02190201120b0a12020405010506070b060907110703060203040b060a0f12020f090a23041e0201170406020c0d090f0506090109080607020312180703080904 81
    0x10203003d03100c048001164420401d40200103036070150040f91130f1100300000890380c41030a14400d0f01c00c1001c3e0b04850006500031200d004c11002e00540108155410748040744c412042a07011603c1c40b01075000ba001942010700c03840d40034103c00c0da141841c24038552121000c820014210b0f0380900118800544010300c201030030100030781e801d015140d54503074a0800c00f020307400654050351b00d0103000e40428520b1034000741d01e000300c603c000400500f061030030445487c090050300082e81c10801c59040c17080b059032a8600188100c40d514400550700d040d40240103000d40784d101e1654541c6204900748004178205207404c03124503030040010060074104e0301c01216800c400c441400380c0d01e0189000d010400007560003800b007240407241182d910104402045641c224684205000307076440d95400d2000d400e089006100f42c0c0303810b040c00001d0300d030f1303508201d0300e05081150303070000580010500e00c2000748005110742e000141d80700c1c41a148142c542c0482e4840d03001d0b1100404821f40044d000303a03681c5450b = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 55411937 1250 55410687 55410731
    0x414061e060409020304060c08010801050603060103060c17040f060e12030a0b0f04021903051303051902010608070f0608070c0b0a0e010e010c081509070f0813020618011818 76
    0x210f41551a0305003490140b001c0c0c0150740d458030102d805100041064801440350038443c0500800030400359103580c8030380000b0240d0340d1302c460410202d1100b481c81e401542071654040c40c429845540e940c031560401608541002c4401040390302301d0038441d86034100c0c240c1540d03001040107000240c842400c0340000c1141d0400070340c00f600b00e8000301d040003441c04015916180500261414845a610741c030071400014805200100070600a1040c0c0080c2d428101000004100300e000001d4407503141c0e050030b454800c0c2648142002190150f041c859994800c44854000b419401d10402c840309a58690340448030050806040c1c0b5a21443d1010015003500091200c4c04000001c0107c00314441d00242017800480c0c003000241032500250740981884030400e88036100507130f90020000020581100c800e04003602201810381803801400140ea5254014600300490382c6901d031942003003030009231040100a490b0b0004908803403040117400464500640e903c4910003000580402480070400c00c0c40705 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 55413187 1250 55411937 55411949
    0x60a0f020c0a0611060106020c061611090c0304060c02030f0409090c0317070506011202060702010c1401140109050703060e011809050d020607200705010e010201020c060a0b0414061e0604 82
    0x54030350300207426500114056444d1804c4419156680c1e00e81c24261381d144000c0c00c1040d0082e0040210070342d82c00b8035001c15032042c1e00c82c94035031407000d1141c000980e0700d85040d1642040300c0c0c40041404104441403241d0307500c448480c0080e5080060b00f0b80c0d510b070180580d00c01c101019407a80765003030420800c042040e02441d07000c03a1860b07044102d4010151142c0090758126691300c030709000841d80c2061516001d140f03a6004150910340f0505a004580707086162008840030700d8040d1001d07602c44000c1c01024401d21091042500315850498448150713240a0700c200f0506141c2081806080200e411107070644002038076280d170b070b10484139042c4002d01200001030007a00070b41d1f903041006640410b4050160703040343c0c0c880d80e03840780e600d081c0001401c01020381511644404130410595020b09106103055105000050415200019640c10024119844400d255654072076030402d1401e40728941420146101c090903600c1c7c1000855441401c440310511414803101100b800359442c0001c440180030 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 55414437 1250 55413187 55413199
    0x908041716080c01090f030c2c040506060117040209151315060207050a081b04020f0a02010507020f070609180b0604121a04080702130b0a0609081506060a0f020c 71
    0x40c0e00c0907450707181c10307a0240f03280c00201200000a07030506c00c038102c04150380d04540810394941c5003030030140103a8502c071440d04896400300c9104940b4440c98150f81d20030ba0242015003031514142c0001011070b5428a6a6175080e44068140000358076030b64215030340102c4100d0100e050040520015006010803920390403041c0c10306036541c2d1450901c1c080fa030121400c0f5022140680d4640c2d0030010400d401e030084035400d0740800f011900c2c9201c0744010244411014000519000c4d1150200950740c0c0314030898000742c2c1d112010f101c8116070411001c0ca882d003030f03000900f2060f41080c0740180724420398420b00303286800000b00060356407645d0744060718070040100038a030f681c1c0c1d03644009040d4030440b010507140121002c42d201c1041c0b0281c0d01c020310a5078007002007441c1500030382c00c00800c1944d032044444c8059644403400295124000000c015000139160840c50f1450401c03420720b44441d07049104500000c1071306003e0161541401d03282001d690b0704021404030301c0c0d00800c91401c00d4800c003c41d4001 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 55415687 1250 55414437 55414439
    0x3040f03021222050102030c030a050a1202070501090b0703050c0d09050f06010e0f070e01081f030b0106051e18090c0c0d0c05150106080606090d02030106030302010b010207090908041716 82
    0x2404601426a034085030b220b840e0483c90b9030300016a12030040071b4240c00150410400f14a03401c0c03144004068100007070806038036007007003c01454202c0e0004002202c1c1a0746d51a07102c0e0034002c050600c00c2c0c2c401a51300d410b000038944206404410b0007106400b900031911040090100101845104400910305044a0940d0b9540d20048150300080c0c1e142600310000d0000324070082d1040810950801c0182c64250040c0c482b1340349103128004440705c4500d000090b080200000300c5001010b8000c054540d211500c1e0021080c4c6440151141501c024400004005c451042085d000c0041204802140c1c2c0052aa0312032141c0c00c3ca501c034480c03414810340100e2205100b01034015490308010b5000318100c5184248842e60b0007000f030802c0c0a08004181403800003910b80c5000c000403d000343c1c003d0000e030204d4243e80e0110f4251101138200300c025075103804c4074500c95681040220000d103085801802005040d403100b106a208502071005400d0182406400c180b43c10070101c1c6e004030000840d200c0301 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 55416937 1250 55415687 55415707
    0x13020c0c040e070f0609061e0309020d0302030c010606030509060a0203180601080601030c05030318130906060b0301051801030f0b0406230402090109020901080a0b030a020306010e040b010902030c03040f030212 92
    0x103404240914130000c0700b040c0d408a9034521801c04007040c1c55240d12603000031580841b040c1e400710406402c520800d612a003604005849001070003608510030340080d81c03036503400c101c205d0940ba000d80080f03041504c0c000803c030600100203003c98110380601d800581da502c540300a55061500c80d140b1607214440c0c41c000055100f0000b030102d040700d0050401c1100c1d0b41d00c460426031070703110700c0c2680b444101041803400614980524016015a040d000010780902c00b5900c42c2c0503680e407640800c01e1f505000c001004182400007401450000e9404452215810f40c4e80382040481a224040c00d07070201e03000010200601d90f4000d088540750400350444001d10342e03000302000381088404030b000740e61000c0009807094842c02542c03040c8005854000040c3c0d070300301145c0d000305640760300264103101c0c160f054009030710140800e030302a02c0d5150300000c0d00d1816040c6800500748c1130344002080c030320400801c051303134401d002507d400c0703944000c014400501c5d50508a2a00b20380304400180400001041451 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 55418187 1250 55416937 55416943
    0x20a080d031413020103050916060914040606080c090616050a03030e030c07060e0a0308030708100602070605220801051611010e03030103020607031b0c0e0f01030213020c0c040e 78
    0x9500e04555051104480900000c07800b00b1080d60380e480c44403040c810040040d80a41c00c003d40c001000021038907140302d82c00200c10301c01610740c00784c070110729442c0c1b0506c1070780c1000b15510071b13900c02528248116440e140c2c0003491448001c0c4000b030040000706401c01e00356203100440c0d02001d1040795035100300031641000c580701c00e80c0e00d03012000300f0300e00401d00d821070001000380d40e0030003d47d03409050703810b14154054818078401d510065200c48408804400954600051402400c2d0755444404502e0941c158444101568111106542c0001020030500354800304a50001c86102e810303840110340c090005011000c01d82148110394244020015960085210015103071a1a03450505003000c01751800c1c221034105a010446e60020001800903080c04001060050300ca0715001c1d0740d60804a001000307e4038401030480b20b518000c03400b001301c440346082007a00050010001140c952540e0300141949001c0e00020740c00c60740209160001c19000d104040025030b002e00184000c0c150918071310b031 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 55419437 1250 55418187 55418203
    0x2030604151e0c0201140405030a0f120212041403040305070605090d0605010b0d0b04022503050412050703030906020102090a0614090439050702040506150c060703290418020a08 78
    0x80107611b03116142c602048030302682030081e60040041d43c60400f141c801201d1b01200910100300740302e80c40b010094640071a2008210042c4080c8a801042c2054905010083d40c1554a12516401844103101007180461920100c80e45410300c1690b41030f00a0103d010348506640141c01c403450480001401b050420050805d015011410016001030b401000103c0c06038015a900c400b102c2440c04143c0d140003da4245078a002c3d0a0150030603030b0b0f5500c150310041c0308210441d0103401c000c00807c2015040060740300078201d140029030800d0409404206148120721a9100700048611745419002d01d100c00c5410640024005011030840d0083c0740c050840010890400e4000d455550070010003500301203840340080b41d464510f00b44440d02004003800c0041c10313069010040400c0080c03040040c5004100300b15102c03000c1c0090b8500b00303c016080340d202404050f000007014494044480c0d0691941c511182d04030740001c0d01c2403403c1c0200c4c000d0303170000e00e009403c400354040115007002c00040002c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 55420687 1250 55419437 55419461
    0x5060f0d140d092103091512050a09031707030f020d021309060e04060218040501170705370504090305070c120f02040b040f02030a0f0509060402030604151e 69
    0x103030b000d103407004046481da603140c814144080d00c0582c4810f00c4136000346906401c1c602900d44064815202e0400a0341034500810080c040317201c2c002c4802c00d0308141e00840f41d1003440308004000c03040c0709d2b440c00341480d280442100443c15080c00083d482038040d034404d81c1207280d9028110b4640c5c42c5107200340020b6000c0702e90a035104100a200141442050040f031056901526100e0b015803910b40d00c01020b50442c0341c000d280e02e64100740c54020b544441c03185a00802040070034006030607194030f00da800c1088a81245000d6036142040030000c01003081c05d01504a00504040000c0381965221300c01d210650f040280c0c0681070000e0381081c0345d4098040d05d0703c5809603a810842640e604039180045036444001488400c0c1668401c0143c40c107503002030a507880150000c9200120810440102da1040b00c4080456603038000189803c00c0501c1125800746e044802000c540c10503800282da5448020030043c00c0310912101041c85041c1c03078001300c0d16800c2030704245022075404030340c59000d824548060307 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 55421937 1250 55420687 55420693
    0x301120201020f070317030702190c0302010e030604240603020a0303050304050f030a120218030d110d020c060d050402030a080c07091803090302010503060a0b03100302121203060405060f0d14 84
    0x40b1060f10404180601226840406944078801061b000422500000d1071402980903e56041c5107013560381104d224424800c02d0103a00c120300318800504901c81321414640268030680030040000e0361403140d0141e00c00b4803a0041c1c600707151104410701038041504029004071402400200301600200591b000740e200b101514002c140c3c070900a607890140d00b030080000380d083d1043c0a01031050b640140300700410000840742c03c0111b0408a8585900c451710031000031004003c151800c4010700c0b82c0d40005a071071001c0c0465011000000d0481d004440641480b5903954010404642d0100001c4101c0b1f9800120703940c0b10700800700880e032140640d114540019080c44102e8071800020000c201003d80d25071961903041e803e50300116000c2d0801041d0f035400c140d00f940c2c040b0340b40c048817010310702c07480d290f040302e101060a40c410301c0312045402340ca1080c0c41c0e00c0701d4042d4030009500e006895014405a070b0003d003d81c0d43c0c0c030000300b44014410500340c201c83c04840c0b40b424800e2600b4007845001d50b040032 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 55423187 1250 55421937 55421953
    0x150207150b011e02070501050912190c0605040506030402040e2103070e010e030a1b050307120c08011e18120e09010509070c0b0a06050a06050a080109020304020a030807051002030112020102 83
    0xc607244030f4010002c0f5000581020205124560254019248249018041405940d41c0700140c602c0c140d4482518000800d0b103e01c1c1004012400380713002c02500c81441c0142c246894540414814000039200902c2183c841c0c200410f2802c0c2003014181507003010070b4008001404462864081c0e00076035074034000550b11404d00d80c0360350103200d4000175180080c00400d55040540c031048600484609980300300e00d01d04000180c1d03036804100c210003401e40c1c40012482c504580c68102d144220b036a000300d0b56a410320b0109041c40c44030801c9084c3c031500006011849910112041c0f00d0005c003004000c00000c1588910980d05500024410380c2d0704003540c04c0141640c86800b04414180e00712840d400185002d2008000980a1210550070401000000c240d1580700c1c0c000a42c41c401907000000045d0010481c1014150300c03400e250300500c4107010441c035505203034012a101d010709000140c507000c00000e28401308803003000300140c015582d000031920303940c56080c43d04000c034480324107a00602c60540 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 55424437 1250 55423187 55423217
    0x91201020703260c0706050a0e01110c100606020c19030b0c091201050c190207080304030807150501050105161112011b1110111308070501081501020604150207150b01 73
    0xf2001d405201154102c90821032590765060180800400304402c0d140c8600c42000400b40c03d02a8851540e4011425902c410060082c0391a01ca91156001c1c4550f0403c982000780703e4010400341a03091094840c1c0c000c40106012240c100c41c900c0e48000d110a41404c1000080f00c084400b4103154841191910080070b40d07952680d0a0368016501d00820b51401c020820340390125540a2104801d180169055031b80c0e50040c03241507401650054900c0280020031604002a2810401c10030801c190100401c2d410500000d04901803d902c0d025040044800035081c48030200c111400e04200a0040c1c8010700300a40c118060100f890449441ca42014030032450b050140c24421003410b041402007038859482800a006070401200c0b6a0710f1200411903440c050184541400103000c1000c020305005103454001861444000c020ec4a1046c0349d0a8280c5160f90110307006410981000c10803807000300d60f00c1501c0007032080010080403079203e4405201e03441c216402082d14488262150120022442 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 55425687 1250 55424437 55424507
    0xc090c0207050112061d0a0b01090f06030c03180507091808070206030402060c0f0a03020d210c0504170a1208010807031e080307030902130c050906091201020703 71
    0x1006409600007580900c01540300b0908a41e000b500c60790041100e036503034581015960070140b8040200303a00d6408004030344180f8001d91561002c28a800c000e618540038401a00c10198003e900c20541c036642e6207080e0a04c03070b810124400441032501c032050941791038a076646440d50301c1212000390500020052540a80250700329880c1c0021015107880052f5003000295480104203d0340314400b80000c0c68490001c000c2c0503040d01190005020728011410060b03d0040d03c0d02c1c440b0200900c48495a23500c030000f019031000c4540700c50317000c00c251000403000d440c24083c64107e1154070b070480b201c448141c203000600343e0b0458000d0707000d031a400008040c2124000003d01403181d156201610410010360070206c01c00b1407845082c84a071401c00107958911481d070050b6080c40c0003070344614a44003546001c400d000884070b8079020412500400480c050700e04c0c0034101c7d020f0310401c03012501044540703800301d1108c14012410000c56036a1007900e4040e00480d92114000000e00a01da00210301c86045 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 55426937 1250 55425687 55425701
    0x50f160905010c03050913020f13050904080a03020c0c030f0312010f0506120705070b0f010e060d0c060c05030705120a080109020c12090609100f02010b0924010c080301060801030c09 80
    0x40c0e40d24111800103403801c5c1c605c0d80c040301c0300d503412004101000c43d04010070b1014066407664500e00950380c4e903a050044041640f84d802031031240e02900140400101c20004584048019050242e1510048004141425050010942c042c02031040c07107a40110080300401e001c0c0d412849140c01c590b00e507610403601240c207020702c581202d010028108076a4202c0c28107035200745585065843e010640d039928446030000d0303841c19000d0051500500030b0000b03e510071648520240d9032200454440e8076410000c0c0b503075108281c1400070030b07121507090107418000c0781c0c0d0140d002000c54490010b9098003070034a034013840c1448002008940003082c0000e0900840d230300783d03c80c0f0f00200300d60100e18280003010ba0050364a90360105080003500b01c161128200e081d10940252510034482030f0b8802d0190070340710f0070351809206011042c00c2050868145000f035010000c800e07141513440d01c40000503502c5012218025068440110000a5856100100fa17044c1e0388102c000fa9443d0ba520f403140410b41e001 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 55428187 1250 55426937 55426939
    0x12090a060e010b0a121a09030c0109060902010f081b0c072c0606030108060109021b0d03060515070203030301030803070e090109150e040b0f0417040801020405040b0303042108070204050f160905 85
    0x5505850201004001b10150015100b201396450100d60303295913400c40d42a400b04139003136034071040c2040c155078005965008100b80da06201500e0304e0006014949915022130300102c0307200200355010018800c020b2440038100229500340b100c0301108101c4440081c8035403000c4030404071000540542007501c00e0700e040300d00c00e5004000071707420400ca00d40a900640c01c4040218a000e00d4001211020000a100c1604584002414a080205001203010f00000815038101c00b003001c4001a1400011241140d8001c0382460702c0740c40380b4000700c8101c015a800c0d40da00071580400400c1c40d201691014003107003605090705401d2a40d0312204912924200c1c0c015101c0b544010010f0328000080c0341465000e8451598042a29514440c1a41030381168001d102142e50216051107242005c2c4580320b1604c3e8114021030819141480d500c0d070311414601043c40019103400108100b00300c03102503031001035000b07209001034a443c60a500d00d20030204c503200d0f162501803102c2800706005000c05025204 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 55429437 1250 55428187 55428203
    0x609030b1302130b0114030403030903110309010c08030901150305030a02070e1509041103010c020d02010b030309060a050a4803230409110304030f030b0612090a060e010b0a12 77
    0x325043d00303072000381111882c56041c0504041c400920b00c054200444c4194032a03100000c0b03032000781c140100b02d0f045418400341c80354001c0255a03420f0b07800030108204c5a40c4880560b503a51b07112003155001d0541980c0c00b040d0b51980200120810078040084d1034082c0066084030480c60740c983c0d450b507443c08181c50784075698030ba117881b0483d103045c8891141d40c0140a1444084d00013666404642180c500e2030308500160003602542503080e50a0141031a8180b0032401581406403800014080c0d114450340d41d07043c858002210345105006c0c0c14143c1594083c2c80c44c40c03030f80c051220402c290340f040d030061900300e4455880414400c0148030301a030000c15015640e18a407500c1e1107066100c2190074400000001c28140300000c0c14903250f008200011454002c1d26813641031030302d40905404820f81c02e0005050814081c4170b0f4a07218102035401030001d4100752202a00c0d900d103458113100000401601890900c1134001041c0c10540041a02c1d0030240c0701326640319610340503110703820b00812004100032 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 55430687 1250 55429437 55429459
    0x21203030708060909011b020d090501080105030627030408010603060c03150603020c030c16030b010e010305060604050a060509090606090a091a0603070f03030e0102010c141603030b06040609030b1302 88
    0x804d004100d1944080c58800008078518840008501c5e40c440e00100720040e4050301c103042a4a9114945000414081c24510341650401002a0312500010007110000c010301c910800c0c002100c61a41460040000c2601c1c0e903a44c41d00c0c2e110740642094001a40d101e41081110b08030b1500c00c0c80344a4115140b03081c00c950b0541000d04c114040d601500c510b0307a180c4014401c12422600034070486808810020764203600b5840d529000d80b85a0050780082107204d086c9004001040c03011038010341c4402e04440c0050983d5448111400400240c1c001a800c629140c04000c00c6440000d400c9005600484010025681e8007000c0015102c4540009082e81c0080c0360408581210b00001d0350800401800d0740d5520782c44402d4031420040b65401600000d201c50400351503540c0a103d60001e4900e03924001da05010141c2a2908511406104c88420400c600b410401d0520942c86001011401840940d03141c0e6155402021f00315076000940d0407400c2e442c0810342c07103080e00007890425940078104032813903 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 55431937 1250 55430687 55430689
    0x105010c030c050309040e0708011a0120190602090f030f03041e030605040b01030b16080606070201030e06090c130c08010b07050106090f0c02010b0a050603130c0503070b0702120303070806 83
    0x607030310180210b41604c82805107000540d124062076100c01c03291401000d0051501d94041d082d250302c200e00340403040c144680d8807490f0360f0150b888a00141410f407040d004203c4030703210f42c0c900a04e10f01c0310b400d003034561002402000750a800415020b44d007203030700d0a4201034000c1019100c2b10b1203206d42c00346500810040000340040c000201da9210b10351119001c00350380344c40340380680d041194212410303030341400180704008040c0445a00b22580340380446588035400c002511001014111520480000c0b48030301c11a0f100340c0000407440003a105549180c02c082445a503900c440342e0b0498402d0755002034044004c000b81c07040d01400700300c55030742c04142c3c0d02c0d1030310080803030744a00c0c0242c070155281d040c0800d0000c00382c061040c50003030f402c00010b05001c3d04000282120081400b062080715201000c01c0550341d5036051701c1c2c020030325072183c500c8000c261900e043c607a0080c0e449950103000e1003034000780c40603941014080141c001e42d5040240c2c91090700c903e0702c0344011181400840e4100700400d850b = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 55433187 1250 55431937 55431947
    0x7030c260319060b0c0f150606030103020618030a140d111902011101090c0303140306010c061805070e06010206090d080a0207030909091b050102030414042a1e05030105010c03 77
    0x10000384020b00003042074841c0340c05001a440380051080071340c0030a02100e0f003450200501000c5940c03e1640003030505010000507103a20062002030310500b00481e40c840021101108041050f200070100d039400b0300c661a000070320360810103507200f450041041c1841c500b8007851030100d403848514003400500c60601c2d0f20807020410486d0030fa04002c11103406000341102445066070003802a408481941d142d80340c01402004e81c1d0ba20904001400e0042c0841ca98104151107003c0354020b601040b450011201c040c406e07000504040e00c1c9100307206001807070301040c92141c0e00070a02a42596103968880c0603032a40c6180e0028450300080d41c0c07030002181c1040503800b8180c19442480d091108940c2c8511400955844030350a0340c1c000400c01520b010360f0b10403075186000704000c1c0091400d0501d003100b0101c00788954000d5030b0040e91030740e10203529015050003018041820040425a40c1d2031840000c040200c21040199195803000380c5450041c094020351781210b00c140e44080c01507210f076030110341c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 55434437 1250 55433187 55433221
    0x9030c0409080c03071110050f0a080711030f070203100e0a030c020303040b0f130602190602090a030204060b0d05010806010b03180111030702010e15040c15050f07030c2603 76
    0x1480c41043c04241d0703440e0400d100401c04113000369110401540940c2c04c214080c03820300e00c02d070113211007084001504800307041034468440442c140140141e42d5a0310070340b000384100b90f40321070a0000245211fa1500c912020f8102e8600980c102c0e100500d200400c001201c0148050780e045a124141180020740f03e05d80c01150907102034156800c260703950420720301c950000c105505404401096152800020b07000b842d005140920080c2142c9901d0040d941860041100140525400040c540256100c102040000315800b4100300007190b030b90622180d5542002e501003000608250002603c943c00042c40380c142c030032400b4440e00c0d54846602c0b0300e40c05103d8610141d041c0d502e03144244411501c488c0035502c514429000881c00d98901c0650340e08000e0014012160303500b40106010200e1102a8900b00ba0341c4a60b032200e9445804603410744580c01201441012204005074013000c055010300507a07503d0340318201e807201d1407222010480004000c464035070341e2003005100042e41c1e07131400000b1403 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 55435687 1250 55434437 55434443
    0x40323061b09040c03050f060103050408040603020d02070206030406020310080304030201090e0702160b04050102100e07090b0111070306020d0f022118070305060906070207060f0c1a15040b0609030c0409 89
    0x1c1c0c6007410741400f02d41554202d64400020960715820400c0503040004020b034410424a8104098a095600c18030729004500817501015408290b200c02c803800d40d4121000d00d60000d10458981c5810300d4120080e5000303d600094000345264000345194000042d00c0a8950584035481102e007460910700104000400d00d108520804504030030f68905550f000300600800061183d480b4140000079152030180c1030754000e490f00c3e0020303400310101c0100720310041d40d900d0240410110501d90040340d50800f40381450400380541c101c0003080054660007807580d50121601071100352460702040703003240110700c0c05805448031901800e041c00801c020035a0300c01d50300a400c0c1c10079001018154540100c07500111361603480315041c4090729804002c81644043c1520040c0b5850b401e00e40e000b44450350a0f568601800551004001004699032200700e4030098106940ca05150509511010107983c0f00964015441c09841c80c0071130900c4800c44410b20005402014031071501c0042c4801480000425 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 55436937 1250 55435687 55435741
    0xb010b0a050f07060b030c12190f0503030a0b040b01030507120e03040902040611100908070f060209100201020a080105031b09090a0203060f040b06031903050306030a05011104032306 80
    0x9490810b800003900c0024041d0100142001c4104185454a0302c00c8840a1003213040b1011454010350014008001c8010b00d40800034800c0c8504c1c003030006500c2904000c2160002004100c4030361941d5101c000d106001711402d108c0c401800005500303e84050305c680700026000b680c85180e01e911a000301c14801d028500f04c03890710344d440307a0b0f2400b20b070800c0d04542d0002c1e0020324148040070042104440031030000303d0811642603c0e5698030000c4c4100b01d00203003000111480e501c144400d55040c0e40c50120003610076402c1e042181c1d1300030700039131107051000c0208001701c0010900d418001098800039801843c460031034401142001140301d00206004018451003080c0801a1020320405004404e410070198240c2454584006822802050b0f0f60103580480204642403124402c180100e0b900341c00d21560726243c58003c41e080900610b809001342d0308103024400200c140c1030007442164000c2000b01002012500c021b055242900e000c206103a2012021843c9100d07449140c403101c10360036040c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 55438187 1250 55436937 55436947
    0x51c0f1e11030a03020703031d0309150c1516090503030919031a06150f030f1e1f0e0c0703030b01200a060e0307020a030b0603190b0703060b070b010b0a05 68
    0x20b032459016194410020b41c000c1040c004250f058001ca1a2414010b0641c210038036084903010385d01e00402040034400c0e11505002c849480c50241169000032101060f41c400720710460001001c003078140c41c40c802e0550300f1054031300c40f5486500920306954004019500d0109510200513500c4034500d0f0121481824031000000a41030514210043d40d00f506100d1507441e1100800c04210300303049004131040f804100c0f41403181201c0c01101c5d48080301ea5103002c200d444000142c6040881c0700d214214002c007000a103c5143c07500341c55085000020140c1503420341d101c184201c440c240c199280501d0390350621180b130000e0301a400910102e84d0600d0080b0741c80da045444c22800d0051076540c2c04154001d00035400c1801441c0c05010317003c3e204107004514000f819030108901e03110701e00c0040c01d544102c0012964566050040b00b0f0710b0319070400103d0b01801903081445810005079002e0010070f140410004a80d011002a41c45c3c2c144c100f29100c4281c6e1900c0500c0030603900c121403042c204541040 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 55439437 1250 55438187 55438217
    0xc03060a0501141c05040203010e030c03040519030204053c0a09050115120308100501080402040e010f110405180601020a030324060c060501090501080d0e060903010603051c0f1e 78
    0x7009075048034803040301103006d040c140145400c64040d8450900a5041000000140c0030700000700c4013101c0c400e035a8200482d1101e045202201c000343c20081d030013418030f07040c8240340081c000307000034a0984400b22001510100c441c9107610b002d02e480e24104030555000180d9641d0268072000840b8010000403981d200c0c2c8162400e0320590310b41060450a26080200c02850743c401c1889a06c0585001050324250502c0e001034007108006200910554581951149005e420340001c1044107003001c0c01d201c0840c010140500b036401c6070160310301803160205600344140304900ba9078001c22046e0003a007114881518120098070b50300100e60003289283c0100003401c3d000550390801010f9503a9010405941440c140082c1c0390180d029081070f90030440180135014000c1000505a6545e0401c2071724900c0090225203203002d0741629541c95464928004144040031943d61895026840d43c01c1c183c140395201a554000d047c1c4601c000240301800c2140240c0400c0c04404803d4110f00b000101150030f95 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 55440687 1250 55439437 55439467
    0xb0d021203030712060b090d0201020723181b0a0219060e060708060109051e0411030910020a021b010e0301060803041403150601051c0501080a03080c03060a050114 72
    0x414100296030001007080410f580c0801040601d0035504c5041c080c541c0342411111941c0a2403940e10311601a0219a40071680208a040c00038408001c6101c01c90b071410407540b4843c003600c05120b00500701018088030320b50042c2603a40c482c0e42c001c52040e02c802c3d59605c001d02242c00c806094029403150030b41d00140c0130b0001c0c102c842000c1c4240004034000300c2b00121745013410000b6003400180f04135842880380c203a800c0710030581654415102c81c0002d440703020b90307580458120705140b90800d1500c2c09007441c00301c000780214070688241c001c450300c01c0c8012041c0c40403031180c0865500160080d0702c11244d2081c990351008007140c014589000c0d00c1c4140e00000382115501d501005ca207920015040140801c6800c02e03000c080d20403000b40c2342c01e426001505101d404010145030400c000000d07110891010601092180e1241c0c10003000701e503071a20b2849a44040c1c0300016070101d22080005020345400100300ca01c43c42c0d000d0880065945000019a401d61100c0e5000161070401c0c410b01c0d000c98404 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 55441937 1250 55440687 55440709
    0x50901030803100f1e06030903020d080702010f0f0c020d0f140711060307030603060b01020718050702030c1507030b04060503100507031113140d0b07050f07080f071104180201030b0d02 81
    0xb04d01c1301c5c04003c0d5558a049240301d40d81c4a44141420801400042038001c5280341800c2c11900380303d1203542d20480300f00c1c01055200210b0060915141c0c040084089a82c81102c0f02c1016400303c1d1030f100c0c00000165808050729203000009000c500c0d92048402004024183e0b29105800c0d01456144402c00180150012103107580043d940b94410024048103000301c4290312000e0002e48841c4c1d0500c1240644240c10b4820040501d44481c04030f180300f4420012542201c44000640309100040c4103000240b5800395002d400003424500d11690301d107024421181103902c01002040360031070001600010340300c010700c8841403641c0c400d844844c0c211003400030410702d008605200c1c989410000ca094006550740e14507406034844150340400156800320681e0081c006080503a00e070000040b680401e4460740c403004061084c04110403100019170009002c0c1c0601c90b0001058100c14a81807008566110480744241c0c507090411202550081c0d00401441101030031860409241d41c02080840940d = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 55443187 1250 55441937 55441949
    0x2040908041409150f0405040f02100804120f050403140709150503061803040e09030702060403060219030b0604140103020c0304030308040308070c0203060105120319030204140a050901030803100f 86
    0x1184030b03160661608851550388049401c0104845024282c080303200000c003406400d00071543e032804036081c081514042c0548581c010483c4941c04407ea00c010860300d8191011141d2841865801c1000742c041c56000c5030300c501c2d1740e641e039003403030b1858486079040f41d5212008082401a4003020800000500545442c401040f01a0749070a10380301c2814940f282c01030804662600400349404040800300440b01100c0170b6621b940d0094840c4031207541144076144000f548042c000a000081204607006401c0080c43e4091180b20755000072400d0301540ca810044a6010034204130500c002007403030003490020003040c98014280f44011500382c0c1395906c19003099001c81d01c01020003080540c003c081651049003440d1611052980b580400d984031010b0040b6441100f42c05003180d030340720f006c04c1500e602031904407035201420004400038000758402e025801e03d20b668084820990704003072140c001101c4010789094003a81c610340b2403a52a40014050960080d1039050020f0500c002071060009407007 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 55444437 1250 55443187 55443209
    0x61e0501060906140403020d020904141c0908060609010e0a09150f05060604120b070c080a08010302031905190507080a08040603061203050a0804080c24010f0e070c0204090804 77
    0x410031030302604c002c103030600360400719404100501c01600e0301d501a4504c0c581c143d50050203601c1e580b5061484400b00d0781c5001c1c00b4411100c500a643c950081400c807a024030361500c024a60700d40780e4103511402c0844105800804450042000225540c3c10780d5008a048a0001d40701d401e9943d41d1442d8850403070f100010070703152446411300701083c0c0303c1c5e2501302500312140b5281178540103841144d42400c80f8082c10010440c40007840b040d00030010142c01c6640a0718640d514040c680e0301400141d000c0c0400d901903c5450740c1c03d408580c4041c00c0701c12598001d002030044c1e5030003100358036010380d401004a03618020030300009100102000347d4010644180241074132681411f200a0440b407155021100902c001c80001001c290000101c0340b81d41e03810b250068080e89c0c1c1d410041c01d1442000340c00907980c819890942011880340c00c00900d403202d03543c440c1e9101c0e40d80c0c106003401482d45000e8044100b003201c01062000d1300850380700351007510181021030b5070130080e00d602050340c209502c4241c1000b = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 55445687 1250 55444437 55444439
    0x703020307110108040c03080a020a0602030a0212090f0703140a0602032404020703050d020d0b0a080703060e060105102001050c0d0f05070f0c060f0e0c0118080307061e05010609 78
    0x50000350042c251042880d01000c2071a0641b941600c0c0c4a9a2102034010280014140e20240c030a0050003800d0341c2111042d5568244900f448000303500400b0210610300c07841000c15a0b01e00041030b07042641045500030085142141c895036803181100414900c20f01c54018800002642400510b1142d1001500640b42244d0740a10380c3c018000d117040e03148101d1041140c080060342100c20341c0c170b1081d20401e00680b2080021140307401440c82e100090f07807108000400240c10b0301c0020380c00041ea48200f20500c402c03141c1446081d6240e000f80116a449030030401c80241d200c1c4aa0074043d4041105482400e66000358004542110030035a003640c22403600240c010004c1c0614000c1c2d45101e42010020445440d02100c01481c0090281c4c0c0c0004100e80c0400500034005145c000c008244100c420400003c00040e0710b640d031790130407103143e140414090404038442d07103803140180742101c414070091071900155640e03820060015865034096000203452a0380342c031146201d086e011740717030b0398480c50041 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 55446937 1250 55445687 55445693
    0x5040501021b030301050d0b0604150905190203060a0501031e020a03060515032406130801020a1701060c080d0204150c051204080a020f010207082b030e0606011101110703020307 78
    0x41003003110407101c0d80c0f040004210030b845484000040680000c0400683e443c7c1038002005010b0101d181c80381928841c07804201d8500c6540124064070001452401034000440c81c00140d00046450070b45c801c541807410402c550180d008180b00030641085003031240d01c01e8204c90100c0c0c00c00d884d00c0c8006aa10340050015050103500c095604178880c0005082d4901011300300f00340d900403e18412240e100f0b680c040c00a441c1c0809a465140a095000640d0307625004000c1c002d400400c0c0c0000050041341048074030b4040d4011543c16244660358085c44036907641c8980303819600c0b10360100c401960030000060340c0c804c040d0131464090300c2545c520340100c00354106103141c03c0700f003510305160040401c020081c1040000301e02c0101c0e681500c01c2c440f40490100140e09000c00d643c0508054080d0644030580e0040004136003041101c0c181c40700c0355842141d41e0071403c0b200c0d03000010160358000fa01040300fa40c080d100409a11510800210300c40003408452003044d000300800b2000750780082051010 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 55448187 1250 55446937 55446967
    0x1806040b010507050607031508071d0c070c0e040c0302060309010b0301050603010b03190c0b1303050f061e040c0b0406020a060f0b03030307080a061214100902011d01030b040504050102 81
    0x40092901c1424108544c44064440b00c000e00414140765584140e45500350001d0106070050004a060310499030740d03160a0303206039a110f405c02025580520000b4a0f1110203416500007a4000c41c41c030040382c0c01e285400109400240091b01d161032800e00010044e95848019881114124008528601a4414507007521b02c040c0409120340d040c8558a513035610006202c2c6c000b03103e8034402a81019240c00d2900001c0c000d1782000054807030000c0c401c88480e42a40030182101e1044e011210000c0c03102c86a2919030a041da00f03200b040105021000400c1d400c0045950014000c00c1707880000c90b0303a464100c00590096020b42c0150300075190700d005000c01c0344120030746000c501e4018003225000b040041d0b107030310004081c142403020b054081144015244d101c10080c10680c500800e0104440c04c140e0351409682191b00058070442d401000901a9801202c10096040e150003440c2020140e04c0c6c405404906103140c1010740d1907207440499a624001c1600460040c400140c1d11000c0c4800720718 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 55449437 1250 55448187 55448201
    0x303090605030a09120c15110a0e04020c010501030b040b0c040602120307053c07020d080a090807030305090a080c010c0602090d0f0c09110c1c0c0b0702061501020f0a0f060902180604 80
    0x161800201042305410f0f07000700c80c4e0440c15481d000d005500c100e00000c00170b0182c400244169881c12002104000103661503602a41c05601c1d92601640ca403901c12289124a000c1d03180103801c44545501900d0001c809181c002100381009818108402100900040710a10400394500300588051412120010760700285250b004030354601701581e008925054051880101651301c0002c0d81092184680c20f5000641403d10075100d14a681c0e080040407130700104c09040c40303001081c8001400c0c100014034002d502c501a1283c44400f540c54403404000c0d040540100d0b081200a00400e0004c2c0e08552a080524820090101c40504001c0d14104560304017280242c558010490001080d2001480f0a00360219403500f03500044401c100f01c812401c810001000301c40c030082400f0300141c003c11321601c80d8802000500074807400200490b90741c60300c140d001e212504602001c0303020a440d00c942c0504035024510201d80324160380e002c5000001c8041c43d48800702e001a051088030b15050082038 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 55450687 1250 55449437 55449473
    0x206070c0e01170a08030a0b0a14011814010e210601090b06040501080109090c15110d0305011419050a080706020105070212090d05010b090a02040302010e0a0303090605030a09120c 79
    0x14481022143c0754903035030b1070104c82c0a090307102c001c00050000d194540014a8070180508500c045c82c0d501c01c00c4190000c10049901c0c0400c0d00f0103126520404801c8211084480d4042005100c2d8141c10055640c0d1f0501a2465008007a900040040c0c04c1a10b50300c00b039950400c002040345614000070784085964041c091842044200800c0005a070300c44410760545040d02c0d800a078010303280c0f506604100301c07a4040e00d2603030226410610320743c0e085030080c90700f80e80c54410f990f21807003003078011022984240614011310580c180c0080060600380c41c140d5070b50303400141c409640360f140c46c00210000350640c014110780e40051410311006a080c014107070400510f000030014030141400d00c0c0c0c50750158034155405800c0c400101814803409410803107407160082d100c40707518285440894044d51050009a02054000c80c4000c0316007008001c8208480e09541d40c02c80c51814441c044655902c05841d5500d155280c412142c003041215a0800800810342c8805405180c10f280c081a2122015290 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 55451937 1250 55450687 55450709
    0xf0806040308220c0b070209090601030b160302130e16080702070504090303090b1008070b16121710260706050306061b01090201020f0a11040504030c0206070c0e01 72
    0x8031000a8114003816041075112000c0401e4020340c48540098400310007000c1d0504400d4200010300e408940000c28440e4005e41e801d13401c543e078210200b59144000e10000700b00301c4407000019841c2e10000c0c0031056107501c0c0c0ca07001d4039040c0702205244401e04103800003954060795000b888421002c40d41d912404100600f08510b5602c0e0100d0040e440f0745443c0b1620707000b40d40b179a1100d001c05110f98800d204c9154096603888503800c00303041030f01c07100b88503014003c00b9101c0e105000c0786c1040d021081d50041e0b42940c9507480c034821190b8640820b036440340c0c00030062018114101404940d0391018902c21100500c900d50400e2070661081042d43c01c40060f00c00310000c404510745051004110802580c0782070805968079103030b14011410360b11600360000c42641108000c4441e582c010742002e04518000d81c00c80da10002c8c2c000c40b06841e0031026000400007a00d80100841c0350415402880d03010f8043d06201040b250030b60081031003540601400c035403400b8007a100340800f158544807103024146480380c0c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 55453187 1250 55451937 55451941
    0xe0a1503050705012607030504110114090402070203120c061608070e0d05070503030706020909070302030c070b041a0f0603011103010605041419080f0106060302090f04020a0c080a090f0806 83
    0x2035581c0b100c005002d41410440e00c0c900301400000341c1d4010301c10f03040c42965404024039009000500a020580d421640c00c0080840300f019984140f02c030172050280852024500301d02541044002d500000040381c140c09058200740e0020041005000d203003205901401145c58100380040da42d03201031040074144000003040c4000181d028541a0b024001a2801402d500003414001d10b0f2244c40d80c02640d01d40b000080c1c82041050a801808440500740d80c22072260f11002e0098059010803101c00131055424072401020480500281d0381240c01041c0311409200c002c03045d03c4008004456000048502d4000c0c0001c90030709115600d0008155075504d81075504003003006006104030704c280d0b400e00d444910501610780c1c420038004804458600c924004c0e035511400c241d02c030f40c21030200314510351820900103449802802102c540d01d5000b003440c138001e1001020070000b07410011281e0100505c0a483d0340015820030001c1002d9680e548072002032510b0401840f01995960300511426088802 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 55454437 1250 55453187 55453193
    0x2071d0f0609061f0507060501090506060f0f09090c0702190e060103020901020f0f1f0c1209030e040f3206010c02010c06090309050f010c02010e0126010e0a1503 71
    0x1021070700100119501c5100c0e8403054001070803003038180210f40703400a003100e03219283c0d608071008003030141c81880280440e83e615407a406c111541160503030741160781045962031503c07542c801400c02006034800a4145040303000441c000e0030080b07400201e4848002610025490075490703900c4c000000d54805030025041c0300c81d04c603004d0340281c01603050540109070303401d0aa00030702944980701503a500721100d0325a1160816684c800c0b0070604807010300c0ca9500c80c0520b51850051a201c2c90075034960007904102c1380c00410003032090000907810012600c281012540e46c038011070b038500000d84c00c0841c10320400950940801050555100410345103402c005408141c00d00c0f00c1e910000900b0103015299403400169001e61800b072005080501d400a800201500080e0344020746030150303a50103030782c517450b401901c80149462001e40812040403039500598415403819080c030443c411982605040c4110580307101c42c2c20380150111003070303010801001c0742c0c007480342d64000701ba001d0b0254000352450b1 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 55455687 1250 55454437 55454461
    0x70f180207030e040e010b040e0d091a0306010c080c01021303021005070f12020c090f0403081b030f0604020c01090305030405060f010b0313030e0a090e0607030c0215100308070302071d 81
    0x2840da02840c1c680303005c1ea1249100b940703c02000e510240042c4007145151160315101c982600c2c010000c10940c8030003040401032002540c6920810580309072950b1146001950180d500c0350b0120381c0c5810030000482c0e584000c0c005480352610b1801001044c6040d03204210904001143c1101013110502050003c00c203060040b02d00d01d50002c0c003c0d0184088503004030309210030b9100c2c4a0300000107605208003080d0117580a0b105d0384c069074626515444416920b1040b10781c0a00d400c0c1d91680a01c049000943e6040e683d030781290b4028001072805040c14071050940d001c03068180c0c0452000310801040c0207003441020303403007180388501592035810846451440e000c041c2c00080d03075030b5100d01082c003014010300a044060200030b00c201100d640d601940c1c000746c010703101c800301c4e0743c002c0c0008103800e14060300810005000e19005440310648400002e821948020001141007185000001c0411080f200400c9240c1c0240d000d4958507040100189407250011000e1548015050030801d05c01404 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 55456937 1250 55455687 55455707
    0x807050f130306020708071103071503052701060f05040c02030406050a0306030b1503190309090e03090d050106060f020307050a1e0b0a020901020f0a02150f0408070f18020703 77
    0x52004940c541c98059004034800c0300382d80000f0301d02440040c0041c00c0c4040d140c041c240d00c41c81002064118469203090544411051040c6040c1543c00c220342c40c0e060740681c0259900081d0820000f044180c42e1110854140c20301282e84072036550388405000a0345d0000051000d00301c299001c0c860100c1e1010025920711540c0b1410042100c0031440c028914070039000700c401181c0010f68400315040012b0544072804c669001a88248208040d4054000400c584039030100d0305030700c9028285180c144420050800d10080c80c415000401104450303965034483c221151703018100000c1d400e420410041c094906d0184c444055610030701031840004d034009850301042e980441c03030b45010f08409500c0071032940030050080202d40800100300320008550b019188092090303080b01c0303001000501154030303852041c070040d4011258240029441c0903150040034212010401180b42c00e40e504603407414180c59170400c81d80e420450308100440c048140000f60382d2061101c04600d007051a40c0c001c0c5c410261 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 55458187 1250 55456937 55456957
    0x5090105060717040b0403050d03060801050421090810150e0412030b010e0d0303140105120714030a0506010609050901150518030c0301060f090509120304061107020a1205010507080705 81
    0x6580f943e0a11080e428050b00c0c0149200b4542c01d48544d1246409501c0d40700170310348200000e141607400140340a05008182c042e90b005182030019000000041040c0d90302c0c0c0080c0401c1c058006e100055010041100941ca04142e01300020061a4061040040310b5260b00504048070000b050001007550385041d45030b03080d0035080010f00107800038010b82c0d072a1509246c0a03481604480032000381034250f009031150203040d0424100580c1c031441000044100e1941da0380c41948201030038091000030000682c09200c008003142d690318219500c092408900741c11820006404d241c2c200213506180c4800c5015000e0a90b180c10507940e0000020010b005e44207824888128503030700d80d44d5a440c103001d141c416550281c02442010713100e4802003802c141c6485801ca40900c0c1170300154040305c000c661440346922040c0110301c0e58480703407680005041d03052500d02d03030100f007048841e0060391031000100c008c01644909074200390050a001d400c40714020100e03030620000710f0401910320303405402c03900d405038 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 55459437 1250 55458187 55458203
    0xd11071e03030b0d0302030d060905011a030907090518070b090f01081003020306011d060f0901180204050a150f020c0f22050c04080d020a020a030209040501020c0105011e050901050607 81
    0x5960408a010307000064100e13800c48012880309040c10703804001882c00301c178804000c0c441d15070380d0b100d0036040320024407070780040c1070800e4288400750740c01400460b000948041201e0300a526680c0340f20860300190341d0100c1c103480c2403808480002c000d1001d0f60040c840e00074ac250400c9007100c082060030740800041030401c0315410009050500142d01e07400503540140c11035025603102d2801c0c000303040700200e990118540d4140060700c0c501d000041621500c501130580406640b84c00408080f2001030804144620f0302840046960788954a03c08000c0c185120b042240c6801500050300010004004404542021000d100140c40385003440b12940000c1ea03500280d262074001c3c0302103210186480380d0440b401c10f803d200210f01d4810241094440c00010389542048143d02a41e507240383d84002900036844030410809803a2540c0000d42c454001ca00140c80c10175644012070031034909070090181d074403100c5d0300c25443d43c034140c800c034016200a8614500c65410100060803a0080060052110b1 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 55460687 1250 55459437 55459493
    0x30803040311061006020c090105060d050903040b12040303061d010311031002180909070303090504090606030615030b0c090915030c03070b030f1e041104060b07080d1107 75
    0x580701d42d100d50050340c4008140c8440b030a080c410710744e10b401c961060302d0040c480c0303901030020340c64800910f60481e04018201481c051060b664000600b1005104882502007808005178258055004011045080100590310720f410310f07014040f100b06801480120010345038581d070380f0b0440801d060661342c003d964101c4250403000000d10b060f05c8400c0d0489900d00100c1c1e0740c080d1444514008510020450b901d01e030640d40c003c07c4039503a04031448090b0005034546410442800d1980c440328000340143e10100c1d40070745070349401d400d03540c090700c0e500d0507440500420014001c00c10180b0b0703000303c2c0c014946860308001030b000a000c20006846c0b420403040080032000c481e03804000a0040001c05000c0c0da0105541b000c1148864204a400c1c51055504000003600483e0003040e000c1c2c0513156914418098803603455035080c41c0300c0c8001a54000b41c1e50100400c01400c4540907002013442020101d03a1214418450310665400c2151000000c20500a10700000ca5402ca038452210301c401640b0602 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 55461937 1250 55460687 55460693
    0x1f06140d08040b04090f050f090d030c05090d051b01030c05041e080a1401050a0501120b0601022a190302030a080c031c02030f100501090b070c081207030f08010f03080304 75
    0x34422540143c0c50004001400501c01042c0d402c0452100c00c0300c402000590340d00d820500d000002150079044540045490135003040c001e6000003074600d0145041402d2030300500c0860b944a90004003603405510646c242050840092441000310703c003840e0502400415000180c0a401940141c44240030304040a030700740c0d00c0410412009240d0001240d11a5082c1d00345910b60401c1405201c0c010350900c400076a51a8a81c061141260307000c506803600d84415440d581c030002c00c044c212038118000c2081080701c5800c01c08158a400f0b800b1040d10343c011441a040185144030f4450b0040c1c031001090301080940e40110381e0015140c2c00540c030f142e40e480000007850461190300b400c00180e441d50000042d100126030b022310b00c80e02c0d000c41d00c1d41242c1c03510140b107041c06009101c1c09001030708200b801d004002243d40035103842c5101300000761405480d8003c8030308011051030010a549030108000040c10703800401060806040e0524603000e5045c820100d010708101d01010704a10310002c01b090070 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 55463187 1250 55461937 55461953
    0x5100302062704061508011a030a05070c1a0717040b01060f0203040f081e0c030c01050d060e040f1205040602030304200301181101141209070302060c1f06140d 70
    0x800c03001030003003180a032a01c000c09240d401409a05e00003030780480000c43c1c1c2c25003500030504030005401505003103aa41425500191a008103400b00300420344130f01d940021980b007130740d81111050900396070151400781c400910f506071b21850101d6507101e84042c000818088681c140c15100d061074180d1407800342c0501030b071079031055900c80e4110035040a00010898000f1a51215030707801caa01400102015030702103584d50300c01e40c140540c99001030211400c02d6000300d0040074001300380e6001191865583c070181040711801c841c107450055444020f00100311443c02035136091300403810302c02e0904d410404003d40d01e0000420051048240d003160f00ca0000320390080170100302c0001c000b48040341d4603546210700d1841c1020100c0d5004a404d20242d440d40c040c04e00001c0ca885c04011890410380410412140900041c1040600d0b008940000c40540c40f003100600b40282c001004140901000020101841d029240000344500d800c10501c80305003e12084903007880105e03603a145100c03c500300000 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 55464437 1250 55463187 55463257
    0x80115050f12070f0f0e0f0f0a0b03090c0405010e2d190e0c01022104030b01120b01051c03030906110310090605040903090b070f02150c010510030206 66
    0x4a80760000c03840701401c1d2120105288200f0302a0343d0b6445800c055441500d1120360300690002140c40c0c04240d0015082031058078520800060909002500600108602d24043d800c034101c0d40310000200300c9480b00800400000607029038081041350b2502d03a0442203900054015a4210a40070761078000b0603100d16801d02505e000c4800100c02c0c01c02510055414400302001000d103800e107110303403e21a07804071381d840c084d080680180c2200d00c240c20030400e000e0184210502079850a100100c00f240a14002034007800150320b044250f150981017184203804140c0c000c42c0b0590400f1701d0f190200824010365400c0c95458140440c0c2c0800a03c0c0c000090000c82c90341a04614001c41042643c0d20300034020401c880c032a41040150f2a00c030000e0000b03030f0f0748002e005000b20304110b608000e4a04084010041c2e103003d2281e401c00510760383e0015510811048681d07000d031201180d10305200c842032094640010003440402031561440d0b01007801800f80c0940490341e650341c540b00824100b203c40460b0 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 55465687 1250 55464437 55464457
    0x2090411090f0402010e0901030503041401030912090e090303070c03110109050d02100c1e0e130203010605040306050108030a1727010204080d08011211040b0402030906010302090a02090108011505 86
    0x111035440e02c110007007010b8104540a900107541a0302c900703c141002c21805041c1c1e0f070010095490903042070f60200e074161020380f0050415a844003038030089100c000140d0000b04c901d507602000c00c2e207800d4064200d501e000c0c1c403142d4140c0003041441040758018003038134221507150030712040000746048524010700d100076015000d80240080c0c2100180e0105c0c017500c1006150780c040000808500044503605041c4034202d40408481100d8585c140c00f075400d80c0710014004082036541240b0b100c14505036002079000102190001c42c0038020040503000da98090f00414000758180020010020800301c5e4a03190715900403610008603008846200c002c1c0c0030f140d421041107192844200364103000754410b200307407a154060b9800c04000141300f807070325078100c0e6103003142001d10014644803045400d03920040d4560096a03410545040c4d00e80e0300182d8403c000310009054070750302d5401446003800c1e0082000908910410240d80e00340c0e0400d0b0080c0c19900450b400270600030031200b040d1080c2c41800094 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 55466937 1250 55465687 55465699
    0x10e1206090105070212160f0f050d02012c1506060f0708090a06090305060a0e1903050901030c02031c0218030f100b03120a0324090c17011202090411 66
    0x8005058150040c44c0106503950895038070042c000005030050081c1c800048084917a030310385078082040707203501c0b00c190b600981d00300c2840c000039900d140c80c02c070311904030030007503511240c0841083c01d01c40e48091450100700140e900d400e1070001c105403507805000d02d01040711043e0300440c8294455a06807030740c18110322105c81e43c8164904104105130031801030a442903034102c07170106500303100c0c44000c0112a804030003044141c41b00041130307001d0440414100414440c001494030360340030105044501d00c0c041d4440c3c903030302c9072004001401d6401e80c9080c1070079580100070f240c0b6507011020b44040d5012082a005840d02080c8152903190140160120360610942180100601000c101000019046802002803e41880905894030000c40e60513111100030300980d83c80318080e03007101c84091032903064144280d00135840424401e0458104040d0203549265598170381e82c1198140410892003c450500b0303615240d89405106087d10000340079502880106e0104541c0408403480c082c001810 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 55468187 1250 55466937 55466941
    0xb04060602010204140f0a0303200706050307030c0206090303070c0203030d050708190608030a03020c15010303020607090506130302060f040b0d02031e040b04020f0d050f10200306010e1206 83
    0x2d020350040c0c0580c2580460326690443e031031500b40c40c5410702c0caa0103082c802441d8a1920705030380c1405400c0f03041580d682252403c41c3d01c040f09211000203402c40d512240e8887c10031840003001c681d81c0e0703036414003554401c000f88441c403c00001500e43c450818075002890111501c0400c0c11801402c0442d52250f0521080c800030941003400c00d8400c128030241d491903000c3c01041d03101506c07a1480b80c00c1468000300701c0241d0040c0302e0380040070340b2050102180c0c060181d02e80022107582d000d80c0140c005800460500a5403179000c6020402000308442d03080c00e280740020340c80000c11241c4002403195100042900c031118103034080c3c0c2c0040003140f070016141c1100707000340c1d0080d500c02c984118520841c41484001000b25000c0140203a07045105011180d89580c240076603c0a0b84aa50b07910180103116800021030400c4041400040e0401a0652600d01d581081c241e03180c0d1409040e5581c0341035105010713546404140c80d840301092800811050481011840c41c1c0d00e8506c48050038042c001c2 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 55469437 1250 55468187 55468199
    0x70501020c030712020703030e040b04021c050403120e1c0e03030304060204030c050a0b070b060102030f0d0e0106060e0102060f060f1503091b0f0409080f0a20030307090512010b0406 80
    0x2000e081c0e0743d4014105407a40826116080340c0b207807000c1c00b00070081101c82490302c01c0350815038020000c1c198050300040c1b4080500c1c0c4190540c02d45150112820342d2560100000c0562004e814400040300e244284a80b010340c2c8110360b15805560386014104181c0190800308034400d5505125240014003a00c2d03503070606007420720107507000d80020350b41f4074604d000002c1c031800c00b1030300402150500c449641c2862540d903508031000320064903c0303046100074440a041300304100020800344060400008029828881e42c6007919410790041060010901f040c02840c2d8002c9001ca50003000290b4483c410381e10040003c001040003020720b50401904c0600d0076114036810021f46c02094314604980034070101068040420300a0001c968226030038a00c40e032061309040d00b248140621440143d400d00e46408030311001500502d228100142c0c448404000401d040184580d144014402962447c070b004680944003011903c60103001f40029942044100402c1d4040070000b54000c00c20310100303540312 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 55470687 1250 55469437 55469443
    0x209040b090607050301060503010302060d0e011104080105010801061d072a031106090c040c0c0f050703030f0e0a0e0411040c08090c0a030f0b06180108010606030b04020304030c0215070501020c 85
    0x407640d070018031855000c202030300d0051064034120380c0c05503119071845e030841c0c3c203001c40c40e0884c04070013101648030350000980003c02c0c042d0450841c05841d100d900c4918010b11942034031010390040d2190391421307809003d544014603020540350310001d4a2011511200011641100798800049c0c0021416413070b42e0110641102d203400b514000c0d41c40d80040004000300030b1303c501c2d064440ca0081c3c2e0118045100900302504200109400303410481c07071840841c0c0340e003103000441c10340c11222a089000241f0426401002c0c03505083e88a14216040c50011004a00e40a07201c1c0280140340c602e4400141c00c0001d41d90043c49038260103031013407000c0d40c0b80c03510183c400781003640c0b00c10440c00303104403241c0315051100c44141141e8014007108450104c43d2940746407141d0207030690340c1080c0f405a168161108603004180240302d0b010001881500e062002000c031b84107058a944154010030030320000c079601c200b52294980e0115141c0020840900081e6400d02c504a401041e55001045c80300a0705808 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 55471937 1250 55470687 55470691
    0xf03040b0703200a170f0f04030302070b130b181206010e0c070503070803100305240709140915120615060a120b0103090b010306051503010b180c070209040b 69
    0x1a4035001140300440d07908040308540f02071540110791294000794045520362040100b508211800c0c0751801124000c1040700d5800200c03a040c0c03903880014104105507040088200603c00182c0260901d50b002e9660038206010344661000041c0c08681400b0b010311010791349640000082000d050fc0c002a0031a0740c448409108290030510114009081a03e6510840f9031280d44100558600341c0e01d56100c41c11900042c011071002c503018400400055000c0101540004101504d100040507801ea12508d19900800d0780c1e0400000c003400700f00050040c07401d1402502c08543d90300c16660b4515424402004141c50710b03600003031080d80074004440116126004659090400c0e074070403511814004c26120b0307203140034001010401c02e944801001d511451080c041403502080c3c242c1d454032017000c50380c42a001903c050755117805000310f1448000c410041c9440c03d13002400302c000e21000040c0621458440c202032407041c000090001c00401d4100c3c0c041aa0013400d20788503041c04e017131207042c40000f = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 55473187 1250 55471937 55471943
    0x11202040f1109060c070b0307020f0607050f0a120902061c0e1504030c0f020907050405040b0a0b0409090602130609050102060c030912070204020d0c0503091b0f0f030f03040b07 78
    0x40c0c4a8840c611001e64010190b44034050016245810a00c00900031540d000021050740d902402c00c0208a01d00c0390341c01103006082d182c1c02000403038080c01c1460304242003c1d011030705100c42000003c0c0b0a111240a591030903605041500108032100c0c41603010b0f01c424400294843c00004084041c0c0c120302406c0406000c010038204a0700400c00015640e9482182802c00d071041094000f0300024424010041e41c54031031405e102119085034007060207072006403041c9000c00c50104041c4080d0509210341c0c01045030440e1754041e1185806c2803014144294000d0802ea0303901c840b03044083c810103404850034035840079058003183d6034070f100040802807035014141c010300507103010400d02e00202c42603c0c060010000038003038020801404040c19072201304200d030859001d0241c490790078080e20500c000c803071180d00d455940b8980381d4459410000190050142605141402011500d030380f104105509801e890800000c0003000001f858480d0105c90b281d0b80b888009004603601080b00c003d03080c00e601c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 55474437 1250 55473187 55473191
    0x60c020f01060333020a020601031713030b0a06180b0405010b031e06120303130507080a05060a090204060b04080a11060a020303070f050c0a030804051606300501120204 74
    0x24a580d02401c0c0c41c880d02c00500040200c40c8000c50103c02d000780d0510000241504900390301244224009076044103404001613008080108284510309401208580c05040b6244c0343c80103c0010410304102400b000d8113038801c1d07074006022401c032039010002405c1039110641084c40d8041c1040f0103043c010a03494061070400c40002648800f5a09590113400e00c1d000c48040025810781e40908864010700460b480100000b401c030034040180003c42c0122224035816001f407005003041460010240e10008036a803042d46454085100072035071700d800404014020480100c60300014000d091035800500140c080014001a464000222090043c3c410100c0010042d03c40e4100503060242003203040168008100044176035210f01ca0303d4210251900301582810841c2e50b4052030180d0452003200859228070500090180c10002d44032a04251188090314a080c0680100740b41001c69601d80c410381c0060181c461541001e0501c0e41104001d80308001c1907a4442510b0f07144042c1c1c803000e80c0164 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 55475687 1250 55474437 55474453
    0x2030f031615020c19050331060e010c030c020f0a08061909020603010902030613020d020711042003040309030b0705090f09010302060301050609030a060c0c0c09150302010327060c02 80
    0x300302e900a07aa03240c05200e01800b00c404404000c0507801c04200b904840d41c0c0410014003024050044507241719580180140d80080f041c0a40e044a2000c2a040075040c8003c00704d041c202d5a9200b520b1b06851580742c50041d001c0b050a201151030f08c04140082c0d9800580401c4c0400d0012000640d10301c151440c0008003010b4494101040403110310000c041d400000401c01440601e055400554010102810302c1c03002e03200780c900050403a08810071059a80c3e400103044000e0205c2c60000c00d40d034460441c0c00f08010400c42a01c0d00000368507002000c4c0c0850040001010326010388209401503401c00291b5201c1d14000740010000d82c0001d1080d8802c620510844a407410000402410791f98090000b40c83d42e42050200007203078000d20041036140c46000c0d5100e000482034000d4000004242e121041030310621311f802d8200c06070f0768025400c0c442c50075000e100031002c10300c00c800071a602801d0000b0030410520300ca0300441803410364099019560040d140130002a07500c07103800030420742c0c2528500 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 55476937 1250 55475687 55475723
    0x170f01090503071716110f030f030901031508070302041d0d0206040b07180e0c07170304020411031b0703030f09030f180501020703081b06100828030c02030f0316 71
    0xd000d58442c1030800d554440042002a11b540b05c018170010004001e036190034100000607240100e4030b60080110303000482c00061550b018010713071200f40d8468603441090350801081941d10206444043e21454a4050b0001600701d0880c541015200b843c0580c1c0c801124642c000c0d40d078010543d01124181c0e640d100041c072542c815818415100407592034440090f142600e44100031b507020340b002d520701408005400001d2950706000c4001079120780690703140e1802e801000112400c11443c400751450400421008442c3d443c609520840400358558a85296007002c0300241108080340c140d803891719480e8018150040000c84140609595030000d54200104500000d402445083d0143e4409034041c4006009980541110458004085801840c40d0407003450301800f6540303801c4516008006000c00403040c40300104070134446620b00d503503103034007085841440303000003014040101076400d000466130140004551600d1300c10840b500c030404141c0605405d11070302400c4565450254620003a = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 55478187 1250 55476937 55476983
    0x3030e040b0102030304031812050f0f0c100804080d020301080a060c1b02010c06020712050408070e01030c05010e040b030609010b040f0507050702061c0501060c0201020c010309020a170f0109050307 87
    0x201d1001a8065400c54540f9078003542d100d45500e9064182012504002c10592541e10510400307500441c01060440c104084842c1440c44c800c04a1125070003002c1040343e580c55100340b080141c0241d161a000995031420010310764014017880c010b01500010001500003800600d490050340159400c010342440c05c41c09442c1c100d58210740d82d43e000e8070301400101540c0a540d402c0c03141401b820000d4641180c0c3e80c2da00d034092905003040d1011500104040c0004a01001010702030504441c95900d1541035440312810b030240e40c4501c40c1005100702c0d020505840c0ca41141050800c0681260780700d00707005983c0350180c03140e15000e50040b40f40480307c10710310125018681c0121101c0e102d4130b01c3d141440d02805600d51004c07001c12100c1c0ca140060492074261842010b0007800b0541c0c0d074000d0540b0b40e100080c1410710403a062030405080682c0f00380944d441101c000c0495008a000032001d90052500c81d0030b084814800e180c140d407a00c11034800b400004401415014410913400442c1896501d194407 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 55479437 1250 55478187 55478201
    0x231201150309051c1b06150f061b060b120102040501030b030c150a180605090429040209030c030a08070b130305121003022d030102070203100b2101020403030e04 71
    0x100e902c80042200d81d100012140728044c42589010020b1034182490115100210074041701e075146e944850780013103085540d040c00034000e0ba841d00d07607030540f4044005029215102512100815041e51201084079982c06000c40b10809407031001183c801841c014000d4000e4400c1c0b5011a08041c0c090105150104040c5940d0400401b071940c0101e0b03807511310f401034214098070410302c14215020a1035004000f0000014140b07072760b420795a01c10403014001a120050203a0182da1524407803075914000442c0c85000104042d00d005841c1c00c0a50002460089450221034150064001070018002c2c0d0000800700fa90050700b03010601d0f01c41070303d5140c441000b03840c00380000d01e0a01c00407280501c2c880500e60072804200086070b00036107035000280c0d80600c00c03260030b484800d5141c10a101c0500e5042d01d240e1048202c000b103003404030a4000c2a1030340c2080541c41103460740c80018400c507598000100c0d0a080c6200c1c6110141e10914440701d000358054042580841e032050103440b903929142c02052 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 55480687 1250 55479437 55479443
    0x3050d0e0f0f03060a05070e0d11010311070b061203040902040f0f050102070b030414031902060a0605010801081905030409110a020115050a030b04050c090709090e0303060303030106231201150309 86
    0xf1541e50352401280080c0406000202085107020412380c031a03a6801e0400d0030203008010865400d03070b080c000541112003541e601940b00a051060001044904a00541c0014140c0e400540f1503149902c060651180d600103a407a9880400c0105101e0840300c8144161046400141019034803800107981d207282c0c602c1208075514003040040c000400042131901c0c8994400100c0f418400c250400a1790780051524403070060f4005000c00100741003902512006007000c0c00d001035254144100c00751540b541101c04071010554801000c00c0007010030495004185845c803c1240c0c0d15181c411b140d0b1a480300f843c010042d0300b02044140d81e035450344485000ca0b20000d280c402e58918669071580c848400400955040c0240c00c4118195200c10803050302c2448642d4610620f0303400c010000044039004502198254002d01c1044210b031000000c80e810741d40d4030700f0318079403140c14902008114121648059849080403d8650044c1c240d0700b8000c0c1030340c07201070f01703000c010148420840c1250b078188805 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 55481937 1250 55480687 55480693
    0x909020321040501110a060203070503060103051b09010e01051204080403030206010806010e07110109020a17070e010518130f0b011701090515070905040504080a03050603190b06060403050d0e0f0f03 87
    0x420881d8002c5c103d555020004009581c0c2501c056203584003280c0040302d240011a10020810400750f80c1440303030550003611302d07042c601c0340b4564401d10300403400b4501031581440855042143c0c00e81c05a02502c404800320360100e441c1e45071a16020482d6040341c8022005440f03100c0011910410205503035041e0740700c003100701500e650358500031203603113200c02090b50f0107543c5c440b806409038842101c680041c18401480c42e0304111000780321840c00885e80d104908040782000144003e5a4080003650500c0050f0710036a0180c071003003130300d88603c3e070300c802e00030411221040380354101703d03000080d14103c0c0d9480d002255508003455040d030030f07590b80c000010030641044042c48840900c0d022500d800440c1440e01440b45503d0b000407a0407941e0550b420355600e1404240c21080c4c0b85e060140c107500084c2a40a845a0080804a1402045d02103001411313502c0c003900286981d15248141c81c011500101250a88003804070040d251541602d0b48030300402d54008201120708106058043e40540a801 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 55483187 1250 55481937 55481939
    0x71208070c11011710080c0607021302090604080a2406031a0a0605060a18080d0804080705011e020702011706010c0308060d0512031609030b0a0207030e0a090902032104 74
    0x600030714182030788889060040000c42c18002050400040b8462140b031141790012a040001451400f114220081e10545081020b0001030f211044944180110b207540543c42d5011200001c10302d000300d801070b6400b849454094000d114130580942c6080340b14050095242d8282c40031501a140c690202030074600c03111302c240404400582019901402c090340009000c1d8540c000116140c0c0510050700004050312440041e403803030384417080020040100101821700610002030060000200007514091001c2822824071500f908204000561a1070850700c402c03841074604029000506c0c10390004007150184040390044543c41401221f05856600a40c04c0c1a41d0071210b03107100400c01e80d085070849403030000245041200c0c01000e42038010054491070041611110040b03c0018681000304030f800800c08a00ea03280001d8202101c513a001d681c800c024107040e515003e070f003003d003030300902c440c800040e441c1030703640c4080030b00c510031000e031226020321000303140b0b08040c8013440071410981080 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 55484437 1250 55483187 55483193
    0x30420010e2101050907051807020c060a090902040f150305220201020c03161a040303050703030207020d1a09010e01050c0d1d100b0108130b04060b01120f02071208070c 74
    0x10207601c10401c24802501c0c1d10b07421005039425203a06030750319101680140010700081c03400c010000e18242d000d000b01561440e201000941d14440c00000d6030098100180ca815498403540290b0064195480c1c2075580c3c56072842c007a001a5451710548a2601441085075401440fa0141c58001c0c2140e0324040030714450b501c080210188040c100300c0c1903203c1c0c441c14a0141e02c1c14001c2c1c0c00b88548820301500140d150450341c810302403951001800c2c0000030441840000d40010913142160341500d0010389070340c009d1010031103030502c081000c2c14441856a80c90901060b10184034407440d85030009000407421100114285e0740103842c00c440304c141c01d112f00e0390f504402c1c1e4040c0a0f1082100d800d1841d2965070b094183c00c240910382408a40c2d0b4a4481c81c0109507000b140f110f41000e021440011000456115546600360242008100710385a03800079140341e215070001c48042d0750368070f400c11840111402510007540030240458401e01c03070100044480c2d01840000e40710721070548503802d0a03c170796a = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 55485687 1250 55484437 55484449
    0x50319180303020903030412060b0f01140301030803040c0e0a1b02030a14160b04060b0f0a05010c03080901060512030409150e0109020703020109080304051608060705041202040e010908030420010e 86
    0x40c0195170544002c3c440081c40c10b0b05500c198460340d0041c400080c590b00b21105000c4c2d5600c0b2440424107108564071285124400c0c0412641113a070030041c8151a0f8071140b401c180c440a00740c1c04141034003140310130311a052002340d0107403034001c031218500e020000304a0400d0380c0340d006214000c000f04488491005101e41403100601c01203000300d1080e5290445a40c5404900405448c10703100540e070b8041c0400b140c2060082207a10110464191048a1134170000a041304250400101001700035400304848820035004070000e44401810365050f86800600c581c0d0f6504284140c00810b42803428040e5191003400c981401c0d1405101040910fa0034414080d000c2e51041208030700b1590784104080c04190050082c1d401a441080a4800405002000032580059402a105c590411410b0002583d0007504850031114030001903c042d4403140000340040442040d41c003505e50170000f41d44100080d400c002d510491280300307958116100505180c824010118041d80030842803418040c07030385000 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 55486937 1250 55485687 55485697
    0x11041a06091e03010507050c010609061203030905010603080c01230c070b090703150204080607031a0d050c06180118030b0105010305150a090b13140c130308040605031918030302 78
    0x580440d10320415260046130071107104540101c001140820720040046080c029032004205c000000d220146c18027845501c9012103040040602d6500c03858101001403c3d00480f00440c1c00c802c10944400c80b100ca00c5010300941292880c1c0e411110058400d03040c28942e956001b890304c034a1160514030a5a12880380c000d0107424178a0602c0b81d10340c00400642144112180003084590142c0c0355803801150901c4c180c0064060320a040c1400c1840c070201d9007070450341900b00f804448080d001600e50402c1414a892801da0607040000000c1001100e41c11004400000900f0b0344e4480c00c01c0c03003160304942c14030000d0000500107940580100f02c2e962007030300640d03000000c210440200d4400400068011080703907104440d07854580b030303002003946400c40200078010310010b41444100720b04401451442401402102503001c0401c8001c2e040001e00c00310300c0a103503ca4a16a036850321034101800ca500203c030498441d590726170340310440407144d0181c0300f061a155445500003800655064019401c4 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 55488187 1250 55486937 55486969
    0x1614061c020409140a1a0603060a03170301050a080a03080708180a05070504060506092101020c0a050c10030c02100b0619030207060f05070203030403030b01020709050411041a0609 79
    0x440950003031402262005000401c0a0344000840703403451400140c18550041c090035100349071500f82c003400045403407002d507114002ca81e1302c0e680e6600d450008828101580025160102c1424114130410540c0001d506a40044170811072150f0340e0102d040d0f840c4d0b1000401000242d0710030214901078045c000384c50300300602401c820f000c034440509251414004900680c0c450f4000401001242400d11694000c0c040c15500f441c58000303a8008a00801045070b9201c070303440e088400410311031a081d4143d60018801d80203a540011040c20055961012402c406214020309188101654080e1217402d041c1d6a0f160003410700a030449002c180101170148809412030001c01040b61a07084880f203d140c0d64655450060f114100790030010100c4200d000b4075031080745400240003071244c0020581394881e40c903140c0441c03c1c10103000100d00306611684004c1c207250803c02440204800d04a0414a0710400c0d14104001800c00d07001c3e041011104903899004030007000441c60b03504141180f00c3c01d80d80 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 55489437 1250 55488187 55488217
    0xc050f090d0f0602180105040b0403110a0905040c060219020a030f05071e0f08030703080606030c0f030103210806010e01050d0915021e13050402091201110a02161406 73
    0x200c0380e140d91200d800c0c0b00030202d50142e4009035807010359400000301d140012007842c080e41060b00f8004008014070441c040078011091500d00d020b03080c4c0e1440e03201000740206078014842800c1506d42014101258000c110250140010320300021441b00d580d00c6003075400400210782640b564840104d0101c4451060701c1500a5500119030300d60100001080c41201080690f81c40c1d00c1d060b0120100240e50f040304000e0b410400040f008a0b80c840304641d08070368115292540c070b45030f03010840e0080c403034403070f458201d884044000014030040c016101105c044640c2e50400030b0030400f0084841e0402210358a0100c0c0440820102c01d500c5440502141000ca100000d041c00a6494200810500b1255541c1c3c0b160005262044980d010700002000180345c0e030114100749001c00356020801c818050b25004690228055004d036444284150144240c00000c01c16441c2103e19500164803080c10500544034904858000c1d5281c4603225089541d0003900c10b01080d40c1030100a00756006c8541c1c600c5140b = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 55490687 1250 55489437 55489459
    0x90204020d24120c090b0a080109030201060306050105040b031011070b090d11150f130b070e0103150f09050403030204050907020601030b0f01060e040b15040315050603010c050f09 79
    0x940d6502c50380c2040e8800342d880d084007401c400e241c1e52603441550002d0304562510712464000070391084101064942e580300210380794011380f010413a100d0095114501542c201401001455010341c003d806607030182200f80039a070380b43c806100940d406914020780560000a58150003c2958440d0401d56003588000e854454541c440752100503003541c0d100121b4110140c00e0090903000210914006501d00c05481040480d8030090691400205009490082e1400048804e0f804400c0e0a40c3c40d680010307595100d0400c19402003110350300145882c0420300d00414001903075070400f1910110b5402c0400f01c0502c5003007a00c0351000e0400a401141415001c1c400800c89039a00e0100b54480c2041d50b00a001d550300d981061503880c0005081c0b2003c40740c10000500042d40d210b903140f00228800d441c0404c1400d401804508050004414480d21040c003107408001c03c481c880c034040d00800644028022521010304140c2200c800c05d0741e13000454410040510911950406040785500080144840c0c03 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 55491937 1250 55490687 55490707
    0x6041e05150d060209090901050705030f04022709060a0209031213150c030f050a082205010509100e01020a0203160606050901090b040c110d0c21020a150504020a0909020402 76
    0x1020914003c503070f203070303004900b81c038090405140e071651103a241c0e0001c2c002814045000b80c0240300261014040d200001c00141c19503c817015840c060030a500407480005d440f01c0c03111641c11000b507580c06e42c00e004c1e40000c110340200500a641d043c0720010060040d0814014142180b80c1c0f00c41041d051044440c4400601d20b10070803500c000b02001a200d0a00080232071400030154600c40c103800041c02414055280c00c2c590004d0340b60303440301980e5041c01564181000301d8032242a1a81d00415560a10302000801c0d8000f04400a02100c068024400780340d035620070030b0a0b40a00180c02c8010382c0280002200480c0d400c000c003d04500840f40002d03503e03222008240d01200c260417103d52107032900d81604490803e880340618030401c03441c200d404c0e894040541a195510728a03000700304504816041c00780700e0140a40c00c80c03400c6094840c000800350344006334680d18071400c19500b050306162450744210660040521032540180002841820810300c0c100424100c2d01c10b0741c00c640c2c00d209059079 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 55493187 1250 55491937 55491949
    0xc040204030b071407080306060c0307020d050d0e0306010803090d08040801050108010506011e21141008060123010f0c06050f04050607030e1c0201090218090606041e0515 75
    0x1950044030044250f1030042e00180c1000c4d0184421041c0c0d01040140c5404260720b50b00303a82d0000c004a5915a980e02e4090a2230f285028001002c0c2d44103405082c1441086030000d2203014040880c2c4400304110306050070951141030900c2a0407840d002040802040d1803d4480b0300061031245403164101600c4050f401d0844d4070076000510713282c0d518801d00c8400d40c1c0040b00074810785202c1d0004403c2c445064070041640d0503035514081d21030f01030b010b211640045604501c42c020405080b000c01440c1004400b030800084e407003000d0480c000d140022035145000392680b80a0388440c50303042941041c070001152030308010010407040260320030b80b20000612034015035005040c03c2000048038145410f0481c20000d024000c6014145070410901b0201d0000c2100003420800742c202d060a11841e40050f800b501d207111000754030501368007040800410100c1c20301c2c09141040111046a0748041c03c2c04200d502018681021407480f104903070003110b0036088654000121088014000c221031b011032a = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 55494437 1250 55493187 55493189
    0x801090b010909260d051003150f0f0c020604021206010e011707031509110603090709050405030c0f0a060b040915090302070e0114010210020a05090907090506070f060b100f030e0c040204 82
    0x40e504c2c500042c4c00c003100d03016014003038102c100d03290404440341c519640d19105026465507095421740310303492042a4600c0b9400000810086c2e0001e2190f03041e441d41c002d48511301190124403400700d0740c450007120000080c21a058504502030710406134200f0200e0442191010098001d500c0356640120004081d45003440c0c000e1101d21000c5012580c078908055150280c0d00ca040c060541801040352890002400b50111003c40200107500e480f01e080850661241c0001000b45201c0c0601030481d0b1030300041d0003407449008000c104035003420b40c02041705494400e030b00a000303100ba0444000d0340340460317408000001e2080c01114007650303480c1c040c50380c0280240d0007a4900218031410f0b014a5030107000c00700710407860350001c5241054800014049000e000c000902400741c0c0702c001155030b4001e001580c05844010103035a00c0b03000074507200d008030115a001300d822a080c05240552030030602c01d039462404036a1138005c560b200c0c0c14000c50041c6000a2488071074032841100310480e841c2c0c0c0c40100 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 55495687 1250 55494437 55494503
    0x15010b1213120806030c09042406050409080307080906070207030b060415080c030d08060a12030c0503071506080c13020d1814010b01050415030c030902040212010303090801090b010909 81
    0xc1007450818200350070f11b401426414001d0000708100310008110074400320503d102c0c0ca000200043c515105840148603680045802c549424001018071a48001461066907070341d40c1d020007550303100104e68071000241d40b45005031744404010300002d108109940d03889031015100050050003031004c043c011920340e0100c1a207800074a1510a0b174181840ba90081451504103850107090075004101c459490b4807540c81000c40d241c5c0c0e05001c1504c102c0b80f400c41135070858200c0c0c0c0c840c04141001a020b005002852550914020001401b0600400c0305017449100134451035a038501d0030351034406940103a2080304165922420380b080c601e002407002000302c0c01103080491044640d20740d14210741d981c034207083c148541880704118800440e010182980c28038034022810300390080050b0f0185c04000c00c025132090001c0382034219010305000860403a4000d980369110160350303081482c02c940d4840c001420001240b401400298840c7d000168820705c03c2c0c074800304244209ea2040c1d8000040c0c2290 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 55496937 1250 55495687 55495697
    0x2090604110721020c010e060f07080a0206060307090b1003051009020703020c04050703150b07050312011d0703060f0504020304020a0b07030210060b09010f080a060b0d09030215010b121312 83
    0x403410400f111081000e04005030009015100002c2d002800e03c0d58103281461007840c0002c0c841d65221560401d4501e000c0d4400701c0592106007001c3e000c0c2d2a0801207613002d019100c0c1d0600041c00d01e0707503400341400740100580360030842c14510f1011000341030010020811802414030001c1c4400303451002788602030080e4081c1015070448400c01083d030f0000380c42d0b082054244000340c09440d0f00340101a08440307130b82c2403055540c41546055401c50040d501d004e01a54100d07400018200040e081c624404105821720780c925685000099084035036901034200c0d819001d402c00d00c400d00f0190b0046411038001405056015500d0001c000c01c1e0f03000c0c010450060f0040100d5400300c5c110b500802010307054a800e00c605212120340002c2c03012418807120400c20070200c000c5622002e465000c4800b40c0403c90000e543e80c4048038404020740f590700b9045005205121042c1c5c1085041e038070140c140c0700040d003990720300000312059901c101c001900006204003141411380008000c0200f0310010103a41d224 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 55498187 1250 55496937 55496963
    0x1080307060b0f030705010f0201140f01090c1812080705061807120203060604020325090f05010228020613030605040b070c0309061409041e0b030f0a020906041107 72
    0x284056500703803902d01c1d01504402c400f125084e540800d07074506450082c44d103e82d1155103804100d024211906101c500c901500e000d008a20f40d0394500340c3c0c181c54551400b0b00030b424540e0811220240c80b4001c0c4940300003904000d00c14108820303c18806140104001401c00c080360310703114181101943d0400c40d20381c1910040030184814403001c4024058030001a030215030320380210791a100c0080c8024030403680080059864079049010b140b400030450200094140010005041209a405112465420502c0029182d031002034000d0403000c8044c0603024584020000c4890003110302e000701d034400028080c0f0903c02c05507000c448011801003602081e2400e090074a1488458064007907020003001d4003011000c41d030020a00000c581a0707240c070809822002e1050f071034902550251643c09410440b48440b5004c003640841c1401071609010049a48000100343d92030368141054a22500400040300c0036152005402d40c0c0b02c070f4003a001050f00000808545000d40c020341c4100c035a03001c0102 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 55499437 1250 55498187 55498193
    0xf140103020f09160c0f06020a021609060302150c0718060f0b0406081311180405010c051215060d1404030207090203010f050618040207290f0a09050f0601080307 71
    0x601a040100c0a0b81c00c41d22500b04810191388110302010321000f840300a072030010410100d028082110354102801f1500c4408a1b0002503e03802094282814199030300070101d241c600c588a10001c40c1c0d401084050440700c000c60b2080320350400c12643c4201e00400e0b40004503040307110038083c02c10b0301d44400020040d0800f4103c0c00142d040d038100c0e00c40071409100920a2a80103186543c0103c03105114070003000a9150804201d030a6400440c0c01c510510520074403008501e840c0c030301451159000384110f00409000712214021007441c40c0952050502050044140084400c0002009030001d03141c90311800080c800e60b0a1501c0407104907000c10100000d0680c18080400074000549066245501d4200c1d807501441c52402010300c9003c00092a000740c68080c55000d03842980944255101c2800d0f00b0003c2900796001c5048001c0c8071082e6100d801d40000d03405040c4a4068240310030081d880c0c41041c180100300c03010701103070f2921440b01048044041000024020084907009540c2d95080746 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 55500687 1250 55499437 55499449
    0x111040303030e01050705090105280e030c060307020a0b0a14070908160303050417010b1905010f03051311060c10020405010e220b1305010602030304111c0809040f14010302 76
    0x1601c02c00c0746034944400d11091a07404812904008c6091800548945084000a40c0a0319185150380c189200203802c0d400d203a0001c1d2080b04881046043c1d604420310502407102e24401102c1100050700010032400004072484450b030b400141040d00015100520410844080420b0320381e6004560205020441140204021250300c4102c682641e0060b00d0f580d03011303109000c4d0b401108400c180c00310b0140140d49095004400c40d030401004000307038501c80490f4200882050061a002400307d01148a03001e01a0050030b016205200b5034007282c21043c0c50310310042d0307488201c880c2c1c40402000401d4201004002040e0644020303d0300581d50b500e80030000d4031011030260542c1c040d104090180c003003a43c3c544410305407401c50400200d8112a0320000551413031b1440d1480d00d0301c1e4503243c008a02641e000025520441c410b1620402041c0000100280b0512031400003800b040515501c01c00606250040c004a500c09003001c1180d400110102e000d5606250744074880032003e000400c00e5161503 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 55501937 1250 55500687 55500701
    0x60f0f0702010b030a0209070201110d06060e0d11060d020f12010e090703030206011401020109080703080103050709060b1c0b04022b061a130e0406090c080309130902060705011104030303 82
    0xe0300003088a600310301c010a8480805c0c0034040e108040700c0f000101c0c500d000b9040150114921416284d42d4038180f001803000781460f0103a00000b0791011950364641c14940203822040f500092012009000c15080100b254000c14200000075005d010303110380507900300041c0218108031000e00d180b560600e2314000c2607150090100030700350301401c000c0011a8000c903405064400c0900103d86080b14980140c2c090305000c07500070080c1c0000641e48090540c0100624181c03440b50060740d20460359200b2500c15602c440c0504000c1002c00c003e0210014a600071070300300f0b8a00244041503a501c500b00040498104074800720001c0140c1071107900841064102003440f01380410100328540c10072110b0340111314404104030300b8000004120300e030881c4150403080106908503588580b0314003031400e000500307101d10f001c4038050064180460242408810b440e01510701a082a03000b054004c00c60014249003202a6013041d02000b441020030341c01e025072514500c1580c286592189145001170440d041 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 55503187 1250 55501937 55501951
    0x110d0e0d0e06070b0a090c0b191d190306050c0d060509040804060f050403050703140f0f0d12060b0703020c010f02070608010e1e15010f170703050c0408060f0f 70
    0x819444003506586042c20b940300c458000b86044900c1c2c1d02c81640720010100303098040c050280300400003d0303200360a402411425107900e90304d00a0650003009940c9000c503e5000300102c020005da0100c5402d10b1909004210040035110030340541c0d80c0c03506c00450340295000e0003610400201503040ba0308170b0145200408090304d0404041c9001c0d15000384034040d81c0a031100304002c030900d01c4032044c4103130240c40180d50494251840c9aa5920f0500203030403804001c11714070f004035081d15400d5000400d00074050100302d0b0150800740781072081168005e1110145044d1030f6a640d401141c54400c05019002a501c290010109455400b00240c00101511446001c542c0080c1d0700307200302540704800710304460351500309001c1900e402d1f0356190740101d204d03001140b07103a099003084000c8146580a0030051020303282c0340903114500c0011103041302c0445a41d032892600f00b02244090344654050790788508003d1845041c0380d00c2d0101ca07818070030191031010889106206212140c1010f00d40c990708000 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 55504437 1250 55503187 55503197
    0x20c10020c181905131709010801050d050718020d0207120305100f03080a0c0803040321060605121803070c0614040608060409030513060903060507110a06090204110d0e0d 75
    0x58411a1854007070f024400341d005083e20341000c80c54002800000d54183c1d44e000d90341603200000811909015000082d5060001e80780d50000560b0b1705000d41c141480c00c0d0004050108641442c400e0780d00d642805403001d400c1a03080044142d600c0d00e600c042e00541d8403d0308000515244104010240da1003d4468600b210001c9400c200301d00c4022208400c5a07844034a564882c40b00750000d451031100048080c100c0c0500104100801d03078010310401d203e810151890340d0304598035a02e04100c030f150f806030f8408160100050144029142c1c0034607070016040100c3c040d03901c0742d440c20500b5504440c600b2180c0a41e850710500002c2c0d0041400d220000d41349005a00f02483d00c1001841703684d020300494004da41e035090442c01e140c4140300302c50080c036807100700420f0541c3e205c200810010780761205407142480c210210380c2103842081090640366920004050180e03154449100070174544004a070302c25940c4898900390b0140f003003e001481c0c4001e4002900340e404581203418a124007c407402040 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 55505687 1250 55504437 55504441
    0x7110406080d0c060609050c0909010b032412030c1b01230a09030b10031505151003020d18030e15040b070203030409050103050102190905060403030f020c10020c18 72
    0x80c800912034090100e0351414100c01c1003113040c404010309040e00012905400e00d02004248944003008100d1184251000748440e039aa184035001400190b1b0b40c0344400741050b00c400030346140740d0381015510500501c00c00500e50301c03000c0640740da0701801d10071a40f0b800c0b58194015440361141d11840d841801e00703060001e0780c00c224141440c6070040001c01b441403c041104811315205038031b660082d40e4848210440ca0a00b403091210780c0c0b0032071100310f41403900c500b0036032681c0080340200390041907200c0344140038080700e00802410141940549040503401d0021000119050080380070400c00f010050500b26824100100b089452450040c000c40352850b051101002100851381140c00c80c00a40d82c8a207400e20009080d40714503442019101e04100002c0180041076004118500d403a0003510100501c0d10019038445001e445000c0d4489400c0c0410130201e802034410b40000c1183d881581c84041ca4032002844a00303c2d540b2410041c2e2000e0313009851030900300c07007102e00982031041c0000f141c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 55506937 1250 55505687 55505699
    0x90309010818011506111002090d12020a05010213050a290f04030c140405010f08030d11091216090209030319020a0f030c15020315091807090207110406 67
    0x9402901c805800d2550b00c1424440398000c0d807000590a0040c144064102e507140310050210140700301107011806280d201c003801101d80c0c4212410410041e007101c1080d001c40e150a00152029041101075004011085002803828070040c00740180c00c01c04030800e039040105006651189410003100046c42c01014604441581c070800ca083c0c4903004c01c80c1c0d5a813100340340204c10340503a60009288903850704010aa03100d1542e511450f641c2c0586040000d80c0e0b0f036030082c8250300f07101d1150004035002080b030401d401d441798100c05412034450900714079040e14540851220409115800c40540101080c5008018410851402040082030550414545c40d0002e0303100c0c410040009066003000e104100741c00e00902c004902c0346e8001c204040040b0040c1009803c00c032442808494010940314800600b80f00341c42924001c80e4211480c0cac0101040708180f048004c400382465040340611a09000f9516041041402512400300301603240c1c0e189107065284612420303122840380c1d0900900b4818 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 55508187 1250 55506937 55506947
    0x30804080a0c050f1305071103280201091a070302070c060c0b06040b030d110f07080a0302070803070b040f050c09130209090606090c07240219090609050411040810090b09030901 78
    0x785c10b102c45d5000030b5940b82c0413030689540c40090354521803404040b840d03541c6169003041e041c0080c140281c0288109140b003c4c01c03400c0303c040150080c141c0480c80d00d404409440354014603401032a50400521300a2180c035020b048100300c1c1e00c0341c40007070300a0081d401004252141142c0040b020344080c42451902000a5224000419000104503001c03100c24283c5604010080340411083c3c251040c003500ca6184540390310400006502512405a000401c96400400c45484941081070610151642c4c1e5031400e810349505015512032141a100d448075503204030300380740074503a1704013000540f1400b84103021500f4001890800d82c1e4202c007041090548a65803042e6100c00d0444002e59115098a8a100c0b4040700d64a8200403010703c2e09842998042c59004081c100444a00000d00311648082200c0102c0140100d0b030018000700d4040266081030342114080c1012441400d0402d83c44900c5540351540700400c0042207510f03441080c080c415440c10781a0000d0400000e03501d031541800020f48 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 55509437 1250 55508187 55508209
    0x60d0b190305120901030b0a080105040212070602070b0a020f060709050103140103081b251a0306010905040e01060302061c060b03070519030e0a050109060c0309050a0813030804080a0c050f 83
    0x207942000011030504c103a01c0f036031141da0400340040031102d501d03850f0300400d03009003000c4804070f004980143c8110b20314640040c0300c0302180c0490340100403860501981d00032a400168011080d44100ea1252080e4141449003500ca44415911100491302d00000107056a010350440ba1294803144018800701b8180ac2c1202c1050314507e510810000c1c0c1c000005180c00d00089803081c962198142942415110b0b45a10303084aa58848100483d030700f010141e02180b02c02d8481030302265031541c00300002d04140e0040f81452420800010b6050794036000305007660b0048420043c0e00500f10107140b0304100c24072443c400b81501e000941d08506e407400000c3d260b84103820b0041300e815901103810141501c25045154600c48020545401003503600c0e03c51301914a06004130352850a10400c0758120f44a8032400b0503890b0403000400c031400940e200e0000303d030722144c4440c001c00307280d030408408a26058000e01c001c007803480c018212000c2a08100000e605d940c0c02262040ca140541d2010503921040072034 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 55510687 1250 55509437 55509463
    0x100e010210180f08070f03020a02090a060e040314040b041403010609090c030303050a0906020708190f170411060406170601050f0708030702010905010e01060807080607020d05130302060d0b190305 86
    0x4010220b084c00e114841e4081c18000900f1a0304051020041590118440513498030035508030384c2a45680b8141e0041e158540100070b0071459210000b00401c1c4143c6820659444c1c032020249440e8650841048583c42074210000d0441c40c0124203010341002d12442c001410301110400c22030b00d840d41c440c004003025200c080c0802d80c6510101e06500c400b07500c0340140c20352098045581d403880b841c000036a500541c401c01030310030030704100e4001e80303000d410030445a4826a0b034030124460742c40c3e801b40000070050410b64010003401e4850515455010080018009640391034024841017001540140402489181004028014040700c1e083c207405507189594400c2d5030300c0e12130f900e5240482c010703e807098003d0055070034018441c0300a1300644c000b0058512545c00e07a00c1d296150020195607a0058a400740141d00c0103d10f43c3c401482070f406031144040c00b01400061765901d400040541d0009048580010f40d0703840c2c0b0340d5062800701554400400e440d100420010703e1900d038682c0b135602100c042 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 55511937 1250 55510687 55510703
    0x1031106030403110703030903030e0909030d020a0e0306070908060c090607030e0301020d05010b04080708030c0c01030504140a0602030106090e06030a150f0204080604020f060f0412080405100e01021018 89
    0x1190805004444152603a84e0000840720015540d0030000c2a420300e6120980c0828400c505034a0641001c0480601c80c4807580000e602e1b01c418044241d0080d841009401e04110b281d40b07400010380d40901000b070103107100d9078802002d581050055810440040c0c01042076500410000030141c80d4803080e1000c00741c0500f8034007152002000401d029103d0024614101f82c58080049038480000000e082691280d004940c901d80e161161196240b00b00078070b030701c0036a00c0381e160081d4561094000790340c42445241c4d0070303504102c2061030501d4000b181004841c0190084010b020040d4070292850041c07580462400c042d04006001c030b03440d4003900101508010700900400301c1c66109401c00c8101001302d00086654582d50b421060311050265000c034800c1d000340e0840801881c00c402500d54100981c1c01e024602807620310f00c01044001d1203011600d1440900c0700007065076450050a4070290192160104481c211000a003050742d45e0364149031051600c03002c8102c00b04000c6100c40300da9400303404 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 55513187 1250 55511937 55511941
    0x1050609130c0e0a0e06090109052109040b220509190206090112060b0a0207030203210315030a06020f0304060b1909020f040f0617010504110d05071e03230103110603 73
    0x130090182004480030301c80d41c03280c1d200340103080d9415400188030034010025110034072503801018240d03c2c1c0c1c00c64000c800c040705004003001454564000014243c004040d0314160304c500002e85c0c10080e02c80c105180007942d48040090390348040c40620b20454000c03100300079020302c1d41e00180260194072840c40c100180d0700401164100309a00c02c5000c2c15038542416242c101c072078002995680140030490180c000c03241200d43d1101c0c035144003640c00803103003107150466589254100c0c00c0690b9500300f0742c2c14403c08000a000c118244002e001c0d0f4030785820819628682404c01c0400e0300c01144105010b030050754640010700071078002000603140e0506000da5204c070204070f03c060320300035504070195a9641ca100003895030b03084180a01c444d20b902481d80c0c05680d8500802088415503172180f91038080820031640b86180a5004651141c10707824082c070b00d0b010fa5104088141da125043c040400d60350100f20004542407054500c4803007092a262000e0740c11581c40c07214075010381301d03003034024400800 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 55514437 1250 55513187 55513201
    0x308070806030709180314040e060d050a1b0306051b03070518060316090b071502160605090f0c1203070b0603070306050702010b0a12030c020603150a0801050609130c0e 74
    0x1241c000100861107052198101017112000100c08400c1c045001c142902d80b2004015810f03010798044400e5058007081d2681c5500c00e1180040201400326024001e5064201c0003642a25680c19108014264040200e04602d080d008640d0054000d804c00c0120b050b001e044c0c240e10314200c0340d0020356458860340700c401c07003885821200524481c0640c01007010003001885800c030f812171150f0103400d5803900601507407040c0380f242c0c40c4507a000103003c0403c02000c100d0301386425001000c1c640038005c2014010b4101d0303100d8008449003034a03030b0140c079002007100b01c900c03080812200480c0b14003111810004503080f14069640e101d229401445400d0035800a981035500740710a1000f10341040081c06145400c110090081c003034030f580607204454002d00031400e0540002c030020f604d41d254803103005081c450340030000d040d04005c00c4c04659841311001d1481d1902d8920b041d100509a02001081a0a000080101c1d00c08010020640c0d8070401c4d030351001191118240e00212052103040003c0790311284 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 55515687 1250 55514437 55514443
    0x20304140316031107050607120314010b0702100909020a09080c0102280c080604050d090605030606030a110d0906050406060605070c0605090303210702060108030a20010b100507110409030807080603 87
    0x180c1b18903440a00070079018280082c078820b0414102e51a43c040201e40003003030303070030a6515085c018000c440c07030b05010850050400e6a10107840300e075a0f05020741c00b107568001c2d60080c0d07030040f00300100080702241c0412840340100030645890200740003401a01241885040d4a01d4640e0342072440c181440c2070400c180b1240713620080c0648980420307034a192402c2d040c803d07075500c00040c40da40020b0700448000b48441c4150240c070301a2400600340303031968645000d2100540303180c00109400c0e0b0010011541aa1210f21419098920411000c140c5d8a082d05000742120007582c8050140801005942c0c00103079078041c075a090390114203040340c0301c80000000c0792841c012510340e4000400d03440c09010030107200c03541c42403145111b036003100c10030703a22100d0442d101e00942101c2e0001c11801074080700e1510190340c0b9100c2800c1200300001d0440c03140800100d0702241111030901154000516006000144011019400094a00307014121740e40c0c0e4014961403004010008210980c07000c10700994040c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 55516937 1250 55515687 55515689
    0x30509040906062c06060708070311031603030b060405010504120309031505090c0d150914030307080f10060804060506060705070e01170109050703020d0c0b0d020304140316031107 79
    0x400802005132030b84070307800d118402190001c00f402145002d071210640c2c00301c011413240074040c0460303003041da0f035036210451a0010541102030001c214035441043e04108090f200c20181d40e04004001d444508010382181c91040f0014040c3c00104428001070f40c010b8122001c0701c00c1c500040c0b20f0351049040440d0030f00302d2030304010001d0343c0c01080090303940401d41199004514150541c0d41c02c1c0222401c00009111104000340742c01120408242001e401c0c0d44240ca00c1400360006000b101c03880c003107207425540221042d50204900009010740038009401860303004450b0020b0b1048503040800142c005900204014042d83e11800010001e84a040507901200c0e813000032650055202c04a13485004c00c00d0080d104c0c0b0a86000c6940711040d014090b4000261304100039021407421034081c4203c4000030390003600c0c0480300941c0040ca0f0600c02c4006d01080e0b101181c010b880341400d213081c0070303a40700310342c81e10300581d2041c010301c5400d00441310b130840407952608290b02c0c84035408075101c0c100251 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 55518187 1250 55516937 55516943
    0x302012109050706120c080415060518010906060206130602090d06150503060604140f0a1103090601050f04090506070e031029100c110a05041805100204120305090409 73
    0x14240c12004014001603c0350a0b11801d4940c0054555890448002c072101da807030f000005040000800c2c04145445041101c4000715000442c2060300d80c0042042500d8000210300b202031000c00400001100b88a0039020380203604c06890a818020f904490013000098041c00c05580042c3e5080341e65603500541c42d0b0075500250500210000010203000300015201d00380c081c4c028203002030050702d4144500125444141d650411503180d0f0729002400c1c01c00100901041581c80c566040c216554001a51040f00c0d200010300740f660401d000e00c1001070480810300c3c012030800a9020000f44040b9140b6070001451501440785e1110348002450301004010881e0200e2074001030080680c0600241c41c5044101d13511000c040c0c0d18007081c444506800c140d9003001034020884400090f003042c0250b42404030003450702443d02d4071640042c04403803800e00c089100c0d1243c40c0203c0100401481502c01240e4000e0003141828a40b050700e00083c541d44500600f0810300184403070669a81d03034082103405030 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 55519437 1250 55518187 55518191
    0x5040f110f120a060507021906051b1306020106060305040b0402040b0a0b0408030d110903071211220e06060a06050a0212040909020a080304080a140c1203090109080a050703020121 79
    0x180d0103004a45407440204113032030450900c40020741290000035462036851442001202229240d02ca000c020103019060100c200781c01040ca008c50b054a801400c00000403c038906440c62034040b010742120340c281d011405144c00c002c02c100c0803803038118101d54071540558001c9010058440001e200302c0c003a4202503a01c84000c607011600c50f074000003500c3c0e01d014400342044581620042044603005035800e00b68550b02525061010001c0075056950306032050070f1a0501071500c0b00040c44580703015134854070300e604c138441010b174240c0b8601490159030301324400303032042e03040800101c1d000048500445084c024000b50090a29108100345a50b50850b0072a06440350344820214016000400d4182e11840040b040407492000100854084840c220020400d01089940702e101c1c903980344200c801d19000c1c1c040056200e031507203da01100c500900001d5690344c100007002403c10f01241d08200c110390300410500c4002400011181c007501c0e02420162110840400c00900100303c4940d5030b04102c0c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 55520687 1250 55519437 55519459
    0x105060c0109020306040303060f140901030809010c060c050d140402031b030f010518160b0405150418271703090703020307060c0203010c08070804030c08091806090a05040f110f 78
    0x10307859408001540d40442c4ac40e0103080d650201c000c4548002c07444203030310212a400400009411900802c040c49060610580104c500d0f1180c10881c0c02401d11000411000503004919074001e10038040100d42e43c00745201c0504054000c00c1e80c84081c0300840f60b01e89020503603517685079400c100c800601c1c5101c0c4028005450480c490100754100408000030b1441640001100440c0652540007980c070316481d440c0c1098031b49000c02002d141182c0a040c0402020000896400c642000d00542d4221000000c01c01d201d890200d140300342d4016440f0031034540c8440510001414a0111040000c8082803041e00ea0f01ca600101d420a40c155100035814843c0240008156412400c0555058001c03802003100c00140c6000f0f640ba0039003110400c000840b0080010000790080301c00401c00ba0040c0c46c0035042c10300d018040307121007184140c610b0011403284200440c6180c140c0c4220303485110a40240402e0419660740781c16445208030082c50304035054a104000c3d21070b001c0200030b0070b1009000703080c00 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 55521937 1250 55520687 55520693
    0x30201110c0a12020c181e0a020909060307051302030c0f120a0b01020a210c050d030902040b06040302010f12090618061808030c13080a05010c081e0105060c010902030604 75
    0x4010b01c980890301d420030000003000003800400c02d0603101a000e400c1c0c00c04c005c2000720b4020b014200400e9910b00c010488180e0f58011084d07526144aa90700400041c0d543e90900e0810059040040c1654420791081909200303e480310309ca584100f5010740000741e140d88404402c030046000f1402031200b407035408039060000000c0307984c00c5801000f01c0e080c01c01080041c20b00490f01d59460150262a100390b1000c1081442c0c0f00010603c1c402980780740c0f101070521582d03962400e054502c04041c00003915001180709500c0c0034401e0000301e0b00d00310341c414034091442d80080c001031903400c00c3c1801d1001e140042020801950450746556a002c0410403400c4c00030f1141d50041d2101035801c0d600300d850401d207100544007900612291641055659065598a204515141d845203400c180f9500709280b001034032540401440c002c03c0d10402c0046044090840021300c030550041901c0c0e00c610908111005552160340d140741074600c02e03607181e5621211032501c213014ac40c3d80c850007505442502d00f0031042c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 55523187 1250 55521937 55521943
    0x30a12090203030c1c0801080d0e01050d060e1501032c0f010c1d03011503060c020a020324091203011806030b04030903020a05010f020c0d11060d1a04110d09030201110c 74
    0x1c105c000500d5440c1035140d102049503500c200340122901c0f94840551516494002c4055002c80a4145840d624089092a4480c1580d07626882031044507800d030244007098140c09042d46030140c0a10f810844804110030421481c0c120342e08045c0039007030301031a8108041041c410994007900c001d00911200c25088401032070300c800003404403c0c46802040c01c000340d240c10f000e2700c0503c031500f80e026018142140c9511000b0110f9105e04025881450071800042e10180880e9003840c640c001400c401c01c01d240e000c0515590000c0c50700c919074101c10240a03c84640b0400d480c10344042e80400b107006c444c4240c14000604140d0000707030201000300c0400c02095840364110091303910030f50b00403204070b03615801501c00800020300b0102580040000e00554184103c4d2001c091340a00182c007844058400451016888482c2c1e04440980301c5440c0141c58160300300b03824000009840400a985e1100c400e009076004c1c1c0840c003c0400d454200c1c22003894400d40080415003a12030030650340719903489d2440e607 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 55524437 1250 55523187 55523203
    0x10081e060109060b070320070b04030b060105040617060a1805100602061e04020f04020304080705010e060c0301150908010507050408070801060b1e0c120403060e0d02030a12090203030c 81
    0x14080c822040041038401c0c8900920781103450039041c01e070500036a13641c142c4040040c0c02040e1808a0303000b643c91960041040920001c194060f621503940f03045080005000e0300041680e41881800c00041022642c481c0c1512511051210b08a1301600d4800004129601590003001074144044071800ca1803d00d5000c180035814a090400c031090b0b442405a85034a41116110351450b6142d8030b4031508080c0c00e50303d9034400c1c0300405290981c0500d100003003c98009480aa998041c08503c100400c0001d1181c0103c40d00c0040040c0690b10700b2041245062005014004031092110320325000c071070140707024a000d484110002c1c4181d04d0100c00090468000e8802c0860520072380c000001d200320180303e00d02c01d44101c1003e07a880c0040b10045001d190b2403880e111103440c0400c2280000d005c84c2401030780301c000100412140d9851450410500b511031041c281480c540100420034101d940000460301d458601303007400070b01c01d407a040100300182503c1c44007a401d80400510085050000300d201c0c0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 55525687 1250 55524437 55524493
    0x11103090604150e09010b0f0903010f0207060204050114031510030f0e0c0310110d0c05040902070b04020f030316060b270403170702030703121805010f111201030b1008 74
    0x4103026000c0d0130417154500c20300c81c2c210310000400640c10b0f0950000010010786e200603002207078000401600c0303412640b000c0815a9120b5000c6014080796074082074902c080c1c18000646429818184051075040c2002181980b0400b5500c1954200c00c0c041e400c240d40344208881c0800c1405824038003280c80f0302c05422403501c05d0041d0000c0e0702c65000144202c0c00e13a00d01004003c3e0038540d100d000350005200704a1480240407052100042a40d1789000901e00b440c82200041010304241c030600c8810984400d20300e1190308140305841140390103030025081c0c240c00c03000104001401201280b01040442e980310328000040710207a1a46e6200071300a80102d200f655203585a6203020606418074905840000040e0010452030021070304c1250316500e041040b050008030000202c200619240100300200c1d2a1707515004043c800113154490b10340d1507000f2041c46860110904242140128140001450f4100b03a00c04280b0350002032104c0e502901220003100c451009038650105002c640348101 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 55526937 1250 55525687 55525697
    0x1e0803070c0509090f0c060a05271e0d11240304050c01080f0f0903040e070c0302010507030519050903190215060303090108071b20040501050d1101110309060415 71
    0x12411200000590782c6445e0f403054046c2c00400d28617010003046601c8088a0820044180280103846500c0c070800596011030b6100d1688002d00001404000301c160040400c81b103249000d5002d5644a11808200c001c0d0711000517201003407a5000665100d844540c200035200c8100d0404044080810056004900500449103000c0c2140011605180110751451034003000d40086001c250b80011102d0704074040c1d01c141c0b402c00341c0f1840c1010000a045652000081c00350491105041d028491303250006403e10b010b000a2800800080300119001c0300c10100303950710f000103040c001060095480015640c2664103604e00c0d03101703000f903840301007403002015001c007007002c16402c2c5000011101d100506071a80400c0382c1c1d4483e400e8401c030b070500b200b00ca840b5859000d4a000900c0d4041c2e040e4508211030090a84688504284001c491058001501610038001144003140480d60301e240415000d18040181e10504249981540100b10b400398111401103000b0424000102c0040c0240c0015610 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 55528187 1250 55526937 55526941
    0x70e040f06030804030b07030f090c170d0207051507050303040b0103120f0f26090f1b0a050d05150a1a0405101a0912010501061b0503041e0803070c0509 67
    0x5441101d1a51200600101042104000040e100380e403507035220300c59090000c0c0d01c0007015a058152000200102d904003841d02c0244046c48001d51143d000b100c015009001c102c41c0d4420281d602d01450090f030748034400c4030441e265103100e8401100c0c9151341c0a0b0075070742c44e4206850a051080300038001110070f0000d6000f002c0e0307210f1140d40d00c40000c00d5640c0d64640c0d21118040c0960f07016412821880c40031009030f6004520b101031008041c05184644020200c07182040c0300a400c1c00f4081d61007006219140c8001c000075526200d0301415614200c6119040c4482803820622b49020b840c891010760901904100e4030000a0780a840016007081203c44441c1807001008101c4400b00d42c40098128904802d00980210b0703002d58040c4420f10314014584099400004c2102007969241e9400d6134451006102d05030f804014804003860108415007201038a5442c1601c0f40900c0c01090005000e09003201d0442d44402c0045004101c41002d40ba680c1042e030405801403000ca005c3c040c000d0280e800 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 55529437 1250 55528187 55528211
    0xa3807030b100c020105070f02030105040b04051b030a080c1507020a0201020d0e0d06090302010e01240506040b040303030509070f09150b0f0403060203061f081b07080405041e0203070e04 82
    0x141c031041d1056203503508030b500a6140d0041da015001f40805651044d0400d94540050f24248074981c0101d000d24810700d104d180c9480d00611744103150484002005000c0c01204d46924001400f40b4521350000003162600000c1c00e10354a41700140007044074480c17040313040c07100080e00400d003035090318007e03070a541c0c41c486604c1d01921a9008440d80701c0d0480c1c159160303a804506141d00540c4c031240701c1d10000c1415906c182881e400d42c1e0440790f003c46001c0b201000103200611201400d8001c2405948140c1030510340440f000f9240958400502803617143c1c400102004424040500503003504840e0a1511380c80702058002000a1070b801e8041c030b00704070408106488000240c858a400705914186007a04550b10349000e50009031440f90004151209640150059029100c3e051620380d16545036180510340700d03041c0504c0f0300018800d6241001044041000d480455040d11000d0b85e01164407058030400c20900d40b4884603141c216480401403100380d9600c15084081070303804036418009949030003 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 55530687 1250 55529437 55529449
    0xc0718061a040512010f021809060405041a040f080d09030806030109050d0f020307020a080d080112020102070501030903110f010515060903030301060f090306020a05190f020a3807030b 81
    0x18074140c128400612041101d45800d40d00b8001e64043c03000082059202551494240c0c2c028440320240900300501111140c1072800e0844c0e80708408650921503400d043c0c5a90000b1301401050360345407010f0b100041d00b40000540300c1e5550613400401c4030354038080d800b02d81c002001c034140300328005105440801c0c9103103414052401800e4108002d40315003c00c3d0302c410344035511404082c2e819400306106070400340e581c04c42d00c01b000308401c801404401020240080036424142c11844450494164400150341c3c00201c00c02624000e0800048800050400740c5164142e100d0260349031080500311541080e040d04003d0050411403040704650000008104c0d950003128501c40d0164000d0004200c1c10340300300004000c0d0300c1241418200680c99171121b00c141c1c1c1c00410318202103100040c0401e0310403a070821307002c0d80d041c03e0315003410711859080c4002d4407108004c80140c401510301e184004800301140d07038166900c0c14440340d81c1c407503903054401a90120303007150441c022906c0c003490018203003171003 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 55531937 1250 55530687 55530719
    0x4080a0828021005100b03010b0703080606070b0f0c040306050a09020118081c0e0d030503040b0f0c0306010c03030f020c061017031207020c04020d0f0b0604060212030c0c071806 78
    0x940203840072460303ca040d00700420005115015069a031580014424000e070011340c044e1407507265207959102c542c200a466550007400b1540550000c200322004500d41c54070450300507842c020294426150102c0c0e40e112802207400c080d025600e0f12080c4000e08104bc0c1c002e80c1041d100303888010340f40364072070f10001c101d00443c80340d0070950304010055501142070555800c0c044031242064201c042400f00480c3c42030341c81d4802200401c1000041c4010311910310b4100764090001c0c03206503481e1504034102d1819010141000c2d040c0400d09014000b010b0282d000340310f4040000034210344540314130001c84d07600d02c810307600e013090001a40000304c0c0d02501d0394150310703081c903228004610703160700504200081c59005000c041103005813000048590fa8070700041c0340a0072401ea020a510002c2519401200c130100f080e14410b44040004001c01c940200702e40c004400000c00c0c42c0d859944245142d041c9109942006580b4040c4e00c401051014000b84e14070b242003d031480421842d0f8481f00340e00b0003c121 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 55533187 1250 55531937 55532017
    0x60f090b10030c02100f0905070303020f12090a0902070213050a06030303050c0703170709050a0f081c0f0c170a03052415030604090606060207080c01030203010b03060402030c04080a08 81
    0x1c034018840121388150044840d0791b6032000001603440c03103900c1e030508100094104800680108908c5403010380704000b120000320018114030f152440030700014141a001d44210185140c000c9802420355651041ca040100072041040c030003842c00e01e08100c001d04890004401103442c042c0807031010400e10058401495040e22101c2c0c21388543e6250302c84582c0e00074810300c108036071103102003695107800005100400410318040c800c01d052a41050401103001603030b50600c0305600800c290a42e011065820303da0b051300340784020448074105842003403514000401001c1000030452071055156020622418034200c2c0d076403a005541040900748104900030a40c8911600b40744400c0d00e0310783c070040d80c2001d40100300045078800d907551142950490340c040000340e041684200b042c054103008540f00400c09107811440c640c1407440015035400f000d040c80380943c0d0f0200000740188400c1c405c45015008841c2181c040f07520500c0c0c41c08056001501e03440c0620404c080c18415020f264100030340ca104 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 55534437 1250 55533187 55533193
    0x30301030b0f1018150803030708011811040b03010501030507051801051b0a0c14030307080f0703021e010c090e0f0402010309080405190e010602120715060f090b10030c02 75
    0x110084030882008000c0c091100f01080300100041840c80340709413030403a0103100c8020074100008524100c3d241c0890b4410380c601d030020400c0110580e880b18040381941c0c00e80c0140e5200c40e9940100340000d02403a0317003011114a001a001c550783d54240080e43c1214000d9074148410b076034070f52007203426024030990104038200c1040ea0200310340c06440545103140b00c0f044196403070b5500400280c81d2084601055680200301c1d2020b00010b035030800e407042e81280c00c0c1d00452910340d007940d0301c1040348501d1121400d180301c04660901014400d100448000403009045160000d540d41081c0c024500c0c1d079038030408120030380c00009100804902c000d1190703040741c203078050075902c540041d000b4200c13070310089604074002c00c00031806130f541c0c0d100d07610b1120782e0441c0c2c4902c56003843c1050103111010b0b0004c0c0309660003813030a110200700860495a0311640020088491440c182c6480c5c0a040145c000c0110320140303140101d40da0317107180d01202030480d0071900300030688004c00055044030782030501c00006070 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 55535687 1250 55534437 55534441
    0x8060901061a0306030a0609060209180942010f05040917090a090c0f021605030706050c030706110702030d030b150c0c090406020a020f0d05070b07020c2808030301030b 74
    0x42d601000d10790211016080c2c4209111659907030040b40c2601c0422100f580c0d003c035145003241840b0110107602c0c482500c01d0300544c10800245580d0b145414654a6408040c011500000c140c500d140c04164000e56095420b54412000d102c111076070074020140c095001100c00120743c9814082c081d0165000905032002543e19441c445072540200b8100390401c60503800007c84465030701c60624030396415620800d00c3c0000210003401e01000041600500c3d10880041c45940d5006c41d01100301c80d03060402980d5480000782c43d0341540542d440251802d460090741e01c100816400c0201b14041c408c4003669005140954140c0032510300c0d10044d600b010b007624000072103110f260018040722070b40d442254814030142000038003041e0102e80407102c07a80c01160301000c95404004480c03c0342000000303444c040050001c0100306000b074050240c84400c3d0f210102d00b441c1d0082c4040e01540c90f0182680d5110321040c1d03121034020000072002c40000d01400f40000f015074000c411f581c1a203600018842d096 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 55536937 1250 55535687 55535729
    0x801030b0408030a1506020f010606080c0a0309050a0b07020706090602060f15030a050a0c0504051003030e0402071406070f020706050c0703020d0201030e030403110301050105040605100f02011b05040806090106 92
    0x350308000c240513843c0d0380d070b004c1200308140c40c0d4150f903006002035801401051124401130382500d001c0d5002d10700340901a82400201075a1405992150130a481d00094200450820518081d400c0720081c01c02001c5400f440115030340485c6445c00d5458607110700c600d50f9610202241d0b1000c00310345405400d04004007003100648041c4c00c2d0100c0800050844070f1640c9552625410403502d4007044526142c0783d00100401e00b03280c09030983c01060042d41601c03c40c84c58401411b0700c03421a070041d1059600150078130030003080070740080601165100f05d51030741c6882c0308040c2058118600c0407000d4414000006a158802c0045840462500300604012881d42c1d084c402102840c1000b2410706450711101e21a461040001d480214021010401440d1f140028107003105c1040c4c008501450400308240404e8480550b1008048502d141c128840b03102840202d00400d05030084044450380600c003074404e42d60010140c0280c030741600c1503421540b00e00041301c0c220340285c8588403510801142581c41 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 55538187 1250 55536937 55536953
    0x7030806011202040e0609061c1514070c172a01020c0115150305040201140c0c15071103010c020c0d06150611011a0604140d0501020703020601150801030b04 69
    0x440d40605000004520034444030301a60002e4114180c8140c110341040b50b03a250001d120382d000042035494180e0544051a08000300d500d034040900b40e025246a1f151602e0780d25403259014809039011040c840c10840002051409204002e54015202c1c07001d038002840000e084800c806659680c5280c0c9078501050307031542d051000710382c0c590355500348a0031b080c9400a025412000d0b00c2d00d0b800c941e00174208604140603040c0307405040d081510308410000187d81040083c0b01c0000c00b45282503c45140428040c0f40003054503400e5000182c900d84115169a40d00c0030341001840364105684000c0c2c001e0605088450001c51080180d01c01d89018006042403503651443c503008a4000c00c132140310040d4041807801c40d0f40040d0000b541c3c40200303c0c3c504020722511032043d948441800801c140c41c80090083d01880c0240d44c860501ca1403000800d40d100a40204803d81c400000c1d5100e01250070081d4903203009204a1880c48117142600d50102d115603120303810b072680441f40362001c0d200e40e241c001c5 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 55539437 1250 55538187 55538191
    0x100e060d06020c030c0105070207060810090b060d0c050301090e0a020904060209030a0b0405030d0e15011a070501110c070f03030c0303020702010c02031005090c0a0f05130b09010305030a03140903070308 89
    0x180c000d42c200000300f0025070070f00c0100300d00701c1036a0020545081ca00e40c003c0c500b0280d58032000400042c801800006c4801c1821013084400011007c201d940f00a4001342c1d444c820700c468030000624080c400c840003a0800061812222442010860400d00c000c5450322403400c2032000f5030000c1034130000703400280717107501a08440201408407107980d0010303a03407009070103000e8030151001d600200304040414024005c804600004501421111000c05000085c00b071040c041e600a429890603184018600c10f016204a113400400a2094a40d8020f0074a41648000d9150025009801020a0070003890300b0520880707500d0340e41e04a408403680c90850003134000e045c0880c100300030041c40c440940d4080040c0080300c0c05c020030000d600d0418441051400100d01d0241d8003071003114404200d1076030500c42000403114144c9004c0001ca0410308000001d150108207140e000e003c101c000300501c81300001030403040c2226201040801c0810314000024039089500003905c1d41704000800000b4481c0300c40079 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 55540687 1250 55539437 55539443
    0x2070f0305060406091a0a0504060b01030204050d021011010c09050a0e010b04090207020301060e04031706120703150605060406110f07140402090111060a090218101502190317100e060d 81
    0xd00c224000d022500d4048401f501c10300e800341e4948081c4018001541315102d05e0301800d081c11482c043c1b801011840c00b02110364040d02c0780c4206946510164040c00008101d032095000030040d40003580d00240151055003d0140107204148000c0b440d9460200d191307041e101c05000325401d1a01c0e20140001a42c03044c601240c041d5200c1d90000340c01c440041d48680654030a80314140403001d10200c040341043c1c003c0c11030b0b105d000013003079600d00f8140128150341034030303009408003500b11414501c40010340039039031040350800000140011003660003408020110a107100740d4062107000324489903180b80038000e199411004e0f074650703885454940d008221606040c10910310622805403004d05181085a18052564903a40b5500071407810404085234120803809403130181c14402c1180c040c2400300e0040039004815158181d140078020030803402010403c03a11040e06007884d00e070003130003088850701e0740f0183c0d08005c000c00c1905079030304001015500c5003501d440702e03075079154100000d00715059425 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 55541937 1250 55540687 55540703
    0xe070e070509090703060501080f040c1205071706090d020c1302070f06090b0a0c0503220507030b0c0d0501050103020c0a0201030f150305011b0f091211060a02060702070f030506040609 81
    0x1644592504403d840c440c0006840010701c0c64034050015010390300c01890001111041c43c10000024114000c510980f5807084900f600310610340f410918100c2079400051010442100c20042c000c400145244980480c40030b0b0b07280d046c0c0c040f1040e84c3d558541140f055100000703403a005400304041e800342503502d00074015101c0400c0d16440d0300c4200da541200035114100b422003041040c030010700810455221500d0518031f11701e0140e00c0381010558040038081054442502101400b100f0004000515002105000242085020311a0319404880e07140323002414040005102d41c000c0c0709032220700f01d031440030b0860340340340303500443c000e2400b002014003e540e01c4502030080005145480051031080c0c00014282e1b0458282c10303881151100c00e0002c01c07208508008840f5449031300342048070480d403030021000c4010318042201d0741c5408902c40d0032803070101e200c0307004030f60000d64540500d05940aa80e0400d48541031150089141d0001800307942c05580407400007071030f651244840301d0048181c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 55543187 1250 55541937 55541947
    0x6010309060c020601050109081506150f0408010b0306011203080708070504080708030903010b06070804030b220807020a05010f020304060e030f01060303090e0f01050906130b0603130b01090e070e0705 88
    0x12182222800d650b507400603800301c80107010958200b0503103000b0b060040d00400b010b2180d4082d900d84044000d00d038a00424260108042d0041d0b22402e0303545001640900c961620f480b04a018002d004000030b01d4424401c10b000000c2d024900000ea800c050b82582d259100c59a0700d50091b1105403028000741c00f0841e04110004401006109038806062208041c65a4110030b904240c00c1d1411602028812001001b101d000241c0680483c0c08480e844981180341daa2403044604008500581c078003440f480c100307110030801c00a000204415482220703090301c001d445000440f40d2081c2c0848200c0564410041486134500031304081c8000700c001011030b2403680c141d600b11404c0d91000d6200320003182c2da40034203210301486024881ea0201c032013020380724298900000250840006091300340184156200912540e030720742c200141e403183c05040d1a90741d05046815600300a002c4070240e444220000c000304641707541c0e01a260703c241e0010010305980c2e040c5140e80b142e0f018041d01c030364148202000 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 55544437 1250 55543187 55543193
    0x4020a050306121e2407021c050409020a110d090302061602040e0304061e1e0804083112080711060d050a0c0305012106360512070507060806010309 65
    0x1804c1c4040d00300d0300040c00544515542e14101d501c2c000d6202981c02020404005404d940003503400c4c1e600352286040c0e01980c001000640b024882c035044125124000503844500b0360300228004081c1e5416070403a84448004081150000b084c0d0000035800102000b05083c2c0e4200d480e02c1d20100c0d800204006146030000680e113196600662100c4045040d04020320b070040b884261840c125a200d040442c001e0032500e154803071402d040c5a5140612920a01140a02281d44c0075030b90418414110a0100e03a9040ea80c5030300784120204000003901d0400c40400c2c8044d016442c0799205a1040959081181035039400c161b00082d080601d030410700500440440640c3c0e4000e490041c048880005071112500d10018240c2c0c5050b04030140b01402400303400480e0004103405041d407500500005525600c0790000c00394110488000642c04a0712200540d00708081450264035900c20411242c80014000d54010113009400300030301107401c2a00108649401400040d600000500d0300003040c0ca0396503 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 55545687 1250 55544437 55544473
    0x7030b0a0506040e040204050601080c03061e101106090703030503060d1106030f04020301061403031801090902121e0105090711100c11120301080c0111100e06041104020a05030612 79
    0x4c2c0c81142c40039103810501c015400c282c8070703c6400010a01e402242d900d04180c20120b540300c090101402485039001c1000d0483c1c1d003002e64003d46000070a0300d45004540c0000a1500e145440b940042d4011b0030007150380c041d000580c000491380d041c3c94070381c116076407101004100306515106944041810044408607581c042c02144140c005070380451141c2854018103084841941200d00592030441c6040d801c1d640020945400d00c64800d102d000070462140100d8100c5a0b6602c0707852150300218882101044070fa1041d8400ea150805950203c489414191800d120070311512741c000741c10002080d40f00e07120342c42030241510100219101c080402400c08210351410744140000b45614401101450050141c500e5141c00e144003542154103240c0b030715855800b925100f6050203d51740b41050380340018040001408107840b420440c01c500451010340780c200460b4125510300c070b100c0c071842c002d14040c82980c3c0c0008240d9500c5095035a45001e1050203280d82c4d0150300103200d06140d58850480c08 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 55546937 1250 55545687 55545689
    0x11d040b0405040f06060b120f1e0a0c02010e0a080702010f14040306060608090d0207050d02030a060c02011b03020a0e09060607060c1d04060503121e0424080f07030b0a050604 77
    0x2c043d4613400c43e040d801e044048490517000400421001c110300107040824429040d0007098169480d002130700c5840d2a106200080c0d0105001c1d620ba100800003025800c0e4040e400030725031070b0004d20007000c1c000002521036281900040c12284240072103005075105025402c8546d00034104400c20145000700001320ba0010fa00849001d6102c081c14440b0343d500059250300002000000c0054004103580a5103401440c0941801039240101d504195a07041140d90f08098003c40c041041c5001d01100038043d000303804080111401c00341503800c1c41c510034400c5072524841a50b5000780703450394908018680b400070381042d82c40f09080c401400403d55078401c440c00b46815440d800040c0420006901d21240346240341482145007040421083e1008030300c410b4100c0781c1785c4a4950b1034060080440010510784200103641d800490b010808409015414480c10a80e82d0011680c810104003101c4c950001c07200f0400c6600300401144aa60090304850024840109404880313512003011404c1c44d041 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 55548187 1250 55546937 55546943
    0x60f250f0303140f041103030409020f2107120f02070203010c030c030b010e0a1a070807050703020a0e1612182004020c1c030213030b04060e010b011d040b040504 71
    0x161600d01410141c143c440c4811552040541e91a00d2502d500c0e0000c01c014000d0020f030005000040d00e0010742c2d02442203401418a003481191a03140410003480c16410801004d005410b50014140844000b42e18148c030030040e680ea1b1346225451038030203030058855a030000c580386400340040001641e081c0074604029107596030001e210a01d0340c1c8000c0588289000d80c906006071201a280c040d199998041e0990302e00e6211580505000c5145440501c5503000c080c004d80004190303042048008035010084034022566200c0907501c0f51100400da91094580780e220b01d4554a034200b545000b100200000c0008007000a10307400d440a070420050004401100d076150007002e0307100c4d0400c041100c024990300c10342d01141000e544600c1240d031240e040080c4001da081e00e003880382d0050320036011511085940c80740320f50016568a420403c40310140e90458020741803695200203114144106030790460f050b9070380e007540c82d04004402c17402e240c2094000d412588a00407011039864900815001e144 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 55549437 1250 55548187 55548203
    0x120c011e090b01090501060207121104110409050705160209090c03030a0e04110406050901080a09170c0615011d040213060e01090f05061b012a0e0a05060f25 69
    0x4118540b011030900305800065403945400010710000360300040c079a0a40e94100112404601c09041c0086481d0102c00601c0c1d019003010610b01a01702d0440240040b42c42e0101d00317102981300c5034010356050050f600340d07101508141000d80003504d07000c051682c0007003400d07040c1e0f5107410480d000b1900707550191480a020403501c030303004c0156050a02c52b0740c455903a0000745509103410604000c080307100b106d019904000380da5002c200f02400a61144440c01c2d4850244410544902412013080e000002c5600c000c0c041e03200003a00645858002c605510016980c1015102c003064074000b0462202e0b01e5550010b80c00d00440d54600c1410036140090050b83d15580c17035012504000412241c004e401804040b41c0c810340170000c54a90005031200701628824411309c3c0e132040b00305a40184040521110080c003080020048403c041400c1200d4102d940c2d55007140074400c80c244207441001c0d104d036603017120007001103500b4003071214081e001e51402020014403040a01d44400104084503200b40d401d06 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 55550687 1250 55549437 55549451
    0x7060c1e0602070f0b1e04080f0f0f0c010504020a121a1b0409060305190b060907030b040f0b0906040213090504050c0a080f012a03150510030204180b03120c011e 71
    0x150010141c01d00c0e41120120146d403c0c6010b81d50790f44240134842e0018a22200800c90b0601c5841e0442510b00b52050b404215490710b1810300d01c60701a0409aa05a0250035003a002207400c18013000603085030717500010000300350060101d0041e4084401031100c0440040b48444d07541c0141e10600400003040c141001041080c11403c040d414002150b801c03007084200034400c040003c0207510941e51052003160710301c8280d41c9004040c1c001c0c140503103150764418644000c0744140442a402114908010b80e9030704456501c05c01404100e2140c505d90758100d4506400800441d2100d03040540c0c414807030001c2c0d40480c41c421010460028144d080041d0070f4009140c224005802485100003441000000c8110100426031038100c9a0800c2d0000c0209916484400c0d880000402c4a03030060502910407044000710301d4004009420034058442240c680081038000d0a1860080c42807405000740a450804407205e1251150b40c07145200351030035503c4102d0000383d640c01c0c60100540000c5500046000 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 55551937 1250 55550687 55550701
    0x11151308060a06080d170709051f030b0102010e1207020a03050706051b070f060e0301060e0a0614030309060913060302060307050702030d020105090d030207060b030304080a0507060c1e0602070f0b 86
    0xa1882600804c80e15402100413001e840e50269602c0964013140701c040005844000080f2500355050b0051a0801c46056058a407640010a03804800d030555500f00b159000c081c0c0124280c0e40e1002c0100e580d85c1c000c075613a03c40e50201030004c002c00f40c0300404040203550360340d0341e0074100b6829038403940210b24080341c0c0b94502000b5048032029254904003505541d07003810f1011401c2c0506008a1013000001d090740741280c3c03030940c0400040c0000310252007003440e0a603d01800340056002750120a0850080d0440d1818004151903070a07030300420742401c0c14031800030300140d015425150b01e140b42e1a01c80000250b212000214050156070303999959070611401071500d8050a10b00c2c10003168074200402451000115010200030070900d4050b0350b943e054101840509404225070b58180000a40012081d04c0029400c1903d40b10300c068518090743c1d11801d0303070740140b0342c130010b08001c0200e015042c1d4130380c400d0032100c02c0c4c0303203e50001401c0c00465143e406a03402801c108a8041002c44d00f13100b01 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 55553187 1250 55551937 55551941
    0x40e010e070b090307031202010e1e0c030703050d030c120f05040b060d020a030201030203101d090d0813080a030609050a090204050a02040501021b04060314070303170411151308060a 80
    0x390140380d24161038072030070b6004aa51001c003440050001040c03000c7c00c16425100b03402884c454400c100803600c005d2180012521098200014460140f0500d8624071140c10080340e613600b100d4010003d00051a01d0b11400e03030103002c80c0781c3d0300b008010700c250007103041d01001d11500203090700302e801c005170354509071030000300d110400b45c16184180300429007500103035203102c500401c2c0c03036080c038002d0b0301d0f5102e040207044e0481554000c81d1000c0500842081e090500003940c1c0d11601e10401151080c250b560010358213220203460b824200d0301c0c1d1920660100e0750100c000d00321042c031450001a41740d030350082501280d609945501d4000d888681203019071401c0e0040e9504110f5007801140741a02c4c11001079a681600000b0201c4c2e64200d0890410070341e1540d00c080000c40d080628a8003169915549507100c45440c0411000308a0b050009002c0206003005d0500c00c903440000c142200c3c82d10b204006010040c10100104400200408420700300c1840c3c01400802c400700081c82181409051082 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 55554437 1250 55553187 55553189
    0xf020a0807030605013002150903070603020d1103090706140f0c010b040608030412060e03120903070501060909020a091a03010213050103060909031707090e070906020d090b03071d040e010e07 84
    0x2040500c01c00160201c0e20300e495640300c0c0746c0d6044410a840b4180d41c1e0150300c01c0c2c003d501c1015410b00550100084007034040c0c001b130162041203001040b081442d070501caa00d0b40401c1d14105840d5100980901c001c82c000d84060140504076000c06003820700003004000340c3c1d40855011001c99456400841d01818039016040c050541d510195003417070b003040d410103401a0704901c054400780e119000c078110aa000c2c001c4511440d8a1002c91a0518108100b15903d41c44070208481d151310302030001a0f298482e10403440040da000700040080ca00c2c068107000642481949408612040040180360b83d070248018523042021a030001c411074501800501121103984c030400039142041c0d211000650311030f43c0c40c06041c1c010100b014845d103c10108881101c000d0704a0607130525039205008110fa080704404040368081c0d400c9034407003080c0c1c2c4821144030540d0700c114070f500c480034030219004074000c011003189020f2041d072000c1c00300c580b080041d05490f001c000852160b50b403500c80d83d0401380103001c418 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 55555687 1250 55554437 55554479
    0xc1f0513021014031617010e0a1a0307030302060403120b0f0f03010f0501080d140f0304030315030803010e01180207050a02041805100c140f160201030207150c0206070201180f020a080703060501 85
    0x40341d642c17508c1c030000c1c0d0b21203004021000300750b075521405a40410700c840d4202460741c02341c00c1310000e42d1240f4019580303900c140c50580114240090310582c4417124014000c030170f4009081c1300302400400b070034022546090204982c0c5552240e0310072904000e03900c00c00d1f00030211513000301540702501d5000f60401c2440d410611214030708221642c0400a1042242d8120340e15240000e8031104d0112400c0304805c0e69040208038140001c00000c0b404a00c01030107042e16034041e5085860001820300204920071154014101d800100241d009440d02e0f41c130070140a003004844050f03400311035940504049148d002c5071185680d03440010702044d48100500000da010090312840c00b52004c88200041c00340d405511050300c1540c1000086901c250155a801c030703803000903040c40b00c40c440380f402c0241c1014400c660046c4074442c00104440c0c414015611200b036000b00e44502d80000d51202c214040c9400002d0781c014501000018181c0b408000741d40046015070000079072541021080d10281500d56640 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 55556937 1250 55555687 55555727
    0x110a05061504020c12070503070b070f0e010f020a02011808030a02061e0105030a0f0302010623090c0310030b0a021216020f070b040e07140c1f05130210140316 70
    0x70100010340051070f800c0007200003c1c070503206c10742482d24a181d0312503c000144420303451400e0203140d9400010b40301c04001c0684469a014019400440e1091084a6458010f9011080d4079000d94000c5d0060201d240c000c3c101d00142e2500e400e000392855002841000050340050200154441d100d00340d40590100c000751b6003019450240060b9840c00007540c080d221200d04101481018004d600c19402407407002d00c2030401681c201d0041c94266120011709018007488400203003410f10300d40c01c0300e126000c0342d82e510510b9804c5444540c0c1c15003000b48002e040e1507082246092051500920a1007020000310a07500c4007140c1d14000c2c00e20712500301e043c86a40c8807104c1407117070841c100182d13400ea64220111484640e140401203c810700f01c4200c00c01c0c5a04000f4100340c07000c402050741034280c0c8010719401d54900d480704c044800c5401c1155500b02c06684440d07981b00618118400102c05222450504070301c14900680e40c4960b4800d907610191241170b0000b01a0072a08250281c06101b02c044074 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 55558187 1250 55556937 55556947
    0x302040f18150b090114040f110f070305040e0103081c021c0506030c090906070f0c15050624030406060b030f0612030705010908040e01170a1101110a0506150402 71
    0x101ca50314000d10780040400802c140d000d0844600c0d54080e142c0740030003c00e042071135695108004c9180c07202c648414096810490240510096802002c2c84103c0c1d4582c1c040c035011a6031160390107504545821030410030204400204580e50500b0b05003c0d501481081d42d8403802c0380c50180c1080082d01d103220059006000100041e01103441d000c060a01c40100854030b6624a40002e0502c1101c0d00d07071a5010304d40c1001d00c80d100000085491041409880e4640b49101030034080e03601c400d01c21001802c4601c080480c00f00101560452a0403d0000c1c0c24240f444040c8001500c01748c06206d40c484000c40c002c02004140085801404000c3c03107002001032450404a03e1101c0d43c0000905081c010100680a010280c00c200121510b50341c0000c02008a6170051418100b154000d00c100c1c071041282e20004200313041c00802d0b0f8a4281341c980010603c2c0805035442920b2500d03226271086c1409130350000810304c0a81402100348151040c03000d8011491328250b00512012100100c500403481404 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 55559437 1250 55558187 55558211
    0x218010e03120319020c10090204061706060607060b030f030703031b0516080f0c0105100b0906190c12030c0305070306050f090402030f0f1b01170105120709020408070302040f 77
    0x40f01e401101204916030100039029807080644124105640644500082c13019035400941c003214850344212014080940d070b5101c2c080d0725480308108641175410107000b203030f02460084014440c03588201c60100d84600c03400b001070b04044410701d412541c0d41000500104040d030601c243c52082d0401441200000c1021a00070558003400805c48080100c41000c81c5c01d0041003400d4907102c40040c900c0ca56200008900d480c042e00040d00d00d000c0c0c568851402103102c202c0c200a03034a0b0b00d003003d40000d00f088405603100c50000c801030030401c10b015100b041140031070742c81607038200b40c150b0b00e45001c50b8031010721800404030b0704010200700400d4074020b020300c00c0b40d8640c03002040449049410070b45a440310f00002e030820342d0010042c0500d01c14581e1385001c95001103268801707400c00d00c1c0c1e020310400e450001940d049281740403a00d6207890001c014030080c40e10032003000106540a044a10395031b1913181940880e40070707800121107503110910410446c5400c3c0660020940600740500100103100 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 55560687 1250 55559437 55559473
    0xb0c16060c1b0801110d0b03010501080a0305070c03080f030f0a0c14090301020d020711030613030206060405040807060911030d0309021c020d060c230c06070e010c060218010e03 78
    0x58020042c400d0450382401481105101e0300c00303008410001c00081480d05198a00c0303501c5810400441d80c1171019110b094501032259074100c034041c2016196002603a03504503001c0d030060000720760b00108004c3c0030021442d8207003d004184502c50342c066990070030101d4400c00700001040c5036103076401c2652030025a580f203140706448146002c00c654541c400440002d02900800c1900305c9801d02c085030103010300241d140100c000c0f001c25030980e5071030340720000760b81c0c4205880390000d00903a2003080403c890307041651246900500411034181070210a40ea11f5040d190861029030f1112262286051035203400e0040800316101d60070200428001980811035010690b800381d410445803c2032581035440c2c0e40e0014800c50b0340715408005140023803a001e040b85440f04001ca040501d10f0401c082c0d000034803411180b889100728010602d44d5a081c07801c803406a85103190030b0402103403400080010b90580040c040c0800c2040090b0629259000010070100316071405038825400803150f030308014080 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 55561937 1250 55560687 55560707
    0x11109040e060603070501080c0c0307060219080c03040b06040b03100605010f020c0d060b01020106031b0905060a120f03030e0f0a0b060604301505040303140712050a0b03070b0c1606 80
    0x83c2800c0e11349130348843c22700049000740710000100340800204101003008550050000070025502002c0c100c071421004c40d95000100d0341c211141201b000803c01003042d084150368032500081c0045000d040c03010101e41020452075880b9403082d00c940d000d0000b0340e044107404010013224401401c0b003d0020002482c40b20703040c080038000c01d56510f0b5031900740c0d00c03c1d04284080d503009045c9009103490441503854056482c415410594905008200316140800d00401250803003003002c14843d1035a01c80c0030020300d1258007242450b54035070079010701c44014412203030108107090140005201c6030809840c1d00340d00a0070310b0b02c03c0404200610920304a0411401620302400b00c403409600000c84102c001c110380701014000c1050406014900c11031900510700c0b56100f913409104148100b40e000181030426201240411802034001c201e18107103620040c0e112148240206410081201117400d0282e00d8124003005000068040440c5104002c100703614549603400022403494642c0040601c185 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 55563187 1250 55561937 55561939
    0x714030a03050904110301060206040b07050304021323011203090512031207020703050109110111010c05090d0c030605100e0f04030801061b050f0f160b0327011109040e0606030705 79
    0x103d02846140c8807030b840700c030400c0d2842c800c1590b0707135840d400040c5d5151011107088036800c0310280011505ca10643c01d8030b00999010300148002ea45001c40e0f000605401c421900310402101c000505681411005a0090031400c000d042501800e0a004010707420350341000c0d00610a00d410007181075000030840b401d00d030820f00750340750940302c001089040c041e4961010b0301e0b035802c00110b441803140749603990400700306c02d0301d5502078221a80c0715107090300c090021300c4020800a009a080c2410310441d8101c10368030440380e0100c03040c1c40e039071814200d03402a925001a500707942e50501403503078491400c40c1c01c007032104008180c901d0559802408554140641b00c00c128001000b2a400703d043c1ea00e207000e0641c800103803100481c0640c0da01d9650162904071301624401c15104800502018060505940d5800442455603492a02c9041050782d464840840e000700b45401d00c6240d4401e12842141c02003111640707540303848d40010030003999000d00c42242550003c40900502d0759000884e1011100 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 55564437 1250 55563187 55563197
    0x306010f0902091f020304060e09041a0705160506010305150c030a181208060906011110020c0703080a090e0109290102100c0503040203100219050f19030b030714030a03 74
    0x81e0390010034661a4030413141650008011100702c00240c0100140003513403045d60b5a000c20892a10410030400f17400e0b50090a1001d03003444045825a0f40000c1c1540100107082c8540b81150b001d8116555034203001080e62240c10440040c03003007100501c41100c1c1c400d08403c401d8502c1c24012404840d07072102401c8202050703540c08803a0b03400b0b1448034030345459907040554409000941071000e00020703000c6456502c5242e240c0c0029000390b000f02e0414016800c0d0b500100004c080c5604003000960001091980c1c47c411410b00200141110004002801c41907590300030980c90001c561038040410b030000e04d0035900b0518115a00d08034586251030708940c0301c00302c1507180740d0340b00140d00b080714500c0032014460034688000700654010005502642c400d40440d640d850008480c20224050651f041c03400300c0102d5402c0304028860740140007851801812280b4024217640f0100b4110080c41414003c01e031545880c5080d46020f1200d0002041681d052150704050000025101c45007594010f013804 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 55565687 1250 55564437 55564447
    0x906060604030818010c0206030a0203090607020f0c01030e03120903220b0a0e01030908041205060903090109060503180102030a0c0f020714010507110d1b060903030c060c03020d0501060e030c0306010f0902 90
    0x603200c1d8002886c0140c02802090b52410a00071060196004542d54138051007580c010039401480015450780e85000040607040204908004501408840340121302500c024803d00c4c0265840354019401600e0a200455480c181700041c400d50b0400d041d03d840d00884850070030050305461104035814450146480241141c5440c0160000d018041c0007420303219020802040350b620030038410700301c036000c1c804a0701d05a9445000b07643e80c4c401c43c3e400500007001d1a5080007564040c9010799000254a510702c0508a060f032001d03822600101d4200411035103800503800710035001031480782d4220251024200850606000c921107202224445042020001d019030a21000384400401c07803034001c00b520030b004500c0c02c00360250100007420905920392202c2c0041c00724001c20410080faa41a101d481f03455140c0c4d16004001c01c40070444906041d02001450100d600d6071240d54023806170f80d21924180d1405400781481c124031f1544d00f60280d0b00c19001881501c641c6842d140c22070311840381c05030f070324 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 55566937 1250 55565687 55565689
    0x60e0604033906030f02040518040212010c020105100605070309051903020303030103060504110603091f06050904030915090b070f030512040b0a0b01050405011b050c030f060906060604030818 84
    0x180800486903040141c0804604600e04420310340040f42e140341d900f0700424a1244482c0200d12132803181541c0301480f00c6107600c401c00521149a0700900080c40e451001c0d10202d580d9082d41c000d910f111005075550000c00202c00449a04007000d08075520b0014144601a074001d04a00c0e124001e442c440c80307a07049040603400701d1440e490050359010b070640303860b96901e15142028080599003280e10342c0341c2d254a0b40382400d1040a90f4824332016000b801d29100c1c00120189140c80d90098040c01074940e02e002c20f40c0d0301c3d480c01081c0554070942d14850315924255485519001c50800e800400c5040c140820203803c180081c0c0d118160040484454803c00703103030540b4544219685110f49650034001c00050112240c04140304103045071050040003059401110203100c2d5015140c0890b07040c030fa5081805a1800419107006d2241044580503020f11001901d4180144a455460741c0480204015101d040c40b0391a00700070151013860074203003113558110740c034050368401c40704440d01241c015012b = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 55568187 1250 55566937 55566983
    0x51911041d0109050f060c0703080408070c0b0c0c01030b06160308060607120f1101050402100315030606080a032a03180b040f080c030d0819020c0102030a090c060e060403 75
    0x520074041e4002c01240805140c180e4803491041c0b01d82c44540a90000500c00e0400c2c1000c0f20399481e803540c1d9440041e0303076079a00d10819030401031098490b08441200810082e141500800e440440440100041c2d84010001016280020400da0140005001f02c1000500442c0070101483d858207200402d03130b80d4030300402c0b181d005070b40c001707400c40c5107110f401c254168119001c122240c041381c0d00c0ca241c4001c59000242644d0741038400a4001e4166011403c145100c0c0d480b66120400015600003074594035180c44c000e489050b00f01e03485640012422004240e004401d500741c039801c140c50044044000500c40e800c00020880203000e00c81800156400741120707141d6071000d0600c407040d05444a0320303140d51400003011405612100d101d801c3c1d401e440c1d0b18000480300c0e85900556220041c6075950891081c54042c1c3c01f081d604100d40074040101038032401c1c00510700c01c03c0b0000f4000380e1244107081907509010186d0052042c04985251844c07a5125801110156500b00600d401c0c403080010b56a11 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 55569437 1250 55568187 55568231
    0x16030b0405010609030b0703020c07050907020f060c04090f050103080a03020901020a0606080709110c07090b04140f0a0506010f02060f0403090b1603030b0312040905060f0909010905191104 83
    0x10348680382100100e08207800c004000e0131380e07024180451a40d544d031b40081d0101d12030200603102551003500108050324101a40680c000ea2900c1560484100303100d01600e0401c050b1003c007172810010805125461041c4150700110703c4910040c8203d51554603044203034031400c003100b400c06070005203801840c0d00030000136446542c030040401100d0382e520700107500c84d0a54004c5200c800e0400200d00b18400c49c81082d12090007100003d0084c3c03614100003440140502d203c03042c0c2003a1910b00041104188281507031141c0034110355031040b890480c120f50120717103006010074103024850780820096640050481c0d408440c0e1090781c0c00907140c5042c207480c0f900d0254004001060005046603c0208084481d6801d070300c280c030240f1803917101004060f140c00144104030641601130008100010f1141c1086030862005080d001b0200e0000d00400c06986045908400983d15040400c04001d4100200d00c010079202451817107100c6d40396a070360741c615a680300c2c003841292600c0007c200b00441c050303051 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 55570687 1250 55569437 55569439
    0xc0302040e01060503060f0414130302010608010204080f0d052505150c0a0906030501061704060e030301030c060e0108010303090e0a0b19080601050604030b0c0a0203040302130506042316030b 84
    0x3224940e0369020080803580101e86c3d0034020f90048058502500701405114038400e60907040000c603580e5071610109184d100101503003190b4a80100040c264020303c0100003a2415030068035001480200e0245440070350150074003000800c1209681000d02c4240c40c1000c3d07140d4000c0a03901108904003a80f4011032084030a0070f00040c1c1d02132003500d90222009101c04100b50f210404c16a03560f03003041c0c04495003403094501180403585200c070241e424881080c1e01a03c0340c1400504202090313440c9103150404d801c2210042d801ca0018000f5540085181d5098038007480c10468941c1903540041210342d2621480400480b10320100c1c0c201d400c107400440c17015101400324034522540c1c810600a100701841510341d640070f0340e400032078103040c040115401d4a4101140d0710700c1d600c0b4200e0b944801e03882a071942045000600000c401681d6000c0c3d0705408600801001c6064285101040222400d042488034148844101041182d181c10711840e0b00c02a180c4641180842501090700607114026440e = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 55571937 1250 55570687 55570709
    0x703020304050415141206070f0210060303080108160b070305070305071502030114031209010c0302160303030903030c0309170310030206040905040308010b0f0d050c07050a12080916090c030204 85
    0x48004544c03250148012101c400c03600040c1d40b6014024001e0701c003003200115002d0f400882c000380020303009000d100e850055510440380361450008194040b01c00580003200080c0c205001000415000c002c103400c5410030485400c1e0706407508455038024400c1040080c1400320100f401e80a06006500b542c494940120000d01641c6800030300c01e009500c2401403e1012040c001c030403900341000a03c5c14400000140c14034500880d0314015a05800d000004408500c10041000780c61840b00c00700100a52281d02c010032100784520b005029190803040000416151488190109603898058001c40420078a1150b0700c0e2074110384580c03c9034a5800c06900310302d000500252504103a0322003403059000740e0382c03020140d8881c5403c400302c3c400e802400c01034070000e200101a60443e0703030007641c009081403001d628250b51a9181c5040c003608402c1901d4240000c3c030001419a0407040d61540003200700701134006e0607444000f0ba03a089006001c3c1030200340d650300c8a4540f050099045402500080903e = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 55573187 1250 55571937 55571951
    0x106020c0d0303021b0c0a060201020c07031106090a090c020c0d02030d030c02070503010e1501060206040b0411130911040b03030406020a230a0b01150c0804090207210f02160602070b07030203040504 87
    0x640c0c420307100c40110f0041c0c560507c0003c030588188251140c2d81036160140000701d00c4d40d210440c0e0100e100c62403580c02107080003840c0140c4d075464010001000056004540d61591513406420500d0142800b0701800e035090f50207005a4000c158080101018217000450310381d0800203d14200d045d03040030780c16601c0c0140e8038200c80d00c0001c40303008004600280500c1aa00c9010890311600107682c0140101c0c110001301c0c2c0040e185049018904074090016500003100240309026202145002d0381c5605800207060081d0515000b00150000150004d510705440c10b107000f5659031000c00054003d03500140e81c440c0d81c07118500c80f5010000b000c01111007c4500d8100380d00810403c1c1710384200c181800204034241d5000d00c44c580440340e0001c0a490034035140102c02000395108200849241e16202000500810120b203c032501040682c1c4500020b00070504c0a40380152021903400000c00c0300c903040104a0307000801d2800d0b00c40d490700880c2c449a0500e4164607601944e0000c61b40b2504102d0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 55574437 1250 55573187 55573237
    0x20a1e0c0501060f24090515070c17010c110303070f0216031212110909130f0b061003020c101d01050a0203062d01030203150607050604020301140106020c0d030302 72
    0x540d90058411281c00c1d8001c1c40844001016110004154000480c6c0142d1003000149442e000004204a08a420500d4104591303680e5101e00030580041c0c1e04154400d000b132002c20024400c40c0c89c40c0754036084c55003166540081069807404020034880c2000300d22050481405e10a120702964010310214071080d250300c13032808015a20101e200c000014101c8200e01c039003a40036002d020111441118800c1c68900c1050910240a01c0200395104202440a40703c0000b0881c0c504074a556018a0944d401400c100081104441e006005170b0f00b01801440b80c80203100740407641520107034803202c0006140c544110710744070000e541d81c1ca6000d65440d04041065034130046d0000d610514040700d56907100c101d12103503003005442011003c025540e42e0045c0142c554020fa00454115001412888019001c0000907519a210880c11503031504841c080c401182001d0107043d94071400a00c0800480d810700100035921019031080c0343c0f040034045610014140241d0440310101c0c0741c284550f0104060720 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 55575543 1106 55574437 55574459
    0x9060c140609010b090105030d0e040902011704030e0f09040b07030506130c090e0f040503120c13080f0c01030e0c010302090303090901150909020a1e0c050106 70
    0x40e03404046020108105481022080008581501420203220745020103a000364000d511448001c00e4a681100c562042141c0079280090044841e0004a840070032300320303a003640440040103200900d80e00c003200c3c07102d446056400f0118059000c0501c064068210b030054640682a0042040c0c10300c680c10443e04604014030310145403000c480c9540488120b0316881002c60980d88080205403408200d080d448005036461000c1c0e0324054a030310307440313200c0e6044091440b90b03200b001841c011352070f8040e2000c42c541e0615420100d0f803035006107a6291601e11500c0359601c2020000c0b00590710902170111400d0800c0301500c0c40b007403180c00640c040d40001d000c80713505001c184001c24603600c803005014000c0c008040d000e88022041507020b0700b07800103600440b0040f1b004000400d4541e4202c1e0511000ca040c08214448016103208101d4076101c8032000100301e94240035001071109408 = true := by decide +kernel

theorem cover : BRFrame.Cov 55395687 55575543 := by
  have h0 := BRFrame.cov_init 55395687
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55395687 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55395687 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55395687 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55395687 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55395687 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55395687 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55395687 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55395687 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55395687 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55395687 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55395687 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55395687 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55395687 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55395687 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55395687 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55395687 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55395687 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55395687 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55395687 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55395687 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55395687 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55395687 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55395687 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55395687 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55395687 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55395687 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55395687 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55395687 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55395687 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55395687 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55395687 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55395687 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55395687 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55395687 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55395687 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55395687 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55395687 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55395687 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55395687 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55395687 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55395687 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55395687 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55395687 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55395687 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55395687 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55395687 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55395687 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55395687 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55395687 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55395687 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55395687 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55395687 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55395687 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55395687 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55395687 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55395687 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55395687 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55395687 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55395687 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55395687 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55395687 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55395687 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55395687 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55395687 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55395687 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55395687 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55395687 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55395687 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55395687 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55395687 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55395687 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55395687 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55395687 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55395687 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55395687 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55395687 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55395687 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55395687 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55395687 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55395687 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55395687 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55395687 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55395687 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55395687 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55395687 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55395687 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55395687 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55395687 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55395687 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55395687 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55395687 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55395687 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55395687 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55395687 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55395687 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55395687 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55395687 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55395687 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55395687 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55395687 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55395687 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55395687 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55395687 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55395687 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55395687 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55395687 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55395687 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55395687 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55395687 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55395687 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55395687 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55395687 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55395687 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55395687 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55395687 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55395687 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55395687 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55395687 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55395687 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55395687 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55395687 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55395687 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55395687 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55395687 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55395687 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55395687 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55395687 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55395687 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55395687 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55395687 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55395687 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55395687 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55395687 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55395687 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55395687 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55395687 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55395687 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55395687 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55395687 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55395687 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55395687 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55395687 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55395687 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55395687 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 55395687 ≤ n) (h2 : n < 55575543) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
