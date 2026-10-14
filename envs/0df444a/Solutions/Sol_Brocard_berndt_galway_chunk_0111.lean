-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0111
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T17:53:44.503233+00:00
-- url     : https://prove2.me/submissions/10a8b0f2-7e3a-4db8-9a8f-f58e2ebc6c11

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 19784179 ≤ n < 19964035 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 19785429 1250 19784179 19784189
    0x12160804030605040b0a0c05040b0a02150a0603020a090c0905040207060e010c0504090c110601061808100605010807050702030a11120f0a0b01060207030317060f1008060a120201081b04 81
    0x1010030000144095903109510940c02118240010764400300540200c0c2c1d82d00c92004007251090000b4054450104081c00ca10300346401260744a00d48118410703050310303044611880542e00c841081c0708504001307507608d000b00503401c020302c07440c6c8003000003070702c80f030094003416014039400300710f900900c4030a4000c0c1d4000f4040200070040d0b018180b0000701194854001c51044900b8054000380c018800c0307940c0c0c3c0c3c0607295403015164030b90800100701d42c0da0b000c080081000c4048600c01060110051200952081000d03100044142c6000000342c0b8160000b00154140b22090000d80c0142c2c030301042c200c08087d4060050b00702d081d25800003a03880400c1c400d034560648510340c018083c07100b000461a840c60700428096141d603a031543c007240d0380d201c28000200010035051001d81c481ca0075120032600044000c05041008051902080007840c080f0030030b500160840702402154245011801d0240c503001941c8846051030343c0010341105006440449002d138249290505441460143d41c060302c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 19786679 1250 19785429 19785443
    0x12090209073f0b01020c09010b0309060105010f020a120306090603060906060b031311010c020405070302180f1804080c0106080304030302010c0201051b07050f0d11010e01050105031216 81
    0x428110801408201d05825511407403001c1014004030704507071035010940b1184000070180200288540030040c29944425034103611400c440341355142e480040e228041c20103a000310703840f46032010700c0910b00501070740310a06009030340f00000d120b10360100b030144449030440380d544422405040210028803156106a6805251010100400c0126041443c02d54050301090000941382c00c41c0b40c04a20082e254004403003003640500d00056045c0c0c0315020001c80505101050311415000b14007511004c071014000660300103282409590400521141c0690941d04451381c400814086801401401d41c44480078a41c80001010000c0c6141103c1c00c00c1c2c1440c0091003423940d01d202c138a0b52500a4041213000d0b500f425030a0114510500c1030710b20606500700803e05070035440d98480603e17444903000795501c0c0a142807040082034200a100740c0030f000c2d9a2070b0724000071036402d01c0e030844541002e010800d0b414900100f005a90010340c5681241c031040241d550b03690251355048044004010042c041 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 19787929 1250 19786679 19786681
    0x1a09010602030901110106050108160c060203040b010303110a0321060f03060c0f0302030903040603020901030207050f1605010207180b0307030609030306030311030c07031203020d05040f050f07080a0312090209 92
    0xd280d000c80030340040034081e02c0755107070b42a0710743d009401d03210703503024090019503010700240c2d041079503042c5480e04511905010340030f0721664030307044242d0b481241c06580c2e048481004008155001c42092045e8012070040c0020b03804542d03005010000740104040308441d90185010207044031b91121004005001074038903d80c0e540c0c5020406040203000d01808030381d0b400f4030303030803858060f000302d038032641c3c0d8031001d5441c00c0e051a1041d8002e412040d50b06042503804c1c05a000021000c00c0041440960100202016034500f6924080e01c1e2098000d681103401c441c1e400c02500c5900481c50700d1028048401140951442d00400c0c581001944098a5241405644001e164041c4c2c00302c010750b030282d074904a0000e00314403142e030349108074000c1071450750003c0e500300f0204003010b604401807500d85c5405850031b20301000c1e01080d50025901554440c0b0034240c40c00400c60100000c103080580c402c00303065170754907103510b45454600b080c0018003409120702035642d40381c2007a4812882c103030303000b4003500c41 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 19789179 1250 19787929 19787939
    0x6050703121508070e01080105090a0c0515090607050109060501120b06041d060109060e01060c0f12120608030d0b0a0f0e04020303040f0602030a02210703110c0301051f05010305070801091a0901 85
    0x314045c03e02c1031102c15440d1401184000d5004290b24a00c590041c100b030100903d09800d200070b201d25031010350442ca401f0b0160445c40c4e52a4001450340c1c0f40100c0001c264416541030020423144c0690040410012500803180040c80318541c040d48a0f03004c807000179801f98940c69030341c21a280700955030264040c160010440300741340c0d8031000540702c100d50300c240d00baa00c56109540302d17030401401404000c0500e040100140b484030b0085202042c910340242804410b4502d0815901c07142c001e41001e800c042643c900c40ca800380301c0c90b20b004804450303181c103071803510075030b009a5065030060f10002c1958400140644d10704000700c0e03004208ce0842118100d40c2c0d0400291030340c00c01e414483c018065a00d652498294080c2c031100300006580120f80f40c0a000c1d5016143c21080503100b4085026072996031086035001c1c490144a82e0110304d101c4810140030014501c014a0713504290305162400c400e010382a64408803045c151031090f03400049240480b2103491048280d5107419a00801200011036 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 19790429 1250 19789179 19789199
    0x3040b0307020d030c080705030103140a05030c0a030201140c0306010503130f0b0f060a03031b0c0b070302030301030c08030a1209050309040603240b0f0409030c0507030b040c0605070312150807 85
    0x142d8501107076420406608017080031609402c1c00c0e0b40c0c540c0040e00500041c004101e084445d841030b01d03217140c2180c151040a80d10076042d50000041c06c00301d0341000541d01c2c103040c0c081c01900e00942c0000341c001c946160141c458062070102411441c1000320110008450409902d00c2044440c0c0042e65440132543c40d14040c000c400c400c64902070700707586280c00310345c8a042400c842401d4036450341b00c51050301da10031413078244488072200c00d0f100d40c040c20f900000c13002c507507600400070617000740d0180d5504c1d03040d070404074180c107150f0f84039442c568420000c04081070b5014481071100c0150010110304070030720707043c803610714000c1c0741000d03078441d1601d80c0c00410010318a5107581000b460211120070b0807940003e200459641508141c2c00004140284140e481e0135440703c10700520900b0542c403509290789850346000141d42003160400c0c040340501090124002d0581c00910f010318207549030003107070381d4014903c015000c200d81d51180c40b0035540386002003070f0901c8005426158110341a45646081d006 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 19791679 1250 19790429 19790443
    0x30c021c0501020315060a020a1e020607080a030b0d0b0601050d09020603090706030513020904020d05030f030903090109171f020405060c010f0b040e0d12061701091506050d02040e03040b030702 85
    0x80d044c1101c0b2820745c005810300340c0c1611542249038019086001f4039407038041c5840306071020351040300d80d0380d03421000503503c0c440502456400790301482d842e150b581034050b040b15000000c85205000d0195003400180001c100d0726803055017031070115200c1d5850624440a88040c0d50025800307507012081080072400000d03c00700701e07411360342c007407160352240c115102d28030038200300203900060311000040c05810080028002c06d4451400c580c50701da01c1c4001e00308d072500150354001803078200247d441400d6900920360030280c00341c248101d1003050103c03141a525030b4510301c01904800a0b001c103040c2041e007075055400900b4003034042c541d601542c410141c000c01c228058007480e24540041501281031a100c1d2440c5c15043c076000f00362100b50304070305464811400000c01041603c902d400306004421700891007c4150000c0089840348240c035044901040d8505a1410a4a000010060b80e5200c3d2015096a41c040c0c0300000c145004098140c10b511458200000242c03000003400462a400241c0b4 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 19792929 1250 19791679 19791691
    0x102030901060504110406200703120206070207140409050c040f09060510050306011a0c010c1e020d080a020702060705030304030908070b0301050303030402120a0f030f0207080f0307030c021c05010203 88
    0x304980b5441c1c0041108403210400c0c100c43c03a070811301003400210f00a4801c10016541c584105006400ca0301c0d504d45410030780d42084a1252181909242c4a6010428241c205581c1c0c00501034280c02e0261401e004101004100e20854540400c001800406e000c0b801c07850f400030704140310b40101000c204004d00000344045411520340400a400c0039200751948003901c01c02006010303d0391070200408451214079001c0844124100071079290820309200e8070381249699103428048894a60010900750314002c090700654015200010109503c084c01542c41080c8083c0141c0b9140940042503c43c06440700080c003d100010070b0009154101e60480d0484c5d44580c2100e09042c4c40b0800e00303106000070b2080a8040e030007800841e005260414001c00039480301c00403141c400003143c4a0a081822000096020034041c0203010440b0340e0501106011b03160903001841c40d8841207070690358a1150100c058204030b00101c4800443d601c5003090161329800d10082ca2101c0d41c1d07424a60300079807040e43c0f6 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 19794179 1250 19792929 19792931
    0xa060501020706020c0307030605040c081903080c0306090f0a060e0f0109061d1504020702041d01060f0501020c0402070515040303020a0207050f0915030f030c060609010e011a0f09040204080102030901 88
    0x40051a0384c40080d03c1e0301a00030280c080c181440c83c50741d6103005800c001d0822580341784800030104043c07a0070001042c071003131800080d817140303400c46c200600940400b400d030400c408820402c100060302c1d052a16a0040005c880040e1507071344581d804d0004080c203401c0085000c44d800c0a000e8580741154000341030314030024080101c41c1e5943c04040c0d20080d601601c0340401070b458005155280d0420340d40c0d0100d00003034009413078048180d0001b802c5580200d69002c5044860b4605052213009103d190080c12400ea40703c0d21640c00c1500107942c80c190a860140b00b903800140100800c4010700441c0740b4007034502018092400d091401a0180d0000d0304c03d01d0051060740c00002e01890b0062450601d458094a1103055480343c1ca0151489140c0f50b00b01509449140380441035514200010101d078951302002d001d0301d0038410104041c00206902800c08211480014411704203100101d00640302c0840c1465640c400d04051980107010b081d0305554000c0c0701013000a01c0000c1034001310311030303001100 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 19795429 1250 19794179 19794193
    0x3110318190b061903050d0c061506020109060501050a060203090d0807020a06081e0708010b3901060f03020f10031e06090f0e070504090309050a0b040608070503190504030509090a06050102 83
    0xc2c0740d00c944c014403028125074000382c890010b01c1e000e044903034507080c040c250124852010f56039203e41c40c0c2d9558843c0d00143c0d51901088140001da1180d240900011501d400805281c002c000b5600e0148600291048c0e009003410301c10411520300701d58115a001d0105421183d0301c081c00f4001090403910313007407140301c0130100c40c22010443d4542485105151030b0380c401c3d42d00703100c01e49003a6004000103070124122017240721890a8502c0101744650031003c400c52000995400060956419510030590240c18080602c0180c0e02e4001c010050b48055400b01e415a10707140045002c0c0c10720b4034825407000041800c4446030b81d4150040e50640b5410076041c0848844c460000040701d802079040000d40d04400c005100c0c40c500b075089844424003034501070306c5071900d500005106944d660320071300440c10b000400304400c58000c9952640803405050590031031420003402189001221850381040c4c0e92030740001d00300b5025005035513000308042c02e00304c00743c0380042901d8000d01890003040d000d031107011 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 19796679 1250 19795429 19795459
    0x303020c1203060109060503040f0606080c04060b130501030902063702160501030e10110a0908030703050f0913020d06060207050d020a030b060d02180f0703110318190b06 75
    0x20032240103c4060356a89101850581d0480c1c0326000904101c60035034408003000b0100e50540541c1c40601900e8019000d0300051404000440c1c0c01c69022a40f09101403140300080c02e1290b1020307084610a09000c681d942e610300c0060744601c00c0040c440020114220b061000c0d001c104c0c58200c2c15a000030605800d40c078140701c241c0c0d90305901300b101d18020301a410305100d0b40d4429002400000d003054116103022a2000e41ca40507a10100b034481c04100000c00c4008580f40c0c041e000c40000d0a0f180055480c040d800e07100106184541f014240d100380e40003e001d02c054aa0501c1004140101c032001c64441041d440200b018114070710805006220b001004103a42c134059105200096004100c08401455a952103180b03880007040780c1d40c40244040c00b40003588400728081e00c40c2008250380703203d40c41c12030302c80c0313102000241c14801050715002001d0302c210350f05001c681d0001802d4003800400b850461450b45401e69a007520030091044200300d80c2042000515a800713644125035244a151405d = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 19797929 1250 19796679 19796713
    0x901090b0c0106030c09060e04030311041a031b13090218130f060503010e0a0f020301060803040f0627030b0907030602040906050310020304050309010c03020309030303040305090102190201120c1b0303020c 90
    0x1a00480c60721071007101c00312740040d0181d44203900b040200c0740d0749818695101074190318100c84001c00c50514400104210000301ea03614654050300380d201030075040c048008241030448034640500018154005940031000707407101040e40c55024001c146250450021030803802808000c498030311150b081010202e0945410f0040841800e580c0008200b0010240c940c15041400303010280d8140d581c1e4140400d841009200800c00350094942c03a08200d450620002d203409007221a013000c10f00c01501c0b20481c0078001051400b20b94102c51000131507190107031658140185039200606a41c4000340000e050b1540f5006135080341e80450584480960701070b00300007a80700444000380103420820656007190300031505d100099000b0f1045901b44103401d00030900d035500548054011800100c2c0500403036a04100807003424202c070359003003403034810b581c0080d1540c19036091160b54191210100c0d03a40340e00c030b11070844c284d980303801c6885400d200707504000d07000b0b61084800314098000e0001e500307800d040c0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 19799179 1250 19797929 19797941
    0x100603020414041106070c030206030702060712050408090603070e0405150f03010501050f15041203030515010f0f03050901020904060f0e0606040e040602030c07020402070b1503120409020901090b0c0106030c09 92
    0x130a501d02d00000d9075104010f150303071010030b00302c1d81000c1844000c800f60700c07503c015521900c0b10790002c1c8600e0800440c06822200300c004c0318141755090504010004c0c090105403007100d40b06032099610f035103c100c400d4403c0300c200ca00c00c80d04a4030344820000c480004c1103041e81d901d8021f880d20f6810500100500d0f09a0344240102c40d0040701c0407a0030181b0341001c806031a00d80744803000c0c40782080c1e101c581e03100151148560640c002520782041c0100c1604030410300d030248409090072003001e280c0800c0903201a4000c0719040c18540d5810016a10b00000e404460301004020810400a629144040019400d070f0283d2030304000307010b000400d241000812a000e448501c0070340c43d490358942c0c1d01c0c203010350320041c015158007500340031110050b00c0b03038000740c41001e1151011804614120300d505d001003524800781d605c680c2c080e1200d501c96070f03100404c0300d007a80c2401d00e0140e5900034050050b20352603800c0d4820b03d40301200180455050906600c240c0079603200307e1140c9015984c905130301c01a126 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 19800429 1250 19799179 19799183
    0x30c02151302010201020702090703020d0506040203010302090403030506040b0a09092d060203130b090307060509030f07110d08070b070e01020304050a1e0308030c0403020f03010e0d080702070810060302041404 92
    0x1440c08042290303004099280d01001c0d105200251801c00c0d607501013420b83e00b0554244000c641c01069461140310070380103855105c40c0c1130318118219855034000446658010f04040c0905a1b504003003260f40d211a044403020070006088500d44569661620000340100c4000740d400d0030003c1e5070701c1d000303c00210303078039030181080c00851030140040c0d25a100258005007910300c02c81100790a281c0000d0032000440e1181c82036002658070b800c1d05042ca241a41c100030195200c0b41c104215038003080c5460b40644d4002a00504ea601c840a005000f1615800c0e0302d0034041e09282d4046043c1007006030b0341810034807032142d07591003010886444d001a44d40e40100d003c1ca80d4001c21100b02403140540c0007000c02c8110703071180442d02075642d803600e0704078481d44151b44500c210140041c041c415400c0041c841884a4001d038000c00c010500e068240703442d501002514020490300700007003003070a482005408090b20018060b6112520405d00d040020403d07440100e0245040400354a003000c007400301c4038455a = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 19801679 1250 19800429 19800463
    0xd0b1305072601180212070f090c030e01050103030816020106050402070b06010f0503061807050d09050c0102150609070c020315100f0e1b03060607050102040306020301030605090f070302040203181c030c02 90
    0x41e13400c1d420050000b002060340c284a2040040000d4084021001c410007001c400000007054000f400004040d42d640511400aa0303060400420020b07030310030000c5074029000c0b141c86d14a5036001008130302400e81a48080d44c41070010500d0001d004032404401c1c0145401d0720b41d01d0010901d074a00342c4407800111138860307200421403200329190115800c101d0348495a8074119150158001483c2c0840c1c07a040c0c0140c2d0b40d5849202150305550301000b107480c0c4204401303403010080c64490002015040000d00c4a800c00800c03111607030454508001921002070040c20783c881c80d140c000c0100107000c403540300340180d910740e041d000600f14503048402400f4800520500c50b01002e081480410780c0e102400c1160030000401446010400c20300c080c1001c0e500c00c0e60050382d603500d54140602903035009001032803943c1005c0ca82c043d0020000445e03804895050710003507100d66840164041c5132012a5088440d8001c41080c3c6036503144040c6c150352050040e407020411104400000c90342c4003041000b80d41d902c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 19802929 1250 19801679 19801721
    0x80403081603060302030a0311100605030a02040e07030b01030b06090f07020a02010c110d38010e0a02160b0901110301050f0603130501020a120606030b0d0b1305072601 74
    0x45458a80751007071445541030128401e503407580400c1c900441c0d91015030014804400c68a0128401c2c422400c0100c010387c000c0c0722550070a400203440c0c1906450082c0b0455468100d007091000034000c000045400004450180d0b80da4148000c0200003103841510950b4000c00040d000c00301050034902460301a401064060103a6005480a140f80e030001d0f50310b052089000d2485a0300e17030500c0a0080d1103003081d44c0c620300c2d548104015001140d400400320b2003020091a24058403000040c0c1112681d415401c0c103034551105040007440380c050071503400c41c0b043e030f1100c040c000890b0185010303000c11002000107030b1314403d0030803050100780501d5600078118090742840b407804c03002840d0400c0e035080c00000c03904aa60b490508a92110500307502003200400e007614203150501c1000000c00305401d0070304c03041418000060180f034007540010200700390380d804284052401d00c0c05d40c0419074000215044a03460b0701c00740215603440002561186c0c099641107040c440180905121500092104c83f41 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 19804179 1250 19802929 19802941
    0x40f0803060102150a020408120307020a170906130302010813080a0c0302030903010903030c0801090903020c010809151005041a0d0803040203150c0a09140312090d080f090a0608040308 81
    0x555840500042d045215611100000340d40001d4180e024081c4000010b9490b0b00d021620ba050218942c00c40140500c18801c2041c6260080b55110f08207500c0288500d00222220620005d030050002e80d60f0440d4003ca8101448001c003445038050b64001d0301e9003010b0b036071800032604c0401441c100042001c0c105118052206000e500d034252114440e0055900740701c41c80010038212106d91505030002030329905c00c451140c1d0080402ca014240c40b14040c03200d41c01986002e55034108a81020b41008a0072001803180307103060010141d040f402005044d4a41402101054043e07805e01070f052245180250005182c0b03202940c04407519400f0300507040485090f2503080301a04010010384c0c25003d204c40e1805c021807030282d0f880c802c040000820352500d01d220300050504800f600102d481c081c1c001103c590580d00050700d85254945580500c2d9101d03054004070304500034001c2c0007000850007058030402e170b08101c4050070640f0340c19188240c04a55070f00007181c80090548010b00422000c50110300 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 19805429 1250 19804179 19804193
    0xf010c0204110405090f1008030304050616140a02010c0914090105100306051002100f0506030604020906060418020c100c0c0b06030106050a080c0102010605030d02030904090c05100c0c060503040f 86
    0x2c104042d406429041a035504042084100100c3d0180c2c035040d0350400f0403103000d0100300c0580c0075080303640c0250300f54034160b900c00399240f002500302442c0055150410090a20940400042a101151194503003001c00c0010340a009003109000101d0142d03a0081031881071310f410040c90f600c000703044c14016403030b150030300c07260a0100c2a01004c260b281c0360041020707121070418006484941d0b0003003600c41c001841134412240180002000582008103202c042d075000250940c01c241c04640403d426200d6400151807403255030302c44110301c203c02c5010b00b00d141d40b981c06080c41c0d116500c15900c41c0c044035030030403045400540502c80820186103180d0040746261120369404400a000011110349400001d4510030403980144001d80c00145100c1895134280107910092009030010040d8840804029480340213062415008a943c0c5902c2403c2c403036554040001003101401401d80390303604e03a10080000c219468255440b81d140f8100107042c9100d03804592140740c10465111040440340c0d5660 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 19806679 1250 19805429 19805441
    0x1905030a020403060615020c011b0303050604090c09090b06060f04120f020a030b190605010503070507021807020c0114040503060109020a030f1a12120f070c03080703090906050f010c0204 82
    0x40990707003440040001100d078031a150140ca003035094840c280609501c0280f5150340303d844c081c1013015000f40a140c0317650000b036120800ea031500303011a403903403150041001485200c101508081c0c504000040217441540f2443d000c43c06240524426502c0344244a8103110300d21180c10103510030801004001400051141501e104030b503000321242d0107030001115106039030001d4400925a00070300021354840460300b0070900c0e0002041c0b03c0c0b00e04d4100081c00b0760100401100501c000011940c0443d9180c550b45001e01108501d0f420241c00c2c03009001303586080b41c0c80b20714080b4508900c000b44151030302090b2012114020000d100a030300705804400650042c050350f009040d110f08504000e080c5c01c0c0609207401000d1440002e80b6001802040402e909100c44030840350484003162170f0301c103070500c100c5981c14046005e00c0d54500c283e1400c52499102a0f00c0580040c10118110301003580c0207a80c1400c4074440d030703014000a0748030f40402000503181205640410140b01c0e80600600f000c1d0801 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 19807929 1250 19806679 19806691
    0x18010e0a08030a1701050f0a030308180a050a1e0b04080d020c0607082e0308070f08040b1921091e05030403170f03010e04020a050409030203030a0b010203190503 71
    0x152500765640d00252854000030b0002d404907880f481c8298168410121071401841c00319000c4009404020110303016420324000641000380c074200240041004480810601c40e60608888125400f401e1207500d8a494103000c43d0701240084c0030480340400500e00001c0c5a801045100f02601c1c1ea035280031080d8000b03001428016024000d1009040302401064480c80303080d290b00c4894034005046031040406184490800e6039500c0891007007003c000f54400540b50f100020715036a4055060048036a150584005c00d1408001000b1401c40c100b0750181504105800d071116501c2b0900700160380f00619410345003000c00b00e00407101c01451080c0c001d5072515000d10740410902903402c0c1e04030458121083c05603100c0d40000f404008000d8803102c12141000c0b0301706001d0811000003a00c110521041c801c59004c40324030804103007955620641c0c0001840020003c009010052802940320b81048402e160058030b044620309d0294001b00803200c00502800c5003000112200d281030321903803c00352007 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 19809179 1250 19807929 19807939
    0x2060d05041b080d080127020702040209060c031305040b0f010509040608010507050a021204050108061005040b030a051503070b0901120905060403021e031603030b01020102071a07020d0518010e 85
    0x30507041c2c020416500a082c0e0100640710560000300060546001a03000540e0b0035503034110484483c0303d07039240d0b184242da65800035948505034000280603011390190603520000000391052b1008ac00401444c690560141480045550300e003000200c3c0c03001c1015940040000c45101e00661042006200703001c1c0040c0001929501c4003650f50031280700302c600c480480c40020340c001c906074040084107410bc2d0500700e49850181060f00092000801a2030b041c02564800c2940407041d02a00948010b0014860819200c3c80c101840304003808055600100300a800600090503080204525050b01c0c40d41154034640300080b001120940d8040c007044070f0007580c6044480024006101c00b50046000768020501410109000c2d02c581e85c4102e00051a50710070440c4017100b01e88d16030301c941001d401d0b00340080c443d0003171801070f800f910800fa40181702014070010040005052800310740902425401c0355072035800c40b4026034061103008410401003d5001c0880401d40c45140000052400a05 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 19810429 1250 19809179 19809203
    0xd02090612010603020a02160305070e06010507060513020a0603050708040209090109020405090a060b22090606120c06020105150105070f0201020106030f03050d050f01030b04111504180f050402060d0504 89
    0x201c40784400c00c00e0b041075001a80001c1c482d0500c41e41000b40c241036401c0c60f860706542d28030b0b43d036955a5601440c4601c4d0215403500740060990781c002d40990f0803145d0080424041071421340b4202c12003402c1100c0892180c0014540454501d20910a440c0300e0b0300c10303448404890f101e54081111103074000302004215034a503844440143c37610f010303c07801101150014000100c5c245010303415262843c503440c2c011004440c8212044059600f503250a031201d4070000b40f914080c1c10908080e04190300708240000001c243e50080108a04c1410200d80b5198000c0105440b4501408a501c40d00241d00b40098801d11424010543c2d00e10401c00e518414000040d03002c2d03503540c1e402c20700c81c80b55800360085103000c911070951401c98022144d1001c01d501340c00d20700358110707076811061005c003610280c80ba802c0000050543d4682d424043c14517000080600e032143d50f59881e109a6540c03041c825180305013840035044c0e0b018040d018503030186900801441c1844a1410140010f0800070826241110500c0b = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 19811679 1250 19810429 19810447
    0xb16021c0309050a08010c02031209010207021f03060f0f03031103130608040b0702061b0a020a0c08070f0503030307050406050f070602070605041101210b0612010e011a0c030d020906 80
    0x38108881a0300c01d80311114582c1c54002004449512544820752590500c0a414001d0354040102d682c1c103811040d500d05140c94030ba41681c02030207103007030094100301e440102201310a203c81117807255a0b000d64051220036281c000c1120f070301c0315034821405080040311003400001d0150903034a501014580031203080044040310300c486140180c1c443d0010400240500091110608620b90302c100c050008100034140003110807811555082c40541c000d1022600f50f03c0d0038400e000c0103041d0360300181c800d045542c4400b003603500d603690351055074200e0720b41801c00282400e0200039203114444a4507809d09091400c40c040e91254002c14440c01110782c20404000040d40c0c074405032001d01e000e91340000d030174070f040d10705030740d10540e19118507040c00840f1002d20000803400507031144040c01d5135030100b80843c114000c59940e0082000400b00204030302c0003c28a0400101c80c98122800f0460501101074413110040e5548503800040603a030300100005541886103070005d10f540c101c0540601e103050181c03 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 19812929 1250 19811679 19811719
    0x807021908060c0d0e120714060702100f020705070b0a230304020402071403030901090b09010b09180703020301110705150709210203030c010b091e01030b0901091203060f0905010b1602 81
    0x90014030284010205454048c481c883c1e45c40114044005c00500c950304044401a42e41c0c80e0304150b03801e00310b480310300c50340035002e058041d0f0702410b90150482d00e540d510303421412440e40025040d5800901e040101440742202c40c11010343c0390300d10a284a00e95211034080c000a544042010b680810707403e0742c5811840010001148914148400041c0c0c0c0252850100251070010f0082041681440640302d0240e0707980841c00e800c4410404001e805919051000d0b052000315030019506501e840c1c01c03600c40d4400748000300100e80c801c1701600d080c100b03e9282401140ca05884107000580100c5e0140b2680350025150520640818145c0c9080c9000741d0001e459940116005100e694440200c000d41307090046480d03812801070b0000c0e2980d42c4801c0c00b408441d000500c80a81052a039002060074102c0a5021094154103c01c0140c0320201a210181c00790a03584102e003910100f44800207142e0b1594820360f4140c0f101c0c002114a4404040d08112040d100548182e034800d84070300c00d6519071000 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 19814179 1250 19812929 19812943
    0xa0f06020a02160b0d11030603030307030f110a05040305070b070b0708060a0f0b120a0c0c0206090a0b04030506090c010e010e010309020a151101061a0304032105040807021908060c0d0e 81
    0x10a03509140c2e00c0340300c900588207480000086c095907000502c2403015036a00442540c2d4086e00a10b0b001403174803c60f500b20006012445c559030210300300080c481407115071000061080d02d0040048034401503035001480c40074444c48401601d52451300c00031030344182c4900002e980081004142e107031666182d07400081d00c0d892507030203600040d0000511611401d001012a944110220010005407201c030300e000d008140c503040002c0c4200c100180305441541e501d06040050111181c92503161602e03407070856968901138507202c9441c0b0950350074200640c8501c80b040b4a09106a544c007000c3c1e030f1880c0054014210920049070f10a03e4041e011520681205185c0c1074025296120b40e40600c18103055400c4410b19040b0035262810304080741d08031180401102d4105070306180026890f0300c0c85006241d2000d2151034180134a003800140b10901c40c03443d019241041c000c4ae001040c1c102c290401c808600064820010799400c03810025800c1061a805440c1c1200c2c0540c000c54804288400c490400780 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 19815429 1250 19814179 19814189
    0xf0702030318120c0a09020c0f191a070e04020703120510050103060807030c030308090f030c10050105010c050d0302030601030e01020c070602060603070b040e1015031a030a0f06020a0216 82
    0x8031102414280750040c0c00041d50f5207140060002d0070550342c04071748554034034020301036965000200b00e4500201085059490b60040d000d84408140f9418500729641d5a220700340c900290b501944d8281c50323140803a8a0203003a040e220500102005011300010390407104040d401d0145c00c801e6404119220b000d518442c04084404008403401c100014089602503007101e03450b40d0111005000003155156005c058a805050030300d05982c5600d82c4600c1c00c01464841d005500011a05810020000640c25a0405440d1040c03006a0f02c1e0001110034500c100c8000d03049902c00411140d41500036401907404c0074041c500450f0240042c80b4140c26680a165a502640d004010401039254144800c40d0408012405002080c1c608400004140128010104182804400b185043c1c4407907110a00a1000c404525400c149910000d070042010101d02d09120b0000b80c0c494900307180100d040c60a856006801d840342d480340c0d850740b10080d0890720f01d520951084400c40301c9150390011006000b04 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 19816679 1250 19815429 19815457
    0x6040b0402030708030a021203060a08100c021e0c1003020412080706061a0d05100e0f161103040306110403081903140103020f010c020102151501030b0a0f0303050f07020303 76
    0x1041901c149490040c840d4401315154006000e00610781750f0101d900d1514610f42c0301b100e6240e486150006414007055030164034180b1512411007071004954200c4009003190f030302555900c00c4654a5266082d4a16007040d0b1507422001c0380041c9494010040a030003911443c0060070692503607030001c481890070609030b402c14008640070701006018001c020141074002010f01c00c0342921310745010f29010f03120140b00c496890b00c002a04c2a41ca0112810041000d49200841401d01c030346008039101c0162074805c3c0c001d80703410341d41c80c005020f0b814030000c21403200300462030107165071942c01c02010441c2c481200d0140401000000c20000380203829545042c400f800200030310444040e0440c0e5024524000c0d11600200410140e07880600000c4110400c0c00d00c4913000d002440101d00742045900500003248484040c4070944007600d00050f4041d03002c1e20104030b42001030081161001041c882c3c000f4961031801b085c000a403051010301800300d09807204c0c5060003c01e90019086402c02c5074400000d07 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 19817929 1250 19816679 19816681
    0xc03060f0909030503160c0b070503090f0a020102100e07090213060906031505061c0f0b0120071a0c0102040305033604021b010501080c0103110f0315010c0506040b 72
    0x40d0240188040090501e03000801c040e0140d581c1c0035046000042140342d0407404080000004c5018106000c002c940c0910903022620300614050066041503c450741c05101d81c1c0800117002e5000641c603020703960160000d00c03005600e04211000341c03410205051150040110006a082d03040c0041d0801201d421403409803070303082650040480f400b545c441800c00d418100310700c0100030010703140310030b81d0350603622141c1d00d0940d0702440302400100c814140d031640c60944100f604e160031303034401143c01c0001d0780e079038082e5017500c040100c4911010b00e0310060b540215500304001004401f401050340e03401c5858604000c10190343e07608a03000b6078020b949a4000144588998502c20304410880e86003d5641448210b04408400c07001007540da55401254001020780400b0480383c00c2020700407001c3d00a100d55038484a40030b44400c182080240420f040010482164060318181e424840790768010314190703600d1aa21310044500d00104605205207100f031030020500a10045102d00d0080000c00c00c5 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 19819179 1250 19817929 19817939
    0xd02090f040303050f010311040c030209060c0a0501060911040e040f080307020c040506010c151a030307031d0103050103021008060105130801090c06051c020f12040b04031101050708010e040606090c0306 89
    0x44c4c6800502e40d043c4000e2810042c8001141d50448031801081a1000502c00351261000d400034800c3c0030507160310140105018140b00e07000224861941d00c108000d0084a6480c40700f00162200080d01c0050007005200034401170010a8249a00c2030003103c00d11140c6e0003588901c42031b0b5206841130350058001d4000100103050a019040e0841e03001c2ca4000990b403060f0b04c0e003500782071418411121441d11090002038695280250754031400008041d642da5807840e150140410001c0740280203002078007000c0c00c00c80e44c000d102e040d040302e4014042c2c20341c3da8031070f50f01212000c0c4000e2015050107400d200302c80040e0342c079000040c060701a01c0e00010388816241460360064050381d001c14200034080010700211041c001000010b46c01100c00540c07a054581d52800c058001d41c0e12004084c8c85003c01c100034822005040c50041e802520389544000d48101103a007600c104443d0342020805900c010800310305141d05056004c2c2c00345800081071601e0b811260180c07843d12841100081c0c5600c03007071003 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 19820429 1250 19819179 19819181
    0x3010603060b0a140a0e150a08011a030103120309080403030f020c04062603040314070e010803030f040b0402120106030b01060306060806030705040e0f100f0c0503240d02090f040303 80
    0xe0201402200d05040c070300100180700f000c071134682c840d0101d0042010200f8502800700717900e0002009068285e00c203441e075800c44564219109074000168004000941d900100090740c15902e844948986160700755203411461041744442c581c10103994900076000b141010b00584091032003070783c4814800e40c0c074030320003442c00346000d0400b03206510b0080100030350b140381045100c0c002103501220822103500c0d0714850550041d940054010004d0f0034a080d060400411000c044e1141c103000d200b03160b600e42c885150f582c04215003903240f542074480460301084060b10380d154424401041151055081b4030342c1820b4030490b5008071003201040005000c5140c150140c0c0b03026203100e00d45a003580c5031642c0000e9894000340300e41405650361700c00042030440244485a107801d000d10480c0c00c400c6541a052000f406003920b81c1000c9440c00800400443c82401201d000300b410060340788000c20141d81c486c02414004041d254800042050000162622400c140c4078981d02440c00e42d0625003800e000d0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 19821679 1250 19820429 19820441
    0x13060305010806060108040b060303040506191806080112020a03021906110115030f170a0206010305010b040e0c130f09110907080c0a0f050d0e010e010609060b040b03090a080c0303010603 82
    0x2003d4005008001659a018050320f900c40e4000f64091516107071240801e095100301d0b007055402190000e9050401e41c1800d01c12058030089549200705c41c1070301c2d107090080384243d00451000841000040001c5038072103640c0b001050005115484d125a203a0025983c1840c090301c400480d5441c61003040b54940100c6504d14000d1030400074050600c6084554030f10b0241c50000030411400342d41034074140800c4506211004803182451b9070354404185010b96100803d11003122a5801e1036000c0c01203003082e0054003038600c101c00040c00c1c0840b041d402c02140e107501e0035200d81e40c2940e480c543c82c101d041030302400c80950300682428050001303031070500c80118001803207002840440c3d0144071441c1e0b08030f01211940b4500345001e0082c54100401282c1901c00d01c8048240c140c01e20300e14445444042d84081184d4201900801044e13684000302c40a0b21120310500007910b00c01e1104004641600000755440302d83e68050380e880d496182c0d03514640341c0001c0c42140aa038030100040c441581c0501c203503 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 19822929 1250 19821679 19821689
    0x10e071a04030311010b03061003050601081605040c170a0605090a0209030a1b0e070809010e06060a05100207030204090b06030f010203090a06020a0e09040803090d0804020d020f010507081306030501 87
    0x566009045540032685030300c541e00c4000c04200803403d00e00c0e1010400c0d8040ba043d4031b0002c0544190742080710392009448081d00040d0f9907401010000a182400002c400341d900b541c0d248540041c134a440f0070800104035541e840010300a056100c0c02c400e000c110b034440d205011030180050b07460308003030601142883c01080c136800c152040204270187c1e50b00103130100c00560700403120b80c84400007642d07a040003121980300312044c7d12107400b03201e001608501414411070181000b00b0001c280300b070810381c0c0da0b102070300c00c1a0008529031007400142041550b2100f12140c07801143e029990781c0d80842c00700e80303248005079289004001440158513040c810503c0300880f0318000c1d0b00f1810054016500c0b041c240780000e203a40e900041c2d030790788140102c20003000c00304003c04004da1072400341049041031f40701b15002d02944c01034880075034485008945260213190003601440c000e045590030300c0b80b00800123440c00d060000900440001500c0c00b402402048004510504a646401800380c2950780607002 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 19824179 1250 19822929 19822949
    0xc020d030305190b0a0306050403090e0907050915010c0305090a170c0a050105030403050d0504060b030102030f04120c050606060f090604030f020f060301030b06090c0417010603020a050d030507031d040e010e07 92
    0x200017a940c10000ca0256500181d0018041e11640780c15500d1412546c4460313000c500302401c1003142200421240b045500c01d55802940350755007400c4000304d8003603243d005d000c96160780320003010030b2240780a44205d0308090081004540c980c00b00c0b241550401003501800c1d44180380303c0c200360602c0a100c0c0d00034802800e00500310701702980d014019001c0d84100700f64040e07071840000c081c050190001a146040603000310b640e800c01e04403500495030308440503682409a4280d08403ca44689090802160014090310581e101c220401405610284030241d0024083c4080e00403961141e00910046105601c03440d81440f05c2d1040c000d611040740c800510036201032004101117948a000c445e800182150250050369885c4010300d180e0055030003903002d401000b034000e0442d480560118060f203008a4843c0c440070f03550070802080044208005001580503c45a00000e01551090840f800544005001802c000c00810700300c1d1a225050012030703440d400f803c0504074060025801824105078 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 19825429 1250 19824179 19824191
    0x20c0f1c0501020d0e1b03070e070503090a080301030308070806090606040e04140d050408070f0b030402060703020f010606030204170109050c0d1113060306050a1a10020106030c090b011d0109060804030c020d03030519 95
    0x403031289131034000d1890092050010008202c51018000700300421780c0403914a480b5612400c005222800450701840422045b10100d4021b01e040800a4410070000304082d01c0c00307003480d507009103030503020b8011101c0400101e42d85200410a00049508100b1582c0d11601d483c648003006107007000315880613000030640001401018891300c122a4025010742e551642c500f19803804901d80030010507940f869500e00b030008111107605800820881f031032140500720740d4007100760042c02c80358040e00041c00ca41c0204814812030038010502c0c0d400030300400501581440030800715415180c0300301c4803101c1d1561130006001300300880c461950040b03280e59007004001da201032a80901c500e545003491180d000e1810782e01840b8405d42249000c1c0d54000c0711606400c0e501e1000c14003424100c203004e400705030f85d44035550505000c0c0030000030704c460595442c040c00307180010640b02da0350043c105030200a40c090440015841e400f21100f00c0610907034000400345012400f10154600d07403582d40341c01e94208a = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 19826679 1250 19825429 19825439
    0x1061d0a0902010c11030f0d0207080d0302030105030d0c15020703021006120209010303031d030d060f0e131b120b0402090c0913020307051e0703020c0f1c0501020d0e1b0307 76
    0x900c0302d2031440d40030005542617030391200002d107040c00400104000e44102040303c3c000f564041401c608580040d0704448000ca081d8a040e000d034002401b0700798059010f1403a00324083e00c1a1404030442c2d00640707141c4c0b080c5900e0755020060b13910001064015074807107500001265401c5c404c00c0c008040c2c10112250180050b40001c866a0041c803003d0101522000402401c588442001b6800c1c1e140b20300b01c2c1d40d513500381d080700d01c0548082d1040244100528100283c015001226180310b00c000030144011403a1959035040c2c05480e06620189640c020100429078901003144600c0550007040d0078441442c192041051300e400003000001e00713100901655a072a00c942c483c0401800413100c01580720758803203c046403580031300c081803400b0004140e803c0e01e00c0b110f5500184402c60017542a80c0000e600141404440c5032100c1e8503e400900003c0e105803010200400446410b2181001600c0d10307401d444804251348200ca680c2c00e20390003420f148803460022801c50406080c064001e0325500f440c03c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 19827929 1250 19826679 19826687
    0x81f060804020f0a0f06020a02040f0b03030d090807020604060e040c02030f0a0c05010902030a03170105010507171804020f0406020c03010507021504030207031a06030d090e060d020109030501061d0a090201 90
    0x1c1c1c0001e005000800902d20301340e07035566909003e07042c0c420fa04126107a94680095481ea02084241d0195250041d10741c0f0318503003070280e40c0320f50201500a42c070b4031139610f184000400c400e841c141c0b0140c03c00e000780001a612440144020065551902c0d58009080c040104541d1543c0c03080003954801c108080422a03c40182c40ba0042d041c01d22182089150928501600e00600025814018240004205504142c0c090900359428840400e580c2e2174200541c0e00740710f68807000d0000c0c2c60111070503401208a0000307004402c1030400124100002c100030070700781d03084610861a10700c0b01040902065504014105901c44218001d11003410304103006503d49214400c8803111040400008003413600821000005560208400c002e0411400e103803143d03540d0944074580302c0d003d40c0200700c6480d807040400c2c0d008c0e0381c0340411510703c0e42c0310202044112640150101c0c10300510704000030200d482803050b1001400001e0003658082202d140f14100e42e14014014903400c1e20b403500200241c0d0340 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 19829179 1250 19827929 19827931
    0x6120501030c0605070503040e011d090d0c1502090307030507140303030c0405040c0c0512040f0605031e090a050109050705100512010504021c0504121824030603080a081f0608 77
    0x50790900c00c0c1d0b502040d05065087d8030943d04a0070000e10400000182400d206080781c0340c0310b03500d50310300c1c04644500d0744090310b60000600440004031145030b0b80000c10041d07800300cc0b50b00c1103284d0061809020344082130510600d40e0003510542c00c03401080200c902c0b11a07684d0303040030085000d03519502d00102e40c941140218084c0030300070341d516155461028052011841025088805c40b0b40f100340c00108104140c0c044d00881c5042058072400085850281094900983c40039030007120300204400342ca41500c0000300001c1c800d104240340c1501082081c1328451001d03014a0103003003090b0400e814420b403080c1c03c003c004204007040000c0340e00c0c0400340d84d40d141591012030300542d075102d0000480e03400440c03941c4d18101707061608040c04200100304911114003403140e02c642c408119070810381c0c040090f682c810343c024000c100385a969058518408038000c0c2d00f403420000740c0c0948030380f1107100941044024001080a2006001510b14622824502d402c20084903500c034070b007001001411008 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 19830429 1250 19829179 19829189
    0xc030c05190309080d020301030618080a270602030408070503030a0c0f05011e0209031002090d020d1b0602070801150b070b04030915020c091e040b07031401090606120501030c 77
    0x701c0c400010207109400515050390459460b0ba21903034540e4607640290300a1100301c60003403620ba10009403020000d098448241c01ca6007103400c0c80803128040d2240314409624080b1441100d9000c0748107550701c105240a0601940115203640c1403040480c58082070340c000070720a0307100303001030340d48a60722a904007081584041c100700b1449151500c5405000440300c00f04410211600d8034514245a40c05420000d80481c00c0f14041c0d400e82c40041d0803880f40401c3c46812603602040071b40542014026075900c54442d0002901c0c6218008265140c4c4015412140051300144000c02c0030340001d0088002c240100d10505110900d0101452a80d00c0768600c001d0010070030100150901d070042008800918039640c0d403021406030018020744031000034a00a2280701c070300c00840d80541412043c840d0b500000d1030340012545030350700d40784c06010004045108058440b005000f5086000c01c500d0700038000100080f6a160826401074583ca500d541180e00d0940781c58010004240620400c4003224 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 19831679 1250 19830429 19830457
    0x40606020309032103180f011107110406030c05040207030c020306040c030221100e0102090406090b0310060b07032f0a0b0105061e0306040b0603042a030314130905040507090c030c05 80
    0x2007006c4a042184821800401e5460b064042c1b2001d240d40c40103028441c071604549503000c21001c104170450706d56000103410b4448494051102e400e2650003440384a002e030904403115181640001d06d0100c084404650010003030104004505004440300c980e00036022440d482d4188259050380c0e00c805030f01010f080603440c0c003a21081c14000b903040300e1404c90b01400600080b0740f55000704024082d007550150003446215410703aa6005540718034410f80c0d1500080a2900d04540c80441345804900c002444802c0c154031a0b44008414070311000c180040c2e00083c089910460410b1402280140d0005000b844104420726100c240e040090b11182d00b4942143d03183d80700c50001c6030040466003609900014004244800e10195032480b004440c1508100616201d0440c080782d54204103100040110b8218042c5100d0820310310013800c1c010900400075a41c0560750055401940c106540503503160308420070621a10415010351100da161900f414070441c032031030400038024420841307a480c0030 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 19832929 1250 19831679 19831711
    0x50f040302032d1603110f0c040b0f0a090c030606050702100804080c0a0506090105090313060c03180b0913051605070807051615030501030803040305030402040605040606020309032103 81
    0x40003410703c0341e02210901c01c6904c0c1c440d44c140100d04d84049100e482035003c6403100c8540c1d003d140000510514100d45031000e0800080c091003404050001000b031035a00c150b170004005c11a880da00e40080007040510008075108070319100190440e04d20303410010030054100079010260f1640d2000e5441c221491402c412503684500b0228440d00850300407110500030800844207101e00000c006024071389940003000b950b2590740006560f0b1041204072010000b46030700c10006140600b04114846001e0308004000c035404450f00004541e150f04004420f0300d000c80e90f83e00c142403154684030a07000d46041040103080500c5800101050030300e50500700f08000500400b040a0001503492040d88001107440515111480300e080030780600800c1101c0054000909000340309005503812690014400ea185032103e807002c40b044e0348010016600300e0340310040026140c84d035204400080809501640e100c031a918109030a0000d15101c00c40e612041030380d0101001c05610840390000d0408072203c00c2 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 19834179 1250 19832929 19832977
    0x1a06041203030605040c0203070302011a10050c120d02041e0506030c0d0207080c07031401060f0e0402010507051002090f030c100e0d060912030e1603030f0504050a031104050f04030203 81
    0xa40f0041d08100c0d0030600340780c0c42034643d0f40c0000150008521a800a21001c0d65498100310101c80c05040560300c031008441040103907028000400d8a42e4608003a0b48040b807030110020595440300d03504182d2503600007400c110040380081d9030845100e80d45e000c141000d2030600003a80901028100680f0b04c071000a03150800b441c035134100e0b1105644040d0380c40c8c03604600007006031241c078544800d4844080d10400343e0141501803280500f950014001000800c0c18100d041034205d5004104906200c400c1001f5800704008201608640c44008005a91518440d091000c52010084d00074002c0d031080c1d5000c000e41e074500001d040c106040d490400c045c000728000280d240d001d40d02c80135103001c0c5080c1540c418041051240c504502e402c0d101403081c1c9240c1d82d0401d584120320a101d1010440d840003e0000900c1507007942c04004062404030b00301a01e420000340c02c10040e0380125020103000202032240d040501038145e011090342604078942c41c3c04d8502a417a0320508030b03c03456210308000c40000d = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 19835429 1250 19834179 19834181
    0x5100b03101208030601030e120301090c0512160207060201060b07080a05090a0902041e06020604030e120106140a0905270703060606020606040524090c0408010207030c061a0604120303 81
    0x1051000d4800b4503407112401e006401d40c2c000e540640c00a801c080900e12220300015581c0c10030030400c1c41031891350303103041d15460042c00180800c0c03041290401c202c008142102d0302c140d01070348806414140c640d40300039010b46420032300da001c007055904011741040b1024041c0141c84004c1e401c41c1020b55240c0c14414222031a00c5101a6140d22095545c0b01150122031a8060301c107844030102c109200d0304481e011005511110700c52400142e01c04000240061301c05d00800c40340c0d0802620340032480055000f00307425507185420a01b00085400000741c060b1800c6c0c44061700078094071a0030809420030280d031504e072a03e0030b200c9a542c00b464401140d078210303003008000001c541242003082100d0722050001d498910598680e4412401c120107d00c80c1301e0040152102486c00500340311440d00102d05020b82c0c030342d0043c026449154140030000b121072080c0014003c50748030b84d4a4102001e0b00346807140460764803114490441b0411040303900d09071a41c1080f182501c40000b031041d809512890210 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 19836679 1250 19835429 19835461
    0x204080706090f0905040803010605070f08030a1406120d0503040c0e2e05010905040902120a0302070315110304080c1f0e0f120306010e010219030503010311030105100b03 75
    0x11665100398440000c030740303070701c101e0050076100a0040c000485503101c400390280d50041c1c5010b0304560301007004004060141c1d0007060254441d030059110000c10392036142e40c60300100d814031510380c0c07525104103480c1c1443c0c4c20182c0c8600210303240442d404402d03400079074030303003000240f001403120000c0840d06000c07a0580d01001002e1803188010907103081180e419210800511840c1140da00050340c0800800180090b000d03900180d540c41480d03458801008003400706c40c88207a070407075907600b11134010040a01441c04500e000780c008007119841c40c0341c05400c0380c50107107060603c6441c1c903201c0308a5681200403240c205400192035501c03034081d000c00070306101500c10404648807400340c0d0818000c1050b0410704105140e0800c0d2135a280072806143e849034035409400c40140010000030b6002e40c00b4000f01c0b14412410b20445000041e88140404442c1c940e18094004c644080010001c0100d06110004614401c0d002445142411000c5a404803000c0c01a4600d0400200000f0760a1f0701c003401d08 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 19837929 1250 19836679 19836689
    0x2011802210115050a090b03060705130306060b0301170609061302150c0705150403030801050d0503071205070b01051203030a0903021002130305010e0604080d0b0301110309010e0c010f020706030506040204 90
    0xf00070400c1c076440c4a04801c0ca1602c1500d010b0f2859010002d601e032a944a000d100e210050007500c2c803941c0380c142c2241c903580441d000395189080c44101002185180c030a60b4003074126117222a50301d5050440c4603002e510030405040703043e0300c59420420300ba800400c00d035420080380500d00c0d00800f0184000b4152051200e588200072601084032014604009040012500c09451043c030070820042401114071903800041c0109600710b0040105003000300010048500880940e81850f4444d0380f52449520400520400610081145020b10030705030105401017400721003070146081c4207030360162240001803101100c3d699841340c5000307060090080c81c0c0c20340c0d41404115694103d11000059802a6020030344466280040b000400b50b0700113161401181c01103c2c4030300f0041460182000760543c03414480d015502c60200310480d115007009540a080c0705130010480003915004680307403d0b810180c0324104401a01d5440d452a004205181520030344c0c9804203855440501090281c400c07a404 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 19839179 1250 19837929 19837931
    0x801150f031217240a06020d0c08090904080301090b06070b2707170f0105062202040803031810050105100e04060b0403060507090602031806031306060305100606020118022101 77
    0x8004800700000c3c44608061100356540f21125424004e104004a6034086c020140c0d01c900e00700f2030818000c80c840d0264500c82d0b90210b01e05944903000c00c0c0282415142282e50840100047c0320005080c0910390740080e0590b0400e0424025032200d070b1102c10040c2580d18007030303c8420b4592490850b0004950783c0c040f1241103c90303042d034645400581440c203981c19440d1380100e8808040c640010300403240a240024401d8802040c0200011201d090301780588200950800000420100905c041d500c112115503280002550151120b4200041540010780183c507003401440681d98484401c1d00c1d103c46072814101c8201da00004c10028a420340041550500100e0300108210494116910480e0180c2e80c000000c0e6450500b6a075074054680600c0a0b00f80102d01081103051000c09982d201031250448081c104480d12800200c80d0305403c2074900760407042203040d461030540147c2c801494648004c005480b0018103008041c2a0000000e10900d8040c0600101c0c22001100302006050400 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 19840429 1250 19839179 19839181
    0x30c0c02090c04060e01050c070611070e0a1d0a12031503020306010b0306120a051207060212040f0b13030801051002030f0a05070b1308030a111b01060801150f031217 73
    0x3002c600160001d00c0b07079500041c9800c01031104c5500c66400d81d009200003200030329249040c0a0140c07810403250802550500c102c0c040042c500f501000304034001c56950000045441384c1ca034040b070440c0000c0365549115841010002e0004d0300104056903800c00c05d00d07000800c0f400f03004042d00c05048650010f9414800c550010490b01c5000d0000c41c01a40c046030741b2811700c4620700c0c0c21500d03007008a402800d04d40101c03203500d07080b00c4050014404588512401480d1074081610125485810b132000d454440d180e001c40010091710b886055004051041018095000c40d94000c107284414010a4020110046a05011030080064445600324090065142c12140100421030f802a401c140d9047c4584404603a2140c03488400780e504e150054108d500c4d541e159502c800180001d50603145850004101f840350080ca0601c0c00e00400d5600000411701303134545400207094500031540d00c28008000c003020040c01140b202c81343d048a50101c440b1100c00b24810f0292126046110b10500c1801c2c0c202c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 19841679 1250 19840429 19840441
    0x207090606020309040608010603050304151e0503060301111306030f020c0106030305030a050a0c050f03040c0b040803071703070f0c240903081305031602060c0d0306060f020114010501030c0c0209 86
    0x2001038401130340c0c10388041044507982d0044609860f01c41c4005080c1d50401c00c014440038440816116003802c040c1010040c1e81c1d00c00c020141d040e20081701c80c10004001205000b0945000e0081156034002260340780c0c100412801a801e00c01d40e5032040c00c0a00d0b5480c3c91141107512203805480d600040540200140c075a0b07810050420f0303000701e540c420160719000020b050390060f4410109110580c2e40c074103041c140c0780850341384c03243d00240043e12039204406000400c802440c5c02071002e0115400515241c180910b48130400c64048072008580b02c0051040007440e40e0300c041c1002e010311552034500d100c103a0604003020f441884c08a41e13031500909694900c00b040e5242c101c00c138014840e81e11401c0541e210051281040e0303807603000401c2a04200815080000c0c01201c0c4046c00707000411107482c006a004546140c0700728204107902198a540d0b00700302054100c1c040d044900f0050000788807401c1c500d40081c150b07076414080d0905150390341d85120000b47c807500d009801290701404585603400c040d = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 19842929 1250 19841679 19841683
    0x10f020f07020112020406020a032109060b0f0102010605030307170409050106030902120a1a0601051b150105090103030504090c0306030816020420030103020f04090203030711030607080103080910020709060602 92
    0x807035001e90115561440100f61081184221000c8495940c081c0038109025502102c02c2602c45003140b510107000030031425113003514480c412086100d0240024480212130501181d200c00f94480c5040d649022800c00a5803404402c07030b000c0035809000c0902502c0d042d84103580c0c6004030f421640502c0c0c989800801c1d6643c05a001291080c000c4907001030400480c16000e40e1111591001400210321000d80d990603054001101d0700500141031540c1480789003100c00100c40c410b08521007465004920950608a032440403901502003516402c4143d8150345000c3c20741c0c840c0703114506485a81c3c0c20454642032290744180065980141880da4030b080080181d6080700300315005910032407401403007034685c9641c000d0000c210700c04900c0e1513003140c0c40e40d0204903130103942402c200c5e009901c80f11008010b0798140000d00b00c40b0301c0341d11400c0d1150752010a0500d4141c0080c80708082c46840001400800c0e8504140c03148420201c2c1d804240e012140ea0890402003039034003040d81541000740c007089103500 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 19844179 1250 19842929 19842937
    0x70812030402040609060b0a0e030c040f02040f0b03060105030c0d06050a03030c0302070e070207050108041104140f090a020a05040c09050306070504080105101a031b0a0c02041b0e01050705010f020f 87
    0x211404d0002d107468000160440320035211300300c0080d808005190820b80a591800100c11000b01a102d00c54901004038017074400800c41403030b0113a80010b00740209044440340c1c50142070030300c5002d42140b5103040040e00510024042c000c2540d00450300c04182d50760340d00300c1360103401c0c06440c00c00b07100d50320714002d0103180303040e007088016000f031700c5e804119804015441d0b0b01c108146c0e40100403461030300c0300544041c40064400d903070301ca01d01501c005032500c5500a600031101c0c9082401503034506040704250303848010b414a50325801c0b2141c4100940d40b04522202640c80464000a000300d00c95010383c1c26801e25407109405010b0f21040102c155042009403088442c1e2200a2104d503031541c020603a00d241e14019203c2294034112008468031426019641c0f01c030110209c441c00c402100a101c4003508902445000141c0460a120460170303c0d0054100704502c0000b040410003106002134000101d002c2618100500440c1d81c006111094100e80c4626070055021507039400000071403605548 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 19845429 1250 19844179 19844183
    0xf020307020d0816050d1b050a02060709060c0803060d02030d020106090b030606150a1808060709090207170901140304050105041b06050a0c060b04020c011d0307080d05090708120304 80
    0x1400b0081030340b10307001d0030516200d00350030010b000504007003540c00e0701c1c1c0e034100c0880724614641e00c0b02603400c03112240070f20f02d43d024560740b54640c41e041d044c40028a4188018030500c2005a250010020b4035044030320f41661f2644541c8c0541c0340d60307403200401c24590b0204406545841044400a419a0190b000106403024440144600c59203d800c6c1079651b4416640c030750700b10300058555070b40c08480e0b0024014291080c0381c800c840707640240c0010300b40b801540054460b90010010f0101003900182040010302c0d02640c10f605180a030307141c61010420344403011884001c0028407507074a030f01c14100028205699254991242801d091050080200301c50441d14100901844407011415000c4030040340ca42d680c8592401030040d00c1240d46040307000007203078065290b81c02415195170b20700240940700c00000001031080d8a400e1641000500203240c8030341074000300302d58008100c000049510500601c080412039841d08026540341500503070201806005d01400c10802400700d4005501480c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 19846679 1250 19845429 19845433
    0xa0603020a05040204050607020f01031107030207060201050f090a030f0e1c0b13080304060b030309060c0309040606180506031806070503040b06040605090f0405100c050c01060b18060705070503010f02030702 91
    0x661104244003c07171086008040d44802d0611480c00149032001c210703041504189004101598404668074081c3c211407030460268000c0078091201e00c1e424450554000ca044040c48030700e08101102c591a0242d03440040e041011034190341071520301070036548025000203000342c1c129611240300040c0308000e0300000c862036400f00740401e054410b2200d010350001d400414071461604d450f542e6a00030311541030040e8040c00144a12805691000d010701100310085020351765812000c0200012160700c1d4200c4020b1100054014180410304c603200c206603441665a03d40d2038442c12800c04080d0441f028100d01c501c01c0c0740400c413000b5132010285020302e01c40c6e07601c02241d464a004010a507211401801d4220840d000003131548400b0700d8400317802c11f029000740e40741c090021902d601034803800307002d40f000704a0024903000c19210034450840100300401d68607050520302800d01c4080106041010f1240e6008500407051003802d0001c040182401402001403042e1410a80042d4008480640140c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 19847929 1250 19846679 19846699
    0x3050c0301050103020609130605060f090102010c023f070501020405090106030203060d0b1e07030b0a051503130c090f0501090e0105160810051806030601080d0e1011060a060302 78
    0x180c24140100c43c180e9a005140500300b80c903c1043c01600ba00300e0844200e030030741f180d00c00103282d02c0303000c000c00900280c5480199500b14882c000b90947e100340040c0d40456020305504228045801c0303203482d0121641c400d0f04610303205502c001881440903410b0740c4041ca0006844410030105500401c00c5980c2900c07189800e0780e80345002e800701c0c0400c642c1e0741d402007281d4040d00c0c0011180c110060b8050414031408501d40d8405119444c1d1900440e20600401d6440c100d01c1424502080100f00414003140c100355820702403803000b560b07800054400050f0f80c241c0c01c1c0340300030498407580e003c02402c032010041200301024110040038000a20950220920305800c5c406094818014240304900c036039601d400d0401d06d64011125000001c1841c01e00504844010500f41e82d0910b0782e54242030b5203603007407103035043c20300c101800c007a010391254640ea4031105078141165042484205d0001c8110f0f441c140490104000341c84c00c0c4215030f0f1811040c02244100a1420340d6a40081c1c03e403402a600030000c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 19849179 1250 19847929 19847953
    0x5070b030705040303030203040f0b0a061a0a0507110f090f0f0112050a020f120304030605040204140403090b07030c14160503071d09010204090e030a030b030c0a0302100314010f0305 80
    0x140320079100c0000040341040144046070181d00110740051250742549040350745500d03803c145034015903030030f003403c0e031201402c0101c178890408605890700c1d4182c030301e40340c10034050001e00035101c0d40d00c000341144801c1040311440e0396000d001451448024008044070300d04110707520102072003107520140c050792007000411644c040c191640401c5612200500d0003c140ba002c000300c003001d8050696109541c2c141c0810315200600c090070042d44241c030702296600700f03031040200399141c0710441c80c1c40d020100108004683e008070384a040341c0035258100d41e101140c0c281241c640511041c00362075180c8603000f50011510000750389102075040301c40c1c640b50544400415072079400c18450502c41c55441300501c01160a451101500f1800c09400146895900c0012a06030f41001158030300300d07007011582c01c09440d014050380d000107500701c0142c40140d00c41c0000442c91211400064001c880084402907128045c1d801140c5803441280000169a91040c0101c0c2d020740d5070000b01c0381409000c3c80404c07 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 19850429 1250 19849179 19849199
    0x15040b03090a140c0a0b090d0204110a1704020a0302090a0b0301021303021305010803040b090d0f0308061503010e01060302221410050c030906130b0d021207080906040809010309081201030507 84
    0x2e550440103054a0a21b80f40c140d4401c400c7d0080c1d061154800000300742400140e81c1c0d4031440800d4460740321142d80350880641d02412422140030304005002481c010000141d4400301c06605595040312500002e480c0d61038400002d04100c0d1065405620000b04042c41c0c0501c1485642101c0c800c03517089000c21200c0ca405800d9030800e1141740c50690003403205025080d43d0902504000c0405018803101e140c180c1c403101945d12074114150301061545040c4216030074402651140c0d8000e581d100351547d45086250007103500c05100d140101903010401860225510b10034550450b202140100c2d4207860702c54801601100740320041c400c044946002d408180035170190b40681046802840c1011b00c0038043c0724880c1d0000e00c11103112102c41c03601203818540c440107031540b408590300c0140c0303a9102c401007a00030341d03005d05080c040c070141004014814800040c102d84c042d50107841aa2607150180c0160054644008000c12002020880e1141c003d060f00c1154100d90084044421907540d03020385030 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 19851679 1250 19850429 19850443
    0x60b0402090d02120a0b16140403050a061802030a0b090105060a030209010b0f040308030106020304030c060311030711070b070b040203010b09160507030509060a0e100f05070215040b03090a14 84
    0x10ba040b030115021400940380c40c07000c1c2000c80c401c00040d0303024404565290001d009044075070000c841c060a411401c15076000240100c05289104070501d01410341e15100d5a849003248010000754403241c401e075820100c000900c05a560190894802818a01d000c4090302000c5502200c2d03503292000096840c91b0030803824080f00e40181c004080c990038245803070aa944803030500003503100b0800001000484c8480207600800c401d60282d62964118605540003d1980d40000c00301401c240f4500440903002044036008655030038846e48010700746411605000c8264840c0c0041d034000f084036000c0c00103012200703204a01c00c070001c0100075555020095001f07025034550804020045148614500950080c00090301a0408500300342a4900090703da501844050000402d03051140400d410118650141010030307041c03c04000e00c034900000c1040c000c0d0340020b84203c1c4108080c4100210078000c441c054501c80403515541d14005028907991104224225800c0170480e01540910102049071 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 19852929 1250 19851679 19851697
    0x111c08120f060d06090203010e070611060a020f190c0c0b0901030509060c0415020a1e0501050a060b1608040305060103030305040c060903020603071d0306040302160501140d0213030f050a060b0402 86
    0x50000e00003c1e80310302000380403500c07041344c26643e2840c0b411001e210070090000184407a03035074100f1424601082030304040d00980440400f5005018804848801c075003959103105006a4200350a030840c203044862100650b009402c5c9a59007201003076400105004155510080e02d0621468980400c1c00c0d59859040b2018501510709010030321000e0142c205640141c01d0600c1122800d4409481b030181160701b104020f01402803210141040090070301034541e010b0b42c2d9040c10800d00d840c01c8a05a028441d0031002d4510f02001a0325000b00b01e440c600b0380d0b002e150420126002582c4a15004c1c00800098070161717003414621000091891062861000703481e40139000c41d0450710f4100007603c01140b800720140b41000014281c240607102040541e109a0081d402440c29404000d440401c80209410076410030910716444449069000c0454840c0d0180d0140140e40d00200c040d04140d00649400041028119000340030a00000058051070540210001c105030300d0b00d00200001ca200342000 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 19854179 1250 19852929 19852939
    0xf0a020307050609012601030201030b0102030903120a030f0f0c09051504030609080412030f03050702070605040506030405070503070b090102100207020108040605040602041d010e09030f0304111c08120f06 90
    0x6000b1820303c80e0290900c00018100359280344102000449500d418a050414814104004000750340c2e2501450300d051a0a00155107400f014002298030b0310a600c0c0b0807161800b0000d04014440d1180d8403400e01b40741e03251010052050440062405040d848001d0030000324050004101464031581301500e0304802c403e010300d800c1c40c5a80301070103010070780b40540b8a660103002c0051050820104403041074400c0d030741d602101c21600d00140440328003820160465001100622103a07400804890079620100e41858681da10f6140c00c07450100113410042d01030103228000940064414054030140d0400d030290388004400d0001380c0201d0184c400b002e400030b00701c403000c01c002c20080c1d4881900680105805441d06894084081c4200c01a61101d142d2100040040044503c042102500844100041c61402045020b81441c0d404050000380006070b4030201c060181d50303402d203c0000040c1d5030100e60885003c900b086181038010f40c09207082a816040090000c8946040240c428180100 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 19855429 1250 19854179 19854193
    0x30c0602060f071209020a080a06060906080c12010f0606021f1404030c060f05070c0605010905090a120306080712060e061603020c032106100c02010503010905130b0f01080f0a0203 79
    0x9030440c0c1c1000c4c524403a1840d1075841c2280380140c1c80300d03241c08028240380c000400208078149055012075120754070203c0308510f0320318140011203003c5448180b1a008036199070070010b100d04142d0041164818440e200f40c0b410900080458010803810380c010600d0400302e9003808441d0000301920101c44c000500501d100d070001e80002d01400007095141c0c040d40c40040c072030003d0320204003124400c0e103032080422140c0010501b008100e02515015010780f43e0284090300740f202c559035031181ca040004010045000c1c082c085244280d102000924440c000c50303048540d202c3d00301d801038004c0350381030303030043e0602c005038001d1f80002810a0150000d00312460301400c03500300882c02500442959030081c0001c11800c94107403401d59800c030081041d00c11008540c2403850400ca0014a440c0c039200a2180c00c0d081500940e8028051320f0441c0c0a0000100740c6076204507402e815a545110014400003144003803145c4800b041c88003038107a03202c200444200212341e580560f0746007032540300250305a1101b4 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 19856679 1250 19855429 19855441
    0x10c02011b06050906060a08070e0105012613060c170105011103090409110405070206011419030203100903080711070308090d0c080102180901180504030e06040807030c0602060f 78
    0x700c8050070141c800409400164595502d1a06440702680d500807181d229600780500340ca0101e500c44002c0181d04000c2c000075250007801d43c0120014450740c0e040c0036100d040040030081c40a03604459040c0c4003046105481c118451001d2200200815180f0b81c3c605000090700c2801011030114010032040c480704241c1c80c004c0119100424a990b41c00c0c14003061208000c01d4685000700d0840c1c51151840b1301c1c4c00c41d00ca03401e03c000c8800040030b40b030071035000d040100804a11040280412102915080d04138080d80510031034480b8954402505440344000b070b021300329160390000034424860740d45c00301d0b5911090412622070394815181800790b007101c40100700085100c002000035400c090a91005040349403903140c10000c02d5400000b250350000b903109480a00c059403000f5038042212210381035410f00008105241d010301707030a0510755903400410241800380c2740441e41c0200091602e41d5480d21464480c0d1200c003a031004036800f14041c40045403070740c0007240300c0d8858100030030780c5441ea0340d40c2 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 19857929 1250 19856679 19856687
    0x9010210051510170f07090902070323030a05010501090503100b041b021f09030e01080a09080d0e070b0c03030f10080105040303050609150f01030b0f0d030905010f020309010c0201 79
    0xd4400e110341c4941200302189a01c1d5404031103501400341d11007820b410702e80025070884d10002824181120040d204001505802883c0300003519030421005032181542e03d4141c50450501c0e01821112604c5207981c103020481d503004500c07d00c0c100c80c09101a0342c2e2400156104602805101d03810340242c0c01035490a40c0c1c3e94065540c901300240003051541010030390406090b1140b200030010b8000c0303034103507200103945680a0424184100200104250341d14000e080d081d11700e20b81c0741044850303404900d000c01290080010540c2000c1c1e03043c3da540b5194003c40c01044059080d00c4103005d2190005901010a4144e41c1c51516100140d455555401c818894030310004040192268100f42e02180114007480f0b443d118611070745001840d41480782c104044100020044c0f020210950b5289916880303404501c020464207080214810005000003000341d080c0070102c540000e2051480c030b0615a0017404401141c42c207807540d100000c60424100c1e00d0f8480c00030351501103009110714074015445 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 19859179 1250 19857929 19857931
    0x21b0d050705060f090909060105010509090702150108010c0909051012030203040e07030522030903030e0102031b07060e0118050d020d120c03080105030f06010e0a090218010603060b0901021005 85
    0x300e40140da040c65100c4000443c107801c40030300304001c0000400c00207014189118034941188481000305041d600d0400020121300c0f80f0412503000d4080080402c00c464002c100d0850f2484038400e0030305c007540c1c550b0b81c4907000f8010000208006800c0ea500060110042c0c8a0355028402c81141401203505200d503a250f40580900708604501c801c11000850703030030724031b41d182c014035141e64041000c2c248041c00304110007117881c1102e49401a41500400a5084600f000c22260715081c41a005201000181e065001d004241300c00e480300c20010906000000c9220800e44069031034500d2101610001141c02001c50b0500d104000c41c681010300c100c0c501074081c1d000342c031300c001e1150900d0744040e0b8030340c540b40b190740c4d40d100b000c00e42c0041d0382400c06400c00a502d025000681c000d0501000d16003d8a0b6070710810302c9080c05020094000c6003092100760424001190050326806150700c0916120110800900c01c81c000a0f07e4000045414030301c031011503100f02416402040b01c03480c41703800a401050 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 19860429 1250 19859179 19859183
    0x1f050304170f030f1006030c0e19080a0f0b150105040308090301020d02070b090c04110702090c07020301050103210302070f020f011106151509010207150309051005010302010f021b0d 80
    0xd201ca1800b565a6070020f5200d04980c0d409006642001c41402002015941121051500301941c885109a00030b400b000e07070310000c50380a80d87c400d210000d800c2c401c410350080c0722176018101505080c481803c404026240c8121144101d039503034854425044241400490700040040104001040e0403a02905002800130001440c04540c02141005c80c1c0c44400d023256400d40348010040e4604086c000440f001c0b1080d1024003141028982d03024251149417402403145014401040001c030501080d20031150380a0000c11940d41c490500419070001703440b241c030032116810304a01c10ba80c820700980d14003660100c020302d480741e802e171700b040300680b074803401c9a040064007000c45406100c00c204190040112401c1c6001e0b010000f000d105017070359071f20b0540c08000300402120b030980c1d900050341c02c00c8440f01c44269560927440c0ca011005001e4028025015205001711000090740315440503040381c2c0300340c880160300340518406076211200001c4c00003215101e00c0c5004032038104220b400d61024 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 19861679 1250 19860429 19860473
    0x3010b0705070f12021002060408030a0903030905010c080f09030a021518100204050a050105130311030f010903020606011b0c050103270807060e03030408030412090504090b061f050304 81
    0xb9455030b40029041d90980e024402c4120b040654000794103003494102c07020a0f80b440039000b60f15003915000c002d4800680f481c461160f907003050380185031081e4080300c480d5610000a0181d40b0110310005e041c4041540d040d00a08610008590b05d002d00000311070261046402501c3c587c80c100301c08120b82280102a001040760500c40303911524824001c0c05007140200c840145c685050005104038407501d904080c0c14410704101e440e02180914030030383c0803241c1c8a42034858007060750020074246822844400030560a2030010b100f09500800c54a208003000c1e602c5580d04d080170a001c9207003c802c060080c2410401000901882d44260085081d0a0300802d1a0400038506420f00144260264059800204c08140c00040080d071340039640290315210002c604604268907620a103100c003402c02401d52000403d5050081d000303084000c01440f0040041007131307170300a04088100d400b0498903940714121910400c01c2c10308044074000d0400381e81e42d407501d04603075480d5548007184540080c240c82311 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 19862929 1250 19861679 19861693
    0xb06060d06031202070303120e031c0b090c040503060a02030c0901030b0a0f030501050a0f1401140a0b0408010905010c02030423040603170706060806061503151215160503010b0705 79
    0x104032903a0010100b03c106900800400f441c50400401d460a1400c40105c0c190a20386107103c0004000b0039101c13113802d0807450310000101c00c554800113116071441c3c01d422039003140030170001d4803000c00604101d070015030542c2c0e10b035a02d90300c40070b04034401110540c1c1070b0309050141c0c1d1529446a1701c0043c0e4100054410b514441c0c4550111030901c5199004503410f80d111000c002035010607009440d00614500700a000c3c4400c080000c031195401401211a0300700600710742291a81d600c0f00c00c85c018001d51400641d525290304070a8064803242009944640c2401c40702106144004122403c440050080d0340240c0f140f0300b40100c0e05422000120743c815214a404000b0605403003031441c01c0c60715400312580e038100900e0018281c03585a408034480d508a001044150788035404203203201d0b0050000c1d10364170303a2400c82240700455034114103504a04004500c0210300d4002881d40f082a9030705940c1d071101d5a8030305500b850003036456140343c005181480100030320342019014116aa1080c4203031140 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 19864179 1250 19862929 19862933
    0x3150d02041a03010b090601050a1101060306090804080d11030307110a05010c02010608160609060c080d050106091e030c05010c0c0e0408030f0718060f0306030203030f07020301060f030b06060d0603 87
    0x90700c0001c0d1504070b50012905008074185002d20401c1120841030340c0342d010754604580081c09600500d50b00000f4000307100800e8480b44000e5000341c000d10b900802c10403070444141046400d6400501421044d4415074121104050280090440240ea4070000714615507500c0e00c2140c03480c4011402c8032440c032074010800700144003801401c0d24044a42d000003000c40c6080c501500d4a4000d41800e4030081001000b40603099009408a05607121414240b0380c281447c60028911b2280001140d103640c509400841c00b55441402c000c01c0340c450500f40e01c941e0381d003200a10382100e031382e2000803c0c545c580741040140c0d5000b100d1194005020f04480449245e56100c040a01e1a08035412182c4042c00020041558813118036990050b00304e1402480c00300301101c006100c01030350f00132b41c428010640c00101400b4420f4005102465014041c0c076101c1e1201c80112045030083c0708201c0c883d500f0004080340681c09a505042101e400c018800215203c9409010046c0e101c140301450f00c82c0c4402e00880 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 19865429 1250 19864179 19864181
    0x70c090b0d080c0f0607170a05040c0302210706020c090115050408070b030a1508210d06141203070201020703060f090605070503040212071203080c09030a05070306060f030803150d0204 81
    0x8070840c840031309001c800148499042070700041070038062100c50200d0286240408074032550250031010001220349030350900f00c00c1c007051a40001d5114080c11000070341c401446882000140b0400126500244c8a442c01e90b01c98450b01c0c204c1ea002251500100031071000324001c042c0d0b0300e80e54100680b525480f80c4201c0e0a003000c42c0c002c070408100010501040c184180704282001c1c843c4520b80d0500341c14007056588403100600000c481021420110000c00031104c03c0300c1207504100010080780c1eaa80001459010301d0791000ca1003405400c800b401600c0d0040704032401ca0782d050b4040d01456003181e9400008004480c3c41d03850255545049100042403481013b004255544841352645031a104014200103600c0b9070b84030a8000c90010012007000c000782c0210940e141c1420b03e41a614072420410342d008560802e51706108642c8076005000c80401c8010070340340200e2082c000943c4a1744140714007411480001c11041c010070016240c18411043d20000304001020484c0042d02a00028 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 19866679 1250 19865429 19865437
    0x250203030a081b03060d080a17090f0c0306070e011412010f09050603070302011b29010f06030e0a03030911090708090706090302030d201203040b0606070c090b0d08 72
    0x20011816050034004001010b003007050000346800d10142c0366107448800300b080100d071800002c08007e004a011102180240da4500d6444514086d000e42d91424a003442c1e525103011881c4841405944441e07041400c0110700a4443c45040d160004061305540045030b443d0582d081d00988140180056681c2025081106008209808000c0081c6081c0a5003034100c51024005a03c80d900c07078002000140d0f00224048040d0041a10080307001405041c00d403e005005000b0603140886542c0f6a80703801103100d507a50580d6000f40e1007210040e02c40d10290201c038181c0010407070680c01120090000b070301c69000700201c1031140d0340c801c0d5400c0c502d0340440c0040c0f2040c1c07640c0300070880401c10082032078410080507004102e10b107040a800c3d850b68022907110341d500c43c0d420b001c120a101d640d4884580010640c240000b200003261690a00b00514003034540050701c2c101c402d41d043d40041400c0d03103010401c0d680000e40060a5408051074a0000c9005256015840e908182401c42560102c0c0108000d0 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 19867929 1250 19866679 19866697
    0x60206060901080d0e0114040509100305010506030601030c12020d060203090607030b030318040e120408010c0909110909040c090c020304050405070912060203040f120f030e0f0325020303 82
    0x80045040400030800c1100c01600b21601aa02443d403509856500002181c01c940003800c1ca83c001c407e185090508234450381c1c100c1500400d43d48180700e8041e8905005404490240b4020021501c0d90403c140e12a0000e110180100801c03034003d01058451403400038205100602c03104074801c03555142401c2c1d810850302942c1c10380104041208941e01801500b640110843c0034529083c1d261141c01201c00602680f24081c598174141c01b48050b0040100b2204440288246902c50307644203a01406000820880b0b400240c1241d00080e031440300e80180341c0400303150840907040c40304100030700ca60751500800a888502501c07800044210082c45030a4901c9001d074065035445003010f06003c2640d0b00074000004004100d881041495020750202d50640d512070405030340c984840c24190b03108100b0180190400c1d00c80a8900c0c0b540e5001929482d410b600c544041c000350900311a4991102e12a00010754190010800c02d419005050143d0111500086c0a01c00c414200c1d008646035400280007 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 19869179 1250 19867929 19867933
    0xa05040b16120c030504031202041d060a05150a091509060e0a0e09070f08030a08070507060207021917010e03160c0f0801050403080c0a0e0105070302030d0f0f06050607080702010c0f08040602 84
    0x46c0018503a00c21007044000350a00d00a41c83c2c540740a0803000c861191310503030441130754040b020510940e61150080f0040c030005004038005500e0303002c0062154402008000800d0320384000041c0c1400c8a45540c801419a49510b07200d80d1034540142d4442951800050303100f4010710740031903290400510503005441d907000401055080c64001ca14001c1c0c09e8004ca940d40e4014070000004982c404c04c03490303200c0480d03d803490701d800c010314042d0040d0048501c000d40c001040f5400c5003007050802e01c03000884c0d56028128500d0759544e4421401c1381e500c008600501e4204002100c460b048038865400302074131484103491403680e5880c0044a90019400c501d85594442d02403006040c1c0c0301c020307580c10111608820f40303232103220800648081001d840440c144100071480d030b8103143c000d005807020b0811495081c4821092484c60500604214008280603490701c5004641800d201c0300f607504580d401070341c01c3d1800426070015180000d8501c011102e14480c0844040011306c1c50001d04001e043c2a00 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 19870429 1250 19869179 19869181
    0x21509120607030c0512150a09020c06070f17010509061201020d020304050c030d0e010c0303060e090703020a09020414060304020418050a1205070b0a0e0309030f0f060a05040b16120c0305 82
    0x40000c055800c107403100e004008003449060000c06d6000b070101d410071b12964000040303288000c04a032201085074440c050480c404034000b1a000800b02d29940704901a94032440d0a16500106030f956400500c2c42d44034a4103000010310280c02c006a41c10f0700004001d11281c0501003c1c0e0301182a0380c81881036003003a64000c010b0104004040145520f168002c074007504510000b410001d080403c842da8013410801d90307201d0401494020340c050000f824480b40303181301e9031070a80101c0fa601c442c0341c84102d000383c00300c01d00004d0b079003154400e03241500d0303001c40e4500481c0340c024104419608050030581c0d00c9aa648074000345500c0c2d01d5131418010348a00080c041c071410500f0800d4610304007503510700501c00100030323443c00550f0703c0c2c0b0509d0748005180070000c0c49a00034940d9a01c0c2d0f019406040d070b003500c141c2d000301e402d0140c001035040c0300906007000c54580e030340d50010580584400356401005040148086803a2a0258100c0c2c404110540b4150300e40c04d98820502c82581c140080302004266524 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 19871679 1250 19870429 19870441
    0xb060a0e0f0a050d060902040209040903020a15020a020d033204050c0402040308030a240909050106090b030a0b0a090c09020a081b04060c0201110d0305100f03050a0215091206 77
    0x28101155540308640801142d490f05000c111103903d0404028140e83c0e444250100319035580e03042d00c1c2c908901510812284210b0f15000c0e40d688400f1074240d030040c804041d45034080000e8001c032801c80e003280d40a8080c85602c02420341c05865450041d00484d880740b0506842c94100c6051424034a00c2500e01300002c1c100f6003080c505225000a24034002d9004200a001052001040381e800c07a1048000080d07050b05a0612142e024840780c004916105413000012a1641a04001d26030381c003880080141c999141ca1200c21070300150282070b05038100d03c1000001c0380161003003e9103c1444000442c5c007903240d540d0b041070800036402c141700da00e81c04519003005580c00740c407141d4040c0703001d2024451302510a08400060146204200070090307502d160000310791248130340807003982402085803035101c038619000e0060f00040300d03102d4542c00708260000e00e48585055040403070b5000f9000c1c021158198082c000041400d200250203080c0c01c0201421030340f00c0c907039005c0005010201400042c2006 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 19872929 1250 19871679 19871689
    0x9210602030f100b07020907120f050a02090301060501020c0306040305070309080a061b03050708040803100302030a0c030201020d020a0b07050a0903020d06090605071409091803040608040b36010b060a0e 89
    0x58118004d1800140000307070058030380841440c2c1025481c100303072003c003c08940031000f07020b031041c4050f00c0d2410442809658040303900030f40f403000e000300c00070301200b9154401260344030f00a4004a5147d4004000f0a0119004d0030040805e18040c2ca42404c010b0b4503561400d203010600c600440e08166500040c03401c00f8460400c100c08070100b0328040c01507050084d4000d25001c0d010708081c0c840480000415101c68000b00d0620013180d000d400e407001c030b2070107040118240700188026409800f500d6901c100191011030541001644511a11003d40303c0c8401200c50703403c404161000d2001468000c001750303680c0c6140940240c8206d001242d1f4101030b00c3c1920035590080e2541d801e1044040d46510118020313010340f1f1681030282d0309a8115035410700d8420403941e46001200090200290204134103a000074000c1c4150b02485030700c2c2a81d1103003000c800100342507050258103003a400e4592101d460011404000d616040000030030044505400070700c0350707409040103001283c0001c000d84483e05107 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 19874179 1250 19872929 19872961
    0x16030f1e0309081506060a0e031f02030a0e030405030a0b070c08030a0516030c05040306020d021e0a0e030a0201050405040e0c04060f0501030509010207050604020d060204030c0308120a05060109210602030f 90
    0x46416104d0b03084c10402d011402601031988540140300f2040c0461210361820002c412101d9844a2100400e4000b840e65a000354070503981742030b255003095600c3c120250004100c400b107910180040000340302549a50000d00006043c1004200341c0c0b00e20070780454400030142d400341d0100000010513040442c0400760034000481d440382498140007a000c1d10070b821034107035811a5007100001d691569803010350002846050f01020080925601c4540100e000a0140540994949800d440760b20a002090340e200b0a0322002030004e03008000c10702080c109504000c1c1404520002c0b28000c0142c00001000d0750f580d90402d00891740911810071440d80e060003602d4000c00300c2c80c005c601d4500070b40c80c1c07640c0300c5500500c0170b400b40341640d0319074040104581c100e600440d040100c0c510115220300d4604070541c810410500080001e2011900c035408620915000e2801619920340e242d1074a81c4501d510f4072908804c46440d21134040e0b80b0003188a40c002076101e116240341c4507055150203501c03200d174950 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 19875429 1250 19874179 19874203
    0x2040608070f0e0f1002010b0904060c09090203010e0a020a030209031c0f0c080304240c0806090a23060d0804080601030507060903110906060415020a02090916030f1e030908 76
    0x1c3c030b01c110301281e900c841e0500c1d03d8840301034903071002c024180d24080e8090700c1803540a54000408504010a10804e40d004000010090381d40840075650341e180103040c0d002c01e00030201140c400c0306c0071030652507a60b4001c1c00032401e982130160a00d04030707100081c200414440d840c4141d82161400e404000d60007a1103221541590520044200e80750302c1d01d40d4140001040206080e02c1010042d0021245000c2e1202d564502807050000a080384030082414000b82c51250064407408081040050f01d8080d501401c0c0040040207910b5048682107040007001900c6980c01100b1a200b450215203020014005009031300010b0845515500c3c28030315107a52035010304104082d002003400060900403403600c61032022605c12407151551000500e0a03c102c0d0b00c03130304c05580200041d0a00d00d0b0041a0100002d008480504c00c40e42e811078016107407500002e8420540b140500c0920000b144c50a010220300c0c01402150081c0d40428500d104542d81c0c4802075000c651001c10401c0607810800c41815414 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 19876679 1250 19875429 19875437
    0x10b090f15030f0f09011103060607020a0510091806080307020d02040209130207050c040b03060109050403021006031b0503010b0112020f040512150603010c090b03090f0303070e03070512031606020d02040608070f 93
    0xe940c402101410301015000d0b51140c1e100040f03402c25507a03000301e030b0700180800030410114040c80200203041d004143c0708042410b00470382c5100c82135800034410f500c12a008040030398079005066003000428880d41e4412a40540d080c4000d00b96505c0c0d90352a070b44ca00c01d0003000140e4a0445040031807800009140080c8141d0900e8980c1015407004228941101c0c05842c020074175880343c0ca401d80c00e100c0303510641290503207440800010b01c0181000980200c845120032640b09803910241400ea505901040b4042407074900340a80090f070ba41d00034980d003803800031810b09298403000010700643c4030b60501c050645c04902c0460f464819601c405402240860081000d42d80444018103d002c0e04c1c8201c1840401c0800092f0b1514810b021034480241409d080c0c07a52490a40c00180c040000758114078024859900045114241408041c01d984040c500460600c100d40fa52582e07030b402e41400c11103c468080c0481e182e50b03003490010700007034002900c5110061400130401403019002c11000e0b4100 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 19877929 1250 19876679 19876691
    0x20a0e04150302131b031b0903020603011802040b04081606110a0b04030c1a070906020105040b16090e0408030601030b0306160f09030c081e06010b090f15030f0f0901 73
    0x3014407980241c12690305541c040c2403041082081801000c40107660080001e0755054204403591640c000c100210881c0c201074084150720504994101150000a401220400041c020402003000b514035100392000d000d4a000c1d25420900f207150400d5118140c00e82c490704c6807081040304540d4060140c0710610f0000480034175408419a5610014001390802c44a41c0c00704080c540300301e42001840e508001d0154410418601100c0c280100f15000750002d24007000c0458800d106001d5180595045040070440351903250440401c00a010400002c1c000c4e960400100c2e00542e58119100d140681d072025181e190181c0058103451000780158030a070800e00401082071804240c82e0b8105041d490803600c8446203101c26106241c0c95000580010b882110000300400300150080041040e0000e10358071105810040341d80e00800e0080360199030081c07220070040d0412175151682400001c03d6403070b080c108412005032a80c410340f0300351281c2d4990001c00158600100b035064003c507520b0000c100c1 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 19879179 1250 19877929 19877951
    0x317070b0702120a03020a03060506120702010506030a150b01020a0b0f01050102010b0a120b04060e010906060305010c08010807140a090507020a030e030c060909090304030206190318110103020a11010f020a0e04 92
    0x166204d00348020341419404281d03101079038400c1d0f201c240502030180005550348100d214100c0601402c5804400543c24803000426500f004522405042ea02244c00031000c480c4401d81805030260b01c4002e0304510900722940c000c2654214018004e508641d500c25003941024002820b40b01e494041501401c3c1002e010000722088540641000b500540304035400e884900d0100085c14607001d14003070541c02d00740c0c0c0e40180701056204a0849200b2002001201045001504c248409108214494000c80010450341c0c013840caa804a403080107201c268440d4940056000721681030b589036005a001211000415420081b840b0804030304800800c0013022000c00510a84100440c06008800c011301165907000d0030030948010316070051500740c40d0001c000c0c2000400f5a44000880001e0a0688808402e400c0b401c1c966151500480610080e0648900541c040c0d448081d44008201c510106c0c025009400e1141d020f86a24035007000d13944504204004001e451075101440c4924941000155 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 19880429 1250 19879179 19879213
    0x606080c03070f020a080c01020a120b09240a06030515010c0b070c050c0904050a0221030301051c120905120309060301030f020d08030106090e010603020705120d060317070b0702 78
    0x103804a120302c0e003914040f185000807800c01001500c024007405020800729038400064024003040812940c603001340b8842c40484800303541608101d90b8110aa04000c40c410301c0c11021030100e03407500140000c0305584420b0114520100740d030701c070500080e6100103010f9030080000a0320010710003464524801a035540b81d030082d0042c00750a0005001032013904100f08042403000c030b420940d00512102c9945414181191100400d000c120310401c0780c103550071800344112011f031190041c1070f001141141e007007600340050a5075800d0013480311000d01184a001660866008140f02c01c9941e03945016031825003804803103506070103042e030745130000c1c090324550b034582d90243c83c1100d801000200324100a800841d40c1d000e10244080c010220000010450b2500800900100c0701030f0502d41110f80c3ea5084100d0490250800080c050b0300403001050804203088007501c594581c852001030307510741c0e0fa602e17030361043c0d80d10400f4070b00c156003c01d0307035028400e000c804145d22100d503002034100312180360700082e = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 19881679 1250 19880429 19880431
    0x30408070b0c0a0210150b190813030503010306020306040204080a0c180e0c09040201110d0305010503100209011d13090f0b10030305031609050402041202040c0201020f090d060e03030f01090606080c03 88
    0x6000d00c0c1c1c0c2c3c0c00c10f42c00d0354040e500f001c0c00140180342c11f07d651404c24603d100b250040c0f10160b034020418402c0407510f0211035025001c54680c00d6921f0300c1c04d60342940e80d550060f52000e001d5550040d0280030101303058000307110200c003031442050820940ca241a115a02030a120b5101c08012442c2072200e80e010351011075845c00c141400c40d0302900640d00ca10040e204100c01c03507462605032003841d0090004581550050b07040e5203048040718400119411104207030310550340050300090714049890322491002e8103240d155039005000c0c902d0562410804021900031070303015500590b20003000010b00088013421a00940d503070001c20714803030443c1c40c040d041e8800501000c910480f1a180c6250041c45401010b020f0400107006654459542035440401c4490801c143e00c510300e064041c1417450700500c00c5072800c146075140c2c40c1c1040a03000811801d000603510564034191200d8801c202400c007400150300c03030b910040444805504081c0d40e10100e40d5140c0002007417080d44c4080c4070651410b00152 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 19882929 1250 19881679 19881703
    0x20117130b041506150e090c0909091f09060509060403020d120b030d0c0302100606200f0a03091a030403050702040216050604050f010c0306140105090d08030408070b0c0a02 76
    0x18070a19100c6207024001c99501050b2400c07500e180800c003180b80c505c4206140c0300e042842c0e0b10790032024039a1040004450381958114022070081280311460b01307042180c141d2114614081d10a20b001084402591140301c0111844490740c6401640400c16079104050300004114014440d600d41580d020703680d050300d03400b05002d0140c01089001140c40640211801d0351020307003699150b00b51484041c0520010010440150041c80038170624801680300d03010454515a458051840c1d103e0713680c100041c0b1a44403103009000e0f04c0c5080355142c0341045009180b03446a40e4100310f0b0351405841195004a1040c1c1c4e0ba5100030800500021a80c860305903042c03141c040300c0040c1c2e100002d00200c4080c02403143c0042182c0120004c00081c0a070105080402e0000030f0000d005501c0c0f00c0074100c00b01c03904c0340180380f00380f24058403010095106070040c0c442100c0240c0841c40020464444242d40d8008541c1168007080006903001044040f480c401d0300315510b01c1241e401c003a603841000e52540d80200407 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 19884179 1250 19882929 19882943
    0x120203070603050c0720040b040207020904080c03040801111315050403020103110904050702010f050603070501080f0403050c03180f0a0e040209070504151806020f060403050306030304030206040603050402011713 93
    0x8580d08646500480d2036565008002020b00008034440b070601e050003c81b403d01c514500344089086091900840d04100e07401000706116135034590300ea06450300000ca1079102407000348408600d01200b40b04180c20946d41e4400661240081b88404482d81300503000500810320b00c544d03540c0780307c1d041010394060720b6090034086148401801000210302617241c40c641c1c854245400d0014030741e01984405021041c2c07040a11681da941d2051640c3d406192088070300203111b044c002610190721014098006120345004d0b4a04601d07880600d00d96040659684224400f0700d5001d1260310301ba00406c2007584096458480300b5280c80143c503640e44004201a0207070010b02d000400141c4210300300c4021b8606100324200040300204001c08141c1082c01448103051200c40201d00b00d40009140000c1103000b000402c000e030f49940e001ca0360740d00003401081e0580301c244000f000590f00d20029002500703940d58005954905800011b040c81c0d5404060540303595003200340aa69800070703002c1c11400ea00050 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 19885429 1250 19884179 19884181
    0x60303040806010b0702031603030302030601030b0303130501030203060406030f0305030f0f01060f05130b0f0408160b070f030e030a0605070314040203030406050a0909050f0603060906060307030b070e0406030605070912020307060305 102
    0x401d00b84858036280d0385008e04010000f10401d90107a02650188a0a0b60201b0848604605041ea00d10811020100452156204201562103031700116030042000d000070415554030b82e1124190602d070b10085000c92004005c0118030b800015006030700203014880c01d001545000c0d0003501c51301c00a00c0300000c001c0c0000c8c0c84089203007548040001880030072030091380c03400716000c0c40e191500203004030070050003010071210342100303000300d82820341300c00105462501d0280d50b00c0220416200c0b408800f880301801e480c1c400c03654140502c3c14032a00400012403d880c101c08000c049035040d6403020809203828080c000542c80000995081c0c5003541001070355000c0072802035132003c1c0154400407040e0300303100c104185050200281401842d050f0102c8241e5110458295140c04044481e1a0583d001c4401040400d0303016090a402c410142001682100e0b10404141500d480741c00c165030058803101400103240c0c0c0052114014a0001c03a03204110402e940001d84440c8144104010152620 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 19886679 1250 19885429 19885433
    0x6080f061206010602010510050103020c0d05130305030703030902010807080709030201030507020c03010207080d05070207120f0204020c06070908070f060507120e030f07030507120b0a3b06060303040806010b07 92
    0x1103600074062001c002141d56641c1d650000a0203000c0c100d035500c091003520000007595502a000782c0b1200c3c0300840c064840340381100700841e243e8121901c00505846c00240c004081070b0301380001d060913070183c2d40200300081e071030001401d86113001e4005800c02c41c40c44200803c10790f10072081c00c1034903030900c0c0100703560300c031050124078050b0990045941548000782c0c044c1004000c070000e01000607024001d124a540e040016a2100f4551140e5000c0c07464940343c0c3c10000d840c80c3c0d0101c9400340f00030001414416410f4a8516140d0110f458801141501505004980c81045018001c0c1900c0a5080909081c054020058015090000e14840c1c0c0440081c2440d40134901407070f40100b000d811030304e00b069040d4940b81d0b515442d00c01a00c032401418000724011541c0340c041c080083e042803007001251607060b244d0b401042c024006c8864018100580c140c0e00c5c040d0b0001010305a401e42c5841005035448400c0d60034928013400b078500c65401003104000f000d901141141c1115840740f8a00c1d00e0303132001c0c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 19887929 1250 19886679 19886689
    0x2040204050a0e010503100b1c0c2105010e0c010c1511030f010e070302030606070f0f14030d0e01050603070e0c120a0c1b081c110c010b090903030106080f06 69
    0x16007005900020b420b90229896019801c0e4130b0480703c040b0300300c0d024101c04121a000716907041090903006407640080c0c0c0e80380030f0030000484080d4072811314071921583c1c1c3d01003000d5a890100e882d50211400c010340340240402401511100d42d00e5001501c0114080c00000c0c048440b2000001c0103008804958440c0182e42c1c0e124100e41400c15115590313900d0298801090700109001f102c002d412010040342e00b0303a1291007524464800500407e1030720455841d5204000d035110f41c11181d0000381c2610100066a80344804071072103190004544402100d901441507408405c0801030fa60b14000c100b014541d4001103940489101103c50001c070f4981000808061180101e120408030212043c49000c3c4e8850b8000c611180c200c1c1d03102218080810724562108810300d4002e001c10300e00348110000c404591003406015850144002120100602c24040f03a8020114000880c0d54a407040440390401d03500300360f840510b604c0a50301d150305200d005001e021004d420f103c0d04164140000740c0c43d86403 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 19889179 1250 19887929 19887937
    0xc0203070503120a0f02010c0507031d15090406080109080d0c091d040201090608190f0b0423010b03010b190c060f05061002030a09050621010b09010314150409020402 73
    0x2d070944958204041240d03c19502c150390440010300c1005220304181c1c4107200e2009171801c01d80c1c1d290318190290f2405c030b0754411240080d88116044042001a50741c400c0b240101d00b0540c611021786441d1050b042008076100d50f4030150499041c010020f0020b0080ca00f22605d8904602d40081c030301c0081041210f0f10070142d001150902840013203039001030302510517036200703e10076a91400b0729500c4000803201c041c419150400152100c280d40c00542055030001ea5002d0125036000a03140f5401c00082c05032800d803a241e40a103100c1001203020a019100b22602501d1040750261455240a0b80115030780318145060b90751060000103688081d02c902048584160401420300080c540c030000c2100500d42074905610a421804550b5030150001c0292000304000d515901c0d4107500e49414000203900090018143d41c0000411040c88000d808034a4080c104180390349460300c00d110300240858096008250381d034106002041104072599101c031076414010395021822941e80c2c80414041c3c01 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 19890429 1250 19889179 19889189
    0x314010603020d0c0510031107060924050a06060f020a0b060a05060d0c020705030c01051b0f010504030906020105070e0d0201030209150313030e04021810050409020d020901020c18070c020307 84
    0xc80e102044040c844c1441d1004242c0300c04130b40c00d02c1b0485207654181d0032181c019481140c45201448544003040403075000a00e00380c081c208002084210070100182d0b402c80c5040c0854050380d520520035000c5140c4500000b504682c2400035040c1c14008019607034044403240100201c1c031030b4001684c0c44e214108821700a01015103100d4564402c9105440505800f14a120051040b60400101d619002031382c0d020980301a12518900040e404280621603040710a2b02e109200e5030007000092202440343c0c0344030703900030351b1000d601070304004000303003519805403610040000726442000c00b81d8800304048801542400c0c0160b0700c44180000c0743d00d804004002881105000c030400852901d00103403c240c840c0f10b580d031400d030500910304220490117201c4001d880c110394044403440904040b188000310301040e00b0300500309503a800c80c000982c2e100101e0400c0072500420151455601000100101c1604442c2c144044084018486070210b008102104000016a01d5029901c05102da40080c3c0 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 19891679 1250 19890429 19890439
    0x30a1104060302070203011a010801050409060914070f080a0203070608130219080c060c0604030507020d060609060608090615040f0b090c0a09080304080a0308040201030b0301051302031e0304031401060302 90
    0x81d580c1c00000d0020b4000c103005034002e50070001c800c11540b1001c018100b500d4016142c11003541d0038042408014807440d10200c0310719940e0000c0c0303000714400b070351070160f9409000010700c203403130074114402001e01090384010340d643d00c00910080182e50100701c04007962007501c0c1c1180d003546c0c0c43d102d45210964400020b900103e402c01d482c540c02d100130307a608058074521401c0300c6c7c4244a0f07109205291040c0400703418190000e5000c0707400a407081d4024a9658002400501e00f12a2034580d00101c5001e948402c001039035980d0108412900402c0da50b5120000350064052032401d44124003103085104030304ca100d1b0703640d1605014050a26440000c001038040c1410000c0d00d014016400750b68050600000895030800740000c06000000071a403e0b035078400050441e5020550f81a02d801c140584124141600d80742510702a403001d2150744c1c4036101507505040c442804d401030600b031904140740b02140078959900a40300000010071541182d0b0300c510300c0517124407194107ca0061040d900029884 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 19892929 1250 19891679 19891687
    0x903080c01060608010f18090206040f08010f0b06030601020a0201080c1303031106130201090303120f091208160905010509120f06091002070b0403030b030a080406052709010b030a11 80
    0x101a05621060559485446101c032698030b46c02e0b1034005101d00d03c20100500c007040541c84042100c0c0d0020207a091001c0c0031182001e4851480c00e10440007a04043c00981d5a01c1160070201d46a029402689805035081031950400c040000e460700c0395248041c2c1404905004035a000010100304e444180503680081c030010789a00c0e0080c4142e10400700d9066070303c5044c01080e103c00004071501d000680c1616402e00080c0f0b0756600b07842c0d881c000e90304102030565801c60301a1210081c0204904144104551200e100300540040d061200140000c2021417001252502e02500042010261402400c0040e100d00f00040050341c031244031303010880380c0e004041f0b02c039191601c0016818010303020035003980c4000b44605080c2d0200c0c0110200503200039400000309000c41c0c0642e1181030340c983c0103400d550402d200c1c2d44484505a00c242d12140000e01d001540d9807003043c000001c254450106003080002001701c0000440b507040601034500d0304100000070940380310300c941c44030454081d1024841d4403 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 19894179 1250 19892929 19892947
    0x5060903130e1315090501020a09030203100e03030a180203030a08010f0b030907060503060102011410090b0a1a0306120a0305130e09100c0e090a02031b1207050901090308 75
    0x8940103290207450500d4480c401048626181d08a14030901c44110001c00700741454881405140c1d00c14103071840310342e44100e4400412001c0c00140b0400036640c8808a01500c1d40c8181480d004510074007400341e51038000a0859018040202c03500300b0a401e002186500541046c214943e044842c02541071000084015049800441c400d04a442c0c58540c0b140c4d280e500c0d00c2c00021440100c0d5003103142d4101004c103002d494000d0340550340042c1c040c0300029080300d90880360a281c3c03c0130b45000320f608010f05820821282c3d02e0050b103625203410f17540403a02c0d41c81c00c4c01980d103400c0301382844481c0c01c5011000039201c0e166540160000680c090445030009042c5c01c01800b1580541d01d02d5000b80b0b0351400104011808082c0c0501803480800180707100c000c10794607080103215511908080080183d1940b00303540d6000a098010b4540303c01c0140d1340d0030300b00303160708141070b501c0d0030b4400c050300500054441040240403030ba4410002c1c102169a03041140048409170b14603000244000c00210703510f49 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 19895429 1250 19894179 19894183
    0xf020d02030411121513031106040605090d0507050304230a060306140d05060f0a020f0a120c0215130206070b150901051f140d05090a03170c030103021c050609 70
    0x441c5034140e95100c04da9981540c665151141c05104c0d515124400002c15841e45541000507040ca01a2400006a40050800034204001603d0580300c61343c407041440044c5509100400c4040c6050410340e04e0724485950341d94681c00b83d8410800c00300284004d41c44041800400701103004001460030143c9502c800024004106c2c83c040c5d00410711800b0302c2c0d18228101420310988054001c03004240e0750780e0300850341c030411000a08044030b0325020300c81c44604c031030322001811046205444100e014020a890001200c2c101c5030140c3c06c5601c00c3c1c2e9020910001345c10210b07009000317440065006035140c00800e42620a107403008040b0010f000800c0300807140d040007004130b400110f90522850340d8032010000507442e040600307a0034103400646070002ca070040741c1e0003124a17140700110b8104910040e9100440303000f01c034a110103801041c1d0400405a00540d440b4a180d495086207006007804a444a030034041400002d0150359004400c01610300c450007561625a07020045441c2da02c0c00a24090f = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 19896679 1250 19895429 19895453
    0x30405070e10330914090c030408090f0a080717030403080306011d15030a050a06060f030e0109020d0f210905010f020a120905130b03060403030b1c0303090b0a021602040f020d020304 80
    0x8100050743d00030b01c805d140703400da04450151100300409402c585840c0c0b41c48900750b20001d41c590340a141410003103402d440d48a9071740e000b001d241d4050000d01e850120644e6075000d03104803103c1141c03c00c10051000540c0c00c4103581d0401001e103003203040d00d0240511144000600754103503a0009441c0c0010004142d0341d4015071051030102024001c2d900c4444890042d16900d0080700042800c4512501c0e41910035130001c1d518082100c0080703060191038010500c010a2032809991102d040705d41c20042c02100c080482e2400702c003680b0540240034030200100700f1143d5000c4c0504212003018402c81c014420001028602d400c40402000780c41014006031200740316200d96401001d1da0590300702d07025a24425840c81c80009406024183e540f507904900400e01c00c6103184e4040c0003203000401008260500307070740c2c5912944001034100000c0c180080742500c0104885030160040016032070740051580300001481e03050f18045025059010040040c0c0152051841820b2000c4208802d015101c0116 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 19897929 1250 19896679 19896689
    0x9020a03080d02030709081603031d0405040807020f12120f04030605091b0102012f070503040305010f050604180f05070510090f0602010606140310090e0102030405070e103309 77
    0x31410460b47e581002d91160402d0080712100e030030101040001c079004e0807802200500c03503940390013507100c0000041c080b40e10a0742e083c0c0b103080000c2030410071803c04511020821100b21001180310000300f61440d924240354101d00c07505803000c41c41c000030010784800c0d5005950b12170b606105130f24200010070b9072405d00c0301d50388503d00300a140c1102d01d540188200ca6101c1801c05081c89800d541e4400c030011821031810902881d2800c01c80800800c100f8000361000c0c41c41103002050401120403c00140c682c040e000e148100d203041c510f54103001c00d9090300000740d6849000c400100610703081c0141030000c075034000b03604420403a00c0c101c14103520008c00c0050b83c5008120a82c1180c489004070b080760aa0301070380d400b082083c560800c0d504007a078095540070404d15000c0300020344034200c490681d90030f0010030103076a40120074481005810300601000e00700341a2140d100303280c80208800321600303610800c0c600c0e440c40685c003800050046042011340401c89100f000e000c1002400070003150652180d = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 19899179 1250 19897929 19897937
    0x30403032a020a211a090c1504050904020f0303190801090501050612040501141306050108060c0304020d0c0b0403080702040b01021c030e070e070804031107051e0607060e03041d041509020a03080d020307 89
    0x150b07c0c6103140c503120604540211050b00c0382801d0414092000001c0054000eaa0000c08540700155a0758100028140c184002c11140c2810884a2015040c0f07241a00030300c0b806e5041c500140f01603240e2030f0a0b101039980e90711142605444a0401e64010940c00d851944c503000c88404103d83c41101c0c4041c094468070403401040640c0e40c40d580300da107411742a22070980c80202040814050319004c0000314a250246e864000c80315941ca108080f558417950044840844c0812108203515151150140480c800c0c00134003034011880406040c5016081c00070b5092641c4c0d0805080030399410801d070409820f448034011540d082001001d46451400c23a8201c00040d8480d04d100002400800d012003100d030050702c10141c0e8001d0308844d40d002c08800401e103400034400e01140003c13910a009581e40358040f1409166518241300307444808000d60f2000e88508190f190500001078404401140b8001750094000754800d90361000401d00d100c076500c05402d101c80800d000303003451010f1303000b10302605c0e440d11 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 19900429 1250 19899179 19899193
    0x12010b0306150702030601062001060e01031e110105030921180a0303090302011d041503031101090c03060510050d06061401090303080403030518030403032a020a211a09 74
    0x1142d60342511a83c0002909a0000310041110902988160102014250100034004076112030a800c44119910039204180c424004001340182184840d4030030003404041c02d151001e90300e9080c81c207407005580d2410814008009601c0100900c1400c0a0700300c1880c3c41c0b2020f80070f201c4120082d801041c0784040705841c028800405140140b9404100c2c3d605848003c0d600b0700e10303001074a072030203442502c1d8005000d80c44900c03030070365031403107070f0110325030144101c080c0241503040003070030101250401d4081d41e1418030700c100170a142c20740306012268042804a107554900d00c809140c81c445070f0005400c400d41d1b007010010018660045c4c01546c1c00705085030320038880c0400464029440b41300c050040b444810204010a1003078015907407014400841c213a03520a0380030040d10716401a8801e40000d02a03040c150400303e8007825542e48030700d11b40420050300e0078a4001a100041d81d1045201000d000d84141172015441d5940c000c009400440c0101142480d844010310490103c45100540c0100301c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 19901679 1250 19900429 19900459
    0x8070b0109090b0114031501060203030702070f12021203040312110c0103062303010b031207050606040b1005030403140409051e07080105040e030408030307030608060901020a140702010512010b0306 87
    0x300c5210702540d004401c3d00d00741c0e460b200c0f0b07001c40d5400d60346205801d401226030240c40d10301c900844078024101035004596034542480d009007816829007100488070001c0c401042903081a80d200c1014030b404036481e1240c50890355001b403a6100d564402800c00256034000e11145400c0042203d280580c281607444a01d00a001101140e0342802b9803c0d020984480282020f11060365014203424060000501c88141100080c50003100d070801003240720b40003403101d0820206003c04e0740c100500740c90521240121b00c00113059120464600410050080000b6007818410019040e58241c2d20700b903c0d58858440240502801040303a100d2031b640d00d502c0c080700702051006500c9200d80d01c150340d806080c1c1d00300400c000142038603010940c1c65101c103000200700d0150600c015809070401340c034001002442c0c001340302d080c0000100540040e91042c03040203840c0d50860f903681c80d5039041c1480203907150070310720050340d803030180300c8012120003079000012034101e5241e4025401048101c03032500c443d41c140 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 19902929 1250 19901679 19901681
    0x80103030f110607030207050c041d0d180314120408160803090f06031308120f07091d0a0905031b010605120304120302011803020c0109060f020309010c03110a08070b0109 75
    0x1a0b495100a50b02850004600303d101e80d0107842c4241c49101074039020b91881c0c000034140d600840028451f070200304000c2107035a000700308a6140c103441d030401030680d01c00e1892064480703020f4440500b4020400c3d014416615040c400040112151245942c4427900c0d0a0b0850352550700758071080c903080d5090004a007203e00001681c044140040c103011404001009110181d00301401c00500c0540c07112030980042c102c080a400b259841000a441e14030741304c0c29440484a01070400010b00550b1802404004c4c546001c0751070340041916241000d881c0c28810340001c0002e03181c05441c07400042810403014800c525010190b0024800a009054580042250700c0d2805400f600707280c0d108210410851804640340c0340c2242c06400002141140741d90b44002079003006504400582110310605070320360b0030400701000340c400380c80c250702821140308000e03550744076503d03c0c1d03410702c00c2c4c0402d03500400d44290141a50542d00c8030540e03a20004915040c4030a03081f81c54120f0342c8000c1c620000c1060806 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 19904179 1250 19902929 19902947
    0x60106050f090f040e010f1b09030308070806031504030513050a050d020f06041a0408190c2304060801020901081e0705070804030c0e0708090c100e0301020c0607080103030f 76
    0x84500c01c1ca40610b00041282100c00b2008068000f07454540710f0404042c03e214445004e040b9a001203000b50b00a1040440c04045800380c0c01407080c1000181f000c13961211003a0b5100070b8038240b400c0c0a40700c441c0002e1808a02c8000c0c002100e080380100400c145d4441c000e4088400301c500c001c0f0015031180f040020000c40f5028603a008003a07041f5420251403d600484544040a46624138060311509011003401100204000d4002c000604016021081018486c081d020920030f202c03104007a80c8040d180107541c8101501c9045040c05814a10b1080000381048440180100103240d074503000c80380070b900140101808249020001800d214a01d07500142c2221101c0d00e9010135a105501951560401d40c01030b10100740501000c000690f100100b04050305900022403c030b440c0c01480180205001071026840d41c001020310307880398950303800c0000310404505000c070356900210003087c0203000f8100707241c2da54441e00302803080183d0041c01940c10303640255221403000900744029114865 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 19905429 1250 19904179 19904197
    0xf0105010e0415050301090812070302030601080109020903010b03060a06080d020604020a06030e030f0706050105090a020702090114060c01020d090224030114010c0212011508120f0304030201021201030803010806010605 96
    0x11041003112646070551050600c0c0d0f20507082c45140b02c1c2c07a140404e08441482d04100c4042c400000d808007440030100855512a001d0714040d4603600c1c207000000c02c0c40f10103110305c14841c1d03000720700b40403503582c2074024a24030301000d001c40d001450310400c8000035103114851340d42140100340302c44070440c0c0f0108481c1e214035000350000c416a032402d6801c5009240000314269540070902c1a0085030318682c0003060b20034041c0101241c594104010008001070151149400d540304204103001038aa0010403811101e011002c070541c11340c1c072000b02c0c065101da41d165038181c1d4070001e070044201c2200c1c2e120709641802079400e4074400a40388402984811a000c8540740e5080a000420001e005140c480e1880315041c0350a800350901580484e0340c410400304000600d0b5150094800100e603100d620800802020004156032100c007005d1003001d01c2407060b02c9200440002c0003c003418004d40403110b2108006e85a900c283d039582c101700d100c2c1d400a004010142c0100c1d4000601d081c455000c0e14201d103 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 19906679 1250 19905429 19905437
    0x606020d020312060319030c0b01060c021003150504140a0c030c02100b0f04050903190504060c0b040609020909100f150b0a0306090c02030406030b0d050c0111120a1101050f010501 79
    0x28100750002d01c243d4801460154148a190491002042090a0316600c54400c0c0c4640d41b102d0340ba40360104035464143c1041c001c009489880201581e144540d404107440d0340d060004040510000100b650001c0b03800c07550704a8280055070300044100c0880d00c0c811008804208100042e0100c120180c4207982000801130b80421684414042243d02c402c0d0084402440c0201000c1c451010806a541c1155448000c0d080800d0030540c6a44501012141c081c8600c1c2c0070385080d06240e0040c00807101081d010b0105000880094200941c0d03510181e162500100444201d20f000d8002039076034507003040c010b40204e00344030400c000b0020700e01410b00c0107400b9540c00190903003000c2c200071054000090311000c00d13413079042c009162203881c41903041c2141c0c00c2d8055542c0b02d080c500081e06548084031750318050781030310252002103000440c043c841e800091a05014542a00c0442c80c5010283c8203203401d00d8000240c0c2101090b048000541c18040080091041c1e9568012146000b90240b03c1d085c049 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 19907929 1250 19906679 19906687
    0x3090909020f2101050a0605031605010909020c0106170c010f080609040f02030109020a0303021b09010b0a03050711030a05040e0603011803030c090e010806070305090d020c010e06090409060902040606020d0203 92
    0x43c685085107580040d550f000248070000c031a405182940d0055400c035110640c0e802c028040b03420305004040040344000c0300151014074180000744410524401c10b10059400314603c41405829044400101481c2080700b6460100100b51511486003030703420740c04030300c0c07040c0600285401048000e1182000405e000700c0c1d0358840d11031142c181314200302240c0c1956150b00b4040140c1c4e07061080c0707000c0c40c02a030044c92504d401c1c1699440905090b81000d1091802c00010800b40e040c0d00c04840307a01c06985400304850703c031820191072002003400404061700021130255510b44d40030020700700319541c01191108646070351061500b00c40c25211190079840801300344002003402504075030a03041c4980b804c1c483c0c0341e6650448054150082e0488007031600440284001141d25001c1d4942203402140a45211403440c00060350b1904040c0e85d041c10301014901103503140c0c1d2036100380d0b01c480d003000e0401e0012020500e2b202c40185051b5070220b204600c0c000f800b107000d070320015207003100c101e550f0015498 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 19909179 1250 19907929 19907959
    0x1d07060315080d0c03090905040b04063603020304050a08010c090f0302011b0c050604080a12030203090a29070f02070602070503030702010e0f0301020c0a05010606031407110115120309090902 84
    0x1045804c00c01901413041c11480011918420310440d84154010041c100755420075181c11401c1d14021aa1500050b031890514401401400c0544000304441d510240503510507107010303401c500496010562210240000141c40d44040d0072940c13180520303030307a01d1050a44485c454200f000b00c1b80800ba0000b030700070007410310114200400c0400700b802070480000c041da943d4002031aa500c0f031f42003a031040c0c10846a401c04c101c2d008502d541c0c00074140c2000d42c00d515218040c5540ea1030300000142500c1c103a10b48202c042070003600768030100b024420310300c001490720000203041e02080f000008010700c00c403440011700c00d00c049020300544000a015618003540f503001154800b500040c1d5551004010302e4100041ea4244004c1801c1c0c1c540364084c00a40e1950708020b82160707010380c0910305050a2148035944141484246944442207040030300180b54402c00b00b40c01040ca02e20701740d07001d250f034041c04514400402c900301101486695401905e54079224840c0a941040c04000d400c00f26040c02d40407 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 19910429 1250 19909179 19909187
    0x30c0d050a06030602041805180607050d020705030406030e0c0d03020706050a02150106030603170301050105070f0f0203061906090b0a15140a05070c0902071a0a1d07060315080d 78
    0x80c11035441d00021030a142c5070b441c0c1070300700d038099803010101d0708401070140103010190080b0741d402060144080543c2e1111850780343c503000020041c0b81088000102d01080c0c29250303041c0e44556400c04100d0341c035143c5905c405001171038410004070080c4503107508880d551500040e408806945a40605103a62803d4000d445541141a0407402e5003d503280361082c51040748103c40c0240441d0743c001ca8501d245003001c0c4090401914940b040c031100300010300061342c100e01100d910a90180c04520603040f5814010508040e80350f0081d450300600080c030441c040303600a400c50103003400004000b0030795514040402c440c0003405098000d41e01030000c1060705a00d4000c00c412f0785050034912950050086207107000e600540400c0c01249012607003006200200c4200340c084c00d0a100e0441c0340840c0d40e01c0b0b240441410340401c540b828054800100100500d4020f80404981020500030825240801a0300c0710600d00444000038a4041028600100d01c139000c01200d440744060014080e184404031 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 19911679 1250 19910429 19910431
    0x130209130e0708061009060605070b01120204020d090c0e060d020d020603090f070909050d0806030615041508030706180807030507050c060d0903090608070e0607020a0312050c0c06030c0d05 83
    0x607216000300e2000003500300041c00345034403c000c003000c136803221410940c0c144102c90031504448d00300242032101c0b00024001c5040741e4155a940d01941a05514520005010744500e10b5802805401d002030001040400c4d000c070f00644d01d1102d032000d40d5945000038003a280c0c00654010f0740c000e00002050015041803801150014502170542d800f4134092550303540750100c3c550151001e0b513619400b020601a040c000c600e42d081992910500a040c00d1001a90761000030700710034241c80101c5003c1d000b56640e41d0100b0450403545c0464644e5903034618070304e41c694100d0700090340c015040841403980705801070100c041d51a808a0311500b880e440b41c40486640c0c0055104641da480380d0002001c440e0350700c0c1e002c0c101881d000c01000c500048185401013105505611040038001c80328107000c0c443d60022071080c80002c0c1074a2180d22482c03540006038031030340c1543c40901840c95100040081550120082826220003c1250440502070b0140016880106c90b51852140305000c0742c446081e40d60052 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 19912929 1250 19911679 19911701
    0xc04090506180106090807090603030522090608070303080606030c0313030903020406030f03030f0b01080a090303060914040b0c090105120702011d030a030b01030501030f02151c0b13020913 83
    0x222080007250082d595040c60a030080d40100d01d01500030070101d1001c0109401605204030f092013a01d02d507503400307012402042201648100b0101020380001904810100241015802803011940e40c1e104c580c1c0f1280140026000180b0207400200142068000caa0094518040c068556920940d107000880781940040b020003003014800170150b500d500801001c0c40c010482ca001580d51480c015085a0905d43c004111500304001c004c03413617800907440c69110782100d0001c40d203018985812802442d4580005081ca49031241100d4452042c16446104074804c01c580c0303281e52141c002d040001d00880140da0300140b01008030314550408000f5281d0018514000403c010403440c0c1e10814409610100300c0b455880401c183c0c000caa4503024070080341400313090400c041e50654483d1000c0d5040d1040c064020b0140400c910501c0203000304440050241ca603440c00c4860301240b03444054004800c0003886220a5280c0c4d4031580498402c803580088020082181403541c810400c0103030001d1002 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 19914179 1250 19912929 19912939
    0x70810020f0706060602030d0b030d0e0f06070606090506010905032a150c0a020915061603140406050d0c0e01050714070503010207080306120c01020703031d0a0e0708060105030c04090506 82
    0xb00000048160196901600b00b5402a5803152404010b81d02102c211002c014440d034846008003c00395005040c55480c00400d81d00b24050158041c0881e08a110b0b086004000c5450310000040400b00b6074003076406550240c0c0c44240c402e82d00c408041d9100341601d40310039050b484028000203080c800c10140031200015240061010b42825000a1500704000e0600b151b0000d0302c01d24110700d04504c1084e03105601f0401c032004a00d64a0100303119018080c4001000000da046000034103000315031580c2041050203409580d04d0303d4800044c45604070381b0800075024103041207030786590300440d5000b80800b0103a43c1d0509200c3d507615184020524924100c003c0d0040241c041201e840c280001e00b20b85004244442c2d4a0a00d07900340a50105056019100d98100965040a6030707808600701c000c603078043c03421100c030f0b01100f203241910b481c151403950381c4507205d00300010703e400c0d1000c0322610076600c82d142c2420541c0d4650064480b8401241e00000300c0700100810302021206522040e080343c1c1c082c203 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 19915429 1250 19914179 19914187
    0x5070c08040305030901080604020c030706020304050a0f050a03030e0303060d0f020f0415050306010e090c01050a02010612060c0807081005011409040510050307090c09270c120e070810020f 83
    0xe65a0a59000d0341040ea4290000034130034070ba5580055245801200c00c0c1d030f0440c540294000899107900038024003c21007500080030800b030000c200002040c80c0d401c2100c05698440e6403400a03a03504000314210042420002d0b00c840400f00441943e00c201c102601074074001c102a84c03602d1510b40042c10481e4000344104020340c2d0742d180c42c41030041a1101124140c9414180400c15141c070703805a0010300308200c10002c100503210b0100d05541665404e090840d1154810801a4058001ca41003030402464410080c1d060041507084401020700e01d0729480c03100d0715442000c4840c5031040320034190882c01031000304a194862105003141c00c0303825a507603092098100006080d10b80984071040810000c071400c0c40185014084000145500c04c4200034500c040000644280814801c0700a0710814042c10030303c4080c001c101e24808a003227401080a14481c00d4040c199881038203203402d0852030810b246000440c0003800c1000c0c3d60500b00180744803a80007841002a600988540c400360740c085c0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 19916679 1250 19915429 19915433
    0x818030309060c0c150106020c0102150402060708070804030b09010b0a06031a1e0301050c070201080105032b110105040609060c0203041a0d020403021503091203060d030305061c1406090604120305070c 88
    0x43e07031700d9001e081107601900c0d1000c1c01e04002447e28501d20000041c0c102043c0c144001607484a00f200d42d841c0c0c0c89040c2c0c6e5140c000300e041c44a80c1d03020310361015240034110402c0018a00041d4040324001d503049820706002510307541c0841c1290340440d0803050749070380c50300411150f285c50888464048115541c800130080390901080c02d4800540d00d1154000b0089a40c00441d0380156080d40500802d0b402011031000062405880c0d40d401c40903101d5444a46a0400036103101c0c03244140d032a49000000d01c0a4102450031200800719190b05a8241d0b2507c3c1c0080e5030703030382701100b154222035480d100c4010761010303910307040c01e03582c4004040b003501f650070000040180c4031500031030208100340e50001e072645024550300d4100071042c2020b0603c00340810820007144e5442440003806038240c500080c0342c0d560302c00030600080031000003c648400c500895002c02082038090401701c00c3d01401da47e002e44800010030b13542e00d41a68020804003890b0514681980305e170f400780340c3c008603a25180c01c15040603 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 19917929 1250 19916679 19916713
    0x50603010605040606120c03110f07020a030b040807050c0405010b120901090b0f0103030e1903080309010609020d1d0a0c03020132032203050d0207080403020604060818030309060c0c 80
    0x1c0d030b100601158100180302c400e06c0c11881014003c52840c10709001c0e100880c410b024441c4070f00c8894000103403000c9801025510707221500301c00785911403114541d0342030a09208080380c0000108964906c503041d00d070259400d080c061181240c4000c8200d9051201c00f1511f00701180300185a04207035036a50b600b00010801609041d80644080c5040d16000c2d41036080007400146000ca20320700941250f01e203604c1480d91285c0c0e4004036504103c42e03d880c0e848517410305001d020b0715032181c01c03003900219000e280c004650780010b80c05d0400c6222840a646008901c030b48a048400c005055080250820000341d406130303009210000030001424036010403601943c00c6000401e911441c504000701c00c108007810f5498818524aa02038116084110590f42c01090392140031070304e02c03020343c0104901d420010420706480155034014401a141c0b070710340c0002481d03094229207400300c54404a1106100003804001c5a004004000c040c21060f5031307400c0c160700715a0200b9541205403007102c0890100c0203131 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 19919179 1250 19917929 19917941
    0x3060d140307060507080108010504050d03050c0c0d0207050a05044a010603020103050c0c0d1101020d0609020306040506010c0507052202070c03050606180f070314010306020703080c0403020d030305060301060504 93
    0x440c43c0c0c000b510342000b8600414105058200004a030702d0300f014007000c501d000035250001ca00740e24022506686444404c2d4041c0100c11140d4114841c0c09881800c40c1e40124410064410603101500c840b40ea5008210698103000c545c840382c540c1c08400d0780d84000c00007602d1900340c003000703009480d00b0021000d01045100d0140344150240d545075400e10841da403500a407904070780b06000d21400c210848200903143c2d44142c54140c1030003c203c002003041e180a4054401040303444030201300c030681d070340c84100180d401214481d00c26440c100000742c07158051908156600d070880000c1c44c1d1507041c581400364001843c80c101036200720b010480a00d20890380001d02d403142c8980303100703841da920310310307245142c6080503001d0791041c80d2641008541c000c001500e66448a00d44030004a80d03116000150028041e001750240812030300c000200900c25150010001e561003a950399405958441903d0124041d07808020342c400452420580840c2c82500b02d2500035800400014406559600103011a12 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 19920429 1250 19919179 19919183
    0x2040305060106050d05131e0201020120070b0105030313140a0e1503010606020303151507080301080303010602070501050a0c0305030a0e0304090c030b0301060501200f06070504150207080303060d140307 89
    0x800001d12680d54217490280980140300403401c41401c0d05265034068502510030544410040c41d03075203840540e0f1003500403200b000d030b02c029030408280180008040d0b507440003030191403119401d4000500790074000110350382441c103180600e0b4118100b14004a904103070480c1c0980c807268002012416840402c0c01a010b07048002c03503a80d4204c0c00a05060940b1030a41c0f01d84103540051003005580b803081106c4569516088070701140d58200c1d401091b0003401200c4001e00758040100c004100780e43e0000c029410798a485c0c00b1030302140e13a243c004482034420316042000086032402d15200003402140a143c209540700404a20212701240003840d64005600c04040f454852003806412505881070a16a150a80003807002d24200000a40748901c03804020030549031851562500390000c0c0103250701d000c908401d9841c2c50600910080c0709800c540200015000621202d201c0369000140d50f10403100c645000d1030642d50382e101048280004a0000d8544480034111001e460209200801c400c0d8 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 19921679 1250 19920429 19920437
    0x2030c0405031005070909090201030603140607020708030f0409020a050c150601030c03050108060606091f08010608180d0e010504030b0103060207030e1504030f0311010e0f012405040b0402040305060106 89
    0x141c54081090302c0c00010046000040780703010306101900f03074840c3d014010381e135942501280580407440101c0c024030031544042c0003500300079104480f0340070226405003d0000c0f80d0884943c10740f64150349440e4410403440310401c19081000300709041460300a0071980c066070400d070342080120a901c0f03040014403a05100164200401c000d555a0907124242c58214103250410084d0304110409507203c10150005201d440c010500803003903651010101d548040092021400b80c489400103800128280624401320358843e0008a1081c00e080302d2500ea440180b00502210441060680d10380f040503401504101c5c041001102040402003001c0c001c40c45090010781c0c541a509008005866031140184103000e00413001000130342190540c1d059039002074032201021844e250956811b21100c540000700d50030300280d4143c0d4440441d42c101040b123640e000b8411a06881c041705a40000c440d08404280c0e50721800b8411824558001c41d4480801b400051500391685c8829140204c00d038440310000e = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 19922929 1250 19921679 19921687
    0x1017030d0903030923100b0105090915060c01020403050712050a02012307030203090f030d020a060b0a050901060f0201051602120904020c060c041a0304120309050c090a0c170106080610110102030c 86
    0x34108001c030000241e071260040000c01021f40c0000d02c0380c0b00e41865240728500000202e5101400d40303c00c54200b031402000715545103410389001c1c2c043d40191006403601d01403424009007640c0001c8031002945c3d8000054140d800c1c8560041d140310a0071a10034041c0d403544004400203910300402440c0c114041c1c4c0045403141040f004108081071500c030a80c1c001e0304024a8030000a4002030010452076000801141c41c10035040810b802161a900c12640300c1c1110000240c0550040c500c14803403052035009109036900d45400c0500aa0800100310050f070080c451f0090f403140c1c0d54090240040c00503c007614000300b600d03140c0d10b42501030756085d5078100c0000f802c02c5110107012040c0c2c400140382c80c00500318585900c405098101c148580b4080c107442d2380000b420000f062140c2d40b00094000d148400300c1c2801c15014004143d900c20740c80c04600381003200c40c611043c42280f0390403601d196032180c0c95681c2d070506008909003176034070704405d110340c580000407040b0b02030010314414200c0b01c45031915 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 19924179 1250 19922929 19922993
    0x1060905060604030305030c0f0904091202010c030908090f03010e06040605091603080301180b040c0e01090506030c0405010c1a090c040c03051510020f1002031017030d09030309 78
    0x40310000340506100d18001c000410000390400c00f07403a4407003603c0290544880050001c040d980c410341300082d40c0680b800c010001003020410300041c1400f00ca600030081011081415400c40e4501a000303409040140200f041a00d0151915101031202500100b1b28504086440d0715055007510111645501c3d80100060082c0c204010107050030141c00d140d0139946507455402403880f040c0203640003080000d40490f1220f8040c3c1044080c804054003c00844000c00030080040100600701400074203040b00005103880e040c001c0d02d0084980c0f0007034510f058501401540c02441441007141c00180320b0b0b5813000c480014001541c8114003c00142c1802010b1000704003c03129000c00c0301c0141440c2505001502d814103185510a0320140c510b0342ea1481c0e0402d090341782c20f41100100c0058030074003541810241d41600a0340c007682d82d540002c82d0300341d210190308522881e03031a0300c2c1c10154018808029060a9a040400d815000e03050000f0101d015031108a144140040302c4000360000c1c60b240d0340 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 19925429 1250 19924179 19924181
    0x4050f0606030d08060d02060903100501060e0d0b060402070204090203030409020904050c07031704150f060302030c03060405030d020708040b0a0206150f0325080604120f0906051204030c02030609010609 89
    0x1034807000803009410b040140c1c100241000d0b80180a0341e0107103228406020071516400112000140003d00303e440c800f40c2d41d01010040d0000340a4440001d50b00d1f610403000d4103005070084080d0b0340c004510f8580756140001e000094000c2041030780d00984840c41d001c00361f00c05100400140007040c00241e40ca0784440240019a18040c1254001c171804121600c0070a910416010300b0303403605412000c0036211401d055100b45032070b44000302002d10300004074031407490303070b50115085902c02e800b615111484042050b07101d0b42d04450140c0780303401c10000c1a141c500164000d01016209004c1c546c10503468038038060941e0001158100940e200740f061107a05545000b50200240044929061010f4580042a26003004078071501e81504400c501411036450317100b1603000341c000c1c5000c4540525160410310301082c0302907a403002196044100841c00c520440000d0b050b51490f03114185801e00d160340a510b100c80041c82541040400350f184c0006aa05000b903a0245142c500042142414000c40c10 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 19926679 1250 19925429 19925431
    0x90e16030e100603050312241e060c0f0606100e10020114040605040605130c21020d0804030b0702070503070314030c06040308010f0918080304020d080307030219080702151b0304050f06 81
    0x8040c150604000b4002c404d0110300720340ca21002030f1400d505111108050f40c018a1503034401c82e2b8400404601072007a540c0000b0403020800b1444110382a50700c8036410301c540044003a0307008002841d102e4010090b8100319082001c202c80318400004d01058142a4000e010426641180e520340c4640500060145901603070f42c001d4a4059120240000e0780e40340b00d900368152103004001c2908010710b0085410044e69088509d03006480000300000500d405211503000e4002101d1400710b03807000c2001144001111300030340d080900100f5200d410b649a00c010004281c0742c040391440300700304511440380b05003e4207000e1846600c88200315410008900100a465004812124a4008140341c4c90a0041140d8402d0390041c0e2070301e80d6511140042803040f41002c1e40038160300400420701c8036260789513008000e030310300b0b1842460351a00c0ca041d044a510400341e03180001030b40701c0220300550020040c10260402c006030b29000c503c0482100030381e0550803c81d404c2d40d82d0741118404d80c12200b0305100399 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 19927929 1250 19926679 19926691
    0x3050d020105060f01031a1e03010203010f0e0c0c0706080604111801090b0708031302040902030a050a03030f060501020307060507110a030201090204060902130b03100308031303090e16030e100603050312 89
    0x900c00c101c403203040240e5047e13008180c584111460b440740c40e015080a02134071200c95000c1c009564ac1d68540e41401c002c030741c040c4200511190300b000012020402a000da0f00c6035a00700c806402c03510315041044903c036030040c000380e90242e40c80852002030340c480001003103000c10300180c0000f908501c10000d00404869071010781007200800c040400600d466003103d42c1f21081c24051844c4541600106000f031149400094241c4500f00300d00c070600400003200e83d00340b0f2017580c0074491509006541403d40c0c5442c8109409640b0920a0754001400f9810642c4c0c42816841d00607020080901e0726894200c0e818800c0e0f0250350340d40d07102c4042d4201405404054181e044055140c00c580d100c1505502000e88203180f0014408004240c141130b1010340c100c0215042116036489080844070002c00c0b0114200c120045584e0382d20004c1c40d07807141540d0521412150924042c0c00c0c1010f174041d809404840c030180f030030340161340d014070030591184103010286000d00021134550002c00b07110b021340e5002400b0 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 19929179 1250 19927929 19927931
    0xe061b070806090c010809070b0f031005030c13021b010c050702010207081b06070302030c0a0602040503061e061c1a180304030c06050d090609060c030b0d0209160903050d020105060f0103 82
    0x40145810340090004130641d001e2074001c5060ba01c0484985c00c1c91503c3e0400300e010480001d01c86800e03910384000c1c60242c142a0b040c500500e03a510201035841c0c00c6c514180340c00ca038890b07254076080ca80d0f40d0701503c0076004181041803080c500c1c002103400c40d850b55443c4404030388003040d65015540d042202401800748000202607013109148059000000444828400c1c040000c440041620a2095900c00ea500108841035901c05252200281d003107070003000e001c3d2042400148161280721031580d0703500311450081c5600d480380014060b940e02c1480b20b6407004220032007908000380903640707800c004000352140003010b410519900e42502e6429070301c504461740184030074004240030039194022110306003801944c403120307650040058003103028050401407428105200788402508802100c041994080002c40c030820200040b80c2c108440294001d204400020003000b0020341142044401303040103540b5607030380e90340c89242866a02980340180d4441d014400130342000d0031460668002424 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 19930429 1250 19929179 19929181
    0x30910050103020f09180304090504060b030606010806060f0909010e04060e0d0503060d0c0e040f050d031413140d0201020a0f08010501050304031404170a0c06030203040f06020a0e061b070806 84
    0x15004495852406101c5e4200c60080745007484440c103c0003c1c00c080b00d081e00d480d16903030110f5070001c1804a5058034030074101814030a051a002c2152881160161120080c0d619810705001040d0010b8103200f01301c00d002c220844c0c80707070389c0c0c036484074028a88446102e00742c1c41d1914107281aa00b8100801d4480e078010803000c488035401006807a400002078480003c4070310b2500342004604520303404444051245402d000a02080310600301c0c0442c011801c5841c01417034503604034111503402031802c4070103ca05010684204102c0300e05000103018080c207145c0c5519009c2c4041c01c0c44243c041140150b036000800002181c1c22500e07031040041f890818035102e40c5480e00103062448001e20080c1000811503561841c48000025034020304007005103c480e0200c80002c00ba500d0035500401d44803101941300000f1018420f008032407042c0d40c00310141e400c5180d0760b07451002941141c1001c0050081000d003000c5991120406054072032440340c1e240d01c0403c4050061402e02210b41c00c01041504031034 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 19931679 1250 19930429 19930433
    0x7170c0307060e07030f05151f0620070b13050402070308130c030503030108070905090a11090a230f07030c021c09090c03020a0f09060e0d0305090d08030910050103 72
    0x30096801d480d80202d03001c1075440c400d00486007481074a41004044c03c415095190a0003800140d00c0f80003102091807044075295010307070841c0002d4801141041c0c2900c500180038079445150300d5102402000310602c04562058001ca0400d4002d07008010741900c007042d080f0580c41c09501c02001004203550841c0303040c0d6640c030b000740041d1005000064206032000c00300200710101c1416002180c0000c00d9980300e5850b007400ca0380b2669030740304561340c542c14400400c0b00c4100210381c40004035808000d850032450314105001c5100c0f030007000019020350720143d40d149000c1e02904542c0022028444440d189032481d0510903482000d04400d08240c500030740e0030803094001039003031003484521034141d0030204a01011514101030f0380011140d117040c518813401c0070350150041c0000d4042500d50300c2c0e1200404004865002003803044000043c64100321000b0b43c02c2c800000840c242c081d10780030789011904e001141c0c03802921282180e0b03d000010404ca039401c0248041c0380114600d02e0180000d501d03603 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 19932929 1250 19931679 19931683
    0x20c060f04050c030a0305030601020c040e070314030d0204030f060c02030a08060603130807050102090307080303071706060d02120601120603050c04050c0705070611060703060b160c05040e0307170c 87
    0x141542034203000340e40450140082008040e030b444500070b0440303514504a1074002c0043d081564a2070140c801c00e100701c4403611303003400780d0303160107107580f000b4660180b85d40c03605441d80c5148004020580002c00c1503042d490342d1800148043c5004030502160040540351034412100761003590400c6400601449203940c0d0b00400d407642000c412661151217032174141d42c501c204d140080000b40310b280009107030410004d06401402220b0011015502c1d2180d8882d030594591200301e441b00000380f2a980d811014034400c10f09182c10550240c1210700b040065200c0f80e00720792080c3c0b0131490005840e01040440d41c3d10461f0f2041601a1103400e0186a00d10f9075060b584110294099101e161210b0001e1107401d2103806980b41c503500301e01161481a500c00e40940784c203a61041c0e444007070060000040c1d400303009014480c01c0300d6089515038a4403001c4c4595040c401403880301160f0200c0b40344000210340ea254010b5035002c0301d6002c00f4690701c0d00d0301d00d01001d40138401c030400210400180110b68541d680 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 19934179 1250 19932929 19932931
    0xf160302070623030a0e0309030a0b09071202010507080304030306051203070606140a12020301090219080c01030c0503060904050f01020307050405010905030106030825060207150b01020c1513031e021003020c06 92
    0x94040e001ca07004445d10b00ca1b83c00d500a10441503050311486268409108410700c00f24011a051170561342c445407524803c00e04540d0035900680402c40401803080080c108100442d4468002e141c0022510f8481c000110103030344568500460340d002151b9041480000d01c10040240f890009550360083d002e030100369040d540c3c0c0b06502c038562501ca410001d5440a40004462030b44c01031030080c2c0c4146000502c151001039001d1640644900e024120a550003440350b132044007840d88580f13003140e50f540100148180c000f44101d03414005c00d64850b0104502740043c500a205688a43d0745480c10700e030005240015603401140700740c0c1000c504101245d0030004807048041c80c41c1040035507805040c0c4901c1c607190341507002006030384001426014002c107088080f904485c3d64000707001080b03c140c0120b035103405145d00a90b221b02d011000c40900c000c140700411100303025002e01c01c1899502e484000000600410304082d0140c02050b600842c904100c49406030310440c03c0441c20305000c080300690f1184 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 19935429 1250 19934179 19934191
    0xf0c010e12030d090c0e01060e010909020a20010209030c0d080d0506011e02010207020a060e03060a050619080c18040c120c05090901091104060303140f16030207062303 74
    0x900011101441d20240101c82d001c101058003805206954036041100f54030b10310400d00a90f0b40d0000100b4550722502074411100c00c160b40b100f001070f08100c415402948040c0500342404240443d030072030350b0050942d40900021a0000584594800c07081c1810448602e5500d845070340441200303400120554155102074400d0704d0000340f20355525005884071303c030003000c4c00808442d41508810301c607070540042160342c0c401c1d02c4038200c0035038450041d9403c604601c0d071070764590000d1300043c0b981c0d11701d588502e81c03028000705540c500702c1401d656031211000582184206800c541185d030700c64100440480c00c448105044060b0320f2a054503455a0160140541c072044400c400e0741000307000000c100d000c0075000040c051a4541080c81d0000d000b0b1001420440c1c02030348009040c05c80c1d01c0e1601c41c440c02c490305504c1c0c050a0300160080f0b10b620754400c081280280750284071320104010003048141c1c0b0a88070350000c11100c0d08081d0040c01c0042c080240c0305001240008001066408034107a9812071 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 19936679 1250 19935429 19935439
    0x8070806190e0f060108012a030c0e0a03080c0d05090d060b0112020301080105070201050105060903100207020415031a0c070c030b04050a05120703090e0c16080903010f0c020f0c010e 80
    0x20380341c110440140002c8a0300d12094451804041c2c0c1c03507440415110f040b1803510f00200315207680c032401c1110715010f180c1340d00001042c0318086000c140c000d4101c5004040c6a01e080c1e070851165500081d07402050750425201108041582e1352020000c11030880080000c2c104281003204450000c0c15055282c1001022181c071180710f01b602e64010b1206001019080d401075440b5078489404600a100c11a103620056080c880000303442d042c40411504003075809800340c410311140342689006907112200c100d801550750901418584014400700000c3c511a0b9080700700c010209840410405016185051b040000c000200000703540e00a0001280d40c03084001038580d41d903040446c1060202c1d140540f4034000c2d00550640380d180300c4014251203200e80c0301c00341c1c42600c80c0c0c83e84018410484030031600781c0c0b0401c20442ea0400c0d01c040221a913109043c840d25100b49800402d0035501201d041e182c0a07904d07030311815005038040c030030b07501c80710090303c0200880c44d61b03800000c0c240b000f00c000c01ca02075 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 19937929 1250 19936679 19936711
    0xe010b031f08030d0504110907021c1b03050307020706030b090a0c020a0b01080601050a060203070b0a02070c08010c051b01020a020601170304050301050408120f0903030a02090109080a030903060608070806 90
    0x2900340c030101c64010302910041e60f4071140120107100240908890817200341ca103000c21003000d07181003a0403500680036540200103006400002038890000c8100002c1805220180c102411140902e8000303540c0c07190340c0b0b064603424444806407a040c1c264004405140c00d100081045480e0341840307a41c002007207000441c108881400c16400c018540c1c101610703440e010310000c41d89403c00200d05040700d9042e900c0349892130f0740304800c031307168000d2880c02016030a500d0081107410b40c041d00078100c80c500408036403010947d1205606c0c00c4504040007600490702c04120b4450848524034170460102000c0000c1d403900c8500c51009480b1b10050207401680903ea0420141503d400c00c20794015100c050000c02c8035090a0500514a0300024174114103854040005600d410719401614040d82c186801181161542a1070b500a50000c900050400c1a900b1000900e01410840700740050302a858481d00d4600318200034080d07c4054005515035070040c0c500304030b41200000da03036038010142010f560207 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 19939179 1250 19937929 19937971
    0x212120403050714010509060601030e030304201305010801060906060507060f020f0a0c02090711060f06010309081602100801050609010302030c090301020a17090601030803010b0c07080f010f05010e010b03 90
    0xd90f000303c100c00740440b0540071942540c0d82c415400386d4010440a4212440c031f43d10755004400740c1e01c0311031040540b50000d00128001410404c628146810f001400b5103084040340049403414051980c900c41c40d98907003004001c4500203208100140c010380344140f141508150020305a486428801800c03103550b46030720703030b00c0e0602e90341610070b0b4529441009035110181000240409088502a4810084d40011803440d03070203041c0c100034006804024000783e903608042c8001404000382510f062648404460b8000303051540184000304610b610380c0041034107401400000c441d407000d020180a00303880140807994920b819035030400320901e0056520741d03691135410518043e86422541541c004a04d42030b0302500941c1e0218204610b03440a01d059807000707041a40c5040a03c405894004c08100600180003400024510b1480b00b4084544456440c407443e4038220001c01194010b9560f40d2880f085a85e40c0d0080600401c9840e551850f82d5052000c82c0541d480003a141500070384aa40d00660 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 19940429 1250 19939179 19939187
    0x4060e0d02040e0304030201080a0e0a1217100e07021b0607080c0a060504150902220e070303020304051203120604090f0f0807060e010c0c12020c060412030f0212120403 74
    0x1030950340608140001d43c4000c6441d0b5894004c0d0000f280440c164000044100c601449200350b541d01502c000e02c640c0303406469030140301078081000c02c200614417011680e0110080d0266014410b6284013400c1e440c0303810703809406c0c01b01c040c20708003c5400c01c18036150b40d030441c3c103940e56a8040c1210440c0da9007015107003026051150701c40c240e50f01d0080041c0b80c401c0c4182075100320b1086000f01480d8480b13501c025509001c40b140340000940c400780c0703010652001c9503109000c4a094655400002c0c000c1d0700380008514040301b83c4e1003280181e100040910050800c4068120381411440c025401d01d11403e032008400c000c000c1803107001300d0b42c80a108040c0190032503612280c0e90081c2003182080050300f000c83e01540703c042e05881d82030802d4038071000083e0502c2140f00810883c0c0d11801050001c0da10300013206a020007450441c854001700390030541d40d00340100010120303030b01d00c050094003030b00d00904801810100b04096406ca080102e400d4160382084521b00300341240401184e90300da01d0203072 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 19941679 1250 19940429 19940449
    0x80f13050a05010c0305011205120d06090e0706021009020f1201110f04050a0f05220e030f030a0507080403081308040e070507110a0f030f021305090a0b1b04060e 71
    0x2808034030031044404184a81940601c0040e07249a17400d10076a0b0704d8400017601c1c40002c1d13100500c11f80c0300c1006648418280809041c142e03c502d500410190740d02c5100600341c503100504c0e00d10503044800100a4944c0400494041d4102d0701810300010300c00c0c1d0001021034002d00c2c160f60084400340048280c2c140c080d440116131943c0c50f14820f0f1681401d2444600720b4105004090045c80740f1140030415204488034281140c00027405080590a2000c0c071f002c2440d00ea209101020b921200c0c0500f00c48030030300241c606072441c103c00036103918141858800f51140a040d400030f0010090622003c281c1c842110341c0e10102c2d00028400c61500340c0751000e541e204903440004481c0d075100511404551050003842c2080c0900d007000d0071002d4002c00c112003100a032113030180031240031004000080d040040343d046107000a0000501c50059549841610400c40d19034500760060480d01d400c0000028441d60401040740311200074682011819225100d40c1c01a00c0134098900481d2465664a00c501 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 19942929 1250 19941679 19941683
    0xf090402090a0e0f010608010311040209191206140903030c0c03040906060c060e0d0e01030e15040c051009061d030c030f0609070509090a0b04020109090501030c18020a080f13 77
    0x1424010760b072441c1407022098155a54200d84d82004000160341e44181046030603282c0103420000038030312000403c8001d5200c4055030b5040101c8400642228401006100017440e030200c07180d00b08086440c080c3c084840d212036424086000d0424403c100e43c00009803a440782164800c550384462a844c040e1850190f5030166a0301d5060030004101e83d03600500319444680310f51301c180300340030764010100d2700c66143c04075510028004000c480c0c81580302c0e811510166121009440841071070060107882d001d012102038540c02c41c804406c00180c00e144600c0040c0c0005494040381c103e00700b000041c040c500d000520300c0100d039041c0c102213640d5401e002580a0707180040403610102c00d030784000c82e1249411100b0402c64083e10034002003604001d8480362080350000050700740804582d40341021520058000d03410009041d1020400c402d2621946011310300034070120741030614054003120208180140ba6000b00d0050010201c0150841c159a07007221086c908112070b0756400c41e90319141e1250400c0 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 19944179 1250 19942929 19942939
    0x402010c0503131401170c0f0c1e0c01020313030602070204020405030607080601120b0a0e04060204050306010303031a010507020609040b030f01021206180403080a0e010219050c070504110f09040209 87
    0x1143d00c035028101c140c8400c8810980408060030040c40c01501c000d1044002e10030000003010005040c81c410000400601d04042142c43c20824009a078515200ca0342d41c11000006003280030301100d9600300555100600244000d614185000c0c074243c02c410300e6440300400c69600401c0b42d10455a5030740648025000c050b044844c02e1801c01c90040c01c001003582c180303022801c50004021482c006010752a109440a000c4132556860b042180c42450001007081c0d8006030309010104595500340942802540669000f140614813150703d440316100307a005460522034100901c0300180c90b001c055421008045800162030410400413a041c241c10b030b80310031141d510028000590781080410103014042c01e0380d1956000214010010100b01c0c1520040c000c00c90f900002030700380d440c03074101c4001c442c880800582003241c245080e1902c0300030a401e16010030004280000003c10803c031090080c4406c49090102200c204840e2059100d41c0d800d080081030000364068807034445030100c03402c102014003 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 19945429 1250 19944179 19944187
    0x506010909020a0e01080a02030903041205010609110307080901050105090a1a040204170f030a021207030c021011060a06030210050904060e040606050907030504080306270a020307020d09030c030204050402010c0503 94
    0x44004c2c01483c000c1481404030f400c000c046000071906100b541c0c807540e00d0350011803400742081030401079445645000c03241036403205070120302c01c0b80c14003400009411586540391641008440038000341401006e58606038501001003040380d0304c00c0c2c05240c00c48910040016891003d0560810415601069075081800041d000074802255076a262043c0b0780107003503034400044000860f80702d2054a6031007005030311140a110351000150000d20220344603081c104c190003440c1e0f0210b0821003400020301c02142e0803e84035031005106100e207561040c0150000c02213103007140d000a8110701d140d03040c003080040100d500030007a11150300c208080e11021810042c14940345c6000d01c045d020600485000e0181100841c0886029024a6002c0c1d80d121807014115a6618180300545000c019021046034000900c5410144104e02141c010080c03828003599900e417014000e8076004c80400c5040410040000410118040800307803419290304440116054460b03000498110000c00c502605a000c00a = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 19946679 1250 19945429 19945447
    0x3060d1202030a02010b0402030f0106051c060308090a050103090312020c030d060314010b10050301031106070206070f06050903070c031401060803040806010f060305130308070323060a05150d050601090902 90
    0x40076200a0f4102d034024889185414140403d03400b090300c1d0103001400314001800542e000ba0007030030113a007071000b444905032140032000043d1313003c640c0103032009180001c1d1092175041803500080a400203007402d00c15038117a5580102034640c035906180042d030740812103003c418002c0c0100e902c0100151402e00031a40c8900341008800c41c0d102494a03550310300403540c60103080440c0c1202c510b0f0055103416046a2075034460218201e0101002c41c2d00c500c0070054400182c2d90a0043c096080c018000c06507007440310315064045405c003402100c1d00f0781c000d10000c0005040c4002c07003420303245c0c02001c64814540b50185103025019a40110049001c0414042942403002070b240d0b0407a50340c0c150000489a1f02c1009900303e5900f80d89454001e078440c610741020074020304620341c02070614500010600c140348006036803828940d05113800e144510003840707828580200583c0150a08684a0010202c800f4101400d849080e64242180b6201c400250250b8042c4008400420a150702956100790030 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 19947929 1250 19946679 19946683
    0xd09020609210d080124140d0207051e0a02011d060309030d06090209010c0308070e1c0309050613031e020901030606050415050f0d1407080303090d0804050604030503060d1202 77
    0xb580803070010b02c10030310100319035442081414100e07102c1d09400070702c070701281c40e12a103200280d1040a040c000c8909416071f440324000001c01c1e881041c030600580b20509803800034103104a03042c03030700c040300c0340003030801c40d00500810a4a800c550908004100c1119801c584809016440324103030720400100030411032440100082920301c4140300c0c100207880c0c903580040200c2c000c290820303002540007803071040001d0050a680e80c0005944c208400b2850030080020100725044401c00300b99900c080d100010940c126088030003500040f10350034240149c40800d0310090361644009041c04038800404403612030301c004262441c90b000790146d900c07981c40c0c1c14020060001c170303c10a80110b00e0070221210030408501042d041da04000c140f41d001c2e0311040104034092078200c2c02a90b0586c20000020410f030010011703023005003074030400782d03480c1d00e0070041640c00c1a46d4100804180600c40c42003000081700840c4050f80540d0604240b6104cac0c558078081510140403a900600e0352440e2030f00050b0050f00 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 19949179 1250 19947929 19947979
    0x2030106060201050928080a0302090306070306050406090203061509010c120c03091202030714060d0915060509190515040c020708061006020303060409050c0a0e06040f09080d09020609 81
    0x105100321021445803004661b0500f072404030103219420240f072644000f40c03801004080210541c680507080c400500c0001e0b04102c0203a41d032f200881e80d141c404010b2402c20380198001414000c0f0210304524041e00030892101c0c807040c04018010340000d5840c466805030418070300103600710a480b2002e06a61202401c4c069103204158040780c00d4400c00110014003041220809502a0182c1426840c04210080601d44040c5017030380b00070f09019444456130107108030a10380c0c0c01100800090103040440100325803a03034000c075004045010801c801e10140c5084003002907800c440c001076940d2181400c1000c19030f1045d03181e92043c10180f002e0210303a400079202041d600e0540544807261215080703009901000d200701005a042840099814601944040f0030940201e06481ca030354101d0700040c80400194000e0a50b0081407410b028681c10144a5042d903e0b890404c1004080130316100c0352528001c03220410761087e160407604046403181420707214042000750610994845030800081e203424 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 19950429 1250 19949179 19949191
    0x1205120106080405060c0a0210050a241403071a07020a0513090302120c0703020405060d02030601060504140f0607110a150c06050a090201140c010204030b011203020f01091e020a030203010606020105 87
    0x101d179501003241c41c450581141d90a081c940c00416400040d00b07543d0004d428000d21340c4108035503442d5116641100303885040d400e4181c4e11541440c0605240660090030090a83c480c080da001c40418841024040c1000074000c40034a00651104800d01c0041c120030240e8000c035801c60080e40d40c0004c0425603030000d5684620940039601080460086e100080c05460440c040561103c101000076040c142d00c59600b00304003804007402c00c41c95401080ca800800c0e808100003640010b0100301e540742c418443e0007081401c840e5035581d02c8180c400130381786004890001e020000250720820301070350359401100080c011003060390341c90307500141d005c0c4c0104694031043d1401d900b00340008105400b60304c40d4144844d4142c4840740c90609200c1d550100b80c1014401964540d8208004404603143c040e58500808240710115140b0040749030003818054910541102681089060f200003441c1e039a0400c0070b044c00740710700c9a59140398000181c00e503046600107909546019000300c0c02c6541034205500c03400e = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 19951679 1250 19950429 19950433
    0x80906070c180c05090402090609060c0a0b13030203180d020d050706030c030501030b0106030905030c0f0c01090509160f020c0909060708160c030302030408070b0f071e0207031205120106080405 85
    0x250b0020b02003000d54840789081d000240041140d200c25180c10340c05800c11003000780821b814030074040701154059000300145e20050340304444000c20014119412544803101102000910302c01e0760f4065902c1c001d01d1141440540b0f0208600003a4032881c1c0060313212a0018540c10480308541005c40e01d0302018004e07140000c0c03d001e000f03442c81c1d000e8002d140c1200d03445031509101341e20b4010101d00400306001c0899140c08100035078480c1c0b410800c02034640300740d898060103d0b605190000340030600340b03500050082c18000208804101040d000340300100c0079040c0740301c480e041c001d402c078100030706441c0055000b1a50001e0061717040780021094410074054442d940310f0b482d800b01242c3c0724002120001e0000d07a204281c3c4001074800d8010315007051147c51042c2c1800c800d680ca05140c407204660b4040e215014608010700740d90701c00e44d1200d542c10f0480744001b41c1d04110f000251030344c0041c00081c141d200c1040518125911030703c00ca80440324032141340394080d40c660388000e244410a039030581e43e038 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 19952929 1250 19951679 19951709
    0x1505010201060803071e0b01090510050d0807170d0903090905010602030f0301060c0201030b040608010902040510061d060d060b0c070b0f030a05191a09010f0b03040b04080906070c 79
    0x554014810441500e1500004505208140da551060040007410700c0320040e018010080c000707142041854040c00030b50802080031300e00510340011201e5103501040c490903200c0071920108140c0821184526085000405200c0c0013281d81c9002d0710a4100c0b0a001d203280c80603400506074852820310546102c03a800780166660346000700ea9038040c400d500702d1441e80810040141600440794055124418100403031281c061000003012210700303602082459458440f80b0085207000d00c01d15038003000b8200201441400c0a0004003407091070882558203143d40800140300355a0a015210018994041400016250580d4001039040080d201d40d0300d114080740842c81d0b40e070a00036100350100414009003140d0710080254007034440509001034132000c080004401781298012003000b80c80c1240b000085980e40c105100c68100c05901045850080c55002d10a800501d4102da0700260003180746e0b0250349603818154030504c500e004065104800141030710403c2107100c000707021245150181c07055 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 19954179 1250 19952929 19952939
    0x8060303030103020303041502100908180a0311060f0c030d0c021005190207060e100c090504110702012d08010302090a0507020a080d0902060f040f05011b06020a03140a15 75
    0x6240000e010003541754000340001d0002d082c11100d4403000100520444910a0f03688111200710b910f4400203880f0444005000c006146491480b08010075080c0e4160381140c0c5580c42d241600c20040005030711a03140001d243d20141c1100c0c040d24840920001503a90f00e902010503a0000c064600d005005801080111140c8001600c1140d10855500110788409600000803800a41c003620b012100d8030380c1c6204140000008000c0120000340c4a0400203048900c0000903110050179807049100b282441c14940c004a480002e442d95581e080c2411603500c4000c0c00000c2c0b940e101d0701c840865101102e0b0700030700c0840c1d0183c5018101d034000e581c3c80c205501d82007200c4090307805c221180f5000d42d200c80c12010006a6503001032400340702d0880c00242e4080240d002070a21f6010a081e401d2040f4082011f0100c0d8801c451110300608090030003500841101007504140448004007400c0250702290080c0e10a01917007081e070101c01c03c0c012034206403516040c0e04005005062020b415002400c00101e0 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 19955429 1250 19954179 19954183
    0x31005150a0906050f0a030504020d0f05010b040605040b030a080a0302120a05070e18060f03030f120405010c0e09070c050309040501030f0501060503060108330907170c06120601030603150903080603 87
    0x45c000700c0820101e04d4001c0610065020b080c010308102d8100c010440f42c1804074003c205030b41c0000344500c0c0045242c3d00c024040009980403500210310891400d495051b0681e800100d68100607070002c40552240d808410940c003e0180020281d40c1c0c0389044100290b0341225030060b4800d1003640c4419001c02d1080d814400a0241200e01502918070513020491a00c4d269444964013540281100e251040b04052040c40d50007043d030840307900e8459014441040720a010320600004145031111045500c040040c0b52644060100d1302400780d401c035410203004041c0121109404054410710407960b40c0e2912802d41100b0b44000d643c01c0d440c0400c046041d203000728206040703401c01802040414819900c29030100e40701c1c030300c0480d284000c081d00000d81c05c203840c40902c10002c080241c002d080c50512684904d42541c050082c098220030342902e099690681980c03a14903008100340c010740d6482c80140c009005035000078000303481c612448401c0b410141c000c0380200d846039484180c1c5807101c2081c95 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 19956679 1250 19955429 19955437
    0x203041a090a091e060609030b010504050c04051005040803030f0133030b0102010608010e070501020d030209031b0d06091410050411040b0a03080406031d0303040c060302031005150a090605 83
    0x660710a807202d81c01c2103a140d1039004020445070251a129407514040020411102030ba0300c14004548808030410910584240160041c070b0195802d003c2440c2501a4140511450203030a21507405102603c03401032246050780c0103000788908680c1d50b4102b40e07612809000c4244079445c54281d01d2042141c001064955034090400ca000d00303078403907114070031040e4040c0030312840ea541190b580e000c000030094800d0003564903160020014003282c0d0308100009003000f03002c00701c0c03d041c18010440d914143e2000240602c2101d610112400b010300d00500103806801400307000380c407450500041e0014450350301200c0044039000021100c4401d068408182980e400304c85c040c022440c0705516285600701078101d114501b4004003088400c135100e50318040790b17030429001640080d41d1924080322003840a0115030003414a03400560662a15648201041b525801240c0030540c012021401c0f0941c0c0c1e50b445009001c1c02050195071284409103180c5036048880403000043d004880028880e02038400c071 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 19957929 1250 19956679 19956697
    0x8070e100501170705090111010f020304051501060c0209040312050708070306050d0506040b1b03010b070302010501050405040b06120c0604080f0601050108040b0103060506030c180403030c0f090303030b030c060a0203041a 97
    0x891004d940303000c3c00399480d4100d21a814140b0403c1104007113a00d5003032180b6120070311116001030305ca05050522a00c0c1c0300ca03124039440d440117404014400c00b50804070079681594100c40c40301f100d584900c2c089920341400d1141120003401c10f018030841681210b48031348581c04542c0c080050a65640400200054258015090b50454004103001c101c6d080030f003c0d84402010703107030140141c1c1c21082d80c2c1c50b684240d10801c00e80344049104010180d081c043c0c10300410040720180858105901c42014202000d0201449a148504443c0401c041400448210712000b0320440c0c0f174036a40c100c42c503201e92504002005030b010301070021407158018010a8001c0f40c004c00c102d000d507808c6547d560001c080c003504103a494450b02420b800155204072114480550900c10040c0c141400d1030050243d5000340301310024402401c001503051584491030004503a014074003c915405400c000c2410300008441868100310700089c0841c503d03400000500850790030289140507800d01c2c08a02c209409401c03e0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 19959179 1250 19957929 19957967
    0xf0e010914061605030406020906030103050a1109010b0901080604060305010e070e0108010612080a0203070c06050d050a0c050306100306030f03022a030a15020d06090609110c060708040c08070e100501 88
    0x3e940000344284051340c1d1140c85248010725005604c0002000358109034000c90b555403044100108000c081c83c0c0e81c080648058450030200d5040c0a0343c3d09103802903500c00f504001c45040001c01d1660b554203c40001c40d040300003040b40101180704a62203c1440c09180b40d03006010000007002c03001445035030111040b510382c0c17102c0210305a4814032264040c00314081188800e02401e00885c0c010b411450080a581c0c40c3d041c1d40342e03d052900b80644400414200c0350340c5c51301c0801d050b126040000c0700c1d80824120340c21060b169a00100350001c0c06181c00103401d98550704640d1007016000600058500d030410104d844a110701d030a003586140f140901079426400000c60340e00001c1c4c078802c844581300c070428009410062a0300c0d200303007150003c1d40126251601ea9208002045442c8250024595010307a054a000000e5401a03500c0c1c9003d806e14041064000008080c04152116100504010002e40c0c01d05903444541141352081078171501ca214068405c001070560050010001911007401 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 19960429 1250 19959179 19959211
    0x60102011a03060606070c090e010501030201120c020a06050903040b030405030c070f030c05100e03060a0b100e01050403020904030e06070c061407020915150403080705010f0b030709050a0f0e01091406 88
    0x31700c00103800c0003008070f500308582c00001c61050b099000310382c076511b00640000703890340c034500006000385d100c031010b100d40300e11b041c410001956001c034800044a4222070041410b0b10b688040d0b52652050380c1c40015404001300900042007008002403200d042c00c20121850b503034656050038590784051200070901030003400e003041320f400c04030600200383c1040d0a00601c54080c0c00d02090825200f11858089181e41e280b02480078a040d14504400034954544100030608100c000380491040d8000688030311514800101014801c0d00600070020015146684481c0340703240035101100940070300e20103c0c481044c905e0350b001d52581035030800c82d00186407400c0c0ba102c41c00c00007034400d80308545a0f081080e02c040820513410201c000c0c802140b15440e150341c3c840d018203001b0300b1501c01902c444940c0d1f05051380c5d82e80e2503400040b403405543c28504002170b90781390840c68000600303c14510303120003030400100d1403c070300c81980f00704201070080402c01400c002d86520161101e000311492091260010 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 19961679 1250 19960429 19960441
    0x80f16060e070510030b0307030f0506040201140901120f06080a0b0103060b0103020f0702060a11070612050c03010f05120102071e110d0c140307050303040f18020703020d05250605060102011a0306 86
    0x5081ba0035502c0e00070b01031b00e02042c0c032600c8021701083c00751803e13603465104105010841d640a00903104030104040d1041c100114100001c241031040e18004403407549586182420300860b600000040000c10112060f14805142032014800c00348400e0f165a4500b815580480d40280211781102c40e190485c54030301480c607801c11490740c0008a04034104244c0850140b034100003040305001034200c0e510b0700f10320744075455200c00641e0740040039560f80c49000d0004101064516441b1000c0d902c04858900b402c90382202401c0c0240648000942034900036203400310f0060a100b5510070450190641c0344002d01d09109201d8140071180c40140303c440d5041c400c0000c12130240e0f60002c451801400e1b07508207991413002138695000341d0425080c07110144401c00002903107500c8400c0010500c1c00940c2003a0140e200a51584501c0341c03444184000059034003e603980c124454201d140c08152154840e29044c144080180303c211015405986414503041c1040c44000000710700c100c00030020051542c540c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 19962929 1250 19961679 19961681
    0x9030c060708071a0907060e06161a010f030213050f0606030702030408010212151504061808011401080d030b0d14010e06070c0c0e010b0a0804080f16060e07051003 72
    0xd2031041d02c02102c180508070000b10300203416912000c010841a00c0c90600c04c10305070912800e54010400e0080040c2d1241060319003506449101941004000c084941401c05038442603450b10641d401041d90800401c203170706124240c0094a009130741e0b908024100310b10305c40c12144107a502c141c098203100005111403802400942c1d01080e144144c0f810036580300710160aa8204544080050200d0701c20404100d007030349007a091103001214185281007800e03640c041140b007035004d8182000302005200040e009448200001444000e0082250100325031a00314061002e0044600d640103058895654034424000c42039070002c01410348104412540e556400f511000650320029520f070b0000a040e40b006001031780c410680307601c40c3c0b18002940c3c60b04000119a076003166903501d0300381005204201d6407070305444010304107080090041d11941407002140c0241d05600000c40000101e014a100070b400016207820700c601c2041c09a0040958101d4850701c2900506030082040c1e416001e04901ca = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 19964035 1106 19962929 19962937
    0x180307050a030606090b0d02180406060e040b0403030f020901051b0a0b04140c0108130308060d1205040f0504090b04030f050c0105070305010e070804110607060e0601150906030209030c06 82
    0x154001a190780d540b5168200069010001038104070710340ccc1c042009440c400c094601980340c00d2a040620302c604840c1100003a040114000300300400b4025101c04190584500e0308011a908079211036085014040300540314414904000c0743c460310030b00b0f004a028404e03528501c0c44d0800d110323181800380e02d5240c0c10072020500b0807507500d1020071304111117a850b241c07149158035503000141311000c10070005804480c202e0a010f00381c9411500500480c3c03425188080314540e03a20030001124100342014040d20000c03000200000e04c5114000c650301450b0070024100301001d40c816003100d104888030404203649030010302100e1401c400c090f60004031440c10b0b09075460f01c1d0356209260340c1c0e9620924000c442c085144401c010180c0c0143c40740310401c008440440d83d50310014204060081c1051010640c81000450401d01c240211030000101500500c421940704051003a40d80c4 = true := by decide +kernel

theorem cover : BRFrame.Cov 19784179 19964035 := by
  have h0 := BRFrame.cov_init 19784179
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19784179 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19784179 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19784179 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19784179 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19784179 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19784179 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19784179 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19784179 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19784179 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19784179 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19784179 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19784179 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19784179 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19784179 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19784179 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19784179 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19784179 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19784179 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19784179 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19784179 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19784179 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19784179 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19784179 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19784179 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19784179 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19784179 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19784179 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19784179 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19784179 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19784179 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19784179 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19784179 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19784179 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19784179 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19784179 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19784179 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19784179 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19784179 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19784179 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19784179 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19784179 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19784179 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19784179 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19784179 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19784179 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19784179 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19784179 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19784179 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19784179 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19784179 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19784179 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19784179 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19784179 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19784179 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19784179 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19784179 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19784179 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19784179 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19784179 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19784179 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19784179 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19784179 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19784179 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19784179 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19784179 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19784179 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19784179 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19784179 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19784179 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19784179 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19784179 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19784179 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19784179 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19784179 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19784179 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19784179 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19784179 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19784179 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19784179 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19784179 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19784179 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19784179 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19784179 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19784179 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19784179 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19784179 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19784179 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19784179 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19784179 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19784179 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19784179 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19784179 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19784179 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19784179 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19784179 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19784179 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19784179 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19784179 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19784179 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19784179 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19784179 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19784179 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19784179 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19784179 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19784179 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19784179 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19784179 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19784179 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19784179 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19784179 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19784179 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19784179 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19784179 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19784179 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19784179 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19784179 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19784179 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19784179 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19784179 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19784179 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19784179 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19784179 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19784179 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19784179 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19784179 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19784179 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19784179 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19784179 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19784179 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19784179 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19784179 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19784179 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19784179 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19784179 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19784179 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19784179 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19784179 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19784179 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19784179 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19784179 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19784179 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19784179 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19784179 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19784179 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 19784179 ≤ n) (h2 : n < 19964035) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
