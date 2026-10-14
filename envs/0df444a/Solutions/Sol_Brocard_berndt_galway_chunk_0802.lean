-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0802
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T22:53:15.56019+00:00
-- url     : https://prove2.me/submissions/b3d7566a-69b9-4e60-bc6c-dca53c416976

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 144064748 ≤ n < 144244604 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 144065998 1250 144064748 144064763
    0x90c0804030f0c020301140703020d0f0603171e1306030b04052a0f031819020d0816020d0819090317090111071202090106050c070b0d0f0603050102030f0603120403 72
    0x551610201c0d0042030900340148012107000300f042103550b4142c005240f0220782020500cc5128007034041402e8801e24000200319100c031102044600410001401e1038003994840c0b0780c500e00784142c4130400d552158154030f800840d80313407040c4013082c0c0502901398000380030b031420801391800f2180010104240103440210309080c42000303805150b24001e50300040c00503a140c81d80c0e42441005810000d1513440b0360344c02802440082d03800c0030000b03007a0000b000e801420071103c0c2c00090b50303612126403109181c6000f0880d000e103690007607103507011b044544604c01c2c0c404694a5203608590301d204103a840301c080800c000d105080c000500722440703020820310742c040d890341c440c4610001650b100881000b005c001d0f10401c200010102101e14212a010303000756603140c0544d80320300d001c43d05440780e14108111540201000c1005140c0400103060f0210034400008014159200d041d0680d90150300035100b603034001c001d0000503005410641d41001e4102c009000c0c548030418090800d0050780310282165 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 144067248 1250 144065998 144066017
    0x61b030e04061d011a070305070f0201030e0319020f0a1106090d0b160e2b2102030c0105010f03030c060908040b03160e030d020714060409110301090c0804030f 70
    0x54035242c0102000d8826141d10618000051a90805829003445040360b0a030340d1a001c00e804900100498180710b804d0ba803241d10385483c60b12503407440b10060000301e04040c0d540c40907010303100c02030001e0226200d0040440c1080501140001d14180341440c10700c00c40c0d0031041a007070005214600c000b0321000306907400d640391300501d00042c1c001c0c03807001800340c20300d41c8403010454403001c0c04000151804142c0c6030415000003020601071115500101c000006c0748648001c0308141e01f540b0603c101c58414505590094000070f00031201398003c3c003003a40513910121313511030300701000c2c040c5501400351040e000d04000d1a40c0c0b00107101c1910400d0261002d40d07111358500a1208800449014000600b400d41c5e1702d06280c088002aa03200105400000e005041000302c9490b001c03602c4c18012072030340c2c0240740d070030b081107084021f03045030019640c2d000c03604000008010b66030b402410a000c0708213101580725891f203034100b000d45070300d4400700c0200b069040801c03001a401900d0009010690300c0d0907e01e0 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 144068498 1250 144067248 144067277
    0x8061302150d061d010f05090f190c020109021206130b07020304030f0c0305100e06010603020f090a08010608070f0803030a02031f0b0a0909050c09062107090e01061b03 74
    0x1ca104140c001007510303040c6900480c44140c01c044046100e0340d44400c480d2140e0380d038079000c01011194060320307604c5655000400d06107040490400d4000c00916107046024440340000e50494240c0d030340c0303040940d4648840f0070030351400c410042c01118420010b0700c0a071800d2840b071110150402d40040070805110040740d07240b4401c006440c007865015440c82000d950ba400c0038890b4100320300c42107802d0710600081c0c0d0710460040c0100c290159206c0001c0030303180d082400c260003039007103a04801036555060042100d80e584030400800107186120000038030508027082d25060088640083d40c00c00004001081640400021264080c5c046100180c03240c440754141c800d0303c900c1a1a0301218400340f4008210941880018191042c1c5616250342c4195103e210409464088580c2e106101c000c3c8140d0842d070614900800804003040020101401080d0094407450f90503108a00014961344060100300c1802c801640076250904208003d076100300304040f80151114001001c01c080c2e0140342c000c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 144069748 1250 144068498 144068539
    0x2070e070302070f0c0e0a06090b0a15050f07080304030311120a0b0f03010f060602071509090b04060302061b010b0f0306130203010615050304050c010507030507030305060604050a06110708061302 86
    0x58650b40f1200f0000317625139071092450041ea0a542c0c01a0381803600f14005110300081c407480c00c1100f03019010143c0075140c5800b20848030347c0440d80760280501004611031030030800c0300904030380d071042e0b28482e140d0816040040c115404c1c64010b00412204108000206141710140c1e544444005008180c0080842c040b501011180a240f03805600f000c101000030f44c095003094044e60900d0f421540d0041d0740b119a00b0000c00d05034465800714052140070b000f68100781c0c0284803004009807020034956588d50110b0700310f0740521b1148a213040710041c180c0138201d0038090102e0380320040302e03031a4503640c100d00060344640000c0c040543c0549401d038140c0c01c544007904000b0091008150003094181c0a80c0c01400b2984102c44c00c40380c0d40145107000c0420743c0540203480065815984090a000080e5002e0380244009450964404014480002c55589031010740c0d0160403659a10a00440d9054031986060b04642040d5259000b5100300034200d001100d41840070f580440c0c0500748154541400703032 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 144070998 1250 144069748 144069773
    0x10204030602120f0c03010b0d0e030c03070c090c030203060f1002100e160f0815040807050307080403030e031b040213030c060f021b0d14340602070e07030207 70
    0x401181c004983c00000c1003c41c4002c521800303445426407002e5540340e4461040f480300340142d03c0100d030240010810303000706600004203208250700300c0e80b170281006e443d20310b1a000800300300c5141112180a00c0206a180a0051010520f040c25815401c141c40080c100625140c46540100c03c0c1301241d1417400d10810405948402c3e40d0010010ba00b060b810550312144031140c5644490001d02000034884030840148080707522900151044100d54900c1c001c00e04005441956034140a01560010030018001006094400d581d902e503034a180d1303d406020f0000588031079110390040d41c0e4440614002d0850850003000480d00140d40300c6400071616070b40000c030b0300050200108240042801034000038a0341c0c6100003a000c407201007038946400e10300f01c560b4a41c000c1d0440c1c19005564000b07a0050b41031501ca1240d01e00340c43c1c4a44003d00304101d0b071402c9015030340c07000010748840ca00f541c045640c2c0d03401528180c0f01a280c42c5040150783c0d145440c0103001001007650010380710b01400040708985 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 144072248 1250 144070998 144071003
    0x26090a0312030b040908030106260a230901020405010e0303070f030311070501150305060907080c0603130b0702100c02010e0705120115080a0209010510020c090702030d09140d170a0504020301020403 87
    0x1c11154480b406c100341c098000740a003a0100340404040c4001e44000c81543c1d96407a2803d4100e105c40d030f6140421400b40084042900b1401c0c40c206403040110340c1a00441d108030104000186c69620309400104900c00c3c1d02055030081c3c208014a501003402c006000034016058280491a810340d4140e00ea070501c00c03140301078042d528100030010700c4995517003e041164050411546030342c0310083e103640c8904551260128070340c0010524101800c16002641d44103c0d42104040300142036294070019203412250040181c00c0758403801c03144142c0307110742800208607100130001b2032000c2c80030550b1214940100c0c2d1040030000b1101c0038201c4250070072910519480c69401e952a5200b425070b6075080d602c4001c0307101b40000c0001103400d0400d40c502800e5407050340c0c001d0107500b82040038440d90120281c00c2c0c0d802c5000c1000007020300c80540c0100c003d40c0d031194060049a262180a45040c8121708006c54100404a00b07241c1300c2c000310400d2690041c218241c0040c103926540b00180c024402ca5000 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 144073498 1250 144072248 144072251
    0x1d041b05040e01060510081003151103090f060a0501080c1203040819060515060901050a0210051512010c0c150b0307030609140a020913020d080726090a0312030b04 72
    0x28500ca804044d0481c5040313950a0343c501079940d014141c1501e141d0411142500341d04d010050410124400b54422401072640c4100000e804400c41d0603110300c1d41c8115a40d80f003030392107001002500042000226442540c880c1e0411641d4140340300c0e1038840100702090341c80b0f56488400d00d10505001d20072640106440000c0b200c022610340d400d0401006000e0003a150700b858140040c810450340d1503160201000180341c80d1070496020010b460030381014404e01d085100700e03819840d0014413403007004d00030510030056041e106160b904010354114072100480d480c4e41000040300f039164001c0302c1280807541c40b0240580304814460a203005040e00f4500c030b54540302c0c0390f00020a2103000d51280c0c031401d002c0c41000c2c581006410b0b109a45501d4020b00a4012512800184001c03400c09010500544010708000a14031162134520b03286d0005041600e5580c1c440d50710a000c9a1096100d010420b040010b4070300340144200064a00c400070312000c0d1a90087d1407051803114400d500c00c1c440503000910 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 144074748 1250 144073498 144073511
    0x6030c05040b0301080c0a0f05010203090d1103060c090301150e01120203030d0507081b070b180709020d0b2110020d0e0a0c0302040608031326190c1d041b0504 70
    0x800607500d01b40e5589160040354254030128000da9110007500a850040e00254035100000c4280072000305c1000050350380c9500b03c07903a10300c643c2d030034841903001e450b840e0b0740c10352680b06010405085581040d010600b03524503030381c00c001c00d615005d0354a046660940d030100c6801d40070700210b800c0d03200d00140016010b1410080088242d0005c81c42030003144600f0802c540318805000100c1240320b160030103001c0c0010540010311444403105050845222941a220310581d0340c0ca941e0280d030400410351446585808030308403a0706000c4194841c4895502c040705009540075490707601d5040030083c1c3c0610540025001500840ca600000c204245041c1103405424950600300300c0c28505000491245040032400600c0301c0b0000140c0305180d03100050004140e25000c404040400030945a401001425040c4404813205000d0145141e4045c59450f05400755450201a50344650f0000107601103905440050744007881e42c40b83d4815440007081005000010b5000d0302d8803045d5114030b42c0300d424881d = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 144075998 1250 144074748 144074759
    0x130603050103030f0507150b0316060905040b0a051e03031e090102010e060c04050f0301061a0d0501080a030c20211006030809150403060213060806030c0a06030c05040b0301 76
    0x500c001d040700c0c000e644100341e400c441c00040319240705521005d426200036103038600c0d48074100e5200c240c0c005001001c03a04100c0e01310b00204841e0501317604c244e0206089810030440303801d09028030f10340210101c8003540c441c0e091a001607415044908010b80c20156205000004c1d01c04004480701c825442400c0440041c00d045c402c101540071489040c01542001003140100c0400155640684100c804007400c00c3c1c142014007003600003510141303605640700d801c00185001001c5107440c0d0081c00090090f43c54005500c0001078503010b0340203500faa8031119518003c45e9008240031441580300003100f0700c1c980001000001d101c841d09a45a008ac80c01070f100100040d01c40f02141c18024050581e54003030149482e110482e441c1788006011024100079a840328903100d240090000c3c5850112410143c41e500c2d280f00700c0e04900130b1601208410b84081c0009500020400c2d40130b00210018510041c050003c65002c48051284000303242d261700342070607101d024030b05070360107002d00d090b14584a60703544 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 144077248 1250 144075998 144076001
    0x6051804020f27011e020a0803010e061e010e040b030a120810060206040b0105040519020307020312011e05060904020903060903070605090303010f14011e020105040c06030b0a0b070602130603 84
    0x18541c195085800380d0782c03c902c03070340000702d040700003605840f9104c00d19039150050080b01300030700e604000c5008900030200080c140070080d6018042c08500c000e413500c1c1c0b05d0140300075070420800c11202c8840c2d9001d5580c86a034090000350a14000352030100b800c1407804042803400811311001040050360b84d803030812982d4450416407003201e4030310709000d40d10380d5917000303980311141a10050050710100e0300500880c149908110b030406080c0821004034045080620300f2070300141c42c03d10050304006504510004600015800341004080c1a940c4414030001d82400000c4c03071265502446011078503d1041c0d889030f060340d00b2410013400f960304914051035a50b480ba40000c4040701c40c0c074a004007041001000000b600d040e600c030382c410000210f0074840440090b100c00407003e41002000007003441c0300ca00300d45003180003003004c1c1c00110f400d080c2031501014610143c2c02002c02c044c0303400329030001c640e1039041200c11a1202c050b070b940e4503450350420b00041d1241e0000707050180018000000e425925 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 144078498 1250 144077248 144077257
    0x90618110112060b0f0307180803130f050d1103010605100305160305010305060f061f0f08010b0c0a0b06031e0a0c080115033f02120f0406051804020f 66
    0xb42e031000004401c1c182a070080390118042c100f07601100b446442841c550b404000c541054090400c090300603804c0958960880301a005000c3e41c0d0004540a4401c1010450010281c103500300c2d40e5078401e09117030100b03080c0f02c0203420140201c0300600c080081510294881e40c00707004060030980c541828540090701901c0b095a4082c448000190b050150310310034403074503040e298890301a02090302c4a811015801c01e01425503a44070007880d0803958000144042c2c811307a4072017503c40081ca01c920f404003901500c0c0c16482550030302010440c12903007210108480e85c0840e840341f010001034030307131030007080ca440c00304401e806e50b20780040f01d0140440c1c000503808a4061040d041005000e0700c44896130300769010b984c19a462080340d103000f4000240400004e104c08402e150417901c221030407181c3c0d812240000e02d8468000074a1014100720168140003840c41c4040b050b80c01498000c4e0181c0914103482103225240c10840c0c04141d10390340700c7c0503520070500098020010b646030504641c030700380117912 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 144079748 1250 144078498 144078533
    0x115050717270d1109040c0504090b0618090706110709091109010816050f0f03150105010e0a0f060806120102040605120f040b07081305010e0606181603090618 70
    0x102032402c01081d03c3c00d40742c054406a40301103512507105028041c418490b5015000302c4600000c25400715180d1038510691450340d0081040720110f081100c103211044050b0341416050000c100c0801c0f80c2100001034000888810345030550503010882845424031289070880207500781440703400c4050111b20906011070102c00c48140d0742999a40d041190307a8102d8110a0290702c0745444104200e160210b031001d4052001703448800c0c04a0143c001a0611203103100407034001d0484001804196440003500c8202c00e4195080618103041404500030700c00035206070f20400981400241590b00d4110a4138406450b01000b5074459031940310280140c0c10100b170014040b0700034400501c00c1c580e000402401030750804c1b01941640ca90741e50444500c00010003c2203c0c54040c1c51000006009104083c0c003034488002410321401e01000f000b107103425840c1442800703200070302404020940c00c030001d19002000d080020300140a403510308040c0800c0e42600b800e0881c02507120701805042c6620f0700e10040e = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 144080998 1250 144079748 144079807
    0x303040309080f0d0318120c0b15090408090103271104020f0928080f1c09090b01021e030a08071d040908040f1203080c030115050717 59
    0xa403a0603405035540100f0000d0310240e030080c1c10159202c1d0283d8041c510384420741618442521480e04e564002d6a0210602000212102d6000c0e0a0040440340642c102049034400c5002400345000582c1c1c00c1405000a000a400010350a0300c0340c0c06540891000a00500e0304151000c0000c42e01000c4103254405480680860000308100d1404d8421188190061840d20303051180700b0007804801020301c184c503040b49aa11420440c8421051400c0c00109a0003004021100c1490740325030410200c580e421031103200810310714801c640c00040761400e548400d0400103541f000e0000403803400c10320008195460008019044240740c001c401010741c01c806846545054446c0c0000b110144030849005125586000b0f5080051401e03030491004103000c1d2000303d00f00782d03c45040fa9076100060b40201210714030100c41170708150700802c2440d404166003c070103040d9031500c00c0000707034030072141016000c01200007428000c0010f980c807000003580950a00c141c94aa00c203665100160b50f07041c4400c10744 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 144082248 1250 144080998 144081017
    0x30a0807020601030c030f050c15090f040b0a0b03100905071d030d0f030e03070203070602010e070b030c030402041e060303021e061b1c0e0a0213090201080412050c060903030403 78
    0x58000100c20f812250b02c648425482c51442d02e41090015010000300d8542c011240d40c00002d030341d07101203441d07003110100107650b840c400b00c0700700a02d80381c00e4540700f0300580c100031001407160b44400002d0704842c18035045503901e5a03000018490780c03409402c00700b0418a00800e0003086544501307400031212151001001501c48a401c140d51070701c8501c1105d00060706c410a28104520035000288420b40c02030440303007044450390000c1d0400c13006411060050390f541d50900c142d61020803031240203050f86100b0600e10b0a040c02c3d04255480000d00103070203161204080c80f42d003198550074110703001e25120b040001d5a101d16000703407509030100b01c000c4101c0750106214a03044c0040f5009000c1d6208101d400d01d140240c0414688680241400e103440b81414000c0c82c4440700c25004002e80c0002102c00b80036005c0c480e00c104100c02505144c5051301c18505086c0c42d0060f40c0040c1e01642040d0415600d60080490680854a81c032a4896040d0b59003d0319092101400d40040914040c074860346840390301 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 144083498 1250 144082248 144082261
    0x21041a090a0e09120c120d0e1e0d051303150605040e010c0203040909050309061b060c04080619110a05030405010e03090904080304020a09320c040504020f04030605010305030a08 78
    0x40c00b8003642e00c450681c000d51000c008012100c001001c5009241e01690002c0b420503000039083d40004592070501d90b128070340f0180004e0180310100d400511303000c1e40c5611400c1000c0c41540da40b044c6e59007034244500020311075134602c03450030b18000540d4001c1c1d503080b800401c0342500c805062640b02d2903010700c0c2170280350300d00e41406018400c252203080d80110709241c0b0b00260540a894060402d4401c0c1c081040031000e0382e21420000c00b2059010304070700040034080c80015152210080500c00d00340d10078030040c4401c40d0003081d1150031a6003c0c034081010154241083c0c018a4060403241d0600e5002500c5e0896a0308100034510a84c01907000b0059017940301042c0d601d80c410b50b141c00ba4000440d500150000d20200b01031900940090401a0102c1e15011402e0031144208841564820303030402548642c21016828190442d98200941e405d0030001d19a64907400385003c0c070381c0b1940c2c0106441003035006001c1070f5402590000d0301446196968100b45440e07a11921001d000568210009205d = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 144084748 1250 144083498 144083519
    0x20a0501050f071b08250b0f03010b31060801050607020f132304151505060703031e05180a02030c010c0807061a0301060f0821041a090a 60
    0x2801a03000301407807900c92155100140c81c03c20034604c0c1d440744888880443c007690100680c0791a0590028000d16880103c0c1c0403015070b09043e400050011003c0010340d02000c649000d4a045840c20950140c40d180c0101000c4400340201e03e070800258401c1c3c16965600d60201000400c685032134443d4051a604c50040c00300300c1c810380e9006504880001c410300110b04042055120007650700900203a6200d00b10050701801144004100d035002d805000e010074006000c04101140c0051901004520613540101004011038403a080c81820045410001d05001e504101410f0080c0c84000c03107d81a401c0305000100016100c0d81542c0f01101c03841007900070009006d400080e0010024600401c079940110383c45450b210044444500900c2a98000741311800354a160503c10400c4011608044090600b16421a4440200c84491040030081504046000c1c103804160201c8050480034112007507032580700300d910100d07642c41c07041a5210301e00c551344040d001c400d6040f02e584894641d5003034141c4 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 144085998 1250 144084748 144084757
    0x100602071a070507030f2306040203070608090a08030405030a090f03050c0609011704051b0103090b1b0c03043203030d0b03010e0a061b020f0d0c031205040302010207020a050105 78
    0x401201c450842a51841c0c00e29010704882840780084442d01c41c0c84e80c0d600e581c5105501401c0710100c0b101ca1180c80182c00b409101c2c101c0c000c01d00c004080030710b06500020b6840420748650f009100a800100d1046070b400d101c0b035102180c1000c0c505070b0740d0415182c040e50320340c004174100300007507140365000c80e01c4100030000c182100e800c50010011201c802c02000003641c44032800b1410702980800384401100c02d1906280300b0b9025101400c24041d291032512110020340b08280c2c10185403054010001e070702d401541c1d40100c101c540010240c00c80040644281c42800c0d00e2084c1d0f803001140004042c00c1a44540440700782030080110780b080003d41c203e00303420201034010760541060092005088983c3d02c406e01d640c034010008100101c14802c42811311964280c03d1321001e4581c901014115481c0d0309140c0e0340d22082c801050082d2348600c48940b02c00003850301c1703001c01c1901d001070014103102d04401130f0302030585a010482c4d41861301d40603000754000340d4224001c920300c03440080c180d8001c20996 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 144087248 1250 144085998 144086009
    0x11104051f02010b0a0303020109030f0503010510031802030f0d0207050102030a050306100903061503030314070c0b04030201060503011103040227071202070c0b03061302031302063010060207 84
    0x408101d840c0301c0e841e840c12003410340742804665852402c444690740d006080b4000318025000021080b1140c20010300d03440020078001b0a0010400c01080281c682c5841c84000f090545400209424009440c0c899030309201006541131080c2c0700c800200c400c0114031408480e0492f003c403a011580d5000590300ca01a04541c0408100d0030f00004041d07003042c5080d4280d0034024540b40040c00e4076035503008222001c02048000d1010100005d104060305403040584041c107000b80038007103240554009004441581009018090017400306003014002d402a201401d07000300203200c4c100c052070700c10100c0c1d04100d07001e81c03040d46021100d00103602560010154000b103001c20070050350703d0007029500c01c009a20042c2000f03500304807410102da130101ca04000745c041e40c00e040d66681041400c2148004020840d214050310401c207115048076100484907580b80c0c165421901c3c0c01440d5101e024180b210710300055504c0c003407030758240c6403112402d021f0303c60450680741c3d48560380c480d807040741e43c0d034180d019a = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 144088498 1250 144087248 144087259
    0x140d1404030f02030a05011b020c041104150c0506040302030306010e040b1809150f01290901030b0a0302030615011209020f0409080910020a05010c030c08130809030a03080901110405 80
    0x50020a01e0311040c504003c3c0007130119010130a05135034003800c403210040700d000040034103991003409580c180602003000d00c0c212000e001c9500b290300c041302584202d10034410034194a5035a410381d28001c548070780340c040d000420b0300c5540c5014180a9142c0e4012504140059906110f14019140c1840b6041040b10b000c1c25038a004c00c040d41e00744040d0072014100d86100d00c1602d0300303000b00440740301c46140b06110404200f00d06503d480d003104125440003400c0f05800d00c80300d02c0c12000d404450207441902c0c10918012030300701c410b807003c1a44e400f2550800707074250107030604110410286682c00a00d841d420307a00c010121081004440c12201a0400203610041c94161404031380b44c5900901d400724000c500c50707860f03c1540800a040690300c079143c040540c01414078501402000e219111800409040c140400b94812000900001c0001d040c01030707424820000105121424080d42d210a802804551076000c0c01e08000e000440c080320130241c03d600380042c605800b4014000d640484001410 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 144089748 1250 144088498 144088507
    0xf040b040f080c031602090105030307080d09020f1c0b09030c1b0402040e0103050f0105101511250f0f03020906060d09050d050c0d0e01050409020901020a020904140d14 74
    0x241da0002068036201580c2500c0c1c18001d5080a5800380014115030080b0456841da11003548140014030405900051094009101d00c80200382584219498044988400a001c06a501c0016030074241f040849070004000c8031800103155840c081c0410351801580e251001d9075944282e50754a10918641103a2500210680d04100c400c103000c9000444008001505041d00c0301c0103081d541100b41c2c410386141c5d010541e68440c1c00310a100e0300d03400c501811052103107582010300c402050050700c40d40ca010841004125000d01205100311000386000100c601200051210303403440b130399081d00600f840c0700b8440b0000079030500c0b942c950108680c0c1c041c0050410b562100200300d1650002510158401e450f100f80d03a0014805004400342c0e04e1650f115182c60380c01d40c050047c54000090824024031a620240090507030300082964101e407060017001d41e4030202240101e082210944000790094511018441004402050650713a991403034101c0d0008100540308458100d8807210751480301c0000c01 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 144090998 1250 144089748 144089753
    0x516050d180b0c030f070203070506010501051c06080106050103060b030105030a060504020319030f0813050709020d0e0313050102010c05030c040b1b1524030615030a0215030a050f040b04 82
    0x41201e0042801606607440c0c410480e00e82807540d400440700e818519a00000300266002d002107140d805c0742c1184000c604110b643e983c0d50390744010601810741400380200c1c01e00191000303c20f00150f840c03100082440304031303501c01e41e01b40030b401c1d40c0c0120342c04a4105080802c80800c6201940e040b00c10080c01090462010348035080180b8002c1c0c410b03a010301500b038080c00c01200c0081a08441c0e1300c650344407442ca09610750020100d0601511221851401c0448076011410010755030013070f00c0c90794000695403801001d0500c0204003215140100d80400308071241703845041da0b601c0007290003c2c0c001748860034442c18100c80502c42210350703880e100801d010a0207010b40c0c50001c0c100420142c03550b8821b080230114101d2808903031200100c1500800420010b0825003c900311401984100c030560001580c2000643c56400c01040000c605c100341403045019601080030030321f200d80290203842c1c00690790f00c41cec10840d40101d4020000c0340c200f10128603c00d10804040b8469500718a1090907a182c66 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 144092248 1250 144090998 144091001
    0xa0b070506011a12090606040516050306010f110a050c090108030301051309020409060203150315060f24040b190207060c08030703090606120c0909050c12030f03010611010516050d 79
    0x40c0042c030211041c0a0044556290700780280160344ca2002000140b0b0441f08010564000070020fa01c603030320385080c0c5070800b50042c1c1600d0f01300c1400d0a055000b1040700001700d03810318024000110303521070505284240080031504a40c0168181c801c9042d580c0c13224002b6503688000e1040740c1d08803c41d0b0000b0402224143c1c030800006100400128075003405441d02c1c03090b80c2040e100e05510006001519a00349000c00400300c0003401c4015503c09850b00c8800109a4042445802e00900c4000c42da8611a221940c1d006041e24000c402c550f151512120f1022040d0031a029515084c1c0c14040f0407000b45000207960340403070380301e5542c00c2d000d0707000c903030740d40c1c840c4e40018108200b803507202c09540f000507040b80900701c05040000b0300e40700850401d0400c10b00d24007860b4001003c00d840d000c84080400c80114024a210005407145c110110f41044500d145200d8520700440c07004c0f02000110b40f4640c0709000b606440b000000074841902c0c0c42400c00c50106590303c030303040230400070044442e808545 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 144093498 1250 144092248 144092279
    0x21303050c091303200607120f09080315060409020a05070308010f030b01030822080309040b04110d0509031c0b040605010e010f08071101060801020306010f14071e1e020a0b07050601 80
    0x148020810880301c217000306151041c01d541d0180494024084500180300034031503100b90300c2c02c640040c130400c10262240348151101500520780450141a400144c0d101c0800f150010419071b4800c5503100310610b0020100d41181404400196001d80002a00c548040e4803900b0380fa000310498003d0b9285075100d900c9a8001844180c0c041d000c80d407000c5400c00c0c07503075034038000f00092000355580e115031008010440d01c031400e50b18400c5e4548015207840d4113004d420340d01404440c1c1030010703440e1600d404440c91402500c0c0343d2400000481d005082d900d82c40d13044011800416034052000c0361b102c10045d100f0f140800c44c01800110f4090620500034840c050f42c941002642c1085401c0d81c10000c009401d4a941381c0088070b07660f40002c103002076035911160070303000c801003032074400c03402c1c110002c0c1e4130a1842902c4002e04400201e0404400001e48099507541d4564001050461001004c0c8800750042180c0000d9101d880801d40c0041c50f0076288003101c008542c070001403e10b613070034901d0141c0340052 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 144094748 1250 144093498 144093527
    0x17070c0e0108121c0e0d110d0507140a050604030908160506091912030207031a01060c0f110a0801050603011a010909091509080301081c0507031d04021303050c091303 73
    0x240c1308404045a00588a900310502500014221040100708040e00d00000e0402c003484070343c00810210291035000c020f0b00c606951011120340c050601441051921000c0b44001d4001e000e4201030008045d04028024100c0f01568252000c465050544c0e0754034444621070660840401c001246807440d020a5400305650404d1003041010b031110402e1124540c0c5030800c4025a01c900f03800d20a0142d155085440204420300305a115070400c00024110220703820700801d070001c284115420040e0000e404c1c24118405044140159078904070a4044c01003543c4072406946030090109004012a225504e62041a11000f00c66072901d00810020071040c1350a171012a00782958030b1a0400300e0144c1e2a02c28000c41c041900c075418100c4060800094540040380c81e0310031004d040e00180c1000c1500c06440d05401e00010300001d454060759041c03c900005a44584005070601d4211660583c40f4282c1c0c0c000c40c02c0711502c1c094a001d0107016602503400c0700c007610400318500d00003031103010617644034134 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 144095998 1250 144094748 144094777
    0x3010513060e090307110d020319030201060b0a051b011109060c01061208070b010602150c030a020712030608010b04020903100c020f03040e0714030717070c17070c0e010812 76
    0x182d032800300c416400700c203507a604610307000025000c0900c101440e80407810b1404445904413582290700113955031005450560050201030324040900d8000c3d8007610051001084203a0b481045102c000c1141d4030002c0003441c0f0380d00481d1082d0040105205410203a050030000b5071030409110104040f0b0340181190310029902c1c0c2c000030a507940020032f40541e003441800840d8603060103140042501c64140c00890071035201d4010100b015010700c00e600e42007185001d0842d6030342c0301c0200c03c44c0a4410018058070548602140c50300d0b00307606078800c2084819031002000416410400c020a900c074840d0b680d50326034020b460320401c00806900c144802c4440c1d004941d10b800c810b298103400c41d082548907060038000042080441900100303a80c008070003d291892a40c40c100c2005080340c82145240da956221f0701d40069070503805681000700403a00400749280c40560800005070780c0e400504210344a0280850000d008034102c014a0706a8071560040d020b40ea4218442701d01c82d0308407030611a00700 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 144097248 1250 144095998 144096011
    0xc1f020c070306060807060c050c01120b1f08060a030c051302041a09010201050604050705071716060203150105070203030301090b0a030210050705010b0f101b05031314010309030503010513 83
    0x554200308141c021803041c2004511a8600510302d82030411962005080c043c1a010500000310b004c1501003c075002401c10032000011100003a00400b00c06419031b81000d5129035a1915501400c4603132a911110303502d4070134990b9406c2c00d21400c0d0030244002065643c05400600c002d18001c65044ac00a1340c20000604190740d559031440103030046510425444030005611600e9603083c02802d610640aa5040c4400c0c1045800104140700c0c1040c00381c0284021f9203104a0030300e0060440d80b52440706210909146414144607009501c241c030405c1d042c0480b442000c0d0554010000d45100a40003409941907030301c1d0403148000740130a032482e254040b41099001c0016030b80d8600c0d450310560340d6910340b0303101c0039945011b85c00c6030f60302007510384160703044039040d00565500c00c3c0380e00480c003261401107091042e0006c030118291101c41c000f011f502000c43c0031054441420700e90002ca5801d881280e90840ca51b80c019001c50b41c05040c00f40028a0810051000e400c2c0f03103100c3c4441d01c91b0b000c00095030 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 144098498 1250 144097248 144097267
    0x801200717031e0a0908030a09020406080d17010e0402010917011806020901020c04090c1202010e0306070e03160605192105100e0c2209060b1207050c1f02 68
    0x1260300841c1c052030840c0030f024071000f0b4440b148403495441040300004001d0750340981c4490345e447c08010b0064500d80d488044907001c40d212500000c0050030038100301c0745106020b0307001030901e13807002804400034511100006078030007000540b42c3c0260b80607182d0f40079440c18213040d145031214215601d8040d6403624280c800c500b91b00302c10703402407502034400117072240c218400081c205901d210482c1e1041c1d04004e507800116814100b940c0450b40346c41e121100500e154401070b520741c190100c0c0711b60715015520822445d26040028024100401c5086d219070120380c1307040000150f5203001e0321000034002d02c54194004544d642020b560075050400b840c2404443e0b041254240301c1041440d07080b503d070810300001a00f000d1400c80a4400114045d15a28000d001d0718000d000b108017032290520080261011451005070100c040c0c01c050100380020b54907100841d80c1035128411409694031a0400608000c3c460b034241e03425004158060320000300c0c1000002c80e120005551040c025900f045420705 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 144099748 1250 144098498 144098543
    0x4020a090305030f0310230108070306050d0503070204050115020c09041403030406141320041401031101020c01110c0d0822150c05031606020d0606081008012007 71
    0x102ea103c120551039880c1b0382815003030a080210b0788040203034280126152003207080302c090202510310a10b4100d02903134801100320040c0419600c415000300680d508030043c40303170200003000024003e03501889030ba40e0b140703440c0ba40508a0002c26005801c02c5076158140c0c80e058050541090250208500f0450780103080c90840c1e1068500f00c0302c40e990f81038920b0f086541034640f59408041050014920061500d80800c0c0c0e4004c8030429040400c42c0c6200c031081d60b03642e80800c00c1c00d0361074440c6407500e41c5c480c50150303002000c0c03020702400362180b028112003662140f820500080342090192080e00d00711400d1021000b40c5074000c5030703900d82c14407190380714050700b010595050038a42201c0524900e8504002d003c0e52046d02444100008a10500c020400010449140c1254200811414409414200c0090242880960115042010000e24280d200d400240035201d0080d010180c1c1d41e43c3c03281c00e400c0390104030160640e500d4803042d01c02c0781510f20020703041560054030b4080822045100801 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 144100998 1250 144099748 144099757
    0x304020d060f0e0c03120f0309031e0a02010b09040f0807051f0c0908071505030c070c030c03030e09100603091a100e07030b030619140f0603012904020a09030503 71
    0xc1900d940d0344030b11128000801071112010b9054001d0041d04000210503c407a1103032407004104640c0001c0400e1227404200201c95800e0b1009181d02c2d0b20100c0d07000c2c02e000e1540302015281c010b40c02c246140f1b840b840c1c140d40c1e0318011a0300040300340303000c00d441d50740c00d000b600b1269084c1c0350342c015020000d1800c102107143c1c2c88500d1803030100049018110a0140c00452150010718241c0c5c883d003001e006c440182c0441803c0d4400d1410031710349075075602000044501ca0050001e12010030f40c1c00001c10440300c6000700d030580c2d201e6101c40d0701513542901480307040d4900b21030702c200752414030a042240a0013584103c00b031070302642e1850702d842d03003e41180b070001c042610810300c1ca410001341046104810340e80590092828501840303440803546c0008c1c6da0b90001790181c000e00c0404c00b110780b9103058940c0400f07074003040314104131418500300f19444000f80c3e044810030b00079424503241800c4200030504c082c05843e00084450500d0b0034410503c0000d4214014002c14481c031894017001151040010b00f = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 144102248 1250 144100998 144101021
    0x40c050d09290919051212060a050303090916030905070e0106030b0306011d060105070b13020a080f03040b0c030c03030c130e090a1209050a2421020304020d06 70
    0x1c00300300750b0002c4020311030b5146848402210782c41c0024000800c0021031600d000c01c4100b0b4120701c0540b41c0382440703401c0040c00400100c22600c005009260104d640480501c03540e81111800ca840350b0780e0f810f1545911860000d19445031172040000c5801805240f11401c003015890700086240207590347d285040a59089400442c0c4850010001c80d41c2c503010b8505908001e401801c04d9500d000412801c092042402da2645000c0ca000103420741d00c202c00391661560090040c0e1040c3c01c2442140c2040301802d401039005689012021515050000d140d004d03281003d40254905440d1048141c059002041e6507034142c003003041240c0c500101040030354054840f4a001698906519803035a21401c0c0a602c003599a110070300412407900c1000c50342d10541c0c1d81000c030481c503440449030200d41d140c2c07841c2c020743d6003e140f0900114159801810180c0c501103e500b140c5012036407220280d0721039000160103c1c890015aa01410280340b50300070f1034000d48003070668441c403125640c860081d00d0521008 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 144103498 1250 144102248 144102263
    0x100518030d2c0303091e0304030b0604020f04090e07050306010f09020309070e011d1e01030303090309081f05180706050703020f0a030302090f24071106070b0709090b030c040c050d09 80
    0x10b11185101c03c0c4001b030b04401c040802400c20414400440361079006d188005012b6450036030000380389840702d4040781e41d00c03080910031030b94940c0c4a1446400410000342650f902d032140ba4000b048600300002e06a06880c2250342007040b607860141100060340c401014410305000701c12001a100e110340980074042c104000c200103241c071100c02c80030f85402e0020b044443c0e00c03103004501d4050030400050241903036014036011409081d070b0b040c256440400c641c02044140b0070864110003051040341103c1c200e164080c010321213921000d102c9c40c401040c83c800d84045400c4440d08015690050b030080560764400d0055400101c4d0100880d4180842e41c441500403e400003038110071460120b00400500c3c038100e03000d480706000c9161081c3c10012801c050780081c00e0000d010424402442d0451040d00b40061140d55651660f150051603240700f659002c0104040f654049a810340c580201c050080c0054000e150744400402000094240a14a030080c40400c0224450703505090090500c0d07140610391 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 144104748 1250 144103498 144103501
    0x41e150302031b0108150108040303050402040b09010306020405010f02010608120c1c020304170a0c0302040f0b0301020d0b0405010e040305070f060e1605010807090b07061517100518030d2c0303 85
    0x1608071710000303001c9000c0c0400e80b0f10b1b40364280e800100d10307500b180e094500029203664038400304006203200d42c80c040c0d00c0004040000f041040c030360010800d54074207a890b0101c14208040030382c2030341c055009070b0350150000420400b00050107006004207840d01d1080394009184042030440c2d107050480724400603000080c041c0b000541d28443c094420518000804048640e5141d0744040002808000d00c034a8507070803514101c440d1604030000707030140200210340c0d44114440c0308005010000c2214044c5e420f10b0300004061040460052046406440d030518040c101e039641c99081036140c4089903200c0e5100314200350b0348801c010064440b002c0f400c218402a04000c000740c004507004103070104110841000340800c0488005544c202c0e41c0c420000700d840c21282c041040740544641100340d01ca03118040f01d041120b0005040d0901c040d608030100115251380050000800d0340b2848101954420442c400714401107622000001c00455540080246030b00c4282e800510320b4003046101d54030100 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 144105998 1250 144104748 144104803
    0x60a0e13060602120712110c1009090b04050106020d08040c03060515150301150c0602040e100f120209160c021009060201110c0d120603171206041e15030203 69
    0x706101d400c01c130075600e103030600800781d4400c84040f2005e503059041100004d6840f074441c100300016106000014403829011203401001800f4409505c81e1003602400c21803010b43c682060300c52076042c1e40706903000c0d200c050001c1d802a140b0501c00313001103452220019000000c11914400d8900403003417080d0034105035070b0f84010408084042460039007031070400c0004120501000c082c803030383c1041c00c0c1421080d250550404000a002e0b07940254010305181c010400300d0100b01650800341c0302c3c0360f4840c1400703d49800c03c01c10340c2204644000d42100083c0b01003070341c0d0720019000c4204120b8500c0c14800781e280710780c04a40011088442440880d900300010b002c00f54080c094101641e0f42c82449038204851940015902d0601241200501c03080c2003401c195040c0607081040a1504901c40450304000541c42e000650f0246002102e4580c034200800d17172524007400703080c0500000c02c0245d01908040207483c801031001c14010030314404550300000c0142c9007031000c0888400305030003408000c003404 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 144107248 1250 144105998 144106003
    0x13090b040b0901062001060b16020112110703030b0303071202010c020c15121b04080703020a06080f0f070309020d0605010501090b03090d0e0a08010e1b0a0302030606060a0e13060602 80
    0x70035104004207001030001503408003a46401c03220200702c03080c80d103428071065401403105420803210180e000908031103d01c982c000c0ca05845100781c1c1c1d05c1d0b82c0344012108a4040b0b403c0c645000386d0000d4100440404a880394000c00040d036001403e5a1038406c0c02e070755440c0e00c24008004540940d4482c8410540f50340c05126100ca280f1041c0c42540d19138014000100b5140300d00020106980f0640d0301282001294005e00350302d2102902170169202e840e00d02142d91540a0301c000c911618190f030010607480c1c070885803a405003d05200307140d80c03500c442142c0ca001d0b010080c05907041544e2440d051003d03954601d01040703520b020b210009801e50401c000100401c0703075a001004102c10070400d12000304000185001009100c0c07900d10019041300300060b11000345a40102020b608000c880145020086000c014010640c003071745010072907240500640c0358441c03002070341c542c0007040042e1890030700d00011301c0049403d20f0894420940880000c11234840c41b42182c26943d0350701420f00895804 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 144108498 1250 144107248 144107261
    0x2030709050a050f01050708030a0213030c030203010501090c0c11010201020d0f0f05090c1309061104170c03070518060d060203130c0503011109040902010e060d150f06020307020d030513090b04 85
    0x40c0c90320384e4200100c10000e402c5204201c001007198a0000004201c090103034166102c10501415200c190ba42e00c1c01d0135095284140001d034030039440e040c0001683c0030b80c0c2c440c582105086488060349044030362144001101c0c0012000d042d55000c10442105c0403c1d4401d0801c0711041e442c0001d1640610f414510840f40014103480d01030b0300c03200862889a5640c150207034850010100401e00400c1460400c001d4691480081810300d80800d000c50040301400e900c480404e842011940d540949000305692070940d403241c0350700421124510101c2d01380002441b0740c0004040e00d5060076644c15600c000407a80100d880405442c01081c1e00310800c80003003801d000408003100244602e024501c003044a074410388102c0b0303104507038461740c0504590142c50207461803d8003c208ca030716000f100c030301e41d4040d0990418014035074441110114101401203114402d1303a0340c0703a000310700f005050b0742404989409000241d0074441c05204200c200c08203030300644082d100c00074001c41e40c4d105140a00c41655103 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 144109748 1250 144108498 144108509
    0x200102030405120f0403021f020c04060b091215040302030a090b0307080a050402041d0705100c0c0b0a120f060e01052713020d050d020c091909080d02030709050a 71
    0x4100740804904001580324005011080455681140c943c030342035503102d02e0b03000a401c00407613600030034210340700150030204403180d8003500c002c101c030b40302040104c6071680206880a4024042104c00d402c1280c520030506e00550212800039458114566160b40200c400b100140d01c0090450402c0c0d81c0824400c00070107030b0300344031801c505100d500035000c184005c05000720103682da00050107543d1240c0060310301c0f6a61807400d00c59400001d2105e5143c00440c004d060064144150304c0b01d810388a0302182c003034950840c909a19040c1810180b084070781c403400042c010001203042c06590b100b094810045020650310000070010710703001c140c0d00704d0081640420310404941c02c090034000c0784491a01817081010841b00e10b903680c0c4010002c40303500c034290041d400000000b120000c2003000a900b525903c40c070b0f0202d0307101d5070003c0200458072508807001c068044c114680740c412841c807a002003007144c1c41011811305045025400c6001c81e002200d803500007401e0b102c0108402e0500c00d1028003c2d05 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 144110998 1250 144109748 144109751
    0x150406020a110f0907030617030f0f1812010e16060c2621010509060102150702240a110405010e0f0d02030f030d050f1b030405010608030a2001 63
    0x14608000a900e40c046080007800c0e101d082c94101505981d1000120891900242100203500707161000a005220702d02035180114a004e4144400d25000420b882c91a022003000c01d140140c0d10400051315040100300c640385008000d410482c60f6641000c02d000405800c0c0000346541812103440c0c030f40700d01c0784001d13100704075420300c01e2101c6a48001000700031034010103612086d6420088a548280074605c07581401d080c0461721000c096800100c5489003440c900220100d40d807034104106602c80151a0b0030302580c041700c4c600707404415925140394000c80a0056407891414501000c1e0341a41394950640d0084c80c0300b003040390b40c90b4213114002403000d2245e0041c0c00c050400c40007801000d40b80c1081886428001140042655001d03909c6140b80e501606031317000d1207a0011b01a03038035004dc0300082026418034000801040074101507610030755a1104101610041c851412150750002e002030f10155294603011401c918104014515440551b60780880e10541c240070344a80b0400940d0b90b61a40d = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 144112248 1250 144110998 144111007
    0x30c0114010b0301061d1c020a080c0d120c0b0406060302030d180605090f0303040b0a081311040c030f0c180605040305060105060a1106070203130e070c0b06010207051206010515 78
    0x2c842d66001d881c1507a42d0b900b4071620b80300108803032008013605140c01a42c0070188850300c00407048461070300c0750035500c00e503030f034043d43ca4039142a01c2c1c403000820a56a0421074405a01c8082011200c0b20b41881d482c41c00c005082c0d5800c3d4651150700101120281d4200c0e0b1a500104114241009201541c0400307152840408036400f4150344000100e00c5002c042100104502c81075640b90a10507140e2403004007200d581d42c0d51105103008030340080040802003895400041c030b00310000386810303440b541d01c4240184400142e108000003004071786041400c16540758454500784d11030703108000102e19651510707560300e0007000c1078401d07822464100104111003448200b0024000082c07440c155501110320f180c94800c1498101d80d0890f47d899002114440c00c800c0c017210340d80100c028400d0f4401131010900c040e803140c80c20205901d00360b4014002138941d41c14040400c000345242c82d004401441921030b1296510006044070701c50720101200b5400603001000140350003c0c401d12082107019a16041 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 144113498 1250 144112248 144112259
    0x100510090c020c011805130504060b060307050403020d080f130312050a02070504090f020d08120a0b030c010e130e060609060901030f030c03031b03021801050301080a02040f060b0309030c011401 85
    0x226007801c81d0f0725041c8a00904c540301320000002c00316010b8140035041d9070381e002c070088000024000640d0700341c5074a45000c182c4841420041c04030fa10440c07003501d034286030504d160f00784500000f0300502900c88060a0280000303030304507200200040d0107180c000c00031080c10750900c901b6014001d1034003414460100865030b002c540100b41082215001c44002a07104845c0c2808407460040060095004401124a4003000052030141881c100034010f08002c42e564840712404807000368070150b51503404105030b8455588210700c006010500600220f01c04901c0000302c0b01aa242da80b12190680c11803001c02086041070703d0310030345c4000101c5900009514644805241c0c20310248003400b040500c9180405050203500303e140000140d410102d401280058028025001500c10003c5c11502c9005c80e103180d8881c0043e0b0781030f243c682001d400500559420000107064200440003100d46a43c00020070200007005107100f891800041d52307030f440d0f4026640b130840f68000c40c0380f03450342c0051005102c0c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 144114748 1250 144113498 144113503
    0xb07170a1d061009020d090228050306070c11010905031009020f0a050d03050c0a08071a06030a0b180a0501020f090a171506010201020d0c1211090303030403051b100510090c02 77
    0x11601031000041c0d1b106034200307914016050340c003c0a90030a001c5c4040c0074800740003d0206042c2110b111203074104a4a440030107403200c1c0c1c10ba400000007000304a0100102c2c0070301e00302505409050420f5080c495640000c2428800c00d019120421566036036800300f13500b4002d89000d5807003004c17907081154908000000711402280c290150410001250740c8030310400810200c4146504042010388400003032030881c0e09924403e10324544401c143d40031645605000612151060b40443c2542003940e42c503000c00040c144003210648280715420038440071580070310013403e010355404030442d91150b07660140042d140e520b03804182c0310303441c1c142ca880d0703400d0020562182c100c02c403041301d82c600d4a404004074003a0040703050005606182c104003034002604034241441c200c104440034070036a1021500ca110074002d0314409074150b081000040d000911950050034a12605a500211700300d990241c280341045a5000405c6075907150103004508000b1007c080081c48001400d10102800010094 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 144115998 1250 144114748 144114781
    0x100c0e0603090a1412030406050105150c070603330611070602060a1107140a05060c0a08010b0703090e0c0c0c040504020607060f0e03070f061a0d0b07170a1d06 70
    0x130710900940c1c1c100c0400b0002402181000034400748115200c0c2440e00f4510000e050a11405128134ac442d0b041580c01d103030000c1512200c1d0b207080301a00400c0e192078015000361080920b113518408000d40140d40b00000e250400d03681001403544035200a062110140c290781079120a40a581c1c40f880040140e05c0c3e001038a00d505c403506170400b00d12141d0004044069024032100101840200880b41c074140100107a08014180a1030480300c040d00c500102d01080d100c0c40c80100300150260005000c1c0c02c01c59001026040e20034038181c603030940e8641c0e0044484e84259842c1805001c001180b203d0f200042128100018040364200203d0505038001440e921440c0310080c02252a0000d0060050710f56000400d81141103041d603644004901c4c0a1014070f04045080390418641001d07500c4850210207615084a07020f4110384501f142922685140321004150004104254124920b84284405130a0041800b0f0030042221051040342190345113002c4c84035521503000c0010071440a84014014 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 144117248 1250 144115998 144116003
    0x201050a0c05120c0a030f060602031c0e0a02220203010321030c08150a08011a1504030b070804140106060906022407030908090a0f0e010b0712031d100c0e0603090a 72
    0x142ea0750354007518213901408147c600001034614044000801700c0e008030040020030440c10002c13042207459119402200c1203c040030900b644000014001800c02c0c1e1740d1482c41044418000850880c4075101a00703076402608202c0349401e061104a0300002801e101c14100d128078142400f08080d0038000602e030070402000c2c50464840d8440494060300c8062055000e000303404024040e0640b40c21045040120f43e54090380541c0720101e4107a8941010700548040c3da074000801e5800342c6a103001102d4400d0701520650706598a4031081524160034803e5000030312564841e40000d80c81d0400c0a03080000c215003a40610040c100c002c0c10000a981841d580311149090002d020003007420302d44020301502c140c6507040b80300a5404960212140a00030480d0700725281c84807281e03203411070308009000e240c2d0010081c4040244030b0780c105000c0d801c2804682e54075000c0d0204018080000d40c600351064000c1d8115680d1b5102c000c01c107540c00034003424002402d8842d640356003424902d4907940c0303005030000b = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 144118498 1250 144117248 144117271
    0x20c090604090f05010e07050f0409020a0911040b070308070e030607020c060c070306060e270712060908071101030b0a050a030b09070807030305250807060b060d020a0201050a0c0512 80
    0x60004110340c3c00002c0491540110003000b14425501215903500102e004691203402c8011400040e0314290050a0b440c0368081c00242d9500d18211585003d054411600f12501d2024040400d46410302c401074003107203000742c1e90b105080c28541c80190035030340729241c40c6e4026049070b020820150f0b000649800b007542c0545e205a0f40c0c001806180d17042040540000303050500346500003a0303c207100d03000140900881840c2e4040c440140400003d640580c0003020031942103d20204140e0740c4002078003000380d015000c003207074b4040709940b64241a84840350481d591404004104019641071040c450302c5030f810758020000d030341040005110020341c0c0c0720052030946440b000448410045c002080208032410481d5101c40d228500500140c00511030412800c2c841504406040e05003041151001d40020312a450031102d41ca8010180c220100d19680114041000c0c14074203c4c507100a1200f030101e6400085c0c41d042400750101500c0101104c1c0042002c14000c0c201c1e81034070b441810b078025910810 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 144119748 1250 144118498 144118511
    0x61603140d02130e010e0103030f0e01020a0b040b0a060504020310120606080d111605061b1501090b031002030417070606031203021908040804060c050c0d0c0510020c090604 76
    0x10300800300e105240c01444128000b0414200b080c500f00003690558501100c0091541c0e00c034401004096824440540012110b92010b012140a42c0c0400d6074464107205981c4c05200c1901c0300d0307841020990301201c04582200c20071103010b817948103040240200312019451800c02d0154030301802e240303000301c040c1d103000c2620740400c222080c0d01210041140006640c0c90101440c400b500642980040841c0c0b4058800045080218040a8415600001c000d103080c480c60000c81000030305946200302c00f41c4200b0001030031440c580c1181b28000c05c1d040c800495080304000030b02d8103004800403415007040c018000c3c400090061011440c28460401d1490744800040c2850800751401d58805807210310203001e40c02c10130740d06800400301c0300c0c030b441108021291190030407a00000c089a020300381310b200740070502206100e1100480801e01603c00c075040390003450001502038504040480d041d165800e0104a141080c01081d08003c045002400030f4011000100e4040300c0c00424051050b5903900 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 144120998 1250 144119748 144119777
    0x60608180d0504060e0a1e05030d03061a031815061005070b0103112205040b0708090a1704050405010b04030c05180f04082205010305010506040503031c0204080a05010b0a05061603 79
    0x4059100504042e44c41d450400d000c1f0484901111050082c94001d01038000b80412443c001e000b440201e40d050300721048800b400f074800c0c03070140c1c01c00303019000707040580545100c503450100889502c0304100c0f00703640c515007002410800304c800c001070850207010301404108040762003c007030b86044a0704940c0d0304066a0803c80041ca035880b00c445074103000449106944400000c03544240d03c62845900452700a07103440100f541c1c508030448058009902c0242076200183e50343c9100b4070200c061081d5107052039103400000f82a2a000d811010074681c010030100f060000c6024110020541a648a00111001c5003024000e080040815241004039404603041007005d00841d1844042e002199114010455407a080c040c001e10034070780024102000400ea81c5040001c6804645004008500c3c0c80001c0700c02040c00078240740098051030b824000040c640005000170360900e841500000b5151000c0401c2092284594200b140603007828089613142203600d1003d980202d0b00350403c4460003032000c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 144122248 1250 144120998 144121009
    0xf020c060c070b070507030219031e02060d0603080c07092018041d060105031c0c020d120c0302060907060c020d260d0506030c0108062101060608180d0504060e 70
    0x2588802d0780104001001000d1020101c2c081c0280c82c400c039848552001079030444107400889d0700000d0040740442040d11120350540b004440e055201400c500d08018803009003904480346580107030f464200000312445080002e0024002400b440c060820016000961700c005a2070003102c4502d41c810001076011140038412a06045400000e00c18041d000003170403491911a03030820743c1c0484e441140000300c3da40c540424044149451155061415131703900504030b070703440e0180c5016a084510b07540040b000c5580c03041d400442d1480c580f60000c00c0b03003443c50024507291000b49040841d13000040c0600c032341781d070000160740841d40441d03a00c4010b00031410504586540d049500d0f011505003055030f40310700c0105015090700314440c01c0c1040655242e209040d118030070000581e0002d200000007500d01d140100f483d044c006482205c4213040d03003582602c20300319125038001102180c606002c0244010030520303928500409a4040e01010500360009005030260f40502810b0107003800c0a280241c071130 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 144123498 1250 144122248 144122263
    0x7080c13060e0c0901030b01020609060601120b1c200a050907030b031b190b0904090305070807050304091b080408030901240503010b09150103050a1e1a010f020c060c 73
    0x168000c0c05103c0c10305420001d11035110005003030220f0b0402040e00119800410303107510a510b440040e000350f50702c500044034078084d2291000841c035902c407148203094403914140ca0460715072002e400300001c441e0509482052000c03406444855504000c18800d450700e0380410102c81082d03480c060603480d81c03e0143c01900c02500f00b40e4041c4209800008541e01911114501c040c082d5511180100b00d50700894846e241802001c2034100b04226441843c14a40e10405c2650b0192918a00f401020380e1040f82c44ea00025042e511035001003024411300360f59208960401c6001803810380440b040e640060403025000b400038291500100001380304107001c1d0004c40d24002014001c40791450a42c1c2000d10b041103d0023014041d619041c00c0c180c183c140983c0300c0c0c3c00f401e6484200101d14001d0801100941402001000d0300d540303484410100700350700000485014600d078000f103030364003140b005800c903800c0c0400d51504001c41108056540c94002ca0b860f0380e00345041d01c03810360390000c60f46054940900b = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 144124748 1250 144123498 144123509
    0x20a23120a1404030806120111030c090613120c0b03010501022a030a080423010903140a0204020c0c010e0402090a030f1e0b070315030206120a060905130501050907080c1306 76
    0x9040b4104010182e001c1a007911a5400b158010307400c1100e580aa82280c5101e84082407081080000c1640d07101d40e500a802c0500c001045a031621484c1c660540051003240e1040301c3c20b40c650034200c010000c001e040f40015244560300c1d20300b1076141c040000d503210b0b5510401c40c1c6c0880f0f14088880b440f40c508054000c210b0028040712481c04041c5480b0520354040e210708a41c200d01d078602040d00e502104419148140169038503100c55007961116500c04100c141d0f92a00c51103001c45200058407240041c103c071800d80009010310000e05400540300b003444c02c0c005442a441009190140da89071103080d0b040c0c03a08034002004c150100c1c90030584803280055200303141080101e407a42000803010403d44100c4041da810b00c1620940d1071811280002808020f50003d003d002000112161000203684406c0e0743d1000b055455442e80c0c3c40085941c00d5484060720030644400c0350a0007001d01070b461300801250001c288440c501407000b0340f1041054281841250180c031074803206401c07600404007601 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 144125998 1250 144124748 144124781
    0xb030a0204061e050f03070302010f020304081006050f0102071809020310020f040305070806010f090209040213030303050601030b0123030414070602060117060702150a02040e040501020a23120a 85
    0x81d103030701d401501d0603811900020f9180c09048042114240032002e5800400040c004044450943d070041d500e80e0050020301085100610000034550030810207001c54455a0703000044207801c24062140c001a00e4220074155070204100300305030541e8081c07882230140b00500003d5590701c5840000d041030351703c44042101d180042035038145030100d04000e208a80c0318604540707820b9600d22505850304004d00c5004600c2e81c41000c00c100039001074000340803440b0010300040c900061500302031b5103040d440d001507001a948a003000a00c1d6058803505500240074200b40c4503903400c1300d1550340100e00301d16403181118008000f060400100c880302c5005a9200b0094460075a01d500d03009642c0e20782482000c5c03040c0541e81504500b0340020500a005a440d9400342448080250381c461855202900c01d516142e420040050341d5000880d140303000da0b01c107800150752540b4102c00100f00442d090040064120041c1d0001c0d2080b40c207204a9101036010041d2020aa881d65401c3d001440381c42c00801c50703c03 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 144127248 1250 144125998 144126011
    0x50a0509030303100503070e070c03030513050f010507080601090308040510140d0f0614030c09060a08030d0b12030f040e070c081b06250503090102070c12031205040309090b030a0204 80
    0x4900b03040e13104c05940d8103400b1651541c0e40c8801e100305034030381170f116030380401d03020448940440d10a4014139401041c40c0340481d0201003560740d061034140000c42002c80c1d03964580a002440741e02c00b012a030010790900e8880c00d01410b50302d40b14038070b200d00d100300b0380300d2074210005407110b034040c100b0b1500100705c1010886d211445c07004900c003d0404000e402002c1841e09030046010800030603a0801d80202034001e160109038001480300100020381001c0c3e00415891001a000342c0810080070311003d00c00020070b9120003a42032021420340301d1440c2c21240c2052205030a10342c08602500c1c01c95038480189034040e02c0b804015183e50190250241481400141090035813909040111180045104480c1c183e502c8854030074a00480c030303042840c0b2441e006080c001c8180701e030000c0c0d82c1000642000610340052980c548044802560282505295040c3c22200317240e00003d414880781601c2005218602d025a0000e1910300c4a011704090181c0c0c0b040549200c0d10208014890f0079030242007084074 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 144128498 1250 144127248 144127261
    0x3181409041b03051c050a141303140d020c0a030803220c0906031109150105070305120f01170604111314190e07030b041e061404060e0102031006050a0509030303 71
    0x8030081c0d101e07155061018080c0c41505e0070b03ca2412107841110175940e08000c2980e19500c0e68590b8807130500c4010580120b1004408502c00d0100500c828608a005089041c40c01708060708022600c15011f2041c2c120b00c1d420408a44e050b403c4a520000350082a44a04200c07601c2c40f142c0d50702d020019107001ca58240124450b5007980c44074054038020602001580c40388000c0002d0943d00303c421520380203150100700c41c00d50280005e0a0920b2081c1030090a1026481401c600104d044801d40f420110304001084006c0c0c202c1d050729444207008014210610300b5031189411a110000210f000d40c0966103e0144002c40350b1080350755511149040c1c19608000b0b43d2414030000d4a0004810949040e4102401ca000000d0b10b5040740e5000d02c040200ba0303500c0c1c69001c000f6480d000006895450001c1501c0010b0061150030410181118a00c400d4140303420a2022211081d400c51500d80c41041446044144541e6081c1100ca992804965031148070008982c0ca010340980c0942500c004814400e4 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 144129748 1250 144128498 144128503
    0x20f0a0303050f09010203091b0a090906090b06120a030c21080106140a0c060903030b0603130519021e060f0408010906180b0c180901080a03181409041b0305 69
    0x1e010118012103454450304c2da070a080348410313100350b50a64807030111344910781741900c00001c1d80c0000402920a03a0b5036080b941095078501074007203030300b0742e40c400d0990100701a90082130b400442c00e036242c801400142d443c0541c1c034440000050140100220000200030101056103a00b07000f41c8841d040d00e85e500c1e0030183c1a0711080c06910081040000201d028010160550f4640210780e0365600407050b882e100c0200800e910541a8105a00d071034a0140c252034641c01940500c40ca43c0b03241c0b541d50304505281d410f1550071210030351000c81d100e1510000da171700c5410084201181b4410700780c01094117000900c1c980301e844000108000e011030b001480d1007040d4450504140a8942032101020f078914481400e0030402d030080c0000f080c40d0200708041e1286000e004a52003004004200301e049500240058001364000c0200341d001100480815511650910800c24034104030280181040c100900703c40307044511318024040f10b00002c1c1841491a021403080100303040e020703085511782c02d0182c0c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 144130998 1250 144129748 144129751
    0xb0409140f0d020609030f03150d120f0806100e1207080718360506190b040504081c14090a0201090b030603120901020309040c121406150a020f0a030305 67
    0x2146006841c009900140013080300b5104818000165150000c20943c07103541d80c06c0505400a42c3c0c0920741400c650391141101c049195010f410201040624550001c05503e44840520100f04030b8106101e515140c50b4048a00703a0746600702014902501070114000c0c91a480b0606110321645d0000650100d002c101007058550240084944980c420007402c16074840091443e04180d041c904842c48040c41c0440c4068892031001cac00032941016120030b4038080703050318175400202a00c122042c4c0880c1510504c00d0050059405001a2615860701e07a6a03002e2025020004030791580b000301d02c03940383e5000103031a0001c00b04940b05c505251350034a42d07a11304480100d000c552001c10106210201d42c0a0328400c41d002001010b6940e4540c2d051801c1c1c7d008589900d055200034410421079a0710f5005040d01c101d010394800403003100010088080e116003500380c02c9054209010300985803500102c80c00f01d0f4515014259440c452820120301e4009402005905402144000c00801d0303031580006 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 144132248 1250 144130998 144131023
    0x706150603140f15031005070f110109030801061209050a050a2a2108030a05090c040902060d0e030403080703020d120509031207020708031602040c020c130b040914 72
    0x70420761481c00d4036056001d070b0954501801001a10001d071240e150340040c041c0429001c3d09a03000f150b0907012020030360b001541c12201054009030504400c5a02c6080f8014070800c500013446042d4054901400031441801400100189401258054080e50f002602111340c800c3c101c50074460503017412600c880e0503150841d00741210442514950400c3c04a900c1c03110000a50203400380d14085282d4100b16007400c5840d004003e10240b04041000c040165124006040c40819540340c0900110f08240306151054811440c1c43c50703040160311080c0075240d0644c408403000034080c0d80909801e2450195920050500c0c40000d403000426a0108561402082c2d41c1c998502d00240c0b40800760680340c00b202d42030420350040c001c2c841915a40f0003041d07007108180c0165001ca90b107a138407060440d40008001014141c040a84004504283c440c1a42c1e0350341d2480902a04600100014011214401c2c00507c407602e8003c95001540c07250301452045500c0281c00600110440c42d1a843d01e800035080c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 144133498 1250 144132248 144132251
    0x10020708060105090105090c09040b06070f110301110a080406061a040906090c05090402030a0f150501140c07051002010b0904030c0b0901060b0316030902100306030b01080a050a080f0706150603 85
    0xb6013414a08400c80c1a02d40c001c10103d032079070f2010480b10440e0007161040d50702c15240c084c04030403038680b84000d0495038021418640400d0309820241e01c40f00c5042c0189009a24000b0142d1031450044181d0364100400c0c90804001d840301d0811501820042c2c00034081100e284c1200101c070f50003000180101c40c0c140b10140308503035480341506c0489688507d42c83c0810410410424240303410b500455111b10160300c0028140340010200b81110000080040c90041c4460305001541e001503044150300d100c0e00c00d26140589105002ea100d88552103694051000081d40200542c001e4115046000010301100c2c42894181001412a26103100544281400c070010550000c018028201643c40006003546191203541d400001a0744900780c40c030405075160020401a5a01004041110b07041d65003c55010300b9030400c079200700c1069009540c185d100d100954005100440ea040a550b0020005a29040b03407044c060400c0c03140308001808146402030f40e087d00c0080f402c21800780e0340030359030 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 144134748 1250 144133498 144133501
    0xf09080303010605121e1302010309050a03030209010e0a05150c07090c0503010614090d14120f19020d080415020c0d02010c020106210b04050109080f09030c0d0206190e1002070806 79
    0x2080413840c5031b402044030141881e1b02c0003490205442891441661044c580040c0e034950341d4440500b0b181c4010b104800294002981c01c00c3c0750fa10080038841c02404aa203405c6841c030303000001e14898100c01c900401c1c2600821761918040e01480094000c101003101440400309030200184140c0c003d00960b03021582451a0349030a000f9401031341c00010001d45042070708100c0740c03589161908150000301c1070340301310703081030480c4181c04018060240301080d02588443c98403a11400c0407840100b030070215449001c4940010fa07012901030b802a8200109100718031b41c00303400c1c00180c0708040c1d1f2010075100302003144400a50550109401d500d40d64000c020781902d03541d843d0079034142d04542805000c40804003501150704400d50fa600300340b04000004031300d640b079600d0a60a41117140305032005070001c203420711103007414484100ca41d04200c45150826800c0e50000301c2d240034038008040c5c25101d0298603024640244211031036003400034100415a03005c1c100c029650111402440200c0c0034440 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 144135998 1250 144134748 144134761
    0x40806061311090904050f0f01060e28020c03040f0b0d0501060f1409030102071205070b06031c08070e0909070305070f060f14121602010c02060402010f0f0908030301060512 76
    0x10448803071015442c441481c0900110401101c0c03070b07029005554074010540c054403041820010341c40f5001c0b0400010070034500d03241035611081001800c100144d0303520b148020703200401000003e10301d02c1340b600041e19a010560010b1442c015600a004600314045000c00d100680034041c1039910b40508062007a40c0e01d524048608500228503400865058940030a5882c074035405448054809400141806290307180c40810010540c40400464000550350080c400c0303108035540e1142050f001411200004810303001c03451041030010b0704020a81000c104403074415100403035640001841e00050b0706100110940703a00b0140700c100d039030707116080700010310b00c4004012204071501901c614454448100080c1c8950020302d0b899000c03003d04105540c0c00e0803040402e140100703181d1040c410240c1c400103000c0e003182c0c501c12644055600800c02c000c01030381d1001c49041c861403903240100d425000803005407910074560f003061500c0c2c00080000f0480380d0b0300c00068002d036042540d4040580d200d12 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 144137248 1250 144135998 144136001
    0x204050a09050c0f0d0c0b131e0902030c0c1f0b040b0907180807090209040c1805060c01020d0e01090308010e040c03110616060902010e06040e04060f0e030408060613 73
    0x3000b0711582050048043d5841c107403400001d80da00282c0b01416001c0c041d550b400c2d090320aa08260132001020424040c000b41071000e501c05440140810f41034286500024108a141e034458800f1030b81d0000009508103001078191900c01d00a2412280608401ca24006030302c80d40000040c0c03500d20b001001e0b10390340f40a00405040c944003503c414600d8035450811038182d5812100ca8211228080d000954003d080007510011701009900603294a03184042005960440854408002440340c0302e101081c1120103443c1210411214540d5446048080c1d501a00404a0300d00d41213150200100100324190400c0089c01c0c42070b664801e5aa8840d54907200100081e075004e44290300e8054103200007880010340c0d001a1100418036810b1030340b50143c5445803061604101c4a00d0303105c01c030410455800116010b404c1c90200c1d1158107107402c0c0040c1903000341c401030002c0e2603551100800484510230341d100124082d16101a00c1c2d07140e4a400e00c0035a502000e03601c85014074ac562111403001c4005 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 144138498 1250 144137248 144137261
    0x409140601030f110304020d051c08040510062102190b1b0d020312101511010c02031c0203060a030204090c030b0609060130060609090f020c06070c031403130204050a 73
    0x4c0c248880e00316212078080c00340102d015a004c4540703101d0341c01340344400ca0031910388500c481d85507900c6030742a2401d80352550a00c02c807840da07640214213108042c030407c8161030440b03101c151038030600c94001c1c25500000b04451586200d18411000016010542c1c110030001004801e814003011400c140110080075904d035800081003005810038804107800c018520b103c6600320790350784408017030107840d5000c050368604082c0380403020409461054160030028012000b07040340034000340d400e0440500705100c011001030000618241d00000181140d038a07035403c0400340d50090f200b00890011441c0c01508100903000c01c0d500002c8020000e6441c1c0740003c9407612850701a503401b103842403078001c000410009140e0f40c40c00a2a000164104071103184900301c018080e5540704152103142c000940b01310b071031856030000f980b40104100c040c103071800610a50401000e2412400039049401c0441b500d284031001da55a00000000384165207840c080352f000030600032130b0100181d45039919508100d641 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 144139748 1250 144138498 144138521
    0x8040f14060717030a090204110a02010524060715050a02070212030301210503070f0b01051513030b0603120a020a021305040b070f05070f0c032a0e07050409140601030f 74
    0x3003d03148044545050702c007039a0065070070b04c4d010865010990009043da014241090b8003100085901483c144e8240181604424101030f14600800345100041140d08281c861a00441000540404010360040580b8001c1e015840070052404c2210201c000303540400c0d82a07104088070000d050000031702004881c100e400141510031680b07050001c01c0b0158011003810307034040c00140b1401001c158000002c10703e0314410310980d0800d41c140030401c9121584101510240c1100f403100d0514001c443d1000410340307401c58011219507031b42000181c170301006100c9110b2001c8000ca91418220740028886002c3c5100b1038102c1890030240484008803281168041e01c05040400403030201d034011400c4201c04c1e1564074201e40380012a441d526a02540c2403412103001440c15000c005001c07036805200c1d4240f044000e55080030702c40c0812150240078a001e4a9050104240454078450045040390010500c00e0001c1c000e0810480d4900021981294010702003401c0c5000203160800c54070071355039180b9 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 144140998 1250 144139748 144139763
    0x60b07030f1b02100908010504061d010204030b0606090a0302030a050d09060f120e010605060c070317071a06060405090123100504260304151107150f0c08040f140607 73
    0x402c2c6400b00314003d0702d08482c40b014002140c03004980302030280201ba10442c000c0b94040340702500b400709040721070700702c5c82a4046644184002d00008120050a0f900700074215021603c5043c0c600020300c401201d54402503261280e0780204082110115811000801c1915840b985a540d400c0542e6402101c0440a0010b2003801e01d40c141103031298040741c0005040e0000007181a1120089002c551010a100039107a10a0004008020310500202120700d5007035a418103005465542440806000700c664003201480d0000524a032078841c20796009003401443c4001950752884d10401c03000c02c17038218607810704640080690034103108216a0b0f0446156403400d141c00c0c5043c80070500031590101034066442c0e105041d41180f45c0800250000c5c0021907051034a03500f0325030014080102000c20b0050a4000d85c031704200036501d02011100d80295824100001c07280c91504403010038005800904020000c40d010451400e480001000c1d90801f061f01b0340314045201c10003101d800f402034000c0800 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 144142248 1250 144140998 144141047
    0x60501031a04020d0f020417061302010e130908190305090604051209060c010219120b06030c030403050c0703050c0f09010e06010c020303040b0403050105040b0c131401090801060b07030f 82
    0x14180b983c020b080360004868001145040d205e00075059900030381c003000c3c1a8100c10402038018800740241c40c3c0101c0d607403008086245041d400600b07200020308240d4416180034030b0401040100d42c01002105500140c041d40e122281c84515401032103d400000000380741c400020034400000902c9405207402c80000d081f94030388001c0340301c2280e1003601c005801040a00544c50891000d00141490548640c640d100b1805017000003401800c0e068000020142403a031407454540b23845040325040303581c0c51030a030717074030b035298141a80c0b5441800000b8000d481541030000a0180c0410500c6416000300d510703c0220044004000e15148207010ba038144203a207801040c40f96000f00d01e0b001c5d007035201400382c07410b03d9695004000070341c005d035009588903515001008204101655102e90141400080e142800900c44050501c521a0301603000d428810340203e100c00e82c040c0c2c40d8400107160b203000a000d403d80707030303161214140c1050004a001c6442e5023000c5541d0b6020b84003161890f400c254800900 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 144143498 1250 144142248 144142301
    0x1308060603120a030b0d0c030b0c0301060905090c0f180a06020123070c1203060e0a020a0c02040b2214060f090c0f0409320903071b0504051906050103 66
    0x80e0f840074103100203055643e02c00142e40c4d00c5e40425445224001c0d010320300f1941c550b007880c1010440080c00c0f5034914100308018031090385c00c05040c00545105868030390603940c44545d00100c910854201c140d80f0600402c003501f00c0000340584090420090b1008108141c0d107500030390a8420740030100031080d41109840c034901d607041c0400e650100043c03900300514111034440100b804400496140042e07200d14060140c44008141d254221289100461400400407801080c0004042000b4403030760300c510070039101d50b55903845400d00750034803c01e0000e5110584540001045008803d4031548400c00000b1404d00d0041038108155102401031106a99803252034500307036000c1000425071040c10300010504190320320410080c4c01010f00d411000620603000080701c08094000514641410000c00c868010302000b40da00407540803031017030709440740c80d84c1409405145402080d0044d2400041064511007084a600a5061010b04020407504c071001182500c080621400541c807104080044 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 144144748 1250 144143498 144143533
    0x13080a030f0311040b0f04030204180b07020309090a050a060504020a0201090506010e040206070209090a050a12020c0a0f06030906090503070b061201020a090b031f0b0a0201060905151005040801020409021308060603 94
    0x41c6c0310b801062981c80d1580341e5000504543c842c504105401700030f440c1203c00c00111660319900310030a40000d500703013100800000d040190061001400c141c07114080384020455030802c4015100040040d5210455131100900030300e20340d503055a41e881002d0000418814059045002da130300502040d151110300c1c2c00380011507002038400285031041e44620004075205022202c8402c2c4582000402d0620401009162142503406184144c031126005c04c022030ba00d03102c541c2218060f0070045882001814084000c10001c1809401400001440d03070070400140c0c0010311401341180c0c0764480a0490840c2402c03401030700c0001c008650440824011146000041d40c2c2c4210041c850503400d9104440200c3c2652141d40712203951400881e540f03121640a00a903405441400e50410051030401e00c85180310804003582801650100d80144800b4071500440e8080c0051000030741d5200d61700d002803c025440b815011001c080c0d0b8540200d44480c011a01c240102d2004006120310f103001d000914 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 144145998 1250 144144748 144144757
    0x30a0f02010c06020706020d0b04050f0402010f121b020706090f060c020a080109120806060a08010b07030306081203060a09090222020405150903012a050f13080a030f0311040b 77
    0x7414800040100c100140d6075000800e440e9225403009030712500461507000a9448502c0d4191080b400c104c10000c40c0c1035402d030b4140d4484e030240380a104551001c5000c0c2c40e510908c441103e180303410042d00032116040078882000c049019402c44100560b41c1070219085106c501a039a1740309800001008914410041e940006d070006007400c48070366a4040740c908480341458100d0301d040c0400241c40300d00b0341050180d80e0246082e21524502004030400402c0e41205015142400e0000708110050510079403141001d050854203da01d0b5100ba0b480d1b030300b000c0d002290181e102c2c1c011a2408640c01c24240592140164064950040c06072a41d0f20361991030030910f41403011642c244030000c1c0c55695040185100301441030050ba5071070400081c0360079112080e0510b1003031080100198100e088409504035450185e00d0106e8a030301c61190701100501c41c0c509030295030303881c45002094020005c80e0f00c0110364401d0310340c400a823a52400a40694901c2c000c440e50890041c041004014050b40051 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 144147248 1250 144145998 144146003
    0x9031104020405041404020316051014090603090a052b0e0301090204150f0503060c03010302210a210e0306010b090d0206030705130614030a0b120601062c030a0f 71
    0x3600b042d8031040801c08407469030240381c3d00120020280019800c051150b240b100484a01032100349041034042850b890348028200704120303c001c1c4040800310b442e41035a07280c8000401081e07490604e6a061617461441200c140d03054003403c80315018a03120340c144011540340c054110414651484010382e00b03084030200d0140c05548441c02c9500603501c52289100c01b802000c40c4920a509042c1d04034140803554012901a5000da0140a0500c2c09802603904583c5d0440d158107408a99101c0c0e180010080c451074901c5101b80301d05c2e0000c0000d051507120603400c58400308400c1c1500c400b8120703084180c076010302c3e4040e0000401808090800e0303005048400b406000b91800c5481c560104865a20440c1c032000001c0300414048842070840319404010011072500611007003000c0340c40e4610348000740072041c01c550f44408807122501d0340b40c040c261000b000c1e41612080c0d0b07510300c8060040320302c0d08442411068040c180c5514922099051811480094000c03c7c41144942e0758035800c5026901c01d = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 144148498 1250 144147248 144147251
    0x8012102040b180108031305120601030f08070b161409090103030e01032a090503060c04261e0c01020712200a0906050901050907120903052101030c0602070609031104 73
    0x5544800f126500321030f0080c41070304021643d0360124061107e07140410b410591049410044024114400244c00303410f4903000140c0a0040b815480c00c110309101d40302d401051185410b08010241c1042d11040d000600240c84c0c2c070708250152044dc1020344242c44020740d0101c4040010300c08244203407000d981008040c140043c001d00c0b001400401c044400c19164101c1e1408210788204d01c0e40500b00c00d00415098004050504090111200c54041c1e07020341003822894900c40047e40d51045040100a642d100c103441802e2203028150300420008581c90300b02d88a1103c1007000c40d44005100001c0342c1070345c801109034610030703950b00c115400022448020000c0d40340c0408015170b503080090703004004046000403681c0c9403c0510115810503400315102d207076442c003000501c070f4200340d02000010050b0300004409619240548803801445001d600250010300826510903002000c40d060340d0040340c0341f0442550b601c100b03ea4890307540c094940020081c00081000a0130a00c040c0040980180b0 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 144149748 1250 144148498 144148519
    0x41217130b091c2112021810090b180a0906030b0a05160516020414070207080f19030e01090305031c0f05090a02090a140423070b040605160b01080c0108012102040b 72
    0x80217010307608200ca40c0503006402562110700c0f0303c0c0004900700214110306040f24010326200d5220140d00540c2c0e00d90164a0341c00105060640d03442c09a0409049602c0041000d1a140e00f4200c1680104a903002c1402e4a0540880c40c9000c242900d41c03403180c81603483d01d02e041c480c201000040c480c501e80481e00306858a2103070801c4842c0d00007240c0b044041e6401040304500d8943c106e864520300c41d81c00103039500000d1109d203008611504400141d074150a160110580c1e442c0101c1d81a0103d900142203408003140400c0b540003140441194800c1001c0c013406505101051601118400d0711036082e998882e1000f00018100066410383c060400c02000800d17450700400b00015450450b4115484040e01c40712054040362410390140c900c000c000202091420104041d049d4416406003006004001c0384410600c8190380520f0a210790000300ca20455a5070200e00355103180c00e82800c0c1c045003440c1d0000c90402160b004050b08100842c000310710300d0a0329000d01004140072080182c00c20021803 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 144150998 1250 144149748 144149777
    0x10f030b030d030b1005031605030c12070203030a0b010207051c08070501051f0e060a030b0a06050d12021c0e0d0311060906011703041217130b091c21 66
    0x45450316100d9200407454004a404010b417600c0d0900003c02402018414490164407500d103030004c81c4040e06105903240c48040c4055114001d4015070329410005400300800350341d01101840c069071404c3c501340000031480005a844085a004080d00109280644140b01880c5c80c4050025802401c8451a0841a03142c0314250b9070122000c1d04100d03014541c2d410f10343c0707080c40d54500400300044081c0103400c00380001500c0c01c44c1381c031003e8401c1c84464003007445005071b60720070001820f00400b00711580f0051b1800e18000c0d6450401d600142c01050328152a90041202100020130f0079501c1d0409100100100082850b8403441035042090003c0190503505007041440d001c4e1307120340000d003032961400759091a17034007440a004145810a101c20003c6070700b03803014040c4141c0e004940d039542d03080d01c21074103445008800c208100505400130010b070030200c540091041800c16222030b101c92a141007540c14016110900810080007030303281c41ca20303210800c00d8a0501c4544d01d04001c070985a41d = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 144152248 1250 144150998 144151003
    0xf0d0207080301060203071a040b0403110c03160f0b030106020a1202011b0503040b0604060b0711120303190b220504050c0603241008010312110307030806040e1b010f030b03 76
    0x1340c0055025900000b5010140403444010700540072480d00151200d01d095603e0a03a4000060401002d01a074104d1010740e1803400c1c0241c0420182c090200d0302c600a6042113042c040300741d445030611250f850140032a950b40d100701100d058400540050285c551643d07a10000d420101c16078004656894900d9840c9010f401402c0402451076610b064603824181414452404003405040c811440c0400401011a091054404107904021140c60700b240c1030022038030f00307127401d203c01c080d0740000400c1001ca600a48829000e00c51001c0c41080825000000e0007040d00b00c1600f00d072031050b10164503466920560f0842d036031191062054410700c0b818980825415081a0380d003c444c241078581d600100202162403071500c0c101151300440580d8800c6010340542c2041c00003a1891580305580385c02d0a01400720000400d2040d8100da944160310b040003450340c0d10942c0c003d4491810044207200f54180012204560214485001114900d24005503159400d41001d10245900d4503404100d5030750a = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 144153498 1250 144152248 144152251
    0x41b090c030b0102190b2701021908070c03170403050904050705091003090b010e0705040b070c0501030612051c0c020a0312020c06130e060f2d04020408030f0d02070803 74
    0x16100031400c2c02025001909003c1080340840340c0005521030790003c128012003882d00001d21030545d840844002440c1c034210415111a10025030000406241c00350395112019110b403819a922202c0d911403200c12144041c213021b025000414050540340c1c18240c0200c041d40151007820018581b01d151004a402c0d45e4044030b000340030a402054805183c10b000e2800c041e41481482d0412180ba5907076a103825100040c0192201c660318100055440350180c1d00329805082c4007015540c503071425143c0074042201d140269800607080000000d12000e01700400c141966109021344213030300800d03016100c1840059061f17002c00c60a01100805a00d980c0710010186000b044e900311103502c1000003a203060240c2105600403142080010040614100000151000340a204c2d00640350b81000030040007040d8200e90b409665422000145034804816007554007020311122107404804c41000100d001e00d21440c940c9800c20483c2d2030140d04c5403001010780d806070900050a00e42e10b9241e404440c0c00 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 144154748 1250 144153498 144153521
    0x70516030c03021c0c140c180a0b060301150804030e060a05070506010e09070e0a020f19030501080d0c140a0606080609010609061d13050105070e1503060108041b09 72
    0x400c007401803603410700c8401c3c031080129490324401200d110005248aa070201c02815a07412041e0351090007105000a018401004088014841a5004020100310207803026074000b454810007944a0404030281c034102d846000154034004c1d4003440a440c2501c0c010700440030031030b10182c1d0320195500c44010b08041c0f07601d035940c1621880c1c10300e04540fa21006030440d80442c10716400700030301858001414802d5518295202c402625581c405c0c4002e8040c141e03101c081c55001054407414105440c4c01d004001b0b60b269800d0000380d80c0c42c2a8291907658003411000001c1c100f50140c03001c0f40b015540c1100d4200755200305c5000c2c03685920344800b00c80f0309420050854102506004a8000074003d52000d4040307214100a001e281200540304070381911411041c0e48180c41c0015540f030300408011042d00d400000a000760300c1c000900901218800b100c070f5104500383d0311500801c162041c02d90348030b524183c44405440e201c0784c41d42c14182c2e813110071068000000c201e0103d040417603801601120741 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 144155998 1250 144154748 144154757
    0x12030307120608010506060306060c070b04060c02040f2a12150303080f0123012d180e06010c0f0f0507030c0504020c070902090406080304030c05040e031207030507051603 75
    0xd100c00301e10a440d010391000030742d03a050105101241c0c1e0740c001102e4012400320f83e032030340d2219903202c0e80381048042c0d400598220b501050005502da000300714142620b100b140e0030042105a0303900740e07041b60341c0c64010101000001d1041c00c00245600f82030207183c422414403002000c00144007105a907140401040301c1c0d140588200b0416801004d41c1350170446031030700c030561581028004200700342d8440d40c450012840f1034a175021640034401808a0106c11007245040ca40900040d11560249100c2c000001e2001d041d43c0714140396071113418007505c007502c15040b819202d550045510240c841c07429100c6903a460580b10005001c1000d82c2601d41c821005481814a9030401054041080d403025005600402c44d26800d0344000c1040c03825100103040c0182c65642a04c04034006254980002c10782d80300014020041c0003094541038102d0b182102c0602407500195015500c9002c0d0140f005a50b09070300740409d046900076040581d0107410b910b022810100320101005240a40210030350105 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 144157248 1250 144155998 144156017
    0x120e031603021809030f09210a0b010807030f08031b04121101110d081005030708060a06050a030c06050d1803050901120c0f052a030c100501060c020f12030307 70
    0x18180420040c415000650039842c5034640310004da138072841744529848840380c0005100200780e03250807641d0b60a44c013500000c54502d10500a056454440b410144c924080d84400050300020028105040c3c960003854050507031403d0f995a892601301510002d428203015189640c03124990018000502e03140c0701243c48003001c1c0c10188401c01c0000366090401c208440601e5603540b000901942c0c401a6240844640d5144125017100b444142c20035a07141c024800e000441190000380d850040b04454410801e1641d070708200280d9040500c4001c2004200310010000180640080c0c10034265481c0c1c0800d0482c0c400b000400d00740884002100840c1c4040346080d440c0d44c0c0402010034038004028204451061082d01811002400402c0070800200080c0807216081c4042c04a250040c104600a8003215201d6495101d400a441c944028400d18165041103010740c041d881c12941035880b61891050144c0901000100e003243c641c0c0c000780810095420040700700000c0d40304654030354800041 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 144158498 1250 144157248 144157253
    0x10608121809010e0408090307170109051c02060c0307030e07030807030215090c13230105010f0503071d010309020310020414030309060f0901180303230a0c120e031603 74
    0x11107a24204441c05190220014007083c00c00c0c010072604640c00c240328a07110130420300001d01c2e1000b01d0f0058440c02c914285141150070054100046407840350050399594032205078132040050070b03010710800580c8820082040c50031000c0c011900711f0a00e00c4e021504008070700380c6500d0b110300ea600440d41348800241e468181541480b01c03a03071150040039988103600300186920f58805d00c59010503c60a520a409410007150368031400b19410620100300350310b00b5140301d03811154000d103d007070b0225a880c02c1c80300a4a12507000c036031040e6601c0d143c0403166025101203030f41701d00415000905166a130b4480001507902001899510043c1401c0540c0d00c1e070030010300c00010380d9001d034420b000750b00a001c0001c1954a81e001c0e0340e10900d4a00c0710350703150001f18004803001180712440c8030744156106004024158483e44d0050140d000a101405070a04190b19828620031519180f0000300c40045080000703d0b07032080e55100c2000c1e4580791034a0017043c00041d0802c0e00b00001c4268030303140e0741c404104 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 144159748 1250 144158498 144158527
    0x1e030c07030314040f0605071214040c121203091502031006030606020f06151507061b1b240c020105041b030203060f060301060308270307051003050901060812 70
    0x7240e42600026011420155030760301e0900d0860304006d14041c3c40c0e00004985500c6a440c2200e01143c01d80d090248004119052030558400c0d030b019602074081c0c4402041c24082d42e4112044164491031030314030318000315001c900416000200f02c2d5400116548040d40310380500142d07000348c10310620385036121307e040310182c110b40b40f81e48000b0964100e003043c0301c689040411500d070300610703070744400c0101d00300b400000c0d01240248203090200d0b00080b03551301c24000594008480d401c1e944045c0c0280e504810020740e0391050110040340350401c0c1058102c00551078521003407400c0c000020404108041000f032000340c0e03c008401c4030060392350340100300c140700a140c80c414140d1524145544ca181c1140c02080e100c450007041c42070f400c210311011800689013544600b00642d0805002911086c102000d80800e5026809009000391040a501c0c4540f83c0421840c01301c0710300600001c2e004c0061101a405010010040e140c295614400000d00b41d030f061141e03141c07141c0d562500a035070344d080219204 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 144160998 1250 144159748 144159761
    0xb0a05060705030903011b0f0e240304050c01030902060405061810030c090b040e06010807110601030803010311040b010f030f020904050702150703022a031e03180606030a03051e030c070303 83
    0x14211f49850a20070540f6030400020441c0c0007d615044440104840c04200003544000410307810565050351141c03002c19850246015601c80d10580d40c0d20780b108801102564141c07400030758001e0023000f080200b0314009000300050001229102c3c5218403000018818414040600b8082512400300403c03081e4041c0904c005480015951403e0606203c60155240401020a03050021080208215078000c070058882c403410f00c0101c6415686030300e00301c0d00d943c1081c4000c88114031860b060680030b00e800d0080c42001081079460921403803103090220090100118051940d079800c20000002c0d03151401154402e1585400900090441415000e41000014085000c261050107003080411040c2040c10100402506401680220b4001340741184070b00d80b80c0c102c0c0035020740c80110740c200080d1301551060355603440f044005c400001e070301034541208580290749030b0004002880042e00400180292180e20803c000c03101510181d04030840c0d009407101e08903d94041a024101581030142c02c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 144162248 1250 144160998 144161021
    0x2070b030c04031b0306020a0906030b04020c060c0904020c0714010818060115210b040b01020d051209070f0602010e071202010e130e07032607080301090b0a0506070503090301 77
    0x54694030702040e11a1070750096000082c003a42c03a84204024011580004001031508080110347d2440700120103406444030340b181c2c0001c01c0c1030200f41803c0d0b00e030600c00c1e9400045000094a020758405e0510181070703024040d8294090390921002d0581c502c200444800750003020756215180100000140c8030800090180000302d100780e0321058200404106541101d00d40848890380e9091104241d88040c910703050f501c450312030700c0c0005200c1d0540d600302e40390b03000e0b050702c0800c101c03071400d001240c07a83e005a03800e20128604020600103840ea80f49401d40c01211141541e0007170351200001c080e03441c041d034000f1006070f45641204540707000a004c3c00006040c04d05140c040e17902c4940c0003801e41302000d20414031411206035402448003a47c2c002442444d0050b05542500e070b2a45441203140a50712040f42014040504401c0010300c60303411108075542080f0440e045a103072100c4100981a03800010350000c1c030220001606456241c054000e20f07216002070b584488601c01407508645400885 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 144163498 1250 144162248 144162269
    0x40801060909050d0f0c140604110102010606230c0312150915011b02120a060f06120210030608060f01030b1614070f020901060201051801060b120402010c061b0207 72
    0x42e90001d000001c003255461024100162201584a000d6900b601d10801c0501b06040c280740015a02e00301003003c0d4412071140038a035495050b076100490881e0b81a006081c08240c081d000e00c0410301b100150f101c58460005c00b001d04d8095001c500034110f820042c103289120030382401340002c00c40a400070700c07214281510004058904140014547c0054210319418400c1c0015081529001c958140f40025006814a02800f01081d450341d90358520002c240d452034030300003401d1074841f0940101400c49090341d03001400b465941c0c0822440000241c00c1c0c005156451200050300ca800b80500340c0300700964100c03280130758511b06146c440c08600410121034019100c00c1085480d030002000f8000328032504d00b80ea214400c501c2c007100f040d02c4a401c0030b13502001035400000c24642c150403841c03051600301d160440000300682114203840e641e00403e011002e0a01946119040b903521711079000d80145019076944400d9111641101c0034040306858045100c4405404a074040000760001c00440d5031 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 144164748 1250 144163498 144163511
    0x105071b08030f150a0303200601150806030703061415090402090403050c03070602030a09110a060203070213021207030b0a080c0a09090c080d0201050108060c040b03150a0801020a050408010609 85
    0x2030705065440300500c42401a01000f011400a0499030b1203000700d81c0c1c014001c0030186460741006007141208801d00d492000991008102000c004074802e412580c0204000c400e01d290340509072900c001c018405905403203003030700c004085083c50207000003e00c43c1c8500819036090100306640721442da00c0d0018040d00101c014080180c40c0c64000c00c0e445509864801e4030303111100b085908500c100e407009081c090011050001e041c041d98005000303148164031210300240184103000c0c05100da07103e40d0f00980c106110b22009400c254412120402d02c1d058010302d0940042807078405a1030076038050000039a184107080041c1807a1a454000e800c07a10700510020340d4483c0010504100381c00760f41855626101c2c444100023030014100054203240b4250399044940000090082c41c0c01d100b00e280a1141c40c011402c02d081c1c1c9822201034582e02d50f0618507581d03600300c515040f00c29011540b504183d0365200046e9912003840035185600c4181c1d11036950b42c1c070f01a46a42920010f0b0400c0703c1d480d03c2c090 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 144165998 1250 144164748 144164753
    0x90c020618010b04110301050f0405010e040f0303140c09010207080610030f110a0e040506010905040b150114030709060815012705060d020301030218071b11030307050105071b 77
    0x3035950360200181503500700403070003158010701400c84030142c0d5401c6401d0000a082d43e461034406103042c0e030021359441c610080004104800e8500a20507110950080404500410002081400078502030306000c68541e200420071483c00c84210f1f020b284c030783d00120b58111951303818445a00284680c0f0020602070410303802c09070040d002440b006141c001f04910360002c01087d04c0b000f80901c20001d00d80e40c840c507501e41000340745401c200d90440c0d681c010b90300003080030040e901c6001c3c0999001035840f081a178444a0406501c6131004900b41800103504421060441040c02184502c40d1541c60f02c202c203250a030041c060b0032010300350b0466121004149030303169134402080420044c4d13101002215800000b21080960003030380000f500030600054204100301c6030b4004604a03407007600c2c406052024140c02412601e01651160000741100c03819021802414911078840781c06140303040d019004950020746150b01507030007150750344d4449041141a641044030800c1c88407803d44545089034203035 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 144167248 1250 144165998 144166003
    0xa1d071d010e1504091b02060103030906050306030c03100b030f0a0f06020a17070c030f170c0a030209180103170a0804060507030f0e010f050705070215090d0c0e010f090c02 76
    0x64103541002004185149141c0d1004440000000c0003c4040d0740c464549401070040d0150a0084101011048a60407403a100082d4a4102e90f00356807840000c03410b102d000c480c3c5a20180903141d051207440d260804940d820700c849680c0410b486400205030050300f06042c201500580c0300500703074020b1640b1502090401c0300020101b54004001655056409400c0d1065052140c03801d00d4000144100041550030200c2224254003075120424054000c81c42192040080c0b00031190613100c28001c40e1402110314040e090500d228280541400030781c0c2c004c07510025a0000710415409460010420300200d0001801c8910701c504000f4508140b806001e0a0144003500c003e2280b9a1040016100c1d4030035840b00d01144442c01c024003420114060260280440d40380300036078203142402241d6090700540c21624466800340614905128800414105800000b20240c1010320324801400007403024041e940a001105c040d100554100070070040c0001e080d410a20500b45007030202c90750340c2d800 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 144168498 1250 144167248 144167297
    0x5150a0506090111120c070b0913110409020706020409050105030f06040f030c1a0711032a0109020613060305070c020604032907020106050321160602090a1d07 70
    0x103550742582c90400c1c000403034290b2180d01a07500103009078803201c030007002c0340342c02032510050304d004441650f030725011050b00d00e2040c03160941c1d00001c0800d000d9a002e1ba5500000010036080d0022810599114244002d81e0b20600e4225403041d030004e0207100b076906034030a16000d44803d900808100e6039000758569214000741c40034004c033360418800010948148044a01d81d6400088404142e000000d0f6400c0c000c2e040e20f041d00420f2040da44800c41d02d00010544d101d07944807a0b40c030310300305640001c02035203124401e14012642d52110116800740e1a00401403929100321220500005c0c0341200060481c0e001a02600c204036103c0080b03000342e5640b8080d035060b6078000300e0810040c00d629040358407607070050049514100b445400c00111580650200c02103480607025106031401d17800701c014175800c40c0f03106a00000d000784a4108280c07000d50034042550b200d10801480c000034100010700b42e2003035600880425002c0304480c2d003025905d6245075040304039400c0c1400326003898100440c55000 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 144169748 1250 144168498 144168509
    0x90e090718020408070603051501030e07090c02100e070512191101020129010306060e090412260601320c0c0a090e0601080307050c090a0f0c0e0405150a 67
    0x1d0001c00c1040d0100e56812240200100f4086513405651000080c01411003151580440041d000031524254000e002e885105041100038000503414020800000c1062403640811842030340240198143e90b40f15803121102c0d54001400898600010040040740c940c60440700c40d000300d448001c4902e40d50341100d0f0031940c80b4500b442055800c00041b40144548210481c40310240c01045d5109890121401c00d00d66080e43c082c02295103400e0152120b11200e01040d80250800b00040e0202d4084c10039a030728002c0900d00151311400b2884020041a10001c14041a00700c42045c07040d95071700700400c0d45454100440d82c0314070002200d48900404c0003100c900b400c0c03880000c3e02d000784003424404e090b123100d00100551a603e8036001c02c2c0004084840b02d00744d59118820000c01d0030100001030b030b480194003a00030550214910140b2100c454050700c803485490711144a0042640d031401240407041003640c0310301603080404100300c00c2d0b4001030409110000d01070b00d511140d803a4908010305844 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 144170998 1250 144169748 144169769
    0x417120a05090d05060f06040506150f0c121309060e01150e21011a01050f0724020c030903010b0406050102070504050c0c01051801050a05060f0907111b01090e0907 72
    0x2c910010414088a1103002811401028100494804d44074201806010700f55030811169580c3d01c140110190780701c06041d90406d00780800140491848010148480e1000a4800d0105c04428001341d0b50008401a45002c04804003444450002c4c030030301c0001d00002c0002e46e4294500100b1401e800d60781c1f03101d44100039641e40c02140c0c83d120301400d0301045e003608002d4101d00760300b00500c034000c2c01c51418000200508055038031856102e1810740d80402c00c92042240341c1042d0f9a03c0c00485030810014540384490740c09004209081031001e001f4001d8240c010710b03a51a126400c050849001314803051041c2d20f4560140800d90380003800d0810f03142c05440009440d210a003040388240036400f0f40c46401c3d8240340420031042101c030400e06400c900320000b84455201c070344212303050381c3c0300300c0c0e00f00d40200e1580540307015494040803068200707a15042c10b403c802c240c407881e83e08002003503443e61401110a030382041e4a581c4450414003d105d0310100d00309904203161401e8603641603118061010 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 144172248 1250 144170998 144171007
    0x30614060318060c04051905092403030a090918081b03040b0a02240c0304080702010e031c020d0309050d050c1509070302130c08062b080417120a05 65
    0x41c00d2603090503001e10310b240c1101d0302031422660008082d8014010203024200005180781811001a645000d8480040c44800103640785445081d041044907075482c11414603140080160720144001c12400e80d4590341c550f182070030100d10300182c0305080034042505840008410100d40c410702607900706031900c5001001003101360304140c030b07501031900030701c50030080003982c05111900090312014007943c100030803003200203000051100c0b190031075004613180b10800004002840c894010403035144141007603142c81c0c01e0640440c2c504100c00306e0700031154295188510f003c940400080c0b0061449150901c00b400e442c1d55425203c0031818034400c1400000b0944d18204503003804114040300300c840300c0800f146012107980f65a04d22500c41039008900d150200c02800c00360380078070f40182c070007901c5680d020b131115001d11030072060105035020340040d000454506a00701c0d2850351400303802018007580325824072080044c080e00c0e040c001d92407648841e02c0d56608c1300b94035060f500e40d1041810240c1c2c0350f = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 144173498 1250 144172248 144172261
    0xd020a0816020306010e010603050f010303270e0f090f0109020f0d02060702190501030f0209060a0f030b030118060506040209011b020303040e130510051e0a0e0307030c03020d0306140603 82
    0x16031201d0009615000b1000003054010035403241504072030460b90240040d03140c0c0c080c0805071001c03c0c04003800003080780c1e81e00d03a0015000f0004c41001003001400c201d050341e4070004020b000780140c804070303900441c28051245051082002c3c0469030760440080240c81d01741d50004103103070715500055010700901008401550345240982d40c102da0060060702945041d1880d0301c0172002d4502415005c02e00d0034010a040552503c00d44001c403070f02501203450180c60b050180d5003249103041c80010180c654407010620f440038010340504504440f058142c9900701d203025070613504002d010741e00683c41403144100c40d0780d0080741100c0481240c983c1ca102c0d242d81e800840c3c1148501d400829640e120300d001d0054200b51180e044001b1030043c42030f540d0710150202c408042c0c603020355280203800710b845e030041c203819585507521390000400e07203000620086412506056800c0b41d4001c1e000b2400201512041c160144951810104a0f10381080340034100501c0440d0400c854019502075840400000c50 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 144174748 1250 144173498 144173527
    0x2041404230405030a0206090d080403030f150602030408012901230a080105190f0b0a021c0206040b011502030313020f04060e01091a1c050a0804120b06030d020a08 72
    0xc0c001414201407009160034140165a0750211310310030300520402c000610b2600d00420318070480281c964490009407a9a18110090200c0c24000d511142c2d6919142c41c2403042c0050610040031203801440d2183e03e40514942103900d1022804206401120b05042e50140e01d6503400d0841d00900703040340b191070240a46441203031240d0786900480b10000c0c440b1101500903003958100d640c01c807100110306ea101c280440c0030503400d104401407405000d105100a41249001d0021140b0502c111000d035000c00c0240900100151396034030140e0401e009220600c44121603190141c500c4ca003600703400c8141100001c0d568880100246606160100d0034011036648904405034040000e200f840096144c003048401c1101c280b0590700750521b40210000e050020006076040e45100400010060010046000c29000c101a04507140e02414a10030000340716000503101801600310303148800e20491829004080300504001d100c1e901030030301c646249600051207003800781c1c4406125190102c0d509002e5 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 144175998 1250 144174748 144174791
    0xc0a080c0706050a02120901091a0c0913020a0f050c150c0c06070201051f030f0206160c1202010930050c0409060509060604090203030f18090a0f0506010302041404 72
    0x1403820b800c00003130181042c402d8000c2c5c40400c0d4040548540d64442104103406c91701520300043c428920082002513000d4103207441640320702c40781c00040c60720780707503500049010066660000e04607901080c1260390580c0282d8541008040c1c0c01c0551401c1008645240d40380e0349806242c022580032030000302490baa0005032028903c1240494220b82858040a400f03001c080351031b00805068646040840c62100040104580e08803401401c000543d0f000d1180542c13008141e09513210401c519800090066140d6000500200c42c3c680c44902d402d200042c046d035040c0e800300b0640007140c0110204503803902d03100c1c5a211341c2a044460f041c807552030f109042010381405030346d005141c0700c81c0505100c001d0f0402d910810942055680c19940d03c42000200ca051540184d0076030f0040c4040460180000000c1c852103014504d009811602c000010ba0070401c1124200111500c03800b4103919034100740121034200d0001d0905505040c2040900c00310f0040c4030b2109441940c4030ba8050301500504000700307 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 144177248 1250 144175998 144176003
    0x40b0c0106050a0b0904050606090d0303020304020d0804240206070504050d110913060501120506130302010f180b0f0c090d021309240b0303030703090203010b03060106030f060e0c0a080c07 83
    0x43c81240c3d07a4200c0c0800c5030008020203000310304140000308649454401c0b200f8400c001030100e03a03102c1080c0ca0860094200a000301d0700080c6801007100880c11040141006000c0791117860681c0c424008600f100c0c1606219070707400d40d4403200501c00c140f40c000707040d64241c40c41954480d80300720641c10030b0845030110b80c4141d0b0300440c1420500c0300e4007200c615840441030281c48140105d90b07813200c080f001c1b4141c0400c00b52072a001500803640c90881c040d02400290b0081c030001c5441409611a041129100a00c0048002c0b50300031035030420a081140c0e56001b200d074541380c961851304410f031000d03d02c07425132a91f100d449543c9248003155030b20540025402c080717140070040f0f48114642011a111105003289100c0303080e54041030300c1001130040d207a082402a0145065842c2c20700160081c1c103800c5000c030303855501d40705003108684041000354002c0072180d07004a101e00e00700080004560054001003038815070082003050f0300c50b807142110303d04072040c502580c0343c1c4d0b50001e1400c058040d10000 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 144178498 1250 144177248 144177259
    0x503190e1e031501090507021b0a060320030703060e060f102114010504060e01030309050f060c0d030c0909090309030209090f070b210118051005060d020705010b0a03020105040b0c010605 82
    0x1050003c005c2c6c0c010b5104030070310f030200c5405200301d0031150160010103400d1588001100414006180b09400c040c007000c41d000c5220907040c000c5052642c45400464076200000d5a403c4c040108581201c1e90303a402000c141c0301c80b0000c0c141e51700416550307180b101b402c00520085401e4403100f140318050307604402d00399200070803803181066090b000f41ea800f031064070f1141c3d050280100d501c0c2d50804402c0d041742d5041d103620b41101c2c605403d020100c040d22034800d40c0210188240319001009002c00d20405c4004e079000942801007120141440646421110466150000400009401800c8078056a404035107220041e80ca2421051420f8040f607003041c014003038035000150400c040030181600c1ea00480003c013041240c3c0074584c00380303030091082d16052a000c4040032800c44640d4001c43d00103000e8522a000c107a114000300f01290300c003520003001e1640c002021401d2000c28400d1a54603842103079400c0c002859500020403070300440c0a47c01000200007040d041c406002d503c08001081d01504 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 144179748 1250 144178498 144178501
    0x9140307030c020a0503121605010209090f040201030f050106140304020a0f06020609010c020318061e030705040906050312070311010912111615030b13090503190e1e0315 75
    0x2001014070000c00b400328000d511500000c0b41600d00810000c0c0b0b100f010701422030901101c24840318030801070b50000d032507035507007000400310948402081a124604040c034064843c1018400101107460082d40d03c4280380c0303054010301106a002180402c8407000b940480c1d00c07502d950000440340451940024115200c80f4800a051784d0041001445554440000c000d400c101a070280c6c2c80c1e00c500500518003191a0040031841c0c070341440640001031441f04001c86000321101c03100b255900036074040d4045035020408000c5e44034103000c0c880c054101940908107441d041e0940051600038180c0090a0180d81c08140480c00e009600c0040b140307401c80c020380300b004030800c0090400d007085180b84c0442e0103400e682484610009803403100711a2800700d141e1400715800341c120000d0143c4c45441d0350203008000080e003016641d00071244818010000b45035110460070b10034402540d5521841c0500010214075281c0d03541d980711074520464040c3d401d41110303c010000a041031011040100b02604500 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 144180998 1250 144179748 144179753
    0xc0307060603051203040c05090403170c030615071a04021201090803150f0f1e03071502210702040b04060918020301060605090a151112070210111009140307 69
    0x401c2032080300d0040040e2000b450391505443c5151004441c060003000680004006c507080a0b0f0316198028068a020301107159015030300c680301c04069561800b00c11010040c003000d0315012040d402003550704941d0300e02e040c0daa541c030328025645061032042c40c441c0000000d015515a0002100d017104881c008004001d06403030000b0043e00181d07000c0382c944141151311685410501e50f88242010010a00ac0c40300e00c03d4420440e10311001c0c02484000500010740b4071060b1420880c030405022580314045d859082500d00034504140d107100c0586132030361082c00b01085c403614021074034640c0d01910046030b2949051301080240216030b2025542c13501d40030f628056a0183d10081081c640700301c0003400307c55903a030f4044a0a00401a1541e80522034140800420741041d24041501c04103050145080360300c115100e00b0303c1c00820441213000c0002070301c10110302c0c01070041c0c080182d09062510f1443c0b0344250460b9202c0b01010b000914130343c1d55040405000c003544440b0411b0042e54100ea603607041a1 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 144182248 1250 144180998 144181001
    0x70816050405060a180609050c0a0804020f0402040f1202120c1302091f03140f070f112104150c0c0909050703020619031a060339030601020606121c03020c030706 71
    0x14403d5446032480c0c400450271a207402e40481c1c0f5404003070303070381c3c140903460365020031010f4414114280d40c0700764200000101c07040311109000090100341d0601c3c000108600511100c00f140c0001310249400c104000c01c0265540c8480402c0400403060043c0c4070180318000c40e940c8103a41c4d1441a05140303000080c035115a141c1c00c106040401c4c02110507243d160002c0c1c005072804285d8907540442c6807918244c450318030035000504100140b0089610b9074010300d4006140410300b03200700c40c00400004080c00452005441443e45110710b1400c541484607540b504000244a80180d03d501600c4060740c0e0184201080064091a0010085540e61102c0b0084584c00510041c5100119042140500c81d20700010070301e148118019290740d1543d900c5c120654650708003107041f0410207401000c0d401010500d503a103915681c510014a075681d0403d0301c006031600d900284054482c1c80d0500d0000c2c0041c070082880f5410000000b03207281c03900c1c118a001d401034054078050402512000ca940810300030b9a = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 144183498 1250 144182248 144182261
    0x1407050c0124050f0f06160c032009090a05150403120507090915032006040b0a0c0b060d0c03060e0f03131a070c0311120d0c0302070816050405060a18 66
    0x100c1d000d0611041103005e1066401c04a0400c84e8411410300c420303007000b80c40015001c2c00500c039540394001c90b0b031640e4450042990840040444a400000c5001c0700e05214169641294044004021018550303852903522100d114103561460819008a82054010116214494848901031002d450301c03403001020840244507080c150343c00d007040310b81d03110358000c4040180e80c5c1003075100d400740084404054507150a14041c6401000c20000090303200c807284c01508402c91a075888081c02c0083c0c0c14050007180020300024810012780241c50001042d4805001c1180c0c9d010501080c3d40c40a500140c0c1020414441c2d4601c1d80400150f441c01c000316402d00b035040d25007000381c10049111707580782035401c2d001c0d06e60020820301c1c0d00d00c410f01c00304051a030010600c2c800104140902c1040d0410b403400c0020170a841c0e004a4140c500e860304050b0103010241c00381c400030f03001300105001e420003d00060498880c0601440d601d402003200340d103904107500042d10725251071100900070180c1c03c100a24a = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 144184748 1250 144183498 144183509
    0x91706100614090402090f0a0902180105040501120c09120804080d020c0315090102040b0403060b01030f020c0703020d0807050d02030a0906260a060e100303121407050c0124 76
    0x125a180800c0076030244075a40c0b103289200400c281080498001d00c80254403900010350f10486a000102c115500c0d002004091300000902507114113400c10629900394070b1644260520006220501c12a607111a2940a400e0b20700804500c0c050040c07000d0342c160306107400400202c0c0c42c405c030901c01c2c086509e0081007141d15a000703d0f1010610810304a8450340e810500136410b400c1026005a40015640300b07641058010000602c0d0a9450261140f10340c4140d00032030b201516002d040d0a25a050b01c9890155400a0015450050202403540c2ca50006010007441203c40b810548203101003002690800c3d07901c90203c407a0044484d41c041c3d520f8208202020000c8c00241e404207d0a2007030180c2c51450160040d0190404100d01c692016424018000140d40b40d80e914000380c250604841640551030606503607141da419410014151030100b45440086420400c040300100000030b9900ea1012103890480e0700c81c1001600b907030141c22011052051000700960b21603c407113040211a08840 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 144185998 1250 144184748 144184771
    0x60f08030a02060916030f050304050a030c08060702010b0a120c03080d05010e090f150c161407091103060105090117040303140109200a0504090204030501051b04030507060f091706 79
    0x544c2e250501d5a180c030000e5503040c9030001c00d00f0130000148407a44020225100b50150303410143c0750f60100b013901006900c16110100201c0301000003031024040240c00c21071620003442054a540c0c041115000b1600c2007000703510702485120180441651541c003c2c5601c0b1034055a94018420b407000509001c0c061010701c1814600400c2c0d0b44140000c4110850b54035402030031012400d40801012000010058892818100b2650544122020301203c03240d22882502400c20300a0318400d00d0807005400070582e681c50403515114109076013082c0c0f6408442442e0090759103100f900100c508050b40c0310201c1c014500c03041404201501a000022203022000c03172035a90b07a80c0d58031080184c0312800e10f105024102d00b03480d5110400c0604c000c20840c03440d41040c42c03520f45d442003040103da1013580141d07000d175074440c1400b080c6c10240a81c405c0c034100b40c14a46042909544403251149210f00c40c2900780300e02d4803642d40c5914045c040c16401011010881090168031041103602d8070400c9480c0318804 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 144187248 1250 144185998 144186001
    0x6050d060b030c01091208071406091501080c031203090102070b130605060409020603040303050c16080309070f05030d030c230a02010b0102030310050d050a05010e0a0302010b04020a0c03080a060f08030a0206 91
    0x1540b0171100e1038102c8420075400c40f80c0e05c2407030300c0c1e9030030702d80c801501900c11840d061305400c00d0b0303001002068000d8aa4100030b0100e0004001402903120041c2c100e4080c03a00140184425039030f001400c0c02030360070394010f15560780c1c481e00400742c02445032250042594058108000b01000d6002c0c400c0d5159004140c203000030f5444404200c221240580000e601200c20300114011921a50085a01450342c07900f19150241d41c00c5850f03460303032200000301d41c0729200000b0410070100c00d00c141c100929102217030101d030a08140001e031315080001d51341410141d445c0c0c6030102c118811805000e1030382162403603082d99003080c0b810100c0d56011920417409582884003004c195440042201c4c0309411134008019418100010040e81200d040d900361198402d024040c8003290080c0b00342c010b0000f1800040040303000614001e0b0a64551048061080b0700c1403000740b002903084681000c3d181da152500100390340c0c1d01c180071402014142c000e4445130302800804220150300000412990f1840e40031035920307 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 144188498 1250 144187248 144187273
    0xf0f42080c0307091701060924050603010b071e02060d0603030314010b0307120b12070e0108010204060203030705070305070510020405040e031801030207020303120906070f08070816020106050d060b03 88
    0x340d11040d0760140c00111150010030851424a4405c5154501040003051843da13941c1c40205940880d0714091541c0c00c18800d2090030005505041c005082c107450150641d80342c031219000c94040d0179000b034001e0103050000203080c840801c00600180c2d005010f6500c030702481c41c40400038045404210082440d29190050811003200130300e048070141e10340c080c40e507990958200c0d41020b401004850f035030f4494000e01700b150f56007240a900c00342c0650080803c180742580c80b0a903998113034400c44450b4410031061082960110880f5030221060505581e220203500d01100e142c0304600b40585640500345404803074800c1500180100d0340d0407a814001c00404050140d10303442850101c0c0c2a41010550100d0154000d401404240340000e046d01c1c00c0c401c00e14482e0000000481c1d21100710b401c4902000030068001044030300402c41071610840c2c524040501030701c1c4050140c5091503062210f4900c600041c802d40020020700401703024418020114500300010701410790020b0310034009c100003ca10b = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 144189748 1250 144188498 144188521
    0x9080105060d020609010302041a091c0b041e02040e0c01030f02040503030306041a060a0203070b070c0f030806040e0d030516080903030408130f0b130f0f4208 70
    0x75110060010488040307603400c020b0164070254a950525409000001d009007500214541604070081c1c2d1503911925941041454000032220500e04000d101c841c10200b12510030351035115500818040d052000881d10105154241100a42c483d0404545901d40038000c200280349101c01e0701d003400b076590062030600c20780c040e501400f9090350003400002d2243c03515410103004440c40c0300d01741002e29122008a41c16030720020300d5030050f82c0006400b6081180b010480f55122409190440000a01d941c0e0600340c401c080c540981000081e002080207540d9980c4040c0c402401441240e06003011010003a0107480704580280882036608032003032007240242e0300c00d44110012400b4615540d01ca0303480304150781002040c0da40d1844201c0003c565807000c07001050240c0000445140c580a110030214090742e00f070b40080c802d060f00803000300300900c08168442c090b101c040c0c82d611a407a00c958558468150b08183c194254403036042c900c0305107604070381d4012080071310ba920040c0c2d580d074076642280c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 144190998 1250 144189748 144189751
    0x200705060c0301230402041706040b070302090907030209120f010c0e18070815090406060323031c0905010912090f0f03030c02040e0109030915020c0f240c03040609080105 75
    0x402d500c107001c8001024500000211300e950704000c000504081e00c0e901c0c0b00d040d8100030f01e002d4040303600c540144024400550415a41300d0054030302076181c08800c41c08034510340c1000d003003d0f0601d60082035910035581d4290700c10b00003071241c0040391314155a03074170414040d201515150300444ca200c000320320242450a80044000e414039103541107500d60580460301c03032100030301d0b200340c0060380081200a40c0ea061541802640204804603d05003581045c03012442c111603280f1208031800420006d42d0008002da5280441444040103031501c44c0085101424419000900320752801c94941e00f0080120a43e0300002c00e035566064001c0c4d00c8802d007070925801070003040f0441a4200c0d0070000240706400c0080c8807403001d0030120b00d01c808403000d1800d41c2d4030f504044020403549074050102440c000381c00b0210500910003031001d904504007040803030300040c44090244410100c02c50740c3c00010040407601d80d02140e200340e41d8880c01003586859810134082d140c00541c1c83c1b000019054414052907 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 144192248 1250 144190998 144191009
    0x2090a05040b0d0b0c0f0a0302091c02032d01020d0207030e09130b1803181203041a03091216050106050f010806090403120608031c020a080112020301200705060c0301 73
    0x41c200070403541c480134041c2d44000e02e1850000c20800c80300e034288510310042c02c0d0071807140d18050b80321051102001045d0540044250306041361000e02005a40c00084d0300c0d00922030100c28042c000d1001256010312802502404400d60000409420306030159004100582c00b0b96100300b10703202100b0400c4015402503520711000b003142030480005c03070001d02d481ca82042621280a103442403c0c01114115007146141c0e104101c44810b000281c1d0070011044050701c1040c4010310b10f05424102c021001c054200554483c48034048001041080c04105006034441240da060342c58801005601c00f502d1003c4a003101c0c15424858001403508143c542080d050105031107061666031000300703120f2802d90081c020741c200f08c01c0d01d02c1010103108034480c2e00040c1200b60090344d80d403094003290f10341f0454000d41200d6114030400c0444030b030f070782e010400c2410740301a80d407000040034103030001a003d40f03590b4221100c0355248000000488407518000e294003440b900682e07050341da8440e06100d0030b00092150 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 144193498 1250 144192248 144192259
    0x91508070608090c09180c03011b18080a0b0a06080313051c02042f040e04031103090406240207030506070e12190b1003170c190602090a05040b 63
    0x34008640182c06040c1c2c4641d140b03040b00c42030b101c40e600081d00e2600c2074810409041802d0682d03021508107210000b92420158001d216414084502000702001c80d0460010813070309050306140d6680012803c4020200c050441e243c0c002d0a0900d1042c5a006940e40004c1620300800019019408130079103460030004250704054500e0b02043c000d00701505020554541422884000180e9691183c61031000c00454003c600a003905960000e10f5420744902c004444248420050000d0042c2c400b903125615107000b41c424003d00c4842842e40c010440d4580e40981000d0000c42c1194810b52840007447c10000714904896032071a007640c88a07240d00002e011508914000b9103418021742d00f03061140b20142108613001ca40e842030a042c0043e8450300002e998903499000c00340044e1304038080e08451510240c1584600d19a1600c13141d0b100c3c283c0d011094800070030040c504883c148820080590071004407504106145002002903001c030840324802c61505e040410b503820325205442504001500 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 144194748 1250 144193498 144193513
    0xf0106120b150703030209130c020c010207030506070e0d12080a14060a030303051503030d0903080f01180f1803020705011409010903061808070b01050102010b0105090d1104020405030a0c091508 85
    0xb04091940401402e806140d000c0007809032544540740b80d0042c210b8015800a030308810003000074105055001c60b141154003000d0705001003040070070300f2a042030b00780c00c04e0715050403000c01081d1600300d61100600304030b42c0a0314000203031750494040c6200d91810b2400304103c81e05c001034080b01c65801d03a649030304980140400d1000074081d5200c55041030200015209907959400080d185a0101010913440c0303864024810415400c075800b035820034100032003a0510f41c100030380d41c002c4c1502d64100341c0517139884e041c43d0b43c0a141d0590007480d4040300060f082403000001d08001e0b680703800d240b090740d00282ca503490101c0c01498080903100d145105941c1c4208142c03a41e1218030181010b501000100b40c1d9031503032030000440d814018400244182c101103110740c5001c7c00a4215203108204a060050410101c55241d0b1203001e45081594050440300e000122000802d000b4012038008503098032511044409000c00462445e049418548041c4a101c040c100254001e500794407400e0200d510020 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 144195998 1250 144194748 144194779
    0x10150509040b070e0103020903031809010905042612010303020606011404080c0f12030406080f01050906130c03060b030109060306060f030503090603040503120124142b050f0106120b 80
    0x92010300c4c000414503015060540303642c0003a08507031040010440e130590034051100c11b410000b01d0380f40106403101c0200950302e40380c2c075010900124a20808162030b21030384d4a00c0041344020907030ba8401c411850340140ca68503441c0117903996a0039161503000c1001e403601400c0f20b446080845080c0c50f600ca014243d8a204182808050110303400d501d9071151075a0b0f0b00b6401d0260800180c40244120341c0d840107a81492642e602000006801541c0142d6a010402500e510340c54119000680708070310009508168180440090140b500158041c3c00300100000c0e041c141c603002a0305403802588100496641e0302054001e1036030034400280542c20900020003c1e10b0207402a690060190040d646094251481c140414100360001182940780c0b91880f070600c140c1c000035400c808520b041c05c800c042810102040315001d00d0742d0881030f407210303076206c440034002d60082c1c0ca64510014205004505020f941001c0d05c0009029040002e22025904010030515020790903801c4005040355400070240f1 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 144197248 1250 144195998 144196007
    0x604060e1e07180f1b110a03020a0f1a0705090102070f05090c03040311010204180b100e0906010507050f010e0d080403050304060f09021002010501050f0105040e0105120a0510150509040b07 83
    0x2403075240103ca648200c135111400303050040403c0b000300c003003c0d56652060140b001d45880b00071a03952450380c5c00b02c00d01c5030000c3d80001e204030074181c20042c64410384001c0d1030070713203100030000a8040307182801d070703051011881d0000c0c06404000c000341c0035280c2141e211001c01e10301000e03a100d03072a885880d9101040100314944001c580050081c500060310101740c030788403402d90b4801d503c214122042c2c4159840080003510840c400c1c00343c12601c019080e0800c440061100b481055010f1158400700301180c9140e00500c2220002c0d5404416926a00200010b05000388591003503880d180c0910190018481d01c1803541c9442103900d5128a411074803991075030002412000d204540b150ba07192a00d41c05070703503408101030070005d2a50000c100d56041409204000d000e000080c0e043c00703811300c010f0102c00e0869040c107055071400e03184c0f240071624001e04545442010600a01540550540b138000030070207070000e001c0c0c1c0d401c450f101c61b8141c4d540c0080c051009130454024055405c100081103046100b03 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 144198498 1250 144197248 144197279
    0x206040f03051e030402040f0606021b1f05030405010b0909030d0b01090b071514010503070e09160b0a08010b1303110d0203030a03060906050d0308011e03050604060e1e07 75
    0x6854002d0070140181020940e0f481e10441c1c010b040500801004214030303190148540713041004c0310034048039151801c06942c58103c4041b040d2079400600c10ba95064440c2c2900c8005881e91007506801c01500a030051700640c001c2d103056a503035003481d07a49000350034540421740c0030340e040c203000710f181c400c8000c20341c001002ca1240d41410031003040030000b1414100300207803942c41e010b504c0e2051084502e0b182c84086031542141c185500c3c1c0030000401007642c0205910040390503072600103c081c0d81d2901058140800c3c0a5109456690b01e1404a142917168000c2d0884141c079464281071070741c96900c80c03605070081910b50003140312000c0d010f100244254512030340c00e6070301805128503681c0a50009003541c002d42080c900107680d84104201c191100d01900000f01026161686d164a00c0d07100106811014000d01c40d0500c01c20740141c601851000c1800c00568221003501c000d82002d2900d4006007100090040c0e01c1c0c412901000c0000c100e00c0d4800d50565000700041039071074904042218079004 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 144199748 1250 144198498 144198503
    0x50618090915040b160804020a0b0c0127020a06030603020904060f0f050a0c23041e08030c03030a060b09180703020c0106030c030311120f1c021201031e030206040f 72
    0x1c40c0549403060740d01c0c82d0b050b4011441901c100210b450041c100000a03900c0901c00380030000740100744805038071241054415100400d0807150380d00400c0c0700550245c484c607440c48041d40510320f03c80750380498002003001c101c0e01c202d65141503203590b41c03801c85c161125400701940c00020b20707001c40d001038419400150601298200450324043c1000c65070105d0390100e4203081200d4452003003180d000d41c000078007100070b1200100c0501e00745500342144041d0140b07014040707900c0d0459450412018110101c100203040c0c40044950303600050b603499031039400984000fa492814484085114a5800706603240318030013404012841030603c450303a84044024190781d007899401c10a207100c9507070a010b4a4041e41c01070140c800c11910b9450010b100e0040f41c0034440003030304520000b08480c101c0360102d40180d941c0411441d143c05007110603e0030f00c0303012001001d180384001005020004003110340d504032402a0900c03650442c48181e045201111602c0040060f00058001070001e13032928980c0140c1c90 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 144200998 1250 144199748 144199753
    0x70e040902011205070801171902091e0112030201050105060a170402012a021305060a03030e3c0a060212030c040302040510080f0307020901060804021807180506180909 74
    0x43e5001c482100b20b5800380c40c00e2001504c6100140f09119800c1058581c40169900038282901d0200c0c0c10050041312a40081c07180c1c820f0808500c1c07441441d814840101c0b00c0702c50148130303540d55094a0440f072448500450255083c5000004d040c60300c2000d6412150103901c0382c1038079410340c6c250500c60181c0100100c3c144200340f4000c49800a0602d10442c840d0641c4802c070f620504980101308200c22282c40001032103040c141040315607191030803141c04803681403c003900300049010026100000c0c0215001c1100107441511041040c16481c16403c03040c503600000ca100c8441c0e003400114111402240c0c0541d1005410b0103125031504001c5038080c07102c889450a00b0f45981c0000c040c0e880c01c2c0c9012000c0303003c0400c01c0c804000140260010311070f11200451600a241c1d010500c00b540c14031402041c41100d200160654446880d000d0441203a140340201038a00010701420180b07440141d40e140075540c00b0046017600701130003154034030000d01c840714480d8000e007020428a031400030010b92450 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 144202248 1250 144200998 144201017
    0x1110f0d02070e010902030601050712170c0301090c080c1902012a12020903100b0102010f0c2a051203040f210806032a120f15090303070e04090201 65
    0x85060104031038006aa902500c040c6107849115140c400068101c5810144100305009041c0e0304202119562684007078600590030019005840031050f030151030710a460048108004035002304002e605889111408003c0100c0300e41c0b04503032140c000c48020074102c0003006a880d0310103850350351110201c8544004542440b80c0c062030040078008498090604a11501000b192504210281034111100c68114240201303900040d555480162240300b481c2e613540c60351343d000d074030079000f0f00003074406000184180800b02000400c82200409040c0c0b44451075040011401000c49a072401a5004801410480380382d0305038850b40e510240045581100a000c50400101d400f030480c01940152a4003401d40400400c010740300460040c03455209801a0f81d007051529414105004044001e40c2d4802c3c112800c400454145a01845050054860302402010101d4001562400869516007409440c0c89132111945c4d68042599044046a126100000710781803e512000700940141745c00c001d070 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 144203498 1250 144202248 144202273
    0x120e0a0506060f042309060601230a0302040306150501020601150e090702030c062809020d0b0c04091401090c0e01021c030603081606110a050706090206040905070503040302010608010c0504050111 86
    0x6101c5d004602d903400800315410088000700034800290302210030708085032282074078800305c0b050b5010140386000c034500c0401d010241c0c0c0d20030703419603000d154002020040100d0500070751140328858441c09006110b80304c00880c0301e05003485c00c40400e03e400e458082894682c84200500640c0c02086202188010301000c0e04540041000f81d000c0c06c01000440401516996a01e07400001504207110b002c1c100030741500141c440030340c02111142c01000000d82ca031503c0701c400780300344265440b0a101505041d03203130340a03202a008960403646a400c0422a03c9400d010030380c5d044428142d0705000d60040c000c00303c5802d220f0890106840300e14580055020348a176500003154204d080b191307140c030034900c81c44010800305106035082001c54072203242c1800c0e24a00010a0381c0300e03000004080c03c0d00c07404d201c0119103c00003039901a008014082c801464015401403064008441c1a4010f41c02d01100103003c200610607070041d001140d4849250500389401500c0024111031002d14922503400d0f202507 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 144204748 1250 144203498 144203531
    0x4181112041209150504140102010e070b0d0b0405060f060a0203090405070e09061e04020c0c09090c011b0b070c05031605030301051203030c0901030921120e0a0506060f04 75
    0x100364820400255842140c0c040108010040d0300266103000990b04c90102c465000b50954084134000708441c4882200c550040340500444036003075945102d01031000c103942d450007001d4041c80ca21240100104030051041000307440098801a80240301400340781d5a034144000144200102401100d1500481c40b000c18210b60341221508000b58284000703005502e4074106850308040121881d203040d041c030341c618440a5220802291095a00040c281400001070100030040c0d0130007000030085140410255864429004100b40050f0f4070340a00b69000d2000122122041c0d08001100401e990b000401e032200301c6035400c1907540340700c244090450506c1c0c010704001c4851003403001d0b644075407400041c080c110b44400840a01504244100890095034000f66038400c00c003440c020800902a0030306c00340d02c1400c940890050b0b080c0a0101e0b109a400241902003804403510400c1504c1c4003031002c1d501c4007003089001388a500160040364203131500344e5298059807001000040c60301c504104608 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 144205998 1250 144204748 144204751
    0xa0b0403110a03141f05071e020709140a0c020d0206070507020406090510170a0f17040b0f070c050607030806010c0c0902120a0501060201140103350d060b04181112 72
    0x101c6680c0705c1118640b40480c044a1511110740000050045040c070500240c60002503034210103210141030300802c0498402c0040e540200300c07540d41001061071490400021500403542c0f8140c0f0341c1403401c5150303500c1c800201020906016030117044030b6110020100d595070300c920f5050340d00c15150100821031081c1d6108540c02085070b50244007030503103402c088111202441004a440343c10403c50b4402042c80941540ca482e54490780f99006088161031491890045d42c0000400c0e0b88007185100c06803070300038020421a80901c3c03040c4034140c2e4600820181d4400c0c101c1c000c3c0005c2c0c0340c1e008640e0b554050341c0030a803a2441103440f000340740e4a0314034031001c07a04614490300444400301d040c090980041d00c03525001d8000351000340012440c0c40104100d000043c0f1000700758040502c100c031648950402d00009103001220050b52501d442c040a160310340042400c001e50318948600050303189010b01c102c82c2240c654000c032800b180704030121200107045d80b510411040404004510340b07030f150b074049036 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 144207248 1250 144205998 144206033
    0xa11072004050708010b07030c170c0a050708071505210a091b05090c0307020f07030305070506100501090b07020a03020a03080309070b0c1203041406040605150a0b0403110a03 77
    0x25110300380312410002900c2000c0c0401042c008220010b00000002c030007215442605420045c0f405400d034941031a0035038004002c40c8104001142d03c00400501040340444580102d044966450302c41d4030a98580b8031a110f007581d0200d80401448004e4000e1001e4004c40c0c641009004c85400c6d4040d0380380c40c1284c100c2c0c0c19041d0aa0303c0b40c52504000c4104010360110780281441000c0c0740c203200118000c0180900103014514000c40012205482048040303002c0340c810b03042e00e8905a5a00d80607002e038014900c111090b02074080020780c1c621000d03100c28203c4a05a480c8200c03140707424048943d5503c600d100b0781e002003aa17200070000d80c6070014601d00440c81084003554a160401405013410710310340000d18000420401c030102000c000030f4181070071802040c100d81d40d0b110b501d030040089880c0000340c800e80c0030324030800040c0030f07403944028400c0040f4072042865000aa04100c251142405203c0001d402400240041844180f5410100c51b014051901c46510307074481c04042d031481c42d0b48 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 144208498 1250 144207248 144207293
    0xc090907050c1b1f02100c030b092a0c0705090c0a08061c0501021918080307020405190e010f05010602070305060a0c0e0604030602040317030c090d020102120a0810050114030a1107 79
    0x4c0801b0f8248142d4030901c50304d14040042e04400c1001441038000580084016000003010004030000c01080006040c21505038131b50b07c0f040380c4c060546840f039034030840e84502c1c100b4001a008141d440b0032600118156660b2220613501c1b00304002810010980120300a84070030107030800614240b0017007240001e180c0c070015001440c0440105600d501d0140c440410180c44010818420f000054882d140d0341250003007101e5507032180c40000032083c2c080800b502f038203102e4140c6a410042d84010707582041c03900c081c0300d607a80300c60050746d0b5240580f0000f890741d4003001c0060340c0b00c1c1c030340d81c09046450803900c3c0a64040002c07000107003840e00141c1080e646181d00040400c00c00c80070140c41d004031034090326000d065142905805031240a0712204c1d174000d8014084841c00c680c400c2c0601441c0f01e440100b015111a486480104200c0701103501d0061001801c40100b01e541c06581010b030040960741410f440d681d145000040a004841824031009400303001110004210810f100015011120b1 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 144209748 1250 144208498 144208513
    0x6091f0314060a06030b0a050a020717070303060b09030d0302131710050108010b0112020702040609051005090105041413030c0203030a050a02160602070614040504050c090907050c1b1f02 82
    0x8260400101030005080e1030b02d040b50070000540c504850707d90004000341d00007201c7e0f8448410102910074000e008040002e401c140b51181e03900304000c0d05c0e10030301039941008415140c0310015410712400c0305065250380a4140010303014442c0e00108103501d150601d0010850783c03604120541c1c90600c070a12184d0b00824034410340c1c3d403480c0c40b4580c01008044000d004001800c0006804000a400420368041d000034082041d9243d0303030844402455031a10400407441c3c04c1c6070040d1582120301400c4c0c030455000300000341d039140c14020b00c1c4d20800c0e9481c20f605581c4400340204501103115504805008600803c170015a42c1400034151403e495180c09595041e075040003030810100002d1010302000a010912030035600240d40170551313040f414115240005400d060465000e6030388025070190a2800f0082c0041014002c1c000d6190155030a0040d5154003100362158094070b4000301c00e590004ca10b0f4403144c110b81c0c0410f1a40d13200504682e00c1a0714080f568803e0310041088800542d01441 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 144210998 1250 144209748 144209783
    0xa090f030c1706100501050307170114010f090311040e1e06040c0503150a0c120906020703020f07060509040207060b120c0f0a08060a050c041512061205030306091f03 73
    0x140e20b07900080c840000340c0a03501e455120400a40554024681084404000103405034090039101e0050307104c820240340c0c1580d4a896280c0c054040c0c00c05280010004c41400d58481d00031ba03904010399500005494107012500148002040c10032450203a1f4820312440c040c551003c3c07050708000011f0f41024003160300c1c0c42d040c04045c0f152981e110600990025114445011402c0c1aaa4006101410204d503009120001f15405040c3c001008180ca00d0305400344100101c503030040041c1442a000d484815a607803812039115080352103294080748003008111b916280941c0102411849032034005080000903000c125130000c400c0021507141d0006004142925013840c075104524130444001c4801400c100b00551620805000d0806064031a4041441211018242d4001d008000000c201d030556081c802000c03150003052103141300e8a01140444c3d1003500c0801002c0c0c0715005401140745031206424800d1001000304205401c200b125122820003420041d2100158060745440d980b810041 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 144212248 1250 144210998 144211019
    0x80a0e1507050309040f0b040c0e031006060903060917030708040209060301020f09010c1e080706060801110412110603090304050a080d1b11040f050702010e1b060a090f030c 76
    0x48020580c00a41844901c0000b040042203c000300001d8502240340c1440d9040303c00500900324005a01c68105048028415032000030910a458210215580c0e58850740c5584c1c1201d180f80142c80006002c60300c10702c080350058024010b61449010071550742c1d4444080d90074550030a5a130100001c000400f80400d52500c02481904000128000c524250610103440c4c030b10300c500c0340307414140400711340c6810901103151602d01000320010382c1d481c0710000a18185000d60301144040390400c9c5088000701f0b6a2105102c0c904040c1c10141c0391618050628841c0200e03003c940760111405190b04042103100c1c3c0314880510700030700052004540715400e15040021721580360700044503c2d03001024400310310b45d000446c50a40201c01e400003610504a04051890400d6408a103802c0750410160300002c8446602041c40740d105680200101d01500a04031f485e82d00b800550042d081e034030b6020403120700d4100c00509401e600d5042245d46965134103e0402c2840f203030781c4103441c604200c04082009840c0d0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 144213498 1250 144212248 144212269
    0x90501090c080105092a030403050304050601090903080105060d1b03060612021e030403050c06090a030908061603020d02070c0b04030b060105120c0d021b010915060b030f060d080a0e 80
    0x1030400402d20360400001c1121041c0080207400f07a24881c00d800300030100c007010040010303810080000c0d5245014240501240c0c02038a0803038851103403500028181c6000d00c1002a40c6034195640310003a4a80740401074160030070011040250755a902c514088140180c070410010180c0e180031501c58605580540301c0c0e041484146c00003070041000240034304032041c80025031809140d0035500c03a250350130308076614051002d00c8091849803105000203448005071076107040b0302c240e0f03c200549440e60001500c40c50180c4103034000c40012075210030964000c0e0050018010b0394107005040c008151510240004594003007078070804005018418031070006100c0354071980c00c2c241a45000800319612160f09030082140500d0703580450007071141321142d01141c5043c00c072000740c82024101c51000c06c2c02481c030a0412500d002d00d44000182c815030502441044411408645003135a03240e40541d8258203004040300d5003c0c1480362440d0000e03030100094002c01000f0b540b104070a400c00c80500605403034 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 144214748 1250 144213498 144213521
    0xe0103170f0904180b1e06040c030204080a06020310150806010c030e030a0b150102010203010f1e0308070501020c0615030a0303110c060405150105010905090c2d09032401121a0109050109 82
    0x407800b100082c00e08814503280c003d01c7c140c40000358511401c104400a000d1032b0010005802031601410510506170044c5004680c031742161850070b03544044144104506c4962400402c0d90f18000801c176601810214075200d009091890141d070301580000e003488a912000c5400c0755400d07090110780144007884603a02c080a00003140365504040e8a488816200c0c4580d5003501c0c0f0100447c5150b18070300800c1c3c4001c607404503106884c1c00803860503e000c1c2d0420788420500b4425680010303031645480c4556001102e020b4082c02d45043c49803002c40c06000c0c0c1c00f096400c5c0c04020006901036000801c081031060f4060405040880c5000d10111b01744001a4441030412031901e0003880269540500c50390031000412406035915480c4268248035004811120200b0703000428490035186040004c01d15164110f0941c1d016113600518130034034140603640b08200d200c958006000381102000040001402042024000891001e40380d0344c0240903044004a66110b034010807442c811806080d60200 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 144215998 1250 144214748 144214771
    0x2070b061503040b090f01090c090e064c1a0306100e04091208070f1d04180f030c02010e0d03141804060807030b010e0103170f0904180b 60
    0x41c04a0031074440c0e02000c0c00180441d080368000c10700c1070500300480c1101198040090001c1001360a1005046465200340701c05c0508182c550034140c040030030003520a030305c0d95582d017044100d00650940c180c408a445440d0040c0c0d25803034490240c14450b0401806040d6500d80718400c2e0500840c1d166410303400040504014051050112aa440fa03202e031aa0300910b01d8020840589031002401820003818041d003034900211560300c04039409180b9900c030309425100c003800141000c208403440c040b02c105058036240b5500c1c1450440c0340540004490000713040071009502d8031600c1d146440c900000084003c01d0001c02c905003156000705e8083c020b036004580c641351104103038030060143c0d4103000202d9900d503400035131400400c215070407107034090002400801c01603460350002d650340c04044c001651010a10300000850618821034103068a0348410785480c046e4034010004030719088030756500c0000d0428480f541c25034403588900003800c03101142040e1104550300344201000c2000d01a0300014 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 144217248 1250 144215998 144216019
    0xc07050d03020a0204200c070f14060414150f0702010f17130312110903010605040c0207091a040905030901030b0105032a0f04080303190501140103020d090506010902070b06 76
    0xc2d402050400c60b058055402090b19919aa07500408808800502c0104100400d15840385e010001c0d03c28152a02e403020f42c0042d60b1100d00801c6a401c9645450740c2c8550204821f11041d0540d0740d900c1144403005e0800340a00361a0800f190843d040b2540c101103002010035130109540c1c0c8104100c01074107107410b2131440c8000041c04009a040000e000c40c8240c4c14070340d035040405106009001e4440e0350a10104556820744034840420762011284520940c02c182c4085002d04d442d00c25000701c211140c0003024854a09107560020748603242001501980c440e0824026403128006d20404070305c1080519030354244030700003604507510702c10100c0c1003040510422119072014400d18003403401c001d992003000300800c080a01c4034820402400f00005011800141e402e000002544c0a23802d54410116002d018190741d0003110000d02c5501964581c1e4011903209501036401400c2201014a01040d00c2d001034442c9490b2820aa00c024010341d8002004414072088042d0507030072940031246502032 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 144218498 1250 144217248 144217253
    0x30905090712020304020d080307020d0e030706080f090c040c0507030f0c0507050105091906020a0201020d020f060613021b0d09090b030c010302030709030b040c0302120d0f14070b0c0c07050d 84
    0xc40741d030b08690001580d00102280070740d40c407010003d1859034060700803039a0b481d008000a4031440c1c2c90340c540020812000b405800c5290100741402034802543d10440f4594070641d400000e428007404048160103095041c4810780c4030760044c900380c0019520f5140c1d980c602e91030700400c20840c001c001c4007000407002c1c80e8000200701080d0a401c070dc4c0246400354413045035000166100a903442495001c071125100010031680126803a60b0042c000d0b000d960b1180e10102c2e0680c4c85040c4410104001d420032400505e141c80c00600c61610850155801420610b01c04020910151042c82404080d40010040704045038059801c00242100a81c2407226501c1d403000f095070740f241e4481355810f054001c000200b2447c1301e03200405c021600008620210f007440c0c280100c807564a40003e9000303105145514028050004401260b40c20690f01c41d00d4000c40d4290444101c882590040d591440812400c8003103690710013602c0c001d10780390500755a00c002030649030f8075041e510340c010390044104a21031b101 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 144219748 1250 144218498 144218507
    0x403030801090c0f05300a05070206100504181208090120160201030b09070e03010c1707111e070906060e01090311030a061416020601121709060301080a0309050907 72
    0xd0041c181060742c0c407100891049140b0314002c80c00c209003101001b0703403661044d01e100d4085000b40140902005541c0300d011003241ca40c2c43c120352081000354084003c00180c209940442ca4120340000c00d2015060160b4644980d076002c00c0000d07000808902c01c0c0710b40c500d400c4c031403590304440f4200c2c030f03000c0d08418410154041c0210a03071801d01c402d0002c441c10959000780c10080047d40010308008071441c0c80000039000200c01a2010f000e5031800c40795554150050350300e00170400c600300d580d0880740e40f181c00c00c441d150341540110f0740902542070301c00440c510f41819801a283e0708800380900c142001150310803100ca41d40014100035851003242c03210390b0000d1150050342d80058250400100031008a8030740300940500410b03d074504000a2080819034048070300910303100209000146100c44200e940b54070a00407145d1046001c8400c50001d40d4290620502d600b01c6100300b418403103001c00059850700f0076031080080f45c0101c03003400c00305075002e60004094002110709260704d050a580051 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 144220998 1250 144219748 144219767
    0x100509070f030f06030c0e0108010c08130807020409050f0721210201060509010b0a08060d030509040903030e0f2103010e01060c051515030d020304030f03030c180306020403030801090c 81
    0x20b040e6964840401811650000e001070b6400070000442540d03a5015042d010f402486000c100707500c1c08290804a0344560f4480c1e00651010400245024003070725110070f541d0204c20101c2e40560b03618051800100c1c240706014240c04003101801081d45021041c00204484060b010100101010719800160022080841c6140b9200c2c0d89864003042c101c00341c0c010040c40d049a640303c01c405d000052041c0340d100c001c0004072401d0341c8519054071404240200b600a84000078003040c010707c50451a03050030f5104030015030103850041982e001641402d800c114004104d01e000f50042986504c41c2840040c078401c5d504604484076203503600d4040e021106e01018043e0704200864800254148402013203a100c076a0075080c041605402d00c10f84203c8000385140303010740030f0300540d01c0000040e400442603804036038100b400c88841e024180e070704070010300580c0a09130a022254004002e003803038998a00001d10b125940041e43c0701c0c1103041c00380c0a40c40c1640802c002500746040ea582440d44043e085 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 144222248 1250 144220998 144221027
    0x102010b03030d1d030304080d06050d020109050105030a0f09390e0a020409020a09170307150b2b051c0c0b090c150403061b0c110303120703020310050907 68
    0x1c4c04e1055002d0034510000c864500940a02c004003d00c02400701d0200200561644c7c8042000a10390f550140b01c503031141c185001c1e01040184008001d2540108010740d07014002036400640c51b052241c9080849002c10f905032034610030354042e08030000002d9118a40c00e80e614008800c12801c0c0e00c5584ea215609018503200034660001040002c880b0381c0598000d80f2081f00203545503044000024a00d04043c0f056440d07001c415129074640d5100030013201d40403a0080d0140e00c40d040604600c5011700024444d40f50403010302d41030b280803010622615454168209003e404020361420b096140c200d11005000c3d5291714001d82600840d049103540d80c140b940440003844e103607241007072a800d00c6240c903442a00401c0440882940b410070b64020000c0d24400c4004000c2031312129404400c030000c04c8030040c04200d0074007040700850540d01d5030f618140c600500300c80ca0101540900691401d0644d010404079030040148114801c0d5480321710050f00c016200e43c92a4501940010300c660f0040380071 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 144223498 1250 144222248 144222251
    0x11e180902061c050412031e09050c0913030e0a060e0d020d0501050c0c07090b030304031403160c03060507080c0d15030c170607110c0f03010b04060f0609050102010b03030d 76
    0x240c00454807610203a5a4120880303494076500c1e01c08600000103000c0807039003141c0090180301601d1515000344240120440c4114100032100e100c105800300900752407a050310365100342c98001d02e00d0360320a41c9061283d40c0b4120221340150240c980544102d118201289c880e0541040500400e45d001c500c0064200049400d2403910040e400400c82c000c01142c40504133500b08020404801c401030b00030094015a2011175a41d656204400340172074401070b52080e410b070800c00c0208003003174803481d08002e010326001c02d49282c00403210800d0302c200d00c0003030102e81c1007180c220100140011840f036a40d111001d400c0c900c500d840d01d00d408076164440c0fa5600d006440d030312500042c0380c0030089068005582d000030040342041c2c1701c401c4403c000c00300d9400b00095204401c000340000e4410381c903040b417460041e00117101c001110070820000421107a0782a401d03640c0c5520403013446c1e0702c43c050400207241c1800e801030140c5c05c0c414020311200c01034002906682c1402c21f13000064a0000031200c111011180 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 144224748 1250 144223498 144223511
    0x60d0b010c0f0605060112090c12081207030b0f06070b0403030f02092e090b09130b031902030615010e0d1112010615140d050907080d08011e18 63
    0x5846900320218050840040800c030142040f01e0b41c0c0c002ca00540003600c541d441003c4e003900c2c201c295480300c0d40c010441009004100b00305151304a030002800d214251440c140780d04e80c14a03061303014040312004000f9484512290480c1001031801d0000b101c2521181e241000c241c1300c0d000c64440151008040541d68855403031900c0860741610010000180b0a08018883c1c0644c3c8800603038042c05c00368a4881c4c4490f004801e401551110111000c440c2c4507030034079110388100a1160220035203801e0064442c50241e280c1e03501031121400c05c0c00b804441c00341009180c0181890840001c14406041d402d002d411030840c2c1c2c01030380c41a51803404403600b81010980d843c1040448000c00401038204030308c032010b041000f1041d041072003641c4031411003051040303044004a9040003071185a80d2440000c100407014003640c0e40000368414080003c6404180c0d0754000036140044144502e00081c03040001030020000d0590340142071140301c0700c00c042403803d002e0385c0c0c02007100c4c15140c00e91465032640c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 144225998 1250 144224748 144224771
    0xc060c080316020f01020f031803040f03060203150406030b0702010614130f0f06060809101e0b030708071508010f06092c01090e0606030d020d0311070b0703200702060d 74
    0x4d414009001500035512200004099065600152520301142019050a040c00c050000581e42112144058000814030316212000258006010314454000e142e0b002c1026441c1c5002d0390004520641002401c2d1030220700007821105036030008034a010411200c2055070b59111810703203030444e0b07a90001076050100540f000042c4981000040240d042032400201150010315841c0b16119403810754196226041c02041210a4844d902004035500340c2d5a103c05540d561024130790b00070203001c468140341c6444086140030400c1d803001e002d40c0c1e201011030010035030007441e103401040c662000c001c0090802c44090f20403401030180282c0c000450303500c00f13108000d10701b80c1407109a48241c00a92943c5800781c60028002803503110f82580b08420200303100d4140000c020300400155409007100151880045000d4600c0c410440f405272410b1041102044000704028040c2d0b403651400100c0d00da160b030014081511030035001040c480184060009030702c03490308072000080142c1d0001201e00040 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 144227248 1250 144225998 144226003
    0x12061a0a030603060c0918230604020d0501080303100e0115032c01060e090d0c1103030c06090307050c0102030316050f1612140913020307110d0c0c060c08031602 71
    0x70b0f8805083c650802c0410744400d504842c204040d5009060f401e2114411004a002511881300300c903140c903132016810100041d44010003541200c40144013600d04034107110010240c034003c0e0884103854100206011107031074103c108a000b02045691518590b250041c603141c00a40310340a40e0603d0303120030041e41c0c95420510b400c854084004c0724401034440c1c907111740303000300401e0050700360342010034022411507980000e444c0c0a10034180e65152120901e6a6800e46440445403d140c01d4481481003020700d08042c404641b042c648000116280c9680b410032034034003284103804a0654200308107004a0700350f102c44a11040469041244d6039001903c901e100a10480300d440c424000301d4000c48080020071554424030020659607183c4000300580d80d805581b241d42d02c5e1690000a00140c04000b81440e005581d0121040c02c0c2030600c40507070007906081c0301c0112020030001c0c100302c00d210104900d400d83c1201615040ca0f00c1c08803028207607511030300c622010302206500443d904241e150325208 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 144228498 1250 144227248 144227261
    0x405090c1207020307030216050603061201060f03061a0904051009110603040501090b060a05010504061d04090803070906020c010503041b0b190e030109020a03020907030f0c0c0312061a0a03 83
    0x1428400309807030b00c0d0800130f4494015210840041c0901c05101c031100c1d40380310700b0070f0546100901080c0f56403281070030044d01031510040300c2c04554031810005a01814515240d0007580101d401203950b200d10410000c6912060a405200d803c0c0c0f0820300021480005145a0444149000054859090500201c192a078407151035001c080001003004004041d0401c039500d0303200302c0c220030036610b545040000022243c020f890018000b40400c100c01032203040100e114507000301c40d040b0f080c03603408045401d0703403210f42c01615800400010303c40d0710340d4403818841c0104a14401703465101c01d03440001f04188000380c005070400c1c0c0a4000d650025181494000081c13100c1030009568292401417081c51001000300140072802000160619003018021741c51040d40c000c120410703040c216400c00205c580c01400c0c1300304050382e810079005202e54903c01c03541c07407a401d9101c800c0490740d14680101a0401c1941c41c07010710f81420004c0000e08100d840303a41e40105200c0360f094403100050703402c50040c44c0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 144229748 1250 144228498 144228517
    0x3011e08070314010c0c1511090406060e0a0603021e0705030c061614030405070b0c030d11071e0c0506030a1503060605090c03160e060417010506240405090c 69
    0x1880500008020000c9454070f2280c4140303009000b4044103c009840c0100c40300c03000390603a80701c0d110181c0002110780c001d007880c894031546142030030003100c003080468139150011404266480810402850480300e02c01c000e000624041d490011021903502c0341c4045003410401802d00451200c0401205106580304001c03210121806c40c40d00082c408843c8500c006144c000c501c41080200303134091b1b00b108681c45180c00200a020b2980b03050008013656000001d840341c980414029100030340d0480c010031085020f008151a101c20303581c2014103241c0d030707081c100245140ca0703180d840340016000300d80f10f03046690803106241c036680d9011140000d000003075400303840328490b00004010881550702042c02d8507002e680071612644d8a10240c0210b10007581c0d802200007018003111119489a04800040e4801500c86810b02e0f075280e103c1d801041080010b043d0701d03511041007028038141800e08031080703204006103459003444a65120224462800f469000380b0700c078000240c2001c030f41f804940c1e0307018 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 144230998 1250 144229748 144229753
    0xc020f01051606091b0305030f0d09020a0e0403030f0203091f0605060c100b0f060409090213050c03250e01030b270403020c04052203031b0c0c0b0f03011e08 69
    0x400f45003001c024082410f04440700c0007100201c00404a0719110300041e298443c005510b030420381941000c1d250402c1e00b52210a0342c03280800001070715007900740401401c8814a01f803c609007407030080c050303400c800300603810140306108100310840006100b03420030030b01e034010141c644001c0d0041e1014011740e80001e03030008000a14156074400c0011030440e00e6030b00c518104010000344082001002c08500c81c0396020700305010038402d083c4194000d070741a9100411007050303444e4508441d01610000c50301c06042c030300040100701c8e00d1251000c060340b4100342949400c4444410040203404500d10112041c100742d90351141c0c903140e8441c01810201008142c4082e582d2110410140c52441c40449048005006101000f902d07420a401100e02a002e0040c05101d40c0c0007011141540c1c2c0301440e0b00343c040540314500d1110564050888500184943c1d40e185a02000d90910300c10592a0b80e1140006400c00c210508103030540400380d81c155240c070305010424a03000400d82402424942100e081d90 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 144232248 1250 144230998 144231037
    0x1506210601061106060618090a0603020d110f0f0307090f090f05161e0303031a090a06080d0804050304090e03040305010509010b0901120f080a200f0610060c020f0105 73
    0x1550400c1107440c0c901c003d24201d030b02903070f18041842468010001c02c140c5103072200c40081a01d03d401d040c42d0b40d106501b01c500250655903071300004c1395600404400d42d003d00b1442c08101903424a070442900b140001d580a001c4803018074046550355071244074030f004265646849141e04801034100440755034010101c111240710604103182c49112040861a0b042480c44000405010700145000c1d02c044107080b03d1303ca01d1a60b1426000b409040e80f0b0200822040c00701c0c4c0e14a665440c601d0390240c2405000028418203101580d80792212030305800c03043c441c4c00300070000094000011101600c4002c44d020806040404105155010341d4100070007650815041020303820056100f0240301d00c045603c07490f56641c0304980c1c450010003640280c0b03105c54175116200450041c8004100391203051401c14040002c46a810b0303210012074018042e10f80003041040c145000c1003003016040500102400303809464901e000c3c10020903ca00240a11074100b40003038903038054802c0d03604d1a00c11007103030090f8 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 144233498 1250 144232248 144232259
    0x51c150f06030821100803040e072a05010501050f090402040b0a0e01091a010507030e09070e03010c0504090e0304060215060103020d0609020715061a0c0106091b08091506210601 78
    0x2074201401c003200b40040c1d148001544083c456000e17a04807080c001c065840c25081204010002c00c0040c817020030310a6074401481d09440d41b20103c1081c50307140070b03010502034103450131a00f51001030b40b0280c400e0713125030319045065840101d496040fa038101d0740003e0b014100130100e418030500c0d5009001e41102e00c000001d90700056080302001000c546100c0840600007001035402e4040c150020b000505402c00b94005401c0040c8910f8005c9918181f000c11840034000003400e690310051090001540031408001c5e041030b07400313035035000492000035600b042c6c141030000f9585c1034500701e01c00034405160045001039000342d04588640420714000c2c8000d81c1c803080d600c8040d5110840c1100e090440030144034000315075116400645803005415010111515201d1296030082002c080c500d541c1c0343c40001e040c5906101c0c0510114040420801c0d00300446409000b401c40240315550a80002c0f07002e04800903903650683c0e000e042141c010080c40246c06003215000c19602d00d12107240f2640001041 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 144234748 1250 144233498 144233527
    0x522120f0b06011b08030718090f0b090108030a12020705060f0610020607080a0b180907030308010e090303060105160c0f080706020c03030304061d0d0306051c150f060308 75
    0x40d600500c650690360312100e0044134603512644080c5941101c0c0c020050005040070021900304006241c095442210f03034840140314030b0140c0c0320000056503107403108549405400b481d61410710481d60184691714005109480c0d2094540700d80401c412003c1101c4416020750540791010341107400c583d254030700800700c40402c0100b84e0307070303d8460140b80080352115803001072642e100d110b00e991507161580302c0800e42d00c054105000340c154020301180c002881360b00ca0205039031159103000b000b040d100345140cd01418050301a000500d4010800c0100324a00d51b0010440380c1002081c80e007140d9600700140d0341c2e40140314014005000294290000591001b240d4802c1d00781c1780007205440c01540e03900c0090ba40c8103850281540c2641040c40010042411913100c85415010011848903400c0810b1680e400d100e428901c503004203035600e2080c0b1190800110103880325a00d45039004c8400b041d925640c00f141c0800f1071a003041d585803104c6002006041d08408021640111342907120b00c1e43d0400c20744c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 144235998 1250 144234748 144234773
    0xd080f040b04050f04150303141b01021909060206010509040f020d03031407020c0f060c07081e070608070804140709060303110d08280216050c090a050106052212 71
    0x511484448821302c0c4185003d1003a6550144040f50840e20580740d980d040d210354441848903070714580280901c007840356045900801c10003141c000180c0d9a8450745200f0840300c0d04d01002010410b80309001e01806c0d03000039416040d14000c61742c1c2c803166550351800407080300d40d000000307411144100e000c0c400c040d0185c00031003250540070480c1e400c1307503038081081b40d40e06e50040090342d01c03031750810030b4844604002000305004015041035030304103921000041d141c00c0780f0012107001c0c00110f51592103070344424008440503081601c2d0031801d40c14041002800410007410180c210500c5081c55604c0700002c221150090010f80d505000c030980d6414040c2c100d43e000320800e040c601071000c2c03620b00c062044100b54400c8428008040140350f0704280b40448090001d19a005030703508112500751301016495418503030f44200c00414060788010148401ca420240c200b010160a200c018070070140c000e020f642c050150540c888040c5414801154460021070303000705500500440d0101c148000c000b90380 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 144237248 1250 144235998 144236009
    0x506030a170703030b151b030904050103050d020f2b1e0e0111010b010807050a0e031506040c0e0303040603020c190605060312070b04080903010e15070908011104050d080f040b04 78
    0x4101c582ca12600307001e1001d250002d16680c680701080304011440e0341f40440075888045030304480c04c180f1042e000c0b8040b0346c42a0010b50f07090f80031101400754154104034001d403031400240500034a0000914001036162004800e2200074a802e1071400c44902c1036191948140c010011642c14503180c01c009421070314144002400940351840d8611019814001c5402c80d01040c0c0da43d03d403a03901c40788101c0303144d04401c0b43c1c103041088130041c20100d903038104480b50000c2450f000c010042d0515100308401c46402e0a030607420302c031105660300f480c0e5401205440072528182000350392540c20203134080c10b141d034080d0301d1715101464124080a0005681c801c81c8030380b900fa822960075810302a0008901d000d01c4200801c404407441c00034001a03807200141c0701d0650301800200380c000c55a652981030103001d4101c4180c80c0a408104054654000d50b03038001000c2c40c1008000002112440c98583d03c600d010f058001c02e002e80ca4081001252400c032600c65204400f4951520b88030f082d20101984244900d = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 144238498 1250 144237248 144237251
    0x60807080a0c0302091e0a0b01030e0606030705130905011805070b040b040902071e0b040204060f05010e040905070b0c031c0c0c02100e10030204030501060b09060703030506030a17070303 82
    0x465000400100c0e81c41458100e450300c032045140d03074204440484000c011191600f0403516842d2403003001c02e68203009100045011490607d100c0004040318085010f04885038441c809206107914041f510205071041910100c40d900b01e180c140e000030340300142008100d50320f08842c2942418004e654480303268451420b4440036580c03510f034031445006500545242000411040020b03500b607900401d04203118090320005088103617071140d0302c0313a41050700395800481401040f00710b241c1403244c64090200309000603512800d000000b80445e1000762003d000e01e542e91209010710100f004030030010098071b03488950300d071041d100f0107403290401006401c100941c50000d421150242c0600c243c0031082d07039201050a180c1c0d03020810b40110300510041400740c1c7d20813403150b41d01e0340d00c038803c5602070b16180075070744610b5407401c1c5003103410940c0144442002405188801d503905821104004c0c1c0518000c900c586903500000e05010805000400c80102c40d040c0c0413010030104003810645001c1d440 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 144239748 1250 144238498 144238513
    0x4030b010e060901151206050604080a0314041a031003021504180c0804061e0507030b09060d03020d0503180709050f15060405010315050402041d160c02010309050f010504060608 78
    0x40c00100142030240c01881381840b0b10a0010621804090340628491b40c0e01240c1c240c1d5070000303d07500b070740b00341c210a04a8100402c02002d154000d6908028050108449072403e0f1130140d00b140c10b40d00c03c0d080d404c1040c1000000c02d00744845e005084000d50340050480b82c00b0080700d0b4000c081d6074402c3c45815103265a48030b4250706141e0302e00c134040003182c41d9296114290384652390780000700b8002c00900294040b4a420f880700c0c0c040f41c0700701c0d071140025071000100461410100182c8050007040c1c00c0c82074055007007200001e54013003940302449420f070078100d4994641c0d10a40c11110b8aa045c4200607205003440001c0b10091600030600503a030f0500f0200c07280d1078030803680a840d0140350030f540d00420b04200410095206c0d60003110004010443c0e140c60310f4840700001c0036a400742c4d010350f840110303810000040c0300e8524040c07600825854440060b402c60901d01802d141d000d01006414995954994414400300b8802c0c1008544241c1c000c0110b4502490b001e4010a014002d604d5284100c08 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 144240998 1250 144239748 144239761
    0xa0b090f12010e010e0d080f01051c0b07030509010e0c0607060b0d060f09060f0e150717010320031f1505040213030b1605041e050a08030909070503041115090604030b010e 75
    0xb120b16000b0700800740011624ae00b4001408903140190003240c8080c034842c008280840c0d1071500f00c03801201c003030390b010469007014020315096030202c9040e484503801c88a420070041da1030f40221101d140d400305012507000c10000014550080104001c4c140c60308014440010380c0841c4d02c4072030801d02c1488100011481d4007115800c4407140b50580b4200e0380500c003c000812040300c003450b0700c14001d02d82107400e5441070130900300c0d82100307030300855000050b01c144680114800f41d55010141007134000344013244221203c400390910340303c00070b845680d03181600308401440d6441040541005842590b0320040c0300c94001c00660a44030581d294103400002c11038807020441e1084404006594180c00c06040184075844210030713412040d0400340d5450700003515182c400c1d0760001402454003a6071101924810b0103007400f0001c2010003008010000c0000040c400302200104900036100001c0b02c00c80d2403a0142607204900d85994840d002180000c10042007405141c140d80100d00c0181894030b418 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 144242248 1250 144240998 144241007
    0x307020a02150405010503040b0604390509090112050709020f0d0501090c0c06020d09050d0809011a1f0c061a040e06070804030c030203040e010b04090b0a0b090f12010e010e0d 77
    0x901130380d80021030401c00b243c0811068540c26402507070061001864000e1141c0c48035100c01c0d96001120742000c06402c4e858075a60700b25003c070600d201d40c00c0c0b01c3c1c9400c01c100c0004461403414040c0500e00d003210301e50802400010001c94028100040085543d42024a2121110b400c64040440000e007003100120b0940c4140c061038680748400e44961080203505c0e41e407440690003070100451520f0703940d06c00b42e01142003007048104003442c0c0d403500031150800c500d030302e82540c606250700104031342101011000b6445400345000000c96200800ba5660220441155010385602d0050240350815043c842c0340224800703170300c412601c102e80412004841c88003558654004440381e202040d003400000c1c0219003d00303840e2038030741e220748162458076440d160702d0343c40c17000300f0703000700c00c40580201d1301b40204032203403051a0000c0f41c01c48103062040d2400185045511520169600852045200c001213464440000b0301100c2490028841c000f142c90b0b40700e008010490b44144d007445140d50400480303014 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 144243498 1250 144242248 144242257
    0x309010e070e01050d020d023105010e0c031f0303020706021501030b01150504090c0504030215030402130e010f0207110f12121c0f09050705010f08010e0a0902060307020a0215 77
    0x1c80b030716401543c4c0b9044c20420301c03000004060340c006080410003c010780e190041055110010b0640116089502e9200100c41201c042d229641c02d00d420010710030b0200701600a0b0380103080250040d540e0752140c0000da407020300d0445044140b4941e05001c410950046407000650341c0513800c50304500c0c40c2c0f030041c07441d0138800e12014000150000050100c04000032440d1070307510581c201a46800e0750f590210080310b140e0300c4010f0018101007028000c525191191b030703040107400c8200d07a0541c2801d800040401c00c1c80d280d141886642c600016107c1c030020740101c590400d2040e400c54480b10181410400700c0340404c610341c131807001c0000380c000d0303031902044000740c241c0b003c00204074203140e000209026070300244848d410411540700d50543d5407074500480c0795060407804080395180d0300b840e041b8900ba200340c00090520500340003c145465000200b1070441d1400c103c4842c00d51941140030005003046500130350002c800100704a0300030740004401040510070b0b5000f425054a40c00544494000d = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 144244604 1106 144243498 144243509
    0x304090219030204060f0f092d050904080403060209060403080403110306060102010b0112090c05030604030216080318040f0b041514061306052206050309010e07 71
    0x48039404141410750754181907003814200000070300041900d1365840100003035100840c403003e116800d22402000c0541b207900391100341c012000760456002201601350407064071300041c0c03400d10030701007881150441600c9040034210395400003e948111b1007264400d50034000840400c418800a100440c8901c04400c2031964900900d030500c0c0004020340c1c10740e490b09041105036604446100c48850311201e00041650b000e2400941748803c0750062901440b03280c040104050b000201c0401d107040b010a201d1040d9600e14403240e61348030300094600c40452580f40701165040540010030700c039294038004690740d031030540880c04071041552501451107543d4000c0188105660100c059420706071445440c0c00304102c00d48094001c144240c0707080250005000c840686250401d042d0072a000f03c1801c4415580c00c4000c0003a0000d9600305110b501c1d00000c5804141c1c0001c02404544 = true := by decide +kernel

theorem cover : BRFrame.Cov 144064748 144244604 := by
  have h0 := BRFrame.cov_init 144064748
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144064748 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144064748 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144064748 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144064748 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144064748 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144064748 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144064748 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144064748 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144064748 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144064748 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144064748 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144064748 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144064748 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144064748 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144064748 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144064748 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144064748 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144064748 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144064748 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144064748 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144064748 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144064748 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144064748 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144064748 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144064748 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144064748 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144064748 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144064748 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144064748 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144064748 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144064748 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144064748 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144064748 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144064748 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144064748 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144064748 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144064748 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144064748 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144064748 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144064748 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144064748 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144064748 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144064748 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144064748 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144064748 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144064748 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144064748 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144064748 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144064748 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144064748 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144064748 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144064748 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144064748 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144064748 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144064748 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144064748 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144064748 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144064748 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144064748 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144064748 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144064748 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144064748 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144064748 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144064748 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144064748 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144064748 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144064748 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144064748 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144064748 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144064748 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144064748 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144064748 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144064748 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144064748 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144064748 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144064748 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144064748 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144064748 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144064748 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144064748 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144064748 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144064748 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144064748 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144064748 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144064748 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144064748 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144064748 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144064748 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144064748 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144064748 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144064748 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144064748 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144064748 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144064748 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144064748 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144064748 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144064748 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144064748 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144064748 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144064748 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144064748 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144064748 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144064748 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144064748 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144064748 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144064748 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144064748 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144064748 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144064748 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144064748 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144064748 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144064748 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144064748 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144064748 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144064748 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144064748 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144064748 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144064748 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144064748 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144064748 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144064748 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144064748 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144064748 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144064748 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144064748 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144064748 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144064748 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144064748 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144064748 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144064748 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144064748 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144064748 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144064748 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144064748 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144064748 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144064748 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144064748 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144064748 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144064748 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144064748 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144064748 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144064748 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144064748 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144064748 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 144064748 ≤ n) (h2 : n < 144244604) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
