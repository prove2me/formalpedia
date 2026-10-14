-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1419
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T02:53:30.259186+00:00
-- url     : https://prove2.me/submissions/6c31dffe-a9be-45a8-ad83-3d9dcab9d01d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 255035971 ≤ n < 255215827 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 255037221 1250 255035971 255036011
    0x70510060b0a0c06020901030902040903020609061003050a080d1107051b010503010e060d11060706020315060a020601090507030f051e010e1605070611070c090b0a032102010e030c01 80
    0x110000701820012660400392a050841c030005043d5500402d40c03c520780d11a034428050250005c00500c90103009080103915500c0580790780c1810300031100064045000b080040007240d5000000782140c0080b80c0380c00117a5002070b0b610480007620f80261038080c00c201005801c0d258041d4024090413101440940400d43c5030541d17050502c90103000402410145d803540d90790001c000d8852819800403860306210007a00c00fa0f241d40d0011011a9107418020b035075000c0c511850355418080d11208446040200074000d006280c001a80640c005003c0440140c2109030000d0741810082030f004950074102040c1c0b5801c542c4038200c81e0310084544540144840054018820301d5481da032103051014010b10001440c01180d01400000288a000c0006541c0240111009280820b03122015807621014003141841a800c03180d04101c114022450a20480310850340d100548040b281161a00c5803907104024101e8401d40d545c032082800a143d040c001801040f203010300004011010b1054a150b8407 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 255038471 1250 255037221 255037229
    0x51504122f0a05040b0d05010e1b0406030804030f15020d0b092511031c0209010f020c0303070b0c090a0e09070614121f0807151701170102040b07051006 67
    0x35407020000300054039030807200c0003a91420344012a0b41184440442da4950480c00000d18662a00c0c03800ca00d0741002062000c031588801084440311a0104100000da403c0e0b4040540b0710107040008100150014100350786c50351051141070595074410074220101d030019841000901e8032003509034828030b0459202a8810700301403032040e405c40b010704800f00141c01c4000010078400250f8a0300789181d4108142c4007002d24034424040411480304411000e500b0211019020a10308129034202130b001181480560390b01070001c50810102d916407140d43c03080070701001c2080d0800c000d441d605441e0150440c0c05030600c043e0b80003a07418050132262a05082d60300242c200012900c0a144041090045840d081d0701c8000e14903907034441d124851030460107074060584580320181c0000704800023181c841c085400301d521041d0680c03901c0c84242c40c880441c0851000044144005111140b1050740000503ca2400001400d06440c0c01c1540160f922461044e622640001c052602c088614060030020b8 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 255039721 1250 255038471 255038543
    0x105090c030721050402151204060c020a050f012007080a030b040608010203070201270c05040f02040f1206060f08030a0f021f0f0606140f031f0303030903080705090a05150412 77
    0x40040c0e088c40c140d150502800080ca1241c0325588224414070800c9026161900700c3c040e6410b01480710b040d01d008200c950660304c0b001c52190307401c0324803800c0542520745075500b10f400305d0300d408045042100208070008031035501c1b039520000850401000d01c05180306001030b0300002031b07011950081e109007040c082080c170900035220203108001254211341b54100c0d10107503000b0403041c195400d01000390240d50030540c081c005002e0b00143c08100400000c80d50b41c0501c1040245a8132201c0780a10301740540201141c40e8410461051014440c8a4010140e091403040d02c0b14040e0000c1c80e0201e07544102040c880094980c108694001c255210300c070700800142c02c1448041070110402007643c02150a088405503004c40083d02d1201289a003200b003840c84850501c01d240c403498041d000300b101070303030a8000681c40800a5140350140f8100c0700c00040007098130028515040030040200c65003c8410100031081c000020241d423828402401c2501c05c909444950081d0120105000082d0303440040b0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 255040971 1250 255039721 255039727
    0x3010303270b070b04020d0204231003021008060a080601060201060503010f020301060c03050d32060a0506030a15080105071e0306030201140711031b01090e0105090c03072105040215 80
    0x392010b20301142c0805a024842a1080d555030001030441d160142c006500642030a038680444000802c18000072944400d0034111501ca9100d41d002c0c9842ca4000290420001944d01100e58003503401c150f40305a000b4800d125042d141c00b54076007411400c0c0d000e2000b60b912480140b00500d02030040c01c2088569940450956161500041412004a0001e014044000784100340d03161146c005000c0001c001c901c903003004800600c2c140400308052803140703c0796003100101c0c3d00c9281012400707084a200521781c03400e546a04004200a14807030031499184001610700091404003030141b24403034100c0d62038403c2c0c11340c0412040c07810b0091449142c01010b10b807844c2800140e82091902c0401c0307414a101c603450f01aa860b040386100c0c3c103003940c0d41d0f0600c588000d10201c4055000030b039645c01000e0341d402580c5c5076900343d954a020b40078010140e10030b01c124009004e242502c405940d100000340307040c500001c86d140c10400f180400c001c1420940342c5610400c015070a16100e041000b03400902c885207 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 255042221 1250 255040971 255040979
    0x12020c030313050d02060d02030f040c080604020310020a030e060903130828021302160c0f080c0405060d0b0f04030e01080403051b1011040302090105010e010c0b060a0b0301030327 79
    0x3080103580076072803041054490920a540303440080d1090007041080841d5270f030070038041c070001742502107804565042502c4800b246070040850064091a4090010560504a203810300e019400030349114080503034410314480d2490041000c035001c3d0444c000615903500700346074503403904800c3c0c0d04443c82d203074000801c002c03a081c0040c441e580d40306402410100300e60f000317100140c0e0312041c0d24440203246001041c20007014031868420f42009102d60000381d190780d9140f13648a01c0214510400c0c030180c000413071250b240e00706a000140d001030010540d44540b40b0076580c0548803403040e81c2038864003405004000801d500f11020015841090030000190f203003d43d0300500301d20694400e80c080000650307401c11201010000000038680307442043c4000c1a00038524102d503001480280d02c00c1e078406000040325405a44500f2100e141a5102c05a08410791500c000815000d800560000510b05000424103200b10146001e14071a64a003e0003d00c00d00c0c000c2c16030310000300d0b108a41e10f000f100c100 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 255043471 1250 255042221 255042247
    0x4020a0e0324070c0303200a0906111002070204020d0507020a0605070311070615091b1214010e1e0411180124030207050d030e0601060e030601120203010f0912020c0303 74
    0x29034807911910300303140f01440c03e2400301c0107003503010347c0004008601c8402c0000324201030064031f2600c00940e0340224841e0f07961021213034076141d2848246260041c401044003074106400034015a80064009441c0008003040d00c41100c6081300d024005800000c4c4000c104034083c041c681d000200d52505000c5144288018040c8e03205240c0c00400c06503884070b001e0749081c1c15086000c002d02240710304009600c00030002041c24030041554500042009011000c41a03040c0308148090f03000101d60041682400c4c0b12380c01c9403102500c118201d11201301c0c044035070485002102c0c4030341c1c49240a00680a80c0c0b03c00d002200100620890600361a200144440503038003009000031085030a00120700c107101d10054000f8461800d0180c228010310400075149a01a08040c0c40c54440104035803541e070760349038125510300c0315000c01645600844010065039808007215105280010000541a103004005801322018480200e499100c44030f500602c0d690103010f40c68280205a000c1c0d464020541000 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 255044721 1250 255043471 255043543
    0x40207111207330509031e0d09080115060302090d0f03121406030a03050307090e040c060906080702030f07241d1501090903170703050a0b0a03020105161104020a0e03 73
    0x907001c205004c02d400c6551b903810008041c000c110300c1100c250003401c0065142c0c83e5555000c1c460080344031003400091504051182c03800f0300c120718044042003801c05c1070450195020100d0181e0050358800c41e41c0204030718200160b01d680c881d031160f004134801c000301a8140c4075584c3c480d640c182007038010005d02da10003103540581c2c10341c185003241e81c0740c0d10a902550b0b04140c0c0d8001c02408c0c04124204000c00c06401006003d03110113881d000c0c0c80b01c1da0340070300712644c0b6021103030079005030024442d00e050050100c01400100d80304105203a84c001c803080d00c2407203d4900d60050022107440750825410f0b4240604c01d101000003600142802c000501030503010039506110701288144d4074040c0f88189480f9152440360300c2043c220a860905200c080203002e003c0c00d481282d140d9150101103241450312000300c034116030703043c0c55040c145074000c103000e20116544502910b1004800c2d02600c5281e9903403005105c049840e4a40303140341d00070b003020b162804000c41030605400e680e442c20003981e04004604 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 255045971 1250 255044721 255044819
    0x1e061d06040308250302070605010f05031c1211120f1e06030c040507090303020c1c12020718020d0b06040308070b090313090506010e041a040207111207 67
    0x41042502d6200c040c28480141030400d12204900c051366a0000e40d150b0000c02a0501802c01401241d0b00c4000e82e001d0425584141503040d40013044a001b90684d04a00a10b5113400c3d091205030208000c1110040e034a00e02d0405501000003e104920301c0d8210800d5070f00300c1c40c03081491040e450103500982030510702004d108032011203240000c200f0b59042041e95003851001d402400142131450780a000c0c4e4071036020450140c02a4820b166042c1028840c52515644406411510aa070b83d1650b002540c10314014008600a0a401083c48a803000016585104c0b21a0042c2c0d180c140000303090450302002140e91043d802000300700085000703141a12021a00300660303403450303141c040b111880c40c8605642c400500e000504006251800b07a0b00c11407140800303072100230704032070504c0030401100c083d0141c0ca6035070034880300395000608059000e000d10621030841d09080c03140803000107415100070f00441220364002001406035418031396110034584044000510700e44a54080c0000b51102c4d182 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 255047221 1250 255045971 255045977
    0x13141017010e0706030207063908090607030506030c03070312030b0406080304050f010203120a15140904060c050d110c07080a0c03030806060f070507050306061c0b131e061d060403 79
    0x80a80900c22310b039002e01c1e00c40d4151f480c54007080c1c10a034801150320f2038181581c2d21903540c00b00700d4841c00f40640030f100e2090800390b01900b07095882843c02e800a2002814654052042c1744a82e90710b42c508006140c003031402075840101c0c061211400a040c1c5030103004c1d43e40240d040490402c411140001900c0c1a40c00c11141214103c0304040102d25502038414048422010082481f10300e82103a4007401c220000c8040c103e1055440e007110300d14040c404110386801a695800190101d0550303071150f50304c0f00305850050b282040202c0e100058070700c044002c1400381000107001d4040402046071100400011002d0310001056440311140d8200a20000d0b00b0300071701e500014201c2c3d854500300c80b508100da42506031230308070900340150345807050302480d070192103030901048480c58070140c1d50303405955074200c202050401c0e0f03903030b03803862a405001760f83c00d552040341c4c1000085240c1204284a8a96056882d2811003410460280d0710150000d031128024140700c8902800f0118921785c0c8160182 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 255048471 1250 255047221 255047227
    0xf011e02030405150c070b0a09150c032021040213050a091202010b090121080708090402031f090504031713060e01090201030e0d0e13141017010e07060302 68
    0x41496410660606150b404c0b14103c03500f0883d490000d50043c02c1d00303d01408040520780e81d807031142400c0b20040c48014154500a52480504100c240c01020078540c01e4038010405940c2d0002070b0900346072103105185072584c04117403c00710701c41c07041d500005016500d4401150b81003030b0b0041903c0b43e0325207003c003155507180c100003061030308641c001542081c0e02c6000d0b0302043c422081c000340208074441c10113118903207030800011881c00c2601000311541000b0031004c440c0d00760750f81c0d40d8241c1c6c6c862241206d03207041c203000b04400d541d22440914450070081b0b40740c591849048403d28440c10954103c01c503401e00c1c0c41c0500000c00d9101002d08500e5080702c010910a85500350444d4141c803455000030003003414511808000c03d011740100c54103d200380ca00307004c050341804000d611413410800718000aa20754040c420b02c1d103070812001c00c403c803400400184900c400d076000d01d00c2400489003600f02101d510b404002c0500c444040103c50340b00300e0300801400b840d8807415501c80c1c159205001c2016008 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 255049721 1250 255048471 255048473
    0x310231518060310090c020604150e10021803060c0313020f1206090102180d120e1201020705060414010b1503060105131214120904091a040b090f011e020304 69
    0x40341c20400c1040144101e407240392914041070084001d0160704d980f20300341001124001d000060f1240074030351100360654001c1000800301c1c0100740030781c500801841500c090f40b0348100140300400064640c0b80f0074003010505141414030300007016103007a80e80c0ca010001c200e00e04180b1904c03c40ea4075411600d02c04070b4882c81e00098500e8000f03105200c0580100b000b84008200e05500912400c4107140001c140d5420100400440f0906401c003d811900018541c0640c40d2007038000040803a40241644c0a2100b5043c9060032138100b42011285035001005000c2405089006040700b10020b0b0000d200c0c10780080c0c04585d040055000c8000c18401c00700200f9001d82c041c2003642d40e1400c000c035040c0095940c51498500220a810f0b0a47e4001000084843d138030402154980252010200785480d0a02540600004040051041d160340d180080e03500c01190303280c940329000fa4000c450210180c02c003070306140d04082d1105070030112a0b25104130442240201039040d840c2c0c8800745801070300c07640c903 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 255050971 1250 255049721 255049747
    0x7080105040207030c061b27090c0216030f020a0902041401030c030e030c06010f050a0806011413020301180b0402030613050903070f030c12080f0402040e1203102315 73
    0x5030110080c071140c2002c10f942d04082c0e928001c079001d410140c8e18800c03813082c9600d8503545140c104481101c4240030403000c0c04a0141504030021100031481100c03d000140f0101100e006004d420444108242207144000d41c904400048040e0943e9a8114503140c230304840100d0300b0b00001c3c0410705142d10307440d11276005c50281e0b0024a030903050382c2c1625524680e2401c040c1c0c0b2000700340079400c0340c0e42403000003203003e040c1018810151200072005021a034206100c0d8200030800c04103090b030150801c00c0e12960301d901030000c2c50081840b1070a0400341c918070961442919450000710340624418010418555034068140c1708203200107100050585a59240134114850480c1c0901840000b0942c01c0415038061725404595000d0342011a0600c0c42c8501101d01c030a050364142c100e0603903400480e02500c2c096214900d6103010a040720800244403038103880c29001161000b90440020b102008041c103160341c07040c3d4548064414009007404071000803040e99440060072000e00022481c5040084 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 255052221 1250 255050971 255050987
    0x10b041502161811090f091009090c0e07020c090105040b010302070f08070b0a0501050102121c05010b18060f0301030f021306090f1407020a03260a090b0106080708010504020703 78
    0x2920034030080039034450705440c940c0341040003007880c55450150f1400c01c404c1e80b0700680e0781d00b0400a0805801d440c4400800c000c6840143c071510150528074400900d00c6401d21610f400c207071081ca0843d0907980782540e11060224010722800564012000302102540d40d02000c0d8103603441110b00103a80c001a80c0100c0080c0501c81009003081c407115080b00600c031500020304062441100d440709a40d4540200c00245c1e2005c0c85440d01690240904401201c0230402809030040c0702d01c8000058080001c1c2070090b20800e0f8090800d000e00014070103c9003d04107036443c0420826509c3c1403500f460103c0300003480c401440041e000340a02201e02c0c04554031121074500d014840102408035503100d14102c001001005000c596161400d12400401408104c00074802c50560300940f0502465423021380320840210707170341130009510188440400e0007040f03880b4000d0188a40c001103c10041ca0103191301c00041c3c00040610000070104003559034420714150640300207813030140c2c9500003440d003940c0090f = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 255053471 1250 255052221 255052243
    0xa150f0b04090f023c041b08010503060106030903021e0304050316140a030515100f0602150106020f2e090605060a0b1603081b0a05041805010b041502 66
    0x1410000b1900500c070003c030340443c4880c0201c80ca800781c4104006244c00d000a07643c9601c00d40c03521007142401a00e003a40c42c0140141000d4030110300c0d2001c0300d10055940300d41c5207000001c1813085005008a0a04001c0c5a02600312130800300038500c5a40c40280d56100c40c0b4080382040254211080300c03d02d018401d442c0144005011210940b15001044e420b048850090b0b51040c4007181c04070700d1502d003002400701220b0300000a0002d00451030341165910b80d000305144400d609510700003540b003000b92009401805951b01078480038481c5284a2001c1c1810b0388075100f194802c075054008968040b48944104818100c030300c8580b0f410b100f0440142140c010140021481c1130080424040c407504618401c200460702440d141d901d0b01456441c6010700c000302c680a028401c40580000c1c024581c90342c00680311100496942070842940b500c0c0d0f407055410500160010030208100d044001300d1900b81065104c0520003907040c009403078082d004030300c6840300701040c4038106011030307009000c40b640e21 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 255054721 1250 255053471 255053479
    0x15021b13050106050316030b06220305100207030e03061005010c1401020a052503050307030b15070807020111070e1b0c062401020703081209030f030a0506040506030a150f0b 76
    0x640c2c0d9040f01502603001120021181d2031086421800d807480384c81114401d40000784828100f0f60001250b100042c0c0502041e206040d2081c00400407641c104251040f5140d98a0056038481c06c9140040c10400e504030694081e52141041c48844140110300c081030392828600010b106500e814510310102e151709800c0001d510024044d46445c1c0c1c48001062602003d14034000351246000704054058102ca130301500003282440450066813003900b09064504006210483c0000802c010080701c0d40468012160800000341220441d60040c07190079540c2818000b50000c2c0d850880c0c0f014207140c004015080082d1281c9244a500340740c02c06541002d100d2008440407894000d281f94100c41c2c1040040410241003035550b580c541c800221107003600e030f00c50b0000307080c41103084500740124009450840306000902445000400f51400386119054291020855040050900048500241c61075003c0c0d001030101c4001b09410080da29060442800002010701c1083c03218001082e42015041e40 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 255055971 1250 255054721 255054731
    0x402180c0d06141804030923180109200f070c12050a0201021608030d0c050412030314160c20030d03020408070603020306010f0c02010504090603080d0615021b13 71
    0x900b403500b54141001406450301e03600002c1c071302406440100c08a80040010f40300000a0001c1b0361000a500060900e088201c14100c4401d4005482c041d5040e0564260241840040004400900600903c0e80001584171142c6c1d050a1204ca114400d07540c0869043c48000b1b150390411002890740c80c0240318040c0309144107035a07031600360b840f000404000e80c01445550000c030001c0303070031184c01c404440c1300b40e0095242c240d6810600d005000203041071014440248000100307a104040e80c4841030344241d500003030000451180350003d54001d0038500800850594802c0c1282e0070081e4002810741010840040004144a10002c60680302c004c5825000d014500501c680d007680141064540840a580100782c503500e04404038002215030030300240c003c8a91207080b5000b29510b10681c3d0044c50114034054039070606800303403130090b882116405000101484000c10f01d1103628007406820300c0041c0350340840e6400a50b100c01154a100400800100c05000d950703c00741040804d014086080c42 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 255057221 1250 255055971 255055979
    0xb0c0d050a0203090d030b10110a1e0302010e070605041806030c170f0d08011505090a0f03020f030d05041502010b0904060212070507051f090609050708070b030402180c0d06 76
    0x1020b50810b5410707994521845205c0c0c5040790003401641402540600100c1c24012042c4044500c0041400700c0300c403074000d90007641c021641480000044880c0c100e61410400007501d802403c40341d1401d40b40031541c004070320501006038841c04480803110159904000d0354902110a07004010340d501c0200303400000b03100090032a00361031405411942000c2034801a1181030a00b0f91501c0b1f41005030800500302c0d40051140c0e9400803812400c1e1030007840c041e4286009100441c0024a440e0088203401510b10020021840d000360081200c520650180074030301c0000300054a01e02403805004d200212543c14a000c4510075805403002603001031180c42941800d040284c001d510450402e0000125540001c101e10b000740c0c00c41d00e075281d120b0000c058541c900604000d400300001c170a110680d482c2e15400010a045014070150140500041c0402034900040e407440d1240562003410342100c18010080580e5543d2080c4000204980c000c00440d40c43c3d84048480c2e12032200c40c03103440340c9858800302d = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 255058471 1250 255057221 255057241
    0x30f0114010501090e010e061908013b0a0210170411040b0a06050a03021612020d0306090e12130b03010f0501091202100c02010504051021180b0c0d05 66
    0x24102c50003a00c56079242912000ca280109030300b4020400340304d800002240300b90504600c1542100300d00300b5003c018940302e904840c00e542e10100b042060200e4a0391441d01e0504803022550f801d1012403030000a44400d504e0030b61111181400070b031192401c0394a0005140c0140305072070311494501c686000b2803505203001610310190042075800b803032519442d000c25080c00c0d8034800642e0b0643e141d85080516140044020f9070000c001c0301500701d02042982c2c005842c4084a007074802058000e001c2d91940c0703440c018119a5650f2100071300d182002544100c80c1b034040369580d010030701c1511191792481c403215240c145c20100d03480110200d100100018040c460445081c043d554245e9554041c00c0d6540c0c2100d4000c40c0e40e8401a520126a0300802005405112aa2030262040c10641c1c10155601d002919143ea81030400020886119040201e002c0040f200f880c0c0ca00c5c101d0b010050300024000700040001d290310700402c1c1c141c07000e010881040310401580d441d107003068428840c0c1e1070401c05003 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 255059721 1250 255058471 255058511
    0x40f1d010b0319140307081c0e0d0f03020c03040e090304061214150406090e010f15030308010e130606030c060e040b03030f0f09040609091b150e030f01 67
    0xa21952900201000e546400b01d04036461409548100520b1241030321403804403110043c83c0c1c00c3c144410080000000c0d01d0390b000d055041d1030002100750310302c0200c00110031394803040559030807074114084400d0381b142c200c18540448a030a1078010381302c01110031071510b0761140d504590011080e44082014803040000144103442944c0d4840440d141d168000d60141c0d00d081c42c00384a62808100015844c03403402e5042d544081000b000418200d5a54024600320b51121107401d0159448003042c0c2114811409086000608401401c18440c41c64500078141401801900c404150200100325064600703110107110a40006007080b0403640c9281c20002440726100383c0e0041500400b4500951900d403180e51858031001e009940b03415094010b08045034030006501e2440001030054200c00d8032544104005003160200c0010942004d04051110300760406088408542c400c80520800780065108120b40405040440c00303482d960300080d08000460704500015840c0501011410000c0110 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 255060971 1250 255059721 255059771
    0x1e171602100509070504090501091506091104120b09070e09100e0607090b0901140c01050105040528090c151e0201110702091803040303080108060708010302010f0c02040f 75
    0x2200d00908000300380409541080b41c5507003d9030040141003200b420f058201c0303072159102d01d0000960301c00e65a44e050004c0921020000e0701660350700280500d001a00c102450300c4a130583c43c9082a240c10030fa10314980c1501c00040141094001103a000d2904001c85005072480d1003a108852500e01e0520b6540c512074000c0c0803505007000c80720301100340c002c01e8550064110340d0b1826661070500c18100e01503408003d050303041040c9c40c01541203100c01c21000e05031a201d01000482c495250404010541e0070182c0f08052200901c5000303528418607130801c1c030000a08a00210714001213003003d50074072980381c0c000340091110b4005c03c43d403a40e001300070006058200300c040f028901d030500120f080b205503056880b600d0004002c0900546040740e422640304e542c1560401d00300b5040441c60b030840d0803a81c021800701e190701c4018000c1c10030501036a540540d252a00c0d503030310740c50f50700000c0202928207130f140240020f182d400410b5450703a400200810080c0c0380107001510b00140008511102c0d007071 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 255062221 1250 255060971 255060973
    0x121b0b271008240d0309090608010522030306051201020712020c1815060a020f150402060d020a0c080318060a140f131a0411030d1e171602 61
    0x125040103160400140344107035903550b1814050307655640e407001810300b803418900b9031502c2c9014100303090759051030901556100380e5070820000d213009201d0083d0742c3d80f504900e080d40d0401c01048520100c7c44043c0c62040c19000e1910103001160909600804081d0495038000d43d070070328120f00344070f4150020102c0c00d110392007591600c080c00a049803510b0807039212580c0908000c0394843c01d01d0b44075134180e4008085510009840e111000003451a03400b18030ba090140c0c0009800c0f00d8001810b000d11003900001d100820454a42a03001031007511070202d4000c100748e408103a10b0480ca02c11403980c031100b075014030300d03950b2410142985440d144517558031500600c00c1c02c00041c002c0c04503004600c2d0018180ea0f03400c1050302c4503c114148540d000b1f0007c0d00f00c250643c010008140d00307201900c00c01442c003007010400d00309410819203503482891903d010b68040d295840580d135105806106115070340d4201006186d4040048585246000d00d0101c2c0409a90078003810a442e403400c544000c160b50 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 255063471 1250 255062221 255062287
    0x3220510111c020616020c1c03090b0f090402031512010b10110703020d030210060906050906010507030e13140405030d0b0d0c0311060c060f06030f07121b0b 69
    0xa94100c8030b030108070200030010782040d03000c1010318902c00d945900c0c03d80240191203038408400c0c0882c1d104c00c03400c14407184490f1000007403018140c02101000c0a04401c1030070ba40741420000e01c00000e44142043c80b0302580d0300000007041121100710903001600000e0100c0c291000310801180a445440750071382c0310704c2d4200001410640a06610040c141100e40684101480c40e02008070071502d038071098055001e001720001220020348038601c040d051b0031784001806418602400a8000018482e40c144001080540c001ca03400c00b1122184040844079012000315514a0038043c2c64859407080036408004140410808044041c0c0082056039108000e141e41e000200005558210701c041c14421224405101141d02d40c1c540350020f00c40075040e0361800c0490607000d890080111103150742032100c80140700881c1750a000401030241704200400c2e5547c00c000311410f1200c10f500000345114079518601070307202001d8110f48000c2002404c0c031500c50250418408008800b0035134200a101d0603 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 255064721 1250 255063471 255063493
    0x4150216050d1b0b06041503020319030f1b060c230304050d080c040e09151602060601030c050d0b0a0308041d13030c08070303090b15031e0322051011 66
    0x303440d152411680110381c213005038551009010050024804111000480314000710260b28104114881090304c024480b0002d201414024596044820080200700c940340c40f40240a14140400c12600d420010000d101c41c0c001505841d2036041d0070300010b00c400030b01510a6814079000240d846107000e6030984201540e0610111459881160300718401001031100b0300040e0010511107920900b2801211f400c0c590f809010100c0380c208580d107445c055006003000a10076810320086400c50421309090203048640303400504603000b440049004260360b00c60039000c40e0b80b1294010002c1d0b0300040040d0f66030713480307140034a0411134071556000010400e070003042e14000c00c100c2c1c0e550480e80598a90b492040141d40340d1030280d00442d03003502003503207507455007002ca202000c450f80a9080c1d10a0203181c1c44850040c141400c1d90782070383d050101c080701841d04090fa000300407038000114200d07021484050782c441100b100803058010035007003612005103805d0b003500b142d80c002400e010b0710211070795034102d = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 255065971 1250 255064721 255064757
    0x510090c080a0519080f2709060f040e03090402040f0f060207140f19081b01030e1b010507080301260c031002030a060305010915050702060c0304150216050d 69
    0x10102c000c00c40d41c41a1001210040115641c001e540c2c840d4445e20b2621503c41880382842e040300318001c0000215900d0803042036212001d04040007001e4564079a07e00e00800040d8014000b014a1400350346c0b2824401440c10b0281304071008080000d0007152034907111901c51255040500032615080c1c016040440da013400014001c04880b0341c0b0f11a078252031708803824410300c80d079a04003994220522803620110750b8240c54045001e00303a054000c004510041041d030104640c00b600c44c0d810b05207405040c008018010403951515086150300380c2c0701056050040f1000c0c822082c0141007903902100110fa82d0030306121034109082c0100c02000031507440c060280d00c555400410070781c1507109007014000000c1c01d4010316404080300c003000500b07699a032075503404d540c00d20b00c04503001140801d22400d48451842030980240070b0f44018500e034036100c00d01940f40d2001070030240907030250290088150000307404903107600390300c06070710b003004085072506e541d0b9038440c0c03041c840104042240c2071034a130107 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 255067221 1250 255065971 255065983
    0x910110a03300b0406140a03080a021e010501050a0f060e010e06090406030b0f0a091509050a0c03080705060703050601020a020607020301060b0f12010f030f1e0510090c08 75
    0x2505502412440000766825075072140c1d249110420a40d003440c0410315050080000780102101220206104002c0e400300421500e05800c0b003a031154030502080000d490340400300043c2c1b6844090b070b0344e56071102c10082e8900000701260101c01000084004800041900183e049460913038445c00c4080d00c80c4c182240c048001c2c0a0b83c8000354000d4000121580f0645581d5801c07040580038526205043d0080b5084d902180c2042d2801000a003d0080502d12070ec070030b45d40580344020800008040307684018070404450030442810382c664000c1c6080c404140300507880643d0080d00e61080c40e41e0788c5003c81c01a0000c1500791154028400051801402406034038801d4405a01506003c03009508006581e0071414082e0b8040d03603505c40210f51a19108028000041e88450068403071030b42c00038030741505030160414900090701c41d00400001e20306440000c2080d5101c069841941c02810040f40024947c1c4006001442003c85013104103c007984a091000c0c040d0814203091902c900030203903951 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 255068471 1250 255067221 255067247
    0xc041404032609160504140402010f11060106120507080709270c020105060312090a0506070f02030a0809040b010801080307121e02010b130c090302040b1210020910 72
    0x1015040010000707449406000340c1c2c0c070041c2d0080c11030959680e440c0065410112503803221a40020010240713110b50b10121070091a0490f402d22a82111072400e20359181b024100a05018003007524032000e80c040d01500795466412000c0360742541c0c2d134000090003c24804988555036150002081e6020302c00ea00f21803084101e921100c0240303151100354498850b01c0000210602c0001c0a1042c410110303020394000c85e0a40e80c00407840e420708104050906c0800080b50081490400001541d034403605480c13802c9481c104c44040e01e408850074001154107200ca002540350180c0c04071030f402c00980c0e401800c00303e103060340c0c1040090003a000540d0046401c2c0a9003005030b00501610f000102d01004000342c00401d0f10341400e070708050390b030402003000d03a83c4d0064000d03035110480b4104900b004004440c094000000900c200004002c015103042761901000e406184c560740071031483e07150300000328501760520045560405648191074001c0d0000402c3c40e100d0203552a00801c1c01d031007070250304000 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 255069721 1250 255068471 255068501
    0x30f030f09050616171201300b0604051b0c07030b010504110301030215091909050c09012718050f09030408151302060c0f07050a1512020d020403050304080c04 70
    0x505002c1c5c4440000040c10074040816420801c002610a12058000c41c028124616030705049860300e2082c1c901200e00c02d03400d000543c8429000c4000c61021051250086800e5a000603a070b111000340d02c542c50a405081209800e000811010011002906e90700722801041c0c8200d09036200c1c1c1c104016984610a0b03c0c1c00803505000500151034101121079103107089211583c90244424045908500c202d0514600b800e5150340400174812030780219981f20100803d91841c04407100006001c2c0c018034035000d000031054178999a0502131070314403c0090410301d10000c10300e03041484140c6c00b030881102d26006002e00000807070a000c3c800400c0c0c03005d640e04072010706a09450511102e1240000824030404910304004140c0580c840000501010f9031170030144c00f00c00751450826290a0040c0e0101d4041c510400d000c01450280085c02c4540c00740c075280811290a070709407050040d00401d4171200d00544009800003c00600100038021104000250341081c0114800c002c225803680500407a6 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 255070971 1250 255069721 255069757
    0x51501020d0e040906062907020109060e040609061e080303040b1305030d0f0b01021b0f0d08130801020a02100203010e0f180d0e181306050907030f030f090506 70
    0x8164000e40c10201c5501c0054000141c1c14545e80714441681c0304d6500604540425860000c096040c01800d8180c20301a01a520300d00003669000901c1c1d0100c500c0b0740d10030420351001d040d8080d519500050000c00e0002010b00c0000d0700e500c0c003010310780001c14551845000040c00001d120001100fa80e1284d9044400a29559220202403240c12072118089549000c00c01c00c40d0307a040594420a03000d4a4903000009284000d070001a190143e5a041366403007207071501d500b240039a01c41c1420100c482081d24030f00044582880c01c603069008512007410010b50841000c03030b0140d8154090482c40b07445600315a8003216644c24001203100a0103508124243c603000507650f0050b0801040e0052011503a5000b6500c1160845050200500e0600700050100b008201285026904c07248501c0810a08280509210071540c0001ca5801c4004161585500000312401000e010f040000e50b0000010f02c41c640d4585030040c44800c40e2070b00380c00480d918450100d0303203040060607900c119682c80d0b00950 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 255072221 1250 255070971 255070993
    0x5120d08100911030411040911040b13091104240b09310b030102120406051003080307051e070f0201030e031b1005010602160614040b0a08070305150102 67
    0x240103440101904445880c1a41c00a000c6240d803040c1c80c2034596000c0202d4607814a40340408903540705000c568441c5003041056404104048a0000c107d0411107000039504840f101003030031868030307103440a040c5181c942c1d4039040c4040304e003e8008584003290108100240851011211082e800c2c3c2071040d440004410b0042505030801400725040c02001c8454601c0c0408130650405901c1c6c8600000010b0080e204030a044c0718004c0a80c0d0700b0085000750300708840840c202800c100d0041018102580b580007017002c2c12003034448840990b07003100b803142d81d074030b00307200060540e5218450000c048003416040300d0000220b102911a0140d000910028929250300110041d02148000116500080004169224070a490803156500a05c050301180003403450503000c42d60164080c03401d41d048046403102c086000c4000001380d52090030109074030003005840400a00854000a941c00000600d540300c0f2500408801d1140307119035800e0140d9681c0049150172114441061400340e48181c2e4468 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 255073471 1250 255072221 255072227
    0x3220503010e0a1b061d03030f03010b090a0501021908160812040b06040c0e040c11011a030c060406090b0d0207020301020d06080f1c050a0311072901080303010e070314040303051005120d 82
    0x46e000c1c0c0c500404403400e0081c0032136201c50583c82a40300f00420b9000007821402828040d0005004040900140240380f5403624480381000248a009112603c000b8034540700800002c40c6c500020b400c541d4031a294080c000980c0d4000b4010744041d64010004000210180340a0281010205d01c0382d95103c102c0e50b00909002c050020072202c0000d102101300510703042e040074452546e104c1101c040700e40d0200100340074141084068400c00b405800100000d10141b50400001c404032450003010315506d501801c441c81c0240110b140083d8903500006805080e038003aa089201964804815241da04560a01440c0d9580782148100c01e515440404148418020b00c064030b6100c0e814100403401e5141e00b9161050b0703074000002120f221043e0000114042c120340a85031941d03090b00c02c015100d50400e4103040e40c9010500c0f0324200000920700140074148a5005800203040c01c4e07030145006d0034145405005440c0c00c8401141d010586080020769242590620303400380d42c80341c0039110355154040f0331 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 255074721 1250 255073471 255073517
    0xa02030a0309060b0d151a060403021011060709180504020102121806040807080c01260703090f0f0618020a050418080d06090b1203220503010e0a1b06 66
    0x107070f403030f56590035900c002612140480c0e44034034401c060805031100b10041c01000c03550010b03c0341200001d10b00d102e40e59500c074a8210340c02e480c0c04039a8107145819698003118200d00c1c140d0040c9040c0691414404804d401424140685040c40712007003d03c03241b0f07050038044440881c0d0290040e40b285035a06a6401800b0052259a259150640800442d0008903120f507006a0140445d035101c1c910070820b103803086c881c2d02d44070042407a0540900102e02002c80f0301100c14401a100c00c11950301042039107000e80c2c0700e4021140d2040207035410840703e0410540e0f040c10101305650840c10000b980141c1c05942c2000e01419034000c20300740302581030409200c01001a5440d0f00a8980f4500008003c500c04c90082c040d581c2e11001c0201b00d0900b0100600199030b803504c0024014070890240c440040008000e8550400d10103e2001c40c2d103c0150303e041c10201180d200d035030154030f0100741103065040850705a0805000300c0020210304c07054044680800c4191180b54005068070f000e80c001500d0408103 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 255075971 1250 255074721 255074723
    0x7150206040219410306010b0c0309040c120501050103050c07060209281d011203050d0f020a020d0219020319030302090301051e07090e161101020408030a090b0a02030a0309 76
    0x644082c01e512400c0c0d42440500804800a89483d89610791038134004407814118001a007060303a0100c0560b0360082680e0315010b00482c001048041440e1012590400c00c0c3c8420240c018002d01648003400405800cbc01e1040311850085805d10300041100d5010740a010300505103d10458905107841e21120001d401000311a84d0200b5900c0d819096002c0150510345000d480301f003d50b103801e141181090f40007510f4020101000301150040241c00110085000a40c0c5c041c100255103406c408400c078000d06540c4200050f041c03010424010841c2d00141940b0703004515000c030f655031503078094000f603501d81054001750715a002c14001455411020444c400491207403c0141c08c1005810010b800c0d9102180c904841115828544108070031218402d40c00000310b00b0000c1a581c24001d1482c8030180040070702d105079001e030071000302c03061064208200d6108403200071515151600d2800b41c40383d002d80d102000041444901040140d000702c12103c0d620803d070015440c10032400410313800f911031804 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 255077221 1250 255075971 255076009
    0x11e030b010314210702010e18070824030d03240824070c02010f05040e0406150f080a0201030f112b0b090f04050a0c0605030405071502060402 63
    0x10000000d03146411081c040d61007800f282c00b10440600c05245801d074600001e2071540000f07070344911021000300848500d5038082c40d001e8951800c030400b040450072140c90850b03030440e0a80800c2012507004190700c1c043c80354140b040c0011041c103002d5010303039104804420b9040d00304c80c0b40c089100b0302036803143c402d950050f9104407007400140ca88180100d415071050750305410080c40043d800c440b6602c04107818481d58136aa041d406c0c6840c00030140703c1030400090501c02c004414826150049064400910300445074403150710307040c50028081d0a039440c0d40006812001004100e01c00c07610310210550304544020684542c407900118050440b200103000c00c607551307070000c0031401c005400511b2000d000742900107206010035111840b003012002c0c40a640c5140200140071036540d00c4020340c025504421901707494540c1c1c24039a0600c01a210014030407040703a440000d9460b00000650711032802101910030503641d0750500c0c962040307541e0111005802c100001801450150008241680001 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 255078471 1250 255077221 255077279
    0xa080904050406110c0106050a06260907080a150b030a0b1605070f0f020a1e0504091a010e0f07050418090f050601060c0209131703091011070312060e01 67
    0x1c201d1300640e038800044006580d46869041c00b4909005510b000104400d142040c0340a58240e100c0a0350021b18520340d2211540401069082d40c0c200b0201000e00410700a03146040d01500d880301146808024104600d8180f451003082c034940070231024a01500081d9220700c82e5903000040b039030582d000c0c0301d070802e020301800b0001c003013901c0c40180983e0500c2815410010451801000407a211a6111100e0706001510076036594a40d0803050084490540d404100d008840c50400144110007080840e02e0303804000000da00e040211016015881902030842070b80c030b031030320300300d40c10700c942d018226004c601c1020580666038260b00c442c204c60300451400b042c5014070764665040c01c20030713030103003000410b640100d03000d5160040d81250026003c2c1c000e030300400c020381c1d1402d2000700500c00100c1c18160200009903040000d01203a15040c02003042080840c2c0010300007040794100c098198006007a030318250440007002c0c49018180c1e01054004030450703107028503524403c9203c0c445184031030448 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 255079721 1250 255078471 255078491
    0xf0303140a020a0b1905150a09020f041e0611030c0601060f17040305030117010e060609070908030408070911120121051507030b100e011206081c0801080a080904050406 74
    0x88203004042024003140940d26452400c0261b070006015000d03d5030600d0200302c0d0546c0c650308510100e41d000303035000d85c450303011118452040c0034980c4519188400f5a20131011410026900800c1d9082c648468801d00c03510090305903a03006003a42200b141c3d0000005025031801540701e42c5041d07170b440c41d04400801a00072070b10501901a5021400f09502000601455100784128040b11401900800011283d407000a640301c40103080207004120402c04100d12a101e01650000380140300c044a5807156161401a81c0700d40ca40700f00303504246001840e070f030b50502003130494950900c12025841c0907401c1000445c010450400141205a5012180c0001a10501407120114038801004c021446c160304003406480403101b08902c0751032001050210769400180c0030f8a00707403003071078103800840107120341a004200d2500440e205200301d0800756040c50060703041d0b01c01102d050b0740d100000c0c1d0740c0c0d2070407a550314129080104148404e0110380060304059002961140c0942c40c040340c00440 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 255080971 1250 255079721 255079733
    0x804140402041203120e0307030206040b10120302061b030f0f0c210402100207080d030f09080313030e09010f06052206020307050114010b03010308070309050301060605090a0f0303140a020a 83
    0x943c85084001c80c600c1d11480f01c5942c054800d15010040010140d0724050240e98000c0d25144d00a000404040850002c40d031342c0145070760104d02824100c01e0032820a4031034207005c1d54640f81200c510071070784521130314550411403d40c113680c00381284041b0001c0c0754441100020300180001d20150750301d2824081d4003440307004000311800da00840322524407582014018803d2000401528906560003c01c003085002d20001310400c5100381f170f1500003031088120a9841c0541800400a406c03000007005021002d00403a0100d0a4140310361944071195400c2c1090003200f00c0248140141c9400721079041164601400040009404404102800754007400c2e4541704082c0c0c50b041000180d1000c10100104002407280c0e00a9080d422900e480662618840303003520711050100a100d0100800c41600b0180104000300240000400a20040f92200f40c0188250032085061340301b40c2040600151504100c0c0350748d803c0d00d4050703840001282c0800c140740159400500c8020440c4501144003000c01d007 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 255082221 1250 255080971 255080999
    0xf0a12092109050d0b24040f0f0c0f0906030f020705030d0605090c070c0501050d140a020307020106090911090c0d090501090210080f010e07021501080307021507080414040204 77
    0x203100000446101c060400181022166040380d4010464200f42001188840050560111249072292840101c10061003000042c90b200650040c0c01c020240300059482d411902e9040c60082c41003100e05482001242c2c0e0031002a08500420f02c20101808510311980042c0040b16100001515003d0942e65007490b40d8000c80124400d075175104030500c19450011245608220701c1860141081881e4070f942c201c4011b03c1c03041c6818003000080548043c0c0140e04503464007140640c031442e091420381c0b4080041d510450301c2034015481d00700e0218036040f1501c500403155403c1241060030604100c0ad201c241840503090801102c1c0a0104410582c4d41d07016201d031417403260380045420525841444401c426400704002400100410094154040107d45044a00c4002e840b02c0c6911418400c1c0d0501c80146d48400004c0c41010001c10700402c0000107240d9103209a5000d20318001d8050f0a4440340281c880017840303408100001c209180c046d007106a824003000740300514060381c0b59000e4444a03 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 255083471 1250 255082221 255082253
    0xa17030c03040f0801051308030105060a1103031611012d020f03040f150b0303090d0813080c032407050d0b0a030f0c0b03010b0912120301061d03030f0a1209 69
    0xe4600c3c8103014102c428080d00c0e401043c4009039a8606106546556850105015440c068040460703000c06842c815aa000802ca5546056030350b03070305009007402c0700080c0725195000030503105420140354910500c1040540a2100301d04585000c1110304084054002c13007200026503028011100c0d410f03a404001c4d03004910402c2c080010385854582581f03420550380d0000700035403a00d0881503094401104492008500f101e6800540300707285030004d003a008420303115500060510300480e8000e00000c102180c804200d040744c01000b6441801c00c81e90003980403210306030b4440008201098011401303069500b140c0740010a28489803404a080d440081c0d0050380c0d04964001ca40c02400001a441d4004d4900c810b1040d02d5507050406000882c0300780807180303006241e42e1041a03403000041c8569900d400b0514004c66486d65100d400511030322840361070030f0410b01c2c0c2042c1e50002d450008215003020350368154180c2070100b242c034196011160044100700d0f054403400d0382000a007107201c00c55800 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 255084721 1250 255083471 255083489
    0x50a06050c040f050d080307050703090317040603110a09050607050a0b0f15010305010501020316020301090f030203030f01150e21010c1d03070f0b0f04120b0609070e0a17030c0304 79
    0x75501c1c08040b518649150b504c030382d0041c2d41048443e00843c441c001165444081d41c102207944a00501d421a21000c141e032001d000a07480740000000400c14800030030868000382d60600110311050400103c078451025404049030f1804010072407800e014000d000000e0045040d0b0b0182000d94550700700065007103840130b80e0301c000c803000c0240390f0b40c0d03081c8515582030007031a08110300d41c10640040e40d0b900c180869480001a540214011940c0c01d42040ca0415400030000788590314618000e9500e42080d20070300c004c59140b1f03002103030820300c940802820800659800203041d05501c18811210f9100c81d404960340111071903908001d80c00d01803000038032416512008140442d00c861a8110307610300c5851301ca60440e200410008828103490403d03140700d542856034401ca440020707103040c41150700c40c000c440f207120310b0301c010301400f030303145a103c0c0714141c810050560740e20400700c80c404040039040b580512030751000e018003002c0401030110710fa0000100d038a8201400d603030600d1504690b0200f016 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 255085971 1250 255084721 255084727
    0x12100612120302180111070305100c0305010b070803040308070302071e050d020c01120218090f1909051b0103060b0d15090204050a0e06010201020f0c0616020d020c010c050a06050c 79
    0x10407214498201d2110390500d021410003501010348100c03020120002130400c65010320100070f03140700f44075000003954400c08030340da10324541000c030001e003000750030709030100380b501c4000500105a80e04945d01181d226078400d10355134541e80d0584900300c0103800501050b60a1000000180500043c1800700c0001000d004505c1c01501e4003d02c2c103055144c01c0011500301c3d44803d0300903604450040c05540e11024090f0301c8c2c1d004c594881d4507000c41d940c4d400350f210b500036060045081c01c50f00c0090245280c54600b07501c0d424040348847c00d4901d0a04000d00640c000240d483c01040103840d401c4084130b052402081d0a50764920003600b540005421710042691481280010b100f1904c0242c001c100141040d400c141c0b4040028030215218410350070380d5400382d000100d02d0381c401c1d411261080643c0641c0b03612044411045c9507615802c50b4026001c5224011440b5014000244064095500d50040c40300c1e0070400c0c01100d0342100d070030085031030340308500540340054058050148640309644005032 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 255087221 1250 255085971 255085973
    0x150d020d140103050a0b0c160b040213060f170102040506041206090203030c1e01060305060f101203051b0115180207050604030f0f0804030512330a0b030603070512100612 75
    0xc00c06c00f000e042014800020400450002a43ca14a2139030642000d8000050303a00c40c000314035000601810fa1440c946403620114031119881804000d0354214410b015a01249030034642c201d120305d0103916440780003404204a40e0781c2c20149221250311407500451005059030100e85142c001c2c0c4010041354022149040c4000041200030000d200201d0003440418955210591600000b8041800800300000055000101c480d01c1c7c1c1d0080200d040c1409015490b070500a20030f810000c2c0e02c9070038092030310104008003c1401031b664006944030086032443e103014442600800c003070314208420380d0203101e2000442c0342800341c24466402910f030081d1840140070000c2951000000903418040800c040c400420b40c0b01c016164412040c4622801545400c5200c80c1c8005000c8170040b03000030b182d0401c48541030400781c00c00d012501a2000c0c840d0ba40c40303003a0110705000484034641c042e40261420403041c03400298030250380142c1c00035a440240180d010f001900e01a0300704842c035844842c0484 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 255088471 1250 255087221 255087233
    0x429060f09010f0504021b0a030903020103051e060f1203070803010806091b040c09081006080606030d0215280b0102100c0c060506120106090614150d020d140103050a 73
    0x10036100812541080958109280505540703d04d001d264091680801d58081d21010620042c800d000104100c900d8014a480d00626203003103404202c1c0003904080c049001d58080016054072191450030482d05c44e90f840081c450a200c4504100c0d501101030803400390000c01c1070000b040580d0094080c180e0f03941c105004149004806080000182c0c89001c20300e8503880451a003080111080b500400c1d101d07001d01d03003100c00d00c00681201c0d580b0b0082c24800f940104156005404480324481a55003640d628010580c031141d0300800314026812042c420810300031800320301648456645008443c23803240003002c00d0000207042213010b02c181d945000701c6071580c0410125403115085581405003040001c0000d0072400c82080042c5407036101c4000c130f203256840403900d510711000351008215541c2e507007001902400185c4102d2500d01d10001800019041856400340b04070741c0241010721b40b02c1c55954801c020740c040031500301801d680b4a02d0f00da01031054000c041c021070261004042d8486176082030 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 255089721 1250 255088471 255088489
    0xf0408071d0108101e0c0201020a030608120d05190914060108190209040c05040507020a020f06091807031119021b09010501030f0f140f09070b09040203042906 70
    0x8201d05411400040001d0792000400400d10652800041340c0e0a0100c505824241040d04540403140e00342a1801c0510307034158041c0091400c1039405002581d50303070034a01c0d1a08090720004082c0c2030104212066600c480e0415078010100d0f0007422281d6403c2c00380ea00844240c9002100c4683c0200c0201d9a001d00400207a40503260480c0030f45040d03c0c0c0c0180e0803600d1411804024060b079040f02c00a024003140e42c2a450040401038401e120514241c0b1009441e1114401e080b446a0310a010000080c01e225042e1000440701130b041c1c0d01480e03c401d151280b005402401303801015111000380c40301c091040042d00c4c3d160000d80d0040100100480041d0030000c010304844650104511000c660740d4800c440d083c1118000c0c240080c1c003070f002a1380c2c7c60142a02a42c0310f42c0c61810701ea40318800c2800345030003030b00c180060760f21203a05031208403000351590b0040c450300c0b804100600800e462449d1a500131a0020322481c00d05014488089600a0380d4900e015442091217405d8104015400c0290359 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 255090971 1250 255089721 255089759
    0x105091602100c02010e16050a1710090507270f0b010905091308031302010809160905150409060e010b012118020a03082701020d0c080f040807 63
    0x5080160011020025611040b1503501e011280d22002c02d040c0b000e000707601030201c1802400658a041d224140207260400b05031003200e0003004080d1000440044400940c55101c903501c000e0b0608030358034402c0c4c401414420005450a0103903640004402001c0a031000100b017840300000100020b82d60314030101d03280d590b0300d000c19a081c000701d12030907070340700e103514003612000c032400101c607124954040022410075500502200c000414071a0504070010400b010b64400da8500719599202c03a007481d11281c01d02100d40048111100c14494500d90f5003100d035205119400400301c0304592070006040d85d86e00f280690f852075552440c04c0d504a807e0103021444102800c101c403440ca180b411710400c29240b8040004d02a607120807450503441280c40c0d00e60300540007051011b0950326420300203419804001007215620f1000c3e1070201095a8400e40034038100141c015000719008440d058520252a8004949040e020040d80c84990108070140c00541043c0e00286a805c0c10405c0c40c001d20100062 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 255092221 1250 255090971 255090991
    0x609070309051c090f03050709050c0a0c0f0819030b09010f051e150403080406121e021605010507170a06030c050d080f160b060411030c091f0503010509 67
    0x81c100d010440029096140c03000600301c036000c9101c03011085890300016006403d020086050000c03d011b00000c240c815502901020809034840401c000002e101d801c1c07a82020032182408903000c28041c05084001031301840c40749150142d04100b25070034805840d20480425070312030000c3c10600308043d402d03014284581c900d441c2d050528000484409030900c2107030801a071a5402210b030b0311290401c400360303102ca10640303071160307103a00c0e00014a420074040d940c00500205903440d0b1402d158010703d00307081440c0b11480e01e000202009031010b5400340e180e5003022900540c42e0030020340c0034410700e071240d869641c6445503104a4105142c54400140410604a04000c010300100c5c910803c0325040714011175484407200307114a03224245000b0854400d454000100b241100c603600b000004141318030820401c0007a94070f002c20001120060803c0c1111050184000340c01c0401712030040001c244c00900b40c21402c840c031210412520807000c1c0c0311000a101000401140c00c00d03070305094005020003 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 255093471 1250 255092221 255092231
    0x60c0f1b140a03021509010c020a0905040b09060106090501270e0a1d100e0a0605040c06110f0d03020a0905030303040606090e0706020a0f0305040312020a05210f030a110d0506090703 80
    0x6000140351010a14144103045c6000134120181da0180d0310040500f9400b80c228807002c4c1d50b0302c1c4440004d00c404c480c1a52100164400586101c6000c00d140c2d042e52801d4803121030460501e0300444000807511441401d14800c20220000c509451498000a01d40341d40b40d42c0b9949840036001c0c0c20354030f1001ca0724481020a16404024060104284407814516100050342d48048003942d0b00e03113110b00b8009400b041c43c0070706010501600030f004c10709880c40d988442040c1c0070300c0c0f00c0319a40c0300c0301e0607614245a0001902035510510903002060600e43c6460700c00c11a948803000603007103501c00d40c2c0450b905070327a070082003051503094010b404845800790050040c0030302d40300020b512900c03107020062501c03040600fa0010140128240e40195400100910341a0b9001c0c5010b580d13110001026505481000b200d00d20500380d0081941c11583c1080f1002e0a060f610382c1e030340070650801340500b003103180c85030a0f019401f80300d08041c20780740340110804034440c1814030500c01c002c4005444001018104 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 255094721 1250 255093471 255093473
    0x201030609091a06031e06090613080d050a0b19051e090f1902040602010c091707050d02030a060e060a0b04020f03130606030519030207091401060c0f1b140a03 70
    0x40c0c201da05080c60000040c1039507911000020306086c0118034203e100d80c0d0030415030701c00f00000180306104590410441e50191119643e42c8264042034600416641080041c00480200d603005950056520349010441c402410001442489030282103414030840c20001c101d1482c0280c801c004480c0d994401c015181c5101d008154091002007a55044554100c08282440d0b80030301d107007500030b140300e20441d1107a4032110028044c00700d06100c0c41c0021407581001c5020001d00380f40d100030134010001010b503540b5040034404a0309102c0000d136818081d80c81030300c01050060042d0810340301a0b002510b071510b0200040011500e01c06080ca0103240f043c05000f14414550084235000b4004140c0c011282200d403a19102170403403904000d000d40900708064104241c82d80c07002078114440d0f0240c1e40801d0321111980111695800030741c0d01c0384d28401c01080440c3c01503040b40e003103d0151a440000311003a886001c0c3c11808040924080f849150040102c040c07076000342a89138401701c81e054007103469 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 255095971 1250 255094721 255094733
    0xf19051b0a0e150a030b09010516020d110709060605040f0b090a060e0d0c0608060f0904020904020d052503020a09020c102c03030708100e042409050703020103060909 73
    0x12406202d58140700c070b00104181c4028580416600100100000b41c503985a1500301e00503c019103c102d1590700784008a40202c20b81024116005041e500410400725041022107000405041c5450700c4e001c2d4000100e004140c40c000c032400303042c2c40d41b152039846281400044510200d03501013502000f0a0204c030301c1e15503400314280d04840a600c0d0112a80303d250001070b050080f8101e00030320f1a0f40c40100040d865030004001c510030b02c01240d054110030b80358402c2c0840d003202118000e5000038880001070051901081551a80e40144100d03000e601080340021703400710440c252406902c3d0b8034503080003140740c800703007050141840800030b6041000c000241603032a40000d803003040c0d13551101c0c80d03408281d80e08000c01c4001144240c104180a9145e00c2580e00c0c0e0740196018400624400e0018204650052441044940d0400301500b00d40d65620381c525642c441c2c901c81c901038810403005103014901405a02a00c6004401070100d5520b144000340c200d817600e40c03143e03001506011841000c248 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 255097221 1250 255095971 255095989
    0x22150c090b0309150c09060a020a1e0510020c011d0615010306060f0c050321010e06030a0803041e0611092d010e03100c051c050606070807050f19051b 66
    0x201e248504e83c9680f940c05600007540078080200b500084040f40740c038451a8002032075102d96001d03040b480100c5804000800103201d640c580900994094901a0b2559900d40d00405908140e400000303240074101440004000941d0f0306041c042c2c1c051300c2403180300078009250004e000c1003400e042050340c0c40c1180c040c200c04900d11915050040c2070b510b040a11034203104803410924100700b80b0070481880158500e05a900307001e00c1c0f041201400000f000c80c14001400303146950005001c5085595a0380c1c0c907100184070b106400c0708250031040400009a0714045ca0b9103a2aa07449001c0c1c0740d440d46414400c0400c15148504140b82505ca018003010b00c0501c0090000a02880c11030100c1c04c6402c04a8238100c980160603000038a01051480f0503580305025116500b2240c4510380700e0070341c0c583e0810035a4801c1da811075020904204000008100780000d218062080013600c014243c1148190304045003170088110082080c428141000400c0c0445009142c0005454207520300950100c0c510324 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 255098471 1250 255097221 255097243
    0x8160804020d0c1a0c061003052503050102030703020405010f092417091606090312030203181e0f010908070b09070902030a020a1704020922150c090b0309 68
    0x100044982d41c00340300d443d4400710f0107880c0183d11403100d031006807903401c0c40741d00c046003038007060060300c01046140141c1e1019600b2281c006000f0302601c4003410001515912440d1a4940c45d0a00c200c000b00251003070014503c2003245803801600c3d5880c202c0050000d05003043c01c00100007040d4814800542800ca240c041c40100180b003100a05c0c00c9042035403c00c0b2105814107500d102213007005910f80000400303120782214105640c0981c0e86d03455080d600c9440300c5c0002007900c5150740c00d03141040c2c841d03406181d0000301020300c44a01c0c4074941c0b94904219840f1109182c0740d078003802003002c603201007094526000301d100003081003e01d00c4d06c0d090680e004040d030042041071080045076862004000d4400034003c0d02504559074286a60b981000b54040d01c83c49001c20425090f14864403c0705042e648165009005c010440c0d65942141c400c94021400c840760692101c009180844c1c80840d460f5501b0000c2c200018502d1413031f80c00902800c0c0380c0c0e44034104080c401c00410811101c0400e05154403 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 255099721 1250 255098471 255098479
    0x81006030b010e030303010f030512211504050406061719080a05091c0204060e060915040f06030b0105031005040f0303050405010b0d08031b04060e09100e0f070816080402 75
    0x410a0340700100c1d00c202e050b03210160301d44000700c0089003002a103900c040840c2d101e40300302e620210381103210744028081d5082c540f40c8900d00035079104107801c81001859010200c030607400c0602d03c0440004080fa003040d40d080e45e030f550742c0c1c3c032051084072402030360001b403201000d0050603d29080b20543c11054264400181000e2010039451501805207042d100c0c040c80c020581b46909402040c500c2001c0031074081a80700b241040d00000e511303c4071103401801107401800d8440780303542c3e0200102d41e44003150886034001d5521040c00e00b10110510408000e10f200b000200d03925450a000c0600d0840c0e61074900540c0ca03d02418480015030300c4207440c40490341400c02040d40d54550400b80c0c01002401c1c00c40381c01841c2900c035102004040e000841c8510400344001965907111215101c1d2030003140502000f10700390030754111301c038a0000f6010303511284420740300c80c4280e100d0b614229030071016520078218080346002d21120b980c1010b80158010843d45200840c0010054024200b1101400103401 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 255100971 1250 255099721 255099731
    0x4031d1905040f02040503030417010c0807080f072d030e0606031e070b07150c113f1917011a0c0609100c0c080403080307051306030b040c08100603 65
    0x412400344c0650740180382c028162900c07107941d850228898509c1c40103240e8294600314a4429150140030914010440b5586003662650b8501c1c058a8090003c1c0031a03007440030030340c140d00c400d02c0304904000010036041445042181029005400d64882940d06040381c1c1060f010485103850000e40c010700d4032004104400c1283c4034080c040e00b40036003504109914080081e550040c01401c041280f005980b0050070481500102d1007211610111049200c0980290724a500446821001d5200c000001d8032080c00c82c040b2054982d140c03800111000c40380c55004250094031041041c41e0901284550815005d205020480c1810003041402680041a0612198103010000105070390050004a048821908007070f000d907540c0300004001e650109052407000e10a0310b203c1c018068200d0790000c08e1504060541c2d071402c1854000410120800105100c0541b42030142c0b580800244056180047c8101c4000d0501082c1d600f50310001041c02040e800740803003866200003240c100c034410b140c00a0 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 255102221 1250 255100971 255100991
    0x1090506071b06060305070e09030903070302011d0904050d090b0a02070603020a050715150501111002091206070314100303020c040b06131409070f0c20040504031d190504 75
    0xa90b41c00245002d00568644040070081120024096080e14229428146242d480b8a07000c1c2e601d100d14945150150800301c010001135001e0651b20162284507035110300703010a0342c00407400c080e1048600741c9041d4440e00001400c0c41c0c108e5000303c05000321656581c034110b402100a540c80380d02d881400c1c2015030001c1c1c0c2c0740d1580c0c806e409640c04594401d50f00031001e640041907402500031480011440840300e000026158010840c1143c100803100180a0824210300d8020003500310b80607458203c05030a4003800e00c52028840c103441400103440c001058000c2031610001c204000b814450341401d20441070000c01d8002501c1d0388034500403540400c1c1c2c04071032000715a550007400511480c07080c43c8640840c904010b6203007248414019601c900321903503205000c49403c003141494902007951040c000300030481a20246400d482c0034000c600e05001c4075400b06c1d0444408480641c000f469047c60030900f099032003071500310400704031040c1034807022401d038a031105111841414401e5642d14400c0c2c1c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 255103471 1250 255102221 255102257
    0x31c020a08030a020a09050a0602071e0e040f0b07020d1707110106060302090102010f0911130605030a0f03030c020a0b190906090503070308010902042301031b0e0307080109050607 79
    0x681601c0d8010103264590504100410280d004408500b0206049080119a40c1400d80000d030444026600501d0128600721070481a039003042030308000f6480c1c0c480040703000318010712498051445200e110a441030941041300f100034001e4803240c21900050010b502840c2d00c1081030041c0101c035807000607035440e26001034401e070440e081d5032080d81d4240b210001e20f036a019806132101150a030000e008090103407540714200c0355490001003c41e0002c66a0b08124200132031040e0325100922400036881da20344d030002c0c3c5405803040d411100540b1b0043d910b0b040560600071410f03004401c1c0000c0c0354002032591184c0c60004014104020507100480200b98506130b9041800b4182d00080304210581507401c0c44c54580d44403400a4001c40c04140000510004c1c2e8800c683c1258005650040724440c1418000001400d0f084000c3c101600c44140540c0c5942c210305403024100d403916050805191030050604100003580180004d924000c04030000c1900031030131136440081e030318102c018042905242 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 255104721 1250 255103471 255103483
    0x80f15030a050610060908190f1707061a0f0907030b061306080c160b04080424031107050709091412030906280504020121020304020405070c02031c02 66
    0x89541072056100d400140100401c81501640441001d81080c549a10b400c0c3c0308804c0138400c044080d40001a58840e00208609901c40c0c94411041d50140080944402c0b200d03d56000c0c64a42e2805e00180400800140f881401d0503903800e88181c0e0344002c04540000d01089100c1040da005502d15000100214403e0f84000b807940300003030840342c640c042c00130125008140c0f801043c001c03840250101e02d00c201000c058070700d1910745a814001050560740c2c7d800004002506c00c889030740c024400440c400440300031155420b00300c02468010f0142040004060b5905024010038040301003100f10046000801d82d40242d40c1140340c04176611455280c141c0b40c070402e8041301039260148400000302d40240600450250388002c0c11640f460f194904c0401100390000a17400107d046101000007960040d04125401401410328500d0440010b00410746100018015a007250f4008200030451a144c03184a130004800c1ca408030715a801640441da41d140b410806013101c08407401c5c0f50802901c2080f00e = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 255105971 1250 255104721 255104761
    0x71d01031a0a1b02011b0809060106261509070503010b04030f050319080f1b07060506150f2a0712050f010f0e19170901030902100917030703080f 64
    0x1d204000f0700a00d07002030080c8004030070300100058004010750301c18880c450043c0540b01e001c01030161646024016200424101640b039240c62044500f41e07044030a03140924032480e1194850000c012100042203c1c0c2a4010110400c1c09800d00060121030103c006a40035260300220903100740044c1c0c14890b14500640c025a29045403d5a013a03a49551086449007c0c818ee840c80080d90f49034034541c04041d24408107a4902204240580340208106400154002000be4075000c4160f00c8000e81c9070160f40301818024517054000340c006a4901c140d1030000340040045880103004002c2010315407075495601c00c178002c1100b0720700076405014080c0a03450018001e803000300101c003101e085403009001d404e40850541c0c00359032005211000c0003040134800700d6010102884502d501001031146402915005040654907107070000103848001170a404104a41c5695a1080ca007101503040323141c40c40804901604140f20342d4000a400c8000700e50481da071202011220741d540e2202449000c1d410310 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 255107221 1250 255105971 255106001
    0x6071d030102160b01060503160302161502130608060a03030c230d09060c020f04111c02120601020703170304111c02030606030705030606060d020c060108071d01031a0a 74
    0x1035803102c3c543c0409010030214428200700410783c0c1c3e98030060f0344900040355500c8958084ca03900110b407901c6030740105100303a40d031081c0101e100e1076034071120000a0a0300101e80c10325400940030244c04450080c0d60700411982c40c2c400c000d444c1000c0840e03d00a00351000605100140c040c90007000102111800d2080000000718690300d10045020f644071141800440451140c1601084441c411400341000e80e40150040d040c0b4000541404014400c2c2420f1450001042c0910382c02d405c80d001c034581c01301c16403c6002d42c545401710340c844903601700900402d06640c001001080003c4d030301028040130300100e09180d0303169651801c002c4111014444503603130207102d40f02c9281d0700700d4403c502d200c00c450003a400c848e220f64a8000b8159541c00c607024203907265000c1c00c0041d06030f2500e84010481107141d80d801500300041c000407680740007820307001059a0381001c86e0602500c1c420340c40c8110386c0a00d25200c01c00c03e501d1a00e640381022251540e80c0b29a0fa0102c001890700c50701e580041802c1c44200c4 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 255108471 1250 255107221 255107227
    0x5073005010e030f0d0c03050c09100909020c01021e0901120c030f06080a06060905090c0d050109060204030c1a040312050a020a0b0118150303020303070f090801110a2006071d030102 80
    0x40c1804550b90320064a400480c0d15081c0c0400e00b0364420b08c1014816130300410710383d02d48a803031020410310140c0441c080303007000050351021840b02414000350405080d52030025032a50307050380a1400e4641000034104150300b05000c80230840e070b84165070481e0711641c1e8100190035016517000300c000e0180035050034921400c0100c0081c040b90009000340711940200e004101241d15440302d4003e0303032020b840411417644011900400e918001060711805e070300c82d070000503014803690366030700590b00503031b00584160f559032100b00000d4610740503400c0c2c9c00d601c014400c0d15081c2560303a0505082c012026410800c200071030700c0b01100e4020480d00c00000d4010800c98003d69590b00002da80041e000c482450550070311710440050200400b5034800c0c0c0b030f0705030091070440d5254801242e10b00ca007614600e040100b60f20300014458401c2c840c900c10700101074525644d039000f00502030705501c070322042c043d00141c0c000c540c10301e41b80c400705411f6044001844d24416918071f0520400d400c1006850f1a40e141d4400 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 255109721 1250 255108471 255108487
    0x70c050604030f0210051b09030304170a050625030e030714010204090e0106031e0812130b0711070311060f040e010512060f0406110708120405073005010e03 69
    0x400380c40d0089940a60840c5c00c0c10020b401010251441036996840c8015100c00c03030f03002d05458001814036480054100c03801c1a07918004041c40c075028620380c52039504001c541c801030000030710249500142440204020021850324503c2000c02684a8400c044ea642c4603641c12032424000c45101c6904030584107001c03089110040d0007984030b8482e0b19144c0c1d18203040c0500985e018011441240e40100008007150145083c00095508450382140c1141307040110f54450303480303150083d00a10803113030160004442868440c006003400b500840600c030700384a070f0900d0030b9000501c3c0008e40b9800a50781d41801c0b20707440400c035a030085442007a030209002c070300480c0c82c000c580c80c4d19048920071a140c071459400c5940c910745a43e0180d920940c641e041c48000f8011400c0c94000400c46112407015902c0c00300b1940300c0640b5604010340f0001c1c40000b51050100740103041011001410440070b4410050311020001c480c0b04d0402c620000daa584064194000e100c0294081d00840340100b09407036480d810 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 255110971 1250 255109721 255109727
    0x309050402131509050a090f0207140105040302070504020403050c1e040f0b0306070801151b021206060906060a0c0f020a0e190f0b01050a030b12031c050906070c0803070c05060403 79
    0x40c1c0507450402c1c43c0c0b030000364072242c41007024008580300544107400090411080c00f000d0555010868411a0208012000a180e030003880d56600e6410b00001064181890001e05020141e44240d22036401448103202280010071560340601c402c4034001041e0b15006541004480b148100b55801868071031006401c03109a00700d0654905c0481c140d40c141d648800007502c001c0420f0003186485013900e0412030026000b00180882c403080c402220b003a03a8004d034000340040c406107107002c031325800000c10700809003800c11540c0e820600031a141e074201500c1e00d4000301b8201c3c01c3c9002501d0110f00c00664000d41d22419010b502901d01848206940c1c9810840d03481e4205400d80061000c52401d004402142c01a11480001c048141c3d0307072514114080303008401070460544110751100d01c1c85820701207442d00704010b200d25001080650b0200480038981ca044802c02091421560002e10400100d00d5001c510b907030807140c1c081603281d01c070f4407100c00481d04801c070980002c00702d104d1341050200307040e0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 255112221 1250 255110971 255111007
    0x1d191a0a050907020c101112040618030803061c140d1103070b06060a050d14010602010617030a0305130f0503030609060d02090a1116080405040608030f03060d0309050402 75
    0x18080d248000141d070788405000d8400011140000180c00811200c0018903210b80b18915404c2e46107000d00b8000c82c507200b42ca09006140c07001c81d4401d0800581049095000440950299070f010039409005240d91a80303410340c84014400c510440c3c1850030242100520b042c0041496000485401c100b003074441c200d942c80700d145000b00081440034262003400715000044540707041e80000c400781d0326107940e03080c8540d942040c01c070181400002c2c0311040d8416410312800340d568220660841180d450144083e00f1920980c0020562000030058200d0300b00b000030882c0d1030141f241c80d00041039515841408821aa40d210081c440e5210140c00c0e001d000002000d980100d10444414010b0388402e81080401521490001d400c40c9290001801302005070341b19804100e0b46207102440d000e900c0e51141c4000454a204856103900072500b80b00a003481e02c109009007451400444c9814000500c4950501006080f6031180c480e40c000036080502c9a01c120000f8107002d0000d540314108400c6600c0d06c14 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 255113471 1250 255112221 255112271
    0x2f0a09170f151e0a02070210020703031214060f03070308130302040f1a0103050903190809060a02030105010507140a02060706020c0105090d200106031e1b1d19 70
    0x110911041152441c225100e02d8000c0a0140c0b08100c01d032842800f090341180000c0c142c0e0b86242c5c4c00e02c000c00141c1c2350315a011b201d0480c0359001c1d0450909526010300001c4a90b0301d41078441e85400103060307901150302c0c1083d0b04480c086890085940400c40020300d00701140d00010001000461003081c801895429035054910031a030911203560044113580456200780303613034040c80101d45a1410594041d17071040e908908200203680c90070f62407051b140e0f408072000480e007002820190800a007000203004680c0c12104820f003d52655140c40002840e5001d44000079013821080c0d541d048481c0c1d420024802084c0d8061302080c0c54991605201c0b0082d0010201c0d0903c035400c24000880580380441d000030003904680b1008000b152400405010108100c5903042966859101001207070f0b00301d0440082e880009031402030a42186080400100c028202c814030440040703040c491008140c0f41801c1e03a50501501c5640303076580e01110035506100701d0341314030200d29000e071803002c401c4400c209071424 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 255114721 1250 255113471 255113473
    0x20705030a0e030a0308061e03010612050c040c0804020139021009080714030309030303090a020307061407060c0e090108010c0f0e0604050423070807032f0a09170f 72
    0x460102c40c140b40c0c0752440444000d00041c5c24030b0005102e072a00065010384150050b1502d202c100d00c01c00403070b00f12460782e013280c0600500c106580040080c10082c4078074405080d44d091002c200244c2019208660141009040c000700c41784580d204400d0529006581c03c01311040b51900b44403120f41c044007400248280c1c010031060b254034110724084e50640c02101d05c22402005200d260100300283c3d9110502e00d640d16000c1044107954a40d07081005d18001e008003400b51021a82c90f104161401003260b01ca02c0c00d10043c8051802200c900b0b0041d5034905410920100b00e25a2405044400d540c02001c0550310685100000c5000e040540c441181404241c55040c840188030a043d42c415825489041d03000360300300030034461400c01b41c106241c901e9903030a080c554440c07a00d494600d841000c9a0440c00107401e00100107060380c0c1402010920042d2900c0c450000641400c3c00707281245541d86402804000107803804034911400d9582c0c020b00a10031050208011005031079140d462007812a541 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 255115971 1250 255114721 255114737
    0xf080a180e0403170403080a0e12040b090a050d15020307090e25050c0303041b0b04060302090f04020307021b190801020c07090c0f08040606050a0305030d06090e03071403040504020705030a 83
    0x101c0b131320010441c090794164680e40004c0d51102c5001015211842031140d85000358201045102d6215000c1c0020303041101800e602d0361003000510084102540c0b0441c0f2070f04c0d4544158003c0364a08500003642901c039803000d60b581c1c4e00c1d43d10560ba0b21205900181d1500c107000b040005180c03110f60f1004018040c4e40c079500e1000402c4004550500401c061282560001c1004c50300240440f2035042d240b1b070202482c000000d50718030030700009411a9201d01c002c82c0d0009a910000c0c50905018004400202c4e011821030420b604000d5482c07408010b0200303031030181c1401e032045680fa030f01c2e14036046a4980448103800c0c4c8401c00b8501039040050848002d200d0b402001c68034181d0b5000d40500f0b0300c030a1b51140110071859a0848d41c0c504040c2c4142e524569854000c50340740c81e5205505d01a5003e0001140d0300c01c2c20385c1c401d208942e80307580480e44140c5003a411280102000c0111203505400c04030b01c444100000407090700358030956014640c032520005800d01004408005840412043e46039503d07 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 255117221 1250 255115971 255115997
    0x11060709081b03010608060f0907081c03050603010b0915090906060d02060a230a0215040b06060f04051306060f0f050301030605150d061e06030f080a180e0403 70
    0x340da81000d014260070350700950307098a0940d880030b951411004004002062250359414000e0800900b40d0f0711503082e010310b4007000402d101c00c1040000800c950f00080c40504058000f06442080e2842c1140801d5201c0b4049400c540d425003002d40e07500740040417031b24141040d8051084000854048500a034003180010348070b810089400c030301c035230006000c1111003100e80d030800c1a0350b8800112801400078241500c5003020500c000000c80220180c1025070303502000d54064549440b009405850b00c000a0030003000407500c61701c107030f00480162262505ca0303089034079581d440d02440d0001038000040441c1840602c40c5a001001150240d0321029241080c050048400c08558544080820402c100400020700c055000c258010b0000c1c120036001c14100000131810f20340900d003510b16580720320301010800480500001c90b1405244100f10080c699a1107d440c0110001e016005082c00700714910f24a01805c0d014000c10a9103070f03a000e2641c2c0b078a01c03d90034110260750540001d041c24120304 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 255118471 1250 255117221 255117227
    0x11030304020607080c030c06040803100801050910020d060506030c04030b060a06020c01200303090a030921060906090c120c05010e031507141b0c150a0513050a06110607 74
    0xd0003590090806031400c48561106006540f100c10b40308914842007008001038842400b02d1405036205802440d83c0e230030a0131503500d07a20b105401140490349401c041c000420000a4008003088820101688480c1c3d0155000300908441c0c1c44190010310000800003102c0d0300754000d0003664072600d4900c0403911144184852100a1702030400540d01400c00c0349003a45c0520b4007030142c500041c2d660500c9030801d07110107096400640c0c2180300c07079100882e0b0800301504000201c014180b003240b25044114101d00790742c0b84501803070014100d551780340910030900580d5044920004d412911102032150380d50003181044204500a8902c0b0810031408034841d88203000c06590514014000d107461030180203080340100c03001e44040244080e8040d040c211081c1035014101d1490611034200002000601d46030426014010142c859000c0034840b03d0144549816184005041d00d0305c10303222090061800d0b41403142c1e42100b64072404800000480c1c035030004500ea02e881c140c0c01541c1040e11401015 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 255119721 1250 255118471 255118477
    0x4171f06030f1103030d020f0c07050102060c040e091608030c15060a0b0a0306091b110a02010504030803070e06121906030507050d03050f070b01060f020a1a070c02031c1103 76
    0xb480031001510030408182001d040c880c94030340c000c05030307841e144140000f07078100d83c8524403a45480c0404640401c2c0712a082c007001c1c00078002800507201038504a8803543c043c0c4514000d00040b000002e010407090002000000c9904c8401100c1d036440039201c0540503940d03042200c8101e079900c0754400c100302000300900c2c900c0c050340000d0555100141089098a10342c3c10020101c003c040d910000090811490301491a205071600035045403001c0d80b5100030643d0400380042403032640320110b8840140d0b8490100c2e0116a0000740702c54407511307905402c44008140e08030003a40020049809609440031007070460143e801110348881078062007205109440c2a0311001c0d181d6042028200000d08022407100c0c0314a03c41d10700603180c00e03000f8089640b107400020094400e840da43c40140a11a0000c1000e10104002d0005210030203803540c410300c030f0040a294030340000c801d14010a040902035040100440d6006041e1040354540c0e0103059540c903961081000000c08036501800700b06008411 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 255120971 1250 255119721 255119723
    0x915050a0507020f0607060603030905180402061218070803040611060403020c06090f06030103050a2a060e0a030f0302060702120f070204020a170106050d050a0507170a0204171f0603 80
    0x11039061036490303004c22034402103120102e90070180800c00f0800042e650701c14580a5440307a1202e001d00360030103091020f40b0030801e0351100d5805140c1c051001580d6140d0a4907072912075962813480e2942e4114120400c50045c1042d0045441141d0022079074441c00700c06002a9372040d910075500311407124819603110300999014000d078210641c100c000307007003120041c41021030140030f030049059480042a201c0c4c0c070981c802da880303070401c00040f41044468040d8805468000c1ca0300594640e07c4900b2808400c05840344c0f00c24032800180058042d114074000600a58005c81c480700401c905080203921000d040710388a0040c00380110f559184903400d02600d42d00f002900901e8105500355090100950043d0f1900c018096007070b070341c6828034540e00c240c41d010f8203403603540d070b604c4d0042d00c40030400399440680201045410302c010001000d078008001e520203501d80c1c98069494441e014032000a1146802a1400221152102c00c2c0700c080002c42000081802410180c0c2e00041050340040307680c5404 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 255122221 1250 255120971 255120977
    0x20a0f0c03051c02040b0a0c020301050f06090a0e0a0206030a090204110a021e0106031b06020601060306050906040504030c02130c020c0307032a180f05090601151206150915050a 78
    0x1d0f0558008081c01c9840b0380e0101050051905440b110380d080741e60032461004001a00c004052021400c081c0902a000404808101c149080139400500c0c1628020301440385641e6508021002030820807140000a0b0082e050076030724108041c1500c0034240c81e00090b4003d9080c43c8441e2000b5950408994140701d20b81e0181000c2d4500360099107850100040440d03403903407940000310104080740200000c0b440141c0b9841491845e0400207414000160710031401d051900804210301d0300c0e00c00040ba4004000c0354005015516403038140c0384a208101c02030f40242030284004c0c03200304294400b034611020340d02118143c2c11a0400c06503501d43c00d00004204041490229500809049107409c2c60140103402200e29a152540071440d030409000509004c0d85032041e060100c0341e11b105003500400c0c00e002418546d8101041200c445500c01c90340404c2101c034440704920005e003503003d00040c1c00910b805030310380f4036100002440d906187c02903100482101c0c0c401443c0e5402601200ca0011080d1 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 255123471 1250 255122221 255122227
    0x6050a0b030d120b031510060810030804051002011e150e04080d09021203180907172202120303011e240c2a060c02010c061d06040501020a0f0c0305 65
    0x5100f040600341c2d4001242c2c02d445640d0042a81c1d10140c410305105d4421687e6001c032182c42e2000051030350001405030800314807581010f00128404000302c8084e0394064819404209034031008078014100303180c07a00650303208070415a21041513504090207562140c180f0381146519140700c0c0d103e8000a0314010581c0508005200d1118803075008003203c01d0008001010b00d03504130007810304552010a102c040140205140c541c140741030800be0f50403907102c2c80c0c0013013410f1411070840348802020b0403820b2001c0207011030014108402289100c0594050a00d02d003c0011108560f901c0c0c0080c0a000c0c18011400b01c981c8032440b000442c030046441403d034070040d180d1403916000300203098640700c0c0b0801101c40142c201041102003220303030307408045000340d416110a0040811600389074001800300b100c8848140090307070b4001c000703801482d08035400060b1010302d07494950140c0c40708003442000e40241c004101c01d2110650191040e00c4450700e49000030070381e00c14110f801c04400704009001c01c0040c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 255124721 1250 255123471 255123497
    0x72d14090105041205010e0616021908070314040b04090f0605011b0b0a0f18020906060a0f3f050c030613090c1e09110c1c051606050a0b030d 62
    0x4c2d201c601e504c0c01900005061640c00901d103091681c2210442c2004680141c2c0500c1298100a10407440d4166108580c00e11712540e5400c181d03200c0d0030310150800030050415641c0281d22070441d4020300e41d28549994480d5550a10790141265070000c217a407914099001a40d94000d4840c00000d56449400218860050351007000b02200a04246c0005644821012610500d807054003c01d0b100070380c00040e010022f20410094076402841b00340903c401740602920f00d500884d13000080340c00c5051079080802014019040b1030850605103814115100c00e03031121003600408024180d1a481060145aa64440b01580b92005517565904401500b043e660500099440301800a22400d0800200d44d0b45440855090354000000050b2480c1040c080004144601c00d50034107100c103407000c2d81003d80103401203840e689043e8900c52520f07003c041d9003006500c01d1048602980c45010502c2040d02c01d4100640100030459850a0703c1d460007046410318030340012500c108a41c0b96840300340c14028 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 255125971 1250 255124721 255124739
    0x6020a061401270209090a05010302041a030c011409060f030108060a060e04111206010b0910020a020906010f171314030c060711030921160308040905072d1409010504 73
    0x840300c24a00780c44d424008401ca42d903030300348400d0241c0c42d10705010450b035055004000c11201011041e40d03c080c20480c400d4060707140401e104850640900341140711091900e0000a588105d00205074032440c00550710101c500100044c5050300c40500403145030303a48a04103002103d01c10700a21128a1041c00000c000401c0d4454982d400c13140070f0b01c000720f00c3c846200c921b480e00000707800c00615000046001c0216061100c1980e5410010380b000701a0118140c002c107540d03040c0a010a410440e40051070061903004d1121841050070190703c5043c2450b10307040f0100c066220f4902210206c0c1c43d0030100318503060000584917036221b0440035010035203030404140c40c40f812a03046a459400148400d2b40700756070b40207400900c2e10040d188105481c034000441401e11a0100f081a0310710101c880c00d001181c2c07210141c405440e41c08070001001d80314410180c500030840801515565264440c11074103800314030700541d00139800c4e1159154250042c41e401c03902e0280520050005030140010004c0c980 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 255127221 1250 255125971 255126029
    0x3071d012402031909080d080604110708090f0609090103030207060801170c0f0301060914060a090903050f07020d0c03050c03010c0504060e010507140a0803190204031e021906020a061401 82
    0x10a0504170354a1780d0360543c1904000ea1070100c5400b107000c040401581d41894060000850b0b50750255920745002c0790740f039020074041c44502501811088408034190784486040b510020070045c00301001e036a5030720300256540d00c580240340000c0c0b4203000010741da00d070b0a049040785543c2c041c060080c00002105100c0544540742c9041c0d810340d03c0d01070002d1541c156108a450b1034560381090403883c0303003140c14001d44200341d0303221003002032505480d103000c02d17030200070382d008681c0c00c80031283e685034140000780b0803910901001d01507210f815800010090001902248140281d00034004107800041c140c989001d184604000304100c050703001c0b003541c461030042030000c0c4940d50030145146809905032a00c400104111006140002404012180c0c0b42e030901aa64840109500d0035003980e0300c0341c0fa440d0580408802c07400c1d0b54640501107580303001918851034040003604d13460075501e54000707580e50301c480015511035107841ca40d100303481902100e0320306032000d19001520304200c0302001a600d00b = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 255128471 1250 255127221 255127267
    0x5090a030e1e010e0a03150b03010e0d0903150b06120403171b0a020709062913030f06020d090303150608010f03290103080702040b0d0f060b03071d01240203 69
    0x4490040100c0021401341d441102c14001f01ca00185001031881407508540443c4520320403544202603c1030f80e00d038000f40c2841a645c2c4400844131869a80b040036000c1c108030b1402591016010030380130300e0003c1d448403075440381e0300a5466041501456003102c600e0074040e40c25280c036920807441e45900100e4203004040c2c0004910484124946e207402c1c540488a994102a00e40c42c65003040d500d84c8030076600c000710500002c450441c41d10240242044890005100050260082c2d003081001c0c0909641a5986511642c00c00d000701034042c80d00030004d2408011144d2120f200321008510507101d09078890507641000100c220713076804c4d43c640c2500080000711a56070601c8140205c012114464600c6000310b101d00c1d0640d07110406881003100f90340040200c140203101c0d80500102142c20355503a0001c0c160440c0b00000d85450800109041c074a07507401c801c0465038403200c4142691703003a60366141200c586008100512400400f002610004002803400607401481229000e00c00d034031405402d4 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 255129721 1250 255128471 255128479
    0x7140c010305222d0f030e06030c1603030207060e010507110a03080f04050a0f03230a200709090b011403060403021209030c09010806190605030a031803020405090a030e1e010e 77
    0x11803403072110303109a016059021145c0805510903101015081176803c010940d04807041420b500e840c2c240e20f282d50007404a2540404582e0b14a0002d250080e4119514075801644c2800a240140010390203001c2c140c5114000a00f40d01d100ca240106c08919460301541c16540c0c5009a203641e000f48030340f000081c00a890b5070040900b0000010082c1c03007001c1c8140e10035200c8201e090940f407117640900003240500c0a00807807c000d1200e500da40a02c1c18034000d0100502c1e217801b50040b40685251034501c4d0441814240f400b41c03814140029004940d0403520742c6c224000010f103110041c142c60700c0082c0d6000740540c1c030488001c2c1c412180440941205038024040752030b091880000110755180070f81c0180307040e4012105000e440410340400790b0000c0e180352801c1c0000d81c541000300c2e540b5507074140003808012010a28066032a4000f238002c0007560002c105100310b04000c030010743c440390341410490204048030b030404007904040300e0450000001c51101070704031000000544819a034440250742c0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 255130971 1250 255129721 255129773
    0x105240304020a1205060103060c050a080c0307021e0102071e02030303070c060b090112050f011103180f0d02010606090618050607050c030604030e1509060414030307140c01030522 79
    0x8003c0c2c448002401340c0160b006000c02c2d491820440110303940002c108042142c10007a415030141c2010341c0c00e4100d564603058540d82c0c0c0d95910201c5c28400000500b1440528800c03601a41303c8054025000d01c50140140007910000506080d1013000c42c4200250540c0007400028142c1e4010000503c961f40102400b10380004000d0000358501400d802411020200c64581c1c811b10000300900e400d101d1262000300401104101703140c18900008044686c80001100c08401c844030130b104500e6080441d50407240004040603010340078101e54029600000c00704200050031501c210203a100d20701c662035440d5007850070f1a041c00056400003e0a503014417071060202410b890820040344224000e40d204042a161a42004103801107010790907120603060040000e2a907900d41120102d5141d04d11142100640d4000310b07095000b02c85020704442c0c4801146100c81901240000040b202640c0c1006980e6400174010031121304020700e40b03032803154502058005500303491030013074040c6109a0501 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 255132221 1250 255130971 255130979
    0x5240109090c0203070b011202090c0d020706090f170f03041209081605040b01020c031509070305030a0c03020606010807051902101d061303230904050c090102060105240304020a 78
    0xd40d00070b0800100142e10024080c4240664610744034003600c0d202902c00459000340c4c00040d4501d4001c3c2c2850075018000038900701e42102541242c0e10603900c20b0040c041d0740107034180458200f02c0c0300015034519080106a801c41442081140c40350440c2d540c1080c01d60b112501d485804003160a00c040a101c802480881e4107a410411840d1045030b412049140d2800c020622081c1e41441c0c24035030540d4090000b44900d0341d00814a801c040c03100c1100200b075684c3c1c91220a01e488203540c4040c010f80000070380500301691014039110501d001c0e8084409035100c41004440c4c200041300c2520010304140400e00030340c0c0c47c0003189440c0600d40d204490944102c01e00303100480c0d02c6001c0b50408550320300b0f401401c054050151030340c40f02d0340003070109001300e4032789000d0310201b00c03424408039084600c1d003074114002002c000d80ba17404170701400c01c200901d030049002202e944100140750240c42400b000040c1c524144400e001c001d0b40001060320065000030038036146030000740040780d005440100200b = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 255133471 1250 255132221 255132239
    0x109060516030c1d06070c05060408030310061b080706060b16021906140a0c080a080105241b070b071a0106080105030a17070501051f0905240109 64
    0x7405454041462000208403640180440d90312801440a010225290414110050564051401c0e003030380c43c196030703003194607024007040344d1904401c1c0d0200001c1000302c6d200100001451141118a034442c1c180f94442005039100d40c202503060041010340c815410003c3c15000140907a01e204140c007203501a22003040a8486e003003e500c0c401c101d50b00d0500c240c04c1d450002c0707202948100c8056682c8416080c02402413000750f0f40b04c80f1038102072000443d09035081c824400101e002e81c100040303584485086000801c49030080c0b0409110742490f15424001ea940d008251082a500150040ca44000348072881101200c0300c10b0019107019000001a4800b4410010000c0a2146033b890700b041a00203c520030700141a0841401c2000540050209460000d030300641c142c1c000010700a292007004402c017042c441c060f0014869400c1c01e060241a0354030308002c807000c4040701610901a5200c002d0be0046401c02c44001ca0766418481d03e031240030740848403000703146006240406145071140d4a01c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 255134721 1250 255133471 255133481
    0x40903030f0e031314060f09030f010c17060315040201030c0c05190b0907060c030e2b020a05030307110405130f050d080106031b08220602180105030103200102010906 73
    0x10044681001881c0312640b04d5059a02d405040c20f8128541c11160001c04202680151b410010502000080e0701031155230401c21240300c2a031f0040240080e1303030b0082004041601e0f402e040c800310300d2510003154031458040780c003940040c0107a466110b03035601d07900114040d010001c000418081450080c0c0b020a0040c071001c42000c90180c24100810198a482c100c40c0381c0c02000b114498001c12000c2c0040303944600c00c12036081c0c05203004200d07031266500082c103000241c0c2110071242071041404449444450045503d64001c440288140c1e680300e0505440c1d12034040d00a222826613003031403a49280961203150420030548030842e040c8015a551201c0d0301c8180c000761110b91281c03403410b544680c003010341d5025108503e0b060041e51001d040f14032048444004203001d100c0f20758006a91080305c42410080052030003543e060b4180345080410007544001100c10701c600c1208040c0020394041e0080320f04880d8801e151803030910b0382030403541602c420309055604554803070448801160080c014 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 255135971 1250 255134721 255134741
    0x40f1817041a07051005060105030a0c05041203020c09060301020301050a0e18030703050408070f060f08060121150905160507170a0801080c040e07051e18010e09030306030a02040903030f 82
    0x218960710512070400a24024410f201c0d01300c17890600d4208103542e680b100503641c2214143c0300101d0b154007183c8081c0c48900958010034400b4912122002c1810782c00201000c0c4c5102c15243c24802c1c2d16100b040c1400d030b2100340070340b60b001400d261040009007241800c3c00e07841002e01450b840011062221281035503c011000e07000079101107424000d030310003400040000c01e411044c5484007441c10402415034024003d154007800080c40024410740d00a182002250101d03030b0318100d00c440c0c1c029103c0c2c02405004c001e20450362000b180071602150500c9140d0240b02445440c8a5a2030038080441d01503008010465010600b0b65508290f072009001500d80003006440349071072581000261450283c1c2c2105080c840c504080c1d02410016021803402c0c00c0d0b94050310002004011306040444d990300f0b0801070b640100103103440308680202241c505050b11080b0346d5003403075500c43c0b60180e59280010b03106d02c0c2d81604128038103070040c5404c1d0700282106100f41030100d0044103005103101110342e10b0071 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 255137221 1250 255135971 255136019
    0x120a051201030f021516021002010b0a06080a060602030301080705060c1608010c140715050c040302090a1505240d090209090a0203010b040e06060f121209040f181704 73
    0x4041c0d011480e110a010035440f0030014490b0401000c00b040b646c0324090709a029001d1101c0d9a104504240301790070800958102a012a007034a42c0d8040003408c43c0300445000920780e1400e60041400c52000c005c4038100e9640704000c1c0340700c5040400300011544101e04407681c5100d511121141025a80000401014024000600030030f6040c0050030041c41c1504508141d40100102800240300300040d80d05000c0c140c40004050740e6015180c0014801c98001942c0028a841000261805a0081c03103c0540551941c0011507403002840b0381c200c80003641c0711006c4c0096004010881a0384082d2245500380350010900144a401081c1070340c505582c4041d490300036490131815800c0034003d00700168401c3d01c3c1080309000c880750158803642c02511461007000819052005592403038407403100f0458007020f4802103070804a5926041e03001d00940c4c2e00403411f15140d03040d001000e04c1500050b81c00d10071500803034135040c0c1c0c40300d2a40c1c00702d12007440e81c000b00380b10110341f050030940031480c070894542c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 255138471 1250 255137221 255137243
    0x90d051005060609011b02060d0e2b080c1309090f060c0801080c042c070e09031306030e070f090204030314040f060f0201093306050102120a05120103 66
    0x64119415038800a169a001c0e443c1049440300a0340e0001280000407160b4003c0c3c55030340d005100160203032091440701c11201d4140781c112100c84e5408280c0d6000490103224007581c15051410070007c1c1c0790719407441004988804000b80016108030700402e581440549180380503512000c220b8100d805d0802c0581c1d503030441e000380e0800c01c00302e072090184402c01350030410705070b40c50100b9099072504081c646900841e2640890300302c100d0844101b4400300b04505040380240e01c400302c1d05648002a100300400341500c0f802082034010084103c0d00d25401c0344001c1e82c07150341003c000360041c1070b484032401814450060001a2030b1050503003640609000000540e445203103013802045400007a13210703000d02608120401c08029480700c1e01c011103900b03082c41c6006101c0441c00340d0041c4060b0101a1252601c0e03004466420701300b0340c0300c10308030410601003c100e2041005000c100c402d14000c20b4050303406200b0040c0e00c144d000b07014088079550351801c0c500e840e034410030110807400f00f82e004645191541e = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 255139721 1250 255138471 255138493
    0x150e100501060e2d0d08040b07150b060301090c0e031204230f15120c0406031d070e0c0f0d050115021207110a0306050f040201020d0c0c090c020102090d05 68
    0x11001c0804034481c1220114640442150307160b880000000c500d010020010130202003a032540640c80b540305402018039500e49031303181000320440c0d03c094001c80e0511014101841031250f188a070000781d00c0017610b1346055a090546010007007441c0b0040e203044c004500044901c40e41c1c20031460481080140b4142d46030340ca094280c240983d02102d0409002d01e01c55500c5c10240c882111000000c1021140315021119410b05040c20f0312403006100a8034440008004401440000410840d03485990800c40c0c0c1030504041c070142144145982e84d00e811415042046006220007690000300c0c0700c401c1407030711010358071103101c47e4861420154410b40b1980100000a0413050700d4045101c03a001030710f0002809640745150b403142d2400100b00105401c4500c5844c5c07900105407000c0c55100c40108824200140b098440585c1200c0490061250381170203404248520415001194400340c004015410310300c40e48040c2900d10301140844d9030038400560300e075443c2145410b04034042e07000b8203039031140 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 255140971 1250 255139721 255139727
    0x402101209051b0d051f0e1504051002040302030309010e010201020f1b070b040b1204170309010f060f060507020f0d0506130501060b040b03010b0706110301060e040e0c01020604150e10050106 84
    0x103a083c0d00d0301c142c1e0040000d0011030404107101c5140344412800305404103000d4030380001440710780b10104981c4500d90758466400320b407001c5107000c2c03402102100da072004100e2000060740f2942c00029050781051180011035401615031410314201400054108030b0403000003c42c58222103c1c00035541c1c0104c0803000d602d403042c021180500301300d0b9405032038582400555a041d1140200c0c2c0000003685000180601003145603190702c100c203048400b5502d00b858a043e6018201080301c0104203881c056001a640c50b0751082035003103651a0b1a628280201c035001c2100c804803160382150030900c10030354000003c00612005110b981c045086240c9503d079401d02500b11030140d0402040814108418850110202c040d0b034111000001105d03590002403030072402410a00b154400300990100010070101d402003440119007000740da080000078000103c8540d6920300032707001030240e0050320100d0042481070100f038a40d0a591800801c040090144551410840942c0342095554940060040070b034 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 255142221 1250 255140971 255141013
    0x6031f08010507170c0c0a0309080d02160909170d060618031a040303020c150601020d02070e0705090a0314061510170a141003020f0117040210120905 66
    0x403400c002005a0b20f84842d02905510040000004081c4140002100c8040c2c80003103e6440c003182041d42c10703080c041d1402806154143c0500e40c900e000e00620603410610004548030003100d03001e0040500c0b07180c00d100da0b004214400c41030324800701ca05110100280c030503000300300c1c903000f142c8000790032440c0443c002e0041900e0b0740c0301258601c4005003000800e80114241610f8041c0301041030351038680d0324042d4000d2191080000880c011140040b00115000003500d100711000e03025105c90300e0308084100d84900c0c00f8003420b02d007108404041401d030380c442c00107450300703040241085a000c0d40b03c1c2c4a01c0c13180c82c281d00705c0c40940ea01c510208402c0801175020100d8106064030b0f035602c090b8040502030054558403c103800b1345480c1c40002450401d254000e80320740260800012568240f19030b60a140501071b01080c0d00406007410071a6855128484e14100c40d410030b03900320f0103500c0713503070800c00ea00321415840400c0061210320040d0460b064450580050f1083d0010306812545181021841d1 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 255143471 1250 255142221 255142229
    0xf090f150207240f0e04090b010e06181f0503100903140901020319030b1005091207050d0609060605130905120f0a030203041a1906120c0b0a030b06031f 67
    0x800c0d0007480b0101d04285504a0716a03006030130038040f04600c90604840c1d4840d40d001451717009040c02980c40510944e5410241030b1606850a59410f564000c00d2150020705207a24a000030042c0340001c8141d500b8032440d01000725140419000c241d5180c00080c0b2384540c00e08069100303940c0707140540030190403c0c0000503050704030b00c0782418101001c001039240c1c0030f840443c8040204000500c180640720358803007000f204004100e1106118422030062843d042148100d00400c0344c4418590022400105041281c03001407211444100c607640300c1001d094400030403038612b51687c102181c26030b60070b0244400ca60f41c80e4000600c901c080d0403c41e160420f58203010031100020840003410000c6007040f034040c0d44442c10b0241c0d9a0b1518074001d28130f0314501c07081c0030041c4448000d00004590840c9203111800c0b20400601c40b0030740b1009400844c803021800202400c1240c6803c000000c003440280003504031038280002c078450000080b9200e0742c421150009842d111141315501c0c440440c80e407801030 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 255144721 1250 255143471 255143489
    0x2040e1e07151706061c0e071d040f0f06020d14160801050303041e050402030a0209090a0e1509011805031e0310140607060f06050a150f0f090f150207 66
    0x200b08843d00541c0c407000341056004030b000040b072a18046c0403800d003c0b100780801070100b001c980c0490019403540c00c01c0c010501d1901c480750808000341c0b081300c000d40c00f903904424800c2030a40c103907907500c000f41500ba0301107983c41c2e004c3c03001284000492103850983d4600042401c3c103072500d14141c04c14503443e020308000740524030005001300c2e103001066500303954481130115a40b0310b4480c0e4001c8408003503449958010300001c00c00c240000d59030098030340d0030b0003610303414a59151000104280d0304500280b0a545d40088940c0c21104034200596400c100100b00001750021070045038003111034400d005850f00d50001480628000703111a003041c1082080c0d000c9411400c0c004c04242840d021442500541c0ca040c0d140070400c1d940359030031900b01e6548044200040d8110900c150090719082c40b03000d2041c2c00e007510004001d0510345540d0700c4032900340c0e140e103207100c041c1c1f0b015541403250f0140c1ea010409a00380c0481c4040880c124000504164010300207042e610b03100c02803400149402c80c080c0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 255145971 1250 255144721 255144737
    0xa030b0906041b030b010c06050c2a0d03050a180507060206090c0f040c05210105180103080a030f061a070605100f17030702300105070203040302040e1e0715 69
    0x301410410389151030700f416190102c0c203a001c0d0f40040710318426210020b42024609014400d5244901d0000c180307240007101c0030340ca14456824050015000b103894450356801c441c4d80e04110a00c40e502c01a03001070074650024450f0308030390303200101c460300030412101c2e42c1c4284424011180c040081d140e2124034040101700f079404040201d1031201d4480511409140c03165049400c282c05402030701c004482f02c00311010340d1858501e0b9a01c02207002e03c941800384803a09288407400c59a0781089042e030750046440303442c00c041031200f10b000785032124002d408555507540c041401d03104034100e4207803880b203601502e841d111103043c00012550080c0111085507004078003000000040b00700e000450300304140c0108900907403d1301500798403910000940c40448541940d04041d0140590081c44400020100c120094000e0f400c0c02c0310000d585000159000344000c20040c41d054222802e025500300699080c181d245003180c0d1103203000d10721503000750044041407245880300d04402d1240100c034608088 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 255147221 1250 255145971 255145991
    0x210e0414160c051015090b0306040b0609040f050303010b09041d07150306090501090c030c02070506031302040207060908072006030f06011b0c060e0103060b030c03090f030a030b090604 81
    0x41041015840c1d0010701403000046400c0c02010300c20b5a102141d080f405000c1d0b40c001070105200041180500d5184500d032220350601030800117001417246500c06801300380b07502e0715030801400710030050044454250300030728840081d0041c00034600a00800b80120b41307401c0c203881080b00740e60b9020410851440031b0126522480c0c00018545c04440c1e1001c2d0000c62020324800880c00361106421411440342000d0001070b110307905602003601c0e08000d41c4c0411010f020340c04202e0301d0710f8a0348a801d0740b01209101254032084a4403000c440507100400c01803504640355240001d03a4000e045c25240140301003008820300141850f511414032348401120900c007101400141c0f540800351400e1030400d09600022018ad02074008080e0005150180d451800c01a1034003211001c80b03801201d001071007428280981d94024000d4000740c0d0366468660b400c0d9501ea0b616212185c1000b421003110f07210f8a42001d410040602c02070221403010740d000f00b20948141e060082c003d5010341524042c034070313280003c0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 255148471 1250 255147221 255147241
    0x1207060807170609070809031303050a140319180810020304020a0501080c03130204241e03080f0705010204050d0b07020607050304030f0818150a0608010b010206040609210e0414 78
    0x81c5d101c45241050302c0540c944940461560041d00c1c414440c2e03900024020041c03240c00903038030103914812640b4944902d092a5525201d004001100c51000300d284600704000e07000c1c28803041460000d60141441503540d001c518940100d050300420030300d40c000140310a41c04c1005c5240003500302800c24036002d04100e05086000d01c00201418510074038400707500704565a540104da50b076803805908030101003501368801c2c80c03019035205420000240030b20a640891680d01d856045076000007146e824001a480c41c06103980c030444e0100d0b89554200008030f820790703c0000400e4118021034427801c40303140038140030b8500b990107461141405014810080002c1d40a0700705400900c441c5001c1210f900c131044e00100300c20310f08002c0d201d030780a581c4601c07003501d5a01c44058410504c5080603c0000d075140d503010f082fa03400201060041c3c01042c0000c022813420781014400611032002c0c2d0442e00f10071500e010f40413641000c000c0000d240e1010310a20703480c00303010f072071041454100e0295071420704200300 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 255149721 1250 255148471 255148489
    0x30f121b01020306060a0c06180b07030c021b01050315190e010e011206200a03020a090e04030f081f060c050115181d01020c0601030b0705031b0912070608071706 71
    0xe90204447d4032481e01c100621500540c010f651000d01c0105020424505040300b80c008541d07030f200081c070341116010500c0c800244d03280c00d288030555098a50009000440345503000400c0f410507000603154030126030b02c4104802c0c44034822010950141410810703425180036040e80428102d2613540014007107040c0e42c64403c100158001c000040004e2880702c25031070844990a840003d103000f1944822158064008211950165641ba144c1686440c1040000c3c0e405580280000d44101400c101e6580036429850f04a048026080ca50060398943d0b001c4031100c64000f03038002a542d071281b5041150900403a000040411418144142401a030514189491070050805c0d92203560300c80c000040c50b0040c2900000d0000207660303c2c05e9080609503144030038402214000c222000150880d88140181c9001e036604a01d480244403a0740070104840d001307181102d038402c041014420001c1002c02c891001000142c49509485c0b4115502030909004480d4a2916282000401c0035682e644805 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 255150971 1250 255149721 255149737
    0x20303010902180a06231206010302070309030804030f030e0d1106030a14010902130e1302100905031e100608210702060d0204150905100c02030f121b0102030606 71
    0x586995100f8402d000c07081d90074031940c1d000822080007241c6944e0000d040406800e500c840d00e41d01d07207426800755030303644100340781e030006184500301055140d84070307030001d00d4114060710345040300c99101e80b034102959005500885498070089800d008064102c00084035403070046070b940c9003040035038031815624409102620b21900c800400141d05041c00d40c0800c0c4000d03d084409841d6685410904001f588901d151648403070f5225000524540f011151234440c134070448413001740e084c880d400d101a8244407113011050010504d404612910204111801c0820011402c0e0005d4400e441c010300b00f6100c040344100301d60508406018802000540300f4071840311090350086218007105400303c600032044025444080000d070101c1c0e51286401400c05d4685c0c0c0f0f9400b00c4c441c0c100c3c01d0281c40308241e030f01c9200d4015045801c035000c09805100d5203401c183c009001d484104404180c180d05000e03019103080c100d403002241c210401511101e82e520baa0100d00001c40c518200400020035038010004 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 255152221 1250 255150971 255150989
    0x5100206280f020408060609010506120402061603020d0305151806040e03130819020a090509151f0b03010e010b0705030c01050a0f14011a0d18230c0102030301 70
    0xa4224148908910440c840d4003408100c54032030080b00d180654420702c00d40080d481060041401403030071210140c101c9200400039458091300f031780c040b004004000c00580c1c3c031140a00c008144040b1320221400940e11a0703010b09008110ba000c003a04861024041c4900003003031480340c9015803158440c04080d11140d0740f540042e0f1351000c3c00a00608040c08008906020128540400c03290021900302503c5205058507018155440d030381524120b024000380d48080c488404214450041d8001368010313000c1c6041d550886100e103c124040201510355008000ba43c0c440200400e12503c03840b40034082400e440b52031949440761f00001c0e0f4406008000b1428400a810700c200401001114100003407100240121700e0102840310040c0500004142c41c50306000041724000300c0d0021050503507424034440740d120f138071002c0c0e04245600070400c00c0170b005030742d211907001c042440b002c007102051041c00403107501072500a074446004c200301d040030410750000242440700e81c0c0103c15281500d411ba0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 255153471 1250 255152221 255152251
    0x9081626060601201915200702010203070f050d030605011409090c0d0f0614030c0a060e04020c06040f0203010b0d0b0606072d050c0a050108010b070c0312051305100206 74
    0x882038002c0e00401392001014424965003c610301c1034045d1507000280904103c0100000c08003c1d00b00350781c0c0d09143d1014120b0300c07624001d6600c450070060541580188116414a80d45641d200c1e003845850742d080d100750340100c4800d0300642e418022040a84003c1c038200756210050b1800c460b060180750002881181c50b0800a448414648e069440c1c1e8101c2c80400c2c071071b03401c120000f0303001032189002d00c103000b020384410ba800034200000c903c150454042c1142025038600341d01190025020403150358096020809240180000c00c062400f0314000d80500c0002c4242e84109404c480a04003240d024003100c0241d000815034440c0b0340c0d0f50014055460380d584079450303d0140c5001503000300c0348002c03030218a03920418070700425040a455114008581807035a1001c2044a01080c601c45c0c1800660400f00501142e040032001d40407e6200c0c12403910510740300d81e20b030114002c91f00d042d000000e0300481c445901085514040300103140546120541d600d03000e400a4580000420090100f8412 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 255154721 1250 255153471 255153497
    0x908010e03270d0821010f0503100c120608010b13060509070507031e0c12050c190c03050105040f0b010b070b1330090b0307020d0f09081626060601 65
    0x5103080710203d0742d00198099035811017242a115451000384545052a440c0c000458200b420545c440c080d40d40003402080064a03101072580985034100d509010010b1031000b0b0440d0510030f010307039409401c6000c008102408c14509010602ca038a80c206aa41824030354208096120b00d42925002030b62843c2903980d0b00742e907060541e03011541c991912038800040340e11040340c9a1081641d800d80d0f1003001c18894034514044215a20300400e2602070040d0403041d007800f61030070608180b81c0f401d4031500000b00c49950301d880d09800c56000711820385001098510030820001d617181e940e401742c4400c1640707a0074a142138a55045442c0010006a080c50b10320b0304030010b00260902446140d21300c0003c9021190741562a004040d94030a030071808509030b0071000c42c1d109544011f03240b083c0c2042e40184103621044070115902c00710803007860b0522000a5012070000c074148010100030384201d190f0b0b01132a141100f2003490070444030041320707040120042c280001c5004904d1640122003441c04c48125400 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 255155971 1250 255154721 255154729
    0x40305070f0b01060e1008132414100303020d030506060d1b140405092205010606030501031419060b13060909050d08090d0507170a0908010e0327 64
    0x3a604001c1c00345103615040100b045884401c0606070fa0319503980c0c41c20742c103040d420302c441c032444071140201150344040044c0d10065040502e0f98000e00546040d001282e038540d003031050319030301c0425420951701c41a10740a0403902599442d0000031a010f515010341c51038074001d40ba50318144403441015103540c041021956040d080d03c41856121004011080900c07100b6201407511030441d40110350011217200710746440c0402e8604442001c1c060f00d0881e074030070891100185500300d512044144017614900402d1007446110082c02c01618001003550650070005400341c040340e114506035000b10914924103c03c160306c0821254440d00200d00304031404005210710314143c070040205480c0c80400600212540c2201c042c15008a0a551070038000a030211000e81781118104071641c0000b5203c001540302c0c0009111140c01805220103150200024120031b83c0045d000364005280c822040c000b1420078032408190300c43c020019031610b0110b4800440b007848000c0015001401040a0f4070700e030329 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 255157221 1250 255155971 255155977
    0x2072c071412090d1103040b070503070503040320270a060512060615090102071203020321180303100501030209060904050f09010c050319020318031303170918040305 73
    0x8101c00d80c0c4450041d0481c03210303030500b2500003905100311600211458000d4211071020034050001d03500e028140b01d003a4846d9803200004070b416201c20440039001c10404d0020300091031140304420212884448480100c580241c04030780320b00c00e80034081a03500110401056010114102032610742d0715051880010034140c2d020680200701c4628100380100085010381c8965421942048800e20440c100c0030700e80680354040e805a0f1140c20700303010807c0b80780d40d1409d07224886e104172441c162170841c1ca00c0c1740c000130200b0044103a601009102c1040d2445a44a81c1d004107803005500f0741c40e0921030303002d07200040e12034035040c03650001d154415a00d41e0800c6900505002e041481142890414420000c00441d990100e03940780c043c061341402d200e102103d00682003e001a50806860f0108000a600181140521526200c0c0b80555508140040e240c0c60b0401e02242d071441d0f1640c180003054000001030021400c4080100b01d8007982c0f103c8800d07041c003020070300003482075450345020744040c4 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 255158471 1250 255157221 255157247
    0x4020901052703010614030709060509041b0902040b030403021b0f060f07060501080d11010504122a030e0f040905031204030216260102180f03011112010602072c07 72
    0x1500f0b003440031544550701e440228100c0d0b003c1d0100c0b00c900e99660400b01c1220210b0040bc0c0d80f00500b0804113020401400a0036401040014060000d5655500000c1281c2c001d0b407000a151901208001c00d141d018049860480e06d0755403900b05c1040d03440c0002d407007450500d124910031500130401001a189500550341030581c407807020080c5585036240b42c6d684500340c0d504070b80054044c044000000806000f1503002e81c0e40441e0164020090940c02d540c4250103a00d03c40003030440c0302514101911081e0400c98150281e1155110040240144611041e6030100d80d07028a0910190400068001044400070103501c05800611703126890124204914100c1c00c0031a110114008600c00802e0b00340015802c240740d220401441c00d80d41641c1c00e0f8058502d2001021a1250b504007841c20850700c0680402c5004000003084521011240c8840d0040c20591650a150b2401444a190104500d50140031142420000c0c45c0c2091104007200b09009545502c0c0100103020a003c103000b420b2203c41e0b1 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 255159721 1250 255158471 255158473
    0x10f051c0206160206070b01240e040504020409120306050901080d0203030c030c040e09060a050f060f2209030305090111190e1503041a07090b04050f0a0308120f0604020901052703 79
    0x10b1b5074207007040100403601380a240300e4010841156008400290030355085100a615410b500d000e00c03400700700040070001d1050fa0000d840b9081035001030030000c0040b000034095100010f465003001d040c4040440c0c141c10669159100c3c41d0f10100c00d1750000182d90b0300c49035400c101c0f41e4903600c5403690021801990303c00b820081070071040c80750480000c11030901c03039620280100019540c0304e800b4140c84c041034400b80e0b0400c00c424200d4985082025009251000200e405c0b038181c159410944100c4102c05000d0b8000707603450040c001c69039001e020340c104800400d0001410050000c4d00010900404030881c000d00c00d40007031088003074035041c00540700d49801200d2251a807406051900d030b140760700402518800c0ca5840019002d41c0955044000d440c070004d000740c201030812051105e48080b11010f01d1b40700050140002c00030725114002c00f0044a541c10320b840354145820100b1540c1406080c0e58451070041c4101140c0e032f64480203036920866003a40000e50204020404010880000e00d81605 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 255160971 1250 255159721 255159727
    0xf0c0f060914030c010b03060112020f150d06060e030307020a18090203010204090903020d020607050d0e071707030302070b0a080a0504060e060f010f0b03040c060302030919030206010f051c0206160206 88
    0x985008000340500c44e10100003404805401d404160300d5080c00d01400b04070441c202420805820103007466040e07030001906c410300c269202d1081350305039080302c1c0913149800c2e00c3d080240409940580303a50101c010580007107051806aa00080904103180550104410310301032810005d401070308901c01450b0042c0c005c5646607100c5a0001c0a002c5500d015005880703003109800f1803d10000c0c0c80c912070510b903555242800300300300d0114058000e0120710b904078072511030040b4a0301d007082031240c00d5031541030081001500d5450007a040c2822a07004040e0075000340452a449034014101a41c46803c14100142e160740300d00e0207070000c0010807113600040c0729900420000d0303e096038103981601c00d814001c1c2816079450388501c50b98401150001e00402003281c0400a25000390007440e003020b004800e549840c4000c502001090b0b501c2e500550041e844880100b01031002902002d001c0c0405440030210a84120740070700c840d4422102c001e008038030001d12051103040c410f9814082d280d00402150f6 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 255162221 1250 255160971 255161003
    0x1809020703020102120c12010e0907050a0b0406081b03130618150e0118060218060f0a030605010908030a0c03021006080c040f0902010c0f0c05061c06060f0c0f0609 72
    0xf00079007120400018541c2c600021401460002c1c0c20703100c1c1645403041d8200301d6824081040304400c00548040454451048049445d90360010100d01a202002140d5251031405000908000001e040c1d00a00381e60403880000c419103030403c07203600580c0e5440c0d44001f4841460000000c00c0c1c0101c07801c6522110764401e008000421030380d400c0395058020180611144150401c0c203c3d05030f00d81c01d83c2101c06101c0510009981a0050005030000070070040940140e80c0c00308515600112704100b5140c0e00080c103100e02c030340620806000d48000e1030701c205000d0803e00c2c40381d03403441928106424000c2015288003014800c2003c01100454010103214160343c6205982c7c0d83c400d000380d401e10960914046c0095a10380340302e000007994050b503c0e106981c495841d04821060b40000c150303003d8441e40c1000c98180c50b081c0080a800440312080540d120308a00820101c1303005c2d82019040003181c55450300c1d5241d221040c500041d400c031696039038007040e030302d0017100909030014010b02c200c001e07080d011 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 255163471 1250 255162221 255162223
    0x70c0f09020703020c0906030d0305130b040b2d1f0801110a0905060a080c0304030504081615080405030a1b1505010806071e052214010e1f180902070302 67
    0xb6494800e8007282d81c541000410025480d00444416400d45d1000d14004100c6200e0b4000039001700e01d00300030304800c0d10103444450b80203404071019581880200c1c14824015030100c4801008903059400c01d40c94904210480304215001d040c840c04071815807030000f00e00b0002c41150009021800081241078022220003040e90401d00308000400c403692000031b250304083c000c603400d0700d0823561964002da40d403150713407607140e0005441901080401d10001c98443c01c2005868407081c26001c201165074541100361740c080b0030001103c41008125001d020001e4400030960f00056103604209480384070761000400c180107a07260240407812059049040c0c90156407045040c8c91440d400d440c0940d0301d00d07038292407150030003c080e4242c8100718041c9210714030503406424104401d070403102001191340b106503101c8490b81c0068502d00000c5440304695a005503890140010585001e9408202d41c0350500e00000c00307501e0071060000c103190402001444c540b81401038481e0210441d150725030f508000f = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 255164721 1250 255163471 255163477
    0x102010b0307030c15050c070317070501150906050f09040b06010311071214030c040306090f14010b030606190306091403070302060901180809040c05040b040306020d0b040203070f05070c0f0902 85
    0x2442c003100c0c90b05c149103d54070400c00c60b07018a03080001082118074540e51107641200f505407042c0c090500f4001403002450a0040c01c0c091900700c09400d11040c01c3c40800d40c2160303040e41c080c2c1d01c00d01651130383c601d031602d803001d80e158016000805000d81d5a078000050340505461111361988410004000d0300b000141500500740c2c110b169519031111140701e03051045440142c130028200803007030000700300140440e040041c120784120b540c4d03585000655181d202c0502804601440c6945070071032142c840c10b080050582c031410462388004180c46140e0303c0d101002c9035020252031551a44042428031000c2070400c1440d18100c005c880c0d5507459420001d40358130050740c00060395400c00c1681c2d0040b45089001050807500700032003610b4480d034103081000501040035228180134043c040040c510040d0310181c03000b907008200c0076aa03002955680d504a0f4401c00070b071442144140248041c182d40300d01c58903059401c0781005d540e18a41400d18000c04191580000f90f013910707201001c224048540c000d = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 255165971 1250 255164721 255164729
    0x4090c090c181d0603010608012d1103040b040302011409030d151206020f0c03121e041703102402240f040305131203021006141507020607051612200102010b0307030c 73
    0x52092b595110350780060660710501e4100603526001d001040c003080a41d41e140d40c12521900001500020342000400b407507104440060721034201145a04292403240110801f29211074407907040a824485114003400b034000c0041c190325804100f200c00510002c003198501c1480000312074541400e04125014a07000701c1d03078120102e51010304040142d0090743d0890065510511903d0406544441401507030070003046202c150307540900000d0039080b140c8031004211414461141812640d45004e0310b0048203110400704804100c0b00e1409940c0d1101d80f82da000711b107020600c0c0041c2c5a50030200e07001d00903000070398042503100d400003520216000100722041d200303400b0341c0d801d544000c8446040f02c2c2c00c0c1c0f14082021800480211031031038100350000703c000c2e09518950510816802207200b5800c410f504a4160780407450f90310306072041c108110000d0000c00c1c3c18000c0c0c034082d5034801e415602c1300201424061545101006903030b0003034011740c15524005d402ca80e2400e0766420164440d05103486 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 255167221 1250 255165971 255166031
    0x501030c0b0405132c070f0605031003081c021204150b0d020f0102100e011406060403030f051c0f0b010806040b1e04090c090c181d060301060801 64
    0xc00200601044103079812030304000c0c20802d4848104448801a00c5800d40544141482c1034074440c4a1075101c2c0c41030780703070428071006140040c1413030400804040141c0100040c4601401004104440045020f0650303078081c18480e20b811680030115100b8100120382c0c450030340007042140d685035014201c41d102d58002c0e566000f01041d4241100c04407880000590303000381c0038612030701c05428131f0008003401a030184111444d04003000d403c0d0b4100d0784100301c5140a41d4407084105040080a03a2540c3c001d4011982949010315540d0083c2c80882c4c410810000d00c240030445000510704180907254424140c2000d000d600c14558809004003040c0c0e51450100e5903640100f503c0381014403445a9050002d402862458007132890403401d80403c0300c0e1130b9446038480d00070b070b400100c000d5803880c001c0844c000040b40c00303d240b66016007034003120011081810b0009a04100d0301031408d41d00c024080f0180c00d0000c44e5100c49001c00d01501580d0000c05c000d40c01c00001c03800c0210009080882c07250405 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 255168471 1250 255167221 255167243
    0x9090a03090609060503040f14031204120806090a0c020c040f0903080f0c0a0c0f0f0b10060201050f19060906060504060908031204030f030b0a0f050909060c040b2209050103 76
    0x155040d655403e10b800f034a4001442032001400141a240800072101d008403461a10502e0b000c20361481c560000c092040c50501c4401403008000300041e0b020701c0c29117281402e013802d2500700c1c0880d9000000410006a1070307200c02c0071202d028000e2010b1070030028042c101740640d080c3d00204c0c8000c2c2200300d0f400c0307000404040c001628280000c2d00280070304801d912103840c104508408844c581100301c42510a46031550801c00011540e06000340d0580c450001c448061801e042d18030040141035110b042964103110421250381e49003180b80c0d41c080d90707a0b01001c078890300c103a14540040900784c0003078001e140b4001d401308080d600f100c00340c41241c0c400c3e514800840d8940c0e41076a104d014402d1440080b01f005ca0100740020700608046007690068074000887c80358410000382100890750029801e020304840500090810311030095000480200401190400982420707540c42a071298020b6120042030180d80b401b5800c08024010b1444810184465101c01c50280100f000784811100d00c0186 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 255169721 1250 255168471 255168479
    0x20a03030314070e150c2401030201120b0a060813020306071d040e0c1005070b0114040e19080d060e0c09040b101211040302060a020f0c150d1a09090a0309 68
    0x2500f0004000d1070702500c42c05c80d00717100c000c042c2e07201e0300300c000b04821500856070074545c010322403540c10b429020688180e844c9549140005030120102c0e40042580500f003003403003e069110000408102c901c1890324004c181e407104050b0390900c0c1040300003076040c0036040501410703551040c1e081440bc1e03000c180300710021605d0b404000c1198281e0b00d40300b0071604030308000005844c0030008404510381505007070b45000707429940c1d804400310036000f07807944ea2180d0300c50340d00900f480c1c800d00d1030f44503245006003407050403004419640c04071000002c1c1a10070004d41c0f240803555540059009240706a1400c0060a113285000c1064004500a50160f0314001000b4650310f03040c5c0101c141d4543c01c0d19550303e2419001020310203030041c108003982c1100704110002c01a00c1c0d1100610020440b540500800781800070784031300300b521a0500078891481c820301740d00c0c941d03512801c17502c040b810700d200041d85e103582c07202d0083c542e003402940c154402018000c021001001080c0415454400e41c1d80801007521 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 255170971 1250 255169721 255169727
    0x1150e0d11010306080a03020703080904020c240a11180312070609020f0307030c0e22050105100522020d0f1b020607031b0315032910030f0b0a09020a0303031407 71
    0x10381d06c4003900581c00000e0420124110740d000313008486000d0400761030000f180c00b0541c44c008801a2560541030500c03080c2d0300070480001c442d40c0181e0340708014000e00d003021003802005d010301c8060341c4090703c40d10746109036698100524600c69078850000d0751250400d0900500510081509a005102c0c400c95000305140120b81c0e0003d80e540031199a40007400c060303c003464040c00902d0040300106000c1d61400800100e03030203040141c07044001068a1909041105801125034865070003503081035a480d50583d0f40c0c10383c901c440003030f02000685500e00785800c10064440b10040001151401e80c06d08100c00050b03102a200d20b03455000c490290304c40980450444800e4a4004c607020903d074070014240f80b0a81003030340d0308130071041d03140940c5840e600e0b55106e03424154100101841d0703621002100084124009520600c01811061003d1940c4c03a40240003d01000040c035880b08400018203926061344030b14100c54002c1c3c10542c943d6220b2401400400d035251081182030808400600c0c4588 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 255172221 1250 255170971 255170983
    0x91c020a0923090303011e0909140d0c0201050d0c050708070f12110c0d0201120608100f090f0f021507030f03050f101715040602070b09031201150e0d1101030608 71
    0x50100025845c582c41d00300e16105500102d022900818040c43c0005110160f070f0062440090103100030916194a4403200307464010b141c0030300d40601028180480150f0380103410f90f85900d60100d004242e290001c082111540b1a5a00041c03820f0b5021170a0b00030b200240c810201400c0c401d008001c0045a000420784143c00f0180c0c220072140e00c00202d258003070600380c007640015403041c1014501244d01c02c0112066aa103034210141a0303100c0c40c0d0300c510a03c0c00d40150549851500300c03c019041107070300c0780e888403100544003601049161140310300315140d0303110680003601c10084e155100c444901e401001c0c00700b040074490000c2d0404020603400e01c00211502d0003912118100e080c42c624105500035640130800407800c05000b40c6010b0404045581c1a451141c2c1c807034100181e0320191450181200313800a45020080d500500c595084a1814a0b07081d0560f0042640800201744000c1e0440380c0f50300c0c10449582010304004503c0401c001028002607248003601c00384080c1c1e40320324044c1e039500 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 255173471 1250 255172221 255172231
    0x18050702150f06040b0d02090717070c051203060118081b1f0e030f1b19050303041a0f21310203070302031212010501020c0105091c020a0923 62
    0xb0344288049201403405030f00170505070b40007610314440070b8400e80002c0c9001804991001c08100b11080c0513030310103a1000240e900800a0038040d4940c280b036152a541e5016020480019050000101d05503038090030721940341c0e0030f0811540042c2922505c1d840e88a14a5080c550503551545060b60744d6441e182d0301100f00c0030203500100300c0c507401e180c0c401c030703041a01c40c03601c3c40e0180640002044103000c02d0112000c84c1800a4070003000b0401007040c00010b2a0602da5500c104403100d00c188116a80401143e00302c0d611001824100a010080e40945200c2c08098007840c481c0090b2801803140601c1111301206009564000c803503a4600317650030240a100131010301c47c003019004400f602d000c2180b000c0340a001a00300c859203a10b95001c82d29004c07a05110710300810000c52541600c01845161303601401083c4090201c41103c0000a0014000c442010b407041145010110003450305501030003082c3d40050030020b00c1c0750345e081c0140c020800001608a00d8010407440343c0c83c0e12018800d68081c1c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 255174721 1250 255173471 255173491
    0xc0f06020c2d0307080a02031e0c060a0201063b151201020d06030302011b0f17090c1f02070b0f18130c17070c0b1f1805070215 56
    0xc4105480500c0c2d1252070300c103404484100c444500740346502d0400c0048003a112001c01014004550b0040620b480c6496100d41402040011502807c0d0310200f1041c8081d00c2c00e0f079445464030014441070b805480340c0e400c02c840940c0b004a400c0f40d5080210b00c1e442890300003541c5003ea4042c03600b0707000c1401e24201c80c1d0709480000c0358421f85041c00c100c1c0200c901a13000500050905811803c61803c1d11910340c42940141e44413030301c5000d4075500c10002c1640340c1c0181401171151040440c0075200c90491620480b4002601002031070508051006441142e0000c02181c80c4002c00460042c2e55910b13411080018450f000000c100340d16000111012a0651200030382000100018204007502040440d90001e10340c0615a00f00070640c01071b4600144151901542c0d107095503210b9000280c000c14000400510206000200d0403a10485802c8180c1c42d03c40700d842c02209440d0b501e03500342a400380480b14404110f9200144c140c3c3d1000c2c0c0140d00582c251a003c0c080d0030134040c49010300391545207103 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 255175971 1250 255174721 255174739
    0xc0d0e0310022710080f070302040b070c030c0806010e1909060903080f01080c1302070f0b010f031505070c06090302070f0602030d0e01060302131a150901020705041b08060a03080301030c0f06020c 86
    0x102c0c00803144591f904c0100c071315016280503103c1d030740b02c2056000080304803140358000c0814410000c03018410006080c2c400020700f059858030303c20250091014001e280c010302218007613080710340300e07800c819071451b00018203006280035407070000c0204004a5540f005984110000306622402080e00103c2550080c0f000c1c0d88c0000d140240c1000354060b001c01c8603c0c1030120358001c0014a4403812038020003400380c2c0c261807140385003400902180c0780894040020710742410844070300d0700000c03424007981c1c011000040072801481c0607071410304e540e08515041c41586000050166000000341143c048080e424003060141c154010f09a03000342c08000c0d0300c24aa4a205505000303a43d0ac9030036160285141081d4412001003c5964020155a12141c2d403c2c0050342c4101941c04100d001700034041524100002c8031141100c2a911564401c24010001e184000c42e1507990b44011a801560308081c0d4940ea9503540c0c030304000301c07410510460494007003070740c0001806030022990296800c0c0150080712 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 255177221 1250 255175971 255175981
    0x6041b080a0206030c0d18060b0a0609031509062409060f0303050c0304230f010c1709030708031605070f12080c01020c0d020609120c0d0e031002271008 67
    0x140c0d134000030b00c080c064450602003104c01620500441c640c00c0ca40160f000c1e403c1c1200d081060a0b580d502d14501c6c010110302c41d08000366075004c0e416608a13a0000030940d210b40101c00c1c0000a082d04040281002e42000b40c1e000050502038002e100d8100003000e2111410f0b1303035858100646c1c0c400d2081c40e40e01c040f0743c102000400d02910051071290301d200241c0b841c0c692101c50aa4100300c00c601000340034440e400b40c2ea502d6003010400c52400001c2420110742605083d176401042002c4c07405114203c074000b00703040150380c404200701e002174040d40003584c0e01c900c94000c94045200700c003107056921f40302d4080001303110444440c004040d42c1040480c0700c030100b0309494490455000d81e1030401190750030000384200307a105010320110000154050010b505129110a240020400f070240c4400d40c20080000c0c42d041c0092903882d51000c6080c0510000394250009043c07803210080041e103207000042801c2e080903407041e402420040103001c5c1c1e40207a00301d800d00140c0b4104181c480042920b12003c60 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 255178471 1250 255177221 255177229
    0xc01050307050c01060810060e25032c1504030c0b040f050d030e0705040b060415050906041206050f0f04020d240203010e0a02090d06020a0302070206040806041b080a02 74
    0x2550008650070801e28024110b62221300719200350780000140d40021002e10260b40c020300950000b82412440988581084480c1243c003003030210011900e501c09000b0304411500903040301c6a90402c105210f00904d07074100030341d0854800e02000110038020398025400424040e01600e0050f601036035034018000c010341c2c0c0c0482014000e0403e4462490031040d00001078001c01030050101c1003580c1c04900e4811016a240c540500c9411251141c0d05204040050307480b4002541d0456030102d0204200c0c1d640d961007990107104445c03c541e082900040c01103000c41c0948078000c9064801c060400070b43c0d0300c0400300840002d040e109028090300c440082030262030222a140c082501440c002c40f82c5001e1000b0852402e500c001d01da19500b40c0200040040440030060582d01c110300680541c80c100c60440002d02c2e0307000f00e1900901041d404560089428400e034143ca109a038060b000da03a0307894032100005e95903182160101c03802d00300042c440300c03d00d0060342c41200302c9082200400032810154200 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 255179721 1250 255178471 255178477
    0x9140c0319021902010e24180601060c0507060c08030c071401050702070321021c09051302040905151302070602070206042d03050712051f061403010e0c0105 69
    0x56007003078059811201522090b44001d00d064096034490300a01140c5007000b03030030340c0c007a0020a1200c1d040352085d000c03407424a12000043d00788405241d1000e0740c03000500600442803003014800d521034440003107040c1e900001308410140c0184111038a1903503c0000310b410450000b0020804107003400442c1c2d011902d0303c09000708a2180e910032041d4104102000d0840307004070355040041c1d1002100f0000e0003001000c100c04000c0075003103071600c51aa00d41c060354450796a9040c4001c0560030005800040c820308051016000084c103500c440441500c1c113002a41241c0203109059107450301045003680c7c00c0e0f500d02c3c90f2000c0a044181c0040821402d80000c0d00035220681d030142d000c1145c5001603032480010701c050b01c04054410308151011848800003203400c00302c1306d020380da400010320100b000059800220761003c400d00d010f00704a850200d040810003d40c0d414460565016201702c1c42c0c00b81c201c14203803408003180c01c04403400a410035090f140f80081103040c9811408100081d54455002 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 255180971 1250 255179721 255179731
    0x6080f1b0f0705010f061701060312110f0f01050f0601020607020d05030a0f020c01090302120c060a23090c01111501050906010e090a02040806151e0a0b0a02030d0609140c03 76
    0x1110b8100307800e07500d40c9402c0d54105929014101e80d034500074000d0021640c0d1040d498000c00d0020085c0300e045945a41c511350001903010300b401104003031041502e80070452820001d0954017602e4120000065050291500761581c80e0001075910000f802e0354400240d9512822a503401040b040305440d5068410b5440500094141a100c0424681e50030049c001040301590040002803450307880d0400030300b089844c24039070402d200304105034079a54100160103604906400000103908000c4031046c500841039007018860320720004200560081d01042c24402180281c0b00d2041da07900d081803141d1583d0500e4401c034914282500184814101019100d50140040c1092800d01e0503c0e00010481c400071100106081d40024080c00084c40501c8181c1e0864481120842c43e0250980040c9200041c0c04030a004c405669504c0e4009903120800c0c0e100620111460b6030b80c980034120001e4817076100c824002d42c0281014400205409680304421340398036400c0040c04981c45a0182581680c0050a = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 255182221 1250 255180971 255180997
    0x605090c030a0c080d08011206020f1b0a03030606210b061323040203040804090c020c09070905150c032d04060302090906090f070f170403020706080f1b 67
    0x141841601d003000b0212400e4090041a101c40307181c0030000317140c0041c0d01c40301c00070080003034010865907030028000200d0710381c0401c01507203c244450600e0f81030300a144035204803480781540c940341003401052071105540259007d0240984540c3c00f0b4580345aa4000c601d11101c001c07050a05619070b5510007060111f0003002d6a2404a0152100803228125006041003190101d08400700c103030403992469004400f50f605601354035160b100d40d001c500491103004242a03c42428130b003618402c5c0040011000014040c41107800c0140004000b04039501a940c080e50200c0c0d640360070300d00300b06d05031088003004c44004c506e0120802c1e40301c080c0080040328503010707540311010b14003800c044201400241178540da0060300c6954580c00c20402c1200a84890b00401151040c415800030154019500405a0400b0351050100340000c8492641282d01c800b030580004050104040d0701007413000450b01d065580c0d040310303140d140301001403401c15203040c0c400e10440c07080203c100e00c6200c00380c44e00c081644 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 255183471 1250 255182221 255182233
    0x170c090103050c0103180b0a050108060f0603070605070515010305030a0e04020c0304140114040b09010f03140601180b040f05030105090f060f19021909060504060207050607050102071202010c030b0913060509 91
    0x9540d0541e07034001688e00c1100395441d0001400142d00801081e6030183d81180305401c5400d00b000445d4540d20680030f5a410001c00003603040030b1100410401404824840d0306220075a135901f8415100d810405410b0700050b00044e54aa00d450700d4020f94a214014101452410745085161441d10054009150602001d01008121060342d10013410041020360781d12a80e88110340001400e260070b0030701c0170040c5440c00d4448418002a545c4081e4010400e003054800038580d580c0d00700403c0300940c08000b01080006010480c1a0b491b1502400c840d0190003d0200d41c0b11005420b8079103000d4014544580d00c20700004010709020701556030006046502407006001c102003410603a484007202109281c994a00d0345400703544440701b1801041180307000c0c0d05040c10010029107446041c882c9510400e400700c1e800d000e0100070750442c2d08240c2c0c0154140060003010384042d01900c1c206804c3d102191078041e00c024a8106a89018420101c513007200b0301803400b507036922000701405441e0205034407402c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 255184721 1250 255183471 255183473
    0xf11060c0705030118230c120a0b2203080613090602041e08030706020906091206090d050f16060b0d05060403030609020a0503060103020c070806130b090712021018170c090103050c010318 82
    0x20049251400b8050058201082c9c2e50500f104102c0b00548614904900c0050071202c0742c900c0c010080006034145414421034a80c0c00010f402ca2040c5120a800e0350300d40a420b0b0b04101d515030040084520400301c4118440558510350803807401803040f802d44c2d801c00c0168000080316a4010410041e00402c0142040d07104000305144040054003481154860014000b088000b001103050140103032800134038142011840440318042c86040c810080907050024003005080e030031101004502070082880c16007030b4240256100c900340c07010f80102c1d15080300455200e105008071010390543c0c2d144c503887c41d1202c4004500a6005a090050900844002040250040c04000d0149101c11b00f0f0400360300d140e0a260a0280015005e001564041c1c402009014180009d8684d40e64044403240c00c0754610000650750383d1440c04101d0361901c40b5030008a800e41c11105041800742c440d0048854030310350300c801d0102c00442804081c0c0180c1c03000c05126019803294002d01c8081d5403569409181382d4107 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 255185971 1250 255184721 255184729
    0x180f020f072001090533090a23060706140405010c020c06090a0e040203030f0a08010311180408030901060f170613030c0f11060c0705030118230c 64
    0x101580c56400c10038005840c5003400035034550384840a0407807007100070200114002030000c11107445024007866440c00110021a403114942c800c01d00b0741c1c404c90b5003041c0d074451120b1040d031254258503c078410004001ca4a05c01984c1520b8980548200308032400d101041001181d4000d84030484d0741e40c2d15441100c0c0921000d00c1194081c2d403040c400410b21100d6610040d0a00003032003900b40c0103540510030410507030303039200003c01202c106005041103510f5900209003503200302d50f004510f4500003d050350f00720358400b00340781c1200e001350070300c6090301983c0381000203a20203c01e00d0400304400d1808a008284220b005540005402000042080c0d4808600014040544c0701040319146a400c040e41680c050045a51000c0307483c5680b6030304002550301403c0d01c00c1a1101800e0002a401c00e402084101e02090a16010003400740380c6666698030b405546032101e0086d68082d50a14841e504e9070f22007092401a82e9074081200079510261100403034001d41da600020319148211100790f031560301c2e = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 255187221 1250 255185971 255185977
    0xb1003020319050c0609030c04020705030f0c073b07090f0303020105041401050403020303040609020a050901031203150f09110702040507051308062205010e0709020a1101020f04180f02 81
    0x5003021607040b041289081450620101c0351055000e907104011541e034641d004690108041801c80b0b006868510a0805a01c5e60042c0740e0b0501c044400010000b02e4000009541400c458850004040e000b066101d161f04c8101600e400d4044522065440c0d80b5050100034000c0d0310840d945003408480340e4a060000e09010300340e1003940035035520001c1c0720130f00481001500c1030026850082c8000d040a9074025500d00c8018005080141d61304135000440d51144089001441c004003030102c2035071039042c01071114501d448058042480c1c010302007411043c807400202218000328100020a20f0580f003440030b040c0b0200007401141080040c42c0060307549100b0180588000c2d560b231074035a80405520b0b4503840b5550000c0b0700341e40c07103c401c101c1000103045814050f00301007101d0241003200782c078040c1d024041c500b60240990040100206074010640c1c007612403088242c0d5101940803045402900300c1c40b0b1400c0455200e00108418400d003030440b54002003a40c00e41c0c1001800d01403444507441260 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 255188471 1250 255187221 255187243
    0x201030b120d0302040602010b190b160209180f0114070507050a05120306130923030d050106050d0b0d02090a020f04090c09090b031b0f04090503030f1f03030c0b10030203 75
    0x3e940820f081c09166824850824880341c00d95404127003142d02c007950114100c091049140c071040010754508094480311007a8403482d4060480c1c80b10f810400c410440c105601d502c42d2500d803240e200400c01840050207031000314142c081d0f0010080c3c60700d6604031003561200c501643c16104401c00d03000010010042c3c001d64080044209469041c190204017006030142501544c80b030600ca0380a011850152024000c0c0610051513482c140f42403420b0f904501902e2115130002d4501000000d10642020007131170b05d44480c2100300040c07010801044000711001c0380103900507980e0000500c403e040751b4020303d102c4c144901c02c075003001d507030f1010b000990f60401601400604002d80c20030460380140580c00b40381348214040c140340181c00032500b20181d0301e8140d40c0c0c0b0944988000c0229a25654812608140c2007010359a0f0380c900440103a50b01c80041c0c41e0031895000c0030442c1451100250f680c0c00075130b07505680303031611200c140d242e0070180c40c0080d21203030404c03140e20f000000603903041150b003200b9 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 255189721 1250 255188471 255188477
    0x70b09060103020f03070806060d03110f010501091113050f12060711010f14040f081303030c0c09060e070807020c0a09140702011a0402030c0d02120a0c020c0d0201030b120d 76
    0x25819403061190001380f1a12090080d800030100384585000403858541c8131805940300002010141000c850500b10b01d596440c950141c10b1a0411181040d000b203410f8aa41c20b2060000d01c800c005048400e1141c040105a00d42c400b603018021403501d50108084a980100b82809507034007404010b0420506840d40d8011460046c0007490343c0d00d003805a100300c824913802c2009201c4400145000704038000304010100104500a40b04203e40c1c2400e82d0903184403450103014150316840c015140c40e015103426103481c82e0102001502040c98000c0d981998020000c0c003030301c0d407a42d0009449001c00640b411041d40103062051800c0e4031600070650007004000300202e859175030200c4c503000e0b400d00030300700900310390614526500c034003010812000050340a41700181e0300e070341e1006401507601820581e002518000100c0402c1d000072000c840c0c0c001c01c4681010006d0505a4100307a980f000a01d125540205124084e0005507000f684040c4000700058400301e0380c40094085503040a00c40601c0d4004 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 255190971 1250 255189721 255189733
    0x5150f13060903030215070903151e0902150403030e0607080f0d0b040513080a0f030f05150a09020306010c15020912060106110303100e0c13060e040c032f070b09 71
    0x2d041d4100020b0540c6d5030200141c03811800e11030b200070400b88040c0005040f004203100314500b0800039a000780901166200810108140310141030082c1450501c141d204a0090410890a0498508032411203034144c0352a00d08200da03905001441c0c120101c207460741d040078052140e0080c03540004114410440c840041c040c04040100022603c014040340c1d500405004800002840b1404807881c0810ba810719202c0c540032200d00310003505030445903120709420a410f2003050b20342000a2490b212007221521100c9441d10540412804102d03a520b000038010701048002c0748942c180c8a0112400080140c50408500007048400d124901e5981c41c0c0d40c400401045800e9200c10180144000c038405585503083c0700303800700d40411103409004031494104002c90a2000c1030022100d6006402510000495a401000d4100890710b2104c90141d4101540f00000c14840e100c0c0040c1d03074030b615070310b0f60003040c3d501c043c1aa0103421110741c0500110400c180030114140c0d1941c41e1240030700d2002061 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 255192221 1250 255190971 255190973
    0x120301030f0c0806091005180f030712050a090501211a040b0a03080d020a11070b0d2a030903050d1503060e16060309320601080705150f13060903 64
    0x200c540842e80c429180b541081301400300f454404241024510b92480021906445000310881a00c00c03010800c5000e00c00c0c841e540d00309130700100c0a004918001d00d032849843d006007406031250302c2510300d01c00000b080b10350180019130050202c107000180e00b050320003180b0012002c1c0412148401c800700c3c1c1d8916a019030001501d0300780980a5502c105540050000b0302e55a00d9042c030b4002d51002c50342c00394000c10140e103694030030701d0340340001240e0780101c0b0213a03070743d0300081c009580c03000300e00c9070800e4246001c282030701002000ca070703690801c020600c000008441d07104a008143c080c0d021000c2101c20441d59162190601a400071403c060506100e001d1462501c442100c1c2c030340507019006c0c3c1003d034100100601c0c0f481d10304100e80d12800c000c1200c41c40c40c9440d80d0064130041030104e05490107140d046807408040e2030120840c034080e044422590701c82c038070b0680d14007907440799603844014044449091466000904000800401300f01c0c00c10b01c49a8040300280090342000d000036510080800c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 255193471 1250 255192221 255192233
    0x30a060503031903090203010b090f0709121101050c070e07020706020709090b04140109080711030f0f030a0e13060303030b010210050108060708180d030c020d081e09120301030f 78
    0x180081204400a40c07400304258410300b40c4105840c10b03802403650780c800700da003992030030340040b0303c0c505004001c5082c500e004030402c10a00c1080c0c9a040004100c0000805e4040034602107101c01034000040040c180450001103c451740002c0c0b60000a0090036400904c11000d000840e0190010340c000d082c1d000e040400007071420107e80e004034215401c0650400204a400907450b42058011502c400300e803580f41d403101e0140c560100000c0041400043d602c080c4422640d2100115104a081d0b41c5250800300b1000c0e5510078485402c0a10340082005c2070206006001c03103c2c01c60b01c00303008101c44894192051003214003e500a4002c039441d010110019030741407203058003902c00b0700010041541031090096075004020120f4081c0b10040021a03680d0410004441c00b0b419440c003207580c034008094005010b00300900c000c0d000b5203d00c2030b003072031218003441708640324181801002000c00c0350010603a03d00d02010b031400d2201d0199042c091503002100000b540030714000e8403c5a10411a45401 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 255194721 1250 255193471 255193481
    0x21306061e02030f071704030b0a0911011e0302180306010308130509041502071e210c050307110a050607060b100302040b0d0b01110a051b040506011b050111030c030a 73
    0x161046401c1040310900341807412041d140103071b8014550707000c202c0c1303900c0550310350b407085400151948816004201e00301702680c01c98500c00d8413682045014048080064840260b00e0140941c0381c2c034036004505903a44640e018100034200048520703070b03808000c0f0109060002c01e801c260b49650000803082d012070440c04c100e0f4000c201c00e03180c035290740c40c083e00c1d184410385040e140e0b1402a9000102e4105100340c801552040202c0c002070802a04164a4200c40c0da2aa0f4910f550b8040100c0001004c400e00601a41103001e4102c00554036041c119550005000c2c03105810940c00b1801c40130204198030740c4006008454415080042c14910301d40c00c01a15295103c100303000c150040100307000d0039160005880c2034001c1c218000c55040759041c0140e880021080310710f00d46208800303520050010001d03030409000d49610000c20520075038014031080c2c03807003143c0d4103002c00d561201211754400181d80e1404058090800011184002c0e1003510b81c40d8002c1e540581d440c803001c01030190b840160302c58 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 255195971 1250 255194721 255194777
    0x90705010c0c0b0705010f020f130801180b0408040801020f130510120e0f0d050a080a0b090115050705030409050f060d050d0f1206031a0a050615030402130606 70
    0x2a202901d0706503511482200c0b1400b4968903410003184c42c0040010035000039141d40e2411070159120745e000038075001c04d6008001c501030f0b004002c0e440002c0c03081c4180710340440f801c20b110400803207200340d480b616402c0358043c100f00d500ca4001c020008800b00c080c4060140207240e03403800ea80e01d9050700d03090740303140e0b200c0e0300b055210700c0303800c014407a0b259009503170b054000355510800b00c3c18000c40c51503242032180d03040c480d040c10b001e0301e401170a216602c04000c003003081058540038015201ca040304030448000e0b0030002c2e045407203600188418501400c100002100764500300d0703e46007060740e80d2421900140c0c00b2600441d1101c0c2406071a40b20681d9039640900c06039100842092992242580d620300d0102d11414402c031644c238400940d00c549100c00200009503014031680c0d81d1303403400328501001c00c0440f0140c0030190700030500006250056900a00000f030400c00415454031007142d159001810072640000f00291140031050540107213001000b241d22500d1b01e2800d16a0b82140d5038602507a = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 255197221 1250 255195971 255195977
    0x507081602070605030610030b090412120e0a0b04081606050103020a140d1205070812071407050330070201061406090d080309210a030c080105010203070b04060b0d060509070501 78
    0x2605001a90703008060300c0d40206d0464054907070341d18200040c2d00402d9849025038104950800304030500c45000c00165984046a43e1000c1c03580561081c80111080346542e205150081c000c00c4022407a8000c80c1b94000d405402e00615006550b070812104042668080703540030340303802c010004c1d440c10003075000050010b14490080c0c11051b200280c02c501c840340000708680c808a01c1c2c082107031700c1441a00c130303060350281d480c6030703202014000407845600407100d482c00100481080030001c4051030585038405d07802401142003544020b000341740d0003846d0a410081c00140f000c3c121107180c400303900300d00440d201d0f00001030007810020309100401031502c04a0103030a007007000428946600c00443c003a182c000006035200d803103840419083c410740007001d810b0012b15011307804060034048028a1405550346003002152464541502d03140424494540940c0082c4103200c08221020b03c00e980c054411040022030304020f00000b200201d0000080e1031041d5107808000c0c6500c02000400050300c000d003 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 255198471 1250 255197221 255197233
    0x2010f0302120a1a12100e070b040b0c12041d010504060510030513080705070806070801061d01020109020316060912210e030a081c2f0d0507081602 65
    0x1020185480c200608014400f56482a140d90a03100b40c0f09180d084040051800c903003208030119907944e07002000d000e071180c549444c2c9044004000042da00c0c0c101c1e03007817990b114100380c60310402010b513811081c0382420300e02400c00202e46288100f002800500007010324400021013941d207190300c86505821483c081c0d03181150030311030b40e80c41c948103007482501440c0c00f04103a0350300c18402c49041d02100b00100028000f00d40c01d0b00b0408085441c40640d42e9910450780b00381e803251402c50b40d50a081c41001e001c5a00d07800d4020511044a01104d2004010700010070b2001450340468078280300350a02034100b20648605100c80f9501016400c000c0400e488010707500c0901d83c0b180007502c60340ca282c041c0700ca40061540c1da1003074058401850038a0000307003950140b00322400c100310580e11150002058440b40181c110a0900d144203010400480c0c00e00039a0540c500c032061941004ca400c881004254244088030b981e60316401682d00c10b0700d23a980d422005003464119002c01110041e032441c20b41d000f035 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 255199721 1250 255198471 255198487
    0xb060f0307120201020a1a01060813030801300b0604060506040b0a05071b080312090307050c0609040f2909070c080f04050301090b0601230304060903020705120a02010f0302 76
    0x54803805551096103142100704070b03440180d141010a1500400100701d045800040f41030701ca803010704940c007507140c070b0548d1350390f202d03a15070440c2203482c00070080380c5068010700842c45c0d40c45588003960714030240300700c4140b102c60301345009548404003111106201c40c01c1107083d0419000d00e4008010654046007490300b4010a29a10702855018000f0050085584c406100314003104070301901c001c403400f00c0d03050703146d80c51070307449621541003044c0f510703090004190240303c00011942c5403500100039003505d01c500e600300603459100526456100703850300903a2400960b248100102e103a07030340032403450401522107407034640c00281c00316034868005403040085044e0451080440180d0118000382e8a960f424001d0b412406142c01136a055803030044480100301076501e516009400980300d544035800d8a1190700c10813004490311580c403260030300100300040c6658014040e01c5100f401a1041152244085060407a5001c5026043c1c0d0081340d2000c190b517000240507d04441d1413806516040f0a = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 255200971 1250 255199721 255199723
    0x101809060606091d0a090804030c03020307050f100f11030c060405060603010c02030a0509031912030b09070c0609020307030209070807030e0105010e01030f060b04050a0b0306180c09070c08040b04030b060f03 91
    0x71082c9104e041e00950720008189120765840321448591147c222600c0c1d58403820002000e60a60100324040e01c1030307100c04100f43c0380400350700720b44400060510202d074a80c001c00300e515054088018081c01217060f0758818600c41072000d8201802e0400041c061840c05007001072400c100a02103600a0340342640d02942c0550200445503540d0040c2402c03a0751740203040101e868290041c00758100d070f2070000000070401001c40f8441c1d8020702a070f9800d000300304614042021621040e115075000ca04d4811000740000d00380d4101d081e805000805491103175940b0b4011580c544000c45004001401e210108050f90740c15114020340103443e14020012903050141704040c0d1901070002904440e01c500009080040301c0d08100c5a060000d0300c00d0050342442c0b80404040c04d420454184240100000110880c07415503602d414900c4010003031030035589403002c0c0300c42494094603050401200102007004140c83e80014070003031840f040116966481c50415501500b0701621844c400c0410883c128244c1e98 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 255202221 1250 255200971 255200999
    0x90213151a042310091401020d08130c0509040c06020f0a0f0308130c0b1306020a082a070e040605070e0f0103020d0209040e011401080a03051210180906060609 70
    0x4404003a08000000c2c80c030f050035036010070002459102188501c130304080c0d907016001000b01d5000f0f0072488803100b031030300069807507219900c1c0d070800040e003000c002410852451074515945008091640152791600041070b1058012035095989c9400103404010740c1d0350401403e006401d00c1320151045c0381c1159503102e41a0500c0d00081d00308002c80e000329030030f014118108043c580d03008041c0803c1d2940c44699902c031790401c1c400444140c6081d000001c005d070000c24a2000036501c81e40c030303510300110041800b03843c0340f4520810544c800301191458580d6010030114001d011911418141881c062804505682c070007004041000401c0f0400c041e01e889810b004103180c9800d08001d030300d544400c1c1c50a002801041e006c030341e02c02d00303000d20821000410f511029891406082e40403071607803180a00e0f40e4070030801c0d50050000300b040094080c0303500b10058180e0040c20101d0440807107540c85188503a0740504005980ca400d40c0e0f101510708019003072055500800c00b40c24075884561402c4a4200f04074 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 255203471 1250 255202221 255202229
    0xe010e010e0c0c16080601050a0b03180309190504050604020c1f020915030609160f0302071502030406020310080706020d0e1908030a0305060f0a051201090213151a04 73
    0xc1c008000301c1d14405109040d0303103014064904941c580407a88a0110840e00c0c90300c00d03000f03031303014a038004034031402c2c40d40441e1306452014503010301c3d60b10748400d030001d84074400c0a443d5082c081407005403902d80daa00c20b03166265950150700c03110242000200011580c001e40691310891040004051020700460780203401c1380803001c189040741c01e48001d034019101e2625660350014006503036103419260781014600404041d1000e510704c2c1d8480300706100c12024003100001080c0b00c4141c401070188207800602e00c01e8441c0c02c10000380d889100030502030340c20580301216003503008420840c441c0900e01030000142040401440c1051410b02c02940350094051801c1c20000801140543c5482d46d0804010000c1040800b510780c80d81e41c40304a84a0704440803140010303003088041012071070520100d20f05000c00a084030a107600e07140400020000520380c070840c9540711012003000da40c0300c1d1144a0000040c050114400044035440f41106c81290000c401c0d81154000850300780982c0300c2030320181c03 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 255204721 1250 255203471 255203489
    0x31b070609050f132d150b1b0712061506080109092609010207090c050a211b0314010308040b090a09150f06020606011d061e12010e010e01 61
    0xb10440c0d000300782c050a140284c9140c050500080700650b0b0070740c41340154a07481d034003010083c2500307442c00c0d00240c8070440c01c0209124a2a6400d015400c0210020442c104420481d40c072001c4a4014150030115940c1c89071218a0440020b0320038450076002d02404200414080c01f007407401d056014281c2c4006016020081d5501c052441c00c10a052409a031503081c0301c503880c0c040a020405c0017540740e025048503030050140c0040015201c0c01030146014080154031414100500b152049503020200c2004e042c415440004030229680c21b486000c0701d2806504003001300020b0000c000e0180c4076150240009a48200010408540754000f03039801d0b00d00c668100741d41c0303140c840c000845015846d0044d041c034920341a603141003107150100340800ca0712540c01c2c100c4284c0d80c400f010798031101c04403141d502261b00e8400050340a841101c804104090080036941040b001c050750303002045a00100394a100400a43c09030681007011020b401083c4030408450958103055081c441c1010600ca00700d91 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 255205971 1250 255204721 255204739
    0x1060e0301020f070804170f060103060c0e09070806090c040807050618060412020f0109081b0102070f062609150c1606150504180b15030f031b07060905 67
    0x11a640c203404a5042c62481c0c4895600e4200354203100013168030511415104500c0204040401d80020401d01c062008610252810f82c3c43e5484410203822698540c03001c010b8210781145155030390040e0036000b607249503100b41d0302e03180c0366051044210003d010119602410700041110311800030300e15040d20307000d491290b280d864101000070301d09404445658090808500890603600540717400b51700380d0013210b036544248481d070015105074000b07021300e1030b482c8c2182134090400901c000004145c140188119001a6501c2e0400310366018183c002c3d100040828488200b148580c0b0301c41c0d052298408454081c81c00c0c0500a5aa6600200c1c1810034000360600052aa50304840540d04101d0021050030840f0b070345490728900030b000b446080300c611483e280020449040c24800c0c7e4211280e980e5034001c03203007400d8031128010301004001400000004080407440d071020300c4180c0302c0c2800d0300000c5403500d4491a0f20081d051040360300d086513074482003041114651240310369080791010342b0040c1c4 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 255207221 1250 255205971 255205997
    0x103110a0309121b17070812041104060f12051204060f090510052208030a0e010f03150909080f070807030207170327100e0f0603040b01030602031801060e060a050402070b0106 77
    0x250303004884007e42440c0021407031480c00664000002c0c0700d1071164030703424644c1c5181400c100880d800c03406140036081260700c06010418103101d1314010540034008442c20044500e41aa800d54000e8014200084625185040d02a00131024001501048540c140000e9039004010075501441d60030042a019118078804c1406804140401821854050b1b03661004000700c0a4034107000400e06070300060b11301850400c1c00380b09214450b00540d6001010300c19601c0c22080c940a4120b00100740c521800030410001a41901401070040b18805e8901540700c050604003c1e04180c6c060340b01001c079000d0310f821500245004002c80fa501054855100015204883d40f0750310400c00a50141d00800c4900c0510090782d0029018610b001d0b048444c01e40007a0380300d041c040940000d50700100000708200c0140002225900a968443e5444080d00c400407110b60840e825980b0301c2e4003c01c0c1e1407642c0c13007d226650908451034409050162415482d0080c0c3d0350320ad01100c0710500c951001c124814001c80 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 255208471 1250 255207221 255207263
    0x4210b042d0206120403090e09031e0c0601061107050607060902030f12030f100e070201050103050118020f09221109070f02060a0506060405151306020a020901140103110a0309121b 79
    0x280034080301e03841c0602301c2c0f416041d065a00c0d84041e04013400c40390b20068410700304101008480b17020843c4405040f0907444d1041c00c0d207903081100401c044034094980045801d440d00805050018000c45011510241a00500d400c00c03004243d10192500404c09200100001d84226600454802c403069503903915170300214000c4102d40c11048690307800701c013404825541504654142d81c0100020840d0740000380200740101c1120400130741010344008401c08a1034007403040795015861a440707030304400809030340d8a03000107810340c03c507540e0303130200002109810403917442c42e4858468100102d01890801020b5980c04005042c051820748900015074191a41402d450040001400c104520f00d4124041c160581202c2c14425499080c40740005407a4400600030000c580c0140c080609a420000070448003402d034900d9074140740d02e80740c0a061940c03680c07004103402580ca580002d500c40c170303d01d400f101d0300490008542c10810f030442400402e94411020f10348065200940b00c010b031109400d00 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 255209721 1250 255208471 255208487
    0x3060306190f1e051612020d0b030f0f010e060c0904020714060a0606180302450105030d09030b0c0912010612020306160504210b042d0206120403 64
    0x240c0540360604140c01441d141c00b81d560a003c60800405216654548452078801101d4161090008444656104411015500400f10403095690100b402034084020a2901707400000a20080d4031403103a04806030001e116810301c00451101804450904a00e070140c1d602800c00d80610866000071300404010503044010b6010300c47c101500d0b828030b001c03a44a001032407a44244004100c52a10900b5900b1910900c041600e60052032204865a01c0100e4508000c01e0300360080015001d8104c03500d0031254044000c1e800e00103200400d00c07903040030306050400c0098500203003400000c15060000440000702a540031010614a0362508458000682046640c5808036440e5203084400700d03400c2407911629001c40e009800f211002d84425417004094625866a0800038000f80b0040c40340c80c400c0c039584014540c0d04c0321300b0741401c03195072906800f011040d00c0842d20440c08131944c541103010019040041c182c640034080000c103264001c100c0d58130690041140e030394401c000042c00c05000da640 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 255210971 1250 255209721 255209741
    0x3180f0f09010f08070806040f03030903090b0309010914010203060d03080a0b041a040606050f030106080601052a0d0509010504090207080412240209011b020a09020d150503030306030619 82
    0x1400226580d83c1035030300b02200190160035000e001d08000400c803030b040010a2405079034410100c032018a0291030450041ca003528046040048182001860342841c202641c0141009000010300300d41a1400700d00307401e03422000c40c585034010b008002a07541ca49d00c2400100e909418030b10303400e603542c544804c0140844048543d1161420f110001110307880e03c69100048003ea030200002c5481c0d00c6c042d1694041c24601c8800b1080800042c00304601c140c480303d40042d0306050050030500c441c0d50210760014010b541c40e0401c0d4461451060440302048507105000071410030520300500d0708002019407069000b01040240c001a5140410011000b160010a0240c0d44181242d5a03494039035104038043c100070b1400104104d1054104929100300e0f40a944161258041d04d00241d51202c98407013000e00907640710400920000e6800c01d81c0c001084003200c0c0c400001901e0001854804c1e40300001c0d04024000d500610801c40075850000316503412200340c40304c5503030744500e00c41e0701405080b86410b = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 255212221 1250 255210971 255210979
    0x60111031605070801060b030f0c07170a0807020d142508070506040b10050d0204050a0e01020c0c031c090b0309010f020f0711030a031e20160803180f0f 67
    0x1c0c4010074800c002c64403900303a9406000a001181d69680304103154001a558000700d400d1400124030310000c40310040503030900ca402c10290f006d0004080d00076640040ea036000128812208002c0001d43c18496007882e5609801c0c142c0b02a00241d41d03030b1111b4050800d900b64094070000c100e01c4081241144840100e0b07018010035640ca0991030036030307269102aa0112441b60301903020034000011310250340305889020f8401061409150200000ba10000c5c00c1c413100c1e26659141c0041d9100280010034242948200400100e2411360038145444c40f40ad03964407c01d20032140216605a01c20043d00071101705002d080e459490740d482040c01403600b18080c1201c5440041d40040010002014000311f5005442c0b45078504010b20a040c1c90b1041241c0c010001854104c09401180010242400168036450041c0304c0d0103005124100024103811803441940c030804402c00c0054009800002070284071004e1400c243c507000200a03241a20004248a48821012440540c5640342a40f901800c010 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 255213471 1250 255212221 255212257
    0x20f0d05032502031b0f03130312020c0d0209070c020415060215060616080d02040608311b0e0a09120c031d041b0c060e0d121d0d05180108010302060306011103 70
    0x402e501d00326034218070048410045030ac2003400045d002181f6a0510100502080b0007c400c2d0390030021590350041290060003400d044481c0561201e1003620114100085e1503000035043c500042d160603102e16031044529100001c0059644a4209884032018a00200f4014803940e20b000100e40c020035104011292002c0340c0065802d6000e84224040c00c8070606080d0b10b41c0d56541c9810110110300500f4075030803505403006000510703030440c0c801003105540a2080ca02d80320780c1d2699419a040e183e960009440301d480009018666200340890521400e0000704036a4980d00074100180b208040100c203a0111340207407103512190424141e00a03000070711810510404000703000710141c140e041c2c960b5464403e1100d4002000038288000c801c0546800300404526000e1102400d000c07018841401e048110044070070b0800c109418021183c2c0d21401c1e15458000600c1e06480c00c924900b034104201900100007680380c2000312a04040203107402c40c92181e4840f561461423050a50000d0703014521 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 255214721 1250 255213471 255213487
    0x70807080a0c0f08030604060e061e030c120304081204050a1701090209040b040507050402033c010f0e0901140403120603140a0501110a0816020f0d05032502031b0f03 73
    0x2d1300114840d0800b1501042202c0c1c4511603244c91441c00c03134010340c01c8103040c02104e54502c2041052856000b00804840e810b6465801082a0407052100b440076a4404113050090000900c02d030b9910b62075543e0442e060034a40000200c1c224168403031400350f065000d4464031006002e402121400d0b03009003600040d42050302c1d09500d40c0104450660307140c0a60000840c151900d8002c584c0100803170007268054501000c14103105041c0e000ca02c04c01c1c5084d10010351020340c611154a402404404406003d4030301d421010318041d20003d14202d80f41e49884500ea030f441e0ba0700051180c02a805142409480104030000001402d80b074101400720401c60711b083c80e00000000303001c580144a00024452071580c0d01d191807090041c52000004222220002001c05806443c1c044044140d0f2040356110100c0c1d1081c50b0903c426803152030000380000080001100c10b2001c1412060b401822110a0040b6608000d4482c0074000c00e0420000d454110258410020009043c480812400750f0f030782c942c06 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 255215827 1106 255214721 255214733
    0x3061f020627010509030c060a060e010b0901210506100206010305060103141f090201033206130e01151502100944070807080a0c0f 58
    0x503200e9102c00030400f4003880340240040c6010b140c2d01c5100744815400e28400400581b950343c146242044400e9090303200a045401000400345c0b5002550300403104051444940c680c518180e00e80d102d000042544114010780040302d0403581108104410303621900e003480007a150741c200b1401040802e21180c041401e9500d10010b0303483e84480390400e6032440810005214015a4548032001156054810800c00000c002c0000a048046441d02e901c2c560b15404884a00b100150108495071119444650142070b040c10912000c50b00408080c003e00031301900c10b01e416030145c40007030403505c48a01c6c1c903000b4900ea800361100e200505c002e20050180014103c90245181d559050843d90204000c41e60340e0303030000b08904c01c4101d07440b410340e891040341c24440c07120700c104100d200103101c0504480010364860f45c40c0781c039520303543e0301a200b00c2070382100502503008e400304220030011 = true := by decide +kernel

theorem cover : BRFrame.Cov 255035971 255215827 := by
  have h0 := BRFrame.cov_init 255035971
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255035971 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255035971 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255035971 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255035971 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255035971 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255035971 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255035971 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255035971 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255035971 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255035971 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255035971 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255035971 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255035971 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255035971 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255035971 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255035971 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255035971 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255035971 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255035971 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255035971 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255035971 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255035971 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255035971 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255035971 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255035971 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255035971 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255035971 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255035971 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255035971 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255035971 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255035971 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255035971 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255035971 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255035971 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255035971 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255035971 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255035971 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255035971 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255035971 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255035971 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255035971 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255035971 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255035971 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255035971 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255035971 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255035971 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255035971 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255035971 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255035971 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255035971 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255035971 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255035971 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255035971 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255035971 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255035971 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255035971 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255035971 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255035971 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255035971 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255035971 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255035971 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255035971 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255035971 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255035971 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255035971 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255035971 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255035971 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255035971 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255035971 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255035971 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255035971 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255035971 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255035971 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255035971 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255035971 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255035971 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255035971 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255035971 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255035971 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255035971 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255035971 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255035971 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255035971 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255035971 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255035971 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255035971 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255035971 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255035971 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255035971 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255035971 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255035971 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255035971 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255035971 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255035971 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255035971 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255035971 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255035971 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255035971 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255035971 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255035971 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255035971 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255035971 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255035971 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255035971 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255035971 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255035971 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255035971 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255035971 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255035971 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255035971 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255035971 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255035971 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255035971 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255035971 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255035971 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255035971 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255035971 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255035971 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255035971 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255035971 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255035971 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255035971 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255035971 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255035971 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255035971 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255035971 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255035971 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255035971 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255035971 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255035971 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255035971 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255035971 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255035971 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255035971 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255035971 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255035971 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255035971 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255035971 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255035971 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255035971 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255035971 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255035971 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255035971 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255035971 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 255035971 ≤ n) (h2 : n < 255215827) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
