-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4912
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:08:15.325713+00:00
-- url     : https://prove2.me/submissions/0d777f48-08ff-46f7-9a06-7d230ff29f5e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 883273381 ≤ n < 883453237 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 883274631 1250 883273381 883273453
    0x21f0f060b1908072c0a15030e12040e04050a0804180b030613060e030403140c01030605010215060120031204150605030c090901021e130603020702031902040b0a0611 73
    0xc030250b80c1d60705040d22130804510045c2110781d681d100402e0015140080d008114280108001401c0d900b042c90310480a4100d464070700710b111000d408075070640e846085090000d88603450003901e0800d0001c4040c00100001c9008a0720f042000e00c100101d45c20b0070024440740000c4410541c131660140c5640600748221600c0340000344558104c46c2800c810708082d2406d140d501d40b5804811281118403240c0d90700100c800f4a820340c1c00d44180b0014120a2009113204248458400c210440140285040c0029010b419980486401240140b07480140641e40c462100d06044c8074040402e4804403540d40301808414001e408501c100411200c008000301441e1003854240034501300c0140c4001c80b195020804d00001c0000a41040d10240c1c514104661754040320501450048180d080042010300400188000daa80003540b9a620758103140c040c681c020752480003a005000303034110590401d0002d00005a07864125010040c3c45941c3c1c001c1c0d03005254121004001d58080565807803d482440c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 883275881 1250 883274631 883274657
    0x305010b0f0603013618050f06090a1401020d0905030d0c1d06030a0e060103030c03080703060f0b130f140a05040506010503040f0c030c0b0309010c030606021f0f060b190807 76
    0xd03002c0c107111035240d00f40c104c180170108108054039034245031a111081000c84840c1001810812180c24000b0440546810300b032028060340c44d03000901c009402c40303500b034000d242d070314cc0294102c0e0002c40900104001034242c9180080d265040300402c07108003450041c041e0000c43c0110f80420300d0340500c24400464600410810145400c003800c1e40601c42d5480782149440c4400b002814042c6020341c0303540e0800b800c140740007032070032000500d20802c041c2081801c0000c00c0d1165801001e0301c10740f48001e40c8075000c4c3d002c1600c08413541c0d0b02079102c0400320714000402e0303000c0401d00360034140282d407402d451075118020301068800a4642d01d002807410400900400c070b031f12403c0210703288603061103d9050f07521740b103035002040903410800b0380400000510015101c2442101600e528a04040c45414540f00010351104680800040002da0b005850460018650b022140e02080b40c10300700304403521a065442e590300310040340d40c0c015031080314007e840d5001e40c00242c03003500550b450740c0d404444 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 883277131 1250 883275881 883275929
    0x31a06041205030702040204090207210507173c120103020d02240904180c0608070212040f05030c0105040f062109050c0102101e050702070503070305010b0f060301 72
    0x701100b60b40c5030201340030180c01079840c3e000400003808914400358582e41e1600340600c8081034144403e03103190040300e180203900c0c1c00c10b0981e6038141d0060522072a8010130003210b0301d144104882156510f070091882c0c484125201e00580d01580500c984c015100341c00307401010103100e6a0f4184800b510154010001450002400501c161000d0101c80c160044800151000c1968003c15001140080340d6032a20382424440e00719032402034440d000e410310f1980c3743c8001c0708070b06014071002c0162420001e08402e00801100d520701603a20b0003036584030f503508090310322016180a024840c0c00380d8120b40d0407941c46042520182c0344e0308003d440503a4a00981590b03080c040d601000000c100011840880ca0403502c20310350210302860140407040e01072000241440e04203e00442524603000c400e001400540c4190030f802416150000344070344075240141d00e00740c20340d844140d2500c02c0a00100c00c001d011340010030380000654084494070000c00400810340424001c2c0741140c00201d2140030341c40c403 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 883278381 1250 883277131 883277159
    0x50106020609070b03041209080f01052224021b0703020a050405010e0a020304230d2c0105160f081315080402040b0103061e1706040f0f1103030a0f031a0604 69
    0xe41403840400c0d030380b40d09272810b1a8002d000c1c180640d64407010040c0b010039a03508004440042c1c40740c10015a895aa01082c0025403034120203101303011020801080c134503604540c40007020314110725210b1010056541c1e101d60a000c101e000b600900000070305410319004180c142c40b82c03103000c0402c42e50f98451643c001d401c0140700340d401204480c6801a8940011038404044140001030405c04401400c00360445480e0160100303910140401c0708201d502d00d81000e04462400d29250b40e441e10340728030010403000c601401401301031041040d0b10400401d20024a401542c103814081c02c1c640e41d160315079031000d00510100c0841c0490001400501c0c159100d005140c80c14140006c0c9152681002101d80e07450446540020340826414000d0a03048004a100c2103024002040d0701d103400c0d92120541c60920000504031001485032400b08403291a80c2ca410b5030003d0f04694903201e85d814010724800080c108000801c2c0307040c0e0784070005d842d0454102c1804402801c1e10349018a00015411444 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 883279631 1250 883278381 883278413
    0x30f010614070c0e0a0b0d110d0c080708030a0216030203060c0c0a1401271a0606070605070f090e070c12030b09040f120903030c0b2206050106020609070b0304 70
    0x502040b6150004551070704820162030360b00c01c408030a1070400140000c4070700205d925442808180340380000290104080c0709074070400e442440d2040c4140c500011081c0d00c80d00405550700a01070040b61410340000a04484c4c01d041e401c0300d12041030800c1b0401c0d00003c9000c0690141c04c8180000d8100b280038005104440000045601d450b025840e80c12550359014012100e59450f00d039166044c03d0540c0c2020480a01d107041d100700001580c0c4c503002011400d070020740f410808500002d050340d640f00195903c3c203401010602051512b440010b1441707442440b02008512183c6011130303220410f01c0e10921038801c80c0c540c411032007001e440da90b400410080c0010205600c0c2d6500403030300d0b10b0310420940a41c0c8a480194404521880c041c0f51000001c2c910f00104049540300b040440d60002a0128076074101e1541001e0b0344a02e50409040c55030600c2152032050b414000c80c081040a5001030b048500c079a00780e9400c1d446d180c034255103480c018881d440300740b001403000c203004c074905803251202c0b0 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 883280881 1250 883279631 883279667
    0x910120816050601030c06021b04111209030d050a180b0627090607180605090102160315050a02041215140709060906080402010917010f051906080102030f0106 70
    0x9840321240d41401824980210b44a0b0000c00040007000492800c101c003510841c0041c09998080800300d40c0042800034805204036251404004907502000c01c0300c054140c1c1c0104e070201c80c03400c4002ea40e9a5032101c40040d2007035140c440003a0051080e846a042800c80b040c0082c0107506107500c44c600202030103410150320194a40c140003d622000070300d40c5221041030080280da15200c007842d0b082500041840090004009085070758864140702503064031518244152140f1503030700100d01d0085025441200c84030414401302c14000c2503180c200b004118650f081c0641d5480e07070b00c41e0041e03014905c114040c11001103031030380000c1c11140c0c00d42e02c68002c0c2c80001440310640740d80d2003040f00e002c1c0c40c40c0c4081001e008050059070741c00300244c000780c60f1034240303460a800c09600080c4180c5091049000e03014503505e8030701107600f0a40240a41c40c6805006220508140200400c02d0110308081d4910501d0301000103170096060095910405003000c003011a607103450029543c0d40e81e0742d4040f14003 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 883282131 1250 883280881 883280887
    0x609040506310f2a020709181506030b0c160c0e04120c020102030d0e0c030a081c1a0d02030f0a08030f09031201150e181509101208 58
    0x25600d840b541ea118214a0007100340c1c0180d6803558210480d1451040c10071010b00340030301000c00c1d40300001c2009124410081d05202c1070a5010103d041a890b900043c006601b42100030000481d01c500701640302d40207542180c0d045480b140c08000b121120701c8000c12410701440000ca440424a002e010421240390f640480340e4040c0d03848021491f8150040c0e04040320507000e00c0148079025804182118460400641a48032030b000130756a80a244000b035011511142100302c05003050000307185682c0007400300c49150303111340340042582d0454000300240200102000c18981054007500301d06411500201106140039814441d83c51604541641c0500c56041c007001c0e0000c0400041b4035403409441420340320b0074049021141d5002c0074104820b40e074401c0c48410310310007085110b94119041249603149490b8441800d66031150070002c00c0d68040c803141c0c9030301300600d00380d001c16200c1d1200b00c080401e040740340c170b08224921100307407601034105400c01d03401d0001d0000d0640c0780f04024012010241 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 883283381 1250 883282131 883282159
    0xc1101080c090a1509050603040c0311130e0c01111f090503040e0403030504150c08070827060109051605070b090304180e0d0807120513020904080c0c0d020609040506 73
    0x7404041a4012650484c100c0e001a581c0c40d07200015001500040310503d01e581000d84030017102101d540805014001980a4101140d4607080030f5600300034030b07000a11015240407009a01c442c4019000d0f80815060a8050314803640483c0f090076801c06201c000032078041c5c2d00c501c00002c3c04010307402c8803d840100000708040f2411007100d03124030300c2540c001c215860b0a240c02c0704806483c0b400c884d00b1905194a00b10f003c1d400270010b0358002000d24210701c070350344c0c1c4041140c400070910850100720f04141402c4e40441401040950588003501010311643d110454558403c101d42c00e01c103000160140003850003e07030344c1c40446801c40d0440d0112400c058403240c010f03401851403001201405e503500e0341d29031121405d000501d0040d01c02d06042c401440e10b441e006e80801032030b10301003010039540d0000810000e400350400e10007a030040c24204c4c06240c01c0c0741052580d404442c10071010310030040c60000a03d4128001302030b00c1e9000e801c070f5003030a500209100c040d2401400382e9601001c5c05009071 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 883284631 1250 883283381 883283389
    0x80a0c020d26160f0201020702090402090615030a021b1c050f09150702040509070b040b070309170703032307060b03210a031107020604030f031e020c0a05010c1101080c09 75
    0x70f40120700c0c20000300428030000300c020b40a0038a48400500b507900600403a0050703520080d48551150301500d044c1c815a40321000200880003c1244042145000c4284a00100075a014182e1074500b40c4004a09107060aa40c6a0b00e0100e840000480e0b07900c4129004c0c424480c0014103d003071035070314581e400c00706a80000ac0c003407036240c0e02520b0382620115241307003585803900a0a40095900019112840c10f01d0321041440c42140500c03110050700086017000c2510803480d507001000020a40d84108650201c4992908594071069000540424124012040030800d1940c0300c3c41411a945c9404502d5035503101510b041081c00f64140116107800c900d002c1d041a12009003000c4801c00b07961508440ca002e0704543c0702444122082c00300744a40001a21f03a041254103a035089003000c0206003492404548050700d041035000c0d109003800300d4501454000070034041841040b81c0351140d4645031780044500c42110718024003028a1500b07054034650058a005070400c44515000f85804c0d4414045 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 883285881 1250 883284631 883284707
    0x10e180a05010c0e040f141524190f080402090709080f1c09060c1115040f14060903250506070c094212080901080a0c020d 54
    0x200c1c1c04a451403002e0980c03407070603114000d1380e00000307102000590083c1c034040c02d47d4030707006203030031422030000d00617202e01d0356085c01c1c42c403804140b001c6403515100c03000c04200254102e515900351344191280011030302800b41902c10300340f2a41e59144015030340c031a001c209602d44c01a180c40180643e404000ca42d40b6428403c3c10004c6404000504114110300c000707482c461071b503d619204115020310140011948030360040c078920340280800c481c07511520009040d00d080150402074001000178009400c040301009907007280e1031080100c810a803998140700c000c0c8101c81c14203606400000700801600f000303083c100300c0501c800c02c803502c0c0c0c3c5031200301240705540003a10a03034601007210740400c40030180b801132680c1e40680d44a0605688a6449500462000b52407603244d550100150031915030350b400c990074010810601c494014549900f85030b00c09901641070355001490901c00100c14851901a0340000c841c07550040c8040d40380785004503102c00020f4070a04040c0d42651100d00501810016 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 883287131 1250 883285881 883285901
    0x3050415050a090b07111002030405011b090911030c090d11030d050c19080f0c1006030f02011b050c060f1605010c081e0114061c0221010e180a0501 65
    0x2c0000c0f01c1c046802c0481d00010000c1684040088254801182d01004900c0300088507140b400581c42e51181d00d007040c0540f006a55014081080c86c003061b6101d035025900390f04403001610104070b054104d0a1401003840104c030080c490400401c600701640c201081d01a2416008036001904030007200002402c02d1014a00700c0300081000c6000f0501280a10111841e0807488030741080811840d504c9986a00034118500701d0b200c00890b002d05501c000b80701551003001041c401300281c0e030312468007400790b104485090b80002c01666560f032a10a844440318502e581100007880344800d442c08000301a407007840c204911034414051501d40156a060154001e4842c400209001183c001300401d044001445010520780d0048031103410b4803003020f00c50550b0343c00c20f90215856410000300c0c101c2e1040c46000c860142031041031700001704299025082804407442c4000021031783c00180d14248030213000d1b5205440324800400c0114a0311051139a113400781d001a10301180e071549034242114103c0740 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 883288381 1250 883287131 883287151
    0xc0609060e010819200306130618180c0e0f06100c1502091207060e1e0108040f02030604030906030507050a080112060b0d0b07120905060712110f190903050d0305041505 74
    0x2047c0506851320040c182c8025000703086c01c00c07000d45492030400885500314400c4030026500c0c0d81480081c3c90f0360304000d44981e000f0f02500f83d00e50362542c2065040380c0460390002c010f401200407404500e400281912a800d4a94480103504001e4481c120060034515040c00000c0e800c10180c0000d1f01d80d009540c4508000310040e26546e4504030001e4a0200d41c8135003940b041003110986004603100c58660007404000b031900401903920b42c0b900d16400c0c070700c50f0000b0b9410301c41c1400300020103a211961a068a4940d5400d100a4513280419a61400b0b00001c00c404100e2080c01404a00340c00305100b1030b55070140c4004070716000e211011500089643c0821ba80d95003200c420090b0450300105a07480c20040e960f010020814503458550b181d900140c0444104015200b034810002e049400002d40482d083e00010b558069140030f050740c80e401f40f8140d01960a00002c2c072500980203803181000c90760000003900303411400400032002404000c01c203c80620040300e070f4014181061081c0341c45204140 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 883289631 1250 883288381 883288387
    0x606171810110712030624020102072a0509070f0522291213050a060606020d02070504020f0f0f0d18060b0f010504150507020405040c0609060e01081920 67
    0x1040400c1c11360280b035042030901d070409204000c1040b007049070700c000102540d45074110300040d450403400f900c80c3d0080940a070301050061218520b990a07049041d0718800031680c080c030340d00c5042c04205442110340402003160400c0400c4500c0c0190028103140d008080044280a1645405c4404404c01e412103a210700401042e131844408010303041240b0301c3e40002c41030a042d81c0042d1041095801007060f0700a10582d0400300400c60200815078225500103c00c0c0001d58468400a40d1040c1c0400386000511927a400052141050300c22100c44480f0710061618000e400640420a54040300b210900c2e05820032403ca01300c450b81c440c441d40d101d0b440c0110722a101d0142020010f40325540c0900740b0503600141001d0b6140e812900700c50403201050303c1c0f0051001c500b2025101c6000c1d144010b50060700700740401080140101e5120300352203003900c90a6000e40c07507080494070048042e08081c0071400303070b201165107001000a2207101c441c8410001c00d0003101d0003006810b01954241c481c0c1c05280c04 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 883290881 1250 883289631 883289633
    0xa1a01050a260f0903181003181b0e16080612030705010c080c0a0c1502130306050403030c0503100303050f190905100e01020c04020c0106030b150406061718101107 72
    0x22003c03907000300c0058000c50406200c048103080d00c002c9802c01601c1054103441849003140207400548107845407200c209078898107810581c54030460541580e01000f0702e1540490b90081300d5204602a802010b0007a0880e074105100707603040040686501e91241c03004443c0d08000d6000c100401545101c1c02c000300d41964000c80190400002810109003400180424030b02194010075a940c81e9800c0b2404d0713000c103084a60302600a1199241d90721456428102c0841442015002240180d00c207580401115203c1081100d06000646008040895011080010a218001624100011014252505087e103c100043c0d0f2000030b14000412b4a03100d00f046a85080e1004518241e5181030103842c0e5009940002d4030b8400e000030040c4a190f0100e00d41ca2501402d6100201075580b2000b21251400c221501c482c004015200c51481a03040440100e0f80030b110b42c1c9511441040d20b00980e0b4542c60b2003004594110f0a40c904110920858001d641d0300000341c081c100c07071149441d8203143e4594031 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 883292131 1250 883290881 883290901
    0xe040501050d020603070e0f0307080601030b01060e031209031c1d04060810110f0703080a05011d0a0f091b060801093e03100e0a1a01050a26 62
    0x4164041d074440da600614100c050388960040700c1d40302100d80790500c0715018001c005001071041c85100c54052140c0a00481c941000041c0380e4140c034090700345020241c0e686d20040310203d01d40801d4540580064022001e09400c0c10301034114400018181e4404030b04004d0884025040844041c1c00103000700003416039198105401c5106001c02e64082c0400c5041c407051590b600c0c80c402d142ea021760341d034500c1c00c5002002c407c180d603040307040040410b40c0c8215a00380104072240c00c0e14401401c2c0c2c81d02c0000660315800c0740503a42d00e030f22000460540e41d82c900c04444020300303840051480813911481c20b1800203d400403400c1c09080624001050503090090091110b00160040030038545000c9600c5100120380d40000f49401c0100300c144603aa015602c4061728210580c80c0342c1d5010b0001c0f083c8182510324404140c141c40c54042d941d42c1d1960f0b0b40031740c0c50554495880a40c1082011840c03c00294442d2000b02803240580c1060780c0c40520b0505001e2140300c2c446401c40806003030009215107088 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 883293381 1250 883292131 883292141
    0xc010605150a121416090305031315030612080a44060306010308090a090e010501050114090a050105090d0203070306020c0607020d0203030c031005060d0c12200708070f030e04 77
    0x40c00070400c0080f8001c0c0c015408422102174801085209560304821001d4400d41042c000303941d00c8001c0c0c9440d00617030107028103690418020002001704841c0c0d25481381e0300c00c1c0700790002c56109240c0040c09100f2030311000c0760740d44901c1200081010860242d418902d0100b030060300080c20418042c0c0000c1c03081242101d00080e044502040e2150700b0174801995000103042c4d041d260010b41950ba41c9000c4000510a000c02c0d0344120201400d20303c18011040044d40268100c03002078882c81d285400380b10009c9502d00c100603078035030b00a01e86003040c0107651141c0d0140c02d6550000e844c604a141d0150002450100d095100b10b4010750002409101c0c0c802c2070042d190000d0071800145615141c40202030f449001c024014030801d400480082e1500a00500d03000045c80040c2030070780c0c0c82c0007408421003c0d0001e50389010202c2c40041103641200098410120310304003154002118444107101118503601c000310940d00408240711071004580c604180280545c4282c68407032141e1524070900054034 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 883294631 1250 883293381 883293407
    0x1203090510140d050c160c031101080702030d0c0201110408071e08070b0a02010b0d05030705070b180d060603051905010c0503040f0209090f1e010b0f0f060c010605150a 74
    0x40c040b04402a844090301950500000100c010545907500018030700d00b40034551301c0952252a2201c40d0f0180088141e2a60581e4007500304020000e103c4401510600010303218140140d03c100810025003100fa8001c00984040340f00101d440d0101000f258000d80040d00402c806820002c01049410494520b95907241a14102a03141e81d217451234803515600580b245407002c900001c2e00e550114803e51151a00c00801030000e44440b07403d08005982c0d13000100c00701c03154803521101040350120314044d5035035280840d42410200100c08240241e844071040201c59140e141c14020000031004d01c03c4040351001c224141c5190001d43c20f20707600307441c80d020b640d0050100410034403002c140e085901c004100d80607038020790a51a00605240780403c1441d464140c0d00500d081103a40c141c84100c0f03040d4500d2142c000f404410a241d041000e9268030181d65540700c01500f001408074100344015007418200c0304000a8907036500c0021a05502d03080003001c00810300050411070094001804c4030103a = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 883295881 1250 883294631 883294637
    0x40825030c0e100932090c0f04020c100203070f0507080703110c090702010f0f140a0e072304050a0b0d021c080712030605030303160807091203090510 66
    0xa146848076001201140a00311a107151040040c04802032040c00800402d007030314080003403404009004941040c0002040f042c105c13a0051010312018200441d402100c003000500100d0501c48100485180c4604e042600907070240010150023100344290545050006c0c0050707070b60710300004014200d0f0340442d0365001b400802d03c030820100d2411001ea44080f54107040c80901c1c60341c2d0068452900d0000c05806620101c03e000700546d561b41074100d000340c1d2120348814042101000145000c1c0d8905607140d021502c0701000140c1d141a01d43c006980402c81d0200361001c0395100e00118099480c00010041d00c446560464155030416100348c59115014a10401486602100103003e01580d040040c1c899030854a411b071140300d00c0c1101e42509640f041c0c4441c2e8800d09441d040642c0e00708120218082403074113200240d24280402124401c1c0191600035400b01b8500801355030940c0007600010400c818407101003042c2c01e00100034000240240c4421001a2a0804101c640c8020075070304010 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 883297131 1250 883295881 883295953
    0x30318031208040c09021c06051e2e02070e3702161115040317130e011706090c1503061311030709060201091a0403090b0408 55
    0x800c44040640000c10240d161a03402500d96007004e120200c1c40c0d4001c40c2c80a44001442c400118004800c02c0321010003080510680e0340e541d081211008040719010400040c006e40d281c0325141410860b03e0403240707141c2007200c2100d80c211070100c414241d40300b4005070380000000e105403601403d10592207203400c40342082d08000ca014400e141845110081e003007141003d443d2021380c885405860130342001d40c0c030002084016003010070320900d40c40c424a00466603c035025009000c4001140c082e00d402005280d00b000c90701144071b00c264000035030f0741008555140007007800a8095100e0b4001c004000464500c403506d1911507040c0900a0941c02c0a03070300211035019261140030302c4480303c554115115869a56060100e07208010b40400c440c1054074188030f443d40445020042c6000d880d46a07204094582c480c0c006a00300c80d0090f102400045401002c4241201c030aa10303542e0003031180c504042c9550791503d010080b40c0180c0c1000b001c40d00f00c0d88a5803a4011500b5003041e00000858580e45 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 883298381 1250 883297131 883297133
    0x603180304180f150b03041410270503160c050a2408070f230c070f14010e04020a02030d090818180a05090703050a15060905090c010e0d020d060603031803 68
    0xf50011310310a100359090040001350902500d10b42a50300c002420050780d80d251200a07404000745041c080c02c0309044ca50904681d100c845d40110b4480141d401001075151800108050f1102000d0b04002c4441c01050400429113499590340c54000f41059000c001c1c0d16980c0d030300c8109501d0345e040b401c0710800104c1810440b840303030b0101303503001080e08504100610b90092079a58108101c40d030341d140215900002c8200040c2f40c001045000c64140c4210800c2c8203880b120300c0216000d0345600ca42c0060985120700b1450b1030940d000700502d40395801100d08d032601d8039047e501510321400c03061368210008074002c00308242c2c3c5020f030302001504aa20242e4103130390a80c445556000500162100750b82c40d400500500c10030010f0314050341d040700031030707114072400d1802036802c0000711100040e8505020f400620304030307a80101405850101c0107094131902c8480111240f0360b402c1c005544c0043c1d85a098405605c403088120314290042c1c6000c2141e80c1141800380131150a6800c154901140c0c2c2d800708 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 883299631 1250 883298381 883298411
    0xc030e16050405070c0204090809010f0f09150e0904140c030109021f03111204150e190203210705120708040e0c0f030c090301060906140603180304180f 67
    0xc20745104803000552516404411200524007400094006291000710000d001015003e000f1804003644d40341c440d02480d2000301d443d201ca0210300004100c20b0501408020035104a9107925252440d06845040e41d5800043da040420307641507541001e1010b40300e20011080c004544408001d6000380010103d03030340404c2440d905202840c12004070203105452181c03094005803200d120764040a0307260030b040d420b00e404481d400d0b20101c98281042c03a1584d07108070395020344c14001146802401d41114440720941511151941c120f0307140c010600d0a034102100d82003074031030b0021110301c81da031101d070249082450540c140c50300c468440f106108aa0015180e0401c0700e042c1c40080710351020702d03102c0344510600c1d805500c007403680d00b5074003000700080c028040c1c2c0584200e842c01c40c000e105865840044104907440307402400e40d911402c0ca41781e541400c06000860f005804040741d040302001151084e03003141c01582220350401034200c0742400480e218001c0f0800c0c2016810208502500c915040e = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 883300881 1250 883299631 883299673
    0xa290909031e0f2b1407230903120c0d020c0105030402131d010204030611070206030c1b1b010e010903050715051605030705160e01030b0702030919050a0b03160e0d06020703030c030e 80
    0x1401590400300c80a4074002040c41079239075805016040700c801041200750b9a034150440c0e90604520310441ca40d02c902c0d6440020f0305511094184c5803103146032140e0b02444441010760075002c0c282c2d515841921502c2c2c0701008a40c03003240514000580311030a510313040060f522400000424900c00b48441009a50395504598000024442d07696841070000190b040c2070a54003d039642c2405450304c0e41000c080e40314015007842500341d803114803003420b01c0010346110b0402e00010741142d0040030184408a01074051f003c4412040c00d2003410030421121b20360402d8030011007150340b5000800c6100c2001401c0144041c2482a40c0144031303918180301c55104656014440545245810004100614000c0c001c46900c240080d0131102c0408910401081d514040d00c40c0c1800b502c098000010007011250549000d0b0f00c40d01d401ca02c2c030500800c4126030343c4040c3c8004a50145038001c1240005400744001c25025104e0340340440c05445002c4003904031203070702c205481a5007245115249001a007142 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 883302131 1250 883300881 883300907
    0x8070501030e07031203020403170a0f051e0c07090b09040f06020d230414190204050403020f3009010e01080a290909031e0f2b1407 58
    0x4002102c6500e0040140741180b280d00250a404002c03030009040c0341e141d002402500c1c00780c02c4d024610b0000d400107000c18070480c4c2440c0b00003864045282d40c1e0500ca203004107055014810b400303020a829030504403c1f40c0c07004c0551100c6900c2240d0801030400c0f54014060180d004039152603092034247c0310821001542c4100824142d400210b45011014650200503150180802c1d07000340c441200d450442d2560944045d07070038035050030000c0140c420004201000c0c084e0044260608484d503821b101c0074000240c801c809502a16074810003020082180c00710300180303030b00c000b015a00001e42c2120070040484852010510403c0702c4040c60f44c00c0840341805100a10300840c032aa503a6042000400c181c0240b22403003c441600e6020241c452805606261401c0f150400d00707485242c080c030369078425201d18824400c20707020414010454180940518407002c1b0140c0d180c24085008003100708964602c2000e01e07050380000000704902031041040100d510070511006051248000e8800301c10100 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 883303381 1250 883302131 883302137
    0x9010504030f081b0304060e150c180f1002030a170f1810060b09151204150b06032d010602030f0a1205010f17070b04060309030509030d11070f08070501 67
    0x4035013462890302c00d840b505242e9002ea640c40e803d2624041c00902940c1e05601541c0c4034140083c081442d000540740d0041d0f404114843c0390241c0003482c020302104003020254001d038551800d80e410740f0b8031000080f0650310b40c1e020f55581c000d55003002d45111458002d0701c5814403814100055860710303003155034112040004ca096090000c103001d43c50950303e00304c60140b850a0410010303500351000301070035000c4421070318810f40030408002c261b06806002d1900400c05981c4002c036000c20100f1502124150070400085010824000030a080da40107840d03491659610441a40200d810341440004900074090680025451310230020741e41c3c003030141c8011000b80c0c0000d8038100103001d400b1040a030100d04506000307560b950701c401c1c0c2d04220548181c0c08005242c9810b02c0742c2c60004a90709095612400006080504210049000f460007400c11018000c0402140c00141c0d401c008000030388055a540540342948480e203181000307145d500c02c0700c110300d4800c428000401c010981c502540d6081c6 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 883304631 1250 883303381 883303397
    0x3110709051b07140d02030a0f02010203091b0d060504050d030b040b012307020406090b091b040332010b190e1503121303051b0d06110d0c051209010504030f 69
    0x20401071380074030103400c4010042c414100c0f1101c1c0c2e940c001c40a071559442c140c0380c03041c0381485500168203030311007106d803404190000d11805034001d07100103002048035006086000f0022555990310700322007050714203540c1940840310078810543c1c54010314000c908141c50602c881510f010000e05a047c41c018a501000c54105046640e03d4140b4244d810b17070b54006106014003036503111000000e00024401034090790121001504446a203101d0014282c0c19500a6203480e141d611060b1110308110381600b41b01d40004913242070040c5e649410035115451100005080c1035a00410021440340200011548021042040070302600100e0960141e001c8501005048441000905000e16414950100c060106d89034112a42102511003904e105400700d407503e0789040000c07040000c001004036440328020b0800b00000301c680c0c000c541000c901025080c20088800000c0741620b100300103036400078030b0100b11006142c1171003103015040314080000700520b06294a00401d504051020102403100e10 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 883305881 1250 883304631 883304633
    0x906050609220f0f05060901050d21020a0c06120614150309030c03043b16021203070302120105040204050a06080403090e040c0905090601261903110709051b07 70
    0x141e0441140b041c0c500c1030400c107032011342254000406068132014084e696404c00801c1c5800c00c65a291595500070851070840303001710700201000c030342180c192411130062482d290000340c240307405900544a991a0a041641104407200c100c1d0040e5000e03000300da00c061740d06042d50302c5640c100103002406d601055030303039699520424650300c202d804e106010b01c800200003801c2c0c100d000c80303d4840141e4400c0c2c010440d00310040c0404d03010800c410003080d00d01c504046502850411440700c41030b009401a41d0000e01c0080c04421280c004840c144082500054290320304001d0b502c403d809003100b00c03000c6060a05140108030101ea00707001395002c0c03000000c0810280b50244000000900d20b42e001e2551614281ca4406818203441c8182421603082c40046100c112000c03a116060710700c0c42c42c04030b03c12442e0411000030010340027031000c600d006501c801c0d5001e00003c814030500b2070003515600703000307004c2c413082500d01303a05a400a078a840c40c0c4014800d04800005601d94010102c4030010f8461aa03 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 883307131 1250 883305881 883305949
    0x20a06030f1d030406080f0f0f060f130209040b1206012c191d0c061b01060e06100207060219020a0905130b090a020901030f050f030f040906050609 65
    0x4600c640c001102d84aa5403195088004000d005840c8181d83c0d582103038440101290302c440c010b4a2070350070819840000b03002002c4003c00c0643c0b040340141b002420422800c08501818100007005010540000f5164810b0601d0b002d801d00741b04041d036051041c3e43d40c80c610700b40c8582040c0198003c080c40b02c40141031030f40302a02da89441b82a81c5021801394204202507242c0c006002c09070807026800c00450036a8450051080380b0717070104a1000d441d10315424010005180d02c0b214070324a0028008804080c030311400d10400004e040140348418450a0031030801c05200c40c03550813030381158403600c0306004072680800d466010007a099074940390002d80d03100044143c550f6801074810280382204001c010701080c8003c0e0425409107101c0c800c1a260b41c1079264440c00d02e108069000600d0f140100002000c24407403070080c40c0224140e039440100d00b840541941e011260200392918007280078440b0401d01e00c40d28004120403551340e4035008612000c107001c51114000205051203403461213a801d41 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 883308381 1250 883307131 883307141
    0x2070905060d1b050102070f05100e011b051509060403090b0c15041a060303030c041707030c15090b09010c150e010c1d040c02031209160b0c1603020a06030f 69
    0x54050105183e070343d5480307105944400342d88102c40c01480f0b01c0b0700015182205211500a640c805000f82804100d00b1101792401702e003914145040207045101050302c103804940e148440e620030005022039103442c460380f2003074540141203020203802900c284070000790402c9582c422144685203051b211318400c00d00d1410802002008180c181c000400c0000304010b0701868001e99084100040c0c6503210102415502e02046801703030095141000180004904040c5000f88081e58404461410340c03240c1d2580701561995100034250400500c10a205a8001038900b02900d0480d0315541000380c10f100081c0715014102d40034007103200c800885004100c140d003152840c1c90200000784070054100038001d01d62038030b0090401b030181c64051000b00b40d140a0040004a941590040d0f0070440c1c03c1510070860040a4085045441280501c0c6280000c03d160b40c0010910500b03055121068070080a05040c40220004402600c4503000d0006035075004034403003a9541840c0000d0034010803880400201 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 883309631 1250 883308381 883308383
    0x910180b09180a061508100b0a091d010e0123040f0803040501090b070e240a1b0c060e090a05070807031d0111190807210f05040c060f09030302070905060d 68
    0x107040510301030720340301c3c5c401400c41110324400403181d440701240c028104403501c0440302c5030b00c402950410010341c02d080e003107401500b000915200740f04000d01041c1d801c450022440f09566516040c5000200342d100315000900f501c1050007001a180c5540c0e10440c4c00d14400c002081c100300400070400784130003540100b51496002d12400c08500306040050038000a030700440c3e20848012120701c0c00003100c401c4c0413128551160301a400e00c101740c5819608840010b0b2450481d041c0e555410000c100705040c07010003040c4903260501c9005582007400080c00000301392011060800c000d10030780f242c3c04642190303c030300e072440e00244030008250203409881800ca0750b40b00e25030808002c2958500103400400d03ca48060107446401c810301c1c01c2c10380300320700102d03200c00104408248881d40380c8849400d001e203402000c04009001c8000660030f100b101e030203030b405544000c00c80b00709112150b003080d114035810b9640d00342680307400e15546e4002d41c0c40d8098081c81c0c40300354a40c80403401c1601e440c2c0c01c2c40d03655 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 883310881 1250 883309631 883309643
    0xb07020d06110318070f030b011a0708040e0105090f01080307020108190e100e010c211b03050a1a030c0d0501060503120703020d0518040207050c0910180b09180a 71
    0xa0404200b0b108220003442c004640501460000046c0c44100b6041c00c401c80380d0190440210b607281142c01c4804004511789921036000c20080580001d20304001807001d00b480e030044403880c0d414201480b0400304d0027803c2103a00315140c1d0051051000000a40b802164240303003801e502e41d140d141403540682c0381d81c2c0c20210300c0d081000301c000d48071022030491200007000f40100070550300b00c40101e081e5180503407071502044040e01c120050817104c10710030031100c4c500b0300080703034046143c941d405030a03014902000c000b981d1070b003d116500559001d40c1c41e8072032100c07003114084c0303121900003602d0304404600b0f00d11070b183c282e01d88410081c00b03400800003080c0050649050050f0342030000800d80c8038400031001402040e103014501c50045083e2044032000021614441c50341105110003580528402d4900f4031071200c40310008d9075100300103486440d03600601002589018010070b19400390741102e0300141d007484414505500c85060b60744d400000c0014009144044888140c00c14801500282c07034 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 883312131 1250 883310881 883310887
    0x62a0601060c030315050d0201080a0e070b0304031206180216050a05150a05010f090c021005010902090f04202107020102030115051908060406081504030e0a0b07020d0611 75
    0x560340000c2c407040c40a0081c0c4091191545901000c0d07100c10303003402800d520518518541c00903502c9203001a0344054207581c001008102000400d141c138040381e00a080ca1400001004101036024040c172200d0100c0076018031003a418540442c0d02c44882e103040b501036540c045420002e0030351090321007601030b800c14280e0703410440da03007000317511040e0715001c68005d82030200101c0c2003541e29224140c1215080080c05903c40c0c00c202e0315402605ca00c8041d101184100b0400340c949038880c1c4150b40c001c0c0310240005a840880006020b07070003c1c0c0c0c2c04058030071803030041c0c0350344240c00c210519a450301031124000d55803400400303030580301280c60303c6e000e004c40700d003900300010346405600440c182c81441c40d450464101d144812102c0344034080210b01c00d01d80008400074001d005880c0300350401e600801c0440d0603901c5104e290314003003c280911a4900b00281803009041e0040303080d502008040d0360f0000343c00c8c18420814007034422034800a01a402c0071140c10140500360344010705041c100d03102c1540d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 883313381 1250 883312131 883312139
    0xf03160e070306150914011e080403090801020c0a11120610090b120316020109120804090c0509150306010302120f250905090c1e0a020c060405062a0601 67
    0x56140012070300c09022074500000840c000c0904131000c1000c05003030361880301050808072880d8458481030040c82c140100e250b014040c00400c0034080a0107081580c071b4424074a86420000c20348059a031081545900c10803002c4400800880c1c0342c4051900a8a0503c1d460141000300e8046101446010035034000c47c0148010070702d2001300081110302c914000e021503004031042003009500c441160889900400405090346001c01f4183c4030305005051900da401d0ba215003031002d0b230308810320456610b440020248404101031144a15208151a2031402d0010300c00c0811880d4914807044000842c0200018143e43c1c403940480c1c2004030244114826030034400c3e817101c0e890b4006c1d20420000500c3c224a901a1618054410380300e9425a40d011290b61038581840300202e4007801080101d141003154030752040e00c01c059100351407281d4800c0c076611030703281c03030002e041101c5104910b01c6004100010083e6036a4041078070611002d4100d018103c699022003110300c6028003928401600600000007 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 883314631 1250 883313381 883313399
    0x21213030215210117013c020c0a1a0402150711030703120815090114150705031e031009021b0d02010506040b01110d03020a020a050118030e03030304030e0f0316 71
    0x64100d5601c0c8125205e01440a036083d403c1c2c0724040011003061110b4101c024840c4000075010401024110004452a40340100f00307040e0390000d04408003503031040041004010f408100d05400c0c00345810064000d04140d80042c050441002c10228801c1000ca02c14050240e01080c01450b408001e080721216030752032400d482c0320902500381c40c002c5501c0c4000a4032016600d4030030511141c0080041e260703030f0700380103424241050001586402440380072410122606010040030031300d02070300046445070340302e1140d030720600612002c00700041c07000c3c024003240b0306c02440824241e40700c07440090f07103550f02c80702300c1884c8106100f042c500c64452000c0d41030b405501984003034000c031015602440210516001500c0c102e04080e0307500000d0b030005e006504680c5c480d0380a032001210b1441600c1200010741c5032103007500d40da038403c00c0c07140c5200c91846c010941c0020044074200b40c01d034013640c19450709031000b50900e03441030f0f074440c09610009083c41d01594144007503d0b40c60000780502c100652916a40 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 883315881 1250 883314631 883314697
    0x21801060f1d0102070512030d02070f05010b010203120a0c0c050d03063f08070c08030a0306170307141608071404060302311b021213030215 62
    0x1c4400304885260018030341030108100d08480b64107800400d00315280c03100344408180090290075039800107110b0341741240040e000800c0304038002d00007010050740f070341070a80c216424400d48a0566004101c11300b5000b1b00a02c88640c04140340c0c42c009034040030031a041d030b081c0d007900130b00618034007078004c40300d5409d0381503401b88060362131141c402c2a20790144401d6101c103502054141c83e82d4001c0782500c942001e407903410b422003e4841d42019081c41640e5555207000342007074205c01e00941000c603260b400183c1c58491940144062200c0500d10b21468090a8a030322a40002420f820400414840740180c2000021301d0600d201c00705800c0302e940d510506032036041901031846002d0a202c491400b504e807e008840541c1d40040c5099a280210941e110403600d01d01e00e148807070a51861801d010a01c1ca2207004400408000a840080c0d440d480007400e001e07528940c140b5140c81484060040702407215107506980e07060303034500c200284800c10000d242c02501e0310404501070348050100c04810724808 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 883317131 1250 883315881 883315907
    0x2120d090f0b0f060a060c0f0c0503010203100e06090606030402040903032d061a120a060504110901030c031406040b220603170c061918060b011b11010c02180106 71
    0x502045511404104166150305104503400105001e05010214070031245045808c6d104020b10030800b5a00e03004a0300766001103441d4040841001001c011440917070080640c40a81202d007944603107441c00c0020000e000240010340190b58403010841018001e0f400150342c0007002e801202040214039107004110382818003c0100e5040c1600080c000d948a8029a005c252481c0381a080030008061034600314002070110342010340703410000030b458807144200040303190000d8185550704030140016080c5c0d880c020304041010318150f00055240710b8503040a42040c02101c7c0400d003500075800240a07151081d510303031202d01c4040341c003506410113507200c00100e038410302510010200ca241c1307090f90380c003e8a4412030b95401c000e00007000e440031060300c64012a1282000100644080c0002e00030f44107441d0200d481c9540c0c0e80403210550380180c018280003041c401314418504199480548154441031300301e040c815050709200071551103d045000d20450545461410760f542c00004200103010a0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 883318381 1250 883317131 883317151
    0x80903032101080d030207080a052107030515030a0c05010e0d0b0a050603011b0219030c05061602100608030708030618130204050a05090a12050c12130801060602120d090f0b 76
    0xc01110700741c000d0096407c8941c101ea020b03810b105030000300341c41c01d501c0b10356580120002c040b0100300d11a0260312850040201d56030000f0b251505506030500640144c401a10a902440340c400009030103940714010303500d0078a802c40b1800d04d80300218030b280b40c00060040142a419041000d04c1d403050340f15601c9410101c0c020300291100207170540b0444072081800006800040c900c00c80500000e00d502c3e541403003450080302c8a0410f40b40c031401c242080d20340080d03501024500c90000782c0d04201032031102e440c1aa00b0030040b0b1516440942d00e119501004040c00310200c00501c10341c2c0ca5000c40540c099142c0290092480c1c0b42c0342c174403020b03600d90004910840c6040c002c00c100c01c0c214803601d44030300038400052460442c1a1501d01d0b4072000e41c40000b042120270040d4401d12202030040445078003580e88038503141d0b00420a01d200744142c681000115030b14081040001550014a4003500341c1c070700c6003c83d40c80c0d8030702000c1009003100d504041c04040783d6160380000c00c02041c0b0a184141020342c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 883319631 1250 883318381 883318393
    0xa02030105070c0209180a060c0309031829041205030301030605010b0421061b1805030604170f04051507021201110307050901020a050a050c120f030708090303210108 73
    0xa4000c0d103583d461040d0103074010400100145080003203030f41102d040106617003140c6403072580744c0d40c1c0c105864603009a607002949400b00c1c00c00b01904818800080e40e00d01d804400143d04000e1100c14400e41c4007200c801811041c003d02145411440498018046070021a201c6400754100142e80c1c1e4002c0c84102c446d030b442c0c0000012078801c1c07401600e0540c0c101401610321200c2c42c40601c032300c01e0b940e820140c6407159220602d911001500c00e41c00c0381d003e0541c41e1002c100090b6580e0000c1c00d442e5900c503a000784c10078401c000004840c040703240741a1010350305d002c0c1c99a202c00340d42c10b801d00403900410342200a800a107100c07484040003400d0207074400c0744c01000301a184c3d12803509940c400041c9074180706050010801b200d0103040940700714007042c4100c400d0782c000c949030240351074241041661190071041107000c80d82850020403110551040007440005481619a60740b4070034840701500401c00418143d17400da40500449101d071205c4103950b180c2010581c862255140d0070b2003540e80c648252 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 883320881 1250 883319631 883319641
    0xa03080f04180e030a0f020124050406060203071a101206020316020c01080a0b01030b040510060f05280504090e1609270212031809010e191109120a02030105 69
    0x1030049411043e03800d00554241400c0e184250781d100341d440f0141066548841200919100030001190003412080d80200c8031454281800115055900524210340080041401140d036048080e00c072208160f24441c0941c0c1c502c101d00406412641200000901128a03e021301095030081c40c06401050300c11500401e501a081c1d0f903429110120b50702080120700000e50807182a0301020078682c06040104020411400050807a00300303d803414024620302c030081c060281c3c400f8500e918140c0d2410f100b031030541ca86840b402c40c0c404002e04c8005050180795490042ca1041040e0740003040326010900808040203046600c0e100303801d960100c803600f80e01000482032003034054032014088030420500302c2c2c207040042203a21031060409a80280d800f100d01511480c00308024600c5200100c40030000034010020003c2584040c1d020500d9801c0d041c0c14800b5001c0540c020248001ca000e00c00901c070075400b442d00800d4000d804016911964030112400100f001042005200e07200310003c200c15a60 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 883322131 1250 883320881 883320929
    0x503150106080f090607080a18140709141504092f15040501030e011b09380702040e0f0708060a0510061d03030a0327200a03080f04 58
    0x11100044d240e80064045245030303003e03500c036540200321010003143c401601c100381448402c55445c126510282c0d62040d95110310113010940c050440e0034402d1100c81520524100348450103803407014444031000040001b6943d65010380f1072684d105000080d42c2070b00b50071807904212010b5460380440c00d2520b540000d850b040012109070490100080e003030501b0080110010041c09010741d174590768445288000221002030f07401040c4495079150304d200c7c108050103003588251410120704c400d4404950b03c644096254158500354401001c03a00d80550340006806040c15420b440d04d0b5001d80d5040e880e0b50300c0007103400d205540141003228030350344404054500b120000c4444c4400404450700c1408820702c1170826800c1d550343d01111424040d90840040e04591101c810800840c0d0b6501c0d0381c01ca0315080010a148000d07945c81d40900b902c00d9520303407c10b42300d8000070014040c541c4440f040c80c04c2c2c0d60414414003541d0804541e81d00c90200580c00615503200c0d00551034160518011028040300d = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 883323381 1250 883322131 883322161
    0x60f1b020c0a0603090309050607060e0f011a0d08091f022802011103041d270d081b0c060f160504090c030e192f060c07050315010608 59
    0x1c405004500000e1920320100d000702001c00e4214100845513500040640d204801390440030f0044000207412895101410315090310514a075030039906041ca10350000c046032580c204e01c1002503c152380118a2842c0000c55071144404072540507a1459a56200d10794403c1114592802602120700c0d0003142121420040d0304c080240051400b0b480d114401075204607030f004104203c407021a4101a141e00c0215900035441654400c021404010010341c40c40e4990714900c01e0265201100310210303411411501d4400f0500d64405000e0500003003400580c0301c04025005129113070382c02da22405403450441c2c80d4102a6004446007a05202080829901c101c0d40a00c00d04241c480b245058070b45020300c801b034202035125605040d5110f2204c1070060003881036000c51241002c0c91107840c0c03010f184c100c1001141040b0a41404880300c11441c4080760030540402c200e500300e4055844140da2274000b072900c0303070031380119806004803403820300030404071001a8107a821946950305a90344200c0c090040039 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 883324631 1250 883323381 883323403
    0xd0809060c1824030124080405030a0311040504060e0406110f180307030b0f040312020f0904150b0a110f03091023030c070302060a0b0609100c060f1b02 67
    0xc0c032500942202c07807614028a200c681110505004005011242c0c80016007003640500d180743d803000d00717840c001c030821010301a22102e0760a1021a509103511076a9490040032160002d00d940d51000740300001d0342d0341c1650700411740104240b04181d1244c42e082c45070348055504035011400c0071041c600041c003078029207140aa60184003800c05c0c0500c540c800c015a0011011605030060346070110100e40d8400142c2c4c0300310f40440029000c0c4c14035190080100100049007a00240f050000c102403200300011601c1d20340c0100c80c0421441824044644400b005038030184244e80005429601e541d00f0002000700b8031000400c0e55002070a034602d040d1281700f40308445030321903010404550b480d406410042c085050b408010086c0456102400045900a44400840e00004541e0340101031b41007140c030b03601c000500c40c1440742c5014580860300500031011070a1156800b0103018003031500c541070444401e0707044002880034480001d80c00009005400042284009d084039000c845c6000044c00003200d = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 883325881 1250 883324631 883324657
    0xa02030906160f24050405060106050d14010e040c0819080d0f0c030b0f120d051c0c050d0501120201120203070207051801090612030903031805030d0809060c 69
    0x142800c42041640c0c0e22080d0400102076020a40384081108a0610124144511030381d5485010f80c011a00316021002a00c0301c40700d00f01420040011004600700d81100d0003410420746031810400340d440900360350b0101c1e2840b081010000a42e02c00c1843c015401b0b079000d06040c000068451003030a0f00e80c1c48179400654240380d030705002400241c25500800509420030000212140515064810b0729410020a400280c84482c004010300d400b00d004001039108482850400f404030200b07688885a506220041c84030210340201c41d40d5554030902c01c00707401da42d81081800312198004d4003e410004a00704c0c500c1c6440d0010030710b403003e05d03004102150140c5402c4a400d003250150b0010f175000410000440c05081170008458450b00d00c0c514034100e101c06045e0b080c2d814010010300302c40280e032242d104402281c00302e5020917084500c41c400d0325003524003140f401403611080484030555920541d01840b50340c0f15040300f6940010b5007401998148241e602a03154400009182e0041000075152 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 883327131 1250 883325881 883325887
    0x703080301060c02060c011b110c0d08030a140702070608070503070c1b080304090204050f01030219050a0207170a060e061612090c080313050d0b07031a1011010f020a0203 75
    0x107643c010140440b92610080c103961420304110340c1030b401c1d02d000c40304222070340c3c2100340c540520603000325820800d04482002081c800c005138000494000d5040d101910100b80000030034040c00164203c42000a00304603c40c01d28101240000e40d01d0320284502d100240b04040440e400f18840d9044a008844030744c0c8070041c05242e510344082d900c4601e041c1700c8040800c00c200107051f0405201030402400140401030b00c90340713003030244494414009400350426104100c400c0e03038086500c81c503850b08520b0303251682e1105c0003100141e1900050390480720244044202c0240304050000d01040d04c1c0348101014817004013000c100307996071032055856628591105450512540c41035a4018415490794004034160200340c503802e01da0b4403540c00854058000140740705c04803115110000080c02d00742d80d032400e0710110743c40d0541844405452032040584a40360454100d1841d2100c1c0e01400c1d00800c1200403206245001d0028003d9080b000115420705403502200b550318400d48095001c0c1da0041c500d = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 883328381 1250 883327131 883327139
    0x105060901090306050c071103070509011a0c12031909150228090e070e090c0d0b120d170c0304141204090c0e060c070303030509010227010f020703080301 68
    0x105030001900300703041014080c400408501107005450191840c00d02c21070751389003c3d04040400003031462950340203034000401008107454201840c5d0441c1c800b03450150f07984034070141c81c5100348680c0c25001c08500c6141110351450100000460140c0a417001030035030400080b441e0420b032616188043c0103032020000001d05444a60010511303e01d00b0029500c4c03c1e00440b4208440007072007007041000504041d8140301003204141c0c8660859240c1c104030f020442e204c03002880001d0000c09411404002007150300001d24580c00036400500010940c1326000100180907984010070b1811100060308020034001103001d005078640900b00c14850649566035548980e0b00e030440c0b802840c3c0c000d10520760219020500c2c44050400b40402040c04140c0c1403a41c003006054595510310035100362030800884224900004042e400c0380da06080c041001e554031594940240204011080d10800c20701c070032010f009820860300c09146098071401c40a4101c41400c99a030071440c0002072604c2030400c0144 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 883329631 1250 883328381 883328389
    0x1050d03090b0c1009050c090f010f03170d090605160504080c0904020d0f0c2301050a080721091e0c030611041d0f0a020c0714060c0f1c030b090105 65
    0x2d80f42c070041c01200ca00158540c410703000c403403c998080c1d845401c05070502e0103e10b0001501904402010fa950b04154141700c5217419038861440700901102e40c1000c00203012490324159104000009010803000d00d8504044002d07007400c440108850b4024911700650034002c0064a01340c0f96684002d001a448000500480e1035018106a03801014001c008002404060300012441d1040300103020b1309107890b0080c0c0300d840c1c00202c00102c0e1544410b82e070815990200545200d003009242c51862070701d50640030340f2040c61498450310000001c528420025005e6001000d685115842c0c8050204e070400e0f51101d0708040000040440d81ca80504001144054010040f82201880907034a029504c0d050007041d40300803078041c203049040104001000c00c001217104d902c040d03d07001c15450059074620f101e480d000207000f00d0045a109204c080d50640b40c02041d43c000c1510141110594806101074903a5042201404544228508036851400e0b10a0040381c05103e000741101c52142d00b07240c200 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 883330881 1250 883329631 883329637
    0x5012912010f240603060b071511040906050307080102040506070b07030e10141803032a0d022203080a05030a1b0e0a1710020a0c0b04061401050d03090b 67
    0x1a80641d9290b030142014040c85118406140f01c1c81403941c1d0034030298250101e003c00c4030364400800d26280c044100140001a02110300030742d4030402800410102c00e0040000300076281e4401c50701d1a01080c00709440300a81e019805640f8203c0854004680e0f0381c110900b030f4400c80c00b40c1034200f2414072000d40004c04c0e07151004d40080440c00d01044604064034000c4c40c0641030a40720901680301c1c003080f0302081c134455a154000c545100f200036001d00000c2c9540d660301c40a40030301ca4041000c0000c0b10180d00085003007089600441c9050340d600e61880803000130350811409081c000b880e0340746c0e20145400801200044952103a1000c0c00d02c11900000c2d22650001000b446c015a1680c45280d00c010342601c1600d0300d454142c45110200045500380018502d0729000b00c00103045440c00c508180c580010b4008071040d2040015981d1441e44104450340303070513404002c1c403001e4400c09200c00c0200680041505810304518010340781c2c0d0311000c00401d91728409024000c100c0011040c0282c040403001 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 883332131 1250 883330881 883330909
    0x1091113050d0c08060c03180d200a0c2301080403020a06090606030609050f010c030e15070e03030a1d04060608190b030703050c10020304360507050304050129 70
    0x64110f096030398038442824400304070780000c591a400010080c4c40c581c1c40e454081d40c88a180002c095180c0440c001401071a030346480712200c006401d03009240500d04015448585502042c003141507551b0703100140406a1409024030b40a0a0090f414141d520660985105a4041d802050114103039102c190090018000030359440da126079011010503054000c1784416440340b4000e2a80800c800310a42c00c5498450702201090308114032250f2100001504a0b42030228040a08103601c0f440400e4901c107046110440d01400046950025180c003d14125201c8001005060038511100d0400045841c98080c0c100400d002c0008aa00303a10303002d11041750399200e1100062005009030001c2c0c0f030001c1981c0203c40340e612241d6903000c1030805c01c1808948500d90b00085040c14140348034813000b01072252441022601d28011408415040407202001d2001990100458104043c00030042e510480303060300e0b00c0d070074981a038074400c440e0074901d1300508107060100142c40980d070400c0484000390306 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 883333381 1250 883332131 883332143
    0x80a180b1b0f0f300f0c12030106090905090a17030115020607080408030619170c040207170c010b0d03030b012705040b041401060806090f01050901050d0303020705010504050601091113050d 83
    0x41240034803000f80004002c02c404075800c89407074946c0d03480603620b04007a19500e640c041c0e50a01c010031100f50880402800e6482160000c165a500c44516501e8940740c0134014221504040007054200d00070b60085041c0c9518041c5410240d40c501c0041c1d940d03110a617409070000300d0403000100407511a402440e08440002c0490003038038550b02e0042c011840c2038003c02142c8504102c400c0041204210012107c5001c0da02503040c85229102e030b4195250407200009401d5000400302c84030b280c2907000403407600c0002c00c14482c500640c1030060040601c624801d0110300c1010f40c1028041d60b0b00c1c10425030b609119101680a8108400e000c007600071545001d4100782c58210340d90190420441060180c0100c0d900c881c500e00e0010100640500c01900004408800800501c8507031210955541598016900c28484051510b1304900a1080b0f100c0034049518190a00040002c041035860480b1050034045c171a07520b98000c2c0141ca031040212003004104506000c01650a100906417a42030242c0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 883334631 1250 883333381 883333453
    0x70b090102180d210809010b0d050c0f18040c030311010509070302011d030618010c0908062413050103060b0f03151308031302040606050403080a180b1b0f0f 69
    0x900510b0324004c02c4800004180d50604021000c02d00340f103100d807440400c4a11304100503031384d220341c0e48890715811864011847ca60710064991210b2818003020390b01070507071071841c0c41d040c2028000345004d404200c00280e01c0340c41c0c0519114050181600071304030600500000d070300c2d680c0113480b44903452005023807800303501941199071f95003030080620076803130010311034001000c5035131003801c450f181d10300001400506642031000300e0001130303031a50100c2d01544104000c1d00d0300d8a0340514002401c191580064030216010250b40c0350741000c0e0403a88102d40c180912441902000341c48100c6001d031903003680c404442645020b03400400a038102c1140070a802c205880d0340c55203242c940c802c9a400101e01c0c1c020403030804504003803043c00002e2540c4e140c828201401c0d966851030314828030251104000441300c1845c0d8016031900c0304001000700c02d0540f50b0f04c030700c2e901004511720300d40700003889140104541c1000120012840e003525488810250548400d803100000805041c85150042c03a2206 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 883335881 1250 883334631 883334663
    0x315030705060f07021c20031002210709050303160609061b0807140f071a0a0906060906030b180312070e040f1b03200708070b090102180d 61
    0x510000c221409031404651380e0740005005004001d00001c442c0c1d480c0506600000c0c01240a040980c07044040c060008902e42c2c5900340040c0c40c00018110409081e403000031500071946041c409400810825965910036aa036107c040c2c8a000c803c0c441c3d640c0541040080101011440c00f0f1006847c0c0f01d00000074007002d103038613108122032141c0c200c0440070a4124420100c80d4118410700d42c000102d14100c15000d0300079a1203d4503000300d1060b800054000f0078524200049c0d0700c0400c2c9452040f110502562804000c1c00700071385072405082c0c80c424503010021509210754007511080c7c0f40c0103920349006850b0071520085912480309041407500041c4111702c051a85d4030003040c002c03e41940c40801c0014a01c04000403250101c540c0140c1c2840c01400160105840149040304040740c00c001900340c450703458502c0c4060b0304040c404402d4800145020802c403001d00039060182c0202040c0b5511b543c0c0010f00f034201d00ca4101103068030107450388020b24615201e0400000148250030b858030450076 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 883337131 1250 883335881 883335889
    0x703050c0d03141303050f0325022101060f0f05100f05041e0e0609101e0918030201140c09040b0f12011b0306030803010504020c0f060406090c0501140315030705 71
    0xc2000a004c4000d12400300300207000003000344080c101000c102440c03034121000038002c84041c8141180c0302c1c5401d221040c205641e102400c0585e01420070198001154416006071700914450041079840300c104100810b003080c84030301c440c096990140c00c644200c0041c3c241610301e0851006044104241000040340032110506524298440c556840703000c1c03402e010b44d0001180008018900600c0761354100308101200b900d143d412101e508210020b04050301900280c0040d554200700351301c80c2005429580f4a60440050240074020390007009140c11135054241040401d444444d80d40b80d0a1005e1211447c00e070b44020915800100566030f007442c03d401040b0345080821001200d655514198621111400c50640384500d0303030700c0c1c104212421550b4203112404180a100d0040e5408124105400c40800c02104d022000408481461a02d45440c001074480c3d250308441144841000103904c1d4040d1800e49031a1911000050031070707131649284e000e43d100c6408440d1307061042c200001400c0e11 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 883338381 1250 883337131 883337137
    0x71401150e0105090f2a0904020a0c0c0f0b12070c12030f0e01060506070b04140118060c03021c0c0c0b1509060d080708071b060915020703050c0d0314 66
    0x800d94075081190300d02030800441d414020200821a140441000b061005000d02d80901c0c8441c0b44c02c1201c8003507061940b00c030034041e1601064110b07100013190081180c200b4014a03800b84a9506640c805460703000c00200c006840c844c200a02074203010400c13109400c500100ea0101092812010700303103590319400200028912a00082a52101c01c00c1340d44001d030281848440f10040240036007460800070136000d00c55041c024200c030790128046001c1140d1864290810407101c00240b01c0031151205952541081311000c440c1c41e85003200404001b8021f0081d92008200e084030031a10b20500d0700341a001e404c5000070007080080e005401000a000c00c12424020740346402c00344211401c81c014080045000b0b85040e120b00300da02031600000d007a5500f04ca207680c0d40981c402d62034000e80d103001c201021285080c01010817203404003190003980202c209085440348a00a0403031071200701c0503622490b1502028200c3e403c103c44162081c2400407840a40782e100b8030b8910174645101003600d007036070 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 883339631 1250 883338381 883338389
    0x203010b0a021603081905131409070c0201140a03020c3408030307050c070f0602030909061002253c0f0e070c0506180609070b07140115 60
    0x80008038070411640d604000c50324600740c503000550f841500319290b411544c002d49603480f0261a015400900d500e10500036a8145001e01151824082c1c6400780d4900d042542c4004038041c40c0500c0001c0c0010b0322600c11458140d4040e107032182c00109004040c1100d0b40010792810074107030200410548071000704003040c11100090064520016206909010380016048501e01a100c012003400310b84408411240c202d400c50a000d9920004221a5803c2144660180045080c0703041e00003071943d000310083c81e0801d82121200c00f19607445040082c0800344406420060b0700001c0101e0040d818001000d03030340c1009122103006680d85240000110b21010710240c08810007561400d0440d08242030400200e44900b012602503003000e1400522014a12a071200c2403032030004100356502983e68030b2102d60700042900c80c18580314072400541c02c02c1000304800d602ca80000100440800714802050707603501d04030b81d403620101341c07600e03c4181d001d414020b0306c5540c1c030f28000900d1554140014010 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 883340881 1250 883339631 883339649
    0x2102070f0818011202040311210f0c01030612031d280e0f071b11061b060c0406050a0815120d021603030e090a141014040905030304020111030c01020301 67
    0x5005100001096100c201c19044d0640e03006100900002d442010140540c0c40c0503500042c692100415104407500401e8a0750000d004281440d00d0004c00401c10710300444080c0c0b8280000c0d580d032100c5a003068a0000007600146801100358036009960f002d81e401c03850000c00d0110031030301065443e0000a900f5410380740e50319803004108105200d0384a82c0b07501103000b4140340e2040c1350510b1302401d494410366030f00302803003680d50f07400e02003184d220040b2941e2000980280c0d04c900c1d01ca001c2d0402014410001000c6109240019040491160458094403140d58885042402030300003a2200034010380362045140c9480940d00c0b1a855198000f61311010301002440c041500c0000607040c0602031231070140c100348100e030a1000c01c0d01301e25503040300c03031040c3e503561140c3d41e800d0030290007058030942e049000c01200e0140003020300084018419079140c82201c440c0c0440e6442007000b2a80c2c3c24100514507002840000c01542c0580c502c0100101d5001c00d4a281c0701d040842e00c0c0c2240d209030020750f04 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 883342131 1250 883340881 883340917
    0x8040309080d0f0e060703080f180615010e030f03182202130608010b0301122a090b0d0c03020d02010c051f0b0f0a1505040f0909020f012102070f08 65
    0x707103d40c0400981144d84c01560264548440744c1c40041201200600e8101c0d450806404078118102c2c1305902c90700010b100056171805d0804d402800391720769020b4501c1e40010180d030401d100360302c0c0c007081003106460403400a6103000b12070030040c50788841492002d41d00c10f07507941e2600b041040030814810054040680143d44004040c0d12840580064202c04100000f403030050002803450f10403241555041450210520014505103a8800c1c070064158000c88140d02070380f500c0d1011644490944541c039200380f00d601103910501100c0d000b8044050b103450b0b5103030010405410301c0110a00a10700601d4240c42c81841500c07550316003002d442c041c94090695505c1c6d8042201c0601c10b44042403800c80300044180321007400992410524061a19034500664404156601810840e0010801d100c0179007601681c0f503007010000c01c00400141d000d260b4031000414150f1059803010f08242c5100220303500d0b041442c241200035000b460701220403038181302c5480301044038000a00704040781c1d00c1082c80 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 883343381 1250 883342131 883342157
    0xe04022d0d0e10061d060118031406060307060e03030403080a02160e040510060b071b1a030f0108030c30030f0a0b040e0a0b060a0512060a0c0c0b010608040309080d 72
    0x402c54001c1da0002c00700c210007a410582c0d130882c01c0c5885c1d42040003443c007900000323225100540300d20b4080d84010a90a685180940780c4080400d581e4403e4000720161074034180d440c042030b14200040001960315400c208414400a00140045d0040514510480703200001914140d01244c0c4d1540120030403903184400c00c000c1003820040900e2504424105009061415030410300034001c07004024150030180350740c041c54403004192603000380f44480c0c5002900051076801441d90f0b2040c0c5a888240c403002e0001b29443d0800402c4918079006240100801c012180303000d40000ca070720942c0c0181d14040078081c2c018090324800345000720074460a000b5103040c81c0a0790421104e165100a02035800c01003160600350002c0354801c081c9400c000456182d5032080001581c0003902d4000552041500002c4414080b000501510411882100700014020300b201030318406c110034001403610808800500c00701d403040c000540c00500c00c1c14801c444035180d203841c50400c103211002c0000130307a000074966 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 883344631 1250 883343381 883343413
    0xc070e13140307080a05090f030318120703120807051e0c0d020c01080c0715050a02130e060d0303020d02090a0603020319180320010606030603030e04022d0d0e 70
    0xa07a801481c84000d40c581055603a072008a801030000c0700c03080c804040742600c3c40d51103213040e40310503600003000d480e03070780c01200011000d03000f010407414024000c191145041040024050f002c0d20b0b00500019650102110119200d00009240c00c00704036040c80315104030400710708410324695814a040351601d101960036450700150a42c3c0004550002100d289903036040050a50810140d420480c1e03551452304042c80c2542000d030710451164500410800070881c0c0b0b030301030442c0540220ba0608502e5403218140d069090030703500554400c0c0f0f03c940d5500040d0090f03000f82080300340380c1b6001d8108000080000c5e0741c555203038171590210381c000040200d8510000039a0380d4110043d08104001914160003082065001000a091050301c00310004182d40700c0c01c0c0c208220f40e81ca8001e202017516004010003814180c4000c07000306d0016070b558900d038038240c0240c6a841c0200d58040d040c8002d010460001506001003944c0c801d00b04001c03040e4010703410f0007209505081d1100801c81001080a40 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 883345881 1250 883344631 883344653
    0x1060807030c0509280302090f090106060903082508070c030c0510090b0d02040513020a020622060519140f0105120a110109090903020a1b0f06050c070e13 68
    0x316040007030401201c0490ba403651600c00c40c000c000801520000840e41041401203c00c1d000a9404a424410001c40480c27400340e0502c9145003070002c1c840c0340c0e41d0750f6003a80c0c00c41080c0402000c260050208190b19641c40d80000340000024003102c010100b10f0300c40c032850341d0000341d050396000001d100c140184101c0c6034039080202415078559408003000c02e0014400300d440c1c0201d00801d2000902c02d40750140e00d406403805880000c04d5034490740c481d81003040095220300c150002600444002416422000c10001d615600d81e120f5000c0d800c3d10342c0d41c4c220003010010203001c12a06041c03800c20078003e4034894984080da41001c41c503154184010a10b04915050388018820880745032482141d20020601008140c1e11002e08102c102000f0010303079026910350046042c440c9801030900038140e001408981d624001c0390307915410820141c111001c8480c6020f8100c00303000320754041000300c0c40345000b41810100003042d01d46003500c03203e03856030960040e5130440c5500c4d213138000c0c001402038880c08 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 883347131 1250 883345881 883345901
    0xe07021c0e0a0302041e020f04030308060f010e220c030b1f0504061407060f140f0103320106060e030d08010807061d220e120d0518060106080703 64
    0x4005203001da0002040021540070090040303440300e2048030074a0781020b407046034a03103101c401d545030b03003010301501d5481d04107200550000e03452201103601c5041101d042011050103940d001001c19110b0240302c018403451131503038038001413000c805066407030b01c0c8243d207440501c5d50b401003034200191007040706119040002d8020000d00a0301204055007080c1150204c1d84141402c035a808089202000a802200c0c005042d050422096040d0f0b002554003032a82207544210038911a04e80089140040c0b009000003400000c501e002000856801505141c40125000110400d005400e807003500b5160540d03c11000b02d5292094100d0314641401003040c42000c900d03010f0440c2d89042482641c507103c500ca044140a500744103c0300c0d801e4040c01c44a8102d40140948201200d1460005184041140100e280038074040e8880c08107000400c5082219603245510380c2868009092000146000f81441e80d0400040c035003201176000c240400d500800f66512202490310340a00b001d82622034400d8 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 883348381 1250 883347131 883347137
    0x60601050a1806121a090406090201090b030f040606060c050c060c030d06030605101a041a040801021801020c0303040503060a050604090f08040e0a0605180405012301050f090c040b030c040e07021c 86
    0x205546285c403000c6d51346602603007048000c102441107000603650310640741c012a81800001080012009880105034041c0e881840704208440d07407410304503180100380307200501d2a0070500b010309492510502810705120100300743c1e8a02408510b10108031103d55000715005501c0c7d100700805059000e5580b4000c0100103010403015400c5400345c0d07824450350044205041580072400c08140c0c0070019100600302d050000c640c0ca05050407041d03940380c20b446d41e4038010301c2004c1510b51682808400e40b8110741005e40100015101c86100b1005040020300c12a042555000420089450300d217000f13220a000788040c690b56400d0100e4038103072640041004240f41d003030800030042a241d01811a04c101030700c0c1d151381d40c0340c0c9a500e020341c090814074100344000c0149142a101c19010a10361a0483c0c4c021654040915070394403d21400b00c2d01221128580c180500c02049404003480065a1107101d00704030394503141e1a64101704c641c240580b81000140d10031202203020000c031440560044030242 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 883349631 1250 883348381 883348421
    0x609040b0a0b1c02131815180506150109180f11070b011e1a07020310020409140907080303071821030e0a0b041a1603050309100e060601050a180612 65
    0x42c0310a0b0306068503c90050081c20369a000703984407640c03540f02c940740e2001d0032003000c4a0008c07070510707507070314441a51900d640c03039250301e00d003041903015042c1c4804440441c4a200f0300d030109a041c100051003410b110745500d0b9124442e00200310390600040c400b0070712603010565954101450050404511004001c2e40001c0940603c030b0610306801c0e066000340000180740d0f41c0c85443c808241003510303040074080240d002140102e80d41c0016040307030340f5409502240a8a40daa8082804c0d0780e0301c4540328200740c0b17400c01c01c017040840c4d11039178a909003010901b541d10101e41e5111101a404511078101d00d10020714503504504242d488290030902c4142100d03280142810014110021702c40c03031246000511000011070380380f204030401d03115103108140802240604a00700036001d544111118641070044824094205400d880b860803209200c100500c616680c0380010749807540028948800d00107082d848403281120b9440c4040035001d15900c442445210141e1042030740c541d03428001d8481d142c1 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 883350881 1250 883349631 883349651
    0x5040209150d051501150c05031602010e1f030b0105070f03080c130305060a0612050d050a2c030d09080604030c0327080d05040b250b09030c10050609040b0a0b1c0213 73
    0xa6540d0100c440000ae0640c0c4110f100503241c40c0c101c0c5246e190401d001548202e2051503803800022000c04584043c0071001e0020011603c1c2d210380c00e4014440c0030280c8001000c02d1282905542c4102d1542019203411320004a12028801d25442183c09603c020200300c214029070144000400110700115450000303541c03650345607500310b41c1345003c1200c00b040f85145180b240e544500d64810540b0422410b0320711880c030404200085502600912600e1400c1d0490381c4a081d10034111100d100207082c0588403aa400c0341d54000c00001503042108140030304940c0e09008035002d00a107d2035580e031030050b241c4403000c0d0502e076040d2807980034044240401c01501e5444400c851030400840c910055944403211060b104c0010400064400c02c421420044145400001812944204000c54500a0140c408a0705039001101c107141c0014981d408280000c000101d040d40240c0c240c00301043c0d14100b003002c80c076188264078031138034984844164041941040c03030038500305215141c02400348202c0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 883352131 1250 883350881 883350883
    0x5130e16080d080c0d0903050c07050f06030705030601051b0f060c031909080705060403090609120c23030f030a1412071112042705040209150d051501150c05 69
    0xc030b0030400500c0070840004904240d407a0444022140c1d013001006110414100104250007400c0300e581307103100e4541c01042c0b40c17400c0c10001083c1100140785a1641d40d427014122030503000540103905001d000c0c0083e000344058100010704044440b0001e00c0440b141d1400285001006804e0003003442d03040041c0581c803403038a1005800120700d0240811140c5462800780520f100302440504107000e2642031004159011040104a071055070300c90311102d440300d45503075410b03c0600004207003a0800340100300305088243e0302c2c8a26256092240e41541018000c0390402c034034038142c0f1a03160000a1554200e0350003482010b42c14200040c42402d2400c1020909640032010740007901303010403419024801c18080000100159110600b00c2d1995541e80300903807040d85400c004000c0760300c0110300e0385400d02d031403068501c10b0b9001803220341c6035203e19504100e9030100480c42900003050014100100700200401035601000d954106115031409d01845030384098040c2c443c0070401c480d5803617804100 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 883353381 1250 883352131 883352143
    0x1080f04020337031e021b0d1e290405061b0d0c081b03070807050d0f050408180102151b0405030d1806031814030405130e1608 56
    0x229440b62010108080d54691000c0c1c0300380000f0b803659000110030000c05034440c00456800c50081c08040c440400d0400990302c540da1030740c40d40108035182c900e9401500d800290250300302d00640c10411070302c092403010740c04004040801d0b07a800c400c0392000326080e250700c1c01000104504621042e03480c10143e440e580c4070840903000000e49620100b01d80f2420b654101110764050b00c082c000c1040702000f120190152108441d02d1034200008484c0009d414081400c130ac0c0325180c0c0c0d5448100c83e50714540140c403a5000ba05020641903138882840c8004034652041900440c050340040e92030306031160f140c903048602605030a0440d000b04c4198454154503003242504401200c01c111010440c5c03200060b45c9000e981e021a50610911062011041c0c00103c08910b01181600381250503856103400da05807140225523013900314070088508081100c8554108411000760140c03464195070740b0015100c400d2442c90055000c1e40c0c0e0340410b9184000f00107036441e04105042e50000349140041841e2224 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 883354631 1250 883353381 883353403
    0x90f030b010311040213080115060c03020c0114090d0308150402040e0a050903070b0153010221100603061802030901110f041809021c0305040b1801080f040203 70
    0x50f800d921840002c0d0740316010307a0002000042e420315466078403c0c02c40d02038014000010b2100d5040040031816070322070703803105400e02d070140c0080144032011801158203040e00035030017034441028400c41901d80d440a030f40d00304c014007030350f030310003040c204084800d00712080802214800c500c1040304010342d050383c0039032592144a008001859543c0d0f244414294801c2c0c100c020090a4a000045400799420a0b18101d00d1200000d01842480441c030803d845000395400941e07141703d1a10110344000c81d00c0100051100b075100250606c0c00c0c01a610340604041d5004031103c1110000b003041c0700001145c1d110042c14203281c1404100c0c548000b0214171103d409510900744d4001001030303403821007504000d00d411380e004581a0348040810807180303a60000d0040c08100d070000308402406100030300400105540041c0300d2108400300c14030410781caa21704101101841000e0000240c0c9810303040180400e24100081c41a04c4000d020004042c081c008041d003950a0b4203034188130242c0c6000544010038 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 883355881 1250 883354631 883354643
    0x8091605010f12020a0f0806240c0106090c031e06061b020402071a100e041e030908030403150b0301020315060901020c041b09270c0c02130b01090f030b0103 69
    0x742e5410440301c012107550a20035203800044c01140d05680110002c40344021565080f00546035001002009070441c2c6d191311741e0324107440e03a40480b80719500c01089030500c2280002003c603500c100d6501a03a41200441c000b196441d2000e8410b6903001c0c104202c07009014008000450400c0c0c000b92404524243c03801081440324202011501c960f0304075082c2035044030012860f4104c0720181d07064030727000700e03a20010510043d0700000c001c408201114040ca078480c5002100041c940860194076031000300503010019460300004205000f40014000385028072624180c450b0686001401e4640500e0017601a81c030400030040190301140314018000812034115580b960080b004034501109000c81030340c041e10744000300042482c152103083c50000e0a4035010a06952000c04040440345410f0000d0002022100b40c0030804d250760010a02003030500f0044074641e20741c0c000c150680c4104103511445a5500c00d520b48030f40e000640c2800401c083c0031500c421905540e12070441c400107210040c90 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 883357131 1250 883355881 883355897
    0x403030822020d2f0105030114010207030b04050c01091409150109050a0603050405120f160303140c03071404050607080906070615170c0603070e0a03050d0f0809160501 74
    0x2800c80400e0700700511940041c440100c0485a041180000d01c40c2c02543d449111003200b001e0040b140000141104103058442a045a02e0040300c402c00764031564070641180a088004130018401d00c0d50540514055002000500744640c0054003001168000b02c800300200e80701c109150362040d00d01070340881c490030040c072501c02010040c6c45100c41074002c9544440d4002011544651550081e44510b02910840304884281a407110980c4294610900f50b400200010b00342e101c03071440340c180e90718031030301c1d000543c0d0300c0c443e00c5034030040020b032410944601c0010a02c08225401103034016a102001010340c41c142c5000d0000b01c0900c41c8450040c00101c010401000c2e550300d401c21381d0f90403500504103212651580c0711554103030a103801081c00420b106c02a541c0101c50010301015a07c0014088504d103460303154068802111a441c1203030b002c011104044001482400402c00d40d1080351140c200c1242010f4020b4101840101104030341d6212508441d10011165800d0b000ca840030300700305034 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 883358381 1250 883357131 883357171
    0x1e0301030f06380d0803160e0a0f03020909030f07080711011d120309031c020f0c09130519120e0619050f040305030f0405090a1e110918060a060504030308 68
    0x13550b80994880500131410100400006070f4005100d020481c0d081d50b0f4a1840311a000d040001004403801030426112800c50144014141030f25800e8000c2c110740d084a04001044610610650003440300b100d40002c0811300804200c003400310f000c0303840380034282080b11480707140f00f0070b4901c00c0100c080791043e000e00c072203820315010520445011020103400d84c0c845c1210480c071121141ca01381b40b080700600c246610030054040214180242c00002414580c0302d4480b510044c030100303090403080d145c03802084a002d42209010407075814a500c113aaa0001d1312062070005042d601ca4066610301492040012041c0e8020040d85040f01c1c0506080082d1282d101c9400c40106000d182c01c010030a100c00600d0005401040c0082c00494a046a903005030390b40d0f0410920a0312400211460800f107120f1008000800079048403803002c035a004203500304000b1600003803c3c94000c2054000c85200c12040c41940d05154162402034962800c01910700762459600404e458030040480720307003401c02c0d03010131 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 883359631 1250 883358381 883358389
    0xd0c1706132c0a05061014010f03111c18050613060e07080307060c030b100c03020309062a06060306070e0f04021801020c100f051e0301030f0638 64
    0x3030344040d402d92500c0b144141d1400d81a40e110740120058800e885824005540c2c540d00e448000180ca40558203508176001c00001500c1d08200880024141500c0d18140d442e00d0500300050505101222001901600403034400001c071007850303115940400c4040c1c01400840c1000605580000d00324008041d14101402c0800c0244106110100741c2e0040c001d0000b009540000a0300069004410030061040601f40690840e0043c2c1d40c2c958211540340d522f482400d00a402813103030b00b0b000b070064034540081c42001070344a03030000415816102d18155090010130081d400031002c1c10001c0010500707401d01c40002555601c000f00000201b140d2082501100e031107907054401b038070201400544d29803c080c1c2ca00c007844000042020300500c07410080082520300101c52079a08041500c40804140f09200100d882d503000360140407580c06070160038101c5248810040d4000d60041c4031900307803c0481e1501d1425140442d4500e8403001c2111452117040520240901410703001e020380b03c0350601140c001c1 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 883360881 1250 883359631 883359671
    0x2070b0f18010e2e1805010f1406011805040c0201020d1a0d0b25050c0d0e060301090c0504050a0e04030f05130b0715050906160512070c080f0d0c170613 67
    0x1003080e0b51706000c40780811181c4260075901c0c0900c00c0009100141c5510040d00480e640301c80154800c291780004170310f8950241c4c0030f501100190b0000b008000d9110404917056504a0003a007005079800900141001d80d00e1051900d00c00e81c0c000e42c00f1107010030100243e000c081000018045c0c80010000c41c110341100c058030f912400080c0240c086080f495032029003d60480400140c2e44d000391f9280083d00f030321510301420701050043c021429070342000f448400030b104445600050010402020550356038000c2d011000701217400280c0300d03900d041d1034000d040010750144001841814000490880011902da80648410108884c0c898480e8103064100701d070540556050340d071411043c4602014082080c507c01d2424501c0744c041c0450f40c03001101c0c3e80c03107042c0c0788405403120040450b440e248241c0198031064040c00040d8113007110f20700d080b0895400965440d441569481600180c10303080054040b40c428060100031117403401402040451807011070032035941d941c40d808604039207419201 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 883362131 1250 883360881 883360963
    0x5150f041d04060e0d120b1c0c0f0b0f070305090a0308070b0703060b070f06050405031207051c0c02060a0f06230306060a1d060402070b0f18010e 64
    0x711840c0c400c102034061600210541e81960780c1800c0c045042081c2c0d42c000f407944d07800480d540d0303503100314081043c40d83d000302181840190712511401018450342402d5404901160007207210840d05464aa06200b000d640c9034049100480d09002c24a0521181c5054a00e03607600f605209907152030000000c4c07420f45123034200610200300031440c0020b026250b00e220b882404907450801c203890301d40c040481c0b01d0054070001888401034404c0d010000c0ca90b50006504140301d5021213041141e40d50f401d4090355011198000010008900f90007205002030b0484203441504800300890920480001c2d1503200c01003452000e41e4072000300150416080d44114001c00d034401e604078031120030011603a6841f5040980b0740c031900c03549012410926051600304111544001c0c01c0080c21178060280000600051620360700c03503800d00c24480440c20079003d051040512190103052131038410103044684803220910720540c1c2c94074102c81c0c040f034400102950060640810b4400c41e080441401d0318051040f04 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 883363381 1250 883362131 883362149
    0x201020d0e01021905040b0f0706020c0d0c03091a1911010c023007260301170d090807170109050f01051e0c090103020a051603110f01020405150f04 65
    0x120044074035040d409040014481c3c0c1c14044034440c03080084609015078010319076403000400c0a010a06070100c010b02c1c0244c4160300140c18180c1120100d41005100203040000c1385400e110314003010380c0001c0c81d80142c03190b42c076511400c0d032801e01548241c1c054060300c030740e0740c0704a98514460340740030316500c4c203000100c10000c0c0101c401c021002500c424145d502d184180701060280103040031100d6000600d01e030402c0600f4144a4141c9134682d07040040324014801d00c1c0c00143d4000c41d031309604010f501810110381d0703004a81d90300040007440c00d821180f602c010800314000501103120085003510445052030039095440c102d5502c041d004200410008106103d0000b0700700c5159419008107108100d1140800c03641c1d0405050070346510002c480c020401041040440b45070340c02503000c0c007001402031401e1810300e10910090704d90840c826806901183c60142217042012041252044004031500203504062410f00412250715004240030080200841c00c14104203141d402d48000303010300f00c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 883364631 1250 883363381 883363391
    0x311150403050a0e090402100e01180306061a0306030c040c050f03090f061e070c0309180e0c0402091e011707030603120309030503130c0f2601060509070f0201020d 72
    0x100e005000c2d80e02480c8114040b901c0c41400040d1454011051341c4240d401030401100030031000004c881c41c4520004242c1441007100808a20205c0b40d2601d01c080d62040340000392050400304800c0356000200c1481020150030010030040b6140811a001003043c01d031070119940c02d0400d8243e906010301c403000c00151402100b00289901c00103144c1726045202c2c420348040707454010394107174081c1e01c0c1c10703000d0101000d02c00804e02c110320a641013104a4000e240c002c8030035450700c0c540040d600e2851228040d16481e1441d24501410502121554803000c84e011440c011a00e400309540b00501d0202c0740c101d000c0b0203a03841140e40030304524004611250000c1100d850b0400b00600100320600060f55a50a001030041445000344a01d41406805444e0a030031544c2e189400500242030100c100e44940800000290b101c10003940700300507181c2032104641e0081c604081b0711017801102008001a8100030042095885404005421001a15014030322410442c001c0c5c0c060303c5414040b0700420310307003 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 883365881 1250 883364631 883364633
    0x61b1605010f0c08061504080d0f09050d0f02031b0f040216080a020a0c080102120105120a02150a0e040c090b070317010f06030507022d0a020604030303091407030f03111504 76
    0x40086407103040211401d1b19070f4103440c1d025034130318000c50203954940c0c0c0c05203405090150184e5041074a8504514248007a140c031440401e161503103134281140c2c000c984001340c13001c5107001c1c029000c1104d03104030680c1c0c400d0b0210001420010348600814022580000c0e449581800c0d0342c03000b0707117040d0041c03181907072011042c000075a0b4030102c110a039544080b00d50301013510203042c001c80c0e4210290740e070b810001d03900300401c000c0102084822013200c0e1207030803500d0b401604d0300904860131520b41d500b0b07580c0b10b21405074050714a8081c1c0f401d451003280750a85005400d43c00071800e0096842c103044594540505160907107400c10325140048400345801c000150718406003110768103541d45030768240700c25150703a441070b03030350392044a0110b41e0044103888080c440c0040041101da100c01c1c201c1103607040012500491381a1b4400d40040c0d0019868071015004d00c5141031440f5040c5000100520300540385448000300d0f100c0c01e680040c00c00c4543c01001d41000f104004141108602501c08400c070705103 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 883367131 1250 883365881 883365887
    0x1905030301081216020108090a0506091608010608030d020f0403061407110a0c03151d03130f0b070308060d02100c20090a050a060b0a0c0302061b1605010f0c 69
    0xc02d01c1450214402d1200c2454061880425940c2e80658444500c803a102903038015034540b0b50081983e07055226265800d00400d000f004428000d500c0403003d4108428a89004113800100b80c1120309070380e0600c081000301031070002c00c80f9010f400807040141c0382e140d20410302010b80300706d50001e0501c1c0d06003072180d00d000d03a07040c20701c3c0d0090030561940c00b07002c44043d04054441c840c410002d8203402c414041000841c2d600031500c0d21480f803440d00010405411822192201d02c1e50200e07040d036520104400c46012001c3c12040081c110f40550954024a04040e446440c8a050801020041664040303000b60b1031b04160181010360040210b0000c8200c3c00006042c1251884c055600f4403451000b0400010071440070300100b0809045081c1680e10320030902d01070b040103410070b00c4507a03946000103410098840a0110b01c030482d51110403c2c87d0301e00f4024070b80784020307103106142402c0260600c0304180d10801c5034084200115401c425200e0750a065006021007900c0d9180e040c1040c18500708998 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 883368381 1250 883367131 883367137
    0x30a201c080d1d0606011218140618100903090504090501150e0c160503070f0308090d0801141201090b0a0207061b0203030f15030d1e08040c1205190503 67
    0x1068203001c00c00101d800404243e00788203841c1d400c00c103400c1080880c3e1154407a490003602d08148500100d500300c0e01c030540c0c0c1d500c1905284281d036400c0c25225010315a06082c045642c0080003000100c0c0c0f4800c82060300f5490311010905255995030303076081c0504060155010b14002e0100402c104802c003110b0800074040c01e1010107504070180041d0001c20340d00010141c090117191000c84041c00c00c0308070244903102800098007500ea41c032041c4146000540011421011325101b5510240c0c541007190b181c80c5806c40d40751404090103850001407050102c1c002d21401c4119040302d480850b50b254200c147c1c0100594000500401480300c204218010240c004113101445201e04100082e05100c0141d000d0288024100058200304041080c1905204129410070010200e0035441c84000b00000c2c60540c1c100080400300300114608005604122810010b1a03268200009a480c0960350499181d00e02d009010309409224042340510100b01724510300300003000050465045542450b60341c0e50 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 883369631 1250 883368381 883368397
    0x30a0c090516120914010c0f170405150601030f0c030e070501090f06080910020301061d0d210e030111250803011511060a0902030606030a201c08 64
    0x1400e11020640d2019159091400a460b07903a40840c420b0304142c3c0c51000e400481400d4550b8050b2480880080c08280309065901da019110716240700e040c010041c00d80d030708040c152024500507a0030000462008608012024441c0c243d450650f80d490005078020700d000c803d5a18540d292a0110503541e8050303004600c50b201240881b03a100d40d0b0b0323000450740c2c07114030b004914078081c841d90f0403c0303000d000791300d03070f036004001c4405a51810440840078422600240d00440000341d4860241c3c410b0300c0c2c0701084400744c040c06c0e1260f42d4200001c0d00c812a4410318140c0f8041e4600a00c2d1004800d1485401041d81c400c8000b4000d0002c0100c2900c0300750140c0100490f858003040c0003409102c40e40c2c03440303040d400c8140d21102050a60780b0303020381c9078403200306035441505000d4a411482d5100100784000303407252004500020307600c051401854907000000b0b080d6402540100303122804280c0385038445844100e1030f0015500114045c0125000204000e1070401860f607c50100041042200251440b4 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 883370881 1250 883369631 883369649
    0x180b07020615031b0603070207030b0403020a0c0504050106080423010e0313090501060207060e01051c0e0d0e010c110a150903050f0604021305062e091a16030e030a0c 73
    0x965810109038660f12131000100c00d4008805401e019800c02d40d000e5584401c0300d005813000e040d030b03c4e201d000e103042045400320010b8104001070400c010100c051b413405000700b0380d0b0401081d0704003000a412064050006030040100f0750b401c2d003502021049001c02c0b0440c0000034407401003a84101135880e0411035100c4c9025481110208103411a8030803641242e105600a003000e034079007403080e02c4880082c3c0449040113000c0108001010840b421040c084840c840c000815a0030050001c0c1801e40c03628044003000503c1e000b461450ba0700c0461828903a0300310004c620008080400106525095401b90794054202d882c22024030750030026100440f4050b4081d11a1030307505500302901c5040440f8025806007070300401c3d07120300109a1045500a0019196101c8509050210400401c0ba040e0f007a85215030455a041401d034080010f2004100005030b8804080c804007030f02200340100c1c0d2941002211070720980c01810f01c05d01c09211284005016200034071200c0c2042004d2040b64020b08182c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 883372131 1250 883370881 883370911
    0x3060612032d050c2a01020f0106030201210618020c0708070503031c0209031605100806130902150307020601090507050c0d180302031c030501060c15180b070206 71
    0x6400c003080520a00101c0b428420080c001580c01540c560b0040c1007072100d50700c25116441c030b200041ca9186440d4140c2166284081c0c2180800240b5104c070300004403101ea41070007001c00060b60070150070040900e141c80e1031144c0c80b0300320100d00010700316680314161400c807192041044c00c00540c0100342d50350415059070312454540310440e03074880c00ea108050301603004021003892500d91911625901d005441f02525100300003001919010154800305412142e808041086207003600d01d0548a410509140e8014a0079000250100640c84903a50410380c032402e1a400315030303841d441100903460902496459081c2644025924402405072041c2c1d14509008142c882c0d002e982964101a07814000b450b900d200640300720341c14a8034074204500b81e540e10a02100503a0207218011071620107403030001e07510340c1c40b110040c1526410791101d41031041003070051000c50715461711003005641c0d81c040450071120040701900311100440300030703000700d4010003480651640480d00600410b0180c5151403 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 883373381 1250 883372131 883372157
    0x170705060c0115150e1002030f09010302042d0602210a030b060307030b13180f140f160f05030a080f0d090b040209150d060914032109160308130306061203 68
    0x60075420030320034800548c0c8140b1460716452190402858000c0b010b00d80036041c5996245080c1842a00080d117000c044181c2c3c14075040c0780780e03900784900100002e00c004c2c04d08004002d55050076501403940000c101500203103210032540244c00c0070b0300d1850050011a540e2600c050024018041008098410611400b0300402c440b01750203208240f00c205054407520602a0352114041d0443c504200c841207505008000718101c1444004009944c200240c8400c461000e813000351903200b500815000444018203102e96200001c1c40c40405034441000c40d901c601c803240c0802a0301840020aa0060502c4140740400610500320b40c080e6100b0350f1035018940314101000844c0c022007040c2d41d0058401c00c80040030940070341110360020f0168002003182082c0a82c1030741194010420360802c201c3c000b80600080407420912a03001410f40302400048134808000050074103948030141900b100400c850f03100ca03031248401001160710840401500740d6604000441c0008100b0907404540e4481c1c0d046 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 883374631 1250 883373381 883373389
    0x30203010e06060d0e010501060e1206070f0f0e0a030c0602011a062508030c040e10030f0303021810020610050405150d150e0105040c170705060c0115150e 68
    0x906030361201e5118a503541d5844280400340d0000d060007514181c44540c80940054280b140c40d01a28071039440300e00c0540d043c800d00070012210880020990300010402c0880350344000302c1c507081002031810404044010004582e1402104422944a1024400041000413030f00c40401203400320340082c8007841c0e0540c0103240b00100c010140ea0003407020071042000481e246ca840343c45406442c0c881007814040d4a40e10306540044a02510a01d40000c0c180f080c40000d5000940c0031401600c0350318503c2c1980c0e40d61190340101e4400400381500450002404600440c065000900282020b03400340a0400000e5a514095071a018000361280e4086410b00341401903a00c2484c0350344000e2124039104080c0301c0d03c032101c0203040c0c1d40d00307002950340c42c0f91540500406021035502c3c000401c0301e007498105800c3c15031296000c1804610001d040320040540070400500f01d5402325112038680504819150244c540128000050805034001154085007448800001802541d40512806191044c4 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 883375881 1250 883374631 883374637
    0x402031612020111010510090c0203220e09070303020318041b020a030305060109060e0f0d0812010e15010804020415170f071707120f0b0c0d0c030501120227180d0302 73
    0x440c2c2550700d640c7c07050180c1c0b60103401007061741d001c81c411603241a0840d1201d450b600b0500d0040100541c0a07041001402e0301c104ca80e5400c1036566000d0507032949142d401035680e01c602003816410000201880360550b0301c076807100400a403c1d029403008602d00c4140292207002074081100400c1c545400304015521489901e0b059644e580c55110b03003800258104024001071000e00740d0300c100312045240005e41d844024001c0080350661302c40680d41043e039900d80c207040003425102d134580031500018240c0e92000341c081c1c2082e015200054141e802c5402000c0c02002d58000c401e61100d282c0303180ca04014001100d072000d0402c001900d91031602c0b1108410b07a482c94203542440e952103500103124070015807424000c014811034074000c00d122143d450210804041700d151203180c90202d2000c560392180e026108014000703207001c0080d581424030150b1010350403200a030194200d510120b03d40034440405401c2284010403a8415141040418404942c1010504550f00070b10072041b440c94020300a13 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 883377131 1250 883375881 883375891
    0xa06020c0d03050d0608031309050a020307080f040c08031b0106050907081b0d110d1409072303030c06060a0b03011d070e0a0e1008150f04020316120201110105 70
    0x51401c04503541d44007110550000f101c4028250354410300094a000e0030002444810500080c000c0a14a8544204201c54009001200050042040044545d44807d21591140490408450301c1d00c41e41002ca104001603044018a4400000c0d44a8403161001a00f25400e500304028403045450320300b070204810042d100200401c0d443c030042490070141070306241e96030b6040c8400a0a204110754040250b4869400611541c44000b03411404030926008039403241032a10201001c0782090040e403039031400d0611504104400d8107848008508520034103500748d038401800c07640c6a11010003100e4844c0002c0d1005485850f10080002d9070b01200003e40c0d0480d110309110480c0a80d400303103d51050f080042c040d00821580c0e8541c4a207a5580341c401d44c0260291440e805140d00c0c1441103508100d506804c0480c19601200c4001300c13068403600400d41c0041c480c0800c40f016160317480072916203030f040d400890300142c00d9076002c6503d1058550000c5058002d80e40c080113640b460110500301c83c0207a070 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 883378381 1250 883377131 883377139
    0x6030f031e03180d0c1203181502160803091e030405040c1b1401150b030406152c07050a1b0203030d0c0507060e03211003080c06060a06020c 62
    0x60010a00986a0007443e4420030201060503803188401d83e036400c042d400c500401c08a802c2c03410900601140e194012454200c900301044008000c134040c5000d2581104010040e6a1090031351101d00749903016945c8080311100c3c41d0845c2c410078a010002900119005040c2d481407480c58900600b0183c2020319041c806000f0394641414081440050481d075440304041c024408a00043e024550b0507841203607011f08889081e841001003d982500c2005001d090740364881c1c5405e110302c20b068821250030a0340400c0000c0e1032511840c120b104c5410360380c003602c420034000041008400c03010860041509500362404801e90b9165816039017406030000c2c04e00012480952003141804001c12a07005500080c1102c0c00c10b80700e40c0703009055513400c203001c4001510100c0c1700307810840c040c024030880d5100d071406182021040c0c1f400124001084284076400c9081101184d0802080580703507001d035401941e0342e50341d0200c050040d80c0d03030041a20010f020719031290700024042d10100706070744c2d03001000b0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 883379631 1250 883378381 883378417
    0x203100519151502011a150a110a0210080103030806150a050c2b0212191b0821060a0302010e01030c030b1c020a090c0f050a020a050604060506030f03 66
    0x8020740c00284403129a2801e0702c444070b10301084040b9000200400441c1e1070b40045012034800e4101c2811400c07081c03078076008000703e0b40d649103031484142c10341c0d09548640c070340b07001680641031186103004d04d80e520113908001e00100029140758003c80b1213050364001c0c0c41e0001142c0b41d61050110600414440c000103002c2403001180d910311820061103000310400c1250130003140c05211f142c2008406089041d0f9036420480c4002e030703a0301070081c5289940701070303201418041c031207041240c0b0403030981405040000d00791003000b154075a40300d501090f41e08800c00b41d850b690740e0151480640002829401d800300d0392000036005292008051003074940c180d43c1d41409406030401940a0528444c0c01c405254803940100155202d18a050760041f003802522403090342580140020803410f41c2005001c0360504e0741c00c00d042a040021480d01e40150300c0c01c1d41d0b440c0d08290b01282068489136000381300740106824407051000a1300980c2c05607078102e00341c60704244924001c03550386c8100030528031346001e04 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 883380881 1250 883379631 883379671
    0xa020d03050601210203010602120906070204110c0601140f03030901440402040507020d020a020108040c180f06050f01021005090c0306010306020c1c08040b2a040302031005 76
    0x1d4100e6074100b6010305020066aa08600c4407801e41c00c0c00450000066010004201080c0d04110200c400c0100c070306085e2419107030b400030801c3da21418902a0285444011001007d40c548080300e4103010200d064035580d584030b8031300040440f40d00b0501c07407045201008010051a0110407100d940d001612050f1340b030b00c86510309801c1085812902e20b0f50300301840f140303002072110681c0d090003c1000c280c4000285000e104120071128040d040004640c800d541c00c940307194000503191002502401c10103d0340d625490550666081034010b8070103001c022810304002c01c1e0795082003490b020807120900c501611401030248400060080302e0059101d00726248480015511807908587e00b807041e55070700403410004c64900202a8411565168000f9032804040e07804d02201e01c4500c03980da01d440003c4800c3c88010158140900041d124108502c04198240c00080c0d44860204504600940e14841d00340382d04516007007407005900a02a04064003c180036520495100f80603800d20184052a4 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 883382131 1250 883380881 883380887
    0x18010c1e050d081e180a0c0e070c0206030103030c020d0213050709080d02120706060506070813050618040203090a0c0b041a0c1914010207060b1e030d110a0c06091502030a020d 77
    0x181811540820560922007070220901c4441806c600031912903402c14601172040542c1c0000512002c10060440140001a515041181d044035010314002c56400d2031800010211201e250000758000040b140d003a06080081d008980b240b03104d80c60f4488482d41d61002c07e900c0714241c210480050300140070b005000003da201030b0040a000380700001e290390b00d410204e28140d1226500780c52802e004a01240b0b080c140d40054000750505582c258140b0307500181c04a80b1800b2a2030181c0305540100000c0c080c514108490750403260040c100203000c81c5c1d01e001120482c1c3c0503000320000d480c40c40c030b09414441880421a0704240c4084000c0c80352210503038441d0002c0000210441c0d810020782c1d0740c03084408003400a003009501034280009e00c2205601005015202421010180040390602c00c045982c0410265000041d90821a911905d060612801c20f486108010940c940b229400b003089944901120141c3d00010300d121850885030006981d01d00401c0340758001607010801380d141240c4 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 883383381 1250 883382131 883382191
    0x906140102160920042934050d03020a030b19270c02030414010816030e010204030605010801020a030b030f030a2a2d020618010c1e050d08 61
    0x9904e00d201030b007031100d005400d1554480d600400b90000b09401500c490201c01c10316010303101120100300d161008034030314241c0314000c00340c0030b103c407131400005401c5641070081074005199010054170219105040054000c2d08461461000603113032072900802070510300a00c2a0441800c00c2900c411842c1108103052010b4801c10705501c0528070111000c0925103000d410711400d03480e005113840c0c6052080c2080784018111400f03040000300824071a010401080e2380b0f06d29a600d247c085403441c6100340c0031380640305642c001081c02e407414000050000e410350282000e000c0540d81441000502800c15560b0485c8580c1800c2d42c3d0020000c203a40340d409101c0039407c5d101042c4202003c164501c41d0074440f044050403c0d40c0a802d09408451441140c090b09076442654802c02c04444ad01764000c900c403801080e031250244000d0410000030fa0380200d5820200300d5200503400c2c6c9001018035000d8113400d681b2000c03601445203440503202640503d00303461103141c0380c0280c161b40500307440103100b4040b = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 883384631 1250 883383381 883383401
    0x3060903020f030d060311220b01050f120f0f0c041413091a07020f1e01090506041a06010309020d0f02010c0c06051c0504030f051c0609061401021609 66
    0x22080c0102c04800e010b05001519103800b48000000341c07140340d41002d031004800703c041c4a111310220500814000340b90640350b005c0444124000480d16a200016181c0b4030500d081129985804203483c452080c02e010464414103842030700c031009441c0d50007010f00c1d181d801e4400064264048c40203002134003034030000d0f600c003c030000e003001851209069200221804810195078074242c110003010000b08650310a9003240c190302c010040c2c880e01c940e04503154402d40065915600c034482100d1135092094000c0d42e200c81c0c11006454041c00c240c83d01560f216126424a806200c84c900000c2541d802481041c12036500680010318003a000e075500f501141c81c0000c100d041c03042141240000c02d032081c485030007034507003a25980d554820140d540e003030020000790b607800050f09040130040000d90000c4520881034142c00c1c43c9031541000d8801000c0e641d40211160b80032494440c000400701d07001d821843c2142d02c08010000301490030801240c0340e0540b940442c9000062810804c9210140c1e44130f14644 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 883385881 1250 883384631 883384633
    0xe040b0a0902040c030b040b120607120e030c06060112020307020a2406080303070306050307030c05103c08072109020904110f01090305060f06010921061104050a0306090302 76
    0x500581c0c0d00140c00c0310201e01300d032000295503407615199400d03e440703000c50503c012200308140e0990100c20a40e038610080200b0200031001040181d030101a40011501110b540243c3e41c4595801800c1c0d0380e5244115901e070b00068040e10045650344440c0308480c0205820b9001c0d00c400e595070f8840668880d000c40d00041c50081c100381c0740d1020811441641c0140680038091990780c1000e04004003681c4940d004544250803022041000641680890301140c0c001e0342c41f0118990405016144010b44002040b26040201c541c0b08107031b00c2c14608043c40c420200710000b0a4442d001085074020002c0368024003003841c503802c103900c88900c01051410444c5041000c22601440c1e400b01da0100010340d42100c0b148040701c01c04100d0324020114498480e030a00c0c050181e1807440c3c0b189590b48001814080700501e031803000c90000d0b44a5070642c0081d0400c500c1080c624601680c41c607030030701700f280d006655207071400c1e03000701c1102c050808643c00c81300000c24000300b079400c41e100e002c000c0610348011825 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 883387131 1250 883385881 883385891
    0x50d050705121003060b1801050d0305091c02030120071103010b2101140403051206033c070503100f02090d0f03030f11121306060b041e0e040b0a 64
    0x1901d8804100b840b40b004010003860540c42d605e171490aaa0813880c0e02c500c225121440d00c051340900c01092411a5000c54440b0852083d9007405d45051040c41c20168100428440e003000300d01c8811031070f2030010b1090f002000480008030303203031019500ea20203c5202d03180c1044504045200040040c0c8880382c01000001c400300b02c980014507200c0b501510311800c2d0820303140c2490300002841604a2544680c1e120003541c5080d5800800c18400c861024a010f136540000c1651924100001083c050311800742400d1844a0703c400280d01040c007804d1542191000107401e46d602c004141002240c0007d401824000383c10502e203800303448542440359549a09105140580c2e503080c1c4010001070099107060307294001400c1c0101601c0c62186c40e0400503080c0088140a01d042500311008650b05400c1225182c9034070864543c0c4407506400502a84d040480100b03001000400800440b02d4142d01c1c0e1013066010445405035010030300c03440b02a07c1103d000a8042000141d0403980059600c2002403 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 883388381 1250 883387131 883387147
    0x40210051b06161704030c1502120c0309100911011d1f02060c03130f020402091003060503070f0f090e250303030b04090c06030b031212040201080c0406050d050705 72
    0x860440c2c1201c062483c0c01070100014070260700700e40c8182c01c034050002e88414900d899100608a4406139400038011025100d00c9070300d100182e81038800c000106040e07422642800004020b45c0e410130307034091341e00303003d28017401081280c4d41c422016000c2c1d01ca2188440c0d184508010f603041d00c1e074000c0107010351300c0084042d24a50380303900c3c405550900d00c03041c05041162240000f8034118004104a840c2001081840204401409595025603102c07525500495451000c80c01034020301e807515030455404501e01c0403950300358020034240c03801542215041c2d40e41d03542080c0d4142c0c0b603110340e90706103002e85003c0c80145a140c00003138000c0454030031910044071043c915614a4034a50550511010444042c010140c1c0750180b80c88403403040b20140500e20442e15001038041c2d09208040a040d81d6040294554605114441940d052482c0c1c00b0345603011803e0041c607000c03040b17600702c0c00164050001514014500165820740760180c0d1558240b8019080d29002443c01512071401c1c000d0900c8181 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 883389631 1250 883388381 883388383
    0x1a0f0a090908070c1a0313020a090903090311060708190c0f03030204060201050f090d0c060f060e0906010518010e060a170102180312091909110304031403040210051b 73
    0x501c24500c40ca0007940e940466080100200001381c0100c80614809202c03003503018045000d41e42c014a4007029514034512500c005019031136258081d2030032604200b00d0a091640000425040341e005074201600000c45c00c0410000d4880c0c4200103215840070b000e02d184024003600c444407007032080c0c1400302001d00703291107001401100c800110000b03600082c2c180300d9194280600c0e078010150754408103150402d519500d48a0b2000c0e8a61000c000741010700c1c1e410300000c3d40003011940504501040038030f44968a5140181c0c0480b8204050b200c0c950000a040c246405480d044900120760082540d0070302c17101007000e01015280680c0510580740104c1c460040c19103024a0015038000140d0300d80d10022a159402da00900740c40c40307038020a400c555110116012181c141c10200d0b1325210800c410b041c0c60000d07014a0b005404854504078090020008250055010b540030340c60310f030103c42c40c2103100d110714030080740c0c001e402103110901060100e00078400703401e240c00700000e00700c40c40c001c040c661 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 883390881 1250 883389631 883389641
    0x30d020c1e0a24020c010309080702010302031902160303051f0302090c0705100603050f12180a23011407080d020c1c02013905030619090c030f1a0f0a09 67
    0x300e551083e032004110810f5404105000c216030007802e00b403022001e591901d1080b4041d1000290505400200098a020b10070141c1111003070740020864442600080c0440102c0c48144114042803609021030f18200c05940c261344404110146407000c58250350070721a500f14060b200c048401c1d014402040001d40c148841d107101d618403240010302e503180d820b1152900c104082c1e004025002288919001c20182c03088900e403051710903001c0e00f55101d80b8082041001d00c0d60004d22902c200c4e12030703d0007900f00701c1c3d001d1211500990b01c10340540100b403480211413003051002410190104030000381c500c401e801038006800f0f000c040d00d0000003111b0207034049021521205006075510080d00c3c92807041c01c003954030300c1e80b4444040703580d07008000001c1c007050424180380c6040c094040005234071666a0f0030440d104070b40140380c04200307d5480c0141700c0034005900c5480086410251030304441c00880c03060380540e000d00b0300204c11155061041c054044082c0b4242604924031000c04298501e0900803 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 883392131 1250 883390881 883390919
    0x16030516081c02090f09060f030a0501050703060b2d0d0e06040c1202030a0f240e071706040f150606021e070f1802070c14030d020c1e0a 60
    0x18159035000703540003851001c10a0000c4011240705001d005281d031114071001302c5c0c088054888003010303140d10380040d003001c0c0c080781c0c01a07052045840002c10030006420140c066044e546084c001d01ea02e80b80118101d000fa01400123056084148001c90b81c407400394841d40000803006900c3c940003c845d0740300c042e0390400d08007125136880502484200907021780704200414084c41c001480121603400281c503048034000160940440c816200c0c28070400e5100c0504208141e130591016840307030a814400741c02d401d42c1c050713000e00824500090b030b4082c074090b83e1945414480070b03010715629a950300c0c800445114094845040440718213040d0101071080c08080e000d40d07001815031500300f8548046101d00f00403595541d4100030400c12040c0211040d1005441200d50072929400519090348000d000b140c0000c1e02c04e004101000a269410504410042c80f059003501c4840091000a80c2e46101540720540c00910107844030b0000401001d18040080c0300030550680f581d99096040e0403e4190a6 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 883393381 1250 883392131 883392143
    0xa110304030203070512160204110409090507150f0c0605150301020a0c0618020619120c26010807140307080d0f080108060609060904030c020907110f0303060616030516 74
    0x2c04c07106114007040f010704169400c00e00b59243c00a000881c003020040f42000074002e64440a01c17224005005e0140d0303001d80202e99080010a420341803036a920384a0707124030060424419065500c00707218103a40e101030885a150303010020040e594410051800500c030b03241071401c55640c0d82540c5d134280001c02849a050b41c40e85200d00c075a0410030110344890b802055165100b90064005880c4d280070b5500c8014041c10f103030101440d140c2c0a4441081c0000e640f19000c1c0b401d140c1070000c60f00410b80c1c1d100d80440c50800483c0741035019401d0f0038a00c0c01e01680034170740e20412040104242038030144c3c0d0884d001074151400e8507680c680a13407821496080c400301040300d070030200040c01c2e44030700752600400d0b0302d00007040a424640c1c0454010040589481d0080301d0349400a81814001c0c46c840031400d40c0540440c4691400c01d40060505d10502405d00340c0d070249030102ca80d4160000103480c02000003e0455103403060362900301d041300f086100c048090180600c02d4007a81510b040e034248903c1d014071 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 883394631 1250 883393381 883393387
    0x7082e0906050103021812070902040e0a05010603020726090402130e0603190b071103190323010b070501060b041203030c031406010e0a0801090501090b0604090201080c030a110304030203 82
    0x3015202611035076000b49040503c10b1280c20780e0581150507564802005452079000040005440c0e8103202e0b407a0061041c131800045e00190701e8942d09001413291003501c02c01c02c081d9882d107408905a204242014100d608401e18142a03200c5040481c40d00707552014010b407408002034003042c240d0f0843c0526142c4004401d10400c205022483c40c954889000c40103030040071245100d8003034a2082a03c06826a602c1000040e14180541c4100b248481c07048201ca444041d2110003201c0c907101c1d075120100290506404041010969003285c0301d0068103400384049a0030552079002d01e0300b060005407042d40d205d04000844203541001130000d00042456440400c0d01401c0140c01d07501529070000425107882d25208500c0410021f043c3c011030240303880724034040c0c40d0000074103040558000034529440e081d030a604002c81503102148051041c65200d01030341d00c0404000032a100940043d0100c1d81c500c00160840c0032400081d5070250401000280003c4040103d80180e00308a0301100564000 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 883395881 1250 883394631 883394639
    0xd06050412020307241104170c01030203060f04050a0b06040807240e040b0103090c0801202a1c0905040f0501080d0e04091506030c060f0807082e 64
    0x107486844a550800d0008524042c20351342c4110303610304492001e4212282d404e407040e03540401504101c101000f1500f207251110b881d21101443c01d148002c54884a100315004202d09500900a0740e1107054000c200d0026004124180000740a008264004080d034848402c45076944036400b4002a003164402000e5240c10036010342a41e1542c01441c1031800501c1034072802a981c0488c03c42c1c1c1211040d00d0102c0c2c80910400141c5c027038031105030002c000300d0805070081259003055125800500e01e060644910414811450324548102d2500c5014450b0b000c59003045400c11410604000a00c00200c0c1c80c0c1c030444031030b1a500291440c0e40c9100140d080c031010400b030700d464041c0d84904070048108104a51501807190b56428000c1d84042c240492080040d4142d40c403544142c82e1607410800340c17466881f040e01c40900412803400125050002c00a0124000748509590742d410f0720961549201501c1c0c001043c0ca004034002e000040114000f0000c194130300740070740c00c2611011030001500b803050074 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 883397131 1250 883395881 883395893
    0xa0c0306020c06180601120516170c040b0d081c05010303050702011205070207031202070819050706080f0f191a033711030319020705040b131a0d060504 67
    0x21342001030f40700c09905110180c40c40031800c24112842c4c14081450309100c0c1c680070307051000a01459181074140000082e40e68801403030740003002a59421755090085d244100301c100e81c0c0c20328041d50016400e01c40700000500a2008010300000c2588031640460720f1030305107007501d8090300308500040011400d03404558100c0f00c0920380a2285400f400301d45040705c0000d554900d0b5110140c17452010000000080b0f00078050031000d0001503040d510342c00f0b039a509000003440040005c80d17043c819003c00065041c483d0100d540503011012079a1a517407903a803540041510068506070300c4404041d00d0880e0b0710b00d00d02c20f0307241c0080d01c00001c046000d2a081003506001030340c16104000d6088642d00c0c0c441c00301c202c1b1421400180c43c01030140945180c01c1c203220901481c4459030700743c44005a00c08144118081010035034105508880b00c0381d03102c1c0180070a85840c8442d0766080b120810020031b10740700302e4008a64407907291025411112148000625410306048165000c3d95124140028420 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 883398381 1250 883397131 883397143
    0x181806021206041b080a3c0c0912020307050636010212180a0609080f1605010c030e040f060302030c15030c070507031205030906090f120c0a0c0306020c 67
    0xc82c1d041000c1d10764842031480a41da1039002100700885c0100207010540c5582c0010408004048004025862003051421182124050400100c4101e030200800c05090240c00e904d03c104e9030712243c4c0f8529041c01c6446001c4140c0007243c1c180604074000c145510780501808800c2c0841c1d4502c06038039048100c0854024486502c3c18803180c16101d52000340e600000e00d0110010307039024240c1c5d2460f41d103040348101503150031400e5016441c005d002034426808100002559000c5068540e05900007150a9480d1403035292100541590a000c0040750f005039040d5000b54001d04003480010840340c0010110750401e441d844400e87e81e400d0510035070404100191003050140e500c0d17010b0345440b440c508002e000c000c0000b03000400025006e420000103202c060025a80070a401000d140106005040d9402c02c41d0320b02c26910400e000030303000d40070000c2c0c0001e1071203030700024100180c0704021404880c0c0c00300302020010b02c1624105000100441191001113004050050b1200030b50100c0c141000 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 883399631 1250 883398381 883398391
    0xb10020a03021b12060702010209030f06040b16020307050601061e030e0a0209100e0903030402040e010b090c0c12030109240b090904030306030213141b041818060212 73
    0x940900d428100080e0000f4644060078640700014050403408000121254049100c00c600d5000b00030a1205c010b405401900c031075a801c6064810341a00c51a800d9a12801101c01810724008900813881a01c00c00116021082c2284142ca2518115403510fa01d40030081e070145000480c04d902c82c184a030407000c2c075529020400e2405001050380202c1480d9104e044140c0a44580703030210104486403491200700e002013410003000c042e54940110703507685942044a0980c0590304200443c2c0000f00103220b4009100300041001d007103901c078018004110f411040c86c9900380d00c82c43e0060707558150881c000e94000c1071940c0300807030b43c01d58a80211b002070038a110200c4a40300004810702090036003806848482c2e805440500e0250383d2402c4c11000b40c80c80341d1002e9005400e204041c07542800c1a04420141e280403046075485444620010301800c001044946400106000c01d008440c280a50101110402000840d40788044003400c1c2d086c0074070110440c0c0c100e074005240d83c0f0000306000556440 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 883400881 1250 883399631 883399633
    0x1b1c02130f1a1803150403020307060f02030603031606200403020a061b1205040306020d05040b071e081305030408150a0b061615110d0608030f0a20030d0b1002 70
    0x800042d1a58240d02e014008a90140c9040c1880600e06074904100ca010000324034420300107039007003030300303001c0e40303d0f40115002e4070071504100460051072111b000300d80c082e100c0900154640345101d0450103400b2120141110b08544407841c0c09062071038503000040c54411041c003030340d03220700e18410005118000e41c030103414400c1c50340400c00365003200341402122a8101460181c2c201040300c0448091140341c01c02883d01d803001c110100f4980150344881e20441c8516800e00036904c07500001e40340344290a8810030728059402c50044618811601241c018541341705031030004040307030340722401c3d40c109810141c2c20f607100d0013004840b10380c1d40e9440c075004800c0d140104900d244a42c041140e80c8a6100b000c0391180d5811050400c1103d981c214084ca003100503001c014904001c8119001d540c0500da1210003036080000100d0307207070408011615600003980e0200d00c4d18001c00000e5480d414020000a41303040c10080c0c14044035001d100411a4010100001030b4a00d0348508008000750818091811 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 883402131 1250 883400881 883400909
    0x5090f150c1b041a010c0302071a07140f1207020d020915130b060909091c1e031505040c0504091e0e06101802090a0f05010201141b1c02130f 62
    0x94a5003070302c0400025021b103001c0e24000c0060409030f1800b070742c1d035020314410f24030584500a0501090081c082d4144150990700a1890107104a82d4840004404400c643c0111003c1005a441c400c01012060303c060b2a07942d04031103d40009a41c034000326003000310490a0f151110b003900d003100b0300701200da0303c0a030200120789a540100311240900c2100f01d02480c10301000c18041a4100010203121520342c1040c1d0659286501c028000b408148004a640022400305040d803800b9000c1c070641092644541a481c0c0d16040030400907140d101444d03014420100400b0501d50030314051181661306041c0588001c00707842003150102c8142c1c0b105a0718580003031040c01440c100c41029030045a038616000820004034440c200002e2281380512540003802d030340b00003241d10301d104140041746d01c00d170001c02444845802c41d00ca03900302143c0725038000c1c0d220490a0300409082018184254865204440d0f0407031a903808002c1f41d00030000c3c0c4810040e4400c040009074172032141c0c3c901509045240b000 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 883403381 1250 883402131 883402151
    0x3081209030c15060f04090f020a06050c030319150609150302030105090a15080d08011d04020112150e0103050a0606170d200115090b0103060605090f150c1b04 70
    0xc0c840301c0b2203500200e003404100c003050031380d40d440d10185540c2c0d000030801c1040705801e01c0c0c606014a13109500328003d840b1418001070b03172801041610414075052010394039683d83e00701d107041038020014400140c20354442c5000e40002410824201a05058480c5805c0d2800d01c401c0801d0903901c0b010f90805c0500400c01031016442d001d075000d070011651350700490801360030030324550b5981c01e980001c03a15115001d0b40d444002c1d0300400c09412247c903020084501c80704180c0029410f00c00716006408100307442903114018509500100321103103408151a5501d8071040744101e0a13200b0b03801916550312403001e2509105141c86014014161100d008a1104c1c0f907128068a603c002e40200342444440c0d4044510700c940d50a00010380740b40540200500000401e00e030301804020b0150510340741c03501c80300b8940b550091140600352035942c1c0310a81042210390412010308900010640c202000c8200d03002c8121500c0301a000c181c58031406440443c84045080f400132102c204001c2c800c9081c404098 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 883404631 1250 883403381 883403383
    0x3010501030c1e180903080f0f040305221502061014040207060b040e011b0504030314091329010e0d0210140301060905101106010b03091603081209030c 67
    0x40d040315804500646124440c040d41d8052101c0c0b5448240310030311300707803880d03880c03da5581c04542d02904c6034030b41100d96180c1c0740030f200780040c045405040c0140b1140100340030902030300103025201c0184030680300107000b40e141009484000e5010300d202001c42d0003c0d1150300d40602401d0b42c4401c40301550300c5100d1910b941030b80b219801e07402c590b005a0307000445a062110740e0700944400c0c4400303842449000e1441540900a04803001c56038010214200070320340c00c0344110100c900322901a6a45669041c9078a6a01d085922440c00c956015440791040804140640580b81a100c10781d40c0c00071750101901c40030704008280b480001d0400c40700f404420300a40da05107242004070780658902910101d070305810790b1004000303118a102e900c0c01000000711180d0041010b4140d0b84c0030758951742484036020302510032050030501440280c000700014080300c51001e015552020742c1404403100c00e440d841f0140080b20382500241c5003040b0020380103051600043c00c080c0c0100582c4011031404002132001 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 883405881 1250 883404631 883404653
    0xf063103030c05070501093e04150312020a0b0705041a03070306030b0f0411010f02030306040e03040f060e040b0a12030e24180a0f1205150112110301050103 69
    0x18241540c41142c00440d91140d0140c038001584500204100707449030501600140190707058051182c401c0c4240d540c2c0c0103000000321450100042c414401820720802c22020700302520200e13a100c4c084070b00000100d00110801c06080e140d44d005854405854100a11107140040c140c0e001e01004101c10017050b280d84034020000e880003001d07103849454941003103028003110303070000e0520341d122800d111103090800c0000b401517101c1c41c01c9265507102c030401520850a00900d02c00560401e000060890520b0f800160710400b03044140c0f0302d80394580041d80c1d038400542d0014400600c1c01481c00b072040c203051042a01c0100c08a60845800303180400d4148007048040004041202d20303001c690703180e203c003d124100da030200c01120450110000700c00d8220b4000c4285100200304080c1420100c1c00d00055505c140d848803410701c621a402e189000b014800440381c00c0342c151160003210305145a1106a540c0a46500ca2846001c500a81444502000441c51036882030b450100108001140e0a1343c0e = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 883407131 1250 883405881 883405883
    0x405070912050106080307081308190b10080607020109050f0601121b0b040b07110114032706040c1a030717090a02331606021b0f0631 59
    0xa1085003401442c0080c05070100d0f6108001310f00c0301050309000c102c400c50107404801c00d601a00310348150759042c69903a039504034041c01c0c950500300700014089920b5590096105c0c010001140e039031541c84841d203160960403200000181d555800e000300300038040c441c080441e00c80000a10440d41454100502044c0071380c00103010040c1543e540c8000c1d940003400710001c10803040e03e19141c1c0d641d25120030082d44801c5040342c80d0b0f00c240d614039201c2d41c0940924800f0640a520942c21075542c2a200040c94606071100d1055a50701c54000d00783c0c4030104510307881a8422140080441d107040b16401c03640c111642d1000221000707204100280d580b0000e002000003018840c40029110010380500702501208040c0d00030180310701c031940460380e1a00c1702e0655001410034541c0d0020094149070940035502d87c054110703c85101e0107001c030701542c018280da4100b00c0d041c40308101c00040043e103080340d590300342015a040301d801c200d007140060034803400b10460800411101c11580c1c8100403001060b0f50 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 883408381 1250 883407131 883407149
    0x30d0507021504090606080901091709030109080403060204050103050c07080d1109090702061501020c06120a020919031e050d140d060902090f0a0521010b04050c0d050604050709 78
    0x1614030a640d68002140030b424000215540e44503154070038000685090301a400110351800007140300d815051141512150f0802d59009045090360184104d0b42d02c20200310380d0542d00c3c0c51072031010660b118002d01c01140310b100b005a44501d44000034040d614014040c0d90380c00001e00c4210081004582241c5100030101c00001d08001c0c00c2003646200c2c01108402030b0400303003000c10402039613000907002d0f000d284240783c3c009080b07100c0c500492b620340002c504c8540154060080d90076003660390007125013006004c80e000d4240100400856014481c500c020034100880a408000f4445a2858203a05401c1411003591004250301c032155543c0304111028100582c461300d040700100c2c4c070010365080068014050003480e42d500d200a010b5040690710510650f11911071510702c3c6071440d400c07411503d01428039068411a003041600020703090244003201e54880309440a00d40d59441080c0c410440c1040507521003010030102811a45c006207140d020301d1426090080050704141e030702c812510402d0b = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 883409631 1250 883408381 883408387
    0x1811030c07060c02011b0503040611032e0b210c04030209010509091c020d08010f1d07090806070f12052202120105101d07050403030c020105210a1406030d05 69
    0x414105e00421900110154414246203100d80c00d95103c001980101d000300c0c03040c403900403a1030308051140b0050b201e80446c0c1c0c02c0e607403d201c2e1203004083d041d28104a9505032600155880c1411f40c0300b503100e1440700c0070410210030006010b02c00050419040200d010b425403d103400c1d6408280a00c0c1d06005003845a920b00b400211800c60400c00030514510300c4240802d0082e0b80d0801030b6840ca056602d8102042440d4004500040741d0000c1c101150109001e40c00c6854420140d004406000741c40c6104005120401207043c2008000710303400341440365100441038940760002800c0740c0b510060310003c58208024000280d00007801c0e4910302003490881c85070000d1500c0011104080320780504455402c0804000200c0c540d00342d05400c507a00c0d000242d091511a40807030480c0c580444035540492030601040c404688103225070585903206040c00c41ca082c9e4500b5241c2d503280d00c400c1e183c0f049c4034203d40401400700389500403814945885072181d801c03420a500040d846910141990003081004 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 883410881 1250 883409631 883409651
    0x11b0302090f13051501030905100507050712050a030501330c15053108030c070501021218070501050d0f06031202100c17040b0903040504061811030c0706 68
    0xb020312407400c0c44008210300c1800140c21000005420100c40d1100004816038035802694001d008503ea00c40d8050301500c200c0d01450344e44030091502030701080c00c121090000500003945264031132100406900c480d07864901d1910000c0c00e89005820907404040ca0030300121282e8401000300309110100c10103010788241040b0110f4680c903500c2c0e00030f04051000550581e41070b516602242c014030781d07504940c02014000005004280000410300d4400e40500d1030301002c40c94413806550884050305100d1303d800401d48455099808c64600c08035418004002d01040c50780700d40708034950b1812320303015005041c5032400180a40c0269894583c0740340d00c1c0d554203140b0103016807041c801f031340e03000780340c025840b903440340095583d00c82001081030a4904100f500b5045c0c0180d8141c2c084400c80c3c402c01c03403241e84d9651030524180003d04000118441448041a19900c3e801144054481c2000054406161003004804c0c1e4681c1c48541c1030444040050000c0c04400008031032038a9000540841d00e00c8071 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 883412131 1250 883410881 883410889
    0x1b030118080d05060f0d0f062307050c010f2301080d05180a09020f1209060408031f051e03120310121104021201051f0f2d0504060f02011b030209 64
    0x1417a900c6600902444201040280041041c400e050144000304044030162150030b038034800800040789905484030000b06040e20800041100702840c80c00480c0902022561070242c0b46001d0b280d035056007480055400404003150b03045e00518082c00101105258208040c1c154490045113003c092a6610a020f868956050107801000301c00c8045584a1002c2c500d11625000310901001e45807284000c0b408524001411f80d00035a040004c01d451070311140030800280400090304032500c03140000000e0780703a4075241d280070701e41341c03a030462030031410440d04050070100b60340307400c50140300180180801140780c1081c0e4802c1d240f803420040d101d5141c1342443c030314000e03500100c180d00c50300001c1c0604c9002403850790541282c0d02641ca50809404400f410104400d02000010015465020030f0010b07070f110b254100e181001c500003503c5170724403c15544c140456090740a0002c00d400040801c02c1c1a03010501c0a0100704074402006041c0740d96559000307801b00201400c040680106034010181d0f6 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 883413381 1250 883412131 883412149
    0x3050609060d1a090c0a060c030509060a03090c0608011a03040507060e0a08010c21020c06070810030b010801020901080108060c161a0907030506070318081b1b030118080d0506 77
    0x1400c00f002c010600e4502402943e5101d20410540552070003100000c2d164020714403080103a5160320380605002a201c1030100680000360282c0c2015101e9418001064545c900701010300407940d01c020840d8100b44402c1c000303e040240350300302420108204404204013103440f00c156245c0b880c105948060070390019204400725001200366501e811890341882d40c01624454201031000700c1c0191014a4100c440100d000380d456030442c0d6001400007a105521614a242c0d0048906007002c00f80381e05e84c1c8402500007001d0b0440d4050380c0d0300188802c101e42c0c020894500500700003004080301d01c0c18200703511072070040d0303050a0710000c6204098010040d41400741d00031380d8a046039400152401c0b1039915983c030454801a07030b03a802850003241d480b500c039014004801d090898107100808190b50f50510075031042c1c401e01c910002d00c06144c040004144070300100155003245800007030080000309421191641034400c0c03407180c034040318400102c01c0e0050b10140d461980d00066103a03580d00125040344 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 883414631 1250 883413381 883413413
    0x6170402040b031e011a04110a0e010207081203100e06010917010b0d0b07031b0c08070203191a010e010302180a0608070801090c08060601200c1c05010c03050609060d 73
    0xc030200b24a1320f0500815405441d0200301300014040340b20700d00c0184011144002d5120301d03070f00c03c10410b50030090f00810014041c500c06104450110365507140140c2040305030030160205440000510013078508070450900504070b02c49903106641000d900190120019108840f103014100078081c0d0344060a500680c06144050003100c4c42d20f006240c4411007441c22114140400c2c40d091076840d901c001c1e000b6480402e08940c8451900b1241034441003ca0341152504917414461805186e08040450310b0085d8414460195155822000130304000980c0d17058000c580b0003540400100096510302002d0360714011400d40400646d16007100075030203440a40c02640861080810008450505511001010380a441e8215000381c40f0f850301c1d51216401c3d82c2482c0001c0d880305040d50013240744c910b440403d20a503130442d18070300d0b4000045030851140084102056900305d4482081c00ba00f80109009410a03280400441c500390340021640341016080a00448800c5c44641c208803881002030a05 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 883415881 1250 883414631 883414663
    0x9030325020904080c10060311010c0c1805070f1b0305160f1212140a0c12180b09010c12021602090a06050f03070305030d15090c020c0a06170402040b03 67
    0x940b8160904131065440001004601e1180202040d501c00340d511460050304d50000300e9180d24040701d401105c80295001090390081e00848c000112608025201150482c0d042c80202e6140351240006d051451071980130b005101c06100a50b6148501d542030f0526558136050094481c0407007480e54039200c0e0101401890184207000f80000d00c5104412181111140e60b2419403031000c5040f000c0c240c48800002a200108020100745403000301d03001011078a490786440c400400c19042143e00355015101d00390b00411400854500380000303481c3d0158401c9040c0c009010b000450803004240500c52048400c0146d030101b10ba0130220303080038080c0840354008105903801d0600d296420001c0001e0300c0380031311602c520011038502c0d06011901d0b0040b40e8010024604100e02c2c4041d1307001500c5002c01c000041030101c500071544900901c0303540b09100583d40100b400541503c14000c4444458200b0020f20a0340803451458a0954002c2a48150f05803000f003401c1d03038401c020910749040100c0305090 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 883417131 1250 883415881 883415899
    0x705130b04090c0e01081f020306120a08370f09051503090601080708030304030c2102010f06060806100c0614090d120b01050406110c031608010b0301020903032502 72
    0x600c003104042c98113442da03030700c1c280155076618000d050781d4641e110b04c0c14a10000080840384040003a0b4061944020301800d100003084039000150304000c040901142d98607004100c010703c3d075401d5800f01e00780340401001400d4079510050085060179800c011282000101603c140c52039208a07a40c600424016108210307034030f004404035016030021a0350003d280300c0d11000240410700054020121a44000914956115900d0487d85040e04030007d40d09488000900b0030320700010f0f1070001c5000110b9000081c2070701c1c02c0c000c0200341c4143e68444c40420520100b40000c50b5942944511a070145003009110a5902d240c803101505a240b050140211400c080104411010900380b01c0a03c00c0d60301d8600d099984014101140d242c41c0c1d80e507000900278031051011502545a00321020818022070700d03451005400a03244c402000c0120855140000c01007004c240d00f402a070680c800c007203009505001890300400c1da640101103000130050300030303403541000000114146440079000307015811 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 883418381 1250 883417131 883417133
    0x2d0f09010f020d0f1104032415090b09070309020102100c020705030102070501061d010608060d050a0b04060204050315090a1b0b0a081b070b0c031e090703020a0b04080705130b0409 79
    0x414040b136080d01c2c601c0c144200c051170070b10300314201c50640b0361101405421070700102000d0000d044a030102d412041d5144040e4820803803007203101005000c3c03140041b55030031821041c485000c4020301418245070034020303e600140c0e00440c0c014410354030340c50002101c01104100320702d0106e6960140e5055440092540305020064000400399a561a4108035050b000359401000150074420480060b0b21100030460f0392420005584000d03014008407010450b0344e440f2a00c84090603903040301c20550010f0104940d0806012115140c11101160086460a01c01031600e41066070801020810b032040107600d0401401842c00140040907200c50b1034071407240026085400c103480803294020150034a40800036034070101c0e900710b1360200040081c1c4d1a0661801590b410181c5101000288501007a1a00058012407441036409030000c01841740303940140000441290000c4070000c2c0e0400081c0480c450000c0c440c400c4a42c2501d05c540058203c0c1500c034001c1040202440c1c0c0315080c525003034 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 883419631 1250 883418381 883418407
    0x16030b010c2003070b03280b09190c0903080d05071e0203251130010b0a050402070b180c040608030903161202090402060d09030203032d0f09010f02 65
    0x488081d000e40860701344507210761a00f0918041151078007403407800c010817410118000c81e844031001d26200c1d008141003998900003410002c040742c0807260201c5002840c1c6070700e01c1c10700514101d8411070500e003003024115110a0340e42e11610f2540490507131140e010652841c0b0a45c554103040c91504511900550b462000a40320390200c5001585905441070390050b9089948040c03c0b920390228101e0303024001601030000c0100c20344241c0c0501d803003070184030a84140840441c00050042000000e000b0020410440d51410725041030b0300962050118000240003021025009480e00310250141d40140a56a292070700102e03a0682140c103100000802460020140c01d80004c12020389584a40304410140e20515900c03920a00710440704070340d005800c040a10300e030020b00141c5034620f0141882541003d59402c400200c006034000410025805480c0891650400c440c0e0030681d1074540f02c0052594403400a0030030080c801d05070000c150122001d510284807200350344019515a0006140a = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 883420881 1250 883419631 883419683
    0xc1c08130e04140106061e030c170c040305060907060c17090d0b01090c0c0314091504080604030f050702090a0b040e06091c050c030a08060109211a16030b010c 70
    0xf40540c284180441c41602881e080c5030807446504043c408680704420840c054010f40140006120040c0003810540320076104451164258260b41655603241d032415904d0050020020a403c4d0050003050041c15840311903501e0300e40d00301c0030304c0311000e4040d000024103208032a2010740c400b00c0101c101c0104a51011054121009071204002070600310340207507125000e4010040000f540104030044d550801e101809800d100039080c0014002d980781705084542c0990001e248a9028504200c01c0603800518221709044500d00303581403491907030105121100150071580e4003502d664030f042c4030707844039401080c04201070030880d0b006040200300700d52a480300c240108005040e4118081c07241c0e0103070044030f0100540200440c80c140210070125017282c40540f070a810001390050001d1804001c000014100040311800c00310000e0030300c0c0444981c0d008020051514007114100654080642c07410700c1e404c0de41e030074081280d04519004994110611000070100c843d040841c000300c4e9409212 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 883422131 1250 883420881 883420913
    0x1410020708161401020a030e1e060d1b110c060307050d0203040615090b090f040c08060901050901180209130813080309030d09030b13050703061d0c1c08130e04 70
    0x30f088081c45602004a898240703c02d8042e000c90840b4010000d98200701740031703d000340f48441440044110402c00502241c2c000340d00c4030700d020b440301031310449076500d081d20002c0881d060610f8450304015081c0070351510046840e0501c140408000544403d028a04030b8540f10b40350f0344210b62f603250519100c40200a200300e41034042000c0f101c00304115806110307075200d00c0c0e4010042d92132596135504800d8560b1000f07004031130122485030b00140c80c010030030400d8020200c1d49e0012032985090302c080303401c55110075410f055412410b41228050386506840302d410070004030703481403480c942c2e08041407244114a034034500ca1640d040005522038022002c0c00d0f4069088064801079201c3c813008480104a50002a101300324202c08212074100d2140703550840345c8528241c8004542e0303038660108481ca4444070700102ca40410300206900010301c81006025011540c02e81d50780e1050740842203900c41c1c01c0e401031403c20f0000320203210b801040302240050040d80e6402c1d48a00c3d240c5401840b460750004 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 883423381 1250 883422131 883422149
    0x603010b12061909051302030307151a010c031215150201060e010803040b1b0d03090212060106020607050a0201090c080102040f0e010312120209102106141002070816 73
    0x20200340540f40500c016003601d503007540041e145508211102c0010302002c1c09022002c000c00c0369a00040c0c8061014204040c01403404400580f9031b803400d50f00b40e448656511028a14070504416261f8104050f28003c0c0e03054500089008042c00c6071400800305404880400c041c42c40001443e00c901c0b9820340c038846d1070b82e1b000303000555544002840212080c0241803090b00103100c02d010b00c01e01c1d24050701140c0c0101d6405142ea00c1c21044050a10011240100000ea03c60003003c055050042400740e4107580c0d00c004100070340c034040c002501c0b504050502d504200d0005900e40c1c0c041d00c00d420400416800a88400300f0a9451500314000d511900c640c0700c1650685900007060f0801c4640341c0d040703030b070403000407510403500900031124026440c0b0103580c1070383e0030300108201b40c0304c640780d00c043d039582d5032501114040150000707085018420200001c40342010824820103080d0072000500d0303181a10110015421440306071308061454011310501d1042c82070714034007014202e004200f1120528 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 883424631 1250 883423381 883423417
    0x8030a0806240c0f210a12050405030409110c0c0103050c040914070201060b0708070201050702150c0615040204060e0d0606030b0a1a1507030e130c021509010603050d0309110603010b 80
    0x189002d9113600d98028400340d00213103003a003e0644170011008000000c22481e111070081149001070040b00c00a607002e4410b0341c8082070500c0010076903c2140030701c020904480703040080091010750344d15500f001c2181019122008141e06d032000406443c0600741000c0203115000c0114140c11040104480c000d0056013010400a403444601080300c1281ea0020262131801d03465800540d01d560ec0a441260040114150403030350b100d07003d0140101019002c0600480e051818141c10076258103044d807071003984104010005103800041d40780e43c15a042c0d07141d200003503075400c00d40300030306c4541d02c080d05003c2540c08100b03c20b66950310464054003810b0410446c8201c5100740140d05502c58032042038800100403400c04a400340141e08800c0030000c0007650750f40b081840d240282c80d280d40104005d64030008100f1200c3c4036020b1a250f0004103540208810341c9140ca983c0c0d0b8a0103072141301c40901d0350718402e40090040110026006c9840a0501603503560b48209000705907101c1100074407026600 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 883425881 1250 883424631 883424653
    0x9020c0a05120c0d0e010c020a030f060f27060f091410060317090409080a050703120c02060c032e0504140106080c09010903020405070e030f060108030a0806240c 71
    0x2d0080c0c40705545420028100200195000c0e100203549809071814031180310100b80041c0d94041ca0800031307503c20040441c1a04140c0740c41001d807032901c8a55070410f400c00d0400040c141901417640c680c0c0e10340704550035442a079420b1010040074510110444581020b02e00d0007840540c0c10b144810b0201d84044552010707000c450f20007242ea00e400001e01400e161a03a0a100895a0740606450100104002109071040d59840003950100c050740c8041900410030300281500a507000b0342c00d0100200909c02c02c511408025240c50b0000c1582004d81d10202c00710741c6441c0340d044112420180c4a904500243c440022810310750b069100b014851814202070072440038402001c541240d42c81c0e15001400d407034070481c10708180c01c50a262410805420000409640c640c080c0758055041e07611203498511540c4245410305040c02d400a01543c41003004200c00140042140c11040303241c80c0c1801c05448040002d030911054100d003c10260040c000c0c000d2640300b10004282484910045030081c0c060 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 883427131 1250 883425881 883425913
    0x9060b0a060315051512040c06031d0312130c08060114040903020a02060a17010f0602150903070206031509071707110a02120f07090b0414190f0609020c0a05 69
    0x114040e803400110001904002e45d00300b0a0217605e02169401c2c4140c01e1007102d0128686404044030180da62074042d0718204131581d090722900d0300c400d40b141c0c0400040010031160960324400ca92030b101c1d920803070b000084d0705405e517a60b11004156201c94418001355560030341c195075040030700032a40885014815104946040c0c4030301100390350f150700038001c0105550200002904a101c200c3c007841589000c1d41000342043c604d40d8080c205030000d180d5200c0c2840d400919020903200d1001403042d0020900c0102075000040c1c0e9800703a4111003440e900ea980c00820b03680e84284a50040c0c119028500344640d8a401400030202c07100d002c0c04090781592409811500745102c0319409441e50005120840035051100550b4140d0402d041224822005c0f206141c0c90241c0320b80c803020b456580e0b0764011042d0f2400d400340d0601d0007005100d00d009424440040100c0e01c40e0880035a0015a85203509074060341a500704400a088021045445d03540c94010252102590743e41100e02e03000e501e01007c0c1d8420 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 883428381 1250 883427131 883427141
    0x80a1e090501120b0f0127060305040b09210f040e040501092a0b0d0b180412020102030606030606090102280b130305030c13031e15051504091509060b0a0603 69
    0x45c030302446481d910005450040c2403024900114040600703c1c035400f00345080307100c0100070365074002030a45000e0500d2f1503299000f074024000c1e6001078402c2d40d1300000d0380e141010210050740601d540c9081c0e603626584244900d90025041d03010641c00c0000b4004198441131941b4010386c1440c010144131403c120100b5180088210850a0b0320801c1c00402540300140281b021011800114900b030040000c3d0070140c009482d40424003440100810051000010080000140001d40c21802c0c0200000c5840c080184401d026940108020b00168030800103521101c5030304001891030389440d880001e922142a106448084601000c18100710b103a03400c003408030b50159a1517046803605529011564400001960000441000840810070f400c0d00c1d102624262032041042c15110b10708125403401c40410511031b01e1620003000030700d42d0400d80150741c601c0b0889001401703030303140d2070b100b40302d00e812000c14924640790611403400c0010700d500ca25040d400444554164a59907002201620 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 883429631 1250 883428381 883428401
    0x291008010b030d0f120f1a100309201801060f0f0c08040506161202060f01090e100c1209140f0604083f01230904080a1e09050112 57
    0x5110a51040061342c450380301000c006410302c0d030202c1c0c0420200c1c489001d403003600f881c0500d800000b180480191800e28858155440142424040c06005071164825101040c04030200441802c02285c0303960303502da01e071000f40150680a0501c55845540040048900c14070a401003040c4200201c0440c2c0594580042d01e50b0006900c1d16003410242481000d03000b02d81c400a00000d440702610000d0800c02000c2003551884c1e005091900d4200f900d50070121048e40403110749803a007020080650070110b00b8035900512004089410102c540045a41c01054900c03041c0c007910340754542040000007103251051464a0341100d0046440c0207080792101030503503000304104410000b00401c45094145a804506548048140a420244015010441c148407600400d000d2001400804546840000c1024880b8507220b4258420804101d44010282001d84495404079040642d40e2050303000e602c0e02802040c000300903083c002c3d0040c03c401074038090a07021900100fa0b11214038218424a0851 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 883430881 1250 883429631 883429637
    0xf12011806030c180e03030c0306010e0f06030a0509031b0304050301050f0124180617070e03030a0305151c030206090309100807120608160806040b04291008010b030d 73
    0x18504d80400c00ca50294210448031910345c07540e001402281050026500c0307880304410083d40e920b00903000500582d400003215104111200404a032a240d0400b43e9503c10001c0c20001039645135074140310710318001d0100b410282c944c4503841c50714201000c4050421100154005e00c056101c203000d00c2180c0000340a00c4003101701c00801d00c07443c64110380b18040705000500302040c0a10201c13a40302001c2026070003aa000c1103400d0122811200c0e05102d1075880000782c6001c04000808200280d101c2c4030b4042501d042607180d102280d8481d0f0690601410017200400c03800c032910b14403d0040810710151000d40240c001d1030001003030311f1804401c8607400e220080c10004140c4102009896088016007240e082208691403468040210f00c07404001e40620780080c0b003e20034120900e0f00d50a225000980580c000e4018040010349001c035064001e98003c9061080081144ea08804507500c00001b07203d040d160428020184844000413080e1115000244000c2c3d001c0c00c103141d91018513407120000 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 883432131 1250 883430881 883430903
    0xc09150414092d0106020f1b060c100509011401080a02131112070518010e090a180506070f03060503030c150a09082106010815010c080f1201180603 65
    0x149010801243c1c0150600d10000c4410030035201c0104a05440d0080c3c640e0011000c0140304071a010071907440b078201380d60014040300c400d1030034509402d040ea0403c07900078680401d8203440c00380280140040d0800301e21081000345003106040340030344180d800240e001322030100042003207803002c40c94403c201d80182c0400325241c0c50001d41d000410000c40314150a5205108800301d016040d08000c0c06240d081d030301e60740c80728405003503a00c104203020340b214140700c0d4500040515881d402c425503405403180e02c0002d0340706004c0340003030b0014254500040c418000c80701003044050b000841a2404585a5003c200c0700d034440061698034800d01c0340c0303064294030020030390701000d8142903035079885045920089040321560b59440c0c520782005020b40c400111000c104070f909a101d05600390712610900e00f0070b0560034201035007500152a150290304001c01e01201d4014442c1000032541c094641e1000d00c0d0340e0f650f0603030307000c40420401e02826820907980d040507000c1204038000d0b03c041d0383d009044501 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 883433381 1250 883432131 883432169
    0x6032a050607030519181e0b0702040e030a030f05010905130b0402012601170106050604030f1b08060609150109092004061701050d031d1302030c091504 67
    0x81260004036040301001010000c0b44a2000304514084811280f6165005554006124002400e07030a4000d110a87ca2407c45d0385040b000d400040000c4800240030a681d5001c0750011038007800080d0403024080c0320005984a1903941079000e410300d00001700c8100450790302e41010a090700c00a4074088141c21071012410003080340641c255400c01e00c14144201000840071000342c650750307040f4540c0d50541c01356004010007000b49082e540c441144000800c8154100000148580900d0002501b4120b200c101182002020f000030908600848401c080f00359942c041e4582e00d2008494007400b4122034808209641030680001010001c161034801c1d1290408041c00002c6c482858000420703101c070045040049014401403000d860f0035a641c080003108010703032166810f01a0700281c0594920800500800c1d1b01c1108c0c1811011200489450700c90b07444000341703002c000741c90b00e860824800402c4c00304c00aa110300501c48500162900c403445100e03200304040300c2c01180326a51110207a058402 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 883434631 1250 883433381 883433389
    0x40e1f0806160e0d02101115041214042312160b0d2417030f0403140f0f0106060314040f06020307050c060103060902131b050c010608010f06032a05 65
    0x1481c0203c0c041c0c51207503501d0f565000540c0b07002c011240c01c0085a1403d14189045d90306002e50540020490028102410281da850714008440b00b03c520400c002d010326411551819002c85008150440d40101c03180d210b40d0562070340828020207a44100c01c108111402c0d035101086400c0043c0c19801540d024602e0841c3c03a0100350320181c02d40741c51581e0703080c500b41401c40803282040e05188842d10044101d0030041000d45820351003558503030660082c01075004900410040302c05907580130741401c0088883d00001c40c640b101d40c04011078140144440d150400e00158031110448035255000d0100d50310310a06d05000e01c03c191406030a812004420b40c000c652660010750300094280b400515003445030314101d0900d80d00b80c204030b4403107072500c1c4440250b00c0c3c89a603002d55040d8002042090741e030805541000c1020100007103041c00004170b900032080d8401e61000d401404604002d01c8001403107001a402000d00340011190040f1094604042e40024038507040d150381c108161a11890411f0100 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 883435881 1250 883434631 883434647
    0x230f0c040c030204051302070b01050915010f030e0d0201290d0b1b03010311030105010b16020f0f0d06060f060e10140915030406141e090102040e1f080616 68
    0x101e014141c08101c0043d0507140c03004100d00d41c202d0600010780341c01d400e1908204640060703000c41d100d20044411301c1b203004c00320001078420f1902420800d075022802003069001d400c20242c070300080e0095140c030301d44450301074000e5600000b035141040040c0303807040c0358130700e07480003100031103401c1161001c40100240c1c211442641200440411008001c09640003d07481e40c0260011941c0d01204180d40c002c0c0d040034094039000d440c500c41040d05085640704013020350f00c044a0040e05ca0800040c240c0150f41b90300000c14401c000180c00e000380b6070502d0910102034119445003611906000000042c030380d1242d2290542c48400410020410000c41c0342150180c0320900036645100702001251680c4d0b0380d207a10140300ca003941d13402070740320b103080e0030440201c0d500725001d4103144901d4801c12402580c800850b4054600c0004200120b031509a04240280200d8011b4200b900ac01030510842c089040110b20091030300006050200d80c9440015854401c10350b6220802d150350780c804640c0764010f0b50b003 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 883437131 1250 883435881 883435901
    0x110702040e1905070f0b09011d130c030207030e03070b0a050c030d0f0507020610080d0f0203120f220b060418020409030306091107020d020906130504230f0c04 70
    0xc0382c00c01e40780745007910701c6a01c90800440366a0701c444410007031039801c8405130004080c1c10303000f142000c0025001906580550030300021203007003080301d1250f03556001807000481c50042c030104040e8a03401c8018000358440340080c0e0207d207100002081c00c3c0340000d03181d01915100340d0050b044c06030165007542c1b560454100095640828010601d401187c0c0c0700d5528071499422001ca081c0c14042c80203404d0041c0601081001b0095290501616a00055481802200b1b280924801c603070b02c00304a00307601a800761210588020018081001c4882500c1e074001c0324140258585640400282c920072a0300c19030080000a01c000000c20034603080c1c0c490420740c08400c10542d5051020340c005000c649074101c0407800710340e60707040c240590400c034840c0b1500348010002103407078005260006950100310381d00081c81465181e0000f00c0d140c036809415103100c584510180030b2400c051400c0c00c000d809421078400c070b410347c4066080c000c48000480600c40c0f1001340181112000c030000f032201400b51111 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 883438381 1250 883437131 883437133
    0x5120d0e1c151a0f060a09090f0c0e101d0109051002012009130b0d050d0c030212270411121501260a0908030112030f0201110702040e 59
    0x5401900700c0045070300c0c060351445000c580d564021804414402ca07500d2007460080f0941e02030104145031290304950921610490341746440d0940d4000c02c171246042500903072409800d04088580305119a0440041c6512a03102d0b0300292095006001c0c85610002402c000201e143c40c4070804840c890039085c8943c5010714040c0d01d09615940400c5c804801401c0740b100603036440e0034481642e40d610320302507040e82d210000c140c07600114100140c00c521f50007146503015a81c40c40d00814507650101c02c40700c9294010240e8100440508000d0703d206207445059004d8015904942c0c91001c1c4003013118120342070401d51240d070141414030740020b0b412076000300b600b007aa03079050000c0c9122120041c211421403464541454a401d205d03121a84540c60340c864103102e000000080c2407500c1412029411032042e01040351591411204009016002d0010b880000000004100300582176901071045000c1d460303004401d90061800c030701322850584035a84808042c010783c0014501a000302c1d100c841000 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 883439631 1250 883438381 883438399
    0x507020319021b0913110f100903050c0402070c090506040f0204081f020a08012108030f040b0906010513090c0302040c021c020105070e1309170d0605120d0e 69
    0x4030072070035402601c640d10000750703110071440c0b208200b1401e60500f00010035078412000e420901d102d84030000820000505d04c15111a04580e00d4039507001c00c0100704030052020004200607000078080002500040d50782c1e01034200c24001c6410b00303000f100d05280d4000c0308040464900400c240c01490007034851944281c0301d01c2c61340d60200781c6002800291980740d0150900d8418031800c80030000341000280c50050050045c3e000c0540c21000c2c00781182e4041210302c12000d001844c14681c115003c01c0242030110100038000c40c2184101c4c01481248030310402c40c880e0b2030351108150742d040240f0900d9840a483c81c8900030001440d000281c0c810301c103c0301c0184681e103990001e810f617500e55500000590107405244403040c2d56000c9140d150003180003c0105040908005051103110807405d07002d2a00801740210f8a00140d00801020390048208840d44000d4401140180e000e031405459032070500c40c0200306032400324003500d9808030b070340010040c0301003200083c3c9010031884000c99200c0340103 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 883440881 1250 883439631 883439647
    0x605030618010b0a1101050402060a08040326060a080c0a0312050f070b0f0c03070905060a1e021608160302120a020a0306240b16240b09070201110d05070203 69
    0x3485072540a0200c0461040e1904420a030040400d0000b104000070390b8180300500c0090f131100011034404820a160aa0141d40ca0b420f095407040c41820b0394004015101c2e0450300040712000c0018003c080c02c81d030f0400507981ea065a81e0340c1e00c404280c45a406491801c0800004884411450b003d54290608608102c0a41844600c0e0f40000300c05031180d0081104000c0002c44101c6050350203880300240ca4211705020000038000d80090080c203001d0301c3c000801204150140c1e41190400c0c1d408003038805400f05144000f92640031266500541901700ca81c0800c1101022410b49082148411f50035450351030b540070099040800c2d440c0c0f1046000d100c00601c05a1607070072180c4059802a280410380000f4120721104040c0c3d4401038075100c0b05816024002d6007070540403034058a40c6900c2280341c0304814208000d050008191001d005048500c0c04800720009801c5058002021a0311441d10780da40c440036400d03100c8415134120302500800c000d0200e82115800150402da05104482c1003400c4 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 883442131 1250 883440881 883440919
    0xe040b0603062808010c0c0203061e040303050a0f0929011505070f020301020f0a1206060c14101d070902040b03040201050c1501180506030708100b0f06070b090708030c0706050306 79
    0x50001b0400003400c0202ca1006604042155030b40000010b002e01c0541c00c8144241d9005050280000b410103442d600071035070012070b0317400024210950040401001c0d40601d480350708800200380140c18000d0406007640308071404101681250346640343c0f80a000100da400300d5882d030002004451000ca410310300d20150b1024405403515650f0322005075a01c100200c006000a0a4085a61209814440c1c24006203a20189455525910440b00c4450074a00200c40b820700d05401891402c1d41d250501c40f80c840e054980d540e40302d100800041c3c4040b81e80b03400301c40040e44540d00401d001c4400c10000705005500c56001001e00a54881c183c40f20794081c11084004a03100303a0040c0c0080b00984c1e04901c105ca00c1e88a0660403040407002411194500b00d102074880c0c41c1e800030a0001d980e60714014040c1d40710b600c0202d00da202d009000a65a690a00d0044003205095602030700e0b500c10054013040345040001110320300810b25004100761464030404483c0b0fa0300081c510341e00000c64040350303500090 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 883443381 1250 883442131 883442141
    0x2e0507020d0815011205060414090705010e04052e080d0503011d040b04061a031005090f0a050a2909100c020d05030c0307031107030e040b060306280801 67
    0x80154064181600398040040002e00050003155034410f40000c00d904580e0448003503030b80c0110360b01d00400d0556039440050000c3c00c071740724400d100308058020010300010100d41c00007034441c2605d4920ba07140c104824041210012a0082d900c00200c22001402491101e800a0005847c14030b100c05e440d00d4641250411588100460210b01f0110041c45070050700303035070480c11410b0206141860301e401e45408100c280c003e000502041c0e9a511001124130310b0b05041c0300e241c003001d01201c050081038440301c401003408491070b40e00c9000d10003240d4917800b004124005901e402100400b00300002d501e448051a43d17500a04070300c11190494440c8154845940d103204000342000b82c119201000076140640340c0404a4600310340086a201990726080010f4a410484a00e1010740302da039055400d800600c50400806104080480c22008060f801079407001d80c680f040e0750034000103035400b040c0300d013600007515a19809807901400b10349031842141c445103081c06d0480e420026541c0d4120309070840d6 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 883444631 1250 883443381 883443391
    0xf090917070506071403070806040e0c03010c08150402030601091e05040c051e0a120f0e0102030414010e01020702010e010305090a0c0b0a0201050105091302011d0901352e05 76
    0x6007004003001001174001c0788501007180100c85a0f441c621740000c00403d594002464144625514544440895020406202c4029014000300708820300341c2e00c0503144d1201150691007840000d41c9107486410f0900030759002d40810785a0700e0380c0c6401c090307145c55580c20000c80b54041807180f40740014995914028500d9941090311450381d41d603038480040644294510075042580002c0000707a03000b030350229280d00b007100c018500083c400c1c0c0c0540510041c20b603048403c0c420758008010b220a01c2901c80c000c220f01d40300c48008204e424100c00100d8281c2c021000d019001c2100b01c5211100303075005e81c21141e4000006015500da111466440420703440850b00304001c0003101156804030b00d602481005d000d0b20080398901164a13050072400c07000f80314030200034100041007005a807060b117115100301160718001d216409540c1c40701d01d21840c100c03070013101c0c050408a0080c459400c41d14000d24050210054020f070901c440c6201c11840ca041108014030300102c1e00000b161002d950030305c601030040c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 883445881 1250 883444631 883444633
    0xd0207060903020c0d030207060c03020114092a0303090103020304020d1a07030b15041e08070b070308061e150702190503011d0a11040f02130f0f0f0909170705 70
    0x881d0060400070b241504075846035008940d940c118030082900051502c04843c084c1c90007140201031454124098100c002d1106000400303a01401110140450203e114007411a05914010000390300d08005420f0b02d204250542c00402000889503c2500210390050025188400d064016515002d5a1724248101d01c0300748205000d004015901d400b807000c40a500b182d401c143c03e5500c2715aa540e5226511170511021001040e412090411032611300c02442d07100241c440003541c0d4025020b06501040301140000c1c0d05d40c0000351280391030340c2041c80100350b405110151400b04000c0c04100489910031421030a024009440181d4680c51030703080e982e0078082800c103540c0c50a020303d825a401c3c0d00c0100c0003c000b000f0320303002c0714200052824105400c43c1c008001c04103d1700106004018203d41280d40c5800015250881220081e241085515801004d0041340c0e90b403c001c104115240070303006120501c15801c03c072441c0b075504000301007406441456480400008003208503400040d0485107 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 883447131 1250 883445881 883445891
    0xf2f01050402011407240b090f010501022e0b06040b22050a12060504061103070c1209080705010819020403051507031b0f090f090b0f030a0b0412050d020706 69
    0x21944e1060700300061105602d102428071205594402c44600c0142d2210041d0344180101459008079030043c0c5181c0401804003c2e0030b007029407002c076440209010380742c094071407104507824100071a640030003046800c410185000e0340032034000d000381628a0189078070400a220214040b06d0301d500030810b85c10002c0f4034002030b007a055441c5400d40080c0d44074500c81c10742c1c2c00d400c1080034059132140c8080796000c60700003286c2c0d0300c52601d00000d11120002121070781c03010080118903a000710641c41100d01031040c500d103c540341c100465a03201c1038045d100640c0c00116040006500412516400c003601082c03040d282034a9140410803030300035901c2600e841c2c0c4201944105041c42d075101c2c603000102c3d458140559245a60381c06214080e0b43c818004020b050074011502c140f0511b0a940503000c0f20501444040d5500c034003c02074800742c0c2d0641d120340c2001302e00640500e0002500c0d00c50759804001e460160f6229102d960f8944004a490024801d0400c14010540541c0c07006042c40c0c2d00c1481e00040c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 883448381 1250 883447131 883447133
    0x25060f020a0c03091406070b100e13200f10020106080a060204031e1709040e0618070f051003110c0d0f1704020901170307150902010f0f0f2f010504 65
    0x204807a8107500180507841402d41c41101620341b882106d020030b403c00c01c420644d49039099031040c8000c3c2988542c042100c04014000c00010403440130302014000c02c00d1084107050008561181c0b81403c611645c010030640344c441700d500b40f81c16200f50b56100c030300002420315aa408001c0c14507920786800c54007958009414030801030030328880c200c11900c0200c014010645039403510241140741004c40035415002c00c010f04113a41d1a004070100c0030584e42910a43e04095412100c0d03400403000d10072140c081d41002040c03100604480c901107486c000c0c102004c400c032482c8180d00408540e441d08041a00810074040a840100300040101c2070540d01c03091f10408041c0020318a0201c036103180d02440d190410300c8050b070b60f00030940e411b46000360503585580d2425590a4510310421030001c2005e0345172211903061403565030080e80c0050003a00d0747c100d0507541c204203c504604440e8070f1008145c00d03000c4080901d116148005c07401c504460040c1082c0112145071100c0e000301038800b0007d80d107802c1004 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 883449631 1250 883448381 883448387
    0x1d06010f0e0d0b16081b160515090709090b0a0507030e030f0c0c0d03020a150204180b0901060305060901150509150310140604120809061201090e0325060f020a0c03 72
    0x404c4010140c60f15402c5400d1a07100300032040d409084100e54011b012860b02c00c2034180c0741e074400c5060750100450b110108124091403e0b540c1c00c4582c00d071030f4010080c0000d60b40d4090b0040b60140d0b40d204071140442d80d9a00d050300b00824001c1c1500082503038810341d42e0301030f20f001c000a126022b03402481c02c0d1111000d240360303481c02020003107960107160146580030019070002220100d05901c440a0740c41c1c0145c60f00c1000003030255a1080c84010070041802d2080045176202d00c1c41c1400035260b103540c503a2134170303030560580d035082e03d420b604035640c0e02c010050140340c0034290050f0921460f0152030100380400141d690520b00d080601d91500010a0040c0705640300c01d58402800100d00b0b2111140c600300020342140600c1c4289211058080b46903020002d0704000c840758400d005220a861308000c420350010b01c142405044082c9241c081c0c003580070000003040d00e032a030f80c0460865641e24404078040c0007041e4240811541d031519400f401d8100a41350001d04800100e5544100d4401050b080003 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 883450881 1250 883449631 883449661
    0x150210060914010512280311010603020d080706020f191e050f0a020102040308040803030405100b030705040c0315030b15060301030b0105010809030c0708060f011d06010f0e0d0b 78
    0x4a008103141040c0e0010742c40c0800e5030a0704480003120303031680340c0d250720f2505d50a22009010102030391444c1c01c88582c1a070350f0036980002d0a8004d0b601e649030a403260040500722402804080e5012100403000c9000030b540200515241c1d100310809824031908401154081d0445000b02c1c80c000915000c2801c1c8a0b40400b0100a10414032034a10901701c04080260807842401403802c1c58080004200002500035011900110307806010a5034840e42d07104880d0300c83d0000d0350301302c03940e0103035107201170800010780030303046070b0090090140c00c000c1d191004010080c010111802e0900d03450750003906218800440e1680118010300e0960b61520f41886180b520750250314111703120300381c2030005001060101240d181592000e00388101d441e143c5156041c954004d103803078622944a07041c0080303031417035011038518000c1034200d011044036601e07001403c9820096184140e15110002c0004041d98450700c10360259900b142440c285022080e008502c5014410780141d541550709410310424059001070 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 883452131 1250 883450881 883450889
    0x30a0306210218061908030a0f0f021f18050f060105030115050d021906111009152a02240f181e0a02130614011101020415021006 57
    0x10041407807000d600042403224003040101400c035007a00094940d0b1143c2541c904040280c502c10b03000f003940c804081d40e0b2a405081184002881000700484441c00713407074082c84003010f070340141100c1c601074409039217207462a201c01c0c1001c907241e0054903400d80410f106014803d0050000d401001c00d0540d43c07e2901d101a4001c41c040c0e03240c50840f4050b00b120446003000d44004850304c00b001011400000c800041e552134082c03810408070400203c203a0065590642c141c45841502c5a150b00110013070201c81c204440a04088184004821040400d61103400d95000c0792003d941c94925106007100d00107540d04004016038440d80c1d0042024403040280c0c8000c0780b610890f1310303142ca810703010350088160140c6200301a10154082d80900e50301800500450b5a52140030010340852005d400c2d44c0d008100c000b41e00800304021040707820100c0d0700515041d00c090b03404986103040e03040011200300e080f05074440341c6550700388404116407030010702d1a0640c4280398000e189242c07041128408490f1640c1c4 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 883453237 1106 883452131 883452179
    0xa0605040614090a17240408030a0b04090c060e01141e0d02090319030e03210a1202040906031a0f060f13050702030316050903060112080408030a0306 66
    0x3c1b460042c00c818403941649181c44d451a0b00e011b101564042c00d081000c00010b035500f0100d8120360035460014000043c107058644601d08440c1168001000040c48000700d649103680c0700c421500010000c013600c9182c0508141c1150f40b40c90b01102c0382c003030342e0000b1913402901000d55064400800c1c01500ba6041e1703515070980c80c2103d50744840200c000c00c1e01942684a28200000c0718a429011441400628500e28003a02c4140d0450384911040100c82c2454010004071350000e00010403400c00701150403400e501d042622190a8000703001c1c00c1c0130200800090015440e6116044103058400e000401c005201081c80401112000c02d5442d09100c20301021981c00801103100350386180c8045065080e454040700c5900c180400140d050344847e006100207803645503e0f0b215948205040c5113002d0b55450118119007005584502007961000b00308402c095015444028039035807a = true := by decide +kernel

theorem cover : BRFrame.Cov 883273381 883453237 := by
  have h0 := BRFrame.cov_init 883273381
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883273381 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883273381 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883273381 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883273381 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883273381 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883273381 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883273381 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883273381 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883273381 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883273381 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883273381 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883273381 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883273381 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883273381 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883273381 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883273381 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883273381 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883273381 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883273381 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883273381 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883273381 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883273381 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883273381 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883273381 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883273381 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883273381 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883273381 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883273381 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883273381 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883273381 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883273381 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883273381 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883273381 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883273381 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883273381 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883273381 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883273381 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883273381 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883273381 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883273381 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883273381 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883273381 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883273381 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883273381 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883273381 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883273381 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883273381 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883273381 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883273381 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883273381 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883273381 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883273381 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883273381 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883273381 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883273381 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883273381 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883273381 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883273381 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883273381 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883273381 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883273381 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883273381 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883273381 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883273381 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883273381 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883273381 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883273381 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883273381 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883273381 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883273381 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883273381 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883273381 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883273381 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883273381 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883273381 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883273381 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883273381 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883273381 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883273381 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883273381 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883273381 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883273381 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883273381 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883273381 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883273381 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883273381 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883273381 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883273381 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883273381 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883273381 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883273381 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883273381 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883273381 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883273381 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883273381 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883273381 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883273381 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883273381 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883273381 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883273381 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883273381 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883273381 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883273381 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883273381 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883273381 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883273381 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883273381 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883273381 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883273381 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883273381 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883273381 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883273381 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883273381 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883273381 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883273381 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883273381 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883273381 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883273381 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883273381 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883273381 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883273381 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883273381 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883273381 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883273381 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883273381 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883273381 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883273381 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883273381 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883273381 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883273381 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883273381 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883273381 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883273381 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883273381 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883273381 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883273381 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883273381 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883273381 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883273381 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883273381 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883273381 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883273381 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883273381 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883273381 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 883273381 ≤ n) (h2 : n < 883453237) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
