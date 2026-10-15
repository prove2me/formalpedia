-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3998
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:17:14.664234+00:00
-- url     : https://prove2.me/submissions/ce706f41-28e5-4416-b9e0-015b9712c34f

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 718884892 ≤ n < 719064748 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 718886142 1250 718884892 718884917
    0x5071e05150114010e3102162010050721180b120f1003080a1805040903120b042306040e0d1e0504092412030804020d03 53
    0x3854000344600d90024110070704018001c03086005039070b4a00c2c02c0207003042c140340c2074000d0115a0502d001d0409a40d401150080641000c0382c0030940a1007103018001551600f02d03003145a807200c0b11491702200e68203c52941d860010300410024214180c00806240c10070385070000940e4a90301000040f41e408034082280303094501041207400311410745549040a40d80d085940500d400096004281c3d071110601604c112829150708190f800350f03110310150450380f10401541c0c0d0180c0c69070001000003a01160400103568045114403e1841c0c001ca0182c44595a409000440d41c0810025000a511041c0b0f0303c00a8400d4100f16110350020b000041d1051800c5511010280100c1010000514038824050645414003030201c02800c4100034100c02d00600708040c0c440d0349418080680c1c01d000c00151030803503010b0003d55000703100702c0b03000340b0410b100551000c2c154924030031648040b014400700420703070645020302e400701c3c60340c1500d9003c0d1940f516002c10103404800f03c0d040b01000005110350 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 718887392 1250 718886142 718886153
    0x6180609030b131506030204051b03040f0201020705030f03030a0f090503121f030302030304050c120a11060421210918020c030a0206070f0804032012190905030d05071e 74
    0x14810380b2013500c00140c281e0441c41040146d6902802c2c100114880c60320ba458080301140c11250402da002075003440c0c000440c4010307408c11035558085a0301d406211541410a880400214403568001030200a082406c40c034000c00c849404502500c00e034014000c0594900041d406a0340080e00b4258003281203a00e04151286000075400460068001109100c20040308100c0b10f400400d04854641c1600c01ca001b100359600c1d19a00050004585003c2c00c41c41c680741c003070880d005403400c0a000c1c64112070f4500111070072080048100d40e8103074800440d848522070b0840400c140382c066a1500c03100b628118003c0405540c0c11401c882507030b03007088102203186e0308000034161a0100d8000c2c10140c5041030700909020810345202061102100c20030002a51040740118103120004010781c541c3e2188103080d14101003d214507600f01030000d164184982050040ba0400c400c1d0340e03c00c03c1d9640c07140c00385074482c010705000101041c014886c92001038080d042d59401200c0d4958000294041915035 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 718888642 1250 718887392 718887413
    0x1b051902030a051c2a03050c04030209061017040c14030111270d06150806010b0f0f07021e24070809130507030207021c150c0221030106180609030b13 66
    0x11280a015034174144a202509401403950098841c50340905051440d0081400b070080207143c244a802c0c1c10009004081c0900c0c20201d0218560544401c03620b800c1c641103c5054290151130401003524102180c285014040c89550000621240d03050601c0e6103d0800f01110b50000c440c84500084440c0302e007500d602045c0040c4038014000428083c02d110786035070580c14a81c00c5032007282c00800042c4042146181124000c04510101c1540c4144122a40c00340b0f01039410000d60054417041d012500401c0980d01001d0710004564400425001400c507800300706029201c115074100c18003030301011031a03201c050701140c0000303800521040d2040c24000d08483d001ca600e90040390b40401c011066040c401c4808230174111005604d5003104140d100d076030082c4180c151500c0d0040e02c40404580a230710070320007412405417898800310340485101000c0034542007400b45100140d2211002a4001c9808030b040f000c0307600a465481800b803c58540c503415410003000005c203142c00701c06203800200398030308 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 718889892 1250 718888642 718888691
    0xa0225050310050a0c0c082b020310030b06012a0804081005010602010b120613061b051c060b030103032604031709010c0e060d1b051902030a051c 64
    0x82d0f034600400302c03200310381c0d10b240310000f040f03c03403038803407002031103640c2160900301041408590310490f002c0c50012450302403140204083c0084103110400c00c09400c4041501d110381080411030380c2d21030044903e14a208120310084200ca6110b5000424800c5105041c2d4029100d07580f52503101c0380c88501e004003c0030710440d041ea0b60001000b40683c288500c908070402101c08080c00201709180c030396200400f0303200c607080d85104131805d8100030315540031350b45142d03040c2c2003088442c51070f80c000740041d0010015180303010100325100341d512000b0b1103000709a43c01498a241180d0840d2030072074207079081020349030701c0742030313a50b00d2825903451030110768031651083c0d0b541030012040030141481e5102c081e28000c070980c1800f040d850095007044441c51410001c0d1190340c1c030750f0484200398024080540c0b644081964a801012701154014001c0c014484c1140910050200e5010100e81d2482418240d0300050001c4c070100c80800c040707034120b01d00519425004a01a04000800c02a1010f6001c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 718891142 1250 718889892 718889923
    0x160e01030302060a050c0307050d0603140c090c0c030a0809070f1701141b0c12071a15090402090a0e06070801060f02030c070501030c02070e09060105040b060a02250503 74
    0x140100105a410030880350710001e24013003070001e0f0030442824030b0b450202802c0003003070140c08900400320401681c03210000350340021422851079907161050740c88110f00031165014118060000e810040c4480495001030b80b0600158a4001c4800044030700c480d02a2180c5424010904009131a090b40c50540c0050b02034a410440d40000c1c25158038219240401444030086440d4104240b00110380c0100c648c2a8030f914032a603492210040d42e5040c5062800520704500c0c0c041b40f200203000004407108055000241c00030015195507500354014058070704080e51001d000300000e07005051018011750425014000030503140a02c10b139650501d501219204001200c00c80104140c50f2f10040d010017025030350000e103240280760103005884141c107010311414035031503001c00910b142c401c010b8480146010003106032503092001d4a035844080030711559120354105020540c0c0361a21108a424140068000b005900c3d40d8910540e22080d43c040422032003480b2800000e40c03034805010303003591500c112 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 718892392 1250 718891142 718891169
    0xd0203040606050f0f03070b0a030f060b070302011410030f060902030604050a2a0306200403030201090501051e0609091f05040209090f030f0d0b0a150801140f1216 72
    0x4400e011407680110300261003103250045c0d0014a48000c15808151441c840c11a640d0341c4d0650310940c050302d94a50841501e901c0c105c000560b419210700a403100e0740c401ea00030301040d4010045440407d4080e02d00d0031103032540c01c0c8100001002042d1740710007079105045c041118100354000a09003c401c80b001c3d26250040c1201d802007001110104205c2d80e0140017180b00c0e8034401801486040c09400003e118580d0b518420b441014400ea40c0030492501054495840d601c2e0b140003406806000c03000c07504c640c204404644030b4010b25615004814031200c00400c50b036501c40030001000300140c0403800601a030b144140304510300c01680301c9191807111010585048c10310601c24a0b4000820300a2641c10800c1c4442100d2001710440d03881042c010000f540395408209040001c00c42c043c4110362260b20800700203003072500040500390005440d200e010745a0707a5280c940e000d1a900703480301c6901040d0410540514600183c0b00200102014112950019140794804584449420010081d6075a = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 718893642 1250 718892392 718892399
    0xc290402010306050604060e1909092301021213020a0803161104020304020102030a0807171e0a0b0a060c06020f0708070c170d0c0f02190810020f04050103050c0d0203040606 76
    0xd8028440100415110a032400e41b5142000f0023042020b04540d01c6541c5080c00a4141610b90244030098010303a0000c000104451404115908228a41d444590491114507100c060103100b0760b00b00c90f0022035004416501e40350f5403a0000030701e0000702c1e40204020000710b001141000503104ac1ca108605445d16403d035410218845d40e0300c030407068440d500400402c40180d0307022064550b4036006046c00101074560785000d0300c881019142d10088101c0c01c60070851308520a60000c1c07884085810075039103035124007034440c0030741e040700b60541c1d00084c100c0010004e2030b2123a01c2c0c0d0a4064002c4c900103080c241514507049030390b4850401a21001c0020402c40244541c0d204018010074205103e0120103ca414007e0344801c170141088040c00607000700f0200b40001160318140d04c945c02408511050202045480301620304e009280302c500c04d0b980880c000350414400c03541e0301c0061540c014145031510004401a1200510701510404284008007100c000390000e980141d103c0e840105a541c02c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 718894892 1250 718893642 718893647
    0xc0307050a030807081e0c011e0504030f0833030c0a0e0f07170a060603060b0403170c010908070305071b05060d0b1512100617070c29040201 62
    0x156001280325204401d8208002560f00c021a03814a43c0226500e440e4403525240300c98405c000c804800700b81c503000a102d030145206601903102c0482e030440c114400c8907400302100480d80120740080c049500381c4000b450322405442100c0d40700d030300113140c400100d0710800882c1180030300b540304030300c208600580c00000b072505020900d040402030740c60500c4546440008054413401400244071881d07810040b40d03182c2c2c032030050704c046075405040300107443c18580340b940020281d030b04c2110b001925250001c03800315207030f50403581202c0d006400c001542104450160055100c0400b1040c55035940e2080000901120b001e0103190340039440d2a501d590681c24040d1540c034640019100d410031004003488190f84a2082e42c0d0b030600f84a00000c0c0c5044806e0202d8a00070804e2141b41c00803002046006409454403012481038110164980c0304c540d54a02c2078401c0001c0b4460030039401003040004007060300c20710810003164003030f030031a00700c01c40d1841115484980c1d2915110f401054142000203558 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 718896142 1250 718894892 718894903
    0xa090203030408153709020109030b011202030601050a0503100b1903030504060e0904030c060504050a061a0418110d0c03020a170115030b0109180203060703060e0906150913140c03 79
    0xd80e45000d00341e03407021140092003001403610181c3c1b982ca0704039009691180d4443d130051503000036145907550315810700d40482c200740c9001b24824411040086641d00309005440202c80b070160082003902c8501175108003a000c100c0c84960070034174004105c204140004041c6000314025106c2942d22420000000d00051031407000c03c0c09820603e061100195004039210304991304034200061030780703c5152090400001280142c500c82c10241014269201c0d680c1e1105003d00481c2d082040700d94a803204595100c2c0328402500c000040301c450506420001c0800300c4071b602c51404024401d0700c07580091002c0303000c1c2c0c200031108003200710010004c680034451982000c0380c41840c0b072a01c52860340c0c0c4540b05501401520700460316a04075a208160740c4c0946480c166006007a00c00700d01e4130300c2c0e00600804040c803580c40c0307900448006c0381c412100422007a006041c40b02d050fa80d0842179406202c28104081c5c0444010040e041c141d030041001c1d801e0340c002c6c0c1102d08015100d0075154808052518 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 718897392 1250 718896142 718896181
    0x30106032109080c0d031101090804050f091e071211090405010e060d030513180207050d08040f02010c02210601050108090f030301090c2a031d090a09020303040815 72
    0x5808401400820f90014083c0090002102c41203500c2105140403500781260841903081c941c00e024100e0200041d0001800c2500e4054401c010028801400c00c500040c0a0741c210001034100100014a08001112150300c40160304102e1149400d0009610444440d500d02c20320743c000108140b1405d241a00401d07005106e180164840341c105100014269860340c03000406000d800a01c1515490001e00b9170030061001070a14105400304000b00b10103544004c40481d61b034054064143c19690044171014065908281c50300c004c00e6840c2e0040d43c22030540c00081c0d92120000072101c03c0003122a24413110350483c2405040254034000c0013400d802c0014200d10340c15084070006060044001050b80c0c11034400c990041401280c0030701c1a99401c1c012588803107455500c600a00b10b03110040010080684207640c0e0503044002001023100748041540d4265100c00f4250204084444640128440a00040950b0304e0955910015443c0040032900c51280c0c0c0c01d09002c000184041c90b8415a12 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 718898642 1250 718897392 718897397
    0x7051b0321093703050c030316120201090c08031305100e09060a050405010803040807090c0503040204020d0e032d0310031214031305010e010b010e040207020d020301060321 76
    0x5003030011001a10b0103030300a418010040d00321410820120801c2c0218030b40d07032004806000095425145025034258081964540700c2c0d61034040841c20700108031002840081c505450040d02c50740c0305030b05014280c203068215034a680b02c102c049034901001d64010440000116520000b140c40d4048150706c5900507403285000446c5050318542100f400041c41c981202e001c4450b40c2d0300400241d00e080107800c190f070000c2c0341000101d00b407800080204185c0d16408200c544044d07031900c80c1d1054581c0c12a0081c0051028008200181040d801511b20070f0099500421189840080c00c3e2030740d0400a880101e81c5000328440a0b8400403d1f910207510880d03a05540c5586404441a2140c174802e00c40142108140d45194049074030581000305d1090707561018655900340b1110b100691100d401042d28254601050354559840c14840c0c00384405040e19015040d04960007084001d400162045c0d070000590030808005940130700c541000346120340b018504441d0b91000c880c04c002c1c2e07803150a805 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 718899892 1250 718898642 718898683
    0x60301050708010902070206070503340c170a0f030f1206050a051203130807050111030c0c0105090612100f080703080304020f01051624020f1e07051b03 67
    0x5031954032042c041c0c1565000c500c05070b5507001c1440441c7c0584034004014166000200d400340318000b0111290b45481a000c0f032590704511a8000c044d41107028040080c98001d85140070842c442000c0d000903c041400d00c113490301140c01da22014000c403280c03501200014841081185910f030841080400303078401c00302c200a064203000204048005a004291280044070b03d0a01e0f400420070498902c00d403880491030074282c1d52090b0740d5641c0311601440d0f000c244046c222184004001040d65080394108005020303503456000151141d5001108903a0040000c101c0c050000900320201409980700c00c2000000b9443c0028101042103960031049440d004081e041001c144404145c03508660126109003084040c000140c0e210b124280c070780460711404c40028030502020068001c4c0782801c4410320200c0d4011101040101e2040309200724403500181b11030a42c00710240107003c3c00740742942c802132801200e41c03035440c0380c10600080d441a103481100340c50244d04052104d6411880c0306502c160 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 718901142 1250 718899892 718899901
    0x3060e042621151c03020c0906010e040e030d0905060f0901020a0512070516050a0b0a151e0e0108060106030e03070b15180a020901020c150906030415020d06030b06030105 75
    0xb0000b444140b103060a00c1c24880118405040e034442d940d40c030040003082e400124413414032410561182c03820950140c099145050260706220060320b03c40c1c030b0b05a640d2840040a9000c010040510440501c5144030038003095001003070700e12410310820b01542c010030b402d00d003110b4080c6259000034502c06042e40140100080f10350410190380c03040e1b21415505259aa400303c044549001c0d280d094025041400c0d500e005000003c189400d0040c001e5141004aa031841c0c0c41e42e0903a0700044c4032442c41d0110280030401c6d180b1200380000503262054090310210b0303566886410002d000e811144494001c20010041950140300e07401c881201400a1410a51603841e40000224020403091940f004040c00c0d15859440580c04688148040404101420201800002034020400090151144070f004110324980030300440d0710905013081c1c80d07180c020250184626908064012100c040e003c07074541000c02d48030700140c1044ea2240800040300d030701d5410280d00e451806801c06020307034581030a10 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 718902392 1250 718901142 718901167
    0x20d0e061f0e090c040606110d1701181d0105060111010e100f0f110405011d0d060b011b0b0f070f0905100e0307091d0708150703060e0426 61
    0x318201c5071040e0b8469103655440d292070b4100030f448400154000c1c45d0040c003049054001c1c0c030140c015284c82e0111026800500c0c2e0036200d6a01c0c1c1040d040400048000401c460307105002011101b48004038042040407480c0000c8441341803040e00030308982d4545040040659012141440320900200207009100d000581151900c0040c403148905641310703101c012618680781c0100703c1044808104100094000070340b540070350010f00401c0c0c00908461500d0240658086007111915401490314a119116588042c010304400c500c1c0740c14400132144005910080c55496031146016100304c00462a0141c2c0b501203040e4003d022400b80014a078080740e205501c500100140c0d8000d4600d00c0a023140050150b400001940340f165241c8a600b10209040035980c010040c0c48a994558a0740150742400036038680ca03903401034000d90342c800c07101c1864031100750007419082180c42c1800600d454480d043c0034625842110159500a1a1080e070320306910040035a4412490b510b42c0daa0504070000d809 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 718903642 1250 718902392 718902451
    0x18101b0303051b031603110405091f0b03090106030209071d220f0f0c0f020a06090c0b0c0303040c15171b0c07030b0105091306180501020d0e06 63
    0x942010b40e11030015400426846001000511801e4025124030300319140128240401c0c03003041c0003904100000700e5844860082d617098640c02420303440d0590707560400741164040c1850024002c503402d07100050410418001314020f003c41d60002c640d81e811070061141401c801b1703112200b003207007082c8612602102d540c0c012144000480d4100400034a810042c3c0001c00c1440300b92a48504c0c04402c004846c006621440c00d00752032120900a6000d60481034455006800146016030003088850000400c540c0c00720b05060311600165042548804075000305070000c4e1000925640000240300511604206c00801031101c1c41160382034203498035008004111000e4469884084500440c498040308032511100740c0e800c9408c141c032140542280c56031000584400d40740c40c05840004200d034203007000d40038800c0e40718000360780305040c103a92104e00408114a000d07248011401c1d684000540078002804005040030780031a505080040890800c2d401130310900450000703030590080d00185004 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 718904892 1250 718903642 718903697
    0x60f042d05120c09070f08010902030403140d0212010323060c09060a0e18011a0408060c0a2c04060902031506131d01031e020315090a081810 62
    0x414020402ca5005501d00d4004030340d4015911040d40c8007003003206a031020480041c00441c1c1e6684043d82d90b40d050241c101d00c0155406070010395102240121550008024891501c1210b0010b07c0d03e02e000325040760300102078208440f580c801c40c0d60144442044007809096021400140841d402c0c82c4000700c4c203601c20f900c40c1c540a080c010400303011007400303214407980202c0e0203031280b04441c0808400d014400c0090060080403507004034240f4460070300c0416a03003a1900c800041c50142c0380d888141e189508100c82d40b108001841d11b00b00ea0182e00d00714441d0130342c111085000c50b124041e00802082c2c410580100c0740b058814030803c9040120800d03044040241900ca003952491400703484070044560b60049180385c0c1c41d44181050455001d4480c504076400742540170311031104603581c91181d00c02100040d45c10382c840c0001c000d4801080b040140c000381024205d82c5040c51707540e5082510303080b041241f220900217141e1140c503820b03c1d00384095121040c0c80c0c8401004c203040c480040c070020451 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 718906142 1250 718904892 718904899
    0x21030806010c0206040803030403270303210c0e01030b010c020f0411040308040611011508210c0a06140a0513080d0603020409110a0f05060d1802060f042d05 69
    0x1010514076401050151015500a0545551145c0b40c4580c290307a80c1c0700f610f08034001148156600c25582c1440900089404a030141d80400783c510b850844551140da03511402009204e044003865541500c940444030107103469050001040d44009800c039102c1ea102c4c1c60600c050190940016620b801d90003812810840c4c2c00511403004080f0b405450040c0d4000801440300020081441904281480c050003d107400034031100341d00300c030940c80d00038003441640c46a80c0841d580410071000c01e08280900714014403a2070030001560f8a66280070700b000003c7c1c0c0c415a4440c1c86000904640c9131081c2c2c451032501050041e41084030403032a10340511240909003020206103801016007981000c4010340c0c00400038814100e250a1818250070540c81d000c2c0f08014a20300011082a1319000c0b00407101c3c02070019040c2401181e07420054491181900120690404410010307603405000e0840c041c420030b81c2c40d80fa00d0500c0f615900c0101c010802207003d101d510301c031210481118949405840e800e8 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 718907392 1250 718906142 718906157
    0x90b0901020c1504060204080d080f0901110a0518090c070302070f051507030201090218010e090604031d031507090f0b0708040510051b010c030c0c0506060904050f060403020d092103 80
    0xd08141c1d009001f1078101c1103490041001d40d50749681d201341c126008100855030110f050303d070011103500b26064420f640c42a46001e00c03440a40d2030084c0080e05103400c960410743c0c4400b0300540003c480d110105e400000a0702c011443c0c2d02071540c100508005003220760604690035050200140401e6080154810350703110010740d500406200b90042802030342d001d80f055448550040b50440d84950034002c0c0c0505041c42000501e40c04000146030780919090780340c80080c466001e020910340d40c443c48480750544035080c0d0420142403072541c0b01c1c1c03040341960b49900c0c0711804c2000e2820141c0c210f42c0a600711100c00e002e401c2c041074814086070210380e02211414401d8101800988440c0180000541d0b00810491490103d00040d0062044141d265404001d0b0091a402c1501c4140881d40d01911544c8034000083c01e40c1032080d00c16401900a41c2224036200b00c96200624003801110101e0040c3c00c0301d150340320710580110303801c6e01510003503040d00d00503500603051085030b00004501030104030a2 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 718908642 1250 718907392 718907401
    0x30601030f033e0615240d020304050d211a1c151e1805030f070c06090803030a0b06130f050a0603051303030f0f0f090b0901020c15 58
    0x400c4500c80102444865141c030203403020a0305800c100060102400c0c040710f4081d1078000307001141c46441010254a04840844034806102c1950301d0444503040d101211410280f40d582284064079440c001007401590b245010302e0b085e814001001201c406100202210450310402005405103020241c0310004244031141e00f90804a83c001c14203981003090641c15110710b8035202c00c42c0781c069015211920048148a42c101c007104c91a0180c20f03a04510491006075040550b00030007480d40e00000e060a101c02c103611100e0659010606000740103500050940804c0714002910004001a0070004841442c04900c543c4911000b40b01040960380e17210281580c1d40c0d0502510040f80d9000e1542e004285c9500b14034202d040c40e800307801c1c0700e500307501d0000400f01e1081c05050b2040700c0814088500707200c559000e5010380b1007110002c200e542c951071160361500040c440d00d503140280303100125460006080c18100303040c02410840c25a40100400b102e03800700018030010383c550043d00341415589 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 718909892 1250 718908642 718908647
    0x306030c100f02060f240406030615140d15050402010207030c09020c10150e0a06090212010e091204060e010908060f06011d090604020f0903011e1406030601030f03 72
    0x842440d441d40c0104064440509990300c403a10201e020996000c41d0296110b07031030410880d40c003c50b06a098200d2000030b042003a0800f10760030841c801d01805c08a8210b40300e0b69020305485c80c91500c4800046465010404100c802c042100d40301e40a41d64030200c1401512550040c010706550040c0741c944941c0406d045902c2006400010341d00514400250b42c8c0340c40c483c0000e94843c0284110611516070082c400d414144211411b0755003010314110214940000c010b29100010203a44015584d031100144e1111640001d12202e03010400054056040549840507020090004e0031a0f0707114120140401000702e003180d007540c001c1d003484400d407412880121181005034100004501070f810030310424092041e4032a005da24240c1b148507001c500c200042e80700301d500454444d070001d40c40011480e141095030092800380300f981441841d14042402090946502c24104542941c1c80316407101d5030502c0e84503114071407000401c01c200350700300040000c4d50b0b040103000c0900a0040a8a400d04050 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 718911142 1250 718909892 718909903
    0x17010b0c032b0f0612021516050304060f0201021e0c0109060e0a05120307050a030b01030615020a12170c030604020c06010608160c051005190f1a0f1005030603 70
    0x2d0039071030885241000e01818404112040314074512050410f002540050180e00429083e42e00d2424518a641545e800708403000c80150000b9100390420441d5248500c00000e41114090181c070003150744034078200c1c0080140240c0c091442c03c6910510501205e003014001d22b81c640c03000d04820a480e201c0609c0014010040304e10010407035882c00004026440c0089030040c0715600501c1035580c880460250040b05200c11206070000034010044045d03180d00903404111001418900010711a465201c0c0c1009491103074403010169014071442020801e1150b44500810321038940700e000b05510380c40c0c071190580050314064000d4030220001d147d64132154141c03500016800101c44e09543e580c40c010300a1075007a1690f960307203074500d09070b100c81c9030084035102a440d610000400ca2012841d10010007030801410b810380400a8174200039041c401805076080d440115100003625101c0b60540d080200b81404540340981c40e04a4411703816510340b66009120501030405c5a942c2d80d900c00000e0801 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 718912392 1250 718911142 718911157
    0x9010c1506031407060e0102060a05040c051011061f0b091314040c0e04030503130f1202100b0f0906090403030b030d080610230d140c071217010b0c03 66
    0x61521000100b03010740807850704108001e00c000c2e505003a171142e104503a01c00060740c00e41c1c0076074072410109110307102c2644443c1d40580140d0030446000d8990000402c50f000d04480c0c040003a00b070b0051040840406e10815401600700e84501d5023071407485141080d00c603500c2c4030381004250301150140071a11120307100c2c100050042c0c010400c0045c501d04848941401b43e034259080b0700141004280920782c0c408503030181d6096220182165112810003a00c0028000304a0350300302c2e0000311000081c0740095000302c450300340d00507003030b001c403a01450f9044820940400c4d01c101c05020a0100c80e03210341840743e41105040d00c7c50009a81c4504081d03015005268059416200d11292150000c0d80020500e014000c103d8503a9015450240c08894100503480d1840c2c00d00200380e40401e44440c1000180001c0c00c8800004c034110079a5000d80c6100e900490b03070100c0020300001c0d6842080f0382041b00f20440c3ca00e41c00c107680c40104660800303448400500448290404c0003801031801c440c00c00607503080 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 718913642 1250 718912392 718912433
    0x30d050d0f050c0c160302010c080703020f0a0b01050111030403020d170c0a0b0103020112050f16110a11090603030406020712170a0906030b0d11100908120903060f06030309010c 78
    0x54248100d0f0a682c40d844a1030250150040c0710440d0520500800c02800b280d8050b90780b10f03c1c8050544801c80d80e68001c3d64114158810000644a548420b004507a21280501441b81c5075600d448005003039040c2c010005641c07038100300018001691200e03400812140c00c1019000100c41c10920004144241c04070403e0510032010084100300070b0030b4200341078901c03c0e0317550494243c4070038415050780d105071180110003008900152130481d01d41c54042d241b80311440c009400c0c4d500401001e041000c942000d0303071400070544010b40e56007007880e4100d810002c01e0b4021440c0030301d02400207444119a00a42001008242c802d00030b21035500c2142c05e8150218180c148e550030540400b40100030f0a100f02c0f0003103404d16055200c2480d101d010b00342c0b41500001e0084039a0f4080e42000000150035240c601482a44400031405010400c41d10303c1c496210701000782c0c1c40c2c0808080520380013000b00451040b1100d50100210b03620003005803144000d00b03003042d100ea1900c601c1c221051303220a4000446 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 718914892 1250 718913642 718913651
    0xd020904080c240a0c0c12111e0a1101020307021e0619120c180e0a0e010c0f021c1b0f050d03060501030b0405070c0f0501180605070e040605030d050d0f 67
    0x41e00803c0c40141070060b0300e40300007000080c1100606440301110702034090302040110a000c50703024002e4480c0e9510340f543e00241c0714002c006542501101e040541c40b621144e0000c0c250b01e0400a802d030241c08501024002181491015030000e03011140c0010400034000038a00102d00390303103805098460340b42070f10602c0110480b100400904070900b40300040d0100781481d00ea41c1c5103600400182002503000d001c10f2140302d0a1204c001c2d00e02c1805404015a95540e42c2001c03a9000203101e040d082c000c140e5501420502c0007000280780548100f040ca84142c03900380107400b1181c1210181c01d009041d601c142000305114140035424214680c4041e0150280306d03858880103074154460426a00240c034100b21103070840307042c00103e8000300c0d0b100000c601504203007000302e010f4001a41d41c1c03d12510001c98500e8459001540302000903404840d556101e40500900300c1d080140c03d0340382e03402510b0806c446850117001a07610010031704508203200c0002032140748459540c00400b40c01d14076401c02d01 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 718916142 1250 718914892 718914943
    0xf070605060607320a03111b090a0e0a0204090b0402150319050402030c0d140f2a0d0807030302090108090303040b0a020f070506010f030614090c010311120f0907050d020904080c 78
    0x40c50b9011021f40c03882c00c0e004a20382d41264180e0001443d58660014003506800e91703c103e001d000600c5401400c00349841060b401d08016038031400344186051088115004608107481442001211005078001c41081402002034030341d032540c54000005100c040c0070840d91600d001107814042c00066140d040707400301d4650018070201215940310014041d0031107440700c1d450426181c440d94140d02560132458041100c10f0440881c86280c244204000c2c05120501003c1c1d0b6540459800b4071812004a500820344002c2580c000510651048002c000f4620394a860350fa00050400c00403d40c0504a60104081200038515400d540c5503da101048841ca941c58064016503c9264802241e00c1410040c821400b0780758400301c24045e034440001170140700c40f01801035020b01106454065100d0041c4590706810b200d200d241402080c444036010800d050100445040c0502500f0207130041c081904d0110040c0c850007401c95129802007100398480c8003217001d007424000108009060b4001c80040d08 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 718917392 1250 718916142 718916147
    0x7050322240e04090201091203020f0a030807030b010905010f080c0d0204060305010905060303040509181606120b06161b12080c101808030a0605060f070605060607320a03 75
    0x10004008152205280700d02e00d00100020307070f002948005c0c0002c04502d0104680d50710b03501400400f51090065a00920200e81020f1500e46420400d40019001e20180b003102c0d601881340c003403945401c1c42c10449040c10300b03001800710680e503c1842c08000e1141e0010b50307a40060410740304d44029214040d543d40343c3d120030040c003402e000e015494600345030201054a40c580001100c0848002600843c410303034039810f00c0c41c540340c07008059003ca405100d10960640c64002c040202801035511001c1450580411410031900000c1500340503140410034584072110801e003821496a01190000d00c0180c5000d107020801e055a1108043c45110710b044001c00045501a001c1001020100c0e1540455150307010705550a0f10100c19059007200500d001088104000315400190404041b2701c032552100403810320380c0001c1200d0540351000c100c0234200b00c03107070141c2600050122a4181002e4607902d8001d240050482c01c5000c125035060010010460302c80103510714403c20040d11291601070902 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 718918642 1250 718917392 718917449
    0x624051309151412150a0e191b0b030105040b040e07080a1e0c17030717040612020306060f0903100c2d08040308090a08030103050d110307050322 64
    0xa6024241081143c0405420820b6040108640403001400b0542d07200c1c8003442c1c28200030342042c420540b40d4a050040c214100108503485040c03d503100c3c040c01d880e080c01c4403d006441c40340010b005298500f088001c54440030b032415580102c9002625540e0400020020411a403140c18280550070b00014800c0c0045a10184a40a803170032030484404603e1803000112010002008036040b0f41080c0142809001e1441e810003e80003124600103683c0c8481c1c6001407003850100c2043c000041c14440700340e000004480c07888214000303605505110300040d03080e00800d240e207003404402286c1311645940401655000005d4810204694840c4141c0103102060308007407139099852031403032450381d041c5022408019403042d039200c45041e240c0303950454280130003504001c0036210f41800c150100328400c000b136008500c1040101411003000402401110a040d412134181d08244074400110f20702100b00d03200384180615042045040d15400c0000e0041a0012070091106107411034218070031910 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 718919892 1250 718918642 718918649
    0x50108010219020a03140d181212090b1b121515070305160501110d0506040c1b03050c070e070c02031b01140310030f0503070303062405130915 63
    0xd014100082c000c0a907550022581e004001941c51500412071034042c41c05084100c006a2021500c1c0140c10101070708201d40110944100710205160049141c02211440049541800c14070181100303495401d540c042c0107111640c1c1d040c0c200100959054060202c0c0c3c1000310669450106003070108040004030800c1d560745000781c084241821503400902c0c19900c80550558034240f0708208110160807800040d0300840e41c6640b80c200c2170203031b054548094807082d40c829400140618100701000152031002c040c43d02404202c070015072890455440084841383c06040c160b64035040052805c0ca03080041d404151a05039200500c581d075503102c0e1541e000a0300071800c441c0c81c0e00c0c400302002031919002c44994082001000d0401c1ca0302d62100c0950f5101c0440a10400c3c2d1030340c0c907100d40182c000c401400301d810341c000041c01002c064042c0704140c05000c0f0780500b0313140c8080101c1f100a4414070b0340343c4031043c0000822007004000803500f400c0064003030744005100001182030000c814644600 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 718921142 1250 718919892 718919917
    0x140303010f18110a0c0f060f09060b0a05060406050705240a0c320915030612070e0402040509011e0c0207050d080409020c100515090601030212010509190501080102 72
    0x2c01c0300a01d00d0309003d840320800e2030030086403500004103405d071204020644100c032203074900c82d060302c04111103100e103408080342e89101051112581c41e042c402c42d42500310b83c510170f605130722045c007032522114151406e503901c03410070b02c0d51001c26040003403800024407041e4000c607194400241600c84400d01c1e4074000c42c20b9280c1130005603000d59090702d0900d41002108074001c243c400000d0035507419601e4203541d024810b000e03407608401001041c000d59031521000b0110100009100c254180702032440480c2c20000040c040290820031310700007500f005000a03100b15101c401090082d03200394483d0708a407590b4000340c50b00013000c01d1403401a000060380f48015004024000506050404140b6241075100c0303622460b060030111148029001b2150b034603454400c5003015000305045200750b034003940d107000041a03c0c11040b41044045000117080724101030040c01510150031444102906450080303d070080e0507a40c0020301041c001c1d001401303402407030510b800041e4000042d8014008014001c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 718922392 1250 718921142 718921169
    0x18030c05040b06190f09030b090303040c2309100b0720010914040e1e1f02120402040b060c0d0c0b090a020a0b03090106090e010212250c140303010f 65
    0xa040201c14018001908070b130020407980304070301500c140705000341c41c2c0d00740c2041c9103915100d40f50f8400c5103034121504011540000148401d22588a204200901c42c442c0b0740400401030f42802e1011340d11100300c0b507000321400b0001c650398005003800c04000d00140c980903510b1b40030a003410103600d402400c400b803002d10b0311401d189455119400900607600020078601d50900c1c04814480200130b85001c0c000c017801002000c000c000d05029100b450100000c1c01800006040503213009003542941c52501442e1041001e001c0849a0321001a440750f011100012f040c00044049103c9108000d85180c090003441c00d0014800c1c1c1001c4001c00340c6000d8040c00980e503903402200c2d42c6e81d00034500042e40c00010100e0422a0300c030300500841d40007090f81c00109007595209401c01c2600d182d0380410695940204074982021a05083d1650146600c0c00840c1c03403240c08000d641d11703261240710740c00800440171001418054480503c01341140f0000450360740f580d4952030600b40052a018115007110342 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 718923642 1250 718922392 718922411
    0x402030a1514150d110303160317090c0a030201050a210614180606130302030303190506010305011a0f2a060106020105071e021005092104180c18030c0504 68
    0x183d02c110300355900054100f0014400a032101164200c8000d662907140c030081012924a2685c00310f5039070301c1032003525180c8148d804a42142c950407002003004807036038040040c882d026902e00c07480d80104c030703021f003081c9a54000040c0c04580201c55280e0305c9940d6810482002e241100c654880030403290b0626142001c2011038041010001041d0620441026001c0108005142002c000c240c0b40c03540c0d00002020b50707030320b9000c40d00f96001104c0c03003000c1d08620401020069000e0043c03c0e40b0076824070741041207604105068428403003c0c5c01c1402c0b00b61001c140740308242c0502c0d00315006417040b1101e0300000e00b080d184104500307014200109090180100020b21140140a8203004500c1d0307442d96a4007408010118409100300d1885030110b02c5085a1090281030a102e02d500552981000c0c02c00ba010302c403910240c0340c80983c1d9200301c002c0100001c108940382c1102c80384100342604004240c03032866103402c0f100b440701d140156441c814040c200004000c2e4010750a02140e20076a01030100291 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 718924892 1250 718923642 718923661
    0x3070801050105131515020a020f0316090f11180111030406140a03110711010e0a0e0109020a110706030b1504031a07120f06030b060402030714030402030a1514 70
    0x10280f203016009026242039140400c426080300d414240d080c522819542d0b61074440322030501c1c180019801580014981c0030030340c281300720440c6500f401a40241032108028200141030702d803600c40c40d45019070310b44411629844542004410080c416101038036804130b122000601c010900a450104012107080103028030040709030b9040328a6500e8807070b001c4401105178451030340140f90040400d962038084400407009030340030703100c41d9005201c0001301030b1002001521040f8004480c621841c5805020003004d61020301300c82c10741d1b003140d40141c1c40b078049540c10b5555908150005215004284011403225416400091080c2c0c0441c1d140a2940c5c1c1c0c00081c854034441c602015203040060401821901015400c0300c0d0031216600d04010b6000b521180e000455001c1032018a110341c4a80e81002400306454410b9045001240c045265040540c0b0181501c034900010818690000c80020103650341481201039242d00700c207004165491201e003000c000e000d241c980036501c103103050109a130002e = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 718926142 1250 718924892 718924901
    0x1b0516140303031f09050103060902030d020f030f130e1f12081909030606080309011205071b1104020d06082505190815041703130f050a0c0602030903070801 69
    0x4101030080d40c82c44e12201d640746441070f4100810f801460869800003002d607000e1180780e00031806420005500303400c070710405051484074900c4000315804035075680030a00700070040b540c10f035000300c110540c2c80c0411040449400c50300d5200c1d6010301103000c1000011016001c01c001103070110001d00003a00d48070a800f505116100e42d01501c882414001d003c0307540050404071141400900b010380040741c0d295556000c1e0307121500100120342001c076140340d281d600301d2002036240300790300c909200e00d18007038100600079400c80c0c2e680d40401000512900610641341c551498080024100b5580e48400d04030b401c01800320f92107511030f80e2280c1c103454006410b00b20148034004604142c0c03030109610780010400c0320f10090103503c0f48408001400902e1a508000280712400000001101d07440c0074100703201c10092402550707407154020020440301c146003a0000e05c003994442d03d503d110442505000c0d01e4020704581c01480c41c508000046072068000024001d060000c8084550060b1507200e49402d84 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 718927392 1250 718926142 718926179
    0x20d0510140f070c0f1406040c08010c05040e0c0f040312080711150403030e011104030606030c2c0c0d020c0114010b04030809040c110319030f02070f020d02011b0516 73
    0x1903a0100c0d000c005414041c050b030111b4060800741a4104c00c0800c40ca08108007964121100780c3c803000204006c200a0050f04440070742c0f0b0404504003480d0080001c045400182440d99072200010902c0d40d01c02e50300c1c10740b4069608600c130304200c83d914100192640f0b07001d44444d0041410b40511030b2003900e000032500c070310036414040c41100392201e60707054029003402c4100c10130a54032440101c8401341c6c204040d0008600501c000b0811624509140c0c0c4200441c0d00726201105101d81451264400c00980845070f80c044280f6010b5507540c59905195401200020801e083c00080c542c484804150042d4113120605003503040541d903928070b151154800c600c0005c0c08420144404000f83c90700340d100c02c54a00540c1000920b039000c03409003038150743c0105103002d9400c3c15610075103a9154035100301441207042e40e030114a0010551030b5070240401d0b92034024407411100042200316441440b0020000c46592034841c404c14075407401ca0f031518801c1485010f1b055040000065203000c0c40f070b59060b036 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 718928642 1250 718927392 718927397
    0xd050f01050d12031a0d0f0c060e150f04120516080d020c2101110a030605030316060c0e060d33360c110a0b0112020d0510140f07 57
    0x300101c0c8404d4019028803040310410803c99410b00070503840350100454170a00c9000604e40d26401841c14903e02c0510b5041501005000c010200c066100d05096541c00c0300d403440c0140d200d2010030084042403050740c00000301c00e10f0600320705042050004402c45e8030b1301a18100a502c0c2d86035031499a54945003a05440164401c0c01625107500302294241c440c20005903100740c19020000c120350945101c88001a00e0100015011411a40c144a01c0700900000c070081c5203030880402a103056503032240d0000c4e104654075907105094078060100d06168050141038107407a038101c0b04004005048100304c03508401da14004420100c0074400380c41046031464100041600d00b029081e842c181f000b4001e0980700c502d4411001001204000c05075000741d00002c010906c40703000d42c0002c00c0307030401c038010410a500120214000450144045056520b8140c149080c03514500000d03a203414406806003190284100481010b07515070400107401506a03241109604d4001c40b543c0060000c4848200 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 718929892 1250 718928642 718928663
    0x20d1d0607020310050c03091b01121d011a03010c090806012904081b06071203151e030b0c041a28020a061d0601090905120d050f01050d 60
    0x56615001024010050020b000c88004132104075803a0201d0320180c601100600c1e000c42085841c0f2810491a1000c00169060754406840300e030010b44403050107840c50b002c01303854403401c206d02083c1440322038028000748002d00c50800072440034201610723601600340c000d5003000103194241e40a05c14020803106400300504280e03280c010304468000307428102c2480c00002c00080038083c2c0c413200180014080381030140100c074041d4140c02009002000c00240110820710007030000c600c6a80d20b622001805090104003005c44010aa00c010a141c01c110040c0000b4200000800c0210f400c900c00d03284504041102d84d2507030301000c01503000d0381c4550002d011030903222110001c5e482c0040d00c6034200b6000c4140201040c0121031150400700380101006a03c02400c2d58107110b07103802000202120049021203100040e1a00ca4803201c05000d0420201e84601c0742c1c4081120401840b810b4080c01c1c40c90f140c4440e0380700810b401400307050301c40ca00c070a500b00c000490103140030514800f03c15030140f4000c8 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 718931142 1250 718929892 718929947
    0x106080907120f06110409150509272a030607020723060405041d0615030a0b0c070c06210b060a110a020a06120513030c1403041a040501020d 62
    0x504a240c41808542d00345d01c807000c2e50300703220a000190000e0700360040b000c02c1ca8038580345c1326843c90715a0350000b8850515002444124054072004100e451800b0382048144410140303c5854030280c1c86400d803030529408807443e100440180940303640035088084d90116110f000c02240d550308940a98460040001d401c2040e07100b16440d29009280050b00f01420a640c800001c0c048540c80c41c0c155008215490034004030080c1030002a60001720010194181030b00e000c0400da85420102000702208d141e400480c43e0148a50103690450350700c0342d40c001d1074984840c0c0082440e08016a49008078104481003a100240790143c0340305200302a00060a0201c90b410441e214586595164050b0044454110240e200d100d0440d028018a4075021892010700050100310380000306031280701d034510a04c860010340d0214600c04100d030803103084080031540440081c00d40c8030fa540054200712400455248111036000540111f907026001d8401c5034840d0001601d0003105244900700450b8000c0c0d414 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 718932392 1250 718931142 718931153
    0x100903032a11010e030f0c0c0a03050303010b070305070501060324061d07030e0a030e0f030c09010303050f1215121b04110c010f020d0b0d03081303031b08010608090712 74
    0x10104044102c0010807440101c0784040d065902410714212411000200303003101d440d04111200c5c1c1c20300250340890405140d615071584900041c040c030354040500088404c103242c0f140b410b5405454103d0020402565a4904500d9241180000b00b544085441b010340c1644d8561041c20116030001e55003e01c18410901540c0031528001d000b4814075988a030007501d0b0010400410a015119481d141e5031321080d00d081210002c028a07010380701740e02c509007010b22a220142040c2c1100d03814180203031a102c08043d042c03400e0044180c01c142c1c0344441c004110740a4a403459100c4a50402d0380c2f00340d0910700c9882c400f511008076801345c000e14100500041c0d407900b026448403d92550b4055914200900420780728251b0316204040c4000c10b4000c6000f50035803200e0b21940c0800341003203ea91840340203940d4040d01d1407100519203083d00d291520b803141454080e03000160403541c040d04441c403100d84020b024049100c03c1c082d0700001841c080000e010303602d0002d074020607142c40100b81240c240031079851 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 718933642 1250 718932392 718932407
    0x306041104030f0b0108070b160b151503220b1302150d0204080d020102040501021e070302040524092a04090905100507080403080a1a03100903032a 65
    0x180c104104001c0000400d900701d005608030380c4074081903000c0b54903002445107040c4c1242c01001c007141c2c007041030020141e4020440c08009600400c07024081d9104500c00342109814400309400c204030710001d00e42c20281900443c8600001106041d5510030744407140964084c4400061144d071101e4040b030385590401181036400c0340300520161208003006103290309504520030350080c40ea00032a040c001c141e41800300081c044103d1000f181801e04d4600000c0d40c40c140849000b42d0310240360200224010140400000b440d005042880b003410301100ca070300c00361491140b400c401408040d8201a5127004900079005801c00356004604100c0f501120a69034141ca011803d2507100b00b00001d0342c0d8a25009031507210380148042d10f01141851075003020740304010090340c10000840c04000020b80c000400d1900010310f40000641c608449240c80740b40c00070044030300c1d8144a20315041d02050b0064100340d40c0c0c02c0c400d5400f8880a441c4400034029421454080c40e01341d086c25a1040d00c65204100 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 718934892 1250 718933642 718933661
    0x61b020402070f0606150905031c110304050a030809041b020304050f0f09010602150f010608181f1b1b0816080f031e060a090c0201060314010e21030604 67
    0x1840380810f0071941e105811500250300210580c00100343c801c1440ba08a91010010a8150007078142c540c0c80842000c101c1e901400000c06100c11156070070703808081041a64094039000d8100701c805920ba003043e0829411403103001e40f00340d040140031002500d80308030654040c0242d400840c00c1c9801d000400032041054020345030060311180302d00c01035544100d181c1c1d0081ca400e40242000c6803a00306180d091020003403600c2e8815414500420225078059402d60744550750b50390121240385002c1003142071a503800d010b0040c8841e200b48040c412816a80a00b402c250000d0304803204640e00740003640d4005a03198030100101a40c1c10140209505c5001069500d4045000660941c0a42e0b24011a40c2010000e41c003082408810080d142030064800d0303000e900054a002803e02d00000000c412068a0140c5252540c50b5501100d8442c000d400c0100a50f600030000b044020707844403c14001c0c40345000d1400b0b2441101c0168140c0000c00f00350a140e9211940d02605c4c0d44e80d21024000034000000 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 718936142 1250 718934892 718934903
    0xb010b0f130b03040605060618092508181f020d1b030209030615061c020f1c1a13091e030f020106080c03030d1a040213030507061b02040207 62
    0x30100301c0c040c0e120020700150070301c420080c0d00e0f0705041c10082c04a8200800144c0182020408816060560700845c01501412a6610700d6942c6191903080d68030741e5507040e07c0f0304080c403c0c03010f100c4940040f0000c0c41014028261300500c181c903c01c960ba104014103801c0c1050f15002c20041c40c0ca4251303001481400b0b8031880106250494610451041c404600d10380b00207039012641441d248ac05004103504400b4103904c02ea01c450910000400c0c51145648071000080301c4606190000321503016216100111050380d500c03480e00a892840c00684120400344c2c02c1d06e8980900c01a142c082c0f030102807020058040d1410000440a48004241d0440192100191005c420002803425104280710510a6443c12403070449080b0103400c0d940e15070001d0905030026a100780075901c001007034071a45200d45401080740742e03110101c10103d01d03200304003d030400d0001600d4858104160100811284034000300c1d010a56152000c41d04490307140c65048800388c128100f1005403400d070b0094401640602c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 718937392 1250 718936142 718936147
    0x1d0a0b0409020304170406021006050603010321020a0b0705040806010806220c121529040f0b030d020604031209080f2a0606120102070209130305040308040b180303070b010b0f 77
    0x2c00c66403103400c01e47c00038006a001108a007000303441da00a480080c8425a102400c43d415a0b6500c0d0482c18079188819851188180e443c0c034582c42000301079001fa8100520305418103000d10010025446400b91038440e04c5820000545504c00017055403080320007892080c0000255440322900c2c04005205446c01d604581c3c021407540c20b8214502280b1388104020400950301c01e000000341c4410800f05a141c80030741120034458401402030b00b00b4408222400241409840c3d4030358010200040000e4049c4142084048210740000b103c41c0214020345440002a10b0f00c1000000c9da184001d000f4030002042c0702400d00d44000320050120315200207880302c02c22074140c01000180031141d07542d10055011609000c00c1d0700f8202c0c0840c143c3e0240400035860000c607070700413070717040300f406446c0b140c0e609107a40c5100141031090041c0c80107141c0c803440c0c1139a00e9079101000b4813903402014089071580281e103003e11040c5400811500b5807544000000e00340d0b0b20380841c3c040c041d00040300125400408 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 718938642 1250 718937392 718937423
    0x90a1103120a0c060c110c0609030a0c031406090a0f1203020d0903020115061814060c060708060f061204030815042f040513050a0f020a1d0a0b0409020304 68
    0x1000090b101d6010030340d031800110001c5003044000e541c8404011028041003111615002c0c42c0801e038240d01003c1601c0081d66400388002091821340e110f030303019001c2010700b04040200710350f8540e42900c40c10050100c0c2c1c080c0d140c0801d12510b581d00c842c40204060f40d408205ca0024551030829180365100e07040040c1444c03160300e50780040d100361460490050f55120150400080790404c19400390400d0315080407107072208101074400c503515020303501c0b98417940e00d600341c034923502c01d01100c2d02d0103407200546545091004000e40001401d43e1142c2c421201540c0c04841e1b824107100369601c000c06107009040c0c03615103450a81d800300780035000180c100d0b4074000101c1191541d02030301a0320700c80c1215803a048421901d02c208030744001000564001da08100400003907907810020340f207100302c100c070001e042d444280d4524000e080c40c00100c10246c3c004039152010300e412065649910315405a00c80d140d80100c002c00c131648074580a40594254244000d0201e01990790241d40d110780308621401b0800700 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 718939892 1250 718938642 718938673
    0x4030e15090a0803090d02010e15040b040e01090507170a270308060306100612290108090610060f020c18060a1a070321090305041508090a1103 63
    0x503150312400d032004005a41441414100728071002403408401441c00c2c01e88503000942d03003200000019041109140407026240e640c1d4680b48140201c07524102e5650340c0d1012268526007051207982c031542c0c148c0f070000640380c085000b0203211310000d564044118200d2140015002c07800303001303210390566031046c0b00b60800e01d80d4056060800d00d040141e5504d0300f030340f4000700440c80c0200314900a030410400c0c8421180407040d0441039620310b003041d201c59400b0845a4009100701d42e4200464841c2e0802a058441030214201000100780d03103a00351646c5000c2010f507600025500c0d4400f40765a040104042440b40d4004d0100a0b464416181a803003540001660403806401e0302e00307030708044028041306240c5402c0d0302c030081c16070b407a1254002c80402031641540c001e580c03003c0c047c060040700c82032083c6100280292100c0c2685405c010020160a000300160080d0103079440701c0c07195018000d80c83c0d0050110510810700c1d00000c00228669a40302120902d15500c120b0b09482410010903c010 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 718941142 1250 718939892 718939909
    0x6020a1101082a03100501031b0c0302121602040609021317030c01091203050f0f040b10030204090b04030207060e031b010e1f0f1706041d01110d060902090904030804030e 75
    0x3410350801d1034483c05c0146407480d54580710340c00b4605061070640b50000c1c00d003613010300c130752248441e050402c0419402c0c1402e82c2015507000214115490019a41c3e060410500820a42500a880400c001a01c0c1c20141089100c3c02c0c90140409004a004025501d69024508103520320704090301e0900c1c08850b461402e581d10300e10100e85180c1d520111146841e454420694003e00651442489040031010b510719140f001d000540100303004000164142d0003146104015a0b014100300076503009418111016141030701d0407401030040c82c070300140144c495490f81e40d03408001005002c25102e00c0111405001c0d040014a05119200003100d0303203613680042500c40030b40d00c9241c504075007842c02c9008050394041d00a280601800d0724441c1e041e1030001c0c20b9540c1c041d0b015580024a09900040e02014505603503038614298204581405078220710350241001145405060004a03120070300e072002d034014614400e400c007100351700290110b80318601158101d400703810210800d654100203d5a984d = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 718942392 1250 718941142 718941211
    0x102030405060d0504051504200a151205060a06141806030f0a2004050405060d1704060801170d20060f1e01030b1503010f0606031506020a110108 64
    0xca513210200300030322005008402d0034245200401d03a003458940c0d03400900b941d00ca40c0240040410075034104160b103480190001070701c9027079100030130000207980c001c000ea0103481c4000145410800420020f0800d46c0c02181551090384602440c82c40787c160540088c2c000814468501182071001d00254981d00c00840c050700340703050030001e1860704400c030341c00baa43c5440051aa6040c01044880d126182d0300a403001c0d074201702c07000300301602d868000484510364100040e080030340500020610640daa40203000300c40d02074036501c500382c2c0d0380c42d112000d04250b15241200c503000204481040e6100d10300812300c4905a0080ca43e00c1d0f04078440c81480d000301212a1041040b44030188400c0f42c1d03030074140c24030849169030302c0c5e441581103503541c1e030841d03401608944495a0341e2004420955081d0042490695644402c105859031040001d01800c20350504141c80c40c480e8001040b05072000c61301c070102c030790007034083c0c4090301003100110342840e0000c0603030035540300105040c610410105c0c50071024 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 718943642 1250 718942392 718942417
    0xf030f1d0d02070e010b070b090c03060f01060e030a0b041403040f06090608060d12030c020c04020c0c010e0d0812040303020415020d090503010c080f04060b0d05070806070503060618010203040506 86
    0x81c6280a8042c0c500b1240340c000440d03072000180104024045e600464490550000c0c801076607840308250300c0d103088440c0b10041d5050040d1004c00606000700400c2904844055076034002d01d0810704181502c50041101c0a000100140002030101c3d000f50004c81d1044011000ca034a0995240c1c040045516150411000030301c00f079000700501e503445802c090304010225081d001e456250303500c843c0e003128840040380c281501c030200d6031304180c002d0184420712032000e130040d9540c40350445180d860300e0000d150580810f007801420006e6007440301c0f2012050340d02559140c50f06510345640406a10000c10031800c0503001c01000c24052241c00311140c2d080003a8000300800909404050622001d0750805402a8580910101d055901030004e0350821240039003103025440b2800c0c0140503180034043c0704c0d0450301c2688290104540020480700301c0300d400c8151644e5840e0f10000b21018442a80c038154008010b101019070031425005031403003010140101e070b15007941c8102180803a08410400b205 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 718944892 1250 718943642 718943653
    0x2180106170115020d030b06040b0c0601030c14060301290d0e01050a290a080f0304080111073908030d0f06050d080708090d06021b0a030f030f1d 64
    0x680648108030a01500490f40b000d40320308200c10000350340d088151007036400c05895800110b241d44418080b00c01074294041102e030ba034a80f0711003a5985180a11044a6198026400180c4c00300c040c40c0c5403070010b80003454a13103164608440c9041da20301c0d031110080588030348030f0521840306009c001840f810107d044042901c1e00002022401c5640090070404698186000a000030044480d4002071035807600358040002c9d03030207000c180d020085803c000514464103510002c0c20000002a00441c2e0a08000f801200c03070030358003040700d8050b03840b001700030250b4204403441030001a055040d40005880150000000380320302a201c408441e401180240c00014509917280918011008845001801400f90500d04400b044e1070909217207010345861700c0440c50004001d13070001260401000100184444441c0b4140700d0000c0d03100b401c18100840d23410041c25000c0308045810060903806071108460f1940220055024001c051908110300b981c500c0100ca541c035042607955102400d0000826 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 718946142 1250 718944892 718944917
    0x30c070b3103020d18170f12030420060d0e010f05042604140622031a0a090308011406041205070602012a0e0d060f05040b28020702180106 61
    0xa0401d06010409020010021400b00e0301050058410044a081544200440039240a4907080500c40b502507066402107010303505203000280055406540070b028008151294a04072f20480c058014240b44c00c020705001450070703440349600048a0040c104004242c4070301704840101226021281212130100108510041110100710103030807030380000742d044ca0329040058480080e000c031402e4034400d8800050040552400460003042000302c19505880c540d12880e1421400c0c0c030904000503a0711034140081d10706c02035406062401e9415403548590340c4d08042020030142c000c0c4411a812000800c00082d91005d1031221201c00c5000b41c000c1c141060602c0c0d0003d0039902c40d00d5001410b01a417140200001d407440b40c43c0f40d4210414204103071318198800205190ba411848c0280c180781c03410120b0164580070350402c038466441044c4a04c640d940c4c154030800d0745415007400441003120b828040b0703100d00f00d6900802007640002c0c640006a1017000390700e07072200426000200002c84841800 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 718947392 1250 718946142 718946147
    0xf011401030c120908040f030503040510030212040609111c1101030501032001170c0307170c07030c080f030c07141b060319020406110f0102030c070b3103 68
    0x1009002441c00740058140c041c401007441075400d000942081c0d85041050401114000311303401014203010340d0750481e90b41d042c030f01d0302c070b03040b0f4480e01d0b00a00b041c501e1428581d200e4800c440029028882009a0740c480d0b4036030000402c03400c24125005201c02501d02c11661314221410b447d41c0e222641008401078a16054860b03004004000d410b05050030010300016400c1e00350108801044018040380102860040300e00b02e00782e80d44600c980c02e644061091800006008521a43e450788640c0c401c514254801c082c8020100d8100ba48050700703000d080002841058a48060b5003c6c4860780d0804102402d4901030b6882540d040b640c81a0000d5a41c08004020138a0902d0401140280c000c0c074101c1040000c40a80302507160f03114a034004001900380c24288540c112400b04401c085490300d44882c4082d080d030302041c40021980c40780f28900c5030701100500840707100700510850181040c030340d940e44403240c80c03000d82000022555114451050001400000040070580300042e030742e51000c0c01c01 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 718948642 1250 718947392 718947419
    0x1606030e1e0c0420090d0807060903030605240d0c020f06011203080a0e03090d0204020706050f0901240515040812040e09011b0e04060e040f0308011e050d11090f01 72
    0xb0400e0a800401900c2458080d020945e03100000a64402110390300600d00114548142d0340002c208501e0032002e1814168160b02c0f031000e403003080e1030f82070078018421002460012000d141a0400d041040042511300054000340d241c80001d004035041c002541e41240e04044098004041c60820a071654050682c401c40d0240c200080c680104510b008000d40c0302d849204490b00d0600076003a07811a1421512240e04031501141c10850801007400c101c0040113240b41c069841c20515800c0102d808100300c5850b00d803c40000400d248800c0b40d03031500043c000c6045045880c82030000c0103000000d811641031040c002039144d640e103040e69460800c030744000f030769502414441c0c441c0e140c540f681e00d0403c464009040d00400030b081848000c4008000a406003c80c1e4001510040301d01c1d0520040140c0e1020003454a88262100d1441e40c0c0c13592600c000d84444000071240442d40120300f001141030101041f1b1045006440d4078441aa9810214802840c10340d0f07031010907070200004000c401c181c0e401 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 718949892 1250 718948642 718948661
    0x5030a090b0f0a0302160b040c09110c071a19090518040201021f02040906060302090f0102060402090c030901150b070312060506040b0f160b181606030e1e0c04 70
    0x49038280300080c89000020b00443d01d841e000c0c140c1c00101c401c00d10754000c1030030981c01d82c0b2116480c0c00c0d260a240484004299119110380305090000c0c0140c01c0e030381142a1103a884080004101b51441e00f6088206035040c4000c2c0d00e903603041006041d000048001040f015005a5103d500840e4603110520890500444500101e07402010074040180c0c0e01080000b44c1e070291031100041c030041319400070024451980300e01c945514100d000514540c068018082d81c003411180c104d0381d80c81032801640c5401c800c44009502000020002e10607503078079800f550b0004483c4000107800011a1105090304045400248a03d8408914902055401800300002c0000001c0c14058545840003103030245c041c070b0294684010006c99451203030411081902c11150507501d04103074100c0c50b81000c00700340c802a5883c07100301c030704c00b0041d40350303a0740005018403090103034510300e03480714a007074030442c001c0c412000e4203066801034010151500a042002920442c2540e0180a0b881180304c10881118640c00 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 718951142 1250 718949892 718949909
    0x1707050a140601030b0f06210109021f0203090105070c031a0402040510060f0e0609060d0914070302060a030e1c02010e0d0305060a210f050115080a0b04062705030a09 73
    0x2c00500000b03c00140c000d401144110b4005000d0312860b000408041882c403410021024a00000c5e5410805400809905000f52206001505c0300d042102d441003100c0a0a400343c1c2c82040020400d501c0758004141c40e90040d05000c040680300c0d038900b01319a00322100c3e14020320780c01e018032080d4034080c0319458020b81c0320075140e03040516082d0043c015510740c030003040c2030082c1900c0c00c45c00c1d52607440031180c0c201c04c011b0009a0300e8140c648020024100c000e000d540e03500c0b50007000c00c0d03a120002182e605a03500203141d54185581014200d000c0e00b041003815050740a008228042035502282c100003401c0650000300d401e50017902d6551034082103054010425040c0014400c84d5100e0712901c00540381d109003000303a001001e9411600c403034000f01c402099a45c010003c40c041c0b0006511000b541201045942e00c1d50782d5408402d5a54040c03000041d00c2d0b00c840c84085000550b296002603c800b02ca03402e84428890800c1200d071009190120a54940d00000355090000c2e900c0070781e0101814485 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 718952392 1250 718951142 718951153
    0x80a061b05161b081603030e1516230604020108060a0605030a02210a0b090114062208030706090b0c0403082502060f0a080a1a09041707050a14 63
    0xd8844481112200d01030502c0c800c00311414000c05041078075002611024003262200980714402201701c0d110b0707210035400602404a1244145802d40f101d02200f000701d50701500f012400ba510710070500350103104940c18005080940b40b1a2200c01c8840e6601d0310500280085250900015284281c01070290b4807988207818103122003504a001c0d250044540c24005031039000c40d5a0b16111026000856082e1900d08000c010000c0c0050b042418002d070180e9000c5056660740070006004103004180d41c1d8044c4041c022621410100807121011803944440071a5060783c0e10455400c6d540005400d542140d00d5548070740510108910300381d0401541c1c0b0320f05280610310b80340d4003070034040e004442d210080c5c00e04045070b441c90320701c0c00c1015040d00104060366610480340621029401010100007007002da10002d00300342d445214500c17050f440d5015160110102400b008801b2600400496a02c00d03c030100c010a481e4100241c258148150300410501260b406e024502a030019403042080e03005 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 718953642 1250 718952392 718952407
    0xf050c04140607061b0f090f120201090b13051806090c160c060305090606030c010f030209031501120c0e1003030f1e02010213080123060109080a061b05 67
    0x145048404590000701e24400c42075210001903000d20406034058a00d42c186007803011070352501140840c5011268442840301c00c480304043c3c0340c02004d07105036a00ca0610900401c04c02d0400c0090081461052418015032a10f4800c0c4030034030b40020f10813620807600d503d02444241400141274059142c2c17485c0d81c3c030303061800c2c00004002d050b0041c5202c0c054800070580c0b030800d6450b00012030070158001000c01105032219030007030062100329885801440f03264003280d10fa0802082404801c10180d541594202c8042c0f01030f40a94400d86a0b13903014456411164001d4001c0c04c06103020b030090160950760b103421070500106038186600110b86e050340c00c80c207000e0302948109000c801c50342c0c1400d085d1004001960b094a02c40e10400c11204045201271040441076410360003419440c00048102c00c0080c1c84550325070894a05420b1074446c80ca1074500c05c0b0034000c021812903400101498a04155925881c03080d00f400c1148c041102e9080d2a0380c0202587d00440304000301c420b92a14109051450 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 718954892 1250 718953642 718953661
    0x1602070506090d1a0106020303040c1d010b18060708070501243c0e1501050f03060609031903030c051813020f0a0804050c030d081f03020d08030601030f05 68
    0x16070b00c202445800541d03584010000c01464901410b00c0740e1840313040b0b0750785d00c4001a4a0754022a011a58000c000c4004102d064162500070f00b20800d00300502c05503800c0c075003c0c5903513500035550058401da2071154200f0656074440108000751060002035140d1203185031a609450b00304107544030381122000707014040d86101c100c1b54100c400a40d0300001105140200f84c1e49110001c1c0d041d1610030801003000c40c4241d5010813042114071a80c0c00e28565901c44183c1403003681808030084c00160700704032100440e0404806150400070081c5000c1c50214510002403808480070840c05ca03011426000d2424160107100c1d0180002c06810410303d454544580034059a203240012403241071040411011062542d05803041c0c01c029841450b50b51402c1080a049a403040320102c4042c410045518518240464100800102d50300c4000c901d40b9400343c6000c02103803c0940600070349860b0b0780000503a50f0066038104250092500950701d040880004003038504550fa2082000d003040103000d00e100 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 718956142 1250 718954892 718954897
    0x2f090a0606050d020a03020415030b0310020a050d0b120d200a020a030213270606080a1a1b070303020319060e01090c090512011b1b030503060409050d02061602070506 73
    0x83c2c0d00c0300040c0d4515901d041580240260340000c0b64110311802901c5882d5056408021032140c21801ca0b420803080c0804030003a403049000714000204248100c113102c101503003004030003080042c5182e20704036003462480c0c544544414910300044c00140400340c402d40240d81c0400700900c900203018101096000300320030000a00c00240a5141d100703002841c1c50695101d030401001e954a88210785030070800c0c400690144200c29510745280160000c2c0c1540002085144a0f500c00389156040050542c2c081040c003005040d64540c180c1000f880302111309400003000342c070b40300c0d85005840b42021642e086407884902040118a031412100f884200e1011104504440900f0404141101d111104403405201ca9208941111052079200694101034110207041c0001c0d8940e01030125009808a501c910602c100d4000c8039100b040c200d0200340310300000c5502c00e03000340c408200101146e603a603282c41c2500d400c440058000b4410b0044600b0340441c01945201c1d584024803425080800103411072 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 718957392 1250 718956142 718956157
    0xa0c060314040b040312091103192a0e040c240207090e0a080c010501060e06070b0604020f0913060e0106020109150902010e13022203050a0209042f090a060605 70
    0xe0fa03894001508252207101000346260300d813101032081800c180f820b010304002c0c80c00900e110780101845090b602042101e6210703021f4104804000003507610428102441009881d1240310340440c2d00401c4009401e81418051781c844d2801445062905e940c4030194062484c82690b0045007075420010036030300040281c243c03005400c0009000354182c40c21468a010080001d019903c041000c0c646443d040d44064101c0d0f54949032401030302429000c000c954411207030010b000441040c04a0301900b0142e015041c1c07803805d0f50100b4a4810004c000990900145040e0307001241c03a0b150a0090010300d01c8254010301181c0024407480400d542c03110388001c0c4503c0d03003911440d03035090900256031003402c1000a10801904007200725400313030102030280d071100c00c14a0b1000c03202c0745040f2240038407019500c1103942103000342400000980c00c21401d9030001e030081c1d444000700541c40d22440b18070508c0d0524031003000305030340300c40303000105014140000800d18190145000010405181c10800f1140c00 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 718958642 1250 718957392 718957403
    0x4090c03020a20070503070f0e0906091e0712060f203007020d1404060e011211030c0720010804031101060915180902060d09080403140a0c06031404 65
    0xd07a4050b003e03946410510b502c5164584104400001c0c4014081d201c1f0007500c0c4404041120b5035207a40003159189001d5420b5045e541c001c01000c5d500031507072000034520705c0034201035800041c0da170600e10b606500c8081c2c060350010703030ba981404085242441040001d0b095589210710302d02c1c41041c414424024a40c001c0114000842c0f41d09802c1055001c22610120a4174402001c0c202600c000350b8070b0001d43d9211022030b075094a08a030b64403101c810b4034201e600513581e2152032003c081c011a100c80040d40c030114a107448036685d00e442a140e0014610440410040d81d454000a0820001c2c64100c08111003580206940d61005170346e010020740d9000f50035007070203c40045201c581b9401001035a01640b1801d1910400c0000040c2c0c9104d51b10450b0980c06d0251800150081c2c000c00300c0714100c6000394002410450703018866504d400004565010381292810180c1e030741c60f09105c4459580300c821700c5800a5408008000c200a20100a40510300c1d0422118040e0000c2811115010340007070300 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 718959892 1250 718958642 718958687
    0xd030e01150302090105060d02070b09010203100b030402060307030b040207020a03150f0509070501030e0a06090b04030e0402120a0e010b0d0507170304030c0603181a0402010f0e0607020411070f0804090c03020a 92
    0x30203508d40c040756001980a00203060916001000500035001038605540d25a22070030000340794460401902c0c01940c0040030035103143c4620906400070001c018500d500150280b14000160b901e82c00c0c2003000b18002e0004080c84030230000d00c07808480300100f40c1107050b4a0302c2c09002440c030b4005141800e407031081c00c0024052403d6000786240210b40c41004103141e051003001c0041003102c04e8554012407181d11105900f84907441048140e000304095800320302d075003200044440e01140c003c45001344801000040300d04a0304082040040c03110f409940ba68400c41c010040c3d002603098008401d170554010318105805c0d40d807030207260300182c8078880c101a1141c8850048180c0ca072000d1101c0c035441903c50346400041003c148068100711010b9021694541c0300084460088807502d501e1040140324518060300c46d420000200302c1a2900c1c66509000d03c6030000041640105121044c0200f440b182c1302e9181482c181e0a81d240c4040c140c0c01c1500500500d4101604842c40030700d2044000c40448 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 718961142 1250 718959892 718959907
    0x503030717181507050712021c0213090b01050f0301020c0303150a180b01031b020a0b0c0c0303010e10080c010906030b120304120b060d030915020705030d030e0115030209010506 78
    0x2000000100c0b5090b4060542d180c0740904440160041080318400c4003035031400e41e0358041d4200b03200d0120102170742220f410300340342424110310440c0350000c610080211110100001c00b8034200c8541d00c10442d080c150b40d00044c07065242500c0d043ca4245000c800a40c5003c031017203485912404007521986240d15a120741c0e40250740d4928400340a000c00350215003c064501e8040303c041d007990030786503020a141c9100031103040d1a00c020001200b000750000c02d010042942c6442010800a19546019505102e01541120b0a1000b540240620500f00c0c0d45810040074642d41001c26510641443d48031002c0b50340d085c0d8108254804503240c5041c00503810024401103141c415905007503410350702001401144600c84842c014120500038180c842840e40d0b0102441031002084c540a404034004100c100220b0503009001000780800307105907450555103601207843c15a0803140340000c2f030744521007240110780c24420522183d03040dc00c040b06151079a000b055a00d1410300459004590005400 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 718962392 1250 718961142 718961167
    0x60403080a0504120614060d0507230904140d0503070f080402041b050a0909050f0103080a17070206190b150f070c030809040e0708060f0711030c01060608010503030717 74
    0x2140144802107101c130701100c00c2d1611200034188001b4040d2485403210105071541082d03584410302d164070030000c0034030a042c120b4034149200302c600e41503c0c1e50300101c040192038840c4d14170140035611070f02eaa54031035859118101d01f4070b2a5030100d002045014070802c07101f0341c2d001000002c070392071608151045031503500114000c1c210401c2641396041d40c0c400b94211656018004082248803940c56460f02c0381c5401c2510281c440030b079800800707801c89500520110740540c1c0184031003d4141462040c6001100302004d411400f00d5840340540c102c0d00400121070751701003095052151036072003081100205400580c040b0b052140c442c40850021880e02c807040081406c640003590041041c0d54201c0c2d680c502450b9a030700064115000707605104d002c0e4410200018504141c4000350301a0100d0f690b00403080e107031518024003200c100076004c06900e1904400784003e04a4113804400814042e04001d009449003106a1107580241d004005107004200d14074280612030b151500002d036113480d0708040 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 718963642 1250 718962392 718962397
    0xf0f050a060c120e0f0415050906010903020a050906040b030a110405150d1520070611070804120203030d0e0c04050601020d0e0103050a150f08070f2409170109110f060403080a05 78
    0x142500706c2c0c03401e82011a55a46840d40b101110011151030304642d4958004540b024446d200013034105800603410f002da80b418014140d0b0180b409040022341e18031100000c2d1802e402030380d040d9000070807885000503908007809907941c00b051042e44001080c51010200d01c0203013069201030410340510038200d103000c6040c2c0190041c54154441030031a00030382c0844d50b502e0f40c00791800311030706403500014506181c500380581d44444d801c14121403c1070310b411301040d004040070108990501081011010705942031162100c0c4403542002080c0c0d100c0141c09000444401900d207606540c45500003045040d800fa0005504500c20b02c1c0220703a41d1180f0001501500c100310501d251004c5c98100800d8a10b625000042140c1c003180c100c80c40103949a295001342c50b041c2c000d00f0401c8510300f401c034a03011036003401c1803407042c01803400141e0565945208000c070344803501c5003003560351034401c00e00500809158041c2c400c607080f90400841f900110011303403180f20394070004000e00c50100702d10b058903010388107 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 718964892 1250 718963642 718963669
    0x5010b07080c121908100b0405150d020a0815040506030c01140c0d0f02101a100c020a03060b310b01020a05060a1401060309020114130f0f050a060c120e 67
    0x6803925214041d2251550442440c100070019105e400040c4044502ca039407402240c044032500c40c5014240414000c100514584202c0146020008410382c602c0350320041207130202c1540d902c1c0705402c110400310410079078160030034403c03420081480050f5402041c104c490356403d00b84401205244410f07030a6174000d00310305140c980035031601071f800903420070000350010000d81e00b506c000215100c0c992080780c455144160308041200c0ca00045801d25407001442e40c00c49091942c0020354070390004410100b00d4000701c9030142c4400640303442d401c00340388401e8001a0f07800140c100f2141c44c00440c6c2c0c6500c1c218007001c8443c3d110940480264000d0100d1020a5048801e448a0f4030305200b800c00900b02500944240000034400000d089200344580e08482c4e5050307581d030403000103481c107070262034028a0070a1005aa6510005030400b07001d000c2e00c005241001503440d16174904002c009000b842503016000740b10540910500242c0050032401000020381011f2800344188030126465001410 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 718966142 1250 718964892 718964923
    0xc030b063a050c03040b0f0906010303080402044a0a0803060d1a06090a050103021f1404030f171c0903030b13020306120d1709010e0307030801081005010b07080c 71
    0x20a20000051103c001c0d4481c5005880721a41030301c901440c8a02000201c0c0c00c40c106d90070040c014000207200303410140c0c10900080011038565030324200d9021408507036000900d0002c3c01e40c5000d80361039101e40e24512014005c1c50015240558418a58448605050080c4161000000a4010f0b0f50380e02e032458045270041d20416000484021080c58054283c59032407048022000082c1540f00500a0074103895000c0d01d2076030b040c2c8814481d41d0020010000034414440000c0d00244100e03aa50080c20055014010102c200d00c01410302e18415615050f003000841000c000c001c45040b050080c070840030030f180c1400a24400c00703044c11401001000c03201d540c80801003c044809a0040d0090360107543c0407200039a99012020515564909a048202c041200c0e044205883c048084036598083e822a0010403010b207143d20803401d60340304100c110080790090005020142082041210904903507070100804c5d418150703544007034021134000400e0183c1c0004c184180b0703101401010070441e10b15 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 718967392 1250 718966142 718966151
    0xc06090c0315050a02030408040504050403020f0d020d09080714010c0f06020d06090e0606100f09030206040308040305060a090804050906011809020c0c01020c0d02040b060f0408010c030b063a 84
    0x82c81e00c15050707080e01d28880012400d110124000313408a100722800307950720660f0145411300c1d100034440506002001030303040d400381400c10f1034510030030701c8414219070240e40582005448004060007218094100c9441d60703000d95014440c8131030348544640d0180c0309007842e2110070070b00d180a0a89400180e8010501800450031001c16400da07080042034801400c800c3c0031320410201032a0b650b010880c1c040d40d000307003c0405045083c1c050112803204021600d09600100d4890300411900c0c3c1c0309134422201d0010010b020030900400340600c42d00489201001c1c00903003e180c0790350300140124015a8405c0106502081d510381c0609041c580800000703540200145da580d95410082d00305480c1d0440c54003860700002802e6101081c803280108000300200b41c000815002d210041c030068070003a4009604200d001e507180da072a80034000801110001080c0f4060030300c00103042c1ca8011544d180280d2091040565404a001d404100c5a42480d9020b08a15100948800070340c0c6d14140740d0a0b05262 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 718968642 1250 718967392 718967399
    0xc07080111130501031b0503130807110103060e070206010312030e060a4d04080f060403030624181203170f060a0e0a0230010608090d0c06090c 63
    0x1440908010268110210322543d07694006400f542c4078111880d43c0141480c000350f07102c42c0680c029540004280b04650020007041d584c94070306a000503002d8598100d02000d170b50056a05001e080c0141c07140c50030301c50460814400c060354805060000502084480380306e01c2c00a4071070350040c01c00b040824101d418500341807400000038003c81d02e4400ca417a00746c0d001c600d420040307401e0f01c03018030600300720004940480b800ca401d080c0403604020342e0758110070480058040f000300400c11041e260403010782440d04081c50080c00702e03040380d07110544150041100700001c1405200c020a42031807402c10f44607039000300b0719082d0045e03d1600280c412016581110f018180e1044814042070b41000e81600703c1c3e2610790240c03042ca41300304d0b00700d40d00240c00c41c2d00b40180002051015001348840001506284100720501001c8a00380c0741d022030711089099198041e0342814002e401020350341421241c0d4102a4203442d155220072070758a05114941442e00c0822410398410100181c01070039100c0007544 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 718969892 1250 718968642 718968671
    0x51909080a02010609150303230714060f0c0f0a020a05030f070c1e0b0c0a15141303022e0c0503070f030e07033002070603110403170c070801 62
    0x1c400380403001503203803030004a20501c25102e89088a00001c200d031a156240d035504031200703d5a0800100c413803031011080c9041581007405003071140c0c441c1420038034451007a500107261000c0148040c80b0b010710318080c04182201c2c002110007121a030030115a64213040c81080c0e18144c0d60141c02092407100095505000c800c04002d400c0071072080725008852030303555903001a14452900e100d040a001d52004004000d281001024903107040782c140c13041284561981e100400c614440072204a03142c8180c0c0c1000055803a0666012030140d2a81074480d04a450003903942c50340c003031040c440303a0ba01007400400e59032005c0410b8040e020008240a035000e5483e004050360400d90301100030940c2120301c2d58440340030740619069031a0040041a10307515546800c0403c0c0c030209140c844482c808220a40c014007210040a03e4001d03c1d0010407016241c100c0040451307502150b1019801c90500050002421340004800524281000191507010706000d86081c100d15620400c0e071036107403180c221100ca4 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 718971142 1250 718969892 718969897
    0x30c1b0606030118050309093c07021f050a1113050a06021504080a120c03090b06040603240b12070302030d050f0306010c080d0e100e0d09060305190908 67
    0x403080c2c000b0b000903050302007012241e01003000014459041840000700504001441541c07085000da4500305d01075585801c0c2002001204081c8415203500d40446c1052024104454010400340300070079200c181c40004009401f6005940c03494251100080740407021250843c410a0b92860a000d5031002803000d094203002c442d00c0b48034050650840000380c0710f0b0022032881481d00c42c14110440c0741c0d03601e9803400450743c0100080014840340000441c07620f801807280400b880843d0320001181c0723504d03003400700c0790040042ca4144600e0070b28005100060205190242c9610280c004941c2903603000d9010005c0c010300041c5d0350701f04541d181da5006e0307650000b9101040364000da094a080c4c0310014011078441c42a240440040e5004001084555102e0120500540d00810820741020600c0316803c0c01c0c1e40c50700c52001513340c001050a282000302c6d1284d2140c81e4002070080c501640030280283c030702000c41c070420041c195108001404a01000d41c981e41c07441204004100d045400d00d00100942c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 718972392 1250 718971142 718971151
    0x10e090c100306051c1e021005130e0f04110a05060a030203131e0b0609070e0d11100203130801020408150a06050402070c0e06010c24140901060302190614030c1b06 72
    0x4050600c00813000e254020344606c51a0041c0c80751010b18000741d010764441d80440310800c00040c010700e00007158105111102e0240d4180543c0031110705003400c1400355440140d16851007403000d50400c001e2640c0380320480d9088541410b000d82ca80d5a000c4914040508070140907114900f0b5a0791905080d044ea00340f410013504c174414802e459141c11041c0010484216803200c04901c500d0a41c250030b1406903141400b080c4148a070348800c0260344007007100211002105005070f803002c551040803080e00300104000c1c062000007142001c3c40c2c00c506960320111403d0030004100f200010400b03031056604040040c6c0000381056555410b2850b00c2c44403030909104a417003035100030020610717641c0704800175000150860781800e40151081192a01c1d100b40303070200c8502654035423440d040d00d18071855040c810301e0201c0001581c80e25500500203008070660b0407100d4035160319024083c1c290007020508940541d09030040d2660b5403004900c1151050040c0c80f032050012300c8500c29912800038145100307 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 718973642 1250 718972392 718972403
    0x6110712050d0f1803060e010f11180d05030f0a05040807080303071b0b04021002030c15012402150c040b030a0b0a1a0304020f041b17010e090c100306051c 68
    0x2843d0030709011155100080c4c00801515540042000440c040d9000a410315940000014182401040078011030351700c20a8815482c0c404500403852640c1a07000050340c020503030b0307004244040c03a83d42584a01c51400d98444d031100200740402d51501c200c1c1035030003600e07140046801858542c40c420350b607508100c07112000558154401d03c000f07e00354801c00100313580220020705c962255401c0101885640e1003800442c401400307400e0003481c0800c100c003a0080000f104902da54101aa50102c2440e510b0005d80d242000041a92440d40d00041d501e9502d160f0349941015900e03116802000c52180e54030034141c0c06000b20901c06040c260341c1c89001044002c542e00004140d46071072903403802c0354401000c1d030718103410700010300582003003182054401401000021010b9490303003c00c9a048500c41208001004001c6c540c1c20b143c3d0400c002c0c0c0c098030600314004643c0c1f401209040c0e0704c0c9030356014240201c2d2048100c00100d4001d81180d03000e080000c00c8403101d2101c1841815a50040740300c00c0d0740 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 718974892 1250 718973642 718973657
    0x240f1c06091b0e1012060c0e1e040e011104120215030106050919050a0b0d060506030f07020c0f22110a26011406070c030501141905010f06110712050d 66
    0x201c2c0000380c0a541d04885c1c55040c80d60360102c180c2c550100030281042442c09014402c0d910403541e5503440c40b4026078850000090b40c0c9410f816080c042190756052007440141c5c90178050740c00c030410103819241100c1e00d07581201203410443c4003180c0242865642003a1200010001240c1d0382d8224001d012060340c181e51010f00700740f0b80c03002c0204c201c6080c8aa190011101c103000d10682031040002c00100034000400715105580f400402c0b50343d4812541d50003031428603020f02c21016414811130702030420464000c10007803c07590000e030080d10300303421f9022040c40291b107400703054120b600f250151003101c86007580c89031440c0c4400341051403003000f40d100350094107034103c0c84181d41c0c1020505898071102d400700990010000d101711075000400640c0c03100701600001002800c2401081c0f0f20105540b80c0c0d500b1400e100010000c60031030a602040c110341054014000e059046410000300c1d8020f15008641d40c0360345042c1e604000e0319800c80d20414941d01c2c580410300200092240d00350314250303280c1d003 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 718976142 1250 718974892 718974901
    0xe1905040b160f231603020105042a1203030b04060e0907050d0b0a0506150c010218030c01080a0b0103020c014b0906020909240f1c06091b0e 62
    0x102c070030509100d210086140b0700c46140e154034020f250350b003044c65810a85881c204000e0100a6a603071111801c40050b03446000304400c00c2501c1070a4680f55044d0b41c04101c0a80d40000c801c09071100078010303000840c0142c243d100500d40300e5004070a12900243c020000e0541318288043c460f2800c4807403414078440c03000001014240398034501d042e650410000d8007240c44030303841c110140c080a030100b0352120305e0b040503c9a8145010050400c41c0700c1600042c0e545440b0340005050f042506002d61203500140c0d099629070f40c20400c80b9600c40c81e415000540120140300590003805020460b00c1c0a61a000c111a10020301480302c48030f8001e62000c4110403030000300303071030150034035208410006501c00405000499141c0c01c002003040c81003102605000e0240b01240001a00303c03a0039021458801411300c001c112400e000030314640550700070040388101c1e80444c68280c24034001e98104c6403032086c0b034000d201056100303010300c55101c0c0403040da07211618400c4107210210300554201904080200f03 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 718977392 1250 718976142 718976147
    0x7050a02030c030f1903200f010510080c0d0c12031d270c0f0a0f090e010506070f0206040503120304050d0c020f0d060b0411120a0207020a0e1905040b16 67
    0xc0007104c05440245a5404540d45078071905a800c0d20441c00e004e44448008640e81ea0144032400c0c00c3c2143c0020100f41c6040040301e401d48401629260150380c80c00390900060002040e0460000300c1074071080a040128501030703d1450f4036038001c4510082c0d140c19041010350200e02225012800d0a61240310509041001800c1c00103c00c9400f00800c01c014038108150280c6800798404910303a200703404c103460714410100f583d1240c402c02c1d0000c1c1440c009000340316005940d03003014203480d19840000f5070400b008190984169003000d8108611341c445c0300115903034041181c2c01303003d02500f9580012040d03a003240c1e80d40c01c1502c2c111074070f009050300b61001038464050a1500c0e40c0003030424810229181c207208100c4e0030000180e034900d8945d150390441707480317502505030102501d0f0310b100d41d1a0414100c003016507901410310300c4101c0c010404400541da80d450000b0540d201190282e42e161581c0880034441d1410804003070790241400c080000b403001032002a88101c0500480b94855403010303904 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 718978642 1250 718977392 718977403
    0x1005281a180612040b07020a0c24030c020d110304080a0609200907030b1207060818030c0304030303020c0732090720010b220629070c0b07050a02030c03 67
    0xc0d2a984100b43e0010b03010540070040f16810100c2070041e5060300c01d640c3c41d50341d4405119000b00d01c448a00c2d424010303c6603084030104a1403034641c034003004155207042e0001d40700d84065100000f001107142c407807414008203100711401025104102c0b42e00340d040e0300d4010040d00c104c1d80300342c90b11395030740b201d101101c03250b1110154a503200520f40c1d46240d6584400750020501031680700c0d00000d0000c54500d03c1d6204101a0020701035039141c0920fa850f201058004c0e2a41c8010080750b240c01c01c0c00107003800c83c03000082d60300f5254107040c05600d0704009007036030789496100c3c3d000856030b51342e45151420040e4a51000d41086800d0740c050039101010340107100468009072142000030b01c03000e148406000ea03100c69681e4103048140003084000700400002c0e05c54642c2c00d03013001c89800301fa80c8181106d074688107400c018002c0d44c280e06400350701d102d140070703030074001408007050508000707482400c000c3c10700f0104015000080701c5948130042c80c10226a10303a0054000c80c024800d07a600c50500b4500040d1 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 718979892 1250 718978642 718978657
    0x1061203050f0d0f090605090c0607023007090603031205070f140903010e030310151e0509090c090f0405060a030807020609041e051005281a1806 64
    0x101c161030895440c0c50902268008211888410380e9854500c032010342901030707504154055000802c040c20410b00542c01c1040c041c4d1203c0c031921041001c0801a1030380440c80d01d82e80c28410f80118501441060744002c404e041e40e04080f54006e146011900d50391640c8a8020b0382d000340c2d0740e00a0302041c0c4204d441110416034120000c0b0f15000c80034480d0394450841c440610845041481c00c002400c00440c1c00c0d0340d0010350082803a0804010414461203843c50440180380007140c0980030313040c1c07139400340c941450219004042641147c0300c5881c035000c1c0c411103540210213010201c503490310118100858110030300c1640b2845d10031030110118a050b01503c0e0182100920048603d440c40d65113149642c00100101c3e040032040c0402d6040f580c4902c03441b5002d001e00e13260b03a0390680f15500307141e08480c4010103041d81400238a405201e65114011125280e42c802501140800c5441e0b9268003420240d6201040c030f0495480d00d00301305405840170f070949080400c01c440707804151404000c03190041e81d4 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 718981142 1250 718979892 718979897
    0x2210903120606030402040e030d0b090603030a17090c10080103060e060108101a060a05040e090307080703030203130f030203041806050f240c011b03020901090905090c0901150201061203 82
    0x800314242c1c1c80c0880c02582c105100400000319801202051400c5801c0041110041940c940081215050003420980e201504801030b5103081040f810252019031460000000901d45100040d0450710810019482c00c900510024031901011001030540c0b109000c00c036600e505040000000d9000010542c0c1030b0f0304813002a05184010360710900003021203481c0b074860200460102c99098a03550010044c075002c0d070b61641d56132800c001040c524120080c1c0f807042958010018400407031000c6042d542010b50504c2c3c050307900d407a02904e5000c0c6184074100500b11440c00d039030070810503800100400c00c540f015030020303d950ba0184503950856041d40300d500c0e008401c14851101d04d20300107040700709034445007080000005400580300c2190b0800e00302c82a661b0b54a4941c0c400f540760b1680c00401038116898254580403080e80001c00080e00d510468110517203c10100307544500511801c940c00c01c024010318010740c2d607151b403c12807100000c0440d026500e000c401191041c2255040c030041c54254 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 718982392 1250 718981142 718981177
    0x1801080618101e170304030812060a0504021b0f0c1f030e030a030b0307140105070f1518020414071409042711010518090a0f02210903 59
    0x40000200c68001410070185041c000300114030000d549860005003c07104100054890500c00051450030100700d8805040d4001d0001b0800980c2000481e1f1142e800c260340d01c002601c50101146a08415410141e48103002050701107039545800e101c00321040001c8101c076581c07281c0b0034410f500c4148419540d07812010001021040381d8488002c69200019480c00003980000706031840c2c115007000384c2c2407002a8031000d481c0d240303160401194014000c0c1c030a01421021000001905901c60f1613001070004210120440500010500301112481a440d0501c400801041c01e114424500007003248158504020380403034440d00c600c100e200d00c0907510380071035150401440e6007270340d0070501034154455254081e02d900309002801e8840d0300c940900f641401440d1700e12f400d074160300c44203401e46d040050a00c0010b901d03a83c50204005028015a6a484692522240345002e01241101c0c0b086003400000c2c0b013640c0c0c6401c840385213a071003038241010f11a80c44035006a600d174400d0a00107003859042 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 718983642 1250 718982392 718982419
    0x90114010e0d050f12130801050f16230715060b070b0a0b030a030503150301053d0b09010206070c030c120e0a0e0a060b0705071509030501050c18010806 67
    0x410704101628040d5080704d4001d407902001a1910708005842d42ca000c0e0040384003480f24455841c1400600340c01402408145030607000c902080c4401032412401214000340c5840301c0e170042c1c048052108900d000d0107000c054030a10210329a1001c28101c410041100344080304500300d10540c016950300300c521518184441d1101d00e004e000180c40c880c072042c1e480b1090080c941d02008164000741c42616103d4883c40d21785400350031443c511500034081c1c0d0519042000c001c1765a015100e6003030030703100c41901450070f06030755040c01d03a02078030f140d4840144027001050725007045010b410424401d900b12142c5a9404004860311051172100070041030b190b41c50000003410b101d090f655082218a81b04a00c0b42d903260002d1a890f01940c0568010305080003132100d07825250007aa8041c000c402c1030303d4039242181d42e941e6900c56103403054141c10881c200003101d00c40d00c04c500402c02190400700a0085003400c040c0349016900600c00d02c01d1443c100c0400c07200315401760a2081c4102c40040c80215800c0c0b1 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 718984892 1250 718983642 718983649
    0x200111010c1d0109030b180f061f0503060f1803131211030d0c0206090d12031b090e040b090a14150612031c020d06080c0a06170a020c0102070204020309010b090114010e 74
    0x302c0079428001d5000e23555a180d1011000c024080c8520320a07040c0c015100341c8180b49008405c0150800e40c0250803400c03c00661300b021a50241c4c010500c05184a00b6200e603003402b6041d4040c0c40d58043c00305034000c0000803940c05002c1640c000d580600c0340300a00c00c40d51400c166079014690100c0c0040340014001d007001d49014000b03001c0c0d405000d0444142300510380da500d030440c030010310148080b07592910340781c620b08183c058140482680381000c0104c181010100c100e001ca001f070004141c40c0e40d1000041003001d0a118640107668000070b140e103040602040c454540d444640e03007507000c1c81d21400280192510141c600580d9100b0005186484030000d038900c07011040c4959003926507000c000c008245400341c0700381c0d0300a008900141c06e07400340040400c0018034881d40680304000c0d240c1004c80024907080852908905083c10043e070307843d842c0409a002e4014810045d50252002c420003145600c190408010260200d03254102c9a0300c511000e101a1504103101c0d0008202c184041480d05 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 718986142 1250 718984892 718984921
    0x3160309020d150510060f0e0d0609171801080105060906070512130303090b0a020715090f060e09090a030e0409020604180c0807050403200111010c1d0109030b 70
    0x240080e00110904002d500c0d1004a820344000300c0303000030f5807101080700e280180f040c2a40908103138901507506160811006161002c0e031680c0d5482400821100f80030889554007403100c85503c002101545480881c500100350480329403180002428240e08001d503200d1800d10703043e61070050440d070038101c100050104e142c004410468040c8140c0400422024040b00a4100303001c0001c0d808180b541907103001804803a82e07900c005400d0905100231160160045589001c0d5460fa44520034000d221110403204001d80c0e034810a81010f0b06c800c08100a5440004807200002c107844a0075076850b0140001d40e5221560f0002c1c0018805114100440c40d00d42c100010450005002c241010b41b180c48050b500c00b031801594040c2e96644103941321003500010321940c04281414914102441e544039a000803207a07034000c044280c80600544100d031f01440143c40414503500013000590489a00035180c518001450a00040314024a040a610880c030343e009a036846080c0c00070b80e8650246000303000 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 718987392 1250 718986142 718986161
    0x50403110105010b041406030c0d020313200a06081e07030e0f010504020102010605180606090418030f0e0a030c0e10030209091b06070f0b0a0209040911100203031603 73
    0x84160181403000000d0040038040c2442d061059a00c82c40c141d2071a03640060b901216001d50014420841c0544000046c4d4155002030200980d50760b0321040e103d807200c4610540145500d034180070310000786600841c440042c140595451200c0c2e6112035040d5100d0f801161010f000c41c0360200040030440071241102d130042418140841c68048003400b41d03050071400c460400c8a0381d9130744c0c1080305560f4240101402010162134400002c0e002070244040b01c880206140e0103000c001408500c10303111581314400190200c0e00b866020541841c0081400c10070b4500c840005036802010845d61501d200310b0b02c102e90b4080000c00c00240340100c280ea480383c000701400c40307122844a000000d138880c3c0e40751900c5152800c015004c0c1161080c04184844200d0200600800d014000302d40000d80380c0502141c16034024480794000c2d915860342c10301030702c6103590850b0498207250481c1c1c20081243c001c004100811a031a84a01048010499480c04100d582c000c1200d00203036038a141c0d80c00b070307880032401 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 718988642 1250 718987392 718987397
    0x190308070f110604080615010503070c1101210b0310021903110d090c060f0f050a03150f06020a051009020d030507150c0f020f07030201082d090a0c0e010b0a03050403 73
    0x9000c501d9000403415000350b407226040d07130489807c004c1000405096180f2603038090a0446c1941421140200781c5442080000c1011100382d0781e103583c1380e0040d5003030f11100d07655001003030b170b44044640f0440103850b215070814083d2040150743d032030048035402900c04006c040400c46242d404248070841c0035003032091305184988000c100d000200801f0340100f42c4c0443c007030024002103501c0c2982c01071a0205880d0220101704107404a0110380d03503c20108c4066000750f2401042000da12207009440ba110399203c80c2e102050792800184050700440c9103080c84d80580c0075140410400b2031004240c0d0240b0100961154001c0443e42c0080e01500140005a00811140760b00303100d2910288100c1e142c0f0172103c0e001c034110400800700303a1742c10001030020030800c1c405070011718503543c0041c0c017843c8040e01500722080941ca4501251007503c901c480c5c4100d098045103c2e60418502458488800740e4007950140110000800d511010301c41150403601404280c920340b0042900440003440c029104808 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 718989892 1250 718988642 718988663
    0x804030527060c0d2307060e0f0d020105090c040b030d0f05070602030907031e051002033c0c0c0a1509020904030801090507020f0316030e06040f05190308070f 70
    0x202900c882d8007070500c9414850003070448000d031203000307040002e41c080301c8410384089032407041900020000750380b4141c0c1d0001d0b011031034901c81d1000909000d103a0314025101d1284010200b06950305401081c01486000195440b8485001c180310030b42e10300044554250b4015600003403414482c1c000344941007842e244c0b49042003025a07454099900580345c0030410341c801e5030300344103101400c607a80741154210100801d05030002d99482c0e0315440f6003150082956070100005804100d0a032215502e1010030030120074494283c040205030200180361684101480000030382901020030460f620350f100301008009401d601c1c1d455414001d241041024020b494920a40040e2205c80441c1d000354403d44440f1100d41c140b820324821148010325160031540022080901140040304680d44003101c00c0000010020500b000d07141d100700c8492441d00800d00280c0000c0f40b2030019000740568000301c540c01a0254010384504400301c0d14000030b0f117a05420440c0100145005500240e00d5215540018 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 718991142 1250 718989892 718989967
    0xe070c0c0329040f051911040b0a090f0203090706030c0507110112050c0c01110a0c080d0603050601170106050d020a090216050715030b09070203092710031208040305 73
    0x5480c46025501110b50280244c180d030208501404100d82403010104240100300c0507440d450341822614400b1400b9541d01e0354620960788414003110040d0a0b0b031007040c482d07001140e0800c0003e6004650f503d480b40a02003000c261b1070320034001c0442000305030759a6410010075480351100c403500810940c1c180000c44210310700b006064000c291081050300d5116488030800001c29081d039102e540c0300e10051904010f024407807504401d075242d0860300040a01c0d20307510300c204403100402850300090818403034200001900355298103444001000c1800a006040e652401c1c0051810701c2d20000b5401940f0110503ca8640d20780d0260105804404080044030800d44415040007800e40280030101c0005000510040c4c06005240c64441c0c1075611401500e0181d400a40b81e00502c030541e4421803044441c0c6400d4818440031610354142c80b030b520724590600020100c3e43c54040c1c030080b21203030700c1841103048590040109a03c03075909070f2602c5140602d8450019419801110005440b0030820307100d4 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 718992392 1250 718991142 718991213
    0x11e0510030504060c030b03210d050103050105010503070b040806070507031818060807050d0305070c03060c080f010e07090b090a180b030f0307201f090e070c0c03 72
    0x440c1000000e0301e000495080c1414101c0035968442e0f0a00181814a4080403c5440014410161003015040d00c40421200c00741c0c140540308001e40e449440b81004000710501c401984094101c0e0002c4080704e02490741c82c9100c0003680100d1040c0503854126000041055000e00d00915103544070303140c0021800500c0e02d4444c40e0b4500c03074004a107a035030168101c1410181d184036500240031201d008104e540e14110000b880414050001000c010000c905881005101d04445003e1580310109100d4a00c110000500c03690b030880e002d40c00482d8280c000688002080e0b019030140400366900705d011400e010304000154012292039401a07485100042c054410b1400510340d0042c1c00c00c04070304804603034105403401d00c044c0d01180f15601308001d00c200040d01e071500c2c40055801c03004176012580361314000801008880b40f40e20101d105401502c6003469000341da242c2030301e140220408071502c43d814100c41119400c0d80080c000700141c8800e00104503482c070740040c0c006004030740102c0c425600090 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 718993642 1250 718992392 718992409
    0x121e03080108061305030706180506130b0708070e10020f07090e010b040c120e1f0c030c0e151e070309030309090c0504030f0c05061b1e0303011e05 65
    0x1500000c900d00d0050181d08024440c103600800601c0c200c0c1060351064442645034420b01400401c07807960780c0400d03121145e10880300e600c8030380c12038140c901511703000d41907401ca031410f6131040b20300e003a007000001c080b01c5c0180840c03802501c1560340c1d034207541466424800100d8082c404c100641c0f1950b000400311590801c4104046c054601010901416900c9a1070030b4907000001c0901c9207003429079041030b4951121031108400707102d0401064001118400c1824603001500c01d80e40c580d030301c1000c0540b4410326081040961015902081014140641180c60000d10070040d5031006442500b4071b402c002820107400e00c00e040031b50b0700402080d1034013801c0d0142e002e480110086201c40c201041456044a00000200b08019050002000c040402040342c031460000505001b03440c171000d810f003c2d15111300300181201501555032403400c503441c00c209030441813012000380320f100c10400041e4400d078550310301010800c0040d0b085909060310b03030080013540940000101c0790080005074540c0c5001d40d = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 718994892 1250 718993642 718993703
    0xc01150b0f07111e01021011091c0606090507081003080f090102070f0f032f130b030106060e030d050403020f0d051f090b070f0915140304050601090b091012 69
    0x84c121540b9035014006410803d0b1000c2030a8528038002101103000a140221112139804441d0048245505544140078100c1c1d0704010305080d10740580800d61030320b941d01c0b1234054982901d861900343c1d2101d41e02100c20740540402013000100340310220350b540c2d0000c060240701d6014016500055140d6240c0c1807140c205611507018002c103003c1c100280b0040002d00f000c4c1c118000c4a503009071a5030305100140025107040d60303004210440c3d80d41c1d4148a03070f034041c15074490024003d100b01a51800010840008101e04034464068110482101c0b8082e8040321b0840303901400b1034840e2440241084401c40c54034800362191701030010f10550b01011100e40507195144c200b80004d61101c0d03810001d4222000804510030300030b40d901c0008407107800030008000c0f500c132000903010043e0b00c0c030000c646010f9182c90304141070802100f48410000041000b5050f503078811410402c1550308010840303002410b8078100c113001103210080c0900f04054000305047c41c0552007004015003005404180000701c0c16 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 718996142 1250 718994892 718994929
    0x7050f0c01140c0d0503250f1b020114090f060a18060e090402040509030f040311090a1503060b2b0605010501050316110c0d05030c01150b0f0711 64
    0x4a1100d507070400000100ca00d0190300650a02801460031607a036010396079000d05000010000a40029000e2080c0c9940d180c0c011900c001202211406032161100c0d079020004034851940e00035190320041e002c4a84076805a5481007081100740c0181065882004429000011050307503a00d01c5d20b5403070041c200c5881c01d96030010810b60741039100c0741c0400b00d81c1003c800c00c05100ea00c3c0c850395480050460700160102c400150304d840d40c51507186148101802c0d030710280300c00318001040c01008165030000300d100341e07150b042c1030b941c40c2460011121a404010381c0c0111003d418000b281c4190303c04c0b42c042401403d1003a90080281e800ba04a001010b07a006082811504030f8040058500502c1e00502c001c0c02c003c0c0c00e5041c02c0e4403103071404080070b02482c20840c40c4601031805480410400d200d201b406072079200211507909110b5120b03030101e9950705641d0b080540510416560803481412a280341105500b80030034040f407450964000e800035107103002d1442c410040b6a0350400005110300c00c11 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 718997392 1250 718996142 718996153
    0xc040f080a0c050a0501052703240a020301050306180312040f020f0411031311151e0301050102100e030d0f051005010c0b0f06121c03110903101107050f 67
    0x240380c48684640b00d6003002e80941c080ca0b80810990b42c201c4283d81031f030703e402d02c1303000c41e001d0a8a04640c4e9031560000c10941c5031250784001c6034080b5075003075549048080811318000039079032200164107920083c443d480e0981d00400000d0451003640c100100c10b851040f082e01c0c58003d80f4486001051000c2e9000c0d12100c0d4085104811840c050060038900003040c2d4040c000c0659100075102107000c01085100c4101816600104028030010b2486101d5002400d094a900d00340da0001040e801441d103901480103017001e242d00480340c01d420b4a0480314140d00400140c240c90fa20240030b404450f045050a2106100c104a4503255021710918035404410004843c68041c46225100d8260743c807203418040a0300d0701d400032515000001d68816030401808006450385008540c0a1805c0d4005050034040d50070030210180c4014109440e44c200c0e650140f200b4001c030100d95109104d0303030303480551590001c03072950240d030a540c104000181060885905001007600c804d82010401610850340d504034 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 718998642 1250 718997392 718997413
    0x6030a1b05010e0907091413020309010b0406081605040c03020d0e0109051b010c0f020a030813090c050c211b01020921030a05030910140601080705130b030c040f08 72
    0x1140044488030480d02c10380d045c2490540540700d54013a003e0080c84405030201061140c580c1c0a0124082844943c21503803881c02144680c02407480714040b070b01c01c41c00c00308001043c040c0041c802200c000d8000e40d01c10728a00e030404110040c08421075aa051603000d00c60f80190004038401c5180f04515140085140f404500d080c508117170340c0702c103001030200709203800c4c2199982c0300c10258149944200c00425829640c00011020381403540024010080090b00744800080c1d00049001c035180c58405000100c1402001e0f515405111032401da568411034104800d200755099180382164000d40c0702d0f103060204030050990007010b500f00c0c04c0c603079000107141e40c0f242884005a1038000341c01c90f141c44102110110f01c0e8807413040035105420404080f005c520f40d09070500040141d1981e1100c00c04c0004e014641d0b50a080d40b003264917038007040b480e1001554450284040710b1110500d0310300014078906100f00040f20f6000509074081102d030038070021841e614000003103006403545500421101e04e5 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 718999892 1250 718998642 718998647
    0x20106050d08220f0308091c140c18041509050715090e04050703030f030b040204030614060306040308010603091b0806060931030c1b05270f06030a1b0501 68
    0x1100451450341c083c502e0704000d01003e0264600582c0e0740034001581c3c1d1000c0300f0004000b8400440009408480c0080c0f040802009074100c500c011400020b8800c8031105108000401e10071100b01c00c20060080001400100030074224594076016900c002a040e5040e00c1d003520b001640d4128500310000c010b01c281035a034203c0d6250004005846020740c8506d8a0b6030b442e5110741180c4402400d0201134070450310790a000350400d00303e07100090400c5403169641e04140c40903181884d23044000c00990030108845040200e1010311954061300d400c0c210740d10b080b504500804a200042d25800c05468000c004000c0c5100500d0082c00c1810003004241088030412010400c0500241c0200c1c4240070180d15640e211002645104025082c0d01140c0085040a0324056940a0700600101c100081e22204c0d0740410b81c07400c10f442e420340d40e12030700c040300002c07958403035010840c0e9020410001000030f100303031140c41d1102d50002c4040c050742c00f002e410313989078900ca4841c3c040380b0401200c090414070065a = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 719001142 1250 718999892 718999927
    0x2b0510060e0103021f110604060b0a05010206040201171905090d02071212050a20060709060c1104020a0314010806010e0f15150405061227061501020106050d08 70
    0x40c1d000640c03200d5145900185000305044152110703080d03840b00000c61180240080700c01c0c0040720b4151001441c1501c0c03d80c00821403001c0203482800700b0344011496501c00281d192080d40d040c0c6818107581c0000380f0901c80c0b480004d012015003088042e00e10208005801660700410903030008068200501801a00f8041590400038841001b80780c07602c0440e40700700305180715130941e007422944c50742403080c101e80f01000c00c07900f000c04e210102c2c1040d00e400c1d40000e00d0740c403030b41031950b600c480180c035044125418042102e0182071030a0150002e00203107015070082004052a050000b40341c000b41c0060035a4240983c010340464106400400030200740404440d0300110004900805107810100702201e2107451000c01d0290242c030340d6034405107054204590140c080103003415240c1400b06034280440b407080307030345415450482929401104500e011030103070140c22000340c21590348500450300178941c10b0b0300150466403501030014054458403000d121440c00345240a80c1d80036010740a40406 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 719002392 1250 719001142 719001149
    0x9030706050904180f0b060d0210080703050c03010503072304090818010e0109170f0115080c0a0e061012090305190c020906101112130b0909062b051006 67
    0x14402c0b0b9070310702c0000c40703454101c41010b1b840300da40d40064403203102042c82ca60000c90000c3d00148100d46240965401c00e01e82841811030340d405010301d94546002610b68002845555010340c40000207101840301810282100e101d80020604c140005400203802c6e212980c805660340100020960a040310800792840e0948003070074030203c20059100001c110740001c4c4134180080c903c0200010380c0403000d0001c074041e6100ca1009005849580d2020124403005100b00800342c45110354a480d50700303100301910308592100481c07410f640d41d07207000d0050b40f00c102c1c031070700013042200d007800780e050b070ba581c403a0052140c081c0d5511520f5040580c2032002501140342c2040502c04a8405032006a64662241d60b11104c2074030100c1203901008015a018081c041c20301206000d0101800c41c061050009000070182c0051407000d525074400f100d038424410030035516001006400020300342d0400c0038100c024040250006403501e41e5601c90f0081601000e041141c240e00700d1018084509901e00501024 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 719003642 1250 719002392 719002421
    0x3020706020c061c0219030c030b09130b1f0909030f030b090a0c0507081b06071103180f040c020601030b060f033a08100e01061d030309030706050904 66
    0x70041c180c00103c00d405115507062400c40d2082d1302c103100820f00c4e01a102d11410750b0301c00c3c0d50008030f64500940649005412100040c0c40e00307000e00f45a01c0e01208403070040101c1d00a101c3c5140b50364460160b2920001e1103041d42003041968803443e15240e0300410005e000c01d40d80010b418440f85001420882c0801e50281010b0a00140b120070703a640c88140d50700164041d6000460b140164015140d900546202400041c2c010804000b4800000017102c039801100c82a100c0950300c1086c1640e0702c0c1e240460f2603410342d009120b006503152040210b1000182d000300500300003020000001c0a6942103022840141c100c800100100901c043c0c40e5908940112020403400290001080e600d012511100d000c12101d00c910060100640c1590604132101017202c07145180c03590b4001e04031035025a8010320400860000180c1c0b500c1800710f036416944c0e599104001c00b1045039191802c1c03081c80c00040c2c1e050108101090440e941041a03c005181c6034403010b86540350b400c1000104c85006000901 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 719004892 1250 719003642 719003653
    0x50607080d0533010912061d011404060b0a050904050d020d031b03020d0b0402030709210b070e0a0e150f0402070809191a0309012912120f070302070602 67
    0x20030103941c8004140314894440f0002005a501d001200e00c440540e003d00000c1d20713403108600c10310026410920000311141102004c0d44041501c2908803075510440030030401355170300814002800d41d0048409100f008050210b440d1301d03a80000d2076800280c034119516489032440c40b9080d40c0500c01080141100d04040007500b24098003144640680d04002c001c00d540051075001c00c000780d601c00103d052024000310748901e010700001d0900e0fa024003072003a258003000e140440c1c22801401140d503041c5c1c40342c1c011103d901d9036401510022381e0024201ea00904c1d01d600480c600400e442c2e03640c4641d000309843d09540d010402271185a107100c48500d4001c5004100710700114003180d0231584440029905200340d440000c080125200f846d4111031503100c442c501800c03400b9a400040e42c0a80348440007000b903490f04200c00c210010b0003000b24107405800180c100118a031100240d420030780c0710001d40d121081c45003e021219441f001c506107030000d012409106040c0d0400140c3c0190006000820 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 719006142 1250 719004892 719004931
    0x24060a060909020c0a1203020c12030103150506030c09040c05100801150503040c0b030a1e0b030607110a0b0103050a1202150c0a0302040302101106060f1503040309050607080d05 78
    0x41401d400c901070400c00a40009408980080c20409690059080078060201c4018820010065881905450314603c107001405d44080d0001040b03a04880c1e20034a54548100151141d03c09070800038040c0e5803500a090080d0010748554034844e115900c14000344c15898107200c1044000f9030110085c004010303083c0b0040c8014122546942d00d903560508103103403240d5540c81c004001e29040e800030403070608003000740b00807200b00d50040d142400e00e01203c41c2813645003c0401e000c0320811030900380d040c2e008201103800b690184c00784041c440d05100a40b4400146074440c507441d03140a9004646a030b000c0032112080c886081c2d2801000145e91000d00fa5031083c1131034006407683d002c0d01e00c4911480020302c0c01c7c201d5000e03030b0460700255405042c0c1c0101100d030b14005010740641042c2c41d1010300441c0006581854506602c002c2c03401d0003820442e03148005400e213009030f0001041241400040e01011540d07549400140c41c24038811020f10359583d0f0180700e080d056030030240000c1302891000c3c0010 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 719007392 1250 719006142 719006147
    0x606020a0b041e0807080316034d0c0606030303100e0603031c09050d021c0e060708030112050106080d0504050105030a060509100915050d14010e24060a06 68
    0x741c1d04581c0029980a450048034540d02801402d40001002401c001880900700010200514810460341c44543c2044c1440c42060781540e14014020070b20310743c03c4036140c4d080c0005030352030b03c450440608144034000007114041c00a0307401c6002445290b070045031138841c0b10f004020760750f07002c4400e030055811410445920442e0034064050908074400c108001011030304c003081a5500f10500c44000c0035581902518200148210801962103000700040d20f0265030001987e80700140500b103040903191031028007200c0c0e0b6800a440c43e40e0001003080300384041964800514040c0100c0a00d80345102d00038502182150080d900114480d0021451001201c1d08002a170b0120380c1c00303003071150f665a43c092505000303140981046500921711000d0003002c1d00040c8210058a129072400c12040c1e00440940500c60214440c0c035503c140b6864505000400b454101d040c18010710303001282618030040154100f0980c00003007400e08040700c0030510070300749500c2010b03041102500d00c41091b90601c0d100 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 719008642 1250 719007392 719007413
    0x702031905120a020f06040c0e07080c040618050d030807110a0302100c05070f0c06030e0120160b040b0f01090b09040b070c08030906100e1504090f0b09100606020a 72
    0x40c2c0c00c46007000b0490b40c075020f000b0300002190703600c140262240d9283c249403070540030300f45015141c0750803c44000964080d0203aa1000d0061030b1050300d250809182c1a0202c1d09a20b4514410100501000740090243c0b200d609008426102e030b101d00d00c0c0c501d4a038200421150306904024650360140c0090310120380c0100c0c85080c48500d202e00411418608007054030588079041004107008140840d15040c081c141c0f0f820701c00d540444d981800401d0307103502c08500761601c0b490110403100b08920740350300b84003140c00103044a601e0401c89801c41c0046468210000108940c2542c170403090b082008503130203040e4041405000e203280b0800c80c2d5500304001c00c4180000a1005000402550104407000d010741c40090401c0d600048503a528035080c010aa101e0205480180484813013001c046100101d921041e48104200656012a18040b00400015211090701139440c20102c040350b03000b0460b028521032042440000520002c07200c2581c101c00c481c580c0e4444070464010410100005e030700b54a4 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 719009892 1250 719008642 719008663
    0x50304150203120105040f020c0f0604060b04151422020c0c010801060206070305060604090603030c051603240609110a02390310090c0e06030a030c03050a020a12050702031905 77
    0x6002507c248460306000c0280300e5401181d106105458034504810310004a10780705910039402440801e0310342050100b91021501d400d0788601584009109000780001c092030302c140001c10000300d0700c404200720301940c034a130400c0c588080e80001d03070111780200404c2615412030007868100b400b980f42c004020340751240608031a040644500100301c03199141c8068401406201004020b01c0d6501d142c054503407010404115154020306e00148002200c0060305001c51b50403013112400181d424078042ea004018800100302c00d5691000465807012078440d861100c09858821991800c0d154406458048000a00f100d000130300303004003000320714402150b00310304916410080640c1210002a00b048203076450034100f01e18000780c2c60144540d10101200f01d88100d101c207006901d42c201495101d00e208100034020814002600300024400c80080107011058416200c1c0074246030781e201d11087c100304d00500090408180001549014040b80c0c9000d01c17860958000e0308119070300c00d0b443e1300014a = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 719011142 1250 719009892 719009899
    0xc07031418120709180b070f03090b1513050105100c0c090c091a040803070b04051c08010906170705090601210c120515040c120603050304150203120105 67
    0x19107001e0700000c100551080000c0140b06541c6800c9450350281e03120725a1040d40b000e00d05100301d5440341d034400700d0641c50b41500a02c1e5000380d40d441c2d120680da03425992032003071704240e83c43e904800802c80f070610352030240499521801d40703248650f0030001d80c109a050174100705807420004110a0703442c01c1c80c58482e1880c0b801e0031043e0740710f90700780b2980c1204150f000c01d5903a41080141c0c00d94652150492090301c50078020291503142c1e20a011701d1601650040302c802e036100300f1010b004034129002c0503a10511403801c8274230641040c84100302480039025040003180d1004014804601ea03401140090b2010320070b00c4c04405106006150350300032030301c131b800c0c010300c0c04001054081e442a003180901004841440900d0000f041d060001401d928003441300140600403010580901802900d01800490000000040540c81000010b12103188914144600903107240003207083d60003410011409000515100c500c0c08000203075003000301100d84c085410130848100c0301031110a1890660790242d = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 719012392 1250 719011142 719011147
    0xc0c03080f07081f08010e060402030715050a030216050a11100e01081f0e0103050c0f0d0822080f0736020f0d090f0c090b0607030e030a0c08150c070314 67
    0x109980d51561358a60014070544d401c0040c19401d60000185950103244207500311440c00740d0b11070701ca18100c0d01345000c6030f000500401c00c112a440c400d030040e007000810200d050050301d42c26550701d4500110315004840c00c0a4241d0824050b01e42103400702e030301003040d05081420b1152440020403148000300b10f140c8110404880365400783e02c00708204003424068880500558482c00e1259890560a0074244247c0081a410001e42055003040722a80d5000c01c40c2410083d0212100e00900031406030811801d0140900268540b8100130b64070440c214800a0407542d030406c0058074010074030071a04000310001010481081510a04440ca40c6110483c010785440010900f0003051158030500245c003802c1840f40000d01041190840c1c810b840740c21291640ba80e0f841210042e2490355944540c03045060100d4001700340280c1e0b240c40120700c000c058a03409403040d5600d28540d04d03150032220050f40400448a01e00390301c6188260842d8070001c00c10b050103016a4001c080d01c5801800b08c900e44400f = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 719013642 1250 719012392 719012431
    0x12030d021b010905070801050115121d03040b0408060a02030114090a0603021503090c090412110307150204060813080a030b03030702040609050601090b0c03030402041e0c0c03080f0708 81
    0x14040c00c4100c1003081c00083c0700c080803e0400d141d072240342c0d01803580c43e940303040c00028291013140c48500072040341d030b111030b226500215150401041e0b00c0f03100b810182e442d9000c5451422091008001620400d09056221424401290301c0e10f00d000301402d08031481000140315052440159000c0000111600345180e51040c1481d03001d80000d80c0029002810b9040440c881780c000070140d1310490080c42100c402c501420200718003c00281c50203004452054462860184034200c8055100c50702e0046903e40401c1d03543e0b086900c582001185a0282d004c58180320300c03a40410042c1c0c119050f181e0065004603681c88000e5144110a80c202c103155a55150a00d01e071810310036684450707002401000615651100078015050031039110b07001034110100440c18040c00070648500c8014003009600719550b0303a00740b000829610241140c42060024807683c1702144c0e01940020700c046076a04038140c802880c01404010b405410b01e45500c0440c4200034030f0a605c0207003203602928100105880110 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 719014892 1250 719013642 719013667
    0x18080307061508030309010504150b0d02010f020c12010c0e01020d09050f0d020d050f070512030d050714131a09090a0b0f0a0f1a0c0d0305070e04090b06010e12030d02 73
    0xb8550f0200410380400b000700f2071806019480540700350302a040c007886624130b03c41d590080741c00e00003207240d00284410071440594410041c500301d4500c50b00403641301c18030b030384005820f08030341a401041e2a03450300303600780a8541c4600e088060003020b00092072180c06002000c0e0035400e81e070145501400c0c4924030103075296140208031520b1a00030341080c42c1c000b41e90906648401c1c440807150042d104102c0b0016181c14106034001035200b540020718186500c0c0c1984001528000e0116420072401100c44000250100c0c01001f00861071702126807114a03041851101c001e591070600c06151080c071280a99440c0d40700641da0010713403104000b40a000c0c4070001000304051110b019000881544040340c40b03914600320500352140100c0c4003510040c40020320900703100d03080e103c1900750007422054840c54081d030001d0380c004503c2c0c105400d80b2040940413404580300078109031074541d04002846025600030700341948110068900c1c90390220040340d019980e00c01d47c40b0008250740c1c005070400b403031903 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 719016142 1250 719014892 719014931
    0x6020a050d05040813060e01050a120b150c060705040302010e01270b040e0a180b18012d090b15060d050f04120f09182a1808030706 58
    0x42001c800308032070300700f50400300b0250300401e00580d807400801e030b80401c8040c01943c0c030b84020081695814507040042c07100b01e42e4a51849103a180040d180c101c000100e5648110a0b03400c082c844980c16203c40100941600e82117029040105101c0100700500260b40d1041200d40d05a60030b080810200c0360303c8940c00302c8045240e0708143c03151101038010410301e54000040044035901090008103844582060085031840c2c034030300d6600002c41d0080d10000c0c0c05806000e501502c0100e03a0301e8441e48000761329007500d16040c241881d1405030306060800d003940c0580c00510b50422801000741c01c209070784402c14084040d00950a0f40d07002440d9201660b01c0070100e440c100541343d404d020506001c06007244203070b41075804951001040f0320410b0100e12460180141d0f10a81d030324480c45d54906200d003c2c04092105405044540b02e0688500c041001c3c4c035142080c2c4564440808103190b000300080506442c109001c00140010804102440b40041511400360300920000303003c1180700d0b0980b80c03aa = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 719017392 1250 719016142 719016157
    0x50d03051909080f06010f05040b0a08150a18050607030506030a020d080d051b04061b020607030206180a0809061308060a0605150313203c0d06020a05 66
    0x74400d0700201441580b20004204986404085840f18006005070702e848a809004200160701e040030100003618054000d2014800c029120510003901c03540818140801c00041c04c001c5c0003004c040c8a0201e1280c414208420502c50341505800603d650391342c0c940340090910341c01c042d10780012424030380d41401440840c56006040107500c2c0001d24111405802028204c8011440c00c40060f2615920704541d01e42030740d201313510703500c1c1c5801c111702650350360001d2040c042c015014201080058540c40b00a00f01140a074004007050f280a444a8031307407510202a442e601e030071102d41a800164410146c071901c0310100d401a4561500c0680b640d04400c8580c41440148101400e102a50500e5400078061311002e840c04a0840180d45141d03a452105841c1d14041580d601d01603c0842d00c038190031103094600c9052180800c4c5600e0010307000c41e02e1020101c0034110b2010000c0c1c0e0b1100d1101d0800c503900c00b02e840e19490024890000f9a801e285840b020300010340004494041900c2441110001e = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 719018642 1250 719017392 719017417
    0x3002090a0515060c1b010c0807080d1509050402040b0609060d0b0f09190506010504060e19180e0f19080d060e1302030d020f0627030309010b010f0c020a050d0305 71
    0xe6a00a035030240e541c0ca4084017421310700440c0541c0b440e03154407410460750856000940c080c505581995004076941c0101c020f1214030340c0c0c400300ca00d00c80134660781000042c0607010000c6002e0030540100411590309800c014420502080b100441d601c0c1d2900303079404034030407070000900214104003203461a050440307140d074850710b0103040200744280405400000c0800e00303810042c2d036a416006464510543c0100070214200d0312030443ea0b8500400d0507011945441d030200c410640d1001c808000c02d00ca1241c000403d070b110049078034200b40070003009401c2030400e80245000e50301c8003d100e600380c040f04c01c06480d20100003101c16603241c46403c42e40c02881e0400003460180740078450900d1002c0b80d800201e210303000e0007580c401c080d44001020180152464080c142903200e0507102d48602c2e1007101189071f041503904150381203200500142d44a1145c1d40c1c00400c0039440c00000400300c640c0f88101105024801080c0c0003da05c4800c60780341038038025100201e03ca2101c0c03c040d00d01e405100e250300340 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 719019892 1250 719018642 719018647
    0x30b04030c1205041802030601020109060617160b0f09031f091502030f0708130b0a0506182e05030f0f100b09040f030c02030303013002090a051506 65
    0x40507800002504214061000364080800140c0c0440741c134441c5100b140290740045442200c8040c09500a40d0080d50500001810303089940d00d850582d04158011010000390800c3c02040040a0241d200240400040d0b0000e6508040c0c04250320b0103200d00d64590301202040c0101140c42c00c01271031403081d440e8002e403035482d400c203100c203070162030000400c036200c46001041a102c80e941e4003d6a000b4940c040304c0030519600c0e040c0c129007103140104548021010001a600031030072501056008421441001c5494a030a005209101c6900c81001400720115002c0244d44c4610f502c4c0300645800141c1c4503101c0145220313011180ca011600856458001e0b58489818420002400c1d4a4002010305540d0703075040c410302c4c81007203d01007025940c00c9102d6800040003c0c135160780c09058188a82015002d43d08207030040303071540d00260411056050710344c41034009800c1d86038480d2070040204008180400f031503404202050000707080381c1411b9441e07401150700380090010600010001500198 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 719021142 1250 719019892 719019901
    0x507140606010e04020c0a060504020112110903190c060804170d0b09090303060d0f0212070b04061418040b04110d090b1608070513050a03060c0305090c2206030b 71
    0x3500c403601070720340c18007103609011040c200381054001e4130103000741c00c1e02a1180247d0f0380c46403400780500420407410030581c01c011000110180c410f810f400041421107036201d420803410b02d841e010001c510305007100241728401000401080c191070075070300c95207000101c90301c5502d410801280f07c41030960341070341c01003031440004005901a100401d0100c0340c641403600c0d2004030503141e1000f94ad003070340c000207083c481c0c1001c00c81e80f1540e0a82644040c00902410101034aa02c1c1032680e00c2d0414280018000342c1000b02540c0072410900202c070b0700950900e4450034002c24001600341441c201c3c0aa62101407005aa98403036005210f4544c425606640e92000041c00c480141191102151442036403c0820010817a49048030301036215616421061b0311191001d403120313000003408154101c04524003003956110b640ca060002d520400c00400e503010010001b07026030700000d090031110f41c044183c41c095581d588406c0b4042102ca10395840f40d41c0d403900303900e0001d0501e42c0c002410501e0381ca8140f0 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 719022392 1250 719021142 719021183
    0xb0d060f030f1b0810110708040602061803190311070510020d061d07141308030a09061d10020f0307210503040807020f010309050a15060602010608100b010507 70
    0x410205200f009607036000c210401510800a281d0301a2004541c01201c103250610354030350004811220341101c0b1030810803a0780c0e0b14005917116801000c0160419402c0c051142c00074413801140303c4891003c0c0d41003002094070303410103402e000d150000b019100d00542113101c01807801ca543c0c09030841d040e26218080000c550001c1e600c85400d14005a150010000d440364023100e105c544260303050341104450315404412103030400404c481d00c0c0c50620812426140141c220183d00003004040701442d00c0756003100d0b01503c9031701d8a500010138056006c818000c0c2c10390103071000000b000102c1e0703c100c0c01e4000130822403403c6010314010030320703120000314482802180310030401045444000c88071a03041406c0102ca041c001520020580308040c00f00c0401841c00035030840b1104010301d000200d01c0ca050329428506403c500782660119070345080c100481d461070040c032010b0056800280726a902e00300505940d0b08000070f100540599400c1051800d1703106100b1928090341105400010b01d0306010030b07 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 719023642 1250 719022392 719022413
    0x40c05011e050d0908120403110c01030b09070f030f0c180f08120705011104061206090e03041a0f3f130204060315090b0c030f010b0d060f03 62
    0x4440c04034034412548091040701e41207502000301c4542c0c2d00d0381020b1014a03002d01400e11403904980218080c40010750840618040d144568040e581c0d20b200b5400340012641407410700e5030006e04050034125114925180c006e6841d03000403030f916090345046e180040c210002d08840c44804401410489040b000a03408038105920407220311452041c1035488240d014900705620800b4a0380d000180c3d80400b0209100181c20418003c44c00130031205c48451a031603142d07005400501c04207400007048801d808151081d64003a042d12070081000e600d200c0740c0e8540d02d0040c0d210740f01d1400c1140d404c1048008424041e00c11801154058907241e48914511820b4404201640c102c40710130b40b10041407100184100004500019442d0441b03a01e6080b000303500c4081c1c3c11000e0b600291107035000000244c0520700120050150040085c840c003251906404200b409404100384400a0040c40007014540d040107044a5040c01e1565440101d5019a000b409466100500b81e001014000007030110b240f10 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 719024892 1250 719023642 719023649
    0xf100804051002160312020c060f0405070e010306050414010c02030d0c030204080a1101021c050d09061503080417060f0c03131502120c070c09020c030405131b0815010323040c 77
    0x32210600907034001b0032000c03801a954180702591255022a6420b040c1000c06a0854011703c1907440391034503603100c2c072800e003002c2e0f00c1241c03983d554008000600c104404103040d03540c031050017071000000303000740290340e0b000d5440d011441d22b0307803032201c0c0110501a90444005140260940b03403289510b007809014685064001e6025005080c40184015044005410920141c0d260750f42003000c2058808002c010a02040f00c91b030b0380e1909842c9006240301e010f40000c5114242d0142da85040c680540605a140350958041d903014000b800784003605103003826130011000000b2034895541041d40185450b20304d070090500b8981010f016000303c560740080460303426805440c1095111200000c000b0320036210040c02c625000d07903050203440c000e0f4005082d5180a030301101c0c1401e4840001403051100c60880c00881941c5030484200701c180403a003809000c4032410410701d9440d20b84101100320001550703441c1015501c0003450b4001101c2151005140b00401c10480b4500d81480e00c001d04108500 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 719026142 1250 719024892 719024897
    0x3020d0614071b0b040c09050f010303021b030303061302130e070f0f0e04050a0f150302040609092d06110c0c030c1e030705030a0506010f050f1008040510021603 71
    0x10005088a800b440f1522404040000024a0384840b500c1305546441c018200300c8900019007000141764107240503480c0102e410f1903401c1090f514502c7c0c06864105565421550481c0e0180c20513100c0d076000c01907983c441c1e810358041075104400c602400003441001d10710300c42420f100d072000ca481d541300c0d400180b099445482c2e04100b402e5190054030f04108142c50175000490a01e020342e80390a242e0080da4124503190b001103544410b4042c401c0941c1c02005640b8071002c0390810800a610f07041c01040000c020100080000144c282c0355504004080390104c08100c00c00042000444440c907071202c40d03d0340040b82006850800a084911035104070b83c49400c0c0c1c820402d14182e03502d03000ca0904005080207005040d0141403410041240080682d0107600d801945400102074034140160002c003031203980585034560400844600c000580c0d04143d0007100142c030b4000540c2c854100090009080342130504003517603207203015807404480c015221040d41c0007185602c0040503106014030498440d4 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 719027392 1250 719026142 719026181
    0x9060c01240519030609050a05013206100c0516030f05100e0c0f010311030c13060201060311010e130603081804020f090d080c0703151d120d0603020d06 67
    0x48040062001800f400c000360750075441010070014a6035401420528492002c0c0d5211196549070142110407030340c07290095046485040000594442c41d501c00007011801d200401d003805404500c0e000d0240a480782400b00717280a003000d0103810400640c2c881c0c40b60802d8134000e43c680c54242100c0320038220807501e40c401c480d92002c402c4c02500070380c2800d41d541e200500d081180d080030000075548503001c1e54181a540c00d0416034080300040214441d0705c1021140d603032207030700d0340803a01c0d0500d07554840380869141800a100003000741021080040003444d05040581c1c031310f8001003050700c1801404221914001c80001004480d1001d80b5a5105214205a0a054013000c0c001039106000d00760040d040f0401200c4040d00d405020410500d008060310340c1017040b140c00291800c0c14a804c144c42c410a1900c1c1011050b856004188040180c2d807030b0a80600c415075041c42c0d27185e0040c200301160180205010500c4c4004e9405003000b180c005080c42e190055600301000202003000003400541c4c1d20 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 719028642 1250 719027392 719027399
    0x130227030c0312091507080c150903030412111b040c0c0803011a040b07060902090c040b0d0b06130e0901050106050310060f0e0d0308060909011e0209060c0124 70
    0x812666007042018016101d2040070032100c0355140d00c480c0341140c0c05107000031046082d95640000c3d00a642c400d500702d03a5210710b4010300390300e4280d034403d03000d010600319030402000941c0482607940142d400140070409030b02034071080d01c0503004200894030703070711501d610b03011801c0801c2d8841c102c1d404150340030000410f01550407501c0000c1090f0150513140100010131482e950b4101c00510030300251170083c1050744031101400780d03600201c016a41981c4844c00d03001945803841c0c41542182d029000149483d240c00300e0041d0301e003d10003c007120303290f6401c090045912210120303520049031083c194041c030340b40d84a4010a03401601c501203030b0b40c070342000890303e02e000380201d9001d80703c00366145907501e20300703002115213880c20180041085043c800705000fa898405062030300034800d468403401840c0a82c140404540020403441d410ba040c01c10b055405041401058400442d9000c056600c07502031004c50a6441401d8184400b9842c0904800c54103174100c03803240d680e000c41141140480c0d075 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 719029892 1250 719028642 719028649
    0x4111005190503070e120a05031b010f020301060c08070212060a060303140304021f0311030f070210050c030a0b030a050a0503040e0108010b0114180414070215010f030b06130227 78
    0x11180000480c981c1000240705d03161100041c000d030f41940d8200c41400189956085c119000151030780d4405a481d189803866803000c0c0601900d0300c010002c118107540c500340d070081040c0104034014203080340c005501015900e6204050710b58001080803582c2508100003018014030b0b10b0722007600064403d11100c60422205421607029030f40090031003640703c2036801d00241e81c00040c640b14080c19a100c00b00303207644810f440503611404000307050207030724545010044e0a0003012004505524503020810511281c040c081d41d42210090200041d6500e007100802d207000d116180c003500f9403184006220030000008001d1003920800161140300e66a075059890989150080040c041001e140003400d5400403940a0f02d00f000840c0c110741301c0d1a9448011804aa690070300d00c0030915140c50030050015010041c1c0d003008440c9805151056251500300040c0300c2e010b000c010003060002022543c55030b5201c541e85d82009211000f117541c3c40c03802d1241c164017058120b03a100d840c00700801542c3c1518 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 719031142 1250 719029892 719029897
    0x2280e040b0d020111070807030c05181e070509120601080c010c031409150706060501090506041208161a0609010f0312030b0102160f05041104120605041110051905 72
    0x1c0900541c0d80b4040c15401920030325020301607544a442890380c00a14584104403000055004000419a482c24881407250b01100c000d840c880d550138010601c40e51814001c00b603c032600100583d07034012381b01c10703004455034440c6000c1d080c1d03c0180c80b80381214440002c41c840c0c0c102ca03004c1c41290700340c1401200559020081c580090b000c504541c3c3d11549400700304005151100c0010610890803018001060280d00b01000c169038a50b6900d0051003103580000843c00507080482c0c10a00301803800e00710281c0346807030420040040720b0204045481d4800250102e086030751210002034240541030000901900450389903224803070b240e00000c1c03518601091141540d41040d1030086800e1100c03002d4000c1d26408107400d045204058215115915005581002d0650701080391000e81c0b0342000c0105541c58180109881102004100200105040004261580040e02181c1645d440c108800381200709124030b50080b1512507298a8503510030028180b018100140c181e012901e130404a4890 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 719032392 1250 719031142 719031161
    0x90e0f120319090213020a0215130204020f09061603121b08040302151f08120a08190207140610060f050705010e030a0306080714090604050a02280e04 66
    0xe180400c0441c00c0302c02240c0c140300458015800110390b800301030f404500240e817914950491146c0c085070a6410650602000c0c421011184900c152800d042101340c40c80c020b0020024852907000503c0a84040c021040c1c0785078100043c042e603142c6040d0508100c030405550300c01c400042022172055074080040c1300b110b5400c071510a80c20480d600c01c01c2d007a40e4911001d0004d4055204901384a9010254100100d00c0796216a04900381444e141091441c201850f4001c5042504441502c0400d41800025100040000e10741640c098842c0c805881e0040c2c2d8240901c00c0c414000070708081031108c60724110501100d0101204e02c2682c8030807909904030303076a0247c1c10005103461002200305100c0d4000c0c003c0a03020341e0001845514001d110b62641e80841c1120020a803241810070184006101140017403060031280007076440201c0c0042d14980f001401c043c407581d5608086400401c05505840c08041ca2007540314225040c3e2115031245080184850001500451345140d5820f09000d2000312 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 719033642 1250 719032392 719032423
    0x9110a0e0f06090601021e0d1805150901110706080f071d04050a02091806010207080f121602090403090f050a05030a060504020607051c030516020d1413090e0f 70
    0x1951542e000704100444064685811849820a10074482680d4115103c2c4003010070300038600c41c10b40402c003514446001d48502001c06000c4410815610792200411302d6221001071710b0355515034413006848000140b020b001007441110400721f503141e0490400e0f030184400203e0202030b03a8904604481a070481c43ea60180d40000c3e00340d14615090580042d60087c100040140c180124240880c0503051420358030100204038070244641c0d945c061003600040c209080c05070480c403c0d07400d410307903a840111045900f003110005103600032914140f08000e090354000c3c5440c0490a140c20010120040760040711180c110105000580f40b40292818044800c0030300640229030f416160078008006c010000d90b0451000c20801c00000c50a0103040d58008000010030043c180703640c8024200c0740001c051806141d44880c92130a6035800180020350750019141070342042031103511000241c0201501e015245001c40b1010070f458216811442e500060201110070380c8488499081c0d031042d126118024 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 719034892 1250 719033642 719033671
    0x1c0201240302031005062101050105040f0b061b0309040e0303070906090f0b07080c0105040c030b0901054f020111010902060a050d060b030705030f100b1603090909110a0e 75
    0x811101c0c5400159100000521020024a1030300f01f0024820141c09040c0d4265510030051040f0f181c98480c500c103109020008100015a80002c101c8510406440101c40c440c1c0294021511030100112002400301810600c040c501c90103100380e49070015120700f00400c40024010a003039100d005400101c5500c07608102c0080e1421914450700d0340201c005551a200030404c40d4401f0f8402d00416016521038a640d521442c6181037050020303401038100e4017503904007028060b00150740402440000004100d540c07550384c0030799140428014020380c9164221421050b4223260b0411105104064000c0e20355249142010a01c6401c0f20241840294401c0061016592143c410409022003480005001a40648581c001c21680c1c00c22071b00200080c03000010800041100800c00307800200c55907280c4c0e82a820301002209500420b40301d01210704d0780001660030b06110301c42500c0100041881000241514103040404001c6840c0131400754001920000300c07159900340c0c062241d102d05100384c3c2c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 719036142 1250 719034892 719034913
    0x3061d0304140301090501150e0c070203071406190f110313060305060a0e01091a040b1003022a15160c030c020f060d0b100507020319051c020124030203 67
    0x20720500e094103442e5015940d90000030b0000e2424426051030107201142503803a5454a40890b184c100002c0079840340380400d10203c001a10005103030030681310a800c019440038951000b24169000710046071380000340d050010040581c01020310048000142d850000920b10504070f903a032031040c0c400c5130320341e10010f81d0200b12041c0701e603100a8000e44010654440e4540c0c038024819602001c0e0806850560740300d18440710030140ca42c0f00c4446107800e031000c0c808020308400040d035100021a4080c18543c000036515410030b204041d0070300080d1000025114481d8031042a0b684d18240c0b407544005480340c80110b4055090724401ca690b20109960f0500700c2c941075039044581d0300180000302c0e0014a060418002c9a503001c000d009443c4cbd180900181c107100710410001c5180c0d14200c00e40c2440002c014000242e00d020400c01049031b81801c404034085260324103140303007601d010800c41401020128212403180e041d048a00c040d407201b2844a50518100306c810381c6c540062000039850740c0000f0511 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 719037392 1250 719036142 719036159
    0xf1b090c0c060e151005030c010323220503190801030f260d0e0c010503010612050c0409060b0a1101110301061d04050c092706130f020d0603061d0304 66
    0x1444449501d01a5401081c80e8004662400c40a032031545c2c5040011405020311305040200d0855000c1c2441c085c40b1000c1c2c107840c620380c00300c1d6111580030031001007000603907103444400310340d0f8100c0c6110b60005030f0780404c1e01702540c0741e80140407983e01c0403a6800000b4801e911600302c1c00c1c16a80c03c05401c01c40a485603031109041500c854140790040364a65000f80700401c4400600503c1c018660003091100080c80d030541000150184181070050900050023080e600120119111004107000034140c0c80b444280f80030f0780074135440140c0040c01c12501041c6070143c2c1014000c001101d0b01d4031009180501302c154207817468981c407161400c505100400c5268440c040466221a48151525200f82e40302c01040a880003203d441044c084009200031442c107001e0780c1e0b0342d107505400c0c08540c102059040d40f200655005071101c3c0c45481e442c040ca80c0f40e60281e5009041c03451025900710740d2008010700c40750252a90784010385e006460084145d6800d4058802070803504501c030f010394503290030051750 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 719038642 1250 719037392 719037401
    0xc01050a02010f0204060903230601060e030a12020304052b0809061b0706260411030f011514030321130f08030414030f09090703090f1b090c0c06 64
    0x40d2400c6640703480745500425410b00c0100042d00d03e40e0380c0c1141c2c45e41141801049030441d460316103a540d0481099190410001c14598155070040c5041c20400e10700000003403800c010900050b203141001400c2c401c21580020042049640030745184001c1c0500f000380300420281881d40c2104280038120070000a481c0d10300030200864002c040b281410380d892060054440215030200255100c040e090140d09d81144140401c1d95207180811528100d1440d00030742040c01910003080d41980a840c01ca469805001440d0807c6600c40200507070603400b00e000d05d5807045445010712a0381c170300c141041582408012220300e0b24a520300d46150a540031880e41064000500320b40743d04026498110010b80d00d0219228181c0c0200c001c0da0b16402e0030704003a82031006801607141140d00c200b16010014802d40b09803031414000716403454043e40c0350f036400d4000c0c01c20740c4c2005001c11882e6800c0e00c03c0180c500c004c0244038841400030031802d82c40301d48000031201041043c001040c42058a10001400741d040b = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 719039892 1250 719038642 719038657
    0x3071103071101032d0902041107020a050f0303070b070201020a090605030f15030708010e01021b010513061a0d0303020d0605030d2109020907090611160b0306121e01050105120c0105 80
    0x43c074000c1c50035044128840200548259441d480e203071441b500540c50517014002c544107150f004580f51100340e0780003d8804100e44182401001c00b1071420050742d90500994210745c2e08502c0c0340ca6a0f280c8450000d001b58001e0104001080918101149a40c4201e058910075900b00d40308040e50b4440c03020703946a0352a03c03c2001e9040c4540000810780ea41d0a000784091000d01000150300d414a82c54480702904141740845076a82c0340100304040c84c010b80c580806d09980005000911614501d17401410b0460700300240c0c0c000c01001d40c0c08041603030540c01410080f0381344600300f116035111404c00d52a2055202c03100d0000e1001c00d04043d06401c0c10350880e50898440c00300051071905507001c0b0304142d10886520011400d042c0b810488150081500d661200c40c400141440d40c40c8120400c40f84c522901034003044260200000e5100e4445a88100c02d030341005045074041e841d15040300340c0102c12005480801d5003404000901410708059110501002a000d08a200c40d900011503080e0400b80 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 719041142 1250 719039892 719039921
    0x4140406030501020f13050d0201080c0706020903011802090f090706050a1b111c02061c1409010f14131704032001090b12071d150307110307110103 65
    0x640000024000d200500c14082c4117038100762540007a62155420184540c00b05000701000c05005005030303880601140d005041c24070690b03c8514900b4921300074000c040c21160950301e405080d1501d500503804002150b4800ca5aa003c9580da10304904c0003210251503030f00560340181b2050080e18000c001501d58441103281041c000645e44080009907030158400341c8800000d84410b503041e04080c10610144030128a402e12003001c1c60f80850a64407845501007100c0491600350203210100d500b2a860740f4980a1000403030782440c6588a000305590148000d4451801287c0d4800307a0b90b64818511941e203002040d2000101610b64240da40d40503405142000c0e0700700404000281c00c90308207101c0039803616401070024000e000140a0b0170300340e0418800c4510600c41320a039030f09100300150f84612140f400e0301214411003e4540d560000100f025485014608100d103a50081c1004d9441500070355220744940c9032401800380c40384180d440142c02d0080e201201b600720f50282d00030340b1501c1c4008 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 719042392 1250 719041142 719041151
    0x2010e040e070e0103020a21020402031b0a08060f0316050607031407050a0507050a0302060d0c02010e0a030309050c0a15030218100302031f05060730020d0f02070605041404 76
    0x2400c0700d4184070181d00180e00d403e00400c0140294244001c07a00041c14101030714442e10000c0604141e0012402c850081c031990300017000030050390410103100d0303400d1020401d0a85414100c68047c24000045804902450007040b41c280185000140081e012083c0701e041c401d03142c18082408420f50002000340c0030f000309142d00c1043c2e00f599900078051103002d040980001c101c1740c03801c98104000d50744090b1041100f40c00500c0541c1d5540122880440070103c00940c200f034542c3c0503400b4060241615456000d4030340709105044e0541c0200603201d11401c142e4014418003410030a04100070701074206540b009000410451b1701a0340280a21100a19045ca0b83c18005c80003410b150b00724442040007030307000300621a005002e00c02880c0c03460510a2044905424a40812510300803118040d00b507059460400c9802d403035803290760207400781019007448084c4a000e406955a42c100c80c80400060f1943e1881c000c0501c00b2882d07a0070340740d0035a2070f545443d14010102c480d4451950400d9485640c4 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 719043642 1250 719042392 719042411
    0x307060f27030c0e01060e0603070309020a08240f0f041203110d14070201050c09010c0c0512030901090603140103020906031c09050a080712030302130b03010f090b01020a030c02010e04 81
    0xa80a541c030040d8400d0b03c050315010b0514450030303650344060307001d0f00512411078041d040741c0d80e03000d040d00d40c41003c629000590803500d000049415125a202d00340c0380c0181440000310420190320070b584179a0b812054601504c442703441d0090000c0172142d40b5103980c5040041400a0524152500e07194500d01e0081040d88824503444c21030b6212111604c5400d940c1c2c8000384c0088507100c1c0c110f5100e27105000812a920b45010200c4c414410743c00003604210546c080c0d1002c128032100d040018060180c0f10407508035100782d00965a80c803100d000b03400f241d03005000042076440380c00740032010910000c0301c03910b0707910b90740c01d01c0203080002c0e000a40c140210220002101e030f0020800c00740d044c1c16a43da12230740d4030700014000a0041b64000b144250490f490510640444007064030042e5407600d00181d03a800307230b02c0132510b2440142c0c0140864400c00800080e001da0b451b440301080d541c0495003041845207000059948550f840030003030104880462045c05503000e1203000701c81490103403000c504280e0 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 719044892 1250 719043642 719043707
    0x405030d020315090901201c0f0b0f1005090402070309050904050a1e0f1203020f0c06070f030203010e072007030b0f0a090b0a0f0207060e011a0307060f 67
    0x4216100303c0320b000500810f2005103040c60840d03400000b0103008100d0340040114a01017620345880c1d18400180000c1c20041803400036881d0056030341040310800406d954690a2009401d0344440907100b109519000e00032843d04074014140d000780c42e140c1c6480e2030188400d001c041d40000000341e0910028450009160b160320b00c4843c0303e14442d80c05031103201c0d070740d00d0701c03241002010034518180700b084581c0c00001018286080d000f982c108020765221220114114041d214604a040030000701041e500c02c440400070382607008005036181c0c081c2e0212501c1e4110124003007449012042d07442c800104450780c0c020700c64941c03080000c005400c83c104a2813070b018902640d5500440301c180d54101003020f0f9103040e1400c0c0b50030000300340d818041c203201503c3c0d00511102c040c1010b90255520114041014042d604481c2c189500c001c5c1440090030070a1403500031300414800007540c9400c04079801b06450003045500c19604c658940c0d4a0640041300308955009207a110310440d80c604903e485003030b29 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 719046142 1250 719044892 719044897
    0x90b0406030f1115030c09010c0c0b0a050301151b060e070b03011e150822020d060c1e14090105281106010806130516090605040c02030408070603050405030d02 70
    0xe000f6680c0c60081c611400a210074103d41d44c035549034600c002d0044c4072a001128003205d200805c02d1800e40d15041442c06c00c0071505069910403074600d130002403002141508100918100c80c109050500c00c0041100145c502d11590705041c10a17420042c0d030340001a20030351100c018510303401300301c0c1c1d400340e2508280c1215034420f0304860b1000c641a190750006400c7c447c0c02001500015540301a6480308950280182c44003510342e076210100500d190204612070b14000301019001011403500c2011420213100811000b01001d000403212801e020500c005a0080b258540040e62101d07003040051241c2c202c141c00410380c042c10000c04100b800f0004d84608070103c040201a042d485c0d0256040d0740c0601507a082d00400c00701a0400c0004202d04580407608650087c8000c019010010f56454000e0600c1040c180800000c510340901040d402c80e564080e00c250344c0151004c000608003204166074034003a80c819815141c0c00740d2000e0001600c40c0d000560007901c2441140d0030402101c504106a8 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 719047392 1250 719046142 719046173
    0xa15060905150909010e04170a080a0e0c090703110705151608100510030b060c01090b0109062711030901050406060506160b0403021608030d0c0e0a090b040603 70
    0x2100600184a079180c05114040b118402c0342c070461620720503d020a4a00301c0502c5002c0c0440903502c005000c2c0140c00d204400350290310540582e991065050182c1020070503502900303440d03e00501c2e04401c0314001125030b00304100410254465891600850140c0b10300032032019182020300851001942c20046141c03802d14103101c094217031500ac04004070f81080081440200004181031002c03c0e0b180605580c1601c200740c071040440380c04010305401408007910740d960003000001d243c40c104c54040d80304a031014031500039003c042c1d980c0c0000300b090360302902400450703c00c090642c001011f450007481c01190007544012810705012584500d070f580003100e0a14190751107404101c00c0105620800010304002c40d140e50804001030a8a40030040d1103100501c2d44450001240c1414001c0044034540c0321605494004503880312100c54880d0003a03807816850f941050703c0030200500404030580c0191001e04041045c52520503c100501543e454480c2c000e59192004008030300c80c0d00030904035 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 719048642 1250 719047392 719047397
    0x131505100830040302060d0207060209090c03330f1906020f100c05040303030f1d0a05060a0608150a020c060106050a1e27091a0a08160b030a1506 64
    0x4544112201030790498080301d00e52032140b4200010300050340c41d581900c04000390160010303140c2c111031601800901c01d17068050340c801c0102041102400d000320013944545e240d19920a4240e40102140c070143d5070721148601000c8089070b141e001c0303045c40d9602d61581a401000740840d0b542c103480d49003185110f5002000143c001203c21005900c0c00c12a0b40e000b403005100411408025540040030390103140401010540c039861580c041030b803141c1200f60404015510482d038a00d41c8030382c803961503803202c2c800c90340c0b8040d5100041e103210040c4a604121828003001e4038520b84205401034080b64004c08121843d6401c2c1b0500e421024100f000c18068004c07604c4144d0303200701c070000191440c240e602e03842c55008401000c1e072150981c03002c00006001c06200c4c00d9120f0100000100d01606400d801c0b1a0491f481c01420f9500c000d107803800c407a201803054a003249e00640700d01d201511220034440309031381e5440d090000c0101000b80c1e07000f541d1003070040d100007580c1c10040030074076030128066021600 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 719049892 1250 719048642 719048683
    0x302071403040b0a0f110709060807060525050a0b0403090330050d020c1213080a21030227010809161401030207080703080a051315051008 61
    0x10848604600500c0c404414000c50500e0b00d03129000d4003a20901030b4400401400c0800d4802960143c0f402d08500781440c0e007510075840e100e5080c0c030000c0c00c10b4440c10b500b91054120006440340030b00c00300c907000940850321440c04200d0500800044801c200d0880705072240d1b00c01e41c40492200158180643e10a5803001502c034610700304030f03240703a4070750400e00c0c1d51100c078500910180e070101a10f05107120445c240b542d1144504070188009026116294880d4054040c0e0300243c0c24204006012444051040030b03a080c0d2610005a03603482480300050124250088002c2010034610b170528080000c0e00d005840c2000003c000c0c240c15201202074000340c100d0080c2070102d507070484080c0b42d03c110a2030041006c1a903c081c1d03100320342a03902c20f650001000303c40034203040c2d00c80d40440303040c1c1c5d07002121161780310040e00d0001c140c58400c86480e485140380c1008540c4031101d0341c2c1c10110241e04000c041e4200e21035107042c04010403014201d8003844460040005103803106010440c21480b100c440740f207 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 719051142 1250 719049892 719049907
    0x190306090c1b110a1d01050405060102030909220302030318032515061403010f051b090621012d14030c041d07090501060504150e090a09060c03090c050f011403070302 73
    0xe017000010303003141c0d2040c1c1c100000c2000c1a43c0c00000e40300398010880740c10f101d5844001c2c264a4184615008806c0e0021201c0c14a0a041e000030085000d4000c2100741400000740790022500d900800640c2041000320024000050601c4682084030030f004403203241003c1c0221051004a500c2640022581c4290b440600e1441c5001e100d49204a82450000d001601e8a490081da05802c1c4090803440107501054038001a01d99400307580c0f811000c4a1001c1d240d180450a640341903c00340b003a07055518540c0c0c2d024846010070040040f103003070310304100f100c02c509018100804103d403401c00c81e054411005441c27007a55640c060312417445210019001481e46a1540c2030401c8402c0d003210300d000e418440100003550b0f000c0308030313804c81d144822042140c811706141162480400032a50380e0061480741400364040340f55001a14080c030600b010004c10184d00000d030190349100b0005481c08560b00000c103c0340c00c1804145d007005a052405c41100b0100024002480d0008c0d114000003a90119007035 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 719052392 1250 719051142 719051189
    0x507050a05220b210c010c08041a0c100603051e06012106050f070e0d051c110109030819140103080c0102040504060f0311010908100f0b06190306090c1b110a 69
    0x42201c40021f00c0c05000c105100d40300e840300c038480c0c0d00c540d4402515600c91000c010170b00b002a80c2c0640140781c107940e900920001c0c04800307401c46010954190281905036680d5540c1040c400b41d40041c0360300540710340c2c0c0c41c11903d203d8002888003030991646000e810b090000d840352194500c148820f4031712075010b0400e000000c10610700035002a00420f582c00b50000442e00c00074110600301080d14554540f04078038503084070310a004418610896080071844010160401c1d1041c0c0719001c8918044203002d4038050740c070152900c05d44615681c0b480800180040341450700240300c01d466030341c0050300c0c165440c800301d012150703664401200309188400034070400c030307240400003481d01003440c11040c211f041c00c81341c5440d43c009042410109a0301c4180300b40301034050b0070000b40002c00030007d584035444580510304032985004510000b07480c201c4c010400100620420181a0700da50701c440703040e030009034101207041666809071100140345c240055507130717509200d5070060f00d01449403421101840840 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 719053642 1250 719052392 719052403
    0x80c0d11010204080a060c0e030f0106150e09040f05031b060103060b0108060913050c0d0b090618120c0705190609050d020d0b1803160507050a05220b21 67
    0x11031a4010007040000240000c4c802c83c8054200c840007900941040c4151000c2203c00c6031290503014601c6821100d5506602802c00c950b600105039104e411006c1c021200e58640c0c0d4480369100b000c003408500400c0d42402d41c586c002c1d00ca501140d00e420350096020482110310581ca40c0180c4c4030a00520811219010f0640c1c3c1020a013030545860800320009910f2200091414544403410b000842c00c0c00010052080f48050141c11b00881d02111704200c00300380811660b0400302d1091502080ca08c0d183e0308030340f201c411900c0c40a0566444000c40440c0d0755400009400704511540c403010071166100c0c1d07040c10640708558200c0c8612443c0c030102400220890b0301562096468005030405a12105001c50307105502c02d034131888655503820160281c00d070b107121500051001207040503400c0e000700c01030a1040e0081088032032265480c410000100c0090081c0c0340c010190b100d00c040f4542c0390111540030391180c050081500c044280109a529118286104d5442e10900500e030002c0000d024 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 719054892 1250 719053642 719053667
    0x7172a2208060108060105010f090b040e04060b09280f1416020d02070513140c04090f0207020f0f0117240d0309031103070512010603120206130605060d080c0d 70
    0xb4020540c545107400d03444840500c100350510009444651020784078003d030304054907004024984880d250341002d084e00e14122030407228245807a444100c203250004542e0f108082c2071038a00c118003081cac562189885100c001ea02c81d030796220310b05c49410029500505140134198102c00c4624a40050100824410744441c2015034001002450481f50701203a414240d65003952902054650b00041c4c0c0010004000e9144401c0320790000d10102000744d000400c12507000b06800d0290000c034400304012881407880095100c071501c00011070030308103100200d4074000d050400b6541104000d02c001c441c41c108461038628590004d06a410500c0e91208450b80e115080c4d41035880c0050540d0050400783e840c1c003020f4030556a24030507034660b44d000c001100c00b9080182072200e282c01c2c04588940a007001d800101c445040700016901410310000d115071094070100003035401c91480b521924001c140c042c054a030404805400c2e0804603400c3c500a104000d1610000e100010b01c042000340700140c2c564 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 719056142 1250 719054892 719054909
    0x3031b070f03051606020c0f0705060f1b190503030f07031e1a100203070c0602030a050304150f09210e03150916080304090507172a22 59
    0x30031038000c51039145050030860780c0740c01c14a6030b8062060400081d011401c2d0000c04440c00003803132240250022903074458a20078007040310744107a1200d0411031240a08114200c1200d02070001c0110340180380009451440040c0c141c412003450310302d030303a031040240150544441d440001480500c401580305243d200a55240400c0354607450001c3c4000051758018040d101c54a64210b080b007811200c1e2940700d4220001c01504052035060800380d220f030040101603401144905001131110b0000c411902e0103989031399044e240d5540d5583d03d128858180220440082e0b40d0750602110000c0c42c410218654042c071003c610071460403200c81140702d0038130001e00c1000305510022086880004030484440b441581d20040c0340c1e20102c0651420a0340d598040d2030001d0403100080d0600040000c1c800d03110b0050b0305200503500d4190a40b80904061441c841c0f00041500050032141d00b80781100ca11410361484003080700c001c4152140300d4000350304204d0880906a81880000000f0300c079a00106000c0 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 719057392 1250 719056142 719056147
    0x5090402060901030f1d0a2a032d08040509180613031806030c12050907060f0e0901170708011a1504150509010806010c020f04020d0f0501030503031b 66
    0x6034040740c028010086100e051585031144443c0c5500c07280c110611000190f545810713441d14140c0b01e42d075219204003003a00d88c20300050f50480200258100000c200300c801404e45100c40c51b65030f600300c900048465207a503901c0014811340c00301800105481d0054010114591140d00349000c00082c0c580142489090201091000d5480e403404514942d016800c036002e0031001d0410b080903106110018400d032805084040042103c0d034050344445032000b196510f00f280700910b92201b03011208280d0300a19282c1c401d282c03c104891080404e003a6945003854a4419000e10b01c0101d082e0a030700f0303089805011400c045400100d04100310000c011720505009000070540c0407014000640b40400700d500520070401e000080c000c01004170741c000c010040c60740319103080c03140c001003080c0c11000c1503a00046010000c01e1080d8420b604210080c3d030001c00c440c00e00307844039042000035480a00c07011501511100e48034103414541c4222030095000354050b50342d9103051520b104041d10010300260444105 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 719058642 1250 719057392 719057401
    0x3021f020c01080604021c0c020d020703050c0d030905120f010c020c0a0302102601091b0203120901110c0303010806100b07080702030a0f1119300b100f0509 69
    0x4041490710003c0c2003c40d41d68a44802140107403003080c0d045141600400030308102440540d000040c02c801c1355081d901c00c10b681c4001240c48d051103106c00b41140d4032503103001001c1e14000c01c0054095202e4140b1845250f07886c0c002c12041406103031445403035002030010b06610182806000131a008a201800c480f5003450300007050603007036000190185004c2071209141d540148800c0d41016110610a0010465070291011140090081390380841c10f10003030700c020308640b40c2881706108079034000e0f5040101c080f4092000e004005c290304036541d20f131040003403112400b1004140e4150000091580e0b581443c0385030380b5041c0080c011a00341703845803004100e4522600151011190f00c44803466440741c81e400000e28104a0103006400f4144148901041110880c0100710300380303040c2e405030010304003613081e40c1c802941c6200700c00030203007074149000780501600c01000700e48007101c80809030a081078a0b810500380c0c0460b00b1010500c0d14040078070610034400c4141d40100400c85001229161 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 719059892 1250 719058642 719058647
    0x30114151915050d0b0a0b0c0f0c01050f16080408070e061009170a170c0c01020c1309080f0712080a0209010e151905041d06030607080c121003021f 65
    0xb06480c03038002c01501041441e032504583c1c000106080300189980a0703580c850b000c1c200700740e000381c400c0c000a11800c0b07860f55154002044180c20010140c44560038050380100c0c030b10301c6500c40c00303840c1401c24407500008009a014006030000c2e20310000241707a00b90506030000d9060340c02815842c8140c03159641c004090f50700c070902000707071503100c59070110041291007132a01d441e0003094000c20340503180d04403031110491803000d4070000301c1120031203035166070070001a40c4070f034400c564541d0082041e401c90f8196950917040043d11030b1003007000301c1c6800043c2d0600011604054800c03210020641c0403040c140d81c0c1720340c0040e0446502c010440c606140d600c0080c100d003000c1c548060045000d60341102d1142c3c3c0c032000b510064408442c20290809100b04002c4c542da109005000d5005210041000c2090304403811038458032004d0001d040d19101d410056480c450300900d507075071550041041c150b04c201c24403011030003000b0114001d00340d1411441001000c0180c800f0084c0491030482442c90040d5 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 719061142 1250 719059892 719059919
    0x408120103081b010e0c45010902070f1103070302090c070605090316061d0a060603020405011a0301260f0a0201090b0304030e010c17040303090e1302030703030e0301141519 76
    0xc122050500c80045801c0740805139001c03c2e00a80d081101d980403407040000e83c41d181f040c1074a130b46100c0304583e00d80902a08a00030b24002504d00d0560080d50400a4100040148030403401401c82d0001c99503980064000c8504403244d00d940c10010034020104902405116048040341d40038508040b600036a03000400790683c00502505e0300c8481810222009607843c0c60f45114507000d458800c5113906015019140c5440108d00171f5103010000100000e1400d4030300100340740b1811407803844c0d01e4840c000f080850007602c070049440018402d440d803803808000d80d416050020015120310f00c9640005000500d1a030b008100f0400100104070000e03522054180d800c0340242082400000d090804402062007502440e24100d0b000401100b07258010780c02400325801d402d143c900030340d950350041d41d051000700b400942587c82070700280002802986c150300800009000001c0b000c40c0001d014044010984940c89001c0785d022151000341000c051604060781aa402030a0135441c1940527402d03030 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 719062392 1250 719061142 719061163
    0x815061303202710050a0611150c04030b061c0c150302030601050919030b0a140c0403020a12140106030b16090609270e07080d0801031203050408120103081b010e 71
    0x1500c00400103942c40130001d1403034020b4000580110205070710340d44080c1c505082c1e003c502c1e160b885a50007554581c4a2071503061f2003103541e900900c3c01c2c20b20355652004a40d5010780200e50003429110030001c01d0030098800828035009100c2020b906141035003299002c00084240c0301018010000c219603039802104441c500c0b40c1c261401e2a46081d20f0005035280380301c0382c0008182e40c581c2024008030a601e50002c81c58240000b5115525890740c40580341c00f8412840001d402c500b0055080003a41c2217001c03489810340c002c0407050644008003003003508550084e002200c03440084010300c035000100e084640e83c0e84206040c014140d50400e64058490100791150802c1810f85010040d03003c04020108540e046540c001441610480c0d08101d40780e030b0752405840114494021b0520384d0794030030403810741269000b960342c280c2c504081d00203c1c09031000070410fa92010003044070400345c0d490589064001c5001c0c0107455225483c6c84403a07400b040c0008001c0c18075a042c06c01d170b02e07020b0741c0200c0c1c00800d0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 719063642 1250 719062392 719062459
    0x501022709161d010e09070801060207050a0302090c031b0c0d171017010b040204090b15070809010c030509030a240209151809090307061b081506130320 67
    0x22620303c1c0040721600d1030f44403000c0d04040240103128803d03410600c1d0314142e544940030b4070b50150325541800802d1002c0d1201a520000c43c0d8003180034280300400039504101e4070300c01369008a40c10000c0f100380d0f40c080444450b1b190701213101c1c008003690000361404e10880142c0300001a0900ca545001440a913000e0710584903040c8103403028484c0250320980d03403020040d10654480303039904001c0c001800c08014542c024001c1c0030500c52902d60381030460380040d40c061351090401da4100c004452440d031242085040c00303020402452a980d08000000c450303840340b02d14004d201d003101c1c04030107001c000030710050741d4600600a000296541010108582010003c40754441516441000d032094404191a402400044c14048090b001000904800c0d02510051114041140003020940e520038140d9000031800004100f4464030700c5140600328400400041c103000c18035220b401c841202d5402210702c0c4071408032a485406604511008051b030444002a080900d9a181e642e0003600c03000c14100c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 719064748 1106 719063642 719063687
    0x40b090a0201120b01051c0e010b06091003091104020703020d020d05090a1203140f07060e0105011a0c070f142416050102270916 57
    0x4050741079442d0b001e124110f074140802001d8160703105040003010884140f5a06500070000e00c5890110300c002250b103a40c41c1c038a42150b4031050300901a040600040070340d9034582290265090310f604010611710702c2440c00b40c00511000303003801c1c0c0c0540f01040070010f05034000b508030780302103054003100c00c4030b4030802e819101c0b80a00010303540d1044070480280301c00524113140c881468400e040c030a00e4048115404020358020002c4607401110101d0413806000030b078003c04841040310310080150f541065000300b1401260480001d180b18001009070306914204101401003050900130b203110b5480319070011400d41c071204040c0c8a0129000040708145080404140c2c140454000500c0c04130f1000800b020f04e8401c0005413125542449110000da440c9808142c44030601c2000d105800424001c020210901600c1c1e0001034000c240f0344a04550442001c00c5441d6001c8640103 = true := by decide +kernel

theorem cover : BRFrame.Cov 718884892 719064748 := by
  have h0 := BRFrame.cov_init 718884892
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718884892 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718884892 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718884892 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718884892 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718884892 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718884892 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718884892 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718884892 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718884892 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718884892 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718884892 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718884892 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718884892 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718884892 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718884892 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718884892 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718884892 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718884892 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718884892 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718884892 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718884892 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718884892 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718884892 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718884892 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718884892 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718884892 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718884892 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718884892 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718884892 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718884892 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718884892 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718884892 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718884892 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718884892 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718884892 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718884892 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718884892 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718884892 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718884892 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718884892 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718884892 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718884892 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718884892 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718884892 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718884892 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718884892 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718884892 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718884892 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718884892 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718884892 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718884892 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718884892 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718884892 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718884892 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718884892 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718884892 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718884892 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718884892 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718884892 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718884892 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718884892 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718884892 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718884892 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718884892 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718884892 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718884892 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718884892 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718884892 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718884892 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718884892 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718884892 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718884892 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718884892 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718884892 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718884892 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718884892 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718884892 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718884892 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718884892 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718884892 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718884892 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718884892 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718884892 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718884892 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718884892 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718884892 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718884892 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718884892 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718884892 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718884892 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718884892 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718884892 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718884892 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718884892 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718884892 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718884892 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718884892 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718884892 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718884892 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718884892 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718884892 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718884892 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718884892 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718884892 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718884892 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718884892 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718884892 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718884892 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718884892 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718884892 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718884892 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718884892 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718884892 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718884892 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718884892 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718884892 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718884892 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718884892 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718884892 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718884892 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718884892 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718884892 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718884892 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718884892 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718884892 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718884892 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718884892 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718884892 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718884892 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718884892 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718884892 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718884892 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718884892 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718884892 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718884892 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718884892 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718884892 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718884892 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718884892 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718884892 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718884892 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718884892 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718884892 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 718884892 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 718884892 ≤ n) (h2 : n < 719064748) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
