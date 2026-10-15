-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4587
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:06:07.600726+00:00
-- url     : https://prove2.me/submissions/f109de59-9224-4d9a-8c60-d6c6f41ca8b0

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 824820143 ≤ n < 825000000 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 824821393 1250 824820143 824820149
    0x15120115020c010f0201151701050709052d091608060a180f020d0608060906130f020103051e0a06240e060d0609051303080a15050f131113 61
    0x10400c1440655056000114050402e40900740740e407596101032400c80c090424511107800000980200003209281d505c0200d07100c0c017400d4000c0c48503035140310703080700c18404074459a94040384104298040043c41c240b004480d442c03003a283d1154040c40804030f85009010380c1e040d0303011815100072012a0b944001d0154010000700e410401003890002584040059503100c2180203903108070044614545604580c00e002c404e0006000386c0341e4403110340d5182c02c01111811014040c00b030000c4c001036501c001c1341c41950740c0b00e01006159205500114020000104802060044a104007200c40c440c8580c19228550050010409508198011032003080c0305c1e6449044110398022450354580040004804100c140c40640d1605404030548002d040c241c4d112199127031810083c040d40c0e0304103150480040d8040d403a01031040d160054240120f07114910007004400340340000b40100d2034684007103e000c40c0f006113012a25519801075404031080d14030b000e0400440050408501c150341c841c50801 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 824822643 1250 824821393 824821409
    0xb0403080a05060f1e040b03100522050a03030b0301020702091006030c0c02030304050405061522080307170f070813171614040603121d03010e0a14030405151201 71
    0x6880c0c2040116001d0700611742c0e03011040d16110940b200545903075014144108009044450106100760814000d183c169001d5039104817404940030050300c0b80d001c050039164800003d100c1060175071400c600403daa51b01450780741d502003002c100903a80341c20b44903004503110340040d0b40e040d2400780302504030303083c2d101d010303042c400282081c0c07001d650040261011510240e5001c519540c5903800a0b0307084094038403008071100f001c6891070124410107040f5840006818140a000c1e4403400170a0b03032405204401032101800d0b5130300942c040d030308101400c1d106815042d040c0c14070a0340d56500105800080c0ba442108552100411407010b0b00240b65200700186409050041c07043d0211a1000718a8014000510110762032001191a01c0d84070344000e5030411194000c0d51b001c201c00914841314884942d6141241d0740f8014070501d4184111607402c6100720040c003030410b041c2d5075020301d84824076008600e80004d210004064a8899041b8041180d00d482c00383d56041c0040c505002500c10382103009 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 824823893 1250 824822643 824822659
    0xf0703020106050405070e0d020934200a060b0102030910030b0a0b071e1104020304050c0a06141210090603032601030803040204021c0e070302150a0504050112090b0403080a0506 78
    0x101c280c5844a2302c20703540340c040e100380920756a40c140007900101940a045422210b80c41c282e003254203141e0b4a0310031120140c0d62802d6a6280301034a0102c00040c80c4a09100e070800141c06000801c40d501000d00301d013041c01540c1c00c1c1201300c0700182c1504044444000070988507105080c0d14942241c4801c00f0b49198500582800ca02e43c0f1101034222800016000b5184040580014082c5000d210000c44c04020000e558900d801d00c1c0240e22203c1101283c0e0041d03200542c0030400038060f82c040141541d00c4502a030500541c11907042801401030030b4000c8408410f01c002c1005040790080d840a03601a8a9815040054401c0203c03c5034241c5a040341c01d00000700140f0000303000c401202c0d08160125400b6840d580e0054802d22150803102c0005e900d2403400c0c0400e40300042c041007500490b8002c45c0c0f41e501c1441e40000d6000d140c428810f4140010700e0400061140750700504030504283c080d81c000041c1c0c1840c640d02c40116613401d460540110700c3c60820403640c1c5a03240030b04c9922030740c190f85a207 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 824825143 1250 824823893 824823917
    0x12030c0708150702120a020a06150602010f09021e011419081305071214060907090b041406060c0703080a081009230910053402031606020f070302010605040507 70
    0x25190115030030717101c0012100080c4280c1d0181308100b0303070603603075040b8000304018080c100c84001d04205a01c40c441c095400d10428044407802031140115454000d01000d05080d811034042c0340c0d10307200d402c6444c14001418254000322042c000500f844080503145445d541050820181c40314030010b00070a98800700100031000200f001c141302e4100c8036078071003031642c60035070749001080c00e2900c0c000300800b0320440f0100a54484000b907036030101d901c207440410440724048140000c0c3c80c400c901c8955000b0305c040110350682413410041c01300c004600c09580230075440741d82d01c079519031100340120006041c2d101408100e407030340c1c1c0500005001800040080c6445c10b0b083c4100b80c10780c07802c0c0121600200c00091f0121100b40407011040c89404010406840e1904441c62150344030041e00701e0a402c2c00011400c10488403912401c05040340d0010b40c03c00c01c10401000c1c9003050350700200e07039a540900c103800c2140c21410280c00001d02c0380d00081091030511041c4003c54000501450802122a8400c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 824826393 1250 824825143 824825147
    0x9051515030403140d06050607050c01261308090310050f060603040b0a0c03110412110a0302090f1302040e0f012a12090c0b04330e12030c07081507 65
    0x4c0d00380d0074040c00007140c407010071303151000c01030043c0d500081d040b41c0001959030401c4000b05042010748000d0f00c0306080250504030b200c0b00c403c441c0b807080700c40d50b50b00f1022682106405000304400d1f07110b400c885140c81c4100c0013007410101082a040340c52a02c480601003425110004a940000151000d60440ca0661190b11030748030042c11041145035580101402580b10340c1208450440f000950750f919a502c681c032914802100005036039401d4030960352002d9141080780b003c212600142454100e454400c204014094040c141c8414035005400e001d005803210700401103000c50580203404050f034017018071425510181c05184110040c200c03100c600041406c014480d5100b2791030140c40d500c0d641c581d410000c104d03080015200903c008400249040c0c220028010b0300c4a258020403071aa0100f55044c43c8021000c00c0d005200c042c3c10342c0d01445115040061030007800030400c0707440c202c11986141c2990b100030f03480502501f0010060000210400500b5052021113050041c04c1c82c1002c00 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 824827643 1250 824826393 824826407
    0x105041203150f0b0c060604020406080105190906060503160e090c0a0c050f01021903021806090d0b0a15060207080c1002161410050717030a0609051515030403 70
    0x80040c03507a0b8551a03103203031456040d01e10281041080300e0000a454890620164016106501c041e1049400243c101d05260090310115002600c5004650b401c6c0f104000404d410108201c2c00851520000034060100380510f500401e050340f6a507940381030031026003121301c150b004a1300070300181500001c00e40c0c40e00444264032980082c82e44e502d13003103c0c103801c82d413050325820701402d544912820382180c00010341c014803c6511010304450001400030f000e030700ba401074003880241c8014010200c0c0843c10240d008040400f4000c120310302c00d4070f695941d040030b4001903940c08191691044030240010340b03201040c000e4940b5000030b2200505d0503003007550722920030310007a004a0b06150b1500c9228000c2227000c0c903504943c5502141e0a071078003044244804c0b483c01c1c0341d204400040000c91103d0085c011104003d4001c5145412094403202206803079001601004005613519030024601405224040c0102101d5008521405110042080030800001c9031030701c04004206100001e50440a = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 824828893 1250 824827643 824827673
    0x31502120c0c0118120807020a0507050409031b0c050406140d231f0501060806030a03030914120903010e0105010b0313110a03030210050a05070c06090c1d0108010b0102010504 77
    0x1409580d105100390040f0301418241105001e0303045507007000740070880c0340301c0d1500d5084c0d550391b00c0c0080303940c8148081360740b00b41043c4050515000320f02d0070300c81030a0940004604901905215004100c0541c422014000310641510095060741c0d0500c412b01e410b0169100030b123601c0d1014603a0011400c001806105071000c01400c45c0381c0c045940031a5100c402086000611903c2a20b01074048800c40809142c0c81c2d6003003450183c9840008100a0b001c0c0c060366020340713000750040001c2d41c01d45c0e609070001c141055047c1c0308680852041c0101540810000c04084111506a600c4410300740901d425204c03940e119940d40d906120060101d03140801c01e895001551496080c80300301a801c01150702e040040040d034009884002c040241030300000c8104151148003400c200f01ea42d4140380c5411a4000e590310b10000e030190706950081121a00031035050340c00b9003202e000712035544507004c030300c05810b00d08140a60181001023181301c4080c810403021041c20b000900c15807030155030354050115094 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 824830143 1250 824828893 824828911
    0xb0102011a01023a02030417030328092a0e090d081306021612020c0112020d060e131209030f120e090a0e010b0102031c020919090603150212 62
    0x2080f070b041322400540340c1d0590541010300c10024101e0f150700030345950203030088000301c120403004005550400000c5034882d05003222814648075001c1012118038200349114004251075410620200310448180d40401130045071610100400c0c4207818109543c56000440d0380782d48a040200341c41010600a800c5641072610010300d0b650440d01100d203d0440c0805003c8510105139a011403a09070100d522050280c20100c0003490040001c80e501e45603004041c0c00240035460f400604080d90f0094044100d008102003055521000e13442d2000208441070424100c03050342c1102070145400f2403090090062030003100031401c41c0c03a40c14521545140080c00e10400c81185888a0310651103800b0798000280746845a040c08030b00c4102070090b80d10100015441c1445000380e660000045490040190302c104161140b40c0385260000c3d000842181e81003400c03405208140c010885848014184040c40012103e0071418450014a408088805038910411010f1507000809000c950300041c08 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 824831393 1250 824830143 824830183
    0x81b06100504020c101e0e0d080c090a030818090f01030201110d020c1003290f040606020613021c03030e06010501090303050d0b0609060724020906121b040602010b0102011a0102 78
    0x2408001c0d40120703203814001999150071f940c4000c1c00c2d00070468036407a001a58440f201500c40741c4030340441d8400ca591203903016075403941c01c02c00500400080c044815440cad145003503191612020640c00041215111544d24040b0014401c56030410410a00c08030f00030700400d10305420280196880c83c907603000c030b48640d003070792100b00450b0300c00e800200289050114105000e039032942011144605010354912444244000084c14241480f0360401c41d00c590340200b01c203860b0304a6800101144038001e07178104041075045031010004140c22025903102c1d0351f000801000050a0500340803041c2c10560402c80420010004a503004003030790f040201070900010500c1c0c0b0200001d042c0c0c42680102504038074042080380501c0050402c43c440c4452403072030019074282c84500f00702240f1846046030350054003132003480302400f6000001035200a074825407002e00740340724003588402c0c3c20550155006070f468040603d1596420b000e201403c1c24030b03100808c0d003105850b0010791035070007410045c0c001140d1 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 824832643 1250 824831393 824831411
    0x2091305010f0617100c050a081803031312141b07080d0e09010f05060427110415080402090a0f090c030c0e100e0a0207081b06100504020c10 62
    0xc29484508003100403030080008a940701903002a03048850a81c2c10307a40501110440804401d001d6001c50f940d19a55080c0b9015082c2819522482c0141c4140e90240310052020100c4108000860041846030304140e503255080c9081820b50180142c41420401030010050640e100c207015075001c09104c004081d038524920038402d14011248d40100c0c0c65200c0e0401d10020650030000e1120b1005042d110000d0903a250000f00000000500c102a000038041004114100461800c0302030082c1c01c01003003118200c407014042c01c1e54101d0781c10900e40341e80050104023100e64503d0680405141d800c2490440c90507030002010f03214001c240070b28040d109e101020484000e030707000c5144140e10001c4802c0300f60310307402c3c0f01ca00e001c91130144503c10a4603001242110091013000d8044410000081c0c140381e40706148640a908030610031501c8500c03c2c0902044c1080c0100d8040c1e205034071000500561500741403922201289901c11409588100901c070300d4800301048a09101440e14404128003403 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 824833893 1250 824832643 824832653
    0x1112150606070303140c09010216050915192c071403130f0f0b0907030f110a0914060a050f0d021017070f180b030610030243020913 58
    0x80d85281c1e10016641005c00c00a8a01c44500603000488081e8200d429400741c01c2c602d0b0540440d10b000315940910b218000603810808a40c0842031110050320b0600001404040b0041c00061034200100002d00b0281030400184412031142d152041d583c100340040c1006c000203015010544403103500702400200103410f4181c0c10301c0074400e995001d409480d0601540c14021101e10211340300b21044140706010075203400340010420150303030300901d001105264a944554100b0190a14142c007d11203010000b685003041c803481c00f444a070445010100d107018401c02903540d5071307600030520590f03d0720080045510f900300c0d6440c0d12503054440035024401c03503c09552141b08142d291000d080140104011998030041105240c1c44644801e40442d074020240c0c10503000a011b8042440c80500014509240c130303045c1c40e160845903050040ca4a0340c000d541036080504502c080e1b0011071071028182170102d4080c000720801d906c8018030381c0c0307100c25a8002000d10601038156000921000c81d420b040c00 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 824835143 1250 824833893 824833901
    0x1504110d0602041a0304060606030501062c0901080c0909010c1409030a060905030705010506030a0b2e080c01090504180f05010f021602090f090309010f02030702030a1112150606070303 81
    0x402980c0300b60313420320250090700c0820350088a040f20f1460030910300042d618024011136041c0c0301c0640302c148103082e4005a46540304c0c0b1001400101400c20912030312542c0b01c0103841400303044d4480182241d90341000038401481d030080c0404400383c0c903104240c90341c1c5a001080311070840340800c131151781d40382c80b100003464641c0c1d0b1a0701034841d81c5452001e1040010020040c0304040c8610024040e943d1001e04054403810a410090128608040004c0d6010402c41000f045022a2507210304001c0e00c14031005400c0f00d03a5040b45261b030380108180c054540c0c00030600002000c0440c1d0500c803031384a82e9807120b508130314040001c046040c0102c4030400c1190a422002030007408000c00c5403545200f81e000c00c580105500240d0094011402044d111791000704018450741701c0781c00440c9404995001114958007240c0c40c0811800240309400059800f80084501ca0b4000c0501d0500000342408120b01010000284945030303100500303400e2000c0c980074406030b00581c112030742500c0d45100d04040e4094 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 824836393 1250 824835143 824835149
    0x905061305100e0303030f04061b110f01020c070905221a09010212060907020703080403060f050709060903080a0e03031201080c0303070c14150f07051504110d060204 73
    0x452004110181503840d800015411210202d42c2400d240300100c0050780c12901080301913415400401c00603620300c1140c041290000d01c00d02c80000c410840b503ca109405d1000103e100020b80708100a4000700410812021114a8003000b1407030711100d020100e60b00c0c001c034030424900503192000240221181c109158000c044040c140d105003c561520300703030b47c2d5107401420841031640e0f0041409018140f00740c801a2050035079904440d100c120070003d0601c2c00501c07401c114407079100c1c0807000401000242c0002c61042c40040b070b5a0034100016020f50344001e000c00300700503003400304100d820b5000c01d0300700489400c2002c0c1c47c1e540c40070000440d0040c1040e261503415200001d00d101050b02c1900e119030490356680295a0740342011350400da22803281a038064000d400d400000d2204001200e4000c04c100002884001030700300d91402c40516070421101803004003804910182400001c1c451407d800007100072072025403805d5602d0b010103400f4040428054400e0804d43d200304001c0394100c41c05 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 824837643 1250 824836393 824836399
    0x51501180909230309010912080702120118110307080a031e03060f080309040b041104050121050702070305060c0301230a170d030e031603050c010204030210050403140606060405010c02010905 84
    0xd595400c00d24035a130394000b42c06540001d15101000461450304603850210980c4040100d00d403e607141c0800403107100799529180d080d545d0301c039800280300c4218841d203601e501c101582031070841003400b01400e00c010703030b8044032150f00b1040c5402c001a501170504802c4ad0500340f1408152044141c0440003810b00303400105140f08096008a00404004041c0a00d0903080700c092002c0c0241005000644405901c9000c0d801400d02081c4a80d60040e050f200500e41c0040036000380e5044200c007030701601c0c0182c542c0c03030141c0c1000300e042c414444148500396010342c01c0284140745500d40000000c00b400019040903112a00e06000d50b01c6d50307550003503100103108000407030b801d400f03850300c03420340f5900c07050440c2d00401e192942c80c4081c1e400100c150340e20b010040384070800300b120584083c0d42e070b58042145100c89560030880840180d49460901c100f43c94603507169610f139401d51811030040d10010b01c0d00070183e0300010401c0b030569240c400315002e0320401c4c6402040000c540c0b0042c1c403030040b15002554 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 824838893 1250 824837643 824837693
    0x21c060902031203150f010e04020f070f0f0b07022a010e04051501110c06030705030c07080c030a0e03030c0a03110f0708030901090e310f0303051501180909 69
    0x2076a03292140113540241d101c0350564140c4020750040116034064540c0c0c1c580480d041810603821487e00780d01a1520651000095103031150941da600000d81c0e0002007200d50f51702445503402401900d41ca41d07903100c10a40010440840101907821401410003001c0140324240c036007006959119030303000da100c074078090001c0c0041e040c20800200c82c100c46680c8140083d105121550400b1000111445000d80141c0103920715100c48a08851541c4000c01d4125904001c0040c0400a400a001000d140414a01842e2900c62108000b8079940c04085000c0c4668070522070b5010414002c1120000c1d154035080910407101202080d43c00c100e1401300c5070b6000d005000380011440c001000401000c1d1090f41c51054a544a1140b800c0c0380c5400c1c0c4400081d00300401260942d00601d9600503c3d00750011442c00d52440c1d80d0381c6402425a0b244812030000c1d8480c0c0510a07940c2c446000c2070803400302400d01d0240b0b03190701d03c0f03400d11020180c031459000a8846035100d00b802101c0fa00401d5030740172102095 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 824840143 1250 824838893 824838913
    0x30503010b0d090b090d031b082703070303060812030114100210060f140105030106050d0e0705090a0f050117460c091107060c030e07060e03010e0a021c06090203 71
    0x51b00c444a4040260209007049003c02c50644415081822a00b0030745411000e9120603803508403002ca0f12100b04400808584810030b024010005000c1061081e500455004d040182440c2448000c1100c603001c02018030043c02040e41c2c0511040310800140c0e05010b0700790b20604200c0c60305500d400b01900307071031406001003102c440040610f81520741400d288500105103100444952000748100c4001450a001d01d03440b00b290340c1c02035000c01e41ca03107003161105604d440020f04604425a10783e80229034801c1e1001940d02c8500400b401407800100d0a4940c1c4042400c15807104841c10b213088503035620718080010b0781480400c0201c96060b40100183c0040b04076012a46469911410b0b50f0300c0b824048001050013043c01013120040e0458100c50510340f5070b503105409441c65802c6001416142c400740041d002041003440010150341d500e4081c1c40d24010241740c00c55908415850a5400c403c00031009616200c044440010903203000f011140354500b40030000b0200f80f20f0003035042c02034050035 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 824841393 1250 824840143 824840161
    0xf050a08030a1a0d03020c10020a0c0603020d0c0306051e120106300203070b16300206010308160503040e0c0d0b01020c1020011803140403030503010b0d090b 69
    0x41110000d2580c41c1000d40d04000c20001c000c01c0d519002801648840c07920940c0b4240440c040c0340b000c8440c012940700744941e0b03075212012f44064000200099000c10382d4095080309000341540c03200c40f400d0400c900c6003020041100300c0204949080c51403021000594191110300c10010078101c007030002c105a9489101d80211840401010907010f01401460b50022003040f0301c1c0700c4e034240d0080003045258038090310300345560404144c0c100c14005214119000c1401d03401c0d80c02441c5100445c0d015800c0012254640c2d074981e5a41a8007198815001480014049012038080304241d40d001d02104d1906d1514900d1403045403c0f000d03242d0520428031031b4001c0c00c02c0181880000400052109503c020300481c1e540c4550060964003000300018403032102c0c091640d198845c52404252003140c0440301c0624251900950b203000c60011440501b014941d100c1c03d200306100403140c4041c134041c5962802007007400180560394058038001102800c1c44000c0c0e1110354a217a21568070742003031401c1800 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 824842643 1250 824841393 824841401
    0x20f0d0f15050109210f020405090609240f06030109020d060204061403091e0309030a05030904050a02040510031a10030e07082a04060b1303140a0f0f050a08030a 71
    0x40c018070904041d0040344070760085035124141c0c0d41d8a540103000da002d41a1550300000060820b40744011010726045c01360b11180544c5219030003c400030282d9003045c44030103152008140349102d0001e03078960b030b85200304541d248075500030001c2e142c49016610349000080c011300179504020351100b81094040100803698001e07004403025911040a0381480400d540101e100c1100d07142072540100d89501d4898681000c0c01407040310707000c1224105560303100807918003108034406a40d10341c0003040c1520186000c0c007034207510103c44001582094030309004948441d56120400d4107060f200c1c01d88484004000c80d1300d0305507840c000c210307a803c8489414090010a4012001040da0280040c007140341c44000038201503507844021051039441c00c80300480c0020101c8810356a002e0740f59280042c1079070591001c1e10040358102e4624800d5031075031034000d2588100729004c50058201044120100d21400111030546410240e000005291403a20904080d5030702e070001c1503100c0200034000c10001e1680 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 824843893 1250 824842643 824842661
    0xc030702241315031a0121061710590c0406230a09061509080c09160e1f1202091509060f190f1809020f0d0f 48
    0x30f41c810724040300d5808500380e4050750944011144101d803001c00d154400c6150910010300c6070301a0900c041c01c01855000d40f200d0350301518450b07010b8141410f2442e810320100e044024001b208100b08004043c2440282070300301c0311031008003e910f80c4030560907103490100b4503040d0701c1c85c4118040f441c4c103040c1201d4040c03412244000ca04c41d00304450024106441400c05440048009107002c85a81c2d030041902140b40000716003280d50707080c0025030000d0f00e020b40c6021b081c1c0d0070015030314580b007588000c01c00c0885500c440d200d54050443d030000740d214406c5103a003006a039607102c3c00c00d101c0140141c030b5203841e031040360f0303000305814400c17406c001d10200c7d0910300890140d6401e011880640040d4081e40107103003187e40e0210300401981100342242c0010544160003a00103428420001c41c2c030304254110780b4840c0b841c0e421450f641d142ca16032240325050700300301c0c5080c59400b4010581c04000480518040e0540341a0f0018150511007905c0c02036504103180d109051103500b0078070341c184002d041e00d10 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 824845143 1250 824843893 824843909
    0x4031205030910060e0f06030129060702030102030f22031b02010504080a050f0706050a0203030c1e0a03050901060906060c020904060618061a03010302150a1205040f030807050c0307022413 83
    0x1d000b01d6514072307041c09541101d816025883c12200c2003820010100c041c003505080e48504100034440041c0c84c04e00145201d01201c0107200310600d4110921202c924144c81d6444002102c20380003000a9002440180410400c010404908160344010303680c6100310b801c0034005204500415013000400034120700760412080940359000c1d52410141c81c0743c003881e5065400740e08203000050980d0300e04409400d268035040e807070b041c0c818140d60012040394024184100025210810051400c000b40502002080f40e40c600300a502c0c9000002010405020030081c0700d40740c0400801d0521a06130031260140400100c0700441181030407481d40240104e02c542041d48100c443c6920803e4000d806503070403030760050b00f808020510f5200c00442c5500500807102071111102541c0c41015041c402c40344504e01c01d0303a010342200854180541443e00092440040010400a030107140d00080190b841076039041d1403045c078200700c508180961152080c0c92000ca000007150b0a20a5070714142808121151a = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 824846393 1250 824845143 824845171
    0x2030417040812071b0605071217060f0d0c0603020a030509160b0d0213121104050c180307150206011d0c0714160902030105130204031205030910060e 66
    0x340c00c0c08105409107200c1e0000c0c5800048005504a000c080188116446242289000c08201483c40004205a00180b00007003022a191007044403107622400964190308085a646110603080c0d900300800600f428041d0358130148201003902c0390390f0b228408541c04800c1c0c8400c661a880010000d42080c244800080e0500300410744084005c6509401c802d180450010b44074108400c1c1a40303680f200201d4551710b5420003030306c00b224190f007801d00d002d4407007090024004441814056207011070a240c543c800d5207040140000c441a08048408610010005018180b0030300006070400105030700001039101c06002d000310280d400f20f0400d050300c0a8803100040081802c103014003a08044806200550040001c80c1c0030943c0458454039801c04a0700b11400c2c0c00c2604910000341040760320070341d006500840180300c3e92400ca0000322580c501c0b081c04506107031031512200c40801c24030080c0d000340f100c0040400c5c1c800d5401e010a075181594650184003442e610700c0c00c640402c20072640070141c1499 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 824847643 1250 824846393 824846423
    0x21030b0301060e061e1804031101050f0106080a0506010e150c0709060e090f030306090a2403060c051e07050109020604080f0d14030a050606131d0a090c0905060a030602030109020304 80
    0x85e1840010150001e41200d0824010380609408450041e1055040c0324005451100c0398809000300391183d20f82c542044c02e25450010003824141e4090850b22200d0704100c1049250f0f60300c910303151250b003c1281c1004640070040072205e00c9120740400294180240080800c0074202c90700716404036010b900c4451500e03941c000015840300050b03a81104603410410100d01c00d49061402c181d040080f90b100041e01e40200c400304058076440940095003031000075010803e0104501c54060202c0250802d18a094084901c1c081380004a403440045001e004c0750003414494254040d20f422a1302a01c84c656403901c48110701d585009041d41510a4130400c1542e241261088202464800c05d000e41c05095486206255010304402494207030824401d1010145184080703045030014031843c0107c5c45120390014006100d0440209010340f46400c0880c0d24002415021300a002c450000b035000030b454640c1c0c0000b903003080c01940068625400032001040101040c0c0c002c41c00b440c410f400b06d501c4805 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 824848893 1250 824847643 824847679
    0x15190e1c030903020303180709020d0c09060f020a020904060e030a320f0a0e100f021207020a0e0702120f03150d2d0503071b08030721030b0301060e06 66
    0xd40b9001c000c005800c1400400d02501481d0b5034040072495000c20341d015a0303184d04014080f40c020301801445180c0310340818001c0c64005e45818060300603483c0c04001c051041401079a100304e0003000a025081000026007402039a5002d41130f442e8003071090340e03070355080758100526100c6040404d902055800058450480010030206103500c04510000d003084180c2c80300c42d0726a00140303107003024001c00340e5091440355503680100301d188080740c581582480795024001e14029411003030712440081000210096645c413014007044a07aa20a1220ba507910f0007000c0f400c0528402500000c16004030700c00c0b0840300c6640c095882050243c121b1950b41810a042101c19140c07200c0240002c03c03405005000d1a085907a08895120304808080c4003085540c1c6e20351442d481100306a98940142c3c600382c0680f282e441000c070081090a00541c1011505e4031030031141d102069005c010441c001c3d982031140c070b019800909610900900802c01e090342d03452070b00e011400c21541180705e10008001605054 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 824850143 1250 824848893 824848901
    0x51c020a05070e16120e1203011401050414090414030a020106170c0a050f04200405010206131101030b1c0b0a0605060c03040b07080c0a0501060504051815190e1c03 72
    0x2846000c13070b0380e0151002000a450540920001602d215250100750344550010046031107103281088580380d40f90300d05064003c524180300c410342d0421404000c10030102c00d18004600d0003510803600c0d03007501e44403031509490201341d903002c280b45400042150f580664040d031118084824202c1c070b000300b140310240342c3c0e81c035125103500300c4e54000d007000814005400d1040d48444040e80191001581b40707021500d4045400c03144a02100e01c0c44002010302c05540e0501c1420303041009000c070501038401903515040310000041b4941e04041d5240001c400e1036450b05010340190400102080140f007481c01c000c00901c40840711900c0722810b00c50006a541000c2040318050301138000614102410043c0c481001d03808500e046d10011820300160fa400442072001c44c10003403183d070000617403a1a04c0188015034000401895560b00c059480489852000c5860340030803502c80e02e90010745d5a01208041ca130380c1c0c0314940060316454103801c0c038884000022300d004420240030000c0320032581d148080301070f2 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 824851393 1250 824850143 824850151
    0x207020a0f0803160c0f030507170d05030a0504020d020d0803062e0e0f12160603060308040e1e070f09051e100e061303031e050a0c051c020a05070e 65
    0x1c3d482005000c079107000e9018142003031071260314030240003581e410072020354075047e400580d0182c0200408210307043c0c0c20703140c503004146c580015100941425101030b06a010040c80450811385401c001411540e80e405600c0d03c0c0c6078020301e0000c0c03c0714107041c102e5040d002216641e0003501c15100d0703920700c0c0001003442d81c0f4041100015085100b18428101e64840710202210b030450f001d01045440e650362040d0300741c0c00b282050b00070250700c2e44140f0303400c2050f04503510400a062a1041c01d1010402940031182950028002e03000d00d82c0740e182c040f2015086240e80d1094004202c0e0900c4103d540c440ca00000c0506980c0c1c07580d0f9130907183d8042140780c0203e03c00290074010407420702000c600300050008150b0398941011005001c04001182140d44072000c1c900d45003001050920404d07030080d40d01001c6c0c81115003007046035881c201016000344960040c2409100c5c40080950422400708011f0a80804010100880d202c0526010750f0f9030340301c0354045840b0700803c200800c0003040b16081030300c5 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 824852643 1250 824851393 824851409
    0x101205060108040b1302040b211c050a260405030918090712080d05010803190302130306110405121524220c080907060f0504030813050d0302010207020a0f 68
    0x341e80c0300c1d5140005c50b615001c500301d8010703440d4040c0100580e05c01200c1c01c0d105106000c1c90035030407551411036040c44490007030b031a0b451124055100c03a580e0301c90103070f4410b0b0519040074005900084210031400042c41c840c1e5842c15180401c0004004000c005000366180c02c0d204c1d000401e102c109d4604000500702d5200902d80c2c0050801c000314010303176003651036150041340c00e40d181943d40c00400e81580c40903000041d00764000541a400d1034480d1500520001c2680303811810b1010300c50044410105906c006424a900c0d1a40800ba100c00c1c003088800500008041c45409040100c581e42c41c0c041c044a04c40c020325030321700042d0002e1044036510f8000442001030307507078404030341c0c0c01c2103d165644a6a81c6441c0c803e0784240c0360b036140c01c4c450743c2031014042e11080c40d90302d40303800c8280c0b400795203400800801000941c42c01e010f5411605640649a00c44c64161311510f45411b1640e80450f15400954014080c0035031900340340d0194002d240050007603c144112503118074104021082c50300c22070f0303d = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 824853893 1250 824852643 824852663
    0x71a0709051503070c0f0b010f06080610032a09090507030608100c12020a0e0a080d17060f030d0c06150f1e1517091902010f0e10120506010804 63
    0x1000c601800216031251301420959403451094498040da06035240c01200c0c0d111002c00103204950201d0a484000d0840e4500305840d854280e0100e99141c0b0701e003c4200134076880312682006e00c0240801215051290070700610400400a8001d0070001244640d60800c1e1803c0301042501d442030003100203480200f0000c0038105800700d0000000d1000683e00710030000900a40e030b4004856000400b42890240d8500207404203260400c101550396a010640540c403c10340000c09a4010040021241941c40000455512040030a44003c0c0b07811410750305000e0b804040b0980303a0440214141203001c1c81c410884011506034540d83c503012402502a90f00301008200003074104030003105450390703085c040c040711284e179407212504191600c1c01038404244440d01001000c0910100d4070b42c001c000c20001e0101a130340d1448400303041d4403008041c1c1082118858241014050328403104451400340ca19402a40c505900070004e0400c0a4400d200310704140119885610030041280582e030031840183c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 824855143 1250 824853893 824853919
    0x60f1808030c07060204030c0612092102031209031c090515040219090f0e0102030f0601050903120d15051806130603060912030b09090601052103071a070905 69
    0xc485500010b0150700001d200f08440400074060380007800055115094003020039044c00c801622100c2401301d0b0390b04851410000a0210708800080c0b500d50b0143da0900c42c558404440890a5108a000590400c5004802c0c001c0d0280000001c080c41e40703c44007540c0c5000800c20005080e9034540340040c01d5a80040400e0000e50346803603080340c119200030a0300d0381401a0031a0315046040035404088140d640d01c00c61380440b40e007801044411a80b20f4001c51444c90040c040c1d044400f400360207a8100800841e40c00c0140d2400c03c01c45046201d1286401d071a41c19036031030325000d01100054034180ca52000c0f4001040c0c1050001d09040d032500341c1c02d281055841c00c2c1403100300c09413a60000c8005443e00c000002181e01c6100e5444240c2c0038644031321002d0040301d0040c003554400802c99004603170001c100410602d020174000d040d10f4013160f4140350710b61015144840c0520b03135142c403103e80c000000d00b1804c02416150016030498600400313000c44c0d85d01601a40d03240b0f014442c05030840759502d011 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 824856393 1250 824855143 824855153
    0x60a09021b16081b0d0203010903030603020312071e061811100f05031602100c0305010e09060906040809010302250507140d110a0305010c110111030112030f03110a020a060f18 77
    0x701d50504e40103001242038400c1038000a0079079101c0441600425928007051042d4102840011034401c40703c032030f03507107003600c00c2d03490588950708015072280c803100f1200504c04108081d0000750041c682804009240300450034144001898641824410482e00703180340015401045c0d641140e60a13900d4490869a804205e042032000412901046016030844050480554494a40042110750300000c1640c140603066a001c0c0340a4a03148281d8004c13000c020f0207040028600f68402d82c4a0131541e10342c102980168041d0040c0041e015004422485100034041c00103c00e884041c0a00308945c2019603c3c00c641e503644255a0364150008016200c0c4004079a0343d1209840740540038003540d4460f55240c5695085500303003021500000c1001e010905070030805d01403c1c80200c0038000300b514551410107208014035000b8002803c0c81104540001c07224000d0b0320000c0440c035220444ca0750f840a00000949a901442080345c409160418049000c3d07450b1098400d81c0c07036502c0e40c9900d8481f0540710 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 824857643 1250 824856393 824856433
    0x6070e0f101205090c012006071202160f1109040c060c02012109140303013b09061806060d0212030c0a050102070b010e040f020603060a09021b1608 65
    0x181041c42200c1c42d00d407011040a10802d885450301c50080d00f440c0c0040d00004206140005042c1c1c2e0b10124007065580d803040c0410025041245030030404d401a07076158150000e800380034440d002000c2a0800182400440c0c9510407085100d101c601d40001341207404c10000301001c1c1d4001d89540307280e100620846000d1080c0940250050504803580f54820111460140348032680c0005039881d49603901c10401c0c88240c14000f5a03910016605560401c07110610520340b5000e1502007501402c1d2656110007000c001102e10582040c0301c145902d881140e0590b2220140d039400c1c100f80e600000c582c0b9402d00424500e001d12802015606403c01503000c000c0088100c3c0b80c0380da0b003400100650341440504000c030000551003900056245d42c0941060030301304605a0000e058500788508200c00035000d41c90079060a41d044521580703d40f20013010402150a90f00080b506601c0090324003101e008010020f500003484a044a408100c141980d80501500d44925078850b8400c0000445121441c10 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 824858893 1250 824857643 824857669
    0x40b010303110a0b04230d050f0d06090c0e0f04090c18020c071202090106050901270b0412020a1d0a090501200d0b040615030e070e1806070e0f 63
    0x41152201d0006803920321306050300b610116907404801010008440c1c440003504400300c0020050003802141c944042d0851081c440b050a1010303000032a00341d0131246a1001c0050000441c04004124071020040c3c800030f500702c029485030b002d0f0702d01c1440e140303014050350200c00e40c05a003000081d8a0081c2c040080c0040c880b54241c010b40034084134500c0b4804004650051103012003514041c22280180004000d040c1c00410410400f08031074000e03070740c1000d03036456007140d41a180c840251543c00c4103e01000030790041c28440c400058005400750b80080d80400240c02107401d43c24031642d50942d41d41c1c00012003400d034000e403903000010b003000460785d010344c060601450020681c0c651080904000d00307400c04a82407900c4000c6120015030320780388526441008141c40800030f0605005190360032450300c81400301010b45030b030350800d002c020601c19600100034440907000701342420040f004078040404c86d0440c1da486590000b6581a10540400540001c09001d031042e603c0010284010b0f170a95039 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 824860143 1250 824858893 824858927
    0x6090904060603170a0e06040e010e06130609020a12060312051c0516022e020c0f030301030804180b060904020702060c06071d0909120a180b0a080f040b010303 70
    0x742c0d000002c294244100d003142400e00900326550b668002015103c1c280e41d2010a015900601041c01024203060800d4150780f82c4910804107940c0b1800002c0d460f1220b09405c42d12a4104000000d000d1800d4000e80400ca41580301c0031680b02070301e281c0104a4030584800b400a5116540540d2030a0180004140500c0c84003210140780f0312484020050f200260342c000d50180c009250411025810701c506600015201e646104c0300c0381030b808001c0c07403040c01c982c2000c00c0c5500044d1107140d10010494141d0104900c82540e071290381d04e00f0000c841e50810b01c81c0c207400110002c0c0900040010384078241444030b0080129081010744000d10000b900220000ca030403010800205000c01020080607100782c007507a452140b54070b43c0d103a0340c806d00d0300d1036142d0714080d1040106001060340c3c0461440b0000b1044c280094440180400c200c1d5294215a00407810260741e003404510020740c1030041c613868000d0340754000070b0b40340ea2a600d003209204a0703001d018800500d00520001e0b10074660103030181602 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 824861393 1250 824860143 824860151
    0xd0f030504260d0203091501080102070b0c0c03130305070519060c030e0103060302060d1b11060c0d15030c0305010c090302060738061005031e090a1a091b0609090406 73
    0x51040204a030700c06e031407543c81d640c00308510740c1c01414081c10007030160003101d00030b5042132829511403032a80000303000500d24980110381103000c0c0600b0401e40d290000d042940d10001666414000c1c0c031041e0f1402007034011482e60f041c001c11401c094411004403101c9507500501907005440494121541202c5241055110381000000da904c420250000c080d691400198101002840c1e00c62078005403c07000900015100c04000024003048003940f0000044040350755100b0428040000c08100c070740d000c013021143d000481030241102e044000d50344107200800c40000c000c001a031347c0070580c0c840290301803800c100c0300f40040d140316000b150408184842d51007000d4113003030380114990f042001c8001031200c1000c00521349401c803103e10446025007071451031810702c10a1401003038510f25610003000c100d06c0101d0401d010411440400941109603040880f00c80d41c9107021658081c1d505006510a0b01c80700058140445030148840c80010409440c280380c043c24040010070041003910040c0d91 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 824862643 1250 824861393 824861407
    0x708220b0420031e0319020c030f0c0a051e030328020c06030109090c0f23101725050304060c0905010807030c0507020a12120e0a0512030d0e0d0f03050426 68
    0x446c030310140d0300240d07900030700741c580d03049030a16151183c00001c406455008c94140c0040740c8a07094a4810340720140d0320480c0e20110b100000d40c00200210000e505403000090046400e42c00245513007040080b202c01039403403410102e041b0382d0389107883d200e240c0c01002000100501d10b25580011078040c442d400d1407a1090f070b00c041c9d010301020954030007102e46a05140e05900c02031507098015081c00200c076042d145600e03041008200b4140169030030b08000051012902d01d516950170f1608586056004903070a030890f13003004189400546044a001e401d00c140100c4180c061082c5500383c54041e51141341c15a1500000c802411741d03401040c0500c0410444203000d621002c0d1284090308402d09200038003070081c038042644070121120441040910500a05241d0382c21404008491044425001c60900d00842c0c2d4154450066907864044c0390103001c10001402181c2c030301c00440141c5a47c010100d5400c825803d0301d9080f200208808290701d01e20310b94031000c00640f1030780c00030150020f0030880 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 824863893 1250 824862643 824862667
    0x3060a0209030a0230011505190909060603060b060a0f03020918040606080f0604051b1813030905040c05030a050c0714010203090d09030b0708220b0420031e03 70
    0x800504410340c00c0103414020060171030007180010802c1c24a0000c1210100205000403181c009015151107031100850b04801d0010003150800501900c45003000240201e2820700020041c0740300450702d860503d01c490000b031511805583c000c0002d9111400c00f02d5401008030700035449508a0780d801058440c001c262542c032104e403d03102d00e1140d070b03000651764200b0784501e1502e420700140c41c045501c044d041000154020a00c14403800310041e15441c002503030320020b200700203003c01100700c0134041c2c4100b040c104459810f0810300703402915040807607600c40c002d000a48201c0d6a4100c0412410008980614000c0e441140d000043c1d41c940c60522840c0d0752109041511380c507003420a69004414003080a00500100701050900d08007401d21900d50350782c81810b03400051815052150040c005440a00080f00e400801540b13007128a89031007062416810404050b58262010444441001e04054511083c4176507141d0040c000c006907141c1d40b440c4901190f07012111580760006109070b402101d = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 824865143 1250 824863893 824863909
    0xb010903030c15330e0c1b15040609030e01030b0609060f040b0c0f0f1f020d0b13060801140f06060a03090204050a0c021c0912080c030304030e15070203060a0209030a02 74
    0xd280342402c454007104042115013030041504840d0703910488a090044541c010b901f100c075110a0314003c4080f18990354801742c101300c0c0c0c0b5240c107184c5040040420081100b981d1145200c5407203502ca5040b1100414011800c54145060a9030400010085882945015000b804194804949482c6056101e1351250803503049403640d05281c1e8460390790f0309200d2000f032001800010700b0030010641d258866000c0c4200101114400102c80c1c0d0018104c03803c400160000501c00c140507202c070400c0c603c42450310000345040e1155800a510340811401c041c166400c3c1d4600915412a0206450710784034200421584405840018503540d038103e600140c4850080b00e108070900280000e4007480c1205c060301b029a07800340e90381c400070051819003030240c0082e0904107486207100d00803200144c84c07409181c2442014840446448003004000c200350b0b002c55580d0004178142d66061405650344c40160080c00341510081d4150044000581d40d60815405003405c8070005049414a20407500464210 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 824866393 1250 824865143 824865191
    0x1060b03040c060f0507080c011b02160b0f250b0406020d0b1c17091e030111070b0a02031009141609060c0807020a1d06040b010903030c15 61
    0x1480210801051001180d2028018941d5042000701c43c1940f0744024441c3c0300782d02c030090406001041165a1801c00d504c0300c0c0005148011100541800d05000380d51a03001160003945510b05001c0031841c50030040a030b035024060058140d042078081202854806103410102c0032410032045984003040c03c1001c8540a07070700807000160307213003e690301440030340b035080a440d40038415041c1d85c80c4038906c078207942d4180710f030300503034041c072035080b102010b2000b07200f901d189070340c40801d99194224280d80f0b04503100320032400314004c11055202f80b914a216006280d40500030140940000703050b03d100c0d4005591180090003a5039003561210042001c9596600004c00720303014450400c0a600e409502416a207000d505103880740c580350050003007041481c90002040c080c008590b160440d01c808020b000980f4140c94403081c060310300c1403001d114410489016214905040c00e4261a5004042d10015642c141d0b480410b41002912641135400310548141049951042480c6c2180c4c4648001c84030 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 824867643 1250 824866393 824866409
    0x30209090601091d1b07030206010f080c06030414010b04090b062b061805010903112104050409110a0801060306050105042a0201141503060a0614040e0f0106 69
    0x22022464144060203400410050601c0710b008014006002040b0b40ca40018064561a0601d07a803004074151803c505407603080c2c02000d01080c3c801c2016000306805058a2294083c0368000f5a10304d0302039524180c180700c942d0081010004030300462854010740f41051411800424180b6400020404950024409070390000100040c01003e01d400070210078001c0a00f107941318000d169401105610100742c00c020b01282d41c03075010b00750b04400f0f01110542170f904900204075601090030094910180001201c505002c0e0180e000d284406000094441c0138407080d80d54203080c1090203210040c48644001da4101d080c0038120810f6589680303022010b00b51003c000701d54245185060790980b07104cc0c100605c2a81001134500c120307841e00d0340a503111a2a160032141c003403446402640140100d441001c80c0c80c945004011900c0c0038002c01a01c0444e090f003c032211640c5a0000500311451400341a8200044404285083c81d1580007584074030542000d4840010300c003a40142114400e6100d001 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 824868893 1250 824867643 824867647
    0x10b030604120e120705010c020d0c08011407080c0306040914060903190509030309090601091809020906091003230717010b01050a020304260a0318090603051905011401060302 77
    0x40740d03d510198100349003005641450082d4030079440607031181d015001d418100203001c0345031002e41d43c0c1c0c100801102c1d90011521850580c85007581d901030220005981600050040807507001445a400c0e544110200e0882c01d045445130340400010785102c40094582c010403400090113800181300b031034012800b4000641c1e440800700f06810480340d10041c54024002c0a02420100c1d4801200300e507034841048950b605142c0d10400141e034100301c16006003101c03803524044d4400300080d65000a000600803500080c4a984407000c100707901c602142c070741000e041d41180802c00662140814049200500c003150301e0f02600300b21182c601882907102c051440c0c840320503000208003e2241987c060020310702145402e0b100b01000e90380b841903124490200102100e003c0066075000810040c5000c99010b503a12a07105080041c40c07030300c0d078141490405c1c031846800035005619200d03180440c1ea004014004c880704503881071003442007480080c0d07603654030f2304598203045c0310ac0301c0018042c000c1d07501d00503 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 824870143 1250 824868893 824868923
    0xb030709050a0f0513181202030711090411090c190e1008040b15130c030203060a05040506010c2a0605030907060206011a07060608070f031709060a050a02010b030604 73
    0x40c440c1c550009032503d100d600203001c951100461460084003c1c40041104c200a25184c8640c9644d0040505168441c5901404030766001c001014503500500c13601031426200c0b010400a41015a0b0085c1403c25400a0704420308000e84403550003240041c0090038907165041c0d6100b466041c1c0016000910111340340701d1680703050011064010b00314030b0310b1b520520f416600d89081da18050151000b00c10622600d0302a0799a1040d0254103411144e014040711070b0b0503002502940003503074481d10030700482c180031900f41403512803a44503650582d00d02c001c001d46030700d131650100810110300349094581110605d0b1025011348000041043d50b45890f600d05d400d44541c0c3c01c0c1003490300140c2c00c5402400040059412081d0b84c2e840010b43e45903469681e1440c1d00e401e4000b0b103641e03440003540d80a541c60015050500700c1410045030b004040781f005103068255146020701c40d01104651000c02808a103461901c00c0d406002001074500000602c40040000240707428000c58040710507060340c000745 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 824871393 1250 824870143 824870149
    0xf0608060c0306060921030d02030a0c020a05060a091109010e07110309090f0604021b07060e0a0b041a0c2e0b0d15020d06031101140a1d04060b03070905 67
    0x286521a1900079600c1c110b052810029065104044000744119085056101407041e03413921a6003c003036280c2281c0d900ea00e0100144084d40007110081441072a1070150100c5a0000c00c8000d03800c1d50000c0a0402c03aa02e03442a04010164080c09558407006c1802c02b03603032901caa40340c0d903000c2c02c01c000e043c0f02203141001c0c004010a501a81c000141e40061145503456159000c900e41c110940c00d102d45419652140070500901410f803107610300d200300892541c5600c1001c62600142c3e0f0b45595640c0c4400040c40c2440014a218415840f010300c04020400c144140c10b000e082d1017801c0b0a00303541c980350400816901c0d002203044440000c40801d513440c03103101c044400410780700303005070420300c42c010703007000002e04510407100c015029610105010108803a140c0c1255a1401b050104201041d100e0501d544a003984295041c08548210303094440f4400040585184110681c0da10310300d01003480c4407410110700881401c2e04540c54503404a460f08060010b1482131140b036a420134214540820 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 824872643 1250 824871393 824871403
    0xe070807060c0510091106030f0411030f070521060a05070315140d03020106152105130602160c1e05040c0215040f0c0e01090b03010507050a0c150f0608 67
    0x304005105102030900000303800402c480c00c0d180141300700020034013541d04144103005e00c1c0b6100c507507010800000f000144000710849601460280092000f420b6021040c155039200301c00f0306c4480c942c002d50040109103403000d1000e100c007481012081e40d0012600362185060810f803210384800e41c4134000c010090740d25100d40300d10355403010034650360706103002143c02d07010041c541d03c9401059400780b11400c2c98003d41100e4000c2c290011907170315040082e40021300164001441c9210094a03449402c000c0b4002d0080c140904006030080000c039500340d50b41750095001008402c001c02c00a1550030209030300d490140010000410303101c108244d00c84910702d00000a40055102c0c6250850080080b50300281c02c0c0103000408041920355212410052031f17044842000405046515201107500c1020b0f98640717049540815040c4590b000c008209030176120200c40c2c2c10001401404040c111a03c100d4216001034003809030080020110b0704050140c1c4c0d070f8140079200058903100100100a0204a = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 824873893 1250 824872643 824872649
    0x7150506180406021317030702030c19210503310b160c1a1908011208071e080c0f01060317032502010c0e011e210e070807 54
    0x91400e01c1d1180e25810181d8501010304060302c6994007041244203100c4543c40360000c0d02c01d00d42c2d004c609080ca4651541d03a90b100450403402030007800301025041c1003500c280f9400c1c031645a602c0d20081d080c200182c5055240890881040500d060a000810420300003030041d0b545004551182c11850351441103400000c514034107140030221030810803500d2103801d0742e0040c039030302c001d00c480c4441c5420151070302d01c400d400482c80c8580703080c0c56040305040900104041e500900c01210041110901582c24410034440c442008100f26550070010380c4040003080740f0ae1181103070303101006c1000c929109114082d5000c545400d00001ca00054800030843c450f404d03070300540282300113130443ea120b108850145c940001c0002c000300105038207407054103605c1b807000c1c0e0809410100800340e1400034060b00704030452001140c0e80d5180c000076544150011420307980040c00384410940901c40c11608401c0c0d03403803000701840d113900848100d040140141c3c401c044854004042d81400c10070114100310142d4 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 824875143 1250 824873893 824873899
    0x5060a060206040c2d0b1b0d0f0807050d09050a050609031315030b0d0b0a1a090609070918050405070603020a0210020c100e030703030b01050a020c0f130207150506 72
    0x3108100001313072001c0c22042a18120702595135100181581035203074210750b111056241e00101000b0800708580d202400c40300c4c281105c00d04180051b810b00c2a2908003082d4403800094540d00740d09000c900510302517411105502d4124038100304400803204070f98030480708807010b030007131000e00f0213011080110315041a0701e8000780d403410031807083e00382d0180b805104e003c034000b00c0d003804424803500070340c0f01c82c140450107031840e8154281840c201241c1002160003100180c070301080c5284c1005035011a01a028001d010728403135490b074000f040300740305c401001103080100c3c0d07010101d200c0038206404440314000740001704240c10640390050600640380c0000007050710500056921960008400c10f648005081c016555200f00d502141802c0c11140300441c05410680905100d11000000b425070350300030b0390200a128440c1004458070700c9a505144d0041c0e01040c40001d6074607010708070000d028402485946550710401804040c3c0e0455002601d55940501d512000000c0c00d000c0c06034462412 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 824876393 1250 824875143 824875153
    0x510020306010917010f02030f01060909020f09061c0e1b0906010203071209050a181a131806150302120c09181015080705060405060703030e1f05060a0602 68
    0x680002e00c0e8260038407503507801c1180440d00a548913000c0d17015944070602d0782c009640d2450681c1d5501c0c60308030284114030001e01420360015070410507200341d9024800f882d15075464031915008014842d0810886502c1306a00d03034141584603030302c6201d80408076046001805110352a084c8102d000c142040c426401034030404200007550382c0c040100c80160768072a95002d4104003452003180c20324079035049180c0000c414040499010141e000a014407820a841404074040c100420345040c40300d503002c26007040441000303280c0c0e69010f800418521a005034035100e40c00703403525a081940c00e8040d000d28040405082482903061160701c40280400000040107600e6071000442c0111030001c00c5030005640003828100010743c00c0c45610004d0380d070750034244802d0749502016031044407184141205031082040c0000e080c101007041c0c42c2104d80003000903050400b11b840a9000d0400580d10845500880c1503046240044007444621606004030014680c940350090154000103174010006561203 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 824877643 1250 824876393 824876401
    0x23160f0914130201141e0d1b021c0210020301170607020d0e10030902280f03020d02060306041805010c080f061c021c061413050709090c0308031305100203 68
    0x40d00c100096450390a180c082d100300ca200c0300c1407205000c6d01c982030925040c0030f640051002c1d08440504468560301e101001125080c0c01c400d440c0c031a094880307602581051401d400503450b03555882805155500640f1100c1000b410b2000072030303000340c0041038442100880002d119000700150b96101c10300340010800f2004624000d03160045440c80e2034410610101100d41141c80798000c8240181d01420781000306000019092860101c05a50300100d005140005141345440711481c1c2100c3c1c002c0e0000c00c8040301d5400740034456100500c02500f042d19841d150135000d2200c009554180d000d4800015050752580c0c00a00940c4007408500c4080c9104080c006180d5030040302c50102025199201042c6d06144081851f60640c00c0104400c940d06e01c6900c0103012507508410034100321501d01c2e458235544d02111442051715100d024109070b0007a034040c0050100d59205914182c0241074240341107640b40e0700e07038815034030407507100003601e040b03802d81010000704100d06005c000d0310b00010341c25894 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 824878893 1250 824877643 824877661
    0x3060e01030f0206040b030f06100e0a05060c030c0a0f060507020c15090f03030c03070b0610080c1602030118062d0c110109060516050723160f0914 65
    0x50600001d0840c40b03000e200d2904540c1c036001203500801e49a80029140e01d0000c40364004441e0403a4141d008100d034403060384456110b0001c400d0242002031903080118101424030986030007146600d0310070b12081111851340340b03040016000061183e2000118200c081ca840426070710040c207050155403100c181c104042e034501c2900f418194143e02803c0d00d0307801c0314001a507400c1c1074400c125050300001070600b40c1070b0700210080c1500c50265140340034a131120f5080c404820110706081c00080c400801017210550420010148800b0401040c079030104207400203821105403028200340021010000b404000300350294090840800b441c82c140d4100c40001071034140580c41c008202d40741e03111802041140a40000b0800070500d40081108180602d0700e10020442622408a818110700c860489148503d04591a103a44034284030080703e44c070a9584230721130f100c8a1701505402040c0c184000c1c100c03226034100003807107811840c10b450380c9461005812034120a0300c0680201400381000040c01d = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 824880143 1250 824878893 824878919
    0x2040609050411070f03120e03030402090a090302160e011809020f01030513200a0e071b02060409020a0909150f030f020f0d0501020d1a0f0910090e1c0306 68
    0x60300560340400d9010440d070100d03c0a128110004003501c00502003d414113600c040400e80141d00310808100c0c001421001d1a928002120003d600c0318803840007940140e40c941001900a00c24011202d40b40d10110071032451581c96000310304484038101c01080400c0ca4540c0303c039150255824100700b541c00716004200c00004012185050540f2400854840020309012006454000020030301c01d081007015074200b02c650301c44151061002840c04074001e29060701310b90241c003182c0c95034030f0380d40f07c00c0880c0074842c482008240d0f4840400e010000d03d000c498002000c441c1c0440e61009602c609021300001180c4104000b28000c0b18160014003d405c104403500042e01d0300130f00843e0183e1075510028107942031820300b1580185130044000d041044c1500a401c48500000e4141310b01030141c40d0090204d80185500ca90000492041c14400e050062110f500b043c02d03080f882c81556140c00420301514030860b840003240d8095035411080401d000c4400c0d1002030286001e00c01d00c1c1c0b52141021a04c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 824881393 1250 824880143 824880149
    0xc1209012a02010804050c04090f1406010f1802190c06050106021f110c03040806040515040f060216020a0824090d11010e1032150a05030f0c1302040609 67
    0x11016050105d400d122003004070740381c01c4e07100510078015107409190603188019503540c2141c0007040400300fa007100700d02003085810703103a0050b0110328052410307086008a0b042550a13603413150342045019203005200c031281114400076107641a600545150003011140c050340305a085400411540202c3c4001c86002c0854640601000c28074942c4108421014440c0c0a070f69109413200280001350081c01180d1240f250307008006a90a246109036404007010007107400502c00450603545500103062075028140319040f40407070002d0124036502203207501e422904501321310f501080340c0400c07101108260700c8183c1d00d07454800c507150401d0b042c5190b58960b1102c0c02d40c180000001400d00800d002d40c420b0810340d40328411a4000c420040199000b0320070044610818240c11070704007070b030120303801940f0380001c880d552055403580c400031000019030940b010742e54021500c02c0e00203050380c0c00304400146c08c3c0400010741a40883c61041090f40081a400b40d54440d00500041100981083c40d080072 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 824882643 1250 824881393 824881397
    0xf0a050606060c0f0f0a0507060905100503040f020a171902060414032b030615090e0604021201090203011706040b16030e0d02010603050705041505040b04020c1209012a0201 76
    0x12040740c04000e1342030009a030090300303282c0306600d040d410345940001e000342c070315000b4002d40d6a500c3e110407003221180681e0207620307000240c0688048001c0e120714011365000e4042c4001c0c4035070700c14030b5000907000720260780038000c0402c02a544100c601c5043c4040c03a5107405201c1410308900c2688d01051590041c0d10507120800070068100d032040d2030a00000f101c214640c5144850094140303c000d410018150303413500003d1400c9e03400b042e030503040606607100c61141e4030307040250342c40e015540c42d4440e0300800c0346821035028880c80403401110341d401406041103000140c3c5940c1040c03a440302210914020240c168072900c240400301c1d000c0d5007400c1e00074402c000c110055200a242c141c01509150a90300702d540f04103142d8016050f4194460300551307100e9029200a03903070342d50801040d0384420180044080c55007104014920701503020f0600c46101500160524103820440c6082000c404040c10009500041c054074a42e804904800c1c8110320410030101c1892102c06c1d0920101c0081c0c000381 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 824883893 1250 824882643 824882647
    0x60801090b0f0a06080f101a130507030612030503010306150308340f03090906060f0e041512030806040207030c0809130e0a1704080303060d08040b03180f0a05060606 73
    0x21100c1825002800584824012074401b9003190030b2450b0391340780c00070500956070710700441101ca0307211a00d044082404014240100f9002c15800f85009150140020051590340c0000054618030502c5203207030680292030b101c1d10380d031450400c07400362030742c4081440c080341c100c2006000150500050740d1944690914448070388603c00e50920711511107003005000e40d01e00707030b070100b00700701002840700425403290b41c603060368a9448150b00b0968005004000c003081d51840c4843e0000d10403400148800b40041020400141c940190302507090300703400218410060141a0f41455040a160350708907000f41c50071407601c07440762170007040f08000c08001000d00e100019113086964800c080c0c04001100a4003c000d600d105c0c4030307a66640c40ca11041181c04000402c6800207420040e0150380c2240d480c0e00295145543c0d110070000c000740c02c45000c540307600342404003040c20101c2d4000b841c454240310140e210f003c0d19080d060b5150442d540340000383c0742c2c4203012040c00100046040d03604041c0c1034840c16 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 824885143 1250 824883893 824883901
    0x30f0f050304050406030606031401050c0405150702130b01021209060a140d060f230d08031306020406080402011e0c020405090c1206040b070809031207050d02130801060801090b0f 79
    0x904500ca0750b0f100e40da203c3c0c20b01c90040240401a8880c034100c6c0e11660360400180c100402860071303581d04507046881030406100c1000681023906d5002200c011001c3c503c0d00d403200036400140f0055940e40e5031208580c1d100d200701800e580401400200b044100ca5140c01c207211400040c80318843e41100000308034220006d0014101e045007030360b180d10203c007004c0c0a0207440d0020703000487c04d5841040c498003d004e42c1140e0002000485001820024090070350800300d40e1546d60312540090403522040740303031404c03007400701da0a440507001401c1d0b655200902ca0a081c00010108940317881610000941038440c00c0782543c201c03001d070840035810742e8040b4080c2e44805030b803400e12011100c000d4000c62040a280120000403070005c0c030503441401a0001601c0d0074000b2900640103c2d202512940100039111031052102c40c281c4c1d016019140452401b40d501c0303502c100303a07000482d40b02c45403400e0090a020003082070044001902c80c00e0001c0cc443c070b410761288a404800540040301c655003201c046 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 824886393 1250 824885143 824885153
    0x220518070e0c0a12021b0c0f0604030203060105040e0a0b0a140705040e0f07110d030f0e0c010503010b070609020d030f031a0604090b0303190513141005090d21020c0604030f0f 77
    0x756846051640410400b10050a5919260480b4005888c800c0304445c01c001700c0d0b441c01400703803400d0f65006001001302d41c3c20542800010301295000d11450320070304020000081a2464040c858200d1440102e15521881e0580d4100d420150002042c41020700c028080391001304c030f00f9580550800311008468542010550f8407642d950001e04460013840071704040650150007800390800e180740100b00f80c200000c100d90300c03210074080c40303400103908100402c0b1100d508409003080a000d20000680c0041ca503000039485800500d00310b0100311120500906107805118540ca851041c000c054000342da040d0004000c0d01c030b14020094429610240108103450030030030b40e0380c14400c05841c401c0025080c600502103420004403501000e1151602050418006104105c0340c1c001500700d140c4007144001c19140b5404c80180507401c90300c1c80c41200d0101b00e642c040380c0140013800b0b0048044a400b624000e0034110181a0103000e10b9080000b0400204003a01629403180c10800090444650f403410b = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 824887643 1250 824886393 824886397
    0x5040b0d0321051509010b04030206040e10080604060e1b03060606072a03210806040504062a020106090e0a03082a121302010806220518070e0c0a1202 66
    0x1204a10340b400d010032460203140b030142402c4c1142155102d0243c0e0745d40300b00403001e01c61800003d400810a1008100c0b02d50307100e80031030f003240c52103e00c20380c01500c541686107400003c8400b590380b1500c0700000400c441c001e0020904a000c03130144a600c40b4000e101003680c8400140c0413a0007103600207986018810742c0c1d020140398080070340d4501c03140c807070705100302c814038550380419120700303803040b10400203460940d40001a0b00e00980715440070707584a10401005180003001030302c8031500c0f5061004003040c074041c41e1211914040d8824400d5002e2007009007100d005811075148646084556640326800103001140281c2c0b40c03625081a80e26502c0410724640301819409051540640526031807c000e00584407006c024500d00445a43c3ea0300e50706003190700960301902284406c00407400c0c41c204142c40d4003080c81d0700307001d021240030548500380803200c084035504070070002c021440180c0e0f40709111b03000003415903c2c151011800d01b140d230481c1d544a9910103005020709031400042d1b40e003003501 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 824888893 1250 824887643 824887697
    0x250506161d060307020c041802122e11130603060512120a050408063c04023703050c0609060f0a17011706160c141002040f0f05040b0d03 60
    0x403e00100300e030070003a192303503908448080740300d00544c2ca5403040c01c00c40010046851146521020806040c108180c0c00c2c03442c0703010a05d00c406171070700384400c400c031000c100600c100103111440030036041c035000b401801c481e8503030080b601c02c0030200030b40891034100041359105000030b03018044c1e1b070303440c015010344041c41076a200c04003074022242001886080481200d1403000c962001103121515041403024a580010b500070400384a000420054144801c0300102d105408000c210b050400d580c120a280d601148a20b448103841c0400780100581403220f00c4038000156592410031840000103102401814404c05080202007400c8220728825207241405584c904010041561507090191403604011804075442c0f01b06400300703060b502440201c40402d09182e6a141d4204010350b100f4940d0903840010a54a2041e10b03140c010447d4584014002000150310175803441d031078900c0840244656a00840c441d07454104c040886d40c0300c20300c403454401e5141c81c00c8141580440c3c240f00f00009060 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 824890143 1250 824888893 824888899
    0x60a05090f1c05060604021219140c0406260606030a060308040314063403060510020a0c141302030408120f060406050303130b250506161d060307020c 66
    0x11a11810140000c0e00707481007500400a444c0c80d6643c03d0244010b0f48503002c52002e14800d40400914008032009130541450a10040880c3e07242d00440c41e80f0040f070003a905610010b00c00602040001e401c1003a96a10b020700403c3d000c00780d14914440840c2c003000a0520b0b0060f4000070000300a10803582c0030f00d02850340078021984650f02c03820301804101c02803642041905c608070200c0c0070104c1410b441420022011a510b0840082c0c1d06662448005080e82d00c050685030000820036a03a502c0345100c00303010710390013041d40d1038060820034071a02590384610402c1002615004694a4101d0395503540f80c0c0308c1001590743d8640d403901040610603861300255840525041c40380280041e548540903400894003841003a0b00d80c801c054803880740840003040442011001c102e101d1a440160200e01d21003c0c15500304483c0d0309240078503401c813034012919900701404004109680784110340c1c1d0010140381c201c500c402400c0491004501039149140f04600110014003210710801901c10300b002d000e = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 824891393 1250 824890143 824890159
    0x30c03070203040e0403030506040f091709300d11030703050a210b0a0605040b1603090e04061b0c020f0103090602040f170c03010b09040b19060305031e0405060a05090f 74
    0x5c0d040040c02008161000c9104030b06017109106500020701a81058981041141043c42c0840107940c801e503100784001500101c03040d00c170040742c050411001c20300301000c900200881c10b0858103541800320707843d80c00313040c06202c0102c040045c0300001a6021150f250408507911965150281e41c000c0b880311016140c0380a101c1804612000307038100328030010040d14a02503d07500d038007007552103006d14000c1e224210002e00005a01080c5031441e1949035020782805090345480305403680381d41354119420b40b5071544860b03000c00300e401d140c100c40342c6440301450302d000e0f610610750000b88500004120a0304064440703a4085c14404181e0464000b880000240303088256600000f07404da5944a0610301c0c24014605030003136904040c01a046144801007a55005540d40e6032a81100030303000d05040115215280e40c40714004440c41050040c1d8014001541c03903004501102807124a00410020098024030040100f0740b40c01d0160361044400d070400c1a200e00038200860001d006442da425485144 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 824892643 1250 824891393 824891401
    0x19141203071d01051822050106021608070b0318010b1002010f0501050d0c1724011e08030324041407140c0619020c0105010303032f030c03070203040e 66
    0x1c0055154050301c40d9020005081003039005403403501400d82480601217480c1e42c24030192500c02500c0100f00c103010303840d031412451409420200d510980040e4096400f4000c10420010f80148d102c00030706454008041903410948020482e0001810f4150350311603440700051445400e41007002c4510300a0601c048200c01e01c80028080e00c28802c202c0440b0303281100209142c01e0110015024039005442075001502c0c040880303461020b411014034903405480c4241c4043d030600d43c02d8030b8805004100401e955410506200f504450044071151001c000388401c120210010064940c4201030f0459580602c071060103242c3e41280c55405264403038070385a03189509040705215507018210a54504030501880809402103100b88210a1000ea100300005170782c08403018603004490211440160078000346218140c25070341c0070b80040300483d40b03e2507810429a896840207072100c00d4641003088074901401220080c1c48040d0500320f40c1c90000000418440c000c00450b0010a24114400050701e4 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 824893893 1250 824892643 824892647
    0x9060d0212061801020f070f050a080a2604150c030e0609070e010608011202090a1e0902010f2c010c080d0f05280518070e0603010e1914120307 63
    0x101200c620252880c180e8140c443d80405200b500d44000800801c14903241d8030b502c48811468121070b04a0b414840c42010388000399000e0060060a44940c0700c0d1014030001e0404920094107082c616005e503400c503410803010030340c08003400c4440c81c4000d40c0080d604000e000c04030050589494082020b10480702400001c6600054100c200e60221410809607601d4140880300f0031401e1046104010700760180740c01500d000340819410401c6e0076070010f210080310032115481001c0c41000303411141d4504a03c2d00f90358001015a0380e0700703414a444c0c0508080040303581e0b07200c202c00c1c0c403010381c1001790304050703140e070340600180740440b80c004100c59100c0d002442c01c207003c0c01040740e440c050907040102040d85444100408629840312a064149413a800e20020000f40401003424082003400b8003003031002c15040c403100c2c01400c00d0300315802003854510280f6003502c845e61005002ca41c040c200c603240c8031010440d24100140d201070424500e250908926180c029240d2108010400000c2440138841d = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 824895143 1250 824893893 824893903
    0x12031d0a1a070b0108060f07050f0d0c21110d090606261c08070e130608100605060405091303030905061641120429070e09060d0212 58
    0x140c0b24082c103c0842e138892900c5038580c2801d03251019295146404200840d020380007a010401010b01d007642002e00c1c0000180c182c07441704e50007802090f542d510b040380b00e09011607400801040c00d5000c1c800c070802c10210040b6489013000300c0d05503659400c010410410642c200300300819030309105509140121810380e0003403010b0f000c1c1c0300e05445289000c4c00c0e078511240821544107056155004c40da81c0d00c40342a1500031441290940c0460b804000710420701c274522440d0041c041e590700a250080100e80c20004503201504154071a200912041145903100b50485038040039415580813040c0711403600350041d00f0000c0b0000c107a405001304101400480400c01c80801e41603580b240c41c203c2c6074000904a004442003142401c54001c00c1c12014206001700a00b581c010744c0d4851880d00b402a0f58066115500340d600b150406042084035111725a035261032401200110921000c9081101c405002046181302190203000303140d0000300070799108800600c4c1c2d43c0d00601088c041d201e4030174400351070f0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 824896393 1250 824895143 824895157
    0x1306090f15060207060c02010507020f09040303020d0c08090c04110d05090a060b1905040b030f0703050601060e030712030305130b070c021c1e052a010912031d0a1a 72
    0x1a04400c0c20002d00d0601c0040d0000485005445c1e140e440913143d001140c0d2544011002ea8001c51200c021051680f80c0702043d62050780640d03401612644c120f4004000e851806e41100c0811023110203020000ca00030400d0030f000c20b0100d40c0010031051549130411075000d03c10990b1000751415042180407440440d16815262180c0c1c0208440e040071400c2002b181c004801c443d02074240e0703103818030882c00c0541c003a20160034028116586d01031181d2025141c05400d0300126001c1d00030a0040040f10b0b0400b504c01018071040700030307241c02da00b82050001c00c030b10a0f00018081540f0307100403035400b18078001e0907582950004008241441d10100107030484181d06012401a0241c0b80c02c4404c2c07503c0201202001c9502c00c00d100c0310b0070700c0740d46051001074005200340c917035000d4100c40400380105103481c0c00b69621000c1010160701c41c1440003400360703a025071000b007010340104400c0b00041c1d4030001182456005180503400d05034018041113580105070040121030440103075460300200403001408030 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 824897643 1250 824896393 824896421
    0xc0509090f0c04110313060204171b18041b03060e010c08060103050c090f0414040f05070909150203130203032d0406050304172109010e0c0109051306090f 68
    0xd6811040d041c030007100c0034140f13960591403003480400d0809203065408040c0c940148409800d041e12400c412054401c0302d80c41c1d4050b60301166100d050f13035110421000082c24119003070400c84038842000009400300400080c910034580c51404070340804905820055070308580100301c00440018143d000340a140e8050000c07402040c000342603588240625031150080700907a07810060403c2c00c0c405040c0f0074140c11b82c2d0040d110b40341e440481c100100301a00c03490250131010181041030a00741c0c249151500252101c0d406c0040b850081000c0c8000004041c100c00401641c1e55a817810103880342e40070250003949404009407040c40642c0710000e020740d50400764012640e54040782030f1800148290700c01e10000c02c40900c0000c010420110460b4000703000304e9900f41c42d0001d0680c079460040d4406030003d1340201d03014140f0100179400d220302d40c4800540d20041201144040020f404590349100c1da500c10101042020400b03852504514001c194142d014421185980c4c08400900f0003140004c40d = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 824898893 1250 824897643 824897653
    0x10e0a2d06290609150d090503091018060f0c0c0b0c1615081e0403090e0c12060f0406081f0b01020a0b0103061d030a03050411040c1205040c0509090f 66
    0x24400c1140340c0e41c025001c02c01003005141042150500c200010840080b4032055001c0c02440c10500b07030b50040800861051010355a5000c14004100c100d0040c084941b0400c41c1c444081203142c80c05071103a4084c0c03559400c080b03e070125002000c0381c4140b00d50500a0410180344030004905c401000686144403000003a14220303090b008814032018082d1085110040040160459460083c2e00c802e420002601807040800150040c681040c0015201200061841ea0007000542017120255400c40380c0240b015103441c090304242d0323500e01d0010300307003521814400c040074203286c2d100e9000600502d1404144d61107610f0003414003149078041410a001141008135610b0341d0340c408580310030259888100101142d00316210040106004100f003040c0801204011641d9001003010708003405031940d000c5142c0c81c0c80d01c3d2140c0c1c0b43c40780d4030049006a0900706a103480716008184c00c0000031003010006490b642c0ea081c640b03860001da901030f81c5c1000c042c0b014080607100106032240540311403400c0314 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 824900143 1250 824898893 824898941
    0x30c1803112206060318080708090a0b040e0403020d08090a17090a0f05100807080708150604142803030503100504091b0b030114100e031603020f03010e0a2d06 70
    0x9006c4001500c0010074418041005c0000161400f020304481940588110b83e01c42c1c80b92003148803580140c0000c9110500c41c4100802c040e810490621b101d82c0e146400d402034100189219503e01044000030040b8200742e400181c5190313000d05884e00100018030700000150f50380c06540c00c5002c140580360007000515070a90b00640906c0b603690240903030760798221256458160885507030f54080c0180e008020003621039411966640042c0000d031200d5103440302c4108144041004595896465080c182c1c0395813110854a1078202560f000c9a40604203540d0703d54407585810400351103608019803040c5803480d22000e00141070415004a03e40c0320101800b5502c440020045010900c2040b07151405440050094209546551000c0000c0d041800120210700c001a040c1058500e00d200001701c615004c2003549080300e003140304036030190000c000500c02c01c00d5441c2c8824042c1c2014209082e01454001d5640700529180d82001702845040508541e600d4808050450010051400b00f5010542 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 824901393 1250 824900143 824900171
    0xb0c07110409030e0d05151503010c030e06071407050312010302120105060f100201091203051e0112021c060e0604030314190c0212040b0a030c18031122060603 70
    0xd510f03050b84803940101c0b00d030420070882181401c0708440600444201400302d002d40c0c01040e0061040780c1d07019401d50a180281400c449120000d04201410480e00c0d40940601240158000c2c0591600d0500c01c046000348841ca4851203400411900c400114091032070200d0032180d050303d00c2203403c1c014544104454500b0f840c42500d2a560150341c42c004040d0798030f001c2c05600a10302c01400081182001c545540e40d01c0402c0e44185000b1944890400c400c0180e0b88400b03a4584128088588055050081c548204821140003e01a50f80d800348000304403800003004200e070764021401e02c101d1b41340d00b060070748406055070220f0100342896100c0200311514428544138101c04010501852100707003220014042860800055005010001c81d14020100040c07014266450342992740300d88103032000781169039050306001003000c031690307440e509c00c2d90034450b0080700c0d0080140b04081031503800003001c0128443d00e140d1041084010721080d40001c2e0001c80442c0d0440e1000c100c07402e80702d003030 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 824902643 1250 824901393 824901401
    0xd08130c090e1e06062e120b0d0b0708100b0d02030702070b0316081e06040522050a0b0705040501020303042607061d01020309030702011115010b1c0b06180d0b0c071104 74
    0x1b101c100d10b603032003044003d03600c5180a2504403034880c1c0302191114200300492007840b90414180d404a44c00f508000c078041c0c000c1c13443c0380c0003882c103249641218504011469540612003079a40c01d69000004151410b10030090f500141c000030140a50b0380c1081d640c4a41410541900c00c8003090b003400015071460009400400071100300480500c0715901d60f0304020040200600061006503510858090500400e1840e440d02d8820002081a011603041c500b201c400300030048404c10408100510250360b0100507030341c0241d03100210709414540040c40c0000c16000030341d15204078001190300410f00c041074000700d00d05050418940020150b1400d080e00340e220440d2010801d50003041413500552141d140d4612107441d2106070790301541c4008066000ca5030a0f40080060100801e007100c140e01c42c584a5058807039040701c01c00c80581d6500208109003d23000d04254945100c11034480030b5102e51030200c40e1258002c1080d402850221040c003110b40003140165600e4585017640d01e924241885 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 824903893 1250 824902643 824902699
    0x230606030c1305040311030a090602011802031f06080303240d0210140f0403060e1b0d020126010303020102180f0906090c0d0e0d08130c090e1e0606 65
    0x210304180240d400b0b50300280002501c21002c01c0542c1c5106a8802e030b080c0050503012015030303502c403000c03072034110001c0c00d544042d80300210000180e882d0300700594002407881030a404640784803510041101120000b803110342c0c0a6100c030b02000041100301e41d41e1900c003d880c04082c00f10302427025000000e00c130144154840003034012004409540c480c5010b80c4003104070300303030000e5032510300300389045040030300d4100307a0085072010b444440c0310540100034030900a10365164013104060f02a600c0015040c0809030001a060060820303040c100940e04a402a181140315100110203503501e1500034007d60260070520880389000c0b49241c460703e0001d81c10401c9040041034005103844c0e5104110204d04050100d9007600750811100300c4070802800348500e400484000b524a2245400340503044040c0104240c9100035112214000151800156001d44d00d8242c4000b41d0290724411107894403d01c0444038185103c041c0d41d1056008000440d6403044400303a5040107440000b008045112000d08 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 824905143 1250 824903893 824903899
    0x50a0b07050a0206150f0604031b1e0603020a03020403060c122003190603410a200319050d020c010903030e0a0e24091003030318230606030c 62
    0xc408a40040c218060342220758000038551b078030209030f00340011103035442640121000c465134484809200000c50f006002028414081410510090848400310009010705c40a040d03012440c05c0c840c501c66411b0300c2c051035000000700070300b42103440b0141c208958000021201400c02c1c0d031810002504564440d15070032030100740703400c684801c450b600d0b00e415003030929140181c0da14000000310b500b5207506a071500350401c4040c100401d0304104e10322281e0500764002c81c50300910703624070b0b0200c0c0040ca8106d4250401c2003829047d1111a1604412041102455240c8502c00124a04020644d1702080440c801d00894203c804402410b907141d00e00c2800f00b50100706810310810119016415203901d030b100041610081540360191103000300e10503502020b291800b200422040410707241000640c000031140d100162524600f179180005003400300500700340c0ca5110042e903580300c161410f40c1081d03001002c15a559450021905200500d03039401c452880f40ca008508a802c0110340230501107005 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 824906393 1250 824905143 824905153
    0x3020d151205060c160206031f0b0403110a0b12060409211e0503040b091002190e030105010b09060706020702060d020304120c05061501110f010506241602010c0f050a0b07050a02 78
    0x26400304101030b08010a81d481050310927a02c144140850441003024045154030340381c4540c11410702c5100c0d0300c00d0200d024011012500248640d00c0c0e1001620750041c104040707500f290380c602c404079000d4101028010140008000411904401c410b80d030480180b8507940e100ca40407030150120208460910310b9004071340d007040400d002c1810881034a034410041412607449100d1111024100d0f44000300b00040d40c04080480e1603940d070b01023421004420128001d2005505010310700741c0c103100303029900384541400a01032041018a40580c2c080c00e800500c0c0303603210704401160b83c020b54400c45084408001d44880300b940f10f4016600e110302190090001c028554070044180004614508000d040c058240305000150a01304552405100d40c98004902414104c0910034040348200c0206200c0d01115030030f001c0d21888038162100080c3c0903465448541c0b003400140c401707905620b40904145000e51050090240005502c541d4a1259500340003566076038200702c4030341c0141d0350040016004 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 824907643 1250 824906393 824906437
    0x30a1a0f0d031107060906140a021e07030f0c090b0d030509061803030a0c050705030a0201020a0809010e0d0b160516110616050c150f0a03020d151205060c 68
    0xc810392a6015110f814039228811114801074075054250f4020310000341540814000f450380182e121400710211080d42c0d092441c4000065102c1c942010310110750161403441d428010000c00114000f1604003219821025480c00c211080010500031b40d2720f4075041020305002400c3c19410101c4076500b5690305410000d43c9805c1241540c4580030020494001203075000050fa01407005143c1ca1089860328540d803040340c6402030078a6441e40c4102d102e07401c40c14074080580d0b0040392111085a10041035642c0d014107400503074500c6d101c130f5603d980082e40364007240c08021050704424054151030403400c90401802408a80a102d8081500345180c900307881c68000501b202800500c4000003007a1a0600380c01c03450820803001c03014400c3d40c240c1c1c460000130420307042a80890744540c079603504c40ca01d0300400700b42910b02c0b4429440080101540004c50441c480c805030320900b0f40b0030b800c2c5224482141d981d200c042001c0c140c40b605440c18003490f00450716100b84801129090074102000001000c8 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 824908893 1250 824907643 824907649
    0xc040c0203030420150406020109030221040e1801060308310b070302071e06030b1503160201110f04140405090d030c0512010602060702061003080415050c010908030a1a0f 75
    0x104c90b807011a0444032020a4540d0b91000c00d01400180000364000140c0d6070060400070300d03011407100201c0b0044090422401818045c40c21902075901910301481d241c0c0751116460709450b03c41c1c010348071079460148040b00b0405a08010b0801a00003135041440e040e10451082c4800b0803001d060704c03440e00b00f80040002c12841405081d030030f0701900603280c0c110b60780c0c5500322880a011441211348075040d8000d100b80368051041d03055040d01940c4404100e03502004900d9103100c0902030704860311013008a0750149100350800082c0c040310340ea855403900000c20424040760028010560a04d600785a2001c2a0030309100d01441111104002c100c0700c40b01c0c0d00d05400902c010f101a2040240401028040d4a40125424002d10150303005055034a00380c4002800d0400107400b108940710150010004209240b09035802d03210403c0480d90040a4894281c0e0b061003001100341465003000c864105200a42000c6e501c2000d00c00d200788241ca00c0280d0456038003005c44030060344110905605c1d00703641 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 824910143 1250 824908893 824908943
    0x302070f0510270906050a1d0708090a1208010e0a0c0c0201180b0304050a020a120b150d060e0105010f08070308030c1303080408070510050c190303020d0e0c040c02030304 75
    0x4081d41450320f51450001e0101c860141142c0c0100318001e41310300c5d04001500f8031003009002816900b01955501d48522036410740740c00c01900110420044c800442c00c000c9d41440781000311548903030410300c80d10400002500000007442240600c4101500060700d441e0240500844808075641d480c070700b0066503005451140d0901030085407404444008201180303460003c1d030050340554003c20f6022610310402c2100076454000d1091040c080d41554000340c0c10440c00390704410004141d90b6940c0b171000100c1d401501c203085c0541402d003040d00c0d040842c0e00641c01181641c1218118840840d290310649a0b1160f507440003c103d5501000024a02d00444e40600004a880c5102138469503694841048035040b68200c01c0c03460300305031001c203c149000d80c007040b144035050131302904242c0400c00003038640481a076041e4405d62071500400800d8820b504462455903940400c004c0080741d031111307941e0f800c513051020b03020758540140c1241c1c050001043c0c9114a511a80807065805400e039401030213 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 824911393 1250 824910143 824910167
    0x605130911040908040f050d0b0a0915110d0501050603060d150902030d0210050a1e0203040203120409141008031b0102300f10060509030f011401030302070f0510 71
    0x454500440c1c03065507840c080d440400340580c41094881c0c0c181141e04504400030791082d80309201258807400003403c1c8000300342d030040136080002540007541c1000104600c00c1c16050460700d14046101402071032000c042c00c401010a001009030340e884005001280c4010b54800350b01080310464900026403461000d04401060070000c03501d42065800300345000c0810450b0781c0560080d441142e10170480d84601940010741d0700b0240b14450028822603407c024452000e01816000000a002c2d91401c200608150281084076552559180341c01c0000306891450043d81201d0080800c04000500e000384040e030341d0f108080e602c1c0410102c03800000b2951010140b2055409000312070340c2d6405500c0c5d6420642e00c14071041100d4060f06135020400000608044041090106100d40f5600044a60040e03e800f0b080c469502c410000000c1e107082081c640f600129030901460400040e41220014100c9204e43c00303d6030803585a00500b100c0040034002c5640041c0d904000344609885400c1080070 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 824912643 1250 824911393 824911403
    0xc091b1d01020f060a020316051806031302090114030c030114160c05120405040b0d12030c27051c1106070204060803120105011806121104080d0f030501060306051309 73
    0x30910b2803003481030404e1412503a03242e1080d40401002010340100d0100d000e514090303e066490704020104280214000d00d05c55809094040000703920209584220000f640d00100880081c1d80d4582181240d4031460039142d0003401180840500703400c05015402100e00b035902005030301d039100c2640720250140e2100841c00c00c4801c40201010840504c4401d100000101039141d880b8109000d220030341d805401c000b8001d06030a800c030707004208240b800e4918001c4510300071600e801640e104030b070b40b030302c00c003110f02d07045451015894000d801303000c015401c952054400120f0400c3c103001160320070848200c0034050403c4510740c040c56260280040244510040001441545825002e8a16007040710f000481c42c0589005000c1581c215a0314080109180740c0114010b003080c0d001441000421202080152642c40708185480b000f0140c130302a00121040741e400c094480c03c010400741180001d000803916000c00402c1140c840d01a40d4280c030340240c00064000d0703200d002c420081000e440c055070 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 824913893 1250 824912643 824912653
    0x18140907020a0b0406020307030506090601170903130b070b100b04030326070807080a0c02100b04090210020601141009050105160c06170a0507020c060c0a0c030c091b1d0102 76
    0xb0310030f8500c0c0d80964052403005880b458600809022141c0103003c0a220302018400c1041a1782e002d04030342d010440034103444042c2d80310940054914007400250200740c496203113011880c44020780c05880310718040c610005091326111064a1000107a001d40c0d2940e0b6010002400032a0083e4600c040f0030300307074070b0740c691111032035100800c00c0e2907050b00c2c000000f4510701c05000c05980d01000580d0000c1c1440400c100d01a518080071b03544002e40608220b1003510f0700013040c425a1694041000d42c0d030041c0901181f140e014a0003501e542090140d1050890300b20001d0300c1505000004800c240101d494881d01c60341040b005541913000181000d581103400a51000001c42075500c140c0145041e840303110b41244403d10007004190000c20801e8001d20b07100c100300d04030b5400108020b001c0c800303881242c0ea1700c3d0001c0c2810b04050400b0000342c61a20344040001c100450304944d242101e81d411000c1043c060049405184022000c10301000280d06180d0744118145000c030b40ac9184005004a0b9 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 824915143 1250 824913893 824913913
    0x308130b0412030201050612060112020f06070506060a09060f05040513060e07080f16260d180509060a0323060430090605070c05040207050a031814090702 68
    0x5031866001c2c0e005496101002d2680804241d02402400c0d00700004a40c418040b4040c2d4141607500c800500c107600702c081c604c110342d4055442e40383d180000b00c000981125503d82460030030036580c880564244d0b000b00085440050030351158032520f425541c1c50302080080502c0d100c100000340102500101c200c1101c100103400080c60340c815040105150000703041154a02244030b402e100204007101c2d0141c000d1102d50a810100c0012041594a00030b289030a04010103060b004050021464001034070541c1c81030403101c0d400c07107000354041c07140c420b000d01d62035140c2c0284a0b1688003034810b10f800014100003800028000d01d0000707100d102c4000b100104c0a00030f01e260346050002d03282500c21071803080c483c8000202500d800099404940d40c50306184024100080c60050148200020440081000e004010101078040d0082000030029900d5000f9414090f0301c4003c4622700700d01240710440d4055900e4203980440045070034105c05452540c003850148008410014502411130003803c0040c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 824916393 1250 824915143 824915159
    0x7050a030b010509041802150909040807140f070e010906031a060102010f061d060301050c04151e05030601020d0f021908070602220e0c220b030109020d05060901030c030813 76
    0x200c00d021b552000038610191a0060100c2d091030354041d4001488200403221280e100e429500f0f0708154404070741580c4103c28100214240c1c1d5003648000720b406122200078204800180710f801740c2d0130394001c103e00303640d96801c40002c0b55181e10000301404007a1390850a20300002410952250b81070002041c0380710b90032204412a10350750050820801d1004600d111036503078099a650010081d0000c00490801944c0300215000f503100d06902110b000c0d0308501c10303a03c101c2e0807105c5c2c030150413484032718204a144046d0041d00100c64050051180f90b29060303401f441100040f81c90f10194028100399030140c007005941c005200d0742507800138003c106003000a080d80c4010316600586240d40c00b54030249983c0d034564604a43c2c0201d90200505061216000310b45045440041400c0d40c114501440c2e11080301007005240d0201101d41c01c08000003d686600d500203120300640560100400e60302c103410071034120020f02001c1e100074004001400001c20300402040c41790381c00c0c44140d0301c0d03a80d0360348a = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 824917643 1250 824916393 824916401
    0x30e090106180b0c0c06030a0209030d0c0b1501080705090a0f090c1803030f0804140727090c2c270a0230161d07050a030b01050904 58
    0x400c200040c0356500707070401020390350b0301d501c041d20100301814070b06104510401c1d5220143c90040388110000004105052256411100c0326800a420b843c038400e031414000d018107445140076500241408001007003c00b05101014084405840740700c0c803500c030140b048903541c00c10325105420000c2d449010035003054003514000103060b1100003243c0d0381e0141c0307802400760f04c8200c00d40203180c400110a20002e504640900a00e040b2031411144a5656080081101c0401240154140666600442c0c61020320244654030600448898941000340c050389046a040742406003034084400310038080701e1055000005890b0324054420503236408001c00c200140340941e42503029590588450b84062501c1005502040454001d00340903903194001c5504030110a044481401102c0d030104000d16109140d46c0d135500c0301034211590102981c4101384610b0881c000c18000710b90384c00710070008484034200305201c2c00b11b50340c0d012704201040005501400c421030b05981405418025541d0544403072003 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 824918893 1250 824917643 824917649
    0xb0f070e09131a090613111909050903070b06100e030f060402031018060c051303030e0f041b03092103090314090d020d170f13080c010c0f030e0901 65
    0x8080c0340c1514051404030030b454180107668203c1e1031060200070380782c400031500c95405605040b00d40208280e62500f00750004140a0981d070000111600d801c2c00111180000e00b82d9203c2441000303241c880d0070740b555590103180e40003004442d039880011003c1c28500d02082c0980400d00b0503a40b4014044002810100524130320a0f10b0f034030003410041940303020064510184002c4504010707401c0016404e000c80300207410050a9280c41c0c4600100441c459021100082d0210381d910500e19100d1800030941504405201d2048002180d01a0765242c41d03c1982102c1b00c0380c120302211901180c10541c040c1011441c1611018031041d0b1002c1c400c14101000c021592070b56400003101d11042c40d0281001549007644400c1c0401805803030182c1e1100360261058980455a041803020742d490146150011180c80c4160048081143c4400c01e0340031b000ba1840c0c8084840c12080380f80c98840080e561a45d00c1002030026803100d800c2000300701d2580e207808503e40a403030705030980600d0002050403120f013a4 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 824920143 1250 824918893 824918911
    0x9150703022407090b09031c0203070606140109030213020c0a081b010b0a170705031b1201020307140a0e04150518040b16020304080a0b06010311070b0f070e09 70
    0x2c40c0e55204881502d0701000000c038903a10004142c14242c000030010103560091075114440010718a0700e42d80c081000d074001503403011f030030b905070844200000d440b81c002c0034048800e82d007441001701e401c2110419041c2c0703d85042e52031083c032030b1464080100c8510403840c042855a800c224220801000740511404140103610716555041101f000045840c0201904181a40340a403c0582030740c80113081002ca50801481c201e0619400380b03114286582903111340e81c1840b40b600d44800c000101401d5480d2482c00b01c400000c0051035201e91420303403108840c0440060018440b1215410507030028149030306c0d251a0a100c58600fa5000c50101c411320b00301c2080070b94003c4010411850004005625502621601e09190800c4d982e5242c503e18064032111030000072440b9401520f00c2041520001c004c5802100c68240c5203040c5016208010b03148140007c0c20814020f6144205104a42d000c5a00c13081c02d036550781d00d0031411404588064030b942d04000f240020041c113940d0b1300d005280106a08 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 824921393 1250 824920143 824920153
    0x717010902040617160311040e130302121303031d0306190b060414040b0103150e041b0803121504140108060f07091208070609050c0406080705150915070302 69
    0x858009810b1a6070103500c2064030344da8004124010140e074100c1c1042080b103040114080443c1c00a40c003241c0280d41007054503045074000c212044000c01482c0f08881d0194007902c070000880c0b464146035100310070103a4402d0600560410003c2d100704040310141c20910f0f1040c0c04081600d000a09141c020b559401c1c21601101202c1c034440c030144111805181c044031914903192a10101e86400100520140e104645e038030390030f04003070b400b0360451404c0703204421b00000803a0701d5a01c460049a0252030580b850f0310340102c000c080d0048007641000303840910b80114204160030007801103000c8000c14508001c001c0c0803800045490700d01491410491304070001c50030358140b101e07161514030b005090701c00d500602014040b10b65041035041003501e5480e8040da030110f0039403d281d6014807030050300400c818500f40840d014003202040703200903900101c4040c44495036412800e681c94505005240c5d021160310b810301180810100207014403d0701410600c00401402652107098108041c00ea02580107 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 824922643 1250 824921393 824921399
    0x109151709030714031c09020a050405010b180103050709030609150c030c110606010813060207291003020a14011e0c1b0f170f1e070b21071701090204 66
    0x4c803100b14a24509500114200080200761000118000c0c030301c0e04003641d42c1c41945040d0340f81d22000e03501a280150060282c1d50b03440d113503100307035500411903a81d030308485288100d01988203000c1d13140125402e5842c035007800d0564551100800703030040d045507030f1103007001000d4051025000713a1007400580e4900041407884010041c1c10580c07683c0340001103420038410020f80f42c5e040400140c10601c2e0800001440c02640b600070000d10070140090b000d0881c0415074241558409500c144801119407000041e4481184403200e4582d00c2c00029400304c070903a4280300c0240014507400b00c15005150418070103400068003540c030040c80300c40740c000411000911061205d8043c01081620b00200c655880038500b00d1001681d4030640034162407407030701715080700c460001000646c0d01013807610299001c01911890750348940b00000d80c2942207015800d000508841e03080c0503265200f1480d03400e002d0522681e038044a0f030401c01031011040c00b160207400c1da1070041d28144140a40081100141d5030f0b07003 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 824923893 1250 824922643 824922653
    0xe0d0b01140a060203090a140342090a0b1308040e2a0436050f091216230f07090c0e0409060204080d091a040501091517090307 56
    0x2d202d4200505560080054109076155036000710304507034484443c903010910040c002410212060f000d500c0d021800e00b07420020341000c405103501001c1e0603800075220702c0c89401c1c2c0d03034420104030780034030071604002500c0d000315420980c019442194550706123152183c1d5500c120711500650000c09c001e418000030018103c1070503034003811302c0707048502c544081d5281d0001000c240c80395004100b4190302851291044900c81340e500c0e5035803460000740030165080ca001440c0100740440303400e4a000e02c14400b00da440e140200c2c005c1c204001580e5024a090f0b121a19226060740c07803503007280c50b80c51240303005414003902010300910621300009004012416400382e4540300068000302556803610851010860300f08840c03440b02e02c0142c5010401004a082030402801203074000e40c0180600039000c0005540710811a043d03e03029900d00b860300300c80019103401e0303000e607000d59800b01d803c1310b405001c4940c0c030100003000001603141c1040700001698905100490540d4803a40d41d5001052810400c4 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 824925143 1250 824923893 824923909
    0x110705060907050108160f17040f0615060e040e070509091c050901120f09060c0306060318020d0206030903070c090e0d11030406110a050d0203120a0203040309060e0d0b0114 76
    0x20200f40385c8903460b41016030300011508444042d0000340300a075818014100c1c05400c20f00010000c40000c0c0b0b1030361030075040c091a08088170034111011031400f9071107140540c1546081e025966140d403452040710103501403100603d00c61034155102d00c00c58030005034603074480c0841c600c200e54610240c01d031007882d40c00c4503e00d00b00180b00b2000b4030a0601c071500d02079910107501803800c2150311004c5000d5a1000080e0020f014a83d809020281071030b005074492a0981c0050080746d03056a801c001c1c01000a600d501103848450340254400080c040444c0036240c4417029582180010b030a991401095075504038007900c844e4003213440203440d02203a1a4030081800300700401c4001d82002168071004000d00e0751640700e14040c1c1001c2c410300502504114004000703214030294840212901c810b90600080e5032600031300742001d98003207900005016650a0b0090382d02417a419182e08507507504040c026114a1040605e841d00943c1012038400030842c0e9010b036600a0440c0810502e68042c00710500402d0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 824926393 1250 824925143 824925149
    0x130905060609060d14040507140405090c0906150309010605010305070c020a092c030d0e0a08030f04062306010f02030c0616090b0309010b0a050f010203071401110705060907 76
    0x414504000c020381900e41c07404440c0001c000b00d603920394800940891030001c0080e030201e031214445440800c010400300017145025940340c0303d40b8907820030a0300200400c2c0e0b1012910503006402c401080030980c00c04241031600824000c0c443c03007c0b04002030f01014540c01c05c075011030f00c5039101c0000700155601480707200c0c0c000c5114501007001000303d80209010300c09603c00e048420303030360300c104c610201d01c1d801c0740c0e030007452100030b10341c3c411000c0040b540e59035000080c0c540c031020b20308500c56040840c0081c0b240c1c84950312070803e030b0a590751a41d490b18400c900400646503652110041d80640c0310039201c20041c10608246682542400c4000501c500010b0700d140003554030810101e070100c5400100c3c268000a41540e0b580e2018490070308880c95011a170069403401c1d0007000340107c1c08010f4000c0f004440701a03421040941e9100104190454040340003400b5070810803288010858100b50320320321040381d0001041d514515036007122103030310410040d0b510b80c0110b03007800b0840b48180a50802 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 824927643 1250 824926393 824926409
    0x7090c02031c06090b011b0209060f100903050d09030218090307080c0102070b10050607081c05070819020a050412060b0a1805162016180e0f07180e1213 67
    0x1c80381c91000b501f140001040040c1c452543c880000c0c990341d507022822032441d04040c1100c000d0210031640030307000300c52500080310307240a40d241248020b481056050100e0740c000f0009088104030540ca81e41d071400203003624403a8001041100c011035058401090600e4050780010b9032500e1038289404c6516010701142c07401c41c80c0d11820401f0350380350780030f8a0881d5004078441d82c0d203458400316641601107a2607445c04039810b02003000300f556040540340c0d21900322022004841080b5100001c12440340c0c4040001189041c4000c0c03007080310341885010114410800001c01c14415000500f21000c560b200c003c50b00030030b40c10941d02d4101406481d1300200788501c80014000140406401d44800b2503520503000d103e40e01c00784101d0320130030401070b80301c00c00c40b011a002522080c01e4140a009541030303800e02c900308240c80c001c1080005400d84400400f001400d2014240404262012000000303c150306889032285415001e05011000304200419021a07568032020580600520b0551040007 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 824928893 1250 824927643 824927657
    0xc050606010e01140d180c0302100c020604061b051e1614280f05150c0a030516080d05090c0a0b09010503040c0909120e03010e07090c02031c06090b01 66
    0x7480f82d070000c0000e141c0030001d4a42a0725040852600c20060070040c20211002c104400c0010034842110041e0301500d00039a01c4c0360400c01c0320781c016164200d64807402500400c041004000d114801c40100c13850940c18580002230340d803152251460001800300511041c0f520b03481d8007901c03d504028022000a42c8040307502031918108400c01390120002c1c006000364900a00b41e40160003803550304008191145400141c0d40d160f80c600c3c001200c0d1401340c0c074002e240c613942e4401e0340c154800a0342c0c01030188400400301030131140d4048610b034008903849408481a1100c560008001078013503c013080ba0010001a5032510030078051824118041060041b0031000e81031007051800d000f1200f0800080c03c0c4227550b40c07124a40103000c2151580280ba10314a480200d408208842200c480c030b04403035039500301d40e0013046c800b0142200c248900060b02031f444024108010302c0c241d000019030b03100c00d005403402e01407111080703c03581c44201400402555102002d000d05e03481c900c10b20640d08803e2030801 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 824930143 1250 824928893 824928917
    0x207060503010e0c040b071101021002030105060306010f0e04060e041505091c09050a0801020912030f0d09050106031208010306270f0c032405060603090d0804030e0a060c05060601 79
    0x140c024070042c007441c3d600c844000c00051aa600c0f03182120020303c0352011141d60f03180c05040a00b90701c0d410301c40260040c050f01e020481c1a13115030094a0588030001d01e140c1c42c40c0c55407001500c08269046111050144003030003030505590714480d4034001c240c03044816205240c1843c01580e0146200b03460b044c0c0606c1c1000f1301822250004a0602c0400c002c1c916044030284504141d543c4c1e400c5078807240c1c4c031594981000c030b031850041d00540380e46402074507219a94000e41880980324050611000100001880f810f0301740c0200c2d0b009942c0c040c0c080c100010b03660340c6030740b91124561828600d030070106034028010020050341c2d02c504840c10500c61025607080410100b86650051016005811225401c0781032040c4000b400311003000b591701c800c8070020080c080c0403a521134581003000c2d00b8143d2600d4006086410a802140e10824040700900440d4646910948007507901500560410141d00d1003000f658580d403c4c0c51018040d151203142c040324407481c20701c0c60302d10018003003810804120001 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 824931393 1250 824930143 824930147
    0x1c020109080a0f30030b030105060a06120908040e010611060c1801140d05180d020708120f120c19030b090613020909010b09041104030c210803071d01020706 69
    0x60b480703590301140410b00880b0b040000705407084c09604600420840408000d425605680032140c0b500c0150000e01c1642d0343c410400c900ca104500c220302c00308100d442032015503881c5900899144c1d1064140741d080940b2420700c050950030907048040442c08001c014001c1180400c200c80e400340303640a000e454002d00900702407902511010b01410f03c21040c919410039603030394040d81e0b45691840002c111300d00e000e01c01000a01403a030f1841d03240f03010321050924002e10200b110b4007a1600c0200500701840f48c070540c040142e1092141000c40d0405110b607030030800340a42c1d074900500c081541c079038684c2103040c81081d081c0310400c0e0540a1501d000400741c990740b11039642c40d074000800c07510b4000e50070001150601910440c0351460740004200c2c000305a0b0301804001c0c0142c00c009840810180400001104207407049000140c91860742c003204204030740c08003400d520a13000011070001032a40b140d48400141c1c02c06e447c145d0108005008a060020350394814034000e0300248020800079141c1480 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 824932643 1250 824931393 824931413
    0x1b121203050606043602070c0f0b0c0615010207050d060501050112020c0a2301090b0a0c08070203040b0a230d0c091d2e0e0a0c0e060306040b1c020109080a 68
    0x49000441740811003d00c02d510000c1040610035840324003550f40e10341070f14210820120a00800101e800c00f6a0007013011a4803109460078003140800400054554503c01d8500e41c03081c5007020b0440c4100c030008030b065200ca10300c41408034412400840d032075060900142400d81901c226800c5a8070500130702415000015150350101d41001c9903800e203c498040c0503072102200d40a01c2d411350b0800c3c00c50020440c600e1129031055800b00320410901c0490308044412440c1a180c0d000107030b0007030005006c000c0e1000d00420101c041c40c01d00a114081c108011500014030b01c044c5003e00e440405c1c9007030490818010400c5011480c070b003032082e06003400c0c14540582180c9400c1d60094403080001140d14828a440b00580d00c158003010014002011305c42230200d585001e407101141d0003c02280d140003050142da0150812074994480a0030741e0024445560001420150320a031181001a05a19070261040c0d80d040207034440011010320340009007000c0c17000d42c08494140c1c080001c9001161000c15 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 824933893 1250 824932643 824932679
    0x16210314041113020307021b060408060105130204030c0b04171c1413260d020a02010305091608010b0a211103030408010c02010204150203161b12120305060604 70
    0xc9819458203003900892203035160f8204a0030301c14800410311030813540000744001d00d0b5804854045d554160302081c020395010b50301c581c50065001c44010700c00340c03070304e100810481317201080010f044c10b9598a44010000700d95000309040d110014050040220784410f90728440301080c01403640c000724181e182000500c11100c04200224200380841608665049070210324026a07514007090302c0303561101003900d000d0380200c80d06002c41c240c41c245030740200d0b07481402c03030b9540c018001c07141241e00154090900109032280718001c201d9030541064100d0745070350203003074100e00000303641d89007509220702214150800800b000c07a502c40e121568a031407002c0c01020354080020603180c1100b0f00807d103036002b039030040e00c0e6950030308081a07101c5c1d13815400343c81103a00701d004000503203203113104c180e03103d12440440010b11581030202c600494600d41041c00b455101102c112074156032611240602c002201045802c107800d40712800070f01c1e525000e5150403030000c5440b10304d81840c1081c0300051107003060b = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 824935143 1250 824933893 824933903
    0x130c08060f06040f0b031203012d06030207110409030207080f0708100e012304050105010504020f191803030c0c081212060f0d060e06070e01020a11061621031404 71
    0x1003c1016041c0d130b2030b0004e11301d2400c050110341905440c11301912a540013405030724140c1ca17495243e0610100e45002d039284c0c1e50b2890040e21001401c200040b4041d43c410401992003044131040390b1792071340b035501c20b025880e03010340e010303145241c2402d850341d08240464991700d446a0207200140040c0c0c401045c802c078026040349000580180c0c5010803405400c00b9038250b20f0189890b440c03911100340c0740b849a17102d0362158000300650f03070b00c035801c02c0124050401d05400c0d1072008e0010100c41000350400300101e04060070310703104a0142500c0701e002089190001c0f40050808400c006c1000401a120005002c000c805071101903081c0e11020b825004080030b200d110b0018601054090300c0f12040c16805c0d91300503200701105001401c0c103402030039014003000041e100d441c00080c00340c3e01c52100b003608044164040d1000d8041501c50060080900000e194050001c0000180309145040c0602c0128410080701c043c2d0360312104a1099050082c41e468245400c4c80d600c02e907290410041d855100d680070b = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 824936393 1250 824935143 824935151
    0x7060f0c05071d01031103060f010b0306030f100e070e06010212031f0f0608060415050d05030d1d19050a0b090c10031a0d12030221130c08060f0604 65
    0x10303041c80c51901d000703a40400e084656038800080304004002100381628041d043c1b07000e02c41144424155542c40c119403044650700080014071011104400840e000740b80241201c1da0400c1030b0359040d0901040911406205550340e66000360103505101c0c1c800100071884840d009880c1040001c3e40395030034030407501e420a00000015803403550340080022212686005280c07456141e8000800000c103d0290b100441d002d20b00180c458680381c0101c17003608400030740c0d54405914040a105a200c0c50201c112a01e0005100d9001e801205118000c0b50f0f0341c44160503210810b030042c1603800d12400c4c1022008103000c0503607503404100000340c00740c4090383c40791000c05150b0f101c41c0c145050594102086900100d4240c16524841c3d058002070003400d001078140002400d03010422005506d416001440d41901d01e1181e45010b020398090a40940c8100300e41b00e0700c1c1070300001c2c08403890086074100c105900d040284018170544052120240444600920043c24480c500a02d0280b00801c064840c03611 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 824937643 1250 824936393 824936417
    0x4051203070203071712012133020d06061112160b100801061514070503120405210c0307020909030d140a0b0301020901050a0c080f030703050403020f07060f 69
    0x801c03c12107011a8102200c1074443e032890300310300e5860780007581d00c0358420205000841c48158100480c0c2e06004503800070281024284e031001103c442245800341000303801c5220740041013243e030a00c1c04107001c4040050307480040e2010b050840d0300c00d410600802643c8542c0c81080fa0380019118505110740d00b003292a0710300c0202656184a01340002004071410380e050219030403050010b10180c030201c0e4024060b0315100e40a01b102c0144248403403000840750114842800102c20080246900034000da1b46001500c1d008080d1400c01a68225110392110b0711b41c0301d0060807420f10600541040c1c088503e0010440e003c0f599900072940d01920a220b03000120701528001c200301c4180859080c03042c00440c803540000400300004079084100a404d0a124030020318041c42107074580c160585070f0b5414170915030801c42d1051f01703600085842c1001040148130b00904030014620a0109070780225039490b00e8600242400b01c200c07031000c0e4a1340000405c6c000c05400003202503843c80c0c107103895400ca0203 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 824938893 1250 824937643 824937647
    0x30906140d0f05040b0a0c05391b06040612020c0a051b0f0a1a0310050a0b0304020f0109080c010e190f0f23040902040213090618050405120307 63
    0x840c1d1941031020714503041c0040450308441e044180f00340d004600402d22039960703600c0c11041d04c030a144503400041013002041c0e05031790720313030218481880d08030030003117048104005948152050510140c080d0340130a20148042c0160032042032401c8040d128141060b15143d00500400c45a40e19148011b4000c20f01c5d0001400030000301d907941e5000b004840c030140d070081c032840003260460306040c05480c1c50241c4441d50f0070a0f40b6000105c0324503810a01054003121801c0b07440740c001408201d501003000c1000101543d401019201a049400b0035603560304052041110241442000e603040c0190382000b044030b03000105600c02c1c401800e0801900c0d0495410001e03030b1040740b2481c900c0c0000341e40703d40460280c5003420103400366030140c100303068202d44901c40006840c0a45024101c1c82040100d028403501b055001081514806807025003044602d800f4215000940e40001e141c4941c0c48070108000d810742080055000306405c002c00c15810321383c0b2142d49902414030f500c0c51406000010506881c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 824940143 1250 824938893 824938897
    0x10230a030e0d1e051207080601090b0a0210050a09110603060103181202010507080f1f03020d1b1a030112080c100f0b0a12021207081902030106080a03090614 69
    0x6480c0320940d0304031000001c0250200d51202485000080c03d40c81040c0603030b00400c212043d0b08941c0c0d0402c02c0a90340c1300c20480e00c0d00b100410050405caa046400608551117001410342c44c0344907000380c00c4525900d150030b030172944010000f640050400002ca4041080b05044103003803003003502c03100e0717aa035601c0c1e00582c040d080000e241521241c81251210902c1a1302e04401e240703010a600900c070507143c5103c02c981e0410305507064a21190090041029080000e05840141a03c0307807401c000301e641d94000402010700408142e4004c0c1f0400c44a0000c6074158002401521039011620340030548480b00c95801d02050065031030a0f039074000e0301403d01071030b44166408022004100e070405502c10340b00c040640130124100c2401d50404251450507c3e054440200352800a041c0b0b1051540719003c00551300d01201c407040d40c7d40074055011601d070030b003448004804c45040d0901c005012051040c142100c000b54480c80da913070880d0f107070315000079400100c000c1100c6481c600910728880340c10b22500c0318 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 824941393 1250 824940143 824940161
    0x50703020606011d090c040f0b0405032e0b0a09050a0506041103010803071e081b070509060d0b1801063b070507080f04032003060402100c0503040305160510230a03 72
    0x122000710000a0407081c4c09c0040040c1c0d041682a81c66110444040203540036002000d2913150309150814100c6038a244d11100d180303c8028600140380e540c485850b0110f0314147c03903880081e83c850782000800d0605004280210480180712403070341d89018140794a07030084c0745000b00428034114601c01c000c10340c0c100b000601c640144a0a0360b0f84801000100381c203440851501040c000c08000141c01d05c8c2540e43d051003100041d010500101465540d142c00510041c18502c401c40c07100f40701c110202c001d00c01c00740580281010490f80c2c51890307120b0107a171006c80c25038049814460340c4249a054141c0d401c00c6d000740041c20055201c860600e0803291600800480c0d22806101280000a10205880201d030f411403d0210503c8046103105054480d10100c0c0c0280d0065a140c03003c80c641403041203c0b02034180250280c03401d01e1b40342c0e45e446041c8034000c010703017441031440c3c40188254581580c0c043d00340162820041c82e50b080400c1200c2d031a0b512207883d290f141c0b8000c2042082d45009401000b50 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 824942643 1250 824941393 824941409
    0x1209060703170c040305070f0819020102150103080a1112070b191112012405130e0405010b0108090a030c02011b0602160c080a020906060d140403050703020606011d090c04 75
    0x2c1482d00d608508016009032100341c40f5441581000543e00c603184104200740d40200e405000700003a04074100b0ba264a40c1c4600b24118803682e4441d800407085080300318082c40c800e81c1c01c0766640d0504030000f440001c91049240113078210a21060490141f8012101d110b40e1000808284e075503004500400707240e10300821902181024903c45803505084001e00441070840131003c0300e645c0703480d600300100c1030240f4207040b8074000f00d002c454128012409490f4030b00d01d0030074140c41c16842d1210b030891038500340c0d421201a134454821003920740e0081c03062a40013246100500c2c000c0d0041d103004021507941030002e4140024520880c07236090b4922880d00e1080e0b00b0100030756481d000400c21172400e8a400d081582c175012088030102c2c0304100407501c0d01d40c02d50003d01c0d10380c050701c8040401210340e101907881e1103c1a42c55000903441c080300d80c100340c4628002d40b2016140c1d0320b141006414104014216410490441c24110450214101d10100b01c0001e031b0b0122100e580310785541d40c0c1c83c0700340e420040c0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 824943893 1250 824942643 824942687
    0x90b1c0b01032d140f01060306060c0201360b03090c0f2209020405040308070909021c02030907030b010f0e0114010f0302180316090f0203101a0f1810021209060703 72
    0x410349005d401c00360b04803a081d650402c0025038030308084071000e810240c005d00044015a244003105044c0310001d80e100e8884002d9000001300d02c4c1040051500f503801108bc0c10408404c001030070401b4050f0381c1d6114801c0e03451080103000080054407070b00340c00c1c3d000014140c0c1ea43e4802d10b46001540301002282d4058401c0141782024100074011010071a1f55000007803000502160000c414025104d2900c0b028180300c509000ea100c5480c040d400040c4080c1091260310400004103280e103140300d000b01000329040d03411a08125002c10450416002403018841802940f90b8590b80410401e4003620340e172134010303203071a0244d00e401740c0d04031545d000c1a0f0510803010f800450310100151031040700c0d0b111000b00091400551900260300003141c40c4c000203141d1320020460b10040c02600c0c0b07603403042d180b159440c1543c00300034202c994006811000090b804549a001681041c006000088941380010600d49401c50f076051042e200f0482d20a005400101c4e407441014014501c80c80a40d0004810360 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 824945143 1250 824943893 824943901
    0x3040e100806090a0819020f03070803160f02120a110714042301060e0111060108030a1103070f021c080408010902040c0f0906050a090b1c0b01032d14 66
    0x3019482050080c0318503805880d001c40e600410001d20010000c1e4403807111414200380d0412456000b10041c0498298000e5011504a10200b40024101e60b0300c900125a00d0b810a04401d5401180c40b101000c10f003c950011103845640009201c0c0350348074651800c558402d4031850443c0c05c01d03c034005104441c0f081c0c0d1800b29130219103c41f203004000c0b0a0f00d00b04200e92414041d03007140880c81c101c641440e43d0100051181a100c0c04d0798100d442d0042c1096500c3c00d2840c2d05044c6051426408100c440c1c03c0482c0c0118010780c00000b81e0708880c403131401182040043e4907010640050280028400d0500881c0260b400f00040c9200380d6042e04070752081e4455540e0b07284035002e80203d0384202d02c00c41c58100001070040c0191031410110103103554010f8003a044c0760b0155a241e22003880d250600080d10400142842d41900800c11260b2280300604c216490b0094841507070102140381e814941007010802cdd40040340d429981c804480400d48904580da41d8034a07100074070400704200034500c1410200 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 824946393 1250 824945143 824945161
    0x92018040204182414120c0306090706020d080106080703050a0f180c08160e04020f10020c18010b0a051b0a031d0a140f22140603010e0a1403040e 64
    0x20400c031020941e080c13141d21881c5005a09120a80a500d8010480044c826101d080284051203214100710894201d02d003000002490310500310382c0d41d400c59010034000d018243e81403225007000d5906040069040d410550044c00c240c038000c04100c201540c51000480c00101a0400100d014101204010440140c82040c888000e2000241c80000340c0350030000da2404005910150075201c500d10b2118170b4284400f00a038a90043c0099900c01902c031100c0855540b80300340c03004081200e4005001b0401c0c054240000012061b614400d0016001c004202e4500800b0498140b5201441c1080d511025811000318820741072140741c46a10900c41a501055000b880a814441d142c81c4c0d030b6008004000e00f00310810b022400b42640741d280c1d41e40748020380c2c1404a00c03c00131880c01060070001c0840022241c104400032218040c80c0741c0c65400b2102d003500f0b0b40d04070a422103015402480281d092400700f40e0b6a40c1684401041280702b40440401144c00740242c5018000e240e8490b14241080108 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 824947643 1250 824946393 824946401
    0x3606020c030105130f1205090402030f01090b0103060806131b060306180c0c1104020c010f0f0c020a050705012001151a031b0d091a0109201804020418 66
    0x2800780290718140109000d203c40c0c20100c00b481e80d001003040d81d0f120455851159028002010209210042c4040c1e0055911800039504c1450807500b4050720390702d4542204161660b0f60141814149070880511480c0780104003a0380c464088040350140e000945095107141c0d045590003101e540c104080070034001c0e41504030a086030048840c0e003041813504912401154500104040070a14004a1900094050303201c50780f0400018030060a24274007088003420742f000c04100d040c0c00c27592101c00300705041380c030301c2803641200d0140300401c030100c1c01d956029910003182c00345a0522525800c0e00d5900560000e540c03c40d1481e5200030f11510324a5504107805146602400002d201c613030048254800d1150141e9224542849103000c8500d14084c0001c40c035408845254010740d22003000e200421213034442910010b03007004a0a01d59071500f07090008440030400000000000842401d402c000703040d0039510080260781c81c406804501000060082c480d03680300c40c49101d8011084001001e4030f40c0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 824948893 1250 824947643 824947663
    0x314091b0d1b0f08031c0b010c152406020303011703041e080d0f050711012c1305090337021014010503210f04031202010f0507360602 59
    0x115400c3c0b181d4494410540b41d0140e02c07041460380d00824505003e129181c0c000040302c0f01c040c1400a940159130b180c8500c04401c402c0c0300540c46403a41842842c501d0001d82c5007861040c50343c003203002d4a00341304c4029103901c010312032190b45e20121034554900141c01d0084400400d0300d05a81420b400c091601c00c80f04002900ca10192400f403096407a6410b170003014441d01140e907582c0c0d568585000c60707072000c03840307415003011303904001d0703024855400d04800c00c1408003e0b40302a2000043c40c42040708111080c42c0d003000202c0403905003003d00a00f09000019602d512110b1702c618070a5142c11b0f11a140303035100103c0180d141b0001122030b0002140c010600804004181800b400801980355082424000a02c1441e4040d407040442100390100038202c0d1141440d0440610b15003900d031381c7c2641c2c598229410585404641703600d102090f85c0c0900ca00c4140c01d404c00e0701441075140104010b8148c1081c1c48a0022100403c1010324262101a035080c403401d00c3d4078101220070b51503043c02503039441e0541c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 824950143 1250 824948893 824948909
    0xa0614040f03052803080718081207060e0319080a0b030706080a05072102181512010905060a0909020f1f17041515090c030c0314091b0d1b 61
    0x4c4040c400140340c0c0c0304a04a500f503281e01c202511501070480c0e00030000300803140c03110801d100c04100c218080c40401130928402a04907101e8185040100c01c8a10040340c6400c40d620803c8481108412030200400b2003410341000c2ca01991080409000703040500d00c419414051074502081458200300400c0c0616800c1c5810092031340c135206e0642e01070055100901c504021042c01003402a07035034000304900c030122030601000003030a00c08511a8095091007074000400880c003581c1c0c00060304030150041580210502c03c0d4185000030411201d0030340210305596898507000e1080d91281355030111140070103040240110001001000580d0b004ac0041002502d042c2d56408246444442036010316001016417014001d510104001131a55030f82030004841902c0c00050701113130a10030303008115034035140030660400e0040c008046a06c3c018114114a15004c140500024001480e410b0b0090340045400d440e41c8420000d803403d44142d00003005188a0a040308041c80c407480b4120807a9001 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 824951393 1250 824950143 824950183
    0x150c050f04091d01020c10020c0705030703080301030218011217040b07060f052a0d061e06030c0302041d0601021e15091f0c050d0504210e0a0614040f0305 68
    0x1420100d400d1b0710410882034140d07400000c4170396003840d15a0041201041007001c0342c418a0784e42d0003207410100705910550b101071000c00100103608102c51210956498015156101e40c140b56140d4114211020041d000000d40142d2030944003240d002c45018200c00000c26031102560f01c5c1640c0900301080d81401101d00f428003095541014565175095500c101c076104609036201008a000342c2c02c68140800c400c1d071a2003000807551034580030495440c074980c4040485a0810402030207a90b800c20580701058410082003044140300351808030a44803030720b6400707010f8a410700100d01c0c1c10400e111000c0c00071040c1406420340d10000a00110b00c611400191210b0360b20200d03000e03101e450300d00e0201401c2140d80c403880c41c04081a40003103a54250b0f41400c80c18207803128410340480304121400c81e60f6040410340c1d054001e140010701d02c44e4a51504e46680d0100441010680840e940c0c824001445a0700d404080701c0c254400030384019001840102310003e6680c00c0c01640e0b001210f00d541205040 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 824952643 1250 824951393 824951441
    0xd05161e02030c060903070603050a060b0307120c180302040c02070e090106030c050907050910020a2f0906100e0109170c090c0702060910110706021b090103150c050f0409 75
    0x440c4c0305071400c5080040240030311034a02001030380a000c0c010040200b0981d80e040c0071030109854070142d4052000b50340e65900703c10b030140084017111105c1649505120000e9000c24040803040600c80550b541990003007900d2248010581c41c103041c98220384c00300d09007681003001c1c50105620210440340101401e9150a5650084c03000d1004103a810f43e00185080003a03204a0402441c0c3c0c1c00100d0407881210030101442c2c840c41c095440c14000c00702c0c80d42804110100070300d850380702c40d11300c0c030301c01c545082084c2040c00000d8401c0f003041040205014003e80800c41c01e80c00b0302c0f8280001c00000c00441490300d00355000640300c0307401e003481911031141300000c5454602980305446101e80c1c090700041c5494041810090940c2241d14240c08003e112500c580300f01d002440b00030001c1c5241d4000380000c07070083d880494945065030b40715020b070941c5801003000c250404180002d440358000000b852041004044443d84980c0c48103a8620000090005104003140d02c03007a002512460403508040d4 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 824953893 1250 824952643 824952649
    0x11010201110405090a0b010c050307061407081603050709080601030f0b0702071202150d151401020a0201080610051201032015030601120209040c031416020d05161e02030c 75
    0x5240101130708018a8000030302c0e4207196502101c40224141480744100d01c1e299207461465010300c004480245e111244002c020700312600d01600120385041c8803a05103030030a0141070640b0024288410540c584001c6200303540103042c818050320001064884e59a101c0c10300410304000880c040313880c2040c041c0002e0343d103440403d142065072041a541c01b00c0c2c582c940c0800c0403c496480c81e1221300401000161040492440350782c1c04175100c658103280746440e042c80075609504011390b0300d0541d0402c24103d80181c0c5d0000d01c2a502078822520403a036200c0740e50044400d401080542002005644004000d1102ca500ba00301410310340801c035011a55454140003104031180350f50f00c8201002c0c404100c0c158003600b4200036000d001c10700141001d28660006c0d066800200254001c6903544481e060002d0340c007401030b40d024205a90444032000440c1009584505078001d62041202c0401d8a080e95880c81700310100b4540c002d01e000e161605500c020310ad500682d101c00301e10a02c0380b44001300c4541 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 824955143 1250 824953893 824953897
    0xa0b0c150a06122004020c0f120a0512040609020409080d11040312031802040f0212011a16031101141909080a120b0301020c0102030118050c0906071104091101020111 73
    0x103110f20360700f0010890690b483c0d624015071080343d0314685901e4000745041c0c0d00e462000d000c094003143c2c0146840d9007095015404c0604000100845000800005031034582003404c03990404a8600c25000c1c1da5100c0c10301c08000c0c210720000035403290a00700414107100c1c4000240003404100c5070104031400e02003404412030300c20351100910141c0c0c2400e42c0c0098038026408a44030b100344000c550881d1007a0b90004045402186a200d0910340c0442d00101081040990b41d0141000508041040c82d0b014001030b802d00500741c519084914200c05002054850a03c500300820161b0092207103245180240368a00d0303084820440c4200044c0300345600c60414041e0202c0c082e0044074642c0340c0010094101d901e0801c0b00307585558561102d410044a880900c01002e070707141b000000503125410004002e0072450403040100303101d8180400e05c460f10004030202c034030045080714002e50f179454511f042c5d51550040c40710103900500c1c1c00d60390303000d100d8060f11514132100268003c0000000283c00081a4 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 824956393 1250 824955143 824955149
    0xa0303050f01063b032b05040b04030b06150309030706050a0c0e010f1106010803090a150801051e0301020a0809010c0306031109060a0b0a1e08060d030e0a0b0c150a06 73
    0x10792501c1000a98107101101e14407004c2c00700011801d010f003140046072078120002080301490001d090707880342d410310b8125084920400b03490440c4ca000c2c5000d01e9010035024034040603140041d0078010500964540034101032640d0881c000c2034076484d001384499203e8000d0102914058101000506c06900611520440000c40d465883c0503a40785001180c0b001d0425525038140004201d080c0b11104042145c3c1c0c1c0246110001150350342d01031000e02000c1c0200350322060a8000d022038a540300e0780c2000013541902c40580d0900c022078001880780c19490b5038a064160154030024403005141d07402481c052041d812103000b03101a40410341e040f000c03120703035100203031407405900000c2c405c0d0700d0840c1e603c036045440104801220b03910303541030130b450342e114070050400700342c08100490004c171100c1380e240c1c5600e489041c07908070fa240950216480300b200220040410100c4410384119a07a06072020001d040801c0b003040c0c076504000c1d00c807a9541d503c0080140d5a4610100107491074843e40268425 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 824957643 1250 824956393 824956427
    0x20f01030618050414120910050c0715140c01090209180309040515041401030510050420030f12040509181c030212070c0204050f22050a02030a0303050f0106 69
    0x8502c4140510100030b243c058001c0b20300c120840303103584014000f00030801c10340c0305840e0308942d100e160100b008140d4803014684020300405005d0410042000b0410707204844009c2a5200c801203450b40c1141c211042d4500182e91602c0400c1500f4000015840340207400d00c02d940d0403101d51205000034506840103010034486900400c03004c402414140c02498205c6080c0c440811064038120000f01030302c101d40030400c0134140080040051050812124031321a00d07135041081641400d840740e88005811034840d4500080c007107102050390b01e041000d0140701c03e00f0810703241e080312903525030b181e10350181c403495104840110204802c06940001c10400120902c0180310700311003002d262010301c2c03174900c1c10070500da800c1c04090310710b90303c0405c10f070302c43e410603529060000701c540f041200301d400c0541410801c1881400b0000341d0070792410700107032034000c5803105880001c440c6031a900d403012101009415002d80c80c03c0000301500741d00558000d44034904d003240140e0302e440c41140c80054400c150030b9 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 824958893 1250 824957643 824957669
    0x103150c022107020109120506040c0e0708040605040212011b090902040b0904151203050a11210f0c010e0615030d05030105011d040e0d020c010212030a0c0219030309020f010306 78
    0x5000e40e070700d000f0400640b060406802555076111f022a003180308820035201c81d00604100400c01c50241c400101400010740481510308001e00300400d07182c1c00074070040c0016070710030124040d903540425031a2243e0200000340103880220260a211009184040c00859241c0c0c1c408038210840c1e0090309c0944054030b04a0717080004010400001d41800c1c0c00d450840c8152110200300440071040480045000e9150b440d81c2c1c4441d03410061240d001e03041c01c078006801100402e0f5414003204225a2080b002e401030b41c0e1107220350305030000b2070310442001814540ca801c05880e41c110010038460b2250003030010008080300004185502c50365001c5c00d600c000782c07040005201c2da6002d41010808040c5502010156a03c2100031408503080540701c60b5080d401b0403900356040754104588400a030080c80541811902440c8400043c04090481000581c41d00f00e40c681035031081044801400036007010145580030390070f02034014001c0c0d0f402039000d00303802d441e090700c1c55000340101400c4502360102d0039 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 824960143 1250 824958893 824958943
    0x61504061a070b060f031005010812040806060405061c030207080f070303021203330910151202210f010e130809030a1205250503031f0e0103150c02 65
    0x503c003d88010640c99015180140380591a10200700031107604004141c001069410602d20358940303020880d461100007000c010600c083d040215140350800340c1503401080c2c0340c8545c40050b1211480810b03e9003007600045184003415030005103079086500342010744841c0c0d020013110700e80310301d0300f40400f07800750780100140444005a4001941d00901c0e043d4071078407a1400030704210350241d07400e84202d2821031442c0e1401040c074054000717980050b40c0f5901c123200e9178038011840c61001c02e004900c005101520f10362910400356901101e900e0b03110f10b10540c02415001b80e10711100f51080d504084403486400001c0b40307e07411015440c4c004d9110942040031184103030345031501648a020199014000c2d010008005041340d00100d400b426145c8420740c65518240050f100c001050030044610310000440c10301080b00441225008840c0c02410350701d0803021050503217104171541c00f0b90f070b809507040000001c2c0509103146c0c540c2d41c58000000c2c85180c0e468441242d0720389002a50f440c081107003840c04 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 824961393 1250 824960143 824960153
    0xb0a0905060f0424020d0f0b03060a0c0302070b070504030311240423060910020f07171306260610120605030124060c0c090504030e03061504061a07 65
    0x142c0d4420321404524a0f15101302400700454030503540300c100003580214803164840308a009502a6205a240801140c030389800041e070b9403100602058051540c480c2210032941c42038040b42c504c0c035040b44031112103040c45d140c020096849071006800017181c10004a074120000b08403801000082404c404a40403e85000c07000e08501034000c45280203003040e2188034911800c0b1810310440000301600051911340b0190342000310050038401d40c680304000cc07040501c1d582003561440340d007041c0c2c2075903880340310100d0b501e85d486408020701449400c403000140e041c0d03010070080c00e9405400e000070092088110001d907000415038200391b10004074850403c68a00c24000b45880481c0300703d000c28400d650320042421101c4049244050b418942c4403004023902e00c4031110300800892401d2001403402e41ca0707040200c10070380a41d00c94592500d0100d818075201c0d90140b83c5460005056070790904084102c0c175050710018018500980c01c0040025078900400c8d80c0314102203030f0b81c8006240c010329560b0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 824962643 1250 824961393 824961421
    0x70305030a0902040504050c130903090b03040218151306051311041203081f050102032205040203070e040e03030603030a11010e190b010902091c030c140a0b0a090506 73
    0x305060079035241e500001603a201e0046600590080740a443d0200101d401d00c8040b000a0700d6401c015800c0215031000240d103c401d0904407019809031329142c0d00d561000541740039000b01202d1404102000f404216100400c00d002c01c0030044903415100e129a001d40e0094980c64824103500003200f0b541c610454031280c00002480d0200b592403481c0903115040381c981810341020903400610124100100c603050000c4007031105e2414110303440c94601d4600002d5880c4145403000181e0120052034482111031902100040e00006005546901d02042c00401c410003841c0142c1c03003a0300300030307c803800b0303910220403a07015480c0074000c2c528102d2503a90950780c511182c24054295036072071048000c07450b0140704861515103507540d10107110010742001e000c500c4c1c060300940075042c0304122031f480d240e8800c464003421b4042e04043c81c005410031308040e03030714848003c006040d035200d00d011014a80c44c0450203154052050b03c1c01d2119458400703c42d400c83e0401034000307055500c07a4001c6245400c034400 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 824963893 1250 824962643 824962651
    0xb07050a030f020301230303040e0c0c100212092a1e030105040b070f0807020a0f0503281101090206030a020c0f0d02010b0f0306060123071a1b040b07030503 69
    0x703020a9000009019808030792090740084540032091245448440440f00c5c0e0842200c4201c005508040c2050710144540300041e0807140349400018480b0b40c2d442c0240301c06016518034200864441c150076508003000c840859412a842c002d2119942c19880e80d00c500c0300e108801807031f50b80700385000c0340706001000001c0306807034071522020a402c0308079690900443d4411071041d100110035003040c1102800140d00640420240407c0c44100903400c1c0d0300055901240d81c101256040c542040c1c01c040e4110b11410b1407007100100b049000c410b215610410400c22506503a54801c0d01101408c851800c8600d4100000e600c580104081242c3d403000d40c02800c1e00311040c00680300740d008040000d40c5001c0400d101000540d4468500c4c0441d40340146040c020008168046d096905c0d00d03000007055085458071305140c880015820b104c000c1c1c0910705650034140e0140e0640d0602180040131248200100c1e040c2c0c0150703000645034400d00003400266400c96110010311818881265000c0e076071900010 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 824965143 1250 824963893 824963897
    0x703051b0f07021906080c121609031e0506090c060403110a05060714060606210a11222403090201030b09190b010315030b0402030c1005030708060d0b07050a 69
    0x102103280035948545144c020440c03800c2d80306400a01d0b00e40044c04241c001448900c2c1080c080c426a9800804c54020340d40c013403040c0b03a07020405682d0000c00d89501d000c941020304040c10380c55101803140c908400c00401d840c0508201c0d80c40b40d0b98411b0b41541c4043c07146000b604108184810800602021003d14158800400ea0340b5000d443c1c5011a0b26070700001400c1da59900348611007803c4400610409800c0401540d00c01d28000118001140340c0f00c130a508156000c21400c0010b15107a1681d024906851150b08496a110046512415403250f48050703151802603800002680e00f41d01c041000c1c201140e405401c1d250b1b0240710041d0020899480c05a0502d03446006201a41c1c4c5e880c030700c8070301c1000a45200c400c10380f10b41c0d04400880b007900d11954189840c0402c81203032901c0e074bc0444000c8aa2056903e0f85aa56900c00300341401c0b0504800b82c4c01075004844602d07200c0c2c00001039407180605540310400c5640715410040c03952140500505110008004100302c01d102d6401040c4080c000c0c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 824966393 1250 824965143 824965147
    0x1403090106090e0307060f020315010c020409021f02061003030c02010c05070b030403030e0d0e060d1109060f041d250509100504061409090a05040201181d0703051b0f 73
    0x2441c102d20a40b904090510000e0f08001200c000b000564030800795104141c010860451074558400c01d0399500280c446030600c079465000c00d0841d41e0717a41200c0340f40b41d030180005041c40608688080c3c0c02e0301c8809400098096030740060320b00c0746174000380302c12240c1655901d100b91409400542d0103c0d20b401c41038a207070240c1280841c0304d9804100030b40c02540b00360390002e00741b022800a0342c01c051402000b102080394910440b8407696072081611a600d003000d500042c000e18608400381c05102d0000305541100c00800c61b2151660b001317000c0c00850782902a2541030482303508089040d010201c42e101c3c40c2c0c090b181002c200c4480b10a0f11080b040700301f82880c62807c182600080c0b001241d2141c2e21000910000d018130000764042d41103081c9000044100b41014000310000700a80030080c048813640e99114001010341e8071039144c1c0c6c845421422150409203456440c02c000040042110008040390300c03000c1000355110744121440342082184d2041c5004d03500303041b141c0a9114000f030140344541 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 824967643 1250 824966393 824966399
    0x60306030c0f2e03060e060a090209030c0d150e070b030c0310080a150605060f090d05071a0c01110705031611040606020c101806030f090803010e06030615011403090106 74
    0x103c108000c40184040c0d100a45202c034000c0003800c0e034140303400c8020340040300410701a00d91590180c2c0c80c2900c644803005a2070788050b1000c24504211017017942d80c000d101010361020300c00301c440401407036406003500380854100b4800980d0384005505c40e10301c0c43d400800014848030f50341c2d40a15002403181c04403150455423005028505041c219090b284c0e1038010104180038035a9211301c0000b032000741c551600b0140e10151090240c05010403240c0200d100c5109003003041005c0c80741002031301386500e20203000300144540340f6039504402c5d0780071000e41c40c0441c0801850401016150000d0703018000310324014003018912034000070000c044402e140308440440e80c0e40c1d100d0144402030056540140600c41070002003100c0001000d01c4c050600c9403100e41c0e8902000360b8042b40042d1000c43c00c0225101c3c07600c011a038014180e01c0f9000d00081404030021417050250074000d8005c804c110b04130b41d0192180070203450b4201520134094041841028000600050f4201447c0d000a040c40001183d44d5 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 824968893 1250 824967643 824967679
    0xf15020705060a271506051917010b060702040b0a030b0c0a0806090603060403051303230c0f06030703091a0709030b010911031915060f0905060306030c0f 68
    0x1020854035034010404101c2d491255102d110b11603130960030040d2005100d00b813007100c001405030300900030304c081c0200034180c8881703034004030300078200642030000740d941d4648801140300c124020400c140f0b032917000a040a080502236032001e0180180b01920300031140d8200001081d510402c3d40c0c02c070541c0000000400c520029582c0300d40404c81c40d40b680d83c40100d10007803100900a0500340b02e006441e0a106140c5c030001059507226130302d4207041ea03841248100b0b10415540a620040c03502c01560704181c040404440444843e103155000c8890703512070081046605541c0c1010700d0b4001a042c03000812040c400d40140303c1660007240f004034481540281c00d8441c0c102250414007082c003240d410002c00c002c22000c1c60050200000400c56240b94409000081c4005081d20040840c0c825545848070156805010210b410300a004032040c1e450501601200142c20450080780016500054505040d401c6a1040b00c00401403c00c40c4060f5040040a100307102c00c42d0340050200400c05d0041c8 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 824970143 1250 824968893 824968897
    0x10050903150106031b0207031a10080a1a13030f0e0105070606080102090a080a030207031b080a0302100506040b0603040204050408040b0307110d0e0102150901110a0e0f1503040f1502 80
    0x4101030340c3c040b85c02c0303250840482c800080d114040d011035104580400100c1c801442200c0c0ca80c0c0034900b0070284c3d854904c0c0103807005020ba00008030502403509000c0401142e150002c1e1810010301c28642c0554a50040043ca48982d0001601103000c131f14110b9026803046485062810050404c1400c107129074603048111a2640c2010f010b60b94002003c01e003902e020b031070100041c8080d0b001031054a4050398020b44800c001d10009103c21090345281c4a40ea103602e14520180c015002210700c06200c5040c0207617141c1a00b9552144a86003101003001402c01b4002c10400340006003040c0c0ca591a69403c1c8001042d000f070054511f00000c1c000410102d20081c000d502560241d6900d903603040b051036059050000c0c00c070001701848180d5404104990300841e5000b11081c00d40361501d8155070b0220424050300100880c501c04000c00240300b041190051010381c0c21f56000e55040c44040c1040d0300b4030400a500c2807034100c90039001d100140005518520784080c0500c074a92841030702d01503001d10b105907 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 824971393 1250 824970143 824970149
    0x70311070c081015140a24030e0613081b030403080301090b19060503070315060201150f0806130302101a040b040606120216020909060601021605100509031501 70
    0x7040c0c164401c00550608001d80240004460710400104440e03108914203650240720742004050740d14400011940c544003504020050310b50000300182058174603542480f1030704003400c08030b0300d08000c00d03403581c0d80000c80d280300302c8445000001c1c148541c1c0313800e00d1075003100c60601d0304100e000d10419046841400940000d51041d80c3ca079460754103010301c0100752001144e4444c05000d071440040c246a041c0000c4104840e060b08041d13a894892a804a001c0c00c00164210401d039100300b000100d10381d05522011801706201000014643c407552444016401d6101d034210a03440800420703504040111a00c562500c00c3c012a007024406044030002d40b14100404c0850f40d600e64107c09031810a401030680121040303604000080c100040036045c0401208803c80480e404186101070460303026481040700e400a2060b071040c40d0905c986a92803d04075041401070040e8845032144800c90100310095a50040040400c00c031883c800315000d421804030b20354180304454210b41e01c440c1e040b00d42406 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 824972643 1250 824971393 824971403
    0x61202130506040f06081803070204091e050304090b0303030c0403230d0203041403010213030b1305100605010224010308030c040308031504060611030d02030405010902030d0f090e0f04060507031107 87
    0x41203150a10280035240001c7c8010000502e682c1aa6000440801120040340e030440300050441c9a40c02c0060b1101d1090401c14000183d500c210701c28000d000003d08102c0d0031450301489046205010305807603000540d001c040e180350521060000490082034005110b411604a500308000f004441c1d00d010304800c200805030300001428800a50b1051051040010590081d8682040200400c40c200c01603c00a40001038440200742c548003c03039080302085030400c04482c40b064180c2800001800075210b0540544201c8080307414406c450322110494042e00140d44c0f4480e0720b192600810765100074507070320028200700004400182c14001550040c29801d400c0c200000f4000240003c456040d0011014088505001080036500000702c0300c10421104000d03840e80c560380f4107603014140e0500020341c980580403408481030740c840080700e0420082d9440c0c4402903991020807000340015500d041c40102c8007070016010464940205401c8002031600103049202e6080b8031409400c03031007040755 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 824973893 1250 824972643 824972669
    0x15070804030507061106190e0f15070c0b181e0f0601050405010f170c030d1701140d030f020705090c09010909050907030f0c090501090e0f0706120213050604 69
    0x2c2c8202082084081c19150801522641c00c040c0d565590b03840007019801004044500c41e8222034054109010705000ea00c11100a05d40300a0040d458004401c203801d1104038000001b500188140301401842da000000e80100703441e81241c0700200f001c0c03214009038500c5850400400031901c40704510105500c403018061182036403050328100a07042e8801442036007014014085400d06200003000c072001a5918200403083c00d09890901311400111507141c01818804041650492500f0503154603804400d51940c0c8c03252800c100c560724034001c09420407103030103030303036000034000d11000074030003003a00494882030758400014143e880308032150744030340c3c07404103400ca90307544c000c00820041e01005806001c2c1d0700c2d200d0407846e610490b40c070028003483e030000148414001201c07024409000c40c000b06005640c3c58240840240400000a10315031140041c4285040741c04a2403d081c0e9205554060f54680305000310b00103034100f0195580c120306104000103890340c4520003031006100181b01c0c04 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 824975143 1250 824973893 824973899
    0x10915021203010f0302030123060d030e04060603020405012003040605030c0c010e0304050418123203100b1809060a0f08100b0901030b0105060f0903100b15070312090215070804 78
    0x500707640d840904106d07440003440c0800c41d100012700055500c200251442942404103040488181542582c45e0780c0043c030f4000c0118185a040d00284251042030701d4000d070315400c0380940200ac0d40c40041660564009001c1445400d10482c011500030242d9440c0c42d00746000d4815560840e03c10b03044007070240e40006810011403c0c140a1645411303001d01c4082803019613500e50b1414201d04032260360402c0306000e41803242d400c0380c2140350a1980815001014481c40d0720108040b40d1060303402c03c100340890400000c100c180e0303108480c1d45141c40552162000340050500c1000080035041a074080307000d540c04101041d0740c003450802061104018207001485138680f808843d40b00320818010001080140081100440c4407411a1401e4502e00e5545180b150031510b00d000302d94020b0780c10b00404941c8441000190004080480103d0322040b000007000792031481c074440c4200050104800c5020f1841c81241c0fa404880c0950019017a003116460742c800745002a40303c142c044070b40f80380104041c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 824976393 1250 824975143 824975149
    0x519080702011503020f2806260c09090403030e010f0b090109020c0a150204030b090a0c171011090d0c0e06040b130c0e090117100506010915021203010f0302 69
    0xc090300305090b4164001041c10b580218010542550016001d0000d0f9040e1400e2117034220040d41f484003902d003200c030100307880741002044804105001e0104040c9000385903c11168901c080340036002e602440c1e894070750400300303012601200510540030b02d41d480040c0c1c0f0b4003100a009258400c9a41400010030756450b00410482100680100309124410301034090002d0000645280c4560400b148040c942c5140011101a100365000204195139034424000034000010302300700034a210307071424080301d5201c5200c0c2c00046140b06203481e0341d40c4583c40748941d46006500020341d0f044c48480241c94194442c01142c4104c10301700d02141d2403458a0300400124000030041608100c0450702444821b003072000044004900d608006920b07559141c81d000c04500907211002c0d4118040c1c1101d01e9903950303102c2001f9442c4031202c800902d0187c510312204c0000a07120700e900c40c17001610f41442c80c03400e000003800072601c5200c41105522440d040030381d04455240155000700095100410032034118418 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 824977643 1250 824976393 824976401
    0xd02030f070e0c04060c0f080919091a0a0506090402070c0b0c0f06090d12090b0114030c240c030c1f0c0305040218060103090f05060702190503030a0c051908070201 72
    0x440280700c0c9084c80f05201c084d134041040365405800c414800040c090350300301918940f288082084e8080e40b500403d40c2c140108002c0c1c10102d601c424010825404900801a14183d6100001d83c0c030404006050000f46440c078094030154030040c000508181c010b0380c0d000c4820340d142e00001056800030810724801c84040189500e41000d140140019041c5501d1103592603404404400c244a00ca640b584558003242d4888005140c00c00000002d659460500181010014010754064001c40001541318144101000f00401520740b40d4420f07218110084078081d000480b0461141c002000240b102d0a000c001d0003044c0401f114144c007084560a40140c100c0d02c07081030300340602d0b007400100030160707132841c00c10044072481451100840da90340004030002c1c240d0100040c032014010340588140040002e00301e11a07070150302280d1007085000c080c022994041d0300020301c00d6100b003000456680040d00240c410a03041c0c2066801c14111900c0841d03d0300840c1c2506000400003001c1245c03443d82401 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 824978893 1250 824977643 824977651
    0xc10030b09010f1712041802071506051e09190b190f141e0105040906060302030f0601090e1909020901120b0f1303030e0c04150e060402030f010909020d02030f070e 72
    0x4000341e200e121810a01401b541c891400d080c100c01c01e12100720b807043d80440340c03c282e0241e011042e036031202004100074980782c010b09000c0c6000302c645420305080c0030141c1000c460010180c66003591140c00c16001040500ca260142988402c0c1d5081c09440d80081e410707a01c0c4c4100f400c560242d050180000c214802c6901003402da0000151043d00303901e0b010345010301031545061042c030042800700140c0701d038420366000c000d10900e05a07001540940c1980554000c1202170035003c0a512014011a1032021a01824801c0b840d5040030900f4881d54085101d03841c48840000300369004290001400304400b41e00c200f1900c411035a0004c01c12004502c815803002d100c0d00c1546081c10f00c841782ca180030000c00d20046c2030680c2e89280c0280c1c40010000040034880c020710521000310900e84006400c0b0040c414100b418251402161281c036050080d28401d4028000d106502ea10f084403c4014140c400400c1ea000128100c0c0c11004d61801d0200d202038140140080c941c2510380424500102c00c010 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 824980143 1250 824978893 824978939
    0x50d06090f030f02011a0d02062107090503120c070b0304141e010f051504090303020f0705031306080f04080d0e10020318031612050d020a09030c0b0c0c10030b09010f 73
    0x30380c0c01c81c021f95a48802c400101e40503900c0c80d895500d0140000c2030340181440640440c405c070410400c15540c4618048150b031b40540560f1f8500200e0707840f20607603000701c145500c1c007900807040038040c1c030104202a40d4450b00500c5c82da0401c4005072006810000030303004c020302045519040e80703070140090081c40c1e4142154042080f0724504038603020382450381103106510030b58540c0e14623400d062003a0190b03024a20003c40c029500c6100d0701d40255280c0c05414152a2403001c000300085060003034164a02c43d0002406d10b212554465803401c62943c0a00407805865a6a0340c001507001c0041005032229442c42000594030308094a450b00140600300e60800254010403130f46509c119030904500761168044003000e90442c0002e020303076250151b101210400c51021910f00c04844d4440003da044034041c4900781d20f1652204195081c500c520190f151445c0c2c004a1180c0d81802c004603003100304d03801850300240f851380440020342c02040a80c49103003070202290040c007042d1007148220301d2461000b = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 824981393 1250 824980143 824980181
    0xa0605030609070306020a0921050f0601080607050706060e0403080103111c0206030a06080303070815010309080702010e06041805010510030207020a0603091511030718060207050d06090f030f0201 86
    0x560000f6551401400b004210503000310701000391501448410010302901410708403a0030068030303508600082500c09584a1080d52650580008013060f102d060b101900c01400e0b00d582e488205a50035481140200c81c83c0d55a044001014207541d00042d0140d0300c00d50314004603501d541001c1b0105084215500c2c07290f0100880b00307143c1e400036028036040d180e050302c441d43c4903a60702c44494020051030784000010300000041090095028003194445e50001c1020707030022043c000114200e405240c0028205c0d00104641c45c051340c020750b120032802d40e00500580c84e1540342c188505030003192215502290b500c41d001807099146c8000640c0201d5005d18003107051440640000d881d0001a21400d41803550300c074803402c01c1c0310400030000550070384104144600e00c1c00452144841d0702c115180400070701c040181c0c0049450040010f42250041c1d8010000c0c01e0070320003080411601c0340822104180d4454a50780021040c0c1c400d203507018000d448480050f0112400a420750b0642200e0700c1c420447c03 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 824982643 1250 824981393 824981401
    0x18030f0801150e181e09070e0c0d0b10020a0314070f1b0e04031d030c010f0e0619050a020714030604060b01210605190311010503040f080d050a06050306 67
    0x5440b5580324032114a107403030f1680e5004100400c02c081c020003004813880c103001d020007440c900400300c00c4501c1620602c503c0e226694503486a078482c03415020b028085003556010840040da070b04044c0c0a80c45215400003001a480000500708882010700707080541c104031401300515412040d50102840d00360400780c0323401c7d107942d03c2c109500c04850740100300c8241c4900014070155440405070281c04e803080403100e40e00340b508010b0000022440300d148000c0c80f1022102480c00c001c0381c0e4802240701038507506041030341c954040e600b0012140542e50000001d0101842c01c4504040c0011080c405844481d030700d01c60b40c18004e04081e1142c001e05021511070a0354040342d00d00246450b80180c100030001642690840101e0711200b80400f020410319400b0090560310909a210604070f8a04940c6405082c0b145d40b200b40300c5070000c2c48043c09000b01072568458a5001e0401954014850302c0e040d603080c007042e991946a0b81010100107071a655800400809903102d00ca0030020b05000c40081c0480c2c60 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 824983893 1250 824982643 824982659
    0xf06050313021908060c1207050901020c09150d0818120709020f0d05190b030f19020105040314100612260903030d020d0b0612040b040201090918030f0801 68
    0x110301c8000b4011080e1000320003400c50b50102c280f014003441c01c01c0d60030750309001c1c074100c049410031502d03018420030f0000803e10840c0104100c41103580182c014120740740019003009030803d001000e04038810100c1e40c015520f6a20040d6807215544550503d035203800c0000000c402903600100c156003d0840e4201c0f01c544000300255000446080d6a0f0240c1d8a813080074009010340654002103422030300b08402d02c8685c114102d810084000500d00c1003086003140010150341d01c1141c07044ca6020341000c1f1042c17a10000c6001800c01d01801030500c50300d420b60760780c0e5048041c45400c00e9454582c00c070140000a810503030140a004001031000c1810311005d41d05d400a041d4004401c0b5021080700f15030307001da05228841914540d0b50001c050300e03261425440712402960022184d0314415180c0607000f0860f1404400703441c811090861461030a82d40c5075510480e24601401c2a41400440d81c8005103002c0240684002106100c50881d0210078502d0046c00c107428240d0b5200a101e000001444415 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 824985143 1250 824983893 824983921
    0x309080c030c0102030a180b240a060e01020d0306060903291312050f040603051f080106140d170a020a0615080f0706020606010e12060103030201200408120c010b040e070f060503 78
    0x80c21302780950049544d896220520456506e940076007214448200040c4150000c0711241c81c41400e0302aa880702d02c00040031000c8a0701d600807040841c0c2030b2107050000c5843d1490400300c5d040c82c10004400200305144000e480b020440d11003820020a007072007010050070000710007180840742811802c15408900e02c01503400759006a20805540d840050f50741c080c524024428180718105496030180c4404100c1d000e0801802000500344280700f690886041c1030645210315504050810021181d001d0041000d81c040340c80f00d001c600c6408a404040b810910601800c00e903241c02201905207440c4000341000e412141c00621604060030070003c50f5004581650700000919110218030074400010f444035003401c8080d8080d100e040000b004050301580308540144c54500d82141002071480180201d221300c0c095011541c0041c0c080150310301105016001910320a1300114000b900b620105044921098070000320381c6c0201c0042051603400c0c02e03100041c0c201b502d000392a5103007808a2000c21 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 824986393 1250 824985143 824985151
    0x10e16030b030d030c2d030b09102c1311031903080c1b0f0105010506070c140f0418120c05070312090e010905070e0f030a02010309080c030c0102030a180b 68
    0x4151110202c030122480341c1e046c0c001499010152801107550380301c0c50311403001c03402641008640360000c00c0f070852070a00b03522071107440d15105041c0040d04042c2c4040840c0c05008000301c10070006e104549214107615103252107411411801c411042142c180342130081c09a11100c0e001b900030301740004840121120800709907030582031040054440c45140000d07131144483c0d500002d003a080e0740e8050414045052140303911070303000a20031a42c885081140511032020f00403e403251081081200e00390200c00801480e40052064030f414000201050549540ca480c003c030b0780fa6807118030300401580001d002c000188510b450340310f01781d455650503524502d900003d005102e08030190402244540c180070041c1240c00707000c6025580d04d44118019101c15034221000c60044191100d1900300102b5010400b030340100203204a40c2c0c0c81d00191700a001d1a202511200401c0050300c1d8098002c000400a00a00000041c3e03a89052500d0f40111084505d01d000c4c03034520340c1c21810204181c05d000c2904 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 824987643 1250 824986393 824986397
    0x1205040201050d0c1808030307021b01020a080a030903081b16020f0d0c1a1c020c010e0115051815061809040c032a12080d05010e16030b030d 62
    0x41a2164001030b10180229400e006020303003004c0124800c0c0350b02c0034040c000701034441d8482c0711954480313404c16140d0100700c4142e00140c4c4402c03141d03000360300044413000d130807881801a40c0b031400081d1904c03e05c40e4800380e043d4003c652203078080e070b04140e80b001d68070b81d001e080d01d103c1c1043d00c804010044d42c68412000c08460003001d0741c80100640d030b01c0c4d0710a0580c02c180204001d0b150303021071a08107806002407107002c1805500c03072001189201c2c150304071401e001641801e0400d6065081c9640c00075040b420300079150350f6a4100408501000b4403030b030141c490340d0710f040d10f540a01e000100155400030010b119511214039041c00507841d8a07011151200c0c500b240d00b180c66901c00700c030034000c4c09800b00015520007420310522051000406095041d01e010310300010407101070340e101e1051071140001040e034000c1c0101c2e0421807080000c900103080c5100f00311052401d00018441820341d10280c2003001043d5043e024408280740342400c4140803443c5040600c000107001c00002d44038800c031142107003 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 824988893 1250 824987643 824987651
    0x9021c1b0b22140d06240f08160905070e0301090c1e031a0403050d0501031a0f06030a031209060e0c01030c140a03051003050d080402030606040e121b0303011409060402030712 77
    0x104002c46500f15520b07620905000f8103101c411001d140840b21140d1158285801c198840800c8c0b146020681201c890268000a1000d030b1421000708004c3c04000c05140801118032081d40320741c0d60a005450380c050080b0703040140e003800c00400341c5030032140509103c841900340d401000020302c100318009981e80502043ea400da501c0c4c0c10300ba1200e11411442d43c001030307c0d00c0e00210401c03c607014910500d40b1004420b400d607544491544000c3c00e810340b442c9605074414800100080c0c42038440840b44256540082059449542c91500ba01c1d100000c5d8078040d005042c026800d56854800c0862102c0940340c14400e100102d243d02041d4031603201d00d0800c15407210300040100100307805070002142d0000440d2904249480f0041410ba0b064038201d109008000110b001c81c3b07014010b0b190701c944c045018000010103a01b10326402c1d4442c150041041c0d020840703000750400b0610145000700441d0341d8402458107418101300c480107009040f64821807050040c0700c03801780c1c0059920206940000d00007 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 824990143 1250 824988893 824988919
    0x170109020c0703051e060a0212040b1503010c2006040c1206180305220b120a0e0a120306083418020d0f09021c1b0b2214 53
    0x2414000036403c0500240301300300e128400f030822890003e22415042c0d003650401d4407000503c80680c410300810180d1101d03004041004190548082a0005940120b90b01c0d810141c0e4046030030340d00031043c81004a10492410395000900e02ca551465044079400380000c4e19045e500d58040742d58030b0180402c2500710190380020030540d54008a11401e800a00b03030301d605d06916001301113602c04540741d50355030351100349141d980100608590070b03901c540d41c805040c0341c103042d10001e40340c0c0000c0c00107000b035032141000461360788140040346042e40100030b0300c103260146400240a0700d1003070384481d60715484101c81003074010303840c5035040345580405559030044280341d4410103c160701e0341045110307036102034000c01100342c15801000c10210311074040c0811241c001c190812034144c07010194010300100c61070000d1001041c4000d0703e69202f041d0714440b000900d10708040b810220f42005800800001d00c920f0450302c511100c0c00207546020055456070304106004035008444080e8030b0203840980910 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 824991393 1250 824990143 824990167
    0x1701180f03020c03010204090f18021c1502030403170906011a0c160905090f0109051203180102030901231501050f1b070f050d030816030b120d090617010902 69
    0x10f00030500e8000d0007036481703e0315003205800901240e076554503420310380ba144a00b071103010048400c1c0c068000307010640c8240078000c204850800718004440303003c5107440307200e0750b03041074409180a580281d03a10000300346030441c6112070100141c0140c50952002e070041042c071001490150002e01c1c0c0b2500291140c4d041c0025a1915108150704580d0055502001c10844045d83c0198802c118410446140920740b0524500700e03030343d00d403001d882c0f078000d0701c162140070400300010354000c155003076041c40d4200c1081c140d50880e0410b8030751000d240d448903410900794100c800d0040c5104203540c1c0c0810107040444071403c803500c510b21100d05000011441e4880388171580c007616000a80b0140d603141c8030103660303552911a07810380110781d88060144070104160810308c00c90000709906072030700d00c5262030720341d0a280c00201d001c06007000c00d916022004c0c1c0940f50185044203000d00400144120030380c0e06c3c1c01510070300b03a41d0030103c02c000c40010441c02c83c0c00d588104a0440e04c6d580310051342c0301c40007600 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 824992643 1250 824991393 824991403
    0xc01030b0609060a0c111e0402090d0c09060e0114010f030c050c12072a030f020f15030420031506031903020a0501060f030f1202071802041701180f0302 67
    0xa4075501000104860713211580125003091140c3c07082e00e2442112504c1020000340f21044101811051452165070795182000c0c0d00070844040e00510706112590203a44e4800009419003041036026240c10041007426050841503026100000c001ca001d0064000000d00002002520707900f055100c1280d102d0090088040b078440340d0b500702c19680c00b044070480d0580c16900c02e80e401ca80c3c444c580307400b2a00c540402035081000c20461007002e03401c1c900d03540f50010b41c002c0300030044e6440f9aa07006588420791383c0d03601051092800700300369901c130f16250504040c01c0d2901d81c5105078410140c03400c2005941c3c040f402264040520003102665214840840c1c41c0232000c40410b0038040b8203c100d1014560006a00c924640c42500244044c5886a0040d03003d11403520000307210000c0d07580c2e0f61380080c44805080f06006000d20498211698036100c245a50060481b0f800081d54009800d1100e84444003c43c0e41c0c0c00c95a0000740328900c5040c0c0740c4070413180a44009441041070313079001810144244a = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 824993893 1250 824992643 824992657
    0x90c090420030105010b0403021c1e03110115060f0c080405120f030a0509030f210c010b030717010f051e0402010915080f0106020604050703081b03160209060108090c01030b06 77
    0xc0204032179030719503003000700320350044c0000d9110b00b62940440d0003d48802c1d4000044d55803240c0301820220b8060007010b9150300643e411414040001031000e003803c424411104518404841d2621040c58400083c0005024040110800c10328100d03600208054904441c11544150381200c80e4102e2139540030b0400345064035118190000003046c490240d440340207425020800c07001d0310500301c400c0e181c042d40e8018291125101058822031907040303000c0740c2d000c4c1c0700ca045813100208490000320700003810100c0ea0b80090581c10b0f14a8101c1132514000d101d007030bd00c2600c402d8200907a05200588030620b007035242c045150408510300007401c5910452124008100380030003c62001c20400018010310401c60b10401c50740c20803070000a0940c40080c10780d0080d50448040e02d425030454495048650089038510f0003802d511003110b4400400304002c14000d0b180701501201c0c0001881040702100c8064403480c10012071a0030b21840b1440400c402d000c450090038001585800c81e008901c83d0702071a4 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 824995143 1250 824993893 824993899
    0x70b0915070503031e0403080604151e0f17121b061515030f04020f0120010207171c1a0d050102030709091506031104030c03080a0206090c090420 64
    0x11070701c40d041100000146004d51300e603603004d03801d07030a8541054520450803074001e400551013038082040c030700345544600882d21020701c18000c8141c541c00008101c0c4a128860302412103030250410919052504800140101250011035584d1902c1c2103507581484000c0901301850018255500044c00b0100400c41036010013501c0c4a480c001ca16150103090121071140203911141c008014080c03201d040343c0c030078007221006140903220307038081c00511034200d2110390502080303241c0000146007500c0f0fa4884401c800001695400c0c843c903100b2010b07150740b1082c0440e02003e10048409050500d00050700108800001500c00710a010252a0071400d48469401803c00100f800500038190021441150580c0384c2c1200d46903283c544004850b1105148200e19a40c090180003803441b940201d41072203000c0204c40d003840c1d22919014108003c0e68411508000b00103902d048140d0148202e5600042c1c0314040d1804e070f40e24a012030303020000180005c0000e03804032180b500d0b18401189031941c0b0000a = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 824996393 1250 824995143 824995147
    0x30e010f140d0f051f140a060e190803180a0e0601050a17070e0f10050f09040e0d090f0f0303080a020a0c12020c0102120405030a06021c0c0306032102070b0915 70
    0x8149206500003114886180c0d84615280c0401c20018519840c01b850602410030320710300d8a0440103c0f980c007c4940002e038000140c042400040840c184d81c40098030340d44015695600d035018020066400d1010054002c8042c0b100c100042d4000340c1586a000000b800e01940e60f413251780b001c88600c044c48a0448c2143c1c01d04080c08034955000881000c0184184c80d813046e80100c000400c45c1d20440a114040040c0e001c2140e4088071403d100544107000d0060004181500740884650506001580ea10300040403d01c0400081c05020388201c0180034210743c1014941c29514000c25840c0000d004040440e000250f024510344500c00d4072005980002c407031607111690040080d2146001c0d0744050061117254507c41d10b440c1d1a400b01d0702142c00060042006080c1e642e10b59000c2e402204407458286803603840003a45c46e605004404491040e0b03940001e0340c034118608035040300081d141003460400e50000181c1c165030005404400e94031040c0c1d8036a1684480c8001880d07411740081c80d09441000 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 824997643 1250 824996393 824996401
    0x80a03320402010f050909061009050d060218120a030f140318102a1704080405130207050a0f141e010507030c120c090b04060c030e010f140d0f05 64
    0x40c0d006841d0156100766100060039801c0c56040341c1501800c004194002c6007280420258a40301000100704541820890603443d560000a8140e00010b201900d12640014414140600c540902a492039080b240100150078400c5042d43d50071403a44014203020702130103034100842c06500b03c0703903041f01989107080da2840c1c92661040d0100d55034555801c13a100701c01128002d00100e0298095406003c140c0c0d100da843c2c448404914284a090310900384400085041d80d0a100c9003500d0b84100c0c090790500c0c1d9200c1c505814050300000d190420b40184d417052214400003540424403159482d002010301c03881ea00e6070b0401c410301a12014641c0304520503240c08070388080c0070800d615144c401d0362000708101d5644c4e000903002d65030b40d0381c410f50014058201c40480044140c2c8920700c3e04400e840d0180d03400391a40c000c40e4030f42e0310a0308a500441d072030309620420107074441c400891040f4203191843c0040305401028108281a203110104980003142d800030002096001088507121030348144940d0038 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 824998893 1250 824997643 824997731
    0x50102120c19030b03030a18080a050d021005010501090e06040e010f0e0616020d14071a0f0703200a020a050304060809160e0c07081c020a030612080a03 67
    0x84006504000c0c140c02c0464140382500070320840b81c81e200c0c050040e5184c214105803c4410030740c2000c80e02e0089400e240040f8400c8001c110f07038040c0d10302c0785000301070480426030003914248103001000440c60070540141300a9910501c00e03001c0b54554502d174080e5446040000300507160706240a0003e6203030820100361410769070420800035000c2d900303945150701e82d000940c40e13881c902c0d0460009640b1a0b181c0d802d10f98030071b403148060740382e40a038114204081651024581800c035422030302c03080504824809180316a0b42d0485d00040c040c1000c1060182903645541160180481240d0008010584600a5009004040324554080103a81e519900d61034054207082003500d040d203061040b10b210402c1c043c95002500162400707901d200b034107a541c420a0b000140e00958088031400c500340201c0154010001c14112a111000e00c090b031100018400101203d405900c110303140c8212804407008502d0101c2200c801011a28000c0790301d110281a80e8002140e030514042c60b2480052000540341e = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 825000000 1107 824998893 824998897
    0x507150f061d13022205040b06010f020a03110313030b0906010e071b1e05010609110a1704030309080d0b01080604020304051519060b0c100e030d0207050102120c 71
    0x2045c40c021801243c40c075a0019211003510b03075041c0000c202d168007503150300402c2031912035800500303640000c0da2241803240182c11b0101e40c0020250182081c01107501040009040c0041a1364170701c0e0031244c4a8044903060a80c2c0030301c1001041561035014403900501c0e556845404080340524510f80c44441001c04681c00c0e101100009001c002908080c11450302810001461038500301d60202030301d04104500c1d8110b0340c100404001d15400074000b015480710000300c40324035907484c9400d90040c0544a00505005008250007240c60181c0d0813084c0090b1303007a6214400380d219541130000368082a200188a40c01c0350150b0b5003514100403e856101c241c0c8409103c52850b44001030742140d0a80d046410040c40004500d84d141504010440418101c00c10411000c0c191140040e00d0740921000000056000035400e414130109405403100308610803810005402c005481529035 = true := by decide +kernel

theorem cover : BRFrame.Cov 824820143 825000000 := by
  have h0 := BRFrame.cov_init 824820143
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824820143 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824820143 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824820143 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824820143 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824820143 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824820143 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824820143 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824820143 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824820143 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824820143 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824820143 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824820143 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824820143 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824820143 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824820143 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824820143 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824820143 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824820143 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824820143 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824820143 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824820143 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824820143 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824820143 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824820143 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824820143 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824820143 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824820143 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824820143 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824820143 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824820143 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824820143 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824820143 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824820143 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824820143 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824820143 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824820143 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824820143 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824820143 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824820143 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824820143 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824820143 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824820143 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824820143 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824820143 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824820143 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824820143 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824820143 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824820143 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824820143 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824820143 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824820143 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824820143 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824820143 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824820143 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824820143 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824820143 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824820143 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824820143 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824820143 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824820143 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824820143 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824820143 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824820143 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824820143 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824820143 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824820143 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824820143 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824820143 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824820143 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824820143 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824820143 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824820143 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824820143 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824820143 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824820143 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824820143 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824820143 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824820143 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824820143 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824820143 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824820143 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824820143 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824820143 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824820143 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824820143 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824820143 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824820143 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824820143 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824820143 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824820143 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824820143 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824820143 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824820143 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824820143 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824820143 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824820143 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824820143 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824820143 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824820143 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824820143 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824820143 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824820143 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824820143 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824820143 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824820143 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824820143 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824820143 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824820143 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824820143 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824820143 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824820143 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824820143 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824820143 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824820143 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824820143 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824820143 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824820143 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824820143 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824820143 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824820143 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824820143 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824820143 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824820143 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824820143 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824820143 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824820143 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824820143 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824820143 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824820143 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824820143 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824820143 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824820143 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824820143 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824820143 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824820143 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824820143 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824820143 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824820143 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824820143 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824820143 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824820143 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824820143 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824820143 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 824820143 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 824820143 ≤ n) (h2 : n < 825000000) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
