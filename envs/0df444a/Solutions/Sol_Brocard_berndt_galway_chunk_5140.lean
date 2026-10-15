-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5140
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:52:54.795978+00:00
-- url     : https://prove2.me/submissions/b874430e-cd32-4385-a193-3219765edbc8

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 924280575 ≤ n < 924460431 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 924281825 1250 924280575 924280583
    0x30b0103170c0316050a0b040b0105010e0618042703031a0613050906190b040503060f01030b040b040807080c07031103030408071208190e090a05131b0f080a 69
    0x14046103400700c00540403203a0a4540300021490510456002040c6030101181211a40900030803103001c2504803907400c1c0254001c010000241d4505800501020300030103900d4080c1a090101880380100c4054080d601c031f0040d41c01041540405840700d00d10702c605041101d00081c103501001c14180d041c0d000003651130818541600c0d48024004110260044100b082e5003016200014406420078400107908141d0160500c010a003418504034070411060300120701080c4046010000d52400b04265908984041400301e03041d4155101c0400c140c000400180030824031380003182c2001141c0d4210740c000c1740c001200644400c0b100001e00c4d254403a610060703a0724000c0d807140031161318020085400303d8a520b80105001403074024440741d40744c02c070502903944800074050b19200d40031108100e600c21003550744052030740d0360b0b038020040b200b18003604036080c59140804102c7c640c40711014850050ba0030100c80c1008041e0380088281550b05904201e480710680c1e480010000700025152181500c9 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 924283075 1250 924281825 924281843
    0x106030b3f010c081005220203130f050606010809010203160e060408010501060f08011a0414030a0219030b010803090307030212010b03030a0915030b060315040b0a030b0103 76
    0x18550400410141410350440111800c80303025008880c030544600382400c03211869002645209241c0342101c00081007000071649a60402800d48481042031028040c00c40700c808012451025a941c9074480e070a003070389582c1e800804540c0550607084401c0a03a50301c42406002d10400b89403094a80f00c0c25910103012448200220f1025101802a40d108400c500c9281900404414044900c035003000d81144d00000c040001003100c032028050140a80065283d1640003e980c2d80002d08026050b4483c0b200302030105442400d02c49640100d030202c0340b03078001204e4154140c01c0028141042e9000c020361058984240540e070b01e00300341c03502007120b01501c07045a6680c1d0710382c4d2040c0c03244580b003030640d4550410710082c00103140001c0c0d94100b0080880000504251450200380703541d00c01e00b16503002c545000e0701080040c04420401140c000c0381e19041c0030000d508000f00700305000c05080901a10103400b01585642c4403640031141d02c1000410b1846010ba4030b00b000c01501c0d00c2030005843e5012 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 924284325 1250 924283075 924283091
    0x60e060111190221030910051806032e140406030c05060f040f060e0f040e0c1c02090f1015020a080307110102071b05010e0d0b22030503010603 63
    0x809440303065500104040684004605840d9844001c80018001c0340d00501d41120780c13a00c3c44240b0503980700341c800c960045a40c2c107180700802c8600320900601004006c001c00c250312040300264040000c0d0301050360099142d4880b5150074410455800710910358a42d2404691852210710030102c0c00c45200c2d068141a945402c01417000340d032110b0202902c0c008000c0c400700414240000240358082020a0450420751640d41700e21a8081550051001901c08000c100491403d100c101040100803a4208114a80d83c440c00703803600015548030707220b610101391464100d28081c205152140c1d004288070094949035503448150340e4140c070001d0109101c120003190300c5400a44900c0800801d170000c103c1c4880642c0c4000b203680c0010180b4041040e130003440311041c042400a41500d0b031040154802e07280e1900c1d002046110580d00032170400002e16251031403610340303038981d402468000e0303a1307841c203540c40c134800a08200e00e13a10106085503038080840e043c194000080c41c142d5041c0c1e5800d10041c5 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 924285575 1250 924284325 924284327
    0x5041b03060501183012022406040c0201020409020708032415090a2402060f130f020303070b040c030b0114060f0c01060515120f01030f020105130e0a060e0601 70
    0x14407541380e51400c2c122100c400d1054100f583c1c1d844400c14101e8144200c0c620885d803200756542d480c1541202e1070012400c24150707064051100e01c120406c104200300c511018100d080c0360800020f89002d000c0e83d501d14220a5240c802c1d0116400381440750010b560740c1d54a0719102c005540111344692900380324043c068805d070040040480326240041401c0e41c028003c840b05401a801502315691001c1000c40000c1c5004010705a40415101001144454401402c0c0a402c00800070030707451071110201d00308041c000141c011240801d40015a041c2e1460040c40400d2440c45010005448001300e0000c020804c107814584500340ca00c40c1c205170b021a40ea40700000c242d8071b40380f20324a074400810300072986c503815201d014191a0704500e00110390300d0b9039100403598201400c082d04400160010303ea1101e12510750350550403004041c00c1011940c51901c61241c510100100241000000540c4e007081c2052010b001001d051a5240d0141a080c1201a5001012680315010515940100051143d = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 924286825 1250 924285575 924285587
    0x30c1707090e06160509040603030503011403061b0a0c0605010e01080d0e010f0e0d0f08181503010b0a0216120c0806040b0f0a09080c060103020a08070803040b1305041b03060501 78
    0x1482c00c030042205072542091121400304009813902088403d110028081d940d6000f0034000714000c1d15900d0781c81d410650110b005104000d24940030b07030710500a100030418040f406d2a0100f41c4050241d445207100c0390704903070444145001804035410000040782283310700080d2030407078a82e14115004020480e1050320104600c1000c940854038200100b100e0b98043c8010b0090346800a0501582000540c0c80000c01c500c0e0420990303d0380c03004600300d1000c2c0c5403045011040c0d58102d60b03000103800240c1191503144414010a03400303130000300701c56400e03600800101c1821079655110700300b03481d11652003100c0040145c00c01e5840c0340c00b03241c0c002591207000c01c20901854021460040c1e55681c1703c54090040005015021140c2d590200c007000f02d420b4a01408182e10110b01604280d4511300401030301c00d585802800e507641010108126a48000080314220f40e440c0750350a0f1111381e00f06800d0540c00c4c2c05e6001541246c1407216000311140c10791a16542c11030162000c02100f5180e000440e01 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 924288075 1250 924286825 924286841
    0x3051806040e07080106180b0307091805010e090106080709020c19050d03150b0904200706092105030a2c0109060c08010f0501050d320114010f18030c170709 69
    0x2002800200502008231000025584050f80e81444215566034541c44022413005000c0d610166598000600c103180780d041c17010313401c03640c2100244103080c2080c060584540c40c9208880d05144d0004944180d4041803090381c0020126401008181d0034508040303840358956280c0000180c9070260b00780404060030120340503500740041c06420184240c062100800501d01003400c2480d44003000130540510400074604180304643c0403805204500d4211466101c94002d00e4003921b0019144040d99440300c1513a6018980c05804940880c140d001451a040030341615403810b4016440441c0380307001500124840f511890742040681c480840c100c4a0300341c00c0c003582c0e40002d0122801c000c82d40c8070300043e110900300410001404e5602c1400901c00c1d0f00e0200302c4c15014191090300c5440d05800608840c01020310b80100c130401c00c2400002001c0300b040d1440c550502018620302d000401110f040c40c0045e607030144048007016114440720030001c2900d41c0f00718080c07040142c085003510030303800b41d118 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 924289325 1250 924288075 924288107
    0x10080f100c26040c0305030301171b030d1202070206030a09030f08190c030f0606090e130f02040507020f0d02160f030b011703070c0905220f03051806040e07080106 72
    0x80b4101c2c2e0440503100c0e000050002e80d1180201440800814428401513000301412101103000301d000890285c1040080c806010034903030038944406140d24041385103030815009241a8000d00a40303032960340280103094010390031405c04400c0200d030b250298424110240030751070300b00300c0207403044044904d801d08565003213562411156690100d02c0e240c00c194141c041c0c504000c030b880800d201d04217044a00d039620920010307031044410041804c030b292415400411440245090900c00d403034440c803041040000078015656040083ca40302d10a10082c03030115000029211a20050000259610404041e8100d116420800000c50380d04c01d04966089a0303015103100d1840e032034002914000e400105595070b1501040041c000001c1055010030003401d280350000409042c2110001d61030340100702c401d034219440b8501c600219400321142c0c0281541850261394a000007401406059200c045a40e0071038070100e00422010094441580320305250342c0d4685e40ca80c1d0383c102c102c44070500c10040c99 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 924290575 1250 924289325 924289367
    0x20409051617070e2e020f0a0f14030d051023060705070b0301171504020619032012150a0603390e0a060e01030510080f100c 55
    0x1141e078a8244203e620036414146a2050b00541e004a140c601070041904501010071520604000c00420014031860300b910050043d0500c04201556683c00124054508210a505c80d02001a22400212841548400d0341d403103480088444010788001d0b100d2120400400700d000c01c800e20b40c14124031268000c1d0340003102d6502e2083c140001030744019070903100c600801501044d208003202c019070080800f01383e240113503241c44002a042000380d007190100090480706210250f139600060340c54407107070307500d02d5949261351001c1078000f420300032104200c0741050003d50300d05405200103031658480301044080c15a40b411500c503940d40c0074480d480c0d8002e2200b401404164441e601c442d00c8104400920510015401c1c0b00f41c0d855042c0b540403140c0e9a078403110342444191720a441c940c111405a0355051840d003850b0018029542c0007540a040580e00c074001212041034981400042003144140ca07084910a80c905440c0e400a15a042102c0c1c14109880c001c9032084820614503040700b8414 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 924291825 1250 924290575 924290597
    0xb09030106080115031e441207021507030c1d010503180127030e0a0503031b12072a0503030301140d0c0e330f030f0d030204090516 58
    0x60301090f503506e8079100440c115002c0c200005c1c5903600c1a00e60320b0324180007080c0a1502206403070b42604d200c0c07451500340c54464080c40c03c040b24881610480320060080c01686d13514403108905d8484602051400d81320700a0a01c00011b4240d0f00c4840d454583d17640e98250ae01c001c080241c2002503802c18580018801c100144050f840311110071402d42141001080081c414a400014243c402c0e048140c88120605002c0c04c05411014080118000303407100586545170400103903c1e801001c5c510307021102d81842c0018a414184440a4094400d44086440c0c0c0c1d0907050501040c00c05c2c43c000d00d968905841c50034041e0021031091411102c0080c0198030b16800c02e090042c01c81d04012000c0c3d0450302c24881c4c2800036458003024006081c18010000c01850200ca0441d0030300041602a5040b071216581c83d25502c20060400f400101c042d00c0000c80c9012241c0800c0c40c214601c3d075001042d02a64040300035055054009000720349201d5014051038590b0004188604c6582040303101042c001190 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 924293075 1250 924291825 924291833
    0x60305060a03241509051503061603180f1719030c0504030f05010c02010b0111071a040815250c0611130f030512120103140a06060b0903010608011503 66
    0x1001c0e21264000440d0100c0c242010010b020364030a0310240c1d0940d64020401d0140c5d841034441c0f154461121824051140d038201d0101e510380c003024100540080300300c2c640c2d81d0950301035081441081c4040240341801d07013550174a0000a000b8840c101e680c2003003841e0b181e001c10500f4080d01c00f4030005c0c0c6241d184159102c0d40550042c81c400f42d18800380a405e02000000c80d0341c004030419014080c000108032086803007002801c44010340da01074180540c0c0705c075083d001040080c105058410820f02140300e00341171001d25640c0c0c007690784990041d01c10200d040318084841c904840c050822404081403034042c801b1004844000011034100080340840e10a000c070720550002038100311240400da00e030180c08007500e40807490941004081e40060300c42042000420480300358410302d030004080c00d003c1d1203854a0440441031201030045184826500d20402060108e40202e5074813800421009903201030b0740020741c0203880214403c0d4a002c000203105034040c080c101c012180701d031702c42c0c50031801c680d9 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 924294325 1250 924293075 924293093
    0x70906050d0917040315110301210606050d0f0515060105071211070b071707020f01110321040203210f071a01080606120c010518010c0204061e060305060a03 69
    0x382610072006600c01c1c0254404103c00810107103003c3d90007003000321810011030782a1074020461480c94601040104051012005801c80600b404040b0000d1048141001000f42402ea00020b60004100658a0800452541030090f59204805403150510390003040e080800b002c0306c0d2280032039810020741d000140d0308558088003030641e060051160340043c00307561405c1190b0300040d1015000191100600c0804a0141c01c03034502a81194a03146855022481901240029505220601c101041c2031030040c0f0903030703042100500c1c161f540d5a44404010441c02410ba9050340207000d00c0d5041030352903810030041c0b440350302c41658180c0b0340041c09082d003140398401b01d015940300e5881b0382d140040d03008410241c0e00030000c042c010b02780e6080280030460b01d0128800840c0c0139905c1400144042c0e60007006a40d041103418034403000c00b0007c02c0068400c90b1070b2000080d805490004041640219034111501010441040580c11902c0c3c96050b8210f9400b6030724142e100160341000c00004030240 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 924295575 1250 924294325 924294341
    0x100c05100b1206040825020d03030506010c061404060c11070510020c031506092811040b070308040b090a05070e061f0201061509060806150f120f070906050d 69
    0x5441401801e00310402e2500780941600d08480b001c40025654100485e00d048078000440340c6400e511052403203500140304079800000003400d15413140000b84890b0702920a00640a130040300610003905504040b10a0b50404c5404a40c03a51900414081d180d07c24841c0b01e01d40c1c0d8580000f05200da00700700c200200070400480c144114800c0d00002c9405403000d101ea1650030084040e04449410031400b0800403020061061503903143c042550004a4080700d8502508031481c40c00054904281054800d2031050341c022259580b00025002c04041e4040750081c4980e0083c3c00040b240d071500404240c503420014009003051348110350602100c000c509465412002c000c00030984203000c09030031500030a512a0705030150750748102c00c002c0315200c240140800411841e107449820704045000c2c20752800070b4500c81c010318a14804001c101c0c0804111140d041104400d01d44a4540402144c50b000c400c03524200d8403160140422a41401980002c09031186070f2196410311925104500003400700e0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 924296825 1250 924295575 924295579
    0x4060e040e0c0310060e0714120a0605120f0c010815013c0816121a0603011517090304050105030903040906030b04020306070807050910030f0c0e100c05100b 69
    0x142d18100c15030381080304603001141050085101c45c942000d0700351000303009101030188014402c50400e40d6070b42004603030310a6941c100301c0c101511012a40e10041105030080317a000f10700c954040136005000101e114409110f00704560041d401c9500460321604156400d4100c02c0829134802d2056024058040030300c603007550102002031000700c8a0841d81190005983c0c0c02070808a0580320a5114003403550044425006087c0c40c183c0d44001007640d100c4808040c20199609100045140c200207181e942e40c10050080780c072541c50b90001060440c0b07411120f00890361480c110410307083c603d482c551060440e000510306180c84c2c40d0041d50158001440001c0c01e0000700804a52034070584541400b860185400d80003e240500c14545044000b82800701406108804c00440f650f118044130481c030b03820388001c590701e40c070014103401400801846c00341041c2080942001e066000007083d01c2603004407210003801005080c2a10780f03180c04800500580c111040b29000040706402c48602c0d1800 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 924298075 1250 924296825 924296833
    0x30f0f0e0603180d05031003030c0f0507080d0323040308061809010504031103091e040905010f05090c0603010e0a2003041209090606051204051204031b0b04060e040e 73
    0x801400034001e64000c0300c400f40f00e86444820604466010041e294030f0805a00780145141400100b590fa504802d00c001030411500c1c41c500700410140108041501d5402070440e207515444200f0700d07440c2c0b5400340192000a24089030300b18010321030190307041805011007911041d5221500d04807809040208101e4200e422620703021241c0c0e80c42c404c007502c50308054000043c64203280c94010421401402801e806500522005440365611001c21100628a6035490480d401403004280a41450035001d00300f5403825805040c05c080503001203216442d0801650f901e54205002c11120380020b01230540700d40f080070006000e112559021864884442c01c40280e05d004031040b80d06070342d0044034101c5220710b60941d65221283c01c11289009486424004e220369810310760000c160b0302031b4001c8441c2c00c1c840c040204062001c280007026256440d106a140d0f20364807424510b401c4010070465070654171610000042a110050a1f01c0039a605903840020740402101040081d0010014010560103 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 924299325 1250 924298075 924298097
    0xd060c031503030513230f040e0a141510060804020a15120b04020406052a0a0309150306050109050607050c060a090f0503010c05310f031e030f0f 64
    0x1d10403400000350b20940c1c44903614480d0480254001c038090740448401c008000016881083ca0040d05a11110941d10031001d0001500041c000c3c0c0400745c956845802501c0c3c40d0420700070545000280000110112080c0518403104510b074400121107884841651303d030b0620016214204142c0c000340028883c4420f141c5440c0500312944551004802045461503005807810542c01503d00700c1d8012107046003410715192015003207110b420b80c609140341480300306c1e5044285201c0302a44440041045030142e024910340a00a11081d000d00c0c413015241c645030350400c0303209025000547e0340680d14015410b103000c05001c0d164002c0c1d60210380070701036400299100c1d2240760282070000f4036550340211982c503050040c200003c003608202d010b40d050400b0094259044011141203d01c405418512086880800c90303001071010903501c0302070649030000410030882c2280005a03401031411101740712456002e0b0341b090801c00c0004001c80c85280b46070329958016003070866501e80e54141148800 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 924300575 1250 924299325 924299351
    0x50408060f06100e0f0d0311070f06080a0902031b01230a091a1b0a0807080d0606020c0310150e131202060f01090207030908061306050c07020d060c03 66
    0x211007211081140d00e922410000d05107810310191520000d0340c10820080564070003c15000d2003001030580c040c040031444c1404040c4210a14a449000d010649069680b502d481165a60051145400041c175039800300342060540d1050100b140e5000340100368211003130840980344015050018103110180c8001509414640c401090608800c00200d58a44407040701408000041c1c0040862031001a40c400100720081c0888108034200e00028031955513052407189000c189420040c551440810301504100401014200011045509008081d01c68504076510f440380009141d050b4060701c0c0d1004401160350049114031007503902004030a03144e0090b03003580c10040d554090b01c0407845540348140843c90150140b54403152000d4115810031100c0254a2101801015001540010003004050003600440b0003000b404040d1192450403003c040180c2401e0f1005458090802c0000f230b9400bd10a800c8850003940100711000c2403c40b80c4a400080c890880c11005040c0c0d103800216041c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 924301825 1250 924300575 924300583
    0xb011b0b01062012030a15080703060609020703051b0f0708031b010c09061116060e100e031207171b0d0302030411090a0b06220509160c03050408 64
    0x6540681034280d0203514200c0d000704102000d5241c040041c1003842c1a8264040100e8101e860400c0c40080684075192804031038002d28150200744030000100c9800a00d445001c600740040b40e024080c01c0200c0f596511411041c4d01c1248001400668100911104840c4201c00d1603940f55140d4212401a640010110700d80205074000e101c0990001c1210f41000744018481d0340c1200c0d81000a100e82c1c020540090080003203805030700140082c180d4010307000402041003412490711400c0d5030107040d40c0c41c2000707842d448101948a000302c28403c181003c16000c0c074940140d854010780245488280702c801c402250f00009000c0300c8140c20301c44141d2083c45100050000c08101d40e400641c01000700d40c54500d00090301c40d8040a1500600800c000301c2d200940c1c0c5840f50f582555685410741e92001804001d005010790607030b0011011400501c0e8100031521000d07105040b140300481c042c5c5a00c1081802401160140700c0350340d210300c2c0f840a2030f2107105003d503068402d0605608294941d2852410 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 924303075 1250 924301825 924301877
    0xf1b030c0b07091a0408120f1911010c0c03140702060702060a08060109080c09040201030c111006140d08030a091518170304121422080706050c100b01 66
    0x54000c0000740440c810111812030070100074030f604e51804e890b203918961144190300c4414109070000c031300401c8000c111011640240b100688070042280d103114041c0c096031401c150450035603c2c0001d1100a10300950500541a801d511080440a490341d0320140070350100a08031f03003080041c4900d02c0103803500f4025106072a9681c854840c98640b031400109400c4081d03000800682c020429100c441d2600e8121540003a02880d0120b24003082d0780c815540000421340c40511441040c10301900c1c107041e54080c0b8241c0714400a180003040c0507000708001c038038040d5009407458404102040ca04e00d0280e20012005102c0c841039560400d44a015104440100b40c0512001032007018501c200030f03d0342c1c0692014031a4082060450501d84c0300c1c005c04000410f00b58090004e412844100401d02c807055480000e100e099698080400c1c0c6181c4100c0200ea00c900c014a104d40023000c030380c440c040c00036282c0c0000f490000b001c40026468000001d044104c45450601c14982c040440380106200706001c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 924304325 1250 924303075 924303077
    0x51009020c0c12060f040b0c0403020d0c0f170c0d050c06030705030118020412150e0d020f060a1107080306060412050102180102030316031104151e0f1b030c0b07 71
    0x900001920203000f6070260340e00c00e031041d0350010410003003038910201c040d0760082d030032100010495540c1c49400714180f14603000039500a1201200004129180c62680182d80c0b901c98030701480d035030301c41140c20503004070350100c17109802010000002d42807041410780d015002c0c4049035407980d035007004290550300c26640000050000001440050180c9006090703081c10305004601e407a261600b1440070741e0000300020f10b200205078900c904164582c100a9106d20218141c0360b4642e80c0d103001031765403070742d4440e04001070050300001354810f02d8900c103504060090042651400b5104c2d9101d29040d40010040382c0d10110500002c103102609a6590491f14450400183d40d00c40328140a04e9030304030b80795028115031081013000742d2110304202417083e01e2214100401c07110744c8440d60340c806001e01d130000c01d596454003040002807070703202c50407001012a0100c2c260581510a40c00c40c0c124248410307100200d6800811084020500305665410500a2400b0913000600380d030766030001c51065035160 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 924305575 1250 924304325 924304333
    0x7170c0307060c050901080a0e0a05120702010e0301050402150c01060e0a06031109010506040b1303051b19030507030b090115030b07031a1f1b061b05120109051009020c 74
    0x1802c0101511680240490500b003490824140700d0009042c044000c109009023602c42c84040e00c803100410140104030b40c45015034001106041d6100c449402c0400180d001425107000501181810320645005603005862850100d524803508a490782c42100c10b0945503503500b100084601c91203103054003500c5008000b041203451030415113405504400424440d940aa00400207030f5903200444040b2082d02e003445488040d103541001d405a10355101a240340140b0310614020b40d000b11802212000440b0145154441d840c21980400c0c100d0200904c05d9001140c00d101080c0e0140d001390f4814404000811a03800484519803002c601c0d5008075a00c441010500072019094014001c0d211200380d415880c066503000020101c0c6082c00207100446100e1181c1e4103507910a4021001a01d6440c3c1403051908852610030018400084240700340d00030b208906825602c01c504882c4004100e1450690302e034280044500100300103082c1034041d450fa0303000001c1c426042e0001e0000315035a41c02030 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 924306825 1250 924305575 924305587
    0x5060d090f1209061106151201060801020d02030a1515030504020f030d0305070807020a201908060a0605042a1101091104111c02090f09010b0d15060905010507170c03 73
    0xa00500e043d80702c0503166070400010084587c81c102c00541c5d8101c07040754070a00c84400e4039a50703401800d090700805455400062403031050403d0380c00450298060250400c5030002c11044918619040d0240b418000200031134030304014071a401094000d400100043d40600c0c0840000c2e00d0500e05403450f07030129031280c0c01c004d00036800103c11030b071120700c0740080c0c05c41d40f845a407a603410201c0c0680001d2041c140304801150350711030303401100c0c801c800c9030311407a0100c1d1100b40307103942d60303008488865200d82880701c003140c5070800c2c0c0a0700c0601d0025409044036100d10600380000911a800c4a10411000080e20b00c40140309000c0e503090780303009070402c040041031041400300740c0b0190055650165020000f100b011100100036200c5e24110a800603115402100090710001100014070760040000b000441d4440c02007001b4100690482d004026400b003c0c3d0380860214050311600c00411000c0d0800c00c8294003810081112510030300c04841141c020050a282640040084605aa1010642c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 924308075 1250 924306825 924306827
    0x30b010237060b090903190914060c0f011802011d0901060f020304151e170a18020303030405070f09140a020a20031c020405060d090f120906 62
    0x7a820010500a200485039407542032101080352064122061100000800c80034801c095001400100006000030000d0410140d029500d802044a9202c140204544000001c1c00342d40030b101112492141101c3c60320940c400c001d03440d0004911204140950034000e848001b003803180c42055000c240c001208000a8000144680c0c022030030386109101000d141c2e002c9507508944603046401d149040600c2c0c0740c111000f00d045000d40d038000c00c5c2e00203040384110a500c1e0029a2003a012034400d0902908001c02802116841c3e4020381c10034203182c4800210310000c1554120b45103e100d1040100701d022403580c046880d40d8800c13070f02aa0660005182440004100e400302002409808001c0c850803600700c0a0700207501c00548004500d41d8001080310380380307000340045c0b80e1154071030620324402c07008982031302c0d183d80c458202c440c43e501450321180b561031002d10035582a00c1011b0000d40c2403030000c00240008001c1034005887c40d0044400f510000740464144042090840c1d486d86030070313403501c88 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 924309325 1250 924308075 924308083
    0x8060a0c0e220b1c020420030106030207210905040e0a0804030503040518100e041e0308160c050304050d03140711212e06141c17030a0209090403030b0102 68
    0x1014501c0344ca2008052200030f40040358120086804503030028003a000d0306803c0e107030f4002c81d002002c009940480001042e40e0564080c05925004110329100c9002d04030807400c4100e807441c038504c04104040ba0a00c41420f10f94890344081c5182401c4540b41c8480c1c0c2c4a20319140c2040d40f04407080d40c80000c00f4012820000b2005180441680500c1075a05084101211607403142c01091680e8200b04e0004090010144184040044041e4452910f0402d41401446100110707110b0300555180d488442c121803080c035030303080d4454101014605080c20310041012420002e60194208000d08000e005500c1c2c0c29401800711380d103e800200d2580701c01009105c1c05405200c1e103440c0440c08011070310151100440c000e001107801c070131809580380b41408284000510554160303521440c2481c007140422403d5000d820744081200e807a86d0b00492001414074500c04000001c0030351090288529200440c1c0700659008402c40078058105404140802c00740c0c80201e605900080d00c0d02100c50340707560140 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 924310575 1250 924309325 924309341
    0x4050409051c080f010905090106051c03031b020a17040308120906010f05060702060715060914162307080d091b0303050a0e0307090608030703080a0608060a0c0e22 72
    0x420310843c58a8829400c03a00000c0510945040300d03201c0c0300041c1801e5003948540d000d04002006c0c1044000b08680e01d0501c0310b10010114003003072a00390307403000302d405650000c00004444c1e8000d02e030301202503541d802403006400039201e0580e400d00001c40026258805041c061440f5581e42d8040d00d00360380d420303150400c10381c04070428100d00c030414840d80d100c0804507001c1a4050364030304d03074400c10391034100d502607260b02002580c2d5181140c04150101203810240005508581c00440c58482a000c2a15240c0002c0248007007040c0140850a0942642d05050948d608210b52230500c880ba80303a14a0320f6102c410100d007140d40d101c1500040004660002100041c03900b11003060340c3c25075074040c00c2441540c0b001020700c072000844000f03d40c2d0412450001d4164800240310781580c03002507964a401286084002c0788910300069104c501c3c0c0e1049800300c07004032008140c9a12010343d00c0c8000c0182c84448010400c0c1c83d4074121107510360748449014000c03481c603201c0d138000a04401008450041d = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 924311825 1250 924310575 924310577
    0x170c040303171512010501090c021b010309050a1b24171f080601030201030e211c020a0903110f060d2304320312040804050409051c 58
    0x240000e00129074029100d0020030b007400403061190b190071980c0070414060021a6600c00300b03100c50610708050641056040360650305090148140d46942640c0b47c0c914442c4920800a0b51000d01c8100c0d80309030415078006001d9410340303880c40482e407640801c155807105403040310740e070100d0300700808070340b0780f1041c51201c0401010820420b403502d802040d0310900240071507102d40c59000301380d003800c00b405d01d5a000144400480402e90f5528042c50b22210240705c140c1c0440c0c0307010303003000704107101003542c0c0d40421441c609600360f1007081e0b044c01d03001e4103c4100c044482d843c080d851071241d007140c40102010b0136103441d1104182d1562420701d070440284000030340186010000340740c0944130340c41520a045040310340070802d18a440401d881e48081c40c403410100c1705102040c4000c0c044c1440b503001d240007904412035843d00c85c80c90044080031010b9140314055204000c004036080800c0b811a8015110310125881c240e80e0f40002001c4d0b4503a5001519244c00009480c2c0c24007046d100d030300000b0070705 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 924313075 1250 924311825 924311827
    0x52a06060d0f03030b0604120501240b120a090602041d0709080717010e03040308031806010b0f070c08010c020708060a0b0603070c0309030c0b030619030b0c0702010207080d170c 78
    0x18550b0341802092108200409143c0c5811400d40540e4900090300c0241c058100314147d02c000f1400e00a001c2d04407451030907045018541d0220b00f05031040409000d4030030740c9111516110740440d045121407002802140c5681c1e658130b0000004006000800c0104102c075281d040d00e01c0f5007030038003c0e48040505201d00380600c05034100006031303021800750221000b06441c030320210184084140502001041c03201280400203010003044400c01c042d6010b8030614808072200940e50302510303a202001e024501d000c0a044c08401f90140c0884020b003c2140300f44030022030591355485640c20760303401d68842e00242e04155400d022030601000000ea1040500303200303008090b0910302041c3d8500c40604241c003001139241c80c030f1040c5805801c441000b55409082d501b0300325a80d040741c800365001030300c01034412a2455a00c4501080c00b8920f041500e8208a880c00750340c54002c000080d561000504a0640c02028000030710584144a910b040c0302690712140c0300009a51061045103800909640200390 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 924314325 1250 924313075 924313099
    0x10090f0e0d0e0d0605010312111603170c070801050a0e030315011407170d1406010e091902040b2a07060f210f06090605090610052a0606 60
    0x58002004101c184141c200300c00700d52068000700d9400b400207940034000c0750800c40000100803000c0440c0341c9101e03140d542c601d60752002040c0580c5442c5a81224101c090000b00c0c240003042c41e5407001c031829080d115140c0d10b8621100b484a0900e9081c0d40130303070610b966401c1001100d20540c015150103084010240d841c42c030300441004440799a20318048d0410081403524003890b4070440856413003a0700450b642d50140f45000d0700e1320807540442c42d885146414441c0790114200c1c00603985019207016180c60045080c24800c1c400d0726600101004203a0641039100c6500a12038030091000e4446202860303aa010100d03d012034410107104030b407040d0030010b45423404014000c110030b41524090310703100d42c0c6180240022114607042c2000249400c04482c038074000105950f01c00404200700203001e0050f555030b40d144c1c408449240c800c00e80c0001640d0b0000f41d84d81383c10300038414001c00030304081c1d06003003c81d42441039240580c4803903036684030142c000040c0000100142c43d4091401c940c0080550 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 924315575 1250 924314325 924314351
    0xb0603060705070c1517130c05060705061302042d060b0903030a081e0702060405010f1b03021b01150e1005010e0415081606080108062a07020910090f 66
    0x4407040c800d17550380302c0000e103c80039894400c0340207502070800c10300d0400a03402c00d6070b0040d01d491901c9404460b0140c074008000350340c1c10080107407200983c0107400f420080d510103203841e0f08000c040780300b01d070f016035286070725403514170061750100c02d800c445150100300703148442c884022030b299500460f058507410301404855580c000103e0341c4540207490984900c0c1c07203943d10f103100929080003140307030019070904000343c20785c1c0082e8041c4554041c8009102050004444008951140626500f1214040300a414050290f0000d0010008018001000c041381d00715841c00c4030b50381c402c402c0360101c1c1d107082049901e40081c2d0317460b00907040f896212034441c41e00d00040e044020848689000e95100c0c03800511510b4001104401410b0000651300721008421180c1240b050707074000d110115282100119048400145007803045080324107540401c0d910088944185c0040e500a2000181c200700250068862241c0180a080e62800340040c0a00f002060816501758200c1c0d2800341e842e0607090707082c41c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 924316825 1250 924315575 924315593
    0x5040603020f010c0f02100f0f080103051c050c0f0c030d050f040e0402130c0e03010c09080a0201230a0309030e0910031104020c0105130605060d15050c160b060306070507 75
    0x1030030003400d12240340c02c090f1a1022502c030781da00020394400e0340c060a91401d960423000b503c420180c165a11000030000701010740d02d044083c04098401d9212500414400918000c00340e20300d0703d6410183d04211100c030026241101d880341c444565008110035021500301040441d4141640c0d062132428606201784070960f501840c4103488500c0c00d921302090a6481c0c045903442c076000140428490490b5400001c4d007018000340f2071034081d600e401e030506186440f8035600c806a48940300580300000f025001124006960b81400d40300d201860806086a500c000003080b80c04403079280803485035003504010b009000c840c0e21040c050800c5404014254038007066a2095a61041e8a042008114804100240124096010705603c2c04043c84920440000d41c039120350300c107601c184070716501c2e00b043c0005900501c4006098072103c4607801543c052a40105030300c1601810601d0528a407041405040003520340c1c00c2da00202e41e0002c1c0221418144942035012449051081c9860b00b196079540310 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 924318075 1250 924316825 924316849
    0x70e010f061d13020310171203011509080f240708130302161202030106080f120c01090b0c0d050f06060d020304020a12080301080613200d0501110a02070504060302 72
    0x112684468505419070f108041c02400714241c0000b1900da1522810008241c616401000c00080a011400d0565600081e40502004183e12020304592a20080e400c24480c09220201403081d1401c021401c40010807444003c42809002440075004e0103010301110004142c40070300d5400030390b0030845096000341540b40c011841a1381d01c1580c1c00c3e5402e003241480306848940005c141c001e440040c00c8000c01c550080310318021002004100e0f60751110994803044105901c5d415042900120702010102000c0e0084001d82c2002044006840e514444460021140385000040c0414090345035441845003980c02112141e800c1c145080c0040050b10728000c030801c9074826900000042d0440d1623013070034100100503007144a51022200c1c0f4004016400034090b503a400c0c400c0100145440c82101256180b030b40d0000e0724451490b80801d100a241d103134414405400040040ea0500000d41c24840c1d1050200340200345a15410314840c0241004401c0c0d000522490a048061015940b04000e4480d = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 924319325 1250 924318075 924318107
    0x60307080c070201020a050d020d14090d03180e04030527060409021b0a0c0510050703050909070e220b0102030408060c1c061202090703050f150f0909070e010f06 71
    0x901d0710b0741c1d440101d151944011004040e4010b403640c4c50300d42c1c3d40000360690b0101c3e05e038903090385d00d20929244200340e01a8118203980940e00001700b1011901907001c50405000400c0c85801c065207c0d4243c1d08804400da0f021000214009048861940b1840c4c20603d90703103090b2002003400c0403403030002d031040c0154020b40056907030000e40c1c255450083c004420021400200340c2d03010381d40d941800341005910748611409850b804144801c0c0d070f4070850844d02c0c22545070300c6981c1048802c00c18489a4240105075609100b0301160340f010303d680e441c07015108059102100810b000d80300c00d060050b5481c0000c84c40c150351050100340405a0007082c03080d84000042140794541d460303942c0c4810072852480b224680d071450403401041420340c403684030140714001d0b141070225864112007102121001c59400e8090201e000100340b440a80041003600c0920040c0411445201880006c010b280c040d51101900c3d0b00c002d00800c40d10101c183c20030300405029500d14a624503014000d0601051203d00307103 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 924320575 1250 924319325 924319327
    0xa0c0e0402030607111905031b030f0409090c0801021216140306040c0c020d0b01060806010503010303020c1207210b0a02071505060102120a030c020f1207080d02070204021201090506060307080c 85
    0x40e07841c0e00130046c143d00b001c01c07646544a0040701d402e0158496000d8241d901c03001d41c14000002c00960008100c617184850b14258030b160525129066000b025107600490755590754681c0055030140034005002d03150140c2900d8840e43c1801440c08103455207481000c0288962406010f042c01300d504d040c0c07584201d0541380805c80c0f40c1100f00443d0b404001c010000c6d0700c40441101c2d03500313010340070800a0507205d0303d444440503520b40c0d10064801c0d0209100083c0141d00806102545040200341d40035800840303c02c56142c00d48620201c40706030380c641c0f0700e0941690031015800038000c40b6540300e5003041e2403007421440d240e20f80c1c550140c0e4001ca582d0710400d4a44a0300820340a9208002070405404ca080d030040e154400180002c000d46024001c0c800180b0401d070403030304070708804a110300042280c0600c1519140003540c3c1d100ca29084685d14810199081c000320000d40c90300e00050104c042c08420f03503c1598106940300b021a14090501d5004490a02c2000a2290400303986a0040d56135071181d = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 924321825 1250 924320575 924320597
    0x3512040315060906120302070801140703091a0a0b15040321020f06040609050607080601120f02131502120c070e280b010905030a08090111030c060103050a0c0e0402030607 75
    0x200142c9515400820240d03c3e0440018480714010322400b400d0b882542520307006552600118207840c4508000842040164003099038503020341c0c440c0780fa26109501c0c0084d208022041c100040b1411102d02c103101e42c6400da08005481c1c9240b034401203204c003159884c03e1a0460f141c940c141a051000100324254004011174038030700811401180c240c0c01c6085400e10300d45880c10502070400341030100c40390301c101404203a42d06e014911562017800c040e5504607496080c001564042c020344007401d44401d9080004004000d01c0180200c094084101e003803050354600000245030100c001040c03186298180061000b20340c02040680071104a0f804c032b12144d0712220501c0e00e204080d07803160800f0070340d603817013007006d95203030b9088400040402d890f050b2030181c0d00c4d002d068442480f058020200c0d80c003003064421340d60050011424109010b01101c2c00c10a0442d092403501ca020380064a51360712003c2100200004044041c002e010a401500b07400d052640c04669a90406800c1e042400044281 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 924323075 1250 924321825 924321863
    0x61401050a1710090510020711100503090606011b0807080c120c0c0f010e0607111c050601051c020d080c010f091e03051e09150306010c1101030635120403 68
    0xc41b00740c104900c44115660649407812040064401580d1401840e40440780d00c43c0b01d015a05030b070311844002c07006d08480e59410004642c40f0320702c100c5a8501814540c4000041140035002e0b20000340b103986506d41e20b40e64010b080346006040c510300d5403600c4003041000290a0085415500e04005488030000c0f40701c1c0c0f07170058a00c140441032154000102140810a00c05900c00d0030a10540039114040340007030000904c00b40d000001c2c0c0c0509198440b400408c214181401450b40440e500c4003014210001039000074940102c010f8107407030204000c5a030380046071080c410300160000b0701104010260321aaa48030310a0a4160509146090b0700c1800c41450b019004480c48034490307007498881142e042e0400c0c0c08581042000301c0c040e1180203501910001018212405024161542c08407031459590340c0741840b4aa0ba4201d04043c0c40c0c00c000100308102414821186150785208421681e400c3c030200320150108180640d50350000304901400faa0603000c4078156600064020074205c034210ba = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 924324325 1250 924323075 924323083
    0x160308070c05060a1d1e0904110612010311180c16060e010204030528021216030f0515010609050f0301090f1a09030c03090418061401050a17100905 65
    0xb0000340c00440000e140f080302c941c00303080800248586101068001043d10500c00803080e882600c0240d03005003662109145420310790380d94000c0c80b604a041c032000290010445030f403c11f1000b10758000381100140f0402c0074540c84c01c1807250b4241c0300c2c52220360800d0940d14a2100160030458401e00001c0c099030341000b54241c0b00e1102d07401410038000c0101a5007168002d600030700c416038070303401410a0101904c422000200840f503803212644034220050b020008074090040d460f190500c2140340c00f0009049012800f4000d500031250f51441440c10708101d400c102030250b200101c0e0800e64018094241c10001c00001d482094840b007628524640c04a40109040c52010780701c0603050408008000004040502e03449001d501c00b505516100f9450350749014000c0700764120b41040c00350409500b081e80c0700e0f202d181c000e40100c2402c58a9911044100c0d441101c480c150603600c43c3c01800142041084840201040e00c0c0305a40b0040000c3d0b41512580f028001a10321a00d0780700c00828004200 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 924325575 1250 924324325 924324329
    0x603110d1a03120316050418020c03120a020a092103180902220518040b060609040e070806092805030c0607020a02010915080403140c0718060503160308070c 69
    0x40c003210f81d22140c0524a0701c25801c00c5030b401701d42034120030300520380c640700744103030b40845980c900240010b804091070710019402400030003071203105c1400300030312010403071040fa0700400a0440c016074481c0102d20040100c2c4c0075400000840300540e54000521441d486000511a01840d0141441ca10001c88c4c41c249259a8400300581d0b0001c40c0040c06003000d900c82c000e00c4940519011251a9228240104181800c903852440480a03001601069115560551041e001099145800743d087e000a08684880078200b81941c04501c041c4000c4c0005c000483c1c10940a00c02817015501c6010603007050950030301c80310000396a00804108000041040e101074002c43c9041d1001485d000703d00030342c1e0700f507140c5c0141d00040a03080002a04505455000910b00e942d81c1c0b2002c45554680301501c100a080c03644410b680c0c0200158030412000f0322000c4041c0100c10800c80180d4100050031007542c44681005200c0d400c400e0900d0321006410311807408880d4000344a07500c0e0002c90402e4105540d040d = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 924326825 1250 924325575 924325579
    0xc06200714100b060306040b040221160207080a06050a181a0105040219030207020301142a031b070218090a0605090d0903150b090c03010602150903040b13050d0c0f0603110d1a 77
    0xc041c1500103171070bc600e490352240c07020408890403003003441e60403651036a51f07214858498110319074601c0840e0494200301c0d070152032210045100340282c4c1c201100700941c21010703200012080d001d94040380c410a145401420201e60a50a01e0040080038450300460007040b07050503030000700300045407400c1d008071207200e14620440720780b846c201d42d400200e152081c1d01540d00b2170110760048024080e0b03005807405003441da40b003c0704000c50404c500301d0f0f9901014059030300c038403403002240c844072a20724654030591000c009000402881c0c0340250940d440545000d640e504070800760030301c1c1d5a000c0003040859401c840d02c450401403580701e19009020b40c170f006580004480b002c1185882240c401941250043c0c1e003204c9401110f00f2204a151a0640d50310340ca68004001c20048500c01801804003000d00072109280d15940b0400605904020b2030215070410000c1c034108088114180d4400003406d1a00701882600001041491540304011042c0c02d21543d03105c0e100049502e40807054145100 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 924328075 1250 924326825 924326857
    0x90103060203060907030e15060f0a08010e0d02030c120a050f031302011202070b0c131d01090b15091507230c040c0c06200714100b060306040b0402 65
    0x120308003880039600480d00180200300b8030000c694400d00c00d00ca1038502d540f145000c0d218940c00c0c1b502010031002d01030100ca610500780300c840b489136555407e280d0024041e200000401030002010f070b0f803e114400006070103540081c4000c856558001c200394841c150100b20055981c17010140680e50340c0520b055003407030a440801000076070320b040600710510324001d80b28048101d004043d180180d200758600145030050801c04516514400000750041100d40010703600074940766440907541e840c070040a2a001ca20032401002814054421b000c0310b42c60a0320030009086a003a1205414411000307220300404201ca90b00e1410031440d02511081503000f0310714001c1c0c0c03c0614000702020850300300c40300c0314000c1032104110351509201d810082906601c5055000249480300c40013002198110406603d00113140d252441c40ca200400005215080005462040111141c600300710100b44040c2c4510b880040c00d059605c07070044e82e078040d200322400b00e152000400401d010340500d03480045407001c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 924329325 1250 924328075 924328079
    0x225080706020c040b060403230f010905010b0a080622061103160e1e04050606090904050601030303050c1305060c010908180312090d0807060b060301060c030e0102060603100e010b0901 81
    0x9030100707010704051004c85040c010302d20b800301003081d40e10031444010102440840080d580200781d0b40c07030300c0110480e40240c50010810b01e00041c2520007400c0101c40c0e0b0396403803c100910349445d13104c0c540600300b00c90003400c0502d0595580b03084010038401d240a05100106504100140c0e030300200300d16040c80301100c0e00c82c1404a40c240c60905151140808104244088131030b500300b50114a04071001d0601160903d61107009202c000c040144c80f550700600d0070001e200441d21101c41d4035015030b1045c0001d02e1203625504005040b50f5028062000c484400c00032492250174414821003920b804959031640c905415001c1801803040302e1000f801d0f00d0b1f020841d404008a121140340003204182d080d20454002440c1645441c0b00d11001160300c200010103580101e036185001d0480d0354842ca40005041300080001850303a04264840c80010300b4070100c01d400c0540c4a02d40400c500c100780010030f11401c204000a07101c000490760151144c1d950241090000025049131108090190500e40f5650b = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 924330575 1250 924329325 924329327
    0x90f0807050117133809010516021f11120106080f04030207150c0c0803040f0504050c0703050702030f01020325030c0f1d0405150415060e09040c0503100f06080a030225080706 77
    0x7001c100c86c4450907503c0e00740060a4180c00d00918501200d480c0d014140d51216035600400503e45020100911544c0d135803480705c40074091009050240e00701c100400305604d011001800000f00404055980100340d0a000001c0d80000d40e25003540c2c1415280341c10f2908144007242e03800d11400c1e01419440808000140043e0003200400944510300341a41030705448005002c161403003541c40e50340d43d0000300411004a071080000d00840d520040648484801c84007030a03082e80c2064400081c01c1c0782c040c09040d02c96201c00031510044605040c00d000c4074004580103400320300c884801806111141b6440d0018507400c00c004003071580002c0c020021410311840c5008000d6003444041d02940c501403010410051030381600301103402c26655642041443d80a00150302c101900485100c03010940c04165580c050083c40e00414114000241a00004c490441900d882d1360012419403c20208400802d0b03010602c1b420066950740c10b0107494422030b10404800c80e02d94407a9145005008010541c0d13 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 924331825 1250 924330575 924330683
    0x6070203060f0103050d32130315180f031d0301061d070e100c020607170306181905060d020613061205100e07090f080705011713 57
    0x380b40a4001c446e048588041c06580150000106c88030000d8605460400807480940c0509024201d009003800c041e201c0041e1420070190307820444240036202c400103080c90f074511402c1e8400c24851900741c00084242c07103c010602d007800d000741c02c00076400006070040401101c3d81401d410050b000f004901c0e43e800082c00c2e0005401c940301c2d82d41c00c0c81b4001c6004c0500c1005100c2084e18001d113981c100d100c4028080d9103003030501c04126001350040c0305200c0440c40d04222038402c05608134003d82e903403404600f0040d40d0b09198a03080745980c5d41205001d000405800c000b0002a462803001899440e40000103c1032105102c0080d130212000949040c1a0701c1d43d15003108440d07581d19046c800030f411541c0340040c0c90003160404490070015008000c42ca001c0d00750345401074124240341002c80d44646546060840c0d0b81c01c1420750b64014881046a96032086c0242035103440180900410308110f06080d414401d04400030300714650340041d14910700803542403403a88180601d21040b5600309900c0c48400 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 924333075 1250 924331825 924331829
    0x40222150e0301060501212007020f0307180b0f060705010923031c0b0a06020f1005101203090e090d030614100f050717120705121506070203060f01 65
    0x9a441c50040e62030300b414051481030380c00585418040440383c4202181031094806c0c000c51854540c02d58183c1e41c2401d28031913881c08002095150742e0481070041c8a5034800c52400030b802035105040c10003000c03d0680d030050000103c160041279a540d8000096102440c0658495100c400022030508008055000c00c91040c40307101d20b010f10038500d8142c50714000d600802150240c00811044828032404080da000da420b81130700000d101c84d03141c40450000c05c0503402075809680190560210310104012401c41000e4014041c025450803c40801d50072241c0c3c030440e002811a5514001094015802e681c081d255120035581c0710715226100982c1c3d0300d040031004c00824170b0030b03c01288900804c0540800c00d8805403001c061801643e00403204400d48980d11003c1120610031400090004030001000200381070380b49881d1440e00c0f85410310603202500f10814098100b220618280a0fa11403c0d80003c143c20008410408103000c11014824280000d41c140525410810a58525540c1c241 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 924334325 1250 924333075 924333077
    0xf0c0114090a090902011704121809090f06060b04050609040e07080604030302040e070804020102030a0e0f03030715060f060915020a061b030e0327130606020607030c0306050a0504022215 82
    0x103d010a02500000182c02c1658007800c0c2d9040030700d503003542c27502448480c08161040d003081414103036075044aa081f580342c3d8108840c2c00180d51042d006018160040902074a03010440ca46007070300e400b000510302d110740c40d6050700641e1241e0180003140c030305000c1c3e48014000c910680300685003d01e40103009600c1402030702240c02d6040c2c040756000d8422001e01c0e2040d075040e00194988800c0c42c0e401d0b11300413000c030321203944007032918407a24643e2402c2c400340c031a440c41000400825104011007200b039036065000030030300c800400003c100807684024040700b101c000051100c02031412000c1242405956840540007030b01b04000b045440308042d20044c051410f40d9000c11010111000080d107a00c0b071f04403d26101c40c01c03118002c0300c1001b04102c99640800040101483c404516060000d0b12055442900560402000c01c00999050300440c01441560b02d02004964106030000e00695035070700a5a0180c1da000c40d10741c03207036921580a40114188065500f0341d156a8140041070303181600d2001c0 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 924335575 1250 924334325 924334337
    0x106060c1506050a030f0f0c08010c0314040b01030b09010609061511060c0f0c07080a06020304120e0a0608070c06090b07091e1401021903020d0905030f0c0114090a09090201 76
    0x30200031890b00c00c080640e0402003106031074916580b12012112005441a40c0300e00300d8400150016006400c020300800c03c440c00400c02c0107583d9800b504403440c44950f14141c50442e0200000106c0090145056980c021042c00c0c0702d8440300c844c180108034a8000e042203d00e8200c0106030000103030051044c191450381c900c070940c1715042000c0e032200d40517541100d2034502803101040107011100600501454130040f541155550b0340710a00d0580341800503910305a0000c280824885030740411840000981403e41407580c0d4a80403404078000307441030b8002c020790503001c124203600c104000d10115400c02818040748003503080c44284c481c400d5664801081180b10001425072144000ca0000507a40072074550301d5150a025848011028144034110b000d0080700090414001c5a1001c41d54080e40c018211800c1c2070710080e0943d5000d80000748641c0c08a000c2940c080000200102c1c4010300b8a05080240402104490140108401d445d03010420f100080380706041a4000f4600f40e000340d89503 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 924336825 1250 924335575 924335603
    0x6130f18230a180218060a06020604030e0405040303090b16201906020f0c031317060610051e1e07080a1b20031002031006080604020c0106060c 63
    0x700c035a21141d855030403100203909001410b032038007036031156010a624014208020556030300281c001102d5100020510480d2801d009590500c0c0d250500540030500003010281002d40b00a84441e076650078041c03089440781d00040c10503109820880b6000d920403c00026400e20b440b01c8000b45d1807400d10003000a00100c068000c00e102c000c00c207030341d4a42d2034005c1c104603a0903981700721103003d00b807030107a50641d0200296003030203002c0002096007a40700d4010350744406d880482054081c44650280081c18a2869a030f0300162000c500140c02c803104039035124003424581c009071a9401a100500450011141601c1140d1a150300401c0680700613a500c40c901e244081081089000348000a4000c00c3d05110800d55580aa40c40f10f540c1c2014034500300c2c1c071501503a51005c0d54a944580184085001010350b2800c0c1010015024034000190043d401c40c5003c00035000000240d105400420840c40d0100f2000d844d540d048411681c43c43d402070012075120071019158640c1d02d8021200c0e51001740d98 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 924338075 1250 924336825 924336851
    0xc061106061e0d110a060909111e0d06090c0201060806011d04080c12040308090910081f0b090403080402032b0302031806090606010908010203010f030206130f18 71
    0x280006030b84090040416840c0c0070600c0082c48a1400c1210441a02d011980a691301e2500d0000280120b55510440303034100000c420507110f560301000d00301d9030140185d1540c103d5480220b00502001d0312060745801d64a038420b000380c5070a6025540142c50b00c008010f2007903041d0403560a0310f864108440899990721000225804401c0c0c44030400903401010500041c031000c014000004070600f220418500303500c100085501a60003100c44000018000c241402c203091030581c0411000300c03a4220b146032050080e02e8401c001e07000504a0b1a060848640c090960701542440c20080d00360826860503240180418405590a9100344a00c01041c4c10500038088a481080740e007841c10103000031821803e40280d000a0002000c2250140688487c14000c00c60644265242401000d242c24181d0001d4240f0505800040035640100014002d88500b0b01c0b00c001100d80c15612140cac1d5040c002e0941d80d254480d078000d00003260b0b01c0a00011103100b60350441c3c2449503c40800c000300000128 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 924339325 1250 924338075 924338089
    0x71a160804051002280306061d01120b010306030803100303080105090408090d140a030822110907050c0a0809030606010e1c0201030213060c150207020901030f020d0c06110606 77
    0xc00034440e90000c051651600c200380c025291540080c207181d152080c612070704103100c01907644030300c0000e940c0b81c0c4100308c1c650744a904c0301d0600f14024040451003802c10002000c0504645000c41403070344410900d1a96482a0700007070046400040054480c01c141c4800703015420544020380c000741c08400003060905d0115002e43c015a84100d020b441c00c0d040505102c6a801c02800507122030060088803221483c00380300194a81d8401e9035511800d00d4030720220a4a961109040d100000c1c0402440340050115a01c40e80071001c00c88800d00c89541c0d0300d81c02c03141e5204004c001d0032140071304289c940c104181d0300064031550008809441140d41c2d06001180c95260305001c0304d52104a60b01101e441d0100e00c914401d14030300601d0b003d840c140114055090410f01540a44002480c143c5440306012121550000c1410722507015032510b00c07641c000508024042c00003814032101d00b00c100e001c5540e100b00038442a54842081103000e0740c4d81101507c40c01c81c1000780c3c0d083c3d019001c0000c0305c62520003 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 924340575 1250 924339325 924339331
    0xa0f0504060b0f1603140307080a051b0403061107050d0c03020706030b061603020a0804060c02031207260d1e050a050103051e0312280614010c020303071a1608 70
    0xb092107041100002c0f02058804c00b5080c25000c1c0450f14100701c0300d000c1c1000c005c62140d600c5071034030348040c1070225800040301c50081a0020400d940c100710618200180201c41c100d0350003000102e80341c1d51104074003010340301c0d040c4021b10b04e110ba4001c01c0c003015006174140a03013034040d800366004543e484000341c06541c2075181083d03108504000500c00034a41e040c104084901030b00c11542410702c10b580340842c5a020b42c1044001c02d151101e41411440d0410a01d41100c0c1c0b040a0903080800035a10660880a404582107203507140c0c1ca402080002148240c0c2d81e48449864140f0104450a04041d4011504150070703241504050008450800038022030381200d5000300144003e4145080d10350a0100c090780792003d0780030400c00d640ca030005001c4040d000d906806102c0140c803101c24200030b0642c1c0400400302070b0b6410b0103400c01ca8100c8000488807141e00a00703100d502d40e5070910029044d07102d607120081035500001c44214601c5540003249105541494010065040501007650000750072 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 924341825 1250 924340575 924340597
    0xa0914031b1209220207021504080708151302011b08251214070b04050d0216030b0f0c0f0307020a02100e060418021207021f05090a03080c090a0f0504060b 68
    0x1a0803130707054401212030841c4440c40c064010300b0702600e0341c0040d480d9440e10300148400d0030007003024008000d007404a08028103080c401804445010030704458200c0004024030705044c00307104007400303590242d01140300142e910702000301101c1103031514080c0c81e0003000f9901c00c91a40540c1041c1c030201085281c205494200c90050036030140303a0700890300c600b8000807440148900b4005800000d040c1c09030107000c0d520400151006400d0000000d00c0c02d8041054036400b42d58101041003c14031010240360000c031192480101ca86e262a210201881101442c8000350000010071840d19030101d0b1450001d403007215018030061683c04102d03250300542c3c0394a9400003007003008002d11040c0010343d040081003130b500035090203020850a51881f03022280180580c00200c3c21503034510501035a09118080d00c8000c0005007051a030443e5a03600740c0034020148034100b0046800071030030030165044110700500a08440e6128034081e5072000342446418050f43c2082c074003282058110098449080320 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 924343075 1250 924341825 924341839
    0x310150f050315031c09030b060f0a0b0f070f050a1208010602071403010b030f0d03050c120a050a0f1509050a05070f1815030605190e0a0914031b1209 66
    0x2620422280c20b400914510343c14403452061030341000241c044024038080b46d0300d80d0b02034540fa50401c1c00803907a000b04030324072a0043e00c4589400d40d6800d203040c4240d42d041000c090315800395100d0150030b44102940601220880c0b45c814082060004000307803401e1040318102070711000d081007914140b5081c0155030260f0004802401103c03c010101031440c100140007082003814400400d00705015191160020b422400c6507001c119054042c090300301c100240521f242c21f01c01d05410b10f074200d002e13201c000e00540751004100101d4540e003050403012015141040402c0281c1c0b520140c1c0c840d10f1160348102802c10b400140c1075a0306224031403007803030203031504840c1798180740044640e40200750001d104943e03440341c08280500c5014104c40c405080fa140020b0303041c140340c03c0180f61502c032504203174800d04111042c80b007845030101898000ca26000c3c04a210301c154035000880d0803003000c08018610001c510581040810b41074105641404020349101042c0094600880d1041540317250300010 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 924344325 1250 924343075 924343081
    0x60b1801090e03040b0c0708190308221a1501020114062103040803071104020a021e0109021f030b030f0a0b04060b09160e06161401060b0310150f0503 66
    0x4110b4101c12005070124064910300354442c0d2600341590001b0003180c00746d910032601440340d54020000860200710400b0146450b151aa9000f00040300050020000102c04040e40501880150581c46ca89a015040165212070b82020040010045a04400c00040004511510350043c490364920030752405005003740e6415090140c240d9081080522440b02c0c00e101040c0354009001a001a2000c8000f0f16542c0030b49080c00b415181e030340e03000c00348643e10400024100e541c00045402d052100e110503440d00c1c1105159445c0141011003006e50868845914003202e403904140ea43e10a05071603d0400c40c4c02804c0040c0740ea00d45802018203126406038407680c3c049005202a240d010b0b20610b000b0440e0080c44000c40c0d505203060380c0c01c10044a0394114050303000c1c2c00c4480c00100302c000796007003801e017030070f000415514003071080b40504105c0f1040c40c3d019051704d0030f401450240a01c0d45040341d4a0400507a00c4420140034803a00360f03e80c01e040d4404030158421159614010704a40c0d516045403 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 924345575 1250 924344325 924344339
    0x20a0c0f1d090309030a0c08100219030c030e120715090f0b04050a0c03030806180702030f0c15040c0e060109030210030f0e0607051305030109020d0f050102120112060b1801 76
    0x1d102800700c0202c0e2200348900718180d0b500f00300b0481d050344611a8a000d0030300c0c080b038541c541081c49490051203401840503e14003140c14089124440c1c0380e00d000f2030050203604040d0000d180c05110380e0300d68000c002d40b989a20718404010420300307100340600200d40e40409688000ca400c1e40c1c000a0440812100790300204a09072800e83e0000d01071001c1d5010041117544858031703d10340c1e5000300d000c55a03060801016284c00d01d1800107040310000c0040381450300c0a4001c2d140d1060b040350900891010130101031002c0c0c100007548041d645a07404e817080781000d0401644004940c400c0c1e01050000314006007035540308400381421641d000c2c1c03400c50340020000c3d0503070150603554180100c4a03501d11030014500d00c00c001480c001c0761240c603082e0341c401e040d200c041caa101050b04900d006c0d031f041008040041c0c542d40e290034280307a00702510b880f00218600d00796029210751f14a090400e61284004201880201c082c0c8002c40e100d0b210402441c410403007408546040504e84e00a01000107004000003 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 924346825 1250 924345575 924345629
    0xb30060a2403080316031112040308060f032d030d020405120a120c02041404081b0c0d08030403050c03030a0f0e010c0806060a14180f010810090b041b020a0c0f 70
    0x20204501b13010402001e40e1111240940120800081b502c42e83c3e0140000d050700070b0310b102d401010550300f00b0030502c040c0c40400d41e5030b854800c2c0d0703405662940d81d904c101c42040083c40001c10303020a040c7d80d992442220340e00040d4010f0300901c0d01c40c40708228140c0d90300d240081c0c00568594800800c00d90356220b16010f40e011999640181c1e0429181c040d0044816541841c0501c5944624402619000780b400c00c03001d11016045040300d0740d800010b80700034039520000d0328000e290380110070a960ba540c62404603107500030350440400c01e00c008024054000c1e0290000c846100614a041000014071b00d05142a01c81002d03000300480c0560000c2401400c14400504d8070043d1410079030682181c800540d100c59000858041c1c040380301c3c40d01c8200ca4039003031a645070003002c00d01c2d0204072411f12921040500195204c2c100c8410750b6107800c240c164803030360403074800900480c2c1844c010030fa2243c0041c0d21481d14104c125800f4440c580c0104020381c188004006031403070700003e1400e00c1c507262628119 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 924348075 1250 924346825 924346861
    0x609060d06050a0609050604020f090f0a08060106020606091006052a030412020405060a0b0d02030718060302030a0c1412090102122502010b30060a24030803 69
    0x450025400000301d00d50b4040e440c0500d9800340e0001e4100e244c10003810072108064030341071045004000720325640031080c00f0796940f00d90444421403030001080001e50180215400501385004d81000003ea4680204035076105949c241c3d8800000d903940500008840ca29001d000c002c07071000d03c41e005070b11401c4643c40407103060045242d44070481500d056455030300980c0c42000b19240004d048011402d0a008080e00000c09441000307480c1c1c02c014007840c1900404988180013a400310005504070f20409000c0000140c19480818450b101d4100402952044030b00340383c820308144240402c0d5101d035428036102400d10b00480d040c001c140c03420a014290141c000c01c080d640a1001c08800d03090b40882034001c003c840e01021468045d00c456045520740f60840e2001d69250a481106c2622405400c2801c841c10035410000030610340c5c0c6502c6182c40350401c000c0280b01c0c4108110b5945210b0780701d1680500d01c00043c4010001c07102a41e004a0750901000700000381c00e00104d1045418070b865101 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 924349325 1250 924348075 924348079
    0xf0a0902311a010219020d02011409040f020a08090a0804060c080d020a0c0302071211092701020406030e0708121612030605040c030e0d050913020c0d080907060206060906 75
    0x2410072002803510a0ba01d600c030105484800aa14655041d0780420072080090f060601242600080360001480c04203061006410300030352180b40c030700c4011090201c440c40780000b8030822410f0003203103400c0c1c029008940e4107004100500041f900c0a00c00060001441e0350003c40917103000e040c0383c1c0455111424050413681940c0c240300d150504030280c000707040801d040e50307100e803800441402d000389008101da10810207401340481c600301045001c503160720030031000d0301d800c4140d03200d82c41140200441025296803101900000c02840c05064000300101d408a90302070182a40c40c0c0400d83d1a002c65100e1003031140d20590224054181c1c41d00903013048010100e14500302d0007207880c1d95089601c1a4401e074006566000c040c0128034044c41400d1240304149800c01c198030701e101c1d40550301e5013201105c90900ca008181c5800c0c0355500340082c8064800824255203c803608503156648004411030b280c080380c290400903080c140d0020b15202150076590041050b078543c3e070240906294090030642d = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 924350575 1250 924349325 924349399
    0x504020916050405041e1410050d020f0303030f041b060206150d02090907080615210736020c1b0604050d0308070207090b03100f0e12030f0a0902 64
    0xe581c0d6200d102d030302c0380c990b84550b649103d200740c004980219028490b080d4011f20307200050044c846a100f0000007507070801c0d542c1114402040c00000d040b000207000c010b80c14840002000000110001905c0c040c0c2e1007200300300400c00d0001083c04c0110301c81e0003030000591002c03001600001a250815561140240c042c000502158010a403541c0c8210b03900203407540120b00c01c000d0102c0800101c1e40c8070350102142c03c428580500002c40d50400009124210300c000240100f03c240d05010755401402600c0a0010600e8942000441010b6045a01d0003141d84a1100300c51080e035030003111112900100903000e60881411122038000881007456040b642c00d010102d0b19403a00f00e80c2400090190316600302d14a46141c0081c6040c14681040e041c542c2441e5184850344c60004860340e2800900d10041600048030344400300400d01c1c003010705031a120705a40c20726188483c200642c0101c802c580311103c113540780810482a078184407002508450a410511280414140f07007d100c01c0340600c0d44 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 924351825 1250 924350575 924350579
    0x60f1b021b22140f060108060a06051c06090605030105150a0e04330c091a0c19060902010f030209060306270f400f060204030515060405040209160504 66
    0xb002c111018148202d80d40f480302000d10840a1520000551015003480c0c070440600e4581c010a00c1171502c1d00c034000601101140d503c094800480000c2040c5030b03901c00420425540b01001d40160580340301325070080d4600350100e42d880b058020300c240001c0001d44044610b40c9400f281341015100100f081c0c0d80031400b5074031340100001c0f0325440300c1d1843c62801140c85060040891008a508503d8100d0030700c07071428010080c11002c810004000706464440d15110001030310942c0c2001340000f950004e07110890000410132501e548000b0506000ba03a6980915004000a404912540c0d48480c0d01c00410300000f42145040500d098902200301e80060f0344000101c0344916900054812121180e1a0400c20030b2803600b901007002c2e03890729a8883c0c0d103505900e0035100d400342040a03150407440205204241441101400d41c0003203030b0301400c11940c540d074a0429545819a403800100c885204c5000b04030f05141034003070140182d4004081f0401ea440d580010145103041c0800401880780034800 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 924353075 1250 924351825 924351889
    0xe2103190801030b060d02031509070509012c090a062d0903140a09052e0f12020c0d0804020f0a060305010314010612030c020a03060f1b021b 62
    0x8040080e00103484081c1d241d411480c01d41c0c000c0400410320707030003035807041c80ba1005a9400250303a40e060032007101c010b10545501da821800d06032290071958000c4401340c0009410380000040304680e4071942490030785980000c0307220145420542d0400004e0340320801040104a141e0b001035650640d9600200341d900801503210200441c43c81080c07006641e88400109041d08071b00000141d003150461240b6151018034060a8402d2901800d4001d2001603000740d80086880c0d03001c0310301c0c502c04010f07150741c03481d605004050101d5800760a0008183d0401041e443d0010700940d0f600d01e0300a40500400070b9501e4046130b6034580148280d0b848a001401d0a09980720450391070b002e00b00d6a60041020741c15400d10105c104854440b0040300da151503000c11007444035125203940c01ea03040c80c00c44042441800001c0301403a0300d0300083d18040c58150006415880d81d40004203071100d141c580c4a424044400580e01c0300000301003100721030424078000ae210b18103d01801c8085c95285640400100ca40b91 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 924354325 1250 924353075 924353107
    0x4051c050d0615020607050913270f030e400f020705070e060303040612020d05070f180e16090305070b120a0213140d0b0f10060e2103 59
    0x220240900307843e0b045007001158140510340e13000c20a420306600d050f0445000c03d480b10384460203220000e944e41200745103c2d21509650001c034403081c900c07120305415410700840c44150803400300c0116074144d000910310b041100301c011044034441d044070948051040c900c82d00c01d038441d04020000542c4070010300e07890442d11a800703c003840700f20f00603101d091901d0020b262040b01c0d04414046030344c8d041000481e540000880e026221a85004004160307241c00010103030081c4c9400020450402d402c102a01d5800321a0300d0102d1281c0e076500f00c0c480408140c3c800344210074010765126043e880e00040f401405008141c1ca6102145000000030303640f501c81604003141904940d4060300009a0211f1500400345010340107040c03808114900514070102c82c035044a039103e0012035241950300241150b444c200e0355626560444001e290501d0449059415400125044110201480310104040c1c0c0b00d41ca04201000000d86500c4044038681035510040e25401603180300c500c010455141c15001c095 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 924355575 1250 924354325 924354329
    0xa0302100e0c180912070c05060f1b010c08070c030804030809150f06040605010504060815010c0501021b010c0c02210a0507151b03080604150f06020f0705030604051c050d06 76
    0x1040d0414079040104c00d66082c0402d2034494041094140000304c0400c5040300c1c00d0301150b80490300a69220a01c5a07400118000c0d17044641d1100742400000e00c1d021819041914201070542e10380d45980d0303581405503018031060380e002e00000c0c05440002c00080c003c0f18035940101e802c400b2120300360300c0c5a581072030b104800c6540d44842d081000501c0044e0400e03014002c003918003400c1c1a800d00e424404018007001c1c00a002c18011921a0020800303640201400c0350b05070340143c001d558515120300a488059400d0b00aa41d6561901c0320030020940b280e61907c1410340e00034110034480e044040c2c800003082e05200c844c002030040e0394002c400180300f04000c00c010009081140d260300c000a5014181402d904280696401e14141c0100041d40c8400001d5100324100c13400240c980094000144510355904042c0e071220b860040440e01239000a14044a03441c81e8040350000d9855109160f100d4409a40042403603000c050040360440111a180c0c04032111440c1c802d06001e00760840c50300344d8a5076 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 924356825 1250 924355575 924355609
    0x901021b0c0a0e040803150105070206070326011203230406020f060c0304170705010902090702280b192406120515010e060903060f0610020a0302100e0c 67
    0x800c010803440d0034420a840000d1043c0c0d07400aa0038980b03a25840704038840141040004181c2e55440000c0d68001c105031100c07590040e0482c1d440e001245009000c2c07103244034911100344005c120b0503842c0301c06044264103039450120746001e15043c0e80d0303061310254180400d102c2e800c13401c01032031b0502c0040c14019000422840e80200309441100a240d4102080500300a4030a6020030401001c02e9980904810b40c60800348156030b68002c0b1700f0101e006000c242c50081d07200c003110741402420360780020381a01011b0541c0217002c0740158070009403590040080700410700c07005940040c485c2e1480101502c0c1c0301102c820b001c03840d1000440c4a0701032101810002c1c1c094044d41009021140c2c2c045560b0b03c00c00c007400da04100c503040c1001c02d17288800341c45d5a1a0b0401000520028443d2160015107030032034800307003c0340e4281c140712021540403c0200c030494029000d0395540e03401c0c52b03c0024081c040641503009030a0503402001c202001d481e20200e09440c0b481500521182915901200f11400b000 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 924358075 1250 924356825 924356833
    0x12020304110a080606010207050d1b0e0108070b0c0a2301020c01020d11090f1504030501020f1b0706080f041e0f0201080108071a0304050c0607061e061d0901021b 71
    0x1c0542008002c002941204049910910070800c050360001102d0050300c00807100360350b22001900e001000c0540340c41c40c02911031000c410000c0e182010080442c142c1b01d100d01500d0390b16496000350320050203010141100d0b6441540038a01050f000005110409104481e0264010603840c2d1582079078001208070006a50000d84103c04401910626004d5000300c4a450b150200c5540024000702082601030b10a400d5810505a6920002c003110003d6502200a6469220030b000100040c2c12182000810074110042d11204200101322001030b10700759100d9046984450320f02120080000b40112091a41c070b40340150341107040d64030399600d82c2c880d2100c2406489035200044c81c401c410391212000f54003454091214401c90981e80d001e4203004011603840741d8440c04e02070315001342d01d140e1f15001240001c5003820b01602d900020100521004114155010140e41e9000c5501074810b803ca04083c4601003045c4065030401c3e03a82026000380050304141040000b40940000c50001d000a640 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 924359325 1250 924358075 924358103
    0xa0f06320109150b070228080106080715021c0207181517120319050118150f0302060901210e01060f06021c1704030503070806040b061912020304 64
    0x10140206003600c5491500c06441c3e41c68078004c2101c600540400038841e440200e13100400b100025461201d290010f90301111880d035410950b80240158007410300d03070b40125a404904401012840301c204038490f802840c01009051740d00d0101503107804903004500a00748000391040300f500e00170449201003000040c0d0070a042225800b20003465004004020001d5445107030a20f0205071000e6151946e1610303541c80d0384085199480c0120345074442c05080c902030001c1159a1201c48244001c40000e02c1044107081a4415210141c3c06124918075003541c45420310060802e80c0141c41c040301d043c1001510300310419a010710154860040f2000b2507940d044040344034509020b003000030701e021040c0c200d0642c200380d00251190042c0c001881080043da101c0401588122492603400007000001d1900307041615005101da88180c5d40c1c840010344000200f54a45000d100b080850940101a1850101400c8442c502c0352007242c2c0000500264940c1c135010b50100d4001540716600c24954441021 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 924360575 1250 924359325 924359339
    0x5070812040501110c040c120c2118080a0f0809030c1b030f10020a03060920090a0f0605180306250516110301060b0403170d0204080a0b0603010e0a0f063201 69
    0x5080c0c42da17509d080128400c0d21850b440a011030040760144052070203d080001901340c80649a02d80c4801800030400207180b4503425400910001c40072155a40c004590710341c1900243d8070302500311000780c50b400040920200a910030701c401d00c140c2d00a810345208018882406050140d21941d00f110207400250214425505101d640b000e06109941004003c10305a04480407107480c0d00058550758002414030190307500c250203400100301a40c0e1942411361a502d00401982040c00e4a40a0011950b464500e600e40071804604c40e001e054041800105002c0c01740303507100d4821a100051001c20001d15405841074040100110b0145100104041c01a01814211a200d500074500d00b0003d0000344002031980005540c812010100552614904058a8002e100e240c1c0614001cac440c140c0c1100400c0038400c500d038800d100481c02005200848140d19071240701984008005aa521002ca000180c1c1c513400802040001b01e41d092000301080140e42e48a03007640004140784403180300410000e = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 924361825 1250 924360575 924360581
    0x306130f0509011509092004021903060f141815030703080c1b0102190201030f05131208060f300a11010c03050a0806180c0705070812040501110c040c12 67
    0x1046040401c0240308a51f4880d00c0c03060810003450700c105050401040007da4940d01503440b22144d103042c280801c50180c0000e4014105485070b9900c02c0c00744000016182d40c25244501d00e00005002d000c9010b401d600d60b0918100001c03d1880903110b10071000f4241d84080003003001440c419040184e490500c4020280380c01d401034414500b4000103504584c591364040b4038075220040c2404540d803850300750320042c0c01900300d00c4c3c903248056141100304040c00c92000304be6128540941d03402c00f0a8001c4071012102040c08441558000c40c000d04000740d03034102551800e50a0800071855400c001e00350308ad0603100b9081017aa820705900101d0740ca01807141d01d0441c0c034102c13203090a103006214100e540c00381c014040c0c0d03406078060015080003c7d449032101400c03840b1321024040408007034a80307540b24103002c0d0090708003600c80c0d10032520701166039040081c0f081382c80c44070312912500f81883d10b0011030b280c41415031800441d01503038640400640386c90280100b81c480680741c0c4100708200031001822 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 924363075 1250 924361825 924361829
    0x6031e03021501080c0105070c08192a0b0f040902070f03110c090103080c10060308130e040c050f0d080304081206010e09010b030702070b0d0c081b0306130f05090115 73
    0x20007480b030001000700d4000000c401841d2902802c2240e180d03125070070421440d040e44c0c0c3c070460940c01849021107410210040c4500154451410b078621170312180070f80c0428401e0303c440040041b4011409100d56102c80b809401c0200300449010315154480301110140d8100e24812206043c04008507030400da0040c0f0b2221580001200800b52461103000244c0070301d6040c031010304030381d1000504802d020400d000c4203540009802c02480301c65540d14000105500008240c802c51185100200f0b80202c241c82c072901994001c05d002344511f04080802607401109580c00d41d00c40d021980b08400903008101070341c400c5000311141c584540c0c801d4885802d01000619031030401ca48400000010b07500d130a03059041d02c0c51407940c60f840e0b60380e142c0c080c2c1c0b03040c12a0700301d8082c850000c01e0080e42c078407140e0084845000c403170340c46144903102d40e02e5106080001b01500e00072502c1c18800645a410040e560940840b4460f101007552441e05c1e03001c004840301500d08010f1070b511101e800030800310300c186403c0 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 924364325 1250 924363075 924363103
    0x1c05010e06060f12070507200102100c0c1203021c090203010605120a0f03030e030f0712090f030b0c040e01080105070807020c130e0f030a050d06080c01050703030f06031e0302 77
    0x850004041080d583c0c511030320107018074401d60400807803800c030305c26005e4840e000c0c0d222a004500d00d110048042e03003044440810343c014403444000d500c0301c08642c043e040080713483d600c502814040b56541c4a500e03101c440d85070010580e090107406070002514500e240004c0b14104002078020740e500500d0309448039500304500400381c801c04008500d00019890604a401910725480303040b9130728040700a003040e9000c111952001007072080c0201940002445c82d40d00c80d00c3e008500d840c1f40802500c0560b0786d4803e000c1052440b09040022807820500e19503c000e526008500d020b4450700d10303580c010800c0e004071869a40d54400c10920941142d5403035040010b41c0000c0c0074182043c2c000411411a400c0640c41c0542c942040141c06e000402040c10010598826603440302d04186004205800814510001904104000604bc035000c1410f550007101030303440301c1c03070321005403003e5003d020940e9142409680c1c1d0031000002c1122540c10f18100d815241c504140c440d06030a000b443d000d4054074000c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 924365575 1250 924364325 924364327
    0x906080103230106080f2b020c060f040f23010903110d03020312130203120708030a1107020406080d0f0e030303070f020a080316091203020606040e031c05010e0606 72
    0x4804507500458030010190400c40c0140c40700b50490342980505180d40c088801c52003512000d4803403502c042480200380c030702414090301c0141e00a242c0300e0542c100e1980070780560000c2d118440340c0c2c1010300051011200407207030249000d0303481c012401038140c150720a00c08030f5411101e2201c07012403028204403030b210034a0500500c50450302c603014004000c80c5520700c100080c007400c2c0200340c0240b0689131001c200402020040c41d107100800e140f81e0b40c4a50803482801862a10180440c1070425070b009aa0044500e82c2140d40d24040d00006068400ba03180088105000f904010794035030050320301034612500075004102410802900365195440043c060048207400310080c0e1300c4c0041540d502051529101001c520101c034141d0a00d8911103010300fa00b1070004c01c0200041f41018140c9031444503541d107021990359030034580f001c0740d409d000050060300b110700443c4591800b40c000c103242000d43c00070b0700e01d0301018941c1c0d4000c503807010000006980d2148010003141c0f00b60004103500c800c040c0c0d84e207 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 924366825 1250 924365575 924365579
    0x30909050f100b0913090803040c0e15040207020a030210020706030e0706020a1e020d1b0b12070e01350a0c0c030507030905130506030c10020712141c09060801 70
    0x4401c0401203805207010807400070451241380c0d920078804c14020800000204000121303400c140b1000e510441c0d00713503000e1180d40c1d030000d504824803102502c07403241510640d84401c00d1008000285d40041010b0382d000c1a40303080400541d03103548400002d409590024004c05207003282c060242e4060b0003c0c504203401101042022503004a010b03070145a001020340800146151041e1a10340800c00103500280e9042c04e040c02c0200188004200c4003c02c2281059150740d00c0f1345d09110b05c5103d80d03014440400700e010804440c0507507000d00c04454141040d441d00c0f4601045540191030011100f0700d0800400d4a580090f0005194035030402540f000070310400d03610881c00350007904003550080c100117000580c0c50034148110702c04c001074803006207000190303400400900301034401590307002e00c02d00a4034031809052130000c1078030f001242d40745c01500030075150190140d2185c20b02d00b0151903005410000c00300d036140a01481c550703401d100565004182145000070440c5406400c0f941c00e102c0f0314001 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 924368075 1250 924366825 924366841
    0xe090303041a161101020f0309071404020f160302010605030313031103030306060a1b0813031e0b161202130303110307081b030d09051b09060a03081b0a030909050f 72
    0x1030f880030b030740141000d025510780781d411140240f2a818045c03002c0003000c014012500e1001c1408008c8422003084142c0032840c2004001c100e02c2082c800c194802410040b203812120203001542d2403900a00000500315910808242181e0001c8482e110400080c081402000140d0707141c0301713810b44250020340c00c41c9091004920300d48150764558041c8580a08600030200900c00082e6200d944504542c0e115070405034524020700d0107000880720300e117010802c1043c001c2d0814540050a40085140c5407030384540300d554092294290500c001c00c070b41c002d480070b4000440c1c0001d1150320060040704400030315508000317020003500071440c401078204114404c0030075088802da81011412001d0044e00030b00403018107181d480788802c078410490038004040144000802c4800d1047e0081e405101c0b103550328070800003c001300702d821981c0001c0004091003c103201d08003404e08449002d039001c0c901c0241c42d16071850b10710f0a07a01140003410000d028010701801d4004c0c1500407003200c51040c1d02d8188900 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 924369325 1250 924368075 924368101
    0x61514090705070c0f0305061b0a0e060a0c08040e0f060105070c051509040e010e010b01260c0f040b0901030c170403080c310e0108071701060e090303041a 68
    0x1d900308103000c40c48409000c0750100f020014100c2c1c0342c00030042643d0703240c090348802c4102c4088540e85446c46c5901c180300c1280c400c8982000280d61060f81101240c000c02c0029041600fa03941040051131024000420304c40040001e00356520301e086482ca407036100224220070040c0a80d042000a00100000800e042807010545038205c5136508810ba1034070301c044440c001e2403c40f50707000d400e002d140781c401481940f1008940400b0300c02403052850380d600650b81004000c041000451500c0c040d000248050b410f0142c2186010b2101c42c9000d420350001d00058100e5008240158000542d4409035a014424030344010802e04010f40c8000b80d91a2182804800810103028000040005444112800c0460750b0846100c40c00e02c001c8500f0120190b074110f40c446209030307000c0a0601c0441c2032890740c0c03550b504955690b0300824841e41010700b808180c01200040c41040d40d2282c00100301c04060b400c8903403290307415500840e100d00c1d00c0d01705440114a0307400e00007280d10340302e400d01012041c114 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 924370575 1250 924369325 924369331
    0x110f0c0a03080319020d0506040e03040510030e0f010c08012133051302011115131a01030b06011b1101031d010603050304030201020f06090a0f140a06151409 69
    0x9089840340e50f421303c1c101d802090882c040c09100e00c0000c02540c2074015078840c81c0a114103440400100705171800050f50380c400c0e8011564810003030b0744501720042c440e400c2100340f100740c0001d481020300ca1052072825600d12001c0400801c4070000144002204a101440c60800b940700c502c4010341d403520b80080c144d603030086c01801e011140700480700850040d03918403005860b0403020446032610782d0304046691000b50040340041c5080d8800c106e102000102018240d01d00400e0a000fa1210011084403551501c000c545a02e040400004503c00302080c3d18004c2d8080c107080c07012480d010000401c0210954451060100700c208804c012411000030740100c1403081c00d0004803c40038404144490910040d450295801c04202104016004c0040d20449100382c0131031b4070701000c00d070816480d84421141980d0b01d60001d10311001090307004000300d181c940100d444211800b503c6225604000e200c11083d0360341516200b0001c02298a00d00100090101c50b000f0a0026001030005034103140103 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 924371825 1250 924370575 924370583
    0x90303050c150109270c06081008010f0626100506040b03101d190f06091a010f05010e0603010b2506050906011502030a0c140d110f0c0a03 61
    0xc11820180d01d000c001d100c6044424180741c040c50743c0c1da4556040600040a4444807861100595460340814a100001d0070b9900c2404009503504260080354031400042c4070400100c00c40000049410003841400c4034112052004246c6a0828942034002d019002c0b0006004284c01d00c101180ca030041011031010821000206441e1070b10380020300036284000e250303540b50040e00300e203031a660140d034004900250701c00c0901c101100c10f01c04107511142880c000740c651002d00ca00c080002900c4a5010340c2c21403082c0c400003560031a03502c1e080820072030b00043c01c50301713074a000050162030310003540302d0700402c000d2800350046001080440e0703160106201d0301442c0c10001c10702010a0640000211044020465840d100f0781c0c0c42c00d00001400068400c42c070240100c42c0003040c0082c3c00c81c0c010502c039640f6001149002ca961074100c461215004044d103143e400a101d4940044040c42144d10200c015641e08900708170350242c242c1002d41e25002183c19a000c58520b5007207480e0100c000c0300322900 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 924373075 1250 924371825 924371827
    0x6141902012004051e0a09020d020f0a0314010902030c16020f120a03081b03010b0315090712060b360312030a140103110420210a090309030305 63
    0x2440906a026100161190b40c000c90511103035009511142c0c00340c422210201d4410b240365890041c001500d000041005130400c034814018845840789400900d074a0599407001450049500c1440095401c41424040066101c101c0100d0902c0229403d50240c031002500f14a98180b40560750110b01c200c0a0300c90540c0c0385202e0f8001503603105c3c03841215640b000303842004401880d581e002d4440d00c00c018101d01080d40034000c507500e82040c0ea00d1110f07a2000102d9185940d08110011109810003003190010600b6000249841d03180d1904450003054292181c2d03250150600304181500d0840c2c20811041c0c40034081403c00c50300f00c10012101d03400d040d200b40007140020150045100e40d00214903014881d80c5035405003034022030700440c030170b4550704401c0110b8980d0342d8417240e685000384009400d030301c1c40c0d40b00e0740d03c1854a507001c80509000391440d100b02c814110610080d0750008000780c10360104056003c0066074040b4280782e407003c1c551108000300d005a0342d0162031321145000140130408 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 924374325 1250 924373075 924373117
    0x1116050f03030f0301290910051605150a0f090b0610050c011104140306130b2d041b152f0106030c0f03080f0a02030717090a0614 57
    0x20140215038000d400d5481c1141d81c1c3d038580d507a400c4e00000c8102400c0302200c64075201d00c6ca55605000356100c00100070518100600500d104480c150020080034500b00540900000051070400c502005528a21210b44c410702d0581000070803112840c0741d003180c40c3e05160304480041c7c61461903562000044503003604240d900c21040354079009904c500c1c0107561808406004048000300940700b00c0c2c0c40b800089000d2103240050607282d500946602d6103500b91220490b001911000c036007540845600703241401e56550051401e401c0c0b42d83e51500e00075100d030206220074000c07500485108210040c8201c0109442c2c00301985030040455040320400140c074488441351400c0511562806200c0d1f514541643c0381030000e1030082c4220f100c01c9408806035034002501034a00301c40e020032260000f04031804e00c0800c84080e40554011111941140000c000810000303a448040c40101c2110b0039080da00c0300140004e02c01c032041150400300510941d00d0b00c0c6081c0a218074201c4e56403070f10030821811011 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 924375575 1250 924374325 924374329
    0x105041a042004080c100c0503090d02031c030510080c1f021504050303060a0602010e0d03020706060306090c03060609050609071116081032040f211116050f 69
    0x9046110007000c2c0400140020034104c009100d801d111002c4592000d0803001c01d20a4a000600740340040c840e4005001400300c4e0f151806002c0c40250015050351410b00c619813425001c445104459008030f03036280e082c000821030300903825010b042c3e840300030407801d41403800080000c0802122202204001c1e08440c0c25940309109001414140310344540c1d803800c007481c0090b01d0360070072141c2d07502418028900003a40c52050145150030420386001e0b000714a1500300841c083c1d0f114440594200d07450789030000002d8907500c80c10151900900204500b603040d460030300241e881c1039000402c441d0400c1c0078045aa45c807403050719002080e42c02c103000454004c0f888603080c03009900c240c56000c03886140010703800174040f9044401401401040045444200c1c41349000c9005400410841e510207200100c02d5218034140340d0424015030101001c14020750b21072810440d6080b580c0c3e9000c0751941c1088410360807207190344c800f0031030002a080ba0702c13040040925a13001c500c101c0e403003140b403004032000703030303 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 924376825 1250 924375575 924375611
    0x4081b0a270c0e030f010c0f0e010c120203040329010501032d050709080114041b0905014713051201091a101505041e0e0105041a04 58
    0x12048020040c8850101c180015150f4614040340e1070107801800701c2000a0703001032052844989081e2a070800099401100b111051a60324600d810b0044d1a80e100d008101c5021b2012001000703a4015a034840c207600c0d2103005142d00c000b41402c074a42d181c080c550020400c0b1950340c1580e00a18001500c8d0011100100c1d000109154aa0091a040d845036114a0068201d40d2094450752034080c1c0059652081500306c3d00000d11920745045000040b4000030b03582d003040c85000111300000d1043e00c0d100c05c5980200e5800381e1018883c100003400c984042c00384207403070305541c00c0c000c010803103100901070440c030003419042c1c202824802e0000e007484856400e0f01282001d014050504080213042150041c004e0840b03840070b441c01c0c2040082c1300e5654009900407407154818a03041c0360101e162120003040c00e40042218807d01405220210f40340421426811403410140082c0110601e801d00c0c2000070740c0c1c1a089940a00d00b4410420070a071088403441801c1070081d07400003076095125201ca16a = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 924378075 1250 924376825 924376889
    0x5030705031e07200705150d020903060903030a0515030c0d02040f0213051806012007031e060c020715050f1e1b010b09040308090705060a030204081b0a 67
    0x5100c1d2407000f44032065502074001807440104c100040003c11145031090360b600c440380320b01a40000c0c58640904003d81000c040c048400300c882000d820014145c000a040c100c00b02d810b041f141d440801085102143d0303000d091381200c24080e003200c600c81d480001c6911540c00d00007050180c0e02c4002800d086441d99032001d81c204080343e808544030b11020011210644141c07040a00c0784d654090303481c1981c0e80c40000d8600643e0141c41e10b4010f409801803581049094003040700d624005c60b840003021070041c5580006400e07009107005002c4074180341c000200d80ca5018a6030455002102c10703c00d442410400d085002094181143c44001c00311100b80c3c0c0303216507502780b0301281c50452007880821000c0c01a081100c13035081c9071404031700c0001d00d44c0c0c200e400c01c800e0b5540c00082d880206000ca0b01030350402d03402038081010b8800c11901c030000300303559a201d500000000b95001030108074008050140d05d10410001c0c041d4601c080c3d448002858514140c012000e042034281c11540e0a98100c0600fa56 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 924379325 1250 924378075 924378121
    0x70c060204080708070503062809051203040218070e010309050f0d1106010914160c0501050c09010207050306010b12090a0507030317060103051e131a070219030503070503 75
    0x1503140d442c0c100103600d6100300d00c200c0350144108800400d0310724001c07941ca0b215101c020f000d1207403c5050402030002d1100c4400c5001000d0750f40395440e0100344240081000901514501540e9052034414002d80c00c1e03124118031142c014160034094410307448410b10503111001d1030041601d00310b60500d00c1c10203e520a00448a12459414101d05038018200700b1402020034191840c903070743c43ea440d0b02903c051074814041c44c51a4000664400c0c1d0320108002d111070703186401c083d41d0801c1d5541500311103040d42c00c0c0c040d000000c5641002c641c1c1c10081507000d00410f8000d0540c1d540761034004401401a2214500101d003410300040c0384d4070040003c0b080c482e40050484a440c0c2e52420013400c440598011005030018030070008a06500030b0080c40d014034041c41c007e82c3c4880c814031444101da48050603180300e030110410300e400400d000c02c0b001e0849505900c0c2c204840c4c1020790000c0c1c940403004051000c0d90744000c0305079000c01e40003000d49901c030100d8140701d40d0740d64540720302c18a00c0f451205541 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 924380575 1250 924379325 924379327
    0x170d05040515070504060f180e07090f06030e100c020a1a0a0501121e170f03011502060f013812010b0f1c0f05011512020301030b0c03070c0602 63
    0x148280080c01c07520200b540120740a4070b0b2180c0d88121900d116502540c0003180d0b400a9485c0002e01c210303003506548040011070106241c03266904a003141042d40c0d004005009024103128089020b28144001e05880c1010007141c9081150f09031900b03c10500700c403145664042c2900802c2c024440c0e1100741c1e078003800e035080c2c0c2180b040b121340084200395418144146000b0020898101d0022999200750300405113031300b80c0c00000c0c5074200402e00d4200c115400c07090804c0a0940e54085805450202c0f015440070b0f490b50705140b407c0d0881c1c3d120b0b0100c001154880014081e80b5200032078504e064171041b1914554211540c1009403903025900d0140069051380103080442403205e10281941981898031519180d90361000a0050700032403045081120040261041c07110b1000d10864030300016000124002c1002000384007122402da00001c0c078a1919007042c2040c941c03080d0040300245407034804504550554807440d1710401c0040c60124000340000100f205640210030240c4026441a025 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 924381825 1250 924380575 924380581
    0x50c0a050307090e070b1210090504030c021306081c030f0c0903080304050c03100f0b2d0d02031519020f0d0b040e0f1605040203091002091c05030403020114031003170d05 75
    0x104034111000c403808d4442d006400c40108a01d0300c01e0203a1030040e50980d60f0601400401d0b003c100345525240032000ba465507c020008080c1e4007803000319603100103d01c00e202d04281c4800064291407110b8011900c0e145810f2010406507000111401603c0e00640040d4072543c46140082c80c001940c00e00e141d140c420354042e41c4441216420400125032a0081480841079400501c443c44241b030b10003d21990540c20000b84585004003074030301005005048181182d4542c005ca8181114005a94071002c81071040140e0307200c5054030503011103820081107103081a1920303119a02c0c000c8100301a80c4507161349204129607a1a0002000d4a90740e1065440005140350065521020852100c8011040a030001060b140510a80f4440c0c0b40400c00780505000b40c1d18004000c0d8010030100c1d0f400151038840c4200390b90343da10700074a6a48910011503407281140005414031802c0e44c9522110b240c00c01c00c00400b001c0042500044950042c1d5040d144090582c000c1101d0103020464001d0300d2a007420 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 924383075 1250 924381825 924381847
    0x1030f0c080a081306020105060f01181d0a110a050a18091505100e010c1e17040f050f010e10030609020a05030f060f0307030803060109090e0307050c0a050307090e070b 74
    0x201004c03101342c2081d854840e6610340503403e0300c20480d0020707440354411070402040e5010300941c640c885503510b1a40207090300d82c81901c00942d618481100782c01e0011080040c80c1c0d55601c40e41c02108054040030b400c1c0b20300e4000040c95841a0040d20f020802e0300c0940403e02e000411040001d042c0b84002880701d900503030680140600180f00b15407051424000e80d040300307800b84401c1040d04a040c0c1d01c1302449078168403410032401c85581c40460007010b48200d08080b030fa80c01407030b00800c01550f1642d0354403443c3c8081d080140078543c12192040745021a03110040e03800001c88482c0c0c0ca010344011445641a0b0030541c001c000b03d500600d02c1e2800010700c0d00c1d2095021005510625814640c0d440c40c0d01c55006101007003c0f034010342c81c1c1581c0031803000d2000c40d8400c000707160f00500515101c1c14070742d04c0b411107a054552440d000c0805520104100b401c01005201c001d00f0450280c8032041d8491601000940d40d8a99128241c2e290f6900d00743c4003c02c1a09121031030103002550092650794415500c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 924384325 1250 924383075 924383077
    0x190509090901091a33060a0903030e0f010c06051f06050909011d130f02040c0c050c0910090c140315120c0312090301090b010b19050f0301030f0c080a08 67
    0x343c1160040c20b2000300f061990075021809000e00c007180315000c01c020f00810f0300070503200c6012110082c0000079072544801d54604005200f0710b00c013540d605000e94034601e00900020105098180b286c80d81c0703c001c44541c0d0b803001d8440701e1142c00030b0700482d00c1c1c0c4843c200304080213003200740780303e65080e9400c1c003040040d0050024900600c06032100003d0b070b80c1e1884400020742d003114414044c00380100c0030404401c031a0b20040010750044050392580c95195000400b02d98081710040081008034a000090100034007001e1040801521514000d00d041c1c108003480808a0240301c2c0c0b45591600750b40601c134403850f8a01a140c4a00c2e80156403414040140b1210141d660b0810384038005241103050103810103e03801410600c080c00510f102c00c01c0c00c1d1a240143c225146281c2c05642e5040b0340d0000c0360308031011034000c0c140d140c00d003540c0b0f06024440000c401f00f03000c2c410041c024100000c01e411180c2e00222411a9008205400304d0a0039203018034480c1030f5603110418a00c9920036100c00e01000c0700c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 924385575 1250 924384325 924384341
    0x411120f0d0206010815040302071e050405150f091801050a0e060c072f13050103121d0d020312030a0b010e040606121d03070f0b0703050903190509090901 68
    0x411512101e04072081280d545400340102440740e045050740e8421500343c4454030f60050b1090040d10403540c0c5814508420001ca120305184c0141200400c00c0f4600b0144034040d0010141c0b40e00d0b05403910719101241c00f0300d00a0800034060014207001030754002c1d624134269a00e0300030703400a110358200084060050100b5809840aa009620120b80300350040740c102c40f00c0750385c40011103a40c00b27960400803175880d1241e005050300703007140e10010744030350740b40082e6402305501001c0006242d41107040c9800601c440307100010a1000c1c02610701450820403100c3c01e00b0280450b12641c0c0000c252003c00d0801c03010900701284000301100b44034140d0702c20340005900510070f03662182d10004000802098605521420011903500001c0910380c1c105034000c02002c2d110040c1c02c58500c0032400300149141d000d040240d03070409003260034808024114841a03004401894244054100b0051080e182e02c1750b242c4110762420101da0340001c50f40210280c5040990080c441c0c0303854580908000e020700b200b0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 924386825 1250 924385575 924385603
    0x9160908012f030702070e100b0a210e121602031e0d2c010201090510021c06360c0804031206060e01143c190503041112 53
    0x6001203101004010b01507a11a050640c02450000d00d8102031051101015001a803607501c240300100340c07004003c0081110034502e40da000004111441171240550031803200e0810141014003100c0070000014480740c0c007820390b440f2556100032648441d01c640054074002500343c00b4821100712540c600020b4114010600c3c400c1d18011090201d084566951400c40910031241d1100d1861990507826140035000c2d1041c0000607840082c0c0d140d8510f081c0012003050707446074000494804a5100c1c4050a4458540100034007261f410040c1104160240003000c4154400030002c038155441b2032045d1010011010030104001c522001d00201407050450307050340412108031000d1904910f600c41c10b011640c0f075658448402d1007d400440e803104064646009510040c000b1b00308461404006000702c04480d0381c1d034880180b0b24402c0a200007801c036a83d00e41410280b00c500c6c1c00e00e802a80038140c0da48a80382c02d070307030343d50351850980c2480c15100f00058000c1c00c0350890747c8000000241c100145520 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 924388075 1250 924386825 924386891
    0xb0f06092404080f06071205090c040504050c010e19030b130b0106020105060f01020327040e0601150e03161a040b0307020a0b0117032d1818060916090801 68
    0x1130b9a09a41ea02c1d20103440b100000303164036140109480c0d0030752001e0b810103000030903107040880c400c00207815600107032401e94458101e108081300035030304081c4030310080401b5500d900596180d9a11071030307141903070b2001900b408140000182031080c3c0c40c800e001d4050780301d068100c055031107950082c02003404503081d85c020a9404d00d204260340c00081650000030722481c04000310036491319544400d50500b81d01c95046030712000c03039510101c02845030501030301c1611130801220b039410310014001320b290500349000b03401880050504d41400640d039000d680c5841100c2c136000210340980b00039407050342c2c0026221074000c0300303108109502059000e021801540d00c0c841e0360340ca03607a11218142e0841840b8441da801000101b05d8001407001c4503601007180107010050100c000c17507807000e5600400a4000004d0b42c8001a4a1031030080030403011580100f40700a0149000b5011503001040070307081d5180c00030340c85001c407281c9201e18140009406000028007204102c10300c1807e210912000c4607603030f085 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 924389325 1250 924388075 924388093
    0x50705031608031e0903101406010302041a0c0717011a06090102100b061201030f030f050a050a0c02030c150702040e061b07050a0813030302060a0b0f0609240408 71
    0x14100501e42a036051802451030402900100290742803c44c012005210040c0b0034003103281d80a1002202500908901040c1d983d9100341000d4402402080d0394141481404244044400c3d01d901ca05c1045441102a40e40e545003180c0c0c1e444c05015078043c580502402e07154414020040d0070420f4441d2640141100500d0508200000c0d40a0100308500503030214007001c19400c0982c103c0d08200340042d0000d880c04001074051403031316809030025140705103a0004041010b40c0b0404000007240e0a107440d5040c43e408040043ca1807003003000c00303800c00050019120943d0780c2440340e9040307058010710311280409100c4a40c1e18a401203034041c1d120b140782c048040f404210101b2024440c40c50740d007418142030b1543c240e40202d41c00402c42030b1420b2142e070080c0300c000381c0090000e01000040d003110b40c0d8a14610301d0001d01e00403008100c1c442190030a802c0c0d400689943c880004c00c4502203c04c15150000080403880303a540b05284130440f1401110300718117031a004001001036030408019562240 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 924390575 1250 924389325 924389353
    0x3090c2403011401031503111c0501090803090f0106030507030b040629010e030105042607050304330c03050f250201030e150a1a030d17130b15040603080705070503 72
    0x70780e0502c0b014184900c148c40c044094a400440b40034005036100000300002d4464480908440314058200c5083d100007051083c101810400c000903100d80074001c0c0112400c41d030313449850ba182403100a101070490b001203400c124068026241c40403071121380d0340221651210390841040c406001c640890319424001581341010300400384aa0740144030803600d07003606140c0b41c07901e11034107040b460208401c0c0404c0d0001380050001380018a1030420150b80d042d8580b4810b1705803c4600041c00d02c0f00faa0180d8006202e8002c0d4801e075039680c140c107000e0340f1099007401d190810710031900016510545680038480004289007801d054030b000381e034104841d140001d0700f155a2075559003482040e40408000640540b45600904143d00068815030404404800803e10b4900305042c49008541c0c140f858800500e4684050740d4464080c40c40c1d01c200c0c0703c1681345c002d46010064420254400b441b203109000e9116500b20200466000610550385c0340341d8145030b230325036000c1c3c00340074840d015101c40102c180c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 924391825 1250 924390575 924390611
    0xc03200c0a0f030809060c070506070f02040506100c02010e030c0d030c1202010e07090207050c130e0f0d140c0715050309151501080a0f050901020706050c03090c240301140103 77
    0x20703e500c00c01e21343c9090350102c100551a000f000b00700f800740c82008408221519480050101a403140d8001d411a00c0e40d48100010384200405203809480e01d00000c0c5220f50340414030550840d02820310032071441180010a0518992000e072036001040129102e04050b070200c1460306860080c11600c401002c03045080342603415a03004944c4680c0440410702420030036034010060170348140d0450b00c8180000c0040740c012020100705641055440502c45121301c0c05021100d1405400809428030b5805050083d140c40c2c2d020ba60201c103000d0100d0f5411071188204540009044001080080d0203901c0c40002c16551040740d050300c19003e140c080030603484a01442c1c0780180c0f01d16401600081c0200011229400020800044203848040114003000103125140c00b9a500f00e0025a50307198900b03141c0c041d41e4002d07010071140c0d1030800803c00c0c40c0302c000c6a052540001200c010403500e14498851070a444941100020240c0000000913414500c501c82c0341c3d4044280c0b400e10103810650120f07004 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 924393075 1250 924391825 924391829
    0x603030901210b2706040c17072304031509050706140c12130603050f041403120a0c111506040908040b030703090b0f040c140102030d11091903120c03200c0a0f 70
    0xc91940c209140ca0516003080301a48103c1500d48402d455080034130141c000d0602c07244555000b0fa00107018400c0c088102600d40094851040038410903c85a131102e550705900e100c0c000c2040280703900350b034b400810181142e804000c43c00c00c9504209078409106d10a600040e03070907100c14000800002c641d40240212440381c2c1c60f240e03100410341d50704d88400c41d9181900380004041c0c00100081c0300c031351006007200c40c0210680171002684885d10040070780301c46210b1440d03880700d030700c001c07105e0031940c19015225500060548011941c03074803528003c01c0303501540c1c1110044141c0481000100c580c998441c940040c024001070405440301074180500d900c090701d0240c50341c09160710070b001118a03c60086001141841284d10f0054059015011920200c06003400300d00d0009125002c2c0ca4030b50f6035250603203000a40c0003001c2e881d40e6104035100b40080b58100a0050380078500007854059079500a000c07202401d41900f0b4011204c02a40394606415450710070240e640010646011014030441 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 924394325 1250 924393075 924393077
    0x1e031a0609180606090406022118191209032429280b030a0b030303060307060c1a09060402030d02010b0105220b07080a03050603030901210b2706040c 66
    0x60303441300003e20444200c003c000f038407015004c108001c80c9a01580d01ea5400c180041c9aa0402e07081040440c0202016420006800d42c4404a581c0f107011003268054000d6900c11a0400e001103000000d4070408155480a841440074050714051a500c00006032140e0001c7d0f0342c00c004080b100b9602400c020a002c03200c0b141140c0c0e100301540035080c5040056842d4000040c240401c80380d403014034000359a2a001a041c250000c424814241c3c800e0080c403c0c41e0754202c000d50b00f50700e81580402e545a100741324030010800c0e202e84000900880d440d40715806446071020000c0741c0742108155070b6420069400f207003c1d100b01c0e64440b8a20340f0610446444460507520507140112368901a1018111643d0003560504001000500d031500e0070001e051030340c4500d00d002d403aa0100400501142c4000301901e001c0d410801800c10346030790014030300300c1c192501c913201d0785403140000c04e650040118540e4270b900000b00201c4020031120003040c01e0b00d040d4850b003955189540b02028041942c8071602044 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 924395575 1250 924394325 924394333
    0x60c050c030303011d090c092706010308030c0d0f06090603031e14180d0302011b020c0d151b1e0302040b1206060c07120b01120c1e031a060918 63
    0x842204811046e07004110641128207003507907200041c1c45850280c0e0032000d021480020030303003900084102508a072000c01c0140040d985103450398500b03407100034802c0c260240002120601041e481d88000e81184450900304003203519000e15900810160100b5008154080103024101150359044803000f041507407011000e208015a402e40741d04040c3c110307480c030021201418807a845644107110b40c40d002e60700106c4c0a100c40c0c40b0800c5141c3c00108188110b400006000f5030648550303000312505607114803501e01580000748884c00800040443c00d503081d50340440c0140b01c1da4071046511038040c21100080728001401e2081c5c0c201c1c4601e11802078500828860b003001c0c070351000481c0307908c400080c292910309484400278034180082600500241e8694070200b105020802282a0142ca14240c07512581c000c1c0340c9511043d002a13100e024146543d03160101042490350180f400110741c4419419900c810544031031101d414206d800c18092214040025400c0d00341941140c5400c400c0c80140c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 924396825 1250 924395575 924395609
    0x1080c09150c0c040f021b06010b180d02030d020d030e030403021302070f02061b10180b06120d08060418030f0302130e0408091008161107080304060c050c03030301 72
    0x10700c01d800142180d1800d004030414540d0030340303850244294a034003202c00141d884200c1c400341d0120200040003603032a40e00241c018000508610125404840c00d10000c00d0219510740000d102d0420b0440001d4060258912800100c0d40005c1d16a0300c4010503101030021692101d0b210340e50303029070310003e0341c0079410702000c01c0d02201c680c0c018412107020300c075041031201c8240c0114001f03600040110314108000c948a40701c1d031805002250840c01c50440071f008854015048514088194401500d40410f1602041d011303910040c10b802030354886401c0e12210302c600e440140c40d400c0122030f0b07a409142010010746000320040340c48005107515031264070300e1a1842c0000c400940091107400242a41080b0210b21450894407452240703104111241d904e40e0510140709480d2240c1039034009204510051150424203128602e2100180d442d0404018885075403461620a00394420030950100140114407941c1c0400304c2c0062a005200b02c4084402600038180e80e0b100074071a60a096010b00c0351 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 924398075 1250 924396825 924396859
    0x108060c0d050405160308040f120f02040c0306050301152907030f09090906090203100e10021c0603060c110a080409020304060b03010606083903070c05010e060601080c09 75
    0xb15400034021401c454030044040703168003135081113403c00d603030f00c00c000300b020806070303504640510290901c1240d82d00c1c0120107503207426001304983e40080c0300d60f0b110342c50080349030720903031041d001050001c009000c0b82096841055181c5080d002c2d1101c80c0d00c42d074181d5400949688880d10941146420480c5020360a8400b101d4012007242c0300d0041003003100001804200d64001d000c3e031070b1b0080b000010032100380c0c4105440c110400c00e104208908140752900008008101c542c0f4a03000c00a01580e1040040b07800184031150071108d41c0413626200c004401d00880d6444440002410346481090207081e040843da0b681004000030680941000140480d108540185400502c1030078081504c0c2800c0c0002800c1d51820340040d40012018000c1049000202030181e881d100450344107195aa02c442111503843c02e01514800224800004140c145201d510080d4000c0e400c08006c0080b80c8070021444d44410741030707402c240020609404140e04000c40000c0b2110150001c1c0b0348010004038605c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 924399325 1250 924398075 924398081
    0x1503090318030f0304030515090a150b03010f060f050a0506130909020a0b2106100c02040b061b030301081501060e13020d0e06060307060302070c0603110706020706050603060108060c0d 81
    0xc282501030140da01e5039070303d168040018101640c400c034040c21030304070b9982d40c506000b5001004022294448048040441c0c1c00e4004151459000000811b200001c88003180c0941844c0b00003580c114a4103500181141494039400242c803c00c071368001c80e15549404015490043c0c812229071100100000c000c011841d6000e0303007080b0b2010704280c070540d5039244242d9443e00710f1302c3d0f11240301142d504400a500300e10010150f200900304e505010100d04428000c210006a0343e0082c051036842e4400c2c207455507080e050b80d10725811319481c851106503000c08652a5082845108218491901d12404d1b1045150405040e00c03041d659545602400c002004455214040f030885d296908010054140302c01e4051081c001c00f89100411b86403c0a40905280080301d6004004061040c00306a001604042c0380008484030751034080703050131074011910841d00c5403000091642e440051443c040144580015228400450a86100c7d1303994280705600c4000c126407602142c0c40c00c01492034002e151b98 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 924400575 1250 924399325 924399367
    0xc02010519360b06030609031e04031712070804080a030c03110d060e0a110909070504150e04050a0e1f02040f14090c09150903010902030d090515030903 67
    0x201c094140c04001c0c150254aa4094004215120b4850501d582404002ca0301107030440d6040d030041001e45401c02d0450785902600d0030090260001002d50301e030000296090f10043d6801c840d980e50840102c003211101c1c0d510548020800c45a280b000846907402201c0c3c1c0303841550820481850130840301011402005a90741240a2603070307440300200403210100240c014460150000900c103800c03c0502c810462000340310030402c0e0305041d41c1e03020100403201610303040f410907120b14405407100e040a403024000d5070030180341da030115810b03600c1e075581c407104080501000392800c0089840344075002c0c054520100c0070092175405000c40c544c001504501280344100681d02c014207007a120002d50400042c942e111843e526201142031940b4074205101c0c030f030080040c3c10503070b1034030100c5000b29030765400d49199164078010100b0b840c407068900707403c004a025030090658006807030442c0f000d440000a0b0150781c1c096400c403040821940c24490480e4010106040210309055040d0004441003800f9 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 924401825 1250 924400575 924400601
    0xc020709110f0c10050a15090b0a122306010e010605070c182003160c2a1511010b0a030c03060906110301060804021c12320d0c02010519 60
    0xa01c10400411080b8401d172401041a40000304403001c00710035650205845800c80d00419240c05030103181d540d20070115804035055529400d81c2030f403190038482046e1906051502d54401800206a082e00340070905034140c80b01c00010790b1450f40c960404407998020520004c00711001908240503503103042c2c10020898404842c0030842c0700341550280112901c40501541252000c0203003e000c00b6240c1030b5155803145403170203150031610303615480030118052251807a404501c000701240700d8804400040030345403a1803203614030514200014881e100e5248842102d520782010611503141c0036010f03804698001c80002d8000741541c88090051451040482d4001c1d900c0002c04010000c88016500a00c400e49540c10a494203005010300d80742d544006000900100001740c001505c0821103441c410181d1905140131001c1868041c2c08000c01311441b00d01c0c4944498803004110404c5c0108030a04d0030200c107001075038911606900380e0b0001e4070b00012021000c1424008a08668006032100c000 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 924403075 1250 924401825 924401833
    0x403110f03040e06130e0d03020a02010b0628051c0e030d0509100509070b041203091e090e06010e180c180f09070614070f020907030c020709110f0c 65
    0x214000c118030350340c41070340b00041552504040092618200046250381c55041c1014021044404251601d0340d003400303034442c01c0c10750100740116298801d40c0861041400601850740e1020715110b0303410900f560300c559580c014a0130703c0c41c1380114415000d9800710507440c0018460b0bda003241242c3c0140604c801c0d2042030780b005204898211101b401014002c0c1c03201406444418010040c1c4000e071100246080540d42c4010340400c81400320004403412a002e031541d03e01c030300c1e440d4903044404003001c1e44030143d00105401071411800110a01c0011100816400c12a00100c602c0c9151622000d220700c1c2503038400315000a90700c005078400c4030341c0002c3c180c058034000c604140c0000c10030780c15002003405c154003a0302007104100f20f40c401c1c1500b00200900405c0451f1504800801480c4440181184130350041000d80400108641c1d007100d41e03070300800701895881c014800900404c0000300c0740e401840340f9000080c20002900c103d110070000c11503d5440d007120704411408551100c0031800b520704c1 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 924404325 1250 924403075 924403093
    0x121302100f092907080301060908070b12061816031425020715050406031d0a1707050118020906190b0307090e04060b03010b100801090509030c1005041217040311 71
    0xd8007401020503d00c1641c3e17664a075410310500070802144c50700144600d0b44001c009200303402c9040300340c030360040118174040381c1d641d6900041074134002e40c40d1442c403072007101130184000007a40001051060a41d507070204001d0280444050b018801520b907280c8106240c0051140081e03d1401c5141c48000760040720807081e5500d0703200c0140d400150a007000104045007c0c40303115454090314881c1c1c16051012032021071107030000e603211a0342d0a0f000b42000c68801c000504420010140c0e409140c0210003000041201406174107680702c1d0358400c91281c284032001a040d450034032002e00b041400d401da502c0706a030500440c4903066001900b0325040c40240680002c4507403582038100c2c0305a00c00e01c0c02003443c009540030305007900d0702d0842d0b10b80b103804024004040141d204007503c1c1155030104000c00d26840c1e410640e4114400d1079680c54140c004d1104a28a001c440d4214500441c4112880b09401044140c1101c41d02a411121158883d40e10081008244100c803010300020015040e906042 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 924405575 1250 924404325 924404399
    0x1d160513050f15071b0b070302100b031002040807030b10030510090c0302120c03013804060905010f0e01080a030804031101141603050903090d02090c121302100f09 72
    0xe04020300131151180d1410140c017060301894240d00060009140180c204181550b0203515082c00040d01600300b03503030340c10401c01c5a03020442000d0703403075090318215503868031040d0700b644808240c0000c1c2c13076504008000c42c04554140810004036a00b0501034400000d030800c800014000c801e0301503c0e0710a05000100140e81c074103601060741c07021200140b4144034810241429144d069003041d80285110710300d020400c0701c01e520403421120000040a1407515030001600401c0350f6000003500502d007070008210740c0c02004103c4190341c80400105040d0382e0302d0069039035a44c1045001000a414103000c50300003400340060500c0340180400214080b441003440b4100c0315411a000c203250b02d54504031681c10382d09803284175006984100038520b40500d00d03010510507000b00d00005d001e042c4240000352080d103500700f03403007403090042c40111081c10000810000701a0208069110394845100c2c3d600c158000c40d5200c40300d880c1501e412000901d88120340400c4020103510060a4418000c60f042c1c41d = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 924406825 1250 924405575 924405577
    0x51c030815090f0412030c09050607060608063d0509041118071106130210170a0c080a0506150a020c0303120708010b041208131d160513050f15 63
    0xf80c40d032a0600c1d05515280c01e00d030040c80c20360176038041894a414410020203611040d03010944805413281c1d5a5680d181c60040d00420b1158051200ca001d03207001d014a660140940f01d0201411280722694102402c01518030511002c03549003000c0c08807034040095040c0040c24542c0300d07005036000304210010b817000c2401042d4411032070074800d4456040003841d1350070030601c00c0c0e10f51341c0500404240c030b0325892500340140c050102a11444040d01017003400ca1041003000400121002c250700242854100203015000030740500b80420500700000c1d0001c482e0307104041c45480c000380000c0e01c04040310387c4c5400552000e50700d44210b000300050300c855074504000a080b541d6000380c80001502c0c244c500200070781e030f040e004421190000c100c100211036094120301012a00800c585987d14621140717284219500c1d4411110a00b4421540c2e4840d003074207064500ca680403501c00240c105d8900301c112241d10070000d24001176580c04000f803280c1d0803d800791a0300054040c00414845d0003210072400e103 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 924408075 1250 924406825 924406831
    0x80328140a030518010c02060a02160f15061a0306010c08041a0304020906060301180f091a04030806060a1b170708071101050f030a0c090302060c03090a051c03081509 73
    0x10a440c2d00510990113a42e4000c80c00c0c21010030000c01103845100310082d25400003034103110760f280d004514a483c03002848485880e0716401622240f0307211440c68408920301d070652026a2072840d0207400600700b0544110700c40d1916407000200d2070359032800019901c007130a45005944840041c03001251400090b1990000010300d201c0d5141c40f413505104020307488000400d801e00440051004000115480c024614003401c15140403d114482c441a8801042405000303040c80d046890082d50309a40e4107034450155020f81d42c0c5d04295917481d0140091442014454400200e1540404d0781c200d54800421150903c640c08010401403908181c038856001480b080d0740004000030138404102d4681682c0c000080282030a6003080f2145606030054080181820b05160300c546440c0d900034412074807880507503030041a80e0b0321409172141042d0350303400c020042c40c0260346407480421149016200c9409080340c080a12283d480c80303580499580001502c0c1c0c481d60304100c0280d80301561000e01c5284 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 924409325 1250 924408075 924408077
    0x207030506153a0813120b09152703070c05010f0801060c0212030d1505040614030303070e13020a0210050a0902090414151f080328140a 60
    0xd4218071030360400161a040700040f00f082c5501c615003469500340500904408001d10380303103081c99411810140403e204078040f14640c1c282c0600c001c10a440d102c1101c00805004d42c050400d20b039a002410f994964000c102914294103140000300c3e2210341580000c21080c3c1c4c2c00d071039500300c014914450301d150440305044500c081c880e20203220070750340f1000c02c4904046510b49050507514054002d04242203541c0c000e4000c04014202d0030854804200301e41c1024081c200030400d11600d01154601d0740054051588076a04180c000920790708004c00314001d040001740914079507251140151402d26040303003d01c0c0c0000c43c0440b5032244120520107010110045c7e0050482009194480c5c400c43c0c00081070001c01c140307071400c5640980c0742d401c03a01c3d600c9a4426a040b1600140100417860502800703615008244e8807030402841e01c100d0a8100120040810091032854403031124030780360b009414020698000c480940203800c0d94480c004400c4060900300a91041c03d0390b54821441e82c48000c49130 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 924410575 1250 924409325 924409351
    0x906040e0903070302010509070b1e22080601090209131503240c0503011d0408040504091415040b0a0902060904020f0307080901020a0c0807020f10020a060509030a1b030207030506 79
    0x3d09042c0c080c010030303a02803186805403855604051110030b41d0301810541441002150000c10306820b0b40004039003246030742c12001c00c8040d0380388904a03c1c841403030140b52801d0003050000a0b4281990083c0c2e48a01030082859424146005021008040c1d1411000c0e01042100c0c000020500c85155105003c8001000c1100803092000d0001074419680c2000c1c10400c0401c010014034414261800048400090f812a25211403c283c1c0e020301036900013962091506d60020104004502c01d011481a81005c0d249014007100d00ca9901882c1140d01134400d02103000094500c0074140d03c00045284020a40ea09007031105012078100d0300203140c00032510400205000d0000c1d001204181e0020400009600c0d002d00030340010001c049082008100d0314001c1050021940c41542d403000305400513002000c98400c9500c02507a0700003081c0c09840c4146040f0110342586004000c0794232256103501c80e0100c0c0c4100540301840025541b600b68214044d80001100041080c0006d50144084410741 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 924411825 1250 924410575 924410587
    0x6081f0f06080d030b0a0609290a030e012f0c0712030f1805031f0b0411071b0302090606090d0b0702011e060e0f090a0807030804170903120906040e0903 67
    0x18044601e01d4904a06c613201d240c3c2c0410203240e01a402000740c03585106d403d1500e81c403020074600c40c10038811080d40510070204114110b01c6e4140e200e000d10851001c02804624000c0d00304101404040107200d0740719000e94180c0c3d00100c1007400170300c0103040c4001141da0f00c50f59040f07043c1c05000042c40490014510740c0704201160350000c16081c1c0341080403814030743c541c41c05000075501c1180c480d52013551640c1c2440b03000c08a8040d40500100c0e817014100780305011421510303184903400f008003150b584100c451038007480700c840399281060382d070b010301044d102c3d4031101d0400550b508072a08907503122107041c204e800000c0800d081d443c002d89441c0c001007807919040104e0144108000da108a51703501c0c00f1420088084c840011680003660814201c155031561216581496a0040b0103400c20000041503030805a2094138148160b0207252a1100e11024041a0f501c500c074004209600d644400103901d440c613091002030400010041c00c19181c65074400316440303001c1049854100726080071800c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 924413075 1250 924411825 924411827
    0x60f13230405162016061b0c0e0c2a010b0301020a020705040b030f060f0f1b090108071827050603071707030c081606020106081f0f06080d 61
    0x9035550348042290144440e01e0401401e184144041500d04108000d02e450458083e1229030301501100810055412044820540b0005058544200340000c0c5121007240340c0d07400030fa58280703102a40061456000c9140c80c4890880050151030310190607020006040307103daa2091143c44003a240407079906a0007280c1394142181d41d248039250090f40100299a20303039a000c02d03c0b00c10b894084400185010855021031301c0c045020001e0101d6100e80003c0c4440b02d000300452910a0000640101e001d0761130400d6201208840c030300c050b10502d402d1002c00c03203560040c01c1d5254061001c2c41d000f215030901c1440c01e0a5602154000c2d42000700c102c02815822a205502c0c40400600c0f403014000c609082000c0b981d0b0350401d1013104070010304415200d221034400d1000c0c800640d0480788412210b5100c4001ea601d40443c4014620715806000001070308900600840c0210b80c90701d005084190003000413850044807140e0a400110b6640f480d000c4a43c0082c0301e21409411540000c01145000000c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 924414325 1250 924413075 924413129
    0x1c0b0103111305041a030307080c2503060b0d15091e080304080c03120106090608071d04020703180f0e010b0c0a06020a050904050c3006060f13 63
    0x10710411066000c01c4903000c95500001c0c00d0302281c0041d207001840851a43c00c00e29000c2c101e0b01265898040010403405010382d03140071386030b0305242c1d8064071241c4515100b40c03c06d052100801504240c0050010400705c2c503281c0c02940000006404400100815601c0c030b050303c0000041e9000c1c00340c0d510124000d01002c2c3c0c800a024409000480380007c07c01c0e2179190031400014801130002e903001034541c11a00f41402580c005841c10b800c2901296154140545045200e00841000030008400035034070600c41c401612500d0f10455001150a1110051001a42c0030782070543c28407900c8020260304d200e01d2403101c002002c0840c0759546031f0f03040803240600c400040e444160b1040051001421000c401300b003030701203a03031311800050707903000c1003801617440d405804400d03541b2614120811030401c50b401c000305051b80c2d00c0300b0030201019603505103488220001c46201014280c4000242981c10980028050a002800d429003004400e035041c071f1035000141c00c810109950b1107001540031070704da8 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 924415575 1250 924414325 924414341
    0x1406010f0c1b301e060501080c040b0105030415110403140709060512060105010302031806070c03030b030d0e06030402030a140d0e0a051324170f0609100c02031c0b0103 74
    0x101a100c0300402c64146510b0070303c02c03400241402c0703051180200b4480140025600d01c9611200074081382da500c3c1c1500d40c80310b480c1d46615000d10300b0503841001a40c86641100d1046500251005040b89007160741401840090500c410000d0104001b001055101807070000d82c4e400c1800614080707040c900d49030181c465942c88103000302d604d212000088400407818505480c800e203001030310381d038501031f1841e2180282c2e400650140500f40034001400d52148240803e01e0007034505110b4280b0311418035640380c0f1b0702d103800000034200008001c4189020401533030000d00090845000c418580c4440c6262a0040b1214403150320803040c0568464125210980b0b01804a8024840038034200200d02803c80b01800411400e5803004e040420031000c5814a00444810380401c00e9a5100c024900141c0c000c5e0130b48581c03030710995580300d8001c0c20004000744146624405000c04005d080306100107050443d8a44055000911412548418070309103088104882c0c0e8002c41c03406180c81c00035040314200c1e = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 924416825 1250 924415575 924415619
    0x30b370302060a050306060403020a0612290909030c070f0e0615030105012303090a02040e030c0d113a140f1606020d0605090a1406010f0c1b 62
    0x120008002603076415090b541242528201142d80e036640c44002407107803180350030081d40900400d00c04900c4076800071400b9840d03140540104602111b020f0208000c21100407820841e07801c070388050019080102c0c645401c1820101100e040c0515000c4040c00c0c100d0307540148614401e094010409080000d020540000c0c0c160780108946400c550b0040b01d900c014091a0305005130740300340b800314110307510f012045040b00000c00d40e00e038201840310340d40f98150141d05a00c15806e09611045140c8080b00301c984240c1d9400c020040011541015a11a1080c44044209015111f0a94400b044402032003404c1148462202070014100003450390721254580070008003c42c140e44098050041780072a401400c41200858480f1246041020001400c40c80200100d00200d001450014aa0011000c0d5442107460341c05079a50880c00004848407512003071401049480031881550080c0301c6038916820340e140607200144251100b00c040580341808000800c50500100100350303081f0040d0501d000c0d0703 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 924418075 1250 924416825 924416929
    0x703020306060a0e0d14030310090605060405040908040f030f02120105060109260f0105071b0b061302090301180204060609030c151b0f120e130b01030b 67
    0x11980102d10300b80900c00d503034000d1101c406000c9499a5030303440308101c001c0d40107860610b16401030502c1a10b90304151000755011300b00000100c1c25105a016500554a0192065040629240400c80544450b500030740e25040e0811021402c0b2150816080146d40a18104426905076205204261b00c981c2c940643c140d02d01014411540c0e4002040b500720340b12106543e584154610440b03e2003108060303107850030301c501c0b5941d140202064002d01d110380700c10389404056108400404201e0083c0000060001c00450001071f02031506480c9103400d155584801030801c000c440109084078940c001481003c6278845d02c1d01e0441c603041c000c0c540a080070f403610011051442d90390b94109400750085405259440c402c41d41050302c03610324070780c508401600302800b10b6020309140401a0200f441900c4030700b0b552050700c007140c2c00350b01034401042e000341c40e1440c00401c00015100070501d1f01200c034100741d10380c07103040394994408007410904d22081407080481244540c2142000040c80c1c8440d4460340 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 924419325 1250 924418075 924418081
    0x1507050c060406050702010f020a0809071238070c0611091e12150406150f0b070f240b240c0a0f12110604020a0603020c01020702062107030203 63
    0x400801d03141d410660200001c94030b030f100c80001740e0240c81c680000e42c9038244045120b00f040342e406004035004c3c81e10001554146902c03641c0c400b0518030740c824054241c40720b01c0e8500140c070700b4200e0407924111608140f54034001e00d2a00014884505940c48030000700082400f006000c0180b0600c00d898216034845413a0070250000715001c480c510b07601041400ca1b60211404649880c42c140c01e00c0c0354074405545490b280b0403c00121001c06a0f03003601c0a62400c0c41c0407450847c90394105090701d4020314030301c0b0510301d022294499507211910840e0710110107004440082d003074151070301490005200801c1d040e040001820210344030203801600c130301a0b03610155004039000c02e4180320720210395081035035200211a01032801845000040c05141e4041996051049040c44071000c4185a61008022504025025507031002960081c0d80700c00e022000300505800391340140700c5d841d40703400003504080d4107070001040c82c1c0040417000508003001d40541e04030b14007001d03280d6100c909401d046003981 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 924420575 1250 924419325 924419347
    0x4050306090f190f0c0602061b12011208072001032d050619081c0e012012030108030a030c0512040813030501020d0b100903031d04020405030f150705 66
    0x880f0348050305070030000c011150018800c9000384107a1243c3c0083c04850100c0c3d6866000f90303542c1013103620310f590758446065189988006404c43d818441d46d80c80c09012a42810001c69032440151400ca401d2281001500001084221800701c600f07400783c1d80501d05000d00340098182c441c03040103200d1304200d054580110703441400941d21016047c8000103081e94404010030b030301e880040071115160032042000120782400245d1240c030301c00641d00ca0340e03200312101000c3d62084c3d5034403080d5001c1f1310461320b03100c00616084440c0f05007988410480b0903003004007041c461140c3c400c3c1c20441c90350700300080841c03800340c050103290880041da140103868024151601428a0000b903c0100001000141070400b01144200000a550007000865485101c3c00d40c0c40700030460019114010144900f88503042c5018000000c11207406484503080d04042d0b490322039600e4041105079921560170b01c80859103480400048100761301d00801443d01c018000954210300b40010b120300100141000221018 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 924421825 1250 924420575 924420583
    0xd08130525270c030b03101505060306010c02010c060204150804020a081c121103180715020d0c0f050706020a15091119090f020a08090d052d04060504050306090f 71
    0xe8060000c00141030101044120041d012800701031b80d040c410340685a188070005d5000350411801d0810040c0b01940e54001e000c114002190014081036007044402c02550090001e000d140c2e104000042c84d0640b905000003030304114110400c00942e00c1c00411085041940510700640ba405000b019100c195040701c40081030000610410404104004070b07082c91182c108078550791113142c1003510fa1524220503c0c6199a0403807100062150b8400020b00d95008030721001c100c0d05a0f40501807580e1410f10039103c1e0100d62504842042e80c403004240402d030244502c5001c0e002e50b6015152503001410324541010b21505400c032060f02e8514590006905207120a0307183d8002d40703220812140303440c0b0014101c0c169503c0104898100381125503c400141c0c000c040003034043d121140f060300d803510102d03960180310010358080340c81002485243c801d0030780358680c0310310b01d41403440110803400703200519a0010340c400008640007141c144042c1ca03007845920390100c42c880080008100a20f4901c6d65 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 924423075 1250 924421825 924421889
    0xa033c020d080a0908010617011505060a0507020a03020d050c01120510061115150a0605042123030417150a05100803071506060801080d08130525 64
    0x3040c034001034071003c5980610070000040c10040020084550740e240ca0074220303010310500c6900755103400701c0400200c1400c50603030284d0703801034003d90504440880030b581c141d0040744140d80c0905885000401039940300b0240345124840c03806880d40500100024000e46a40c0c0130ba40841c0341464204180c05040410b441c0403102c56150070f6140900c9034a84c00c0c240040f02d90400d00c5100540200300038200304144600c6c00071015039103110843d58445048840b4003075801442d8140c0110b800924407080c114512810035801a5000c050400d0702c0010388104007284c4045002d141c20102d400c0104840101058040103903001c054611400046414442c1c035000500d080c2c0c149a80320040355100d00340303800c140080e2040604503551901c550500300c2030070900c0d80700240e9440c1000300225005218980d600d04a4040c0c070000e108800c4104400c1d1103c98000304440200b10302038130300070042107040003001c0d42c4c42183d5210800011003101c0188100c05d15030005410201c24641407041c1541e0781a076004 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 924424325 1250 924423075 924423083
    0xf14010f05120f070f0e09060d05010b0307090e2407111608010f050633090411070501050a05090c041a06070c090b01090f03030e0a033c020d 62
    0x5000d5000c1503050310103004a5609851692070341c0104403401074540c6007103001e9601501e070090b404c0c1081d0421540d803002c051100d900144400081680c6003001511180081d1080002051a0654801080ca0622960700200099450300400802e01c81c040c0010403405560061043d40c1803c682911071038040c01a0600c1c1c00c01c1a0302110180b586418007001c0b603c85901c500744000c0300c0e62105070724081d0000c40c0c5400b0042d4507000214082d443c1171b0301a9610442802d1b07001d0100002111140b44044207124005449602040a41003135a1144181e4100d242c205403440d841c1c50540c106207085800040c0407005a0b458841403000c0c940000594000c99801101c02288056249100c5450b507045000101d82007480800c0b0342040000d40030300c1c1d400b5568003d004201010066004542c601c000b0320455140c0c556003401800481e114003000200100c000d0f0a000c400c551300c0e80d074240e4881c04045020050722218115910030b007211044c8800b000350501c00701d800c0c0c1d05140c000564105c1102c400030 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 924425575 1250 924424325 924424337
    0x140403170604110301080c13060807150e060d0f0f0b0f10090503151605040b070803180a0507080c0603061c050f07030c0513020c0d030b0103020d1a0103060f1401 71
    0xa6081da840ba00241042d03d0810016600da50707440701850b075560340701c041d09031080144054681c50b4001c10300c01c503c02c842c2400c0c01050004e150460055160880304109402c0103182c0003101c0c21626907000400c000b800240b400111024004851004c40d03151148500c03145091984d901c2c03a554038011124000c980855400004034954030041d20511a039600003074040c05494121002c2a4561800303e10404400307034441d000c0b0700360100440d4580303e14000c28249507814480b6201141a00700030715400840d4041e650724003009441c00500d08a0450011034881c5c0c03220310300b8800e02c0018460030700d442900352032490550074010000f03180c0c06910160040c18407101e05540f81401401c001003007103031440c2010ba0300c604d42c0700d040c100c48601180c02440c0c001c140300984040b0f4039105100315203402104501401c07910303e80e03583c200c0151032015050b81c10103800b841100b400c02c0c0c240c418038010403102c3c00b210751115060b80001d802d0302c0305075008004050244c5c001300b0502c8a030446c42e1400380c2d0b013481c0c45 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 924426825 1250 924425575 924425581
    0x100e030a080913090c05030705101e0c082706070206040306051b12070f111903180905060306090102040e04081303060509030a1403090d1808010507050a0314040317 72
    0x89955042e03103000c0e0340b4040c3c4c142200001841800018482030b42d0040c0e003507802c455192010300c9240e1250024505c001080c0c81e1000c10030020046401c01514400e2500d074199400704c1d02c4154007508501c510201800c86c5500c0440c91048d0a80a8070b480201034980da030402d0f0040e00060068007c030302c400303400141c4a2000030180c511451003050755481d1550f4158841c0c2103101209400c031811120030010600c0d0010307151045001d520b07110410580d040c001d2080b4601c140d0500c1102110260880a1101c41841d6a02e4841e140182c2406003500020018003403903c107080500d03280001d40301c0030107644104014401c20141b8aa02039000d500200032507a40c9807900105013405010360b00140c1035524040911101500c04402000302545560313400741500f900701410003d900c0240c8001c60190301442c1103200e0302c1e002e40045490720315850501d00c10580e50b42d4142e800c0d2441114105c0005000140500c0c50907018441e10751109000020642d0900d03055074042d11304040b80007080e8140f0350240c00 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 924428075 1250 924426825 924426829
    0xc01030b030706270f1e23130c0203211b03071107030308010504050a0615230c210408031204051c050a1b05070e0606190e100e030a0809 60
    0xf820035012001300044078015a201000f02c4020450b0240d0b11070f0442c80850f001114540702c203208180d40b41001d0070645842c0413241c500744280d4802500c0e40050320662504d1003802c82d4030560084042a4002d1a5034190300c0c0c0c0e203104641e000c50322002d401c0407270100340a040b8242910302801b000b14030070103955a48031010300355400c0741c803071031030100714450010044101980190058122041900c050040c2c3c0c0380c00c071410781039540c50b00803014261084640a40164070606031007422005506030810080384440383d00030780e80e001c950091101e40c0004000d0340301481c414964012418045080390401d42096091501d902c64030510084926440e0085028000244100748820250707100140e589520a04003070315a400180b94071012030841d60525007004411010076148551000143c04c01c80d00b00000e03040800c00142c00650001000d00040c071074000c9212000c0f4800d0381584404000c40d04c4035003040300540c8120460410015103812040c51a00c00081d00c40b11181c0c0420416120303401080 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 924429325 1250 924428075 924428117
    0x50f0604050403020f0712060f0b031b01120608030924071709060c1501060302040506030a09111009051c02090609070212040f03061103011d040602131401020c01030b030706 76
    0x11091700d07107016555000075907a80e60035940c0c003014030802090080c104503540345011103c1492006c2c0d09500a0002c40f0409000310380e50305503040b8141009500e801c58500014200d6105411a69240d880000c2c40017561420865420307100000c00000d00420001c1c1e142c02c9418051010020002050000c00402d1a4802e50a035599110054201c3d500d5411464520b5524000b801d50090031240d10000800c184e44a8000c130b0301078800c05003006103903484402c1c000006018040c000d0b01d600307031121485d12107035a0700d641240551440d540e80101a50405041140c0e440044c0f94406402005500701401a1505088668005001c5401800300c3d5501d000990a1200e401070b000000480001d0104a4081a10320b100690303006003020001c900c168070400c0d085210a000d030321504180e00081ca050f0001c1d1b9042564000c1c070030000507040c20821954560003132155005560b81d60140c203000380140d40c1c10060304800800900e800e02c00d020010000c00d8552a207405454100f0415070560f880c9040110 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 924430575 1250 924429325 924429343
    0x2205011406061e07081611090117070e0a0207052a011b03050d0b0405010f080c060a05040b0a0905060708030a230105190e04030c0b0903030f06041e1d010609050f060405040302 77
    0xa0b00b41003200c2e4518250060601c3c0e07122848c03103611407200202e5440c44014103841580410070052584605295964802c00780080c00c0e280c074140c081114000262044c000141110710901c4101c0a00d8221151025070b07146d040a858100007460710000322400b10120080a450f8045c1010f6550b03c2e0301c0030b10440a80741d0703007441507041750500b000050744030240b900840450f00c020044e229601001e000300500b071720a20b0071590014400b80400d208207086a4002d25501400781400d5001c05c4e51000450704503003000c3c4003a200a18040704003e01451035005264072092210b009a4501200b1510000034481c1809424040e00448036650001c10b404040b06002e403191606419040c0b41511707005100130410034017114a0700820002c03130811440041640e008000700464208690340700c0b002e10000780000103004c0300540b442520200030710b0040c03085424446070300c11686035107035200c030040d400e4504c10ba22070090701d031620003084049111043d455410103001c4501180c2c50b101c6050892400b42d881c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 924431825 1250 924430575 924430597
    0x7080c1e07051003020f0426070905161e030c090503100c0f0203071208130813140604050109031104090503040602060a0c0f0807082205011406061e0708 67
    0x1900116006100003441c58220740085410714081026510220180e02542400c20740740303101440140030100352000654083c00526015180000425550602c0c2805e0b0b580700e406400d41d50400d100c03034074620340b07004221a806400c110000424503581c40c2d040c070b41203800c4141055540d17280764003450720481c8442c00a010080841d500160164005801090122010408070f0042c8000755440c600204c1600d1070341d50032405020030b030001407806030b0b00c00c1c500400340443d4180420580300061071281c082e0209400306c21031540f1440c24619049401550b10140600c10b150600003004503a070b00000c1c002c203907940302006605291030040807030b000d801400c0c00185540400f180124140c2c1d4001040c070301c11110b4450070300c5202c0c0b000100383e800c07100e000e0003400001c68200014614038003828045421a00d0300f1178410401e9041e24420300052400300049995035140c00b62054079210800c0240c0e04148100d03540c3c0d10304650004050300b492031080d050390b0b80e040c002c0342000501040708152401e011034 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 924433075 1250 924431825 924431863
    0x80a0515030a060b042406050d0b0405130203120c0d180906081f0605010e011d280b040f060c0804050904030806031509190501151508010e0c07080c 65
    0x314540040500107003c08603010314500185406622420203802460f052486c00c4040724904001c0704443d10780c0500c20218009803a40480b402585030341c41281d100b03400c1030146418800391441090308003100344000701c9080e0801e01c09403450b81c5000c62010b440414030f0a00e20240418080441080710f400c0e0b10001c9071516041001900c0480801c0101a0506050400f90740c0c003c001e0318402161010b00030607000441043e0103441c0781d405840b039040d003205140c40f03400c801040c3c040002d1652910f00840030078164071039408030009003401160b002501483c0d03107603401c0c14223001500c611441903104150410a01d000c0146c04d000240007150003400b00500100b4043c43e0a06002d040d800f020b440072030291080441d5000d1440301c0301c06c0203016452880240c00600401020100282921201917519550340c10b080340707a142c845ca440d40d0041070030782400d40c0c03900c5104602034110b24059200e0080500701004000c1e40600314421140b03071990000c4940e4842c0007100803103140010100e512000465 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 924434325 1250 924433075 924433093
    0x40902130c050a080702070f0902030406200901020c0102010920180a0506011d030d03021b0f160e070f12020c0d020f06011e150c020603130203060601090303080a051503 74
    0x82d00c10014108084241c981070501d85800c0d40480e030b581c030341e07104400e280c00d000e003024070811445800a54106001d4072002c60007a680b02c444040d0401420b100580c60140059014880d503014042d070900c90100340002c0100150a40728911002d2000e140040480045c2c0d8005020360b4031070b8813078000075500601d1858a4907241d00050000c103400d544060114189000b202223078501c61075045048507020b0042c1c00000580401a0040e40000203d000c1c482c5050800d25106a010409040b06e50fa60000030140c078900e02c014411900c0258210503010100b207801c01c40010b030480c101420425880c81d0a00d040c11003845500024040d01d0318105075405110840010954005072009221100300180c5005981e1000001500e01a0b460380203080140843d0801c030030000054941800c2095080c0240b144106900040e200e500858011440d80c00c0f160100c01541010007455501c01002e0071f00740d05960039034a000d0701e4528010a020451078035140090150030100201034041c803005421103041207 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 924435575 1250 924434325 924434327
    0x1051903020d0f140c0a1512050714070c0311090402370b0705070f080c04110408060112120503010617090a02031606020c150708031f031212090b06040902130c 70
    0x103d048a11107105620201d00030554281e6805290f540b809148c0307031b08042c2c4c82080062400342c0f00003840c8400b800350900350f107190a44224000c048a5105d008012091411841e2204603100b0320032460380104200c50412006856000c130350241a140c0d0041001004036101c3c80b400700381d28140b00c6040c47c49101c6400600b00e241440506682d80c13050058403440364035400b810500ba01c3ea0711403804130741d000c0002c0314207904069006601d800b0851000301e04d01034031543c000e8034200081e03001c500d407a03070010401402d001d50204880c0600f0301518045195514200d002480849043c442136185408076000c1002607900304241c100041d8007500340c0d1000740c13003440d05841000541c400c080260164045a41c0b107441c0410950a0000b800304801c1c2c2480d02d19125150550002810004000c560b0a1000c02c41e003201490031004501c121406080813036030b5400249090201c104100325075007071110303150028803803851207584010140d9000941c0510790000503042c03e4280d10222000e45401d28402590f = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 924436825 1250 924435575 924435583
    0xe060607141c1e1b0206040b0301060e011107141c0c06081504091505041e060605040b1e10020717010903030b12060415020f0c0c0901051903020d0f14 66
    0xb440c001d481e00310041c10f010122880b2100e0104a0400060000210400343c0303075503a150030407281c0040c1c0f072582030585440d40b0345150385c000c2e08120042044100c00c0f0190f5a84050700d8074120a0300b0340600f01492074070300c070340480300304550540c4d100340d044401c0b840003400f6181c3c8c030403860781c1c0041e61124400c0c0d43d441c01404188050781c0c41d014072164a01c40707201504140c0181e02d8190780c040c4090001e000080c1c00840185006001281c540c44040b000c507001c440d85951800d4024006c0b180050070602d0407042104652400c5502409850a640300120210f1400b540d082222b800351039228001da0506412414456144c0010204000018603614200c0c81503025541582c840e8508005041d90002000301241c0c60b0f0003840807079880000001c001903905030a10b4282c840050001d4200b0741480704a06207034014600312103885d442440c4004541c0b4000c014140102001d403440c600310180e0780382c0c0f5800c9075503600002e40561044211501041003c014803a034140c1c010264102c074031034659182d034503 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 924438075 1250 924436825 924436873
    0x32040212040201030e01090b0c0a09050d050601063e010b061218010905030304081e0a02030a020d0e06040b1303081c050c180405090f0601060e010201050903040e06060714 75
    0x81c54130403245105c80c41442140c032859040312418100d42d552140b00c035400d910107840401004040d40707000403c0c0d01c0e500c0050f08014821000323041503604010004000802081d80103914031301c0480d01192004c1c55444114a440c09400301001084e4000019070250862210594014200096681c8a03c0d24401b09074080c50602ca014440d8414204c4a10f00341c0d1581c00010307046810400214001908210007440095100c904c20b0001c000409800000f5401c5910038038003603040094900c030b415038140000d10001049082c00c44150310308501080d400e02407030160048204c000180513102c024030400c4c040c010743d0701c070f43c659a6910382810406d24414080000200703a0342030601103801c80c9041001e88000324518041c810540032014104000b609002d019510980510300312181032140c1400814081d21850312515404800c500009003140c1c0018443b002d103401c02c1c04144080d45152142da03400240403203030545c5440c003a044c000706141025640002600c0f502001c210a156110301d203440e = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 924439325 1250 924438075 924438077
    0x10804020d300201061a04080d08190c11011b0906030c11070303020a05071d0412030b0d0b060f0d0f030e031c080402361915051932040212040201 64
    0x880c00b600c645d9266211f0245005480d550b4000d403500000061183d054980d00000052154031000760b045c08220841e10b010102100040610713405141c1e1203801d0007091898122096500003240383c0d164001c001040c00d010398410103464817040c1c03900781e105048a40341880e50400b5188041c0d50384c500690344070462801140d4a006407500052000e00c80b910a200c031011082d60380c4400da840d640c03603041c202c060320001c0c2c0c14555610711500c4180c84210452055501c58040417220b824001d042040303000c1881c0009110b190228064000036683c2e1482d10000356260400c415801c03201d034002070a280000204502e00c261200c6c141e42c40782e90080180b80a50b0007a501d62607050f0b1280b034980c141d03062036002d04805e00c0200c007007140740d4514250307202c1e40804803101c0c80b1003030b1050341269002d880075035500d011090b22604060280785440300c1d400d400b040501e06420222403404d41240300c00c1a80c00c0c003205044260800041c000d040c0e1030010003903110014000c554a4a11501d2070100400c2901c0a80c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 924440575 1250 924439325 924439349
    0x1504060f050301110f0a0c150507030506040608010b0102030d020a1b0c03060c080108031b21030a06120b1605040e1f08030a09030f080f0301180b010804020d30020106 73
    0x4280c00425049844d80031303a01c45c03d1072400e0b85400c001c3e0b0f490f0a60340402c540400542641d4041c4060f907109403801003207956004281410310404020946015800c1002c403a4074200c061040d9a07000400c0311480041c122002da220701d640001541d4001419001c9811f294011000800300080c4800710790a40703208003000c2000503808201190402c4090240300d5050313008001150f446070b4421203440880e24160101c6802c81c10b142c1241c070441055194090310b0301f00100c1440082d100901075800900403d400072440c00c44680ca45800508014210742441c070700c0180f0003800c49210b04211002b40c102c50701c1451050900205c40181c4400440d00000044007031400410900307000f004131180245242d807500c0d4540d0070354890034055501d02e07008842a6004000d03982e0156459800f95008001c10100c044644071200445019030b4207034110b481c100442041040b0041e95445c1d545415a50422036205500c00750740b030082c0060740070703020440c203e03085044441c0d95103505400c080c040c0c07010480c40c2 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 924441825 1250 924440575 924440591
    0xe040515040c050618040204120506061813030507020301050f04031d10030b0604030204061e0b04240201090b04050c12340306090303090218040f08031504060f050301 73
    0x60360001020303074004005544001c0b007007081d0b15002000d0b040460503440061207000a4078000b8040b60300a5020000d0b0484401c400c800744103007808255809082502c1c12480e100540608400090700205000b103000001c1c440799060510036025110036030f501400030091030805140c002c0c0c03412022502180041c184800005030010041c1141b010355001030700c03920100300c580b503090340600369109105401c241c050000102603652401010b0003001044070700201030307461100c81d05800c01c041d00710003050402000308005168041034403200c10b0000d004240070b2081c119004070b000d0704c2d400a02400c8540203009100074050702140301c80e0031540480e0f810440303103000d185480d114072803100340002140c0340e0b800022100b1090880840407045030084480d41980329030780c02044944200d0103400007503440c01203504504004201c0300200d11055000207040c50550746d82d800076803003404010a00c04011011441e00c08082e0701c960301c20740008000f40034103500c40c0e0121103090060b101d42d078425800c000b81 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 924443075 1250 924441825 924441853
    0x121401062601050d0c1d1006210b1206190b01140d02070f300e1c02030304030b0907051309020607020f060f040303170708070f180b03070c02030106081903110312010e0405 75
    0x700c0b4080c90680402c0d05041d05c0d59271040041685a034002c3c2c0001c40c10070901c44880040c840548039426141050051304001041d09046401120380c0c0390620010241e9445402e00100603100104040200940d40d81e0f2070340f51441e00d481d1103e50042540c1c0050040c01c1d03500e0840040d910403544401c482e50f110080000c4103d8000e0080040c460302300d00c20920070020240c0001c0a945aa8005400c80386480d65998840c0d43c03c41044032002801e40106409002a141003400381a1340002588203200024613500014024030814500034410441c04512144139111001640c982c031b51a000007075207803642e038240540303100c03840074103202544000400030780300c140200c46050180040355a94008000c0181e400c0d62189141201c40580e1802c040e000181524101e00031482441c042c0e483c001c0d1000148149400c0d20700f2600180c07843d0300440420f420221360034882d80f808507054903040501c0002e40e803c0c81c0c110700c41d80403154082030506001180041c1018005070103940315400320b0703207500c2080752 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 924444325 1250 924443075 924443087
    0x90c2d0a0b1209120c06070f1e1d03070902210c03060d1e0f030f090b03131a07090e0114031c121401062601050d0c1d1006 54
    0x80c86401d14400e020300c00075528030b2400940e0041c500300480d10741004105003403006810100401440764040001c01000c0c60f84458802403102490400200b0004a040400c0414010121040804c070340448412441000c201243d2400c1c08081c041c1c6500030b03161081480654002c004440c0200326000d1021041130b4607240312846103000c0780e4401e0540e10380e031040082d60402ca4005036108603014058910014400c03000c001ea00e0301c00c0c800c0d01495109441c001d0110640501d01b082404850301c010095126000c04030ba500510b060744008034a015072404c41c4400e40c032a0030700a0011080010403403020303004200c0605a0700042101c554507a0b03103000c3c00020000c908070194068018154920034a00001c035140300b0010701d4103003440201c601481003811180f050004e41c8804aa0301c0c010402c05400c02950b041500c1c42158690300007010003655421081c0600c103490203000303200780040030310100041f07580107490b00d2815440d08103407001c444090010240d51515000420180001d0f43c240241 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 924445575 1250 924444325 924444329
    0x50102061306200f0a03050f0609010302040c0903050f0304080601080f070603020a0507150903030506030d090315021c0204050312073309200d03020303040b090c2d0a 73
    0x401c640700d031410075903150b8010f010000d1040c0f075201540002940400d10b0305000d030000e18118801991140f01e9010000c041d038502a00070000010000240141521000c20303c0b0b054940507035010540382c00d41d070811100f600a03580050450700034200c4000b00c000e0040000c000300d40c2c04d03804440d49030340c0b150561a140d12640d080a0500d40c00740c5400c0004034040d4020708441074103030512504001c00f503103403006007804a46481500540e1525068105605032242a42040043d030042070f07801001540505611081c0c003000d4040802001d00b0080d001458040f130b001002c2800340b5124450310f01e40014040e400501a0078442d0040400307280c000c0c240f000036100711b070380c010300110038581030800c500c801d94018640c4201001080e000e9400001c4250180d80a032910070300c815191100305100110032803082006161042010807801070100e58000709032904641c014246800c2511a07a54403403a01c2c448180040c0c1200400790780d44040c0031520182480402c0c1000310241c40c100c00410026502c40c94 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 924446825 1250 924445575 924445591
    0x42d0602030307120c140d020304030305180c01120f0c080106081308090904050705031b010e120703140115030f12110717030f030a0e2b050901170a021305010206 71
    0x1308805010040c4a6000002d500c840c1e41031000c02581c02c10400c02c66503104804d00015550000300f0b01c020542d0503c1403940c401c00c80b02d140240c0c030880850881e120407038032016504004140340c1810746d042055004204801040408110700500410007070701401007440f036000450030039000903840340c0c0c020b9100d1110a9014418501c2c0104040400c000ca000182003078803507200341407001c5404d4404011641c41c90315017a80342c2801d55001c20004200310a2504c4031801480002009048804006031080036070754032a05c258000c640c8514141e00401020440c11b6070303186840030010501c030300340000407912405841c0708401441c1880042c0e4407000950300d0b4000c0c603441040c0411103408003130740c1d4660780404d03030b820b881c585400f94502c00740c107800c00e40d1804403680e51600000701500301001500c0015003600d020f154045040102c481c0b09002d01c4039448140070380090140302c203a216034108245501c9515031110380f8141010104029004001000c82c44602c80300b000c98550300000d2081c0c40b54580c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 924448075 1250 924446825 924446837
    0x161421030412081209010b0a05040e100b18040305030106080c130506030901060315021315140904020403021f0e0414192007050c010801060804110303042d0602030307 73
    0x1416034480c9900d80901001e4400d408244900d041301c00441e00018003640e0074078000304405140d142006080d18103035100301d204a00d851111108030f400840c00e40300042d444580002e0021810011804040070b41c411411142e00410411042603009005141130700c0c0e01e070340d4000c050b07504d00305100b18074824191f65451003034403901c082080f45041c200031684400031400225540c0da80c1e990310025500c800100d0f402d45600819207400500b030702d000000041490985800417160351400242401003d980c40f1540c45500240414150721140c04a9004607400b0b1f0002040d800605681c40300d801c51004030307400003031900c0003846251405000320724208004030201c031065140c440b19000e01500c05001c007040c158690003601c01c0d05502d004440740078088500c80d0b070b40e100c0c01458124200404071401c41c1c1882020307070040c842c540c1d000d01c040740d101d6800720300681c00c03003420b40000e03155001c1c0d50f00601502c0c112856417280454042c0c45003a50000400c8032600b0103440c0c500617070f02e03800f08035510710000708 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 924449325 1250 924448075 924448079
    0x807030204083012010302090c04060f120b100c0b0f0c181c140f07140103091b120605060402070201213909261614210304 54
    0x38601c9090718004145001003640b00d4081840500903030000c1303100c4044d40b800503004009604229604651100048642c54070305401d003080a080122000f03500001c1003510540c00c0f061800c95440740c10b05100c02052114041e0183c0d030014011001100304440b07911400010820710080f80081070700800d00f0100ca241000c030290030030071071310741c0310303040c00e9446503010f0450807a032030060782c1d000e130701c5406100d130f00300b510407042011460644a4010b0081c0f580c8010b4040011a55032500c04024100900c0c1c00710f4030101c6820054400e51610710356130316410702080b00040180c007040010307010358420901403205507905000c01049004207280680461122200e403281d45081d0044004070311184400020240c440c072200080c10b02080260ba0064810405041558000690200d02c414420310300000385034202960894011640c203010388415001c5402440c500b5401d11107402c880c0441c80382d12002a60300c003540502c1c620386550a50280c5056540c85d07042c202e59214407080440303114002d524042c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 924450575 1250 924449325 924449353
    0x3120209010c08070c0510050a08180a061d010b01020a02030c04110c060c0702040b030a02030d050f090607060f0e1930090806070507031707110a08040303080703020408 74
    0x50310060065041001d46030b088000070b2190005003602d42c0c081d012030902c0a0030a018003242203041030301e900500900b40720350041c00e40e00440c0c241d80125500a40e84504502c141040d18018140c0340082000303040680d90b4101c554052005807000000c080240070304220103006907220000d09001940580202c4c4690b069810240c2003450030a9170070484d140b510b82480005c5040c01001e40b01c000c0c41341c60000b14602035251502902580760000c030007505900c4803580c0001e54880003840203000f400000300b03200802025041c02d49060303071009401240d8640d401d161880c010554400d00b000344a144c01c0102d04912000a6681d1040c2004960b264401c00d2985416100100c0d00d0000c80b03401c0000d01441006015030001100e120529466008520341020181410712400502400401c001072080360f0102c2c3e0320107d01480f042e400c000d0101c45803205102250700d0140e0b20440c101a1041841e250200900a130050080700d0203662101c82d0358444000440903441a441584256071015954010407 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 924451825 1250 924450575 924450577
    0x1206091605030a05060a0b0c07060909050106020a030f050c1b091f0b16060903110f01020a020307022106192f0a090315060f05060906120403090b1b1009031202 70
    0x3080c0103000c03103a06d660790200000d003980140c84a14954002d840204041070f000110f8601400e03606a060107030390304000000f03603030b0a19281c000e0100105050341d2107030301d4002c0c02103440d0b203003020043e903440382401351100c400240e036903100d14002c1202c5400104050107a110700f42400c60b1010101c0d03402490000c00460030f410100a80481c0c038142c00b4644000703000ba200349800213100780c80c0d22003c1d4408201540c2814000c800c055140e9004004000159038040300f1551065411604550100f60000d20303085a1080d402c1c22560768402c81c024480c3e440281988841c1400c05039100344402100c0f03220b244040c07807240101c0d09440744402c3d0b40e4503140d0079003800390600d00c0c4c8529109040075a642c40b08050840e1020004865582d19501030110080104c041300107070100387e43c81440c1c89055000b14070a403041003403042c07030f601200c4003107030406200d007003580010840102e405480c2d803144045104505e0803416050250320500c201c1900c40501e40c0100800c0c2901611681080d03039a0761100741c06 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 924453075 1250 924451825 924451831
    0x10935240a06090c1d0108040c180e0303011409070e032113090209030c15030621160609120b0a0c090305070306060812040803071e06021206091605030a05 68
    0x5540310180441d194025101300c0340c09040c55035845068010540000c0c040761801c00a46040080c032804002c04112044510000c4400c105a484c032500c00300d1001200138400b41c030400031217000001c00001d40c5282c52450100d46001110000c544c2d840c2c1410a4980800c5603180f140c1507000341680b0040c59030321144642d060074200411610307002e5085080c600a420b9600403001c1a507010800303460b030382010001c0214504060341d640883c5440000e039803003e03001c001c2c00144603c41914450301c103801c0038180d000041040004031040d00075121302c0a644220107000314800501e091a0001c0c80842078901c0c00901904050000003a07111408860090300a111805003408007404d0300000060003004401c000b0750150700d000502c1400e01c02500d041c0f408213060310803400c5083c8014000740d1000b00859044940c04044408801c20000b094404101d0343c51000c0c05207407000c502c3c2e101003d90003005a1060404403150429507690500b0001015101d08800e0b001038014000200300303c09070303800150 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 924454325 1250 924453075 924453091
    0x30906060904231006090b0108060d0303020906070c05090c0405010c0f02190803040e0c03010b180315090604030e061303110a090c020d0206070e01170601093524 71
    0x4180c02d2903075801e042c3c03d20307044000c8440758071903402000d0010580c802c52000e040011001d121180100000030038180c0042c140c1880f0310442c0c42e0000030903000c0c0d41101c80044016201daa1240500d0170b185000da03010348aa03e001d00c040000140d4545121001c90341034550507142c90b0b02d4409251140d221017a0310700740c00c80c5c11000005440b040341e600c15101c20000d0422000950f07842d402e000241544440140803440e83e0701d014030060000f108450240c445209540241d0781d40904280f000a280140d030500450016202e00140702007000080782480c81076000b900c1d000f030303000310343e1080c03048a05c504030410803a8100c900e4103000080c1c40301840c0364440002031290b0515a02c1c1c500800c112400c81c04200c01591142440340c86050301404102c0d0701c032801c0d0400d45c0071503a607400040c0c0241503011110700c5214820001509581c000e07d950b0010382824091100c4184151807162100f502d40c81c98010640f9000f58909220140048c6d0400300d442c0c0c1000e0340041e02550082c1d0342c09094044c020b10 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 924455575 1250 924454325 924454343
    0x3030e0a0f0308030907210c2c0910090f051506090610090e0a1407050c0d0807020109122105010f030305162009010509040b01051908060408030714030906060904 71
    0x150400406420030842002049811f0b28031114644041e0401c880d9201651040c0a41c188050440c0c00391510390303491400c03103004481c40e981c6012080c2000051205a41d5103031400c4652000e0000c9030f644060518440c02c2110101140c0059003078054504554144c0d000c0002800034209091201c418500007100d4201204040c0d141c1031120008103084030001c200176982c40703d4810280e80034080a810504909050b1700d07018407402059150107040c0e400c0001d0148100203d80241d10035406110326607000044442c01240503272004144600744142031030807000e448410300e1300d1101c134810306040300d0f02d002a480c0700b180386a4007070b1181c2c1c201000c09107070348269000b12030118209001c1c0d12052400c817440107071100c1228040049002041c1c002c00d0042010704100400220011000380c19580c045411a1050842c0040c03030b0041c0343c0a030802c030440d004001c2800700f008049000b842c0582042c0d244c170044c0b45d0a00c9148452070004541c4080039034810b001003160740c1003d42c030f041d0301305000c2c2a0382 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 924456825 1250 924455575 924455579
    0x1005072c1011070b30041a0615030403090311030d0c022704080a090b1206040e0f0703031107090b2b06020c0303041b1208090307091503030e0a0f0308030907 69
    0x140b5080c0c01c400e65003400030086400712a03070825803444980c00758456442000c5c03d0f04103030710b624401c005001c0c240b5000e50720002c04210309035900c43d0800d016134a100340050740c0e450589001401c40303400d488125840d0301c0703034104502507190114031921016226601c90300c40c4400da4003003200e0b08504414490f183c02d406260891003050200d0b101d48902d000b04815551682807202c02014401264040042010107000c5002c440d8000100f05800003000c64022480d9036152840038282551540c10845612485500000700f5401800070f04c00c0c007600d10142d07110140d039090440190f03440c9521050340049541510001c034080e200807160001c60103030410412203156900e80040380c3c021040910150300c041b041004000c0481d40a82580003401401c8900c03500e00703103a0401141002c50014000300d80030074100c826441c10040400204030510301405102600c04120000240038002907000864003122480c09050408142c0103c1d6080d42c035400f491450b6071140c084580014007642d405005200340 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 924458075 1250 924456825 924456839
    0x80f040f03110406030312023105030f0303013f060b040b010c020a05150903070f060f0801060e1509030f030a230a111005072c101107 59
    0x141019040e003101429a590079418014589a24595207522603401d00d2810300c0002e502c0188003035012441c950168464000707084400c0020758600391024a0703100400b070a80c1400a80d007102c0100c420550554266880c0350010640720300c0240a0850074080114441c0c480b03280b40130301190442c2026019a84001240840c01140b50f40050281d5166440d4060703150507141510400407540403d08109040c40d2480d8041a5507101d103110307681c03190001404942c0041d1b642400c4030409440201551a42529241088044c0595010303820002d0b242301035500c00e072800340107428162020b6444401e0b000283c0002c100c004400c194000320007078028002982d4584041050301c50a10080018545034100100002d2100a00c1641d00c8006806041c1811240c0c515000b280d0182105280c1051140c29141070389103007001e207034030340b1702d14900e004100031030345611014110b90342c030740e005a110354803155140c40704061075401d46055004c240640700a08a41c081c000f507042046610055582c0140d841c14 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 924459325 1250 924458075 924458077
    0x308061903060f0e01180303050c070206071b080d0804060c050c06040506011e0b09090a0e15060f01031a1908030c0309040c080f0f0613020a030f050f01140607080f 72
    0x1c02150302c0c036118070300304107482924000c03a0702e02c0b803900008200319400139030903800b50544e1903400340906a0f2039000c94092141e00c01142c89041d0064401581c4803540d14216a00310b05412425129400c411f001103031480740400c05200d01000c4c1d6844100a85554582030020580500342d0414400100081202c0c04004d0018911a42c09a00130380250741c908002500010b04d00400741303013094401c4605100d405000c1041c0d8040003001d035800032165841c0b9028000030320b8102c1c00e4881d14411403600818051000c84030600c04d03d026951024091030702401903090300c02a601264094404076282c03151414004440d103401644950014111030340c2d08516403c560100e807216500350400643c05400d42400d014034220341005180c00d4585d031800319000c4020711000b1300017255480e07000300482c20742c1d65125007006602041603011940c81da01518050700500c1c0b8010000d40c0300d4142030000384039a41e1902d48a048a811003051146a15038004024066201c4802100c21a000380802070368035074048 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 924460431 1106 924459325 924459329
    0xb0901051b01020f04080601181103040f050a0213150503061005060d061a091903380708041a15010e06091003060f17030703080619 58
    0x30301607601900c1084880400c0100205000c1103115000c81c100e8100c50717080035107500f0341400c03d4080d0180c51400c0c4180818150900028002c0b6101e0040c03032032040e01c1041500e0207201140d0010b540c80d00194103c20b5060b5071031a29003680380300d9403c03400c05882c049000300218500000a04520b1040c0d00805005007000f249850101000c3c0c0c0180e400b0b0032000c161041d029150204040c02c0317400c40039190784a10260403140d03580103680784505041d69003252080c04043d4100d041500350103040b603c03200d40000c0c40424100f2081d04201384030b00582c0c06644240d40380c2040d007440064003980c820704540703002c0e00c8018480703940d6401080031103101c001c0c01c10600080e0308100003080e500a8a1029030816084041000025403541c01b0406a0380960249036605d0388030aa0840100840c503111096540100305000109000e0800d02e5800040104400b504e0040c1d21840079002c000307a = true := by decide +kernel

theorem cover : BRFrame.Cov 924280575 924460431 := by
  have h0 := BRFrame.cov_init 924280575
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924280575 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924280575 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924280575 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924280575 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924280575 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924280575 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924280575 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924280575 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924280575 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924280575 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924280575 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924280575 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924280575 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924280575 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924280575 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924280575 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924280575 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924280575 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924280575 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924280575 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924280575 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924280575 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924280575 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924280575 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924280575 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924280575 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924280575 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924280575 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924280575 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924280575 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924280575 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924280575 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924280575 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924280575 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924280575 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924280575 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924280575 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924280575 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924280575 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924280575 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924280575 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924280575 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924280575 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924280575 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924280575 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924280575 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924280575 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924280575 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924280575 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924280575 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924280575 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924280575 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924280575 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924280575 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924280575 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924280575 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924280575 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924280575 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924280575 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924280575 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924280575 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924280575 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924280575 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924280575 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924280575 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924280575 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924280575 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924280575 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924280575 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924280575 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924280575 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924280575 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924280575 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924280575 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924280575 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924280575 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924280575 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924280575 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924280575 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924280575 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924280575 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924280575 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924280575 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924280575 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924280575 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924280575 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924280575 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924280575 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924280575 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924280575 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924280575 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924280575 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924280575 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924280575 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924280575 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924280575 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924280575 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924280575 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924280575 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924280575 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924280575 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924280575 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924280575 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924280575 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924280575 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924280575 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924280575 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924280575 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924280575 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924280575 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924280575 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924280575 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924280575 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924280575 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924280575 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924280575 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924280575 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924280575 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924280575 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924280575 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924280575 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924280575 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924280575 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924280575 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924280575 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924280575 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924280575 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924280575 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924280575 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924280575 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924280575 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924280575 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924280575 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924280575 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924280575 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924280575 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924280575 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924280575 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924280575 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924280575 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924280575 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924280575 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924280575 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924280575 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 924280575 ≤ n) (h2 : n < 924460431) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
