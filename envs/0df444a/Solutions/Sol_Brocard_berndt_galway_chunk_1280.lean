-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1280
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T02:08:47.801986+00:00
-- url     : https://prove2.me/submissions/c55dfffe-e8a3-4002-9dd3-519e7ca65d05

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 230035971 ≤ n < 230215827 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 230037221 1250 230035971 230035979
    0x30204050403021029030102090d02090903070f0c080d0905060a140c1b011d180406020715060906050f060d0905030c0607050912010905060c0c011401080c03060108070605040b070309 80
    0x455900d0f03942c0c00c5042c0101c00140e42d2505200c0b00b9407400005c01d800960405a041d00840c40d0b15000550007480386003081c00044905104105482515810000000f0840220b082c00d0f424820b05005014080c019802c20051070b6004580315000c6410180000303141c000c519a00300c0c0d10740ea00012448090508101421120608100c07440ba0a40903512110003804030800141002c03031013035020101184581c400e10404c0c2e80c0c642102c1700820300c0100380905a41e079032a151001f0300ca0350800400d24000e2540c40d4668542075440b000a8854a4000300600c648a01c01c00110404000425600900421140d10b4560041e041030031030610410440e0708210301c00c11010706119040343c014000400114005c1e10b00c0c0340074000d1100324841c0d034008001210035034035800d86400f4000c0c040c900c804000203521240c174109600c5000031901100c020006540c4810308251501410071001c0d20903c903a50011442c0040410018205c41031074540c01d00d4149007030b1004081313403c440c00c01c0e8144046008005 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 230038471 1250 230037221 230037253
    0x30a031b0516050307050109080a081e0d1d0102120c0a020316060902010e1203070b0c1605060405160e01030f0807060501090203060a0f150e0307031202030d0b04021303020405040302 80
    0x81d00c6051009035400c2c0b85052409041c40d140456200c181040612401004003810120314466059040f0b050959500c20688aa560a03808980c100d070f115000001c00c44d0003c06180d111304946004001110881703001541c0d040d0a03405221200e11640c00403402203502e00240100515150500d40107072420510070b0310000002c2040a0819a502c5844103100c000715a4440c0c1c900708400004c841c00c0041140703090303803507640e4003810200810b50b212034404200c926941209817110f442d49d00d401c0c0b0300c80c400503103480e44c3c990301c0580f012075042c41100101092aa000414202900c540c1c40d94074500ea03185880d480c09079442c0280540c0c180d10b040059a02089060144d140640b142e0390000d43d6904203a018408041c040d035010140d00e500210707085c400c1a01c06203642d203400101c0d141021414501400190800301ca9038001481c84061001c000c117060740220192103807240081e802c05c401c101e040c01340b0081e80310303941c00d401c0710145510040c401480c00758041d94010b80640b040b60303402c0c8000745900c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 230039721 1250 230038471 230038483
    0xb0f2e0e150402120a0b060406081501090305010f0207050f0c09070c060f320f070c02030c041b08160819021201060504180b090103170f0d29030a031b05 67
    0x1c003070744450913810000c200b1101d0299040000050301c03000d01d4a450250014050b03a4064000c42e0303040c4a08814569581c4102100c10103160810000c0000300c0300020103100079401010101c42c24050150004248480428110942d0344054101c200503503884404039142c81e060007044441503030f2880401c4104417a803082c3c1d680b8000e52543c6100a20454420125400e41c14180d1417100029004001140c41e45614403600a401420103515550261000906000c0002134503074200d46072000000016404950f015080d010702d4071481629150a82e5980301410300c0350661001c0380c20240421880d08a001001c80000b50401c40141003003034104000d00030945c00c0e070100002030342c00305041c024115245489202d15017608010070900c0d0b0b5040128204520510019111351955410303840c210083c10100c0c1c211442002e80c240e56050395402d10340003421909451210b4010301094106420307a409600410344030020002d0806500303a50781250591144080000925085074a22000440030400 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 230040971 1250 230039721 230039737
    0x70603060f0801090507050114160605010e100e0f1e100801111201050609060c060a0e0d030b090a0b04180506040501201210030b0f2e0e150402 63
    0xc50100e01c1c291010601140c2500040710b1030740341c800060b00190300054040200c8a0a003440d0340c0c03a5480080a603654000c10418107054031881b00c859082103041c0c0d001a0580e0400101d0010341c4e21000c00341281c5a00c1406841c6004180d20080f401c2ca8100c0480b041c9d120046900b22500794101500180007000d00351581d107500d544a000600030100e00303008022004280d101220700f0b02c01c2017404045414018800d40d030242c0b10000b050309441c1c54000403540c0304030016084603050b060a400e404014104030594504500031504440c018030310038020400040c000920030b0a9944480d50b600300104038a4050b5548031b82e4a030b0540c014003007889003c65201d802030001d04180d03e09400c10b5420f4605a0f4468110ba01c6000302820a01401c9800e0399a10422110515090f40c0caa507458a8284007a8002600745644c000400140a003044000ba200780810b00724400d440d000d0ba00c7e8006116100104440070500c0400107011546078914180e80c805440140000c1880104000ca000c80c2e0005007 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 230042221 1250 230040971 230040977
    0x60703080414010b15070203030d06180c0f080a0b120d02101a0102070b0307030f0207080403110d0804120201030b1201091b06080106110f010608010605030c061204030c140706 77
    0x8200800d005079202d4501032a0050310092082041035000944120340a0f00d40c42d1508101140380829520b00f001035901b400501c49042100c552a1002042084074100c1c3c40c40c00182006911101184640e0340c06a0868050300d5403515500d6000c00030b0060f00e42c401c212600300e8090f044e051140340c010020b00070b085160350003500444040e040080c090f03c5402e11508410100861003002e540d038005442030440c0c25040c4903980302d881e50f4404401800f5400d1000c0003441c0046003c03424410000014001c0b42d00c00c040001e0400c91010502c1212103d14030082c142103400d100c20060854a075030802c010341d1052400045600c0c0e9400010200d000c04c0004a855030740d1800c2c2c2204111200928100c0c005112048949140c0f41540042200f50140144800c0003441d1402c0d03022031a080281d58100707034000d0004d0001d6030302c605c03046000703245a00c02e4034480d201e1800e5045450070130701c0031103407180f0361510034085590301d5440540ba009144103085510a200050f50640010180700d40c60181409603 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 230043471 1250 230042221 230042237
    0x130c030803101d070e12010603230613120c0b18210d0c1707080f07091202120a021905040c0f0c14030903030a050d0e030c060703051302060703 63
    0x80b6401e6036410b89411860741062003281c91071091900316901940140359180c1644c151002c003000c50300c410500303806184250709205011003004801c25120704810822244c203041d4101040c01075544540075617001e101c040d003440783c0202061071200201290310007420803031240e10481c0d4039200e01401c2242c140b00c5021841391340305080d00c004d018100d0031070a2241304000c0d589501c4921441d5220b003045034070410350b885200b04961030148094100c052041030040c42c05103041c1c000500200800c0340c0200c0d510f11142e001807801806100780b2421741d04528220f415008081d0b083c411504444408140980329420740300340142e440800022400c40c44580b07041e5a00d1418050105a9040d4100c5006118040040e416840d070f01a07001e50340c594203c401080f064400440082c1907109150b400c85d0103000005041881c4c941041c0103013100010004c04020071a80c12140320345070700174602d00d035090346c1008000c0345200d0700c81d820140d0008520001c940d40e07400075900003400c69024040841c0840c14030 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 230044721 1250 230043471 230043481
    0x204021e03060f03120a03020d06050d0305090301060602061009020f090910030b070e1815060c160503030c060417040819020f0d02030309060f0d0203010611120a020303070503130c030803 82
    0x103c0b04902d8030b05403d43c001c104c20711054203004010f015001007030f010140e01113690303412117445400080080001412105208550b814000c0081e4070014031540a03600b01480040e2080c0b0024005203e24035024050504508120321b5101940c040031403c60241b1050182080b03a6441d10311040c0034500c04520744100c01d1070f61800300c80b181401001031050020122085040f62100b02248503500407800004d011075540301144202202d0450615411100100b981c0700300880008003c410410b4103e1124041942ca2040581c1e07441000400e00980e0040008100007580085442c007114140031065420030341ca400310940780040301e1006045c076030f040170860f6007941461152281007010a940b02d1458201d144c011a9481c400d104140780142000100207034608400025074403c031a03101c100303564a503985e0000804078032240303180d5000b0340070f2074900d0040340300d21134100e80500446801650445e65031940c00e0b55140c02c010443c20342074182112980c0051070003d10300b0b000d107200343c20041c2c513801c0c6 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 230045971 1250 230044721 230044729
    0x911270114090a0902060c06070302130b07110603130b0a1506031b08090102091309022b0201031e050709060207090603050c06091801060306030209220f0204021e0306 73
    0x107030700c20651441c00007021840c94035003241e8143e208008400100f42411148082405445180c90121082c01b50000344110b1300d9068004041700c0382d903186540030460310f480c90f081c418030030030500811003c15111403420074100071000d15400340840105150008054442c6d0480c490119030142c07403a0342c0c628200c01d07144071101100001e4041362804200011003489031070110b4640c1000c90341405032040004001c400d09404880c41070802801c200750f4686200c6c03407030000d0120304c00101d1080400d003040700220288000b032010240041010b64103600750540042d0f004003419200d070445403035155000001007003280a40c0340100e0b510b81d034006c840c1303240110080c2841c40b50303080424464103007201007010801c00141300c03110a80c1111400c0d5150410340000c2d21390708502c440c50200c0e00c2d9000c00014440e030160b101000b00e130f0080c1c0d80e10443e507842ca5a028401d440480aa40320741e60118044808281c1e0303000c21b000c0b1288003401c0145040b207884c801845510b0103040308001940f0002c100601420 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 230047221 1250 230045971 230046049
    0xb100e0c09040f06090c0504051804081213060903020a020a0803090d06020906090d1212091203051e100302120607080c220e060111060403090501030911 67
    0x9404080052142004114119a4480c001e1850711480e01c4001c82d01c140d03445035210300014481c1080c1003110850120018040340c205d44100c1d8818080581c1100399910384d071503c94420380d4040d03900380c604540d20300d02520041c0082c0104400300c104600e0000010080d00c10300d04800d0003a00200200070b81c5204103c0c200c0880d4000c010700380c005112004580d1500b40041c032800703900040140c0c40d443c3c42400705050b40108040c0c50703400400c00c008481031213194003082c0c0302c3d1465903640c014146c810350810000c1d41e6004400402d50442c0e5260340d031310b0912076070080d0342018054074900001ea000e40e400511400003500c500008a210356410030452030120901c4a40e001401c014042503d00204094030b600f1004088100303281c00041c1403100c00306404000180c03141c01680103078540d600c805000c03100c4202101c105002ca0300d000801d00c080480056914469541580d801002e01c0c10580110043d04440c3c400712100701c3c00707900c140d0030750380d07a07203940c03e031207100ba5a00b0408411510483c8044074 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 230048471 1250 230047221 230047229
    0x3040609031b0806060f04090503030a0507080109051504050c1b0610050306160c020a0815011503020c0a021c0804030506090d09060801030201051c0c03051602120405040b030106120b10 81
    0x10400b944108119000800e0b00d6901c03144c21600c002040070f074000813402800c01c1c00e000424034000041045204001584081d004800d1640c901e00b642e80c858980307102f224015595107814600c41301c6020f8070741ca06500802d81c002e40203140d007402c0c07900320396080c00401c056603070301c0c24030380c0042d000c001000024429803002040228000d00490800c5074443e103201c0481804401041600f41c4800259145e050041c1c004040c08004c45403008088a0201000b00e400e026909580c1c0c40c04c80c0810074a44280280c0766501d4503407000d0001c40510f9420130440b80b001941480b91a48095104404a009280604006e41c0507001400c41d40c40c2c490195030034008a0180801031164494040c41042d500c1b42c44141929420b0800070354400e01460221603008011208081d2281045900f1a20030392503007145001e00b0607090010b024001c01c1205a0b210b241828441c1261401072004010500d45508914420507018000084868681c030140c3c950001950054828001d104203020141c8002c0420070020 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 230049721 1250 230048471 230048513
    0x3030c03060612090501060e09030408160303052a0a1b0605070b040b0702010216050a0201080702010c1d06120412080c0a05070b0a0f05070f081510050c0c030304060903 74
    0x641c00e08001600203c030303403221010495910302c2c40d1000c11401b5031007400641000303c603003105450303d50380007a0b9a034403901400c503d81c0a1b22541030910b510303441e08541a25071580358103040224198003004070794801c00800e6581e010690072500ca41000b44000030700319010342140c071690324070400460301c00001e0782c0c00542000b20412100001c1010504c0882d04254440c000d40225120351500728007902034130801150000050040d0801c001d000a003500d0040c3c402c6e00c5208980da105801603007258bc110000d6004684210160660702030187c082400d074035401868241031558030707031400350008401c0783e0441344c0000034035020610a80180c0a298040280c80c0310314501500c01034010280e024080c0010030030b50b800340c046408840e043e08890b124405015003003005140ca12001000c07611001c0c018000300c0d2504000c212605ca805440b220903110107040380311404d40000046800364090f01501000e400b900000c424995014002400140650b941c0c60803094110300705801e0071030010010070300c5 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 230050971 1250 230049721 230049731
    0xd060e0f040f0807080d060b250506011511030703020c0a15021506041811041103060307031e06110711041b050c190f1a0705030a020703110a0f03030c03 67
    0x1000046440034596103c4100c0c0d0f107a100524000209016495030720b40064100702c0081400e0b401030000d405426085000000d0007106c04400c21194803c0b054040c0c401d4010400500c4890000e165142100c01203240c400c05076480c44c0c0b07030581190444101240143c001d0410803200b85000b01001e00030309050800d2400c11959228003030750b03e400030031064054501e0003000546640d201e42c090036545032081d0401e1910a040d140429444c109800007512551600150170380581c40c0e902500c0c41114094010100b483c110f465004e20080c04224420280380a5081f4034002030390360007217825566940c03000b2603c1d01030514081c041640009601405075151103039442681c0d12140701140040d0450070107a03601c3d407810140b6814803c2122092001c0d9220b04400010000d42e5007400700c08901915003480348410360010080340c92825540480007030030034804101c014082c5d40c0102203142c0702e414000100c001046000d41403400014041da4440d404039496000d1580601035154409100d2608000c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 230052221 1250 230050971 230050973
    0xf1a09070507060f0f0e0a05071d040f050a0c0e0118020712030e0c060a021f090308070806010c02040606020a140d14090a0911040f0911121b0d060e0f04 67
    0xa809050006031106840f4640e00650b886907034004490343d40c0c0c60748284410340740d5102441e87d40011120440d00c6100d00c0400051802c6032106c240c104c400c485142802c10746a64507440f14040d1040415a683d02170b507d00617001940080b00f5500070005040c5880e100d61502400019000d018018540614010884c0c000025410015520905800e0030300045400035004500c0ca0501084010b5400c9140000c540f40d8007500040c010b4004004a600808000314011500c41131714041c08006000ca410f0324081485903005814180d4041410325100550100c5600001d00f03941c11030b03100300c02603044100e00c0c5061211004e0444130301408000188086540c3c104001c1c0080c0038041c0e03491780d0300740114646c451581c4030300900d4000c04401a043c8802c2c0c2c401c990b181100e5100f4440c81c1c1c0344540304040041c400701075004101c2c4904e031543c0b40324241842d20308180c2100000404045014144820924501d19240080e220f42c1b44070540001e115400c000042c02ca6400203085c940580c244401000 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 230053471 1250 230052221 230052227
    0xb1b07061409100c0203060903091903021c1110110c010806030c011404031205041712160203030d09060c110114070309031719050112020f040507020708010f1a0907 72
    0x2000b0031030544103070391003407109030080341c03912850100203505014450900003194800400b40c000c001c0d04541c0c44400345e89200020316960070506c00203411614000521625009121621800c07900178007855001c00700f0000016910310442850001240c2c207000c040c0b803407130390401042001007401e090a540718180f0748006a901d62941e40303400d0403c44010a2890798150800139500255032001d040d100440105402411940007402a02a182240112603075116400140d0b080904040c1c642c551601001c903042c004590000b160a030b03014841000304d03003010302c02445108051405100b0002e4004144213005007620f6201c4600c0c0b040c0d80c1400d50062207003201a400c250040540c1c00e00041c000898501601c1010418650a4140010504014125070400907403501e00003aa04208100e030703200d40d10280407401200300a034022007034400003035013801d0940c012900910b41c3d00403903142030b9880b280d250a41c0d942d0b0450742d00c146e45400c1914160b20151407452000082201c00f45040d2805003801 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 230054721 1250 230053471 230053477
    0x316050d080a0905100509030c0a0605070e030a120302031003050a150f0b0a0e0402120f0d08160c120e0a17071403100b04140702031309020301050609090903040b1b070614 75
    0x410f80c0e0780c0d4030210f00965800c1040310303020f041c9c031415a02d81007000d0400400425007161610b010425828090f52145404500d100842e6440003d510345e18008074021402504010060703030850400342c20100102d501002041c0c50707140708410700030307403409202401d2058901078101c8103031950074010f60000b195101c0740b203a016100300c110302c0d40413645c46000040c500c0042c044440450300447c03024140010380852a43d08036442034440404503181d40614142c2183c1e4421007600080b0003004607400284590500c0c66500300785d182c040c1210b1103010004140e1803555005000c05078032010f401880700e40500c010700040145000300480c0a000501190310b8418003140409010365444000000f80d540e50301c03400d400c00d0b80300e903108a00c0c5001440030396203611210806c070060314000c00020312090603000b02c0303041e074a01400300f42c00d000508003030000008003d801c00c2900e0006010200b04014050003400304170500d0701c0c08480b0b490b54a44490304166080d0000030070003e540c520380080c40300107012 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 230055971 1250 230054721 230054743
    0x6020f0a2409080c0c0607020a050f130e101107020108130f06060e04060e07030201051617070c15050f040311130f020a02160f0311030316050d080a0905 67
    0xa801a00301039010325041c030001c1c25100c04203240c607050200050281040140464441c10f4080394440d03050003040011038001c1501c003e41c09582e107101030056040604122a90180c042c02c80007482c2066203101c802d80d100660443d802d40d1007054075440a9a103400f4004811140a407658074045451b0002000301000601c0319000b00410084807042009000d00ca05085421400810a140d01d0b585802100382040d9802c1c0c40d03040c02c040512500e070502040d86401ca0380c3c140c56981c50800200031401d00c40040d44000c0e500f034601603000c003080444031001851441c1c4900950074015051a907070034040d00400d520081000000e018541c8180e8998049805480e00421158904804c200019000c070006407280510181042d0b403100d60701e00c20b90090b05518a464003599808814018854510391091042d9010988a400704002048880d51b10784a00540601500d142c6480c0c40b4240b182c40c00303072881c100c3e9582d1000c054600345690104100e9001510f904091180d46082d40f00d45507074180b180f030 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 230057221 1250 230055971 230055983
    0xe06040e0c030403050c030a0203040609090e0a06050c12010f06090b0c0c1509131505100c0b0a090f0b010906050442080c090f0610030c020312190606020f0a 69
    0x100f0305150081055842481c510402c490303070b804c0440d01c0291a50014403941c00030590701d400104026081e4007d40c010362072114020030a00000d510b8201c080e0001a100c1004a5802c014400d00c3c0e40003103d049010b40a00c1c600200c010b4902140103184000b958000510305c10203003e845140080802d84074078501040701c0498a00400f041c24210074070452004660281d038040c1240007494958120482c520070854051003444c0c0c1d00d0090200000f0055000b0b00020744109000f00051180000a6040300312880002280000d0703a0b00c80001540280d0203aa42c0842c50740100648810390146201030715098405104401040c3c5401e400c1ca0780003001000048103048950300742c050b610721070700c40040103a40310428540ea51441d86454910f0080d03514003c6003080d0004480c4043d221409010b950040d00300e08851017182001ca00910746030307443d401180410011303c440700b0310f04183c0e58040c0c0d0904601d011050340ba810340c0d01c01c0350311650003501590803003000c4204001c0c020981613034581e00a9 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 230058471 1250 230057221 230057227
    0x80c03071d0402061908041721190203040305030f011a0409090302120409020903010f050f01031203020408011407031404031d120307060902030d090b0d0b0402090406060e010e06040e0c 81
    0x11001446a0085030944401d00c0d41c0035905c0d03038101e680b01701041e0250b0b0103400500d64441000c80c40d5a02480780302044000c001d42c02e1038045658407102e890540c00681c040b1000070035030481c10350310107036801078600380c00054010080c0203504045051140c01040d4403002601800314810110110b800346210345003045503180079040c2450b00030f01c900c031704c00c261a00140342c0d81c4c0d4071070000b4002074100c82e0050f4001d618203480780d04029818482d1074016100b01c40300860980c61a074441c3d000c20060329811040640074440011909801d028580f203000a8071241d40c60740c60f02c3e910050458114044000b04010380000307002c04039400400d03007440d031fa000e100c14450380425000443c08500791a43c1d210440e04c03000032004140019a4003203840c851088094541c8006066422900c0c1782c5180148a600d41c2c08001d4100b40c0f080d40c3e030000e0b41a810140016040c851900c001908644880d84070b100854007019164640c0c1da4003200300c064040d0116041800c1c2410302424000c001402041c1c10074074a000 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 230059721 1250 230058471 230058473
    0x90a0311030f06090f0f030f0304060b0a030b07090e060d0f15060f0b07060b0306011d072705090a15120201020703050a151d03070605060a1205030301080c03071d04 72
    0x82c064000c00c409100125505030804044140c1d68220a400d003c03541e000b130203c04204000003104407045c0079030110180d41951910b0300d500c0003c0c400400c2c00307030380440303030400000014504940c000e1140c00a0386642d181e5a00d0406140001c0700024040c0344100e500f403034010002803010000340740660b000b81181070003044808020000b00070507084030300315882000c00096844031103001408054807806060203181a100b0a2540e200d0080c0a2030310308020340300152545070000088964000340741e140c0f03480200b10710400f822000030118003445034001240c10521042c1080c140168001d69219010004400c02c40c0c0c405c2400c000d54082c01c8048035010b5052819a0f1003041814013440c4c104041e954119003d14040b40280c6c60b1100c40314201d070800100c0701e0010300761900948144902005540f4041190392814002c00d801005030b60f021170080740110740c007001800c180b40b1042c4141c0046a5950400310440c0c5041d55070310100d84070340d200c1081484007100c201034130380700400000704106143c3c4075 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 230060971 1250 230059721 230059723
    0x7031d041503140c01030b030718022502040b011d04090c0509090d09080a020604060f03111908010e04020d02010c08121003110109032406030f0c0515090a031103 71
    0x207050a2404400300e0041c04828440140506100e40c240c3c40215103404901078015400c0d900601e010780c1c0d040d0030446c000c000321403060000d801a0540c1100042c42c0c070010901e003816110540011500300868074440c3e20841c1040e104031140d0360f50908000c0d481850001c10883c655084860ba50300507a2185060805c1005c3c008601c00644001442804589880402c0c02d41c0c03140490120f02c0020500d80c0d0001da0050007041c202d14954000c2c0c201803811381040020703240c7da803180b40340c0c600701079030340c0303c03a010814a500c068010b400c00007003a1311031003c148a00030400d050603000403040040b8203041c040103030b40b0050540010b035420708181120309024207050207640a906011ba5440c0318400400280c00ca600c2c2c070b41d006481c403880c25a89141811001121064030034000203140e14494071080032a0f480c410740c020b03070009603500e010841d1916591028404800883e046910390003041c3d051200303191a200080b22119000c241c07500300700c01b1000180380c40c225844050108c0701c0001142c581514 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 230062221 1250 230060971 230060981
    0x1f06030c0e03190203210f070516060315080309030a03081f03061409060f0601080c04080a08040e1602100504231f0c08010b0d2712030207031d04 64
    0x400900f943e0076101d5015003408000c0c1c610908074440d00a60002c0c22140015201100000007009400381c14500c200310540341c00c1d070115100303940d1803050411882010200c0c800342405050159070200e49000e4148800c0c0e61401170340c0089845400c1400039003919180060940100c40c1c051502803402d0705e609030705600020701480600340d207158510780801440500d420005e0000380c0c3d181c0050f0542d995a40b00d5840c1d041c00ea44c00213800d000725010a1081d0701c100c000c41c2c0c000d620032014a24040e5104400c91a1004150045804d8400480c0411211441c2d4480c00d0740300c0f940002c906083c0540c40402500c0701446030019032629038400c0030500703028640d03161002d004c15001e03c80c03202d8560014416a030703004401c03400040280c0b100600020321403c1c02100e501c5051a1528003d0740d0030400707182007640001900d4100d003a0344142e101080344900f92801c1e46084408101941442c460801c031014015651003103041c180100704000000c0e500000644e00103e005420300581d042d15000240505 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 230063471 1250 230062221 230062247
    0xf2a110a060e07050105031312090b1303140c03120d060312050d050705040f0909151401080c03060708132a090b04051501050d02091008010e1f06030c 66
    0x44100000c0908200d1550301c042148050002181d4a0079a0f601c01165144012105400814810450507002407003c0c50100c00c0e0840500b400e01c040c0b5100c640d801103682107580c4221080c1084507003041488581d4095506a07002c030b5025100c0b80d0301030000701c1d0744c8503070b0b00316100d401000014072101c44c2c0789240c0c042000f9680c02103000303a00000305c1704014015000010305207000303854000818003241c000d40856040f1907180d0101040c5a00e09020310b0010000c0150940b1810039111044140710300c2e83c8150f145d0007041c001d4880e09941405495450b226160340014000e038054070501002c0345d0801c02c0d03240e004104054801003c0c43d145012100d080d55000c0d00c8181120a034500481c4d10548a0712005031941c4860400406120100300002c2d16000d132107950402c184800140e059500c248002c010070080d51001620740820003010448030b1034014080303000141e259005004800046070110340000c0c41010700f00741040900a24000b5203010310401e1709041d5683e840140d0b0760b000d01a200014 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 230064721 1250 230063471 230063473
    0x8090c090109140601020d020c190b040b0304230c10020a05120a02010c09140f01050f030a021206190506130e240d03050702010e060c01020711040f2a11 67
    0x1550350b070194070000e042c400d40040740c0420600d000652551001400210254480d4010320840c0102d406000d490103200703801403440c3c0c108400200da003083c214000d100400e00150056540d01d0507091030711040c0d040139103440604092284a004450000440e101c1e2068100d4182c000c1e40d0907000103920b0a00e00340d40040090240c581d42246204c0700802a04480c00d140d00284455001454100d800d03d0385d0b80900c80c0f0b10420280c00300c401d400c002403038805049043c1445860302080d034000781900d4004a421420071034001800c007007549206000e40b90848419030b00001c4035103a01d4007510f2400c1c000e0155a00a92000ca070001180084900a90042542003040240360525640340445200d0341012424844500d40da0403145040840361038101c00c0c3c1545d601420240558011100c85003020143d55000c07509109040c0d22074420310007003d00c24490b004a80322000181300b0320040c0c800500401d03600e18600b2880c2080580140c4240c84184583c1c201c0c10141e04c8a01c3e0181c901c0d40d031a1601c4541 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 230065971 1250 230064721 230064739
    0xc03151b09090b01050a1409010c020307030f17030103021815040e0105090d02151513061203090807060e04050405030c0f150f150f030f060c0d060b07050604020108090c 74
    0x301034000810784141c500102090101061a0340103403903610075049507600081c00c90f14050250300c242c03001f0b0024814149401ea005408540010385450b885400c2611444035288000c420012900103900c8012402c1d000e2070f045602d1500092040031500c044541c180442c14000b642c4040c01034900c07618100e00400411003034244a43c594000d02048030314440c00d210b0851202d01641c0002003082d0042d001c030424070240d80c0d0f03030703200031034481e400e07d01c0c1c10f070082c00d40000b0354048240c60003080040d0100c000c2100d4000414100180b400040303a000413101d4001d1002440120b90150100d005144c1c103039804104d42e00e46107850703031031440303100703441d1503e03000382d0a000c00c10400c08580b4030006a88101c000865464102900d041e0354025102003507892413440000395141843d00d1070001c90307100102503c0366981190000d40c18030508840900b8220b10010715605410f030303203109043c050041c0c040c05600308a91030340c45e199140000703400a4140720001c40020940c860411840c400c20070041c0c10760300 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 230067221 1250 230065971 230066021
    0x40c051e041a03030a0f111b09070908120f071a0f090102090a052814041409070501080c0d0603110f0d0c0b0c16080d110601030c0315 59
    0x26200942100648074074248003502040381e040044804504030700030051880c1000c00103050391243d1100750b1000074072102e103115162011081c050070710f409801f07840d028411000d110030811481e40003490303c001d0005010060121000006000c045005000746441d55803218058403030590040150003825040741240e0b1611540c03015010500402c0552403a1160f5150509118240d0140c24411600308086503000c00403840e014034640403080d0103404840080340e1360b201d201d40c544410f400c140e0140d60104040411420940703d1003904c004030060310b45a0381411190551214042d101d510704100c0104046288a010041224150b146aa00070040581d0b207181504d032710410401c02500c101c02180707143c491800c11807200641ea039805940700c00818146200c21040d500941444030b520f200b210b00f0350510101c5030904501800d6500000d0951441d445802000c01012800154954101800402c002400312240b00c058952040904100114034121100103055030070901007060010321201d0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 230068471 1250 230067221 230067259
    0x230f0a0b0a15030606050301032d0210021b0103200706020f0a0e04110a021f1b05030f010602010c020a03030c140d050406050603070501050d09050708070807060801140d0308040c05 79
    0x24010800ba92410b20105588460035901e07800244005015100142d055101e45540c82d41c514060205101401041c40c1003500424600c40c6d40b000c024000d40e0100c820030030524000300d00c51f81e00650074070b42802541c400b481589062900607800d02080d400100d5004100b001c144c040d90304000901409030340361200d0700c1006204800b58581c5602451503c00c1c55403031024040100e84813900300d90001c10103441d14060201c4506200441e89403040d95031074040c1d440000d032218034406807246544158590a0030319032903c42c88010b87c0b1a5055a14000c1d081c0003060f000700311180e10903058103000a80025240e0f06441e01e01a08401040d0031030300280c864032194281c0d10807801107010749010803107580c0d060f00749550740c4c42c5801103501046d8103100e0024600180e8001000c82c0b8415401e44000c00d0303580903903501d400c1e526048082603400507a000d00406a002c1c500310b0051400d0741c030050111500b20b0105100301180c24000c3c040098100014062002c1601c0c00d40040c80058420031908103c11844 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 230069721 1250 230068471 230068499
    0x60b0d1b0e010801020a0801050108060a1707051302120601080c45220b12030316030b3a050f0d030504020a150c050607020a0204230f0a0b0a 62
    0x1403210740481030002c11140014803c0d9220482d860b20b482a07503034280401540c1c4800028400c5502103c0301002062400e840095000042c003034000620b2424140410030842420000d0700d101c40520511102400b0903841800c1030b00030100707003030249164903100c00e003011500c183d07032030102d500951403135030910120f1501003840b460341019440c910320510040000d169044400215a001c19030303152400c108130408002240710f02c107900300010444100408905413681052108a19030004010480001040d241203a1307d01140c3c5010080c01e28036800084256490300c085407003d00c00a01d11821042a00300802907480c24246006510070a520b450703a512a80e00c0c250250341e0049144201c0440c1c042d0007000d000d20b5004202c41d14041c240104034207106d44070804201004914103107070001c03030018444140608174983c042d2505100344d00500041d02c012030100c80030902040000c0c4030905010420319044505d509032010161500d1100c0700207460707110801d5911000071a00026403c0d0303602c0303407 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 230070971 1250 230069721 230069729
    0x603130f0b0f040c0e0f01060e03151906080a050709020d0b040e2d0601090905070315060305010b0906060a0c1b0f0306050c0703050403030c030203040b0d020c0c0f010903060b0d1b 79
    0x1820341100d0710741c4500c1d170b52620141d4510304650f14103401072207000e024040f11000c40e00c0c042c00303c865036242d00c5240c0e001080306130b503079507101d0461252800c04080c20380030340000b5194110007064400e80a03604c03640d5454051203501207035036001c91410450550f80d0000d405580000b04107105455400703030403c1d100c1c00c00642d41c01c43e000743d814001d021081c20f032080040051800e4054040c6a2034904035002808140c0341c00c44490007281808800580c40c2e01e980c40b2408be0b1a440000c00c9030540c0f600500711002c010b4903c0c4500407950812a07aa40c90104843c8545464604150f442c5004e1034600400350004030f6070748030080865004207000ca111160841200e01520007407041e900d9400b56001284141040540080e40070001400864094258007110600c2841242d24196803101e80030b40c15040b1034004040036400243c0b16500c01b508122035000c03040304550298845500500107440d400c00791100424007602e4000c1078442d6910480c0340091142c002900c98a112080b5000f03003c0c1c0030722809 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 230072221 1250 230070971 230070983
    0x30209070302120a1803140d05182a130e030a0c0c05090c270306010909020f01080f130501181a09060103050a14160b03240603130f0b0f04 61
    0x1380780140d4a005102c01641035003400e40b101e4209440482d202c140e007224090614404116040181c109481014881e040501131860f1b0740042650a6052100d0b0450031592aa5103c6460040721007040c1032503200042116010100c021040280020384480318078040240004102041c04a4000c0d00d40038240d031140170310400041d201c2e4100841e0300400d9915802010061220b41b81001e07041c500d000b2038151607506040c0c4c003405a0700091800c01e09070403e02d1901d4480d40c44404500b0943c4560f1403031802400d1258061a21050034000700e0320090020039299624850303036003400820740c00244101004245081d01126900300f181490041110b9441100701c0900054850307140030403030034180d03503010000d8007020185864181034040d00d000f0919250044240c1030340e1407401501540011b11003415141d4981c42c5c15200c403030b681c40714000c0040b400c13615000c2400b9240c0e10801100d5200302811060710781040d0030304140c40706050400c00141040160418009503000c00301c86188100e100304 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 230073471 1250 230072221 230072257
    0x1109042301080c0a23060c0313060c06110306100302090a030507120c120b06010e180403020706120207030203040302150702090a02030609010b0c030d05090f1002032a030a090c030209070302 83
    0x44400c017051150000544003182d100c0240d58034181004101c1e060541040782c1c1005101c2108010205040d4064000309602410303050410503540141d000a02d00850950301750303e0844003088510040214000030581c0c00511507090343d031503602100140d90814101c4102a0300c4041240341300c1c003640000d80c1e14514003c40016102101a22104201c0c0d02041c82c0302c1036140d9200540d00382ca10349000079402203041e5440d5420050710280641f02c1ca0107640100300b110f151040c06000000c21400b40d1034001d0040003540b0101b60000120340c00c80303505548000954586030801c29450052800095102605e4018800044202d0b0051401180101c1d40035001d0b99071009810400d200303001d400d0405400c1407248903158000350b80910307484011081550380c01f501440c4800c0c20706009038030049046c1d5010040c8020045405c0050518080d400300e1000c00058105682c5a00e000c000c02005503140c4540101c1d040000010030a8001c55010300100f0003410400c0001d00a50007100440311011045 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 230074721 1250 230073471 230073479
    0xf080a0212070b0714030702121507020610121509080c0c030123040c0e0c120114061b030906070308070e01082a09210d031109042301080c0a 62
    0x1c1161030803604107a088914020840d03617901410616680c0c4040179000c1807000f10003603203690190045022000024009101003a070900c00701ca103010f01940210340c808401c10498842e07406890301601c0c0081c00b030f41c158080c21702c1c2250642d40c50000100521381844007000070050480c0c00361410300c0c401c0044d07400031402036092500f00c848504016000e603048410480141c5452184103030064020f60441407c0e60300c1d420140d0f84000705880e8541c105a0026040440001943c05103000d8094264410181745401001030018040c1c91044580203210360415100600c04000b128030500021b04219201c10309814054900041140c0300d07001b14a500d0030414441d8810000c80f0f21070b2400111400445503842d485a03000c00798191906041c840800400041c0d640c1e03d0004000131044002542c00c0307541c1892001c4c1407600c180f0304441418240501c2c000500b084806454018509840c0007490307588200f079070582c1030501030f0140000c2c610100003003200070f008106212100c0080e901c0604040d50303 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 230075971 1250 230074721 230074723
    0xe060417160819030c02130c051903050105031e0a05070603140c0c0a08090d020d0f0501240e070e1305010603060b120105040207060605100203071b150c0204060f080a0212 75
    0x7040c03c410510403c1e0000000003a01400780c4401d484c1c0042d00000100b04004030301c004540d070f60131140c80030500100700b011800c958040d040c50840c0300c5140500c56949800302207039803492441400310340c655141c2d0718a8182c1d01e040140e44149a04801102c032559070700d400107002014400340181210f1342c0400004d490141c1c903002c840100c00301200030200d02042e9104d0131460b41012121540c040f071550b45400250f0380c2c0701c000940082c01041d9200c601041d500c2e10754211090055a031114601d90140d50034040900719994040b01c03201d0300954065500c01d081190340000003000c41d640310f264146004140180796201c1c0307050341c042d0744041043c00d8032a092403411380a40d04075a201d0344460401440340c0d040c0341e000340c024544603800100302c4541714000921808410305101005034000b203482e03c14014400c400c1c4081d81601071690340b5080c103040007114859402400c0324148510751a0401c215100d541c00080186900c000060f400c0d5240c0324820b450300e602c5e002c203a100d80182070581400d260 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 230077221 1250 230075971 230075983
    0x6010e0c0d050c0c121b21090310020304030c050c060f041403010902060f120a0203010e010b070f14070302030c030f0c01120b06030703020904051003050303070e0604171608 76
    0x4801582a003408601c9507500050600203025100f071820601003001c1407035080101600d1004031503280d507114246a0211b81c880c165200e81d1072901d41c403070600004170020407031789401c14001a12005130343d0140100400d140079251030b07141e01d05a10000410083c103a120300211103151007801508d450401e12030800a603030040310080da000f080100300800500d840c0c0750a00c110440090008180c01d482c82d00010080d403c1020a18085500014401c00c04800c0d4800030b036001109880c11403c650506c2024203142105000740008031200007140418014034100c0700100c291320900200b4482494800300751a05800e02c0201d020f48201c00b0729913140e00d40410107520704808440248060003034940111a00c01e01000030281d440e42c3c030004001252210001544100901c0e10302580c0d811503c42488120390307008102d40391043c09458188000798000c01180d0b00500035142141f0030707404240c0000d00314415980f280c440381041100000112402003038454421b4038480940149136641e00a45031240e0b = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 230078471 1250 230077221 230077231
    0x703090b0c09011403040606030309060203031605070503090a23040209030307110109090f061701020711010302031504020408010902270415110c01090507150912020f03100209010206010e 82
    0x141100c0000e001c00c007000c1c0c09454108414541103a075980301200e0088640d1050ba001d6884039140c6070103005054211425a00401841c4001c44c80d51400b1759021a00c0420203120004200340040d9000501004209444049100411014025554091060f40307010040350784c80918401302503202807443c082c4282c0700c21030340c0500078502e0441559034400032a60141c84842c1440200c603030201d2081d81c184919000c03600500d40c005041c03410f00b105040381d40840d04190205a00420400d000191202c80e14a542c550a00740503880b5210803a000040e004400aa150444e1020400140c00c0c001500910510341c001d543c0b101060244940d1080d40840040c801c54400b000340740400e000030452100c2010002d9408000215415010440f1840f98050388414105a460780840818824107000c07190040451154103441454402d1024001c1c003803a1013100007061603424440d0554a0f4220f48924054005040e190301004404402c002900726220141c010700c12a070020030b11000c6212254015 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 230079721 1250 230078471 230078483
    0x5060103090c090f020c060f010302031b180c041a041401051314010c02040207050610090608070b0c07080f030a080615030c16050f0c012715090b04061205070309 71
    0x30320700340410500540702c07403403503540da1650801a055445500b845070300d0023200c003c032a10340d55503d54010140b50914120205180f11000c02080e00242e0703940401c003030225002c0307a907120540e540c040c2e00b20b1680079035885881d03104811170011034442e1004004105540750180110450840744004445074010380034018802d1640c2c0500703000790901d46030290307641030f01458010040a9141c2c0410241d81210308121059400035082c003840f07031900209070015280070b0800704402071078a6030f1165039070110310400c3c0140b00002400c1c0c1002400340300343d202801800084031019550042c2559403580140c00e440009000071022810f2407500342c0c480541c0c440308001c1141581c07154030070140c195000c000301c825080c0d440c030302c4c040020b50284007005819003583d000c1c2010158982c00944010340140b04041808414900e44a842002c5900d041c02d55000d821040e0340055203610968050b6035507004141d0300d0740040750020315071340e1044e000c40301541c0001d000c3c409501d401d0070940c25200304600091074 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 230080971 1250 230079721 230079743
    0x160611030a2307060f06060f020a02100c2a050a0602161a07021005030601030f0501120f0305070c080105040c0602190b100e09010b03060f010303090b07170307120506010309 76
    0x311920780c42c08880e002821030b8a0b00c0c94800d9966070f000840e08420801001c031500e60000700141c0c0d411810f04404040c0d603002600e0049200da0014294040c80c03c1404280301c820787c156000d024188451011505114103001c201100b8008040140f2400788101440750b95058004541a44081000c9904d601540441c108203400d01440d90305414480c1030000030060240300000160b50b80080100d03079452151111a56418000d0006007600c0d6070b519100302031808c140040100c00741c2200300d00c03151604074004044805461600312401e21554001a1032441585000300f01110107610242c0618030580c0d0b400340d019a40c040c10b07030316101010400c24180d682d0708076000104c0c101c0312107981c2c0190502069a8556203507590b8140d240f00941e00c1d00c10b103031764411110080d828204640c1c0e411140c1d070340405c805585103940051441550b4080d4006a00303010556204208070407103075658240381541d880c0e03141d00d0314000041c002200810200c004d1741c1440049950741d40030b0301c900c01e2a59004425088 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 230082221 1250 230080971 230080997
    0x1090605060f191e0f03110711040b031e01060e07110d120b0a0602012705190c030b040b0403031a030322080a142e0906060503160611030a 61
    0x107010045845490140883c0000c80e0310f48075a644c070f181d000c4900503150610150140c102c02001c03141c48010222405508010110220f0103207e404e003941d5004460200305050303000b01080c1050a803080d010320450003004065040b500c103400220585040ba071750505181d82c0d6070b07411100d07446c8821140d607054120070405d00742d4a00c140d61180e100e4002a0000c01c01d004042d002c80c0d0b500079140c0c020700050f5900d500000f07904904036003503184584c281030320400c0b014590311282d40303030b403000c2100707811044440f0038000400030a0120340c401560400c5179041103207407a00b013000740d51b46c00325001c500092520b1040042008500500102c650300900254201700602c0d0081f48036044400444207207070041c24000030780085c2080240f40f401d1042d003440352103079000a1002d2400481d080400580001c413403490303000d0410b14400b460000e0b683c840c0810903402d5400c02e0300050045030022a01800f40000d01d0819501c1414800c040790010f90301c032545144144c0d500343e02c174020704902600141040300e10b40 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 230083471 1250 230082221 230082247
    0xb0312070f05070512070602060c04050117070c0602030406020301030317150f04062112110309060702060d06030b16030504050601050907180315050105010804030804170409050f01090605060f 84
    0x1c008600c41e40448000365181c00000301590782151445c4d440e039006680a01c083d550500416410902c09403e15003070070b08000000c0c0104862406003480180c02030002070040b4814007002d14001e400800840d580d00307207410440040e520901050300402d4083e509100f160100f036603800c1c407441c0681d464001c00ca0340c0404005c204004a0200c82e4040e840745004075240ca11500d0344146544001704000c46451070340b0b860080340030910001014418000000c5415000101c1200e044800445880d0b58501c013a2002444501603807807006c01c910714014010041049001c0035901440c6617201594242c460448102c01f503da089800030300f41c0d04044010030040c00c048641d9600314000f41400c0c4035500440c0c19155201030198419503d1100420405030550070511a09014040030300e82400580780c261400391501c1c0014000802c0c840700300c8140e160f902c005e4404c0d1401741c00300c410280072030b0814881c40e40b11803d0a00800e18001d190100024031443c210b01100c840b440310004d810300b4850385190070 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 230084721 1250 230083471 230083493
    0x806180a020909091c05120a0c090803030406090c140f0409020f1005030709151d041b030e01050105090f1602070308070b09060a061d150904050d030b031207 69
    0x3000441c0c080c040d030b0b8190750740c10704078a11607049400109003105020305076144410089280c0c8090100403c00300a80b000310265040d032006d1003500c0400d80800032401101c4902281d072000029004c0030003803004109042c3c00080903e4001d80c4d101d06d02d6038035410090038080140619590000b8440b0300b0f0503050030309400c480c0c40c040c0001d003281d15007101440410380b00440380c8040c40000340300004002840750003040f001c0203009034100243c8000c1c50544050404038035201c2d00c611194018841d0340081c1d0f125040410030001c51001038074000c80d2802c0141c060000038012068550a04001050038144000d9540c4591458911544c3c039842e2030240d148201d0b04580c0b084110b0158020102c0031809000c01004014412a841300391898070704c501504000010b0b246c070941070b0400c10200041a49100860700c40d61100005111741c1d12407541c00140010195103d941000e00d940412040c0003021807604450040d035182480186d10500401d83c0712804100d2408a10b4418409003010642c01024 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 230085971 1250 230084721 230084731
    0x6060c070306091a04030807030c050a140d060906140307080c091902070501110904050a0b10110c03010501080f100c05040317090d0c050a0501020601030b040303020906040b0a030204050f01080618 86
    0xc00710400700045040010100c201d40c06d0b0007260541003071020450340361080d01d00d002054034000c0e0815007000e00050195200d400c204c00600340c0440c0082008040b40d2291700100b68506007040031643e1a200413503144103106002e8800c1c01200d000203100400440d0780c02d4003800003000310240707a80700c02c41ca04c4001c114100e83e003c2c2c50350911802e00000d03001d01c58032150304081007105407a0100d0100700030650740d000300071000d101c1c28803401020b1621140e000381c003009500d042c40010906079141d92440e10804500d11035141d07003071400004c0d5101c800325074030219510000c156018402c0a05180c410344244230100300029100300010404180075585100e00c040002141510301080c080009140c0950f41c10300355410026400e04012070b00e48200340b00001c0100b0300150180b0740c5140c41c1c120440e00b00030700140a0580000d40c000466403038801b2134020708990710b00d06446d02c60044004000f0340207405040e0090480d002043c0840d07000720f102c0781c80b4000c0100342890004064444040d003610240c8 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 230087221 1250 230085971 230085983
    0x80309040905072327010e15090f040b100e0c0d060e0414070504090b061e0607080408370501180b100b0c0307031d040504031706060c07030609 63
    0x80042000240c86440c20310034160311304a40615410841040090f090001800c0c10b03040104030040368605240d0510780c1120741c20b602d200307855a205000391140c1c1c5c0b140800d095100f062002001081030001401d203004501802c142c1006541e442618142d01556000e040d2051003294005040e1070700690003060038200002c5d022854035560440075400c0d00c3d06460486440c924074002410a1a04101450003024110f8041c4040100c42d15840100440604614000e0548082008030040105290131790075001810440e9507c42c141400300054205028003607a900480458000b006030015840510100358030f100401705400d5000c0300c2d00e01000110481e00d9549641c91041d840c1402044482400d00071801e03001a443c00b03040c80800d08016401810000704203211408044c800003081c0d44c20300f030303043c2009190301070716a0b9503a000344045030825510a00748020801003582c802e18140c03a220901307400100c151110302c1003003c0c0d40284420600a607001d09000c20109240c3c1d04504413140c0240 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 230088471 1250 230087221 230087233
    0xb0708120126120403080904020c0f0d0306060309030e0d1106030703090201031107030c021203090d030e0f0109060f0509010e0607050c0102160e0f0c1b07080c010504080309040905 79
    0x8068200168000da11400740c0c00e15140416210b0600d503018a450700c194040500702c190202014805940200c0c04040c005403c041418842c984841d4101d40d4107100a004681400b40a540c0341070f6186888258580000e00380f0a000802500a015025446a240e00d4005684c0407800034420a500390101c1581d940303110f42e0354000e081c1c0f82c15000f10b008094654011842410900000d4150780c03449130340306421001002010042a0f108a030300203520340c115801d081810340d200943e482e502656407180c0e8444c0c40c1c600301c402059042140b1070b104c240c06949038204900c07950015101408213101b40c40115a603504000c603164802c200600c6c0d02d080c141842c0005041c6c03c0c0105400b038002c0c84003183d07681c0c05020122240d68041148060358412000d41c10241d5040c00401002c1c0f0001901c3c1c02c2e5804c0d960804204072200500690b5003400504085101c0c1c074020402c9559242d00c039200320070160007007050480495110310204e400f0b48054600440c6004040c800340801004002c2c07007500ca5002d68 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 230089721 1250 230088471 230088487
    0xe15061e031b010e0a03110411091f14030c0403111e0108100305060115080108060415020928030209010b09090615042402070609050906090711010c050409051305070b0708 75
    0x101355401381d80248007e0fa070a514078801e0000f100c003030209401105d40e062000030f0440d0748545c44031400500b03951028548002e040400e03501a41e000500ca80000404400c01050115600c01b402c1103a000e5448a00580100c5c0e042c007191503a145401c407440301181c488600203502403441250000ca65000d820521956911241c4c2840c4080c1c0080401ca9070355400d00c13158503401182240034080d28009004107090660f00c80b211002086120540701d50042080d5155981e0f400b01c04501141d0364604800100b03150014000256040c0012842242c941001052000d58041a40c03d1020046c200015a4591a04100344031480708480440300340d00b040080b4040004504c0303201c10400741403601c1100040c040019090680c1d5030883c208010844108010369520f8240c0c01d50880d2058030158003540791640121012608150400510b60a0440c54512968004004c00441c0c200001c10009503c0790441140200980345000e0000c0d8459241401000300711001030030701030b1040503900d02d45480 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 230090971 1250 230089721 230089729
    0x503030c060609180d0309150e0a0b091f0e0705060a02030a1d09071b06180302070f0b0a140909010e01080606090108031b010e15061e031b010e 63
    0x81603a0981d004036051041a06202c0e11907500400684075803245101007900096640946290340400c0507140c4805070240042d039a000c0c65051201c00051210312400740030141e44060001048500044d5003000508600c40071681080802050501c0d401c607c6079188840003504d520080020940522100041c007552820001c00f10042d558000e0f5440e40038002000c2d001c41281e2108091034401e0001c46e00321691800341c01944024070b81049440a001c21003220440c0e0000d0310700420304d600e449000541c1342603801ca030078103a03032007036003221b42d00d42c1c5490f84041e40030f46c1803144e0402d030802804000b103118010500105030b802140105810101108009410020282d11840030440d86600601c0b00c1ca806011442c0d00203000d03030704240c1d59454040655a41d12542c200e142c1014107024085940c2003084d0000d4106000c00b400300c0b080c010204e07d80c2a48004146c3c3e049101e040c0c4074603d10260000c50301c080010a06c010003900301c030003203c2c04102600c4203403c1524108840da05041c12a556 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 230092221 1250 230090971 230090977
    0x72613050718050402180f040b091c030f0b031911062104110613030209100506070c0509091207080702120a030207030302010c09030f020f0105070b0703151406070605060a050303 78
    0x10b2003004607060605005102e520125a2a40381c035004a5508100c2c12441035084540c110f64016030f1040a581c1c2c440715a400c0030000d00159040c0c110410a094101e0782c16000307151130ba10200300c10801d2002c40010155144000310300c103441c04008121b807102050007118810723954840541b0107880e00100300001c81c00d18074200c02010b903407242c15041c482840004822800000c5c400d0340c8091401c480510800301c0301009210003442070340404c0004600c4494145844000d01c005031105407988110f243c010616035403805914099440000041d14003034000809840515036612514030b030140340d8985c080d0550150324140d812440a6004e03200e070610070451850018000d5005c2c0140340d003546030081c20b4a039241c20f40001c1084044090002c610510002d100d1513038101e4480711910407002c01070320f0714000c5500241c244190360003000b81c02c1d5090b0f0001c0b000310107101c8280ca10341da01c135840300051680c1200d24680100c0c003030000d40300194880d40f2550b04468020030342c03004250340f8130000b46194 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 230093471 1250 230092221 230092259
    0x1020c030706020a02100b0918100f0902040c14030f060a0f0602010b0a0501110705090405010b0d050d0909050f0601081506040f0905090303220303091a0726130507 72
    0x940c0042d004d50019810310244141d0400640300340304c604000c1c0e002848a05002d1b1070304100811b22030440c01004000c00401130700600c0e042051084850303040b45400100000941039020340d04020b6040905da10030810b562200910f0307518181980c4500034220200346008017225004007100364080750300d081a0310400b000305441d03030011030402c20303030b80034400100015404941881040320403200400000320b819025030703500f0307907010384d065880c1d007816405859200b203000e400c0000741230b1401c2801008503039882c0424540d2a906001c540d185500c2007142d0003112003420340e40ca1400468075940c031800e0201d4010b0a11040c103405108850300046039030b1700541c0810680d0340c1c1c54004120048040c040d56078881d0110000d1821458038080d00c29804011001000b1699403c201800c1014001d501200f0380f1508542500205c038141d848001d8405001c0d030300200426000440c080f28443c410f00b01c881803880c000d00a44840e16103030107504c01d50101e444102c0e401d0050340008107280c1e40580c0c4031342d844 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 230094721 1250 230093471 230093483
    0x1f1113030302010e0c13020706020405060c01022505060a090f02041a0118030807240207060209120328050d110a09050d030f05071502030f0405100606020a06020c01020c0307 76
    0x5285140703006421551411820306040d0080d1501841079600d04201c1c1c00008101d40c400b691741e0101d890704030000d200d81d0f00b00c15031292000c03456660b07034034055018015510311780c00704180c2c2d004520040b40080360444c5e4014640e40c41000000c400500c82d401c8007000600c030b03210030310290f280d40c0d0000b030a480d40340c603d181100354120042885503901161003014a600d1b0a0520012802c685445070180300c1d03032601402d501d03012551441c40c4664011030790002daa9a4800f11740f1400280307001c002952001d08002e20a04088a4031003140c08081700b00d50418245014008440b424480c02d04081e8115280b810b0078054240807110000141d800740c030703540c0c901d01d000159076010603040c0540260341035001680a0742d0803e20710340c006a00001000c00541c2e803420240d40b19886032600d10a1110183c0101c02d040d400401031169221040040da07006501c50b5040da070000c00030301c441c0811140c40c0c0c4111001a030043d80c080300816003990061000c04c2d80c600001d03140c506444207641c13075035004040842e14 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 230095971 1250 230094721 230094757
    0x213090803090f19210903021005030603071a090f030f010e010b100206010e010b070813031b080d020c0103050405010f060b030405070602070b0405040b0f0310020903070b07051f11 79
    0xc1c4a030f0910003d80c11800640322500201071a469811240d4a4007031a42c8201804200403100f8502802c03503e801154020400301820b19501801003031a00180c50260180c4034035600805d01417056403010000102d6151100c0c1401c120808020003101007a140d1070f010301400c00d09111a880a005000b41012800c0000c20b900058000f0310603103015132200c00b002c5400c800014001e000310400803c0c111350f003410109440c0e02d07840c2004204c5200d080e5400b00c5188000f000002000640310343c8200c0791811030a0000d1a40da03840903103445491941e29140107030040003041c5111740c06640407581180c040c43c000182d8880340d200c294222100c80d0401c075507280d00482040200b010412255021b8040c900c06071040600e400321074680c82c09103000740c030701c5030340c8400344003400780c40740090400e034002d0040c02c0341c00303110500c0d407500029844a00b546001c0d002d01040850130310b120400310380c040c55000000f01062094440c40c200301d12089007030750464a444071022042c00c000c0b0320240242c0300c1107030003000f4 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 230097221 1250 230095971 230095993
    0x180901090b01050904020109030b0915070806010f030b060a050d0b030102031317070b060f011205010603050709080102071a09030412080d050609091f06080115031a0f04021309080309 80
    0x706618160300c558404e04200c020000181d07440032054041b01e6004070a0075843e01c42074080c5050084100310200302c244080100a00030350b001d01c2075409500284c071141841c812130a8120b00b030341d05c52040c00e5000a004c000c2030745041c1c468001030049212000e030004140c88440006801c3ea4029a240c880d10300c11f10034414248446d0001c4490304d1441703030f080146081f4943d40c8442503c2801458544140ea80c1c101c07602140e40680700415110009076402c11007076071607560160003440107071800c000040c1c41c0100800c0340318052080301d00c000d8101e01c4010341100c11b4800a0b1030030301c0c004c2407505140410b0200249485104c512200190b21414103d80c0320300c4001d10f03410485100500302c6106a02c52824040c10301401b003045032048003035403003d407203003021400b0200160004d58016070b140c1d86008400c0948241c001d0401d4241c03032003401800a003402d04080c0030003c04055500c5540d007038140001ca4010320b010345a91903c8905840045451100c90310b03085d01c280c2040392103801d5500902a059 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 230098471 1250 230097221 230097233
    0x3010614030d0504080604060903030b03010c0f1b0308010b0901050705100c1b08033103120c02060601021207170409020c010f020f070213090b010f1e060e010e18090109 74
    0x40304010700c6141244c186440c24035016a0307400d01600c054a901d6817141e02c003041c944030b07401400300054042c00038448401524402800e06450740e07902c02c0011700040c000c0b003c3e400301078071014040d030b003603510050306908088620b201a0721482d01c2c5418080100140000a841448651403031944070344001a0b8014249000d0000c084126a6468103404500c5e8180050380c6c2e0400d036a00074200d0b81c10b5500e18180234900c203603120100b83c42c50a017021001900c03002c045d0310a00b41c4254600860061040c41780504c0181da035000c0035108240560130035503480c1c0720307030a00d4000342003400e00450310b07540b203203895040340c54041d40260448440d50b07400182400865000b40105a254014030380218941900d0004050541c020a0710003440740d824480d16021000460300412003da400045032500365a50706d1074607a60f84c00c24810080642020300c140340d414141101000103c8a060311010052119040119038400780ca40780c00794081e000144c1030b890035030b5100310940b00300003e00c00041d00304039070304000c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 230099721 1250 230098471 230098483
    0x2613050a080d050108070605040308090a050301050a06081005070e100903080f071406010e010605070203030903010606030b0a08070501050a05071e050106081005040c0e100b03040b0709050910030b150301061403 92
    0x9000c45d580604002c06c042a480000c81d011680c00c0191561542e40f06400a855000294030081c0c3c190b0900b0240300c040354a95202e0000c8580d00c5003215160440000712605858040700c441000c100d01801d02d01d803d081c002a400c4d80c0070314038900026a01e40323a0b656030030250442003401d0316050b804036103c010400001185554110b141d4028401c0350302d000c0c0b00441500d81400b9100800001048801c21901d04009940f910007000f0700a102c80b0361250402030040c100440c41d40d2140e031881500003005603002c80c440e419620181e4400d881c0249144096850303a001d040110f43c07070fa044181c200000240807a00e41c03d004e210700000714220b80b410070040e26114230325140c00c0c4400d2802091000265014010904a90290291000559485c4068052660258440700c650080001000100104601414031552660f1181a0007070b850b0401d014207090f088031184049814900b013071001c42d40d551401c2d5440280101c00040301c4140c0e00c0800d003503031441d030f2000c3d24458042030800c10600e030a002c8 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 230100971 1250 230099721 230099729
    0x50706080a050907050103020d09020904061a0a060525050a1a07140405100c08180406090212060d1103030c0a050708060702100c05040e0103150c2613050a080d0501 72
    0x1c203001a081240b440b940700c03d45445058103160740050b20703080840032504000c40940e00100b2100e41072803d800e010020b0a180f03075480881030540b405016051501e0881c08007030f6181d035910241040180810640c1300907040c1c044810b111810060080012420040c00c13034105c1c85141180c2d101e2002e1b500c200000540a440301d01488914480b48005012480541d070860344100c41e04039150700d4125040d1412481078502520f40b4800190340c180380f8889540d40441032b10b081e50304110305503840d0f03261000c038050502c50f024030a900e40c0c040303611460042040d80b99240242c0c42c800c030001194000901c2d40d440b40d180384480c0d4000742641d17070a100082c44100d0040021070f01409a0789400b110094403541440203841c411550b030952301a080d8480e0003030320090005401201050750b101c0c1064065640200d085075807a40c20706184450a92140c6124861485442420343d4100c40c2e0750014081d0000003440c441c2d00c407448030b086102056042101c0d0344e10368007945165640e850002d040100341c41b41600 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 230102221 1250 230100971 230100991
    0x70812090106361103010f0807030b060f121c020606150304020d03090b040603061707031106070521070201020f0d0906050c160e24090115050f0705070608 68
    0x3002c1000b0408031907080f000484142c205090b040388050b0b0041905001c5890040061030a000150040f460ba0700460581d1404002641550b950712035895a85e03045000081c2954000f1000c0f880e03904182e0014000414018441c0d5154031810b16071a05c0e0042605044441221010098010315018842640c0120701512101080d20b15003d080404c2d201c041e00090080780c070500031000f0b040c428206080038183c0b9240f241d90b0345990389030040140c07241c1d0003203181d61403403281042c4541d040000c00004480e445600d194013008000200001d0343c004503c156058001c0c0f8a00604003015091801610340c41c0758206074980c4180c0c00020700d007403141c080b003068a5100310700919005030005240c400301e60b500d207009540c0764184940f4a050494540303022202c104800000716103000030b80c100300d1203400280c2d1901034031010300c003500140750000c0513080d81250050340113001110704000ea40b109418070382401d915201d8410301d4541154080c0d50243c2d065000103005004041d844045150003104c404 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 230103471 1250 230102221 230102231
    0x607080118060806040305090604170601090c021b0609060d1e060602071d0411120105070210090c14010309080408030c0106050111100c020c030d0e040f150b0a0e060708120901 77
    0xf20f46075540d100043c00c0581444000b044154555943d2021100502188031201441c0014958259901c00c0b0a005c3c40c00824207126401e4450703480021a600034039015406104201c00f64806c0c041ca550084a41607002081000481010403050055080c0c81c1403e8445d03800701d19121800004961440d003083c0e0864012600c10800640e12880f000c0501c00b05c031b1040000c6440710300d8103200c1c015070a1411070300b01c6403a5001000108040d808140b04401c1502518514510348210508442030a10000c2c5000c0e200c5005201c103401207d10741400c51018100000c401d1400d17114008160059404515150710010720203150803404c1c0540c6c0001c10080c248440a804440042902d844001044040b4203648000c0030307103a240700304100146900040c00351042c0f404c1c030890080880801840043c00b0743e0401c50182408540da20884000c80314940c0304c120b8090500903440c0e4580d104092100c1040280701540c80d050f81d89030300804916200c2c0e480196105500c2c0500c5442640040405c241c5034984 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 230104721 1250 230103471 230103479
    0x20a05040f140904031103130602010903080601140703050c070b03010305030705070f030b0a090302120316021b0105031603230601021e060615130906030203250603021605060708011806 81
    0x1c03e042c81e085a4035080c981c0108014480d00c07403550080118031b504020f500000041d4454041d4420b01d0194080d07945e00545a0b144401912484070082c40603614580421810000c40c1c411070240191810b11030035100fa266036a1a04049900701380c00a40c1d258000081e0601005002c0000364028203013498156805071450312034080d078840041c96004480c0d1034009000170140f003404030511080101981d903460741040140d010041d0314980c1c1070b401602c070745c8100c1941e41001001c2a1440c80b016522180780da031351074807105010b541c08840324042c1a20b0702210303100034503100101102c4401021200210349441000246071074441103002c480d4141c010b0100c04a240c021603880d5001605991a0b90183c0d08044c20080910880411000302d5102c0799010595904a40240701101d000710212000300c15800301c105c000b00e4034019000e00c41919103104000140c001d80151090501c007104082400c0f00d151200c0d0b04000c0c085807031000003100f440c01400313000f4500c1152044640070079000c110103818 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 230105971 1250 230104721 230104729
    0x180105030f1c0e0103020c0a061d0a0203120919030b0a060e060d17070b090a1119050108040f050f06060909071d061f0203180d0506071110020a05040f14 67
    0x7407030001c2e020440c0004000d86164001e40450350020f240d00212085407005040040041c401c4c06290303100c0c001f814841030360071000002da4030000c0350001d01074040400070541c1035006a11000820340c0000c400d22006040c20b00e110700d400e00a50158140f950a440c2424552044624641000c070f03070940b0382d90500c0042d880745d05804020079403002800000c825000f018a080b40101c00700100b443c040d41e41003024101d030106414119610604100c81a541050100724004140240c0c59940c0c003240b03401001103611580450350801d000b030000096808154880c0b600b4010b603041000040c0c5c0c400000e100e150304150f2801607010166170040c105035400d00d6223000d0300d41c8110004a60116041003c10150b56820303c80c64103211240140048840b0502c002a4580c1c10030044144100310b92100303503849003046910100100e5010001e8046a500d0702000d55019401e807002c82014070030042e001c41caa000c18401010044421707213402d500da44c47d18800c8500d0242c0c0750880028840680c82c460352940b6 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 230107221 1250 230105971 230106013
    0x6030e0d11060610051b030c0c030606130b1309060510050609130e0f030c06150103110403060c020c03030c2503050c011b02090c0405130b060a050703090302180105030f 74
    0x10700310713000744121071110021100d501078103102e840c00900394400e0021120b4000300400c00c07000b800041d00c14003200c0000f01501c4036000c48046401c441940d00070004804182e004d040e00c808024802030b100340b010707010788080340c040300c5046a0340380e035602c24030035040d019036200802000700f110810310b03040380707030002c5031180090481402c5026107500200400e241d042c0308484611804800312910703220140561559400c003030340c0c1c5001900038580d4000e01755100340200c031254504003120038a80b91569940c1e90050ac00340302c181003140550b9030307001c1c440d940070700081080c1c65061008041c100c0320101c85400103a0350300154001e017502f091080000441c04185004000024207000b5503c0004c82000c484000e400303040254000940c2040010b0070041402074002e4031400d44110a4400010b54010f04440244807000c3d030050040c098071581d280301e00001c0540f140320746041c10341c0903035070742c040f680200d40d2900410218506200602a6003010041164200c41c0b85005010061f01d40105140c211 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 230108471 1250 230107221 230107231
    0x125708100216020d050a0c06020106080703110316080102030118180201030b01020a0606080615100e1507150203011502030a09180e03310f1415030106030e0d1106 71
    0x2500410050050489071503089a001d4000d010f001500a591903c40d44486c409801220300c46000c47c0007003100fa10511500c1c041d101c880004144081c155216640510740d1407509591501c00c00011004918402c0c8070400140005000942c9035410104401c4055a480300308038400ca18107048202000d0040c580000899020700f0001440d1740007000403400c000c024200075140b01c0c1030440014005100003401c038031030354014221040680b000c80421418500d49505a0001881244a80502d04d00901010012401c05160620300070175540e0350704030703000b083c000d808d1401ea002c0010811806840750014200d42c60784003641c41c00c003a590b80501004554000c851400480d100c066512654a40c41507201401d0300341185e803680803504031800f1890140760290313030041ca00c015080804a009a003101513400c42d60f80c04038500c3c2003401d151f900944e40440380c4d83c403401c10714006032445a0340c1c1c000c6010b46144d5401040c0c0c060251740c101d26245500020f0401c100c200d80c010f80b0700c050040780e115085 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 230109721 1250 230108471 230108503
    0x50306060f0a0909020f09070206061008091e1908070b010504112b0501080d0f0513051e0402070c030b160c060902030705040c0e03060109020301125708 67
    0x1280b40c3c00814680001b03140401c3d000382ca1242440010760f000103400f403107848121942001c200c0e10b50011900980b00755103455895000c000300354481211a0800c65440c0040d00807100d10300c050010a41a014800409803040c203000200c06090205a4010030301400c8180c0d014170883c941d14034090500e02c10407510706404005001a0304408050001d4030b03000c14a4135005000300e50310f9583e103941b00c2c1301c1c0d856000c01048000e400031a0f002c0c024070540780d06c01003d80c1c2d03607140342c0d185c02c0c20b000e005140f924980c1203c2c07281d20310820450303565101070280715000d20704200c10303d41907160401e90b028018210340c60600d21038200049060f488401e00e5511039001002141503146403000c05d10713012080e00030603031190a1640005040341d0010750805502000c904880c041c0e6a55070010307080380b000313004044d412001c803208000402e402d0700190040c200b54201c0500010190200c0b50141c10000104142c2d2003102140120f0301c030340d030218035100691401e0402c03404d1031904560755a00d901e000300d00002 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 230110971 1250 230109721 230109731
    0x60f02010b120a0210091d0106030c11100c020708010504030203120a0b03100c0e1e0f0607050a0201110a1e12080603061f03060f0506040501170309060f0c01020d06050306060f0a09 79
    0x5c464880c400c40c2000380104144030554505028450801c0c540c00d0003810300107172410000c024028429100c0c9145440e0382805881c0c0c00742288540310103400200c030958150b205108000036014001d00c20340d886540242d000e5520740c94001f03454a0691000f410484036181099501171456501252030b0741c000c600600e000a14910006080e219862084000795004105400c2d4107080c07801d003030a14212820440316400c15074010020014140030301000601180d01071204a130055018044240d0100c24000844000b60155070f6001c0c2c2e80030000240041ca40d010092000412461902e01c5245031410305102d11940f0b030081c0404c1c1e840030010310a40b20709110720307030400070002c0b043c5001010b56003000f028441c8100c41e0304040c0240406a5005000303d262a00005a10360b00d14500d445650f154805545400c01490401055406c81c42c7d600300f209404220902030648244028600c00450b16070200f40145000100750402c0c000400a5000301c2d02080d454100307a03034460800080e40c1011400042d = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 230112221 1250 230110971 230110999
    0x4090203060a03021306030b070908100b0433050409050303070e0103060b04260a080a050d0f0507080420210109080a110105070c0201050906090f0901060f02010b120a02 74
    0x200e0704109a1020307401c455441000d902801746a0030500540b40a0680f0303134151380300d440e41202c2903102c074480c0400307907001601150036036912170b044120703010001400070441004041e03031400b2020404c039101d1044411030340315100d404840c070b00e000d00501e811107041104c00010f440c0d10752a403100a000c101049281511801c03680c1c000e230b000300050440010115102c0d038a0342c200030400358080040c80c5480c2070210302269000c07400201072122035840400d05080083c1c3c004241c5680e00041942201c66031942c14410203003c1c2842450b2092410f940c031001141401c1c01c12001030800e89900380e80103030b21510030b8041c1d0303201c078008030200224442203500c000042d40c1c0c1141c014891100c0003000041c0004a0b03001e80e641c0443c4480c403c1d00b02c03000030001c41e15000e0301582c0c0c406c0c00e034000030302062080c4030b25406441c19001808040d13401a00d0400c04070300900000d10440310036008580400c944491980d00240d0901c1800c01d0703900d065440c08401d148a02c44941d4030304048500922551030224004 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 230113471 1250 230112221 230112229
    0x3150d020a080f252d180c12140105013902030706050301050a0e0c090907030f0605031609110f0301060c020f03060708060603090307170a030b0d080409020306 70
    0x1200800302ca00a031121260510342c070a848603040754590751825001404020700b41e04104002048030100071090a807500260001c8a04409a501c803400c8902040800103200c051174400c5c940419034050300060304100d02c0b202625410412500056941c5840301c04200400380800e05170540e9000d083c500e1248400514000000c40c09460074882c03410420300104400d0000703502d0041180c03084080d144001d484450840c0e4a010034410f59900c40643c540410030002e9190800d500724801c4c0d0341440c034000008000c01d1030840306580c0800080d1350707201503651603d5140300c0d2030040c05044001d0294046020880038260309a409506440c6680d105180c1140042c1c2045560707202040c1c401685960f52128068085101c02d4001c0e1301030115604140e4551502240c0c551041e11aa29107080a840c0c032070074002d807034100410042c61440208426000b0522003402248011074040e1040e40c0d9218180703000301600c0343d03101424080c1c20208994000501080242d400780c0e40441001a200ea0f0307410002 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 230114721 1250 230113471 230113489
    0x109020304242a0807050c100506011419030b030c03100c09080d09090f061206110d0204120218090d0c0501110412050721060b06070204020c0a0506090303150d02 71
    0x10100c4010100d80e100303c1c0000502c421081041a01c0360691562101030585452042070398255203600070f80300c5141c5000107503212640040b0107140002ca598900c1e10f042106a2102d0245c01c05021800c0c0750004242d8180503114044070158050100c40400d840465590040f0900b01804952100544030f5000d1064010200070171040c000c48160300f15030f04010b052403150b4000c00c501e0700e05000e481c8c4e1910007540201030844403c2404103c181135140c8580b801403606400511000307004004040101d0b07500d001500c00f0306003143c40a00c00e46164410842c1520f0041441600f082d00744040114122003c2201c64040030f403804c0004011740ca51400d80d0050241c411041d074802400320b00807803c024201d147c00051849002118021500c40d0394030322402050200c3c5070524036403a4007d00000d9441d0700144200107014040c0e9003490200d0780005d0503071f0081b41814000341e1100b003600d0144041082a290004410b50207149141094080961100081d40405025031a0a0340b40811074a901c044 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 230115971 1250 230114721 230114741
    0xd051906230108190603031e0309030e0105070302100c02100f06050d1b0b0a0e1c050d03020c0f01090501020c0613080f03060616050304080c150406030b0112140f010902030424 77
    0x104001741030b200e14000d00a1003000e15801c090000c5080c603c08071f54024469404804d03010b4640000508480e0011a010b600415040301140202c10030140f100300700d8019010408916009804e0074009c1403a036070300301c40343c50b51010000d5040c50001c01454a4003601400c4c180d4200b040021714160606150800c01031651060007020400100e9400f20b5900c08280841c0c10300c00c41e102c0c0f5620790440009c040480100c00041c0041d00700e1602104020300980c010a0f0729103091081d5605c140d810039100d801c45006078803d07101a500001c11500950f020700c45594000500c4004031030050103a1143d440c03501a48103030880301100080811050754904065030716000398450080543c550600d4155100c0e0028868070790380303104581c2d0342040c0c0d107000c0075031041060036008968102498400220050991007501d03030b0500c80b00c101e01071a41d0300d190003458406c40c4a000100d0441c04c1202ea8114241c5059001c114414030501c01c2c40000750008400380d400c000c0c0c040c41c04d981e00c030700c11100100400c01c01c49 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 230117221 1250 230115971 230116021
    0x31606020304020a08060f01090c120504080403053708040302100315140d120c050303010b130603050112120203090d141e060112080d051906230108 65
    0x501004108060300103510492007550b06084141c0d48181c850b41d2080d0076950400f0322500e400043c4400b510551150401140901d4806001c0c030400ca619021114265800d5070114400101402842401c100442090400d5a0304942000d05240380041c154100c0c03080c1182c81e0150f1040c0d1052000c03000c181c401540e0002c1442c148138241e600b000d0700920304248202120400d99a00050788041405024149a0040c01006100c08641d841910b030036903803218903042c031a03400208404a10b0810103980070b02000c0641c00d0380e4500000302010b11242ca940031404060800005011014500c000c400c1e4860380000942d00f46818010180d0540c0614100c044c2c203e0941012a01441040c0000e0b0a5051191041e506c100600720b1000703e501904183e610703801e5000c170f801000301e0a21074844e1500e03a40a040440c0c18104044111004d461090781e040b0003c4c41880092046c101303c91082c0d100403c490401480d00100343d0f00010f0015003040c90035410301000d4000200d86540d5901d2502c91442441 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 230118471 1250 230117221 230117257
    0xa140310060801150b090d0b06190303110609010504030c0615050402030a0b01030b2413080114070809062a04030602121e0105030c1e030f07080c0109030816030203 72
    0x3014460003400c50041c2111303003080d90079000902170361050072242030810140c2880c9600580382c0b0340346c01062028081a4101583c1109244905120100103010358845e035154203006c0800c04e01c0c6443d0103000b400080c1072343d00d010184030019410100742d04100340d1180703003c28240307541c0034428015903280e8020754109000008220814100b17900c580c4a0080980b030400c081120031040c0581c0029640e00c1c484034440d22407842c0041047c90002e0146600101810720700b10380c8a005039405d5803603401c021070b491a07a44062024854020043d84d13800f081007001402185450341c0210342c8145144100d03403850400405c05000c801001c412100a0354016405550f603204544000380c0c100c01c2280c01d84c42d49038424240c8440c1044000100b412148003c00801034a0b03500400c00c072458102c10900310312220510f00e24066600c0c207005e9a00d0008038003018110701072a0141150819501001c19810442e03840c4040c80011415015107083d08200400082000b20602c0c050740746100703484044002c0c400301 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 230119721 1250 230118471 230118479
    0x20309031b0406080c28120c051008090a020108061215150121020313060905060103140d050301170f030f043b04061104060e030c010e0a14031006 64
    0x41c03190311500711060303504200040e03a941c502500d40c4003116002d42c2c4180d00c801d00384000200401c03015220201d40101c94045d0b41e1300c3c500941b060907200c00442e4000514103080105140051500d0400292800c003103440b481c1070500c054842600f000020b0501c14a80040340058035019a4040d41072500000c07120300c0f00d001c0e5520075521104403089121688082c80c07401041d44224402084420000031014414200070309620103500000d000c196801742d1a150040443d180d8043d44170310030f021302c002e4451541141492560030502180c4110158409440c502000c4d52140403a411990540c075100c0d0801546218181440d01000c80b0454034170012480c020290710b010028000c4a8402c40c68813884204460010505010742d52081e0803140c241599110b072858000009620601c101c2000501c00d8050855440c19001743d0089000a00c0382c0c40320942c9030404001d880e442c4442400d0284036102e28a0000e400744020340110b03117001a0b440701c22210343e01d041000000c0c0c60342e500d80a0003c1521 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 230120971 1250 230119721 230119753
    0x10c03230412050705040b0a03060e011b0e030d03020906070f0f05030f0409200403061a03070f0303080a05041e030c120309110915010f090f0602010213150c03080702030903 76
    0xa01c102c00e4556002d13031100011207142510411013181c001600c51082285035407142002041c882d2950005035484030b03194000180150280303e07543c1026195210408e40d801c1c281032420217810921018180304206200c81952010142c8940d66070222014401002919040c8801e100091000b80300c0c2c0320101e00190000800341c013400c252884000104030011016103404822000403642c9140040e0420090000c02c1e4030350070110501c2c40e002c05241014000350080783c60164554489030703024012841c14001c250384a0f4083e604840403000500035030401d80c442d001c41200c0e420200d030f54000555401c904060143c501c2d08000d5400501d028a04c0d44191409000b90004141c1240d0207581c040d81c002d614501040914010207800300b942100c56261310065908035551000340742800080d61000a01c6031100d4011409010b07123900240e00e0b0400000102c00072615500044002d1840e00c023400310541e445454000a00c0d01440d1a07a516240d480050381140704071204150140150308030b006080ca5 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 230122221 1250 230120971 230120999
    0x12070302150709080d230901020c030a0501020c150603032b0612020a0801091a071403092d0607140702040e0c0108070c030e09040317010909020a05010806010c032304 73
    0x4c60140d41c050984918211180503d80d03008880c400179450b5442c10034103403000900200c11040c0112800e071308007000043c0c80d001715240d048035036a4001443c2400c0e0101409624240601010346252600b0320800081d141c1c05030580c44040c64580c030308072251441404244448110041000b0003007203071184000c03000b00d01600401c2e4081d48030410006000841407140181094010102c0400980141c1d040c50704010050824030402c0102407500748007541c9440298010507600008180840c6241c01000380014042c0b08298490049080103100d40d101280c0c859110900d490030305005581c08440440c20b0158040c065003007403414507036001c00f01c1c00160040300a03100b604d58004d1683d850000f207901100003800100020a4110041d40d00d082a40764560014840e0410a0782802c00c076804400c1c0c11000d030300c015840c540b14140407080d0b09241043c0b10180c0b00c01e1910030714500d09a40082e2580c075038840000d041082d03004408021134440ba6031880071814680c544c44c2c0d40d0360784258910b1101 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 230123471 1250 230122221 230122229
    0x12030207060e0f01210209180906130c0308220e15041107061d060708070f03090b01060c1502031003020901050a060c020909162d060212070302150709 66
    0x14250310b030011024544103100c1c00a610050752840c05402d4001681c8041200c000301400350340b038090208606640d6200344500d8420f013602150006840c040c8180c030300c0c04030090071641c00d0000c5500d1290100d061000c0700c4040d40c0d00005600d5542598000400b00c00e10a03039440300001c801e9050100300b1001082940d80104562010380403140a403030100011542580710070f440400c2d0400c107075000a0100d4204040081407a81d0940c220501c9510f01d50600d10301b265114006550342c8200a00c542c1c019003440c89a94175454100100500d42da100070078101d06003e8001809650442c2a080154448009440f6110000c065440f820b0403070405000c0207090008a101e40307144400032407181080703001c14049031450791f203240030540d413238007885114800075110030f1321360282d40c0640100d00d14510703c8100905101c0440301854404000c102c4589114004004401142602c01c02c000d9070300080010340343c2110071060f035a943c0c4519060f80b4005040001803000b142c42410089459002a9118111 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 230124721 1250 230123471 230123477
    0xb060118031e20030705041a06130e09030307050313110d05060604060603090b0606092803061a030604030806010201090b100503070503150f0a020d0218100e03030f131203020706 78
    0x800c54983c00c550490002d803501c00d4151340300c1070003000940380541040c0652460b03180600100214540400d00c180e04c00b480030110030364001c034104207010701c140319a80e0115000002e107085051040d00209540303c0502983c0e10f00389080301040030b00105040c102400400100410700c064201c0c5841510b900048402ea40301d07524050001925502038050188041c0d4080940509566203004100c203d4105400c0e15070800c41411a02d000240da410100c02240c01c010307480e020781c52031494400f060340c045115000e15001100040300c1c040d2000100150802e0b410b0500402c181d4078000102e0040ca912030717019101c0c5000c1c2040c040700c8041c0da1000826a24150103507040c5039102c0091640d504454400c02030303044d10080c00078601c41040c080e420b400104045000d454440b0482d0000c090360410b03034580a50701e01d00085140e6500d454842d840e0808600d040141082c1d50440004e0344a000e08011140d044d000084c481c025108103030f2645001c1c0005010252030035403d420002c3d07591805004034004 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 230125971 1250 230124721 230124743
    0xe0f100f030201080c0a0203040519090621022101020409050117010203010803030f0405100905030d0f06080c0603060d0b0c030901060e190903020f072702070b060118031e 75
    0x160503020000c0d00766a01030b114040c40d51502c0451141c40d5005404080c1140002c1c0804240b0f940c400c10110100381c03407148203003062401e0001c4c080498038a58420030b49088101c11030f04003000460501d00c2e04580460310b00418028140300704d0142e40c803042c0c1804907544001000711342c00f07540703900190588540d204051030301d911b18a000ca00301c0c4002c1c041c00c20701d54014030000301e040703040c01d40d1964090b21030030544101c1c0c0400c1c009001aa00b19840448a43e000450311100c4801144a52000c0380041d61041c820fa511341090f45459140c5021074034080d400c0000001e903541c48446001004035404402c003915460555140320640d04159005207165003040d4000031220640104e0382c4c00744c14401d078417280d40b030f503801800310041040003000c0341503009460705900303000c00a01200005101d06086007551801c0b1550061180b005102c00820140c4140001808100b544100b140d0150082c2004500c1c885640c2030341307a110117aa07000034669907405500a903204807002c1c145143c00e10501014003 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 230127221 1250 230125971 230125979
    0x609060f0e01120f0f05030f0a05030105040b0a06090b2107021510050a0605070f05010c020f010c0c08030a5403020607080c120a060302092805060a0e0f10 68
    0x4503000410700040d2190141c0c1130f01e00c0114004551040c1c1c49403051003280c1c64038014050511440d000040b00c403000c40c80120040002d81001d0042e604411400c07580201d640b0b0038440042d014143c180940921241c1c0400e544030000031030400c00384c1416690107403000a28011000955402d040c1000440611540000c10035000c02e0301000e0040da070000380101c10180c200542150030340c0100c00162074080079802c107200890320078400c40c840003490398050480d10010160450035551506054000c000c030005006001c40e54041c2600d400085014000c15003074070502c04580d08403100980d82d0100d48008d03a40d0200d136013241c9281e040c0d960b10b45080b0301c0800411450018003660000014016030468400500000e101d200559405042c4810316400c011000e840c62140040447d13a140030300b541c0ea5030500075841c110041e1980000c20b0701c84108030700641a0351000c0400442490306e800c54a0300d01040c1c072991900101e1028000c2c0d011103100b94540180ca0010f0030205075550903107850154000301d = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 230128471 1250 230127221 230127239
    0x1b2001030b060f0913021c060314070803090f01030905060c04090f0c172509050301140c270603040305130b0903030a0509120d120506010e1e01030609060f0e01 70
    0x90050383d4a00206420f1090540a101100600c4020090010380c208407000300102810868496840e18040010b0301c10f095180030880002d903070506507103550100d2010850600008200c44c0f03003540a0741c1e1004141c05000c0183c0c0036200c40040105031380514420002004402406030044841015007030181c40c20f00000c1c1c2044078442d0251400043c101010b146901c50100c04254100100441d10f1003010503034145d4150310b85040720b61100192180d6820401860300740a0071005003003e00581c841410415072410b41481070740130030038803003000300e2f040e4810700c202d40c02c296100c00c401b5001c90b0f681c0c40c00349002030031a4007200402e01007004000e004598a0840819202c030300001600a41c605044981c09440790f400c04e002c2ea59008185225004425009019a500d2030b00301c2c0e150641a0412103030f010003580c0000380070a04028008a070800702e5500c40140b190f42c1c4115001c08400d144140004801415540c1c010f65005030030031500207503050700741902d0001c4030b400d09920006c0c1e90302c81104d0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 230129721 1250 230128471 230128477
    0x1002190e01031a0f0a0807090605011d0d021207030b250306030b01060309110406090e0d03050f040818030601170c06040b0906030c0706050901060f1409071b2001030b06 74
    0x1503120f400c000d80030740d0407420f210303108201d0700c8001004881c1030703591414228039054460300101c07002a1540c108220558122030842c140c1003400c00e01002e640306090101d036020701d2418004c5d100b9681403901e0702908a00380800000307107400c007041141e5440c140300202200c0c280e81a000400341c05a03040144103a11a104407000e4076032020301650240d20380b80080740500000c002c1030380c0f040b0110b02c0c0710309103940c2c511071003004003000240802c3d280c020b480c0450410012a83e06001c1c14240402c01c41600c00060081ea2320035804101103071a040c0c00e11102c2c402c2420b054589030144544000400c2c030100f048561800c1120840072505c1c105542e005002450060344150b82008809000180351803901c0c80245038420f006210300d0381481c00c1e98807801d040d1201a660200c8595440109021000d1002d010130081c280080c2500c10700e030940342c04030790301890040c020710401151040c1000b1065402d028400e00c1d540180304400002e960403041031025501c40c00d5140881d04d001130b10720503403c010381a = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 230130971 1250 230129721 230129741
    0x1120c06020f070e0703061e0302090609010303090e1806070903020a060207050d06020a0c020a090f0b0409030c120e0d06060f0801050c0a030c021e0c0f0415171002190e0103 76
    0x60141c6070300d0301452180c0c0700343c05840d174814183c0b01c0a012a12144084c64120b07501d83d60840d00441300d10398014403030164805041703940030f0340e0064010300c0401d81040e41d03c0d0444042ca5005403030340d0350300800401a1117003c03070fa111241c01440144105640d12014a00a40340203c884107803140d503801081c0e968a00c40c1c030640d42c10032003110603500410150f9001d020400018100f03a89091426400107000c01810380040401030303941c5130403080081030380c402e0421518090b10f042055050740d403805080b880701c07940300412600103981a450304921a29100181c842e01800c0a00d108115103082c0025040b1030040314507000740c400001030140014018a4019944180c2d1140340018035541103000c0d0048208c00815880b80c1c90080720f10001c0075000e904940100340c05400e01084e01c404101c003107808510f24034425170034010b001021091007040c400031903003c0d41541200c1854030041c81c2c103144000401d05c0c4100d01c04034400d070a192114801d40c2d41d0301480e070f48102c41101c500c40150100d4070110f074 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 230132221 1250 230130971 230130973
    0x3080d0e0705030d12020c030301060c380603070302040e150f100512070b0f04031101021b1309050d0906260c09030c1003020c010b010504050d0807080f0301120c06020f 74
    0x104c0b4016480c0154050b0790a01c00c02c510251801560500d00d5140d680300ba44124006284c9011741d40601103103685580c5038202c501c600e40c04400340750400e00070781204c50032040754520149020a01650301040f20b4001076501074000d021458442c2c03140740c0c0b624038205040003807030140320001d0388220001c41114800c094100060b00c249003040d0a208406132642403610146c45000c030041b074522000000740520711181c4440980e100e0440c0f4000c00c5041206140c681558403850403e0740a007500d443d4600c03200410350b4502c13540608144403001400d20301e00003030294020b8589507034105900071010741c10741c0c125481d036800c0340e607494803d20b146119a40170052540c01d09004038024901710001408154002003c540c403075058000081d00c840e21902d110030100c1e500041400c03592200303020f1751480304001d0030503500306403820001c41c442da462100b000300402030024000017000155000d60b0760a0071120328040d125a100d01c1c00340e0341c1140300c6c20f090b140d10749210381c0041d05c40e100140140c80400010 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 230133471 1250 230132221 230132233
    0x10c051c060b0a030902031501030b010501030e0309031c2105041101080f070810050603070809060a0605010504090e0a0c030515010b0304030518030c131a011b0b0406021303080d0e070503 82
    0x11400704c0c010613040104981c980103005011020038040c2c80754501960189003007180c0c1d540350800140860b62035201d5524036800a00020406950100318011614124815914a401c17402e01c202e40c0902433482e911084290800c1c8000001c80f0b6902a030302c260310900494407641203a50041d600c420307040720042c0b901c0c18401300007140b0310300c074500c216040700507007200300d1903a5103c0380011003e400840b00040051240c00801c20741c01001c0008a410480f440010070103d400c110008100d841030b40a015041d98950800c078541c50010000c0c5040180c00c41e010206030303526868183d80341c1c40302c6000e903080000600300210f452403004046034066503058a45a00c0d14002d03100d1520003003c281801c540c107001d42c56618400351141c00346580c0404000c40c0000d6050243c0c9052800303a01e8501c0110704200242c00d054080030a000b0310b182c80c844e000490814103658500d0a603000c0e00c20144540c074403d202c800000b080001d800007402020045190501c24981e40c40d070701554800c0c11f84a19030389a8022 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 230134721 1250 230133471 230133487
    0x30103030e030a08180f010e0310020f04080109080d06090c0c200301150e0f0105030a03081b0a03020a0201050a0506130209060c071508070c032f010c051c060b 70
    0x9900d0200c040c001c0542519804040c90300c590450342c00004000342c0a00c05503012410a01c3c003940f1100c0039020900305813201241c2200481ea0b40d81e00c0480798580681d000407501950710007a8155001041241c000303000c00d00c0300c0d1500300001d411181c5040302346c6051040c00309603d130a40c0200c540503001d0b591800e017003110603150080d110401030111040000380001030b0305140c07800c0c0140101d0661541e0402401442c060b0b02c40c0503900010315400d400e0200c440103002607600810b94500b003a405161a590949908121068404c00d02d43d1a0901d4039000509401207501600500390b4500b2540081000d9a54861040f0a5030400c0f1031490f44200d103e0300c00b246055080c0d025103008100a0415030070800801000b610303140c038540242e98414420205286e00641c8042202e510090500d04030040e40b083d42c0d0094601e0074800115440591b881d52101600004c0041c3d0024a8184000030f024011185801420ba60312130100362090712801441c00340b21350024054541110610b50320706280c1100 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 230135971 1250 230134721 230134727
    0x306011406090d1e0b06030c030f0312180a05071403011b1209020603091513080406200102190201060b040f0e070504031401020901030b120c090406110d020403020f0402040b03010303 80
    0x240c411500e81d40c40d030204955080e11840e0440f24144585d00b000c2c200d092a500f09443c3c2016054001d110f61701c074502c421260710010040d09d503006060711088080785c882c0c0c252002c840304595a40a42841142c58260502c0310000e18a0304840c10700d0f200083d1411a072080c14283ca01000c4101701025190031140e07203052080340c00c00c1c02c9800d000790009848082d41d00040c80b680c4161140d4040350301c4600341401c02002c40340b0032504002c100701000840000c076134408025004921580e400c0c81003000000d4003450550211100080c0c10000840d50b03003003010141101350b502220107000662828101254840d10381c0704940684498000103d030070f034500100360211403801460b0ba0200270090100000107000c40304001000c41d0000000341e254280d15000404989941c0011031148003504400b0300c0c0b0038008201e0704c0d80e1f104141c4a005a41e0742d1414036201520300030402028901000a00800801540c0c0c09441980d01c00c403125429401502e0400c000c0c2c0c0924090b0350740c031090400c010800a80 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 230137221 1250 230135971 230135989
    0xf1c0f0e12160b190327020d080c01051501050406020a1103010f0606171b0702010c02011107080a021305090607050304062a170c031306090b070e030601140609 70
    0xa0601c04031410761a0000200c0c0701440180d0001181a00c08220105020404000c6400d024001d2800f0010440241128401401490700e606643e003c3d01c0080c0040d07441d83c29142c005c45400c4096180e0707581804240900034582211901070f0041c413036045056640c4103400301e4088a2140d4010030f1503031200d449a41440c40e19406183d0715642c0c1d0740c58640150003500a000040045898528804488080b0b2119100004080e001a07450207442416422003880945080303940a20b0881074004031403006880360304c0300003034855181c03186460000703031200b001500d03042040c4269403819414013907410070b000b0350b01c044e0b40c02000c039004040084d01032446240519801402040c01007200c000d48810005629201d80c076072440001c01d240c0c0c1c03100690f000075003010341c022880c41c00c111a2070108070800365030001034070074500b00d40401d03800c80900406400400348260403a03401e05079410300c201c026041d100580d184501a010740c3c400000d080c40d03848080103a04802070300c003a1806140c101000b803004 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 230138471 1250 230137221 230137249
    0x1014060c01151e060203030105031e0312041b05031c082a090a2103140c0f0102030610020307050a08030c0c010c0207050307091e05040f02030f1c0f0e 66
    0x342d41c408012000125801d003040040260003050400003c56103024003550015030407407410755104100400081e10b0000e100e00003040485080442c9198281625065204620003101010508800d000500c1b28040c00350b80d1406c103190018041c40d5030b810605486030700c0808451a207150020039010400d025840059200c0010300d9088282c43c400f00030799500d14502514440003900206040302c8500b003142904d405020b4100e02c484041904d240300c590740940c0c1400040c1088100043c28130b0701c030529000d403501040c4000c00e417444001c04040042c000c1d0012542c5500c6121080c00307030260680003104a130303241c0ea040405813206407240e49618405a0000d81201c02c0140100311550f0542c07402e220b50b00075040142c2c080c1c80486c1c40c05003003514095031a00702050b114684a40c5440003c3d0380c40d01d21411110303c81000c1401c1e40d031814000005070701e0b9400039400d4020054a41d034840f4012030a068901c5040940da08522081001168241c240345510000710b50310a01210440c54038007a519030034 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 230139721 1250 230138471 230138473
    0x3031407020d05190203060601051c1113030b16080405060a0c0c0b01030506040c0f062a0c180f140420120d0212161502040801150801051014060c 64
    0x191082d64075a480d00010070750136641e0002016001d411071409211031500480c00b403078500e0400e044011840c00d01c070005009000e526136521180603551404c10107952001c06201c424158003680c0f4100860085400c03540c1c1c0d4002c04e0095000d512050080d101e080c01607030040d00402c4140e07500103803200100543da0b420828850b0b0b00913900300103045440f8030750280d44644060642c9092030b181c29001e405103074001c40554403807110248442d0354030a030794075801d00c905c45241d00d4146c1d0000e0a003000d190510301c040c1c008440f2a2003c6280c0ca40340d803920800c1004c1d05810440b01d07c1905040c02100c14640e142184c01c460880481c01103082c2d001034100040610713601d40090f46441c0700103100c1c00840403007180e0701d400c001d0200445580600544910549542c030561424002505160005400c2040203203261550a8148940c2000f079044c0d1303003e0031030a8003c0003100e2071142c404000d103005200e4107106600b400c0c0007c41543d00c0c0500031023180e00c040005007201941c0d4082161070382103c6002181 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 230140971 1250 230139721 230139739
    0x60f030902041109030d022811040912020f01090f020d0204020d050405071701020c0c0603100b0301060206061c44030f13050a020108070e06071104150303140702 71
    0x940d90b24480c158650210603591595016100241404d09509034150400d5402c14148000e1300c28051496000001c681e50440c00d0b1242c592806102040503032072001e4026183c20502c1d0b0400c601100c1c42c01c1c83c0d803604d400310303007005601032943c1d426201d03015001080d0306a241c41d41c0b40141041c9d40d14880951004001508120100070313042d045880480742138465078080042000410700c0c44107002d414005202c001e40c60201910201559410405001707801084000001079100361800700c024050b1801d15282030fa80c1d41d48400003940c880c42907814138440c0540c4003014015440c11074110b000c155100d01841e816142c038960b80c0807110303010202100341950440c19128040e131894411441c80e0914982581c0724100b03c8442200b55078020030000100c5044500c00c0d0100f1000a1800d82080d424604a080c03591803890454801c04a5046160088000b0071408100030440411249001040c2c904020f020355440d400751707202020307100282c0810308900d403800c3c050300e10314000c080d190300140850342 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 230142221 1250 230140971 230140973
    0xf030507092a030501060e010c081e0c0d0f26070c02060f070b01030c090207020603010b030709030209010303050c120f0a030e030c06040c170705010f0c0201171e09070f060f0309 78
    0x14902c000740b0444000281c3c2c1c0c0f40148181504410100309071030742071a00745000c1459a0b1001c4252080050700244110044100d412596010044404c1c3c84a981d00756003560f2818200030700902824112030000c91003021103c102d09817100c11100e01e80425050250803900c0f41c00003502d100201820581e005541000382411001c0110300034030b102440b564030f00303015600d5414010740300700d4150011000780340104802c00c00350740c810098a0655100c280d43c80c1c1c1d20b8a074000180d42809650340020b4000043c1d5000005154101c805031178101201010344503900031501412000d403003800101e2081c61820300001000c80d21079480190100d0107002124508521408410314052084604541c9045203020600980c070000052003a4601000020701c1d01c5800c2c20006054488500d100800300120301c12880306581c411041c0c6500e40c41c108058030540d003044082026640a0480f6444403611030102042c410b10b0f000402000300e6401c07185854440307041580c101d0391030b80520344840c20036450752076000c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 230143471 1250 230142221 230142281
    0x9060e0f0a080d1103040506030601051602040501032009010e0c0d0e010e01060f0e01050a090e0c09072a0206070f0c0801110403030e01030209090118090602120a060f03050709 77
    0xd084944003c12101d0034a1400619400088080301010780080c00200181d031221010303613030420001d0802035100e001d04403103014400c2069001940c010b041c00d000105020020309040200910b4801b09917048583d01c1c10300421150138400c03e11400784100015184114660290035441c94128003c0b46c01c2c01c1104400c0d09480480d40f410039981d560381801c100f0b40690f000940010200142c00091540c500700000b0300640d0340c1c2c401c009515441d20080c0f04480b02c1401040701c1094000c0c1341d40c1050900b480018086880c0100c1380600c01c20407124200c13a4030034196034040265000304610700e49400c55031207551949082600320340e608541c2c0c0e408a80108280140d90144c43d0300415192541d203035080041121020041003414188100000380594480080c0b05042d87c0250302d880c12208400054000140401302000e0702480c40415040c13410944015680e000e84030310307981445a540c4806200300700c480548001441ca40c03003e10200501449904000605a1800000012034802003a82 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 230144721 1250 230143471 230143489
    0x9040605150409060e07080703120f11240c0403050303061519020c1302030c070f081c020301030c08010e0616090f0617070f0c02060708041d040b0601080709060e0f 72
    0xc550341602c40d25441d015220130003400d4000d07d0b035880100302c4c091840c1c491f02c03007141000000b0001c00c010079510b80311050141420844540403101269180c842e0401c450140039900d0348036407400030041020a08219100007580c040e2604400038615644903582000158903002e2594100040c0501038141802e82101458800a60903000340055000c81d4080082d1075404080718145588107100b8000c5c072041b1001925035440c0d00c50b9103015444541d0421140c14003566640c00000c0b0b450380318110a11110b6006581268842e0200303001094807000f000342a0341c11448485890380c08900005d540e10894101d0669100403030601c0c621543d20f4800b40c28404d0310541041010481e1003003090101181d460b20580d00c1a101e243c41e10003010780a000500000494401170b11402020910100f4050000300700d60040c070700407035003440ca0510324191148061048406450702500f040c00151654000d00801c0c3c40744002d03980304444182440400c2d100c041c5c02d20074050f080540014680c1c8103032130740408 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 230145971 1250 230144721 230144723
    0xc1c110a0f0e09010603240f02030c04030203150402030c130e1e0f1f0207050705030a0507170a03080a05040323090406060905060f032508040b0c03040209040605150409 74
    0x4240791030303041c40d02070142d203540940014481d0f85001010070204552440c4a076542100481044507818058900c0e4064041c004081400038070000a014030f0042603002170086034401d0b001c1e603c84856844007112400c07030460740a501500031040c0d11440d0700d0440007803003007840c1000f00000d050843c114824030300351000042034030171450540b00d0303030038014200010020000541e00410b105041c10b0700c0c0d15004a103c200c0001c821f5000b04400c0d013007100c140010300182001608a8030f81c80a241040c2e6981c46442c828a1000003100101141200021964000c115010f48403988541c07035030308e080c80003000020001d03000c00c0040ca50100182d2056003800c440500c601d81515100e440711000c000441c1c5290f44120180900030b00100b04580743d843c1039600d42e11050b031b0400d84950b10701c0441e039191844650f01c03030694010050b00703d94041c3c104180c070703011358024a8000a169102c140011491005580195201c20709c14009000128035420803a4002e02040f403403824a580100850159620844 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 230147221 1250 230145971 230145989
    0xb040303050f0105060c070e070e030a0804050a0807080a03180302030307060b03070609060e09100b040b03070f052505070b1216020604030c0b060607020a090b010f020c1c110a 77
    0x10310080303080b40c004590142104031000381c5440b00040c015076842e03410b07100b40d8400043e600000360076180206842c403100540901611404034041c5040132013a1701074001c481c4640050100815246c80001d41d0206882e4402d0041c4040305e01a14241c1c0e02d0981650791880d04540c041000c030040e1010b0000d4105a07200e01404078030820004101410500103401400030000030000c2080440c2e80031807205000c50043e078110026480b0b40191a410b40c0c16604800356040d4001000664900c40d17500541c42030f01c880c0d0381d0f1312400101110407100303881075070208682c0c5400d00b070001d8040302c0b030000d40071001440f0747c048410095a030b0908020b1074200c0c0c01900140b034090010000c4200108130701240b1204e26101410b60b61170241ea01030202c840d42030b4060300c031280700d00001e00030b521036a086621803600142a0321405550303582d032102411495075054001189400c2581c0c2131400000c0c40c8100c1c1d403000b420f81320f19806002010007200e0351051300392801d0b2200145003456458621000c0c1c007601c40c80c2 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 230148471 1250 230147221 230147231
    0xf04080c01061202030f0a3302041e172a1017090c060403060f0b13022113080f0412110102160806011e0f03060207050d0e0a0501030203070507060c080612070803040509090a0b040303 80
    0x340d036620303844220340c4888010400e00d1415182e008021400001540031003900724141a50003842039000035814100c0ec1d00400d22144400e4025000b9400921442d890b000240d215501c444825440d03111081402d0303000441404144001130140d00040b000040400e000503140c80700c08002409042164420281300c1d030300103260480d900e490440031780c414455040e00f03280b034240f000615040c41e44e04400542801800700e180f44d2808054011200246010052030b403c119481c141514200d0300d000f40309016100e005107480111304200f0380c0c00119074000024012580ca070402004094148448061242526482c04104100708002c0540598014240162541d11602c0d0003442c0c210300c00e03078040c284210420804e48030703035a403a074160070f480080c40c1c0941c4903119041d066030980180ca03030040446080583c448c0b0101c0d48800100d1251500725400c1c11040d0603100d0301030b00c52155000b1043c0b0345d0010401408141000c101031500000b2070002c5a001018a480f160030311102900e00b10002a00c0f1 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 230149721 1250 230148471 230148509
    0xc030a0c050a06020f060c0a0909020d150e090d030b240c190c09090303060306050a090b061507060b1c1113020f030f04080c01061202030f0a330204 65
    0x341e01c0b0064003480c0014404100000b003c1c51741c80c031004000e00504080000c408120034450500c400013444085410754650404800100c0a845a4420111205611040058040b6480c21101c0c0241c0514015040b500903140c42140980f8000004030340000c40c003c480d8803003000c1a102486c15045007181c0541302c400900f500c506107000e0b4120340520110400311000803400d110001c44c1102c904260006040c10580740582c090480c50748080c12161030310041087e24252500843c42c600e205800d18850b07a03480408100e4004001010034000f800244442c4000071030503440211400c1d402800302c45002031903800000ca40e01c000c1800c5501200808142515041000548c40c90b000f04000c00d500b0000050004241c0d800020060314401101c940400d09020688080b01c25052072000244120794a80c0e907050500e030f003c100308a0013072181030602038290b84045100e905461b4055810b040031a040c000d41c5e00355007450f0002ca543c1046062042004102510062004009410994180c4d01031 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 230150971 1250 230149721 230149729
    0x7030b031e1c0e01020706032703030f110a1d030102070506090d0f050906180f04020a030b030c091005061c05010905040510060b030a021e0c03130909030e01110c030a0c05 75
    0x8086038660901c0746110f2220b180740c0c1c000ca10390703080c0d8406280016118542052800503001c46140c0500401c244041d000c0a040c0d05821014030f081c40841d040c0080d08990b0302210321445803402d408005072030540707a0124108810281c84c60305034000d00150502c0768689403203040100585419480307500c140e0742c0562942c0c100c4090101d003c01401c015080c802e0050108420744210850843c1d8990750642c1d00055a44207040030b0380c1c21602030800c5490341050b15021300100148080f05110b841041040121880e11060b101d115103110184000224544005d110305034000009042d841a5419140110b18045108150003040824004141c90515051260510480182050032039007070410511442c1840e6003100d8210031006401039803000010360203000c0003408000301034141000984000d0221000003d0840c0c16200c0c204420340c3c83d0350700c0c03502040300d440040041c007240b80d0000040131580503c1d41c01007040e40d0203054a5280910313000080c14000c4410086440c1e1130048070078812420 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 230152221 1250 230150971 230151013
    0x6030b010b09100e0d0204050403030e0f060106030b0a1401050304080d090606050f0d11090712140a0b01020d090902160b0a0905010506031b06070804030804060c2907030b031e 77
    0x101c5070800c80c1c0050138090120b9885c04410390040c2c0101d4580300445d04141c440e40c01442004034034000d83e004884c0c124001507e030032081c4a180c000900346403642c110b600d0014000812202004080082110303034000649581c0c00040081d141c1c401b00303221034610300c80319000c1c050348030384142000030726503042c6000c00c078100f41c1d080c1c910f60040088100d40c200003405c900d00305181100845803844503903600601240d9080d060900c0424540c10840d15508031401c2c400d0607802815030100900c903580c0b0803c01280d0300c1101c9a030800c0042e040c220200310325000c0764010078650040790020004110340d03465480c0110002c0e20020350b4075503164407003800d0090a200340c60700a2001c034040c01020740324495096038100b601c2d181c5840b8050014081007004480b8044500855006502c03913129035803064003410030390a00f841610020a031440001840011032042c0c0001d10b06008200000d03110090202c004185428107507406110790400340c0106040c016400c0300b81e0515800078004104107505110500f0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 230153471 1250 230152221 230152249
    0xf060509060711030709021602120f030d02090d0c06020d0306060e2110050708040b010515030f06191401030e120301031217160f0f0e040f06030b010b09 67
    0x4501400000035980d0380004542d00c00781c000c0d00307481030000f41500007030070b010791030b403100340e00c144006000601403440b84200da100c2802140d800c88080403d1a245413281d41140e1080c1254200300914441031540b039011300340c3c1c50005000189840041d669040101c1425001040941d220000d000089685401060003520051034a0718000389110301050301128450340b0707400e10740030303400c00d801c4541400c000c880d5989102c6c100c103001506142e54040d0001c502039405880f01d403d900008141030401c200350140640001581d60700d1590760b5002803038050000392100d80d020145440b0b20244001181551016000700a44106070809841c001b50840e1600e0210303419580004a81c1040c511841742600d0440340c001020100081010408844091801c5a01410506800d0501066085401e0080c1030728907207460320742400c590040f007618042440154000040d60b640000a12410240c220000507041c09001280c0301e0f03140c0da1540c01c0d0302800d030440c0741500000b1032081c06a02d0800003100040c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 230154721 1250 230153471 230153477
    0xb04060c030b060906090613030c031a04031d01020c0411090a06030b03060606090d080a03050115030e061f0902040e040215040308042c040b072709200a02070f06 71
    0xb510300d0000c034480e402095059481460045242c4513280c9503013080b03c0301040303521401004540ca0340b505661802141c04150b4405505914080b450700c039071110715004680603291004100f006207503048035a441c174103200d070440c0500a1000380b42d84450056103540481000c00985411116050220084041c2c1c0101c080505114580f49180c45c0271501c82c0e0059800d9411594a100500c042484030301921b00003003d82c2000500401c41a50581c449810b80720f0400c42e50f1940b01d640001107080d00e01c03a88058090780c002c6004a500c100d50380410902101040710348404840c1c0d0f074800c40b4200e0b04141c0c45000071141a400700002c42c034020000480d148201d41c10b160a041c1144c445001c2d42c0964018526000034031045400d20440408615400c01100782400700b4a107014904902d0140f8242c1d00040070450100040124042008a0820700001106490041454507101e02c01a10001800c000f91081c81e0a500c88103444e8800103104a1000380c00030242c0524001e82d9074000b42c6150301c41e40030 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 230155971 1250 230154721 230154731
    0x21040506060d02010519020106030f0b0624090d031202040e01031a0405070b0a02031204112b060f150e07020721081c0f0e011109030c0d1e0b04060c03 66
    0x40c0c5c2c1041c29034802d003460142d6004c01d80607100090303006001d2500043c0618000b14180402c1280140000744150010340b03941604141c1a147c06045004d584207002c0103010500c072444560500c0098050100d02900e80044011102d180c0e940032a80180c01504d00342d1303200c40043c018010708200c41240480c00f5240da007a06c0c41c1640300c540d107800c5c4600039840307001800a590000b5601c03c0055940d0f9462011032034100741040c0c0b030314118520b0700d6034585014015850701c007504c0c00c0d02169024440d10502d6a00040310095955000050004543d40e4071800d59603000f01c035454040f59610000390010355007450845c10100e0340680b4050340c80c0c2c002c940b005029559003141d914803a122071074076a0302803172094662001142001d40700042c050480e580601d401b81800078503066411100d000450003000f001810100c0c016030445200d82c0c00c1542e00b40d4041c2c1807200e641d06040701c1422060b406949001e000e1300c0c181c0403940c0b1034510b10000b0b07550200008180310070700c40544100c4414400c81c4c1070401c0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 230157221 1250 230155971 230155973
    0x306050d050d08090a240b0307030803070e011101020f0a0813110d02030a05101d01050c04050108090f0102030f06100c0f0201030c1803080a270b0a0521040506060d 72
    0x30742e40356080c03600010401a9030100d00380101c100441c000c130561000400140010440f41444c000c030342c80c8074a0400320305080d6048020b040c08250743c0b081c0c3c4d410061503441c0d65100841590784100f03c00c180d6040000003a42a51400400c0c405420f080198040096641c0344d51600140283c0e0080c0020344190341e100014000030700b8900c03002c415000c06444980c9802d2060001030b050048000014055005526a04001c00035a600401d8400c0520380031440e48190418040d00b201d02c212402c3d020080208070500c001e41c0203000042d80b0030071880403608002d00221884d170030398006468444014003082c00f809861714120340700988030803680c0741219186c1e00c1c07610380540160041402030305140d0740f158000c034541c3c0b03c2c4400504000d001c0025003203850b80c03450100c025074071040b40c81d0b0000c0d21401c101c12200040303114403242030906c9603010300b101d4201400e080c500d5000722480400e010b41000440c51040044e0301d419444444046d14068515080c02d0082c1000c00041c00f071441003c4d9401050 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 230158471 1250 230157221 230157223
    0x50c03070f0503041d28112a0708120d090c06030506130b010f030b0f0d0f0506010b090a180b180603010507230d0608190302010f15050f01090902190306050d05 70
    0xd591b9030310104d50002c42c0000440800e009110840910440c040c00288034201910004440304100c0c285503415100c4e08444682c0b141c42c1c102602400c0d9890b049440c41801000040c0090408420586000902540030303a8075528a0195984a500442d03100c0d8104041840c10400c10100d04540c2c8800384954480080000c0c481130080d15900c040c903548245005043c1c1300c8810300310f102c841c041d1200c802d0b0310725800d00d4014a00303940c0084405200b50000841e18401174425101501406400a03050900701201001d4030205412080c0e419699180328502c640c1d502c00010348950450301d41c00c8040c0c108801810f0075540010910703428002c2c606540d02c0c8000702b51040464000ca002c8100e91104024a0140003a0400b81e00004881c800c92401c60038801c100340007200c0716442500200540f40300d08030b04005072038080031000d92110912000300442e0800e0304402030350300130524100e44025141d00425080b40c1040b6106d10303220844442811a140d00f51140da400b60a044950201c1144241e8503d = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 230159721 1250 230158471 230158501
    0x70e010f12080d060302030708100b0d1a0a0f051915080304050607060b10110d080f010306020c1c03060801060801050c03160908100207120816050c03070f0503041d 72
    0x1d101c108005580c002a0f80143d0003d009143c1c018155105c2c1030f42c807004181e403025200288014540380500c2a006071411046500025500c40700f04029041d03aa980d0309000707070000f0005241030b030300e410f16412401400d201e900e00ca0014004251001100740d050f07241120040240c985c503a82d0060010300a02c40d000041d1012103074100c030390703903600c0000f4074200d00501a40c2c058141c01078240d4282c412000e421420b0360440c2c5114004480701100b8100044600700801da034a07001002d601030050020500c00e80007031206070440022600b2500c0c0d441d07201640c9180020030440040d036218424401a6003e015a43c0184803000c024010744c20483c10240701440003806811a0500d0052244c0170305000700d000340000c045901c10f9a20100244502102950080c44101da095003031030020680389004156040c0070707c2640c0d52900da00e01100c401a5115842409100121700c414400c2800041040c048021400e200304055500d0350310b4600400c00011500502c41115022401042a4046c0704c10340 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 230160971 1250 230159721 230159723
    0xa1406010f210603020a0305010c1103040e01091812090302040e07230f03070e0a050601090305060a090c082a0102010504053c1501091a010e1c0302070e010f12 70
    0x1c60a040c0b40802810009001580c8000d40020301054004144041035000d440f0b68891074950400c2c21a42c0c4101d50303243d1040703014084090301c41400600c0041a40d900418408119081a50a40e103241c1c40703a40c45c0003082141900002c800b600d062003142454083c48540450040041c580303503040c458512815580c3d00d84080200035100046000d50b0b0fa182c80e1641c0019000e425554155140e400d000240c12084801070406410000810119403062600b0b004a980002c090b10071911882152005040b1320b683c150750701c460140020070b81d076909000601081d260500080c0120705050030f00b1404c0b0000500d03841c15a45041e0420010400126904018801daa4542c1d03808003078903801c180c9102c2c1c43c1441d421980b289104003910781d0400180254a100031041a080c003a070703990301c2143c00c1d25090a615400284e40c0c1c11040c81d1075021f640520000003004145da128418661181c07004240c4844041d00141e01000d410001d0180f1070246a0242600c88200015181172280c0070a4001ca400382c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 230162221 1250 230160971 230161007
    0x203070207120213050c071e02010503040f1110020307020f03010902060405061308010c0e03250b09180708040c0b212d06031e190203150a1406010f 65
    0x410442d80e5100c4030300e000410180c1c0410490906c2d440c25003181c0c21458048a040b01e21258400c403503084001820500d540c1651000d01d5a1b03656654010f550300400c4045800c0401c0c000c00700c2d41903580ca1890035465075030354000c5440324040e00410440c3d4000140d400e002ea40340442800240e1140700440b025140250f9200d5581c0380c2d01d4401c210050764a82c80907405518080d100d03554140d100140d107540c84411000c5890710300d1651480512511070030540c0c041d40c034003824200003030b01c00ca001401c4a0360f8020000948400c134244c011035103a00858803540020994401c000030400d080c042000640802018039003400650701e000080c034028150549450504e800000308040c40500b540380e502130a452a4410105c140400911030503020b81d0110310a0061103003003080303c240498800c4100e2851802040031360b00440403032040f4200c07250300341d03014015001130000b40d0344003104840c005c0e001074000103148122806d080c1041d501c0503040c2410070464070400185031358020004050101050 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 230163471 1250 230162221 230162249
    0x501121704170a150c0804141501030b09010c080403050a08060a0510120e0c060f03100b0c0303150f0d03030507110106060e0901050406060c060207080409020415120203070207 77
    0x30142215030140d5480706030b07540d850304502c0002c01c0d40402d0440340180304003602040c100c0224542d00984940f0031411001944035400180803400c01e8044040942c2800e00303540300b07408200794090008038240c009035940070070402031045a0000344141022100d05140110039810a03a80090861007412004001c0020680108041c3d56403800090001c01004101c041ca46410742005408000e00210140c1041d1501402d1f41480d0804110000f0402000f003900c1d00e00001354031b0b00165031300702400c0351115040c2101e0101d4107044d103200403e80c01e604000107644074900304581800790f00e03060b40300e40d01550805440c000300d510358107142d214503071389800d003c10595612001201c80152074140545150b080150000340c5e1034010350b44403210082900c844c04540c1e29041844141e51140c801c400000d00c2808001022480340e5005d800814480c00e181894550f071040d031401a030700140c100501070b1101e91703500f80300f56400c42681c02101c0d40700003055081d8940300c5400303511107407644500152043e1a07 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 230164721 1250 230163471 230163503
    0x1b020c01020a030c020406050409030c050f010b0a05041e021303060e010614060a030b061606110306061b012003150a08100b04020702060417060c1201140105120903030613050112 78
    0x5031f00850b000d0300000d0801c100703118141c1402081e140c0c0f1003005030b800380030b5032403601078650060003050907941020748210141c40c507007000d0100505410b610701ea000344d64440b0135803403800503000824000b0030716805048c10354154200031089a181204c09c210a03071510700100541780d8092850048c140044420944811001005402400240800301d0740a43e001401460041012012205680c09910108000321548450404c40c0c40151030a59001d28244010300b0440c0c04040b032084400034404c000b180c5072030900140d100000d181c00c144000302001008102503000b5628081e401924129487ca0303a552801318450384418000c0d24981c01c4940715410585943c456404440e040381d4081c20940c1d51710b64035030682c18113240c11007044480e80101404a0b07611080c0109991902d800400707041d44507482c01c3c4890b41c0c0d41101e48011418054240f0240a8020056402c203209001000c06199039141020420503582c101d1188403030002d1800d0010b0040f007001d8039594140541c00b2041c082c1c00840c03 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 230165971 1250 230164721 230164729
    0x909021204110310090311070509090c041d0d03020d0e0307020a031e0b0f06010809030a020303010519031a01050307060f1706060c060106030e060601091d0403050c030c011b020c01020a030c02 84
    0x2a914400281c107081000c0c50040503441f07481c0002401c0d4440985060b65140c40c10080220741c192000ca105a2010040b1384580c54554070030f800c008084400354619200d4411040d052507040100000826400701b5015102c800c64003031440180710404c00b55140000c168001035022a187c080540200319511201c909a0701115080f086240c000c200c0b258146092a500701a80604a80380390015a030707200410010700d400026074016887e941c01a50660303007400140310444d2400c6c005022064a4114004042080032000426034481500320303010b158108002d1601c5c020440d80104208420002c03e00040c641c01000000c40d2811301003401ca654894000041c054021110540954090b00b400020016095801095428025002d80705966212030044d500e11010713111b200481510010a60040c4100e4081c15900c90302c20b013400c604040c41442c845117907030800251900284c1d500c8815800b1035401040c010640c200c14801404021700320f5000079220400e2503801403e00203048464030855031 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 230167221 1250 230165971 230165983
    0x190327021c062403060e07050607200d0809040b03060610032a0210050604110a05030414071518060203041505040b1207030e21090619090609090212041103 68
    0x1410b10642c05606520f108900402d40e40d070f01c0112200303882e04142d0030b040d00c408500b00c006c450008007400d00b0901c0d075440700c04c42c035400e80c0780d0600c150030b0750415020309950b11505502003a004410064881400c2011300088510960754944641c1c040e400f0058503a80c0c407803a001c5114840d24001c0b8044030300002031035800ca614582e00300d60420020000c0c501d2580000d46c1c591150302441c7c14040d41d180c01d003c1c0022100035101040052404010036040c6602a0300255000343c482c010304c0a0b901d0007007880a080409903003001c0800201409900c03c181c2d400407070107024450030b2503031404451515201130f6503441544643c03014450445002c148860041050320001c18182c05c0e21503a46201003266107030400103c1c0d480f80405c5c601400d07841c25401c00540400000d01c801c840c0012454400300707004007900324601c0650300c08020050034030091a182451414144140c80b003280341420814091f080103025002801b001d07206100034400c40200803451900701c0d8005144280c1200c400c40480e040c49 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 230168471 1250 230167221 230167241
    0x110d05010b270112020d350306030d020f2d15060a1502061f03020406080a05060f040f0209060112020c070911181203190327021c06 58
    0xb050354600400d03404404a03200480721a84060281c2603072240c200d0f058010306484040d42040d081c4806c1d000140b10003101c06141d00015803105c0204000712810400d0510301c8548101500c2e0100500507241420015001440d07643d0000d00181091001c002c0d58445006692518000301078800101c4001c40c25081d407840310f691816622404032039103284407004025100c190050284c07030f0000904100b02003281c08119100d501910313544c0c0303a400c092140c8403400d885000e000000510f0000c0140d07102e1082c01e00900c2e0b158042d10325076255040440c10305074018810034035a440102008002140074180c004140d6048403d050a034450310300403074102c2429a202d0001e03a10004010a61300c40015804040b80c00c50f080034410021703800c184031100d01841c801c17440e41094200d060052454007413a1a544044014112400d000200c1440070f8800b100010f04004a1303918448000c800c0240b100c07801d100c01d6540d0800b03090450581c0450302d2031004100e50404503411801741d108105032a08020906 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 230169721 1250 230168471 230168479
    0xb0604090206160b0f01050907170703060906080c100504080604060c0203090a09140901020a0f03050a09020d1a0108070b070209130b010b090102070906060906110c091e06040603110d05010b 83
    0x2280300d4a410030141d40152110624045c60100000e51031410b6000588a4003140e510040329000242d207007104c181024100a0606441d0003003c540082e082c41500000c01d0100028040d403010041400305844086170302e0010014100814010101c000035808d41050344090700103410840c6a40481c01d50083d0080c65070b005209200c0040d41c00c4542d0480c01003051b120301c01d0811611030b02d540500301e00c16020f8883c00b140000030310b00da225000382c0c4842e510030142d03000031480003000e40c00a002d0703004000307081380c4140000400c40c283d4001991500e000d401c40d83c0003001d4080c1040c5040c0154000c1d0f00e0300a105805030000600355074032807020b070b898155001210440d9035865803080c1d00e480e0006010b0b03500511824230b00080080c801c0c00360004449a85e16a03a40c010706140d000c0751021031844510149100c1c1e0412a0600c0d15103881d004e2064245112903c1440400c10034000d480b60040c00d218800c0b424603c0510101d03c55119081d001c0e4030450303a5506507044c0d0b01d4142d0140c1504e5a0b20340d80 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 230170971 1250 230169721 230169757
    0x40506071502030c0d0f1406120a30180510030f0606020c03010e01150b0702010c051c030e03070b07030203060a0305120a0306050a1a0a2106060207120b0604090206 72
    0x92298084060140e0341c400c400c1c01c4c41b42c128030781d45c40310407110b882444c640d540183d040410058108102d068200c00a0b00d0142e403c5194941c69081000e554501d841c0b28400041d10318494044089042c4c0c441c001d07062800d020001c11420403a2440061801554424800c1c0110030340190301079441000c65101c68801030001c41ea0b5807130f0280d103881c2c046c81098065400d288041b03031b4400040c4241c5203c072010300421031889041c070fa100500c2d80c10200081341070142e100c01080c0411420854242c045c0c204104034420046c0410f80242038400c45480f4045603842840708000061074424025445001c5140c0140c503650746400003100d8081c40e130b2002d441170194020b02c0300903840c000c0040804400c2034809002c4103960f0000c2c001a040e940c4a8085051118060840b10661602c020030300441c0320310745100b2040342d119400c400034030060250f400840c0d4801c400c00407141c051103c0c900405000c3c00801448260340c41e1050b842c60014070fa0781c03040e6941d0701442d00715a40c007010741c0c95140b508245109 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 230172221 1250 230170971 230170981
    0x403030f0e10050105090717010b0313020604080d090e010e060915130209040e07080331060c02130605280e040c08060606040b07060c091a070c0510020304050607150203 74
    0x100a003004c0c06240c0c006c6400721b00148201d8050407030900482e20801a40d015a860980004059000030b08102c002e04503002108025a4071140a00040c000b5400500b44425078120b000c1c10a0030945d000720003a07280720004224000e10107003096803000041e01c9103003581d82c48550b01003180188a00e4a980020b5200c1e1070803c80850754040c1810920940d01040b40e0503c1d114103980d24007044c45841d1841e130080101a140078110450080d80e100349002a24224908043c1440d00350105d030406000510444220340035403501d41030705041000c2107802040b0791410080071a110000c20b01c65004c4556010f0170320f228402c0e45442150040c59862600c0080f4105441c16049040c1d0314850540e0b144103ea01284141c40c1c20011102110b1004147d03511704803656139103e0141024080002c140910003900003410030861080c10b542580f20309041743d0303483c20703841c1c1500900056048a0300800104080d1941c2903000030858094039801c4418079151100b81c41d0800070ac0d210740d1103803410f060000c02400 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 230173471 1250 230172221 230172253
    0x40203091e0c0f130b040504060b190609051216060201090210020303010e04060b060c0d020d230706020f0412050c0a12020a14010c060213030c0602070303080403030f0e 74
    0x2507240102007840c01500c0002141440c1d50748152141a6800084605421610b1034004d50082c0d00d00f6040c50041004202c800003d02100c10445041d14110344075955100f06151030031000307000c00750307018005080904016000b090340700940070729070140708006808404c4001c2040540b00802d00343d421034100b1500c0d80c3c0024003070b04c51018201d0040e082140041c0307141c1d0011003564140c401e07101c1c5824166a607510740300b014000242016070002c0b4204440c0c01400300030b01174421051003d40040c801604600c0300100002c41c411002a41c40040c51100f00d19400b00408496110303800030030268403507003914040760b0741d88502e074016450000744c2c600540c10403802090f08500c404044565406540c2d458861a04080c3c215200a5214222400902034903808591800140b1418074108942e641d5994501003244d100101242040c103404004100304900c940b8a54040c24881c0b020b0f082480c40d540d0058400c9602500c01014541c49801f04110b65003190b20610b20f582071441140c41c80200e0741411 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 230174721 1250 230173471 230173483
    0x406060816030b010210052418060f04020d1803080a060302030715050c0d020d020d09080a0303200406090f06020c01140a021519050f060f010c15021c0605090705040603091104020309 80
    0x102101d80d002050544079241ca03140c62003140e2035050340c509c0b00b9075802c020000740303010201e0780592041d801e028010802c0a80c1c45900b0441c0c03404009400205010300700501540c1d00101411249400c1c040b0030b00041e14003003003510850b00460950300d140034684005442c18090882d51529911840010080c2c15500090b200c07801080c5400b5100c2178141400200d40290f100d024021003a0b1101c042030000030f2181c2c0c0700040e40280340c2d541e80326501840e00c1b0701d05140d05c203074002000510001001e121880c0c0c9200c914008200d10300042045030311040018080f1540c40e50040d580b02404a40e421030b05009010880c0340e5507003c0030034100d81c9407000c041c00098811020709041a4500000604080350120780d95001784c0c0000c1ca026440c16016004650003148030724102e8106403408a1241900c03c0350003d8522040240074070b6105a80301140c0d2000ca0340c15900480c810510481880760850300b05045905441c03203490040f620b00228200082c41c0c01040c07100742d4001d4800070402c18400030101d02 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 230175971 1250 230174721 230174761
    0x102090102060a0e030427020a021f05040f020616060c05070606090203070f0c0c0905040b09010518031b1009030215090601030314090f10030203010614030603030d020a020a08070b01050406060816030b01021005 92
    0x5120bc0100f0084861080f185d0440c3e0003803014440607006000740c506170f030180040e0030780c01d00340880c2003c03160317144029102e068402c000072410229549041100310f0040703201030301000804506500d0201e00042c0010b500d05120b00038014030100700f5050184000d000005424112414802801c0601e007692a4400c01c5812000030b520301400b00d046030a00d80e1640358503c2c1c17054011405c05020940e403428441300d1100480240c030440c4c0900e0300381c0506000714003101c4d009401401a00401e0000a860850014544000c40e00400014000650440c00759a81e40500c0001c10391907010040102c2c0305104000d4041c1c0e848041c0100d08548203a04da001181603507081d59a85a50000380195401c42c0d000940351039626400c02d000480d02c200407940030307000d014210710485400e441c60303454880c2158484141900ca01d11140014000c50a15010701030040c0f4880c60610000d180110110003002080507203281010b0f1154100034040e8800c0001d007581e00b40740c0004100c0c1e800c101c03402a40202182c68 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 230177221 1250 230175971 230176003
    0x2250509100b0708120c090a051011061306140f010b0702040207082a0a1a04320601151e180906141f2601080102090102060a0e030427020a02 62
    0x40d600c41050000c0d03810402c8007503c03ca02c523030f084c02d0810028008885c1c0502c1000101d07500e0b040001070411000313005046142c00440d4403569400c0c55030907500c1001110031480e003090103001081915413003250445507425000e50310790115200090103807284c840c02401c040c4001c070b6000c44080b0303c4d0b0313080c80043c10500c0d035824030700c4241e0b0580c9841c0d0003501c1c006008172044107810100b03c1142000c40b40e00c40d1090f0442a45001c00f0980c1460003d422103050400c080500d0a651085600b040b615015000c6507034240781003070740f01c00010400760000000d49000808030a8600400c0d00540d21800003501c4141c80c0c0c0d480540700d06c150b6000307180c54441c3e0310301001c59211030b52486c01c200a241030400100d40b1601d013000c426403003e4901201840e02880140040c0d021400071135509102c1e240605a10000582c4e503c010f040020302d0004094411684d4526002000180000000c100c038100d851190060108440f40c0030080c02511081a1007001c40d400090f907103000c039502040032513500c42038203 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 230178471 1250 230177221 230177257
    0xd050c0d05030a060e1f0e15090901020702061c0b0405040b04021014212d04030c05010207060b041508100e01020903030408030a0f030b03030d02090409050d02070602250509100b0708 80
    0x1d0041c001501030b0746e88140c208d00603c11085170309044c0c00040c2c3c4a4034440000d4540080d80d07001c40d0b46035112031000014402c419502c461801c591f80104180700c0300403682445a41450b85602c00328401c0608024401e40940654050b41d0340141040c0d004002d80c04050380d1030b2015012200c190382292051004504021000038081e4030400b0070902c45003e003214000080070300c44c80020001c0c040078106409224a1110360000110240000d04500e0b1040b0300200b10517801905000030b4480c01e042d0031102c980405001e01140c980012410b03171404150700049410001e5000050080c420708026907054000050003080c212070010052041a1840d503c0f1003884c42c030210308908032448200065450b4104104d4550500701c5500903020550300141300142c00d8556640f01361400c0b0302c100c9420702582106108129260f018410414051342031146001c80c40d501c520740001408032402080d108442c0c11020038207011b80f9080103c094044100459a44d489504042fa03058003e200007596000b000 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 230179721 1250 230178471 230178479
    0x812040501180b06240724020d0b0a06030b010c03030216051006030b070516021e1201051b0a020304120c05030f06060301110f2a0307060e0d050c0d05030a060e1f 71
    0x3e12010f4440007005e50006007481ca065455001804c44170f203c0f29800b16040a14600390b5503184020071948189000001d01d410f1510305001c00413810781d0040c0300341072410086210a98002a00f1400c5e9607261078010b1761780046c04001840d030070403048094414031501110440c0c0c104568082c40a40b070141000d144250703100503040b145d605c2604900303100c090224043d2001400d1211503800b240d040d480d1040381c010001c0c4041f803c44001d40f14540e075969100c0c8140001040d04980414810200d00700151070102c030980301943e40e105522807014010b5010040da414400c00c82d00c804042c1c0401401d0340d241010400c80d643da20102911268400d501e0b040b11820121590f00480710510400c550395420401090074020403c45041d60071840c681c3d00c07840c0c1030b13001e490a00c018604244640790019070812505100d07031520015408520500800b000389003004200040c2001c02a4810316003190750f17564801c0390340064203150b40000180d031442c4050028028005041c900c100c444038001c4803800340d076 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 230180971 1250 230179721 230179759
    0x70303110c0904082d030403030902091006090b07020a170a050706050306090f07030b1306030308060604052407080d06080c0109030803060103181b031e0812040501180b06 75
    0x1d44000701011410043c0002e200104112110740721700c00041c094080c0c40001080f0003942c41210202d000075581c0080c1c41c1185452446150480040000801040e080c6480641254000d00400c441c8520108410f421941d07003500144c0640070aa0b400c036039002c07202c1c19541c0d0710000c0010845d040e000700d14021428904c20003d1b030b4804c0304001e200810036269030001074160800a801c501c200340c0c82e0320b100011521201c0d0003100358160710b080095110300c4d5040003044508064640b5105180420082084d682c0700304038484c64003400b6080c1c01130501502184c070890301c0b982c180203180b03040205205054800d542c0c454002c40d4900307001d4602c1215000b00454401e802800024104542403000c900301d940f090723201820b41d00e002d00414401c50169203444007042c107903003416142c031943e200c42441000002c2081c60b20500f2020f010074005190717543c1d85540750040e0b140261700c4000c50000201402400d40084076580c81100d43c001c4507030102c0c2882e4615240441300280901c803112042d5480040c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 230182221 1250 230180971 230180989
    0x61802041d0f19090209010b030109200a03110d11180402030f070e03070b03010e070318030206010302010c0201030b100c1209080a11030f0609010603030201060f0b030a0b040e070303110c 82
    0x601d8107082c0c105070f40c0c2c441d142c0d155000710903a500800f943c4d490040005896041c907250103051060110340e280d43c13414060100f0781704040146035502040c2200c0c2c2140c0c2200b07805403a059803440c02d000c10b0740c8845965851450090300340b900b14045c184250100251072400c020040c200c0e13890b0310710a0a00445c400e201c00c1e48801d4590001004c0f004000925240c400e084000920900406031202540d81d801000001c0d082078101301c0700d81e81c1580c103003d0700640502c1440c0200268a41c400d1282c04e541e10082c1d11400c051001905102c0d07070386138800442e0702c84d6004070070030300004000b1070a1152000001f012080003000c110b80f032060580f410450a4061303034840045541078002440404001c0c9c0d50240d4410541401a4161061008030206c0c00c0c0f085c0000c80c407400c2210000a44c480c5541002825605e10343c0c0320300c610314481c48041c800e46000702c0440c4c0e400031034903c0101d1403940f02d00204000380004080c1130b4003070040702c00210801d0390261910015055020455407520f00b56020041424 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 230183471 1250 230182221 230182231
    0x4030f02040509030f0a11010c0c021513030c240806061c1b2102040605090f0f040c050901260609040c0e0106210506090c070204061802041d 62
    0x110140229100600d099082990301c41031030010b490501039007000c100d803541c001034400008158011482842004240725010001c10103103081c940d03101003500440d00c1400202140003240b44001642024503050655100c02507620a03020740080f40d82d0040850754840c4814100654040354604412607440340001502511008240c00d01d0501140e041019004110021544c5540c4664000d40c01c1c0082000440c1007c2098031001d001c103040192102e4000410401c0010030f9205101c140082940b141c152074489009403051140041c552000900000078030600b2b503407003400c00c0104015968044058484d001081c0c9800000030b0b015a9481546005003001c0c680c00d202038000220b031860291030b13498103d80250010400986c855000d1034441000b60000c801250041640f034501240f010000d00c94084910400c10260510030000360344008040d04c0114a041701146203402e640d250b03848000208134074040c42c002c9001040c040301c06900b15203d2060741d58103480c2c1d401c18000640d0341e554854 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 230184721 1250 230183471 230183483
    0xa170f0607051b0a0807050106150206160e01050702040c030609060b07080a08250e1c0c050112020c070f090e0a110d08090d030806090615040308031f0605120c0403 72
    0x4000c940c054078900c03c090040c1d154581c8140510403000c0b8840d2001000420700820001c41d00f103007030814803401d03d1642c000003000c540c050801c018520100d81401c040f01d1005140504440000c640100c0f1240035118002e50b00c03c2c075003071150200580550000d000c071074607403105001803079031880c0d00c4440c1e000c1e082000d08608070404c0100c54407032141d1f4246038004110f1b00382c680340041420100e145d9110442610b00407661052004c1460b10b441d00108400da01001ca440c500b142141d901c62400c0c07015407041505000c070362164400030369a2501510801a40102151482503035120b0000b0008000d229940740a49000d410040e400c0d000f0075401c2d4035542000d010700515900302c0a2052400e000f440c191007440c800c0c04021980c0c0e40e501310007148036000f542c404880d0309004040105180024010f14410386c600740315503000590040035501204d80104007035850341e130351100c1041c25036110030040d030f000c4100b640c01160694225010b01004401040c406806503291030f00005c561280d07001c00350007 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 230185971 1250 230184721 230184727
    0x3070b0a0b0d080703050304060f06030837020c13050403050f0d1e090308010f0f05040b0301020417030309010c090501090510170a0227060304030c0c03020a170f060705 74
    0x3002030990000711400d60058544481c00040d034a030b0009581080000301c001071300020900c414040a805003204a0702000d1040051500d5551580d0842c401c0c460031510030080301c400700190b101c00c80e403600501407800c0b211035a95211100000d403180f00b1341c0b41031489101e051020044001d058440d6510856164580d9483c00d5500b102d43c1c543c85d00f02e031a145802c0c0340c59124102c031001c081c01c42e081c0e19200590000c40c801c07005240c0645400b40582044488030001071080080c0c820303035421002290400d80e400600301514002007406441581c101102118040d00001c00c200000001180304a4541008104204030014121a8401188a01c1f40001c0612805100d00d00d032460300102f000d189070071f0500101c01c03480543c0108003030441d038000007154041072004142900751b000150794040540541003116031000000c41c50302024001030f0401034928900010402504620f402464004081e404071559074201644480402c0021407028080c20584c1d644003640020901e0048009444840c1 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 230187221 1250 230185971 230185981
    0x60702060711070302031c08090c060d1509060807180c0801050f0409140705130902060403170409050405030721020a02090a020d0e010e0601060912020d0213020a0f0207060203070b 79
    0x103003500800320b10384074a0043c0480000140d404201c40d103c2c044000700840c001440c442c4024100c01002030840f011b541110b488503419680e00422108a0711212100164041d042032031807061410b95000000400d25202003c5090440000c0c22011110104654900c0f0709840b107000d0140c4001010b01d5011600c410014407007854444860090141c0c0038000203400c50719600c2c0d110341c508590680010b035420814091106003032034000e18940903d03c400c1072120426541c00310780d951140d4030002e81070010010040302d58124600485000307200000c0213100500f0641030090700c0c1e6101c402c0480b04a0125510303000e1501902c1515110052180c014000c4031446c1c2d001d01c103048100424482c04c5941c200000390350032096104a10171005803000003da40d0103134040c41d528000042e004481485581c12040143c1440e24000d891075580c191a620321180381440820001d001c017540400c0303001d0002c01c09132017146c1d0102c401808174000d5402c45054540c0e0720026030322442403850181c845450540099 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 230188471 1250 230187221 230187227
    0x2d04030b04060504021c0f1101051e03040309030f06050f010909020f100908010c0e090106030e0a1b0906030809090c0301060f0518060f03090105010e1303080901150f05040e0607020607 81
    0x1540300d40040c05807115000346140c03500c140300d409031003103d82c10035403602c0728288018251003102c841c8080c01e1062402e03030003119520080110200400902f40000009801c0501c5031011400942c0d211900c8080303011945000740180c50101c6014021a5a0b5800020042c0e0301340115035006d034014011540c40424102401112505090714405000e000340d00010105001d101c0c47d03d8070200c030f5540445c0284d994040050055044c0d00450400d0308100c00060b901c2c1020440d201705580c40b6141e418190f01c2c08004042c110300552100340c40c240707400e0f03000060041120051656880c22078810066030394103c0d150b1a83d000038051000012090440b0204260003600208404c44020502c6012001d400000800c0c591080e07200c03e82244011040c0203004009004e1107026044601c4080004c0c50307c41c140d0422808042c0f0050708100b004800328158031001e504c00121440d90100d40301205841e142d40600c08040c9105440c043e600d0280c040504801c00f048441c019a100e07405020b00da12520310403 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 230189721 1250 230188471 230188481
    0x6070b070327120315060e030c03010b090c1608040f031505070503061c0803040f02030d090b030c0708090306160f141e0415020a0b01080f07060305100b2d04030b0406 73
    0x5201450f6a030320a030000030000d0358a420081002c0e0b60342c0310703041c00c7e8541810300309030521514a00983c1807543c43c0d1841d59416a40c154081c004290745912080c40e41594000d02c414150098691803000601192040a16400740c050301d018440c140303030380480308180b64115842210b07400000380c000c2c80400e1991809030210301c29542c070040c00842103403550f181c00c801c41c1d100b643d0031180245074842040c210b09003071002d401d0500550612a4240745006020443c911004240041001740001c502041101c0b640543d5642640502100d4861525003041d0300c3c0d69401d500a0000700b8541c01f18181128400d070245100303420000c00310b84c00c00c0034420800c0600e000d4050440c1042000f8417010510131011001c46c1120a0541d0042503810014208800310503c103030131101c0d00790801c20b0b5000303024000044100441e00b02d441c000549903961f010b185c0c08522036411040c401500003405071414102c242c80c0449250f00d4151800f111188445001501d22443c070001f40000d0407000041c010803110b03448 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 230190971 1250 230189721 230189753
    0x90f320a08160f0f14040203042102060108011a01020c042304150b0a0803072a060306140f0312070c2105010b04270206040506070b070327 61
    0x180000e561540d0240b4103040c000d80140380785200c0180304101c0c405040c0d2040008100d5032404000443c00c2040c1d0401103034960380c115001e030307070000b020404102c0500c203c074002d000d42036031500b1710401c140d90081d01da01080c0f061424a41c2010b040f1110b0444d48940010610b1058000307004008104c01400081c01c403010307a4401c12081400b01c2c901c40918005031030300c07d5201d103080c46000c8014216450031601200e060b54020380e803e407003c1c000840700000700c8102a40100032000d0b00c02090054420440c484c01c180481104202000038540e40c15410502c15140d23000c81c0b080740005640c044c4035410171054072540c3e0503800002203d03060b10200004014650080c0000c0d42695121a070743c02d10b4001100d1010b01841201c1420f030140708080c8202d01c0110011281802a00319281ca00200b4804200803850305412070740c000030440d61010100e4004060180c2080d4441c0c503103042a1071032143c00c98107407002c04d081200341200745422520a101141c901c0300041039104894480c00591540162 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 230192221 1250 230190971 230190979
    0x20307020a1b1e06090b0906040b13081e0f01051e0702010b100c06050f1014011b08090a0e0709090c051c050601020c010e0d020402030403140307090f32 67
    0x5011031154003c10a804800c40d07024032a03902c503480d200d001814208103034000f80b00d800f41803182100030f589210455086880c0c0503407040c0c8510702c07071820141c10182a030000c2258800c1d03050800000c00c14a00401c14010303508184c600a078420800780d4241c4508980d003d008a45e000180103400446d00342c0c0fa90401c886100000301c0d50001008151548080211507010444050382c03a000c000031401400d503c03111842807400241803211084a44038001d00442d030b40070342018038a0750285d1207843c2c4642034441020401c44441c0143c20010115403000d04514005c10141c0c902040500040d85030b503005071003964401542e03034944600340d001081000001800c00c242009140c40c411710368400c0800c05072a082000455003010800a86455485501241841304031195248582c3d110018207031500d07015580507a582c0e40b540360441d03a4a143d0a03030100001d002000344110b0715440701950054a401e0b01d40b0701c1d10340e07481d0700c442e0800e00b100c104a80e14103041c0d02d52082d41035988001c1c9040011002d0 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 230193471 1250 230192221 230192273
    0x603060c13090c020601050a0803091f0210061e060903050316020d0b340e0405151507020102100b030a060b0f030304080c0f0402090604091e060e0403080a020307020a 73
    0x2410301c40036500b0503100440164170181c0148503510b41051540002e0103010f000b140340c45603a90104465408055113825180700b54074140e20241d00034847d243d415540c0301380400c615071b269603501f80c5120665803082d0009000d450003040312401000d580c0d06882e00310000b1800c0c005034a480305020300c800c80b07080382c00600b400405000a00d4100005000380d070340349c0e540c880000900f46142026003071170282c01900030001c0f600300c0000390005203042401000740c07401f081e10794034030000345103070102d0f0300607a9000b052507070300505010040307005001258402d80c00d44140505040d000c20503644900f0603903034160003401d920f0b00011142e51003252041c00c0584000c0074442268006800c5070041e0380a0a2503401c1030f0000c2500b407900c02030740f00548104441c01c5091400c0c00000c110325004034040d450b8001e59808420220f8041d4241901740348110000520005480d40e034601b500074019135003200482d8140700441c59004e514000d40c1d2041d06187c6c001d041c2d0715155158042c00308008958140c1c014006 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 230194721 1250 230193471 230193479
    0xc0e071b060b15030f0f010f12051912090b0403030e042c0c0f060307021f0f060303030905101b140c01090506041b060f030e150a060f0504050603060c13 67
    0x9a1401c510103076440c203419890f49400314060948017401422007450300d15650040c0048101d0081e410280c405000c030401c018007852400e00d29041d008400d0903101d4100c504407004101d1400004407400717019643d01c1001e02c2da204182c6516000350f00008011035045c5601a00764140b41c1d200781120300e8080d0750384488806500c08208801e40220038502c8a802c5003400501c0f80c10100742000d04003e0a88040d0b1551800c3d0b20000e4035288540b108202c1c0d40340703111401c0440113003500182e4020880c03140400410760740c0d2038054010413500b04d08a071070b030240c000d6140361f020851045920a600c859005071541b122000200c543c002e8050307042404090521038050501000d218402d16140b1400051440b41014141705034000004c4080f000340502c55002404201e45c04075141d546032040d4100450b25201009549040202003003d03885401d00d241c007045680d0a2581000007165420b5101001c4561a074050000351171085800d5601948a08003080e80005070f94020600d510048010120071511 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 230195971 1250 230194721 230194729
    0x30507020402120c0c01180206070b100317072d08130b030406090212060732070501050105090601020c0612060f0603010303050a0816020a020f0102011e0204030c0e071b060b 76
    0x35544d100081e000070802462001d4244501e480c00340921414417040d2170340c0d034001035551044031801490310f440400841c60010041503c440a5030703100070510b140035050000c1468940040034103032405005401129016600704a0002050b20f00312100c00c64650652581413250303001400186020f5049030001828035240c001460180380706020100302c0c4066401001168003080c00070710003035001030040c040125000005001d1803044044d07030410401410034048682c103060205240c40202c001905006c001d410344c4101c1c1a10400c4811006a841d40c0c00120790310000b212486400c00c2e8100b059184482003004484e5018100905944101c0641c10108002e600300381d00032408917001081880d0b561303070042d001c1c0358012400d446160450103406c6009543d54202d00c401390041c81e58125100d030b01c1c0d04c00c0d00700c202040c80c0729014000a4054a02e06002075000788019910031500d400d001ca24034040442960258101c1d9884d00c910501d0f015000c1c08009202c60100c4a00303980c0c0307606034181c1d12 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 230197221 1250 230195971 230196007
    0xc0314040b0d060f0f1703091011010507140403150906020f030907050612010302091305062d0403050901120b04050f06040b030604021302070305130e010314060108060103030507020402 81
    0x640c0006459100b801c1d600b03001e45150350050701810140f00428802e10704182000c2c01155040c503080a0b10030040d840302410352294031802c5400440c0e45541109a40d08118203052013070141008104941c1c03112400c44204500f04c0392080f408908000420205030002c54600c00701c030b1401d000041c007a6280d0f6802040781d000c0d042071a1500408410029410000d010f036000400060b110b0500d80910b01c1d8980c00b4115050100912030b00000c0046009040c960459102c01da51100840300c0c1c84c2024200e01150080d6904143c4140c1811150707000621201400280521b5254941d1818000508015594441020803034001283d40303902495250307a580c050240540c04040308000303207003040e03020b00c0180c801e03c10302c05000341d0040d0103000042c0c80759900b18030522804c8100680341c1038103240c04ca0380d6100d0108201c1d148070700c0c40c2010a920800700f03101c50483e886280100b5400b51001c00780c40c1c8400f0244100030441c0c1101004001080c082c8000740400740c40100014540044039204200c440 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 230198471 1250 230197221 230197229
    0x306080a1a01080c01020c0405040f141b06070b0106110f03210903070308041b09061401020105060a080a0f1a090a14011514060705070902120106090e070c031404 71
    0x403080c621030459035007409064a01402c1e02c1c0000d40140030304c2000207580c40b110302c50424001d55071140000e085c400d9500e05000d0340ca500001002803407032083c45443c0c0e100a2044685c203102e038100206003091034000203c561280e400040006168a041c0c0e050301e030400d4914243c2220f010700b40491112003024801810107940100c1d001808801c60b01c543c1c000864001c2c004800c1da80700300958004640c0001081d5030059114000110400c81304192107014407980d400015603d0034104003045901d8001d4400c40c0d800003e9008203c299a034008100c200451417090070303030304e41064a208011404000c03100000310b0181045d02e01d10b03003d00484c012a440c0444040d41680c20240300d104c2002030041c4508034800c1d0140080c0103510800c0c06042d804085840303429050944d001c81c2941c0ca40300c0b101a1031400d500203050301c0704d441e0780f4440c000285d44002c03140005c0b5550140042800c0307009204041c19105160f003c55095981c1d8041a20350f090590019018000380d05508182c4001c01c000402c003074 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 230199721 1250 230198471 230198483
    0x80304081e0309060415060504020418050c03011203141204110310020309030a080402130612030908070605030103030e010917072405071b150302180901030201120b010306080a 77
    0x520004058008641e01c140d6501805074400c00602000100000e0000c0d0000d401140c841e00440319155903500610583d0b0206400c1b03800810001402040c1d658101800003244200b4000b96451280c1602184002d0003a500f45052500c45034000c02c0c420004040840e184840756880e06103403c6a00c14503080440741100c2d40082550602d0960405204108548a9920081d07045040083c5180d0301d07806035021403000c0120702c00000c0e0a40d51100d0700022000c444210401840380c403000e15229441d0f04c5042030f80480c03121140090a840700082c0a01210300a5440c81c7c02d5900b1a981200c3c0309801118080c104045c000340441c01c40500212143d10f83c424200520903549090316654040d02800d04065102462071118034000360007404407050308c1d9100b100f404500c10444901002d61555401660f2408207481c981c01348503815500410155050b00398510544c2d444404010b001042400002d0004900441d034180590740c640010703451080c14140842c075a42c036014441d05e4985140010741d84 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 230200971 1250 230199721 230199727
    0xa0318060c110c01080604090c0b070303050609010f0311040f020d060609180e0601050d050a050304090203040204140402010e060f0720010e0306100608150301020a020f07140d0b0402010201060308030408 89
    0xe07a54201c809482500050005842004650f03000a042d100c0c000340300034020303030b1550075480402102c51942000350440320b08080c0c5402c07590800800905040b80d10b140124035150000c2059415001154102c940c4140e00c14180500c1c4000d10015040211210140903001e200ca042404c24600510020b0211961080080d40c501095421649414070040f00ca4919040000c4c0a4000208060341900e8060354400c1d0308070a1490042c0c0b600180d110302800600001c2400720399140d59030000e50107540216410b102102d27964444810450040d58000c1c04585040d14144003410103001501170b50900340300c201d0421040c0c1c2c8903200c0c50601881031000c1820f52444003121503822013015058404140c004201c60301d40207100b0080308105004110900c1940400141824041c0546940240c0017400a542303030318003004041d5440d40b00c1d11300c0c1040c50207018000310348020301c24044001c4880c0182019001c6000e51520024154041c200740d045540300d03000480494030040c02103008611414200765 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 230202221 1250 230200971 230200991
    0x60c03050a0b040608120903030c06040f0c441005010e0f0f0a020c03090a06081902030c04050d020a0e07080103120f080a0e0106030c15120207080f0a031806 69
    0x48071440d980040c40f07280307802c070306011a01c0005800100305a00b10300540e0340b407011000007455401490300208092040400700420031142c1840094014840c61210840c1c80d12407034000010135855894100080345003081900c41d00349000442c13010751f0080b0f00007101d14038500341c42d4200f195061300611400d40310030041000c41810381040d54000740400c0d0030b01c1c007800e000c1c80395880c031480a0300148500342c000c60f103da01e0703410a0044900c0e012004042444165803071101500c111400c840c0e541060b800c0c1998599500094004c07680704404441c20300385410b08020030001e070061400c2c01642c1040d02c8030360201d4a201440c08640c040c41c03c0b030f125007800d50b25503d41000c0c0c2040040c0c2d40010010361990a22000d50400b04594101c801c0c00d0001c01c146030380c0c40c0014010a800d0b44058609004420300041c403500100300c0d8040680e9546c0da05401001d110010020f900c6060801801208204000501c141003500a400b1070b100c2d03840e0100360664552080c00314600a441c0035a651603561440070 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 230203471 1250 230202221 230202241
    0x1015170105040e1c0e190303032301121b0807210302070e042907090509090a0201080910020c1b01030c0c0b060105040e090601030501050702031e0a0903060c0305 71
    0x190050408a400f032200a003500e00450301c03a4a070b4030004c43d055010400d04003429000c4e0501043d4084050000d05580c2c201c060b20b014107140502c01a030100e032074800326290a00c00d240d00d819501001d00c200803a030303074078100004506d400c40e640c007940d84c00d0204030320442c40150901c59100506030f0714010441c00d4208a1092a02011051290301b03a2040c1040710000a40200c2c0310805c03a0010104142e0319692801c000e0040148a143c203280000c10103102c20f031185060082c0f40c040c2c116562a801125214020b0240c444815103443c0403030351242c0070203801584203aa00075030140e20501603410560400c00103500b1b0340c1003c4010211900150000b005c45204195018009070b0709181c1031000707403800800a0170b18111500040c1c0f01010038400694945d005204070380091180300d00740c05803890046250f80d22404280011150755081c040407601851000050310040f40200f10340c4810300c4c100286030300d1a507000380d810400340001c8101c0080428014406c1d5542c40385aa100400c2d03901e000441c03c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 230204721 1250 230203471 230203517
    0x103020102120715021c1506090503160306180203160302040c050a0f030908040807060305012c0f06031e060403030e0106080c0904080f03010305030c0c061801081015 73
    0x300ca002c800601c4040f001c540c80400d040d081c1c0c4c5611200681d540344540b000b881b011251406200754030f00b441c070b1054244060240b010200d400c1c560711010815103030010581c07618054000610000080441800442c01a9115400142216850b40142c50082d4080303410003102041001b5003000081c001c10940c00c1901910003620440c7c68000d1420308403240c06090f80020382c840340c00300b55076000440108920201120b000d0302266085071110b9070b0f25030004000c0d00b024003569010590003603207001e03040ba0001b224900c581e403881a009e840d60307601d00e480b4038003640200820360520038480c00c60041c2e001e50340e50100202500c0b0140c000361501e170802806441d84800900c00316803400c0f4007000b0060005c503228003039240c1214540300d00d07111030030400d40b140a1070740095005840000004200540000200f1a10b590704040d101165418010402c2900810b80400d0402c202c1140355010f56104507483c0b0350100a1041d200b001503102c0301c000316204d103481c507403802140791200941c1d80204d01d0001 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 230205971 1250 230204721 230204743
    0x50c1201120605150d110a03080f0a02010f090203121806041401020105180606060d02090a090c021203010303080411030f010e06010512031c051017010906240b0c030f0d050103020102 80
    0x101c0708500c8031000705c1c52a00d0000006403d040c0b4103179143d0303801d80d5402c480800131a00440d10030744070245484428803691140c0e000740e01642c81c00c400c41001000790b0041ca0283c0d03400401802c02c03140a00070100e0154070200c84100213800d1080c0500d942d03503070f40010b00050207070000910912048040060b003101d5000c0c107400246090a040303030005240c0004c075540c0c04203080d60001d44820f86241740c0e602900800802c60b9014001c03505c0480c1d110f58941c805070036a800380e800c41d4102c147d0000980d580e44402c0c00081d00040c00c280014001c20562507191110f808064121140038000c40d6400342101c0e030000720841c654016030010811854040c040e104c0d140129005185030a0084001003a45060617600301c50494070340f0002941504d0821003c0024120b101f04070055640960929000f010030704021550507151040f1924114001501801c00d08a5001590040c0d070a0111155203500322010010607403104009140341c410a20015100d1a0409070010440354118800a8201012070070 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 230207221 1250 230205971 230205991
    0x5010303030e0313090f0905010509030d060e01060c110604030807060911030c031b150c0a0605151806210303040c0e04021c030915110d02160603050c1201120605 71
    0x200380d82c42030b11a402c0d6805c440c0c03082c0d80010195220400300c0050040020060655480c100800111582c0400142a1001300010400003da00c1d641c104241500c00e0203403000095100c2c0102c400a03601e120004001a00149040d040643d05d0340c0d01c0340103034403059003150410b071074162500c100800c1008403040021f049001c5c0c10700030001804070356240c401030b140e03100790342c030519001086441d030406564070040346c00740f21681c403c4c4050800e0340c1c801144104071003052030000000d411070b413081d50a01d1080c400801c00f48030f03030311030300c03084001d040d00035040c030354480c108a441040030307510051040030048400000e0750b187d14050610181d032005030781c0400c02e01c1100c2c90400005035207082420348101c5402c4601d80d0886503500701280c442700c241c2c01c000c0d03002c0c1841e40900e40340303500f00320b02064155041040740d442c03041d450300880e00c82200112120340350845500038030646000e0b420095200c000b2020381410000d60340c080841010f02070344044000074000c1680c1c018403219009540d40083c0c00342d = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 230208471 1250 230207221 230207227
    0x2a080309100e0d060f33060311030705031b04090e0708070e180c041112070c15022b0b03160807031410091b06030e1506011404080105010303030e03 65
    0x100104000c88079000c80240185e9513048261480703e2554002c103150440c0c200c000e00d080008400340f00031801154070000180d90300c4a00011030511900a14240300030314003000d81140c41e03406059030942c1015061406180b500c1c014055401d521001810043c55000801305081c10324030013550a02c01c01b50070101042c0c000c074205100c003030301d45249281c00081524501e201c000203103280e541400b15072810b899010742852500904942404003501604100355008620ba86610794295a4214640f000900120a40705004240c0b10503a000d4402d80507003c40c01d2042d501d8810880d4a00f024459111060550702c00d105ea150381010805014401c481c0c260070140c01d414402c0180d9541103900c0001c100320703107045001d01d04050078404807801d20085070b401d04c0181c025181568411070501b200d120542d428120000f0f03050300c203005040c0c4201c42c0001400f20484000c00d58800000300810319414484c00c60812000100020010401040001c00005542d411840c00505031403041c504008694400c2c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 230209721 1250 230208471 230208497
    0x80403050c1c140301080a14030c06040303090c090c0804020f04062106200409051b031905070c21110604080a030b0f0609090612010f050105090907060c2a08030910 72
    0xb1010036480c0c01c8060910362302d4018005070310b5446400005012030213a1030334081050b802d504001f2425100d41081d200d01510342c440413086a0b003032050780340095420000715016080100c0c5c191136440f0f014001040c180d481e640020301c0c15102011814084510880030014000b1a20170a0400d00c0d66151001d42c8a0115502d81960b0050b0b0103401001980d400120706103080520005a800807102506038682c54001c22040000c0c1d0b6185030098508c1c01c00c400190740318410504c8030070703842e4028600003001d9800321170220501d2116129105010095240030785075a02040100c0c4106e20801c8119525100c2c03080040036075440f90a0940035640d043c519608594814041d50380015055608510a960700303000520645041c010750301c1194038080072010f5141060304418141c0c1c0e42541c5c090040c0c0c0707070155001d955803030a109010001d2800c040c18030020b20030304603070540202003000300400451a02c404a5608040d540b0407007859100186502c1c041c1490900351010507410300b001a904410 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 230210971 1250 230209721 230209723
    0x70303090b0d060909080702031002130b030a060b1309110901140904060314030a090f0305120708070c06032c0705010f030204090f0c170402060a080403050c1c14030108 74
    0x241c041d0041040c0041000410304000742e1240004103141c9505200240c2e06003002c2e082a40f085c4c03000c0c0d00074080e0403000407044050340210340d10b880001d086080d501d403030282e206402d07400c040c05a01e41e07103444d044c1c00110402c11002500910004c04c4c05030107074500e0803000c50f04a40000d0062805040300780f1000d00135a82014240342d0002503140c1c0c041e0b40311540d0002030024030356504010180c070b030440755030034010000001424142c0156195620910780312035a80c80310700c07075610009045078092001758030300c0b81541000d40106881000400d0511080750744d841394902d0103801440000355608850700e1300d001030202103841203d2180300144102c0c14085099151240c60040714180120380501c40d82c031500c2a411940100807000003001402c541c40c035810f000d00703800e41425000030180d0350081078111038250302c580113036401807045203424000c0341c081c0c0701070340018806e0302401400d21800c200e41400303000618400074030110321075400204200c003600071090707180c0ca02c6c1c0305607040c0010720069034 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 230212221 1250 230210971 230210987
    0xb0919060c0204091a01170c090112020f0303040e1303030621060e1e030310060915080411090a0504021306081e07150e130504030c1104061703030f09070303 69
    0x140540340410b1004190a05d911203900300b50000d101d5418040000907030540003002c080310384008109641180c00c40804003c0649e00a003d8a100c100b0400407040043c5030405030702ca05511301a0503a0305207075403220880140d82084850301030030b9020381200300c100341d13240c07084402070407869545001d1009404c4081031000d01030007000384030583d10b203200840342c2d40c10400315035500607030786020301841102500940c80c4d800030382c0c403011080071a940c00b1442a000e00200000d40d041c803041005081e501c100100c0d4100e10140c425220100340804500d410f07111086400d104050305440420303141001e02c14052940300a084c0e1400091400009005066010881c0c001485030580381100403c45940c20b142007008580c0280d000400d80e00c0c04524258001c001e144614200b200c003815000000c01040099810807540200001e50b440f070f140d00003c00562481d0a1414080c0000820a44403000199042c1400566687c140e20210802c00c501e406c64900a40c801c032110090001c15180d5a005040a1 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 230213471 1250 230212221 230212223
    0x5030c190504080a03020715090b22050607060e0606010e0604050108090c030d0c0308070801060e06030a0f021303020a080d09121416060323060d06020705070b0919060c 74
    0x41102103440d068440d809840103040901c1c29034031141418078000c0c0d0380b604184502e840302040980d8003072081e400340005104039403030100407030302d0106c03030b00c0b00402e0b42c00b44901941c4003203a6900002c0380b1500c4610181049612420740010701c01a10200c0515200000b051a810030000c5820034845841d000240c03800c94000707017001182605c1d4500386506040703403010030703a070544119129851020342c0103e8032042c00303000b51682042c070b8540b500200c88840e824000d813030100b03c0d003009800d51410040000c5902030008500010320082001d40141030343e01030501d40540f440b03000e03024002d502d170104031b1a0050041d0b00041261000a10340034000c03802074403c00d1400d0745d900c1082801e00002c0003200e008030011006440e44a0340042d1160021315580c01440e001034503080812080360054080d01e03054581e642c5001c07150340d40e41750400014040c940022502603800f0702c1b11400140c001c0140c003001d05071660800b6142e441300c4043c840041c0412030b002028000c00704082003499004486002e5007 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 230214721 1250 230213471 230213497
    0x15060e010f031103130201120b0a1221021b040b090c0a200d0813050a080d09170a030c05030f0a11191106090a03022d1002091005030c 59
    0x4048910010b800500d40001c0c0100a01000420460140302144682210038400d0320342551259006040000701d60400c000d09820101c81e000500c01112000408003140303219450102d0301034400092142028610b001101c01340e444051100c1540311075200000140005039020044024490001550308030040d20300d51040d1400a9070720702032803060b02c0003514118403451440c941503010100725580d003a42c58000001400c4030700071904030030400c450b079821035401400528007a02075444a08655024a0295103041d5039113144200255540b0f44001c428591019210380341c101300c074009070580f4840300d0b6103400c2100c00c0040102e170301550002990040d003600c000240354100c2400c9400d080c840c4011034840d100f0300d161901c40c41907005440305250480707070341500c4881d1074002d00103a0356580f14500a004d40c200f049401038417241e98040c4983c0929414a06052000c8420360030b00b0400b110006040c00c5400007802d070000e0038407201c00c40b21510f02c7e18045140d03207800b0a0800c0e41d401280c1003031100d = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 230215827 1106 230214721 230214737
    0x9040606090e0a0c0203251101050a02030a0e1309060203060f0312042c07021507080601050313111003060801150506030402090405070e01030b090115060e01 69
    0xc0b102d1035500c05540c0d44840d45a00e000c2c2c600180700c0741c214030050180046c443d8035081001004901d04035201d031021490304205101c04030b51202c245c103000d0104521540b2542c00005c0790290f42641c40c110340e42d43c00107000660401950322100d000b9078200055403050100070390045001d100c1c115500181d1018880c00d00d41c480e03030b00085040704d944050208100c42090312184070034802a4082149030882241c0d5000c00c1040281ea82500580c0310550210740f040e4407030045900902a81019002171038990002843c61000920424a0380301615200003007000d440c406206a200c01041d800c0f01d1568000300400401292103450425130030400702d0741c018441c0d20412016140090100f915540d02d5400f84070b0000b10150084400b840b8020b00094511f2080141d00e01952050071240d84500300f055000b82034a10a41c10030803030b081d1015007005007c0d0050503480300c01c1c10a00341001 = true := by decide +kernel

theorem cover : BRFrame.Cov 230035971 230215827 := by
  have h0 := BRFrame.cov_init 230035971
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230035971 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230035971 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230035971 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230035971 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230035971 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230035971 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230035971 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230035971 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230035971 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230035971 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230035971 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230035971 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230035971 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230035971 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230035971 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230035971 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230035971 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230035971 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230035971 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230035971 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230035971 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230035971 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230035971 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230035971 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230035971 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230035971 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230035971 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230035971 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230035971 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230035971 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230035971 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230035971 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230035971 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230035971 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230035971 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230035971 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230035971 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230035971 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230035971 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230035971 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230035971 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230035971 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230035971 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230035971 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230035971 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230035971 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230035971 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230035971 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230035971 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230035971 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230035971 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230035971 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230035971 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230035971 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230035971 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230035971 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230035971 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230035971 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230035971 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230035971 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230035971 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230035971 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230035971 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230035971 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230035971 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230035971 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230035971 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230035971 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230035971 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230035971 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230035971 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230035971 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230035971 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230035971 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230035971 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230035971 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230035971 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230035971 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230035971 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230035971 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230035971 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230035971 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230035971 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230035971 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230035971 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230035971 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230035971 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230035971 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230035971 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230035971 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230035971 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230035971 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230035971 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230035971 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230035971 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230035971 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230035971 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230035971 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230035971 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230035971 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230035971 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230035971 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230035971 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230035971 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230035971 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230035971 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230035971 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230035971 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230035971 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230035971 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230035971 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230035971 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230035971 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230035971 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230035971 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230035971 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230035971 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230035971 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230035971 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230035971 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230035971 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230035971 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230035971 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230035971 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230035971 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230035971 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230035971 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230035971 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230035971 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230035971 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230035971 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230035971 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230035971 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230035971 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230035971 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230035971 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230035971 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230035971 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230035971 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230035971 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230035971 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230035971 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230035971 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230035971 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 230035971 ≤ n) (h2 : n < 230215827) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
