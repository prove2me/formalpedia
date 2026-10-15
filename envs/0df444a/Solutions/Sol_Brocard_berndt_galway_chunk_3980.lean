-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3980
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:14:09.678451+00:00
-- url     : https://prove2.me/submissions/8ccaba04-2bea-441b-ba52-57cf2ef05013

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 715647482 ≤ n < 715827338 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 715648732 1250 715647482 715647511
    0x50d03020f010c0c0201082a070515010f0321030209120c150a080a1503081605060a0b060d0e0a052e022106011806031d03030606030c030a06030506 65
    0x1480720070300410444075040e14016940480c00d0700020a503410107445400001030001d0080c1d201c0e0714021003001100682c5100640e00c0c40d052800d95583c5458000320412500b41100100c1c0d43c42403001071408580d0400900600040314074440045100d840304d0500c141035080015001680300d81c0d0b020900070360404060028421141b0500490a030270403865945030300d0403c054000c1303e03040250590040d014460005241c00c0d15000c0250b00261508003403d6900089800b40071507141902803103041e0700c0340c0141c0e107107601d44c040c4003001d590380101f03100c2d448107003440341a840381003d038017120103802240101c0c1d9004c00701d500c44c2428810448a00d2883c04040c1d03000c2c16000c04181c04d049210300a411085180042080103000040c54600d54240d800b00f940b07003c14000c1c0c3c4a43c2400c0c1101000544c400e0b403c554070704014000300303c103e6510341d21101c2d41c01c256020780d80200a49102e002d0280c40b9a145683c0d03200171010325800241802c1c156540c0b0b20000c00440c0c02008001d1045031280b003d4507 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 715649982 1250 715648732 715648753
    0x914070504140f090717060d02030334080d0c09050f130204121209061d10260105040b040209031005061507060f050c030907060e040608030c011b020313120c050d0302 73
    0x882c3c6010060541d4008c00c00241e0840050310000111540c004000c8e504001e100e48000d50200c00644580404440000224441007807250740300080c8840b104020b02000036021120050f140e078507591084c6540400510310200c1c4d541004800b00883c480e10340710051900e6143c1c451081c1d480c007800b1003615444c00034014070b0b02c2c4641108030a00a04058248403010600340075111110310321a06500d400b4a40003010060780f24001d80b000715411541c2c2001d1400300c52500c1e603e11410209100340e074411420050040b0040c02e080c4201c41e60742401801510b030031521303080000007600c4d0140c80617400002817140b0780600cad1100406852140e20588002c41e880019034012015540c0181410070070300307000c04c203100700190001240011100e0505014105100c0d80c00090028511540440641d0000046442c68064190b00011481e0440340c0d4803040942c10010403a80ea001302422080c01c0c040810060002c8050805030560042c4142012008952120045840c6422040080300568065031104 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 715651232 1250 715649982 715650017
    0x105010f03050c01080c16030e06120402030715020715091206020d0b040209060901030e030d06030506010e0709030c300510050603190807062003010914070504140f0907 74
    0x14900b070f03091a08030000e00700414000304500c10300404142d11188103911000700750042c02da0200f41078005007019180e002d03040d10842861821074040703200c0c0c002c0d02030105030100c41500440b103103c01c43c1d0080a020741001300589042005c1901d8005210207440c0004100300582c8480c54400c1c4101c4000d40c668004409a40580d07045680f003900c00e600502010500d5203800c0e0a8440d800400d103004598903402164643c118818624528181030030300c1c20100620a002034814100d03141000303403580d60b990f0000100c4068543e400700503d1400301d100301f00903511100310f200080d4800381c030421600c00c0b20603054411180e5411400c40302608041a40d4121000e64450a980302c035003600a44240d52455005c942c1c42400200700900021000c40c8080074800d059001020100d40005409103181207052400e12607003091284903030702410410004048040e08150781c0c05001c0c1d07601c0e018105400d20010a601a819a241a400c01412240606140e0b10790540a01445450315035503052280d901070b0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 715652482 1250 715651232 715651243
    0x20414190614062b0f0207140d0905100504051f120b01020303060105130305060109020403200a05011103070605071e0e03060601111207050d0908060907170304080105010f0305 77
    0x4000c121901542c0d0003401d854507411944050035280414000d030103d00040c9809022843e441c10701c044c504060031040d80003d500429501e0301980011904050210080ea130380d0120307035102c000040300110f081140d400d20101c0606d810040742005070400d80c0ba5800304480c400b11004812184000400180440f500014a12854140a94140101c0000400203540d81c8006801c0c9410448009107000c800d40021040d800550b61040560321a540d4035000b1a002c1d40040c001034440030400712610781118070081010b681e4130805803040700e010f45040c0054071100180d0400210038042040f588000982500c17809110f0380454440d1a0f03107500300c1c110b0124854845510308103008003442d04482c50754000072499486202460300c5203440c144081c0e4140bc2000e1000521a80000490107404102002c9203006134081d80f50340d0014071503501c00c200c40e661032007561200750f03075003000c0d9007400f040c0340c42200c50240c80c1e2400e04481c40c0540d07550309a07003141e000340e00c40500c50100f800c007801040f8040c0217 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 715653732 1250 715652482 715652489
    0x20a120f0806180117100e01021908090606040b0d021c03124d03190606080402010c02010203250b0a05070504060c0c0e040b1605040b0a0c0204141906 66
    0x58400c07007000f18400350440184180036600800781c2d20070284071142001c201c101d807103d40281c001d100c1d0088400351207010f9000045c00381c24030380c5030326843d00c101846040c2807131107521143d006110503100c440c01d00005000781101e081d00461908043c1002d0303203890441d8002c4110000030100300c61440e040003021383c13494409034456a8104074901c0b8031030b0300403031401c103000d4801100821840612101036402c0120781079520314000303c8200005603c04248050751040c0304c403590a400e032000c2480110121551030080c0c038080740301080440d01651041c1d404a0b009803060040f42c2c608006039000700c0004000311210241040494080e004111400074540d8229030344043c24010743c101078030302900074000c1d4016030b13040008100c030140c284114802c03003100074040503000340200d04041c1404100aa82140c41024002502c805202241c0c40f4000301d40031a8050300c40740f81071015000c07007118000480c1c0b00503680a52034212900d9240e03075096803103000e07041c043c0496100c0c6400040c40001c2d10411b60 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 715654982 1250 715653732 715653739
    0xb032b0c0206031518100e13020306071206060f0c0803060a0b041211060c0606010f2609010c0e06090121020a020a03020d1107030201030e2a0a0b030402130c020a120f0806 75
    0x40920a90154640c01d440644000c1500030340302c0c1da68000c0132602d0032302655001c7c1d03141c460201805101504202e4000d020002510184031184d2a1181565000c1c2c1c8a0490000540041c0c05c150100394108007440e0403403002000c42d028182e442c415040e5581080e007210442c1c1242c042c840b400c008040e001814170281c2503034110305000b01240d4040d2a82c01c01481c960500060b41d024204113031040006e0031010b0030154441041412441064640d488122580743c0558a0034508181c2c3d00c1c0100d40741003542800400c11840c040380d1500444203840304078440240740903100c201d00703000b00c01b0b4006070001c0840340d4014440315105003802850240c1540030032040c40201c1d20300340a18440410000140ca8080c00c000c1801c03e07551031001d10745916600c0050800444100a022034490403482106035141184c40b100c1135501c50ba210700b03240c030003aa0f00039809500c4292910181005402c0200307031107110b0042e5114452a500c45c002c810540600d0f8500240021403d501c1a0382c0140520360080e2056 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 715656232 1250 715654982 715655029
    0x312070e0414194b051902120c16020604091a062d12040c050108180322030203100504061802132406080a0b032b0c02060315 55
    0x19484d6a0010307440407803018070716040304500c0401603650b0b0031402d00900700d11040c1480090001c01c0d900101400c0d00c00c040b00c200c061a61382c141c051140203541c03082030250101181502e80c501105242d44c420340c440c003010110a1908000f59031044094001400c01400102d91404a01c00d1504040c0f18600c1e40703803040800703000320070414401d01a9916007410301007400602c280541c106000034010281c2d1040001d614204201c03c018001c400002203036420f881d11141911191241c91810203810a400003640c414809410307040e401d00701c14180d556286c11082107240d01d83e000b090414090042c18601c280d124000e12040050a20550180c800f4181e401500e10001d5030000d80c1041c802c3c03040880d581d499110382601141041140c1c00440360361110f00008990350316000d0001001110000c0c2c0c030b00e107442c04042ca00d08010800602d1080305080e16100e080340041c1440c101d941c040c607a1010000d404104800503203484006600030040d0a05809401d00810b08028800c3c1000a9908200189 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 715657482 1250 715656232 715656251
    0x61518030f0304320604031a0a20070f0605010e090f03070f0615170c03100902090105100302040902041d160813031b06050f07110312070e041419 64
    0x5540241103100650340710359a0984d0341450340c000a4407003c030480e40880d002600004000b640c0020032a880e8000c10b0361203041e521403440b08120355500143d10209411840b80c0c20b25000140000c2000303034450740d04d03542158901d486640031510240c01010840031408140f041d245005c1080052904030b00c4005c6151944640e42c050881049140c000c000d0f03034542d07408041d07603088040040c015100c0180984580d040e1042c445580d0861885094068002d811031400307220507e0003101d02c2c10303030003804c00f40da580d00e00400d000f8014031110070042019801e00c07011034100b00500040004094400150403d00e035904041c036610318015100154131409482c00c004125000020164000e0601c0403030704511071142010345810074180c5014a1030031103940300d02d0403c4650b507c001d004081c440c00213403041d034810200741c405100d10101c42030f00750300c18848106000307861900c055100c0103900c0d09000881c0300d0004070b41a21b600c0d510000f07072924540c0401c8266541140b144000301ca08200c01d0059809 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 715658732 1250 715657482 715657499
    0xb09060f010b0403030f0311090405090106050f0301090203250e010803040906171f180b01080c090f15011b060e0606060a09140301110418060b0a17061518030f0304 72
    0x40150780c4400d07d230b15020720741144c561880a6421290000d4001d2225240501c081e600801b0786000d080e100e89400000c1000c68241446045203032940070300244891700440850203402032081c460500301206145002c5104002c42407214000c000c07080045440f00e0411461800b56012a00316041c1f080c072030b682c0c03000c0d82d40340012a0350b0714080b42030030703e0204141d030822400a0680803030000d10342c00c04142c0754000c01034110300c1c0a04860342c0c4401d945643c49432004200c081c12040d07075203005100ca210045500a01c0300b40b40700300360300414184003100070640c103988401ca1138030b110306940341c0f90b8440d103c85040b1810702a4503803028080f901146412491040900f110886028030b04509007100701c12411a1030951100710702c0070000210944031740e55501c5040e102c0500c00b0300c2d00741e641e0170050b000480443c0c12003030718500a4140c40d0003504800040b00100e401d00e000b4521503011030441c0d000c02c9111090340c000d10038103100d41ca10300541020310701890300d070480d0002244990ba008010400100c0c0 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 715659982 1250 715658732 715658747
    0x206060f120c210d051b0105040206120a090b1e311b2403050103020a05060307090302040e0a0606050a05090c0c12161218060c0f0b09060f010b040303 66
    0x7080f01e03000c401e410b40074558007010007800030840d468440c1d01102c0001c25007050240015601004c524803001031110522404d076001980d000390080411f10072141c1600791408102d43c0030520300070025148005441380e82c0c00701016509040d00e2400c0104540d01240341c5032116500891840994581411452550703604500c07000c00020340140c18800307002000305030310a2690300b082c40c0001184183e00c0b805840c800c03042401510f2211000041c524401a000e8002e640c1200c2e0000c2c000300c070640ca847c050100700d510050000042051191b80071005079502d2041420108c1e0120042c00c40440390301e825011154660000792003520140340030003c40da130b03080d600c585c8203082c0081d90fa207402120700c000e443d1100700c20b803035205da50300841c5a02a603103000b94254211400781c1403200350401d1540040d80c1c2414030110340020350300700c80002e100741c1b4040c03052050a20700c0313480c86c1c2c40d440c9215103030903940b00c0d005e5400440c13a4005605120b444150704900f1409001102c2e600c5103000d02c1d6607030203000310 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 715661232 1250 715659982 715660003
    0x60c1b321309052a19050d0f240b030c0108090c0105250b0412050c12030910090804080c1005180a0e0f0907090c08150d020a03030206060f12 62
    0xc1d455414a07802c000081c000d440c0c190310000910405052102d401440c00c2d030304c280c01103004441ca8400b1260005001c0711140460304054002c1c070075080a516011421121500260b44030301d001c0d14520380a040000480d068805204070000b154940b650816082460b6020102d041280768401c1c028046e102007000040132a0034285669500003c0e104c04011926030f401002c0c00c0019420020280001500c4c2948030314820301d07a41950b10b100c100156290f0061407040c0d04150310a00100c08070203441c0e0029a0406407000468030f00c4003528944000755068070301c007118110400b080c2080741090030045160800000c407400e041130307d0f5004009140b805030100312000046030010f205403c2e19121160f0000c1e0440d403100c12843d02e00151384840c0160240d4041d04c191040740b4000914500314801c0004e505682d5645290306d4542c84d03486100d8a19828080e41d004c124072216100607a1080001c1d40198441d4002d029140b038a2030030450809c201c00e1009014003050540c80d11098408240300294 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 715662482 1250 715661232 715661269
    0x1808070b0d060b04080102220819050304051c050d0201050c12071e02010b03061501050418020c07030b07030b01050f03040602160501020414030f0a030207060c1b32 72
    0x11041e440e04060080e1210b540556000f41c00007802144d030043c190002e1802415030f82c01104440b0650b0200b42240c0c8040c4990207464008441a9000b8121500d02030005070240d000c0b642020346881c00655681c945512a44c0d0006012030460100070b0248035002c015a4140020001c51811208050321031250702d0f0035411619084001078032071030242c040c103404081405000102c00541310400303402803010305205840780c0700b50400200081250488141c0380d10042c0d407510301301031030134081150310380252241c54051074080c40f102d01803480410102c402140034444004060500000c00307411501c01181141c104030042216555603410001141d810540c000001a51403408000fa501c0d110b080d074034010410f5000040000c0c42012a0250002456045050b58030510000025607521030521130001c0240e04828070807c83c0078004c8008812542c000c42031910600b0700d08409000380917454100003151000318880b44540904881c480584980b01c040c0720800030360802c0050041d00c03010713409006 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 715663732 1250 715662482 715662487
    0x6060607030f020109050d12140c0d271b0609050d1e1a07030e011a0f0a0f0b13060302071a0703020904020c060f1614030604110c010b011808070b 64
    0x402d8030035440394424580220079a40710081400c030042c02d6054000c1c805c04a01d00782035000740b100a02510b104c1c041d591924043d071400c990382200c480641002c6030321141f0843d240714070000d841a80f852446d1514800c01c40e00c402c0b208000428450003000f03820407000c201300b51800303203c1501d441c0c4c140c0707074490b0708100e40c0c10b17001500c40e080d4441a90740013801030010074048008a00038104004950107800e00351018001030f83c54461007802c82d84180045d6140b0921500e0724821410302194048000398060013810380b07035465103641c03100046598051080c501002540c502040510007406d0042c2c4403601e402d6291129030b40380ca20540d0401800c03441100d28600125500740c0c001e50450718800f0014006640300d500c0c40c02d046031144412a84001c85400700000030781030045550502c00600072589904886440c0c0140080540c0c00080a0b25005075545010481c400f10a07405031114002c0c41001080c492001d400040c0140c045189640b41c001a0a4040c00403030404601c41c0180d8010659003034 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 715664982 1250 715663732 715663757
    0x41e0e01080d18050418050f0c0a05042019090b03040f06110d14090d0c050d08062b15050705160206070204020a0504060e03190318030615060206090606060703 70
    0x58448120b61302240e40545007603c62903401c1404000c00c61107a008009403a00c14070300060352911415250030403580540ea81105000034507003644003503103560f034942c580c05050f032940c0d48000071548035200b02c51815082c025a40c401c150310000000140524521450450804c1d80c0c031001c0c0c0020100d00109120b403100c00e88840348900409a562214000d2010301c00d10000c480d00c903143d1641a1103040e000d00a91041081450061001c0411130383e20a000b01250012544104d491310000303009941d05c0440804100c10307404040d00500c40290000081c002820410718024030409943c1c1c045c265101e0400c400c0100e85600b1405a4400380b44014450814144034800030310148034001000394094070109030781103103e038094007a20544611740c41b81030507001c2020802d40d664082c580705020b40c0980c00034410010344281c02a0542c01810414a580c0c03540743e42d5410300395041c0d03042c07c40800c0d68403d002c11045504200c083d421000b6000a03248504200e000b2505c3c0c6e110700e69025052161801d60f00 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 715666232 1250 715664982 715665017
    0x50705010504150507020f0616060f0218100207091515030e1b031e07050a08070506190e030f0f121603050309070b0a03050103060f1b180308041e0e01080d 68
    0x504001c030000c010780d0759103829243d6509c00742240c0da000d43c0c01d58a814898118088240700301c400440b24030079030b120b0380412481080900362a5110000c04c500820b0300c0040c1c01e2505001e000d50080300c0d1130b0001083e0341008040841c596048102c10105420500c18a0070182e0102c0c0e20700340b40660141d03240c0800200400b0a00d00040c051b0006a1449107000c1554030220100f40e043c1070b14000c840d01038003181d8407130b8010341d10144c601030036078004001c11a200c051106480300d00d4221009041455905282000283c10305000c0c807852003090b0804103504c800c0308000e00c042414011690806824552041d40c0c011581c0c41038100101071120010106103089001c1214100500d01e03580300a94940c40602c1c020080d0030280300407a0f00710b092200041003442e85000d401b4000311180c4101c090700c140030408948260300780c4068044001c0c8188040045103138040140b000d89110060242030000f91761b410410207407544d00122000c022600140007000c40491080c1c5130305104e1520008003110326070603 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 715667482 1250 715666232 715666249
    0xd03080f0a0905160528061d03030c010f0b0d050c0405060d0813060215090309130f0e060402090129030a02190807140406020705060c0a0c0b0705070501050415050702 73
    0x10344613210380c0041525000c50303041000d0039150f0603503000c6802088450000500c40002e90061100815000e00b40b00c8030703100350214500b040d0340c3d081e0400402201030100342541e019003c030b074420b03944070704010804801d5030040301012541590760100c1e601c1c6d05d03100c86441c0c1c110742c500144210b4640010074816030f5404681054550000c11155a52081c2802c04070108480d110f420054005e4881c0d07013484845007031101d0b1290300b0b90400385280c14580401c002c00344e89a120111440b9646018100007101603119001072030030804000e2015040034010005503590580c0550307205202d02c5020040c140052000c0c060101c5d81c80303261600c81d02c035580380a0281c05186414104110340f09241d080007075201919a020360700c00c0d200c1062a540c648030060440c8290b00829001d42c1c4120030030405810150b0040024a41500c10365000c4403840ea680d1646c4a050383c4800a00000845c07201d051140900c66600105402d084c820301e02468040c010070344d24401200c0b1001e0003c00719542c000d54071740008 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 715668732 1250 715667482 715667501
    0x20604030305160e040b13020316090b131202120714030c120d051c050f180a02010801150c05070b04061407110402070203030702100203180a030f0609210309110d03080f0a 75
    0x954070303480d0294410f0385092b00303446030a00180d5246000a4020012400c035260340042c442c1d1603002c1c509040311006000c00c103c42c1241c01901c0860410500c22040c080040501241c3e281108050312000c1007500c3d1081e101c00440c450901d18406060007c1c0004d0302845409407410b0003503c45030381c00c80b0f0b03103510509100403110a03428070041140000b410f4003014802d607083c41d0300c003035213030080c101582d51400e514000030301160300c1000600044121440800c2500c6c2c0614081e8840c0800b0707918641800544d5002203c80ca10105081c000c458000100882c1103080041c42820001d00381c4910010200026200e80a40c0e40051b0380d0b002d5440901c12200600e401806c1d410200c40c030008001e42c0c0ea80040240c10f1a0181680486001d29005000750b0450f07800c618009600b0103162070380001001d0400c0f01700e4010003910040c00c2c03421030b00c0e6213042a0003001d880008410556080c5100d04003040b0403010b1144c155044010006030b00588400d03000741950380c40341c4040c1d490600c0d00380100a0682c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 715669982 1250 715668732 715668769
    0xd0810080a0305041d1e0a020f070f030f0f05090f130e0714040902010c120c020d0b0103030305010e0606180102030f0412020a09020a021903030605060a020604030305160e040b 77
    0x1c0007428550810000c0c411210300c0c01c55400d01410070011011204010fa80c1c3e901165540c01c101c090903c400c600103030f045200e1400042c41c00508a1140c00c041d80401012190526946800000d150b0860702e00e80c4408900c1c20510f002c44201300d8018000c4c03003458620303446540d600000b2201a210350304401e0f155a91104204400c00300103e076195103040c0303403007132107560704e034500e5003c041d400c003401407151039981038542d40d11584881d074440d407403920010700c1c200411035a034044001507981e4400c522030140c0120780c1004c181d4158103009055500503042568000d500a05008554841d40211207800e49806c042100b4441c4800040b410740c4600881b00001041c04034012230316071210034440c0041442100c20356000c0d80d0b180c00c24810b9016031001000503030000108034035910742850381030040c81d20914000610907181c42c0000e04d150001c841d502c5c01a80400c00704810150540300e405d8100d03801e4440110b00012854009007840042c4490b94081c0d1748170300c40c3d5652900c800c1c650380480328041 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 715671232 1250 715669982 715669993
    0x61802060a0e09010512030904052a0415020601030b060f130e07090f090f021c1505090d0206090601120c05060c1612030503010b0f09030610060e060405030d081008 72
    0x244402061002c8403050140f0940528000049918100101c60005000325000d1800c2124400c1004003c1400804100000c01361200e550414030f07445954051349907000c00715586640c24a84160207506136507400005540c0440018070200b00c40c84a1a036006104441c05941d50b07007810080791000701461420900c1c0c908041601c1e42d01d06020800100f515000c00c1704110210400018805440b4801e9010b4040c890180503000942812009100700c01a001040d2007501c03580c2e030f614124481502000c0030010741c0c40c014070072510810701c02c1048484007480100000d05020f010142c51b8003061003a902ca038034400c80f01a04115203010b025005180080a00d5165100c1c400b056450314a00c10005441004c1041c020601d40303883c0b1090003840350141d44d140e00316824000c005400e5484042e0717000b070740c50301800500c10300c2d41e00300a1240701c0c14100310071380012850150301a0481044040f458860385040c80280803644001400d44081c00c1c55140940d030a0312110b20b0303990101850f400401c3c0c18000e0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 715672482 1250 715671232 715671247
    0x6010c05100515031c05030903120411120a020f04020a020c090408040509071d0d08161b0b0f0306040f150f060e01050408030a0305100f0305070e06010809070306180206 74
    0x75480144100039003008121624a440d040507103e40000807503c0e1001c1c09400d041d004244541b0195510500ca90300302d0f0b06d8540c60b00b0382c0f40c07501c0500316030071111404003071940d650030b05165000c0659025104010a10100b00d54002000141c000781c1c15409150702007035a4184d94805c10900e8845070b00500001c0740c90030b090030042d550344d1180c040c0c0341c002d01010002c11341a902c21a4905000c04000c01c401490400791401c11820784501b80080e40c2540e424000e80000c540341607950940c0520981d0145143c10b9194111420140c4c4c035840031169038400d02031444a8418081220b500490844c3c0024009040840c100001c144241280031440829480455058401c46103102610300c40e81310f522030302504800440703140c400c03801503165a4200f4410105120f00942105401103001130380000115181c64014005400741d41c0159410b5000110402950702c101c82c0c1107800480030b2134158114039000541c43c0c0d4440f590b1000034100d61342c801080c05014000d040100c007107a8003d00059075180d4 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 715673732 1250 715672482 715672513
    0x403050d0e07140a0e0f040303060f140102070509060d080c3405030703031220030a150509070c0f1a13060b010c0c18020d09060c02071a03040b06010c05 67
    0x40c14001d811000f10000d00000281c41c11403003240440d6000c2c0350b0341c2080d0b5600c0c80d0744a29610301034001c40c145515048042105011255140082d1440e0302d02001c1c40c483c0103000a03d0100d541d40301a018103030712810b02c03540780c4940c05074200e92900f29807241e94890308280580d02d41004515140294414605036030400003041000c903203039204406203080c0503501c1d5002c0544070030381c138440240420a29031554400c10060b4100c0030101800c40204119040340d081d440040e540f086038030015140c0c0c1c40500443c0103508801d00c1000d06010b607844042840e0805024021000c50800030703103c5a05030000d10104500d0856400100714840b44074250303800d1080c06001040c07840039040342c6450810000007181c3d4403494181105540003500c13a190685080703404000c1071001c6c03110181040d0204924a85d035000d6000c2d41042c80d00c286400a03050144010007400d003c1c03d60031903107186040040410842c40174000396904550044524109620ba031750060301c414100b408010000e00543d000382e0300542 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 715674982 1250 715673732 715673743
    0x220c12090c0e0a0e0303041103010902040e0f01150503032d0d0504020907020d0e01050318030c0303010e1f030618020d060b0a080f06012c0412091502150403050d0e 72
    0x460100c100802500d0342000f4106071022401039580c5980207000050115060300e1071558802030103000002d50740400c0d0041003e035003400c008102558020644100400024402c0c0e4980301661886010712600307101c0083d0f26842515190080e00c04281805412842e04100c00501c10000303181103603803421880110005030408542c2a441245010001540c450012400006d81189603582045020480005582d650406498010311042400000210304000c000801a8450441c019510703589010003401018000a03c030b108108074044802e5070952215070b510341a6a400f110220305a0429540f61500580b81c000195001e1210701c0840203204d2254012409590159240d401640d15484c4032aa01c90003a1090b00319a0302039001040dc00511601100c020a003d045030703070080d480021600108001920207403000e646c24501c840c00203402c0380e55903005017600c5600c842050300101029454001400300c81030f200c1c4094001604243c032482c108c074802c441e050030410032644040305443d900d0 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 715676232 1250 715674982 715674989
    0x309111003060e090a290f0c131d07020c1809030910050901120203100e09030f03100e1003020a09051b0d0212010b030609012d090e0c220c12090c 64
    0x1815001c0c88003080c194110814a4689850080c012447c0c6511a80c1403115a000740740c0c040104060040c0664251030714040d000510000c45c0d03501308180b02009589946d81c2c06401d0800b95880703001c401d1059181e00b0303c6c241c00704128808e0f031001580d03041a15400c40c0320300c800096000c6003044c482030f4000e400401510b505c06003070b0f80b00203c4000802d1040200c3c8000c0c0c0300000034030908401003000041410115902801c440f065901f8015401045030b41138100f51b4660070300400d052802c0c4010001014640c2c2e100355411841000035195401090b0803090704d01030200355544a4000500d04c900b030713083c0c000f850070008094a41d60a565050b20009420441c48001071800c0080001810900751068130700070040140f03890956403034507070322403c0006103030302e400d13491480011802007080c8484840ba00501e600500070903000d484000c85421710005040315485004031103851b5419001c540c00d402100701c40014005581c0b0310703807071054a108010150408055040885420401c010781e40c092045 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 715677482 1250 715676232 715676243
    0x3050d0c020f10020702040608191a04021005071b1e08060105060901030c090b0408010902090603011a15040e09150717060f040e03280309111003060e090a 68
    0x8900d242481207032540c402101e42075190f4010381511010300c00d41d900500c45035100a0001030050b03901c203040c9050140c0014580c1280501c940b0000c18814680325032225030802c0b60741d10825141660010f80010110800c04040100c085242000c004c0451340012441020041454800303594809040f030b8105403451025180b04d06100008080e100083d00605031000240303200c1c10718000400440082010b070500e0000c001d5103482c00070f04151448010405084032000100c1e03800702a005100050700d02501e11030280c2e00d01181406031642442608a040300200e400b07020b811710384612911240601d82206418000c24814080451000515420000d52890442c0e92a55400740c050301c94a04100302c01e4004c2003040c00290b01494200001d5807641e000030700c0020121246843c003442c5800100000425103045c00c0706050420241004a0700c17141580b8040c002d11060740da58000034032402c00498011443c030340041e610a8002d400100141420b02c050002c10701e0580002569285904d60039500b = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 715678732 1250 715677482 715677491
    0x40e0604021002070303021e0c0a080a17040e0f100518040b09070e0f06030a080d0c0228020f120105071706060307140a0c05030f25021c060f0903050d 66
    0x201c460020130007104603601a00a0441c0101c10100ca903031010703d402d0041520b004500400889503909401d410140004200034175011002c0d28000c030071900c034816801e082400500040042c0140c0c2d1403100c1d403019a040c0900b18980710f0089164103250940c2010f64400c01b0429004080c0901c50781da60f1285000360301e0305c0e5041c4c4403a01c3e1b15468802034021000702c900d030600000d04200585810035041500603003140d4000e90741d40c0b0380c004190003030220854616120b80b010802a98104001081c821004400084846c1c0211a47c1001c000040000340075180446140c0c0007640c03803c10340040e4251840017489a80307010440200601d40c4003004144c00e07400360000c502541005c409503031040d030751764581b002805200101002603411540c141004c0040c1e20a06400140050018120000070340e8901e5441e42c41000c80e0b03240b410301e14103840020204000541001d03968510071a80c4205914403c511030540c503003800e2020380401c15000880700c2c2000c8910b0201984134004000b50405105d0410 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 715679982 1250 715678732 715678759
    0xf0f021c02030c1206041e0b0106050703030b09010612090201021f0b01080c03091e25140102120d0b15030f010302090f06010c02370306060e04080a0815040e060402 72
    0x304c11050000c000c42d16034001d400140002c0d000c070540301461042817460b04402c03081c0d80c5d0303584140c2d107090700702c440045d2021410008054260084450070071048a41207a00c0d81410401092100340c41203203030160f81c61b41050402d5900a20411000300b0000060b0940340002e405a1009090400540da00158a08002031204082c88094074051045d60015140840c109141c0e8020341b0020081d4044501a802c03824456044080c110280c1c507003203940d90030300180b5103802d010f0140c08008a0b030303055401c00d013503a00c131a1002e201100c140d2084c0302800076a50041e8404122413044010121204140020a0000203243d01044504a07482110704089540d62283d00d580343e00340903196280455000494000186844103041100b0056401490b0006100c0c0801c1540800d0154881800139401441401481010300034040544804020351a080c10030b40c1d5045c000c1d103d0a444202003003c040081100b0329a0840d500c1103041005005202103c07000c0400380d22080180c1d0304a00c40c1508480c0139 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 715681232 1250 715679982 715679989
    0x1103030c0405120a0f41070b09060d0c091802090406060e100309080d090b06030f01060b0a08070504090e0d030e01061404090f021011070b12040f0f021c02030c 70
    0x1504907585c0003004400d102c80c1da6550074000d0718940b503400000c0f052509140744511180342c0b082190b602031805074551458103103425091040c00d410110141a041168041c02e03118001102e04045a21000203402034041c1022144806150043c41001403000c501000080380764000d02500a001c071000c1000039507489042d519510113707141a000b541800e01c05030f54502039444456500c0c0178580c15403620300c0c101003000031502d29500848442e4030402c140104c5040400488a80750200750080100c1401c140181c1c1c01030040380d41907410010030000040c40c59100d6030a071002000011000e110120b040ea0b074090300c07003440f100c001000a103010710b003c815105c1409000100d03086070110028203411f2200703000c05041803e50a0f201c2c04107511400006031a502c00c0951001c1c016560400c040c5090741c00c0a05000a0380c1c01002010414400d41c100780045021240e04070382c1c01050210034030103a20302000c40f00017401020754481040d000d40702c451031721014114540c51088040c1d8120042c0c2e602017 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 715682482 1250 715681232 715681243
    0x7030b0d150903180801060806010503030708071b05030d05040603150605030606130512010605011d010e0f040e010c081005041814030c010e0c101d010305071103030c040512 76
    0x98100c01075a1442450308445034024000c0030700900d40880240940e420341c02449010b58450b83c91690345d20740c100b10b5248140450360140804402940c5400c0352926400071901509602a10154003030828105640c813841c0d9a800500001d000d9400300008514003600d103820900c02c00380401d0400c00c0e010a0310158a404070103491241c1c8840b41940c07030382814482e00b80c100d01c03016564103060b81c00210f00c603929002c03030b2400e041c801c0001042c85401c10000419001203204804001d0f0455071150010f0703a04140780803001d0030280c610b10a10300e110750004016003070705140384074154a0700540d01d81050740301e01e18911901075040390078501580c507010f00c01140d056000c041a8901200300c0c900c002206d0190088240840b00126810083d49840c040c2c00c446d816050740034240e111a400120f1400c10040690031403a0074101941c1100c000c8440000441c11001984e042554580004040c98000c90490360180e440300c0c1241d4807880e080d1040c1616500c580103041c81800840782505450600144 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 715683732 1250 715682482 715682509
    0x204150e01020a15020d0e030901090519030f06020910320301140402090621010e04020105031f09110717130605070309050418060c05041d060d020a080607030b 70
    0x822480300207440d085101c4d0040034080580f66000c014029a2040750300490290721820005140d540014500241c0031034540e030b0041d030103403850407112902240404c1e011800c507504660445414001440e107013000f0702c60b415055602001003010324462075400862001404488111949440c1c0040d958400c140303140740c602014100108010b01c4500c450040070340c517200d00504003604215900b000211150811075460310500c58802141103502040c190a41c010050095400d019045c1a00024030034403005041c0034603604118600d12042d205c86070184002c01159404102c0c44048845020a5600116064518482404101081425601c1240c8004000c0544072140354030b8a4420740e110340050341e080e030501c0040c10340040c55484a001f5110545030045500c4880c42072460b00030100c8018561440402406000c14409031b01c14185c0410411080d0b50b032442c442d030b9401d0000304201682003000f500942800300c0003d26450001c0c149018000319201840004071880c20700413a44125803 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 715684982 1250 715683732 715683737
    0x9060902041410091a030a0b09190201050306100c12030b0111030a0e270c04030201180812070816030503160c030c0204020a110f0705120102030f0103020609180a0204150e01 76
    0x1504001134400303a03101810941d45140308401740d520302400241001c4025409a850b22511020019400024082c80410341200111820700030542d40009003680401003880d40541c103002c1852503558054080345442984c840c1e242500100810802005000ca441c0c5550203d4400840c060280741d000c410f84450000e655240c02255a290042080c14040041440c6090072980408019403072424481e6200302041028541c0d1680365200041c5200c400c00701c00701c101c60b201a000d11092401144200f442c002121546403200e1003801d04504910803c250aa06c071241c0c10003040c101900800075501c200d119901801c0c010014500907198450cc8800090005105082170b50040c40c141d800f1b010002c1442c034014104040b0314210030b203071045c014901c17a21030340128030400c150701c2c2c5103144000301d16601c00250f0031801c3c414120800f200b01808001d10840000c02d80d00d80c00e8442c00b40c0c21180c1800c010300600c05003072060b43c083c0250700c039004484054200080c4d04018138003424000f00d00d100180d = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 715686232 1250 715684982 715685011
    0xd05040e06090402010c0c0801320708070905180103210c0627050c1201060506160807022206050a031a0603010e030d0e0c03010c050f07020112090609020414 69
    0x1078200714440c030000f44100e05112014640300040f504140d035040181c88580000220000c900d44c44010f1030340180d048000581c45010717002004a0342800c22a013252140c01c0c520709c1502c40b00025a00540150010750300000800031304030428100c0004181280d0080105031a900d8013107545907226105603150303c0c0030502054090000410b550720101030412074000d900a241c04040b141c16818255030401c0d285039114054048951604e444004203200f000300c001c020321131500b80829114050050340c1241071040c20100d030305005502088449c1c0603402882e0400088004514500d05e040c407420341240d00d0328001000c00d00d81401c46a1006894100d403c00c000100803060514035120300600103a0107540b84e550440400c070040016100d1004070075008110a0010b0030041d203002690380c0c840380709030b041117101c0c00d4203500001119040003840c10131a907102420b000517148030306e070600d034040e00924000c04042031241707030b901c10000c55108039000e00000c007514180c012800001e481c001680c0546 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 715687482 1250 715686232 715686241
    0x11107030c08091302071104022b09061107060b0103110919051f0215010f0b0307020708031b060f101e0305010c0c031719020c190309080d05040e 64
    0x1c100c0c0c092224800c1e54440e1822140e0404a001d2140d112641081e040c1c01003091400c0101555401040420a450440c00c00c1255040d100e1402c50b0034400340c0340d841c2c0308042045040c000f900540282c1c2d07046042800f0345e4110303603614a01a44102c07002c1e500a0f02c0c2c200800300642c880c0c0a2200501000520700e8102554542000702160300c840c014180000300400016040e11240d035180f20b07403040401d0300c4e2602d40d0904800303420448020411104941000014030102030304c8610301d8159412820107584035514410117900d0040b154004141c50b1001090480d001c41d41c0700745100300842d26200341c4a80303032504100302d106134005440240e010414240702788070418804c050b56454858400b03100c0d0289560b80c40341421540c1601c01000010014102c0350300b40340d00003080781c001407854601c1c0340c000c0c6040318621550030400e0001c50310309030b00040c04d410b80301030411807082044c10802c81211841114600a00014518881c17140c29000c2e906c052400345005209440498840c10400502c03543e5 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 715688732 1250 715687482 715687487
    0x20f150106031d06070e0a1a04031e14071502010c080622090b0a0501121106070c1806150203070503160f0b04050c03060a0203060d02040c021218090901110703 70
    0x100c05100740c14180c46242001c203d9941044424003440c2c0d9030701c1d0036610b51000300606c442c021254100f50b8401c404807115021051a1300c085804507034224880c44007002d0a04840e8031424000480504105c100c9402032546160208103201110304112454260301000042a401d8401c03544902c00440c0100b0001100d80c1003038240301d80008040c0540451101e494040c0ea01129200c0300103644801c40c810402003035008034483d042c050700907a402d0000000c4940d40f200c40f0a05c40c505403c0c0075000124565003004101d40820000d0181401071a00c44068001010f0041c1350f248154004080c00ca0940c2c00f609001004445a0680103c00345161110407030049810410102c0704440c40c000400051021880c0f46100d1400346125038041d065140000c0d00309480c0c0500035050f12986403042040c8070240d50782d60603001030b0550658010400c4100600180e06013054400c031140c1450002522241e0305410718046800118200c81c162082d84030180f202c0e0803201c80f40c60341f0803040000c000040104e170 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 715689982 1250 715688732 715688741
    0xa0b040311010c030b18060d0807060207060e030d0614010903170f0f0d0605060a09030f11220e0706081b0f0403080d1823010e0703050706020f15010603 67
    0x60190406010703026166401500315003c00280304006551040c0420304d41c074108030303000e2000d41001c103d200c46040c50000506220081d00d00101601c0d40050013004003ca00e4050b81c0c01c03150003820030000100346121080c1c40b0351005039001d035824a00003012509504081c1d83e80721503001a9030760300107103003135940744141c80454a0508004042c280105c407507140e10100101b42000580700c00c1500d40020307030310780c105840c42c941245104140921401e44116802007000d0100ea420002c641c0d4400c04504000050040210a00d80c101c480c04620a44c0200854281e10680301c501000304081442c050950b5101c24160043d040021104000306600d0012820034213408000d50842a1174140015212081644654130465413001c012071482180400c03449425042026107141c84031000d80d950741d00c19540003001c20622080310040c5007503100030096003c03001000d405421030700416103030704040c0c0d0307520514400c0200600c10b28002030941c840104d42c0440c18203034072400c02c100741d00f003400c1a03001d40b = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 715691232 1250 715689982 715689991
    0x140604051c0c0b090307141209130b1305091509061f0b270f030c01030f0617070e0903120403080618070914010c0515040206040b0f0a030b010807020a0b 67
    0xc00b0406410100d44105400390095015000a40da94040d03031600360005035048070074981e241c11007265000a581c2c50812201a1001103800c160340004124040700140320881346c113608800c0b01d00078103540d4802688041d0161a01030304440360f50311304a9403204c082e10b084841e83b041350800c0001c0360054122803440810901030b1582c82c00059141d2000d1b00d56034008850341c400c07180e10140035401d17031010700a04441400b4207032009400e0059980100c2d585a40c0a04294105959210000c03d090040c0d404100900071400e000c1d851480c43c0000140e41d03040300d00445034504070901c04034007010350010842d140001c0041143c42281c0d1141c50984030414028031880d0000d4452941407a01810f03060024400c00c015100c120341c503070504440c0400c004050300c8040c1482050700c10100801c4c00001c00c8590301b480c3c1000d20380c0541e128400f04c2e405004590040024005c0426200d00c441500d0380680313400d1040f55001c0003c411100d0045628910035a9030a000d80c0020341c403800415040301e0080d520 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 715692482 1250 715691232 715691237
    0xb04080703110301021e0a08162f070308070b0114010815060f0a023007110409022e0e1c020409080a09140a0608310b0103140604051c 59
    0x4004180c14400d100135603100188184020000c0c0c07c400b41303508106095045142c06040304030b07860682c0c0001e00344492201c40c401b81a80407034446440750400c00040c51140c1c1c0b43c5019103aa1a645e85071035003498015440803205800351400209018400110703c03441e01405030345003207543e150002c0034801c4090010307000da0446410030085503001c0340b0400800a500d4140c0c01407000e461580c3d4480070030040000354110141380014040103421030282910039258002103214000f02000000800410740c01c9070081d0401c42c030428100c3e4900740324040142012121107010f001e04242e5030115011011045101e0b8031845082c55031142d8582d07000340000c0355101a100041840e641d8a9481042d00940140c1c00011801d4409221100304d2911034560a481621440c01141c04c1c02c00107000044000c0c01d066200c0d070300c0c0c18001d540010101030142c01e220181d030700d05455082410316408241c0c00b4001603c00d0413181c4098a03281c5000141584100d8004e8050302c0482e8000e0110051700d990000702c2001c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 715693732 1250 715692482 715692487
    0x60a0219200106260a11040b0a05150a08010f29090a030b100905060604030303051b0703050d05090307030906140903060c1207050c15040804090203070c0303060b0408070311030102 79
    0x35800003d1007018040d00b80302681c21941c0d65811426010800718070032142c915007149080400065100b041c0c0c0640050846003c1000d400383c0d000300324048065403203075900450444100e40214a6030f4014641140c0640c0d03030842e1a07880768001c92452056120b1100ca500420115124589075181c402c06c817107130600e441515103001400014090f480b150010b84034501c0c005c0c03e015080990700000001080001010b22180c504071b800107405001b14400902890746401c0041e055040762004060444164a40d00303845603018100200070f60042c840600d14036182c88042640b0304000400e40304400c3c1e049d61124145801d09401302c036507426040c3c011031000c90501419011b80e5051000c20311a40d2080710039038031841c0307840884812120140152052141c1040f4098000d5030110303000d9400407049820180310346403460141380c544559030184100d903201000f44070310706030b00a092460040c02a68107102554035101e404400b0700c00ca20807040c00d40d01a9000b0400124400c41090801000400050 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 715694982 1250 715693732 715693787
    0xa090c0b0c070501030b1c0807080c0a050c040b0616060c02010b040216050120180609090901140c031611010f0e10061505031801270203060a0219 64
    0x1500c0c0d03082072030742049a030010b0005000075641441104c01c0d0301d43c1103408207010042030b0101c80707800d06644400b4195a40c0083c1500074010202c040b01c0c0c003203903c041101c020421718140303191100d104201880c403d078204003403541a0300d4010242d03012600400d00105c80e080b1156686e400900c4c0700c40e01c0030199506e44450b4407503580e40b0f1010b4509568000c02448008101d407524a007101d87d10128004183d1603021002d100540d08402ea9030b0003141c1850b9241e014141d0030010310280100340d541c076404020a01000b04030700040d04000c83c600742152044090740c5440c0e0401c00345010465102100014403014442020b2240d0146103548044900000c1c6c0c0c80c00324080801941e520001210b41580142c00340c7c04201134610844000f40741c01d001d04030380301c024448018100c1c803000c0e0440c03681c45450b800080500c0402e52011003400c10841040040c44901941044c040700c100000780d1003401400c1c0010000d80580c02201c40c00b42c00c0d007071300b403409005000080d030756a0a03540e141d00c0203469103103c21 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 715696232 1250 715694982 715694999
    0x10503150d0b0c0703020c0402040f1802040306020d0614010c0213091106031503070f050105070b041a0106020c1815060304050a0c06020a020f011106060436060608060705030a090c 79
    0x140c01084040056a41d130343d02420b0291800701c0c240d05041c00340c2c2c8100010170042c40c2603806c0a080c0d580c4007950759081c1125a032900060f0040e6080036041c1c920004a400041031194070100440381c1501c40c06030b00c001000010346a0b4440c100c400380d000344441002c000612005d43c403071081d80384145269101c0c049540042031075900f00b1a00c040400303003c1d464500c0c0302c4c039040000c0401801200005d4002c0c0e401c24000130403034052960000c003111010030101c1c0400070f000c0c0075294500c00c81c1d10312011135a075400f402955550602d400c03038014081500340c4031201003042c010520a03e01340b081c071001d00b07007508180081ca80c0014002c2e95a40103800d04240054000d02c0c06c8401085268000d0880d00e180e4010801100c0c405411607050080124500c6041c09001c9143c95009070115070002c1c0700d103001e1000060402e5050302410601c45804a428410720110001c3d01c055402468100501c80d110a00c007662038409807681740200b5402d1000640104a50700030040c00e41c411080429610350322101e0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 715697482 1250 715696232 715696253
    0x1b03050307060b0306160918060b070c03060605191214030d0b0102150403120f0209030a030203071e170310050a0b031803190c052d010507020c010503150d 68
    0xc885841d2511505072240c50300304074103500001506c2c0003403c8980c1007403000d884030416210f55502100d00e602c1070442c0201640c054001014940035640e907a08a0307140c2141452118002101da403450541c0106142c10b200407103101c501071400000c4685801c010700303604a212507400c1150042c2711007040110650040c40608003900b4800c0020607001f00383d9001a04104440300c480103102000c03010000420b41c05640c034010304a05480c00036a40c200c2ca2401d5019105440340300b0341502c00c41c410b80701003560010003005014001c0941503c004034945080007280d100e042d02403c2c2c1c1441c44001c00da80d42d154001150802c5d00c001e80641c1c280d94030702c0411030314580d07a031180411103804420000d005055002c98140d00d03140c0006103280c00040caa0810400780c03000c85101c01c11201c80e0081d0708000c810401000c81c5149010341c80c40d1b41902c2c0a4800b010300785010700200c1c0707500302001310b0b403442d00000d65250480700507190399085560341007c4c542200c0c4d0312040315901521940761070002c100c4000a = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 715698732 1250 715697482 715697497
    0x7080705180a0317071203020306010527030d022503050309190302090c0a0e0306010509072601270501080d03051e0f340c03051905090a060810031b030503 68
    0x100c0d079160172040c20625044040051130f1824180100304202260382d100d021510480d591048503000c40704e8031100703444008961000b0b660076100e1994208115a0001044c1030800884064140068080c03a429020030b0340034400140b6603401032103146020728080c03090034242d0f810310400850899403900014110502a41c1036103400c134000415040003640404201c8009005600030000355141c2000f18420b00e00040424042140481128007490010100f184090941300d0025041d56102d020300b080e645042508910002642440c04100d2b03081402242e04031512840a0b200e4190810700603805840010080311151866a82c110001410350105501581a072100c41000d40b62020f24142c030b00e9007d407540d8800c1c10311a410300d00320400107070780c0241084840c500700c0074200c01d42ca000d44103401820682580d0042000c6040241c580c0300c00070f4615003c08840313403400595120415142403100f03480401e00003856039014070102e0b004144141d1800705071003200184e25500e441e1242160003042 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 715699982 1250 715698732 715698773
    0x180501060b0301060e0105190503060d0b0130110411190c02190302060d0e01020c0706020309100512060f011110021324110717031207080705180a03 65
    0x113001c8250312443c1c05100580a0800c0c610b403042d040b01c15a020944030b0010303c20060b0000000342e0b0350f140c6e0386840c0310084d400305a061080d40c4602c0c0ca900241100c0c0c4000d00c010b90801c4807828683c240c14503140d80f6540000102c150541041d0600001d07110320f000402112408000480c015400b504140044101c00d6031010824030300c03441000b160507426441b692071010304880c10b00159992400b120b45003404003178000352103d4210401c80c06070282c0a420f003403601640e140050b82a4000c001841600380464801005d0706442c40241d6203402812084551540c0380000124607040420354410504070506100c5803019072201480d01d0b0803000c0d0340000503540c010078a10318501417601c000c00501403440040b90208586180464405800d1180705d0401614090b860107003482440000c1c0503000510380d103501c00803003114583d906c1d8091480d003246a0b503074030001b0300340521640744d0750b0103448140d903141d21b0520109a25011400c03010f42956026801c000c00000148070041d8a10070342c000d11 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 715701232 1250 715699982 715699987
    0x90e0307080433050a0c0c030206041805060603040309060f020f07150e040e0a02090a02040923131203020a02160f0e0c07021c0f12020c03071208030109180501060b 72
    0x103c0305030001c01a40d01408010354880390301e0040b00390000b0580701c12070554079100c1440c20b82801c089a980c0714652000c1d400c61070000e000320b031031000950f040343e554138802003c6c401921020144140c80c8000c6174003500040c041c541c184100ea124180c04051b50546104460302c010304402c0322030134042c3c4c0c2e602143c40401104a00000980c00c50380015400c44121010404038128417032084d10741d092031000030b10a440e00c1001411002c5554140c4020b0b1000301020400f81d406039403150b00d400040ca540012a0a106002030b6070360305240d01c01c00322182e000660b1a00c26002c0b0200b0f4002c1d4120aa0101c01d44c064020600700040c50400b083e401051007203865240c00c0e28200e0003012018000d08058031610b41000041c0150311014090711155160b41d0fa0701180d41d585091910030722034082070007454274221905058030706500242481070a0130407000d40e82d61950b41c0c84a10042000001c00905603070081c401005000d4030340c2d00040a074003d0341c10180b2a43d8030703603481500312001900445580c4a02 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 715702482 1250 715701232 715701269
    0x12010c110c030f06060f0d06090f0c0e06030727090809120f03090607020409080304060f0c0306050d080a02070e01060f1e1b0203030f0f091315090e03070804 69
    0x1008000707030084064010302950815009110b03101c2d800100ba081c005c07084609501000d841d11070507051401e800200070025003d1514110940519118090b500c24131095000f055413802442010302030f840003801814600d00e014181e01001e40f40300d00c04c81c583c6254403049602940b00b03018600038544a050940ea0361750005041090001d4502880981d50f484030100200320f075000811181068012145151590202c0c8006005002200c100415442d4007000b44030070400345811840001170704a00620900800385011001c0324070078840d040c0e1124940c400c2c400403070034040007001000303e14415540c0c8551100c9600c13413902020381c408030014102c0002c0000242d80103032040c0407181d051000c0d044041030798000030424400c0d000580d04d00e503008030701d01085540800c1100c0c00c0240081c14103499481031a04d03000603030410003526000782241c04002d18031410900c2001586400380d040140c5c014242100403005100108940d804c034403080016101042148002e0002090f5005211558290f03 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 715703732 1250 715702482 715702517
    0x6160303200f04080f1603030e13060e0a3c02070206070f030f091526010807170a0209040f050307020d060902042f0a09150908070e130b0612010c 64
    0x1e65540c85c40507401c0007101060f15903c0603200b108481d014139105011880040001e56151004940b0940b101e18240700040d8240303074540e02c00d204080ca00c4c8200300c2c4c5445902581640d00000f011659a40e80c2036022640c1a40d41549a1840030b442031401410611a80c0c046001c551001105036000c95158503040105540840480382c90419031421120b0b903860403d01a00d540d8085185d8028419840e1290824034040d04040e0360090407403040d0010342d42d5540e00c3d9038072150103005005c801071010007441c0c4440d6000a8680c80941d02030300140351544d4030344a07400412050744040301c040c0800c10017407002d0b1740c60b5146001d8490181b03a002502c80414410802119640041c01004003080300c04903480540d0200324030780241440305190707030b180707010641103071803002982044402c103818015500819501c407441d1000d0312010000c45040e42d4480e103941e54444412503504107582041103440000a200480c0780b504040043d000740c0c90300040069607030a45060100c120005109450400140341 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 715704982 1250 715703732 715703743
    0x90a021c1404060f0e06070e011412070e1c150e010e0d081003050a23070b090d0201091d0405120a1209030e0603010b0a090506160303200f0408 63
    0x1400c59810014210411200079190030010400380c2010b568039141000f01e070784c0703420002402c03e02c02d003510400e1500311000b5106030000c010303c600203989000002045d00ca07030b408850510904640c0a585655200411104000c0f0403010301c0d0459821034604070038104c807050200c0e001f0b00c1642c0560225100140b40b408440c0d00703421001d516810086044c60507500030178104014800d502e8280d089a9502c2c0320b402e00450300f640010b15900c6048810340601945004003400407111100c14103948041049547d40c81d07046020301480c24070104860b0f40b440c41d0100d14180e8080c418141000d03a02c0d503e8400c10360301c0030034040d018807281d41c003010007041000522407a81e200c0c1c600200a820002003c1005101e140300c10362207000e0a60310028401414051030310078088400040846950b50303144c40c09000c8a40260044002203410300e42d002c209490904103035207248d01401141c12480305107440490141041d541402c200002c21501900300c60210001001e001148041c03060fa0745140050142c80c22 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 715706232 1250 715704982 715705027
    0xc020171040b0a06120609050c0f0109230d050a02010909020a090b070c09050c07030806030a0b160306081002090915030624040507082a1b0309090a02 66
    0x401103182456000c018000c1041d0070a40200380011295100306484008003900c3c0c1000003043d10042e00a0208081e40e000402012311035404e913808022400d09002e91160f0405050b40420f000c0c410a000440302070f01c2e9081c88400a103074807100340e40c4a202290380351841041c04d841c2c0e034020b801202d040d5604a401a401000a800118900104230740000d206040d1806a80c441d08400155603060100c1200d808010f8501c0c92020080c0381002840c9040640c4008012000f28a0780000203080d03240103d130106d11260042e001211554a00a1101c0080507880040003895554400170600000801110004100f0741c1c3e0011380d5039800f0420054081002004c2e413a151810b08000381d500d4034040740c2c8981280004965510b031010441d8140c07580000d651501e03070402c3c0b03040e0800100c1640a0b92903809845a280850320003401e00505a40601100e024061441c6041004018444481c01c00c0c074601c03031a402c00c0c2ca00300f64444000400310300090361581d203882c1d00401e4202e00c0d241c0e160507040c0c90 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 715707482 1250 715706232 715706417
    0x82a070b0f06090c0708090a0905060306010b070506131a190b0306041a270a1101030e0d0e01110303101419030201030203060a050d0303060e070c0201 66
    0x807882c0c4900003030500c05005181c0c01c4c05070804902e0701c0801030708070160b0b170b0550030051a0711900d60700c8492000090108031161882841003000010302b14185608940300b02d0f030881d02421403a55a06035084400c403c9020480f100c0c3e061154069003010301c1e0b075019001c2c40c0d0902d40e0a0440490000762001d0f500c849005902ca038010b041407000140699214000001042030201c49596508520004030b100310030040f07402c010300c078044885013900440c00030a9144900c5000494a036044011012a046001201800d51200c0f0018120784c0c0a02440d2400382d42c145400241e4940d010344680c25034205a03100d20808611600511080007031140341d01050f501640c0400c0442c0312091641d059004c14440030b4141075001011480755218410408041d040103031a200c1e1000716440c000300203010510134690000c0c544008548420700c80c02c07000346000d030140e440b58642528400c803405511860304089414101d11011a0990103541e040c00800346507020340711281407180d1f1220b40400c6040d1040c4c044 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 715708732 1250 715707482 715707511
    0x7080a0b0102160302150c120901180b09040b060d021c0c0e011707090f03050606090a021305120c0a15090e1611010e03040f0501091205070501082a070b 67
    0xb4108850030f0444112901118800305490088030b1780c10261244100d820030318060303c503500c03281c6600c0400501c1c1040302aa035503e0368051200c81481c02c114035000d00d081d0303154200109103091400f5042044000401409036160148088003c5e0403039120308000800102c900340a800c04903030521a407580c1c0b400c54180321804d2262a40000c040714060540108040480008a00135501c40c80d864409045140f05001d5100d4803030030303e981c0c2c0c0e51044032000d01c5980c0d01400264450600d0007610388041003811215180b6060004101125000c4854008107204082d11000140e80d100210b030b00500005801c8010720f4000c0c1300c000c0c20007500d80c0040e5203042181060029030409012825007011b00340c036122031400e05080825000d814a40da100b9854440030802045d5200c944c15410304a030001d80750721000f1a500d00e82031422034541d0001402c02c1e045031004100c0c0394002d00440780d0091642d8900c100d400d40d03644250810030010311251851a0011070f00c0f07010414400350076500041d03098202075 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 715709982 1250 715708732 715708753
    0x3060b0a0e150313081e0a1e0e03120a020a0602070b0405100908030610051b0106060f02011e0203040f061104060e0103092d06020c03070618110d0212030307080a0b0102 74
    0x81c215414000014810680055206035061b00900084440d40820b500c5582e91403815000030206044e000c20050160003845000b29039500903c203445c2035500c0a0040d0114511251543e0181e800410f02e5006500851600100103281440200f01c010711600038103245e0706040c00c00c54a40039000c2136102c600c034500b428140c040341600c03068030303442442180c101000848920341203a060040c0300e4008040203085148503003245064000b502611000d6407102d145800100080703099842d449070b10b80950400ca0300c00c0034402043d4004640c002e001d801d00400d04e0400c1e075030384011034461140e6890001303001b1a0612005501c00010412030809117000d115620380c688683e40141d00d559200807605602c484201895413460405880c11900800115112400710b00345070f0326540300500450f0510b18005d004541c0e044540d440c1c00384c964112503001c1e14880b0090921102c1103200d981a1b900500b070010b600310307080302000103501c103100a030380e111020b0814494542c2680c0398a174086065410030394040 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 715711232 1250 715709982 715710001
    0x70e150c0c2704060207080a0c290408161e02040b0a082a0d140c0a06021506040f0c03140907080a0204021c0c0206101d0a020a03060b0a0e1503 63
    0x11a90854002c60854464440e850070000911450740024032829010030140741564000b80902070150054611900383c84030401c00d140043c0300c0c1e0003241e602d40d03071220100300403810280c0034102c00303440621100d81c001d58640311050b504541a80d010506002400108210708160044002e446e000395000c050035414102a141c0b42c07040311800442c00801c00861000c5d000030710000300c01c514401707460b14035500c0c0f1300c0c00d1040a42070460203c01051043c6400381c1241c3c01e0a0307100d4800c41d00320b98050300c41100d4a6001d02d59045002e8242544262a0940400a02c100380f0954a07615015240083d1012030141d8450390184010f101010b81c2d000b01208108003130000c500200074560490300140d071684014000c40401c103082c0d014045040c904407103070f800740d40c0000e00140142542c840200312540c1d81c00c403000800711601d043c4c0800c054110b011500c4601c0d107070081e062146840c01c01180d40d68032641a0409a00040c0280001440d90050450319003020311403121017001104806180d80340c143da12 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 715712482 1250 715711232 715711279
    0xa1515031401051302070516080d02010516020d0c080403150c0807031509150803030a090201080901152c16030b0d0804030f0f1505060a0e041a070e150c0c 68
    0x121309555030005448420801c00740600d031002a204a8210b20780c03500e0382d0300b0550346c1559041c4c850140d032030403000c01e4007441c0d40480d0b1500300ba0f5550080228108802d01216850007000c4101c408010612000c00010460100e200c035403080d0140015801c055818010080e00780504203a080c117240004480d4240c80544511042d581c01030b501296540c40c540d03460031284d803980d01040c51401b0100900100e140c0e990001d00c5070724000da8628060f515003000c0b00b42200ca40d45031700654a101854100101c2500001d0203601035070851105d9120040d804000100712012a2000c1036410300724080480250544035600c0d098205450300303002d40b07640369141d030340e50720580c000038007070050703503801d140811800c103100c80b2145038420340c005254881c3c025910040c0109907606442003000220100c0c00ca898080000d2045800c2403041682600714006d407113640314090040c00802440c401141c0040d16000700641011500d030040503034504100300186c3c02d14851400303440c07103031244a030400360b000e10b6802d5 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 715713732 1250 715712482 715712509
    0x1805010c05060c031f1701140c0414061611120312011e050312070b0a0b130b010908010603050c1f090b0c010b0901120605010603020c1002030a151503140105 69
    0x180d030790300e4603040e464100d000c40c1c2c04041c080c0c2c01ca00721000704070000d10079415002d020040009008c081d9058424100744442102c0d130400016040c84204000c0040c0350103809609806041203280c400c81c149400401e0160050644156410401c4075100e410071028a1203541c42c48000341d1b08003507080c03580101c00304062084a583d5800f031b1510a2054244049140080100904440348007030403c00e03c01d00741d003114409440e00b100120000700d00c0d4649008603454400010b208074044407244652400400c11101c0d03082c10480c8141000c52003440900c54403020310300490007001b117448003400704901e1207040f25249908404c07a070800103c041d04009141d06a03071210340540d4560207084400380c010408191080d600207590000014031a5145014600c2280100c1c0e00380690f070780302c20b415401c0c1e1045111041040c1e00030100503118030340b2640519049040a040896071890151014003d0205604220b6010b02246610848141c16110307410013840e00c1180314145614000000d00246001c45 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 715714982 1250 715713732 715713751
    0x6030c02100902150c1615140a0e100e13061422060e040201030e12090103020912060103031e0e01020d080a0b130f0c02070b0403021215071805010c0506 67
    0x207901808565071a04071501d010301240c031813034445c51110340c2c60340c0c1d507208401c0015040385204030104e444640600d0060703500c44e4645030040c2e0351540003000102c2d6845405404200041e03640280803541d00c4940400e0000c046650b4503804694000401c030030400300c2040c009890f450004104003944505178162180041182c0d0707054881c1c489600c6051921080e04403104071850310b140450106855109940980c0c002c0e61b04000703141d181c240302c0740e940c8856483c19200101c2841171004641c4240c00800c4101c5002d0005001240ba00640a1401c030007a0012800b04240058103001200c41c80142c43c02d06015140c42903484083d00c0011351954001c1425508114150000a0004031607400441511001030010b8104680442e103a000600000811050301410103036940210791000030040700351240c480a8500e014595400c201e00c5060794074071a05036003d250310490a2803c502c01c4a4410001c91b11510307441342c003c070b610300340007000e1b0340000e414800c00c50003003008950300280d640e60228021 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 715716232 1250 715714982 715714991
    0x604051e060c010501230402030403080a0b060409020f0711030303040803010e0a02071b0e010b0427150b0403120305010b070303150b07051005010e220606030b0a0506090106030c0210 80
    0x1003000c01d01e030303105a482418007582010b00019000c520740c1710304481c000c4004034019240104c030007048164401680e020300040c107041d002c038400080c03941c0306050100c0c000706981c0c0b4013907450050206a8100410203080701201184840600103592900c43c826a0124055895413510341d558840500060180b5002c0d06005400101c1c1a009541110406034100800841d24000e0300c10300792440d4500d01502203490800e000004800784c62030180d030107a6100d180094001031a8000e060309040360424561290354890205188054262002c0070141501003c20f82d038130350840c100b04007103a1400da11941018079010041003031421541c281c68006905160100300000c046840380303200c0c40b0b550802d43d00e80d50001508030070000006503410791110b00352001d100726030303803a94207400100e001c858000c035204900c0340210005440c81000c0403480d114040010340151261034400e43c80000f1104404016510402d0004502d070000c1224014448c0c0c0c1b4082c0043d082080c8001d44034a841c00042c409161507 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 715717482 1250 715716232 715716289
    0xe0907030c0804060c0903061a21070e041b0e091606050301030609050a0b090c030105090a030906050a140712021b1c030e03100501150206010605030c0313170d0b060405 74
    0x40d410303003801148c0060042c090302c12002d0700c000c054442240f085200d001110350b80081d20011b001c031480d500d941e007006800d40c10710300868045540e500030030031100104e000c14801607520074001840b02510885140304c0440c5401c20701e440c54440104155240c0400c2030b01c04016442c0c0c4a0101c0e815aa030211002c20301d12030528007140340404102c0c0c0100b01c80a03074000c000c150103001444460002c8110002d22407500c1c3d41e82104c1d110180184003034001030750030106204aa0103180140b150043c1454550805440700014240c2c58002813402c81311120154200400d082d410088100d000002007089903201040030000f400340f1040f0403610540c0380d1401200000c0c14052860440351071000303803da0300c00c429080d448034010082400303803520b8422544c002d00d088610010307001303040c0d507100e890781865a00c50120484040e000100441c00c2c400035040c142001481010000450071200e0f020306440d24042c040501c1540e00c8178280c80c0c0039a005000401c8195948041900240c0d807a4040c081c040b00c5 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 715718732 1250 715717482 715717487
    0x3050609010e0c152b1a03030703030c2a1a06130c021f051e010e07033308070602010e03090d0302070e16020d11030304030e03070906060e0907030c0804060c 69
    0x7484900f05108031707480900c42401513940c058000c2c411840404009851400d03200c40f1144400d0700407160507078400d20410001034040c3d03000c0c10411820b801c1c0910040001d5100c08400c078200c407485000ea00150032040c1c10400d101c5660584101c3c0c0b4400c00b04a13181110101d10131090146d51694a10703120708000415034000d101140300d1100400309040140040d01c0070001500054920588000d00301c05001010003283c100c5034107850020701e6144080d11200003c83c0034040c065069200c0f130500c50200c20358103202402001001e0000d0a0307071201c01c1e14142b201810140b65034425425641000e01e1040d0840000c01100d03800c610840304d110103401d41b8201245042c001e078100f07508070606941440840036064030503941c0c0c0d05641d402c031a00442d07000000c44a05222b0002e03000d03642d01c18008100041d0194851003c880c1c00034007141c050300d944600403016140c8550100c004510804034140d828201622800da200c4060304080c007210342e880400502e468401800601a142d8503c0518185031 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 715719982 1250 715718732 715718737
    0x207061425031b081005010201140c090f040911040e010e0706030e010b040e030403060c030207030503190b090703140f0103170a12020a11011a03120901020307020a030c03050609010e0c15 82
    0x2200b0f03d0000000b0640007a05043c0191846081035180d40b400044540c0b05000d80b0001042d0152000c84039125060b20300c00a421040d462980940c489801105a490341d01c078a032021400342c80040f045c88000c80c1071000310369a50250f641541d0404d0284e80c3c0075980028140704403141e5150020700786954280d11030040c01880525a481800c1422107500100008041e200b80c9011b010304000c4650500000d404900c03594000601091007480010344092a0001c403c5040e10003503000300780807442800080c2100d000b00c0381d400100e940c440354546e000c00300021080e8808501480c0810950443c0c403055100f001c407a48074190081c000510034142482050a00c48a881c1007600b036441c0c1d04c000001410455848554052562806100968121045452500c40e2034041c000c1c01c20130100d10724074480382c2d10a28030a8194441000450300684402d440c040c02140104a44048641035280607428004082c02110440e0b0510111407100301d0003041149105004480780d081d4035180c00b55248250 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 715721232 1250 715719982 715720001
    0x2104050c120312041218231306030305210103200114030a05040b150d0204020d0204030c1517090613020a0305100506030c0d150c03061206020706142503 67
    0xd01684240b000b0400c0a110341c0c008220551580070a21950060301c02c2007403860300c1f500528201c029415401d00001e1340d80c807441c204014000c040d60180c0340c3c04460a440b03103076008500280000811401725060114811061200c9804d00ca0255240d0313241c148258070f16441c0d020004000c80d401d22120fa018051518050302080c148645034613100b0403a4000b8070007220141e030301505540000d0280c1180300c84030000308500070000010020310b40c09120080d0014140514001c1c0e0800010001c50818620580100fa8600100c0c0c0b03011038040780140000c002c080e2008000078120306000d0010f901107016540180c1501200001c0030103030001501d0421241d00142c200c0c05100600e409118868010174032070f404c2a8211480b0000b00403d00809244411019101c40c5c48030356001c5000501c0d80003940c0b104820b180204003180c403000a04a015403906040f07402a5001505c0c0080019600038aa4142e10080e001e00c00303071400b071003a840f031661141d002103104034030304c00840d0115000380c1c0034005d035 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 715722482 1250 715721232 715721257
    0x1050427021207020a0303140603030a0f0513260d12050a0f0c0e0f010e010f03180210020a05060c0306060a111006151205010f050607030c0501090303022104050c1203 73
    0x60b410100f20107520340300c241406900107800e10285442068202d00a18001e10001e0021454004c0c15482114a1928698168204041000700b60411602c01d99444090100c00b08071f100c00740641d42e200500c04000500c2c581c1150070440510107450f401400e10400042800000704150365025008401029101501e250403854158403025195005100200c00c03201a07a00701d501840f581e00540c3c41010341070941c1c0c00944d4001c4c0c4030403020301c40c0c0c01c138200b00b054852046000c0f04481d4002000058214001001a400140010b06001042005941090072429006d2450502c81d0101d07105106400041003442030100e054602d6840401c040300b420b40b818a020400f01d603c8030310402007841742c204040300188581040c0c80b140302884c401e250480c0e000d80b4660b6441031611091125640043e6003d03028002a0b2143e10007052081c06035075406880799174011f03603c00611a0401c1240b01800c0304031040c4a10008100019000043c0c003025030000701e64a078600b401e0f6901c441d10354403540c0038100c0d0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 715723732 1250 715722482 715722517
    0xb042106020d09120806060d0f0b06032e060509040c0203090d0503190810090903050c0102030a15060f08060f040b060c010b10050c0c0114041716050105042702 70
    0x490b9003196001c50300c40e030301ca6801043c6000c003094003158a00c2e801d669007035000d40c0400211191440c154460000114041e001003408401c82d0700107070030b5400803110042e540f400000b80d00144c14204c1c604200c810f41900302c0c004064140f201c020114090210310740d01a66940c1781e460903890003041a5050010000c211403c840c02500d0900c0d1260010601c9094800d0b4203c80c440b44540120151481048045c180089880ca0070046c84044c1202341d4041e02840010003000348042000c0c00250300c50341c007945d000f003840c0d00800c0c8041c41d22086a030091041042c8190b204850641c40182c00e03400c80012201c03021110214400a0003c080180b03810341c0c0284d00040640603042c064100c40304074034044900034143d452001c1d0030340c1c42e40303d00144070403a40c00c0081c8507001503000b8102c51615040d101e048a0606844504010007030100305842c1006500c50882c401d805880d00807100c01822080c40d0042c1020b1408803108017100c0204644803c0b100d444a4100d241844ca50550b6100311620b0724000 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 715724982 1250 715723732 715723747
    0x160c090e07090f0b010804171c021206012607111603021e030304090915020301080c03070b0f0d02070809030106031208100f0b0903100507110609070b04210602 70
    0x41d5035100a01ca811500303800d001002103501c0c40c40c45450341c4803034183c41d80c200303d40c1c50f5078030080445410016140d15010030f00840301001c0c0d5080e4207000460041000590365540090b00c4070101070014100c0341005092141d05000f40d040341090b901c4c043c803410580a094980003015030724003881d01c001d0360043c40303152805850150701c6000301c1d0449000341d4500c0c0000c60030a03070315104190100c80e19078066200300000c02c18220550301110850b40a0703d41c00d80d041780c074003400340160381c404e90142c00719600110460a43d45402c3c803458004040101f04545005c1c02440145090f000b52445000501da01003420f8041c041c004007154058a80100208001b64492500c25080060544000c0005038510300060325215854160700544000000d0310061a03d00a801c00e5241c0c0002d0701c0302c6d018050b030350170441000c515028030781c02800c460b100e50140f000e00c2013065181440003040300b81580c2c031400c0204001200c20040710151307802e6151000486c180c9943c4000ca004460314010001440019040c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 715726232 1250 715724982 715725011
    0xe060c010f0e07050a060516020a0e06040c1805120a06021306082a0a03020d050403051e090a0b0901110d020d0905090f0c031b040b07060612030203160c09 68
    0xe008031500407908100d0300448042860362040103000701c0b604440c000c1c0c0140001405080038280700d0b40b00c8100628282c01c16804100b00c80c403544e108031842d02d904405d01200d443c041c000e80c02c0c0c2c045140b50030140c8a11403944a500c051080c030a19005030041c1f83c4400d8015414404568280e800c10000c1d55184440b00c0d206840e000f5901c9160006070a05000c41c1c00a40ca40c03001c40c00740c85403c0e030414605081d00e01185440c0c2d101c042c1000506a00300109089098240500c5104078003a80320f81d91582c0c508440c034586a80c2030304103180081020881c4442540d11710410005a580c80008035071110141310042e55040300740740000006100c2d0582c10340c041640083c03024412255942c405e010241d42c3c1c018010702c1181a0b815110001001000415014041000c1d55200c400b2042601503900c04803003030f65042c1c1c415000440c01a900143c090144880d5010b101d004090090382d080306200035071402500d0f4082c085504100c012291098403d0000725003044015080d8440e007002040340e1400780 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 715727482 1250 715726232 715726241
    0x91b03130606050a080703061107050f0c040b0a050a0b0a05130e060f040606050d0b0118030804051801030c0b1c14090607030204080c0103110403080a080108010f1b0309030e060c01 79
    0x8840d402d050400120f80c1e4200708003548102d0343ea480060140d0f07801c2d80c7d10038000d0200c4420400d01e0341001c0c0240404581c041001201703d20000c8003800143d00060240030964031411400c80c0580c41c40001000b081e102c24021400301c4550000e850384800e80248210b449200700d4003448841d00d102180490340c2c0f0081c0011a0040f001202c0341da507000200d00c10700098512910400001c12401d001a00d80754a00d0380000d1034910051611102d10039038808084a80c080302c0e003041c5da0700c010100302449207040010946030f60b001c41c280b100e9007661465403041901c090500510114220100d2010702d8204a2040d441022821030b20030300144e40d10308290000e10f007040368034403c0c91051201085a06001c1e108980668079818013410100424030010b40281c03c08002801c0d0300d6408010001c04125800b0240060131843c1e500c110841d4980307107219003940c83c130040e020105403505c05560300b9000140e807038440d80e201c941030201d4040d02500703081d40c014464484640e000307007000a1030010254103510 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 715728732 1250 715727482 715727521
    0x301080d080408030a05061f050909130b01030f170403120f0c050d0e03071502010207210f120b0904063603080903160305090109080a020f091b03 64
    0x845045140c0031004440d0208280e4001d00341160400c0403410310081c0e9085a80d00000241c141c885035040b1840140e00c64000000d440c000031400f08100045207000c1c0c04039504036040c41c01c110040001a11100c102880612004001c202d101c4242d60401c01c1890b2002c020162900d40640c440366642082a0811050101030000070003102e1240c21032801014800320040e04030008019400314502c007030b11180403119071903902d0702c00e51000051102416207811800c020300e600158030b40145141c11064004480e800c1c940c0e0180d480b04017900309621460b130180340800c41c500900c0380d2480c505502d0040c072800302c203990004503c10400091101a400c41800c1e0325500740e6400100c61894034100b00b000c00c503441569015003000c0344201180c419420240c00c0301c224016640742850900046d6180701c00d00208401003080811488200d41c0c0100c1d40304001c10000740904403290300c507400174500c1e04100c0d844c83c0c03148080402045035468041610b60807000000c0d00c1c141d40c4c0c2001c0b0340d243c954910f03800 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 715729982 1250 715728732 715728749
    0x20715020105011d090615120a0f02100f050d051b0309070e0c07080f0304020609030a0b0108011b0c1202010b03371208070e0603040629010e01121d030301 68
    0x64406940114420164445e18001e000740020b6180c01135244a84a410351201c0e50100100c03070000101d040500407207001c10701c5000100c8020f041171041c8030320749041030300c0e013018044050b94120049030084111180c1001510000480d90350700300103e2006035012410381c0e51200d02004000c070480001516405a8820015180d030680e02c2c2d420b122020b22441030f00401801c4280a0000d209100d00003842c1c2080c40203060504000d9080080b82c074111075030105868281c4980d0041080460a109000c100210601c5900e1204041034001d00840d000d00002815104652591300300e051003940106041600141503403104401c00c412030f951000b41c00810149203425107403046c1130405030010580b900750700002d0781c50010700984060b0740310034004014a05210207034600c10265510400114800d5114110024400c60130002405100c0310031500401d0400d240064031043c1c0e0780021100803400f0007440d05007881c00d02030346101d0180218410090090300f44500c0c220070000040041d5060300c07801c1 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 715731232 1250 715729982 715730009
    0xb040605030a0f060f060c0c05030312180106050906100c0c080a0302070801021e0c0a0204060b030f2427010828020f0d0503120a0501170303060306011502071502010501 74
    0x20807010403508135200b03030346040300c075078070f080000c175004504005160707000307110000d603030755444010a04590210006c0001c031003420003003010114001e00d0301d545980c81d2500800c0010f0514000c100c50a03c00340c02c041c8124001e00c00d4080061040c3c0500a0056100c0402c11034581d940040e26550101c50b203084015000301d2102082c200d5052003900c0079100c5261401c0102d2084864800866000c1d1001d9480ca001311806000981c40300d0051400030711561403229030301e1a09000c40811039802a1009442c0d81d4928071001101460302149070304070b4001c980942488010400c40d01c0b08121818074201000c0343c1c00000541090f000c5103100c0025900451000301da000c440804034a10100c5400a501c000c1080d0300340101e013040381846c80f5a521407412240780020010302120324040c21195908015200c200520840b4a04c0b0007504207600408011403c500308540002c0c0c44e020140280480c01c11700f0404000f40c0ca108000c4400180241c0001141031040581c00a000e044c00340907014105006 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 715732482 1250 715731232 715731251
    0x2180d03030b180c0d051308040806150d050705041109090412030507180603271b090902150d092f0108090316050c04060e041211060a090c0b040605030a 67
    0xa581d50380c411907484003110700e800640c440310001008047c2c030305502c5003d4090003100103581c1030001d0028007130030401810b181c43c015011414070411100501d000d0340e101c650713040000308005002c10a94004407004a81886070003d4101140202c00744c1540c06403944013400b0034818060a41601c2501640e410312890351030301e10603181d4890010301100b400341140003c20100740320b0360201441240100000341c4c828250a494064a00030840c240c0b41e540aa162458048046844e804018075580d501841103107013070340004e0050801542c1c1051928800584100c280007254010410b159100070908040540c1c4100c2d0704043d44510b10440000300401d6403020258008c0c40040d12400b5004001c62034104104c4040e6854a020003049a2030f124030107260800743e9680c000c440143c0821400850103203000d042c008040c03070901800c0014400048985c0d060b028002c03580e280d1051a085010410501c0e40c60100c040d010542d200140d42c150101d0041121a4800f00550160120040510102c0c0c0c1 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 715733732 1250 715732482 715732519
    0x41b1d1315090f06120f05030f1b0f1b0402070c0305030f0a081f06050714100b0f0d030c08130305161409190b130612021e100302180d03030b 62
    0x100c1e4000c0850386202c08030001d00244e815940c404074544a40c7c1924203280c1418400903c0b80c06c00c00c01d2101c410000c42c2180c40d00304040002000c28100a80148500d410240c200c9680781d45055005020b82c1e0002401e0081c4415080c012000359809004c0320b90340c81034211007910a0b00300c203801d9400600c1c0769000c1003246e1100459640b252070710a0b40380001d5071405a095919034440502140c2c5142003402078100000244550139410001c01b4000c90042480d80801101d0000c0d5490769215521505130440469400500028082c0d8041c504a0359800444c82e48c46e0091050352004200b4864000040800c29000008100f100e40c881c0a41a52034000c004100d500300302103c8034201041070b00c10060418019801c0781103c044003500110b9203455a07640881a110107405c0b00ca20600440f08440031420450008444c02403040d142031201d4980170001058100d03101504000c140d004500387c08031050f1000c1d80034100f6401001c1c203548000300e1070b01401402c0c1441321a2310400d000700c00014003c1 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 715734982 1250 715733732 715733741
    0x30f0d060f09090b070c061803020f0106170303220602070602091f02151302120f120304050d03050c12090d23070f0804030f050c041b1d1315090f 64
    0x42d07100b1002c40303d0385d8490000711000311b00c0520507148a601ca920045807646031004207588580a54080c0c0365207401000714a081d03d91903840505502084164024003a00c04820f4039084000424050030b0030115210410700c107044043c4c06008503200090040401070b440d4000d240265080d28075034400192090102c1c0455a0100c4000168210b0407a406a40010786181540102003001d107030028090303900441e4500d500f4000e90f5003c1e520490040b03501620400503101d042110b03040991961a2503561552100b2038482c43c401816110170204550ba2607100a60f210704281419807000d528103182103c0d5600e002064203804640054048031002c0c40b41e04601c201d1080f10003000f031401e107883e5540f40301031700740e0b0000782d42111080c4000301c006401c8c104e402c202c040c0104000e002c984e41005c108000c4075081d003088080f01d001c04920700c0c4800c0e004000f100e4035002d14280700d114203002001040810109070903541505140094420848045410300300036550745010800c1300a01510100044a = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 715736232 1250 715734982 715735001
    0x6060903050d03050a18082101060507080309010b04020703030b0a050a0f050f120d0914030304030c0905090a1203060e060d050c090a02120a050403020d020601030b0a020c030f0d060f09 81
    0x140c1080400345402c50082d0846a0018140003001441581c0400d0398158078500100445004000281000c8114600d005034054541c580510020725454410003810174800d80000a0050034007000180143c2d00c203500030305001c4405401950754a0803403500600401440003814850080d800c00441d250401d19100d900ba1216803400c4004030f42010f04110a0105c89100c2d96441600c4034854911140301344542c034400350458813562607050a043d0a4060b1131245004240250301c1804104041800c2c000c0b6041111400d00e00080da5841d041e524030309114502101415400e82d001e041c119090781075001d0801c80e1002001103125480d40d00c1006042616800041c0c0b8640c0207150041561a08030b4046800c4525400d005203090120b180d40d4000b00b0080300d0010101750303124200b00a0680511042412403098406041158155030390703400090340103014000c00c95400704d0400d50b041c1d820003c40380e8440c0c41c084140d44480d40070181c2009031586001c0d280418420080026084500d8024100e45 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 715737482 1250 715736232 715736243
    0x19030f030c0819060803040f08120306031b04090b07090f0b0306030a03081017010606030b060309101104050604090b01110a0b150a05040207060504030f2d05040b0c010b030106060903 80
    0xa944a251a8200043c41d040080682c40c1c0d880c000010001c108100030b20051101540d20a4002c2c6003070142ca08240010300e41d00958001001000301507603001c521800ba4415400181d07040a03030400c0424010021050014a42070742c0c0703030030b00c940f90b40c1066500080702c001c02e01045805403a43c00304070326408299416901544a42c040000181c0507450546d07218a08901c4107100e5562460220404118102c1c14101a59034460234015168036000314003000b8000e80e8100e10394184408126902d1405007415060141c0d20405203580c052501c007124001c0a0080420f51261784a02800000306036298510b030120300180300c01c0031010004960000201c0d0003540880c501d07680c410300f0303069224100403000e42c01490004081000d030b40302d202030805035025420000305464103140203803c04100820400901040542e44a420002140f00481541000c080c1c0c01500c14807010980300c0e03000f6600240031701d6402059811404105600c1749000d810100c0c02889601c1e6075407401c1d03c40c16250300010b0817 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 715738732 1250 715737482 715737497
    0x62c2a0327280303140103030c02040b0105030c0702151b07150c050d0f0917160605032202060d1d3304150c020c01170f06010c050f19030f030c 63
    0x14a212200503080030303021341004210803802c0008025100d00903001140825020800b15003036040600c1124074442082c01d1851441c242050780d0141ca0041e114024800c00c4074141504140381c01782c00b80c45c120400c00382c0c010100441c00385070070340742c20160240d202c0d000e9125000c60200e03407003841900c6d56907070000c0143c00b00c00750140088500084403842d01c803d1100e81c1c0c800041108a01290f01402d03030070718025000140124600f02402c091942c010001c004043c410b00c10002c1e2140c1035041c080078002041240702c0c2c036030310100300c1c0c03030003100030003d0400c0c03a19504d0a261014101002c40c0324004105544841d00601031883d4013400c03403e503180c1c00c410340004031003217811100302c0306820034043d11041107075040d074200d1001650128121000181c00c03004c00b003e0207580000c3d040f0f03200d01c07501240c0d4016181c40c48082a00200042c695410015000c910b413051200602c200000e84980c041620704030200c03410901090910110100c000680302181040302a1083c071444940e20511b694490 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 715739982 1250 715738732 715738783
    0x1206050a270302070f0902040e0f0115030f1103040807020a0b0a0c0308040201050c07030302010b040c03021606020a09120606060e0d020a060e031f062c2a0327 70
    0x201d9002004000302c0a5108246010504480800710780000304400c80d0090703525428200f6001c1c1c0018003921000e4501680801800741010341c0454140349015807070f00281c81d0381210380310780c054441c1c42c0c0780c110142000418401407001400091803840e00030744101841960b40d00d08105248a101d0300000054403c46401c800a03205d40706140e00140140340c0709091000411012342070211760f90003180503070b658100c005c41c142001d0089080703801d0141802c600f409680484d0403e4010380000c014039440d8005511091107000761280c202420801c04c000c40703030603414589503008019601403100071a09124a0600601d000444442001d0f80607001140f080c1c80c11101703548040401080360791501642d05268140303907061842c8815042e6286c4041000c80c07514000e1200382002290016000c03180c0c864000d04c0a5000c900c95802c00c00b2036005014920001400e02511080c0b8540b0b8200400b00005114960b410040510342074840744450f01456181342800e10340d41c603140c000e40c1030000301030a00304 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 715741232 1250 715739982 715740041
    0xa060914100e040513030905030d09090c0203131509050405160e011b05160909050318010909090302010b1f020a060207020607020d050604030210110405040b0a0503071206050a 77
    0x540c030169a03820002d5003500322000180589800700e40c0c0c5000d0a040040c14428194800c85c0c100051001b600500304826500400031319203150340c0120070074180c5039401d00500701d208004440d84070b04258180c0148c1d54441b20700070a11048805050001402c7d0b03040410240750600c42e5074020f41d2b02c0d520041035448100c07002da4000031490421814080c1c0d1410031582c06062044401c603040c820b034050314510f040500d80503460450b580108585c40e140003121000601c000048802d011202d21201c0401e01c031200040710400e0464102c40521420304c00d13280c04150f01500401c20040c0704541c111900c400d107a0750902e60f07849042d003480041c0d01203001600031400a5004103200c074006000303d0b18205940c0c0118002c40040710080314a64000002c00091550501042c01604d034129404c0c031101c09001c01e07480d820b00444c0652441956200e07032000c4c845e030700c1c28113610007004060f080d50a125602c41c84c83c2000564400140d03040c906010002d10701d140c007482039440d545c0b9070b641c200e8034140e90034040 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 715742482 1250 715741232 715741249
    0x305071e0603051b0310061d01020303010521010f060e0615030105010302070807080712260f07021c03020903070509132604080a0c0621020f04051207050a060914 71
    0xc600c0b0800e00202c4813070905800d00001c40c0b04e005940060281540751101c01000b2101e080400c52940d240d01651984030382e030120480e070455404a8000b55480900814042803900300409044d05628005500300460801e8010700125100d852110f102a5203030414004c0c10b12500801c03e0064100b000103100c81e43c001e501401c1e0660080710005d09081072583c640b1000d0b030004805865044c2d8404000e0400b80d0f000d080383c291100141041012944d030b00d8250072181c0300250054489100c1e407400224158070811801c42000d02d41c4410290030050359002a000b035200425041c06401003520102d05400c2028843d0301506964081080805c92611051510a19140c195201d121036030442c0c0100d40c0010302403c050108003018001507a642c0c5040080c02950391700c0107080c044c1c1181c4890f14414490610214003040040251340c55245150b00348543c856600060b5110350191f0104052180000d44101581c9090706c106040640310300007621103003411320030340400301c000c4001d030380b00c50429081 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 715743732 1250 715742482 715742491
    0x9030f020319140915130501090807090908120f0f010f03150e0a2a0e0606030703050727050301050709121b0306140a0b091e09150106090305071e060305 67
    0x1003a0341419400030000d5001740e501038040740118408a1104100c03d0b400b02100c0c0104401d00342001c15600c4d00d40515240e01441c401d0800b841c0da6081c401051101c160201c908240c1c60140903551860070002c1c0342e0321444c2c19116104400c17148000810000302c1d024059081d207810081044401c5c0303a40b80c41c4030142c0a5811700440c6805140d1040f00000c04911030441c2c144030520103c5006004600100282c2d84641e116180d0b0303100c40420302040f511500300f120341141240c6400f182d41d50f901b041c02c1c0d5000e5500141580000315001c0301704418281590700c0c90903200304a0090046440782041100c040384075000c0d22101c40c645280c03910000b060340c40c2c804000c0079400f9264614a40c2c81d110001180d04407100305007069402c0c0104000b01c606446000c0c0440030447e400c0d1002d00f0000041e44840241c0307041c03000740c24000320200d8119042003142d1a505800606a1403007980c44400007807485159100442c0d2900c1902d40c0417a118404403207a4220b0a00300c508040d8441c50b0038001c5025080140 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 715744982 1250 715743732 715743767
    0x9050316121401050708070e033f16030e0904030e0d060e012a090608150a03080d1509090b0a021b0a080a0e0f06030f0c1b0109030f020319 61
    0x1103051002c00c4080c01003910802084d207401e030a81c600400081c00d024074002c00e6600c070703070841c5403510b00c035030070006600061704800304088109100e40c00400b03809164000616040b000049040e0040e100000d000303100d040e100b541d60b80c52204c1d2501c18041d03140815240200451a40e002610301e50a10340594444e11b4011030000c1891480000000e08490349401c14204444954100320001d03032034003862441c040c1c818507042c2001031074000c00900e860300c00740c500b507464106894945100da41d46074118020b0f41e00520510f41c0d030300c00084040e0083c4960460305801c2e4440c810300048800c080d114090703a00d60042e541e00701654860700f005000354416444080004292000c40c42030702010005600d115201d01c03a480e5440002c1c00f0058030031001e0b083c10f54812540180c022250b0703103600c81500c0e08454000003600494640c90300c07218240c012040280005602c410302400c040320150407600e081406034407841c80a0802c0d400417620391050700c40c4d40100f405c802c0603844081c0d00c5000e42284114081303 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 715746232 1250 715744982 715745003
    0x909070509040f083708070509061b0d1119060504030903050d02070509341106071206060e18040501060b040902030a0f2307050904090807030905031612 67
    0x503a100c103c150000f00b4075042c020000401240000513004004e58980c444c49040345c00701d0724400004000c1e402c0203019030204100803480c50b6540d1a000255003820b0209141e050225071403070001551b40010301c1c8100001140c014042040280201d51040b1000e00da244417056403d080d00d0b00720107004003800072800c00000600000200307006004803003000d0401d501814000e45008c0c01c120700f0300f10190030fa143ca80240b908030042440559002c40d030044c43c21012a8802150001c265818000b5a0200381e2500035641001091036204000d040414041041008a036840f21021540d400c040070030180c0104658950140c840c0b54600c00035440f41c880c00c00400d0b00b0f034881d00d5003c2542c000383d0242080c15008801d021135001f135809015070a010070401003096002c0301c000b20444074545c0c136246034070140b2000420003080c0b107001266004407000d4002d000c44840b074a03184400e40d010280036030004011a01c0420140341c04241c0e4800701650f015500445400d00e04120f410407640001226807440d82d = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 715747482 1250 715746232 715746263
    0x603060209030d03020f043b04060c02030901020c1c050d090801060b090d0b150301180b163002040f0612050106090b0903030405030d020c03060f01030804061428030b090907050904 79
    0x10312540003580006000002009d040928040b000d0340c00303c2d600701041d03400500940480782d0b03000903440305400c0e0440d420440d0000c0c2840c50b0040d1124004068018024000d000760400d412881450880b850203000700101503644402184034020010b0b0711354000550800c0f44040b8190361143ea8004070107046060491b0f5000d030000b42120103659003a400504050481014001020a001d61240090300148168440d0b004014807202d0044000c1d009901c0088a01c208103004c1a40c03400349000b451404c543d01d640b07807501614000b00f42e2082c4c40002d81403503d45c108100644c003459049400700c0d141c0307003085070a042d4a1503050300b20452003605840140800541541d0400c00a10200c40c540c010341801460700042c0750a00c50002e00d0290348900000040000428440c01c58041f1807044c40c1c484904c10218400080600c2143c540175115205103c101c1c005601c00750005002204c1d6803400c0098103241405e00c50bc4160880300d01800350003121082016003041c00c0082d5002e0711444040301c91960 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 715748732 1250 715747482 715747559
    0x50d03030b091005010e0409080901050f0c01090807120e090402130e0709051023010509040615080901050a0614191a250809040e100603060209030d03020f04 69
    0x1118500307080b201c180c40804c02c0b56041003501000e80004d80702403180040c0c0351036100c3c40713102e000501410008000f880300c1c0804407090681d10128030b624028030803082942030850a54104a10581c0c5020702902200c1310701c0e0203040413407000e59001c2e10702503440e6129002c02102801c01c10001169580703030541007500042c2440309501030070702194000340501300000005011441b40c3c002402d500d4902c82000141e24503106001c201e90400d1800303c2d034501000340441c3c05050164480140111500012050707590401201442040d40c0307402045640da500340b040050303515a100b502035001840090101c1820305036000444404d04a0010078100e03525880c000605103602d0100e009803601007201c002c1000721055400e035801d400c805c03c1090901c42d40701c2030030328450b07050340500c180d81e2612100c1070000305001c00d40707440d10181c80c10044c40b541c03403c1c0791000c0d601513030036588a0b008803040c03d03030b03101e000e0b1003603030701ca0824001454107140c10800301c915101202c83c1c00c0034940c040319800c10405503 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 715749982 1250 715748732 715748749
    0x1005250804020118060203031b030c030103060b03010902100302270d020415080703143c0c03010e1605090115050a0201020f072109080303070c1b120b0f070801050d03030b 75
    0x40c0d0b946c0150750303038540036045508008268aa0304e900340000c1051014841d11001640d06507a00040001000ca143c180040d0051068810007500300070380588240070035425601500d41e2090384180d81212141c4501706c0800c150301a00c6140e482204940d600c00542804d0b440342e89081c01d241c520001c1191030b180d40504d0700c0200e510440e4585c155408041c00628188000c00a9520603100008968407444001d8141c01280320341e8080803141c4586200d0728401013190300309285002d002048585508101c0548501d80001100c401603101100020281026001c250481d45101040781b205942c0d01400c844e584d01107401c0a003150b40074044c49035007c10050090945500c80c0e8500c07110b4001c031100d800781e2500254024028881619001c0100711000710071079920101c149808a2040400d24104e1100a9030600101200030300b03c00c0030a800c04181d0401840c01e00a555070300481e07031024880b0a000d030040f181d040c001070780400100002e0030101900f00060f44203040c00310b001d02e083c401080c00107 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 715751232 1250 715749982 715749989
    0x9090d0302130e1501110606090a0b180a0b03010c021903050901091d04121803030509061c050105210a0b071b0605060f040b15031003080406021005250804020118 71
    0x10004e07034a0108640e00180d007101c60000d908082c01e403510302040041e05c08500107000d010b4131910790260b070780340356075034681000109003500a03c12141050400b81005210b9011480c1c0290729141200035090b00016446901d01c8150381402c0d1100401d940444040d001414058148101c1c444082000c00c42007407001d03200d10030b01c241c41240340390904021209900c014001424011880810810b0481c42800c8105882d00b41c03c056507500161404036507075100c4d545548c980110f00482c05482d165168100ea81221030495020445e0000f0f1081c419002050380c00d00b8405621218100d0001041c9450040c0c0c0182c5606061115201c0704220070f10380e42901c8012a10f6a5a900c2084604e2501489000c465007065804000c1e2840c101e01240813902c40030317003405807050702200003111507242c03010b0400516482111207440d01c5d960302d00031b50b076580c2102804510a04000c0040c0c8031404000c1c0704852030080034100801020f030800207079103007400a0010f030304201a111110034000700061158009 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 715752482 1250 715751232 715751251
    0x3080d1404080715060e0f0c1309090c0902091f090302150c010c051e0f070501090516050609130207140717060606070b0f130f08120609090d0302130e 66
    0xe5074000c4c034015400e58100302c0e00c02d4046203442d1040c0f00c101e001038806644a04010808803054560301c10f003104a004034072684180e10080329007c58085e0807908480c040503c1080c0c0f19181c107031103000c1103050740510700c00b01d030304000b10325000e50245561603a10781c00c00c4128180000244d48a80206034080280407801000110004107494040024402c3d100010060b15100b03042102d04909002c01d00f08400101c48003140c00303e14081541000740440c0c00456025008000701d10311450140c1d02c0c0e05e08a01031110f88a40500700040f00d040100c21910701c108001d1681b035070a20987c02140081d04041c0c000d4070b448902044a035441041044843c0103440c010700c2ea12004156115a145801e100601c07460240c6002c0c0716007000104000c142e1030b003002c940108000542d403840e4042981589401c8050400d40841601400740f107031050052504440300a04007505640d20800d0045021056400e1146c81d402441c100b884180b03c1d50242c505403d0341c02640d0005907642c4942c019086050300e84200 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 715753732 1250 715752482 715752487
    0x6061c06180209130608060a0b010908060108150708130609060902120c0312070c3605190b100503070909020403060f0b09252717030708030103080d140408 68
    0x80a150450342d052a400d12800301744541414a0881a100c0d94054064000300752505207904c01c584c018111840904803000c222400c660307554005a03030b1780000100008520143d5808110194403071710308944901c050350395182060030103948000007040220016140255030300e82ca81d005aa4403056420810b44050040c444103000c103040504003807a00702c0c21981c03074004010307410006884040d0300080307c081e4a4400583e1880d41c0d00f50441500005a03d0b10ba0004d103405c0c507600e45d032140d208602940490f840d111404014a21320411aa071110b42d03298810310551000100c50710071401141c2c4014145001d0f1100ad40c0e07411300e00c0c140c3c3c220390801c61b0015129000d0000704a1244661400080c04940030601801c00c5280c00301c0c10100c10701035030702900c03443c2003031254103000d110310340c2c0c401c807484c02006c802c0c1c0c005044040480035035011f400000101c0d8202040c408030008280c81e08650064502480c40e480c1da80d5040d690703030200c0d201041c0141c45840c601d10150300140070321310030760240000701d9 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 715754982 1250 715753732 715753747
    0x712030204170115050103230a18060c1e0815032404050607050f070305030c0f1602010f0201150e0402190e070905030613031d09070c1a06061c061802 66
    0x200300d04c40b603421490425141565a800d0704c008201c1c41d030701811060031001659240d1034070487c06071406012249484101d00071603002c0014a9101d6125441c0a50700c01c03040b10f0111203c108804048148100010000c00c0070403917054500003000100d140040495880c400b25030380900d03d2080e58184002d680c8143c1c0704120510105029090b800f20a500d01240f0741040d598079942c03c1c0c0146030015041101c01f00001c0d44508000044450301d2440e00c0401d0340b2441501d42c0144c2000201904070300058601142c51b08140c014001c5110098400c031410f003805090021100c100ca8009100741d0b440721800c0b0889001c0429611030138090900d890b281043c61400380c2d40948003d01c0c40c1e00a5010780d120300e00300a401a03425111410055151074691400b1031800e4000d4021445c1f805169480903200d810b001d6000c0e0880d003103101041c401d490100c03555607404401d540600341240d0164120504005180c00c01031542211100c0031500000010342c1d40e100d0b031110204020403080980c1d5a6800a10701 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 715756232 1250 715754982 715755011
    0xa0e01090606110c060418200c010e01050c250807030201020901020d02070305060105040f1401060504090f2913060909060f09032102210403031d0307120302041701 72
    0x1680d03480f006400a0620131000008600a40300b00c0c8288901126613451040070700d181c0b508024400901341c40107107280342d841c112100d081e6005c00c84110079981703418080002c02c078040c000c0501c955001c601e07850400310b94902c10440d01e6540380e4001d009001602d01c120000700c4420103000d54900960006844203401000a40341503200c2c1500381c01d41d8010142040011000510b09042d620151408110b40e00000c400c170300680220a00c2c50704040f0340100100703c1941c02400340003201c00c031003010702c90348841d503196170110750b80c52072154103050100c1b001117079010401c0c82990716a0f9002e0301900b640c0c0c810035441022104150480225252520100c01c00c1c0109409a0703848134145120402c8003603490790f00500501480c072501c88a0034405040d020f41e00000e54184c400491002a05403015400c48605d00034007042101c08501192600807440024040b60b040b503400f0440705001545044403503180c448200720018041c0e01015003c1101007070b1006680b00804c54040c800c0c1c0003045171007034110034 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 715757482 1250 715756232 715756247
    0x3100501020f030f19091d070810030b0a09020328153c022b020406050f090316030b04260711060c030a080406050109060b180a0e01090606 61
    0x14440158002d0204a80901c6440b01725481000d29418200c58140700790001e0303e8031922030780b01c3c00d01040e4103071440c0350540403983d03418425441c2e6983c103030309a915070310040303101801c17030001916180c07030100041c101b035039a41d105d080718a0004003141c40e074803403004000c01c164040707445070249054890003039401c00c035006001828a401010301445651007a512100c00c0318003120000004024030701c085001d00d074600714202800d003000c000640d590358042c0e01303e400b54082d04a241040303551070604000d4808080c400d80d410380700030795246858030900b642c03c1c1c122030b00100f00883d13041c000c4400143c1440781c41e030f00c1c11000750f210713018100040c980340c00c1c122000da40d208101c00010802d90b24181c0d41c1c68181c011128440d40c040c1c4154006070b00800415124064641c02d0760941c40b0004422030310035008038501d44030b103100300014030003681c0300d0300c01d1800c0d602c4510441c02200002d1001948000b0030040340c46510501a1651200c10f50300c044034505400f00707a01208289964400a20103c0c1d8030010 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 715758732 1250 715757482 715757503
    0x90903110727060f08030a120207031b03200708120906040b0d0f090f060c03050105030d0c081c051b0705030f1606110c0106050103060b04090c1403090102120112020a050906060f0310050102 83
    0x10850800c50710341c43c0a8548440601a01645200813300b0310805014640960119003140070000580200103030341582e03003450307002ea40b48501c50001c42c44000d50070401200d811480140c80740d82040c1c0381000901441d00015000000661a81c104d040364030a24413070460494090510442101aa420580c04640c4034926880c201400c1c00c0c0140144c0d280024800580c2c00c030ba00c3c2c82c1014010310700381070300c0c1030294450b039024205041d26003e01c0c82031207030042c80c002d224211401c01503a400340d842c0302c46486030700c20040c0103810901441d01c01409580142030f2260640c0440000042d0f80d0345da1030b0485920210030f01c400600445c02e0400e9160900c20b000103014282003c00016041c00c2c80c1c400a40214412504d0981c1c45584c030030861481043c506e8948a4104043c03031b244d00340904000d02035000f11900d050610354510000801c4462483c1649050b0380140c0768102d55802c2c40305000550750004c1c84150007050030070034007030120301d0100150b20480900f0340d0070310b0242c106000241044072811 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 715759982 1250 715758732 715758767
    0x30d020a1b0302030d0501052e030e030c010b091003170d0609022a03040509041112060103210f1b030e180108060601020a0210080718090903110727060f08030a 70
    0x29083c032002d5003104030340c070f26009c20342c05040041c2030301950840213032215441340c055500001c0385904031036405410034100780a00301e600842ca50343d54290444003034990301c806400b01107540300000308180170708000c02003103000307610100b841034640703415100f642d21003803408030100100310580c0d0b01580d8508004000081e0a000782d880e180c54000020704454010700040c0c030902d031280c116000c90751030006030b011000e418401d07625690b03583d04089401d00c045010700d607110074400d084024100d00c110203a40c0310040e66241c00300340c0781c01c0e842c019200560003901241800b0b025003d6025595507240e4208000c400f007100480030350f040210103401c0c140d025003483d056600042c2003074010f035280079030403007a41c60525251200c0e40c1d0300e0008450034119070200c0b132400d601c2d81c0800b03d1801400c0d04624071482c000d494021181032402c2d25141ea80c0410701c620441071019035103082121031070040d80c8850018101c00400c83d29211001070300000c90b650311010180d400040e09141c001d8010300f0707074600a110704 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 715761232 1250 715759982 715759999
    0xe0601140427180b01140a0501080f1008011506021c0c020d05150a0902030d080c0405041e0612121b0204050c0c011104050307120203030d020a1b0302030d050105 71
    0x60a120b40c0070265481c1c00c00d4000d01000e503000d4844403030340b01000e18050041c244403140c01070f08011304d00c030b0000e00039a84c00d608020410903c506101020104646040c2e40f00305017950340e5100b03181c0c2160094504644250030389400940200c00740070341922100c0d95103056492525020000e072818800c600d421245420341c2c07111138076090700010b8402400340c05541010340740340c844c0b800c1da00b060003c0d449040019465003c2c032800030969400050964405d07000c542c4c100006480c00c0d980310f001140e82380390718502040244141d04003a0480710701015002c054510345403404041e4415601036400500703c0340b4251600200384480302c1b0000c01400c1150a0607203020b0800409080a0304002602a020710b031581c001ca0030083c01c000860b216100902d00800190503040001d1b070b0180d1040c071840f4846d11540d0f20100d410300a0340c220307088640d07000707000354a030600305c40141c0080d4200a107290140505144240010040c0300c4100f00840c0c46580619546c1c4407118070001285c1060b00600d0113012030303 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 715762482 1250 715761232 715761239
    0xc0c0321031e150b030a05071115061219210516170d09150605040204050102150601020703020d0c0e0c0c100b031908070515040203030d1a0a0e06011404 67
    0x3242da1044800c94900070600f992110000c0f081443c1e1a0700030b44da030702e80000070064041c1c800e42c4264010051680d804080402c052009a034800510703003602d50300310105021843c1854074083e0201240c0006055403054080c0c000c401e00704400d0004261800d0015010f0f030b075002003840700350b81040030281c10520f081035a58503c4200d64400540300400d119000c0303207458030108981e000c0c0c44c8141c10600301441981624a417210210340702042c503081250529601260303514082c02518240c0d07006a006142011410b555038542c207034090003840c150b00911101001580303604010084180c01100d019a100f440d00d000004030490040c07010b144510140190141020042244000560301d100d0101c0c1e622907034400207060210a0a000446081305004002042104000b5080460064003600ca1104445903d45035420048070001d6168104203e5120b91411652101d00780301445800203403c5484540459106149070300134001c0c20fa80001002180d41e13120101180b0201981d1015023051318 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 715763732 1250 715762482 715762511
    0x30f0a090b0112020303070c0b0d060f06020a230102030106051b0109030806060a02120a030e0708031810230403020319240902041103070f0c081602010c0c032103 71
    0x30180290610f4200100c0300c801555801c00564070015004051585400d944504d184560b5000c0000880e00c81d080510000701c41c034901201750f0032203d030750300503186000703031662151883d200000074180041e0004c400541d0780a8244051400303410381da00e5060784c8070101045a04151400848140303242c0c105450728002990007605140c018200360340384e98035280c01c0c4030141d0405a062012900000c0d010443c4c040840e4035801281c5414000415200d145496100c06c540380c2c410310440c0d8103680d10700c9040701c2c62402d101565000414443c5844041206905070200000c00005540c611146010405206528052200014000d41e1060300b900d200c10070746c1da0358508a042c0c041c80181000508040186108503040040225801401002410003c003030071820707030b00141c0710140051284140a0740c058082d526172107000ba00300070a54100700c440107582840c030341c444104a04000c1c00c208480001050440b4a101441c407595013400040c900e00c0441c6c00342940240c0700003c0504000e0039030011103 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 715764982 1250 715763732 715763753
    0xf03030324050109140612040302030409110313030f1205040f170a0c030509040e07082104030305040b1305040513020108060411090d080418020a02010b06040b221a030f0a09 76
    0x484d509400c038075070400e00000425034011050007100351f40c40d00e0100300030542d01000810039220300b040304020201c007520755003400d40000c840300d1a611181c004400d0100780151101c0f00044000c1c980013580016034410a02502c1040e10229034042d02c11000342b00304010107210001c07251005001c181407070007550001782401c41400d400707030500c64001944021502c0d030360070002d5100101022079141c3c40e96032849035520500c14000300c034040da402c2085001040003408035030440790103546141c06e080c1011042380c0c40750320005040c0b0880384540070006803600c0b9406158810b03d0300032120440d04010780009003c41100a1041d8801c07403500e12603006d910481c005640140c2011340e00c68104045a107000d0b110340c859900030801055a80e40040083c0b03401c0c2d002001600026802441081800b07020301c00e03035008500840100120500c1070007041c0c0d15840c1d2141d01c8032401102c10007219038402050104c8040140341030900003000042105081d00b4045454002c40144420880c519064139031000d02d1 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 715766232 1250 715764982 715764989
    0x103110304080a032c0312090d090308130512011a040501061205040c1707150915121d07030512030108070e04030c0c060809060711070513060f03030324050109 70
    0x50344e01d14090a403040320720b443d2041400c8003100c180b0005d1482c4002540c039084140003501209440001459100c404a9940e0b00910342d03403500480039040d6903074140140c00c2180e01d94010302c0c6005002503281ea035100e00740d8088110000019400d04841d840322014004042c40b5402f603030409004000ca00c2d804941c0348100700d80c60301700090b1a11603252411942c000c0b5070010b09120140c81138800302c0b42c004aa107004643c03030085040400181d2113026604d03040184150030301030381c40c0d00e00c3c01c0d201401008030345501081410000307203c0107800034a98801214508400d440d50006006004002c8200543c04040c8010401b043c1158036100c645940c0b078945000f100181c1c00b100c8049002c15001d000300c800c0d510342c840c1c0c4518000351125001054a501100d03100c0e4103206800118000c81d014012000e43d80076210058100ca13070600c400c0c001c0c1c0300300440a96070059912040003607008144568030b4003542c401da501244403e903080c00c5c0d04040344823070050402882d80040800c100d0380c1194695049 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 715767482 1250 715766232 715766237
    0x150b1801050d02030106051207030e03120a140403080108011104030f0201110a0803090d0f0c020d1220010e060106051201050904060204050303030f0a0e0a051f09050d0c020103110304080a 82
    0x1180000100da50b402200c0c0300c9031000b4008000840c0c125040000340240001024001205a84222040302900e91801d034039a169082082100d4102404a0b105513125034001d8003c5900201c20700300c1d00e41720904407810350000b00500014040c07030000713018084030548600d40481c2005d095442e91942c0ba004880001d050045002c0480e01d40c0500340060181e442e08040a1500da103080c104080d295210b1088500004221b03400c0300066134041c1001daa09940c01070201260350301c2a5880310000106507107450280000c444112400310590922804400001c03030011800e041504c41a518080c4117070450424042d041c0300324240c141031030700300300d045070412240c081c2c43d5210340c14004000d00c51a004182c00d404000200700200c0400c1d08a14020160508204080c480d41110591590f10b02d4100800d2a00807981c1c00c06210010754072008142c2170740100091100c400e50b1007600e001c0d880710400012903000d00c101c4040d9031b00752080746000c040ac02038591071450b00e55900440303485180a40301c03d = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 715768732 1250 715767482 715767517
    0xa0b0a020a030b0907030605040501060302030c1204140d030f1503021e0f0a08060405071a1b0c0d050d08090a110607050c120a1104060302030303070c150c090801150b 73
    0x954500c20f402402518030301421809007070504900c010007601d0f2601445020380e06000001030007512a00c00c50303205500910303549061a212000c44030751401c01070b00640d200b02c06002e9048802a042c0086030900d103064070009041104850460207a80c0c100e9400c400040c0304800030401740e159480300c81004e106180b18054410225000540011000490242c110300c110301c2c0031800322000500180a180688202c800341769031451500300c03491001d101940942414440c40c00c3e014580702e0100840d120040540c0c2030100d606010a5035000c0c412810b48680e8452106400c810317422041d031513013000166001c0c2c410b400a50702c41000c1504510421070041600107690814080c040c410403081c1c010003851010011041010180da0340c003510b03010f99400c141116402d449141501c00d60040781c1d8090040c0d41940e0b00c240007941c0d04c000c1008252020302da907412a4a200c60a842020440c03070b20394480c6c071565418034070b50508441811a03034004000c455402400182e2010003660301100e1000c070b0202 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 715769982 1250 715768732 715768747
    0x222180501150812161e050f010c0e040b040f0e24090304121a0c1804060305101e020f03011a120115030e16060e0603070909021e0307020a020a05030a0b0a02 69
    0xd11885c1d03c901400010303004181d0034183d0310303802560f40b210303001c0d82c2102d50810018469608031211380c0750403004525008106111400c05800021038610014000500341c800c00103010250303581040c0d1601c0b45e800401700d038034106035240011750014100c0240d4011790b140c829030701a0350b17100742c1c02074001c80368502c1c9140c0100068030491810030761b100b80e0301c04598109642c042405400c0040d440c22826428000191642001d100c0d01d8100c82c0c20900a25450441c11401c500a010310210007246016170a802c40c900c0780c1900060034248081c40000c0e642e0361404840211044104100321414101003003001030200c116040c1a0554800c441007540701c110007401075004260310700303080d400c1c1d000d00890300c0c600c602c0034401c80040f10f80a81311003014041c030f0020001707988001c035000300100782ca0000034030035001580e0152006008117100348441c4184240403450700e4008940c0140143e00502c451070450901540c020001c1c2b50030740040c805500240c0c4c0e0443c803580000c0052811a50224422 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 715771232 1250 715769982 715770007
    0x6180f06050c0418050703050105030c060f0903030c0d090f0608010e16030209131b050c1c09030b0a0b190f0b0c100c0804030305090c0d0222180501150812 68
    0x1034008104507114130f03140a115601c1e00c1c02900003100c811001c00c0c900030000600d410041018240c1c20401091180760407100c2502d02400d421a500c1a60544020f21460030181010458400803100700d4403888900d525112400204200c103402070402c1010f0b84004109440d1024000c9410440d20402d641c0c80c851a035008800074014000c0580e404204580401010741150b03004400e0442e04811040c1c1192078140d00796110711500c028420a80d22080381540864840b154441844120340b501c4090284e0765103458040d25004daa6000005030382d6114207145280c039480c0d085008040c031140d981107514001d90034900b04418420410410310018071954407003414400b20b0140d044442d8108407011200c0d0004000c40710494007100828072f000b001c95410040055113480000b4001c181c011540c841d0303800c0c481c10500b03100d4800408041d20064000c00a800d008551030806072928034039244805040503425110090702481540c2c440c0716003400031a00c041000340c1e070001940c4496980b140c030040d40c2e = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 715772482 1250 715771232 715771237
    0x916060302090f1906021c0c1209030c15030b010e03190206040812191e050d020d06080105090c0d0b0103020f03120a020a031101052a130b040306180f06050c 69
    0x145502207403c000782c0001c82c092002c4c007019a00daa0342100c0c217401c807915603010941488403400d0040b0321443c100800080003002c02203a036194610b40701c00300a55964a05500c0d000f19000310040010441400203c07075450700c1056540b40303013464821061030000f40801d440d4062401105c0c1f550820080500c1551101e40c00c41d0004d0440030121104810303401000c442c2034101428901561184400c15100c06200d9105010252803c2c2c0c24107444002c09503003652035520070403101400c20b801380b20144100700580710301401021036400206180c58860240d509180ca40080740d0311031030381d20725580c01103180c000440c3e05407981510b0500000c807160340001c0c5080c000b03155a4200c01c50004070300c0181940401c1c6500610b20a4903006001c208030a14039003600d000b00c0345485009103804032030840201c05d8041105040100d02d900e4601050030b03c04140c031101d585c01080310200f00107400c20400c44144034002c92000d482101c102000c2040e503580c59401080000540f2041d11280450110344a0008 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 715773732 1250 715772482 715772509
    0x8011e0506070602071a010f0b1e0a0f02160305150703110c0312180c040b0103060f0b03160801051c11060d050a050a06050d0201030e1c090e091606030209 68
    0x10140e210ba480e49040f0000c0e52200100315400c1107505459800b5204003900c20707040c4d90000800c5071805060a600001075042001c000c4503844c9071801c913220081c0c4000007028040303c0b581d606541c490300f0301000b038038005100d61181c82c0c0c00e10400e0104007240c00814883e910940c40c0f407100c0d82c44d84950030110050140c038640d40d240000001036096030301000100801c0641c100c0c1c1d1410301960b94120342810300d04410f000035200d81d0010802c00e106445c10f6401454110380504000905945445a44030a0040c0b034000392584075000041c03148401402d41d600c010200c00c4d252020301d641c1060046520f40e40320a030305d20000c8600440301010810328680300c400501020704065101da81c901d8a85020381415a04042e400d407800011036420303031041c080c4400ba01c0014001400c11102c0c0d600440c018401c40b0fa00111502810030f0f818011004440145005425507032111005030038641142d41100015040c40e44075403080b54406071000c80980c85400b1542c1074200140c5507100306c070100c2c80c1c0011801 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 715774982 1250 715773732 715773739
    0x1b05030708030a0e01090b070b04170c0307020108130c0e192c0a020325080d0e0306150102210d050907150c0b010302060a0c051507031b08011e05 64
    0xe40400c1c1d603400040508207869255650140c9550601c0040d18400864054091100401c000341c001240401e440d1541140c850484030382442e8840d0a0000da0b50066000303031111313800024510080d5a804590603401503000c3d00c203445003104581c0c135010045a01d100c0c0c0050034502e2400100803071800740e001c0301d00f400401c00501606120000d01c414035201c1c2c445804141c144182c2041140b0380000380303484119070240c01803410442011503046d000c0f06c2d241034040d8902d403404021480380c40c14003c441c3e503000e49440380041623000b05d04050400c0c00081451402519400143d0402c0ea40001d420000000a10f24200b180d1004d030b010f02c50340d12070444480742540c1400e040c8207a04400050010484107118017008102804807400c4a414109490182c80621910018409403910500400d8030307004c1420102120180340d030350300e03040c21711581600b8507800082c82040380da03d07050700612901d0821841844210340140c500908483d00c1809503a5010246000c5100b0781109084c0d604040c0000a = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 715776232 1250 715774982 715774993
    0x507050303090c010f0201020c0601060311040503102f0a0507030c0b040f1506180213080601060306031a091b1c0b0a0f0506011b1b0b0304020301050c0c0a1b0503 71
    0x3030503040c0d03245804070032280095070764624464074601c184250760702c0c080100054400cad64a8003000700d001c0c150031080f50340c45000c00c02c0005181d0358100705100000e00c50900204000c01441e44010522081440644213004010319007000d10010707000b00e0384498400d090164440b481d600301200c18401690000f84404680d130b050005210400d031004150b2403181d6a140820410405854203860461107803554019030300302d400340103140ea82c01030003010040500c4003280310703512000341c0d00c0d00000b03034428404244c1e40c100038014001d18440010350b50340c044001c2000d505005070419620031400c01c454440001140d420786295883c8607008801801d403501098600c1030604008020090980e100d88100e85805c6418070f03540013034040c0910500b4141c444071101101c004009071030040074a0101c03170701000c6a030031207500500c000d511805040314010040c0c4a18007841458212100134001102c2c4903402c1c861080d4290300040c00345d100517400f0000c4c244034094400800d80c0c1c11015049640d040c0101c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 715777482 1250 715776232 715776241
    0xa090e04030e040e03090307140d0c0e150301090b0109090609050304140306010503060f1b09041a131a0f060c060901150e070504061b120809070b030c0313030507050303 74
    0x30038507002c8030340c0c001c0303401300001d110b4406000d0341da210f1004ca498054102c80781c2040104001c0c40b40040201c406400d52441e200d2950304c000080704284c02c5608408160b206000c81d0082c903c100c40b000520540007000801e54940b640340f10403c0510400c0c1c002c41d1100f014400700b000640048044076800b6044a0315192075680c1e4803212941c648056002c6e1040312700000701841c001a81030b01a10a0040d90023250312440d0710304c1c00081c501c02c51121012400c021840007038a41c2d2060707181d44050f001048104040c500100800c5121b0742c0000b04149003803051040202a40d07003100c50118004031170507650071407001d0206840d80a640c00d0018280505810000304500c1900300e84017135100103405d00402a250044001403040c00d440070f100140003440b06024080c0205d541802d440c0d00d0450701f120000c81603940c0350400055003903100006110205000c1c210004002d120040c0680d0000c050030b40c60040940aa613000050000c2100403140c402d110906015508031042c094201c42a00c1e5680381 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 715778732 1250 715777482 715777487
    0x190603060c030b0301060e01030308071806091a031014040f02030103060506040c0c20121006170f1510050604080304081b0f01080403020f030711030105010b090a0303050a090e0403 79
    0x140c080d00c030110f410704002d00064034040c8035a106450346106180c0d12a420350710202c414044c01090001403010b1380d054000c0d4000da024140004003841c0d5542d606450078003901840c4081c164038210803810050051010301c0031020f540805482a030540c11140707004c00c00c0010040c0100d618241241d510000c000300c2440f040d908024412982582c0c103004c1045480380c01c0720510f110150140030700403401250403a002c0d0020260b00b03501001007034807d0f0440c0c5042502e0404140707200b80400e90750740e200108015103006014401074241c1d035015080d4000010745094660702060441e14141400100040041c03007c108210301502d40548046d448945410b405030766a0b00501070190240b00e804181248083c42c0540072101880240a0644001c40000152951b10015000302d042d40101d110b007847c00f00c1c0404c05803a285002d0f4900300da603800c15200b40f60031120180c001b0010100108000025034a41c14440e00071170b941860055507608141004682044280d00701d406008885001d2006155 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 715779982 1250 715778732 715778741
    0x501021b01200c03160b03010b0c010207060507260603030706020c01020f0c160509220201020a020603070e0405090c01050418240302012705040e031b1e0a1a19060306 73
    0x10010f078111207503000e4022405c68241c0b203501c108015080b04000600881c02d588015000c078a102c80009400c0c00d2441c1d4072041a9802203071179100181e01e4103600040d0103000b2800d07007400036250310200340c0e505007a00429268401d002c00030b030056400064a80703000f030702541161030070400641525217a68140351955100c450b142403824008155940116091800e52003c0d4000c004d034000011111088002d4000c08a80c1184164198066070701d6000143e2511070086114290940e522640c03070031010300300802c40d01c0141a6401c2d90b80407180038195640c00404440540e110421a4002001c3c0e042c14000074000c00580110580d814282d030f04510394074181c050741903e01c01d885440780401d007144100b4a040d182105603844014922003040303030b401e09900090000840d401564a00041400780380404c0c800b040c0c8503800303a80300940d008400112503900c81540407450700900602c80c40f60b02c2c1c1041c0014036000004900c1080c10100b00d00a0150b183e40c4642c00900c80c00b1700060356130f41044001413 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 715781232 1250 715779982 715780003
    0x140c0a120816050a020a030c05010b040c031e05090a0807172b020a0905121908030919030f0e2d0a140310110f031006020c010302040501021b0120 64
    0x710588203075800503c1c015801c0e01c0e0310300c031158002e0001d4a4240c4044030300d28140700082d21155030710070341040f00f501c0d540180e039982c9009403008141c5945503008000208070702404080018a00001c0c007420351030104265000941066107070b910340340d00e0f080c1003000c0810001610f140340b40c0043c0c228000341604840d040d0f80c00040315410000c0441c44101d509034031469503103000291180a051000d40750030029000005038035021240140801640c000b02518441c8080e40c2014021007000fa4045040000884441100741c07048030780003456a02400942c41c0c0b134081d5007488042041134025485221085030001440d42844041c15081030b85100d82c1d05280943c40d004403c0450042241a4100d400e5526200084c008082c03c0208060b0709005000346500500d25134420842c00003640d401c031001d036010700f0a9004110b03250346021000f030314000303107034030210305060040c4020095680c02007012566400550040101092010012900566403500408040c0a110400002e040000825080e030703 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 715782482 1250 715781232 715781251
    0xf070b0f0f0703080f0f040f0201030c030209060c0a051c05040b0a02150a05040302010506010e0607060b0d0204090302300729100815040507170a0c0b0702090f07140c0a1208 76
    0x5a180c0074000304c0c6c40030007260041c010000d140c1c140001035210380e012150005042c07034010b0170280c42e4800140031768040a111400f50f0301c041818024481e090003013081d0100140340064091000342e2000d045801031744a000711540001c11b800e40c000d802404006050108c01050541e94609014074000801081d581500150718010020f0410350042e102405034a40003001181010555035400015050f0350024a4003c029403120390016200c5000781e82440c0d101e600034003081c1d604484065046008110002809020951100c1300801868210741e14580c2009840d0040c001d0784e032211b994041a031100b030401c51119010130400702680c0c140036003906c421200341c0d41070f62108441c0d0041d280c0d0039503000d0b015410458041041c05121a059100b560805058440b02d180da61a2000d0784400d561213441046400100101146840072100350706c00383c80e4142941a05120380002d044101e0b81822401e10300300081c1c5400341e40e0040207016911076010500c15200031403404000c10703240c002c3d2840080c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 715783732 1250 715782482 715782511
    0x512150106050c1528091401060e0705071a0604020909012c060a06200d09090c171603022205040c1b030c02220c020c01020f070b0f0f070308 62
    0xc07120440902c28003c4642105000c0c45811011a08811303000e17142c007448059507144510300c0050001b280c54034281003440300004100e45802210350461030001e02200030008100010380000e20100340c6581400c40d9410903e00680e02c0700b0100b0020712074100d42039813200502000050704118840d00c911030403030300d4080c41c00c500716407021350500e0042559143e511500740b040a02619100315044280c00080b203820010300e220848940b03081c0103115107910000f0391888018001c02005002d2021028034a14000c2d8104c0c800c65000b10302d159024010400058500e00246241ea200381c058a15196183c0c5116804840a6480408051092184d94015400e060f0b030305a1003400350000c44a0882c103030440c1150101c0340c4d58202c500c00070518080764041030307030007007903550488510552180151080e000140c0014402000e80b0b008100c0341c5507411984440c54082c156a0040f0b1003800311441d1040389600c41d000c03141000c3c007038080c12040441906000c0b03500018140d110322000c2c000d203000301a03141c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 715784982 1250 715783732 715783753
    0x50a020f160c0f030201120b03030f03041416050105071218080a1505061309061503051e0304151101020c01051009110703050a0516060515011404050a0512150106050c 73
    0x208090740d40d04c0080e020848034a400d0240c0302807904400322040b0002d00f0b0b2441c15148171090003041c1c00a54007030f501c44991010940c00d00c80c0402100400c80039035141d012040d0b25210000700b683c41254802800e80c02d11004a142803401041d503454280141105c0d500320644840b01150381f03003806141600c90485502d4a8140d00f1200e105d650301445020b408407640d01003140224019240c0e0745412100169108450a44004040049800345200354003810402d40300c0c00f40400100804100c05a0359041017100304002c05258900019135580d03410450082501c001c00d8900a0140c00d034010b40c59400d1100b0043c0c907a018295140036111410403c00c00d8200404020700c40e4001c191000303001c42e00400044002e1070164020b442b00e00c008005401c5c075001a580c401e000d540c802d4a901084c090a82c039001a603682048102c0304010080b05d011741490300c0c140c0020740e40400b501c24540101c0c0d07171521038408400c00780034070f0b00921092500031099503510030004006074040955110207000d0040001d = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 715786232 1250 715784982 715784999
    0x3031404031b050a0c1d0f0c0a0e0109030f0506090d0201110406030515121b180402090405030409020f04170a0506010e0a020d091406012106050a020f160c 68
    0x6409141c050b0340390260211a60002984103030b402005030707840c0c400c0e005240c00003014550705c0009070041654804000400b82100d18512002800b405004482e480401001c3d441200035207500407002d01d40114800050741c01681c056080d0f81018000b40c858540395424401e0004281d80110700941c100c4c2c00f05800008101d00300c40034000d8032a10940100003c01002d48a50045a000210007188501c152605c1000600d107401c847e01990143c2c03c1b2280c0c04030140070600d90140e10340d00c1690308210322041603140c1d420181c4002c1c0f009104442e54000300b02404010000c2d02e000d0902540300f1540c40e5458074860346660424803234031104038403c1d110b07042d19041c04601c0c0004540d20200a1510381d00f020303009560800003e00d2851040e500348041d041c80c1d4018004c1e0f60001d03024010580d8858a0f141c030007400c2010503003090784000703c5da00002c082c040303844001c034030a03680144000850f42c5403025908040d00c2403410308582d1520128540d0304a030340a43c00240c0c00b900c91103113074009036500c0007074 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 715787482 1250 715786232 715786271
    0xf051002030304061d01020a02061603021317011e0504151407081503070b041712030708100e01060206060a062f0f030a180605160201030c020f060106020a0303 70
    0x15200180c00c244049400240c2035041131103158000c00050b02d09400e0700c0042400c80e00400203210040e031201e070a0260b07140d507014694040d01d0003854150319000d4002420a0310f0031052040d07000070030484101c014080300a512098a59070021803070540f41001080c2a00608010b6409980142410607030031602a501e20650810241c4004071160950307a801058404480c01020b0100040321000800c0c030565041c07090360b0150840b081c0b01622a0704240c0080f101c05041d042d00131003030b0f0140380c121301540ea811068075402095450209180d6070b92000455041030b05900502c04e0101e801c00120702c2c29004607026118900c1039a04141c4680c0d10305c001c40f4502c541c8121010303019001c990189055a031800002450407002040b5107031482903003c164695407041e04403000091240038500c03190f045c04c500030300c0101480c0c80d1260a10030032101410710700d281c040700203040c03503502c2e508107480d00d000340f0840c4110161481610415030351100040d44820698108400107032030312021801080c90f4151 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 715788732 1250 715787482 715787509
    0xe0303040905040b100905101202030718021e0903030910031b0801090e06150d060e0f0a151505040b120a03031e05100510050d0c0f080105030c0906150d0e01060f05 72
    0x141d4040381c0c81c1c90420b100c0b4010270f05050340c05001d943c1000c1403e180912911210801c04180140c0d21030380000122000c0498000c09030903190204260101da99001081d00d403115801c40d610010fa43c1807040540c010320314801c10310401d8003152090040c80750070031034035412500305400c140030041b900217030382c4e07283d803003c84076500610181444403205050040030704071801e100e003400041380001000c001d031030401003030384e01c0100340c1c0050a04000c12842d403440f230b20b12154914043c40003c0c00360030030042018141c040c0070f003d00e0f580d445100e0180d54042d90801c16010701c80070707a2440009401d00401a1890b09161451808000d20200c0034407554444c0d82d204065440303502ca042428075003003104545a1251160811070140803000005c0024032484040142c1500d80ba030044000c181d001c0c0010105a00581c0309070410000707071100383c94039007049078018400c8403a00c0f40101444105480343c040c0c4c44402082910b000c3c2140301d4007234154045010744103000b60140040d60f6030301c208584d0015512 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 715789982 1250 715788732 715788751
    0xf071d070e030d230c0a050c10080106080618090a0605010f2106090c0e0603010f060e040f05070f030308090f0106050319060618020307030f1b0e0303040905040b100905 74
    0x1000a485440307244041030401007051032485555100640300300301c0d0084518880c140c0c000c6c035900410402c0130001380b0200c0400b59040070003104000000780c006e400500c07465092051070b000080559949640019200320000103440c00350900308442a51485683c0c4110348480c0b4040000c1a056841d00c00c0e181280e20100b900e0b100b0f815501040c0c0440502c144046443e0380e120f090038800189100c10450207025064105442803070400101030945a0315412a034402e898408140010400408443da010381c120010000360700261070103038038014581c1d21a00c809840090007104159000b02480e014180f10000c5400b1450321081707090803141c8038802c0c00c0d8568880b018021102568030717040d00f8183c2c01942d00003056aa03410b020246110042600e00301345d0b03800410881c08a4141c401d40d000d20004030400c00420307140440100070103100304403103800d201c3c60296520043d9407c004403009880b00c800e00340100e003024540072402c55810341e101100c50b4486a004a10510f061041034840c0c4c1941 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 715791232 1250 715789982 715789993
    0x30304140415050303071505250c02010908030307090807050a1d0c04090c0302070b130b0112050708070603020c0609061b0309010209120c040c02060910020c0f071d070e03 75
    0xc4042000a2900450440c040b2084902c000707642e9400380f024003035140c003034440c160000d50801c084104840d40103040e405a0800002204000681c01c035032200d2042480c1007840c82c08080780010385103d1016840494203105c0002005252540711480204a5841c002181d03030440c0c0356020001c04c0310403400f9011900e100c07031125448541040458075007141c02c0115040c505a100d2100d08113032001041448042500059080c0c200446030140551080d0602d02e0307500305290340e0b82c41c05440f0206120b144600891245e106050060a004990041940710205c80c502a610360010700030303400132040c2c8906405a0390000710310200100d40184510990114504e080761604e00b00d903001d4201600d11000d81d903081c00341c0c00d50340d1a81d4111082c10b9040c48014001304100b6400c12040d40e44100d10f400443d0404d42c240000030300300083c0702040c2c02440074003503100c01805820614248800f01e2040c01d510519100040c01d401e404560428680d801606076516038880d601a58103045c2030100701c1d0181d120 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 715792482 1250 715791232 715791269
    0x1050711040b01090f030f0308011706040204020c012702031c0801050105070c05210f2121010b070302060a0e101a0604180e15071d100e0f030304 64
    0xb54000380c0500414142400056200c102c3c0352844255604202c1d0820702c01401e0a06268000c28800d00420f043c0728016580144011032685810340548000e004580104040005200a40103080c04c440d41c130a00c070411404d809c100c0c1a040e80c0101c0242d01078028144460099645851201c4070020301d0340f6081d490b40d28020046036035511407081520b04e02d15200004c0751683e900c15070410300c1d0351068040d48150720136a9503541401c000a00040e025408461413a00448010055041903d2518402034603000da6442c2030841c1c103e00c0154107942d42d008000070135210445005400720b00c0c040c0d0300b211000c1e980c2140f410111040c91003035500c694820b05054900019680211320305130a100340302100102e0038004502686c01c9a002408004100500d141820206103d10a108000d040040907409101281c00c11480e40140144d4100490101c5c0500042c2051105400c05440a40440300d84c0e05145402031035078440e54082071041500f04410002458000305890550f40c44074000d06003c2d04 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 715793732 1250 715792482 715792489
    0x7090b030604062105121306080a06170607020c0306100306200a02100e19080313150f0b0d050709150906060504030203060f01080303010b21090c0a0501050711 70
    0x1000741180e074480c0d01c070b650100d01a2400045803038249482c0703128041031002850001c1c00c1c140700503000310410740140055000c03030340e54242d4002107503800e080840480d151212a080540410b8000c0c1c0c2c126842111324404007080007074500d100c0c40c1c0e44c0c0c0c02c0c0e40b0039503907003820140c40340300c1a240080c41c203003a4001480461500d03403210100d40c030741212a10016520818400c0b4981040c41d440004d60481a2406101701941c001c01881c1c00d14035025205080040e282041c816402d500c0103011100044006520442d10410007040c00d604050642ea020040c03074100c501503c1030403666503550b404c01080c0c98a03420301100614802e41e001e40502600d508100c03c61000b804400101e90640340040310010b801d07109445440c000c0d04403542d0752a502c0b07040d0b0040c5854040058642089194030034010840520040305a906582c0241c0c8484d584482071801c89000c01312071800d01c014100d0715001c0c8a41c15034006444d10354004196202540166140019a01e0340900000600400030010b640c100d20728 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 715794982 1250 715793732 715793737
    0x90b0604180f05180f0c09040f03021504080d0b01020f0d050c0109020a08010207060c050304121b080d1a01050906090909150115140a0c0609080f0d1a040507090b 71
    0x1882400041070150040e4200c299107043c0d504d840c0d40892824440740f5100107120a00d002e036a0440105450b0408402080425500810150050302035102141c2018401d200c0c0000d005046883c0c810141054209590503510149007099401d1511884180b507500121702000d00c014032902070031380300c070382100c094560341c2c030821100d0728956a500f46400141e0703c1b0200d02024100010005031208918580f660031915070056841c244201403040100049408400400600e00d0f80350406020050407282e031841c10205030001c00d2948003003411840c0311a580c0c800071000703820900e81070f41440300c440190f41900c40d01e00302c40d403c0b800401c440540303410045074468101940704220780140700d505005003c1480c0a80045a40d410100c4c213522589a0021260f03000c400764032011464501d50507030140c4003480c080e4004022a4540c3c3c144001d00001c3c070b088d54524010500da05540d254100c02c0040101103480f03d9070890300d2200009039007810709201c0c0a100b1251500c82007481820800d1020058 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 715796232 1250 715794982 715795019
    0x306131404031805120307060e0c0901090e16030302010c020c1e060f0909041406011e14040e0f070915050d141006060e090601020a0308160903140313090b0604 70
    0x200041000155505c83d050008001d000c240046c54135085946880310666081c0c0811350080d40c004400903a15903a11040c8904641401c40c0008100c88134400690030031111200607000c00007944000024560190010740b09014194250388100d01c842c401c020250007154141018040101c0c100e10182c2400d400816030302107072242c0d00b4203100341500042d800d070b10100c404441d007602003240b88040c40e20030048140500001c02c07100200007a80f0801560040c031074443c00200c0d4500c120301d030420303880d598082170103400014261100d4900c604003403640c0c3c01c8140700e100b0005160524038440c821450a0100c150340004013002c14101d51611102042000700b40d0144850168520b6080c00000510940d00103180d80d4a58902207840c55040200e00c420050103241503400c00744068000070b0740725403a03951008a5002081000d1b14a000440c0e03800354640006100b1a010440c0d084032007400000390103025641c580c22401161540000300a036074071600a190400000d01050084c81162202c00649 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 715797482 1250 715796232 715796267
    0x30e071206020f0721030b0603042003071e0b190302030403021f05040b07020303040b0a0c1b051005010f060804061e020d050f13050a11180a02030613140403 69
    0x2c01104200c019140d511880045404107124240c5c01c0c54050718000e28550142c1c10b040404c604008200403c40c1440010300007405e04580920155000004c641e00103468a00542140c544c16120200383c260b4030a03202031850f540740c0d500300c0020300040e01800c0300d08040012880625a44c03065900745c0c065000074100700c095015200010113a03820819107410611000e19002c105c0341081c0c1460486694083c10002c1190010010000410401800c00c0d07000f038036034240014042907000e8201d071401402c2a20400581c1a0b00e1045e0a120000984d00f2180c0c0140e00d0811444c0d070780c0c40c01d41d444003e061054201080110b800a404661141e0129003002d2888a9010004070801d02100403640402c8915240f40e40d21800d01000400440449074001b1110304a084610420348550383c0d81c00c00309400410a03400032480406035125000c00c006032014500d091856070800b1480b44d006034000326811405600c00118189520016000e0038201000701007240c0ea45d91a141c030111410072102001c41c40d03 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 715798732 1250 715797482 715797487
    0x92706190605150a140c0c04110a08130c05030d0206010905010501050c1e01021612030b0910090207020613080a14070612230709050a05041103060d0f02210607030e07120602 76
    0xb11240c5c800014000400078001800c03076602c0c0b07001008102c6515603480001c1a07000d1024a207800c3e0002c4102c1c3e00455010407a001d000d4403880c2101011304140c22458050194481224a8540004040c0e040c0c5590b40c00611880c2c1e25800111203500545807509015804844030f003843d0030700054070f42440c01500300050b00e045152a0600748061ba4603034102c41c2d809000c00c04800540c2d161060b80c4144004a418080c3d070b0a112081e80c051150301d00600580c1a80013484400b103590700380484a185c008203005019140e595851a80c03504403060082d1001914619007204583c400b04143c8241e95203a1103506031a2503848480c001440d03c0b00ca007400501d6024110302501c0d0345040703000c0c80f50300700e81d80303080100c1c1c00e14041c00030b00c1d0801d50145000b43c0c205020b58107401e0090b426254050300c140e550b022205c1c8282860a0001c0c618500650080503024120320398801c400da100c4403142e0644121007086d26180c1c011030840d040d40003644619040f441040c07110b486041c40c41e0214902841c2c000d0b0 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 715799982 1250 715798732 715798757
    0x2030f010f0e06061002330f090606010c080d0b180c04030308160203250506010b1903090c0603050c070f1a0f090a0b09070308030f070f021605092706190605150a 71
    0x50b500340180c178481c094608d00000c21406031810032619030b000c4001e1820b542c90b81c40c0c035a40c824440c01036468480090b91244c2200e00151900900404242d824003519900c6042c8941121050350207400250005040100003c082403036180010726503441540c01545000d030500d05440c20200b580109060480d100b10700d080200780b04008250213046010f402642c0d6110015900c1d1031442e030f1860141c14107043c58800c1010451401c0c5d46422180c5504022880b5039480002c101503128860009000c4901d000b40401030014220000e800500820b07010405900c4062424051031002c64001d411541f01740b101c580003031601c80300796030440b80300000c6504003522035a44103400e40003141e081ca00310b5460f0040010142c0d00c060300396104c00483c005403582c0c6001c8402d01490700800e0081c103010320740e0500030036100c4142101c0b0304003041d00e40b00c40b032101056884951351950019503801420f039808074100e916140d5030b885840c040315002064021582400c011000180e0001c0c00d299050019801c10107 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 715801232 1250 715799982 715800073
    0x402091005061c150e0c03090304030f030e01020606151602150a271a07150c021506060306011b230d020f210702030f010f0e06061002 59
    0x1455402007a1000d03480552038100f440080303414000b81c443c1140c44a076001c100031091045032a82040107200030751366070303507071000c0061039445250300081020602028040a00d40d011841c44000103003642951040d8807900d0800c80c1c40d001c00016480052020072413200c441441680a00b05644041c1c8041040c60640200b0056500004051804544440d40d000301045801890441034400188408080c2c0c0c184800708034528104e02308001c3e1044000341c910700b800094040800651002d0314280700d00ea16101d070003900c482c820019000c3c1c50201a0200d5400d281000c1a80d20070300c3c043c0d5544012032860080072a40c41001076098940340b00c200ca200348403401200c3e02440c1200203400400d00b20f5502c8031b00900c0c04103a64a0320816030807080e502c0d03501d019107a01541c2a4494086255202c50701400003a040404000d040c084d150300e0301011151510580e001116000489429a241680d401013848160007202d8240001030f00318004c1a90607800d0101a040c40c00c03641c1c48805131828404085 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 715802482 1250 715801232 715801237
    0x1b05040605093007080a05030909100905010f05030f210f09031608120403241e060f0e0115031e110706180c0314030f070c090b0105070b040209100506 66
    0x2486450901ca144648243e100b040072100a0444600030240441b10391038203502c078020760300000d100d81960301c089500061030f000448003806060400300030950751a0358002c550042445800d009001c5c100081d04e605401103481600710320041e080003915920130107002c0040d404107084a04012040c000c02104e80c0b02046901e90f2103440710b4218501600b0078651a15210441d82050303442c2001700028000035000b44c4000c590100c2014a100100307603418104400b6000020103100108441202d10007206515007100048900390107035203140b0780c0c49012880034164240030300b248140001c1d01034507449220b507000d40c1c00078580004009002047c40503801c2514021410040301e442c0104482d4140801d52184588210312070310b0400e000c4005a031184034041c0c29110240c03044403c0210302c100040280100d802e800310315800183d860308a85071030050142c0038052140700d1880c0401100d01c41d4010400c641003d03401c46840c2030295203503030030401600b0b4020121401034090010004007915084003 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 715803732 1250 715802482 715802539
    0x303020c0106090f14010b0310210209040302010c081f0515130305010b091003030807080703150f031505010503030706020a090b04170d03060b090402130f0314011b0504060509 77
    0x180800e4104681d03085c24040c6806810041046ca01001800350391051044044200c400c0c0380795031428607405a801030b021005844c00650400c01e0001000200741d81948400c80b5a03809441e60300e0181c5503104034a600b200c02c00c40c0e07000c9410b145842070015103407208502e541201d007000348628280f141001211a10410791040311a44c0d15900b8451070780c5001c10455901292840c020300b14079180d0b4500900b00807001d01444d05008842c00401c01152191300f0400b014211142c0501081e5521034098620800500c415105003101c84840c0d80ca90600c0c0c00340c00e04a0380e0040045050000750385642c6c000303500142c1448140400ca01000074045400800f810007480c610907065904205810301c613040c000d00000140030585007880034403480151201350b03100901c05a0700103896080c459201e8181000c60303081200c0b00c4d1500c01c000410440014601c40040030307244028404103000700d40d03d03860b102c1d11184180100e14240014481544104080e14002e8401020b081c0c1080003500d812449211214 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 715804982 1250 715803732 715803761
    0x3210307080105180a020a2a02010809031303080a11070f0510030c09140406050d08031f0f03060c030f0603150b06040e010b0307110f010914190303020c010609 70
    0x41101407604211024014481501c0098a401c041103007611a594010709200c0e07095030103d42d0011007445141c0d815620a0211004070b4090038441c1118241e1001d15005c9002030b10600014241c0034021098132401e482d80901c103850b140c11030b603071500a50030003040d0004011554800c1c4940d0700741044850004c00404d0324000350030b81008207204242c7c00c02900314090600381011081c0481d0300a0a0f0740c21104403510303090914540717000150280480760311241c1d00850b031081180522105000442c003520500b000228a5003a204850204032498403517540c0e10000240100041540f5030410141c5108a02c2e00041030000304901d102120419003043e074545c014520103000c0c00d92240308448002d00101c5501d4140382ca0b0440c204070109050140981d00140800170401140c09034102030100c001c2c000c00d54840384c43c801000e50007041c0201c02510070404c2c14260400001c1c010a0380e0420124007000150741844948040d4082d60012074101d40c90366807150300044051702813207a15208000c04 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 715806232 1250 715804982 715804987
    0x8030f060108070c230a050a0b1005150301050609010306030b090708010f141609120f0b0601050405060d271a06040b031902030703141e0303060a060e0321 68
    0x940010b041581c01000c560510100000c604080340c07803440160304000505503505110540a0540c0d424000710707060007403240c03081071004800c20000078000c910491080d4803001d0b107e5640c0e410411094400c00540480b03440810051005007000001004030010605012074034541c2e035512410310881c119003030035080c0c00405041c040340c2c02c02e0041c1e480750200380c0f90600011036849040610b004000d00403c07011240c22600d0201180100280030060004840380704514001c1e04054480c3c40d00d005d800c0766a0502c91001520660291050710709840018242604000d41c00c40c11100a202010340e0425212a0034422502840301a0f201c1d242e0074401c1c44000c1e12415100060403a03508054501d91140d070820112035859140010100380b600c124490b46aa52902c50000c01c1c1490400d40018181c00ea949040c8845103100084810490680d404445107089280520580303078001a2441c1c1d5211150002c2003180902c82d11400c0c24144004090701c40166890201040b018034201c00c0c41c481a401 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 715807482 1250 715806232 715806241
    0x90609060f0a021213180e160f060503100b130510030e011a090c0315090703093f02012304020a060807140a051e180604230d08030f 58
    0x184240c4c40141c41101d0554113243c0104502c02c4640300d60f000c1c9009014007000301000f184400d8004c2c6007002980401d4491100c0703466000c00e1004603500a0b00b051341031140700000d19034031880c21a4030400314412401c0080b4248200091140d02001039034402c11041c000221b0242c1c0e5092000d4103004440d180094100441280c550966911075211074404030b080c244c0c0b414644428002030350054082c0045030b503e031f40d151101e61012124456080d0884119010003100700c4d00742d405001400d0007108001800c031403890500051f00702180300244012000c00c10f1b20b500d00100d12031848500c14900010883c0b47c41c4040302d0b802c45000c06800f580c8503420805000550520840c0e40f40546030354034000305540707040304010b0603581101170301000c2081c0c001880794650784a0070980718950781c020340b01d0111040d0801401c1982c2c110b00b940011100744135404a0040c501441110101d4007008440c401414a603458a482c00500c1c460707181c0c0060000c00041d00090300d0740004c502c51112034100c203501d07050 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 715808732 1250 715807482 715807487
    0x3021e0607030e190f080415020c0a21080a030b09100f0e090303130201110a0606091113090207050102090918060c160209060a0906060314090313030305090609060f0a 73
    0x42810748100c0c00c0c4c00480410a02c000c00c40c1603854907640243c02c103007a003891450007402c6880307a070344881c503801171003424135403541c0c1d001c14428020701088a0205a90b43c480700041d0510f4600503d01c007030290680d42c004006416540034202c03485d264200000d00c030f031403903022401c00c240480b0150491115040184060049241c504001c0c01d60903c011000b4a0440c901560324070002e424068141c004102c603000316840b840c840d00c20b161142c015076140017418944000940326074080c03041424180911502010008400d4135188000c0d044014400c1c1d240c81c0340f02000754003803102a90995000c000c020856210b00624a00a4049002401c25055041b40680c24504041c1c624030100a00704403126000351001d141d0508203404940c0c001817078883d90300281c8410520703400031044c00d082110016486416610854100c4189204140313140c0d244d00c6440d84900c501c03c101400314141500605c0032900ca440502081240640010f1034411b1200008429403c5881c4180031181d0010f030b070210440c0d = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 715809982 1250 715808732 715808741
    0x1f050d0608160e070c030503040c0b0706051006020c010c0f15020a05070b0709060903060203060a0e16030e06071e05090a03150b040905060a0b01121a120f0d0c03021e060703 76
    0x210395110f6011400c01e82c0009210000202015040140c0030000c901402141000b40c4000d02c40c000c041c070341e62416450014050301d8101ca07055020220309100203011030000c40c503402d035490141e6520440740e5041d940c042c00804446004d5482c80680111410420754034802425100007685034180c6618241c500b814040034006d105404228000c0d03000c00065402004240c1500e500000152300c07540c0d104003294164040b0b5010300d0060201e4400e101425a400350a0302003100103690901641c4864503105075202010b44107800080e03d050742d070707680d02110741340c0f580100bc1e0345240c01481e0901c204006001c540c000e4000345e6104441008800c11700c0e00d60701c41c2c01201c00003520284648001900c0700d41c2c40e110001c01185440752612281c00d00c0340c0c4114800e124501080104014001c138014101c02e8810402d8183d41c0101c900c1260b10070301500006441440074180c800505110004140031104a04c0c0cc241c00c506602c070f060f43c1c600041d29038507002038107208400700901d154038202c2401001d69 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 715811232 1250 715809982 715809989
    0xf020c0a03051606020d0801230a0e0a0e0a110103090212030d060f09090f08160c030b0105040b01020a110d0f0206120f070c1a0c0408070906140f1f050d060816 70
    0x5601c01d0000143c0550050540b604603407015904002e8036014003018419042c4034480301707030b203d01c1c2b004001c120690010100f42c0105d0802c4010084c60080307600303450782d07103658100141030191000c031046400e40c0305e1b40060807401c1c4064011305034004101a0301e4a19044a680c4100c2c41e40c54000c2400030f85540102d00c3d0080408a87c280480c0c4540c1d01c441c00705e5aa0a54080c0400d0800106011117138402d20601d00100c1d444910620082da407810714121102080c0107452160741800c2503983d056200203248504550004201500f44040c0010000c005074130040842d00c060001046030f000d6a20036000e455030f071001442140892403c4008000581d00042c101014001c280c00b00ca0301044071910072071450075444190b01d18507210070f000c0b41c440f0b000b45d43c050300180c86a1800898010380c907420640480d5214881c0810b00383c2c101c010030a50703c4204840c2c58008801200d440c074242c0290040805042c100c1c02c00743d00d4641028442400e8404a0b0072010084d400720b4001e110110585080d003005 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 715812482 1250 715811232 715811237
    0x903061905061f2708030c0d020102040303120905100912271a07060e10140105100507060b12070602100903020712060e01020415030506120705010f020c0a03051606 72
    0x3400f081200002c28005506071141080f085100b0b042034085112005141d401d80c040007005415a20160656070350320000d030032050342c09000000c0030340a005000b83c401f03695244c2c5842030191190390408004054032203099806200d44050031640150700c1c400d60120901910f01c9084280c00e00c600602007280403842c41d803e0b0700d8006583d0b010310482c01d40400a0703502c40d4400c030f43c002c1680180b101d0580a00c0e0390142c64585405400385440c07400041b030440680d0099014030940000b5a0700d0035070080c00340b0400d500112801c946601d8548101c0080007102d00c581030004e8030405250114201c1000c201c2d43e4106684507400c03c0c0500c40d010030550800c50410300042c0001542c41e5070081d2200b02074403502079241e0b50864580100140740d04100450444038000b151181d507039094203011200d075404001d0100b032401000c6401e9081c18403201c0000003681c001411070915000044440100c0d00e00781c0340c214001c568030782c0501d50311101010015401007000b0500f080000c1010301c0842d40742e51280b0306 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 715813732 1250 715812482 715812499
    0xb04030801050f10020d050a0c020622140d080903010f09140f06040819140d1a06070309031113050c0702030f0304030b01350703050705031b060f090306190506 70
    0x1000e80d001600c0e01b400403c81c6005a1030340c0c0b81d424103841024403150000d6220f600825089080840e407155040c1a0300111032840c5030325519090340c41654a01400186c112102c3c4d03200e1400b14820a00034900d40c24041c4c0002101d0031100080000ca51110400700c800c000240e010200f080c1d82000f50418407018003001e44243d00f400c1c1e4a010180c030a080351180b442041e080d035103108900455544291100c0c04180e00d80c0c4054803040040100448001103a4900e0300c08250380726400c02d423068500150381a103070020082d00719100d0340120034000c040701da802541d0b1907800c840f88400d4000c55015240e09109191a07206510405081c049190030801d400e0f070003444100003140101070400c0c1140c00c0002841c10a50044c00c04140031001c0e1600c0c2040da030700b4903c864860000014111003101c6c041d006480c0f0f016240c20400d904d484405000c401c14030140aa500100c2c90014018020032203d4a202e80c50302c0284d0020904008007102c115007641c400401912030154039000c2d20794400d204071382100e03 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 715814982 1250 715813732 715813759
    0x180b0d0b03010b1905040c031b02030a08010e01050d0b15040c080109050c030f071b1a190c02120f090d20100c03120f110c1b0303030718030b04030801050f 68
    0x90240c45c428544901c2e21424903461030b9000b40e108000a02d52241c5980072598000f0001c1e549600002003e030005502c0000000c1610401d05058180d910040842c025030090380c0718013034803d0014001d542c4110654a04d200c095075588140c0c1e049001d96101c0601d5036141c1480c54003114801005900b0040080080040b254008801070354454001d00b44a03003226034140c500c5a000b1440382005045140b0100010303030714403207516074034030980207080e20f41c0801401c401a20240d60f64402a03001690040403600045558000030308010a91142c01c54200700c6c0141c00100c00c019442c10645000c03c0402d02c4c05420b40b003681e45c14248030801d6036800c2041c08100070040c16144c0669000d802c00244500f1755608a40f142c0262415440740ea41c28468245150034690942d07011603010041e81c440d058103911502c0149a00f101040001006181907546e0307442c0c195101e0000c103000070700400b0409408800201200502030144c0c0c025903035011998107280a20260b80403011003103100741c0c00380c851071 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 715816232 1250 715814982 715815019
    0x30f0204060e060309010204050a0b030f07030903120e1c181d04020d0311010e07060f0804020a1412060901020403061a0904061d0613020a050108070f180b0d0b03010b 73
    0xc1d64402025a01d03544e0300e80d50810803600902030b41d0401903005100360030009024502d480070f980148010081910940c407901c0b8140c1c02c544116400401040100344030350882e00c0365521800d224984582a80c0c4407042054440c0035020b0002242008912010266144003c40c0c9004c1805450407846030000c241c1ca41ba001031540000a100034400c1007010300c81b83c1018401d00c50340012400c2d200003800120008540a5110056800f43c140010881070070f24000714460321405010320303000340041c05c00170304024103035201d0078401e03c415030040d03042c0e420751800c02c004011292040d00d440000680310b50075850100300742d40c0c1180400200594200100d15140d46a1440d2a0001d82c00f010000b81c0d18512901100b00120320084a1407502130302c400c0000a1113518405e2844910880e0b81c003001a40350401540c00080558a01e8001800114105c048500603140c0c408603a00d16400c817a04142e46806090040d4880d1312480c403050380b01c41000d825401c003405941c0c0c0c640404c807081e08c511820250030 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 715817482 1250 715816232 715816247
    0xf030a0501051914010c080a0914040603080d02090402091009210b0a05150a030308011d160e030a0b011514091c060212040b0115030212070309210f030f020406 70
    0x3100c80203070300544c0100c8607a0068400c64070031640004039075180da8401c0400b6208184600c64007805045120088040749024840e44060300c1c0c1c040440c60910780f4011140c0000c1d00052441c640040c2e00304200d2183ea540d40b01103010203c0c80d6a6804401380c10b120390008500c107074041d030001000800071401d0001d60005905a0302240003000011030b541e802f00310031080d0340700c10015500100203c0001c42890781c04104c0034103030366800c00120b602d6aa00c400603c0c1d200c60498648599a100303071140b500d424410024907900303036401421600d040003540c40b290b060b59020780c420202401300b40c503013a01040d0040428003e6000341900c484c10280305002107544030102111103280101c03106021005c10503170758107a9404a5580200951f05d03d41454101c142110a01801c1c2d01300416946004205200703008403030350080040c07461400364484281c1038018004003c001c030340c250200c202030941851000c0421107000410740e942c8080303075070022000c0d00f2241160074188881e40100810311009400400 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 715818732 1250 715817482 715817489
    0x8190f060b010c0213020d060b0f0702060d020409050a0e010e0c2413060f140f070206030405190b07091a0909070513080304090f0c0903060b150f030a05010519 70
    0x60100e40e10030003100480b44000c010f50001d504c40803812501202c20030f554098000c2c4001d204007000980d844010240307450240400c00c685401d000c00c108001424003001901c495000c0301c1c00503091944824103071096134070171200300c094640e881c201c1c800142400d0080780e070b404481d10040e0a60702c0900c40850f01d024401d11100f90343d1a01d40e40ba05030f0000079501181e60401c40d210b800c45e41c0c642c0740e1500500300440c0c09030040000741081c280d02e01802001c0e0880751108601c815591404d1103d50a21003d0740001b80240c0d12802807a04500c000c1d140340c442030362054841e0071205024644894058150b15594100b640001d990300001281a607012084510004d01141c10003480d17a03a05404172002d00c200a56820340c0100001c000500010000103042544c52022081c0880310601802200301d413000c0d01c014001a01194041012034460b600541e040c65010305445507440e0b407401c001c1c10380c2e406a0100402c5d0440017040050b0038403c0d2041c036000d45411641e0f00455030154010780034070b550600 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 715819982 1250 715818732 715818743
    0x6090e07151b050a05070503070605121003080c0c120309030721050f03040303090b030c030a0e01020904020a080621030a0f20010905060f0118150f08060108190f 71
    0x70000d0030001c1c080c0700e4010075010018a0310b0030841c01ca107051a20b454004504917201c0c419030001180e1403402051030002c1c0e071a1551038a0800f00c2891781c0000c0e042000e085032465070304090004c40480d01c848010404100030400410025180401f4803400712085008070700c0c60b800600000da81540c1c00305540e0100c030b0310701c00000c80071000716100d501441c10101009055202d520300e400c0051201201400c1140e0007515450f400c42c0c1d4400c0140300c21320040f41c021207410000c20004407041c20940c80400c00000141c0014181351009001c10100d80c40f140d0b2082c0880e0200042040d41d19065000d40824010000010014045a00d8140d560b000c1d0b070702110103006c0800019621329210f0b00d440700c008600b62694884e40c04604055134001c18002c403080d6182d015110015030f9540c64004072034100c03460182c14441030402007a41c000108403815454044c1d11203900000b41d40b0000b09400d03000b500d4840040c10b2154035141c0e01034601080680c88641460000e0040008140c003044c0159044d900003 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 715821232 1250 715819982 715820009
    0x807050a09231012050c070b013804050f0d121103090312070203061303020705040905100203101d13240e010c031109060d0b0d0501061806090e07 64
    0x10700304001c2c2d003290350410303900540c4000002001d550320007449080482c02400030045612407a489804034414458042e000c5080c0c40c004100f00c1e064a41c8007010450302c811500c00d02400e030b802d1000c1c0c903001c1052a02c40b482c0007040912462800070308800c0c1c028400c8413814003424281d65003103c07180d03806401c0f40501c0005143e8014552050080b9040903400600707403100c2484c64554103525801803002640244910301c0018100d201d282c0144074443e4160300280b000520380300070000a03284007079080b43c0301c1c091a68809035181c50390001d5405010581c0c54010b03580d040c440038850100f000d0035055881e01149007400a2074823560f0200e5010742d040300c403506400640980c3c000300070082d200003c183c20701d003407001c5800602c1035010741449005903809000c410800c154001171406510300c41544030700100b1901040c0105580b0003001e8200251030364200c044207440302c5084030b54983c0400c80b40e40304280309900c9401b031132049101511102400704001ca51303c044056070f8094038020b188810020 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 715822482 1250 715821232 715821269
    0x906010b0f07050d03050a062715080601030c03050f0d1e05040513050405010b0609010e09090a0506010e01140a06050703030504021311130b0f030f040816030e010807050a09 76
    0x10200b1200703441d8110044500e0302c044c8640040040c2412140e04a180d854000d0105d80c2060540700410301c2c03c1401c00d21080c1c090f50034800710050070308000c0c1035400c02d0b100701c0018240c00300b80150b1340207501030a080c0550510354140141860b4048224000c690801c0b41d03035058445d0800720241c28604910000d0b0004014040241c0b5240305a411065201106a0455078801559013045200e00c0c420b0009204980b805014801316000d00f40c0a98040b41441a84100038140b42002d070340d11030769000450384060b40c6929020306051013a0010100411042c0c010302c001900248002d15240046c0d442007050b0740313011002480d0b8080c40900034200f54072040460290355400c3c05a5052051210003000f685143c141c000509520040a800c04000c02c801c0016601803000242c40c04200300d004146d140d41d03640c070f15050742e00200400031141c00d80103100d980402200c10501d507c00c1031083c1c030341c0101c8041e49000902074010041240040000c1045180035860380100450211116041041d020294 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 715823732 1250 715822482 715822507
    0xc1b020103020d0524040c051c0204031707110109030f02210313090b090c1c140c07111504060e0409080a0e0a0e010e071101020d0c0f090504050906010b 67
    0xd505842210704d01300700511140360802070118224420903440d440864450764240002c0e60384c8082e011012840034040300039a6442603014001d080c1d40010f006207050780703c1c0d0795034000c10025201c0207a00d500110f401810030141c2200c80004600c00d003001c144852640e55034445040107450000c1c012043da4051018041284a0703103a40e8107900420b4903166210380030402c050820f184102c01e00142440e0900c169401c00c4003065006402603c0c29920f49025403080d605003440790035003510380c140e40704c0c01c40042c040e00b02c5060703008142083d030443e51a010b07410250021402c20341490303c00e1000b444c03510074800d0000700f19401c1b941681803000b000c0034001c00007001400032031000342c0082030010710041120703031040208114440440b0419201a100c020800c3c9690003400f5a1401e00f102c0340200d94074a00440300c0302042e804501c005890a0780c202d01308001d403941803240708041103541f030f248810542c1000b0008d01410065030208003501d0f00c80c001c3c1781d4450042c0306200004400084a520551 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 715824982 1250 715823732 715823737
    0x7170615041a0306070e13020c12091c08070213020a08161103030c0c1c020d0c08210f070c0506060d02060708041508160f08150409060902040b03010c1b02010302 71
    0x2c0010244e9115160000014000031040707003846102d034241c400e41901c050001d1003500c411000300f2004184403503051008900c542e011004843c0c1c00401c4007000c801071400120040780c0103110309900b0342c440039544140440000038130610303038004d8010311510a85070f0340988a2a8081c807030071403030448400d0882040e00d00040c1c08500203141e001c004100301c1080402c1009015040d0410304036600c003280569003081059115804a005801407882d2010700d070b100740c0c811400e0303d015894007403800d204017401500c3d201681c1d0480300c9d0b504850042020701085060065807025a6041140c4d5000c078540e180b503110310000384000e1140c2e1030017840b03c0039074480405980e02c5581c810b0146640b25164101c800301c9010200142c0005540300000559441c042841e003108036400d5107540000ea0070f00c0c5c800342d80c1c0440003420600d403018040c000700800d031f0301e80c0180c01c003403402881c0c00191076031180184800e45d003249030420f010740c0c1000c00c0060940d41c01b0f009114003014a21202c4403561203440128060b2 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 715826232 1250 715824982 715825031
    0x8061903110f0a0515130f080d02120306180a0908030c03010906060906120b010e060f0433051c0501031a090601140f06070c080717061504 61
    0x400018001004100103024003002100007160b404041d21884402c001000d03481c2e0140e0741e0001600a11068950039a00c007074075154001c83c941894140d1940c01e14107d544190f0f00009055000c84890760700c59030144402050784d04070b81001482d628040000c46d22580211490142080310b0704002038800c08a80d01c002d00c040d07842030450303599051184003948281c00030f00420040c540380c4000000c410f4058101d1004883c419107951a40000c640201d0b0300408030402800e0500c032050703025401d5a91150000d1400582e200802a102c0c3c1c10b2444814012100240000011100c1000b0381c0100401c0117074070500c8074281c5001c0340c1c0c41e440b02c0350003101d81d101c0070101981c10b42418004410404200c0d070f0703c030f8020348041421682d42d80300c4004a0b6100c03820b20500030341c0720346072101c0ca1450801903c8813412050140101d480d11100e540d0390140c0c6650f6502c102e80e00d800101041c0102181d45080f903c070798014100908031420b00c801d03101001408429075038440d6940b140175141e0041c0d0b40c0d40c0302240 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 715827338 1106 715826232 715826269
    0x1b0d020c12010f0f1d0123061f0306090b0301060311121204080309041406090402011d060408070f080d021b01120f06030b0903270d0503030c0d06090b060a0806 70
    0x900754040c1c50282c102c401d82c80403c03270004600f44141180c264940d400529145060303800c0d41180c500101052180e4180740342000030032058282a508484110340c5c0d807903149141010a0300c1d100c14042d0901c0c17281c0b4045000208401d010001d4400f1030b5098a007486009150005d018100d0011260b066001d24003030003050142d441900841d4102c1459481c07907140c886200d00240d81a0400c1c1c0c0303c444c080d400400309100300c03688407844400909545c0c00622002501c90000b070344600c040a0200010311410800354032583c400d00c1c0744d06088c0320b006010000d074441e43b160213000d05098001612104000004103000c508000100c0d201c90b490401d280301d101d1142c0ca010034803a000c040c1d5241e404010210518045007003400118050b40d0000310b4199201c0c0181001025202a581305a00440c07620010b03030480e4440c00121100700c0c5492130b0090159540328001549070341c080c001404c9 = true := by decide +kernel

theorem cover : BRFrame.Cov 715647482 715827338 := by
  have h0 := BRFrame.cov_init 715647482
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715647482 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715647482 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715647482 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715647482 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715647482 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715647482 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715647482 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715647482 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715647482 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715647482 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715647482 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715647482 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715647482 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715647482 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715647482 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715647482 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715647482 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715647482 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715647482 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715647482 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715647482 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715647482 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715647482 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715647482 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715647482 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715647482 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715647482 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715647482 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715647482 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715647482 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715647482 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715647482 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715647482 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715647482 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715647482 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715647482 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715647482 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715647482 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715647482 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715647482 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715647482 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715647482 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715647482 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715647482 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715647482 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715647482 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715647482 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715647482 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715647482 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715647482 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715647482 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715647482 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715647482 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715647482 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715647482 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715647482 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715647482 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715647482 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715647482 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715647482 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715647482 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715647482 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715647482 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715647482 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715647482 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715647482 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715647482 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715647482 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715647482 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715647482 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715647482 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715647482 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715647482 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715647482 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715647482 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715647482 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715647482 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715647482 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715647482 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715647482 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715647482 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715647482 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715647482 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715647482 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715647482 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715647482 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715647482 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715647482 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715647482 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715647482 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715647482 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715647482 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715647482 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715647482 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715647482 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715647482 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715647482 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715647482 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715647482 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715647482 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715647482 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715647482 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715647482 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715647482 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715647482 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715647482 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715647482 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715647482 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715647482 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715647482 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715647482 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715647482 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715647482 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715647482 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715647482 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715647482 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715647482 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715647482 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715647482 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715647482 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715647482 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715647482 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715647482 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715647482 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715647482 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715647482 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715647482 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715647482 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715647482 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715647482 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715647482 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715647482 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715647482 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715647482 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715647482 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715647482 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715647482 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715647482 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715647482 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715647482 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715647482 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715647482 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715647482 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 715647482 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 715647482 ≤ n) (h2 : n < 715827338) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
