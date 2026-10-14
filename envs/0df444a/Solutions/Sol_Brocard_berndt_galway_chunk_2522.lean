-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2522
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:57:32.984913+00:00
-- url     : https://prove2.me/submissions/aa18ca47-bc1a-4d8c-bdc5-3f390091b514

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 453417266 ≤ n < 453597122 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 453418516 1250 453417266 453417269
    0x1407050d1a060a050a0215011e0902130b0913110a030b0f030615120a050109172107020c1e1c080f03060121090605090a0b010b0c070503060903040618 66
    0x2c01c80c4040090441080c029006018220300c0d80c03045840c0c2015182e0b41a01074802a03101c00300b85041080542c2100798880d1030301c07000c4c0c0500c0c0f41c210f060110300130305892072446d94411003940e07040004011029031521101510003d140b1001030020007514101036400381e0280ca0301c0c1c000640f82902c50100c0e0319101410410b551401001001940c40d6042121003e05030b0210722640324410306c3d200304021406000883d0250b00800c00003410110604120a03164600345400701a03200800400d1054584030f4100302082c41c1e00349a6940690f1400b81c16803908c039005075942c1e8016560350701c51b000e0b00400c40d072260080ca0700b5200c49076840d55120b4404000315003040014a4928140203258000c400710001c0d680c0507205140c5040c1c148002030041c2d02e1a52050900c841c0103444070280e06c1030122500a0903000290b10b0011320011245856003070722090180103200e140c0d0380c00074040d210702c50104195405020024241c0f00c29040103018207640e940b00c0c0c49214040b408600321003a00c0c1160290f500d0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 453419766 1250 453418516 453418519
    0x11a07050c040f09120224160806040b06040e15040e03032214010b0108060f030c0d23101a180a2c0708010615121407050d1a 55
    0x410114100401c40a4112119201d458039a21401d501c085007096405041c07828041e005864445012640030040349984200140a05102c0302480022238042144040c0591580b400100948610000801074500b0000c602d601403400300380400c10f031070340c403880c280241d001c955103041044150f07042c482a030740420700301e0f07d840d0010f00025081005c040c40303019a500000310741041000340303a51000200c0c0480d00e02940703c4c1e0b5603840c3e05686541c026410503008401242c01820000355200000e980700b1503501c1e0603020f000c0d8440400c1c100000340d41014441413164900700c003a0340e078152015659a01291000c8270380d60525a0807a24080d004c03240c4a03010402400c4088820450324900703005041c05888811807aa6a82071080e04050020500050f103103809071740c0348050440384840745001e00313a0f04078505e07992620004000301d0401f0011810b056407036050880c0c800c0701c0c04d50f441d40113000c4600006a004c0b440e00401681a60040041c25101d09110040000e1079609800805025941c144a03 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 453421016 1250 453419766 453419773
    0xf0d0309030f080f0f030126100f0905030d09030207060503010312080c09040f06060f2606010c0c0303020d080906040b01030803151e09091204060f0e0414011a0705 72
    0x18008101c411001e094614019036000785000d1300003643c1c40c041c3d80142c41000042402000512807103107500791420038507a0010504034400d204008007603d0b5145200b0502e0401e0741c420826010311150b80080440e25001020340c0d441e04a00c0314200040c107038030790341200140034a03903010031001c5c01113050706d06aa421004a03008441c1c1e00c03070b0070f44035010050b207208100b0318180b0010420780d0380c9014034000c5465100b408140d240ca82000070380380b0009030700c0c6070b42804070040380c95000c83c4200d10481d40d0050580c4150034142c40b040016680400c0b4881c000c2c20180103088013105140e000594200d511410b81d0f2a04c6250f551079a01c11f0b120f80058170f00410030a00742c4010408520514040c40c2c07c03402041481c003110040c400054551614410783d0648400500344161145c500150b0950788400359002a15090700c00c04c1101c0d09501c80e07070080c241032000078101c0307c03a028810248494100c030701038401c1090010f220151880420300b48242490100800e40c0303424502e041174142c504195000005 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 453422266 1250 453421016 453421019
    0x206010e04080a0c0602040b07150b0d0b13110607050f16031e0201030b0a0e04120924120606050d0b030d0e0607060e070e15011b0f0c1802090f0d0309 66
    0x3155000070000080d100540c09007c04986407086400a00d49188a5100303140766100c102d10240540e44a1801d5500c01c41202803a0b00c0400c0310903141d42e5200e00840300c8062031238400e2400c413005114619039550405d130046001ca0400038001101e032001725810040311901c5d19080c800b078031300f40742da40002881507940c00c038458a6149080342d01071039a48141404240f111600012070b9a806550780040da01500920611051000703c0b0221940c070b032100c0c5481c84140c0c1c00c04003514800d6209503407401a03440d150b46400000b9110740441c1d0181c44034003800340000e5136180c00c01808ea4002000b4200400c1c941681011245800141d0f110600200d4507050050f482d40c00400100380c00044c07083d41c00988800302c0181c0d090080c0800c0010700a901303043d54907810490203c18402801100880c1805079460b00a6030990036692003513a0154040385824085003d45406c0000300340d9a40150362140d081c12440000541c140c003e4000158140c2d0b07140181042d03801003148528640c00050041070f1004070 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 453423516 1250 453422266 453422287
    0x605010f0b1206040e1902180f130f3810090c110106030305040e090304031505090307020a060221090f010c17070303050f010501020a120e0d081204030206010e0408 72
    0x1c80c0b903800f1100400008550900b000740c035041500e200402c00112206440100c11443c00710b00100040c1890f49644915103030801e0300750000031020301505810545001100c040050312580248000e80c403402c0d10388034810040c0e0240c982c0c0121041d61501d001c030322000c00045902c1000c0c45205850761040540394502e00f522a01c0100203801040040000c0c2205020031402c007402a40f00540c820f60740c00755904d18001225498200180124000d90000c01c0100f0114481d0321202e21302c2c0d10003000004054a41d494007601e1845030030402900502009030011b50039401046101035a82046644868800c200c8244c031402c0c400d20300c085500991161141e40d0b03951040042506251140301e9490204a441c2d00c050481e0700240d0048001030745031010040ca1200c1580350fa40185028002490741c400e07c4ea5450b0041204d2410303050801080400440e8a42c0d1010440080323035030018001c66a409500078645e844d50301c1101c040e40584501c2c0700015005650880c1940b0481d044506079003070800601 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 453424766 1250 453423516 453423547
    0x7050c0604020910030c0f0f120804051e03060a061401030603030c1403071403070c090509060f090c0a140301150b040608361506060d0b03032101030605010f0b 70
    0x414525070022503c130040001191559410080c014483d0340701c20040c588002030f4000d9000741c02c8009100c4044d080310001540c5002501c040e81d07411600c80c50b501403109010340c840d031180300d0181e5061003080280714101d1100c0d8042e00984e840b1008618981040c900190144d5180c0e1100800045605401502151401c60300305101c1c9032070001d90749045450f886071460602c000741da8030000e030400940403081180300c90040d8010b00110505001780e1600d072507400d88640008103425000c110000001e180990309105c400c441c610014480301c0650b80b1a8465400d004140800c2c60007036207886621800346111003060001c642a610038586060300301f038822140708030090050060303105000400ca401000404d29884d2800d44000c07e44d52080181000502d00511006031121034011f060030300000d603d401e0126181401c2c4418013040b8298030345d0101c0c0c0b55200b094036030507407100c0400780702c00d110900c040814101c0b4003442c000d02c071745e0340c0707420505c6503082c500d00c18013088d0501044603c2e20403251b07d = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 453426016 1250 453424766 453424771
    0x90a020c0d031d0a350307050a03060801050a0623060f0f0c0a12030f1a0607020f040203010e0624092106180106270e0a06110a0807050c06040209 64
    0x30480c0c00500108040542d25040300c07500200e4034214111005d02014003a000c1c240b5452403514441500b0b01200281d050b485d1102420060801c2000568550030134000e80142c801802540002c200c0c074035142180c50010405030040c108244050000c0305c5000010b803011030001031005114500d805003480c840c0620f980401403581d1440000c0c004008800c4d030500524030303600c0c050704520101084c00c4600808036168000304041e950301d481010212001c4030710281d183c1000035580544d42d9a000d0000031007603039052181e6a4018000000860b114100c4a040c07406013105589040035000000700e1510f50602602049440020a1028595078900440c0341d881c01c0300c040386010800b024000095042c01001c45840b4441e42141c0c89444424501748680001040010400c0b109007040d60700100c41c40d50003600c5051095101d0030b03801c0d400708061010452a0781d101c0001c11003418011440e805075000710005c1d50224140c08000b41026000340100c1e071100503040040c10f400c0d9196800c002101d00d01 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 453427266 1250 453426016 453426041
    0xf0201020903030a1812120305070c0c140315010b07020f0102060103112e020c0108150a05041a03100b09100b07061a04140406050c07050a06020f0904020406030b090a020c0d03 77
    0x200300020301105210341306c00030b4500554464a02e0410403002038141c62010341b50170b0030010300044510110390400342c0c03401070b190100c01c0075410002c007900183c40e141100b00c541a114030720400006074601a14004c119861082c2d507074454002c0b0100041e81c80d05d000b444003400105060b005100b0340d10f4184c84400360150303071014081c3e00003c010790b0a9001154a000040541c2c0700c40000e031095070700281060350062200070f51400664441000c07412a400034450180a19181c4508071409822603086506090001d0112a4103181c2c069601c03001c0e15107400c02e10b020314001c00200301d510043c68840c00540f500381c0f1810b4034003c9241c0d11600100582c80d10410201c1c900800191642e48a010300a4413208000f0203040b24141401c10704111840642050007081003007140d440010000319000b05025002030005894000c6006031070168850030420540c460300c0020042002ca8150740301603040442034465110341e685000e00101244548142e0043c6a400460180c660900c00d41261980303505 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 453428516 1250 453427266 453427307
    0x80f0a0e03041a090901170a0f050c04050405060a060815160306030506070512090c21120310081b0a0506070204060902040f080d0212160809031c0f0201020903030a 72
    0x15506601c0e12000c01c03c401140d220903002444500c5450070300101030140480300701400400a04810300755882413820f40081c5803000540190040c40720610083c442207401400c14003841c07808c1d00e0410340f41c0901311605011140b900b840420a45000503451034540d100f103032010103d889062181d0700c1131001507c0344081544500c804000100300384140382c094180707511400d445103804401002c0d001001000c40c54a540701140c422203d6507004c50f00030000c2d58102c2d804940c0e00c8030519050030441000d05140705003000206121045004010380c1003110814030944000707008450b0060000200e0090340ca5108103580300c00d000c1481c2013001048840d100800003d085035075000c0d05070aa80140c0d0001d5079150400c00208140041030000d034421406505c080c01160183c18070650701c03401500100f1040b9079020b00001c080046000440d1504134004041320706050187d10521400e8100800480c0000c48405080440f140140241c0d141c8180007405142015a0400d084518580b90b0941c19840b42 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 453429766 1250 453428516 453428519
    0x12050114061615050114010212030a0b06040e070512090604030807050307030b0904081e120411040b0d0c0f0f050d120e150d0c0c05030706050a0b030708061006080f0a0e0304 76
    0x10700a41c80940205820b90000c20551b2605050642d41190585144e040d500100664203550400c1000c8031b5220b03013074860001e0240040004901180903030b1b0070408070740d81048144400d850700540035241c90311500041c0001580e8210199440701ca042c1c0340203011440200200700e5503405076000e103501c03201070300e8005000c2a4200018101c03290903181a26045000500006086110b20700303420580156200245030500c0b0b0745041c4080c0b40010005030103102014015503003590f40c0d8000901b5914014010319054856080822100b0450b21a00040d00da601e400060b1601c4c0d100042070031194002d1055000841d40d854601c007403841c041d0b048003044036403a040803642d83c50303185140a1980307030030600e42c07126101c18621048038052522030b0306218070014002d000420020031201c0d06a844040401d076a268403807014050070004a003160f250185503030109403c48001405442800c1e404000e1803480d81d94401603070307151016540c20310340900180c0040c00b000c107160440c060601c4c101085a1405 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 453431016 1250 453429766 453429773
    0x605090118031205090f0717100c0e0a0906050117040203070e0c070b130c03060902012a0501050c1206151903060503011b09050d08090405100303120501140616 70
    0x1c04000c001140030030020742c407999404543e8030440d60302a42910041552022100c000d69a13855140718609004213402c5111100c40000c1c0440c402c4110048802e00603c600381e0390250126044000700342c040c03083c0510000e9120454068013040b914103850302c0c494030070031006144800400401c03c2c0d03058400c002d00062100c0308040045e1242d02c0e07420748a5225161840d00316048d0b00058009652008000b03002c002042903200e408040707903800000050407003035500c0162901130090844242203410801880070301038806050f01c6d03d180c4504002c02c0180c5e102a85542c260055807440d48815241c0d07000210701d820003400f29a01044101c0c01e02c1d0800ca0496854205001c0c1e803520940003a440e81002c1122b0700b001d00920822440869004508250301c49004202c4e242034801c59200e402d8007035890040c410540c0c2141c08422001d88140b249191196400109881500c0b0032800503030b403071a61850740c0300c1901c12141070303461a615910840060108000e90341e007202c0c0901c0c0d4a01c04520700c49000 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 453432266 1250 453431016 453431051
    0x207021503100909030504151704110a05010c21020a053702030d0f0309060e01050f07050c0d080a020f0a0801031203060b0d0c0311070317010f080a06050901 69
    0x1900c2000c0c26a41d807442d0404050031225640d43c00a2081c0e4240014440040e070000c0035641a108852510040c8552004040f113600030b0400ea000d00c91102c540034041800001010316600d034900303550400c0040c0e501c0340110303210403415a02070182c07a002046100a915121407410030440d00f4030440306d0308119510350a08251080f48902c2142c0080301e04e12150f04ca4951090141110744c03641c10144858580100c1e4039094259000c1e030811000e03505508150f40203074800078209410010030403403100d15000b002d00810040e00c0600700040c1c01800622480c2c810300484402a01c1c14000c0e00010041d801c3c00d4450940260031406510f400b407241d090070261002c05000f031f062241d40d40c10030301d52443c200000e0210400029404240c1000000c0c400103a0300400c50b50000642100000c0d100e150703520440007840c0c10030814007400c02c009100014164040d01d4500715007410360540000b41d90310b0000210000042c0b240341c0842c0c0002000602051065011030350264400f000480c0c1075000313448003181c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 453433516 1250 453432266 453432289
    0x2030705120702090c040e0f0603011e0501031b0b0f130b0f190810030b06030c06130e0a06030b010b1813060602060c160b190c0302030603010b0a05091306020702 71
    0x103000c20041442c4065140c6020007940040003002080e01d820704040c0c03420070780038008105208c03d40c5000c3c0800e000742c900754415001c0240c0c18406c0c19a0143e080c200001400c3c082c03205440c03131024400c01403011200d16080da000c48140c481114071301642061810070f0394104860441d245011020b0005480101c10003c244600d1070a0710140d4960540014044400000301c0c020100250320003005417040491841d14241d98101808040d16620313400001d14100400c589140c1140011441e001e0f072001034280c0000f9110a01c00d40780455460038901c90403554544000b42c00d4541d11401007040e80c0400005181050301c8007031084000c980c65001c03a4100040095000850b5900c8604100066061004035007024140c03403080e150030a04e81d0fa050180f20055000381100314010049510022240880c4104021082c014000307116103490241c020f400480d50b4500070f5090107145421450201c00e0041540d400811340c190a07102d258480e5651560b101c41240d21543c200101409a910000c0052 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 453434766 1250 453433516 453433543
    0x7050904060b0c06070e0901090b060919060f1103030408030c0c01090b070e04020712030c050c06040b0f1e01140607140705041b0807140d0e0606010315080c06070302030705 76
    0x2a43c0c0d81000a880d80303007540c0206100700b0088942c014030740350b0391110401411591a4040820210700810001c0d03094417070800410380c0202d0020790070309210400a01e0304203e480e40d031240c40302498100340603100765030038001104103a007007000020000f500c0100555008400a20b40ca404e1401c0c2100c6c45003100d00d815802d480c00e401000800c0007165008a4075100c1c8142503400b03604050140c0c2d124a4907088441d520f070300b410b8954a083c10b074140710b1000e65500104000886035107060070b092100c0500c00581d0300034a020740c03d50008028210383c9500f4003c3c010000f0303032a0940d03840c0c280404980c01c658104240e000c2001c10030302004c50500311705c421041c8a10703006801e880d071914013008105c90b800040703140340b06102d1617104c0007a5005840c4075844070ba40c0c1080400700008910016651194042e044542ea10b40f11034291000c5e0001105441820300707032400c104a207601c140c8940316170769911540159178400c659070007640c00e209002c2c0002038031a0045900b44441545c52605188a0302c0204 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 453436016 1250 453434766 453434789
    0x3070c05010513020102070513140109090201120c0f211d060108070302010f0e0a030b0a0b010e012f070b03070c11040510030f1401020c0309030105060411120705090406 74
    0x4080c4102882480d411410160711000002a150300207904d1f0442403082071720580c01001540c0c8210880e03002107205640b514270301c086568440900100800350044180e000800040d5041c058010303610032802e40e01d600351521039012002c40e00403a590728800010460120801c0a1841206418064942c1c0800c1018240800726080c540c22460300c03005074003002c2d003680501010400360341c209484030003071115441d00307005544100c800b06000c405140e100501d1006000d04000040c5640d51045000c0403007660b0311203801c1284001100c1c610600481c004003420b69101c11440314840785004400c5015910030b403400b46558541401241d00102ca41c0300101784001c2150081100740e500b520313903a901c220750400c40da00b040b5a010801c040c05000062940328803852007070510032071903010b40002a24000a40d914188000402d817250403004840307000c0d44c280380200329185418051031103c8a2080d0302142400e0403075100841050000c0c081400b8000200800c4d5501c1d00c071070003074002520b10005003 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 453437266 1250 453436016 453436037
    0x2060c03182710050307120506250e040902040c08010e0705070c05060a1e200a02280e090c0a06030c14090310140a151215060b0307 58
    0x20a40c1481032207035540e01c40d203030050050004541c02070348118520006107000880b075494040c0d40001601641001d81d0510440e000000c00c19a402030050a545c8507401391000740d1101c10840d40201c00506c2c4843c20311b0528038898520b01d2152510041d0b40d0001840030503501040e0f0042802c5807091800180094040c81c014400100e0036003040e60081503a20304035242803a10b0f214400540410300416104100024840000c00d2260089441f0040e00b07210003914641188006403c0d8483c92840704592515101000d1402c100030807545c139a1500540005a4540ba40b041c40341580c104036503071815101d2104000c00e40d1004200c01a218285000c020401012a0010810040459070000f000c241c18030824000300c5500c20304211030034240c1100943ca500501d000a401e01b079108000030800380c82c2c00c4030322110300e110959481c05442c000c0c03000c1000011100c202d5003006020301034940818002925500056604000c22070512401600007600b00c0e2150001c0860350700582c1c44100007403001c00c1 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 453438516 1250 453437266 453437287
    0xc020906062b0b0904050a0b130b070306060206010515160215040306050601021203060f0f0103061d0a0e0102031e09010f0603140c240c0c090103030203070309120b0c0705010902060c03 81
    0x7071055103003000c81d803100052a00c5d80e500340e610b000081005100003508000f0429032795840501e800400d5011040c0c0c0c0e40341c6011080100200b4075445924014400d0000001d0b4608114404045007409a4042840c00301440c00c0328a145031440012600820148d034007500403c920307006440035503c038400104003820301800092030150082ca245485001c10002c0c00341c035680f910703800c1c05040030647d190404045c2c01001640280201e41c0249049440725003540c0c52541c455455a10480c1c0b15101000b454064400f42030807400121a42c07400040701102c0401e40080340c40c0f040ea0b00040200021461a01d05070f01e2606681c003591080340e01d800000000103001d070382885000b00100041c0c920160796059000c2111840c1031804190b000b9040004858840341d10500401d00310301c5003d000c65803079594914009640303034082c03907041e000622080300210b102202c100e00d410035507800044094207903c0f800b5040c2480e80c08014103d6407513580b05221300058460307002800701c819900002e182c48014549 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 453439766 1250 453438516 453438521
    0x102040e1e0606071202011104061812030801120c0b0a0306230a050d05010b0d111504080d142116030905102c01021b0d0c020906062b 59
    0x350405000100d0007045481e8503104180c03203003e80c10004014481170354000131b81c010401c3c0805115500b20001d00800c820f0b03042024101aa80c14800c4003011640d1003400f4107102010b60700050000f0798a400401c508294050140c0455000c1c1400440300c0da51a4407002d600d501c01c3c0780d0000401d440e075a00308541d4519061000c034601052122000070a08080060001102c0740a070b9031041c1e94a030702d8802408800d620000380071002034003c80200303d60741059204001034003466845070042c070911002c1010700109540172a42c1a070000c0141801120090317440c001202c03262800c1c16800d01004100c5d4200c990034a80e810140e0104c08070340d082014410104481d803c00740b00600d4103003030188000510000f070350055030307041d003100003020381c448000c50040b80d07800a8500c113545000d1540144842041d4000d01082c580f041000d500c10000d150034070345800c40440d0040100d0304045042016062060601d607010800500032841c080388803988100342056403d1040c4154071000303495600702c03003d1 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 453441016 1250 453439766 453439801
    0x30609090b06041d12030417120402060a111605030f010608060609060a03020a060f080115020604061e020705010b0f03070f140607021c0506011401050a200102040e 72
    0x9409101181040d01c49400115000e001103000341d40c4c840d0048000c4440d07000c000440c0002406a8002c2c04c2400b01030030310754005803019640d509914180c076504104010895034446500c00300a40140d50701e4007002015082515020180510100c0420700514103210220030140c3c0b45105415043c20501407620384603617001107141c0d130703031500390148460b41c2c00041440e40810102e410107403a594079400703d41c9040d180d5100039004188c1d54400300c2c03090b400005840110300c0968506546070380e80d52698110064a82e03d05016811100206020032440d80056140b10280e040d0701c00c0c1c0b0310784c0c450340400702c0c1d00026054035265502d00c3ea040040c075008003c070050b140d088008200e5603040008450107000036202d1081140401460000c107500c562095520702600140b00603114114138560003e40f10790003104030382c5402540c0c00400c00d80c0d1030481c001c05e90001a55014141404100c0a680c20140303100000d5050310a43c00407c3c4a0000f40018000b4058203072800780f41f800e080d01d500518800f40c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 453442266 1250 453441016 453441029
    0x3070602030a0507230d0905120705060103060e1204030f020414090a06060b030601081306061d0609060111030a1d09041208070c0809010e011b061a1e01030b03030c030711010306 78
    0x182c44004174480c0c291400d4a002d00000400004c00783c4051803c0b61800100d03400c44001540c01083c01d030280300d004114070341224000d07039041c04a43e40311840542c442e0051a0210000141840700381b001caa01ca030240c10350180302030400a942c0b1110303103400c0481d210071500140d8550110204008104150145100400d03031000510300f03606040c4006071120b00300401e6240c410307500c102920280710850700550b00418009001090040046004208030002101d0080c0100081c4010442c50351150000c0c1c0c00703100d0108003450905024080c11035118500040a021115200803225440c1d500c210103203004921401d0703000300045030400040c1c8204001020b003400d11503800050800300b4840c5e806c4030815042440c16080c410100c41c0141c4041c24000784041e8908402e0024108005c86644801060080b0152402440048804001880110307100c01c41c03044407540304000380d40d40603800c0b09000d920024281d03418400540301c0c0320b14642200c80d040d00c00082688100c445942c062240202a209 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 453443516 1250 453442266 453442307
    0xc02180906011a03041e05100e100c081014150d0f0b1c02060714030a020c13110d051b070b07090b0405031b01180b09090c030609041403070602030a0507 67
    0x209502c032080001c04896044403644e0780010000100041230100ea010507480300000c005084800c88041d65840f0700e0151541c40d2071800703601c5843c903409081d03070620034007400c00a02440790800608540a0742c02101e1a80c006412900341c1088490040190118810328200094107020410110041d5501c3d807072024059000d043c4d580c0b46141c200c40d02d50520640680300d241da038000ad40317049802901460f240d18858000885c09076003040d40480c6003104080101d4071100034410b001d0040f0115200c00c81c1d66038a5101c20416102400d0068000d2640560500402407040e0f0040070040350940c8031490071104502c2c5c5c4005c0000d0160002a110098017044a24508060070080405d95400d0028080c080c0c45040f80c81000203070380b01e80000c01d24825401064000d00c0e40c1e80e15066810781000708010b214046500000d640d0349080400e42e486000002d0a5051315182d68481074001310b1103142806c0a40010030001340403400d5030000358040e164042e40051149000c610040c003c1601111403205201c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 453444766 1250 453443516 453443521
    0xf0b0604030b0f09190b060102060a060b0405010e150f0304060e010603080d02090f13020406020105061023040e24010e030d0e010909091406090d0903030c02180906011a03 75
    0x5801c0d50550707a00003c00012002c8907158500045d29180050018294008048503000100031081c0421070051200380c00f260340740e8076040141010344100b4051440440424071041201d1740c800d40a07403c0201e000703000360500c95030300b0b404240b40d07034403281c42c40010210000910080280300d01c94014140b0541c00204405130665030b4129513480f1f014019200c158021071552416641c1c002d0154800100901c156460020480c3d044d0103034200d4030903140503510b0070b0000b88460a1250302080b1641c074595400342041e100d01844440d1400000c801c01e880b513000e020125000c00c3e204803440c01607132041c4d4500c1c040b80c4044500100d0303620b43c80c85141040f03030740249900d003901c0c001100c0d807841ca2035080c1044090404c40040710304035440d900c41c1811900300071a06e07040c8104c041e001c031644540740301a0303803055032141b401560f1203440700d002d04009044003508101180c80f500e1480d040620090080c04044200c1510301070101042e03503444001e07006107004220840501d0107035121600340e2081c60b030031803 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 453446016 1250 453444766 453444773
    0x924060206070c02211005090d0e1804150213051002011527051602010507080c1e070821010909050a0609021206070309020906010903150b15040303030f0b060403 71
    0x694200a00800080d6460b280107000c5c00c2134400d09580180032911146e1041c41d04001074070b020ba42d21070203409450810940030384600d1100e07040410181911405140c41c40b005000d641c40100180d40205426004442c0d44007940002e22941041c4000c140031395041604029070f00303295007030b2481560b14017234044004112610100c402c4030b2000e205140e0216101c81400a4040c0c01085140c5107850042041102c5205403410085507520390700030060365a4011007959024019903010407111401e1000030b0000c4601c8591b68415482c6072903682c00c0480f00d548449240d04080500142c1c01799034032703109641e003810b0301e02c090040820000911130030301d05403101c0d0b4558031214805000a901d0314030074001c0d0340315000f0040790f641d403400c02c03599030385843c05004006080c8200704034800c40300d400110340c45610601c12402929080460000b9402c0c03105017203070080c4800624150040180361001c1401c0c51824054401103000c0d40b0003051160584c0c00303260480e8011120244103200074041803011 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 453447266 1250 453446016 453446027
    0x17070206040f170f0304120305070203070b070c0b0403050316020303010506042d150905040207031d01110304090b1201020f0a0f0504030b07050a080f04020114090406092406020607 79
    0x1c250811070041440045080c640502c60b4200c1c04100c0060b03002954203504800e800c025032041e07004954090004104c02d00131000d8034400e41e81100103074820312030340e0007140d404846141c00400c40d007000641107650b44d0301e14191580440b410740100300084100300361480c1820b80c85804564a102851446d03042800040c0207008074010440c3c0401d52000d1524107078040361005540444100d10b0403c0c860b0f0300c4c40c00640704180e24214500041603140002081d041900a60b00039641c5510b0747d880884c446c0480215a0507860f44050411a504900c01641d06040c8003d10240008070008520800f00300c0901c0386551554000701140e82c8100300c4202c4000491090b91031031111846c0c100c82500d4900f8044490b409a0341000d0440d0300c5800034032440d540c02000801000e88aa15506429034410150584800044401034041110019130043c1c440180e00280750400c4008c0c00050764076101c8825000300c3e000388840320000101075210f820310b221020044130003807050380300400c1245404a4018007 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 453448516 1250 453447266 453447271
    0x903010c021f0e030409021303021206040f0809010318080421080301060503090a051002090406050108040c0b091804050708061003080d02090607020405090a0c05030a030c1b080d020a0317070206 85
    0xb029680d600458030700c00c42807041307400034003540c02c0640d01d40401407140031200d0a10322089119060703501041342e9140000c2022841160800b41c90401c5641940307410b05143d002a120720b04169580d036075a1140d2181d6009010007a0040c0f2515890398100050910aa484c8903103407810010000904000900030104681c10b448036171800e50384a4891600341c030302d0800c020380010700d28021280120341c0b0301e00545c05004800320843e018000560f0700e6005550000083e100640004150201031140250300e50041241040141040c421126006000301511200390b508450300d8021550230000c0c15030030011380f03412603068040400d94520b0b503a500403c910030040c8054586030041844001e6680b10000e86d0050b540141040c00340b858081d10094951074442d1080360001d0824070046024280041c4108a059158803642e5000a25450780002211003101035455000c0d4003201003020401804a10495040c03500200202d400a1138003034006c10011440c0c500c602400c42c00c12000d258006082078 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 453449766 1250 453448516 453448573
    0x161208010f300309031a07080a0905192306090f010506060d050c0f0c01050709060504050f06070807061b030509280f120c0c0504021305280b0903010c02 67
    0x5060049520f0141d4040c00c0c40da102034039200c07074070f00344221841b0301c0d01070a4410754a941c3c4104107030ba04c81c1800c10860341c04000241c400d0780011641520000e00c960131082c0c080c0103082e1038649818604501c030b904c4c40e440941c01d0740c40e0884402c0c0041c07031804001c80c00394003507454000c4c4001d160507804a00e0b940504a0012f03900354503140800d4084042c5021907003104050084280e0392010006942e010300416103000c0d00180c480c08001810500c01d40c143c07015114010a1b900c20b8000e0f02d41084401e0b0050a416128402c04100a0001510030b2280c241c801c45041d1103220601d40002000e0100d402c010300c4078683d03811076900d00000c51041c0703c600b9803140010000001d03044090405485070012400010300c540203290319008010340002c0b00d02074052040080c0c0e0004d0b5120011302042c0c0c018000a80581c02d02c50105011a14095030b070a001030a048064211044c8000e0701070000000f81e52001d10a8800001c20006504082c002d8800b441c49500041c01400351005403103401044130031401 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 453451016 1250 453449766 453449849
    0xf06050916030225030e090103020a091a0307030c08060705090901030b07110105010303030e21030c03061507030305060112020a09092309030406020d23161208010f 72
    0x41140724000c1d41941c5821003007420108104080c0340103054130208820003503020492044909803245040034107181a40d42c0604280388040c500001c0b000540003400c1d03001214801c0382400c0c000380c0c404000c40402075015082840e4014174046085051510203407680e42003110805c2100d0b501d48401e40141e0440b903201d20291074695039801c04980303003042c901c000c0d8041d5081000001c107059050b000f041d140d0002c00d0030307903001c8002803405d5200c0745185088100c801400307100003030000b03550324081c642c0b04d000134100040d4030703d00c0055003a4590203003200310301003595401482078650f4006a1440381c5140754104502e0803884800140184100f4801c84040b60748400034401c1207001114480c2d03c000d920144190f0354188062615202d400c58010711005108001aaa60503807081c0982e244411941c2890300340c4003149201d120240d40b2040510743c08503a02d101c05000211035000310941c02849644052155047c41100060310000340e0080074040030303603c03060354540d1008903841055403450425 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 453452266 1250 453451016 453451051
    0xe0916210f151508010509030703020a020f15040b1210060c2d0b0a050c0a08010308030901110c030304061b021002281d0103060e060d1104020c100f060509 68
    0x104925440d240000b909207410901c80482d500c002e59540d6080c1c44440000b4000d554440195a60381e024050001d001a8868110724001d41013001071140c8500c405810304035403030108240030105500c240d1000a10100c0050788401001c3c513402c0d100d030404205a2080602407815400030329844603410040c2626144804028409200802c0c01800701003001c01c1d05031010a81c1040540301900315250301c0711a04050000700190345180850b20b0382e00158403558200d03400c544030070510360001041c0c115950358944802000b08071841c003422281902d18011a50ae1401e80f07450030688910780802d25260b11012001d411103500803541c9440340f900107a00688451110043c032240e0040d401c9030190842103000100320499010700d40a54282c0c031346092118039402240110708a41ca0761081350700d0b090103080481c0c458038006452012141c000da940500044580d80001c080341e00980d07815059500c040380094510302d00c0e00400303074400c40c8400100203aa00e40070229280702d800810a01a280040c5132 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 453453516 1250 453452266 453452273
    0x21c031812050901120209180405010b03011a1305150f0402120736060f030209100f14090609060703090f0f17030306100809070e0916210f 61
    0x11000d600000001009000924060429404800d4642c0045ea08040e48080c800d150b0003240e00044003e003028402d00c80904100c4120300740a042154a95240c0c406901c072a80e0034040e100307020720b1120341c403c2c400c0902d0381080100041c405c811004075091400b04600d0130070b542d0210010310320554520001e0070200000900a20444a2a00303d203864a0203000c0304583c00400c03030000c1d05d080c2032141025445420010300c1000b1a0100c443c0040801d80e040c04914410001051900c003607007000740c2020444070010310590b03540c621090004c0c00315804a04040d0380001080480f404004400e4074061120000c42c2051040140315402140d0004038a0b04061050034418000c08400401c14030441e2900c0304040b800b42c1500c035001201c281c2e0f000500300d010020044034081c40000308240c10154213060141ea40714002001101107008929000030080403100c220fa1140e40c0c060040d1565900030800358803802200d13000700080081c201011521040030401c0548101d82021120761030048928 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 453454766 1250 453453516 453453551
    0xd0b040c080a2004080304050a1d070513030807031e0c021507050f030310030606050405010602060403030b03030412061e14010b03040606120510140c040e130506040c0f06021c03 78
    0x1851081c1c080c42c0001c0024045c4000b02c041c01c1aa4412140e50301d11070b580e112001c0058074401d050101c0c61503200301190300c95003c1e0000380070350107101c40308000741d079500e40300e00400740c01011050300070032903d0240180003c079680c03150446c41410300303140e0702580e1a600070440d90391816411302100d160020303141c800d0010800200354074401030030443c0d45d00c4c076150402e120289040e1000b01c41050030144003045a00c3d2901841c3c0c182c44855000300696078590310b046002d407841e031900780d825000c10480400e8003725100c00b01d14040c007510012a4805e03250074402c2c400c03041c0407042d140d540e02e09005001610042020300d8112100c0c028407a45a840d2428850300616480e0320402001020300b041108021000c1003d24501d80c644404220301c503050b008810301e0301e204807040548544100020322440c4450b4180030703002065020304034103098540c1d550b14030784407040d030741070360942c0014000300080d9070310200709405460b40e4800b5210780c10b09540722090403807010461100b4180c544144900404038032 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 453456016 1250 453454766 453454811
    0xb2103040303270305160509071403100e01260606062b140106170105030d12090818030f030405090a050402011b1203111c0b010210110d0b040c080a 65
    0xf00d0390340f04090381e603240443e611a0150001c18507088554400551454134591862085c081c686030800749000080c600881c56100810304241d40342e80c0c51001c0351200304488614003a041000f0340c0031b00d03c044801c010502500910404803903500c12010080b10303860303180075941403d64003031007c500c0d46c1c0c41000c40c11310b0b41503040081c11107a1500c0c0c0c010001b01201d1503a14100e516036241c001036100482c1010407826000d00a803a01741d4020107014081c548560224206200c144000190f910499a80d040860707001d50300b448107000f02200121103501d400d010749004a00701c103006516085c50000030446100c0d0061181e1400ea60f2000001c040da4000c099505249003140e25032583c000c841e141041c400091030300362500103440c1c04d11201030b801c980000c641590381c5c1e6980310b414685071101d080010740908107074681140074841d1303410170540741030042c541c149200812603920b80c81100d0201c0c045030510382c0d07480d208030b061412120495030860403040c1c01209107100490541c4850305401d16a0b080d4 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 453457266 1250 453456016 453456077
    0x50d03090308191409010e01052d0702040b06070b19020c0a05010522020303031f05030f0a031205010e1609051002030301050909060f0f07020703060e010b2103040303 73
    0x54003d00d1220400301c12443c0c03100076220302200020050304007565000d04210310303001c6030494605001941c054000b412041d02d04100030145000402d00b28601045024200801c850001c00d41d002140342038010b60300000e1086d10f51908282094980c442042c001801a50f2122080c0d282640c032074040c0e804070f800d4880c214084030030009592030003600038401111b1140b00080262240d60b050b00003007030091006a0018029411500c40101040d5a400410341c40d401085a08000240d103440c01e0000144001710f0b0b401510260100b810054804800c6503000c4254510b080c0c014446640003000347c642000c0310300807400100e0300d4060103480c0108207070801d5900c402c1000009180c00d60000056060701c000b950720301c825407034410030240d407a40d09541d21125440c506001440c20440b07086503035030000c2c00780b04458801c1d030340f274484100315010505603045030b944650300c00109003403000c0c3c40c24100161380e0704402002001d03461306450f4066804014204000c418050010f102d81001c040c8500c000c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 453458516 1250 453457266 453457283
    0x61e10051017090d090b03090c0411040608011505030c22170c030c0132040e0103060c0f051605010b18093a1209061a0402070c050d030903 61
    0x4400390003070a10421441408104040714001940f0190080346161850b0040e4880700080d606010305005203410081c01e4100754444c0c1c4282696076039031030181070605034500fa01c0c16620b50400a00801116050304003024080800080e214069071100c1245d51005c1503000042e1505014250703460702203000c007071032544001236070000706040c4501500345103880d840000b00d07450004400d0a1649a0380e200881c903010458000003948031921059209202848002c90003a0444c00803118441a030015004262000d00c0d44006004108041c403e00400d0071031424410404c05124400901e544100355559072408186c95403001084400d4018010000e00100011803078124040d90070651141101c2c061501e02c1802c4900304c0f01100d0f40b10a0144680075884511403551b14606d01d010039200310007942c1001011030342c0c881e41e8a001d104000d00d25200d500c01140e081e40d5500806412480039107298072652041264100055400c144181150410384508190785100e09064503100385941c030240c00c181 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 453459766 1250 453458516 453458539
    0x180c130f061502101104030f0807050604030804121b0201120605030118050d05030705041202011b05150c09010801090c0201020c031309060e040b060d11042c061e1005 73
    0x105010301800d0910660f401c5a5241080c84042c070140c0d030220b003072002c5282c010402800412000c0c1c01c01c00c003160082400c0386c0b410b0340e25900c80f890404111010f500007074200081c0020013466964a600c2c1e00c0340c9103049400c01c603525241e2000400b0b1410003d06005820b00070300074980c0303035410810040000500170010001c10a101d40c048180c00901142c8502609890012003806081647e00a1f030b0950b96041c1002d0510340b01c1c28072621005400e038140843d00060350580781e101c200316038a140c0b003400a42801c107a4811490801000580500807421041c17000001a0343d00104c0349044030305107480820380d603d00707a000364020311a1001c40e06485c040044d01c600d81d40d04c90660b1350200c1c0c1441c0b00411895546880403c1c0b50304081d00c1c003c2c8000582ca000c031701c01c0d203002c1c89010304d1940242410308504a04500103800c640206400a114456040f20700141b01c144d418060703000c41d45140170306480d00d05004c0240140d0040c05041340031040100106000a84071300c5a5000340c0400f80801c2c8442 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 453461016 1250 453459766 453459779
    0x3070801091b0614040315151e080c030309060310030807050703051009170705120c0a030915051902070308030a02030a15150c15050f0609180c130f06 66
    0x140d4510700309100510b5003460014507544604605510011400d041508040c1140c0d01c429243d81c040c8100c00d042502e81c0f00c1c1846610090080c038000f006815003101c00c00442410340717416107005521140f442e0b003041480140f5920040100c3d08100d50480e842d070341c0c135581d40440d43c280c4181500040c28403200818084108030340003410b1420349010300226421061107069040565044180040230400720160150901048201a012151151040c1c4e9690f190320110001c0c99000b81c03180da0041e6002d54003800506410003008005003441060160710340c02296800342c034600c41d1540d48000c0c0086050403240d894030901c0034001a5502118a03030341c03810308103807504c0070f50420b55600312480c0ca0280c80c0307a0714246090480d42103c100402d56898181c0c0314500360386400e051002134030360300c0e5401d24403807a85196204e0a84178102204c0e1000450400b201449081040240160b00304000744500040602001030000c0710000c04640e150f2002c850038141001a01700d40c001d00318a21300341440401c88 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 453462266 1250 453461016 453461033
    0x1401090e1f0216120503070210110921010e07051203071109040f080703020d0f0509090a2f19140906070218070221120a0207020111030706141806060f0307080109 71
    0x1f44416601300c500301000040108111141d2443d45008507004100c0d0091134107000c154200d051014001886001001000280c25503000d143c1f4a0302036005410103002510307001c20900d80c504422001141031000d2981c3e10050b014040c440381d841071001800240c02c004681c41c1d401c03055030344000c0d500d40b5410a07241c041d40d1210340e811160f001c030302a112039007092441481030f1005000c2c01000f800040d2141ca00e990300901d2038649104003044842180b134149080601c03642c0203200f030880415524030300c440b00c2c3c24500d046200760744100000d040000840202c200c0a03100c00000840d06180e50324210310014030781c01728072104100e034000d41e00c00304101c5a0300440c7c00402c0c0d4080e920320074500143d201c4404401d1068011001461802d0380205501c4210781c0c2c0504515807040c189200a0341c5000545480d5800294003298050b0300c0c1c2050141e4680b0440003950403680c0f21a46110080740600d4054032004002c211500910502e1b002d096103507400c114810080508030003c00c0580d0860401c2070f076 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 453463516 1250 453462266 453462271
    0x60b030a051509070b1207030506040b060c03071406190216140f120910030b130510060201060803070309030f171803061609271401090e1f0216120503 66
    0x9407802454400544d404a4078203c81c6d803242c0c07030040d244c20b542d19400b06800502d80a089140c21a540d00641c50603529204014404500c5040081da1900318130703d4850012491b80f40715060a801540500c08055094442404449600e01e80540c072189001800d100381c02040350080e04c1110308001e000d074200c2000c00e07064803030441241a107030704049401a41c031007446102d42d5982c100c20840703d01103046109600c900c00000008042d2003151003090103100c00d40b40c098a20502c28440048200101a024403a0400a0501c20051400e154842c0c5010f4483c244a100c003070312500c1c4543d458410410064413075008207a0401d81c1a03200c2d0261115503800400602089000e4480c010108084040402c4002d004030781c15139031400d406003017500360500a07004241000d001c0c604030700204070b80c0c10b0502170070901e41d21000425099625111080040e100c8400c841405d540142c64000c0010306e140e251142c1e140d401503800340e5107070b01900c80480e000c204410050041a000c0400b0725809612800031030 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 453464766 1250 453463516 453463531
    0x90c09130b090a050105220e15071818051f0b0a0207060e031908130618060c210c0203010e070905060a2d0504141602070b07060b030a0515 61
    0x180c6944511283d07084400a0041544c8540002c13254030f614641055541701300141c0c4000440c0c201c411a43c02442c00b000f10200b00c64488000c4100070000c1d07401622817007410908014102281d10b000c002103050f880640003c200581c4510000702080504d6207480c0c41501c07201c020001075555181040381d50741006400c2001170007010f40019219101d00c0f90b201c0d0001d001170141c040d1a4003107000c152070382c1c030307828089803054014801d5421001c0d24590000081c003064480303a20940990b6100d40c031803051a009001172000f03108050010070780154207440c2030003c642d41c213074031000700300c4040d0340c9020902c0c0000c2d13240d8203010007801880d6000c90620102c95260406020613100c00c400c10414030300a00904010f21164950b00107084040d00406040402e07500c40d0608003a1101c012a00b50ba29a00f1100b80c0b800d401c000b0310503103c4008080c0f01d1b0111252000c3d0294500313100c4141c504d8450b000004e012680c80b02100300b6103590070702821010550000c111a10390501c0fa41d8410484000c50700032 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 453466016 1250 453464766 453464779
    0xb030d0f021c140d20040e0a0225050712060b0906030309030d0c06180506060f0609221506020607020d030c0509060c0c0a06120605041802090c09130b 66
    0x1100c0c049003904140b110602c1d512000501500000881d020742c016500d0350403455220325824071030740c0e0030404010040252680c401d680300e003001014001c3c3d05001e02042c80319441004030382e1541080c071040c46080c0482c0504c4040401490071b081340780c244207822507042d04010342401c1c0b00704407035640b003d0030440b0b043c0c1c0c1d01401c5075907030b0040685a0044040303040c2c058000e24090f0700b0191050310b0010019201d62400101142207803409013400e50503104c100c3c2c05500005c01c2c843e0f1803504070070719540c0a400b00c0d4050701e001c602001007044102903400300b2500c1c403030310182e641000c41c95030803840d42030305491056001d05e9500c0a00030750300d1200b55400070150081c0580d02d113040d84240038002586510b03446440c0b6210030a001d00c10f90764071030758000e50507009601c148803803581e0300700754040105441c0c0d030703554602c0c0452440c003011910319030f00103071156180881d00d50040b036564148803a180d8048038110500e5903650400407861040002003079001520038051407400f007031035000e00c0c1c0c40d50054400c0e = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 453467266 1250 453466016 453466033
    0x213050907080426270d0519061107050c0a0e09061602190b011701090210030c09030c0f2d031209050d260a0e010c02040b030d0f02 58
    0xd015030014140c503803200203041c010010b400f09840d48031850503101c4899540e0035805503840e41d004650490300d403215492840c0c2d40004005084042496100041160083c040310741d90ba80c2d07140c0d2204c4031601ca0100340031180d020000e00150354012060007000200040d650798480c601142c99241d4240c0e030b03900c00c145603140410b040003c1035005104007003410017404592288401c220b0b003080030015440440c4241400e00300788404605000200310710402011030780b541440d0f41801403c2030030b101c500caa41e2410400f08050399810000540100c10780c00e0005250010340c1c000c54664107640c0015001c0d01c0b2018000401105035520202121014080620092000038007540c0c4101c0000b15044440b01c000c8051001c24208948800f0716071644c00c01030401d40d500c00100b000c008421000340c82d100030310701c143c0da00b1030b17140e814070000c100c0881c401c1460100d60300c2001e0080c000f881d42090411620340d94500440d100d9901898a012000301210543c1590100040c40d64150004100050041ca940d = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 453468516 1250 453467266 453467269
    0x20915120f10060c080403140d0f020d1d04090206030f040501110315100519020115050d02060a21020c0606030c0a060c0605191e06150804080a0201140a021305 70
    0x111900604241e80c0b034080c0c881ca407600c00c581d043d214030b00030384101108100001c0050f14401d500d80041840344042e111034840984041c0c2400ca4030b424010554102d0000841025031100c80c4400301802d0f2004502940d09110200e0700900f0314150094015600005114018169a12880c0b03e00d20410090000050541900d020f50000746c4602c0140b48110074150440c2c9400d517034185240815190082c2019000c15200700e075802507001d410090307552049141c00303017050520320b80d0151805844510a00c0350650210b071444c424075043c2801c00011010328000d10720008002031000d80e08500564444038034034115a103562081d10710750700c60311400711001c11034200146803c080f070300c4649500c0048996500c0c1c44010f010003c040001c80f407006840d0710003d803454883c121214a0b0a21061075000100c07400404540c840e4001048102c05a040c001c4010380c4021070552066000f200d40da01c1d505115070985c007415841c0d00b500f0103051714001704201d5a0b00b680c050034013030000800300c00b1070658650 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 453469766 1250 453468516 453468541
    0xb0c030c12070209010303031806020d060305060903190f020a052a030601060509120c040501080d02150603030301090902060904051f05041e1d0f01022109100f02091512 74
    0x7240290002a02001040030900a920681c000c0603102c05a027045400da43d03a81c8103ea1169107a2104540c2d60030b000d0060007002c10041e940186c00b88001c40c5030a40c00440c4500480c92044017108004560b80c1e000c0a4500c24000c81080c1c81c0e00000303d40c28128000001c258034030500c40085118171080c2c45d00308072480c0019040e8102c1d000354031950b04e06023001041c881103211801c0405070707034131910311540f481d0b880d1403095a0090070802c010b08800c08190344024100000f112440c14045000c809200c038554021040340e044403102c1c04001420b91240c40403540134042c1c00281a846840c1000f04009c40310f00c15424081d0f0a88041040441d40c2c94004010440b001803503c8070b81800c0c0c014010202c0b125550180362001601980b006c0e4030125544610301e000119483c44075165004a544200c880c01c03400d1501c1240391482d03005046241c1402d00d0355132626010400c411407078507040381c2030071070702560304031040d62034080c2c940e40141ca0030808002d03040e40101007081c1c4c0645100000b0f10105800c0 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 453471016 1250 453469766 453469777
    0x9060609010f0513030503042405070c0e2509050109061805090c0903031603022103040609080405060703091a0a0c060b060d0c1106060108070903030302130b0c030c12 73
    0x585035804440e0070b841c0211520742102080f80d440d0910b0b441c0c040040748082026000800710000c0741c00805038150040c0c000c4481c0660b640f002d00806106a07000284104106c0d020349a0154145210307640300454034048034904079240550781c030007800480c45254414105070039a007003a01e0744060703d50f1b0f0715821603840381200040441c045440030240410700c0d10054044e0801040010a0301381114080004d0071684208482c401c01c6001d03140200405406018403600e400880c00c1008a05142c080c05078168800100020040c50b500c01d51b07501080880ca09550203410040e0146403104044d150152118031b0500803010240000348540c22000201e001720b41103440a0780d10200d03d0305282e6100d034003800c0508001a845031003801f01c040710510501c244100110325903680b4403c210504a11402c00700d0245c5400d0410003503000300100250018180400c60307506280050361707680d01050760010b400321078011032150500042e0203410010300001518400b03444600761044002e50035400d00c1180b082 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 453472266 1250 453471016 453471019
    0x209041e0b01080123040b040902040c021f09030509090702010e010e15181f090206120402090907030b150109030506070207060207061107120809090916081516170a0203010509060609 80
    0x80b002c071788060803d604071505000020b44003240e040015030004058410700c59481c4016488107500035a241c003008840121226046000c00c030010268030010458421a1540360007900071f1004280014403d50040300b10009200003040850b00081419490744d494003030500e04a101c140220303402d0381166151924000344a0000e1590203881c0f50701d40f1401540741050140341d96103404171005611032100600319070b100709900b2240c0d03180c00d00c108041c28802801c1401c01d648000c50510018078903070324454000290008000c820700b110340c01281c6001d415000140b050284c20140100070b50001006826600c3c2e5400780c40801e5110b010441c2e1039012220510302603800b0351b00410821414ac6810100740d80690b140034a407415080100d488904140d48908d010707031107407403624414056084040302a00305100a07140360f1200141e890f040e4000a885d006110050407443d007a40c80c0505c511500841c41c20f40031005074544030a04070000d4000340304190107190303000700262050ae85141120b104030300 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 453473516 1250 453472266 453472319
    0x1c020c15040203100501090b0418030f031e0906020903190305160c211103070e0a1127011d01050a080901180609050c01030603080a030209041e0b010801 67
    0x10420940200010281003a03070503015504004410400500809001c2c000107100070544052301d9082c04101d8a0903486440c01c41d000a28100000e41c2c804410200e4000c0c81c6400b140c0ca50341c45060748240c05030010800401d0345000112410425550040c3c070100004600b51560088049424100784107024002000503204220002180c1e2445090007a2240034002824659840e40800c0704018600060014185c001000640c100a411948a107143c00242d0191210610b00b090030050000090888840300da22500e00039003444202c0c06460241f15141680c40015000d2260740c4200d801108640d80050758a000e81c5000200040e200c1084c044103075280c501d0004184070884507a032001d040360301d01303541f1400e0301c1480c608040301d41060326001c0c80001400b041180340c61440c5c02c418582450615040c400f0800204901205640306120345040c00341c3c2d607408032400a0000c0410140280040d5028900111140c14941c810180030500f0f0302d9034102644c85007240c409a100c48981415200b0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 453474766 1250 453473516 453473533
    0xa0504021e0327060a0510060c030c0f05150411030c0d060b011709100501090501080705010c4d2b080304050c011209020907081504060b1c020c 63
    0x2816000b0343d80a002c1c030300032048107150300c0d4541c0320380b1200c45180d84013503105405208040a09120725178201851120b0307040c0c8245001c00240140c0e00691b8040c051003841400a800d014000d000305100a52280035602404441c0842e0a0500d409403070a80328920070401c00000c5090003d08410305107002000c903900c0e58070343e54940e0081c280604a180c100040314280d10306a403118103000d0b00885022002e003100c0e00c3c0b41c10b104011203030164007404049042c00e00400070100007181503c113070f40082c60190401d21340c83c00d022056403042c00d0411039030240a44242d81c0d101124182d841c4230383c0c4074440c150201c0700340d040454210105203030580c0c0c88003075014442142d0203224100c65189100190802e1501c3d115120982250421942a54540c202c0c000aa55969104000d00c0c60030600f030700204808000c03900401e8200c10018041010f11400c8030114029201c09130301030700e5101005000380010754446000c00602d4000c5107001241c0c20302c805000a0448a9009840389000d00400519604 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 453476016 1250 453474766 453474817
    0x2e1511160e06030a1505090d09120227090c090a150b0a020109050303090303091c052a01020711030c1c08030a1404260301030b0601140d090f020a050402 67
    0x75402805190340b40c440c0c050080005600405c0c80b4402c500c0d50b140001e094585207444904084640600a04003c5075030410301c80340784104094840c1c03640548200301c0c00108001070b01e81700c1d112500c0031034018501c41d040016080000602c0c46098109448080440d1078000d084070588220100398000e4404103402809884035050103014030030b003244004600c4c940551240c07030850b402a2100c1c007c0d41c00001c10040c9615041101c01e101e1402c2c10520815861071b140b0007021806002401e2003440f030f22181c8450703a041c08403100d0b811a00d01800841d5200c40d24640030152110644041d0300074003d58803010050f24251202e0900c8900c84005c03180c4006040d03807403401356031004040c00728069403800740c007510880c1221803a20451090803074a6001010003028540c07150000c101a002c003e00704010f00020b000a0040f0b50003000a0900d1007072000b00415000c0c05000c0c4554640e802407030b02211348203014220031011207a5000340c850145d102d03203403000d1006a120f5410802d04031004110b140015 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 453477266 1250 453476016 453476039
    0x1d010507060b03010b04112104120c0606050a09150b040f030212010906050130020d02040510051302040911040e01030305030c0c0d0c21082e151116 65
    0x240b15004000291550b0403400180407601c08120316182d034000403c5c5241250302c045185411205203108901c2c0704c0c0b50540c4d4495040194a44a000b0010000e16141c1088a542c004801800703004012a091b036440b02e1400380101011200d5084400d0103150000c0d40d07400002c102e406a540c1e404050640303a00399000e002e00d40d083c02c1181550781d913a5141c2c01020948600c1386074080d02b03600481711100c07071150302d8405808140808260f01c8020520701c1e100166101d0807081009035055801240b9950341d1400da03c4050195880783d60404900f50401c0c03c020000e034001d02c25500114801c1114000041507141203000324000c00804603881401400401d000740061544002e203071600300e01d0000004819070400c3d44038480c0002041d800b101e03040400c115041443e0544040643c240484010b00030020309501c0003400300c55190000c003152020a4078000806118409400c0001880300c0d900c00c00d4480198031050780300c00180d10041c0c0c01e80b070780c03001040700c0082c1441c050b0f010340307414184440d1918 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 453478516 1250 453477266 453477281
    0xf0a020703050c16030218060d11061b01020d1a06180a090c020709232805040f030f1d010516050a2006090913020102031b0d1d01050706 60
    0x1849401d11909048101c108441c9080c900a210092421485d52040c890201d0803003078480b101340080303402c1140c503840c0c0340c1c262071209030031125490001c0b4008001c00e445202d00790030015410041401e0181c0558150018000704855500412020190184200c8141c41c260310007075220b01c080000e0a10b070254001011105140207001c2e240d500e582b40c442a0490700d00e0344044016800c00181009046c07200d2080543c042c11072200d001d05071b80c83c07820034100300c400204020500050b44254944403c0100103451501e21042010403440c1400d00381000780c0540905d045000960500881c0700440c81810320b00140d0140d0704a00c000103d060005648580080300c01c032b032030160f60044120100750104986240180580d0300c10440c2e00c1c40055200e8008200d0300502c0c01964200300f0000903032940840141c0c48503007042c1c681c1d0644d8807413004034114810203000782d00741034940c807a03c16509800b09040ca40c0c1c0840d5100c0c010765134603c0e5641d03210210044681c40c003007401441200b000c0340d142d40101d003 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 453479766 1250 453478516 453478523
    0x307080706051021060c0c020607150f02040803030f07020a05030301060807021f0b041a011b02120a0c080105150d02121509031c02030408040b0d060302040908030712050f0a0207 78
    0x5580b84d0701d070380c4044036031030928150303c880380b040c40345010070300c109031003034400e480301031301d0004491300464021850910500000410407403100c0d1580b0f005080c00e50260280c4000d003803066688680e52408580e40c0d400c10b0340c051301c10084210200b0591400080c040385515400b0024508580c40d021054401c1030000345450194098045165141c0003c490710807608060340c00b00160030500c0d04144401c0f40d10b00300000302005c18001c0784030900d070b810080382440410403031031000460006201088510000505000552081c201c0000c104840d0140301070580b0384040082120b940d42410074a400004050465000301e10301400c4009420200594074681100300c0c200c03450b601011003107034600102110401c1d0719400100340c8240800e1105600354000705010815070031070038243c40e00c030502c1c82244203021964500060704c5014040580280c2d0085400400c208001c40d01420302c144558012924403001845040807a40264071600c00e0501540506640c0c17207150b5100d4140c100294488803054 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 453481016 1250 453479766 453479791
    0xf12060b0d0309080606030c01050315040b0406091b080412050c01180309080c09310501020d090204140f04150b0a030c0317031b070c080a0609050f030708070605 71
    0x4485911080041c428031407090b80d48085091518520302d040c45406003180f0b12a420036110f24007036a0740300040c1d98201c1b141050b1183c5403900c8030000b500509070100099009401d140d000211140310340d002e062408041c050032481c0c80750443e0120340a9404542c0200030078030501d1000c681620550203029007885900000503941d541c0c141070a00344000c044100c0000d0f030305a0781800029030034054641d05440a8582012074200106500c81411003036a9900c0905040001112035207081000da1001c0d68011000b155624040b0f510a03003d040000000c1c1d00450800460501000ca45040380b48150003955003102e45031243d517901c0d80440d018081ba03041550311420694150354908d850080258450003100304098510701d031001009444101c1000c03180001e00c03c210304001100c148041c000c483c08403460b40c1d222940342507140700009401034900d910815802408010700c1c0d6100320700b898002c03411100060382d1000c10b43d6489c491120028215181440400002203075038210940069130031880c0c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 453482266 1250 453481016 453481031
    0xd021207120909090606170d091203091205060106020c060f09090c040f12140708060c090310110a030b120309040f020d1113060e060301060c031206120302060a060f1206 74
    0x220f009a56003080305903030705540e40710100305140100d60b6541042c00140040c03c0301048000307024203103e00500c280e9603004031240c803001c100740c400c03d00c160180081c006c002c0d01c0950107007001c0341c0d100d10034054a405807041e4060038049280100545a60f030604d0380103240780210840070f00c421500007500198500800b40404224084040c2103400689501c10350398003090200d09058000342d00c805454a0150407041e41448002c0001c0382042e840302c2006009641c0b100d910004c2403a04852400ba2800b46141030707200d00040940030028000f6500a80e41170007406041404c0009880444551000940c42082104103505103a00400b0b040f80306800b0050405a006800c0d03c07e0312030000340c1c088000e000041c2c4070ba0302c808082c80131020307000d07e00d0260041040e840200c1c81521040c06a04107108003406503c0425104061810000c83e1070081801000d9942c1c0d0030701c440b02d04800046016018000014060001c1c602ca10021102c0d040c141c91001e5150030688510100d0906094031079070384a451 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 453483516 1250 453482266 453482279
    0xc0108010b0a0f090305070b0a080c03040206070206030c0d06150e100e01030f0f0c020304031e110409050102070609051c031505060903030c070e06090c12070503070207180e0d0212071209 82
    0xa1f80c40100142a41c1595408203004000c20140005110100d50201031041c0009a110070054038007059054030015a41c1d21090300d40c504034058078080080c0b580c03c10102003042e40302d002c2c4da030040401a41310080010b403020100041240d503113820b00000380d00100070299562180d0840c900b86007000800045946070301c0070ba041a034180b00800405a4800541001001002031620542c40b440f5000d00386a03815075607804102403000c800b0a0f00c1035440e80003a8007807001c00e50403101080c1d4403140401082e40c00746081d0b9241c0203100014040c4040c03c14071148a01d0181c0103072450a0240c6000106540c10101000241d801440d5003940503c0306201c40e8002102c00c1100b28060424440c0c440700503e002d0007001580c080080c40300508102c18042e410081070854000740c0c100c01c0f5410815100da89054089180a45c5036100344162240f400b84841040705550000c12086204020383d803503001c0c2640d00340d942c0c1c02d8a01c1c0160b038100c410040c4201040da40740014041c03182c14940401c1c1e145c2c4d1100c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 453484766 1250 453483516 453483523
    0x140906030a060c0c0203121206011103040e0406110a0806090601390b0c13050a1d040203010b060f120112030903030c050313080c041a18060301022a0c0108010b0a0f090305 75
    0x190b03000102d1000107614010404c523880040c0e807101003413074040d0303104050110654503400390b4405c0c0740e1210340c1c0001003004c02c1711907000541c80020401070f643d10307066020801000c500c420b07514640104403100116143e54428070340d21101f8a0050b1000802007003091020000c0869201d0844d07840c00c1980c0c9200c0002e0000324401d000e90003000c00d040d141c0d00c41c900800011a0035070f0110744038143d0014100040f0401c01002c600030074420058440c0390742d1b50300119026050b40003150380d00010002c0c0d0a180420820040c1590441d402480c0400340e895a09461060000450207004500c2e0340b44100006807045541c01d01d00d600c039006689c20440c02490450600b4840d800074825034000b08014226030425210b840d80746000d0700f07090071b40031070200c020607003c0b02070450b08950308400000145441e2402d4044030880451410514603699a610024800f000d2030f07850006540a126140c9005601c9112160b045ea9980b445c45d6260a07100309064074804800b544100c1801a54200080401c0c001d0 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 453486016 1250 453484766 453484783
    0x1d0a02130e0316030f080f0a0504030e040606120e03040f0b0f070204060b19020705010807030e070f030b19020403170705011b0810080f0a110d1b140906030a060c0c0203 74
    0x201d1103850f140b0341c14580a030840904807015410004078000708600d06800b004090b42052a100c000600d6032182d01301220601e0110240c00c3c0c100e8141180000e4099000310300300c07940442e241c0c0400080a940d202240c0305e03c11449660349900d040d40b0b0510030728a02d1070003801c0040710300030110b16100480c1e010070f043d50070076800400c01c42004078016000c01581d10001c05504c00e42c1c80a010350b182407600103080c02402900781410181d945000103000441000796002030b00c2c14602c9010700541c2ea2900e038440c00d600f2284241030014680d01102c4a1030303540281d50503207a1280800d5000c140001e95044030b03801108098400b9900c40d0303c102154940242000c80c400e81ca50b0b105078081c60100c4484880d00c1d11a84104156400082c00c0c111043d4081340e0041421762009481c0007003801200003444202c02c481d4041c226040c0c20309000c0300200b29604241c12a07038054688940c1201030020030034083c204442c440c0d019003107640c000d0300041003a84040b00b48205c3e420411142040c90300402d180403000d = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 453487266 1250 453486016 453486037
    0xf0c100507030f0c08041e050609030705160609030f0f29060f09040b0702031c0204080d03052e0819050106170307260703121d0a02130e03 61
    0x100d1080c4240141c2c1405200c0349072060b4882400307110303652031000f80030302d40042028050411820000b0703950002e81301c10f03440441d0007000f240c806080c20141191260b0010b041221030b48201c4112010440c10414984110f40c01e5807207103804030313181d80c65405c03070840840d02c00c58003c649125500f00040c0e030040d100344281841c00c00c102107008500e10404403c64090b0506100c0c44000080140950310002a0740d41306600c82145c04098403038500c10f82c9036000b4044d0051503622468030400364002241d019004407030001080b5100d80080031800d404a45013507943c020100f00318104c9030b0014150f00c048090302118420511401c1d99039040ca06c1c00c203081c903038440c204080b0f0140c01700306200090003905c002c1c0c04005062042019080b2000d42e483c4a80c0c0001401007030389290180f0300402c1740d040310341c103230140d410786a656074110f1038020040004240030030a802d280108603407019040448007107000c04900c004000c5010a5000c100f4050301c40f0804032200ba803100b0044c0c058074820310141000301030 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 453488516 1250 453487266 453487271
    0x10e0115050f0d0b04110f0a030207020f10111b011e0207030804090624050a11010908040f0314060103030e04020d15080c102a2303040602210304080f0c10 68
    0x900a00300000c1d1100e042c0c0d40110071b44140017200c0b03a020300303500302c0d14515158100166901c050303102007100908007001003580b04401344400d410035a001003041c50f0401a100c282c0308541c0e0041d00092820146607840e50014108014500d1034070550b0307032680500003141c01241c490944d030b07648004655005401010105454800070130000109444290b10b600d0210010811840c804100401c1c80c0655004001004500010310070003040a6101c540c0c0560444003a65840b620b917690080c02058078441203a0881078805140000303403022810384d05030381d03059803420309030640003080102035003000400c40d400703660341c2c1030200382c4600884c00c00c002070445c0d03005000301007120410809154060420102400320405c04280401c004030040c280341d034644082602c0003069030030060000d0780c1e42624207508568241a51036144400030290048480315403c0b6812a410b02c2520702d00703c1c0304000000f03410308080c0085000144040003520500d01e446240a00384070034498844c0c82c0103182d481d00f0402c80d5 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 453489766 1250 453488516 453488531
    0x1050d05011401091d0408031008010504050313090b0114031503010608010e070e071202030a0603060c0c050f0a02090411040b0d061a090f06150903030c24010e0115050f0d 75
    0x58020140c800241542c146038015121301011007417041d100100000d010150001c0081e15621845400402800c2100c0081019180525100350ba0b81e1018101c4400740c81000e100141c3d400346030189e1f090805040c4e4603400540c4070725040449a40014010002d4400c45100c2411380c1d0310244a4400100034110004c01c01c051804012030a001d0b458120340c101000c65820405000d406c10304007030065500b10001a5240c1c0c80c00903405c01400f05800c02041c80341805042110250b1002f929521030b80035200303403030a00c254207110b59620040c40d000250880c5003900090085851084001c1c1c41c9140030300080f94450341c0e100090b8003d208007000300ca54641d40d0301d052061140d00641224905016100e000c03650070301001042126000401040c0700d81000722008445600b0a0240e524003c0b003d4101c070b4840000050720340d00c80800c818800e00b00f08032401c800048000403002d40d41260114448240c0340e9003000240c3e803d10019070350602c00c0c45030400448000221600041c85500901c85d030001c0c014 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 453491016 1250 453489766 453489769
    0x804150e0709200a05072909070602010e100e240106080705090a0b03041109010b0702040b15041a070506040b0105030c0d0305040b0901030b03060403113901050d050114 74
    0x20354160310395103281402c0e100440d100c900f40c60101c40e603402d2035003403883e1141034929000013200e1104140c1c1000f10100761814070701c62800c00c100c60261092200ba00c4403262101d5049080798038210261f20b1642c8042001203400d0581c0d80280c00d0b803100751090b20071201414040c2c032040c0b040c00011510000016004000441e80041c1c104c1e0000854500145010000f1000815400c220300542c0c400d800000003150800c030303008a180d070865078040c03d030901d1580e58042080f102e4001400680c010783c10504090500d240103401d42c44076809811440b400e160800607500307940721401242c040c14410030000500030075000c100c1c07148503900c2494001805c0d8101024181044140c400e10350181c0b03238200386600002d401c20144c50503181491040341e01c0c1c00c4c1c4000120040d043d110941d40d05802294180000e00d42d0140e10900c05841c030f035085607000c0344501a055050807848a502d2070b00d406200030081208074942d411021603a0500d062401d10000300b0001d4103c410a84c00500407000451081000d0b = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 453492266 1250 453491016 453491021
    0x712051308010b1807030209150c0f01022106010c0b0a02131e090b0402071506050103111207080408071a0f0c0c03190203130e010303030b0604050d030804150e0709 72
    0x141240744000d0190004602c041070a541d44207440d18103c01949001600951017603040d120341c40001000c499190520b010f01d608103501807000292a4003500602d465085c10500854101c54036000b000100b140007400b880984d03000c090421350402c5406070121012940c41c0114a005d80c550540060b9103031180c0042417004122940507800c003009140510b504400307444000000c9909c12403001c140d461482e00018024440d00c2c0c0018600d0076000380c15289440c0a91100098a400780c8041203020200c01000010340506050584517900100000340d00354414414903420a01c01d03182c2c582804180d07503802c0901c00240b6507401c0005101c030204082812541d00943d0044544841301d480c24884c001030f2510303403180205881d0006070b04072510b41c003103200700308807403060000e1340c00f0b1040725032100348003100e43c5020f03c020307000282001c1b00b50030249030010882d421940c00a0441840d00c003166420749290032300a005945c0400740c8030103500840901d020740d050b000c0500002e450700300c0c18030550004 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 453493516 1250 453492266 453492269
    0xd0507030c081302040b0d03050d05090601050d080a03090b04060e1509190f080714010c0201061d0403030e010e071a1206061b150103140604020603060f0607120513 72
    0xc140c14500000c41040d000707200e00b41c0081c1c0d1040c03100c0c0356805a001003005822103620003a00580c0c14200c82081c0b42d03014021380b01454107141d040c0010388410301c0480c3c0e5060203016460b0700408078482200020341050062103401d16a0401003840b04040c3c03100609090101c1e42030380c41c1c946840c2a9000d1940034000980c80402c80040340c8500d0410600585d0f6885040d90031100c904010041001401651510714440a500c000c10740d40d10345041c0f81000200f4460680d008080d820b290760300140078010b01030380c0185d41c0f840740c1c10489108660902c002c48000500180d040c150b07240308000ca03114084c00f5031800c0510010042070158030b000001414810010600c820110041c0714140c040c0300e040e03445540240c42105e03141e4960300e44980d645402d091b24070b5150201d201c1c2c001a0018440c000b18024103d0380241100d402d9035400508464841e034080314000d41c400400c200166080c940f000d0034000560015103124182180c84d41c0d00c036001c03109030030a500802c0b000f083d001e0300035900190180 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 453494766 1250 453493516 453493531
    0x71406100f1a19051210120b060d02040606030219030204030c0b0304021903061a03150106030e01021b030301091d0705010f030e06100618080304120204090c03080d05 73
    0x12109458118058000e0031035014501464000710104291202c0382c40a40701d5283c00c1c00c00e4086070315a6040040c06692005003000307a00d0b0005800101000844072210f002c85441c2d84641880310000d86d04c00403d46070050201b5807021400c000301015803510f1182c507000d0210b54078016644c52001c1e4441c2c4552180c52614400c040c010401072000400400c2e44e001220816078031552291610b2001580c44207a001e603d80203c884010008107002158204c68107620911001040d0300f035205090507201c00c0d40500b5104181d00302c000412180f0703c2030b0700869074106600700040c00c0490040d18400a4890f02d00b05081d164004401801201280d110b82d040c0319420340019624441c1404280e80c0b02d0220784a11414440c2c03182c251440c0300d001e90040c03001c00007485e055911920b041c417006041086240258000102c0e400c504c1c2059244200703001d0b06561601303004604007498480ca8850818101c80c1c22038100d03840e01e60754000282c0c002e0300d0102861107105065160540081000100c480003400701 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 453496016 1250 453494766 453494791
    0xf040b0901021303151d0a0c0b1809071e120f0e06040303050a0b0d060207030e03030a230f03070801060f020115030605102301090f05060f03180102071406 68
    0x24004034441c4009002180d43c011031120400d0f420081185c02000408060303052003e9a01112074210310125038884210722a0700d502e40c0f00b07074844071017485a010f000700035081d80300c000480b00302900d8200400750b40003242d40303001c1e04044100f001030484450078485400110301c440902c1c40702d0101c00d01a041100b41d843e00104614007141000341e07610352016001406240d61000401d4001e1300b1900304c2014040080e252a1800c000c91909400941c0295010750009050b120304d40000c1c038010085692151072a901c21113101003075402c4180c0c84d090681052440d035800c203d140c140018100c06540309503100d071035940d0a5854150085c1100081400c100110791418160021070b001c46a41700081d65041100014946e888108410a2600c140c000050040c1c20100468100c2c54a0486120041c801c0e6203d0889990351240380020700da4900501c1d9101c5428089494080040c4000c0c2d0b500c8046e9184208071124107a0140d03003240d02c001420785004004590034244100100b00a58003d540d480702c2 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 453497266 1250 453496016 453496027
    0x190e0a03020c100f0f14040e0f070e030714030a0f060b120a0b070c0516080d11070305060a150f0b0301061d10031107081b010c0c03020d05070204060e0f040b090102 72
    0x14034400d0b040c45418103000b0040e241c0050781e1b03c5010103000000c0030150203980c2e035455040070090124100c40c402c44103110240040c801710712900d40340308802c40c082c00411056041150700344200980030143e903003500c00d4940d503001203030720861400348680c001c400000d4003842c00001d021200d8040000302c071055000c50140c1001800002420b648200130f403924071000c5000d4070b030150402c04400c0c140500740105500c0450100720102d001e258854031038480c00c1c50320301e00c10010342c0c03103030307070a1002070055004100000c03034141139504032144519010382d81c13000040d25000400101400d50300804075030100400140900e40d00035017418810311440b14403a0000d11110005003100018801003c10980c4070003002040381100c0b0161100c181c0d100c0f004ea44c0710b04070341c0c03019038203095100d010051075820b00c0002001a030050007416080c6402d81e0141010f00048082900d09902001040360030954a100000c0c03a081c4546a05008241c00d07071801241e401c09003003e40005d000607100f000542d104018 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 453498516 1250 453497266 453497299
    0x90b070905030f0a03180504150e13020901030605070512070201020909240d0302031b0a05070603020c030d021309110901080a150314030f03010321051c05190e0a03020c 74
    0x2a4606401e80c1450806908003100054000e099402d47c00240c22900700400c4000ca4020036078500180d07030500c3c40007055a600c0d06020095004e40405c0a03400048007001031000c03d04a801c5180c0c008490300b407483c0352505e151559101c816007124440e00503540803541d00181e2400c020b60130740009007103c08030205d5401c802c03c0300b001d00000640d64411800381d150a000c250080c020b03540d512508240140f4400e2031000066201c0002c03c074110303010b014911011078194007a1007581d03501c3c1d843c080210304244c8010380d43c1300258041062a4280c3c0541e02e000510110b2a0040f2010317502c1c080f01080d141d00302c03a40007500320b0354050b00c080e1000303040c14030f07003500c0780d01380325a40e000ca03074004418500ba202c7c0d1492071801d51048409031490755200200210500000c0300301401702ca1000e0506408501c01c0080860f014040d03203000c0401c410b12074600481301d1116400064214045d503060256480d00c8444a10413035554000d840301540085010070145a014820300c030348120180d402100b8007850b0030 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 453499766 1250 453498516 453498523
    0xc06010501050f19020c0303041203080f0708060607110a0b04060e0a050306160504030b0411030f0c06070807061820090906160207030f0507150c030e04020c030d090b070905030f 78
    0x1d150300300066807041300c00c2c07045100b000410003a050207002d903039442c0d890701c0300a40040480581500030642c2c0c00007103603e0000036030301140700d1802a5615902519141b04000d82135222150650b03400038644140f1805659540c100c3c0020105401e070740d69034a10b480b03c06032802c07154814161159451070f034100810f03280410802d90122000401540f40396507504180c41a0003150400f40070141104100000c105040000941e01507084048a51506202e44001e603114403142c0700c0f41d003040d4180036101c0014101c8000d024194800e080100d400c1b80b0b024038290041480400542e80341003044003260b270100e15400500c1014400b51400c030828a8020041daa481070301606a8401345140d50000043c24401c0c4494800303103074001001c2c04290b0103410f0203951030ba0b9900030480c001806103881c0340c1d0350780a928451101541925042d561218103004c01c80290001c480440042c0010003098501401510600303485510412885089007060603009051503541e812441c040d6200c0205c0e03041006001 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 453501016 1250 453499766 453499777
    0xa05040c08010603150b0301030623011413110a03090c15080c160f03050a020132090705030f1005090a1a0a0f0507031b0f050f0f0f0c030c06010501050f 67
    0xd0038081003466090311002c0a441d0154021b142502011001008000c140d070006c01c0701c0c10f054109410a41c00300c0e1141c8041c01000c1c03180c80041c290858a915440c1400307000100b207400d11840c0000d0300c40310510355016603841801001c0020340d42e0064001088007407114607020304048840003103032200019000c0d14007240a001d07410050700100f100d001d40d15003a1111980d040e48100803800c2400389180140c540d4200030410009035003414620300c800c9168840704040d14a240907110203410309904482c2003202c0107041c10005004000d0302245944007080010720310030f40d89004000803d00401c90400300c0742c0c05000c0b10b03590341200e0225408244055044450788145c10589600c85e00c50a181d400105014092820f00038104005c00090603010350008840010400d000071002960a400300e55000c030700b88585021940510403048105030300000703003001ca8030410102e0b160150b800b0b0707810401c3d08a003036a24156403000500c0c0010b00e506000720350041000782042801c00406c03445404190281 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 453502266 1250 453501016 453501029
    0x3060b1002012702190e0709051c030c02030c03120a0305010e06100f0e03060c0309061006080a0b01020c03100c1e0203091002150921030606030619090c0305060a05040c0801 76
    0x80c0f41480c01590b6890400c030328100486035a402d100380d40e61003246003520f0701300c0302500440c10000340080d59040401d40320031115440c4903900c01184090b034040d500b00b95010800d1780c1600c034020000140da00c0c01c01c01311030310154080231075440340d22403680101a910140c11030309080401d0010711056456000d1124068a40e40c00e05400d0f28490150843d101c5e684042a5540351044000780171425a08000842c0617100c03150a407400c0d0364860810001040c80340c45414002800d81e000501c04c000e480d072250a401c00140306583d0140c0110f40080e00d80302084c1e020680702940c07901c2000d0030a420003101900c03540c6120886400c0c048a01010f901c1e802904074040c01100c0072148032090720720900c4440c640d0b0241204021140c02d101c6000342e039400351070b1690706482240000850200400c141540d102e002d008000e00e1540e07841c10140403002d8650b10300c49919100d400700214403c4880e000307540510500707540002c0d070b901e8070b10100481203032190301083c0124a40014900c29550009103181900c00c1e = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 453503516 1250 453502266 453502331
    0x1050403170f0f13060e0102030901170c09060414040b01110316060b040516091e0302040e0f1f050609060d060e1903021014060306180a080403060b100201 68
    0x1500d0402280b20312500612600c60080010408070604521504109a4469070f0390048482800340040e6668860103010340d010503220170000300761940483e442a80700715a1102181000c030f00790049080d03904071741c0040c0b0b010b08005210340b0043c00c00384506000d404007440d10b0814110411100c1d038591141e0190300d4070142c00c482024080c40060f800c0050310550103041003181c0d00e0011980e40820303000180741800964007440009072844100c070440581281900031800107480c540c204001404003101a408501510350a0f204007107051080405041341c40c0582e0341c402003a41c030168111784c07009004912071995201480f00c01d403185030b9614410b40c0e01c001c00085103803003140f0315031400218600800101100328a00820503038046540d44188031000018030100d1000250501e03804021030782d080e090360101001401c900c43c1d0112a4048814440942d542d983c15038481c2c00b01540b0540003547d6003070300c5010480f007074103141c03080d6402d0542901c001c1180d1880c01e40002515840e0b891040390284 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 453504766 1250 453503516 453503527
    0x6120d210c08011406191e020106141207150809060a05150103020304050a120c050c0409112803060203061002011401060f0e04060806190b0f040203070c0f0b01080c0105040317 77
    0x48510044510302e281010901d110141e450724014890000f640c01442000c000400820031f0a005000381001c0e03906001d4000401e040078410300c288505480d807103004a00c00d103580055250446034180002c140e0582c0c8081c0a03141490440c1e1400384003400d429400340c9003001300071581c000700c0920000800300346005a50f986960901e5403908203030303881c003801c0750309014100081e071074210300c200c09251310410075129100813180c1003008964640402405843c0c00c0d1260040078604442d00b00a0600500c20a00c000d5460081c80e41001c0d0075500116903043c0d00005003c0b184ca0000c2c071070100c2140500c000d101a0001c0030781c5030908141031062001380701540c802da65085001300003144103c800a00104602d40d076039001159160410b44d0106000504000040e40054090080074941c03000a080214440445400e0100a40c40180002d0410000748074480000390b0300d4001d2030341c45005103600b400c15414210400d05000c2c0c04400c3c1410b10604010400008a0320190303500b0303052000900359140c0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 453506016 1250 453504766 453504769
    0xf0203010b090106020f010b0d3206010b04031505070c02091801090b01061e09063b0109120215030903070c1d0106030515040506120d210c080114 64
    0x52048500c0e0582c400070000020400540c0000c0e9482d84000c080c000703100018140040c001e901d0503800c03014140a080c10000698407a100d2003405207030041101d090071882d0541d8030b56090036000c0c3c002200b1840c000a08000340200b0300d1aa580d008041007003000242130016015019290005009000c0c400c0074001440f4015400764011866010300b0007444802800d24240080d00824000c1b1008290500700b858007034180300d040c84011040d01e407107110700d15091810550301a8111808040205620440c1004d41c0c200c16a4180309036042c1c01c000c1d40d9955132400090401e40c00d0340c0281d101d80290074000341c096500c1d0400c04000300c034445810340c2e40340c41319046c06003144102040a41000c03003001c400140580320541085460a820b05210741e1641c076464110190790065402100b000e035054030f941c85514041c1d100c135410101c020306650100c03000203140e81c180f14075030000101050903d0807215050202030b42114092400e000d0400403422101000f5182d540c040c05111044d843c200c684400a = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 453507266 1250 453506016 453506021
    0x8030702040c0327050709021c020c01090f050f100e03090d02041503080403170a0815030a0501060801140c0a0906180e0c07030f1707050f0f030c13080610030f020301 73
    0x400c1c00303840c04540c04c0210403510038041d0708401110248200b1400150003219803094400c80014164030b4a244030511a040340030b0340140b49480c030a950b03100818000500300066407140c0340d2040c0040c0c1442c11a06805c0350a1902c1c110310300e10002d040080046210001108031950710004440070070110900f800401c00810754017038580171a80d0710b242c0200c01c0c400c0080c041d000700d03803054a8406030031080340d03008a0300b8001e03d40035a0104241c3d4000c140d818204540c0c000254102070700300c40035260b46485083c00e40f58179134001450f82c0d41d00d02440e40d103002201d607070590112088030910701d000982280101615214030480c0f00f00681c0c4036441c032050150042850003020f8030489000320303090500083d5255070040c0c00031030100701020b0813007040d11302840700001e580c2203018030800c3c0c0f5038031403000391107a900c04001c075001d0060800580350b0500401c006540504034035a40f458680c510001809c1c03090103a0b4000394282d034400c45c100000301d0025002d40083d2903002c8108040801e851011901 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 453508516 1250 453507266 453507281
    0x10807090914060a022d04051c02040c0509030c0f030d030b0a03080a090f06080906190b04050a0e06010611030405010509120d230f090d0201021603050a03081008030702040c03 77
    0xc180620b00602400304880d40152021001b01002c00b03117041c44d00c07666640c804a5103804118100000d020400182c50024403c0c0e80110102451030061312841c1c0c002030481c1c050751200b04c0410310124100d003d07400c0c1009520112481640c603443d030141c0c0400040c2d5100151542d0f0380070580c85010700304181d1909105000115030040d42c05845103d05400506011001d0003140d84040b540603002603058483d00d8202d02940c84440a880e140d01d5a400208650030074600c0000079540380d4403058a02c0c1c4a41c400d4a00c15442141c0004048291480300c908081040e030220041041103038545589040c040222400c031903090a203241e640300e24001007804c88482000105241c0104202400255044540c03581c010341540c411684c50556408a40154024001c0b008281c01013445160400c0c03c01c030101c081214014011155900a040d85448400009800480d603a81106946104040e00084041c0c0c020340615076014045003800700d01a40c0e4010b02c84064800d64590482e02c4503d80240c0c007114 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 453509766 1250 453508516 453508553
    0x702190503030d0c02060a060b1207030216060e0607030e0d030c02070f090203070807050406050a0c02060d0603031713021813050f0a0318030201050723010c0e040b090108070909 78
    0x742c0354100c003c1041c00521486030410b016024480020f0014016231080c1e00580b100800c071541811804012101c5100000b06800280359007005081469289a0b500d2201142700c2d01010444e0310340200e84900707105014100200341414000303030840040307020482101c1d0403440c1c40c00291812110604a103001c280b98010000149092808500c090703a503001503204505545904201d900d404e4002c4490b482035105101c006101844122090343c8a100e81c0d14409000400c203604100340014848201c0d003840c3c1c0120b003c100c2d59004580d0307000c0c2e03451010360300842c0c7d5148019008165004550480f00000840303014081d2900044d0b0102100d00c0303110101030304481107985050321040215a0b40150010640100d407030041000c194841110554080d0395040e554141000c6494ae9400d081450040f0a8507182ca00d061000c190241c0c02d205807038030701d511551000640e43c040c20600046035200110a40109a50001841010b40c0041d1368400c0303608044e40010407a5207410b050070f0940203e0ba142 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 453511016 1250 453509766 453509773
    0x909040f02130b10090f151103160201120204050f100c060c081e0118020a090902031003020a05030c01140a0e030708060703060f060c0f060b030a0f060b03030f0702190503 75
    0x1e008900c0ba640800c451103030980e004950701c2e6001d81c0585d40441c051164a034030100440d014010480d5448030788025991a0424407a1100307006034103419a0070400f0326644400e44045070a0566070f00081c1c0c5d42c4050b696090440c50300d030030000442d801c0780703284401d40d0144400d50500341d08180b18409241d05260009020040c8800c0034070300610a40c6c099039079080701481072442103585508510b03214100c3c2d03401c044a948004031000c101000c0d400000210003401180080000c086980d0700045100f800b0b4480454800350031481000b115040f190411802548404550105643c000e80940380f000121100b0544544140b0b02c01c4a265241d45501038141c0203c1c00002401c0000003400c41c0100010348050108a8450641310782844641c0311342e5000603003540c82c02020880c3c0700515220103000c3c0d075020646000100202c0d1078002c03044000c03101e60b503003101d4200c20f11900384265910800101d01031031503c00460f10017555405002000791103a5000f01d40e09183c0442d2428040007010090146e = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 453512266 1250 453511016 453511039
    0x5041e2604180b0f150d090807020a060f1209030c11061303030c120f0c0b06040f060806090c0406050a0513090b07020a06051e04080703020f010509010c090b09060909040f02 76
    0x40b100603101c030141503801103845011404007482e106500003104140c2c10000c80c100840b280162000d0300049100b910003c00c1085000701503218110020098440c581710300040300fa1b407aa00501000c08001c01c1d01a1501e80048080000d511a801c2e582d901d40000300c50700034000290000303420b032007203940400704800130f900000100340d00290081d03c0d0728040c1c00c079080c289507000c0044c0c5500004401030301c0004c00358001030000a00c8580d070306d904800c02503c000f8a200341d40e1140000c840f0950841c0e24141d011030704101c0c80c0d40f404c118662a114060f5800c2c41231906d8130300400c43c1c2d80e115001e0a4410068480aa0b55900b2141e100c9410305801c841e030300d80c4901300601b01030346907800c2c42010740350a814000000c1e04c002c4c16080c12500d8000c840909151a5075039202c00e4041d8002c0b440032000c60003082500c5115103004d0040702e008164500002500d414540e00250401c2d203160b10140d520351080c001814561342d01800e5800802090310040b03120b40e01c0c1c4c9030201c07000c1c0200074000d5020038918079 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 453513516 1250 453512266 453512309
    0x30b181f0f060504020918070e0d1a161209050f0304032402030606030402060315030703080408010c0908100e120d06140105090310020c0a0c03050105041e2604 70
    0x10000c541d400044080050301c0d00c45040c402640b20f0010b80360781004502004003558014820801e03400081e503e88001400802400905810b4244038181c98124102e00d0484001c00c0c101445038100003103964140708072208850150411a07448007000c1d443d5a604880000d204d81400107000201c083d0003600da445440386810114907000c01c4541b1144944103200c4500740600e03108881c000c1034000c0200d41075039590340c05c110903944000c011141d07400c404070180055840c1089004003075485000c0458541e42403402c3c682c2143c001c076103c81e0401c85100d10030421070b00041081010340c000c0003404581c041500c10750740d2034141d420305020903012001034141c030803000f0396202c034040d40d00082c050328104281704011507507401170481540e07064100140006645102d80d0041c01c0c01c00520081c0d428040d003680350500240030540c030548540c0d458508000801c00102c91181a145030940690703a01d20721a26010514200c40400d2200342500c4003000030084521010348005140c4418040358034110140b = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 453514766 1250 453513516 453513521
    0x3a050303090d031b0e0f0d050102070b192a1106150a09140f150307080c0306010e090d03020d06050603011203080a0236040c05120c04030b181f 63
    0x5042c40c001914040400031810911018803405130100e5540c4070313001c80310f0b1040090150407600c809038480503100044001420a001510000e40511913210492402100e86001890103e582d9404203240c404051b40480980c010040c00c04940f40c000f07100440034803020350344400200031040c4c091240a0800c0140c902901d401e00c3e6608068848030880355844a0301c80507a095460b4030b0006458140c0003406200c1340f403400c17941c071802d5402e210151100301c00119007055601d401c03000700354201105844007400d08009039070040160b9910310150f071034500d1390942c41c0c0c8010b0345241c1c101034000604d2200541c0542040000d0032004040940e0795070b40e40340b20841c203a0f00c00f01c00c40214265400003911305d2064407e50708051290303000388140711a5031040b00000c21003201040b1a00712880300f031340d0039900c407481101080809502c0d0f0a665804024012800d02c00007480152030304810441070cc0098807800300704d80c1000c501040590f110202803050341c10003031103030540c569a034016182102030f6032268 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 453516016 1250 453514766 453514783
    0x1020702120a110301050c0a05030910060b070b10061e05120f160305090c0103020d18030c05210d021612090f081c0e0d08070804050901053a05030309 66
    0x441400f050b02900109040c02d80c0c3d411104410b003202c0c2484100010307070203003004580c03201800e070580d0701c0c00c00403040b01d008a442a41050500b244042034030340811080748201500400054921806540382c00001442d07994103240d1950039034484070b0a0882c0ea030245007600c4e00455000c0c901e10040c601140c0c40050380c03504032a0100024803000495003c07e0203442442d00030401c101c003818480364000010740187d40f00b515628042d65541039940d074506103020f5904007030f81c800c0d40c90030742c1d6402070704200d4509081100e101003460b01e400c59400c1083c440104803200c0c504a4100542c071003040c114114841d40322844081c1c5184400c0f580c0d288025070080b207070741c15501803501e4508507030340fa2807085070703101044e66600c40c06005035840c3c444040c2c000d052991042c60001e05042c00c4840c15910511660081081181c0415010800307000d1403034010089070141c1401c0d602010388031240d420403000d140c641420349031804502000e521105140000a180803900300e0202d80e81c0341880071103941d03940c441 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 453517266 1250 453516016 453516023
    0x60c07030915030f050f070c030f0903140d1403130b0a06030501020319240e15060c0a0b0705071a040c08030a090918050703080a050417010213061e05090301020702120a 74
    0xc207000121002070a0004034000c50787c580c0c03440d4120780160750540d422104c00040505100c1c203440000b001a03441010b03d1074800307491014003402e40f114480944281a0801c007058000d82c10b2042100140c00c4400d13140c19150440140e40ba141c543d1401c01000f4041508050411b5000008111a01800e180c2c0c0341c40c04242004100080030b440381e014010b440741c0ba03129503d1500c0100c406c002c070b082e01c0700340650090304149076640860301450000f03a444c1c2c04001101d4035500310140c85070910031384110217035000c68141002c5c2c0c541002170356056146080c3c100c1d0000e2080101d0003003000c3c009190f0041000d020b144085980d10991418098032103c031501c92980749a0509a018109a0052400d003003a41d0380b1130000c08020b0300750fa40c1e42019070818a04041000030610000030a90380d1660480e480740301141c00103030b94400108804420110f01e401c4a418408a0450501c1c030042400c000b0090048904e0034079180c40d62400001d029100c3d142c00070b90b00c10000c2c907681d000030b80e000c141c000100d4807 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 453518516 1250 453517266 453517271
    0x605060a081f05030706031104120308010914160516150207050f03070308061e0a12051009030e0607060b0901030c05100c05030921060a050601030608030c060c07030915030f 76
    0x14400c01c2c4800350100c0c0161a0580c00c00c0d0702c2008454000d401900c0c5041383c04203400e051a403144028030891a442800340c0010703030b01304010010704040c2e220b142c0748520744555481c500c1c9444044124410355014607481088000180100c0c41c034100101201295440125103aa50b14035020240181d0040c2e0303c04d596502845c0f44044406c0c400004a8803100d5143e1581c2d45282da0700400c101c7c11101c140351440614410060360071841d0341e612042c401409041e0aa000c903210325040680c0b0740717140c804400c030300c1901d4491584040f903005004810100f40850b00c072a0f0b038291a180201c0a400e800d40440c0c0c0010940c400401081811032061050314015121444401c418880844280417a9070010385560420403141d220303418408206084400780da04040050094003c0301458180c080300e80090300c50707641c2e050105c15a410b00400c0c0c01071443d04000c40c00d101c014881385071240000703000080d800d000010040b04060241d1a40002040080c54800c01d0540710800035020b003500d02c441070394251 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 453519766 1250 453518516 453518551
    0xa02061b0d0e1206090a0303051308040303030c080a090f0b1503030d061410050403060506010e030a060f0e12030109020c070b120a06091b230406020c030715021504060605060a08 78
    0x80f0010703030f9920074143e10006010070242602c0690041078050400b114400709040c4003030204c0d07028401040118030135940000c050280d070384020560030025050520030f0b402e011141380410003180c007803100c60f5080045181161200e00e0702880d8851100015500341c000440c42e0f243c10101a0f0100048401003640c0c114412004000c010341042c205880401080c410300042c00030a8032540a1076100340f040c14084400c414100000f442c01100010488006d03464540325507902c0742e40e00804c0d83c2419408014802c40004241c8005580014001c4e0414258003040d0800c50f03450800400000344080d404e41a03450001e034007061400c50301100c00c850801d081100001e205112803103525004407864400d0300300070180d079200300d9601078241201d14249410b242601c0780d40c143c1500800042c081f540050032440302010906041900d581e001c2140c169101e03400d6410300340c02040440c0c0ca1890316401d035140d0350f03e61400d0780050402d40c00c0b240e0082004203901b4040d03500000c0c844d0088034011390006001 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 453521016 1250 453519766 453519799
    0x20321100b1614030421050706141204050a0b160311030412050a03060b0d0e07050f18040f080301060e1e0f01140910030207030f0306080a02061b0d0e 66
    0xe1080d500d012400c0c62442c0103840c08a0010300e410801d2000d00710940e8900385e55084001c00011055829103000ca0740b0160800811004004582c0245814200030209250304028001d40e07000e90041071040d041128001010403805000100f00b06900c8003008126052503030101c0e6a880945c040e03900803070718118200c00c42c0d48041c01501e1187e507206035884540401518115142e0304040381c09810b0507162000070900040c17040103030001036004400010240480d074816860091191300c003c1c02419014100c549985509286c4d00140b040140d00780400d03100e1b45445228101014406401c000d0044008211300b070740101c07640c03511a0300315628241c40d6a10500c4140100e1801c141e954000603440700180d05500459406085c803403110741d034505102519010804800b041c2c00c0000c0000c1d4001007001c00c058000e904100b90010515041203c5420580400d90340c1c8001034010344a20f1005c01e0280720405900d4000ea007420b2034900341d400780030640030090800c10105007040d2180034100f40701641c1 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 453522266 1250 453521016 453521039
    0x6010f05031e0f0703110a12080301120507180b01030507020d0801030b0613060b0a022e09060b060c0601140301020a200f0a05060f0105040c0c0209060102032110 71
    0x361400240a08002c0c059441110320311809030325100100d00803100f0181c00104180075600c01580103650050f0405004d008000ca825004d0300055100401c191201010071904010307681500c8000c00d007010700c05d9843c10601c0c606040c542c40046510b10180c00e02040c0001c9130400400c1d40c4081e28280640c0d01c80c504240d03241e14000b030121000502c07000041000c07400300484d035508140d029000c0d201942d0740b0071054041d1210386d00f0ac084407100010314144d034160f041143ea00c0c0313130000d6018001d5203d4888100740b24032040241742d41d501503c5031080e00c1800305035801404a111f0081c20684d545c0c000c42021034036a042449003417040580b1182d030f0b07011070806000700d90700c21005660710800c01891484861900100180100e4a8071a841038100d030f44004002c2c41134260f01810043c04603182246141c8130150050300894090380c245903843e40590b403c40398126886034120b60b03522030380d602c4500403455400744d0034420900380c4000701e003084440195003040b40110280c0340080500d40c0c540328502c10 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 453523516 1250 453522266 453522269
    0x110c04021809100821070615050303040b041a03060102070306020307030b060c0f010b030325050a06021b010501050a030803070806010c0b0c070506060301050402090f1306061502010c03090506150d12030b0306010f 93
    0x1000c40c0810054001a007248e01000804154204100a0301e40ba0004070707155030001c0c0c2100445907800201400340f81c2040b82071000c00e0300f4006c0701ea4594900000000d440d05030b10311005100da0780100102e00903601980000302c160034041d24568513003070440000c0e80d0324405920394420551808402d10340c907007000f0003110654044840c03000c800c0001c0954403941d0981004007034505004815000700056580d0005040c90318080c2020328118400620042c21a0010791016100300a00c6030100700290300c03c01034988c801d6180c244804140d84035001a00c1441e201c8000401106070b84040103600d101000281410500440844049950782c50a2508031072094402a41c8001c1a5000070f50a00300d801e42c0e558070201c5181c480003003400568800c810b43d00542c11100652484401d000300c910350920415400c201c09203001d00c5036a455444894440c10007410540101d01020102c0403a502d0f14032031401000d51103500c004441c4030f0b8175801801031400d18115807190080c0341c000140700c04103030003010 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 453524766 1250 453523516 453523573
    0x1b0e040e0601060e0f2805010809061603020d020c0f0f100603051905100c081e190b2e03060506030708160c1208090d110c040218091008 60
    0x1140410100401c0700f54001c2c50b40d441c0d4002120300c20fa59462003042455034880b05104031140c0c0c107600f002c0000d000312744000c0c02c881d0540d00480400c03581d59051010524650000c0c2801640c0710b00400d09603000c0d20036200800c0c0207200340c0c064510324582c001035445a00e0604c400b920030304240d5400314010f0f41c01a21019141e54006400b0b03005070745880310f0651515214070103d0701a032400542000a0354580c446030004034001d6801c010600910740e040450704001a80d95030480e160600303040350080f00c0d0480f200d505a03a01c0342700c1025922040340e100040c0c00700c03220101c0825400100712144030300c56030404000a0030170740009414140102581e008041030f4075492115603d0103210700d1013070300e122a9041003083d003001590114a40d0f90001c0700041c041e580b2201c0514080e4102031820186110003410030802e07915090f8625000701d1400003203502242c0250b034490115090192800e46160741a0307000114105004c1441140c80125049555010503205116070301003241c1c120241d800c1110 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 453526016 1250 453524766 453524777
    0x210613030e060d06210c060e01120b0105091509030106060507021c0303020706020f0901021b1e210a050106060e0d0f0606090501120c05041a0904061b0e040e060106 72
    0xc41d80b0b00d4034402420642c2c100000025050b40e030760550094000d10a8942e4441d40481401da81c03c0c41040244000a00424201080d07549030800000b0703d15000549120400c9a880e004c00c03070b0582c42141207814042d4001c5c0341c0100140c440544003a03580c0300c039007528483e6190110000d090360054080d03400c000e4005101c1c046540d0400240038400051400c11010180d080181100060b02c0384064611060045801d5845844036400a481c2103c0c00305981c00c84018010354281c5580c03004a0801028180f01848800707440005c045204910004002401c061a80e10202e0001e50002480180c29029a009001d256aa40d5058420110b81d03860035810007040034058010440303001211054600c65000001d0003035949125804445d02a0400307244084a035080c0c0091000c0c660b042c6001d018215401c01480ca440300b101002102d1080c21540201c03058800541440703a59400003115600c84580d0820040e150040140a51905009544100d2414100f1251000d0020341181178442030f8440 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 453527266 1250 453526016 453526037
    0x14010f05061915020705100309030e0901080c01030f0f090303050708100609091d010903080a0b03060c030a0c260130241a150f070318030221061303 65
    0x2001c0b80076440b80d100f07500754410301400140944900b805019403510b143e80c005070942841c5401020070864402040c070901c9070100511010001140c4500ca05009003400641000b81c00030410181c8140528040c0786480c0c25110782c00e143c1c02da040544940075990707907183c040e0f6844c12040c5481c4c42e14010400040e59080f1b0521201c81c45a0280203004201c5280d000c001c2d000d4011503083d1170015a00718000ba0480e018000000d2170b40c01102d0340c912007203001e080f00345890b0941d04114000204280d010b141c44548140d1010300541c070040001c1012040d903c140c8004031407142540b0000c5c400c3c603102c00140e0340500c421000074254882c00007111030352010b044401e61282c0160b03000ca00c8915a503120b04e10750b203a0402d0824070406c401514100715200c54403004c43c0c01c10080c4650380d40258a400d104204500e1080c07040300444107a9941800d200c49541c1d56061980010300c42604000d4000b10741c036080280401d0010b8a12002d84514002c03520203540c0d01d20691000803800c10000c3c04100c00b0480c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 453528516 1250 453527266 453527279
    0xb0a0e060f030f19031b1202060105010207080c0609040605090f060f09061c150c0c0c0b070308010e1e0a02031f050a09200a0c050f0123040303060314010f050619 71
    0x890100c14000d203445003003407001440b1348a02820f4070034102d41c1c1d02030100303001f40d940b501401003900401c424005840310ed8a051480340d1120400081e00d4810792002525841c0c66413075070b02035030190401400c414851f140001d50380c0034160080d910b062182e14030510500481c81c0c030700354441c8580005001e51020700d99119020a82414400c801c80b404c064131846000506810310418001810135540d925600e41d1030304005442005603049045042004c1140001003a0402c40f124112a0140d0715604269286440c04c658801d401044601c0b81d01c001081c0f0400c00695000f035801410101d500c01001241401d04001c40d0805101c1d00707420000895042202c020aa40044020600300c2d0000e00b044140703800c42000c41c2d028071884408103c80c502c0780828018100310010620002c40d0081161000e01e2460444240044465060644015002400300b501c42d412820003158050011802c0c0c4220501c614040c1c040b03c003181411070710b001d0010300306160000c2100008400320070400010350030400c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 453529766 1250 453528516 453528553
    0xa030206090414070c021c0c0b0a0201020715020901120902011b05100c080405100506090a0f0e0717120405100804020d0f030c030f0e030705040c030b0a0e060f030f 72
    0x14056000741c3d6019107040c01c4012101d06407103200750355102c0200c0d03003e5104000490600b03c8494030003003500742d01880054411403000302134840002d5000c3e250400ca0b2003c0b406442004001000c0f003001a000e00c07602001900a442a140242c89a1000c041e100242000b140d00034900a030000343c0800d108083c010130701c0c1d42e2a008034020000e99941c600307441000300130340300642e0381d960001d0500c030300300000c4c040144141c0c40b07440c8079644280807504141d00081c174a035402508100d001581c43c18140300b001c0d070a1740400340408104050703030143e1b55108445036030200c00c010140024011250142e00030026102202c2c1940c0000b410300d4203414180004031558600140101c2c0c0144c03190340081c000c642807840006c035407440b955504001d00070a1900800c0540181300c80c1c8188010030304103031500d81c6c0200d0500103841c0c1c180d900260340100c141044000e094500180c03500048800d0700403031144580950503214a1080d2041e001e204d485009050f03803043c02c00b0700601950040c00c460702d20242140d = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 453531016 1250 453529766 453529777
    0x315140108190e0307110102010c0c0b01140a0914041e0201020703080d0209030304030516171908130f090b060304030813081e091504082d0a0503030708150a030206 72
    0x101c40009602120001c3c49244d94070018080d00c401903d1203d8000b11760b4240110011f8040da8540b180b90b41c40c1030340c2e0303206204006000e0605001c40c01864540717161603045400000f00328048040c803d00890541a1500d43c0f03068506075210002c40d4a892000303c0750720b00b40d222180e410f0740142078491a40d1034880c0300340c204c0c2c41c810b003109400f048060125075080002c4d1015600401c0508485220304113140c0049038a94046101003e401c024203035a071401007031a10007001c01c0071094405880c14980031000c2d110b08081280c410812640220b05030441461110550b440b07200c0401c0900a18001c10034140000c40f0020000b40d0b2440010346620f25034035103120000d1052203518204040c4130480f020f40f012120002e440004040340c00b40303407490549400441942124441450241452445512038810f007c481d4110340812015040000f03101001601d0040c901050b0b40c0c0c1c07008680380840e00ea03402a948030001a0b0340e01d000c18035444070003079203080810000301076007001c40c80d56003400f9064101 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 453532266 1250 453531016 453531061
    0xa051210020f070c08102306010f0c060c0905090f091c02010204030602180906040516350f0c090d0f06090b040501020307020f031c1d0d0315140108 65
    0x284210000903208040d100d020700b07580e00241c00000a00c1050740229056140c5500d9210f0b1940c0c01311f9024015803040c203421a030b007171070840d0159400c9002500c0d12140d0901c024141880c3c140e030108840c1e8070a00321019a1000c41d174449054541c4e82a40e410044280ca12820940041c96004800d11780f1114100b0741e40003d00001d42003039603c3d2225401c9820000054044030382188c0302c0d1000380340121507203030f215408072020010b90134206081c0942402c5070414a051040403410924440c50030202d0200c2e00e000440c151800c250011a541c03600f0360107840440580708117801103040007803050280c4007600700180c401c03014950301e51119910109500029128165902d0f25880490000c2e4401c4c2d1150f03006030300269507800d200d18002d180074411151280f15070030a001518214201240c403d108022131900440c154001440b40f1841e1000d8031344908482c410300368100311283e0150004031018626081c4200203075035500c2141c2e00c520071381c0441ea00003801c3c54000b038113110204210782040e140 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 453533516 1250 453532266 453532297
    0x30206013b06031e0703030e012f1f02090118140411040b07030f02160509010b07050717010e0601050d030c031d032e0b0904030c050a020d110a05121002 67
    0xb0144503036201c0c04800051074554000c85d6042c0240341d000103e05028035400c0ca80000c002c10108501905920707a055210140ea0b00c00101e0307a0550317820013099021407010484160034405400002000754040c0103202c0c0801c002d241040d15810740718910000f1202d425006800c90000b02c0100002000f01001003948041d0a00c00414071384507090140410600c04d803291454070031f5591000e842c1480c06000103000b840d8075182405551106070540341128107241c0100e480740000e04d0b03c1410040076400c540004020368802d600c02c050705410403005080200242ca005903216410700c59010450b000240200305d040803440c00103403040c02048044034000d01c00d4165000494000fa040c02d06555801c02c00601034a4000040314000042150790600604108a10010200400d150140040010f000d02189009440c140b140512010243c294010b00400c1c120700e0928007101d1030406200040d01480506070003050506010341102e02e086250401003054520000c840c1d00070f540640d09100c2c0c1d200707 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 453534766 1250 453533516 453533533
    0x7080c070605180f030c10020906090303071a01060215040b040c0e2d040302070308070c091506030e060601080610140403030e01110111070201120207050703030206013b0603 76
    0x40880c03080c01c0c01090301c801d55a644400c420303070709440c0c111842c200b65015042003003a6043d0000004031fa00c5400d0b02e407040540ca5a0142002449500030780c05096014080018074104000c40540d400c40e24000050300451543d0321240d08aa82d440346901940e000c0c84600007240201d00107103100346c0c0c880c1c42904401259525048003517111603003036070000800162840704801c0c16454808428803900340b400d40d0465841c0039180295107030042e200103410601d002880f202440440d0b442030010340510f4a06015159508038079007940c80c0580f00700c0d00003914182e2090313444440070071164043e80d0165210034060f10303031030204590008051001c005002d441c1d007520040b004000050302c000c500030b40751440c1450a0748005060300940c1082031190b40d14009a007030000074034030203941300941c0a10f080210140311000c088000c0c85480700c00f500900c07828400000309940021041d041c2c800e80c803046101c55410403946543c44541c58911603d46001030604140c03590003ca40c142c0c4031714000c0850f038400 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 453536016 1250 453534766 453534773
    0x11704060912020c030d1805090c120112330c020703021807020c0303190302030606071505150f0604030f03020a0b2401080708070828140f0f07080c07 66
    0x40b5150040c12015030010410340c65145070a000000b030041c0e103803c10f0b074042e6610301060080800140a024070a19404c004a903e04030710034281d039844010105d0070111541c41d00403100c40d810301310700c084544000c2c81602c101009400a0703614101081c250785000703240004140c900141200714268011032042407000405030b0f8521101c81c01c4250100007485042c1807689000307040442411a06001c2d5004102048007110a1880e802035143c1031b240050b229211103002600c01d00c1008030140240610030040000048243d11250042a4450385840c2060102042c4021801c54107002603025006000c200080b894852a98034050310a01c1590b6000d1060354910b10192019101c903090f11f501c1014211016540445140742e40109003800100f51614100003800608018008003c008524010444200f0014104101e89100080c1d502c8000080710442c0c0041c41003110826400824101103007010310707c440340c14003964007a0b0007140300750f4540c0025981c40a01a205240300001088440e012 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 453537266 1250 453536016 453536033
    0x33714010f0b10080103150902030705180f070816030504050a0c080d030c020307080426101410030302030301060f09030203100b2701210503030c190309020117040609 73
    0x601c0c6060800296182010090002030004541030b4400d0159040c010b1011417045007a03c4001e8010b10710200d1401514800309003445030f80da100d250094250240c02d0a5001d408110700d05c1781190211118035503440c184211b40f448029030b400703000c0d083c0462103010038a10070740140e81d005025074202c071340c5604c0d19a501d52014866a00c01400c1e0340003c1c140589440d414011003100c85072a10040d414200540c0b10a1414882d5100f40d01c07540b400100e0810650780840c5800c0c0f03c148258040e14903842d2480425009454541451038002c140c9000258041041c481107005980c0c0586c025811a820a5016212400394162402c240a1348d0140040140d90402c503080c40d203150f1b590081100807070441030250f1131400388042661800c10941c045d070000304066200381100c1c2d070a00c510812071000340c0d8000a0128004010703000d0302002080115181101c07005001503102600c80d82d61083c1c440c48203c0c201d9800c1c2c1402800908104a8880a0300b40300707010395040f50107079400144001d01c03580c0f882007 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 453538516 1250 453537266 453537281
    0x61905150408070603050f06130e060a0f0c051c05060a0b0a020d03050c032401050d050a1a1e01030f0b03030703030b09011e052b050c03371401 63
    0x80c0030000074140035488051040c07800030602d5080074061070400c106098034a09008021318000c0d8100d0701a040070107040c0d00315185030002c0c603043c3c942070b0030301c030300110003808001c3d86070440b8031b082224003001c5034422000c40300900301e14803200c14090a100130710f9010300406410258060031124002c42c8000d10314004100c0c025680d001000d8881030340305c02400b0b49800900d011049441801004003031000c0040f05210000700700ca21406000c0110016140ca000b01d00180c80114a020100322481805601c4a0805030040c4002401c500168080041c401c4546201103a440c00c00100404654003d80040c814000110340100d840b803440000f01e899a00580d0041d800030351520f84540c9a400c1012250380940b1000507130b009058100f51251a803082d03d8410306000c0c02d400011071031045040c0510411800b2b605072550803010391400c2a6944501e1600c81510a01952290740800040904540440d01582200004404c0c852804d1001d030140080190382d80c900040303800c2083c0a081c400d450 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 453539766 1250 453538516 453538549
    0xa020f0706020f0d0e010f0e0a12060902180c0d2c01050a0e0f070b070f080f2106010f0804050106410604180e01021902010507080609061905 62
    0x12580c3c02d080030580c6400300310034914003446105011100281da02a0900c40b503030009013004001502041c02113004020140d021182006d0680024020052543c00c194030041c02201c040d5405620b17940a1150810b05a0341c420003218100284909030190f0f4001080c00c08980c40e40140d40c8585002c681175070400c1030302030700701a5500d00400802d80c92522404a03080c540000a183c012100140e25544170901d0103111500032011407002c04003c0d200c2c13285c6251940c41045da0361245005082c0c1902074101c1d103403414503002d02410707017a02d00b00f101300b00a105c1c05c0141e55210030240c100380260352020740a4030513038995481e00c4000c1001603c4c100d0760508500034640e118124410035103000828400020b40c00b01c00c0c011641f410403184e035128192000d550112170406400300388010100b00608066210301c1030f079400450707140b104000c1e480d407626115410341c0080c050350361540c008494220049a525511010000208100b030411829052005030000311400700c07551210001001c144d441e2070b086 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 453541016 1250 453539766 453539773
    0x6050c040302090f0105060d111c0605100c0c1401120501080c150f12100e150103111207050c0a0b15031c12020a050409050a1505060a080c0a020f070602 67
    0x400c11810000c01c1284e01600c01d20042c0c405505140000c0d105d4440c010904405944035190f43c018400c10004a40c01d20014542404c0003083c4500c52070080c02e1144070749803107110369201a0317054602a0b00007040d0749610910703461000b4142000d0400030081c40c3e110754104031000031005100861071041d18042c24401d0000e01c7c0480c9400c0c00c10107a8524070350b10150741071003405503030700240f00c140503140c40208455403d501651030303030105001500c1640c0582d1240d0b152805000031300003454100300c05a0001e1b038042c40b0340c40401c030700000301d0300c036a0259202a08050b030008210074462130241c455980404103a03400075445132078014030b4000556096000c80d2131010007400354a130801105d07005840c01901810711a142202c05024000003000f81281c1c140c00003030852405204100700e902901e410401003103c2d00f0602048001005843d0700140f1500c0f05074008241342c645203050b902a00841e5035403103541d0350b034581401c0e403a405c4801d2140c01d500c500092103c6002041c00755001422655008 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 453542266 1250 453541016 453541019
    0x4030f1e0206210901020a0210050411190f050406080604020d080d02040b0408011a180604060f17070806060607080c07050d080d0f060609060c0309080706020a02031b220906050c04 79
    0x100c803c03c0300a0100c0000743e06c1081030501e51900400c000c5081054020001156074860070907492152110140a43c001586180c1303a070a07411012400c82544c0e40c400c0b01c0150103444a0034081268018014200b60b503111000080c0180b07801041354002c94440c42000e41085003143c00002603070032980144c4182040805d007440712220034450090004002500584400303a620042900c0c41051001b45103403012900c00102251034642203c4010700c100d02000c1200c0c0e0ba14142030000d148060404003079401101400128120f00040003400f40368014425440d050303142d6503000c0950f029000164007802140c000003400e94a42d04c0c00d007072880c0500c0072990741d811a00f03a0402282d0500440301c0040c2d141c50400d2140300d0b441308520054401c642011505141c0508054410b5603080d44030382d005129003907002c00c201d80d000c01c204c0c030014829000c9800e10707107105844140003000044060f40014980b400708400d044020f0314491445868140041c5000c500d84a0300103580b002c0742c6611481100090 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 453543516 1250 453542266 453542317
    0x5180d020415031505040b0601050d020f04062021070507080706031e0c080a020304060f1104150806060f0f0c030307080610050c0c3d110304030f1e0206 67
    0x8901c00140b04c00d034010051480c007981c0d100402ca4000d4100d504125001c50707040042e64081c0d044400e594455032141d0340355a50303420020110b44030040e0780c0e0100d0150300450a03105a00207080e02420a0003c0340d265a1060400030883c90b0300080800da49034410800700185d2101305100c050090000d66501250003410200b2045026460746e00c00ca103114502046008010743c4401e07015040102c1800140c0c0e203440701c1c00d0150207040c0c44135000a0161820f0342d12010100c0d200d00600483c0c0301d9004104094504030020342e00c54604660882e0084010000c101100f02c3c61002001e2000c0000074003420311701688229461600110780c503001103801c110501c440d40c9001e412540080d05e151401900c2d000150640503100c1c0400301107070340030303404284400c8840e083d000344950510b403180e95070710140a508408104602e00400c800000b1480544500d000f544c0040100c509a0f03400040210500c0000d598500c0f2130011404003110650682c1c05201c0141c1d0703084002d01380302610340c0420040086410 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 453544766 1250 453543516 453543533
    0xe041e112b060f060c030f0c02030609100f0603030c0b0705070503190212040b0901200f01050609060f0105030705130f170f03041413060305030a051306090605180d02041503 76
    0x42140e4400700c007240c2c0403c0090313800042c2045c81503140c90a41c0c42015110303030a984010202400a600d4080c134001c00c070b80c010380080d02420300500300c01c0034081c48a030a00c50707504655940c0070150009108084610104003980403090b080702480c80d00307900d0b146868a5140c01c43c0c200003840e510511707800c90100c503070540c100401891001d0f01554546454030303005801ca801d01c00c044c0340d0390501101d1045440090200c980d00c1d92880c0c40402601c43c50000000d100b8020903089030901d1040c00d0301000f141d058144045203071004030068642a10b540c8464401b6030f1290007140d44114032040c1e0300004210640d01c0103202005103642900c03103544003042e905080c10301404041c01e03115540140300070050580200414082188165820340544004400d118054141900060010320001815208595200b401440404015005640707a01d807107000c00c03590304815100c4c560000704d0070f204039500c0c1000104020440c90000701100e4408060341d021030140ca03040310b02c14200442c0c00008005001c0c14a = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 453546016 1250 453544766 453544769
    0xb180324041401050f070f020c04020c07090f05070507021c050a0b1e0f0c0901020703050a1a1006140d0b0a0312030609020319090309091406010e041e112b06 69
    0x4000e1100d460841c40d50a4400c0004221b207082185055010080a0003803110f03890012004c0d20641d52120f042780d489944000c00e1007410807407481c1000b420f98000a80c422a409200c0343d030b840500d1300603d03408112603c2c2d4020440d00000403c42d2454001a070200800c044182c410780700e41e401b0b441c1c000210003414000400860010072400c003000715148000d0a40c5900007528000542c45010300e10040b480c11640d5040103000d441031403402001c3c0452071240c050320030b41e551070035401641c4040c94626404800d00c6aa004508006000f0700d5100030103003c1c05140300c0c0c5010008000e014900000d008c20a01e51064034402d014103480400c0c903a1501810015241c4ca00b0150f140d81000701944003101000e010760100c482c1e44130341c41010580300b801039000500030048203200c4540c0c4480b0880d00e100781030fa0b50701d0100c1c030fa80c0000005820315026054085591111900c0102501c045009c0541b1003500800785904040041c83c207840c95840c0c550305800e0720050810b00c001c14110074a0100e0317103103 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 453547266 1250 453546016 453546053
    0x60e010c0209071110050a0504050706111002031306050f07090f0501020a14070803031501020c0409021c0206160804080d05030610030e07050418050c06040b18032404 73
    0x12089003009a110309040320307042211403a1104010180518407420800c52051920070541400c060042a90780e41e0000e41c0214007840680302401d031780b4441a20034042e42031101000b90404020031072603100c2c59000d5603100349400a0412035910031790f102e8003202c000300c4800032400da00e0030500c0700c02a031002100740600303a0102030314003c03414900003031f55038180c0c800300401084c0c00440c070b0743da0880c0500c081c02c01801d00f00120b03a02c0b0306084510007940d800458001d80148221007002e5845d10b000e014604445401400710105d1254103810220700d42070015080c0d802800030041c140c017240c000035401d02042d00030303542281c0f00c0c1d04103050203040002824115080110600034001c1c5c0355034044000c441d080c4a0b06000034101c4500b810f50703080545030380c0000e601030300e0a200d802c000260081120500c41c403c03400c2d18256440341081041d140114007920b02c0c450700501042c08450844c48106082c4040182101c1c20812100038540d040e0300900310011103400316030240020405103612000481e8007 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 453548516 1250 453547266 453547277
    0x120106050a09090e0a08030a0b150a1701050f01360806010e010308270d0305030415270201090e09010225020d0b0606090405070201060515070c090203180610060e01 72
    0x2201d44c04155920140f0601400c5000008041002d0065560042e0105c9202030500c0f8422060b0350420901034220b05803150109500b04a040c41c00400380c1005410b03100e00600302c012110070140115000540160742c00240011100100320180c000440003801d6000b86041c848014100345410f0b040030f0043c0e0000003015045c100620000d038402d001e88444180340a507007100390404080603072513031a03550300e800e4004500d00140001c0c5544103008511a034043c00510000040400c0303c1800c44030048003295150703038400d02e01c484090050f0000214180140750100b000ea407682101186460107aaa00e42e0aa42c009400c0c95107080a030343c400d804448030316031070301080c0468012411505175031400800303880116000070740c240c3c0c1e031209407104a00050420043e038170705898003034020011401458420100000a2035a40e11484c044403461903001490100082c0340c0b9548002030b400240082401105070015884070f12070400c60180300d0b00d60501219101480c05d14050442000000b6103810800d = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 453549766 1250 453548516 453548531
    0x141c02060702040213030b0c0307080f04050a02040c05090306011203020d210b04020417010911030316083708060a0b07031119030c0c0801091e02010203120106050a0909 74
    0xd88800544081c181c041c2c8025984001d0020a40c50952140d0402800303d00500c0a1100181c0c41c0c0002e90710490b41c1e41c44490654588211040c03940108540040c1164000000c56006042c9504903841c002404c2c10914100042c1034002403d00d8001d801280c8000440c030070750b0080c1941002021800c02081c10303e6030148031451007582544416510701c5c41904e4564110207920f84940d4121002007544165078007105608849031400307040220000e440d0940e0701c04035584285030100440b14000000701120f0308010072a503503c0c04c5600004041c070000750015001240c1b40001e070b1400380690600d2111980d01754010040a4801c850150410b0301a030b060140c18041408010304072184e02d909401d18010140c190781c2e400d0310306004002881072240d98002003d04058200c4034101c1c107548181034045007682c684a07030030700700c50703000300040c0050f00200710190401da00300800149050061050f00d203080c840c2c3d070603010b681d5800c0e401440009d100041140c140ca81c4181c1070340103801480420300104 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 453551016 1250 453549766 453549769
    0x8031b090901060e0d15050405070504050126010e0a0b0a0f0c0c061e0e010e15070c1416060e09060102010e03180105070609050c0114070b07140c0106141c02 69
    0x350814001d10040c01134010100b2120b41c0c035040e81007032055010680702c03142d25843c0a60390107480c007a0b07811a0f0b14400c0380303404583d500d000e005007410b0360501c0301286040c144d14007154500c016042010944d655884900a825400a02c440002d207030040117020058141401c4540440d40c404d54011141031a010700c0042441d0f2029503207080d56042040030400d036521001103281a104484c0c0c0300c101900d03003440c002d00c0c010190414004650190300f59200019030302000f855114003150100300191105010301d000414090761140c146100600301c031190320b50852940c55a4005420034130125640101030101407074043e8109a1206081c8002c0c000e0a03961648241e40340660f0106085114440344030107103d91207401a9104650043d209000c19461410320301e0325501d0680300980050f007000201010700c28080100e40039184d019240800581c0d81349411550007a4441100509410400550000070001d0158074003410601c0c194070381c035080810820401440f15114189003201c10004030025 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 453552266 1250 453551016 453551029
    0x30c0f090a0621050f0105090910290103051302060c150c03040b0c16140307050a0609050c0d08040302010e010e0303120115024b010203041e021c0204150308031b09 72
    0x4440c015100c8200944800c030000303041409203072b150790302e1514105805145281c2440a10800c004000075003804a01c0800110283c800407210180c80f1000c04010342c00500307040000b04210301e180320907617420356455096000300c498152103214000c60302000f44014460720b508025000341e07000c4103007858030000c507909418020610324060000710150004039406070003801204c40313155124080e68092f00c241d03c2d08000a0035444810765040c401c030501e6604030709020400c6003500b900510018109840d5500458014240300c146134104480500030741d0b603c2d28200007400d030a00740040b00001a40c100b213141e0920107140003031082154000e420010703000c20b440940c0071411801c01c50a06e1441d40048070720911000e50101c440050a1100641200410650155010701d103d60800c50769003c404180084240080d02c01075841400d4030300709900c0c1a0f200b032010908620107000481c680c1984a88170a03021165071054800410001c208035000f103031020b0311076180c8400c8507040c0c01c02032000e000c22034 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 453553516 1250 453552266 453552269
    0x5030c0108040303111c1527020702040e1e1f0908070803010b0c2b030f111801030b1f111218040f050c030c0f090a0621050f01 56
    0x10700c805180850241446508020450440400c1d00c96907019101c200c0b20898003458030640c1d0282c980045012000c0120540e07034100c1c1c8078014808215045010f405101c0d100091100e01402c0c0d00b0002e03440142c82d00e00403480c8445109010701071186141d41094000c801a903071b5402e154100d040a18400c90148000f140013030b90340f010000e01c0c4d049625260340030388648e00c000b0780020008400040c41800400c0140a00507108081d240d0000110b98101d5181101c0499201e50b03001044038107071341c1442948240380c252100e80740402e25000d5510000318590208039410b0585640342841c2c011940c150050300d098160903500d10201e201c6840184240d01580343d039240410207401507403010b0400400c40400e1103501094069503891076020b8800e07243c1100b2130154000c605010844001070000d2003054815510b5880103861a07a0f54403400c00d090344191100f500710f01062001040c50b80725046aa4090100c545400b0101044401000400e1a082d140c1c3c0a0103801c1104101d881918840c0250 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 453554766 1250 453553516 453553519
    0x807050301120206041d07090b040815190f0b0a052209030c060c03140105061309020f130915080a120f11150601080702010b0603060f1507081905030105030c 69
    0x140b00c09440d10000740580714a61004d001000440c1800007007110080d1071500549664039081c01c0c46030b54a01503512401203110f40000360b04914401d543c00140c1c0c1c042c0c0e5034008006100a04245c85858003442152540030b07984040a81d00e40d04044a8100a8000c02c040c200c226480c2801b02c51080c1c01c020b07029040240c140085454040c420f003054003070341080080590241381840001c04500004009244190700c4035540c1c02d10717100008103410902d003142c0041401c100135140d01401c1000420196004041400a42004210741251100c0301c40461000c0d01070b92070b01240e503459862941800c1540c642049100303800c603010740000125403400d007403e201c2c11400d11100d0740052520903107800410402044890085103591b010300040c0c2c1000d2482043c0980b100d040c55120b000c012800c0381c0e2010340180d0080d00800205845162010f140a0303562402012190b035030340408048109900523620072114070001140ca52140c0e80b00d0022104503490030701e000303402c541c904000240e507100e0524501c0d = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 453556016 1250 453554766 453554789
    0x15160303021b060f06090f060904020f1513081f0b01030204090504030324060207120203010f02040e0405070806060f01050309070f08030c0f160e15040c031b0807050301 74
    0x404060090301924049111a0304810b9052803034400c1c0c0d92218400c607500c400c0741c010b50000658600e080464075009041d682a8004955203110078000d040a0207070050740d02c25001e16030740c1c079565110b01b0030014011900410719242d15111006220079011030f0016860358100c1c4150401c41134030741807400c10042415202240700c45800006030300a20498000e4150142440308020525415402401622400c0c00f010001c8990300481d4561340c0200b07015040068000400401c0f4030100884580d408900040000410300f0b40f101900e800ca82c070542c0320f1090241510208400d0280500103140141840e0010b8847c5280101c0001ca0121007076504505010b07008c03012800c0c0c0407080050700d02403d40002c001c02e015483c1c01901d0382d00c2e0840d21a8540504c140034510501d26004502d40c000f184000c240110385d0f5040910340d40a98100911a0080c0640700307611584d00da9a42c041d880c4c201a075600c00264440342000f0f2445480c640703081142c107003e072010078446403640c401d00322411580d590400 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 453557266 1250 453556016 453556057
    0x1209011e0c05100c0f0e10030f0b0306070206010312080708131b030c14060405090403030e0a0501180b010801180615051e0301180503120618090d0e15 66
    0x19240c1c040d5449018003548226501d80c2664034244e400041182c000b0b03126010849000d031800ca4000c601e9022041e00400c0c04540160068000d803c003c48891001d0808510403410101103450a07500b10b9607000141c1c052001041441130040794480762042d180342c03585d85458190009810700602070000c03602190341840070300900107941e5180c0c07191351111500c20005503a9040c09180c0f90018045c0b0305c414201c04403070b03040c985400b03030071142150f401900b41e10503640e0b192805e80003444154050f0680f40101e0b90344a0000e5420720031807002410141070f070a20f0361403600317000a840d94140c011000c641e241146408000c41040090f018469002c000441c02400d0410b00203a00c0466602442d081551502a120000c84211118080700410f40003041500d0300c1c4d02c0e04110010280c00003074015002001103100301e403000908158030031000740038a840c1d08400541010110400c8600e125246c000000b1001025030007075048404c41d108690703010300c14001c15070f5079241c0d1040380300c02030880c03440249 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 453558516 1250 453557266 453557327
    0x5120622051b0f03070806061c0c15021b010c0b07090b040f1403011506050c071503020310050f060a050d060503030304120909060f120c0902031503120901 68
    0x10040c80056100c01614038264aa214041c041003055103030602c43e42001d0900640c40c00c00290709001c0b240e600005103500d4440300c080c0002c4c84a001000c6100c5580442c513480411074020541001304103140e98114030242c410002400d0014105128031001c40c01c845425403603a200c2e410343e41668116014840688614500f62002034459100e43c2100c803020400107101103003c1c40c8841110390540300104040c0f040030800d401c0384ea5030503480e20b41c031507821020b2203818403440241c0740d001c18cc1d60881d20f18907280c4c0c1550003100084500340001903000000c01000041d000300c034100134030082e0341103445c10b025000060543d0140342d409008029002c01c1c0f400304010180c00080041030060162381e50307420a0708288100000004599000c202c2e2810300041c50308030352082d03104a0720402d0000890a0810f004007981c100c00000540d0030140c02c4001041070702c3d803480114010140020f00440ca42e802c442403500f0112456201c10010409200010507a41c000540ea0b02c80b44081c18404c090600c601c8 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 453559766 1250 453558516 453558571
    0xb04050c190e040515030f010e150c130e060f0301050603030414180726010f03060903170a02300f0912070b071b1203050603071d0402010801051206 65
    0x480d0150f1080c140f1040c02102c0401786001c0141d040e06905444001c40300280840c01c0c0e43e01414440003e03882001c0b000181e501406400780c2090b0b0880c000c0d440c20b403000300b10b2890014690444410b00740030314148910380c0341010702e00d840e0f81010340c000d01080c94043c00003a240d0140e0b102d0680350008801d040b912568945908041c00f1108480c0d0701d1f1181025800100b407206803442e04d6401d410030048004009005111840c1215413080d500040503045540b04409484407003011030900084800c000c101c0a840440c442c42000b10314401038541140070107242001c0609402141c2404112004511410300900303040c0d030007180540011030300d494445010349040e081d54400301003250301007548010041e00c880450700466640c0c0da4002c1404201000c450f0f00c043e40c92004180075182402181254042d07001035a003d1070040c00d03035a015a8501a002204036048004000707140d080040208640e0000d0b0745501400080d6036015810580007031f0984d80d010058106140e48031780c00550301ca80b0002c0e4 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 453561016 1250 453559766 453559787
    0x70c02010e01051c0f020304050c01020a0f110d39061709031201080d030506220e0304180207020901062109020a03021c060b03120d0f020d0c02030a030b04050c19 71
    0x81005c118503540880b4100094005450494881c0984c090b082c0240d032001440107c856007001030b40750801d030780d0750351031070700d991145a02a000400a200000424070041040810300c0710b01d0700101c260003a6491080b800348445c034030160103242c030000034000760340d014000007003003040804580c0780c038ac4403545038078994090702e080e007801c440a12001040d030602c00309100424000d280c9007400280c035031408200c40425150050107040c1440c0040d200860490307001030005400c813005586c81c0c80c1c1c48200346503503065006d03840c440c8550000349001c02c40c188040014014400c2c0d150402e49040c800c68042814503100611441c150f84619403a400e554600e0800c00c001d582c0188801c01e14100007800b920421085041540e00c186040d062174142d0801040c4040340e61903101603d071030030007580200d100618010600011060b424050280c08801c40e1040c0e0fa40c1c00a0340c0c0007517844540f080720040590b13440442086c05135091000744009070038898107440315514036107184590001c0d21003040316040c600 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 453562266 1250 453561016 453561067
    0x203060409120c06060b03040b040b04020d050607020f160b03010302240304150c020a1113110703050304200303040e040602071b08010b010e0303161a07050a0305070c02010e0105 78
    0x10b641460b1103580001808108521038001440085e40e40e2001a4540c00f00300c070302400400600340028005525105803a60040c07004110f4595034005845072031514208580d4400940d0028281010511040100c03510301510400b03400412800c056004005000602c4020700800c10851301083c15100c501e03daa0000b60303030040301074480c50b160400c40350010248041c14041440c05130034604080c40480c84a40441d00b086911410400f040140002810302c0c000f460030b80f964030f00c1c2079000f00c41c0100060105a011303540d95522810f081c240100c0c110325402c000e010131406150715002948000c0262406c686044c580c5495594541c10110080c1c450380744000c09090300c0300d0f04000045980544141900c2d2480003c10840c500000107460001507019201da140e40140300003a00100035001c00200d980c0b2584250b94160406103402500a10903940b4401168003c80c40004041d854811182e01c000c2a03d80410400302c1e540028180720407254003641000380001c0c1079811018a0781142c5410000c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 453563516 1250 453562266 453562283
    0x304260d0c120c05090f090a06051203070606050108090d0c0602160507090f18020f03120f030a1505100e0604270b012d1404080c0f0619030203060409 66
    0xe54005041c2039205190000d0b440c80c03d000507108074411020740e5a04440600407403144181c0c40704210700c1c004001c1851000b2520396801140584039240c540400300300001c02141c07502c019180a4098400750f8100c4d6040107901d404004205400103614001c8060303d080602d4018468200f40c1c0280c412240c41c5842103941011040030028000b030680708030303001e0b0802040350613100c008038015a4441c0f802014202c06030180fa001514020700b004c54504002401ca0301c165094284480f5140c00014140720310217000302c01c00c00c440c80340c0c0c015040e5000403030b414485c01501b000c00103804000c2c0b00c0b541740d04102c850f4103400a55251107040b2400b60480801c1030070600460b14032901c00e0010440310b001c619003081c2000c104c95010f10f5041083d4070b0f0f0045040d601103828102105480800007180c010080069130015003002590f0003003000c0d00641003c1d042c500c2c0f03a00140541e62100c0310003540104d00c2007003a040f0b41098a08004440b2205240144e5651140c07000100034096010300984107a4 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 453564766 1250 453563516 453563531
    0xd061203020309031203070e2701120b07030212040609230a1505090d12090602160201020c01080613090206040b030109060f060306030305070f020607050f01200304260d 74
    0x19000400f400003940b0440403142034407101c200d900541e000944040d004100091050a624a8150380e4488501d01c103810072060003d5149280704c1b1000c080c0e11020300a0b18240414086c8155003281641c08031441c18250301d005105a8031082e00100140040d114941d6016400104038000c0080c1000b80a6500515106201d00013607a07201c03140e8600448591205080045082103940184c1d442403007210041d00e10032000000980d4482d5840c40b856441e144e03590b2083e40000c1d024805001c0e265400c030301d44810000035100191a102203240d0707907414011718038200b100ca603951b5020711003e8000310f080030414901c00d1003c20720300d00aa42010160340350100010440503d9036104000700e510b030044641845a5450054045844500020380011070803ca40408501c1c1000102521840a0000c0f854412651101d80c1015031034030b402d500e6030b5159100c042c0c0c24170104003103100c0c00440100741e13481e60400783c0c0c2e07035a00d45240241748509244101c254800d9000d00e50152841c1c403c04480a11000 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 453566016 1250 453564766 453564773
    0x15080402060909091b09160c14160302010e06030f0103080a120e0109031b0812190e0703030e01030e03030f09030c0f06060a09060303080f060604080d3906020d0612 72
    0x88910210340361107081200641036803840e021241a0241000d220300381016843c03000308403114030b01d01c1400d84003d03040c182418102030080180780c100c608800c00803010328bc150310005114280314807006200b0102403090113659600311452504695000c101d26a444903060000d4910355400d40512a40c0d83c5882108106520190042801c840c825a101074203a1144017540744e0300d68140380d010307007078150510036600355940d100c0b50a41c12a100e405450726079807140700700c10240c0b58200800c829540126078100300705500700c500920742120900302441180c030074420866880c04010002c1d002c1c5031060021400300c0c1000e01c01c0710b050510300b000b5260080c1c581a2141ea4500c42500c016005402e0945c000801d41214401c02c000da0754076a881207650b0315034110110b00c240300580000d511a8040000041d040010403620f07000f4021512808070b901002801000031555000d0401c0003a0a04041455405c0c0070784c040091051303100324010b0f150324080041000a03c61500300348000c8440e0b45852060 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 453567266 1250 453566016 453566023
    0x10020304050106060908030307120605090405010f0f021e031005190303020601051009030303051b0c0d03110702060910030b150d1505010f0c06110307180f1508040206090909 76
    0x201c0c001c01c003c0c01042ea0381d0300300700d0310080c0740c0c400c1c0c00d09500f090022802d800c1c8600c07001c0e502c100c40c10b200070900e0b0b03454038005404404252002c8401c1c3c1c1d99441302101e02c03943c9000705401c81446075000c5007082c1041f41c44044088801c83e45080710704001000621624810415402400300a031102501c1d8881d5a0f0442e90024140019000361050400006140c5420710140c2c2042103039544881c0039514640d0242d0203040007515408090400e182c02c50800d9042d0b4010b0b0140311108002840244a500009412105102065942c01008014050251301d801044404414013520082001c41511030220024405a1100c2c2d40c09042d1800d901c15504901003d45440c050a100c10040102456800807205020303104850214070304642054460b801004040c0c402406241c000c00c503061020030300489580101c8042e400b040d100030044403841c09907907036080138114410198400a00305070121000f400c1c0d0101070010444001d00140454488406880d0102c00203080060f2270704044d0581d031384 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 453568516 1250 453567266 453567271
    0xd09090e030c0313180603150207230709060e042109080d030516080609040206090613120515010e0c13050301090b0406050c04060e040209010e030f210c0d031a03100203 74
    0xd90245c054003000c00f802034490034040380e43c040c140004a031176006099010750004402070f41c025620f07a140305c00203603811030340c41c0103100c59101810805080820280c00c50360300d03801c44010b0103008420000020f03903160b11150700080c3d44145c3c1001e0351003400d01300c03035003caa40c021000500419000c0c5001c00e8043d00814000c60006901c0e45500d02d0100040380c0c1d5180484045610002c5800400c016040c44170090240c413202400340351400417050b40d42d443c01440340c0e02030358046d043c02400a0922106001c1c802081368501e03840202075142804d05500410058080e0341020360001c2d04001110b080440d42005000103002400030100c142001f440c0c1d00401c5405480103030801000030141e0074a1002c490541c0c2d859200c603614100721105101c001d41150030b0300c905104002c1c0721840940e5080046801039161580101501d082400e82140d04420064a140b81080c06005080a0841c08580004806080e00d40064204118040d10003a009045130050301401141164540329849030011403 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 453569766 1250 453568516 453568529
    0x15020703060501052704080d090b1b090109150203070c1404050901110a1b0b01080f1018020d0f080f04050f0a0303050928150f020d09090e030c0313 65
    0x14603030344c0381c051007009483c5003016003070281d80c045000e00c280010041c40d03400500442c250350501d481c410f80c8101b100c440c00d405039544401c500c00c01001e00c440d061101804d030380c3c4104c21804d200c942c00019220f00c0d1180560005011040c90080c1003502c02c0042d41c03401e541108203031009642c0c601007203182100c04038115000385d086c600018004c00c814014540090500340316a40340c00211001200c00106401045905144034842813000c6801200c1580c0a004c040c0084d00100700c014517101d00d48091882200b002c0c0e0f041c1844e04180d8641a0030880100c1d406544000e661034091502c480c1443c41c000008140c19400b1545038502a5807601400c19101c00391140d00c0c646061008000014203a03110042c005601000421190300300b104906805d1000c08030410307a001811075030880424140d4114811291034500604491a8004011980b0040500181c403c400708554003c110381c420b8040c55030110749400c1c0040c03648104004403507540740c1c0001135a44900032140542e128030098403492 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 453571016 1250 453569766 453569771
    0x110d0207060c090e18070815011d0402030d0c03120c0e130e031e04090903120b1c0308070507020d0f02031510061404090906050108011d031803071502070306 69
    0x8000e40d83c0a120796009a0791070f41d280c40c10310f9a81c1c50045c8405180f0300d07207495180c0260040043c404c041080b40040202010750340800e2981030905103030401c02d031201c032200000496014400036071008201580342421900c0c100700020b8246c1019281d0b240caa2480030f01a41c070341002459034540c004800003458030119411845510714107500d10581d00c6080000c49039070030411421803461540462480e4844031145080c1c1442ea0391400d880881c3c280c100140d001c12030342e01031804d87c2000c0c0d1142481e90320044960703000c4000300311800751860704d00e20b60003018403054402040a160050042e1000c490703000301840d50b02000d0b407800800146801c42e080b40a80301340000b10108030030907081244508119200d1113140e40c0b800c0c20450350040c0d01300001141c034804000100305075189004800340c4502a140c04541c951510008601311614014940f0790609101c003031511003000881203403001b1600c000e10070000200d4400081c24041150701c84100102000c3c003040d40d141d00400d4800c00c803800368608 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 453572266 1250 453571016 453571031
    0x260d06060e040902060d090f170903010507141602040209152101060212031017010902031501080304031106041508040326070807090816030605090307080306090a110d020706 76
    0xe00041d10344045000354400002e0200e84045c1c0d000c0e501405545008441c504841480c80d22010781c251480949d00c0070101300001c00c0c640b1402c00b4010103801c08910300d41188080c984843d050024011001814084c0ca03680280c001596503d4065444030315000740601d00032041c0300e540f1a120f40c0310718606819a1802e01c1a48101150041414120b4126130007401c003c3c24888c1581d60280e10050103a580d540007920045641508480006516080000005601500743c0105490445080895400442e00b2001404015008010b58003120351008044045840b0800082d01314022500040c0e21004e1551840100a0780711705c80b0781c0600c0c0a601c40855440081244210800043d1502903040d003404010981c054495548543d1000e0b0b00c0c031b000c90030181c5402420781002c4d1025807884e48813034480c4d420f006004c1d00b1300c242e58000480c18001e5180400d20399450589000080659104105c0c0e48001031240b90329410039000c1081d1006401c3d0303644412060031000307401c2004203541a40c500310341d = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 453573516 1250 453572266 453572269
    0x10201060b180d140102070605061c031209050307020904030c3804060b0406080c031e100b03030c010f020d0b030c010c14011e050115020712260d06060e 67
    0x481d0581c00d200c1260740c2a1202007400d02410058441088500e442110450504544c0a02c060080c4510410b4003065034240402045402020302c08007815905584c0072480009400a49008010380311030008200c135102c506000d802c40c040c034070001e0f4102d51040100010140c5c06104412128800c010410703494a070340c2c040c105d8080c2d01014180e409a4240c0002c446140302a0307455070300c40e100c0e070340205071a1f038428042800d44425611458469224070301444040c60180310325400f1407a0042d0142c5050f48031007075141d482c0c101c45c132074940056841d4490000c40d1010310468045c041200c0c000e000403c0c6060043c0000d511010b00e00c05001d2400d60342e1002440d000c2940c50b80e4000594074500c400c5110344400d0180139500d00d0b100340035980d507041c0c0707451364039000c02c03802000c4c001110009166140c481041035142202841c0000c64100742e03414400640481e20301c1200035041f100c0d1415540004c07800f45a4000c00014503a01c41c000401e002c40440700b10b030441c07421354100b541d03010110b035600c10 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 453574766 1250 453573516 453573539
    0x7090e03120c0f03061318050d08060618191e14180a0b121002070c1e09020c12071407090204060909090614070207060f0206071416020604060c0201020106 68
    0x18580c155890400100d0058642000d07220030850380c00d03100080700c0282c40201d10001c1f150b000e0444444c5c00171001d285a464009081c942c3c0124182d44103441c00c1903d0082d00020183d250101d4442d10401c14003103c90315506240b00301424014942d50204ea030440150504811180300300e80c4540c469404086650400401d000320f036100400724410107440d032011200241450411a642007985044a4031004508105a0003d5040c4030070043e0384144134180713141070030016042914030920340c650041a070344c011688a401c40e07401c104e0060311624802400c0b414400000c818403c440404181d410600c842175030400b101024000407103803100d65520801d4203030300543c030400000c00d44034a010480101103400c4100b00303900c41d03040021009500a500740310120290b03494401a81724542c180705182d0070210886141203207000034140c610b0b005e0740040584659580c4440801e5020075600152066504241c000d039600402264940c7c0d1036400080a01031018070a90040d070805e580010ba000c00c40 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 453576016 1250 453574766 453574777
    0x8011401090e07030507021f0606080a0504030f051b120306130507121806090606170604050c06180d05030a14030103020d0b040318080c130b0f010f0207090e03120c 72
    0x408a890b010780e240030080d001804c0082004003903000340c80c208150850400c003900e0640c14003810014a00341003400c01040f00000810801d042440c000034040802e80016124000351108c0c90122768680c0312150250180e0780d9400340c44000c1c401c01401501c88614040034501c00c900c1515405030459149000c0c5094a00960303c20002c900c282c0209508003d494204580c050340b2901c0c0081070b882107540c0c1608a4101e81c10036140650b6419003805101c010154520101c9444402002d0509164549036100d131b06010003107102c1c92002480c2034201c1e60085645194980c010202c5902c0c1055041c0b00341c807a40610000340008850081002e03080c80300302c00380c9058940240000d28280d000780d6600d04e804501400640c117104180c072480010783d4804c0381c120068000030002d00080480c45017803013141064888241c1c0440d08006194402c0e0700d07000031305240c640003460310042e243c0d107400041e4244181070300310320509400c080f0b00400f01c001c000001c0c000640c008880c002180c0e076440790b074000f50046 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 453577266 1250 453576016 453576029
    0x180506010f031707111306030b010b0903010c050406050a031a0d06090c06020f0a0b0912040914060a03030c020f01030e010c0206061f080f220f0201030c091203080901020f0301060801140109 83
    0x140c5d400f503103c0d81440c5100c02c2400c009a600001c190341c8030303150008500c01c03d030f210440560700085c0584c4941828014000d041d103890405904050424501400718082c80144034209940c400c03038218015108500c4041902000d4080121031500d4205480503000300c91055814000000740001c400b48001800c280c20320000000d4200c580e96965820058600640704a0035482125141041c4003181c200030001055004000070341c4042500c603032602c9910081c20584120b80100003003011980060803810599070441d642124600c1400040e0011300315030781c6101e2650300c0c00140800b06900095454091301c4201c0300001d9002a159403c4004440e00850400040450010035442c3c5100c00c10315400481507540c0901507520340c0007640002f138840c0310a5404210100034030b1f043d0350f0180f0441c50310301400d18040c2c08007810001c41149940080c030004040010440000d2202d0b1020b5064501403401c2400a65a9503074400e00201961004e0095030f0121101001d0b0381c80c1d45d030049040004903a078 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 453578516 1250 453577266 453577283
    0x4140c09330d060801020418020918010f14090c160302151314070b2d1b060a0b0f0d031b030207170c03070306180506010f031707 57
    0x8411040c01107956500d40001000c8110300000e4544a5816290148005601c00c0d1103403100c1c0ca80c0b1400c03003a5009076012070416481000140044401c604042540c4d5000000c00340e55441208003003000c1d40b111383c1c01d01c00440a80e03400070890002c110b15640454800f4000482c0414141003009004881a03c408643c0401004100429452184204851303402401038500d4007001c800380100400049130400c000c8040624120100040110a941c003000168010881030f810045e0885951103460304811080900404c014954480390b042007581c0078008c0c2d101ca450742e140e1840f80e44c145190703481d100158081e150014902d485288540109034100421001e000101c0f00b060090241b070016050702040000c20391400642d00322088051030702d00c65070040601c90f00e0a0556005e000b40705011451a800c13480309807009a074001014010340e0b81203080040c0300c941d80380d600e02020680000050140c0900000001c000d42e4103000e5a044034041c210404510050b400c40040b2442081030040c02e143c3c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 453579766 1250 453578516 453578527
    0xb19050d02060d0905060402041a181b180f0102060c0315010c020603070207090605120303160c12050406170c1c1d01150b03010f0b0901030615050904140c 68
    0xd0002000440280040c18040c580100507542000382e40681c842512103600c40c8052004604080c482d5481d540f14203c400c203095402d042c00070711510151241a00b0072600034001ca09a00b0340d00741e555580ba00c3d0040d90316a202d00402c1c002d0f02c5002d1000710303d03114100c020418040741d400400c4c9140300d000e115a100f0315660b205184440d84070000b5101d1410080441401e80051f107402d4001d5000c0c2105800402c0a6454040700100380c4189800c460700468800c001d184000d40c0000980e5080380e48400c081178100810b500c1206c81060109002c0e050959055425003484d400c070005005541b600c4c2d480300390540031040502001042a01c0100000b00308104bea8031040664404103c0b80c40e01c005c01084500e40041069661210462540e420780d6641c1040009801c0100c268001805c0d2114014110340c54851020381d503920754441e6860303130580043d004000341c4c072075030020014010705116401ca0a080c100f00030640d4002d442c900780110300d000c0c403c20851451000300347c81060410186858135 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 453581016 1250 453579766 453579769
    0x80a120504050904140705130921021b030c0d0c0e070503010501120e0c040e0d030b030606010206041709061206090901060f06030c05070203030d02030402100306140909100507080105040b1905 84
    0x424000310170040c0e0050480204095440c6001c00c4840a120000404c00032500d040002088000e000c040a4808184c00e40144494021a091a003107188240f04020031024001003403c1091045900381c1c0302804007444c000b000242206039050b00d000c40600502030b580c1d000c05644510003801920701081d210000c2e40e40f04403040e00809070b02c1894005507800130a005000ca4103407a03045502400c10341140300301d4400207501d88030382080c90100310000d022500381f00c00040d403103400c05440601170070301040320362046041c1c000855802030b4001e0000c07581c4044c140e07200d80310403c066401c684110556000310f282c50b907050160302d003680c500c0c00c4c06e940300d1440c0c100d0030340040000d642c06a0602c00c0038481100580c0d0144082c0150083d02c84002d603a034078007403040040807500c030a21401030507d0300c1c0c8207201110110412040c3c0d004d007540c007001c0350b40340c6500040c50040161903485030241400d041040315030707201005178101c5909032803e00c801080c0e4400c102070644183e0046041c2c0d4841242086103 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 453582266 1250 453581016 453581033
    0x1060305010c0f080106140307170a0e0f010501180504051e03070215091e031e01020706050601051206010c0204020c100e0f030a0e0f010302041d100f05030613060b0307080a120504050904 82
    0x101e41030303050041804003c0c900d44000c1060854184140b03e3350342040000804052180015143d1018020401e942c1000e18a2081701300100503140510390350000601080020403010f000303151158030040c24400303002c01c01640ca80c01100124001c181c007065081060000c44151075815400070150b841c1c100d5040343c0c03401c00100d04100d00398076200d142041300d244078000c1d12039400407400c0c00026aa4042c9420301c1000d803100600040d0402004001c042c00000e02c41101a402040900e0584040109400002c020340502e043c0074550b40188001ca44452800c0e910031700c0d144c0c02120954a40c001035a96031a12406580c24040118080d207444040521300028102c1007540141401402e1684582707a40c0600901342c1c1c0c40d000380f030919030288800790711911544401040040125814503080c50042901c2d86006842d20b00c40d410551200c6040250b1500041942040034040b030f10890b0b03440c1d405958850001c2002e4400880340c5503100303902841501200c09803400548020f1880c1ca4650f40c1ea81c6 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 453583516 1250 453582266 453582271
    0x90a06030921090518090c0111100b040b22050106020c03030403171b03040f1e0e0709030b0a1a060403021c0314040e09010f050106080112020a0801060305010c0f0801061403 76
    0x4010f0308a070301069641d075158802950300f0b0300c40c00c1c1000a1404161003441d203d40102071074107000c10195841100040064001c03031022402c100420002c0440011501800703440d24410ba110820141600c19071004a400040001d40018180b000e039030707a602d00b80d0311004200121034254004002c00d1001c50110030a540d0301e4065012014a840f20280412804032022400886a904002810401c02ca1907071080e50180c08034a182240007034007a912200100c205200b4240288044c0d03000801c41030090562100641e001110031a840c070b44026400c00804452034050715100140e0b0761710400c1c0c24408180c406480c2e0181442051500d403001074040c0c284410011010441030507140801000e000002e04010040c0004007034890a250001c0c5017512f002d03012480300e1034584001080540e80c0800010b046503040c060b8200d1b0301e400780c00890000b1100340c200c101250b0800400100f040030550001f0007003041944e0320b03c4000020070084659403030038810351000a41c0e80c603000c00420307208401580c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 453584766 1250 453583516 453583583
    0x5060702030316050114070f020303041101030209031605270103170c0d03060e13050d120b04150302120a051b01050d0504030c0506220807030302040f0b090a060309 72
    0x381012038810408418000d6080c0855890351143c00c3d6241c0b04210505d070641001f0b035400c080c3c0b0900c4944200942c0c0f0b01008001600c800a6402c01e50b0040c0d01a50445400b81c10141c1070f02c0700c1d40000c00c0c0000701080244100c50080062001c0f94000845041400f05001c030400c0406500385d00e1921482c000400941914601240c1080404c00304031040140c02000f60035a10701141c02441c11442c6621400300800c4106030b09808914580000e80100e92003447e0000f030300300f40c0b010079aa0b1503035400801d07007551256000741c64004118808030702202500c0c01c0300c0c0b086039120307004405001c0c0c0944400711080001e100381d01014950409040e0a00341401d000810324006080c01c85801c0c504094aa00740d4066000c91040d8010200303001341404203552003101e02001d4a850700c80b8500406a001038950040c0804070302040b040e0825200e601240d00406000c014505001d40710210950558006c1c40328510540c07000741d000481c2406400b030604940e0300140070782107040b50305584600500d600030000 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 453586016 1250 453584766 453584773
    0x40b190207121b0b03060d0f08041a0904200301090903030902060313120f0c0b060409080309070f0602070f05040f0b04050a021b0109080313050f1911190506070203 72
    0x10408642814100c01428010036440d0b461504001030107612100d260881240444204104030442c7c4400d45640941540031305141c820b0003050a180c42c1c10302841d002107010481005030810100b007404040c06528030100c0c1c0802c44016000b0750407280181d5101440890b500c2480100001d810551009582c1402030502040300e00103a0b0002c0c0056004492000c8019854140e18091114000140b22905524288085080c6048102070321240703107800000c11141d41c2c080003a48507155500441082580421460349a080201680d5200e13000ca0003042501c428001000034542c3c400100c01c0f08880c103540e4103144250a01003848040c050036049a6007464540113010a47e444074440c15200340034101d001a160004002d0504a044450a219205030304181240001c40c00900481e07410000400020005481c0c0b85000303802c0030038240c0300c41802e0082d01040301c0d0040b49050f1500b40d4074402c0254811000c0b4000c10806030b6000d4901e101d01c203501c00d0b4001e00842c14128010a6001d0000b8101c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 453587266 1250 453586016 453586019
    0x30816030609090f031701030803270706080412021209062107090f1202090f130c0e07170f01091806020d06080c100e0603100e0414070803040b190207 66
    0x16090700c103c40d0b000c03203c001d0441000e03024194405010344d141109000740300500d502d1529004024080030313091050a10005d074181d090707280020400f103030031a002d0060b00c040b581c1e1014003078841c1ca001c58084d01d20500100007480c90758404500c60702140d024010b01c50074211800c081c41800c0d0441007006c5220180c0007407510300b51110501441c03040084d940c500d4501403d160301c0b00b400711640c1c0d112800300b4070001041801070382e4030744100d0740c07085107842c51400c117560300e5042c84022940c103e80505180004003002c03401c4400b0305003e621a401e1500e070b805105102c144a4a50711900721128000850401c1c014425241d09821415404800c00f0400046000d070383c0704d04c3d00300d030702100d05c00c40003503519903040107907071418071103800c00360021108020440b88403d13000d402090344000c0c6034030131180080082d800984042c00c00002d040c22400700720b8546414901110004405215030006120f40f03000010703900c00000403141501e030510482c504100c5c071001030718484408040194154040c1c1c500 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 453588516 1250 453587266 453587279
    0x80906030a061502010e0703020603100b0406030f1d1e03040b0a080a060602010c1704080d050a140105030616140d02071b0501020a020a0302060d0905030310080c0d0308160306 77
    0x9107019645092000400600e0300d280c0c120510100c200300e000f0740e4104010004803c8000c980324003140e40549034603584e0366807091500e680e030229411418014001103004184160b00d40d01959201c80c150f0400c0200713004115098503101c80f14181d108007035104544283d6603d00c8800c09203402c0d50301904803414140c4410301c1103da038128400c40d200289291040003081c4d540d0f405170200420107400200034200c8030b0309000740143c0030084a41540041940482c04000e40030301100c18000041b070040101e41030003503444000d8074500f0f41c1c1041782d182c4c2c08000303ea80d20300451054040c40000f603040603040040301c81950148070104420218070401e0090304440350b118001004010b21811214144081c42000d044140c209600158110f5108500035001030700c603103081e5401d417a01110001c4d00e440300c403111a0040c080c0007200611601000c800c0c008207401c03070b90002c41912184000e030740700405401c0500007080301d070a4001c0d00089110b00801c020342201006c0340080c2586181c007050803a112074 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 453589766 1250 453588516 453588529
    0xa05121006140a09050f07050a11030a1709070503060a09021306030b04021908120d0b0a0303080603010606020c13020c0a1b170102030403020a060b041508030c0d1110090809 76
    0x5009440c1c40e191041c1c00c0000d0303d0945500c9000c0c1c00900000c10090500c0402d19441d484010280003d0020005905480310301038401c01c0c414400746000c0700d40d103070414000140380b0b802d8003404d0711103500c901d404204d84c07103c042456015101c01800909140c0e542481d100c0c0a4800b100c07081c1d82140c50004042188407040c080c0038040c0d070042d42d0031112803c041c8184025640e40013802d001d031030110102800b00701c901041044000707100780b184545071300082e1450390007408103542c540d9004501c10000010107400103262481004c04400800115544600513038a41a10050703150b0700c501c421442200c802600c4d4042c2c0b129141da042102e001103d50364544c1600901ea03400801d4964100c0300030807045c071100d07404600100c01d4030029804d40c18030340d9001c0d6403200c9150b4020a92511000711442c1500c0301e03404402d407940110300c5200c17196138400d8007079141c0d4401003100c1c140307006140482c2403060041880a80c18410720004180200b0301c46100320050080b0007044171104020040c2000380d071b6402 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 453591016 1250 453589766 453589769
    0x2c0d020d06060303020c06040e01181d0f0120041a040305070806040506100501080f040510060306140a02040303120b011b0305033103081009020a12050a09020a05121006 74
    0x1c0d00001901400d5040117840d004458054a11070041040f040c40a540300003205411500c900b4001c40800b03100509900c09403003200e40c0019400c072100d00d29446403400046c0889603082c9040200049074558412984161011f025040d051108100400c030518800d4840e14083e90f03e9140070303050035281d95400d0b0501c2299440303001030740d000c0d80a210070300c9014002c5a400582240b044c0f41d01c00d02d40000030380048402421041103a20703400009040c00f50a0006058005446504000054682c075021004000c1d60318164201c440f11000200280098400c50741030341e4141e02c0e030110b00c0500120b9180a040c442e50068104401003000d440c010b0801090201600d11035240c80e5264a01445600445002c2c00e854100300d0000754140183c0030803a011107641c06405203004041965242c26400b11400c1c541c1c0002052840050040c510640c0301c41900c02503042006c0c1032100e511445202e4003600c048c0040a94401c41e9103030100070b945021441d804803a003101d0191400c1000c00048041254000d = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 453592266 1250 453591016 453591023
    0x603010b04051e06031006080f0105090103140705120f070f0e1f1505040510080c16050c0d1b08030a0e1314040b06030f03030c04050909031902010204060f2c0d020d 72
    0x8091b014002603411107a459409441a41e04041d1036141c00002884040e06110141881025640c080ca4520050083d0000f40c40c0103410140901030f0006202d95403400818100c2950054140108500d2071a018100c12600010003680c401d481d00441c00300c01610000654907203031480400050746440c2704203080e0390711031103031922a1502e15103824483d99801108950341000048002c210039100c4202c00e85900788400294080c1da01c0c000d143c101d1030484100c40680d4427010003150442004103e20030a28001c640c070600000c503d41c1c0d894001d03960b004541816012030b40c61000d0f50400e081108841504401940e070114007605166075000800744c040da4246d410320050300c00c026144c00c0410116010b000a10001e500d1f61910644820b424000c0d40682403040164802007141000c0400070340301c4200c0302d078061518030b08009001034002c0d4040d10501c3d020038154071203107202c0c0e4000c4820708100b24041307000c50240c4414036100d02c0d031406840d51003544440182d42c01c0e40581c44075451a402d00d0300c03 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 453593516 1250 453592266 453592291
    0x90109090609020d0c050703140306030c0916021e06010e04030912030c0308070c020f06090109081504120801080d03050a18080702031002030c0a081902070f110603010b04051e0603 79
    0x41c00007079241903038185e540ca1300500008012010000750b2202085000c80c48543e00c194880d16054000790074840c075807140d254410072050501503450940c4807807000c500c60715002c80d04502c20030320705804015208082e2944641020004021740d0a0511102d82e10a1107803074100c6007da150100c1c17502d888491034080d00060052075198081642206045030401214100b16038084100d42c0042d00c00c9481c80c20030350141001260f969a0b5074000e41c21070001c0e004040544010315290a00c100c03000d00104d5040d2901c08041100c0007407240294440740c142d8a8601c058124802c480200707802404001d0045030980e596050300c10300940d00f508544100b503226400e480c0d901c2045004162601500070b4040d014203104005122074182610121440e54405003010303400e50b601c030b03858203001c445c07200000400702d030000402004014841f00300342e069030310070001030045100d0346041c000a80002d0081d881110420032060010345440c600d40302e08550059070040c1868212800726890350010380c4c42249070751 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 453594766 1250 453593516 453593527
    0x40201091502060a0614030705010c08190804050105060f0d06200a03020d0501090c0f18180203190e030301120503040b0409060f08030c03040612020d06030b01140405130809010909060902 82
    0x2070303600605c4001c01101d182c01c8002d45041e0300180c3c0301c01540c8256814002c51041e401c0c200203a1606544501c0c4c11050a14003403910b441c000380150700e003290211001d51901d800180070386800003010580701d10113030041c09864036907603424000300f11400c070182e007000ca20085000c0d11680b200080600c480b0035a40940c8a4a00840c0c50003541c9068000d02d003e1424205c0300b490450707118210340081641843c0c10640624001441c00d8100400e800c0500a03403406c21040703540c0070490b001140240c80f900708000998040c01016000c645031068801c000c3e8004000401080b0500c1d584206c007103003c1c0c03060300e1a04d41e50b11100611079000741d10001405841300390070085000980201c5008001c44009149840d44e00107000ea1680305900850b02030000e80300b03030100c59200d282c1c150f0b54000901081040200d840e8240608a11000d2003041810000520954540e04080c0281d50040c10084100c3d146440d540c2e0300c18105802040f40c6604005100c8800102114103004040003005102001039450 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 453596016 1250 453594766 453594781
    0x327010c110c090c0f0d0f0911010c1a07050d1401050a0506070c03030518130b130b0a0902030406020f0a171305030a140408010204090f1a061204020109150206 70
    0x1012160160781c0c5541002a00ca901a201d1601c0d403680700020301e0b56669550825000c503101d500074001c95410140c9421885900246103910641d21580502c49010f00302c6424401181c40d40005913004107002070180300181c5020810300c03016000003d0782002400c0000030041e403c11207480008845100c00300400410403810914082c50140c80300340c0b09103140ca0a03e032070354041c0d4602d9100040800c50000b410700402c00100501e60f044440c01000201c0d10100d1119038005800c031755001c43d02c2000c0100400034510201d100300421000007a103010f198a103801c040c18000c0d000100300f6504590200680c2c0b415050000043c083c03c0d5141e201c4015480341401d01e100c000d10700402c01c124004100342d0a402240c8008107903a503403c5d071498070b445140c0400d80347c0200382c050360780803000540c0045030100b01d60304941c01007a01c000260f0b1007000b14903030420948041030305400c0342c29008407041200c1c080a800642005078058010706080303400340c0d1348480c51100100c6ca00d00c03c2c0c0040e0440c40500039803 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 453597122 1106 453596016 453596027
    0x19121e0503090a0b0a0e011a0d020108040c0e0c04080d05070305030f100e0106020c010318030519050f0a030501051914120a0b0702033c0327010c 64
    0x80d0402851401c05002c00c1b21100c4c09950801481d55102c2e0080b460820b05400001c0c60111000c00540040d28008005003060704c00e0000d006022604030342c405c0c046802020704004550f03440c1d103001b88842c00c1001000f020004c000d41080741c1004603601c4416280c22200089000c005900e580602000609480c4c0c4100c0024411360000100d00e0b40100d034042c1c075040d00b0703241403041a030454800042c4500342040240420014840c42848059890400d000c5200c6420907501d0004004074031600ba4000240200c0060f03205c00050040e410b005a05141c22010401580fa10a0408104600940a50400601550509805401400007041054103180d04440030807060f05104000a40f0799000c00052583c0c2c020a800780d1440b80200381c04031452941d41807801000e400c800c9015003840e48051303c590b003d80c00765500210311400c045094540810190700004001c492460007412 = true := by decide +kernel

theorem cover : BRFrame.Cov 453417266 453597122 := by
  have h0 := BRFrame.cov_init 453417266
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453417266 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453417266 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453417266 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453417266 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453417266 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453417266 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453417266 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453417266 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453417266 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453417266 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453417266 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453417266 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453417266 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453417266 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453417266 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453417266 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453417266 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453417266 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453417266 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453417266 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453417266 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453417266 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453417266 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453417266 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453417266 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453417266 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453417266 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453417266 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453417266 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453417266 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453417266 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453417266 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453417266 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453417266 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453417266 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453417266 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453417266 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453417266 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453417266 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453417266 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453417266 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453417266 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453417266 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453417266 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453417266 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453417266 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453417266 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453417266 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453417266 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453417266 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453417266 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453417266 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453417266 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453417266 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453417266 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453417266 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453417266 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453417266 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453417266 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453417266 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453417266 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453417266 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453417266 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453417266 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453417266 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453417266 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453417266 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453417266 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453417266 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453417266 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453417266 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453417266 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453417266 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453417266 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453417266 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453417266 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453417266 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453417266 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453417266 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453417266 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453417266 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453417266 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453417266 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453417266 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453417266 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453417266 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453417266 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453417266 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453417266 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453417266 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453417266 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453417266 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453417266 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453417266 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453417266 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453417266 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453417266 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453417266 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453417266 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453417266 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453417266 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453417266 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453417266 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453417266 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453417266 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453417266 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453417266 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453417266 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453417266 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453417266 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453417266 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453417266 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453417266 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453417266 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453417266 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453417266 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453417266 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453417266 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453417266 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453417266 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453417266 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453417266 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453417266 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453417266 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453417266 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453417266 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453417266 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453417266 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453417266 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453417266 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453417266 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453417266 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453417266 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453417266 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453417266 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453417266 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453417266 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453417266 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453417266 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453417266 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453417266 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453417266 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453417266 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453417266 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 453417266 ≤ n) (h2 : n < 453597122) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
