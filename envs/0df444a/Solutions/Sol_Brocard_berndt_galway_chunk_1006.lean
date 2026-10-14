-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1006
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T00:47:39.476737+00:00
-- url     : https://prove2.me/submissions/a74ee8f4-3b41-4654-89d7-3e40701692a0

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 180755395 ≤ n < 180935251 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 180756645 1250 180755395 180755401
    0x403080c0f0d020c0303030417040f060c020f0906100e031212060a05010c03140f0403120806150c0309220c0203030708010905071202070611040b130b07030522030203150a05 76
    0x100c041844030040304c001d0700450543d00d0320b035641404881d00241c1944035400c01e1000141410031080120001c02c1c050301d800480544c18010b20401da0141492580102a650248031407500c46c2100c1048040d034501d00601e200c6a00070020342003c5250428481c6604003042e01e541a20f002074481d40102000c44404a4130b41d5503000645055081840180125203424038819a00c516a0010f000c410024191589040e490340c0d101d0445d0580d400c54040010059001c211301c505100804441201d04c000d0810705003004060f11664034421010000c0c01501201e002650407a50303011540130754404c124090040141640009580b904200c0d003000004110b580000f8144001e40b04260140b030450b65041d500070240301c4c0d9003010b5442194202e40e1075548182820020b04141302400c0a40050300c0c3c004d50304e039400780310030b4006180e58100305a0390004010b84000250070604030380c90044000640744806040c00e1a50181e1486540041c0d01070040100f000c240425040e03000b4460f9585083c1005151 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 180757895 1250 180756645 180756647
    0xf080f06070207060815060304060209011805101404080a060b09150d020904080c060109020a030608070f0e040c030c080105040b18060c22030f020325090906020403080c0f0d 76
    0x40360a640520150700550310a0001078400c140031a8000d008601040745502d1400100704140c1c1f00f102c09036004d5a01260110b019a40102c045211502040f42500900e00304400552740b1180d80310301c2c40c248401c03aa03440c52900744500c00e5030018584c0700b0540c0c0e1001c0050030244040d005c902d15291042a10361f0000d2041d809100d058902150040c22021402d51a642806000c01c1c2c0644140d849010501812520840800955010784260400540c6801a00b42c3c09001d480051700004480e400041092104001c0a1600812180c140c0c0314064180c4035070614400441064001821607940c0f000c0120783c0314415003000740540d10460600310113030756207002490300e4127288900710702580000000c1440414540c02801c2140d0703000c5c021442d0080194038200c040102c40e401190181c4075580d0b44415483d0a201c05c8100801c001d25543c80201090842e1301c18408a019030080e0954511a060510009506a034007a55000040b10b03078030350030301e4000b565401880106100d0f6220701c2c1d501c40815 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 180759145 1250 180757895 180757903
    0x102010c090b0a0c030c060c0f09050307030312020a09050d0f151404060b01030608010e2109030a0611070f1a070318020603041e080d060e060109030b0402190f080f 72
    0x2e42420020a05195803560225502600340e642a820040105180004201c180c4200f01e00003116032101c0105400c1c030207000d090141305600003446030700080c0080000ca600100c41c141c1c203440c003003c010390369560300e8800d480c01c00003a00915040a03000b00782400b001030042178407040d5806034442c12003440440760640d0944180f00070784070b4440c81d13400c003050001d031044c0c200101c00c1d01c0505001c00e03030549501e00e55007103440d02d00c1d80c10400c0c0e00019145c00c1c6500317061012903541c20058a05c0740b51002031b0340400da5903440b440c0b004101c185d8402c05100050400b10594102c0caa024007102d40504503400d18190029040c89805840766081010412490282c86500e0103400000a0600074600f503408011140d0401407040d1400d4110313010a4201403042c807054050648500c040715110b0500c100d00804035002a040001c0484416061121580c2c11951440c00c40c1d5100280210b140d82d188042080c40c0600c1c41e5035528403500100210f54404400c0e003a40681d03c400003141c100b160401141c0f60b813 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 180760395 1250 180759145 180759149
    0x90608090c0a06030b040902090a090b090c03071701060b0406030603120c1509140304090203040b1311060315100e0102151e040302070305030708071127060f03070e060102010c09 78
    0x40310b910400304200d83c0b03000350031040c11284020000520b003030094001c101c0b8407a007100d100140d29995061002000200f00c1e4080e00040080b0081509111100109039110710a00642142d01b0f01000c04800800094004c3d2000e8501001400d03111699207802802030300050200f103038495044d1041250703081c0b2694040d002d8035048a000c5185810401d81000281403001055401c200110780440507008100000c00c0200803103200140e8918260230701c0e004462000c0d1145030040d603a56440c0c0080341071149c076017000c44001c880c5540c0e03d4980c1d032241c4061441ca010342c82d40100507821035420300c07a00204a202851000c0c0c0949458001c03031000c4498441c0c00316403810080800308648181c1d4000d00d141298018840e00480d0101f68407038070303900d10716001400121b44000000a900c030421650b8082c1210585058408218580941c81c01c0344040320807901c0d5101080d011710004030b880d620345480d24014500542030b2440d058031030500445e449400c807880c5001d90b003001c0c280ca103c14811011602 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 180761645 1250 180760395 180760399
    0x3220f0c0f092d020f04030b010e09060403080604020d0905011404211b0302010e0304030c0801060609030201021f0b15030406050114060a0f020c06160201021005090703020f0a09050106090608090c 86
    0x21098000c0d0f444002110340c1c0d440ca1000070750070301c050058640700e800208043c6009204034243c1c1c1d07141109003440303031200400c2c07043c181d0854024031001907009000150001c804581c050b0300c880341442118010600100003400f40c0d820210014071044102901d28001d42c0a903200070305240c0105101d944d00d0780d0002000c4001641004481d410324150680242c0070f038800c0c40041401e4050284251441d04103800a81d80c0b0b03034941c0341c08c001aa900f40b103040000e18040c140300b400c1c0340c9183c001039118a501020320404045a030003402c0d103480c40c0e50140062504c000c10350840945006858a85900100c4003100c40340c0c5081c0000c06d5406002c41c0314104072400401c864508251140119164220030001c00207500c200781d04200155100800f1b0203020107100c40e81d541509260000a01d40382c0202e00c1510814540000d018014102003100d80580340c064403100c80c00c941402c0031807410715681d440303015524940703000445e440e54000c03104006c40c4c07941da592040075210307120303450340f102d80f9204215 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 180762895 1250 180761645 180761681
    0x5030403110d090b1e0f0309010e011b031a09151c05030901120f02040b180405060f0d02060702060d141609181b030b03100209030303220f0c0f09 64
    0x102000040c010900e4880d0441d14141701000b25a00c001d258002d081101804c000120400407085000d01c110130b072241001e03000307010092000c03a42e03035018030400c1c807410201a19000059421002c1c2484042c441c4006400d0503a42d02e445a040034410041c6038500d446182502c00c03000e1800b0130301c00000c94094211003c1c0d03182c1000d150064404055614555500700e0b2524a0503403400d0151010700002d000e00a840f50742d840c1e903078050b81c2c0880703008000603208034030300f07000e10046807168680c0c0980b220301030b42d0071654214140000368840c050741c034009502010000da01c1c200d040b5150001607052500020604c81501c0d6081740c40c54001e114160b103000105403c40400c8142c030612140707600390f00f46000009030705000844020003800c0417a402d0000c03c0d10307802d00102a041c00c10040c81ca4480b44002181001407102c000303034482c030020380216071000014090f88440104034102c0b0698035440807084403004506e14209002c1000c0b807107034085640411500107859190786c00f0b22980c00e0b100d40401 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 180764145 1250 180762895 180762899
    0x9111201060f2a03081e041104020904061202040e0f33040b090601050a0819030201060f090515010c05030901230703020c1516081e030705030403110d09 67
    0xc803801c1240400e09402c01c01981c2c0b022a281d06145102c15001c103c0f034aa0500d450b02d5801c014100510280c2200c03514a1038202051034600d50f100d00c2a003083c0d0200310301c40e2404202000801038010180f419078400d00e001000601d407da1071728055003039071094030140411a44042020340305d140c0425100c3c02504a03107481880c0e01110000d00741d0101c1c09500703501d900369140c41061000001200d08071138212514007400708903981000000d0050a08552600b503150804103030030380342c0050b4000700d460403c55842120405000703400032006000d580c14007000d0702d56901c404101600b401e503202c69580c41c5071101c411055200d0440010119000001076290110700d03401154404080075400d1aa0010f024000a801d559900200754a90007540240481c01a0004110220b600400d040040710010004c1c030141c0c040e00500d50b40f83c9604410026250b080010340580c1074505c44202000300c48002080014040d0000090b40c080c0d400b954601712001700400940795210540c00c0100d000c180d6004003 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 180765395 1250 180764145 180764147
    0x220f03080606040e0c07020102010e0105060a0e0c0c0303100f05010e0f1003060e0c07200a15120c03020307021b1e060f0c010e060c04030309140102010e0f01060911120106 75
    0x509a0000d0700904a02c2c41c00c0d81c1c0c0c101090740070310180c9250b4084480001c48606541c3c2c24014580d41303000120081005050103400a26410301e2803103103c0e2610034040000e4105190501a02d015440741c8068076664030b04510040316080c43c5024183d030050311500c02140070b502c10809204011400f03460000050f0200b000c20268007a00b604031020142c940f4004600a05104d46640c0605000e0f031090380c9480061400c06101550711610460783c541c003020300034440d9a106400e00c1160040400303018686d501700000c841901000c4282a81d042c14141c4d0003c0c40d03941a8000c41c8249401d0b8203803184c0390203404d204100c4d00007007214960702004114011690043d002d1040401c14030080140e8540b11251204503410303085450001e003165914038205038002002d110031a84028201401340c40e280c01c66501414024030340c01203040e00e6800d08454110b59000b54030550200000d44120b4500c1603110502e94003030080ca0003000c44160801c0c0703000240101142c00e940e6841c2c00650352440e60b84c24404 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 180766645 1250 180765395 180765407
    0x406090611100908032a03060d020a030c030813060c02031f0f1a03060708040f0f020a091b090605040b0301120c030210020321060d110301060801020a020105220f03 72
    0x150824550044450b842c038450300910445030110300c20340c0015242c1c0f81191004400b5920b00b00700980c4402c2d10000d854888201c0011643d1110b02103c080103807015070b0012030540e038042e400041000c2200c0c01d000c0144401c8101908994174a90650800c840d00c485080358000314001c0020340580c084c00c0300300c1741104e200d0341c80054000300620015a2000310350004083c1d41201d0300070b40a201d1510482a40b074141070001c1b6911150343d04024006040580d11500546c000007406072180d80c010310170710119513600302500700516000c603090141d15845401280851484603160002c13944084001500314000c000f95000c807041003440318210303807920811b06440c80c03100000b00c40340d041e40200407006a0b9049464540803c0341d034019038545903035480e080081096441130103135441c415002c00c5983d584017240b200c1c01a80c040d00ca1380d61440300c0804640504000e4010480d50750000c16200b100c982e05610552050003d0144c2c20052031000d00040c00040030103001070125018441c0110101340110 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 180767895 1250 180766645 180766667
    0x319081c0b04020a110c040c23040302040507050306010f09060c2a080a0501050a0216021201091e030206060a080d050a0909050f2703090d020307080607020f0f010204060906 76
    0xd100410711040354000076003240d012900c134001040380c86440341300e5100c0070428104401c1060ba402c120701300c14260090701100d178280f6607480c510585014082307044691420b42c0c2c01182c3c00340051040b070a02d5203016100f07030005c86480d4000b828070340310003000c1440f455202e812160581c9030f5070322059854894025001d5a6580001d0f5012510014210b2140103a01100100f243c003000d050340000f1490403500351a0042e014100c0c8034010312104c50490a00852592450b40c100c40601c415940d070000c0e18050030043d0700103401d25982c0309a040b2084000700291044074443c2e401d0315260341c0c4400030008051418028910b5a5010400d0843e4450084008098075442c0b0f0030054840c903501d242410a894045950000b0354016009102c40050f1486c1038901d103500c901c8441070301907000c9501c4c650324060b14150038491021180c0190075514103100c8100541202001e0b108607290100c0c01a6980506801034442482144801d441c0404184241c0c1d0a460f004d5440d420642e1404504030303511100301c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 180769145 1250 180767895 180767947
    0x7030506060324210706030b060d0b03011415031018110312030a1b0509030a06020913050a0204081903091503020c030a02061611070b030901020f0d0902031908 70
    0x3d6920045640c130010005000120f0210070000a101145101e05004555101000781810145d031181c003950345906440d4605501d50000902c8000440083d025003882c6188000d441032007824804106400c504600c02080c0c00e4048403040a150080c040031123698521218052003101404d90005d600d4506d644042e0000034100d406034101018040c071030381d100ba103011b40f8880c0d171083d0103000350800038000743c000001814403604101d17040000c20b80714000443d00403c0780e82d0014400105035155824091109000c08081015240c80d00046009610500070400140720f60521801141c00b8054038886443e07140d51000d0300d00f40f6001128a021f2041003c074414541c00744100705d06c543c01000540090740081d030042020b400d00c014200b50b0016000c131440100051800440e289840c0081c21608645280a420ba034903070310385410324024042c1d03030a00d60700d580e000181d40c4803000b051b030008413400340210140d480c44820210014007408148800034015003080c41032084107081c00c20294030b03006003 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 180770395 1250 180769145 180769201
    0xe0129042307080105040612051e0f010903030e1203060d150b09070305070f020f03160812010602030403140d0f0e0103060812070308090d0c020d080708030106090e070305060603 78
    0x41c505450041c040c1141c502e000200c2c41e200400151400340a903500500d032505058241c02c805440f0710f600d5003004036038004203c3c907201c181851a40704000c0756110440c51002040130500915006018161041c0f034003000e440384510380030149a060b4100c034001c41000b04480d41e011000d540741c3c80440e086250b150b40141d954005051242c41e031405c81740c49420f0315a4002841c1ca8000c001402c01001c070600700f070841d40000358903003143c4000000c0b2006060f158400c1001d100182c0b80c0035902e889000d40c0501c84190103000080d045400101803c103580c4104140c3d1070501c411a800c0b0b59840c2c0e0000000000740c4d0440b403921034180641f40c140495032040c500824081e843d10052803629900380703801009000001881c405155216850300d030080124405003600c00c410000007400300c4084103010b8818003107004084208030f42da0781190a02580302084586a682d1031101502a021a00c02c811404054800040180303209203d51480f0b481d0042c00349042d605e45030002e4110350500c40300442d1080ca = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 180771645 1250 180770395 180770441
    0x8090405010b0301090e0114221406010f1512051e040c0602010f0b0d080906120906101e0315090b0a020309070e0c040b0a1b060e012904 60
    0x2140d00585018001d00001c555680d450300303d0030b8044031581c0340803095907454050407030b07038000c01040c40540080c10390202c0e10640300040c8141110402a110040000040d030b0800192344d60042403140c1210140603028038059614107051000031070259407240040c0d0308181440c3d415600b54006c54100c50341c00d0b08000503101c3e5180441030040c0950f029205000642010031003594240603140c1442002d81c402d0040d5a90b56010988080c1a200c0003800b5804c0882e92001603101c03030301554100b4440c480c21580300e041c0071044989520081d40c10f40b088608010300070690841b41c00302101ea54104121080700d6504c0c64580510000000d4581d010480d00d0308224004030f000d003482c40b405440d20031001a584d0031b107040400d1a103070483d8490b10030080c3c00d104010901e4074000c02d8a0488514024040e610780409200700d0f04120a4003154680700501c081d000c2c140041c41c0d10000d40042c145000b00007940070380c000702030078035944104c42d030394034545030981007032404c20303400c4060380040c40300300c4c2c240c2c0f02 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 180772895 1250 180771645 180771649
    0x71e050a0504260606061c0c020109020d0b150d23030913151509060f0513060215070e060f0f07020604060503150103021e09011e0309030806030f0d0c0809 68
    0x40c1d1404060a03811014000e030402443c0500215400500c122442c500c0c0c0100340045180000c0304000c03a140103513407032401e106c0c0c65000707402002169030b00401e414100340503840e141c0c0c8440000e41e0524041051100c940103281485083e1501040d000813140c0c80e0070700c84101200d002c0b94214a03220090105010100907a210b4102031b843d43c0b0f0f0101404910380c10039460044a601460f404201124401001c03030040ca600f2055580903030f00c2d6860f2211189502e501c098546103c0c40c201301c2001c82c4803490000b082503000c22100c503c040062101c18030b60b02c84083c03c07a2840d48411482e548103c04100400d0f4460030540100151001003c51500302402500090269042039105202040c0000100204503240481401f1192002d003400c40c1050062998486040d120380340b0b0b01c602044c0040c1503149170307005140c3c29112300c100c5042c070b0f001043d0001c0000c0c0540401e410842c00704440342e02003141890b01241c1c0e0090041c0b00c10051103c15500b40c402c603129468110103071000f20040050218507 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 180774145 1250 180772895 180772919
    0xc030905240a030b1504060807080c040f0f080d0f021e0a05030a0c0201110303070e06180901140a17061315050907030c1202090c0c070e0a05010e071e050a0504 70
    0x26840d40c3c3c03000911125150103122070400c40b14455001c1d0034041105004494100003442c0d0009001d280c81100340c0d03640e1522040c107100756040300c2c0c030300c0e28126000103004040f6070049043c1c55001050325071018640c003080d00d20a104001c00e8000d600003540b280310045030084400c820400d00404ca8480c460242c50300c40c00c540c0040305020009000d040c400056503000035900010b80c404a00945c03444c50328420040c06c500782e2010b007038840e0354000744900440700e00300455000c1e040b00610aa0302541c0d1a11181e408001c040b0849010b046040000540482d244035020341041c00c010151035280c0d210501d40304603010591007241d0010020340c0c2c0f00c2e00d200703552090620803d60341c0010041c07641582450720005a44c0da20001849030000440401070300e58100c0c15402042480390740f92a407100c07403051130500207580c024840000081c010000c044d03096400003030403512080300d42000390b21905012502d0740701c020640c0c90300c0d100102c0040c01c0749101c2d100a14000507103141c4541003d0321100b03582d481d = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 180775395 1250 180774145 180774157
    0x24003031d0a080a050705010503071202090d05060a09060e010b0105070204020a0309050d080103030201060f0b16031b11040e07120b100302060a0f03050a06080a03082a04030b070c03090524 83
    0x85901c40003420007044400c01681b0050042424014218588410300905188001c030031041d07251b0700811008003d40320001c05070f1507103a200c000d603a054600f400e070000041800c0c110070f6600320b007002ca052000e16010322a0038010401a0744140c070f401c019070240006940000044400c15644d444010040380c0148680300b002005a60384071210751441c20000c0c01d41d100c03a0402e4901150500c0c04011254402044502010100c0b80c942c01d200c51a003030030b98120225105008944003401c900b4030030413400e5040301800c2a01281c04004164580d6812556070b10703d4000d0b00c500150304201c2c4d002085440c408030354040c400001c044c001c952281d002c920603800548560000c540c00d05014100b81c2c6c2c05001f5076601c0300314038904100c0c09150020107580c504031280054180070f105400b01d61904000108030512031b01140300e558001a07651030300b0160398000e01c81910918546808240701c5072040e4000c00354280c05940b405071507400c0c1410803405074071800101c2045044e2150118180c00714a000d489 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 180776645 1250 180775395 180775409
    0xe010312090902041a0f0408030708180405160e040e01020a02011509060501020d0c0f0510090201170f011701110307110708031c0507020109050d030b0301061208030c0306060409024003031d0a 84
    0xb0702e940ce18160740c0400246004060b1099007080100801e0140e04d0039a180701035040d1908031034100d0741401203802441c80c4940c25030b0f0340d400046c501400d9501508032001000b84a00580c82c00e03a0759827000c0c811190240289401a0845002c10b03000030710071100c0d07000460265080701c1c07400c50590344007842e1404040f5040446500e441c0701c0c0e41950380081051810b000e010014040a16010606d8280c4610502a100a504070f004440b40184800d6008080101441c0c42c07041c0c0d217090a44c0c0c094000c280102c1c1c686800e128010000c2000c0b80d003c01a901494031216075841c1c0c00c980316620501801004bc1010115036032000c030305021440c10030000c040318030640ca000424514031018142910390a80142081c4025560884009a160000c50354455010380080341c4903214000094100d105903400419058004690142080c420414403400c07e60000c2090002011001e01c02e140081740005103003d040441c90104003181c01000d81803042800c004410390710b10700303400003e070900240b80c0041c0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 180777895 1250 180776645 180776647
    0x11060c0718060f170d03020307020a0605040506010e0c13050d210e10050703050708030402040b0303040305010222060509040b0a05120703060e2b090e010312090902041a0f0408030708 80
    0x21842d440c50b10141c031400b004101c0304c0c0d480040c02969400141c96204c20540d0010000751414401e1011400d02980000180030509250501075680c00c400c0c01074551580b000b101162480044d0011200030454816138502003d14210400504283c9010242d4030351000440c00340c210a041c0300900b02078034840d10b80842d01c0030380300c0910204142c034a1101d400c0c03080c00c000c0203010a800c07000b035540e000d83c49003103d5038a80d194400300d0054906009095014400411f01004000c8190042d044000b0040d20500c100f03410200440b006400d10b10600000c1001080400f49505181c2c0140311504000b51400404556500118000081001c240c100c80c1d040204240f003000300d04d014004080726220010082c03072480f03420f44040c2c09090b00181c1c09045002c050401000e028400380d40060242e041a13080325a0340307051192962860312f4100c00029851030002c180c0d12803034401c0d1030585101110790200c207200c0b490700b20240da0110300c6103043c0c950309002c0001c00e214200000c080d030522802c1ca403 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 180779145 1250 180777895 180777899
    0x604030c08030a0615120b03060618040611030103080c0c030d120c031103070918020a05040e09071809030318030504061404121a0a11070602070f020d0c06020c06040311060c071806 79
    0x80701240c00030f141f072034441c0c0c004a003402501d980d0000624244102200c1600175a00c5500c0c0900c0205060365000c50886030102c0000140605800944681d00c2d0520a5620b14841070081640b46c41c800c0c48030102180400c2e21030a40800b0a60142c580e041241c140041e91f00e50f03104d65507295810441e4818002002400184903101110308a50002c40031500294180b400190000c6c100d406940202410080c0d6240042d40c00b010410280d00101064291034560005aa8102024001c000310980120b400c0c0300420040445246000301c0c03130340d05982c1e09820305007400000c44d40b085041c1031a0405010030700c000b08020907c0300c0500c41861050601c0c00c000d4416681f60901a1001008000c00c00e19080441d40d402804400310f941040d8010401a0b60315024039113a400c5068408001e5000810b00d494907003040110512403081c0c41458084800441c52030081007420702c40c0d400018500d010000040460b41807000c09014000401021b8941641c2c03910317407174034040c03580600c4d80c8900c42e107820302 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 180780395 1250 180779145 180779177
    0xf0304090608030c030304060b0d08031e070c110103180203030c100c140405010f030906020309073204090507051203130b1207081b0703080a0b030604030c08030a0615 73
    0x2030301d0002c0c5001409076040c49841c88540341c981c000100f0180259890f030203008900d541d4180c018140d164015812922818403a100e4864412402c800c01e04001d40035001c9891513004103c01c40016500c603000040e4940404c0046024004e90307500301d0304607a86e614010300183d50910103400c0c1d480c0406e0003020f840301008218000c0e500004200018070040784000c420600c102c004440c04d882c070a0070040c410a001341401c034000d0010010140404d403010060014a190120300d103811600c0d030a00f00ea003901d10000420072412901d520701410b004d0003501180007400e00b5000350601c0c0d4002c41c05d8900455490b00850340140f2100780e5102e40e03030800104010b4402e5030000a00c050080841c01c00c0c20400451400d440f0300c00b02501600a01107260300051690384103031091a544a41c03480a1515041c00d8074015000340c4083d05c0800c0c00c0c50034202120791504001540620030b43d01503540e500301000c0c91311001d4881d0f101400c01c054030342d1070312030100e0180750618101d1002511991510302c14012045 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 180781645 1250 180780395 180780401
    0x6130b07110a050102030a0f0216080d0906030b240c0a081207050301121506030804080f01060b1305120f0d0c051504171c09030306050a0f0506030708040f050f030409 73
    0x98010b00ca01200320301400240d03400029aa100002c6003010000c070070304080e0aa1824150120120001640c018007003030001c400710364084280c000d900c80e41c9480d41c035210140c090b62044905290806d600d2000c00f000e01f284500800107030111044118545140c031500c8070305000200d001629521800140100500c0c250328119501000506c2e0990455040c407c03030035007480d5156006072003c4084010002182d0b09039101200070b5500910031540c89680c0c4801940302e480414406d0280d503e4200e00288480700340085031020178003d517141c80118140000c00c01c1c0b042c44c010782d40b0024820342102200d00e034010002c5040110003030304d0b040800e207060300c1c001c1d1a01c80800030a804401c8480e0501c00060000075402002c0002d007e0402d8a4010308016048826140d80030f02003064207000e0302e9024150903034000c80581d6020750b41c80551585511510002c0383c9180719142e0042010000540d0041c40380801d1a00f05200b07210a820300c03001500e50604e04103c08100f2082038100142c10490000288 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 180782895 1250 180781645 180781673
    0x3090e01080c03030711040b0306160e010806060f0c10050a020d0c1b060c050c071404060f0e01050609010507060e0c03280b07090e010b030403170103050a0f0206130b07 74
    0x2100900c881c40e50b950109440c2d00a41d20010030801901a0010040d581c9420104c0b184001400711a9540340c12002c0004415043d13076024040b500d0300702e0b0595294480d0030b580d88110f0000d0440c61a0086952801916030700c00e0420241502440c034803401c250b4000d005980c064144903001607200c1103541961011204075a07031080911540348041e1000704504048240c20b190007440004458034980b5040c0e869110b82d42000c6214000c41701d011800c14000302003030300604421b82d401c0000588446000300c901d042130195018400c030000c01000342e840d0801c02008030300410701d041c40c10504160b64035001e4a0019140c02101c0d001070801032142d05040220f030301c0222038040b030704404e442a2046190380541040000d050307111410000790000c0d0040c0484402000d5441d0001c4040d070303650820040c181c206840441c00103501c400a044111100c215042c1a070f60880c0103021001000d03a120600c3d0503404104036003042c010301001030706040e099050001060700c0c0710b90580d1070115180102c0c601c4011 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 180784145 1250 180782895 180782909
    0x3150602071e060e040504050c060c06090706020a020607060e011e050f0a05131e1a010e0603060106200c03010e160905010f1a0c010504031101050a0506091308090d03090e01 76
    0x12001c01030303282d018490131050300d016100000e40f034807141090b908000f04016580d40002e00054400354038140050054450010001990407031601c548040b07071075403800080a944000306005a6005c9803140c0c0c8012a0741c0c030640000101c5d014100700c1a1a422034201104000c0e40d510410411000390043d11141d00000107007042050303103031140c500c0c60824210b100160101e40c3c405110515484802607281e0301d2504591200314110710403000916200d002d0282d18000b00c03500f000324009050000d002d5041c0c0741d09480b04003110b0710320b01c0e40c510400c0b1000d400c03a01600c5801c84400b0107032804c1c81040b000c06101c0000c0d000185007400850307500c400036440404810714002c010005500c02201302d4023501c08a0301124040e5440f0759803c840c500a25501d000294030341000d22082503004101d00d1003041108c1c00a100c503641d04a001c0040b40c030219101500700c1084000038450a40103074050401a10610015003062000700109150103c000401c40205003850b07170500a0041d26400c480c010090 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 180785395 1250 180784145 180784199
    0x20318060c0d11040e0a05220201080f060105130b03090f0a0213110706140412030902010806060306010302040b04080f15070c030804020f030a05010902040501080f06160315060207 79
    0x41e01504410344a1201003400c2c980c0d5a03564202200c41d404100c41c0107100b003845840c0b442c00e2038140f080061005484601d42c3e02141c1d160304000d070301304490f4803100c941c05031034800e5a0795a21402440c0c680004000d2030400c030080141c546800c00c1c10801f400a4401c103403109441e4503040c01ea140c80d1101e02c858501c1c95601c007071200f0005a80300020362004000f19400400d100e03480803070740c03240303270007507240050080e428023154411404c41101c1485c1720300c1c0591080201c0801084080d0102d400c810b01c041c3c00100c2110010f00a410400001c2d0340000061400501e0942d40d02072598441d001034100b0500d030b41026031801d41c0c4100030450b04800b0100028444c00e01e0411040c050301050380721400400740702c68400010250365034541019441440075041d18200c000c1d601d407042c02411038040480c0f18610f4080042100403001482d40e55000f580d5004000c03a4403001002d000c098042850701041503190300c040c40c980078050718407000414140c1c006050060400c159800004219144902c900300 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 180786645 1250 180785395 180785401
    0x40e0f060406020a0e1f080a020f0901112a09010503011e090203010b0a030b071106060d0f0510090f05070b030f0c0703020c04060f090b04090803040201110c03070902031806 76
    0x8000c2442508268080340040ea2914843d07002d03182d10011345021a4010f404036400600b030152030081c0f01007200c02d561400b03130540c0c45143d601301700e006400303c20004000500c940c140550080303120307102400c0041d044850390086d042500c0d146002d0782c070703610301d02c40d500c0580c1c40e01d83c1c01d00e455460b0140508800074821540404c510300e2404416400701488640c45803802400e646003036010189442000e00540d000c10b44909007404040f03000c0d11003d0014005001c00c5d00440c801065150241c02c0003410500106600d8071840b040c1401e10f001502e0502401c001441c04580e0b83c45191820385c4500d001d0640d82c0c4890504d00c1c10040b45074400b40008104004124500c40309910455100c0b1040110540720745207810b080b4a0581031190703c503003141c42c11402003104d800304c0030b080c0115200c1040c02d1000c0302c0500207000540c1c4804c813001381201001c1c80030400640c0111507444c4129030f40004c40d15042c80060002e8500380c142c0d4040740c0d4803a400414004212003072400c3d406001c90790001810b40342 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 180787895 1250 180786645 180786673
    0x110a020604080d03051321121103061c11060706020f04030c031a01080a0b040f0516090e0703080403170705061e0a0c0f11120304080d05070206130602030a021c0605040e 74
    0x400202620701c16904410340c070418290040910202400c0451230400080001071700d041c503540d00940d2003a02c1034000d00c1407015603030b00b140c0d901e030107c3ea444640400200400410f004090700454400c070341c455001e000560701c0c070340040040c200542c005da000c1640b141c910704200c80544038003c10052480151401444802c400207018600d05900850440c901d955505198800c00b058460061082c0610408004145130f14001002a100b041d001080307006540705103595111540d11008058003010300040010403c0d0408488101c14081c0d42946081201ea40d0141040304c104c81070741e4100e14811401c20f880e840c03044e0701503100401100030000b00c101010090030108030500c061042021042090740494000d00080c06001c44040c007158030b9041c945000b4400750869124660014904070014882c148001103840c060304818009040b00101521820084d52004115111b42e640070801000c2401030012009000308842d50002041c0b82054104000e907408480c104030150310a4440f04104 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 180789145 1250 180787895 180787913
    0x1c03021c150e0f090c011d030604061d030a081b040e040615050f0603040204050c0c0d0504180506010804060b0432070503010506090f0d02060406020303010906080601030c030201110a020604080d030513 88
    0xc5e9200b4205190a00130103d41d400407100c440781031540500440040c00200412078000000300340b901c08264900700f41031410b02c1e9681c040d0004050000300300e04007050f6092040300400d20304025511485103072030f440340e1100304d0320744c0c095038200c4145607a420104400a40342e19102c001d0441201c1e0358440992910000309280000b91020748501e546c1d40201d505400082c0031100801d2800c400c0d61842c001c1600d015005401c20b11424100c00801c0c2d460158101d16031141070700c123a60507190b00d041521207485000040081c005242d4006554000c81807104000000490703440c0d050b41c5581c01c00a103010300880342500c01410040a0040610041c0081c0e0f0f604400d1311107443c800d0724105051881701c00000c12145040d500a074000500017004180a9030110080d41a80c0c003819052180340d98512031709035203000900c00500058414901840150310800240d10b149a400046421600894002502a6001c3d5004d45959480792120380c0e54160503000d05030703012440500000300402a6207401c018 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 180790395 1250 180789145 180789163
    0x20a0308091f0c05010e060702190c180e1507090b070c09180c06080106020a03080c190e0414010e01050609030f0607051b1c03021c150e0f09 62
    0x4a20104034105940c031007036566014640011080e0000b14102c08000d459009120802e64007942421a2001580350000f586405100a0f60061003800003040580c0d1529400e2501194408915480022201e030b180902441258072580d0000d41d4051007903002d454155500342c1c18280781100700030000940e801c00c5e0518101d070848024255a60381d2032400c00603180c096000245a02e00d40001005d692845001d6458440d01c600392070b42195807034440c280c0b2500002d100d0140181c0c8448100c00010b0311840036140c100181d0380c0b000c1e0030480c1d4410b031180003441241040d0001070705101c40351003a180502900e04000c0032001ca2881c42e50500c00310f0081104140140b40c0124400905191542c404020707110130402d1203420b0303901500303000078018441e6115025807405816102440e9211312004541201d94101e482c4109129454110096001e500219a000c90604504d0081c00c1e800481e80941c0c00d544000803410707190301381461400c1d44070110141105120583c0e160130401007101c00695618 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 180791645 1250 180790395 180790403
    0x150a1d0c03060a0513090b090a0818060903010903020a02130605010e060c0a021e031204060206060909070b040306090c0b030c0412060b04020d091505191e11030114010c020a03 77
    0x195030b0b9a1100440e402c41c01c681d0003a074100346644000c1c10310350802e9019010303031407040c03520381860344945c20420f981c0c00d40703118090440c074000c014110300740103581c0100004070005410103040c4980700c00041e007101c0c0038481c1600560050902d04c411131030b1404420006105118042040c1c41c10100002d2205019440c4039001e00800203050440080400ca1907030a554020300380c4180d9000749540c0090790210300420360092090070408a05905070304150340507650a0760041c8155aa070170b080194040d80500403014a004070b11001c01e04179003d40051000c1c40c01070b41c012031000703810b1070031010703240603a0f1200d010b2440a0051020013040203003120111240c0a02441d002c500700c0c1040402001d0600c1c0080d070103840042c1b080d14112103500860301c480e0162040765440b032000e054203c142c5401310f4241440100002110b81c0c40c4220740e2009184412464240c0c90381f2640803145001c44d001139500c1c04508101000400c801c40103d825201d86003000e00c0c03c04c1d1b589000303074080f41c40b801c011b010044c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 180792895 1250 180791645 180791647
    0x4060806190c0e0906120d020d0306080105070e1e030601090c081b0909040c150314070f0503010918050f0601150e10030e240a0c080921070506150a1d0c 67
    0x15100f0386d6910660241021150140e50a484107004040e40d5401c500d0b135a000440d00b044400034000d80c06102d000d12800581d214866084000e00801051078400c05007440c550614408401094400304a11070180114090000b42c1510508d80981810b0004014030000300011481c85030f0b0603003410503100301c180e007a15010103a8545113050b084a418982000b005c8224142680043e0b55140d000f84d141c00029503c3d5010984800030121001e54901f1703840c10100340d040004010080c02603222032014800d01f6504c00045030560b0f66141440c14188503500703154000310060190b2404990440c0104006050030790b00d02c1c0844020172041648848094103269880545000750070f01030103000c034814007c000c0b00201015042401041c2c66082d191107405618060b20003042c0c6010b41c01e154021401d010041484981d03010320b10500018800410100000c01d010990002d201002100c2c00750060781e8211b006c21500c1c0080c81102441a03110300221040d01440782d090102c20400903410840400c221 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 180794145 1250 180792895 180792901
    0x1a040302100e070f06020f06071103090406030f02031e1002130308030906070e030a020f042711010e010c150b0105131409090f10050402010c0204060806190c0e09 71
    0x40e41440c0000400000040c1071400b9207802c1c5102090782c10a81d801000c90000803910b4a400320fa6442c80d03125100c10982c000b0020440d003d00410180c42154650800c4a03cbc01c60040d0224054810310362040301c45408a841100841c58140048860b00d00b907002194080032000070283d44d64806126140c0c010b0780c0c002506e005c04040d03203031004007441c0c22551040d0b41c1d0a0995000d5a00c00003102c05030005150700544c52010b18021403103041854008040d02d18480a032420030004024200c1740c1000181c40b280780031640c544c0106001201d5004208486401a120002400050301140344504000c0600300d1a0001a00c0541c6c01c8001820500001a211042c40045e1031603c110145114008042d950010702d900c1606502168000140c0e5030100c1a02d40e10001076030b4440c1c0c4029401c40b504029807030261180302d03a020b640d003e401450002d600d821590042404c89005420071542d9070404001c0141541100c1c010000c1d00111542c104896002c0420045c15402620f0a01303110310031032004 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 180795395 1250 180794145 180794147
    0x152910020607080606040e01180507090605040b1b190302010b030703030504031b030b0907080c0306070f0f0c1b03061401180b0112140402100302040b1818011806080a1a0403 76
    0x180c0d000380500c00e0741403607a56100d890702c030510089e11b10070040485c200000140104e102c0ca2020040342c1c0d2070f13164941800c1c10300034490a02c0d040714148a1030b44999407440100a002000003110804610100c1e240442c15070030001e007505c844c041da0900a601000c000c10000e07038004101d4007104d400a40520700641110a0032172031814035030001d82a00b54078002d11041e4580840c607101115101401c072908111030100385a10350000711040f0000c2921900c1c03800119010310102e0a1f003002c54504107801c4d4420b9952044214902c60310b54401c002101014410030156108103400c000001080703406940c90070503110348440001c0e1485900030f441d510b5403011640104010ba0101c55000400c1c041090541c8a29081c008102d400380d1081702c8081184c85242e000380700b1036060703605280043c0d02c0c01031032004100f0030440510401e40c10032443c0080f1800d40c0c0c0b02030940380c040d041d451f00003080000c0c028801000d1350031503046890381d44c00412460300011200e00076a9000c0c1c0350001c003884103075242c0c00c3c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 180796645 1250 180795395 180795397
    0x14121602030c0109081308120a080907080a0602040303030b09100302012105130317090316081c0f060602120913060b0c0d021e06060d152910020607080606 68
    0x81d507070b40d4642c2061501c4c020051490040c2514807000805071400c565510042075450207400c29580e07c4c80d804100750301c02c03203108030310095015886c0c00442d8680d80e619840e040c608107070782c2800c0e22700590100d014003c15900d8042c00c0f80071081160f80815a08050214141c0c002e0305103c000d062014ac03811841c5203c82c5407580c1918040f00000420071482d00203420001e82a900341c00b280003c01d581880740c58a0030541a050060050340000c1d030400040084c90100801082e500340d8210a09002401034041070700405600d02c00740280118500c122020400d050b41d43d140c0002e01950130148a4038036600804003501c20080041301c2c091041c840c03200340b000040519070090b0b4001440099444125440019024a030f41807e030300725803089444000d1001c084104019161540d084100401e241c6d140030802103035124000c1030303020110000081c84c801160102c203143d604480c0d104010390f0265000585000c101c40d0156908600e04280c010300945a6100804000030b01c96810003044541c0c076060 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 180797895 1250 180796645 180796657
    0x61c0302100c09080c0405040c030f020a03120507140c0d06020d020d0c051905030c0f07060b030d0309021f02030a0c0302031e091216050f01030f05040b071412160203 73
    0x6104120004603090b0003080c101e4240284d0050f4800d8200507021411301d0700c249441590070401d02d89a0500755a0b4108503c01214802e07a803041e050003020001c58031000000300503000715200e40d41e17a10302610f08003043c0700b1040c540e807416030003941004c00d4a0304c41000c0600100d501560061b61810101c0700c0c54005e000341c0700c4802c1814a4444c40902c641c0d0070100420f11854120006880c909135005e00f100c4c2d504c0708841429200d20280810921a10408041c0a1581c42400c0204412850b0004a45001100d451820000380c0300d00764441981080e554203c480d4803441d043c1202a880300b00040c0d5070384104402042000316036100300c401c0c58405c1c0156105c0c2c103040301c2881e000036140c4442c101e442d00302201c620310502c150024a002d601c1e00050000f800301e9010f6007041e0f0180b5150411040c1e85100800c181415211031414a001400748541c510452182c26010300504110400500044d00c0b4442c03000c1a480c10000d162840390070a242c03a50108500d520440c0c20001040b040b81903006075 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 180799145 1250 180797895 180797923
    0x1221020c120a0201090b0a0501050307050402030702030d054002090402010c0b041110030209090109180605091014100b0706020c01020c100e0d0c150204170d080708061c0302 76
    0x202d034030ba807182e506411220345580114010003003a103034883c60740205d03602849032540c10307402100c1c1045542050340265034410300030b0060342e00b00380c0303140340c3c401c02d80b407007140e101c1f020000c02c48800003070881e4420070580001e44c071034121292002140d501c659811700048068403500f001d100040c00c682c49001d652a400f90702c140084218201403800003208503140f0811441442030340e80140d0610b10071300c241c0c2c1200c440104000ca0381d03440d140f4080003d1040c0312403030034000d8104903484007250141c012a801190143d000302004000480300d50211240e5440e940b060020305c2c014000c00d442007040305410f42d25503c8440d5540d41d45454504028800d1300500d44040d400031640504056000c03404c41010a0180c070103002c100418040240c81d5141c100e580404a0304442001d0701050034040e02c2d1030560f040e004014a081d499503813450b0800c0b480c42c40c081c4103600500c040d02a1a07407020b1100c0d00007085041a42e1142800c000150b4044690000560a075030611008000d0520801aa504190303034 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 180800395 1250 180799145 180799147
    0x106051011011a0904031103090d0507091112040b0a02070f0605070e0402041a030408090306090304090e07060c02120c0411040821040b0f0708030703091221020c12 72
    0x21005040c101030703602800704551034000b000058900d803000d90003100070014070003656a580e50f80d081c0c076220241d0b034818585206c2800660920b40701d1000007100c00c1c1c00f50000301400c51a0101c48015640f07041c40402000b0824130085115409010764990051b91040b024509907440240d06d04c002e00881801500c41c0030a603054006200031a4040c03070056a00b9683e24803455002800d20040e44a10722070034100402c0b41c101503090003070000141d41c00a11810f40c4501c4c14014200281c6000420341754441582c00001e0104480282485110064a44440074100c2280350502c0030748200d8100c1300280c014617401d8070082e681c6c02c0900011054030b40040041048807441e0b0400300c219007184c001c0f02e1407449803001c81940c1542007004005502d0603295400d24003403c02030703100410382200c1c42c1901c0d120030074420701c1d001601440c0a14456451a84d000501d84681d041c088000e046c2c101006003800304000c184140700d4200400c5441c6008510001f41c2e541d40200d2489161030034242c010200284 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 180801645 1250 180800395 180800419
    0xc070210230708040e0a0c020c190e070504060908011503030c1109090c2814011701140109090b010801090510030b09010f0b01080705030106120219090302090c04030309030206030405010605 83
    0x10303c540a842660440352508002d03a440040c80b1045032181c54080380940d0001510311140d240c0350104501240c00036a81140c820395170b004401c03440b00d00340c8040c404150040b8050210640c001e800710300500341c15000740b006011519500d103040c40903010141c208250310151805106903440c43c0e1045101c080c00c40d264515042c90215154070305030840030302c140014400034140c90140d003441d0303941514900c004c9400a02d071070b19961703140b1800c401d16414001c803094807802e0003040900d120700804401c409840d0052200000420382c0040350040001b16252940031066a64072150080c15a40e40f40c0000600d81c68064051504454036880203100140c81c6007040031640c81900940080001208107000c141c10410041d51003010456408001800510040204e6403048142c035030485002c1200524003020000d0341101c24200c01510001700d140c1c2d800400460810100082e48580000c00c890304150443d40c0040c02d00c040e40c40701a1041d000031021400703110b004e50001c002000014444102c003a = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 180802895 1250 180801645 180801653
    0x612020c0f01240b090402030a0e060901050103150204080d0f02010b060f12010f150509010314010305030702100206190b06090a06120e01050114040507020120040305060c0702102307 80
    0x3030300c1020001003030481c0c074100b042c0e424540000c0a440005130200e0030b041310303042170000035040105400a450707200d55031f00c0242041841070501660b200c1c000810750f58118280018071000e4500380140085c13040100f0044803a0100324849081e0b1280b41c0601e0141600e84102c0c007404080020940c00040051041c1c2202d98650040500551848054407541c1c3d0350309580c80c1044071446500d030f549135946045030586d0f2060300240f42c0000c050500050892900b038510200c2003003608201c49541c03001a00c1c80c10340c5002075480e58900d1745440103003058a041c40048610110308101c003590390351940e0011402f6071351034090355140d0700d026185406e5141d491900410181504142c5002c003864000404403551040c043c030ba0685885203140041c1000000070300c001000024868011556212402d0603101c0c4800c00c002c2d0709402d6601c150303071102c1c154180b072030405070040c1545001c1c6030100310f0600180c8074901c0f1611317903484905003040a54004019a03140306d030380f60b07402c0b03d09050000d00c0a0800c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 180804145 1250 180802895 180802901
    0x50706091b090209040605031b09070302271924030e101d070b070311190303150602060108060f0403120c0c060c0c2303040506030a0501031b030308010612020c0f01 72
    0x368134125001d1002d00e03030f240300f0b064a944c051952030307800000ca0800600f0300d040400085401840d1803a00501d031041020222001c810703402d180d0605080d100e40240d04030305d0080319440188030b12000740b0070b07410301d400001403510391900845000c1c400380040c0f042800b800b0798024611941ea07801654180c0400c01ca00c10001d04078600103590742840c00400d108030000004e0440183d03071884410629007030380c0b034405480710308901d10701c14001e1254400445c10542460812209540300c2e403404245040920280c810440540d0005030440d0320000040250400001d091600040e14050300a400e0b110f0382001c40e801c4485012a580d214206410062016404011566414020041000400342d0111b0460310842c14800250618021443e81c0890419602c904400d1540c03100450386000d9866020450680003104d0032488250780e00700400c1445011401d0b82c16803c00300c0103042e281419554003910401043c01401c081100840340c0e0101415585c0c12503411a00402c11141c1d1210030015149c06 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 180805395 1250 180804145 180804157
    0x510032a1103030708070302090d020310140c0702060706090807050708031c060608271b100507020d11030a023105011d1302060c0a0506070f050706091b0902 69
    0x1050310756080c00c1e4040101c166030013420b41ea961100680c0350080120042d42108924a40c007642444032032005031f404000703080d840840e0080c00715448140e8032040c07554440061103480280d07000c20180005a803608110b401c1f15902090000d124038080c01c05503924040e80301c00a16500c100c400c046500308000018007014a03043c4403d00c00382405013858020369030907110b40c801091128012038804c141ca0540b00520505001407803103154605182585441500d0000c90311240003c0420003003800c000302034280011503414107078031380445e40d40815103000314204040c25003101e030742d40c14610741e40500100040d150020103600d100222880660550700e01e4a8582c86896065414078400143c1402850304036040b55003000c680000a2800c1082c112000300301c880030190100c0c46800603520304001c3c2148042c1c080c02442d0719040c91a0441c5030401c050185028003130400c40c08a801c0b81c2c040101e40c1180d038460b0f0701264044191920521900045d0f0b416032075a0307210344000c2064030032039001e040 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 180806645 1250 180805395 180805397
    0xe09010b011704081608190e040b06070807050312150f010305060a0b0703020c060705031b0c090412030b030105070e240d0b010909060e0a0605040b0a0510032a 70
    0x48035030003039801980c9550780e6a000d2aa20240390001401041641000e4011a002c41c1d02c01c6001040d00d81c2c40c0352080d48212001d21000098148865000da441076101c0903084045d1000c0080c9809100003c1060041f014010100000001d81b0400c014003841640d80000505950300396900b40b039010390b1032250044115500500c1c51402c400011740c400e00420740071b032034054a03000c40c03541800c58200e16540701384020781c1944a1030050b001c650700c60358000c100450040c0003441d25009e40b9100e102c814060511040690303804181c8160f03590b500d04011a400c903910441d50201020003a40c1603001d05460381180e9450352800c010000c1154000350280e080890481e00c0e4041c0c400e01125406510309280000c2c44c6564080c0481c0070000b920380c0c00424a9441418403e40380341d42c88018000790784040d000b1103090454803050100001060042801810040b10300b40700010440010400380070092142a01c201e10074003071004140c1c020b503c4546282245c81e0341d4181c0761030285542e102c2002a0610340 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 180807895 1250 180806645 180806651
    0xc0106090b0306060a0513092301060e090d1d0907031409030703080f04170f07060b0604320d0501050609090303130318051011010c020d09030303021608040e0901 71
    0x10310540b50210307600d0b1040c0001041032041d00d080c60207202c3c01d64600000c00000c0d555030a420f0000c200c0d904e40003c0820760701d40080c40c58020312040f842c20741d0665032000d400041010148a0100c4001c00d6072980f0101c10720b8480d220f1043c0450802c141e41d40200301e1604442c5510074008450b40c10f401400801c03010106100c52a05c81003032082d0741348076500002d0001004030021829000080c01c1898001e4055084601e02c1103003003041144582c0700c000b421041c1d42c0c0c0050507101b0001d031070241d980343c8442190078901f41450407204031004d0144050024640d450fa440035042c24640401003000584041c1050340c10328210b203005c3c0d008000540e01d20303106038030130400249001c400100322480fa4010140c944c24008260360140c8421030344200800940c0b46401c80400c60b511414008030f48a00c2a6890040c070800e402981802c50300b00c91103860441d001035001035603080c0c1250482c1e04503503040c0340051751021100d12504510f00c0c90000185078190004d0001450420300c92140d0190003100020 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 180809145 1250 180807895 180807911
    0x1020c0706052a01060504020c100608010605010e0103020a03060f080a15020313080d0f14070809060705041e03202713060e0105090714040e060a05070903080c010609 73
    0xa41e20360050342c102004403402c000c5145030f104100300b006000140c0302c0e400403481e15140c3c00028281e0f04029206003a40d4062101c400c2070300864000c9c5002481200c008101c0d003400c0c040003c29215003420018180b6400148410f410382c801d0344060001d0808640200308030362039078100358984440160648200810b13001902601d1007620844e4002e0158500c445a40b802a6440001d281c0003100300c2080b65540304102c203180d20540c010b030031070361031410107207170603483c0190707000c1c10521014003d9800340e40128200285560044215002d0b2580d404222030901c44d150604224a03400303400082c420b0142c0c041e0655811111514032449282c11540c0c50b00113a2140101000030780c0d01034400e100100410301007130405e42d00100c2da01c80c0c580100c202040000e40c0054260945405403034094031540910000c000d2001124407494001c0c07011203092107200710741c20481d96100c001a040a5a0765900c4c404a0091401207004100461744110401d07202d90300d000899000f01b100c0c2c481c4420b0607044c1012 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 180810395 1250 180809145 180809147
    0x9180711210306010c020a1208030105040f09020102060606030a11040e091c120b04230a06050607030915020304030f0302010c02060a0c0c030e040608030d0e100c02280602040801020c0706 82
    0x714580803186500c060b815a961071004680d182c039175200583e04640d5009012512403052a1581442406090225036952400050000b152240c007040c03031000b403a041c02000141ea0100700b0f00e408c402d040f188543c5075140d87c0c58000c02402c00c1819103c44110010300010320031200c01540c0e00c11240981550000b8070744024100001d60301d4130072207000404941081a03601c596901900c00c0d203c3c09000023840100314180010800d120089400910380840c04200c081c800038000d800183c0026901c0e14201a030310381d00600071810074003130f000c0405a41c1c01c464051608c01c201b914000c40d088820f001c80715505003006802004840c1501d40103000764000109040c0d0036008408040d003607a9100302101c01503441c205d5407100344104596004d621840700050048080010b01500c00312460700080c40c0c025500f100b803500007900c03681c851446c240381c03110000c2500860f1501500700c202460380030381041080300c107220305804000146914800305c8c2c040343c00041517025207010603281d81198026911000 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 180811645 1250 180810395 180810433
    0xc020105130605091203251803021201090503031003170405060409020913020a0e0306150d0201140c061617010b0a03020f160302010504170a02030f09180711 69
    0x2601a81c141824100000081c440d40c0c04664450400400d940c0c02d08400f45500b0415030050f42c0001100c0e040100c04c00803030302842c0c6800200521402e040c5103211030066403521b148a6480003910031680c050b0380d00c1c0e180d8401e41015071441d50101c03c0d40c1d940d20304402810803114050209651803015600c50029503210001140c054900081c0490b04061a191500001e54054a407040d0002c090754000f0104859138005002000f14039190701c4400400303442030524195004103c0d0440c03583c441c1481c070090303d4510304110070351f80a1801400012041601e49164804c6804050071403103031900f000400d858807010004101020398554102080c60442e100001c8400c3c002d80d600c560003001184001030196004118800300f002c10035081900300c0c40c08280c0060038690940141c0d455100b00801c0044424a030b12400350190426800c04034100320080d5a8000c0d80c0301c6100044000528100039079940010030f131014040302c0a40264a40005d0003021103517081198881841000c0c5d44500180b100c01c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 180812895 1250 180811645 180811651
    0x30415020715020711090a0f0b010305040c0e0903040b0c030306120f0c01210e1e030a090504090305091012050705070b0f040f0b0f090705010c080304020904140717010c020105 77
    0x3061103941c00c4030100c82c64009500140c0201c44803010f200905200f51101ea12442c0320303584410001502e00224000350059a5401824504040c5084100400644e07100e40b21416240510f801c542950f540d200c1c201e145205da900b002c60310392800314008012260020003540b00b082c0680b0014164001e1904050fa0341d5110f90744c002d0f16401c100ca201d0322652103408042d0020031405514440f008000b0181c0f400c5440303014061403141c000703000d42c15000445910b61070725070f250840254a4100c80050081801c101801103c1c880e0383c9442803038060601c52400e44001c200020086007909449000c06004056445d816000072406c1000051400d80500c040e42da10366007107420441c440e03586000b80107281d00d0040080b503102c8151064000411800c890b81d500c0307103085440030151410000c4409180505960203c0d040010b0b0340542070002300650705503500a44d0665241e0416211482c111801d80a0781074a07030224440e00320000b41e00903144100303a41c07120000c0c008011308550024124240c6501b1 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 180814145 1250 180812895 180812903
    0x3070b0313110609131409030301030213020c0a0611091306080307080918090a14070b0d0b0111030a170c12162303010501030c030b0f01320304150207 66
    0x5610aa808207120000c441001080180484d140c550305000103a560742c104600c1850241c0e40f4040c0240f54075800e0445500082210020f50940d0700d10303400501b15401c00b030b03000070945401217000021503600b003148200c441d501400901000c451a01c01d0740068000809144c441e4030001e4620680c1d490a218801c195007090014500c2e0040c1c540f20f0510f15400880c0c01d5401c50324980d00c540c84d40740341040aa0117005148064040100c10341000800c0d0201d034544020743e82c00c1071004200300140e4101322021440381c2c4001050451114005071500b480c0207022090301e00001900744982030303211314050304a8680340785606c007540f01c05000346c83d0f0b406000c41c0042613100c0b1902045c888200c0311a0080001803615260818001c940c4081c0400740314030103030300c2910801000610817580c042c01400041c0003540340400ca903940c1c5000181007204004101e0341484000e400a880d560b8014030003ca50903d040d2403038403110060080940c0300d5008482c02e40d0000050380e404d16204440d4001c5600036900 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 180815395 1250 180814145 180814171
    0x40b070801140d0201050f0d090224071707020d050c03010e010908042601060e180d1d0103021e0306010306081506010806040e0a1406130c0b030c0c03070c0503070b03 73
    0x104040c002c3c02c0403800c41c1a41400400e002000f14804444018207405215101c0411400510300c1030102c10142c101014200010004404043c443c400d42603901e07c64000045ca5000e1002100c0300d0003502c14204082d4000c585803104a05110001401c56410501503008108034046100001d003260380300c0000800c131580c00c20040245c030304034202007000c0344c0b5504110040084220707109400c41c0c62a61142540d02c04a038100145000744230703042c01c24459000e0291070400403003e40202040f000b0404130900e89038403200995507901c20b40c1a510b5003002a03542404400c035603040b0b1202a0400c8451a000078141900428013400100314004043c141d40c4107850390351a803000558004400402d0035400c80c0e40c4040c1108403003010440d41c004603000c0c0041b0708171100800d4400741041c4005215290103a00f10480744001424000c1080403104604079007522500c0300140452948200340c03000e1002c4c4400714104040c03000f100042000c844e41207044407205646c3c4c0c04480c0396804101d68948035200 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 180816645 1250 180815395 180815429
    0x40212060f06030f0c061801020c0604140102060703020c032b0204061d03280f080f030f01150c0f060b03060c0a090905100b1c1e0605120a140a02060a0503040b070801 73
    0x41c60155045c07c0e000c0c14010f481508131014085819074000d0b90101202c0d02d00204c1e07042c0c00e960180101c640107009403034154644076401111980e40d2040300d04000408480300c06908581800c0680c42410744a107a80640d0b685a55071030050401c00081c00c21031186680b02502c1442d4580080e0301c0c0007a014000e080b1180b400401d0242d030306d1184a0b4420f071332861848001c0c42c00980c0c00802030015203011300d09103440781000200448c460005810035040c5c071615500d450449508072010000d69a485010841032100501d02074011300141684107070144961781c1405280002c80c00544254807055807403103020703584c8010384016244140c170840c2600c0c072060010b00200942c94020307e00c0120211401000c060120040400c540e083c001d5210400708018003c406485d0714010034006200c11908842403c0d024407800d80c9804095400034981803c0304240c07010301c2c805202c000481600101503e484500d29040940f640e40304860440785821004000381c141c0340244101c41c141e440389401444003030 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 180817895 1250 180816645 180816667
    0x207080309090f09030903030a08010806070f12230103030905090a1404030c1a10090c030b1320030108011b0804120809010e0303040c0302240d05040212060f06030f0c06 74
    0x52005444d5081e113001c200022a41c03500c081000300b40f402e2a5541d00c1d0b1981d1714000d0001e04010dc0030b00424100035000740000d1200364824881860304102c000300184d801543e065082d01051801c0d4810403102d1040c00000c1419001070750030007100c00945404d1441e5942190200445220310b40303001035104840b0200300480d00c0b0341c580407806807040d036010f030854500140201c0300c030500311003080b01d4400c140e106210358441401a10145030060506112a0500c4000104041a00010024a540c0c1c0c1c460300c90364200660419200710b030a1030451580c0e9611902281c0c0a030104031030030b40e40c0c3e10001004041c02441405110311403608804094019800d001084800a602604010140d0348500c985040743c0410310046019502c2074548440551643c4144030341d19600e900c000c1c142c10b02100104000090803401c444c1000c0e003011001641c1e540741d00c0016402503030303031401071410300c680d01c10030181c0c2d01070103400f03405040304608a60441e180e0203c0c49540300c01240c1165003000003848511514 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 180819145 1250 180817895 180817921
    0x801030f110d020306160f02031312020301060506070c140901050102060f0a0605120a06060b031312030609020706050a05100612020d0e0a05030a080702031305060304050a060219020708030909 84
    0x410310007800089803000c650006450060700381c0e280880c6da80000e000b25001e0703400c040c4401102200303001a42c24100c005007542c20940c61486824024040171250390115074080d03002d0009003000030401d40d283e10150a221b54030780b0040c083c6480341044200310700c6c0d032442d103126424100c40c41607004007100d03a240c0850581030701000e4040345007140c4074480883c2550311030f204400040d003404020710140d969403d1050595505610a44c50000100144150384496000c0741284a4020159903142101d0f0071080f002000141d00406a43e880424441c041003003d070406800340906020500958503511a060f4401d40c031441040b0200715a4490343d0259407140d006071170710319080103000480b085840c40c00e50038a00d0400c0b00311843c1c0c00019078040110b0700040455080351482c4010750030302100350003e03443c4c0e00d40d44c010755100d98008400181009810000e019003d5840300307095403a18170100308104203100c000e0f003400140c00f41020129144000106440c014840105412465242d0740600080 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 180820395 1250 180819145 180819173
    0x180506130902032d04050a0b090a06050f0403030f0b0306060d0807080c031b0601050a090f0b040c090f090b0f0405040804171b0916120b0a08070e070801030f 69
    0x403980c0340d580001ca5584900c05588907000e40031180c1246040100728408600c1d9440902d40c03941c4070841440080340e80003c03242c03e82d661111628034543c4402030303001e16000c404000109003078101001c008109860400c0207020702d10a8806101034001c841012096401003a4126010343c0304400203002031a001d40e11024141c042c00881e8034122551301c0b4158150b00030354940038140e00c0047c9085c2da17251100c1c500785c0207111280141203194104000a640001d40784140c3c08400c1d241d07115100d141c0c2c0c075503002e41c803124001041000100e82c1500060b116906910684c3c003004554040000ea500c4140609207918500604118001002e00d003008010701c4060000d45083c1420300002c92800d0a10403000c04106440c4014902c1044030060320901c2310705011020302844048080c00b405880c20040d42644160300e041003900d003070310102036a000700107a18a19901000e51500003034500030118401d0180c2d040c040340946d20350f881d40401e6a07411800e110060045030803241d110041007280440d140 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 180821645 1250 180820395 180820417
    0xc051f08130b010e04020933010915180b0f0d0c180e090d0c110909121204060c020c01050409111c0c080603060601050406081305010504051c180506 65
    0x115142d2188088803000340c028446824400d001e000551912201c0d19500a101c1015a00c5c10414004c1e541180b8852441404811141c550302d040076078047c0088402400030300d4200c1410000b8000300801d00b15030040c10000744100a100412030404541c1212900701c0c3c0103035010700d40031041605600412040c0740c0d10040000403440c0d00103082a0100c070748020612412004220300b0090740050410340b40c5000e600602412500c0d40d070014203245141074540000b200d0b8084555644002c040c2406075600c800040302000042c1c05042d8589861414000c5004590820101101d0380b010303661b54000300c104601152060104100b030301c989420103407003140c0b00c0040074280300b503422400c58084180141c801c1d40380e4403140031700c50312640540c042c2c0d8080303c110003c1c20141403040004c0c115203d03601030101040300d03d04c0050030007242610b10310385081d4020000c114518003030402c1c54032070390400074807116481512100580680700700c00820442e0f104d00c010030b00781490107003005100e500c41c2c03007a00 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 180822895 1250 180821645 180821671
    0xb0f0123090409080a050a1107060e040e07030503030c130e060a15020c04180303051f140301020c030a080402031509122506020c010f06290f04030f0c051f08 69
    0xfa0004040c0c1016000401240c2c40e856202e02460002800715200f008044415034003044040090036408054001c0c1e1002c00c0d507000854088a80d2001d0800c034490b000500300b4440002804803030b5005c84000e00b001110710020241d0907450745056024044141d07415944020300e100184441440c04040f040d0524280c0100c5450040c45800706095600b040050610700c0048502c143c2419098050b25030f000c00c200d00079208418500e05042d594a00301e01803030311900c401c0c1e0040c04c16500d003541204c03146155141200d88a1000d520001c1a070607003100c2c200c0c0a03001d180300c80442407041e0500346004440140c00340810000404400b003264120402d080040246081e0b01d0680810b07861f1a034002e2130007000c0c0981e40c2c0b285828641d0a440c40120059990743c80e0980812000078001141c4101d010360380120308840440d44501603050080c0040d41340303100ac00283c004108202c6482d0204601e00c80c6100030364a17a55802001a9489185000d4281c45a41d1510300c0c202c0e40700d1204568001074a20b485 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 180824145 1250 180822895 180822911
    0x30109200616030801090f02031314070302030a0b0921070b04061e150501090503030712030617101407020d08181b090a060302010203300405010b0f01230904 69
    0x110788440300390b04054010642010061080240790700800210b004014800e6140d4100701c102072001d02030b040405029031440c110b40c81a050380911040006540040441d2504100c500341010b441c442640c07070706014070130250020701900c402a050201c151008a1060030450701340c840444080000740203d41d103d030342d0702d007a291140c04150005480080c00b00d0008003600104c1d10001440c9403904002e040c440f051104205581e0000101c03020b26511034400700204507428020303809840b40c2e402c0060030340600300c4010104040085c40c1201c009501c00280b1120744201806480b00905a8020006030442c1040b80010307401404003a810440d40a085103c121032096540d05000c004c0782c0b0041d040c0108074402c201484c1c680030a94100c010751100b08500e900d103a0000c5d40d640710700d410340186802c10701a81000b02c014040c40b8290034110014130300c010700c0c2c0380c5059802001c9221001c0d2286a03490700102e01540310b441440c112030300c0d0030416002060000b803106840d4000002c1a603100c0d48070140 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 180825395 1250 180824145 180824167
    0x190606050a1d0105011d0103110f0304080a0212040e130c031b0f05060a0906110a020d210c0c0501030f09120e0a0909080d0203091c050a0e0301092006 66
    0x80d03600107207220340c03800c075880e074110400706400b000681c0018100415150301031b115082c500d080120f08402400d0010b81c40b5480305080c0b40b64000c00c404240031201c00b000300414030140900800c000c800703640c00d90b82c0b08507804641c05400d004500480c0c2c00e0040c0140051910441c0d104055182405890300c43c040e2942da035610b052038040441030305800c01003158104502119841c0c8817002d030801b141d0280c01c20017003050080c018029442180b0401142e411040f54800041c894035138001c1e0041d0511001002a00300f00b000c0841000026155028002061440d42e200e88540c113501c40e03000c5184420705141000440c00f6114000100d00ca1943a114081e00001e19084640c02d828821900c8140840902604201e041030442c1d004580c2d49052040e600c0010b0115000c0344da400e070021a00507129115144032514044050340014000200000e5640d24990000c0c082d1261041a6442907884080d00051609039854000003c0021081c2803102d074820050045450403440c01600690a0541c0c0080f = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 180826645 1250 180825395 180825409
    0x307050f071a1504140114010e01201b0402130611030d050f0f0603030f03010e130503070c0e091504060507030207050601060e01030b04050f0403140409020a0302250519060605 77
    0x3030300070b543c1c030802001c04000b03003040d0060030020f0200c54044010b40d850801820200101200c03128100021280c080b205e5178050881802c0c023500c0d010003005510804130566559811845441075021007044002d1420716050080b20020325040c19a1a8100d150600503151085841c1c0042082e0105202207500100c0303511840340b191241e070304440e4141c140803692803845003014100b103009400801000001d6940942240d04458816494440c2d80c0d540c28048041d42c10001801003007401300140300d03c14046201301410540b079100940850648542050340c0d42c4013502e4145100101c91100090080b80c100d5100e40c0e032041c0342e07081c09480c0104507501d00b03041150907040b90b004642104600710f100c1d41c2c1889801b0400106030340c01c0203141001e1004a00850340248010300708410300b48525001c862040c141c40040c001c0003020764a484010002030069006004060384c0725903540c04113403003030f040b03103803035100442c1c01002030400c000e000000c2c0c0f60800d0384220244c8645440311000141074030703015 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 180827895 1250 180826645 180826651
    0x150412030504170105040209041106190c05010b090106020d03050c0d0c0f090605031b070201020f060114090c1e0f130603050717040203060109020d061a07030f050307050f071a 77
    0x551400d42d2503041140e28602041c000c0c1e00011541e14120030840162504150240c001d50400750b858010118240010314a209160f4031b2004e04800c8082c400f50303107811030500f03040e182c804c034000e120312100340051000441c002d1141301c0050f401180b1b00003049000341d11503a00101004c2915182c40c078132055041c00c0d1068100b4620008604002261401d54041c6183d400380c00d0520b4100d00d10f061002c9140b00714040c10030060015080020000e04680c0208015800102424141d07004c07580d4940310740d034400706201c0e101801101c0c1a000215038000000440b00801c81c01d000c1c04940e4841c0260b12002900522400d41c8205020070444464107180307000744000341510b80d4042054506103000030904140a41d0760350040d5518014000140d4000c030b00103042d2140c440c4016214540105040080d0001d54400e806814480624803201c40045005005003030103610f83c0d0515010070312086410344021141600041c105001800001c00360800030a015406030818030030101300215603410481c015 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 180829145 1250 180827895 180827897
    0xc031b08070f031a090604021b0c1002031c1d0601030510060b090d030f03020f040305010207020f0d0302070303050f1b0708100b130b06160b04060b150915041203 71
    0x5001004080d0b03500c41840e04050000c1e10b41031115480104250b0107108018142e684036128840005c3d1040e1100d80c15075402c4041c07444006d000e420000901d5880e484001d4074035010316600c61000c510140000200c030711108408a000420366611101c2d41d00600403492504586140a810000f0ba51000c00c00d280c080c1d03001d10003a101203c3c00ca01c10708203ca1095200c0929490240f154101c01d60fa003005401000e6014100403c40c0f440000c4218000e01c030741c0c1100c006242001c10f000c018403c0550290100c0b520079500040181e1110f000c007d51000794003002170040c0d00a410501c00030703100f4005414100e00c0f00c0c10321818103082444103658080719200d00b00b030a0707202c103204000b21603007000040c208906d24001040912011400301d01701e9100d508c10600c603541c80d00b030104220740314002103540000034149071052070046841c0040714600141c4041e80c9240c10070703421030800d103000400148138010945242c1d16041d00302044c4055206691140b051000d4103210002d40342240c034000c0410603200e = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 180830395 1250 180829145 180829157
    0x12050c031f1d0303040308060402040902041e0501030603230a060f1401061d040504050325060605030601050d1220030703020616050403032706090312030902030d030c031b 75
    0xc1c2061108540110300400c0801c1d0800c21044114040802200d0300140c06140c8102142c0c3e501002c41c01a114582c0f0035503800e440050300051070360000d40c1134a2004403c40360b00074182c1c0e6480c011401d0f98080e000c05480d0341000c0c144c650f00d80000c040ca0350820740d88171095802103807051301d4007021a140d015070741c0d00c0e06da20b91414608103410703458640e0140160f400c1c5940c3c5600f190588030300f900755811034540981c0e515400b1070240941003054564200c000e0030321042c0095642007203042c405216508031441824014081400d02c1c0110f17030541a0345001d00075008801064481502a21000802100b80850b840f541804001014050842e807943c8000455581d08149002407034103500410810b10440e01c0141e41050b198094201d508507905441e00012541662a001407914824001302286102c0d80500045c4160410000000c0340d0190076210001d100010f002d4050702d20100000b0360640000401c00c0a040c0a07030300200702004a0303d400606c02846c04c9a1240e036980c0d004801022841c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 180831645 1250 180830395 180830443
    0x61318020a11010e100b030a08070305040602061b0a050304020616050105011d06030c090c0c060a0f0c170408130b0c032d03040803070e090a0905010605150412050c03 73
    0x140000b2010000c2075000b000304000c88824203600d8441c907041140c4142d49488410100c0103075010418441c03090b030025255030740c0d12031901e4017600b958040e205031005409050300242d15034991000d59102c00d40048002c0d46001d0010004403a2944003c0c030480e40004107100b01039529074020b949000c0d2500c29000040e04d54140140d107401030400300903200814021600700181900e0110f4007052442e07064031800c05507294151840c4d1607014170700580e1214801d8408018209056401c5003035070144038202001a0018004204c841c0c08213450700307030b0701d010943c0003080016150f080204041e0b1910704c85107582c0c0c1d403202c0780c080443d4001800105240c2c40800d440103464000500400891410301c0d60b07040c00c5e40202c5c0405040e00008002070207485000c80005d001902030b044800000350300030034140c41803400c141410010201c0c881d0548166282820225842c1403610b110040042c0d0000c0329800c0602d0142c000e18000400941101c50740201c440610080d00c040001d04140301a001824607050 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 180832895 1250 180831645 180831647
    0x103060c031811090c280215041b0608271204030606051c0b010306050a0b150c010f0c0c15020c0a08040315110f03090a12031a03010509030405061318020a 68
    0x10094038800c4040002c01100303403580100d01c848a88160f40300c0502084440c0686c0507403c08054036004080303d02042c041200b00305c2d030030385014041070411305030500b92900e80504884051040b0750300702c5030041c3c4880d40805100004c0c5800790300343e51441145c6003140c7c2c64480b0b11700381d0401c2d4070440c0d070540c4624051120340782850780749000280b001d811070510201e1740c4a80049400c18800030300202d54880106410041a400103420680f0180a080300c00b840c503215510745070300c080d0040310294079105040d1000f0240d0300440c100035041c2e0383c81d056143c030a5119045205004a60307542469802c20601c5c001c8181417112150342c03030240c40040c0d11289036080036030328010f484600541247c5807000920040800e28142c4e1100150790b80c0580c0c496030790a902d180f9010080d2006454115015800c04025506030008681485c80d05a07000d40403590000345406e884094414001a810a10040c051800c0110181c405031381c1c4e164107031802c2d940c2c030a4810603000602002100160700022162159 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 180834145 1250 180832895 180832909
    0x401115040807060224160504090212010e07110c0f130f02040323210d0e06100801050f01030f0507120503070b01080604020f040b01111c0212040605030103060c031811 73
    0x400d40b10480f0300510001680e9400f170140e4010220b2515000405071030400d94490b005440152590401c00c43d130300c0840c2c02000410207404d02c20700c0d4444c5440f00001302c80510518128841000b403000030602c07006c0ca441080340302034041e900342c2d070411050303050604100014000d45402c082024401170340d03603085092452440882c99800c0040c29104850490401000038200ca028104100340c043c17401c2c100c11080256100f102c0c0c07690001ea041103960032240343c0c0131600e1070051480c00c241c144640c0e56112440d090325022520440c8260183d401007012404140074000a68460810742d4041c0f512004002100b01007502c06907015071020540340204540744040a003d05000c4005112501d007035800503504d403544848060142d41c1380e03d03091070503074012640003c079450b0340340a540307210b075800301208c6420050080903001849400304580c2019299800c45081d1013440e40c51a24680c03c58580d00043c10402060030101561000203d88690501c1600c09403c1d1080d0382c5104004402c030100448 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 180835395 1250 180834145 180834163
    0x10503061305190204060b1813090201090e09010621051b220b1003020d06061106160c0c0602030d0c050a02070612060e4011150408070602 61
    0x100181002422011440000c3ca81d01030004411001c40c3c105518800f1a018005a070300000c0342c03d030080b54a0300306040b407411009401c030302030b21601142000243c03a20140d500030f40740607001c140703896030500400040e491940e60107007503d000406c44581c0c80017010b8800000d444803150104c0300254900c200001440900200030207170740191028600000091071440c1c00b607100149400342945030755104441070700551060300c002401c4072101d02c1d000b803004c2c010b50700544007c0280d500e450404a001e5028002c0303005101822002041a6503c4580b4041c2135541031079020103121400300d222000901c07040c3d90b580688460b40c05140c450192620312000c2d03d0101c1421414010300384100b8035841d03800100502158030b18a00165203618180c1c4103401403404e9000595581420002c100c0e171400c2d40710078058410031055007900300442d03100c0d0440d00190b10301c4400070464494001000440c50b0310441c441080002001c1a0010034005a01c5071203901c190b00c4100c09810803a0100150398040c132018034 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 180836645 1250 180835395 180835411
    0xf02010203070f0c03020f06070c0203071707050112060f09020a0314060f040917030403090f08030306010c060203091504050d020f070b0714030403051207020405071d01030e030d1401050306 83
    0x10840c1030070300b009000e8412072100305041025000300c103000d240c802c000c090300580b5502c1c1501d1403811300020090240211040170b82c001d105018000820201d0b40c1074000070041100d0117020401e091000454466003040d00b614034150302d40e100842c04a400c0c01340782000300030540006946814624019041d1405d807441140321014143c03c00c00c1c03544038800d208402c1c07902100c00050008a501d03200d00040c3c0e0400d40758506901c04002c1004064204455038180ea080c80e4402c10600e0760380d04429039900c41201c010380060000c0980c0400151582c026580110041e0280c0751000c0040e41e022885007800c40e4252500d500002d000d109a0307030140000716040004030068103205050800da078041c1e108104008140200b85c41d180b83c2d904109005850145921009482003043d07585000384180d0043d282c2607100b1894580032401d0140290801080500114054201840180010340c000c10074901d04500a010800405030406418070860804400081404905504040a06240c035200a080f00 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 180837895 1250 180836645 180836647
    0x90f1509140102070504050c0d18020103150b0d021305030102070b0a0b031506130b09090610060f270b040e09070b03070504031106040e0405010b0301050a27110307080d0f020102 78
    0x41e03101e9a0226910003600c0050701c000c1056201c10040001c0c9110300503d206034586800b0b07041c3c1c804250a955804150b00036a010b1041000011400e6841c6001d8840c503020204c08000d000c605041c6500903110741070007401c40c0c4e21001e950f900881d003aa4410901103410892020800c1030414241c0b044950620041d40103016014051088054a620140503603100b02c804102c40d201c4921b0039040f00320034100c05481740089041082602c0d0780c443c000c0e00c11003034010901ca00860b085104010b00207810300255035903421040b80c58141c00c0308070350707070380e00c0000e8111030110200c0c2d0351040100400080c11000f81c004454902409102d08100b0a0307001005140d0080051291054ac04410b0780e05a03038020800700c1c5540224070000e0941d00c902e5100412404201c4200001d10206601c400c5c48118280c0090000c1d0743c1d60a480021901014000000002c0300c980908201c9844100701091521841403440f1359080a40000c1c6482965440300c4690351010080700d000b15401000700142c04000e000035 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 180839145 1250 180837895 180837929
    0x211e03010f0501050309030c0f1c0315050402130b0c0304060801080a03140310090f0501170708030a0e040905030d020712050301030803010e0403020102070b0414070b0f040e07090f1509 81
    0x8007240c041e14420746041000c0440403403115007061003151048240c940c2240c0d004c1c800741640d961a0790ba101071854403568032024807260a4044d0082c8031144074290304004c409420310003080025004010b158500010b5444c010807480d481360010b11030703880b040e401561038900d4504020003401058102c2c0107290095405000020340001c000d1801301290070305142c699031031301407441354030303a6039171120b00c40b0b80c00c01b07000901003445588158143c44250034403141c43e521402401da581c00b840d20032030407283e00400844507000d11448420104050090010820044903200c1602d5a0071004004900c50390024500c1c040000174543c001c640041303820403c0c00d540c51910740155038001441921007070184030000608040c401c0d41200d203c1d941c00701002c0c03205d0030306051610300c4100800d190460340c03250768000302e640c9002c03000340c138600031411980314035050800e00150710900c009441c0e1030611004190126058ac444c064074805000700d4501105011041440142600340d954041c212028501c1c2d84 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 180840395 1250 180839145 180839159
    0x41b09060b07030302070f0501020f04031514150f0a0801050a0c020604030c08070f020d0b06010806060c0a0224030a0506031902010e0f211e030a08040b040302211e0301 74
    0x6942e075403038160400585407001070901d41210003002d107000b00103510009408560070103103400303001500e018a4981ca501902482c245046400d04c2c41030000c40703600200051300441300d42c400c03e0f61541014061101c103000b0340d00440c00307510003600884d686035142c0d42001403840f02e5100e040d00e01c1ca543d00c02002c00e800c050310058100c039119000540001800903080041c01180445491200d60140c00482503040c54104008800b02c03c2d1070440c005041030002c20141e24140003618583d880d502d0282580348025802c1005903e509100e600e110107c3c1c4034a0501408158040c602c41c500804000c2460702d020010103092110340f45140c00d842d4071545080c00540d9001840c0b40401e1403c1d0381d0401e2000c2881c0010304010343c3da20704880100002403507403246080205041e4403483e043e07043d82c1010000c500025440c1d0107103031455400107100c0d4002a0104809482d1681c0050182c01510780c8070000044c150300440c8030f40c041084103800000c604000c203840c1080340007607141c400345850443d418400 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 180841645 1250 180840395 180840397
    0x60506091f0e0405070b030405030a030608010c2c0907020d030b09101e05030f0c0405010902090f090c121302090a0903050405010c0201110d020a030908160504090302010f05041b09060b 81
    0x100d00201c2c1c03501c0c00007410441c0400600c4043d0503811708180d01d03442c052400b40c4d5250310600c80074000030306003280060302074014050800040f00a4440348250000b507001160802010401c8000b002180742d0f140c95640c80d1003a0050141099602401008070300503409015502c41d070b44414040c018400800004000c0000710a080e504c2c09a001d0011200f80c0c04019001c212903002541c0c0b501900e80c0542100d000007406625100f0141c1d420300c01683da0f04006c404a00800c1c0903150850301d499403032042c91811810303641d032100440100c1424944104038418111000300c8540104408442c09802986450201c0542c000e10051050000c2912540d009025016900c2100d040c049092030704002c5a0041e8011402007021100f1150701c0701010354025610340d50618103401050350070741c0110300001c020485d42c001c14640340c400f0003c0ca03d4181440001e1028075010740031075584140385600c070081c42c0605130080d4050b8058100320384c22644203140201c141d0740401c820524005003001183c80d204 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 180842895 1250 180841645 180841649
    0x121506010309051e010c020f0a050d08060303040314010207031409010e040b030a08030a0506150f090f280e060102010c09030f050f0d050c010b010503010e0f0c0c0703060506091f 78
    0x8a40440c011210745803d9107032102004520700301c40c513180443c03041d58005622000d00d0021603400c54009000c1c120160345c032403c401d8000342c40303a0491001d100c1d40390302030003005406c040040c0840e0721303081d5a500c441c02d00c2a4030590010786a5000200c14040c10752220304910840c032442c071081d15107aa0000003030441107110903118090303030b11680f40250070355080c00042e507000d4001e02003d90324540541c0000081908813040c501c0780520b982e02050003401601502c002480c01c800c2c082c9804140004c04c8090a042c480c4c943e805404282504036172003003511810458907000b92481c03514cd0501c041005c0312400140300a04581c98210410b60302540401d86404582c1c00001e25080301a06040c0241030100c0e5002080e110302c508500c00e038070a44d22000409003010100001c0003001014401180c2c584020301ca0542202041c0000c11000162402c00580080f4000722092805210402c1d2134100000c580c002ea0314142e8500030021031f41021490940e101c1e401041c841c107180300c2c104009084c07641038 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 180844145 1250 180842895 180842897
    0x90a17011b0507060b041b080610050702060a05030a0603020a090b03011d030f0702060f04080f150f0601181e0906050307030302120f0c07030c0302041506021c1b0b0612150601 77
    0x2810745c003070082d02c03503500c03184c00411404020800010301c024058034044043c0c991501411800c0b0f43c034a1614800d0041c1d441d0141d00501d020314218802d141160280c0000c0c1070303640030301c0c3c0c3c48000000580d66141c140000f845a04030104511105008050843e81036022000c0e03a01829030940d841d683c00401181c40030b40c215802142c41d0041400400c1075030094200c1d00a0380b940008002c111400001444c0c0c003403186406c2120031a6000c10b8501540140a58400f8184220f41c4003060496004100644045807400310610203159035105566030411218065050350201c04004c0c80b04d00c07820b0103101d000d00700c19001070503004d155580003585c0344403511819600103400b01d004240440c0420485140c003403408121503131141c41c0e007465404040709200880c4600d00d040d184c803980f00001d108550444a440e006001c41181e0854883c0c00116007001c031508100582d10140b00005507150001d0000d4000e071540411890b208040c011408100384c1a205c0b1540300400101c041c4c40400712240c0e0102007 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 180845395 1250 180844145 180844151
    0x61e050c0a0f0e06032703090d0209060d021003050a0f09150506010c08030901020421050d110f060108100c1e0c15022116050d090503090a17011b050706 67
    0x1104508a440383c0c15068480c2c2d12400005c24001280b41807000e40c0c41480c072051080e40d0400d42041080d0303503845640e00003a08030210715007040c090300d00782443c954403e0029014501c115280c4d4000b03480ca08804581c10082980c80f001d22038000c2091084140548011004001980d943c0e1a8100a60085002040d16039119400200a40d20980f10019090391094030701c0e03182e0401c0c43e50103000c0c1d003040c0181c80a0b00c80142e50b049540110300f2a00382e80f070350000054644100030020848180004607840890340c411103840d00c001c0030041000383d0080c0700034805041c4650184140c4015540b41003800002c10841050312940c542e08448a04a04020f17403c04489000061605411081c02500a60201440443c511a80c3d17070585407620f40c07840e1110500d0565940340d43e01d0220b407880105c0d03a04005402404101c0c40280c00c0e9004204203400344084070300340080c0c1d800041006e00190000300c80c5003080c42800800803001d002d0b00c0c441c4141070b106044a10400000207044d4024400040c006c261 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 180846645 1250 180845395 180845417
    0x506010e060307050a14030c12031c1e0c030b030f07030c05010306081005100905070c02130c0507020603060402070f080408013813060b09030f06072708030403061e050c0a 75
    0x507013023110303449018001c0c00014640030005481c0c0d4507a0800440d02c440c001d0700007a00703102c0740340c14420200004480e0501c0d42d980704030180a000200b103180494020b0550b10700c240740140d541000f1642003c49100020210141545425591002c040e807000c0d041c1400c084050021600104103001200301401e0005039a03a2050200002003456500c191200351808050180050b40b01d52020800b60007954000f25003010030300c8440844010301d0150000402c180300d2030006250001c011504080010400345c10000740b6280e040d558400960106c8500300000f400f00450030003802004c4581e00d1104082000c5000005421410324400000c0c4100020f8002e41e00c00507520000000c103500314600c0100101c41c1c1b10341c003280043d402849410303c03030310500041000c007030b100149461080c2c90541d100300003000c1041c40f90b150b130885100003c04130301000b00040f07811002040038200640c059079012506000501f8062000e40c0c20300340301102c0e90b0030441008011801d10301100d000310224642050140 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 180847895 1250 180846645 180846649
    0x3090d140a02090a020c010b030a0507050d15050a02070203100515010f182702041d221104050609040c05011107050613080607050307090504020d020904090506010e060307050a14 78
    0x190034000d5010f00060705008141c0004d0b8080c058007040c6400802140b443d0a040640d141c84030304000301a584003400c203202c1c034203041191004070303441124801d4208580b103024a040c0c800c200c40c12510b15601103000415031900300102d5100041c120004c00060507c1e80016002801d074000c114140481e1508044555100c3c0750f03004c00c081e00012040d89041c0d00c403030881d0080e0300c10303003048485101b0001d0800d0111440d44200c50464620886d4030405555140b0902152540140510414100030041c3c83d01d00d070400c0c400d107000034403071494410988241c004000c202c88014140c42c0c090031a040c104000505011441c0003030340c200342041030340906000c41251030b04280e41c0040d5040340b80416585140104900c03a081039508880949942d541e507a0012681808100e56107400070740c15071360401c01400c00340c0c0103180e4106945009807a051030322000c070701500c0c0320102c1110740303600c160300401c1030300b200b5140d00d60401012405441503a00c2c00c0b0028001030303524050403040c0c10303900081c04404c0d = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 180849145 1250 180847895 180847903
    0xf3b15040312020a020a120918050a320a0e030306010c020a05101206060e011e090909080304050f0303090309040e0c03060103080a020106060509011704060908030a020a0306050303090d14 82
    0xb0342d04004042d541c4400d03a41c0d0003500c443c03100c401150741c1d4150f01040d44500d030144010700309a03000c640429511110070703d1804c0c050000a0885000250750b103402c00d2425000202802c030106107014964109860440c0844190000a018900700303440c0c62822122941c01008136904044246000d5402c8550341c00041d9808161f81e003c0ca90009421100c00a029002580818400c0c0030000410205035205c209072079101049000a00140c10b031a2450394180065020140c5284946084001070792500324082c100c1c0c0c510001a229000c0200c10881004010001c4e6000d05040d000610708505040c400d4071740c0c0780100d559640c407840c0c5801b41e0090b814010007008074200310040c2107801c0b40d6501e0428130b0b003e41c4054202c00c015400d0070000300e04103001c3c01c01c07501900e4040c2c0d03444820b0100c0907400c07049040043d104503001c60f196400400403ca038100550701070b207104000103031340b018004009000ca0b01c131039204a0182d0014800000d007582e4200200c101107800c00018180c0840798013200e410 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 180850395 1250 180849145 180849167
    0x50609060906072409030201050f041214070b07050c010b10082403010c03051008060412260709140103090206030a15150503010302010e06090d150f3b150403 69
    0x2044000c06513100940703529070012890240650020001611080000e2035000d10403900900f4015507817a42d8a144c0b849418031a034200f0840c6055400c2c0034107681c0d100ca0700c02382a50090001400810141e0984000307100302c2401a404031030b0084000c0d1000c80141041e28020010421095481010007195100d4074003403044030b5005008000e508101003000d8014141501c1c401d82c0c29200030701c041804000020b903103004681000000d101d00e0203001084801980480310741820000100c0300c00d00d200c254079107290040714540c9a07078440605001d01c902c21103072001c0003141014104015180940c50317003400c5903000300300ea44000c00c02d0042c0d0100c10f800d01ca404e03400001c41d4000c100080e50b42944c0480614140c0b0b100f640c0d85010032030780c0000c02c80d0a01030203268941c8642c01007420000140d03d10a107440c2c180a02c0700206148009082100845051100070003203180c0442640c400c83d0f40c00c05842000c03916904060000c0d440e240c281c6507461240d2800c0718940e141000201d024107020307c08640d1 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 180851645 1250 180850395 180850433
    0x30c040801060e01290706020703053a0c0914010509130203041a060f040c031512060506030304060c0b221a0702030c0c041806022205060906090607 65
    0x41200e55801c1103d9032000244110500708460400c8007100300d81121088050000f05020142013144648441c0025804500110140b01c810408507095103986000066030304560381c00c4007400c00c8403e034860440320100110600c940e10b00a000003a05030041561070a540ea100c01540f0050440801078a540c8120400c01348d02403200104034803c20b15540066110f05d100f6050840800d1810661620028041c0c1d02d09501c184501806c050a040c194064015019246808900104042d48070070308004160081c01440001035654400d10031075000382c1d500040b05030011450980342a00040c680701c98800010a05d00c900008a40070540030b000c14200014942e4a160b042c1c0e07041d20300403081c7c2910704e540d0384584a0441c002500c5600103c103640c0d00210b90000b90100c200300608000c0200351758444501680342c100120000306600c1e10280c1500001e261078032071250510a42c00c0020502c0381d004907c942d401b003200b4001901c8200560702140d10079104c00f40c0344c2030b19140503030401d840005d040d2 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 180852895 1250 180851645 180851651
    0x8072c040225030906030b0f091005040e16051c03080403090503120408060906060a05120109050d1106010b040b07060f0207020d05100b06030606190c0804031a0c071205030c040801 79
    0x2007000007501c002803074251098854138101642ea1009900343ca4a00451544c8080100b4409006e070030025202e90f4400300c05030f98404501e4076140003904491158884d06500d0b440400101c0034862403804070806007a08803845086042040414003e1921683c030003401c1080ca03070041070401d070141d80f04001400300142983c984440707103200408140c03c10712624803180300f020082a00b480001c15442c2c06100c0241c14150b40a041c0301c2803060399610080186501d41d038a00d07541d00440d10510121035010707800c1d03442c0c034420700304c00c8541b0b0f1400b401038015010520080002b0842078103042e0031a85036640c00480450041d200300c688400074050118040d405c000150781020401c84085244200f003584010104030407825030061101902086408580100d001c0091035038003c42500681402c40051814804100090b652904150803680c012256602100c0f1012562402d20860950005458000d1414003900c4d44540d00b031041d26100b401700380400000425000c02030ba000f203c2c00381083d50024 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 180854145 1250 180852895 180852937
    0x50c030112030507061109012c04020f130b0415050c191118010801060911180312070c050a1a070624060503060f010201020a171504060b0a08072c0402 66
    0x1031b64030307640003003000c0740012241054083e60b05000508240c4580000040c00740c88030500b410b21000b544211000030955005015011901c00e0f0381d00d0b040d0241108101060300c59142c0714800c0c1ca5000c003000d025083c80f00601a0740d540030303c001140a0400c0000302da04100b00d9090401100965025200a42114500c0c1018024001510415048407401c1008024042da00c0540c94211007102040c0d001d003010420000854402e00c1414940e54180201034403e2006540000314a6910404c0120341400b0044001c20561070710005910080507512020b1115850443c610308051150326030084c5002d550700c42c0d17003044259801021b0b0b0740302070746220181c1d02038407114042e11940045039624030400c1d0b107200c40c030081d51040c02580c804c03401c2500d45800104c13604074032000703a00e4000c00d80d0440c2a40102c020800e65510302840c001410907480d40c66031480398210060824100030841e0302130140e005500c20f03010000f01d00300c155200c1e032400744500342003440002030040d200c1c038403510411850030115 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 180855395 1250 180854145 180854171
    0xb04060215060307080a26070f06050703021606020d0f0e0f010e03070c061d0d03030203070216030506011202010e04091407090509060a0b01020a0203060403090f0504050c03011203050706 82
    0x60701c00d08048082428110b942c80300101681d50a00d40541d6150340c000301e64040003d6250001403480110401455040001010591440782c1000300f060703510704829100c3c43c0a0040a00c034032a00042145415480d01c40c030b4100e210395603038103440000c1030642c1c0010601c4800c481507011315071400040d001401802c103040030f0503a07101c1c1451441e03441e0794038010010141030400011640749541c0803061010305460300d032080d280c039001348034804000ca2181c0c000650310344d03c031050481c90600c25180181c0701d080c0032100a18190358010500c000342d892100500100300001180c0b030440b4403003801441c04180d07a10040750a0f070000320103580c119050120140400003000000440c50075440111501140d49010803000d0f940203403540c050030703040300c0d01003880460682c00211110340107004840081c65142c0c04a0720f000b20880e13040d000039140e51428401d80c40c010004d4001050112000d1040f410031000c010f483d88010b10503483c2c0100c21031040010140260160340b44c440d0486010002050b0f4824 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 180856645 1250 180855395 180855403
    0x5010b0d180b0708090f03030a060e15010e040216020405090a02041103310206120105090901060b031906030f3215040c09020f0414030f0607030f060b040602 69
    0x416462a14200580420000c03444040c1c400401d800c0401c0404503242e0980c02c0e6034450300640010060f003da000d2031b411030002000107501903088584005007071403421521452000003e8034800d59000488540701c076903a80180070306c680f40d10885006075184a06611500e28107613921000790041d0030300c402c00202c1880804c0700c0c2c10799070094806000b0720321040f0381c100d82444201d901400003c1905440701e101100c5c003039002c80d04c0c0d03400c500c00c101000c000e400091075504500900050305401d00e00501c030a040c41650550044652002409981d0400340c0407100e5020007444050844c01c010002040e41c031440d040b217401160050b58800d004000c5041c00c400a01c0507a0441010b4445103600100c400720041c402d01182c0c1d5444090034001c00d0042d014100032102800c103654000700d8440100c1c079110648001d0401168003c01540c0d07551400f282c03241054100c0800c0c41c4a13400105560960100c0869a00c0e44208945800a40e61401441c0a4004c0541d80c00250707498002107408a480d40d0000313 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 180857895 1250 180856645 180856657
    0xb070516060b09130b01090218060d021902070f1e05040c080709050901030209182d0c04020a17100306021603110d140f070512070b0c0a020d0c080d05010b 68
    0x6512005582e80784c03548070504e0740c4401002481601e00500401c00070f1201d41c007600b444010326240c41784507000340001481079007180d641400c0c6103900241e803101e207a02c0700108405102840c006420b92902c6c14540900c100d090b4030448a084142c2c1496150101c4480b0140c400b03031200400070400c1c02c1d202c981c0201501c504503505000300300a014045082d25000f1030260480c1d03070061080d01c480e52102c1861100c11030031082c0c0c454520070641224094090401e030b8591030046903000903543c290f03070341500e0701e812004505640910700c104111020a03621808000d101c54502c008004182c6512045039240c809517840500310341d20110390025003c880c15051001980666620344a0199039030041c0e8681010711245008a030200a1130007001a0300701c050047c650714561104e040901c075031201402d042008410344408000040c00c1c504011003184400c1c1c00913540ca6440b4200394007100044d6580e043c594140090003d840028001c000314203080b9404860342c08400e004650f0f5400c2145000e40080c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 180859145 1250 180857895 180857899
    0x3061918052205030405010f0e2e0804050a020103050702120f031006051c0c030207060f0914030a0f0e0409080d09030306050d1e1406040f050706030b0d0b070516060b 73
    0x2e2600d070458010150215002c003508240903616183c40c2c4001500d038800e1a220034801d000c66000146d410380d95000d80c19441c4481c3c00b031300c222541150895a5503400803050311034140b007504000e06c40400c00c005280c80f04680d0a090024641d11031500031b901d03000380c0c0c002d21188910002601c84403c05283c0285020b03503520848080002d44810f010780c0c0340d01881d1608103181042c0500004010040c5e0425482d142c3d80381401841c002140e190141034841c254802001030785c039140004200020f4041280400b21450042c604190380244010700340207800102104201d0621144c81055071140d105049065000c0340d142c2d80c80840c4030303120010f448003d5043e004285007541c001060b007400c8100364400e41d408802d100c41032104012180070b0180c82d440640d803104002008072050b00c000c00985005e03034010500309420002e02c0c82d0080c6808003a4000c80708040c149100c811650b181d0341d034024026036004039441d616a0720842d045681313016661240c60100444164402800225801080c04e443c003 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 180860395 1250 180859145 180859171
    0x9051903031b050406020a1511070c030b0604060e04060f020d0c020c010e0108010b120a0e0a05060114150901120e060705120109060e060607050c0901060e090609010b0306191805 78
    0x449003c2c0c8090007036204550240c3c004405200c000b5109510b40060300c642c03824001144402001118000c1c1c02925040b0b8001032185402d0040c0f11172003280c190301c00001c030b800b070041d0350a051403d00100301c0548010145500e90501c016909100d406640e4001141c020801040608e8880203540315101500d0502042020300c0014440d44103058060603196409086450220b00002106403003a00034100c200b03441e0f40740ea031030401500900210741128003620003402c240d41064103c810003010501d00314483c541c1800803600c00b000c100151400e410023401c02180c013240f940f0300e11000d03094003102e0000034000d24040044458010018180a09141c0a5021180e07251241d000854680b4003440c075481c01c1d0701001400b030307150281c01016a03920440546110180b0400451980b1600380c0041c0c011408480507192503041043c06241c4c0902c00300d42c041641d51501c0320008951101520841c01041050803409401103100404001480140021445880b03401d1400c0e00400007911804100c1c1c80e = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 180861645 1250 180860395 180860441
    0x423040c080c031501050f120105030601080102070b0103080f12071d04090218100e0a050601031103070e010e1518040506030d0509040504140d17070306060507060905190303 76
    0x110408070244500d414145041c615141c0e07102e8809407241058103141000700400170f10340c00d0080080a01401700700c4a0340d802065041804040c1001c60580210409a1041c010780000c100c1c1150440d04407600406140e41d90281c4000c810748510072585048090341840c0140010907500c00e8007154040e900c1130150034401c1e80d400c100703c141d0f4a489000fa610882d2a82106c070043c00b1754100940007107030001d01454207580c2d2480b00d001c8000c12118018595515002c10007a941c15024441e040085a421140f443c5000302010305030601041d40380c0d042012b18a0714100e00e89800c88812100682d2202c4580c03515028101c08042c50b0b401541c0c03501641c14640403405070305000425070001811529902c2c117206150b01031100500f0001e0040da0000d0500b019121251000e20048818010943d03c13085440780494050130310030070240c001001c0524000d4200040c03070b400415503100503401480407412820310b0030000d250480c08260600500601c2a0003003c060b05641310070360382d40d400c0c0c00100b0050 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 180862895 1250 180861645 180861647
    0x2031608030319020705150907050d030503131502130306140106020d0c111824030d0e060f030709030c1215050a0e030f040f05030604021c05030423040c 67
    0x205540c4a220400d0340103001040504561050500c43e803502c60f04014241300d29511240d151442c0514070540c030300e50a03800d110b04040140084030150806440428a401c09a0f50003403091000a04001907503000340e49601c08c000c1c500180951004a4003020764941c900010741c03208868403480304481e11031a000c18640e8201c00849014100c030b00c140c020300b0034200481c0003030710a290300000071160901d5502c00e03110143d4940000c0a10b2000036428803003503262003442c030001d20403600950400e01440271003581040c3d90008132168840b03003a28012040c6004030b404209036019520005042c0b090210402c07020340c0c0e000a41c00100e9000d00e8800d040550303500d05415508070340c024060a85068992041500f0082d6045035030071912152000802d0740d40c1148090840d004609810a90140050100845d24650982c20050715049000d0403c40c00c240e40026440034a00110041400c02c815070304080c4007080c400c1d24020301240c041c805418508040c0c0c82840322104004510403840d000d0444500d0b = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 180864145 1250 180862895 180862933
    0xb040603061d04030804080c06070305010501110601051c23060610090f03060203090f060132130e10020c03091f08040b13060e210a050430030206040203 67
    0x502c1d5401800d1503d841e2520101c41d41e000041064580304001c22210600c41410407025100b00920780d4002019414003000614404501c0d0700905036070b01180c01801907580f2405080c0d100d410340100d149802115142c403084000c0701060519801c2c1c1a07100400c0d0021000c608240309003011103803e20018105202541e150115008000031b40652400c10710000315203600030b41d0483d0f4004219142190050340e0309240003000d80002c55450380b00c1c041c01e456082d90040d00d5080c110803400c0c10423410200000b05405680d02981b819010b52900a203450420b0b00b4041158540c140303840c10340d901c2c00c150007242c1e0707254403c01403940902805001031034840e8030880700581c000c0c110b0f82d801080f5125902c82003094480584a07010003550128440c00140b028840c2d4081a804c20019240744c0c040303c10342e02c21120401c49050900d0f17504002d00e001c0180d1280444083d00c42c4c01c03654209c2c0502c424038001030000300b211140c550080c616000400d142c0c00003001c41c480e40c0308400701c48150003005040060 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 180865395 1250 180864145 180864179
    0x2091003050303010b07020109080604120801270c0c0c1409280b04020f130806010504020a0f03050a1401090905010e1605090a11040308040e010504020339040b04060306 74
    0x705400a0005009030112040103104482c014074101041e40d484a1545041400903201110041d0174401140301103030304945d0450042c0092205c121080c0c1d0465041002e1141100c81d41c080243c2d0b07125040003950048280f60303c856042240c903403040340c50701c40c3c0c1c80038202e8194080e403140c080d8400068503400d80c0315031780100a4800100740720307000b4075111010150560807481648982c00348808860000582c0241660040c0a00d1402e030151070501d84901b80724043e0000c2c0d01643c0100070a8401030f420208650303450096282c0003c1581d02c003080c0400030080680c190307020140f0300c400010761683c2500310104290080008105207443c043c02c8503500c60250074840c0d21b00484050401c550b00d003d074803403940103080050103d400b404403d10440e0640c040d8004450b003010110307081c0302d0383c880c0710340941c00b400b005d031030071441c6007400410000d107400b00c141100489034005002078080800b03d581c081401c0580525907480340e8507105920303043c0c1c001c0d0054800191504030002a1041d07004981c4034 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 180866645 1250 180865395 180865403
    0x5040c08062d130308060d060513020103150506160f0501020a081509070806130e0604030504060813020f040903030207050f010507030b0a0f06030b0316090c030506180109200c0a02091003 82
    0x240110184e602a95030a13001004240e1140100700203102080c11030289621034804144150310301c28041c0700140407a96494403911811059600c1403000c1d4640c0e030200c03451803210450301c036104c0c1d844c1c1c90314a00d0301032406402045540081030200c4041d80000c10140034400c041070820800c1310078028044240342c01c03111000050407040101e2018148030710116640c1c40c00401c0800d00c0706038072101618040d8141c03400c0b00081d10000b42000700c0341d0701118180d009103617070852803480b1005400094140702d101300c81c5441550b441c010b20003054002d07030482d0038030750303003d0700b51000b001d00c014149000b0b24040310304401090410914081e1340c506015070800ba22400e41241007940c2c2051003c070700401840005a8051240c0f01450302107000040c1600010704801d20041144905000c0090507100090000d50160000c0310001001c00e20304204141540c3c41140006110b6504041e02c0312907a40c4503a80702413680b4005181c4030301e50b03c0812028040e070700a8a100101d40c46110401c94148181d2202074 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 180867895 1250 180866645 180866671
    0x806030307030e012012040f0f0b070201050f04080d0e0f0f0102060c090d0804121502072312070609050705010c0804031106040902282105040c08062d 66
    0x50070340c060807020b000b903120300c455810409100041d246c40c1980c54106400b00303d00118003000403800c0c01ca01078014020761414040c81e0740c44d0185210a80c040c00c040241030190100307001c4010006401614010010001196941c943d20700e0050310011200b01c050707018090400d100e40762800e100c1e00001022106a0082034103030350350000c1c1c90075504560700309980046003011502c0400c91030301c040d1016001400c051820305e00750349008a143e180701c8880c20034550041c8000804242070b8040d001d8032500403000d42113100b600030101d07420a1507078604690000000b250190030b00419a01c00141c01c1d1080c1b08440a041d110350055450f81107510000f060440700f000180000380c0000d85c3c5e000250000b130105d80c189600c8034044000c0c2e0300501c41c0c0340d4100c000065a11554814550f03084035000150400308800c030604041003002c8018074507a201110748031400314080062401c2110010b00801c0e007915640c0c03c1015121080b1103408010b05110703014903480540e40c40380462481c1c01219036200300 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 180869145 1250 180867895 180867917
    0xc090b21040204060b07050f0d080c0304030305090f0610090f02130b0a020a0b0a0b180f01061d0d0303020c150903070609111f020f0303040507090b061603020c01080603030703 77
    0x180c00c25030003002243c2064660400140b040c04050190504a2050010f0016018003000f05464003c01050800803c1040020304c201e40c0001340460740c01a4040c940410280d803181d02c0300345000208000030b034071486680d08025212000ca0f00600960b071280e88240301c070302406400c0310f007030f40203017a0140130307200b1249400c1041c104080010803451006005860400c9416294109840790440c0d0480f03500d138403400480424504458600c40c0039580c0803607644242010b001d400c401440502071704080c003001181640200c2e01d14654071003500401400f66589080ca0316000740650040d00701c250f050b10071030a12141142060000c1c51117102d01000031410003503e600d0303900c06809060000d452200d0440b8400341140c4035034800e1092103407a0a58001f00c00c04105000f440c280302d150109200e0f40050061200140021810b20125001000040381c0785800c1000520342d4818081c1b42c41ca004514000542007540100700c0aa4040007600c0300c0b03c060783c800090640364851110b0003000a0182400 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 180870395 1250 180869145 180869197
    0x303091d06031018050a03080a0c0c0f12110303090d08010803041202061305190810020705191a0709060305010b310503010f061410020a0f02041e0c090b 67
    0x140f6990130702201c5001c195003031500c44030300300341070010194000b51540d0308000600b0018002c0042c0c5185601d0312a8482056444029909059000041c50f07007021101082d080c3c1e1056100c10b100d8000401901c0d07403404c1a0345016070780c60b0f00c02540004a09090000117809402106880407941c0e6451000209401c0d582040500c3e0310141001d1070003070a803400850943c84060a400d1000354440c0d11002841c2403a5009207004403980d180c004107801000445c00107240841c040b10340714000b00d031b026075040961408030022103c03150103140c800019000c000c030a40e03000c03801404075001c9480070080d80e6201c149000d09845141d504248484500300f988030f4694590b10350300b91009c401200000041c2c0c4038400642907905451140c0742407500e0750b0003031101e170341020820460000100d88903104902d44400194480c030071000c001d002d24060f03c00036410343d10380340c000d140c80511401d2036215800c528540f200041050105030300009440b00360104084514104461240b130308102c80e01030b5000d50400c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 180871645 1250 180870395 180870401
    0x1201020904050f0f0127020c0c030609010507140f1b07240c030f0e030f102a1202070209010f080c0a0b0f0903030403060f141b09040b0d020a0303091d060310 69
    0x3504500054a0f0714500480c850f551000d0194009110049c04044c4001c0e806c0501d400c101406902240e4500014810311541005c02c503075469582019540d1a650142100318050083c140c0750199040c01c41100400000c0105040b010f9410b9045ea00c044812039040d034005200350010b41c038000c50450484c0e880400d000e2072070000103400f24a00300c04411040000b0a04000030512581035a5010402064095030113000e0704080358044040280b51040d00d042a80d2403a903c040d00e9801d01a50f4100406034507101d03011035101d1900a0141e4950b960743e440000c2024070188514040750240000e07080091418900382002c44140305a83ca0804100500e11241030f8070170b0440e168941f04c108030000020b6564007d404803005a0740000070900180700a00755640802050f450014201c480d04140965160064401c82070b4140c0e03001410f90800360205904c0ca0b032001000e0340c403005108001007010780c81030400d005e456001c172242c44016102682500d2010003500c034658981c100d45c9841480d008954 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 180872895 1250 180871645 180871679
    0xa090201050f1b070803032a2b180b07020102030411040c020a0b0408040501110f1009020a050d050a030e1e0904030225091505010507021306051201020904050f0f01 72
    0x20802e203080850350304004d2900c03600b03520000c0e1641000c403c0116010b0240030741441400d00f000040c4c04080c0340ca41c5d9805c1407060640c0c10060855100d2200103403007012290303034117115044074104820310744901e034840c010b080204115a091040701c0042c02c0c052060003540c0c011940050361406052355101040040c0107803000041c114451040c215000c907035040307d464012030141103c00da6540c102800140b09100310005002154803d060080b0f1407007000036076031034200201400003400c0c480391000411106880c0e200075444101d40200000380007020803003441c214840d0708d424502200000078026411450701a90810241d80c041c0400788e402c086d0040c6900ca4401d20544117404c0d09503003a1683c902c18044c0004a4038a009000d000354410b621881a071740d02880e1150180d60718000000300140b041d504002e001e01c000b070100c4164990303143c01050180c280242150201130003954240e000350000f840d09032185007084c000c2100e002c040b90070b2901815419428144581c200b10341a00000221 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 180874145 1250 180872895 180872917
    0x91b1606020d091401050708040c030b060409060c02030c012f0c0c041404050f16141f020307061103010b0405010c080c070b0304060515031b060702030304030b040b0a090201050f 78
    0x81100a5419a10744550300c2d20703620480040580702d4184d8041030844030018a840140580390041c400414211130584040742c2c0d10040729807650ba15880400c000d07241c8050010300c1d903414160803950b00383d008006040a540100002c00044074034503080007070420760070750801800c082c0c0008940601082401843c40c00d02020455048400c00303000f00d811168604000c40c00f00d02500b0a00c810464103121059001e0070500c010400c056180342c078611090402e1150071800401e481c4220100e4543c2e01040016010218055054803610b1a01a44a0b4000082210038901d8215000080400c560aa9060f41ca4808216061604042c015244801200016034901500703000c22102041c0c00c020590250001081c2c00e92682828602074046e100090301d034062084101803071400030b450000343c02c01c41c0020034410710350707210503c0045620f601c50383e80040e4050200141c0801480400d1000c00e00641c840c080c214081c0d540d815944046810703446000b800524201710780350640b03094a014056209403 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 180875395 1250 180874145 180874147
    0x30c020705180403110f07152303220f02040b010903080a030b0f031b1c170a0e0a030503030406050402040f0f0c030b0a120b1b030403030b091b160602 66
    0x7928002031104148110305200c0c90000700400040644c0003000f8010914600c0c01021401c41c401085926004103000e0300032050300a002d02c46605104541d0501007102049400540e200840700903c0640d20032601719214044030020030007900350b05000c1041d51508007004105e01c4c3d0095080001402c6200c40301810000100000700c0400d22500040a1002c00c0d07032030005800c1424001c2c000d906120178003161082d0400c41c000c511f0517a042400b03504c20002107400182c401248901e249100f03a11000c050444c18581d15901c0c40c5007103042c002e0402c0c840c56200c04120300151410009100490b0000420640061011600181c440d40010340c00510041000c0b80640203034181400701e035030481e119940b882c1c5407205444115018828208064003c3d00c80e09c003c10700704803840c000c20800c0b003030041080c0103080c0011426018050002c800d21044020030b540c900309818010090b14110301c100f0302c2154038101203111500d240d01d00003600c1c01e02c885400c1c1041107142074000c8280744d0340c80076500d00350 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 180876645 1250 180875395 180875399
    0x306010e0a0e0703052202010f120f27080a0806030109060207050c010806040612030818060108030a0801060305060d030309050106051c0512030f13050109050706091502061501030c0207 81
    0x1480200703107006404000307810002c514110030700a00b82d400103002210400301c0840c00500f401c0018810482050f020b0805081d1040c2e02c04088400041c41d200d460300c01c6142c8129450a801d4541055071200001c1c800c1002c0050f011203005c0e085103e200c002020907004004c0d8050150140b00003640c01b07800200005904469621040240d9002650442c0d00341c02c910b80c180303007075030b00083c07003e0700f042094078100442030602ea8203080003d804580601840b000c1000a01e10709154003038030b218020710700141c0744956500d4030705540e42d4100040501c003081d2010004500c1620070b201d440e04c00c9400826110081c00c003600d044e0000c060345401a20b0742c0d501c0303040124964403184041882003401040780c200700b48140c2003890408034411641182c0d09810414080e059110504480d089144080207800105051500a004140c00c1d1001080340c003602740005600d58100d009682100c120030058004d2440d07080c0100d032180012203005d05000c9064041c03017005e52081d071141191000900442c0c0d90b041d = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 180877895 1250 180876645 180876649
    0x91008030703090512070501020d030b0a0506040f030203060703020a0f050901120c0503011d06060f0912010f020304030e030c090a0c0504050312130f0b03060607031b120207050109030b0c0306010e 86
    0x1d4030035841540840c644000802c0703141803c0401c480c0350060a000745c404607041c100000d441d00340340e24281c4c0815440e02c080d030403030b40c1d24850700800610300145410f9540f940d030448841c0d030510341e06c03080e403181c01201c00040b17a09009000315500c2d01c1007a510070b01c00c41c086a80641d4030783c009488940c100020701808500e0584144102031218040791103c2e6101e40c98040d940701030814110b00c0c1034100b11803905201550315400144d80401c0c0c0740c81d10450322910080d01041265034206c80f10f034402d6007420111804016241d00a5000390300907071380d0180e0184401d007410382d1022303c45182c42c0c0203000d48001401014107940f0110068070f1a2600314a002d0b40c484c0000e1038030b2501c5400d040b80440020f00880d101e040c40d841c1b10b0080000c0041d40011901d4541e48000307a02000b411103002e1000003404004152190794480f164182100480c0d0003506141043d0007994010354170000540b0401d40007260541c000c2e50f4083c1101c1d0b100400301c026a95200c0c650b6840e40000c0c10850501580c4078901c4426 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 180879145 1250 180877895 180877897
    0x3041e08030403030519020c0309040b150a0906031d0a0201030903021006030317090606090c0c010f0f05090c060c030f2a06070219020a050d0f1704030302010501150e09100803 77
    0x142d0007554086202c2c101071841c003283c005029400700c0c6c04c1c3d00c1000103401e40b25000c0103940b0421021140028602184004200c03464500c0300794448216001070b08008142e0041e201906440041ea410000c0601f528101031500c0d0780703003c000c2d60682c001c0010100540c403940010310124881d00c140c5030f210749140801e500381d451f01d07007048022885800ca10082d0841d40b002d01503011007900000d12075800c1100c0031039190500030f0680058848001aa02c1c0e160809411001d24051450020040780d20032100820081c4025a246601c82c002c0c1c10352103070140350001c2600c44001c0c611000d10b15208400b244101150b02c82c0c5070b16220380c0c201c542d604808510f42c0544c412101d40c120060440ca2424001c02810100d101a000c0b4144000106060240e2603000c074040039a441030b60f0384d8905201c14201600d80540065000b420b900f581c401d6080d072645114050400c4903c05c0d0020301c507590300c1e6450300325400b13110003120700010305080030303550586499070302c0ca50807122901940740680d890350140c80c11 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 180880395 1250 180879145 180879151
    0x6090203100e0a05040b0f0a0207050601263c101508190210030227011812120504090e0a0b0105010e0d03110102160c06020c1503041e0803 61
    0x2140c45074601000042007080081e50300106000d4100000e01c0c080e9206000480094400445903a02d400002d9800c01c4c40d50441e02c0c3d40d41c000c0d04482e055070f910b42004000603030b90b200c00036601e00301080f80e906006c0001840c000289030281c00000448801400a06481c0030f00b559540b00404c030045400003050912001800c0c401c42c9401081031245240056401807480e03000c51055402180b010b1146090460700c0740c05507034122203448441821f281700301c000e405114180a02e4800d031079948000002500c4502d0a41c90302038a400040c002c00444029020b0068071904070342401c98011480002e842440c10480e40603941402400d068413049000c0c100d5002d424004c001e58000c1e18504180308204003954010642481e0003002c0700111004116000d04240000b070502c0562240920100403c3d01521802a1181091160002d00341495414450903110f5000503010300398940120f0b080049442ea00144001900e61454a80d544c5600110300240341280800c080410b0080001705014010341c0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 180881645 1250 180880395 180880411
    0xf0501270501050d0b1e090903040305071401090e07020a140c010206010b07030212030406050f062704020109051005040f062307020d08030103060f0c030b010905090c0c070e0a0c090506030109050a06090203 90
    0x40c40751010007d11001c5e040103022007030031354400e11040000820001c0e410701940c207140c000f40b454010f03030300041e5190010b680145034031070098010058400c0c0c0c00281d000034540103040404801d03492000e0643c031900e407e2109070050300683c006106a141050007800c0e550704c20b00c100d810320742c242540009540c0055404a403403a4440080c80f600a807030a04454104100b00c41d500300c802030b00502480b50070f92900406c01c3d00d100e02c4000405680c003840d00341d802000c0107050f110703d20000341402400390b809401100340100d034502e4049501307031003a6100421808215190038090f10000c02107030301d1750403821007260710800c4101c0b8000012007140c00b0754000d42c0300e803901003103903003a0030442c1054468104000c02018603100c02c9000d50788e030041481d411a00701341e44407100d0f03884e00c1c120441c25200306015000303940b14282000604c80b88803245144225056141044512012441144c80c247e0341c0c456030f40d20100c00d000512008800d0360003550080240d0f4000240540e64602a6007030f60021035201d0 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 180882895 1250 180881645 180881689
    0x20a1715013c321b010b060a030e150411060f0d090c050f101b0201031b0f022107060b01023406081308031801060f0501270501050d0b 59
    0x2220114041e404143c1c0f10b600c41d4030221183e01d28403030041c00c0d004a02e10403036413000800c00307607142c21002c0d8440c04841c00c029090540d501520000a0040c00f141c0420740c84030f10030080142080308034000324500885d80403d81c03c145c0d43c3c2d91410088030390841d0440c2c1000d503c08124100140c0d40d248a043c1071940300d0700820b540307180303006d040100c1004201100c41c012000c445620041030b50104060701031655100c05103000300e0207800120001c04e904801301101c1c031240480386450b2030304026001d5150095500700c501401c100d85c0b1902e072920000c20800c0341914103102d40d000180700e0360807400d16500184100ca03000c00048100c8000c4901c1059040c5e041c441084e10005003400d0030603094043c1c90213003009142410302000c100c907641241500982068030100c003003001e2041051111119110001c000d0280700d03182c020300f2440940300c0c0308881c00b240c82000c2d4a190448850820642126412008120303245442d0054030707640c6c003e1103501c01c416602c1d801030103140d9500c0083c15140c810a281da03 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 180884145 1250 180882895 180882917
    0x1b060c0f0c12010b0a090c02030c0a0c1e060f0503041a0a050a0c09050a090b03030702150a0e010806010203030a09030522050a05040e07060f0302070204020a1715013c 73
    0x4000004002142c0c015164104420b60205440c0c400c0b207841160384080c03002803010b061000403415409030500c0d07002c4600030b5201c041e040c800e0110524054440080e0f1003000100102014000103142d40701c0c840c08150951039203203005000750013542e4400d00450354420607a040703a01c812410b181c1120441a01980c1e203050080d080003034490358196540d0f0b400c0c1a900c00d400c140018123041c11354403d4000068035032203035180079203013801900d44d0319902811600d0150402141010a40c01c510f41150000b0300310024985958481c1c0f81440c064001070b0007031030ac3c40c0c840904000241c0ba0458042c0d0500070200b0610203035450400c0c2c02d82c4031084100321050900d040004001e000d600d254460340c4194184000d04a09040200b81c2c4822158541408402d0f5001003505070040e0189010207540070348007280d04001181c20040c0c1048406645200207501d5803013000d15803950201d8004c0314000348882e07180040000d08a21081c01c1443c400413807485915218204d0520369003030581c40030000d001e094007 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 180885395 1250 180884145 180884149
    0xb07020a060b0a0506040306020708040504020406021509010209060d0b010c140d1106010302030303010b160c0938040f021b010e0d260a1506031a030604051b060c0f0c 73
    0xa618042e00080316100006072808002500f1801603010142030f10740d0019002c420803094000b25002000098015900c0b1507a4000c06511085402c20fa808594806400100c00d0007040c1b00f140c81400005001e01d00f06240c3c02108c100400c0c0c0784026506200c0c40314207000115030b0305004450425004070007410324200005c0d00a1503441345403851b04403a80b0003c0140b00594000c0160713030640b0084840c060b00d0b81d10f1060147c1186403034036409404c04140c5a404950002c0700c1d001914141c109002c405a8120211424061201004411007030100359414120543ca42a000300780e11007240341000d814041d80790242c0e00d10f5040701d000d01d4800e80d900c0c03181c140125001d104850600325a424445840c00302066000d224050f407208507064072450b40300040150303030079034840516040b1031482c22488039240d0304081c0003032840142440d45407007480c508075032500d0001244c501c105d40c000040d05c44211440c400000f49040c4480f51507110805120007801c00c3ca08012075817507201c0d07020082442541c6441 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 180886645 1250 180885395 180885401
    0xf0c140906090c070c030b040b0114060a02120904091a0105010215041109061c0c090b0a03110402160218011a1801110709020d0b041104300b07020a06 66
    0x519501480360181002140c0c0c0e14001c41c150320941e20b2071610f039501403515014800207001d80000704501604400d03c010b0220090005050b01c000205861140741030030b08000d80e40c000d00100c0702c0141d006040c0201400d4440340688292500a400411a0b9915548240d40c0c8204802114050040366004202541e4100108129000713007980004450a05482d030a04c0e503000414114042c4407036002150f02c0e0740f1840410206160f4140c071a1030903280c0c5280c0b0031170704006032194030060782c14500000000d141c11944481102c0d030203203081000d44600d1080c400a9080490315a06000d076004440d005615140004410402c000c506d0051540c140f1044030030025a02c242c840c000c5d50180710502075012400d182e03004007034003400d08854140c00007a4180c60808550000c1082c40e0011595413150301c2a0340040604120880d0f003030011000d4640301c0045405240306050302100401181850f015814050011811500141e40c4511145864040c41d00d00c080c0c40e040010f07440b1031800001d0080c144 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 180887895 1250 180886645 180886679
    0x9020406061b120509060c03030a060b03010503031b0f0708030415230c0109080d0603020f060f0306010c0606030204140103060b0904120f0309060c0207080d0302090a06030b030a0f0c 80
    0x7092480350b80002e10780c1200d210b040d541000b0100384548124415990046003a107100750030040080f5540c10700001c10700d0b100d4002b0b48520085038100340c0b0204002005400f641d0695102a000714103003d4141c500302c0841c44641c14100880c0141100d40c02448824071010b17000d8506200110760b21450400300301c41c0013910404c082d0822580d6000f01a1421000701c40080c90220070b00e089450307880e00340816006101d140310041c003c1400084800021340ca54000d030303088a0003100d0306003140c06007009002c1030384211084140040000c04c0082c0c015805051002801c50155000080c1e007a2250701040c00c0f102c100c1c50140441d407940300100100000c50040a203040e2064030b0a80c89030501d503407900004007560001800f4030041c0400304e64001d03c240d1103045000d80141e0140901004684041e4031044036010f04482405a4000c034520369019008454450b2006017074000c400e827400308118020301d00702e80010b0b81401040344040202d856005d0100205000301c5590f07061501d80904403c040da018 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 180889145 1250 180887895 180887897
    0x9090504030e0d030e04060306050117010b0310050c0d0e07050f010c02150f0c010f0209010206101202090703020408030c07080c0a060c200a030501020a0f0903050a031d0d05010902040606 82
    0x88410440080d6000190380c074240819250404500001d2400307403903401c1e20703a950300d0301305280080010900005811a80c125403461a00e00351707448024a5580c00d17503030302100003078141e44400500d4101041a60105074404140880e45041091165600058400c550072222065101d41c0702031005d032501c8014104080405d08006441410581c0401c241e001408030001c042a4080782500c3c100c80280704070780030011004000c007c42d03035035a44801c1c025000021080d0061194000103a4507030184286c65060b5481d805001a407598a07900f0010000402050071003010303000e00c80010707560400c1001c0e12844681ca800b4081d22404c04092501d4140100e500320b12a1020410400113946c000e41c0c001c54594001c80302d5000081f4030720710209064100e08845401c03811383c407000001e204065001e441380c90200ea075900044c03200342000311124100b6010250040c0c210111120000c2d0088207104004011604520b840d51030000002d4075000341140b0503242039459080400441c60244100b1000d440d02d = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 180890395 1250 180889145 180889151
    0x503012310030204080d09240207150c1a01080303040f020415030f14030a1b050c03070605030709050a03031715151e0c0a03050c0a080301090b040f052806081501060909 74
    0x60190040751a503a840023a400b00c1110205c0807660b503100b4845040034281c40c06009014201d408801442c204540c0d0040c1c442c4c5107220f00400e003031101c40c180700d4102c907007101c0210304545a549902d10802d0044e10b00b05d1b03000d552600c070f4403c002c02d00200c2070010b40c09800120426000303800c04482e0304e00d078440d80207056002084501091a0024803000f944006c001484004065614246141c05d44007000d00341c2c503210f001000180141c0c480001c5108200e070340e50b510601e070f656500380302008081d8000240440c800c02c4d1400182e44034035028660204000d00000440305000c004580f407c1c03c080e1100020020010b800c000030403e40003003440d40c045005800f46010009a403094440b460640020300704080010170b2403508804100e100c0701c10790428000d664a59403035040c0ba006241e0210506c0c0903505203010a10009031502c5018401c807480f074031441401c0d810312a111202510400c40541550740c44a01045c2c075101000441342c0c1d00030766024130f03405505111000c0c041c0d100d603500c10802241 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 180891645 1250 180890395 180890399
    0x40c0305040c1e0302030102040e1f05060d090f02090702060601030c0512011e030803091f09020315090f06150906030703030e04020f0c03031608060f010503012310030204080d09 78
    0x82c1c1445602141d45540341048910307107a804003450303000c8030360019505600206020030170680c0c404c1c3d654094642c00e041001560f00440c04042c01490510079240c0c449002e100d10207560b40c554102c0016544101002c0c000294140d0010b46200010783d242c900603401802040f0484d60980f0034078505200c0381c145642001c00721403281a00004c14061001d41c0388001c0400c0e4108001901c2d08400341d644005000d480e4070700f080d50b4556940c900d0500c0a900c108414070311240104071303c280d042413500600942411260700c0f000c03441c1c2483c05061300c025403252304480394007010305001d41c40c029400e40500071085044101007014101000d0011440398008400c10400079410503598000400c09030390258942c80282505001d45c005c03600d510707e07039000003c10441e0b034190080d0060b21201090b100c8201d192114000c0c0700da220140840c00340030810400c014040c0324442075134012807280811010703900c044110003180d08840018003c00110307030003080a00204a003400041c403c00d00342d03d041c28a184c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 180892895 1250 180891645 180891653
    0x10b090d150b0307080f0c0a03050c04110c1009021915120b120d0906030b0a05040e01020c01020703051903110306041d0303190609090c03021302090a14040c030504 72
    0x414540c50040c00c001a41400101420316078100307541e20700009040d9000a03582e982e950f501c030b07030308010721200d280507148642c8000c2c44c11888030419240c02000500c1021008414000101707000c04107130006050901025040c1c007410480d0030071b4801c20103404100c2d041c0d544184444104100a49141110103544c103000c0a43c2640b01040d12910610700059404030903040e000c01003481d108502e8021260500c5084800000100030b510240c8030340d15840120780e1540218201d030074070303c0481d0b400340c9002c104104910f001d40015200c500c5000c001858a144000380601f242d0050800300d012440102e95964820031080b1181440c8045003014441c0320801c900d0803000344801000c561140c1c1d0344004044449100025007209040c5100c1148e84c2e0b41490f50000c94901c8070300c07003060f0f812030a00c08085500302960048a2907198403041c0700b5207013403d59080015502c0b44102643c4005d07400d00c00100e0329a107012424009040c41454101108122003c1c001580c00601a0034181400c05081c08002 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 180894145 1250 180892895 180892909
    0x706180b09010f090909200301050907260d021f0501051c050c031f06080a0803010303050304050f06010303180e07090b0a05040b030f06040b030d1e270905010b09 71
    0x94507007441c0985085103003140c1501e0300400d5801c400e4841e483d1403074000c200252840000c040d624005d156402400301402058281e55088815002c190040c0004000d002c0404142c0c180c0151141d205a107400c1c2500700662904001d001a540140d00c80103002000341c1303460280c00a02c414141e8180615070418001c00c551542d10200c0030b841101e141c0f0480b041c40b6082c03188403400b00c40182a125034107603002401e048580c041c0e006e4100d5900c0e0a00020b04a400010f1980252341d10800301c6080d0381ca151400e840035003000300256003d0040d1688007015103000e0040502851081d16100a4103a8040440740100d0a980203450103400d00001e000c1602d410024074400c80b84074181842da2466a51000c460718082c1d41c0c42406042d00c080140150403000141d4a031041c6800c0e0303020030003c21130358101559506844010317004030b5004510448501003590403a86030720101c0c1050340056141003807000c0303800646003200c100c10020110600201401d4003e050041044104240c10a240d00d8009214 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 180895395 1250 180894145 180894157
    0x9130e1615021504020a1710150303020c06090a050d051501090515040f18060e10050106050d0203091203090607020606010819090f0204020f1902010c05160201090503030c0706180b 79
    0xb25840303090014045690f15400c80028001059001800048510440799201460340c001c24a26080c060400048003072700051000300d035015801042014108414880d56a015031100c2e80c211079441c2c7d020440380c07510100c80884030321400040c03500d280000c0e01c08170741c0541130304608105824081840442880e042032000c1c2c51104481c0004c0c0c42d00450409002030000311103003040d4200c3c0c4554141401250f5001c02403030352400d419138004002e429250b608482e403d000790350104200340085809080280c0c00341d41d000d000da8049640403034114805901c10f4004075441612a40040104040c2d99814001c0a4009400b804d1411044c2410b11103264443d400c20745c41c510b4155240f01c46418001440710004003560054411560388550710303417060312a44228400440b0150006a28081c28414450900c2c05480c990710141001c03e400880c00b20040c3c045010b9041180010010820750b03400d100030020504c1d504010400945007280190003000d5040448400b41422541000003802c0901182e0f0 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 180896645 1250 180895395 180895423
    0x106030b0a05150d09050d230702150705010905010603140c010c03050409150e04081209070303081302040207060f0c0f0c0510020f0408100902010e0405060d020609130e161502 77
    0x2441d1580e04a0754001441445c0016010380b045080084605070030030b007078900304054104d105040100700b00034011917100301c0c5070080d0070410000030000189a081c024246d194400c074000b050348031045d113400382558100d8205550101d072841c2070802d40765040080d0980000207003007428500b081603c02920034040e501c030384080c035912103540680c07985050b014500039040c580440445810f1606001e101604604213020144021034049100700d080001d001d81241c0d40f50b541c0b110140d450480000e6072178860324040760400e40a110900c0040c010740180c4030307003100310100042d4140107000024005003007189100c0c184560100000042117010034010464840d40a02503526142d40e145201c2512071039000c10780764041e5280e83e02c06981180c1107641501e000f660344242c41c051090400c0111340301680c1403584103c6d41c1c000407006061100c050b160320030b40140103413100242806c00b10255007030f0204500003500300b001c6259080360b1021400e00a042100c015030344545059201a5942524003c401 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 180897895 1250 180896645 180896647
    0x1a06090f25020124080106080712030c0f06020318060105010908060406020c0a05070b070b01051f27031a09011404030305040c0b19141e0f0408010908030106030b0a0515 74
    0x407050034000d401a06242000d00c1d01c1010014080d01c0b012182d11a03401000425424001c00240740480010b116040d500c0e03603617028051a0165400380d4507000d0000040304e4001d000180c0c400461000e00c0030318400d15440314407034040d581c01c0c5105400d200d416040740c0e0511405401c00c0c003e110300020640e6226500040059490b850030101e50f10701014540c008220303100e010000300d002044580078010702d91190052468a980f103004002044076080b00842e04401508811402d00c1d110b048586a80060110030f0f60070010821800075426940c0c1c1c00070748070b1030030b071052000c0a0200c0c0590180d01c1080d030b1b0f008016215114620700b01c03500d00a4005020582c564011405002924110600a050003440d46a8840080070518014486080d08074003140c804408d41100d411503804482100c1401040c2c12080a5002d1b064102500010562034100d07000380004120b80c40c1c24400c10131154007410015840c1d601d0031500400761014510540e008a400050030081a114200c2c0008405640a261 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 180899145 1250 180897895 180897961
    0x140d09120204020904020a050d050a060506070201030c031e060e150108010509180102030708040506090705150a03020c01020406051306030605090604020c010b100806031e060703050c071a06090f 85
    0xb6019009040e5800d030b01c14400940c0e00d4000d0b41050041c1004044003409101c15500c0c04004400c0f5401e51041a1300200d04115400041d032280d808144158620b0500140c2d010660380c41001c0815066030004080d540c1d40018440d04144030303183c036800508034040c0c4440e000510300007003403500180315444c0540c0c000404909241d400000e440342d00034a42c8000c54a038501543c00030003180b41030307406560764001c4c2e01c0403940d5140d0115100741074440c082c2034500c20310b0010100062075800b4080300c00805509000710130b010002800200001e14142d1784013078490440320100d910305401381e0b00c15801e15107051001c10564941000b8030307500100480300107071991100d61046000d440a1003d290b4003038006081c0400c01c0703421000060240e2401da0850b88850091081d00c1d00081744004581c0c02d503840080003603071881c426001290300044a0b407005081060705e6842e0504000c41c482d04442a100c42c0c01000303c1802c080510541c40108100d0000107414040f44a410040841d00c0f803070006501c0c4165 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 180900395 1250 180899145 180899149
    0x1a070e2812080d02030c0316080402012f0709140906100501082806030303050106020109030801030b04051507020607020606060f0307230a0306030b06010f14030703090b090604140d091202 82
    0x183d50074902040e40c159607030300e00b450203100c40e03078411206490035024221048141f030b4410b9131007030720031035040c0c441c03031130315450541c183c0866141240c81200089401843d44805481840800020710b03415002041c3c1440140b01c1d61800720b80141f5000b1281c1c04803080048481582d10810125a003c2c01c144009460307000d0355003203080700c1500b920b060b00300b001c41040514049a110b0402c4a001e03036010000390340c90700d404070f00781e841215001e400140c1d2400180302280c0744052180c0c2041c8200300315038000c60783d600410509213088800b100542c01031001c100120b40c0511845a1017102225014a03107188000301c80454003019101c1810031a021062140f040b00389600d58075800c15180100c0c0c1c641e000c400004028007040c2c00100e0301c00340031101189065000340c21184400000e40c894120f5400096052402030300010300301400c250702c508071036000c0351084081c10b0188101c03401030103052406080000d04200e075450600c61a42c80b803642c841a6517440382e070020130340d0454000081e1009040c00 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 180901645 1250 180900395 180900397
    0x40c021507050705160311010e060319020f2107020c0603060603010603200c010c0212031b0a0c060513051e03160303020403050303150a080d020606010c1a070e281208 73
    0x21700346940224200c808000d10103404601f00b9450001d0b03958116240d05034090215a000507100f100e41810340e20910350005405030060300340da88800755020300301a401400c0004000340b0b00440d01803130840c41c06000056506125440e2414402d964152a40c03c100020840600c030520a400826a603682c5401030016488140c0303a400c101040381948480c50600f12074001c0c000b9000050161280c009889000318680099130b00c0345d00d008800c06180030f40c81d9084a116449181039a00300005419450300003002e82c0f045902400e0a84680e041d08405464014a444003000d500b2a002403d44005520203c000040390744250103100310190300d90207443c050b03019003d1500011704c07601000c0100070700610400d03c4444900d800712075050701603a42e420715548541030451110016004200040c449500807010a012144155842c0868220091200002450542d241000501400744040f0b180c500625400b025084c0009140c840365214110810304424503c500c855a640010036007007409a004 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 180902895 1250 180901645 180901663
    0xd0b010309050a061a1507110a180207110603090a0611040f0e101a030c0310030b041a0a06060c0b060d05030f0a1701050906040911040614040c021507050705 69
    0x8441e40d0041e01c3c03038000b0141000800d401d480c01c0b40710030410914940700e086c10110113969148249442459111a55a04014051300380c01400710788002a808840030b0b80801c9042d50a540103842d2000e07441c1c000d011703c14411156104402c00e1052144280c40032030100e030101c1c1d01100020b040d0f072101b803050003a80503da00c90766203007051a200203500d800502c6918031070b000c4604000c1c0c12075200d00100011442c40107034a000d070b80c0240002441015024001d50700280c0c9180961005541c03980c4001800a00f11021624080703078040301e0a151740d1443c800b0303400ca2000c1a040c00b005003006402031142e00480e2018001c41d4403170001c6800c1e6100c00c180a07100300e030401c095036581c07a8120000b0181d136100c640b807180050500c0202040d484103291015050741c60003407001ca2280c951404000c00360171710000030354608842c0100c1e0f81c4160745500c50040200380a80d403070301121586004000c129221108401c00b5034000d80ca440f403507050100c1515501100d10308049403240703450300b04540707001210 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 180904145 1250 180902895 180902903
    0xb0f0d0501062106060e04050304170c28051f0c0f08040303090611030f04090507020c10020a030923010f021005010605312904030b011703040501050d0b010309 70
    0x25803080f10060b00159007140b8114041c0d50b05024481e9221007104d0120070448000d401d982052000380002d0110300c4410080030a076000305c9000500c82c80001d00f0000031002880a15005800d0040c415844080e40e800105401c8031142140500c0304090205d061084101c0b60400040742c08110802c141c0c0041102881c0e004001203860b103880785000380000034180a10b401082510050b52407040c1c001044403030084400031441e0600c0d142142220150102802c00010350040d04100b10031602e0b5084010140d0b10300e17500812004c03800b03050251064a454014804031549a480a015191881400c0100110a190450703d0f5941c0117000c908005288451070341c1d82c0c2c2001d000180c15a400f01c0501f5080468609001c1040001d007211101c4015030075910720714039680c0d14100000c1d072010800542d00020880100d5000071030455840c0554045d4008554030011440188802644464a2800c541213200250301e803e0602e00081c1090080d108456441500d032404c0040d00c0e40f29401c0f602501d940 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 180905395 1250 180904145 180904169
    0x1207080d05090601171207110310110901030c03181209030501050c04090f0b03060f060a0b0c0d0311071a0a09050109110108070e06030f041a04060b01020705040b0f0d050106 76
    0x210205a2224021700c110224011402c201d0110044040341202d00b886559003a01e190400c00d0750350005442d490700c0b505a0501542c80b80ca107202c2e1036030040c5074080a1480341a5a9080000000b40c1250344581e0440c007010310b000003030700005110030151402c064024010001d69042c41c1b07000c0300e42030840d820050295080030700303001c4190130007800b82054405410050000801e1101c040080b035081040c1c003a8035611070000303d8014500804c403d130f00410040c14192105d502d0361102c000c0d907030000b80361021355400235400c0c120b11640752254415004207500424070305203507a11038284100407104102841e951910200b6a1804641c0c00f030721200e42c1c400700034020500e00e800c00130050205030140c0303800304103490009032800344195080e0b074590341d00400c542d055484100b5071205c1018000c0044601d0044140b81c404118604440301d849a4032646010498050b014002800c000312984000d010705c0c04d01c0e0151680d6a100030780483e0000d0192021900c1507128203100307015004d60762000000040c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 180906645 1250 180905395 180905401
    0x1140a050604080604030e01051903110c0a050f070e100e0a140a02090901050609030a0b0603010e0703140d0302120411040908041e05030a0f02090a060e01090207050c030f1207080d05 80
    0x3c0850224481c900948400350780103000c0006640d40c1c45440c60304075216298090846480380a131740001c44162a0070740e0582041d07004007130186407000b0302105448503400300c1142808043c080041c00003402d0040c40033141400d09030b01d4a81007007021302030465074854540015900309480d9000c8521280384056000950406d8a140002507009252503030140e25414008102401c01c0021240600ea000d401005044980e8691080c40403000d44826415501e030b01001186030010400702c40650301414002c20034880c1500302070314000c5940d40c0300d01071600501c600048042100c4d00c150384031350007107045440f5030745040004005141c0700b030b802020000041070103e9200b0b0348a014566950392006807400303071511003040644d54000010014000d0000041c65001400d00f100844d41000c9007100100c0c0c050740300e031028058480709800403031a842c1d002c1016002d0081c108606a0a00c000794040c01407400040e14103601c0d06070304041600c030385a0009020b02008402401c031000a9a00c10301001641 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 180907895 1250 180906645 180906659
    0x20f0a0605150d080409021e030c19020a0c030b25020705030c0904021e151c06120317090f071206060e01120b100513060312050405060301140a050604 66
    0x401c1c1a500340600b881d160400c0180e40c14500300d2101d01c80d401001d0682880d18054038500a9030010401106008401c0010410b55040c407020f940141211100b2039100c90b0f11000b13625904010845172401c652004141902291a90f44100103480c3c000c4480b0340142d4400c45400d000600d05c181110080074190360b9000c4055003c10408241c5408030140c1d0503042d600d000b040745040c7c2c180c8003e50f101101c9518200300c00340620303040309240b1000d009042000564100920701c1e4100c103004100103852051543e11071821446000702400d600c915000300c41d840c940b0f000302100c4091180251503031550b404a108882c04211414410029000300c42c0c1450b01c44652400500da58a07088500034208100421030503c0d42440394141d0f82459103c04071605603441d5492880700180403042502c101883c081129281d200c100c2c0c41d4a1070314240440c1c080e20f0f40c605000b40c41c03104401c3c40c0c10840140014089a5070380c1c0d04480c11245050000c00010103a940000c0c44481e003540607552208002a000400e8 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 180909145 1250 180907895 180907901
    0xc1a0f0a0806030712080306060a09030b090709060e01080d080702190f0b09010605100309110a0603090b0f160809070b07030f09080a23120313150e1c020f0a06 70
    0x203030070141c054507401507443c1014401c05d46001d900422400040c80010000c2c1032940140034141c1052802e0740710075a2380c0c0c40d42d249000e000c0c2c03401985a04503540078018031589000f4040244816204002258544224103464a1300002c4010404c9044404503422034030800054100050072905039034080e20528000b0203041c4d01110444000e05040d00103a2070060603c5903900b143d6010f00050505e00c0d0020044000f480580c1d401c6900d000004070f005850b40350901c000010b4002c0b5180002c8400c011300b031020255400400741d12040c0c99010400880701c02140051802c1e4141e030811a41c0c0d512000e5140e070612440ea040070480600209030b071000d042d0701c60756001040c03030319490b8406000d0f280c4803015280c4081110181c080005004000290005841040d05484410094402c05848600781c41030359401038449029580801e528502448100c480b0418a80ea07228020081e42c0c80250360039031946068844900c01403200c5d10440d1106000303102c013500c8080d00000742c07111640186094002 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 180910395 1250 180909145 180909151
    0x150905010e010b0901030f060f0c0906030f0e1209031002030f070801080c0a0b0705010213060302040f0b090a03020d02010c080a05030f07020a05070b0a020c0d081e070c1a0f0a08 78
    0x206609200c0c8a14501c03a040c41a2141d02c14090502ca00076825a21445000701c0490b408880c003d982d40065078135540c00c1e2041d44840a402d0355100c40040c81c00754001c0131303540c0e2a58980d4038145415692240c20384001060841e925940346400c2d02c64540c18002410200d40d11a926070340c1e40008204042802050709840c4141c1d00340c0ca42440503600d03100e0384d503503a41c000c0e0079848c0c10101c4940c0620400d8100f40140540d030344610000751500000d40c00b0300801460a0f03121070042070b00490280200c410927021580603101d0542e81c10304280581001407883d482c50710010b4000c0002464140a591066a403109000d0700103500310707614912200c00400300d80c0122500d501042601c0c0104418520206920054907002001041e09a0800d2015011030f0300c400240e030150310840200189a444040084134164021842a500c0e01261102d821000b5126a82c0f820481010440300d0006090704103000d0544d0f40140481e0307950400040c84104501c1160481c1c00c5050300401c00304c0c0c110740c0c084800b501c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 180911645 1250 180910395 180910403
    0x901060317040b0d0b1f02070e0711060c0901030212040c03050606041823070b0309010e03030402010f030209180906070e220905240f070906140a0c1509 67
    0x18100c520a220780d581c01207005030500b0031000c01018104040d5600519203502c401096824404030100c8a4262a550400c2201c00340e0000c140c1008102e01541340c3d00d602c11824100a010340319410b4809484a000404031003030a040890041807903407003541a540102d2203014803644500341350516800d400402d1200315903e01c1140c001800e21300745406407412031404030f0041c0340802a0b44d9a080d5240300c004c20006404c840013204119101003c01c40b80c8000c014019a20340d40c1d08000a0082c02d681800030000000d41c420400d110050340d100603a42e1072242180342c0142c03551041000030340070328182003107001c00341907540900942c1d00000c5429400360034943c0311409194510020310200100380e0510b02069005c584500008221940203070680714801c00584654201c0785407030403038030a400f0b4101800e9010f54420841c0c4c00f03640480c1a03401032054104480d40d2450440d00600d803040d1100a60521500411000030b075034080d100159190350300410040034010854240c000400d0301c1c800c151 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 180912895 1250 180911645 180911663
    0x120906021b0f0a0c140d0209010b070201091a16030306080717010f1a0409081b070515090907031a0a0605130b090f100c050105090c010905090f060415080609010603 72
    0x41500880052035030081c9510814540141385007605d00a0030441c6013010503048000c880c2c2000050751001000c50180c004044580d880d007046000040c00724130103070082d81d8070202100d900c42001c4000d00c243c40d5098480c046d008100d01180c90304070060255580400036511580c000444c01d84928400b111049100304020026910080e55840035101840c601c241048138401802000c0c0c1090b070040d41c410360042c40301c41d00e003115224800c51100e4401130382482c150800c04c8240301da49041c0420040d40101c11103064107081d0084006000e03403074042c0c110710a0603541c01030500c0200c498a042e00644d00e0040c603411404d036541344040d21030382c840407241103d8010000302041600c048002d66440030005408180301101400c05d002916111880382c03418800154044000102c09000b83c80c4245810005061400240000502102aa46c110500c514280c00400548280c210021944400b00f00e0b40402d442140c48010700098080d07400000e018060b43e410094031450541000c2c040340d10540c955 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 180914145 1250 180912895 180912913
    0x2a0904151229190b0a0e0f0412142203021011060709030f080d02130312080604050c030a0b061b16050a030b010303140904050915090f0c01120906021b 66
    0x180440342c1003200c0c00404a250110007040324181584000c0b0412005844168525101da00c0c41c088039000f02e9a042213000c20f841000b003000480104482001083c2c1420210366070690213001107801100a400890303178845c1c0003201c05468402c0b0440086802070b1414080f9180c15000404021460f41c8030312040c400d400100381c11510070420703202241d81204a09604461654542ca200c0d40010007214aa64003070001400000b44102140021403152030729030b20200c0208000340640600405043c81145050200607110204408480e031080b12300b400062020060400a0960f0040c104010119400c5c01c0306131105201c0050381207000c460650280304440c3d41c40c8200300b005aa140801004118a6001013000030f001d2082c0454084030203040d54102880000440d04558048540c403800d5880200c940d141b80107648110341e00030540c880944031230401c0325a601d54600c01c800d4103038104840c506104841c41c0040c0d01c8503000c02d51040081d5a2610141040000d01d1a01c080c00503107802080340e5 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 180915395 1250 180914145 180914213
    0x3070203010e120f0f2802060a060e0c09120d0e0406150c0318050301020d0f0b012309030f010f0c08070915031d060705032a09041512 59
    0x4180c42c019041030b0003629080c483c1144c12001d41150426000000c41800641e00454240f01c1c0111038846031480856001c61028000b850f140d000762246030b04a2800005200c8401c200000aa11007000c00144e6524400d80010400094030360704808400d0044018081c85554000380f500c80c12072040f03406101041d2030700b102c4c0b1905d1001d42c031000041040319682400190186412444411842818035240e50f9518082400ea0344021094040caa5503215000c40c2d140d0f5a11896080800c00e00c1c0c803480b455120041c515000c8520b400c035941c101008034505045603010801541c035106503030000d01a03004080030150150250f12010004039182200150a40d8480d1061008694002c5900700e2031904804054004001f1801441c540d40c29a08000700105030812160340145281d031303981903413032426421900ba0f0b0101a00c4040c607485420801e003880704401029218280422903002450500c10004114440c09542c001104004010110f1061141d8490841880300110040c000d2400000503 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 180916645 1250 180915395 180915403
    0x503010e011103070f261006030207031211090414011a120f100905040309091109030606040f020702030703050304030b0f0402091b0c030d0f0e0f0604150204030b070203070203010e 79
    0x1c0d9045103000b05000248000303200d001e4900c0250400e0504841403104001c0742c6600d50b010700c4944880012210603c170342001c0100c0d0b02c0c030041406190460810f80c00b0380e8014030b100404500c00f4032040d180c0c401114511010400c90780c425030000c0040007003080200340300840c00800d00c1101030400c60420415a20b0005a08950b8503404218101159595050b0481203403400900b40303851140040c000070400c00014440c13280902d000e0f032a00400b143c90803852409980514140400350101805000541e0b00c001072802c0d0031501c100c502007055400340041d06c00901803100e01940c14840c00c0d40000030f04c4408030003001541c0c0a6264803080e50b0f01c0e4100e0480c40c900c00d8070f000350007503103400c00220201c1e0040500340b4503882d01001103142042440c0c80d189181c00c201010035807140d50b00c0c1244030a0741d5034801e851018101e00041d01c520fa0a2415207030321f8030001040940118954070081098030356550480f8040d50388190b0b2881107040031030000b59280c118030000c074041d610700380e440380d4040b030001 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 180917895 1250 180916645 180916661
    0x3031b0e190303080a0c0e0409150c090f0902091314011a0301031505090a0602030a060503060603010e060601140d11040e0a110901032705030705060109060608040f0f051005010503010e01 82
    0x1884201301c64980b044184020481c041d4030004001b151607400100c0e544a015800035180240ca04005280400781104100c440d412403505c113001c40301908200301644426203000325500300c90010b0311481d04c18081149501c03000e06203091245854070300d064a40002090700d060703c01c107130304151510286c910704046a200a00016000c0d6900300000965122541c12143d8071411400c19606092041c0c0d588505a81090301d0071500b05494450500c200d042c100901c640c021401c130000e0003400601c2d94810b41342d4038064401410006110348005038080c65100f100c010100c90001008014240c1c05506e625030000c0c081d40701c0402c2204041241c24046d8050b00450342d0b42c0001c22850002003500550040c0341c43c0c041c5a40c40301851040880c40c0043c00d0340826041d000c0c0e0046e507600c40300c510748142840030580080e080545004814440158003500007640a51320060625846004d818441004034210a004080f4825003400030124030f40b90300014103e07001070300207004c0800002416800d80c5c1144c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 180919145 1250 180917895 180917897
    0x2060c03090a021c1a061c0f120908030304050c09070f09060e0a050303070c03050111070c0506030618070905010207060f0212090406051302070317010501021903031b0e190303 77
    0x2030003091000d468001036109111071803c40d00b85011100c0c3d541d1074080060000d5801217603694104201d40750074a010100081c4d2444c2d200c2851052080c3d4421400d0801001c000e4900040c00b242c011186010f1109400601587c0702181d0b180d1410b464025a0f40e105540100d010303509040200d05500d0103400740f10b00e41a003e440701180c030390078150115010a00004807a610081100c400502601d0134001031543c0b80c00340c00d400071601c2c00c500b411402e40c0c5003c592610554810020703540840e4600a0880584400b110140e03a030740c444000081c03540c03118039841a5600740710000c2c00b200030b4100880c0b004590007a000e50742c05590383d0006482d03045002e0300d61001760304007034242c00100072018001d01d00303c1d1009000203021621880440c0c00c1a82d60100c0c800c00550028100d8181a000b256803110041300b5841c028080d030500d80002c2d140c07083c3c0c1c01d0788541c48900c46841001c040c042d130029001d000b41c00e6074a5000f0145440002d020000c01030f6020b0140f41c11000c104100007003002000305030303601 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 180920395 1250 180919145 180919153
    0x90620030a0f02040902070803010e07050702030d080405120301120b060103020310050f04020c0303010f031b05011403040501060512031c0b0906060705030702301c050c011e02070302060c0309 84
    0x240348600d40107014508000c48142c0e50130040800c55000900c00b4000ca00e010314003098485d818800411402da10242c1668140304060128800594001410345100d04003403404006030307217551500c1d41c90031100318003450919401200220307803003078003142d440101805500800d010391190300040d800c07031201740d44008800811102c18003030f5043c41803283d40340c0300c2c002c3c1005107003010400e541410751b0001c5e000341c000180c19040802c240040035030710489000f0081c400290003494200040c1251922083c00c242c5a000440001d003407101c294808030041101400203410f02e03012000603512540300100d0948103900381441104071041d0303449000803c88002e403422078941c48000820256400100701100c41d880700304400c44c01a110722040742c1440c1c0740207070045a0a03542c0701d050503000055148030112a80309031001d55408d82801c030070f08503000d0703a410103540d2101034031501e902400141c4a100e4403121004070520710b04120754014540e050081c0d0996007140c503221011822440195094041d940c0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 180921645 1250 180920395 180920401
    0x1008070c0f02040212180c0d030806220203061c17070507090c0203070201030b010329061201140325060f090e040c06020706260a09051009062003 64
    0x10055800460460140d40c2a060030780255001400740d0380141c2d80d40d94000a401e051100d000d42d01e6904200305d040307180142005001030400b0072911b42404001604002080300400c0e115200d034143e051034842d070728442c020f42c1c107803105819021f94410f4510b14003444085034641d02a800700414004920743c4280341c0303035a03003041d00d0f901c440b15000700005031102c1c09803441c00600c900591003400c074401c0e8243c010f541c440806d80009000c0b103904d1841c0c14149410300c2d482405143c0107800c45074243e00100c0c014018900600c0119029010b100f603551007803020b800011440f0024000007044040c0200c01f0bc5240c01c00d0648420100d843e8510b002c0c144d0445c3c010213215a07401038441500003400e40c43c007011119030b200358041d220724040d80d00f503402c3e19411b0300a0201e50b5061202c400130b481c20b41003c3d407815992480b8880501ba4a5040c2c58a80c00c1b18000701e640303410550400b100c060f8010b03044a6441c80a01c00c2100205940b280845013580791034500301d000c1904030040d0100302c0111640c203007166 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 180922895 1250 180921645 180921647
    0x60302130b062d041706070503090c04050403050d0f020d110f0409020306030307020a140109090e0318040605270a05040b0a020c0f060c0c1905030712091214010b100807 74
    0xc0c90b0302c0e03c0703c0c4074425001e4551001c5075902c8007400003440e0121443c0842400740001c2e5040040191264042000800c1041030726480000d051261800503140000d0f0ba68441c11300b240c80340a440c0b00203002034142400b0413040c94032500a02100b91030b00c9010030200d403412018075a14401c584162599003400d0108000414036980516400708014099902c1c20b881035000942000e903030b0300840343c0003074018003480b41e41d6403240001000e40700d030390070402130300341882c440556901070a01c10010303000171001c0c4c0d08059103aa400040003801d01401c5020322544049110040c0d10a1210408034140d0502c00103840b14242c2c0a028007890300504400341076107442d401c10010794040f070b440c150b03140301361805102084010001caa1085ca1800319840c1c0b20303690090b645040180e10100507401c1c0014030400780200b000070003144c0485900282c541e03450505601c044c0e500c08a150700c0030b6031000e07031501e0307035018043c405824240c00310095000300500c082203010080f102964030161000030310f101340012002 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 180924145 1250 180922895 180922927
    0x90705031003080a0504090b0109030b13060905010c021c0903031403180609030316020f100507170112120c030816050d050412080603030c030f091302070501060302130b06 75
    0x308a640404072500d45a0b02c0e1480560b100c10720072030010b24001810011a40c003489035001c4280b0234a0101c80840c42e46e1150102d610003d03001d01060b10928a1031001c004040d4080a948c6034040700030312041c145c080c8065103a15100320340e02103c0480b840703030040740c520501001d81a203a00d5240d20007040040c400c0e0001d05c3e00b00400200900c90313040258181d45108010461003010b600300119034a1401010f0082100c40c1c8900241c00d540c0403010507504800040341440301300b011104006866a0b604004852640f2414013850214540f03500124940d000b003140580c40a01942c50141c06000356071003116482100c1d08003800082810300860429042132003001e40700003880c580742e81040707401e24940081718400d44041b51346001c0088512096a081000039a2025044028504003600006055141e1040d00300d008464040040e44003002d9541030040014400d20f500c04540b241c21a00c6c0c168024800307800300341d1003090f1000042d40c10b50b11301d000b04900c103240600140c2c1000203a408107000 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 180925395 1250 180924145 180924151
    0x230601210b0a0b160309140d0f0204020909070903021509060d0906020c0d03020301290d0507170405010f050903130b0331060c020c060307110a06020c010c09120209070503 75
    0x4441c009a0001407904244806460984a14512200504c0c828035010b41554500d44c48120410714503000000c240d82d50241035503c140e04010350070300c182950310000c0c000b441642c1456911000500522403002c1d88404940e00350303032003a01e4400d40c486082c00300740002c0c001e000001342c1c0329404120070f044c01d0050707810850784240724142c054103203004079150328200000100181d0010381d0120041281c3d44020300114059074181c42c0440f82c1d41c01c41b00300720f901e0344640b4a18054450309c64000c10340c1c1c00d21800007040d5240c86880080c100d4105860400d028201540715000d6483c01c1c0804180c11110200440d10103070750410f0801012440c02ea021071076a00010000c003c0c0c60144545007210002168403024003d0421941240b086801e19010301160030322100c0804561200c0130042d4692110000c40782c1004c29801c00c3c41e0ac44400c1d200881ca4034500f1440207001600100e0300d8546030405400110101c0c1d0f1a8403a0941a61140c0700c0100144582c0030103540010380d0804035456602500013150 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 180926645 1250 180925395 180925399
    0x501030b0610140301090c0318111903021503040317060a051e1908070909150902040905160602010b09090709020c0703080a080f0105090615030a0f230601210b 70
    0x10000c007600f4842c2100e90000d80c800d2500a454100000d801c540c944030343c1d415503240c854441c69005c81610f581c003110002032000e60066803a10214100390511008600c01580c1c01059600700002c15402410981c00a0b18110045540e040c681c00034200b0900540c1e200720070207090580c0e0140340c00100003207440e02000d51490710003245011585074890045001217060308000c41025640791941881c68106103502200c01140f8100301c880c0080e14605502d41921000040400c10481d54000640200034900c8010294400c420b00540e0364545400541c00b19200b035002004410809800e01041c01d10446011361903402c159800e010a03100d950207420401341103021100307100e8403581d90b0740807548003101d0200400e01c90003c01150130603222a15000d460155010a42c03401c0c803d0110b030b0a47c5400015040600021001070540701044c0e20070350111181078414080e24088512504180c0840030315600c2403401e080c0014019402942821044681181c20201004a00c45010010048111a16 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 180927895 1250 180926645 180926657
    0x816020a02040c03090b0f06010f140a0c03030e0613060c0e031e07030503040605030f0a09051e100609050603120f1204020a030f051e0d0f050d060521060603010501030b0610 76
    0x45c02103a4025032161040c50603203803404240c10201c00250032102d04940140401074001d450113401505401a03d110a10300d0800318070811440c5400d401805843c00a0780040c0718450030001103203034059881280c0c07805000b08100c081004041121481e003140c10306030700360b80b00500d150381c0110445240e044500728142610310708c031746a03130b591030442d401a80410f00084010081c442c6075003014a0203908000d80c4503081040358480d6807030941b181842070303400ca800c0384400120b009450041c032841465800b0400200410307911000c4080007004c0c00d4824500900c50a00c050091031042d008030b4001c0c220383c140701410700f07030f00c000c20000080d401481203810529000e0000001180136041000d80c62243c406040480e0181010f8042000380503141c40090f448800e5202060340c20074004c0c9203920103481c0096442a40c8a456800b41c001035101359005065244100d00a06121011401c1c0c0031485060b100242c4491042500340e6000b800060851400c0e080400c089150051112000d012107003040 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 180929145 1250 180927895 180927911
    0xa03030c06020d09030c0b0108060402010c0f0c091e050906060a0312050d0207142b050d0e0d0e01090e04172503030c020d03060308041a040b0c0d0816020a02040c03 72
    0x10f4141c0d615900c1c110042600d494048080007000040c45014000610080c0020300d4076800091a5500c0480c01a1507100e1150446061000310f0020705c001e081d5102050000b10364024040350320101082441000615001c00f03da110b07080401e1850048400800502456065403500c0519121010202062000070000180041790368000760541c82d009440700125200d43e0003140b0306210200c104548241c464404a80310710140c04130800c011003491904e180c40d140c0c00740000c070040c21007401d80075941c424560302e5110035600071080802d0480c281d17120340109590b1102c0c85680c000c1642e00500b18180d0922091000a03074201502c104180741450064958800c1e1314034007140344010055000030b0321210480001c6030108171100000c6000c3c68200022403954655466900030b501403c0000604522104150043e0b40155000b03011103d100e103035124200c105140e034502408c5119004101e040c03000070401c03401c8074801503110700c894010b0f01d074074071040d401c12008161450489042c10354507501 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 180930395 1250 180929145 180929167
    0xd1805060a23031005090f04080d0b031501091d030a1223040b130c1502070812030105010201050105010c023001020d020c010b03030a020d0e01020a15050a0f0b0a03030c0602 76
    0x103080d0b520a00d4000c0c1e0ba0b0303a080c42d0300552286007464101c03601502041c01440048418070010076401a00310380c1c41a201c000440d04140500040501a5414843e404001c501300340c0844080741280e00503078080004580c50088941c03400c02035501d4083c580c10038020801158090320400241515042d40041c40c1a6001320075841440c19400e003400703603204d54041100300810174103160340007001c0c581c00040780b8029075540c100404641c01030781c1c03c0c01d0510103c0b0020500800c042009000040181c545d50410030708808030380c1d0000d200b0a030066090000014055000307804d4103480b250003400b641541540040710b025000d1308051035062849079a008000c6210080c809007801c0595518050380d5100d460301f0844c02e44008030f8525210350400c0000d51225500007901034121030590410041203040c0c0b0740141c0c10803456070303c003500c038034034540301c0256003803981c1c0c0514030800c2d210f02d04100e41c51680d074000c0d00311000b00c02c03402c1e0840401c01050011a0003000d2419041c1d1050ba005072032301ea8900301e = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 180931645 1250 180930395 180930437
    0xc09060c010207111c0204022805030f10030b1f051504090609110415030e030409060e4002040603050a02130507080105090403030e07030b090d1805060a 67
    0x881000d6580490f0500c2000300065410429200494524411030001c40344901404150742c0c0c021b1243c1d0340002d000e15a00c00d40007400d100c0045948204044d1b012280c0c0240982c1d00454101032400c0e00e000003e400038441d452100d09998100403480103e968800c0d0f01075444c51040412407000c01507a200240303659440c920f000900d1880700886854616000c414003d81d44c1c5600540c0c45c540c03d004500d0030307094000d406d135400c0700c420101ca2840c240c404201038008010039003107400c050000007008606020f240d003250702113410641c030b55100d83d80d403582204441c203203608200c65080001c101c20800722102900c000d044600c03000b51726440d4816540001c08451559108480c650020350702642940f820111404038440581402e100c1490540b80042150005000c0c1d644169503c001150626101e923000841c4041007104450a090f00c078280386103606030482d0311441e144946a103601140e40b20f62100f5004c08003c036480401541000104129900039800031030400100e44818449030b07400d80 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 180932895 1250 180931645 180931657
    0x9171c050a0902091914040f0807030c080d021b0f150612070816060f1211090d050705281205012c120403030c0b04020f0a03031d0103060503030703080c0906 69
    0x5d030485a42c0141e48040d100703482c103003100082000c042e01c0c1004003041210003d42c40503944545401d565489600c0e05407402e031007560028200341c1e008200c81322503031520b900604c3e02400e9170341c16115000b200c186c0b8996500780c500111107240c2180036003c1e40e080c2c1070601a030300044018000c802d8000c54911480c508006070f07201c032001d580440c28000f60400601100c0340a0046843e05250080c40f003403010703040480e21402141e901c0e9407034510024030550781d030030f443e1141d400400c0d01c0d00d020100d00340160369405a0056500c1217880500841c0d981404040448a000310001d00c0c0702c00f9480d0a001d80c401c44041c440603030700d6542301c1e18a1040d000c0d0011540007040c20290030700d40c000300c0703041d441480c02c903420440122440c42004180080381d044443e03041d40c59409403100c45c585e5034070710120701030030b441c210a030360080c00c1d25001100309900213145c5248002503541d0481072000c401c004400396029446141d425800c10000382010034030407003000341c0c401c02401c0201c0ca03000503d000708000354400 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 180934145 1250 180932895 180932911
    0x318030302030402040b0117010e13121106060f031009020312220603020a09050d050a02030d0906080a020405061603020708060c0d0e0105010510050a18060309171c050a090209 77
    0x100f0042107182034419600007144c02c1c42c2c00c8080c0b4a94003551707020203030107008280c442e081901c005081c1807080b51681c000c031030340005001441ca01c1004040c0c0680105030b102400c038040d1000280c0c40b0b050180c41102514402030041802020540180004000500090340c06000d80c94018020030f03083c4c40100300b0b842001824802290003600b82e580110b00e9500401c040500400480d124140d000d000d07d029500112044c2e165001a0b0cc0d182d803070856071010003509400358890b0546025000049001240da49071a804460750ba070050b02ca089100314000c485e4070030001d201d4001e5080c600d06c403600040d4401d004480006844254040c603112007201c24868440000035040a244020301440000d010400001d00140d410940020000b5070001070322010410045902c4000074440c120030780c40c052807110005d410540b25240100600480d4a0988481d0301008140107614031210443d02554078180885a40b90301010740e0502505024048150b05038440e0030560140e40d0700c0120074025001 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 180935251 1106 180934145 180934147
    0x30201121a1e0405010803030604060504061a03180f033c09061209010b040b0d03050f070c031a100f050a0b1e0a020c01030b0405061f0318030302 64
    0x5014040760303c41e0a00c000007440d03050100007540186c8050760180a0151507a00340020f480c1c440c80365040448035050310281c080694009590412001c90301e840c0140b040e403000b20300d448502c801480090b00005185582548455521034081040602c005202940400650103111401030294103075280001e4041465403050200c0d01020000c2c030540440781000c00301a402030007105855070007589052052840c502d02188104e1350780364140d0b200c514040902106c83d119400005045906910000000c80001c043c1d892001c482c2501c0c113241b0500745007402c2c84418440c100d5200729a80d4401c0c060900c071a03164001258191080c140c0c0303c0e40c0c0c0ba900f580007080c20b00003003441d00003000000306001000300d9010075200c461400c240c0c1c003880b44075920b4042000701e680940306070f544074248200340c110440b8400e01c004c240d00018100000c0e0008021201c00711410490800c40001c3d174 = true := by decide +kernel

theorem cover : BRFrame.Cov 180755395 180935251 := by
  have h0 := BRFrame.cov_init 180755395
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180755395 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180755395 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180755395 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180755395 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180755395 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180755395 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180755395 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180755395 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180755395 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180755395 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180755395 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180755395 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180755395 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180755395 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180755395 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180755395 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180755395 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180755395 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180755395 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180755395 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180755395 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180755395 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180755395 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180755395 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180755395 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180755395 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180755395 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180755395 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180755395 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180755395 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180755395 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180755395 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180755395 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180755395 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180755395 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180755395 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180755395 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180755395 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180755395 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180755395 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180755395 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180755395 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180755395 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180755395 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180755395 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180755395 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180755395 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180755395 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180755395 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180755395 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180755395 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180755395 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180755395 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180755395 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180755395 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180755395 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180755395 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180755395 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180755395 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180755395 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180755395 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180755395 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180755395 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180755395 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180755395 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180755395 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180755395 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180755395 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180755395 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180755395 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180755395 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180755395 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180755395 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180755395 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180755395 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180755395 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180755395 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180755395 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180755395 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180755395 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180755395 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180755395 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180755395 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180755395 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180755395 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180755395 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180755395 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180755395 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180755395 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180755395 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180755395 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180755395 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180755395 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180755395 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180755395 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180755395 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180755395 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180755395 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180755395 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180755395 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180755395 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180755395 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180755395 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180755395 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180755395 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180755395 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180755395 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180755395 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180755395 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180755395 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180755395 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180755395 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180755395 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180755395 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180755395 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180755395 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180755395 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180755395 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180755395 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180755395 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180755395 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180755395 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180755395 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180755395 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180755395 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180755395 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180755395 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180755395 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180755395 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180755395 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180755395 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180755395 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180755395 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180755395 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180755395 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180755395 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180755395 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180755395 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180755395 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180755395 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180755395 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180755395 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180755395 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180755395 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 180755395 ≤ n) (h2 : n < 180935251) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
