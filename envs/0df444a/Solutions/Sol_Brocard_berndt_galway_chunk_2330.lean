-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2330
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:23:21.138746+00:00
-- url     : https://prove2.me/submissions/46f3d454-a510-4968-ab2b-75a02bcd2546

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 418884892 ≤ n < 419064748 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 418886142 1250 418884892 418884899
    0x4120506072606010c02031b1003020c0c01181a120c0306030601050f121e0d050f031306020d090b09010606030c08180106051008070206060901060c03030e1603060207020406 76
    0xb2a4994140040d041c80c450280d0201034481034068101e42100e01410560705511755940080c0c030b016110310341000b03c40041070300340c666400c04011043c1c5501503824294107106003140080c0e0764004014106040044e10882d03099030b41c0020a2482c081d08040700180b8600c00e1001c2c00c41841d620250040e02c19443d04c0c00018813403480502520300501004000c0e00c50b5910303120030800c40c00100c800240e84004c1c0030300100780504041100b032541186800d40e840089007046441820300689903601c0e01071010030058002880c41c4241100d03440b204140c03401d001032046081c110300034021640c024415514200000d030511402c840000c4c0b140d0800e01c001c0c001e003515402e0480a80301405484000f0030302c65800300c0c0142c51102c1041c0e004000300b500008000e9624000649580048000c6001240542d024003000d240c0c1403100030340c001d0043c6c40e9151507515114009040c5203404402500705692815022640b060600140c0c00b886c003c0d0a41c0100e1030348a0820000035482104101d00c914640342001 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 418887392 1250 418886142 418886147
    0x70f0e0604060303050a081b160b06030a020315130c080a050106150509010c0809061219050408041509091104090f0501030321020403060911010e12031e040b0412050607 74
    0x42d070603242d15a6816041c005500001d90ba09007000d85481d5600621011144030011041d01500c00741f0000003240000c0c81c42800e04251042004e400396009070440503880c1e003d84c80004440840c003401540700e800c40e5072180181104c0c0d21503e140201805050080005c00020000304c10612a000d10700820010b65a11445000c0049050907080821420302100e480ba40c003803c1c500300c000c3d001e00025450f05004000048080c1e003ca90218010345190b814004015101c100e60000401c80441c108250704041e203446006000ea4400e501e48d00108030040f01c0003601c43c044280003403601c0d40c000d1022065030b21940c41c2a030002d000310001203280c415108120b0302c1c6406038130304980d0142c48420a20701044600300c1d06031170303110340f10a82a03000c10001000610a10960600601481d0014090f54070304c1e000410035418114154404c00010700301084e0644040b00f01c81c91903040380d94016031a40000054150790080750310112105402141c00683d8407000549005918440e0041d81c0307681d038400c1005d = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 418888642 1250 418887392 418887401
    0x1603020f060f0610030212010e04170408100c020a05300f0d15030510090b13110420030a02040f0f180510120c030b070e030307120c05070f0e0604 64
    0x18005402a1070002c03c00c2ca040811034840e401040386400752a0071220f6107051000303107080e80300000b946032007410003050048000f01d547c40d116000c800c1c80e103043c1c5401c402a5a82d040300e90b84010a070340d5101c03213030341050003089841c0680e80d0040c2039174031000e87c9900002d450115200c410425500a00031640c080034410200c6c0c4010940450b25414035005400750b0004042c40c18100240d100146000b00200d041002449088a0100d01c040383c0c481e203c0c900405c0e4000060b00e5100c40d0301081000c60009440840351103c035071800d60300005c00341041d60741c04507003030300d0480c18405030b440001c10b00811082a80080054811958088505594404016211302e1092149a031460b40c6640720a008201c5a04030310f03040980b43c40c022440c1900c0c0c02d00810303100b041401c101c820803a03141e001c00400c50b150035256884805401c003040a04d42501c0030948901c101c49005000303240301d52004098a0044080740d4103282c22070112440e890305c80501580181150203010410600000000c1c4680751a008 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 418889892 1250 418888642 418888651
    0x501020d17040803100b0d020306130b0919181103070509010b030a0509010f0c0216090203100311041404030c1403090a0b0a120e01020a03111905071401021603020f06 73
    0x1d1019441e40c0c2c9031104031141e000500344401010301004005250226040030302800071000e0001a96401c0c90000c004140c0f04440e08036103010f040070810100c0e5544d900a1a501c040d0342d49504147c02c10701c0b401da0004201060f0280324a103c5c00c000441886100103400b404260146d00706d4200329150303420064400360910a0032040342d000c000161081c80c0d80c1e00929000300d400000403501c0143c050700c100590701c4a41c0130b0f0005901602d80849814880c9503654000c0031803070301c11403450600d4072413184140f01c1800044d0800c03140103c04550f40d100e40c1c3c40000800e01840e1101c51500741442c0040041000f00310075101a400c80700c0202c0010400300894003142d800810841c4983d02e031040005c0150084d009020a102e203480482c81c040721180642107540c0b075002d00050341c6080400d03020b421100b107542d08a411240903c908541e01c44002c01460160107542441500e61160345001160000000300101c42d550020581818000d002e40100302031502c01e4003502d142d03d00700c6031415901c40c4100d4 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 418891142 1250 418889892 418889927
    0x1080c03060c07050c15030403080f07052704060608060a0f120b071b03120e0109080f1e190807080f060907020309030111120612070302010e0612040c0501020d 70
    0x340412100071841c0b0040012a1013070050360b05083da000002600c00705401e203000c1880a002007084101644274007001c0e84901c5003150001035040902c030080180c0904e941b04d4000e00d082c086c58000b40c081c81129a00c000e03200400c2070003002e03218103005040440507503165000e4034846401144001d0250702890a6404040d01c0906003840340d2a002840340d4050b1201e024000c03a240c00c0c17003106011005001c1003502940701c405892560090344021148444104070280c1d1402c0c000ea40042c1c2c4100c2103590070741281d80b901c2d4440040030a8691000c3ca1812041e8842100094214003051000d54600076010240c40e02c0d000740d40da0b81e0041c2c484c10b5045542820040250340054005e2418850f07040d04080940704a9040c0700a4801080c01c4414129103445c08400100b00e00b142018004100c41c0e0041d015284001091124400d050707440d0780500000b4103100d91902c1c080f080d074490505851030f814180100c01a541010300780310901c0040d5005840c010f0103800744040081d8024490b40d41e0210410 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 418892392 1250 418891142 418891153
    0x103110703080f041e0f050601061d06030c040f081c03060302011b03030e010e030c061807140301020904090602070302070614040311040e0105040c0612050c03010e180d030c0801080c03 81
    0x43d4000d100c0e1100080c030456002c08042443e0305000000c40076021a588505c00c402c000c8646400c0c5246003410580c002402c06c4803001695200910385804800c1880c000e0b143c41d40c9070f4070340c0c1c44002d04900507034003d41e6081285d0100051070410011b0114500b09044a50080240e25401300301c040da06075010103400302d203400300b45050080750304c03500d40d4945009150008900307050f05142402d44540384d13400c0d421644040b815115181d418002c1e035400071050707a40d9076140100400419250b41441c07041d204034022014a8100a031029011102c000200910030450311546d40340031070081d00405020303001481f038840041a03490150a814031410711840445003424519942c0f42c0783c0f100c1b07118440cad80054803501902003c2c01c0034080d00780154407860022600314113120004081d072190405501d551030512061140c4500341600300e906440070703814445081d6450005030102c2d02c286008801c41803091103040302030664154400752040410faa03c011003030b41e0302e000880e6201e00044103140d054000 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 418893642 1250 418892392 418892401
    0x703020406050a0e0d0b1305070510020c1912031d09040203120c01140a06080d080c120606090a03030e030106120803010501270e04110303070b06090c0c03040f05010311070308 77
    0x505100a0310b490001c201c3d00f00106142c1d60000c1b1000280c6903504451214800f00e410418280450300146c1415140007091014071078000795603000c105016801030028041d10341240800b40041c034040c02003501541d140c1c1005203030081500c02c181202c90700000c42c6138040f400516100c0003590185d03800900624907006014001400ca40c040c1c40610318542d03803400d40c8201c1d00e102040300c070b00c2403033724582c0050211b10309400300b41480e0a40780908104201d600400128820000903215140404c44000c1259540c4e02c020a089214590015510003c444030020803d5072001c2e88241a0788150300900c0665a500c08404481001550080c1a11010300050040d544070b1a00c548080c1010300f08480e1241c1150381c2d403841335a00307420000790402104100001c1c801d0f04c0406445444040d40214605040d9807604448183c0107400540300755000808601496619403d0b00c00319513000301038a40e140e039205a00f018407680380c411030f0b0110f42040e0420041c0501c1c2800e40d801103403d9150394500b99507 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 418894892 1250 418893642 418893647
    0x1020c030a12180305010608010605010206130f03050c0a0b1005030a03050d0b030c1009080d0801290904020a030617070609091e020a02010203040303110c1009021c08120703020406050a 81
    0x140c0d00d0105080140900382c814043c0b030041205030045020b0000000d0041c106a00c80c0e080d90129042241558020410f00041100795103510070303802d812480c4068034074100c0c50126014400c10400082c1e6108503110041808800b4680134013440c168070341e01c20482e58550a1548075580070300302501054051200700040c88054106008000b001000c1c0c481003540440000e100c21a199101c80024171144c5051000d2001002825010b05131404d0414143d8500a503074180c20002d0b40340200ca0341200c070303100198000880159682c0040c0248299224160600000c1c002c100521a1003079481141c0d44007940c034074000c1400800d07250641c1e039400c400ca040c290128003402a003102e461011002d007a0440042d0024405025218581d0380056039138105428000c007681e0302507240c500c0d0303c03008020680d2066070000c2c195001140081c1c010500c0000c82c000240021002039202800c21490800c00013005658401810f001111041000741e6440d801c100b10200d004500595021400400c0705006990 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 418896142 1250 418894892 418894913
    0xc180528050a0b100206041a060609010c060b0603091f0b0607140c09040c050f0a0f0909060e060a1b08040b04020d23011e090f0215040b0a0203070b010501020c030a 72
    0x1440a400412180e00c180041519130040b25080310058101301b050004008030818000d4185220107201c400c40d003409c000140132489903030217890601c02031201540800001e40c00c8084400001000142c59207032054050b9220000c030003180d0002c4c190f6001c091a0070a0b144103007120790a014007000c0c20800c0c540d1340c3d0100030003c1d0950b00d02e2481198180f0003150f03101d00c034542c0b14074812182c220300c2c80d00c0d003414007070000c00d40c00e1080d02c00e0400100c10302240400c0c01c0302c80210350300c0c494013007548074450401200400014280e15413600840d0104061110142c200c1804190040002d24068074460403c44500406980003420f60071500c0120f07015150181c241e42d51280a01c40401429048616101c920510000800041d9444e0f821300d1983c89080480c2c8100a031049406104030886507484c054400351480c40240b04040c1200440411075001c2c0596028120b100c0707810341c0e15180d001c03019540c3e4100190032140100140c0000c1081d510104040c4204a00600102208812a0784125121 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 418897392 1250 418896142 418896151
    0x10b04151209030f030e030307020a080f0d02070803090618060127020a0306050108060a141e150405040605040c05090f04150e010504050702030c1b04090c18052805 72
    0x204160204201d08541440740322040c510a40300e0b113100001060014043d107201510305030980e0418020002c0b000c0e0040b4425068551112203990340d10b2640213283c201e030044a480c030900038808103002c810081542c005500410865080303400c0f555801816210041c04100160215004800100b04a031141402000c0ba01c846550382190f0702d104c07980f4801207070840520230700081d449481c20040d958001280303a400100c240e40c2540068104113034038070b110a0300107000d4000d120702d40700c08144a081c040313005003500004018141c3d4003e184e038206410b40181c02640d03ca42c1c40c0507800036141c5460f00c110380b0403d045444641c1014000006c0010240103840420342084d240d500d4402d0402074000313a074018040d01201c07440c465051809000450300010075200c2558000c002e0210090000191441e60040030744100d070351140104003040242040d408024410012000003082940c0440589a0044189901041a60750780b0900580b40c251111382c1c00c0001c640005100080c003507a801c2158003 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 418898642 1250 418897392 418897397
    0x204063506091b03190f0c170a111206071d0117010608070c0506101707061407142d0c010f1d090c030402090a06030209010b0703180b09010f0503010b0415 68
    0x480c0311115140b41240b10303100c0c0c01c4a00748031450310442081f21441910010b4208103d680d01c200403022032240d6114805800075001c4481048204410f0362000604401881038500766003260034034240180211407130780c140d4042c0004404d90400254420745d080700c1003001c10010396107264a41354003516040c10103850079080080c200c0141c0081141042124012441c07054075015062910794100c1a540c841d50041049800c0f200042045a62049007800340f42402d60060b03649484601c0c00d245d2403040301c080d942050154101064100200e40c058500091000680701140d41c4c0450206803100d950b1001c04d8003166401815050f01442110ba80c0d440000300000800d40300305031000034201a00440c0d034418609000000c100440c1800340c1c50641040d1600d500b804680c1c210380c0007910000050041d1800c002c40820600c0501d40710340a10000c42e18a0708585500750b488400c206c60981c8046103490100740c030b580c28003a002c0e20510449040b85c403480d2005041030308218500645440c08038000c3d04 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 418899892 1250 418898642 418898653
    0xd0906020c1021110a0e01080103050a11190303091d090607030e010212010b07060629030c07200108070908030409020c01090b0a0204080105070314060d0204063506091b03 75
    0xc0f01d0b065031207610240007980924035100d2010030390003450001081116410090301d600108009000000e0050500360301c140b07195400e400981c049050807010260541007113410780f40001c24160481049006d90301031540540440d103030303184e5810300103c068401480300d900840002da40603120b940014101061031001510340900413140c0c010180c001e030800403a035480003c0b0401001454410100144074812802c0b214020361155501701c2c450355480b613090780381c0010010b41b501103614100c1d00240e900000c0f0103101c0c10003443d109a4800c0d4503420381d010441840119054501500382881200c407504015450103003042c44c0c0001a401440c07a400f80b81d900c40f003c0e60000364114485500c500b2000e0360060300d80c0d140006450a5440c003401d640207044c07504542081d4052507101c0c040d0310050039690326000010910114004001d507034060b140d1007403443d03103c0189445814581006030400c50458020052075941140c44030403d54241145a01885298011005440001030190300040a481 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 418901142 1250 418899892 418899947
    0x2031519050d06020301090509010e061303050d060608061e100c0203100e0307030f170403032f070201090e01060e150d0609060503060a0903080121060c020d0906020c10 74
    0x11140e10310b58000703c9820f038012005008a084900c51240c0c02001d40000340010f0704428440ea44485002e04111503110310140400c083c9800790f0215845464221030400003155220002400e110007039503900e02c41c034111440c501c4d100540741450007441030f00030a011075011030500c3c2914421020841280c25003e0704051044200c00d034810002070448407401b5642d10200c0341303001428940c500c040302041c020304d407030450000c82113883d18503402941802c002404004402e0303008c0170107441d106ca441280702d0603005408541c0c1e40a000d8000a8803e803540300016464440c1030030a00d0003400b4910001c0c0c1601c06410b000d14007400b400350784500e0995660324000588901c42e042c0da8845d04411017071501d4007001c00190608101c0355034032070703200801000181c0b041e5070014841c58040c81100c0c41506d903218a140250700c00400a00810b9200d082008842c1c0c600002035124043c10340e5550101d071482d0800035402d1b0001c1510419107400038841340c25046003020940e03400b0341c0710f903424039200e400e407286a = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 418902392 1250 418901142 418901149
    0x71805040b1f09060f020307081801020a05010516030b120d0e1c0c0f1509090b0301060b12060a05060315010804031e021608030903070b16150515040203151905 70
    0x100b070a00c01550310781c58140d05010003c4d100710b602603600d5046610401450005c0390303801d800d40e00b001c0560654105042d912500407031038100e02e150f015085500e480700344584622a80c5d582c81c60b41c4031613101031011007005410401000e04070b07442c036081074019884044501d40300700401c40c541030000780b114040c5c411041c2c10880d40e004101e000c071000080100700303100364035603030f660640100402010841030641041c0018801d03c51440360792981500c500b41800c690780c1c00e40002025007400710140340c60702c041094000516034103403111030051000140c040b400c0d00b04201201e105003e4203051103003600d40d8000440e000306005005800304641e02c000f00080401c080c103040c104400750f60052a42224022602082e10301944c0b041d41c640e4801c0200c9203294402003180c03001c586030207600721381b00d4a180107400c5100741000401000c6240c0451034180440b110341c0181e0103006041468014101c0b91414082240b01c10341c0e05220104200c50341e107030185400040000c0b40c0740c1e5012104905a90f80022 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 418903642 1250 418902392 418902439
    0x50328020f0411210f01030f0b0601020f010c0224040b040f061d03090a0e06100c050c10120b0306040b04110a0b0f041403030f071211030d06030506071805040b 70
    0x422604504c540440c112100019001a0070601d080996600c5500d1a503030750100142c0b0100042001c0900c50000340503a0003031000c014a0303000200240041030308980c0007174540e6040100d031085a1480c00002c08040e0250035203d200325402072650406032035a80700e0130b462404c550f500725031154032502850140c13000d09000307040d01260b000040d074440444c42d081005940e01508170785100a1142d082000707564400c618281c01905504207040c10018904042d030038031400058164000141480311105c165000b00072075004605208100f050318003a0040548401040c4e0700680007400c10000b04000c0f80c840e0152140d071000003050b00b122103554407058a5940c100014400c1c681102040400070140d11300030314815110102c011b1450903090642020303980c05902e801400500b030283c0d4264046025280801d07610388c0180843e078031180c5a0030304030003030001408111001e00580c400308a00a01560310400009020300201c20700501300030602004000b8640d0a5034440c1c4140300c000c0d940d0681910 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 418904892 1250 418903642 418903657
    0xb070c1506030b18060f0106121b050405010807050307021c0e130518030c0615150d0f0c0201020901021b010302040909120e030d050406080709080115050328020f0411 73
    0x8903a250f0301c4c0c29102035003403407114040040c00da00000c0401503104810003038107040d5001814264090100300481c1d500601c9850000340c895003c0d000c41c0d0101a400401600445600b40d030340d003442d33a0312400119aa4002a00c2000150303102c0000260b1128402e0900015107002c1d00d40340040d20320083c0051001030880d14490400b5aa80c003d12041c0310102f0f00c10190180040c008500d400d0a0100032591000001e1002518900d42083c0380e1030b41d80d03044d0001900d203044c42c507416207a0841c03080c07290003800f041b07d2101c038940c0742080c04080b0500600039602c5a04058010740b07040c003240c5e42c0044c1c0208281ca10700b81055820000407884101520500040c0c5018800d0041d441187d490b02400c0050710720582e51190344102c450b2502d00791b10504807000d0307840e145401c880c3c5488a200c291246030302900060280e508000303d03881c0380706040742070300c086440440881e0b404201840041c0c080030b640000f00050342ea070391400c41c0c1c00350900605a84020001034400141103c9103160541503030010003 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 418906142 1250 418904892 418904903
    0xe10030f05071101110406090e040c0b030702010c0e0109150f0207050301020703110d0305060d110414092103060109030605130c0b12150f04090213020310210b070c150603 75
    0x3003a24018903c248241c6864056005602c0d2030305040c80c401504410f01c40c8501d0040010400014042112407842e250081c50b0034400151a030500100281c082c4c00c20395000c0c000590020f200400b81d41c4141c00b440110340f5800380c0e0b121000322070f80c403c941454041208400703602c6288800241c1ba1024401400a607019641c4c0ca034041c0507440c0458101130492910340700b054101410710542d81d07142c02d0001005680b000c650170191000c000070070083c0c8410404c69120500c0c0c2420030404c000f011850411a0032401c020b030404050022402c81580801e40d410740c006046020b0502c00290340d13901c4590403190581c4002c070413070a5a0344140545006030032854070b01c0c0c00410040c49500300030304031135040402c070300300202c4000541340400c44003014400070b103100350b4651180c0d8042d9201d160303401c1c0070f00c072080c482076549140c403002002809841e80300c0d02d05a1180064000c2c00c0a01402c000e05500d6409459001161100142241e07a002c00b00420740c0c045d081220100790b496401d02c5824021032045 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 418907392 1250 418906142 418906157
    0x402040b0901082109010e0d05010b060d0b13060803032a0a0302130905010b0906030402040f09050d23160c12052b0210020f04050d0c0905060604060e10030f0507 71
    0x940100c07013406441da000c50803c0003c2c06142c80c1613070040b011840a00341600c00149041d4541003180c0540700c4545015000800015800720310f41321500502c1803808155022288060101c022790122a000d100d40b0305150014408107801511501c0030405411000e400791400103428811240664040c1c280b4501190380054007070640d007100c280c020014031601138108410f40c50440302c06a10303c1003210b030034460038001000070110360300d5a1154098000b411002c000c46020703403405a80e260b0aa040c0940458901d0b00307100c5098a119414031a0500030845080c1441841072029100010414003100c030640100004941d4540b601c2019034014013449c0244462250749121501d1203400300c040c4503241d035004211040740c03500081c52045808074502c005944a0025034100c00c18021030704000e074030040305c0700e08c3d000341b242c5803c51401b9500c40000810036901d4580400c6114800c501c100c9002c989055500c030710902d841040088100030504000c01c4100318410f1300011520112020004500c0c01d = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 418908642 1250 418907392 418907413
    0x40f082d070302010606180302060f1c09050f07050105040519030510020909060a080312060f030106090f180b0a0209032b020c0402040b09270903220f0e0402040b090108 74
    0x24003483d8014091428070f94008087c031082001d180f03400d40000f0b4020840092545407070945101151800090403a0107003040c20200c05c500054034842c10181c0b02d9109445c05c03814800000b240010803600c0584030580380c42e1a00090003040b00704140d120000308030703104c0c0000c040ba600748424132844031138010060b51407441034100720360124060100d600031508094284111200001102c0c0c1c00c500c0a1007001550f0382d00c1c07001618000e800b01c0603a42650802100140b80041c0380c10208a4010f0554140b00d0480c2480c204501107000100182c0511040c1000c51442049070f07000785a030840c0603050b21030a091443c0160020f0f0146000074210000c04407845040660602c040810b00340104d40030340c50f140ca02004006240180c4070070302c0c03280040016400d40107000c0c80c80b54100180b211030b0540c903803030006420358a03034002c1c545803c0300344020381c0850b4040c0340d02c2003c0350583d4001003a2000350307402c1030410a000d40d4000c00c02c82c1c00640d1548003007126560310000714024800d000007414028034 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 418909892 1250 418908642 418908647
    0x3030421020303160302070f1403070605010b0304050703030f050f1c0b01020a2a05040c020c01020f010b0901060318050a12020d021c0e03033609040f082d0703 70
    0x80080420210b41050003400340942d0482001c924100140c0750150300c036940b50400541d002400c00d4020800071801d007181c6220700c400710181088a000b58030400c1a6070f03861a5498851000300d80080c45c0790400002030000901030022201000f10500e00b05041c5510700115400c50341c000031940c1d902c09101d0413041002c00f903501881d00039180a1001d0030030680326584028442d01202c50100f00d06111480914010310303140000802021b00030028080300c03401f64006502d80cac1402c6141030050241000c2a903410405014120340003074041c01c00f112681c41e040c0e0890003003920705202d100c418100180c100104504101c081451405004012030307411090708040d281c401e080f07462a040d50410202000e0384076030b520691000c070b949400d0a000600d030110000341580700f641440d408152507544003c014070160200988403900d8648841c52041020381007180e410001c42c0c00420350444440b2031000a0503c03806844100d0300300200082d14900505c03032500140046e0f41507824010040381400c145903 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 418911142 1250 418909892 418909943
    0x1020414010201180204020f0903030f04090c0903150209010c02040912021e0c060307020a0b0f040c0501050c100c09090608010506041109010f050327030318030a120e01020408030304 80
    0x208240004c1024500000c000085080301d40ba010303110f694041981202080c08808a5078a02e078001c040da82c3da190b54064400c19900980241c2e82c195240440c06411680a038424000f030700e400c131b0290300442015428401c0a035101410003410084117003644030050f05d50303000745040c052041c0340304c104a89242d140203141118000e2035120040c84040e030a9a01900468180d41d4460701355401039803592b07000c2050340360001c2d210008190002403c10040081441445903008600c19030900d441c5550303030b1004640d09d001d5004c5a0005402502c104980050258048120900346040100c1190382c4c4468880464000d903100b41e109944400400c0380ca031030f2a01c0744180d80340304c44140e00d00f03041e1300700e000070300400c40540d80105100000010400a41011000c3c0307403141d0384052282c00c00c1c407450001035200d800682c1c1c5400b540802c0e102d80318144d1004002e6a000190030f41e00c1c401c0b0880c1c200301e82c0300170341003550485409550070400810506000d000640c40b86024166910f0b070403000101000961 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 418912392 1250 418911142 418911179
    0x1c06050f0a0203070903110307120507060905060a09060c05150a02090906041b12020409060306090308070207061b0f051b12011503020405060f091f05180f090f0f010204 74
    0x140d104008000010340c03c021701000b501c1c0c0040c032611413440f128001c686021969044500c2140c200d85c43e800c104180051840140d4034203a83d48408141d07038209220242c024220900081515400c043c00242c0c0b04001649015008100715028a011650704c0600540103445070a401c9030005555035003410b14100705034003e1400c0c0c608108850781a210307168414940b848100c1040403165281c080314000303070107a030b01902140d541005815601d2800c0c0000f000f030b5600c00c80104801c1000102e05900124441041f9206a11035000c0e0600d41d42071030181034003d8a080300c140201a020300302140e4100300f0401d042a00311201705982182c0d200b001042c07040b417950070b4426070414501c88d590b00109990b030323404c4990544010602c2d44409c0d001802d02104101c00c00d4124410104220321203c4841d0807070464100c1d0003200d07107090b4462041c406400c0800c882c0ea0440030214001c81c40c0c15101c400030551045500007074071980100c100e0214141039001c400c0c0d0307140f80e4002c40d09000804c400c41c48a400e6 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 418913642 1250 418912392 418912411
    0xc0b040305181212030702071e030b0618061c143d09030c080304031d0d021f09030f050d020105010f05100c05010b0a0e0907080d021009021c06050f 65
    0x903850301200503030740c2c0c060385081d0f204c2803040400883c04090007000702c2c4015050f40011043d0385044410f280d5011001c600c07050b18100100004501c0c0303410620185001a8881082100036603501d405000004040d85003040c1c2a011000e50318010440780300e440c01010486034040c0070f6020318107100e070398242140007115072500d0040201e224001d4480d69000f801c84c904070004a541905801c003545c41c06030b040c601800c40c0c03030000100010140c6c001101c81e6101e00300300c468014050020103003c040040e00c40c009406c1000301c02e206140c0340c0590f00780c44645600786040f03400303d6203a030f80c3c0607000c100d000002c40340d55000480c04080d4940a01130940900076503413038400e03003078901000204070b00b2085d0324042c00d1161071040542070200c02c0d00104101c4002070300458000b595940424001c07801103e010116008140000c1580d0401140b09090780c4241e031700a010400880079444010040b121040368000d1520806c05039010040030021910340c000d0100281524056400b603506003001000081c9 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 418914892 1250 418913642 418913659
    0x50a090b0906030118120c061128050f0d020c0115090c05090a03030806030a06051512030708030402221d060906040203120d020d110901021605150a0c0b04030518 71
    0x5485d032080c00d901010ba04290002c08030707001c11200303442202210383e018104a0400009082c510b150900408022000500082180c8020ba0400d41d45031540003034000011020003e105005021801410500c0c810400040ca0f041440e2025400c6904804034031200d00c500d0078082000402612030b180c44a0500d0030240e2400500400080c0f88400e140001000e05c40c11a010030b1050300c04000d40d94500b0750080080000b41803580d443c00b801c280d161440e40c400c500d003c03c52100141e0210a17529040c1c0d00103070031400d60f121942001440302c18001d00584404401501000303e40250141c1c2c09441c07179807408259140c401119490038480e0080803000c00c0c0d40418103002c010380740011100c1c0c5c841d4040b03804903128030301e0b03400c018040c0c45150504c1103a1810074444007141000c4070000d25054209800320b130000080941003080d603940c5803103255841103101c1e802c1c5061141d184001d00088045141100030944142c1c1e0301d43c6915410b44040c0e00040012035480030200300050880c0e0181d104641210 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 418916142 1250 418914892 418914911
    0xc10030e150705070c0e061009031106030601021504060b0a120309060809010b0a08030a1106010e0604090201050904180615030506041b0503060106050309061015030504020a050a090b09060301 84
    0xd50707940812440c000d803810768030000780d425403142c3c05848a8035842050007000954030403100d40190004d40b0200c0c0b20705001c40d2142c09043c0105d81d030348100c80d07028440700c486184400c208081500014200c3d4198043e90540105034001c0c003042c2d42c4220310071980013402c0d804200c01d0084800c00354001c00008203a8483d48000702e41c210300d80c14101c80141c83c00b5005650b40074000c80c0136040e00c252135a00701e80d031404040390f000030200261880a88580d00d1075891004a200303291764900a202c1c401e540ca08140c00328143e82001c0e00685250360040c1131880c545041180807404039010b100c60301c5258040700c2040002c1013003e0082d41041e64a01c0801c4000c02c0c21a04c40d84d0701c54501810080940000d045244209241c802c0d101005000080c2501d00941c4d44540181c0180c1c403c54100b0300c240240e0380090b010a9100d1403a00503150007e4003000c50130178241c0c040c0c005005c090000e9a1040704140e00081d540ea5050f050f001818002101080c803041d00d00910106c500702809a6201ba4103043e0fa15 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 418917392 1250 418916142 418916171
    0x4a010807080d0e01120f1d03030118051311030304031a070f080105151605010e0a060510030308040f061d0a050c060304170a030e030d0b1905031f0209120c1003 70
    0x781044082c000562203502000c051b008140907449128103d1034800d43d02401000480914100d07641c0e041114506030005203084110351044070400420080410300314042a030413050340b000b002019040703d01d416100d40709c3c01c1c9001209502d110b14a0000010800300d0380c0d22141802a404030390401c02d44550401c03000822103038400750010313032242021448012001c85040044242c41d0440001c0100010342190350b40c4030980a04151b84030750500010840020046010b074044941650343d42805441c0c65403002211001400181d07404c3c0d80b2221750000404030a8001403003400c0600007000f084886240860600030546a0140b00302d000780100320100e484a010001ca902d8200d03d0313288e4880030326a0a030f00034040782a55100c18032012440c1e000c1c02c0c034640c0c01225101d00489070305400080309800240040d00e180030b50340d05500065200315a00189011003150004030990150403c807004000c151004c1824000501540c03010348030100313a080c141e664400b03021441c0b8050003009100d0546 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 418918642 1250 418917392 418917407
    0x190b090d021c0516020406030f2607060507050c0610081b100c150507030609050609040201120507030b060c03041509080705010c0326104a010807080d0e01 68
    0x40040c814001000540c2c211318030400303100d0680c02171040111a0b01e90a268140d0081c1c0c070021a05195070401005c0300c000c000b001203801466944002d4502140b40d078486003e0700025054409101d0144001c4518a2051102d58800c0c8800c5401040302468203401a24002611940c05682200c0a41d08d4030b080c0c864100c401800c0030142814240b40d203042c60310142521080318400303110342c5441d05100060340d2540107a800c42e58003c0050150f034039a0001c01601c107005481c0240802c0089d40404030900342c0743c03c0f80358842c41a00b0f0000d03580041901007503087d030105181058580000600b88048010b840c411201820b05c3c1c9022031450f070600b07601031340e0360200d401894180304250f0320038802c0612521441e0364440304d030390700400152030030701c02c038060608242c4884444543c40040440d040800140c040340d000e80104400c011842810071112038200c002e48004250313041c80041444900c1201007032402048801c0042401c503180c5081c041c01c20f6400103540042101d201000c1d9203507a4132825 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 418919892 1250 418918642 418918693
    0xf06040501170603120a03090201020c01030203130303090606050d1a0a0522110d060b0f3c030a0b040c0812030c1b071806092309190b090d02 62
    0x103008502d0b1600340c0001d00e0085c1d4810400403204000030103e0105500d03810088016100b0707002c80f504182c2110065060340412624280c0c000008403189011910030b401c003402c628050400052000e456801103042e02460402c15950703400f15407403030b0084040d60820950b001a800302c080040741410060340c0e50365884201d55120805007140c80f4000d1140c1c0100f64001044002c1429054510070714041d0003130658980303414411440d030407820b01241801441c62100d60480d4441d40380803140c0040401d0b4180d4034038034040e404584004800501d07201084070b403449034000c1a2141031442c283c6000002c494075904841010b4000511220101068605990b001401c401001d0b0b01d42403081ca500a0000c0c10b10001e0001d0312540b200000c1403004410903032a0041102401c0c0041a2140800000e0b1259041010b40801e000e0444070178440c04a40459041380039042624010f05034544201d01302c1610801c2510200184010701c2940101008440c1241070341d0300107030030484240c1031901070380000d048 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 418921142 1250 418919892 418919927
    0x40f0f290d02190e190f060f09091401050114091509071d300f0c040b0612161d01121814060603010b03030c03031501050c1b0f06040501 60
    0x1203440284032a24015401380054200307908861510081c64a80c18007070804046541d407514440e403c07884070f940114405e56442c80b84031045035140081e040001c1c2000030003038608206001320502c1c40d10081c010309008000c0d400d244205a1149002c00c0900c0c503001d0701038501e5924540d007031611038035100507543d40429142041403c0b00e0910b0040f5a8041c03031309070144d42c0001b59280d580c1691081c00900c04005004a0380403c400c44090040e80e41c403441882407885c5c99014141c82d0030140340940008002141c040c05183c2007000240307501070a804165880c0350b280840b0b50204544640c03052008014840c69a01d05218485450006c3d104202c10749036421865181c40383c05a4154260440b104415400400440a840f0000640791955020f0f240148030b0350a20508a00318030300042641c1c5501ca81742d028500d542c0f14402090000300e0840443d60502c902400b5600b82100103018044100b010080f1490000c00042c041012803245000d000e8402e000600082c840782e60b000c0003052030041c651 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 418922392 1250 418921142 418921159
    0xf030f08090f040e151005010903020d1713081c120c02070803070605090d111218060a0c0501110c0a0204050a15270524040f0f290d02 59
    0x400480c8006045120b4250001e0401d943e80c00302d80d1000580307110034022003162803c16151100201080100c6104250009031400010700161a00842401e8400d204d10042444d20800484450351030300a55810306070300c41888420800c1c2c02c0305000c0724800400344d0250001c0441600809003100845065a9200340da48401c0c44400e030340204080383c00340803680b045030303112042c2d4603140000d000e0441d600d0025000300b2030404501401029070824081c01ca00c090600d480c0c0a00300b48049410020068551400c04510000540c0b01d070002086e005249544c3c10000c204541084c0b0f003943c40e401400ca0020f5001c0114110585006c582003a229504403000f05441d150301c00140c001d0000001c00e0408103d50000015000c84560740c20210400c00c94032961320603090315600e0007114411184d241054bc8178000311461044499031904401c240203000041455001456204452000003d0710280e5036410f00c0000001342040c03411806030380034500c00042e40349140800c01e820f6940320003d000e109071 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 418923642 1250 418922392 418922407
    0xa090f05151b0610050411090612090a0b0103061406030f0c04021336020c190521030916031a1902030a050a0b04020a0f080c0f0d0e070f030f08 63
    0x15400202090404803c441550400c1800110158410710620348110715000d0703000082c0e2503180a803984488000e005034148980030512040c1c1d201d000f803031002203000b4010140000307061018020302030343c000e18001802a115143c0c9008400d005070815100368045618a10882000a0b200340100d0080e170340541c650311034414009180d280c030b070810740d6100d4400070000c5120b0004003911030580d0910341940f90070140742c45803108a114500342e03002c0c0c0c2d811903504161019250b03402030340d80d14440e10864020041da104895a0b403042008030b031201c014000f0a003c403c41d0b00b00544d025054401c0c0c1850700161441d0f695106045602014600400440c0001a4100b40b038115004d00300c104142e0545d6a4508980f054008010884026180d21b2909004e0300d01810039200703031400e880303e544a450420401d81026241c042d0001c018561818081010307024220001d8050010310594140100d81c06d10101300b11818070b84aa04400a40110514104045200324244145c0542c1100b1107a075900c00 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 418924892 1250 418923642 418923667
    0xe1501031419050d03050105061215060408151b0909010e0a0207050f030301050a0b0c030901111002040305063414072a05040b010c03140702030a080a090f0515 70
    0x440b1102c80c503071005862004140440402e0000501c400c503501000180e8850040088601076a041c280100354030a0008201030301250320200b0131030700184200e05141d40c0303500b0300e0b141c202002c80d02d1011003d41401d015081130404400030380d88908804072420081250085040d00405200e4004001c0c444008116401a43e03130440720290740203000e4906004c0d800d00100e54a501c01e1040394068080c058002402800311010764004035038620103545483c5002d001100c1c582501e128000c00c80c0100594040000e1035403004000075849080682070900e802d0b08a5200391030794400303070030720000d02c81101ba0403407000401c01c18419400e0308081041000068241c042c0b070003180c400801d01c46148280280f2050f029101e00b28121720055400b01650b1a081848141d034038031a101804150500f19030b0000a001341103002610300c00c90341190401d9500d0700000d01c0d05c07404140c04d64213480300098042500780c1c0406804040c001170040a50918a000c000c110f9984200002c0100300c000410807554440 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 418926142 1250 418924892 418924903
    0x736170c040b10050d18030503010602070b07080f1c0509010605031506060306120c0612014106070f11100e0d0b0423010509071409220501020a0e040e15010314 70
    0x1c03241b080e401c0705039521380600710358001c4c042c0300302501c03e0200016007102d090003190005548410391038100341d01c508804415402154450010400400300c0c603055400c60300c00d5600c10601240041070f6140f4010a06003041c450022810b03c9100d9042000f01c0c41c0c44080c1200c2d000002070351048110719152505d181002c42a01d68681d00c4440024101d0030560820320080c140c80d0030010701e0780304e00d8101840945030f400741400c100c180c0c2c51524251520504141a4001c070881c05000a0b2034942a59200d10003c40080320071100040d80882c00343c00c50400f00e4202c4607624040c244540e90601c51800370314560360201006051041410008040111180051000c824a0450003550030030310340c1c62901070304044500d0781a070300c42c110000981425074034210030842c4020b001e155040e02c9920110a58800d8040608403503200303844c604002400900c014458014150755903003d80000c3d104010035503015500e6200a98004951100c801005041e030f6130440b5803217400e00340710340c00840d842d60804 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 418927392 1250 418926142 418926161
    0xa1202011b0b07031103060d14160b0403120908030403060b06070506090c1c0b060f010c0b0114040f020424030b040c0203071a0736170c040b10050d 65
    0x4600a01c4101c04006046048502582d0b050300c060144520300c4003a00400e000c126060395000c1518a03140b00420341c6070034610740050301501a41c090f180d220341c48110211703459011205544000404000b80304021020f40401e907254501200014581032030541d49010700d02020f04025030301c500d00005551500111400301d60711500741c13415807801640454540040300440750140b4066500040e04ac081c0707003080d500740c031352007062091682c855034207011441c4030848429046c04100d441d10404903194544aa00804802c1950174180c450481031100b903c0e403034000e40d005140140000d009601c1c2c0d505540e14030344050088010403001b81c04049000e0303c0d0210410b600145000c03e044150b03075003c401062000d000e404910b201400c6009880c900d20000c880c00000960100801110840c01e04100c452802e12100b0b00c420901650050702c00c403a54603403101e0350315010b0038154a0403075020f2212045440d800c542c00c004c00e00b00348011071040140d02401e0020020009145080c0c4801940a01e451 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 418928642 1250 418927392 418927427
    0x60e010f0905030a0201050702010506010203180d02040e06090127020f010c081305030c06040f060c0807170306040c0e06030619090204030501020714010c020c01110c1504061d0a120201 81
    0xc6079800c2c190703243d500030901000103500b4000000c2302e00b4014002c2900400d0103a000790701e004080d0480c00c9a51641e461a035600111640180c1c3c0966101e0081404140041c0e01801e41d034240340c0111402c42e907209080203c4040c4040c510b5044074a94002c2c150045c4c0c05036940300842c01810012298042114001003513100702261584098002880180070f0328400c0d011100344103000b80420001340114444e082000e100c5e40814002c1034890510203818a108549060900d88903a407142c42448003000c1814144602104000b8985010b0140319941d230214184114090020804200c2d03c0c0700041102e4019001200310381c8000f03009504650042042d0001192580d45901e03006010b036000100903684943c1540003425044418072808140d00034a4000700030383c0c0b02c01d100643e0310040400940f40a07006888050225444601e001c1000112155170780390364a0420030040d01d241d85c8078a504800600d550300f00c144984441d18074006a036584503600036010722a100407104c82d0384500d0400e10 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 418929892 1250 418928642 418928651
    0x2070507210f1106160b0601090504060b030402010c241b0f0906081e0f011409091f1d07050a090c0c02240703050316030b0d0624030b01080c060405030703060e010f 72
    0xb8481259046c1d4082ca4099a17460390650391a001c01040e20140c0c06001c01c2c1c684100045001076018141001c410b0b842021181400c9c085035400401d1442c1c801080c11405889030750700c0b0b12100603000030804009442c109000312240d0070600600e04003441c0640341c1071222540103d41091110a003508007182440d01b4030a40e440c15022948100c4802e1245074942d00380103103180c2d014689644036034403402854004010480c1c0c2090381d091003062201640407002e540340c0504a20981040422541c8140c440092900d1850901404400c141c540d0008411520340060020207503440f04810000a07011038560f600c00d03080c03c02030445502c02c3d00c42c2e00014440081e40000301a0000003030341c03288010030724103004540320800541c29035007840e0045d503000a20308241c20002d45903a0142c0c61100030031104c01088245900302d0341d080101034000b0740c0c40c5699580104a8031308200700411007c0010340e040d07801c1ca0b10340700100f82e0ba041140002084e1a40380c29407802540f0096104a03015008440140f0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 418931142 1250 418929892 418929937
    0x804030c0507081f0b0102030c10090c090203071d0301230907090c0c0303060501050a05121b0a02010b030609011503030f030209060304030e1003050105010504050f0a0902070507210f1106 82
    0x2400311542c13050b030013856040046090256001105075560505030401900c6801c00c080400c1c802040d8411040382c210981500c0818458104c1c8099417182855448426008501f4401c0d001d081983c20fa6041c403d03070422400041c2c1d9042180704241500c2d41c0c0c014400140c940c4820503050121640104488516044130030f01c5040c0c0c0440090300c072a01079141040003030b0700c820044996108045140300440c07401c1110680d0034109a103a07942c058415000704030884602c0e10150312992180c00c450006079101c21016105280500c04290420102e02c020444d0781041602610340200501c809400d005c4001d92401c5001c0c001e40440e0345a0000800785030744c03450580750140c81043d00b07083c010301820030800c0c3c000007980a88a2a4143c1d0f40c142c50305400d280c5002c0400c03090061200c0c800c0c1e080740481c10009050f0b00580090008144200d019056081c1048148d8018031090320814444100766401c00012071020a02d50662540281d8114003540309080810694410000c52140e00d0f11000c0684 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 418932392 1250 418931142 418931173
    0xa0302010b1306080d0f03020909040c09060807030b0106050304140609160b0909040221070f050f01080c0a051303020616120c08090405040f0813030c06030203070804030c050708 78
    0x801941d0121450000d0440c55400002160304900881c2042e80c0b048007134085c640d00500426210502c180f9000d0b140208003408182c1141d000c1c2c42c2194140c1c2002000d10080107540100c801410000300100f12007443c5403075000880c0018420802400701c0000071500780000c106042a040031b10b9412101d00d4184221815941e403030358411481d10051200300801d03040101000c480d0f00300341c001c0481070240c41e544c0821007040707045220312081c0c0491b020131202070202404040700415007141d1048000303181c441402030520744d0646c00345c1086110810040c1d80d095040940e200c0d4102131405688440070000710700c101031000d41000e90b01c041c02003030301c460040701c2801100d00b00344610058009081d0740101070f6102c0c600454010a6224180005c0c05641003551207a54400d014030145030b09202651078410386a44000c00041c0c0c0c40d0388005080c1f05110b154120380c0c0040945140451079890803400080010b003014000404011070101030343c0c2405002c01102029004e04000d40d0b04250011031030 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 418933642 1250 418932392 418932401
    0xc040b1c02012a06150509070e01031506090503070e0c16050307170c0d0201200705031213050c0303070308280213060806030a030504170f0115180b2d030a030201 71
    0xc0762071380e080203d2034450304005000c1e0012120702070071420240d00d800350280d5118103410030749810540d0710709100707c02c0c4030600201d4005102d01e890f201249402c0100741400c2500d80e42082000d1084c5505112010351003800721400e4491400050f151020b040c40c009085120352000986045a02d0000c0d440744080c5030000c2141d002071400311400c440c1c445e0340690070f84040ca64200460074030002c1101400342d00d24004c1078003a2043c400c0c0c2e0300c3d1079074006480c0c1003200c0a903050040380b8441c105072020080e003001242d2000900300c0c000c500307045560360010034020004141c0c0603540e90070f1843c64002d400c0700383c40174a900180358043d51180700d0b20691a08001891081c0da00040140740403034151304001c122840350f2138240ea41c0520740742c14580d400b1385d076114501c0b0412480c841c1080d406150032083c0b060f0041e03c0e030246d82c056526450820520b4040c0074010341c8000981c40c0c4446200596609586c1c81412030415045165080062004900b40031a8548050301406010703400410103a06511 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 418934892 1250 418933642 418933727
    0x27050304081227060d0209010309020a0b030f070215060d0503090904030302030a060608010b09121f091502190e0102070302060c0706030501120b27100b01020c040b1c0201 75
    0x25850003403d6400c1000100d0070020002c3e4100b401045901074404058008011303610060401040d10226607002c941348600320b9105c11400500071040c8031104017140102c03a08a526071004004040090506c403e240c20003030961480b6100c3c5c101c503101080340a105507038135000010081c4c100b174030b0700c0c1c2005070203584204e4000410a01c0d00e100411560700a040c494140c0c0d980b40700980c01c1010384014401e90100c62070490b01c4034030410340c0209240c50650342504110030304c03150100e4895460b28000d2006c0c0b1041e030100c000700303005200008902225030301482d806061442d2003c4070310070040c0140c1c01c02100d904041e400c0400003c4600000ca80064210126801d640e82044141e07078911301100100442d0310014a09900d0a01180e0700348103050b4282440c089040d540c00d155020458014508036110400c90f40294541c038841070b4568050120101049003500e01341720030102c4e00001002548006244a1000d488001c03040640e4441e1141c1c00285000300207988294002e02900141c41280c02c4 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 418936142 1250 418934892 418934917
    0x1312110d050a141227071e08070b13090501060e240f04080607050403020105030c070507150c0624092a09090b0a0e060409061515020c04270503040812 66
    0x44446160400e940204060700d40c1017005800c8546c00d2500724008508880c01451801516450100d07404405115001c001c0c45500f032035030341e2811070b409a1403940c01036070b0118418610380030041042c0c0360040c2619501c4d01007210f0144807208a03147c28100020544865200d50002050507c0001810300c0180280c0d01c0400445406c2e40da600b00884191046000c0240010000e0021074582c0c20041c0140c064117200702c007075480e090344492900e2200c075031084d005000030715950140002c0c080180300d05001010000602a10360b200c5e01c0a1440c03000380780c800c134520b4070380c0c0300ca01000074549000d045e00b0400390040b05545034400360400a1080455000301c3e5682c6281c50701c48401c515100010b10100c03040c00e13405140c19030300ca0381008010086030b28140e50705901d0750728005185150b4028100039100c4401a060343c910001802458115088090f600481c070f003810301c803403100d5206003860210135111995940c2510324501079045004543c041c1c0b0381c03803040d00f860144403251030000c0d0a4072414207 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 418937392 1250 418936142 418936171
    0x40609062705010509030a0c170c100209190602120a180303030203010e0c0a090e0603030d150603061205030702040c0203040807080309010e0303090a0b1e031312110d050a1412 77
    0xba07061710f4a912450f000c074008036004d81e005500140f1078032640058440046802824101504011820140ca066034100159400031b00c2c10b140d032401c040c41071a0080b100007031480c3c042c1006000f0303603644000a49070055040110b603082c40d02d4811480d5a0305019104d48007010f00e50307246806000b0390002e01400103905403810004410203515000e4a00410469407814402480c00304441009100600000d070180402c00c101c40002c0c0f407034028144c04020442c800d0501072b280040050895105410090100b030340003e001011039000402d07504082d0301150005419080000d060b45148100c0d4803500341c83c02914400207038501d001c0301a00440500b030301d4075101103189004054480c451448a030b5801a051501808042e00800203030241a0900640084115001c8000c510513007046401104588201c840e0b041080041c03c000c00340700d81c1c0c50600b1010200507283e12070305d17040d03025038a40801c00041902000d0303500c90003040142142d00076010741d650200001445c0c3d010b2003119003401120381c0 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 418938642 1250 418937392 418937401
    0x60f0f0a02280813050d0c080c06091605042018120d0806060406023c0115060e030a0602030702010f0609201306050304020a0b03070c060f050c030406090627050105 72
    0x8810030707413040c56111004c0c00c1ca401280c01c0c10b980800c070710030b4182c07052203090010310200d81d01008000d002d869648001d20041c8603204081e00b0484041d000640240d00b4044165103440409444642281451103000c0e1540304455008030040c0c16540d034198043c00c02c4400240e4400c02080c001400342c420ba41c0ca01c003941d502020300ad230711b100e04e20641c030050703010381408211040300b800403013640500e000004055250345100da0b01c0150203e01c24680d0390b55150310064000141001050041849007080c003008000e040000e51264001c0d44068101a000400164858400c8d03129080356541180204589502e13806510001e20014a10751a142d034035860080b5403200d40f03019284100d0501c850404c008d420580110748030341015004a030801c510032030108401440c000034501c244c420340c3c1c40d40a0342580781000800d40c0c62410000c82000d140405208004044000f140d5020b0340004000ca808465403501400400c100b92401d03010340411030309000c0b028007416410b0b0900d801a40284001d498 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 418939892 1250 418938642 418938661
    0x705030910091101051e1306021006060905011215090b03061302030706030c020309061206150705030f030403180608090c0405101a071b0611060f0f0a022808 69
    0x2d882010f0001c0b02c6408903401e096110f000100b0182c4160b601d003800b80380c0b160318080d03110f0304460b80c41075440c807114900380081541001400034214400388140304040c6010713405000020103000345810485a801321013480310381c40c2c200c03208030300c405640000e80c00e03611b1030642d000304404002d04d071280c044c0b0300120340e514010450390348110b0f030000c019100e103a20f0180268000c0824900a5096000900012085540700c80183c030302140100c4502d4214a03041c010130101500403008444429014482c0d2004104008191006806001e000360b03660307100c6040548181c02010650302c5020b00342100030640d01c0e0300c80102c60091044034101e070241200e40707041005a8104460b07400c0c05040400c001c0000354107a5007058400400a0206840e008141c0c80c0d0007084900b0121900740d00302c0101d02040303902da004945004c1c01120a0180a031420301068004458002510f52812004a00e01241d400c440c0c65041310001d01584410f1010555282d03038504d8511411503d420214051800003400320071b = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 418941142 1250 418939892 418939901
    0x13060905101d0409060f02030901200a0f0e0402070f0c140f21060702060f010e04030f0c0804081605090a090f030f0905150714010b0f0409080d050705030910 69
    0x1ca41d25542c442c03141140400040704410b4081a0740952101928004106548035801e03c124801e800941e80c0e00d0413450107425180304100014042d00c03426401b0926241000589402002c5850569041940c40710200c1e0030b00b484c0c0002d02e0f0b00910000d5840e00300044480c80d041014032801d02e4124041c0d0b103070788584c18114130400307045c3c02410024094160789410140c6400c40c080c052001520300b00000b49075807510341d08842d04405640171109001c000c040310680c9070700510b40c2418080d2140382c5950002c0c50360721180c500c20280807000d1810400c010751030040e9000b402011080b030b101e201000800d0382c00c4032800d20603035000d550740c000400da15102d01d0080c090f210b504107082c0010012595000c80300c15620079081e20402103280c402081c0365441958055a40207900942c60310380590707080c4120100001e01210328103070326001111000e9101c0c002041c2c04110215400122095a410302c91440d100c0c21650b0b9003d5460a0200001d050300600614051030801044403000364040c1c104c0d00484 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 418942392 1250 418941142 418941169
    0x120702190b1801210e1203090618010504030e240c150903090d030c061b1e030b011d010c080c0106060909020310170f010504150e06100306020307050c0313060905 71
    0x1d20703941141c41113040e640d070040050054100c08640c0c0800040080032803541050f9894030b159080304080c4800649040c140d0362060281034000c00190400c0da0303001e07101c00000310b1aa40603100110b03040c041640a01c50080a2224000d11155960091844180c03140070402d80224107440e07410104840c11800819694080d402a00b00b01c140c0455072400e541000460f40201c2d03210740c49140d0031940f62050b140b2285601c6482d1980d189076002c031800d82c101d201010f11a4410540740c9542d610583e0b902000072130811407c554058a0010400f00407140600c0b04d80c40540318480c00545442c00c00c005505c0501241c080380d40c1c2000141d03d4041010684c442928480c0300013440540a11800c8211120410715500a03011256200c1c00c2e21443c50a6660071141501e40c1c1c00301030040042c50301d450040c0b10f141d46c00d000c00392801e80340011280341550301c0d03400041d007102e0b408000104074038001c0c401c9a14020b03168049980b00c640110070702942d10800c2c020200003c0e200040007a080c1840c0c400400340 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 418943642 1250 418942392 418942427
    0x2030903210d09060207111f0e062107090f060509060a0915090e0112080403080304050a1a010f090507051902120703081611120702190b1801 62
    0x1941c500008662020030301c541c50011608040104881548103403240c1c4120030310401e00561182020305210a510f81d074000d20601500301d5424405201d4400200501c6007512401d1500703090701c6800c0450b0070f600940b1100129000c41c0101c407a03914400180c2c052240041e41d60304a025911503c80c030f4100c022a11410020071418003001d0628a0a80d01500a04100345440c0030100e50740c0f50300b56061207611b000c0a01140e900d00c010301c405103610a0503405000300f10495184035206a071074038842e1041d440301500e000800b0000c0340402405001414031160007808810071604c0076085c400c00d242081c032440c5000200c151000452070010300400c0c0c41080b098440c0350420410740c0b401072801207101c0040007140205010080506910009000032a00039038803110f041c0f9110061403421200c100155003400f0381ea041d002ca101c00300040700d0b01111116800103481781068404907201e0403245520340c02d0694214004a5030350300034006014030000341c43c2c824502000d2040156148111820f11009 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 418944892 1250 418943642 418943653
    0x209010c0b06010c0b01180b030c030d031109030307032a240e0f0709060e391605010f1523030d020c101704020d050c09040c060f02030903 61
    0x1060718004842d42c008410f042c24401c0f40351994034040c90352003d03000140c0c81281280094a6001640b04252940405030300920340a070600d40004d503210a40c0048100701911004403580c01c6c0c034413006684c40d404001d421681c4aa20074500a0301000811840341014130300358565520b02e14202c40348604842c2c01001b140c00c07000b20320301420f0082c205248242102500d510103070314001c17400c0084c00201d41c42d8002078152103003001c2c003650a48550741d0080e0100040f0794248030444051071025904034800f41050248201059000304101421002e0700802150200711940251030400513066010f100b070000b00051508000c134030703044880c459141d0040103400441400103690580440c01c55010a80b00350380b80c40c00260003e840c2240d07440b440030060b00b066005002074148507050354000e41003801c0c41815141c0310031005004000c0204040c1c80bd100300b5071075205000c4240808c1480f98401341505801e80303000e0410103000e01580c4146030004042c96600c41c0c1c054130100558105e880020080e20 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 418946142 1250 418944892 418944917
    0x18210d0e0304080f1501240e033c03190909090305130b0319020d0902030105190507050f070807060615090e01060903050307020906040b1003050108011401120b0c1e0c0d03020901 78
    0x2066070108401031030a04c85d800c50504400d903020040c1e410309184090544070600c03180b108684200701e50700c030025044007014954094002021081ccd81030411581214031200c045008111100800d0340d024410181c83c2012407401d156004c0018013a0800c0c030446858100d580b005004c2d810305c004c440d10100380e8400e00c075850700301d456600241211201440041072a40c8290006400c4500030307150100035401e04100d1101a411600a1036403284542c188107003007014051400c0c44a01c0b070000010504400058088200300c3d140e400b41014080f260081e402080e0300d080040e024601070b020744814400343e1000050003600c644002001d60703074840059410420030341d0034412840c03006400154030a456283c040910703207402d866400041810780d000308285d45480c8000742141d030818807890308008150010305c08840e00d100040da533076038040109201581c84000c1c86c562130080084141100402003008991440c00b0304c0a085904403c1c410748112000c407413410780407442401c2085012501010803907 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 418947392 1250 418946142 418946189
    0xf0807030902061b150f0106090614040b0f0d150503070612020d02031608090109022112040b07021c0f0f06020f03070818210d0e0304080f1501 63
    0x40040c41c0b016110505102840f0107003035414241c694070300b0041e0f03c161018902c0d104110144c58003e590b11000d180994144040100080344501030a418081c910445940020b0448104e800402203040550f446400121f801c8036036500101c1400c25a50812021841e0510440c0d1808100c0300000e000300740462600700203403280c03100128040d000d04da0034484900d401d161400198460000d0484091300300c400f02038090f08504001d000130656a00d020a00340040e200c0c09105200003803101c03c0c021596082003080c80c6042a0ba001c0d15808503804580000d11100c80c1020307080301442164001c454002075441e001415080c4800030b004046000500d0010a140039804040d15004900161520349441c035180ca0950040d156140090f00388000c1000c4480e40c25030792400078441e08041d00c2c401c0e021040c090501140700780f40500c603500008030a030a22000c1d602c2601040c00090659449541d24201c0c0d94a6090494080c0c1c030b6401440e03400000e030f4088200c12410b80b182070820f0902e00140040b40c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 418948642 1250 418947392 418947401
    0x61808100b0f0a06051b030a120b0d0c1401091a040b091804081206040b10030f0e070902070302011401150813020402120907080c060301090908040f0f0e06010f080703 73
    0x81c980041006075144a40d440307005003030000d0442525580d6985448802c00d560540c01070381d0300c00c00383e0010f21191220560000b40f1111201c81444082103070003101c1c0009010000b010002030124041c01070005900142c420b142130f13000c000343c076548030b19a558a4504045603000e0300c1c005007440304000902440c00c080d0058084080c01800340d50807503280000000c0c003a14280d9090711016400704507083c28005a03850194010410350302400403620600105850540703003156041455210f4000035a1210640d200d030800c0701c0603400301c440c0c00c0ea031481d41c00020741c00b0000540042d402d08150002241003041c03841d04851020000c891001307110101200d1580d0003038a00b0240ca0a075803501c030050781c0d850000e00390309250300514101c0c41c05c02c00c0342c2d90300e400c800f41d10404041c0c110701c0002445d550f80e0400d59044074210308000c0340c46071061030250300d40d200d40d0b00914401e40b0010030118088500c0d802000a40740c1803031050b0f035907441e070030010b58248066070f080c0340005082c074001a10161080e00b1 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 418949892 1250 418948642 418948661
    0xd0e0907090b03070309052e2a03020d20042907030216050301180204110d021306030e0a020d0624090c03050f0c1603020a1b06180810 59
    0x14180709081c0c4a01d0590410750083d5544000a6121500c0700c007481001d10144980c00c8207264100c0b18000420307180f02040c4207282100c2034031652000118a81202c5140c045440b130642259410100700541c00500250084203841e00e61524002c59a06030329803181c91130000c4c1c01c0c111034560070b062030300060710b000400460300c000031202c445182221000130039000d01829482a0090101d241a40d44210901c4100e45d020611aa0401860350700740400a98480f0001e03405032008140c004041c10b482070f09100780c00c02c02003540d2002541c560310891400381c81d000c2d56825602032001c1e0f504c2e0034240d540c407c90818080d40c000c200c0700c403080c0001c00c00e510401031031102102443c055035108840c00c1d0300000c554480034646445440c03415403070340e00d4403e07145e02c488041c900c6c0c803550401d499070015602481b242e240d846000342c0c4850092600070002c4c901d00691021000010544040c841c501161803445850003103150492503182c2d04403040315010580e515070700285040001c840701c05e005002c1000 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 418951142 1250 418949892 418949897
    0xd061a0a05040b0f070c03380a09020102030712030e0607021203152116080723060d0603110f010318030f05040503011401050f0d0807030507020f031c0f020d0e0907 72
    0x2002c0001b26444005c0c03008501500d0302d81c0d0844003c81034501021248020b44000200c8200c111040c1d8101c62040307030700701280100001da0024648010303071540c41104000f80140124000a9416030b526400c1000040300d01e100340c602d90b482d0064203a80d01c80c0170940c83c11001c201400015440410582440c412010080024125036460021280c0119110351000c0c4c00e5045562201c00340000e0038510401018807900400302c5602e05803204001e00c1c180c01220081e554100181e4003144d60f11801d8030503020038688104030707107950f901d801c004201c0c51111050054011054100403580240300c0c80c2d00b0344e40904100704031903140b40e9080b2204581e2980301014020305000100c0c5070b032024400d0071003048070181c48114a50418003041000c1c070000c0000d0340f040481c0c4070480c0c0021240c2d800c2e12811a4107041c42603c0c1c0d40c2c01d2000801800c0e102020580602c200c1c0c0c04408032115500300f103485040113441c0c90301360b000d88072012038a520100e0081130124041c58521aa130b230401c8d5500356407101031803 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 418952392 1250 418951142 418951147
    0x11060705030a05041505040506090d0e030a020d0303150f03020103060b0f1606020c19050f03090a09020306010318030810050105040b04030221060103050714090f060f04110d061a0a05040b0f 83
    0x96126130071031b8020f4501781c80550000040241c03403035003003085110412443c1400a0744868000c002039907200b12840081c05002e04d50305031800c06009400c0b01c10a44981c4600070340b942c2e01c070b400f03400c05040540300907400030703081c04400a0003103003101c01c0f1400e810420382a10320b050a0031822100c100c2000404079040c0c1d60800030f80e030048030144802d405019000c801d0221301001401d0061804031071401c1c03e03400350030401c000300e0160f0703c40c0c0e908011203007401030158a03a40e550300183c0051540c0a40b9201040110b100030040641c042000340c80380740c1d10f0202d2004203454170011a681d01842c0513000b0350030400c00040c805441d00407001c03038580048210360048100000b03210740c00e00c81d00383c0c81141c003640895010f00c89280780b14500a03064034140c40c000c4480c900036100312121200a0841800ba11412121010a1315250084805400815100d5603551310444003c0010a020720821a2052061b020f1100340385608084a50468481c0c0c0c03000e003010300344144080700347d0100c1c20080214004 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 418953642 1250 418952392 418952423
    0x30402010c11060f27030a0b10030c06053105150403080c1606030c0806041802150901020709090b070e280e0a05090a030e03120d05010611060705030a0504 68
    0x110f40c000d20081055030540ca0720351140003100d4101c1403c0118500c40c420070201c0a2415440008904c1d4a030751b04040c8291142d1070b424400c0411300d06941000c1d040540402d00415666040b0000700200101c91105a046426100792640900810315034000c17040080c10040106240ca40c40100f65100750709482c0d46001e0381c994455205511400890315517030080100d041100c04c034000f01000400841c101131010240001d0000e0580000501180c442c5613a01c5030383c005221500072039500c3c0c13540607010600c0c4016500d5100300540113008030070300600c2080004a1034a0480c0920300300e0980c0008250a240c0340d0000a0740d807425046c48960700019642e2403c0c83e16031203000c41076800d4810700d141054480c104900940003020042450340030b90304003028405005000203d800c085501403512200d4103080400283c1040c0e41c2c0040c08120200110303147c01e068080f98002412908940c9501ca0300c507101c4071130bd0740c4842c4219814400300d0401e20000703007607130342907044070380d1051041c19040ca61801 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 418954892 1250 418953642 418953649
    0x312050d0218041b0e040f06030f1a06030307080f03130c030602071101091d0c090a06080114100203040905130f0503070c0519051c0519060609050705030402010c11 72
    0x1066204030003820b245a109400c40c03e0074442e101560105034009000c40f0428100501580496000e41c4c0c091030f641d0800711a8682c2e030354040c0c0c02855020204840d1442d0f6802c0c4604c2c01460344003101d600f4955000400e00c00c0ca4000201c0d01100c0d4420490342c14143d404041507400e400041c10585400b41068171800042c031080c000394003441c8103d0006846400da8204800541c00c0c82c2e2041d0305101d4203480031311000010180883d091540120340c9a001d660f030303880709081401094906500003000d0131002c200b99170400b501c41e058038181048801700c1c00110080009400b4101290400f603042080706005403d5142c0065038044000c10400b42e0240f42941d800c200c02030314040c00e42d00b60b00081400410000082041401000b00311011030582045e0307054000c01800030301c00c1902c0740d0002d031596803211141c143c03041182e541040c03e0780d617100f200c00c004003030101c0105802c9803082c0c41c041c0302142d200054440c5500800c01655524150740c3c841d401502c8a1000c1001600c01401d003401e880e01c0d558 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 418956142 1250 418954892 418954897
    0x40e0a0212150109020403081902070509182109010c14030a030b030c030c06040b090a0503060a1407050c1504050f16152a1a01090c0806030a020a0312050d02 69
    0x440e0706008060003450494040707140c290603040302d1409030040200f003005c950820f0545000316440001c0c1c081034040c400e0143d15110840d400b0075000341c601e00401981401e6220441c01c0041443d040da044801a0b07608011883c041c86005400000244820000c6500c541038100b801d910440000c103500030a02c035403030703d507400036016680000d07110200142e141c202407180100066094004020b501c11100002d121070107540034400d0070000100d822151607541c100070350b00600d000340c00d40e1200e041880041d80a03140f501e003040c000c3c0c21802e01041d1480d1159003240c2c041c0c2a1007001d03040c5401d142151101c07180015200303858900c80c1180104404009002c01c002561050b08805041d920b00015600c00900300d0f14624103100501d80c10042d15103140c0440700e030040c081c0700d5030b20303500d00a86007410005207101d084e85268400d035400402e50411540c44080642a182c641d1045640c0300420590344110020b0029049008004200001403070302226569001d0281040390a040140340f015040381c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 418957392 1250 418956142 418956169
    0x7050a0905190903050f0315100804030c0602090103110f0c06010b030906060f012a030206090a1505070c140102030103020a0e090d03091119050406080c101206090f0203180106050d02040e0a02 84
    0x20344048260084e5241445940c0c0c040d0009d401c10060b14a01a00c0c05800402d090342d010b084c00760005a14070103a88a503008001aa0a00805c0d44e115148a03099840c641c01845080d02c0c1c0303109000000c6600b55420341603071b20904465000302015900e041c188104a079004035198107120a8058861004013901084001a500b80074414600c66103420024940f0704045c009501e80c0c0c002d00301050102e10014210190100203e0021905844600c0c0881c0c0500a08902801290344114040358040c17042d001107049900072103502031181e80b1a0201c1851030f03010b0340c2203099a400801e04070051402070f00304042041c001c4800c4044d050603c03000c290b031680e071031200d400342d90003910b410f102903c0c040c403d08002d40341002c000c140407010540411484503400710094142309500d1320031400d212040c1c0005001c0c3c04030800601100c01c203054a07902a40094625002144514085141022052243d04100e80d170040c864601c810098083c840142001040e005080c043c040f46100540c841c0c12405260b07 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 418958642 1250 418957392 418957411
    0x603031605070905090a11091003020d11030a141006060f0305060a08010609060501021002070515100f060c200102060601050c0109020607050d0f0f050301270c0207050a0905190903050f03 82
    0x4407209141074010031f611107446520444100301130040b0010413072624426a076040d60030b8080445242450346003080340036030300b941c5881050503650800911580c804081e03561038080310b0780481e85d0b42445007030790003901440000510440308140320612035000300e6041600a031000d41a20b0b2034000180c00e407443d5030080e607400358031108200525681080021483d81d1070000071800c0400703c0c1e48403504c409920042c0740c064000540070480700b04913818200014209201c001c2c03401517450300050035100e401c800659264105c00c2030b00821860010940c0d0344440146d01529050340e4000054550b41c0260498084665032992000c0050300c2d040300601c0d619010302c00030888028040801000b0b050103a00352010000d007240c860b02d03161b8005003501e0541c1c3c40302003505814113580c0784c0311000c003030303903082480c80b181c141000013030381940110f449001d407001030790580000740c1c4404518007560f4003661010500342a905001e080c82c0c415a00186c4001c3c4203281c1140382c01c0c40309210035440d82003690460300 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 418959892 1250 418958642 418958653
    0xa0c0215090a061727061e0f041109130818210a030f0c050a031e031103041203060f1d220312270c0905060303160507090509 55
    0x201c500c0e0000c0060001e100380d00c3d00504411800a810ba00c421014000a000c0351120381021070142020035003c40301643e0700700312a203515125007116010800f054071514513040300710100e03030342122000005109942040c0c000ba00701d0b940702c060284e4000000c203070030001138001064100040409004040302e000601ca04407600d50070400708502c20503603201c184203207001c074061000c0c10100403420780001609400c210280f4121054240c440c491034450013880c0c1c0c0501c059030300805810072500801d0b40c40502d041c20942071012010b5049500c03a0742105119001400014002400d11480403a162298030303003c0346413581d801d20f4003082800703034010240c84250030100c4141d1255521050b80d101d43e00a07182903829000c1c4160401041c420180601040540000d039202501142c02441400700000c01d42d40c400166a165100341810425044402c94580c1c000050107008902803280203c2c8004d000d036260a88031034101d04000c03441002101c60340101c45002070444110b1151504c030f007103c880a401d = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 418961142 1250 418959892 418959907
    0x10c03021b07030b01091e05040b0f0c031003110a09050708091c0c020d1407090213080c03070506031e04150e0d1407050c04050c07050708070810020a0c0215 69
    0x480c18100c00245601c9500c8101c040010132140c14034541141c29080c80080c410322800840141c01001c91403088619040c00280b1040000a02c0805d108250140c50040e464458036986804d51100762008032091000090601c0898107243c004145414018040c0c031102d540c1d04210380070745c2d034100da500f0081b85450081044050090050400e0340c03c001e03400d81005441c050700600680340c10480030b8000d1132140c140200b000283d400071112001e0507400c940490307544a188002035801482c42d041c042d400c0c1c040000f805640000c0001c40524020b004c1d0101a00305014030107241c00040040703100d4100c0324802c014400c8500c1e10320b4020381c042e01c04468034043c01100306003618409142903036140d010131000c2c607240317a0000c0d0051041110b02d8450395100328034100f6a15100a0018080d07115142205100142e66040d0082c0140346c85603084c0d41c6041d60b2a44030548611840c4502c0344280c1004440e005503446580c005c02e01072400d824028480d14054000c40c0036180301c0411001000300c000b6852 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 418962392 1250 418961142 418961167
    0x6030c32122d090d030203190f0b1203070507030f0f0f0b07080f060a05101101021204020a080318040207020a080d0305040302100b0f15071403040303030f0902030606120708010c0302 80
    0x1402c446a25120b400d15400c10440407503640346022141000c0541c040f010a440030080f0300c180365010111141805400d00d07859466008220400b43d0903c15241900306d054114004820381c0c0029800c180a4105545103803504244a40c018008545503207882003280c0001c0c03204101c10b40c405014084200c0a07140428024040040240c884c281e486101001c0218035a240034403d01580d1081d5601021400652130903500c140ba0000040d48a5001051580c10742c80945030b003502c100e000319882401541d41c1c0d04103680341c2c42548041000340e51211500102030a058004202d0280f015105940d15035031411a54284440465840300107a00d070001d11050560400c4104501c0c4802082003107000c4a42c400500454950104c41c0d0181072034840a00d0000149410f840e080c2e030b00a85a004d080030040441905d0fa4410b00086012901c1e024085114080900c50403c40f29030107401421301e41c980f0410020b011594400502040c41003800c0858124002c0c040c006001d81d080d100941c035107004181c80c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 418963642 1250 418962392 418962451
    0x703021902070509180c0d080c01020c0309041b0c0f0f1e0c05040e070501120e06130302010c051c050a0608010e07051e01051b0705061306030c3212 65
    0x71030384081700d443c0c41034254503c0400c40e402c1c50340c1d0880b10f98244001c1407400752103900540c500004194404a4180b040c090084010032119038122030420050400c80d00e90100248664010f00002d1030483c08400040d40104032501403c3c041c2e200000d0304400c45c1da9030f05c4458009103c005030012011941c6040242111000c800b42c10101c60a000e0825800a100c0d602e40f400e200365810445644003010941005a01880c0c007138000740280e6031180f90645283d4182045040704900642c6001e455500b030034030550030b84091459106145c0481d40804c00c645001e03150140c503c00442d940d27030500144003c824801d02d107490b200400640b0195260100b0496a41211a04101030350080e0840c0c0c803c40c0c6c2c2c1700007195180b10203840301907000740728005654a040110303001300340c200038000b5460001300c010890620840d14950303811b000c014903244044441041408080b0058030245400d00c0400200c40c042c1c110a06a10440d242400482078920201d40004c1d180c01d840b0f01500030003440001e014009 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 418964892 1250 418963642 418963651
    0x60501031503080307030b01050d050106020309030609070b030406020f13030b010807060309050c09040311060108010f1a0d0803090a06020715180317070903120206090705030a0201080f0703021902070509 89
    0x100d40e0745803032a41e1250046440010200c400f0580d03510900c0940d17038090303419580d0300c0c0d4010b13604101b07560711250040d40da0382c080403c1b94170921441001403c801000541d1009441107240800c0c21600c2c0c41d9154000394020a1005d0740308035080c8102c059440001d80b5400081d80910b02da0803441d450210712508107a00740d0040d00815080a54840c081940000c500d0a601c01c2900c0c64a8a55642d04049031500203101c40d06480340101800000e154605410100a51038248810440c90000d4082c0c5880c40480c0000c20340c01611890302c09001c122844c01440e400f898000c00d40d13440c088141d172620201d80c8101000c9901116101c011010a00c480c45102c1708442c440c40c04696001054030060440c881180190307444084030000120503500c01c46908000711b40c0314404002d5403c40d640f01a4807044206c80f1840e8a1040410001d96072a0004064100c0d50701a101e800080d21a800702d2810b1101c028100803e05408111810540c1c00c0040a003128031696400303008038a04100400406035001350 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 418966142 1250 418964892 418964921
    0x11030c01140306060c030706020a02010c2a03020102160c0f0501020601051c1104110d1104050a0902090a0b0406050403050723041a0307060314060307030b0c0c12030a06050103 77
    0x6442a01a40c00074003850151207010303080c586a80d201e00024505208400c0354800c0c9000c08512501048269009843e03040b42c00d80080c80302125501e4101d0f5121010626264052000303030081c4084c1d82d815000780c41050282c4009131424000102e42446440f409800f15403440081c82d042040c0480d003241c00029010910103400075500d0030000600302410b448440090030b1040000404004c1c88260f20700d24210b0140007441810036440c11706200d0b0f0800320000b020385040c400e0064498100c8000c0f14181c60004102109481c284003021000b90040e88100d1f41040b0034440220700c0d882044041d00040646948050b40d643c11440d140e07060101035880300a0480107040c41c000400c0a101e0038492101058800145900c581c0c41140380f036644803084240c00d40100d407000700d860342c2d042c2c002c80d8000008503034540860b02d60f00e041c91380d500040d100103001000c8076004600348051060007403a1728048807003100d440304403c91410b07000b58820703640070310f0103aa205410401035030035001d050341c00600d6a = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 418967392 1250 418966142 418966153
    0x80708030d0e0c030c01110c0d0c15020604031e031e05100602060105060a0c03030f06092f07240f0507081e0114150c01020d1401060f08060a0e070305041103 69
    0x20320101342d507504182d1017503040c000004c06841464008000400c04400e009040c1d51242c115810300103a00c1c4218001c1c04c081e61034840c03110818070f0001400e14040e0781e05546148429007540200340c05410715a83c0c1108068407612480f108c02c0c2c1006e9680400b2207540c400248506103461110a04011030b03110340d095402c18001000140d032101c06171080440c4604202410340401c3c50110000c00141415000f19854408003003843c65083d4003000c180c1d0344251400c0c600c030070203a9104200c3c400c081c0c1c80c212804820064403000408982c0300d80c03031040022013040d00e10b01c44440e0034000c1e180051030910f403107940c52042000069110f5010b507040750300c4244a2510400642c40440e08250501400c0c0c200140001918665150302c4100304040c0244501241c45a52600d00d09021350700a040c0300748040d04000c84c0464022410305083c3c105d80c10381d02c41001c0e4041030442a1090380740280000e52000c0c50110001d4054400c4404a10850541da030016403454189400d07031300d0044007445a070117039218 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 418968642 1250 418967392 418967413
    0x2b03051602070b07110603070908010c03021204062d0b0307060906080f0601051b150c0405031c0c0b0a0c020601060302040b090111010e030f0307090506090f19080708030d0e 76
    0x81840429180303d140c2c1ca680d5200c0908205052030050f480d02034100d5000010041d0703079548503241c0f4013920000d000034040c0240740d0308200e080e4000e40c0380c010600140d92011500041607544417000d6945054000e85400b2401e130284c071341003010101403125031521405a08043d150a100aa0140c0f0036030400c07000c29820400003c0041c54014492088207100c0e0700421220703070082c810756004800348020704170202d42c40030701c1603140c50b810f56580340d0511860f008a8101602c4c04d00782d41c180c0368060001c1050000e027141c8100b00d0400750f0340090901124061800c042803c60352030600c00d9010b113102081c44086460028a08003059100200700342c4140303c140201002c240c02c403143c8075001d10b0485004100c450301280108215041c440840c40700040800320421140702840c071801050300c6441c400c69898052103c3c500c1603044090f800f031050aa032100c04d243c03010711640c400940c101c9000035152910351040ca0b00c0b455030450304030781c2c0c40460000c036042954007138010050054005001900305 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 418969892 1250 418968642 418968647
    0x604033c030818060109090606080d050a05071505150319050c120f0610060206150108010510121109040f0212040803060105130e0105040f1e020c2b030516 68
    0x40380c00e401001c0140d004003203072034408110507000100b0850825100b60356034803c420b40040185060490340c40d42480c2d0005203241012031814038044d41604c49524201c1419002c0710603501220003183c80319140002c030402258248522403041e050b00d55104191025034007010315200610005900301070304c03202804000796000ca41c00030100e00607141d6482c9101d000b0407003810700542c0142c0500500c6090304009181007100580030860f83d894080d1007540e19185a8003c8401d6440392560100d4002c800400250a001d804241803034014a08020800c011000480c240c442c1044c81745600d403000300340b21205240900c5441e1141040d5482103240443d17120f910301d000d800040000c0c1a1072004000030b50203901540484607000c064106030380202d510342400c80f4000f00c0c01e0040c180030344c0c0b6280d40000084000d102c8c03801c0300c0c0d801c0b0411015640e465010b8001a40c07040494102e180a5290b05401581651420500c1c1c80d038645090f6903c40403c00300103007291001491165004407844603c10310a8 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 418971142 1250 418969892 418970003
    0x1050618060d0b0303070501090c1205060f070c06020a0c030921060203040201030b13061a030705031b1c06091b050a030e01091208040204050f10140a05060403 70
    0x32000d80d115525000c0181d0304000a0000c0c41d001c5070140400580541008410750004030118419840e010545454030520618147c880400421a038410008620400e49204800340c0c40620340c0303004c05000c034065490a0582e0001c10000c0080390180129100701900300c2d0f11032014001c910300012008110200f5401240c90010024051980c00408a403e6902c45d8003c500c803800f0181803008082d0001c0c8800000301807502c52a10030b442a581030314200e02a41d0204d9014002541d2800d0131070722034000c240b0904230f1258410148550802441c03841400c0c0b001e50101c6258400800035604e45400b4844041daa010644c8150f210b00401128400907006820784000c5003991a000801c0d04448020b9030040c5044000030748100c2640e030941c401c6e2684200300c24402c600c03c0c0e4040c0081c0e110010050922001907e000a00103140c2e60700b807281c07500e002041c1e00000c2000f400e840440e9900e4000c00d03401c0e44560070569807400a03080a500f400100021034a1554031150007a4046841a09545090 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 418972392 1250 418971142 418971187
    0x1d0403140a140f120f010305151504050619080304050102100b0907260f04050f061005010e03070f080a0c0f0501080403030209120f1606080108330103050312010506 72
    0x8001c81c0001c80c1c1e0403043c043e41e12184800b0422070300350905030001d0742038000910088400d072284820500c030740183c103880039000c0c21541c100b4154580300407042101a04000307050039000054414688400142038030345e01d0080c1040e04c080c50b9036505040009042c0080300b02d407904040d09100c04184151661402a54018868a8603900e000d9480c48080c2d2032900c40c02003440750302ea0020920155a50701040d89004d14070600841d9200305400364115141d41c0100c1c0c00b4421100c0850040004c0d501030034454041d40c000030181c030032050f01d55010134030758001500702e10550f9122998480410a00200c150050f02d08030342407003003561a1100003002110f005200808040d0007183d01521500d5003044030080c140b480c0190b03000b00903040901c90b030b101c0541343d129480e810b00010014130b00d8020030365641600d40c408090004d00c222241d40a040c10152420b5441e4880348035070744400c1e010b405502c50301951003a0003650340d9a26a41142d03810344c0c0e043c2c119900ca41001c01c84000300d07440296258104 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 418973642 1250 418972392 418972427
    0x12030307051b160510110616020a0b0f04020a0b030f13150c030507031d0a061116030504030302011b0f0e120a0606030b010e010501081f1d0403140a 65
    0x2541000d004110060324100e01a41c103c0c81103951500e040b444581d449000d60324151409076030003d01007000c480c1d4002e03000c40b8180a070032180c04240455110280c002d100d8415004480791640030f681d0741d01341c200044403a18440c1311201c0500045183c4031480f20000c00e2048203403400c508058030f502907840005025030305030b408401d1031a8104011201d00500c0da03450340208010400d860030015024103c110352402c0080d00d8165035100700b0700e00500c0b0000b84282c0b9001000b00181903039500005100c00c941910100805100d0011400200744103140320620a55507182c44519610b4040c2c2521401c512540039151480305161840c0d40c01030817084410a9450001030030315490f80400c841c3c07032510541400d18000d288440c4c0c03d00002c4c0e0040780840c0e03c030300a00c1c441a0f07a982500545810280181c5001400204c00b013060615800100300e41400113500541c0f030076036030746684c40c08000c1c1c3c070000000e10004401044149600070b445040303024064402c4a10786041c001000702864050a1503404 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 418974892 1250 418973642 418973647
    0x150b090301230711070f080d0e01090b0d05060f0d08041701050f0f0a0e03040f170706050f030901140a0f0b0a0b0405060f040504020301060c05060903040e010504181203020c010b1203030705 83
    0x4c2048080028030014030f11031224043d019207400080e40c0f174003401240301000c201f5070001e9403c154481c0c00014216040049910b0400110318003020203010b010380314550005c2e203000c003014070f5a100d8081440c59482200344070394880c5404c0020030000078030341030b2aa580e4502810090b440391001019503110b00b207a01008115620b54448200400c0316440e0781070144000303c0d020428a5450400f03c0c00c0e5450401210318280d01c528803255255414095100000c6041c8503d00b00640010080c42e00002ca0100200b402e968030861542c103850116070980081c1e44414844030711242d688108050307024160b582300c50b60f41c2007450309041840b4900c03682d0f000c7c07032000403520350f031000100540340a450010801c1d5517a59646500502c8482c90740c0f0152894042d00f408554038507000030440d422150842c0c02c0100aa1903d010000145035070151601c0d0314007030b02c6401000036803456080c991162944c034016281c0041c100301508407140e03450454002c84640300c4010741c170000042035030341c002d80d946411a07 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 418976142 1250 418974892 418974917
    0x10909052401021e1605030313050f010c0b090102030f0a0216170405040e0303010e1608010504021605011517010b0f10020a0c0b030a050f0c07020112150b0903012307 73
    0x2d103020541d0013a00008000312074400c07030044c03001c03030a45881c1180340703c0801c070700e901e4a08060300c1e440340b0303c141d0f1841c44401c503041101e8280b4001e03c00b9078040504100080c028103454484250b4011108004540d41c00805c00c814089032003151500004001411810500610303c003e0881c020350301c0180c10a81d4a1132482c00350046402110082d0001600c2480700c61001000140d90350000c2c016082c15080395800200b26251180034a0090445560b8000499203404140f000a41c006c1c65000034040f100c140400100d0004d0190500144040480700c40162911042c102c08592107201c3c007500342d0502d080c1d98100da8500130012200c0000700c5a1412030b1404440591401550001c010000c14901e400010381424840140d442941685824010f5a5075083c13813044001c412190005c0c800e40501c80880903501c81d16000d40394000d1804002485412403140705020308103075010700c50700c40c0d000503415020b007401e010307111521074030084000c0000c551180f0981c0542c0c0051101c01000046011032 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 418977392 1250 418976142 418976147
    0xa02040302060307141902100b0102060919050a080f0a031103100e09030403050d0c0b010909021003050439090911060d0f110c0606030604051b010c120905010909052401 74
    0x1c400180c4620391000074406c003090041d490710010305000c1d000901d8441003004550001c10b100e03125001c0d86001c3c110760070000c1300c50241044034010a80380c0b031080300d403c04009842e100c01051201d281e21807581e2a1441054010700343d9003400080c00c2c81c21001c2c804d10a88441842d08a0709580c103440c000e480c0c0340e80362640f540c03450085600103001441643d502054954000209440c560f010361248030490ba201c100e214291001100700039080001c40000d805168800d0340034540003440345200d40300040010104201e00d4102c07800a081e07031008008040b1080c403a0024400051081080a00030101592185107140303142d004403900440000981c05c1411981d41c4c4070303500070009000100300b5104010f050003d680c000c56010401481241c1c0464040c3c41d00040091051740d21200030038044c01e54640d181d0544240d41d2299040c42241540c0c1000187c10004020700489c0c9580c941038100d1070b001c00141581c00580c00381c0402454541031019040d502c4250001109405100f40b00d4201c006004 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 418978642 1250 418977392 418977397
    0x9060c01240512060408030c03090c311e0c0c0b07033c151a12010501050316030908040509130215121302030c0303130e0a0204030206030714 62
    0x750a24018030141507924030710400035240a07241e0554403101005000c007091a070302c200a80d0064003014080c000902462506030007142d011260030155280c05450001207040b0b40c1b080300361005155580b840c509006c1e01c07500d009040c0b1f5203070300000f44604690300c4010a981d012800d1801082c80d214240302550a0003051a02442540400e2220207454a0707036000740100351683c10b0040300c52a0080e0b50081c01d000c07030b400c0322025064a510300440c500b1010b82d1001480c2da6200154003400400c00000d4034500340400c003076640d40e101581a9503150701d001c10500107d0580015040c0042481440741d60311000203c00610726283c10001070603907450500511501441c1d000f107500000810130010080c101c041c0700c1041e68030a80c3d0f10b41ca0002c05060080301405203480e0b007800649004005071441c54404a400c8104d4006015030310a40050340200781540c2c840031005520030109401040012404102e040c0e104403112421404c2608503400500d40c0d1001800010403c019281c949921661b903008 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 418979892 1250 418978642 418978661
    0x5090a140112050c04091203091b0603051501020d051b030d05010603020901020d0302031504090f1707111503010608100f1401200c130902101d041109060c01 69
    0x40c00341040da51525902c01030340805004840c0c074014840f801c0080e04041c050840001d43c00009944040c940030700c114020680e140d03055840d0805420104c000318003948607480900b44503500447c8520340030031442c01112280300010b0441d0701c003100c43d4003255400300680d005410030302c4020403da201e1442c81d038a1801031182012145140500020b16640c042d0b00400e14060281c0a41c1e20b0143c40802c15401c901003200d4140c0c0c00b00030403078403600c64075099000c012128444ea004840c4010780c0e0300c2c0c0d0003c89010004000c0207101c001814800e2240e0f800810300e00d09000c5449a54904000019130020300042c8031700d0042c0201c1c08042004441c103031a5a82c081c21180041c0400c682e694800e4003080040c10058a0100b00d1200789000c040d840c2109805042d40d02000800c14603103180c00713012100c0c3d96481300140300d641e10340310040181c1d5401030300c0010009176a00d0034900ca00040c9552040e101030300f01d8602c1240b0700100d18222401c01420b65078000340860320240c80381054882140940900344 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 418981142 1250 418979892 418979921
    0x30a21021306110f0606091803040801111209070b12041110050406031d120a1b0605010e01060e030d1d0d060c03111303170d140103030806031605090a 66
    0x2160403540000c0c070000f0040c1003001c540d0540b24801ea003a454540c00c0c0c4480e50007024060004140d81c04903001440d4000d0351804491420369a8001203003100d2983d003a8100c0040f00044152008440040701a04100150081c024152400300d00c800b1034820100c000d000c900c8a4000101401078002007144c403000003405824046c4100ba0703004200342c1c4180107640c0481e16140700d41ca100a454161b87da801c1001000074078070007000418404554020038010300801c000031106800442201a00301409481220040b8032035050503c43d214012058101c0801c006400320031901540d400206090003104c51b080c01301c056039650b4140303040200055010798010b410070b06000c081201c0e990000401c0c400590301000032020074144da800c07501c6008c904183c1d0440341e207024008522003889106c10030325007150080c500b1900020a03002d641ca001d0030803102146110040050580041b00640d000904401510540c0e441c0c10400c60304075000e0085034050454040062504503c60b84042038a49811 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 418982392 1250 418981142 418981177
    0x60f081512010b191805100b0a02070905160813020a0b160b09071206020a030b0a14010e010302030c1209010e01020304121701030b0604050405160b070311030a2102 72
    0x8084079000c1c168221000c0e0013600900071110345902d03054074813416145003510100c204194122000041c020180801030300b1040184000b40c01400c0720001e0203549026000361401e94a0001d0b0300d811244000c0c01c0c1c6518400082c00c80c02901d41c00000316a00c05010618035080d09100e0003c00d060400075040446107120010b0743d00000c10140201542080c0300b003d0030f00c01d40d5940c201082d00c49040b071141c1c3c400108844944000503c403500034108400c2d42c0e150000308540c441e800144c02101c158001c0f0201803810f2001308d8156440300c11000050803e017415481c50038034020307454451040d01605c00544403002c0104d910340c5001c1d0800344036284010029916410541020000c00c0790050014012030801c560741d005c80c2c450a04041c2c1241e800c880c007804590754200c1404082d040040c800c450501409104000c103100c400740107401303000c031070381030315110f403410b2402410350118803400030001c0d8000e21800030f01c00e42c00304814846061490700041d02a28101940c0060700810401202e06c8051 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 418983642 1250 418982392 418982419
    0x140609120f12070c290c0f0d110c0a15140d0f0506090703050403121d06070f0216050a030f0c0b0c100516020c1002033105010207060f0815 61
    0x1800c000d014258010a0100d5a0301d945690070342d00011582031845c04a204510b414510305000405400c81e50b00343e034159600304540c000d840e4108501403039207202050901d140d140701440308000c8018107503804d0303404041690401003ea8500c101d6400318034200030310300301420b00503803007601545c801450300c40c8140720801002200300050b080460350b0301d020350192800904a94402e005050003941c2646480c116903c501d80854081c01c0d000420b00b8011489040c0d500b000281008180d1191182e903850b40b641c4c10300c2e82d07070013030900008020f5945100c00c4140140b000e5654240050301300c0e1340c0460b02840b800f41038a0400f403056280e070301918a0f400049014070342e500d404551512146600e110401642e6660703c2d148020b00865401500141d0000e0144540340c1003061003441c50340b466004580c207060b1074002150b1a1902034001014411003000d4220542c80418484000f8100c00d0003d0155942400340040940c8020b00312081000181e8022400c1206d46a0820b00096805071038850603506 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 418984892 1250 418983642 418983673
    0x303182b050f0f12060108040f1115030901050f1006050301090b0307050303070b01060906110c0d0611070f23060c0f0f030915010b1e03060609030604030c03020601140609120f 77
    0x100fa0724603044d0031000400180590320a400007889241d12156001030f46009842c2c05504401840c68250042a0401c9042c00103800c0d00c05548207501c40d80c00031a8901d4980504090220003410081440c441640107002e03c603001804c1d00d05641d07804c400010150810030001c0d1404042da4007054050200084030000d0042410a160584080384c4030350726526079a28080b00c40b0a07082032002001e03049085203100c1c1d880c0c05c0c030368062030170b0140901255211200c800c05000e68080d1008403401c0c04403034407440800280000408602d040203ca04062200e030800c581d840b00300041c0003a80040c00042c81c0071040710f65100342c2e03201c824020812a103a181140859030744901c03240710286031008090002500381c00c044110765032040c48006c00c101014401c40440320035000644485e82c8008180039001594170304100840c450740c0030f0760f640b010307401c0181006401d100040c2c001d105110940f514110a9490303107800c0f16803440303040e00c91258240f1a545140d04000c440d403480d80040c010342085080004 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 418986142 1250 418984892 418984897
    0xf1b0a120206160e1806030a02060d020d110f2b02070303020c010f0b06180a050d2d022b060501060203040f0b0c0601090e070909050303182b050f0f 65
    0x3e4100754040c0c040b0f49005040c1d80c0040c07080d1441d5409040c00c420700d4042d92a803010545c1101002d02164800105a800908150032100300d10395415408140540c0b240c849010b113050b0100c40300c10051800c0301c4825800032510913100350360640b000704100d8024150480d060b034240400706010454642046140080c007035440a4a408125800d001c1c54500340101c42c410503070102c40c02480c8601d85690f04105822100805158541c45241400e001070071b030702ca40c0340c81d006032841660340703002d212120405061004002d180000402021082100068a942c914240e07007044400c02d0307140030164007042d0280b12015410041c034031030800000065207600040034005441500000b146820f40314880301c940d034003072500002190790140004006910310342c3d11a55103c80401c040d0b640c510380b503001500079140b108004541daa0320010420807803c5150a400d0001004000900f40c0303030701030b60b012010700e0030f0704590503503207883e4680c2c2d041e2114010b9013103074006041c9603446521007009003010071203074 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 418987392 1250 418986142 418986151
    0x10051e1b0109062c10110c070e04020411040f0905040602070f050d08130b0a0f0b03120a03140103030e09060a2102090703050705040311030106030c03140c03030f1b0a120206 76
    0x1140c5503941c00300c2503130180500c1641c4110340001c0030401c1101358800b025000d10840030000786001c2042c031181c00800d01c08400641241e024541c2141058414403044030041c460303c003400101404148000d02c0755008920445506200101d440e840360f05021000f0301c1081d0f002800412440c1c13500d000c020000c203501800c821291101e1600d5540c4100d001e80700000100c00800341408400011680e1400c0c0c0d1203082d002c80c1c10341d00080c2031440600403a24041c07042c102c8103445240802c2c0c1c0040158540907280700741e040252a0f580c103503d0b50b40c0142c00c007032011480510801c404800540300b40c8400d5260002015024107109400901c500086480715140300182e0180309540001034140d4040d014080c094101c980d00c103882c01e85141c03107ca068841800320242d2554881c4e00000202d180a85004041d60107041c510481d080300c1d2603401d03c0c004050b880e10303001790004d1101a02c0e20b4911001e80b030103c00d0002c01900d4603882400c0842c01c107001c0e0040180900e04e515003000036551300088042c401c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 418988642 1250 418987392 418987421
    0xf19020f120703021002070f0215030613091704081b10050301030305090114040b07061803090303140d11040503010b0103110a05070f170c060a06050a15030e1b10051e1b010906 77
    0x2b040417400300e0038150700c412100543c00117403e403001d0707580142940c0102c2400340514014691030700e100280c0203465100341c3c41207603a688603c020f1040702d0206108440181002c94500d502211141c00162071400305100240a02402160105c40c0740d0041c58840e010703030444014544d07956191034030031007150000d10054419034a808014801000d5480803282c426426803144543d80740745540842e581e20f0001001486020103001c48584a2502d0085031610f88050700a0390f01c1e5418072040c50308546205000758100742c240180108081d8680e412140006040d00e4602e030354500a0400100f01c0c0801807000300b000d4881890506820501005001c0340341d40001a03442c540c43d440001c40589a041c0501c80c0d100c9188001000b94468503070071941c010050b400c2c01300340c07025980794031402c0820302c254510030651000e952100c03a2810400d00740310407400d418101c1c01c003810002e800441c8002c80841c01c1400c000058851115a104408410f507604c0035002840112602e01d000005000d110301030a09 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 418989892 1250 418988642 418988659
    0x6060305160b0702060702040506010c060204060915031506030209040e0a050705040b10120b0d1a07020115080316240b10030902010c1b05060f19020f120703021002070f02 75
    0x445008400407a2800f6800404881c03e028240d0204001801c0152006045c4441500010002070281c0040c00042410f51600c0640b58600a000e07500101e60314402401c040c07924070f00180a42c009190641030b5405841c0c01602c41c0d55038004a0300502c1c5c000c40c0c004451184003a1902000000604c0c0c40582c1c40a980c00d0000401200a21420031400c0740c81401045103688601c64a520580c0b0042c04003400524a035401c2c4203030780720720390301441e40c5003003081c1c0b180030500b004805070302401000529100fa888c101c0300c49180140c3c540e102d0203a030000c20940b440350a200c0040c404051001024115047c5051103e9489800c41c14003c01d5124002401201d40d0468250075900070b2048040c8260180c607551411001542d03051001c501410181540b48030102010526880700005010301c81c42000e00907507110215651180402c4401460400f190300403c640d1124080c0803807501c0140510000d12501d03003045150582c00d10440c0c1910b0a0f000d440422540700780b10480e039030180391a00903200b010 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 418991142 1250 418989892 418989899
    0x5040c0509030304060c030c020d06020901023003091212010306140411090901090b15031501060f111c030603142a0105090904210503070906030203090a0606030516 72
    0x8640c0d01522001e1545034000b13000401155005550010810344246465640b09405038005000c66821b800203607500340d80131401c0401560100142c007a291a8a6a56842000340d0342c40c02040c01c111481228a019020000c00c0407050100700c16140b1206601080340c80d240484a4040e41c14824030041e2800360600c040320724000354038400d050055422541c12110811004c00303101c8444000b43c800d10040d07507a1681d804c04605103214241c0144002429000009540d008151406429100010600190400420a480d04051042c1c604802d5042000808a880483c0c6007421402220401411140d40b441e82091f5415030000f03041e6440341d80c5c03890054171030070105030b50340452442600c045046041700755001c40c072640d035908403240e0500d44146440a40ea003c20311004080e1021034000c4404a20413100b10a01c00c0304059100903460210b040d4039068200a024003404e21800050560010205500324000c1c031030074000681001060044035500d151155840c42c0e40140d19606140182c00070 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 418992392 1250 418991142 418991147
    0x70e03150c160f050d020706111203040f1a0103082a0c0103020904060504060909110913060902011103070b09060a060810020309031309020702032b03270c05040c 71
    0x5000302400508203050070005036030814840300602c002d40303071024003c0301c4400280b82000380504c0f01c580fa501401c1d0311880e060000d4415503160001c002d154220180000344034041e10b081e030360f0060b00507424410021060500c0000c0c664003d40e00100409140004000d0002e00340090000c100e0745c0d40301d805806d0100d030b1180414800c25031050b0942c0c000e01a0b0444e07a6100ba0081e10002d04010400507602d9580c00000f003c07a40560320200703686448890342c50078000201081281424140c6110045140c10b201020b031f0710150030401030801d80e0b554072003401e5900c6001d0300c400040b00c1100322a40d48600741000c0001042c00c44a0541c0f03031207400000340c100006805035104031043d1600828540112404500182d040142a0b03c0d1500c4207000c030740c0841985450500092503e01e07001a915040c900525081c095901d00059508001c0d004800300d80141a405040a842c03524000640307496004244801c032080c49401c001c403100e991080d40030300200000a03070031224111820004ac90481c0d000b0b = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 418993642 1250 418992392 418992433
    0x5010605100e0f1207090c110d03090206041a0d050103140708070b0d0504050c03250902210403020109050105070f180803030c1b0d08060102060a0621110603070e03 72
    0x5070342142290f001e0381c0d00c0d421300304c607041d00502500b0203072102c144e01e811400d021540114034802c00121088013060400c2c006128101c090300c5a4902400341da00180c010032440c1c030a80c0f2400c4442e241c25411007146541940660700d4002503140c1c10b1002c0c0d6542e0800300254850100710340d806018280c0002100711000446108aa03040400e55003015038402c0b100006000041c810303a41e500401142c0326040d50244088131900504800070384800001a040c407022201541000c42001d10421400c1403104c003050450101d154502c019800a981d1490b00324094024840010003540c00c1c4000d0140382d0341c01445492814115a44901089145401094103007040d449095900d40040020902c8c45c00000b0080440c08c3d803200c004034444e4481078640f403030f00600707a8000c00080d80b41030a1040c0b56a0500101d5042001c47c4000e10072141003031580003003a04203041508200c0d41d03254910041188400c07580083c014000e003860707140e14280b100586140c2d03200c0d000c10310034000c06101540c01c151103401c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 418994892 1250 418993642 418993667
    0xa050603070909080408150106081501082e0303122a0507031106040501140705030603070b0a140412050606060a0e0d0f02270108030705060606090105160501060510 72
    0x18070940740340c04603900080070b5440054424040c10803000c40c6841c020040f03000c4141c514040b4400c550716000d8028920100507224401e00c50300c083c01c152031681e0050503183c01c61954034540f003003d94051200f0b42c0c0c0c800796000d251940c82c411031002041c0b64024850000c50b4444120501c00b2600440c0382c1840c54a003580c441a24010341e1540c4940b0b207105102820703106100e82800b04d400341301190384515111023260100d500369120110807084d5100717a440d440c0c100c1220304141c0d01f107041101c0025114016402030b000701c0d42c00415400c0c100c5205114180700c00004404441c0c2d91511041705103205143c000003030780c551103240003040c000d09010084034081d410079568000306103691020800610580c40050352041000a941005aa111aa040100100f0a2140f007580c1075003248100b6a883c142d12040c205e4105000080c045640030462a605c10000c41e2001e0f520084280140c500e801805404030307191940c01d1490040000550102c402c0e0b030740450303051840f0f8140c0002195803011004 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 418996142 1250 418994892 418994899
    0x1d090706091206180c0e0a0b040603020102030316020313030812130818180903070215030c0a1b0602160302060c0301030f12030906020a0e150414100302040b19080a0506 74
    0x502c52400305505a10025038082e5404480c00c0341152511400c206010540000042035000e00520803401d400e846050b1030802c0c00d032000d2203c00d2441d00080e4490000505e60300061480100c03405055100f80111600b84410050f4407000300d07101d04007a1515004100d00c00c006102803004114801c401c0700c0c001840d95403045545103480000202851804074455016400040c0d8032007610401462202543c4900051001191a41814010131040c070107400c1c05814403801c1042417016907000071003190a0403002c0c1c1840600202401e030503603541d1384a40030290a0a2000c5480c0030105240045642020f029a080310706d02d803103019000007144020b00c0b00400c0082500e03100800100a440c211038100d0550500103542d034450744030b160680e40100344d0b100000f8504100342e580c900c0c0007194401c5140004094a042900f04401120000201c0644038464040703044c5020440c1e1180d01182c000d04001542c840e103940500451074a4150421001000304113800000382184070184a0742d407103080001c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 418997392 1250 418996142 418996169
    0xf0a0c20011202120103080f0c011d0d0801060e0f0a17060f010611070e1f090213060c020603071404080109030905150c0c0f12030c060f091501050f04061d09070609 72
    0x1550340c82070923803001d03114440c140000e015a00358050b0070710800c141e00b6014030451f00e01d0000c0c1c0c000305041c98144c40c3c00b10280300e200c2d0014409241e103c011040c507400b00380c1380100c10048890010710b00d44600e50180c507100907a0800a82960b10104040d030041507107002501d080d07603e544043da1000000c010500490340305010400000c0700f400307907454000100283d92505586140c800318002c50b4641c009030840d513000580d0a0010354050071940042c45203262030856a03419500003201d503c07014001e0390400003081c6c24049005521401c841c0200342c030740020010f007101c501e4060844009e5114443c41080071031041900d60100e0001c503080f02c1c8044018000400101c0100701300c01c00c4410b03140f07401c01c0750720030305112180040000348600b15400e4010310492412100c003120003a0010306a0034180c0140d070000d10b102d07403210b00c00c40c107442d0700f19151005000c0038000b00b40144580d84c061405078011940070045118540c01e001e0282066400741c50941d910b8520558401c0c8007442841c81c0c05070368 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 418998642 1250 418997392 418997399
    0x3061d060108040c0e0a061a040b0f071109070206010f0b091003050a0e010c081f050d080d0f09140f0619020304020d0c031211070501050f0a0c200112021201 69
    0x240660720f50091040000f0318685071280007021440e00101e640145d0a55513002c00e210000110f02c42d0034805880ca030300507140c02c0c10b00d440701010340250641c000c0e00d4440070554100300220741001090903d07000d40500000e00d0b01190080d5034490a12030034903522443c1d000403072901c000c0c60031500701c42005003075242c056000da0310440091500070808503205503140100c1e0b049002c02e018030100d0790540d0362501c4090401800d82c51024004030507005e88a29002d9080040c2d1310351409081040c2e410a800c0c2d6100c40e156980600580740410200102c0c0c0e140c4000780c010444180b00e0642001410707000c1310159484050b4859592400356410300086150b6a0080742c140d0454000b103500900c00f4000d41c0f20519555035500d06103070740ea0011038144103092070400000d030b44003608011050905004102152070900003900034400c1c2c40c1e0034034491000003200c14526001c0c0d11890181c40c0c0c0b103500000c8901046813a520300851200f4100d00050401a405214a234a4001d45070540c100001d0310440741d28 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 418999892 1250 418998642 418998647
    0xf060302121302040b220b060a0e130209090a0903020c0108060a2702030405030c1b100305060409210f08010509070f11031c0e01090c05040b0604051f03061d0601 71
    0x82c000102d9010307844900380600c81d210b08210080d86007291500000070b201c900340b0b43c01940d551000e0907001c4c2d042409000109640701c44500130203007040d9140b0000c81c910500c4480648100843c86030040102d0052250200c100d40c00000681e00130760a44041e1404007004559026084c0c5166034000c1200030248100c0000580b800440c0d43c040e0500700030005a624190141c0c1c0048405417000c0d0400b04544241000510115010b0b0320382c54000c8000581c0d81000403082000102070710109a5243c0000e4000e454030703401681500d801c0134110307046050010895882c904860100c5002400c10104403602e035004401d1075060302c600400c003030950368810504075011480200404104000075650400e4010144002c01d4081e030000e80045031290020700710810f564451200d0b072450b0385440b1964022550040220042e52022a00801e003080d0400c0020218042d0703821281c0e0065141240c494850900b00d1212220041034406204c41540c8944045c3c2c2000c04d48070f000801014800010915071 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 419001142 1250 418999892 418999921
    0x380f0d030e0f010203071b0603050c0301030c090515131a0f0a0b030c1c0603050601050a03150e0f032a0d0c0b04030c060603050c03010f020f09010c050109020312040f06030212 77
    0xa42c184101c0f41040129150b481d0207100210310801e06542c900c406001540c0d05000c0c030780c2d0000880c214580365525594540e40d00300441c3c4650004540d83c0d901180c0231101a01d84010681d03401054240b80b1100c08007010018050344481e0b0a0811308042c8000c0c2c103040845a0041c141c0b00100311954242c238151040c80c103a071000f00060550001040207520340140034140d00341d4030a1003840011f5080c2503240061030084182c01003842003c58a5003000022a02d810708c1e11480d07030017540410400e492008080c031307100601c00e0000e69400301040e011481001000000b5440da0400064803541c010070f10744a0b01e6000d0510601c0c00940602c9950f804503103540d0f0660340092203071a0046000c10181c0f02d0342d045414680086402d40c0010003610384602d82400351040004805200314a0491800d084412600c51603405034107201504c5032030818007400390300200c6160b402409071190947c002000300b08035030190003528240c1001c55000710381c052191007680c0955052000319000c80d180c40781501e100c076 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 419002392 1250 419001142 419001169
    0xf0507150204030221010522030e010c0b0106020c1f0f1803080307030c02060f07090512100c08010314011e0e010e0114091905070504380f0d030e 64
    0x303400708000001601c0700400b5081c409030f844101141040c0c021170741070a50780044c0119024500c03410084249483e4007084001659043c10420031803104ca4ac01a11050503401014050780d504200000d03200e80c01060404050350122144044035420f489000c50800580c4110350008403140072900300c0c280903c1500e10316682c98401ca01c0c0f020307940e036101341450380100c0310100040d85440c0800c47c101d4040207481d0700b01c03403e9966100b0f0351504010042c20208540301d4284a000d0038421004400000c1c05559082d00c1142014049030150200103050324200380310845016030250700e26030700490103109072a0640e2009142d0740c0303035a05401d2580b0207004103a5059010355640c0b201000001400d21032403c0b0390900300c200e1180d500d000055a424240760300d205503401c003440a5070500151000c52047e094480440d0002a120b19080005a0803c454039403070824003240324000021740c41881b800b1894070002ca405041c01d404130024401864192200100490000a6407460915020100e41c407a03 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 419003642 1250 419002392 419002433
    0x121110408010e0c0901140d150b0405090109170a05090d02060c1009140a08040e0403050405030a0507050a06090e04110301230406060f031205090a05060408030a0f0f0507 75
    0x30161100741d01802c440c90310401001c280c0c45980100d50074188807144900506601c07a4440c101d00590021a503551380d410343c002d01120880c80c101d03210103030990000c10480d40150041000d40b4050642c41d0003401d00c04000e56a01e4400f91409070090300700c00c21113049102070f503152810810508180042e1713410129003280e2010052080500004040280c8244070a044002080d640003c0c2003510301042c2e458100b85494000008250200751180e0072142100c81c241107003404c90790703a4201103075030b8000c6800c41989405580c080e070042c4500010300d201980c07001c6031410003c6d5907640050790500c41d07620a001049010000207404607000710303131031000460007030f0000c5000c0319522409041c92409402801000303101405001c18026503108000140040540c60300141d4195120500c00d1140400c5940400070001204e000c2c2e52920707403403a070040101030581911540c54005680d103070b4103c846014002400c50103103000f0300f4401c43d50200a81060b44407039207011100d4480e00da103030007030304200c100 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 419004892 1250 419003642 419003647
    0x306100804020d1a07090807211b030503030f06180601111606031d0606010903080d110406050a030e0c06031605120c0703020609120d1a031005060f012111 68
    0x801e0b00c03040d5139604880400e41010f010300d8102c501400b00340c4980c006111540c40b040c020b0007a44190080e15907440844410001c42618501e06081c0c0812984558211091800c00000c2007042c0080554011507190060480a07500c20007440392015911003000030283e0500c000c203207a075000d80a05111181c0c5401940c1900080c03440380d50704089a070740301d000065641e415078082980c0c0c4180d00c110b2411940082c00490920701c0008050a07250300000d04a16030003d00d045170032415501c0031300b644105c2c0700140d4560b992880052f109402440a16001ca4103007101c401c44100c000c280e0408400e0010507150642d25803d0f40c50301c8540205480c2e4003448020041410b00c0f92510841c140704045404195a85400e0303858000d0401c040038002609a5004941450410003d0010388941420704100040d07100c0c81e11141d40e440c84110107141c1c0e018010b8107a403642c80741c0141c1029104000944188007101596001143c00b00c003054000750490a03a10b6942a42c9101d503000004005400da802c2c90 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 419006142 1250 419004892 419004919
    0x1d040f15060906020f0102030408042709120e0906031e16080703060e0d0206011202040b10170c070201080a05040c0806011503050114031b0a0b0705010b030f03030610080402 76
    0x1900e040c4241c0050700031440200c0c08102069040003156040100304c002582035041c541c1c0c404604e400b880c0140801e880d00700700200d0001140d0006e900d40c14103020800d1180d03000a00308481041198403480c00061164283c1100a0030009042c83c02024058002d0038041a11800b004507105c080e5140c1c04140031f0012582c0b070303810314580040e002e000000f0151920394518900384003110500729088a00381c2042c02c1110107a5008030b0b20504440900c412800442017501c00134009044880842e82e0201846040030a4190702542c02d180c0004030101c0a0450703102d60780d50260601070504001c3c00541e80c040040ca154610707801943e001031048007072116031500c500ca02030a10f032098200390542000c460b1034115296050040500500c088d424080980f80c0340c00201c0d4584000420070114041140e41c1c6070000c1d229445048004c0540640080e102c0489241150180841110b458480e200c0c42c8180340e444240170046a0180100a0000e0a0180e1102082c0c0e10302c0c00040050341c0c44060100e800 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 419007392 1250 419006142 419006171
    0x1080406061a04051c020904030e15030a0c030606020610060c0c121a070c02060d0207210518031209190521010c090305060c1803070e06101d040f 64
    0xb4201e03100e008106a44903402d0a0074080f015040343e10411419603900502009611643e802d5034209400d4640240915141d0010840e0705400d440140e6500c0c800104004448034242e0050b510b00700b180d034003032040640d02e91040342d58040580d2504018529208104a0b480c09149903041c894403c1440d0f600c00d0380d81c0c00300000e40006080342a45c0114148a07600d13502c844282003a03038844000c0c1000503000c411500400d4884c0141121066200e500042c02e005005009200000d0444800000000c01c40c0d040300c0280644c00070107070000348800000700044a031401042020150382100c902c2d5051504003000c100c0716001406500e0791001c107010001c40d44e9102e100c2a042c1844045021031082444680038901b12141580c1e07900800c03003160414000030300046056500300d54100905038560b0700018880c100322100500007641440740d060002070b0300110050446c03058004580452441038032840a035100c0c10b42894080c2c1e01208030034409814642940b255405140a01000503400e4005010 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 419008642 1250 419007392 419007419
    0x210060608102103050a030e0607021e0c0f150d020a08060a0e0f04030f02160305070618080304360b03010506010309021e030a0b01030b01080c01030c0507020108040606 74
    0x3500203000344041200ca4038416000320001e04021480c0c0d200c604150004514a00010300001d040010010f46181441d220303402540100c1449030a8422a0611001c003a52f00c0c140c5603c0c03190048442e601e074207924140802c1005003964040d0810440e45040e02c2040002158042118842c803414804c80383c98403254805401d1300340e0142c4032104603062040400051811701e601151400c1903003410040078102500791039401c00d034141051809001014070681c2464940d10783c010344807812041c0007043c0240002d1103400c1b0792180d141c0034810003211385002e44000250107240c4455108000400130040c224074003481c9060b4500c200c90250b5038a40d4448000808201a80d041540742d10b030b0b81c00186401e2003650340001e400d003810040e120307090380030540c00c4903840c0c403002458040706a6002603031418040b40034141e600010786c0c41c481d80c403407400c06083d503802e002e103404a11400e03003032001c254007030300c101c0141401030388030203007080381607801103610ba00020000c0718000c2d1503040008000d02c1c507448 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 419009892 1250 419008642 419008649
    0x206130e1005060405060d110c0d050d2a0c050712030c060c08011412011419060602060f01030605061207141302251403030709030b0601030618020a021006 68
    0x21039440300e040008400246105075000244101e0701080204a00d6039004111103030140e203110301082420482103e00424050540031172000d0007401102c004155116006002303035000307000104a200501304582611102c100e41500e4000e501604140e40075005402c0056443d214000f11050350f901d807024451403007198103003180825a0740007010204903c600940040ea0102d19100c80d8541c50f0403019501d126101810500400074298180d1900100790409504543d1000002400f03007060b500009602840c1c0e14104403ca00d40140800e1079440414040e0046028400c0780206900b103072a50001058082c0240b6031213803499604400c001410701804000340520890349142c0644107040c0030b01210129100601c0a20401840b810100038485007c2c0340c00e00346a01d84000700640c035122295003800d4090030841d02c80842040320050f40300107100c1c107503403003500e45c0320381512400c006400765860390103030200f51221a6064001c92845a01600c405c144c40d00c11a802c003100321000d242100d100e0740 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 419011142 1250 419009892 419009909
    0xb04050108060112091b051f0e100207030c060801050a06030605031e160b0d0c0206010b0a0f17090105040c080f07050f01140304110a06093515090c040902090c0304020613 75
    0x6d804105501e029800e03080035100280c2103200c284410305000348801c1c620800c1c42d20071840803641ea50150b10802803003001c0d41d44880a40c080d161158ac02038080b030000d12a1030b20880c00c0000100c1c141c2c1c42402040100c80c4094024200000b4840c03601414050000c4103840f107101e42caa400e6180c0e01c400345100010007a814429580c3c031040000d82c8207843c041d130030410640d4020001040f0041c110000c0340c0b80c0e50b00c03600d8004840c5e01d4011044507a103d900c0170704620403001d0001c1c00a00c040640c00303507000d1449034411442d01542e5009060312020300e00c42105080e00515010003e03810b0404803141103260514000d600c0d04c18410b150026600250b07820788042907100e012000714201561050080c000c9030400580840c50311000102050841c0003c1244070500f84d0880011011125640444544101540e02507000100d00d0400301c0e5040b00c045440c3e1041c0702c91400e89017030a10842c4415a0007410011695450715000039440d800500102c1c3c012408000311110080c3c61010700000d0007004 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 419012392 1250 419011142 419011193
    0x9060b03010f0f050601020f0c0405041109010803191b120201020f0d0603020301150f15051603020307030e011b03051803060403091a120f0402030a0b0c0d060b0405010806011209 78
    0x3d00104940009100d5815540000c0319900120130000b1985d014240458004c0f4541d45d0b58030300804203603688159290003604030030012900c403e021001c2c2900070714035a0598201a18060100d403200740303100c002100c0e00200504031004c074541c0c5d8911044400302e800090f10b000b640d01d5500c000d6601c20b000707407003980e83e8562040c0304502e801c0c05403500d01288188030105e01c504040c0744050080b80340c0f02d038400d006445880402030f540603600ba9184400d0400c1d01a0000025040103512607000d071004070000388900d5044070345c541c01084e0000c0544424030406030031402e0b603a800c1c1d03026030142c0ca09400781d4071468034000241e03408002c01c5111f94480d17034800e40e056142800c044000d8200ca04026242c0c4001d20050500c9101c40a9459010b04080072001c0c86480754004030341808070070358018005010718000c000445912200600101000c00400c0000c580d90303c1d5518544e000d41d01a040c001110300c000320b60158842c0c0c01d01c20702da0151180008405040d50b50f40d645545400c0c54041a82241 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 419013642 1250 419012392 419012411
    0x91509080c060414010c0309120605040b0619050d06110f07051902090f0c1606050108070902090f040203040201110d0c110105121f030b360d0309060b03010f 69
    0x14000304501d500241d5000e401c181c20540700e0145070108060b120b0401904070b00e0707038040c14410002c0c1c070000d040c010984003050b10784d41044400f4080440c5c0a54040481c0d0004c10001e0402c001c01f202003460304030010700c00c0c038284010490700200100c07064800c0c64890780e4903012001d0303550040a580c01c40c0b1802079515400d903c0e105040c00310f0801250800f284201d08080940c0b06d441071594080c03102d0051030355564441c0d1038025180101904005003d004401074020801164044e070f060b2050306084030381441d5101100b400fa44a145071407070f005060050080c070641819000381d90045e105040660310125000c520b946800f030002000c8000035448001e50090003107544041081c52001e2814a1a00035802c10359100c8500241803000c0a01d07400150b00414000003807400041d641c09011000c9a0405512010004d14094500342e2800c40c0e540741542842101c280f03a4901e9141c8102520340a28244c0c0c0680042100c10004c0d21283e403208080c28855034207100b000c3c01100c8800c000285400e4 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 419014892 1250 419013642 419013659
    0x902010201110f040e0703020408061006200a06020a020102091002100b120d200f0f060a06030c17010f020409140c09010e1c0b0f070201111e0a091509 66
    0x22034482c90302120701e003045810b00c1e0200103000c441c00e640031200c1503407440d16403a0041f4024451944803a00358052101400300c000c0d01818468215110381d5110a0202c80101c40c50480b5050141820015031110a10500040d1990090807070804d841c0001418810f40314041405075074102040801070b00414601366a0200074800c03101120302c1a1040021f0181c048685070361500280680c006002c030500395080c3c6031310049500e44170f0a8002c01601c0d01c018110142c542e4074003840030031860500070040010000403541c07191908403034021f50080880f901d00404400c0224114409400c55502c0b8510440c039400f850006100070a40034200143e41c100007030b40f407111003074040d12545071a6401c10150665a0b80080c420009400445203521441030208483c440844545002040c0604000401210007640c00344c561042007a87c00a000c00b4050100c401610700c107100d0b644280c28164603040103070700c04d010003500c0146514180002442d440302010a40000b00548440005040c0c1006114201 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 419016142 1250 419014892 419014901
    0x40c0806100608090313140307051306211a04030908060c03060405071e1407060c050903100204030218060409061a0315100e04021f02010207110f010c08210a0902010201 74
    0x6002005d1424034a1007146006846840c1c8a5100581080c440490807564207010342d0000308001005581080390f010070240141c0300922030544140c000c0c0d4a903002140320244486071256201c0201090042d410070900b514000c040e006a0070841e20300c9001c60820f108215050040040d416150740b00c8c45c054040209072030008101d04204030802d22800480c02c0a50f40c40c4203c0810b0381040340c2d112503501d02d002d030f0302c4c000c100000c2d00780c81c108040801119000303c0100540031050b800d030340d503050400c201907069115601c002500301c0d04c43c103041c04950190840f01500098018000700300720381c150321003205598031004000013800704540d02050318541040b01250104400c2d040d44014942406004503a112512420000441400c0010110754500d4131502c02c42420042d2021700825001d8001d0017500521412a0805840000c40d8083c1c544001041a2008140e503224840740c0241d42d0740110b070b04022800c07507030640c038411004100015440c00c1d034841c1104c80e00004d0201d140380002030079107 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 419017392 1250 419016142 419016151
    0x9090a20071b1e0608090f150a0c0c0f170c010207060b0f0109030309050d02041103010609090612050a030c231011131a0d09060f1a0315040c0806100608 67
    0x65120204048490f511034038460200d949a00380b41c40d0703e9840b41001818503c11340b02014041c000c1420024000b11001000c5029420f15441001204000e607001d0703c590050754406450415100007003070010766081013174080900c81d04002c0d0304107000603201d5400e98201c860300321605510380510000d281010001414220024a44090340c0b524548001c2c002c04460700810b030065450440c01415074542e034001003409448070361034558a60f541d03000101030400130300503120043c0c02c0604c001050401c1c0c50031030340410b03042005054120303c2e42e902524000c0c031301103040361400c5c07800500340182c00034030500d07024490700007015010341c0c107462a6080454140b44500b1595500901540d4144126174400c0000d9417034241410403005260000a1070758043c4100a20f40c0b542400031000c20850f06410034140b0302ca900720300340a070207c515034201004c07080d0480f098066110030700c0400a02003c0d07401c00c0c0c1003402103c0040c0c113242c8800b0540c0c14400100c1d1448102180690108041c641c00107445510 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 419018642 1250 419017392 419017409
    0x2407060e0d120b0f12060f0108070b0901200601080309030606030f12030c07121e08011802220816210f061514031209090a20071b 57
    0x640c18200300182c14070001c2001d00002036900c46102141c0d441e04141d607168510000d10249800709550b503030316030325801200d2880c40000c111000183c00714000682c14180c50100600d142003050100044803070b20340302c000060800c50340350400b1054910a1203094042d00b05070000c1c5990728440700034940782c50070240500b40640d10400c9604191200400c041d903c91500c1d0b50016900c0d00d45000c0700c2e103171303001f020300c0908000c1154500300c85981d002442149540e243c07455060090800742e0040d102048240b07c1e0101e405140c45180b49882150b03070084c20040c2103a0801c002e210b030100c200100d8481c0c26003100c00d0b00e90041c012100c0072074052078030390002e045002081071808856242907000000c04480100600c0500c440c180070040c19030400c0c00c0110b617035200c0251541d0764042e00009800004032403802805010054424803035400c00702c0d47c14090260203c00542c0b247c4584000814410032400104003040c800c009900c45190700070700115010f1400307804e41c10000075410035500d4541e80b14400 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 419019892 1250 419018642 419018653
    0x102090a03050c10111c020a1202160909030801180609020d02180a0b07030509040f051003030807020309010c290c12060405060d030804051f05040b0601030e15062407060e 75
    0xc4a000400c000e21422100c0000010181e00c0007e80c50045140c1d0010800d0501075202d14250350f00103401c25000940620107441999100401422501131045c007130b00242d842d900602101c0500c42e1182c661030191000015100d58942d00c0004a030402c210000016800240b200610a000d040015450034100d40e2008a00d182c0f0b00701e02e98510400500400380030340030982031400d5440750701c01c1000c110202010320a03882d1081c003810004006000480114000f0404a91054800000e0300c606c0b05068440703020141454807003003044103144803260308050030b450226000d00f00341c000c41401400802500b5807150116040c0b205107000040c100b40c01249810104642940c03075450903c44a17400d42400c840b16142e9040c05424054958104441e91101c2600140c0c1071009600803071045000d540d450044d80c640100440540305401d4410718107600044849818a00d81008aa0419801059101d100c0b4410000e18521840c107131220166a10100303040c418040b180c00f603840b10015a00182c103 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 419021142 1250 419019892 419019917
    0x90702010e03070f0206040f030b060117070906050d0204081903020f010c05030a0207020307051f0305010503010b0f060a090906120501180b1603020403050313150801030b0c09030102090a03050c10 86
    0x9942c0d004802c0003030070020800c0d003142c2c01d5465541c100c40c050403440e800032000c15200d00301a124a03c0554603c2c0c002400c000b84801035503c1c0c1442d050158440b50365030070659141c140111182d41040c2941480c071903003007200140907a4108682110044049640c50705c02505040180c1814100501290164180095600300e2903019040713a500001044005840f40500c1c004640350182a411442d0411071803204582070b8211141c410300a20f0241e50b003440140e80344c100f410300b40e405408e0050f4000024800d04240340c50900c0192186203002e25141d000d1698400c481d40542c0c54562140101400360307480c5200f407101c02c0c0540000441c1203044280c1d00c445c180d039600007810006145010905142d081307115600d120303404940045401030308598566001c6440302d8007102540c880c102950096490040c80707980600281c2c0e04032a0082580c00495460b80740c000c0d00341c0e000a2800340d05560822444186030b4403c0e0203840a9405413000301000c82c00c6000f0700142d420342d48400001d020801c900360 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 419022392 1250 419021142 419021171
    0x81b030106050307170a0209120a0c05152b0e010b030a0213020403052a120d0c020f131b0908100c090315020c10050c070b04031404030b0609070201 65
    0x160304403051403800e990740342e444641c1266003801560321a182042040c05116100c00c0b160042c081000c4116040340c440402122480d44c0c80c085034100070311214600d107081265240c0080581c22446804039618904160040d6010071107024420700340458190503503140303103001280306500d01000c1d501c0003000014400d5001076070301c0c1001d03c8001d200b4a80e40c40d00890f060b00507015030b002103900600f15000b40c0008001655803400401c2c25000e28000000c94502900c1d260300030f05500501140036001d803c603800d000700c0710203003800c206a8105840c8000002c0c982c44a594000d144040c4800000d60400c00b542900700303102c10802e95808010000b001448411000310f540c5124025403000011100e1614130141c5202c0495440603002400c922521a0001426001072005094660a0707039000c0354114003150071141c01307554502000e5409d110000c005085031108607001800786c10581c1480c51002988510303680076800403109a9450010300c18581811201d03150004807a0000b48070005203219807 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 419023642 1250 419022392 419022397
    0xb0606030621010f152d0b030c27040c030e070e18012307090b0702060304060b060309070603060f030b07051804020f04030201021b090c0c0115060c0201081b 69
    0xc000c000c07414100c02c0d0310741c0409500000c8446a0300d00305004455040b04800d4850f00070748113403001207005040c60f03a0501c01050000241d250103050901c1894201001407145400040a2502d44001046a012100040c3d0468035803003410807003003d4107000301401d10080d0766004070074105150400b413a8200c01400400ca00d000d45588603500100c90b074070f41c0c00112031413010662001240d4a40744500c81524441d244425400001310390700e111b5520360280031034002659210720400b000040c00000010302d01403005680041c01560b001c61004610400204182d000303a0b916121540200810008181c260003640000d100180d000034050f0315544880300140c00052401c410004005580740040300f0f88100000d421002400840d243c0c04e5404401c5a030768441d010590240c840e418a00128511040c4101e0040da005889046c003071725a030f40b90790f410350040310000d0302030b540703500300956508000d81141000f00040d55031842880c00500025184103c05040c181208805440e200340c02c110b201c04 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 419024892 1250 419023642 419023669
    0xa1101050103120c02030c18040506010f0501050412030e1e040e1b062d07030306080c0d06050615030c1209030a020601030f03050d05250203040825030209040605040b06060306 77
    0x2000c00765401184002800c00d4950705613223500c05082c170701100304180039082c0030b03101e1440f45c01140c1850341c80b4401c0e401d1510f0948245030006800708010301c0800b0003919015401031203402c0c0642c00d074444200040d0603070080b40300782ca044200c03802d0000c00d602c0c05015010401c5000703800740c81c0f2074090910b02c000c800b00d000b00e51400b6010000340340001d51103005425420100c2c104081c42e880031070b1200f0403501c0c1d220302c00c260002070400c040400c2407640815280d03400c40b40140801101401030307844001814000b030079243c2c4050f01d06504040b0100b09002544151a0114460f98a8080ca0303906d10f100d440151000e28141d006001080c3d495400041541c103603501709924822100300c41c0b400b00d42900c034082140e01403505000502c050b07007000010741e40a01000080060b011808440c0c12aa170b80503902c0358481d194006580350b801140c507141d21141c0b180d240081c0e01e03241a16030300070402803401a202100d690356150100405c2c4020200603a4000c03200701c42440c514203143e4000b40090000c0b24 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 419026142 1250 419024892 419024897
    0x501022b0614150c0d08041b0e07031e06170d091d060409060e030c0d053a1d06010f1d180d020c09010b0408060118150306020a110105010312 62
    0x24004450f1080007518006840607040b160642c200110080100805030780480b040301404039041c04241c1d8000c2050241c55a191f1441c40b10307910481c00701c02078032141e29904008507012070703041c0800050f4043c1001501103514514100070480300e0080c906500c0c20946c80801800715400e00100180c520952010444124600c0058482a002400400150340010f0145240c11444c512820b0080050300c1140b00d184160303488410084000d81c0c0c18440c0d8503101d42c0150301d0203600489501113850001105100c404e001e003640c81c5000090341219104401041400d0072190302c80b820040410445015058081d0700480d42480e1950860700e1450f000010b1080781042c6002600c007903241500390038919004803c440105004000c080d4554034890780c82401088800300214240401030102c50072607109070b004201f907a203003110750303e81d40b4461400d0b14007030364848c04d00e0b01444180390032440155018000041c1d40d0b1a510402a20250010942e0300e80f507410407004002080d203041c0052500e2100c4d0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 419027392 1250 419026142 419026159
    0x1e180303180f031c0c031b11010e0f031905040503070603090f0b04060515030309060712050705032109010902030d05030606220602060606040e040312090501022b0614 73
    0xd0940340c20050044030100c510f10021031315840542140040642151840c1020001d070514008102c040c4c80c1084000b6006036455241002e40610441c58845a50300010001039400e144440040c1011301c01c83c1c004c0240c1d070001c54043d001c03529940900e4112445414403e18291412000c070f41c68280921900c02459642ca0208041c002c1c0314002d140c141d54488203c0300036250510b4090010181521000b4a8000c004803412690600000f100c1c01904010045400d100321075444401c01d0061280060400500744104000210100040e080c51000c102000c1400030341c1341c00c0c0c42003080d401404544141e041c4010f20000d03031004100145a24440d00c0c00d20341d00d64555010905e10301c561149c0c412003030061400c00090420046455060b240c296080d190309444110030042640918010780e00320000c00c40100300024000d821a45401e80c403a00c02007049a010340b0b42c282244c10078003200314041103c0150703004075506d0b461031484d840d070070201c04c10126041103110020a801004081d0041d07211 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 419028642 1250 419027392 419027431
    0x120d05220b0a02031015020f0f0304030b01170705061603030b060306062a03070b060a0b030f0c16080c0a1407060203090d0515010825180c0c05061e180303 68
    0xa11400c5e00505800c64900f5503c0e003040c14020366400d1000218401400340180710002c490020003100c0449820280c1209140d0801682010030030b902c541211a600c902c41340012641c5031207001c0d1140d542c00543d4404621080c6c2005810369a201c00b020740324210030410043d1655901d019606a4041c40140b20455000ca01e0010308640c4a0640b8110503c0045808410000c4d07903501544501010398010110542c0e421450410740070a84401c86041c4164002801044d5120041c0c0072030700c0f8144070140c81c840c55071610003981e030210707203010034941084030362405202d002500004d000c920300000f400a1498904000d49a014901440d441400400c61a0040c41410082c2c0380444c2400c81d120405c0e541d4a100703d035603440c41402e42003c6664040407520b51a94100c1503442101c0359044141000f225004d4560010608800564240011180c00c00c020030f0040040610a820700d420000714150502a0414100e0005012070010146580300c00000440401900e8010400d1082c40305103c0a = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 419029892 1250 419028642 419028661
    0x70b0423101a030303161103070f11100f020601171e010c18080c04180b01151d03120a050403060f06060e040b0a0302010809120d05220b0a0203 63
    0x10000404140744034440c10340c45490704681c07000c1e410300300011503200184251001e0540300d010448510700c414848405146086010340d40000160710800c007540d00c5c0120661765041e105c1140c000585000c2c0e984403c4441c1801c3c4075104002c107130046d041c411864007108000964400050142d00c80c0003440580c0301400302c03400c00000b1281da031202a11031601c01511009030080c44a04004000502c10303888400300000200042815103100d40c01414422070400b0500001d400c80c440b03400c08400b1403141400106481c03000c20740c080e04020000341d007240320b000e0000f000c81c1000341002d915082c036407801d12203030307030380001d81c0e112801c9204126a11134030080400c0c0d407203000e42d61001d04514205078120803511919400f0405139040358071003142d003d22407000e100444000051864100b103001405001540c0996a0291301c0107145040f109190441c0100ca901900021244c40c5600e41710800d0060403498181c94a001e010300180c40d510440140c1c480c1c88903000043c3c09250f005500102003a800c04 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 419031142 1250 419029892 419029943
    0x30b0901150e03010f020706110c0a0605131e03020601050105040f0e060409050f01060e0a0608060f060609060a170105031603031101090b07051306032d0b10080f0c070b04 75
    0x42c020001c20030b0320410941c1d08045c0d4004802290f0051401804400c001c0140701694040442310f8001c1c410100380b80c1d603c0004280252681d01c844c90520084000143c1c107550b5180f51003112103a0010718005841c01078a051410381100341407240070b01082c403482c2c00300c20505080780c002c421081c2c0e0716142c14000c00c008003403d50020b00302c1c0c014403020f5041c415054009808850100503803242e81d40d81c00fa02e641c112492802041902c0d0440740c085041f007500c5c00d40164000100600103894007c0a00024013240e00c030044100c00301d0542d042c3c134603e4140000e240c50042c14140d0207440003041001e035030203100c00f05010090511540e80d00b913110380c1ca42540036403a03050703000020043da414030040207411a00032009134664031147c0d40021841902c01e0141072907030360003450303036807841c5001d8243d0f241524004003800a1007039490600900326550703032000d00f8987d00181c45407981fa0070101280340c07609800410500690104109490010f01c80c110901d61054204a43d035902c0001030b804101c0a1 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 419032392 1250 419031142 419031167
    0x5060a120609140108190305030609071205090c0a12021f030f110711040b0f0f061201090b03120f0a03091506080c010921030503090f0102070809040606030b090115 72
    0x149452480c8440f00c1c41c1e500c03098183d8403e08100e909601c095000c40600344110b10005000800500202d81e59040580710707603400c0112070400d1130940311451542401c48000b103038407003001d0b801030003111602d041c001d90081c06008510b891030300c0c131603080d0007040b0105040325410740c2489800425686090ac87c0d400b03480014260079090100704420410400103401400041e201840c030107402c8101e507d00391040c5440101d0207840410303441c00c54410051408511190750f5000b2008104c100740d100c0d43d6841c145c6c0601001d01c4000388404810061514091040c108210001c4e410440c00c042c180503401541c41049040c58049068090391500710385451074440303114400d03414074a02003034040000c44c24603001e1100385c0c2c4848078240d41c0c0d070b4114489901d4102014041e85023094a0000c00c3c4038800865001425608a81a54001000490880c0e02019041d5003c1c040812083c01501e0540101c0700248224602408411003000000c0c3d00d0700818450704007030440708080d00003100c0c0030f0346a0007a007 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 419033642 1250 419032392 419032409
    0x917120714070b18040b010e0306010b1b030c061b0a080105191d0415150b0708040314060601030f1a0d24090210050423010915050c0c0a05060a1206 65
    0x3589080500c0381005070b41318002c42d210b40c1c2004a040b40c0c035445070030070300408038004008242592030701c3c201c602c00b40e114940c88a03035884140d90080250340100b0007030060005000c0181050b00e00080da1401d140380c41c1c1000340843e1000c2111441c220fa001e43c2e043d0540b0720403903000104d5561244841118441944101403080b02c0c1c80c10200f000448103620303445107001c0c0705050890100c08076400700711000e00444c21030400306002d0901045883e50047c0841500c184240c519050b100e4942a4013440c80c51750842441c0d010004120565070b2502605086030942c40050101914400c0c440d1603200801100b030740a08281e200c40014002411807143d0300440d810700ca0860100c02c48001c0001c0d14141030243d01441c0d000c6c656001030707403041301120200ca262001202d940d081d4074216018081080440904003c281c03100441c039151043c11429042c0859210720707940360410a40b290510001122541c46030300d1041040105856510890344c4007038507440e101341183c92a42c1802e00801131600202c20 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 419034892 1250 419033642 419033647
    0xa06031b0f0e0916030c11100914070e07030f09032109080c07030c0f03050a080f040302130f0c11030f1e130501081506090d050109120917120714070b 66
    0x1e034500b29084d0001d03440c00c1e0365814441d218440400b0758107003c3c410382640d26035005c2101c0d0000c0e6403166001e0b81031544030700400901302408080c0716191000e1707034001c0214425031200340035040350944038444400700746030020321480203039071406070003a1070100c000006203030034410668491000b940032044881d40041029122544850010ba4552150004860030840c28a0108651a40b61485000c0700d074400005c0060158076078401c00260011040c0080110041c000840140e6a030441e4440c0d42640b0040000e000c0c01035603e0a0680e04004c00a070700340310004d088515840000f2040f42c0c0398031140380da03203a40c0c0c41d010036076402116101c040811a0142c080740c0c50802c0d114250050040710400d0343c444e00991280300751404480981d03100c0da03501640801c889034050030f03e1400300ca0621300810001460f8001904c507000384005883e00100012007a190600c03280c02541d000d04101801c4c00020400031000b5400710055100e42c1c0800303010800d020801009030768003004440043c09180507811f4 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 419036142 1250 419034892 419034901
    0x3020405270c0d1d072d05060a120f05040b130302120c10090809011713030e150a080603070b09033004030c0f151707050d06080a020a06031b0f0e09 65
    0x145c4400d1140220a1030041e01c01504101c0e50700e00025900c0c0622201800f280203140c0300030401e995100d042010280502114665981080ca118585400144d01000319440c50103180c510a031810062200101100c00c4240c900400d90002d1041c40c10000c44040741d80e030740790401e0020300c1c08100014040d00d203405d2000c8441007000c024084c180b489000c1c6c075043e1442c00c034038842044010080300da02d00d00c40c204c0c86621020900c60102078280b1a4003800e008411610380011940a9000c0b035504404128844140311050400300b0408005000500400d414983c51038006a00c401c0481a0a407100c03448424020b500c800c2c1011620b14038220090859843d40c0c3ca18107051100303842c0c072030b00c3d0340426141000030320f40581e00c1006d103404e091545d40141440d11844543c00816010f480241003040a0000c2c255034407081c0704000103002004001c241c205c1c0b40b481000300b50704c0103810580c100f42c281003440144120460403907030319482a0404508403000500c04070340258103c824590300552050601c07 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 419037392 1250 419036142 419036201
    0x14040b10080d050c120301060f0e19060e03160f05040504050c040e0d11070302010c0303090302120d1d01150314031c0504061803140c1c03020405270c0d 67
    0x2803407426070300d4051700c4440000d08802c039001c0c0400d204280c0400e1500f100110083e03c100c00d07505607840000c201040b200c2c50040342c44101c04140e00504007164590303411140c0c901e8100032480801c000c0b0710851008a08200038006d6400302440350078060741d00c0c0c502080421030305200310b1032043d8001e0410080000702d048010b9448610084e40800700788038100c1014451300c0480e031981500d8042e15000020000f80d43c02f06e000f015400000e9085025903011941c1c1030410000400c000d1005c5100803400d009501c0b20301d808418200124401c82e0316190a80080c1d00c451b1140404803174100d02c50400e220380e400040390940c4140c2c01aa41034a012003001d00203010f003580841e001d18001c01003001880090392083e010b03038244403006004101035000501e810b100d800700802488041c003040e502d006610078003440524a000010303001081d00402e0500190038030180c40080c0300d0301c2011440f04444255a00303504941c0140540025020003c0d0b29200707a490754210003511102c02580025600020307000 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 419038642 1250 419037392 419037397
    0xf0c0d0f081b070305070201050904050c0318010e0c010e03070b030124081e0a06031a01060f1404030627050703030207080d0518012007081014040b10080d05 69
    0x1000403603529400b0400d01075030b800140180100840d00d20303182c81100c1e00c050b20075410004040b070412404100b03080840d10780380030303907400307001002c2216450b070074074041d00040fa100c0014800420703850318502d0034070a14000340b0030866560a00305502c00566420200707081c4031450308103a14002000000007801c91322803446000724040444c400d60440c100d44003c0782d500c502595110300420340380e82ca6419100f01d40481a8100d1401200014a26603d503074030402803140c1303054407211410b20001080980d17000450360040f495a80f90060f0030a2000c0c00d000c00394095030201805075a619003494a00c0c500105a40559464008a501c0c2c5840c40d49840c1d60ba50a160100328014015100005483d0100183c0848140c001740c55040c2001c80004800d03900d240c01e208020304000103040401c035100407440c20303903c1111040d0040d0611a050a049078900700c0844a4180071500e0002c1070030703007480c001d00c0180d085335209d01400c0854270348003a4290140d0190700840308a000d80e41000c2840d0360000300 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 419039892 1250 419038642 419038667
    0x91227120609140d020d0c120311041a13051801030605091908090f0f1302030406061208040608010602030403020109060e040e0d0f03060e0903040b1b190221120f0c0d 73
    0x84500200c000750085075148440400200f07584081ca144c4c40088d4000d405c09d0301940d5103e080d883c181550340c000032542d102e50411404000e08006161004e81e0100441d00c0050035080d90300f0400d80c0e880080c41c5005a80504c000361442c3e80c0e5902040507020207010044000109510090a00545041456241e44800c3c12540301e0510010305004900f0854621001c0b480018050701c1540e1040c0c0700c20b4080d52009004075030903550341e0710101e04105486444501107000d00b0301e4135121420f010001c1d16403031041e001101590300034002040140e07801341c1520113890841c40c2481c040380420002c10054141c0c1c2c203821043d030150b020001d50655200340701e600511841ea8083c4641e0340d41781c01251072008251628041c80e007003007000f8010390942c60010052032800360221908000000449810610042d101da404641040601c10951404000c0c480e02c0c0c504151000035480b8110390900d80d01e40d0f20b0402654401c0000c0f0340c407201d040c2c1500c00d8852044000003903800c2c2000c1550300921070f0040381e4 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 419041142 1250 419039892 419039897
    0x2c01050a05091c05040302030106030b0108060a0204261609020315061606020c03071b030212011404060b0307091b0f050703090e0c040801091227120609140d 69
    0x2000603203544010701807a4025510100a4040c03020750800201400c85041025002d2103010400080180c8003403007078400450040c41c3c28a4654103007800d007030070010060001102e90780140b009100300900c403140c56004903845000c01d01d10340300c0310f840326080c0702c40d02c10858041540c46000045101440e0000c500c01e01c0032940c0190580c80341c07020040107002e084007801c40c400b040b040c2e0340001901a4014410b00e20341904aa080c140141d0300c412610f00140852000030009803410011030400040158000c1038010092180d101042404101e80034010800340200751a1400ea40d00d5071002d00c00e01010f0280448140441e5080035010340f400c2900d4001c50000075400e004106001c0d1042082c0d440d040e07896521103540c4c52034940d2281c409072024000e100040010000041c1a0310b00344601c1003050b1198803602c0d811040030b54090140038078080c0ba04507000840000212a20340c800000050310994008052030b002c0c2800d001e8014110310500400300a4025840c035418a00050407194008a95 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 419042392 1250 419041142 419041151
    0x206160c0812160809091024051806090d0501051b07020105030a0c02012d060b0c2107060e06010f0503030f030106080a0b0603070e01081b041203032c01 67
    0x200c00c0180d40e105400c10103458904140410341c00301c00d1903c1509290390003100001d00700320304a0000b5440481c2941ca03608407124206003001a5010a04104413807034003141d14003400c4800c540301800920a170207c948226a1064074000e0650b5100d0644a04c61400b606481c0b201d1014585a4000c080603190150a14030840304204c0c0701515004a03103a2950695580d4119203503210103030060803591a84100755501e81c50030010f0042407000845104040311001c4801c6210102c02c4c1d4116038450b004819031050801000320405400280300b1000c020321400d40404411100402d21a0300407907000404150810480d41250400002c0300d0341640ca080803103104050351003080590780d1040b9140172030210000d0004009050242c880507a00501001011514045180000c0c05943c8101c64001c0801c010b20400c40403540e0100110781d019554550b244540d91301440503903050701440c45410151310501c0d2100040510940258030161030b000189124542600d40040403a407004c001107a0b60341c0382 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 419043642 1250 419042392 419042399
    0x20c1518150408160c050d0803071d060901120908070c03120215040f140d0302190905090615040b0301030b0f070201051308090307170d09060f02280206160c 69
    0x2034a10755405294003000305844c0505062012540207148130058400200c840d0b40003e168076854460007811b442040e480c5e61b01d1800910140444800001c041e00320443d0701802c8040b0f886800844d030000000f400c02400350b02e400c80b0000080d01ca8510000c060740d4010408008000468480c02c003039034421114021540b10b002c07400c0b660f4142401704401d200e404280443c2c007181c110b04804001602801c0d01205900d04501041d00d011403a052000c0003035400610b40140c058815807020340e0140500d03150418914000c0000e00442c005400c0ba4414540a0800d4811144800445005201200c81e4075100d42c4e490800e40f01001c000c5800ba91102c0e60030001030f11491040c810588203e692220140081000f521880b0b510742281515a826204401d00850025012540d0340941000c0b500240b914030b130368480090120410f60311003024040d050701c07500388068021540705d0924442c0100d0f2440e4001d015501120700381303142000b94001000051092801c0c00c1d0301001c10f00c550089500d450240d6a = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 419044892 1250 419043642 419043673
    0x3050c1608030709080607080105090105010509010c12021c03020301061803210203090604080f0705120d0e0103180605040201031b05070b09030c010e07031202030f040504020c1518 79
    0x60565410800d812694500000841c40c5000d5900f1619518082001c01d85900700980341032010354000d000303e20340380300402040c03504520860144c5020304e0300c1c606040114001030920551342c0340080204007031100140c0787d0751082203814069010350600084d08e1115440c040c0c0250710a000b2080050b82145203425590103260310101245d50103c3c0800b403200162100c0d00e00282c901d0f407800c0071404200900c00d410381c4c2c2c44002d00007620390030000c1c184e42203802d4220380c0b81920039800940190f940c501c0c40b40c440340b0081404d845400359403c103044220f680e00e00480050104500f54035140d40a000d03000203011103a408240705501c00c0c0c130104035010141c00c07586001d9080c64004000200c00f003040301c000408200940e900100b220049904100241005c60f09680a85006540c2a0310440c0100240130000c0ca0710b2004009a001441c80d011074000120100d1159015041c0138580002c2c0c140e1901c001000210000408802400d02c00d0514911800c9003c5c800b81c1d2758240c0f4895900074040011 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 419046142 1250 419044892 419044897
    0xd05010801051e10180c021b010e011409030303010b0a08091506040b010e09040803190510360606030b0f03190c1d0f010806040b01050618040204031203050c 69
    0x9416501e450001c15282c8520901c43c00040a980726902960070000d01c044c02c032020300300300d102a2100402ca2148107800240fa01c10f406000400c11001051045403a903040a140d0300c12440a2130f198212070026680c141030741c802c41400ca43c040c03200000024555000e18040c010004665445000c1a20768040031071365140031703200c2080001c0803a00030409924040d409142408410f0404218501c14500007403407a400490b0b05a500e04000020045c0800340242a18050011007204004606125000ea40c00388018000c3c01d900d5007001030b02c46604080c910220040505c1d50101c0901281c03010021005000c1a10950303002c01d0600100380c5d40e0b40f80c483c1291513004005130050044002190800903c0001588191410f01401d85c0c0030410f0f19002141c205141c1500d031000c0000e080c001729900f403c49050340010031a82214062000081c0355000c0b6604481c2c045a8142e1070710300003040c014a9032500f00055502134400034001041003c0030300c0007010030f41c1540381000b4036035440b0010895807 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 419047392 1250 419046142 419046151
    0x3020109140d090e100906140906060301290702040c0215390705070305060423060708040201030b10120f0b090a020705070e0114030105010801020c0c09060d080307050d0501080105 79
    0xe07803844001d000380704c800320045900032500403560b90032a560360301560844010786c01c425104600014405940d0405469507a0081000d0360f101d451036140100c1e0380d903000d403100900d5000183d600584074a810450080c3c80280c0d800600410280554604c040e40e18121781a42c0b801d210000f20020b00e02212800071000b106401702040308030724a14030000803040107882d0103184109820300400c0c2c0410320800142003e984510001d16190800c0d040c40d040e90410100561601042030062094001010441c69000b5a081c107004070262220700c0188d0141140d9841a5048525540c1d0b2480d1590701403410312014000040c01c200e04070310656090140c82000e00c1040d0440c40c124003040c903800243d4010109113024406443c0415282c21200e108100e080e40803990104c64030785101c01d0340c9028895030b0b00402c2c6a000031032600042c80340701901c841d829072280d4030030004200000e4403619011060006254403110403550303803403c04800740098018200c1001e8880c50140081641c440520540c0d004 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 419048642 1250 419047392 419047397
    0x5090c090a090e1509030d0c050d0608010b060a2607090e06040b030a022101050c210403120e010e07091401060e0a0b0c150411180c030c030c04030f03020109140d 71
    0x1108241d11324940a80c40c043c140090300d100411400c0c8200c00c0380c0c418040300c0041da0359910b43e202d04119010040d00c50707035000800a645070102240d85690345008a40181402c0d04001031650700d0245500f00902c1920081e04500040604100300258807501440503a2550844010701d521281c050000301d030b0004000300e401d58011400360003d4a00b0181484110040c40600e80000000c40d190a0960f00250b81047e860a008200c00710115032686495400c1d240340000c8103940c1c039080e100240144e03c102d01405641c2d075200d1410031460b40a400402c1917428110868940594402400b0001c8c400e898002e0454500a00003007121032083d400d50808003801440ca4202c5070070700e1b1f42c1d83c900340e2100e44045080c1c4603080081d0b4030303903141400c1941320f00d004150400461201b6000e0128010580118400c1c0c0481102000b1040cad0300c442c00d60390030105000c1c12948070795400c0058025403041e81c10150055100c610b10808165054210800c024402c07800030040e044800c8e8401d69800210030790b00c5c007 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 419049892 1250 419048642 419048653
    0x2070807030509120316032714211e0303090d120f140106031104060210020c011103010f050411030105060931020d063002010905090c090a090e 63
    0x7080c8502c002d000b5142c0010070404514000b00c507400c5c9180c0c0100752031001c5003c1111914103040d0072804c2408244000100e504130301600741d42c1c183d02100180142c214480b10781d601440c0d580c0f60300c50780c08503080410f101040c0c440701403401c0c00d694400a000030001c60a440080c1955401c2c0401030f24061450b8000034a41e000302d544007a103501d429003501a11140d51114400090307002802200f0616085892185040d41450402015524220110b00312600204420010a90b00080e052010030445400680300d4142c0c00d01c0e10b0141c000744c0c4805012170301c08400856200070b0301010000b11407007120100881390a02101103554042482413507400038080c448801035007442910601640e0300480b01c0d000c002400e15407414081210442100c80c0c550100d03010500c81071030302c030b60001390010411101ca0866001c420509100c0049050055a002002d4200c2164011403130383c0081e16008021140394030b002d640c8032015811000c001442075503d40400200014540315072000003890801400 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 419051142 1250 419049892 419049907
    0x1401060914060d08270d0609060f0213030206031314030c01150f06030e0106090e0a030201180210050a03020409020d0903020d0f0813020a03020303070b04170405060a08060310060324020708 83
    0x1007140c50045d101400d1060b04003803501c895552001d8035200c03107200750800a0b20444500300340085a15030020140340c0d031f10412411844032404c1e45034004880d41140c03e03d0741c9a5410490002070411700000a1550300000d00e15083d9400200140c4000d41d1200e0082019400e05031108060000c40e01c06d01807140c3c0c80d100c06000d0030f84250001428800c041d000840c400d40e940c00701000302c5560000c010002e400006107041050f42c28090508481d1005014000a41050300083c0310a550411290140070f40001c5000d4518045d0b0103031002420b801004640314643c0110074030180201d218114010302981014030805805013580c82d00b074500135918040350ba525900c46181200d4800f20581c1d101a44150000041c2e0341007000b007000300d218040c1300156050910b0311031110107100b400841c00510600080c03003262a0041684d8030b402c507524000c4600c0d2200d00110742440751581c80c45460a04050011052000032030500300e1941c00c4810300100860b40e0380c0c4070800c07401203c00c000e000341c0c804c01205 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 419052392 1250 419051142 419051167
    0x111030a0b01021e1b0303030603030307200d0507150203240409051006030605010602120f070c0312030c27090506030304051206062e08041401060914060d08 69
    0x386070034806004a55441103e1800d05403490078000181c00c59500c01181c0d264032100210b00a840c4500640c020b60843c20414002900c03400010403034001c11410240c050142c22500311452070714130240c0d0580e03881032182c000c010803d07401807034103036205c0c00342804c001082e03041c0e8800c44c2d206802125003803800c00b04140075030004a0481d910700354042e031540d02e40c03401b00342c0521502903080c800400003c4c50341c2c90341c5460750917904164010025508000b400722079542d00e80c4111018030380e020f9240344d6500b00520b00803406500e0f070341000d8111000720440c0c100f0507825034440c80744510151203080c070041411030440c5880c0301c0500901001440030204102071031b51034001c0c6400c4100202580d08241e203070790200d05c00075000c0d0080e060681c003890500082c1d090a2441020030100f00c44015a480c960080b40b48011100c1e4200ca410014014000380c1031000003a81040c4615080d0024000319984031031301c00140108440c4e0980003140070001c1005803802808402d130090344074103442d081807031102c00d0 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 419053642 1250 419052392 419052401
    0x320030607080a020f131805130b0405421005130e01020304150e12090d060906110901090b0a020d050d201809041e02030c04020a0906110111030a 64
    0x3d80c4032084e000c0c03080c0c12820a400016110030804003458141291410803010085050a094003a24074584003e110f03a03d1030640702d540f2040d400585083d441c0d00c842c64142c0c40c1c041c505040182d050020980c00409241c492400c480c90360201c403658401c0111800c038170030900c0060b14800b8610340b07140f070100101e0801c000020b86814480100165010040c0c8001c1e0999108441c222910324401105c590417503201c0c07040c20540741d00d90f030042501a18983c8142540d2089001144c440c00049010404004041d008142c0160b48448144988144405800740076002008142c0c00b140e18520040f03518541e14095410300c800c15130007080203550450055074560b12030000c4206050b107031604040e04640b9400c041d0100301100820954660300c96407009680b15001071103522071041c24040c8070201b12070b00241c0350702c4952620080b0400840d0f100003840c08002010041d0402c1c0085604c500c12a0440c915070221005619460803601000694a00320ba40114400c0aaa1018004101044d802c2c1d4030 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 419054892 1250 419053642 419053651
    0x90b1020030705070b04180204050904150b030d0e040b041806090317010303020615010302130501050f090d14010b060f0406030c05040305100524031207031709010204032003060708 79
    0x6682c42e008180e12102e050501075000880121400201004440c20005081581d000604400c50400c0e081030300045812501500c05421510500e00007a00c181c2240c4c4110750303030403005089407010708160390007a24061070440c0391403013203203080c1c0004540d081c03a00407101c1604035000189001e80160b5503c3e0000d000c29078081e82080504c0d810b0411b00c41c0c101e245035020f940603030007c00291500008891540d2103141d111070416006214816044600d0701d071040a032402402d2003521b525144034a25014024164680d81c44144441c3c2c0310706000440d005401501d4100d00240810510401446140d00c40d9140b1800071040030442008000e1280c1e10101c921000c1e482c003589015039035203034149003504888816a00303550341c00a02008841d00d210b5450f91144030124201c00c003644000103921442c600d440c101e1180740015159040501c548644ca0400314110b013100c40604007110300034001d420034081102e901490000080911903140302c3d00401020003001040d9558a040c01120001070160 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 419056142 1250 419054892 419054957
    0x10309150f060e070809061302010e10110316050f16090b03210c06330303070203070609062601050d050f07061106010e04081b1009060501090b10 64
    0x120105020005407043ca00511803540d8000850a1401c0c8803410420050030303000e10300908100e41c80041c0d0308840c202d0f40c107800440380600c0032900014261071550540d026152a408009010b022800d61240342005450185c42206c20341c0600c080c1c001d696645020f180d2a035100349003020000c0c0a815002861020b43c0501a249100e1140c10004000b054400c0c00503410b40c4042070089101001300900c40d840f851000c81d1080412000005070400100c5441c0c1e085204406040c09007d07803401c0003201c40650f4041c084034602c0340d580800078101450360041c2400542c002803064042080d0140c04a0302c01c9003030034015540c1e468002001036000001000322407500034150f0042030aa800d02a18005141580395000c80c54094030790503043c003105070002d0b18146056403d21000c00d440d1341c04c0d680e42c1c81401e0b2039a0000e0740c0d2103036020700e401d0001801e0482d40c1c3c18000c001c010000d103a000749049840081d01800a00c000500700203c802d000c080300c800003006001c3c2000c0e95001c04003141030310103121 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 419057392 1250 419056142 419056151
    0x70912030207030816121e11150708090d03060303140c1009050f0d170402270106120608150c0315040e03030414030c0c060d060803030907050f010309150f 68
    0x3e6075508000d402445c950341c11020086408420b0241e440c070001c0d078400c89450442801c0c450500d04030406940da18020040100354240c11145000c10000c051866075680d281c22642d19200000404040013141d100d002401a41e070300400d481e019000f01c0058a5041c0c80382c40c0e20028080c2c0010348c41c6c004440d19183d074842d82c641c5071661032051042c41ca5071030164000c2c01c400c20b00038000c146000c903180010010440c6055480c40e2a07030300e40c09126041641151101c401c01801c8151400610115080c8200e030300080d8000280700e80c010038820940c1d8030b124010720240d40d94012142d180c0c00440304240c0e07207640000c0040c030003460f10801158881244400098202c02000106040750403c0e4075400c0306074000000e200601c01444821086504004021880c290554140030b40310007010380140d00603200070400d1402c445040c0c0202024120300d104894407868094102962015140714aa020309a10f2988856551190003440032041d08003d5020f00359400c07d6201c8010400007140d0031350142e44 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 419058642 1250 419057392 419057399
    0x50d0c0902031f06020c0d0609020d0b0c07050715050712180608060418050d030b06070b0411090a150605090409120c0c080a152c0a0507080105070912030207 69
    0x9880654003a02c141d00c3c0035140c11403031400c2d102031810300da0000c0d001c1d58840039081c681c40e0303185502010095804040410f81c0013039440031803064500300c50028100744140d002c01c1006614440509902800b5404880040e595117031003000400304800c1d01400030380100912004501c01449000c0c40064a1600d40c5d00120f86102075804072a25070010800946074406100b114030b090302400030040d0900102000c03030111640d609a070b0703c0d000b411000a258035030344184915a9941e094031100c0d904054008901c1c034091078100607841a281c2c055129403100300c08544e4492243c400e10050100b0011903096850514105031400c1d008024110752107602c902d011000200000d4152100c00826240c000d410509031070038440d502500d401c88802030744254121008030300301204140443c0c104010006a10142d0303d2820000c002c03448403590424002c00a0002800c80011078094060041c01640e91440e04c40c54014203031101540c560300007912584d001d20201c00c140710300c8200f09100e40111840039a4 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 419059892 1250 419058642 419058659
    0x206090a031b03110a05010203251a070206130c1205190501060501021b060301030303050a0207050f0d030e03042303030c0609061006030c02060a0f0b060d02030603011d0304050d0c 79
    0x1a0302d28914509605810b00300200610f4494203444007404440007598141070900003580ca024503015441704144604208a00c0008084414142034001c141d40019402590658903c004181c40c20001032080b00300084482e007a400b0089481c0b603101c2e0120300d466207452122551400f80d123205883c1400b40b201202c0d091200002e560600d14440c80000c120a442e25001a05048542c00400410480e8080d80c000960310482100e040d00d6141c2000506601c0701ea100c0b00080c0a100130080151050310390307600c19040000cc142d114620555400e00c644280c01d66107644070b00482c4201c000321140400e211340d04404000301e4010402c07000c0c0849050000b040e0000b840c102e07082d1541060750700030000707029104c4500381e18080984030380d007410f1081c6405000025a40c2500410341030501c2d030385420003165800e1980010202d000001c0c92a42c41e2903a05507210000d500035500c0074825864221005404010107660015031281d50b0055420b1a20b000140205000702c1d4404031641c900070200400e800d10b = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 419061142 1250 419059892 419059913
    0xa05100e22050907150f0539010f0c051312140d030b1c03020d080627061906050301031217070e0120030d02130b07240506010c0206090a03 61
    0xa001ca001498200e01d45542e170021061002c0c040b00c1001802d03520a290541c1010441320300c101c0841060340009808118070521030002c03240c220f99000c003550150400401500807041152049070104442507800c041038030540714104403207002c01007050003007092001280312040041c1c064980303013582c2810303940000d0416594a54503800300340e07140307048141c03418a561400c2204441b414070001152407074070041c0d601d0a05c007409204001c84c403c000369903038452034543c10610208814030030810300d801d9010ba85442c0220b030440c0c021440c0e050310300c2c40003c142007000112035031915000e2075030b401c588913107900e00082c480b9503050010a442a6100b40c0c801d04409116540356659122092441000144640d00b0030303066003500102d4661044504801104036090903203031050060f0341d4501500c0420800e421a1720110080c2702c041060403d00155442001203180e20701d50340750103610a036200c80102c0302d0030b8070594000b9112041c110b0040c24048010311981000034070054001d07a81340e54400700711 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 419062392 1250 419061142 419061151
    0x402040e040c0602070b13030b100b0f090924091e0a0609050901090b01180e0d2d020a020103111c020910020c030a060504210c020a05100e2205 63
    0x600b5110081101680c1071016001500b01c0340340051502d4080d208032440e0541500010346860100380200758000c18003040311004140211240361100d8020704052119001052014090840600096191480d03008040501e20399a0100d030b12801109040c0454190010a00451640f08010900500b03041c50f0f8142d101785005003012504030300703144080c001d5503000b03030042550341c1c10302c02d88000080b034400656054130340311602e19480582c03c0c25110080d101001d0554038038080d052a80480c0d5920059182900d4201c440c603070401140e01481343c04d01c043c280209001a0051b8180074015171213504400c0800c855482500d0914110303900e545031000700c2030101031000c3da00007540505ea081c2a00141c01000107800a002d2000303010000c02c2d00d61407a000300410aa6076100082d042000700c095414103411000ca290300d111038001c0e00600120081c0c20140d10910040b0700004451500107940b64401c41c40c0c0e900e920500b0b008000340a03402e00070443c0c5070503c0068160340c540c0d0b00c120b4030032709110f13 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 419063642 1250 419062392 419062403
    0xa0b03101a1e09100807020a0b0103121e0503060f1f09091104050a03020f0d0b070c15061202131e090b060301060515160218040b240108060402040e04 66
    0x6030101c04002d0070241c1ca032260b04510089051081c0d929a544200e002180c3e102181400c852503520b502c412418101c42c0314004114005010000c000c0c44940e040c01481c1200907181d8a030911354003003100c51241e991701c5801000540c1080098000c3c241a14903e04846c0080c1000d5011103090713040300d1107140b048030242c00040351740c0c008010612990240d4030110f103002c02001d150031300309000b00b00c010047c0d010280c043c4289010084140d1207091841e071886402c607507840410700344054000d02003c51001c06a41c17405200c1501c0300e50b10760902c25075040f9000740d006110a042160300380511151000085086250b1300e49641485040b131055150300300704052000540b5100c6850b044026220181c07005000381e140140a00950300e6088030700302841000c0101c50703240d4929006800c0b040f040d00e14025044200101c40244800d00c03000d00a000754410001d2039400c3d9121807118a40c074250072139460020071440b00440307165004107162030304840d01070070251400d6140c400500107568140c90450780f = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 419064748 1106 419063642 419063647
    0x1020d081f060908061006081f0305010501060201022d030402150f04060e0907030506061606140702030a020d08060603010e070e130204060912020a0b03101a 69
    0x840c54415090300007060746035980148080f21510640c00c05110300404142c0580e10072060000b540c20594460000741d82c0c00e0751a15004201c8400701d106c1222085020002c00c01c2802800e001e4003042e000940d0358280c0128510034104403c9444100f6242913004188030381d0318908803500280c04a803804130350120682001420b120f40c0c030b0809120a400100000e82c01c1e005684101e109004030f80c1e1501c5641d07442000c1c1c040d504200e4bd802d51100081040d1200d5420604481c00c401d4041c110000718000c1170511070140d0681691040003680c000b0595081780366040249210030151442c0c50f00300c1c0d01701900810010301042c0203080314201c40300b0000d0307002840f13170301d05542c00c0c1c030010202d074006c51000051500961143c054440007a08000300440c0c880c0d00c0b40300860025602a00c000d405618140414400ba000500074010382030b9a000e0024003a282c82c002c070f00442c3d0306004c0099 = true := by decide +kernel

theorem cover : BRFrame.Cov 418884892 419064748 := by
  have h0 := BRFrame.cov_init 418884892
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418884892 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418884892 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418884892 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418884892 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418884892 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418884892 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418884892 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418884892 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418884892 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418884892 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418884892 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418884892 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418884892 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418884892 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418884892 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418884892 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418884892 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418884892 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418884892 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418884892 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418884892 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418884892 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418884892 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418884892 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418884892 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418884892 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418884892 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418884892 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418884892 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418884892 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418884892 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418884892 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418884892 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418884892 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418884892 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418884892 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418884892 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418884892 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418884892 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418884892 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418884892 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418884892 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418884892 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418884892 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418884892 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418884892 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418884892 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418884892 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418884892 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418884892 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418884892 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418884892 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418884892 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418884892 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418884892 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418884892 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418884892 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418884892 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418884892 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418884892 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418884892 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418884892 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418884892 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418884892 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418884892 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418884892 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418884892 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418884892 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418884892 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418884892 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418884892 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418884892 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418884892 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418884892 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418884892 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418884892 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418884892 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418884892 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418884892 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418884892 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418884892 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418884892 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418884892 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418884892 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418884892 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418884892 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418884892 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418884892 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418884892 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418884892 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418884892 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418884892 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418884892 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418884892 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418884892 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418884892 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418884892 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418884892 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418884892 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418884892 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418884892 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418884892 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418884892 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418884892 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418884892 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418884892 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418884892 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418884892 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418884892 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418884892 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418884892 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418884892 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418884892 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418884892 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418884892 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418884892 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418884892 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418884892 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418884892 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418884892 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418884892 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418884892 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418884892 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418884892 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418884892 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418884892 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418884892 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418884892 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418884892 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418884892 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418884892 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418884892 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418884892 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418884892 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418884892 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418884892 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418884892 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418884892 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418884892 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418884892 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418884892 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418884892 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418884892 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418884892 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 418884892 ≤ n) (h2 : n < 419064748) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
