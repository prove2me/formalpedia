-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1018
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T00:51:24.174341+00:00
-- url     : https://prove2.me/submissions/3d6600c4-4c19-4934-ab78-3604c838aed7

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 182913669 ≤ n < 183093525 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 182914919 1250 182913669 182913697
    0x90105090d061d010f0608010209060403060c091a0405010801080a020a090b01090e0a020a08090706140a0507020603182401150c05030a08091c020a06110409180b150114 74
    0x4003840f84150598280103002e120203039555098a5116040c0f030181d10001c00c0c4420086140c03655070400300baa00d11440c04043e20140d2141e070b152580c2441000010b0082c0030740301d108401c1210b1601b9482459010b0b109241c00075640d8400810742d45000b0a0300d8a00d154000c210704400380c0307040c9190f0040d110f03080c01c440c140305a211000a89131043c1506611407009010010382c0d0b01800074010745440400350402205a00440041c01541d41103a180030300102120107040d140c4101c110100c48903c210345000350880c00c04002d00074070405c41d07107000c4541c9000d00143c0f44040d18000c00162840c4060a0300b0151040d84401080748410003841c1d0381e0f0706005498107005602c1e040c1c40b003030300c1c65000c0b003090000204060308001601c141480601a8150314661013031480e402488001d50fa0950101c001e0f00303440e51291200400f4500784111001000b948505111000d5915a42d02040022070070035604842d008002540d80c0c40d2103601c01c00c1958050311100001d036032900444140b50840000c0142c14 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 182916169 1250 182914919 182914931
    0x804020f03010b060c03071707051002030c090a06020102090102300304061517070902040608010e060f1e040b0f01080c181903050d02070605301509010b090105090d06 73
    0x56180d000007024820101741c0203561741c2e0101e15001103164030680100e14600824482d00e0001900030a180c8048481e203100503803030740c81c3c0003600e0101c0d202c3c0c241080d6118401000c0001c603103806401405038a0400d07026600781c0fa000c251004d410480d0081c0d04801d99810461501a141404014682250103600002080040d20134205103a00007a001800d41d41d41f48000194007810800450015000c860380075400d1902d03020014003282d0040c0203007060460745030000f403407a441c0c040c0c4c040720808004001a255860340e1805030303800c520001099009a0800d4424502800e00140003020190184e446022903a645510380c03a440c0c002d10003641200510014049140e51a07000107466038440c00d00e040000b61441c9421031034040340c05891010f40d0001d91040101d6608101540c00c8a500503c0001d403248119201c084001181206010054074540c20322885800c21016a40d11003820f40f150003e0341d880f441c7c0f60700c42d4003541e200c00b800148104071a507154207007a00c1c4010343d10721442c004945 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 182917419 1250 182916169 182916191
    0xe0a0510050d062417040b07020f060f071404030f170714060f070c11061b01060e0105040c081b07020d060203041a1305060a0507090f060c0b15010804020f0301 70
    0x2d0381c009074402100308a070b040c4000741500e50100d015102c1c1559051554070107192100c5c00d60003120081014099040300000280442d000303101030342c10354090301c0c291409443c1c800c0180f070b5214800e98580000440c5101c1c10101154000110340903650854146403a068859940864600c10802030841c09003050241c400050305201184940c402c503040a03000502c1c000220f90341484008000300d04000b09010314402142240e104a102480165401503880c2c1d4003017900790580b5000060004a0340c60150005061102d40300c48074182c2d101210144003c484a046c201ca00031030964240712020b012881d00380b00302401ca0002d0000c18400b030b00c5031942040a032150360480c1c100f1641075807050514482030315445800d094455001c4c0d40210765103440340d05500e42503a03c00005100c40700641c0d070f0300f012030305481c0a41d078024010020544541d50040e241c51009114050610007295541413200106100b00080c0c4103c58044506a44540640d96036400b04100c040a0349280c0c0e030503540e2032440c0c400b = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 182918669 1250 182917419 182917421
    0xc061f080a050105061003050f0402010c0809101706010807050a0e03010615020c01031401080714030a02030a080706050702031e1303150e06090303070f0c05070e04030c050d0e0a0510050d 82
    0x190b03029030300000391032a041040c000c1d5802c2d106035060801d0f103400d080003107030840c1e110741e56006902840d00d059a001c06140c6000a441a154200e60000c13000c0000c0712861790000018070040f010030915055502c4100055070891410345042c00070540502c8402841440303940b8244810500500100f04190769902d0f111202c6d540d5414040140c00c0031550001958150041600d90500e0400da0402c561420b03904030341320f08681c021400c066182d4036180150b941c2c108880341c0601d8008007595031b105464941883e280e0702516080b1900e6060000003012240003105a480700034000349200c1c0050f14820401c403e9601070b00d0050459212a6004004a0f0454107080032513031940b0360001e1014268500c079450700e14000c0450010307070700400030880d40b40d80c0039010900b030000b103050814200d90180b601500b0306003140c2004a03000c0c58030040105056100501c2ea0301c550090017900c401000800342100e2601d0f95040460300a82071050070401800c0c4144041004c05003491b0581c10f140060804038 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 182919919 1250 182918669 182918683
    0x304330905010f0c0201081b0f0c07080625050309030d06140a080102032205070320011209020d02090a0b03011b1403070e1c0209041b0b0c061f08 64
    0x1000140030302814010355812005003440c00c8450700703015683c000c150740007c103c0000288a15103542084640652a90b05241510009160120b1150319404007243d5255500c0481c4222203880c0705a03000b1502c58811200740b4425103800a02000e5203c0403010f0a491340e5002500302801c80c4800c1180106005039445010050103110f02201c0303211180d1810031901040a402030751007a44100309010b0605a15a10f0f60035000800400405505e064100981061429440a0003641c0d0100b11071710882007004503c0c2220b00c0c242c0b10744003c41106032480702185c20415001f500120361040c0d00d4054500074800a900141000740400c090030000c0200b425504508555281d01148400380800c494004004405081310316104a003549000f0900604511505031401e000b06546601001100c0486082c0711606401501d081414103003807400c1410312040d21400c1149071450b10b008115240142c0860706e40261100007002242c07650340c0c401e1150040001802d01d1741070101c00001e1403800510080c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 182921169 1250 182919919 182920019
    0x210f0307050304032a050715020c10020f0a050a0318080a0605090f0106032301051b0708040302100503040605090d02030a0810080607110118020d03050c15090a03020f010b01020304 79
    0xa94003440179440c1280c0742010380e03003203290441d801d50b8480c0d24180d80007a20481580c1c04507030b2090070102182c400d0742000c103000782d03408050041c1c0c0c82001c00e0040004038499624403d580701c2608603410448a810007843d0300944081c3e400401501c0007080c0c0c3ca0300081d400c032010384240d0b51400ea07030ba8119401c4070a16030007100ea6030142d2003841d1000580e558640181000c0304000d0050b131606403962003448210b1b04116500d0741c4042440c07001c0c440f0351001d45000d50707405407180b0719140c2c030b144028010b0341049404980719802d00b030000714131100110320760307105800b103400460030684144401d46604000a2826040485120001800d00e2003001510f0080702151604181b51036201b5920382929015030708000d00b0682d0441e0000142c46020107400d005806282c081e8031001c1c0c1c482841d01341042080c41c40902c0002c0e0040c400103520215503140400d01c0781d000c0707800e89245440300609841014006074096002444200b10004065503622000240303801c8a052900701c2e4132200e18648166501c03 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 182922419 1250 182921169 182921237
    0x7030e010c020d0206090a110105070302030d020d09210806010507020402090907080f0906010303090302010305090309041a010e04110304020904030c06020c0304060e12060c09030f030705210f030705030403 90
    0x304410158041c1700c1c881d0084a0080600700c182110340728010201d885c003020904204000481005040c8203005484503042404403c0d0744d141c500e0721241e0b01800340407409440c513254042540c08043c8811030032020408042c3c40c0c0102c15500c190044d00c090f0007401c42030740c10940800c40080165901a40144294038a031541c0310350b410200301c0c0141300c1c6002401950194005401840880e41001110007282d509190100359507a4688540c2c6c10740c01028240c03600310b401c1c54295144240c041c80d102d0f1102c5403c0c9d0380d8480c1c0d5440d800070403055441c60003805c40440c20130000300d00581415103001c0c1d4054001c1c00c103e40404000e0b520007040382c0c0407003020302c05c0341c00101e01401884e620aa108401b01341c106c40940b00250290100f41c0c491030043c1c4034515007200020f0107209078405111001041c6240c0b0103603038644513941030072a21500315940c49111082d491600a096840c040d040d079440304003a0f015282150b50722501074a040d403002c3c00640c00c0c01000b01400d144400884800500721240d821 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 182923669 1250 182922419 182922433
    0x3040506010905010b070c1401050c151f120809010e060f03040b011a16060e0a0302030d05070203030421021006150306081209091b07050d020d180e07030e010c02 71
    0x2c5403504071441078210200c00d01c0c0c00c01110b00030030704081011041e951022400640c076140d8000580d100c0c8140880c0d9000c9000f1410f8181c094407006081500c5400d8007618581c0d44900c2110700038241c100e600400104401100d020000b18045801505c640981810200c0744c00d500f0f040041c0668000f4030030000c1e00080082000208014220303854010102680a500f51a00481040ca510701845440102681140c24180b05029603a0802c0d403040d10528180da02590150070002c0d140da2040e842618101d0406000c074102c98400802c41344502e0704286050382e50311010758441c14620121102900710300c00c9584408003c0c0c22445a40000c00074070a03640403800c451600034064400c241c0c420f15150300000d035408030440c02c5004840150b40125410101c2d0307a211403003000880724030306451542c6540030402d001084800135070540751102503002c9a1b01100010700c21151009071850b881c111201c07003c020005400c0404032240c00150500740400c0d03410b22005003d0844100400350001648031074 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 182924919 1250 182923669 182923679
    0xc07060e1917100b0901030f0204062303060108060610050c16090c0f0206061507050307120302040602150408070303020f16030201050105040b041401050603130b0f0601110604030f1107030204020304050601 90
    0x9010f16102da031002800310b030060f0390015201140500c1301811017201c500e121011580c0b2a4400006004503480c0200d580d40407080449031000840c107100e000f0301c50240045651400003600512901c03008001e01081c450f41241194140c0086002c120301c0d10a03413020310740043d20310008601411601c5000644c01d900141b0090040030740c1800b1034259040f04007070082e1a20740c02c561780070761000e03c4601a034a140c1442c1035491403141002c05856089825120b6180c1c644c107400400c06c69810340c0c00c840d05911481ea50809205041e1801410850304101110009001c0e801401120075001c10440c2030074458155240200c44814007140140d55030801800b00e440c0500c50000548010784d400c00c001c0340380503502120494107003d8280300300c0b0084009402640701c0072012000ca03074410a0001c5504006420806119094440724082a1280c0906a107010006185445180c0540d145a08401549420351305591015540d243c140110203000c80582ca0302e000550080384540c5c01001190300d04 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 182926169 1250 182924919 182924923
    0x101503060e1006090510061124040501050f01060c110f0d0605040312020906040902130f0b070302071203020a060b01110109080d0b011b08180d050307030201050601050c07060e1917 79
    0x140c0c004d0780e9030b18a80410301400c042d4041486050b120a4200b402000d4441200c141c64808140340b49440300b2000c01042d008001007805840c02984500001d001c551120060207800550034011240042c4042e100c040200781045030400480700050489100140b014000c82c080790210707a01602c00b15107520070f010400d0740c000c00c40b4a03424618201142044031200002d00f451244d803155000807600400e1001c0340c0c86903440f22030020316801d548031030003d56501e0004266005203e00f030b005409101c1000030142c038181142d0021035030581c050000003220356641c00041020060b100d04018804844002d45d00d024411503450b02c2c050b8080d5500d61181d41056400d841002c40c070710741045a20341c000305054072030324180c2c5145503020000d6a100c2c0356519151018034008207800d81d105002482d8070051090110090a403035000e0350007408299200001966244504051004150310194003007100503ca80c419205005000304926000c81c000c042c151120481d9070003078101ca121009182254800c1 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 182927419 1250 182926169 182926181
    0xa06020f0c01090b0405040f060b0a1d04060303080406051b0a030b030f07061e0309050d030219030605090a021b070609060809070e010b0304030c0b0a050a0b0a08101503060e10 77
    0x903e0880455410700d03e12089a006602c1b41074011611042d1007c071541d400e07082140544142c041c8240c0b41d9040748002481c11000c3c402c41d0341507003000140502981050b0080c80203894050b01d480c4059122507540b035004010091101071041080700b240301e0300c0000d050003001940c2c002d030f801107211a114400c040c24000a040094015400500100425070b001107400d0701000c2c071801e0107512408110026009000304032001046402209292184c454141e4041c141900030100140304600e8030f542e003581100d200c0d000d100d41c05540701c400142c800300c02d070700201421005500c0040e168124500701c03500e0702420f50070410200d440c0010070f10515520695a5900080d947c00400703506240c0390031544110b4040c02000c1d5103040c0000043c0a1501807a185076506500c1110301825143c21024280101800d8585803d03907400e02c0c031588910f02e03005103030b28160346041020341008050340120100400c2c0d13480805a023101524400404540f10340302d420001205440505444068144140c3c2100e907 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 182928669 1250 182927419 182927443
    0x101b110907020c030307150207020409150605060910081b13030c080303040f140304030b01090501080f0307150b010e0603071706030f0c100e03120706050f01030b0411220605040b01020a030f0813020a06020f 90
    0xc0500a14215a8405006801d00e04b410304008401e6102d80056091428504403a005140790000d004082c5082814080c400c80c0d00843c90091003644881c0f4403500c912042d80d002d04000c031180c101c2000308030a40d4058600c0c100002c126841c003070307803a500d41c1c0d14008264003100001d40d8800042288076800e00581c0c07105007005010b1403030185169101800b2100040c110754240b5511001c070501c07a4003884040440800c001d010a4584c03421140040210342045141e249094032a004a01c841c200090740f90032100d501c2c0064500c10140000b84071500d15111444000c0040c01d41c1c0b02802e5441c02d200c80c40d03120318003400e456a110414140b420039a940900b901d880616040300400210f07040c80e4045420a0303120000e03000c91016003001501007907001d00c00004100002281103c10782956100f00b04899040c1d40c140181460302c801680c0350852208050041000400d10501040c415007405500942a111052090017a500031500740341c203513000710300964813005038085035101c1003050f403410070 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 182929919 1250 182928669 182928679
    0x151503010f1d030924090405180f0f1e07030c0b0310050f0904110f0301150311090108190501060b0d060e0a0506030c101b110907020c030307150207020409150605 71
    0x10342d05002240c004502128174201022891407088112400c900c100c0c2c4110714010400d200a0030050b60b81d6034002d52512404100e4484e04802e9030602001290b81814001202c01a2105c440441302c9050401140200003005002d00040840001d5400d81100d000c1c0401446d9280c592801c4211140c0100304c030341195120b0a40c800602d5034642d1007c44081e171040d03100c10068490800c03400401e110b600d02103400c56055003889292001c2c8080f22228604031303401480a01c01d00f54041043c803042000c28007805070190071000c0366004507a0303004404844c1a10880000801e030756200030030010b51b040711149012403600c510303081100c4001e82e014681c021a098504019034145100041c0d5a27440d0381075558081c0d4455248071004c20300449030003207042518084012801035529100541d0b1010410b21840f407007031000803e0300240300007600804100060010751522007180c035040c08028000541c02e0383e683d0200a13900050320750740a982d8459104050308115102e4030f80702e078000e5682075006240a0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 182931169 1250 182929919 182929927
    0x1b090803040506090d0209190b06090306040f05190605010f05040b01021c030e07030c0305060937080a020a050c0f06160606030b010602060a050117151503010f1d03 72
    0x5640801260210381040702c405a0322010705000c030b888141003040281d40f0104903000c000001904120320740d003130312000d44200a174500c02020004c60340140080e0540540c801400100040c1110700f04000c600d008004803a4180300301040c0c0100003842010071101c20351610010402516560401c10182c101101c040c0000c400c4040000e544040d4203144034502808010142043c500960140c0e491002c0c0e182540c00141e00e81c00c003150010a1072104407020300c03035040040c07035070721000c03c484d1403820300d2080021000c58400003c03e03004400c900ca500151420b01403c000240850000b0004520f094001d1f08205032907041181c10143d0048409005100c44920003000d0b0303982004032002240410414182203c445c10300c00300500b140d0b040202a101a0742c000316049400040e4280b04406005043c401070380c84e0303464202610301d0112030181e140c1c41402c00e4500e0f10f0002c040c0076806042d05000707420b4240c001c80000d0a4551903513900c03200721380c1c8040f90002042a0040c00a070100207400442c60 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 182932419 1250 182931169 182931179
    0x60904081206010504050402070c051305160e010201140a05060f040507020c27040b01091109060a0c060e060c040303021219051809010605090405060a140609030c03030403061b09 78
    0xd14441c4050035044141080006525a8003c0040c0c0f000b421014008544411192a206900747c006009161240c6000e21102030a6515409078601c540d11002841c1070003c0002000d44500e800c1504680c19035480703c2c04041e48180c180a40c0d403140f18071800c0807805003803801c06d00286049541410707000f18103080401180b1500080d0640032041c0035a101243c08101c4c0c4080c1c00c07144202e4945a01c4030711f00078184000d1042010906059551240c4108003010041d901070700340b44200c020450300030783c0c1800003898150151f44443d4a03d4081c55000c18807a83c20715041d400e0540840340103000c0c80d40810b09006042d4100440c0e6500301c224402c007490b085070801100d04101200c80603404100b000103240b8051304456080c0400b40e00e014106a00d071756146c00d03010304160851205140154a4400040c8951401282e07883c00c032002420050802940355090150713980c0007140350303600340c0308405040a103628204000e00055005500016031138040e900d04201044c100c450a80400c4804101401 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 182933669 1250 182932419 182932433
    0xf050f0a0c110d0e010c0203070e09060108070602060a02090f04111908010e0f07020a0b10031118041415090d0908060405030306060a0e03100c08010504150312020102040e04060b010206060904 84
    0x241681c450600c84141014000103c91021b00140002e405000308507000500000445030b0601900d680c4c030540300790781c1e01c80200aa40d805c15204010050344494003145550b8403503401480f024a0107002c4149105c0c454000c00c1c02c0c3c885c40104030402e404000b03485507840c017008000042203600c43c64002c5080d450708500c249014800b5004840d414100400314004500030003902c000294091601c2c1c041e17250142c0440050380382c40c4400c0d00d103902e5203c006561440c00c0003190000e0406c0035071124082d2035030307110107110080034051105580319034440340340d140144d800310521aa6860000741a00c02c01c031a0024495545a8090f158691200c820701c0006180481034a620041c142c400584071075041c90200c48941e002c101007901806001e030512000c1c9038030303080507a0038689601c807510266680c00c1880100e40c441301c40e02101e0700c0c00b404140009484000c000682c005284005420300c0c0e00d850594199990650741226041e6894010889550301807040c0341d8050b00c02c5510890728036064a07110 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 182934919 1250 182933669 182933683
    0x1709090411010219030206040b0105010504080d14040f0b1804110301140301090b010806040303050907290d0501060c050606010c0314090d120306030507050d0305070305030a0f050f0a0c11 82
    0x41c8641c815802030716099100b0405195034102c0003424580740720707442c01c010b510707000261825184130300700000102d500d500550031a802caa000400500d07203070203982c40440e1207000e008480c405800081000050031042d1208440180503070030502035549590700d20080540b1001c050080c0164101825091460725006c26a0704645150342c0c028098450500040e0060041c400010418140d640011443c2180020321603c600e1207924104026110388400343d070b03242a10b10074802c403500c0c070035400405010034102d141000503070111241d05080e805a080c1069031801d03000040003c84160100050100030000103410035020f00308200d09251580340140140601c16034020071003030001b052291078079918050080c040c6c0258450850407080e550040140c212807005072414881c005000c5850700c0c008040c050b8480e41502e40c103182c45480d0703500303981540000b81140401595500c440c90150141d00503180705000303581e003d000d98540003a0340003c540a580c500c1c000c1000c80c18030826840300004030303030b = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 182936169 1250 182934919 182934923
    0x4210203060402270f071b0b01050607030519020d02070603050708010303110f1c120e060105090702030c07060512010b030709090509031c05092b08060409020d0302070317090904 78
    0x350318840c444d450811981d41d102080c803481580360401121402ea03d600b10b0003480c01e07984085052983c800500340c0e51041080180419503902d00400030352070f0200060800911901b003032420100040802c03500030903510300d85000360308400040400513a041c4411000317080070703040c10407850609181c024204101400000c05001141c16803101c441c20400820a20303c0c13030312080740e0b8541d02d140045112012a01d560902181a2404e6039849007010300504e60701036121001000c40da880c100409c0b28083d4003402d03200a40c002002007501c0a4000d02011000c0c140c10340380c02daa50300c00400520320543c0164002217140d1014814480000e5000d0340c2d0340d044600700c0d0004901600e440d007020f03046110751541e1841046000c0140010020140c0005100380c080c041613405045e078000000c42d500c01c5000c1c0c400b0001c21100f8411507802d01a184050b00701202810000703511003994089111a15907110550150340b001c0410820003248500c140e641100a4070814101300e4602c0200c0d44441c806000 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 182937419 1250 182936169 182936179
    0x70305030a02090d0213060f090e0615240c0601060509010203030a0f4208100903020a1a0a0b060a020d030f0906090f1203050601120b011103030c04210203060402 71
    0x181c0c3e0140d40b95904550115001092001c007a1450900d44000744000d114855031003075a04070014824501d44a42109012002c0280c245a960205900c020900e20120580d02c020b10101c090804610101c4807403598502c14500d507030312f0300d01185151420005a200c2c0e42080b804002c202d1207a41e0201c2070382c0e08203410401c003080801e03000008001502c2e00751000c08102032000996816a01c400b0702c5500007041d0324000d44141d111542e030b00c810510741da019040640c0e028007429601400a5030040d90342d1406441961070700c00c500c0e614620321000c1d2030240380c062034029080c4040390100744251082139104640852a00c410410065154640c0340300c100281a078405400305c1d81f05154200810055001002300902c20b11071812030f0846520480a0712030300320302d800c1586a54041c6c07080a0207424143c6400c1c00801100b00001c0140583c0320b0b030541002402c0343e0741c0b00301503010806140244650308906407141d0403ca004038041c4131040032003c40f01c0000b2182d00251700d020034240e070010f4045d24 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 182938669 1250 182937419 182937427
    0x8090c0a0b0703030905030a0f03060503010b06030612030c01023009250e0a0c021204060e06070618110f061626040602070302090708090c010509010c020901080a0b0705070305030a02 80
    0x401303800400003054041c0690000142e0502d03400c5d840303110300403221303001e1301c0400030281c60300141403c0703c1507004a550060800c10128200f403030f19118007801c00191008030703854108042d1106081ea00710322a015440c0c031204800e01e883d607044489803160343c5048a00c2440501d04050f01c5a603500002c287c002e58001c2030244040c280007500d6046000d403428004d0385200e4103003400a5002855a0200d5400500804102d0010880d0840403030707085501a965a07910010304404008055100c1c0000321a19560740c450328914442061404441d54000c60384540700722801d00c10700c0600075903511200d2044034104a1360f41241105005030056640006a43d07140410350b800724000c21000e01d0352080030380c2d00400c000038442e600003802d07020369109440814030b58440030825140410240c41301802c5070400d0f03032011503d51155021f051030400524241c030b40c011140d008207091078820b03088080c4580050400340c090282c0c0c464520741000076494405c0c9824101d0302d006050f8000130b060100400e40000d = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 182939919 1250 182938669 182938673
    0x60607021509010c0215030106021501120615081b04180b0f04020f15130b03070c0f02010212180907050a0207030b09100507201609090204020f030103080a08090c0a0b07 74
    0x2880c48030059800340260402600c1c2e1a080880750f0002d100710001842f608841009010b00d00307002c0c0c0d0481d4041003080c3c1a56100307540e12030280c14480341c0e800b0f0100d05d0307820029600341300300000c190101410012001c2c41c10030b0300911055840228805c05a000088c41c00c000103800d1813080e0340d108140402c09001900d49100240b00c002400340b0160f84040000071100310b0040f10002040500e0015140e01c036155503c903600318840c0030442d110008200e98002802c0031039494120286a244140b0698038040360000000d980d40d0803054007126601c070740c0b032200c1c1002d0a080c0303401508500c95003041d60070440f901d00029640c80300380c04010030001c01c11012410300d4000b00021600741090400030700c2780b80f070030560007000704010303199219200031015410315602c000401d01240da1010304140c104501d0a100026024044d41d0500300e810950801082c2c440392204000b46029511448941e680d402044c2d00c01003460030080c100340003e030070078203005200d07540b01c00d11a000c88501c1da0303265807105503038 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 182941169 1250 182939919 182939927
    0x10c02101802030129010e01050a11100204170601090510170106080d0f08130b0a0c12060b0304031205010b1621020f070806010b030a090503042c06060702150901 71
    0x1d020003e4241d0b00b0b1118100c0301082016204d01980011007010b18001c4410004540855046001501180c020421242030510440d102082c410500040350f000a501551003c2268001ea118200154180710506ea0081090003094014410340f801800f4500b00380901031141c0303141d8401c0008842c50036030044a691000e421810050076402c080e82d514400421000e401d030320505540c1400615454001810000300240c5224900d8110043d00215900c0c40080e0009044072158101404078441d442d0044051500074400500a07021546e5100c0c1064a0090155a0100650440d29081c0401400340e800c10b881550700d40165210071514141c51810040c1441514020303000701048000074030107943c1e0f00007a1400112000004032001240d071468031646424003030280c50800b490800204d0b10320750f0a47c0002001034010340aa83c9450344d904000310f12001e0faa03000c013030f2680c3e441100b0090722300d200c1c444550105c4103441180c038000007a400140c10151849060412200104810714541d100d = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 182942419 1250 182941169 182941211
    0x40513060b19020708060109050609090d0e0103020904090807050d080c0301140d0204022106091821040e040b0a0c090302030c0d0c171c090e0c030604020712031a03010c0210 76
    0x185c02c0640c0c5172543c4601c400001f5050842d8203c1c052540c58000c944507200005800d03034081d1513175a4112210610300011000ba6100104031544a502c0b51303820000b244440c0c00a010051060b4000d20714001072220107131103000c0007045800c0b111000e00041200343c148003041c06c2181005c4a140c0049038683c03000078000d01407030b019a103640c2c50060ba5401d841140c44680b0b03001702006c4680c0d1200f13030350340040b00000902804035242d494012224805c088040700b10100030112220160354140758030707510450340d5a0350448080d80d1260081042c441a43c06521a22001040c2403814481960668000c0fa640f540840d40c070a003e201c0c1e10071014140305150000c2c034040c000d40100a008240e000c241c142e86c031441d1800040542d8140c0c422000160b000e03808503c110b03803c6610310809680ca800c40c284d01e81c1c04c020500c0340c00c00d80030890070000413995050301c0940e00840d2000502881c041804203e00c0701d5080245010f80e1501c01c50303002103a0000b440c1e0101c102c600c0400305070b41c1e000b142005c0c00111 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 182943669 1250 182942419 182942429
    0x60603090f060504150207051f0c05270301050c0703080c0f1206030a02211b0f060d15030c080c0102070602031801051c09150504020d1520040513060b190207 69
    0x440031440d5003c100010402441c0c2903000c4000003052044100920111280550f804002c90420030011440d00c150cd0111003a0070140f40e40003103921031010102e4290350702200c9441b07100c82d0014104c0101900801d0391078010f500402610700b4800d19041c03080c40b03885500900c80300b0420301720015000d9942004601c0c01680c0c0504030340400002003503000019818001c11740002c0c00b0392020800300c140400a44a0750b860002c00c64001c0005040c240300040e400080c400c2e203460f07180c1880740b48500c6903108220045109142d030b180700a2600000c2805c250034030302d000741190030100301080780960000a0340c002d07511081c83d00b02d000c0c1c00180141d550344500352038948800e184c60510355118a29520109810707000700000e00b981c01980c0800801c40300b0494000f07503c4940d42214001040c442d4000c194030b0a51050000b40c40c0c00011412030030380c0602190540302038000503044c4a1410300b0460707010f4103203175100180702250a01e0030541d51802010000841c1c0902d40c8200500b1510030890ba030000c003 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 182944919 1250 182943669 182943671
    0x209120a050601140415030b040c0b04030b190c020607030e0703061103060301151a070c030b090606130b15070206040b0301090204150521041122060603090f06050415 73
    0x103980e5160a03a2244000d1250b201c50550300c40f07102c1e055052a0141e225000c4914042000c1503086d0b640e604040e8030003070300a0314a1111280d010643c2108400104082c0d406008180d40320314000d510455088004421038101900b44a54510302c1500014040e40018503410003007040b4010900003881d08810341c0c4050701040c01e01e12500f8815403408015402010241c0c02800841c0c045c107001080d01341e00b4407c02d5881a0b0008100c0c000b40540000b92003124400c81d002403500e642ca845201e0303201c0b42582e070f0b14490381100003804668035011094003203200c0c1903203040c04060098000608128850954024042c46c0002c410301190b1f94142160080c3c01d012203020345079611428450300a400500138003021144841042a200e4080c401380d603000245c1c1001900714241c0c000d0b442c000c031007001e44104d50343c40d0301014804503a5074480542c584012008032280059000d050b03480c0585900743e014205140c5442039101c00300c1e62013501130766000d400c002c000c00d01d51564500700c0380d130030402c548a01c501 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 182946169 1250 182944919 182944933
    0x10b2407060b011b06020304060c0c1a0a060515030a0c0801080c130e0a03020f15010b0d0b040608030412031701060e010c0302031e0a12060e0612010603060c03090203060a0c02060703020912 83
    0x20617164003540c01140201c00820104988403400d40310780809103405802d4400c1c0010801641084504441c1c0c0f281c40c0c0e14003c00c0071599503020940d90311090450125403030010040182800c3c640c4038019031354240389408180e0f5450071083d070b0303150810740c0a51030280e40340d4102400c50148903040031031648940d10450b4610802810025151101d0704840c45207805401411199099070000b624141d4169801d2a8a0700903d05400c1c1c0c010400d0407200354015440d0303c0002020041400504001c09080001e51007510040c1340040114044034190700440e02d0800041c2300d8542c4c4680b80c900c6001003800c05181d1068107090a078035601411001c2046194191407004140007040b018000001301a110700000d01d038800541e034281c0d1080d010b01000c0420b000d00040c0303107140511030b952801c0c80c0c100c00052070381e03200c1e15004243e42c0040d44200100340c5602d1103608500701040b100d54005e0418008100c0748000c0c820094039200044d0035041015008141384450340e42e45041410600000e108407080 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 182947419 1250 182946169 182946173
    0x60a030e0c09010e0412020a0b060405060d0f0c1401020312040f1401060609090b12061513020c0c0109060203040f060302130e090d09060e03031606020c060702010b2407060b011b 78
    0x82c07500d04480c102d9410b1150306e0345030b80c0d4500000f070328021641e0000400b0000d0792080140030003802e004261541c02040242d0030008035102448841c4254050b4490401e410300b000d0503400a100346500050442d0310410010301461a4800b0704d54000ea4000070304240780085050005450f03001c1d082044d0503520340007001644541007801e0b40d003155203100c001d00c01d601d400300401608100300340040c401e41d0446800510400c540a20101d02c0f584000c000310400c1603601004004c80c1c10280d082140d651124030103001c81e40c0c1010f0001e00038800e81c070046141604000d50405d1689a5110304c2d000c0c190003003009141054071001403000340404125035101894400e00040e81c410b180e4500710045000300300c011a14074400c5807403251480002c1e0055103040f0315a0580304107440420303c140c0d02280c0c01e03c03103d00189002d11070540a881e82c3d50010508000b80c0b020010b004282c40c01100090b81032140058443c24800d06035403d8640200000032695480001030f18040f24480000348114440c01005007 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 182948669 1250 182947419 182947439
    0xf0603120302030906070e030c1002190309050f030105090706140f0c01150f060203090f1206070210060b13060c020d050706051201170c1e09010308030106020d03060302060a030e0c0901 81
    0x44074070091302c2124050345a440c8155400c2810494191b0960000c80c5a40b81070b007442400200a08076070301c101c0c0e0180d01c0005005c089221031090440028008010420091400c034540c0216290114020072860605800540e80c81049103d40000c0c040a13407801803401c5a4541641c0e00940f0b0420500d5503542c82c242e4442c0285196100c105031018031840c0030171070040c02011801520402e800441ca0110b1000400c00e60384110901541e00120a61103098444011301140d80100c2081d0024003020580540ca030782620035035006400c00c400709020010200b507810308008100c81c101e00744090307010b40c14004140442c00542c2c01908505c100080081e44a5100004002c040c3c40c1003001622a40c86012180c9115a84203041585030f01442c440707442882c0c4a9440d00c12020340c0b0550312000410140803d10f03c6000742e101b40d9880d8404801000805e40610103a0818009403a04211180c1182c1c0044c4250080b220407108050352220000c2071108108103419040c0c20051a6107891340e99843c2c098 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 182949919 1250 182948669 182948671
    0x10150509090403080117010e03041806090212040308160207030f0501330608040c05040216050a030302030403030f14010915170102040924091521030305060102070501050d0f060312030203 82
    0xa1280d203408a00141e604018840c11002321020400f41d40303000e14241d07040791400080303501e010800d039864500140c0e40c03d40e0303c014810307034106201203c5986040d040140820700000e007100102d0303051103c4c00ca01c007a804541141900d0340000340100c03204d42424160f005120031600b00c4940e01d0034401c0c0e207960301c0500100d41c05416141c00c0d60352080340c8036581111648020380f070080a40100000074065868950090201c00c02034a8080101d0b681580701d09103030420101d01070700800e5000042c0010b169041c0a0880080079102c8180000c00d010096040241c0c01407154200440d41c0343c0320020303040045c010b03079002081400240540c588944048074000c3d840761081e0348000d850003c168a2124000d001c1030340c138003040340d1400a094500b0500a000d440c0c1d507040002d20003613140c030200f510581521038000e014501240dc0c000340d0164a009812039402409c00b074155030200d14104007a80c1e0220445035174026498000c0b5011815100704401707004250070041251940c0403c2e001c466505602071 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 182951169 1250 182949919 182949929
    0xc1b0f24050906010513060803040515130b0a03060b09210f0f060a0f0b0d0f080702100519020309220902061c0b010e1e01021e1005010509101505090904030801 70
    0xb1158510312491100111810b88c030400d030064000740410059882c14a0f100a1540c04c04061686402060a4040c217540c07125040040c1d0000f000c194056555414030074000900801d561305413801e28858005440d200e0090036034603c41031a14030f80110710f84140160300d0100c246408941c40310300151001620740004550350a0a54030b0036062020381c0c00107010702490150003902c1d0380d85030085610f44102c0401008415554088100904001a11001400c40102d45180e540549604444510011492022480404550060010702c0c80d940c0c40110200c283e800301600c0000a80030000b100000e0102060044d60024012416084822001d5944641e2182807501000b000c2011001910780341141a01a0340040098220700085000406c500c00e15450500450f1a201c40072241704030500c40d880d0741c0c41280d41220703600d429a840300c0c1c01924050072044401c50024a0b0690314400c00180500c68640c03410149003d4600060103501120314654020781000c10525107410040c4c8044820300c41c1c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 182952419 1250 182951169 182951179
    0xf1202010215070c030503041b0909060e15060111010e030a030207140d0f0c03030b09040c050a091109040507140c0601051513260109060c1b0f240509060105 69
    0x4001100b038800c03070461146425854900c44480310b0f031021036450300010011100c503041e00d60521103c0811200e000c000780010103000c900d5032003514003c2c007540c40790401c1c0e0440342e009090a21913500c0c0078030b0311a800710082c64503d89009003000d00c0c501411142181d031880380000500e0741c11055054005104460051050031140e18a01c044950380380160400740000406141c40c240070a441800c1840c01180079241c0440c40002e61000a02031070303002e8400302c4400000940400050802c0510ba40c010811124100001800040e00480501c14403418038819541c40000030040d5000341d090329041008400c106840742014030005036103002c02c0c02281d101d00740342120304500211440803601c500184084c01d0304510710b044403403420400305502040004071308100c1104158401d201d1616550b020700f1000c540300b20400f80241589120b0700065205010514550011400042d00d00c40c050ba444124440c1c030003c1025003c2c0f14001d1050418600b90400040c040c40403070000f6500e0580702d044071 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 182953669 1250 182952419 182952433
    0x20618091602030301030b1e0f07030e030a0905210d08040c050a140409052811062704020d0603080903100b0f0f0307050a1508010906210c0f12020102 66
    0x404540c03451840c1e1514006034010801403000422070360403180c101c180210205a0325440c034500c121032080032500151b011255000b000681641806084008030b18007002d0340c44d021842130000c202c61128000c0324042c0c48604028000300d1510500800c40110718400d0ba203031116006401406042e0507503060315610f105440c08074607454880021411a4940c03000a0f8076200800706010190050700c1d001d507214001c0500140c0c24260704c4c240464400100c942200e400035280c41d0a84500b12100070f001d00561060004146100c0b0407856110070140c03420640100c0711002c00010f002c2c4c895584a44274403800e00034000108480007024180e09001102500c42c143e00041900007118400c6a54540c040d4a51000020b83c0c00e06003428400000c0c040d05540303001e600c0b07001155505280c1d5121036196040012280c0c00c043d8004181400340c0307609881404914075110b0020040801c2040801904402a900740d080141110201c0014280c0e41d81c60b490840da6400e1a40004d0705007032041e4050300400d4 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 182954919 1250 182953669 182953681
    0x191b08100902040611152206090b13150c02190606121a130b1b090306130c12050d03020903010914031305010503041e0f050303040b1503011a01030203100302061809 72
    0xb000307110742e41c1040402c3d10f46c003651f801040c0070300c54040240e0700c0c2692901d440c404503100c880c6061044901840107225040b06280c40e00b4402e002c0090fa4090754504500204207650100e59040c101d40e903940c00c0140000c0303600302000100305030b520116481003104c025000b0840ca041ca4031070b41c1503d0480000c40d03540c4102c00035045110418004189034007040000302c92a44080c100300e030b41c09010701c0c40382c02e119a09004c68038140060701c1d03c15034280643d01000412034020380c40c0002e0281989541100c0003240d64a0b0740d1001c4c05500c50b400d060300441e49003103070b0b00c096004280070364020074482c11001c903505025490368010300c1080303040d0030103400101c1c007940180116800385034010b1000321104181154020b109514410446007000158044400b1a1080024500881c010004000c540c20582c004040814046d2062402641040e582e02c455600328003110716594002c0c03c025a99070b0f01c4a86000801056420081d40302c4d42c0812a04c210460980e000c0c0c035007800548282e40652101 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 182956169 1250 182954919 182954953
    0x9030204060905151e0a18110712030f0b060a0f0807020304080c060904061a09010f0e0f1005040f1701051005060415030213080105191b08100902040611 67
    0xf00c03000022490b48003d29019800c0c1240303029020080051043d02e6044020300144038981c803548013224020740e4008401803005244107400360f04405458031440c084060b80c80050310212940c0d0301c014540c0e248034902d00039110790007137210003000510703d50b610b60b550b1001502c0003141c44003600000d0014070000300950700004c101c0b400d90702402d00528a034150942000baa651001c40341d140c0040d16030380005800074505061020384540c501d0200d842d9012000010003000007440701030208002c485083c001034035844042101c0150540d036400d080504941c0507269842682c1c03103154001c034896000222020017283e06135482c0c41c0f04000303202c181c0ba600d102c081d1018050141d00c0d88682e007040204122132544440c400505501d06002d41894520b200c1c0c000152a01d601058048e51580200199981801d1541280c1101d004080000e114240a0000204050044c905c148403c2d0710104090788854041080102441c080c25513480c0e403105c1c80100b1080700c0301801c0001d031094002d00714145600d = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 182957419 1250 182956169 182956171
    0x4060902151b06150a0e04050c04060609090c0509060304080313080d0f060e0702030301170106030507062f1c030f0207030207080d02030301061202070213140106090e04211e09030204060905 83
    0x3c0240607117005130900d540d1000500c0090000c44440c07066240e0500c26481b00d0103460000c100c00e481d504040740c40c6c60240390941e07882940300420031100b000081519030319503040d00d070029040420355031640d4502c0c03241c20180c800d540020b00012008030b29002c2c8040c168014812900c4000300600556a9a11f080c03044c917081035620502503001400184683c3da1000d0b01a40d1a64440d00081809640e0792980c81c01e14050b604080002002603281c035000b01003101d05020034406030200b21651f901c03030810541c0c4910143c0b00212082d210f0480508405200b40c21240740301c1c549500440da60300040c40c0180d07a88043d841030b16643d01a00c26001159800802904c1c101c80107626082844915003d0110080d40f113200200d80c0400740080a00c0580340506c00c804180e019510268000d504195001c0c0c075012090f40610314000760b01c1c0c00c200001d040003440c7c2001c59605800d02003410f401c240240c9200749108901e010b8400b082c8801c44003035511030090350450303000741e804105c07840d150541c480039590 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 182958669 1250 182957419 182957461
    0x15010906090612020607230313080303090a02060a0903060f0902030c121c20060105090907060c17040302031504020913050c120f01020a080411010201050403020604060902151b06 78
    0x300f1015004050708000c00140840340c07040206082c2400203005407c1c58108081d41d0700c0241d400400c036010607a058080d0680a0300c0301d403004600f5440c0400308203a442c84000300003401948003213140703208280126003002c00395501000500c101404030790100d000b80340c07681c026840707881420301821403414a5120511718008020181004038041c4040c1028141c40544141c208810401d80096019100c800403442c50001d0380a4449075250000304507104c1005400100d00b50132040c01002030075040205002d11941c0031203201c07054000c5030494480740c02690300103034040c056090301142541c400c0300210b2003584203d1701d0800540741c0341d01145c10800201401841c542c004551800c1078a46200702c2e202c0d010401c0700f20303508544041e540d0360076604a00c0251000c56207030002d10040140303051103510804002c0c4002c00061600b602c00a54030080584064100c2d50f0390389a000564445034515004020360350034850b5100c2400c12840c1000c1e003c00c2801d00303280103c2d000718a18a07850404510080 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 182959919 1250 182958669 182958689
    0xd061d01090b011e1209030e09070503010b180d0c121b180f09120c0b010b1206011b050613110f060a1103040f03050307020a0605030106050313080c150109060906 71
    0xb44103034000a00000304e100341d00050080104252402201c1406404002c5200396545034204102c1018045110805080d200c14840240010b1081d40c0c0000f003075612030748078184e442001900c0701c0c0100310640e015000183c07841005150108083c02e02120300c441e918841e903480040403c8803410105520303401d0007048510301a000a00f00c503950182c025102c01d54640e0350004130000c0e06e41d43c003c6005844074900020a03002852582031050040310705005004103103d603441c090a00c0510102c0d450b0080c0054144a860f08002d0f8460b07910b003180002d081da2000441c1d0340760070000c030386040071038841c40c00f1201c98003220400c9409091075844000486c1e405464281001d10000f015280000d0318259030711184814030000444010903c454001140141c010f559a40f503540144a600c600b01e0300301506000041004000700c540c040f089a40c414005500040b1064091502daa4036100c4c41c0000c00d01407140c44418111090b40c90440e5048030750246082054035900c90b03040050b150303e842904c03022 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 182961169 1250 182959919 182959937
    0xa0207060203030114040c26011818030c03050409060602100e0c0a0e150307030c090b0612070804080408011b1b0c09051b03150307140904060e030d061d01090b01 71
    0xc4d0400d03410540c0282c1f640e00300303400c1000150042c0501c1071400b0308251103081080d00100084444044906100c500c0c0007030034001c0c030300101420903110a0180c401001c001d001c10185c010300d8855002c0c2d40141141000c140f203890b5a417580259280b90901035005001e14266074000c0d20400059512484240a05440340251a068409552400060425880c0940c03a00d1004041d641403209901552050004162150510082c401102d0402040d035026031001c101c0342c4143c0d604400e080d6030002c004d00d03113103c0c199134515000c0790a0065502400056007030040100c0828110302c800209440a590707080148500c0000240d0395084128001d032088180060501800d242c0d5000140d03c82203010200c80d210035135441540702035104559900c00980d050840d10042d02d0148014802861142140c00543c090a00002c007219405000245000d60f0364241c0740e81203405000b82c40512540d0001009916940c00c017600000304a01d4640c01f10f1400032001095058052099009220f01a51a1046c0d = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 182962419 1250 182961169 182961209
    0x1b0f0606010503250207050a06020708010f05010308030412031d0a03080a0c1d04110a020604060e0307031e020c030f0c031c050702011805090408040e06010c05031c0603050f030a02070602030301 85
    0x100640703001c1c04d204500a40c40b022a080d00e4001c131010085c03410354010107202e03140000903400c440040081c400401e007003d0040010500c044203494100b608039001d0314006000303500540040601501c0b03d511768a6852002005d41400300d540013003140251104501d17542c90500120031601a8132070440031503400c130401c4a50441c03461558104284c09040042c1003407410302a4038054100c0802640142d0000041004000c146e02032110b0f0f4070440d10045042c800d580d034000d0311034540c403889601700c00300d44425611a180300f001400240b51001d003d0b903041c44141c81d030407511105144003450081c4a4502000e99140d8030780c0f4032034041c0c001955100d0070582d080d07004481c0c890608001401c4404c44100c085030961311540003c0c01035206003002581d45181c0710051100220040502d07047c0f108215000c00447c0340070084480491800d041d0006a649045041c002003656030000303019442280100e85001100000500802c4c0e035603001c030340301540c4e210340c02c99507032009000d8803202c1481181d0b2042 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 182963669 1250 182962419 182962471
    0x3060109180206040305010b1c02060301050d021309050607021203040b07050318060901020315040e070e130b150a05030a0c050123070c030c0501020a030c0212031b0f0606010503 78
    0x1030711610940816440303040e07800140310b81d00079400a590350b95540f44229a9403030582a504164024441d060688a0172500041c209000c1442064040c01000700ba0804543d111081e004485c01801001c001484050030540e98950f4101c4144002d0f00c81c0040161104401e5001e9a00c2a94081603031100b170b90b61750100318ce058201409108000702001d100d1082c501007030101c548903003405c10006031649040c4c001a1140b010100c0424001c030304d400036046004001023451001e075500107005600545030345602c0d08001c40c5c01e1101400c011054420701c100c0c1c03c8210318007111071808031501c0c0d480588582c101901d031146020010b240500d1200304000b5035008a1030080c1e038022101e92901c416005400b0070000d80d120060444491450074014800c00201c02c0500025207802e00c000d0241c5031403a84c02500301d000c0203401070f1040e03080b1413050f0400d400c01c1003124140c46500722813441801d15004410354070f1001444031481d070300800700080d1003544110103070b0388522403125030103601d4080b8050400c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 182964919 1250 182963669 182963681
    0x3132c0414012c061305101517160504060e01091509090f02090c030601021914031314060a0507030c05070506040f0306050f0405070b0d02040f170d0c0203060109 71
    0x44050b540354103e04280c1540504009000e40c0d010440000c0303119255501030a2a90040010040058600c042c00200300700040c4000b4000017440005820503540b102c90b42c010810750311514895900d803234251802500802d0101c480032000c880011a5610b484c200016a09180128400c0380403640040186403800c1d005850300700011424148916200c04451050b60802d0300142c070700010081748001103080a904855000c0d189001c41410340c10109c00003500c0d00c0030000c0400f000400e641c0c003207060080800d1102c00b0403036000c08890b030f5608030401c00703c120201403142d40c02c1c0103284152036030380b4105001112440b20190741e47c1850490b050f502603600001c500c00c19241481380180202e034070344a03031004001801d00d841041c9405440e600d0800c00f40c500052503184000702c03506c28003000a00c0000c2e09001d80f89480040c54984061200c0c5800a0045074008003d03402440d0001884201c10b041410120003445c0030744169102031081510b6110002100a400d1303840580100100c9036030768010 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 182966169 1250 182964919 182964953
    0x80604091e17030c04030203060601030c1d0301060902040f15050702061215030601090e0c01020106050306010302061c02040f061b03121109030f0303091507080403030c1103132c04 79
    0x12640100280c00c0300b81940080383c50030a6120000340a0080d450b040003039951110f824a400e20010401da0307001015541d280d20481c5c815036503000580029602034000c0f2015003c1c1110840d2103645d64109180d42c1110f51260300f00940040c008030401c6807090003280c000da070f00606210718025032403141500425004008000243c502e50140c091541d06001c02030082220a9010807882504050582802c01c6409030906682c9055400c1020361400700390241100e0b0112100b0740c0b00c80d0b840440c0400030b507198407000c03c90703440000c0116103100b81d0070007070080d102c0c595510f10178001039210b01c8500d803200352009404103802d0400c8440c4040b10780c019011481036004241d00384120701c00401c0c50152004440d0103560000300c100405940708011131004415201401c104e40c0c2000380c03018280c40030140001e800c140c0c548684c4031503107006174082c0c50380c088034400f1282c1c3c515804c90203032401c54141c041c02c0c10b4001c580d082c01044400041c061000c00000700e45080c01c585660f555041c0c1d4203110404 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 182967419 1250 182966169 182966183
    0x160806012a0206161104150e0a0207081e041a09060d0e03090d08041707150e0102151617010501050406180302090c040f05030a0c0918060c03020901080604091e 70
    0xb03800c9039003a83e084070044e01c0c440e5540700c0752038080c0402c1109a40d60a54412110502001c08119148215034121780204a08070010b07982c3d610382c00c14194900c00c0480320340740e070b0031181e6002c0254003d1130001c20468400041098101c0001c0c001c68005100d18800954004070511001d500224cc650081d1491041c0b84201c1c4c3ca00840200480d00c2c46041e0314081e110090041010414206040c130408020700700c0740b02401645050100d170502d10f1289410741420010228180e1400d41d000300242c40c24850407542816291825914041020265960810005044030400050000d0307480400b4103841050315154140b5017450400c030707404c02c0f000307203400400300801c3d03000030158562881e094011001850300d00d070707150300700510f88551103032560160b8026845402a6008220004010303000d07102115004214400030a40000242040d0800a0410307494070b9412800590554000e0100d420280c0302d014407961450101704c100d618a9501604041c01d40c9108004440700340400803c1501c40c000b = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 182968669 1250 182967419 182967427
    0x2a030304110f19151202090102060106350405010b0904020307060309150f090203060903031003020d060219030b040606020c030303221b0f32060909160806012a0206 72
    0x201e1505210002c0d445030000004159102e556140d1001784041840540902989440c10020001b542c0f039005200700010090106045c4901922200181c0001050803221491703c20520a081c94400c106842c00c031003035841c001000342c3d142440d00380d242c0b00b150001d029110184c50180b055014101c032500071900355803081d07500344085040f441803000200003040c000a80c4016441490310b0440e0242a80e610b0358803c5c410040c101304035103c500180c07541540c140810302c003686045400390244c008103040e900b4503c1e502e03030710b0561300d5800069102d04c00c840612415903101800c2c0e0300d5012001c529a0960400c01c0018542c02c900c8000384108111411040b20500290320783c0c8841071003084410300c214160350b000308203074005e810074a400350443c0c400c1c05003035a011010381d40d0b91401100100401031141841030800b44e0f507030003d40300180700182c9002c840340741442000f018040411a000081104040480d0080d403103000c042400d060030100c4440c0500210080b0025417105180807070740840100 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 182969919 1250 182968669 182968699
    0x510210b04121116051801150f03020d0203040f0512070b04110127061403091903120e0c0301060816030b060d06020a02010b040c140d0f09082a030304110f 68
    0x2041c6113004480c00c245520050600301003080030b0303064030001c0f07a0030100d07003005002e9441e5a1401c64529046030520f1481c242d400c14059010380035200c1e410104a01c0032040005105d0109034805405215006035240c400795207200d442e442c09001c00150002c4a1200044c0000f03422409083d0f0b1104141409201e2400034503d00d01c034240c00c0480c01440805425003000415080741c00c080c2c00f07120682e803071410351800d50810b41c0c0c1c0d140c41042e1082c0c24150380005401b4140038101158168100c03050602c8070803020240f05503136110840d40c0078003a61a0135400140e0100125084224030801c903402a41d02c7d01d1516044100c84020b00b4895000c448858940001130803480107200310030300b0380c0011540340203140c10082150140d51000301071009907201100056021401c41d1a2080c2d0030b48000b07602049406040c1c0209894840204042c10008088003200d40100815424404d801c002c0d21002e40000c02030781d00c90200f27950007040c203c56600b08c84d0700d51802502940d0f8044010b080014510003003 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 182971169 1250 182969919 182969923
    0xd1509090f03080a090f1b0515120c030106090e040303140a0c030e0d0504090213080a080705060c0c120c0a020406091a03070806060613090510210b041211 68
    0x4040407200721008480300d908064120340c440351312040401c4104090105501c070620110301c8100018020440ca9022020340701c4e0409098019010141210400c040d40d901006025440181240603005a0400103554170303001c50b0807681030340c0303c40d13a40e2000302c0e190040c0e8003030b0180c015108806258450048042e0705440300d11252081c040d0400120b008603c9240203011612507014a020710381040e00500d80058000c011201210ba10000050740d17a105507c3c400c400c0007070742d00302410078040d401034641488006000b82941c51f004105542c1036880d06400d451300d40c0700341e9412074401d802006003206821b403464040d10034403481005036a02c04a056000408841e259000400c100b5a900581451140900e00d60403030403106400507c1107a00f0308c1d13607042ea5201c0c010040d520424000030003558107010b41240740020503645005221900705280781c44400c80356801051240410400800c071061030207020884165005040c039031040d200d45d11a460b0507a0441c03200801d200440c00c04009400b02 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 182972419 1250 182971169 182971181
    0xc0207080a08040e0a1407180f0801020a091e0312030b04021c0605010e01051206120607030204080d0504050d030e04020405060d1415011d0103091e0302071a0d1509 72
    0x100b1005280d0320750402034681d0807504041c1c24030018034600b810829515503240525500609982401c0030360002c940001000c90456402001d800d400782d500026105e94150082d050701051900c50038601030303c4210f5031069a03440245481c141d00c0850040011609510108943c2c0c0400d241c04074010300840003050aa9101481c50071080c3c1c0c242c018101c03c40714511820001c2c0009180030710001c2c4c00301c8002082401041d0311142c41f020108007080640e81d49a04e250346094401c0140d40702450319000c0038000750410320601055000302001c03906a03074400e0085609490005251240c1884076440c00c6460500305900203811550810001c1900e80d5880c1c090700911403c20000305042841d46000180004050230304001c08141c16140c010070703a0031141500c8100e900210264500500a0041700501403800340541601c0c11402040d001502a4601201842c02502184d10b2159036003440c0300f030044020381d00c1928050520041607200c22a4202d00120120005200003181e241c040103030880c0d130 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 182973669 1250 182972419 182972423
    0x7020a02060417100912081524121f0609050a0303110a02041505030c0f0307031e2001080f0106050910110303010b071502040b041404021e0a0201060906180c0207080a 73
    0x4114151121b256101d05487c3c4d00104100030040c605181e000807030080103d000009402c1c41411010440100d42e0700d00343c40c581d041001e8021702c241052464401c00c03404001120400600d001070101c6c0490150f207982003161409450002002e00c0c0d41c500702c0d41c525500c605280a4020403140f0000b50360303540030f030000320501031440190340c51405040614140101c400f0b02d010b5003036081c14044558001ca0000c00f100d420800d0500c07014002c544200400d400450004d110021541507040104e45058603110100808e0302c0d41c9a00e40c175504c04250714030000b44503c1001681c20401c40c1c5a5081440a544d03074001c0034100410f6010200313001a055030402d070003c0d5000c5002044002c1403200c0c0c21901280c0d001102e80441c44d203400d00e105c01002d44a0b0303009004600c00c0d02620103c3d82e8440f503040303440389807080300d6004030400e5201200c134240d030000f0101401503003814004112451244644002c0300c2c0c0e02e0342850a51510740e50800c000d13000c094080000d6004401000400c40b00030700c580000c0c42c0c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 182974919 1250 182973669 182973683
    0x5060403030c020706020a020f1002100212060906120a26120604110403050601061d0315040201020606040b010c12051e0a031104030f110f2707020a020604171009 71
    0x2c69000303280180700d61000b03085510003090b41d40036813100e180d1034100c084141c07208000c0040e0b40c0c100f42e04c2c2150800d0656074184c070000c1c4140285642c010000d0140b00220b40d49070064940301d003013104200c42c507009070046d44c000d60030b400c7c0000c4071070321403071182400d0100e01000000ca000000d00300340c00246421100f500301d00c040050318600791042042d00c6140440c10345c1414110b03120582e980505001d4001800100702070940480c1c024846c00c07508000040403038102e20310300c07030110300c0d441303401e440c100d0152041c480800c5d980d00d41070203083d01d0248107a594907551001c03510351a600940d4101080284501040620b401c40010700c92807400280c0c924045a545c1d4500b40d0080443d856010000c0340a1002d11041c030018400310211401c031500480e800c3c501554400010350104405142243e01141e114411040440b801e50703401d02c0d081040048460503910410180d0b20b8200880c0001e60185040100b444020720940e6026460400e2401700d488820419502c1000c0300c0783e04000b41d5201c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 182976169 1250 182974919 182974931
    0x51e2202031807030302060c180604080d09061d010c020414010f030c060201050712020903150a0c080603010608150c0408150a051005061602010302131e08010b090a180506040303 78
    0x224641d10b40440c80d00c0c4401425030074619140207480f5100503002c0d01140310005040800c0d249200c00030b08844d03030010410f682d9a41d0311200255a05042030600000c9080c0040000e4014005c134110f98290a08400d013000c1702c03193324011a228843c20341d003264003503a102c182090f00c6000e50843c0c1d001e0444008100c00080c11402c1c2007810205aa2003401168106810010b02640c4451703012080c0c07095020158441c1101300010303003400446a100ca0720a010601044902c4810703030000e0300162496114890961648010325090f10414001c00180c1ea000700203400e40c89030858443c07540311408000075800c1a450b07010071070a01e28800440201c0c07156070424050600c90600c1800e802912103800d944a161504001c6406806040d2400c03124468003540704041d64001d40484501e0920740c80702c840c003a074131600d9104200a04019004e2901100180420b4019051103041d0242c0c0b4000e01450040e90313011740c00b20103001d0b0155401c07a45c1d0702c3d0b043ea00c40050020071007180268800c0c3c402042d0 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 182977419 1250 182976169 182976181
    0xe010203041a0403020c1e090a0c0906031404030810030f0b04030807031a0609120105010e090723060304020a080a060b010f020a020d080c0c06030403030c020c060301051e220203 78
    0x2036030220b00c20740c2001052040074040029000645000d07840c00c1a540790103031214140292692402860400b60842c0f4443c08101011903554008151601c0c142c607240c4507030f82c40c1c1ea01103040351520130420086091240104010074010090503500c1941c22041604007500c0e56030386821031000840844003801c2000503c010903801c401c4160f880401803030104401d0030107203440e503500d8681361901c50144000140c2e81000d9214911000c48110303148000b41f0065948881440900104580c0e0040c46c1c003d9000115044510224040030750701e05a02103074180319440d08010580e403001d031040f60301100700d05000401140a101c0c08491034010345001a1200e8080005400700c0141d881d03410864010003000c00040c0e490b60202068136070440301c910307240e000f100c1046141c4074a2616160703100300007204004c00c041d411f411092400046500383c0c5c98282c013a005106043c017003070090a50140115020205038800c65480d516034601c0140503500070002c1803a0800c00c0400d00b0462805030350000100300c0c0e = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 182978669 1250 182977419 182977433
    0x1a0603420906040e0d03050a180f14150a020f0403060f0506010306080712031110090c0801150e06121005130506010b03010b07030f0e030304090603030f090311040b130e01020304 78
    0x5070050b8141d806200c40d0100040c0c458440c10216103083c14981c1d18400305403020030310350046004100c20514013000411504000313000c1125420700311403124075640c042c00628400b041442c544801ca180c8034031313180c40d05080d0b0300103508128481c00b41e40405200000128006004200c844055804002920300b0500001801d881064008400c240c2c081c034010030800d021155108501509450000c40300c40d0408680c1c2c0c200090040500035640c2080021814807481e903803000122404000204110f014000900351440b9542c490303031303041e00122000600036044c49d4031070500303c1e10240c0681d00d019149104640c1241e10944402c10108104003100042203010400300340501007018956007903600d040c0900b1040d1044c880c00030200901041304440041c0218480d9440250080982c0e468a4075151103000528003407100707074005896556003440ca107000d800e5140589802080241c0c000b83c0740750a01020304408156640c120281501c01001001103220307284000007030100140e500e080a003050300c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 182979919 1250 182978669 182978671
    0x20f0c010b03120301270903200d02210d050108030a03060812030c090a030b0a050a0c08041112120f070b060a062703150603061a06034209 61
    0x34041d034031683c80c0e4031981030180140e03811903030340c54551641848030f60120b40c082c0840d4080d16480c1400e181022040607000070035150400b8840c1c040d5840c1c80b1617220100d40e1490141c0b02640940c10080c40000c0d0b180c0b4a00c4032040e02901d02200c80c4ca809000000e16040302c100360701ca0a0350f5003002c609040041c0d4540126402800d280004207903400d0021482c3c146440080c00000c07804030f0004200b090703903c840700c501001303642000200c809454580c0030140541004c0301c600303500750703e841e008800d403034021842d8500031504a8076680480b00c20100740300303002c441c54000b00458881c0021495004506000400030581c0040b9029151800c501d0910103003000504076074401d01001400f808003542c8103200c0030300c03074003543c50ba001e20f031195400b0610081d601b40c00240c2108482d5100042c03c000c250000021207200710410020751143d0f4038070560749034070340840507400802007000c2010305010f50348502d442e60407202e000341c914034800201c0318801e075070031841034082804501c4e0b030081e0302e4000e6101e = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 182981169 1250 182979919 182979941
    0x10b0f06040e0a05150d05031804050108150406060f080a0212030f0f0a1b0308060f010806100804050114040f060b04091a090c09010815150105030622020f0c01 70
    0x10360500d42481203290300c00710001c106a84195540001920008104513088890381d4090070300d095182460800c65220380c455031004042e1600082d1014150030140705240c101d07031078540503002c49a04050f0301c440d89035002c0c1c400e948650310b41c1004182b034154816000010b2160000902c1287c02074818060654404210402a40c100b803013071620311500901220000800d28180d9980c03a82d000d402540c000c0c0d8405484001154025000b100705070708042030341d008002c12101e0101d0044c0c03a000464040500302c07540b9401481000b4601d001c540030710000f540041c030880c00881c46041e02400d07036034040002ca03420b8450260454000003400518868000c1c00c407810359090040840980b2400015040c02401c1040400c3c9400020740c100c0f0280082910014001e00c4a401540c1d2840203e950303090050150b24101d0203034010481000d8990020840e403401a1035082c1036996410804c909103604183c507511004007100007910060341807008007440c00fa8041401d48456180d11440d08482e207051407 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 182982419 1250 182981169 182981179
    0x9070c0b13050606010f0c0503030114040b0901080d031802060a170f0c0405060c160f09060608100308030606040806130611090a03150f0207050a061103040f030804080c0f010b0f 78
    0x403001c00700c1c01c0440c00c2c540c0220282003645c08503a4070302003220b64004080c00644140404000440c0c002042d1a940170707502001c480a124001d00501044002807083c8200c0400b0b42c003000d004001300c1d000ba04907004900b01030200e07541020305600030074429030008100e00d00203500000c9500300c0d00070000f1400e030010713038800d0701040c0b41c0752900360861184101e01a4078424240450041d105000810070b441c8021a04d80a4580d0700c0d42c0c1d102408140c13a0140100f01c901c6040c40c5020039194401d1404502c240024013290800d28519214803900358800360109401c094104008646030b1402c0110902542801044002c1c981c4030b410441c0441c0d0100c04e408001141c104034207142c80d5101e02d490b2007a030f80c0200c0740280080c0314072807082c014840300a8182d520380c00450403400348032022a40c0380000d40103050a02001d030300200c25005610080318000d00b011242d50300c40004c02e00c20703020b00c0d80c0540b14194081c60400a1240649018009450700660341e44074040350380182000a25401c03800c00c2a03171 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 182983669 1250 182982419 182982451
    0x11030f03010617010303140306040906090b0a110a0206061003020c07060507050d030507050909090106120c0e0702010207030215060609150901121505040e03190530040609030e09070c0b 81
    0x5401402c1ca40f4007d1190040039020000c10080d54640d40490211a407110042000056510302011402400c952030261689080d10001340c504100c0200d60b40c3d84841d501a05142d40d4007800c00406002002410040503805e015805c2c2e0700c0b20030400600a0711107610b8281c0c0318025442c0c001d2415549150aa00701405c0c80203211b10160044240c50401a0442c2c10b50340aa983e601400e00401950f40a121581c2403009401c0c24070019000c1031307042e00d86c8115901060707595580141e0903131043c2c3c800200164814202d40100c045c41621072900150300504461910740500c0024261550741c003801c40072008006901d8804d5a003280c001010a60100b45c24000a03641001d83c403200310381445040c0c020307921040681c00b0420140204e400d622011609020300c0014400003c0c41500b000711103006010b00c0618100c210315441440f070082d0140025020b81c0da42c0e0303c2d82e40714080c1c001c00904030140111a200040d142d0b5450407810b11614030395442900d10641410b06040c844805004621810341c040 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 182984919 1250 182983669 182983673
    0x90f14040b18250504060602190c12060b040e010b090a0b041e06060f090f0311031e0606011b1502070212010c09260c010f11030f030106170103 63
    0x6416550064200c4251406a80e861000c842d1203412191600e510340102202218850a0128030b14a001c0c2202c01400c00d9503114010300003205c3c000d006941c050384c00101548030340003034070b017142c01042c0c42210005040c3c0d0b80c03807000c03160115031507030100d4425484403001d00490510744561001d26502e44001c2c480304a45102154200102915411007291940040c540f5501c070f5801c60081c09000e090380140007044029000002c0200f130040d6400100401071910031a40b054004006072580c1da411420038920710b90b1800d402041c00d00005405000e030398103005580b0380b00103c03c0b0740014141d001c3c154a02d00350000414120640451001003035200360040082a00d45c40880c080c28a0400300588e100381a00010314683d00c3c0d11020b078070560800026081071079100402d501214640ca84001001000702c0c449040c0010501e01001c00da480309003c00481c1d88614000100b0007082d041c1030f01d08403017256203182168040050b51280c10000001040015403000080710030003858803c0c003115504603 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 182986169 1250 182984919 182984951
    0x503071e0e0f030102071502040f080307050c0108070c02091e070f09030b060102070b0301091a010822020604050303071406060d02010903060c05091e0f03071202211204090f 76
    0x101e0015405070540c03a039440081d4400354100c902030303174000c5814420f2001d644400300207076100f03029684101e00d01280003d11104000141e484c0d281c0d000b009040d100901200450340003000501282c100b100b0701c4181805030310764084c090f02500303002d14a06580c1103801342c0406c0e20803000e0000002c20040c051094803050b4060391010a07640c3c0300c0008103954407507400403440d1041a402c1404125000400091201815401000d041c200d0300d80d1b030307103071035800c40015600e0030000c6481c03040408210328208104035005041c540d03024401480f02b0b0409807078402080c0b45400030070045a10400c20380030201d40007010443c590307011034110780740d400c03509660f40001d201d64581e200c020580ea458a40c807a541d5405541521402e0300701510300c0d6517490005240300080161101c6442c004c0c01911a40d070201d08022400d030081d03c8611a0030b0100d601240d080c040c603102c030050005441211140002c45203c010701206c1306105d88026a107442e00d007440d0901c4115450f0140d00b541c080d140c0320b600c144010f01 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 182987419 1250 182986169 182986187
    0xf0f0102030a080a062c0702030909060f010201090819021203040525091803030c0929090901030c1805090c01080a0e06010e010906170616090905070503071e 69
    0x25240c804450b0300c50312105030103400310390000600620704580d0f4543c80d140b1014040c0902c080511b140300d0300d85800100741d841c0c1c0729803c0905d03044844c602c00560b180c106080702039086034040c4000079003409980c0360440c468215850040201d0300d0315007800e42c05941044a01c48480034255450314600f0320360398007030303454049060b4090b24a650300c004072007040f0a0305102d4000c05481074248409a49410a40c15805074000224046032400f80003518040c815003030f00341a501d088c1080b665070b126211113610000850a680010a2810003500c07200e40c48030080107009500c58807048040d03900781210703c442181c054140405c024502004c01901500001d080d4050b07071401c5c20b01010540301d104051003d0030018103600b0380c0c0c0c030650000041c418001e2080e135049a0203c5400c00400d0b407036010030800c4440107407400d405580000d006c500580c018600c0318105140d20300702003d8485d42c4600c40c0703081d181d08403203030004140c0c048100310321203400c20194220751950111150740f11902c00d40140407018 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 182988669 1250 182987419 182987437
    0x1005211e0106060e030c091f0603020a080c07020109030b06030102040506160606060206220c031b0608060301020408030f0d020909090106140402190807121a28060e0a030f0605060f0f010203 83
    0x318000106502060040740c0d95450f010720300c02340589645581c0041e019503c0860403400050190000a40d0207071040155031915a05070344207503040d03245031654001120060040d65043d58200400600d81e81c5000041078020300e000b00d0720382c2240650803d542103e166900c01001c0d0341282c2c1c10000e01d1400f4006541c98411150681c00e641d01440c1001c002143d043e03000180048142e64901141a00d0310b003070481111146d54950a4542c6d655092500b40c1c040c6100d0304c00c0d941d005005590116001030080d104042d4040c400500707040320380c0c00180d004c40099520b40a165501c507828420011005100c01103080e041e2801d510708408840d085416404988006080103096400308040c0c030711074003034907404054004040c4609030504c0d1075000e44007c540c24462041c8a020309088420100e03101010701c0b81800c1012035031180c0713445026240345000002d030952005902002100103050707030000350304082c0510000075140c0b6101c0c0901020088d40020303c0d20522100402d00f407641c0c0d0000485107025 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 182989919 1250 182988669 182988679
    0x301060507120909050901090c0b091008060d1221051306090201020c030706031508070b0a050a090f180f14061306080d05070302060c031005211e0106060e030c 70
    0x10381c01c640b00300d078641001d030400c69005040c00d0a00000407015013110707035500e014417a41c020070303a55408421b405204c3c0c41442c54019000d200802c0714070f80109602c952081010b01107500810003036484403649180c100c060400304e428139051038520700700d414100d02400d0042d00d0030481c038100b001c0500001c1c0b81c1d00d50014001038032042c4034002c69100340a004410320b0301400301d40d903030780d140c24019025000720110b00c0d0382c245042400150206000840008071151402100c1c9402207040d001c4586902c20392040042c028200000034502c1064204d83c0c2c0100b48030458594400a11810801500d0074002c0b25910a03041035844c0006100800e41035030043c00413103040e1540710700c54050380054039060344140d24034080d0b1002c1c004034513081001400c6081c030990991f440c0d60b541e00e4010046000035124501ca8580d034540912041c1001001c403284910090003103484401c1100400c0d150040f506600c102e440c0c3d904403d01d0541c0024020792002e80784600704452007882030000720391b840c041000c45600c94 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 182991169 1250 182989919 182989943
    0xe37090303021201030c21020d03030b0303161a0106020a030f120f0623011b1205040e090c0a120230030c0a0209010608010605070308220c090c050301060507 69
    0x40c040e038102c44510f1061a03410115680d2401c24007298102407042c60307107500d0004003502c0100740da00c00742c2d20226402003c4814150346909c1c118014854800340300d8151004020040c503a2025070b84848095100e86009803604c40201c1c681c1260240603800382c805c0d0760003648400c0000350480d00d00288486103181003248404981da05a0190002c29142d500840c035040001c1175207280c1d0b8441c1824060311740300d00402062032100444052488000003c140414a0707132100c0018511024040c804c1e92601d0114102526004100040c0d13500303a50f2500c007039200d0100c2d1151401c01e50800c3c1c0040001240800c2c482c94150003050704d00718010711520a541701c806135541c40c541046001c100c0d64103420201d80d2601c12400ca0184e803803404079400d07449420b000f40002015482403000364141e034059502e080c1000c3d076035a0280d5000e1000b410f8013540c25858405900300300c4c02e0780f0242c607030a400703046260074007842c01c55610b048500c452040d0302009420001813002c260000b045030b903a0343d8013042100c42 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 182992419 1250 182991169 182991173
    0x305060a050604030b0907050a03020a060c080d05090c03060f0c0409020c160f0314030a0e0904022b02090a050f04020d110616020316060f03020a030e070e3709 70
    0xe0341256005294028404640403082c8414000c00c0d611410100c0d0444103c16121001c00c107411000d071000a512400c40340c0b0a015040c41076807139002c5a8440c0441a051404180c1c2c040159082101c0000066004524004080ca010009035400210440c0d000ca0607042660f812802440307070b030103a00c410940000c0e172441e0041d002c1000341005000354042e944019241d010880e4195000c5c1b0098030002554920012800004403c0b16440495038441070303003621901d4148108080c000f40700f039a00120740c44141e09419400519060440000100418810014030410004480144c02c803000d081c43d0904001c80c603480d801140d60099012120350124584a2500b410350074a45c22400ba0452008508403191b00e8540035180301c824401c500352a0001782c0b2078003500c51092144211400183c2040103644501d019900030407a0003680d240203e041503002e44018903047c003d90140701c00c6000ca00070407008070b483c0000802005035042000e002c0d1000c0e1440304900380c00d000c0c08134030581c1e82d945402007 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 182993669 1250 182992419 182992429
    0x120c050c0f010c080a0b0307141305090601080d110a030e06190201020310051f0809010e03031303030b090f01060f05040e18010e1f0207080702030a0b09070f06020a03030506 76
    0x503815003440407112014020301c1d086000c0c045541c030110204d4039100104913101c1e118000c07640c0382c3c1c001400070940039140c2080050600407203c00e02da00165075600d50f40c2e8501c04c0e03014142c07184032250000c04072545411221490012182080c404200b11092041c40710480032846042c416054948041142010000220580f04580880f03001b803048560480e4216019005184108051201509a150f0390024000c64000d0714031584034014510041d211418054582c4c207801c03c0c00000002901107010481174a0740d44140c03480008090290240707410181c0c5401400103480302615900d05030300b0038441c100c01000060040d24103010700c0d000f6070203003d407044041e2001000d0640c0164201d0034000580d5a0ad6400143c5c010065401c1500042e015000002c2c20b0740b00391b100c404444494010004204006d401040e0120355000c02001904007507a010015a05543c4c000e2070600402d050040040d8600881544001400c4c0d803501c20030840240c0200d007003042c0d590182008201c55482d400014 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 182994919 1250 182993669 182993677
    0xd110703020f040e16030b010608010e180c0402040308070b181009051507081006020102040b09060c0709060b030a0f0b0603040204020d14090d02010605040204300b0103150f050403120c05 82
    0x707150f41c45641c85c0d24480036080d62201040703d016103542d030040e9032070300070071140385400340a2082c40700703110f40110303040c0c4044080e19110f01e903184c419140d2200c801c0002030141c0c2d106610603a103040001c142801400024183c485d04400d0071081400828540e40300c0c507031070b015000d510421481c1c0e07500b082000d00105021902c80390010082300c1106107000c600240c000c500a031030144041c0020100860140e00510880c1d06070fa00d0040400d040030020410091581d0010341c5900c00e030700807000005182a040e0003504043c194a1504a4407480c1c21a1038908a5200c3d40e60034542c1c0c2e0424404503400c1d1240c2003102c0d00310390140d034007503a110400c44050000e02040100c03107080b110294200f11100034040f0f995880102541c3c0240b081aa4600401c4103074013035070203000351144003070310130440614080b5240c6e61245860301107001440d031191280c62281c07070309a0090b921402d601006003080811446040108400c40e070040125003001c1d10300a0000c1da0300da505d107441658a000401c1c0c0c0324020802c0d0303 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 182996169 1250 182994919 182994941
    0x90301020a0c0b0a0504021528020106171b04050a020c060705032208030105101107081623040c050d0504060b01030507020303070507150f020a030b030d110703020f04 73
    0xe568038261580300511140500c10141c0310700082c20045a00841c8601a0a0255400030724040540d01e1004000301c0c00c0e070180741004090036541c0340d41504a40d00c40840d82da030b54a56000003420300d10703010010609088407040440250420031805014502800d000f25400c14180c40000300c0d40c0e200d4070810001d00c1640382142c114800d980812003100da000000f103108104c074038000c0100404940030140003103120303000204504418030051065003080c8903003c20103462440c2c1061500e8250b010325081c50240c0e00011080e40040301c80e07260a80f034092140e4018440040802010700d8100020401851f1b84030f0f880d445a07450b50000c2406511510a6846010351102c040056040529011000741500856140460f05080c0001d00f01400401a24400c4805032219841d00c00942c0d60000388030103840011079030356a07685401c50582c500d817014004480c0561000200a5550000c242c039100c40200c40380d003007003010a01850f20690100d03000741225410b80c2d10036465000c080005001c0c05c0c9000300 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 182997419 1250 182996169 182996171
    0x61b08191704230f0309060703030603200406141e040e030a0804050c010c150c141207020c060c07120204090204020c0d0e01030b0117131218050f1c08090301 69
    0x2d000030f104410022a080a41d00040c29140d00303d404402a140c080514000160360028062002241004e0b4020805c4500c640b80016030b082c3c580d90f60f88003449041d050210240740e40b4105490038201071003904094509883c10240041c10400054a03c150046407161903000e0414a80300540b51500f050244650900649440d008d04641c000e01d5000c003100c05035070038411088001e205501500e00a0751103a08400300e01c03002061007941102509284641c0d80400c42401078600c80481500040c11100888800c01c0d07000341002000240340201c0090385030f10803c02042506d1400100054aa00316000000300900d05222030000900900305000301035081030002a0718401040c0104450068050300e807103400d00068100011400c5680020085001c00d804503042404070110700b00040d4400401c40e0030384260307021399490001e1500c55145000c041400400e2418404003a5451100503210549007010801e0500c0002248824007603140c5100404aa508005105149084950304280900 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 182998669 1250 182997419 182997421
    0xf0d150c050a120b01200a08070809131a0409080c0f0c09010e07050d1806090c060306060c170318010e100605040227010513030606061b081917 63
    0x1002501ca90310110020000590034030565030000190720688500e200103944a10000000484000c010940d00034010074070712840210700000703107545000f0180b081c86440e2560300d68100c64180000200036054200034a41054400301030f19070a510010b4200c0b1085030040b45404480c20107240c5446010414000c80c0078000700003a134003a001400168901c015101e1951580c3d9070040d1006100058070160300040b41000361880c1040a0740110000651096951400701042d40c0c81c101280e90100c0c0c01c623003000d0f16003400c000e40340c0c0610428004290605001c04805400d61b40d02005a69014003203a01c4031004c00425006a1910711a81004180720b00070040b4039403e00321159030f003c1045001c00700505020010409003040d000703640305889241c0ea10640144041c4c104d040e003081450185040100902202c2c851030301d9501c9402c0154000c140c0040c84a0070724a00500c4031400010008688010b000410f000403a440115013960344088201e5092400803903048441e60308540d100f050000c8108 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 182999919 1250 182998669 182998691
    0x22a0604020907050f070201050703091223030703050d0e012003090c0607051504061e02070c0503060f0103110307031505070f0212072901080a050609030403020f0d15 73
    0x62050046008540080b49980e4541080300d661040f00807019040341d003032107a0f00055004c1c901038880d0034407a0034008105600d03100300ca0350710400d000040e61031008290809c80301038486a0640c4120726514065494001c0644018001d88030307161410134a02c0da80c40030b14802107400c1d4440c0d05c918810703080310325000b844d4180003420340c0c0040d502962603008041a2041615020003281c040036800703c00303003458200080c1e10500c1000010010b45002d070b00c1d62035a003622241004a200480200c51005803501114206914030031080d4001500950000c0305100e0101c00040c0640d0450764042d50a4000000e81da004c00c1c2025030030303800103142c103800a07940c180c12406a00800d110b0481540d82c0303110305200c1030080381d68844901c035041d4251401c0100d02c02041c0071802c0712041101c241442c407550a00890428000c00090313106214a811100740c00040040502c1026000414003000f9030400381947c000a03c0300c440130718078510a0b01520321003420030107855036032a5682c00090040148200c5e00d = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 183001169 1250 182999919 182999923
    0x207120b043e0a060e06070c21030311040506190903240509060103080f0a0513081c0503040b0f0405010b13050106020c090c04060807020a0b07020d031a090406022a 72
    0x150306070a80d00072640b40c0042c150418182a2080301c405913107001d1465020b4050058aa00c01c0c8416544002c0224003c101d1404410b2074812110401445400d22803c80c1002801c031600e400c000102d0200c10002001180d41e11010391320000b40020781c054100341502da05480d040000e40c8001c0101810381ea65160007024081040740211802e2030520903a6500099141c68610034040140718500c140142601013100c0b0010b8080c403000da0414a1501c05441c4150006180560000040754000320b2040c074601c3c04a214002c50040d6803c01a046080036079030035450795402405900070301513540020b414810300750810050a00080c1603210320803e00300b4110050f103400d00501015100b03e251080c45030030009070f460b202b480803009550501d0705165003100c0d0300501030604000c5114519915010602c540000d5010b003105400030803410038590b1007e8107407405c541c1003500034004030047e10305549505052650040d030100c0c0040c0d480300d502c0204c01811417820404503514250280300090102c1c0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 183002419 1250 183001169 183001253
    0x2070e0c090405070305190209030106030b010b0318070803090906010516210c0807120207080303010602060603010c14070201080a150602061f0f14030a080f03040c060207120b04 78
    0xc0d00d090105584d14071059058450075207100044413100807245c031400490340d020b0400000c0c0140046222507480c6c844104014081c0c016007030079840001401840c940403152802c6885104025103100743c40c102d161a120f005450300140036042100019400740e01c40d0048507030142c940304030304884900714140300c5042e00190340503501c0070000404103400d803402042e113440400c0d0710155407890329465564201e0180f0034040e4100661007010000305417002c05102075800b03040154000c0c013080c5004000c042c2034421409210041c030030b0740d0981d0324400011600b158041c50702800c00140a85401e030601c070081c0031804602d05002400d00c1d0220b83d075580804c0d114011417040100e5005a024219050310040d060b210b0444600402c200c100080123180c0480341e02c0310001801d44407171843e40d80b070b01c1001cac2d4070175110f4940040c0000104000c110034119200c0142c4620310081454a04103020300d00c1d008514003018105551103c00a010070440c440013451a41c00d03005425070350404161103c0d04219 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 183003669 1250 183002419 183002437
    0x120204090c020105090c1c06020403140d0305130818031c0e01080f130b04051c03050103032019060902030304030501140f0c04030201030c0509030d2016090c02070e0c 73
    0x4200b03030101c5c0000d800080c1c00070000c00c4c0102507170001c1c00c00307520007400c17080130b0034080f201c464080c0f00000104072402c0e40880f24101c5000034103002c26000000404441c8020b0003444c1c0d1013116106032002c0340e4a0015a40204944503881c04e071000b128000a2501d515130500312801c3c28480e2030301c0e4900398403417800c04040c1000c1c0c8402c0b40640702c41100c140207400485107298035400001030080071421074504243c10a0040082c0c134181e510300f043c80859640402c111102017511880100300709907000d110100c841c500124084100c0a0b4035a240e030310b501c07440d9640800410410000f1041c005281e024131070180e4002e080f01d44e00e5680c0d1824602920092049907071045100002515a580400c80c01d44104142e801d0103140908560054008113a0440440b04104083c0800859903d00b041858502d100c031303845600c5258005900c1032010394100c042070740740350410f599a16800100f450107406a44e0340c0c0d40007181840300024102d24140c2c1544c44050518404018003140d10200b600800442ea = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 183004919 1250 183003669 183003671
    0x70c12021c03050105150f040f080a0c0e060108270f0616050406080406050709120b0a0f020a02060c210a09060f0209010c15061203020c10080c0301090c120204090c0201 74
    0x40400c11050301120000d1017442d03000b40d800c480301c883c01951131004011034080540c4050a01c0d8442040c040d402c20590080350369644140581c42c140300c2003c80d201c00a0885032036441482c501400024408600605041c1000b80c020440347c404025400c1c1200c81103540c08221907801c0440c1c800c0640e11142542c50040e2101c0072050141c00354031480403207058407540c1d02c42c01c0098846650309002803000400340320800030140c80208040030b10521100300540076100c00b031100e007084140d940071a01000c1c91200d81034410082c2c1d215945c2c0214205901600b00e800b850b407030b0701440148054440c9155509071140341240304101e903501040d80300010450084504101155950a00c03c08a21841c4c1035540070440d040c501c5800641c024501945104003000081450382e03444107110f4480700483c1e01140903030031821080442e41040f0045091110452400c05003600380f0900d070300c0f010711042c0604c100640d151200c400600d03006200c0b00d02d01071401d80085655076501d50f0444001d1000400600040d = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 183006169 1250 183004919 183004963
    0x151801112506020d02120906190507060c051303020f040f060f030b13080d0e152404050c040b03041109071e08010b03010902090409060c03050907090e0d08070c1202 72
    0x5440040d1a518a00c245c0e001008004102100000710b0b0b004051031a03800b040820010a400030807440c80c4402c1c1d80c40c2d42761345031601d40528181e4262a060340780c40e002c02005105550b904050704000d48216501561490503513a5840f0105024180d40740d41500028281100000c0004400002c0401c8902030f500e150340c240c40b4106c20031041c40d1000c2015000c03a0b424031000b04188142d0344845030215200c01210b8801705103240f00d0302c0e258000c81d6007400030484802c40200c6e400c0d5103011182d9454049404025031700c1c106140034154050b0f4007030071401200202c00a0100a510381c0d9071044480c004095000504d405803004050328000e00701001e0090b00c1441010595009503185410f850813203c0082c03e582c20035034a440207400c428a841e0740143c82e26101c001041d03161259035025411584d01203141d10b4041001490040154401020a07142c1080310300c003014081089600408545019102ca80b90031108440c9089200005400e82103080320800c6c0154002a134152111844020172500b = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 183007419 1250 183006169 183006179
    0x102100510150302190f020c030106090209040f06050901030305030423011b081006050309070b0d090203070501050301080307030c080912060f011706060d060e0d0216051518011125 79
    0x40c5c0c003602c569001e0500114010081c0e00e8000d83c0303022004891b5104440050700074800003801d441c159400021090350008047c0b405041900071074090740c1c1d904009116442c5480c0106961980c148009402c00a020001c10700b001210100900e00c0500750400c000d022040e403817890300810b82040d00081c400e25411400c0c82c414012400c0d90b2040680308000e1610515088003580c59500042100c17640c0d004100b07010400310220301c0a0607403040307250000290740c66288103040c82d1071707003540200d814810280010001e0850000c00c1724011a45441c1c0703203851481ca850200c12502910b40c00d0313a40b181d09980c40280034040010818821003c4003030590303072030740c2c0c56846044050781c0d12481d4078540c10150005007107003001c2c0c1a48a13082d2041d18001007010310a100e29090003400212003006030408407009100d1519040c103d40034048c02c03255154048580c9a10002a02c5800c0b1442c44041e154088150b581c0c2c0120030503489a80703d0b00c00d0f0b9850068a407800c0c00380120001c05140e0b490001d60010507 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 183008669 1250 183007419 183007421
    0x70503060709050d0b0711010c0e0a0b2b020d060909170c032b051e0c12190608061512010209030327060406031d0c0a060e01021005101503 61
    0xc1118400b8104001312405034850501c180c500400b107500307104d28200b0060707441809108010017065156100d48a1407070b01c508100e1403c580d0341c84223400c40d1091090041200d84036080f0040300c42900e000c1d11401c180220203c01a000310030303903014640e18101c0d002400302c1454018068440c0b140200d45240804842c1c030f80228018001506804e60007401081042c000095050395502600e080c15440b2024146041040d02c0046030152401c02d50003003454003070740500c076026410a201580082c100040310140d040d0b2010020203429010040044003c4c50300090390061020f407114400340c0f07144d4030705100401c050680c2040c03001e008000640000102c0c0c5018800d80303c40301740080107140b03030007201d0001080c55103044569415445502600c0d0b03c41d0780e149030041c0000c00290b200031400501c801d002000c1604d4035900c1c002c0903040816212040d60300e0018030070a48019003010303034424428000403407501d0540e018804d01c0602d00404d010450f0701c0c0b1500002211140110f2000002c50203004030 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 183009919 1250 183008669 183008687
    0x170d0b01030b0a0b0a050f130801020910030c0c17072001121103013f030f020a050606040509030c0a0804050a23040f0e010203130b060114030c0a050705030406020705030607 76
    0x30102190031301083c1078a84c0300343c00401d0541c030803100280c1403c0e8580488074088685034027030003160794006140c040b20300300305034058501d540c40c2c142000000b0304d046002d840240041d1000704183c098102c5003202c860720400b0341e0700c40340e0040c5124003540210000c283d400f9010f400e03100d0100d0042a08180c2000b002c0c054a441503511156140c00d613440c000e0044480442145071140003c045801072180b070701c58001c902500c008000c0c15028490310f41c20007510300701c5c14170984400c5400c084070786000b1880015401303810030402d03140001c2950b5004505400c41c003130000c44806130f00034104a403091000c0f65002d0300580780112038428106a41d118203000c49848403184580d414106c2c080e0040c00e15041d40030080c1152800d401148001c4044ad1140c220b80c801c079000d0810031010402001031003032501c4007070303400b074020b08081600010b21030700001f160100420045040c00c000070b42c0c0c95000d1040042c1ca118035400340460303482e50f442d92800b9445110343d00800b8000d120342000151428810348041d = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 183011169 1250 183009919 183009929
    0x2060f0901060617090c060f0a090506070b060d0809030718050c0c0706030b0102010b060a031d011a0d050a1205071502040b070308090c1302040504050112020f0d170d0b01030b0a 78
    0x1346104507520310301e84510301d0000e00c0c4403118010b00e03d0002540c0c0712a00109003070b5060600541c1d0b41c0320403c40c003030f001c2042ea400040c001c20043c098080003410300313043c03190440e2080311001e4015003d46000c0d126031007518692034050052420000d002c1d039110150401c0425602001c0c8150340c0c81d000e100109000f0880d02c041c0c03580c40740e80c08005180c06075100c020080818030010824540e400045020365100341d1060002998601703113030414049500d400045424044000d0000c0070206c40e001901d20000c0101c1403007140254045420004c0801807105274517440a804002c510f0311042c040e14681061000307541c80c03207d0b0b588241d40d03855113100b1141540c0f45440c0903420100c0b10b440031030b03541d14000c2c000584c612030302040d61402e0b500c0c0049403080c080030540140c0c0d504d0030082444180c80060b4050214074041416400c0160b0ba10900b40010000503a400c1c15961041c1c01e01d44035240d96481d440113054000034100ca05104990080491071070280c0701800901000401d01c46000924803030303 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 183012419 1250 183011169 183011177
    0x3030c0709050c1315020a0606060e011805090705090d05070e040203061b1603120e030901301107080f040e0708060306070f031e0522080405040b06120702060f09010606 74
    0x1e204072501c400810b44c01c20401d10403100120615610f008c00c85900742c10904c0800c1d0403811242181da8000c24445007004507000c1504000c0c0303408040380429401400d0708052000c045101c05050707c03020b0500d00420b803c81e007214400c0ea0f031100e1083c080402950280d029004e80e0000956400700c02c0c02868010150a044c0c0b03141098045400c050000400022002c0101000c20503100800a004088100d1546400340d96184404000501801c240c0700000c0c00c1840d035900c4a0303881d100ca01c40150611440208040792600c1c01404082507885020350084c0441800324050580f02888400340041d24019103200f09581c5a00c1410b0750104000c8591552690080000a0210740318503c1030380740000d03505020408e41c050a40c10400200344502c404090b40d42c500400140284401c1c0c040e0150080b124136040d0402e4a8071624001e01c940d000700e50141d61124086280768560300122107240e20701042501560410804c025100c84041d00c21000e0103c408001c01c1030a001031045204844a54171 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 183013669 1250 183012419 183012457
    0xf04030c0201050904090212060117070e0118021c05010e060105070b061207080a060207051216030e031509010c1e0906080c04090203071709010c05040b1803030c0709050c 75
    0x1c0110340a5009034015900251200ca035400144c80b506807a442c299580c1d409014030398104021084c0b481103d0207490080c0c1c0c440c1100b084001601c1a00131306440d844480c0e08030722144142d00c24040d1103980e407c0080c402e104c10b40604000c2c01540914140c442c6002d080c00c60341c0340c040044800f4040c1c0c0c1809401c5212a002059042c0b502814401080c00c054098400f0107030385141d0f203818210642001e132007042d0005607260402400b4002d2102101c51600b185041504210205004841050000701480080f502e15519503a0400c0303222100c0050400ca0701480c9006920035001c0c01e0b90406101c045900003074001a00a2403800710b00c4102c1240c0e85541c1e1543c507000707003192000d401804151141c1c804000100318180c45000030340c4181c101ea00c0307500d2140789841d1204034851008100e00083e034075040c1c6024070558000300b260220381814860549400d4841c244500101420040e03e9151000140c000781e0203901150100480d0103c0c44104420359070305822820904c101900d12401c0c02c1000 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 183014919 1250 183013669 183013673
    0x80717060f1302130f020a0201061211120c0402310e06040c030b030f010e06010b0405060301090b041b091514030a0c141210060f0e0909030c0a0602040e0f04030c 71
    0x840480700600007404504c03001e032004c91480448102c18010328100d50000780502c4000d4090103544010700000f50b83ca400740015881d901114030b5514030162261030940508030f44004100078a00340294018011541c031540c04460b12181d00d0840064407107a5128003500c08441c80c40980c0b031045a14000910141d90396910401c0020300e100c80c8003101b4141e8440b092403d5460030440018204510000000c3c20421781c0d4800c0d14000c01640507400300202040244625115042681e045604294000c10400d10980028020307115a41a00d82a00708160032910050391000c000c004a41c0040d0390000c03c030002440880b0000d4121030b540100f88030420100d8064180340d8132484200c41c05150002001249001d612240d61140c4204407402c10041c06002481c50740b003408000070036650078403103d94440340ea4064a84542c3e040e08503c2210844009080490184112405c000c030310300030744c2c040c0d034000d00c0c0400c02900940108505003c4100010b01c800d91481802800740343c144e120841441825 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 183016169 1250 183014919 183014941
    0x120f040c0603050f010314070f03060b090f01080a0305070c12060f0c02011a060304020a030b0405030c06130203060f0402060f0d05100501020703030206220f0f02030610150503100f080717060f 84
    0xc6d0040010700c190400014070907078024064025600c0740bd40407408861040800006150241c4518181126840100152040091500e42d0070380d0600300652140c5240c141307001240c8180e0f001d601447ca03427600b41c908015a5921103041001c64241c2081040451813080342218400d0240300c3e40030b03061700741405551404401440e84240b00501c4008140e44030742e04d031051580d0580c1c08841c40d51001c2500075900b6000d101c0c40f07a0000300c202e40507840d06034640020b540e855018107070030480d41c00e0300b01140c15502c0702c0b02103030040c8150400840d5113503400c0c0004170003450100ca031140d03900c043c0040440c0940c40420034904403030301030f2f0052860b0307151010001e5183c104903840c8501040310b41800d03000a02c0149046482c5401202e240a852920f40145030620741c000706a04401c123031644040c04400d43d03400c01001c034007295180c015141c0d0388080d184451250160000c200044080c40c0004951700c00207110410303030b00c070b81400f00340c9400c0f061501590b56030207a4a0301c00908110002030000307000 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 183017419 1250 183016169 183016193
    0x30c04020705101b0207081902060315041a0102010b0303040e0c031911030f070305010e0109020913050108061b040807090e1903030203180c030a0b0903120f040c0603050f0103 77
    0x840c203480102c06403003056000c650b410828104d0a8a03030a0003c90000d40511848008100e4040582080103940c0c032041190340507180c3c000c1c03054501101007266800030001882064402034010080804608500c044280b50305801030300541c2410409105400d0220564045611074409000192902b10b03000940f6000240f0091160700041c03800d0300c10346041d004003800c2c10941c03001c403503480c180f071103414420b03590050110301890708090041194171110321030581143d0740410010303150f07507081c8000340004808000091030242001c0000c5603c0d2070100b00300d801140074000e820101004411400c1e070314011846140446e80100d541084002055001240c1306100c86098490000394403440701c0b1075008480702500000d50200c200306403203001a0180703400015000007018039028410019555002114004100c00c40a030301040352000200195080c04ad80c01e15075140528060f4040c007200c1104170f4082d80d00b035241c540c00007001e5019104d050b02a4007607a000304180e81c01c41d1581c00c45205 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 183018669 1250 183017419 183017423
    0xe0a0818030304080c21160603050a0516030c020309090a0c111209010806060903012d060302091b120103051b04270201020304180605040c0305070203071502091305041b05030c040207 80
    0x80002419141b8001030058418003a29681120506d50420a00071704666005158080244c40c10003881950300701c446070750505451f40e2030007280c1c030086074030104d00314003490712001c0e00b10b0091824400c004006030402644280560784040c1041c49161740107540d0599070380164070030041040002810b5214552043d800740015104600d4a0882c4011070300315203102015220605002142c021400802c0f0041040031220030000d201640c2940c000649200700070700020313085c44040017041113046050094540e034105800c2c0b10b002e03075a520300b8455203070485601650f5440031000401035407407a2920030b80c54500d0120207a5440104803207524006001b40c80c40903410343c40103000010b0b501902401c0c074500c0e031404070360200d1241c0c58601444141e8400c44484400d0500780b10402c01007d85c00400c2c1c420b80343d0040303102c10080031030354203500003482210500e81d04000c00f403144020201258018030700883c0b089429002c6e0022404000e4580e6440f80183c03541504840b124003c1450941c02500e0ba4134 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 183019919 1250 183018669 183018709
    0x6180a0c020106170d0206060f1003050a0b1c0b130b04020d0201020c0915032406090709080109060c08100614180414041b0e010512010e0a0818030304080c 68
    0x213031580e8080c0c061828100038103001e580500215561198103010701a0855803d07190f0015007131a800024a620300c03101c82c100704041e0b6607000542a802d0715042107038001000b030a400740d82505108144240340130244d042d90005000c001080888074000078070001c458200300e114115844030f0b402c10113902003000c0c09904512800d200d0b40410741c0c2c0c200700176014404408055164100e4001414107186000134441c0300d8800008031041640181107805078002011502e480c502c1c0c5d40e40c0740aa07507a141e1a00070381110340ca052115403c03c075003940040648070040d22205050365440645950128080c01050002129000031181c04046400908000c00e4070004606c1e00d0611000410100c40c10490300001c10301d0070702c0600c400d02c0f4180c3c4046400254590900002900380019820300c040188242d81c00351120f4001c03001c10440a41c00f8028400149003903c0140c070950030000b01540160440c030070169003c44002110b80b41c0003003110200c1d00c2c49800b6000070707680e12082084010446400007414 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 183021169 1250 183019919 183019931
    0x90a020a09020c030913050106020f01020903031b10020304032c15090d0813060816090e070c1b0f050102030403050a11030c0307060305040615030302030d0917040611010506180a0c0201 81
    0xe83d0710307214000f904801d86c4000003503541c0350460003444d28000c2146009540d01c10851068a13840101c07c5401281c4418503402c0313a0768840081602d40300d0f540c6c4021850034404810701c0205030784040c0c00072581550b5400c080502c004003c0842c050f825100c3c05a0b4007000d4040d103080030402c41170103400f9501000300341941d12081c41d25444c2196000d040c5c4107a0000c120f550902c0480e8210002942060041c85001800c490410300508103e0312801203d0702c865800000400d04c40c450000d0b17585644d031200f100e00c8012501088400883c1907401400203086c04414042100d505c00015642200e81200007000c58502545403003460039851200036415020b00b044800e45130314104600c000800d01680e000510b45040c0c01c000040340d003510b12020441d40e03104010400b2990001c25109202140000040c985000c1d01c2c0c003084d140950404000050408100000c0d03890304002070000b00274800000307000f04ea580c0d00030007017004060300c3c00180c1180540041014400264400c64103050240000a49 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 183022419 1250 183021169 183021187
    0x105030f090c10090801050703140c030615180a0501020d0509130603080c030307030509011b081806131a0937230129030106031202010e06090a020a09020c03 69
    0x5407141c1c1c040c4400b28081c080200017203402445150390288241c9000c001d40c4c2c8480a41107030783c0c64090041c162055011001c00c51541e41c0c0402490320400c0610926500c090400c21f4401c40400003126511a2550030303800511340d400440d25802c0310304680c0c0d07207070315100c00070040000d103144c180c1c03039280030076030b1640040700107840400100382c4601d542d4029a26031400f100c0003020751304002c00300d5481c1c1e4100b8482420040a20b28200720b500e41c142030801d80e0355908180d007401070701d4811000142e031081806100d0186001c481d003901c01c03406034a01d40200a01d40454040407001500c640d51550300c01da40001c0301003900320403144100200c1c00c074070320050030010440060861941c425a2020550005200c03142d01086800284000f4140203201c40c21038a01c4400c0300c0300d0080c8140074440810f840d040c0c20707603500392b019901843d8441c1ca40c044a905c80d8100900038800c0c0d089182c498407807003001c10f070311090008030010348980c01803400402c2c600b441c400c54060340101e541504a272100b8001980 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 183023669 1250 183022419 183022429
    0x71a07080a0503091009020102060403030203061c1226011707090c02010b1c12030f02090d0602030f090604050703020d0c0503190204051e01030204090f020d0b06041401050105030f090c 81
    0x1d4291040d5071000e4580c2002d5461074144018808005032040c50b1815490050f600440c80c994400c0d0142030050f00c039551000414820800301d80e015144500c150641c508004c94210030383c171890003954130009091100001c1c261581124041c26000418142c01001034400c07044400d03600b1003101040c4c41c0300b242e4900314002913442201c030708400760751110107a00c1581800210405240c032000c100c4100e80d04180c5540910440d102120340415864106030700040308540c04407440c2ca80084d0180c2c0c8002201d0420382d00941040da5443c50042d10361001c80c101c5040095014001c1d900100900112392855082010222a518044800d07140c14480040c140d502804209030341150801910b00e0000c01e0f1042100300c520040c00b41418030080b403c0300014800e070502d1030f810360380d05980c00100300e01103081070800154a04c6000b54410010a019000c000b66036850f40d001b0030040d5803c2c40541040600c0300c3e420340c0240503150004000b4800980c6c448502000c2c10340110080041c0d035405204000854 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 183024919 1250 183023669 183023677
    0x2c0405120d050405060609041e0201110d08010306050105030d02070e0a0f0608031e130902180910080f0c060304030f270305211b1603060b040c080702071a0708 70
    0x6814540d00d00c03c0005022040c0410340e0301c408100d5070940d152a041e51050a258244000b50341c00c03e81b01145071085902800407114507041c1c0400f1900e1071105c0c40001013100e5400d000c111422424075000064a0900184051009185401030320045041007081012800010144900c4584409025018060f0380c46203d0152403844081c43e43c800b002e400d03006503ca4081c1400c90740c2c50040005402d5101d04040b404155010081c0c003580e01d95405000d00a40524491941e5110302d80d0f409000720b0094810191045510750400d4031941d5030039600460311000d201700d4954008004100040001740710f10491708000c45c86045c5128400c81001c081030004001082c080d00c140100041401444820082450aa4a40014000001c15002c4201030340d0041020304000328020b110b03807030048007090018400b1940c40d000b800c41c025990303040c084007400013140c0441c01a85040a01000941700c0c0008074841c81454008048003450701582c2d40509500191880c00c2c0d10f014440a4005500b0740020 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 183026169 1250 183024919 183024937
    0x20405061602040c020c0f010f02010906060b030118020703051608070501050109240803090103020c03192307110f01050c0102070b04050d0504030c0303030522030201090c2c040512 79
    0x81441d801003441408115a03820764904113662050010401956514402c113a6414081c40c0140d600000350405a004d4401c610300102514100380700031840740350b100c010794100c0d030780c0d14104808884070a03003c45c128860700d4000b4000450030030651f40c022684000d08a07501d449580300307918085441d00c61508440c801e810440d1541c0c0c541040c900c0111181002c02c41020500c1e03001c0d18800d00e00381005580e40314071004a818190003098940b0f02a00610a0ba00002e5150020b0751a6018000c0020882d151860340010b0305910004a0300301c281241050320b0259a100400010001d0030200b0030540e96892488030341089000c000c118000380b000e00113004641e1180d04103401c0d500301ba01d800b50821002c29103400401000b44030400208100c0a0140e080720740509000415465404101041000401282e02c2d488a26160081003550560040c401d06010394100c4c4001d40e2510200002942c070800d40c0d01c80d0848914044d18917028116a00740c00c60720a00842e01c820901c4805403446401c04049 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 183027419 1250 183026169 183026197
    0x604120f090501140c1b01030e010c0e090406180f02042009040b13020406080f010501030c020a030503040c030c06050705060604050601090311130615080c0f031f0b0f0c0c060f03160302040506 84
    0x503840a55806008901c0c050327444200030300000041920003842000312494891090301d0381808201402680ea02180d0faa81180400b40d90040e507030f0804283c0e1108d4820121f000c0d0385000c03040d155240c4000340403401d031554290f0300340c6008558001c010181c80c03058070a5600a0032500c00542c0c45e001840204014041764039000750340e1510000702c5c100c14205902c050b041c54208581d0b003040590100b00d0303520483c0c1c5414050748903100d50821034406481c1e0741005014081501c8041240b94101015240301485401100c8503617450b4030500040d200280c80041c042002e828040c000200c00c1c00c84004008800345c8500c0e95420104d9209080c0c0380c00d54030115082c3d6a60b10340c0c00b0302c1544212440d41c4040d08540c15450403501c0200203940d807000410114005032000000041810088440c0000700340100022380c80d10005218105194007014030300c8043d11a01485101c1c5050a01c20303581020030304100ca03821656098028041c10388110744040030180d0030040418a551543c0180001d541c000070 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 183028669 1250 183027419 183027463
    0x60306011205070c0c05060a2c21061503071203020f0304030303021b01050601050d0b27090f0a020a1a0d150e010e1b0a051303050604120f090501140c 66
    0x82c10441c0034606d82041e40030384010042d544480e9086143d500b500c000ba0100c5809201100395031006441001d000c080c0d1082e051810320142400c01303210415401005029a180f80d141e03d0682e04900c0c80c819002600758021a0041250b09003020800540a020740191811400700c4e0505070b003981d21a40046011a03404107801100755002c009024100607071600030001820b0201c0040c0181c0100170a0204031604c1c0c55241c0600d882d1001d090008040520080300c040052280c0c1e409000001c03240d0404520420300c600c4842c590000355406000d4018210b800c1281c1800b526040c0760626403208040c1e20350401041e07040e00818800c40d1401c0081120b0588004d0801142c00c03404801a408003109081c1e00c800c1c000c020480e1408170403100081300100390b82d0102e45400b515580540d561200c007840400b640001401008030341284a68401c181400c42640880c5042d00d0507001c4040d44400510800d00900c003e5018413845021072030f50040050816508104039894409540300031030045440c25 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 183029919 1250 183028669 183028673
    0x20d0b090d0815240a1e0201060b0d0c1e0804030f030e19020301150905040b1e2202091828022e020307120c020a05060306011205070c 59
    0x70003448248140c61500c0402424200f6040d0840030300c070140c0610070800301a0420014059482c80c207800501c403076030261199541000901650201e40805a0051544590401a40c03062041034140d8100d02c1c00c45090020b1800710000404100c610310f0103110102c1c5c0d0404981484103a01c101c40c2d8003d035502481854103182c000d0081400e0240c040a050030003080c10101034002c40d0443e00e403a24120160700e540b4040c00081d001d0800308102030100b8400d10804602c4680907044688940c2c003d400182840d21000402909a02e2800c01168116140c1d00450781000078031800310790000c141180b5070f40050403500000d4a80506450003403d0100c0c00500074901a41413100c01c0c607201340102c90140300143c01c1920000c80742c003140001e1140305806a81105102c017030151400403403403000301080702010303220040d5580d804194280ea0408461501740705080c81880e05601d281d0b401703030003031041901c3d20080c030440d43c001a10003818000c01880300102c00c1c038648a0a0321900c12907a40041301c4000b4 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 183031169 1250 183029919 183029923
    0x10e060702210313032c120303040309030f0c09050c0706050610020304151211131a0a03020c03070212010b0a05060c071e0f090507110d1409010903020d0b09 69
    0x20104000c110302e01c50740c10502d01d02c06003626403048451400b596148160700d801ca0384000800900002c2e100d4003031080c601c081518200706a8580c003612450032401c1e20f4108942d40f400101c0d001070005054a000344001044000c10101003031080b031004000c01e4440380c2c6442940c80445146600304400b007082c1e800e10070b03140101030300032206640004005005050094580c413a0b401500d1040452112450805105006072115203902c1801040114a5107400c80515401542c1d00340702a6054400030541301d0745240c0c2d41039030307881004d2000c1c46c18914440c01d6000c2d401201044890340414003020700903840e013885401101424900004104444104000300d0110540000340240d0060185c012201c0e0300007503a00554000d044810051070b4071501e49019010990003005003d6a010800910205a601301c10f001e80100e480705e4900d85880345000d43e0303450600134000300141d4038a034800c000244050040800900601d4915220750702c0b0b80124440c0e202c9800e080780c425800c1002c0040403401 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 183032419 1250 183031169 183031183
    0x51605070506040209060a18020c064f060905060108011802040b0a0b13060306060c030e01120b030f03030103021203070c0308030a091e02040b04110a050c0c03010e060702 75
    0x50402a040524985803035035902c00081c4000e00450a40010079101d40e1090345100042c008480101d01121007408080b0103904258003460b0709101d0100401c240c148402003090f08039455040e91a2251074002c034604c14a15841c00d50f956201c00b00f0381e21461302c01410510320000d4090440400d0b0361146107040351912405a0000302140d2501524003110040c1e60003ca02041e0110360204000030071100091810450342c2c40300000110000d000303201c0f1007842c1c00036007c403441a14200000c582c0c515082e14441c000000040000303401c45086400c541c0a50711110301404100c0000400980b0344d00401d01d8202d40070343c20002d139400440100118a8410100700388140224059030400c00d19544124400010340170041c103100340800010140403003640240c40c40743d081401c03803412001d0360a050102c0b13207070700301d040e4080c81c04d00c000d05820381058010782140c112000f52441c03400c401e44d41e0444032600140c6042c0c40c41d01660311400001d550074041c80c50392aa402003d01010b080030311700603140440c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 183033669 1250 183032419 183032461
    0x711130212010e01060e06090a05040207050d030b0604030209010b1305040c09031709030d050a030b0904030801080d0306060f05070501060302150901080a06030f020d0212070e070f0201153605 84
    0xb0f00b070051007580c0d809503145c0313080001960426190101400011030303c001a401041d000b5102064440c244040026600e03070407096603c081011242003424400503100d68000a0741000102004002541220004204008503500250b60036a1201d00041c25194007889600004640c00c0062060042459810480b503141008803031900c051000400c1d02c510444481a05000010880202d0980240c0180f1001200101005010729040c680600b0814081c059040c45226043c0e081300154064842e03002503440c1e0b82c482800302120300804450700c0c0c0c8aa4012035a40d52030703420001c01030b110b000e40c10044140d0700c2a40c0d9103a055440c001040c0d410000e20118503030341041c1d020400b00b82c0f550511103c964040c0d6030940910700720300214080b02c40d01c3c0d1003442e4500c903030306000822045c07030003025020740c80a5445034008a84110704038240c80c0001a40051065102030421000f0410b01c1c012a501c200d003e00900c910340c0c000000c5e44000380301508440110340b00c07400c11003080c0502034100f02c0c3c54 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 183034919 1250 183033669 183033689
    0x61f120b04030503040f0c0801020c0c04060f03020d050a080403080d0501080102030f040605071206180e030f091504180c020f0304050f0f1504141f0f0e03010209120a05010606140708071113021201 86
    0x500e3f241c115850b503031452002a010340680090b0300180401844881b1016402000b442ea5682d80d0389003150300303544215200c5440c640392a00110340e455040c000c89015880300206802561525211440200000f40030b0f6401d02203840444402c95000d400b41030006c203440000c0e10600d40a1100f07a1060354182c180c01006d17a00100800f2400070403080580e15020380982d034410083e244604003040a108a40040046201c00b0b50790f580c0030402e54003c4211140389500b660501100d041107140d0ba8011030003030b150310840c0100000311605000e482d44042c031030000c000224460002c00c1240c0c031580581c11400c00909a001d03184401e0400d009020f620070704158034140e81404c1614010450004490124100101041001c030242d80c25019244114401426150104090481a07540e81003c600803560365090100000780c40740070f0f5503070030f450f802c101c10303890326048541d40c40450607030192030116035514041c195818151500003500c007102144010050b0f070b600f4403815501c1c0c4458140d00c04e050704 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 183036169 1250 183034919 183034931
    0x580c11070e061e0102030d0207060203071205091218040203100f0e100603150b0d0b0901090504020a0519031b030203013e0903061f120b04030503040f0c0801020c0c04 73
    0x19154001e40c1001003000e83d509000c40598280100c0c25445410074208030507002044c640240300e0598001c0d8062030300781d1100c5e0b003244880d0540d8015034000329814481908801c070b082038050300940c010a55284541c01500c840d800c200c00160880e001524458640d042480050200c10390b115050b401600c9042c00e802e46519041b44c28483c1f2109602554041540716604404080c40240d455005402d0b907011090311521084a907400420f0501d1010344120520f10000526036514441c841c0541e0300504000001401d0105001c1c002010107440700450017000c80000225110443c24000d1988003003811400c6441c50040600750384815200f00a100000d040790007400d030561ba940c02c0700035407840c10044805002102d80002c2d02405082c0d64044c0240300402030703c10303000c55500c5948410207044480b03840e01c5100301154551b004c107000b803c801c41400820086070045010316840b62042c142c550740801d45a43e0800d803002682d109076071036900404c1d05a540c2000f4044080c4003a419141040700c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 183037419 1250 183036169 183036181
    0xb0312210703020f091e031e160e040b040c09020403030203030414010e06060f0a090509030405010f080c03010b0d020712020a0605060f031504030e0d08580c11070e 72
    0x510030014000c1c8540c071002c40344c0c80c1c00700046d40300146050005050701c00386083c10f095551f040e1a00d81c515a154004c003402040400c0742e821039042510601100c807032882d640c3e07658016410170080c00035140742c10459400141d010381800144080d61103135019603201e041515004403040400d003007089050f41002c00700c001c01c160000c2d101c0d42c420002ca4542e00b076140300b2000314165542903004980701a0420f0308010303c0901c004010b0007141c00c00e907920110b041443c0c0e0112a201c90a54101c420040200010882c5403480740213010020424800149007111a40d0340d140e021060304c0008015030003107900541170144500c180d5611840603124000300715485400a5124864250b955a4080c0350343c01080900d80714400006800e84054000d050b5001241004c0d0300c641c004102003002040c2c1c802203003241c0003d00d1090885004000c00b60704107130340400d01d05501e0b04a1070f0804c0c00f0716854200000100102d6016280c00d003003554807125160596005070f07900f040c55641101e40c204d5000024402 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 183038669 1250 183037419 183037447
    0x30501060f0608041505151003051801091203020717070308040201080c03010807050910080d05030f0703180201031802090a150b0a0509060d110d0203180604150b031221070302 77
    0x45c036502c50b80000440da074071003015941c10140341001799080b0b410042440541d51309903020314041c006412a0b02da1106044100070709030341d001000140603c0100955014150003034002c1c0001501c12040c061100005c000b03c8c0b04d1035000740d903058000400080910042d960048800351f00404501000380c955814070901c2d5607148041c3c0b080034001c521010004d030b46149801d461001070504c4005450000d4003510f00207005030025140d8580405054010070750060103442402040d0601c801902d698076010340042d401080039040140301e00351160070160040e501c10010922440e10400c1c0055106100161010350341480d8000440a1004003c61b200d22600403041d40c4010705c0c2281c25684d03c5005900000c09001c207a188a0031404000c00d500c41c0c164001c1e0003951060500d089800070101159030104d0361843c0580c2c001d070061821307a50001d01c400b440e4100818a01e800303021114503408440860742e6941c8520a2940b03041c2e085403101c01d031800503915698000d11030749010750400303600e80a405 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 183039919 1250 183038669 183038693
    0x17040915051c030206160905030d03050711060402091314010507030204060f0201110922050405012a080c0c07170a05010605031b0409060b0d1a010f060504030b10050604030501060f060804 82
    0x40191201080358445106040083c080d20002c9c09490310841003030b4000d001780000f5982d000106107210a880c411802c001f07059442150014040c581d0b07501d0b62070380c1c1e85002025102c02c1d00d080106c50b60b0902c24007070034095180180599a00165561300d00b00009040c1c8000c00d05600441e410011003580c100035110076035080010445480386541d41100c02c090804403080d0071062118206410001032140c1036006ccc60710071907044c0345184400811011708409030a1100c44002241e40040412034044525001e40400704031241201c142d40d898908109519a95003006005540f118a03020104082030240351300070300090b0010001c0c21010180114400c580b480c815000f10341d40d403102014801c45030041819844042d080c0e201605203428403001030300c07600c040e50300d19100d1040000740ca40121403218040341c540e80c0c0c80506050550307440c00224003005c0c1030042d201081c14000709090f55140c0080000798402c00000034410302d031035050701c1300782c1c119400039081c400408100008501c4c2e1403035075 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 183041169 1250 183039919 183039931
    0x60906021c0c050601180f0b0d1b090e070513050106301103040219080c0405100308040b0406091509120c0f0f05041404050a17040915051c030206 64
    0x24454114801c01111201180e0001901c0342c13040314000111004800500c00090100a406210b2010785c3d0030841c040d282c1d0810042c0d08004803401070030100d2032080e40554452062249500b1465440301100152400742150081c0c9030001603041000e850038035610790102e482031609200c00c6d8549800a40986844c122240c664810502e8070001000601481507501c1440c0008000ca500a10440c2015800c111400c0b8086c64034000354440a54014a00008440140d001441030181c90028032019000141c445c030301e041c84012022001a08072000f07000070b444038581b0552101e18125006021684c0c0e5808824048696840c440c4800d0340000d2030405e8030b50b000d80380300e28050585008210080135900c20010501010000315101079010340c4401211411202480140034031b900e800320030342c0207480003000e96010060302000190652540b0010300720f0700c1b00f02418640c0c0d0791110b4068036079107042c0e11451080c400e020700c824501029100104c00c3c154682d0403001e0040c2e03901a40c1c2d81e43c06084 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 183042419 1250 183041169 183041203
    0x60809071505030c22050301153002060c0309010206010f030b1305190c0503010b091e090f06070201091e230106050d050109060c11060a02030a0906020c0a05060106090602 75
    0x9408501320b08122800300c0389580d11624109851040d61a00c80214040c613482035003061129500c03060242048d00030740701e1003c06941800319090718080c0852800c46a104071103940b02114026a0750900540075508048000c2c2d562415240002803d286058201501c0410103c40510101e401d2002459220380560300360344c000e100b40e08105150400072045c503520174840700d0b80d031020048000340d61b0007101c1d000e400900005220a0400a20b00003c90300084000200c540414902d442d482e030403500a608482521030010800346407a0030a1000c0b268032015079141c041c01c0d81001041001d0795141c0e48401c1004040701501c0c0d64084d04114120303040725492103500000f554000b020b600000003404010035511074000c00b890005c6c007030050401c0982d001440c1c03201d00f1300c200b030044a50b0301c06003091801511165803a243d813a00290000740c8120801903454a00340c00144030351004001c3c4541041c018021020245441880d000c0141c008608000b4030307480411845800040454454803c905 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 183043669 1250 183042419 183042421
    0x801050907050a0302072f01110c0906100c15060e070f050d1a2101060902030103080a030c03090206030112020310020901050a08040f02030604140d17060d0201030e1606080907150503 80
    0x8150b564070b0909841036841e0035840b10140044d840d2a45100c0b0591f90a8940e0b00040070368040301c580311101c046007a1303001211000081d68500c0c0103180c5001c40707546410003460490542d100e88040d210010406106035a6131340b02071140c440221000380d4001c80a24090056408501c030003080f0340140c014500c1003540356286c0c0c100d5810000c15400c0081d1003e4941120007070213071600c00b4504400021341d2915481d0030782c046005801802240d05890304070040030714002c003c9030220004c20002d1100400c150b560030743c290040c1c1c3e580004600801a40034104002c554600425003420780000000a1a61040011300d0443e600700d8241c40780904141802c1c2d450380d50700e09111100041d0188001d40c1070243c40200700400490b41da50541c00400784044610507002c9d0324040c0d9101d40410304a02c000380308880040e0480c54251002d101c564030626000c00d03d000c100c4000e61400c140354000e1030075040e69150a01c03180358460302050380100204000c0030b0b6240f5040c40c0001c80180390450f5010030070004 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 183044919 1250 183043669 183043673
    0x807060e150f0c010e12070c0f03020f091e040c0504051e06040e0a02030a061b020a030206040b0711100209031002030103020a090b010c0804080105040309080604210e03030301030f030801050907050a030207 90
    0xd03000b40b8001d104401606c00b8548907820f0700c1c410340e109550031144080c0d101004140c244900ca010415a54050504103004684400300002114020807201107100d0701c0880200108c4410445400b90384180d40d110822420401000180e60005280052454079168030440343c17010045040e03000703001070f1000540484803400309402c2c42c0c03546801a40500c105d040700000c10825500c102e4400d400100d0b00c407509083e01d00105e803100e00681d000f0380140d102202082c0807035a410146508140e250030151178520300f13800c0c4242003e4007031880c0060141c1c0466000818101444580c510100d0319200314990760465000542d1042d0138040d501440c0d5403481c801c1216405800038002042d08110320f81d440300e82e1410080c0c060042141c0803000580900c0c0d0000303030840c0010780d10f40a5603024480c0e005003103607540340b1840c844e0351004010810030f5041201c04261003d20046001e5400740302c040d4907841ca1420060b1020340184d00c0350340201841d004210301c1c2c1d507005050f02c0c50000d0500c1c1c050303a181014 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 183046169 1250 183044919 183044921
    0x1b090f0f0d0602040b04080705030613060203070e1c0c05010c0515060d0b01030b10090209010f14160303060e0603030f030714040e010b03040b09061605031b040807060e150f0c01 78
    0x1007440201107510008000c21483d01c4030303003d8000c80703440c07c0c101c0c3d042c941c0f10414162038041c01d0f111000041e05006d0000300081480d0081d40c2e201640b444c000441f82c4800f400250400b80e516101c690741c010f086030080c1881403135002c0d00082c02d800e00344814040941c0d0750740e90f070790941c060081041102c100c001c941903a6030700d28145070f09078110041c01c40c1561603080c80c044100381611608039404400340c1c0002c0f521002d000359002203905845e039411a0101072425281c00ca2002290701400c030003040714001404c0e031003801c42d0030703c1c1c060780d0000b560718208440c00c002e00d4805080c141c840e0340288142800d800c1c0020403a40d00003194a08441c2440c0031072a850303020300807030300030710b0a40341a600003045400041000c3c40c0b20701d0040d80507002507203448003040c1d21030700b095030014240801c101c41c01040724000c000668200c1c05012b488001a0041042c1607560b0700b042c1c10000031504419000c02c01507a001c4070006500400f202c030300048001c01440c6a00340e02c514041480b0000c80450031000250007 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 183047419 1250 183046169 183046189
    0x60a140405030604050d0305072a1401050c0d060503070e01060f0903060f0207031b0507050d050a0609110108010e1e0601020319031d01020c03161b030302061b090f0f 73
    0x5400c650f840e0400c0d2810689602c961051400043e15010025544910882c0011400c404552050b00030481c0580b03940200c924842051b00c00c6051500140ca80b0369092144c1481100313000d60480e100c114107023200042d074645a1080f88254012002408091101d0780310138115056800c0c1420701100b0180c05580d0403120364009042c1074a4259a1204020203400902c8440d01c00e0359220b60400701e1654282c98640e1560303000d00150310070300c4203000b2400d2414031000c0392405442103814400246ea82d07581070f80c040100c22034402d0384054040c200765810040749405040c0140d142c607440e180510142900300040052751a005120300c01140d0700d40d009004540c03004caa251018800e14002d40030103030242540315444000350340c43d0200107203252818820b0310541c180d60406549000c0c4003101031a40032000c201d0550710440740780180401e10300240c60100040d171207030700501860310300f01840d414403441580003142c184d0004c029200d507581e00c03c103038610615011142d82000300c2590303001c0f610281e1 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 183048669 1250 183047419 183047429
    0x6150a120302030d06120302071401030914070807120b040605061c03090807120302060406051506070308010603180203190302100c0e100f0801140402091005031e06060a1404 76
    0x40140c614018140c0c084000d0010940a035018064180d40310b08a10b4424481400500160000d000c10b0141c99549001094140814174000c50919126201d840c450015100c644110f54420581005054410f1010350000d200315440034980501548800410201c002d000906040c2c0da17a0002e0481d0350390042800b081e500380b07240c00c0107a64151401501502c0d0074041e4007081c0c410188001111407440155181141c0c1c03650141245803199500c400c064a000b80c94800f07a00902c1e10304a03101d0f1200d034040c0c61b2540c000c0e03548042e0355142c204098112001410071400b0840c4404100700980c4000800e03410340d611020351054070440302d090803401d03c11a440d00500c201e082c12110319841e50301c842e0030f480081086504154054210b0400e42d0b11120000d041d1005ca03940c0c034010407076521240414801c00c4000303007000d450103504100144800000540e014013050b8040b00703004600d9800903e610746510059141092070502c0703000903500340185031403502040180301ca5000d10040360340985000300 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 183049919 1250 183048669 183048689
    0xa09020c1005010b0d090812090d09080d05180604150503011a03060a06050d0b04020a02010c0809030304110108041110051b0706080114030a02043e041202011106101802040806150a 79
    0x10401400080e15100c52003c080c0010790442f60101e042600420301d11124482e64031540d24203828ac1c1c03464845074001d40c8000d9440a01440002255110b908601c40c01401a60301c2d00d9984d814000e40304100c1d0b43e248101105490140100b14840d02d400240200f80e0300c0b1424000c1d00c07003401c4100500640039141802e40c001d8004503200355140e0b01500850340d40c03101a201c01140383d84151000e6030364081141c1c0071748190104180c07120203500460426030841d0046440520b110b0b10200404c3d6954080c140c03d4002410000386282c00c82c101c84603405d412048040032301921490544010712a11041c041c4d0018041c13020030712041c40d602007080804d200d5000c0d20034400d07540c0070f025103030310403c9150805031002101c10141400c00c00d8014114a4a04940c8a8038203107400c002c0851104613130984c00302e05012001300c465a924000b04140c42c85810301d007410f01065800d140010124080d100c1041c000d05005100500081e0800704805611800c44540141c14982500006a130400290700034a220 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 183051169 1250 183049919 183049921
    0x50d0f02041e0c0c0206030612030c070324020a0c1502070209091c0929070b0906010f05040b0d060510150f0f090311100302090a09020c1005010b0d090812 68
    0x50384a00442e4458415034500421a01110035815201203061041c000d50007107017000002d40510b8201c0140d00c10032800c50440703051045807004540b501d0030719041034610000301385004190013948030304480d10005030403065082810303e04c8003800c015481c0b00010300301d0001d01c0c0e040e203010000e641500d0030640c0081c40d1054604110620300e44852600c003d851845640c140d00d25002401071000700c3c101ca00e070311000c868261b500008806003000310b46209017103c10030850f90010411805c5e1980c041c04440c00a00a2540741422440350b800300e9030300c058040c508007807400841d59140f4204507102900110701181c2c0355600c03d2000078250341078000d9135601108404402c004c030f070301c80060a010482511440b920004c0c1003020740309214141701c0108030240f01900030425041240e00d44074000c0c0581000b41c280301245000400030302c020780041410075800708492074140401c100300784500450500401955040a002c1500744c0309804400e4021034480000404001d40b5404540c440021480b91000ba = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 183052419 1250 183051169 183051191
    0x12050903070f0816030f1e08030106030b0108060102010e122107170907050f04090203010b03010c12060b091014040e0a0e0d030b03030a0c06110d020c07080a0c050d0f0204 75
    0x24029480c050310500d031013401603480c0d442841c40e680c0f10a4940104025006c0b201c0344d81d603140c41c0c0f0b4101c0e201c111004410402e00303000030f442070060740c043e20300c0e42c6000c50302ca0054000101000c1c0020325450440e0306150000c2d0342d0340c1002c20745600c04002c03000e1407641c070010591000c11520801c1084011f1007180c80810090550201d91051490101d151011264403044540e076a503110502401da840700d6048041d410304d25040d03000c50840c6101800204400c0d0b00302d00042e08440f00900903801060603414000c1000002c0d22540000d01f21a806441c104a0142c0200d070710740340d000241e03001740000114203142d245890000c0d2002810713007040c1e1400314035111126001510f41c0350148001403059100b184026030003401b070404803910107801503051000c40070048801c003c0b080340a642e001e0340e0346940004100f0403401042c4c0800f1100d000341c2e4602041030315a1400c5026841061150001c02c000740000700450084030488000700e5044002250606122003403401007480203600901d45248008 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 183053669 1250 183052419 183052439
    0x307080d02130902090303121f0314012403080a0c0803190615120b040b0603150f12120714100b040b040c200708032d0a0c1205090307 59
    0x3403030b42c4440b1501ca00d0696440b907400580c002c464031594550010f00c0312504968400303d10300d50181c05007581d4110b03c2601050004182500d41042d650000c40302214561314901b4020944500d981055a0281c0003d0000c051a00009404014002100041c50f02125445a85803c01907600b10040c0c594134140121040b03078a5045100501c0001d0800d007002031141d2400c402242c0c03068064132940b40b00040c2801010041580c240c2e100c1c0d200d1b070b4610100055031601801b0b0742c450b146201030303081c0f40e1401c5c00803c000048032482440c442c00c01c00058040d02d204c08985007078130748880440e942c0c5810709407400e01a1402c600c1c2c40c2016510642c00c03200c40908068010404182058608000440c5e28034184400e40700c3c611080c2c404207058004070004044110b00d40240b00130301c6403d403841207444034140c3e811355000850146520a002d003c2d0740107004060420703171142c01d20800a501d804102900540080c940103005814a88182402c50541d40980d0032596192401810b40c0c50090f00c903001d080c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 183054919 1250 183053669 183053677
    0x11104090c0801050411160c0f030309031a060a21020904050d08010902040501020a14030f120f0c0412030302131e030302010f0504030203091002030906070f150516110307080d02 78
    0x300181002d40002210304091042c1c055019464400e2498580d201400241f90070403544204c0e1842c0406100181207680805588090b5100f0fa41d540d003658614101040212102c058840040140105110300d683d035008080302194030409260b2294035106140c000b51052212001e900201000304000400001050300c0301514419141c1a0b01a41c0354401c01c0c00701d0040340103240c0580d00c0100b042000c602c070401c080c803588403a0b8040b40c0c030784040c1049503008d40c3c108202110020080c07100b80310201115603240340e80701e002d102065040a1801c0d480e070b80050b05490b8003409056001442c80407030145c102e40c2d100504045081c00b2221080d2015540c0d04004610042c3c0040d40303403060032a6100c40d14060305006580542c002c50400391200100290b0800d2007040303c0941c0b000b00005240394580c880034007005405050700040300c40305420b20100d644035860600c40704914100800c008919443c443c4c283c11074143c40d0101196595a805500e1442800805030030180302044a03141038042e60014 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 183056169 1250 183054919 183054941
    0x1020403060903080a1413051c030207020111010e0604080702031e03090a05030c090403050a09330e01080a110405090a060906051002101107060c030b0a0f03020915010201110409 78
    0x1104c03580d0f252401302e42200c1200c1e070000c00d54580e0b4808200718040e491064034030503000b0000d443c0d801130350aa100c2d400071009000301c03001c00d40114501c1305668101c1d900c6420460988002c1c4072185402c115103885200c0108000d054103008038140065440401c40d04c0d00401181c0d480200c0c18082d84a1190b603904100340c640d202d05c511580206a1b07050220316a880c11078060300104040d21596800d03161034220050560422a05140016800482802a0311041c01d00110341e0902d4031055440714005116442140500481e220000b5960364402c1c5404e600c80343c40c1e500005c140501e04a081104d01c00c617844160b008500b4070500131400c0b203035482001122800b031010420103a6560070701080703c00c860254805a004100c81c1a40c915054006e1410080c0e80351040c0c0c5041419540c4e441200d9903440c8500c0001c1d500c1e104843c50341410180d070000760001030b92000301d19107143d0000b0340341200148040d14022002c4d04128082e4001d4010300101d0166286068603152250580b034010540b210403 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 183057419 1250 183056169 183056177
    0x90a0c210609200612011406190f080708091b040e030a0908011a060304110a0b07060207030306051516150501080307030201060608040b180f03040b120c0a08062101020403060903 78
    0x468800c3d071500408035130700512044c3c0040c0da2030303103083c82c843c002440201c82c05820920400901c00e5000b0748403841c80105540d611a4064501d006d200140369002c014070007010310102c0030600c0f01143d4005009080f068201000e000303000c81e0180071401518076101006120720010903c22703082a003155015090381c8403032000b04140005450b00b150b031006c9443c030b0241c01c100200080780105541c0ca19040c0c1c0c2c03441c040c0c00713408200e5680c511900030754440704080c1c1d40550701049180c01c02d5407501480d001484103c40c1d20b00079440d465244035035407083d04e4039004288a002c1d03d0400300010030310040e5069103d418104600c1da542c0c40c0003501c9510144048006510f42440421490301980c030550285403c100c211413160313102d0350010181b501c10390250000d4407451854200c43c0c20101300500c0a04910f42c0c10300d0312460080841a0065005131a0740c4003c0b07800d00500c05595400703016240d10003070441c0d940310002111a0755108803101c0c0080240a03500004010040c400b2a800181400d4425a5 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 183058669 1250 183057419 183057473
    0x40e1209120309010903021e0604060f080601030903051c06050303070606030c0f0e06060f280f020a1205030619090203100608040c050f0303090a09060e090a0c210609 73
    0x2025070340700e01c60b000c0d0711130100310b280200740090b0038492146410a0350814681a05e101440d000508603002603014030005505190f204511750340c007000d51900f20383c003802c0900070820256030181040c01002c0b404007500300750102c0e040e4284100d03080f10008103009403c0c0c03aa51215401d003800540301900050301c40c888064000110780d0914a68401201d10f4015079024a4880008100301c40d40205814252180140302c2e40c43d0415822055001c0030400c1c42c5115022040b22002811003d8050081c805540080803c08081030b6584400d003444010b40c5000e1356aa960040054501c1c01e44410038107034184030351008201c659465000390701642d0a0400c0a880b20703543c80f0100d1300107004840042c02c030501910100201d0400082d4104000c0300202500d017048000d002103400000c040e40703c036014540f510b2080103c008040400c0d6080641d400103800222000c0e1640389644500b407146002e102c1001c0720b4001e01400a610040019610640a0107140710605111801409602d01d01b009400c00360 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 183059919 1250 183058669 183058699
    0xc020c0904141c1413091a04111204021c0f0507030b0c030103050a02040b030c060706020304210503160210060602010c02060105030d1b17121608010303080103020f040e1209 76
    0x15001e00c60074100fa56840d009041a0440004160000075601c2c003a09a0744001140710401c902032501e140b80301c080c00210340015881080242c85007481c000d2030b502c104105610410900a090301e03485901a500c0024800c050524103080105030807014050030110010340040180100d28102228026031500c106502c96500a80441c4400e1100400581c40402410300604150b00800326801008040c1c1e600c03822280e001c00c8481e48200e104036141d40d400000c0200700f00300020700440560254500580c00b680141000d00326100c080c000010074401941c9060156200b0001600071502520042c00790b0b5a0300c20300607001e042c1214125015018080c0003090604001810300d018007803030760f0790840c034122828800405210780c403008d0702d20216101d15074015080041c028070f0b80119025003161280340c50310360b1000a41442d004e910030004288010000f00f54889401c0d819241c040301d0000f02400001c2c0010014000b0610503d0a030041004464810380b003540980000001030700d00d02704c620030359 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 183061169 1250 183059919 183059953
    0xb06090705120915070203070201030f02040b0301051207031203061410050a0e0409050a0f1502070203030d1a0406030308190e15040213050c030a0e0d020601090c020c090414 76
    0x1240c024000440c14002c201241d8034002030550007985880c203407120800070b010034920040040b19440007580c80043c106d0115689071195282d6501d800038110b013010705100d602c0b2880e12062240a2041e00c0402c2e03840d10b40207040c046500115403000e1400c41d0020035603406006000f4610946000782e01d0304121a4072403c058403d00480c41180c0d41309440e143e03000d0f0302501d150020712549034004ea0303030b034555034002401040758020950042c29914500c00661404565106814100c0403d65005020344001600c0c000140c4200c80341d06140840c2241003180401c541c00030102100e98000d0800c00c001050580088600c1e015000d101301c001050f00c9030071005401e0355461140d0b01c03401d5000000c03007280c207011008160b400c1071008024450440503042014103541080e6030054202c40008140301c01200e0600c13411020b0395212000d000020480b6402035242e480c148190a011622041e100310382d14402e111100740300500500000e9072782402d083c501e500030480946a0b8003807186c40701244014000b = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 183062419 1250 183061169 183061171
    0x6030603020a0b03161209080f122436040b0a0b0105070204090309050607050714011412041401020a050301090b0d0f03110106090e100b0402040f0b0918130b0609 71
    0x1743c0039000c143c0300141c42140c1000d02c1d0604a10290764403400c100c00a54414000c3c40e0742000601403540b17603601c0e01c10340e070a00072015114500d21142c00506c204807075016882400c5a6008854050103070b001c0c0300728940f551680814280d800c030b00002c901c40d100703101d01c820300d405540182680304403544c99040107030884a1206500b400300ba4148400001440c0640000725560310900d4007071900741d5600d0114007140c0040340c017262560403400082c00505503007111465402d6091810016424141c803820480e4414034070403031640d040100025080c45100b402d0056a54070b1140215508c120b181c80081c919002030041d011414240b510030301c0329180680320802034036040005208101c00a5409880304803400c0100c1c0340e0780d5254107000400d81c910f132189908260029001e03000b00001a184203044506c0880c00e603210718814482400131007416102a0140d40c000039940d0740e82c00b1801e00040c64a0070a42c030a80445a0560400000c05c0f404d502d0090054402d060507141b9485d060100028004 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 183063669 1250 183062419 183062431
    0x70507050603191802120706030e0a0b360a150603080a0507050a050601230409030503060f061902030a1e02060a0f15080708100b10260106030603020a0b03 68
    0x454001c0b2500c02c01c0700355211007003440d503184000411300800d43c08510351414907501c0003416000308030b042113a55054001c1140d481c101e035015091036000c0341d0b22409940030290641c0c2d1160615600c1403820541d610380c040e00943c0661103420b030001000310059541d2a8140d044500648620245101480e00c0c0101416039030702c80c54031030800f80c0c68541150b01f90002a0181c03100d210f074488083c0422400d000351800b8003800b110310341803054100340c05030440d8284600740c7e00451a000e1100302007540a020380350800403c071190204400391100090150240c0e0b2042d4000405a003007a101e59500080108000603198072007407908080710400010303054002c8017200c0907802070400104106e81c030340d0103413014200810340000c406071000c0d4180724504403900b0080c925405841e003440b42000c00c120300200d000e1006010300c4000d000d0004940101c114903a12402d01c05618802c0408190035448103046240c0d442580d181507940d0200280904070900c07050780503507002c01c0c6c0030070210804000c8900c0b0708 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 183064919 1250 183063669 183063691
    0x90504060b0f0c0a060e100605010e010f030e071e090c02030f1204140a06060e06030c01090e060604031a0103062012060a080d03020706050a0e070b0d0209040c0302070507050603 78
    0x11104140c8000b02c3c0d00c0084a01900d004000081e0002416841407800c4484160300500511252100170030440d00030784c0002e41401155426404160703407024402002c1d24580c5008640c00700c500d0401d901e0188590400c00c845903210342c10420402480c3c09440031100c002205000e45480c664090303840e403003041606030910794200600c215404490500a80080c85411044503015004100314200a03048004072005a02c6000400c40359005403002500500200c001c1d104030b1030400c1c0060a20f15585c03250f5600f4058110000c7c2da0b92350f9038415180115000000103441600c09218029a58000d0100b210b1140c90099400c2c0c0034805901039104802602400320700d03245107054100c5440078001c01c03c1c1c0c1d002d01d01c80c601043c0304406011a940650142d01e015880d580c60b407a0003419504010000e107609803411541c0200120006011022100c801242d00d0f91446150003e2019200d085005134110b1f0610700c2c406100c2c0d42c1940100382c0c0754001c005490b6081d0b1200100512448240e440710f00e15 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 183066169 1250 183064919 183064927
    0x10218011b030509010203090418020405011a1b19030206070809030f0a1b05010e031b06040203120f0403060615030c0e03030a26040309031e12030e0f1c090504060b 72
    0x3d0058009040c4500705004880c10402407100103000d03213000481014076000c0380a419411410310307014040c050f150030382c00b14082100c8602c034401a8011090b001031040301c02d00016100c2602030040101c007040c001c120315520b42060501039035031442a61804009a12040041d041d175a02000380c4902046006459180509120f4102c80c13240b03015191b44410080c0c501110001042403141402d030400c0380c1d0155071a003400484002111400041070002500700404020043ea0b02050310100c551a01c5003840e01c4a15480e4200c0d0030303015903040182411314004001c02c01c1d03211071400c1c5070340316410798062103d1051118100e803014955a2240d4055105015003881c042c05041400220300252500c0c00341a010070404400c030341d00690701940461502c000520030311075041614104580d0350741440039080c61a50b0f680c40c0100b09c0c148660109a600d0b000b00461072001d0040000555418089540e01d00c3e25405407090300c48030441e01d0303011580c0d280000074142402c0c001c034811140e480800e0307410 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 183067419 1250 183066169 183066173
    0x1503030c021908010f0606050c0d270311151318200a020d0206070c0303090f120e01110a020105070b150a0b0d060b0403020906150c0d02010218011b 65
    0x18031800400200d9010070038440b0700d150031100307800000041012000100d500e0000d030741c0d81800c070350060700504100710041100d880c031800d0010380d50044030701c145070000e4101500321681c03000c41d038901c071010200d1060f4103000051003821180c05402040072506104440c1e1912030040c1144203110020b007022008a00c01c00c1414181c45072900101e004c0c60740070484e40a001c2e4841e00001e0100c952441102c1c02145068460390b04011007203455036980028440c604003a540503005040950000b410140c80d000f40c001000020142820030581c0003102003617042c0042c20280600c4002141e00c0e0001c1c03042509002c08000c00148088100e8040e1665460098030381c45031140e59038010000845d1650300c3c0c94158550b15045134000045c046091b110742c442e020214a0400d80d00c8a500902d20000305000900140e502c092405400a508480154142c2d000b1580004680107514036031805016a00d0500d100c990190010070201380040c1d2120542e082c201d00544443d441c44044c00f041d0843e002001c00 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 183068669 1250 183067419 183067427
    0x414010c020301020c030c060f01050102030a120c0e040204081014010609090e01200307080a020405060f1806041202090901330f091406030d052d0301030605010810150303 75
    0x18285001500145c901501c2c2c600a51450703000341880e0515612041c10040034802c1d0150007030141c442440518074140800d04010003100003104420100c80c0c2e5980d24411141c0141d0481c6e41c1450040c10a545070391741c9081040e118000031040140e0f5501300710401e00c0110300860303100e050b55110b0321100d181d2401d0200150080580f095056280e650b92001035240c240d00a28040010700000030450b074a24020400030304100000c2d1810307442c913006002c14081d540d2520255040341154068540d25010401c601c0c01f20300c0041003949410003c00034011a54407080043c004d90140261140c14150325507010f8103003203540064029080e00300c00b400d00300018035080d002035284920840d014690700d40301c807900703010f0350b10179400014942d96404000c952488000f903050760002089024042c0c444d8620f0020306280f00760104030003960301d0403115056a614080b05601d10407400c40c0d80d00c0d01ca43c0c40f4078010b03000341001c0c0600308241c032070440c40c4e910381100c80c040c2002000f4900034002101d881d60703806403 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 183069919 1250 183068669 183068687
    0xe06040f06180b21031b0a03021902031e0304080c0d1a061f02060708160206010303080703060803041503060806190b01030f0e06061002030903060c0d0b060c06011a041401 75
    0xf903070240c3d80e40f550260340441844080b00c40c002d014065541e4403420140c140c000300104500761020b81018020101098011400c0708005800c520441c02d0b4988071301c002400d10402035070300b240e2080741c1200c0504800c0300102820503036204100304e8616000100400c2a802005400101185c00550034a02c40c02c2c407501500d03800c202c01030300341c0d507001d060710319000b089000520031440103a00980420589550105009412134104131071102240d10290b070080d114841400040c003400500004a2401d500c00c2d40f08800070184a4180e94039940c90310740c0c00c3c94400081081d400028244807001c81c0040c00499128050260181491030245801011300c01810070100f4440c14036076103000f0403096100b2805020120302035030000e40b41034a006010016240c02103800d0004640c000d009041261f02c0c0002e203690002d140c01c24840e141c0803198040380c0582a0b01e2130540e042580441c00340c4400d0f600140c0541039480105640541c0c400e01101305945001d24800d0002c50b400240d40d00c20380d0b50080d160a = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 183071169 1250 183069919 183069941
    0x6030921020c031903120603020d02040c021c0504051002030405010206040f020301140403030902121b0f0409050a12090504110906160b1e06030c0603012c010e06040f0618 75
    0x42c402e8512042c00003410207200008031640c01d09040182010158415035482100251000c20071955007140c020031102010391400901035039958001c0010b0038000c025000d00342d06080511500816010340003451500a0701c50f243c00b80480c40ea42c1114a4004030684d400e40f6410782c01030549603226111340f49161241d240698165503917500c00c0701c0c4140014401c0b880b4034082d8a011610440c1481070100a840c054545070060b003000d40c070701c154020500300740019041c0481c0c01203e5404614001402007484610040c094031841410004021015580c07102d00005919040105e60b903803020700c016241c138015001814907042203003042e40e180c5a0040c0484200e215603105840d1081d9640c00301143c41914080c0300030b081c0c0400c1e01c002a5038100d95651000301078000d00038041c40301c0040b07817840c0018007071500c0d14810751565000c0341511100380981082c3d40d00b8854010350f50703a0482151441c003604c066004605000f400100030700b44ac0516022500440607441c1c5406252011400400b0790540c0 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 183072419 1250 183071169 183071173
    0xd03050c01021201140405090c270412090f03080703050c030d06082503020609120f0613021e030a080f07050123071b0609030c080c0a0308010603092102 67
    0x18508903100744060400030008041012840d41842e60325103228200035a254032850402d03081003000c52004c1005c8042a00940d03040d40080c00b4107283e0001520f1007401000c61040f44404c20040c410010031a410442e034580b5840306981d2144040303014041d03503020203004c40d001009a540024826401008112002d03c01c0d41d051541e400e4507207042d1501944030001030740c8070050b545420a920744000d95601c40200750500c3d00d500e90ba010414501403495058030032410082080d522078428000b980c130824506007070740c0051611200b020511049c1071810b81c090b00e801b003007080c0c01c1c0d01100030107480c0c1c4000071300401188110742e0323440600d548143d0007006072001c10b2003610f00080007405800000010020031500101c10422144d031000d400511040030020007440c00f482d8005002032000e41d4a0708a0808101459503080a642c3d400745880014200d140009115215803c04102402c070a80301e5030319900a642d942d4402c03420b54601d8880517181021401ea004040344881c0d0035100c104e032003401 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 183073669 1250 183072419 183072427
    0x62c0105151b15010609260f070f080d0305070c0624090603060c0804020d0b0c090d060203060a06080601170414014b0b01140301060906170906060d0305 67
    0xb00b02c101030360701ca00d0300700c0d40d5402403040c1a80803203400c808034050882450b020661600d40864510f0710b00300c54015007800e0341c040490004401c01800080d078204100421178030307000c0e03944500c100c82314514442c210250051400304d0780b560780b280c001e25016085c3d590747c4d010410b1b1240c94040c0103080c3c005001c60421040100f0010740712000d00d1040081102d0340001520390700d1810300d038080d11300384144402003284c02010400142d40d504e4048d01c0850708900e0800c800d544240c82e1080c03d2080f00c080781e50011070100b041c401c0003400e40003188031340010f8655412090366008241d4400c0800e0315007901080030903100c0101080141e008660041c050020040381a00c0703c4090380c01c4a42c0c0310003003100c40381117051003494468510112100d090341c2c00c07000001c40560ba051110803151840780c80000503144d034640046a8880e640c000d440c200c03d025565541d594410f4041c05100c05445a800414111480f0300c400c80e82c015801807090012902a04055450404008040610080c05c400f03200f8140 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 183074919 1250 183073669 183073687
    0x40b0d0803090717010914010c0906110f061003020f040606050412050c06030c0403020a080304030308070815031204080c090f06040908070c0905040308131502030622062c010515 78
    0x31545404c0007400800011b41c00c400d908010008a0140c000508030b030f07040400051ba4a9031101040048030614500000c4442151092505002d9110b9400d00c00f440b4941c1403080202c140c0340034004503842111034500c0600341c40306020503221703180724035004070ba018881005100350715010520034500c140b00303850594812000042c81c40e0001d844184100743c0208060086051900d40303100501071441c015030030549583e43c01030a9400041008040095034004152104800300280400c0c0c00d00809a420959460384401010740103480b41445610542006091302d00305640e11300d020b43d440d54288007041c1e80d140706001c0a0010031804513019102004150302091240d00400d002e04040340d0301203102c0c140390400918094003c0c1050f040a081e0700c8840000407480e12618408011020780582c8075900d910000304031142c0d54118682d600d000c00740b2100c03020050741c003c03800c1e10401982d040c031112403401c0040e5004696919801d0b45609280140060703e0001c6240c49a502c411150924248880d = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 183076169 1250 183074919 183074939
    0x110c1302040f03080c010605010908060a020a0e0612040303060b0f090d0503040b12011d0708070e190806091905060f1b1207020c2d040207060e0307050705040b0d08030907 75
    0x83c0e0720a4072084004226140303444005c0c080d030001401c00b441c01c400c40310b007420303412505c4000142001c000742d940007401c081d005004180503290706d58010030950310b03025081d250980c0b6480894045002074648200841c00038190410350f640c084a8250f5503080c040c03401d09101c00c440c1403080030390b1203100a100000d09150030030010a0b4400070483d11004651610000312041016041071501d00f80c0030b901000300d00e0703034000f8403a40e0007025403400003148101040880e908440c80c48106460302e40414011600071000981c190140c1c0c2200c048410320340c203600e020341c1c400001c00b8004025801840c081055000603a080580080c0c1c0e0b41130030300b02000300855001d5607a01010580761404c0c41c2c0381c100448a81c06229112700c1003c140c0e2240800501290402d100ca2800c01522014000d040c00a103034a407140d1303040d240b096034001410451000c08440d010b607a5001104210344030304c40e02601080070704050080d00a56071001d081c01e03071041c19580c0d030020315400003007110100703210f48480011038902d2 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 183077419 1250 183076169 183076199
    0x60603010e0a06020c070e130308330a1a1201050607023106060305040201020c01210f0b04050a050105031606120e15040804050a08010504110f0a0320040c110c130204 73
    0x40d0100d494101510306d006041201c0040144808886181e200900f072a2152f800e003001c0c0c0441172200380c61640380790008900911503008180c0107507000501d060f00000c0c030b1004165a90241d07a2051041ea0381c3d40411071144101305000b07400c074425185152854844401745100494103000340e02c2000074204044040795459440400040d0319071041c8415560140b148044400d0300b840c007001d010f407501400030b42c243c00081648600b01d60301d40e0414000c91150b803000c072260400410610090410700d22a1024001c02c1c06850f200c0d0240030301e41d0030304802c903548000803160907441d00c01d41214080c1d0100000d200a0000c2c0030203003d40342c84585014103070305005100c2e5100e030400e40d860303038100400c1c072080e041d007608525442c1c1c1c9131000b8000481c4408002460503581241c0710042100d00c3c20106120101c04e0384010300002100351041c200c0c1095800440c1000c07420f80741081840310032082100c051002c14079299864121540c05500c509002c000c000d46000e480b0030151901c2e40c0c0390241e0f802106 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 183078669 1250 183077419 183077431
    0xd0503030c0d050603011b110309060304110f1206010603090c2402060703090c0b0a030204180207060b1e01080a1517010b03010c14070f080703020f060603010e0a06020c070e 76
    0x300140d01001d040d2288962074100d1030a60003004084047c8140044088400071443d052080d1700c41c8560107042d0030012600d0803c00a0641034582c00c1a20b041060310320910499071281c400c00d2400d07940e82c204081a0030000e0b44000007001281d1800700c06a00a0078894001d5840824081c00810424021601008902d69204110072001031140e002420188054400c00815040ca11a000403031706140d5900d040d40c58a10056580320144081a0001d01c1a0f50090341240e802c842c074404810420307406820003034003030881413040030908005c21a5400400b0303001001d0004104549215520844107071354042034114001545000b81d20076500320924039841b0200c00d5a100140c0d0310380450a00900d122544194000d00c03200c82030b500c018108020b1030302245c9071510080340c1c102c14802101071211160f034010300c540d942ca00c483c0c14000d450758a0148010000d100324800b1821600741403280d241c0400e05c1c2d1000e002c40800c0b5548985c01b9610401c518050340c450b40d000418a40061501c80d4010702c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 183079919 1250 183078669 183078691
    0x2d060304050c01030b03032704020c0f03040306230f0a09200112020403170309190c091805030307050a03060302030609060709090213060c0204020c100204081501081207020d050303 79
    0x11642c001015102d28080013800780d0824062440b10707010440380d1902c1c0410a8402c840c1c00708006012034000d0181c90f0030880c851091541c0001c4030000070000300103030390298005000300c20700703079444021203048210144111100000040c0600000c06005504504262008580907180380c49002c088100c41d00c1d41d901104c0390417999400e40d0707086500540501261282942094070b592501500703d01c03011342e0b9043c5908000006074207110207014249080c1d18200c0c114040c0210790824584200440c000c80003c2032600d03044444580310348526041c0c10750311000841c51039844040803074048d042482e04106042e1107a01c080016501800000d100c1d5404a00a020a2070b02c04002041000558004980144100082c621100309824500151015810854007200b21403010400034820f001401d102401044d40d921280c8040f50010700c1155842c904070740920440340c204c14000c1600f840384424aa01c21055a50580c12a03000b03024640d000411002844025407600e6055078422a9961800 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 183081169 1250 183079919 183079933
    0x19090b01080c18040b0402030304031205041418010320130212060d030e060f04090e07150306050303030a0f06080d05120106031b030504060e032208010504022d06030405 74
    0x307100c0410101000c403008850b0002c41215072440042004009400907001d40d102d5000981036407010003c07640110b0f03000a82500341c22904038010095003103030141d100c1440c1440c1ca1b6148510b80107000403400c40b5500303004001079280d80c0d1030001690020243c030682e075000b04003c036900e55425100c80c02c001c2102c9405680c402c03081052494000004001074070441c0512011404a03500c8806c9603201c0c1d100341e60580d41c40b91a07441d201014001c80d4002d0301c40b903041001c04d41d12400f000c5800000c44116614a039080101e0079415016584607025950b0541c0c010300c001011014a03400902c0d5020641c000011a903441d00011070400e51300c901840c1c0414030004000782004a0075503158014665413500304442c05a500000e880e200c0340e22104010140c0342d00c003040610025a104101024603102102d80c0c5110107003402600c890f225606084e034072035460303002600c244180074480c42154001c1a040000654840203501080341e02116062405a0034001c10142c641000a5000d40e006030010200 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 183082419 1250 183081169 183081179
    0x6051206071d030a08032a030117010207150b01090807080d05090a03021801030b0609040809040207020f0915090a062601020f07150515010e120111040e0405060a0204030f02010819090b01 82
    0x2441d102e0b4140c0c04000007075020261f1000c03c0300401d0341e06403030b17049002104175001d00d8403040c0a801841b0020b4152410803000c0180702c0c29560017614400c5081e00c0e0540707640d958103031040e00c4000c9403140741d81541004d9a9022038a200e40001e01d0f044e10010990004991640c010410104800821916404041d0010720a004000320301c1070b80685c0850740d410080c6042e40c5c800c4164003c80d500340c0d01680c1c02156240c21907490001040410001420284181c60100c1c0e07c100c043c045020010700504204000c1505200075000c0c00017239805000c052204540d180b0100508440391020038182554240721680c40420300000510300280030341080a030001d00c0350f105000315040906002d4408464850b40a020303604003800140361401102c0d41d60003029600c00c00d81c0980340700e00c80c09401d00300c00540460224011780c1c03200d02640c0503008650765599800a060101e1065000282c0201ca0100100d00150b02c23034014164015a40725118484004403521041900c8a500381203c8000e43c4c2401804 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 183083669 1250 183082419 183082441
    0x30304080729091f03090f050309010f020c09010e07050c03030c0d0606020c03060c030c0c0a050a0c080d05090915030303161805010c11060405090a06080106051206071d030a0803 78
    0x464078400d402051500d050400020124141c2400d032000035000c1c01305503c1c040d4041c1e071000910350742084151154203014503160392203511503481c0c51301144c0c0390007080900c0d600c0020300081a141c0504101c03003907401d04103c00d0003a48010080e00070480b041007e481501001d20295000b4269448143c1d20fa0305081550002d681d041d4000f04115400251150303000c0d50001250f0b600f10000c80c00056494607002c4141c1100d200daa090700700d80e4803c2484410406c0380014a00307406501403d8040c000c5502c0e0300c00a85c403590548080c1e40001d5091000303050518200e2005500300144d4900d1103d0080500c0c0800e05640084800e042142e1108003044d4206400083d8140790b82004947c9e0540c040c1000000b070700c0c0b50340c0caa8001d01001c560359041c40058440e101245e0150030010300c1e0f203115190509001000d40014050701d1455401c0c0100015203007001007000d01c0c00091f010140143d99115841103d00d035929040d280300207100003130780d5a41c0341ca00380f00b003c0390030f4040da0748540e480c03030900b840380c0e = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 183084919 1250 183083669 183083729
    0x40c0b0f180109050d050309130c0c060c020a0f0b0601120606020a060207020303040b28030605100503060301090803010902071e020d08070305040f0b0d140c0d0b0303040807 76
    0x1a014081000032038840c10304048802140d42215101100e40040004039110021508215041014205500f040c88000009003601d8030701180c0052169a1042c25282a02d000c107810b1004511001d503d400014036680001000490a00c12104c1595182d11200308030034031040e0598407115940280a0345581c0110780d40e00001071038005011071031900000a68078180700030041c09059001c12914210365051003180c004001210465842e00507920300d800c08017002007090316070080d641041c1c80c10a070082c0140f000f01c82004220482c0d800e030a403c2a54141e0008044550556a582a02c800035808801560180500326070058030f4000d0b42c0b03400400342500026a05d140618462940016600c0c0f40d5074403003040e440700c480ea40361007040c80d054809000d00d800c8944e424a002c00c02240b080e007800c01405100b18001018880d41d42d000480340c3d220b840c1a01d01203071101c030400c140040f40220b6042000c55100184c01c40385044c0d07640c0109410040b017900540000015040031a5480000b09069 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 183086169 1250 183084919 183084929
    0x804030816080a0906030b0405042a0305030f090a06111f1509020d06050102010e072c0108010b0405011202010c060203070e04020d0b01020d080c0a0e010e1206070206070c05060c0708090303040e040c 87
    0xc01ca1420f02d0f41b61031103070306402002143c038001078280c68032540204580bc41c2c01141e02c4404c0ba074484c588103155022980028000a0050040c42c80015840e40726454001c0d00340548005420001c10b8101070354007180000e440003403020745540003005013003031504a16000300300110740161500b0104c0d00d4181070f141c032079020b00d0441e810000003240c8884042500d10846007050045a0841d0002c402800c0220a440e404050021124000078464406400c11200c504045408021684c0c81700480e03040880310b081c0c003034000784124402c080001d501d5802103030010b0041c05c000c150000e400c2c1c001402c0c2d91281c218040d035142c58158111555804000c1c82c5040660f9045c00355591405e01610f007031501504100004000760900340401c16405000000a8840040d200c0d200346c6020444c0c907a0ba6510641d10140144078040008489a22904588225a501802600c080d48400135059015086800180e1700b00c00d041200e428182d80406c028802040c85241d060300600d0581480011010766a005c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 183087419 1250 183086169 183086171
    0x2a0204060e0f0a051609090e0a0506090c0102060106110d0c0606050d06140603010501210303090b07020105090d0302040f06122d0c030221090f06010f0f080304030804030816080a0906030b04 83
    0x8648990010200001d0b20840d84001524540e0000c40f5807a110b4500c0f002b41c038a00800003442091080400c02c0b070244403081c1c00b1207190340d80c1c58908a440440f20190761020360814030303820000900c034828441c80c80340100390100704c0648030300005040c0aa41242102c400d6a2140e5031070144440818482d40f00360210001c12040d032404040050403442c050b0030044000811242000b014065880005000d42046102c21240f600d0040640200401d030386803121032046072808041280700303008440a0300d80311035118480e14549541582c16003895042c40041039140c032800c11080e00001035144c01215200180c0c050721541203480011900010b072140101801080030342442d40340d82c55915011080b461031031080342d035041a1513003804010300303d280860140d000000340e0307174000e448003c05443c110524202582d82e40c0410319070b24421488014a012002c1c402080491005006031900510000300c640c2d04c0c075035503a11000660300c80322121012602d98042400031a80c10710401c403941500780c4d0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 183088669 1250 183087419 183087451
    0x103020d080c03120f04020f030c28090207030203040518040b16021903030507030b010c0f0809030313030f171e0903030c0303100e072a0204060e0f0a05 67
    0x81000c04110344400350a21000182c0c00e00400010004c403142e842041100201d1414603200b041012202a1010b82c4590454811000030385008038a22582c0f45d0014031030b404001d1500d9071108088031100c0d03001040901c0e42070000702c25050b800102031980c4660f01455a983c208000c00003110040a60005201507030010040003030240398145400510880c3e58170942051010100d1038913220001100b00380e03090307107012000c0641503005507014019075201403050003810001100c04d01160400030b040400e103130300d00d00c0105800c1d200a0440c0d074005410f40f80b411038081e134460468110780d84200d819140160009080c00103c0c80ca003a005044180058907208444110280c004031900507440084000660140f1a50301001151040161801900c0d00c07031402c00c403110054440c500c40c8480001d1548000740100348521100c41c2241405404000c0c01c549800c4103c0c040703202c00000326040b90b510b034030200d8504507a00300c07144640e0749070060184c40d14000750320006445000e4070b03001c40c0b40f4640b8 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 183089919 1250 183088669 183088673
    0x20103140115140702180901110c0303150f09090f0c0607020f10020c041e0f0c021c0924020d0e06090402090d0c030f050c0a12020f030127020103140103 67
    0x2002c03095010600d40014914190220b04920788507400001b54007100d26084c02a56500700030100d441040080c00030060000e03807103a12941845900b2200001d60410000200d04031460240241d01d01c20190150080400a1020803111042545c0c10030341030f440409440f5203031b0020000d2a0754400150ba010703061a8075980455001d884005440c1d100b144042415010240b00300100180c13803070018020302040c0001d80d4030640103440400e484551508240441d169017200307004203010319460f54020000a0002440d0707520358031091090b48100301d8400800103030201001142081556592400c2c0500002c82c1070183c41d2140071903143c014009076482201c901ea44000c203a900e49441640e015949540c2c50000420100c09040c0c002e110003881000401807041c4101451402c5100784100d0b48440e071301d102042440181c500c00c110300024440e000c00010b040180b080c40d040704001d4004958404014020218070b610301c4400c8460480c4078500b0815581c2c10b00503040081c04a9890314541d504607 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 183091169 1250 183089919 183089939
    0xf0e04151e020d0b0a090902090a0204050108010b1303080d02040608070206060a170a080a18060903020321070b012405071205071e0b01060305010522051509130201031401 75
    0x10075201180560203d1280982078090700816900140200181d00c09038031041890000d000c448000d13401240d000d0005901c50403688200c1d002d80e00140c55548540c0e10740802d030000b036885809500078805d80590300100140c0399a001d0035100c180a140545c6413030070310300010000800285224215480001030201ca0346038440084103454050918041030742006204da49019619000181804000207680c0310440d4000d642c080510084030b01075910a0343c400c0e00325031005080c00040d40c950405894009503080080c007646c903aa144ca8042810b0040c03a407030342960f40750240d0004000c0d01014010640078a50035140c80c501c980309042860400259481d14108000c2d10030b104000d0080c0020310070107200700d01000d40c04c1050a0080c03082c044e07510b13142c4500c05d143d01788603c0c0040303070034a00046480e10305136149020018281c00010700c0704c0720100580000d0080030300550904002c9012507a416203540c801288628480c51000b1580102071000604582007a10751001100d0303d00018840307480b00c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 183092419 1250 183091169 183091211
    0x5040e03030613020903010b0307030b01060e01050c070509070e0d11030708031606050402010e0a1d0a0603050606040b12150118051027050a0b1306050102070e100f0e0415 75
    0x100d010058445c0d00c043e000c21300400ca400030342d0780d045c03040322030000801c030b10040f009060ba580c03030b590590301c0d08444005460301e025250507541c81e0780000c0d800740320303d04000d201030340d01020501d07040e40051150f07c007064a11803040350580c0d1415008040e8107042c103040000d9002003c14000541c540701000980b4651400c0b1128014031040d107410104017035a104425032044001d000b0000c6485943e1510040e5190500d69130302c1280070000c40020741c09000622401e0200c07178201020700400d68910003040024000c060415500888018246403403030030802503590700000302560038005504080f14400040401030900350b40303a060000f00310082440720100c1f0111251010742e4030307540c010115100484036615261f52502840c0c941000328843c6103401c40b1710510029503100c9404400701d841e8500343c07186030154034050303800200e08002110321042a254400c0503200883c14050311400c0c1c5041000c010b40c44481214941d00c240010b0000b45000111302520410040000c021040a05400f080c0 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 183093525 1106 183092419 183092449
    0x1814130803103b100312142d0301080307030807030b04050f01032306150102070e0103030201020403031101061503050603010b031c02120309070302060f040803040b0405040e030306 79
    0x50183d5006002d0789803c08144601403d64079121a4282d0000703115080040d0240c03803a1120300020003074244182402100d191a4440801c01ba250008400c02c0014a103420401000b00e44000811101c0c1d843e4103042c42a119950340c0c40a60090016000d1260400d081504000c8200c0d48416558160b80c4540104a020301c4086c8504405110b440100c094640c07200d40426440180c40c8600042c00d101403044802d440d8588155000e800d2080e071003240941e4000c2001d00c00c05410210722030b400c1c40000020043d1503d0071600540e840440c01c052000d0698500101310941c4080d000401d02d5500a000c07603250f0088101a200000c00300801e000060160208071422498030004580c001c0074a40000d1012608640030040ca50b0b1207881104c4080900304400a400f15091010b031005041c001181611141b0f1b0000b03000a45034858040b880607002003041201d6580c0f07400c2d103545100 = true := by decide +kernel

theorem cover : BRFrame.Cov 182913669 183093525 := by
  have h0 := BRFrame.cov_init 182913669
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182913669 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182913669 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182913669 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182913669 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182913669 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182913669 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182913669 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182913669 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182913669 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182913669 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182913669 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182913669 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182913669 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182913669 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182913669 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182913669 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182913669 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182913669 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182913669 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182913669 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182913669 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182913669 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182913669 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182913669 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182913669 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182913669 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182913669 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182913669 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182913669 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182913669 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182913669 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182913669 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182913669 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182913669 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182913669 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182913669 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182913669 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182913669 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182913669 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182913669 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182913669 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182913669 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182913669 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182913669 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182913669 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182913669 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182913669 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182913669 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182913669 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182913669 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182913669 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182913669 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182913669 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182913669 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182913669 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182913669 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182913669 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182913669 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182913669 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182913669 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182913669 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182913669 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182913669 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182913669 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182913669 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182913669 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182913669 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182913669 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182913669 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182913669 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182913669 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182913669 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182913669 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182913669 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182913669 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182913669 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182913669 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182913669 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182913669 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182913669 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182913669 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182913669 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182913669 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182913669 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182913669 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182913669 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182913669 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182913669 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182913669 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182913669 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182913669 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182913669 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182913669 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182913669 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182913669 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182913669 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182913669 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182913669 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182913669 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182913669 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182913669 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182913669 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182913669 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182913669 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182913669 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182913669 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182913669 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182913669 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182913669 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182913669 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182913669 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182913669 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182913669 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182913669 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182913669 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182913669 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182913669 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182913669 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182913669 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182913669 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182913669 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182913669 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182913669 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182913669 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182913669 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182913669 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182913669 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182913669 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182913669 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182913669 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182913669 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182913669 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182913669 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182913669 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182913669 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182913669 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182913669 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182913669 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182913669 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182913669 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182913669 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182913669 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182913669 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182913669 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 182913669 ≤ n) (h2 : n < 183093525) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
