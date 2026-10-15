-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5201
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:04:40.936235+00:00
-- url     : https://prove2.me/submissions/69a2d6ec-bdec-41c8-a4ad-866a27a6e34d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 935251798 ≤ n < 935431654 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 935253048 1250 935251798 935251843
    0x70902180414040f080d020a0c020307170c0418170d0b2b1103030d09050708060c0f03070311070b010509060f100509041506020304032307090c02010207050d02 70
    0x91405015020882c00001c01c80c1031a42c6543d9501c01c110020188129210f040611018400f486103201400380048141d6481c1480f41c01401414108903150b000360901d070550002c111426000010540c1c10180305440018100c5690000343c03208200d80c0e0340040c0f00c11b1500c802c0c5c0d1003214008010381200d49141034204a090200d8041001880120b41c51095154000401c803039031100c4144186060f9020308480c42804a5403c0085c0c01d40e40401c107000e841c90703a03d58114050000800085010704800c1c4014442400d24500114960051408560f05280c00100140329544030340c000c02240150110005d032144da275490803034240300c42401060301842030700c0e0028030213107080740c0040908007000d445412420a2040d040302c640d4000c28045800989981c0229030003a8a51400402418142e02440d01c0302c0c21840c0240c0300958041c0c44031031113150201c42c10000d000100d5020304848841c00006014240840261701a000d103c00c01f401a0058242079003107960040744082000d000884141a107 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 935254298 1250 935253048 935253097
    0x905030d08061e010906050f070f0b18030c071401021006120b060d0b0a051e0a050106090503160501121415010f0f021005181213060f0203071b08070902 67
    0xf80c40c80c5208190015240310130410003140a580180407000400010b989800103a85a00301d80c420700c0c4004881c1d16800504000994440b11509024050391601075844d110b5001090341d40e91303405000b02c0607400720a003800015603000300f156040c9045480414415150390f91001000103401000030b54104006600041c124584141c40380382041d4001118151a00c0c4d00d08281c005003401090102806075080c1c1c0000c92000c0d80410394410b5a400c44007107415030502d44010031848052340b102d402507103e0b2446414000604519900751102131904405062400b01010090591b08d030b242140d1204500c240301c00701400d4030a003a480c080c02e80f248655408130310001c480b0050020502c8005802010500f0110700e5503410040d0081c2c0601a01c40829941c00003460a200c4c000c1c0090f030040c0b90004585000d00300781c2038450b0081442d03040c542c1c2e8030002d0180c0a51071348034062000b081ca031195402c1c0f809611403412030f18060010b10b001c440d16142c031420382200035402030038003d0341000020b580340032 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 935255548 1250 935254298 935254339
    0x20705010605310e010e0a02030c180115051c0c02070506041d0c2203051501053706090302091005210f03030a0c0e04090803060d030905030d0806 64
    0x4a4060031109041d5084040a84210b0f603034a10f0582d01a80d03c500e22030719610001d01900a411800f4000346c407855070b50b03204144c64901490305013405400d140904900d000700c40604036045602d04141d0900074156145e0444481c07003603041d070314600d640c49113251101c0d200f00ea012224074072064088403112900c440c02c00c4650b002c0c5115010b402170350001d20f403050b6100008610340001d51112040d04199103c2408644001c1c122102c1e12001000c400c10014041c040000300c8201c000d024011140d54148408607010796540c40c1400c40c40505064407450b444048215410302d2090070004190403621410001c18140140c40300b43d1103440d0f1072001c56901c02c841d424030760841d203008001d44020720854124861101c0c4031200c201031405441d201418150003030000310310600741103d00041c00c0700b95940241101002e402c0700d40c0520b18003a2850001942141203d401030001c60f2a02d021614518085590980903040f0301d4050141e5003407000c15076007140420b401a08101d80c50400c2403600c081201 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 935256798 1250 935255548 935255569
    0x910030608100902180106080906010f0311010e0f090907081e07051203040f090c030c05090915030a0f060c02060106020a0b0a020901140307080603250e1810020705010605 75
    0x4429044038034103020502d0070b603001101040c8040c3c0305803910130f003080c1c0100d0410310992046021902507410808888030600c805405007582c01a000c145c1da045489110004000703116581c10310980c2c540c4441241d482454810388860700501140d482d10300201c1454035080701c0d12070301d4061b10852218141c0021050840c03100070000800030051689800c0c208001c2122000203226980010400802c0c51003242503808003601d240140410b0340200d10380010220391419480c40d04220045c440e00c859035607907004072600000705605000510101c14002420294076003001404c03100c031103078003500304107903500102000d10300f980a448003a030b80d803607040e078039285a6900200142c2c49080014901c0103a41e000d040c8188061626220880e041056186a5401070b10100003042c00c4604000c050300d010880e80e40c80c5401c44001180c401280c00441080300c0307090050303a0301000c2c1c0c0000519240f181000c1c000c1509203600880300c00f15140802e0400941c04900195201d50900034046060b09012803540c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 935258048 1250 935256798 935256809
    0x2318030c030718020f1c0b0a090209090a0c05090301091109011205070b16060c110d050f0403060908070503070f110307060e0112060b1306030605030601030b0f0c04050a0b09100306 79
    0x408150480e02c9440c0300035171003e40c1c0428a060140010898407080c1002c60308000400000052040340990800480b062180d21149034180104403c42030f5841e688a9150804400540828203088851050340c090280e501e034240c166203000449030911045408240d0030840594444034a66200c140140c6600e403145d80280c41544045402c1106011240080a81030305a1441c941c0080e102d035906000e80b101c00700400005642e881030501c11010900400d004038025040461600b41c1b60b1064041900403480040c1803c0e41e01c9446c0780602407031404546109910006495480100f4903160b480401c40d050241e804402c6845940850b00f4000b80820a0341c1c07158680010546a24004581c8102a01359011569460340000140b081c1e0110181c80c08920406002c6081400c181000b4100d407025407085110303500c90801040801c000611054116030039074412003040d80d4810152480b407240b03600103500403c404c0d50028142440034081d1903180c1d0100c0c1c0ca02901001c0b13000c100d0943d030b038a000f00c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 935259298 1250 935258048 935258069
    0x1205010f23100503030f03101505040603050f1504020702011404090c090b0f070f080c0d09090e120d0c1806020601051804050714220203060a0f060f2318030c0307 71
    0x2003036a00d84100d8060342c2d103d088c0104244007140c40704540341c4001e404a000c0d00c04604082814032100e07801d405160340c0110442e42160031450441ca105c40b04248152189006035800240748003564450034040e4001c1e40c480c2c51041c0c1c0c4554075034840004001001d0203500041c0d034a28003150100d000700482d503540b010980d01c00d0a141c91512031410a01100030104c6c0c046504000d15901c40f034081c0304c45801010143c41d00c41ca5146024107030b0069032040030f0358070b8013600030101e1001c50240c440251503440211000015901829510903101004d0b1049014200c540d60b48002410660009116040e607030140e6540740c10b800e41c1e0080c0a02d130242628010034a400080b818000110309500d5020310003001495214030034900f0451058080650b030042201e95000420404c0310700f00b0541520040807140442c00c078140c40d02000034003210300c280610040184004c00c80c00182110003050340e14404040002c7e546001d2103c2c41480d082050247c0d90090060045500e100d1502007603010450707030503424 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 935260548 1250 935259298 935259307
    0x3010f061b0b15040b040e06060a080a03120f09020627180711010b060705061b0f030a0e0115120c05100507030806040e06090604061b091205010f2310050303 69
    0x2d56144401e0940f5035a001642c0e40750b5103001d5500d6004059501107076801902032801c01030140414079142c1c0e004070311640c1c0301e42018070020394000c41401c00c202c4c1b2450000390805001190708007070b01c40304901a500c04000303d403042c2d0020401540c801405203210b403056a80e000748090100c0035001c00b400302c540065860015013041c1c0540d04800e02026840c1c000030301410030800003217640c0c020381401d8034164003880c1000302d0f01814201c1c000f13401c403141c11b6031414036060301c54190a92000405c0600e4040d00c581c0d84107400c086c25080030712a00c01040c0040c4891341c0700d54403404402e06090080c0c0703031100500000100d40c106820110f14200941d65014500b502503101a130742c1003005025a6041661a030b49284a400244503160060010305c002e070145040070708145054604101c040d114960801002400594201a4103000c4030102d0841003400003060801e540100908400c0c0c03104541000000722030280280f80d01541c114107400048801e440b01a100e440d48040f43c00b41c260554000c02 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 935261798 1250 935260548 935260561
    0x21816091e0905060a0f080a020307051f2010020d050703090804120201110a0804180507080105010c050129010f020a050c0609060c03160c051f05031b03010f061b0b 72
    0x1c0001354003a4024080b000c501e030781c1e5500c6d421612025408401d064003c480440210f10341884500e0050204407840b0268805540403526104c601c01414070a011021130b04074441c290302c81200041c03d104400f9a424010b202000f030020f07510551401d1410b42c504000100a58003a2003180c0045030040c129a0520f814502203200e52850030b5400c2e810701c0300e024120490707450308014840e8240e2040070556100d616010548070f04001e030900c11101242044c0400c8042ea50040180f411100b003480d01e07078800440303130070542d005240c44880790454031003910700105864408110641a064284c0c0d03800b88109104e0412610f41c0d034031501c0144903401c09040000145071000c041c15450000910003480d040c0303800c016500c2d50740f1002c016125460208091300620a44502c40401440103079041950b1460040b11303075030844a160f141b5001c4c40004408508410f20000107481d280505407540c03a0703031303584035250006400b043d03204d03250001e00718048030a0005485900d150308294403080954160311040d = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 935263048 1250 935261798 935261801
    0xd0c030506090f04150b03010618150308190516060e0c030a0b16030b030307060c080a0212160509030d05030a0c0f02070b090d0c09020705060702120f0304021816091e09 74
    0x2d4601075000c86e11044110302582d03080c0729030b50040c0410001c04100c0200030340260151034041c0c051060030344032083c00b040850340900454001851041c4d40c601020b100500c15207142c0681e0200c10303c1010348980c0340e4100085e03540203240680080c011078440300c1c070100c00c169407040031b990001c11034240400464020b031400002c0850000c128240842e80c0c074118004031b4a5500729401c1079440d0768852594142d10307900420401d0b000a6006010340ca0894180d2410f00c9007035015003110340301140c0e079020b03c6c0d01c503120f072055405180c40101990049a031140004185070030030307070700c40700c8aa06d402c011614031030190030510300030320803034015200c042c0c0742802264054002c54156070b00b04040401d8140020f401080c28806440903220050315041641405460440c0c000c0c41141907500c03050250341034034600000d8856086420010595980e22440440d0400703041c0d00003551450600c0b0140130b0038115070300c401c4031010300e65559468400c0e560310342d00020300066081c013103640e00e04d600217006c120006d = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 935264298 1250 935263048 935263073
    0x9150e191505030303070801090b0f06030c0a090305010626030a020a02010f0302190915080609190e0f0609191707050312010f060311030606030c0307140d0c030506090f04 75
    0x1001c080c860302903034900c0440d040d0350040310700400081d0316000600c0810810300c00d80b0140350b410f50b49480380c410b41301c1c0441c0ca540300103007542d24250008a21a090300b072148001001541d4800300038448580d40307001989040d1000040c61002c0a5401c115038900d88000054a0340b14400d54014180c1e0540d540056915030b0401c0c807058201070302000880100c1c101c030a104400ba00f925510500d2542c50560000105501c4914280400200c08280302c2070b41d8417901000c1d0095002110b400002d500f115100004241d0124102a0390180d042d0011140304007007103952281101a00391585281c03003000003001d04182e030000504003100c021031200080c078500007401d00c95110f10304583c50115215902d41c001c0300240d200c02d0200303501d003105100c2181e00d8041c581e0300c5105524090f065080000001e181400014440c400b00e00c0c006c40000c0d030007071150940aa000103581c80b210764401d00c0da801440034148246035840400d0404010400c0b600305111500c1c480d03400c0d0340034014140ca131070f51802c0b03c4409 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 935265548 1250 935264298 935264321
    0x30b04020612040c050901050303130501030e030715090b01050a0305030f07030306031a0103061d070504180c1d0f0405031b010b0604060804050115032d0c09150e19 72
    0xc24442c2c5101d4200b0030b1240780c011130054080b1054545440100000d101d0b05800c081e0007604180b2058510075123a813201820f40710f003401c0118000d451915101e1075402070b0740000d440b003952406403035034641036079100400c0e2300e0040c11040000c1c0e88030307011f00482003c50b110040082c1e0040244108a003841c4010740303080c900c0b80c40c000c0344443d41c1c0d0b10f801200400307003880b903110107682000401c1046158414412000d00c01e0180340141c0b070501c25000c3d2240014451540560b898003001402981d00440f0641c40359413200070b80c8000b5440f03001c00d20906066807108603260021078046442d108543c00d006100c0c650000040d403404011405000c2c650401c840103507065902c4401c0c0501540d0b60388058400340030140d032400c02c1868a03042c42c0d0301303649500260000340302c40c02009101180045120280128000c504082121000c0400030002e0505001c003030032a03c0b00c070b0004030700d600e82e5411540001020a202c00d1402d600e03800b035401003107030986000b0484801e00280401100b11508590600e08 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 935266798 1250 935265548 935265559
    0x606020d08061908010f050906090d05090a0911040f08120d02070213021605150906071d060f04181a15160803041b060c240e030901121401030b0402 65
    0x10701880901c03400300f095000110565107030b00e9820301c54003442c8038242d4408514001000182040840a61540030010114040200009422600781c0360440203000130015030320100b12002512080c502c0c0c0d90841d024220960406107000250180000b5141211540304541d9601d010040000c1200951001e00102d8000e000c082c0b41210f0a0342c2c51001e0421502a05c0c801d901618462501505000341c4844040702e96a0310403d011280b1000035106034080058100601036403192641103d090b41001e4140d6403000002500e803041d03030b52440250040750811a503076094007858a0862081d910100c0e20344215060b490a021039510303207225440040558443c00703514010260341030707900e112007042007503401c50f00010500c020017070003121210303564104203071300b5100038107000740100b000c00300c00340180181011340084407401c201d940c014a1591900c01042110030300c000000398072074101d02401d6002c1050f038002e000800d041d9005d01c1481265100c1c820303a0750ba0071650b503442081000340059820a = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 935268048 1250 935266798 935266819
    0x30f06180406020315030325030203070f0c03021002010c0c02100e0415030c0f0303020a0221060916060302090310050a0b0d142806050601210b030f010606020d0806 72
    0x20444000c90074000d50107060056902c0c500740203610054000d22030071500990040103c020440d9204000d81850b841a000c8140d070341000e424228514024550003801c05003041c42ca02c01000360040501c1c1c02c60b0720a495400790761130307801020390803070b524400004003140d2040103000041ca0840502c241c480079074101b40104a21040210742100d410006504a100440c0018000d00c600191800300030440000f0303450f0300350b0940e0380081d101ca6801030b00a018180540e0400340500e81110305003003540318242210a03030b24013580d005940740c20840f062101901174440104041d446402200d40002c80a0020001e468111008138000c16005001888081c2d58900a1065903035404112182e180160844581a003015030f6043c105014081544520410011031005101c2240d5441105c150030090001d036070354032840180d843c9551040da20044544880480c0c0550703403541d10040f00d0038800c0c1c048400384034625400764200c6807c3d01441025074407121141b02c100d4820708a0540c001030140c15080075 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 935269298 1250 935268048 935268079
    0x1020f0106060801050f060304020102031e0f0705100b0f030d140c01180309050f0d02040f060e10031a0c03010e07030615050d050a150b1e0a02061812030f06 69
    0x2101e000d40c10020000350004010444d42c80c3c00c0c1074003c07020074111a85071450074280d0010b50f80e403044080103030108200809240b8220b9a804c255200070b440035001513910f01203450b0154070740b201c0c41c0029110f149010301030216818005c18001c401ca41c090000c1404440342401920101c2c82c0302601404480c040080780c0800400307000b01c1210b14840302c581d000e6a00d00d803030003600481d842d42100f401000c2803810403010340d98807807054201e103030161030000301c009012520301c014002d02d40010039500304040c00e100400004581c1d48044030b01070b14018509442100445100d42c00c1928030700107607101800103020000081c0110b9801100034103000039a66507580519030b0701c0100f40c84400c003003400401d071000301c021030307000d00f41e031200300008100a040040e001614000700d150007582c0c040500824501501a0038043c40c284816106043c1c5403260003d9038000c1da2220219412140c0390108162402d078406c000400c80d4460305202c4149055950b515440c0381f41c5403004051a611002d140d1a0321138 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 935270548 1250 935269298 935269301
    0x60f0603080a0e210a0b0a0506010207060518100e13110307050c0a0c030b0f0105060a0918020d050103110a0b12070318081305402004060f050a0c1101020f01 69
    0x1403c1100203040030105901b400c80344480000c0a0601590500c0704100c3d203a031740400ca4800b6141c2c1410000d840e0f000011281c0744072420461140d0300164000b20171103100d40c100305545002e85003198400000c6601e41000c0e0284c0340f1040320814582018408502d440d03001e14050042408880304846149000e03803038142540c0c0387d0ba441a9224100c002c14440744141c26498540901001c1c0c0d425071402c90002030040424500c1d12880b221b40d14240500c0310381d000305404a034400203070040705208950710303401c0040d18000340c000083d1103000030a0000a5002841c0142c43c2c0c110222142000c0302d44c0c840d0802d5000c1c0c80b029012030540010314032490000744c4034101a006003545040340001441c14002404007080d010005d60462504611328a00545070103542014080300c02c040c1c039151940c00300b0100000e46140030070070111035241e1440d180304035074401c0a001154110b60310210320340700c40c1340d040d1498460014404001590840540c0114100000b00b00c8022410f1044031941d0f0926400e6a0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 935271798 1250 935270548 935270599
    0x703081306091505190b06030a09110d050313060e0a0920071b06080c0706020c010207050a1b060302191d060a0c0b090303010803221a0403060f0603080a0e 68
    0xf0038954034001d0101800c2c03203c0d2002501c52491408000d200103e00c0003885d5800300504c074502d01030320343d004002004501d9580c00440311028180ca40103002c145401510b9800c40c1034200a00c01c10a080010481d100f2000e10b61000d5024040160b00e0b0306240100003d0001034208002100081802c0d4900741c003a84020f1009078018103801c14480001604070055081962004017041010800c1c85504003640b8111090303154424401a43e03040d0600f541030190041c070502070f2403409113120b0407061005850b10421103010300f020704044103031500ac068007240100c6812086101ca80380007089080e0040d000d0400482e843e03188007039000c1200c000031f03805a000146210015107080c0d9107008221100e000285c000c5003e20245003558103110600d80d5902078000310340d0380075922002800c00181181102c0b8098440715508441290b1b50f42041200c551191208450141c0351442c050b080301307030030b11030301041e00e40c86400c1c10f151000d0220121084c10001940b02c4d4000c14100c000d050100d030316801070 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 935273048 1250 935271798 935271833
    0x330703030912030e0f01110d09020a05120d11010903020c01082a30041e05070f05100c0c05060d0b04020c0a0623040210030906020c011d03070308130609 67
    0xf049103c843c503022420204c4801c03017401d480c0c0c1400d05022882c00f486081d1111040030070300000c0c4000c2203000260b61111180c0c0301d40d0700260501100d120303080002c204449500110381741c040c54a01c040d0729003405c9518405014005810031900d0641c0d5621443e6140d8214140301e13004100c00601071400003c030313612111801c007801c0000640c0d8040f40e00f0402ca140702410054190708400d0310130540351084038001800101080320341c3e0000310180c9400320994034070380c0c0c0000c102d910b0b0320f4549051803101170440c024240f0450302c080c10046a0342c800d4040d0158158000e409205482c540010300115420402d5020f403078603122a00d96815440707a101504004010310000e107c0592142020300464030095440004212448400040e042a00055a030040d07416920814000354510741100100144000100150300000d010078a900d015008401b00000007102c1c3c10509220662240d0350707109040300100400c00c400000303005c610500805e040c400b07008030800310f007900055507207404590750407110 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 935274298 1250 935273048 935273051
    0x100c12090b16031b080d0e190c0906151e0207081f060914150f09070c020a0816060c080f040602070311060a0c02090405100c0e33070303091203 63
    0x4002c1070551011090020182c004401c011907040c03900d40321400d01c1203044126102e0307255103001803288003c21650101000041d01210780340000d2406042040d0030744280c0010341d042900104d0150003030b05419444180a8a4415030b0b8407000300d441c104000170f0800602540120341c400114890140945040a20124422100710415a080c8801c44a150b04071080007890721b5818600102e010f5060707138020b076031a080d00e54406695000202c0036811602c3c55038010700040203001c60705401249180e4030a1007103412120486d2100616035645410503060191802d00c8002045042e00600000e07040740e0140c040903262511507100181543c1c0940d0051005a200f03071030070020301c10480ca141c45034400481c7c1d010f00c0d10b048c0080c0200000200740700a8851410040440c040120420480c046540d5540080c001d4010b950005030a145421082d94010b5114900c0307181d1090040900008a481d0125940f410301e42c1c021070000150440c89085090559540d203041c04113400d03840612100409940 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 935275548 1250 935274298 935274337
    0x2070b0d0c02250315061211040b151909080106031b080f0d210920010201020313110105070c14011707020d03020c070e0123100c12090b 60
    0xa009240c1078072150041021810703002c0f800c810303d0a00d5030704022207030401c036000d0b410803072007080c500100f040d50b200c29020074800e5092010840b44140c001c00080d0210350170440d024022060002100c000c3c2455020703030004000d5400704514100c04036102e00828517101d04807503203902d112801c41d0ba194000b62614412041070b1424a582149120090190b07a000761000c058004202944c508114000781d0520004900c107910b05101400100d0202610090030f01207588542002120558a10a1040711072070300030b0b0721790181d4014022a0300412804000000c01d59450725980b40d807201101d501410800200800008a41c80c100042d01409545000214a004160015040d900310fa14010a401c0320710081000c269004980310b03601180e03034207000d40c0c0c4d40c1c007104443c0e0030242c0d0794001c00c01c0798041d48008200000302020504911603800d15082c1c2d142d815600300641c1c0f4084030440d000082e52380f4500b50005031074070001240c803400d90521a04250b16154019015080803400900342601080c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 935276798 1250 935275548 935275571
    0x21b0714030703080315010e0d12030c030212010302150c0a06060510030507050904050c2712010b0a150207090509030c0d210908130b130603020301060e1002070b0d 72
    0x404805603100c0803802052002c0c034550fa4100c0901004191030040404420744c030303074642d0195090101c80413004001c01d944400070315004514200c0381c0b020400081c900b520240c0302a01034070840c0c2c0459001c00b4010030f80c0e8615400c100320b00c4090001b242c9072090030f22042c050240e080000380c0e61540300d00c1011481908010034040315045030f048010416040409102200760000304a41e0030900981d0081141e66030140300d200144101c1000040700e00301c0076000407008842049800400c0c004403007141c0c0354041d0441041c203030740304040200c8d806501c01c030003000110752000104030400300314015503840350341c0c03841c040040f1203045420b50380540000811001c072440c1404440c030010024201036801c00c003001c14a4503c2042c0c2e0900205071607948440f10309001e0640241c0300f42d1015500604141502d500083d18035070003071031000d44440d0106401180c11802030094a043e29030781d55560100303a10031010012000e100c01d9040055004146021940c691001b0081100d8007451901244228045 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 935278048 1250 935276798 935276819
    0x1a070b01120302100207080909090a0b150405150616030c020a030c030506090d02250f090b0307090e030702040f09120e0a0f081203100b1309180f0b0a021b07 69
    0xc00e84208445d01c1000b0351000506d00605071084100103403070b1030069583d013003039040c580342078020040d2801044100300002c0d000c0c0380303410782182c42b410740d41417049440d0032001840c10f440f0251081da10a106003c10802440c1c1150f41400d164001c0c0340c18000300c14103401044040c291a003095810050998042c01802002c000300c64008215000030032030000c40180003500d68103c4c81180700c2d00e40d40ea040d60001800d0f000812006028680c1810726440da48056000091118448041c0a8091040e000440300c4261042c4908103240724061454180345908000081200401052800e40c2d01d1401901180422691003884000c40e25800202c031110780c10001400b04541c0942030803001c458060102980101d01000d1050705021026185c0d11000344160311150300b0381007801103071408203552042c1000c2d0440582290329042c41000060596102c500d0105c2064202600c46008080c0110005000954481c0c1c01240e541005090040101c0f16141355031460840440590100c1d005000c0f51518 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 935279298 1250 935278048 935278063
    0xc0903111e040b190e100b0a02070e060a080d030c08090c031b011e320a0f0201020d02040f0905070206131104060b030901140a0203060a1a070b01120302 67
    0x11203020961202110504011401c40300c0402e00460f241c0395014520348400301e1995800784150081600d40e61200d2420f111048203c40315039042d80301030300010348050076200310740c004082940a41142c1f410004c0e564030604014040603003000300c43d10005040c0320f0034810030b94410007030396000c07079803d4081400070700000e0041c0044510b60040c0340c68a0b00c66a00181140d0503c046d50800c40f15080f00c0300c0161802181c0d03140c840e407460015018941d542d40d2126041080c00d001e00907031541340d642112200408e0750306010040700c1c940d08000114201b405040407031640c0d00d5520000d813074a05513403030326030681e005039205c40c40003010b54109100d62030017800b4550303100303086100401e9107141140c018074010140c2c0c04090680160380d59811010f4a0b035401543c0070346503100740300d079403802e003505024002d0030440304400032000c031840441e5000c0d01e10700071030340152402031603103000c5418401d10b4801541c03410b0f02c04088090030001c000018108660342d034002c010740d106c0124107038210b0901904026a = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 935280548 1250 935279298 935279333
    0x1020d0615021b1302041805090d2f0102041202010e06070302190809211e033703020405240f160b04050c01020d0c020303040303210c0903 61
    0x2004802200c8030740e0003d040880401a0070403610580310344000b2407840300c807401200d08070500000b07000c180929114080c40c2c1c081c80d0040200b01d0b50f5a49003442c0d40701c40d400458800001c0341500721a03580704a50356010041c001b103405115103d61079041c81400c90340700b0f50102c0e08110444500c8070940da0842c0001619550549042e0700e4070245641c02501c03810580191070030000c10030080410b00c80b0f05400d98014440c05851043c103a440041c43d03080d0003a2001a169103845122541c80d502545640f0044d113a0b021000210f050107042c0946481850a1901e441d2014004440c4981104030a0703041c01102241c940300144d03030303d0400040c0006079044800f0a140501c188089540f8020b2050448868a490f4503280f41c85941c0c41e0514031a4160007040504038250400601050000200d09100c803002c0980803900c07002c0d17071b0801c1074440740500600a503140d00244400c0001c42d018034620926442c00380002007030035076608144000c03604000300c15030009a0410302441088014441e5940440b03 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 935281798 1250 935280548 935280569
    0x4020f211f180c020a0b0109022502010905090c091f03110c190201050705010f060905100b030a0f14130b070804080d09171b15040203030d050603030d02040801020d06 73
    0x600b02620715600e0b940259804840c40c1d0749524200c0c2032413092003581c03909944014a1403465a40f03400c500c010750842c1c0501d8280400f9030a045201903c1070740041d05107907042e114005040e251504001d0460401419152505420807014070250b481d04103514a480890a090301c42c407220140003000c4811100074803440440c1082614070a003070024070542134034140241000341045610040b201800388400003400396003820140150000e15421410030740d66042400c000d0307507980c0700c8d21406000c4248640a14607400704041342514041e03420010498542d00c0b00413852540841903041340c0581161840d10600d04094404100180e010150350013030f4440c5002c611a00703154413610f00e217105d0428120f0b40295214926001c224039411865a203c40710866542c44265048103449400c1d4460301c298101d00401080e541021180f50601d4011034000d0000c6042800030f000e040000d14016102039498442840340e14040e00050006001802100002507280c2c10580d4500c4d055450507003040620310f = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 935283048 1250 935281798 935281861
    0x213061508011706070207210b281814070503060106180f060f0513080303070f23030606030403050c0a03050a1d0303030a020d090501020c07030318031104020f21 71
    0x3568005036a0f410f071078140c200b000f2603d16000c3e100702c03141d210b503234003e1058207124100940d524040e01e080013466049180000c0382d11740d0008100032268812000d2501540700c020110110b41010b42142214409204a0711210f8540000924200c0260701c030500180110303000c1c400109040200000a1007002000380d0368608048001d01800281c880c03440030400302042e40402c2400d03480d01c00008004400c1981e6076410103c0000380089507801c4882d0108511500003801d508800c2020007403100f207001e0316401c68442c031040000c1c507880500180c040210a2010300341d08001171142c82c0e0306502c241c40c0c00da51038103064805070800050b41c58444000461240641d13580e10080101c075400304002000503a50300300420014000c201c02280a489580702003500b2820a20020340031054a020740c9a000c03640c88020700d85070b4000c41c1c7d4007005000c651170104000460600d42c025001c0040c0c244109030518103550541c2004a5038285001503c1c01c040307060242227010031011600d0f5502003800511350 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 935284298 1250 935283048 935283061
    0xe090c0304230d0f05090a3c03060e030c030a0305040b01081b06220807140a140103090309050d0b0f180c190f0303121506020a0213061508011706 64
    0xc5035043c0d01c0000c2889000383d24900c500380700b00200d079041a401040384020940381c082040f200c0c0000b10702800c110011185401280d10540b0788440380c1400f1046108489041d60380307040140540b444900c2d0948414015601c843c0001d01c041c00002c00a41d80010b51403809081208100c0c0c1c060340000215046082da00501452200d00c2c6400d1403001e8035015510490480b1b61003c1c641101c1c4400c00407203001101245c0c103400400d40310100d540480d9207107088017034135041000322100da1180c51140c0851803241a00c03135009030002c6803400d000e403d00d88a516030310000b242405c18a81000c54480b40d1007002c210b1601c0d50f1081c420f400c14940011100d056204505055030f405207480c030f40d4031a0010f0b40c4411420542515602c1c00344c25001c0f0300510032644c034134014085000703242103180b401e07052600602c0030034100344203c0c08035046a4003c1003400616000c0c462500d010300c0c101040c3d651541d00104003000f0390507040c581442d44e982c8050443d032404407580d09241c001a50f18440e44c1044060000 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 935285548 1250 935284298 935284303
    0x13050f030a210c051e09040608010f050709060906230d200307051e07080703110f0303040b0a200a022a03280b01060801031109070503011202010e090c030423 69
    0x1d00c80a0030340e01700020910400c00c1030850103140f5149038403d041c8400450072641c1900b160100201140c1c00340102d0302e85900c10384d10101907000d041c0004158040410001348a501c1c01d0080880104003202c99100c1c955003401c155100300c8180c0e240640f80c0e0404120b030030010400d5003501142c4c0e0056429401c080c0e600500303900c28501c2202c074a15205200508200701d00c4100e404d1182e002c0001599a0403e21300030780074201038001d000d00c0e80a191551010942c011003203a02c40e950007401c1200320ba507040324100081c0305a40940c00c00e00c001940d6408150084001001242043d4000346210440801102060382e000d0b0b80080000700c0d14a507410107a1800201503100c3c1c503d0725940d4071071904042c00c207003415540c003201500342002140002042c9400c100c800341a640a041c10346003001810092000740801540e40c2000648100010401221031b2034ac0011a144145403003664100600001450f106054502416440d00001804108090038070395002214107808404000c10880301c2040c2c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 935286798 1250 935285548 935285557
    0x919030b240439080a0b0a080a0c0e0906040201051c2c07061409010f210c08010b03040b04021207090e0f0c010f02150403050408190201020d020304030b13050f030a210c05 75
    0x105151b888907034641d407a650b0a041c0398094400c140440f1030640c9941001000c2c081507104000c0c00700071060100c1c410510108015105035010385442d072a0031000303280740849183e02c1c125280130741c1d0f4920304890310000116842c46420601c10320b99078200c2840009508020300c50b4030031030070b000d84070000305000141300068071951402400c009402d08080780e010b5843c0103c3c1601702c4042c00804004d4207403c1c006600c041d040c00841d41d528402a070300d41c02c0e0130301144019100900b2a42d404000940185040d025121000300b4600a403400155500e04410581e400c62040700025080000f4034031170320100f04812001048240380114824152403030280d1140d60010020400b101480000380500d80208102c0300140b50072004c40301c444072100c3c01c44112402407041280103000342c1d40301000b003910000689040d03c1e007003416250766845081420382d5603070403100121307030794000d5003100c84a59a060010b00301110b0107486054501881c0490201055800901002094600b5113200c00c050f134008280e4 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 935288048 1250 935286798 935286811
    0x40201110f0a1709150d0605090105011706040605031e010c050405010909020c010b060a0c05012025050f0a030206060a0e01090504050c030d02030919030b24043908 72
    0x15200e00f0500b810780520781c80780b00b002e9600600c8030000f00d108044554014600c2d114072003010400c0b603441340300b00304280e0020310865000404da1680c0b0b0700d020095441e16504018001c1c40050070710342da000480c0c00d04010341070032300b507142c00e0307044504c00ca000a024003403038070081c0d07d0041e14050030078001030310b418002d01481a046a0104200031811006d40c0503400594004158a840c4c14905000600c1000c0340c0700101c1d0340b54280300b02070304d9180ca56199680742c0040007417024284030072206000c02c5007100300031403084101400d10348004900709004240c0f61141c480094194a02c0504010340f0b018000b2700300502a031200303001005620b008510441c1035440312003000c01c0329211420058a04038501902580c107018030a0302c0600079400000070001a4015524000c00c001100c0588805102620000d400815000c001426500d44401030169500d00e10032580302404400000c6030480b01501c450b8002509520201a4a901c0140c003400300540e101841900034400904c0c001c0454030007800c403 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 935289298 1250 935288048 935288063
    0x100302130c1e020a0c0e0403032a030c020a080c0c091506031311130204090c090308122212080a0e07060e061e040f1a04211a040201110f0a 61
    0x16001c020302c04c1c895070000a4018a00b0008152103c840e2000440300707407400c401007880d0001080c40007400054007101c550f01c40c104458007484140080c0c0142c03061403020342c214090a10340d0030005580e04d025240c9951160001e040354240036051107202d80b0007901d0440c081c01d15407004c407100d41c5c0740c1040301d50140070b03010b00c88841c0c03913145011040000b040e280350781e005080c44000b4403c0d04284d0b0241c421211848018482d080d4440c0040d41c2400380c0340030280c10034a00304182031803050841d40b0940c02042002051958020342805a0600b03002100120742d000303a00056000e0195008134420b402c04c07507821040040010404016940d213015205102c2482205040c6840d42d0f919001925440010b000304010880c116580d03c104c02d611074041d401c2e001000d0b0740040b440015840c005140100030340095850725040030b1003103801c0c20046100c0c000141a0b10460800a8a0043d55004100c520341000485003054400903041c1807640b03540c451a58807250340d09100e490001100c80b20b4130342000f01c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 935290548 1250 935289298 935289347
    0x81012080d020409142a19050c030a08041211150601020f07080a150908030f27030306151602091312170903120627100302130c 56
    0x900c401070b000c1c940c00203080b645030102d084212590112036a115500917040d900c0c05440342c040980c1820200f400da40d201c90000e0020312100d0100140c0f140c0d440042341401428201026003813850b40c2d105a4004000032004401e10080007400ca0b22190301c95900d04004080d07814882d084c0e56180d0f00d40402c800e84070f21940c08911964001e1020408400024003642c5503aa03c8000c580e0fa1012400e40488044c500300d200410098039610076590f1041e40320600d130b0300d1521208501110300c240034200c00c80001c8104410020050300d80c4a0340c1240c0700c80c1000d1901ca240c02c0c070420001c080c0b55402107401d0413080120200003d019039200c4000765049030070340d00725111700c000078000c030000740320003811820b80203958400c0c0d60b0001950303a03a1903034000105407155904941c503510b90141315085081d80d0b17806004100245450bc3c0030100a41c403100e4500c4c20400786121030140e150341920b151544503000a410b00560a01003448604020402e0085c8800721a1500042c802c900209074160304445161 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 935291798 1250 935290548 935290567
    0x708070303091b031a090717070509040605060405060a06050901200105040c08190c120f0c0f0602010f021602010806060f1206010e0910060807110708010c08101208 72
    0x24410001540c0000c1009103260760140290b10f420120300054848410f14181d14580022000e803003441000d2400150081c14540030b059031008007004d03110003160251000c081101d80302d032020103201e14094400840c3d241025001d12080311400b800e003e009400054081c014541c00a0071070340b1206d800c0c640b104c6225600c1c0540da42c000425085068a942000207202c1030100c43c040710002d858201e400d9418444102141d001c94140c0d15000a1550008080410554240104600c00c0381e00441038181150941c1e5221000041e00e9080107000307485501081c00816824854210b50f4600c21008601d80039015052101c1a003051038024104000c1d00001010ba444800a540d101c1c41109580c6844500d00e500340305005000702c401c603000401c540c202c0c0000d4500010164042c8000300303058001642007400444c0c407900002c00c0700b13013485025103250800c004100071180c01011080c000051169a180004200b144098141c50300b004144100b8084048134000c01910307250302042081d9101c210302e = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 935293048 1250 935291798 935291801
    0x30203030f1e0415180b0907170c040c030b100815030a17070c05130b09060402040b070219051206040b07020f030d180821060103050c16021503011d060105040b0708070303 75
    0x300c540c0028058001c001c5d40c00c2168151199009040700d42c25140040d80f40d1001c5a00d0b041016101040350f8011840c5040d203050036805a0441da034546008916082014040303560b00c010510014000b48020041041c04240003100c80c0d031b548001c4000c1c00d00300ba01611402005800040901c0302010b001500404109402030004001c100103002d21001c1e00c0000d4561000740140c5194a0080d080200003d4240c5041c0c400c48050700c003107101050900040b80c00f8441d034004042410128200008000302e11a90340c449000b59800400f00241304901d0303d458039800c20740f03001d0303c510255401039100701c0b01c0300004810303204407600788000010001c003032500d5954004140100a052403c001950082d0810004e07030000da221100242140070b510b03034000440c1140c0048841070721401042c0074841100a02e050300012443c0014030240311406403164440807940280d00c061080504480da10300441c96070041282e00940c242000c5003480c1c5441c000403c140f050301001015400009028020540607 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 935294298 1250 935293048 935293061
    0x121b0e161b1202030a08090109150f0902060f040812070b011a120703091a06060912070306050a15060e03061305010e06150301060e01050a050d05100504030203030f1e0415 75
    0x44264101e4810800d0082c0d22a8002906040028006c0780010f070b0030001402000411a4441d100321070082403071021b1402005041a400380c00340d01c88125202607951207000e000c11148000d00303242d460b031426841d186014242c0b080129051020310410021410314201c40c3c0c1100d81c0c1d4400641240f81e04464140c26101f054400d10000c20303d9020710001542c507600c00008148503a0005441111030040035601c41030445084ea44410200980540c3d8103003540c404e001010382c503040300c080315200d540740c038141d403402c9610010146c1e030740140d580501d110311000750007007655051140c87d003241600441c0d00c5500051802403242c00820b28901081400d50210b412402200160f840e075042150300b111445955150b034510039030070020040740d01490604901c1c102d940040c0002482c134501402d020307110095420030340d59401100c003049c038000e209008442c8214442e5000c0d5030350b07240c819001c0941c1c40e000361100403e4110450384800c043c106c03035205a0840e8010100800140400740785101034842e = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 935295548 1250 935294298 935294303
    0x6061e0c0d0908120322120905041415030307080c0c040b090405150402270106020106081b0f0105040807061205070519030b0325080105060603060604091104121b0e161b 74
    0x40050001c21b00ca185a80040074107c1c2e41d81e04c071040c0b552a0100b009441a030300c8510840c41048010555108540040d4400c13800060700b942d06104880d122810705800551154519400509001102b03207454803901c030840d54121a89a02420180c84150381d500040017008500c40d40e03000410705564034a50041446400c0b2100d400441c004801d031555240b80a01c04d1502541c2491001b151005001c00ca907030a0301c60229810000344100010003034010100c0101d1818420304210104180000344441e0000c2d04103070300c0d20b271100fa600a010004684009098204005041c420301d2551104800c0340248040039241c0031404140190009080c11200000c003080c3c21650400010482484082181250303140c9000b044140d81c0c8409118892008545031548694100411701200441d03070300441403181c0ba0780100d400e25449298403d0031100c00c1d80e06031044010405d000300c03600d0407a09500080d0030102070102c11414000b400d0845010408248000d00c05802c404413003810214281d89000da8 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 935296798 1250 935295548 935295601
    0x30903080307031a0901060c020913230d081b0711040e0c030105090c0d0b07030b0a0311100306030c1502032a070b040b04060806061e0c0d09081203 65
    0x280858007800400c5041d030070716503168644255180502d40210810b041f1032403901c90882080f1558200303e00c0d410010240c404181c0c902012001094502200714200c152001000c000607405903407207071802040c80060f44c01c20000104200c00c010f070002031410121826606030743c483c0d006140003092110401c0d1060b030011f00e400c1d080381c070b030090000d0035550840044c1c000300016180e82000c01d40703840c8400105d0343c114041c80d000c400003504030001d05500118918000030f0700c44020700001c1c2050040ea10954012035198800700d50313464824503111784076949003800c000f024915681c1c405121528810704070700350b40c8107100f804018002e000302e5030080c1c480c00d294458490b088986049234451041c1560341c2d0710070000e02080f8a604003085805403207020b00e5250030b03d40340010880382280f0090886402c003809100350440301030500b036072105007981c00c7c181d180c45030035000407a490030003084191004c00c02d03141810800300303c2c00310740c0034055845c0a11580d072300e80c0c503003120140003204038803c0c901d03d1 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 935298048 1250 935296798 935296801
    0x3030209040e0d03150305030405060c03131418151c02040501030b100b0c250803191d01051b0120030f06090402010e040507110a0605100803041d040309030803 70
    0x18040f441c1c800f00b84042e14100680041801d81c980f40110f5400b00416950080100340070078030b0460003030000e0606c14012a4030b08004640084c080454940c80608805003041114030030b0b1504003100300c0d00f8881c0445884642c07410100c04580000c0940c4094045e641c84a00b0740071a14207034580040840c1c01a0041c0842e594901c4c00d0043c0c4038048840b002a0020325001040e03001a1000304d0350806c1c030460003030401000c1d154a00000e4110b24a0515640f84891000507440c401880036000d55203801c1d84618035161a00009860342601a241100c840039080e002e0001e0f0f03030010152101480820880c0e00c40200b4400c0ba0b82c0140300401c0c6da2401100301c41008025030140f4002180302d02e615580b640c0041c2c0303400c010b12201d0142a00c000340071801c41c0307840340c2c168105a88560b601c0040d0307190200e440f24002050900740700e5800025103141d902e400421104680c50300b001d1008001c504003c5140902c0c102030382000c0003248a0b8242003500140125041c1842182264040d60f004283c030b596a = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 935299298 1250 935298048 935298071
    0x1020c0c181003060209040b0423150a0b030c0f03190b01030203070903080c0a0615060305011707150201060504021605010b121b040e0a05070302240f03040303020904 73
    0x4610060303208600c034203a11200c0307a224040d41e4009a002d07041c0302c0e210124041c1503070355150107500500c0a060b0000c0d901e03e0311a03000e41e15801145100e01c201321403045100c40503201d00307903044c600801071004407407600321400017900c9190034074049503041d0b41148e8603a100d003407110b28103100325110480e11000c0030050001114080f1140e41080b800141c00300030810000005400fa80011655000442c0c0d45c0181040801d9000d4020844003c540c0291190144155a01001c4a020751031071104d20380d0300340c41400000d405103d2180901440400b08090400c0742c0c1c5c0840c4d60755002d01620b0204440c0c4904a103c1500075005a0023801e4018025500e6240c000140310115482031801c0e200d80d030900c020340d0b64a003089590500d049a605004e440d801903404100760450f2680b003032003030300643d4580e498500a8402e00c040c1180c2441807010300355062841c010407141c00c1c10034080b00c094000c0d24052080b542080000c84a221080a0145840340e1319401c00394000d0143c0c950198000e030a003001e502c0d9 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 935300548 1250 935299298 935299303
    0x4091e0609170c0601240e24030a0c0201060513020a0908030c06150405060315071205090607030e0d0f0f141903150b0d1503170414012606030f01020c 66
    0x40c000d4081d401c8445981e0b03074141082c4501046c0c1c40550054042d8240d0b10500c0b80f084d9003082104a010b082d110078407241c144088026143e0762080d6000c0d02e808014090a8080740c040c90680c0b40e01e5200030310006042500003030a4110386100c1901720742c0c2c005000f11505000e0320001c8024080c00c0c05603502e03003000214094480710220383d41490740782c00641c01442454184503a60140c113018005142805034041441e0000f40c015288006000c14012140100c54044c0581c510452030400940b9090805417000390645a07081002c110035004035440b500542c1d4080f100141500c0300d49030074681081049000d45201e00c14042c03008a02c800020030710714035909200d00c00034010059604001d680004040c43d002da9003580500340215200708848800700341d0355001042c0d03459100c504414440d90b81d076030b400c4902104090010082d070001c5410880125080503140a80000b8203103055103002d860940e803c0c5404400444080800142c04070315251020090154614880d40c02107542e80c4501d0030003035 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 935301798 1250 935300548 935300557
    0x120305070206010e01030305120c0f0409020c0c2b020d150902090702190b09010f0e0601060807030b0d080c0f03180a120b1b07020414040b0604091e060917 68
    0x9001d03120390400080c54286085001341200d4044d40c600341420070000114a00c000e01a0240800b43c3c000d1024114032130107880103000030441000c0c010703620213003199101c2c24001d101102a119151a035008402c1d40241c5220030360b40390240b41c44c05810403ca01c00112000d00543c3c3c041c080a4244c5803801c1c840400740e110140040c001c84900c1d03031035540c54a00b03c1c0e6802d0401125880003100b41c050800040a1840c07042d00049607200100300c2410080000c070172039299481022141c0d1120300108452038112005a070030032b09500e418865580c0240c0407980b4035241d5a0020030221001900d0b03844864107210030b5034060405030949030754004040603848070000c10041c503445440c1c003100003e035020b206000d010500d5400014420185e0328281650078040c00c0030100700c5100e000700480d5005079664403c1c4151070500c1744a600c034034201800e10314400f0314020407550046182c50080340c041380c0c00a911048541640a106502c22124648000680540076004059103222040ca190b40c0e44a0030280 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 935303048 1250 935301798 935301811
    0xa080109150501020d0e04091203061508040804030f081b030a030b040506030607030914101a0f01080c0a0513150212131206060806150a0b0705190f120305 68
    0x280951001c00164081c600c40a1040c01d026a10031010f43c540603004060012044400610014220419448001441307031006001c80020340e13507180c184079400040707a0442c0b000b501840c154000d0703d070030303503801903a0b11032400040c2c420500400f08408000b0782e60101c0b80d04e104880001d6150780401c4000542d03e0700861000b9002c0b88c184910001c01d030505100f46449040010b000342500d071520b0409500030240744209a640d050700014508008800300000c2d4041c1180d0700c000203086140c100c028203580d0f03440d800a407080c0448103284145aa000e80340540240407142c610380e4640550034143c1d2a446030b040d8011160b10344050010705081c540c61512284008c580958800c400c05504100030b502c211848034603e6400c07207000340001111308aa03884168854040011001d4076214403a1034182c0844040c0d00850030006804541e0a10040010050001e450744d28200001a0380b05e81d00e4100c425510703a00d200c0a00e05c61414050702001c0782c02020b42103030581c2c0e0b102440c110000d0203404121190f = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 935304298 1250 935303048 935303051
    0x17071104060515040b1b0f0c030d05040602060414010e070303030f050601080603030d2d0902030d03050108101517030304210c060f0e07080d090906270603080a080109 73
    0x10b4504240480c0d40402040e0088149000d0425522540e584c0060f004031038801903400707140c9518030781048000100c038030080060031503981680415181501d00c4400008001e4144420808541c00141c810b4129503c41050b600b8801001c09c03041c0141108401012248607401307001081c56056404100c0d41400340c54140480d913920f01c0151071424041d00d0702e40e05680200300c4903940c0a060340c031130150340e541c0300d0000c022208107941d9035108020f1003000d910500ea0390a03c02c41146400c01004004905c9402c041c0700d01d602d80590300342c603000c4030700c10100c100e52142650364941d0801c00c51880505440c4648a010003c691901e0350b07250000c0724101e8070700d0028880120031901140740a1000c00c4542d90705c1c0740c2314400b80c0e030b480081c0c0070001070620003e8580310400440101400000041c0801c41c0042007240c141c5000180b1140450703102c000f00d207180c04820300100c18501102c88210105d5500b076048103410220040c0100380c5e60b8005000c4000124110200a170301c0b1600c0e50483d02030540 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 935305548 1250 935304298 935304311
    0x140c091608010b090d030804080d090c050f090f01230402180a120f12050c06090c1905090411030307141608010c0f1107180212010f0308041217071104 66
    0x3c01030600c6450b480f643c0c00102c03420402c00182c429421980c0c401e200c6e43c10141460440345002050310006d102c110780c2c41c2c40703000e0180841c1c1089030882c03001c0d210856142c529403e00b1407040e00111411301421800014848420b00c640c000b0104da8050381d04050003c66807112403d40c2105d140e400501c04134825107042c40006030f41100c5000c8003007802d4000c1d00f080c0141032140c2e50350003804081c1550b001071004c284440134a811003480320510400d48078001d02042c40b07549042104080e5072508241124800d0f039028401919a90003c550250380000090303a00e800400000e8030798050a00000c0c40c5602c0060003548140012aa4000c50100030700c00c01d440030340301d0601500b0313140030000d41d4001078810302400307a03501e04c20100c6051000c4504140c41c0c800c0e80343c0b00080e0303011001c03e203190300b03094001030b980c0c0702d110361420400d00514401c0007181820742503954154140c80b5a02c52002c85405564070700040c0065001c40c070141811a070a01039840340d05262080380c0c043c12004080c4a14504035 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 935306798 1250 935305548 935305559
    0x6152206090303020d230c0703051009151a3f060a1d1b0a150207140105090a031b1e091a090c070c050d0f140c09160801 53
    0x30030038282e0f6495000b5094181d4950801c5544110125a50f00e1b00000a100c03040140c45050081000d80495405403855500f1400c0c80d40c03030f144000c841c0c501881e1034500401c02203801814081280c002c0e03802c0114a1543c5070903248202c40c0007880c2907500404800c40180302c800c0f60050401c0b100ea0528002000050150110320100c810454400080d008600003910705105c030b0b401b0031225128403000400314000e220040b807806441d02c488010f0304d40e10488100251400302c60000c01810f01c0d000c10040d81d140c0f503070001e468285501ca0541020710907512040c250b8000c0041d0792401034041d09908119940c0c0c181811140c1d01c81481d400250740390400410b02c0e110400c40040c5441e80048404407651070002c4000041085444045035403036444802812035580d049060300840c1d402d0129a11000181400c80c0c0801c440d602081c42a100c000e1060009010268940c85031078108503200b808240c07544035103040146100ea07480e40491800200900303090121081604c261460b076461106a803a207 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 935308048 1250 935306798 935306807
    0x1e0f0e010e0f150d03021c03150f0503030405100c06050a0203191512030309050102030c03060117040201090905180601080313060e060d052a18010f0e040506152206 72
    0x98548120300c4001c8514600c0e18141440124002c9105c2d10403100320300c071101c0010380c0c0c0c3d00400d90a44002515480e00005450201036100050840701049800091920b80040e03a01d01c81c600c109801043c0418803400c455005403580c02c0200d800001c180b10510f860701e039507002507100316030fa643c0014040006000f1000e152080c14900e00c180d000c000803460601c9040101c0100c0500c04508064035980b110300000e1080c0084c5004640b0700d566140c80e03040001c000341c1880c9203805142410300d0100d08200150782c1c020101c0044450003000001c994941c4040300800000a41c2c00d90224466880005440c20001000300400c000310a5502807280e1107000440d0070742c2801c200e10742e020100744850704940c107440d88040e400880b4103400b10303050424000d1003501440c1d22070082c0030b10381000c1296144942004101d081e084000d1800790050783c02440c000c0e140c01071f50300c1118040c5a80c0c10010f152515041148071103103c1c204480da80b1240150460002c4119011045108036106500028a01d00070b = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 935309298 1250 935308048 935308051
    0x11104150c051e0309040207050105070e06030403021203070314040f03090902130b0c030403140304080622030c0516090b031204030f0f0f1a1f06091e0f0e010e0f 71
    0x2c42c02810345806104107040c1c2070035201c440d20500b40001c100c650556540c0340f0040c85010320607400481c9501c2d000d2000f4141c0d482170240340c3d00844003001007000081e804074603c0500070320f000c825a01c0c1c1d140d0030b0040f002402410340300306021034a4402d010074032040900b506072180c0300341c4d98502001d4030b801011003a8080c0f0003806000701482c0009000824400b00603205c0d50070088216410035549403550303010040c0062950409420000c1e043c00102e00038011213074024401004603a010500c1c0068003900302c0b6046000c1c040000c0e58544404000050007208403100501001c0500152640d101500418111400360320a00c074050540c00c1034024a0107480483c1e0300f0041c2c525000e420307a19084840b502904007200c52601351261400003452211380e803000c940a01405910b00d01d001155a4950800740c09040c0401910100c01c200035580521070030291200302c03048070500d4007200c3c40e2200c1c0003455000f245042c03600c0301c40460a035085541c410304a642c4401400d0941c1c56405000b02400320 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 935310548 1250 935309298 935309303
    0x30803010e0a06272f0d180f080a030e06100f1a030420060304080c0d020c031903030b090a090209070516060b27010602121c0e030c011104150c 63
    0x2c0c00d40c4c008400d545a548404801801e50680c1c07051149001031300f024401c40303c514114a150f001c00c03801c1000c07500d4412404120141410082e4401d01e0b038a500e040ba104d0610002c107000c10000710b22404e03c0c400c1d004649000107010440790300d42842811031964024a0059402d0305800500006e50380c00300c40414403030551121f03292413640d04c86489401281c1d0044004c0e005c940c0703114903481203a449200085101d076000c0e00f41980c40d9001044064104031401c0c03440c02c21503005141f9211950b5000c50740a5104408a01008015549241c00e07800f81c918008030325803150408080011015858001d800c2c0a4421601d8000540d52a4402c6c0c0d807a000740d00c640040c000704001c83d030000a115034004050f52100401c2030780005c40c58400742e04041d41c064000f0a045062900402856404000703007146506030079080380c1090201031400078034000c1c000c42070b01556207850510b074400b10240304031482955880000d02500c82c5100000045d5805031048054481600c0f00851109216284004c1c0d4a42d = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 935311798 1250 935310548 935310599
    0x2406110d170c031e0a02031009050702070501080a090219051005030c073e040c1d0907030e070303030c08010504020313020d080418050105030f0607080a090309030803010e0a06 77
    0x320b44034140029600014082c480198090710344142d06124010118818200442c01503900c1c0342c081080103e00c92103510180b407290404050102007a008a110380940b04203280040141c0d640c150f0590152480d000013a410003d20740401c1d62800c102c448940644400b5281c0c0c250300c11915604903404d120488403151081310600182002a4000a0074682440c130b00710b20075044541d01440003801c010718a9149408a030082600c00740b41010301848a040003030f82032aa485441290104440d0511200701500c01c2c1d2000000852450207036004901c00b0010b85d0844034260b0703c92402030014403445540c14085400b0348000203047c40c3c036000f01c074414611220801c00d400e01ea44c1c280314142c000000304490510007800041801c1d01e1891091081d000c00748400b00fa254549003d05041c441c0c0d02c01c0066494000001308160150807024107900001840c0e00000d40c1d10541c107084030404031540005005020001c0000780708030f00e0381c1c0f40038001c07500d001d4100201d80e6101c00488014140700c0a219900 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 935313048 1250 935311798 935311801
    0x10516021908030903040f06050901110303090705060702040608010518010605100f1115100608090102030f1f0801020708180a06091a0d0f0623030703062406110d17 72
    0x102d8180166402403003290440e41065201e20f04030784404103d402120000d8004150a000341da48541c01614214118001c0c52450900500d01600c0720b1a9000d524003440740000d41c0011504c5540c0000c0040803000b00030009410103113601040d0142d444441c019039803d2190105a5207001c140f0030000d91040e8540d119110a400000d030348000e504140702c1c0f1203004510358000416804022148905c0070304889886080c1099000f0f00400800b808003407240c2e10500410030110300e4801100c2d00241000301d2140355030b9071151707041c80d004090381004038294000301300c1c041004045d00140030303500d580c0790705141080c0449042c80080071280c400c100001c1d072040800c0202d822003200b1704132004a290769280c903100411480700f06441c0b10348501040141e07101001c1002c2a170203c0748000041c00000c1d031450f00910000040e070340745400c0c00702409142e030300d2040d070740003000801c0c54a41d50760803d2941c1d00e00641e1038802030030202c03600c01c0f0405280203440d0a40c0f5524403640d41c100d034914115050b00400d = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 935314298 1250 935313048 935313053
    0xb150c0303010e07030902030a050c24030403270b0325120209180112050601080d05180406090906050402090a0b1305180f0c0a171b150c0105160219 65
    0x524000e41350030185540c44140b800541c4051040c2c0c4080740c0188002c01e1410780700781c148441d550f0500014502c081c64140032082507140102100c2e04150103282c40120001e541c580c42c140c283c01d506d28691040301249002a00e5520354010f507114142140a2a000e12070784006040210401c40d4080b00091700100c001c540314000342d0160a4010016244104001c141d215545080c00c2c207801165610700f8044000d81003000801100340504440310142c12102d00c02000a4007074000c0e180411007058203a02000b005488980c841c04c02080084002d200480c030750305040009010560703042e07000700f00000015040c1903140c050402c80080203000108651440e5038010700411000d060084c0030907040c5404c2500e4a010403012030012050300161100c948071104100c2d0156aa0340a200c009100d900254005000424820310700e10501c0d541220a80315131000503910059600003042c0007101082d244038041055110700d2140700c510070740c07001c075036480c24080e6561044101000b10005510110000 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 935315548 1250 935314298 935314319
    0x1e0b03071206120506100f030f15111801020c1009050d050102070204020a080f1f030b0a110a0e041a0604060c050f0105070305072709022b0b150c030301 67
    0x709541260002e40340380c50b03010308003034031400032010b4440e9804070f0140403800c000d00303a050b40100303424001c1400e960300d99a00c3c5604074102c030001a091035205000340b150603800c3e8100f112086801034007a90740315420441040448202c03e2914018403c980c101034030750034503400040c02141c1c95110b08507654070b03090402030650050107045940b55005e01c0307804016100c2d13001070201b0600f1911041800d15211003940c80901b4024209445011265202e2a8903401d42c01484152a0001c0c8924407607500e036101040945840141711021060020f51107109650243e07243d030b8410401c8800b03100c10341c03d8006584003c2c40b0300d081d80c1d901010130072042103c140200c81e021019842030050303039031001e030454005084600c112201800b280d02c8008001d440769115151400802c09014109405100c3c041d0a00a03a9594010b1841d81d40d0700150346201c1028030f0306003801d614050300301e000034408c034038210360003400043d83d96600131400b1a009803c3c0009170801c3c1c98407010701c0c00055085038a00841900c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 935316798 1250 935315548 935315567
    0x5100201202221020f060d06050306220308060414040c0f0b070c050d0510060902031005030610170a052a03032107110d020616051e030408041d011e0b0307 68
    0x380d10240d4101a05c07001c5d159100030b8021064036001c001102468442454103003100240521040c0c8100104001d103c480300100100241d0180f40810181c0c4d91280490020088861200141000c0108010400451003042d40642d104680480c04a43d900c4600503c240200d07080103140c444198024085803d04824041600340038908030744c40300d41e9903840d0804403401d580003031030441c0c1c001041002105c0d00301c0151004110a03401060b8520345002c076404000050302070352a0761000125000c000440c01c00860707001035000700541d08030601c401001059410224118142c446040116001c1490b010041d02c504008500507400e2620300b403002554044d50082100701031001d5400030200c848000c0240c0641c803559074000341007904084c4250b4441c591075400900c1001410491442001d1140c1106405100b4440b00c2d20340b2130321545044a8140181c3e0010712459a10f4501007100e2540d16450071b0480b040c4d0040940c0c12406117101000d0040b1501850012210400102d00007611990307400 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 935318048 1250 935316798 935316803
    0x1406090c0909160212091c0323120105030c0d0b09010207060603110f040605060702040b040e0f070e0f1608040201110609072d05100201202221 63
    0x31072802031103000064880b44181c480d9903c0d10300e62001410442d07010040301010b81003180d04241040804000585100d00c0016002d10400e9451190302c1010b010745201c200106c069500b10107912081720102c80a41c008000c003105190400000088500380400c0c45200c1040c040c01201900c0030b00c0d120401c9405c00500040c5c2190b500300b1084001c50583d10072080914840d008000700101c050080201c1780c4c82c00c2910610840ca00340041045643e5403049610307503913043d500800c5440803980018005c01c6140c480108074000d40390b030a00c00301004035031001550b80d80d00c02c0084c1c684030101400d11181080700d54442e02c0714050b1142c0a402c0c010b284050f8800c3c030514114803206488400c0900f40362080d80d602c80c0d07503840301d2800e10462a0890404a0b040954a0040c681c007030021910459420148076290048403001701940070503200790002c080c003c4421961003c4140f090b40003408540c00b00448210f004a181e08501c502561030300032004603079020b2040c3c14a01e1091180e0400c640010808 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 935319298 1250 935318048 935318071
    0x4021c0c0b030106031b12112a0d020307030f1b0c32150a050d0c0206040b060d0b180f0115050406120c03150905010509010f0f140609 59
    0x8800011088000e900180c03111011880d00c9524200c0050b040e5403e01e43c0d40c15a080c01301001400c1075921030fa01208200c0d1080000c14030000703a800b07030304461181900941e0902c4d1018004400201c00e0f56440340403c08000c21203400c02601c01c022600c0e40110b01000b00000d90382c004a040c904d110703001d942889503110a840b40b032404203994000000800ea80040092545040500d908140320a1002c41660240b01e0840044846d070380014448005070501d000000d41c04620ba00c0c03014401c4041d614810440c04003000382c040740d41030203550740108503811039071010250f00107807040c20040d2001590540c886961095615581d5200020f80c09101da28034462260808c800002d48090003900280c41480720307190210b904003401c2c40300703450707081e0842c1810303210480c442c900191070000700c2d0044a80102c12400d08250100344100035084000029085608000900c1050013042d4400c01d4a4192704008202902c0c9503c1c403071050f40e9046c1c1840b05601e00c00030010750b40d420300b010a01da001c03828607803 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 935320548 1250 935319298 935319349
    0xa0b0406111b010b0f03070f150509100903150e030703030b01020c060d1d0307080409020f0d020406020d030509071203030e0a0f0b01080111090d08090a0302060f071a0c030402 77
    0x3009040000b807000e440000c0c2c1c0d11400c60769080c5c205500040d400c224140c0182600c4d909121059991055070312500740611018080120018420020795101d120020071668917070440c03030802425803095000503148121a03031310f501c0090010b0302c190860510301201450410031552000c1d0014203041c02e000c1c0c1035004000d00342030702d03075a0380c030040505040b0300070005001c80c425502c42c036a0310280709000e506648204403080201d2131030381c00d50b02154ac2d1200013603039418104d0400b00803806158050080382c2c0c004103002c1019600882c0c00c2070410010380d8100704941d541d0400e150b80c0d80880c031600e83d00c50300740343d40000481e1203a0804826080140110b40c40406550b990a152100e012001d82d00d4502200050010000a00420071031280741c0c051303981800064000200c01c15400c003002884040c0024040d4107a0303c0310040b0380000c1d42c005144076241c3e02321050101030781c0c2c451801151202c504122169000c400000d06600901d030042d005411a9602d500380301c40d81c20300c1e0394000c6c50056800c0707 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 935321798 1250 935320548 935320567
    0x20f0106061d0415080a0b0f04022404090c110d03060605090103022104140d1e0e0409052d0102031b131503020d140f190204180207020901080a0b040611 67
    0x404c0340f0000d02d000d070700500c000101418040d0b2106405002c01102e410950280000f40e03a41403108442414a541d2000c0360f8500075241c027803d44156030101c64003500f0030106890454103d140c441480420000352501c18101041c00c4040302c155029440c082082400a8129035109601a06201d80ca03600c05111031142014081008403088500b140d0a0410840e60490048144181c06100096040580401e03014200150404030059884070401140d02d480c40701c581c0d200e40140c402e0341e0308030b0252000503400d81c0064019060701c150101c0b460310240c10004c0035240520032207101d00340800d02500b8443c002014000d4580c042d4000140c0158145d01c041214055541650507600c40746d02e0059031821071a407517200351081c4014a500080700031041042030400000c0065000039003411091070000c1150042d0001d0069030000b254100032504d12840510382a4010310109000b01e074064030a0303985031007460340d5006112008165544900c049400241c030f541000c0c3c0c5c0806884402400d290141 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 935323048 1250 935321798 935321831
    0xc010c1401020912030309010c080f0c03041e12110a05070b0309120d0f0506041118011e050403021201050c0703030b0d3509061c061205030406020f0106061d04 70
    0x110080138150000410f00c1118682441680399400c0e66041490703203489c10040c8140160002041c00540510020004081100b415508c40c5c40b08c0c5a252146c403201b01c4c42c10f08524440407449808080b0308144c180c00e882031400107141d01070716800300c014082e080c10002984802e820180040c400c901c501c0030368060510b004400f40490403c2c82000080000034809100d0655401600d401c0c02549070643c10020450010200d4250301c4d550307010b14201d00c0740100121504034507110410400000b40c002c44a030203910200030b00459000312981c03d80384c01122411400c1303940540d800c0c3d140d23040c200700341d100290081e001808401d078020511441038450f51107032207044c06805490841c405038100100038050440d06441c10200a62840c0360600b283c81001c1f0704140b0903074814408104800d001c00991004503000751000d06000340701884c05000a240040d80c0e6002402880f016008188054000040510484040700e8503551110840303002a01310500d0411100344140d081904c1e469002002d0040 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 935324298 1250 935323048 935323069
    0x50c030105090313050f0d0803130c080d1701081c0521010305010e0f0705220c1806030c090509091516030c0503010f0306110d0c0e010306080c010c14010209 69
    0x540042d541d5503905001c04c1c858078007a90040d03441455400e02580054a400d0480840580c0c8807424555275210102981b40c0246403100003030100486400100342510042441c403444070380c9494503228a101b031580c840d52081c090003100c07000d60246034240b40c11168a04810340320307012800e00c90300e40392120703116079a500c440c0214140c00b441424010002c00200f4403032280c08003442c1002c1e1502c0c01020155035128101c5204040c842c030018002500514100000e0300208164600c2c1041120800f200c00b03802c814218404112018070034500203001c0c2e01034001c41101e140e10795920718200c2e081208005203848040e1a40c1828420301080100b8040da581e02d003030017000c032021424403a0248100c02400c0d582c2e0301c612003080240501c0100a5010028002e10903254048008900154039801040ea0343c0154000000c80d47d04007400c0d50340c0c9540041c40b41d14070401c2030340c3c24400305850301c0140355900100340882d070004e02c040c0d0020022500081c141045c011292002525051060001402c1c5222 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 935325548 1250 935324298 935324311
    0x9060105120423010c080624070501200304050303062106070c120212031303030209060f0403150509100b120f0102031005100f0509150c03070507230d050c030105 71
    0x501081d201001c8104400488283c00708000a01c00e00032002c00c0200000d001030000350181c3c1d0340002c021005000300e00201720014003030102c60748030341c030138241680601014a00c4410705101e000c020644c0882c4036040f40d2245403c00b005503d19100d010a1008140803c11000040c0900050304000028103000481c080c64080d601c08039058410b04120509410a608020640d413095422a03102200070f01a03c0d4480400f000100304a525030800b40c0191040070020341e40120001011b5107492004c0020f40300ba41d00401c0300707000103611610110216035054500780070343c0e8030521070001d0b10841a0000c410212002c4e00d03515442d003170032131041d150821a60401000c0d940200401c000380c507808510b50000e00048400300d40580c0c0d40c0c600a0310006013a100d000410100040f440c0701e6813210045860703880c01420002e540d0700380c20206207460303030000b64080740c160240c2ba0000440c44204034440180c120f100307400c607204000039820001040c035601c500700c0302c42c002e036154002e0a079001c0c410148910f2 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 935326798 1250 935325548 935325563
    0xb100804050c0f15030408070c0b180a140f030f0706020f0c030606010906230f0a110114150d05100c0206010807060221130602030d2009090601051204 66
    0x105450702508110030741c24440e014081c80d10700392880c0d0750fa0000c0c0208100c5030a00c450380c0c90b1034074180719005110394500500300c44003103000000c40c110300748010907286c803500843e0015895080b041141c080050f2185111280382d40d4110080b07840d200c43e03007040c00ca600170119a1424021880d0a0500c601c552001015030003041c9540c0036800c050004e14041c0710120040c050314a41607002a001c4a07940c040d440400000301d60300c00b00301c0d183d040d40d03103100502258103948401c4401c9641c3e18903889504e1a00c001000c0140c0c03084244070500401503050f107159200c54040d42c40807003032240c0c400c0c0c20781a140d114100c8400d00003c0307641440040020f28160030081498420940040d02d484010b0340190215031042008214143d80070509003c1150103422200c100581d0511480b40c6014000080040070410040003c0583e0000010200c00d101420b0070b00c003c03510450f181840300c42c0082c8907550450700b04101c28040ca010700c03e03940d21440504005042107088c41194410b041e04590444401 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 935328048 1250 935326798 935326801
    0x50c010509011d01090c0911040801240b1216170103060204090e120a0503040c030219031e0503070803070314040b060103060e060d240e010203060a0b2b0b1008 70
    0x10022070f030001d00390310f09500090200300e249550311082a1114801d07900e10507a41e06a0003486580c12080b40c0c024503c1c00003d1003c03a01c01000034046204408511401c920340080001d140010382081d5960a0b2105541c6402584d0307000300ca0114219503510304080140551199041c0c400f0002a18080c500503000103031114240302c154012594080010b81091780441c03450501c6804030300441d8040030f0286072071601c90711a0b160446000e40d40e42c10003903100713408c00d41c4c3c4036482443d0a400740807030340030f043c400340b409040c1c001d0f095410f4400c10300500320750030810031040031485000040d50000c9103490b0005039038440e48008000351000742c030700b2242d4141c09814400390f583e0500a13032000e0110400b4103885030400b000041c00c8641d81d1400148a8501d1000b44c02440503494030b858480302007044140007129030048076500075402182c01c2031080c10488004a40d8042c1c4409880d0304503c4000540241c440351b00c95601180d001d54160791100c0d07101c07030911500c3c0d00e036070384c821240711407545030494075 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 935329298 1250 935328048 935328071
    0x12100e010b13020301080a1709040207240605010f110712030f14160f020a0506030703240e180106030816020102010f1103060d020f0303040f1805150f01050c01050901 73
    0x460102e030b000406000d00500052003d40d501141d107444460703200d20b010100040b426001e03c41401490b190341d0f84a031000c1408014052401c21448280f4240c440c500c1210044680c1142201c805004d0315000030050b0000340b040c80d0007840080d010302241c0741224442a81e9001d480207056a0580450018644107c40c0d903649400c082e030160300c96480d800c0c0c603052800d40c0c4a0025403040c02d40010b4510141c141c2d14000f5500c0d940040e5002e4080030308685c0e80e0b480e0002c00034000c1d00309103003000010002043c002164007244504141600c200807071034541c98036881c200c1e5007035151180c1140ca0075540c60328004005120b032002000c50034160a452040c841c124000a82111074218030303001c5490808540b9000381e030641d000c0b0b070782c4148101c0d0304251070325642c008036032710f090540b28a54251100241c046041603010340d041c02101c10307290087d244a04a041c3c3c5201b40c94040d50007008001142c541b40159203492400142e54800614116080450102c540ba0030b40300c042c0d4400d10a030f50740b07041c64000b = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 935330548 1250 935329298 935329309
    0x315080a05070614120703020d0f0f0203010f0b0f220b04030507030b180a03210608070806160504090504020607120e150a090504050a11071406070309020102060612100e010b 76
    0x11215000764003508000305110600e03000c2c1c2c0e00600c880e00701940014080c5156156a01060ac00f68100d5001c0006030504002c10000354802c0c051484400a4081c00181c150b100c0341c22118818905841141442c010040303854071460088000c0082c030001c50b03400b080c0c0492344c6015000031406980203207150340ca103003003100c0c1d50340c0064500303510605080a6280301400c0015000380580c3e0515241e8069144894180345e20358000a00000140c02c01000007805500004d50178241d56480c4281d9046446503451890b2034101000100040788040c002002114007507030100c0e51042c0003600035890200295281c1c6080a252018000464100b10030f14a40d808e00d084440c058040f043d600c01d10b401113400000e024081144200f074030540c0c480001a0303070082d8079008006c909820000d21512009541307000f002c0016120607018141c4510400294450301c03a0083c411001c1c1c0680161116032110000d028203c4502c0840c010700e03120f064114040d02c0007503c60130000004040000400302c148104022 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 935331798 1250 935330548 935330567
    0x60c01050a2a0f030e0f07090c02012304020103060e09150c0f04090e030408120c062d0612030a0e01080a090b07050a0c0b040c050f0405160315080a050706 68
    0x2400b5200d54100720b0700c5880c03201c200b040d607084904002141161001044003d05103070290701c0d14134029018018008440055510292410f00c40309100003032001008038200c51016101c04d82c200c480b1402d4407031a114041c2c9254100380185800700728503032901000d0300302c1c0c1d00644000080380c2c09130104250b2a0708100301d080d045801e20b1022031401114050841c0e4502850080450071380d601e10200081010401c2140c000f04401070a0340e610303000240d11101e10b80c2100d800e085c41c1c1d004030380020b52903665114481d811415841380480900908408414401c0001070915400ca020f44038210252041003001d03109a2240d5a2801402d1100308001028040701030302542490f03003400d0184000403800920380364004403600d0641e4580f5214030080710000c802c1940540f01c640c031b080500081c002d40e01c0008003035880c241c40030040d42e4008410b1104450702120b01c81843d011500403840c60622942000300380c9582002aa6052030300d4100700e6040c042c810404554941c000c3d80100405600b019544 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 935333048 1250 935331798 935331821
    0x703120920090a1a0103021b0d08040c1202030d050a0302070c14040e0a0b070c0510020c01050f010819110d021e041103040c0b030a0204090507080103050f120d0218060c01050a 77
    0x81c01004e4076140c2040f80910007050f02814180c000c2200a40301300f02000380c0c00080900b20032644100f480b504058603840045d5416554102a440b011603241d02200004901e03650150080641e038203600c9044955400c10180d800805030208507600100703c401c08030700c000c0d0020b401e00e00040f003400c00803c02115034152417001290840300d00c51001c0303900c0032003082e4012000c0c2000c440c0303000c480c54084d082101002c80142080d04c00301c2d0001015005600c420300c900c9182c84010041d980340c04089a6a00300101704181d40c00022680500080080329003017501580034180303d42415450740018035011094404604100e0905046005403615001d03180d111000313039244030315500b03154880414520450290303285107580000032507c525650390403140142041c0f00304000c0c40c146800c2c01081c580c0203110076a83c2d8401d240401040460114000850710101100d5520f412150b0101c40f029420140407501900b910f00e06041d01030721044010300106021400002e82d9141840000c0211580710015 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 935334298 1250 935333048 935333051
    0x306090d05090f01050c1002071709130c03110403060b042a080408190305070e03120d0905070306050c0304140c0d080304021f0e0a08010b060703120920090a 69
    0x31001090303008002c90310a5081641c100401484480050300c4c64401c0b0900c411840c800c000340986030510319400383c1045881011000451a5125108007590194100300c550107081c00304c0410040705654002c0c40390004500300031420780c0d05040341c0902600b190b401510000e803286541103a034541032290f100300c407281418821841f0b84018445c50040d5041a800f800e200f1148040340501200f2000c0d50540c4d0070048130890341c140c3e82c600003006840180e9110011456902842c107071840d0118200102d60000030006007411032600342c0a015211300101514640503001000c004940c2c1030250900c04c140404050380e40313042900d0001848a580c0190100076046120307510359a0355011044100d01c5d4005410b681c0320740707403800021000d2040c40346054115854202c00322361541c01604071f45111070300705d4112040301d03590340c080c900b80d07a1140b201c25480350042188000103030003980b08240524502c54001160001030340c6031082c41c1c814100400882c582d88a2035011490095146640075004a40 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 935335548 1250 935334298 935334313
    0x9070309111f021005010b0702010c05100906020a17061c03090305071e090608030316200c010e010206060d021018060309060b120601090509030c06130323030601032007060b030609 79
    0x1f070b04c0e526000d1314070300a04001010403180c09104080003103510000744080b007048000000d182c1a03009500980d002e10109145041050b40561020090f901c42c40c00a03184401c3c00c1500e1004c402c5802030490704500b4010194030100201c1d00810009001c0c020700b0b0707e04a50b803000c8040b543d00e15103240e40506041030400600340b09000c4040192a0080b220804021030040c0d164001c1d10341c0b1120307000142c17080000c10005844044005100643d80b9404c0c4c841c0b100c0002c24400481e22803038100c800c0e40e00440d011940c00c0c014182070010071601c4c07116151078200411505500d44090744141e00c4030740040d8482c0700f42d08c24840c1700c2c0309106100f1404c40384d030442da40e00d120102d5101d0105200e00700203143d50b40c0000708050b030240101d840e4858203905442881c40d1429034040401c0e2160015400130b10004801c94068480c0f40101c000e20741031205150031695440e0045018151a004215100021178002144e28084d03501900b2401d1203194080354000401c028985800001841c0c1a2203501195 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 935336798 1250 935335548 935335559
    0x8071710050c21010e06010306050d020906180a1a062109030f0a0305010f1a070803070315120203060a0c120f02040f06081803070209070309111f02100501 68
    0xe403448100315000804500c581e02d00240514600900080102e0301c100d0102002407a0034150000c0e040c5d40c4100003201480c0c5500004504840040c0907080d0441c0d002d503c40b4000d0314040d0366140d800f10b801015490303000420038040341c0c0844140d074594842a00c80c00300005101a20511940c00d440607180740d41090103842016030030103442141c00f00d0a10022002c508070000070310403180302c07c0030601040d0792220b04040c0100100024031072101c00d113680003804903a40450108920005000c044802e04001060315406034560007d0460014140c1c1c4844181c1c07400c251103001c06c006e010f030650305014090725005243c00d1080007001c450046180c402e00c04070300e9400201c00c0501806458001411540d0300041c40002e1189410015103d00001000145240e0104049202d114000d01901100e106012165541c0c01200c4000390700442000001e02124420351140140c2c5019502409045c048507001c212b880e10050868a030207001070306182907268041118030f1000c49110420410343d031620 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 935338048 1250 935336798 935336803
    0xe03180a120b1902280e0301020f090102160303091806050a0603050a051302090c0f0f2a0601050607150b0a03080a0f0815150d0e150a0c0921080c07080717 68
    0x500b0705c00010f44000a80c0c040520502402590701c001400842d45d40300c90100384819500b01030300e064010301c00c1003040031601c0e080b07501040403654141c88014615051804011031002d240d01108146542d522000402c0d0b075440d00d808000702583d441c001550700f003800c0795909444009080c100c06001c0c429860b001031711994411507111100c00c0119407501c54160380b00a4520030344168403201c072000709065208003201c0c001043e15400d80100c8049641105501c42e40700c2200748500d40d4004014025080402d102c100044003040c0c030010005185901d6100103030b03d0701981e1700301b42c0d40f036400440c13001c5d44e280d042071421782c00300d980f400e100c10a4600040c0c0c0c3c00b01d503290314114074065202c0e444600d0341d969a174400d030b401d90343c0040b4040c1309010001084941e00d00c1954510f4121010303030404903006440c1e500c91410b0440c0c960342c40499450900401c00c03d0207440140030310040d0401d09051003c140c00c00040d15400e0707240b1002d000c8551601c076100307241c1081500a41c1e081c0c0340d204000b481a4900 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 935339298 1250 935338048 935338087
    0x6090905040c270536120d0b06180a08010216110303040302090708040303060b1603030b01020c0402070f02030c041b0f170103080a030509010e03180a120b1902 70
    0xd010f41e1910b02400764400120080103400249a2181040d052101185241a445058501541381c0c60540e04026904107000f50100340820100e800c500c51108403050034000800300c2e8580410f021801525103004220254400b103039128400b2485c174082d031064074154100078000c1100400035030a000c0f80303503296031031103200080c01406050800d045140b02d480c03d00a5900441c3c0040c82500d5514001c68050310041c0308030b80480001c3d241050110300500c032034054075420721015000092813401654241d00a00300401c1c1c280c150300c45c180c40c003041940d581c00204002c52182d001c2d8401186c06205040c508418807803410f00c92401c18a061400307200e5018910003050180c5803c100c8800c00c84419209061005043e05895240c600044103000040000308a00c03a06a035003008185c0c0c17119017403401c946100c911000150010480f5242c1520780c201b5003100d45000921010120399507402030f40c2d01c03000c1c01804807072440311501000480b058440c0c260384006c145581c294070f032640078800c1c00c006a44 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 935340548 1250 935339298 935339309
    0x4061503020315040504080705010e0d0806010e01030603050105011202130e0a0305030a06080303010324051b2a010615050a080f04060b09090c03010e070e271606090905040c 76
    0x60202c00a00110010030b01500c02c104040d008000604107424218000c5c0d0101109440c25070829070713114070710b8000040030403190b1039680c0e64105903260f00c401141c40511465406041540303c0e1004000b1800078803c441c002c040c40d012100003004140705006070201072915642200c1d203000303101008a140851420502e40e81031804c40d030790382e984c0d40d545c00042c11690003d40c090701c0040001b000f0030081280400500e9840100f4a16070790380d01c04030806443e41220500d402e0040000d4040030191800c01812000b5045180c40c40c81248136484d11865540500c01e5881d56034480908120584104030307128269501c0d407030600d00d450888840a00341480c080c04010403110580c000400b44080f0b544020b001501c010140107050603c107076941c0c5d5900d40c0d1038206100e94138000f00020f00f80c4c00060808212001c002c0c60486079901e280d80b90001c0103150764140c114190220398214502410303c907459a80015002021900741010390040c40c9108640001c00824500030602c0b005c5441d070b61001040b0b41e07 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 935341798 1250 935340548 935340551
    0xf011b0e0a032901080a02010c12090801150302091006050a0e040209060a0c0b0106050403031218020a0909030306052b030e0a03050f060606250f0c15020c04061503 72
    0x25600c08a016409260b001602042c0f658881914001d040007030b981581030482d100c2c41150b44c8404003d503d5004030031000313000c100035100060001c0c4a24001030620b00c0e017070510b408055502e540d03040c207440c44004a1030092411080500451400c906902d803c010218150340c2c2160400201810382d01c9070715040424084480640101e0384d03555012100741c0710001d4905521003a010300c016056140c0c450040300e444107544004140c05101e5410b540440c1d0701035480854240b9403019400040801921052003006500031080250720780c2d50600c4018900200000344507049420000c0442e540b07508210300c51012900a080e19003541e04000c0c030300c4065060300c1e80d00240c0c189026200301c0148420140c01854204000051040104480c0c100040382c00039103506644032010480140318445a1880a030701c0000700501e4220f1020f0095001417041041c050f01c5004ac7d118100074840c0e651081d03000744414140da0030441e50500c42019090030581c0c041c81a1401d2400c20b9003480310448001c020507 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 935343048 1250 935341798 935341817
    0x39090933060415020c010f050c07061103090904080309240403031d1002071a0601090314100516110f030a030b040b0402070308101d040b06031f0e0f011b 67
    0x607594a41103500a22030b1080c110200c1081c2c24019403103076940042140841c60076204440414011003c40d00460341d0032018042050401e60103640b4540040d041d5550f500c03040c002400e058403081da1040c000c80c01917040e10703181d1415002c1c0f1464050403940034003580c4811101d01180d450003c14050f001545410086511180d16072250840511103000500620584a440a0881c15030f40100a91801100940e01204681e04a0020488190b84070b0b40007030440b80b010000b2440618420f01001410000c3da05801e0031004954103132036065690500102d810031640d00242c1c0c20009481040341c0c031030084c26003142c0c0d00c410300342c03079010b50b0744610249601c1e074401c0702c120740d201d900005103600020000c54580c91181801030103e10100c0300c42441070b0360080c0c0400c0d4005c0300014008940400c180e451165074483d5101040c4d1500a81400e4040c8900312014070800d9104ca0351403000d25100c40700082c1c1300b10a403201440d04150b0342100007242d142c40721038211160140350060956209040c5142d00b07 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 935344298 1250 935343048 935343151
    0x90a050615060d0606230c030433120c020a022b0c08010e0d08130210411201030209040507080f160906050603390909 52
    0xb188030f22101004043d143c9000800d0084d00448000c400c00c0c5050314054860034400c40781440f5100301d0303480f10b03803035401440b0801405005000020604420340d81c0003c0700341c450000700d0300d8000c10101b081c022600b421400d0901d002c0c00e21900759200f10602c010180502281c0110794583c2e400300100d038410340c2e40742548010004100c10040c56550045c940c00c2019601c0781064000c19100084d06003600070307840700007207113481174000501660710a0041075103030702c0d60340c20025207020383d20703101052154190a03d14004010041c2040d0520303808982c0d074240080c1d20940f85059008a101201800c1c01e12510801041000f44141581c0c0c1c1a90894070548a82c14024906400c0d90b0240305903110300003618440d220301144c840d5127030340c90ac1c01c1e041e000ea44451100c000d030344141c0500b641141d420b100241c00407103401d0303554a1a0b02460205c007000030500d0b1181c50314070641e0f41070b07190711000080c11000074104003000c0766110f03400c05410340880d0501120783e84250012034519110500c0c9040c049030 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 935345548 1250 935344298 935344309
    0x2040504110a060309050607030605030d050c070f0602161a120c0f16030806010f0c0b0709050a5103020d0507080106020c09070e150409091109090a050615 68
    0x900c00001000d062100c0e0f52070340c1c01009480d07402c3c001c036114041c0302c0215107038038044c5c080c60081c0e44000f406800980c80c2c1c0301c2c0860751500101c81202082c40341090000c0c840000700c903100094141c980c007410700c501d6a041440040744075030740080008100e82501d00c4100c1e410b4000e90303030441c9034604121510f031201480140c05015050409207240000250540e20442448a140340684030307407500382060343c2d00c00055502c075092000704000300341c807030055000041850821690080d0541031501606450300c0118072009011340041c0c240100d18a5610701090704080415000040c3c002d4149500c00300f0010f071003004a00701c4c14034021200610340c07803a24030b0007a0159040c240300344c40d08100b180361040000340058000e10607107001d40034080701187d03a410066481071003541c07162030320980c0000007010f104038400004030b024000d203028400850424020b014914141d401903551946078481c0b901000340ca51000380049074141e0214a020b40003c1020501d00e070320040c80705d1071403503543e00ca1001c00d0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 935346798 1250 935345548 935345573
    0x8011203030902090a020702090c03040209220f05010c0201111801210e07060e040504121d030a08030a230a1802060309010c02010e161203031d030a0e01091202040504 73
    0x1c4d8040310480802c0306024466000d17020071402207a64050a880b01c1103007921a00c400c1d00c0c0690064085400030300c10905c0305451403445020030f800c00e001284603896050503808985422601039440d00b400e80d501560901644508855960401d85014101030f846442084a0710119050014002e9407045a250f040e81100700701d11141300c10b00c81e025a00d040c0300e4960021f4003c0c5000724a8009099103941820300c100c61041c2d6020300001c0c4034000c0c03200c041e130b0329081e030382c0201540780c00f144010240340d01d0a02c07280c10542d114804003501d07401c0052a580c2034908100500c03017105400300e041c0d003802e1910305840e904000c03601e80003d07810b43c2861840c03d54000264010f5081400001844040d42c415841503450718241d5000f082480c1000e80982c2e01c9500c2c0c60001d01c0200440ca00c2440000c840581c000f121030301c83d060015085003c90f922081c400b10908080002c0d41001c035400281c15045801031620881c24030349452018100601d28008540e00c82000e4052583c41000404020510300d81c41d = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 935348048 1250 935346798 935346803
    0xe09071b050109051203010b12090705130e010c0c0506042a060c2307060503060301091406070207090606081611010519180b01030228030804090516080112030309 71
    0x40220312a410442d018010340601101e441c415064221082d900110950341a178000c0201c00380703414101d40e0451700160001d04807000500500303500061036984c3d8034600f24541c0c01c3d4400441c80380300c015a05400c40e004c61302060305104a0a0004000500208030542d08c81e80c000022442600541d501d43c0d1103217041701d402c82c40d0100d5100c0c0440c8007a08110038080b0f0900c160040e0a15040a4650300d00c0030f07400302c0d00300816070700100040c1300d094000c0c40610307403103400680002038409564456801e40032010401000300d40042c4188a0a6503040c80000d000d4120380605201c6546410701c0105488801003450060042010482e25828071510440c0c050000031740c002d01060070100400329400b406000c0e00c00440346403002425528100ca5040003903107412001d400d100da880d607003d004070407a001d00422161004480e68500f40b850030710714070024500507000701d52070300c2c20142031000300d82d005402480f59260044074540040d510081d101d0554008901541b42d910092800390050031610000 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 935349298 1250 935348048 935348087
    0x301080c01120e1006080d020c0a051203090603160f02060601091a07020a150e04090506040f1506090603121e0f020111161109090c011b05031210090c0e0907 69
    0x1544ca15a5a0304650190741c642c40c02d40d0451140050143d99406101e4001c54100300030f10010880c9103451021440342d110150140d074030300308401c00010307440c3d4400ca034031417136001c4081080d0b6203440d80620b1201000c00e42d0f0006107000d0800c03070000303011251140f058441c030303418000008860a044006403109243d000e00201c4540381c541e2201d807200c2000009860000c0e000b000340341c000f86020b001d08034840e17801c80f02601658403103458890041860301f2080d9a0480440e800c9541656181700385070080803540f100085141c254540b41d0110100485130b403040100516508505110441e4198203480550030f041d80c94145482050340502081d1f254070720508408510341080701d484644c61000c0c244503003e010480c584500401050010641d254109580301e80d10600007540103805140081c200305181102c0c0043d40c0d915580756520264040d9110603440c024015840c0c4449515030144c04c1d2030380144606a121200101440142c4c0141c0303204a601030041412580100e94039806913490400 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 935350548 1250 935349298 935349313
    0xf071502070c170a03094b05180a0b040b030106061e05040f1203140c03130f05060f180312031f050609040b130c11060604020301080c01120e 62
    0x1021402c1018078030640b500e070031454804901c8030002180920b045541a2110019581800d010300c0644000f1011501200076481c0100c903403e0601100d03000c3c1501200c6d1020b0307141b00101c20150100b145900180c0518940c1c40c0110f100710501c00141d91003520300c01c1c0003030300c00b400c400002e018104c0b40000507015441c000c0b01003a45640b00a1022a80e00200c0b01b02c0c0701801114000c135494401e620a00f0300d080c911070f40a00c403c204290120081d00e020789008402490061203150306a0b1152600c6100d5030310000e0003c040400c2d00c40107a00405207080240e41d8245864042010740c070500e44845000c10000a110540c0210313041c000c45612006011500403900605000d403c030751017512082c10426a203038440c03903000940c10250040d6038014040906155490301480041c0c403903a140326038003030260740e104422880d1501c140000998140c1d1400741007144459103034288440544210300450040005001961000901c48031110b820318007018081c1d85504140c1c001d14030144420068005d560 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 935351798 1250 935350548 935350553
    0x90b031b0d02040314061003020d080d020a030b1018060e0a15020102071a0402030c01111509031c140c0c0f07060302090109080a0c030308090c0405011805060607080f07150207 77
    0x240603009692080002c19a9260180c20f05d56403140c084800c41984001c109040c4014101704203203c00c0c1c035200e50303105810070381c403d5072803003c0e40c000d205d903100000d035212101c507d14680400681400c0280d810305514a02c0c004008007003212540c0611801c0c04030f21100c8050507150b03480f1400091111100781014008a00740090117903120f15010f984a0903c00d00c4038001d03450741600300e800307154000c0062041e003010000548a000c2041c08d803000038060141c071000201c01124410b84164034190142d1380c1c0d003a440b482803440500d904208990180703042c403182061000c59401a402c0000003d0070350b00c842490a496180031000d00c02c0520310300640600140e001e80540191a070210240c07240518682c4446810b40e640c4441c11024052203803d8108102190090081c2c50304202c000090700d2040084401050035268280e104ca607145410380c6403280d42c3c580500c13581d5001802110180d20f000441d0b11000b0250003461050520104006460010054040c105030059031880e0404d644801950 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 935353048 1250 935351798 935351801
    0x3031c0515060c0d08070309080a020706090605040b1b010b120a021e090a05040305040f0e011815030321050a091505160518060304050d140a090b031b0d 67
    0x19074410100140407a0140079900e0002c0944140002c1c40b001000300c19982c010440300d401c405402ca40c181507882101d40080303140384008042d0131009400401500f4a800c1d001042841140e00c114100442800140200d01501040b184c01a800c1c226215800e01c46041c40c03401010020502a80500302c00714a980d103007004210760680c4c03402100e1091811407602e42e00f0500140e00e2450390707840691034000403e8081c66034005c580142c0a49081c90a050710f90807500b488041e1034000ca002205a0801040400e11000800c10308008210781480540031000103040302c030a1501000b010b101c440000c084032341e400c441075508001d03803240d410b02017805d0a202940041103811410756071000920340b6414203107001e01506004501c140b226000c42e5142d42021182c0d40c20004500c80b070500f103003d40100642c0c880d0055402540550094000140e1010380944007a400f07160010348039000b17004050344190040c1145c0121030310700ba2195503036038845030b40c03088034642c4610303d0059000126408a40550300e = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 935354298 1250 935353048 935353051
    0x80f0f010b01051206040c030b030601081f02040e0c03041b120201030e010b0a05040f0e0601060f1b0c06080711011b0f0207050f060903210703031a010c1103031c05 72
    0x802910181c500116801d104030007002e10f40030311032404644c460800e648a90090040c6250000f401081d102c006820502c003030b40b0000e540da00c00d114001c18011040d030910703613507240750004518140c90400c0f03d40c90503c005181d1300020202200040610580c8021070954201c1040c001c218240c480424540c401e00d43c8109a00103860a504415a030005100d450010207008100c0715202d864030080002606100030381d005081e8480842041c1440e040260f18060013442d00c47d08190306a60700003e1550035246450640300b011142c412001c10003c03045031056a0152420070026500c00760306480103003403108003440302c1d0300c1e10910000090301280d0310301c0c80c81b03501da8403d074103c0040c40c42240e1300c0d02c06004071030740032030340351129100c030f1030b000d8000e04440c0e00180c1505d01980c4000440c065850041c0a068080000003503a00201581803103001031543d68484030340000c0960b800002c100c9145180024400000001408482c0d5801c0061b981c9414035116000d00042c610300018019200 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 935355548 1250 935354298 935354323
    0x201051b070305070f06080f151201150e13080906091c03020705030d0201023105030714040b0402031303032a1205010b0915030c04120b1e16030b0604080f 68
    0x5c00c203400b01d4054031403800f0b00d026100c8015079400d56250102c0c000c84801803800b61681c480b6182c41d1a121100702805810306c80c0140070041000703649008e0843d14640d0000380401144240340c079010b40051b00304e90542e06440e0090b2a600d4446c2501c901048401e200b055010001588540a003c10940e000444405984098007501c00d50440b480050b8240d01514034107441e5511600c191031801c10040102d400014240071030500059a6080824100a015005410a11103241c2d85400504050152041000040d2001c61840c070b003a501c0244a88080e0000804050702c62504451801391a08140036001b03082045c3c15203031002c65401350a1400741d075000322002c0d0034000000342c0ca4081000795040140301034540303040c802e030307a503810343e03080d171004164400a403414040402d00c0c0b9015040101c03498840c0c8904041c0781000c0d00c640903c5103860a0344181c0d41c40b40403c0000130b48502030403800c050700e01c5c180811840a00c00000710240140d800a010501c1009500210201c1c0001c95200600 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 935356798 1250 935355548 935355569
    0xc080d020a0f0e240706150326120604091401020d0b1206011a1e0c01050a060f1412030c0a0b091c0e06090a060302031b03060d0201051b07030507 64
    0x705401038a61224040b10103a015110716603003400c40b41c0f08600031345006045000d1500d807801941c3c90300b08644010741290454284208284200500c0c006046440c000c40065900d000608540040e042e20036504003118214024000c900380b6280c940240840c980d1007410f0740110441041154001d41020311401e40c40c0d410b109042d411030820044000d203150394030024003450f80c20724089015a07000d240001e5680401009003640310520280038000c02c0c01c94240641d07441410b40016804e640e4081c0448518a250400801504007140e600300d040300c8240c03407810500303820240024000021b4481402050000045126016001007005045144109842400740d11100c041c10b50325502d03507c203c51041920503a0242841c000c9080700c59803c4002e1026242100d0180402c2d400c0ca05544440080b81d00031007030050b956260b119041500102000090861800000180410f10303800750103410700000040d000241e460903142e00e03a00d40700c0c0320201c580070741d900d25041d66100154482d046500 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 935358048 1250 935356798 935356817
    0x2e1e05010e0717010308030a05090a0f0b1015090501030b0105092115130809040b061b071a0d051f14010e010c0201170c0c120306040b040902150a0c080d020a 69
    0xb401183c9142c0c10303030b070f0000035180c00d65954a4041c2d005020181c0380d900c1500c07800448400003020907141005140c454050129142020701a9a48145268000e041c1e203000b07540e0520003903a4041688403c8420910f40802d10344107a000690b8984500b80d2025086042c1c0c0f481c03c03903551000c2c4400a480d556100840c0e411103036502840d81040d1040d174044051850b42c100d610046018000030f080c01c1000100005075100c8000c0c00a510381c4d000407200b00072900002403488281c401031044800601c07410082d440c64603a80141c4420b036104694640039116070300d10100e07a01d015001d1400e03142e41c01004c00d08040984031484c549100e5000383d02580041c80c00009903981c2e5105824500d402903040e10b942d0703584e8540c41580311000030000d00c0b80c90504414040400c6900007002013600d0345104803011940e9081520500080c3c80c10000b00c10702583c2880744000050300d4a0f500c0c140940300550540ba29802180c404440402c00c040c07010708650000300d245800c40c2ca546c0d008042070b180944406092 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 935359298 1250 935358048 935358077
    0x90b0f21070f080603030d0c0809060123240c070801050a0b09010909060e0d0504031e0302121c090b070201150b0406030f0209212e1e05010e07 63
    0x40d00c01264a040000e140c0002508440d000e1041150009001400d407820541c84940b910102c0d28011200400a101d41c01030040250003808400d014000104543c0c4825042c800300317010040351019810300401c404240000f4810110034a55103122402d2201c17030307646005894080e07a403c65400380ba0a00d519040100f038100200788500d050200c2d001d40200e04581c40d20000400510b83c08405403441d80e200e24401910714400d0101d4080704c540d0b626942e07102d60540c203115070403411803a14007017150701400040c40401d400140b2103041451a900c0b00d45d5840a8105440045860089881c402030070241900c040020040c00b45101d006158001c204590404485c9802d0f000c0520540500e544100014801c551280c1c0041002c40384000703025141c4000303900482c12412600221200c94a000c040b85d112044040c0513076103002140c03000804c0c999141c1e14200e02a4288515000c1d0415a50768011180ea54043c00d078485071511b0820401c0b2540e134411401030302810803106000020724080d24203e130b = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 935360548 1250 935359298 935359357
    0x18120309011214070e0102100510170106140d051203010b0318010515100203070b100302011103070b060906120109120212120c0d150602010c140c061303090b0f 70
    0x800b600c042d00f81070400d4440c02c0083da0101c2240d02803a045000d0415456071040d44c900130980103000e1030f403000d1079451508034540d0030143c0c04084100d0340c1e410450304200c40c0c010210214101c05c0c0c1120b01c1c0d103816542e46401c628280e80c903084008011001710000a4842c102c8000d14814030398010055201080038100718221041240c20400080c01c10000c1d51140c10490840e4204031410b0040780d180c071086441e044558001143c502c5103c1c00307002024421560b0024400650408060003107060034201da417200724100000340480e0103503070a0300004032103a40c4c007120062900300c17079002004907011b42d0600c1100844002c6070500941700d0300203010503849041086032210306e2205200e109907200c4514011082d8010b981e40c00c1d009072600d84a00800c3c4d00340036154020071054000040c2030f40c0d401d80c040e0002600561104005405020201c2d140d9000324009900201b6040c20300c5011440b40344c01c0e0346911440d004840740314404a407000d0b15006400c000d00384040313519080100144040142c95 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 935361798 1250 935360548 935360561
    0x11010305010501210e031b0a1406010302150304030309080a11061501091a0706020415080f10050123270d0512070618030507140f070b181203090112 65
    0xd000c400304a01c4403500c9011944010001c2c461740082d249041c2030b0140c4083c161410320301d95400e6411a602a4003046940070030718403001c2c850000b51040d98035503000124074030501000e14214450000019003058825030292801d643d02200361502d5243c8440d000306103500d500d01c4108103208007004106501a40c01c214a541001650740c1043c4d141842d41400c40b0700200040680c001d00c4c184a410000380080c00075001404101054400104840000410f00d07031024080050320080a400c0c40b9049850324a000c003600e00a013800c100b48200c655400701c400359214520346030401d020500701000850041c030b55a00c100310501030b0425958980800002100e4040010100d9010034207850300e49100101405180c1d00851000030711000301900c20403482c04d501011000500001511004c0040341c0559200003a0b00c1402050001f21004640342d40740000c0c001c031819054041804511070000110350187e0382c00103020150204000946940c1e650803100c1c0740f0340810103003000c2d4140c0007858415030703 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 935363048 1250 935361798 935361827
    0xf04021c0b0a0902120321070318020108070e0a0e07200714060c010c020c0111011a150c070f0302040b01050313020609120f0f10060e22020d11010305010501 69
    0x2040303251190821900180060102240c0140000100384171019080c80600307a124481d000d0600e06010100b916405100c00504403414103141032145125880040544210b01c2d41c20700300182243c032600000d41c0d60080b0903001c564010b084180104032045003940b25802625142c844c070f99290b048660f010048001e14403400c14990205204000c0031152030715100041c500588068a02540445110301351450380d141400903a1102a089066503840301c01000c010300c0d824000c0101d103054484130550f0307181c550300c2544166145803c9840b0b42034600c085802c192851011a028650b40b040c035210405614442607206520b040c00d080030a5015901301d0740304804100003494000352903420010b0300d070043c2607295040500e180c080440c51400700310780c6000c2c0600740300400c0c01c5030815160b01d240c4464001811062030502408100e5100f403003001507040200c0c4144481c040d54026045507041c60b80540182d0b121101c0720342170090040503a0000030300c4800381d030188400d0b0303251401500c4119058801 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 935364298 1250 935363048 935363063
    0xe040f0c1e23040b07031106010608090a060c020f1618020c03030a0e120c0f061605040e0603010b06030f0103140105060603010e0406061502070e15090403180e0f04021c 74
    0x407500d0009070108803200c41100c030102c2818191541c000c0005074001c52801c901045222921100f418002c200440c01810b0300c6c906008940f0785016520b44034a01542c0042082d1384546c0941102030082c8220515008420104c0d80400041040402c03c4020741c44cc02820040608039003c1c1e0381d40d54021100e01c50385600046256841d02d02501c0028458605460058003c0ca825880c0910000c80202001c0f401000103207883d2003010030b8242000300262090300c05941b203420350401d5a030484192405c507400041408480e0f40d90300e010a014140380c1d502194000e00000070000c8002c1480801416030340564443c221141a0704001c0e404c035802a2aa140c0c0144248010082c0d0032031040f00d40c0e4410700c14007012900c40d0352a440055105080e4881502603000b9007000c0c408182e2440345a42e01c03001014065052100c0d80001c60315110010300054204808984110301700c8000c3c107075840c001c28854aa023821458000e0058255400991b0100d101c6c0b00c0081800d21141051502000c3c441d410150 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 935365548 1250 935364298 935364317
    0x7050d03180902120708090a050c0f031507031d010c1d22061a03011410051e0d0e010203061513030204050906040b060a081005070e040f0c1e 62
    0x9040d80d44820a03890041c0100d1407540100d010b50490002e40710082910221169900f03101a014140d900d00810024060b4840211000414000510251200403d64020582c01032038404a8208001b141008000862080521041d281d0541c071010b501e0004031800c507600c00b5118141420b844100300c0840002c1c0c4403030b4130540d016920001c100303102040108044001328070201b40c01e49aa401c890007034a055a107400400c00c2203901340e9010003004117519185d1456051100e01c041c01d001a540f0b0a002e1401040210041d44c0600c1c00c032000d102d02d01e42c3c107036480b00f00d540001c14a640404013441d41142001d062217414030050007500c1c0580401421040006403840007400e607a08200d141c400c10900313a84001001d03841d984202805414030340090609807500e41405019000042e16450040710780140800900c6004507900c16101c2c81e4072808110703038952940032a8101c0303001048071340c003d1070503000d00c40c91085584000410040c548a90b030310860144c0500080040c41191030022643d03800 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 935366798 1250 935365548 935365553
    0xe061e030c09130c080112020d14151305071a16030302310b03040b0403080705130b030a050a02030705070f0203070801181104090317060a080f10050907050d 69
    0x100555440034022100728101a40c1d400081d04410281c600743c1036032582d807100d080880358030004983c00740c075100e1080e05207107480d940498442c42d0b020f64068000c400f000c080c908821014441161040c0c1480c00d070401d44c0c1031400140030b4182510342d080729248520700c1c0003c0c840782001019414150305600e00c500307210128155030740003010214210205507080080301c0340b502202e42440c5501e4000c0180103080d10f404d0300311010308803054221803d0f0740800d1007040300246070b00142c90b60240c1e00d4a400240750720340d0b00080c1c07040d0003a048000752a52940c940810f2099886000d10701c1a244040c050145480b060b0032a0101c1c44203469070400190100038034800729201102640600d480501145c00255841d03251038210b6800700b81e04071200c890300182c442400042c504210b41480c1c11202084444c8459078040c0080140511000341c580410700003410036034518544400a00c000015242c00d08081140e0a0301e8204400c02c0d20b01c85807130700000c6118400002820000d540d03018204181d5061070383c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 935368048 1250 935366798 935366857
    0x1a0105070204150f06030606031d0601060c0f05030304080a080709080c011b0501060902030601120e071701140901020d060905010f0e09120a0207050f010c15020a020307210e06 77
    0x1840d042a81c502e0f8860015840405407501c100030034640d90001020707401c0410040507140c41c000700484460003601e03080300b074034000700e00e860440d9101c0c1025114821140fa0104a00355424000340807400084108070a010b08400108a1410b0990f600c00195503402c10a45240f190760161a0281d404200c4452455016802245904aa84040002040081c0d40700c50a4400c0d5070001900f250300442480410b50f0881168908280029014000d98200c0c0c1403103a9241039a00c920048041c032185c050240c50800e510000c000022064008400c1c90004800384c00303503000c0703100c52010354940640060f04104502c82c640c140d40c11021816805890031400c6503c2542c0585081c640f40602450389000142104c0182481c5100d41c0141551511303002c1044680d15524050030b05101160000e04001000c4228008651411803c01601c9101101049285005141d8000d001511400c4040c0a0050076805620034080c0c1e5032301c440346110344105010440c09103851402d0508050314030121418003a = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 935369298 1250 935368048 935368061
    0x1050108060d02041b080601050a2a06090b060f0d0507090e24010501180b1e040b0409141803032e03081209010501080a0201050c07030b191a0105070204 67
    0x1811201e807a40c2c550002412100c00c0443c26005c41d160703041c60090720390000e022950000e802d0801e10b042080d0074501030100b00903800c1e00211402c480810100880710908550709081c0c010300d081211101c10710b040207003418241d929a101e80d020349140c410703a20701401aa0307802548100605400341c60000e101020f095040703600c000500803071001d1040c05014030b44601068002d44201c0d9201c1d45820005410581074402a14624441078000e01c100a56102150012121344069102d14249050f502e510b034081c0e60021220300750000f4000800308403a800c001c048545011444500307071580485134001a140741081c90f41a0001d0000901480d8000b0050120824090450f4400a03913082400c0d680031780740c4c000710381c6074801080200120f2210007100b5030043c60f10000308155414031800030b03070b1030b0400c0c0c0c0001e040000c0000c803d40510028000e0b89c000710b5029032417540da07042c004040c034a0401540400c6411314604400d48213140c820740b10907102000183c6441e4070b0414585c091001400c078 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 935370548 1250 935369298 935369311
    0x120311190819050c04090b04020301260f03030106110106150813110904210c111905060d1d0a0b180309090411010215040209072003040b040f0905040b01050108 70
    0x1040040c1d00305020b85010f0b080c4100318019071240c2d514140b424100c101c410441c1000d0080d4414001404512904100c10980c840d45491001d107000741c84480a04d0030001c07040d100014007010000041c4681c000b010001c8190511009200f15500d034081d4260002203800d85000250009002c04c0412000884921129018800303c8250300f0780840454031040c02030328121841010001c500c1000002c1c08400c16081845e0f251030074040707000b0b8440d00380c0f5201c2405102c0c0f03c1c138131a40c94440342c2800104c1da940285405407085840d045682006002171184500700706c4a00c0c3c0041d8248801c8801013000100503900440503030b160303203502a01450180c0c080c00d2944032880200200d0382c180c0c0e50b950145118600c600d1038581803a09850009083c070340400410305110220781c00740300041c0c0d5a180216070000051030000103020304492200303105441004403a00d41e0000140206888406c100104107030f400007035210002d15610703120601100c0049402420740c148501c0144a60b61044d10810741065 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 935371798 1250 935370548 935370571
    0xf0a09062d060c1e05100608060402010c060f1503050d02010e120d1e090c031106040b0304080d141f06050301050d0f060f15080d032c0a0f1203111908 66
    0x100454240f12500905000d55060b1b210701c0303144109004c1400b90002500a001c00f130613a5013421b40c0040c3c95501e1086c802003189460f400b294546c062103a010940075a041c141101c81d0540e281011744d1142d032020341440043d42484c072001d5032900700052020002d907221a40e645816100c000d84c50040040381c0881880c10035440c4141216200c42c000c40010724014100d0100c21441d6140106280d041b00d0240c6005803401d00080101189110aa940c440c0d001451246c0d00c1c01c4a00d05000180410300d480c003829070f080018002c0f4000004145500c1104065000ca02940c0300d0304190380e940802d110b1643c1c400341d04081000001c1a000c600c032042c03440b0b990041254085101510240c4103250307140e2010380314010b420052980c0420481000c444c140c201000070582c2c00c0b4090b5180c50100032507100b401d9044011301e91030038040100441103a0094201c410319292480c081d1268604450070f540040c0c1417041210f03c04041e03000f101c4c1c40700501e41c074644d4200121541034680ca030006001c1510304 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 935373048 1250 935371798 935371823
    0x60c0303090c0902180307080703080f2505010c0305041e060605090a0e073305071e110a0e180a0c0308030f0c0304020d030503060f0a09062d060c 64
    0x990b900040300302a140b10000540c48480b4074070300c104c03a401382900d079a210380c0c44400c0811200340081054000d4030b4000810a56034251841d0b00801072080e2414120f40d00d0f00d042c450744607940b54900010400c0d01c508000c0c01110b44c00c0404070700740c031401c3da40502612050014401c039401040c0030248540d1041710080b940c143d0f00c60000d0150315085a01203802c130340700c03040724040080a10000e0b010f000280d041c0307040a40582d50030814170496440402e81445540c101070003c0b40550250360741940e015020a0145817400c007603912240c405542280d480044c610000c040389424011038064480101c40081c45d0380da2500ca0404215501c000f001d09030241101180200d15000d01c802d000e503001c0d9440540d01d04080079044000030000700b4040c0c03255814401d10005954007038107507901d241c2520380f1545907201e1000040c000c141d420fa1441d402240c5440009242510360030000032a42030768100307040c0c0c0415021004000750315480340100180e580701e09100301e9000300500002c150188141107010b = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 935374298 1250 935373048 935373053
    0xe0f030a030509033f041a070606150c0303020d1d0a0b091c0806040f05190605010e330703050405100903050607080414010606050d050c1201060c030309 67
    0x502045080c00d900240c000102a001070500f00318201551800d0344c0707418800300214000c1c20350540c540980300130f9105140000408074049200342e40180c8000c03610410209500e1100148603404000211400e40c00d0200002d00011110302604000b106612500b883d486a03640440c0254008041e0100381a602e1a5522491901c0c0303004041201950004000f0340301c0700d04104217809002007190781035501000d4040922200c61940074624038032800c0c0961552602c0c400034014050111190301c541e07251501300524081d60001000e02c0b60f20001007008421780785c0c0d004482043c003251025400ca400900000c607410301e907510307680c510030074081c42a09078003d081c01c1d40001e074040700d42600011400722b0203000d07514058007608606c051905020785064515690540c80b01ca000b0b0240040c064003000140074086407054508000c02110020446140c544a0250040e04403407503070610140390100096514a000c011550903581640b404042d41c0c1c030300b200480780c18803102011004c068031007102800 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 935375548 1250 935374298 935374303
    0x605090709060801020912070b1b010b04020a0c0201030c0906050708250b01030501060b0310091d033906190e01020d05010e0714030c07030504030c091e1b0e0f03 71
    0xf42264100150b9141164420000760003040303016514a90047c0400300320002443c804c484c3e0702c8485405400000701c561078020700501140401c0c40d04a80005003685000d940b00180b034540c00e01c04d807010001041406000c59a0003064090840030410800108c00400e1030070303003d001c108111180b185080c00c10202003c220b00f14900d41201c07449200401441040130a0080c2d00241808101c11820b600d080c40382551402c0d56480342d49603c595036100610002040768040e240a01c0c0308007241d030f440841e01040501a250760b4211103c12626240c5920005403814103034103140d40e41d00003000d031503c0e450002010440c8100325805100c0da640d05003040388100380084c0528042400c0006a03640c0340100c41510154014006410404800c904600044141d400d4940200c41c800c10303a603d4488038582681c03a44903641028081700041c43d0000f8503904640c108400d119820012104010500c0d254002620b000715000101d50012150031840c80c1c2c443c42d1101d50800005042803216402040400e0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 935376798 1250 935375548 935375561
    0x7390c030b01081902061204260301080f2a0310060b0417031204320601080c1002071a0f0a030504020f030d0e060304020103060b0408060405011d0a0605090709 70
    0x998090500c0700400001c0418003d0aa150703d040d200c040403019181e00140301031003607800840ca0040d410340030506001c4040090411041c0444599012000000f4030b02e81941092050004034441d030803042043c50004191a003201020944021082c140c111350400a104124541905031080001c94020314116014107401449074103a065503071810812440540d0b00c0d0318500480c664020410012031035040d100f410390040e04040301604002d0301081c002c241c04420202110940341c48035240c2600e0101058590403030b8007000c2202e619801c904144000340603200c0349440940c11000c803c120401001c802030040305440c0403102d107800f0038540c0c044040e0b001084050000b80c1e44504102c110704000f200d90a181500f10000e0103110100c1e4001421842c2c620b4013035018800c0440800c0459020760000c001600c01d00310344a4441d070322094041d40d01c2c41c08440680309903090a001940741400c00b0008511030301042c001c0c1401c4030040e01d59001038140945078014038415036030005100340c09441f444 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 935378048 1250 935376798 935376803
    0x1521140a0204090f060501080a1d1209040e0a0b0c0a0903060c020307030e09100603020705010e03030103053a1b05100207020405010b09030703030807033207390c03 72
    0x1a15582410f1101c8101e40700c1d0110240014980340f424000c2d03a8000c603140c1d500491115020402803c41211007451003a444204072051140520340c03d481030050000c2e040c04407081d1010445496185040c0d42e80301a0010080c2ca2501203d0120305603164010040c0f80403035140c10720040703a5503603544000c116140e400c1000016080402c00d5003c05a20404070700356140121801d180509180003000a803050324420b4038145503002850303008002003034210020300400c0809494584d81d46e41001900e039a541c00d04100c0840700c0715003416912a5001c80140d0071044040ca00b041c518000e141654148421051181229003014841001440c200305440c1320021862002d80c40300035030b105100907150107801c44001041c084c080340c0916100011200100c82d01407414420795100c45406500504100900c000380031080d00200380e4006946905841013070030042d40d0402c6980e0914100c96041202c0031840860b04298240c003d95403055003004900f949403d1031042c0040180c0e5941c52005007075004 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 935379298 1250 935378048 935378051
    0x70e0c1b0a032106060927051608130308180a020a1509060509130903110307030806010f0201090b4c081506040207060b0306150a1521140a 61
    0x55242400c0b0880d440b0f403103482c0f00002d00038141820380c050b0440e2034034042d50a401c440d55825880d9482c241040d0300743c00d440798a08201c40e0801c20303801d903030300b0522003290004944014080341042160058140c0c40c5070701651084856200e01c640e0003c0f000035201a94018803c020041c805a5103090504000304156011032042c032840361805010308a00b644000c040c403030180b20313481d20b03501c503d81101180c0d900380400064a0380e1300d1601b51048004c91840c10500c0c070002c10414201070b000b101440c05200240c0710315004181c50f500407801d994920500070b0a2030f042d0300200700d0803051b0038850100c405907680e402a650110111400e95065141080040d6004c20410403030032410164400026106510261469000d800354134840c0ca0005010a409130380d000855000f07112581c0d000e0086c07800001c0c196070a60030010040a001b00180c2425481003041500000c4d100c9070b020700b502c001c10b400742c80345c00c10640621400c240500150400d594441d03140c04034105030302c806590461058405280 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 935380548 1250 935379298 935379317
    0x30c21010501021b1302032e0608220213020912060103021908071406090d0b0a0b060a090e0a060f0303050403120e0d11041b051b070e0c1b0a03 63
    0x213282101c241e40d0300700c0d0184040901211526103001030b901402c01c0e02c40150f540e8451021a8004128018050000200c0441c0609181801740415400ca554503510000746403074401c11088100d544c01c12441488000c2150b440041c11300c1e103c402c0009441074001410000c800002c541c1e500ca143e41d400850707410140c01031045103041c03e41c14600e001c03440854a2024208403a4030f9803110140100c031340700e84010540803c1035903018110381c600d01015100798001d00c003604d0248a2040140d40c140b020900384010360190b801c0c00001d4400b102140e07681d003484140b40841a817103045020f441c90503d5501c0702c0d408200d800d420f0312090003d611035560107607117902c0d40c24241c004d0145440310740304006049078014410f0f41c50507131f00441039421480c40c24001d001d0100041c000e010211171031070140c880300501d40e502500300b0041c1901700d08000001d1500080010200d8035501c2e01e00a00030803404460210300c91074868406880b181c0c09026039091507035117900c641403801606503011400103607002d0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 935381798 1250 935380548 935380559
    0xa080613050127090507061b06110a1d090a090206040503060f0609090a11010503060409050706020d091403060a0b151602040e0105040f060f02040f1404060e1b030c2101 74
    0x902141541581e02082010502c269030785c98440120f032203240100100015040040c412070500c17100c459a001030b00300100b61061508001a401609040c000f16540071903488695540c03070f45c00c880c070303120040104080d96140c0314880d004000c2d100e011380c4c0016090101003400d44040203030b1405050f45010b01c036000c0c0b4018041141026000741500100c1c1c101c0005400090102d803034040d0828002d00b8495100c0c0e848802040040a9401003d4198856050002012038000c54403d14103034850382e0b44215035454243e0700d070f00450304914540d016807080c4c00150449210b036001c0501c5130001084001c1c002c801700400a0160000d1403026010342401c00d900c000c514007072007402c05080c60540244840d20f800d84841340c1d1002c4948018041079201c04000303040030107642c11a4003030140b0151820405444038142480909440da94a00407407400e000030810b00d802900740f45c4130702c20350108007100c03952031300c50750001b0382001d07040f446108828403003c50544a05001010150220f4041d40419854032 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 935383048 1250 935381798 935381849
    0x60908071211031602040902101107090218190302031c0306090c020d0e120d05030609150a03200603151807050d05180303160306080102030106050a0806130501 70
    0x1181c0280510034404580c1144410100c1500d010a40c600001d0100f20b210b0700129003c0d04900704000e50002070291403441e91074006091800c0c0c5038440d81101e1915440e00904003ca104a200f2000c814034903004c4c10b6410701d00b000030318a060718084085008039031ba03035011a05d800c905200d030000702c4141456090103503a0500c941402440d82c0300e02400302c0c200c0d103400030303403600c008421b1a41000610580349020742c4501d60340611032440c0c0002c03111002c082c104000c01e0394000392140380c81101c1c5240072440d400090100980034050003002880c0440c0746654010b681c688110103422008401c1982d50010380e2400c001d0743c45840f50441c0318071075164004c10400d5100480341c503114003da030801400134542d8071409980300000a020000b41ea61107400c4107008140c0051340c00e11a070300c0004100a4044420088006944020b4030144915a2690801800d034042401100c2c0050000d011030b40c1c816114551094110801902d0f509000020300c0708681a56000d8008011030f4103440080103004c00c08 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 935384298 1250 935383048 935383073
    0xf030702120406090302101404080102120f0103020a0621060e01240e060904090501090f05070f0602120f120a0209030c010212180a170d09120201080c0a020a06090807 73
    0x1c0181d85290905024015203075105601020b40a6001d00d50020641801007010644c0d0a41000d02d86e0b0b22641d46000042c080c1d841520740b114003841040104c2d544100304445030341641d5008180301c040b5400c100c01100c481c04511801d00145003800720740d082840309480380d00081e110342d88403158191704080c00340c2c0c0408024480d04202c109640c0d041d0428583c405d1500003c1c0c217084610350b60311115500050058150711a0180003940390600340c4081043c1c5c1c1c52401c1c0c00e141705d2016140d0040e9910702000045003644103860150b00505680d60500310b5003001052081400c000032802c0c1080a49585001032080324085100d80c2d0000c3c01542a103001c102100ca000003d00c001c00c030401c54484401e0b43d03402180900070000103d540c0c050001d949095510014017001000d000f40b40c00050502a6504036001c0740e00e0206000bc400400d044844032444000a46c040e100c0c0c00058550300300c021002e41c031030b000304001c5006820402000608030700948c00620700030b5100340e8507038080b4145200278200 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 935385548 1250 935384298 935384323
    0x403020616020d12050907090e0303040201140304080304080d06092315061e120708100f080303071805030d0306150201230c1201082a060706200f030702 67
    0x45512201403980e840303c4c601c030440c00e816101280316140c3d8502d4903e4141c060700b050b04101c0c00c191046c3d140d9000080554480d9001340c0c0d0380000c1b903690a00d04c5400b0320040e01c6c0079080d02c0d020400140858542d10040034606c80c28070002440a6032940700750126520604154040c80c0e44c19480145c0300c070504900d40e0802d0030030411441c0603061000041c5580704109000009030b1155810540302c50501d000d4480f50074440508120340d24000c0b40081c60304504540360744007040000c5001c12501a0a280e007015100f100340118a10380302c2107400d40d01c50b04485500c000d0611401c00109650710700f8400903000701042e0b10041015814600404820b020342c11220046a1521000050030180c2c2069101940e004441340e01c9540c440b4050300700180b05d058001000390341d1010000508890015a5151b00007040d5244411180c0300d440307814820340c40d60010756200d6014008030000c5903883c0d10100506002442000d5032261120350038603290072886400b4104079000c4200018681c0610858281c4003 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 935386798 1250 935385548 935385553
    0xf030604110a0c1401020c0106060c1e0210050c070803040618090c09120c15050a0f083309070302130803090a0b0d0b0a0e070912020f0607030512040302061602 70
    0x82c000d000041805620b010003600c0d1034500c1c9182c03c01e000c000c2d8111880540036000901c510b54030340c08050286101c09104440c80c1f6410317503808020b46801d8103030420043d4000c00c01106294080f50071141d94200c552004054002d0040c0002c90003002c0005200600c02074460184422400000c00c40715141503004020642c2041401000aa03211023a40141ca0580ca0b40200e02c020302d050031400c402d030903042460083c4072030232507064498220000d000304a10781e682d049040d002580049034140d605032480750b0420480007031400101d0040c01613210111190f1006642040d20344001503152101b0b4440001096000801400300035030034090f1000f0384a084c00561030014200082512425940319a80d10711502203400184241144c020b802544130040215104a490300152011060144c80c00d00100748007080029800c04032602600d04580c009000411610640c414040342e41c7c08a00c04804200b03040003803400003955401030a0165010f60f000709400d01d00046602041d4455000e41804e55 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 935388048 1250 935386798 935386807
    0xe15041b120f23190501060c0b0c1602040231080705010c051b010c210e1e04050907031a0702120c0319050408070308030603010f0b060d150b0f03060411 67
    0x80f0b011440000b442c12540704103100d5580d500100d200324005840d45540c2d55410400005085a400444040054000d580c0105161034030800c2c005907210706c11081c1110361480345400090710305030703000c0c01312010040910115821208090074a1502070100c9101d40140c0c50001d00ca004010004140076140a003005107090340c0c680c03901c3e550390b842001e18000744c002c5090700402691250009584440d40224540081c0c8124101040403405c10b00070580010404100c1441528106401003429000c000451150715000e400b0312018004c000c0508100b0b00c140403002002647c1007075156800f000c4114061002e0800210080c01c1c0103090308555042d2800303011001c0d000b07070302104540d0450150340d808001d11142c0e841c01d4855000e1a44215658000e145000081c06000d030021880b810f000c50007005804544402c280448481c100d815401000901050050200b41e9000c02c0c40d82e03020100c001c0f00301d5a105601851940007803a400e24204001c0300348881410503000d6414400d0400300b05a051 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 935389298 1250 935388048 935388071
    0x1308070f0504151703190215090606010e09040515010b040906060309020a05100c05030307020d17090307031404091d010b0406051c020d081602190e15041b120f 70
    0x40c2e100e00130001c161202221201074030008100f11411800d03030000400c00540001c01c080d40b2031140c3c0912450040c205000030b01800310200d01140700f9007050711030b40070004070a418041e04902c0200200c1d002e11880500011490003d44030038020b0018503180359440b402c1c075000509448055020806150a00c8400801681d0b0a001350058603000d5035000d108480c4440101c4d142103032604003909501000007400b904a80c0810b4144800741a525008291004400034154840c0d04590030910340d00240100700010340700712403043e0b4070043e1040c850304290b00d0701c00d01030450309006100200c0d00307601c184464008400780160800b804040320208078051500000c200e43d000b05020300746204808c48140700440d56220300c00c21020b9040b1403035035101e009400c0c400403444003002d401d0f8800c400e540e56001480c007500d841c0f174080c2d0302801c980030b9071030300c4035a030380b010142c0031030243c0364010f0701c46505001051140c000c0400d01600765403014022080b4039201006c41d034121004010b0a4240a001c444 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 935390548 1250 935389298 935389331
    0x2a10090b04140f04110301090612080f090315070224130204050c160f0b250c110402190801060e2b0c060203030f0c04030308040b0402061308070f0504 66
    0x860700c0300d001c1d00054002d07090009444141803164907074414946031542c41d2000003400554141d81203200304101854580d40015052101410b004112460810114000100e030b04040c0c00281c4010302191200000d00b08180c0c4045421034004006074400e121044210100c805d8a00c0b51449c024540e140038140346c107020402d10307962440a40510348403004911810007581c100c0d944908007003061080f00b0000d181100d45180b48003420b64001c922140421300510080c00480c42000c2c80c001241c05111712220141c44000b02000305688200340000f07a50031617200e40c0002c1c804c09217100480503030003034000c00c0070b0070780300301a04018100842c08481d06000d407a1103c2c2002ca505d400c7d08807180c907028510003020001c0003004000e111000c0310000055158000003c0c0d0f0013103070f0600034000b0a5a40443e8041c5600551201500107203400c1d02041c00b143c0d01203142c0750803a00140c9014506107900002a180c10465030010120354030403001000308900c40c20340d07000075010485d018010700304444060700707 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 935391798 1250 935390548 935390557
    0x30d0c022215080c1f1b050f0d0914030606090a0e03070803070e03010c0f02070303030522080a260a0506010c0b0709170706051c090203101a0a030b1303022a10090b 72
    0xd00b00c864031b8522100b840010003c0310001e085c000225030400700c10b034100602c0101644101204a683c00990321454600811800d20370803025022540c10344ea4016244050300710303a00c1005841c0030410004000c07550b034800440c07150f60385407605030310008440c05042c00c4816190b200e00800c00088409880d0390b6000c13a0740310440f9014600030a030307511800d01001e000d03030788061400e050b2102810410100821720b0094070040c1844c1d2100541d003200ca1480c12140807024010454008440700040d26003203550340000e4004e0344c1071500509100c40c0b9503800d00806801c1d58440007049c00d82c1800c01000e00c2e01c407103e1481c0aa2400a003083c18034000001d07100f40100522400d06144504611805035520ba100d00001c42d0014211400d010700d46081a0040003615019220844640c0c05c42e80c042c10004207640450b03030f00c41c5540c140c7d566004298100b45c01800003c40440c0110300418440d130500711404504107019480a0020740001d100308190501c1180c080c07014840c10001c1008860081f500b500d = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 935393048 1250 935391798 935391827
    0x411120c0319021203121605031006120b1908010f02070503190c080f040f32041d010c0809191b0e1302030d0c022215080c1f 55
    0x19580c60b0082d00c0001e0071100c00c1c11a110301c920021a480030851a44800e150007002ca0040d07a450061042c1e00444241c0300483e85021010107614041241030f2140906c181048246440050303040001030019441c2e080945005c1103012a0704028420300d4028842d02c024440c100c00c045250113415036449449005803a40b1807114200c00204520050103414524421544041c2c078690315248010503100303c4c4c00500401c281c440090002250a49500d02400360a0a0400246101d40300688181729080400ca8141d43c00a40354203441d0340d045014466024008500350000c2140d6000f200e00400c5000d004001d900d803a88500e447c1e40e00613400e6a05000d000341c0120307ca09907044084601c0007042d8160307106110105042c003c003c0039100103080601d20920032402d0324044800c0c00c50858500c484e0610203540079408400c0000308103805c05a801c000448070a000c01d060700300001c042d403802055804541980c22509403200b003454003a900b1a0050880110500f4422412070018000316000010 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 935394298 1250 935393048 935393083
    0xc080a0c020c030d02060f130b150a0f08060f10030804060f0507152a0906030f0f11120a090305040506070606080609070e1005010804021e090411120c03 67
    0x41041041c42880a84040440a0304031001c1c024810300c020b42c1c5240c04c6a80154002d01c80010030801c2401c0d4045448050f0000e0b80000c5a40b180135400070071600070307801181d0010300c01000065a00d81940480700402c4944058141c82c0f500640765401d03d05c0090290070b10808151050000414030000d94095800500e054070a501003080300b03039058403409070040e03c1c1d2144903400380003001458124240c4220815040b0803400c05944001c030100d0101400480482c08207082806136a20030b0740320100c040016240400d0035540c95081c10112028180001040300c070004101c0d48007081310300f017140c002c1c9000004005c54030160300c00a045029070b000e23040c41150000350140c02d21255821100182800d9402d680b042e0800030001c0d503840c1d20320321503168076003c0c240014000e0042360f44008201c440c182c441c0340d12681c59500300a40043e404820001501d0b020700900e00c2e5494800d0068400c070320440301c4080c80c5000c0f008012814200a51403809544180c0d80100c1c5502c01190342500c00382c001c0d01 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 935395548 1250 935394298 935394311
    0x509100e040302122a0d091202012c03070605090a0e19110315030109020f06030c0d0c03020334030b0310020708030f010f0b1e09041802130c080a 64
    0x80481c1401c220b5004035040000100c1c034101c1c10502c105c00009014041c0e00c42030000035810000507181c24101c803201c030108011800411105d240907a803503000030310524103240f01c0d440325212511003c0001c80c0444001030b0038090007000341000c00905015000303909006040c851500c0c00126210940e0088080f83c07811580171030b040c0d4400040d40032401814000070700c2100701984020701e56410468034000300100781c0200c20290305061244c914811780150001404904110a0156540c40038000305a071500400084c02100708030302c10f500594030345070740c00741c0e03a8101400e400c840e031001c0f10003034284103200c1031004089482050b030501039a0b03103604000c1103240d81780f8006030a1070061030089414a00000c0c000c01084681c10045202d85030785055981c0503601c920141c0c40c1d0605030f0103541d4040204010700207000112070440340d4029280041c09241c00481e80200d02604d401c0314404440d2841c0550600071460803091a42c80b41c45081c40821020407074400c001d10340030002e000c820090782d9408 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 935396798 1250 935395548 935395553
    0x50c030906041b0b0c0c010206010b0f0403060203060f0319330e01060f06020c1f020a17070c0803030406060e060109140d1b030605060102031215041e090c0509100e04 73
    0x805000f4404042c1c026140c55080c00050386600754030048600500270340f000483d0201035482510f400c0168081e60034201070640e940c08000358005030440d5480b4415402d10105580d0402201545001d00d036072124500555141911218a8041a14942880b40340d0301ca55900c0c1ca02d04035482d058401000450241d803d690400c1c01030125070499800254801d00200d00e458001402c0c00c0800410369101c41010401801006010b403000112001600a41000c0c0f02141c181320203821140a03048a882c40d0416030f070381d01074a6403030561100104d500040100424402d40384144c400030208048a1032183c584500024a140b0480c01000175407214250b5061503500e401400c0a00540d01403986031922111400000b181c031010320045442038141400540a9403003c0203a407806054280070a8564845145500c100c5030113521064006075640b10104004c2d104120b952407482c4203020008812009080020125110342c000302e00555200382807251b0300b901400b45104803500c030b20400310355480d6403 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 935398048 1250 935396798 935396843
    0x3050906070518210c120d050702010f0e090126071a0c10060e0603101a091306091211070803031b0d02030705270f040b030109060e010f050c03090604 66
    0x801241c003e414100c0700c0d003e00c070000040e0406180c00100c0300306c021b6800d0000950b5496440c0c04d51140080e8060002c0e50041d4003078058030100300b55604000010b64080c50104410300e8090b80301a401c072196803002601d0402c0c504410440b5503404000c2e001e61403c03c4000705040705c0000c1d624089110005280c000100180220003130095500741c14001c05544840fa0b8071040702c1030781c55600c07a01403ca203c1118140700e11500740384c0458a07400d42c4402c5219070820100d203000410222490f0810f2501d040001c406200700100d081c440c0240510a804100004149005850361008a40d1000c4018041c0603000000e4a0f4020085070145c14001e00c0fa0920317006070b000740d0441c1c81406002009000c10a50010007901094605040c003020740b41040345009440c43c0b0620656403c00e51011300f01c0300c6420305802034041c051001e40041160421036940030101d07201c1c000042000d9540b090004419103042c0a4281c001c0c0d82c40c521a030440c204100050b8890f00090801080d00c08802910805c84494 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 935399298 1250 935398048 935398069
    0xe090c010f0c0b042009010f05040209042d1b021009030306050d031e03020a0e0d0309080304060507021002010b011704020f060a020a030305010e01081f020d150603050906070518 78
    0x800e503030719070f1801d042c0307001d540700c00440030400b11401d9403003440709140c02c118803054100d81c601c1040d090041c3c640f4007440029448030040c10b41040d11041010300348814403840c441d0405400c110703289041103144014044407500c401c1c1e48141c144600d03038010320907400100801608242003000800c00c20914090b1300404803030384180d8115606d0207007041456006003847c0310b10403400383c0240c3c91140e200004c40891107054044004556400301e1119503051002c02e40c00c0481c8130341068810a92950300041c03541d0440d92101c000100c0c00160b0808500b08141d034601514180d00007805014510030021306401c07200e400102008075808001015036807040e03401210440007810316503a4080e640e100035250185150f013500428100702c00050707d0144804034034100d8500360050320800400d622011111100c01000c02c405035001c0c4600781a403511b47c41014002c2c07404170030404c4902e18018001e000d03907000034105890350b00402d0030000c0740d1342c1180840d049002c2c3e001004400318170354800107000d42003 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 935400548 1250 935399298 935399303
    0x1206030212060117010504120c03170a0c140301121506030218150a030c09020f37091a03090a050a12030e19030e03070b0a030903090e090c010f0c 64
    0x1014101c844039a41c08500e040c10380d66000700e1100303c4020004418241e90080d1070003800140e060310802c9015100300c60205805109252804101d0101042024500001d40304a00c8560391010301382041a0032070146115000780000301d500b150b140005200c44524080009014803002e01d03403142580a981c0d0109002e0341d030050010b8100129044a44101d04088946958902071700b49284a0b518241da600401c0305e038014071460005040041c02070294000c0700c16524414401d100d00d40d801b0001103402c1013038462465414011484481d500c60300c8451644407038050282c20032060081c40e40340c0040d420740c1175107451410b960303460352a14030b89417400c0303541c0180007801030401c904104201c8810406d0f4052080ea014040d03e401408020f842d81c0100c000300c600302c1c4e04102c0003400640100c0c00c1c006d05034802400d03540029a1021b0071410f640c40046c602000a41c1e0f48800d4003019000319410002e89000c08182c2c16a203040c0d48840d55904100180c0b82c140450101528191807068060004269 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 935401798 1250 935400548 935400559
    0xb0c250803010e061f180f15081f03241503050c0618040b0301061701021e0a050706110f16020a0503011401030f031b050f0106060e060a12060302 64
    0x10024104880d1035003081c095150360810070004103e0a2401050140000d10107500382e4080c0340720704005a81c00e50003111100c00403a1000d0002403100519240300c401040403518854010220050003482a41c2c02003014a80418120503102000da048a4082c2075a50200d03446138a46e07500c0703000d84414840b800c0070710320840c101111880c1426040048004581c801c500b00da41154442040080038041d111076141e8289401090204500e407035041080600e00150000030520f4866080c0e0324456074500c030050a03690000340700c013a8040d210304619000900140243c0c1403842100b8014003d106404025000f543c0300c1c03041c4441000c841d02283d0410041540c2d4680d10349160b031050041c40b0422600741c0c0309091b088000a03c509060055009a000b00742d00e0b54a942c0c203541c0d030000400b05a100130380400a446c2000c10304140004c0c0300705940703800b460040494020110b800d600391100d54005d0800c1000401d4411452f0702da040648035000c055040811654003100401c4004040d603500c003a600a = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 935403048 1250 935401798 935401867
    0x20a03050c072d0906080c040506040207120807021005040f080a020709050a0b01030e010c090b0318030a09081c080c0d1e02090a060e030a060209041409060115020a0b0c 74
    0x10000700240f81e818811040e5a20b2482d5540c4200100700c2c1c1c040c1c85032562a801010500c465850107a002507400b0000500050800c0c00380e0b2502c0c50a08202e09001c000f0804001c240602d01c3c1e0100881c4481c5d00a800040c8040d26160382c429414158182c001402d5410210782200e4172402805071001170b02d03400104110500c2c08619a4024141c200a90303400319107000b264174a40d0006000c0e961891106032241c000d124038016071000c2652004203011b1078202030b00c200c0100000c00740020700c034200140e910805003501742a030301800c14151220002c200d40100c40219140c6d5041101c4c15070114410109589814102442101510b80303030504a5000d0b0007075030300d252a010150b000e09880c010503210450600d0b2140003d40d090014454501d5040c0d22881c601070003e84541c0040806680240004c030b04860414800610036000b603903e03001507008140144602c4682243d80703605031425100800c1c0d070501d552201c840b00403028061045d02140000c4060000b4211202502c000c2c503d9460052103 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 935404298 1250 935403048 935403089
    0xc080d090302160605040e060105070302120d020316030203070e19030f060e012403060504020d0b0f220201080604090c03020d140c011d0112180602030f0a0c020a03050c07 75
    0x100c2c001201080e400fa60074500c04680c161013201500c003515900440d804081d15060010344030703504003500032002c510034000d48132814039522000c4c00c40c2040c45100503031a030603d42164010680c02c40880d034109032052081044841d8008506920b9034020f4441c000d5140d4030346074802031034450342c10181241700400302010030411580d0180c0038509081d03000f04191040500e00c810802003c0303c08050381c5c0c48500052011a410303078006501b0501c02403016048000b95a280c0d01c20803000c54607402518000020044e401142c03001c49074100b065800165015041680040d000101c06003c4034002d551780c1c8035040070046282a072902460300104000c80f205464585500c4070f2910920a0f40103001d904280740b01e07940075002071141103a0500c581c200000d01240111a014080f0f01c41540407030f29900c0c100d01c210542d115142d103c901509001d07940c0c1c545180c029103650f20103004031284918011440240a602180e480c00c01541403501d560b680c04c903070701094503105054015500b9501001c441205 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 935405548 1250 935404298 935404303
    0xc030a0c050c100c020a060f0c080c030d0c03020c06010f0b040b0f0403050f0a030e03030313140c04060801090b06300c09010603140a090c0504020a11070e0402130902030c010c080d090302 82
    0x100034806c454040ca00380c0c80717200c202d83c0038000300085000b00e50030720700c000c0015082c540038155004440048074108240e8002810682c0e280c2c00c80783c2c0c003080c4d00184078000440103000701400b40511500b04c003019894110600824812741c410300d100f101d40401e458902c22254001c44000319004000c60302030404d600041070b03c0304540d2608070003294041d4102582401c000c01900c1c4181290020070b00080425100d4221249000344042c00a000745010104603030788910031280606012400010256103e1410031039883c5c0151400c0d02c1009070583d01240301004d04c5c1e065000c00040340710b80d614000c0329640c032481c0c1780001242e2684000f03440d0000c604e80740d260340004503c8079046000050350719404400c80c102c8803c2c800182120180d400244131b9814030b40c0040280304010b140194028141c050454144500c98002e49185044c51041c40154070b818a00b1041d0240740200820040b5a140e0009a80da08503d105c1414007104041100500a491003554000d56116805100703905145c50001e4 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 935406798 1250 935405548 935405567
    0x130308090a0e011503022d0a11060105030a060e03040308030405010902011b020901050f031615093606030f0309030501050915190e1c09050103020c030a0c050c10 71
    0x2406405081d000007905509040c1850480740c2e8400c180381c1c61464550304401a41c4022008500300e48103607562441c05d80342107601082d0038802a000754542d40030040091a40040100d20000fa503c4400140503594000c0f810000301503010000044a0600440250a5000c3c5610140411030080108018400d041d080894281d200341d0b51134a46403400010450388040000000e5000107a04c001800346081001c4500c00401005003124031910101400f6010814140c00c0944407080c17a134410b002c00c580200118001e0308215007496044c031540c20840510340600100c64032681003580400200d4111644480040c50b0080000c0142009a050142c250402840300b21b84562038007000a400318004204403401d250f004800300000e8840d4800800701c0c16002004000c1540c1e60710340c2400341c84003041801422210102d0348000307100c0003400505000855480581130600400061110701d00100448052045a0a140e22440800d00b011440c12001c41d8400e50000c1c803150703410524640240114 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 935408048 1250 935406798 935406817
    0x1b3b040501060f05010c08070b0910020706060503060f190510170f0607110309130e1917120a1e0f09020a051906081f1d0f0f13030203130308 62
    0x303c8540382d4420045400700c010b008041d04090f400d00c110800a0703000300449801008900444541610f804503003030485c0d0240c0300131200300380d07111010061410140151984444901208501860f001031310781d294810700f11012414666910001e00c2600075141c2500c007400c0c14490044c0750540d40101c083c0e0b0b8580c80303130032841244154070002c2c10701440744152558404401001e0b5041807080300c02c4c00f1005034207040c4503488e561110400c1158902c1000301640040e500c3d600c0c1895501345080c44020248201401c90032903404100482c58180c4ca410f40c3c40d0425a441c1c00001c0800c0503203d241070350b00c0303050910200d181c14070058800c184240e41114a8150089842c256a927544500308882016124107080c440310854004004441c00f40c3d48442d4001e0f080c0c4840e5252086002c0329034406200340d000700069611800610095190192000394000d03000c0200d42100d08140d036200e1074810000f82400100004c82d0040b0040600c240281c89a400c640c443d0700003c203449240510755a0018000f2 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 935409298 1250 935408048 935408069
    0x100807230d021e0321090a0b031005090705092808010209090f071b0807120527130e100b100c03080c0412050a1b3b04050106 55
    0xc118a00307400355501076a80200800302c1144005031440b0124070b00400c0c20343c50300901ca40d000340b40d00c0d80c0f10849840d9414642990b51110030700300304510072200d81c1105003080424020000800032028400b8191502141d00840e07540e1071440032200d80c880c2e02a81034005041d00f0002c2d4102a908800000070801c11445094158032803080f41d08030300030b24001e03541c00314a0002040111900031072207034021030270307140254203941048030b8507400078446282129181400108801446031000012400e8041490704900d44070444000d0400c180f40c0030403101d402c00b01034056003000d5680c0100142216003071f40042c40030400d500300071916140c4440c24890014100a07030114540351500c0c0072107001c0299142c810f600301c40c513141200e4041008002001e80ca01c100030200302c2e00301c001c40c86252507100740000c1208619a141000303554011a041d05600c60b00400c050100e84140c103058000030009079650301107150050b20461014503002c80841c041300c80300c03040c0b00600c0810742142c4190f4040a01 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 935410548 1250 935409298 935409359
    0xf0403240b011103030f0603071e0306061a032e080f060c13180b060c0c15041202040b21070306050c040e180705032a0d080f03100807 59
    0x6560302c02d64680c082c0f84541041000607884001032048a4115202800721489103456010103501c540d1419500b5504103c02c8504000b000064098140a071110105451208280712610052030102a2120320400451044c40c109154220b45443c2c11800f83d54603e0700d1903607140c0d0600d40319030ba495217941e4a070040100140b02c1d5010350040b1889060035011f6041c030180750661000903401c3e08803841c102c04c3e4445d07501b40615a101e601034114440a003000d0148410000104030422034901a40070070110280820404081006400201c2c9038041d03c01144500c030070b0000442480e800b048143c03010380203003601c000300c0d5000140c50b0180d81c86000708000c07544540348080d541c0c0c0a180300d51b01c0d000c0c020f03000244401e1081d03064442c0f5a1109400c81d02e550f03850701c0000b4100840c2d1074500c08030002c01d074540c41c030f030700e07400074041320300003001e40714500c0c005660345410902d440307503007200b02e00c00000002050050038450711a00c01404408140e95086441e0108041440c3c1034039410810a0070351344 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 935411798 1250 935410548 935410571
    0x3050d0b130e011d03071e0503030408120603070501020c0609010e030706080402030d0509090c16051b04060605040e06011b080301030809041d0c041e0207122c060f040324 75
    0x3a001d6080e101300da0010350900d05291f8511050a10760082c000c56410010759410000c1ca0410245000300d00c14520b481d12020910258885820000c20041c403a92004008012a0360007260ba200c0c2d260068682d10758460104006070b4601081402403505441400800a016075003c0300c0140514070840c2943c076080c048100460341800f56440480c0d1144030036021070202400c080c010800c00440040301c0c0c60b4a1100e0303c0325810039990143c400c1c1810b602003126051841e051081c030300640640d09010381013506142c1c82c1916010000c04a605000716481036440d40c0d519401c060a01903030250001d540c0e07603141c0c903045000d03811085425000390300b84003a03e1400106404070060103e80400200303280e6042c1000c0002600728a1201d04080078007403482d0003201228001066074038085d04031901e0031440101c1c01402c0e0b20400d0307860243e218402d81d0b00c00c0c5041c5d00508a01c06400203d44075030b140c0d4210564100390340301d43da10042501c2c4d107619640e00c00300031040c4c0d42000569081410441c5c0903450 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 935413048 1250 935411798 935411831
    0x1e0d090f050a030201110f042318010f0807080709020309010e06090102091c0b070818070f0305060a111804020409021c0e0106082a210f0a08040303050d0b130e01 71
    0x1c3e10340c00d182c9441444280881d01c00d8100c4070195040d2400c0381d5644a410300e000c6421400c0b001d241001c2c0d0101c0d0401806018001c133016802012035100030900c2c1441c0034801a16040f1902404940700c1c1c0000205d09601d1003508180320003402c02050b03550605000038114000d50000380180c0c0107098258800020000000c0c122803819000021140e03159a00b09040f030b202c2c1c40c020880740310003d42d400c900161303000c1000440081c0803402d90395200c49043d4141030b4980300005042e828190f050504280780c130100c0e2402d4810740c904589040185580660008010380565000394050303a1001c1001161014500040010702c0c40400e82000140e03440c0444500b1b030b030541e0041c0301483d032041d0b070701c5000828201000b25203600c00420003001c1c030400500003150703a10700c86003444984c5060302c100200044140800035516a940c4020a0081e41a64402189006903c0050140032300843d02046803511a00310100c40c0c10002d104400580c8404201c0c001080343d21a4690107602e0089190442c87c2c0c0e0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 935414298 1250 935413048 935413057
    0x4170c031e0909190e1207031706150d090b10091407090512030c011407020706030903021e010209040e1c0801030807060b030a0b1e09031e0d090f050a03020111 70
    0x90108451942c4190030305080c01246a9042102c0717541e10036540a510041c42040d440000e46055281d81e02d049040090405990740d03120000304c4a41d005000c4c0a507174209401d28035503003000d40640c5914840c60b80200508094501524000303108042003600c1c4404051101510548c5408115941d042c0040d24801c15040b10628007103180c54500340f20314904104000a440c048808403031400903100459800c1d140400107000750340010b041030040c0c0c0c4e078040c01005c02070711451038200802d8103141c0b402581d50200d40b940c1c0e4420540038842e150301103000e40481d0384ea00c001400030b0102c07130000d14003a65031b5a50b4061490399404000b01c0c10810900c00c1820398100ca4001c0e121601700030710707034840100800c405581c0960610036854440c0c002044405880c1c0b080f80c0487c8a00450301c0d9080d85803401100091229a640d001000100a1454103158514452804401c0142c40d0b0100010b00c9006260640c0007610324195505000100a4001000340c1340034400e0340207000c0540d0001111905026 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 935415548 1250 935414298 935414317
    0xf1a0405100203060d06020d0938220c23010203042d03080c06070c0317061c0507170102041211011404030602030f0903031003060504170c031e 63
    0x82500c1078111480c9401441d04694001d0110f500c150040c0d80d907000b00e900080c0704800c0340e42c0303c00e140010b001403440710600040b00b0711504c0902030740d201c1c034025040c50743c9006842e07446c0c40315010030741d610144042c00155490f01201402d040c8003d0410201880f1390f44101c81d0440d411407119501d040b20300501480d0b060068000b10705050030a0300100543e102f41c0500300030810b10840340f0340b06130017020850f0001c0d801028801d907500f40c0340310790600301a030003405074080c412050303107050010384e01c0074298100842d8400006090703142c44c1d00180d0341d1140401311110b082c0124805a05114011034400c3c115480d0540c001841804080d2090903406248207081ca40304000c82000e010035140250161840b505240c20011034105c510a00d18070303001604280c440e913501204022603600d07011211500b012800740214154507003460070303940076001404000c0009440740d01040c100602441603440d030f450000d01168803102a2811955642c101c3c001383c91040811034410615461400103c410420 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 935416798 1250 935415548 935415553
    0xf050a150303080a02071b150201020717160b0a0b0108060301090201051902070905131a04240b0904060203090610060c031d030a12020d140405010f020f06040f1a0405 73
    0x61460302d054036295402840500ca0540802820000801d19107800a6400e0381c41100c2604d1410408038010a410070001c3ca02036a01c1001810082002d100d5401e902182d81410140c1e90b040030403d00050040c0314900412019985007403080901c042e40020703160120070781c0c0780c1d03500355940401c2509841c00c4a030043c1c082907042158006020b1041c8111100e10402d004448001e03684001e100c04a450480b040c04011514900000802c101d2029080c8183e02d202003c904504242c0c80d40314286007140c103840c1e070541080c00b48000842d0203400900ea2000f009000c0c09061a00d8205017001e5401210800e070103000c1c103400140c20020a5492406072042a50780f58800ca41d80c0e9000e403a01501c0180c0e0f0450a00142182015640d0801000c14414401c100c44547c40458140182ca800301d8243d00c0001c0c080001c01c07019100305084103680448109103040311882440b40426820701d14406022100750140c07604100500003038840c0103000c144150f45034807201c0613480c1003203801001078400405c1138 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 935418048 1250 935416798 935416841
    0x7020901050d020a17030a030c020c010f0f02070b041829010c0f020306041b0801181106070812010f24080402060c0a1a060a0510030915090302010f050a 67
    0x10304000c0030b180280c40c4050008026030b5224511a4551881a007500d1080d0b400000c0690a40c0d90500403030b05074807214002014108003460010b401c0c070003041c002d0000c20025a8441100310302c20403954009000c80c01c4510358880e01c0c3c0c020307070325001c20364601650120b0405202c0650741c0e400c5500c8407454501035210719001001072004552001d407410003501d442e0300183e104005a5804d100d00c0d03005034440d8030408010741e8409005a1481d8807a4071076000359150890070400300440780e628001540c2c1c811b6540b0348012070040090301c40c0c0a004d10280c0303540d1000c87c91209041400d4001816200011000c4144030b40d91001090008012038900d04281460152421043d018512050f00503100805081c140825030780c0e560b1505001040c2595940d10091007000440c080780c0c540380d0071500c2a10b240100c2420003001c81c0001880c01c41c810200350b6100c10f840140038012030400100f2154180c180300e04841820028003a201d4000c3c9822240d14000226002c030074244104500041801c1c4c200362507 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 935419298 1250 935418048 935418059
    0x30105030c0604182313020102010f060f0e0405030417070e060f0a1e03080a0302040f05030609120d060503010617010b0108101203050706061d311103010f0c1407020901 74
    0x500011403112485c0c4812452010011900c40b5039244511541e4031030864241c01800020b00391780700c08a8955401d441c10034248440551044154161040d0101412880d107540c41d0a13880d511031740e40f01c1c0e4a4414000b916111102c00440e0840c21600c020140b200c07240c84042c00c10040d00c0860356055403050401d00100040c8803603141d03802e4003030500b82c902c0503540c1d501d450f40d01e203c9e8412002d04002a60000e0b00380034400144607090040c2c0816801003000f8500301c0300c015583c05507407030410b01140c4003061014203010250440009854050000d100c01595155140c1031341e900e4810010342942001005400380d40304054891203403583d80a0b0f440520300c3e0410607046e216030364001341d040041c200402c1c000700d02d0f50f015001c01440702c0342080400340703d410044440400040c103e0240c0546102d000b5541500950403410001c44044149200540c1c80ca070101085c040715000c81e40650034080e00c0548450700c0e07030100940d40e90f50b441da50348807907040b1511003c9100b007400003940000460b006101c1c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 935420548 1250 935419298 935419301
    0x3060c0e03010c030605100e0d03031517010f0e0303040c03080c100612061407050d050601090806070e030c0a08070b0f0f030c04030515040f02090402190902030105030c060418 77
    0x20900d052900041040801080c2943c078503c0c01c80c0302080c0c960408003da8204074030604051102447d0000440494100003025464901400707000c15440d130340745120821461400308001d00d200070f801035050b061400c906018003010014031070355034608070b08911407040202c11a48100d03442920100f100d801d698420034181c0112580564602c6006106003102e0306522444001d0b05000542c034641d400a0300e481d50503580403002041c000d04261050028054104c0d00f60f403604040c904000c552942c500300122081e10382640103082c00e110784814050241e400c1240c1e2255101c007030302642c022482c80f0341481003080f12840383e611154403202d002c00800701004080d0012507145041c0e02d01e0420402c8031502d280c1c2041e2102490210b0002e4100b08001d41006007180e44104103179004aa03140c01c0d142c01400d1040c183c0007901a94a0400250031075035500e410714508000316014010340d507150150007000f5042402144c0c0a03101d4007031046450b00c1c00d0740995013201c03840c100600040c5000c2940c0d50 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 935421798 1250 935420548 935420561
    0x80c09120318030d0c02090612010b0a0b1306050406050322061103040606050102060c121b040806090c0405220212010216020109050d2609030102030f07120b0a1a04080d0507031101150306 82
    0x110f5560b01c94106440740d4490340c818cc02070240400403a21a030501c142d680241c1c2c1d480d8044c4040c0071003000104207854102003502c0d07100507030104268070b0f00b07030103000f41d2891850b03031800a1665107071100c0394845c86801c201071401140150000c000c000c0c1c03558011380c0e8411058494440c0600c0038070101080b014108182c95014180080f0301ca0a00004074100550340c01a40010340a50000000c20103000300400c000c181244085906102130309201145c1c0011000d00c20486600e480614001c00c01c1d5260782984408200031040210350f1268611110210301000701c00c12400600d541c2c000185528040b841d05203000d410052140300d042d800300068410184041c210000e2000c2030180301e215075802c0c409076106036101c1c4c1c9805900d01d03142800810701224800c03810f40261a0000204503511001885d2013a0f58405403d400c0003c0c90034484140c2c0c4c040c9034084222880341c02042c180003948034000d4000988640c81d03e034030003482624501c0c281da4038095402209840f2200402c04107545030000e1 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 935423048 1250 935421798 935421829
    0x105190201060f0e0403080a1509091e060501090b1801050904170403120e10120518010e0f190506040f241e020a080c09120318030d0c020906 62
    0x251107a900d60320103d4000c030950003810f241804000700800d054100100350740c440842c0008000b01c18040040301c03c954000c4c0520012243e6030319481c17003003180800c1001d2511228040342d000825030f926107070000d4442405100c51b034030708088040c5018204403840512054503102c11400c20780c2005e0a201280000400a54184101110890b041c900c010001c0000e14006c40b000b03029010f50440103082411000d40203401082c1c2c422000c0915a4001008a45c10600c3d4074045060380717550542425200c80f03010418500c1d46010107007060741400081000300c150303654050b114101e018154940c00b040c3d489401030015000a80020001212342e1001c480241c41001810785d4808001d2032100ca80d0741d00102c9044050340d9121ba641d200a42204040c200e055200c0c2c10340c82d0020300c0800500a190241122000754408910b0f0546a502d1101d20780d0b04448480460f61920f01072091040301c80180100d290282c0240010380300014801c0c40310307182c583d4000d01590444c0d1240000e110101d0b84c3c11844 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 935424298 1250 935423048 935423051
    0x40303060302090705030105090709151d0312090901050a080a140a080304050c0f04021c090c0b0a0503011e052115090a050f07060806010c03020114181b0105190201 72
    0x1c4016a030700c50704680a146240c0c0c80d640c60750b04040c14440c25410150031881072182d0840c2c01c100c04514854050f014851500c0c18101502c0072541e2140d4041208801e15894001c0310b1109601ca41c41e00007419035844120761024403640d80308244100c8980350300072000036801c5889514040342d000d640d02c183c86400700040740c03d43d00702c1e41c03640991900280d0b07080b40d03241c22100c10440d441c50070f0640000140070071202140f034082442d50101002e14a10002d82d80c141d11103a6003001d00140c2c10920700105000003919580c0c003003040c80205264401d000d290102400b5112a400c110070200074481507e80c050500200e0544241149140030a50844550740d4450b03000d824800080300f03104e41c0d00450108000380396062440c17500c5401c052200d08461040e50140c00e080081070340c8400183d0b0440000c1c00c001900758401e0808a001d8131801540d21242002c910601100e2600700780398030101500d1009442048460741004100c00303501e122200e0004006104071030520414821009045419000 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 935425548 1250 935424298 935424311
    0x5181e07031703070f0e1e0d02040507020f06100e040f0213060620060f13051c020724020c01080c1309050402091b030726090d0f0c0206070b040303 65
    0x540300400885907484803800300011084c030400942050410b080c075240d80c181a07244001e9203010034803a4002503014040000544c54299242d1604c0c20170641c1c442d0090428801480c03c0d1a0285d6290444141c02990340704250004861500000b0f10720182c03540d04c812090746840b2900c41c0040d10110840c140e038441844030501ca0a2289841840700424080d01d8a5580754156420392800c00c000d001c1622480c1c0211040200016041c1191944120540c3c04030414603101d0511501d8240a00d1501c0c030010508001a5035031900020701804503004103540b0304802d606a41c244d02c9044015040401503032085400080640c0540c034600d610a55218041c0e00305010900c19040a0180b40d003d54215a03581d4280401d504000c0c0f416588002c41584003015031404001d9008588801401c410401c04152180608100c1703501c90345208201030740100d0711606042c4116512006408040c8011070449207642c080140940d4102caa05900141030300e0925040f034032540100c0d07900410490400d540d516 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 935426798 1250 935425548 935425553
    0x6040c09020d0216110f0a030c05131107110f060f0307030504020f04060323071a070618050f0d020d141605031b0709050f07320d05181e0703 62
    0x82d5004c2d10034000c0c0d00d1202420302c24000e00194150020240d801410a203d0620110355810780c0c03801201d1083e5009540140c50b443d591000304507405100034003070800514901031241c44200104500d104541304001440404200010341c031074000940e07403122052000801d518065408940d000e400a441c4603641307484000001c2c1141c0198008440a07180c4030322041e280d42450241403180440040200b0609046c80002c81c00707032030f00d00c40c0981030440016030b03603041084580094803100207075000d46c810707060305140c055141c030710801a003080c0c1d1040d400900c08240c40002c543d041c25946440f43d05241200e042a400c3c01e034011a10320b02c0d4107124a40c1803001034420001011007074840140b09100340084c107121400d00402d40c6c070080c4854106410f1003840a442400290081034a0a008050b1340c0c007a03910b03607080b49501000070004103041c4211241d0952420060050030500306041043c0d6a030102000b5a15003000c100c034a45030301558201a280c1c01d40c2034a1040f0803800c100325401c041d1740e85d = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 935428048 1250 935426798 935426827
    0x2010c080a02030d0b040204030c031b080d090603181101120212010801090c1401021504050a0b0106020c03011d03031f0803030a02090a150e060a090e040f0201080906040c09020d02 79
    0x1801c00c80107034000102a100e103481445440c8181401b11001d5181c5891511040c680088a000107880550141e200c49490307907040900b07500501c5100c0a841034400c104001402051a41c80380e28003003030820f41d00c01c0102c103100c0c0c6150001940241040c2c1e40c040d4840044462510303419010240c2036003044180196204061254000e10320040081103c20462912400fa4401a0300009101c02c0318100410141c0c1c001c02c003160381407a0000580196501e074149a481d002c0c0c4c4010180507000c0844c008030340c56a0205021100100a1b0300900c030030a000c1d10f052050a400c92001c500642042c00864003c44609011700d88249c0354100a0756115190072110b41143d10680300541c03226400100310170242400280d000007400d6028034080f501441a4010300a0304030010f031389210304000202c0c403014034001c140c0700e4007510010712041c0d0145000d00c0c00c17051800702c42e4802d0f80415140d40016185803030000e141c0c1d1003aa80102c2426600e0703e4004400007035082280400040c40e000d2040042542c1003 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 935429298 1250 935428048 935428057
    0xe040b04050f01080c0a03082b050412270e04051509060f0136180311070905040503221a070c0828020646081302010c08 53
    0x10000302d50207945409078484c03400301250110750203020000750420200b4403c00a0742c441041090603800a4050402e0090303285002403450100c2600c0c142c1444140200501d1101181c0300e1034543d018400c030003080d030105105040001150240b0a41814480c540300c00b40c04a0300240700d2012288000354405a501cbc0250701250001401d5005004100204240311102401412080d5100c05c1d440200f035905602d05a884e44040cd045444603d14141c0c04240d51010017500320b034045e03150060409140040c01f811018800340502d21a0800c0861642024402d85006030703031250007180b030199107181036030000e600b81514420751159a200055091591034900114803070a4030840c0c1d41e042e0525000c503000304180c100103a542e200c020a0542000c45070641100c9006c2961400f00d02c0080d81f0014040380700d500d00c0c40303017590346469003440081d0100954176050b012800f4a0b01c42c1090205018050251107100c200004594802080300c00325040c8003444601e0040c0b504480a40081c1c40c1c21003c0d510 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 935430548 1250 935429298 935429311
    0x15050f040b0712080f060a060f110f010b0f041802150d022107140d020f0c0d0203070b240603130b041101090602030403080f03130501091b0e0609070e040b0405 70
    0x646000d80e4030309035020041c4e640c01807016820007114180440030902041141c041d11040c05910038908095a001d40d14200054075420200c850350f00700100341034080c1403040181c038007901a2203124201481d15000d1441034603088202c0709050001a000c200b00c051102d001c091604101300845108680703540010000a0007451042c0700800ca40c01e080c2d6102d1100524220404c410012100c08020f1900f0072100b011040d2000541c17640108400d840140c403c0b2155a40c0c240309140380354102d00d401001034200c450203540c801e03c20b95601003186031000c803034500106460540310100000d51900101440c0c001d01070012200560340390f5607464110200542e419203181c1c544a0000b050b541c4d00152101c003402071440610700b41840c590b10a400c40c0a00c410200d1000c0002c1700158017000c00700107050007142c0260082c0501155803c002407880d031003442009e003511020002142000301000c0c01805a14081c3c004000c9545403c412510f808125155541c015183c00440420b59a54000c2500580 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 935431654 1106 935430548 935430563
    0xc01030f0608061305070806010602101a031b030f0c030a0b060111060718090b0117092524020303010e0601050403021e01090f15050f040b07 62
    0x620303004002e0921031041000445000340d02440d0030315014038151443c0700c0e100d24000d038a0b0202401880d015070300485106246500580c000f030045208180e00c402180c000b100041c2c00c1c01d02004450a140f0a055508a0741d8034080c4040c090b900480e100614808250501094503020080005481403c440d800183c440e4040c1212814034a480350945d8820300d8042c101818004807102d000c050104444008602000144a2200c0700407058507204d20b031a40118100201c6607000300424400d00419400050fa030b1290500c0f00c0002074001e0a0032659401c101d80740c04040d20000c03404c2030740b2000c1149203010766004822281500d0208852200e0b6036100c00c010fa840348656803000750002c482140351302c075618100c044192544000d07a40c03841403959842c400d24600506001e4985c810700900d00c5100c00c24001d50080c0f0b840200c46d0066800e00b075581c0348001050b003154000b5580300 = true := by decide +kernel

theorem cover : BRFrame.Cov 935251798 935431654 := by
  have h0 := BRFrame.cov_init 935251798
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935251798 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935251798 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935251798 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935251798 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935251798 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935251798 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935251798 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935251798 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935251798 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935251798 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935251798 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935251798 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935251798 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935251798 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935251798 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935251798 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935251798 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935251798 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935251798 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935251798 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935251798 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935251798 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935251798 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935251798 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935251798 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935251798 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935251798 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935251798 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935251798 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935251798 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935251798 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935251798 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935251798 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935251798 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935251798 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935251798 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935251798 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935251798 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935251798 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935251798 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935251798 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935251798 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935251798 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935251798 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935251798 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935251798 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935251798 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935251798 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935251798 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935251798 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935251798 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935251798 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935251798 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935251798 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935251798 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935251798 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935251798 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935251798 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935251798 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935251798 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935251798 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935251798 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935251798 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935251798 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935251798 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935251798 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935251798 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935251798 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935251798 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935251798 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935251798 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935251798 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935251798 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935251798 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935251798 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935251798 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935251798 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935251798 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935251798 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935251798 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935251798 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935251798 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935251798 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935251798 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935251798 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935251798 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935251798 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935251798 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935251798 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935251798 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935251798 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935251798 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935251798 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935251798 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935251798 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935251798 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935251798 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935251798 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935251798 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935251798 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935251798 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935251798 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935251798 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935251798 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935251798 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935251798 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935251798 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935251798 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935251798 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935251798 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935251798 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935251798 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935251798 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935251798 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935251798 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935251798 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935251798 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935251798 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935251798 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935251798 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935251798 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935251798 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935251798 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935251798 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935251798 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935251798 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935251798 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935251798 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935251798 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935251798 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935251798 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935251798 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935251798 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935251798 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935251798 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935251798 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935251798 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935251798 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935251798 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935251798 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935251798 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935251798 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935251798 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935251798 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 935251798 ≤ n) (h2 : n < 935431654) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
