-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3480
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:47:25.140778+00:00
-- url     : https://prove2.me/submissions/f82833a3-35b8-4ab4-a939-abb67ad8e1d4

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 625719424 ≤ n < 625899280 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 625720674 1250 625719424 625719443
    0x70c0b0c1617060105120c090c0d0e16060f0915051207021506010302071a10080f0106090f0219050706021b03030f180309010c060605061b010c03062103020a 69
    0x8030ba202210001d64403501031040d0081c2c070000111030500703c0e03241c5010800c0318003a00c40f09524204106140b031010b031081c020b031841401403800a004500c00c41d84d40d14140320040440000e004503406004941e0f4000b02b04011903181d46980c0c03a50002d0300c00b001c0e140000d5a1440c003000012040b500c03402410200310043d120b074000e01052540101e00002d130303a5006141c00006076103041c01901a40700f4400010043d645200800c01100c18121525030000c0c1e041c2d80300700b042a502c603440c502e00904078410700c0951b5542c0004000842881c0b240410140d03050109505200c7c20740300342811022800002c0701417000024980d0100301c42c960444952800c1c1039100001ca428201559650703800450382d004d4100224008201c0c40024600b04504e03128a0038029440d10002100440d40b1910b40103040b90740f0340d03e4020104403907840d00050440310b50712004c00b1051510780c0c0708003400c0d84d001c2990b240603d46000c005205040325084420842c180c02ca8902d01070900d0341c68100c1c645000c0f40c1014114015 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 625721924 1250 625720674 625720679
    0x1e0a03031d031c0f0c080409090f021f110d0e0105032208071103010b0f130f060b070218010509072d091e0b090405040c0e0c0d0f02070c0b0c16 63
    0xa003400b402c40032003c2c41e03403642c00100c4840e4069032200e91020004d002e068091100b00030b40041a04102003080c0302d403520f43c042e50290b5000c244000c16001c400507000f44030034072603011903610218a04210072400001c0c01c840b40c0102019002d1268200c641d41000000400142d42c10000003100c5001d40080c2845482042c030b500b000d035103075000300500300c8407603008105144d41498140a00d2203641d000030b00c4c605020303840c17008120344044980349035940180c644500e446400c41907c2044000c060140c102503171440c1920404c044030124072070f03451400500c0b80043c4002e844440c3c0c00c643c4105181000d101210341c45d00d501c0981008039820082ca50814240200340507030000c211000c803020050820824071340c00165807601301c9107005007400c25409100b1a8094603254018540090044600740007146c0c4956802e9032040d0b0403a81d0b941840303400544800003005520030345135407a440e42001c40c20007074140d5542080140d68031810104020101b120300f181d11040c01451142e514112a640d1401e6 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 625723174 1250 625721924 625721953
    0x9010302010c1e11010e030a050c040506010c0c2301090608010e0402011e0c0c0603090503031314190b010905091009080408030c0c040b0603071403130b070503061e0a03031d03 77
    0x82c2044c3c5040c0000c42c40c030142c842a0500040f41540141d00c40040c0020410440500c0300030071340182294104078011032140c0105400d00d00000c0500525408050090205070f4000c0d84280c2191509040114000d0f0410002d03a01c808207506680c0304121400fa26282c50004075441071608001d2440c803001c01c0e950482882d04501001442442207000000d040d80e10902a41185c6070040080c0003500100001044a411403550f6480c65110751100349405220280c0e151601c145020031782d0740b04003448c00b204280410030f104640100080d09040c05146080600281c5a20451040d040502e1f240c001c85010441c9600c15034000d44084411240c40b981259042030380c2e80e03d00d07403040d400f51b0b2030a03c1400a508042045034070404071030316080c8842880400d00f50541e40024a044208800d940c03036507000415801f511070184905564250700c9040c09070400441c040125030340440d400321500c280801d5110107008104581c0c150a00074031f95140d080c1c006000c800c6940d00640d15015801c40160f503403 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 625724424 1250 625723174 625723193
    0x6130216020901080d1101150b031f080618010209011403190c120e010209012a02030106031a06030f060612070b041e0905090316260a020c060909010302010c1e 70
    0x900b1340c1c0c0d040d406c416500020342215103032062140746c403001310030600890440c1001140c00244220044a250002c2124039003010280d4010703c00a40286062081500424a442c0c0304045400000c61a1005c40d40010f000d10f0204481c0b12203a40c2e0120004000e0340045241381c028a03481a4207010f0000002c900401007440041e806440600d0100640c503a03a50510a44201c21010384984015510b0b20106090900b42d164540f003891102c6030000c00103031020f0044030000d41c80388201c04450f540010201c410400000c02e111700030b40c4800b00000080100162094002c0b00c291140c40e00040c1c84844c0c541802111f802154a03c040040c000401350020903a0400000700c0048600080d80c0312030f45801641c0003516950000d510034071a01e00042c00820503514207034031907080c40400e00350140c0302d4804040d41000e0010950408100029840c0d0140010315001384c2c1190708070300d010398660024080b0001800040d04000315101341804000e00c0030300350b90300b10b071040051039640d600700d2420340c1c5031 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 625725674 1250 625724424 625724443
    0x304140d030c05070b0903010e19140a06140115020f06072118020f0d0305030a0525031d01150b03090f060a0e0d0801050907120f0609060e0f0613021602090108 70
    0x3503107044504401403c000c41c05402800307500b201101b2400079901c4100c1c84480d84558bd2506014024030710001410328840d81201c20411080c2c10708542c5004080072549280d80096015500f21035814103440c0d1002c03035040c2e4450202c0c141130990109444207504542203600c00000c0503071608041e442e072481401640600540300307c1d0007407260b8129805008001004100003030200b2410b02c0842c0d0300c1d00460300b00385e078004885480065181454034441c2c00c038241c0c030a00304012984c0c540c0e611301094156602d490045440c00001c1c02a0300402d1003504003112907201d16414400c02101040344401d0621508071090b19220481e60f484c14101026402852280c131052440d1184403120400325005046090403150000c0c03590509a59940d410369912001540c000302c1188c0e22080105030ba4407520031000038004034580021001e00f8800541c0d444038001d02104000c0081104100d80c958a0480300c1e601115100700250300d90002d004060146290150001d40c072024020000c52080c0000540484 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 625726924 1250 625725674 625725679
    0x3070609170304030308040b0c070b070e090708090a14030904020703090e102301030e030d0c12021305060f120c03061f0221040f030b180304140d030c05070b09 70
    0x2080709038004890380c03441907100042c0820a0b8200040c00b042c0d0a41c001580320030b45202103803501d501036032030a41c428003c8403481d002ca44c512030a51b44030f0804100d1309038880600c2c10302259038201100b11681c2c42e25081e0000301880003411060405403024025190805000b9000351b4580701c0615002d4060140c0d401b0358121400c00c2000517496a0201706807204645181074003441d81c42084500d0b4800d6100e26024074145622268030b400c05800030001040d07140d4011000151244640070001d000c29000410000118014003100d600c0900108442c400c480c4121051507803038100c3c0d82d40080d580204c42031130b600042e6003001c100a0302c80300d100851056004860051040400304500801500944d61346030040e03010307044003100740701d45000940400380b0b1030501d14200f660300c0307a5420118400c0d400c11280c907220311084c03106c117960203075203c540103548801035402d090074911000010150b01c91410b101d00980d00c001801d00d8000d6101c04844e513044820364600316201e10418149070700c400411170 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 625728174 1250 625726924 625726949
    0x20312090109021c02010e010e040e0609010b13110f03100803040b1e0307120203100506220e07081f050607140c0f1f170f06150c1e0c03070609 63
    0x288821036030641108941d605844006447c04018011500c000360807a9041d0001d0380d4482c0c040c21500200201845070783d08200110300c041009050000010b548201860441d0403d804bc000e402c1509054500e040804401a91a0f50b40d28941444900081e07211040074000014040382c2e54403880d00811007088046a060800c090811f200380c1548012114400060301420881e80c680a0580003540c101404400b220b01094032440014503c0d44601540f00c6100e1022108270001481890001f0051043c4400141c0c1481e100d10043d055134401170090035000600400c0c0f020b0340004031030b90400340401406140c1c43d4030041c9030041c84a092010143c5a43c80b5a440b000740d5440d00c0040c25011030009042c40c03000c1c01c001c080a00600030300d80036070800e02c10354010902841002c0f40d90340d442000d0009000c155401c0c40d005022485030031006200300600d0800090513450b03400206045003035800f000901e208641c00c3c07011810600401c451f0303a03143c060000000f41e0164081d5903001a40e6148a841 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 625729424 1250 625728174 625728199
    0x60403120e0a030c1a03160c170d091704060f0e0d0f20100c03110c090408031e041a0402031509010e0601050a080a171312031106010f1502031209010902 67
    0x1d03203060104072150100c0e82d000c4800d00010508c149401d1400ca44502441c0c0301c10076044141c540e154201081d0010300541e2440c064060060b0520b10f0b00c00d04080600d66450142050b0005102910060b012014400141d000040341c0e2510358550340c80c96000243c00c3d68203c041e140c540c13058041294280e1104c684003809200a150110300003641030300c0c90b141d45c09800d41d6940e00340c50149400784022040d000d090300e607000d2a03c586c01c1d20b5100701c4c425214565a840c5c82c000c25000850221580c0407074104040030040041c040f89489100b9041d440b2070260380350b503544002480c0c03a2000c2080907001d4448814480861130540040403204a114103490380c90ba2148103100214105124800040d845440800007160b180b0455000d01c003904958245044512a1400c1c5007003055403120b103056100b0445e1000f07269020702000960b11040024003c99450070008503540d8130035000d0010701400c0c55500080c1640204115812003240300004035140c0303005035609000f0300f15103d059020f8402c04408 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 625730674 1250 625729424 625729469
    0x1030506010f0c0c08030a02030c0708010203060604030f051009110102011a0907030c0903060c0504031a1627030f030206090312011a07021f0306090605060403120e0a030c 75
    0x22103104400694a400b0b48507800349085400e2a200e01c4155065030500f48041107858052000705620820364000f16600c1c51034123940e81c80c00a041e400350916074070510a00403240d03a01001c071030490780c214040c2c14100406003406070901011222341300c140342c540140d030003c0144014410601003000d0b0020491400d100208041180c05480110f034440360301000988490302990044024081920b004110f182c1c49990700700882d0715000c5c64102280004c91b0400070000054102c03d041180c0c404024014200010300400150300443c0c0c03901489030192448101d062450801c2400c86402034580411994070b08246100d080060300c00e9006003e214001003a24600008a6080b02911b2240882d1a0710f450144043d40d0741c020304200319407100b00914809aa07a11080050300c0c0100140000301c0c14026030058101d81d400d1f48510355241c10071400308450303a02c00003500c04494101e0002009100240340842d08d010210f03401d26403001c1c5c609004001e20060315484001d892a40c0001501c0c03001c0c8410 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 625731924 1250 625730674 625730681
    0x3111b01020c04020304061d030403050c10120b040f09062c030301120c1503050603010b0130060f0e150402090916030905010e0c01090b1204080c07050405010e060f0103 74
    0x900902680c072000e003070001420560b00030740d807207806074100040c0c2c818070600000040c01c0c2a02c0c218002d134000306062007804802c2c480800070810403a5222141a092800504018240405100c0e060b035112500d50f8144c4554204107958848640104001b80c100e1404d840103089410f240c5034450201030f5100c10388030754000048003406e8418001d50944c1e10381f0034024500d1020040c1100c0c0e02c041c40c031001a201e0768204000c0682d075103d840c049090324292040c58216030070000260304200140c0160000c844d19507070305d0755507a21800301184000c0c40004400015242c103030700182200302e0140d40010007800313692105024240542c85006080c5003041004180e005080300117601c403c080000c221444001a403000d040300103420045101c0170252105404c40300701005241840c0c11000c4661443d40e40b0400e917401405220003100d08202c010084242109001000203040100000d60341401d900100901c8004000081c424401580c5503c3c1c81191a54141c508600074000d280c04650b16600a02 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 625733174 1250 625731924 625731973
    0x1201090605011715040507081f030201140d0b0d0305040303021204050f10030b1810050a08060a0e031303050304050108060409031d2107171606140d02070311 69
    0x203503010314000c10750346102e41c0c005001d044840f010b402d1041d086181d41751406140d215041701d40351000303e4503054090b129500c0700396040003060940d842d1b0600c010307a040094000707064146280e0f56190710030030290b5002080407144140d400bc0410040104140d80000184140ca101c0d0b420b43d07060b0385102041203102d01481c000c05500848083d107060441c00c002c4510601e103007003482e010400b201c41b140880c929034002e203000107122a1034000c0184001c050b41082d001081d0581f00c10410503d00168142c503240301600c1d018544c0c4c1c803009001c202d20030800c00d581031100c0101500c1c01c110fa172482e105517a640940b141c140480c100307a000882e2480c0510032200502e0701901c41c41d440840c040f0101c010038114910466001000d5540012552140f1403444c4031030340d412000300a1542080c500c00c108100d0352500b1201e640c032a6060403000300c0c0803ca03d0003240c2d803a0410f01e6541c1200300d10380034107004440c1400040c0340301080300818554041000481105440113440d43d828480d9130300401d020304e4a = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 625734424 1250 625733174 625733177
    0x31203011706090d0c0213020c010f0c0c0305070204181202031c060e07030b0a0b1303020f0a0f0e06030a12031505010201110a1107080303090a0309120c050420030c120109060501 78
    0x54803c041400e000e000c80c2c203410317071000304074000f40c038521f10346a01203820448485c11107a5552107141075001c074074411440d82005e10b0800140aa0b2140e40040c894414040c00030700458a440d2402044044620812041170388804051189480b03554002c3d81c039000300310b50304400140da00010300004c43e0340c4140f400341c403032828000d085561402c505130040d11b14188180c0d00521342c0300d400648074407450050300d990b034585030030503010a103540108803124103071140261081c501e0b4032042116220421941c070460b81d0600000c031407030740c603900020304210811801070201c50011528407091641341e4000300161000c5d88040b080b8a440b000120b00b00d450f01e0f6a852190f10040100c0c5200c240519285c0303800484910407100c034a1340300c4007550f040d500140c4500c0c129910500c0f01e2820540c000001c0e001400f00346404401c0711039980c0340c91150100764810180a1f0355583c1c00030210405001c050318501780c007900856503a08050702030344c1700c960210300c1d982503000c0c1002c004110705146010742d000701c80c0705 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 625735674 1250 625734424 625734433
    0xa05010605061207200f010b0f19050d031403040605092505041509060308130b030c0f03070c06060303181d0a020a0908010c05180102010b030d0503090a0203120301170609 75
    0x41d0802a20700240d030b0900705030060315003406003052003001c000c400041b0390002c0000c07402d10300320f01c240b1000300116500d0700d200b1700c8145440d24442007031b00e0f50503045038070403506034400c082070b42020703a42c0103001e02641c00000b00001c01c000620025401070350182907254102c07000c100020072031002c4005080e00103128820020010400740c40d09404c59200c500b003d0404910b105e0781c0ea600282110840d6000f1a410388022400c1c00080c3d0141c11010020010703586d61502d1131038000090001e0b44510906080d0100d0040f003c01c0c0003620034248449800d501907001c001c0c0c5a1a4103001d40f0000e140d901d01c10031803103041070101e48000c0040b0031500003400c81c3c07105295500ca440049020303410514400d030401c1121800000c05035403d02909541c0085c2d0344516580d14400b240c01c40c0c141d000b100c192819607052420700d042d02c1d04c0c0050b80100c2c0800510b0f20a4a91301d45d0000c56003010300d1524060742c10301c40c5d2000755a051420340001c50485100c0500c0a4450501d0311802d51200d10894010801c4d412 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 625736924 1250 625735674 625735681
    0x10f051216053d08070207030503161712091606020a1515090203010515212716050907090b0f1303140607030b0f130b040c020a050106050612 62
    0xe1141e140c51544583d408090383c940307140028860112240416118020340a801144686421022042d00305401e88050160340c0c0c116110310344da80c0b007005620b0300c100003680d15031402e1042c00c2a0020006002c508001c0e03a4a1542285a10100e402e0b80d442007180103240031904481d6400c9c109004a440725009000d1a00c241d8031180c1d52440da00c0b03070720301e000d54844244021a40c0803500d03d07000f800303029500503185d5052105101504101100070210343c0c104020070304072040742d0141c48072030007403000215030341c0d644228048078404030300c20130700b03841c000400840c80004901084000314040d46045480c17480d0364138010802c00f00c2042e44c062011130510714090080c8203421008119103030203c2d115610b804a070030046218044294070a40f03500700460030650a444050207035a8000f022403900784400103840000401c0c40c1e04803080c80d4070230340c4240780f0709000a000d900040c410700070040003000030503040320019454254224044035554070b0164007041d00d142035420784040d0501c125440c0210b54 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 625738174 1250 625736924 625736929
    0x90f03120b0a090504060f06031a010b1e0304030c0c121e03080106051803120a0f0f08060f030f01020a050910021522020a17010605010212160218010f05121605 70
    0xc0181c415034609880b6514005908030234028003004621403d0755102ca094a01400064100181c0004004503010446424060b030218504c11441422140c01c9a89884034500ae0f61060b22480004060340200840020b40b03210b43c802003001d840c00340504d0b000c0c8030f2901011341d2400d048500700901003035140005100d40c0340704601400b44c269000c45e9000380740c400d020000e442d01407a003201094003000002c054084903030004403c0001001400d29052108c83d1a6004d0b2410b14010020b0340515806010029a035604100c04000998600000c642c0c0e01c0e0302a40c010060b0b441250024001c1c0031464088000364800900e030b02c000541c00003695002d4950700c40c0282410400c0201d00003642a003044e4070091380d9000017801c01010400a05650380c820a20300a00f90340d059440035042d500250040d901624010045891041548000081d05100703440041c1c00840842010305103801082d0000c5001200c5001203401d1382c40c1120400041c0c2c40310741402e82d0350360780048150802007107000e0401060 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 625739424 1250 625738174 625738181
    0x20d02010e070b03042d1104090308220812090d090b040e0c0d0227011706090a060e01090e12030105011704020307170c15090d1104020d090f03120b0a09 67
    0x520414421b000d400d50044c1001c019004e04070800000768480300318108000e080c0d6812048140252000d028a140b5914041c25041c40240141050000030820355000c0945006040b4013551144d038103a03c44440c848541100713201165401518451401980c80d89805189000e044031f141c2d1001c10310b06810403007142003955001d024170014003010b0003171044026550001d00880540c1805200f90b8440c4917a0114030755004650843c10700200c00f0881000000b420103044d030000050f21030103403a88400101745c0082600c0e510244018060b180045036464a6811016004030084c08461210090710b980702d04a1000b032042c180841d1814131010448840ea00100398054001401d0b180c1c071903514400c1c0c003c15801d4550482440d00916442502e6113060189030382200c0c1c0300e6104030304010140002c1012a00c8022003d000700146002c1d5090710756071a0100c80e00d100050b1800d02000d040d504d000341c054150084110042009605060088030f810302c50f4000900000301440d481c03d240c4441c51009 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 625740674 1250 625739424 625739431
    0xc03140111030a15030819031416030921080f160c022e0e090c090d030503151c1e0c051002011d06010303080c070507141f02070501020d02010e070b03 66
    0x90680d4803030010203da0900080c2c0800681c002c4d08100c41f4034244002000c6520303c100c1c10000c1801c04c0e0038000b0101c04c1c01c0504100900700e04000986c080241003201380c00740040d10510703544031801c0200444982c0030104074001d0510100e001c44c252610784040c04041080c070140300004d041c003240c1c207001d881c080080b600c0c1e04142d0300c079005510b480c4061411b6503040706e00c1100041035410804144500306024101d0740036400090351810581d892000031754907041400c01600308500800441c0c00742e2400319410910303610084c80ca68409144080c07042c2e0f0000c0341441992480818003040b09043e00c0d100e010701e2410381c01491601000c1c20a020031038400c8485070804119075130340641c803081d01c50940468207011300500050055615601d401400c0990060060200000c180990000101300141c50420b842c41101c4241d4459103010101e08000c82601050320482182c022181549401144850942da800c0e4240e031140100040b0990a03244680070300f06042e40200401c124814840024682 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 625741924 1250 625740674 625740701
    0x51c0f1b0206130801020307140705030a031113120b07030525021009210203040b0301120809030105191109030a12020c031c08060103060b03061203160c03140111030a 73
    0x340042c2043c49940c40401e50084907890790300105000c1c0b119040150f108207450240c075020310300000b99640701d03180e00840d80100145a107420a484403001100142c0340001031841110300c0c07950b51a8103440309204c490f1001d680640d034034000b0805042c400d0090714440c4d0244d070522001648000101004120b1f000c44032011130107000d940507404c40040c0146030825009480341410060203013052011070846074005800e40d80208001c20000d402e0f0019139044496100c4a0b5110048900b00140281f040314002c56140d480c003020010000320f4150102d0540c942040b0030800c0850f407110006052264003141c0380c0c07650001100400140d810400c030103800c0e0f018816500d00c680d0604c042441c000b2048100b240034150031003580c04080c2d00100b1650b00a0702440c0a100c101c3c5410404143e501c000f50006009005c0850f050b400244208100c51004203d451500401802810a0717042d0000038001100c00c0c45a195102c0080c020500800c1c00c9010416415480d5440d005044802052810300203003 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 625743174 1250 625741924 625741927
    0x360601020f0109050c1201020a021009020402090a0b1306230313120903031803020105070b070c0c1403060c070309171504030f12110a0f0e040504051c0f1b0206 70
    0x444030203008080f0440c1c0300b8002001c0c808109010000c822a1600340889940e105106501000c0e50005041003e440c150000040d41001400420003911903468403a8000b4000e0800141000c43c1c40300400c88030194617261300300151a140c0403108030300c00344070064202400240d04055000004015500111017850004401e4010350310019180c4041400d10046101c1400401c1410b800184a2490042c546c2000d5000c0f805d550010b4040e000380200036080071a40c00005144a000307800e00400a50042c4021002d5595035151080300d4420314071050080c0901e00106100c0358a0000f510790302607064441803481403c11500044184184401101a1081180386240c040d13508021900503402640c0704035035a41000009800070020500c0b0203102490080007540003800c9800fa5540c403600c0d490114404201c0003011601560050000c41c3d001d8502000d001c100302002510035a8441003107070640c01c4003482d080a0328014140ba0300000803a010500d003024204c0c514070390740c0460b032000380104e = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 625744424 1250 625743174 625743193
    0xf0d060504180516060813060b090426090a0306020f04090903030504020913201302040f060206010e01030c0902250b040c090204210201210203040236060102 69
    0x40c09032064a640784803488a064060b105000301070040301c42505803041080390440c54240002d210850003000e14071440d07000344140042009030780041e0b00f210001040704905007001d04110041071403030310450321079140140d07006413605c010000755900038400a10880344540355864040183d80403a240401c1c550b0200300110308100b962060650b12802682c000406151074030510000780c502900105001189090701d1000174045031131500d00307090031100440380007802c0c00030400400c0300300014107442d4004900030402c1d804640d03820046030016401c40d409641d9a03002a24400e20078000941000840c2d40c0c1030002704595001404a000f04582c8a04060f80c929000d5400304949481254091002010b0000344a03440000802031310010b40304614040c948001d070b07031303803c001494001c903507a40d510304813019a809040f1100071944022401c03902d208255010310001e40c4121400c0307201e000408a800c1c8064020210011038510300f010030076010600c0300f0b65140000c0300500050451195200c03c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 625745674 1250 625744424 625744429
    0xf06010503011b02071203230c060601090528050a030f050d05072a0e130302060708061e060702030304240c0b2a0c010c020c12060721020f04080d0806060f0d0605 71
    0x60740b441c5020502c8c50f62522050907280d070909501030241c074104094401c05202c039950300440c9180e80e4651800090f081c0d01c3e030f64031581e4806910340c05035a0100601e00000305009411101c2c1807024414003e0b01c5403014041004e6856002e0860064810341d50407002811103461034041840c520b01441c40002500d5491050390304a14048034130002c08160080e18100b0150104012a000801420961490310740400450070104840004140c180301003501c91580d51030b5031040b116616005001d80ba84c0b50344aa14100d82d103046052174801740c008400c030040d501841608045500c81e480343e4050815114800707410041d1031380e048500c1d0100800c107020303240c0ca20020004d200003540ca40000c00c161900c204081e0a00c0c420741d90543c00f030b00d5245203244040d00045070159108025003048502040e160b8120850f0300c5030b80710b100740181d00c00100c030300c01d01303800b80094011201100c04452210401d01001c84140c2c4069550540000c0107102c0c89528041030b07009407410114a40f030000300349544000 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 625746924 1250 625745674 625745717
    0xd05011104061205070801140d0809091302090f09070e06061911210706020a11030304051506010f0906080a0e030315151809060d02030f06010503011b02071203 70
    0x3200c0800c20543c00982d81403082e00502e079002d6803d003030884503980f4140754146206920b83e1118403a90040004204004038902600d9804c8005080030205280c116202000c2e8003001c1070503442004131034009040962000b401a100e8402c42029103a05880c00d01850b25142d4043d14555010000340718003008100c00e200440002c12032952050031240c25840c07110b041004007403008490300d0444002c0c0e00400e29034002c860004e030f400700b0010ba0300c02c8051000c44100900e10b49000850000009010910500140720800c1c01c40c10032005440d070b2a04001900d0f0420408052004610107000804c0801e0040011503400030344140d012484940004081d82580d0044400c1140030f072503541100c48500300b40d9100030071240840c1c101307490642125909404040c46060b190310843c08400080d01c1c0d512900000104a540603086440226240f01865283e1100b400703414061f600c0c2c0100010f11001808000305a550940c015000040c10007202541c0210815001d4040c403248000c0f030290403202c0403 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 625748174 1250 625746924 625746929
    0xb0304050c2124060103200c121308010f0516030c0509120f0f12030a0b0103021204030c1101020d0c0201230a09080c0109030201080f041a0106050912010c0507020d05011104 76
    0xa00f80d000b4000c18020000c0c00040505014101841d00c580752008000b2142030005005100400c00d0700c402c1200c022a10340200c0d0b00a0401001c2d012038006000c41002c40700805468038034000b800403000800000c4101c0f00200e542c0c10551840601c0c003c1114020340c05a40344030200e00d44241b405184c2c4000c500c0981886a20a90326803200f00e9040081c1020b01c180f003d08001400600104508281140f480d408041e114000007960303441420940e80c02a8101d96101c04060301c800c40ca4030301410050143c1c58401400d495106d036004844046620100300348804500a1319400210940c6400443d00782e50078909000d9442090000020005103030b10285c140d00c0c070603540e901034042c201a00c0500b000c2c05031240b0740c1842000001800183c0e00003407102c0d80020840c80b05910f070303995400c2c42c4c080262214804480ba405a0002080301c551140052135480740658071800c070f0007034558480d400c1381c00505c802400210301340100c40041c0340c0715000070400ea0040c000440e4045e89400003811540c00759 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 625749424 1250 625748174 625748203
    0x305060705040e10052b06090f0b0f010807090b0621040320070605071e0b060a080601080604121709240601080c0901121805070b0304050c21 62
    0x4102000b03062000d40403d036002c407400e50841c1425180401240070440c400110840142000c0c0c4c01001c200d10165400082d0f9402a505010000503414105100c0e500000203581c20503901c400600301c60121201c1604070740c81c500c010700c0020300d0100c40ba0010b100c20555598490703c1003101842e0080c00c0304984585000080c900e4010742000d1502034000190030380c0d21942c1c00326110b80070521940c007081100860750382d8101076561384060315041200101c0c030310710413240b607140c00e14110a03c055800e00c0e511078142901c02c1c00c103654031601102d554000c2441110348507400f901c00a000244c85900d0b072a0110f40500304041c0403802d800c091a050b08003103c02122981c4030320700c0c20080544070302d0001c10030b42c07140001c004d5a06109000a2003000300404602c1040c0002841e00504c1c0d220310f41d9003564022105080143e41110740c070300d80c04049450010755152080210204192070707900c0440e80256801402411140070305024071403103040034840e0100364202000004802c83c4240002040314080 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 625750674 1250 625749424 625749427
    0x10f0e13060501110d050313150e0105060a09020408060408071407270c1704080d060602160801020405011710090203040803070f0e1804050712082503080a0c03060305060705 76
    0x140400140311800780f02c0c1301c5445a102d14408405075801a048070340006c1842c5002e1003000040c28001014854460206400b07440c1c081601d80315501940024001ca5045440000080ea9500c20405900440c01280f0858010601190019480b01d0040022510500c8280b00d001060600c0318240840380e07002100303032420981c204a683d801240e40c03400d4030403e0a400c10550f60310890003000034446840c50b840440f80340d00410b040c4408481034032041400c1400030b1110540300e4000940790081c680501000c0b0500001c0410122010b00948040e100c06a41d0500e2a108810001030074010141c00220146030980c40800e602a0701c2c001544240c0c001d0302c440380d40b8140900010060058521944104002c100440c4d042c0d90b241014000c0ba40e0b007030304160055131200d0412500702005039008030f0504501441d100108800341020b0315201c0250340107041da00341c484803040c82e4176050510040000d44600d000034503084143c1e10a184072100c80c0380c0020103a131643c1da01440e0803003d40300321003c41c00 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 625751924 1250 625750674 625750679
    0x140f1309420909020d1e11030604110910050306040804061e1202070303060806040302060103050607030b130c0c12080a0606030b031507110d0801060e0d020a0302010f0e1306 76
    0x11034154440c20300d10600038101c1d010001c1c050310034444450301601c4200c40e1112203200035544c546100d43d41d50741d086a4144040041c0c41c80034142400e1580c2e00b2144103030052402c0046180204015220302e8211041c03281c91715540c0c0800c05804001885103880600d150310128031a1070802c46184038070b00c42c141d016aa02d0900c100070700212a48034502c06030f58170044018000540c042009544145180009600c4035001e00d41a0094001e40c0c0192078a07104042c1004181540082d909040b130b401042526400c0e2034540d07003101a1403c015810380c000400c0078911449034400d9210400c3c0f0040c13880c01d076040b20126034823041c81d045400e52820004005005001c0a1400d41c45800018072441c2010480c54880c100841e49840080c0c654031038204100001800040c040c1902502300311102c000e03103080e80b448030b1000d4100d40c820b0107843c0c001611000c5a441c135050107400c0348100b940003801da0a4041c9942d00440d40c80900c10600c80400030243e4124201e40c451003140395414a0b41035003c9140350 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 625753174 1250 625751924 625751981
    0x150d0c0501030b1c03170c0a0e040b040f022a150f0a09080c1b03070302030a02090606191101150501021e010213060504030204050604020301030b0c0903010209060c0105060f01140f1309 81
    0x40041c0800e06110000c200320380c1160f8002627810140c1c58145c0f404900441a00001001000e55001c1914075a0001804003543c00c507201e0880103940c0d024002c0d011114003101016500c1500c2d480d0b60500741c2e207074008210b00f100c0c42c0701c0341c0350300a65028000ca4020754a0b5218001c80d0020b86154220303501004059100107507880034001650740a038001c240491842e00000d648100100c0701078043c18190000c91800c0d1106402c40c0c080b44209680034040e1030a00e4801411810202d0000c00b0039440c0c00640100342c0411805442203440580c001d107040020040242007124001e9010050380d9801c101002641c4000854000100203544a02c5d4a4925500500060b200000c110074400d510400040c00012800b800850b006426424082d0f2140d18010203c0c0c028440c1510380c60340900007141c10400c1d2001500901d02c80e410640e441ca10541078040152105100300405209128050014218242040005d0155058070410341c0f0100c5545541e007100b10340307003880e08412041d80c0019045007170 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 625754424 1250 625753174 625753217
    0x30103050a30261023040c0c03080a020f043503040306050a050903031b040905040803011502010606020309010e18010303082505180324150d0c0501030b1c03 69
    0x3842442901c0c0b41450070581d40c1080c52621300038600b0701d17801741c484a0025400100b04410181020744100700301003040001401c01c594081c070450000c0d94110005075245154003e4031405007030040b0081c03e01303003804030301050240150300000003001d080c88960103000c81305d02d4542d0020f9102002d195103034294140b000c00e03a40002e154050950414041c0b10701d865002048a0303206240319400c04204850320710320346461040b5807050300400d05040601c8180255800158100c50700c9110441c01d003207a0504c164282c6250b4440c040150b0024042d00340e003540a681e50a00080780104410791800007012000102079003a0800e0b000101c0741c60800c0280fa000340a10800c6940006060400b00e811040041451140940d409408010002c0c818580e0302c00700203600c0107000354492942c04000d92500300300d005c8030444a142c45104031800400440c102003541c0f000090308021880340d080d05003801500640101c20403284c001603501e140c602074007004001141120311a6540000c0f0304c00c0c1c09003584a1 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 625755674 1250 625754424 625754477
    0x61a0a0b04170f0a020613180c17070806040e0a0f050a05010c0c050705062a0a06050a02040f0b0a050c031803010605101d130609050f0a02030103050a30 67
    0x31980f2600544002000024020700a2a41113651913958a68564a510844040d0740700711160b40a081b003420030785642d03400030410f00550340d0310443d842c050b054542191032825503480c1c0200740b8040102d8a107082c183c20294011405104880d4040c0403680d55101801000800f80ca44da04488403481c00c2000a000e0001480a10320b08029154041e803103c03a12101d403481b4040c4644400030b061901c07001e10202d041505041d800b0328075074090718074000540350304641d2011501e00340f42200240f14011107100755030030784000141d440c071030506081d0407540681c881d1f042c800600c00117010f4042c04080c100000c2c003c44540e080c0b0f011002c2c1542c2c0901d4203446030381d08040c3c441c0c68014207402515901289003420996600c0c00500c14840c1000030a01d424010a2001807050074143c0100e01142c464000742e004141c1000c001d0324030381c0c03080c2c554000c80c0001c1c0401040760708000102c00204074804801c6840a0554800c8800746c0c01c4815440b4030480c406e86180041080d000707214070200d031080f086004 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 625756924 1250 625755674 625755719
    0x6041b0804150b030312091c0206191107060e010f051906140f010f0e10050c160305030f0d020423120c01050901031e020301080609060919061a0a0b04 66
    0xf01c242000001d4507030051106a1443d5680900001c804d51020001d60450b50865103502c0344466240100079180c0d0400c41d04184910b01d02a142a09000c0c0762140c000710040d4009851b0400001d075640c0740141a214038062125902d442800a0300b6003140b00da140500c0c448950218020f960b0410303107043d680d1560215100296921003100302c0d8a564000380070443e400d2911035451480b411090f00c1c00c200388240150000400c03054078640e42e80100080c88400e0309441120701e200742c03200c52007000c5c500c107000080c8507030010b11890301c1081224002d410b28610b40c48000d81800d480703154290080081205120100300c04400504290034001460402c0000550180c030f50044080c00180880c86945016030400d60b07561501c1d000c0d0040d00001030100710000a0640da00e5070354019069075045d080d6507002940c010320022481102c0005500c890740c940c1d80c1404c64600d000354a90f8401001c3da046280d454072050201c44090381d03603501c0503002034445a082c15485a04104001c2d0380b25030078441001c07 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 625758174 1250 625756924 625756931
    0x6051e01210e0604110301180f0f03020f160608010914010b13030f08031b03010e04080f0c0a0609111c0b0c130303020706080703090b0f06041b080415 66
    0x91180d074400240c02002500181c000040300c100c0c1c9032038004056001030345540340150024001000035103180d4000b44c240440091110000d00f07280069800004000140701e0101d1120a0000034107000b0172206a45c001d0060382c2c01e44404540b050704080740d05a940390f034600b149005205054000980c0d50151000ca6002c02117403400e003071a6203152406020301c3d10035180100315202280c0c8960200703000795a001d41c0301200b040541ca07103004070341c0082c0d81c0419206c44140e1003c030349141c3c2809981c100c4104c02041d6140380ca6131344801d5181e80c004108100011400c02c00c44642c040200039803808a4420720740040c406405040110707006034030310101e40c801e000c0000000c019841010040389215001882d6802c0d9803152000000c641c859200c50358007000f1010310000906401081c1d110032210541c03035010310741d43d0b0104114212014044020071582201010516840c00d09202940c00840984002010125200160398400350002d000b00000c1010042004000c902059045005980343c000c4c07 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 625759424 1250 625758174 625758229
    0x11404060b030112061a03010f05040c060809061501021204150816020705150433031b0c0c05060d0f0e0c010207120309030b0f040b0f0402091f15030605 67
    0x742c05154046005130809446807009252005822946c00015100030004c02c0800302c48a00c40e0041c080441d010348480c00301c8000011035a014034182485132403140040d0003280d44034001580030848150f403032030451161040e1b459450042000910103001c6240207038408480745500200302d100000e0414901c400f200e101d0a082c50303000551030041e1241280c020214181d007058640750307070042c0d902110304030031160b803202d074014101403c1a00c214000c1d258400818410542070707040c0c0b00f102e800d542407900d511617801c940303522034038004140c0d034419030b21074982e01d690b54001a10f607040043ca03a002c043e901d141d80c504200861080c00b5454044030302074400b1415090004c1e4480350381e4440c0d0783c504068004002d040601c5854100c000c0d6904c821002c0c8103050505280400f06002c5078202d450280540229803000c0e900e820151017284c0c000c0c080c052030f50710751070705501c2540900314101150f03a42040220301e80f030301d44c0307444412243c0a80c1c0000d100c5152204004000c0302414244c0550302004011 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 625760674 1250 625759424 625759439
    0x6060d02030d03021e030703020a09150e0f0319030801090605090c0307080727051c0c031e0203010f0504030f09080304090b010e060a0f03150506090405100806011404060b0301 77
    0x8602c4040c0d6141001a1504803800d02d1841c0548142d0b003a01103050004108110740c0c0d011350150280038041d6071035800d00c0ba250304040c49482e0001b802b15001c01e403488524800ca01e0070202c5010045c1c2d000e001c0d242d595000402565901144480444c0030644004c010b01070030040e880307008010001190f101c21b1030b0801c81c6080c0010b10002d03144104226103240003c403000c1c010780000d415115050038141d210703030886001d50451a114040e0705c1c4148a0520b000411f54800308461400c20742100d49288000d01d10b0740c644c041d614541030080d00150240940c40090390f000e100c1c0c3e05618589071804a002d140c40d01d4020b0601070030382c030058184540d810041c005c42d0000800d075410ba82c140c00d000101003150b0380041e241c1000e200f0719164452800140101c40036481102079542c1545620180b1003000100083c8600b544280035264104034103000c03961052505030400c581080200c50809441b68907030011a040c16400d820014412061400f44085428240301e10001420600078550071541081c45 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 625761924 1250 625760674 625760683
    0x70c0203190b06060a03090510050906060a21050717060f0f0709060f0215011706160c06090804030c03080406020607080403080f1e15010e04020c0303010e09151806060d0203 76
    0x100d4010000440d17a009010700a40c465603034241c000c000c0740c0c0b4032402c249405001d048122a20725081c09203034040b80742d03810054030202c1501d800800b141454111204020000c1c000d40c01c064809100740c840010b00c014481071340200701500c1c1000b6080e18a84982c0b610040341c0c0140c4420784420040c010001131503449002281504d9492910801050f00460200c3c0f91a44041896a12074031a40000950030111099080c0c0d2079400f005a907117980e901c5a001c0149090801b103000801c40031280d8400140c49940309250681c4074290b0706017440e0300d0f511040c009241a80084850300400141031080c01d070104a002d07481100ca1412090514050742e0040548901a0580611a40c140f0104404480a040c0380040c48000c2034050918a043c10070039040a685c0d05400d070101d021103038081d9450600c0d000b2201c9111401d80103514503460091b4000392040d00410300300d0140030b2a500c0c00742681285810a029408002800c0c1c07610406a016504048000e00468452a207845811340141c60104 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 625763174 1250 625761924 625761931
    0x1203131d0f040501020f030711011505061801090807030503043f0311060a05071103042301090b0f040905060402090a182d060e0906150d0b070c0203190b 67
    0x51407440ca580b203a01d80b642c0a0f00540c25094905107001c410484456802031140700c0d00c521130350003840038408151802880c08030074014aa0801c60410a4010700740d40e24010780700b4240185003180710340d03079542411400d200be00d13041241d10741c100181c1008011500110070300202c4081c031000c42c000d03e20101c52262208108891031070601c5001c0107505040c040c000f0400b05046880950b01c0074a46140c4840081408540740c0c404106214110942d9040005c162816140b4003450703083e0460091200b441103c0403164400e0400000350408524000c001010309000d25080c0403068983c1e0500203408107481e001001e560041e441844070b200c883d0384500e41042281c1c0396075009a0441d0326640c0402c051702c070f82c450700182144180014000000607400c99000c01d04030b00e01c104112501c80c0900a0b10380802c1c0c81c9000f99034401c4010440310280d684805402d500c0c01003100303140030340b50b81e100c50344100102d41c0d81c0045060010341c3d50035824240200b52044100365a000c180c2001982c0310ba85c01c0b90042c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 625764424 1250 625763174 625763191
    0xf050d0f02120a1b020f0c09061c03050423030c0f0f030304141509240d05010e101401020d080604060305010504080c070e010b271203131d 61
    0x6426000c03100116030304840101d5541ca00101c4645440c80052015102e0300340324030860040e200d10705140510200342c160040c0b03003c80c0500006041d000400c800000c0250484e5442281d45c1c10701c5002c1c200307807062940c40c04d1207500e9075510707940b0f00200c0542d41d804001c45035501000301620b04003140d42c04181d151600300d00b150b0300031414000d0000b04121200c2d0500c03244e09448001808600e03001703039584404803550211401000050090122902c40c02800c103800d412103200c83c0f455544000601c482c2400003000300b041e0781089000800c16050312420303480b110341c40500a0902c0014480b0458031005081c10140032580e02d512800000d545224201002c01088004404a03841c2d5942d46c128400031600b1800034403190a00d0b06121101c0c3d40100b8020010784140c000c00a03103059100c5000c1d0403600c4010600c0d0a0500c00611400c500103181c0d140d1149034040d01040c16540e80c1c801c802c003074080c0750340c2c025038550780604000195203040c0d400c0541c40340041d110440b5080900f1031b4203907109014 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 625765674 1250 625764424 625764431
    0x50115050a110a0c06171b0405010807210c12112208030c030406200705100c02300c060403060c02071206090c0501081902030601020f06090d0305070f050d 68
    0x5086515041262800300100b031100302c02c0c4c00082503580405040e02450010803034400f5a1910240000320000790403c0303c401c15420b000411181d8050a00107034821130900b41a44051a860f00345151041c00c503e1213910b00344e942c0440d0340041da00200c9004914003d880810451034030190951460241c8950f0443e2054140e4983c400922001a040001c1c42850122502c0313000c0c0d07100e06c1d516600640500d03000a2112165204210454103005030384406800141ca0214101018803150540484240d424000521001e00068840003412149201c90707482001007034200d80081750760355035814080041548081c104000079600c0b24200e804032075008100040044542a0030b030b040003a16407020304480740c40c202030400d00003640c1101c0d011610034405001d0890b11240191200ca40641d080080440276914003204600168000c50b04150305004550b06d0003440001c0d613281c40422116030740207410500c82500d0154050042070b4010881d810501348025400a00801500070440030b4882141c4 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 625766924 1250 625765674 625765697
    0xa080a2a090801090b01140d0b01050105160816020102010b03010e28080309010b010315060c02330c060609130b0c04050d03030e070e0105060f0d0e031903050115050a 73
    0x1078150703400400d0400300078480098941401000c001c424462039000c500505281c00e0310b071806080400800b0f074840000c000c146d081100440d0b044c0c0000165030300284200200f1b0700407031116405007880d40300031182d582c1040420320009082d5002584c0087c000c1c0c1c1080e401c0003500002240864038881c02c06c500c060310010820100d83c01e90078035500a42055000000e00070340c00019040051040c00c281c03003d1000803100303555200103100d2407085200080c92102000014a000714002c0c6000d00f4100c103003c0740c41a04415a40d0039008020324010400b800103020300528414020150b20090407586c0c3c2d01245040115800365006040c0010042060302c00002d400440150942300600741c05040541d020081e454041d00900681c8010300e01449941e50000781501c10b018402d040e82d0010708810304101c27030510020720701d400028800344c0068440c011180328403010005083c0c0000d0764205100301e0312400341c000d0100c1d40c068000c009046920404840c407550060211640f00c12645400410b180 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 625768174 1250 625766924 625766927
    0x609060f061d041503050609060c0d0e12040909110402130302090903040807120515160f03090f03030204031b050618180702010f060915060e0a12080a080a2a 69
    0x2612840203902c20300d001d607940c0d05905035a1382841580d00c200102c0b01e2581703c0c001002c1e69460103c50b0b441c85d802c0c08020041c0341701417a4102c400380f01030318000c81d600c0491303864002c001ea030030a40001d0b07000d560b94a50a024494245100001d042007950114035104458021414404142c00064005c082000c04200495810000c6400402204041d85c4515850740081003019101010076a440c0c8200300102ca0f030740d0381c4583c90301c0c020f00c480e10b01603980b600100da00f540d00c101c01c4ca980f2420301d03a80b54000d0001c01c1080d0440d1403000e100f940c0040ea07a904618240718103000c0240c1150740f41c0107081041c090742d11000102c2d1a844001c0c2d055000000040300010449041035009280201282d402e10a40c7c6805401403901883c0c400024000313a42ca03880c0401c2115450b40c0010800d9200301d40070441c10f401507522490508002e0002001140c03982e213144407100540c2012103c1c240002240f4030840e91003403d05d0380002c244841886205000142c80c0c01d40424581300b08111032500304d4403040c05 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 625769424 1250 625768174 625768217
    0xb06010c0b07021509011b140c0f0d0f020307110f040905030a030b1f1b03020f0313030c230909011e02180f060711030109060908030405010609060f06 66
    0x194001e018620034905010001d40350b03140d51100701a41150480854200700043c042c0102c4521055649001c1d40d01c0c9020449034010010401c0340c0c401010007503401d0a420500055400c44542c1c80200905042d0f0a8010041055042c062046400a0141400280b0243c0c0d500035807070001c4480724010744118002500400d0000c000a01500c80054182c0d0415050b03041005046030840c1e034a1482c0803171100d503541c000c140d4046407000034600918007142501c1a1000c000407030091044805409590041e0391030b40d032200408540d54030011004004008400751040c02605c00a1500044003203416106068100015840b41c400c0c40700c0c10000b0202d41d000d5010880740002c0c074002c3e20003030340070120b02030003580403480c0c21008500c60140007105003402e001f8114418800b91030203180016a8803022400740c0744006041e8507549850032240410300f80e0181c40203942c060b01c40b45a69003424030f000d508690f110743c8440d80b25801c0c100704000320b58131a0030850803034040b41800040c24140060f2403101 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 625770674 1250 625769424 625769447
    0xe04020a05090f040b06190306050408070210050c012004050d03120c180504090b1317030c0307080708060f010f0309080c150106030b031c120903080901270b0601 71
    0x302c64800d0411042400420725203020b18000c04150000b81c5440080c030a4911485505c4850b904160008100140c40c9a214541c454002e0b01140d04007202c607400134490604104485002650110f01c8243c48003080c8281010000d0303103803001c41090183c42400019004901c42c6501c50f01071009c204081c18018990f14212003451041004009082000a030203905038000100e1400980c06012035641040d202d00c0700302d103400100700d682d070b640c80400c449040740d0119412142c5811f404089014011a50b02440c0148554009580c591400302c00042c40c10714000e090300204014807040c031045845002e00c00e18140002e107404043d00583d0b110640250003440c00049c0515000500d1360707808080424002e10800807100700e18281c2c0da032031000302d00783c420a80c41541c1c5604804000c1c4808440a401b5400a012038240300641040310105a070171100c030001c0c1900450340b0281001a869002e100b252490584004030030aa180049036003c03691280020080c105514107020800580c041c000c644030 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 625771924 1250 625770674 625770679
    0x3061302153a0c020f0c01051206220606020105070305070e090105011107050a1404060503070e0105040c0c0812040b0117060408030c0c0f0705040b010e0d0f0809030109031701060c03090e04020a05 86
    0x8540540f080003903803605140c2d50b2081070f0081d00001240e640c4a141224890303040416000ca032610348030100017280300040390307409070501081c1750442c084245000d4500146201d40000449203080c08005c3c0c151a4001c0c4210100b00c60082d102c0c82d1540c2c0c01c2c8105056440030b280c0032410980300d000151038500150451a480820400001540f000c00581000103100a40c0c05000190703071340d0b0905650b10464003d01900710850b4005004030305055100c051441200e141201d6060440e07100c41c0e003c3d6014591040b80c0c044900d00f00170070301c0040f9804034010700c10514001c80414500025070f440f000c005d80014012007000010070603030180ea07825240701001000a9690061520104a648002c18030420b4010790801c003113010300358011408102d850300054401000412142c1c0d4400d8512a90002103034202c50510a50000b0b8a00748034240101d071094075003801a074143d0b030f5241d0950105038040303002c0003c10310030080000d502070a1041110071990741c0025030380300c0d4800102c0f1080144c01c03941c3c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 625773174 1250 625771924 625771931
    0x60a05120c03010e03040f0611030f0409020d05010f151b0b250503041505060409080417010e0f030702090c0405180f090a11010f03090203061302153a 66
    0x310004008180310500d4001200200f001c845408082c9860740140d10500d64076000710310040007200c0c080e00c03407166000505800c0d0781c44c00074010048a20b5821903007200804c9640030410916580c0c0522801340900800034064003028a02261100c143c403501d0750020402c40483d4041110040801c991020315901c101111070600c0c1541c0c5d80c801001d001c80f22500c2a48010880d204070901820840f030195802c500442c800d220700c290139401409000d4655500035580740c03000c40c041043c5401510141000d00c10644182400d00c8106003074400500d40002290032400c1030081113480013080f5585136605440b01050703540d5000f40c0300c045004590049400030481045181107040c001006407040300c950601c2012502d81e401800d40d03c0e4100e00000b05015200d0351815201c0d03000340581d01c20742c040c2d480e01085180c00d40d4086404c1200580310600c07801d10b80e5040c0421890000b80c81001142d40c043c0c0d07981088011480304038070b01c20441d000040c212451452844c61199200d580d140c1c05054031051 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 625774424 1250 625773174 625773199
    0xc15091106210109091707050c09150420030114120a0503030a0c0f02070b0c0a02031c020d050712030b181e07092616080a200d0308060a05 61
    0x40314855145003440c0b80c0345100c00002c0742401480c46201000d640003c449403070616081c02c229100d40c80301c4000c0d00c940c0f103240c0c1041110350700c00c241d581c404e000140b41d11000f01075050074030080c0c4007850a103500e4a444095000781c1000d0000940e411100c1d080298440b0a1703001c00030611440718120040302601800d02c0c1c1c14203100000000318000d03503000c0c100b0030000508400403648203402039020b50060b080703070b041044100c850030301500c5011000e00c1500c454450740c1d03000a140001012010351100c410440340c90b2681c0c0c040c041c1c9085510141410b518140340b640c3c0d150b040b42121940d000c103140daa0f640c005020389500421940115900305440000e003090b401c0140140502c44140d05070f002942d00041481c0c3c41903945608803200540300107400019100300c0e548103040310040c01c840d442007a0060102c041d0070300a803c01804800b02822948426042030b054800420307aa405403800400d008409a0300c03455414584503425161450480d110000029014a05680f1130340e80041c41c440300c1e = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 625775674 1250 625774424 625774447
    0xa1217161b060510150e010f09050a080f120c0a03051303060504060b030606100906030902180c030f060406030b010b03060a03080c030c1507200102040e0f09010b010c15091106 77
    0x280c4d001e85801001c41c0c0d909035035841c41a2041865603a03040000300781e21a43e0800d0b50064400144007900c5081c10500d01d42c41c0c0e00814000003607a03200709499400907600701c0e00070b001400050340d4a8a2201c10920b010740803c2d52507074a905030f8034000c04100001a5080c161607034045204d001d943e11800501a0317007081d007401e001818581c002140b090080e000403422034603040b4144d406c05e441c40d072607c5420764030f441c1c410740040c8120312084e60400f000081d00c049888000280ca8455110f14a08030b0b00e900b4003c00da02a40c800050a807400350b49026001e00c080f50070010349034115112106520f6480c1d0f6100042400e01c100341e07000800c00803010440d005403017408000b401100886000b207030723541c500340b1100d0443c01206448036808600946880c00320341640300800f00348900c040002616090b941c0b041180d17070b42403c450a41681d41c41d4414068000428010000640002d00e0042c1e08000d064440040c144120251403d042d076941b00d480d010800b2520040001e0343c0018207581d00c07110b07662030 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 625776924 1250 625775674 625775681
    0x50a0215131508131104110702030d0207061412010311040b041a010f03050c030a20180108070201050405073606030b10150513080f0a1217161b06 64
    0x1100d0302056568000800c131100000c2102c2107250000414a429079040c4180002068880710f510b8003480100a400e025031010004401c5200040d8000c000c0f0700d2500324014044c0181c1500c01e46040820841004601d110300c21050550741c00c082200740e9484107a00080c020044510001d41150404040399942d044910303414400b2032081e00d41549100e0001011012100102d8070803900b00002d2010401d9005564000215101e4103044011a02d0040c926401550403c3c9102000d014011360000015603200e10741c180c0107030260000703203d00c0c14583d40c0d0f507031a04094080d060300c1c2c9802c18a84082991000f580100b80d184003604680c01504005a4601a207901e010030350354a484280440e0344512107030b0200c011140c41000c20b41d0150b00c613180440300c640c415200007404000c0d40d013000c983e8100501c240856410384400038040e070300c52440d101e204803542100e600d040c404a01c0d00341070074400410001d6444000c410f40400041a903800a8460700d85006200160300c107108445020042142d0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 625778174 1250 625776924 625776959
    0xa0e0306041a07030e030d05040f0c0905060310020702011b050c120c0406120c0902070201260402031b0a1a070b07020703140d0f180803030915060904050a021513 71
    0x1408007403196140c83c81502512140d000300503565004120f400f0b44565640e10203078015224403040c007000012522040c401d07420703e4120884540e40c2e5070a000301494100301ca0801004607000541c1000c1160700080c052161803400110101011100d100c200503003880006a16800140060054000440e1550baa00b030b0708051140036520f0241d001c282c001c400c140d4403182c5e0b45d20a64440d1014100000b0344081e400110040b4107104409040036800200307800c42212110301402408068542401010710300800040020750421141c51007a4035134441e2100c1c5000d4030141e02e0a4170b13940f91a0424508140b06008014045410240c107109440b6404601141168040c0e0030f280d40580d4524002c0d5155400700c2815004900c02c0c41d136901549010310803550f00075a44c00e4544141310742d0b90610034195030048520940b580c120310809482413541103002c1d900b001007a2110240c0386425030350581d46580c0c011700a44210020303100105156401821070307041e40112400041c003581d5505940c03000c102c03143e = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 625779424 1250 625778174 625778213
    0x5100207051809070b0a2f0c0a05060409021c020415090803040819140a05030a0311070b040602090613060807030c022b050f0708030f1b0304080a0e030604 68
    0x8080040c080050b89454a005a0300d240140c00b0040c40c040c0d205415a100d6100c150030300640c1444401c140c801c04520b0106080b07144241c1c074050840412079030400000c02032151151900000034003180e00c42d003040c0d405940d030041006a413185076600032001c84141c040e2710614207000180114500c0800c0302a100228080c1c0c8450600075111541c00da20303401240030f51301c861b034400f440383c1a524180300d0300495000d004200d1a41664181511241004250310060b100c2e9800010710342005a0b0501c6072045580b813100d0407030708042d401d546d4002c81c6040500041d260303030317004541140541e03640012150551400429169942d55030700020701003000440c1c1d080046031a154200342030a001040da4002d4484805103000750510602e22080440c6040c0c406208002043c4454000703404103100030440e00d8020380030903840b450078120442070340f8402400090701c2c7e5000c130891040c28280710300366500290300c07e0f0007540341c000300642120440300800070254540b1238901480300348a002203060310b20b54540b = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 625780674 1250 625779424 625779439
    0xb0a09090c0506070506040f0c0518160c020915040b09040c060e1f27060309020406080f030d0e0a12030b0f1f050304081612020106060207030807060c0201060510020705 74
    0x3542d082185502812a010b000350f04580c000500081e000c60384910881d1082c0c601e41000e989410200b0f001820000854003130030111414031141c2c0c10700a609000c1c000d910300c0c0026a05181d6400304c4c0340f10314054000c20103070304203508118269489403c80c1c081c0d804003902c0d549070b6141900b4500440020b034410070380030811841e200e06490500e90207064603a00c00f0b440d0700c03c9103a0503440449400220000014000c01c0c04d1601d26050b801c002c000310700420241d9000316840090b4010031080f20300c150300610980e8001b1440b10300d0040e0100130386100d9512030000180c00e140b5030040c0ba00b13040c003c42c001002100040b180da143c10703030150f011072000e0b10b00b1344001c81e0121200e020b01c08120b40244450f103500300024804034109201c1e0f00107513485440fa00700c0da400d004c6180107200402c24080703c21201440000c0b0079441c200e60921440c4000c140d0b5200030000c1510755120307211584210940580101c2d200c101030444107000f50403010051a0180002e8480004800001d4440f603507400340b584561407 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 625781924 1250 625780674 625780679
    0x703170703150501050703020a060f0e060606070c27050103060519110f070201020c030703290c07110d0516080d02060402100c051e0303041703070c020103020309010b0a09090c 77
    0x71a01c12900b0702e801c40d2280c802d0041c02d1100540d140c6c2c00c480d200300c0851040e01c40c0c0c034000410714041d60401c0340030100e001c00c295404044030f60a15800810290290031300b404502c02240e90743c0004d000b12200c008064800c401101c8410303080800300b008010700242408000010088194403d9209582e48480c400030303412403403550003e46001c90f0301841495024000b1050008501c4000c0030301500c140111041e0030305180101b420310513103a0055815120380c1000c1094884140b020482c0c60920f201c20642925082d07882041d035008880c00130340b08401c01035081805840305130049010302d42080071111102c00f10101120354007058012894103004140d0310010081c00000c01d24010750340104144555141803008541040d280c07101540d02c1d1040303e2207855018250540300c01d504411001860b038914160070b015142c2c410880070002d08020070010000040e60021000000c20703070901e00580c0c0c0382c4508160901412040b000340b0340c000160344001030080c0140c1d00001d86140315030b6070140c8255 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 625783174 1250 625781924 625781927
    0x16030b06090102070603020a11070b071e031b17191b0314030a022106031504150510081e1c3e0105060a080c1513080307031707 56
    0xd4400050b026a00000003844424040c1e00038151040c01c038034043c0500034103004d055213002102d50010f0b0201e0b2000804000b44490713402449481c1c4440c6403015581800303981e0041c4180c00074074034103281425240c4c5c204104100f601d1103000c2d084032813910350340b154104074030903038441d42e801d1000d00070030004501c41d00c1c0301051311f4581c601140c1685a051800e1600c9a2000c010380c401420310200307640c01c00c507408448109940741401c041ca4082d040c4154a441018146403610440c01d0f042094400c10030080095103922007003010111011020690303490714080c0c14400c0041d40c11448540c022844203000700c9428905400113104e20b00111001502201a24903440c091904020700140040651004c0316552400803204001ea0106080952800c0100300c140c0c002266021580745e5102c00038807450b032801d00d07029805805a05d0160608200740000181c0500380800621a02c0c0c2000c28a440303c03016007403034a401444040c2c1502d540340010f1030000c10b2200b22500201c40728815902082d400d9 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 625784424 1250 625783174 625783177
    0x70501021b010302030408130f17150c0a0306030b013f022e0309050d0809030307110a0507090903110609120c0102220f0b0309060601080601020f010516030b06 70
    0x54484140700c0e108102600045002c1d510040c810b441e2002e00308550300080d041c29590100400107030801c2107886040030807480b000e841c0040d0341080c2d9071244540000700e030b01c43d41d50705400a920b1003429503907000c56032040c3c005c0d05041d4005001c1e14a540000524a04040120100c01055062650000300c9145a43c010701a0103040201481c124155480050030300c9406c809801080c41c4100c40c0d1038015055400000e104601c048000030344542c4140104801040325110010050402a80a180901200d6600d0100620400410001408420007420b05014844000b0780150035200002d86035910070001c2c1c002c0c9081180000d50b1206a4103d5204c08038085002d0300d030440240c810403040007825074094100100c400202e543c20040c4c50305400031a5407940c91002d0004000707001031303e00199815a0714070b540c0b0125581c2800c00411a110901040f0958088002d00300080d142d00c0f0305004034900003c1c46405160f561030841401200c003a038400003c20300910359428400c0e00300010500180713 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 625785674 1250 625784424 625784443
    0x6051306080c01050c03070b01080c10080f06041e050103050606090609040807080711130e010f020a1b3e010e0916030216031107050105090604060809010f02040e060307050102 77
    0x26900142d281e4042d561080f00204240c00e50b0208507400d2082544402321414020b9100318255849540c00c07000c24100340d001c80381206003074100117089182c2080c88001c4660000c01c00b0f84655901c0307041080003c046002000340c0c0848600130001e42d81c5a00d080c0390340c1c040640e5124400d051820014080d0320300030f521503106a5121003820700344021640e40c812035420088040f02c0c494019100c0030210b0325080d000d03c0f0300300e1501c04042000c130741960025007100d4402c411550181d00400c4240d05050b04a100c0c020006802aa18001c003000d0742400c891150034031414030400c1441c0c1c030034520b4844200d080c0701c2000e078501c0f402e44200342042c401901c115044807041601301d1640800038204521512425019000c03600f40540342c001004100c00305149050300032000305810711504901c41e00c1c100640b9018004c2820300c90329120049002a5003802248502010840110300068191130b0079003081d850f601c0d100109541340c0361500e0030000018021640d09000384200c10000445605c00145030070f0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 625786924 1250 625785674 625785689
    0x604081915090314030709150509011e020703020f03030d060f08060c07031b1703010b121003020123210412080c030714040f08010b09100f053106051306 67
    0x20310704c3c541910240b1a00000c00280030f21a071124005480e580101000b9104112941d8030796a86003680e0015150000c1d108650341062100c8130309052540d00060303048240c0e40c048407020145120800000d2452150680903e401c81c18240300246550083c0e002201399030b00b04051b1851542c4100d8100501d000320b040c050006600601500308402c1d0352180a14180d01510101200c03400d000c60914141c0e0007a4062914583d0005141080400c103400e0075405c115050341400c51a0301d0341d00000d01082d4120300c0010315001d00441c1e42c1044541c1706c02c482100380e604aa4285003601080f000c1c01114003190192022001c81c0c5201411500ca960070901c01c001001c0410704507190101c007180d00d00e209034a03e4034501b00400c00840c4818800c91404014000140041103003400c900500510304006040071214a071404410302c050b0180c040d6100070341d003040e911161004042120354820150b4107a0400b8a051406818034941619030000c0c419130702e084e95801e21200c0030420780802c46041d03104d600c0 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 625788174 1250 625786924 625786937
    0xc020303093007060f290a05060f0a0917100513030c06020a0504240e0901060c1203021b06040203010b0a08030d051305060702010c090e012306040819150903 69
    0x941d0806008043c041c0d0b41e00420380003c1941e6502520000c440c0d07001040c0001548150802c4452480d05925000c4100161668034480303290401240490144100c52841a1004241400c0507031140100400071304103406000e500c843c01c1d5030307000e07180c00001e000c1030340380d034113000004640354540340d40c076044180e045e80c540c102c00b000ca0711164020341208107010100007003084009190703080740100481210902d500d480100320007090140c00c8044030020280039049910040110980018040380ca03990041c1c0041c043c840d10303140481c003d110b51040c401500d1440d0a854450910004070240709a109078020080107004e50100034045e0054841c00e1050b40c8200708009049540c0d402031030304040c107032030903501051090743c03100d046c100f00702d070180c0050f0b41d1280d03561246680003c1d01c100510300060011030300e5050203480e00d5000707080081c1c0b1220442d82d80c6100381c1500e0342e10440c0e008200034401c0e200445c01d0322440a003d401d80c540155950304180c0700401491009108500383c0d50780c5915000e = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 625789424 1250 625788174 625788253
    0x15050c18010c0c150503010509060d15050a1104090e0601080106051c020d0812040b06091005040e0c06030703020a0210060e1f0b0d05040204142202130c02030309 71
    0x110303240580b400c0d04480c2480d000d9400560014110030703501c9841c3c0151661078896040c01c0500050400040500784582e80c25100d1101085030104a1107400180300000320309965009403280280041c034012210000c2c00050019107140301d80e2080c000307000d8040503218903036a03403d0000e00340c070024080c05602c1030f0004440780c3c0c940200310303030516281d10261110420403806e031150300d0141c05c0a00d841c401c403070741c5c0400c100810000b070005036401982180e9030101c0d400e0044c01905640541c0c0111130051b0b503030340520301d00c0c2d25003084003c0040394010817113a600d2078041c030000d01030b4009628800143c490410703a104114054051030301524410007040720076950314110040b4621003220740c03801003059101e000c00d0400f0f40c44014441000901c801080740c5c107051041c841125a011905a001c20403202441081003600900300700031213001a2500d001c40d0107000003002d20659001c0300705650320b4001c02c0440c664000c40614030452000d400e90f400628088440140d44202d01446000381c02c4a8110 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 625790674 1250 625789424 625789427
    0xa03031d07060923270a02130902030408120408180306390c0a0308010512060415180b0105181b031801150302150408070b210415050c1801 61
    0x203514001e129403c10342d40e5a648a01180805030803100c032204509802105d15504d102601c15076400034501c00e000c510703082c05c014200c4030080d000e01401c0040c503000800700e418040b00000742d401c0143c54181c0c5ca0101e0400303140c80b80d51a071080b04045007a080b00624140e1603d001700e181d501c58080f4214500118608031640000c6561081044071001e0005d04590801e414417000340c41d207406020024905099a401c1c060b1140e94160300451051216082882d0105804180c05400540c070041800d0f145100c40c2e100c40180072900d08803042c8801140d2008148019000254101d17802a41c0b051240d0003008669503e8070003c0314070f0780c203080c4010040300705001c440e0025580721141ca0803406501c8002c450850079030b0000040c111018401020074015460030050565101000940a030700d07082c6060318550b2a035001b8882e2504c0c034480414800304800070b00014002c0c0d481e415041c2141841d0510389103418002440010301b800b80790400059410030200c04842c0584400300c0305000900d45d0000 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 625791924 1250 625790674 625790699
    0x5010f020a360f03150b030c040504290f0601080609070c301202250c0b0c030307140a1710030b150f0a030f1401020702030a03031d070609 61
    0x2098060031a003440c0c034442014030031a501001d06001200340f0500b40c07960400055103000880710041d85850507814445542d00024045424a016a40402c0507990740c28045604c0c40c2e14884191040d02d4607181141083e41c00182c01c0c4100036046040b144d54a41c8401155500d00c2180c10381e40205c0d103103000c00c0c40d10340100302c41500c4502c903140c030b80202c03403c0300c1a00d0307030541c060100a4075407503804d00200d2059800000300c442061041c1e030114141312001c2090b0815140e88248050641501160b0742e00f4068030100d40c0c4007070818400c03032503039400300040c42c16540d608c01c40f46d40740000d0944c6464859404440111a100b450079030720346aa09001d0711000d0505440076102c400c01020f8400000001036170001190302c0f600c94101c121841241103020f001180e51815942032058003440c0d014800a000000d6541405e5041600784500c1c12480c42c0c4c003402840340d006d000e0760520038142d102040551580080c2e652585075410049142d0b010b8a120340d907100180908400300e44405024444074001c000b = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 625793174 1250 625791924 625791977
    0x3050304170405043e18150708070215090f01030f180b010f060804080a080601020f010513231c050d0e030c120a020c0f1203031305010f020a 62
    0x141c00301d15107561240024100c48014070021180742400c071104220b4502c2107080c00d072001c0c283c6000798280303070200309805441c0700d49001041c2280801214076140d8071040c1e00d0f030b04540a030407807003a500c2526061802d86501f010804030300c1007a690b04960060607204080d6984030300090107440704d804c107140064001e091844540084195a05521111280810078a1886038002c0056418650420243c8562441185c04c040203110482c024840007400110845603031004a1a003241e16841e035400407818071400554800003503080c6001d00031100030145528600344d22070003d03000c40d003400304140e40d2010514192014103821181c000c80c100500c0050a0081a440d8907005141483c1700c80b08200301e5400415000c5194404283c010645a00f00101404c0000582a035070602e801407034000d50f203c0e02900014021040300d504003429840d0401d65a00745e0710601c064a03224500500c6c0740c1082142940240ca440d82010000c0440d0719052003226014141551600c0d010109022021203c19044 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 625794424 1250 625793174 625793213
    0xa0501080d0c0f0f15050a0c273528050a03120e0d090e090610061101020d1a031b030c0108060d0204050906070306050907050304030c0510060803040f0b030403050304 73
    0x800d9000c807103069074406c50384194221800010700b81c0f100c2000070644018825050500c1c07e2007010115140381c4009054101ca00b88002104507504200903100c1200b11030082c6607002c00c1c040101941990046800c090010a4401c0d8803696000002c0f42d0000514604010303181c0e030000e55001010a103e1442181c2824002c039012440c882e00b01211850030820004070b2000502a0405200d080c45105a864100e240c010080140c3d00b842114411000620310440c414403200917000004078200390107480400e22100340030051801402404040540e15010741842405500c40442e201003442c03194200c01c001c05030080100c03528440056a044070050102c03070340300d40d005040d03e0060f640e600401d0302c1001d4007000f810752814180d00c05003e8400c41d40041c0d10a200b1001002011548901520390094052800d0030f194407041c20306a08000401602c0409142810000300302c00000100400072505051000201c403903440c10052000e00099400400080f402c00108001c105440c2404030201c800 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 625795674 1250 625794424 625794443
    0x60711030a1211060f010e0c03180106060f1106090c010c1703070c030909060506090d06090506010b130f0b040b0702060c03040f090624030509010908030a0501080d0c0f0f 75
    0x16225000d0020710712030b81c030b00001c0074401d64442210b8103004a0703070001e004505111255040080d68950490f0060841d415500040300080f80c40301c1d080c90403151070519030001c01a01d1344a1000606d04070312001c810300440c1040032001c000600001c2c1083c1704000980280c440441200300440b00000741d900241c6131a203620030081da1119203c00194050203d40d1150300d008001ca15014180c9625503202e40c80e0645450001c006e45e07102c036011115210b108440991503003055280281c0104119040540144248000412008190802050b918040c021282d082c41d54030071911415022600440b041d0403800c0c442003042d04000c802901c6510305c01481c82d030400441c2250603245400540c400c0007504c0e031281c000c002448840c8980d10103080c0b00841040040b4811003807820703005000381c58004141e0b680c000104000800c0d449810310716442030b9180d039642800882d1401a00081c00307035a05501032000c80496030b50003607980200312540b00300c0c844440780894072480c44c01d080c490b605440b00802c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 625796924 1250 625795674 625795693
    0x15010e06090f0f0d051c0305010b070c05010507083006060c071a040308030a0b011b050a0b0c190203030f011509120602041a180405012303121315090506071103 70
    0xd0903c46c03020440b0b410a030140c3d0958a02c0001415510103a100700043c080410461000c00d0b4000e5254090754400e00701140c0d0380b0038500e0039109034460070040b00079600c2405041092042401c28054104100d035090f0200da444100401601e0300c2524000e004a42c0f20820801615013140f241030340303801c234030320000341040c2d078a491b045990340c81224000040707035817003050b410951703005a52440101400c05510025a4150b0340301c0342e0300c4000c01005072205945500280c4800e20a20464100c545031154100c050f00c00d00707002075600d030019944480d50400705d03800030503501001002d031181da0340550303103008060f441e08404000510000b181aa031480e020007002c554500030a02f02c2d4990000c18a81d1541c030507801030510314443d11001101d2145040c4401001155100e168041002c0250b03e14040c40a15134000241741c40d01000407100d403098041131f00118020b0601c0b0036011074544000f070b11000005c003031040707c046106008807a0b0000c414010071020448040324200003481c050304840d82d852 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 625798174 1250 625796924 625796933
    0x10170a0609170c0d090608160e12030c0a150e03120717010e24010207180209040f05061302070807030c020301140408040f0602160605070f060515010e06090f0f0d 71
    0x9100f503105180c59030010070004241a400b4265400130003040c1792403450740c1483e41d070685036034240302c0901c020402c8859904216540c0d442100b0f85001444080741c0c0d80d12541c4000c00e07100c0000042c181d540703c2280364005500481030140844402455001e540351000b4080803540e1510b02410340810407a030003110b4451042801050342c06821080120310071840e00c00c1c802e1080ca1042e4440000d14604544502840d076000a68038050b00c0c95160f26295481210240000a000d00001d095000f42008144050544164081406040c00740c0780602c4176189580c1e54000c0c1d204000004100034402c00c004030100703100b0000d92544a01c010004240e42c1d00c19030085550b04003e80d0b00b612070000001d0104441850f10b00c00200500c250b001030480c181805c038541007801821320601d8140a0300003030820810110b8107014034500c4c0d02050030001800c3c0110001c1c44c00300c00e071403503038007140d45401c0885644c40e14601313498400c980100000740e83c5c0010000d00c074944211507481c640142c41d1407402800035 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 625799424 1250 625798174 625798177
    0x201200601080601170d0e010e180c0309011506080114060d050f070216030302071206021615060506090d1b0b0d02131202010c140a02040e0610170a060917 68
    0x3082d00c80010529035041c4a540e03070040000880301c000c60b80c08a51b840304c025400940350010102d00f402c20713018492100740032a01c0981d00f11050042c00e4012001c108107010420040e501484004000b0401d5822046141c112000140203502c041905071004101004e003036040e90040c07880203492141004600e02d603c405442c000d07106003a004075030b1810850030950400001c0c42241e50b59004014291031920044c0d101d2015000d2494800342e42c8096405020082c0c04841c0485801d81c1c1c113034411045428819081001c4035680003640b0705011001071245021030940d00100801024481c003005190f840c03a9206260a10940790650381c24800106642200301602000198140159440c9000001e12204a0080d00180001d284a548400260344c0c03160300300e800d01ea800300e003120442c045516654603102201e40c00030340c8581030140c2800703d42e0001c2151400340e200040c030420182c4e02d4030a1004400c00c540003000301070f40326490710004541c40f40c2100741e0180c0038015160207002d00d4400d800c1c95 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 625800674 1250 625799424 625799429
    0x512040f02150f09010507021f0c06051e06060c330c030408070212070b030a0f0c020d02030f0a032403020102060906040302060f0c09040c1d120a0201200601 69
    0x1034011186949055050412000301600d450307400e2240392980e160050012805a1200c4030b042240220304401151034402c03004200b50303600804106640ca50000003040010b1014048a00608104c0426426403070445506480f602c80c0800000e80d54400041c030010b40c202d546d0042c41d501c03400301c41d00240c8440e51945142105108100e500030703001e410038440c1c86503014006140480c2e0070402c0201007001e801c1680e1846a044407410811100344a1107490001581c101e00c0c1c0d5100000240500070419520126114030310450500c1080c22004c000d80e110704600e1408005608100050300b21621084024a001041030a002800c09241d5540301800814652686046030550303c081c0300f59a010000302d68040440001050f4a1820759002034a80302c010b420091898588008101c0c0d042080060700c907403200c068020010f40d01a0a001404070108001e2a0300400c034ac1021035a45081056124a800300410000c1104684603401110202d900d1400100c0c100005228544200c000b402003600 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 625801924 1250 625800674 625800683
    0x610120f020a0f020a1a0903070501140403030b0148050d030b0901270204051003050106110c06040b0c03070f08090a060912022103160b0915011203051204 68
    0x80360360a494001e4071001030303e5110000e65000c0204100080e4a50040700c5845940c1c803066102500c945003054950b015042d4000d0140d42445055174203044200800c0340308902a039014480345440e8801540c0c1e035400344000c15a0790a070106c0d0b100711020f405459040e0701b10100702402d440e00000d03e1095245d11401c5044a041c1c0282140707a5205505010b042d42c0031070f040f602c62074154944641c00c0502c0003245060308920203800c0b001e082e09400e41d81606c0003060f015080000c0d0101034507001740200300c01d02078540415084000340807a4180085c107031640e01d2014221520b410f00380b00c00c98106402c0101e1880b00c07880100f2501000540180c1c020740c0d21440307081d10350f403a5030542c0d0821262560715004001040b0184600b0002c03a450318024540c8941c0550702d04403201a421402512030b81d09014181443c440001c44944084014100880c458010f5044400b83d84408140b541c0310349894080c603401c0892800107000344482ca840c0e414041d40300b0309150b40740a0242c4098200e958007242e0655 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 625803174 1250 625801924 625801927
    0x303041704080d030c1202040314210708160f03110d1d040c09210c0806061807110706050306240a031a03031303020112050f0610120f02 60
    0x20012003032503540640500144441c20541005102651512000c5200c0201900d50803070b01600b44c0908050400a0318031101903541d10388030309051020b880740b81a400401d1060aa49501000c0800303000000710300d181d8111fa01e081792a1f00c03600c40c80c2e0804009140d06500448400c00000c0c01c800c41d110f4958403d40b5104d0100c6042d044090a00a140803600d040c020781810302d00714100c80e441d035651908011070700021102031503801213901a04039080b801518800c3c50710043d040f080420002070782449508a5000c06172200134290f01c0d21016507540750007400348401040c01c020a00303810b46c0c2c03045507854040b0040c9034554480d46000d100d80c0c4000f0101d400081070200c1130900c003041e002c02609403103060391081e001d0401000d061103000450410160703691b07480d0030300c036259400c0c6103d0480010208c9881303074214003101c0301c80f14203071008074082f80580a00b102c2000190050510500b0414040c04c1655036080501040e5042140c50b00c041000c4104488240c040750700c21512003022400c0c005 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 625804424 1250 625803174 625803181
    0x210c0c12060f070f080a2a020c030c030304141002031c021e070f03050a0c020d15141302010813060e06040c0b131a12010b0315041a0d03120e0303 64
    0x140c802d1202409020402c08007151500d502030700b100c1003030740006605a000500c00b00c01e203008021030f2400e00401c2d090030303007101c28902d0302c1781d0004460050383e40407000c1e220510a100704142d5648a24030900d403003035080c081624141e00d007a404064282c58680156854482c03502204054865121800c2c2e41503039020802942c4184104114042001d44484440c80e00803103445001c1610743c181c5004040010004160741440d108444540009602904519090740b152410b035000c1d00f03c50300706c403151034503002071018980ca00040c0c890040036104d007201403848854004441c0c407500144107411105c040010580003e85620401504003001005491542000d1818001841e40e0758082c4400b5481401098907503204247c0171021912011011100c01c5015a500c0e01c83d030180c0c402410008842c21300024401c40c00c4c000840c842d5134801c48840c900ba0803501008115103c4e0b480000c10300c030720f10042a185040015071200d1040c001c0c10110312000c4000c184000780d4032759810b032401c0e6810100c1030 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 625805674 1250 625804424 625804441
    0xb010306050a2c16090207050d030b01090608220812010e090723030a050f060703150e07031508010b01080c0702030a08221511210c0c1206 61
    0xc0d190040500503081c02541035000c51401001010031041d1103203c40590340e10401c00c1e081160350904100c1c100d44103150359a80720210029004000140c03410b0061800360401c0b02e03c64841c201071180140c445806603800d1050071514028000d107001d03d0303d0358004541800a840e1b810305807150344214a4550f0310070000c0c282e0947c43d00180e00501a4015450500101000c0400c1d80420380d200d00207480c80d4001c40303200c0318203480d8101c050b481e01030054183c4401806000704010044540060032988103844040302101165006082d07505031718059036007800110f00181e07485030014114030300401c0c0444d28241100c6000020b82c0021204d80d0340d03901d500c40703d50300b20442d240e220504548007400c1c58076940200307882c0c1072414030041c60f480000400d155010700035442960109000e0380107030701c45921181e003403030609170b00039010004c95400c002401d540c000000d0300000254402a00e010704100070480b030f60711a04210b0100c0c079240aa01d4481700c00c1d4031810303050340a04480c84010426810000403 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 625806924 1250 625805674 625805681
    0x60b0403140c10050306191701050115080708041203020d1406010201060b0c1902120303073b0f22020421050303010b0d0603051501090e2a0105090901030b010306 71
    0x102c180188003e0308826500b94100084d02e901140c190360b821070f10681081c3d0a41b0b400b00c00d03000b03100c0380c3c4078504403440d84440c1540035506075400030504040b0014182400e442112046890000040c94100050009411795141940d0307200c8604000d42000c81140c0c526081d1080941001802080301040048660303090040303100900b4441d6519284c010080c02c2141c50b5980c0349404051b91030b219009800b15101d04940048844c02c5e1404c0c0c035101d0030100ca004041f52521591100c419184140f41075400c01d682c0148410040c3c5100b007400400c8100c0280290010b003200c119502600c2c0e201044048807400401c0100c0d03059041005a81d941800d5101c01c0b004840440310b0f00a40043c848800011400402c582c10350b00e0210f85681c070303681c4203610b030001340c2460f810083c428004d140e16401d2660201d400c2c14182c510b0309034140940403140201a503a4100303004801c0305940c008070b0042e0b116202010302a89000180741291518004401145140f0700030707402215005400401007051022620 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 625808174 1250 625806924 625806943
    0x313050706090b091203040e0a02090301110c2d0f010506030f070612020d0204050a0b190206100e06210304090e0c0a0504021315050d05060a030201080c0d060b040314 73
    0x10032400c503604080003c1c480d4040d40d02403900401d140081080003010401c2910001c1c6010ba05074107080c80c0c510425400394105041e01802503081484004081c0501020356030503298000051200d00c0c1681140c130840d6200d40e40019542c02c0454200c48034200511003080303989103240010903c2d08140050610742298440c01180903046281c0502c40d4583c00b2450b403030007160410380581c0302c8001403044c1009206c4c83d030005a0000042c2c2c0009082c9801c1d00c0070304103602c20038140320004841c4040c00d07a01e403081180e90740380403900448103228803c500e0400c15040741000d450303c0d003082c1c510719540d0350080440a850f42c2c00e50000c00c0412070001d00c0d001d41510340c12040c0181040e43d9141c0082040c01d03c090044510403900450300cc10000032902a03a0000c10064100c0702010510640160040d070129000388001c900301000945a07007043c003845002c0380d9040c3e40e103120550f18644c1b9509503030003004003c00b210340c440c0720016960025030043c102650107444032040e0b202e032a404440c030f40f00088 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 625809424 1250 625808174 625808177
    0x30603051b010914060a3606170108060601031e0507020a1b0b0a0c030507021f03060914070302031f061707080f07030c0203090303041e05010212090f04110313050706 73
    0x184e05101c064079810103a401c54042804c0004800f80105003d07010301010054460103201c0340f8070340104072a07180700f50404407040e50b1503041c05100620168040701109008034101c0b41c0c400b0011415551180e446a100840107140b01c1c800d5a1006004400f80c500039940d02005a124011001c140a40c044a45441c015042c00424030603281401044060050342c088600748842c8540500500d07004400f210550383c0e00400d04000da040d0f0104030302c504089400d10500184c0303000350101b106116445003004000b054a41d00782e042d52808421006907000a00002808601020341892584412a80d50140c000d64952080e8030404070018600e51074002d15a00c00c10a296003400351001303542000d250003225a16011549420724502a444e51003496220741e0184030024000501e001d00d10b40717215070f4124083c040d02c220f0359074600490340d8010002105070200c008000304a014038000500c1104c0560252001ca840e41c282e8103d003280c0d800440e03000a10600e0b850340c0710304126041c000380b400f80055 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 625810674 1250 625809424 625809449
    0x30b090118050703121103030a14090106060203030f0619080106051c0b061513090b0a06020a0302062d0a0c0207060306140618090c0a11120d020307030603051b0109 72
    0xa5440349582e900f864030000d01802080254488194400c000300c15a10f01c441044035a20305081c000c2d0801085052a01000103440d00f0100d90380407018024070089442d0740d401503007551600702643c000c07604050641940448208a030b82e1000001001c0072004140f400000150f00b80343ca400d104850000800c03211050380c1d144e0b100d00c0000c0461071f8842d00818196440320342001d0172070b9a0800c620445903400c45d29244139200040d650b2044e0000c40c02e1280903544c03420040da6684d4142d1b65450003000040140e0030001c0011500c6042c80d0308604451040340d04401814003c0b041c142010106403062391a4070b4a40c80b600f001c2980410030100104564602008003900d022103031410a0858603a9901c149030019000d1990368980d07884d0054600d0041540e41c150504941070043c81d4000d00810303021a0080075403090004010860750800e0f2112141c01e0305d00300b8141103400081d40018424420705a9504010010510130040850b0301080c0304080c0c082c1711088030014089003056030003141d0b00d042 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 625811924 1250 625810674 625810721
    0x504020607030813060f0608120301082104050a0e1e0403080a1113121401020901080412030e0d0905190b09010503042102240402030a0b06030115030b0901 68
    0x3600d404a885494041c0f4142d1500c0c0c859910b1340850402521003d001d01e41040c55003842500103512480444029208503400c40042c0100390109020901c6420080d4100c06121244541c41e5440300d0f80c075075603506110340313841d45400024907210000e8200c3c50000d000c00c01041f08012203003105260001c416490310303400e454907980040c4400f10041030741045540786c01c0f4007598140710a0954020032078080d00013482a40f1282912502d003001d20080e079080c1c005081a020140061089401e110310603911001c1c560b85940701d20307000e01800041c0d03004052381e403100020b01d00002c0c81035043c00300c01c6988032030b00289083c0030800030207c00c241036841c5224075a01080711201d260f0458401c0d510a0900c9616981c0e581400440d0f02e5035a00b41003c40c4005c120415001c6901081900a0780a800700b91450300b252405024108101102c000790503500c90a03440c0082401031610380c2d4400030060010400c000b280d001040070003420303070013214004c00c81c0061051011080c0680c2c2c40410407840440300804 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 625813174 1250 625811924 625811929
    0xd05060c1c020c280f050a050c120c0f0105070501020c0705040606031107020d051c080415060e0a0509210904180b04110d0618031103190e0d020d05150a050402 70
    0x250307a41c1c5040003c4000d00c0c070825500741100131912201c0c1c3c029045070074449041c02c215858107420381381112a80685507008441d403424491402003582180010840c298082d01403144080700c1440c41c40c10300005008040c0020805d00003042200a4030000e81040e81c640307010300003900c1e080c0d04620245410068031241c024044415680d5158040380c0958807070b007440c28000c0c104508903610f03458809060764010724041c0c2101040d8000e500c500a024038000d010842a0100d55060180321610342c1710384041444030607076030403464219403008103641111001d4150448000980c0040300340010010440b440103150600c209071441e5401503625100e005140c2e59032074800001030004204410128140106031522071003002250340c03240d42004282501015210b000400d16000c400252100c110074011400c003100b81c408034001030074090b5508d5160f800a43c1d03c21240c25001c0c0c3c00c598400e02950242c1d4801184a140d54003410186c55011181e01ca641507a110041c0211422400c140500c00181c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 625814424 1250 625813174 625813183
    0x80d0302160f060b09180d08190501030503360118260f010b0906061308030301090506190602060a0209030114040602030115020f0d1110060915050108150d020d05060c1c020c 76
    0x700340c6000d214650300c0c551a842c09c07881f0201c0203411545800000700410000000030001822041410511a0404064110f411560090010021960714003141495000300e00110354403589101031140c0c0d5454003040d0034001d50307415040140503a9030907a170b00e07001000d1065102c00c003050802446658820300201d510b0b900c01401450141d02c0009002114144802c6180007800069065035904d5035100e00b0840a0502910305030f210726200d16500c641040020070600441d030040e0098660f55a600d5800300c001d40210f4039640c0c043d5200c1d8500c0405403000000107228900c100300050700d03941441e40000303402ca43c6030034081c10b5504c803140d069104140060710341c1205035546440d240140c0d050303481d9070a0440100c01c2d820040d0030900302240303c40440c2c2050a42e44a00040f02d8002d96660004482205064400413a03003008808403101c542426854078840307600160010070b410a1940e12035180880c00c0300e0403140740b000455000c42907420703999031401c0313800440e174250b080c103402d43d410a484 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 625815674 1250 625814424 625814443
    0x100515030609150604031208070e01020d0914132c12070b07030608030a1d0d0b041103030721020705090105090f07030b0d0605060a060306080d0302160f060b0918 71
    0x1c040c4850083c5009030303601c00c2140e003e035622048103441c0a00005001c0e2030014152031078408640006030103d0954400543c480c0158201c0d6104040c0c140307046400000c0802d074500d001d42115840d48480301450b064012001e064284080b06148410619805081d0715100000360f034040c1c12130f02c040c0c14510402c5013568001c030b801000070b0b01507807079a15041e00202507a5002119502020800b0118140c20200c2112204911501800810002c10030002c031101c0c03125000b0040d0241b00d01080126922280d0000ca2078400f030101c9140c0680c903240c1d000b0807140c0200e600c0700b0100407010f5a45a0f54180040b00007840203850107015941003500207185800c00500041c01d0041c0310000800b084d200ea00031000c3d1510246c856481401c140c101b00000d0201103c500e405089446400984a88244a46400c039042d00000d0103490441d02e40071404ad61154001440841c10054414080b441c1c89a001140602c00e40000556030100300522100640003000300c0d5480200c0c0c4114a210007020a020b809c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 625816924 1250 625815674 625815691
    0xa022107090b2b02041d0d120902090c03011e03110405040c05060c160e01060e010c0f08030c070605070c3201051e150604090216020405100515030609 66
    0x28141492004540c00c089032004601d400003003031603141011a1481030803807503c0d00980e02484040144c1c4040300d1011b4a416005255900c60340c0005041ea210f960203107041e40c815100418504c040e900080c80c4110b003510300003400d05001004025a02c115a810003040721041c031540d051528640303c45042c150324400150180b51a01c00103810002c8555486028141c028051a111440c101d05103139586a407a04105041039041d0000c24441c109002c41c0c0d04179130403a42c40408001180004560080840e03200b01d92802c044a16100001d60f050091172140cec40070009a515200207041650a8503000713003883c814802000030140c00324107040c1168600094201e4010000b0101940c0c034003500c034000203400c009518201c00c2c0f01141e19030814107505c034086c80d038241c0307015103900208041480d8111129507200500300300030801c4d1800e40d005008070360f12500811468041030340106003039076000c43e411688110402001d00003841d14001c100403001200100c6411807030440d002c01e1080c4800741000c030 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 625818174 1250 625816924 625816931
    0x3050903030d0516021009260d05010b190c030801032402030f060316290903150603061f03080306030c1906120207031b050c03010207050a02210709 65
    0x104192010012a80001c50b00c100c20021403501000456085080c40d0000006000320042c1060001d43da0188500064000c0c8542e1101007a201d80c52030b20082c41300321400314803014006141d4014141c480e4500a2404005146d5242042c00c0e01c401814440104141440072003d5183c001ca54060f94803815039510611389001038000c19440034005801d1010324a80600001c20000d0780c01201c01046d024103010780840d003501c611042d102c40c211301c139400b0351402850107041410b2420804482c2400d48901087c1803464940039101090a003103088105003d4400711905201a0741020406940d20142c040415000c611001c40212115180392201038900d09003c00819001d03a428040ba81d03003c640200040d0a81140d207100035132602032031041c500481c035007401881806180703000300e071541940340c0d4131a028160004001031500603407000070368003442003200e800741640342440102034260241005110a855a00c10444d01843c91900c1080c085041c0703d001001c62030004000c8140c0340c00c3c00010 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 625819424 1250 625818174 625818187
    0xe0108190501020f07230c03030f090f0907021c032705030409021201080c040c0905210706020c0f0d0f020108040305070c03030801090b042c030d11210c070305 70
    0xd8064000d4810400a80000003541c0d41041710401c4001e2001b1400400686e4060345a160240c8440c003030308806405401c00c014404015000f0401400c0c400c000800c814140e8409001103032849a0469050000d0b03840010b52844040390265031a05602c00c1c0d02d01031202d90120b12086201400300034403107081440a44000c420480b00303000740c40140548075000c545500e145009401540020700c9006074502a075030301400d103070819000e441101000c44c0c5038200300601e000d050001ca9031a51003072540c01c0c071005940ca0703181c19040c0310b80d50080226a0080c03080f0071481c42003095540201d00030700e1086202021000c0029144e810792030b0910740908005031603a0b180d04043d1002c0c86840c500070301d2181c600d40088101034200482a0507216070a20410040b1010300070300c42100c100b43e01488040c0d140300048144242c0e2600559600350080301900d091041190fa0b0100f074960306140241c0780c03000810700c0d041d582080c610070710400703030f4038207107030f9540c0c105100325a0080c030441c48050101b1170000780a = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 625820674 1250 625819424 625819433
    0x309010c1e0602090a0801060b070b0a0f0c0e01030c0c0b0711190305031b1206060c030f03040b15060a0504050f0f12071a250201021e0d03060e010819 66
    0x2585084080c80110704211500c0d0140013903100c0503800344522007139140810445014070400c401d440210b05440c0c9021403580301e581c02c2110041951901540751007400f941c0103030a005140e010400340d254044280b51000015096641071764907101000a08070412010603904078001d40c0105840c00c100500c0c0000c54041c600b8a10320a0181e002c00c40710400c0c42c410968840002d620980900c1c00080140c2c07030004940646115282d00c007401e1041c1c0300082000c038540305008008082c0c0b480c040b00d10b48455400e5071460354004907070075200342c0340480030402d80d88048108000d060340211a61441c003814140054518020350042c10300401340900030034520b0312040d4103010759175030003082030705024007400d00c0940d9400907015604150f00f88000c18503004000e402580c07805042e2000005030280042c542c82c00b4405008000d038110712a81010a81080305680c00006100050000d05154003a00303801805031007042d0f211050301ca0000e001000000400709500c4042e20304408007400700151800d2 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 625821924 1250 625820674 625820693
    0x23610121e02041b02070905011502150921042408070c0f060f050603010605010f090303180e040c080c010e01142b0209030705040b030d0c060e1b0405090705030309010c 74
    0x1c2100c04d80890a005002c1c0a4000410a044800000d010f208581c3ca40f514089100c166000070005070f48840f95243c000303040070701c840e0307441a621404c552100c600c281c1803264044032030040849020001805020800c2c1c0c100c4586c0c42090589007282c4520640c0c030005101c00c100070304e118200081c18503800f04022154207448001c5402040034001d544012000100805080d112a44250300c0c007a0b00007443c0d40141184410700b1441d072100d80c142c5142d61400d8401d01742016080c0340170201c00c00082409400001f091340900e000f9a205910070781840c00c00e0303250030714101c003031414003e45544600144e079028941c420480b82049917640c60300010440c4003c01d48195240c65426854850100501d1580c5d03800f402c0b075850110200d94149559005000840707042002c91509500b104a0342130205001d000c0070416244030b0080004c0300003110403044e040682601c01603100582010404178075203414042d507600000342c000036150341c40c46c182c00681d40344114035015050040d4020070400f40002c01d03c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 625823174 1250 625821924 625821941
    0xd050a06020d020301080105130210030c090b07050304031a010b1920011a0103050411060304020111031603090503030307020706031a0405191413023610121e0204 71
    0x29019034840404000e10000f0350000d01500c201c642c40d010004d00e055491500500c0141c0c0c02034030030851400c941c1411006001c55070519000d0100f801800513a41100300001c12040303000e0307405180c40e0790035850000c03042e00500d5440500070305002d005005440146003169541b1001003c0d201004a0081060b180c104001d0b051a400761031188040394418010740000b28030044002d600749400b8141c0c0c00640454400b40c8005c0e20310f240000d1070500c00c1c204140255042401414146c29010784041468910383c0305056407e00746034803544400815070802040e0010b40b00442c040e50451810840c002d5480e40e151081c00109926030407a201c800c0c080c580c80ca040000c01034014826450044110514045001009880f00e407520040e03040a4100d8070400340141368050040102111035020050134075034203c9003000c03940410a20492403542e1070001c8028031108180c284161078800c00219030002c82d41d00c4130760000c40710802e0b100080e414088010002c1001d441141683c032040c0049002480c0c5134 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 625824424 1250 625823174 625823183
    0x303060302040212010f06110307022704031107050402070503030610090801020d06140901030201170a0f06080d021b0120010917030a15050a090e010e0d030c09050f0f0d050a 76
    0xc00035144ca215030380344e505841c6200e81070000c00d80c1e1810111201c011000c00b42250390010702c450001403401a07030000c1d901600207070b502c40522680380324043c100d400762011004200324212444001c04280103181c01848116021414990307980c440607240e1000400e02031040d050a11040011401180590082c00c036142c000c64031881103001c484002c00c0c5a015010361500407030001c40140c81d0020400341a00d9040c0d6a035042c410200038408a0100040c01c000d80c0740307407601a5525603a0140c03041c5e50082c0520310041c201d0720128038000c0d0034030b11000c501c03100d40d40150f5002540c69030003003040b80d20740504252a54510000110590040000100c010814a4450300303a207a458094070280d8061040c0c9901040004501c1141c0c280510443c032960350408141c032810000d0b000d0b15401800e1001c00000041000183e11003414241050307510000c0100b81d6035a051074180d64040303112000b9045c10f4810000c90b48618000519032100341d50041d200d240004220b404009060283c126075a032b00 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 625825674 1250 625824424 625824427
    0x6040309090b0d1415061f35041b210f0b04050a0b090d1b020d0f030909200403060b150304060203010e15010804060507020a051f051f0b0703030603020402 68
    0x110254503403286a100c1c44905060042c07404503500d8685265a030f10543c103a103078004115640341c0c80540b003c2c03902e000c0b0109202400500201d08d04605000101d915444181c65800780c640752829550700082140c801c0001c08084005125580c5500b035030407600d0b071035072480c080c03400c0c079501d0302a0180e0340420004200710481c0090000f0810f0018001c5207452181c16198a565a8491802d545802080100700000d00c075800c0e940011001541c0000c40380e0010700000c43e1041c16884960b8400c0c880d550482c00908241003c11191249110b503410401080081c5040f65a05800042075402103000107098155200065016940c130248058251041215055101d1405040c160001e400174400ca10720441c0c10000200503050760b50f5440b90900d4141c403148072580b43c030384880c0001c0c24000c0000c03040d88605031103d00480c0040000105034801180400410b0b40d10050790020340708090034100404103098120710480481e001990161069091019166800d41c103084015000710351010303412510 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 625826924 1250 625825674 625825703
    0x140a1b270f060806060f0706090201030209030f0c0301240b03060117100906090c02030d050402030c1804150b03120d020409020301180c1b020f0f03120409050906040309090b0d 77
    0x1070348140c0340454085031540082d0b66034480502810b40720703129035900c5e03500040001c2c0000541903441400e2050041c034005003003080490100e454665114540000d561190300001c410381350901605507950214484e1400e080300035920305501c101d030b90082010000001c000104242d110b02040a0b031f1200c141e4400009043c150540c0c80d010000c0d01a9031101810035801260515043c020740d110710440f50b000314a02100b20010710020040540202c0e80340c000c20500152a43d103001c16550113000f140310420803070800e40b80100c0c4a401600790203120508000139012555408140c00ca15405104901a61030000d490580000d03c07942e0412001248080000304244117a011030350003040c994a4208040710940009598000c00c600381c40e00810f48801c1c0e403900508081c0b00d183c20319000035001c52102007628001a04285942c034210591307010204007001344982d54080d06030070082c100017525580c02c040c2c40c001c00b590210f024a1007510340302c3c00c0c41c06098440c03074811000c4540085a0755000b82 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 625828174 1250 625826924 625826939
    0x91503050a020d050127110a0c230709180515090a02030601170d30060b0307080915060f010503070c050d020f0f0c061209070e0a140a1b27 61
    0xf000d1900c110540d40609002610618003449089944004035002d141014043d110465084561880460f0b0703004180c07182c0f00035002b0100f00480300300d902c800580305240c10a0341d00e40845800c203e400b440171110389001408160b0200d03812030f007015140e07440041940d82c1000946000d40d010300027905445414000203220081e040c807590601e140701c0568208c4e4080e1441125055020906442003980341000b5201000c88083c80101c0741c0840140414800d82e203400225041d002100d241020034020800c00108980501c00e00001c405501100c6090303080000104c1c602c2d070300b20081141030080010104245900a0411b17851280c0d000e8100e0300c1810b030703501c0e0081d00c414845103e41010300c100304490441d81404500301184140203006a424a4640c2010419400026003022440d010700c03000800e13005813094000344030360444c40011074039040d2224040407200c80104030a400c2071819000d0400e41101e40a20039000c041c030700d000300d544880341c60841c9002050703194510b142d00f188800041c0c0304 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 625829424 1250 625828174 625828199
    0x5060f0408100207021f1e180b1b0a0b04030e0a180b0405060d0510110909090a1b1202090405010605100309170906030a020d09080d091101091503050a020d0501 70
    0x4900c203440106c07070021900015141c98000001100c0810603003036521568030b1003420303420b0260102c1e15048a0000b04283c0e00d5461140d141c1208100e020001140c00750218a441646c80700790140000307020f00642d07500c07607904035400900700404004010480042ca6074510061601418685000c0c800750144c0b00004c1008152048002e40074a0a000000d05d1a00e000580029800c2e007203400b414443d1600e0720030400030000c2820380d216110041c800c0d0261501c2d401c07046880344a0f00d1008000d2804282820301e15486504948882042a40020300105c10b0a610329603625906554011445c2c9951400c075014007100d401441d08103d42c14080d03200c00e5455044244d085006001c01000703814003400383c0b1911f03c07800b401d0b55007041d4200b0200d00410610350003440329840500340007844550664500f41e039a4040c8001c905a0798842c501c280512100c098625030b180c900b42031440c50146041031110b130781d4a880e10703a20285641ca000040a44005404035003a00079040010852076031034210680700c4 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 625830674 1250 625829424 625829437
    0x1b02040624030b0f0f060708040f1814070504060e0111060c0d0e0606091303020114041a06010807021f02040e0f01030507060315030b0c090a030b010503101505060f04081002 76
    0xa060190f08840d40c10b00640c50b802000340030307040500c2c45042101740041c0340c0c0450001c542c440c2c800c05c030010340b12400070820000303401d080e00c0e81200301ea00352451409403000c0c414020400054101400202c98000d401c41c1c2c1280c4440c1000002580d03140011784441507484050b80303c0380200001c0021040817000204404d142000e03080150190b024121940da144c11514281c1005580c0042100300d02100003950703007140b103440040355802040940000c002d1040c0d0781260442e10000200750030310010030300300f0f500840a1038120140d10304414025540c15002c50782c09129070740300010b030074910050340464024140c960014419410301c1205d41c0d4203880244400e079101e00408401240e01b0b403003405814a8091201042d240c4242591580d990701e9002030440d1102110030010842d03103840d00303907040005500812000352958504010b04d4102070051000c4201d4915021007142949802c4104000303844058a28644030009056110040d102c0c60300940349922a001d00e0011a40341d68004260 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 625831924 1250 625830674 625830677
    0x703140c032703071704090e0604060f140a0507050f130905010819240504050604060606050a1706010c0519030906080411102703021f1b02040624 64
    0x19540c0207200460002c00c284000305038241c10402002002c20403a058082c02c160403500b011b498580d54440001c2107032a0355494038015003042c001c200038007550f1710039200030004002051004991881d566101e040d001045000c4003541c07180031078443c40c420010780310300c5503a0030780d4240d0f100c0601070401441032852044500d1a410100085a4801c002c034000825140b500c0f03101c0b0f41d06600341d660998818a0b0042c2828441e80080d24001c00c5083d4051940101d00a0014092506090401c00140d40f1540c12407010b004081114032181680901c101a0f07036102014200c816031200001210b2064005901420921410f030030100d0302c104094034820a03078842d8031240050741c2d607070300196942c501c103d90240c01500c1030350006410342001105520f6500303903413801ca000c0840406031503d1069102401c851109a211020b1045080803000e410312100c0c0302c801d060045124001c0100100c2180a610501c200c28201034021900d903074000030040c10040714000e00c0c1c070500d80d03803585c10104290001e00 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 625833174 1250 625831924 625831951
    0x30d110c070602030f07080d1e02070b01080303090a0b0411030303010617062416021201060e060402030f04021018090b0102241f0f03080909090304120b0703140c03 72
    0x364903000208039040d6179411094581420956103071001c8581150041440f00d9888080100d01c05558020040500301c11400058851465007003943c000e200513041708050394810802e210310f00400141c45c02c54940d0282080c0300a607954034213421002011451160144070203c0081103640d040341c51011044082001d11415507a00403c00c4401903250703c003800d900d080c810340040c00303942c20b0b401056807002c084400308009040740e01003491014400a611121795582000b4420881c10746665a0881c3d0308580c15030035814080c01c007080c981801391009104481d00c1d0002582c1c280100f070340c6992010f407088400d5486655006c03c90151186c404034500500814504001540e07840d640410850164000c40030f260703445418050034140d03108040748503110061000a91703514203840c0440650b1203820b99a0304d4122810901c14501c101801030402a0420b00080c0b00e500242500c05010340d070401441241520760040540007000000b40340185145607100b0441641d002100842c040c952062150 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 625834424 1250 625833174 625833179
    0x1802040c260103080a03020328020d14010506030a230a0906061d0f060130110f030c0315090a0b010210140c03060a05090103050c0103050c070206030612030d110c07 72
    0x41c5803180d007400001c044007000d02c000102544207601969000b1079080e8085402d8800092014480d0103200407a600c25400180e4460182880e01611000392000d11b01442294108400034005000050604545a03a100c5188810410b90ba00180c0000d00e080d20203000c03410104000d1020384140c00059074410300700800081c0100c55081103403214030f241c40703226046407914080c000d21041d000e03000394100203500d50741000711852012a008a62004001e9104440c01c10450754180c1e1403503034000c526000d0074000d460503408070764100c90f40048188425540d96480c591808248104072044c503800030300660421804915560221803500f800360200c40003000f42d44442c43c00d0f40c00c2c046060102401c83c5000c01c20058444000e550061801001e9000680d104c0c2c01080c0c444009a1040d9115802005014059605071203240c0e00310b0101e000312071528210340c000c070302d00e444081c3c0140d005540101040110840a0058500c508200f440621111001c064a40f42d2a0082869411913001c0e00c0c400 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 625835674 1250 625834424 625834487
    0x14041a1302030d11120d090c060c02010207031101020307140604050c040209030307030e0d050f060a060b0406050901050d110a0c02040f0606080c07030c0606060818010c09091802040c 80
    0x3016211a802001001c0110105004a070f62440031400200d4620070003d82000460110700036211101100d203000800102c1c40c00d10b0903021600d03501c40c1040c800c04c020381102607640407582c0403da03a0800d03521000c0541000040f8510310030014007071b2082e526102440302c02880402c4890003180a9011164900800e404100403842114482d42d890350040114500190103210102051503008000450191091700c0d200e0426455940100c03003600010204080300405114520240902146043c10f140c101600074041c1d1140000907818490003007404040641c40703412000c150400c444d1103d84460031950050810030921400300c4c407542c10502e81d0b8092a402380b0803581100d000f55983c400036242c0c044012116808040d0a404001c040c9180f1000b061142c0103040c01026140d884201902c1c00c80d05c0c00742118580503803044c060341401c0900950541c042010b42c1607a444110005245684890030290598a81e000940190030030b0185201c00c2d821061050701b0410b283c0710003102c59110082c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 625836924 1250 625835674 625835701
    0x10e040c09120201020c04020f031b03010537030501051e1005010302030717130b010909170904060302150d1b1e09030204140105130209060f0d14041a 66
    0x10420000d82004020060b6814503000b12034001d0043c0180d07540002d0040124090341d21910350002c07400f400006008000c60314800d0f42d11141d1454003054203550524001401881690b1000c3e0301d089280c5020002c0e0b40c61584221020448025541c10309594910780140038141c22141e5000d00850250101001c5042080d190310620001c500d51070f80608100064000703400141c102700c00c11035150080141c0c6103001c084036019840d05140c01041400a00c1c10302c00321107050b0850340c0028103000d03000d000a0740203900c40c001a05441c000d9601d456160300414020b114552010b50b004c1d40d01c002400000d10308030018072280382211000c1c41030309070703000c400c0318a1031000d07940000107080501c4000360b003000c458200b071004030141350860485075a41c0000f4241d07084200c40c007181c400b1034070040020b0b01e400100400900c071307148425824002d0020003d03045001c0c080366187c0308400040d9000a03000d90381d2140d404d2900092000c42c0038241403c1c03c03e60007220b07000000784506000040344407a0481d03403 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 625838174 1250 625836924 625836941
    0x4060e16090906150b0717070210030c12142a03011809080301080d032412060905010c02030d0e0304050a170109060c0c0209011a030c1e04090b010e04 66
    0x203815521a618146600d4010801c1580aa07040c40d601c1034141070030302c02414401c0003000000082501e078450350503e200001d00038040c8004005003001b403040145c844480241c01c4d104182400900d03040100020303a030350791002020ba107201d0b107440064901c0929502003640070320300452a20140da013a40c029102c82411a806000504c030f8280b004001d080d14004a07090002081a0003050303211039035a0749009900f00b0380040c1c81c41d8001c4014540171a40c107103e00c25030030b2025848400000c440001700400201030703005130400c003035003103d00e0024080b03a500301000203940b1000810800140c030311300135100e404c01400018180d040207050808030740d0001c02d40d001e6a000400d41d0000c03e02e842009002030301d00c07110222044d500c0e80d00c2000800e800d8030400500b83d06c9515018948100b41c1b0401407803031016003000d0b40303842c10700406c01c401244a00031349a0000c0c851108507a601000442d6180300960310301005603890001070081466038480c3c010725032461081e260b10280a081e0390800040d1221103 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 625839424 1250 625838174 625838203
    0xf020f03100e2404081c021207020c0a05060a1b15060e160f0806011b1b27020702010516030906090603020309120901090305032d030415050402210604060e 68
    0x280030501080c1114010071081501040e1b8006480c02c07044e90b43c1c00e0740c002504231071085002d482006406034062051581c00d40c021644054042e0034400042c1c074602540449004000c1003203070860001a0f46480016201c4d00001c0181c070703a0441d0403500000e800399005a9030300702c0d000030200d002c2405565919207000c1650311a200c0c11402c0c21000c44030100d004009a04011807041400c8060171001d1078030041d64040c0a2118036440e00c050a43c80c00b40081e8003506d54181300706000da01004007494401c070298840b16001d40d4a880500049420f03015420318035219031a00d6003039a08041e00701420904407040358444569081c3d42d484107408034002201e00301c105820a07146084170640800051030000b0050520007901d0b40c42c1d403141032640e04682c2040105d101041d4001105402d0720701b00c0340c410000d440741a40366181995451b00c01c0b020384d03281002c0a03616280460110364480c0c404482e140382000001b180c3e48020498565a0300095500340c48091030120400131048002c2140000c440d8003 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 625840674 1250 625839424 625839493
    0x2060c0a020a050603071e1b0302010c2304090902010521070201050a0e0a150f0c020f0f0a0507060c020f09091e0c0a180e010c1d09130f020f03100e 65
    0x14404559240c81890b041c006c018000c003949108504031400c0b101954001d8ac00050130703884802e4082c0461840c2241c4040000e2034914600000900404850550b41d5041010801480b40e10040e1958060f54803c0c0000c6409884080c1181000703240c00741c4030b11815802442280c9402d020282150b0750203070050801c0e0000c54405002c1821a911310410038100c210010310490342018a10445010300310000041e04030050441d2124400c110551503000c40d50041d182065166581940d551f10743c6c40b0b45000e025600348410195656101c0300058664040c1804400740f506041080c2c17900395691010f0441000011121030715070000500d0070003950094849d115090900384500025500e4014541815031a00c04000e06040207009000c100c907030544940100d50789444002e1207900c20314841c103028104007410400d00402203030340b0550700c581080c0084d66407505800402c03408002030443c00d806224180011451001070351014405001c0981504e1060040079580d00c18040d08000e00b50340400c8 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 625841924 1250 625840674 625840697
    0xf030f0b071407021c230f0304060206011203050405030316020910050603061e0307080c180c0d0e25080c060304080a0e030708060c0d06060c23030702060c0a020a05060307 75
    0x4125498120940700c50484062000311941c41da00d002d00c1c000c0c1b442c07070141c4500c0400385107010704020410310300c1209009903003058208000207643d07a40500c1a03003000356a01d8044401e050240d81200c018041c0502074907a03a464a41e00148020a550303000c1b4003843d2184d00090740b0000d184958000c0d038800515582c40e5440385402c101110100040303da03a40301480450050070b50342003111b00001c0000c0c0d070160450341400420894441d40352004c3e4090581c00000f01b20240712031001301d40b010b55a10200107805d29265015600c0c01021400718100c20303601801038250046000c06400454000c041100c40304c101030780900c9130700c3c0000c0e50000d26100c811f118411020740140100403001e2000340445c2ca20035603409034076103882c1041e129800c0401c00003a141c00075844500400018010034280140241e013282d841002d0303e1000c11440c14001020450448240ca0038000c54801039001080e45888800c48100c03a030b252081002c00301e20901800c100050607040c00d0045d0782c421090360b240c407a117030403 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 625843174 1250 625841924 625841929
    0xa0f05181e1c0308182812020604050c06040e0a0e01021e1305010c02030d1805060a090e01060e090a1a040903110105150a0315060f030f0b07140702 65
    0x24100c9000d640e9110039003032030079440d2641000802a4100d5689054048080d400e0140c06003a01910b40c60300090784204080c1481d038001094845a030b07004056251458466040300714841d01140010203000080c07083c841320710350000d0010701030b0380504180e0310501a01010821648240d206920035281d001d000a0703004140303036004c440346441050001d49410381a401014a85141000300103640101041043d40c0c00c0798403001002034042805d140107403000680002e51f85048100100081140e05184031035089490507032003008100c050660707900c3c0d20010b031028091400b58007034191401c4483c03000058092241820786915000074007080f0b41c40d250f040105000d030520003e4401d840c451401c210100b0b07241c4e4030500e003c1d94040c1e503c5c4044031155035404d40c00e5031130190607108078011307125503180160344240b074150490764008038409181094281c110040c1880d90f000c5400c90761542000000e02085a0f00f24100d2446244142e030300d661400000c0d00d14240703400c102500b120b001d201714030060 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 625844424 1250 625843174 625843189
    0xc0c040207080c07080307030315050114090d021002070326040b0705011401030602030613050106021e011413031e09141c0c0819021c080706060b0a0f0518 68
    0x1a40101c01c0c0d02d03e041d83d8541c400e4a440103030362041e900381e40000b464006044c0d241c40380ca1152448080403180c59480d1500080c8000302c0e40b020811704000000e4180c80d680d550000c0318035030a82c00392070030f4180380b0607080103500c8405900c000d4440c80c1d91035020b180c000c250300094146401c110380401e41040e00f01021250b0700d421402c0c1c2210299030324504070f520b00c40e64006441c0250320405015030703a841e021003404640800a6020145039003440c00600070140c0204008229206150180c141f032005100000c0c05082c0480500400e140f170300e410305c0100c0300f00d842c2d5100d9150007034039104240745480011800164805030348100266a002c2c0a010800c080600d00100321350043c04070807844101c0540c0d854020012104640c1c44051500c1000052000d0280503d8085080c446100600c40342c0c0104d00013141c08110380c1c80c10995120090208448039003034500550704084100003054860b4080700b0968070000d40c51010442031130040921500c41c804884c03075075899240d07200000c0808411300054 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 625845674 1250 625844424 625844437
    0x40f0b0901140d0b0f0604060503010c081506090d060b04140412050a030b0405100e0a060302010c020d050f0307112439060109060509040b072a06150603020c0c0402 72
    0x45440c40490708041914296136501408804400241c14200142000308484196000c00c1c001e90610a010b43d15941003000b003588241146243c0189141000020306280704807075900da07001d11a550001c050045583c00360000003c2910f003044940c0c0038a01200324000f0031036000348603110640700c01d48400c0c03048003e880040a21b041c080344080808000074143c4404440044940c00d071060304001d03000e01c501c802c0fa048410301d00c00300501815a00004d040401120029010f40741c079004840421800f01300000a5048101c141c81d1104902c0c13619501100429845030310441008a40d19a01c1e80c06a42204d0310400d0700f41da8503d0804800d6403241000000c00e800c00402048920100311034604080070120100c5181c0a42115814944031204480040e0403031070282c01700c0c00800c0b000132810100a40c00900c8c604000c5020400b107060055606a04600d20741c2421080c4004c1c1e00300080b81e00100c044202100e100071156496031021001ca0068244c0325041d81c4c014081c0c2c1c65075040640c0105072 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 625846924 1250 625845674 625845679
    0xa060e010e041e060e061e07120e0c040606091403030405010f111c09030506010b2d16060603050c0f06030106140409050f011511060402061c050403020606040f0b090114 74
    0x84482d440d40341d0f02e00301c1e110305c05919040e8102e00108803010000e86c00d80c00143c10507030400032040c1070103000280092103019a90700183c0d6243e0440b04000d20412135010300e000000c009016464070307590000c000d07c10500c038603d401d44400400d8901454044296000d4075010380d20540690007039041250222a401e01c1203000c2e020703044540b030a0034a1260910010f01a40d20340603041c915503c0e10314a0b00d00142e00c0352042d094248029554401c0c403640d15200d11040380340c04001003041c04403c50052281c0d00c068102d07400307004003c008110080e085003040364014002e85d40c40d00814000d00c041e5003601c01440c2d501240820060080350b0180000300602001081c0003800c10344c582000030100c0c6c3d010742e4035403040c4800100401501103104040c00c11010985000a000034018600d43d55820300500024442d503004141841044480c1b02c180808081914080c01242072600700a0740380c04082d075103a8081c1d81003010031001401300e0b025079030480102408242c00caa00c1c1094140904a0f000301165 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 625848174 1250 625846924 625846973
    0x50105010c0f1e05010b010f02011b0c0c081605041113150512090a06320c09030d0f030c0e061b120d0b03070f081b0112090b0a060e010e04 61
    0x407120184000f480040d2132060780002004074080d0b0006d440c109449000b001160304003003503514910480074120742c0c2c0100b40e0a01508410243c60105200c03010380c1c0100c00503204681e80200840b02400807039080b0745042d070707007000304c000340c502c1115184c4104040c0c61814400b00b0310030002c610344000124850340003880d000b820813072290138000a4003026201101d1543c021510001840b030ba61046405610078428800150807055000c0c5d015441e0011503074010034a401d00080c030401300c0c14116071300080000d098841c3c5a080f00e802a012841142c4c601d800a07140920000101d0300070404415643d200520310307070428640007a00c1e09a1145001032414600440f130304001070706108405070204105190022a8460401c42810318105242c0d00400e045e49001c2d900f008000c4012070308070081c40f1500900c0e80d07002403a20041c4c0301c100e40c1201c4182818a00f0056009000c810b0501d140a00040360302403050581e542483c1108036000c3c0200c100e01c4101c1c1e40810001420300b207191448100000001 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 625849424 1250 625848174 625848203
    0x212061908150603060106032007022209050c3709020304051f02070c050904030e0907231926131109220f120f0909050105010c0f 57
    0x98245000b402d2542c18010072601845002d14090100384c2c0036111a260800c0252485015403080c0c140c501c9800c80100360000d07a0f1001d44d156039017802c036000f161054070030003543d00c451303e00c000f4580240b00ba0741c1d5020f01c1d141d02c81c1c01e00d01654022007903d0f0b03c05000c400d090056090000040d00507580d4412082c8840002404410500203144500e0048015081018148214503070800340482000c099910400c0400005519401504d0a88100b9681c01c24555030b145816500c0d561a01221079220f840b080400440a61110180010444100031413000881e4100d034000c1034010342c0504102c42c5d80340481c038042c2c0c6125044c1d0380a00414044424080304101d00001079281c1e05484040c05217440366001c0c010f0041190640010300c50654008205142107480514252141503800307120f0140c1d80200380070300ca03001a0505a079500319400c04030050201002031b01d460440e10600c4080b03030751241e0000b80c00d0094070455048a0741038540d44441c04081d9104034010102d072104654902c1c01d03903400c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 625850674 1250 625849424 625849439
    0x20c0307060306051e0a172509111303060506061b0c09180c0f040b130605010f1107050f0a0b03040c0618050105071502070506101802120619 62
    0x240c801020035840008916040c07505000c595800941000e0544400381c80c0036103c4d44803044100d0032110000c070b2400c0c0c590302c003102050a0a24101010803140104c00c0101d2007001e0554a01c03088400011042111481c1c407145900240100c01074800c6940f28000c2c1000800d1590b003245900c140700602c0541392a40a01c5003801039200780300040e0150b0301c11210f5242d07038101161031940100c6d40c202031458030b51601c0000c568544815a032227000c5c10510740b003103019480766003200752610802051034034481e101055a000800451186a000032104144098081d001d81107003046185001c0c09000c80505107020300c8840100d001010750010b9204000146c10300d4618041d42c0070f54413407038a14a949261041c007c20501d0146150400c1c100080d000b081140e07045002c8520140d40048000a120001001100240540e11018000703008600401090068081d82502610035048035122011030200382032003203001e60348400342080e640001080061502400044503084210803c41460303445420 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 625851924 1250 625850674 625850683
    0xc2111030a050408070b0f07150b1e0306360a14030d0c02030c03070f300f05090a05091b0d020c1009120c08190503070f080403120c020c03 61
    0xc081c000502e000c82c0600031484184030030401003540e002c42d00e040c682006110030741c0d4031803028010106003402004e80355403000794000c508404402400c03040c880c408800c1e642111010746680030311900801000410b80c0303c02030480340003003511115100c4956a054100302c000c801c6103891300c4080c4103043c04080003e000c809810b007c21804805151115602c0440b401a241c4006900c003d640090041407040d880010545502d281c00800c844a51900c506202c012010305900c601001441c80d890304180d42c081501d41e200754034495403116440d0206d013a048405000b80c0216a50212043c1e2007003003645052450303d5089014044050340d201c04001c0001180d9110002c3c1019082c0c0200350894200018056101c64030303103403042807003582e000303550310300210a0035000c0034140000e004102040c003101d034040d143d85418014807180c8130700030a800901550001c85403078000510305540b020800b48140d444600444c1d0540f1804544038843d1001ca02404442e1b110504620940c4211001c0396400c11 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 625853174 1250 625851924 625851937
    0x70602070606051807080c1305130c0906030b0603240d05010b120f060c0325050d0612170d02120c030901060e0f04110103181b05010c211103 62
    0x980000d002d0349841c0500200300007000c6130880b914101003c1004140e040040f440c3d025220248450795241810144844400281c01058002881c0d594406000754036510801d13a0059546403144510b07035070542201a96100d002c15a008003091021410900b4030403007071200c466800c00200080080e540104248110240b002d0f03510760345514507008070742030510b5184000b004081c050070040041c12801d03a51004068040c2d112600d00200041c002e0340314100f0107007080c2596000c3c500f817607640070005055411451400007014685840080da403044a0b5041003d181d01c2080c1c419101041c800e49075580d000340c0701c1183d101e0f4003000b8142030001e0005940d031184d40e41c50111500c90500803142400c540107a00310070100d05040c810700c914038080600d41c0c3c0c0d1196103c0d030b50f40307400c4e056440100d02810340800c06009800007042d0312010046100f000c0c0d1401102c0403036445000740e80744011109075055240c0588010100381d8040c21a6070a00d050324080c00180c01d0500040846a02d9207245904c102c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 625854424 1250 625853174 625853183
    0xb130203150108220b0714040306050609010909020f01031a040f09120201151a041701050405010e0705100c171216030b01120c11010e010212090610120807060207 71
    0xc140d0000300c1d038000c04804d40100c42000708a0040c0640030060220268080c2d016000000e82c1002440c450700c5100441e200340e03548501103890b20750760f1a04074080c000590300c00780700d210f0100000c95456285e104130b14030344e50010b1040807904200310054008010740c1c100c0002402e650041c204103904da60242498803e404032000541c0752190400d020500408220001107904002c0500440c05043d21032800361191010020100e20f49503503c070426101c2d0b82d0014410b5a444150000b21100640c0058401c0c1c1c000c2d0300078403460a0a950054440c00c040c003e041e40a2405d96440600d18032560583d940b01d84a50320081c0e9580c4100950081608070406c002248100d40d0304212942540c21181d804040b1981403e01842c1120000070703000098171030512030515926982c0c0d610740c078810711010070200c0c8500d0003002224801110389010358000c8000349080c44802c40814444803000640ca0303c02c003d900b4202c90300b84c0c2040503807142d8580a84040e900400300f0700544010a4240c8010403402c0d108 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 625855674 1250 625854424 625854451
    0xf01020418050606090f0616061401150c1e063b0f0c040506010219390303030902011701180b01050309060412020f0703060c0809030406020a060b130203 67
    0x1a4801c00c182c0e640148820b00415040c01680416100c4440c00080130108650094817540c04644c0920b4640b541c00d0064060f90900c2030140080e55105d0030b10341030354443d40c100461407506440546400c000042e00619175401400c101d16802084603c0160140c801d00010a9180980d007111820100e0341e1088504c08007050f11606104130545101d550b9049660060900d03842c0c0d03000050f40b0b9150000c1c3e00d501a940700c100064241cac0c4244030b401036010100f480011040364a0611200f0170340d031000700c0340da180041d4822244405440ca802040140c80008023103005040d50750031400340c52140d1040741400862007a0200707000500800c0703400707405200744000c9240710001b160b10584607410364035810304c10300304103103c0e0340c003004100303154026004500c070800c0004001049152100c5218030f04001d0240f02c1c0c020040002c1034110750a144403594409846840d044000c0781c40348a14898580540c0c800381c0c0c1d0400203000e603040a440c240006042da40f28840c06a000002d03a88102c03a249281c009 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 625856924 1250 625855674 625855709
    0x120901060e010503150609060d05060a1e06050a0b1303080c0d020111041430060f0609060105070b0705160807060e0105010605040e0c071410050c03060117090f010204 73
    0xe50744545004140407002441c189030428440c402c0c200c0003602c003a0042d0150030000340070303445034481c1c4002654060119016840c1040703150000f0b1034101030b516505540c0c00c0010300440c0d0240100801e40c2e40c02400d90000d649421142c0b12a030380200d400e01020a40c4000010100701280c0181c400c42e5140e00c0509001c2444c000c0080c01c59034690381450700014217000500c6072410360000117004400c207035140880000c0114241c6c4280a049019082e4450345841e4420380700c00c082805030089107808161003141c0c40364010840f400d40c0032a442400600284102400b0414000026402040c0d600f407061400c4801c4103c942d03294007140082c0c2d0101000070b482c00c2041018841c3c10030340c01d2030100800c8294102030340144107104511030102074141c040701107192901840c0407212030540c40f401e085071004540d10b41c503440c0c8100346203015000d0302c0c0c0340c0006c1581c103c201c1101e1003038070140d640002c0c0400d2420000e00c0302401410307080321485201080c6040780d500748020006030600805084450700e = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 625858174 1250 625856924 625856939
    0x1207060801061202030118090212030309012009010c020d0807201306050f0f040f0f150b0c0c04021809090609010c09030c03140a08040b030711031204140312090106 72
    0x110043c089080280704100401c00100d1a0140c00c803028070300f21010454071100d0000400e02d818245400c60640000400c5c0401070505511644000900d501501d0710080f0584c030210302c40c0036810506001c65046401e1a005140c01c0ca240202244140186424040287c5844000408041d149500c00c00d10800103181441c3c00c0300300b03a0050720200410300606040c440401c921410b0554031601802034407030169031135540d603080316030800c03030400c0c041184050010360107000e0a80d104201d0f46c1c540312854003203915407850f42100c1e070594920b030003000211128400d110003540860003544000c200b0b042c01011641d2031404d45070280c030039200107000c14142110114210b8020800f003e0500c108400d04100041c035114252049039046150302d603078040c002c1d2419040c0402d40c0001400d0010000e000720b451410700c2c02450003044556501944868098413a55407840b0f4400350946480724100010002100d129021100320001310070340381800d49404221401d82070542d0382c1c00302651102d50611500 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 625859424 1250 625858174 625858187
    0x1a010b122511030c011a1f0503190f020307031406100801260d090608010614031503030d0f0f0e0312010e100506070312050c090a14120706080106 64
    0x2000ca449603420085211035014180030704100d5200600c4410344006a1500062043c2c681c42c50503200280200e140002c0e511800510000c001380c49164030300c2440450782101100c4440041054070b840703185032503940041520070300c0d81008040071525070742c2003d1001c00324008be40c02000c0d41c2c2c501040020701c10312050320340d03000200540d0085205600800845620400150440e42600d00441d4020b03480784c591031440c1060000f0b0003a40c0f00701021050b400da8000e40c90800c0302c0340b507515192240d0b01c03041d08445000f45003003c540008000d0020500c92076403000c24403d54000102240e02d420704000190b07040e40c54038010200e0096840080300450a298041c5900782c040c400040e610b0103654510b010080742c0306000340450003840d600064402d02c00a0080805898001d01440c0c0b9805907241c0100240001080401c40609200c00b182d054200b0505030303550301034018030244100f42000303030008400d05006012580140d40403000303000411f00384400c40140603140e0f40c61140d907040c41c130080d044 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 625860674 1250 625859424 625859431
    0x402040e060a140609060c031b07030302060a150501030b0d05070b040302030729030403020c0d0b0a141023130b1f17070509101e02070e060d1a010b12 66
    0x80b203007071190a03820313a454401300d504002c0100e41542d180c010360542c0c00d15502941150820402c124a00003885ea00001500c00c00ca911a80c200c8100303544680c4c405058aa100c40e41c4a08504442000d2015600940004102d83d40c054088801d160203174403507618103445580000406000000c0910940c1000d0140001074040301460038036449110711200341103041c5030004009480088041380415200303020001d03008100800381a280d029030f0900c04810340060300c0c44105d0600e0516152440101035040c03600c02c20f0005100941546003100101c40c3e40107001c1c00b0f22081c1c45003025020196035164883c1ca907403102070000640c02d0340c11401d20181ca0003000a80b8070b0619804000c2400c103078062038032203840046074840700c1c5544405c00305445030300030070f108560700c4402d54100d10b00da85d50020071400604081070010501400707007034040e07071680350900854220031034041c0007a0060400e150140300d468071442c4a000c002682d0803101d0304020007a0403a0702408800281450070110924403983c1 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 625861924 1250 625860674 625860689
    0x6030f06080609030d0207080408010606030c080106031a040203090309040609093f1704060c03182109080a0b040203060f0f0f040813290f03240402040e060a 69
    0x185030401d10350f16070340e90240070140e5500d583c000076002c041240c038a0545005100c400e009200303143d103580c0c1c040c028000e03001007070000580d102c0000403014070a00030070b140d01103481038100040103401c0500c4082d40c030040110b00d0070300c0100311a090300d840e544102c1c00184503c0c0400190082d6a19003842c0e1224055550300004095480000401e180d10a1840b40710110900e080c14000c1c0700c00e01610302182a10f02c1642c0d40c0b00d12000c0005000c455000b11410342c1007990f04203c4405604810007102c08400cad00a03000c00345407000f030240c600b0945030b4641958881e05014100039561290349152000c80a0200c50107050f800a120031818100000740c0c120080025440e01450515200c40d2285401040409403000301c0c0080341c1405011012110342100101000007440c0d20344c101035403242c201160180c1c0c01c84000780120f03200c6050009032081000c42d6903000381740d52102d2100301e6554960810a080810000740494542d642e40e01c001d00040c0f41860015150703103403c200300081a51542c1c4941d4 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 625863174 1250 625861924 625861933
    0x1017100f0b031213050411030406050c0c0a06090236010605070f0224040f170102030603070302090907050d0b011e080d05180604060309020910060801060f02011506030f0608 76
    0x600781e03401007002c00080c00c0d0045010380b2141483c030100510002907114a4000d40b40030404012800740000071071145002e08400d20154036100c02d005498410040c600500d41c0041c0604400100c80d5084407104900040000c02003107000e201e0b141c13101600d0070003007a000840e20f2040c540880800c801a0041400c0c1c140141064016160f0405031541404000d1064a502c2e40303d0403407507800140a260301da904040d854403075031145104040f1008900601e8183e003410203a0080c440014021288140700c040c0180c0501443e560900c004100054281c69250041900104072602c89a00d02041d6a025030003203e050b5141c0740058035425807426443c03103004520001884044400a0105000c0c8051316080343e4840d00044041b1681074040f005580c0590009000514103034580c001131030481c001c4903003003201c0d03ea1440a0880c0c0d60b96205407408554120010042a4010040c10001000600000c10384201008004031014280e400600200e9580c042030203000e20140b080030050302c1d0340c400a0 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 625864424 1250 625863174 625863191
    0x20319050a060207083a060b0702150f0c1b010206070f080901020c010e010501050301051f033201140901111204060b0a0b030406140f0604051017100f 66
    0x394441000c6200601040c1c1c0001c2c0c00420480500210358040c03102d800c02803609584181c481104c8402200140090740045080c5800d20040340714210480e07582554213460408964288141194000581151200700340b045400c0241c00f640102503003040500035080e00c2441c40c13205481c8014802d80c003811903102508200920f0f400c090f58002c02011810011507954070f08102d9806031080240e05c00565003050780411030030314150040e85c1a1f4104400a2007150795408105000b80d540b08040b00041580d024200045a45403a0500400c7c03030061400070013141c00701e44205484400d2201d600d041c3e40d40e1060200b070402d10740303855030018400c900a10440340d000c03c40100c5030159449400682030450003080c00c100700c940c4060034150002d80003c1c20140d5417052502c140c0c000300c400b95220350900e1f005070303560446440028852018196920301f107454820502c002840000c04107003010841c1341000c81c02d440d01c84015000f0204034002800300341410b406000a44d040740b109180d00d42e0070010340 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 625865674 1250 625864424 625864433
    0x703120c1b0f02040605030304080a0606080d0504060c15050c0d062c0c041d15031609050a090c0f0303031119110313060804060b030d020c0114040e0a09020319 70
    0x9000d0142d4102071200303010354082c00028014040c6a03c41c1d64544400100010f01801c0401c83d859842d010300e00400c0107a0761004007076210040005400c002810410050003000d005041100000703008449840b030348104a50603d044800684185002c008040303042141031400d4000c00014100c1ca21500952800d040031907010407a241126a50920184001800301c101b00d0055400078101d00030f01e49507440c6070100810340a1016502425081d00341c2c19656040c3c1800910350361445039040c11038103102e20b81288400241800340850403801e8945011902181e410b4091340081c0001c0f41700d41c2c4900746940f402030220360807614403840340d550900059000c84904030040d00b48880324200125080c00013402c440c05e6103c0c1d0344070001005058032021803010b038815100d0f8481c40c4241e40070410702c4203180c00c1503920080d9030410bd00580c01113000303c00952051000b4040380342c0c15a007240c24540c07180c50802682c081201c1c00e1450700c5c0e5484001c400d6240420020303254420145484040e550540c45 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 625866924 1250 625865674 625865717
    0x3040807110a050901140409050111190509090a11070c0b0a022a0d020303070b0f190504150e07030804090203040b010e040b0103062c060f0106031a0d06110703120c 72
    0xf0388244121505003d11b1075444c0c0c0d07081001d0244d03020000300310490310b10701c0c69a0300380c002c6208020105000e00410840038024022511003000003401d05480369200c2540074080d01c1340e02443d4031894000e204034400603510f583c0100103403a00303001c2d072074450350b400d41c0003480e007840070341514541410480d800300541d80041c4540991807081d11b100750354454500110f851031241c90780040032101000100f082045e00d80103150300501e010344208158180c2500c809080e25410f850103061a074060b4007041200001e5400311002e9605c150684000640d039890f40304442c0c0150b0f01030b040c6190000200001c005e00011180e01406a00f40c02c034580b8240fa842e400800303141400006c0c100f03a9144200ca00000131401c003d40340d01c0e06420a1082c0d0710a01440ad515a40c0c00ea07010340a40000070000b0554078001d000d40c96000c0042142e212400641c00208500c40400e01c03130030364405a0302d2a0901c0809140b074020502c43e806034131203041490b0030030180c82c102c0f05154621010480d82468002c4000400e20 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 625868174 1250 625866924 625866929
    0xf0702011802040c0c2004050f0f150a090c020705030d090320011e020c01110f0c010c0609060e030711010935010203150315060904021009080303040807110a050901 72
    0x2100028130120100c41a511100b8616000c1c01c3d0003010700d9180c0740c803400140d440c8030098059805002507150342284009102045e1810300f5854480400142c1e940c006880750040c0e0700c801000c40d10010340c0c5444010889890107442e900503001a4014040d40c101002503404800e80e500c1d14028aa1071900d407010810b00e80085090b1070b511000c80820203a00c2007410b24504802c10112200c80840c002010756a40807100b84d580c0494640e01580c21205000720310344200f0803021000c0c140801c0000700450700b400030b44800319011640c4004407800711303039684624840c800340c8000441d65030b605420030700960107411400d94100003400b5014041c000507180208200070b0204030019080b40c0f0301c0100c0c00310404164445006610210400c0025880c41d100001c2c0f041003078043d2a42c8a10004c42140360010842d0003642214108000c00e006003440361369400b03080c0451400c401c10a4032400072508503402640c2c292034899008c03030b0460500500c40c145c81e00d07480085500c644d01c40d10b0700c0045008000140f = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 625869424 1250 625868174 625868179
    0x30714032b150b190e06040b070f050312040314190c050c090c09010e04020405180403020f07180501060f0e011209020303070b090c0a0b160c0803120f0702011802 71
    0x1603407105070400e03907500407100400940c01e54403425901d4030002d07200e641254043c0000c001806000e90a000c0c0212001054821301400e0603180504001c81051943c3c4148000c81d201c005000340c10000c540180301500701c0441c6600011110306180c10010041030082c50f543c04c0c0300030108900ba00f5020101030b03000640e0014248100708598038145241445581e40006401250701010005082d44000007030800506c240c0303c20244c0915041404200d0046d40903003604816910007190300c5c0a464140b25621910034070440341180300c9140c442c4e003020b0340c9a01c40e070302c00d0008026510410700c0c14051603025200320b14000e0b00c0480b0300d50703005000086143c80340c1c1c1071000929504a003008180c10035103142c1e030081c080341d58800007440c10948a12003111101d1140c000c1400007085403414001c0c0001704c3d4040e121590030000561030400281c080c80c5011500ba0200000014420750b0a0000d0f2440794203c1c20600c442e8641120008071103000208648110392600001c00d00e140b40400c000203103180c05 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 625870674 1250 625869424 625869487
    0x303040b270c030106171906090807111005032505040812090406091e0b0604050a140103050106020c0105072418060c03090c0302040c031d03071403 65
    0x201900311040d034120445120001121807103038141c039580000d2102041d18141d00801400759140700c0000c4100780000c1560783c2d17070400c20301e10210660400060820034000d0b03000081e0003200356580e204607803180c101100c200c206004c0c540074a2403d5805941003c0c3e80d0304220789507151801041480c00e0840808426100e14014084852486102518042c00400c0212412050b0643c1194156001205010b10481c102280400c032484a40109c20203103108008441e01c09025208800240411800881c3c21110a020000705036440c5103610008141d400741000310020188001019a80160407c8055510103003054007a66804411a4403c80d0000c1c00e55500c01c00001c1c00b2508480000e500701001418040884008580001542000c070700c621000c004820f80050281d055134811400a4000c80c4002170410241c1810741019010072050302e00000e2288800306401001d900800301010164000300300e4904100345240c0301a041d0700c1c0d900003141000c0c1d04800340240301404107000701101d00c4 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 625871924 1250 625870674 625870681
    0x100303050d090507060306080709060b0f2808040308090a030f0e0301240f1e1401051e090307090608100c3c03020903211e090117090303040b 62
    0x465000700c094a501c03c05540f50030344e44101c0100549030501600202e4041c1700c90008809081d4400c22007110365402e0340605000d0294414401d9822407400032038402e05000c0050b0b11540d080e246100503640c01c0d181c000d0301c5c1c185810010850300e00145003902603403000d249800826081101400c003190a0300c0c00c0c00040f0390707880200b80900120b01d681716070740500c1e400c154113902c49900d6040548600034510803401d030380d43e602044c1c41c0c0302d1040c010345e148890400a04c240e031241c0c040440d25240c18100b42d441d00c0d40c02108203c02011400503440c0091000c1440005403a081c8440340040040013000e216090601007010f03100c0002491004c440f039034076600a0a800c0c0030b070001036844502040f403400b040325461000392940c000700341d48140c02d80c07901d280510814020310940300c949001900078190207011000714820f146603802c0010302e46100707110303e2140030481401c0d031180481031025a616001b0000000d0700c180b030125001011615803200700075030f1200c00000d4a60103500100c24901688 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 625873174 1250 625871924 625871947
    0xb091f0b070b1506120f06040603050607030c300b1801080604031b0807030f020115090905101e1e050f040507170d030203090313080f060c0310030305 66
    0x24040e52029980d1200422010188031031044060702c140b0452182c058a102d200003001032a12801a107600318000102c08510626250005280d000c0c80c00740000900706d450340c54440c40c00d20100c0c0c40c0c00000762900d0080c181c10350321030720016003120011144804070f01c410480c0c00705c44d00d60b040044400c035070700d4480d80041ea80d0020807810300b1050442c03056042d41c540b00c4035034807050101c4080e0041011a1900c00385100081e07040184075400c000c44905017940e540c1c0c00c551158070b48000b10700f1903403a03400c1821016002440c010003046415000a203074041c501d8410f0802c0a10001c1140302481c044e1808000314480c281034251b60381e0030b80000b90311141c0300222100c0c81d01d8140300c0e445040c50b03c0200814100441991401035008034201c82c50142c1e40c01291b00d0840388400305d201c0c55000112a007031000e010790059030300301c9004800e03a402c200c0c18070740b001482c0010703500044955001c882c10038190101440399507008900c5603d030f42d255140100805155020307a02c0b004040100003d01c0d0395958 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 625874424 1250 625873174 625873231
    0x42304060906030c06081b03011707050a14120105010f05221805010b0d031e030905030c06160c110609060702090a06060914030d030c0512010b0d0f0b09 67
    0x24032600d90100115a103a090449083d00d240c000c3c5d001040146000c101106e640240510020400081c1c07540343d03030f0034207640034203068200640b0724142c45036000218150361209900310161003c201d48060b080c408108024841013611401442640f5110052200c2c43c1c40070b074810107071882030311403200000d501041c1d80c00ca118a0200c047c0d880d840c000320180c410103141d4000b4903150190340207002c205042e504110504104140040200303140605490804411080b01c412556003410000794600c080d4448608541c07050508078200d400c020208180b0710200a503c1c0080340440ca0031b9002e0b4070701a80d8226a18145031199031088034080740c442150382c1c0c1d0a04031404d150b07025100282d42d0812268420240c50036001c0d140c082100e114001c5544043c1e035840c40704040c0c2c010000c20301c401c00d035801030740100294401030080040070080c8244c01c0400060300b40c020961079045035a940043c4031950204d80c080f2400c40700d12030910b48018440c2d921888115040006000c844c000e010f410560f09202 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 625875674 1250 625874424 625874429
    0x120c030d060e01031505060108010e060418080d0c0c0c0b0711030f0a0201020d051c0b0a05090c0901081509192304120e060706020a1404230604230406 66
    0xc05007071003400318910203600181c0c0d040b01d01c26082c85100084c80d95410081d58402c4500038002810319004104c02d2044c110541e4020002400000d0702000f440035030511200c81e8070059521120004044103007114034861824100154604010341107841d9507030722003902c1c03e40702d0350560100118950007403214090104050034402401c642d661031408110f5900c2e1944020300707030b026000c2c500b59105031900880071107a0302d0811403115450500408050700040c040c07200346035001807404c0343c04961b40d00c0d09000d060007005111a000d480b04420340005004500052480290244401c03603141d0729100e4483d1990409243c0d2010317028071820700401401056903250b090b05070200f000c88000880301c1e010220740200e020311184104903120076801e0b240c0d807a2000025400c4102000881c0203d58540d01a18400105c2d20f004a10041170b40d002e024580c000d604984c1c11581801e1044100d02d4142c801e0780311400095a8603410b06140610152185031716001c0d000d032007031400002c0c0c803541c0d81e540d21070300c007 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 625876924 1250 625875674 625875697
    0x809031507020d030501061806030f0e010203070c0c0f050616061119031a06070308040303020403300f0219020303071b052404180209131b05070203120c03 68
    0x105854424070095840041001042c08a4940000450014440d40c80800351513441d6070f0980400c0c2c600807048008080001410a06035503900007904640c10030f00095003c2d00c110750fa4000158540d027030120f1811a91343c450500c0920001e41000305481b214103460b5541100049014030f00024140301d405841c41035a0b00c825103000107220300081c4282e80d4030816000c00e0303940400c03100c42c400700c040d80641992050300d580a14140701c1c6c0000030348140a4030703500500c40d240240c141035883d0358204503501d43d4240720412070005044481007156500b411150710b0341a180490f651b00300780310003a40300d01c0c4541e803175464808040c0408081d51810000c0342d40e0568048000f2100c09036a01065805000d940511881000c0345880e072030f240c140010350500c20200302345201d441c0c180703054060628001c8590b001c004a81e000d002c0e204082c2d80e0b0282c19425000e140a000c1042c0715280d40071051a20605480b070180301080c0048000358800261074030b128040119104ea840200040d85407a50050070010700 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 625878174 1250 625876924 625876963
    0x60320061902030c010f09080d1e0606090512060601090b0d0605060c010b040509030a12180510151d01050603270c0a060327060b0a08070e06090c07080903 68
    0x3103580080144110802c1c4c000801408003143c0044007a0b484015015101241c24002401c4090359a8880c1c840d01484221810800d40504452400c0c1c4003203030300039408650000b00c20002d90510244141c1404441c4010703041a00e030030740000c1c1c0071a1550040101d841c03000b00740c03103180c05d8040d4000000340c200145825190348482d030a0f680640f02c3c220304030f80558101004200d241d5000401e803003c280c602d4a03a04581402c1062950007082c4074164900d03689000e240b41c0d80400c00c240801c4419404107040032400042c07203080c1401c660b0443d03009030044e6404184801a42c1003c1065034191907041717a84a44e41e1319030800c100c1840031802c0c0708240300a80c500e0750080040000411016021055039508103031961400c06804803117140480001d503508280ca42100e06002c8084125418840d0000042240d2028082905902560001c544950000380c06000300d0150449603641302c5000c8072a000e00745064110313045030740941080100000008124a161a5424810400c1d078418102c0c010 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 625879424 1250 625878174 625878217
    0xa0f0e0316121b0503060a05072a03020f120406031806020c0303010303020c1507120c12020c010e1507150b1003022203120e03030d0203010f03051006032006 69
    0x2202c0c00da60401048803007051000c1400c108800c041640d500301c0e00700401802440e03445601400190000400c07203000c000b1801c002e0088100b98082c0100342900c1d445041d220321500e450b0181c64014032064040f11640b009001c1c88401c280c000c109e6003500c003030f85000319400302840b81c40d4540c41103441c00202550300215498100c0a40040958126130081e8215400c02045c00207109002585803000e0050020400c060780104c1c5078500a512103406510707102e801d40269407107101a4607250810b5100680001b002d2290302c1d030388191840c80c0040100c4001134a0a50049402ea982c450b41400400c1403902130702e618282310081c1c0c00442d10300030207072a141140b8800c0314002c00a6000b541e4066400303441211640e0a00011304040013a00c0c0d10009140c254612414191501462508650340c14070040004145412041c00510b0080500f145010b0081d030071458001c0c10805034070103000e0110310305041080031074042000c0c1c2c00720a150705256140080a00c0100b030151141a60303030074002c0440c5045 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 625880674 1250 625879424 625879439
    0x160602090409060b100c0309120f0209070201050109140609010611030415080103024b0d0507080c01140f07020a0803120103021e060d020904240303030f020a0f0e0316 73
    0x144c81c0300b40048070b095496029000041e103a02a403210f01900003003245c80c083c482c14245420b0b81d04624040e00c10b00090480300d071b00092511350102c030640c0050b5158001040406507501505642c5600b101c1c4e006454644000443d50b0880148903400801c071034650804000e00090080307a0160a2022400d40139007400b07000500116000c1c403040380642940810a1782500143c40358100800c590410303004100c220104241c4003a4061040310100300a0888220031651841c5405050f58401d0002d41403451800076441c0c01c0620000c0382c2414420000b80301e0740480080c00494414140b00c104007a200d103014000708a42d4112904061418403001031141c5503000c07010252412248215961011584545541540f000b8948040e070380100c0140040d0000c4100e6401408a8183c09031000a8070f41c0da503e1060084050b000c4541d688102080003402450b5040c050740300d6440c1440f41c154504010700c4801408000300c42c60040401000c104c410700c4968044c0f00d525000b01180c020f0101c9e0688400c070 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 625881924 1250 625880674 625880681
    0x1021050403080a05060f090c0f07140106090c02030316020c040f050a050108010b0609061605070620160e061302030a060501180803030606070606030b0c070614060616060209040906 79
    0x80981c04102150000741c070000480c040c081c8104005424040741031103007002c1c043d800b900586140c48184080c4510840007a07103d0107000342d140100000d11443c900c0000035401c41390300f031b04501d000381d0800c2d02c0b10343c005800100303d94029181d0030a2240030b0404100c101d0800895040c425441381c06c0c0024416503d803a81c002c14003610780d40701d08102e00c0c2da80d40145803c0f2801c4402c8180c000c007091184014610f040c0700134103040014000e203030007400703101c3c2d46450420316075070400d0001ca00e02d810b44c803003032900380300c0901d1031454042c0085c903211403004d41901c0d001e2800e1085801c40c100c50030018070507445928002d800030102e05002d540301d0520300110781c00341506010740c1340094007a04088420400080b502030403205a20055480e58032039100780710b820f43c09044107503070541d19510700200040010551301d104107000c150940d290000340c0340034420354a10148418826500c88148141581c4400481c1c105a00500400101802900e0101c1c042e0268042c000ea00518004008090140d00d40 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 625883174 1250 625881924 625881931
    0x9090a09051b01031b090b0a09091b17010e130201030e0f0619061a0309030403050f070512011b260f0105242d0d060f08010603020906102105 62
    0x1c8091040408426460840021025034a07002401a00c0100000c51f000c50003091290a2881c0582e80d2a40f1040607100b600e10280c1070003001003030b01820b05410b950000c1c2d800b001040342c03c001503065140002158201e10082c003030003d40c208004140085a00962224685000100580c0c201c845160102500d80c1c10840711145403905410b0b1080c026205445001c040d15104020400704121104011690b40c200034504d0390316100820010000c0342e4104a10042c0011a90082a00314104414089018101400d0441b640c0c181480310740868402422004042e565241481540380b80c851000f00c0c0030004c0400040c090318074820b001c1003c0028030007078180d8205440802280804862003400c8036900740d840052841c05101c6032246484d1030503015801442c01c1740c08501d080d000092482c00386c0c0070400c1c01c502256103803801c02849181414800c0103060110080110f14074640200b1041500107025a2050a10141c1c0407600750145644825044842c18004404c0c0c2e031020800d0018981035 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 625884424 1250 625883174 625883177
    0x913020306090c1f0908071e05010f050d090305130f080618070e040f081209011d10150f171006271113030b0105060f09090a09051b01 59
    0x81d00041e6480000003800c3c460320320080c09200820040400c0301a5018501181d60100700400c8000628000c081108401030715000d100c01481100c560f91402d4410110f900c910b0503c02900032461400350000150b03841d51031851000b24004140e0325048800380720794000746103105507506020500540c0b041c40c010076541c8079000ca0b031705619000030000b00030030070305584c484582c0309620500510503d8401c0702d130042e1180404200c414250780d2540510f42010320390384018a90744040002c850800d0040f40f2501181c1550f41001b170149640c11500c800042c41182402510b0f4810841e8850440440400608805075101540e035220440da42510f4140341800f00f3b83e120300e12099044140c50301c05e400c01c03540c0601c2016623448242d44110459404103807001e00c01590340309a541602da002c80103111034840c1d40725940130b40b801c601d00b800c0301d450181c0060b0701401050040e584420308050444040400440301070000b5a81d03410807034040d0040e0750f00140503000d0030302405901c0034040140203030b480d005d = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 625885674 1250 625884424 625884433
    0x1f03180215041e0807171501031a070c050c190305010c170f060901090b0402120c0a020d051602280603090b0f060102150a0e0303040b011409040c05130b09130203 71
    0x158000e41c02c3c0c3c0c10503005030462074014142c2008941c0401c0d044e1030300000e950050750398200700e514262001040c01d0f071094a02141915858400d400b4841d91a64803400b5400d0841052170396480d46ea0341c0700074541184e0b028008000d40c05801d1500d90000000659000009002c18188824000d298040c0214a29200000c082c04503801c04509410944200009403404440ba0b2801c82000040c0103003c40c443c0d0850303400c020302126403451440b00e0f071150103d515210760740d00d00708000a15010344240300004201041c030030180c0201c802413905015030740417140707000c5903940b28034000040382001007200400f00124200048043c1c16802251a5030b00840c400c0c011540d030078010007810841192182d006070000352500340700180311050f6039040204990006046071241c03002c03c0c507644c8180c80558500c590500100401c0c03003024008112440d050b0356114650829503114040100c1c14000d03a07214440340c18800d0380080301540b01c2010114010408445400e24504180007ca03203a041640070740107 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 625886924 1250 625885674 625885709
    0xe06121c0311212d0114061303080703050423040b010f020a0b04080f0f0318120a050c1f021c051005060906220806061f0318021504 58
    0x80710016155140d41d959252000482408103d40030403200402c2012010a4801c0b00030085044030a40c015207050f803500d10070a54100081501610410b04229110354004c10904600324040f4101e10200d0790301c00c94554403002c2c1460182d03101d02664000102340001d41c039400200101001d80136101c03500c00d03242045548000d00044819800915980c000b680c400d5510b0000210380c1d8981a50003409492101d04083d04928100480c0c0d001e60000b600b100000700034045161520030108540070443d0b4020700c008100d00303034104d1003400740f50f4280e0306020010801c4203030441c0612600c03060103984200f080e0907910702500c5100030340004040a0038081a8010050380e0a494818140151054080712103020703d4403081003015404254030315040f000600402281d0025040b403442c4e0011444091708180d4108850245018001072103d0b118010220800c5040749025014100c0d2290524010078811030380b402e6040c845901010013900101801a030024039680c2001800688200700320100a504 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 625888174 1250 625886924 625886951
    0x81315090605160f020411070b06030703050d050307020c0301060b120912040b0f0c192f010807030e0a080c011103061008060a03060615030b04020a090e06121c03 71
    0x600a0292001180c01005403c0701000c00c80320180d00c5520441808081d18000e074049010f48800911094001601080aa041141888490b9401036041c0d00420380305265844038bc1d82e030b110b4558407005201c0e0000114012030700c00e104080c51200080e00a11001d90740f0b103541c0c9016032205110b04a022605404100c2880300451003e1407004c0018865007483d06100d0004c402d1b6000141500d1146820409003245001c103110046581001d404502c002d01c1207420400c40703940900070402101030240401076907150a6404022505100386406035095031240403d500500441c103004280e80700301c0a1003402c010703000c00100305204050000f40000d0f01d9150440307219000c00c0e5070851b44440d40d2201003014a100764801940b0880052101030203903030780d444080840b00150031042a00500101544120b0703090700481030300701e2068404524151700d011000b089801c403405040e20590a140c080780d0151780ba04020800148050b00392400b28003c0107a01d825003040d1101440400d01f4008641d00b0b22 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 625889424 1250 625888174 625888187
    0x20909010218130f1a0a0522151212020f0c0906060d06120c050415030f060e010b040e010518030f07260a02010209011d03190807081315 60
    0x1a0002142006010403200802440d0950344802c004143d940e13a6107000f01000c1400b8551504d51081081600c1d002d00038240300380046a900321f03501078024440420148040c640070401044107030742e00010441420300d0b080165402c560720180c40c404103100c41500380070501d001c4070036081103502207980034402104903030b854030414440b4540c4107460000140031820070074024040c8468035400020000d031540c178010a0f950341c000d0107441c3c0c91400e001c28080c5042521a1510035524186140492031455407401008001c0d40d900130050b98690f94a203180300c00c2500140b25140e4020800d10a030058882c0c600d00811040b60307000007109441008184844000c4211002007841840551411034103448409007480000441002c0ca41150503902030300d00f103030003d0000e44a1503800540d4480e04400010018640c10124200031504500807210075900000c1142003a10890610003481078103040c420910b001d0760340080c100ca03600040d6451885020010b50055175816050707003d1000507147c0c11500d2 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 625890674 1250 625889424 625889437
    0x50717011e1a041205061009021c0c140324060703020d0c0507050a030b01081c020712020117010803031b03060a09180c060908100e060604111b0a0209090102 69
    0x440c001030003071055415408a8850755030142c4201450550358030070b603c213400c2c030500d4103441d6500103500f400440a07120606100074a5084820b6040542c4c0101d1688071001e2490b40c071100315541c4080e140700500440441c1050b03001c1e41d03250790b2645041110030b03c55511082107070582156012205030189800800e440700e46805500a05e0000088041075650381903010742034a440c4940c1c075001906680b0340f9200e0003c2c5114005240142d454041600d140034414240d901c2c0900c2d01c003102040c0c42d0b0303002940d04100d4501000122519030709000686140464441120803900104008500b081d0000001d40c014843e030300a030102d8035000c15040d0150f001c00e80300b595008480080c104040c94440c1c0001a0402c04c48040d41c030110a0740c0e88200c03c011a5900003c0402e1141c14104603400b001d1019a0704900303041000d005250900c4c990544aa030002c0042d446141d03120312104000040c9403d68100c4100d6049034000c807400c60381035a90382c40001a04a1141d003012000461110303040c001d5591 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 625891924 1250 625890674 625890719
    0xf0215090115051914060f030705070c0503010c0225090e0714010f0e040b0a080a050106030b010f03030804080a05041e031209050904020907022505090f04120f1205071701 75
    0x40c0c1c0341803405d200b40e1044210700c1c050380110107118202d60350041030300441c001c10040d01c034a50f59490520303089030941c1c00c42d440a03105c2d0f458094040007442d0081455810507400b204405111201c2101106904910350011861305143c510307440305c400c0d000198030042d5110145450f00f500e08401c011580d810720034032010005110040d000700300341055080000044001007420080c651226a064a06000d014050b07030969124007040060050b4403400c0360141c040c000c40302240ea8159200902580d01c05031004060030800140c02c1c22440c840c40580c0c001d0840c040b101e61004241451b40f091034140c42c00255003d03140b0351031014201c2c4c0503810b00b10840384041c1c103200080e43c0f25002c0100e4124010070075420348c0500100b0345d00000d0159035040c0100101028860081d0030801400007580000b44601c06616150007800040760146000d24041d180c2e0f0b00c0d04951006e881c08003124459951102c103289281400309101d183c6400c04108442c0e0b081128101050760b985405480345419850348151 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 625893174 1250 625891924 625891969
    0xa0807060c0807020102070e04030309020f0f0303070209060a170f0c0a031a090a0611040f050f06040e07020705090a0b090a06030b010515120c030f070804120f021509011505 76
    0x100002d02080c05021000d0050055940303985ea140c2c0300303014521046a0440010780e550032544110300e270500404082d1344003500c001e80100304040110b070f40c0703111b00e0700080e00c24100d805c0007031283c7d9200d0781c40c0d9001c0c10300c070729031710100e51003d845242e038074400c8840c1e104880c02400e54640040c240311280400b04c1e44c0041d403071104403000c640d41448074500079125142c1070259001c0880818654043da07a03116460703e0340140e0304e51130818605031043c40c6800031445040181c01444155865000351015106501046100380e1900c00059213040d0050388401d1f000741e11481004110b4000d5444490381d088180e40c0d903800340e0303034200c0d45e28225441d41c0001012075000e84014403107418500713242440c0807240c401143c5400c0e0051503110403100101e030000201d030400020011609580384030950071603041d0805481c2c5090554504960410150402e02048071140044000318802c00828044000404c1c00c148142810f0303071607a003e03101c034840d10a8146401000007415050036448020002090420b00 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 625894424 1250 625893174 625893197
    0x1507090e04050c12011518110915030c071203090303060b0333042a05031909022707020607020d080109050a0207020306130204150e0a0504051c0e0a080706 68
    0x8104240e0704d460710b5136031000800602d007140380d440b0000d8440300c0c2d454a0800c00310b280c820183c90702208144041c210a1110000945035612542130005d40312040d00c0e2242e0b20744070505c1c60b6005072800501020103048807010b51940640c0041485800b03941c0501006440e40914005440241c1d800c15540c0c4032001c0790101004024405144c1d441c01450130110040c91000203815184101401024150035084030302c480c03d08101001608040c0e41400c5045143c0940051019907008009541aa0700c400740b460455888101141601d0f4211059403140c04403101c1101102d10104c88000143c82814040b4000c50300001e5501e0b0501100d40d10316240c1d0b800c00c00410080d000150001c0304803602031000384010b981c2481070a1042200010702125141a03004110603074864140304148021201c0342800000c910420855002c2074018011905840b1442e00fa4a401c2c0d20300c0e42c844040d515002c140d550740340d100c20200d94031001194492600c60300c80291640350a080d10074003000c5140055003 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 625895674 1250 625894424 625894429
    0x903050702121212150301050118021c02040b131e0501110a020306010b0307030f020a14090a0305060a020a0816091809060c080117010606021009050703051507090e04050c 75
    0x71902c0000950081c3c039025210965018043e4200004805424040c03904009420880103405d0000c00303012802400113515048000d0030707407000c002001222540000b518002061200f1208400b112401c0302103690b01c1d9100401e8a15400140c0c0310031103c03010000000300031801d0407800c00d4030078a100300c00e142c0c5450000159044227441ca0000000e0044100b04405a5410b015084c0200003450740c0503079914228800800321010041011035031441404107605040d481403441250440310384802d59640c005400184141045600040540c4505000c10020ac0d06580142c445078282751078480054841300c80031040c0c180406c8100001840c0c0440400481341c40c0c88268440c1c2071080b400248420064803020180e0b00d0500965000c29008401000410b0107200c1401c0c5040a00740200310f19404e200f0b009440e0562040e6880d40036445240b0002400801e2054900640e0303c501201c1401300c143c040d0300c0442c80100c0d000001b1131140705c00005e0b400c0c082d5038464031880e8040d0150410b03002d501c08 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 625896924 1250 625895674 625895689
    0x20c0c0904031d0f030f0a0209010812030a0b01110708070510030b1c1704061701061106060907030e16171b06180910030c0609080604020f06090303040f08100903050702 74
    0xf00e2540b05411503804080ba0f1005d004590300c10a01c83c000c0c10b00d601c140d006000340341c013042e409404030781d01045140c0903a000a03000d5907000310460402291840007440103c4008030300e503480301224000c1840c00900b40400250720720484005451041101d120508244c04503400004d140307802558200c840d5840c2130044155080040c03084601e000104214009904150004d40011012400c03441d00a40303162805a0f070140180fa591170035021075080d0b191a40d4507410003800c0f190089405501007202a40290415a400c40c2103d04680c5080000c0c01c900f01030004a1043c1501c0c58003a40007584882c0c0c2c040307148038840081c500590a0942890280a00ca1b801a009401e81421242d4203800329030f48c000255005110300f440b80c0740d215003141404d82507003031903a000b10240b189000081004900100300c0d00c1e4415011034100c841504940d01148840c07040c200c1d442d40c14000020003044c0c0c0034101c00e01d407050b11234440403115032040d080391800481e0700c800d4000c0c020513024401040146070455 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 625898174 1250 625896924 625896977
    0x1a0f0901060b1b07120f020301050a020712110705030a030207050f100f050f0403080403030f0206150f010c021818121804050a0f1b020f06060f010c080c06010603020c0c090403 77
    0x40c100c400c015914113220300e2000e0045800c4441a65a940103011f614090190701d400142010b000c52404002d940c804000011451094090050541c18544080c1c403d1181c00028140503007a6a0101c80c0c0d1b02d00292202c8444c00307481e2160502d40c0304401c007410204140b60340c5002580b6424100c2c0394034041640d10350826451511412820030012000880d002d010344025407198449800b511054000641004402001036040314105000b04180d84c0d600b16081c15824428200140340360041d0012654111032100c01070141d000000600560390407140c00e04142d4000903042c3e901c403a440e0030480d200c030f1007452454440718401c07800d00d80003441c10740d003c84d0b0400c3e1903241c00643c0b240d40c80700207000d03100040c00402c1001840d18504000c1e5806003c80052001060b016107114500040058100c02054000c2e904200d00c41171842d040106a10484101c040d02204841c1c3e107680d2080b0040c06540030040c0b2005070f00420081c00002d0030030414a40c0a0382d071645030300500e440192102441d684c080e1 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 625899280 1106 625898174 625898227
    0xc09030111030901201c0f020c0a0201110f1c0320040513020309102412020a14030a02040f09151b09210f1a0f0901060b 53
    0x201c1d1003444e200031b00c41c11260b44240384180103050350b0a040001c00d00c001101c1020b55400144030031000d10036038030a143c480c107520f621501e0700194110b125869006c1c03426420341c40c6d101c0701c40c3c21028404bc0fa00141c1c016103c01e40710342c0d0300c203104090005402c0015092140d403c10320303210044451216400d62960404000c82c541c3d43d03018103041c4459540d81c0101d000b540384c02689144508d42c0c182901518036840b040921f4a03050882d900301d01c034444000f4005424074404482d004c540b035000b00a08014503003502488050100609941c1106584c1c0c5556800a400544124a0401c500c5000140b40040b0b041e10034100400074003242c06e11000704020098940c080161824000803040440110031070f52a100300001c10a0380002c04001000d80400c0703004401300340c8c0038801c191010110210742c841944050032103d490184006201c2c0401a1241c140c0062a40c01300c6c1d151f1a = true := by decide +kernel

theorem cover : BRFrame.Cov 625719424 625899280 := by
  have h0 := BRFrame.cov_init 625719424
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625719424 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625719424 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625719424 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625719424 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625719424 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625719424 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625719424 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625719424 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625719424 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625719424 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625719424 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625719424 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625719424 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625719424 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625719424 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625719424 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625719424 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625719424 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625719424 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625719424 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625719424 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625719424 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625719424 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625719424 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625719424 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625719424 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625719424 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625719424 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625719424 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625719424 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625719424 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625719424 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625719424 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625719424 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625719424 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625719424 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625719424 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625719424 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625719424 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625719424 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625719424 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625719424 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625719424 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625719424 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625719424 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625719424 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625719424 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625719424 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625719424 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625719424 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625719424 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625719424 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625719424 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625719424 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625719424 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625719424 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625719424 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625719424 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625719424 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625719424 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625719424 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625719424 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625719424 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625719424 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625719424 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625719424 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625719424 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625719424 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625719424 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625719424 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625719424 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625719424 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625719424 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625719424 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625719424 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625719424 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625719424 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625719424 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625719424 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625719424 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625719424 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625719424 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625719424 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625719424 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625719424 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625719424 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625719424 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625719424 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625719424 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625719424 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625719424 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625719424 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625719424 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625719424 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625719424 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625719424 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625719424 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625719424 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625719424 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625719424 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625719424 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625719424 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625719424 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625719424 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625719424 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625719424 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625719424 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625719424 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625719424 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625719424 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625719424 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625719424 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625719424 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625719424 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625719424 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625719424 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625719424 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625719424 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625719424 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625719424 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625719424 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625719424 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625719424 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625719424 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625719424 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625719424 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625719424 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625719424 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625719424 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625719424 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625719424 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625719424 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625719424 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625719424 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625719424 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625719424 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625719424 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625719424 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625719424 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625719424 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625719424 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625719424 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625719424 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625719424 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 625719424 ≤ n) (h2 : n < 625899280) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
