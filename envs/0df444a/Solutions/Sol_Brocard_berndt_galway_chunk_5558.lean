-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5558
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T16:15:47.942808+00:00
-- url     : https://prove2.me/submissions/13304687-768d-4ae5-86de-1513da850f64

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 999460431 ≤ n < 999640287 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 999461681 1250 999460431 999460433
    0x303050901060e071d150c03090414090a06050c0c060106080702060c0304080901030207050a0204020c2d03040501080c0c070329010f0b0a05070c060504030b070c0f06090f020a0f1502010603050c0906030a 89
    0x180000f0f16440c5007c00107151240e811505200507281c080c00d0641d00700c6412020040500303000620b8110720340d0040f8010601b916460361040c03031442101d40c40f115a0181d48008541c0035004035a040c0140d0241e07003114025520b0b426114a140400c0d60020403103e42046840b182d50304c00e07005415624010790580710041c07480d60004003241d0001902d0f681c00d81264004414429115075a0034540b2480200d00180d41c203500700c0e007501c038403450190364140700c03120001c5405094817809071a40c2401580484140c9510303810b01c0140000b119074034030340c00c0807078a03061210740e40400303801c6041705c80003034410845600b403c10045098029500fa042000414060350001c074101c07440880c010300b9140c070f0303c91b80c0301c0c15400c1c0511002d40041404060003503c50303032000014040101981000d400c9580011180b90a1800c0801002e040c00043d500545d03010000c00c100070f940301e080d801c41d04200003140c0c1003000e50308141c0c240c4e549440060503940203812071402504060400c2d580c414002815901003940c9 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 999462931 1250 999461681 999461719
    0x80c0d0f0c020c0406050312130b0309010204090b1c0b0a09201008070503130804030203100e0c0d0f020409030e0a0605040e070e090a0b1c0303050901060e071d 70
    0x640e403020342140e10350001180c100e070140500740c2c54080c152402d003d40d90508020981e40d010f41c50384410303028400500300542030203460b008005044481030076641e03401d201d10994081c0d0020b000340d00100c0e150a01c00c0215207822005092482c010a40409a180140d00e6014050400800c81404180c03203110030070001e0b600401c1400100241c1c0343e42140e0035201c005012440902c0000501403000307000034400043d4018051b40e91181307000d00c081120140502d0201d14034041d6610080d090700c5040c000340e01c2e40185030041d446082e038401c01c58100041090420085103030003103000d488641380d60490005414160085280940070741030201007000f40314041611051658810382c002000802d052002446904009030000800d180042d080100c000004001c3c0d0005003403e00e80c2070b6260b00242954441002d4849000030800301204541111308018020f400c007100c9981c2c0315460018017146280d015450903014256030340d200d90300700916040c00d1030000d0011050952264031002e000080245c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 999464181 1250 999462931 999462941
    0xc0209161e0908070608281506031d07050607020f0402042d06050a0503061002150c120f13020909161503050a05042604090e030a0908031603080c0d 65
    0x1c0180e03100d250940c5054602030810701c0039004142001298000c0c050b00c840d00c1c9188004114401d16401000c810000f407840060051031004604806082c2d0001201605980702819060220341c1034500d22903010155529034219008050f40980d0a01a00016041c0504200c2c52503001400c0146019242c1250813400c1d50360043d8804450009040410141d22003040c0d40002c1a20b8102142130401d0060040d0080c0001480d4500968400d441078070110f03c200300d861561210000c1b5150310b41004800903059900202080212110b541d000c0b604031045000c400788607401109000500c0b4a1584c200042c20a02074111440c0c2e10901204105181c6c036a080c5c103004040011102080072003e05028082d103100a0564100d0ba2400040001290000000080030050384d03d500ea001054065102450302598003d8062946000c0d5401141d00c400002007c01d01001d84075075520344d40e1441125035074031a0f000c4180c1d0844170100c1540009010341889a00003d4542c03000d41803024110508045070 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 999465431 1250 999464181 999464237
    0x9021b0307060c120603030f0e01030213090218030a0b1f090e1b04090b0a020309011401090c140a1d04060b0304050a02011d0d1104150b030f070c020916 67
    0x15907075141070f0070900d40021105580d00c4004d6428003100d89540c501400c00e905241400050003401c03040810945c1c441e40c11100001d040200300911240c80c0d500f204000c5d001900c03a0508014028464076940ca4001003004882c2c1e4407103c2c1054598403401e90303807858006030911180780c607080301d404110703500140544134071764184100a003803201d0410340c009408408040998011480d20201202080140d42001d43c46190b6420144c3d90703448000b25103005081da0283c200311a8104c070008142202546c011002d8080701e50fa41e060181180300c0d500900307104071880740000c03a105040000c7e88030350000c00d0305410b0000400c00243c440e640c0b6002e50859100b12030451701a008610704000315038100c0760b0003c000c404201f01000081c01080815a15030710104081d0807000003140a1410f0368942d0000340012014140806d035a5650784070241d480c1d0020b596404055007068000f0742030501c24a0040142d40d00200088020744402e1191810314001503140401c0107400240401c210030801444002a = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 999466681 1250 999465431 999465443
    0x1150804080f031f062a140f03121008100c021e1606020c0a031101030b060f0d060b03091e0f0703030c0605010608040305070b0415051003060515060a1808010501060806091f09021b0307 81
    0x145e15180c480048001c0d0050400bc0d84000214003489103805c00541d40103024411000010a025000c1c41686400c0d400b0304a10310020b1403000610b20b000c0e02184c510b0f8800d0b100e4807104845516030a060740c0b10380c4111051500281c0c2c1c03078000c06c08035448400e0010021410f040c0010703028000c00c04034035941d00c140c040321a40007001441c448d000806100b1840103200d40900c07a800d41c20010481502c07004141750b40301c641000000f801c0240941401b40b507585c1e101507c129140c0e1742d44c3e0f15000d0880c840c440000e450851070078000140050095804078840c035890b0f59030b50b29185140e41c81c1030071070300060300a6415400060300c20900040383e118060107203005040b00306540380380d4942311007900c0c0d008294601d19501e40d00c070822a0346405040e41c440b28181c0c01c19044400b004035442044080c41d80c403000881d824180002032503070300081010301070102034400c0c0c011a03445140d031120b442c100794180031401680c40070030414442c5503805461003010600d002000001c0030903040b0702c0d641100200741e40b4 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 999467931 1250 999466681 999466687
    0x30a2901060305060f10020606061c02072406081e0f01110c011512060b010507051009031d0307270e07060207050901150804080f031f062a140f03 64
    0x4c0d1340b4100c880e11074552011101114460748812000352504c0018001c0ba02495003c104960407000d00e25090320b1400220304219114215400c0c0380c015402d1034240a1402d00c450407080403040031a004a40c00da440034401852894480e04602451150840c00c0c2c4102e0b000d00b14000315400828001da550f0009015901601d42c002003c0303030390854218095030b01e000307040600e08118801610900c3d216150f04003100040f64018200103035414402c08000034035a01170480100007401e415880380c05000c0c02a905d80b103031108030134882c2d0000e0520740c60070303a45503000c010200004524201c40c000b0070003070042d18000009840c0452000d0710100503000c103054006c0d40c0b06002d01903040000fa070081000315008641c1c1c0d4944049604103102e108415030802140400150038840c00608440c81344440c00d405640d43d25040ea4101903a82c01da80034104c24005615000500510540d07200e404d10710100c400d050004031140b07000c40c1e0b4151100d012a25041c12650b46130f1100310501950058002140c06959 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 999469181 1250 999467931 999467941
    0x70e1e0102010c0e0112110702100809060a0204050f0d0c260c060301060903060203061c0602072102150910020f04290901033801020c090105030a2901060305 69
    0x1081d1964606140f0811080c410b22004981e403010750520001c1c0440c2d40090f0303042c020400b26550713114070380e4065000340f0113000420301c8584c0310741c1e0030303203e690311109032000e5072074030450001a07100d03a03c03d0541c070010750583d000181c81d0592017080d60ba4460039182c00c1039540c8500103a071501800011180038034841c1c0d540c0520720b0084c01584014442200c1207840c3d03604121010784407210781d0102520040d8040300244254803882c4002010042402e0718903041c28607440c00ca0f001c1d6000309030407a258000e000038880c08042d026000740360100107070090302100507401c207904006507000b88510111301c41c40034502d060b03080030300c0113004043c04240041e968038200540804281548544001c0c2169180f0405045280071401d0f61a010000d10300030508502c1c003202c0b1141224803038500d0240b800d82c12151010407071240c48000c4600c10a809885401b44450308000c00060248102905a04400e55900018849080000c5000b0785216400c04c603401c41c0d80c1a5040800907008400400e90f64011b0103 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 999470431 1250 999469181 999469183
    0x6080118061b1b030908100f1404021e041e0203040c1205100c0203070c0b040515030f13031e0206100504152304020f030a0e070605040b03070e1e0102 66
    0x280b41e8160344000e80c54070700884100404600002070030180900f1a00c84040c01c15110b11190300081102c3c10031a500c5000c1c0f86d0114004203ca01d0881a60b145001c502c800400c1c0036683d0140704070780040c40494140940605520104400d545560b0b220b079446601184a8107408011841c10903460401600d034030b414075000d1036141c2c054200814200c443c1e40c80c18001440010f081c07404040310f580125807003809001c10307480d60194032001031100103070381b4002c1001c02040001d08112a02160002e400b60170b15404510030b480140d8102d40c600030f2000000d1001e1456034201e5020320721070300d008000d00c60b008040d4071210901c1c01c0000c0068001500340405907d0113209413015000854080040404452030903071915030503c2807a414448995800c19544450004587e03e210050000d6694a41201c03d8841d168070449450300c003d46004403045200d84c0002e4200e081d55240d1701c940d031805040000515540e0001000542049490100681c540d11145803035480100e019001e1000401010006 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 999471681 1250 999470431 999470441
    0x60504060e19050c010c0c050603040f0b01090b0307050f010903080c060a1406031905070902120f0903090105030f0c0423120303060307060c061410030c0605030105090403120608011806 81
    0xb1080c0039a500c211030b400300e0004240008592802d0a09600c1e10660303140c80d0764a4540d552029600160110800003070060021698001e42d100b42d607032980d00c4e030322280620122402c03100300039016480303850140300c01c8c18420300300e0031650014140300c0d010a58a2342d079200300ba8020b228402090304a0024071210840758060408107265440074042c031440c1c003001080d55520150680074580070202c01600a001c820f201c0100a00303c810b80555581640341f861101d101d00542c1c00500c1c101180c000101ca2107070100030341d00c003880141c0d03503280785442d052041d1401c254064003130204181c1c10040001c3d402c2021500205070306508102c400d00d00090b00411840c07403610b6a2031607181d00100200440c59031301041d00000e803001402d06030300d0394160341072440040001040000e041c4002d64207110074000310010340310460784101c245501243d00c9102c112031501003032044540041f541c0c0e0100d00024002c000e654080001c1447c00180b9a070303601480c5080d6080005a2042d000b124070302c03202031001c01d02070 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 999472931 1250 999471681 999471703
    0x81e0d0f0911130b04020f1803030405010c03050f1303060e0118081b030d020c1e0109030503070c03180e1506040b030c03090304030c0609060f030c021c020109060504060e 75
    0x204001c0c04865444003050380e64940005481000b40000340710002045901c800031800016004648440c854a01d0f5802540110300030311844440203101c07101480c000080342d0a5070703c180e450114540b2a03a8098800c1e80041c01c180d242c1c203c0c14403005c80302c080090100b40082d40a50004210010984206801c4410707050948100311345201c0c144021802c1141110b03542042501841d0108542465160440c01802894903c1d14000140314001141c0040d10840c10241411403080e00c12169882508807080c905004010660510016100502541440b244103010f401d1103a0a4030090f038603030304690110340000031210880020b01171411702e01800f40300040ca00ba03810a142c40c0c1048a0030806000c01040c07400e0102e00000051041c840a2050302c2c0155440365940070304a440f035001601c1c0d0403141c0181d50004035600c0101c0d46640c03003801074000d029080e40142c10781103103940040c1749a0980e000c9442c10740d0b48442d00000055858441c00f4491801104009403517410004954180b07000c000c0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 999474181 1250 999472931 999472961
    0x90207020d020105030702150c0702010e01182303030c010c091703070f230601051003140708040c0803130513020a0f08100509040f0212010c05090d081e0d 68
    0x1018a00584a58010904280d0242869502ca55400504a191401452106004c05485820303c00d404840d0b40280c8203080c804d8840b692090300100c01121130704240c541405d04074120010400c404400e082d00051540c2c04800c0e055080080040824031710fa00a0603103c42c00d0b0b540e4414101d00c96840301e00c40c0040c0c4420b0101c0c43c550b01340161410340e2801004030181c400000f4820704401c102c04044100c100c89d038080d048018820216007099241c00091090700c1c0524840003a0901940c8a0303c0341d040c2c980060803980009850f407000440f10400001d004a510080741400801c194800f00058060f01c0c1c603442003283c0b1b060600b801d1041300c1500c483c0001c9254010302c0003044040d0004582c510405291801a105a030b8030207022003503804a0340b107190010280c07030a120501c120380400985190003a541d00341040380d8000b00c6400c9910102c103900018406104102d141e24140c48004600e40c026004541003900d0a884c1820780b94404802c11541c041c006210b010700d036a24000e0004108800c0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 999475431 1250 999474181 999474187
    0x70809041805060916121b1e03030e04050c030c0307030b130e070f08030301060f12020f30070c0c0302040c0c052e0f2903150408091c0512130902 64
    0x166850301b0040c1d2200d0300400210020101541034030700343e03803141c0040020302d252211202102c0103000d18800b40d4002940001c0715440d90080c1402c2a028450040c148451640c1c41c5a5030b20404009a8101801180c00c040d21404400007580d2a00b034428440c0120410002c0d168003c207000328a0000942d02c40b142e8030407415420001c1e030802209036811904942410a4025071100007102c52903207403540d0305542403020400d610680c00c260080c040e6903c044c2450f410000600103282102e41b07034695a032400d51903540c00262113610a02c10000124410050b0a4000e0388990000701912920044140000c013183c60f2001404010451000f0001600c07003a03c55200401998017800444030641100c01307a201c4140c212642c02d6039000c0e2034030480785804104004084610302ca0703260310707440c90980300b44a00e246440b410701c0282401d078011a0702c5007086280143d1101070107161086202d000c0401500600d400307000c01d105022800b0704850350094140e54a80c6110030154140007500503d50300d40c814 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 999476681 1250 999475431 999475439
    0xd0f020418060b01020c330423040b0d05100b12030c0a030f0813032303090c0a0506120a050c0912030a08010e0c030403032c01022d070809041805060916 67
    0x45031f031040040c05d0b42c1d801998071600c0d02801c407903100d0750723106c04055451303500c5c0c42143c440310380c081603418941200c1c103100b110301400400c071801c400c00c01d024000303801040388465803400b213070b1045540e014050b0418023055150009039003160400200310b1000d801c41105c04040503070105281c00074040c0b0f41000d11050030043c44000910340c0d94007008040c469060740d00c80d03c0c8069001100c0000d200d8500031552494014111921005813940e9903010b03c500090118492400c0c40c00d442041d01140300304141940c0301c840ca000503000144c850161060104144a1161030300401c00e26011640b000171640c2d0561982c00411000c0160b0004401c00a6401482013200180b421a034100b901803a01051207090420184400d54004044a10b181c0d00894071044a24064001c2c080c0c0860310501e116110b5161010440d060000258614040d14200443c00c0041c070108050114610701401c0091007080505040d40301c141083c0c0251095400741c0d041000310701c000c2040c5400d0640141424001920b0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 999477931 1250 999476681 999476719
    0x160f171009031e02210315060f130806040309080a030c06020d0b030609070e010801060503071e08010f06080606030f120a0c0b160f0e0d0f020418060b01020c 69
    0x2614035803102901c8290344402d152090071810358a105a10032024502c0c112200a95110801010b031125001c090841d04503402e550811b40e4803648102c2160404001c01004001080c2c1c02481c40030a110750910903500d03c00485181c4501030140200100f000307042c50304000d485d69000d684149040d50001c0d0344180000c3e4084036600c14103a005c600940c40e46144441c0d40d01421005080703039054400c0034100305a94034002529030498481506030030450341c0b500a0136098130170b14010190150f100c004100000740c442415550207095401d81e11012075211140d580c2541e507030701208107200e81c4a95007805060b10078820741380c00c200100e0040c000c4040c2c6440882e2981c4088111119203a80440e44d0400039002c0d07454400c00c1a848501d4204603c0c1407850019441101080c1000081003400002c208e50b010344201920710a00405070380c00542035a80b905d40704d450090040b40c129440d0304031800c44d040320420304002c0501c00d01021500c176490400091804001081c401c0c03103400000760420a54038 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 999479181 1250 999477931 999477943
    0x9010615080c160b01170703051e07080d09170c030705012003160605010f140904060f0c09090509011a0d051c050903060c040509190e160f17 62
    0x1046090030314a0350b0340c030000703101c881c01202c40790854a07180c0000882040b00c42200c0c2030690702200305000c03101c110b032501969190700c036000040083d440041c00002c40b0302445030b0b5510119040049540301502d42e8002c50415015013100300100d42d4011003809440c0340340400605184110000f0700800c2400000070780d4030307442c41c8900c505000c1b1014901150354110244055174030340900c200d0f44e83e0581300c4400c401d1b001004205541e001e140800128121403240d00d89000c4030490901714240325213102c20810846030242048a50503511418080e0f03814550050505010140d260101441d1901290b28155000140010280e925003100042c0720240d6051210120f00255109200000241340403441c100811a203103213045180c0d040091016402001020300013400e070181c0b506031311180080c6105000d103018443d0702515490010f1142c14003410314410060400c0d5000c41c940c50020459420000c000e000c0040280b002d402c240495914100305400910b601954000c6214183c55880d48400e = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 999480431 1250 999479181 999479219
    0x6030c0a0f1b050a060608011803050a0207051806030111031605300103051b09040b041a070930240f1b030903020705010f0c0623090106 60
    0x440600d8101010700d200d03045000c401030611411042d0000c290424139642c2e82d2420003103407a24142140441c00910600036024408401507074200d043c00569002d54054201182d5a0114801c0020010b000c0d51042c4071408980c0c03e100c0000d0040c00d1a000f45400e40358007505000494074100b041c010159049010034425141514000380c0301c000d035989040b8109600c0c140f104080008180050801c2007014005040b81c0c0714008450803400061604240f0a601d483c00d940d024661a0020700401c072a844800d83c040d22900f650032000f13019903810007400b1000d581e0700001450341c131414041d03002c400c0541d14a540d45880d0445030381440b8110300c052230b10a000020403000328098044103030b50304004c0344040702203125024000100d0f601c40700c500070009041c0d403102d42181500301a2415000380f060701a440c0d010343c007400046003080015500d221240740e68600b00400880084003051b00c42c0f0a0302105510031198000f906502c5920320408400502244016458424100026030b2800c103040e104e1 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 999481681 1250 999480431 999480437
    0x1903030914060f132301020d12200306040c0801050d0f050f24070e010801050f0a090f05040605100b041406040510021c03020c06010b220603140606030c0a 68
    0x8045860202d002c030f01031100c44142040d00400c00c4125000c0d114145400c0e01c2c50307000381c4030008407044000309500100440c0300340560043c45480554610900115099014803030010510484800300402c400e07503002202c0b003001030084288440e82c07409001d001785000b202c0c90280b07030341c0d41440000750201050481c01060908040c5224007005400e20000b841880c2c2c0340d040d100f10001c20002c81492607d4013070340c68051070b151000181e01e280101c0101009050695814100e40c3c06c2105001404c005d0103801503010240b00c0c400500122079004220280e2668003000c5050309042c5008026180041e1020030405821130060010f90302200a0300c0446402410300042c8103103480203d506803240350080341d04404080c81d000d01c011340000301584440040c03404001c5810001004030304901035070b140c8064a80000c0c0041204008480c09004120300d02c00001520101142d1035052446103988514040b9481d032444411f514020003c0035406913082e2201469407030080d0400f0000c2c49000c04000074 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 999482931 1250 999481681 999481709
    0x152205032203021c0213050919020a0b0708070c1212081021110102010b010903020603090c0628080f07030504030e090a0f110f0301060f120c080619030309 68
    0x1c0e001d060001d10015500a001c10141c00c903a03081405001c21040400c1e806100e01043c2d01c0c070a09640d00c669031140d41c00c00c01034054a000440b042c1592400341105030307400003180c00701054200c40e12000b0814680308421543d0ba40e5598a05000c402820b079002d01000031000c3c0060000c1844403026190382c003060324140da00b56880c200440902c0000f80c005c0c0c542c1140c5020f000b002224807410801000340203071420a100d40b00940124260b58041444600054101a082005007000070103542c009035038205940e080008000030982541010004491124004103034003030b402041890b03110301e8000c91400f01e11034a45443c1c00e07501d035400030703040a0406541303000040034944601011500400028801f1030a401c0100c1640050b205411052040500c0c101881d014810901c0403900e01ea42500655400d5a04e0309105a078040e00d00080c800030301102d0346c2101c00641841c0301fa02d840c0105a207616000c0c1c1824814080640d401e4000e042241c2a00501400841d41105035103048aa20640c5122 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 999484181 1250 999482931 999482977
    0x301230406020c0a2a0503030a0f0302120702150a09200d020405070f030b1906081b160b1f050f0f271f06080c04030515220503 56
    0x784103182c9180d00c00c0c0207034001358003041100171411000407003029001c071200007018510301c9921200d2040c40d525510400842d14024002c4212514025490a00508020341c3c1050038601e04c4c13040766507500607040b8984108038038005508150f04010040300030402115655070b85909080e585070b003140c401101039281000743c0d842d00c50601340258041c0061145040101c00500018507112801020908001d40100c05086c0401150042c107041d00c034051011345040c006503140da4020303117401c84011034005001c2104030720400502d41c3c40c40851b12141d1104290030540d0755584040c11500d1800c48078081c21030480d0300c9000c0c030300035190100e485031040d001190000348100001703070001d038002001800d0300064400c1014400d1020300c1b103030312943c016075404e580c10070031140210014010201000080c01007030300c03075482154480b400000f0039140079103e442d1945030a9180341100380c1707041800c0800820045c49031841c091180248450162003040b50344507510380c041c00464031551409920190 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 999485431 1250 999484181 999484193
    0x1211040c14070f06110a0c0204180206070803150901080a05070909150c0302130e09010f0209092806030b060a08010b0a060c0602070602460c03020f03130f0503012304 73
    0x20110704a2001381c2507503800501e06c0a0000e01c0b00e4501a032081c0d00d070050300d0181c1005640d030705444540c005d110b1403800e009681d03a503549800182c161070101d40b017604095032946401201c580645074038801003040350f03181e10705149800b020390050240107040c1191030f0002a001c8511040201c0e6809000c0344240c40c001c0220000c0c000c0410384100241d8000b40003c44007401c0501074000c070006802800740082001c025030907132080c3c407107282d0001c83c0c1c400010b48845144040c0d030b20090b4040603455a018410b0445c201b40d510980003a2103141088042c00300078540541c00ca07006002e41030003030111002c43c000090319200d60303225403014080c03101d1501081003001e030704883c1c103903510410454480c00308018a060702d8481154580000d4666600940602d0030010b002d6001200048111410002c01c54102c0d40040c5240c0d04409602c1005113102c104803043c0041c0100789000025030000b240360500c0da0f1066111948004c0c0240d140002c2c00610000c038800240906d07045180980c099166880d00c0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 999486681 1250 999485431 999485441
    0x315040f141006080105010f06350c040504050f0108120f04240206011707031509050106090b0a0f08150403051207020709060b19030e01061211040c14070f06 69
    0x2a005805041c2d04203107655200c0d44160150341221008000e0741c1e80795011110200102c1c022400801d220282d01850744212000041c1c0d41d000c2c8800e500d42d134442101000c4a0040f051355210111940402d0910150070302e8891070780d006c0b8651024030040d5241104403521610810f0030b4030380891001405140500303442007100c0041a141910046589168400300c070301454141e1803000501480300005035101c0c40300e1020710042c190310040c0c08401c2c5103a4500340c003a0342d5000c440940c0d40d210080e03240425000e00c942c20080444080216984800c4e10401089402039000203101944800090007400000a0203601d1010312a440441c00e8880c0c1c10259420300440482640a0444100700f04c01c1a5001c181c140071031780100001d00c149900d81c2003101081c0140c41c0080040c11000482000d40d038480d410034060b0714004030000803400e84840c000d07403441c01210b80555420f6041800600c0c5800c0c503105485c0500464a01003000c246180840d909038801c41c40c0c050440721740d13203600906201d165401 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 999487931 1250 999486681 999486713
    0x103050604140a020304260a05070c050402070f03020607023013030c050310020705030a08060a05181e042a0b0a020a03140301080a020103050a14070c110315040f 71
    0x4482d54074007060719002079801290b04881014a044c40c0c90204002d091074050408030000619003409400507089070f607500503070307010343e2080405c00c40016a80c440740300401400d0300031202e00048100c00d0030068a01500907091604660158858041c0d594500c3c400ca48c040131110708a141d1701c20a5821500c0500840e5400c0c1044000d03070800000300246036036000f007110400c0d0142c84a0300051141e8a04a0007000d07405069a04100705440d0751512845800b5802500108205201a241c4000c00c2c04a641d0107805800142d0910901000d09040c61410b690705488484040062030a030761082004541e03069040c0780a0709071040c0040410151103202c001d001c55000194071011003110007556403d1810b020f0b00410314400c0c664458000c140f044a05903440c000c01088640184d500450050100520200000382c0c1c0f24281d0148c010f0508443d8080d1038559159110300c0351901707003410007500c00d84460340f003a44803201e49500150703a42c508982c0b05401c0170000100c046e50b401c001d1000c010f05c6003 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 999489181 1250 999487931 999487961
    0x90a14040b061b120901081501020a1509030801140a05061b0a0f031e0e1504080102220b0306030c0405060102030c0114010f08061506130b03130b090c0f0103050604 72
    0xf010f0142841200b0210040307001c6104540e070000d5440900c181c10b00c24050769070700180140c000103480a5010320702c45407160043c41100c1d103c2d0f40a48450030604440c0311007000e825100c1c1c0c841010b041e40040d42c6805007070b420f90500c0c1c811409500141819225204a40c0100780204807a20050400c40800401100120070b0f500001840d240081c800106a0b0b02100441d4010421400d00702009141c04105512529400361400001b000c02142c624044070380243c0200800c00400c4064080c00905a412408000040d08a0000310403036900052074102c81e84000d0103201708102e80c2e9001070303100f0f400b00054600081c203484c0e44004070300358810120200c60940c01c1c9100b511140780003681540c102c6000341c0c05804440d0711510b00680710344c416a030107004058000040c003080c1c9001c000601f65412a40c03207408a56030785584210054204503502844c8500d025142400e002c044100c0c5c903403104085003c1c1202420b40e10000d500c516060b0703101e42c100769880b80020502c0d00c3e990310400420080320 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 999490431 1250 999489181 999489187
    0x10c020d0e0307050d0821041703070801090b0a03060603060f0b120c04150302030604030c0314090a0b2107050a020705040b0102340e160c020102210d060b0d11090a14040b06 76
    0x7c0e406402d2442aa411264841c0098000d1001c40d04203064a01810b0a6607030b04403a03034070741140300000d0403149a078103038804007104000000800c0f030f1207213000130362061902240b240342c07100440b01141d000b070203018010700c00007a0680da210004260907408840481700040d207000a00c14624442107141c2000313415106440a000926030001d400043c210f100e60b440518606409102102c28015078400c0758100848407000c0c0822000d09026107510039040702060710030070002460421600050706e2244c080b40c03002403a4602c0710b03414072158024050540d4141714611003000000c2d41d4000113101e54101d102520560312403024031880a0315072200b148400e0b030718161501a41d8010001c240c45110301e000c001404070f0740d0a03028224440301070760160080c10145450110b0601082d68081d500c814103a001c010326160303c07120788a900050104500c0342c2da1504c503860340d0303e01103c00302074002003401c10031310003400c00e681c84515920580b890013800c0e546020b100d03030208001e000b0700110194800004 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 999491681 1250 999490431 999490477
    0x2040c0809071a040509060f0402070320030f041809060c0e09060306011a0307030626010e150a0906090c030318090219030207140f010c020d0e0307050d08 68
    0x3034001c1c0a0440482034407560381e500e1012608100c100c90031000c1c503100c00c1c04200518901091400c1c4d100901604010b54680716a0009003268040c400450200e95603101140307195224180d010220310016000f14a07102c0040304607802c80c011480b4070b2030a04c07000c10a100e00c3d0065504001003044c0c0c401001d11070340000c0040a4040d1075980d8003640503ca004000500d0341c540052528121588a8028400004110318207001d560009042c01c041c03541311800050b5a10414000c004580c00329000713511030506200d6024251100c2d1090b000700f582c007c1136681081418204200c1d0444c006a0000070041868542a0058100401d0180041c0300612000003819000103001c00c40c40101c29540501c103481e00d114504a00800c5451905031a00706002d030041030007070f40101200c2d8051705290060016800000b8544113164a000c1e61594443c10403038800d03030701013005c506190a50304103040b0001825000c030f40e55810705c0c45154441c1c45c4403480b480910401a0484000c8a00a11850958681 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 999492931 1250 999491681 999491687
    0xf0a09171504240b1014030403030b19062006060f1c150b0a0503060420040207050a12030c0e0102030d021b12040501120504080715020405030312061915110a02040c 72
    0x4c6202c04c3d004071554420f1070b035428030a0010504546003000182d013985c03510744044000700101c00e9000e42107240c070042c100c0102003003842c04000303103040e0392800e0b5608040840c15000e480038121a101d2a480b41050029035500c2920b0b40340110401e44480001200c0404101c1815041c0c1401403c0c032890301900072040070594201844c1001e0641e50300b0f031420b40c0c3d030381819910181151301400460303950f940031230b90207480c0900d03a0041c50020005401c2c41083d458450034900034260072103411a1a200741d280094140c0030743c50030f420385414211b41c5005040001f0b0f46074407030301d02004407440d400118103078080500d00200b00b40b0560b89003110a03801c0000741c0f0f08090383c424004d203404150703200740d00384085c400781c080d944c412603006416900708501a528280100c0016030b0a0b005550244000704e5962010800751041202200410140f8240740052001117210724a000b44807248606003484140580021900901c0b1580b500c01e110b50107a01c6800d0614290b184025409030416002c240b150381c1c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 999494181 1250 999492931 999492941
    0xf0905011a01020303090712051f0914010c0507080c07170f010f0507050403080c210405040b2b06061e092d021e0f0a0917150424 57
    0x1818048007101c8801c6403006a07035a000444020702e20b503110003c14840d004540d1002800c50b4030400403680105130300898550b103403240700c00c01d480031980c40310040c00b440018503100c0c155403d41c5c5d00810001d204d48800404034440c054010b000c2c02800110030308100001c0202c100100311031100c1c4c816100480c400315032a0821440b02d540307a503090030a5106c044500d8890305015108548900d8a0320345581d942c00c04ca90001102280d080c00f40c400080301c50001c60218000c002481a9010342e65030405041000319410005440d0147c0c411881d2051032991401179040d8001880c1b08890640ba100d103080c2002c2c01e81c47d040080001000c000f000d080e5000dd000280550b80d002c4c105000072100e000c2c9001c28020703000c8982c001200d00114014080780c2560003401c401007890a82c0c030200d07100000c40c03046544403000c00300c409900000e222082d180e000040744050a10242c904407901b0385c1030342542e0740d0b0080b0002410548881300100e0108100312059501c10410000104030880700a804003000789 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 999495431 1250 999494181 999494201
    0xc021216030b0a2c160e180105040506070c1502121509100605031b0417070b0a05040b16022d1c1b030c030803060f06090d0f03030f090501 61
    0x44204010034900030880c010b900b80e200c141c032400c0f641062000d04e84c481825609036000d03d18041c2442c403c0b0081c00c6040700c50040e0036094840c034024104000041e19504580704000c0141e4507000074440001c4021820540001c054500301c2000074203814840c01d50241c04450050709840007441c04011001c86a959205000c0629200c85c184144810712144c4202203542c40004801c080c010301c1058000d070080c5030031107018000408960101c0394802081d9000390404580c171a00d2804400c0000c0c81004014060314200030051700b001000386000d03149000c0d038001c07482914004160700310a21801c0120702c003503540062902002240c12441d450391005004903d124040d0541d40044907401c103042c2009104190100561200a00c0c2e02c80304a840c03650006810701001550b40000840c4200b8801009107000d4515140d132030401108000c482008145414014107051100d408260b07920040d44410705d13046a21503480183c10701e001c030f00400f00c04025480072072400c0000d0082c008150300c900058 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 999496681 1250 999495431 999495443
    0x20c06090115120b1f05100504030b01061103031501031e0212071d061b0604030807020f0601050a0315240302030f0105090322030b0412031b0e010c02121603 69
    0x2d02d40b036141d500900c40744004007038402442180400e00c004150300d1781c6114203161940380240381d612a40000d004844441c50040051070101d000d10510020288081c014456402c004030f0214121180700e4032800014170401c3c0f0800040c640b22070380c5c0d0117074205c440340c0c00900b00101122040700c401c1d04002e410103401494821900b0001407025806820400c0d030341d034001c4855491034001003007000746c2c070f520801c1200800e0704d040b45100d01a4000b040003d014034801e4960130482d16000700000c2c80c04c1001d2070303200d1a80d40001d0041200f038682c2240603007540e812445d00010b82c0c17a0b00d141040600b80d12034417060802c0555507582107101c040c08400c4140c03403084042d0f62007114110080303400d07a20252010000c1d0f4004204040c003111107182003591402d10540d52040d0315959454050244a0485055403448030306d5101500c101d80c103101e04041d4048094118115030f81043c1c0061400d0b1903030304000d040c403401c00c500c00150741c0c81d654402a45a09042110003400d0312290040c20b44881c0d00c01120300c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 999497931 1250 999496681 999496721
    0x5030d0c030f0b0120030c010c2a0b0105060d021c0e0705060711060703140c0106030204061d0109110705240c040e06010c060209040903020609070914010b0d020c060901 74
    0x20302c195001d010964001650b41d008142c0000307030707500c441482e41e0741170006a2201b00000c0700002002c1c0540303440704402c0d48401401024a02103002020100040303d000c0c40c4414209100103000d900c000c0f41510b000f51b074070b5500e513081411040002e00c103d000c4070701820181e484c02d0b406000c554100d0b4114510351416a8266591681400441c1c01401e01c01450b049000758501d010b41804005031029a00030701c0c2440d000300d40f210107603009030b00030303601c000c0359945031a8184103504080c01903500601200c0e0840004000700c60030070001917818064181c1d8039884403a640d0304600e0307410aa5468a4000c4103807501303940010000b201c00651200d440c6c418021903030000380b10305000c0c0d0a4030101e50043c0b094a034a0741c2da00c0c00440d00714240b00400c65040b0f509000712010f40d00c551262205962082d0001c1a041c2000f060603843c001d010b51000640900381603083e001c0074900a0b01e18115140001c0c156101c21160303034210007a014061a00c102d03403081d401040180b80c070542020039561442041c05107 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 999499181 1250 999497931 999497951
    0x1713080613031d0f15120c2d0d09020f100903060b2d0d06020c0f06150d06111605100507020106050114030a0e030d1a060a090e0403050705030d0c03 65
    0x40c0f8040761041ca41c4e0300004103500c0c040b203410501804015150b4030348007a46800c10003015084404002da80c2e00340701d0503011030a030b44126a4842c11200407001a03140c2601c802c80700e100d4625038410801c0d0340c1641074a6241c80011920769908600c1c44240c01020422182800315000b480380314540f206544450400310700740c2080c03e0022041d03003440b40071481c550b04c2c014030042002807603001044803038001ca83c060088001c168a40302800262102030040c0c440317503140207100b900c0c010f8003602191f041000018851015074034441d148410950104001c11411440c0c001000c9600030b448502d48000144a034072020444045030044ca03c1d070582ea07003001141c6a03504101d00f00c030160f00070039000c41c005a030034618401080c2c015507032261540c0004030710009072030510360864000c00c155080b003548a54150100c1c800d40c04140204c4002591490b0404072140310081c00314503e44105d004d12005040460203140c4140225070206410004886d5a82d09250703002c0d00038411070340050000380c60b00858503 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 999500431 1250 999499181 999499217
    0x20a02010219030c031413090902091021030203190801030c0e061003051330080402090f071206060c02090705031522060806040606080a171308061303 66
    0x2c860a415a0380c2c02c07101d503480d6409070b846540034250b58450300000d21038245500441c1c2c1d290750290145541c0400c0b044140d01c1800240c1d40c0192628030310580c00035051043e2a0b0000310701450781070954000fa19072655042c240d0440c0305d00c840418140754443d10345030102e600181d229040301c0c411182131001c10303541c55508151700c00566415a0003010800c11400151080e0001904900c004940305194403441c0d5a4100140d4806608503168440c8418200030031800040c91a80038002c1c01e01c0d01706450594000344500384014401c0c0010305000000c6045d0300c1c811010309030042032021040040b0380c0c54032809009414400001c0b44a8021040042c40c80d911071401c0e03c3c014040c1c0c51041c01d451060408000d034014240c02d100d050f9003044031703484e060a466806107000810366803001d440541080c0c2024001c0d203e07590406603641d845040145c000078a88503409000006640d000c68440c0700b07543c0d4080c400703d2154003010042c82200280b0000881c80c0300100c20300b80c82070311000b450425444c050 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 999501681 1250 999500431 999500473
    0x2a0d030c3b180705070c2105120a02152802091c050d030b010210060e0118020403031202091f02102906131508012d0302040b0f040606020a020102 64
    0x9800a00b00c0200e140140580040c0a00305e200e0755030714481c1a103480b03e0102e0b48800403100d220041002c1d00c10414800148201601900085481c910740000210040d59400c0d080301200640c0c042040041c1131010400c102c0c0c4001400c0440c01050720040540103030180d0010001c06104078540d00c0c001408441c4c0d011a040243e03408000b500d200c200c0c2c00000d42c01880d240c1d48150541c0500c21100340c000507203100d68000380c189085c600002d5410803c0440803820001c078548841481040f09001280e04a04018510131641c4005030355281860041940c01c1a01149519402200e10715140d4081c4c001c11034001d01500b03494208800030f00f560000070840140d40f411880704485ea040c9140783c3c10000000c002400c07000180081490340d030388150304211200d0304201c001880400040c005864030140d003002051901d80f81a0b28004c14110b2814824002e21000f881590b030741801c0c0c10030740c895444075404140700400403c400b0b982d400c4e0194131020360100490060240d41c5070020703408030f00024 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 999502931 1250 999501681 999501709
    0x1403040509010e0a0e060c0c0705030f060408250602031608010509010902070204021201060804120206220302011b0203030a0e01021309110d060b2a0d030c3b 69
    0x180101a460400303100b01610f405007140d01600e0701c0f4940208202001c020785402125003104885e99840781018507400d000050f04114401d40108002403102d080000700302380c01c981c000e894a5501c840070007400fa10010f4064810404100c400034600c14005240d02440c03213841600c0008444010048085030010ba09000f100c1e48480940c00511000d8101d60182c215640702400c010b162000000600b01141426446500042c880700100070070440c42c2048010a07217000d000500c041d00340311040300100c81e84802c00c1a0442ca023400040e09241c802d400c0b0844c0110342c02d05070065200f031803078029181c0d40120f854890a9040c0f07041c010404005200315110380500704208462181400581005840c0800030880d40132030038004140700e80814801e4070001d1198403850381d510085540d258a0003140301d40d003625020100d0720030600401000c1100d0715140d09920780040c00d00003000041e508540c0704204681041c1e000c0404800268800001c00060f82800e43e00204441114040018000c0c020b00 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 999504181 1250 999502931 999502939
    0x90e030a09031704030b100f0b0c0a03080c1c2705061311090a05060306063001061505030a0e210c1e060a140105032a060a050714030405 60
    0x10042000c540300180501c000c1580102c914901585d80c0c4800000030019520806d2036411040c00308a2000c05046003002012500310325030130072700c0801e6440c0c1c88940d0340001800340f0000d040011901c03840001110101d0700f8040b009011021168240402400303c280b00c0300307003440142000381109420031580344030305a0102c001c0c0150f0b611071841d02400d0210340c00c02c40c1c0402c132145000f4644d5496035022485103403541000116890040b040600d00365000e03101030302501400c034240309001004d00d10030040007625a00310a2072400d2008440c010300c940e90186100ca00300b040603002c000d80c03010007140a00800a001c1c407212039003071041521049008144000064800e140b0b0282d010034030302410b040b0456034240d8841400045002140340601140620075800040400074aa2041d214040b520f000f04902130b00780f5818a0003081d9074040c3c3c2901c00c1c0a1800003882e00501c03402c2c403000c7c1c0c1c00d2078a000d81404d448d08018400038105810102e400c5940020300f00c050804540c00006403070845030014 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 999505431 1250 999504181 999504197
    0x2040605040e0c1516110f061209012706021606060f0e1f12050102091302030604150608220609031106150f0d11030a0309080f0a0506060f1207030606090e030a 70
    0x3540304859400c07040034451f0045890303901d45680f030340e4101c05410b032220107a0002d510361034580e040d5821198000c1420340d16428020b09096500c030f1103103c0c00750030780e031000d00103079180c40e032580f201c0800e610250007c0081d800c01c4808aa40c45984000d035044411803507603040345888983c404054001400c540800c880c804001c00c00080904500b007160b00380c09a030005103458012008260100721700d09140d040705800005002d19400d1a100340e03003c16076030400900003a81052001050290042c056108800040c0f04c0071006044140040d520b231503200500b0800c020041c0b5015224031031442150195008090001e80d0b40c646403c000624100000d003485010210300d0f0820002200786030013542c0204071840500c5007070310100701145034940240c41c0c2214182c41c003800c4030329210088a41503c960040f04080000600000c1e10302c1c0c03c800b0407030320034084003181e401142c003030780001c0d90320307403091040d050000b042c003026a0020080e940b41e418140500341da40481941e40703104a03000540020200 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 999506681 1250 999505431 999505433
    0xa15082d03220b030a1a010c020f01030f0e07030f06110313020d030507141b0301150302060903010e03120a230a0c0e06070c05040f090c030f02040605040e0c1516 71
    0x200304500d42c460800c404001a042d00c03184051026041161005482540c484a040c1070244c0f641007801440c0c400d2030030000c82c500c02c0d0b0114401c18401340030349041c551114018000403500382c01001c54282040125805103503a0f0505144101d1a807005441d00b602d010601d800000308030040360301c138002074620b04642c0000342c0d0910002101d840707001e03020058103101650005034562a410800200c14000b005280482c400001c0208110702e40144030781e14042c1180507003031540c44000c00b102e0f0121841920758030342d840800e01405203104000007074000040c0890600018001881c0180d24201c8204100310004480c091081d1051064907103060400e00050040440c0390403503040324800d0300d400032100c1400008904143c000b0f2900b21920038441c0b40c02c0c01641040d10030741d661106515001d010440540e03da0009000507800054400501c00c00352800359201ca400440091070054020803c8407400c042c0035888654103410280310b100444014906880d0040683d0b4402c84107003003288086502d = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 999507931 1250 999506681 999506707
    0x3140601081b0306030a0b070833090901060b04080d1101020f1b100501080309032505010f170709080c10080c070201030e1c08070504080a08030a15082d03 68
    0x3c02085a40d042c4520407042d80050a42c001950045206807950080c5003003001d06006110b003040925007000c00c03012041c50381032984a100450906042e0740e49280340e100c0603883c5014100a401c021545000020006400d000000d0622040303005a07032707900c149518030400f00d400e0748101800d8050b00c0d14248039102c13060f415002d09010500180e42210913000d200301c0c9904c20b4401c00da01c451100d400c00f180440c8613040a129605900203103483c0004000100c10b000401c8800600407141000300b901010030926016090704440716500c0c004060705450150001490880c09000c2c00603540140010600f043c14801d600c640b0f000f0b4152210b620f50350b95501110002c0c1c0289005070b04040d1182c0a102c034080080c40141140807204007004044070b20544013400c01e0b0409001a02088410001040079203404656907070103550044400b50781c0d0716464039880282c2004100312250004440c000180300c10700140d58030703020000201c0b102086955100d0f46616031503443c05110180c000b00b05880c04044 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 999509181 1250 999507931 999507937
    0x1b090408091207080c01030f02040e0f0c1b0105060112050403080114030a080409020304030809060c2b0c020a0605070905090105120f120702010e10050d1a1003140601081b 75
    0x1c00b82822509401e01c0090500e844840e60141c031070742c0c009070349205044d60305000d060558502d4040c03d501e003610741f81007441081402400c4005120301d403404200303200d070707150202c802415440c060780500c0403940d655140201020340c1c5680c0801c09001c2e0184000c1d03850301529202d5034150b00c0d04a80c503880c1440d140c00c0d4210302150b02d40e050054000c403c00281051380030304082c3c0a410701c010b849240615000d010070101400a0301964004804c20200c0c01c9643c0850301014451651407481041204210380c12a0341c08105101c501c2c03c0104d00d241d1103a00082040c480da0040e9802e10140d100c10700c0c1641c22506034041c050300310714140300520040c2071018002141c1c00401c0c0881b010031020340151400c00c9403005404441800c00107910301590b0f0301074544900c500e0101c42e85841941500340240c41486020380840074681c071081c00c03480c0c0c9240565600c2202001801200d07002c0421800240240200b03c9004540010750300400c1c11940b0070300546128007d00c240201401c510f084484410b90 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 999510431 1250 999509181 999509197
    0x7090e04050d081b04080a0b090105010f0324090b190606022505030a0f051002091e18130c1e0501211503230c190806040c05031b090408 60
    0x900703440380613020007480e00180f0042c82118050440801c8500c0c10b1a030511010308104080c0c0c0c1080c0c0180f1070707042d08200050449901040703c90a4142c288500600741c6084c00301d02a00c0d61404142c0320038000c0506640d031098900708014200e0000303003641c00e4221b901d58051080181d00c040310014200729040c101e1191044410f88241196988a00181c0307070401121084400c12910320b005002c11174200512030b5980035514017982083d0018000c01d01810300206004a007071240c1c03510000640f0303529020038030010701c00d03c001014900091000c1c5c0d011103003642141c1d602807001002400b068051010b1691811091410504c60302d407800458070040705900403003003c03403021440d841004140c851500802030548084030440d2650501c0f0181548885844d41100401c0407982103030380010130701d01011001280c40c000120001c004031484180a60031400ba0303803141400340000c0c04034072000340003260000c40c1142d906242e144040000c01c510b100425400c442d04801003000030350504003500c00b1b4 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 999511681 1250 999510431 999510451
    0x1003020d39051308070f0803040803070b04110901030b06120703020a0302041e020d140a0c200a060221180303044805040b0f120f0a060507090e04050d08 67
    0x5210043c1d212007800e84e441400240e01c80c83d0100810f0300000d20100041c05100095407c0910709001a0384a00c074032840241180140360000d400c12400c04200443c007140604404810745c1c40f813824038070b441c0c0d083c0c485602c21303c000c441d0f880c48050b000601d6400e4a50150070f228889166a00f804050840c450b090b41c46640002c020308a03001451010700700c800b49030000803401c4030042c942110001c81c040d2204114908006008035401c3d000480250148001c02c1380070014148181c9550510442e61001001640005180c440300741403c24041002036a14030600502c2d2201401a40f910b034464071300001e03030f400600001c0d0100d120129141c100d041d8009004155642c5503944520285810060101101050211b00980001e007082c0d86d014101c2960104801095000058003042d07c84182500c50307103800c400d9124a4a040c03003140030304503414044032840a82031030000040d0000322403500c0090a80d280000c0d06840c0700120038081d0381c21002a00d18103550b40000c0350811401440c28181d = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 999512931 1250 999511681 999511687
    0x706180303020c0f031c021c080f060f01050c03070f110109050306071119060f0609050903120c0d0908070308070509010906260c0a090b07120804030e1003020d3905 72
    0x100340701403442940481d840c1e0303008d400300b20381801c5400b06e400700940004e82000021410030118041c0e4018a40d04001c044810602c0840c1e5070f00121142d00c6040078001e03480c0400310f4600c04101212482007100c2e032241d032821080220481c011903d0842501c240d40e4107600c01004100c0403401541d10103840c1c4170b03045c2600c800e8400740040801c601c2016000301ca9280d0b0310003041c0c0740d400403440b81c0b80261042d0a0140700e24100350900d269240144503503d60a4210360012503038800e1b02ca4201c0d07144400c00001031203005001d040a1941e0703080000c00b0790102d0b20600000b8039030351048045983d0b0750816103075030b500079081201c202d816000c40001e1203220102c900a001d00403082c001050b100d041d0b088a110742c0d5040030b6100604056079684440580701302030058900250b1200d50f44801040103140286143da22404d048905814582115800021030907a00e030440790326070002e2540401c006414004041d050f4410031118449001e40c4040707041104017040c040403602c41014401031541340c120300f = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 999514181 1250 999512931 999512953
    0xf0307170a080a0f120b0a05101e052218020f0c010905031305030303010b0f0c07091b200a080f0d020316141912060306020c0706180303020c0f03 64
    0x1d540c2c1e00ca00408000704e407040114000c40d070b902010740c48004040c2c5d0f40500410380e0441c00700f5108280350003428032445614202e0090288145280744101810100190041441050140c91607015a0600c01e20794949070503940301a0385c0312080c8049030303514058154200c0855a00b68025008440f203070f0071503003080000051484090281d07083c164002c1d030140d5599040102c82c01d0400b0700c6031b80172034040d0300140010840ca00c15101541c540d5480030100c00d64400000364903604105490300008c81c2581f408401103000000240020f9020102e038550b030050409001741c80b511940c1c030b034003900800c0c1d10401491000950701005000e0040b10310485904081800540c201640c0044800119510109400416030b550000d0314480d0401d4486c42c29103095110a01000f196031200155820300c50382d2204407429036440d030b010030010b40e04040b04646540c01c3c421000d8803801c951040e0000245841400c030680700d00f4003c400100c9178550000c00d00d0010110500031024982e19005516001d5407880741 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 999515431 1250 999514181 999514193
    0x60819150b100314060a0518060109030c080a05060c041203030e07090630150504050c0a0303080a0e34080a0302030a080f1b0d0e030a020a110f0307170a 67
    0x3180440c070640b004100d0321400c13800c0c1000920000c10f06486951803044c104599103e040640c110100920908001541c5000040e52040344540c002018409880000180e2040c04180311550511907025600700303840d0720b400c19040d40214094103c1140e00c84081000180c040d900c00e00000c0c422000365141250b07103050f01c1c2d007114800d920650584440300c1b4550008441c0a180b424409012054601c110f035050715038081900c3d40c03141c1c0b030040e1641c3d00e020130300744901007040341710320f800043c03080b0441d6481e860300800b40710069503a100464101110381c4151100460802030381c00219a030b84a6a42003184900d038201d200e41090364080895070808140000e0900c11240704034001d40041d590392150101c000c18144000341000403800001060280540b10f001c01412040c83c031194103501e420054410600904600c40c05815621000030b10501e825000716054403524001c843e034803000481d2006104012094a090a0341600004414060500880c8460300414928021503010007220380c0d0390 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 999516681 1250 999515431 999515449
    0xb040509030a0e060406092303060c070303180203061603020d0e030415170c03091f0506270a050405100f06030c2108090117040b060103060819150b 65
    0x4114aa000014801c1c0040d801400c507800500c400d903a04e6150a02c1c000006207040c1c228024660072420070003050015200c03111240215800040075190036041040a02006600070303441140030034281181244240318014001c1d86094000d000f611055030f4401c2903003441c4178405841c400f03056003030040421000c4a44540380c00225441d0046954078100808121185040070b00401000180200709041d030707100ca10080c0e0442c00701d011541e1a92034000702d10f801c100464400340080310300fa41a45081d00010f41206004140686654036030b0b00c0002101c40c01201c2c0407210080800d51400803400e10f903519400a07912a0203001904d0b0000c900300c440c10290b8201e81113106039182c5a250074024042074049201c0203002400c03166101c41d80050500aa9010300903010b80342102c0440d00d0305090340201d41994502c070741407075103071031500d0035140c00c803803e103c20707250240003034a05440419191800143c206440c43c1b81121003d6640c0da6a58011000342410300c0c01a41589640c921507640d114107501c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 999517931 1250 999516681 999516691
    0x71202030618010f1a0319020a0e040905060f090f031602120307080307021b010206040b04031101060612140f010b07060f05190c02030405010f03090807240c020c100309060b0405 78
    0x15201154540300300321712818a000c20034000c07004100240401c0080c0b060101d000c9440c14600503031034070007080082d11000003201e05141c00c142060411400c22801250007807043e081c42041c84403e44500f505a59254051018420158402c00c1080540341c4280c0d654002c1d43e10003041600c5509066418601b95001400215207140c0b0100920907400c0e01400120190307110003580f41c0e41400c3d5000000e5480b82c01801c05081038482e0340202d418107120b10040351075075400d90001e0110550b503290040400c0e80318402c54807a0fa141290803050b088030f44404a0040c503514101113566400d01d202034071642e1144d801203503465030f1030740c54481600b13080c0161403140c1a06891603401151211a04080d10780e5501e01da421508200820b204036030b0080b0180b0003000140c03030006024611450002881c1c03060b03d10103040c544061640346041c229025140307032560244202403029206201003a0390f40c086500b1925486903110103c0c020061003980000d0200e0b002c0c0102154030102c4202050444e1001c2e25 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 999519181 1250 999517931 999517949
    0x15030212012a02011404202b170304240207020319120f0f03151a0702130b030d081f06050c1b06030105060903160915080607120203061801 61
    0x80d14030380150203103c1c03c1003803491741d03035000d0f001c1ca0584d5072000c15001218034025000e100d034013070428545900380150407007103e260341407026680c020000c1e0713483e0210580886024544400d03540d901c101071410340340a103a2100c08035044110b4502400d0b100064510340c000c1c2aa800c0c084100942c2c1e00b04000c54840302a69005403042510741400c8419124105001003030000f10000b200101c0d034424004910706085141c00030303c007a5144911602c585450348500381da1840d45840b1a210328001c00144502c5100b1603040705440c000c0001d81c000e6890301d00049a240c0c106110240c01d1600841c04142c0c010700f1003a00350701c102c2843e0344000010041d41c0080000940105402e03208540411080000e0850807601c014414501c2000810314031050040b2030042c1c1021070075407207070344040103140c44102c505a8550420750f21044108000c2205c106000610408100001496400402c1243c094801980d40c1d5420405080725032010f50300161140b0b030001d9031390001403a079140b40c041050203091500 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 999520431 1250 999519181 999519251
    0x13150603110102010207051e030c0f01060905070f050a0c1a100e060102010e1b150c0f07171b1c0f020307050111190827030706031503021201 62
    0x4182203184038400c9070700505581c070400003040826000240340c401030b05048100d82c610301610442c0c46c1540200d841e102c520344079009a1205804045d045a070640e640c80404220070b54492808030f4a011800444501050b41080b020210a21454602181324040d81d403100c10207503c004007090501040380c0d1541541540c000a0140710000300380f09403c44401d2009100040c98110381544650407006601e85500b1500003517801758413080d19180c1c1c801d000d1b1812a031107443c00030000e91a021030071403e400602405e8008100361031f001070038100c2201240000d190400c1012031114250f00040035445e40401301c860f14243d01c001c41c04914403a01d20404524801b000359105052900180740c11250610110420400c42080c0004030f21900242200c1c0c1d00c1a8482c03d820050350394402d5041c200400500c0311540108610b81c2550000d0300c240503021507405981d83d0078210304071105842640d048014122082001d4031745180c81d11a1603024000006d0f8070300000c0d403c0b0300d8070110048140001c003200 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 999521681 1250 999520431 999520433
    0x306190902090a0e16051b070e010305070617010e04030c0605010b0901090b07051c0e0901030f03080702150c0a0e211506010813061506051305030f0d030513150603 72
    0x4002e1050051040c0003080100703003400803005010317041030149801088404201c010928204510a400b03084404096486407074031884e80d480c00c02d07002d00013130701d451043c0e1100040d02446a0305224480000300c0c00907080b80d007040c6c0c2440f500e00010703005034200940c880b04c400211354244215402404211407071560f445210002601951041e0b0200018034818410f03080841d82c041181d440400413840d20310304240d1801401e0f101c807101043c1d000c0d00b01c1c0c2500e0020040202002800c02c006000780c8070149103503a000000c903619004003e204041700d081c80007003141c800003213016089401190030200c01a10104012843c54140601804850140c0883e40c296080080c0701020484617020720203031840ca8254000307464100c024020300440000110400d041c00031650001d2896441c1c2000c2c0c24100782e494100030810b4000d038120248914a207007001480e8600050781c00c018070851400703016406056481503004040003852901110f18103d4880e00090f489010800c5035103120000055440c11 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 999522931 1250 999521681 999521689
    0x100501060f0924030c1107060207170c0d020112110315040612030c08090607050a03021507110a0b1512100b0d0f020415180b0f0607020114030619090209 67
    0x460703030003851100f04000d005612a0308064100149800a050124107540c0442044641c1c005869404000303015940011405c0d03a8003084100865504020002603148001c001a48071140810183e50200e540080c1c000154014141012841081c54000404040d102d17905469540125a5141c940781040601102c520706441144007428142c3c407046041981c654000c0c1801840c0000940b44000103d8003413403d80e81c034000c0390400c503805416128a00105d00c0c000e90740316452040000f06c400c101001910691044100038410b644010041c4192042500d89c00a030900103800c400c80c50240c18840b440686501c00500c141280750740040c07016003d886c501c5011110003048030341c0700b41640841e0401241144080b03c0240c4e030110380005604259452010070080c0f1603001d40f4041880c4c2c0d81c3d49800301202e500200480c80b0a4a80d24518106001002054412420000d02090464070315404090208000d9a48400c002d001041d41d5048a00c00e084030880d503071700100d2500e4000642000c2428 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 999524181 1250 999522931 999522947
    0x210f27121f0204061b0503040b0414090603010b0d030315051005120a0507050307210f0f0b0a0e0412020c030703140d02061014220504050d05090a090e100501060f 71
    0x1c00390004609240c00c0c1540201581c40d0200f0349401e6011071102241070241c1482191700806121a82e50f54442d6110803401c21030005d2102c0b580b0810f030550000d581800c0c18020b00b01100001400b070032143d0010f5070190700408414000203074111a054000c160303030300c40e0340d0010300315142130720380b40e4441090710301288011000070004940c0a0401d8180442d490300704080e03a42009503414804011f1006410020a0091500e400071001d410120038008081c407690020396141c030381d40003e20100400405101c032094152245c92031080c100800a40810102d030002555138600c0d10558244031801800079140c40107035081940c0c00824815a030707000d01c0041041d40752083e91800508060b242218841c3e00080380c41c480c500040e40c171108948120f40d41c44030b032619080b0004844201e446d0310700d01c01c00000d04040302c08580c1d910034401d85602c0f09010740c080c0c58040e10001c00c10315407241010f00c0000a04040603206400d0b10410034410505401c0307014450180090b0f66a80400808202005101003 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 999525431 1250 999524181 999524233
    0x906050402151608030c2a100608031b030408100f061e1a091e09010e0112021905031504120f0c0b10080a05210f2712 52
    0x7403001c0154560003000f0268200005410070302450312950b0b40028090a4441c81036221b0500e500310a5800c00312240c9400c40b560b405040e030446d59080e000d4100101240e20b40d018428050f0320034401a501d441007554a5801d4400341c809403404c0c01d07580c0029a103408014203240000300c0e101c1b64840c00402d079900c602d800501c0181c1000c2c8086091081410303607000540a006c030b02c49145803800e1003180e5007004803018a03001070006040691032580308445000c00046441c4142124000000e080304105030084c1a55003080010303500802d15400c1110347c26003605100c504108240e0001096602880545d042e0301085818ad5018549031810b900c0b81102100c0000c00d100703402e95003089030356004445480d100d5110408454a8590a112200001360345d44148524850403074188204400071862480704112007110300303480380d0907200810f02402040c1544540010900c44101c075400c08040004107600d0826070a1058103223a00421031080480c00b52a216501443c4d8504808a04941280c461 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 999526681 1250 999525431 999525469
    0x50a060911060901080601030903030605031f050a111c0623090609090a020d050f0a0305040e010503030405011d0406050604090902030708010c050313050c041406120a020303040501031e0906050402 86
    0x49000f01002a28126019285a0401d5a074441a104040c020342c040740182c50010300b1a5a20300c1c055030081c0328a01d0020021a00d103041c040802d014190314051017440c0c0020340b0030070382000d0710072551604110000b0780007824a1707141c10b40010100c68a507441000c031031030b20f14100c0040e101c90044c002221005402140140b14000070010502c0d0086400c0803111b0b41141c1c4a1000f00203400c083e450910f158400300703140d000d0380e05100700b0190084014403c030b41146640040c0b40e0f036160100341d124011449030b03901194100300507911044044000d030b1050800280009000d64403a400b0070880e03003080e0080c804803130b0342d00081001c0d840d04214920041052030001e112003150001c00404a0001130002c1e4642c056400c01c3c0c0e0100a002e20104080240c0544104807441e46031084c10a01d050540b8801d0180031368484101c1401e0005c100103500f02e8000d0f0007185400d162400450050903206800400c8200080b11220100c0c0c0324003903141c0990003510003007410305081c01000384e001c113601d0100d298 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 999527931 1250 999526681 999526687
    0xe160809030f130306050c09010f0903080d1e06030c050a0807121407031509140c101812140c0a0e060904140d030606231801030603050a06091106 64
    0x30004111a42031002c0c0448944950442107030300555115604010712060800b0104402c2c0c1039054050454110241c0e20600c0c40c040b024800e8410300c502d40009410b103001008041303804815078110011001c049944452500002602a011181c65401c01c0f1348041d4031080c200003501c0d100082101401c0100040c01c1d0003403911407120788951540b40000c00705061410540c100d0501404040000d503046003035100504802c0a182c001015980d40480e0070984103c501d00301e1800c0040c000443c0100503100841b5489294415a0007045c21250301c0b1203e440c2c440045240b0070410202c100091081000305c0303071101078110081c10010007007092405802c5102c010030280864001c2107400c80c0050302e501c240d42e115802c000c01e08070f01c01071b62030f0040d10501d01e0311043d459143d030281c0111212541d940492421403042d41e00411070040d03064548000600c4542880c03000b00720018207114050400090007a500d50324a410b1507200c0308140c405a680700e1030785041c46015005070198a60403541246 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 999529181 1250 999527931 999527941
    0x60d0509060f07140706110f070f051b01120b19031a0603210a0302040308041707091104030b15150a0305010f0608070f030f05090a030e09010302092a03010e1608 71
    0x1030078041c0d85d1024151a40f81c81c0c01980b410055400c4440d00788200c241c03550740d0130381c40c103081e01601461042201c207849103018030b2030f840303424400702c10481c1d0051390350300c942030040091600504801a0030701d610441500f4122141000800d480f0300540c0f0036010750680f40035030b032616056a40024a10380c041d8100020321489440c03100110703103581d00031803e01901c035850702c2d900724000d0081d5080148101400500410000700f100c0440550b000c5500440380540e0319000500d00307031240003e074a10302140a102c1440001e0280007520ba104030039012049801442d003000450500e01e0748018000103000080441c04144e00d40151400340c845540e500c038071203182130350040009800805030b20400021181c1081010700c00d40110b00d0805058405201c2070030b0140c0c5c001d0300c50000300d03000c401040e0f008a040085040c8070301081d048a40060407003485984003104018070620175003040c030905080007074240702811210091030281c06840107202551420b5414080e080e600404814140721052003044 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 999530431 1250 999529181 999529217
    0x10501090611070803070c1728031112031f0501020a06020d0e1b0315010807090b030a08041e0b18120f0f01090204050c0304030504090209060d0509060f07 68
    0x102201c0d03081c41c2c8120032220b1412054240b8072180c2000816000002d024820300504907140b030259036801c4080300c1468801413105503141d43e9909280b51003074540940e040c140e41d5008920050034020f0419154a080c07034911507003400d40380c50003103c15a1001c001c2c07104002d4240800000d034400000601011130402002079619001840000c00d421780014801c034a07244560047d003603d801040441d84402d04400740000a0380d20543d0b424028803130b1215600705062001c49040c101c9041c1c0d00642025414000390b000540104000f058052240750b00200004100350001c1008214150340411b00000a00f000010350030580e102196201052002e600551034941d40e02c0b180881c03c03104901142c101740640b50620f22011400030081c041c661401e8540305040d005000e42ca8802c031800c100607a42e0300c000307400c5030006541c064009001400203010113003207035000b0007890704c0092034241048140d030322080c20369108030317210101a04014203000501011010302d94000559040c10404800741c16044 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 999531681 1250 999530431 999530447
    0x40305030402040b01140712112b0509090108060a0b09061e01021e010f110c07090c1e02011b08090d1202040305010c26060603061207151d0405010501 66
    0x1e4801d0b9529200113950b40e000711440354951103d010584d4551a4500b4847c1038203402c00c42c800045a400819a448002e0106c1d11a5080ea410808240d07148814409448802140852030040c0300c010044e105096a414031654003c04101e07000b001d0910304150030006507490361a60501901490007406178a50311410050030040c419441e270070507081031a00407840c100030710024010840589104040c1e00c1c0043d0041d010300303085240140005058044600c2c0c0602c20701c07011400940200d00144102c0d09542c20040d680c24880c90884102d400c00034820086081c2c00140f080981c0d036a56450304140d24030075000d040f0110344d040900d920f103016a60f19446114240c1c01d0000c000400e03c0b40310101d151503040e00c2c09160044003c205100c6206000707042c407025045400c1c00d81d160f0b840841d0075407a1a1160a1207020701811150454461304103001c1445441410b0750340707900880d107000c01c61118820340e0082810b0329a840d04213001044084245a1411481c0c4d40d0080303080c50014865a42c00c03884c5 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 999532931 1250 999531681 999531683
    0xe0102010c080c0724141608010e09070b04060905090612030a1412010303170a05070219140f06060a090e0303041b030c06080a050f0f0c0901030b0402120a140403050304 74
    0x40f81d03980c0e403014a44801e0800c88018080c80c0c4102c603c80f0b1803480b03040d6602880058201018650721901c4181003040e64031301c40c100f40000038100384014130421200c3e02180d60018402e004503101d0b07503103503c401c01d203980240d00624000f8030300840400243c640080400c0d00503c1c02d0740c84040340c15044030407944030321486210300248900268440701314000a800c42d02c2300041c03840c041d0255612071030000c00000007251018045544000441d00216882c8101c60080b5800d80041480407012880442000080030050b02c1500350090562031000003803250b035010550400c0070304a50300d0800304210f00c414094011464162030001c4c0e544021400004503034005410513500e848000990004600da018542c0000300001080c0700000b54060308000d100d40103514405c03081c4465030703401100c0c00c8481d00031102c648100d00d000e400302d59000c80d101c000300725a420615012401043c10004202680c1c0300d000c0d428500a4a2410840c6580701440744554068a000901c0117a06141d24014014000030b00 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 999534181 1250 999532931 999532951
    0x13030f0509240702040603110a17060403080432121606051302060706020903061312111204080a0210050913021c11090306090601060909050c090406030c060e0102010c08 74
    0xb003102c2420040300a4031815a4014000d20520707840b0300d8419100c2c04414612402002d0508000c18607400c40541d04416824000c0286510780d903a440032102000064000e9580800c80f1401003444503042c00f521021030000c5ca2044010341141c80864541000d0302d200740300251080c0800c80c00d00c4841c0718004402a00581c0104407a140c1030003c0441000507100254030580010b400410006260081c1030000340450950324240d8a100242ca4118810003004016000c10801c01101034040c03032410550307587d0001107400922182c2159001540150815559030f4454603c100451a0034450120748a07060302e011030400c0300c810b020030003070311403003440707202064010038800b1400004034100310704403501d46420710410041d8240c2c0304440c1c3c82321f00010300074058040001c0c648000015110704a801955801c11124901022031005140c080c2010103018000c0060f200c4541d035038006e01000e50700501202c5105441c0000c040d00b0040d4030285603055904115088100076003060342aa8018541e02c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 999535431 1250 999534181 999534229
    0x70b040b040e06040f1e110f04151404062001060303080705030a0b030123131203111b0c01110705010503070f0e03150a0f0b030604140708030313030f0509 68
    0x80010f8040d0082d2400342c0041450312400b43e840d8440c482d100b660380700b0342c0e45080244441c1c07c0f40080b0288101d045904c00c400003000100301e00800100c0100c219440c51400d0b4171f101d04450010702481c0e01c01d0344802c002130320807102507038000d54142103140c0c03640d401d100810406140d0341d000b81504000402500034040d000c800074261562a4004103901000100204103545a0003c103450b031010f060400c082107a08c40001030481c644045424559030f800145a1807900b4100c20110041d0200001c0d03003911010a10000c500e10b842c3c01107810208811030054111944e54000050907030a00298100d03041d071103994104080d03600f1008803500803c1900d80684000e060082c02e03607203207440f0a51960503102700390b141114000c6c400303141401038a49082c18040c20014501280c103030350580380f04550541101e0b01040c001501c00174248142c4050f0070540c1d4200355070343e4145065402c21a010090b0f50300e0800c0000405600201c46107110750182801030130082124040f40c07894180300e01000f04c0c14512 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 999536681 1250 999535431 999535441
    0xd030c05070803071b050301090b0f130215070b1e0114220c140703200a0c0305010903080a11030f0a06090c0306080105010f0b0720040c05030603070b040b040e 70
    0x5001d20350103030100000316555034030140381c10000d5103200101d90041c14110000400c107072a042c015019403030f030060f80a11682d1904600001140790107000013a90362001c3c0d06400060319844000c0041302c00e03541c00c6030703100c06003402d000e200c113030b40105810440800040c4000701d10890344241c60542d45040c0945103041196000b01d505100b00d80307400100c080d100c20a02d60847e0070343d00136410f845240e5a82d80341c00f100c4051400b4950060720b1005000c5800e00c00c3c1c3d0b0a0a5451010400c1d103403a03140129503144844c1d13220702800018640098401d65120b520000c00d050b000704000703400420000d02003007008495190030090340005800d8055020030800490080c0c602e03034100311301900100c10104150311448034094003c2c21144100840c42d400e040c0002040340002d04090112002004550b285c148240d842288447d01040c15590001e00101d48038813540700c5d842101d4003072885490f600e50f641418000c15207802c11560146400794000c100510200d100ca0055404980311080160840d80b20 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 999537931 1250 999536681 999536683
    0xe06010c06050f0732220b040905010b03010609150927051f0605070c08070e0415050613020c19061b020a21031e0b1e0d030c05 56
    0x81034030181565042005014035541d54080c014040c0500d5140c010703054090030012004600b0411000c8a0540001640b00710919507400078580d600550041c0e81d0904031003a00041d406945400070103450602080238400d6000900c5402e002d03128000381d007821589000c10090076495607000b070780c0078507515240c40070046000301c44280c00340207102c4000b40c0000e10341407011079005421424241550400b40416800821402ca00011484074100038140c0707400c0400c25580307036019031000ca8841c04070100004004c2c10501c400e5003d4103461004940f581400d050090391200d840c03040c240b019144c002403040640c0d0b51403c014a0018650001d6180d000f83c0d40700d203082111040110f200410010204820840282d018142c8052522020752a4140d8482c040307035103001a0744001c00c140e44148103082c022440c44410450460186400711345813203404240090104408a041092a16413902e0052850035001c0100d0001d82e8115071582c86250400042c65412450340c044c0901c009007440c5428088 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 999539181 1250 999537931 999537947
    0xf0a09020a050f060739050d02060a11010507030c0e03030c0a110a0909120215010b1c0e0109150c03090218060a0e13020907092306090a0e090607050c070e0601 70
    0x24100300010022a004440010b6520440c1e06007004c07449444505029103e091b074008050b180042d0450022880c243e00780442940320038884014010084171012414a0034040c0380e1052800c0c0d41c02213400040184041d00501034284081d221f0b420038481c0d40400e070340004542e0150b0760800e490892201042c80800c200015903004210704a0401071848140075490001801c0208942d007203409642545030622130f101d9003030040783e004845c100204000d21075041200007182603141000030b404e91201101e1801c48040b002d089039807003004d400110fa0700e115481703004003800c800d090900c07840c89954005104900c11900d02760101d000000400c041c0e4842c0341c0c9000140c052218882c0c8a41401142208156800701040740701d0f6450710300280260707109425100481b81c10600682003000f06003011000a610300840300d4000000780201c100700da6030300c075143c401000d01145142c02420100441814808000d1024080c4001040800120400041d0202c100d440e03110214141d1384480c0c2c01220082 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 999540431 1250 999539181 999539183
    0x510020c1e030102160c0f050d11030115080d09232806050c010c0306030f1401090b13140106080c10050412381503030d050f0f0a09020a050f0607 64
    0x161011131241d480c041c00c802c60202c81030141b0440c2807004e0703070742a0003002000607001b12078000980741d10b04000503118280d45581c41d14020000b04613804009011240b02070903601c0307401241d010b0750712071080a81004480000c0e101c00e000d200d05400c0400c80210b005210f0303084460140280ca50442c50700340c04440000d5003c00c0207890030101540e50200180390b504402e90100040d4078120020360707002c1c0030f48039850890b0303070103400030740800345d540c0b1451005041504101a80c0d502c900808002a40c00d400c034901c5a00c500840740c52801380c50401e10807100701104c001025a15010046c043d1840001d00710074400d00481d00111006440c003c00c0f19140611361042024145042a0808100350385500c480e0952000805102004185000302140028901c01440c0c40d8458030100390340f41c0c200b4544244d03010001c3e04503032804444420f04012141d045a100c0f42c1c2002542c140304d900c2c0604030001d90042c21902d0107004501ca07e40000301c0e48180c034442c1621a0040720040d106507100e15040c1c440349 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 999541681 1250 999540431 999540433
    0x1501020a120503190e07090f0e0d02160e0f13170f0a030e0606010c11031f090b06030d0801180f1b090b160b040206270a0510020c1e03 59
    0xc1800c030019102c0d40003034944d03a10842884690500d607002a11460320400c20000040c640a03103416801c2008142010101c00803d4441c80c901359081d004200101c85c02100342e0091194100381012200104c44580140c0200140e2a05005041075070700e005a42040c5018000e900c80c42480ca0075001081800f01ca07920800c4c408201c0d0a458a0b0340d0002d007003882c01c00d440c2841110001104071b51038000c02c60303a0602150300740900401180c41070b00c0c036850340e44003d0100d920f543c0c44004224a00a4544490b468058a90071400c0800454003c0a0741281058009050401110314040c0001605000f14900d84084000e4403411107626000507200d050007207820400000011540d0007000c00c404549070224191841c00160940341c0b101700c0702681c044889040c204075050707654050080c40580140d070f024800380020031112044036880e080c07034000000c1611a8016036814070400c02c1540d030207103100740c0903005c9004542d900032515034030f401d10803125900340591200220b262070302e48443d01601 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 999542931 1250 999541681 999541703
    0x302030909131a041208090d11010612230c0d201f03050705030114090c041a03090709050613090f080f09030129011218080d05130b1501020a 62
    0x20f040d004504140641c1c0203650244446110f09410340701c0881c2610070402503071100c40c09190b1684110946822008018001700d030f020396072101e180000e11201c4042d61448204541000850844040c0c1c1401700302c0b210151115015120000c1c4071a110601c001d01029641c00d80000c2c0441c0c4080006140c2d040206941d22603074100062000301b500c1003a400c1c001c203140002040501c2d01030000d0368100c40a1030140550155042e05125400d1805000100011000d0002141214020031246880d4401c000c1440c1c4a141464040b45800d09591040d1040c40c980000e020641c2c842c8101001c410105000c00b02d01b00c13180323141109809199410260030100301040418400c1c01d82002000718000c110003e214909041ca08030840c1c1c50b00704001d8110440f080101c0c12194040d00c404802503140b81e0b0001910000b00740c0749401c03a0100b01c000c480c02c0030009480d04403600f02d0310a0a400c00240409206e20404545c0c903020078040250880108000d105505040e5a100b0050703c15140e07071010140e24 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 999544181 1250 999542931 999542963
    0xa140904140f1806010533090109090b0901050607020f040e0f010c17040b060307031a07140304111509040e010516020d0f081003081303021309030203090913 69
    0x281d0740003919160058041940400c1803510a44440442c2c01c80b024080c0ca096440c0c80200003600d030840d0001c81c1ea54003c40f0203124644100c606a010b44134091112546d1002071000041280e246604040b070300524042d00161592900500390741540c6068070b0301a5074620600000b61051fa44001d03180e4091f0038100070601d64900459886903050a05001380300350342181c00d094880166103800b001c8991031400026000c42c540c0310b00c05410038409000c3c2d40000e9140d0f1124125014001810101320b010003051220707050b0f1000e1003852075003e111213a802e40c02c00d41d80d00020304080c0355a8600c504041f030b81c174480900c5540304441000d40b0007002089039203111914a4040c0c0801c680d0b48134aa50040989848540041103004100b0401e0703445614941264005480b03604d40030306a0002c20519000110015031503400a2540761068040300380540e28500c10001210407000308415014100341d00480069000800d613a4001011140d4855960301c010516490200c00000500003100f1038503051 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 999545431 1250 999544181 999544211
    0x206060f0a0504020d0f1d030f0a090b030a090519020d060c031e0501050a0b12010608040c03141b010e100e0d0203030301170c0906011b1a190b150a140904 68
    0x1142d03140c1c81803010710904091000501419035547d00607030143d0001c111804102c00c009000301020507150401e10308160b211442d207803150f041250720200f0280c3d184005400c2c03110421100c0e00400c2c03503601e48511110240e0200d001e9100c6404004c111a4130f8100036891a8081d80100f005009800304804100070840c0171980504028410300d40280071024000c10030140f400112800352000428080d0a07920340002103a1b1032030b00034000d44800c0400b07080400001c03007200c80d1001c002c0350321004021150402c04904404c01503012100c1c117100d4224050310051b201c545d01184006500d0800c0d51116801902103040d8252030600254140000030000c140804941d14408840c181c440403107405d00c0c1c070902441854401a212140070810040c1e01c2480504107020340345030213203e0a400f000400c5007254411421105a03004001200c0f071402c854140e1045116402c0104070446540c140700c101d02a0402003446007082107020000310319410f10701c9088420451307070b062901130b0003040307540000c2d1030311 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 999546681 1250 999545431 999545441
    0xf02011e061403010b06070206030411030d051909050306010b0f0408012d0203010f030b0604151401020c030a172503091d040309060513050a0b0306031c0206060f0a0504020d 76
    0x9030460660201200014241445040300c00ca5006c0c01703d1745020740c1c503001c00407160002071007141c0e000c014100250144e101408207114a0290340c0ba015140c0b001c9038848426074406c481c429007005240340c010802d0360790000d85a0304540c00504040c1c0d84203886080c0b1841c0c0e100c0c0d9004072506608085c0401c01030b483c000e07512249083e810301c24481c010109a000d0081e40300038414091009a24081800451283c800443d00108010800221503039104a29100910940d000c200801d1b503c80c880d0a1550f0180000e01e02d280b8100c0103000710003c44c2c0d540001c007001c181c0d0411491203021030300f1200d45203c1140645480c120b05080440304049140c010403000301c50080c9503d40c0d00c030104220301c00000c2c1e050b850140d6410307202d48030b043d400c00200311800c2c0c000c03080e0701c1401514020000740680368034400318041c01d100988190b03246041d005151615920101c071040100303141103160022a070200d003507a0010400c4603200c000074070040005154515a404c035980c86440080d150311021126404 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 999547931 1250 999546681 999546689
    0xe1219030c02070803070303050604060504390c060905250f0911091318050307230d21050708040302010b030601051c0f06090b09011802100f02011e06 66
    0x3052000244441d0100e8859400348943c80b210351040c0100e03030029020ba082140d12410140000440c295600c00050940d000081540b00c01c0e10800d26006280d1b000c10088580710300c01421a11100c183c0d03100c000d001c0104044050807d0396100030040400c10309210310b110000b6007245045e960041c103248040c0134500b0784622103024100140010b0b111046000755811034035056440780c1415051810700c0100c107214109070048540c0c40c2000600024440c11009495020310007c41c1c40315046e00d42185603012240c45049104800240341e410580c00145140301c8282501d40050524051546418103540111402c4051810242084165684212247e10650080c0e0082c00300c07031288000c3c152585000e004654104542d81180d006401640708940d03003191242590200003405612203004544a1050486803007800405000c200c48090042003e2500c0380020080c05800c07940c00140140c40c0701003075909000700c00e00c185c00141c2c000e500c6003a0000c40d0220700c54012200f410503000503c07031401 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 999549181 1250 999547931 999547937
    0x409050928172b0204030b0a0911011d100809060a06030c0501030c021906050f010f0803040e04052b020d0314011a2106100e0f01030e1219 61
    0x940e000d01c1829200054055400a200e01c098506002d2201d05030351010107440d1506007605204a8002e6000140e156440f50002d03005841d00d0841c40c100041c3c4102500c812803142c14018081c2c0030a0f4504140c04200f0003d0804211045080c44600d0450038410141da82c0010044042c41f0700079084180c8a10540580b03048d101c2c07964580000ba07084a800340805840c0c001080c5040c00a540241d00c0b04e0220380d218011100080c019036040d10a400c0103940490310140c495040c054600c0e84031062a001d80030081000c500705090148403a603902030341c440c0c12680715405002c581070003400e011529500b003407009086403481400d04000103030620080c40c24014410340c1340380040e140c403031b218166001204229441050b441d0001c1c2d000d854450352140c810324a070400900d0145032004034080c10314072904400340706a1502c403003001a40e52f080b03664102071211210303c0180c242c0d2144038080541100b401c000500001c2100414506090540d511503503c0c1e000170718101c640325404080145103816a = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 999550431 1250 999549181 999549223
    0x2220203150d0b0105040b150c0f0706110613020a051806030c062a030c060a0501091a010c0f11030304120b0604142a07080a0e010320030a0204090509 66
    0x3209102c03515548100c060041403620700140100e20306604545c0c00200c1c0241013801e03006a080401845e9442800f91144582c0302090503400c20405000c0c610040c00103081220800340060300182c1c42d5000106a12041c03002070060030210350b580202c5001400c0c0141500c0307040303000301c500c10002c6081600d010f4468400d83c41d07489504d14000040382e81001040b404c850041440895030b4004105042e200000d600050003541c812113004c03c1960702c0b400400710086181c0d45400c40b10411240601100045001c03030000c140500c0c1d0300f103202c480406511440701007600700b40c0d0030010208240519a540e01d030000180001d003040400c00340220042c040c200e41e0800e0b44880007084101c03201c072410f01040540c0e14000441c14110140058015000c140224045540392188000180d1004078110341001020407040d4074558408003e40c1812400e0030100000350302d440c000016401d402001c0e004400c030010004a04800c9034042d43c004113042d2600f40005d042042c800742c0c4585001e080030240d410380d4 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 999551681 1250 999550431 999550471
    0x3020a02011508010b0f240706271109010b12040c091a0910050102071701020d0603141b01051611030a030804120516031115040b1603061d0402220203 66
    0x2030003042c0c22400c00081f8001024500100005150413250064900560354103070003000498040c0000003100c48144542642d0081e0300d0310803100150042c40c0c0340103e07440c0c40140103035514070081b61800340c41091740c0c580e2a81c9525012002c0501074021201060800d02440e003c8240c0f5110088024002c031000714070b0742e443c441ca03101c1c204c1c01c81c46402e0044e13004020800000c41621901c0052403090800580760006205103601694860350003120b000c7c0005002442916050117000c05200031447e61004071031529000034904e00518014a01120508207003004000b0f00b000d10114075900901503d043c03620604020b4060f580403202030780c43c8010082030034001d034031071400c035140c1080341b44404071040215101201d09001d81011040584203500c0d0140b6046483c82407203106a204e0401404145001030f880344825410315510b000307060074484144020f62103104171010080300c408a000c0d80366118000108030702d401c1d64540f02a000d00514640b0f800840350010f601c903290400501c402510340c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 999552931 1250 999551681 999551689
    0x8010e030702131e0c0e0906090f041b0e090309010e090705030408072409030225030227190b061614010e0d020106150203120703020a02011508010b0f 66
    0x3075490029807040f502004020703082c003940c0c000d82c2d5850b400704e0f0401c401e8280c010400c04440c08400e40c500421603851032500c141c60000741030381e40010b0545802c1c01500b040c40d489403101c500681700034422002c0031900302c401451103001c00001c00d02414050306508001401c01c0d200e034840c3c000a400141755103012034035070900100507030040c12140e85041c03a55460381c4582c03141e50411502113480a021a1540d103406800c5d20f0b00b400e4221100000007496070f150329001e460300000540a1168072090380d500c05c100051300055004072038060360010419400711a5a61486219004a402405032101400020800030748040e610480c0928200000f00c440e004011030b030300a502003250924003400c0e1500020b4041501100107040a0001254200400c49000c1c100711641e44106c0040c1c0d5948010001e903810404082e000301c1d502d00245140c140310b50078007903240c50020000e405141c2c00082e6850854400d6003d00441009034003410001612018002e02910300844c0c0d0608ca000d800c0d1010710a450 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 999554181 1250 999552931 999552937
    0x110c01030903050f090a12061505030d0f0e0a0f0e04052b0c05070f181103070f0f1806032a021f0906060b070b0a05071d1c050708010e03 60
    0x30301a22211309048000508603800e5104403c03040e003114082c0720000d6446048010b801035980303c0e143c00300d03101c02c920700000c914550680c4024032035403284881a21407500301144048949a0707140407031000c05201d010a01103801075000c0d4030800715100b00003c0c081c800c000b229000307900c1141501d806141c2170850380c0803902881503080704004469100c0c0020350299000ca0b501074031900c180c1d0703100d40d90750704000e1503d0465404030348204040d011800c1c3c2107040740f1030f000310380008052040c10340c10310f040d00410760505540f0900511148a071034815140c083c0541d410b0f1030503165100e00c40140c1742c10004000d000103026504440b400300100d0942400b40907150680c5010903801009038481051a4100345e115000e15500740580d507204bd85c0218072a0301850002c2d16011405642d5480309141150143c00300815540e03405141105100140381c2c0244441d4862068241c140382014a03100000c00c011561410503010f00c0440481408020001c103d000403507240d40004c0140f1008014000d440e0703c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 999555431 1250 999554181 999554183
    0x40b071b06090e07201c0507050307030503061912140a020f1905040f1506082401110102070b070216050117070221090a06030204260319110c010309 65
    0x41c0ba0b0500c1800b8640700d010400d0b80c0f140c503a01e4800e03c1c0c44d207950354010594000000d192072540090041c0b64003c8508800181d04030424a411464a1000c0e10781d00d80b240640c0c01c00030200040040842c80035990581000203080102040e118031503500c400035001c6075240c0004840c00700307100360404100300020031414180d5402404d084604108a810054060982540703130b129a0003459000c1020748071842100196118028002114006043c0c41100210541e020b03200700300c0c080d01049480c2100d101407a84200700850403005081503100141c0f843e1419903814041580f0104561060110b040d040f00d02914898081d41c280f2007080c4c000c1c0182d1001da01506010a480703000c80c9400e018042c8040364040703214030503103112000000c2e0700303612802c0c04014030b6070803080400c1d05141803800ca0400c03c001c04035420110320f064640b179070b00885881030942c040070303000500089145004050040b2004440140500c2d080d18003854009002900b02c42c000440920903040070040f554020312600078030f1 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 999556681 1250 999555431 999555437
    0x4050601080f042102070512010e12070f022e08060f09090a2a05031b010f03090813030606050d0c051215070504090c0e0f24040b071b06 60
    0x103565441803180c2c40b4902600c22928544150ba01c0803003138000700320080c41044a43d015201540c43c0c0310420035601c0c3c0d00c80c009a1103906d001c01c1c0c5003d1520000e001c240c0115007009054603441c16003030000c6881901800a5040003084040307540680c412024084050488c84030715540b1000b0100c1142c0707121003110f606030804e2550700c10381e406241460302d4950203666403048070184680f590710175001240c0540c008880c44002c00001c980c2410042030f00014217001d600900d4044c5045d41c3c03884c40c001451210506016110003c061628481d030044650380303411000356a640e01d032800304503203e03405610055400301c1c5040004605842d04000c9051140c0c0c1140b070254181d400c1c03034100400000c00a4807040320784101f0540c030232441040305a59119940036110f450b00d60380303082008026207040581d19030422a4021481d10240c0d030f1a00142d50315182543d0a61302002c41410580f00c045140610744030700c401c00f140001d06090300600400c0542e00c10305080107400100f809503844070b0b026000d44008 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 999557931 1250 999556681 999556697
    0x1205030a15180213031a042d0314161104060830120f07080906060d1211030c0303010f061b020915060d061a0a05120a092001030b04050601 61
    0xc0c412803034014014036600e043c15440e090383d4a582d1901040d8001b100c09003400c20300d0b8100421b01110400c60030f800100f40f101d001a003040d000052a0801400000030140f00c4040c080804840ea0f15081d554001805130790707048031010f00e09015840b04001e106c0103212b503080041c0464980780c04521950442d00952080c4103000d80d84241640e850280140700c0700ca050705115254030303148000d075610700805031034038030a02d18240400d000b01504001810324016602c00c0d81809455144c2d421500d500c541c100d8020115091100350444444185010000741440f004c03e0005505801000440c100c0711141000241143d0b40e0f603054500049001489407240b04100e00403026041c218031031a0720078065400c11031540005e1000420a410080d200024655151001d10122031040501303640100e00d001001d0401c654800000c1692180403a121001480354000c918200241e80100c130200ea446000d10300044035580c05042c80742142184240002d04000e8915450704017840703143d0080006a4603205 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 999559181 1250 999557931 999557969
    0x10e1c021209102a1506060c030309020406080a03021515100507020604090f0c0e010201050c160507090207120306050612010e06150a020a0312050f041209031205030a15 74
    0x903920111001c0c4800b07002d00c0260000301008a200c860100b040c031038880040303404c4c85003045029003800c2c1c89044203161600c1c1050104941020b805010640d00d45000b01d050507252000c64013070310265121050900c1481400010180c0100d140015044c054000c2c1d80d00d036690080c000b5222180902c03854009400f00e50345202640b140b00200903190000d0401481d0990b00c2c40c4140465040301b58103192940e50750701194850358002d140c9007d44000340300912060070403424405091107001c035000c1c0c610f4600d000804c1040b20501810004000250045482c0c900320f05080064140780c07003212000910301748000c151407034207800342c40c5c010140c055007180e035a0812410031050840a02565445000b2140d150740001050700102030b00742e000da01508054006190107070070304110794480c001c07407402e22040000c90812000d100e41c1c00790b0403007841e0341c03a003542c1103041c4c5800600e0f0300080c001d188070b8400001c2c000d421070000c5015040d02030082216048068081490350309500640200070120346041c6 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 999560431 1250 999559181 999559189
    0x1d01060509060d2409050c03060708060f040906050a020a0f050a08071202160818120307030c0206120109050117010c0f05090117100303110a0b01180e010e1c021209 72
    0x2419620881042d0b1044c40f01030007607410468040c0082213019122041242000b0040c46401c0003188103030014265424503030b101420440005180742e0203904800e00c12a4250303100c0e00840c6c0b001d03420000410140c244044000040d600814085000c03c008003029601c0d240300c0d208458488000303560303000c019152000103c80b040d103500c60200b0300326001e2050070200581808a0000c05210380011a41c2d03000400189012942110350107103e5210940300c503040d108080115030003e50f051603d03034905101c03840001c1d0980101e2100100c4d0084070b00001c10040402da10141c10703100101520340d11a590300c84e0301420b868040444100140d00c96810700300d00d9000360090079021a05041070620701621007071b0007886500c00c542c00e241d0200c0900b010024507800900004202c012036024050f0113850b51100310003030006129500e03002d00c9000050782040c3c459030248000f6418a0700900034510300301410340d5120703501803000c0509194035250030091400020746c840c1c010f0364021302c18203103200c1c10100 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 999561681 1250 999560431 999560449
    0x5070602210606070f06052d010311030a03021002090102160e091504020f09061c0302010f0e030a0f14040f0815151e060408070b190918020325031d0106050906 70
    0x8280c10030204a403600c8182c807c00a4402100c1500301070b1230140d0314609220318071f049841d023070902941116000f00082035010941602803c15801c015a03162403000c0101d103849581240e490300c0854550700407503070800148005005000400c11039850360f905034141064448103aa0085d444618162508034034201525070790342c01b103801440100c0d0070090403812002c914600c10102c0044c0d550b042444100403c80c800c42540401010041d400d1041c1c262001e8001107800341008107000c8100343ea907640e036400c01c007241c0c00341c0110301d5141e0901e0758406c010741c9d442c0300402183e601c14800c41d0000f60540c01c00ca1689400502c01803d09241045102c41188229500c1c000039400c04010080400d41000402192000b441d80e5020580d550104103040100c0f2030307448100307204100c070061040100c249140c100c0c48201210040c0103989032078000c0c0d03020a64030942c1c01200d0741c01c03100401515040d0584d00c2003060b003110111100c403451300d05071300c24200c03403403401100c0d408220940812144d0401f6000 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 999562931 1250 999561681 999561691
    0x9110d151d06010915030906050c0406181215270227070c290402032a0402090d0f0b0114060c100b01261006020c0a1505070602210606070f0605 63
    0x800614102a41c44c0d18040c0d409c02c81e002800d032100014100700480c1c2c080d5540ca000444101c003041c10501303001418100984915002c1c00c141120070080b809030865a1003d8040160600c01205002141e14625100c001411090344240034200c464802c400b0004100d00c040350201828142983d101042a100d10000c01010303210003141340741c0202c205071508d40e1400c6003940b00c101e0b44c40b60710341441090714189030040003031405c8414907558921080310856043c816002210056103440740000881c0c10003865840c050080d8500c200c507174013885500d580d860f0582d5541880031001807084014070082d0300c02e80c81d5016855004203450701c08402198403503640302c1014584070a019280d001c3c41e9085520180e61407071046130900510000c01c1c5000b02c4e800003800c00e400540b5598401100203080703500700e2310806000e0309466800b411018410000c40b800550301000440d1104280404518041503000b0303c2d504500c1c1c954041f42840c40c0c201d040d00e01040d405800306950b0f20055850001400700540 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 999564181 1250 999562931 999562937
    0x42109140913020114070c03060203010920072013051501030e07030620030907081006031e08040f0b07140105131b0306050906100f080709110d151d06010915 69
    0x41b80c0300014080d022110010b41c0a40750147c0c607541000301003012111000c046443d229040113102120142246c00d9400303c68000c08510f903084000b411301203154180494083e4082c010070103c0031000f0b45903022900a940446100903800c8402c030040d8200c132503200001c3c40690000300304000040842c1c01090b10003c1c0d281d0442c40e81401000207030550740050381c2c1d103034644c5c000100c11f03c540381c0100241c0060480040c0e0502400b8030795206c040e6085010503030b0b20900046900d405045c4001307074046400400640c24003c49d0550f480d100c0c1000303030700000c4045404030340414071403100d1081405414040e03c8084440c145070381325690f4200304025044450210307040d0840d00000415aa071141a00c94201c0304003600e11840c091014840725001c0ea004060f1611408a0034007804200140d044181d400d00100014070f45400d034a01e02c41805056112144141420301e0307042540c8010030040111403810000c070302d0480031007118200a4104880581c00554418020412281600d45001d0004280c1c2 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 999565431 1250 999564181 999564187
    0x90304063e060106120203040f0b070c0219060207080d0f1d1f0806030d020c01050903010f1109030f011404330e0c01020a1a042109140913020114 64
    0x126081c03040d414042a11009600700300300400400e42c124628140b034102803003045285141030341d10203c14400301035000e0108030b030180014450b113014200c40303030010350001c03d982c09408500f000701c6a041030b107006040c01800341d01d0f0002809540020944800d0385d05484407007108000c44400c5030411250a0107507118020704008680d96104c2181400541c000c07204000d50462b1203002c00f508640e8040c3c403050090740b100b103030001c015070f0114a51003d05401d10b401c550720700c60400007038050714501244820441c508502140d0f035a000100070b10500c142a81620f0000c0d01c050b000c0c500304e500301105a01450201000100042c295404a40d000014503a00d4641552004520300b1074070500b0070391444080e42c5500070011410100464200e0041c244000c000c8284949d603840ea5403034010440c545c080b014000440e0801610000903440a20800c00c1c40c1d401d00d0002c02d0043c0409403500c190141600c510140e4408da04105400350300c02e103405411107004508690045444050396641e161040ca414 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 999566681 1250 999565431 999565517
    0x2010f120203010b0a0f0e01080403081315050708060901081b150a1d03390d11040f051312050c0d03020403020f010302030103020a0b0a0e12100509030406 68
    0x1c0c4050340c040d0900042d119117800c04804054252042c2034400c0052103103005412841d40c5e8082036180c0d11507071524003803a1585500c0804900e491080c00300030200c40c5500040c82d0349a61581c8084d1251500d55940049500d0345001c1c851103000038010000d170381d0401d000e400c01c024503c0f2004000c164025000d00c4041d124442000c8075a00449009800200440d0b40d000c4e551144090003448000f04402414808000070440d9500d050309404520400040040740326213040ca40f90900c50300c01010b04000302460f041e14141611400c1c40f0074003485245410a00540b0140c584119813107964900ba1342480d4901a4032460a1082c0c6000039004000040020280143c0e050105140d50314885d00e000d44c480b41940304001d03a4070700120100b8101407051004001687d18800440c04030b544060040799103200004007203407042e40c0700e01016089038807014000b444400006042814200b0701c581040f140d15000340154891159100d03040c005611a86030040780002c2d250410b10307494a030100140c200f40e003 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 999567931 1250 999566681 999566717
    0x305040305121807061d011d0303030108242e090615020609030c060417390c01271e03030206070e01230d09080a0f0507020303030402010f 61
    0x8a50040902d0312291070106818020403215020308542e00380304162046c904280c0913500d0101d4032807410010b420b00800341070303140c000c075010142402606680da250f8507011801d50381c00c0c1103a40303035031910f0a00705d41001844c0190b00250180c80c501000c00d66040159100d007616000d43c1c46034100014540c0c00008920041d84030300340082c0038882140408800c20080a800e09100a021014582041040a110b014042180c0394426404010300c00032b11242400e10784240074041c1d06184d003401c1115184140d941021080c4802d103c0d100441441482595100351520f0301d100c68980400e03a081c1480d02c52031a44001c4040d0040001d04200b442d40d9242d100104904190000c0d20014503000c1d000c0c014186e05004096000754203041c00e07000511800e00081c44c81130314070341c042c02d0440041800700c5803d40e4881101c2109003411740c1400341e80300707605001c10749510003038120000c60343c071706c0290b0b84583c06501640d0140ea0010051420340c1d4681c0c0040d6000710040883c1c400b0803510b4000c3c01c0180384 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 999569181 1250 999567931 999567967
    0xe150c0c0616030c080411090c0f040e061201090c0b03060d050703110a0614030621010f06050f04060b03010909060617100506060f03070311160305270a060305040305 73
    0x2041100c00c00c40702c1662015013150000120482089415000c020100c0c80f4003881c06108042a12010050364034203684007054012800700866250000400040050520380242d000b22400c4034400e00e04d01214142900320b40c407031000202914150a020404007007000040d540c0120098905020744106580382410a902500110f442d2441901085000d0514850340d0002d407040e8200398001c6015203c518005010041c0b005214a08006056040400e003a030800b048002c503000030f001d00c00d002004400584800e006440c001d4520300e0411500f86824011642151a0445114510390800d0488009030a000409440c5151201c5002412550394030280b607a0000f08405843c42c4800322140400784e51014143d544075500500c941051001003004698202c0180e040004a1204420038a52103000e02c011000490b0301020445082c160800000d084030052000c2d402903010921485031070701603c9a6501d900812040340034007007140039a00c005d421078060705100703042c0b003001c20540078001 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 999570431 1250 999569181 999569191
    0x607080301180605030a080f04030b071101050c0f1605031608030a290405250f020f01051e1b04030f0b0901050f0a1112100e01090e150c0c06 62
    0x20400100402c020400d18145403448801d140c820300c001031074440066903a85003541c0181030311200007001d00c1c0c2c0c040204116001998040c2416442c0e2070081e41c041d007241d10000f14170a080d400c180c001241c011a0000319005200c3c903010450800d4000b511400d00280b07182403c030b4080c4002c010b003404030300d070540041900340c0c841c14034180cad6460010001c8040e40c2d07212103a9a1076044885030b40d01c00208568074005072240a4500080c0c0b55a003127003041d055140c070144800c00848095018603010391240c118141c481c066001c8407180c06c90051590b08842e0221441d001940c01030251110460030141155003025880020390340b0800b000d0f04440341c641c440d9004880d02d807284103501701040360b9482181d90000384080208a54a8409003040c2d003010020452882c0b02d5661070740764980c03030b007020541e0300440940407850980d02d01500341000d12545801401405d080c084000540300400d805598040361004025044408074040d40001d2a02c0240c404118148107000b1040303ca41c0800905101e0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 999571681 1250 999570431 999570443
    0x60121080412050f0c030c06030c0915190809030f1b03030106031e052502150411031903120f0b030a0c031b0308030f04030309020d0506100e0106020d0e01020c0607 72
    0x801041c0f4140340340102c0516010641d400040156a440d1340118503080c540000b690566900c3c2d454500d61001441007101302c0307030322000e8824410300e1341c00e4007405801c56400b10410f000c0c080128450070703140540d085072900c9441e441048241040200c01d00903040101c079000020200a42c1103c000341140c00903000000060384d03564881443c000c500d43c2c1c5001804483c0d60400a070709120450264203449030301e1047c020340240540003d1107100300821108444030303a90702074075030605103400e40c1c04d82c00b0800702c04d2082c4100020340035000701400b0804c01c22075140d101d0b039401000c0e50001201030704003144220142690342122702e24503101442503c0c1c04522808264000385d05510b000c1462054100700a100c8000340c20741031002502d42c4040701d41180c400b0400100325030707403031504a0142c00701060094201003101410340420000040c00d134020f0229650700301019858450303143c01c0600911441006070700001e18000d40600924850300c03100d2040c41503d480b4410780380400c1103030b400100d0880310 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 999572931 1250 999571681 999571709
    0x927020d2306090a06050f0409020a0f030605090c030622060908121008011a0103020705010f022d1c0b01020f010e3306090a140106030e0c0a03050601210804 69
    0x80c64084002a440284d24004004090618001c43c0c81c001440210350301941e591100d40c0b056660310038000005001c001d040140403500d80c0307001c002400c0c0c150340f046000e00ca01442070209103800700e04140b080704040c0b005201402040b4980791000500403017601c11586c0e44e907400c1e022840b441c0080035095400215404e01d4140413520100601c4141e0205030316901d000ea05840d4140c8440d02da40d503d0800b40b8003d07840350050b04049004101c3c4c135040300800d510004101c44541c405400c1030526108510b0984410032011b401c0703442c00d200710080600000c918654408100009a0201c8800c007018811079802e084040b10036400c41d20601c007110955404060386180030310720380c640400c0c0e113050001c0b00740b005814003814015145014202510861807500040c12000c2541d1000b46150002020322120b940d4808000e00140002d8045140300c3c000c42103039070007034141031459200700d0764072000a02d0181c0ca0803c24448120001c0c11807880074604400b01d201190403400580043d005090032650 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 999574181 1250 999572931 999572941
    0x108071b0b0c070b0a1e0c03060807151d0a15030f0f0f0b0307120b0c0f0f040e06040b03100c030b0301020c071d0f0a1104030b10060927020d23 63
    0x2c600c9005117214802800d05555007004221403030450b02402e071070400451140010b0101741d014201c0c0e03411907401c5114402000034100c80000130b18a2040540d2142e000341d540c0ca0945201d100d01c04001c16411a00b070440c00c020350031050b601244d40006078580090f48d980264840c4041e04c05185410410782d0f11081500c4981e00240714118151104030010031589140100d4028000498440504550000c1002030010340010003154001d0911001d00c5640303620440d04076149800500405c0c1494a00d98001001d604049c8284121014010700030004c407122542d42d80301a1010401c03a0342010b0700e82140011030b4909001a12940e10201d024105050528611102804a41c2c0808010100c51014000341c2d80c80819a560001c0f901d400c0850410003449081c80e180c401d581c00200f00040f00c004025200310080703000c1058a80e140d480c0c48950b03503201070a0f91000c0d061049261085407407284080d8240243c0d00800c0c1000180e80c010901681c081d0000e03142981c0e410b4080e951204040c2045 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 999575431 1250 999574181 999574193
    0xa0219121401050a021e131701061e03111201020d0905061e040201091401210c0807140906070204090503070f030311040f0b07020d05060c07020301060b07020108071b0b0c07 76
    0x1d82c0100d240c4c0046050140c46100030054010030013103441e848000203060480050103042d20801340603024521980001442d0a050091490703204078002e0b07040c0d200352580e51020358a0f60004882d0007074a0300c0190440c40e0b003040007550030071700d0140b2103640c00c00807450003607501e0040c039002c903001e180a071000c2d20b8a00c1113000003002184a9204010784038003000010b03a001004002a036000190f910048007014005948540300c08145030084030424804170f0319403001d60000c0b5180034540ea100003490316030709800d8840107060b10030344013113580038482244141407101c05445010b000400204200e900da0b1603442c10740c1d0004100b07442c0b0340c0d0480f03c0702c0c0a064160003065071207116441d50034034141c901582d0801c00d41c0303240110100b0362400115017040d543c840c4038501a19401c40181c9513541040b2030f018007607038440074089000e9420302000090b0320078502c095031241c9806840b00e441c3d036a9031031411a1005090202075030003001004015003c152507001c2d10f44030340c5000388070036030701d5280341000 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 999576681 1250 999575431 999575441
    0x2040501120804030b0705040b030a0605120a17130b19170f041202030c0f0105071112030f0702161e1712031801110703031b020a0219121401 62
    0x840180044000c5040c006001c2c401101c003143d4012248010645540d0400c940300d10582e488039110403004005e01c00d00c0c2c00341303901c03402c1195011a507010121480c1002d80341c0792419081c0190481c522102e84503810410b0500a009550582c0c03000c1c01c2c210b48481c0d842d900d540007a61402054400c070040c01817025000254100c500c0c4d044401e0040368038003c2d203000400d12004000400c0030003184603241c00d241c020400d945014180d1000c1e40c2c120480d01107624001d101c212007407130002d43c403250282c4603001d000c9884a1001d04640714645503035950b651004c40184064000d0045105005008003103410401e826000780003801094188141e0219010141c60080e80052621060100074010b00400010b100c3c843c100714413032401d4903659140c4a0800001c0c4400c42c5400c0d65090621122000c8800001400c0047c440d0301e007004003208011075002d0051524007042c001d648112600009403400f45103101105508040c2494690784a80c0310b50f4101002400403038402107640d034003003444a401c0c010 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 999577931 1250 999576681 999576689
    0x4060906081005010507030302090904110301051810050402060c0a0b15040c020a030c02010e100c051b090f2a1b010b030a03030902030f010e16090b01051c060e0108010902040501 78
    0x120050728104080b4402e52502d45200e401d040c024001084410140603405407000100b00518400c2d0310310703290a14400502c0c489050502c29460840040c0c41c501d901080c07800c3c0480500002c0034a910035048420040174040c00681c1c0c0400d003807101c1d0840700c0080226510310b5118039200401e134200500a0070101920258152107581801200c058241c3d0000d400c8024a03014a070017025420036000588401154104140d04807402c817580308001074008803608420381c45401121030b181c5042c0070b0707010030402050302207a03c40d0311400031449000b404010160440380700c80c5030051080e0140008464940c1292104440340008070304005080c2c010b640090b141507482000303000c003020305000030b500c0f150b0b214070003024940d030340c06a5015910104485a85030425000802880c1c0070f44d84070a940d405000003001d14401101c102090848460042944128041e100c084c1031542500c03000500409801d811070400d1303a21000050b020b0418211076008110350b4000017540c0207540188010b440301608 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 999579181 1250 999577931 999577937
    0xe04050a0b090a2d0620040f0315020c0a022202030a09030e090103050316060e07081615020d050d0e12130e0c0306190b03070e0405090105151c0c080304060906 70
    0x1c071130004031500b400c551340d030300184c0020900c1e04007020043c0c0c0140500c10405c111004100880e416040043c100c0543c1c2c0500e5074080c18003040050b200580c41200385441070750708444802c80060402d44001440c400a081880c007050410281e0310049030400c44090048980300e00550003415003003070300c0d0400c50000356541d140540c155200d0759603e105691001d00200f00c0e00100030b0070b002d40c039440300c1c200341d41c0d80e4155040701e51364000c0c950742d403810075400c000b0110321200c0000360707415a02056414804950068140001450000e6407a0b410001c42ea0710016100d00656010800c1400a0700b5134010394480c0d01d131164040b50200c0400e00301c0d900029885e110407c2070040070b681d1801541e500000440e41d0b60400300e526214642075070f4a44d032000050030004401c0c004017580001aa071402d040a4400701b2460769205641400d03100240c4280c101044105650142c6081c03400c040120107500c80d1982201c030341555180a8000c40d41d034440c00c1142c2010905012899018020310000d202520f = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 999580431 1250 999579181 999579233
    0x9010b0901061806110c09270307120f05091012180201090b070516090f1104031a0604020903030c030c150105061615020403060b0310150e04050a0b090a 67
    0x240f4101001400c0d400740a09203c10b0f0490109098402c0110714580a40645184841c0c14510100862580400300000c030102490704050f09107040001682c0300150025070f001d2048002c142c084d190302c010045d0400800500b00000034558803004a042c8000c92955111000300050503070010803611007002807174881c049100e61501607a845150315013a90148080705607540000e00d445881c0c10340c00e00d07181801981c00080080c481d9101d80c0550707110b088526086c0221083c4140089003032203a40801000301d079590044d4480d41403240380f0aa8071820252006140034900800a4616002194008840d900001e5402c507080400e1000c224035003000300d04e29005504100010303d45000e109080700b141910600c40405201541aa002080200e09001c560792a03c90622102600c3e5045c4100e001e4418040964410b402034428540441a0b007640c030400581801100c0a030788102030004d03191407044180810100c3c990506050142c507408008213100c2d000c6150082c804883e840c03945c96485080 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 999581681 1250 999580431 999580457
    0xa03170307202d0105040b100b0f0301172107200303071e0f0c15021209010c0302010e07091508070303120504051903021011190e01120509010b090106 66
    0x81d5120f4051862032602d01110041c0e03040a5000b03424a241e80540d40c241824042401404500180a04d105008240e040c544640c103610071032045088030910401701300010801100310789003529083c2c1101c170135900030035449807030070640441e6254031070005400007034444100141038801d01c517140215501481e0680030900041c0e100e0042c071601030b01d00e2001d0900c4201d072a0075100221401039110074080940052800c0010a0210704e0150036502409a050b4006003400001d030007545012052049240440300c000455140039149012820341d074840f49504440c0c0400c0c0f05036006408a01c0002900190020ba200030240c510b0f4840880740d0400320040c40801d5100c040c221000d000e2000103e902e80711480c000340b0b040f40350103008542d0301c5100700210400d54049004081041c0f1140e090001a01c00c0249020500c6046002c0c6010340021000008982c010b1010700d04000050400c8000c0d000d03000030803420386504843e0040c442e503441302d55010310320302400c1d040e000d02103a1405007662010 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 999582931 1250 999581681 999581683
    0x30c0c1109060d0605010305060403030c051206060d110c0c150c071e0905040b060109150905120102161412090612060604051002060f010b0a0f05090a0317030720 71
    0x20100c96000e0030a2a0004001e074451030016807100e075010000304220340c6c1d2800c1640d1500d4042d0b070214006418070100b50780c90751040041d0b8105224208400a540c0c0b02d610030800154010008009501d84442c2280314454000e40580200d035a00030191904003003010811800d40d02107030b81980003500c01d0000e80c140740b03800104030301550b519000c401400300c061600701c0d9801ca0340c0da0040c2c540740d04000800c0300308091030700161702608083e00e03000c01c1c0e1511401209482d005154a600014407030100420041c980070b0780b00e101c402d45942c00103240c007500320000d100c10305440e071081e915000003031300054903030b10200510848613110f002c00d40c0c1001c0c516400181700d44140a4040c9036012520302040ca242d80e03400c101c80042500904c0300707a200140410103500c03081c080325410f882420040000841034201030480d0b81c0c46039541e0f10014440000442a41c00347800240c4610341104651070b0100024000484191041c0c4440c6249522442c03c0c040c002e000082a2891000201c02d1500311141060 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 999584181 1250 999582931 999582953
    0x5040b030f040302100c0210050a0b030307060513020d03020f100b10030c1110090c0f080c0607030e0d0c031110021b0d080f0c0708010b0a0e090c0d030f030c0c 70
    0xd040459156460b00d080880c0745c201c4000b400c203402890150601d041540000b00b03001034185194003845070340d40f000d144030200c44800c003015806810400c1040005681540125030004900c0c20246211000350040756031082500021405a4400c850102940ca0308018000407241464014401c00e829200424180901384240c2820715445aa8000109014068022804100d0021070f107602c12846407400189c620504140c2d0018000c803400300d41207428150900030354000e84000c0002c81701000a21004c6d9110120950420510130709040960356500c041e4104c4c1402a03842501d000d0860906a2500c986c40b0f0610303101340080e8101036031071034001c65008004644206140d01e034051900c003241003900514070052000d14002956208090b21001a0081d218808100c0f000c0c2d5840c0d04446007210084649590300c0b040b90001042400d1401e404d0551002c80728095840c0c411181c0c000c00c880122002c8210046106211030354031407036151146d2027081070a071600e024028900d0300d9001c1074074 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 999585431 1250 999584181 999584191
    0x60c140903070611010e06160906180b0f0408030c0606180f1803040b1308011514090709051e0405090c150a0e0a0803070506060f0f240d1a0105040b03 66
    0x4000113860600a82c00e6010080004100d800d075016031400003c0481d80301c005541c00300100360400c0000c9040b600c102260540303100c07103403881c0e88010300300081d81c031a58001c181d9034400902d0401000c514220103001601e441d0140400414160400804200d11005081c4c0c402e2400301e0721300200600310442c08003241d045003450311401d10111000c00c20508520441d0400d294860000951445644480403a402103885242c020005101d542d414210002d00307034800d9015015440c0e8400d80705141030255075401070010300b0540320581d5124045040c00031010704100c80a40704491400e130381d04003170080c10b074004440d00161440e41680400600005010030302c0035440ca0740801c012036058000e02414150b88801040005020f81e1170080c40d0f070306d60010400b12030310301900c0d010803000e0500349800708100e900244425040140b10702840b100c4031301d5100381c4607416146004000400031090007032160003540400400e9508051030005858146078040e20b0400c0070030041042a512500c00f42e0780c0ac1 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 999586681 1250 999585431 999585437
    0x60607080a031d0106030309182a09030204180203100b030d05090409081603030f0c05040504051924080c09070f0e0402040e01080c0a0b0313020d080304060c1409030706 74
    0x404404081020308020200c2420b03e90329042c070100505d078102d14030341d0440d50391703450914180d001114100162480a140d290303221111034a10703070072540c419154604024452422003050796981c0c00250030307155441e0a030b81e40f03210030482640946c2428030903851181d08101d010310a200c50074001c00d50743d904140349007040007008a0703414960340d02d680069040640081910751034544007400038521540c86001107010901c2d1a40c600c0d100d154a0248603035015030742c0c0b41c07903003824600818800641002801090b000c103c01c0c601c1c0d88030640398407401c007020f0b104085040c0000045040040a580c1d1a00012410361084601c040d050743d52455080c0e02507154a0714498010640c0f8003070b503c1c4503c1000096003e4004900400c00303034810061a4121030002c000c9601091400317083c8903490019014807204c000ac00c00001c1c50040e9080107100e6464409003203200d0402c080d440d44240d40e08207032403c0b00c0d00f9441d40c011030102030344010811450b548002d0454904081000025a43c00c154456035040c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 999587931 1250 999586681 999586691
    0x3021005270c01091e0b310302060f220605040602070e0f0408072103140601110a0305030c090a1d01170a02150f0d0b100f172208070b060607080a03 65
    0xa2540d507886078401010a001c1d070310749440c4487c21600100c0c07144090051400610000c15900c031443c40741e03a000300d82d0060041d030b04d0701d20303041d4032080c09134040e4500c0300c4074600748510100c135000840004401081c2c2c0c0c2c0c0e140e41d19035082c00002420700925038800c042070715192090115441c02c8103000b581041e4011341c0540d56039042d251000d4503840866811044142c07000d08902020341542000e51384502001039051b81e80d40701001074540c40100341804003030354849865400040e010704021034000c40407240a600b40846440000c07040b0300d25800ca2420000010782c2492840205241140585081141c58a182011005031551441404000381c41640044603c0660610035000c4031603d40300445c44076a00c90748405100082c0c1001030000d401201c02400c81c010a40c898544c0402c00c24540d902e558201003100702d540001c12001e841f01c0304c000b4140e444019108203081c0a040492311074291261070f4981c600380010a220700a200742c2c01070303000304074100009002c84111513000000d400c0c0052 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 999589181 1250 999587931 999587969
    0x10606030c080c2b060524091905030321010f1a18090103050a12021606180e0711101a091503010e2d06011203021005270c0109 56
    0x81410055011228404c10300c1c001c200c0e041640c101c0c60a0b503c0a81d1804022400c215070700e11800e0301e40144048200701030094601610741071540c1c0031820300c4407202104260715480064296400252401002d68405800d03c412103142c00c0e100380104a8284810075982c5404500c103800303000c2c80311107549000001000309208403541c80c40e130004440034291a10079a140d181480d43c0d0704ca112015142c1441030005825030520001c2c0451110b0580e410200006190003410349010000b40b02d4039130b28103c5c1d200081841e00b440403550b0b2240342c95079140ca100d808124202418051070000000505041c940c0408004038a040c40d04409041aa8002d2032541d4514a111108403807000169055007414040b1019030400112006000101c44260301081d101e081c2c2144902c0c6d2000c04d202c0140c000b51b004003c1984000c2c1d8003a4500e0080c01a1001120002e090308122041100d848090030500281000f40d2600f500613100480008001003940c03c43c0c2c580040c048603403c2c401c02c08140300c0707001116 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 999590431 1250 999589181 999589207
    0x10e01050322080403060b0a06092916030f0507030c08090111100209040b120d08060303073507200a080f06011e0f03030518030d0809010606030c080c 66
    0x2204590321a001401c1145842c03c2c040710f90051005651850600c100c0b144107180412800c400c0300c10a40301c4a0f8000d01c0c00b11040502c412a507001003442d980365801f100301c0e21042d001040c068001d2003404071140c05500d009403010b04850b1441080000030f02400300000d40002000300c100f071300444a01c1c2c80701340540c0100c0d202555031800c0700c014010801400b08000309078000c0c0ca0569030844013405588904014014048404070405002d5841266000d4403240100300c2c090300800e01505407032030400c480c0c40e4003420070b4002c58400810328440d17451048100e284100c4100e10304243d60014a0001117440360340f000302c9010101d002c0c008588280d41c1540c1c1d41c0c800f400c4024aa120240c0e1000890030361420385410b800d112b00c841c5800756071451085c90413071048000c1a20b8840000e000c2c41401d40d1412103e0b82c115a0ac0114180108075040229980c1040120b0b0034100ca5a81e0750041d1a220603400d09544080d40040c040c5410a0f4142148603044040141d0103c10804200e8840c08248074807 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 999591681 1250 999590431 999590461
    0x8070201033611040903020a26031006020607080c03181f0f05150a1802091c1a06030714030109080a0504060f020d090306020306120f0a0203150105010e010503 70
    0xb940a051040448519150701144251015002e60300904829100500b84001c0d2180322030000d0041c1c00c581c051000142158500e5003212003000b03044030a60b0b00200c0c58103007551054600c0715007003103540c9041001d03d5040140940c02070823807070a0140c5040602c0b0315071041c000980b15486e0a0031120f900c209002040002d02c2d001150b0114900140107107102d131400410211482c0d0702800d0420780001c4203000b01303030080d02d42d481019103508402450001404104003d00c1715079520603408004c00c100c2e036030303501c5032049402c201d12a488691041c0e6203801c0c4462030940580107030130166201040807950b0046001001c0b1006c07400c40d002415a01c0780040c0c01030200c0b40300181040d0010422041c0d00d94450060300550340c030b03500e40c0401e0190181c0c0507690340a91100500c0000c884000502c001542c07a0044c41e040314001c0c1c14003802801e444461410a415035240c19101d07030042c114403007546810002c00e80c2d1980b100101c0251541004c0008100800c03038015141404400008119120304036100 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 999592931 1250 999591681 999591731
    0x20d050111270303030f10030210080a050714180f030105010305060609010b040f0b0702040207060e0d17010e13030c050703051c050c0a020111070b0d09120207030807020103 76
    0xc02050a1803090340c203642e0402424510580c403080401048001c00d840700c01c03200e01c0014000c5081d5580c0c0f403900c03181c040008014204402c00c1e032070000016141e1400341c2c01340d454642c90b007484610308000369804581d40100b42d40104003440081684034806c020845d02003078000d1444030700d948824008035546214481000703401d98a098000014004045a12030103494200e800d001e080c1d9a80a20042601a41c011901c400f1804102005003000d00b50040030303840d00c042c20160500f0700350f44a031400c4500b08004620590005041c1d4031038140d0250403d004258481d80004141d41030841020004000500701384d400300c00125808281401040304c0c00103d0b034410101c4070815141d1410350785a20056403e041e02444140c81e4055060140080d00c101010800c000c1c000b00790660011603140c0340018500c03049000ba9280492440703200d00c02482010040c0d0350115103500e052a2008202001c48643d0b4115008590240b0000f0802e1049a050310b17024a00400d01c0c0b03900402c81580205d01c003003 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 999594181 1250 999592931 999592933
    0x180409020a0315111b01180b06040c1b060c08010f1d0601091503020d0b0406060f0f051306080910020a0903060e010b0a0303020d0207090b0d0201030518060705121605040e04020d05 79
    0x4113079403a1780e40c0030b807506003107003031704000384962103250305103141c03850480500401e1036012800043c840d08150344003040000701490007828490f8129404900050640381c10340d001e607180c0a40d580b0040d0020552801001803a4590315170a181c803000c83c07400d036060a500c6046201c00c00108401c0e0b8030520080d80a4000703000304c140c9201c2c00c00000740095029602481c40641056903001c00c13071400b44581c0045400c6070311100d42103405001c8c1101c52000910414050110510540c610f80305960a00d50107045c007912500c41d142040407010340f801e10040320503401103004212100c070f1540d00010035011607503c00800300d250010091054051309516684580042c0050000802c2c550f00151121149165809a0b00e42c9511076400b10152090580202e402043c502d4890005500c66400954041c144c3e003080024100e10b184101d05001040d0f40d800e000610218000c0041220a0b0a140d04007880c580400e908900000c6e01505d640118800d100035000c103140010199107030a10007102c6613078858 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 999595431 1250 999594181 999594187
    0x10f0e0a030602121902070b0105010f120203091f0504120f0201060e0a060e2401050d06050a03050730081605070905180309180402030a1502180409020a031511 70
    0x15400c001c2003a002c81e481c4170301d040004c2054400340110300c200d804a98219600400310380c02d000c019224108192005002c101e260300d14080340980030b1020314010207042015000745201d0303246020581c41e444625007202032500d014000020640700ce4507919034110300b0700071f031782ca130303003890705900400f1781b0381c00080c2c503e003208200440091294002815502071129641c0e13192140c440c0700711003200d80e2003465001c40b01008180d10541c041d03c082c1c00304151942c0c011416548a1010a0709040203070700c2280c0d282d0000b0b109100310300c9080340b07080515403950001d5002d01e11203100800e440c142440090403031140002c021100c0505810002080c80d0040101c07a40715585440390350003840c040304d0341c19036540c400801c0403c401001c02210b08401000b0a10306189402c0149180b8840010f88104c0e8140703d081400070024038448288002aa0340140041c0c0300d03a9203d4152010801c41c80f882480307140f5000c820700042c3c2d52740c00c4d10760a403a00100c014100240480d0f00000402e00c041c000300a02c1008 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 999596681 1250 999595431 999595447
    0xc03040e10120b070f021609110702060d0905120703080f0c12070e0a0909020306010e0a0905060103060f060609050916050c19170f0d050a0b060c0c031506010f0e0a030602 75
    0xf15405600403c01580d500000c03c240020882c0c8602120080700d46102e0192400c04c00181c9035000041402610031030985064041d5002038106c0d44414501280f071522800043c0c03e00030140300c18504040d02c85200c41c544292540c5c001e1003074400802c0c0340703811305040c00851240c070540c0d81910b03240442c2202c44049810700500c0038007a0100381d01d0041c42040040008583e16030f0314016001c0c201c1d800f41c02485185d0a02c41c4030034080200900c8505080e90314040d030720119004104050083d8041c4a000030303200f4a01d0000015109250071000620819450801c41512015102ca03031000050031804080c1c06550b00490740c92241041204aa120340413000d01e0402e14490240010b40c450180250306e40d101240746400b43c080e190805c51041c000f807109205801903600210790100d818075000922240c0c0e90005000b503006084001c001d03030301c055410101400d0070000f110b21824445000c0c14a40340c044002822030244103528030402014005000107a111201200c02666000c1030554582c001 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 999597931 1250 999596681 999596693
    0xb1606091407091a010503090102090402070f060509150403030e0a020316080f011401050d080d091103060a050f070c03110d0c15050105060405040209061e0417030c03040e1012 77
    0x800201000030b80680c5034002285034003807140c240c0d0065201e02c0207424203405401552a03400c004d007083d000d55001c01c01901241d4803407008020491141015400c64401810180b0413070303000411048081c0c2c00421182900d1203540318203544540e05140c00303d52301115900c40307030034034943c18402509403058454101c1041c0b020801031082d104074a045aa4402c8003000791800d07502d008058401c2c03103100000620190030a00e015282441c0a40141442d000110811004607603c0400030303204041081d90040851409202e0b40c2e400500a00c010300081c101002c1c480040003000e45524240804240c0d4101058041c21a42458118410a50f0b056441030b0340301900b08024050300706c0741c0040f02441c000b900e207000e2007414140c800c0580000e0410f1b08010510000b540009000d0364809400c1c4000707001e214074101607444508442110646840ca4481040d103070000300c40c00b903078039a01300b40101101e552000040d101103c001c0000c0034443c0e02e9102c1e1464800e200798000200b1078801286403030034001 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 999599181 1250 999597931 999597953
    0x10602102f1303051e03210603030421110f0f0111160b070506060108040b161b06060906050a050d02040b18070504060807170f0c0408031c0b01110303010b160609 71
    0x345a45505400000400c2c449489200741c100c0d41442d0303040c107c3d440c00c480c1044c3c0441503100034080c00301c030b140513194801c14104c40b8500c0000c103581176401c6998010400a80c0c84400c07103402c03e440c0005070880034030000d14504240000d02c0d04000102d140940030319020406203e000b2102004c0189140d103614650710903611001e030949261007424003190442d4030581a4074030964110a10179243c2c2c031010007030a1413a10705a088400c0002d006150b440c1c901c1d40268103080c0134421702c0f0000d24180303000c0e000c0e4103a8409520880c450901018100040d40355000c04007a82981210005103000303145c40020f0b9560160008020f14450030810440e200e90890014000d4542d6500c40203890f43da188000c5403610301c030407204c851b160082008280c54850004074603811504000b070042c2450380f240c501920b180c0180d241c90000c14041c2000c54105546072084c039119000a01c1c3c9070089110303e4099654a11040c49140a21040010544540280003400b440100e031300c410240410312503030402d084c0b144 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 999600431 1250 999599181 999599203
    0xc2f09010f03020607060b130c1106010905070504050d140102030705130509011215110f13080601120f03170a09051e0c0f01050918010602102f130305 66
    0x241400000ca0003000448400c4210b0b41d0041c98140340070800d41e590009840300414450700300745003550058043d443e90290b03c5400c0c10990f00d000c0c14920081c1d80340d2400c0700603070003034810514050900065640c808102e9055800a84940581c410603181ca0040e50514850b0b80c0340651010041c413900c0d0b940000280b089402c0e40b0503451000792200c0030046446800e10400c2000c200001320080005e880d02d0802401e00790102000840342c82403103131a225544481905490254002400c01c2504101301c1c6080c040c00e01c0e42c00400c195810045101c8124212000280580d110f10015800b010f11411000c00c43c0d10880b1006100c40c00c01c1204000a00206c000c101d52500650311402007a00c2104504080100d004000f808001401805c4c4581c900050310341c14108401041000c1068440e0110314449140a91100c543c0398505a030007030400b003101d041500d0090038a00783e148900400c45012170007640d9060404050b030340188030790302c551091034031455298006403000003d020000c284a0052 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 999601681 1250 999600431 999600439
    0x1030c0e0606032d010306050a1a0a060507080c010c020a060c05070b06040c0311030f0915071d01050d09050f0d030204030c122f0126070c2f 62
    0x480d85950380e00d45120001c4904a4200c1010710019080741040c060004110760000c821a200c440c14041d07081e000d000903002038402a1311403050160301502d912692a550b00200c841c1000c10184100107440c00d03403142710b03400030800041401c0b010710030500704440b0650061350082122071103564010351a5164201c050703074001c0c9070461821500307004800311090700d603000104445c0c995600701000020314960401c2c800b010740d58080078501407012001580150151070081e0820326001c0411883c1a00340c110140e0156010386c28400010b41100094030500610040c410b114455040101d54501401c1003c10706103085c0780e4080240b003000701e002d17a051401c220684d414822240400d40a03440782d44402080c1c0142207000f008042d00315031120503a01d00c590310402d14050300654500e142864080c0752400c400d03132091042803e60308409001041400c0204441562007428000a81000f0080020040c804020004020406044082564000501e05001c9459034811a42e248007018401541c05 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 999602931 1250 999601681 999601703
    0x1b080a0c1d120c1c120f0203070b090c0d0f170301080709021305190e010504050606070b092a12010e070302211209031005090d0f090305150103 63
    0x2203107100321001080c01903151140e1010321030440502c400c02c010700107100761601844001031001c1c0e9034240c40400342a00681e14120011440c03c0a80f54410004841018000c0611548000a030040190703003642d90080100240fa69400ca0210300b404161110709134803910121413035007000a840400d8031030a00503001072495054203061030000348401c4c01030080990000d00c04010325465600102200c0c4640005801c41580e541c02113010850107000340344e065004050306018241500d01c0c1e203401804100c6061105040601c0880d109210300c0b04040d1104181b000003031901031040001d0380b101e240d10b1640707081000c42c0e240e00000d40e894a03e0b502e880380410741090300c0c05100501404407400d62040c090800300e8695400c1240620401080e500304200c5001a607403000000e011b00e80c0c2c080007200ca07503542d0388804410141009101d14103560f2052422060141c0c04900003100e00020003d2305144103240300a0500351400c0c0c0303256100810710b1007100b014190300748408000604030381c420388001c41 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 999604181 1250 999602931 999602951
    0x60c020c0a030302060a0f15080102071511030c0c19110f09010807061809060602031201051f0509040f05010f150503090606090402011b031808030c1507031b080a 71
    0x80107101c922001e00141d00c00804150030b103800e580816004294148005601c01e00511a030f103408010b42d0140411ba5404202941444155818400224000b4200300091540c009041c070030350001400245c140d10000c514440043c0b0108543c450380d105c00009907404145602d010400112681020350144800f03101050807030401c5401e05e8180d4040c080542007040c14050100e882074803041d0001c8060750f440c0d0340018848228421100504040d50156036a5404c0d01409001e07020183d0215000720b0030303034524030410326090650440e03104003441d00c10750b00c40422002802034000200b08400191420b000000c9681400d03100504550205041003040f8401c43c4040c2c501d07010850308200250429000681649010340391150312074030504040d60403d45c8120105481c00d40b8040480115041403c003588004452407140000e0008900440c80d0002000c80c0d40d03140c0c0305410400302122506004100407a0080d0000540031020404080c28170a00c2800180700901c01c0c3c0314440820b181105d824 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 999605431 1250 999604181 999604189
    0x305010609060614090415090c0e0904050c01030906114614040902030a05070801051009230d0b040618030f0e040f0c180b03090703032a060c020c 64
    0x54100e4100752514107400c4e50740408021103034489032001d40e1103940c5d48841c1603503410018568014000843c80041c1d648904034015101c0c1c0500d588051080c0720314410840000c40000e20300030854820700c3c2c040765041d41071034490050808100e010381c10107400b0503c002c03122802c400c01c096a110100e140d00c0c405a1050318905001c101c4800d136119003510620090b035450160000800000c01842c82a150a07a1000c02d1412a002516100039440c1c07580113200445500012642c003410040b42c100070740e1702110300b010700b040342c8520a03039501180020b105003000324141212030307038001d02928156009456180992007000111012121f2a28003080f01450100544004541e113502d0344501c661113075001b6040c1c0741c6121111416034041e8070b07440060152001030103068240c20841d00c1e80d100d04000207080c40c040c0300b091b81080c03401150030b108000d81c810000408400b01c03030301802d001d000450031500b03180041317013222801070090604060850400c80903074801c50056820f03a00703845e05405284104 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 999606681 1250 999605431 999605441
    0x5011203080412051c020702040e07050604091e0e0a0317040812040503071a010501170903040b0a18081f02190809010f1409120301230a090906060305010609 69
    0x50001984940041c0006410140401580496090a80c00c0c458401710002884440032440326181d0b030045001d10440c01d00303014200b80070316014040c0241038109000f00e00140a40e01c541e4110a44942d124280e480d0400400000c2c030054a5003030000001c0081c94980d90b400204089000411101c0480b940d40d07807200081e805240d001c80068138020b808e8442a034640c002410a40391030004000740340004800841604000101030b01c0824690315140000d0081006141011181e000c14404c00100c54000300803a0156110b4400342900c511112400300c401159200b05a18400c00090707000c1703074514000401c81d0b1203a01281e00500311b204010803c4050313004070041c845a403044d07000d1000882c0d000750100d940c411484000003d900c04205481c009407900300c7c44012840032040d0500034855001d00071321004a4044911610b1545804a8100d10405031981c0070300030000c0b504101000e540d09001c4100510250b6000c0c8120b501d6420000014541c503c0704548540c601340000400c200d0a0242b = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 999607931 1250 999606681 999606683
    0x30303010f0504020a05160506090105130507170a1703161e080601140f180d17031f06081f08070e06030a0b2d0103021c030314010902070303050112 65
    0x48482550b250a0500010350072007a203190a00ca41804100f0345030242c6020340503180e02860043c00282041c65540342180d20140c14500340a4441445038041080011002c044030040d2006000282080758114200f4002d010014a41880d00310340152088500700958021480000260084a05500300303542c00210034008180076840c44212000c810f0141c07540300d5000d1010f04100d07544081400008025034000c0b00c61061100300400c20b1208414403100c500340c00c4000b600d914032190003540703075a0902d04819a14042a243c008001201845102031294143c0c2035900005c5400d43c80d0000948988801c0342c00000520700c410300c1c840c1415801c00f0000841e0703000c0c005040e0060501c1d042d800b06001c0205899058400ca8040900095010401c0751180c20440d0440744400c01400804541a4080d101c048001021000501c050303501c5220105500c0c08038803606e10200e0b4145019405045a00040041d0403400000040c05081680007072269510030fa808020f20ba072104004903030301040340c00c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 999609181 1250 999607931 999607949
    0x6060203130306020912160e0a050f0408070f0507090603140d05091903020307120b1b0f03150406060f09081b120f011a130c080604050a091a070e03030301 68
    0x5402c0020615a40c024016890050b042030041050417003000e14025035010018040703001903000704a40709103050843e80001501d00c0901040c1018680702886a4010b4409048460001001400c0100c520f110108459001080d9561141c2c0c071100400102054842628001c00d221240c0054141c0800c0440712207400c1d4450609003040342d0107215003144503882034042c2003980400440541c0d4100001700041c1840000d070440d01c1340c107103000c2c1e20310035001c1c0004981804060714100c54403182001d4440c118584100a616a034070b10000d41d5510501410b031680041c07400d580410711662100304459a000207869a542d529a9011001c0da25800300031004400301e070400000000f45400074042180900d03880440d0380380c440690446084803c1002800355200c1c40c11000313001428040030343c1160340d418200410145940c040058010315008080c548502e03662000180d114a441d03001c0040c040d00300c00422442c140e0712066006803003007503590300003244288601c000e03c1d2a00001302c81c16920105 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 999610431 1250 999609181 999609217
    0x120b0109140d05060c03070e100903110406151e050403050c090403272105100905330f070507080705031c2412170d1e06060203 56
    0x28021209802208680d5000c0d1181e88654081a0108221406000086075643c0c1c6c0f41008031000e004141c00c810414001e4006498600c0d03030711340114038441100d0f000301c0d803241000f00d0900001e00400c0300e034004010000c41c000c2103034080c9a1000c4030040116075545142c15000c0100826515402188801080c55000d100c0340104c5040003540a0342251080c03d2003660203c87c0100c00c2c0850a032000a090328100051081280d00d400805100540702201d0b040e40c0f100501d174030340d240c41701e100c0c1c40c4940406441d0440d06c0c0c1004030803c0b082004100340b0101d4a4002e40007010b034074032f8a006403842000d00c45c0b00310120300d410103058a00b90007034142c1d48070240350410547e43c0f40f00302d4103e880c0a0307940740000d201d4182c600384086010020810006000504011040506001100705010003081418180003d0100720f001d088070801c05a006030b20604142c0c100b5840d15401d02c100d01240420038105012990840314102d0400c1000c00c121009100c0700d07490320b808a0342d0740103d80c1210b887c4000c030 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 999611681 1250 999610431 999610439
    0x90604020301050a12050f0f0f060a050106122a1d0901120b10150503010512120406140d06090b0310050c1c2003150d23070e040c06120b0109 62
    0x7a85d040d00080c0c07103003080d10702c4c0d48000c060803810846000032a010030f07000a94440d0185005104642d0311240b40c42c0200800e5051540c0113156810054440380f806585a4044071212980817516220402040000342030010b1600010408076529500f04143c0c00e0450140009140c0000c01c0c078180c1d00303144084d07040450319840f07441290b140a0045003258144a07408160814110121403850710181c4545590707502d08420b200724000c106250340e40d00d4000c840e94044c0129103808950031a00c65103800380c4a625081800f41d00781c420319031541c1340daa1400c03000058102e4250803118118000300c003502c4902040c1105401596030889034000d0003076080200140c50a8840130918078121190320000b82c11907038070009203100884001c1c0b40103900000c0104801d441c803c160508081c0e00503100c18007902d45c0340d41c0301d000000c180300740070b1410355603404071490060041180034020010292040310908160a10151208a60003180005500e10b4407075000c000190090f201503003410f9550084a900e8 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 999612931 1250 999611681 999611699
    0x61e04110a12090b0f190e010209010e010c110105030702101a01030606020d09030303090f021018060201090506270a080c0105010509010b0d0b1c0614090c0a06050d2702090604020301050a 82
    0x14089031090820746e500080c0894103100304108000d0b1040016a2414001d00140801c40442c0703095040100c034160b4807000440c00a22205c00c8103013824450340b2a120000141e00b40641145000401c9203411041080c04508880303408100c2030030380701003207004c0d21031004a0722881c511003050f001c1103000c40b003000043c1c4070354800e6000d00e016440d0428503035503070b07400241400b03c1d071460800043c0b0b034040d00c414034000300e503442c000510380c5000030003180801d40e135515210403005084c0700c0b0910000c00148036103809101007050400048040d181c0c2c540709840d1003800c1e40c01c4000071006943c0b900c00041058145081b059050f02e030448405810014080f90110141c420002d4082d00201035207076050301c00991102da91200c0313100f2500440c0354242d420140340e0044004190105c6075021500d5201c440d1602c405503001c0d155245041a079800d5200000300140c45c21001030f80a9029032804000e0441d104039810983c140308a95a036100c0d282c0303c0400007030340420f005140c0c3c40f8090304010000301e41 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 999614181 1250 999612931 999612961
    0x14150102010f0c050d0e031e0306190b0a020105100e010b131509081203040201081303021903080a0b0906010e040b19120c09090803061e04110a12090b 66
    0x1014400441d0907105014240140e030401200301000c04c01c00b01d0041ca10300100d000d40e0201c0510280110304100700e11283c0604060040c4501000b40301c0000450b0341034403114103c4503055290041400a665540e1030010709602003c40107005520786404035135060311503888007084170300100c00c0c501c184c2d003810101116a170060600c40c800511458002030600d03220956416104003030b0f180d100c2d00515109540781854440441c0c0408a0f43c104104030042c0c0c0c100003001d4100a889641110b502c1c46803609a10701400650f82d800c4008210b1080310405901c01c69407803161040090602c14a50a442400a941c40545036240890740c0301c0101902d908265029070b441c000e008005007481d02c50a40d1056581001d030b0030401072000449481c0c0c040c1302a60b104800100f0003040e00300210507c0b612445824040901740700d1091540b1030f42d40e0703007004841e0b425004071003000f03008001c5809182c000d4411944500c2140020030619501c2c0e049102c81c42c490301001700c1d00304a0800b0785564124440c00628 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 999615431 1250 999614181 999614221
    0x506040b060310050a06090e01060e0f10090204240305070e01110c090405010f2409090602070614040b0601020a05030f090a03080f04030c170a0210021e010b100314 72
    0x210403c1204500003800f406014041c849001c1c0000c0c601d400c040c0e2400030740b0100c076020003940c2c4c14040100142e0801c170f10456448940e480d580c4946850715400c03045990550751080725860b00104021030200c20100703500ca002010820541842c507010b15003035081da6402ca8555010a0280b02407100c254000d2155118204120f800d0303c0c85142c0b041c00203944c00c0300c1500e0542d101e030342d2136465041c00a00f03849002940c0400300c3d80602c010302d4404217282c03850b00301d0165031040d40d20350100400f0000e0300d40542c0d02c4250700c448188890340c9070040f920059441228240c82007003908001c24915400420195031054020020318a130500b4004455038551182d10f4880d00030340c03842c40c004081002d10014040714408000710580d66491406c0a90303a4850300d411095075801810f22106450314001004039809030b056901d054602c0202c20160f0a00384600204014280322111442c8142030651092809000c11152801c0001200000b02c00300d4040c2a83d03401030440d16000b1a64504100325095104 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 999616681 1250 999615431 999615433
    0x40c0816031506050c12130311010c17120a110a03150503030a050c07060504060c030c052b09172107051b030d0e0a0b0f0c1516020a0506040b0603 64
    0x1c0c1c940040c01030ba5012a80d4441c10010318085600d9044490500c1030300120a600016141031058200181480481504c0020034070017509400c0d41d9107034000c0103e03075405074005042c0440890b004140524550107403a02d58400c1d41d6140003c1c04283c1c00748502005071200c0b020312070400410003000d90003001151100203560321300010000750b1b42d0302080280f504010990f02d80741c079040700d48082803a202c02a0803440c01e112080c0420b10641d030f40480c8144080d501403925820f0705105c3d040c01810100070307440303243d0103526082d2010036603104c034454440419030030394400b40000da88008e00140d091690b100c0c01c01c2c82c2c009c840070f5042030040780c001030110f8114a00003403800383c00340c2c2d40a2601a00f1403005003240c0540100024500e070500199001703040b90304144064030340c0980080d103100d0729030042ca0020040030502000c4001d042040c1c40300c0750031031011030311400c0100c0100d0402060441d20907850ad1400900654001c0c808183c6000c040e501c100209580e480da50385172134900b10000e1059400d = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 999617931 1250 999616681 999616691
    0xf1403010e0f151005010e01052503030606021020130b03040b0403090b03070827071403190803010603020d0b030105040c18020a0206150a03020909010b0a05040c081603 74
    0x50440180010b00010a9910042c00407039480b00944495500040400c8600590200f04000c56600300c10804903c043c04d2a00540c3c034800562102d14603404210704030085540820f00c0310800d07405a11001c01e48103d5003c8801000c04004039000b0b69164080340001e03803103503244058682111801030305c03195901050480201d511142e50b01e0780da410454060b6804603009003840706141d00700441e5005000d120105914501e00302a0141c0380901c003500c0c0901482000000c20400a110203031060010303a004159550295507418841809a518203880e00c00c1c00b80142c0040243c00466901c00b101d030384003001c5411a071800724268025000704460001a644510b40034036503075000c0c440c5070300c641e00c21690003082d1401c00362142201c0c0d0b49044513000c814030402ca0740c254240c001805562012a102c4001540319280020a000c1c1d40c440e40025002250b45040c060610030641103011500f10030b0780c5040829983d802000199462410b03e4070200c2ca280b004201985c003081c8103e02c4600b400d00b40411 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 999619181 1250 999617931 999617951
    0xf050f010905151222022404030309030510051306020703140c0d02060108031314060403021504060e040c0e04180209160e040b0a151101050c180a0f140301 68
    0x4003640148610641c066000500000c1d28030410320816085159070f051100f01098a09808402070a4017402034420102d52440015118404054000c0c0340c041d50513458075a960391401a0400780140011540e500072803058580c21505132017001e204131500c9440040d03141c0c1b0f80e110350000390700c030040c1541003000d40480c4140070710070709006000d000c000200030f145440d11310f24001d003086810f0300610030305d80080008544440910035104140c80c0885402d1940b1002c280000700203119591009401264010301150b80c0715031078020300100c422079180d025101d100d100810003200c0c0c0b00c0b041c1e1700200702501c100032880e0a0551103131060135250b00640c0060384803900050a0210304403000c0c0030540d00006001092a88222102d451403000e803401e100070005400000c0c2d0b0040715001d10014140088030a0380c4403481400612080b803401002040f590400e81d501480c1c41c0c0c400820801a0362680c07022480303604100824000301c500c007050801d4124204041c0e080d40116000c01c290b4150b48810b1240e03 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 999620431 1250 999619181 999619189
    0x30f1e1c112b080906010509180309030d030e06011a18040f090b01052b03050c1509010b010f0203030f01090e070b27030d0f0c030309060903080117070f050f010905 72
    0x544000186a50300d225000e54180082043e0002400722a2030f03002040100031a445690312150001060700003080081c0503860064076600502d699258540300c0c45000981c9175415500c80c3c42402078410a4038407980e00c905903190807410b00201004140820040c1c05010080c0031408042e103040200702080a000c2c5200e10010385041356000d4036443e642100400242c80d101c0310101c0c58030f680704480030103000e2803044003544103092040034007400000240c86010178414044883c00b00b15000200089041007440c190003040c880d01d480d400701d01050b40103440640000180c80c0704025010855905070300b01580800544900002c0740b28911403660b02068640c40c01002d840310b0300355104809038007080b00040c800300260300c0b14864025080215010501c941c001e00c4140840c1d42230501d040c50195501e8110024100c10b18064081803411014500b0194010041c50480d51955010030046c3e1000c10030701c0d2034072954071480d030500091034010001030900d1031070f612340358005050240c1d10560381c1001c1 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 999621681 1250 999620431 999620473
    0x4060209011b12020f0705030312060a0f170105060402090d0f0512040e101703040b03060f090c07020306240d02210601090c02030703050a05030a0902030f1e1c11 71
    0x480b0181c007000905a4400c3d0304210380d05c1c1d4041070304000c1845038a4807022079201d00c2007844855102070719000140c1580c884181c2c400081121a0100c00d242d6500c125128070400d10040c2010035500f0007000c0b410350b240900a90f101c1c0d1400904144141c0402d0b5100010750520000c11143c4d40201c001c0303903c1d40050080908001c101c44d414100307403443c115490110388001ea40000f0040c0070b23031408000c426680041902c00b5034030744418065881c0c076030000080110000c458030942c00b04c00313482000b0040c00d18802408100b80b00340c0c22903400d074507060341d058107540d855001c02c82529211850490340e880c00b280c500e01030f180090075114005440c200000b4040c403d140c010070303160703008000402c686440f03881280d0403254188041d40c04d00740d407958024094806c044201c01006800b1020a1032000302d0361002d200c25134002d0842d00b42000c50b03501903407078007a50b00d042e80002b4604c1001e82400080030880100301801003261140405030034000381c804001d55801c0044520404484c4043d000038281e0b0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 999622931 1250 999621681 999621683
    0x90105042718031106010617100801060f06020c010c02030d050711060403060603051203100506181305100b120a02070311010c2001020913110d020403061407090e04060209011b 77
    0x140701c07a20010f0f09000d403000a88100380d0b0401d40c004001000a103030b000c41400902c03003585400c48110389400035014880b03001e6811091a95180440000300102c080558004070345031030302515112140c0c0001560080070001010350960402008541141d04c20001440b80c280700714955510b207400e0720089034154000b0b800450304265106001d10920904102800b00c01c4800f006007807440c40e002c002031448446500c1614012003010030000250a141c0c0f46848642d00003421811210401b84000070140c43c064900b0b4022104001011500e054042c003160001429030410201589400403020025030200d40c081c0d08005a04450101500f428041d01483c0c0c01d55a0b42c803000c030069190304000002136032400d04850fa20400480c00e05031202001200648a01c400004030390618480c991b40c284a4150b140d685544006408800c000c0c1070340c0251142d0003194034501d09680c0e403c9066920003207078000d18007500e641c0030008001039043d4000346203a00701890403146001c040748450f0068100080 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 999624181 1250 999622931 999622961
    0xc12030c04030605280b0d05010e0705190506190509090108030304150603020906010e12030f13080a02090a051005040609090b060405071403271e030901050427 70
    0x80800c1030101034003405410200170140c0d0940700181900030004500740c154207014094981002c43c00c1c5a03500a85950041d0704030000303004240c0c000e0002512070120b0700540e07100750500e4807000d1720b05a030101d40c0350555a0261405141047d0b080364400c259a00c0001f0804000d000c001c00300ada9211030201031700030041003005640b0b904191402481150040c40103c100f5440c000702000540c0c0c9074011140c002d0403e0900155000006010400740041c81507038140510000a080904a40d800700400004844001e407800a40d10750721041e84404195102035440646403011440c000a140d200313039040040e101d246d038000d555500200c0e054031a140d001070f41040c2d0703800147d01813054100c1000c2d48010125003c01c15458508009411040001c0415a22003c0480043c043c1e000540e80c101d0342000401c04900d01a55901d0450340c0c07054002e0204003200f056803028010f062001050f01e541800586a5904040c280590441071380303294461084180e0a5801c00c03140c00c905845000e4951600d55 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 999625431 1250 999624181 999624187
    0x60d021009030c050f220f02031e09010e0c090a02090d030905130504050607030b030106170d0f020705010207380306150304080d0b150d0504030905030303100b0c12030c 74
    0x4204660080f500d50f10003030045544c40c0c0d9007200b6a44500b0002c203114621011074041d822400501001132160507552580b40f8800001e1000140d00000c042c00f250086c003485840e02d6851001040c00d03502c090040100c1c03075210030498030b400d07c1d081400950041c1404001801c00a4480000b040e0645004046c0d010403402001445542401904c10b040a44c04500602c854101aa513a0780c0d43c010091801d030415a540c0501c0e04c80380c0e070a4001e00300030459200400009a07080c140a030300c0d8000b403145036020807e4034540c10f50150022a11004442050b00540005460501d40c031310305e02902c080c0103c089800e1370061711800001d0085010741040071620316100d150510134000f0344c03041c0301011040010180108070003c0e2118045a01c0d0148a02003c5980d40d012808102403109009044985840200f0009001d00107030b0300640c0301c0d5010740da5284480c1d565400749038682c4016a081c0790f0300f82c103450050162400710780c000c00003401c0b080300f198245c01741000110099041600c841900305000 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 999626681 1250 999625431 999625433
    0x40302031c1b0509090412030b0d06020918090a02010f170708041b050d060f11030106020c091e040f140a03021605012604050a060c200d120203060d02100903 69
    0xb12050184140c503070078014600860345001401840c4010070040407100c11000100302d041c1b203034004a504100c0508001451035079464240041d4003c3e4036064022611030300c20070620b82c0040360190050b01c549001d440891010740044448519031000c100c188241000c0403200b0500c00758403a8490100d541d41c22803070b400d082c5029062681440e0504280d00c550f03c0c4144030560320304038804101640003100103030a8202d91070303060103818072100103480242d001c0000500309401040d508a2910102d61081c400c1d92087c1d402d60815003041c1d0800c1404201d00c2c0050002a480c04403040050702034246400b00c82e040c00a00d41c81d0244164045005822131140100d140c1c030900580005010242091151518071040700c082100c0c40e01115010509044003042c02d1200600115800b50b03044081407014a010700c002034121429000300c034820301c840d101c82150404c030200d1041725450280e83c40000030f00e451500000607400c0a440240d1203d403003a5420b0050392180900c8100309000c0d2581844103243d = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 999627931 1250 999626681 999626711
    0x2607120f0302030106120f09051207290406091112070302040510060806150904180b060a24110d1106070806060910021e01061503020c07030b040302031c 67
    0x1040300d0003000d050041c030050102c50b8101550035202071105038006441c0504443c038501824110102820f9400b80442c00f80c903100c4100e0003400c0b024052070360100b111801d40b00074011110010044640f035000e200106000a80d05c0d0059445a802a2204a0f04118150025236820320700200040d069025040030011030030310303008442c0d0100c106464503a0003854a1805040d0020007480705118a8514403400300540d110401d4601051014000304150041c1b0000240a0f00307c6083c103a0b80701d0603200024030585030207072040060b1a04e02c404d1f0340b00e050400c8841c500281849400d48140441054042d0b0408010403e035003d000d9565945941da0041c04080350424102821610400c000342082241503181d642c1118601c030019210801d0300d01c9584012410802c40d104c034007500c00d420346401e20010303005401100c02e5623000442c0700070008400c4429412445064035582c43c0e42c109000c1000031811b01c1505507030150190043d28a8039144081d003002c50074850701805071090f0799050920520305 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 999629181 1250 999627931 999627947
    0xf030a0f0305060d031b08163e06160b0601091502061315290a06080a0f02160606060206011d0f091204032004060b0403260712 56
    0x301030608102d2820302402142c0380c803440c41005400c0c0070806110358450710601404001198000d160300d0f44130041044800c50704100d56405560844424401d5038078802e032200565500301d00069903c1c501a4141c04046d000c0e0600c00c007136540311b1018042046007d0320800e0751b40c0707114030650185c266450301400151503445179030022032070750f0000300c0040c03190b64001682075000100c15892034154035652500c041404007907910310008605081810040c10111b50806282d01d86810340000802c0f060414014500d01c5845003000203078620010400d0100541c0c0324031240d008072800986817050321040754501078403000c4119143d0743d50744010003525a0502c062409044a0041d0b130001d14800d0b4816880c80d01c01030074028a00111001040345c440c41005019617205054034503589840d03582c20580d2220040d000c004400d56a00304c0403020304d242031b03c1000103682c0300c0c044213030800d8115118249440749420420540311503100621141c070540f00c003d028050300c6843e21031030129203070000500841c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 999630431 1250 999629181 999629207
    0xe130c0306050a1401140304020a1d06031e030403060f0f050408071a040f0605090c1906030612051203090109080304152406181203020c1c0507120809030f030a 70
    0x2000c125030241d070581e4007561303007286c181050040944075211800010f5a05210341d1040540800c80a5941034940c50301340d5091042c103088045da5040116141c07150b20b000210301c058903154104010510001d0241d40c44103d040d03207650300c001411049810343c8000c0360400e681c15100c1c4030000c11040100407100d03402d90110403a581218109003003030f03913480e600c00f2501c041c010710460710340001030a240020002d82000c420010a110300b03044802e060802d0149681c098240042d05100011595065641e00038032081d0b4418010311004d880f5800304500343d040540740318502c0d500c614001c004500c1c00000f46000c0d0740200c0d21580030700b15402d90f60085a8041c0780a400040300003c014035414003204214084443d81d08184a040480041540c82241c90750001c1441101d14000c02c01807640c0042c42d11240c1e0010f03207040c0c0001031300035040d6014a611030001003076540200070502c0b081c144821050b5450344500c45403801c04c400c480000b07003040c0d16164840581c0d8408074294280540c4681001809 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 999631681 1250 999630431 999630449
    0x1503090507080c09062e0806040f0501050303120702070906140132160f080306040606082401090305031638040828020705010504150e130c0306050a 65
    0x281d2803c101144a8070740003030104e80706006881240c43c142100360804c04d1054603c00e0148843c001c048000303010440c080d5883d0340503928058101d00000124445d442c180c61008004508000030440c1c42100c034040204100114068000700040c484003500883e800340015900000d4002c0085c1c0004100902c108101110308034007009405030960280440d07511100882000c0d543c481d10305c034041c0b800500b00c010041040303610100071002d0100c20000703103000302004c4805104c120380e40c1d0021542500c00342d0b99042659440c440d2811104141c046c26915610181004044980e413a2910340c10341d0460304040d01c031855070407046410001000c0300ca0314100c5100380304120300415000c1845040c40d03041e5190110015600c0480d050291403010f480400030b0841040b0034103101400c0414072915140500009880ba44401250540c040c109039400e03102e8240c10301380003920040c001c076038011081c0505074100301030f0b0881210144071030240e08031070034190f103022400c207141100303205e801c0742281d2082c228 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 999632931 1250 999631681 999631693
    0x503010801053312150f070c0201020607081e0108012013030305032a040305060a0c08040f1703070e0901050f06070b0a0f1b0f0207031e030306150309050708 69
    0x40c446620014a20242d2402d001030343c1428402d010a00d0302c040e604001c0114410065002890702c90303544038070b00c203c440d0360140006072500c80c1d055a071248682c00090158106a00041096200b5006594082801c6004159041d08203541c1030700140c0030380050601c0d94440d07a000e10812005080e82804c4034121019a1415103800c0662400e2407070b0780001410804c002001c542602d6038485014a0b440462903002c0c044c2d0720505010680368002d03c0215514014900002c0324004680f24100d0205034944070f141c52640c5a0b41d46864807480803004036001d882e40c444009012400d907000e188101d400f61214034120038400104500f08805a0081e440340d40c2990300200742e5242c80054a5000d80d0107000002542c44140c0c4600c050100e40e003209110921f80b48000c10b002c2c4e00c1c104001644101a20b170512171848074182207854442c00d010140140032018170a4010ba1100841c035000c02d4020300e400036655803640110001c4020002030400000e494890725014054140000b400900071a002040 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 999634181 1250 999632931 999632971
    0x80a0609021c150305100e2a030f0d08010b03060d1a01171903080601110a0b0121020a0608150a0f1409391606060b0f0301030605060a0f0303050301080105 68
    0x40d462185001e010b1b150358989850020311241041217041c40d96000385101c903980d01055412400300d00c0c2c20782c0188170344a0714a81031071a01c40170a000c60340f05003d84e50203000c1d0b820288403a400d40d2000e40f4894015400070f41c0880483d0306000da42c17901c0c0c40c07680d541d5086075240c408548501c603180da8003030042c1d03041210201080704003030340049210b55050810040c42c0c0c1d0f89030300695580c41c208200700f07440d000700600082042040d15409069400161a0f1003e50714001d200032140c00303e002c0b0003034100d01c00400911800b80503010b581d52201840704205a0f00001d1008103081c520947e0116006c074070f00f1a400d0203030021414100514501c02d89008080d460403107161740b0360039100144c0342c00c0c0401e000700c69803081c0020031403080000f404a50441d51034114590481c2c822028417410b0721021f1a02201048541340369045814465035000d5150850b400d6807601c000034540548213030750240c44460001030080b414400c4030001c46c004d480e8130f51030350700d4580c040c0d00790341c0000c045030120305205013141 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 999635431 1250 999634181 999634183
    0x10f05010f1d160207050d060c020d050a360e01180c0207092403050f0c12030702010509040905010603080a140406081f03082d030c0901080a0609021c150305 69
    0x2981c040500102c418088245610076402c1c0207064021540081c0031045640c20b1201682180109d0a40ca60890f030b11802c072a03404450500401c041034002071400003170ba0f000e422070b2107d04801050000d403140d0801401c441650070300042c43e4040e04c031030344001e0010000d0752b00000820741d0030407001c80240014442164000d44aa455000e80c1500a987e024080e0300407140c91700d580c200c2c40d002c1822100454507810070554641e01c4003040d00b502c1c4540264411030303062070080400f884482d24001e40c20400c2a40c010f4540707400c4581100e421a41c3d4000680100301d09004000c011409040110381c0c4502401c0005c1c41d84150156044034404200020400b40d9849141c01d6030000300d000750184019540c2400601980030b9500190041f9030209580c030071030102078500724001c1a403606150790003490501160050208458044500105102e144e4440d4050202290b02c11441ba900040f00c5071a40c00c905c040342c1100040703a0a1800780044003014402501c1070800e070003e080703540010180785594039 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 999636681 1250 999635431 999635489
    0x150e0127170f07061d1c0503180a0501060e0708180601030212100f0b030c01110c0f150c06060f03010504020d0618050a080d060e09280203010f05010f 66
    0x480e900c5002440314070b5250824140e8030b005030300900038040800341d800c041d443c501c810840080107001c0d000348542d0a0200c05003000150449407147c5042d83e4800400302a000219403e0f400b807405440f86250000d0307c20701c00c43e4040c007486032200d0704a04103040b0050481d4402000b501100c4200400341c110100b0020344681100d60440d0b140d2102500a2040e80c282070700d00b03100c1c0e21070300d05200075080f0311145a00020300008081d0121800320b00a83c004403000030f0701c4501412141c00ca40d80490450520a0144504060140901c0d410300c03c441030000b0a0b80c000d194507112900110144002441d00302070419001c042140280040c0c10542c0020788103480e541401080c186e40c03010119620803141445000792a005010f45298418034280304030681e02c1070401c10202480c01c2c0004c1428014009500d00414045000f410b0014203180501c0041c9008030400950b080d00c4010f00303005950074090700164110043d00070030154500948011462040d8000d440b0800132001c002c2d03c5a8640741c15 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 999637931 1250 999636681 999636713
    0x3040803090d020103090f0c0501141303060b01020c060703110120190e10031409030c06012706230102010c020c0f18010305030310060c030804020d150e0127 69
    0x402c1e01111a440141c0041c12001c034010021a9140050001e201c3c1c1640c40340101e80003070f00c4201040080c482101a507104054017100c0c0311040c1182800411059489035041da001801101c3c1020510b20001e0b8054002c60000c07000100c04000d0101508c00030301400c0b2040c88915410300c00080d50402c0a0810b004000d0309251600d6000c0017410341c148070b100d1400a10f0400f5201100103d2503034001000381c0154000a1000c3c11084003203004070a00008581d0301400e11401b80c0f805900345015100c408044009804903544100495101000d0b540700e110002c0c00d100c107003d040d5480100c403441551481c0700505040d6450441006c0d42d907900400c0c5810b280e00225034609104030213200081d0b54150420048440701d01d41400441081000401140200742c040c0422440e2950b8040484140700040b400800080e40c0340080b600604090710b8030b03103a82e4032425015601a0844030400c08a4550003000790071691039416a0140804000c03002c60f01c0182d81c6050100e074036258640a07580b854a0702 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 999639181 1250 999637931 999637939
    0x5160b0604150612110304050a03050d0b0301062403050c030105062206020a14060103030909050c0c0f1f02030f04120c0f0c0f15141e0408060907080304080309 70
    0x300240d803103030b01445140640031540c0c40156140c0b0750050011000d000507099003441c0c45011911355103508107591003543e003c00182007020095804407203603040081907201c0b03035846280c0b0a0090b03400b0301a000141101c1000c032100c00c9174080070b01d403900103041d003200281843c010038000022030400840703055131820385005564207200d000080e42d18000c00d8500e40703030308242c40000c62099808220642c81602424050401c0312040c9943c5807540030038072004000c90b940050800c1904540c0d0080c55100c01c074015103600344007080c2c0c4494103001c00b0000b44200c6410100c020008130b03450400f0740c4100c0c031442104509504d0682ca0301c081140000e0405015040c1da140c42c2c0f91005e109001b950405503003c501c7c03003904c0d6407901d00744207522810f01030f00013a81d8402102040c01c1030369649031300c00c00c2400e87d03480c070105d161200c45412660108001102041c616100310b40c000324150014402095120001c2125240c06c0403c141490603036000004144c000b04402c00820380c0c0007060b9030f5100c404031 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 999640287 1106 999639181 999639203
    0x14011107060905010c080c011a0907052a030c1606170402030c0114091804020906010e090c0a12181103010506060d090c05120a11010516 60
    0x4081c074800550601c000700306640c0b184820b02e503118000c60509107007825035608a829106a50786c91a07080100035003074005810300c4240725030b0020309494070500f81a00440103800313a02c06140c001e0010351540e2108513600c00103100b15000c0b21801d070200c3d010140c1d02075044da100f01e014414030300851500010010140b9065034070034807803075000f0007902c3c650400b0001905c0c40b42c0070300284030b5140c00c00e009820440c0c8810012009a2041945d41d0500e0315151042019858006016a04105450071000303030540340c481c805ea400022b0125030b6034807070360004001c540540c24205081001c80c2807100d80a07251400c4c1e580850303854000c9041c075103000b6141040c0b5013660410b88180703070041800c00601d21940003d83c8090000d5100b5040b1008056603080001c81d0f1000e4100c200301c184d0070030240d45040020203003448a1003402803c0c0141880b840e0807003500c3d4150800070240c1510159 = true := by decide +kernel

theorem cover : BRFrame.Cov 999460431 999640287 := by
  have h0 := BRFrame.cov_init 999460431
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999460431 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999460431 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999460431 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999460431 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999460431 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999460431 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999460431 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999460431 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999460431 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999460431 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999460431 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999460431 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999460431 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999460431 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999460431 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999460431 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999460431 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999460431 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999460431 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999460431 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999460431 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999460431 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999460431 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999460431 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999460431 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999460431 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999460431 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999460431 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999460431 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999460431 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999460431 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999460431 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999460431 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999460431 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999460431 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999460431 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999460431 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999460431 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999460431 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999460431 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999460431 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999460431 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999460431 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999460431 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999460431 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999460431 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999460431 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999460431 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999460431 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999460431 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999460431 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999460431 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999460431 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999460431 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999460431 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999460431 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999460431 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999460431 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999460431 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999460431 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999460431 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999460431 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999460431 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999460431 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999460431 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999460431 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999460431 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999460431 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999460431 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999460431 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999460431 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999460431 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999460431 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999460431 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999460431 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999460431 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999460431 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999460431 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999460431 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999460431 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999460431 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999460431 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999460431 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999460431 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999460431 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999460431 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999460431 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999460431 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999460431 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999460431 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999460431 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999460431 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999460431 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999460431 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999460431 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999460431 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999460431 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999460431 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999460431 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999460431 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999460431 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999460431 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999460431 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999460431 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999460431 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999460431 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999460431 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999460431 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999460431 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999460431 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999460431 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999460431 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999460431 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999460431 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999460431 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999460431 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999460431 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999460431 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999460431 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999460431 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999460431 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999460431 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999460431 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999460431 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999460431 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999460431 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999460431 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999460431 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999460431 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999460431 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999460431 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999460431 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999460431 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999460431 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999460431 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999460431 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999460431 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999460431 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999460431 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999460431 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999460431 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999460431 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999460431 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999460431 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 999460431 ≤ n) (h2 : n < 999640287) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
