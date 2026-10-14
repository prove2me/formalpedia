-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2597
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:11:06.151374+00:00
-- url     : https://prove2.me/submissions/cec68fbb-3e70-44ad-bb0c-943143b3d361

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 466906474 ≤ n < 467086330 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 466907724 1250 466906474 466906481
    0x13031208061302071a0903040b0a05090306060301110703030519020a030212100518041505040b1816060807030b15040e061503012c01060309030807020d12090606030b0a 74
    0x120035028429040c01e842c00c8086610131281c0e955007000768261004110038000f010000c000c3c08090240c80709110101d5602d01084c010690502e031512419038410012013458200800140041c4c0310f40d1400358003842014507001246c00855042c900000c160369620301d550103140c450128a6580c3d0700c08101c0409054043e402894480c5814402005a550320403030325105084500429401c5030903049507440d01c00d6007035411074105218589a5000481001d85201282d000700c0b4169002220403092244200d60071070551013a030a410090852140d1480141304c1400c024410007040290300000515524840e60101c01035244c001c00020351040d0180c500d0903560003902030341104425050200e10285450503403503c81562a02043d41180e10304007115420b41003203c509100c0012901c41030308412408041c007406407916840010706100541001480750380004c101506541c0001c000340e14042e0001541c1c020524038240201c1d5005d02450705602402240c0c1c0020401500d04040c03010f00c01c4a40c2 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 466908974 1250 466907724 466907731
    0x3050a0c05130606020c15042c10150507050a020904060614030106050a051012060e0a0c0302030f06040b0a09020c0c030111070f0b13050618060901060503070b13031208 74
    0x1030310362404448a0079050103c0b4424030441c0003680c0500c105404508003906c00080c80d0f14201c1c1510708055840841d81416141c403040181e6130070344070841d484d40c0c3d800d00040c240c0141020608811550400c00070482c41b010049040f418803a0204018042180c20004444500e5010b400440507041924103840508098082c20f02d50824010009903e03040500c100c0b4103c900c01480c081101c1d00d0541030044070765917031034013404001c0303070618403280c66907540a01c000402003282c28a049e440d00024010450307103407803440b90401d4010000d00c00d81a000202c15504910101c50002e0320745521800102c00302d17000d6004080d4640003150460011502241d4540e4480c4c05400a1041070700100090074241302c0c0c0e480c020020000c0310000e4022400703d401380e60380207402e00c004013071128641d1079003464400c04861030141040280081e8008900601c50ba5401007400e200074400a0b08050020f91a00124018035015001c04510180382c0441c000300c0d800119004a20b0f41140381b0410b1005100c2441113 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 466910224 1250 466908974 466908979
    0x41e11090703090305040302060f190c0302160303050316121d0d020c06040303030b0402070204060e1005041a090406090209070908070b0712200f0d120902010503190603050a0c05 78
    0x1038001401490080c0107058659a155541d98a03260450b406c11109400c041005401940e0a21600482018111030042085548d440e8503422010302d18000b40f801402815060005007020001c000007a000408c2ea50441c000d03240c075501e03d418000342100d10500d01d003408504c00f4200512402d81100b03a1260716804c401c2c00c0f083e24800c1400d201c050740d407030b14403d01079a0005010001000824820ba214100007500103001601c0d0211036000501520801e8000c603040d41d00b54005c1c00049050f40c01108000d02e02078030240700c01d0080d66004200c1d02420301d003141c081c007513000002e800c006a560051021540c020054071103820190fa009104a809002e00c0400e4410302c200820b2803d6240305803000107911024510f1683d10300170085a0404164608859404068007054800320082c04045d01d030300800c000901d2541c40c594801030100e41c00f0b241ca03445480c80c0144442c05030764000100c82d40100c49003285080c0b01100401c8400410940e8805052402061601003c1064281020086a004 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 466911474 1250 466910224 466910239
    0x2210109020c100b031504060605060304230a030504050d05010906020f070b070201020315280315060b1608070f121214071d01020a080c0c1005040e06010503041e11 72
    0x740c403c02c00311000300c035510b0f905034441c00108120f845582c0e84503501510808001c94159602e2004c10401d40080e01c0840752060000585071101c40300c2500a0301c0d8aa40000400c071074501d50324003400b00d104078040c03a8062174041000c601400002d4010809059105c4070444d40c03040b11842642d01500040e10868660782100c0c08510701903c1402585e0144c2203200110480398862000c1100120800d60014540c0e040d04c0c0004030101030101d0400c00841c020526210400384511b450001c403000380d00910b04142c024001485a140e40d1b03082c400c2c02a0b4010002d507920681420040c01c1e12201400007858046070803001c00c02180e00940c54840745010745024460440000c0b2205800d090403626640000c1c0704400001d15000401c0500300e00610600588040c1c0c0d00a485030071090b400302855030201e9001002810f51030070060280e284800051a26a06107070400c0e082000500010b401241003000201c041414010040720154220000d440d00d0405403245180c0842c0c0e00c042c180d5001e1203500c1 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 466912724 1250 466911474 466911493
    0x160201061d0f0402010e0306090601050a050312220807030507030302010513120e0111012d0212070e0406050405091515060a1209062d14060402210109020c 68
    0x709080d4101c00112003a2000c245552181c0114001e240020401c1e810841100d8404115480c03e000319805080d400014101c05d6040c1018480b2021240e44054000e0740080712844841100030191504500c83e80030200141c6a4a030706000002e0f966080036180703003e404000000c0000003d004000c881c441d400a02c103a6a5402513038404641042c0050a45400c42c2d4500c0d03400c512075001d4604045c0705041c604030520544c0ba10b81c3c210741c000c0c0141503845c4c1d445102440c4c3c01d82e900c4803515900c07013940c034254500b205424006218040c080d007803505001c1401161080c2d070b5140e40017107010300302c040e0003001549010a42e4554500600400100001800300443c003c800340151480da0080c02a204074030f80b003c040411102203c0f06854580740b81d0303581002c000002c0490150b408801d243e0050091810120700c00603a107503111030340c2101c94524001a481548818402c202d0784070904440040e108c1e0301d21417100183c01917410500256104c0100040f5146401e81d003d01000e1035030800300c810000 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 466913974 1250 466912724 466912739
    0x3120117011505120709050c28020c150f1207030e0f032d0316180f0b0304020d051501140405040510050603162c0717100e16020106 58
    0xc01000e050819880a620b00b40042c0c00e000c2c4080c10703801e000ca402c4408007580ca44803481180c07070981d128040640005210b50311001c0030140402102e0254404401c039064500010303603241c000d8610580a000c0500d02c1c510800c1c28034040d0fa10000d84654010343c1e0340541100000588001c0fa0100c010924003c0c02c00c0c0e030504001682003c107101280118900150a4040d58490082108403066400880c00311440341504d40c0280d8000e500000f02d52171528010340c800342101c070101003000e040706085501004192001482181183d03c4c60110030b980362928000300b4443e4890303501c040c01c1c5120390022000d00809c200003141c101c9400348030303441100000d0400c0000303a0714151400341091380718103001c0b0007002c0c095000039040007004085074440400d24220800b41291640859030b0710b08000e420007203006402102140601c1c079040b180b580c9140004000e03080354091b0120b00c0301100c24800142d030341213105803106d015040700390b900c40041c40d1001c800f200c0408590605001035080030000102d08 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 466915224 1250 466913974 466913981
    0x703020c09010e16030e100218012003040e25080105030c0102010e030315030c090f0708100815041e080304170309060c0904090c0909020f1c081b0312011701 69
    0x1c4440e4040d80c03064a075013038000c40c083c00140c1c0c6d403e0658000d5010240401c281d0388000c00c117001c3c103071840540c0c00c028400003500f1000b00c40e06100418640ca2450041c03004040200d034251846080c403008607441d5810001900346885100401845031604083e2210350040c10880c101d40c001c404480d0500c908400481c02d0342d0703194a1081055006102080c804030082400301c47d1800c3c003404440450300c80c00002642500c05440e1f0740c2e89100c800c421f10401e680e2243c0d0076a44595420407400c5003d150424143c5d4510b0b0020340441c10446020204007044901c0d980b4509040300c01084080c00581400c0049c0301d03034800c1e80c0c1115103142410320165800f00700c10a0703d20818441000c0c20f801e5650841e0491503510024501d64825912807028000440c5415403401910302c40c040050b0070036541c070600c1603094400d42024450301d110501c50b142420341840000304107038411041502d0350400c3e038102e05072060f155002c1d11103000210304480204c3e10504010704841c0180d4991a002c078003d50454200c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 466916474 1250 466915224 466915231
    0x180209040e0c0303070f0213050c1b0118020618030111041d010609060804320d0c081b0a0606030501050f13020d0201140d0e0706021203130b100b0703020c09010e 71
    0x6800911507400070030704900c641606d0300d0016100b0751205c810b0742c6513281201d0089504081006020503c07925200d100c6020041c11551403000300500680c00f4200518410b0041000344140070004160344841c0a0800324188020040c0080c00114010800c40c03031039030028042c070000034200e01c000340308400d10001060704851854450b03c5465003098411140c1110080c170541d801000710f01c031108000311014160001e00060003030780c46080b8641a94600300300384640200304111000303d400300880c0019040711801c4a01007118004900b03000040c606040001c05c029190900d0000300006004042d001544600c02c1c00c4414041036a0b4540126000e800450000c3d4000703251800d118010b50040728a01e1490b0352000216003851103c076420360540b00e0040d07195000380c12072602007140742d0b0100480324008060b0f80b4054110718011b265011a50014034018120744003003804100304008020400001c0c00740941002c3e0f031580d603410701a603030340384400045004500484c000a80c035409402000e00 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 466917724 1250 466916474 466916479
    0x1903021b0f09041e12030c090b120612070810050f100f030318030f0c050109090b0f06130b040e090d0e1f14041701060608100e040c180209040e0c 64
    0x106803110f031500781100d460200344404a03d840460304002c12100d60b017400040010b030b6008913900502c060f008040781038035400501d603204280400003031420001200c40d84044180e41001d80d808900c803155182104035400440140035110b010340c5035004507000750780b15180340c1c0f00d030702d2407611507040d810000006031244903d440695101400084e21a9180000c040300d650000e0103019142d440c3e5440024250310112403400482c5010403541d41c110b40c100c0020031001d18108a46c15403040803942c013500c0300c0411440307804006020351079a4454103005001d810b1504405440b139855171b002001c608400e5882ca60640f1540304c5481c9111711482001d04c2854000d030220900c90403401042405c0d1001100c0c00c010300c0401804a0305085490014000030894010103030341c810318200155003168403980210007005070010802882151b130107c03500441d59034051b0f0710003a0f6100e0500b104402d030550030a8081131a41e45410402c19440c1d000703440c0210302110104021111401d0341e42d917400c0c648c3e14054 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 466918974 1250 466917724 466917739
    0x605090105070314041a0705010b031605010c050f030a021e0105062d130903120c091502120f04050301051005220617070608070806031e1903021b0f 65
    0x8000070321800d40d1101000c0904413660804e5150344400b2143c826582c1c0080d480ca001081e02024000300f40920341840c641603001d07210070521388031401038000c518080c69041c4a2088660310400c00c04004141d464044502170301d4580507803010007510350400d0f810034030480102d40c042030080041885900d02a000040c100015081e8065a00c200c0c1da400403400b4011240d003030302c181220303100c1056030101c1e4a00c0e08000a4800013519010f444d442c1c0e041c540100c0d0925042d41300605c99040341d0721005544115510000000e00040100d00d49183c0c95080d0f441403501080004c416803501d40a4400e0340c0c0110000d1109940c0e80c0c00c0c040142106202d5035074407042ca25252084242c5803640301c60000d603411800f04103542c070784a5103400303016810401185507108040410105920400b4650440c0061070404070a080c80d0000a039952100e002c42e548400140c041c0781c18114003040580b0460711103a0410b003008140f814045d40303d400b040c1e00300380320740051003040f8407901d05113900182c2010f0080060 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 466920224 1250 466918974 466918987
    0x2060429070f0c0506090303220b0103020d0f0501060308030f090d14130801050414070501020601060509010305100819033218090c07060606030c020616050f0d0212010605090105 78
    0x1c42d10300b00d9503405082031000408500002c01c5003880b40d507104503002c8005650b00d080c10500582009030605500c000049994120300000311140c1803541100d804480b80e080f048000c3c240047e010403014030042156190810000400c02c0b50006948120959020b0401c41d81c0c1d60202c0a0311100100540c900043c503064040b4078880d40280503040070041a10744114642d240c1c3c2901d0300315107040c1c0301510440750303628101c0042c000800c940c0c40680b100b8805040d15514041024103a40280000241450b840e03400091450000410080041400360200c41ca410300025003070304c0700c100b161825000601c001e00c10b0701e13152514401030840c00b80300350f003880e80d0040d00034032041468010740032a070180c40c0b01e40450740142c0c3d50324039514081c46c150840e1903500c800ca443c010f0121109580050141810042c11844594000c1640caa1011750440030207195001c0e20740468a902c80c0780c894070190080494110341c074050383d074080c0c456881ccd03018001c2180e036207441059900d03000d60340e000b9000407000c0040 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 466921474 1250 466920224 466920227
    0x50f09010602150a1d03091507020109060e0d060c0e0109080d050904051f080d020c010c0f1103010603120309030e0d020307031e0f0b1f030507090b030309030105070206042907 77
    0x40a600c81d48140001401707044038050380417a02c0d0840c001d24015803000c03a009245281241101003980000c2d2022480c000f0036600107054031a15104940a01202283e40c1100362121030314225135660219040001072600407018020350608202140000c01080010914000c0050b01802400c01c5458103800c05801300104005040000c201040c40c01401d0760800d01c400d02081384501078004c50018202c1d2800c0300400916014419408038100040c203030225011440e92903880d80c1803030700514401812070000d8080b078054003130395200426441551111140d1982d240d40704045440c400c0d40c5e1010021701361800c000b641c090015010358036411452041001540c581441c040b00c9041c0f00c0d100c0d9100f010b9440309942d0126100040e51010251410000404800d0100300b07001404c83d645105d0031421a00c07010360300d0000d070188412140e039505150350150f03020019a031201c0c100034028040391924140007901d402058400711050807010a00803084805040800d05540444030708000303a5940490 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 466922724 1250 466921474 466921513
    0x91501090221010f1502070e130302010b2211040b0a0c0f0c0602070e06011b1205120a0f0c0203030f040204110702030105040c0f0f0f030b04060b0904030306050f09010602 75
    0x109000350400148009599031280b080207000f0090312000800781c40c03070960b8030480c15649600e04001c41d0401a001d003c1c070140d04000e02c0d080607100044400036110b902d8141e004201d0364413003580c480c00c221024881c00c9050072040c081c8400c05a0280410702c041e80d0361600314012030190b015400c90034014502014800c1ca10f05590501600d11142210302581f21005e820101e40c00c890b00503003050105000c240701e174040b40e942001c02881c3c03130790071005000c02e500c428852260008065607007040c0c440c0c01261080c816039410b100c60494405d002c0c00d01d22a10001015018a01040c4504000414072040e0010040c1c9210790000900980c1940d16a401c101c001c10000c942105c0c181802d10540015803401d200703561140c0e00c00c00701c0600840c00c004025142c1c100e650300c40100284820700a020032b25035009590102c03940302d455601191240d29141015001160344540c01403400d00400c401e05905030400401c42d10191992840845984140103070b2040034014040585d000841c0400c5010343d801 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 466923974 1250 466922724 466922737
    0xb01080109020f0f0c01020904060f210c050a090b0306010915030f0501110d1a1005071e02151c11040e070315060e0f03150606030702010207080409020706050915010902 74
    0x2003c440c81d20010b640c0b002c10300c1c1c11148200c00940c0d40460340f07040906251164030041e00d00c000d00600e03007034500680c280f02c181143c007000c086105210748010400036015002d0001d0b29000b8004925240c50328010801080d6966001d40302e44114400001c0400d1107100e841002442d1080c40d004e150b00315158036881d8008940300304c95640d078071043d8041a003001c0001c0d003013010038800301048000c0060016419480c1043c0c0c0e10b44106800200d8032000d40d000411904429400085020f07003c2113180748598200e41d10300040d40180380e012000d04a00503020041907003954143c0c240455607422f081d00c0e004c89061f03108410102c2c1d0104018030440c4e1240c81e55030741c4130b269468003091920301b04510900b802c405500c47c801054010074a564646402024100d160f4400d8005100b0b401500107880202800613201a00070701c0700002140f9942d00c00c0d01118007998222030216912555013510a0080d070110100340d8800d0b2514001c12a1607901080d01116004407611000d241d90a01140200039840315 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 466925224 1250 466923974 466923997
    0x2060a18080f040b030103081b0f100b03010b030a0302010212160e0112020921071706070e030307120503060f03030c0d120b0409050304060219050619020c060a0c02100b0108010902 79
    0xb80f00005100040d14021406984610141e80e02d80040030014205000003d000301c0007500074421502071040005a60600105c0300a4045101c2000f2000700b401004007010854140c064000c0003400e143d0150010503400f009032014082d6651408021400c021042039400e0000b0300410034143c181d071042c001000701200e4503200601c1d02e44560005004010240b071500c2c0002c00d4511503c104501c01e0281d0700081440c5059954440603500d0010340ba0071009100000380300c4a0100116261820000c1e00c800380d03408840721460340141e0b04060b005400407900b051080c1d0008d80002071a06020060320741c2072143d0001070031031003d50740d020f95a411800301103a00e61952044d0034005a44c40d400f446004034000c0340030716525170410800034100319102d42011503090301d415002c000183d0010380c070765102000d07250441d403029a045100c000303849142c14010f03051040d941805082401540711400308002a001c541110303900390340c0134040d83c2da01c641035070102c0c0700540104076040e0340e6001080020340c02d = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 466926474 1250 466925224 466925227
    0x40803070507170304230304030c051c0b0703060305060705090102031206010516030305150105071e02010513080114092d15010e010311150403030c020a05030d05070302060a18080f 79
    0x44005200880d00304550650301b00500840c900d60201d0012242c00d1051041c1c1d0145182c20309680342e600030503030a442090300800c50300a0000300c440310546003010840e0303c07040800700d40c140440700a02810403800240d499005490100e074102d070180c4101c40440c50180c000e141019452516688804001810306052110030800300e14070400301848403000343e1003502c0000d480d0038020001c1d00c44040700c10b4428140002000140003181464124902c0b02c02c002e20a030555641a200485a9000c0d609034030300000d0100380c0c041102c0c0010b4000d859110601d4590450507920b01d10b0f010740e50129010911148514410044408110b105074080700444200072903040345590b82c0c8400c10200c1c241d0140c068484180014030410190120044060f00c00302c6a403010f003500c803051200f4070711482c031005050005001910b811500e43c038080c9001050010283e60b0440004240034009074407411044006016440010703003181c40d58072914801c90552100f542007880703503582c1c030030b51a8000f00d03946a0f403500 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 466927724 1250 466926474 466926503
    0xf0305121804051015020d02060109090218070302070602030a0b10030c091418041110020a0b060d020d060905010f0c180b031e0106020a020f0303090f04050c0403060615090806040803070507 83
    0x11503001c1d0300a1004c481e40105070701f031003546009040c564181c0004040c03d0800c03c04e000580c2e140140306400003920042c405082d02d604c0400d030024418008000c1c80d6074004810440300d920a5480017888035401e6403500c07003840341c03605c1c00c404440c25001c00d0800300302a84014080b241001c03181e00c0c0004409003102c102c0004240048801500c111030444044141c500e486143d030504150f6060030481c240001d191040c02960303038641c00c4200816550080521448031000c0d540d5541010b0072158000360100309809990519a000c1c010224070b60440508040850480314450900b10b040501c0c1e62504a42190400b900c0311001d81c0007429214010443c031171142040701074900d440f402031085800500340c0030902d1051003210007000d807095200b60401c0c00804c080b501c2d07a980008803e04129400201d9079148446008a800b4070341000d402103180440c00304201458900d40345001c0740d29201c500e8426900e2102580d079140803200140b8102d018004070f20142e01800141103450310911040c02e5425 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 466928974 1250 466927724 466927739
    0x60405041505090f011b090e10150e0d0c0503160305070e06030a0b09150a0908030a0c030f020c0c09090f07090506060d181703220204020d060f03051218040510 70
    0xc950306c03007139840c04400c501803885454120600e80c0042c000815031216034a01146c08109a440d04d201e8150b07041380400f41e10205a02c10700e0f0505541000030044d181e400003504052200d104a0301429010303100d1000880d207110624901e0600b169404001414085e0510701402c08001001e00f041d90148140c2c44c01800155a100502c0c4c2308940b02001001202c441104148200b00003901400b6020719203402c1c81d02040340d5108891b400041c2c02000f044280c401c11044000f4032900d180340080c9840480e2115180c00c000c20056034031a8119584c10450b1501d0440700d0311004940702422442d4449582080841c03816009642d0214008013441d0804100840b500251494803240003c4100c0780c0003050200703c081c0344180044240a01000d0940c60600d50303100704032408220045100078207182c10011541c90360104c4070821031544080c0710440e651948010014443d0004403484d001c0c800c004250900c42070140c0300b400d40e000111070800710075101071100410303020b010300000d400394010203c2d164 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 466930224 1250 466928974 466928981
    0x91203070b01081c080403171506190305091912050f03010f0801181e051f0501050325030201110a050a052409030d020307110a03020a0b060405041505090f01 69
    0x1d01c0d42c5006404800c690301c3d413070b14040794800b4442c01444110360070b100100394007a1b044120500811140320f2507480c0c0661001c0c4a46410005541c4150000b034900351081400900c0d400c00c0300503071018005038a84250594964900e8580703090352807203c495000225100d00a51003a840d1541010f80c40c104000340302d11700b280e000342c000f00c414000d000c40801c001102403094120303042c48842411100a016550200c80e42d41d038109205c44000d000c0314031414880140817945002c008220500c50a80184a10358064242441920306c28000d000320a0700c00c031400348103246012a41c01c0324070603041c00d550040d22008440c01d440300082c400c4000d08000100100300030b0710070303500410060240d0202203543c01c103900e402e0070910030404090300034060401d00005c00d40d0042d02c0e5900c0056141d94502e1030032503e11106080280c01840b072455844241500810200400307801800329a5882d95540240b000b580e100743d400401c66540f1108120310740c1056071069410442d4a4165000c0f40419500745003075 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 466931474 1250 466930224 466930229
    0x60513080c030301140f090402090a0e070807031b0b0a121103040303140a0c02031204140d1107090e0a1101110322080d1b020411040305101d03091203070b01 69
    0xaa42c00000140300c0d1095010300d03414000c40c11218405813204a2000c90841d40c030140000b07018600160220700c142a442e040440b111034460708a132041c41d61744201c6c03607031100644001d54505400e4a91340b043d1481042001041e03030b10b0603495514005900390205d0744004400b043c401c83e6a521280038803082d1751703e0700940c000c90107540c011512a0720030004124035100075080120350351401c2e070907410441d004030030780d007208a0782070451245655034100b0800c44040442c8403200c0740142d6455800e19600b001310403040e10400d01c102c6d500b00b61138480d14822100c0e10040204c01c0d501c03031540d650010b407a100c04203400e400e06252005400b0311101382c0c14516080381814070624500d240c6240303c508407480341c402c001c01051009142074480c0303400240c9100941080d40308440072460b141d40554441e9080080809034060405903600d503641805a11052150300c09411281420035080491041e0340000d03640b004124043d62400320103104005030a15541d8143c0c003680000d105481c04180c08500c110300 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 466932724 1250 466931474 466931497
    0x81803151f18050a05010503010c14070218040807050606031b0f0103140a090515061014070f140f07030c1e0801020414090703060f0e0403051c020c0f06010302060706051308 76
    0x202c03410198130b4035041c0c0b2016041a07000b685480e007403000d100d5002000100e9109042c05c15a6246414008140069201710007404150781840900c401c105100300100a0140a201620001d031204c10415846601300c904040c0310014a0300c2d5901c843c40c0c40e0300e42044a8005040001e000e2000c94018110a08211051081a5610300144007070010a01064540a1903400c01c1280303440c0460000382d001082a2414081150041c1038202042c501411a815030b600804202080300003440d00081f42d11481101280c0d50007040c508102e840000a10041501d91003086200c01900f0481203000c60740656a6050004071060780001300c10500384000c00250a0004d41440d8030315a600600034401806000041018070701082000f01c00e107400c04082c2600c20b01c0d05007000f01d84882c00c00b1102401803908180904000d0b410b0700c0c20741c000301d600400c10082500d05848483e01c1ca510216241d200900c0041c0d0841d000308506000203005074081e907404200324250144606081e20740890036080b8129061 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 466933974 1250 466932724 466932731
    0x21060906090c01020708030301120c0e042d05151302040509030d0e030a080429070309050c0d02030303220b0708090c0409020d0f08040b07081803151f18 67
    0x60803010302600b98200428001010390526040380b4a40d00d11051003140c4440c04110301d22010400c118824400900d64030b84503d140e81000d0074003900d40b540380d540d1460011000c905118060f110f41901e1400143c1100150604107440d0350403003600c050062466912039401c0c90840016922881114060780c520002540c0307034407800c400c00d000c649a90101d952583d00c2400018007442d8030402072540503600800001c0c0d031241ca06100b290480583c5200801b003030106041080e0f00d54141e0011540c18060001c60300c00d0000039050101900a03840c020f50036030000c00000c0c00d002a0405091000c0a032035103004034156a43d01e9820f8020016104d40c40000c4806090024081e001c0045140714101286c1c100080c0e46580d000031803002c0e445c0c100a24484d00504490148081c1e0001d540c0140100b02c3c0180c0e4a0b03455240c0141d640c0e010840701440342c650a01131289508002034152030b6200100152131043d140d0384c5d03540283c0c00b03140f00000150070030400c010600031901c8105240c62000c1e9007012 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 466935224 1250 466933974 466933981
    0x4060602010e060c09030a26040806042312031003051203040c0e1905040507050307090b0a150c0b042108060103050f070f05160c03051609020c03040521060906 70
    0x4030304103d4003030030150a00c3ca06120840496038041346106074503070300c45820058203903c0f09104010100958044030040404200003500200114050340b0491191044403c0000951007940c20b01c4682011100d00e54080341c1c0c1c807001911224011900700e003c01c01195a4181e8175030700d06103003c444c0b00c0014100300b004000d110400c40d03241ca095000d080b0a00d16401c0b5861f090324005608200b20b004170a080742c490002c602407050900055014000203000d6402468a030100f4202900c41800c1050003600b4480c400954640440308003003001c100c0f640d403c5600303106902d96012488015201303070307645408800600c0c003198050b8900d0b0360482e0181c41c0c120841c41d00c20005011100d000b00605600d105900c100314609900101c4036501007020300785a625001d035151407102c60140c0d044000c11014405001000380000003580107090002007002101141e1640002c0d0240d020704503003060103170301c180800d000e140352290000b0f00680c0030310840c1c1d11517024454038a150010039114175000d03070095800d0 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 466936474 1250 466935224 466935251
    0x15040608010b04080a120e0901030c0f06030209031221010311120307020d02211204140607050705010804030509090f040b06030d05090d080c0a080a020607090303020c1e0406060201 79
    0x31401485404801403c29103040b8815407528800c1400a000e0002c00380710400c014002c2948001c0b1a00c058004521583c6a02e01030410034024080c86401c180b0501000030350b03174071a0085034943c03038003e000707402c50f09024841d040072500007030086e002c8409450741c8081c901009450103802540101c800c100c0b0703d21848240658004480207050403034004001102c050b07200c80c400c1c10300c59941640d80401c1e0300b01c40351001c071080290305441e04c1103000d09818032501d446074030040c009950000d40f03c5154400d08900b00181c911605000600c50703007141c40100242d60183c00d110b5481802800c00c0307498140140b00040c43c001e0f044503d11907506141007400103128030183e4031503220005030024210303840503010192117030203a9070000384240304260b203920070420540141d449010300c240868a80c181c0c0340c0b4000c5401e0300426400b400501c00c2000045803188500705602c116501a009025128041c1d81400329549585a04045e0b00603c46078101454445110b03090040117294000620b45500440 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 466937724 1250 466936474 466936487
    0x3110d02010c140306010e190b0a08040c06020105010f09020703140705030a0f050307050904020c0f011e0b0d080d020d0b1002150c07111e060a0309031821020d02150406 74
    0x101da10043c0802c2c8100401641c004280302202c00040b9100e10b00a10364007240040703001503412150b00d90b10007161211740c580d04040304a009612801ca820100c68072842d00b00d080301c85c248540301d07408044802c01c211f020810390044c40c1c018000d280c480b0554500d45107a1100398083d4100311459400020f4203031049900a41d009071040c000d103003952850800c004020440d018031078a46104950010b505c4a401c1c03001c0002540d500c2c074070720003800300040c0380e454010a20b00048003400340605004030b095051916120b407244851f884580c090510b803000c4155802500700840c5016880d40d1001c00c1c2c0701da9034910002e48040c1400b903009100024106801004024020b031046001040070f001030000500300c10108032181d081601c01e2200400c40601d420400c4544540c1a50480301c0000d0b0002c100747e054020924203800380d2125017416180c40910305504d003092240311040c1a0000600e01d254a56891214120303000030140c01c005005034000444804840c5071200b592440041c0400140d9040f90 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 466938974 1250 466937724 466937747
    0x921030608070501050f0915040810110d0b0d020a080609010b1f031107151401050d050c09100504052e120204020a03090609030207090e071d0403110d02010c 69
    0x601440910301c0c007a03103a5507840460042505004011a000e0516080641a121890380050501c4c07031740e44101100c1c90035640305004900940c02804081d85008695010320018449802840c0e0300c1c2034403141d83c0400030110003c8841d4000090002480541d41b00307085040a0130501002d0282d506000302c07801d003112203102405000b00010404281c4420b4100c8081040d0045400c022500c0d04940c8080341c100c4c8140c203c01054010003044245c01d2120701c1e402042c501c81241840315159807034004101074101d400340001d01c203a021201821990400b00c042c107030410f40c00c1c3c4a00f4140c903114000501503840c1113907004914489200f003071082031007400030074802c00e900180c0c20b00ca050510540110741d1a4010010b80034640003d05410b43c540700307a100d0030a160f0070032400c100e0078540d40340c000d403111890700c0741c040d87c64140f0364182c7e0110030205003102225509204c121100ca0040119010141d00a0003903040c0130136040080c06046040c010121004d4480e0300010b540d108480c03001d428540c400303 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 466940224 1250 466938974 466938977
    0x60e041b11010b040b220b0a030501020d0c140d0908040503030706090b0115080a0b0118170601060503010f0e150301140907060504031101111e07090b190303080c07060921 75
    0x408001500c4d150b101c9503c0782900459460401281c000d04220090007c182000b60040007400c400000e0000c1175001e0b14030750f112040c0501164102100c2144e400135800000354400108000c00920703040198085107002d8030951000d03042a40d1640020b0a41e04450006e9406907105c01040041100310140700c0d000d40640d180200d407813480101c0050142c94000c000c01a0240c3d1a05a6480c5a0040c6201402142d0486903074400035150410520b48131569510007182d40301307010010842902030400e5a05880206509000c2c1914124442c404034201030001e0341343e069105000d5103692005c0c080c4443c5c4100d00c500b65040d904080001c90b14040d850380c008030412109010a10000c0c2c01c1100d54016100241303082100c0c0003180240508094941e4000c14111200c1c2080740030b5600003099000c221906104201706002c0c15800348443c8040c098901031200c49000405d00c0001e00950642d46c001004550b8a420a612507664408413942203109030f50400c0c00d041c03020400c80301c6c0050150315103100d = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 466941474 1250 466940224 466940231
    0x1b0c04111b07060203030f10051c06152405071b050a1a161e150b013e0303150907030e060403050a23040627060e041b11010b04 56
    0xc010f4000e40301d000c06003010030507a0589010502c074000b290302c03880292000070a20300f0319407804014440c100340e4104c0300704d0340030b820060200c02145154880c0d20880f499120680b00c5441c003000d9000c03d06030b0000c820024828144030100200d5814400c1e0aa00b042c0c5118006690b82888100030358154a6407000c8070040c5030f800c4140345805031601792010020b02c0102c44002031600d241003240a0005049021040c5c14441c0c41e1040c80f03080e10310102d5818202d4010003002403007200443c0c000c084d040c280202c0030000c10f40d06054152071501c880000030700071301c6c050191806406241c19640191040484551101004074a40ca0032524680e0055000c1c14200000e41046813440d459810007000035041c0000400c21804990142040280c40c00211030800d800b0445091a811503070400e0040c0c00c0052941e4100c0194520540b01042d46841c2c000d06180501d491f02c0421a910f02c900300440c0c0e005911803d4030f0500700c4c1e0345480c1301c12101150302c0d095039100d01c602d02d1608603000c00a6081c4550304 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 466942724 1250 466941474 466941479
    0x50a050c031605090c09180a1b021c200304090c0908150a15030f0c0602010c1e120504050a020f031603030c050313171c051b0c04111b07 60
    0x5a0310350072011544241c13800c07540381c1e5540f40c120880d07014001c102034008098160140b148008041518031800701a40c080005040044601202031051000f100169015050800320009000300d03da000c0c280928100a040b5807802e001111011142002900345c0c3c800700d0140214401342c0112084003517a450509151880d040d001c40d6185660752042d403188080c400841c1100017135410941e000c50180c1780c03602426030343c1c0ca020074050255201c00c5d0b445885030384000c2000b500c18001d0000c0307100176980300c2c034212200c20b80f520307014441c9074624000d100000101003207404241c022603101c3e80c05400075222592a600500800114484041d4800d4005a80c0c2681e8001180c0c00c080a91340c0601c0c012403640310500d0143d04c0c500c01c02800d08011300341104000b44042c032014640d00b04031041c0c01a1034901014001e000d440000100a980220780306100450030042810316040c40c40c40e03000c003115038911800c8045000c03240e8011403020f402400040c4980d80355001d05881003040c140800422013981b = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 466943974 1250 466942724 466942753
    0x10e16051603030902061c0e0f0d0f0207030204050705121f09090305040503030c0703171603080618011401030b0108040c0e09030c030c0105061c02010e1002030f0403050a050c03 78
    0x4034868100c03900e00c81e403000c10024148681d1004942c00ea01601551b6503c000d071440c52240c070031060030800514107204400b07405480c0400d040201102d0000102600d599a03581500e04003003840c20581180f02e080d5000000d07aa0303078000e0a008000c9610f9490303031540122000c6d454000010007200e10207819440051400254071715100803207031008000680820b0700d05e412034140c8111b0340319540c1440041110400540c0c00315800d070071240300d03006110941a082d80020250300032031480074591207512122201281c06030900907841100100200b511469103481955519030030b03040b18100c03980031746811100c4d50701071150010b110b6007400c1c0480706240a58070080d042e4618040c7c1603c9800d0034001c00e0030302d02d042080d02e00c0030811605407a107641196110a0080000f290128804c91401c81c1100113840000400507400e078047e91400b400344a280e00380219284070009050441c0300812044110251880192014621030000341001c030342c0c00d080c44c0d4600b4103041c81540c42604041074140c0d108 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 466945224 1250 466943974 466943977
    0x21e0306010b0d0f060b040e010e0f310605090610030b011404020c06040615140105030a0903020304051017090606010f030c1704080306040e0d050d0906150608010e1605 74
    0x60300c1001d4140c3d80da04031003201d400546004140d00d40301034140348011501e01000f01c060003c0c0d0740e0003545458103a0740d411031005842010f0316041c00c1c45090b074020079900558940b21100e60541190040300c4100d080c400940745075060f160a0325408d03034503018000401b9040c000c40e0b8100ca14000d000701c0c403d05680740e5000311b940601c5000c00c4156015801c102c2c54846405451581120000780c48aa10302030900001a00074040061000014803a010580c03044a81c03190303800880c182d503a1400c43e907030300721714000070a504001074081d80700c11300c070028083d545d1000402200e00f01daa240c1c918050000c454000340c120240050040d900444d08028981e648110201000c0c200ba2030b0200e80340b450041c003038808085205809101c48403c800300000e203c0c5c0f01000b14001c85040c0c1d0200a001e610004184c1c4038402800a580000c17410805c0d10304c008443e03000800701d903000d8800020800480011003500080591200c004124000010000380150711100c9500c81d0303000c128020303008100e0200078202d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 466946474 1250 466945224 466945229
    0xc0e010e0108090a02061308010b0a0b22270f180b07050408010612110306010f0b090402130312110c060409020d0e0d1809060506030a0207050a0519021e030601 70
    0x100520740b0002000c0304020840b8041040d0082d1a05a440d50081c09054070308506018840e01c3d5030a00e22001c14074102020107000312640711940302d0402805c40401d400221480900c134a0254804e400407402e8500c0d25050340320101030154007003101402044a00580b00c54134040d003241c03440c041c07180026004962550811590245000c48a952002e030140d6880c066078100347c46540c81e00c00089030202404901c0c018040c0903222042d41841c0705401c050750743c0b409000c0c46003000408181080a0721414000c1c00c41e00800500240c10b08451840c0d880d030010b1180e100b40e45540001600d1040b054000310700d0300040c4142000b4052401913000420082c0c81644110031845500090300341140d1019402510745062040586003040715100d00108504010080240e8642c41d181300010003600c0c0d84152401c031a40a00f40c1c0c1c0c15644c07902030032002500620030540c1d5038054021001c0010700240b00001900b0301c19030840c0800101030050100107441c01d4103c2c0c1c000f00349180d220b07825580000c2d03080d04 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 466947724 1250 466946474 466946477
    0x301050a05060f0f07080d05090a1401092a0504090f031b050325140f0d02072114060f0109060b12040f060b0a060c1202010204030c06032c0a02040c0e010e01 69
    0x640d0240b900d4086d03498450a80384c1d1000301e1400050103011070001c0b5074500d0701800b80943d01a41400000018200c4040d0500144011360403841001d84002e03940040c0d042c40c080c0fa503080002c9030398030041800d849445a0451b00810f46080960415030081040000e465482849443d28035165a0741b503560720600c0004c4d000c00b001e810030450301d02d148100c0c03041071a510160b1005070080600c00300b42d4695000350113089502030000380d0711040e4800a0300030100c03410708640008902103400000c20180141c0c9050300c0328a104a15234551a0080200034000c14076002d90704002d602d80b070a41c0c4100c401ca13400014003030508014201c03101d18445030703858009400004003000e04040f40b4001c2d008110395480140c00c40050f65001883c2600700b1031400200703004011900b000c2801060032401c038411400003c000001c2c490342400b0142c070940c0720280c003c5038503004502000c8400c008102204503152034510701d510903408203045003098016414040341d2420304a80300ca5480c000a400310348050607060 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 466948974 1250 466947724 466947727
    0x1e01090206160c090c05180105090a0302060906070501141012030f0818010c0507030201050a090f260d0209041a010e0618040c0906110307031e02160b0301050a05060f0f 74
    0x24000d459584500514600700108810400e0402c050001e800c107c2511f05104005410b030841d45d4013810403217000740c000404025050b400c45e82008400c0d0822900140c2007403080c0b10400002c1d0f400d124520206111301508111490119429001461240c02240380c0e006034460540c00070740c0145d40702005841c40d08090805650303646640b0850401c0da404501d096007011040426190010020b02c0c0240c0640d0003400940c1c1d4100c520700a880760f140780140100940440f0300f010500007444d59a8140c005142d0710000c0c0c0540122104a41240c0c00e00450f2a5000940020a1405103c0c0b241d0780401c40503016104503003c000641081c94040071a80243c00c002410f0f030405001520246d11540d000b0010046170340e154100401583c1c0358021407001c507100301031b04403a000300081502c1c410707a810b80d12501c480e03646a145028001c6000d40a40961107802d000044144410b8001c1380070300505c180703542d2250700d4070003002001c0905034007603400390f00c00301301300e20590184804440319205038076a2107 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 466950224 1250 466948974 466949017
    0x507110f01032004051503060d02010e180106090927020f0418080d0501051507030f090e16030b0103020c030f0c0c0d050a060c050a0f2106081e01090206 67
    0x50b00078120061a030391000080504480c425003004024009803001500d04203a0b030315064020440d144010b42c0c84e26400510f0308100780042d8410401d01c59511030260038a83c40c00c98440d403410405c0000e820050202e0800e050a021414440c030407c03808000b41c1c44442206060058501c45880364a44068055802c00c100c006154413960004140362500000c001019007003800c09561035040050181d4519007401c0c0001803620f0070800040c030502403522034510703240d243e5806031102000a55040305010b5080c5000031901204d4141902c50540c20000707c0b0200a90080101101c5090b541141498814000c114a000c00002944d40341d40c0401501c030b80e074200314021700c0d05e4142c003500326550280e10809060b04000000c556020001d1007100103104a104550701a105405042c0e40b80c0c002440e80c42d4032486007032003804c400354000c00c2506611803c0602014480035548980c00c03000c400d0340480d0070070200e1010000c40302d00b400007100007000601a1980000c2c45840362513070408a210100c0d020 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 466951474 1250 466950224 466950227
    0x100c03020f030d0912020141091b0915090c090913060b0109120609030c050d0509190807030b09070b0a0309050c150306011d0405041109070507110f01 66
    0x1840581d80108482e119185600414080c000c042001c42d901c42c40810011a0340d401405040c01460304450050160f01a69800002d42d0399648800003805031807490040421408140c001d0295441101500016070406107030b8440c40300f501c0000c0e014070620380811030304645103481c000342c5400446009000d902e40c00f01c07103540342c040d10303140b80d50058030401800044c001103420700c40e4051140c9010b000c0820301000549900c80c441c8160320b0703903003014164000090b81c0d990080d60428032a0611180c01e142513240e403884d050070410410003054000503072084d58501059504c520741c0f038002c2e24200960900110304d8440c4241e1200600040c0c1c1040401c0052100740100400b030821780007000d0300c91459032002409003409981c140c038240240301c03d0b00c081e400d01e1840201c60b40f0703000141c14915241e50004443c440600c40b900506620b4003c90401c15684500806000364050320612000d012070000b040980d00d07003c1c1c80d40047c001c04000180018a108900e03510803081250528542d1011800 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 466952724 1250 466951474 466951483
    0x60c0a030e070605131e03060c1b0c0f0f1505070201020715030f0513030903020f041409010e072709150e01050907050607051906020403210e090105100c0302 69
    0x305422680110038000c078509034450b019002003212280360182d981d40d0b61511103c01c54106c90040c090800c01d174010300204500d90402a0780304d402e4034018001201444080008400c0d4240881d81140e04000411030038a071712500c103015101da209040c42041c40c14081d1000003054480c40403e104e030210b269010341e030003802184010541c60480000c04251004000c0080c1401102c201c0c0a03450320002c81d03106610b416517210b000d41d060f103880102c1810f5400b00035604005c05c0700240d1094444038451203001e44500748030700901010001055640420b09482e00b0030200d40c0012108035030344203415030102118807012403222043e001c002900d021506080789400202d4150300030a0b414501421480441584020300c610300c190250b0311600c3e1202e04004180c03013001c0014016510800d00880d10308480605014500c0c40340c84018945030352541e44110486000c8400d11104c01c18110700005660400512070507440704488032901c03503041900064581441c01085030400175090413045c1054000c00 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 466953974 1250 466952724 466952741
    0x6090c050913060b1809100303050a0305040501061215060b091309030e060c030901030e070f06051b120a0f0804200d051605030c10172802041e0602060c0a03 69
    0x11500341c0d1210441101117003003550140702c6029456000001d03003241d02540484040c0c82d0707d0351701d044c03134a1240034048000d00b6025006403019540d92200142c140204500c001500d4807a0703070420300e0002c034030801b9001c44804c0e0340f001848420412141043e96103821301100e00b40e45403040000c681102c0c1c00c08031040b00c0904a0180c000d68000740c80e801050002000d000d1280e82603a040c0403080c0500b0390152036100520403513400c04010002844014003840c05070183d4034501c640b610b0069450176130b03185005081e040202c1d0380c09001580201c8540d04c00885900c1070b4042c204410b0354101a600d04051030b0000251a1020b440e003a51103510755220701075940140e4200b0111441201750800451940e0301070b215991007803198804407074190070407140b4070784250a16110803d07000c00c0091221140c00c4010204405d450f5110346905030f1825044003d030540305282d000507103c9080403980c142d40b010250070a003110310002c00800c402c030b500068072a07200c104140000d440e00c040303c60980c094611f06 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 466955224 1250 466953974 466953989
    0x6040501051b1b03010506040b030606100c0203070306021308070807061d120706020d0804080306040b0a08060a060f09090b040210030207020d060903030506060c0d080423070906090c05091306 84
    0x8050020f040d1078084510001c0d410304a0003080709403100f80400044410304c0c40c005425410050004500b460944544194050942001c0844100542c0001d050910782e8000315940707540841d41807100000300481c040900b9500c401820110b051080181d42c600a91141384100700014844d00e12713010074074500a40c04d6201902490f8140d140c120115200c103c1402444010320458451084051151820340e01039500022544d25540b00c1c4801d0102a003a100c8500d0b0f04441180000a444d03c02002128481c40000350002445410070888901d929055400f40d051075082c0724608010464a559903500694103c0d1940882500c03918154003078001d94401075407201402500006100300d80e001009141e2196030100801e9949104000050140b050407442e694401d01e04011082d0117041400e40250141142c1000960b071340b082d24140e03d8100f5014440b60704149010444021103002e0300000d0643c140060001d14481c40c8020b10500a4170700c914814174907842840464040c543c00100602400c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 466956474 1250 466955224 466955233
    0xa0303080a1e05042402390a060203090c12150a0e07091407091d19050a0e100e030f030a0e0601030803040c08010504020904020607021206070e1e06040501051b 70
    0x5080c102c0007602c81da0100c60410b04070841d206131750b40c014801c40c2e01006004042442d0071548000404241c560180924004284c0b400140345407407003048a0102d035841100056982d1500d4480142000350b4503401a00aa6440d500e04094540c080b80e800307101d22440050014540e01d41910300301516000b01648054041d460380840d0080b100d4014021b40c84400d403014000d601d41c42012226182d95100c1c0800b0405410300da090381e00d0040c1036031500641c1c6200c01d0b200c4134802010380001c0390307415a400c040c1d06070b45400900307040300b0a000c0c1e04500140c0704401c21013258204c015075100d200300300610040c824000005908046168850700f2444034900c100c518960312441c0a81c000c1c1d000b564141d610a421080000b11001c0c140101d034440c80d0b028108a0254549500784a4070f508030941c101e90041281d820610002000c00c201803081c400d41c5d4a5070320a0310507600348914031911840f0543d00e071625a00d064500e403940c1c8111012940207180065540300e40002d40118030f00c42104a45040c0034 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 466957724 1250 466956474 466956481
    0x2090301110a120e030a0203120403180f180b0307151209030203131202030a030305070c0b15011101020918040318180b010c23030421110a0303080a1e05 67
    0x180194400346020300e010f0200722801c0d284851302c1d520301461203000d005074401c0004e0310482180100703a0790800e1090411100301c2d0fa40707118402481103907410650a015100341c0820035103045644000011044600401404000320046038441d4800e01402004d12a4880b201d0300e400d20905c00d05041e0440c1b91410008203010746030083d140d500030041207440514400d804622070014005405e0a01d50080007005007200039a0194040c00c401003000003808165002e4501103911622524450403030402c0c00c45440124a0000d400100b500c91560307100d03031061100b00f1090710f81c0c8047d0340c040c0640310181012035849145c00c50b072074041990729a1088201702e10000b445480102c804084e00e004d403070240244406a001142c1003010150050700c1240b81080301217003441e0300c2084070024403000c0d0540303151503100d0070b840044603241c2d105801310f80d031146241020300c0303520700302003014241c00c07201416161b00c0d50310020034040c005085248951b40e40e1440c2c00c1c0c5d180d400e51660441d404031890500c840d14 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 466958974 1250 466957724 466957727
    0x4020304150605101707110d1101110c060c0304051f140a09050c101e0c0b090601080a1502040518040b10051516081c0b0f0d0602090301110a 62
    0x82100c005548050402d80b010030f0b245408100d0402c01c940e030350740d1121103000321082c2c2c101201010b400c02d81131100c152808880014140180d0420180b03586810095103076544440c1c2c01c541d14022001c610b140d05120381403691314041100c6d0b03001410300b000b06480346c80c3d07810401d081000303024910994002c3c0240c0c884000e40c40350841c4600318444a00c00581351303121844501600c1c0e80740001803650300306c540160b103240b0b0007140c03940c4440c584e80f5208070340c0340309042c2010701064031a03484070100c1e110030080020803d0030307030b20107034000b0b5644050045945800d2410b0b5985a031014014910108141104807204255058034002c000084c8030303000304041c0105600764120156401d0f51109811000a21a0b44000c9412411910050800402512203583d10b001030b811600203043c40d08080f83c0c000010500703c0c405081070908444010008402800010b8202c0320b103045260700826104d02c8800302991107900000400d504030a0140c1d0b1040c80b070380007074010045a00e24213080343c0c0125114242a = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 466960224 1250 466958974 466958993
    0x9030304240f08060a0504510308030126030d06080609070f12020a08010509030339070f02101809060f1205070806070302120105010e0a1a0904020304 66
    0x1004a51204052a080407a0454080f070703040320300750b400070100c480070415414103a005c101d170000180b80301c0100805085a85e1882103040074050054030803001c6040314100c050803400e115499240c00e98111a180d5514114a4001442410092400c01800700504407907601004c099060303c0094aa4072854202010010803480c040e030101c0748103820004510081c0080d01000b5914503941d0300040c545031901000860040b80300880e00070410344000641c5d0142409128011031168002c1c589a15200c45001c4c1e01c080100f070a0b492039000380c4207400481c443c80b0010302041018500c0e059403100d10b401c204c5003101503070800035040341880c07406030743c07160707201c3e5807100c2c0301c0a12440e0841566940c0b420314281c4401e4050101c0301c0703022400c100030300702102042c6032009205409442800c1c3da165416400c00204a032810082038001940810141e868140140074043c2401c00390144545000441d81c3e904040c0501135500a171010f6a180c0c0180785c8080e5140d42100800c195620326242c075004004 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 466961474 1250 466960224 466960289
    0x609060c030203091e0c061801021507050d020d02040819030318110402070201090f0305030a1404140f0118060c0b1302010816090302060d050f060901061409030304 72
    0x164606101a800303603109000b1240079400410042010039102018091100c0c00320080100c41d00c03d14118424903202c01000d00b80002e5107052041800700400300290902c80d103081291500a00ba00c1040b100d59044802d07a5103010405100507211911301e00072000078400d0340c1120b2000d11443c0c00c20040e9866501407554070512964090100c4d507550390140650b81982c1c0401040300c1d4890b400145203013042e6000e42482401450f1019080781d0701c030311462220b112a0400d5a5a81001801034103082d004201d648074680d241c01c01600d0589803110300c200071201c160909209840c0d040681c1c0041c1e20441c90f10102d02045081c3c1c112503507440300043c0504030480001c4441240c0000018400b0002c1c00c070741c990407074040e1541e0041e540d94107100049003510171102001d20840400101c0941c1b0b54401818000c20300010000322410420944400c20b60f006110511a030191801444000e5105c0c440c0325404c50301d244030603187c4440b100060700b58091b42d000200c000c00300300398130501400103004940a = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 466962724 1250 466961474 466961483
    0xc110d050c031b18100504060605190206010e1f0e0c0a110d05160503120a050f0a090c0b0d0e0f01060315150e0c070212061b07020a1a0706090609 64
    0x72410110b208044059164059451303214284803100120f000050852551280c841090090800d4445001030120b41040e00100001080419542c55942504264030580c0f609400246400d614140b03400140d4200240131803004103a64401849031002c06004901412850031228003170314240d45d41c0c6009400c0f05503014001542220a60112000480e40c181c407145640c0d12079140c4603121080b005000405801210b241c8010030031203c504d80310b006554010481840041464200100c41520382c20001c0c086e404143e2401d03a2000000c1c400d83d01100850350410104c0d521080e6141200000b1315514101c00400c0c050840c1100013508198410310035a48a40340407240d0081e00e842c650125160b100d040b0b502040700200070b101640e099031246034480f01003186146850411b0b4045403220300750762141c808a5119005000c10540c1e03a81241e810102e40003085401c002d07440d00000e0429159110f80301c0c00801d5490943d22900002003283c1d0b4560308600107108819181c41d065006007100b807003e88 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 466963974 1250 466962724 466962733
    0xb0601170c0405010e03070306090503071514190209040501150f0513060509040908070b09060618190905060420010504150f02010209180604050a0c0507030c110d050c03 74
    0x10303100c0c03084035160049500c85111402e0a041c1001903403049045c0141580c50311400c900000000c6850056070b0806200b400503580320002450305291141811525025660800760100340528102c0d24461384003101031142925605815602c000903c0340c0c90101390080c4c1000001b040705090040351200500140d540c1042460318214101c03840c0c01791040d034880f80071440404001f090301c40e0700548210a0010800199074810741c0c1d95120561100400301c0d540c600c04400c10004020922190b0361020050b50b50369088031060880800996008140d010803550401207205040c000f44c0c400b80815910604442032820141008a07003140110030b00e02449400a04a0f9420f511a5003607170202d07074100414840d000c0c0007407425103c4030f000c00b01c100704540d800e000454407a0341f000c07440359a92449196841d0316003020014481980c2004040c80c20701410111081011940310040306d0f287c5030145400003558049140903129640c444403141d82c440c60000000042c4800401c081c032340c01000301c0448 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 466965224 1250 466963974 466963997
    0x8010e0106051504030203150705040902030702160501050a12020d020c0f0f0706020a02010816030e01021603110106050109030b0403090e0a0b010e100807030b01050c0109050a0203100b0d24090b0601 87
    0x441e03e104d82d000080d010340004442e800c90018220149030040740070b0030610704142c0c6a00200c0c08980086522370016804003142c141220710304240440079200c02e181161034075185d41c80141070141c00341000700e02d0650000c3c9000301120150706583d15000c409003a21043c0c0d81d1000159915001c81e580c020840c01a4140010260300010300e505026034180c645000903541c00c0310020484881e000d06106140d1130350070b110f00781340003031000f040d000c036040d04010b140012a041c0205041d014004d0f0f038000f40c2c507003803003031005030303001040c2d0011079034030030203071001da5a45144c104c0e13540e03595a00c00740c090205503003030048101d840e40007184408400c3c1d03108403105244008010325450340c1c100c400045002480850081482a008140300880c181003035031a103200300807000d003195032000d02a20703a9001161014218542030000d07100050a10310700340030440c034080020700a500000380080c03201052050300d900386241043d410310303100c90900c800c1001048a05009001c1c840813510300d40000c00f00101c2 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 466966474 1250 466965224 466965259
    0x204052805040f120309120810300c0902070804050f01050918090703020a0f08211210090510030b0702031201210213020408010606050a020309040506010908010e010605 74
    0xc5500c500c0e00141c01158612a54840300c00132100400104d04041d1900900c501140c0c01000c1544041300582c3c80ca1404e18042c0150b12030411580c000842c01580018200d21a400c0358410f4040e41c079a04124070f13420002464801218110b0340e0051a0700c030700100c1d00747d061080c2600030f0803c4510039115200260700c1040110303128414031014541c0b10400e40e0031b01400c1891100c4640d8444540400c55065030b480b600018030482c400e80c0070305400701c040c4409102068040c41108000a40e112201c01d4102e042c8109881500818140350040b1a039440001d5005000c5014400100000d240401c03282c02c0550200c99224018003080d80d094a00e4004075280034800011100790740640b02c0d10071856401d20050f141c0120b200c40352100189055006030000d0ba13158403044440c44000180160f482d0f24102c840350a58910790700003414882c040c0140e04120344c0200440784840e03800c070380c0020aa0303904801039030b01c035500740c000180e590310340715040800320f4055000c03a0540d03208841d020306a0042c80711 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 466967724 1250 466966474 466966481
    0x1009060303120509032a01060602010c170c040f062309010c110325060e010207051e1306060c030e0f030703030804050343050705010f030902040528 65
    0x80000381c00303850000301000690f12150708000d0384015a460311003145c49018031680503d0480c1e046401c0001160782e40c0d00700b44155401040580002e008008180d0000341ca850070481246441200702e40000b00c154003d14122006050054052030040c0d482e4000206002148403415a66009088400140c0d89214003030307032280401650b80c1c180d05d450710354444c0780e400745d5002c0c0303103803d8440d0541c0c450203c21105075580c0d841120382c05c1c00c80700034070340007000b440b100c1c1101c0715506641025000340895211244101c80b0429104103904141f12880003290414000c170452800b400d02d42080400c1513540040c041040780e001b95500303540700c00203008000f020500c4440c00c0342d00d80e000c15070405c0002d001e008034580c0940500292800c010500101010180c00c210313200108880c9001038856101c401440030b0300f9035088031100c40300590250364540d95000d01e401024140001380042c0c09009200b504441c108650103002409541406100031081c1080781e6003e002e100710302ca000030700c02c130094132 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 466968974 1250 466967724 466967729
    0x20106081b0a0510031e02070b060609030c0306010609060201060608061e06160c030605010b0c06041b08031b0c030f2a0402072f0a05060c0a050f0105100906 69
    0x1000741c022404030003203001d803188072840d034103070041036980001a880e60307001c131015058625920041461508078150707140030100d8111641c007182c414451030340420b1090300d80d2039002c04240d03411b80d91403000340000b91400c0007a08850340d05201e910000f0034140da0050b200c0d81143d80540080c0a01c039191101a100b0310001c440543d0001140e0104070003411400c1d10b80d03012050007403c0d643c50440164212464020a03400a0b954669a0101001040054412640104054001241464000fa400b00d48a2801400151404461983c18450041000350300f6009061003012250b5810310075903052070b0302204420030980c50150718001141410041103508600d00840b0250503030681c0302402c441110190504001d150005c0800f00710b07261100d20081c005140a071031a40306540341c6c810020b1414284010080130b0501c1c004465a0070f86a81c00c1440c03d45000b25002c544480d00405c0f03052800c0c10b41c100141c51031258400750109448198071181c0500d480018084246465042c41c006650991 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 466970224 1250 466968974 466968989
    0x10f060806040f170301081c0504050d02130605060a02060a0b0a05010206190908121512070b180405040b011a120601050c010605131a15091207030b07050a020d020106 73
    0x440010005029a02c0452045100b5180384d40c07200d800e4503080309a40c009800c49111503004d034003004d0001040c1542a644902946400c618150404004c11782c808038450000703009026464803013152107059007200015280140140b5128040000002d5880d5803d071040307842e103403829660100701c0c1480d520010580e00180c000740010344070309a556541745928001e80440c0c9030b503940400001003502c0b00070700d046e030080d40400801e4280303120003240c0c0b1841c0c90002440340d194480c01880140c4040707210401c881450302d0040d243c803148070040b050140015a210351051810040108105010f1010750503124280c0020300c0c24014500703100001d01c9408265525240d896001402940c40381e802000450460000419055a2107000c42c40540c0700c01d6040190903241c0440c5800c00a02000000800c6401c44010b0720000c0090a242e16034483c003400f59000d10300d070000b01c01000f030b4100444801190f01010b44002864042402031907608410b001d240140100030320019068414028041554080d = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 466971474 1250 466970224 466970233
    0x2040e03030714031b040f08250b0f040b0d0212010803030708040618020405070806120705060405011b0803010f030201030f1b080702250501090602060106050324040e0f010f0608 78
    0x300d0540ca41e0001000e04c09171520078103000b800d214003100a007006150001007000410b00781040c49050031560842044003189171441080b42000b0040c00000326201c0b084400d642e402000440e1030700e88181d41011300140c00c00554070008800b0b41e802001d000104040070041a600c030460755482c1e2005441030700016421001042c04203c0780c1c0d20401e480b00d40c90b0310200992640758041000d640b411500a00403401400822038241030403003002030b01704002005001218140300000d80d1500403409480d04100003c42d41e021038510591002e04a00d0304034002503200c0d80d40303c4042801038003a01081340040d0410307040c29071100c1503008030108207200e1442c9103d01c100c0024125400f10300100641c0842c41803298078440c0c48681d5030b4904070400da9554091405081000140071000142d10900844d40014010000c1da5404000c0c4d82d00031a0382c1500700380c4403100c2c0c044203482903d0700a034a58400c2c074140750320051f42d100042008070310141400a0180781015500f0702c080f286140b2461940c1d420 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 466972724 1250 466971474 466971497
    0x70e0112210903050d0305090d020c1f0903150b040f05220203120423060f0a03020a030621060e1903050906040f030b1801150b0d0f1802040e030307 65
    0x80c54400090740384007a150402c040e6580e41c480e60310b0500558490b6001c2aa6a400d1060151081c07003255281c80483c002096642c0c1c544000c601580d68070300040000880c00e06d25515564032070b60940c0d00450b00100591580308410964200030042c0914ac244590301e000400d0f0170861a0f409a80e11400c98480040c42d0b1a01c4540413124100c03582104980c1409030075003280e150320001d0068170281035074490314003c0c1c3c600f4540400c1e015200e240700f10321801003400141d00c10b1400c1d5007103c0c408000e500d809a15140590419806003516070804407844c070414140c0400c4084541c50024000d003d002e09105215911030042e8651480259415030140c4898080c00820702501c001e21589a002d4082e91800d0f5075044c43c512155150b0708200c40b0000e035501030164503103c031501030000d10f00f558001c200c0b130340180143d40c0ca001140c3c03080480194001c54030b80e075003246036803069030301005420007403007400c40d0006444030b0341401d03600491042e407820a5550b48020000141e901c500103d41780d142c031102 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 466973974 1250 466972724 466972763
    0x170a050c090f01030603140a020f060702060304170c01090b071e080105010507171801110624120d080907061701062001090503070b0105010e091906050d05070e0112 72
    0xe03400c5602d1410301d525520000300256910b010303007560b0000328010b8550b19915204109180c0a02006240318040038480396001d03a9030541145e40056000702c440c00c0904080742d2825440c00360f200d04040300e500e414042401e1050310b41034a80300707203c01d58461034030540031010400120005509070002a81185c0144035a50281d8001d05446000f060101e202d800e00b03446202d09640510310742c41048252040b190090b5800c001c4181d10007070418050403ca10b0a20011411441d03d28001031a440303c2c44e10704005a21042161947d00502c04192110a841100083c00c40c403001e4031882a24401d5141c000b540740d20400c90440e410090f0340c0300000c56441c200040762030307400c80801040300d9040e400007140d0b0a002482101140e5204501a42e241d507a281400d40d42d010059100341c0c107000a003801d610182e503507404102d0f0b1041149041025041400d54078170001c003d1900f00a0300a1030b641c0348071091000008007202203d07800105041ea80c4e80300c01120413848809440206000010318042d600300 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 466975224 1250 466973974 466973989
    0xf030303100e0901020f0c010b0406062109060e06090703111806090c040807060801050a0b041202090408040939020d030f0f060902090907090b1b0a12170a050c09 71
    0x1001c80001500b800e8001b18016020381c404400580c0603990360706012800c0c2420b006a01c000e0905040281507a040c044040c180b0700c0c10111840c0138140d559042004000d095400083c07481d42c400102d030007529004000c00da69124500060b07407168060f810403031403071811001003d108042c4152035021a110682403050101c3c01a110b114030030801d200102d80b15a0410445004003526550b4103c154901000c0c4204005281c100c13080d40f88040006001015082e01000320305641581e080c582503440c1c2c20110101d0140760040b00c2600c0c00c14580041c102040b5500101d9030f5031820300c203041117140005001c0080c0451280f40c01681240510750b0400780680d020641e0076a11a4011401e4031702102404103d41d25608881c0d08241d010a048015051641406a202500303040500905060448640c0c1e00c0c060160006200c000341501b00301102d006102101c2d00d07a911204030807100c1c0356038001908044450390000d661814040c0042c0310344201d400307031902523448142e02d10f1824503000c1c1071102c203 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 466976474 1250 466975224 466975231
    0x60d0b060a09020c0d03060914040f03031e0f0e0307021c0606081005190e030318010e010e0d1e0503161b031e050f030109020c0f06040303020403020f030303100e 71
    0x1c580040e50008112950b03000400708421000041c061142001201800f2508076800c40380303c00b443d1900c2d244500d000e540005030002d401c895881e80d1400b141c6401c078040c1070150707022164101c08100040d050a0560400c04011460200603c8070b884c040700210340e00e024000c80603511851900c00920a80030701800c5508040c0502c0c13010440c69140ea40f9a40b9091206507c40c103000d90310320400c400045400300e900100100c1000903c0701e9511210039558a0001800c600e030502c8075503004c008205d00175400907001c845000001d00c06051081c039595117450620003000301113200400f0b810f9038280b940001500f607030840d80320181103450b1301d20703001d030540c000c40c2c40181401414400141450007104203030306018031943c0c0c0c6c4003022030580c51020046600c01251014040e00340280c403c0c03034003024247c2e815255407001c0140c846044541d0103140400003c07003516103010b078002340818580d15400800540303000b0350303501522010200501d552403208892401022030a60020700000c000f890b0036940 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 466977724 1250 466976474 466976479
    0xb0907030507050f12041e150209030c03070906091409030304030309020a03050a1b0b0c03030c0a170112020901140f0d170d021b0105090d080c040f1517060d0b06 71
    0x3c1c807038004144c2c8415482802c116011550720f03c00c210801c8940c50004000d80d085070003c6d03102480315600d018802e0010b0b501001c05d40d40200d20204a03440401964588e124002c1c200d0302030710343d10800640140350038054078a44078202411030300c1c82841000c0041c013441e4048000e42c07861360350ba02c0440080609090880c2d000f810034400101003001003003ca501c00f4010031200c01c150490700b0021406507115403041c0da10180c10b1010250740500131041e41c2e4051203120401e80d507081c49090848440c0e174420708150440d09002d002281d40c0884d1806603440f58170030340b090362043e43c0310032920f1200c4440c2c10000741d026500780036059240c00d02c800c0d480010ba21503901c070022200801d4000340c25030001c00c04941043d07800300b800c3c0c008021464000c2c201c1c42e91f490080049080a6031129115160b611400b001c6c8510b000c040b440e0821428110b0b0b005111149803510100e0303c0d000102000724076212100005001d008030768500c5280803c699010b0f04009015a90000142d941c00304a04401417a41d503 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 466978974 1250 466977724 466977727
    0x1b01120c14030106080a0b010e0f090903040e130c05030714060d0b091806100623040f030336150c0203010e010518030301030c03080904020d0f1a040b090703050705 72
    0x1405902601c0550302a10840c4c03034988003031801100c8001183c00c00d4a90b2810001c1508050000780c45120130346030320305803d9841800542e111505d1510b544101e078014102d807211501044144803001030308082052041d540d501c03065954070209591101c0340c1c00354416411003038440104030308d400c20007010b10f1000250042003210707010000401e00130045840c1c140500c00c10702030782e11161003886000d07480800c003200a17546d242050700040c041d0000340b240c000e406402c41428102880310405890050111960514030640c40345002409013010780c1c0c290041d101212504216000b400106110703c2e40c00700074441902c5d250107107400315102d640020b4828415070f0310040016840a0081007250f0018a00102d404c3c02c18240048005985220201035a00b0900050000814110240341100d030002021074444243d400041c00034802c80d0fa52510691510552620104054214180030030300130b001517032503907010b406000603a50b0208a16500500e00300c0003c0c100c90113079201c81d030801074516016 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 466980224 1250 466978974 466978997
    0x1805090705100215150a0806040f0f02011808070504051501020606041a03030d0e0706021209041a03060405010e0139020304050a0305160603021c0b03031611031b01120c 74
    0x34072060b901174401e00000e042c6943c030140a4240000ca41c002415000000c2006250646918040415840300108084413003400700040d60300c0346c0180c4d500e44e55007080f50240c06a5078032020795102c40f6442543d00807410580040c43c0114105c00d0348041c0070040c5c010380615546e600c2008000c1480f03c03203800415601840680440c0c400300090b294071034403d4000211403060b08203092030320f505603110307504551002c071001c16145800802d817103200b1001da90100c1ca85011903080004400308006498151190000308002c0c0001504542035454035107000300a2075400100c3c125900809040038803c0143d500354660300c010500014080e04c04142c4156414540c0301c4000441c0310040d944283c2d4154400c491030264202012100001009281401c5141500700850b40840100c82d448011034242e54034460000c0f601c0a008035440c00c81c4d9848804200b000a261804800d01d100d07103114042d00c100c0251038068503040d404600c1d41801612612820003210202101900b401d502c80d004000044500 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 466981474 1250 466980224 466980253
    0x50a0b0408190305041104020901023304120f1404030b19090f0627080306010c061e060b13031e0c030305070302160e0c0a1b060618050907051002 64
    0x20b5120066901060a00f401d041210020300e0a000b40f61150b03104206d000c0c4660f8001881d004454108618040c2e13145680014481c5441c05039a410705000e030b08400c1008000d400050f88034004100d031100e01842403c4c0d4002c4441090110b903103407040108010a10218004102c4250701c945242d0220503221107040b0407100703503403020130200e884c444c410402404208850240030044142c004051501d5000320b030003d07090b1405001d002d400f2180010109400d070340f107078804040c01500010140300002c0c00c03000c3d072505802d4034407001802e24230344680031503c410b18904444a4540000000801d00d0542d01c500340e41114141e407888402140c9134211001400301140000258080c8e101c4944074102414041d0904c004101d91001c21001300d282408032031240190140c10815007184030b6200c00e40d800060300d00c040800054094551202d00350810442c5c80c0d0400b90548dc0030641919440c000c000c11340050300c01c103682d40155500f01c00d0092005040aa20009540240784100d03881c3c407003076880 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 466982724 1250 466981474 466981507
    0x603020c01021611010f140306012714030f241f030318051c0809060d0906020304050c060a0c030f05221403030c06011202010c150906051003050a0b0408 67
    0x2c0c21180d8403408a1303140070030342c0c03c14503020080040f400d180c1c3e00703200324411569081c40002c180300d05004c0402c406080e040784100c1c0d0310000c10850107031038000a0b150714404801c466900303101480ba01c079014408043e010003090114198a200c040036041c3e1094503e4645120740041100480000401c1588902e4042c590100c0080d4000d803640071000ca10094155160a65904100d00800f081c00e41c03540c0302407504418404c855040707103450340ca4005140c00503040317100d80380c03a0321131042c1031401150a210040c0d0040d4040c0c0d200e001220340c20a207070014026035000b41c1c0303405808100004840c00129000700d011222500c802c1c074040e8030304040321021071116014044e0160035290024820b100c1d00321000d510980c01700c021002942001d101d00f291540e07581c414000d5503580c5008240130801c5900404481d05d13801d50055444c3c40000c1c081c82d061008005c82c0e01c081daa664280030101e031140c03191982c01020341750041c2c040c2080d680a5201c0b644003d03c050012600d151042140740d80781003030b40b503 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 466983974 1250 466982724 466982767
    0x612010b030603071203050306090a0b0a0807051c080f09010903150507180f03060e0703050f060910020f0405011b021002070302030c09010b0901120b0a0603090614010b040603020c0102 81
    0x440341512814002c00341071038442c0c0c82e000b80c120341c0b0102c0c1c5008003080e00710341901d600000440b034140d05a50366030b40940c0a05403403c00c03140c000100d0f40000c52015004507401040d1501943d004610044001c00d0b90003c07031200341c1c064185401001442d4100281c400148901d541c103043c072411882c0c0d00e540f51441043c560b82c210351003994134028040d50f580e22501c054100f800c40140201002d080243c00011a452440001c006a03a2404070342c180f03050500c0500f008580000c140c500d200d01c84040340c0d84460023100c0218243c02400d054004100c0e49100b5140650964038101d42014100401500c0c2e132449482e003003603011160700007580180d64070040c81e00011f000ea400307441c001d03165106162508910301c486510500d802e600500283d40701005640c0042c8091a001401240801e290780040c89011003098202101203404283c2e02e401d43c01007141f151143d40200060319000c902406052403c2c02251040d92082004101503403190b0080c01e000c40000000503c1c160195000c03a86000300e20 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 466985224 1250 466983974 466983989
    0x180f070f021c0903060b0409050c040b1f050301030b070c0c1a1c0b0a080613110a091a0906040b010801032402120711070312051308011a1005070803060d02061201 71
    0x2a00601c100034041c00b50741b540e40c100380c4d014880c1d01101c1da140d98031410300d40780c9203001d40c0c1c3c3c80c0c9120b4619614041744201c0540ca00d460a03804021203500280307680d10901064600101c844c0c08154158400d865048007641c20031482c5250740d0509c280b049540400ba10211820b04080c040d860710310b51036004040c5500f0604400080c402c0f0310006000c090f24099100f841c1a4010004000540b41400601c0d030301a5800398650443c24045400a198407107107400c902c1007285840c0c0c030900440e005140042d588007081368843c4603981c800041200341d410001400c0e000413000001013000402403c141d0221101d404440c59042c82a1031700c070030880e007040d01414500e080000501040b0f541090460400c5000302d0040e102c401d045441d4111a0ba100300140400c01100007800107902c1c00da100c0c104013a2507220002c0c0076481c10a00f03025036551031600036500c00d40c04a40c420104c18050030403a5440303a803226605065070394820811007101c282e41400c6e80c0105c400c020b03030012031340d85450280c0600a0b2 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 466986474 1250 466985224 466985237
    0x10c090306050a0605061905072f0d030f081b0d050a0b01030612150b060301031a0c04080d030f0b0607050d0912020a030f020f120309180f070f021c 65
    0x31400d051042c1c42d4098842c40b01140380480c04d1215440700c0c1e048034602004600c0c8080668005d2404456a108a1070094015000801040900b90322019034100e0300301005004084031f400001002a84007104800401281400306881d24481c0580d241c140d105086070500c00d94441e0703004298409501008038803018590311010007101c0d003070510a0000416007881e0402c0740b41c1c1480008004110402005030451004001d50070942d03007030350450301381100040c002075241d51352440c10301009194000e00006140b10f0704000b0326042c20394820354084803d682e0003849181d803450000c0d4028003c00d040010603644a8917045000d803615002026402d01c541c004145440300b0b40f070300519514154011084c4024030a46141c05a0b1311200b4000c143c0340c00441d80c6070114a1480007503044d0761349502a58001041c0c04002c0b0241c1004006418083e105030b8240d01e050032001d00000080c0400c82c0e0f00c0d044c942d0941c010443e8140704803840340780b81000707004503621a1181189807408000302c1002e100020b24 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 466987724 1250 466986474 466986479
    0x3010803070303051003081c06120f03030b010e0609010c050a020a030803100f14331c02030103020307120512030f01060f0c050604061104030b090604050105090f0d050304080c010c09 80
    0xd02d88101640040b90035401c845c081d0956803078032294864040110088800c60034101130150050b07200f0401013a035062640071000940c85c040b070b2850380485043d40407901d480c2e401d80c030550040c0103840c0540c0004100501d040c818200555404013810300c269060300c1494280c03001600c1e40e0258202a60017030382200d1b1070b860700818081c5640095040b21002c01c4d180c400400410204c001d5524035000304680100000101403031440643c8501644208900288d100210258070103d0041c8641c4801405440c1d680d511480200181c0c4420f210094142e4040402007002111f02c81510075014403507030030f60b030a2144e0f20b441000650001c0e1194039000c000500100b000980020301c80c01c0b082c1c50350601244000c1c0c00e032603490715401e00800c0a8880c03500c07030162521070f030b03400012075000e158040c603054040d003421650256a07040807a001c4071517601c1e203008100004000620f0942200d20600200071051590000b03d81a8001030300c00c0303486420512001400100078000e9041c500821354403801d4592 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 466988974 1250 466987724 466987727
    0x4110c12070b13030804170d09210509090121080415020c04141501021608070e06090f1f12030809100509030d0207020d08040e0a062301180308030108030703 69
    0x200081d00c4152081103e058030400250002a6582e1040e0400c0c54481040c940d9200e511251081101058440d85000000402c100c6103601001c0c185210150b0081036003d00b00d000e494603c9000680d59101040b5001044440c401140b2071200c4090f601c16406012440d07900c070b00c15034021f40c000000c450b0401d600752401603410064001d03581000c032018440c440c4101c40b14030010002400d18810312a4034020892281d00810a9442800014840814107542c4002e81c1d501e0742264041c16100203240c030041040da01d09005040d020300321070400c0003030f5921001c140b000103d4031004e00d0001c045500000180808a0814050f00d02e8025240c1146600e04400c50508000c0c4410482c1e07030191612003801341028000003a06c00c1400d041a0050361203900d40005144100c40a00042c5034080021b400f00d007150080c4d080c43c4c05150b0303290043c890703161180c07801000d440883d640c02c105007004000080c01c0d988140e80d46020700040d442121076141d02c0781c032989103d520981001199134800100c400426 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 466990224 1250 466988974 466988993
    0x1e04050c090c040315020f0901080601090e0114090901110f030a0b0a03060e2a190b0a03020c0708071401030f1506030509070f0f06030e0f01051501030501090203100504110c1207 78
    0x10364035400304611304007c20f02010024007580c01040d04122180002405c107900a140c0c0c24003404074011808850345c1e4030000c0a64200744100030034040c0d00084007242000d107050051420300c001030104c103800c1c03a480050182d450303000105030310051501c902c043e01c0151a00cc10280145000394404107010003070340c50007490f100800350114209005040c10008c984040b4150401d004022a9040100035070214600c150303a442e90400485944000752145c0b5564155000340103000d4a23a09035440a503984c1040b9403581864454881e4586c10f441c441d2402c0e6120f640030104504020304005403403140c026241d0303030140441e000440800d0b60b40b0140041c13031508020080041800a4003000b0840c18200d11a00c0b1801034404c40023899214458860a08820701810300307409082c0000300002d2400018559100c070b807440360340340402c0c6490004201c0720103078000c42e44511814071044a0305440c3c4000e010061a02000c00031801d0800c0c444000703920300600c0b240700032611201e40d140d1a040d0364100316058 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 466991474 1250 466990224 466990253
    0x30e102a08040c030209090109060501080c0109060504060e0603060607050118030e030703080418021b0706091401020d0c0302071a0306090603031903180206190e03061e04050c090c0403 81
    0x10301c00d14404110004904404000580c3e5040c0c4904000381c40d0040031034054201014024401e600303050000c00c001c0c42c00502c2400600c0c09903103c2d141969281400d503020b02c60f40c09000001030340e050f54490141001001140c00c9580941140c1c43c11105885007401c44060740c0b11040da00300a20244818941d110a6640290f14214040e0850340d19656410507148124070615000269a05101050070f5942d03050f145e18181c4045580201c04e242d59000e5141c40300390140001040d1000f40102d0341c02c441c1d89010b404a08107170001e00304140c944009441c4837400110450451091a8021540d141c00c0c4549010344d840314511652641441030405c0100607004025902a40c401e01540305900303c10390300c40b01e06140f1414005000c0720400c080184200c110000650452000950007030040103402901005c0241540c420141d403a40c501059154807040c0c42030141070300d080d80f80c40204012142a140c126100c2c0045031031a9507004007041060504030307507618a003040032070f04206002e4403503500c100 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 466992724 1250 466991474 466991477
    0x3020303070306150c0308040f1a09100501060f0806030a05070f1409040f021212030c030a050702300d05040c08070812120c0c01050c0409061a0307030e102a 69
    0x21a0700424005d04c0210f0822002c0d003004503500102d01840350002d8410060f60704120074440101c01e46d149040050004e490310300d482d210b00000541d000c02580715081c1611480d82e0780200b1100c040d401269443d101905640d8140640e50710900064001c10400000340300000522140303030316004080c0107020b011421180a007104800700b00010b92124200e40c00720354112a02414945c0c00160285050a0000d103410f40c07410010600c602145080095071103801000d100744002da60700b000880e12210f001d11000d141141d551603804d030201c10b02202010048000114034104200f02c0e0056094520907501580d2010390140140002d05043c0002d1000d00400b1005202d413020345032b20781c2a1846184010365006022401044010030810121982e10620070000d02c403070b04040a00c00e00540c0148100c6c03a4540c0344c0480000d140c5a51034410313042da2028180207065a0341c0b07060540103000f018485542c10f001305d020880140c0c050f441100000003112002c0f07140c00c1c034070664200c0030a4030501400c0 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 466993974 1250 466992724 466992749
    0x60d05100f050904211202070302012007050c040c030b090c13060206010807030f030309080a030b0a060311070602030a27060b040203010506070f0512070f05060f04020117041e03020303070306 84
    0x1207224580c81c0170014a589812440081078280c0864602c2c85542e045005203000289003c14980c0c150805c00600c2c0c0d0780280210303e1031902e040c0303038040e20941d0b80003002c44e00580130350708a501d02680081c4807104035080100301107160a0014840000498190701c003640d000c00da8064884c140e5400c08041c10850005003170550410040669880c61071000602c40400b201d100000c06105c2d4104211291740301580f283c40300c114100c05000b130700c43d440b1014040c211910340010b10720301c2401021410200d02d80702c01e01d0007105480d1100a54001040d1550301500e80b0341518090000c0c5c41c14a18044030100115445810f6140c404141c0740000e1880740310754010300c018000c1c3e03a920011900309a13030141901403d00360034905541401c52f80c0f0342c3d4100d00d00000c03481d8010b00c03004041c00700c81248510103555480c0d441002c403040c0c000054034064001034100b002e112030b424a008855401070701801c0c8860910b00080f500c0c0b407440b101311000f100140c101109201c519501030166074040c00c609481d0a = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 466995224 1250 466993974 466993981
    0x105010e0627040206191110020a1b050a02090c0d050105090403080604090303060b030a0c02151b0c122802060c0a050f210105011808030414060d05100f0509 69
    0x1200120308403490700c00b0030386001011500719a105802c403044200810f04494036075001c0400540421600317a0204054018640d0300c200107000f520803500c0e00645070300c031100c0c050340101100c40d100905d2101254944503d00750440036a84221425120700034250200340e4902c050040c5000342c0300c040c2d1050b4012001e003c1480b00282e0012140b0798007030f0741030368001a000d40e203050460240c030b4542d208800080c000018041e180f88681c20010900c03010346c00311a12001c0e90018040d006d602258003c007005c904c40004c1400010aa006003080c0d00520115946011841840301c1c00d07621491090071003905401c02c80440236261502103c6521190020f0303c6285000e05405542d840b51004103c04c200d03002400415100d0b40e601a00d00558071100c1d42d90070503090000c09040c144080c010203011520035041d242241e80007892020036142c54501450600d49000b8081284000e105207040d030003a024440340c4040856881082c0c8910488070881c00c0382464240d10b10b030b900066402c0180640e0301c80d003c2 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 466996474 1250 466995224 466995259
    0x40806010b03041709011205040510060b040503160f0302060a090f060903140a0b070e01090314070611031e18040203100501030515032d10020c071d0601140d0c020105010e06 76
    0x90803010200c1f03690115981c2c0e03542c6042c2d070808414803840c0c013178189800d0700071030400c240402400c16124150122000c2d148492011031004149118080d000324030700d2810300050810001071710314100a4140b408500c1d0711800b164001c00000d8002200051a2100c1081405041160050914900400381030f045c1c5554031004441c0764000c2020042c0000540d1056a50b4411100000116088696015040249640c41b40c459605100f0301000402c035203400381c0b81c07080200c220f480f041400700d01c0c0079807c030302142c0c0710199411081c00075140d000d842c0511003003600c0e20300045128240504900384010300b0900054100c1d24094039690000c5259880409580c40c001a030302400b02c40101c212102d5040c810025500070200403c0d419240102400400341c94125005880602c0c0d0304402d6885084e1a1401c0303c10b10016150705200c14600000818203550041c00350f50b041e01c1c1e65108851412200c0d0790341c403040d103402d2a078001c0180e5603040104510702846843c245c002000b02c2d202c07890009540b16 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 466997724 1250 466996474 466996487
    0x3061706060436110301020a031a0f030a0b071205070507020a092009030f1606020d080c04140109080f160905060d0b0c132c09100b06040806010b0304170901 69
    0x4410183d140342c602000c180400e0459080a503403005000b0f65075003c58840c010054682900c100740c10800501901c0d05600e004a04c20582480150080131441c00d1038035802105c8401803e00c000340003c034035020000403018019503200c1c0300d464a445645883c41c0c410300c080301c1c007039034001c0074010302d401014070000407130002111441c441020059111101200003a00708420104040158841d00031060400400301940744102c845076001d40e40000b21b0b9500c1520b000508488441e800c2c881004180043c1030403100000b0082e0f010300d441c000c21500d4003412440d2400e190403582607644400900ca40c002e654107004d00147c803d4060522260030090041001070003105001483c10a40c031001900d188a1001920021541c0c60b04907020942d40f1300c81156200e00103400b0640c110340e40c4045081c040d803103d0b1041d02440080c03000300003401c40c520011004240d01d910495100c501003100099005081041c1030180010355800ca41d6814070f45480d18043c0340801900020b500c1c20f0003183d00e560380008 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 466998974 1250 466997724 466997801
    0x120714030a0b01110601120c090c0e090406090209010e0115050f070311100501120c06020a021305060d0f0c090b01182615010302030d05090f060901030617060604 71
    0x1e00100721107454a0060301c11056006680d5818803ca00000401070300c10043d040c1c0c840d000c0c1c0b0309801034680f900101c80513036000c40040c0c80892100d0f03481c210642450f1141c1944180500c4d00051a4a0554000380241c2d07401ea2004021000c2c0400600080640c2200c002d080581070800500e00041494011110700401c1030140034044000329004100d20140041c0311484050344c0101701c2e6603110300303500c030f8194061315094691030060000428001d00005000280c07a80051502002100c00e07400c200203490028640d941024491040d18005801c3d280000c2e0308600ca42c071148000fa0800d8002d804a80030006a1070401414250301906003481402c071105441c0e01180080d400c0f800d448008107000b1440000302650722810004039440225144041d040c0c1e0320803401d448150640c0b11088910740944051b4a611245000c903020151070820003c054500c2d040c140403400725a1800f40c18107003042c040410466801c544100800c0f232070544558001c0703401d1500480403420b44000504405450708 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 467000224 1250 466998974 466998991
    0xf030e0f0a0210021501030303150605090d171b01050a1812180308040909030207050114040902090f0409030c1401060303090e040c0b03010f0e0907031a0c04030501050c12071403 78
    0x406000300c00780c03085c012607a542e44100703041502541d49250050092400c40c00c4100030b6000f0520100720540314100b29220707053300601188012019849400000303034410814804607408205240000400d050781c6400301e500c2c8000001e0034a032520081043c0e80c01007452400c0c6c070900701c00001c0000d5660001c0f01d1714802c5031920308104407034141071021400c01500050004080070900103080a256004400d850344203900707032031100340c0d500010346601c103040c5100d62192906100030302000310a41e000d0310040100400c001c80b2040780001080490300c16000540005450190420520220f00c00410614a00000130012140b454800404003012400303903104002003480860180a1100e00044c080c1075545038480d030300c1d651212115460203941c170986d010040e1440c0000c400003408207240d001c0700c2c0c004039844041d40d2500c007660700f444001400d4400000041c08048003054091003401d02c1503042000140d6036280d400c0d1030400c45280100040204540800303000070010300d01c400e898204048 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 467001474 1250 467000224 467000239
    0xa0b1806010518040b0912040b0a0f030507050a051602090c270306041101050d051005040c02030403080301030206030402060c01110d050603032a01061d0124170408190f030e0f0a02 79
    0x4004010742040f081000401111f07001050128840011710000c05482c451600e0b0b0b011401002da2003541569400c9441d64041041030001c26411401750005100303900c2c1042086550208a90009404000a41c0d54510440340401d07442801d41c5180302e00c02d1a950000d0b802c00c900f04800d00040e60320080104000d03e02032140e40e46c64041d0340510203036101c2c4603a2103400c1c4218a421901c002d03070a2418441c4500c41ca0078420380308105030000c011101940d0b00410039900d580e083d5000d0115030380c4054801ca0300005c0c20032010341a40c41c09e10884441c840c050404560b1550300c0100743e42507441c00390035944690010001d140040d031180348600f0454117141d10941e040103902d0101801018664006d070040181d0b2118120b13091070004406040e0f4940010701c802c0c03503414000c0c00c1c08400d6005900b02c08144d4507442c3e41100700d09400b29030b80c0300d4485c9207001d01e4403103c0820300404040781902400451a0100200d00d22505401144024118140140520500d403045990f03500c84e03481002c4d0013200c8 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 467002724 1250 467001474 467001481
    0x40e0307081926040b010609030c1707170a06150506091e0607141504030503010e061f120506040531050105040b011e0b19020a0b1806010518040b 64
    0x10344400280203404108840f50341c186004002e04016049408456000c052000803a00b10700801040c000d0369009010712210070f0802c01041c9a070fa50400030b514480c49403204c000381d54020901d403850903020030400343c0b10b403c13a14944201610f513008080020412120030600250311558107940110100326284003408280c800d101243d914480d6900781c11035030019010003070041c065140c400080d1030400305c0315411149100c1400300740c000e132402000903408000400002c03030a50080d60300284000c2c04842031896500e11000c0000707280c0030b5400459150320b000360003038940b0b105240e40b20b18150380a001e43d10384105140b14650540c0300400401804031100d07241c081c4041d41605178141d11000800403400c081c00c1114800784244100c919241c0342e51001c18004000750345d00000ca6400c8020341d03041400c01e048203c00b50344202c141d001140700e0215000040f5448241e014040c00700308c0e00000703210b21381c0f1051030706000058004c24010b041194100039180c011203501c603402500031441021545 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 467003974 1250 467002724 467002727
    0x20306100e01090321020f0a1e030504080123070f0e0616020d03022b0c02010e031c0306060906080118020903031b030909060102010e0c01110c0d050102040302040e03070819 76
    0x803400c0c2c00145c80800d41c40c481e400c040004059031020b0b500c0d6502200d400301040007003c2ea8480741040c0c002c2c00441e0302c00f0458030342612186c103c06900e04c00c0c10300c2c0e400c1c1a12940203508407480104001c0f4910392440c014180da501c0307844101c0d045142858540c44606000c01c010389460424108907000d81ca00207074285007542c125648442072a4021300700b40601307016060003035545079001241207100c403010681500d84528090300c0c070800321140c1c60b0584001200d40065403080d00d400c2e5015054010641d0012250340c124019024004458900149003424860000c00c419002d800c80d00900040c40c006000440b0002c8001a480c0d40d03807200075030b80d00e2010b4007080c190b024081501c0c0c8210070540c0d0010107a80044050491a44103480c1007500f0380c2c0303460049080e60116030040403103800011040b200b80d4450300c0e14035076821065084508040c0cc2a011415a038000f00059419075404a001d00c114607141c0522010010204005c6041c08031944a6451600c00d0900407001c00f4002c5804a44c0e03035 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 467005224 1250 467003974 467003987
    0xc0c070302031f05010f1d27061501050406052a0706020102120f01050d02150405031207060507081605160f0305090a051c0602180603160305010603020306100e01 71
    0x4690103000d40f00c0580340c040344000d4200032100c0701031031a0700748400801c59441210084003221286510040ba50180c8150130310a4640070b4244111030b100d4031403612074071009100d5100d0b01142d00d07008140c14646034410049600c14021110f0401008110030420b0547c40003ea690b08440e00e0600b1411140941c21551903c01c1d240010000d8080c0d4480001d600d501940501402a1030800c5409195a01215603041c80004d00540e075004114041000140c180040041000850007280a14007500d84001910342641103c50030400000001c0c81d00c2004641c0c09103036000320213810099414248507084201103840300e1010803c2000101310100300003c81d90000a685d50480341225404405040042c001e510616409000d0b444da402d0000e800e080c1441080d07008222100384014414103603480c00040c1d4000029907a681c441c4941401c01c2e965024000d50144100300049801c000710242c014098810581c00740c0c09141c41882004210703120380000441606007442d00740c03040000c600041c0c46030f = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 467006474 1250 467005224 467005229
    0x527030712051b011e1e020c010e16080d0c0507150306030614090c011805040c0f110c0303030c2203080c010b0a0b0d1d0a0807120f02060c0c07 63
    0x301d07008021088000c0380c0001c010f15900410902900c0c612441040440c20f98503610400b00c6440c409040b001d1012034180d201c80d0050b44103024040d42128180125000d80e00f0000801000703075564400c04d0103444c1d042060080c02d09488520075030280c9005016901c81503148001028020303002640403c12200f03200ba0406008a41e0556805040e00c610090090003e800112000352030641200d0407540343c00d04441c40f40094400400a5074040c03401100d5100144a0404560003a14408209955075024001c40700400da0f03605a0f801d1100900108041c070051402c2c0f440750403803015081d45450100c00c8a50089402c100d05a840c011190811440c413185800350407040190180401000040342c024010201c40b50001c1c407440308600c0c20004403828502c2803490040041155140c00c0c4030720340201c09101c400c5c5070300740501504540d10740d0600d000400211880c80d400035481c1d0800c001e20031061400c032418a041094546c030240045c2d51003001030101c8003160000b0071000085d240c01c1007c0c0c7d02 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 467007724 1250 467006474 467006483
    0x6070b0405010522170f120a05060f06040f030210110d0c0c0b0405011b020d050604030905030714010c1515060203130503010c02030d020c0312010e0601030e0105270307 74
    0x2514007810814024203099130050382c000d100c400941000b0760854001c11409411036003a04104600354512840c581c040a0318601000d000e001d040c8101c50200402e522500100d0004110f0b0f20b406810030200e4600303501c0842c4075990a200a0040c22149031404081d02d0b419589030442d90721641d81a54540d0790a030603000315100c1c4601d203030704203903100d500304181c03501c0b44440a00d282d45414a441c207600803401094002a0f41300304030b45040e13a4269000894a001600c408161402a01d035581008011101038010030380c01042040181820420030008210044100c0e0b2103242020008002c507020f000301424100b0070380001c0c081c1c0c039160350146c0780c03d000064071404050741e04c0601a40f203411004090032041000764000401303007418000c0064842d8503a01031490a109101a000250804030505c4146e11040c030007115820050000240a845041e030364045c13f1a24400050a442c01d840800640ea41010b0620046100d9091031703030001147c2c60146008801c14040c8103155002d46840501b = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 467008974 1250 467007724 467007743
    0x2130905030a18060e150417031e040e070c05101e0501090e0601032307091a0a0605090d0203010209030a030804020111060f010303030506120f012c06150607 69
    0x40100000c0200090300098039641c1d1183c0f0101101d182d00c0c00c1e2031054101280311080510101e241c4025281401100c40340c0103403d15445181700008101141a41082540b000400301c1280c40c0800780c1c00ca041b101b00304818030f0981800500001d8120280c040c0c2c0034000129910750402c0130074488507240132103900003009001c0c496200b02031841c41d910109a0450314020001c1000c1d00c7c9405080c2d0350344010b1000704910307480c0d17079903204450340c0382803d8000c40c09400f044044581006c0c0453380080480c0c860202d0b00071003241d0344e121080c00c900f450394407500c2c241c801080741e9504032084c0ca0b4460000c5402205003801d42c00481d000e48548401140d05004080391a010181c0100c0d0302c9026034000c0c0d13030301071074441d11070b002680d2214152504d062141c004401000004e00c00d400c029032019005d42445407019440102c140f0349400000c40000307031f035110800d034940000c00c0c400e0107455046034140c15510104c40d916072611514084c0c00080c0b00c018100c15906140c9460040300d02641d070180d10380 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 467010224 1250 467008974 467008991
    0x1718090f060f0415061103041505040f140307060e06040e27061909060905030c0609010c0e0a030204020304050703080415140a0203090f010e0d05063705040213 70
    0x31003a00084540c1440381400700150011420300c1d114807000d00c10720b800b1401a0508164003502c282c0e0008480c04500e00c020040890000044054801043c11984030b85845906060454001d2a02c036048261a2080d0720010b405e1590300141a40803142c203414141515040c440200c1c09034071454003c0e035014440c3c201031001c5000e07107401d50043e1104118141e0500507400f031802c0c1d15410f050345c1d51229001c200d42c1510082c88035600001c50300f4800c00000690103070304c1c0e55180c00c64200c080700d40b08603040402004000b0400303000d2000c20703055070314003555015a91000601900880d010180c00740e0f50100c0020100a000c01c2102d001c0c680241c80b00d40c0b102e60758260503840c400304c0120b040005201003d0010003c00c080103560460340c1c10340180d400e001001c0d081c0b200840c0d40440705810400e405200d440c071501d503403d11801d141c2c0980090b1250f403078100b0503c60424040070301c0710200d004a40d5000811004081000f140d48807648000c00c0710b45a9000140c0414040001400118682090f9 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 467011474 1250 467010224 467010241
    0xb270f03130501030b060f09061207030c020601090e03160501020c070f15050a1b0203010b19051207030302070b0f0c0d0e0405131707020102011b02010903090e04171809 74
    0x41c000748440315400c1d64a0945800044040d50140c400141d0011014030120a12500f41009001c0e0b81802501d81410107051010420b41403200f81da00c4404695940405c202480d07040c0070715400f4154294041c411103503214150b564034031581c0001d180f00c2000c0c1d0050020000203404658003544c0010849400a072101c0104200394403601c21500d540000001c415007850180341030f614030005039142c0110000f01c01400c0d0f41c280b402d102007242d2555807941e05480c942d42e0800ca50035a981c1c0050305010701802c1c0000e000b0340e1781f8469000c1c8442c1e848500c1c10000658002181070035034102814080e2214076550031b032501d82c0140d008415003030281e8506e034244280d00c01600501c05104542c10b20003511400129650401e081c4030161042d1540f07071204820300207500003090402c0c17040c4000103414000c1c058144140f221082c07100b0040c4d44400d0b0b02c42c20b041d4007180d0f1401410b404030300b200140c01d165544000c0d01c26800701c03241107d18007050f03800522449000114a062016269240c1c41c07401c00038 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 467012724 1250 467011474 467011477
    0x606020d080907050901051c05010c11010c020102030603060a09050a0f051b0907020c1509090a02030f0702030c0601030f110910081009152f0c01050c070b270f03 71
    0x5640000e501c110001d41c01040016011040314400742c60450b05034240310a0018901c034a034901c1c00305480c1c1107142d0002660911640e1822001c0e5a84c4ca865601049841c90039141d03400348a50840e801481417101c969400700d1019000b641f41d000010b0360355003900e080e90400110040103480041a0504103080c0600440c139174420890443c2c03203a844541010800409030340680316900141d018202d06005030801c11000c0b031402094801041c1000703500340000b41e03505004c07205010025000310a100740000080344072600091240082c40c14100b010100702e980c0d041c1480054070380443c404010341030040d0340d191764440c41c4014040015070714041000f9031841c1c0151040f010315104826a00b1049d040502c5080203855100700c482c05030552902085001c1c102c030b000c900c0940c1c1340c03816001c8003520021001c0140000c04241554961012204e550308540000b003088042902c04c012803000a17808004150b40001d40012003445250008c0042d203440f14040400e11803881101907401c4031000000 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 467013974 1250 467012724 467012743
    0x1d100b0c0c0306070f270f030c03050d0801030305031302060d11070506061c03140d0216051014060103051509070e0a1508010509041406070909050901050403090b0c010f060602 77
    0x20708454203525031340c1e0102c501c1c6810031814000504480c2c030385500d01140d00041c58144d11002c1c10000c12544604405440d2840c80e4011034032200881410030403c1000c1c042800c2c0031400e800d090390700e0340c5192405001440000c0021a15a0624242004540e140d009550072850503410030001e18922015a20b61035200d4641a110340c82040002082889d10390500d040340c09e1150a06c0d0802001658146c0e41c0c07602c50f103913140f4009002e000500410a861000d0f095014401c844454050054180743c0d0a152800c2841000141080070881c0d1950101e04002d4005100b8a00061203903959400c604404c01c49441180d485030450040c0b11035198410703801d407981c013000c4401084481da640d4406030100f59801800000c10100401000545840d140440c0c1c040d01960603003100c0142c1240e010700b0034104071111004182d5419060204004a104850340284100d000304001c0c102510058038484061103407080c01480000c01c040311280a4100285c2038500c1981072100685411020751039010300c9 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 467015224 1250 467013974 467013979
    0xc0321050f01080f010e030f071406040f1202030a05070b0c070c0f1404051501230304082511040c180906030506060306070e06070221010608010608071d100b0c0c 71
    0xc250080740402c0603c18091b1041d2900000c62070111008128201c40d0015a03090340e13843c84146024003c20400c0c45060f00c00c0340328140e5158444542d01c2c003280c220050495450842d0710034000d01441a03042800c5035201387d0040e441003034079071700c41010352003503c0b4041c801081101106ca0020b450651501d154042d05e10400d44200da0702c19400070710049640441d0315030641c413010801088194050395610b940d89512011020211104400c13030100e541c0300b65801ca03070001002803480724140c2d00101c240c41c0e44221140d18a451204c81d220304e1002e013180f5500c0c51159a5032054152144c0c041c0c0d035036601c0b0192011844820b0ba643d1510034004103070038441a1043c0c0100c400003000d80c80c000c14003600c1880c85454000c20145990103000c2c241d00200c904a8010054007141c01451141700242c0c0684080e600000c9000c0c2d00307082074a400c5d81c9280d4080d0003142d10180003809003881c1c940c8284003c1c0f590080b4400346950b00c6a442082802585c0b11041110707000600c07900d110b4000c02c1502c0002070a = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 467016474 1250 467015224 467015233
    0xd140703180803061c0f0c0b07031d040b0a090905010b0402130902071a090604030210021c022a03031f1511150c0d06080304060c0321050f0108 63
    0xa050095040d20700c061507040c40300554001034800160310001440d00403c0150401c1502c20b11284030391400c00030300d401610502141c9140500b0440c02c40e007444080c0c68a560b50300d080000301c1d5800350125070700c4403482c0d151349600d62215aa0b13403510752084901e988000d10444202e503884403c2001082c1d82c0700c05070b61035402c041503111541804e000f210749031070104440000051800c03440e00025000840704a4174014190f40200e2182811030009000d5903c0303c01900e15801e0620f0041d18100d0310040401c409401484a0850031620501c5440d041c00120340143c2d84041100300300400d030f80a401c107044450075814440c840364600101440c401e4010744500c004104030b402c1450700f1203000b841aa842d6034030002294200074403d0301180c084128076401c8541a400b001d04180c5881c904560306015107201141d01000041240240070042030020051352500e400c1a6000b4018001d840c0d0107005c0c014040300f07001c8032503204a1284d4064030850780400c150b007007081c02000741020a1081514500c85d = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 467017724 1250 467016474 467016481
    0xd090b0a020f04031506120804060305070206070917030c16150513090f0f0903020c010f030b030a1101140c0d0f030b0a030b060406330c0f0201031a060d14 68
    0x68800ca0382e402d01e0b030305003940c00c041c5180e0360b038620741c4486480e00894903203803a00003400030854041c2500b414031500f259925103041c0100141210801048941194800424001020b42140c040c0d8280e0301d00718640048200c410525601e0b5103d01034504080d4420141304c002008004521902a250342c800c0e6601f5440c2e002804072158055940740c0b495910440504006e0000280d00140c18000f13a100042840301d00148640101d40d218082640560064290702d8415a8072000e006800225400d04120703e550100201e42d4901d449040100400344002c00c0c110240e0080015418801151100503540d0720003108058481c50140980c0300403452031386022640b84e00a000311401e201000d030070140d003a8a1500d0303a000080307018141c203030060381c0d651022a809c4a030f500d11021402d55106042550300140c1ca444035203002e4000c007002002400440303800051407030840c3e182c02d40c1d024a408209a040c00c1d50407005c2400310080ca65016000160f640c2020b803160b04080040c41161901040f20368 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 467018974 1250 467017724 467017741
    0x3100617030f0a0f0c0807050606240301030210020109052b050f031506210402091e0c0c010f05180d110c06070501020c030f0d050106090317030a110d090b 68
    0x607803420460502c034184404040c2d50710842d031010780710b505468083c1c40c0f081c558031480041d502c121020b80d001d07042001086410308044038010002e84014a1030105182180c220110600040c00000e1107035080300b800400c0c0f00d200b50401a0343c80d03040010b4404887d6508941e88030741038850f038a07a0703102184810881c0940e01680603120100044003505107103603140c9030031080d1020b042110355032284003800b5170300c25941901c8141c400425100030303c85040c10503004120a504000f051005220807074a120045032851444954024411810b0942c940c42c42c4090702e400740980300c511000d5180303843c00700100405203141c11590014801d094078800705c00703040d0032a41041001041101c551001c1c0c806205410003030018003545010300b00041c140114912044d0455000e0886035120041c003081c0401000d11030f1003098010400c41c00d003102d40c41d00c0c3d56150346d02451407901a505941001c800584121302c60340000c88112030080c04a039403040350000003002480484e40a8840005110000307442c074 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 467020224 1250 467018974 467018977
    0x180402190e22060501021c0203040b03040f020310091217060f0105040801020f070314120a0504051c05250206030610020f0105010311090f0714090f0310061703 70
    0x44112810601a8186500c16039070444280701860300031051041d01412900303070041d40b00c2003980e915408200c56241a000926110394900301c2054040401414001e641e00017084030101d800f401c1c1c07402c5e100d98a500b854840c000340000080d415008001d000384000c000344d800100640d00c184400b0f04490b41d140002c40ea2107494000380ca01c03010340350001c91441c1c83c05400c10814010149840d07890151610403050a82e004030b41185200c84000c1409030815400207002c04e03503440c0401d16a420070740c0d0038020071507010700908510b88a0ba5904040383c1400028032205071034441c8017940601d180044000205180d10024410f10035040ca00d995120720180300c424103107042d400514a60940d212002000082d210300d1a0709002d61141151078179821400380030303d034001e42c040c015100a44200e502030001296005003502a207400c00740030801302680240306910051404c4070810307142e42178500030840c82d090104010b5850701c681c10449102c00320303c0d0032a100b942c403910707000940300c011701c101c02d84c1d02e = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 467021474 1250 467020224 467020237
    0x507021002281803060e010e100c0e060a05030c03060a03020d050601060305060a080726060403050a0f030528021303140f011803050c1203040326090d0311041a180402 73
    0xf660180c003010000f042d00fa401c021114a04c2e0000081c00307444402a031803602d00401c200114843d111070322001c0f01a000035075180da180d801c2d0388051801090f0700c0020481c3c44014207020850070003101081c015110604450003640e8050101c1d01c403c0014101a0340e2140e0034400c500c0003a04100025120341481e0100c030080b03e10840041c000c030342c2840507a41c140b2000e00810550180060000d810000302001000d00590107038544650301e0b460404010b1214104032642001c0c0750501c01407020030649030741a00c0d46210210700390a110f41c14140c0d0600a845800024032000200c0340011060050070700002e80450068421a0802602d08205500b40c848511907201d280803003440c0d2401080c0144002c00d1281560b0080ea02072101f0700702c0c8004160019501900050000c1410003070001820a00400c04060210616074610304100401ea07520381400342d50080540301c035030241800e4050f60685010b80912940e00a112040d402ca146003508a004402c5050326008080d28580c1414400c5804 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 467022724 1250 467021474 467021507
    0x10203090114070506070f0807030501050906090a06031209080708010501050f0d0503040b0703031b0816050d110408010912030b010c0210020f011b0f0503010513050702100228 77
    0x8000c0c0140064503540b00004001c491070340b0800c0320000007841448880c0c1b00e12095110100b1001000000629410004101006140c80c100041c0020f40e11460030395409203048408541e940c0c0c540301c0742310250100380d0000300950715400e90011001c3c1c01200c410180e840c48411614000c1ea581e003501e00f600c1003031041c0c41c1c01007094000700d4440e08210804403032090080044034075042c3c1c0c40300c1301e130300503030000d681900007d03a030b800e2004036400e04903402410300043d85000c29490030403a858494210903418404240b11002421416940c80c54201c400c00b0000d1500d000e4560b03903078842c4203000c0c1031115400c41c0d19001001c4680300b010b00030b01c5211600c90060f5140c1c40030884540c244800c4038a2912113905501c2020305001c16100f0034096403810401070624560f4036103d0880c0900510400801501404424401485a9110025040b03490405450003050b152500c940c244e007402c0c40d50105601d601c1c00020140306401c14a0500440d94078503840b06500f050404bc411540c051b6491032804 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 467023974 1250 467022724 467022727
    0x905180c030f100f030305090a090c0905040c0309060501170d110615010905220b0102210a09030b0a1b050307050a080907090617010b040b010215150a030b10090605010203 75
    0x28002c01c2d2054507968080180200401015160b141c0b41841d64410340c4100e001400000d002591030820180340070080030299418403000f202c01c800506801c1c4a03000c2d450003a41d490310b029001c94403d412250105030020420013240d611548003515403003024401d1421441540f509007a4188106c021136480c620800246c1180e8450790142414102d01050b0710381001018000844da0b40d03501e220340c40522101101e5045804688801075003541c05c2884103c0c10740d040240300f00e40320214150b040a0400e0381d460701580e03510440c00141e4414039903802c00b900f40d201c7c6c1d0781040310a190035401540c07022041e1240e01c4050015400440e02440300720380040c0000d1050105618040c02810f246400508442c00d6030000c0f51140031001c100e805960000c8000c004411003001d045d4401c1c0700b0307010b080d501524240048a60000040d6807000a0802e03a0070607803030840000c02d035040c260600d171030700b100c02040c2a800c6681d81c101040004021f031001607034050304600000300e583d0382d485008201d80068001e076 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 467025224 1250 467023974 467023981
    0x1511030105100e033309012c0d1b12200d0c06020a11030a090f12030e0d0309080a0c080d0c0308150609181b070206030604020a050d06060905180c03 65
    0x41d1035402d41000003103c1760b4401c4421040340790035491034a00c07601c03024000181000c0c0c5580510390200540301800f900e02c151480142d01d075140841c0c401150f00003820110966054100d005200d070038452000341000070102c0c4c0358040365920100002c803108040c480800014040e84140e03848910051020300803a004600c0500000c840f500034101710f5051b82002114160b441c0381c1b29080d5400703030b40868005060940e090002558044501c1d001c1c100c1e101c500c94401600e507501a011111980304148035a5900c001300040500c40c2d20b404015040380829245041a545480380076442d0a0113404c015000382080341c0f0000344102c507003c0c4140d0300755480b10440d40b55040d81c0ba505503031070041035030805001c2142c08100e4945071f441c00100080d001d1b15183c1450011600100c0441d0341d007000c0111346041000c00b000d80c2d290030551b500550300700c0300107031b4420711182c2c00e5440d4845d40c0f604040031410700c0000145983c01a00f501c040f240c0c15a100003a05001c100c2029102070111010b00c0103034410f2010 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 467026474 1250 467025224 467025253
    0x609140609040903020f01060b04050a1706040303021606110706050f071e090e1f0602030705120307170a0914010b030303011406070203070305010e011d15041511030105100e03 77
    0x9410484c040d00544107404001c200c001e0948025420408103007a0004003000a81001c0d0f9660006140c40d110894203100400b0078641c403440050400b0b01010f4001c204c814040f010a0b0f40d8596180d0b000004001e400319410700d5010581028905a4100f417402000469101c21200030f0341c858059640c4407510180170304d000000c11240440100104030a041c1e010480000c100300d0030740207c411669003000511486e044c0101c0c031159800000854005014900001307030002191300c0040d0391040019140c0c4d840c01c2c0119112840c0140900c007001b0014140712903034107164800c0c101c2a015401c214941c0c820805202d003622120006c003601369200300010485000880c0d110004640000d00c2b5030700e002000e8002928140c00d130380042c2c03170b03d9540d05c0280100e0309003441542801003030b80000c9003d202c1c806c0e40e8141c075444034040401d0406849400182000600c03010320101c0e1090003070410081c6030705440d51070320340c00034003039140270389003486000d0b44041c0140d10901303040350014010400070f000e8101 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 467027724 1250 467026474 467026481
    0x905010f080a06080106030f0c0503010b06030f0702030909011202030705060319050603011404030f110a030f080901110412110409080913020f04270608031605030c0f0304060914060904 81
    0xb001041d5507030b03800201d641407083c040c050040d07000340351460302010301c4d0400051000050303001c18840c0e0b24200d568000d40e2500d50981c0e5000d0040720b2050303415901e83d9416815846039040c0ba0707600502207400418590302c40751168034030034000c0e011151119250b07002c2c0041d501c0190f40400d4850000d014060300300d0025000260f1001024001080160000740e007a56440d0301650214040740743d90f002840392503400250f440d100b040b840d00400c00000e040c0c074041d0a005444150004100c1d0038000138000c0704094215020b1f00c1d051001507903480e55544070b1803100c03036100c94003100e080031954000001850035004418003a500100c000c1c0c0307082e151038100100300188e0491011202c1d020700903000040c400b000680024512a0030013481002001150141603e11441d010131192078414240841c07030001090b42c031100b054800c007081812903828490301d1030264107021400f510401801c0b603440c00010020f0000c8441d540c0340da42041c0e4a501803414a000140302203500700b4014010703083d007458542c2 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 467028974 1250 467027724 467027731
    0x181209030304080303010609170c1507061e1a060301050a06051e04140f06271507060609051602030304030302130504090308150d0b0402090a02120108070609060905010f08 75
    0x101128580b56580b2541c600303541099010a02051070b00c0c0007045003042c1002449960480722004d032000010600011b502c03001c2c0c0c031605114810011403a070b001c0000c1940105402211003415601c540d40542c0e2002c050032998001c1007080c00d44c811043d00c1c1c2e00780384d001d40307058a0f402000369030100d0500340211501d030403203120000344a501603c0348103e94244c40062002e0607240d09a101e0105d1010107110034840c20340352042c0504402c0150100f0714018044c048140e814111000441055000001d40c10003015014013008403400120001005019401141114912601404aa5221600400030102e103a82c0407015070010000a40080d103e40e00074800d40c440005181c003166151004201103c0c0001e00c110b0209810006018900221681c44022003c080754540316082040e5140d20440b0009000203001e140b011004c08c5040d003003034040e1002c880e1700c885040260f60355601070f140e441d2aa84204e0000c1400c02d0b8010400f00e1081e01104180d42042e143d4055450010030100e4102c44000c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 467030224 1250 467028974 467028979
    0xb0f030a020909040302031e0301060c0209191e1107020a090e0313080a030215010b0904051b12010f061403010b03040f120513080d0804030f0e090f0103030206181209 73
    0x20890b24a032951016030305805540280d000316240d4010300d800724503401c9a5820110308040c1840100603007036111500c51942941a02c900300d00d80c0310589101d245905011021800505008800d00d9200e01035645060803079042c0e07401c0c025240d00f000910002e210300c15005c0d400c081c22080a110504113900300a0f0b01c0b00e659001c030b0b840c1c07040c550420318484070560800144d64020010580500d076041041444c122044500f5078869454651011001d1003412a0b8178060380d1120000b4080034140410800440c450f1074043c1e60b40d6565142e1075000e8003090158640100100d80003203900c520581499030504005100a0b20356420800984107c4d00014411103510510400d00c00018000c0080009804c080e915000d454081c40b4082c19101039503a0000c240e1b030380c0003051908070a0b5102808a03001901410000402000003c0495140c4050310485411000c203100303002001c078811a80c24100c82c0650300741c403459110f44140c2d401500c014032130031100c1d91010101e91000d08083c0000c1040320f100 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 467031474 1250 467030224 467030227
    0x303091905130903020c04060609180f02031005091806070813020a0602010605130e030a0305071704080a0f030b220915051f080604241b030e070b0f030a02 68
    0x16031000840c0b5030b00100a410b100d54603510180700305078040141c00c0d5039441c2240c0c240b000605004005048240511a258032140c0c42400b25031101d8842d4400c09200582c01010342d030f2460211300b6a00d00601e503205075801603044400081c101e41107214030407080100c0d20041c1c4450340f1417810407580210050b009500d10682d41f881c03a4016a1840d100350010081600046615807034801040041e0300040107a54110341000401120408007008942c440201401e002030075840d031100403a920b2991400303840581c550441400300740040403000c4c0c45072000d0ba50300d240184006900032070596002000003038206011564502220303140d40c1c03044110401c0140300140110541d11510400084041c40701c0e10700e0350f00c07028011084080c00c103c17a100140802c0001c1b0051074482119518640148050401c2e0441111440c100560101c115048034104009000c841c2036450388861950790752503281c4c042031034050a1041443d01003124000c850210400314141030310340e8003009a03584000c0046601c29070 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 467032724 1250 467031474 467031479
    0x10e0c04080d020d091413020c0a120806100c05030d05090f0a14190c060c02010212040b1b1b04020d090210020304090e011103040206071401050a0b13090203030919 72
    0x3080100303545a1150f000301003101940340061300c1070410340c201544407481141550b10f552101000c403d0000507503000181d0714001881d1450802940071802494209032804c002445680420002e003c0e0700111a445131034481c2c010203503108146001c0040982e0000d20207000c00360401d601060740000d004080c2c0d44a61400d100090801f0900402254a81d0b410301c0481100001000000b01e40959004102148400c940b910081000301b480f40303504114000702c2c20000c59200f448000d108000075071189455a840b00c6403800340307130440800341001c800070b1680b00c1e54080c40044c8521400c214081880c8000c032840b01404040d501100150003030503200c9180d0b50040c1c58240322514141343c650b000d1501d890a04040e48160b611b80f0b01036108582c1880480560f5020b00801c0700e8101c0d078111840c130340d9211a4036014228031511850841c00d94a801c04000c205800341c0c01030300c1d200604940f03070002a87c5c680203070300459402c200080c0d09940140300540c0c1c1410040011030106d4004100c200c41580d = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 467033974 1250 467032724 467032739
    0xa0b04021b070b0a02031902120301030c080d0c030f0e01180801090b070c12270602030301080c090f070309020d0b04060903120506221811090f010b03010e0c04 70
    0x780314042140c0e4038035800d81c01c8024240c00348000070203002d52403541e41c40c10300782c42c030300a50301c0c0108006068660000c4004030305040c0204001800d60310000c414a403203680d45d080002125004d80b00394003241c003590441e02c0f45d1314400e4010100701c942c1600e800d50045030036141100c2524101f200681400600c548010010024116400017003031000000b00f070074245460500005600540703e002072140d41000c10300040c501960011400c4a545028205030309400f11091030401c1810040c1028200c0e4a0081102e56020005505841000c0103ca8121002034144038102904503208080450040c012800d5588260407002c6064001440000006050f07120381003401015241116240e82e074082c80b2081642000c0c2000c941402440200071900c0c3c131402142c0d0444201c59a80e000b400b2600821300e41c1c12469102a01138118142c1d040c10b03044c410300c0d0501200d2a05004c29103e070500000040c4c4400b0351002c10b506035200d100740d10341541d190403072002c01000c020789013040e0300303505000101d50385 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 467035224 1250 467033974 467033977
    0x60316080c041e060e0a03080a08040618051e0f03030105130915020a2c040e010e070b030906010e0c04060e150a18140d08130302060304030c0b06030d09030b0a0b0402 73
    0x10710f0100030040100d18201c006001042c44c00c00060007012107820400200c1e07200e07030944403030f8542818840300780e03651441d09900611224204d0841040d00d402078a045c400d000842814506050842d40c04d24407100d03031410b68a1b08944c0d40e40085030300810050003581011404c18a810b12307100c3c00842c03032140c10340c1d03000c0b41050035050f406503071076011a44c1c025407940010042140c24228003a0802c1451180b1181c01d40c00c1c0c0040014001c6407100b44104103400254001e07542d5a201500780e80030262180c0d01c415080c2c1c4260381c4582144611400030843c1c4411840c560b001d01d0090b4400340c5800c1c60040300b603030042003007503030568050a80d0300c92440003070203071000345028505070340c80c0403540031402040d98521540382c01a42c0c0450a5403070840098881808a81003241c02a903000d40701c40b60200321181c4100e95800094200002209110802d50000d40c032036a91407080148294540d508014103a492600005d00000141e61440401c003040c040c10005030040005a40860f55040020204059 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 467036474 1250 467035224 467035259
    0xb030a030e061e0c010b0a1203051315120b030312070f0915050a030f090302030409020d0f0e030910170403111603110a050a0b0910020a051902040b060316080c04 71
    0x184000104134409010a208038002c115080700c0031007400f03003885d038011114440c0c14002418001e000400c4098101c002e00550000d2034001000c0b045141e900310300405490103405220f8400c1e0030410b10158a05e40841910048210f002c4684007a40d0b03044000c654800d188040e0109000b2400d4010800403400c681c4600d206c1c015485643d60f89218110040850b50b81040d5401c20500c7d0185880019034003100f100d08862584401680350800321000c1001840741800c81000682f40a0040181074008000b4000e1050300700d48696845030f160100307480040c0e110303880458101c201ca000400284c0294141c64410420f001285d9035450010304150090545800641d481c101e614031228040ca0b0410650014102c142c815100c82440c18200c980e40d400b40c24a40d81c42500e903402b13200003091007045076544840e0048100c4481540d40580c03948540041c2509a00842c02d0078408825402c01c070f81224011842040120898014040d00300c03403011015181c0d488036002040001810051308074070114 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 467037724 1250 467036474 467036527
    0x90f02101202210903070b0a0c030f050f07090503120a0503130209040b180f1207060905250617060d0201091a041e030309150c080705061005040b030a030e06 69
    0x40380f10022008001c04000a02040d05588100b0100000030884020076400c9002c8100205c1e05c901720001c1500a081d8200185003d50301c1c0c103040100e60600144150b0140103503868082059440390b0030325445000503402c03043e015104110308512641700f03000440e402802001a5240702d8030b260b000900040042e1415185001240c0c00e0049061329803684a20b800d40c1c0340d0041208007102038071241c841800b451407a00c030401c0810580300b8070a0350780208440c160f2080070f4641e81541118400c8007814601580d10b9002e000c0d080104646000e060305a003c2d41d1140342590083e41c03041c0c00c100c4400d9002508a040101c19000081c482c003484d00400080e4030407001258407103003002c07004840a00701e1003000e010f101170b1090410219400100410a60340f510341c0c0f6090105c00c2510030b82300c0303900004004009940024291040c01000703d0558001c0030424440584c96a40d08108001d9070004410294141c00c102c280ca0000380c021450049440e00240c221802c003190003061211140300281c0c0c691 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 467038974 1250 467037724 467037757
    0x90206071101080f13020d02060c010c020a11030102090105090607051609020d150311121516082a0a030b040207060203010806010f0e01061b020310020d0c03090f02101202 75
    0x81c1a90b030405030b030b181e12500424044209140c2418480c4180700e035018060b0089121543d8002035403220030440e07960807800c000906c41d100038540025074036a6440010f54591004600308141c1e441d06000b01c0c0c400c100165106824501c25000300a12a403000c00211000e11624811078003045d808006030300201a40c1c0c1d001602d446500d49004103550340e1440d041c011880c6c40c0070610000c2d08642c11540b03200e205580c10440e03515041020345ca060078407503900c00d203520408201304640e60b0748082e2a51800456968045540ba00005622042c0d1210b1040c968100c0c120072074070080ba00400604880d0311b0324500400c1d8441c506000c24100c0c2d1044cae2095445d1900000103000b090000c120a44c0149140400031841520304080c00b071300040103008000401240b01411461144c1ca51481040d0980080541d008078801e040d034100258000d040140c0301a04096409510b90b020f48510030940fa000117441c60241065820002c0c4c48000c82034003024010b0706030621791148914400f801007040744800b0003 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 467040224 1250 467038974 467039003
    0x106111f0515030109210504080f07030c0b0a0801061b0f2102030703050a0e010306030203100e010e03070201120902180a050403080f13060507021212061216120609020607 75
    0xa070719041e500028040d82c1001600e0300004d0400051b500d0b5052030841016034000328502c00c88403440741e40c1c4100310718130a04e207403032140c264089070000803640b1440c013814000d035580035060058002e00b409100810494001000f07494090506200001c101c031241308190001951410722104e2201c00603903059808030400140c140c1c54220610010403140002d500385010f82da0005c00c1d92140d0210351040040c42d580e80741c05640a074100300060b40c0d005003a1000b40ca4180318520003010490b4940d080d03582450b02c0c0345052080402241c5000c0d8040e500c42440441502580000e007078002c804a03005803440a140c10003611000c00075000340441c500103c0d40d4141400c00410280000d425004000d14042c00c1c0f2a100203a0202518216803001000c14581e0700c0103801d034241000b414211190520016202200c03d03041465140b007108111203440500342c4c00c0a02c10f036101100d000f104601d0423554418411680107880008000d4850345001c10070541a50104585400c0207408440c0c14201c0502e8 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 467041474 1250 467040224 467040241
    0xc0a06021b041e0e010c08061509221e0506060f03040c08060702030a0306051e0d050f030a0207060305010b2a03070204020706022709160201020705030316080f0903030106111f05 78
    0x28481b0110040c90604103034106000010300e040540b14404c0044000000d1440c0ca98491f00c0c0301500031110700c80648054440c40d8440d00c00741441464002c250544241e10051410f140c3c49910700521010b00702c9414001030103440c00c1d590740b016100355840b182c6400c00054111082000c80c2c4124041e6020f151a86d951641c0901074462a801561003604a4608108034048aa19031420040101c41130204140c507818181d083c641c4000c4440103a0000007200c0c2d03ca00e40008051040ba80c0704d0313404004070381c0d0f121712421040c00303804641001c0713040742102c2c648032500c49082824031100c004203480c5012820360004080b139001c0c440c01c461580d0042681c0b0304c1c1d4025003d00d041c0a026050141c201c50008100040caa0f210051021042815003041d0a044038401d40c140c40c0c08640c800c08490303417400d10485509240c02c060200900082c90071002486021000c2c880f04d0098045000550a590810781c003943c2580e12001c406d00c0d9845110030440140c40e1a01051042010110000805080c031415 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 467042724 1250 467041474 467041481
    0x110c0405070f17010506030402060708090a0905090d08010b090d0c0e090601090c0e030c15070b0109020309240411010507081308060109060501020c042a09080c0a06021b041e0e01 78
    0x3e6440c2c0d12542c2001081103480341421072340c0c0140d040301c1c413550342d04561a01c50464092604a0347d000103103c3d00c0810a005a0791105000320214000c6415803090500102c0b01f00c0001d000301e041d108014002c02030305e0f042ca100094102032250965004980d150303035121451b80d1084038501150740c490303401040040010710851100404a10300b0965058049022903900c2e030030322100c14060100e40b114008454815010b88148a41c07100a0701c0307607965105107280184d0010b544251440c05001e81511641c28190b8451044403d55135480c950b40e500d0ba1110301100030f0b44204241404020000b580c0003440c018001d00020365040d210042550800c582c1c1441e1400580007240d6252505900307000701c0c3e80024204001e1001210045030701300c440000c01e031b943e03945006002e00205514900b443e030160000c03541815541c4c1002101c0c1c0c094541c004106024526100e80009a004038035515070ba0003184c0300312410300c074000d00046030380b020800102038000300800059009984e20318060306807203c28007 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 467043974 1250 467042724 467042747
    0x120403151d1c0c08031603110a050c0d0201062706120609060606090b1c18120228030807030b060d1a0603090c0607050c1c060e1c110c0405070f 63
    0x340c2450000340c3d41d55000c0c0c50744030140000e0090b5070400d03900e21340d042c0b2a410000c00a2000b0102c16100e8140c648042c2c00b03900404030b14100d9004501c4000314075881442503104880780b00c9452984c0d00d0700c0b40c910321421208421507104041e142c00d404141d942d88440d4600c030b500d10651000514070142c1c01e00008481554008000304410210704101c1082c43d4016548040c0801c0700c0e4165945070300240030b0007000098002c2c11307154244000700d002d10242d421790600600458080c0d50030155001d031381d0484906042814495003040c941d1660210303114101207a8498024100050f0701020400003441c5078100c8a14640d00d140c179100c0d0a51440c0109054059004045d500310b0701b9404c181d040c1d02d8580040d031100d1342c0595008076020051060801c1541a052409050f0500d0075280c0251803681401c030301070075101135041c2482e90001d418001903008183e490940359200205500d1012240724100ba02d60340f0b00f900c281010020240e07030780c0c403c0d14007440c1c40342c90310460103c4815024100d1902d59 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 467045224 1250 467043974 467043977
    0x9120a1101020712080402102d09031401061a03241801031101090504020c030d15270606050901090501030f110f0c060c040e220602030a0b040e120403151d1c 69
    0x40c11218270900d6030000400021130714880150f06113001d40d13046408010b00d90005c4c05034005a100907058020650101d4151034443d2181c0750384440100683c1d445100641f0303110512900e01d040000d0352020108041e5428100400340400d44003164800e617107c00c000e0300705071031100155246001941c0c1000d50240100403c1e80c00398240241007140d26124003800341c07024040c54403000142104a8043c151101406100c1140c1d00c4c8940910100c0c0900100700040d1505c031850000301180c103074052003c0d9000408160359000d582401c0c8001180a40a0300601c4c1d0342c01920b035804a0007047c0e0039005000a040d0814031540c4400c290002640780440c09400604608400c200c18050740304204481980301100e8400742031020001460300341003e0f001d40c0080e1605201105101244a440d08101c80b080400c036824844010718401c0301d92140286148034044032000c100400000f80040759010000031018400507480754002903c0803514240e20721828660030101c01040003624400e0103640f003241c0c5 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 467046474 1250 467045224 467045237
    0x3031b0e0a060e090406090201030e150108070e0609241203070c0b04031e0516090e1015060806030109020d1a090109080f0310090e0a0b09120a110102071208040210 72
    0x80c0c0d00404c850010240001e40480c2c0c42c1c501d09810743e4001c0e001940394030407000881d8140c0510440086200d40f00380242c51103070040220000d110b180100c20503020703000081c001e81058a03039a010b81c4140c0c081407034070300c6c0c000080c00800da02591104460042140020b024581d105090324150a59114079045101c07143c00902086c00483c91450080c4020080c106503281061141c6c01c102d45440c0b07821201c402c01070b8003e00007245002081e0803010740e03040854101c80b00130300f018010800362044005020301007a80c1101c100242ca104883d6036401c020051300000380108d160700460206000701d0402e031440c00e100c0041d110030303020447d040d551148640000b00005142940c40c0c0d100c6105501102840120220101c0d40c1c80c81413240c41002428104d0041000c0c000e04089a0b8850001480039a1454074000016480d1040401c41c2a22412041c01e120b2500028410554032030030441c3c0207401030340d400e1040d400020302c1c4240607640c40102c0e40354150940741c248104681410346000c03004c1001130 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 467047724 1250 467046474 467046497
    0x3120a080a051512030d110403140d0e0d020a0515120c0f07080901031e0c18080604030503040f1209090f1b08091002030c030a05010614040506030403031b0e0a06 71
    0x40c0d00c070303159103c501254200c4404030715020080c075501410b000c28125501d8003003503541c1e00c02c00c0c01c020001c980c42150001d2a2046042c10079440c2c031190380d020408200c0b101000141490810718a56405200508000540391650f02140f01e450303051300311290640f00010f9042e65200c00d41c003540c1c0c0c01140310900e0307480d1104002c208501070250880041003c072011564070140c2e03009801824226444401d0001640b11003a00480600140c45992000c56410711207411469800071402054840c050000c1c201c1781c03078554040b1441d501c014002e684e980801711100001804c141030080c1640c0103030390b55030300e62810030b0802c40c202c422080003c0300311498a986186844000c05900c10054221300740300c01035036a4032108c05c0c240400413084010301d174400001c000301802c1e034901440c01208802401c020680c0c031014180d5800d4030b168168958840c09010401c424600b9100665026109240208200d020070005a0341e0103440701002c0c0101d0788012a10b00e072801d1000c0b000300140003500d0809500d04 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 467048974 1250 467047724 467047741
    0xc1f02070603050a090f0b0109060501090e061c0f05010b0a06080906060111160e0f09010504080d022101120213021306032004031505010605180f010e03120a080a05 72
    0x38040c030500c0203250b203a00c00204084402e902c18000160014800401103403a07150600f401c0c40240142c001d60307494600c01080a520803a031180542e80100340941c40707034488000b040f60001c4030314003099109808450000004540d00d650091040c4a000042001640041085030000141c0c01a0007000301481c1045200e250000d045074002e07100b82087c01450701600a0a4100143e08041091583c107202c1c0c005810480c10208900c200e030910895041922072500803801c0c0c0d401620098842181801042d180901c65070003407610715034005886d40e003640c1c0c03014501c14003803003680401801100c0181d40c50a600303185030014a0118581c2045150040c8462124a038110710b0040d20304141c0d45010358120420040d220405000e030084116890319564a002481180d40300070003155507081c04000150300e805042076034040d0302c008a20a600c861610180800081c0c07600545040208080300c024182c2c41c00c1c0542c886000d2550743c40740d507030600e0401c054517854000d441405c250b4034180800400f603 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 467050224 1250 467048974 467048983
    0x70503010522020102250905010f030f08031302101106150a0605130f150f020a150513060606260108030307260702010614242a0c1f02 59
    0xb00410200c0e04522516400100c1c540381c00030061180e03580e2250041c088601105e69141d085500b00f50703090002c0e07a203598002c50716803203d1000910005034211407800058030324002e90303440914160100c1c42508070b0340000d1094201143d40a01250300d801010740c1095083c001a40d0120f14034600c1d03507620005c0408204004000d11401c0200500810344400985c8030b641410000c005455060188984403480700b104141d50042c6071001c0ba08040c100120070b4004542c004120350001c0741c80d10394a10100e904006090020404403880e4190340c2000001200f07403281c8005096266107403089600013407245c0140d80000c00f00c82070703442d01c1e1900411050f200007080703a601038020715007015000a4016189403404e2804d0b000b101105469041000c103d80c154001c0007100c1c10060005100e0144034248050000c401c2111600141c1c04101559a07090f134034010010100d07402c11b00000c0c1c0b8a100c065841c240340d0074403218484d070000034202420b4a89082060798000d400320174510001007801b000fa669 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 467051474 1250 467050224 467050261
    0x90c18010e0118030525030308061003060e0f18070b0d2f0a0201050c09030a02010e0619030227060703030515090403030903030c110c013501080705030105 68
    0x4000d034007890680c0991080140002180441c1c04959041d500da1a01035100c4201400f48070341c040b100a002d10054940842d000100e070b170107445810140d2103050611140a1085442c0014076450701c81c00241d00d08001e28407481014a02a00c00090804a180389121009030035105130507408a1b000340650396268088408420318080d0004107100d540c400301c01164405d40c040f008440107100c0c84000d42003464003c2162801c140c0c000c016560303418005d80c0e400d00494600c01d8043d4000703c0100c005500911100d94207090082416042c006602032240c40b00041c800d06c20002600810f07548842070b1140100c1c40c4c000340103852152150340c024041080c034020a00702408150701c400103d400c2d00c11101e000d0000f02000740c000f0620f898039050240c09421040011000640381801e10004240301e81103850b80309c2c100d81c001c2d02c40d00d03068038011920700c0300c146510240001c00000045042c0c0001e16180c1c1842c405206294843d8035000711642481c0142d80b0590280c2d05081c00c01c0010001001c8600c0c0 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 467052724 1250 467051474 467051477
    0x20105011a040e06040f020c031908070f0e01020f0709020d0b10270503010501060e090f010305070b0a030b042a05030c030a0507030b09090105060a06260712060311090c1801 76
    0x3d036a240800039026041440714988102d01c0041e040d04046000710003408a0061546c0d141c054003400c1a040350441070880c1c0c8480041e60046080741507501c203c1c840d003c6803405204561100c5a044546410604558003c20080740d002840001001d01b87c0120461204122100880714540300e0000e42601000010403655403e2100c800d51100312080700e1002400029000304032540c0c441d10040c10400d07100007020b100c3d602400011703485002a00005068941c0900908080c924188803081c5079000000b1120501d40c03640c50540068a840c4150b08201c0460810301200c544000302e0100b0f43c03030150843c40100714041041003800c070003060440ba0011414500003455a0320f01c0380443c02011804d5049a000c004202032108800c415041503000d075808551000303a296817014282c44400d00191003c0c00d41d5002c0394488001c01d40040956401122802c245403444091540c910032954030390011116144000626200c90501101e002e0b444080300c14080d15052148040d0000b41b00700041b01070 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 467053974 1250 467052724 467052749
    0x40c0506210a02040321020a080d0e0a050c0405160905060d020f070c2111060903070b0a0207080c1c02040b012007091103060d06090c03080a0e01020105011a04 70
    0x5003800707080d8030740c0400248000320300c60542030080c5010041d44c0507101c00e60b028a090b00d20884020104020100c40c145281c0080c126001c3c80d540760112600081c03542c007070040e9918808164600700b40240d18050344608042c00140d080c07401000200c44010380f500868207000344443c06c03450f802c41c600000313032581100d20301d0706d5606021004004e88145444181c880b1004520300c403c200700c480b1550255441e0812140d88050340c0c2c42c010029510034074000d8040804140d0002c0d560401c0070050494003006825141010b41f07503a100821507000000500050340715003010042100140542000400121a2010200115295903141601044001e4881c581d18038410f180781e80544604481c40100b42251201450901d040790380f918410720550386558105480d60b0310a07000e41e01141d1140d18000c1c14080544c0081d159207004010b4000221100715040c0c41c0030000c950b221000d040e40d04442d40e0351002c1d003007160000900307440048e80052424070071000300028916001c0f0070b079000d0340d003280c070600c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 467055224 1250 467053974 467053987
    0x30b01080c16140d090509070c0206070203100221060406050901180b040501080109140102030105060318010905120a0f02060c04060509060d0c020d090f05060d0f0b0a1e080105040c0506 81
    0x1880c0710300460b90040020015001e26102c040d008568010b01c010262248120303d659181071005001040320040c00059484004070700500e48800a0081c8a00142c01c403504902c5025034041280c0c02803001c488691400b02041c201c5501c1d00745003603030102080d0750902540e890b1402103014030340180140000e00000e414082003440700d03a441400107160040040c091940e581d01581e000380807030201075541c640c98019245030b9070740500840b0704072070000c0c0806107556503040480302c0c06110b000d010900c954840c8220700129100308607a0310180812042c0340d5a81101000203881207929015030b01c190341200c0304000d0000c02c05400e40d81202da05041ca1983c4046010021b06031381700301d401c110300c0640b50040d0800c4080d8001a1860402125112001e0b0640c8500e07201c020103046105840c0d12640420060b04400d0300340d00405148120707000c02203041c400407000034030718406540118025400b5032002042d61800e405c0400010402e5000130012804c19031220b0407100058001c240c016403000480 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 467056474 1250 467055224 467055247
    0x1f050117040203031e0903160b04090b030f010222050405070804060e0c0303031e01050913150b0d050d0305070e061611060417060a0605031009080417060a0c030b01080c 74
    0x100ca220582c280b03085080c0a0110284805d5600088022070203441a80c14036107295022500000c240d81c1d515147c242000e14204440300076126013146150140a40610585210700074000384c90306002e07003401c050003440ea104404407064400d40c0b000d0302ca10700701414080b029401401c8507070000d401c0800802c400c0e40c1522074501d06030050140d40c2d058400007080101e07030301d05202071715003642030881d03982510b90b80c800411449182c10340322008d60030b03100503c020016503408050000306003d080046580e000a0000550710f0361540429281ca40025203441d400981c10710480b030340021b0b94141200c0c04001c000c007240c8240074040c0ca1012102420901da014002d241c076050500010044c200e80c1e640d034445144c00b004505401441c0000d200b40e00100c1c0a41016000e801c0540700041c0080546048429944024000e040004d890401e01040f01043c4030400f40651444090090010155070501c101c0c583c0071126252041030406240c0f9442a4042c0c1c0d000050315000034035540e4850700d0f545036961 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 467057724 1250 467056474 467056477
    0x615080a1107150c03140708150d0f03140a090e0a0209030a051c023d020f1c05060f0d084807151b0b1f05011704020303 53
    0x3400740c0d0108000c2414402c0004200007000d0940eaa14814419841402015400d0729000b82110325840178241c009801c207440b58035400c1c1d1020381c601c0c03080e84002c9280042035040700c01d401c1c2607900e000414052130500d904a0b4480c21000d6100b04081c1c0362582d90b140003407503030076a80610740740a410680402e008000c590142e408071280101542d0030100a490280d94454070002100c01d4901c258901c070300303c0350021a0040003d0340c807210100c0c0f200901d580040a0012980c0d0030182c030308111050000e2124244042d180d000c0b00300340030a0b6111000e03074104400d500307100c82500505082608100c401c0d00e509000c0035543c0f40c00d955482002c0304e58585080e15004010000188040071000e1000091101c4064005070f403182c481450103c0d4800306c254105200c80c0140d05e5540d015080070041181c6d52140318030900a1403420b01e1803803403045420000c90a0600064480d25001e00034001080c00400c000b03107031054180000c17140d103841c00e800a480e0801d80040c1800d0082848002000d6450510 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 467058974 1250 467057724 467057741
    0x1c0212060c04210501020a0302041d060102030d0c03090b010b031009110d0c05070f0507030303060501050304020904020f0604030c0f08060112030804030e01090308130e06010c050705060c1203010609180615080a 92
    0x255281c044600004009402c144070751742410700b1142f80440341c020806110341c0a08410b902031440d06007104401009445811100c00800d1b40d555448800724102194103400b070403403020344503602d0800d46003081c0e5010311074029080040c40c01e43d120203405010402c51303a8181880801058141c8a513409545c00e004072000600401e41c603103801c40c04c0100202d80f110030f0b284207817010002180c41c0c100440b00c60202702d80094200300e02034041009807070702c451003da05450040445160684966030303181600c426a03c040c00c020003c5d0780500c0107131405c1c00b045015084960140821840307a44008014040c040c0015090015058858a49134850340800001d5a0000b0340705039120074100c18002c20540c0b622400100400b00e1020404070b40c400e240d0b00d604142c000c0c0003000c41e00d00740340801c00316900800d0120400d01c111022080c1740308402001d03500806041d2075040c001031412585000a4000041d2a0440c41c07810030700307000490955200801b080d1052520006503611400e0b494001e0100300b = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 467060224 1250 467058974 467058983
    0x18130305040522050c0403020108181002070f02030105150d1704120305070201180810020306040e0a0b1f061407030c0b010b09120703020117070903021c0212060c0421 73
    0x3c0140600030341c8507240741c0600541c50042145950b001d00c06243d40c01240402400944550f012480c3c50300c034406040b40c2c0d0b54855054850b8495034900c1503080b64490303041110310345040701d12502503140a11810f070b401000032000c41843d9120034001214401c01d01d030010000303c410100140b282c00070005540c0a84501042003c403003a81e8140030341a0740001e102240050850401b101070310740601d004100719038090004145030780c2c140c02020042e4100034861900b1650f216803500c42030800b00600d250141c041c241907662400d0200c3e41c030b0b1721403d20201c802c030025200740c010840140d014400c4402c074000d40c83c03010340b0b5250f80e1070b0840d240d240c0c80601401850300700e400856a2080b0310001e00c605641251b189002c0b0a000d59059150132240c071019000c10040502045202d040010580d4130414030314003076014075260b0340081d035440500307a020464046031400e00021814440c0c413050040c000d40c401020b60745040d4080120504c2203024642c1802c50a488450740c1c0750380711100000c0c0d503502 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 467061474 1250 467060224 467060239
    0x40f0803010902220501051905071a01030210080702030405040506030a060507110106061409010c082106120f1c03110c010b031915050408091f0e181303050405 70
    0x480b080d0b1070280d044001c2c0301c0ea010034000801e925502c0383e080303107508a0b10306071240c0342845041c02c851200b0201e034459000a10000300081000181c401103002044007203139035807030103550442c0180500c110362b00140805100c14401400309442e0000191400c555044601080c2c42d40c8030f8001c81e003011101040245413a0a06050109132600179001c0b0100007504402000b40c590780700811508204950306240410608006607009540304945c44030702d040c01011524500764000344a0036408031507015420340302c40c0c03030000d100c00303481e01c51841421841c10000510000c0400000d02e9198451220b140c010760391842d2201182d18040d03005904511078035280300381c03200d61020100d40607110111200f4864002c01480403c456808110150015040b900c0c070742d25821100c2d82c0a00409001c0c20030f40e4600011312030b9640e00e5a03441e50801c504100c0401c0810381d90078802001c1c3c40c1c01034029046200301c611480942c0d200401404140d84036501600c070f01d41c0d0480a04040c1e03070620540d013016411072103 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 467062724 1250 467061474 467061479
    0x60405010b0108100b0304060510470d050702010b1009080f070b1902280605060307140d02060405090f0103120306050d11180a0b1e0303070b040f080301 67
    0x1041d88601000d82007a281c8803001c0d030758840152440100c80c05100c0148a0a20104000c03500550010f980108003800b12820355403075280c0c07803980041c0d4445c58030701c090030403502d504e514103268045215525070403a0203012a40010f482d034a18052000a40d507001e0340c0e41c00180102b17100350000325200c40c0250107141c9011007028001c00e80700b154006d0807090310901e600c2c1c140782c040016000c412902c84000e81c900b4100391000c0b040c9050079500c40300e070441c0f050080760501c1448400c13043d0145240400710711000007981c6020b60680740002c000511a030807402040149440074014444800012100c00d1580303603e603c001212030050760403841d04450700714100000c01007400c02e541d0680b40618203030079040b54400c0e0201c007603031480c1c054240c01180f00b42d5403100140a06008c404400d00003050441d01c46881207014401c0348048955101c41170b154118411182000f5030104540c24130441d450b02041c2d840404070703030b4900ca1a000100001c00700030000f020b10000600d50082160700c60b45103903907940d = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 467063974 1250 467062724 467062733
    0x1806040c1e170102090a21121701060305090607020c0306152e11160b09060c060f1f05060a051e040905040b180705011101020904110d06120305070b06120604 69
    0x10400d2000500580345c0000220741d0311f0506120314407010007254140368100303881e40c800040c0c0100c2c10703001040c401e07042c0fa42c4803448070880c100e030301814280d580015945030124a240c43d241020f0b08400564102c02a981c000c0d0310003042d110762100282c50300036015610f40740400e41c00994240c2d4031600310040c0760f041c140505c01c0d00b80e08034520340ca5510b16401d91080300a640d00d403283c0035680c04a9402005082185c44c1e1514064030f0402c0c002016242400607081d00281068011140c0c11103076071031581082114812900c00b8490004480c041d4041c00c0d00301400b141d01449011a80410b02002294030b54007180310b60602d1101610a60b00c582e10742e9070710300c8500040c20003900c007207031520a503200041d01604402060621864060001c01899162400540d4140e000e042615107a540820000e0313844c0d201c50281c0070f00080202210313640c03442541068803c540032504800200d4a0324683d200200307a00c04240c61840350019100603c6803524400501d07a015003590365240b90140004000501 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 467065224 1250 467063974 467063977
    0x1225020904031107051801052d0915100306050114040803030f04050703050a0506010e0a181104060906030c051905130b0105040e010303050d05010b040513020304140609061806040c1e170102 83
    0xa500540b109c89003d030214800e0800c0401a8110601289544800c56460b02d003000000c1d4000c00d0456444444003000c40c00b00c1c0041c206404400d0100741c60300b80410055070311424184c410003c0144040c01c2509040b520364880c44084c0914090700c111001007420300005101c050000c1d41d0003001c031002c003421803601ca40c0301c107805d214a92601c00740c040042d0349a45940101410a040801405011000d56442c8020000b81003421500290340e00804036941045201e0f800180d80142c03d070b0b8458620b00f0302048800c01066070305101055505d031081209413141440001c000f182c408010501a5241004071900d000c0c603400a1468a40300b800001450f802500a0491110300e00c0e092000c1d80e02c48140d10fa941c404c603c6070a4010f40001000718590700190301954009106031802001440418400c0b8030b06401030b202807440b5049807042c8502d4903103800c0b29000240c0090060142441e1945441d12403c1c818804d075280748400c1c3d21020382481e0341025040c00307880c816082c02c1d620100040894004d = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 467066474 1250 467065224 467065229
    0x403030f1103090f0603041b06020a020405151f0c060c050403050d0206070509150d020a020309030708012c03131815030807140a051225020904031107051801 69
    0x1c00c1c90711450340750100d40482251515030010340400c1c884141d800901402c0d034001401918100085010102980340b4401420001c102990040128501d14010401100d9000c2c001010124180f16145842d8681084060800071058005003610404139425110b4102c41c0000900e41841c050407411034680180251013583c1c000c101321141024902016a95003200351900004100300b40803030541450101410407803203003051074103400d2045104d110001c1c2c0c4c102c21480000342c0c10104088407103050400c107880081100400a0092001913501c1d9080e405000d541d0000300c1c50b01c0000013001e40c0c004c104850407010144010004182d4030081c480c008280c0c5a8a074500c54188450000418180032401c02501d1f00100c06924062080c1c2e11480c2410300c41c2100c0e0700501801d65482e010800c1802015820104081c9c1d407607440c00946115149205510585c03010440e00b41d414001689810074140c0d03011b981810225074101c2450b80c56440e0039040e0307100382d41c0259480d007020b4000d0400c1104a04 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 467067724 1250 467066474 467066477
    0x415050115112a0a030203071d06060a050f0901051b06090d03150512011107030915110604021912050f0c09160804290f0601080702030409200403030f 66
    0x2180e2104068550b1a8811000b07640c9402414201c5680c502c060308241e0383c00403100401c00c1e5020340e078aa000c0f030b080c0485030b0301411681c4c203a1403c41c002c1001c440d00003a40110200d54030351a0034400000a0064001d03040d40b0318100da0041020072013a401401180c1d210016800000903248044110907030310705084400603241e001e400140d1045038040d0142a01511406000201b51802c01c0103100348144452807210840d034a4100c0801103081540003014818000d9a4803400d103402c01140405a4902d10154000c002c10480108111040429810f8025a0445401c0c0260000701c4401400203465000401031030580b00e90310041000c0044e800207500c0c0f9580c166118210100104140d0f68812142101101d482207800c82002e07100e1401a64030900c164030355072040d08010080710042140741400c40809410009000e8168280400651b0050091804030310780c0c940000025101d00440c408c3c52003031a211513046400b6407030b0030310445c0000300b40d00c1c1d5145c890355641001420034401101010 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 467068974 1250 467067724 467067737
    0x1623060c0a031206151b081603030b060403020906040506131e0608190b04080c0d0c02042d0c0c0206030a0c09151d010e030d05130b0c06010605030415050115 69
    0x4584209019130307011a0125101c82062014014080e9524940010641041000c00c84403100280d0510050140c607280e42540b0140c002d0507240c0038003124086544244a26018042000142e41d01140c2c1541f018068901140f1600e401011074103842c112007245100794240030007503200036000001011004951042480705d50759404405440e0360078130783c4120704488070307162010110b0080440c00343c110388610703007aa20f4001400c0070382e41010680c003103800004900714441801d40c031f810701030849154044444030442031509182c1d01c0d0003110700650002c1c4551901002c84119006001c102c2c2c0d01500030342096034078541820300400603d88008140c01040030881d002c900105940c0f43d076080382010340c4170100c07090000b500112591080701c800720304003c100c8040d814151420701031001c0c41e18964a8294441c00e410306440d40300842d40d0403005800200b800130042c840c10024000341110000e09206a8984072410500b50b00881c0f84020070b1064123000001071641084071094042070341070b50358903 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 467070224 1250 467068974 467068997
    0x50712031e060803071b030b0f060907050c06220b0f0a050f01080c090604090210080103050f0307081207170c07120f020307060e07050d110a06021623060c0a03 70
    0x210100e99880c020f420041c1d2041c06090002614040541c40b04100038400d208429503c1d44d5040522000307c542c40a03d00005080c040c45041601d10300390085010700f0040d003082c011520440d5150700040c00c182080d104040800052500c508582c00c41c6034000c0403800d25450004019041e9400540b0701d90702940c5003100096541c06816a000d0688010201411642d940c450400407858005861194815501c071800001682c9840c0207d000b141c0c143c5441d02e00d5851428900e04003e80e21040b10748079001008142e00003000181100d0030343c2e4800040c400035856114040310440c1c10301a140e50400e010000340708110914201415109105007020781748a6000381080303c2d080c0701e122904000d68014040040050078903041641c1d40250a011219071f00d0741d03070f00000c038030161245060f41c0f07200943c034200100d401d080c402400078040d18001066082c511001c106012801803048031025442d001d01e2001d16004032400e101c803403c3c014241511420340b480415100d0044c0c200440200f190050748 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 467071474 1250 467070224 467070281
    0x204031407150305041b0602010515090610080c0408010c020a140106060912020d060c0e09090a05071a07020d0b0a0f0605130e0a0507080601080d031e020a05071203 72
    0xc401e9441d12420b844108450007816006040050f1040b0b40d842c822000802c03403051460588401840030741e00100e064103048a1310300201240120003400380d2040c03000c000e10717911094040083d00000c8d05d0a0102c59132038000c01000c07401550000c4840e075081c0081c412090364001800080180135400c907060301d68012807100e00302c503034030f118240104000c1402084034160610011240c0c0b4000352030010707000c55a941c0e040c01c8070b00c84040d4101181d5000c02d0b1800302e0074141c0d8501d40c0401460010701100b54130303860f1180e079232645214402142d031409160301a074207150740c242c481c0c0d5030740070341840782040c10380c0b81c00c0c1d84001080b107009280a1426402e08a00c001030f0142c5401c0780c46c041c000035032640344075400c4c4014140760582e2000c0343c0700742e540040000b042082880014150000540f60a5051105060410642c3d1900034101401c20629940c411902e40041ca4580d68801005a80c0c0c0c1c00e00105031400e00600c24050b02c050402e444500e406038154002a120b0145035035592a14440f0424 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 467072724 1250 467071474 467071483
    0x150908010c140a030f0609020d0c030603150504020a080a0b070e0634080301030821070207090c110624030f06060f15041503110406020a1209081002040314 68
    0x90342001030341c286101c03682c05101800420f400c80c214500030482450140b0b040b402d650155002c0c510f0709a0000e81400250480d100707030303c8041d02901e0f040c0003103465a180c136183c0714040c1c2c2144541c181d03204081003c40d44c4d08002070004100010079290340c41014104003218280403100700010440c600340760b0000d0701c0c113001241e00424070702d4290755000ca03014000c3c40d505002d036407084c2c50f503040009a00b40032074055005180210300c140c0015503076000085c05c0464500d030b60b610f4014245503480034400c80c907402260580640302ca000d400540c0e032907c4c0c402240c104045c403840c007185000e02400c4c1311540443c040c402d40c10f0311130b415206040c1d03032201040c9507a5498102414104c1c6c0c002c800412241c1ca040184201c0c4544001c00030503400444d40f0000001c0d6000740d014150f07000c039205064800a07018014800c0d00250240c1c854105850040003075200d5203443c00040900b001503d00003d101d00901201000d8100401259540c00402c42c00000075882130100342c40d02c941d04c00005c10030345800034 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 467073974 1250 467072724 467072741
    0x307060c080304030c03031805010221010b0403060b010e090a05090f1204170a05010c05190e0a0b030618011e0e070225090504080901080a090b13050a0b0115090801 72
    0x841552030360f40c5584088500000c0c850b011010107440b40c00020b404203541c0800c0010fa8050000140d80d080465030300e1180303607032610440c2101e403090b000411000000c581a9800c41b504418081900c41240004030b0300d400c0b010b041c05030322030300080500a50a150b030340958860320601003110034900e00f252030b05a8030804080b140b900300340d00308414000015444bd601d01c04221110480d50001000e41e00c907401d4401d03201c0704100003207001c80c0203d400c1c1d0051011541d085403d08080d00e4541140c00421159120703400790310500107002001c0391140c2ca840305151418001c0c20620041c40d6100c50700481040301841159035005c11241c808a00444800c02e96802255140c0050800c03c5002c011503c1c1140c503d2142c141c00b0348031042c00660540d01380281c610030b52041200e160b070303407400c0000541040005400300300703203600c2d14220340c0000e403030401182e4100c1000d2720140360103001458900d02c1d026181400511032485040000b50f0170307014058200c080011750300c07070390203258032401da0f09c3c222000d61 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 467075224 1250 467073974 467073983
    0x206010b090d02031c08090d1b03082208090102070b09060921070807170f060f0c1e090f0909070506090612160f0309020303030402040b041b0203090307060c 69
    0x8105101c800c0c940206242e242503c054156640c0c1001400902c2c2c06400141124000c64511010040c0202c400d0000134203120103400c0450b000d488103c801f940c1821001801003c1c040a04041102c140c0d0241c001103000b01d03601c86546000d03020b41303004c01c01600450462030143c4141c0b4030200f903044001c3d0680b150003201800103410004200e042140e03a100170390700e41070909150440c20154400c144440c1d0081c1042c04c000300f119a03c0c00354110541d0044c02c442071b1a0b50040071410001356808114150800c0302c1c0c02841c40c035602c407901501c0c0544100480485030100040d01800032540540240030030801c11121400320710183c40a101130b4100c00c4844c2440d13034000440501c02c0c0d00d410405003140030030140001c1c0c2042c0c07005450045082042e524080c0301c0d107410110440550384024510400e014600d8203218482030f5501003a43d034000648004c1c40380380c64404c41c40f041c0d16150720500b0100f01002c0380d0400c40c0103180010703449910501040e4002d0240060101e402d50182c100b0000c40b9900 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 467076474 1250 467075224 467075227
    0x12031706010c150914190b0f061003150503100609110415030908120f09060601020f0d030506190b0a14091005070c051e0405011e180f1811010206010b 66
    0x103090f4401c00a04d0a42c0003159400580092619078220400044840c0520f000b20908a07a44600745803410010040501e082c01c2c1c401820400e00f0f489040446405011a080104d07850110f550f1001107070b01c00341c10807500b41c0b01d0944513044128080c0c1000040b01d620031410001c2d5043e083e4100f0440c03086019800520703d000a0260071507209500200354030313000c3c030384050401c440c0c507803c11606a800d0f80c0320006080500d05000e5000c6091000d15003120707017400188071944111004945030b61a03182c503141455902ca000030b4982d200d1302148401e4005080034850301945401074100c5a411022807000021a00c00800d500f900d1f0020881d00d60304070041040b0445103044004840c1d0307920881045132901d820002c0050b0940345d503240b0462101a4024201035400000d01303100480b40164405e503c081d2400b032303500c0210f0140c207580600b56192000343e1262228020705440151600e1610007504a02e0200d0050701c04010010000c1d51510400d541100c05e0860401260303038070828025410300500 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 467077724 1250 467076474 467076503
    0x61109010c020123040e04021804050d0315030206030906100f1208160b25090e070e0a0b0f0d0b090402030c060d150e090106050a0315050c0412031706010c 68
    0x480280c0103454505203000c51311601c192404c2105e412940c0f201d20034078035a0303013071004601d0400d080c03000c510403a0303000c610700d031900d52204c540d240d68159982040c180e885842c80d05008000d0705200107150054180d6649041504c4281d5541c1c80c1100c1405204200341008520b010031118048102c80000340103642c250342a8580c0c01d01d50303014840700500d01401c3c120300c00004040c1042c40780700303111600c2c5c000380440b001a008040d4585d42401501000036540c41031280f003400d00840e9400805528020010809840202d100620326800440d110400402c904041e8031440c40100300c0c05100803c28000950201c0500c000c040054400035450782001c02195111f04120740030f803549040421000ca6990747c07100350400c410280390030445031403000c0400c00c2240d510901407100108021b8a4640d1401d01d9a121401e0700012001c00320f040c01d48a01c04912400011820b0701c024180c01c5028204c1503100385400b038406004c803806000d0020000c00003895660040420505036500172a0071f40396010f = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 467078974 1250 467077724 467077727
    0xf121201090f020403061b1202071a0603010209090103060902100507150509010b180612060f04030e062a0f01200c03070605010e0a1103010b1803070302060c0109061109010c0201 78
    0x25215600c04983d800d100c0000892400d0040c13185010b9102e01000081543e504010140200e210081d000c03940108a0b03400061301c0c174421005000c2500d842d00e80d150b207884c070029003e40301c0c1085c00c0d640580e18100100904c41241d0210452902c01c80b042020010040400d40710b601a450703014088031070305c0071140c0d0401c1154218590006010000103030210503107000440b4001c0d4030001380008038000301045142d0030401107034030842c40b10350000c10040c50f1003205024110703002407005081012840704a2a1520385809507a140c1107000c2c4005a036000703a910444844000b10038070301c0d0610880c80e81a24a000612031132141414207032020445124111400748641e104d0918980c880c0300c10000311011485510405e0b000c0c1418142c01d640d142041d0342050b041d500340090a4249031803c20040240b00c000c4c1c0d080360102d1030742da0034030403000302031000090401005910180d0410400160442225810350107020014850601009000441d440803003481c0543e01c0c02c24040f0704210790090156 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 467080224 1250 467078974 467078981
    0x1030506181f06121805030306010c080c1b0103050f04120513030506090d021005090304060c020418052a06040504020f0c07030f060b0906150a0306170f12120109 71
    0x3030850741c1c0d51002c403582d010700c40380c409842d50020000928207004540030b1509406000800d00c2603000d80b841e560802e4581035201c0c8006803245041c855074a2040b01044400e10a0769441c107041425200e61a0360281c4c0c80c4030310300464980a00003468040056100d80c2da0b42e10041c007941e00841c00340884100030074203440c0b039440b03a100e900d040e01d018900040000d604200a501c504044400380c144408280c001901e003c030f50300203000070141010204005200300000351000c0f18107515050320000304600215000b0101048010b4004160b04a01421b0020000e90318021454001015500d40a5504880e095510380f0710344170342c800c0041000700201d107859001381c146001d44c0c655603403404101d949810710b414030f541c0c03003202e0410301c826100e41031081c94811020300b400c3c01d03030716038603a843c01740d000503220048011240d50301e98012482c03020007071080d4030040c06002c0000d410f10100c1007402c0c00d5030350391a0410652070b16114103003442452059880c1511001e0700c0c043c501146590800d450388024 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 467081474 1250 467080224 467080231
    0x708090c06030c28020d090602060f0604020c101a0a0b120403090e0415050c0901020a15060f0308040816210f02061c050603030c1b0f1504090b0103050618 68
    0x109202108440b141413400e016040e60400980d81e084440a41c003a09140c42040090280041980d01700040c40d0007080c0664003080316060301c5995981d001c000f400a000340c1c401c1b0030003403184c02c02d10060840c45501c41506c00c02040040800780d91503408001348100c050148001d410f8040c4500000036012100c520340040c42800d20884843c2c850201c02803080c4c00f16000c0d02d240b1b500055640011002d40718498000c0e0445031040d2400e030f20500040d58654401302d00400410740c0d01e42c0c40c407980480d940000098040c551200014969030704202a40390070a0003030100780c0c019140018181165000e280d8115414500c00112500760002400010b01d842c0d0419200140c61100080069951078010180d4000046010b000460496007580440e0002044075000754070802540ca4103001c00507960280c907130082c2a0781c1c2000801404602c621854a0050f17400005051225072890750500290003500d98030351080114921100045007903c0040c0e50750ba402c00d0084441c0319034143d11486490340b = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 467082724 1250 467081474 467081491
    0xa0216060b1203070f120c020d0201050714100c020f011a130e01110a03150e0a0c050f0406050406110111043003050c0706090b04090b010207080106080105040b0708090c0603 76
    0x1900b803050b40c4403508651060804030b4241403640c058904018000e002111003c02616200c440e150069000c18240450007902038140030b40891801c003000740544507100c0440761b401c20750703424650303c03005c83c40542035244084002d40140460401d00d92014031034a1a050100c0c000ea5044e0305201003408a18000b40c0726100450b91291004683c074003090140c401482d00f0510015580c92108800030100c034607081c0448060700132500d0402051040f0000c064005412000015285c49104001d50325440341250aa00018020a001503141c1c0c218010300f04070350550701d640307204009103806075080b0741d80d003542000900010f000a00038940180e00c11207031200222260702c441441070312250400c20b940c1e0400c9000078400500104e40c2e000601050004001600707241307804030f082c0548500c0074000c500411110503600c8180c00c0d01603100f0040e520041030b004001304007003a140c56031580038000c00c84058504c555040c02046005100d81040e92051707080038049e001c40c1c8400b60800c0b0700d0350f0014103100d0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 467083974 1250 467082724 467082739
    0xc0301152601110a030e01200d02070b090a050d020f06042613031101020c0102060a021305100503070306051509010827031c02090913020d0602210a0216060b 69
    0x401d014400d10400141c0c0300404a41e40c0c6640e2107490040564000100140c03299040024180c2c000300c5150400c0b619012402007207445041e040c00d4040240103109010740707000311540611410210100d4031040641c003030010703502c06c08441c1c5020380c1c0d501000300300000b443e070001c0e0001c0c0105140030114078990703603080c44000d154210b11402042c036422010754003d510011a0b000c00800170071020b484060802800a80007510315000040d40300c1034000c248100c0c03103400040701c8406000d0750388200b004d0700005181240b100080c803030050031a08101c603103801080c900070020426203080380c3d4014a5800a8283c0d80c0780c4100da10044594820181c9200d9804211103086c1110048082c0d00d482912520401143c5900d1050b0681010016004201e0407080c4100140d4140d511180581c5030720150060249107003c1c094404107540e5940303084042d10052001c546030380c000410050700b03030380c40c480320266000700d03217404482404030712803802c941c07060300d10300110701e40000ca154005030b203c2c220042c40e20 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 467085224 1250 467083974 467084039
    0x11032203051b0c030f161205010b09040506071d13020a03060801020c0309031603210207080a03080a0b0f031c05280206010b040e010b1c140601020c030115 68
    0x114160300c2d03a04400102c81d0081805021581030030000c50309050114802092440a9522440c1c40780c005030103481c07a04140104407078280030f402d4001d1500180c020b4008902840d050900c1900d41c10140d65030000640d460044500d2017444119035070600c070008007120340c04200804094000d40c0a500208207043c1c070b40d013000070f40fa40d081c4090110312007e00007456980d008401058244450201c200702925180c401c02c1c0042200300f0010079407190010220b45504444100603450b01581d40d0100c0510f204c0c49181c03000f0580c1c0803200034000d4031854800d0181c4500030040145e042864481c8a400d43d02c0340725000e9507411080310044802c041c0381041454501d80300850f81c1ea6201040341566010380e001407072503501d80d040107001e00500c50000707a541441d00b02003c50030001018481c01942100110b0f0700240b004031169031141600c803440d0200b00d2700000301c4e40460310720002c0754558054040c040400c1681e04060140010b072128114a001c440360520030741e0380b903030800040700b4850750b41071441c0c0 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 467086330 1106 467085224 467085247
    0x5010f0504080a08070c030c0f030209010806190506010306030b0c0a0801321314010807081f0c052a010f11030406050615120a1103220305 61
    0x132655039a031030341005450a805604054030101c01c04900140c1c0200700203441e02224820f41d041b0b605031383e80f0b030b41c402c0d01c0d04c50456003454990441495500b04003403c0e40440d5200d03405042c0041c1d215103940755000903d5084030313002000d03800001d1301c0313b50380d800481c00c90062007401034030407803400c2080322035000c4182d030030981171001004480003046540e07244010000001000c410000b144145203218413514080c482d4400034042c032007003c900c0351004181c00949031011060162601d01030401c4200510307245c0200700402c0310601c020500c8020b01c1501c600e01e000c96005020300045000e10103401c4640c410b0403092020300d45404884110603c409581e40140c00180005a82e601e400200d056033b00c100074803404481d4002000c0600e0044201401c0c018424450100701d0381d00c480d142c1c44031a20054075032030605005e000501500d000808541c0349818800c1c1790050901401d8a00e = true := by decide +kernel

theorem cover : BRFrame.Cov 466906474 467086330 := by
  have h0 := BRFrame.cov_init 466906474
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466906474 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466906474 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466906474 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466906474 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466906474 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466906474 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466906474 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466906474 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466906474 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466906474 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466906474 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466906474 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466906474 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466906474 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466906474 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466906474 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466906474 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466906474 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466906474 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466906474 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466906474 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466906474 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466906474 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466906474 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466906474 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466906474 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466906474 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466906474 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466906474 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466906474 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466906474 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466906474 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466906474 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466906474 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466906474 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466906474 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466906474 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466906474 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466906474 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466906474 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466906474 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466906474 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466906474 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466906474 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466906474 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466906474 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466906474 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466906474 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466906474 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466906474 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466906474 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466906474 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466906474 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466906474 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466906474 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466906474 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466906474 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466906474 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466906474 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466906474 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466906474 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466906474 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466906474 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466906474 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466906474 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466906474 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466906474 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466906474 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466906474 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466906474 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466906474 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466906474 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466906474 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466906474 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466906474 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466906474 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466906474 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466906474 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466906474 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466906474 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466906474 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466906474 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466906474 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466906474 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466906474 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466906474 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466906474 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466906474 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466906474 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466906474 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466906474 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466906474 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466906474 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466906474 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466906474 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466906474 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466906474 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466906474 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466906474 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466906474 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466906474 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466906474 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466906474 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466906474 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466906474 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466906474 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466906474 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466906474 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466906474 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466906474 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466906474 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466906474 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466906474 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466906474 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466906474 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466906474 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466906474 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466906474 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466906474 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466906474 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466906474 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466906474 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466906474 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466906474 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466906474 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466906474 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466906474 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466906474 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466906474 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466906474 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466906474 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466906474 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466906474 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466906474 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466906474 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466906474 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466906474 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466906474 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466906474 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466906474 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466906474 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466906474 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466906474 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466906474 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 466906474 ≤ n) (h2 : n < 467086330) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
