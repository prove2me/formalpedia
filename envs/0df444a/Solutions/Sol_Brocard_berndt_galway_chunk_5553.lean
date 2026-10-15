-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5553
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T16:14:59.445978+00:00
-- url     : https://prove2.me/submissions/3479016d-f24e-45c7-ab99-4e226178cf35

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 998561151 ≤ n < 998741007 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 998562401 1250 998561151 998561159
    0x10608060a02120f06030d1409041104031505130f0302190804050a0b180f0a150206190b010207061b060e010c020c100f0302030a0f0e0d0807020c0a0506030705190504 73
    0x200d00c0b962100c07041d281d09a0307a003404400b1980d00c041d40207650b410011018a806a08d445150845a110310002d1092161b00f0079012075443d07650040c80100c500050224000007802402e000d036512a0045100f02032400608d502d85031141044510b084007180a642001c42d07076041c5410540c603201e4040c40c001c5840c1d5040c20305000002c10301d90404000c240c800e100e800e115440030003182a0720101941d007a156000c058011800b811003c0d000401d42680280a4030b0780c10fa4001480ca01c08c400030a00180d03000c68400f4850201c4840292490058114207014805180a1a06400c441c0303007409050702c405a039a19039004840060b0b2140050342d4564a0941c403e60741042040c5203010103c60341240500d0001000c1e2540300c50140407000c0c0341d00400081c500c04c0301e581c03200340c44e0101c081052111854140600303407a20344034000003020441000100c1e06c0711f44001140c2c10307520400f81c2710120440c01c04040150603040204200108001044110b00404415400d4600c41c40c850b10f034142c4440c10 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 998563651 1250 998562401 998562427
    0xd1211211006020c210703080412060c0c050c0f0f1e09060405101401230909010e070906080c0c190c0617060f030a0210230301081509010608060a02 65
    0x1076030b4400c00441d80b203414490740075500c0120410070207115000c1c0c40c0c1c0681d81200da0390300b80481c0e0b41c0050581400890001506800c228900c4541442000b04008100390070f130081d242d02c0c0d8050000b8003642c2c04068443e034036044c011050101d901c0b0040841800b282c824000400415540300c000e0100d82e00d02d04061a1030415a4003940c1081007258240700300e1a0102045440c4810381c894503904880000c1c1c58001c03a4000c400420041030260846115891a803000c003155a000c4000540104105000016000300116032280940b17419078440c1c0b501e6251280450318100050310f000341d40f1604001d580c078000e40c03c000a1858103200300f2282c00d04025400d08442107021030f800074080c003074107000e004110070400c810681c0c0072074110b41c0128114151b01c00f00b8a00101050001c0d08251300801d043c0c1c4a0742c02c00c2840c00b40042c1030300c40306454000c0d81101c4260740070a00c035070161540700303070282c2c10303201c0454004551004500c40001403560b0b480c4041d80c50010142d81981d00158006459551850 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 998564901 1250 998563651 998563681
    0x14030702010914100c030504120b01050306060a23010908011407180f06050304063c02093a0b060f100206010b0c0304050a081e0d121121 60
    0x4100c110f42802c0c601c400003c40c0c400180d40d01440b0401c8800c20485042501034820396002d40b10040c45403d002032180380c0041081c2082c09242d00c02c7c803d103400500f480c41c14001e00401d40f9050055640501001070700c08020042c840a00d1b03041c0306c0e65030008a0304400900c03031410181071000840c0c0e038a0a020340040c200f42e0450300340391029000c4010a0140b5580344d0f810300100c500620f07001b940c0390303a2170500358001c1a18a40c02c91030402800d81046010080b12465952210840d01d0360503940031a0070300800707d00c02d440030707550420100c6156240340c103084040091201c0390400e4014a9250156030000e1201e00b1480440750801d540051241504020f100707410224030540e90501c030010543c1000e9a165414415007106e240000740d10f02111078244142e400801010303100e640403903115081d827500d400b641c00e61500303600c0d59404041000000010a039554120980701c00c603407600c0e0b5406820141400c0c1550240c0c844082103d480301c05107a9100303030701842c11107a41d0101410244400e00c2206 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 998566151 1250 998564901 998564909
    0x604061a07020609010318030f11030a09050d0206070209130b011a07390302030f0303130f08040312110d0905060a1b08040314010b010f0c030305070309140307020109 73
    0x4400000805a2500c04008641d400742d0100e07880c070780310080c882c012000382c0740100710100c403e8100c0c00c112042541200f071806282c0220b48800125a040c8801140c0d60f0242c0508100041c1e200e4400300101d003002c0a841c00a14000b6101e50315269094002c00c101040070759603100301c1444000c45105100e5460500fa0141102c400241854000510400c010340249a806002032070421400c2c244948034041081c92441c40309030032224424003051030a019030407880240d000b4011001004502000481260310503060920381010300c400c65201e1911482008000302c913203007410480400450041c0c0d09850b0003401596403810250078150345941070122490000007841904c0388107000079610441507844841e92450710304503410841c01c0603a0781480c070309005450400000340100130b111402d0007016941c82400002e0107140400001151902d43c002110000a00017800c010f0001e40b00750481c6030458854038010501e510240c9419656a02c40303207116006900c0060380c00b0441d43c000300140018 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 998567401 1250 998566151 998566169
    0x907030c0312111c1b0203100b0405061801180e01060902030123010801060c0503070807050c030d1d130b03060c0a09300314071b080609070b1b15060406 67
    0x107005901c20000707010300340c01148041c0007042031010b0350303500303889000c1107620b400800329120018110301c8c1d04014242c5008240c0a0381c1001c00059032401e1665507100e1610443c408507115038a00b8a006001c8160180302405403621626246030000c1c09010740c40103061022001a941d501d03000c200100011490300241c0c242d00007403082e80003030b030304400d2107411542182001c48890000786040e41c1980701d19140240010b00c0030420740306019000480c20810442501105c04401074046d0664285015060b40078010a0100303640040303080c022104145c1c000302003004201399410303000103030070710000b2540000b8401c0c0102e101c14040b9405070a1070005c15284480000418140040183e1400018440700035200500c41d01c500705842829901440010f03440b00980716400352510f14400118480085282e003200c03803011424403404148640103913985001400014648955440d00340c0120740c0f001003040210256001803103060080002614400414186a281800412044400303d401500398 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 998568651 1250 998567401 998567413
    0x903130305161706180f01020c1e0a050606040b0a1d0609151f0c020604090501180204050d12140a020109050709021611040207060603050606040c02030315090907030c031211 76
    0xb24100442d000790090102d0400300c2d03c1004950702c540c41c0821190082038a5880090004030785500843c038006d030795402c00404400ac895001c0410350b600e424920242c11900280085902460564858840e83c500642000181580c0d0003003550000c0322226640030850042d800c2145030b2422200e0382d80c0c0305210406030071951199101043c0154644400d20880c41e503103481103010305001d030a0b00c140d81580144034543d215140d2210b6030103031600f84103021481c0344010034045000141d0003030350180d0720054210390300050395460302568182013054917030502006140403010140e03a01c0042454415035000442c181b00f0303a24190307141c80c80710b6101c410b08501c103000076681d88447c1c40704801c0054200302d42000c450100000100244227080d4000c0c8034510b08100002001030101d01d080c8140c0c07049408108a00700913100341e0b00c030700c4100c81c801d0182c00000c1c401c80c4980b400120352134105802d50102c1c1e03c4140c0701c2c0c2d11140036142540040e0707000445062a040002d50204099124280348405024 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 998569901 1250 998568651 998568689
    0x91a0709061803060c120e060411281202011709070612110307122405120a140c1f05030103030503060d020d0606180b18090313030516 59
    0x100100e00c6028800811001c81d10680c2d4a00d03039215803030041c542207682040200c00c0c1c1130000e84003200a20119280b00c0c289442c020507940c002c41c05038411303904040d9038074800e2350520400c8a0341c9007100000c018800501c065610310046c070340c60b5401500780411594841005800090300445810601042c00310400c4108035500c1004140c175400c4861a080c481c545521000c0050042d0440c0da13203100c224500441000001075014140b2210700d41940400c0282cac0c000394a10402d03000200360120304403040741c10200200c2c1000c43c1521500c4c142401610001001030743c4c0c0509201070110901e620f0362101007a06a9480c04000170701c0203400204180030142d5503030101408034041448080d041c80310120000382507403200c01041000c030b540100440c41c0041e0b0b9181450040409004044884c400d0f16401c2840e514548a07460450710014152407400f40704403125444040020300c081181e0100707000d1480c440f103100b011b20b030107140b0400191170201d0b0101001d42c0382540f258002030300d460541c100f5203 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 998571151 1250 998569901 998569907
    0x9170901030f11191b0507030218061e060c060103061b0c050c300a0b07030213090f0612060c12091a040201021c110c0102010e06070804020414010306091a07 69
    0x5406607500e01400482510710513400e0342c440069002c5581070200d50550300c1c04018012a42c10b094a108030f5040440791462599203030a1307002290300c1c0390007000446504500043cac030b03510f0464604005120f189054100d0022038100301c002c1c1d000302c030710645881b4041e20560040c030005103c99418036050312100c465482d626039840801482601540104108003041c036550302100d010301c600400c48170112211005800d03564040190261004505072022503c0f441c403e0080740d81e2078000c0181c0d89032071400c202d140c00040c00a000200c49003643c460001070070140e0819144180ca005042c0012040d400b0314004d000c803040c81c1811080305150040c10400119040703048a0003840181ca01d140d00d640324401031b0b103091040600e241c0c003034285510742c0c0440390380031210859520041040d41d554241d51401642650341540e0590324a8001000045182e4400c1c03002c698402d000500104401c8000ca0004d90020001e030426650541c58004c070105020749046845119400400c0316045458a02802 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 998572401 1250 998571151 998571157
    0x2010219050102040b0307050307180b0d27140f07060903060e010e010e07081203040305070318050a0b090306070815131e0b010f230306010309170901030f11 69
    0x2901180884500d5a020301000354156000742101000c2503030b50307040c8110003418940089804600060070030800c1d500440c0040b01c2c2d00c08582e5040d446500303005880350580c0c05440b80c81c102c50601c3d6a0b28448084000c2c1c4e46210159003406162600f07e02245000070034100000d488500703000d50303c507580c10015254800c90a2080340e4020f040010780c8615030188501529000040c40720f95070920401c041c40700408122402120645402ca561004800d41c20403040c1c0070894020f001700b5810301440b4046806006100c0786681c4072a123114007030b9150b00010315640c555800809020300c0120b80c840c2030342403c010301900b0801d0350a00c4040d9141842002c0d1090000c0c1155602444500b41b8101e55580d880d0040e01403002e11504002c00d41500c00f201c1401001e040421a00145070000d06280160140c0880061400544904040040f1001e1b6a686d65480503140c0d904040d500d11035500418005080d40b10080503020245aa403c162400107013664141c0000e903c50030720741042018100c5030070b822 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 998573651 1250 998572401 998572423
    0x340309150306061d0102160e06041a1503040c03050d080115051801031104051c02181302010c0f050a120306050f1c08040f03030f03050a06031e081306031a060304020102 74
    0x113102c0804c500040106c4c20142d0b102d0030546130b00705c15000841e880381c80c8401c041c1b260b081034404018000030ba01040c05840011800280c10003c400600340c10001f500c0e0065500c5800f0740a4101e46a40c0c96132614600511201c085000a08010042c8100d0001c20070110003403500c0c2c58030506042c2c0d424560950b00c201d041c0d00e18145a501e010103181400c0d600e00382c500900c0e00a1445200d00c2000080c510140c00002040b882480781045409102c1284071159025258110394a401315034503500661b40e00c21001310503100c1804a0581000149080200381d0000f0b1165020384404140c200000c2c05032034880d0012841400f48041604080c0c50b444a00303039002c04140301004020f003482c100000f10744115008003840000503200402850f41100903414444401c1e0340030041d541d210117102c81184c49031f000080540300354481c801403441701d0040314005540108441880c0046000e0300381e0002c0300c2503001030702180d1075188205001740614406600d203001960554610700d080e9000031f490300000d0318 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 998574901 1250 998573651 998573687
    0x60602030919090c0504090b0301021c05070302090904050a06060803040602030706050a0b1f09061b02010e0312221d16210b1c050334030915030606 65
    0x2039044000300342c01ca9a801050b42403010840754604500c010b101d41e0042c01140146400c1c44600843ca040502c2290410488480401c00030383d04010ba0740090500600018201a0280701c01e44c0c040c0e8800c414036011f60f10500040010036464540801642c401e580042d40a40051204100d0541c0110458544592200300007a0a44c3e840c102c840080102c2c01e0000d81142400015640c100344881c0c60b0b415625640d156040c800e071355140111070001543c50012281900b40d110180154040e000500310301c2002405d40310741110000d000550b9410010101040780d00355182c061a120309030200340d01410940707030341c0c0f000b481a00c0d0f418060a40c4c040c10401114512002454036148540a440c00750f015120b25900d41d11400d500c410007400851001c14410024480120f88554030342c000b90310350075032000245092200350320408696006652012410790655904000a50254410400000d1084d15480845802c105401c0a41440408110141441c0540510403a0b40010281c0e2629040711 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 998576151 1250 998574901 998574919
    0x5010602060a091a04290108030904022505010b041107121404080706030228080103080a030905030310141017060604080609100c030b0a0b1e0d0e0706030606020309 72
    0xca4500c200d502e46500e070328032a6540c0401d001c00c100b841081c00306e4690b5004e16502180c8a88203001e62030781c0e000e210f006800e501c204180040c03400e11307402520707154412800b80341c03d11280402040c5004641c01089481c0d96403510f5900d03041c9082d1251000382070100da4101d0078540c0341d50386d4034021041c05005500788000c1d0041c001c10b0120300e00445d0041d103840380036201c58980d41ca5000d000782d000300111101c2480d2244603c9074002240c2a2080000543d50318081d40b41d00e50b03100c22000c1d6000800c254109511441541301090041000314094410000881e4405140c1460308080c415545100b0740301d0340f081c8400c2511260310a00351198200843c01170340e810307250b4a0004010344200e601c250441e000320410840400c0b40480c1078001c211074054148030194121000310102c88030600d0035075000305803000600040e0100802750070040324248442d00e610903450382503d415000281e00010842d260b4919516040080c8400c4008040b241001d100303403420004003035100d0003200c0d411401001ca003 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 998577401 1250 998576151 998576153
    0x6030109050307080d0c111b010324230604090209031507030903140406021002070206130323030306090a0f09060c020321100302150904020d0905060a05010602060a09 73
    0x39840062940c0d070010490369100118035003481e00c0e41002c00c5a2100c580360000d50000d660059500031407108409003e842c4001070917a11154014015640a040603502c2c14254441c013008410b1520725141c1c1803c0da0b84403850301428000010829202c150441c419800881c825180c1c80250350541c4e520030400b503110580d031004a440c04015500d100d1103001d21409021900f81c2513840301035003501075039909024150503414a001ea02c075501c102d50060f4803244000903000e0127540a00446840104050328140c0180100040c04449400c00c0e00c101d090740e02e0100a41401240c58401d0000543c050b5003146840b8000500e0100002c1854642c1c0f521250000000074403903020140c0e0541c07120f41080b0140d86001e0080d6030760480f19150400b040d00e420024000078088150906c82e103c0d0401d18000d0780c1c00c2da03080c0a4020f01c05413000640b150300707000226180e52103002a00703030712204e406c0008810320541404d914001c0301600f888441e0303140c480103003c00d80c0d000c582180e12401446003c00d065000d = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 998578651 1250 998577401 998577403
    0x20a060f030f1a040e0a050303160c0203120307090906140d060f1a18010e04080c1e1f02190e0d0204020c0303183f07050f06090c06120603 61
    0x194644030030528034090b850282802500c400244003e0160b0b4100001110071038410350300d804662001d48240e2040c1f00150a0103071002c520f1884000c01d00c1d241062078030036404a8034000401c5054052124003108000c2038551049002e0000c0c501080107011007460300030f0b40354150003005a002c0c000c28824140b602840440d41081480d00d081d11300801c4414603042c4a041001c40002a462042e040c1505030f201c4d00120001c4941a141c41c0242c1030502d40311030391a150a81c2c8042c10300c1d442405a200c9034030300351011002c1c59845106100c0a4226859250100b9135004504281d411805106000c80a42d10454820f615080905130038214202840c42d00015900720b20303100c0080d07005000180e00e583c0e4200c0400554003980c0d40241084446200100c80e035140c40310202e2500c3c2c8001050752040d4400d5012451070502c103840d0f0b0b100000038805d10b851a0300c90b41715503020345440d402940c4110289604100c8140d0041d101c001520482c4036002c00203143c2d200f080d404d9060682e0080c082040d50b50 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 998579901 1250 998578651 998578661
    0xe0a080a030801080c010534050a050703050610080c0f0406051e0a05040903080a0b04200913110904020c0f0a031805060a050901030f062c010b07020a060f03 69
    0x4624000c8815011961500600e0070100340a03040710340c0511082c00c9140d502a105407460440356101040382c0500100c0c02206807400c4001c1440550481034000011034010300c0010f40c07030390240d0045c106040c110b040940c074040d800340120395250361030242001000808514424508000ca81001090312400000342c0500500d412a0381d02522102403050101d04050480ca0b0701ca20075100c1d10f050070740c0c0d0401c01017100e60b401d50240200f404600002c0d422052a400788140c40c1000b880018080b000001d036040c27505483e0f6054140810014081c0103a150144807030801204804040c485401d83d5840d0403401e02400d83c03442d0095801089006030b400040c0041c603000c08111003201e000d6132650030300070f105450103c2c1c1340003500700051002c602c5081480440b500c1d0602038540c103160490110044006000d41c50f410b0524540d00c1c000468002d0040f4142c400f0003030a61150001a00c140f00c5200c51980180c3c0305085d020001c20040c001a22000d9410080340da503810641c202a028000c01d0700505 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 998581151 1250 998579901 998579909
    0x5100908011b090b0c0706050a1e0504180b031b03121201031505090601030f06020d06030b0612072103350106020604020a032003010207050105090c0a0b07030e0a 71
    0x5420b1090300110803600d69078038800b00c00079584a41250f55526116540740c03050f0034500a00d40c001441c1400141e000e0b0004150145192610ba40813a24001100c2c0703217810360301c0d410302c002440050100103400c00c152040700354a50f40c54040052904a9002079a9010851410308180004c0039019142d43e0b0144140f15000d014440340e0313a40d804100503102c101030000d020845440d40461000c1c008500c07681301d06441380c00210010025a406c5454001416031039241c21540c00d502040700c604190300380e0080c10001c510412817807100c0c0c10800100300d104a2003001f103070940e500c42c003410000c041c200d50a003080702c025009019021001828107c034a29403d0881980d046150703a4440000f084081541600540070b104418180c1d807600812a03d0340415980a980b00074021400d00101351102c000c03441c2003640f00c050036101010407012a0030380c0c02c0b0881c02e440c04d95658003003140d48034051200240300141225909112810100900460300484101800704221900c11000030703268000c2000140c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 998582401 1250 998581151 998581153
    0xe070e090109050a0c080d090308040e181005070e100206130219030507031a091c030e070b040801050c030c0f0a022e11040609031b05041104141005030105100908 71
    0x103503034500b011000d40340c5c1c0348220710161150002c01da001d14030655002c0240ca600000d070398078040c501004c400c400d01015000034126844020310b40c01808041124603500c0700b5107400031410b0320709034030b019101e41c6586000501400b2141c0340c0b900c030141d020560591001c454aa43c491400d9140007182520070320151010310b04d11641004418001c0006162044078401c0d10702032061503440241d07018240090380d011809900c01d590302c500802418840120b5860b15240020381441103454140c42c00e0819808850250000039050100701c80a014042e485a15280c4451840c00c0074404031950348240c5070000600d2034003180001a00c0c0c8284034190b0407a046898140e191080300d103401d1001001c20b0a000000e901d0420480010602c0030243c8040300d1003074071940c20f03039440e41c0c03614800c65201e0886450f001242e01000318107643c5510600d10811100c0c26802d0302d0740d003082580040b0003950b0142d28492100c0d94540544c0313075404030071241964410340f0081000903810200342c540403d260003940c11 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 998583651 1250 998582401 998582413
    0x140f041a100503190605010c0b07120204090b0102010605150a11150703020306030609070303050a0302130504020d0e160302060403141f020c1b180c0c030d0b0907030e070e09010905 79
    0x1c1242c0c04000b5600618202c0d0010306001e0310008408121030985c800e00c0c1c0854040750110300032404c07820520b135004045052a1081005030510102203a100703402074403400350746010310742c15568248186c074060807065130120032000c0032105805071401507903014000c0021030b0a218070100014000c002000c01054030044241c2466400500079420445a030b40c0240300c1d4a00103145106c0018210b02100d0f01030302d41900e40084900e0440c084d43c01080c1801c445132004a0005d081c0d2034620050038100000d01d070008454010440c004d0400400009490148003600710a10140c0d66100448048070b0b44015645241600a5062410302c88800b01110f00d500200200c40042e09094000b0040c422699060f038480204403003489443c203501c00c22035500600707121410a1203808150000da00440c0c3d50314a0f5003407555414100e4555802100b09040c010740316010741c0300c2410007180e881d4000e43c042c24140010700c2120047c80d5582c94a100d980046c01c041408585007910a41c0700038011038001c0180c0d01 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 998584901 1250 998583651 998583679
    0x4021308100c141305090c1b0303041b0b030121120e0a050604080a0807032714010c391d15060a0f020c040c08060a140f041a 55
    0x1016611a00004144a450145121102c040480f40c400950300b114135003050810060280d5081c004180000340714040003102d003982d90303c10012240001a5004640c3c030b01d881e141c00710720b0300f4ac140c114850310100390f0000e01641c0c4010050303e0540d91554100103081c0c0d099210030140511141c000707080401040040980680e2100a034080d5503801d4400b111203560f0341c070522400d441240320b01364030360304901201c1340010012001004070074000d180559540e17202035001005d0005480940003865001c203803c0041520166072802d0741d4109080400c406045521040c80658508002e88001700920f05600c82041082030004030030010f01c0c0d000c41d00c0a884405070120703849a0504280744481d0303100000d1a21441d41107455a01c0d00140c40c0d18180542c621065600302103504001081d40566075610b1a261941c1c440c09820300b8085da5041d0250401d5801c9c0441d00516070005000c2400c0501d04101e01c0e11400d00c00020800180e80c0028845101b40310451000240303001280c0c00281201e00380 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 998586151 1250 998584901 998584933
    0x30d0e10140417100c090b09130b461215020c01091e03050f03070519030603020f0901060f0f090f1716080c0d020d0c0f0f050a08060604021308 63
    0x1140c4404c0608003008680082c0d1801d80d04540315116103480e2007000c014000e603c3c10180141710080018420128004d109080012040315003002000c0d00e4900400840703143e0a101806014490085500c20303000074030314410b454055100340103000f18007a801c0b650070b08019011130a000f42e0302d180350045448442c480c40550191141c0b03602541d140c120b10018003104c15180311012403040c0c0c1a220390349019003010b19980150001801036081c04800d1142d041400d89d0841c40318410030f110755000400328203620401401944050280c1c0c05220102c005110107a045841000800d182d07041c400002c20600320100d41c2c800480c1c204501034031078030000068180c064842004800a03900c03e50741b0580368001c542e003090302c0c68030580702d2035403101c1c503140510708048146c592810b0001d801d21074100b18548070703c500c1c2d910580c480c001d0b000c407580041140c018220100c41c06803000b15000c410301460041d0580d40d030000903003064400d5034002845002e00b05a2400710000340845e609581000085401c91 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 998587401 1250 998586151 998586163
    0x207140f120c01141201060f12111e07030e2b050a0c230402130e040c1404090b0105091519061b0f03030c0302040b07080306030d0e10140417 62
    0x550208410407508041d94204c24107a907110003140451450700e070320f800c00032688031289290079800d21002d01b02c0744841d0000b0340518869400b604140654800200d043d40d681d40020340030407100c45405001040001e43c0c44041c003103c01d041111068440210821601c44370ac0b151081e030f40e01e00150b140340314100301c0301003644441c4500501c044100c0700d54900b4a0341202c0740540d140030215121140304c200c1898150f0190880351000061003035116180c07411001c1a0b4801e650503513030400d48010030400011051220842d1340c0b010380d0b0510840105541d06003a020040c024244102940000110088080b5101001018000345062010103400661086604e42030203180001070081e01c1050351310304560790168141340e019070700000c0c44c20f490710102c0c001e06115001a080680811002070604200800703408104d0007201190307078a0409404252516103449034250a200c0c0040b54000e1075651280c5208080d0781d0360501c0f072540c4400903c14106482190400c9496a00766807051191030400628 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 998588651 1250 998587401 998587423
    0x1d010c0308064b0d080a030b040e0313080d200a080f0a0311030f181606020115171f14010e0403020606180106030902011b0809090112030207140f12 65
    0xf01074045030103142d858088044940d00540080146038604001011003000704008030091800040040c0c0d080005000c6c2c4168403410354041d400404c2c40051010b0001313001c00100b1404c0c0062160760010070700074200400f240c0040c032502954004404814800348403100009510140040e55060019480b04040c3c00441d04c000009140a52680500c2145000c8074021081441c180c819640d416607d41c1d100e080c60700480d0740901881d8000c00d0f03248081c02c0c148020746515000800e0341c2401c072203d00044660385d40403d038414020169210724090125130481200c04482c190f02275080a114401e01511400a103640315003409400082c821000309640d5000798401d900356a184d40320001082074000c0c21000c0d907004400201c3c01048064081c1e4884500c072403040c140203000b6020791410114084240c1829111082c1c00075414030f0340c1c1b9048203240d003d841b0400e404a07010446450087d52182c8e5806200e2482c2d500c1e02c4104480c0ea64181400301808000344898400080180f00e16260206410 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 998589901 1250 998588651 998588749
    0x20d1b0605040f1506030515130c2d0506070201050a090f03060c1e0806010e13050a0c0201180b0604050411030109120237060912050301061d010c030806 67
    0x4c11005810302d02a04c4100e80e00700c401024411001c2c5500c611010700a4480110800841041c0c0c00185c4410310100061940c0503444031000709400b500c0704400c615001c480079468158000340729680d0f80c103040d11707043e036020700c1c3c074079101d180c1000e090355120b240e9000700341c6850040700000100641ea8001100044a50756605007071007828007807004c078660445034807010030403101c00109294070820145142c820b000303100021103104a015003040711416514085907589550310b11a400340c090185481c9500700342420000d03a94641c0300c8500d002c0d000f801452140b0b84030307004a17041c030aa140c4001c070001c100500810000c01640340588071462030382303540c401502a001280118174135800c0900741c1450b12202c4850080d0000030350004e401c20043c070450f04141e4900500010a0031040310f203c0d20010358070b540da42c9504203200905400c03034510306900211410f00e501015a64800c48507a0f04641c0f5060010a45d10342d000050f00d44030700041c02e51400d1038007010318207100020541c00c00041c03110034 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 998591151 1250 998589901 998589923
    0x2613050109061209051f02041a0702030a0305160210020c0a0504180f021203040303080f0a05010f171c0518090103020303030606030c04030b130b070f020d1b0605040f 73
    0x4001900e003901148a900041070401e030f002144101141c0140c2d1100d8403074010b43d0a00e000031400c0c01c00c51b138030705c3c5581244598003040a1003603a501c103901c00941b643c103517541c40c01c0c0040c03036000960710014900010700b00310b0041140c200e05640a1012480d465001744944402600428002c3d071b50981d20741c0c2a44515039013200055141070520940088492103840805da1000c40c5d114003001501c2840201d8102c2d000030b601c1c000c9842c043c405000690b21a642d404107608213a0b4082000e21740240480d0b00007868407004121030800a0700746070446081d42c914441c0078242216039130038000640b4001c0d00d4080402401c40a481c0d104005015040d6041c20100e0380c072146405000b501030302408001c0d09540204040b500914140015540c008100741440385031944a5549045207075069680c52085520325a0a400300000100c8c600d500980616002e000702d0b00c0110025500c20f144040303034003800320380b02c080000c00001d0b801820340550400e405014504003850002458084080142c0d031400c110 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 998592401 1250 998591151 998591159
    0xd03032012150f0402070305090628030e0d031a10050408070b0403021c0c08030d0c08091c0e0402070507180c090f140604080f0c0f0f13092613 63
    0x20450580800e4016100303008607940c3d0030500000758170061094040c88001e204070080c1d40d80b40b08c000c0108001440c8009404050085141d862042d191148400c0c5030400200c0e600c0d01c140000e803904404c020307203400301d111a02c1010fa441040742886a07503800c4920401c890440d03e402000410448101c0801c80d22580c1d035a025082040c09075010080d0301800a0241d121240c05030409010021302903480d1100395540c0c0c0325521f01d1648480740040c0d400c0e0300d80c9640c840761038200b04041d1340901c4000141ca51040f00d071a00004030b4440c5101d64007807010000e4644001d8030340354141c41c0040c7d84502180c1e1615101d046803e4001c60700d9901500c41d905290301600d5261043d0079800c119503c05840c060041e007452459507103a0721101b611a001001030000054800007003203060481603040004c0c22852442d01c4c00d0060043e800b01c101c900410198203103032185d0300d60115801c0a000100400214145180742031460040d54418030b01103e10805413821201502d10003c0c4414490340090f070464a0352 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 998593651 1250 998592401 998592421
    0x30c161203060e15010c11030304122409050d0c1e0605041110020706030c0203070602070b06150412021306090903021005012115111305030c1e0d03032012 68
    0x614513500c1c00501075a011400007210194220b0040c80700409590038103031103403003111100e02c00040540b9400303103032034101c84044a05d1404402c0444054030a20124203161200c82d40c078000503071b00800b004441504002803044140b82c0070105c0001515a81020030281809005000b09403810380306551100c10035082c1b4034111403070200120294000e844140d00c0c20310160001c200217912903081d8041040742100245003840100f941502c02d501422450418405020307070048502c59840490600300001d004803c4080c403e900000d6048510701c6214a1884080c000740c40c00d0f610205250f07052690328010950003007050354030811241d404000580e42e0340d421041c10341c0d00010f0264030b88400c007410004500e0301288441e00044140010604011680c0700d5031132940840340107425101291002d0140d85002e000d880c00c8840121041001d0000690060300740303110b2164502d01c2260784202d800d08050180d04280b20600c0382e2000892904940e0201403640c0d13201540c0c0443e0554450006804401 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 998594901 1250 998593651 998593681
    0xa1403030f0103020915060f0c010f0c020c0f0111030307080105120c0f060f1209280b0619081203060a060305090d0f180807060e010203070305030c161203060e 70
    0x8001090710019074070b140c00b07001c10796034041d0400048100000c141081034503600024031440030b804c038246994496100000b403c41e504c080380042c2e15400e00313404c0745120360300140f242520103044651a211804200c0143c03428440100481501d0101108106c5600e40218510b412100192800a1a01284424180c03200010090075511001d80020300303c0c0d500b070609c05070205444010781d1610341014024100c00c043c60494500701260f000e000d1007601100c000c1c000107000039002401d80d080744c813199215162070f0030041c92103000e01d90b9140041e4409141d1802ea0f00206141c0040d900d02c50070a40c0404c8040d481100c0a50180d10940c1001880501c00d10500b0302c6400150040c040891800768100c84411a00810202b0040c41c1421681c0302c0140c8403228005003903940003881d5051500d04050180500020054190341040c404100801d0708841180d44c0306086d46101d680c0c480808240b595920045400540403075142890350210310f406034041400d4035680707122a0011b40c0d89481d5105000 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 998596151 1250 998594901 998594911
    0xf0906030c0501080c0f1c0528020c030d0e01060b0d05150d0209160e12030712050a021f020403061410052407020a0e1e07020102030c070b070c140a140303 68
    0x201040014521b4404518040c01c0082c480b003903558060700c51002c1c2070041e04e03003d85011a201c44606441051780d80d20b00340103c80e240b11000150b04003d8280d00c2e4548a000d104070b00702500b502e450100320141002e5001002138040b0140ca540c84043c05c089000c0184400c6669011203800c42c900560a4509581c0050340c10383d0041080e00a690b90740603041c20070030512681010720240b03000d400c401d646c8074801e43c20008811130007141c43c0c08660916550309040101c2d20803c1c03100410080291641c08610442d40c1d1061003600124182c4100249009100700d42c0058101e0340b41400c074004650b00c1c0c1d40305e1402203558516540070181c03070380c0800080d4100c00c1b014034060b207100040ca050801415015141480c001003000d55029502c121802c2509811645114014604600c07046040c02c540c0d0856040301c90752000310305500d0008081321461080c2c10010300482e1a00c40021880d07881041c0401c00e240d80404a8100510094a12aa25251007500b02e81e8000581c944058800d0000242c034411 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 998597401 1250 998596151 998596171
    0x150507080706020706090c290406080f09070e010b0a0f030e060604150b03090a1b0b0706110c07150306090b060304020d02030703081c060b1c050c040f0906030c050108 73
    0x8484150382c2d01009500104040701c40c2c80d22101e102c0003095482c00c9034001411080448039070899000040b0b06e54400322280040402c6041c4400c2c030050b607000b800c9661012080c0300c0810345460358951603143c000590b011108020b0b0120020032a0045840507041100e460b40768800841e01c0d140c0c05a0555440040c0f035030940c0c0c09030300018040d00d0150481014004051f403141c1085031112510b440302d07841201d5140700c0c1d07401a007844c1e0800050480030b540c086c0420742c401c40301c14141401060a4428800003030445a1500803046281d6892000c03240c0c1c0340c44140450b14250fa4403410105200e20b003140000219140c9100040c482d2028010180004e03402862140745036101e9007046500d52443c00141d070184070302e420102c00100140b0003840c00c3c29202041c607190402d0882c41c03205031003054101b03460a8400b4410070b986008400300c041c0c0c90f442c444001245554480445c003034140a00d501002c40e50003050400101301c441c684c40300050368000e184c02e44c00651160015200c130407040c2c1d590250 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 998598651 1250 998597401 998597407
    0x30c020a272309010b0901270203070306080d0c23030d0e0c031015151b020415030b0103140a08070f0c1a0316110703060b030a120915050708 62
    0x21242540e4841010020740b6010411110038002d0921400107003291850b007240e42d2442002d210b890310006060050032000980b0b02e440480c8400c00c40c50b42500c8110071030b825004000b040c0102d0090b001a409070010004464a01d080d08030000d1181c0e2600400f591105091190072074005200d011140c140201c14004614220003060780f1401012528541402d5000d441c139507003060343d02032040c0a140c602000c004130340040404540841da044580c050603408800f4248000c845820011640306803109130b40461441c0f001d800401c0c0540017401000ca1081200340340441004500700e2181e06a9000d007140340c40414940c41050b650340400840a0652441408031000050140140e072001d54440d1840100c416540c984c0e807004101c50b00c03002d240d01400803080002c0652500072082c5014660715200c80940c0542c4d0700d054a85440b40005001c050f2104500c07806501c0c10089201540d070321051242581500d100300070b14a0784035003e04407a1b80d14140c00c800141d0303c02c000351744030240c0200b44589 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 998599901 1250 998598651 998598719
    0x304030e121908040801020a090602010c020307033204061214010501020a0b090c151903060b0319140a0510120206030a0506030c1023070b060d050a0f030c020a 70
    0x85042d02c140458450004102c0441c403e142070020f090000041e403107d80300d007130404602a003034922000d0b03a80d085510074441e25004c42c0c0d00c5074580c0301c548a00141022120089402c010300701c41d460b00c01d00410074000800040c50b0350b01036074900511842c2402003190441d0407150202d490404c1c0b142e940141c2c40105e00c940030032140f15140ba0824843d204a4000c10000404910420b1443d58044603043d40410311aa0f03000002c1c1080e1610041407134200030050800030341c040d56002c0038181c1418686000c402160310843ea03486100201c0107038102c01070514000286401130041124015030315088070714006030000300c4489450501e6401032000c0d003107913580042180180750080001754984200b081c51082d644480c1c0c0340c40c0c0c42000aa0b240c800040c14003001e00100310040c212045915410000600480c03180d0000540220702116500f40c009228140145040d4420102905008090702d00708200b603089984203848034403d071400040d8075940c03c4030500c00d08480000d000203900e40305d0211 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 998601151 1250 998599901 998599933
    0x1030809030709110415050c0d05131a091f05070b13080304120207060e1309020402130801051b0306010e010311041211040f020717090d170304030e12 66
    0xc203116018044031101da69076070700f80e0300303440585007180a206800103040c054402103d06c85001d103030031414002d01c0c00700e0104400340c0c1e811169015004100011960345003290990390f14000070010b02c1d074000c505580d0780000c0065940140c1105100340e11042c0c01c40b010720041a19005103070081d0310f0b2142440741031703141e0204040000300b00c031094074807600042c1d0001d00700138080d41c095400307030b010388000103100b04001c1d1a000d116040030701401070040355407005aa403038190000d20a020040401c40e015188003282c040d000b0203158004020381c030040031a040303030150700c494410a440d840600c0c12000130540c54035648801d0b503200780040d034185400e6055502a4111686448e400500d461038140c2d2070104844132510140200c0b84002d510085274981e00c0e282c0038041503140020303021407520055541d602ca520369005c111108914000c40c0c1500b89603101000c02d0585500466500550540101c10802980c400c0b1000c802044030315103400c4042c101140e444210001c020014210080407540d88 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 998602401 1250 998601151 998601157
    0x1060507081605010e0d0e030a151d0f0c0103090f0212070b030c0d060e090a150609060b121302032806090309060813080405060711030d0f0e06040b03010308 69
    0x6441a41042145000320150720b01d050200368050000083c1c2c5900e00c09010342001940c1440d0f00400204030036001c0b265070b0105000f0102a8800c44c1c03406040d05200a080103010380d02040c0e042502c645000394515100880e0280030f150f4150f0613140201101401034003250740c00381000c0c100b0000005aa0014204103101d18000c6a4071411501c50307560317801c00e0031410340c004c031200550010049103071407020740d450280780040c1c101e821501c2c2d03c900e000c082d10307507440000c010085e02081f401224031080c0d81c03040e801035000e03007043c00d01481426240d10010000760f20001805000784440e130001201e102c007610125004590080c0134001c8007026181e1450000021422030a0304018000d03114009031440c8111045144a0b84581c00481c0ca0144050100c0304020812807502004510342c400003291107086a054500c210389503074130303910941484420403900c0c04a081d0540700d8401d03603007440364101d4000d003050310b00c2d80d0340c3c0380c6030804280c24480280500c0c841e072607043d4028030040c00020904806 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 998603651 1250 998602401 998602403
    0x30307080c090d02031f0e0105061c0219091e1a0108070e04060e0a0c02030a0503040f080405030105040606180c1b08070b01170c04060303020a0b091c020601140d0b01060507 76
    0x3819400c9182900020b0404100c8407071500c0c50102c00030440803a41a90107810501401d00c1f001300014600710000c5400d107074100e2082074840c024481404210f550b12200c1ca41c400300481e00c031002c216118a54080100170541400c03107000b01d0314421001844640c01b80c1640340040c0b170400030b1075852140054034089405807201043c8800300302c5501844d142c8d44121350040059800c140801d0030480b158904982c2590062400c5402c00c021200d411500003040700d412981c0710303522040714091400d1507003803030046801181d45942000c1c00d10062040a0300400103441803203003c2c01c1e42038125003030340c012a40b04086840202d084110311241c444034005880c801076028100c5185032003030350387d50710150311426046000100300c100d6500180c80f0007040804144103040e68200803250031900e003c3c0d81c0c0c000c10800180342d500f2a00020710601c8084c48200110f081c2c0c13602d02ea011082c0c05c0c0e40a5110102400740340517078400ba1030192410704d00468040c40d0590000d1180e04281d00f4018220341035404188 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 998604901 1250 998603651 998603659
    0x510050301090c031b0b03040b040302070e0c09090c0a09030b5113020c10180b0603070e2a040609031e0803131103070e0105030708030307080c09 64
    0x4001916031820300460b15001d1040d0703000c162441c02e61403c8185003e18480d00e141c001ca61500600050030f120f01100c1d0029000500c01c4d1090f070380c83c54100d00e891580d4001c07020b40480407041c001e01c004c0751406821b04460803140b9000035035881180c805640200300b204070018080260410125100317a4005400c1441c81d41c040b42240000807039140c81e250b608807203510560ac40d41005464512950a0350787da10030250340009001ca40c0c00003d0319440700d03091a0400c45034001066030700000308020b850103103664060f090110070140e03002600700c0b075204c0390180c4410740000000740041c54046989420f0f640b1604100c65180c950b00802c0d0a12a0703021805044030816404e0310400d4149007010b00300501c0243d403040e4038103041d031501003400d8080740c0f807402810b1500f80350a4001080041940d82c401100d220140c40116070b41030a0046103003907183c241d0980541a4045000c0c9aa500c03001d040c0c0e20103504842c030359940d030b4008560345e01c0210741365030000701c0400105801008900051040d140020 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 998606151 1250 998604901 998604931
    0x91303030603050f0303011d0405030d0c050d0f0c0306050102031920061504060501050c0d1b02060720030f0c0609010521041106180409050a050d0c031e0f0305 70
    0x95500b44c41c119810000900ca07a10220042004180d413a241c2c00341c0c000416400110303400c140e80d0ba59500d004280a1120003070315424001c803402d00c1a000c0d1004510554418070030907102c103100c00c0041040500c0300d00064204003020555500000071036019a00802c1c0c0400d1001d01d8290866091080041e0000420340070295000e0041040141034051101c088201588140034400c00045800307583c484d605219050180001400000c142070280780f0050600c440804919144a030340030304030200c02035003c1c2020030184140007038984a0401c00b1103480b00800325081c8101010341e00d1062015200c2a50301040d00743c02542001006001d54180c10304002d81044848001ca0780a891040b0309071385e50a00640400c01440342c040c413201c0030880d098805503d0900310005020407003030101040c03406151070b00c00542c10001d00304032452a840d000419141d80d00b07440d03880101100705600702940010261103a2070b11507403080c03844102c0e910440c0c1b1104e41044403600d069000e040000c0034050304814803 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 998607401 1250 998606151 998606153
    0x615050904182301050709030201170604060909140c19210209040609020310050c09120f01020a050703170f2202120a0b010b040b1c150e0103051b091303030603 70
    0x48180070f00640850116100300e8400800103908541c0c0040000b4200710100d501000541d8010221625a8403000224400c80d40d6031000b0078090000769201141881c50320644109005045445210152480081d20004000c0000f040708900840f0600c24500011101c20003070b070f01031a0202d03c0c00d180c0b018180c0c22418665000a444600110ba0a844442e1201001c8045103030034000b43c07207080002017040009041c03070700c0c02d41114040d106c0c00368003c42c1d851840031a469801c025030001d41440c5402959a030481a800400f142c1040d101103000c0b61004001003a840d0b00200e00d644134011440303088a0301c2d0f03168003060404908119070000c401400c2c17805031015865544400d190b11000000808107800c0c9480c2c00c41010b00c05910078400c100c024402031201000312030446610114001c6e540d21840b203122185001001b8005456407010081240025500c040c001854100d03400307201600e0120300900200c1410000c5001e00ea640440c8410014800b840b0054000c0380c054003074a8002180f60712 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 998608651 1250 998607401 998607413
    0x5010f02070b010503150f0a0b15040326070302060f0601180f140906180c0f030a1a06070507061101060807080c0a05010f0f0f031b09030204061505090418 68
    0x20500d02610010520340052044e8241003210360041c08031130f5407a560514100040355100c20028054a04989c0c881804480036569a400c070321305c184010055940c1c0325602c0ca0610890340310303660341c0d40204040209064080006100ba1444103400d5009041d580c0c0d68801c4030780f00440b005040e0381c1030001d00301107510004240d90546002e40740b07072210000010b080c404200e03954110312060902c50700707030642000540d0301c034a0b141040d0092400b0740c911f01512802000c41c0c1c02c0c000c11441055a50010040000c104240d0f0031030b20b409050405010805040700050016521030340c1d5014180754020340d8104030584c070071646031002c804120300001c1d0700c5448035002c0d0f042c0790869001c08407a03442001cac1810903241900180c0010042401c1c00711b60000b00010190044075006112024095416241c1000c40e009421522144d5800c00b00c842c000500072030080c110350400d0005a010310301d418408125212420342224400c0d00303076202c2c0707800d05200e181040041c00d0f040744022140e1014079490400a84 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 998609901 1250 998608651 998608657
    0x6240d020712030e0c0616020f01020a0b0a06030b06040615080a0f09030c021e0306160905180702070605032217040f03140d120207030212030c0a021603030e0105030405010f02 77
    0x403543c011610181581400e850180c183e2401e82c89104204004e440f15100349000c0d4152590644464070a806001c0050b4106800000301816030b24083d0100101c10419a006406032842103022502c291100d800b404225502030007052a50450094622103ca00480c0b0407940211006c0d008603c10350782d840508151041d0300400c030003054041d807a060031850300040000343d5410f00e0306d0300c032600380504000a03620f800c0a4116564100c40144450700648913421510281038007510801141c4281030101009007130403120440140618400803e49510170320440303014154030700c041381002088105249545042c5601100c1c03500200c0b4684c0340015200380648014003c02030040600c0340745041c40360554404074400741d0241c0103820400f5145030444413042401201071001030701c6904c1481c0c140c0c5131205945840750499808020803030111000c80041503036000c66400d84020480c1c1d440180040c00351408003c1c0880c81415074001c295101d90080d59205004000100c1c601440c1c60010080364 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 998611151 1250 998609901 998609933
    0x20a15031406060721050702091023150c1f0b0102071205060f150901080309100206010f171204060c060c0804021f0215100e06240d0207 60
    0x80d140d03011032030180161407080394400b5098441a03d000c01c0740d607442c13400c1c1c3c0c01c0960403442d80300110b0f2110b0a491181040c1c4843e164003800040190500c050b071814510041e22071b010b5030311903007546811030f1700c83d070700340b909041002910424807071450104141083c0c10465100d0385c94070a265094810703247d0400500d002030300e8024001040075545000904181182c3c208003444030f0445c0050b80014400144d040d48080c2d0180c1036082911a116811070136000550105c1c0d0018640001241d20403020008000040e0103c600c0502c0c038101d02400c0c1d803103031400d218503020011031000c1002101d00001c02c2c00400d43c0d0300c1003a29002d04107030b51440c106400c90b4100c6d0300082c150300422010041c0500c20020b0200c4182014201482d15500091580781c110685058042e005d01910300c01500801484001e00066003008843d40341001c0744441720b4200b44030300c4882264010105606043c94010303941000d011156201d46051040b60480c4194050251481499401c000c1c0071b02007001c4d05c0c0305084030 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 998612401 1250 998611151 998611157
    0x20c070f0501080907080601050103050a0209030a060501090509010908030109020a020304030c060e01170f13050309030111070506180a0305180a060c030f050a210609090f050d140a0c020a15 83
    0x40d810100010220040101982e1036640410001e1108003000568a03044600c04d1a000c41e00c3d40e03c0c40a0031002e0b02583c0b2005415200303420900c0c1c104078245d00918140d480d070344c01c20001c0342e880c484001c0c26280319141c00f4224400400040c003c1190a40042140c09403e00459207403da0380c0c0c0d90b4488000d0715030301100005042440039842c0e50780c0190f980ba900f4803401d002c0d409078204401c000030a0301c005020080c1260170221400200082481928540c4000500030020b034110b00241440b140d000001c111202c1c002c6c0b0b00001c03581ba84064040ca40399006400500a007812650142c41c07680c880710f41c20740c0a82603041d060f4416a64000ca000141503190b595950100d81460050981c3c00500001c9003400418001d400c08a9880022403000700c013104803c0320303402401e10b0300e580101450f40207000001d042013540001d0080b10300d41a00800d208400320740144041c240c0c210f8203c02e03c443c111244007000c015000140b407281050064035030000305014151036454141841c00302e4416541004 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 998613651 1250 998612401 998612429
    0xc040308120f0609010f2108040f030516062106090c050c010e0f37030224010506040e06030f0a030e0a17030301062a080909060418080d020c07 63
    0x3001600c02c4280d000700040e51460020b5050154403a040d80d038078000e0808100b691020031280c2d2603404103a0b14403e4214018640d00c98a9102d5111088218001038501e4441c050300301c40c1c01400744a9080484513141e8543c00d0180b80c05810810000d0002c00120030543c0741d48021809401504c80d198001c1c6440d19107507903528040d420142565998112224030703030403260040107001c5000c14803c003144041c0e0b00001803400780700c0410320002da03002d11518210303103500182020540c00052400c0741000145090502c070b1602502e003420300109004494204400780000c0003807012401c1c6064204800030142d07005c404011500da0301e440300c00340701680000c40310090031140307060402800010b80a421130820404000044484d520310040c85404204442d06500c0c01c9980e004000c2409000d056452055258002c1d04180040703401c48114144944003a90101b1198501880b55049010f41c8000800004003941c175050038030340000200c802026000c0202c1900e001c010b01456024224221400e51 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 998614901 1250 998613651 998613661
    0x3021b100b0112090201080c031e040821010f05040b010509100e1e0d0f03300b01111c200f070801270804033201020a0f080c04030812 59
    0x2c5401403800c81d10a4003468042404d0260342c5c8090302503409000d08200d5030b9039850b80b424503c1304040c0f0507203504c1c0d01c1384000140410051303148001c048000440d10901c80c0040d07006003002c080340d420320a03081211001c01c01080b00342016000341c44205c0e41414100d090410403404509040304070400c40c0001138001c42c0100151078900400c1d00807440c21100212a03101c0e110214004552520010742056408100f0004240c4034000707441c070b000c90780840d481c0d92200062440e0126481c40007184545400d0a1441115503c619000004820080c2c000d00701291065504400c003921002854100480d00c0d070740b80042c842104440e02018241c03402001d410340d1410f1450f0802300e0b00e401080869061040c034105088030070200801c1c01c85202413154110b0801c0ca00b500c441d03c901e61004125416182410b540762000034a11088084900190196a080c8503501c0c0d080b880b07000542008902600ba81010507481509540e5004038600445441d0649036103443c42903400c1031161094540c9030f0301c1004 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 998616151 1250 998614901 998614907
    0xd0806010903080a081e090a14030f1c06150e060d1b110705041808030a180f0233090120062707091e06090518070b0a03021b100b01 58
    0x180d124000746c24207042d4100150356070f440b4072050b6405443e18610007441c0409400600407a000c24010800b030a948040c020000b5043d00f06c00d03000059068039020b800102d103900350482000c2e001046d51001049445102084440e0708100b160551a9507240c44503c034540545504100c441c18035140d000b160001e800100349001d20a420450080b4100300c03000d424861511066890700b03600140460301c9944000d50480144500003030014548c0c180d6403250140f08404401001650080e85c0c50080018041070300307007600e5070f40b100c1170540d204119000710b40c1d05d100300007030076101a051408240002d8031002e21040700c401c07980c0a0405030015810304c00750316440d248000703c40e00300d01e00401d040850b0340410f0342c4411183c4103d01c03420b9150301c015010010a0003410307001c0440a5800c1000c1c1c2d4403901100010031080340c1e80d00e0708881000d0f5452101500082100c11941d105426603c4d060b41e03010110701942107a0036241d8501c1e1511044400e0580a100c0e100280700c52030000100060504001 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 998617401 1250 998616151 998616181
    0x9071a0906090402071b0b0d0b0904030804030e0102010e03030c0301080f06100905060d0803040c080601061716090b0c030a030c032306010e30030901020d0806010903080a08 76
    0x16844014081004240039214001a500c00c0c030b10450780182c03917089900b00460545004c0e01c0302610440d0401d400704d1114501710140501d0490b500303041182e01401003d0013140c1100b81e8014010540e071000080002e442800100c0f410740061001090201000038803600d581c106441c1e00001b03001c0480180701107803041002200042c0d01c0c078000c1245080c0040350085030480740c0250203031075450b480000c40684410001400080c2d004088a58919013810000c051100e03501030080390340a5140002030203403290b41441c44903110f0310000c80113602c84d542e9500a0700d0850130110140015888002140c01400c0301410341c6400e242c01440d40c58000e00001821280c1c800211030606161803194841142084006152110740c100d88001c06e031501ca0043c0c0d00140c02c80740312a8419106000c1807141c24801e80c5004082c2903035400001800b280c03040d01360b200d00600d200c0a005a22031010004058843d0150715088481030522000329500c81c2c445210130f900c02c150480218001d001485907a080840d66 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 998618651 1250 998617401 998617439
    0xf060b310f06121506031d2806060312020601030c061715030c150d0510080607050a0c121d090103050c0d030504050301020a0306290409020a0c0203060907 68
    0x990304105003498018400d06401e401944100203100102281c0002a40d2014910898104051150942e40c03400180644130405414101e4810950000c2c0310501c005a10340c1e0308100529151030740342c504400310400b100101d800340c40e45c6407680e0700007012501080000f11030074a180c4c083c291030b42c11414002101195544200304116030054503541c80b900801000d030700a0040d014080c003424500e40020b1a00c0b040031045640a9041a031056440c58a00010004180603038018001d9070341d9000401c604402c04d105240b0342c2d4001d5800250301c0781c031130710040890b144182070540d491110f075107411382c5080e4802c0808011a0001c10070000c04903100000d50203520003140c42070815811640d07901d8540c42d6150200c1d000c1da05000300f040800d1701a10944c3c018020240085454801200b0000d0140207588145050f040c0301c0010b80d589000040c2600e081081c2040c0c9861515107800d0401c1c000358810f802a1081181400c012801139038103200d00c6000c1c044400041c030305641040086040b1049441d0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 998619901 1250 998618651 998618737
    0x172703070503030406020901021f0c020706050315060a09090203010b0a0815030a06200304050c0f06361201090201030b0a0f030f140616170402090402040f060b 70
    0x500001d10002c212540181d000e080035880d602d03a100180c0c98411283d011126020f83c420809200e84216408000300086603821242d01f156501c0d819212440306030386e2010100c40504401c911400d0900052020621600d01400001c0c0e440300500308a810a80100c2103885c40040c60800e0558801405c039001940407800211a00c10540001d5079491103400017466642c80301c114000e424a0b008042c0b13040b1044450242d506d1a0900c0c00c00e80b50070210700f440d0311601c42d130300441e54030307041c48030980340110010020001ea90b205103070000340807600c10401345514032010a0542030f984414072421802c9981500206540400e0310000d03081c0da916419003406044030310800c0004540d0700428004aa4215040440d9004a4280640140f0030f200c8007049900c9000140b09840d040400a50301d81005595007000c00d8000402003035860206641c003951103101d20010a015182c213900c8802021442c510000341c80703035201c072200034541000110820707000031074a41400c805a034440d43c54074845124 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 998621151 1250 998619901 998619907
    0x31703010506120a060b0a111c020a060b0f150d0b011d3a29151f0504090501050405010e0414030c070f2301021b01172703 54
    0xc1182c074083d4100320603032910f9110200b400e5514503440440581868400140d8a00c12801c0c09400d0000c42c40100c1c0091080c0a1075050000d40c04460b281d801440b42d0261060703c100d80c44540c0544900f21500780d1000980181d24120741d500c025890b501c1c9a11141c9548550810125000701e602c20b541e01c9041c4041c260340e250204c5032030340071404035200483d00b225000b180003144100300ca90742c9034107100c0c080007039000046050422050400d803511446106240b8541c0d140c6c240c0c10046d03c0c5102040020040010507040301190050700c0c03440b8405002003d0fa00c094502c540001004143e030500406c800007002e020100081c0107280c090a800e480070300149d4500703c8120b007144401040507081c41e40e00d03074100000d00018011205000010001c94000f551075045c01d00c02000c16210308032101003130407005d03c9101e01d2020401d114020580141034012803003034410040440d2808141c0c1003142e40c6803950f81104205400034040d40806c540c003003000d0942c4100400c440f07030b030210450300c5610034 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 998622401 1250 998621151 998621159
    0x1031a04021302130b130e0702160608190c031e09050a03210e07260a290c0405030741031506030d0903030903081312080403170301 58
    0x2800e21014002031080c2c0c010b96511103032401c24100b0941e60084a05241c00265803071356005c81c8000c0d00141e41d000c2500f41c4c01c90f110f0f00c02c10b0342e480068100206001e800c4003c100041c40c050042a68003440007048900d40c00b81458071403040750317025040b4002107a560014403909200044400041c01c2d24500d0400400d45662607503960b1b601c10410040030081d10138640c1030580707060b00181c83e541b403524100340460051841034644500c414090011030404014122200b2411451039660003070b44d40c0d003d0b0008072040c1d00c460345001044403104201c00320794070070401d0191449085900c6180c0b84000d11380c90764100300415041c01c2c40c581c0070385c0d55240b005501440340d940d5103072000c417a6101020810081200c146022102c0d50810024a9041c010410502c102035003e401c43c500c200342c11000d807000c164583d141555040914040a000102c4884091001891410040103254024842019829680c503080d54426003c10803c031403c3d400801d080040110400c0c80a07031045d0100d4a060441d814 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 998623651 1250 998622401 998622409
    0xf02030a090b090109050303040e0613141801020c19020a080d0f030c0e1002030a39050a05010e030717040e0601030b12100e07050406060503062107030b01031a0402 72
    0x107a0300800d442e9502c0029810030aa004007001d50080c100030782a41d440303541d1254494100780302112401d00400c800540c0c8002c1c40000d105500020000300008d403000c2d16040221380910040141140c510740d800c00801001c135030100f041c2040c82440007501800c1c1c9845206005003070f4681d501104039030f4001c584240380190028010b0080710990300e00003500920001003119030881200280350003145401c008082e20b07038048020081c440294940c10709040c0d052080305402580c4e034210743e101c50304070040d4100360110002e10761541800f43d0f00b00e85002c44541c58190840742c546540412543c4001813400c10441640b0681c120790203194a5107080034501034042c0399420b40200100c1c1050742d2050500703140d80d6440f001d111592048001c50f1001d1000da44090000c1c121000d4011013403082c80000a85894207004100994015070760703c42c1503403500c90a12580340302242414001d0040700050010803242080310b000218010450000c580d459030030f0810b011402c0b003002501c0000390104000c00f50315 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 998624901 1250 998623651 998623667
    0xd1a030601030b040c23011b0507050d0f06020c030301030312050403020606060d150e1506030615090a081504110d0203060f070917030706060e190902010e130c0f02030a 74
    0x1d002550100359503502e107000e05080d038a940107034408615421071850b4450b031800403c4070100c1c080e00c0c8c840004903102e4821090000d600c1001340340341e008420034080c0703003017041c440501248204c500414088990380caa006030b800452025845a1001c401082450703884808000382141a00702046107040540b8003c0d01d0301401440a0b002e818000780782200b4044603400307051000707030104060000c00d0b01c1e10341849103050241c0d601141c040541481c0034062600400700c0e1b002d5200100002480c1d02e10070300c0e5515030780041e5032169200d4110a0009440301d810f01c8000d412800c0302a460386140b03031a00c1c12007540042070b2810f40c06000040440300042c0c42c0002c006d03030450700c0781c40d82c4501c0c0e550740b01040740d01105035000392003500100010301f02c0700b000010103008024403582d030034040c0d10345370441004901c5c41241c0d154000d4041c902500040c05c015807200d036010780185002d440050b030407000301c0d0444400301d0308410b8460742e80c50b803268440da0000b00d030b042e0200765101441c0740c0001201c00618602d = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 998626151 1250 998624901 998624903
    0x7080703021225030c05010c200123040203120c0c01140720190b1209120d1e0525050405030a0201050d0603020306010b0307180b04061d0603010b0d1a03060103 70
    0x103c103440c54000d050090030040c2c0c1d1194058024003a48944003002402d03001c0c00341d84804455036112000c0c880c904107008804040403c4c520360302859620444031207650340050010390f0140500a10f140f541b11014000303200030f028104c001e1003021004000140b00340d100130340e81260b2203c148072a03400940c6511140e4402413455106007101a0f24000080e600c40d03158040040300c4904c0c20300082d50040190282c40204402c0c41550b0381035a403c2034540d00e4854801c85005200001c0000c0007114089074000a081e038098203184e5100c45040690350226401a61140441d1004524190348000c9a42c0b08030052400342c50224145840c2001013a658024100e009060100102d8010081240d65000c4001160000c0c2110082d5039501c4280815a1050790003100280880d00002c4506083c4442c80041700e000b02d550750700e0281f07440070845006910f1402461a01c501403882c0403140d442d5000385000c0d00300c0100c4650360350700b5022803c0485404010342c000c5410560b134078004958001c1142c1d4112 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 998627401 1250 998626151 998626207
    0xa0207080a11190902160308060307050306070807090e180c010e0907050706022106010f030902010507171603030c02070609050a122a0e06030307150f11070807030212 73
    0x500b52900c02d450f036030320060b04110b01c02d510100d02c008005100c4d01042240b039002c1c0e102c501498451000303160b00c42169004d45134169001901040c952403054661582c00441c034509205001d445606c0c2c10401030b000c2d1910718410b5a9170f0800700d0a0031082c80005103d003002d08041201e55141000b20b06400d0000f0480c1051260102d8030b01d0a12107035070120b81c1680100e0b05815039101d808085480885030a03a44180010201c1c42d4010207540240b003141c64040c0c058540509210150b90b901c40c0001860103e00387c264001e2088100100d04003841c206050304c44d86000c00c0320b5000c884000e1510340703598060002c10542610410164807010401002c1d1021444c00710122812410580b21142044010303810b100f500704402c038007000301141e045082e100c10024500302615a5410140e0b28003808102a051032030120300840500c1483c0d008143d42001780401180204110440c0d04c072a4002810a40703100b540042d801007007503070503c8401c00d2060b4060a41d401c0803091440403c402c24100c54038200d03 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 998628651 1250 998627401 998627419
    0x307170a060305010e0318030a03080103020609210708120a09151e081506070506130c0b0c030d0506100c03051c05010b130e1303180306110a0207080a11 67
    0x558112500418080d43c1c001000348100d0703084210700d81e901da001118609481149540c11409460081200348070300303070580c0c5c413203405900310780801400340d002c5520503901c02900c0310282600202c4444075a51b070444480a030030414030b00303c095810078006070b5180840120800a504046030000122000da5194070040080e02c0400b800960b05802c1071100b44504030707141c0003000e103a2a40030258501c40c00982e5040f4407200d210800b0700011f0302910400400303a410090020b292400355080004619018000c4401c0c00b580c1e41070703840c205900080804840d40c000090f24400d104440c0161900484299141c3e83c05165080004103403c88034407001b02013240c0010191103500900c46409072035074000d5402c04c11541d480700c03c0e51181d8043d401520768119500c00010f0381d4801c000e8058420702a0361114115043e4031f54003250b92401c80310f03501c10341c0e0592003800b10128500e40b080b2000b4014490489564015828004c0e2401042d98802c1000c1d80c0510204d400069001c4000c030484c040035500440 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 998629901 1250 998628651 998628661
    0x40204020f0408160501081e06180a091b030305120a0b061602040f0908190c05010e0105090f07180f022b1103060603040201050a1202120f0705030717 66
    0x107072090300184881141c010602261075000810b000342d00e604680003032450039540301c1c01500c0145044882c4501c1008008900d210301c08460380032948004018001d00d44c041c2c403c04010300019055455071100341c2d4481070681000044c0e220100c480d2014240b0b502c00503d942c1d8010540d224801178101903a00c2000801e64120052b0032025103024000c0078951980b8284850103492250410b09034492401c2010901901c1d1181c03107128126a04100c132a03142129071010503030b0012545900004020040c0080c001043c4203100c1c1e4029440a90000709090a0031020b080c41c00420060b0701d0f8054100360000c103c0c4010b114207492441e1020035002c918103602c925020001d000b400c1d2918002c000034002c40f00f41100200d550407811440200410441046030f41500450000701c80c0d05401500c100007142c00340d8001e00140c84481e0592600c00380c1c4c540e004114005070707002200342d220400b82440c03c0c0301403031203d031500581c48503076071070228150b26011600900f07254861000640711020140458 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 998631151 1250 998629901 998629909
    0x11070e040b060414060907030b01110a08130b1c0b040902030303040f060e0a0201050412020f150304020a06032a090b040303021e0c030d030b0120060603101b080402 72
    0x1000408100000001a1615062044810100700d44103449145409002c0280c0815400300f540100c8000c0c1902030b413543d44890640043c000e80c1c40060600c440600d150034094000c0000a0640e44150310882d150f09035130042c40b0400f212034205404801c01401445c0c510610089071f090108100c01c0007082c00f00031040860000d041150002c1d425010010400003440500350b650034116110300000c1120101012459071201440803009001910404c420450503000031200074202d0300040c5246550064240052000c0308240014021700344080208801d628020b0441c400428903418103000320604000701c03591001030f0b0311005a004480308035410680f1b104502c000080c080000b90706586039103074140a076507682e104044130510010307162801180100410350350740020f4040c00030000d2901e0024260003a00c03003640c10604012035510f82d80c48480c00c00301d06204046240000d04200d051440c103150030030030390703801031101e1905051904100c0c64000740100c114042c0c2e031400130301b2602c0e02d05c005 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 998632401 1250 998631151 998631163
    0xa090804050a0e0601080f06031e0118141207020a27020c0f070f06082811030103030f0e06090d0813030501061d090d120f050a061e0302060a11 63
    0x141da0801101030001c0b400031041c65805000342000d0700c500d051503a80184102011004032031aa0309504001c001300174290240c0d6041400382c0640703002084542e094040c080c0980f4218409607a01801659020756511003440020807400e13400c2c0e4424944a0b542d0003241c0034051511400600c10b40f0200304810140d9449031052208a200000395610100c2d080d8260303682e101000103080e10300450400050b2000004040c200325461519003090030355852540c8015481145180b0521900d000c2e0500040d90441c405e55108000c20002c10f43c480d410340c02c00034244010042100c5c1400541020780045940c0c0400f5500402811180000c01222270718102d0040c2c0640610345c50a150b400780d010080141c190001d000f070b601c000b1480754100e088140d5042c0d80000603141c50181d42c01c019900c1c3e0005100d03454000480c001e1800c0400c200c248502100704a03a41214a220102d40c1d03400c00b44010b0541c404c1440384404952030400406003540c00294880c4204101402440040510381c40600818000 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 998633651 1250 998632401 998632409
    0x2f1c020d20150408091e18130807030917030a0207210b090f010b011d010c1a0405070609050102010213090c03090807030804030f080f0402090907150e04060e0408030a090804 76
    0x41611800c052500e00741d00d030001040349100e540341b07000c203140c030b80f007450861040144002c240b03005100680d0000c0ca6006000303450240b481003190303159004956090010607049219669003d0050300d40540328400754061030720f40d03001c3d0f002044103111441c0c0c00038108065600502c60946480d099031070342d081e51000098018001c10403a810000085004207100d40040c6502009120300d060340343c011205070782a1410b0074140d0019120f00c3e00b055101d030350075011040c07280c100d01140307100c0f43c03120941d5140c0444085480d179001e20010b100a40d0300c80705920003044203000039801c1c58540c1d4240300004ca0301d40580d000540d60703914020a12482504100000da420080b00c3d03548007402e040080c041541228140c1c045502c9480b02d40384a88905155032180c1c141d039031082100d880b6a402c00c4110100030704201c495200e8494042980f58150050544807100f42d01c0b108600b0380707500306110a07a206603004890101c0240c080002041580044a80c0b00d4080b220016120011349000c43c450f00071504 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 998634901 1250 998633651 998633683
    0xf10021c02070f0801050c041e0902070f0501060501080c040e2205030a090e010e01120f02030d0315090e030301062102030a020a08180c012f1c020d20 66
    0x2100034021500400e00c8001e440a41c03406100d6a612800340c02c3c00e0360403d0360344d640c0d8138204110400183d00c81619100c0e40c6440f030b44001c036500742c0d01e400d040300b643c0102009a0301200110307104c8080000920607d002044282045001c900d050b40c09501d00b0b000b144a01c400840c10380380010141d80c8100c80c5201002c400700281100b040d1a0b04155076243c200c8240d06c000f142040b000803500200300c600c00c904860210000c00002c0c1c0c20500318411280c2c6c140360880c1d043c2460a103000041e541840500440e18469030002640f4030660a028410300d501c0d07102050307983c981942c80d620b001d000300807170341901c0312400d1603980f03aa45500510307000c1c2c0008404164030361012062200c4255140c009000003030480c0d568103003d40751229900d030600300103100041140d0086c69a601294051000401841d0250850001307400c0d25499240d20b000b815240d0f00061b401c00200200c102a850266029101d41e038401010100b0380c210000c1c09542c00c1080d180240201c0030000040501c4c00c10003200390458909c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 998636151 1250 998634901 998634943
    0x610031508060408040e0a0e070306091532131209090608150106051206090c0405030304030b04021c030801120f080c07030201121e0f4203020f1002 65
    0x4c14907200d036030028010074036540c12090100c0c140c00c070140030b00e00320030380300c50050000d49145d90341c1e0600504604108580c40500c4408201201d5401d114103507900454010402d0802907a030302005480791000310551640d0125000c2c45036002010b4030307a201c01944484000022101d03040d055034525515030004045606010021469402c003040c1004104c8080a03061040e0b621640d042e5580c1c026001000038113000e9200007840307403402c00e0030701d60003a1054217028905629980880d0035a80316800550350f00c008042840110308011415801c1c0c007060000181d000111036030002c00c1c811040c0b00d550000b400c0c14141800340101c0300f0315980100d80c01003600340c0d141804000140c842825100590103c0c00d0560402400c030054055121044141c40844c400d07440b00449a50080c400460008841030380e40850200f071071203106a4640e4220700355140e40043d08441c0c04140d161203181c110705c44a4452075030807c0183c50350126400c111004884160903400100005c80c070340b507008404041070115503 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 998637401 1250 998636151 998636153
    0xb040b1b0f0708010c080613050714160b060a050604090504210f0e152a121806090f010c1b0b070204060803090109180e0307030306080c040506100315080604 69
    0x1840b4040f20790801c024001e11a034030b40291038100084444940000c00003c480035602c03505d5100c036500110074200000f032843c000c03004000342c3e0401d100000c8141541454901401f04907413815034132002c2224240390310b81c01d05001c214940601e11a00d2852a258008103080000c0405189002101c1d0140c0c202c40b26004500280f540e08040a40400300d203a201e2180c8403424140729005c5490b058010242c0b9003804080c0012070031302c0031020703501241c12102c0d0300d02d0b0311107040c84144100354900a909450398210f030780c0f003690301c20a840030381d1045100704030910168907540300081d4444024249507a0b8407000341000c1200c481201411140b401c0c1114003c9084000c004c00780c11900e000381c4080007040d0700c41c0e00455581c480e1450381c40c08120b910300704001d01e074107544500344642004000480d54440755407503e0703d0742c0c010078001c90109132620740500440104211022040c00304803001e2010342081c0c00421a02051000325504064503031010210442900155070300400d440030031510300e0320302 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 998638651 1250 998637401 998637403
    0xf17040302150c0d2a0c3203030a0c0f020a02010f1d0310020c1e060f0c040b04080a110f010f030506060403150c0e1503060d15050a0f050901060b040b1b0f 68
    0x34500d0145c44030043c1c0c81c603407400d0720170801100c01552000491070200d1842503001c40000b50a10619000a200e0496415000c010300103503003d410a0000481d0400c0000c0010f807848103407560344021903203c50b104c01e000d82e92059a0840681480c1006030400c4084012188070013a61101ca541511901c002d80000f41d426034002c04040300700c0c1c0c1c144d603940100c0303107410802100307031000c0340e01d0603403003200403c103155280000b55400170300700c941d014941541c0c2d80e004042500075500600c1103404c100e00ca402031085041e401d1511400440f129801d4080c1d072000030700b000b250b0100700400c140c1c0d01c00000e0b01544400080700c0156400007007114040121402820103800b502224100080c0070500c03821003130400b102c203201400414400c0c82d0070b60741d800c0c0500c844001110304c280c038000a4041c65018003000c5205d1580540b401c2075000c03402002827800f2000f40d510281917109540c4c9454001c01564441d6400e41c5d05540f81040f1781503075291450350089401c0d1b00c2c0f200341b110f50301461030104d0510324 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 998639901 1250 998638651 998638691
    0x7080c0a150b0607021002010b03150907050405072f0106030b1f0803030106081e090f07142404030b25030203040201051606060807060f17040302150c0d 67
    0x21041108161842421840005840c825042c683e08142c05000141c01441d1050070340018026074800003074160700c50b000284c1380220300c2c010000103428407410301030011018410030019180549040c481e03810034100c010501c0c2200d09a00325101c0c45001501052a200e0b020744c0854001500280b2080740c5a0810b074002d4202922210001d11290f41e10186004800300100c044500310740c00345041d41e280000542c0c100c0350051035146044e1114285c106280c030412070f094050282c0000402d594030805507024a03040054000030050005400410b401c2c1c0c2e40c0300f0007030b5091079140113a2103100d04a1504003445000b60340005201c015032108120600c6905206170840c51002038214140c040480c3c0142c0c2248000e80b8041e000980800948181c00c2c221141c043c400d600c01c0754001645603880070742906202d0703903801000004416000c0204480d91200d0b040300343d5114031800052605081e40c010303660f100e8191051600c21598000101c41d485030205555401820380b1040c410064024200d0704824 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 998641151 1250 998639901 998639903
    0x405040302150a060618141509130603060b0f0f061b102004030f03110f0106080c0a05190510090906090212130b1506210402091303020303040303020f07080c0a 70
    0x11b03202e0a0111804000a003825048408403892030701c1c890a10800d02952a002c1564010742002c200040005529851002d4500343c0c81d41d00000307041421842c02034140c44c0c640407002d03c21030094441441d29070b12581e1855602c0301c200c0307045a030703600d4052440b46218814208001d40c0c1c05140e0301302c1011210781d003010b80c40400826110b00188615650100280100d000160102c0752000e10500024040c0d118500140050000c0720920805040740500b542c040b5041000c20750070288084e2040e060241c050005400111040114000d00d0314031940900c0091203041e10030030911114521a0b40121071000c05040742c1c0d507050007013a0b2540070f404043c2d844010342c441c0d0b1040d140009038040c00d0400d19800801d0344140780c8112a01d4500f0200e1003102c14040300c40d03010004201403e07504440c03000300c543c6042e00610106041c03815004020b00301c48020030805051b0542529080041d50100450f0713070155242c03d005803a200f80074000032642c011610000d0500c003000580d41c60f880000142081e1507 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 998642401 1250 998641151 998641157
    0x10020111030f1006020706021f0209092e0503030f07031e050406180b0715020d0903030501031b03080f0d09020a080307050601241412040f031e05090405040302150a0606 74
    0x1096941004a945140600c5a20016001500c4034011203544554400c52031589c80d00c00b50400310348000040e5501d000b0340d0f807180c141004682c031069144220165052256a992030a0542c07485d250200780c9a10035808000c0c40c2440000315101054014440d011442c500c220749003500d04003800001e00650f2050250a0129a9602150015a11111000c402d595800c8002401c020b00e65a8000c00c05100c141d080051176003c0c09000c840e04018492060b040c2d001c1e80d0042525403560030300d003802c2080030798400428290850180089006402150b50f013511000c440c5550740d080c441000010815002c00941c000e042190025202c440003000d0201103008805580361a44d9a90030032440e4640040c00a590061940781d0407410340c05000c2c111568040720324a5031a0940191000399141001c503412038600c017050282409141d80b000c2e003d8440d505100e0080105806000f015203e0f0060420142c4141c0d19080010101031080c4a100f4580f158801e56030400d00703241c0081c0340500502c0c0980c5d400 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 998643651 1250 998642401 998642431
    0xf0213060f0911090a060f03140907031b030c0506030a020702030304030b0603011805070603021b0f010c080c0f070b04020f10050c160b180d051209100e03070510020111030f 76
    0x83c070940c803030840b001450024100e030849803501100f6200070000c209100185562501420503031040328940c0c1d84a0782c10b080240250300d0452400081c20a18508102d0310440030480c2800003c40100e408005c1d42c0701152030076284d0341c40c2010200a0712420f10029098000071500000704146240800d0041100320002e2101d545101c9402d40e841070140381c050025800410101300c510300a5009040101c4449851038007060071103403080c90104400c01103807440e0364071400c00d0205075014508641121104001d2031504214a080b980180269500504203103074050106086580755044140c11010107040900038066183c0301034016000103074021545d009208044050b02c084a4025040e135030409003c038201044046140c40003031448076002d8100d201c424518004c01c408000301c03408840800c041a0b51491002c0a1009002e80d003504502402100b900514581e03034049918011b566040da482c10000ca40b80f04102d014010506030b0050100d000002c0c0680c03100710980107403040f1020103281030 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 998644901 1250 998643651 998643671
    0x1a032e090b040209010915020a020411030105010311030c09060d020c19060b010e0904120c0503040b0c10060311010309020609061c1b020d0c0218070807021006050d0f0213060f09 78
    0xf6440b82504460000d5961001840200040c1d0425848841c852048510782001540810112000f0502c5007400d81d01c0480104080c0d82c0c1030040300081c00307d490409082d1706102c1300c0d41d5018010a01c040b84240c401144802c41d00c1da0681c140c41c0161699422601c040003034813102c01c03440500c0c29045e218035041c0049185554040d0a5804c400d5002602950442d5100d0711000c0070440550a40c900704803008000c0d41c00f080c41003000d03002505e5280c198503a40c02c0c003043c55514100d2040303090f14806040050400c04642050701600c1d2404082c00d01192402c201c0c070001e1024401c0d0094a40d0002010814004409105400c1c041c40c8407003c508210909c1d02c038040d44034280b42044000016807105c0300c0c466a0702c0c89186a0344640d4409007104071500880605108052021944480050b00384410001d003640d04006003152004c090780308010fa1b074105000701d484040900b401500000030070a980c401c54841890494002498840c100810364540c0d07aa641d080034184180c484150400580070 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 998646151 1250 998644901 998644909
    0x120c0201090f3002040204081501090b0112020c0124060822170702090a05040605060f011d0f060c070503101506031119200303011a032e090b 62
    0x2c007924140c10300c4800b0141504101895044500350f24950064420510b0700162180c0c0003400250601c03034050030320031183c0b0703044501e683e80c140e0040600310304006020b4010f9810152115150032048805039032a00c07000c0c24140074150a2554041144031410b03c61181780c240342000094994075034400d10b0a032982c0b8644c500420f030460420f00204082c0f0400340020350803040300444019180652802c201e010f4000618100c800c8800740c84003601c2e04200410854148506940501c00701c48069841c901c0100007084144a011090038064241c101d95543c1d41e81c00340b8142d400f0724000c0802d540c40c402d400000b074480105100b030394003d1148401801e05030f6424019425150519048a00094034103007040307016140301400315440d503004125108001e90f5141c01781d01c00341180d072609064842c04142d0a000340c41d10000e41d56880d0410b0006201c2003684031000c0c03001ea000b41c188070391692101903040b080d07003608138101900c1003109441c50b100121107009003c11140150420000890240180 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 998647401 1250 998646151 998646179
    0x40501140f0f090d0c0b090907050705100f1517071a0a0806010e0607050a050601140310090219090b100905060a1d030d0e0f0406032409120c020109 65
    0x1120307854140a03607100c10704450003801441c04001e10240c4100c0075a2501901c1614a03082104000d10001d2644010305101c0c2189030091032510389140b40200d19100c1c01d13107481e030800300c200d2501e0300c4042006084060f0f0300004000c10300703250481e0586507504000480c21200e4100020300c0e0154502c000392220040145065260340480301f180780500700e10b000c6074040001488a810b1100c2800e1044041d2210005065401d203d038005201d00c18060418900d4404143d010404005020321200c3d03568402003510070603000320440104252441d0310000300c207a038162401c1401100d070904000760801d1603030000c0c1c0c550b10043c0d5454a00c0748000008480e2302d00540556600207204108401c038141c86100c1406460321070045540e40c150400c80001e0806105200320340000303400c12400500303441c000352201c0d603400017210100116859640c0b214002d441740410681e480302c481000007201c110030b4100f081d00b00e2b4800104110207010040103003000400d5070040c0c0c00900c0c580000f02e599041c4240d4 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 998648651 1250 998647401 998647417
    0x6040e101a0307090e1c18080a0b150d0807061b08011a0a1d0109050a0b0a08220821041a0901050106050f091906030c080c03070e092a04050114 63
    0x40c12610030003107107245500003000305880c10010502c1141600f2810410004040c1100b000501003403016801c00c45101c21001d00b60100840300c0001c1110b66030344503800010b07202e82c020b8200da16034683f81800303c020b20b0341582a16158181c0b00010741d00a60086059058908800c178503040c0c0d00502401000302d008500e03c810104440e41c020a0018100c030441640c035031070500d04580c4081e20b170404035006411581c02030624100106100c02d01b240c111a04690100458030b6043c29181254a40400d00c604030301c01030200080000c00d0403604115980c0000560100c0305914803d0070315141c02020103000d105026084070304a408034503c00c41c180983c504846190b6140ca0074211b001c00c624100d60301c400e00c8075600031100d81d407419120035aa60600b00800041e1400034091100210282c9000d900078102c0492002c100304201042d50014222040c10b030041e80c9020040d030f50f29000c00300700c2c00e004680b2140401e0901c00c1d102d10304139183c020002d032102a07a43d01a80f14041c40000080d01490300307 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 998649901 1250 998648651 998648653
    0xd181703070f061e05150102120901050c0a06050928050a0b060a08060a330303030b01050c06130615050306010e060607170c150f06040e101a0307090e 66
    0x1001601248002c030518040d903020700000540c01185402407041d480d03001088143c0c8070740355801c000014092a081e024141000e00142480e0403851444403400c0c440d0040d2203041c010042104600104100501845103510040070070050810000c220354907017030b1450030b081820380040c4c10224020401034409001d030740207004042800103540c980b030802c0b00050038144c104c0c02400300028441c5041000e58020001c4460002d0b0710264148590800c1030004401c00c3c1e442c9150400c1e072a14184608180d040301d405140004891490b480103e0f2244078200640c03185101c0e040900440400824205841d188103020421040c41040c6160242300180d2040503415080381c0c004010070114a548203501101c000e10300703881d19040350340d08010b1601500030031043c0c6401080c8003042d42c400b000303550103044014400c030209140c040794101e0300300c40041c8100d000b2902c4260744082428104070300c02c0402d14107802400321404860310030101c4483c40b1407030f900c244942c0c1000141c2244500c12400750307a031144 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 998651151 1250 998649901 998649907
    0x1060605040e0a0c260f060f2404030609060219090803070b0a0e25080601030809010c0f05060c0d0605060903060105090403090e0106081e0f060f01020c030d181703 72
    0x4588500241819480341061103403c00f14401031170324842c91134401c0d940c10703031851031203050811b4101c0603280014200f5001782c420702c01d0196035a85540c40c04030304a40e6007002d054000f070325601c280c050f4040d030b900043c052804c05400c0c1c8100802500580810b0390303035406085804802c00c600702c810004a104400b441c4c2c100300030500120791440d0450744d120039842c0012a00c0220954610301c0e01e41c03a511140131444844500500020170310110b18000c000030b1b4014000755065451700000c500c20350a02d60b041c001f913020b210003040910070345480c140d40c000b07090b0740f080d107002010000681d000050300180a0700e0035001013100d2401341c065500d130303c801500900c01c5a007000240104c002c00900240c05000855400080e98080342a00c1d50103003106588441c1da604006060396403460300d41e0700115000580c0e00420200f1243c1401283e0320140850304681c00b41650b000607801c10000070b00d09905030054081c0d80c02c01e41d0b001035840c422041117514a0032403070307a914214900e206c1a0320022050750810 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 998652401 1250 998651151 998651161
    0x6140114060901021e03040e150109210b072012040306022b0f0b03060601020a030e0a09060b07140d020601030b04083009011104030b07030216050102070501060605040e 74
    0x4070010380000c01d0180115104018088103034401d00300c0421018003541d02c00117041c003070340409120085c1c1000710007840f5840a10513000103020803025001c1c00e8603d000030511302c9403040800d004000040c0d00803002c02c426061449005224078064140100d807a0b5112000e80180d905c000350340b0042c0d004000d42c641c00c05080d541d4400103980940881449070701e40001c0302903903415050503d406100e090000240713112108808006030307440120454800c2c1c0118042200307a98000c6030b19980c0650615195000e040080000b40b0268040d03003203101c10628007040406c0034082c40004003210340c064200084100100044280d0798034100d11030000603040703200100001030046143c0d68001e40300b100c5403402d1009075040408a07103082102d001c0c0c440c1108601b6008c5800700301c0100e401c002048000e0064407812614880c180c031680c4070045c151880200080c9040c4c0c0709a0644070790503201e041625444c1d0080c00c3c814042c0d00508402c0d54a94a0300b1800071311280180103c80403946a141810340554403 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 998653651 1250 998652401 998652409
    0x7030807091d1f0b04080c0f011407020f1255060f091a06030303160e060c01060b03180d0804030c05011e020424020307020913120c06140114 62
    0x261500a40000e4641801003080c0300b80402034070107030884d14024400c00507c1c40400103024101e00380c01e410300000042480f600c50000003140c25030398041d04c00b42c2142d013060001c20000d0501042505490085e9190304d903180410b4500c054400039032181d5200e00c411914103a4001500754000c0603403a46540c82ea034400c44240080d44500c181c01400c0001c1c40f1840c0081150564903100422515900f1082d040382e80c1074041078203140c200106400450451401c03038040b5016041300100c807014080612802c065640d075650848504541d40d100074001d0316555015000950401c0d62503403c805040c00b0814084800010403440c400d546556440e016101c40d14140d425607980d550a403900d54858160410300340ca41c030310403070301e010b0036440041c0d807949402d030000041180e0aa403c522031480b100480ca565900006640d03847d60100e504a41d2078641c044001c040d03881c082e80051030b0344041442810501d4026451801441c010749083c080440c2c04d004d03002c5625008d000304182c0315440c036030303041c19420 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 998654901 1250 998653651 998653681
    0x14090f07081303020307020d03082a090105070c030204060303020a02090a020307020735030315040204051818060702030307090905040b01180b0909010b0a0f0e06090a09020607030807091d 82
    0x20013801501c0ca040b20f2500400c00d2841d510400307901090000d01842200308c02800c00d04400c0301c0c010964401800150045038080c410f002809041040104a403010300950048450080d5030003441000700b25a6460007a44035503103540c0c00c2e4880c1040c00006040c000807802105e100d600142c1c0980740c120305044991041d2007000014081603402c070900d56011000129880d001440d92900540d102e1609100441c01c120200031014000c0340140300c100285c1c2c4030300c4505400c050030081c182040745c0d280180c0200c40b50310310101ca1024464030088c84107a54010008602902042e5200c000c46622002c400040c9d9009940c02043c10710400010482c0c00c09101004181d85c180500201c0c162140e07100007922104140d8802010303941d120000300c01480c00c00b10480007040c0c0809a00c12041ca0700ca078102c0001c50040142d80035004240020700b0715904c55002030802907005100940b603000600b0000d140c41421550310000c01d1188c1004581c3c0c10400d06200c5080c6201c02c48100965160100080d040c4 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 998656151 1250 998654901 998654903
    0x7110601060320030a05010302030c1917160f291608130608010e0a1b030c14030f0412140a0c021212070c23040203060d020a14090f070813 61
    0x41c0e80683c6242e202c40036400460140040a001140715411070042605011482d000300e4410b1000000f01700700d03020403070328400440308040e01200301d103401c13407028500741048091800c03146a0b6402c00070a04100d5280e8100542e083d141201c1c003850400c01907031101d44501036100000c03800602c150407402404107261581144184602400c20f4006180c00035801d146400002c0825010001404607900c0d01c1c100320b034025440c8009000740e8800c148084080390380d5680c200300b01900c9810001c0664016510050f00082038000c40d582d901d04021701c00003130041620200c41e64508042e1810100e88107841c840882e2240c0c5803264507003400c030f0f80184c030603d03044201281c02c4030080b031b0003203010740090241e411188074402c0a03650300d0f003951821070001c040b140c0115480c2410b8004101070354005010303040141c48140c2c0c005a880c0c8803e00064603c4544090096010701005800b003200e0321051481000d52109640c2c441903074850054020410744100c80302c00000e150500041c00444116801c500c0076 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 998657401 1250 998656151 998656181
    0x30e09100305012c0a0b04081321050d020a03090506070215040303050307120e030307111c0e030d05030c09040506011106151f0c12020708030408060a05071106010603 73
    0x2690326510642562180d48850505683c44c0b00840403003c040d1062481c0c20310540d01a0005444581c0d6015007444054406840745001146588207000200c20314805021f0700c06000b6525482604165541985c60300c04440c3c80c003c98801038455400000d10407105039060720354000340b80c240018843c481e0004102603a100d5084082007444885c1040140b01940c080d0780d42640e240307890b0307201401c0344207195040b410980c640501610746d00c0c0040240c0c1c0c2c0010325450f0081442103540142403030f00000d0085c51070740c400307c4182650303034940144c03651007404816000d50b120f1020660042d1000c1c00102c81e40e108610b4100941420f0703180c103912070b1b42e0217001410724803481d0602c03104485c600300085846401c0c10010180354401482c0c40400c1401403c1c020071090402200d41c10000c05000204000500100740d02d440110024024010034003d480c80c030301141c1d2640d0b03070740945640d2a00f041d1091f6000c00e10f07040205184910a64481d0040030b4007800402c516407905030101e0080c60041001051 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 998658651 1250 998657401 998657431
    0xb18151815060309030d0f060306050c0301120f03200d260103020d05030c1b040b09091e1c18081219031d0105040b06090702070317070803040c081207030e09 69
    0x61b20000c0c82140e0000b0070010f00011181e04515001c0d080704c00c080d0991000e20360500040083d1720788010780b008403a0303110324240a034280d6840c050340c05006900300704442c4044036a403090a80e100064030042d20800b5a182d40c8031003036968121245501078040140c00028010060000d400d200d45005403241c0304038101e80c40d00684540507810204a0700c0f4030100703410007240c00030b0149030038010909001c40860f00a0300c241030184070a541e400c83e8480c2c0c900000210700482c00f829034140b020f2841406881220401c0c81890540145020307100d02c0e040340315504e07200c1d006c00c40340e0b0001143d6401411082c24a031812000d05000062803102403400c0c81016101d4801040d84586103c440c0400b03086940040ba0324140782c5000354403a40018034043c011403d18040014a59000981600312034012450984403402d20f1960a0703688a03002000d000d0f07010000611080080102c040c00813184180203032540c080000c680b44541c0d10490702c010300015050920b5a5840c6840414540c00889400c200c8031 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 998659901 1250 998658651 998658667
    0x50c1927080f011a0f0d020a0801020c0f0f0c0a0e0a021e0705011a011b03090503192001050a0503070203070204060603050a0605010507080403060b1815181506030903 73
    0x141052a6080710381d07980c111890340a001542402003007000d0713854046034800c540c90030004c00c048000c6421203611600982c00c400c4259110091404050041c07000203642e41d20344980c4491f45c40684080060a82c07213034081301024580041600006c80da00148004400303803404507121003189000d003080380351950070001c0c0d400e407200d40e92034480c900d50044400313a241c8800d404d1003800c460108820b4801c901103151285056a03101400710080d030300020100400403010b08040364801500d4001c260188078503824014070002021211022030b219984551009054030042303006034040c09441c5010440a001c3e02c281240920061588500c90b48112406c14aa60300000c0c2580d4296004401080d80d4000340207070864240143c1e000380100382081d82c9000b1a60781e9903074640c403403803002400035a5903180020b02650703026030142044004203412807450529006034a03e40504080d10340c40b941008441400051a40b0300c02840b52a40010b0b01008000e1035040c4550f5500050461880d80010000c040c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 998661151 1250 998659901 998659967
    0x903040e1819210807050a020309030a06020405030d02030f090609040b03031b06010b270402070b010f08010c0e0603060d03051e030108010c0e090a0c030f02041404050c19 75
    0x400e40c200b0000407000282d000d410054240c81940d15207100306a02e00304180320a581181003581c201003580f83c9980e8842800400300e01f94018140c5c05945801005545024800e65401a1050b0340c4124151400c180006078103a907a80300d0115a071000039403d11440d00140b030305c400682040030014002240708400d40001a045074442040905480100344075040350000070440c190152551503075a51801c00000c0d407460b540042009090840c0c110401c0c9501a82ca0759010b0b81c51b03140d40101c222007156103491f040d108079501400741c008030350319049c800410240300e50b040540580000e014a4503503124003090009690350722009038240a000c01440c0e00032026102e140303103c04000720b101c540b294100070340d21742900e4680c030407402041285601803025565180420360001c00050f400655440281402d901610140000c2050b0364404500003c40728501440383c903140602f290208400c0d62031105002c85c0c0c0c000c114000012100340320718200c04074018680e40c0c080c14031040081c400e41c03207945889 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 998662401 1250 998661151 998661163
    0x270b1002060a0c08060f060c030c060403050d05060307030b060f04060308130f050334031a04060507090f050f04021903060e010906061e0c0b0703230903040e18 70
    0x10401a407050003000000ca03010b12611881440e18507160701d490a00f800020101004800c080b0f20400c07001500d022a42c1041040740ca2850b00700e01941d6aa240604000d8004d070400c00000c8021410a0300240c01450042034110a0740c1d070041c80c40c2c1045e00e400e010b2101d00a0304140c5203400503170b614004004036078000003a2190784540303015000342609207030780305040e00401e901990281c0c1c01003d0510042c15030180d89508a0120305643c1154280e0042e880305100595101801240340b0070040c00c14800340181080c4a40d0280000303004a1319810300072601a241031180d0840c04602a00a10162a0854108426000003003000d420800c4c15404041500b01c00d0030726001090391082c040245144210050b401001100c40410005181c810081c02c501d01803018035181840c1e221105040502404500c240d4a4210740400141c0c90006805001080425480740c400e0540c0000b101c40d0202501d2a140710b566840c001c1c5040a00d00000181050780c064030000c041606080e134061540360400c41c3c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 998663651 1250 998662401 998662429
    0xc15010e0a0e030309030307030b0d080a05040303091e0303030b040618060306110c03030121060e1e070b0d0203180f0d120c1b02120d0e040b0109270b 66
    0x940207030820509480c01c42d806904a050140c0050003017140f01000803041d603a01a07520b00b004a849004803000400114045d41e004003411408108008000d0303101d40075005480c0b180e1070300e601d440e450701614681d07640c0c00c400e00c0700404d0f811442440004d209810229040d40701500104585440300c440030000c440040e100341420f82e9400080052144e170f800740c0000d610f04101078615281454003c2900c03444140156109403d0b0090581d26420702a882a844a40c114500300700800d80461841d07259640004d0701d248403a52403d4544040c1804a191000c03184001001450030004030403e030065040101403007480700707141c02040011001170022842c03146245024209030703010004090b0001010b0394150700c2803458a0780d82e1604540000c1c076418010b1020794480000b80040c0300080801000c021001ca640c0030302047d1600180d0445c2c122404020100c5060062180e554011121001980705d9102c0c4000851541001c1a0126003480f100c60110382c0082010742070900803a03100303121020 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 998664901 1250 998663651 998663669
    0x10f0c0e0a050f0904060207021309050a0b0f0907060305060d05160e0c091c05010e0102180102070e0919031b0f0320060705130503010504080309060a140c0c1501 71
    0x4111829860101e00035806030408903249600c03c40000080f40d5400f43c002c0c00240000e50014405d41503680c0e40c0d80c00b041c1461000014042c500380c504e800b503101d0a0109044900d040d030403020071080c200c1c0c0103800344150070720030003080701a103800300840107000050805030700070078050380201c0451014441c0103640328001c0c6400d160b075841d003071301820440d000408028008c0001c0c4078450603680d65181100141149000941a0075038500701140108801c1d4040a0250320000f000b400301d80e5914017590107010240c0039036480326628070b041c0c41040d80890341542d445c0c00900071030210605181b03070120070071302a15001d085c01c4c0203540300d00d11105c281c00082d43c0b0380030103444002c20168016001420b030650312201c4816100500c12059942d01e020306100d003400b001041c00f0101d884a000c040c001040014000e209a003821b00300358883d03510581d0000c3c1c46004401c0000c0509516004150301990601d020a400360780d84982c0184940010000c240180140d4100d008217505080509020b02030000c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 998666151 1250 998664901 998664917
    0x30f061e020315041e05010f061d030c2403280207031706041524080702070302060f190905040c030e06010b03101d040309050a0305100e010f0c 63
    0xa44464180101040d01401801001008070040d82c0d10401c6040f641d080e1400700381d00c521408031180c51509108a201810f240000005400c0008124001222969240c0c0c020301001c140e07003103c2c00c1100c01511038140d40f0010040d00d043c14188030b500e0302c0b03c0c15191181070402d40303100e1440860b0320a80d00f00010030040e0800c0181c1c44841e128096005203910011071804602c2e81d4050003814800780110559070344500000c1c201e03100c9400a01050805280700310741d683d228a044007001000300744800b4a14000d004004180d4001c50559015130115002840300910719420040c03103a104008400c0c48803014025008264440070440c1c180d040d00c2e4943c400010b08000900040742e40c288031a108150400554441044010480d1410364540203001d559903915034443c005142425406008e65a40d25034400070020703600c1a0040c042c4e0310913070300c0030504c544e51001c20410301194040545650449000c0c090039400961092000c0403030392001144101020946000703c070464007105020880395 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 998667401 1250 998666151 998666171
    0xf1c08030c07060c0e010206070e12101505060705061504020909010603051b0a0504050f150c1b0904120305151f170c03070c03170a0603060c02120f0d06030f06 70
    0x41e011355000c41040f440c00b0411500d01d0b00001390707907041c060158400d12801c80c0b03170141951600280761a0103000c0d10100c7d03802c0004083e031390000300040402203210740b91074040410036180140c00c07a02015000300043c89643c030703010362103821250400c000784d900680c02c0255482d00d03201d10014078004c08080e18001000d26000a8401446a141c5884041031000300402d2210581010503202038a005664030498480341714080383c0410000450894503000114004904000000e0000d690308a0302c810b048034581c158062000d5081d09880003803048014071042a122842507000383d0b400380c031164030004103e41c01c0c0d01140801003483d01b00101040740108484045030845007100c00c902d030b904820f10b540d160a920380c0180c2d000240c240c0c0100804c2010040a051094407000b0305400c0c0703c00c0710341d054149414018002d2505100849515092400c1c3d0151140049412110400007041103454200c030162030203007039408004450525661f401020000c18490b1001c008440e100d1070000a84140c0 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 998668651 1250 998667401 998667413
    0xa0b0c0c04090b0403020c040902100f12050f06011107030209040803192a05120f0408040b03070306050a080f0d1119120e0d030c120e031b01090909020f1c08030c07 72
    0x800b461f00342c00340b030a040e803110042c1c550a403042d101d4141480c003035440c5a00081c046074444040790300c1c11910b50510050100c06802c69000030b001d21802d0f02c0b02100f5040c5d50603240c1e1140c1c0d07684006988904810006000b1442c44001903078800e04000f03e008030b000c000313801d00b81150714150040b2080c0e04603015805036104c55800c0405040c502d820001d04045098498845404005008481c42043c20003c0b504200c401000e803400744c62101031030394407440c0400005000b0403c1c0d2080381e02c602c11000f0700040f002c1000c25118205503041010304080d034611103064a0303049408200312007910480b84203451550006018001051199036402c030052002c480c014100550002a2032040d821260081c0000b034004118003950799000d00001c0c1d040c29900d5060b80c0860304070200c80d4050050940070245c0941b000522104030b2003d80f23400314041d4466690b83e08803000e45000039040003c12400309003c0c070b4941d40e2100740191003080080003013159a206407240d081562440408003010605408001d5 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 998669901 1250 998668651 998668663
    0x30a020a11040e060412020a080a1d090705090d0503040504110d0e0c011d030309040603050c1912020f040f11030906010501050708190908060106111204050a0b0c0c04090b040302 78
    0x120303001d0008201c200855030301c0e5900541700908803100d00072100200fa000380f1a000c0f03295000100e094482d402d4500192048012041b0f04805090854107140b0700d00c0d161401074020a026920725091404002c10b00811000444c010703202c40c4003c3c000010781355260300401c41e440400010258441e059255400251544014500b545820107003035000b840e640500c0b45844500180f44146240140d03002190540c8200d00b0010780040c20071740080305000000071034540ca81c1003504c00301c0885010100760904075080740140888489541021170261500414046c0303a050010000a107901032418040b0448051410446c0c40f04404001c200007c070080c421180102000e080c03007464050390382d96040c8503120310f508ae41d60104012101c0c80300d291250410102406562088504558440340054000c0c0030341f40d10804280b052034250a60b030340404041d18101d45024094102541c1803d890080e43d0708280c2c003041080c810f802242c2d800c0e590324094840341600600e1812400c1c10a410000c1c2044 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 998671151 1250 998669901 998669933
    0x2010c0819021e03090108040c09050403080f090d08070c080f0c0109020a120c03140102070c080f01180c0306110d020d0f050606090d021c140c100801082a03030a020a 73
    0x80b0072804402003400e003c0112a02d020092034800340300c0da142d260089c283c41c15078101524261800d010041016006500d5030701801d400c59104a10340da40c0a5603644c0d0300e0314400e90a00051059003c06d00d61070080d032240c003401b0700c1500c1d02d908050b2404400c0c2111707001201d030003246a4440340c0c81c0055050015190002d801c0c1e9003000814946507494480d88481d00b031100801c12211051058890602135064580080c0d024858032800d07a034400d940b542d500d66884268050f54a40080d0311000c0c900910003888095103c6140f500d040c0c0365071200340040c020f1a840100403141000303800000212032004100c00c941c40c017000201c042c040c1c007158040b510010405130254030100a07910140d40e80c1700e0303402e081d80c1d4102c4e803d20920442002c8103000340c40303d0310010f007484402c0c403454802c008045084441e4074410b43c1c2d80d032118203007041c1c01c8034034900030700c00d08044d074003d409a08a00c900280f40d083d030040120b2991078a03600c40e400400c1c074550010f0300f07000060704900b990400304440e103e8008100 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 998672401 1250 998671151 998671183
    0x3060c170924040b060f0609060a02010c18180e0102071b0e01090e1b12030409020309060a1103040f0606050d060507120209031b0f0405040516080a030507020d02010c081902 76
    0x2d407420307644001c2050805012580704e4030740700191031801e548560071a0a508400781c01680c5401c0301c0e4602902810005034808041007194a85852021420507414112084074104050032403141c40114020310140812055554013003103100c0c041013640d070b0f40c150710725031001d40c80c1d511714070700907204002001c182c00c80c40c45541440503050110381c000070001c240316039800500c0c00d814407590005034420004100d1603000d000c0460005480482c40d4091442000080c0a80f4a2540d45400c24412107076210070810b444902407000c24040b880c00c2441c546035a11460340024a603031901c00080c20040a408110b03661525081000040e41d0b1110001d81c007040d610f40d040d0704102c81040066203030110310080d243e030100c40c0342c000203450752100c100d6004164090301c1000030b07050504041c2c0e2502000b410a103034a140034040050900400214070340c482d5010380c1d8903410800558204407076115400002c0e8100b01c900410403000c602100000e0200343d64110b4480d181c0400e42d000030b428080c01c091080e0803 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 998673651 1250 998672401 998672473
    0xb0a0303050d050915010608090703051b0f06070f03050d0b061209010b04060303090603020703021906020a020d0203090108040602311d010f031b08150604050f1003060c1709 76
    0x209000505c10785041d51014100011780356560040140307451820740c000340140c8941550f803c10020344034030600008400f5502058500100c0b01846640d1003050300007400d5207401000d41d008a48604050000c0661818000c030b035811803040007a0858000807414000700461000b0302080300e00074461a00a880140c800b40402840c680b00030708112150320440080c503400181e40c804041c405d0003100114120706c038041e0320154507824190003d4020001600152041580040142d4000400c3e20401c100580d5200c485903229640d00002e90401449106200450003012080380e10043c40800c5410024801519403450840040b811128204108412404400040c8601d80e44843c071201030303c0d00946001c0d080540030300c201e90210341a502a0441e400350790b10508180b0410000180902001c507001d204544034582076000564054940001c86041030a040001480365002074110889900348454440303002040011010001c44410a01d60007001c01d00980302c1b000450500c21030b02d00e44880213 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 998674901 1250 998673651 998673673
    0x916141309030c021c0b01081c02120915090d03171005030327090103123c03150b07050601080303060a1e0323010518030901030504060b0a0303050d0509 67
    0x4003880c5243d0020307006803441620000141400d181c00e0256603480403200c1c6881da0b4801100c0d8684050114405c61050300285031103080d4800030f1b6500c0d50010b9107152601d403414040410000341008100c42008140a000410f696502c1c1003541060030302940b074001603065860010120720030010b1020340d8011416000f40241d80f030010544500410499414030120902c01d10b082c403158210751819072080360700e4000320400c100c0049144514149456028034264050025900c2c00c0c01c1c00002800c4180c0c0b0080c0382545d0410b14000804117025040000d602001c1801c013403064101500011603000c07002a003001000010403d0900420420001c1d43c19803c1840010b29404054407400012911580a418042d4901100c1c04000d40d8001c3c220201500494810704203e60900c500380c48551800d00011911029407034051141d003100c8000d503290206420055008010140c01031f074405655100c00c4250351520304041000d94002d031686a151500c21210006a07030000b008110b081d00411882d038 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 998676151 1250 998674901 998674907
    0xc031401060906080408160f0317012d0e1e0108010603080702060f0f13080c18011a0706020403050c100c020a030b06031504060b0a1e0b03091614130903 67
    0x11041d41d14a00d04001a1788660514103d40e00a121903500d03a090984000000c20040408200b1114031984846400d0410400c00004038042442041c815500c0601034248000b070111000002c605400e640d481607e4480000f1003101c64225000305241a5103c4606411804880a180100f050754000e200071811035648001500a0b0040207000d078001240d528403c0385a0b03001da60703918170400c0901c0c0d00d413021569200182c0103580300d0143c20707006118450600341010130460035480e548186120f250392a2002000e06403d42d01c174081050401400358800144a90006100450140b00203000e071003120010003140100e0030340100280404105040c0050300e0303d10458040303d4128400300d810341e8980011a060202200b489030f100a405c108102c2002860340c010032008000303030b81c6003040c0c503110078030710940038600c07130041e080481009070810010400100950744900d660003074641160200c9203561420945402c44001c206001e880d0900741d052620610307403046c8211078103000000140e1005 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 998677401 1250 998676151 998676167
    0x414060d080a09080a06060e0c03060120010905160905090d0207090b0411030a050921040e07170f01090b010903020906040c1e050403170304020a15021f0c03140106 72
    0x40c41d03403a001c514075428601551074040281032a00c166140340403540791050040c0800d004000420903604003013801194203034252803241c0c8068585540d600e09600704420046060340c0301c502190348a01200b400605d06001c02c54214030407080404015041c078904d04150303000180b002c0c4031903000c000e180d8046070380004c5000803181c000000055602802c40810090720103a405100008000001d2000c070b180181d20041c0310f0129003040d516140380344000500e64040c0c0c0700c10b0300440881444144260116889502c0d0480d220382060000198410084010a4021600441702c0341d072440c0100000d41882c041d81c40210310900e800d8a1310ba0039580020096003026201c180940e90b140000343d411401111b601a07520460821003980380d200640080c01684240400c40322a120384030070f03080010000d015240150340c000c0c002e2440606202030030b07000e2a82d68514004510810b0150130b501c441c42d5140d085a80c0c44044081042245141c0107800e81e00c007140703903107070000145004205e4254040c8032 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 998678651 1250 998677401 998677403
    0x3090310110f180d1a060306060123070609050a060c0801030314030a0608070f09360312230603070303140c0307080c1f05010b03041203021210050414060d 68
    0x24554444000a241c444040c990000a42e00204c00503103101c140207844402d41c02103100042c80c010720750b0300c400525880f44019150b07103001c81c1030000c6020002d8105031038a5000001c0022150805186403902400d039250384400f40d0342c6030040174050702440400c1c05804040e64131070038021159450740e0b034000d0002e1112888031441d032501201260400f58540c001e04002c07e4820102c1d03100b1919a4460620074000c0c0c030036000100e2a140150104003682c50380c070041004200a204046141900d00e103050309090b001c124104242414407185008151203444034802d8810712000c2c8610b0418041c2c2130002020b407045200358422181000000d502903103a40c200100194002c0c0c03640004285503166002d4400300420300240070909000e11080054a948480600030300380d05000d8604110008441c02030180d8411402c00f0800280420314070030218138800c06500d80145000c0d1920354081d504801500c00040034010380170100440c2c5814003c0f10b8040101c1082101c203410180c001620242c0080b030 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 998679901 1250 998678651 998678677
    0xb0c1c09080f09120d09092f070305120406090201030b0111060604180c090506091e270109140f0c0916090e070509030d030203071b060f0204080309031011 68
    0x1071914207070384590104c01c0b0480e8040045604000e200b000c0582040c102c0e005440b030742c5140140c001050510708031901c00e6045c02c1e00d008902640d640000407110782c800c1005900b0701801b000001030790111100002d1089005400c00600d4130014030006094030a0901820304006202c1401c0e070454601142e00d503002036080300c00184d295140c0142030030300e4035800030181c2002c00160000031046519040544601021604112199145103440b0001d00e0418449064546a03a000801d8465070550320407130481d0225802484004030500d00e42503904030b24040714a440840c0e41188000810000061603600c91000740c000c2c01210350200c0c0215100900c032200814072040101c0c3c40b18040c102c10000344c482440310076198507180c1d4004c0c1c040da0000c0c4005000344503c02d81455503a1191007a28091b220681e1034032000007000c0100c900300e110604003a1641c0e50b84120f504a6201244000c00c028940c0c4400355407101d8030041014280010021031032080d50400c62483e40c040c8000d4219020310303011031 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 998681151 1250 998679901 998679907
    0x303110414090709150203040f0e040c03030e010203070c081b15252108010e0f270d090905060a060c020922030809010e16120f0b0c1c09080f 62
    0x40c10880321300900d40c2c4181654030464483c583c890b81e0110043c421340e10301c141010a100d5403511a800ba240003103030050450800290706000003407056040c02c1032070354144101d170304200107902d275072000d00c1e0254044082c3d503125610795072804030740d42505200d02e02c048070741c0e5040424040c81781c043d038820f255594002e0614100c4203090719002400565000e90841c103410404522042946254180f00c1c0c1c140000c1524140006040c110070f021040c49007400b180300e484c482e1103c81c0e1000380c41c1008940c141040b5028480d2080c03416080218078030642c0c6594409907132034034000302c900c100d50014100c40e000e8024140140b00040d0004a4054140da040e10718425640d18140b000442c9004031f052040f82d804200b9014041c035a110413007034025a2041c0c020402801c030054507a0f41c0300000f0040801401c1110310070010f182549041465a90081381411400c0100c1c1d44c64011452040312588000754000c40d5414280b440c501071060454041001040703e1b171416220503906008880300708150340000 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 998682401 1250 998681151 998681161
    0x31104060f063b012309100c05101e020903070e040c151d04092105040918210219140118060b03010614151b0a030311041409 55
    0x3d4600c1c201c00070b440a05040c3d94070030034800302c01d440803140c6001e00040018001d10041408210100c1d100c000e40d80d8144d00d046250028840400d1603980c500c030922552004c1c1c0c2c0042001030002000390001e5031000512010141018404012189000c40d107051041c095032025440000d4103909444011240340159566481d0808034013555802a01c2406034688a44030340355044410300c02101e8400c592203031009000010b2008594109102811b0302c5a4400e002c00070010074100c90b440c00220f450020b10702500d8241e0b0b442510410004001c40310041703041401404416400230b18490b1403107800041242d80e90900035514800302c40c01c2603070040c0f14250f1204125140b90142e2545a00c0802071000040d180400d45c0d8400721844190355131401c3c03000340103c0380b40c18480c5c88292212005403150804e01034043c1b105c81842d0b24032030358540b40c003088640c180740c50610f51002682c107003200508203803d00c1e240041c203407171001c0444104c512040c842407000030084400307205548420b40304c901c200c0d036071 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 998683651 1250 998682401 998682437
    0xc0c100b210303040b0f04020d0201030902040f02040e06030f0102310906080a03142b020403060501170f0715050a0311040f050315070c1e0c0b04031104060f06 70
    0x20009100e100320105400301d4003044011000d144107500031001c00b02196252040c0c480e0102003150002e40c000294030045c0010340c000c0d8800b802d500c0c00039000051460903c090a0102d0780940c000d0640c0324081e60801c401c40c90100032080017150043c00075403d180400d40729079849429036030130f0203060300c40c0140d54000c0c0600c40408802006030380014004d1a94680c0c0207922a1a540d0065001070100001494644404803c40700e0707005d603110740940460b0703440344040c001314024412030003210707001c01002022504a00603117000e072040e60302e540700c2004030b08050703441c22404954414083e0001c101c1040820612403140c030500c10b031414400c5d0346610b9208200d00800e038100001010110116001c58800c16041000c0c06550040d000c440541c0c1a40c0b9044603015021030320755000443d191a4400000e00140d0b8148850740d040c0708126001d10a581d80360402c000030340196500e080040307020024030407403c00444183e0b600390b40400c030b12810034000704079600030b50040d002402000d030180c03015212 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 998684901 1250 998683651 998683669
    0x170a230102040f29041404060506070b011503060e040b0717100801060503010b3703120f0e01020c01081b04030602120603030f1603050d0e01140c0c100b 67
    0x601402159126111040c0400b0700c00d85014032428246009101c0300d032488030300c80003000d4a40320500c4504152a00c042c200801d2030803007240b03800ca500c5003000500c0f502c0c0d40010b001c05034414046940c0035814811100070000703a001c00901050f04114040014080d0f5440c40340c5c1013504404030701c00c0b40d0f1300c4081c180d403040340c2c44c0c401c0380141c42100104803081e04983c180c1070a85040b1030081c448507503603508040c00e80f0b9070300d40742c5640070001c130010503000030780041001c03400c0c0c111446900306a1f00c500d080014079132059009580b405400401a48107682c41120986100342c1810074003010903210000035942c0c40002c0c5110b05226001010a03452800c01920007000450321241c541c0d125180d150001c00b0b908881c0010542011403c0410103501d00402510074803086c0c544403e050800745501418900c854640980901c0402c010101601205026180d40310000b0400400da2042031410100c0e8064010721040d9a8030042c0243c1c240d03820b01040c42c00315611903620204580c054140003459000c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 998686151 1250 998684901 998684963
    0x4031103070f17130b03040501090b1501080a0c0206041121031201060504080303150a05090106081602010209060d1a0306040c0305011404020d120c0602030c04030c170a 74
    0x44008514a400c0042d40c211001c1035500c10401c0390400002c090030803802c0d004070a4100502d0746a00d4082c001913100901450f40107000c2c00010450f0409529841001d01c42913621010103a0042d10b401c0d010358025800d01d82000101d03c041280c0a40c01c44025201c0202030700051202c2c0c120800710f2450b5a841910301454546a41e440840c1500c0d880e005559911441102e41100d210b2400028001c0c000c80545003202c1402d0003661440d601c00c1401c401c4091581205c59020003902000f1809441c0c10401601908440d1221903107801c0144030124030136a610112001c582c0100080c200588509003030306c1c1c01d00d52981d4049140098050540d100c100702c101159098801c002c10001400302401b001c108582c0614020080d4200c20b050318060303000100e50194105800c0840c103c0043c0600310074040700710f01464512142c400c1c2d5981c10381642d00c00e07150f100450b10081428803d2101c4599450010700f05040342d0820b80c41e84160030360710740b5400c0001502000b4030441f45000440201c6a8034025 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 998687401 1250 998686151 998686153
    0x60c020f04020c0d14090907050a120203150103180309060302090307080d05030f1e010302010c240e0c0910031b030b0705041a07050a0b06010201020c07090c0e0a0b0d05040311 77
    0x40e6101400c500e55a46000c44d400e000655101030802d11090500111081400302809414003030b5100300041c2d4103079120030f00c824102b00202000b81d81100e40361001d0344c06122449000600564103000060640d00024031071102c80c0848014180060742202001c011107415040c0903882e400300358000390801101e54071540217030141c40d41c1d0701e181991090065124203e80381f0307884001d441390044032600804d40311288183c1042400184055030090445001e5644940e80c84800540d81900d92031825000c0b00c40a919a0388a0108002c444030070b1080c0d43e0b601c80c0580b0200f1003803400c000d6015000903984000341c03ca001d951048981c8940450300200555001048d100541c01c001030002d020364810b1107007103c00e0800651110102d0301c00c0c001c85d480f054100000b0400c91a01d5242c541146402400b03580c150340d0b00b0845140f0898041c00403400a203110100000c1040041c2c0c8003400e11390340d00c01402c3c0304142000c410300c51400750009454150101e4940000c556035545001d4486031180040e1002c5 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 998688651 1250 998687401 998687407
    0x50f0601030b21010c200303011e17060103051002160f0804030f151505030a0b09010b2809061a070f0b040f03140c0c0d08190906020111090a060c020f0402 68
    0xf040805420080c0c80b000c00796603560100068041c2e81c4c0100490165100b030b160400c00040010780b0b6001c0070142c803899800702e0018500c0d41c1c0c0003000102c04800b41c0c4264103070045001001800402c0c440311000101d203c8056240c16028000c0d00c1d0100e131002c0c0b004100d070725010081400d00100d80240d902a5600040311b1840c5051030504805a011b25441c0fa001281440d010b500004440c1042804541000e002016400c40641d110703220640000c0000c802076585842c0394540d580c41c011911140349500402000e60481c0001150700c3c0d580e580c0089803000d081070400c100400d42c80303001290a00e4090300741c0b034030f0712140d203020380c941c9002d6000600300301e6030324051000b44001c69080c4040e0500c48d440740c42207610b440c1d0072042180103010003500a501312004032203003420465441e0301600d10034142e00d85445c9102e4158030001c1400000c03040000c0c00a44140180d03a024498030742d064100c0340d80b050602c1241b000250f50351169018200402640742d002008540700d0000245900c1001001552 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 998689901 1250 998688651 998688709
    0x1603020111013b0a0809092a071b0f05092e081614130b130e06070503010506190e1002030d06050a0803030606030702030c010501060f0f03050f0601030b 67
    0x64040f00c0b85034003920980088031400c080c110015406408a42c8043c00d1424892201c041104da1030004003150601d03803401e50724120152000a2800b03445040314079603a198011410920180d070210a072117031428070200c20a20102485100e0102194012500784003503030780359a62501c00c003e100c0c0c801c404e00c0e0160002e038001071401c204c07100e09441c0c003601121641c0c40a00a80031815600703100e01d42591460304844465400d0420a40700700b44103022010030001d04650106410741540c400c0c00300001c2e0b8500040351941c03030038441c0c00d0b0030500a00c2c12a017554140000140d042c4151542d030711506c1e080c8001c26000e01d008001c101c40b402c0c00200800091005ca400c0a9125408601e043c642140707030182c046064580726001800b41c03141c0c140110306503aa40d2081c00391070f5102510100079440240301002c0c0d20442401818042d020654640c42d0501c90200041c1000f0b44888002c002e050502e4100850503071b4040c06140d0100c001d01e0003207007101c8840f000c900d401c0422002d0780800054403c40f42 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 998691151 1250 998689901 998689961
    0x7080d05010b040512012d02042117071a07110d03060e2a0c0a201021240902090f060a020a06050c090618010e03160302011101 56
    0x103c120b8030141c1d29100c1402020308030340d003202d0b403848000c5107224510300310035034044a0700004400b00c9007080c001031a103515941d40d54400520045084c10180641401d8820005c109004e41d0703030100c0300240c40e0f080a9295844412008480b03c60b510400e1450b0000f43c030f6240318820568011300000b042d51030120001d48003c003c0c0101d03010305003420500c90702142ca0344c40e01c43c295440c48614081c000040c003401d20404034040c0e019101d00c000034401d007a40300021462480d180a4924030b001d4140400c204803605010810494a20306028085491100c1142080f8070741c406000903a00c03000003e1246050340c55402440d480303a4404940d080b0403902081104503a0b004005a00c4101c4a106085406000300006480340012000051308000003070000201c4030f40150340c01c039001c400104d050038a110041361140e00304100701501c401c4440607030901e035604610401031f221401d502414001c1c404030540700040c809444001c0c100000c011a02d10302c1a02076021020006003c811101d500520316040 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 998692401 1250 998691151 998691157
    0x40f02010206070e01050d09231e0714060702010c080307090e0f16080705040302100801140d12201c0f02010c23070c08060a110708030103020607080d05010b 69
    0x8034007500ca0040898a02d50103100100f44421050751068034007400f054010002d065466402c440d9007500d010030305480d02198a8030082c1c1e4a1220090005880d0302d0045080c00702248074000460b00062414001d0744c1551000c55540c0c1e2080e0341c500e903145028401203a019034000340283c0842c1020061041c003070341c80350f000c2c812079451241515050b26070100741135074a08182d444c2c5170558401690072300b516010b800e04552088070f6051450501d41d8170b0f0041801c00010505010000300b00340018062405600f0340b0344000c0e241a120f05c3e045502c3e5658000c1f4150841103404240720465941d03040a84d00314480ea1140300000064400d0f04240030b6020948001404c2148049107800480d0454117105100c1d1f0100800256a00d02011071651180e180b40350381da1000b41d030b2450082080c60301045041c9403000090910600800c0b040c40d02443c020100c481c6034030008444001000450042034001c01901d06480d0112402030f91540b052a250740c0a1041e59000400f0302d0800000140d6440c80d0000f0b = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 998693651 1250 998692401 998692403
    0x140d050c0d0c052103032a070305070c1e0b0d0b12060a1103040b040605040c15020d0f05070b0c0306010314040305030601020d2a020a090f0204090b01030c09180207060203040f 77
    0x480780c003403101c030204c40703540000a0541050035403007400010a11404400701c03845582c003428080b0300598a4440e0031015611000e41a400308000141d01c0c0c0c10014010200801000c1402007620f041225501c01c40011404d0b00c140030000700003055042c0052115405160080030042c1183c1c0320715a224030311a03c6140c100d60540121f45010f800074143c40340c2204892196a01c06a00b600070303541c9030750315401040007500030740d0a203000c400049080180c1420001b441121a00248442664404010074100100c1a6241040001d11031500001c0d00c408505401c03048030f80c5480d440c0d54400b001200200003c3c0301c0302c002003a50000f070009044d0050000d5026450070303801d03105901e60304901074801c01055460074490000000da10300090003225080035045200400780d40c886540c85080209071001c1c1c908400c1d0301940050100803a18462245405e144001c1c28103200486030083c0c00307004443c2605c65159440412000d400140405904440c0c240381e110700c045450b802e160600140e400c0603100 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 998694901 1250 998693651 998693659
    0x4081b0a12030b0a090203070215180601050f01090603020d39051602010309030c0c080114060301110421151d010614100c120c021801140d050c0d0c05 66
    0x440e95480c81c4240200080a20043d020004180ca003142d170f90000c0d03000801a10441c0683c030800360103c21817051150081318504c03040001e8140c0300400c142854810b07400b942c4111106c200031a8540d03003221030707d000c46015080c0161a070700f40200240140920207500440d4007694a4500a00d441084540c000305140c4030704100300313102e81c80003601c80e8400e21074800c900f15100c072101001036110780c1000c40d0b0940b1034034080d01840e40c1036035818444c140681000520765100e0804006d500b00300b09038113910150032802409400a8154041a01d229901400e01c041c8119250302c0204503403d02c2c0d811074154016208909100094202030081c0280044101c40b21000c1e42843c4001405005103429207501c1144d098004003030200304000c0c150703200d49407003c1c09010134000c000b11307003950145051010355484400000380b0320320400070100308612820f88550703003000060085880107581555141c0d42501c500c401c250150400c2072918044c1f08030b80d68000001810f0320204401c0705007010031500203503 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 998696151 1250 998694901 998694923
    0x1020a020f2407030b04090b180309100c03050c07090506041d060601120b12030c0118030c1104060305011b0306081209040f0b1c150606080f04081b0a 66
    0x1c210039225956004000042c1c04035490540c2c480c1040e460094209016040000381c5491000206064507200c0b6001c1c0c80700c03c4402c04012020b560340c1032820014400b6809540342c0118440014402411101e010003003242c02c1c0719150825006030104d03039420034884222a440c50395060014050481118a280550304126602103090a9000c03541800b18542e0050485aa646001112a445200c01e0401642c1c1c032240020103585503105810400d06031036000d196540707001120f150956650b04114101c5201c1c4804803c08654052400e0402075403111040405061400000b07026113035680020f0015484e202d203156a0080e140301d14100301240d81c40c141b000307503074800f400c0c0c1c2c60b141c19021054941c4030822184050b441c00fa4468a0b610340000c2c0001b0744500f060001c03c03d20b070402130325202094515200c1d038080c4011421411016001351009014050800e907006001c0388010b030180c0d03c560b064501080c100285041561141641070301034425000402518640d1783c44000400d44420b0550 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 998697401 1250 998696151 998696173
    0x509040f02150f18130603200105070f0b130b16090609060509010302070507170303042d02131b02030a1d01020d050c0f010504030804060b031f0b0d050a0501020a02 72
    0x1000c240e6142c08070307070704859080032030040a404042e000351304060b500400e0f0300883e100c40e0f65a8490703800554019009840d80d072125111295640104240290502c5400d100e5480081c4c1c3c41d1010710001c0b0ba20241c10581d03601c035040c41c80c0d0814420407005025052110803c9000fa203201041c0f01150955550840c0b0203a40e10403d44544a0742d000d4200081c20802c2101e549e0750181d0010300c4d501d4031801c01c07905d00f10b641c0c10360318206441403514900203400000c24001030060b140321490303901420050b444948014030003084816111204024014070f0300380c40100260782690b11201c604904642d01915442865034001d4a961080ca2003402160b11001d42d40700c00c0ea0100342403582e900040c0c00400e42c3e404070b2001918160000c017807440f400e100da082010300700700c000c1c010340780a140702e6110120700307040600e0800280c0d03960b054010b00a500601c16220785146103900018902d0500c9800540021440040340d401c0e010548040d001e8801c5030031131810048154010b04c41d000c031a90a4990030800 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 998698651 1250 998697401 998697439
    0x1030f0b060103140a15030807051515030c010c0305071505011d04020a05010c1412192f030f04120c0806010e06130f090f060c0c0b13020a0509040f02 66
    0xd0001c0e951050810322000541c10340c9260702c40d08420546c00710803170410744d0381d50704d411850344141400c69644d001080898000d060814425401865110300c0e10010003160010958440860311950b04101040c41c0744c0c0c080c18007410445891540155455600e03010b541c1d0040054203082c07013880180d041c417440003403221070144a80c0d4040c1e0740c001c180c5900f40d0314050044610014020301030320040e00200003440d41c000308104050703900f1116074460b0344800d05002008040d5009003216014003048103003100c031007050804450200c01018042c00030301056140355034036501070140313140b03201c10307000501081c012488111820003601c980c1c1842849600d80e440e15403260002c0c89061601c041410210710701c0c2c503200112844034600000e0000383c1800c0d51100e40c0c1620110602600d09a000c10006030138004280180001202d55041c00b2903c9403070399031408290b01c0c0040540484104111013881151fa0384074842004200040541c891030615040201e00c0c10641c0008900c5a00d180d00c0104403078038 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 998699901 1250 998698651 998698661
    0x50a060905070504110d020711030d0801050310060b0a11010b0d03052a0604080d0b090103080703030f05060a0909061103180f1c120605031911090c0405220501030f0b060103 76
    0x4845c100d0f909100900b90044065040104102c072024a00000764895031800c2290156030141c640d118082075140c4000c4c5420400d0000348044994200f450a00c0340311204070031105518100c3c501403240074117a00c8118010010480c1c1d2a9100ba8940818814194000c000d0030404840e009030082c1c04060341c1086050144000c00c4031119089040010702142810000d850b80001481c40441c920341e84000141120000b600100d0328682e0106190042c507915220f40145100040d40c00c0009003071400028004000314070600609549450025042081e03031380044522421200001e500c07401d24641c1d14001014018160b00c1601c644041c01c08034650010f201c4180c0b0958103203908614842d5041150515148000d0100440d2902d50005840e10b0810003070022040740420801031044602c1c040300d0505036060340522030407200b0140a804122042190102c4104907450360138092029440400005070210b103c41c06c914002c0000140081540503200c554801d15540307045503540305c01502124 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 998701151 1250 998699901 998699921
    0xa020604080c030f0706140f040e0a06060f020a0302060c0c01020d0e010b1201180b060d050607021f0603050d0503040c0f060509090604090b010918051606020715021b010c050a060905070504 83
    0x10105030551303c0020951f0010300c1e82e510000c04007464187c444980c48400001691002d503101d41d6401c0030002198000380b81228882c0900c09400d02c800340c0d4500a559410103400b60740d19210000d1440c800c0d05003541181e174010707103110f03044c000c0b1424403030349900801c01c803e0341500038103010078004440c08062090b0b01a8504001d0b240d1004c1c0c509840707034190043d005242c4d0b40c00900c04040d1602103401040341c248940010303401404d01d542c0100014800704107001400807404d042c0881400011b1000c1154901c40340d4614110b626592103040415032604642e0054020011074040420211b9102c4010419294203850340d01240e107800080c441218080346020f040da1074000700601c00340306103400c2a1410910700442da01c0402054803114101042080398100480100c0020401150140308400041c00f100446d078101c207a40f5003029448403019000e0b0700c42070030b0550390b50102e81e0003132490084440c0c01004540030842680780c80300003042c5149040e11a40f007812070000351460503010b481c0b041 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 998702401 1250 998701151 998701157
    0x60e130515070c06050406092d120e1c02041409030901120f0c0305060a0e1611161707080601080703111302030f1b090d030e030a020604080c030f0706 66
    0x80d004441c840044040078000d0700410140c580500041540ba008090080740036410004010b42c1a281800307c412840e1802c0c3ca1209065941560400003201e042030441c0c0c0141103030720110b07000e0400710349112603440869400061600b08003824075144004003280f61094604100045400c2c1180707950480844100d4035035401006200201e5110b0640303a1040070002c080458603c2d65592010143d5081701e000d5800a5591800c0014170710341001c0302402000c0c0e8442060040c1450882c1c080580610920402482142031a01c0d03000c80c010050b51140200c0f030400c2c2403203180c444080528003086174a00f0405d0b441612404031740d159020480354100c60340400109801440d50745d59100d443c000301601a8004c546291800c00894640004c6100700d404111001346c81c50303c840101c0780c04811881c2e0703081c07610703086c40f29100f41e07100c07006401045500750920700b071410074400000c1d242280350b075030080d0481d002040002d8008400502c20011503411400e440b0401c0700c0c0c0c44860b42d500301512882c000 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 998703651 1250 998702401 998702413
    0x40b010605070302070e0a020a14030606160c080a060b040f0c08060d05070e04120219110f130f0c030b0303070c060f020304090c020d0912050c0f22060e1305 69
    0x526004400a080035071290040c2c078085c0d0380c1e80c82c50041d4400101c90245056400140c0c070f0800c1c03503000f40400254404108c1c40d504600706100402c00301e005030301d00795000d4607400141d10b080c804400d40c40e5005002810072140f00c038495140400240c1940340d103550069041c800540245206400340d550115a207a90b90303421940d0790340c10410118242030342521140a40034000c2410450b00295a1240307006480481480c21071601c000d141034030f900b000c2e503211600201c204000440c0d1a40c5d12000d102c044540000300c01c080710000b50010241d5052450191801162010416140d00510444101c9860411856207000203058481c803409100904100300d80c0c109009440c011000c4054400c401d00c102d82c246038554201c403080316940072400c1c1c0907031700030800b54002d2540b0030144805002d0105580300a290140ea80c0d561719841d4482c054440c000b19190f0915075144d0901d404000b80006800340b5022019000c1031008002500500b01231040e410000344007403080d92080b0411640c060300901c1 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 998704901 1250 998703651 998703659
    0x8060306190b011209120908120f0912100e060601050903030f030a060b040602100f02091e24090f040b130504020607020919060614040e0c0d060b0a030e0303040b01 72
    0x51000d4050a41800704495416503000361360f22404456a00c034890b801c940504000c000362880503036500c050f415038442400c696100151100b074030100384243c40b01645407074085002800000380521903140511660312002c0c50303c4040e8020403450f00c200300549010f522442c00455861203490300c00b9405520411503081004000350045a011007103047c00076206440c1c1040000c103500c02d9004c2d0005031b010144440201480f4800e00f891012016411450003082c030011540c81c0e01040603520300400b000f060107040c2d031240f925040064080380412040c102c4401030300416500b000074074034010281c2540040310b9061502c1150f101eaa4014111100c00340640850f80c040c0800620403604204140421401070321540601801a8440100c4024000382010750404481f580d40c0808108034114100c0480300c1c20700e10456080e070300c1480c8914000c3c0e41c0c00d021f10b8241d1250580700540b492134258001341400c0d030315025043d0019185e030248116401c0d009801d0340d80c0030645000e0141402400104 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 998706151 1250 998704901 998704951
    0xf04030f06020c0d05030702010f060e060907020708010f0603152d02040308071103151006110a020604030b040c060513090c170103061a01231e040303050a08060306 72
    0x6000900c01d80000d450f0540c4070040318289071640190b10003051020040c450b800e40c0a0040d0700000b41d940008018451031304480c030040e83e01c003034074450140c404070f004a01010320070306c51340e00a42803032030007031010851910304580140020310082e1005d011100c9020040015801640340c3c078071816648504650013001101d18800a06d4002025243c0c01c020000c0041c1e000f4010381201030282c26a0520080810107250604003462050120b4614501c200910a809189a2029501d03c1c1c030740340f809010210555460107021042c003a600c000d021034008104010302c40e4140c840ca104030000c01031541d0360201503030140640c0182d8600c0d801880d000303010041c03040c3d010070301840391894a03042216211202182140c002e030419145c6a813580c000311807690b80d140340e500d5901001c1c41c0c45162030900b03030310b800c4d507000440340c01800c41d040005681d411051103021003903d0030b804c1c10480d9515552450083d000e9484002d41402090007880060001e00d000f1800500c101041c808024001080308000 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 998707401 1250 998706151 998706173
    0x10081b1c0b0613030602031b121609080609030d1503080909131401150815010e09070302030d23180f0a1701140f0105011b172a030f0403 60
    0xd282c018109010006001807440b0f070580095015070b00041e900d04104111000c03514401f0204181c200c0c0070007244804410072421a5030181021030900406d581c4060222001d4403642c0c0320420611601041c48000040480240703080f08240f5400c014501c03518100201032100d23440064882c0e4800d10940000c0c0c14080d0300c0c50f512110000c1c42204072406903032000c0d80141001011851070b1364a0701c00280100c103076100c0701c0140a20384010841103403140c007522846441401002d0032484024041844040d00b04911001ba60340102a20851346c00d4000041405600703524080c1020684050283c012010104a9540c1c00f0b142d00d6079251841d00300700340701160030b06100317a54120385070040001c2e0352588024100c40e088030340e20000c280c1c5078280001804100000c0d00d0745100541c00c10040005a800000030340201c8440c06c01d245006134941495480100e42c0c07000b1105048001032990f004000e00b00107951000c52000441214090040415a44e8002e0041a9501540801060000c00c01c141c0038 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 998708651 1250 998707401 998707421
    0x2070305180907140a0e04050a0f11180d08070807030503040308130317090a060e010f1a0d03141303240c090b1e0c0601061106150f030c10081b1c 64
    0x2100c1b00070400800300d01101c00894032007451075079a0060b21304c00c240601a402140040c079a02608010310500c034801c0321110041c606102d842d000c0e07800d0042105800c1912040c94210b44955240c080a003006062a07004a4040703002030242e5000420020700e4403a002c140c103130155900c007800b1042a2a16415070300203414000f1601c2000844000200c0c140590207460100000204140e140107000301c0690780250640700c81c0003c524004121a2210710a03c16015050300d04011454030906c00c18510f4800d100d0040214140110048244050390042c0c074004030186840d0b82c0035004020030202161400410b41c4000340441c5020444048201c018104c0d000000c1300310409001c22a003450403035800321510203050b0300510010881184c0007001012480340e0240504441d240c062800c4408600518640e403140d21050f00382c60302070301d04000d07044010310040c128400f09070381c1d004090720030702e8129622030005c2004586010700c00e03d00410750744200e0811441c040340e5900da100b20400340200c015 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 998709901 1250 998708651 998708657
    0x91406060c010b0a080d021501031e020a1a07021507050616020c2101050705130b0d0605030307030206090105070f02150406140c03160509030c040509010e0102070305180907140a 78
    0x71000d5030f01da5030154000d0045c4407550040c00f00c40b64540010341040290946000240c001c007004101141c04040900b20762454020701e010131040c41e00c0068441459500420a020802c51141c64529003610040819a000301e4195921202c02e2000c0d16480c4620840141207400a202141049400b4802e05c0c0101407035006480c0c002803c4c41c0030612141041e4017480b01100a08030324a00d801003882030580101d800c3c507001e80b40c42820f00360040c0c0241980300c2e00d4404400041e5201c0f01504903404000640f60080c1035075514176540c00d000303641d031805440c0c105195280501160542d809070300e143d440c0814540180c10480110680700a610a000300305039411503c50280f200c481504d202214400c0c1c905c4203070507880c0d062003101400750100c000c0e103000c184a020023002e5003070359000841901036001100e0200d543d40d03510f4901d07070140c402001c05d64940e6001046442c01c15800201401500301c100003000c040c18510000c0100801c0180d03450740c0400c01080d004212100741c80c0003480d606c08141 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 998711151 1250 998709901 998709911
    0xb0702031606020306091305030417192118180e07030b040c0803040b0d091b060e01110105040206090d110a0e0f0f0601140d0605060f040f091406060c01 67
    0x310180201d0004900448040c3d500004000341407910a051a810044592003465507051554450707a0340e10840c003404d10741d00c40190701141230b040100020380c0d030346013480d22241d0720200300c2c0f41202c4400d0203503c40d040381901a1525045681c491950100040200d07551000c1e1039150240311000141d03030968400003642c4a01c0e80112030101003002134025031141034ad0003d02d1800e406c201304018126080b4449581082000700000c04141d0305030741c00841c80000028180c65145024420740162403440d26228841140003e402a00300310a1240d0031428bc940380041465018041d0032500300f264009d42c48071081c0070035550b6060030103480e05550300c1207441041d001c5032000028261000c03a80440004a8a24104041040030490300b981020182c0e000811600341600045c252699103480c2807220f04011524520707400158201100511010300043e649880c1c4440c6081b1580c001e005410f4450080503000400362218030a246441c0c02110892030b030703521164100103140d8003080c0035050710342d221 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 998712401 1250 998711151 998711167
    0xf0210020403050607080f130b060121020406020106120b0f0705070609060c0e0103020a020a08210f06040b06030103050c040f0b100c0b070e090105090705120114030601210b070203 79
    0x34402040614000e400410342442c01100c01071405038010080580c031709099003480003100f1005101480d003580b04499122603680c560048a00341c0c8000201c2c40c0c20010310b0f0203034120000c03d600a1085d0f0b06694001e00141f1380381c0950f100c00e0b4411640040c804081100003440c00c0c1c03107071b407042ca40100c81403405501c0c0c45d4090300d030311003590300c0305d40c0a641c40d90b030721450b00c6c1c08a0b0300010030f41f00c0c859081c00d0a50a000c0c4a000203034036103641403405040c0c802c0c0024903d03514416104c0961015154001254081c1015500c101403494103e40040c000c500e846a05100c4d8070f0200d0a80e412254810001c080c3c0d1044002400042d012260b440c0c8802500d840c42c00d070b010f955405d00c06100c0322550362440c8240c1003a080c004000900079150209111601440d401c0b9910b51880c49410b4031015510221147c44040d411246e074401d00f00d80c00541c2030280000328151403907003000302c00250110100c2e84140d88590140c402c0101030810a20444240c0e000440010200781320a90701810328010740e4103003009 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 998713651 1250 998712401 998712433
    0x304080c01182009010b07031110060f080601120818040906291e060f070611070c0b040b07120314270f0a03180803070803091e0304060f02 61
    0x3018030200e0344600303ca1843c1410b0349001c0e20509800400f00c030704030b18a51400407049200c1c410740802a081003140400910194030400108400190b042001c02209a444103e5001104580541c1c0305500901000003180c10020801030115034100001d50710301403200d12898082c0c4441d10003560807079103400d00140460503900c00d00420b6007000700c50324081405110a041041c008184540c481d5804584031140783c0750361001c03130603244001c0d00c509a03907030b21a81a4031040e000d02c01e0b00504060801400200903003081c1c01421909102d0351100c800d40740c4540b40c500c21030066005031a0716807828002e10010628440f43c00d0115800750a00083c001c03140f1011144101d0200c03140480d20802c294040f001c00641c115114200c080c000240403d026840821522465100b00207030400601c205213084000f0003080050060000000b00c0c1d5a4441d1440c1c92100c40e002114818807c1c01904517441c1c028001219040100c4100710185107028140401920740c1c900e8211030ac1b045101c0c4900c4d106001c81 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 998714901 1250 998713651 998713691
    0x70801060b090102060a290604050301020a210b091506070506070203040602070b03010509131b0e0402010906030b0904060c0504050303180a0b07150903120216030908070503030304080c01 82
    0x84448042c2da40c0000760006841c00d00090a280d440c145024486803202c54001e0742d07182e0854030300c1c43d0107000c40392510004590b0700403900b2913945548001840c1c00c0207034001041502c40d16028102001c2046004078040840d1880e40c00a03070440404000650300b881181d18010001c44003c000900708a190345940785003503403c90f44c40000d07074000101800b910b501040310038010000030310118078543c1040c0100390101d4001d02440d64180300d1601050400175811405001a0986016034052680e52902240c2a40c07042d103040c1d022034000900400d40520a001344a0b200c0001740c0510500d484070340d248001040d55011780320030400300340400305032075a040c030007440c29900281c21540c080c040041044010112940f00c2171030072a00300601400940020000c20410313200c2d442c0001d180342282000d554003955030754143e400d1840050348101031482d100071000150300030f9507030788140e60b203400e0120354510702c50240c1507142e80103000190008001a0080140350000e41c00860b0004449a02c014110 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 998716151 1250 998714901 998714909
    0x30906111b270f010b070c0b0f160309030c151e051b0a05060108010b0108011203050405100c1109130b060d02180103060c051912091509050f01020a0801150207080106 73
    0x5070b01107003401030100100010340d02401049500514009265451a0b0140350508c02c00203a84000728200c8800010f80040c0d48481400c03960b110f80c01c0344613180090041e4014001220700403243c160108003001015a540c4601e0219200c1040c009884030b900c03600c410300d00750f954080100c20003042c1341e10042c03000d10075001182e10340140a011014941076082c104160070002c410717850013040c8801a03a000d2001ca04642e031058103131462180c10f04044038244a02d07000b081d0003000416040c03884a0380720125181080c0180710070998600001704002e04040f007514100052182c00c00d031078002c180c40c1c1402d150060b0f0020141c0e906144a940440c025a8049460300c1402c0030700e5004105010060180c1400d9916604d4100d2504081405000043d42184005000c2003055070410b1700404407a844070540b90342080f110500f9041d0700009101520141c3c1c0c04854030b000d80200002641c40500980380110b003951125102c5a082ca109080c20540403060881184211075001801301028802c0e1000b034 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 998717401 1250 998716151 998716219
    0x518120a0204050901020702030a0210030e060f061c031211040503010c111e071205010e0f010b010e1801050409020a170c0117091002031b120103030906111b 69
    0x144906004002c01c807000180400c103540d004002c100010394002c15005034590b0b04813130523100b191311240c08400030b00545030b43c8141c5100c3d0f04140600d071000c414040384a100100c5031043ca00034840c01c2184410300842c001000301d462007074100100f00c11340d009004540c00c035542844c00d01d9621000a03096881c8003040c013010503c02c454200301d10100303005826100c00e2402c44c811000020301c01896451030107120701100b281d140c06010701042001e400c80c111490a8104440034003130005891802088031072459400705811103480320781410280d494005080484c0722019450b0318003003d20015100c002004c91b44501c020101040b074405c0c048128010805440090006010f810000760240894240c80111100f10f0003c00c1624900004c000b050010f904a001d0784075201c5201e0010084060714040d101520045542101c2d00451424241228001e580d407042040d03a1780c4050316040c10b8402c407000707990001c00d819400b0420740c9900494a51000d0a14011460300840d540a040c203542041164 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 998718651 1250 998717401 998717413
    0x120c07030e0d03230403210206070f05090d050316060203062707030c09270f0b0d0f110603150f030105151e0d030f0311071101051812 59
    0xa041e0710410340300085400381c1d01d00c00440450386000e0002c0c498403078601a154504281850f8030420038042e107006540c4001c120440c3e280620061401f800d5030a840b030010310515000808841c41144c40007040c1d21592a03071441c1c0140e05040c40b59010340c40c0c0c8240d80b0351200300280c00300318040e00c9550400d140200801612810041300300076000412190f40007002407440703492002c40b02409000754020100b03007130006d4580c00c0d001c01551101d070954800c00d52000b10b44010390308100740846c95154400d801e801080034180c8050b01030220740340020003a411407a1603904800140516002e10310700c60141c14413800c100038400006a095208480100800e4545a0a500c442c18001403803104c03040c08500a0000e450442a20a8021205e080340791090320316a0100c0007030200100000202d41000d01000d00c604d0841c10094518603a864030040064a44000320659810010545035041c3d40180b01404001c00d030001100c01d0340002c52050509a606880b00400ba0794020710f0810000c40540a001 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 998719901 1250 998718651 998718653
    0x1c08070c0e0411040c120203040c18020c070f06051b011814010b01021f020d020904050a020c061018050c13140a060c120c050307150914012f120c07 65
    0x40242c10f4640918066420048400c0710107410103003210302d003002200010f840ba9124180881180c03500e81c07010301c0d15048501c5282800890350010600e00359180103c40c4116640d0101c1c54042c00740d4400d080005200b480b10300d1140034030404a160362207070781c00003190034031127100c8900c244404114110381a42c000007180c251040c00303005600d40c84209001418221310b090541d0000758003669100300845a000800350083c8030960305642050394003410401040c070380982c4031402940010840081031040f5030004490510400c1b441d01a00d03403517640308020140385402c9101900020305000c0603100b00f4004600030340d00c0100d1a10003000d04650213002a45901c0c103200100049801c0300c001c04c00200041004038071100003051010040e458401d20908640c00c1460450151b0788004086201c10302c00070006018a8010a454034082c425206008001d050440c0c01c0fa003110b0300f00240c0485050001d5101d080011050540807403070409640360081080c0c201322381540c1154403003841030380811100 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 998721151 1250 998719901 998719913
    0x613050115030e06060109060f0203071e0b010e071e0905091609140d26030a020711060a08070f090803070c091d060a05071407060c02011a1c08070c0e04 67
    0x640012843c0242c940e80c00e0000000f0000903c50107a8401c2c0300d0030225440040d03108004843c0220f07000200428030301d1441c0d08000079208001802da03401d00e170200011030100c00d0324542500036140d03034482c90700c001020140140c03038180c00001481840302c0624006291b4451400c018402c50034041c9018040410710005008809941c21052049180301d0005405865000c150038030740d600000400244490a426039201ca00d090030705414024001c41400061102a006007055034440d040c41f001c1c002c00e04092004600600c124000040e01610204010354024a000c40f0140c00e5841d0001509403628900c610715030118070102c8640e1444182040000003605c903460990f00c00d1030101040003d4410100d649410140122501c1503507140031550090241c071545264401e803550a40e11406282072040040011040e620090b5007003401c0354403038213083c2c403a803000781000510b800e407203810800008031503140f41d01c021542c81c982041060b01284c050200b40006200c64885120765242a250807 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 998722401 1250 998721151 998721161
    0x6070b010801090311012708090a080d09080c06030f1819030908070806181f0f05070c08160201031e0b010f021501150e0d051b090c040905061305011503 67
    0x1d410380b80d00d1f081c42c11400960642603a0304843e1052880e00070b04055080c0340b0b903030b40b00e4030380c0c4154000c941001c0040e4890001c0740354400c0d1400d644400c442c02d555408803d84130300121890550224007000069500440c00d03007591b4200001040889140c10046126032030294005448030311a041007101808050344940c0041c007a04180c40500306461800d40c04941d030740c0b0003405000d8190000702c5a40c481078001c1007410f0340b048200541850314091814501c00401c020b4046002050510700083c00c21070040c111500b43c1c980c00750a041c0f901a002c0805180000c0c024003c034105500c5880740e10b200700c0c1540602d0008440380d0400190907030311000242c9500450b104003c29034108101e18440e00c0d907600c0300d050469022024003e50041c40b0312084441c001c5100045074001c00b550010300c14400c0000b01c50313410000038007007803040c07200d004101302d10108219074591032803000300414030108090b50491a0814000b420103107001c0d07c0303d5149010f442c1d098025130342101911314920700596045c011 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 998723651 1250 998722401 998722427
    0x1003020904060f080d03020a1419030b030307020d0204020a0c082802060c04061d04020325050403020a1214070e0405010f0212040b0402240306030c0616060b06070b0108010903 77
    0x400a1410302e410044da4450240940e4001810b1707011607a403401500480c54120200c00c042034665441e0f502c12200002c1e58074071621b200c00245007280f80721b1103040000490721b68507001050048440740907820000a0b40c440140403040160340c913011400100840003400f12240380c2d086204515598124029458101031066401c40d8403a40900c010700410a040700d094503540c0c80c00602d43c120301511b080d84500c00401c4ca80d0858400002c01c000708062a501c904107840d00c410701d0811404502d4110b86501590101a41c02940300c94100141c00c20095030401d058411300340c8400782030349058400d0802c1d03141e42c8000b940c040b5035010031040020a10030b0304490003012000b1410003040c00d20440c5441d200070001008010340b2000320f81036540d0014018a5054040d090403618a60040d12100c1c1d600252801c42c003e01c641203010324645000800d90703c1e080781800c500b10280a85483e004040d000f1400220f401c0481040441c0100b0500b03a6054041c080311000032601c0d102d6482c0c01007000101c1c0070 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 998724901 1250 998723651 998723669
    0x712202d0a21020d080f100b0a120605030d090b032a030a0605010c08160528151a061c0c2601030b060f0f100e01021608101802100302090406 62
    0x54113801190011011500501e000d1040811599a90170301c0c070028890760410a081d0f4404180c410000e070b8001988490300b6964a001e220140e995814103580b01c0301c0120580125024000034043e9290710030165a2100b100c91404140201868009145400d04a091744907002c0000c01c000c0520024041d081c02480203203802580700300281c5640340176020711405900e040c00056410000d004c8200106046120340000804a85150030300b034402d5044504d00442d0034002c503040d00c800c0c251007803066010143d04040c8900c0d0b100b11050410041c2c2d841110744864920240c413200110000310311900700081115101c0e2a69071218012001c600e8100000030041003a005c801480003034866a0965008034054400c000b03110461000900c21110604200c0d80000301c0d00305046040f94008400610000280c0a546140c80324489101600c0b10301d00843e070141d8440d507008020030640303901a62100800008200c00300c08031382d00048090030765058580000f6008141c03150300c2c2c80d151240100400c0828 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 998726151 1250 998724901 998724913
    0x1b0c1d07020c04020c0a1b15110a0b0603070f090b0109052202031e0c04210b011a0706020307020601030203010f0204080a150207080712202d0a2102 65
    0x3031002596202c1d0b4441240c0a541c010032200d010078020003a4400c150b40c010580d482c100d601c07048410400b204c0d403040c9220a81d10b2000f1601c1c041c059903402c25200e203a00d000d401c03918003a80314401c0c008006022580c062042c10000540c49282c20411406030413480d00100e075040f41c0c0303800100355800c40d402c16445155440380c20f14092030003405a15420000310340160316a6561031100c110082c040c5040b0030b166000c51308000c20000854001e0054800303000d030803800c075003910003029001c1c80000d00c01001d031310007000180720703000703500b183d1011040b4801c042d24a0901c069071000c050b42c0040e154107015a00903c01801145400c0c021000380d450a24000c41c01c1501d01a005541c50100b2240075000c2020410ba000f2111026011148035079001007803207031303143d41c0b610b008010310342ea140200d000151074040b0f042000c03940190310b602d054845001015001000c5091445600d510895154801c42640d048840a8001d00c03104070f2060045100c1c004103184c18800202128900d165001150016 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 998727401 1250 998726151 998726161
    0x906030c05090d170d020f07050d0305011203080c2104030e0301021801050d0b030601060807080901060b1c06170706020f06012106023a0504031e1b0c1d 67
    0x10f140e074244100d82000b1110041c8180c0c40c4009000d1107582c1c0130060f07481c00000c0d60702000f9000c0d4018520300d807040007180d4109a007160200c3c103c134000c4c0a070284c14404910440c0100c0d200c0c980154110004c0015039160840450780c6c688100800f1000c403c00164817070406c800d06070092080341030560160300951800c01c0262416040f500100040c605014004c01e80312069201c81d400920541805003c0324420758480ca80900884030072140c190019844400292040106000714012540076141082c00c000a41c2e00071400d00301000c0602064940e20745000a40800a0070814180d04103940901011401d02d0002424180866854901e80d8080d2004000424103c5102803402e00c0e580c2400c8000c69103072a02002a12440545810311084246640c00600320080c010580d807101009100c00301e401840f842051341c004480c00b40104207047c007449048051b401c00f1000500540c5400c41c107100c00108490300b004402d00060741e00d10a083c10500c0107420310042880b4980584d27010080500d00 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 998728651 1250 998727401 998727409
    0x31130071b03020c040e030c1e0606040c03140f150a03020306011a07061505040605100e130e030d0209040c080c071b0b16151812020705100906030c0509 67
    0x1400d01c15910415465102001d051003400442101d0500400600a01c812040200c2d580d802510141d607082c021102c1c1c0b504810a00507840280703000c940007801170340e03071000b080000810310a403030f1809054443c14250f81c41141203001754450695850b401d204c80c20300c1441813000120811025004040388401030001d80d600041c020304642c006040250f105006178140302c0b081c09030f20700c02010305003001400b202802d10304800d8426240c080c2d0b0100410355a031070070480c0001241c0c1c0c441001c0358041091448034100102004002e030f443e441c0204502403d03100461965104200c59030740701d0750104800c1e0043c5000e0060100c0070305503283c030307000340e08000e02400e038188180b2900030440031021400c142e881e1203607a400301c02410020101505da110503050203c0c5030001e440215100c5c0c8200304000c1c5502c1151044100102c80083e044846103110b80e01c02c1c203107007501c50400041d0b1203108000503d40d52070081d0701d40c01e41000da03104005c5602d0a40090b041c0c1b013891350f5072818480240400f102c6912 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 998729901 1250 998728651 998728667
    0x6080105041812210e0c01030501150309110d0302030319090b130609060e0609010608011e180507030f0b0a090b0c09040608101401210b0703113007 65
    0xa00031044910f07400c80743d003040c0c40104e412420011a00914440c035048102164040c6a95104800c151003081700864011800c64009000e03403c101d1501d403044c50b1056120303074041c81896104131458100d0541c1080023444000c6421b604a005a0002040002d0b01c88103012001c0409402d003010301c20f020b8641d481d020172031801000c2e1035030906025034100c284403840c0c00c401d642c60340040d8104214960960402c2d1103010454900a481d8200340000501210501c540550740c00087c0c000c003000d00f8005880b43c043c040301c3e03d0100414081e9660040403403000c0c44440c000310b00c1040f229140078180d01d80884191001040e10041c14504602c000118200c81c030b12503484a400d00401c0c0d904c143c1070000900074002500551041d00c1041280d002c0004603511040000e0000000c00e41684c0e40c440d94145e4051481000d5043c00c011050700000081e82c1803003080d0043d40320709012a0403040002040b54640182e40003c0010784c41100c1c0148900306500c000c1560030850140d0819498490f001070710440e = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 998731151 1250 998729901 998729903
    0x1020c0f030a0c0f2f120a20010c05010e0a03090f0f0b070221280206070b090304120c051008060a0312020102120a060e180d05280801060801050418 65
    0x803160130005020003c281580c0300e00c401c408000c1180b8961444100c41c41e449521142c1e501a2140c1041c81c4100c40300000e0f82188503a0103000800c10040f09441d50b03410050322a103480c14080e1201c8200002202800340d180c00326a0b06005100400050030010000c0900354008115800c1c7c54400340902d142c3c01c030036441a1a500520030359500d605102045d00440507561426512100206014900030049a00044000325004900c20039407001480b075900108540b0080d030120b0204070700400906a2002140d0250400040d81c3c100396881130084d04521211100b1075034403890b039500b4071142c075140d100600014010719050017a4035108010a18100060001070007540d8200740001c134441c800d4044800c141c5a404000c4c8a82c2441c442450103000345008002041450340c000490941c180b9042c071a0001e02c0c075009080034010100103946961168195038030b04460f6552810390381c00c000300b62500060007642c5149a5600d406d82c010a082c6041c1c01a41c842d07410aa444217101c050138203011459 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 998732401 1250 998731151 998731163
    0x1e0b180c04060305060a120309180c05070f02030c030a1a070504080a200a1e05030633210105010b0f0901030b06090a080d080106030b01080703240801020c0f030a0c 72
    0x26817a003000251318644030b0340c040504080d070390781c0e548101540810010204d0b5040c0700c100c00c0c0001180c003003800743c6a81c140d0450010b44144034400110780703a5280628594005001d82e012600700b040468107100180c1019542100811000c008495035221001d610480910300075041c941041c2c0c0d4103481d1a16520080d20741c641c00c070502d14801014481c1558030f5440109038a94556540d803112309000c000c80402c405801e5401400a128103010032401d10800d40e0301e400e5400d00003201042400c020010305030410542010088010940391440c40c44240c2c030000c00d40700d12515042070141e0035920140c00004016805215091004c440c0b4810780b8212311003402d01254018003100401c05074011181c1c1e0a0348840e00d0940040c80803c003051005c0c88010a81da5000300d40c1c1c1b02c49080d41034900c0031800e070b0700185c15030700080c00082c4a940031210a8040850803070310341c3e0010944185802d6035030401d103d41e0f5400650481a52002c0040800d0f2080303540c0914188040e2403005401402031103005803903 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 998733651 1250 998732401 998732411
    0x30903070b22022403090f0c040507080708040503071e230309120c04151d04031b051c050a0219020604062319121e0f1e0b180c040603 59
    0x6002c03c0140c80c00c3c681c1c4003011381901d030b20340301a407584d80e501d46910514180c0620b40c5c0c00e03411802c1c580504c5200f0112a29219441d40348c8042c200c946030401041030f24140001d01c420000a02c5482c8064510490030349170280121040c1001150384580207062418041c5944842411000210540e10303003020440c0d005143d91190007040f420300c88204a91a441403030800360340340b4401c8401181083ea1503d01c64200038012090b00d04407a45404d4a0140100301c03050100d25041000c2c140c03046040740315406031510242c4030415075001c00800c0900e94003207a00464800c0989034100284084080d115007991014486600403075454425805501c00f0003a071b000c80d402c1e8141444503690280021a1260780e65602c0e0342c0e044824061503812410700052074035080f005500a1802403d4038114840c8840300c00204964018008041807002c88503c41e440d03984204c5100c0402c04110307190070a40c0d80105000d42c54078104400001e944081c42001d600040a028451031454282c81c283c40843c200014 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 998734901 1250 998733651 998733679
    0x8010e0c060c07050418030807020d0903060f06090c0c0209060a030b0408030604090804080a0b01050f03030a350103020a0b03040b0117030418020d0b37050303030903070b2202 77
    0x10402400742c04c2260024100310140c20301410619070092554001d95540326161100d10040342c5490324041d040000030040c0c1828404601998441c40d00400c00b0407002410956884030340040e07907508001c900103c0c100741541c00950420115440e070204085902c0140d02c2d0550f0b4400d03502240280020704540c134040b0001d0581e4440c3e5001c0d02805070412915074031141d6980005980d000a540b08541e2411000c0c00040e0b64204081d90003010035005000c0e605180307050f001240c81d9181640440d010342c44c00741241c0c40740d80741050700c0d00b6100300c1282508c00e60360440c010300c21040007651198000110403c108404503034220071650640b4660b40701c041400c00360b500801d140d400340e900480070380c054005001200007011360080401e800151402d205000d0305a00300001d89031000182d41e00c103c070340c0780700d4010454003464504030b00350b1000304050703000c0d00c03000030a01d103420846070031080780c2c0000b4101080c800781401c0c2e07662044410540b20001c0160190f40e5000101c5084001d0142032101100d81d = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 998736151 1250 998734901 998734903
    0xe0f09010807170109020402071b120c0e0405070906170f070501080f13150504020306090703021f03060b0c0303045a0b10091a0d170f03040c08010e0c060c 68
    0x2080c5c01d13400030015902e541c89800c01586100d894032031034044800030f040004151040c68045685141c0000f90010000c0c81d100014001a5000340101c0f014014204041141c854511885000e0714510001c0541c00b820b5602181c03424006051304001f40c8c2c4407035400c0205a0b4041d0783c0d0b81c0e1011420303603860081e4075000c409954680100200601007201000c01c1d104400041e8800d6105900840032111245c82d04d445241c0ca0701c2090101a4015800204603104108801c0d008091400985000100e15070f40e02c0b00510395421000320380301d40b41c100005010610420161500800f0488a50724041158408600d4062408450b4585150b00c40340c01504c83c039001102140307669076191030081188192450304030300040040f2085d01d1200d2895001054200302d42c811401700d54180403405560078241d40800c03420701d21a01c4101c900300140c0304202c0d04000c402000c1e0802c50302000b03969840341030524190310100400d03080404a0b03813600030180d4100c10005050118940141c031415500d007041510b003 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 998737401 1250 998736151 998736161
    0x13030c02130c0e0411031302040b01020a14011406030d0c110d0614090105160c0b060a050a030b060f0f0303220b0a110d0f140a05070606060e0f090108071701 69
    0x40c1c0c0e15518142c1103081181d0404480c550340c01c03003100c040060701040445039003517000a40c1c040c0400b60700e03004104010304282d1722030313441c0044c14011035210380343c16074800ca107040c5407220390b44142e511001020049100030140790341158003100079003020701444600801a14503400081e02e80044251008000e07101c80c20729038011604040184551820b02101902d0703401c050320300e03044941c03900e000a0040c040c800114044003c1c0d50b40c900150401d00c1c0c54140510034003411143e80300c102c0f2803000036603580d00b4210000641c030900b05c200d11031420104110315a42044c98240c003c0c50070000c8442c4d00d0303401000310344007000d6a0034100050140c080391140c4155091300002d01e264400500d030141d003600102906401d0f40104112941058241c004172919000100d030714002c203072035411121aa49032074000d0071a5041510f01603080c200281c4444058a403940d1242c00030488050088600d4100307c00c2c561011241074880c050a54540a40b0071707503c0b8840c0c0714134a4407110302034089500d001c080d040 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 998738651 1250 998737401 998737429
    0x50a03110f030a020702100f050f0903030904021b070803030c0d0c02101e18020a0e04050f0607030b01020c120d1211030108300306010f0323060a06050313030c02 71
    0x1050b01c81c80d040705810020360065000341c0c41442c0e03580f03c00c0d80c10740c45100801c040051035500c003820a05500300072841074103c001410f606020521440300e0340d0721188040c008403c440641440c02c01980c4190034140349880c0c103d0080781e0002c004000c0c108000e9070480e940300700c01541c0042c81403034180741242059001d0f031880719070301d08150140941402680884140207049003007080f1100d20148204880e02d8203840c000d4000742c0a01040000900b20280554000d00034000d5981140d266080b007424024101c4c4e80d00d011030303921580d0021650b0b04000d000321200080d50381b082c0008030403c40603030b40d0300c0324038140041154241004150980710380000c11003092504c00c040c2c503075840b112a180c58400e404114180e04403514070a581c1c07002c56840007024101b49003889491511980011950856500018420b26031a0301070070b41550400500070084028800c009119410440d0030040ca03004280d000c0020000144180400546140d020b100381c5c03980741c02c004141013007038070120344d0801984403 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 998739901 1250 998738651 998738677
    0xe0f01050c01090b24010e100509130501030524091c02151e070c0b060112060305030c060f090c010806061b030d06030c05040618090813081e010c050a0311 68
    0x1080c404c070f034804050354010300c050268030091505c0c03240d0011200c04240002c02da601c2a581d42d00000c6036801603000f03280400001d00348103d00c0e81345101040c05d0700e01c03c0e401101c41d0f5004c024418255501c030152226080e180003400f60182c00c1c503c800641e2034905240c1c0045280c8214032807501e0a0003080b91810f840d050240038001c514001d41c42c0d44807490350144510407048c8090001e13600621448403003420f00e03440b09250301c568031050011a884198011074404950380d81e140800401c000300003400d4840066801004103141008046900700340c0a8511142540918481449607030002035050780050251001030700da422480003901410b884000d09081401700103100d0307204c030310305400c00704c2600e000784440304485a6810510084070800d210303402c0c07044561100c4004c880d00b40c0d0003c40380030b4000c900486c145001c0c4c40b900032030038016900044250340044405d04110751314102c02402403d202008000d00e240c2410098050310501400c142015911003203169100e03070f01000c0e500c2c0449585 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 998741007 1106 998739901 998739923
    0x40608060126070f050c0c09060609040e0708071a1804060b160308010902130e13050d17180c040e030d020d15060e0f01050c0109 57
    0x6040e8504202c6407840000200040c00e00c040303074001221903080440d0500c1d002c003038400c0190120103428401c1c144030243d001c1e000032400821a0005031052101592080001130240c400c00c0c143d40d5020b40780203820b1641180024811040d602c400c03046a80300350f2600c1d825080000d07403085420410314204101440f50325040e00610782510040d0021812945800285035540c102081c07081d404440c14800409241e40601c0c058014120707980e00710311342000340402040002d014058070b00781048450226201441e01060710b544035030440142c40e0b0700015040001c0c00a03060004250080c130f4640003081d542c1ca00c401c1e041d241002c00304020420310720541706000c041c0c182d1822050050000380400c0341a030066000400105001a400144401464400b200841d405400210400000a49085040c2c541684c3c40007003c0b024280551500d0304581003d01508100d08000c0c0b07007000315 = true := by decide +kernel

theorem cover : BRFrame.Cov 998561151 998741007 := by
  have h0 := BRFrame.cov_init 998561151
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998561151 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998561151 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998561151 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998561151 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998561151 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998561151 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998561151 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998561151 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998561151 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998561151 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998561151 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998561151 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998561151 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998561151 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998561151 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998561151 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998561151 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998561151 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998561151 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998561151 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998561151 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998561151 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998561151 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998561151 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998561151 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998561151 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998561151 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998561151 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998561151 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998561151 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998561151 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998561151 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998561151 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998561151 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998561151 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998561151 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998561151 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998561151 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998561151 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998561151 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998561151 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998561151 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998561151 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998561151 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998561151 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998561151 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998561151 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998561151 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998561151 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998561151 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998561151 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998561151 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998561151 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998561151 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998561151 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998561151 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998561151 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998561151 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998561151 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998561151 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998561151 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998561151 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998561151 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998561151 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998561151 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998561151 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998561151 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998561151 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998561151 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998561151 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998561151 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998561151 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998561151 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998561151 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998561151 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998561151 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998561151 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998561151 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998561151 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998561151 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998561151 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998561151 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998561151 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998561151 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998561151 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998561151 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998561151 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998561151 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998561151 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998561151 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998561151 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998561151 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998561151 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998561151 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998561151 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998561151 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998561151 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998561151 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998561151 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998561151 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998561151 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998561151 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998561151 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998561151 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998561151 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998561151 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998561151 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998561151 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998561151 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998561151 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998561151 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998561151 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998561151 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998561151 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998561151 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998561151 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998561151 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998561151 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998561151 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998561151 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998561151 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998561151 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998561151 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998561151 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998561151 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998561151 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998561151 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998561151 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998561151 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998561151 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998561151 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998561151 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998561151 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998561151 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998561151 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998561151 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998561151 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998561151 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998561151 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998561151 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998561151 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998561151 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998561151 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998561151 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 998561151 ≤ n) (h2 : n < 998741007) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
