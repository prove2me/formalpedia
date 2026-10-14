-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0140
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T18:04:08.723979+00:00
-- url     : https://prove2.me/submissions/4028e192-70cc-46e7-867e-e53bb9dbdcbd

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 25000006 ≤ n < 25179862 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 25001256 1250 25000006 25000009
    0x30503060d02040f0e030702130b060901050913050f01140108010302030303040609020a0806100905010905060a0308030702030714010f0c1806081305060f090c010203120a020f04030803010303080114120c 89
    0x140c1100d410ba0344543c0f2454980c50004040c03003414041c200760300c01150303180c28620500c100603109006400086252a004440c2c0c2d45a903030448070032540900e00150348100d00b00000b11803403219040d2030140c524060800482150921509060b0b82d00b0600f40d99041950a00454ac030303100902009416401c103201140c0002c9403a0004004a403005080b01c00030f03601c40721460b01d0b2140c221011082801c60800400039507065124190143c60003000c24420313442d2410101d0300030030b460322000b84280400000100c1c228400c0c0151007407a5031107400c5102c20100080e5141c041e014020107003240b1480c107100f0214040c01240c180040d402050491340d40399181510580d40c0300802003c1c01a8100b070044039000003402840968400c0c040640410f149040520402e0315249081b000341d410340d40100315040d10b1204051020b540b080b804440540d503840c0d01181e407071f00c1c4e00407580020a810b401200110415401032840b90513100727400d98200d1001c0c900000c008200100d0300850009400005071707805513 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 25002506 1250 25001256 25001269
    0x60f15050706050c090904050a0c24080408091009080106080a02011202070201050f1204060b010224090c0303040303020a11150901030506040902030304060c050c060a0206060108041a070503010905060d03050306 92
    0x4e003440040c0e5040c07000580200703c01c0301048a04488640211001d4001c102c06400404080c00707449040307000f0402042d0302a85011580003400c0309121851002400b0009030408480c4421409003000c1c16008984901400d00051406100203950902d100030a440000080da0222160141e480848020154a0020095000d210145c1c1000010404032840b41e0400000f001074240184200d01b840c981401c10350200c600b0f002c0c02d54110340010300c80d142c0448844440d464507018400d1340110340e072100e0b00268070708003c100d0415014080840c00009054011801c44420703802900941261140001040302007242580341280b4400b00340103ca003554429031265522460291000a0304202030300060702e5500250b100d02d000072004840e80003080703418003400d003203000107540d0b0038204000390b84040d403039910051089042011030300000b0b044c4044c4800490010b29508610b82c21814501d10041465000340248001e05003040041317001e5080c294082da0145406907034113070031611818200902d = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 25003756 1250 25002506 25002511
    0x30103021302040f0608011809020916020a050703080316051c020d020d1b0f0509060d0e03040b0c03040e070e01022802150901030b03070f180905030c01060f1505070605 74
    0xa10366400d20002c201351a03004001000b070b2100b911200d074158506000d420025000c0800f0700107260030010407800603159004440e8022003100324602144010705012490201d111300040d085108204000051000480046000c0c1c003171240440114010500300340c41904c101c1c0503554181441c0c01c103000d070003c6150302500144411800140ca040e2035100c0b10006e4030700710601c0b11016000243c80d045101d40002c04c1e00d5004415007445803c10b4543c80004410b8050782c0b8400b82d56031b0301d0340360060306080f091080354042c03e6010b40503a2070b41540000255250480d000c1c420740e020840000c98452406003146003207810059009214007031004801c2164007614a502d5010003424190b2070340183e89241c184680c807941c00140c151161900c000040c1642c4045175085d009822501043c0082c041c034001c0207040c0d52506142c410303402d036402c4504005004c0460068403e0001007841d8840c80810f410100880700c4403001114802d889850081c03c8880000741c220101d074080098000080140e080a907 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 25005006 1250 25003756 25003789
    0x402040c11010504050705090a0c050904020304020604030b070504050306100503030d0b010201060b0a02061f0e01090203150a0e1510020d03050907030203060106090f09060b0a051b0f0d02010e0d020303010302 91
    0x603001d00d180d40310a00b034070703019074045441d500440420720850400e108010760044d0844014400c2d00c01e01314000d0118864034480030b01507500000001c0070f544801048cd4000c5d41d104803000614540b007407005040c0d0700207000322882401401e01051903003200d584440d09039140140650b01d000161960031004020340d12519041d5501d81d000040c01c05030311405058107602980150a04c0d103443c006010310300d410000b41085c140050007081c0851240e5040c102e0644910020040c1e8940b40e5001c103012400c2c0c0a540540e00030f4403e0400324001d0100c281c4103000351110000048052107620800c10318102d01515000160300210700d03402514481c1d04629040000700082e90180c645940200307003042e1007608410086105070380d04000344841d0002e43d40051090355020002c05050045e0b4407136512410454404100d8041800c3d40d61108070407810400508107001c8852440305c066945860b4081c803140c1c4400f55103003503080d4483c40c2000c543d407500c1a515502031851a0300b558200107062002c5078052 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 25006256 1250 25005006 25005017
    0x11030c070302150a090c0503010c0c0308040303060b0d0b01020d020a0809010c0809100801050a090902060405040b0103020d0c020f0d050412030c17031003170702010c240204120203010605010908060402040c 90
    0x1244100c02e56903d5000300c2c101200882c00b00010709007841400300b01c3d0302203402a850070f0020902240e105101e04501649841d0511480c2c1302c50074100e020b0401c079009002641d00005584800800da0703406160100420303001e503150413a180d5400da8030fa00003d04060300c4c1c2d40c1c0410001750b10b503200302144490031340324100c8903041c94800c00c0441d5810b0744d4482c601e0041000b40005003c2c5142240c20b15009004041042c4800c05040c0c0c0800c3c15401184200c5001d10b80b240010512607000307406580310b90b81421020071403060100c034001d50700c00081201d10a13501903024500d8081f80314100711000d4400400092030782d01d0b159502110280c01c0c901055a107a61030030140810049558000c500a104100085002d981142804800c02d048000b00e1190b0301000c0200c0300050340c200a4001441c0d8100907070010204182005961009081c0180c104041c0300050200d003407003400c2e9030104598020b5008000180d190401541e2098450092001642c40781000500524080e003000503c85500e2410 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 25007506 1250 25006256 25006273
    0x71a090106031a0711070303090b09060c0a050d030f090c170f060103050d02100c0e131503200402040302030a0f0206071a0a05090304050f04090501060b0310090e0111030c070302 78
    0xd03002c80781003c41e480040840ea90041c05906940704180c201081d501c00040e012a40c5036640151840b4014443c0200ea500c02084885181c0c1c2c0b07403002c2d036961149240c141c0740d0b203a00518106480c0c2c0c039500c03090004a407800c0c400e06c0d004c0c1814800c110400b50302c1156882c032141000c1f0820b0500804c0d20940c0e440d4414018590300500c010701c00240258440c1c001401018000c46000c0d0601041690b003900e50340c54502000e040c4d80d40b04050b01c001041c203550a45000d54000e2142025001c8420f0300c04407515034803000010071007400307240320341c00038420f144010600c2ca800801050340b007540310203949076004d5442c03800441c0443d101c07400708030710052400786859080d580e00d01c01d01d60040000079030000d000d81048858100ca014050340103ea402c040c40c2303080c6c01d0000103144080a01000c42c000c0f80e980d00e05208000d825808000900b01100302d06480f80f8102c0003c1f070030000b0342d00a0307980c10707810010ba03070b040303d10140920001045441003003803c2d6034402ca00484503800402d8198210700c6903049 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 25008756 1250 25007506 25007513
    0xd02040207061d0607051201050409030207090608030a0212090a0b0f040e0406050a0c02010b03120903120d020901180303020a20041a030705120601051909020f09090c071a09010603 79
    0x4880980c00d080038603100085400343d0305803c10000425070801e104040040992442c3d00200760360546104450020b901960b0707041c100d190200c01d421034544685045170208115000001030001a1226800c6800040c0340801c1605207000d041011900100070000900c003021a12001d800c1e00011440341f1420969544c8070641d100c0340554040d41d1a0b41e641050044007075183c020b0b0318814440380028400004010003095803013129424500c1d14040102c3d40301c00d10380c0c0c1071000042c00304007603411685035400d007a0050700070741c095600c1078046841c405034800311107032100c2241c04a981603005441515925212107003240380c540d82c3c1c03810b50050074184a445540ea40f26140605050310145040d4002e15018103160003801e4220903c01c00c451810341c1c101d110002002d038150740c2c09481030030128000140307415804500d0703004004401c1c0085441e61050f10200e026214042007200d01d002c07541c84900c00480030b44119000a0304185403140d1040103d00040110ba4000012600024400d640c0e0b49 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 25010006 1250 25008756 25008761
    0x203090f2413060906050712020304050a020f0111010207050c2e03050c071a0403030f0207050601030f02010201020705070b030f24041a04060b18060a0c030323090102030708010905070903020d0204020706 89
    0x200c0448105c0e03034850a00182030340c040d0b9035000c00c00c0e1014046145040c9a00c07050307515024000c4c02071041c048000d80c0c400d164441e148005c80310b400c0f80c0c000d42d05c5e410a881d006440d10020038991f4015602404440e0b404e85032024440c0d8036404001200034041d80c2080120080c110050401c1d00b0507200f04201c2c400540032140302098060740800b200c2079401c0a21700101034070b070b100c0d2045040c14014068040490b4000ca00203044941c400041d03c82c0d0805840180e0181c052008003404034000d650b0700250010701702e03005500c1814507076041a0b00d40d84495422041c011440710070000e000011460400b5420543c0c001003c0522505496041c404004001001e45456030030116810300c0c0800c4c804211011417001c003039a0306084843c01e00300f41810000914900c41c80401800f0151142840054a568002048801000241042c01914140702828080d41c41610488009141c00e8000900c030001807007154001c2e07400d0741c3e0308551f89185400b0000c2907400848181d9005508200d850001420751 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 25011256 1250 25010006 25010021
    0x126040203070f030809010f02120906030406090503030103050a110105040e010e1008060106020304050301110c151305060f06010e040506010e01120e0604051e01060b0702120a050d030203090f241306 87
    0x15440c446e42e0700c0f000000180301c0c040d00c3d50484255808954043c01d002684010396001c0e110a4480341c1c1c1b02d13500c50a112010b4141540c0140c82c0707001c0040080305200000c2400380200303004101c1000c0b02a0000c004480c00e20580c0318440502d09248011301c0318503840400c0980000071400d41200c400c0d21990b41c00e041c13440a0303100f0b401580c00007800704660f003000e00880044034103104445d0704003501146031980301c0c20105842c00b08000e00c60001a4180040740c40c100d42ea641100c00c41d105468004a0940c1c070b00300c2a100c46000c1241e07800c0c3c2d407105103001d00402d40320350410b03510002c080c05c42d040151994018003101c00d20850321003030703020321201003082070b1482a8017500040c02202c03240c0c1886400741c004545c0d00720259051140600400a81c1f038116410181c2c183d620602c44d840000805060102d01400149039020b051140c0360140da040c0c01171400341d1525400e40d0b0484841e9984150f661200300000443e10702055100d1640241c1c1d984c6090b4011036100c0300000210241e0307074280881c3c41d034 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 25012506 1250 25011256 25011263
    0x308030711100b0a0503010203040b010603020a02030f0703030506040f05070c0b07021908040302041103010803032802030703090c051008041203060e04050109050601091a040c020c060c0a020306060126040203070f03 94
    0x584114101601d0440131840003008107034004c40c0b440c01d06480b0403014000500812092540005103554918420011202d070203140408150b110041490300902501003542c810784520b08141580341a10728501c150750040800e600ca03404101c1d080e039039240384240c0043c440000d60092001b0620180d031044006070b040da100d9002c0720340c0d81d800c41c030410049603000040c52100c0c490502c018000c220303001040b02d41080c2100c242d0000c17040084190205c0c03000083c0c800c613200d030001c814480c10340c0d0107030445000c041c4500074440c0195107410600080c081030106510014940e100800c01240c0c0343d51401110031600d1a011035030070707101e0a070500380e100180d608030740f42da40d0740000109105043c040b007070240076400401e1007000c019908a1000d1000b9402a0384950b981d04142c4e003c85000308500c5981071409800a503c510303050040b143c4407514440b0903030007405032500041c0702d984510040c400400c03040441041a8007020701501c1c48200c02403040381c052281c1c05000c40c50601440042000307610 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 25013756 1250 25012506 25012511
    0x2d010e030409182003030f0c01092f06030405010f09200a0501050304030f020f071205101404080304030c02040504060515090403021f1503030203040503070e040b01030803071110 78
    0xb07008444001c5800e101040100d6185160119001950740403a01c9901450742d600c05120003403240005c1d055100f084400b00520000207054480c60b0340c190408802c01d80a071014040d08880f500750f00c42c450f0070b1000c089810b00b0000000b100186014000340d030f0081e0054000007010305032100c000c01181e28946040c0d45a40c403000032030a80005000e51841803900030b45000440501d1b100002e095030001510003018401c00420307110301c09100308400341b41d850f030340022500d1140d61400000c044d50106c0d001a18240141d60200200b182caa0003081070412040d500c0c22415a11500c814040307410181c811010030000030442d001507581d03800340c40d0065002307100001e030030b00300301d40303082034581c59050130f1750240a0340c0c000c101c0400d40100b8015a8140c039072001012060130030a20740c00910b501045108403001041c400b00604d980040500155001582100c040a0301c8070900403595400b1a0000c100040e180300601c0003800c6040610741051140c20034000070240c10303c04604024000d0030705a661070303 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 25015006 1250 25013756 25013759
    0x16050a02040203070503040b01090e060112080910110d0503010b0306010e01140d050f1501020604080a03060509040506010f050a0b0409020f25020102010617030306040506190807060305060109082d010e0304 90
    0x42c0392300c02d8078014241900100100090034900a407501c005200e4103900941100f4405c0600c004002100d6150500405400c003820784040058107c51300e40b100d20902c0e01c1a402509a514025412241a034550040c41030850791110011170303245840d030314600e041010b480d901c20f50a5452a002c0c103d40c0482c400049018a0180300d80c8200c8407004000001d9044055488501c998020030196002500101e255a80b10910201680941503541c01541c1020b003603070421003070107400304405040c0d503200b0403400005981c0d4002c1124060240c001d01041140070042002020201d43c0180000e0001e10000c40c1001c0c10740c1101c1818404a42c00e1800135410303105160115179080c4a40307005000005840b41c00b003212302000d02d81d64000205010f01656840c00410166583e1302d5118a120100420100c1c0300342e01c03404890b4840e8144d1244030042418000840c5c455030048036107000f5500c10400134011802004000c3c4499041080396809128081d4152a0002d0b001e009001d5401d407848005c41d6110b = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 25016256 1250 25015006 25015013
    0x21060118110a120e0c030a0803150301050601090b0a12020a0302090906011b0602032a04080d080f0403080a06030213090b01120c0501260f090606040c0516050a0204020307050304 78
    0x1c0314244484100194100300070070981c2c1d04642d200c0300c150800c010005282100200d00381c50804c110003c40d61500ca038407801000c106034030000f580b140c0110102c41075000d00340c5081c9401d961080c1c1e8040e02040c040c5406000c01040301d8068001441145048040e65401c4d140c1e103409c0b070b442a805940065000107542d5002c0c01c0c4003640079044503080c83c0c802da000405552072001c103000607100030f00b01d40d000000301e4008120301803810062258080742070b00180800c0c000746501e9020748188842c500403400c4803032036a80200d031514442c0c0c80c01e4041070f035a940d8690702202e03030203002003000696603078403000403015031201d03a0b212140c40d1000c1e80004141050341030a41c103101050780032042c048059094000040c46010201c0308030340342804d044014500ea4403070000c15019203940740c41403540040401518145104015024140c618140c40060320b45000340002c2e55884000003020820800c400d24048400f544038160180c09801618081c0030301d0340c0028143e91082c1c0e055000643e0110500051 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 25017506 1250 25016256 25016261
    0x210612060c080c03070507030903020312040807080a05030306040506030f0f0102040f05030303010803070b07021e0703031d010903030f0c0c1805220b06010c0f060f050a090c0521060118 81
    0x20303251034240641c407490002d000283e40c1c4401050b050030800045064401c1601619618001d140e00900f81c3e8144244001c42d210301d034010b072150131828401c1210005100310003140c260542900303c000b440c90b550700c200600c00900009000ca5030035200d94101041d440106104c1d02e40c80001000000d60358a00d0304d0300c1015401041e0308954840d0300104010440c030040002129261980f200c031f40c0f50990313115502641003000d01000d9600c0e1001e645181900300c000450010162031098650b0300b00c121201840465103820380040901240c604034060010a002d140c10025030748c200c0c0b03000700310314520703603101500da51599104032a4002040740c03100148500703015292b808035896010302200b040d0340c061040200055640500076007582d4010440a0344070301640038460343c014000390300d510060b280c8480246824034560041602c2d00d00440d02403586405140006504000c0c0b1080d49410802003055401c1c0e8140804080c2c8001a245c40030228280b280038001c1181814503448800c40c1c0d90034406 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 25018756 1250 25017506 25017521
    0x30b07022b0e0904050c09090a0204060603110304020d080c030c161a0304030807020c04020a0c0302011a0d0215070f030c0c050103050403080f09010f0612020a050604050d0321061206 80
    0x609180798440341c0059445540c15003802400c4800c02d0349511a400c1c62802e0441d580c210a402600100401004e0b0100181c0584407031b209950410207541e6982c0c0403000c42d40240000c0d03482650070130101d800351070041038205400e4028583c443c07810180f038032200d00d15404402c0044a64100d003058442e1000030311400401811b031144200400c1c4144c45035220742d4840104020300340886003000c10340162080020480a410107403086580703240110001e04a201403200860041d800c25626520b603400700f0f140c00d0b8036014042c2c441d800f200301710b44c01c00c4120341003084810b1440606100000c046041421014102030298454441d0600c00c1d04041c01480403170f0b00320f41d0605040c581484002680044215484050b40303500c00c0083d26844220f60142c04001500c200c2142007100c04141c2c004101400d43c98184210b43ca080350541c0c3da414800203010720f102d03642d0b00004185a090100f40904014000300403640000c81095040c1a4040112405500072156030006070102130308200c4548151070 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 25020006 1250 25018756 25018813
    0x1050609010501050a1206150903142109040b04050c0306090c130302090408070c140406170309010c020d0b0c07020f060304020a03080d1409060402010e0604030b070315030b0702 78
    0x4007981400e0020f4494843c0500a2080002030920102c03000303120341c003400140c009403c030286040d0b40300400500300701c054081541d04280410f54080c48060004032070910b5426040c1a4401c5103040d00f40d108a030f003040403800e40080e01c90803050642d5503244140b92160509020a6803a07082810512032a090000c0ca021416001000801740350501c225403c000c60740e0444507003d4994840c6071025035070058440040a0758070760600814002c140084034100075800342d908100d95507903400008962100c201d03010303840d40c000700a03590065104000003406a07001030915480000140d90f01c1300302c0141111915840700010481c0f40c1180740c41a10b0b401b0703d4070110b541d6410f40c2495000281c02d2895480020b0070b9030f100140841d2080d042d900859031007d4500c1202e42c0300d1800b851140d44031a0100e40c100d00080514840803100d2800303500f0b490643c3c2e0006a86121561035980c2a4002e266880c0d03900b01c9440064400000129049101441501164040c00f5002d80103091070103500d100782e0040 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 25021256 1250 25020006 25020019
    0x506030312060f06040918140d05030114011115010303260a050702010e01021204050d03140a0504030e060d020d140601120902040b1801060f0203030f0c0c12130305010506 75
    0x8044108000503519000b01c400c58072402c18200c61030010b20b40c5d10a5902450303007142401c40b48240d554905074a0b407840350144e003e015400642114440d21084510f2002002c03507014801031089960a6101584080060400700030b007072078401d8654a0402151201082000c002c40180101648000703403800c4010041069030755402c0036030f145036034000014295450740d0307910400074004a100350811210003001e48000c542e04e2070010500c100c0344a00703c909440c1f510405030700c0da190f05e12900c41c20580c0300c01021449a01c0d15003020940151030040c10540420402c2840c41c00c05a0391180100030300d13925490b00580e5107078038420440030f031201c0d0b803000c9000d0200142002460398003d002d10017420301d40a00010448180d00c006802006003040e074603041b08100e004643c003031312125040350603910304c1e0315007520581006a04a96034401241e8442c10f150150020070281d101c404050f040d41d107400002e6a4008404050328211508240400400c00740010020810320000b8852207411010030f4800 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 25022506 1250 25021256 25021267
    0x209010504030201111203010f080c090411011103070203030d0218010e090a15030804030501050117010c09030b060d061406040f06030f11060f0a030f0b0d050d05030703020408120a020105060303 85
    0x30341103005500c0040d05014205070130002a000c2408069800800c0d0f03400251a540c41b56600c01c2d0307102250141d0300ea1032007242554501880c24502d62442186d00c2402e41c40000d052400455a411141c103030b1b50b90500c401e004040c0142e900340007a1002105140c00140c540e80b42d880c103030100568248580e41441040301c002d41090322a840415840210b4100c0407491844100c403145230240c0035403016008400108000c01006810f4100361704036802880440d9001140d08140c0b800c803044000d41c5004903d400c0001c1000030f00c0c200d4101e1f4003403c0180000350014070b5403031340016500341514411002001000f04059440d00e03101d00200f002151108016807415039840e10000b6185600240c00d140d2080400d805513904d21048414614070f003c507142e180d00150074017401402c41d13010180702c41370800114038844d051040d0b030b0250454226008011142018005a8041e80060100303001c00d03408202c040303209641044184080c441c03594144e0b503285100700c030003803c456000d04140e2182d08200032 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 25023756 1250 25022506 25022509
    0x2060a0c0c0c090c0507020312070201140c0d1d0d0c03050601080d0215060301020c0a060209270f0403020316030503011e0605040b090a03020a1706070908100509010b190314010209 79
    0xe9502c10360b50050b000094241040c1803da802d80640a00298584a11118082c0b001c070b110001e00540c03403003a221100000b802840305070580c046c0070012500c950094020040035481903240343d00303034000700f54113945134130051001c5a40302c207402c801a1110080c0000800801500b00400c4d07006100010241000f1811758000035114068546444031103001d01c2c000c2001c540d420350413941c20810040460715143c1d002d150030700180d00b04500d814800c01c0c0e9049031466884400354030905142d88403214481503918500d59000c0c030600074105404610003400250100701d80b2184001e4514000e4031442c0e00c962410750458000341c89041080c1d444400d80344108462a0070005441c1610050305030b035a10760805202003040000c040c1d2010350b02c90079207400014002e03003c1010310558103c441c192549583c40ea201510310180601c0382c02c85640c050785800140c601545d0150350031a01420010401028902c0015078a80301c0090543d003941e04c0610410801c43c104585100308d042e43c000070360800d40a41c0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 25025006 1250 25023756 25023773
    0x504051e09070509070906090515070b04150e07180903020613060e01020a030e010b0d02030613060f1409070609080303010e04030215010b0903100510090c051902060a0c0c 75
    0x11400400e000000881c0500005200200107000d010700700302c816150407000103049507082d109440200d00008404245400c0c0400c0c030202c0900508a110701d450003655407417000c5c090007401611001d00450f1503001500c3c1034014649241e03c008010400326007422480c1a075420b251b00c61a80d800d1030910707504000394010408550005c040e85102c0303004d00c540d00f0300602504110031200500d51000900791000c0f90594801002480843c0080203a00da45900b40802d0011a2a01950640c00507001840008460714021a250310800b000325204015010800556a048200850311012541080000300c410031102c0020500c0d842d2a15400b8589104c02c1c0e2a07120602658600e640c8280c0082c09141c001c0020311040c403e9405807c0c12580e444c0c0000300c541c3c02088038544a40103250f03045c00e21403681c1c020140100305c510444403203e441d00307041100810f0036800320428004103008a40011001062002003050560081c200e43c1c50301c0801541207480c01c1540c6002d100708140d140000c240f1b0300 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 25026256 1250 25025006 25025041
    0x12020103021c020301090912022a040f060305010501140d0b0103020105090a03301d0f01030e03040311130203010602030a0e1c0305130e130b060a0504020705010b010207050405 77
    0xa003001665410000b8060440d03203140321900c040c8500000c00003900042650044440d24000c04a003d841180914101d845200440446414081c145003450308086507119005114800500000d2a030784200c42c14015215285e200751060703591074004102000100c1719501c03402000310798268014280e9565000905070600011341001004101d603040b0b40c544aa000c0e01450300240841c40d01c5c00282c4400350600003084071343c0c600030304103412008064012408044406440402d654014000200340061032980810766410107840d40740d00e070310030201840140059400342c00c0030b41c0000512014000850002101158990301c10801004403540c08400d4402050480c03414030b002c00c01c86000201702850301d00c00d01503807080354241c0030105a000401010501e0700141104842030780c0b82548806240b040b58082441c2440c82d281a0008410200c0c50381c0c0300f4002081501c0c00e503202c0c0301280c102d0704110b20032107403a0f6544c032043e61b0740d6070100728081c000e1400315400d006501e0201010058100e09 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 25027506 1250 25026256 25026259
    0x120405060a0f05040e010e060114090f0108040804030b270c06090405060301060b1b0f06060d03080405030c0115030308130201051b030c01090501062409150203070c030503030603010c03061202 84
    0xb4001c40d290b2840c8a40101c50044c800d050001100d0350f1900010000c49900340d9000c7d0110340c0d03080010440100b0a0161009100000e0012061f00d440000540340b42500070800c0b9001d0300108030120005d078440c68403500400300f50100c00a0111007000e1802d401108a080400e144c1c0300b000ca400c0103503908012038840380e50a481c046115201e040120313000d041c040e00445050880880c0440380500055200806c031b105440440300f0182c3c80c1c4c0c12454407441c0560744150041001d6030104046030003032a4058116200c0e104891030180c420390340b50b08640b00d000d010f0000508080e401c0042c10313070203040716030059000d2207217075800107890380060038504c11036124041c58441d1848008220405000742d4891100100c02800415454500280285028050940c00310700d200d10040319403541c0c02800300302d084952074851209040c40300100308007403910003400840c0300400814000074101c0102d400254480c1c801140c2303c0c10b0400407d400d43d211166110708040c41c041081050120410a11098540 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 25028756 1250 25027506 25027517
    0x5150702150705010c17190906092001030b04050603151f080d030f020c060601030e01090501020d05010f080a080a1d060a080f0108011512030504050d0f050105070e0607020103050c090d03050c120405060a 89
    0x48a02d0110701034062b221020f442202031080b105001c000030f0308015004002680c0c10000f100143c130400040710350599403103806a0101c100c1c15035514610081075042030307210444110b40590055180750481094000d02d206400480818800039014001d4044000e003010055040060580c034841e52100010011410181c603200301d461110003c2d03100c00a059004402559240c04800d04080540400e11030702e091000302c3c0d8000201c408010541c0c00340d044d03101480a150025041c3c080301e10305680081c000e10150402c142407504e07984c031401000090311980b0389104034035000702030708a0900c05a115420340d0741004610030300480d1641c01d000c01d40b034044407035015408407401c0840c2d06c0e0043d900480e800034842c1c00d07140300340518079848412640c4181c0007170040d669101c8003160100302c00c0e004141c01c40d005000c02001503002c7d400c100d07030119504c00100e09040e5054002000714045c60029008103000240080c0c1c580c0c0144800c0010320030008055140620741404141c0510603100d59404001 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 25030006 1250 25028756 25028771
    0xb010c030c0f1b270c02060c031512011506020d0e0402030c0d09030c0b0a140a090302011410030501050619170703120906031505150702150705010c1719 67
    0x446040c3c40740001c488124400781c0d689840c0c401e8107944401524a003c45207203e0713840010a800d00841004064a0b070240030395894541c00280c1580000c0c20345003034038450046428003030f200c2c1f5003540812840900041100202c00340005070510b42c03a044002103420003481043d4840e001902140c502800740d600603603941e1001c20b100b09500411600c0b05095041c4205101459481143c1180c4540100714403009a1900c01d0220100c44000200720010000d200002d1075055003a400034800381c2c080d00000c41c0702c0c14500c0302854403100445848100303030310030391003842445070034800c4a80c026010b072009111210850a4090068a54803907242800080709418490341418852070006541c0001012400e000b80c80c13024203132a0007401103200203840c14020300c800d130084105084c111100030344005c50782d2002e800c2d910507542c0a0b41c03007a138100e2003564400c01403001c03140003410035500801c00000c0340a2505002050704a83d0001c0c810216088800d0001450003178403078038024980e1840024828 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 25031256 1250 25030006 25030013
    0x506060607140105070c03020708060f010b0d0212040311070501020606030a0602030603120d0912020303060d060b0315010306051506070302420a0510030b0112080705070807090b010c030c0f 83
    0x80c2c1000c41a0390b065401d20081c00b103075039000030060005510030f409507000e05441e10503103036a9030021580d082904802d80010442403e0801c02400501e180c00e1015250131240000c0303403101d840c117072000c07000106801c6007202c2507134040c030510004d014244003920082c18070302d0010390b890840c4100540950340c00408100c141d94200b003441c080c402c48103141c94680e05540000c13001404032040c166520464040b490800d00d1010007143d00c41c140080c94800f00324181d0f100c040080810b0410103400d13100e100d01143d03155068000107030003944030301404101464480e2040440c1d610902000740640d00c10b000000010385c0200340c40d46004080704062440441141075500151920003100c1c5070803030111076107007405040c00c03129446820428400c0c4455100c2d000f041501074020311019140d003c2090040c80300054100202d50034070700840510b420701d440c540382d4074100f08503580883d0050780003500400030a80c640c0a4071030750f623001342480f00320107200351009040b0000705600104407040302070041c801c0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 25032506 1250 25031256 25031273
    0x70f1103070213200901020610080a261b0706090506030c16080a020303181c030e0f0f0601060801050609060d02071a0a0905101505011202040e1306180506060607 71
    0x300740d034002e61944100156500e1380700f607901140646005000f4100024a00714080c000302048030308500052100000a0310740d03a0b82d0780c50f80109952002407802c0441030900c0e40d04098100c00c400c6603c00f03a401c1040b0b9690910b0480135504c40d505120640c1c0e0200301c140e407660b042ea5401600303082031f01d0b520040425076850b808191349000f40ba0003c0070500c05009039001000c4c5100d07050103501010588049003560b5503d150422011340f550300c0c40381d20034004500c00c0d00917520580d00300c0212000c98010008090400d000306001c04100d40c008801046410b9200e90024010503040d03400c82c0c581034180000c1145440b031180c0100ca270b2a00040da03030040082c0100105c03ca0201a00110098241b148142c406010503a1080d12103124002e040364030245588039a455500f00b0b04000040c0b07074a001c006581d418460b60701420030903400c0c00000303030400c5055591072242c8a08540700f03850180700d2621500302c640940d09103540c005441c203048000b031f20000304140c01440403a4044d0316807646280030300c2c1 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 25033756 1250 25032506 25032521
    0x150c170f070303020d0c0309050c04020903070e0702012f070609081308060109060506090607110111011505010f0f090e060a080a060209030d050a08060d0206120f070f1103070213 78
    0x35000003640105041d4194080c001c28442c1010034418820a8401203050325540d08011301650001e00c441c50031454268020039003a071018007130b1000243d0754026849100011205030b40580d450701d500b91110040038071104080520b20601602c1d00300d0b000407004050242038402089513030b0b954a01e0b018410080c081d14a286116400890005e841d0301045889540c28440d042c046030820802084501d056400e5455580024004038104692621090351440d41c902c40d8905001c40f2a9000e0207404080c0104c80e92269a801d44048951809000600301a030f8003030700c0030401080040b4500c025030f0241d039a4044034890b28034000d590302e442c00041c000711565441503d0314400e141c440800c000240c0c015100c11803044060301c1004200403001e4419104405c01040001c04c444002811803601512800e40180089c240604100582c21a41c0c5da941080e90500030101d960000c204c00f180e4404906804a0f80300d02e07000e107021213030f100a80d07904d0003039040080c80751110241506000055502101 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 25035006 1250 25033756 25033777
    0x130b040311060411030609070e060603040c151707090506180f0604030b0f010608090d0f0201090c030b04050706050c070b0904020c06010b03010905010e04020112020307170c0d0501150c17 82
    0x42d00c6092a2500c40e482820041c0c1aa00a02170795002842080001c0b90400458254100d24107040d55401c00304100d50784000e10489101881290100c0c100b000f60b1004c1320441004c2d10f404640c01c0c00c0030103000b22520001d2100081103541001442642c90315070035100c1c0b040d10002c0403903009000e440000c0200c42e90394111341e000072010400005200000048a01031510784100220698850000311440700c0201d911041e02d0b0302a1103004080341c440d0312000100c050034070001840b518680c0e0f810240010319881500d00000e00c5042c00b003408030900c003810007030800d03041851501c1a038103042c5898100744e21074100e0602001c210142135444580464100d003035000162525981c5800b040403040e0428010340600601d45400801c019400940e9680196016112840003d03a030400c210701035480104100c04104800e565011f224218613480e5020b400701711003041e19010b45860003012150142d02050481507201101e03012141c020b00307200c0d0300340e03003102d45100702144105c200ba095100303400001 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 25036256 1250 25035006 25035013
    0x133020a02060d060603050c03040206190207030606030605150316090b010504080a030917030705060c07031206030b0a0e0102120f04020105130e0a0608010b01020c040e0f060c03070e09130b040311 86
    0x150740f001d841d540807406440c2503440800261311404040700b0207010480e0000e403c00700410103844000d0038880710040648171441203a5010b5120341d600c20a5514550040f118240c485040c0300e5605541c11004c140c52a00394003c0c806404014420f2100103014418980c686a0f1100f0b4030506920130f030b00320380107481c000044440c0c201003450000c06d2210a4410444003030300700340b240340111501108441c14241c03c003009069544400c40081500d0740030150443c184000d074401070f51610881d010b0000154016258440346283c0300228405581d60b40103030418070703403041041c1042d0485d4501802e40004c0c400c540c440641c0e54030310050701c0502c02e507030952840c0c840a05000440f00204034440e4482e00e50284207202d05c560f201d407041c3c00c2e030f0007101c249400740c0c0001101000e1030078541e00c10020b121030b510403142040c42101e640c0c1c0c00d005098840462a040c00070801c070405400482071080544160b8100500d440c0c00b08011041542c00c140003400e00382690045014188505040080c420248040c0e = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 25037506 1250 25036256 25036267
    0xd06050a020909090a03110307080403080a091d090c0a08070b0921071a030108030307081b0c060604240303030b0402070b07020c120c011b0510060b03010801050133020a0206 76
    0x1c5035078403517085c0700c21400904105982c40f02d01c0e0004c0241d070156a441180c150038142550b49165258100d44502401c0150303141d000180354461550419044020507a81001828081426400c1c0041004c41c9405416a00820804000c0000c3c80b40100c414600c4403030f0300d030015000000c0500c4c03c17861000d000c01c40050082030b0750040c040364402c02c4400610300030030041c0f400024021180400d2060541d15081800000c40d42800360051650004807402200203418020b01004855049080741e58000d41c03100c07042008a081520a840b050440e580d5107001c800030001044006103c5400014109611401450340984070364044d11100e960145000740c181c541049c00940e0b803414501304512541106490140604000c22000c4000c1c1040c0d513442d141e52500c040c03420605140800071982882100d2103450300050303a1207480d01400d80e2002c815665450a01c1c414207545042e00071025803080a0b1040000602d1200484109600040d1803c0d4000400c40e05a0521240031006500703e03100040 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 25038756 1250 25037506 25037521
    0x20f0f040b120105040504020f040c0e10030f05090a0804030213090f031d09060918070b0307090312020d08070e06070606060f0f03090804030b09030c0d0c0204050c090d06050a020909 80
    0x39244031600b040c00c6007181d80c0d8983c1040140e88040d58040e402ca00b00c8041e200b0142050b412a4414581c14140200203034071110200706a032400600000010b566247c100d84d12000e207019440e0402100001000003805030b40b030b465176908c194400244240c4101c3c800036104a030541200c0c0a083d08030845030a250180e040c05460a040c01c041074041d285010480402031410203007503800b8160240603041e540e51b40e0508901c0e0440c1050803d510b038031034103400255031621400218468601691151f034610700d18a8022142441c05d1168000c3d900040126810784d81d00c400c11640c0491240307003440607a00d4690100c0c040d03200380c00b0042d0095040050114140c0e4000104207950150340d41c4407030305010a14011411909a820300420044041000b0070100d075540d952070382c0140740c0d107003502d151210801c10a4603003a03441d4508404034012044076019460030740b00b001c2c3c0c0482103072025442c0401d0500018440005c5020042c11f4550b200c002c190168016070554a075600d014141d000315041585 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 25040006 1250 25038756 25038779
    0x151c020f09130905060411030c0603040c0f06050316080601110a0303050403090f0513020a0905090f01050103151410351b031602010b0a0b13080f03040306020f0f04 72
    0x4a4450050701110b01a2240c03011603c205859150842d000d0060380d00c0c0d542d41c05e2044080c868810750700d84500402071040390b4a400085024901c60340003106070038a01900c1c1c01204070355a01140610409000300304643c22200d012002ca24103901e050030855680e00c005032400004205c84a030306225503056a000c2542550015005500030303140d8468196032001050388081490290642200c2e841c500b10402d10116000741544c00c2180c00d01a240c1502e0310301051200c0c0d0102c642c881c100c001240108042d51b00740c0301d0501d000c1e030100d0040c5445800c00004260a400c00f02510340150b621500083d00075102d003030a00c1c400c80241c0d450301c851508030101498407801b50500d00059164120228038440c1c90081003040c021000105a23081d81e03642c0020241040c21906694155500d5944120380c40d45c40104140242a0804600d03131142481541c0041c41130540d044102e059000e18507840000f50004240e030110382d8000c1001d03a0740c444200e8000514011580210f08140c80441d000c10030202c0e10 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 25041256 1250 25040006 25040017
    0x90303030908120106050c01110a0c0303050a020904110a030e06070912020d140d03060f0f0b030907091e0b090103020102031b03090406080c03120a0801090c020a051e0d02060105151c020f 82
    0x7d4009110b40508110324400c0c0d84108100c96000c6001e0004010000703000e40c2210380e10a01e413610050901003985d0120b002c0d50300b01500c3c2c07a040c1074000703000506c1c41e425218880414104100808980c0342401015010f44d48900aa230b028030902c4800d40d08541e02c1c2c40b42d140b0380380e134850440512103a03030032481d96960841c0403101002c2414254042020b4030041819002c45100015500b0440d1500460b41d00590000d0003c0004d030040c2440850a440e0303500400e0540f11459500740307040b41c60484101c0407540c0d4000c1d020b118005d03c10040000d84c0e03000042d500261089550021307094400903019203580720303040d100e580040c01c0003400101501c011501141d545030a0b01a0f606031040e0342e81d01d2055101e01d42d42500450300300310042c40625800d42c4540b03900030741d03030045886031011600c441e8034140c00da500f801180180e1810101c1950b10500c001c034900100340c0001c1501d9418040010403a032580782e0396880d0041c001c10341003075200100103104002c440c40881199200000000050b19074441f = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 25042506 1250 25041256 25041277
    0xe0106050a050303030f0604091a0f0103060e0604020d1101020705030f060601110f100209060f030a06050307090c14070309030206031e1302030307020405060a0f0e1504020a09030303090812010605 86
    0x22003600042604011040780d109a40d1b10311a41e032540da544c01048004c1c003001c881030300c200004480329481d01042c02c111a000740c00c05540e0100380c0d807542c030307040303090b0741250441014540002c0300348001030312240b00c404c0786103074011245504a029100100d01c3c194072544030681c10b102d40e60b010850a1030102e0464001c071020b0b6910868080d94110065541c60000985030966104076020100b100e45580039001c0004e00a00403841c0945200740ca20003a0000d540da00801070380d41d0401c0112b8502006410000c008640040c408038030f0319134010700f00d900400c0e02503940520010703101d420180300c2d0030000701440d0b00510454807800c0c03003d10a03070329000c602003500751740910001086620704c48440804005a00500461815109500b403001501c40030740f0f09074025800e00d0005c81c0c0c003408100c1640251075030a00c035900c2440d203101e00e001c1801d00700c10000c0c01648100424491968030569900940750141000300301a200c80c90150b5a52007150b44491014500c2c00010680d070340c1c000000c00c0786045 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 25043756 1250 25042506 25042519
    0x3030509100c0308040305090402040f24081b09060904020c0d030e0a02060301270f0b0103050606090d08030711010203040b0402010215092a1c021003020405030606090405100e010605 80
    0x1c0300d10080d12408418000035000c92150304c00140060300c110002c0c0f100e440d0162000d400c003992140300a035080d804d904502944c035a0300050805030b00552144025030300701c902d00704800d4140001e0502003a1000802e01e11a520009504040c03034444a00315500c030030000d0320840d03688014035060354a0341001c2c0a001d00007803c040c00841401400103403552800c1d0010840d80c95039180c80071521402040303c06151117400c1840003c90b10306020b20520101040c00034000c145180c03407000060031240300420b0244600c0d0140100035040d106e030310a1440e6280d100503441e0340d81d00c032401c06030740003080d950380307404590700020400c02000500807a41c0c8c0118800e800311101002420070364540c961044a52007501d90059401c1e00d09001c810144d0b44014000094000101c13002c0d0002c1052103150000ea01d4100554008a60440c28018041c4d200c070080c620b000c504060500d400a0748900e40500554800c01c14100030405000003804000d2041d051400200a10804403105a0180c101e5106082c41103d = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 25045006 1250 25043756 25043779
    0x109021315121a030604050d260601030e1908070b010801023c0d060816030f0f0206040905040f0510020a0c060905070f1707050d03050921030403030509 67
    0x1030103440c4140c407680498488005035100c5401d8440240b02014905003c0c0d200105070f003119840c103110b5180a28014409032604107184079018000c50400d581e40303480d2140240c00c08610b04010b6200e140c012800b440c012407062420f10100c1e2030514025210201d07a004030002c08200305d00c2e07000609495200d501d42c2d41241e82d890034070a00301c1c0941d003440342100c481d45400e000c400d903003180c2012421281c45a2241401f030803030052400354002c500350008460fa81c150500802c407041105403c24800706076440c03c00c0d0b0440c3d40781c0c001c10310201c500400000303104400d4411982d60205503000340c118400f0402c95860a8202441e240c40c21002c2502c65000d015030b4840c101081c1c0c021204071840d951260a003070200e0b50b44080041080841c2901d01e8043c0010114540d660f0b945204000d0405001c04e0240c5444240d5403410004541e01c2240b05d12009503454000940060a86030600e4040b5403201410418210551100c040325411640d54040094048201900100079043c0504182c940240e141e = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 25046256 1250 25045006 25045019
    0x3010315021204020108040212030f0304021f120e0c04020309010207060c0203041d19020a0503010801060e0105100318060c020106080c0a0b040315020f070c0303020f0a03050f09010c050601090213 86
    0xb446808036150080001030001005540900318254210b880540100e019200c00324500c0e04640107102c8850f05017070000309104c15480e1001140c10701d00741004607541c428611000c003401d10421007444941564a03031008841601d02071180907000d002c0500150340d40d1404c980d06900035444410212111440c04d0350a01030705100000f0b85042e9101715152841d003070105041d01601b01e80041200c50443c015540e1000c42010070300190901c0d40c0c0c01d480d110348a5051150207400d6840981202400180c0b10004102039501d5410701a41d244e210b040011702d01c5610200014521503958010340810309110000301255815449030303003100c0c801c409441c001c0f100e80c400c001c4002114403071a1441c040c20300060012540e0f001c501c1c0100080d041c401880c1c03061007805505284c00105e01a2003c8401d140200141901800341450311018000580145400d907a8040d0240c0210b0101110420020844104a0340500c00580080d0b030050102c408a41c0d6500420000e5030000720040d00001c1c80d6000041d91 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 25047506 1250 25046256 25046261
    0x50705030405010c0905030304091503051516020c03030906090102012c01060609030c03030503060102070e0a06170a0201020d0818060103110406050d1e080904020c0a02040b0328081207020303010315 87
    0x46c1c070801005589454544209000948603001c7e8402980e88242c90002c000741d81000113180715400301d41c04c181c0d50710f4451802d0506403004055002590410741c0440c01c603a80100854003070500c02c8510329103170000306004034010f2240540c88566441640301308024500c42c10003104a10f110304009218085d1190021100304800f448020802d656070b45040c4006401103000e141c0c014010301c1102c8041d9500c804e10310780c0740c10658a600c19155140380c14419802044040c0c1000d0000f24002d01c88445583c2c0000d65880551107070408001075100401c507090300f10f00680c000814803204503103141d40c603418402800c0e003020b54450f101790b15003c00020b0f0350900baa00120885d4108409401c202c60004500010641340c1c0000c03100001d0401c001c68940d61944042c2129803240d00040403543c81c4c07441480704403541a40c440344a5409881c20202005a04800380812410003082c0c6032050341902e00030105004140851103e61440c0c400c00020940c000090345c1200e0045044030b080d101445003403401c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 25048756 1250 25047506 25047509
    0x807150605010f090e04051204150e0105040b07060f020405060c01050f13020a0603051f09020a020106050a050a060507142410030b1302180c07021e01021915050705030405010c09 78
    0x40b031601d1a0402601e0811601740790b0140c0590b00755039107c0b807840c41d21211540550009284000f481e81502d4107507a020400a124100070709140d454a0b042031010305260013482c00c004e103643d840301c840300451103c5405540c01868003a08082d102c289a980381e0b070207441d04a6400d421001d81d10000f60b4100307046c6110314176043e00a8180da944900b480b030114040d00300105031103084050000006440c40702442c421004101181c80181c0b101800d01c402030954003076610040c441c0c1d20110702400183d83d41c220640844102d4100159180044c0c50074840c01000020030f100710b8060203c8040d002d1211003141d0108204031410015641d8902c0c2c0c80507801462404051320101c005000070300100c0d84180503280043c0010034a00640d014101080c110300030807285d60b060082c020030741ca0110305200000c00404442600011950655940003d5031211603440d0347e0401f014040c42c02e024800140c500b0319040003596401d02c203d1510b4640a00704d903105a600b101d2540ca40b564040c102d500c80c044080 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 25050006 1250 25048756 25048787
    0x60f0b090c0304030c12110c040e1905010b0a080105010e070305040c0302010f1107091e0902090412090e1e0702030309060411010203220302010e03030a05030a0216080715060501 78
    0x2039684805000c1256504024801c50500c40900c3d100c10100d450003000b0f04030a00e1580d584150000690502d42c2428104198240520f081a405486100e0040b91061220240c1c0f079580d441d40f041410082d0141c217100050340d400c1425510b0115072042c06402aa06a81c041c050100743e40d160900110100c07002210013609000c54840d05000542c480e0540c00d070ac00c0a5481c22110b500701d000354003801c0551640c4452400340e80d4030802c81c2c010580c0300711800040c40e030640402c104101900454001c00c00101700520a1110b002440c150a00a0104001800d12421044214075080781c00e1600d69941c581c2101d0b0100d501d500080c00c092001040f00e1188d6440009051551200e40d240006050505915410360105200010401d2206141034014000c84460a090700b0b10714000034215111900c00d15005c0e42041001410711600141103c3c0c12039480c880041ea07409071030013011164090084014003000700010144103001a0750038400790400d980d001001501c2d03032400152041a1900c0500 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 25051256 1250 25050006 25050019
    0x15091a16080405120d1d0a05120a020103110a0c140718020a020c120a030c02040b06070614010605070c060c02030c04020705100509030a0c02010c050a0506070c12020102030c0304081605030409020403060f0b 90
    0x4c046c490000c0f507150080103009000c034110561182d000854558000351854140e9200585010035582e25000300030744082e03e1000c00346003400d4110010030116060001030300d01c01403402c0e0304040200400c0440018410941b0442c141d03e4101c1b00440a54491843c0c7c80042c41200212803a170315000d402c0907a40d40c2c10400402d220400d0707030703400e6592008406003a80d000b40e44000412041d1564002008503d110390800100d00048400c4c0d03417414007040e080070f010403800740418070010303e903070a250050b2101404c1c52484812075200091130400b00007000c0e9046400417500d001008800107840c054075804590a00090f640c54a00039a2030248134512000500003ca0740805540643c4407076003c0d900035000d4560f01d00d515154207103044001d40c0c1c02000558905688001d0010340d50300c2c0c3d040c00d0084d100940c07440c24003240c44101400060b2010b407600d00005440f41e24840340d080051400341c0d11a050380d440c1d03950b0701c0710301c4000d4000d480162111030400d2a05403120000b031260761208140108103 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 25052506 1250 25051256 25051277
    0x70c0c060e0109030f0c0506130503070b030601020c0114040b0f0a020c12070b130e040b1f050a030201050a20010203060a0503030702060d05040f0f050303070915091a16080405120d 79
    0x500c0b100c0d40c0b4505040c0e4004041b403801103040e45a00c0b00401640054142158920346450141850510540d00c410312001c03060007841180ea13404138404428100910309001040e441d62010b01e01482140d0050701400000203c0c0d01c0c140c803041300034240c1c0040a40a440d000c0d00752905201d00204c4035400f10945410620703040c4001d001c050b0103894030585000004a045882e03500041030020107407070545d1101042c50421803e000e48002a002414010f1400e45449207004c0c00b080c0115500c0c040241440f0300421490710051040b1503410a1301c0d51156020031440e8484290350003540141c41150061241d551b01203602c2c2400811950690b60103440c182c03078607103249801002880c020700200d90700e903c040c56110110b54038150b140790782400380c40515580c1c140802c019007035101940c00318821088000440061680100140c0100c82e800112400101c000e000c0700035443c450041103034100710380c162540080c0b08014003e007094680030758603500d0400010b4034043d950760401c1c0758500060b040300c68 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 25053756 1250 25052506 25052513
    0xb04030318051f060308040b0409060b181512040c050306060406031a060102010608120315100c0f05010209030f0616020102030907120203100203040303050402041a0f0d020315070c0c060e010903 85
    0x200f0000c000440058460b8981c2d640d802c86030703c00c0c1d001d01c0c440c0c2000314050002085910644005184440f10149804940c1d1300307504020002440e502c1c1f044004140c060159040103048420039052070b061241380d07240078a0501001460f5000d00e50123403141c80e0015181c0e0078503102c1c01080d25007180d40d1400e0240800c402d440c80c80700044c901030455490f2100090042c3d01080700c012a805100c4600761a440d0880c410a586440c03480118402d08103a85001c4000360031504d4681c40302e40000d0b81100c201e1560070507d019106940da8190140b10380100500074902c04102c160086002401d1f8500b8071b02000c1c0d040303081c0e0105271101c5000390021042008a00348080390101e4151024050350300400044203400c040703070000c45060303004c00c0d1640200021450584103601201c021540c80700e0303400011102003114001f020349014081ea403514003003415540c0810100c4182100c3c4040301665180400d8000c0592103003e100316078648540e280440e019016038016000d880341079452150b40c9280d601d = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 25055006 1250 25053756 25053793
    0x705100216020405100806100e0a0606050301030209040c0b0301090614030c03061801110a030504030e100e0105130302060703020a0209010f0506090105030406021306031e06030803060d02011b0b0403031805 90
    0x420030341160180000002c6e00400c20300505225642c0902180941c81c98a004a0600320004001d4040c0e2868035070240001c070f41020903a070643e60190b03546031056440f440c1c03099112401c0e800074a20201d0100c000200c0c8001c0b80c02c804180d0301000700014070303081c0300f5090603a5200e40d600d86961507044440010b00942c01e4a94422001d8400c40c0085600000b6030310320f1005500482c01d03400000d807900304210916400410459070050162000c458407224450001c1540e0015a0f500c2c0c1003100028a0800391116001003201554004001a86e03c00140c03070042d541e9803409004a005100d1017000160039606032041c081100c8002d02001e181c043c502c00111403541c0018001c40351030b603003880055000c00c2c0080140c07001d0b00164900284000c4a081c0044004080140b4110b002e81861030900000d43d082c03007569041003007070307032846952155880143d503204031004000d0000c0d02d0300b03401401030100d0f00740e85a000d05d00a03102006400301c50380415804251120003e400d40d4401d4a540b40d9a84003c1e = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 25056256 1250 25055006 25055011
    0x10305150916120209010602030a020d14070203070801060e060603090a03050a03020409090b0109050109150504020d0605031221010e070c02030c031501090b040b010f03090201021e030705100216020405 88
    0x1d010380700b6031014242204020b2100d0340200e4804450485a5811400d009410602512003800203505041d40044025a03651044002004100d90740070290481c0c0400b80a440e1003a50050030f982e40c10f5103895880e402000c0c17500c40e01d1459103090010401c0d50030703c0421a40640314480140210b0700c0707152810350b0a540142c0d0711004040d030800000500c0c0790346206030600f85100300b04200c440e5240c00c038400e00342d41c01a000103840916040310070700b07814500c3c411402103401c04c0e1409a1203211407608031008003480e40c0000d4140c01050625102410b91034001d15003d11812007881140c2c00e00e20023958801824040d542084d1184000f140145014034140307580360344000d04480b40e1000f20750209050849510746641002c0c0054010f101e2104c1d00d000700d8009050983d41004a000040c000030702403811121300e0800e041d96506110b0540e4030070700c40003a486c080c0407000e01c1000e60084010744da0f58000c80c400d0b9041d0007445038415050201b0b000b11404291040d5045000c1d01e000c0e000c210060002 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 25057506 1250 25056256 25056271
    0x1110703020a2915031203060a050f04060f0b0304060608060105100302030910020a0c060b100507020603040c050d080406030f050f0a0b04091403030906010b030c0d0b010507050a0b150901030515 85
    0x3440340110b00307010143c50007442030b65080c540c00e101100b9102403500d494000a00c1450b444000c0c01004040c0d210f10341840c08807170007110403008100060001c140140050f802a4400c07002c02d80c4007103401080c1703d0045000700e105560801409607107400f056210340007030082d1640104072680c94984984642c01443d0448a030340141c03946a9000803c407030881c5e1142d2030800103e1501c4000e6030611031244203044e210b000584044401b020070040040241c4103000c0e000341b0411000c00403d0038400150307405400303040050150358060b00c090074220555080381c491800002c0c10142400d20700c011a0080b9402801295180d03005900e45407035a00203400d0410b00182c01a0342c800c180e10100714503641d400341d59003d60f03028544d01e04184c10000d04050b4160080805510101305000130301141000f180d501404900000070810301c2079004035035a104040e00a80382d4400c61b6449002c0c8400e03100c0c20380c040c4030381415617540d2480b90014499900000d00c40904907030450740f80108010405090254032186 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 25058756 1250 25057506 25057553
    0x703080c1c060602011d061504180c06090306050a0b01091809020603151005040b09010305070309050d08010e07031109040b011b050a1e0b150303040b040608060301110703020a 77
    0x42000c200701102c00c40c3c0d00280040c0c1d143c030410500740d00000303030008190403504081c240c44d00d040030340802030041c0031011a01441c2d031070010308a2548040502450075074050b148119655031200700804184a501007034890600c1d000120314405041c1c0305503c0300100603110b03100154980340a88000e401c19400d0300c8010703901c03000c1500c01603807414002c5118010102e440308104851100b4031070f1500701d207900d420a10104001c1070240c800440e040d40d074898007d1a0104203a5152032084000c0c015540000300a803040307404070560030750010315072070680c0d03100641c030002c40d6100c1800320203403125038600300c800e0481003155036080d0a141d0005440035030181801e107101d14003050005048100c040c02035409802501602c3d0411141031080c040c2005400d40300b20442946489075040f100c0054140c01c83c09550701183c010b10b44052080d1401000f2880625803201ea0300d0201510341401100c40303d1095280154504000322508151588107030541d0003458a1030460740c403008108009134100419a0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 25060006 1250 25058756 25058797
    0x521060321130504050105060d02091302030901020702010e01020105070507030507061407020f0f010b1e040e01050a0f0b030a03140a020309030a030e090f0402090606180409060b0111030703080c 85
    0x90465000507001e848015516a180348810000e2200c6605030841c5100e10b04042c0100519500c4000b6915108562440183d50b80c9105002900003081080c0010b1154000f2040146000040d405048040c5c005e8a60550800000b001282200c074122013013000300380284001d81c0480d01c1030010380303c203520580380080c0d50140400711080ca40703400c61746407005030700c00007050f260050140305020601b44584024803266440704000350220054480103ca00001003545030465a281e8020000030045180200001d060030302d0320f4070141110203030040003141052512803e50400086641d04250580c2d07032000c0a080e0156030041c6680f0140744c0c4004c520050080d0800c6941c140041041c0c01c1c0301e0744590102c00c40110a03c600a840181014289682a0100300158035440415940180300300c1d4040d070b0300c082d52201401c171102440b103030340d82061408c01d405042080075403280881e06400d0321100c850300f81c3d0ba03c01503602d214481000300020305100c00b01300200014000307000004040003000c51500e = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 25061256 1250 25060006 25060033
    0xe01050106090e1f06141b03030702120301060203040308070609022101060605040e06190e0705070c050d121206090e0304050906030a050c0d110d0605070e010207030507030f0201050906030112050105060105210603 93
    0xa6070507c04151b03142e00004103003d011a0100043c0303207115000b560141c150342c94444065200d004900c40a03115500001c0c3d030004018060380301c0100298002e04a60040c0498540e858000b5281603006200d0343c40e0030804203640e4013500654003103e0709035503c11441e0361070300d040c00b241b4500701081304081c9846c0407012075007011400c08184a001c140e0b4859450340380c40c0c204030700b2041c01d9510540c0100d20b10410304011400361901c28100c1002401d010001401144031000200742960152003000d2400a1b07840c2c4031200403005000b02c600031580189035854038030030140c99100c0140c0c01000c2d948584404c20850805a8080451501818110742c040207075001290000c00f40300c0085417810703075850802030382680002003007500440a01c000d121300c9045907076096548900b4040540740d8a07219400c2411684114103c48100a005d81019180d581d41c40c04401d1000c001c0a049030a9400c010004034954800c800743c96880c41000c4035154040700d40c4201c6546c400010300116018000d6408a1100 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 25062506 1250 25061256 25061287
    0x80702030601060201141003030509010f02070f12060606050f07060507051209100c11030a1206090c212a0c080a0917010501030302070e09010e01050106090e1f0614 72
    0x90907a81c00103e40d07440c02411b12094001300511045454110413030500110758403800303440e600c403400e081c003088003444c0c40c609901c1c0c40059402081114808200810f8000d61441082ea04c184601d8003840181c0d220380094031603014054030501d030319105200070404546160441e030b0b044000c600708076241080703c02480304900021140c90841d58014412540b5007800b5211310304044805281c101580d581d442c0d400b0ba102d120340c3c0500401c1000342203142401c81c1480d40300314002c003109203040000c110400400780c41700e0080081c03081e0000b030303000ca500342088644c02903c1ca00c00c032105001c0d0440e2b43c8500049070000307a0240c6002004400c400300381c006014500207084080545d01d40c05051450070b110100030f22401d591096460741400d004200107600014900181c411070000c490f000d685100f03500d070051510f02d00042c2c0d0b6601300707000040d5003908510303941c0c2512801d403c1090150b442e00706a2084000103035250740305460000c4100301c0544142003944c09010310104161400708071141c04000c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 25063756 1250 25062506 25062509
    0xc030302040e180d08070203180114070309060801080303060f0402070303150306020d0614031b030f0d031b050901080a11070615081504030207030b040c080607030c090b04050a050409080702030601 86
    0xb542c12500c41c0b1003a0f22000c004441c4950700a10713101c000c40c50b003c04001d480e4010340c0c84007005944d101c620320619a008048050403000c0c8403a44070b1311652103040040000e0b05d144942c02c04078080000103c1ca4000c08803c82e40310340c0c00942881c0700341000a003804000d5020308000c0c0d0030590b03209102c40005c0d0ba1030302060300a42c05914003680304c111f003403281030880300c071580840da041e10340e41108607041d2000f0400000c1d0340c03a40c180700401d81303114002086c240300303001c14400010301801483c02c803132503090380c008918441e458a9017080800030b180183c40e80d20403030310b0781404105010001440144541c001e616040c00014802c0e043c89a2541da40e0290740740d20108014000d00214144902c032810810782072a650500c1d082002c2d800c1984001c0d455100302e00010f0b0510b24100001002d000c1d80900030350060a204049504514220750010000d1000e120300000140c80d1560014000425400792815200c0007400411024909030800c0010821004100c0340d0090601c031600150750203002a90 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 25065006 1250 25063756 25063771
    0x6052802010b03100606090902030a11030703020307021506030a1b0b0a080f0708040f0602090f0d03020c030d0807020d1110060b0703080105042903070503070f05010305010b030601020a030c030302040e 88
    0x1941d42c20b1601018103241c448006400386601e03080c030820280d9486480340b0212106c51000603a6510f03040350000151411020140d6080c0000043c491075a90590086100f504554203480408000181000001030300f6203105905500480141d400f1804114061030282e96110b9040d0086d6940c41c1d51084030b4000301048004154180f08111801104002080d400007d500c2c0c00d03041454581c2d076101c00e001080c2806040d99601041440341521840c0210048100c003d0182c40040c404c0d16000756110011400b150281c02202018001c6034016500e0034059421034014003401c0401b09422075100b00c1a40d43c030311540c46803e0065a980815114000240a45a40340d0fa9554440d041c080c4c800701e010303130040d80103514210500000d41c115070a10100c50724070b950314405040c11000000e14040d15074000503410700030240c00250010550a1500031180c080c0c0b814010340e82e89103981c086a000c100c80c2c05d03002d40c00444134280000c1c03140007084680351007400c0040c00d058603091302c0e0071030181c00c441c00d0713 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 25066256 1250 25065006 25065011
    0x1060510020d08090307020d0f0f02220e0105270a060e01020a11070b07080901051903050a0b01090302030a0308091e0604060b03011a040b04090f0503070c1505040605280201 76
    0xa8a001d40c000031244d13000005030002c40c5008002c7d40031800740082c036107001d01485440a42501085444010004115002010004482000300031800c00060817003100c9102c0e460140d04140e0424180262403290b44402e9121032200205480d440411004605910700c034020f8400d0a0b0014045100c1e61074a04100c100040c1c45041407100070b40307400d280203824252070b40a81000c006606150080781c082d50f50040003143c50340381e00c40060b0303050b01858507410050413025945d910000e034582d0019201c0c0c00c91034030038865000b1403001502d07010b246000180d015003100c035030040840e0280f20290b80051300300c2c04413007400020300c02080d07810100c51009001600040d040c40140186402502c1c1e005508030002c0001421481494040326101e158071070040f600c880c1c1c503c2c275030340d100e42c81816080c1d000050302c0307610300c4280381103600c0342e00c2140101c1d440500c052f0003050900114242da4001c950607101c551400381048003da07034a41084081812030041401100c7ca00744002034110f0076440b668001 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 25067506 1250 25066256 25066273
    0x4031d0a0315050a0501060801080601031707150e100204050604050907020f06040b07020709050c090f13020409021c050115030f09020a060c050f0309010f0c0503070501090b0f010503010204180e0106051002 90
    0x203000e0f20345c10380c48041000000e40041c0262030011440070304403540100290014000442c080710540940040580042d0720a502c040040c40190130030914a0180d8044c0e40c0a8108452038008a014038016103030401000c1c0001d002e40d040103888181c1041a90044401e0310a420000a00d0710300101c0741110104207090510206580401c8110081c20440d0003d000c6441c045d0341c03031242401800100b40c1b20b0601050103036481e4a40410001d00f2a003c040195611034403251f080b40079501203a550301d035014007850446a143d1091091505039442d1141103c0c551110f554118040c20b143c1001c0600f40f03954600401c01640c2e0008a180104840d07218000d183da454145141840346d02084480650802c2101e400700d60b0380001c030601006541e0406849000190811074610300030040005d10035843c060b806401c0c8440e007800e5070300c610800400034180b680c0790011b1509038051362140c1040410000c402d02000000340e0400512661108000a4a199118005052842d01d1044200942c208919 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 25068756 1250 25067506 25067521
    0x6130e100303020d0f050304110d080301061805040c09050607060b1e09100302010206070f11030a0302071407051815090109020309010f060812070c0806160908010504031d0a031505 79
    0xe084005811400c00c1070100061304800742503448020002072002304885c0c0c0041300341c0c1c3c8802b0f2980c106a001040c60740c51350384a640c041c0c60401d101c1c0b041c400103007083c031000803e8a00382c0900e0040050b1551264040e0349810709000c2c180c0c01500c3c04460081d2280c00c410300d941c4550030420100003d0320b040061074001c0704107010400c0f00c040c0c84403880301c0b000107050026036000a04113030044c040c3c2c94003c0c03400000c2c1504440b9030510003207600741404000b85010005034503801400046018221a503040307141ca64100c0d0780d0390414030525400401004444c4c030205d203000d00c0d45900503480020000408540c1c0005401d00b42c098020328120751303002c810301c082e40303c091060030308030104454200421404d0810721a40c41d049614081c1d40f0b50000182c0304100308100e8808030083c80c4510496850382000003021070460b500310000000161221b81c00036610700140a401d000300e41544075120601340e60070f9403120920b100c000c01608012006c0d000000079035289494030000c1141180000c40b0b003400340 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 25070006 1250 25068756 25068763
    0x15090f090516080601050d23010e041101080c0d02030403020601030c1a070803060a030507030b0901050a0c1d060903070308030414070305031602031903050a0216080c06130e10030302 80
    0x200030003022450001004440c00b007a4100a0001d2218280100c1c903994200c01206e1a1258902c42134050b820424032060342c0700c55080000c092910701000c00203581c1c98441c802c0610710100e8010380303d080c40440b00308055003d61070982d000594209141d203094840c0180d442680d00c2680c0490040c0c4c0030742c0042040c00886031001000d8821407000b404810120316640d401e602802c2c8019061503000004540980c1c0c0e1761420320000d42d403204c00d49000965a00300b4540b1b08904917031185141d401c0800240700d07480315108480c205d1925440e004005c100b4903007885903404005243e250006010804170160f40c0d02004800d00031441079600395a01c1c589403519150310706906500c0c0c4915406400207100252020003543c1900e41a00e0011400e04014000030740b420150104070b5064a40d594548020302d50f00000801c00d040c115022a540c110a070b030360340da00d050024410700c0d80a80202130044240e1070008020700700701210700448000d580e04c0f80710740d0f0407032031003961f09541080030700008000b09038060 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 25071256 1250 25070006 25070009
    0x60601080a0e030d0506040902180a0e0607090b09220603150513020111010f0218010215091905030c0106060c03090b0306060708030915160e06030c190915090f 70
    0x4401c1031000024034107a80d540d074000d4442c0c281210340c940307001445607110707035101403003564000348200c81c0c4886488065984002c2911290340103410991103441404001603407501400c0c5c29914600050702e85211010140c0040310941e82c080e00b40ca5003160a0014604480d01801041200040d407a01d5850004806000c40c888400002c4c01c050412141c06182c29411171125020302304010017030055031b10b141c010180000c42448842c404281c99070f9170f995904850414110a0302214900101c446e40c24202c3e20f000c40c0c03894410340c0070780c03820000040d03400410200d542c46502102c1c140b0f081d03003011600b91100394200703c2c00646000462024181c1c040c01410081008015451a5091800100300c040c031800b0300142411100001140004c0380400000b075050f002894522543e0038090781000a0030140c80c0780703071300061000d40c18038018980f03502124013840350030020910b4070209001c1c42c07420810454548042c0900080f0009000712204088100c0d00e401e80d83d10350000c2e042000c1384884102d603 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 25072506 1250 25071256 25071271
    0x60e010906021609020a0207080a0804060801120b04110d020d1406180a0602070f050105070801091a0108040f0309080304030303090b16020c0409061e0207140a0b0106080408040302060c06060108 85
    0x1101c440001d683c0c1c4110501610800301e005a40c92401050030392500360540e2010000c1c3c03080f40285003e004982001c1c00030303588159525201660f032509403004040007444041c0081003e00045000102000514420070b4809800040101a00d40000300103803c20718081d6400b2181e401e801a03804000e02015600000f014940c081d40501400b0151b5220076204008003101e50004040c024031113480140c070b40561f4800c00034000c6140540000b00b5074078003031003034001070f03414240c03e41002c90542e085c2d01c405201c180c3d50415503a6850b00e03022404988030000340d0a100300c100010640c00002d00040018500a46002c500d0301d08520700103007a00001481102e01c1124040707843c2c902c59000c580104520800c80c0c1c0420694410704060000b00b6901c01c1405800907060206540603070103030054414580180c1b410021780003d030300955140e079803159000302426910310040c0700c03040c080c5040c0c64019009807141810941c0f250301007070040d4082801c0006d1395100e442089425a40407201d10743c4200b4 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 25073756 1250 25072506 25072513
    0x3060a02160f0204020d02040b1b010203010b180402040504090b150307030f03050a14040f0816030f02190909080405040c020f0d050a020c040908090117040c05040b040207060501060e01090602 84
    0x550901008050300c00340e0024440b600e204040d0055503610740542c1d0703844540c584119074460360345030110b45591118070000c84000d01000400c03500d59041c400c0d607040340e244078202e0340f40146a0790843c250204810030030750300c19400d1001083d107483d40e11405010904c990a540103c2c24480031101400b0242c01145200b68032001080c070010388190b1034004080c2c1e050918640315070300c492082d14003502207241140e5401000c80c00158048950114a040b00c000c203007a47c0002c0c440d40f9140a60240500020b410004002d0074500141440340340070401c80d0301409225503568a40d070042094600c0c8400c2980c0114000c20700384500e1070301d0720490085030700d14001408000322503c0c105485100c0e80440b44103200c1c0120304041003d0007070010b01c6410400520401102e5041e240c0341c1480c0d0031880e2928009000f0080b403410780031242c420580901d401c403140c60605803070710003080041d2485604d0160010380901c18a4001911801014082c0505031a1200b0820014000600d400080d0348034900310351 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 25075006 1250 25073756 25073767
    0xd060603150e041a0403020c030a0309051e06030403050f070512071109090606010e010c0b010803040614030106023c0c0102010f15030204050702030405030f030405011d0907030902041107060b03060a02 88
    0x1e0301350444890421074040d43c45101d0f80c0c1da08060782061241940b0b02e4160042201050815034030040301c409456003116201004c14040030317a800386151903661250494810004500400e0180c3c01401402d0365410509161403d250780d00b508020a103004102d0322035012901d0020426800c4003140f00c1c00007540e00701024035100031541c1d0f55000140c005418019690500d03600359100c0d960001c0505d4000408d60059699000000d80e2131380b25100311800141c5451443d08510042d008581c12510f06900400e10808401d003c01440a10720180401c08490304501c0c940360721006a103140c001800c030018244039083d00c00060b09460700031032580402c6141004480c2e02c2441054210152074041d180010540d42c0d81600760b10354443d9070011581840f0b4511003600f0f0030f400000801c103866080c1d0740d0410070f1300c400440c06c3d40c02042c9103e440d031103413500000911381440780d807041c01c1c0f40780014004544800280e00c2c442080e840307803400742e600300d48503800040c45007800c1000a80200d4072000071403134503 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 25076256 1250 25075006 25075013
    0x501140d050d0305190207030809010b01030c080403030c1205010b07030e040606120902030c030613110f010f0305070c02060d060504110301050306010501050a02010b03072d03080405150d060603150e04 88
    0x10a107010082c0180340e5a4804910050014040ca002910f48032a04659850342820050041a012600c0075000e600344044181c1a500c07a00030b401202420380c0741c0c4941e540f103903030301a03000d45100231080701048101202c082c0300703420501a00e802400070000c0b4682c0c2d0111406e0003400940e0140c8664001c6080040030017031990b120800036a860300315580014040d0303081c400641001c1c1d442c01602c0d03051243d5000e0180c91090343c121155918480c0c4a103522860265041c001e40029008049010840001c0000c04045c0a60096030b4482d0503441c10801c041a10303800140590003081c071000c5800d940e440c2c01e0003d42840e10600c40310740c040001c181e08640c54400026550301c414000c150400c000812110076041c000d4100ca8480c42004091301c40301c58560480c13a121514100c41c138405c2c0344002400c1d01441400050707090550340c00c120180d10300b500b01003d200f1030b03198034010740e400c8950030040c0036040724440c821203024001d542e9020074546e00c8907441e02c54041c5103800c20500080d800040c00000f = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 25077506 1250 25076256 25076263
    0x301050a061a0a05070b1018050402010f05090301150603020a09080a0c0504020705030d060803090109050906090114030a0602132409090b0a03060c0e130c09030807080c07090501140d05 81
    0x41d19070310b04420358801d68107404944a00800e080201400950b9007404184904602c41009603500c007841d0141500300100840281e41007a10301901091081c0e00707071030b400d512800c02482851005000031031a00c400080c09045001142d110b00e0000b540440c04111035170340f2210700c00c004d081038001401d121002d500d0b00302c0c28400b43d00c50036202e5071b4000703103207410040207105035214086040c40c01c011140d030340c2904640b40c0d4440042030340041d41d070700700215040c6400d03a1810b006000107018003e5503801c1c03680b5803005515600800307a242c03082180f010300003000c0740020582001d9000c104202035240000d840c028001902601d811804600d065038100c5501c11250004c440c1e81d601c1c08507c0081c41004290340e04d1183d00080d21460801845440d0290445100314000001303aa03000841303d81041c104044039503060300480000c0d500f03601080800c074440c020380041401140814a00180469880c0c5088419841285c4007a204c1c2d00400c01c208003000303c80324110051300c0f8100c0481e51039a8140c4c8 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 25078756 1250 25077506 25077539
    0x20f030106030c05280603020705010c0c08030f09030c0f0307060b010509090f340e040513060b04020f16030206010503060106200109080a03060513020c1903020a0c030804050301050a06 81
    0x20401510700070000c6840510a05d51880c0301039568140e1038481070014065840040165895820030440703810b480c0c402c2018440305900103600340d040d502d5001d0301d800381100142c280c0d0324502c0140f0030f0103200542444690030341c5100100465440b51103240800958850340c074840d040c4141801142466101c070072a071035008030081c0034940e0030742d1345407030050951200035091a0120360481d0300307d44000b0b80c068080c1603c0300f00d0300c40341003d05520742000103541c0100e070002d40a00302120a0000511140c1010b040f640c0020009401c2524084d01c1c942a034028800c1c401e071041007030707044105058043c400c01d40901402e4010382100e41c14070f1009050820203106452040c40102d00750040182c00f0350117402459840010b4a40e64821500020050a01402018410303548a0703604800c4414034030880d189407102d00040c00c40d45072a06040110400d881c502513003580240c50281c00007481111132107001e141b00300c1d070294649081406042c21100000c01d0241c034540ba0035403d01059a42020416 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 25080006 1250 25078756 25078759
    0x60604030305030c22060512090a15020c03120a0605010f05090105040303081806040501020307181401080c0408070806040b0a0920040f0516030c090f0608040f0206070f020f030106030c05 82
    0xe07034491000b50035401a84100b40948443c030b0080f0303000305501f40e1001c018201140c0c0740d03481ea59280c031070001154032101c2192004110840e002c6c5007005031850350f005400340e00c0e0b0040c01c6e203007015803803518900c104208507250381049590f034505005c150782110014106611600e0b00d1420301c003030700300042c08070f00c550300000d020f1020380c90000700d04046100c1c0001c4544400b40075035140341010301d000c0b8081c0d0000e494400216509010340e03084040060280300c111002c0030030a41300045104015261030070301401c950b108036410030011071141c00400191b0b00070060b42000305030a03d41414a0b401852004d0500c100ca02d00b81803040c0c0c00321b541e0001c5004848080480381c10700007010800280105001070700c808241d0708000070011003450700e101031981301c0d500c1d8509001800c084101101d03685028003071241d07040c20310001800002d1003509100e0b44148105003040b0440030580018a554000001c22038101141440100840c20554003141641c40141d000b4090a400d5681e5038010380c0090103102d = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 25081256 1250 25080006 25080031
    0x30f04050d060e030d09060e15040803060109030f030807030c08090c100e130e060106030c050d050603070e0108030703030b031f0209030a060c0512010807050906040209010c0507090902030606060403030503 90
    0x42c803000c0d610003034201d02082c0c2220f50300c80a0104803c040c049100060700c909103080b160541441002c02d00311021085e9481c0d054160b6120342e1000b40980001d015541004034151f004070001c0c2500070100c154030300a1b100e5400c1454107040c0182552084070100c4200159001884480c000001d0070900856045480350008518107a00311004050805074aa1040f44601d05880d80400c642c0410032480400d0300f035401503038071200158141d59010100000144040201c500410443da0040c0d800010003001c0d1110282d4680315008041001e030402070a9810002e80781c020190144554a4640c0e02a0b003c0d004081c103405400312540d40700114a80c00c190002400202c0b07940500c41e00c1d90407a031080d4104410f00340c8000041c682c2d049001d030b000c82e06010308004039003040009203203000c0780d0340103020030182e956080500010790012001d580c1030000b5217803000d00003541032100c070b0041c10700c020002500500c14010145484c802801290049408010500101c1c0c0d02008507070380540001903a = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 25082506 1250 25081256 25081279
    0x10c020d06090204021603080a02070203070519120b0105130912050706020d0608060402120705030a0201121d0105070f080c0717070b0a0f0e0115030201030510090203090703060c02030f0405 83
    0x44070107403101000080d84a031000032000c0300310541144c08003005000c0d40d034400c07455483d6a0100308074030400a01a51580c8a0172040069103468168031444594032042c2451843c2d61700d0342080e24540100048072002202c2d00188060705000c0341031500412504414841d07003034281c540b024483e00d0804801c0400800080c104144035064040b20003042038080100245541c59035070030b03103582d0251000c9204200c150f94a80070502e0010311f6800f5118010007a001c3d00003c0c2e801550340c549110102c043c195103464521410b1002415400d03030704000c0e00c00120306440c01200c000d100b803610f040c04a040c4211802440115014641601c010aa100c1d10b004c13916640240306030440d00903c0001010608102c3c200314207040e558205500000c9102020f00c84204013100c4035082c0d40c12006007014500c0303101000c00240d84030345c1001380c01c402d114107450400ca844040410503640200d0790b0310071a9220710820400c0040340c0c1301d09940e9901c0c506c0170790f041c0920520260711781d00c181d100d1540300d05040c00c3d8 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 25083756 1250 25082506 25082513
    0x61202090a0306050411010c05030412020f0d03091a070503030612070e04080409050105060a0509190f0b0903060f06010516030201060f091b090510030e01060b0408031c0b010c020d 79
    0x121034000c0401072040300c0c038a9803458800d01402c81103400f2101049910403040c101d50140c12000c010a078000050350500341006590710180c416200184e80c0140948410103640e2196504200c0c0340d802643d590001c5418454000001c0081000c1c20351600f0040158801045010090b290032890865004256154007504286414641d030800310840c5151030500040040c89130082084500c113031002d0040341c3e603036820420740f8002c1445890106a0802a01c4181d29149900c0b0655054840d803022170700b42c030741d03403007072030104407500003840c50900020459120301e070402c20a0781c80741c10340b0081909494108002407150041c28150701c1022090800f00f810103000f03402200c0900701320000c6d54101c99030f4064240140c4614a05c0541416034012220750700d0781b04001d10f0382500d0b0b0203000b241d1590041142203000306000d00d1304c4040f5543e0b625010440341c0c049c80040000b880031f40021a140c10301c000420020303410000002c2086481e1030a501026604540136840031601102c10b5469a0020705 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 25085006 1250 25083756 25083761
    0x503040306020f0a0e0414060f040608031c0f020405010c0305030714270d0201050301050f06090a0608060306070e030a0209041a0106030606030b011814010c060507030b040b0607020a0612 82
    0x800081c00c180c008a02014024100d1000d031802e82c0160303032000c81045501040c4030885a0800055012400340d2001501c181802c0048410229000e400000d8080d0395460786800d5070044410104806040500e0b100004551302900d4070116400d007046280600d4500060311210340d40100800f8400084005030b100d5000e2401c1e50b200d02000780e142540c80242224050360103400c1403480004642d81c0080c01c3c480d0400f501002241641070b15910301d1030742008108501c0002030b014096020000304444c81e0700e9100c8003400b8000385059140c4009038105401014100700b00244051f04104001c0844501d40d540041c10b0b501742c41c0c06580c000078a46560138402000000c03403c401494100318800041e019915034002000c803407295900b0000010904011100f81446480341c3e440c10741d203403100344007400222598194804050401801030105503032448203807241183c070200032a9a4a200060340c1c20a4054062000c00407690945000510346c0010040f4580d8040d440412420101d4100d0781004d56 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 25086256 1250 25085006 25085009
    0xd0b0f06070311030c0a0c060801120b0f100504061202010305090607020303040b0403030f1a030715050405060d09052a0f100f030b030307061a09010f0b0708040f090f0507080c040909050304 83
    0x1030b091b285e500d0143c0c1004810410b141c4200b83c0040c1c030400c0009440c070001d0300a0f404042c0e00000004158a5010400c801481301811820102c1404540000e140d6101c0c414003004000311030960303125143c50b0001400b1154020003002483e0400380030410156808803c495000c0c0e4082c54507000742d122130904134000c00b42c00b042c04440720314051a0306602844008802d4114008408642c0450740b555205001e00344089040800701f40140410701c85e80c40e002000e003011503c00c40001581030f0050702d0f0103243c490740c60721344503401120440c07011075441d0107080016500f50035100c0c41700584030400030400300c0c8080c0c0b1044003040522004211242e22a070800112044000d0849450305481e080c07660003002d21106610000c0c050540b501d00da810400a102d040798400c003200d40c1c0152034030f40480c50702e43c42600200d0f060303601088007043e0081420b420b03202400300070600140101c2d10580384011144080c0c801020b02c05500c0400508035500000c40707041e02c41100001ca101b060a1030120300e140900d = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 25087506 1250 25086256 25086277
    0x130504080f0406030b09090d09030b19140709050d0b0703050603070503060106050a02010b0d020a0501050d140103030905030607140d0b04141806010f03050706080702030705010603080d0b0f0607031103 88
    0x7400159913038140c0000344600401c480610391501e82d14040d42d955000303c02402d01044081e4410000f040c80150140c1e030060071301408500752110700d410f8004a42510300700c5100c000d11242804402a07208145602605081d10000c181c102251074000d14041c00a08100c00c02d83c0710400030b681510f0a00044000f4480a400c4a8139561180340240894000000000042d0302c2c2c00000c072054900040c82c0c2c100c40390007401e1703015290300741401100c1c1980302543e20300c0c40c95140c2103450822121084118020741c040c0e030783d001080e4200000c150410b80302400f11800c0009070640b1001900c4140c007100c00e44950800005404030200d00032030003a02910501c800090a150100710000315100c4001d01109900425510603a0b25000c4051641c0614000a8010f03401464140300322806100c1082e08410280122410f0041686d96242510a503400880b040440440d800d00e40d5842805042000074089442a402c1040c0102082003801000750150803c4505030443e00c00020034406c442c00030b043d = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 25088756 1250 25087506 25087537
    0xb030a060e070614041811070f0b040b0903090a1503091b08010501270510030210170702030f0d0504080f04030b0402030606040504031d010e06071112030913050408 72
    0x401c0084035295000e83c4940c0010401810404035a20180021101600e008000100d175800c55808000300074104498880e8040c00208521004101a803400a80441c810000843c240c5442d1501c00c0003e50050710102c01507005222000b00d5aa9034840001540c00210039102d041038461001c070b02801e0340840207400160202e4420849016801d09282a61211070090055981c1d1f424081400902c1001c4001070244581d00142115029000325801002001c00228166240d40004040e031061512003008101c0b01c2009011840d1210602c5500420724000ba60805990070250031061182240002040b5a20f100290400034040140c400e41d282050781180c0300c030b440e0702e001c0c0c150364401d403800d078400d2051400041d80c516188c010a07200d2035040c1d03038101460050040e00c000c40c0b407640300c04905200041c0764200d42921080b0241c0708040c022180d0301208008a01403010407036458180b107165400c2040340d0320301520384003403d404540449100151640d214203002c1807074028070342c08900004 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 25090006 1250 25088756 25088771
    0x1d010e190603020c2b08040507031401050a0501080f0c090a0e030304050a0c05030115030809040603050102030a0603170c0706050a020a0f0c030b18100209010c210f02010606020606040b030a06 84
    0x35810750140c000e094415081700c0b803c000f210b41010b507040001611780c0400318042c102d10400c034441e03d9500d80280c0700f4070440b19041d8896544000c800820340c01100c9aa540c1c008009072240203000d6240141394440c0503040c5500720619464440d9140c1e48070314000c00241c400b195400c04030340d0041030240c1001050700d0322818945803070754903907040400a6070310342d010850118007032606210701c0142e000d1105401e200c0074a5030f5038502c1c3d81d4204040d500d034041d0fa9103400001040f4217000075031060707800400006820b41185000c1502c000420000380b5544010310540d600d45400007108001e0302d8007800d05549407811110103c4c80d092580a0003000552420301000411216952070415640300700d0303098006e0346c0c602c50030f10515840000000031562001c56001a00c81d11a402032900d40010301d13100740394141c1a242d00f00480d01452011b880b020341500841c061981c0201007103076201030b901c0240425482c00300700030750310003014007554859036864943e15103940c4c04002d00c500443e8024030512800 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 25091256 1250 25090006 25090019
    0xf0606050a0f09120807030908030c071203020a020301110c010e03030c0906160f060510050103021303060203090c150c0d020307110f130f050109050622050705120103050303070f1d010e19 82
    0x40c1c206d080200e010819550b80850007400202c04c3c1c0d0684982c06d80144403081c6040c65050078040c4503202641540a040340000c00b5840a0040c00b81135120289071603030f920684911142150b00000700403116800a00a000f01012540c040b189181811500c180e100c411020f010900d10810f040d00800f407458941903a810400c0c560800c600ca01980d04032a030019070341e180190141d21504055500c41450308406000294542d03000d50b81002c40081141c075040c1810000c101c04060182403082c14031402302c1e0000d03d01c44100310031070899105201550a0120940d0789080c004605010b10344103210401c04a0a0f81d103c518245040340c0d0242424003440c50401044001090300b0b0260229050800c000103815080c203502e01c110b138140c0720019044181c4180c83d800c00411000d49000c3c1003080070021811100145110343d4041d60094014660384e00f80b80b0f0000d04140240c1001d20180001e600c00000c217030702403c440300d40c1c980d000c0c2081e04a10040c440021440c807602c0c07012403030542c0c0e1101c2c007080d03c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 25092506 1250 25091256 25091273
    0x108060d080c071203030c09030506061504090606050d0b010504050a03061e0f020a02060907050312131e060806041808180618010908011a0d110607030e040f0606050a0f0912 76
    0x8603800b0f510104032180107c07100f2202018607000140c000d0f4000000b14100c1d05280c0000003200c0150310281d41000d0711009114107480b0660f0020b4009000810f2095606019100f0000c1030742090a0051600e8074140216003407103c0d6110160019a40b2400f142001e5a5a0a60840010403540410102030300959146c025008542810014401d15000680c40c0200084140542c1c800900070284810100c240003850390080212042d4902d217900001051402c08603200001c4414100c541c3c80b04cc100344004003404001040c1a1040e8101a84030f082e11a003400540901354100000c00e5036040d25070600304403156000d00c00c5821500000e00d112440e4035013007503140d2240c1d003681c2c0c6280180d5145001c4c0d00b40d9215065450f02d00c2201050703030f20795103045440800d103181724004400040c4144000a1f17056000b209043c1c1c04545010440242464948500400510100020080c250500740d005041740142024001440503003000d17600c20601811519005025403004500e0350002880e18495 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 25093756 1250 25092506 25092539
    0x40e010f150306080c21070b03011a030105010c1101031515120b0303091903050d1206050105070506010515040503030301030c08010c0207080607050304060e1603200108060d080c07 79
    0x4030340300350076862215644030340100310881d03601070000e0100380d070030108009051000d000b10701740d03104c89200e0b0840702030018004400181400300d10035403250325004403580b41b480170005142000300100018420f982e00000004d03852170f0840012400c0c0700c4c0800050700107120040423000117140783c402c0004c40042c02811001c580c6265a0796a00c00001c09243d44d094070071011100e54560801e102c0c205090038205558210b0b48041108041c2099582c2c80312424403409950620002e40d80c0942080540c6207030140c103005183c01e2900c24078100c401e45550b522080c060161600c5004031044400304640c124041c0d80c050040242925a6969280303410403c0c101581f1401c40c4a50038542e1032040349001049001c01c0b60030a41c0500410f07922104100c07180c2d40b00034012904640e5401000e4100c2404101100c0014880d00e40c1c8e41201e421800c1807807104000180241418075018070302e24541e6406000c45070040b00c141d0741c1d00e103511081c0c03a04030224024000c202503580703c0ca56002070300c120603144044 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 25095006 1250 25093756 25093769
    0xe2107080d09060c090602030403030c150209060c060402030714130b0301020c07060909050f010b0711060f070b040c0e090309010309050307052e05010308030f060a030b1e01080106050d030f05040e010f 88
    0x51780a54801b800e98890141d80300180220b0307001c00c0c054011812421420720f94211840006181021310700003e842e5403c01200d03400290700400400c000c40c02c040081a01810b00038a2072075401c07850100184008a002c4d504400c00d64503a246100907032401d405549904207003400f6614443c0c0c5940c00104004c0e0303a841914001030910000c1400009408001030580346100c10092038406207455802d511210344004541000c0f0030416812000c002d480034080c00c41c031603400415541098280090303000707059000001c590112a0030720001e8080041210100f203002e080c0421748407482d04299041d4007503c0400780a81c040c290011030400d100080d1040c0d50140020080915443c4061803011280b09020081035920300704081030500e0b40b1440201c3d80000010009010030351a07948600e01010161541d81280400c071a041c0d4030100d8010300c5c00e001d032642c0c0c4020080d00c1d18110000d0728070300310710b0710203400d000c200700b1220300e6180719408440182c540015041d081e965548d8030384200f94298800c11 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 25096256 1250 25095006 25095017
    0xb18071a0a0311040602150405031201030804090b040c021c0e0301020c0304060207080a0206030105010327030503150306040f0206070807060507020c010f1e081e13060e2107080d09060c 81
    0x82c0c1698070f811003500e059030780c164014013020450000300c1c0307400ca03809001070b68244000e010030004609401303041e5010711700c203103265078075141b0305103103081034540e0b0200f9184110f0074582c41d14102580040c0001e014540c1210b40b0394100111001501da29812a1030703da015400080d00752074100000008208444880d800c0f140d9159640d0b861645840c1c142c00020352250040004014a41c82508100c0303454007140d18003c0040300402c00400380c00c0000d1822000f064010013000520758050a20081c1c541307058001d40554501385e52031030400c0c903d06c2002403083c54046000380a100b62802034540c4941d00120402080c2440b8a004c0c1d42e0705044001340e40003c0103142202d407140d1240c1c903102c0141c26028081d241300304200e00c0542d40e0440040084002e00385c01701110103032040031081c1e0750085000300103050507107105086c140141c8030b08485c0b0084503031009054569192016200612800d00d110030f06884070514540702000307100c4d03220078081e0b05051190200a00407140e001c52480b00c5903840e039 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 25097506 1250 25096256 25096271
    0x131107050a05070b0a09060e010504090c0801030506060f13020304050f060708040c06050a0806010c0201050c1b040e01060b03070503060406051513230411070803040c0311010c0b18071a0a03 83
    0xd8004d24814140000c0000b0186041000300500945034800d414105040280c1000e80340e0200e10116151549054001018000100b040c408240290ba420502c282c95178801300f1010004203102c0c00480000c01d5146900000142c01d02805024805150603034209540d0503080256005203158801c1c4d9083d43d8203a0801800034007030b4003a40032150315001c0c584a2416594841006580000803000c00b80d041c01b03810007050760000f80501184090031410301c03030744540704111001e01c0126075800c098000282c0c980b00c41444107108010a0fa0341c410407034502182d0340d03501e0f0701c0414060500d640c80a40c000c00211420400000d0345000341c0142600556010000d0f50340c6c4a5906142c2d20141050045058002407480c2d81c0c141394205284510051200c0c42c5001850350300d5550550040700d05a4804480076002e1003004110748198180120902c0c0045c81143c0b41c0e00c0340000d10501816480900c40d11410495003028180003102c01800d41c8030028883c6000079271250b00a50100101e0000640340004 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 25098756 1250 25097506 25097519
    0x50904060e280506090106030b12030f040602010608010204050307030b0403030b03010903050a030c020a1106160c0806010501090927060b1008061201060803090603071704050c1003020a0c02131107050a0507 90
    0x1654804c0d0001800381c8826403030070509800400c2c80102090f005400f40202504043d0200002c0a000245501480c1d03142c5c83d142c00203003142c125400907240c0c0d90040004001590300040d82c002501d400c03242144c020389851a080d40100307001a82180c00d542000c80040c00e05400c20040d00701c5030010b840610081041e910b0882e1940c6260300c000300010b040752088445424070401070051194915601c040c00d40a54888903440100380d8000c010301e40c001c10061005582c05070500c2c0040c13440400920142c01d0380c00e440c0d0095040054240c59030601d0039400e00c140b1201c0d0704409007454000e04100200500d95400600405040741c020f409042c1e01c030311211b10b00105116100844a888002c0d5092031581020070138158000b403e09000c1010503904520002450003040703008500c243c005204905622081c008030750848003186045c58818480070300b03415041103000390050340c1220924640841d651400000305022a0b080c083d44c1c0c004100041040000070b107411040c1d0092046a10280e620740c5d = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 25100006 1250 25098756 25098761
    0xb0c0403120e0a05010509131d060108060106090b04060509270a05010905010b0a080c0702060405121c080f04060905010f0906020304020301200a082203050d1119050904060e28 77
    0x447ea00035200c03000315291001d403644881c4844400d400344100b0a00c4a0720311500c1e0030020380140a45400401c010005641c00a04500c000c10b01004000c3c289440e085021780315004130102d07180500e030b0101c00e1103880140320316152258919142103440d20308007400083e0040c0302c24040d40d1003a618100020400341c0a18041e210564403590301c03024103986104070080c01c2d4000d00f0040340c2015050102107043d69506002424004111000384100b410351807242c40c00c3c41143e810402480315520a108441320b004c140103074042e42002e008a8403816924109004082c051080013100d464104003100b0040c454005600841c0210024801707030f9800003903032020424072401100304480c108038980c81540100902c41d03000000740003922004500c2501c5c0508140f52000803070004100240040c0310362401c1c850782002060341588142003c0c1004591030340300e07446010782000d020010170b101e006075aa40e08002c0c0070300384880e401d280506046d0b859510701614240c244030a403200c0021071030300c0000ea1 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 25101256 1250 25100006 25100017
    0x30105071404030204020904020706020316030b010c03080c1605190c0504050c030106210c03090615080c01050d020d0207030207050a080a0b0f07020a021503060a0501020303040f0b0c0403120e0a050105 88
    0x3440010b00d0249950308000c002d6001c0c84425800c15024002c02011417040d1000c1c5101d80b0101c2c0c0c5404001100f20001402c4602400045051101d240036a0011030790100003650b2141c0c00401541c0e0f1280ba0804400c50340310072590092051103200341480d58070201130803150000c1d00c507080980810b030f161810081500c408403000401e03001c0a00040002d0391160710300d028a6188201d244800f800c501298906580c0080d49501c0403c1d183d4848500b00295803150f501c0842213486000710040c1403046003034035030400d422003a04124010403203240c13244041d411541c05440f1024215915401480d0103903c80c1c1c010301c115031040000404c0021003400c0420002c01c029801440c3c11801d503036030300300040c2240c40605070800310b104003a00e500041e04d41448100c414002012072581301e02c1c01204019440c1d80d2078110038115002802407000080800c0b04100c1c50a900100c1c0402a6036080e001d020f4900580d031000c0c100da4189840c0705002a00030110600d0440181c91800d10191100c2c015103461190 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 25102506 1250 25101256 25101287
    0x1305090303131e03020706090e09070b0307110a150509030f0708071403030709050307170a060b030a0c06170f010b0703120b0a0b09030c01020a0305120910050103030201050603010507 80
    0x2080041c0910002c000064042c1e88900e400d001c03034007141c0c00810400d14241e101240982d1145d43c0c140070440d00000010010888601e01c85000d1801003030068032500c1c240324032041d0700e401002044580c0c1c011280c0307400c40701ca488201e0b103c940c00d03802c0000415600900d0200c03000c1c60720380071a640c21000300440b441d0003460850303d0f24041c6580d641c205c40b0342c402c0405030307804a5220200c00701160140000c0d8014501c1740c2d10504d41606120070141007405940c00703001403c5859a2031004160046049040d0725003213040050043c0c3c92102090818120000013480c00a5003030003c17860300c0d04400b6401030010500307003000c1140c0e02c2c213051040b514828010281f00c58414007160001034801c4000d030121021011012078401d20a80c040350307a41c0c0b00c682100941c1c12010541ca441070900300310307a04004109100400300300a241d1000303000351040200c88510300070a03400207180c842040090304806084450b0401082d83d407818000c1c001e140680d0340e14429403c08001c1400d1174401c042d400c442c03444 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 25103756 1250 25102506 25102513
    0x21f030b1807090b2107080402030111030714130e07080702010c0201060e06121e0102040e060301060f18020408060c030403020105130c2102100906080709080604020103050408090405070905130509 86
    0x614901180607040f01c56000170700c800d82c012401000e00301203100d6001d00000e4441e030030076040610405003985c035208035611113010280108000c01d58030800c1800181d150350241969410110f048601c54082500700360201080c810521000c40d83c402d08031885424145e008000c000350b4440200d003070320301c580300d600d013940c1c011400f10b0000c0c640402500c0108622800300d540c04030a890b0120604a5030f0541e404080c1d601250401c50844107104c01c582c018011002004514145905031220300030a000b401c282c8201400300006c0683d2a504841c098401441155030920301208003001541c401c035400c400650034000800c4140d020502c6041503070750702c00c4420424070b0030813514280011001c2034280440c41901c01c400b02580719016011a40c1405079140c0c8080742c20703d6800703000c1c0c40024041d0300c1006a0a10304105030100030903a030b9003080d03091130081081e0f2994206485203004201030107501601e40f00c24407603442e4101107020112202580c2c1040134050204d89582101c07021100d54020344c1 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 25105006 1250 25103756 25103759
    0x206180304030503042102040c0905010210021204140a1707020a12020904021003060f08070f06080405030909040201090b0c01050907090c09030605070203070506040b010e1305030a0c021f030b180709 87
    0x3080300413030000c8026086803403550714a41c7c0009090300c03002507400000c41c00114090181d540d051002031513400780c1b070000350b280c19003221580c800c50100a0020b080560720395940b420400040c04111034203600160006041400b41c41e00d002c10380d0085134124820a84401c002030050f40b8418a09035141e0020090115031752240c00340480041b145045a04069403401c0200d0b02156090090005d8410800142242424048128339001441d00001c0c188003010b81000700281e00082100d420300f03416070f80708880c0e072100d10060316000c00b15042000e85080129074a4942201540900d1281c40d143c400c503011940d41b000740104960100f01001c00040000da400c1c0003054190f0049a044030305881128941812a02c0c1c1c14105a81600e0032114540c1103801000301c0103001d008242c01c82c3d500e0100b6031003480541e850a980e8891000702805000803a00d00805541e03c0c14081300010b1807801c0c0c00000310303900850040040103040c0f0254070500403900c034111000c2c414428540b040400780c6403c0b8015 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 25106256 1250 25105006 25105019
    0x1120e030702090a0e0d03020c07050102011401091a0a091509200708040504021603020c060a051801020106051005071703040c03021309060612030806030615010c030201020d020406020618030403050304 88
    0x102e400802525000340c0710317041354810000801030340784442d010303903001a169080f000c405800c060941d80308504583c10f00140c0e82c8440c4031002c0740c5045400da9100001c3c6101122401810394181900700380c0e012624820000e1003594a80104030119110003d40e40c40c5034498030104202c1e81d2000568400c601a40307078600c1c00c40040c400805085001d008c909051131366030000141668003548000805059805500003050340401c448194598125491414055031007001003180c01440011144038035211906441da034000e60062000c0c1a000e0100055903465a1010340300340c2c00440101c3d40004000e110902155403542a81c1c001c59100c0c06424116103140c0030041d415101e0000c0c1048680d6800364240010810720031040242500902129951041e05018014400040c0150b0003504440200580144090304ad0b0b810303001c0c01d0030500300b030100c1410b04030300a004000b207203182c0c98800540400e03081d4000480b1841051644c058000c03a2070300c6007034035449006034400100140e20034001400076 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 25107506 1250 25106256 25106269
    0x807110d0c02040605040c0c050d020303130602090d05070b0417030408071205100603050d030b010804030c060e0f03040320010207030b06150903060a060303030507030207023f06010501120e030702 86
    0xc442c001440460380c0f03503d850010341180c42c1c1c80c44102c0804e07406410700040041c180b2401c8854103540c00a541140b600c40309842190b184605c0080c140b42c0c0c00070340c4e40001d9850305d900b0400c180c0c010045401094590b0181e50090b880f5002c0c4203280307117040d50003000d1407600004076401e4a11601c06080c0c441e242c00e07100042402e09050444440c021100030080d0401c5500c40d800013140203d0003022a07082c4082c015040703c8100c1820350400616070104400329400c820001081580174100045a80d032156000e8208a10301c070304640c8038000028000180000c800000e410601864001d680c4214054016651200e940c400140f1800c042c000040c0d0b1890030036603280805803ca05c0c818641400d400010f81450011602e1842a550300c40c028400d041c2e01d482410f82c418101d0900b1490030100342c000035008440c0d0055480001c04e007201619406034101008845642e44441860601d0002039886440b41001d0080600090780203608204042c1c4d28041c250b01038002c00c000c0c1d40b604d01c20743c0a1224 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 25108756 1250 25107506 25107527
    0xe010c12051008031309050a02030c12061c0b0103110604060804060b0a09061d0a0b0a0b0309030c07030311060906010308040b0903160603091704050105090d1515060807110d 76
    0x30055240400001c40d03003028001060000100101c4448946c10035243d1011203d024140e03084ca54414403c0bc18110f88000441c0d0076003480300c025012540d58400003a203107044140065411110613142c5500b0004000d1f8024103981c4141d1058086c10150414002103000e14450707103001401090101c1e010a190342e1104000003030107000d90b8a003d40b00c45a002c01d031007181c0e11140ea160f6141c05124880501004c1503078000b80030fa04180241040d10b4001550140c8034003ea48d400e190000204500e82801c02c2100c0754184107030261100503650f820b016040040c0342d101e0090a004c0d40001404060300410414107032507020b1030450070a414a41c00b0500c075004044820303094819081e11084021901040d54000c4c80c1903600883c40a030240b80c130041c83e511054000300340000902040c0710b00d0b0303000815200c0044040c3c0b4400011000ea092803800c1c401e507241d603515042d10f01580c0302800c2c4481e04640302607401540f00d00f0b6140d00c1e00c400c00c030b501404940c001c40083e04103184074080301e44203080420 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 25110006 1250 25108756 25108771
    0x1060b030c07120c0b07050c010b010815060d0b0a0807030510020c06070804021c0c090c0302090f220609051503061b0307030608010e0d02010606020d08060103050604090602030f07030e010c1205 85
    0xa132042501da82c2e128040710305846450105001245000302c105007401440c240314030a20f0940d086051070480ca4001c403020447c85885601c010a03864101c10499003c0054a000141070b0442556180e030f8460b120103881c001610707180034058030039582c03040c01d008480003080c140004201d940d075000811200f25034080c1c4101e90100b0189290200c4810101c10900110702901340800310a15140300017045854006010007803500500c1803014983d9006000b60b91640151110009912a12251910719141444005001d4a00303c0b0115940b11141d103ca40307d001d040301e03e001113900310000c00d55101c004403107141e0040210f404201d40e0701007030b80146800259a08001c22440c2e00c98801c1070079200310060082c1309a0007000b4145003182e0901a01006000034000b0708564110a00010034492000f021541495281c00128005449a0380000c50250f08040115240d0034107107940d8004072820399810700002d0070200243c0c21200103120780f1706a0350b4143c4514412001c0361084030041c000007407a41c1c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 25111256 1250 25110006 25110017
    0xe06070c0e011509140d05030d0506100207030320010902030d03050a0606030204121101030b030a0609020f04060b040603051302040606020a0201080606030921070605010b04030308011a03010b16080a090801060b030c0712 96
    0x3c1b0003e241003024000d5460200d80210351803030b00c1001e020140c140fa08180c1d00f10350100104001081d08031600c40d4a504280b5a241c9203180c15610481c0501b422280094142c0301d030b03804030f044960f49540207a024240c6440d040c80f80c959514400c0701a0b00907405401c0062820400c007000103184e0300d103034602005040c1008a06003d110001a04003c912101580d20707580303c044800031894000c101614071481160304000490414020b400341c2c0c0a18082e1006050b610408528040e58154039049195801001881101d031219002510341801070b5081340480c040e0740118a0601d0041d081c0e0b442090240010002c0351b0160201d100108510b0000340c021107020041c4401180407805000e0103001e550041960302c0b49107180c01004a001680041040300254607140110740e8030508403811140300c0c00507e43c550450001080364407580d80c0f0024011440010f1403030b0700f40e030003213685802c9400c0c500c0200301d40303940c60035541e43c2407108031000050844100071b880001440214500f01c41115441d01 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 25112506 1250 25111256 25111279
    0xf0302031902031806090a0f020d170403030302040e070906120207020a0306090807031403010f0e040203031b010b0316030b010522020c0303060a0501020109020d03030203070e06070c0e01150914 85
    0x46100b240d00c240c074134005640c10348421002c0224100001ea4001c4913041c000c1c000c407c0d1303507180c00643c051a500d0013482140e01e400c82d0b506200c602d00604001260380003210b591940e076842e010b80258854440d00301c01240c1d140025001c10b029900c6101100d896894101032840c861460718001d6000b150126402103a900c40400459000e106043c0c101d40b0592081c2e541e141070b414041c100d243e0316441d0004425040006014061000c3e089604507000d0750104c1c0142d807101d02c0001c0c01c60003504a00d90180d515414500c82c042015001003143d200305405540c010100e04142180501c0d90340009000c14408100400003800c2204005d030b04407040c0c900307090b1000c500074500d009a0b40704052100c80c07a030010091148610302a801d400003400e09000030000d11800341c3c003040c0f444c4c074141806424542e0200c0014603030303406075000500f0404010a040e607980e03020300c4e141411040e640914503500740302d0303000480c0e00b40c8122102d03218080d0989428041c1c6142450035500d40c00f13070424003a04400c540e480d = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 25113756 1250 25112506 25112551
    0xc060b04060f080106060314040c050d020414090c0f0402280302090603011409060a05030624030703050601031703100b0f0f03010b030a0e0d0e0105090312070302070801050708070f030203 82
    0x2c4220242c15294004101c0900d0300d00010180c540d010641c1e560754180b1000e000001c0c07800e10040d03007151810b0345ca040001d0300c0b900000b8010142c21414840d035580c01402c2041105c404141103410b0501145c20784060219003050000324019055003441014100c88107242c50311807003a800c80128420b240262a00161f003000c500b10703400a81c00f4800243d00e074000c07080c003443c01e0701142c0c2d8001001d840b0448010700e0200002d41d00d0001074003841000409500183c03010350030410702604c10101a044854963b568901159655024442628281c4d1321111809000b94841c0450340182c11003801c0b80e506c181010b6a200a03075020300c46542051070104903608940e0b0b2100b000c0e5000f00380b0706c52226240d103015101101070307441040031501541c012030030000001e604070303960068622081c80c0c1191220400000b2a00e00042c50100c001002c001040020030141c0c0000c9000c00d41e07001e14000d2041d629500f2042d00c0c004000d480600204408184400c0d0813032295001c0e40c0d2101d08a121140384490a54 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 25115006 1250 25113756 25113779
    0x20a08070303121a0a0e04020a080d050406080c030603070b03180d030b0102010c020601050105041a0c0109060504021306030c15030b15190804020904021002070305030d0605090609070c060b0406 85
    0xa00c1240459015900350f02030003298410780920030400d41e19100d44010040004540018900541c00e440e980000031605540310030310400050100c10f01190032186c0301102c050310b160024416400000c0624000502070000e04043c0c0c0c1c058a0081c0050502030f04000340c587c0b070354200810344903031001d2640c01d25010701002c12031a0903da0458600050120480300020b00b991030348001d071808d55005500401090740d0200889086480064426103022034882032081c09103e00003c1107255801d115844083c0001c81d40014002c03482241c40411840c2003150010035601240710240c60145016010482d6000d80c18401b030801445190000b9084a10000184990300707003009625414000302e0702d54202e1300100c224090b00000c50078503018074580b540c00540752180080000340684c0c81e06c2c1d004c4c01014002c2148101031548401583d8641044164810003000c9512407079210f00c08440106a242c10410040390240101d951403034004200c5441d0003010b010038034490380c0c0083d5601000200c286055 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 25116256 1250 25115006 25115009
    0x20306150d060e0601020f060604020904090f06320114010c0f03090501030e0f0601140303090901030f0b15060306190f030c09050702070b1b01020f030408030405061b04050904020a0807 81
    0x4440080c2c0b29042c102d4841203c000104590b0540d84024011468614001096035122804031000b682c0c9981000c086130240040d148001c1040704114001c1080000c103421114001c0c030049101701e003079107018800f0440340010b004201903080c1c00304c1c014490580076103003400e0307201018149900c7d180d0300c80d62240f017101040001940000d034002c0082c4029a854042c41600702058401000d007003403015901a2513180600c10035032404060600c42d0b6090b10f0503c161140844020010307001c075070303403820980050b000c50f00c002c07945d80d508080040d10310201d266603000c0b006009001c0340c0c119522071040c031030801849210001e50341c1da04400000c442c0701c40001400607601c14406891010314107034442003a21030280c815415034110341030030310104d5400003d0303441080080c1282c0d410f286088000500900c21040560b41c0c000300001000203000d400002503004520900454240760f40e032100c42d00325940c8980f004c2240d50360401c801c210310314000804d00e8000d0b000800d041c06155a9001161801049 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 25117506 1250 25116256 25116277
    0x1090302060c03070218090c010e0307030827010201020a05040315140a020d0b09010305030a080408090402040b180307061e020118030e03060106050c0601180e0a080c07090905030d02030615 83
    0x1c150045050076541c0c6c910700b100c40f803800003d904100481c0342d190740804502e54104110000d0003110b0356000c0118500964011041d1541e07030000301012402c0d103003c040c00707003902c2c0d02032256110594814030031685000b010b59291401c141c02c40e070720007031411041918040101c1c1c0714428150441000500980615000080180d030703000c4002e20304080c0d5940c0584188039030703020b13401000812008001c039038000303041745003e5078a0394440c600001c041c040c46c5419608240b01103400b0815080400003040030341c2541441c0b01488844e0420903641701c19500442c80094404108241e80c1c124090605110300308030300011405400d6941c0300308002c0e101d00d00c260005206030b006041c50b800d0900c0583e001d0704081c0b89c0240f6001d2403124041d0b8409040c8035010212007103e0040a00390850391142e8070504909003030380d07054100c9052039129508000c1038214240200c000008204080e4440c110752654000301a41c00d022210a9042c02504003d00843e00044c1520080b108000640000c00380d0061 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 25118756 1250 25117506 25117513
    0x170609090102120703060501091205030904020f0d0903121406010903030e01030905120910090e190605030619050a0213090903050f030c030702010c08041a100f0303020c04050a09030f05070201090302060c 89
    0x40d007c0018200c600030342c41382511415902901d00410008401c49000f0101a540583d030750103554210030240c8914401d60a42c585010795003410550302c89004041d01d66840418400720400d0640c00000e0303001510a07d0110300070000c1040003038040d407800c04610005050016851940c1c0c0c440300d0620f04c00e210707294460705000500d0265854048600000813031b581c5000e43d0940d007018800d81d8a00005840c6042000301c059481e907903c112500a24041c3c90042c00b40c44c00ca0820045034106e6004c1e026140c1c0180781020b0018141e200e55100340c80380f03202c440581041e26031038a030f02000200090a410780c10000100300d818088a19080218010040e420003242e4138981214001c1c00c41f422200020200001d003000c0c4000315002460740818403a00d006514260b803241d51a01e01850764036070100785030b401800c01c00803d050300483c000103c00c030296000d000c203561343c0d00141c007120000071004000c00c600ca205031070800c2c80b65026140c02c2d403043c104020500c0d202c0c3c0001d200c03504401d401c462281d0 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 25120006 1250 25118756 25118759
    0x1b0806040609020309030a0804080d020c030a0201061719050c09090708070b03040f02060a1218020a0807030506010303050f090301060f05030d0309080301050d0510090609030f17060909010212070306 87
    0x400e445600c004140d6014218110300308049000c0d16403092400003810018004c01040a121981d0100c40e0a40c04a0720115a504032149849031641c01c1514181d0165192280016900c41b1181031414000610301c09018050040c0d6070104940110f520103403120322821510f0034044e1100780b51039029000c4030000b455181d01e401505860801141c00c581c484500600a010009100c0009004142d40c102c483e540c0703c4250890449000d000251174401050402820f0244821101c02620109000b6a218454645c490881a944681620005015034800d10040000c28810740c060520018414552454042c2072000a425100103411500f0050040c0d402001030b481c1c01c00034424503d80c0703802d05000d1001d40e03865600c0d01c2d0005101c0c244c0035601c0c03a44468100700c03081c0326110030b440c8200000c0155206030700b010402000c138500d084011601416106481340d01900c03083c0f007000c80c4107044c4540c41c1d0b150010b03c0100c0e00302403c01442036400f480261040700c1074003800d40c8100320503a00001c026 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 25121256 1250 25120006 25120009
    0xc0a050606030d0509010c0807030c060929040215090121020307090e060121091a060405060612010302010e0607051c020c0f0d080304020a080d0306060806090f0f0a1b0806 75
    0x300784900d00f0414007504000c0c070103407640c01107000204c0300c3c1c2011000b0b4a4204508065034178052844008103181d2a01e4040300c1003103400e80c885c41c043c8030002010421900c08411504040c00c00b90780c003a50022004400e0003202002ca03004200c00601031411128416110810707250441c280c0035200e641607008000c008841e64050100c100421a00099081e6800c0c2440084c020940e021041e103507003100c0000c0c00e603d004954001c450341079842070502d10507400c03501684801c02c00a50320b84d0320860410000c11440d1600d8025203049200d00b4107005501c2e461a030055130b5021031102d0403600b0800c18054000891010720254440c5035001c02c1002c83d4440b540c0000f820b21100140301441007018044140443d190840c25864181e80300b41e20565a480d18000290781000c598800b084038450382130765000140e81600104201e80c070548175000d0f151030b14020491240c0e82110700c0000b01c0d40076800141640c0c1500c26040d0841c0182100140d400031306900c2081ca8211039100c0c8010591810500846 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 25122506 1250 25121256 25121263
    0x207020112090308180f030705030417060c0301090c0c08030702010e07061103040915080715020105071d0d0f0c090b03060603010908030c03150405010303120e010b0a05040c050c0a05060603 83
    0x250722407160800070394076695006081e48101602000c3c0c49a000e05603605007202c1080380620800003581245d0b150551481d0640da2607106000300400c22441c114841411000011201e004000c007941d0582141e003007081c0e000050042490002c03c202c13603a00c9442c00300d1a80300065020301201c0e8004034803155080d1601e45171031440d60021003000240901c0a00c031500101c1900d0a030384109101044c1480844500741500306103400080081c01400000602c4480c0c40440c026141303025002801503a58401c0d0036564500007002c041c1c0090211108108545400703c4254907252281d29408640d52054503181145006608259040c03980c0c1c2a0303103402490b040028561001e000c030002d215169560350780c07203858080a400d188002601002080f849070341940e07402c3c03c4400c06442000070350394074100280408000105030402038a411850301c001c0c0c03010b01a40307188040291202c64602e19003070078803005001d1164101e04001083c407c5041e08402485401609406407005140c0ba052400c2090709 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 25123756 1250 25122506 25122527
    0x314120105090f06030309010c0203010b09010f030b13030509012f010501052110090302100e0105060f0d020901270f0902030d0203040e0601050a05040e070809120c10050c040506030a02070201 84
    0x600c80d40f2000304001503400004030303a0840ca0a107440c004052707007440030070f015244031070543c3d030300c1001c407000070032a00b031001d007028200c900400c0d9105450b20b039580c11921031944140e015002807800c11065101e940991602c0302190303c01100c142c55004401c603c0360a00d400c4c80c0c0450910303511500100a5480c09445540081d03400790102c01c0c2030b0340f110021035a55802000c0c503041180c1c82d142200c1c00c0c54002c4c405486440030b618018420344c0101c0300514002c000886000e0320986d0700b00c24200751420800b04c0181c42a601400d4084240d00b0650070b1200e40c4a10094114005044401c80e150080305002d0015124050301c00419045001d20415052800d075140c62800c560060204001c5120041030700d58105c4000c0c01e00c03c0d03840c07800d0039080f034440c407498020340490b013044802d001d80258044500c500c035600e280285d1f011740c0c00c6c000c0c1009552040b0410356410358805610020b4035a4164440c039000745d0f140c03048510746035440f800b2900700c1e0802c550352090ba660104044040d541c000c42001d1 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 25125006 1250 25123756 25123771
    0x106140105040e01051504030209040b0604110903030304030e040b03100207200a1413020412050706030c09090b06090d080a030f06050d0308190518120307050a0c031412010509 77
    0x608280c20143c440100480c140b0805102d180c24030a00c0c0b4021410004442c051900a08031a20341d180c1402c045c6905081039540c1e500480c640200c6030001081442600c0000074014051495a00d6940b82100e210104843d01da0f4000d9650a0210b01664108400c1e01d00012020025807a901d150a10880403d40c000607412862504000d050183d03441d212190203841031324012440c0c229140000c14000c2d10108c0001410790300c0040c001c59400c0000c008100d11511441c2260343d00c0351105012400d6803407807680000441c0492a052108821580229182050243c4070500b0b2804800004d06009070900080e500084005004800d1550500072030880f2064400c081c8a09440c0c03101095240030b02000c060100000603011668001c001c2600307030148800c005080c845414001c000410816944402a070188590382542d05010216020340c0d20550160316140d04200c000f0109680b00f03640c0c0b03802241003103a940784003844141c0543c05805401c50141c4210300c250b0408041c03103050040904082c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 25126256 1250 25125006 25125017
    0x3060108010f1d0304030311070302090c0304020f01020a02031b03240712090302060c030c09040606020708010b010c050714060408100f0e03160312060801050411030d0f140322030201061401 83
    0x2169200c000100c401b100d80c903150407416404c010411030305001e010b0f0002940300307043c5414030200400d401c1c061030246000301e480090b86138990005980e11f414420b8000e4240c0c0145004044c07032500c83c0850010294090306813211600034904040300703160343c081395581029001c1c0900015542c8804001c0c940d4a0a00c0304201c844c3c42030710003030f40e107101c020f2200034036090001c0003422484900090328500e4030040d0040c410303240c60781700103910746529000c2c84915600c0c160640d80c40e50311900610040942000281c0055070801c0912040c5001c8145e0454000c8020000021814020050303205400c1040b900025508182040ca2081d90280041100254000d000da144940000520601c002d41c0c1414a01040025096070744050728040c1d011994651900041000f48a00480c505200034800c42c02e44030f07000780c00c1e20260754580b04031818100003081c3c003240c01000304801d001540c00808515500c00b54a030301d00990f48494646c283c04400603519640b04000c400507860108100b1002400c04 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 25127506 1250 25126256 25126301
    0x30703030c020d08010b0306040608030706050f0c1c050402010512040b150a0617070207090f050a0605060a09090c1b050f1506060702011b02030a08280507020108070e03060108010f 79
    0x1000b190713040c00b48000350080000410b11545d01e0354450380007000b0721401d807500e824850404000130300007150600b18080000c030028030780380720a8013181c0101c200312101c812803250071001d120007068014400c0781813003010410b001c000f0900d04d002501c1070303115816004442c40c102c843c07100f403e0380005050340102d0900c070003402407a40001d80d0181340503110780040c0030f6595100003245404150f6201c08400c0b4504100d00071001d21a80045208504100d82445030507a1030303003444880c1c406c4110a00010344240014000b0210f0354000611400036071804080c00006021030022001d0302e58000c031001d9210600742501c3c030030148545100d6008131030b00c0340d02d80d10b031003408107149110300003000341044069000e0354000b44412000420450700602250001d4180b0b00d0202c440fa40560100c0000803036441c0840340b044400200001c3c0340480d5500d490a2401e940c1c0150780301c05c0050b04160034440301c0b0382d8203041d6890411606e8000d000748070000ca03c05c65400120301c22104000404100ca000c0c105d42d = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 25128756 1250 25127506 25127533
    0x60806090d03051e0712020a020c0103060b0c03030c030a02040305010507050316020f0c0d030c141f0b0a050411120712060504270812040c0e0a09170c030c010509030703030c02 77
    0x10f80248010813011041280e0303174460048404001c05403842030120b1012171954440d550015521201c0e070400e0302d040114940703814008900c1c2c082e906405400da8010800a40040c0c01d25014580142e0040380c09400c3c26101c0d42e9482c00d580c02102c47d040090000700c01c1041c4101424080c07055101c04d80060040b25064184440d25801c40800b154051018042490201440750186101643c0c1000c070810002c00c3d14030081e6202c500320078103489545144901c0020103400340c0325160034040001e155840707081ca0102400003601d50f405a4003465a4144805140850840360300f500c520105e03903c1c40341c2d05000c10030010031200c2030f40000340540e1030030021580550400f5041c5091001100b00c043c1c0300312103850103844a20070100103800444000091001300b00d240c011540c140d075000c1000742c5440e07580c007143c1c0080320395140015140d000c1500d1303052410b10b44500100600506002680d290103049030000c0e0969a050b13820180550000848405266051156000c40c2c078203071000e0804001d10a6 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 25130006 1250 25128756 25128781
    0x30c12120a0905060609090a02120c010e0a060206070309060b13050708090d020a1b031202060105031005070c060e0c0a0f05040507051c0b040b120d0206010609060f05030603010f060806090d0305 85
    0x10a40390103000e102000c01c0d10b03070204000c8c45480540c0241103d0425068150403900c603001d4600c5c01e40820f091002c0032074146814000503003a9400c2d6802800d0b02d56600108034050b00420b8425100183d03a12124080c984524202c40000190000d02290701c0c14542001403200d0300050501e41b25400440704517105582c0410480e041d5a0043d0160210b1140807034506940c048542c0014041d2010300c3c40d6080c525000700d04035048942c101d064038046019000c543c02600c408881000019152009000004181c0c5d484a078010041e4007c41b50040080400700d070f0300703a00720b4005081302174404804007c1841c00b4050a9808001890410304080074031064034484200301c0450983c01d9103608030f00d81d940c1c0716940000001c0400410070090444d50303200c95074640c1e83c0e51103040300600541c000481ca850250340c41500705c403519030b2406508441940111441e81010304615415501c998030050412035600900c0d0142a80728050602c60405500701803420f042c07456240145400e1004100032801c609 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 25131256 1250 25130006 25130011
    0x206070912030804080408031b010c0e1005030703060314010b031018020d05030d020d021909080c010c050304050303030703020912070509060d0303020d090c0603060803090a03060e030c12120a090506 87
    0x42c00c05120f651240d00e0400303180d004036085240c0512002c10a086601094402d60380a501548001c0114501c2030307000311080403590a101c0c1d0400d00101ca0807a04520401c0110381c0240d2618001481b41d490b680d40e820b145110710f07040d503c160f460301008041d07407509104420b030702099600200090301c280d0900307c43c400301030341010f482203090301d003c1410b0100c148122103a40581940855613980c41c1810390000b03400580c990500a20304400c0201c03050300070000841546c1e007040050145a50a4004407810500c0010032141400280000203040d18104090750061914ac0c40141c1c9580c40c078000d03c05404528001e40d8550b074890340c01003190382c840700c0503030b90010010b4540c03143c00032440c1000d0f40640300d42510780490510b421304d420b00b80710045664400f641c1e01c559060000c50313564140d869403070003600049944030038000010000106941c3c418070398403104c00251380c102030f19966442d052000182c14204002800940702c8803060003030542540c0805034140422220049851b290b075100d100 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 25132506 1250 25131256 25131263
    0xc0608040212030408030d0b1801030602031005150a031407090603090c030807030c0506010501020309031506031609050a0501050d030507030315090e070e0603010c02061609030209070f0206070912 86
    0x2050654807140141c4096400302d004a03aa41c0d0795a00b003075941c07580038424034410240b0700600200c03c0e20382140002207006203050404444c2e4296243c4200a500c0980a081000001040010741d5143c0bc000d10400159034200d40e0b465010080d0080d003901c0c003449885900007061000c000e00300b50040b00c03260656401d441d00180750500c0780707015407040c200c0d6000541005004182201015481360031442c1ea075104a059800d16687d07880160303521301030200801e40c0b542203068610400400125901d5020780002c04883c00d51950014841c8115040c0d0041c00702c05803130f1420014400c800340611801048180d03500714240e200e588000b8124015408000c081644a21140301c848110b000020094003e0060801c04568001c080c5980c500f603603c900010f801c65a000130b4518070701841041c1ca81c024640150805a40d1422000014600b520b5400e042c4010400c02101584400c0c0815102c1c0c850794540e1040207200002c0603241150040001c000c1011040092100290480d03c00e00610386c03 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 25133756 1250 25132506 25132517
    0x61804030504090e03070303060801052406040f120506100b07150617150604020901171305060a02280203041e0b0d200f03070c0201020a050f0d0f05070c06 68
    0x96900e0112010b20640d40422150307400d11606000c155404002070960310320a4408102d0b40f50381e44a05800e0703400443d0300401441c1c203803901c000080490f4004460f0341000420709490309403103070034107080b070031040e041540100383c3c2500901c10400300300511030b04100806c1c0010781c44c4d031800441d0303000ba1007101c0c0c00411100b1501c000101c0d10b83c41d504050301900d280301d1011b114520300d0306950750ba0f120408070102c2c140240c0b00403a0f29400c0030b10032500f131800180e40c1d44600c0b0001910001d51541c01403c09004481c0f44c11160001c10810b0280502949a020700940d440c030f00c0300041490000c1581f880815002141c40b29030b21260000112021280c0a0510b80d116206201151110214580c8407101600e0006665401d802065100070195075482074110a4521a100741da81c030342c0a00040111880c40800220311b01c6802003003410702061051040300c4500c030190b6210b605000802c48003082d640d10018801329126040801b040060710546026070801d8000d44403014420b045108510070b210 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 25135006 1250 25133756 25133761
    0xa0309170d032c030d0606080606030601180e040602070b06031c030b0a0506040807080609240a020d02120103060b030a0804050409030e0303070b0702121603080c0d060602070513050618 81
    0x104a801c0381c0403e4483c41c50711014480b071003c0580c403540040c010f601c016241c0345012076854021010280900800752180e829036580c4001960540c142ea841899030030102040010302010107212280f05620400f80540c40340d8461811400019015004a01c20380101c540d10003040100c1c05000441e0740030745804605808031001240c8500c0f03554112070b404c45000940071580c240c000034094200c406410440e80030380e0324915000d032180b0f40e240c400d0240d040400f216001c2c105000380400c0c0c20045007280140382040b401c2149040b43c2c498034440f9441c0040c5801001400601d01c1074880d141415406400c4400690742c54001e10b00c958090a4401c59841c031602046c1480344960080c2110080c040300e40c5c80c8031608010352105001c494440041c4940600da810b0803800701d06032079194034000700c59820003030940c0d425105004000e218408246082c40888403203d258010030004180e07035000382484608200074002c01c0c0540314052007215090009210031034850342c01507402c0c4c808103010764020340c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 25136256 1250 25135006 25135031
    0xc03070e060105031f080d0206060901080601080703080c0106051c060608120f03180a050609010e0a08030109020d0b0303040f0906121a0c0705031813090302030409020c0c0405090a0309170d03 84
    0x807810360300309850512520407e0f554154000034080d000e035004550440682ea0b030f41d805155944000d0041700701d55000000d080001078103100103441e0002c0c0400022a1868882000c00c820140c1a0220040102009656420b000c4144100d402503c9000301410401c04020814115803103580034620b1081c0c000000188a40e001e031418001350400e200a903040050142485681c40200b525132078025441d01c074800c000c2800009110450591003600700b420742e1301c1d000402d0002e4200303000d252842741c1c507044280010358083c0000d101804104081c20101c505024500040b903030749400c0000482c52161003140450b03420711211450f20348030032400f5403a88e1a06001c2040e4040c9410007003062201192000306416a0503049a03c0e00c401c6d030301c1003117501100106500399000d00601a016820401c4140610b0084d500100051030548003100c1c001c0f0400c1d00030a0803074408551030986c40e008800c03442c1c10103521221000040a840c02e5140c80c2504c0c001585407030391084900c00041c55698901a00309 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 25137506 1250 25136256 25136311
    0x50714062701090516030b0a050103030c140a02030a12030b03060103050c300102030106030b010f12110403080309010c021608101806140405060604090b0105060309070b0c0c03070e06010503 83
    0x243c5500005030784503040b610040048041444c04101c1e0800e002c10001114500340748180c5040300c0d0140d8400c0414804c5880c1c081d100c0000e000052164003e0000d2440540c40800c680385060348107200d20800d06140300c02c02011103aa40e08864804c1e0041c00041010940000f101c0c010702c0000c0319520400d400c000303540714403001c242c12514075410444a200c1d801ea001980514100d401548060143c1004440110344c254011030070480451080c000441d000e91040c3d201c6540303045a144610f1829484c3d41700e46580d5002182c1c0e000da181e440e01c0300d440b03181d68180040004c0408402c08600c182c0c0c180703400030740c8490101a440e900d042d80d8508802580d4091044281015000341c420003002e01c90010b40340c1c0c900070460b0165280d01c40c01020030030a0800340318a020301500008000382c9642002e003000300c00d5001034210070841c4a46000440d442c401c080050010210f020001d00e10710290030149402c0803800da002c09960301c0e4003c10000c0c1c998200007241d6110150220401200c0f01d01e0b0b454104 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 25138756 1250 25137506 25137521
    0x607080c0c030706020f0d0c0305120405010b1c0615180e0c0d08120601210e0102091903030206010806040c06030b01020a050706030b0a090e03070f031e050714062701 73
    0x2410b1180343c00001d0866004580b161380b2035036840c2902c02c000d80c40001542c2c0000e4448000300014820022090062560403038640c101c0e101e440081880c4080a0004040d40300804051450084803d514020080a0311407000314a03c8005a5a10503141400d0b080102503031240d8000d0903a02d0740041052400d0910042c0f0220f200241540700310b002d1814800c1d540e41180b00c1c1d940c0300c464a000450015802658508024420008071804100c00710071001d014107558007003200c96640078002d4000560390360103003010802500215001540c07860600038a000c406901241198104109100210740b20b0113100050341d5041c00e01040c902d400e100100d18000c01004060b10301d014140000c681d19901d81c210b20300e000b0044501c650300720b40750300300c00d811140c070b12102a80c1940704010403000501603202111500d030103400c00d4900900c1c110034a21407014010b20f6078001480014410041125507802c0349501c103040c0c0014101c0d454483d8220110030490002102d90009490720030b28003800c250030112 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 25140006 1250 25138756 25138759
    0x1503070212131514041502070902040b120a1802010e010e0301060603020d0b010e0d06090c080f0102030103060f02030702070506220f06030c1112090604080a240b0607080c0c 76
    0x3952440442038407941d52030350f801910002d1480031404102203100b0402501e40094008050346480e2034203416910000c2010200790550241c0c00b00094162600c1c800380006000c0354010fa0b40c2c1e001c1108081e40f007684002c0c54a00031902d407140d0f060280b02c00e100c100c0c20b41503083c2024103060514100580b40104208145503166091500120b22035501d40c0140055a802500030700541d000c0000544e028021000b100340c00020f094050004660260800d8619500603001c0761012503c4070b100a04000504072511420fa4000004108021140c424000304000c1c1c004d04504504280e10000e407501c0451042d01c1c0300c1d0384085001d02080c1c0c07405a90711181c3c61414005e0703401c02d0f45d4081d0144816014840c65001c24035181d04901c2d41c1f8000d0720b000784124040d0026240700504101b040405030010f0b400e103a00301c80181700124011108200c0b1107030b100d01982201606c41c402150f242c51401d2011010308909083c804203020686580c001d5440785e41e4009000790711900390540051070000295001c9 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 25141256 1250 25140006 25140043
    0x50d020a0e030606010207032d0c0335070b060f04020403050a020a08010c0f08071211091f0509040203090322030c0f0608060402090a08030a1805030c15030702 70
    0x3040868000040c110a81000e50a940441c4e4440005a0321182c1071310004e0300340441001c0d550700d00300e503552506a01c0c004000703c0d074806071050b85030840c41000c02d800440e0440401c400802c00407481300140903c0d804440001d01c80545000d58103113050250940013004096100d000c141643c3c3c8201340c0d4070714001d02400440d184d9582e420415500d412001044c1c1c0291308240c0b000c1420441801004502c2c6070903101c082130002c01c900c0840310400300400040411420640e0103159501c40d02614001d95910411a40c4483e820001c105d00740f180d601c813241c3d201112900e443c05058000041c1e860404044078010b890741d54103a402c034114416980d5210703a581e52800c01403403644000003920196800ba00c9500c1402d80c03503a01610440d0b03e2030040b4804101c4c01c1000415516154005020000000c0e20780c4541d19941c02c082c03451900102c1094010401c4890f110b80c04000006010300100400c40c02001307041c04160200d140441070502981c4a11400400620218020850703c0c4000d075030045030 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 25142506 1250 25141256 25141267
    0x120a080c0106062007120809090705030f060d0309060309061107060212070306050d080d0f0e0102210606030a050c070f03120606020105040506011e050910030b0106020706050d020307050d02 83
    0x403a000b0821801818045004034851321880c01000345007016404281c002800c449090105c1150003a030745203011240d51004025070080c51300c400c40d0480c068443e580701daa483c0d05180b54005030f240c1008060303070f000e420000c520030046070703002c04000203c4007203040000d0a8841030a00401501020210a001d004002100300401ca2550300902c0300c071899081c041040e031681c15085060703644910445600560340f485040100b1008030080c4103609407113500142d03620403500c54106840c101c5813030801595000c1900701d4500b00f80401d0203580d0181c40c4440a0518050000a80fa40001b8003d40009540c0ea400074020126a40440700b42ea50011030303100c0c996013a450001c1032585c220b49000406030a10000182d50350050050a01a03a8030002400450382890300c0c103045001c0a00314060b01e050344080008954651690050281407080c20f8600e549007182092060450186e0000b011580408020480d0310b0380041a20b40c2d880301075038096a0b0f40c50340b420072100c0f4000d00e0200b422580c40000d1 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 25143756 1250 25142506 25142527
    0xb060409020c0607020601050a1202130e010905070f0603021e070c051302041a04050108162025060206151f0c050f030301140d0614131b060e120a08 65
    0x19600d2060b1314070703402c0740c1c071603038031a814170084450901ca5018200340f881800c2c4010701e0010460401501810000101c0e844004002400d40d942e80f01c040e281e43c0c110950901c20068807800100c017420050070709514000f06d00800a40c8644100301c5142c2c0400041411010041000c2d01070703005120003020409035900300b590030b00c000e610a118180c41042116034a21100722860107407422614140c49460a607500d01e4800c1490050040c0042c040003c5c0e850303400e0745114100303144002c401000d0020908204100550003e004c40441e004401c007001ca0800c0007070507070000d21a60300510145000b03075142e450301c0104242c005c8002c410b20702c60510101421170b155105203010419170180701200c0b203400550f90b000e82c80748404c2c01a1032001d154900d803501305040c01808030b500c55114000006a00b1001d202c90100c0482c03d07200c868941d110b2400c2c000500c200c0300c12502c02440750150018016280c82c0c4041c200d19985901d1030701400040384469807803601400707062903958000007402d80c0d030800c810 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 25145006 1250 25143756 25143763
    0x80106030b150403020603061302040611010e03040f030201050c0f0d0804050c090f07030209031204080307031e0804021e03010c02010f111201090905072c07020d0f030b060409020c 79
    0x1200000307840c0c000000305900d051480001a614401070862926040d50240286540000d0a0542010003e000600018460310040c4000c02c0c0329600c03002030500d0041090300f92900300d24120203c6c2c0c000d000070f02480f80058122411070b0360908002d0342d10941c604d4224180000b0b070590700b00b1402452218521326070003010f0284a01e220320243c1d51001060001c2201b1810180c80c1c0358100c92480000550b598040e50061800e164000c045805000304c0706441490f5a00c130747c02c161590380010400d44201074010084080402c94a600c020446042039002003a1503c01403020340700707110210020425442c02540580c20040180090140d50a1039601034047e1842240c540406031800048140d100c40c804146e8500640d1210480100d034a401402e8010740240313002903238180a1b410001441c120042205e00172810000b044102c03070303d404c080040c80b90303034010070314003d40d0480c0015141544d480220130035a4039050400207030306102c95004c00d4850103176403c030283d5184002150304c080c18001 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 25146256 1250 25145006 25145009
    0xf0501020403030e0108070807140c0705060403080a030506120c04020f0d05100e0711030304120302090607030804020f1c0213060b0705150a06080703030f0c1a0603010b03010b0307260106060801 85
    0x1c6c0c0b0360045a48403075030100da241c3c0d8100c03100320000b4103040c1100c004201d00c0e00140106a0201e08442c440e41e207074800500184e00c40d40c02243c0e401400079030b0f10052034041c060540e000804480441c01b03e41260314a40e11480103000c0c0e2032003158005040550300c442e42c2c040d9170108608131420440703468035824003443d0302d02c94010404214a03100001d0b03400343c8202c00d00b10718820244061030664a455865071b00c40c044120b041020305030244800306031500c070a80500041c600940d10281e0909080c014801c8018801403140c0c0120102a40c00c04400300100f007800429a0698400340404001d40b80707100241030310f0700280000c040008888090085c00180c03014042c5c08150403450b5500c406d0028bd0807100c1d50b100d500c8040d044a4010400700f4021030f015440312807581440d038003056580d91031045241d185114007540910000501141c1d04091149801002042d0004c00c104044600007a54502d828850b804c42a071914407117007001540c0b4401105100300800090000c03a4550310080c2900809 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 25147506 1250 25146256 25146259
    0x702030606040b0f010e0d080c1e0604020a03140109020a0b0705070f060905010f11060103060c0314010501091203020709050403050316050a080c091c060b01030c03090510090f0501020403030e 84
    0x640c0c0109109150074400c86454100003064085407281860054036602404428154024414034021010440000c010210300034660054100c0002d07141d12490301c10910b030010310707050b4014400c100068640a100d442520340204c03110f40d000d00303060301903405031440d41c2d80250801d100e041c2c0003603880d1260029000765889038080d80c10300c82d1101c180329505031140c46204002001110f00300700550040d65401c04541e00b900d45162202d001e10f509619003071080c1d0046610b6542c41400b00720031b0707915104004038204490089403440d40350100090290034240181c91410035452010740415008200340002800e89480034400c80c41d044c140948071781c0040750710055080b26a8000101240b0800486a202070a0b888216164640c140c2400d0f0799040410210780210001c0300281100c0036040000c58818414007010960301c040c1070004050360030080c20101450700301107010740003c0020821880d4000380b5000000c0c0003189040c1805000c80c41d41c0b0141103075100150110626610204481100c2d50 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 25148756 1250 25147506 25147513
    0x504021c050105070e041107030302070c030f08030105150306030d05090402120114040c08131101030902030f0d032415270f0501080906040609050313061106060d0c090f0f020c03070203 81
    0x100c2400d000585514002c0d0507151203082002c0c2340080e000e5030181191a0103880d0700140582ca03655810b020103081d1000f583d60002c088010041890801004511140304120743c1c0c4c19424444042959003886661040a0190203d007508140e1140d90565003201401a401c3e00b883d42d6421b0031024801800c6441400b542c00c0c9034401c0c80325806290024010198404155082c1d03000340c840303280b20080c50b550340b0b0401d61580c5810026a03400c008842400748848050710407030940302009030413501100b00700540d14070321003469803c02007200002000c56032050000d07507030142c410320120362600d0319400400c40300b2000e6042030141d1121030680402e807605c141c80500280d489000550340c40c40200c52400c499440030001a002401580000f20010310a00859003442849402316080030781a403c103100064014148050070a42002100e40081081d600e003040da049a848540c0d0001d050302036181411346840c01801c403250158452801126454001c54407140100d40c9a500d9500040c0d05038868070 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 25150006 1250 25148756 25148777
    0x60501020102070206030a0f0902150a0306050301180803040c090e160b04030803041103010b0907030227010c03110705061201050f090105062a01020a230c060a0504021c05010507 78
    0x5005100f1204502c3e0010401070450783d450103c003000d130000c0540454031a84a810040c0182c85982541807440c20a1705d41640f10103090f07900804803002c581c0301310300c00d82c1010a55050003070a80585d042d696040f0035000d030b40359100c3c1000885200c0c640d203c1000300345021500c540c00c020110b00c04160310f08801403000c14955543d1000c0e8180594000a0001da00030000700300010071204440740351420240010614003400c0000861080c000c599200110b900064002c0d02c00e03440c942d0b103546842c0000060301c14801c025000802485400000809025003030301102e120700c108002d031000901c0028441e0760f5032140308508400b69042840303010302603103001050505c18500010054103a51002c0c1000b0300b494000140c80300c00d00525900003000010450089152442c00c0c001803100410303903212540c524000640d510403c0745c494000001c00e1005104941c880c0c0004101c094000320351038000b04842d182c2c0c1c000a4904500181c2182078070500360811020001c0c1908428417548003508e9000a04 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 25151256 1250 25150006 25150009
    0x80a0809030c06061315030809121c0807020a0b09011d1b1003020409060f0503060f07022515030b09130b0f180a200d1e17120402040605 60
    0x2d0041842c9514940c000300002025800c02d9404000c040c41e04080214849400310480468009590010340305c03400001440765207400c0510000c040544448020000026404100380030803105916034400c0204010100d90b50600c00c12000c0350302900308112143c00e04200740c2050091120001440394040c01c144019210358010510700201540c1000c004400744000c0208a2071444890209007416400c1c040840c01d07840c0d48c8110f0340a044002c6d20444c40c0e40c02c0004151070100c0c02042400203c01c98420414526030202c0d040880b021000e1584146039500820580c541c452038000c0580005a07003240354407203a15070464994031400340c039084000c4c0c54540350b00c203540c6102c110241240310f96101180340c10001c1306002d58004000030b4142c68031144498603508002800c801076620001c10f1020320b203c64442d070030004080404a074040703020032290340e4465822850b07040083c41c403035510301d03280c05002180b6038400200d40d8061516039501400c214017100100140c80c2640034524025010070745 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 25152506 1250 25151256 25151263
    0x40606030509030316020304170f0705090402280b07060c0e010806100809280314120103030f0e0301020307020d02100207030e13020903010f06031401110a0c0807020904080a0809 78
    0xd1020302c02840c07840e40c401c1007810800701001443c2c0c0452004000c0001d141d00460440e000c031000d8400500b50a0313601081d428030300340f0280c021f540300300300f10b0091000680c0c41180c001d8a01e205001d1041c424140551400da201456620040c140000022401d0401c030b00390344119200c2c41141c0750136200c07079070031001154040710031503200380c000740200890428140614185030388102d581e021660301001c81650781d00d0b2824a00d8070500b5400303d80350f0580c205a08110300f50b000213080051181848064001180e80f08410310016090011208040c403200344a1044200a098054001d55503402c2c0448000d6444400d004c1100c01401800900071018803540221030740150540e903034503080100c0c4001c10102449200c4444016a030030170250905407000e001c1d8841d49a0781003000100d0070314600f01354a502c101e4062249131649402040841d02801c030040c3c51280e06149058081c081c1d0130f18143c081440f4114001e0360040c0d1110400c01003102c043c0041078085015550201c0680720700c14525603 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 25153756 1250 25152506 25152511
    0x40603140f0420040b060a030207030f02010c0e09091e0f070b030606090f01021504060606031107050703151e09061103160804031e030c0e0303040506030c07020d080f090406060305 79
    0x100800c000c948100c02110f8500e010101c0900400008a0441c414001120b07540b003c9503a8001c6a0041410b50030b05070400c1810411440d1800207020b006507910f002000000b013085480c2c8940c0360b01022455613441000712060911402c43c9400401c2030704003505503506030050b1150300c144640c00c000b1a400302c2e000d0949002c1c400c0500500c0c2003110410402a0051100d2282030451040680c01444d418000e20304500442c000c1d41d0000340d07a030400d60010280c03448105600c284400421007107001079000100141141d4105103420130b00c0e0088100c00300600000507901a110460940325401604c10761b21420020f84034050030807004e07501200212180c00200d07100e07114058a0801d055106000380c0240e50311500c00e140103071917485038000c0c1d185181c9000700391f01e000985d141d401c1002142c00847c0c115002c034080b002142040d19040c00034403944801010410100c01c04a021000c64071a8901001003076441055181c981c4c110300a801d003250424a041340c400d900b481000285107000748100790 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 25155006 1250 25153756 25153763
    0x412050f060c04030c0e090307050d050a0219020907080603011d070e0a09020603010311040f020703030b0a050103060f0513181a01050406050f01030510080d0e030708070b1b010b06040603140f04 85
    0x6149510701810711030000f0008047c10130a010801c400c800265051103e414022000d885d90303500d42401600c0207150240c038541c40b142d00c21000040c040503070344543c65254000103134601044071f81c0e612004240580948000c81341c400041e0040d40011600102e0590242d4040c0f50504800c0d5440c030007a0002d54403a2200650016130420042c004558044404480442c02030001f10b005640d5514500490784808010b0f000641d841210600a05e455100d40006220034070b410302a060914503048030751103052080c00d02c20b85001c6c10460b800c0c04650080d245181d031031502c6800c181e1a0b420071800240015004800040c8114000b0a00e403805104820603101c000e40700036102110b00d40194000c11000d4154100c074030b4080400503118400700b00c0740140e4103456480307100a80408090520300240764000390802c1d044401d00388141030606098810449621004ac0a00b0418243c8140145070151120303820060000b03020810315090340001c0d8a011410b11442c990707940c0c1c10304442d0000020355008 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 25156256 1250 25155006 25155023
    0x70b0a1505090a090f1208090f0615031f0606090902070506040b130c0f080111030105100e0a08030a0503100e0601020a08180301050103060c18030b040303110412050f060c0403 77
    0x18419400c0c00b00507107a0001c144500010240c49a44a40215024803101114012203205824040d55400500d00c2d420204800c01420a0309200c00101d40b266002407042c1c440702e00004900c2c0c084e40d01003124034110b0410002c1c0f202010010100003010b13000341d0003060040390860600186c0c005851003111180740d0800c000d0006602c82e5610300e540180041e240417201c008c1d0060420105082c0690750006081801041910602e41040142035980c40c11452000314418070040105403200070b03414030081d803107190005854044100060100d03c1c541c000380c074144800301c0c8024035550001d0046004080e0f10342e51b50f111a03580c4d0311100d400c10302216041d0041c1c00880c41c1300006555013029003e0841481c0d2801140380c4071402290071103100340d0045d500d090300c469409181c0c0382c002600024040302c8001912581c2c1c215240c0d1402c9020180004040654620326110440d01100941e009080020800b41070101c0a0030300c15982c44415100c60f03040d000e0940070402605d41d040848084950114a4 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 25157506 1250 25156256 25156259
    0xf020306010306060c2d0203100b21030d0506120706020601061403070210090311030f03040615030218150409050606010f02010501080a03030f06031205031501030605010503040609021212070b0a15 86
    0x440c0030071446c01c030001542d03540b00649005a4060245003e1134040000004000301d40204100380300c4150040c0c02400381280002d010b03400004400c895130038034401c802065075111500030500c402c0d000c50388400c85020312040402c03000c2d80403400e1030490351035030355229449070604000e140900c405d45840d000b583c41b0106008001900d42c01a400007030007801c000c10b030748486c0088942554843c610015504030300004220400c0b500b841002c4007000b044483d07556090442e40400c102041140c0201c11922240e0005402d042c00c4401d58442d602d0040c1041c42202ca25140c1207694200070360344170740031842140804584c140b0520a0314100c030754410040847e403101d0f07241640181520314081c0489c5441385000310104021540e400000342c60b941d40c081c0d903071612002c4c4038444407641e8603041c101030504c102041103aa0081c00d403a040b0b902711400140002e60340c40014440c07510b198405225009403001d01c1080c844000c041d100d03040c021380041840399540d00c00c40080391001079101600c02d070820340 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 25158756 1250 25157506 25157543
    0x10309020102070503030d020912280f0c0303090e09010c022806020a0905010f0c12050d020c0f1e0f0709050907090612020406121a09100f020306010306060c 69
    0x8014a09030040c01603522141c0c90760040f0341594010a4000c580706e400040403082c5042c050001002500504040c007a07a940f10518000e600580a40c50001e00ca00917a40d0b03400e00141c265160701680d40140c003031102d20f41d607190141140300740e4811481d03140300b6100000c01d1070381d040c003d400d02c5028990141c80c00c491640070b01c51030000b28500003070040c18018020000500c41d0302c014403210b5143d44030b0100251a142c0010003600114000c201041012203503440021018585580001c5d0326091040c2c90380c032003010800090280d076041071231a1040c440c5041c5d5030400070071241100400c1000f4451489204a030310799480c1d40c0b4092801c41580710300ca04110000c0d00d544520b402c1004030042e1820b5941d0350f041031044e245550420241e490120f240841140b800c0d2045000400714040d400b140900251249a2400c4400d26080c401c032350080009222158203100311900e002022004025100c40b01e10904000d40080300c0300c9020034501140403c5a50042060701d600507840340403c40f040000c0300307 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 25160006 1250 25158756 25158761
    0x6031504050c120a05010812070b01090507050c0102180108010b040f12020612090f010c030509060a1104080a030c020907020705100e040b0a1e0f0503100515041b030506030105150103 80
    0x9224600640d0248036122241c0800041240904c0c0808000325041d41403000580c20480c40c4007102da02c07010100800000140c04031121411510b55510024455441880c02d4480d842005000d1789154800501907103811604c0d8100c000e05d00c0281d036071003a540c0c0c0f03031000988a40f142d40500c0503044c8444c4402c222280c0100740145d0420310140400c1e04181000b016008011815100f00c8004c0d088208541d04800c0c00344100407122540f03140078000d0341003540e125a2514405002d0405607a140c505521800f5504070441e00208000011502401101c0c10014044103807501d0072882800300c9401318072021302c0000d4242c141d0700300500c07170340b1101c0300c524042e21251003025105400540b2425030f1211342e0b40c0e42e10500020300210010008100090340f0f00c034200d03010750704580c81c010400d140034080d039103000900600d00d1580c4000043c1c5516441045840300e80442c583e9a07010303007000d003c61184d0303a034441000041d07041b03500e00307200c1519144109400c0c2c0380d0454011001e00802c6a00e82c565620a8 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 25161256 1250 25160006 25160011
    0x5040b1c0b03060117010e030a08040210020106030506070f0207050d020105030c1303050109111f020c060a0e04090c0e07030204060e040504060905010e0705010f0206010503030f1b010f15050603150405 88
    0x810300052144601c008a82092000d0f400744040c1c1d00f5250741a04808028000d41c8003030107119020314a4440c0303180018000e0703135003d04040c1c06000d4810404500500035400350700039580103000c5408a01d40880b0040614540145400041c0910314000450303050842c00320035034690584605007181d598030b41c10320682d085049074041809080b900040450428030030520300900595044503800081818440c1c1c04413403060711000c2c1e14207580300c140420b030701007803220030947c0455446a442481d00350880b0900010841c1903803240c038052268003084406026075084074030310900d801403035030303800300681c2240aa4413515011800800d01201c03940b80c558000d40d0b00603c14080010000c01503103401d0708440c5007011100456200b1138041c00b2541c3c2000418441703c12520003001c1b5076040070080303620780c003e0f03e524030104000840e03114051044501d1402002e202100204982c460194200025011b40c0e00010915040b112b8086003a007030900499200700200710081c1909020301007440020700c0c00 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 25162506 1250 25161256 25161307
    0x60708070c03030e0f0904030806010e0301090204060803040303090b0309060103030c1e03080108010b0a050310050406060b13060813081803030f070501090b0a0524010e130e070605040b 81
    0x20048003001824a0801ca40a1400b903078400f282000c55406115090b070040000d03030b101c2c1c400320f400c200000340d1019069502200070301e03201026003241d0011034050711905400950050809101050b42c400c00006007045900070760302c64070000d5454078010524407069500d841c180c0c000b240140042030280c102148821700c1402d07141040f19071001420744064001c40b04400285968004104950b424040c0c0885404110f61000d0900d00c0c02d03000a81c2c03900060b170310007209511040060140011507000000a03c40543c04039910604010740481510181c020a00800c3c1180003068000c0d0b04226800d0074581d10681491802c0e00110b403008a0503c44048151305200c200950320301c084114010305107451041001041c1050140b07451405d03a0300c0208450704403890300c8100174080600d100280344a004031002740810b0342881c40100d134000550394405410a03050003001100401c0c96000f00304641001042e641c50ba900c81600f114148158881c40c000004103012100d01d008014204142d0b9815 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 25163756 1250 25162506 25162523
    0x61305070e0c03040c0b04050319020a09020307050a02060106140909101806030302060a050c0708030406020c03031003030e0f03030a030b01020106080a1a07030b1e12070807050a05030a0507050607 86
    0x180d8072207400d4440300071260100c80d0b03540031050100700b05c1005448405442c83c1410b2a0404c2e09100100b5a41c00541c51a00507400d102040001503464141003070004d0008044290350320b20389038901a00039440303005a0300051040030000900742e403150510001c4815403810561400400f98102310201e003000d03050a55800841c0000101e1007501d0303a502410099600703002c01e00f203143d42400790510350b005112801d490f007804200308010207218103c402c05030b8043c2c500b5403641c03102d0400d00000e00508001c0d40c5035200000600404a844c5919041146c0c802d5855901140405061003185540f944181d074041d402484010040350203a08a07881a11040c4000a0840ea644030040c2c6030100d40c09059135400a031050780854940b50f01c50480d44090b10741801c0c4005c50101e004201c05960350120307a1981e61048080000503646c40d0f041485003031001c1c0c00c69000f19100c1e203005440380d4080c49064070601d400da40018035410007049044e82117030014080e003881072804090140c60780c008441101e4950 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 25165006 1250 25163756 25163759
    0x50405010e06010e0a0606050405030a0f030507050105100f0b0a020c01051608070f030801050d0804030206090406092405010e030c090405030403021002100b0d050c010309060204091112070e0306130507 88
    0x1e038100712140c000d120b950308400035800c142e070f0038404072180b6030840b00410208000c02d00003a1000242280d401e640004806a03880741814100e07020f029400d4000e01c0f55090105103c07000602c040303c4400e40d101000344240313241c1d990070700b140d641c42845180d074003603006521004e0031580a1006400c102c0401c1191030745404040c0d4a0709501d9000e02802c0318802c0011161030107040d800500c040c00f40900703650010b00c100c619221005103001d03e00c03000b80f103810001203245981d1070301d0b08032000501c9607800501442902c070820070142095412603580c802c907a814001225880780740b402c080000c014019241141c040024013503001030080c425204c500c0104000001070311001c0c0020380103002c5a025001d01c5082179040c1051b10520300b0614401d14105005001080d03022400c06103010003400c0000e00b1091515218010b4001c070303400b031100310340b800b030b072221910060340c4c01032507641422654400e80c1d6450000944d000240f40b49402c1d0181d110b8800030780c818428100c0582d080b800ae00440b420745 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 25166256 1250 25165006 25165031
    0x903020c1e060d0f05010611060118021603020c03061b07020616050f03040e0f270a0212031206090c0406080a0b04060306060519030503091302160605061801150305040501 75
    0x25445020f9408800b96104124500f81189200d0b180c050034513458400034001c0200e40c030594801c0113005141c070400710007ea50170308102c6a411900c14000301e9140b16600030305424040d44485103140c40034004d00842000840c81413132403882c5040f0403030440001c2c0c01d00020b0703000c0c00456089081c44004001c220742e10880450010811000d01030b95a000650791141029150b032001f20000d040500100c0060050001d50300c0500b0b04080c4012040c04501e111f11150340701c0e549000106480603412071158044903041000c080018100303c6c0d00c550303a21549403a04c0f0b043c03042c10f01048a10303004200c1c083c4410301030039204100543d081055503802091481460000800301c0781e183d401160140d82d221001c00150805a0b070f055001c43d80084885102840d46d00e40d25200d12541e951a48268901c100b5400c5100d203e606958564502c80141c0a1040507440d18030000e240075030308580300d01c10340c01c4c01100750481080345505031558061807040d8807501510a4002e80344c09070084840b95200c8a299502 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 25167506 1250 25166256 25166269
    0x4020f07060b120c030309060a1718010e0c030703031b06050906010501111515010c050715090f0605040311061c061502210c161202040f0903020c1e 65
    0x140d00030003000030b6040110b07041200c0000c0c0f0301d10110b41600b01030001000c0303540c04001c1d10340d202400d49950f039507406070f40c800703c6003001c00c1c008860200f00c04c1d8091002410001d080c0b9240100028000c109503120f81e04410303903c4164107411641540803c0d404d01c0028071901c070f641002c901102500007070408940d01d4201380c50044807601015480540104007569100d2441004e2a84100141c00c0c500131040040480410041c000709041c0d5400741048466403242e44c04581c0d580e04807003074075240740c0c0702c0c682c0341c02e10849400d034800041c0d41c4a5000c03800400341c3d41094101d030483d84900c4c0c6002e02e1076031a481e01e8042c0d2810940d003c3c8040c00350801c000b5003c01d2076500b039551500c0c000f480c0c80c24041050300c0129910500d20465010100400060500340e50085008040888864482e0501070f82030345804229140003401000b1460300040c2070040c11020706040388201c405210200d05d00804c0400c036254007101070010f0f804031000300320034245469401c0041c0305000780f884051403400b010414 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 25168756 1250 25167506 25167517
    0x703060c02011808090a230d0c08010e010b0a0506040e0109050a02040b0a02061006030e03070f0215040e090d03150b13030209070507170702010203030f070c060603030c03080901050702061504020f 86
    0x42941000605c0c030190300d0503940101c0174061081001c032070b21807188154040120488031a5001c1c80808184d10180030f899100c5000408048009110aa00ca400000d0103014403c40c1203000710042d41000c40c00d49459015541500c240c05c0d065444c0f680381c0071024014150107080080500d90801011400020004c02000300c85101d80003058142004d43d20700c403103005268800c8040500d802a0000920800b00c201c0380c241e60000480f0340754207413a0000642e44000c0e54500800314000040004007040403007a641c0c4550105003d482c106144e041c4103074140ea2a0040c0003d1b0a105081d0901c002c03610680a0010681410b04d0030034815100e501080c003200041d5458404501c000c5440810410b004070025030700c0700c070009118100b08030ae90020756030b404050708181000310f40d07500190540d13100d4100580c03129003020040c0720b960b580f0300707000d003c1a02c040d405030700003500c4d540051b008640c1405050701070a03540e0b00a01095540022505070011203070062a4829001c109103c66583e20501808 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 25170006 1250 25168756 25168763
    0x5030403051e16051006030206040603020702010e0603010e06030d0c0f030305130c03060b030c0d08120c0c01060b030a0c0f021c09090501081b030a03020307020108040c0512011b020a02030703060c020118 89
    0xb4944140c02d200c0e240808051020341c0560801b40140010384542c8c0660301103d02c2c83c1009602d810b540c2c401a200c42040c4040c141d0060804000041c0c10780e05840c140b4090b003020303004da42d070380a0000030813600000a0304014000ca400b0b60100c0300003d1190348460341c81414054110f00c2088150366140c103100381c03580b017907580759202c1840300f669103000c2c0715842c4005403c40359101a010715030761724810b60040d1590110440300b9640040d005858040490300d843c0d610800801c2002d840d07038400411078009540c260102c910705100341c008c0c513010341701040440029030001d040f41c555115241c0c80208150410030304010084400040c00606402980d0181071640090001c5181e20040e00b8620214403002038480e6004061440c0030940210031241156028686081c0c280e0b100d003400039202c1d0703841e80a04e030880078519a841039130606500c200b01c0700d441c0c0c5800c0148038110713010484ea20100b0380c8002c0c0d13240e04000c00810000d040d50307000b804008843e00020030050200245c54121100d40c21055 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 25171256 1250 25170006 25170037
    0x203010515090903070203100b03030405190905060d08031308090301290109030c090f06030b07030c0e0301020f0f07020a2c0901020f0412030c12030b040b090705030403051e 76
    0x2900e142c0b42420b101584402d02c08021030511080345c00203951202d08145041601da40d80c006c6d5103194a0900841d0040c14015211001d903000f10b92030b000000e600381c4107018869181001090b15840e02902c1c0c3d00c2d00c280c004803081c0c11915201c0e03042d904150303c0042222003041c20800013000d40c0742070088444910300c40c3c20300603c015104c035140041c005074803000c0d4100580c940303090000503015103588007030303c079403400001e2603102c200d803082c000f4070450300051300b441c606004000a40d42d042d0089c980c0903080c0d45d940c1000f0012203050500340c0c00351064030746400700144620b800650740c5c40c0c041c10303180340002e10995031582d581c036002d860501e01c20524540908540601259592110b0f800354110000d000214a0b08050804441d41d5015a0103800807030a40700b03c0f0541410f02c14680300f446a27800203030104c1d00f907501c0c02d8040c0040035082c0c044e0740241c0c1407020440491801030342c4180304410302c4d100d070762071951203940440e031543c00340c0728001e03640a01c03082c865041114800074001c9009524800d = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 25172506 1250 25171256 25171291
    0x8060d06230a0b06030103030f020a050304030803010510090506030a09030302160302010e1501060207060503090102071502030105040606090b04030f0f081812010506010e060a0909050901020702010906020d080105060d060302030105 101
    0x418409440041c45402c91034100100c0954940f5103404690440f038040c90050300c540c40a210403410001e00f180041c001c7d200200b8003005103ca032500650403240210355440c21240c0014060700c2084c103034850664042c80510028a12408030340200005a100707250051030f01c0d2450400c50040c8150007021340c0140c3d514503210808071300c02c0102e01c80100320142801030644c580300d0025501c0341140100c604001020000c01e052403001d405440c01654407908040e2080f1001080b603009400c01d100d814480e5041880026110740114680f07001d0701d85100300d1903d03003030554035041845c2c1e848450440b1401c801140034030100d40f040c4083c0c0514483c100082010490f01400c016545002a500a19691404061081d0b5a80208030b0701c042c3e0805899054942840c50810384141220f6480700c0017482c1001e0030442d041c6010341c01041814804d8a40c042c01c0c940740c1c0c5c012a601c42c145c00c684008034444000501051516001400c20f02d40710500103c1d0064803503000c00c1c01d541d070640d01d0442e080d031140030 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 25173756 1250 25172506 25172561
    0xf07090c080903030402040b06164e020309090703060f23010e0f0307080a1b15050c0102070204020d020d05160c140715020303070e0604051008060d06 66
    0x3003820003440c916106015080c003002c900d0701da11000d0002449140d54034000310720760715558103403481c014140c4074a00f071280c0e890038102c0103202c03500134407080c01c08448481d40b908a9240940086001541c15802c03a44403086e113200b80c0551401460029071100340300204031075a840581070b1040c036042c4e4000c40c6035032400d400c030380907902607070400200300c8030401540703680a80301203080e41008001d103000749140342102d000c42d02040000c010301c1e4042c01354200c0410b1449000565541c168071894600d184500204a02c040052807406403030040c100000480f101d183c41940030b0680c1103074031000181740c0b2106500240032a07100004441c10940c0200b4040c040c0c8100b44a01540507807410008410048074203c000c144d01c00d41d103002812520000103100352940208207101c0034080854000c120b00b101d200d000f940e05e4008407002c80015440003100d0340300d42030440503135048035009400d925800c400703c6003e5400f140001d0000350030180b082d01c034602180301030051030152604000e60103602412000f = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 25175006 1250 25173756 25173761
    0x7080408010c030b10050a0e030f0d110d0804080d0609061202010f0e0307050d080c0708010912020a0201050904091a041506050303070224070b04030905040515030601030b06030304080f0709 83
    0x20b003040141032900c41d040000c0e45491160039440c92042c03401650b030324401c96041e500074522103450303500361084001e0071800b00ca00182490a01c0700356281d800040c8400c0d001a6034031121540c14074005a84070340400c0000d07501070060021042c614602180d02a11078260004440542e480651094155110001596040503130710354011902c2c5460741000b5400703404282d5a50117880303014007400c40b12001c075040c419540191068140d6107000c0e501d0050755002014042e2423101c4003035a0281858040f240100d0002800706503090307041e141c4604144122003080014072004406480c801811441c0d031510704000417800d44038a00c20507580030060708034401501210040c1d040030340254020080b9038090f0f9682480304149070016000e20080700c02140490740d503409582c40c0103203a0000141804105900b112805c401d50301300b91400c000c560369641c1e021035000c0050042c40d0305500700e0301c0184040fa0003c2c07145a03020401034100c0f882c140c0d44000da00d02e4100c0c88144124642c101d02010701428142d030 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 25176256 1250 25175006 25175021
    0x5040f0213090c0e13020604090c03110c06040b06040906050412080115020709020901020a0b0403090302180408030a0b150408030c060901020a0906050a030603020607060b040f05131e080708040801 86
    0xc0104110518040d0b440c1c04110b203c0d03000305140350420500041c542104900301c0c0c140707294040c1546031241c3e82c60070030001400c807008444011a080c240b44000050600081c0c41c030b4070000d48002d100b540c90303c2d11240a40000038080a800a0b207c503200c002080060090a00640c45001c0c60300001c10180001041d5503810381218024080c084a54082c0903800954181541c00c515001a602c441c4000141c2c0307010001280104045a440308000c14103400810000480307000303a030940030b0b00c48244105e811484045400410003c810300c0131924a01c165808101c060002801a010494810980d032400c0d822550214030203520001e0303020786182041c03002d0350704010318400a6041280301c070405400700c6101d00802042180c04a24540800c1c8650002c0000750340141c00309030385051905111000e4402031f075001d4091414030b0b4441c81e081610b880365504c22142c801c0c1144400f0181d5486d0080c005041185507240000300c110000411101c000500e030312403060072490766403468000f496083d2103c0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 25177506 1250 25176256 25176289
    0x9130302010c020304120803101d09120f040b090301060f090e0c090411010507080f0d02300a0b03031b0c010207080c06070312180303150905010b0703030e030d05040f02 74
    0x2400104461b2150f18006c3c01070b951300c01d00301600e035a110140100256000d603c0340d0b0b0400c1c0da01300100170680e0034403003441c010030040d021740e40011404241c4603c03030b02c1010040988250200030400480360ba14001c1c00b0302400042c008a640c980d40c48600c05181c02c55000204140c4c1d50b50b10b265144034040001060500741030390119000d00d407a45600031010303402c0503e40e05101e0002480f4041203040320498040034880740a86444420100032280203400144c5902c2c0090002840d09500345803483c502c440c1541d401004040641c2c42404040260182d8040680c05100038422071100055450410720f01e4000c0400510100102d1400207280020700d130b00c8510241c002d410030315600d031907036400c903103080390142007040c108044002d0300390041040408259442e41801038580030158103400030140c0c40f61b070030540c000c81901d815500040383c00038491000304600410881c0006030203500180d659883e0441a01c0c00c014403003004109850040303c08481e11007411100b0000c43c03900f00502c0721030481 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 25178756 1250 25177506 25177513
    0x61305040206030604050612010c02030a09140a0504020c10060b07050111030c03040609020f09190507020d021c020c06040e1902090d021e13020d200a0509010e09130302010c02 77
    0x40c55004205540320142a160080b0344560000c0e41a46a00c0a1103030701e142d540f4002c2000d4020030300000e49a40000d8050f01c0081c400e00c600051000c0609008259500c00a04a00d25140303080104002540940f50f04041030052015610034840940320700c000401c1b481c18020343e6090140f42a5084816560050030081007e10500090120070010703290300c00d03441007001464840b28000104600b07807800c0d290780c3c45540442040201c0401140d400c001241d016030511068032030042c1a40c4500c090302d05800140d02c400b02d0b6080c05403e1044090320254a801601c0000711130b00302151080e40280c014000c0d00a00509100328102c11105000f00d441512104508005c415000170b000e401f50410081d114034403003e146184460b80784200707208030034020200303100740d090010701d080690005d0000010007454007600301c0c000b80200455010150140290925040e15880d081d0b031250001c0510a0403c801090200000c0e120303002040c0c0680c68000d900d01040080389402820349602e01001c508540 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 25179862 1106 25178756 25178761
    0x30e01050a0606050d110904021b0c100804020f030709020c07030308010806071707031e14070903080301050607060207050a11030d020f030f0304031107030308061305 73
    0x14040248665907481414004540701c0748180c001180007004034200c080d11550020720010580f40b1000c1c104124640410200c0e00400030f0707102c035100c803100ac10600504c104901804850202d4464054044290000f01000c0e0084c000a02881e4010340300f01c047c2d035090050502030030b16103804540f52001c0c005001c0e6540018402036012864240c004104000041846846415552507592551016115602d10020024824420503540364208402096401040300c188400d0041c04140d03107544001c40400c0000103031450042c8200404200001044031050701d04580003282e6642c3c4800c0c4504200019102e102c10080c100e00a603090902000700d01603d900c140d800623400c84c0c0c90306a000c00e0581e80c0300480b8003404c00d2981709001c600c2010039244021035006200e850224903040c20754420614000540e001140840c0180041010381d060a450b07022008444180038070490 = true := by decide +kernel

theorem cover : BRFrame.Cov 25000006 25179862 := by
  have h0 := BRFrame.cov_init 25000006
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25000006 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25000006 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25000006 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25000006 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25000006 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25000006 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25000006 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25000006 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25000006 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25000006 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25000006 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25000006 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25000006 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25000006 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25000006 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25000006 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25000006 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25000006 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25000006 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25000006 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25000006 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25000006 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25000006 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25000006 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25000006 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25000006 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25000006 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25000006 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25000006 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25000006 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25000006 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25000006 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25000006 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25000006 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25000006 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25000006 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25000006 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25000006 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25000006 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25000006 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25000006 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25000006 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25000006 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25000006 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25000006 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25000006 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25000006 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25000006 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25000006 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25000006 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25000006 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25000006 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25000006 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25000006 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25000006 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25000006 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25000006 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25000006 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25000006 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25000006 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25000006 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25000006 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25000006 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25000006 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25000006 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25000006 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25000006 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25000006 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25000006 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25000006 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25000006 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25000006 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25000006 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25000006 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25000006 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25000006 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25000006 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25000006 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25000006 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25000006 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25000006 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25000006 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25000006 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25000006 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25000006 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25000006 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25000006 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25000006 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25000006 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25000006 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25000006 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25000006 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25000006 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25000006 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25000006 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25000006 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25000006 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25000006 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25000006 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25000006 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25000006 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25000006 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25000006 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25000006 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25000006 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25000006 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25000006 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25000006 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25000006 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25000006 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25000006 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25000006 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25000006 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25000006 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25000006 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25000006 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25000006 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25000006 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25000006 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25000006 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25000006 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25000006 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25000006 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25000006 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25000006 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25000006 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25000006 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25000006 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25000006 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25000006 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25000006 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25000006 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25000006 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25000006 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25000006 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25000006 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25000006 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25000006 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25000006 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25000006 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25000006 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25000006 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25000006 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25000006 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 25000006 ≤ n) (h2 : n < 25179862) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
