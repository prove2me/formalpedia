-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4244
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:59:24.526879+00:00
-- url     : https://prove2.me/submissions/45f1c2e1-0476-404e-8616-9a1d219aa410

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 763129496 ≤ n < 763309352 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 763130746 1250 763129496 763129529
    0x120c020f010c05060f0702120d14011d130c0510090503100c050d0b150a200111180a0806010e0a0b06090a050915091003060609051608090a020a0f 64
    0x40d101442d205000402c960054000128960300304c0f00e241d40d1040581c01a100490460261418140e0099048000032540e502100000b202400101d601500c1100128a0f00c102e044002d00f0419400030201c0440540c8500c1d04010007d403001d902c0014080540040e044c030310314441c00f9098030518000e0074024820340c0d000c842c0000700d80c01119070100d00d584801d480d00d5566600c03080905443c664860708880b03805801004143c0301401490740c8020359a8410703000d107020601c418000075000e4401526030408584000280000044a40d001d8441000e1211140c40d60302284500496038040c03409809204000940380c09400402c0380724084848007004034040c8001084094061581356a400030b07020b1009000c68100041250f03041406243c030360002d407070401d0000311058802c0b04d01000a0120031020400c0145a000e040301401d90850144410b1800300320408080080202403000c0101c04800319011030802d2000781d0145402038000f90000d42c9444d15042c1d102401d1183c550301ca000701c01c1 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 763131996 1250 763130746 763130749
    0x180a0e0c0d090c0f080c1e01050a02150c0d0f060305100209030c0301020d2301080705040903020c090709140303070f0807030c060c030914030a080a05220609030e0a1d0a0207120c020f 80
    0x80c007510900701d1f403003070344404850b18004446039040385005500b9441442c103052802607000c00c0310740c400c4c5030414800d552504111458400e0782d081c0410300d000c07281081010b100180c00402c2d8131111400c04400103807906030f61000689050120001076403d54800540e800c4403010a4101014007034000001e05062a0007088406594000b4403d4000c16001400144010b2601e5040150800d010f0320403a00006411b10005102132015a07041022031840f030000c02011040c94071580107820200d001c0c1d42801020f80754100e007600010002420300c04000366100416000302c0440701da0907041141048201c1101e60003800402d00310324161006924100010424039000040300e1840d405e07a070340c1080d962aa0010301000d0407024145090313501c160401001143d42440001000a02610b40481d1007616410060450488440d00e28011007001900b4880141000b1004000c4962801c210426a441e1506880240203003030b00244503034041e2140c00411a403040200e00c100c0d00894040012800e220b0 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 763133246 1250 763131996 763132009
    0x50a0c050607110103050a0905150106090f18021303151e0501080d0c03110f01020310170316050c0909060f0105010e1e150a05180a0e0c0d090c0f080c 66
    0x30004010b03a8010f443c69079594801d030001500128440070100303140e4695030b107650070420941c1c100f1a814024800400102e0381c821200303401807444180900c040703801c101b20a1400f20b019000703221000e030000350542d4540140304001c2c0065070404901d030b4601809801440182c04003110703080355141416844840e54445205050403580c4c03000042c1000d10001e007040e41c906440041c16802d00c21042d00102c8040414041c42a10769042000180d89240c484000b1a00119540001511061556200000c0800001201c18030808118040c03d4129507182a42c40d00c3c00030709507590850740703910a10401c001c0000e89140030321201c0708049101c2ea290b0300111100c0d00f204174501d51040007074107020014640406040c00000001c0d1180d54020001041c02c030060f81f0014550002440000f00411080001e40001c1000c180490302404004d2034400902c409031005880144000c4c4005005d5100201030340c860080194025080461a640c961001c0d00343d1f581803242c011076010755024001c4624054 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 763134496 1250 763133246 763133257
    0xa0e06060a03030c0c09110913090203070618081c021b06030a0902030705040c0903020913030909020901211e0209100f0216031113140604050a0f09050a0c0506 70
    0x10702888012071654404694480f0482c0c000d4500102010303003c10310203480d010300c5014580014106940300030b08414020f407042c4c4200d00008052415030010010703a07002c0b03810001c0310304500d413101005000c1c10310311009640c1c640c0658100d10440e901c40240c020099032507104003200b0707001c1d070307043d45803450120300814503c1410544c0b007201000040d605110a80c0a80002750001d011903583c161640c0125003159031041c00034001c03410103081001185000c84205600030024008985846100d80e40540300300080d029201640350089a01c00a40c1d219400c001d62040c03407140070554910404030200024400110800118504100d050760550b03c640200d40724000060800d0303001c110011401c8070218040100c007801c40c0034282804040402201c110005540910100c50b1038a041c1c9040148100c541240c0b41841d0341440c43d0102d10346400e10b0b200d03034801c4050f10042102d81d21043e6140c000c0042d03117a088089441c00d0308090078820000b4408144c00d01ca544216100c50f00d401c2000941c0c0581c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 763135746 1250 763134496 763134499
    0x306030709020f040308070f050c100c200607061505011407060509070e0c13060f020615030f0a0804050a0b04030803010b1c061d0c1e07020303210a0e0606 68
    0x2440c8200218a07280e070003405038501d00a80c0e03508154495445044503404850159a2404280e18541c01e000e0140f000300c403c0441180c6043e405a20860040d014203503001000c5d01600c10892511108150001482050f401c01020300c1e40d03400d090719000c0018658a841d04280344048040424194020b80040d448001c1100305541040d045603110400f818000b010040036000746500020813218001c03603540180c20b10724405840d9140c0b8603102c000c0c04000e03800130701004200d02082c10f40640200d5802d40090703c1000c0b500c40c400608010a245c10551810443d041c4030b54281f42d02840341c6c000c06002500e00881e0f040342c61503903501403c4294000c40c0009480e00350100010018082000700401d00000d0401e20081c510518000d03440440c1c0e01980302d0690124040c0c514038440a0741901682c1c00303029285040c1c11702c2c0d95803010451040c40c503080100501e000295450566800f00252174501e0302c0c008a030000da21140c1a1820092000d640c0c0010b40c50420100d00524100030900c00c2c8034440 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 763136996 1250 763135746 763135753
    0x3180111121b070c1805071b030c080a020a0c0503030c120c0a0f08030601030b01030608030a0f0e030609010903122702040f050a05070e0402040f03030f09150c06050c030603 76
    0x700c200640000000142801107592040080742e00a880084003a01d5254020300c0c1500046161102c141e0b0480071080300c580d00113280c0b81c100103110f50030142e0f0f942d64121501640b0b20301e0b1074074581a2902c0e0310114010303020040104000808aa0020f2500c2409100b1607030000c00ca540c45080c10350701d0083e1906401b039500808a45495441c1803800390207005028000c540502c1405c2e01d54604c1d40b60000d006940d40d010010410503503503010700600c500c94200307190401100f8a81062542c0701d0041d21414030410045074044408135101e010041105a402010340d0003034208944514000c01c3c0700442180400e002d40c1c0049000322292040c00050785206c20046103050442000c2d100315445000c040341c0c0301d5510b241460300b1180d18030030300c2d10035000c1d107030300046505090f10080c0030030a01c880e060303200d80e004020a00c94034040740510412260301d806c220300b4005500c04d058030726420a41080d150f507807000450004480d40700d201140b0361b9025900402c500d445a103001c0b074003440121440f541651 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 763138246 1250 763136996 763137007
    0x21203070513030b010801060e06030c0a0911040906090507110d020c2209050d110a050a06050c07050a1110030b03060f0604020c0d02010f1a0a031e02060c010203180111 74
    0x180240010b186000c0d00110b070203102034807641d60120998003a0044980c981d5640814080a032001c81c907650030a00c00c500415020790500c0c00290100c14600401040588410030300c10184404001d8501400384c0400511000340c548070910010002100c00100084904040c10506a0301190070415651154003820120310f5203030620100c452046407144400340b141d02040402e000c00e200303018280d480750300a0840003440c0d030001400140714443c1900c80d41c0001e003071207000a00c0095503d0040d580b000011440d5607800c8124003403401881c0c00a40300303004901c0300310100280c40300040040281180d9030800401c40350400c5089070740030191070780c0560100001c5a07440b40ca042a15601c4030000308054500070341600c543e0b0511400d01d0620b40540e44031510140c0010481c00b0710701100c4e9107080c012007010700321170000744820400d101c007810002e00100000718102c01e0045610100f5000340007546e403030442e845002e0003940300b00d840d0039803480303640e0503d02201018051001024180342441c2d0600303 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 763139496 1250 763138246 763138261
    0x2040e0a09020a090c050c01050c0a02070618121b0b16140c040f060e0c070c051002030f0703121811040e0a0c030b0907090212150621010f06021203 65
    0x18200e007841030b64402d6200100080c60215406400304043c411313501d06844180210740d81c1e0035181d015001003050030b001d0108034842503000812404968a0345491041c01000c1c51a0b07041810680d04840c20007191b50408200f4041060009004484404820150190703200c0c0e081c88503000e603501c111518114852240c01141c00804811800c41000e0300352600c0b074041e50300180403245070030280208292105010041005105d5050345d000c031110641525051955840b030404403006c1c01a10700c80c401d2454283c0c0d5451007002660303115140780a1303866545586043c00380c00b080071803015810540c200318010302c0c1c441c2c0382a0074007142644070440403060f0070281e0810000d0500d040b070700041803181c84900c0d000300e003114101d4002907004443c05141404c11a00b150308020840c2c0100e00c42c0d50041000400c04503413000740e1744c2d0002a15446c4e050501007440040d1785032143d400400301e04030b4241050805031403032480c960704a07420206c10032007641e550740090361502a032546044001c3d6044c400a14007 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 763140746 1250 763139496 763139501
    0x10140c4f0609121118070e0103090b01031b0b0d0516020a11060d11120402090603071a030a060e15210a0f02040902030f0303040c050a03020f040c0e031e0d0302040e0a 73
    0x491007180c000c0d1143d054035000c40c034005c040320050000c3c40b075641c0c01d00501541000d110b030303d00002841c05008042c2141c0b01e09440e0b10045c8001856020340c858030180029403c039114000d001c011540a070b868960b03107828009440260b440c403048480d42d0703080f00081400090341000340d0b0b0340440d080300c0d0804050100462600010903010007103880710a14003510301c80c07100400c44860081076509142c145030044c0304140900a108500a0b40050014000107107502c0603031802c0b40003480b802d941c0fa43c03242c596070060030b4254041d1401d010400e0500c0140f25001103038207034000050f100d616440c15401c050805522520000c9581c03138000c43c42d084d011038545411205081d00113000801c0450035640070a02c0c0c80007001c4100615080802484200608041c16800500049441404550a540000d9401c06426410610840c0c2da0b91610440c030307024021101c0b0f01d83e0008c0644082c45c001d4224011011940400009140110314a0380c1c0e00500a20030780f41038842c100041d41c25036a601498000 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 763141996 1250 763140746 763140779
    0x40c05010801140d2006071505070804051002090d0b0702150c19110c090c041806060806090612010c0509031c050715020c07030305040810140c4f0609 66
    0x1190343e0405c05064890300c50800421099104a043c100c4c40809001c2e0002180c40c00303003000302009104010f01c0301240c4c0c00156008001ea081d40c3c01681e07170480d40009440121025001888104800c0c00c2103013494000c135480e06400c2118051912a44e1000d1440010744165296030103c40c0c6010405047d183c45989070b5581c0402c0c0c1c100b02c541906105000500c005000c80e01400e80e10000103043c0034401d42003c1401152340e0f01a01845103500345040609030380c0c0d009000c1405030041100064a950794103820b0000c030300300c0e40000c2002c6107041c0b4008015600c44030415020388640c08900d050010701c450811855056139030f8503801c00e0f2156640c0ca10041809420001458080c042040c0d0210140103150040d4801c2d101c0c641d0b110301d80624641002045841c8500c01490102e400302a0584240141d03031044540007000e0f074440c4040080400f0f140b001594510302c00d8040d1070f125001c0c6006080a007e824032021070801c114040480580c569000d004140000351b60b9413040241d8020040c0300d25 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 763143246 1250 763141996 763142033
    0xf0612060a09020105070803090705030d090b09010507150c112b0e03031308061905060a0e1009060308090315101503110d06030c1514070f0b040c05010801140d 70
    0x145400f1b8241c94402d055081600c240e210b541142804008900d01000350301001d0441d424000c006520382442c842060140c441070505000c00003402c40c08010f440e1b480d4108461411608000903110098010590034035065013280380d00c034888045444e600350b910314427442d252450390058001040354040b601111071540f0b141d0548024801111f007c1c01040e1442c01408464000b03200d985041171040000e80d07840910200340c10b160805126258646401c10425254000c403040e040d900c403403811072000b20981d4804542e0b140341800100420003c40024001e80c80220110340c000904000c02c2141c88200790307411540305011341d074108807400c011241010362400e1424002070143c0c510454003125400114031005407603881c10184108407561039020050030b42d20300800651440100e02a010340c000785c1c0030300c2019a010605c0710401013503000d2850303151b170300003002c035018109842c104440e18401e000d05400719420800100e0510700b801e00c0d507945204010f0488080e5440b9440d0000c442c05640400c0307 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 763144496 1250 763143246 763143257
    0x3080703021204060e090c030103050c1009080f010b0414010501121e05010b03040311300c0111070b0f0c0f0a0207050306010f0315020307050403080f130e0f0612060a090201 76
    0x2002c00e8040d4000b0340001c1c1459211045040759003020018207100c0141541d0440800307000510203d40001100ca800321001c0e0340e801e0208182c0f2a091f41d048099500c004500d20821540000d00903043d0031610300420155000d1140c185402c131903942e81c040900510340016211a2040700b00b041076003104100c02500c0c0d04091400240810940035104241c1002c00002c01c00003d0100b019482200c54110704510006004a030100c0102050740e548111441c00c2c0360250039500d00c8416203100202d40d59440184d0081040e944651520a500d40240d04142c4040b900b070f1000601117109412114403c6000d070390b01a25050075401c9035050f60f0400c034001e100714826098003145544040180b140a401f0101003103520b18076600c0c0040440140004881980d4010b0050090749a0403a080e10300350b07607111819a4a4911201d0a500726004021a29403d24145d01c0000342c1121540d038018098410b42c041703080c00d42d46800501014203170039001d000c520781c801c0b00040c0c416055540815195481403401 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 763145746 1250 763144496 763144513
    0xa080606070318060e01110105040237080601050324010e130b0a0e010e07030b0112080f0a032a121503050303040501021b07060206010e070c24050109020708040308070302 75
    0x3d40c10450304242d000c1088a0b110018941e0400c1c070003d812041d0070024051843c00e9804161900c0007010700c07403048810313504d4046010406030301400008180400d283c0b401540d644c241942c0b91001e208690080c001c014119080c21022404444000c000d4406910385910b849541c841e800001000c2800c0380c0c400064810002d07918141c3c13240169018a40440c03080000101c00d401c44001d403032100c8044e0301c00102040040c0d181c040e42c0d8116007a0400080300d030000c5060171045480780070300311001c3c440c001a424040a805900042c4541e40c20441e842e0038074441d000c0042e001c02200f008d0404101c840c2c01d4000c0d02180c81d00700900056400312100c910b26965547c0302d00e160002c0d18200c41903500404c0708a00d0310400344c41440c0302e207011001000312030b10340000a511008103014001d540c41084002500c8a070040192849007a171044100aa40441c0d0724201140c03080c4500001255092174000560b022207402552a10340c0c04c042d4031894546141e40e490f2183d84001822810750050100 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 763146996 1250 763145746 763145777
    0x6050a1d040509010501030b13021c03270e070806130c020f0a11040f051308090a150309030806011e030509121308011b05040303030b0a05060a110f030a0806060703 72
    0x141d81e000710843c10012410b0b50661520909011008043d85044510080010096036604044100b05002101070b90940000340c181141d610b003103d901c00b2000004a24110300208010301184200e40580038115540e03145e2607c200c1d40b160f0300380c0b0015840f802034070200c141c0c6c1220b58000504a41140101c480b03890f218480d0a0600032074610946a080505600e0b12113400d103809003903605101d000d81000a40b030305c216031240703040d03196034081d2003000c001c135039110700d501c80301d01c2c038406000c502c01c000030b000d420783c18010090110018120005010340700440c003d94081e1084012000003070100d08204a2950b6084000700401800344400d403003414000e81400119000604d11a42024641c1101c1400d00c80c000d400e495640041c1c078481055100a0364031141d120007030b03c06580c0e062070302040154041c000620f0f9600581c014945c09480004c540b451141c011411160100440081d10364500d10b03081404d0b100c0c05104044004110300c3e01c0001d030185002d00080c402c1034402c0c1824034440a04a4 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 763148246 1250 763146996 763147001
    0x813090501060e03010f0e0d052d03061c050304150e06070317010605091f111c0e06042402070803040608040606050d120e1503040c1a0406050a1d04 65
    0xa00c002d011034030824030b1480c030342004c0c0500011500ca0310402e1000c441d0284885640c2d01012103e038003040703000b0560081b85003522082c04c0d540c48821102490710424008840b0340ca600c2503900521400d40c1c4e0000b540d85402c07080600c211550400c000d50f040520704030403001841140000c4004000074800326a820f580c510000c6c0100324017958400320402110a4403808080060b0842000d01c4820f04c02d104460342c9404403540d0101030504800928590244165904142240801128055120928510540c200c210f080403200c80e035903d0342e5030014000b40002c40c4500d01030482d018403d080d01800c44590030050940e44038161041740c01c0c96a442c18005c1c2542c009404c20000204088148800d025190140c800941800c480007481407a841d95034049100204d603076041407020021013610b03940e4032483c060300c0e400c0351021000c0d52890607161044240344e0b0743c0113138910b04c0084080001c820917008103840640389184c640900c0c06440f40d0094580003900700c4c2c180480c45010100000c01e440340e0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 763149496 1250 763148246 763148249
    0xd1803200120090301061d0105010c060905060f0405060c07030e060309160306090516080c04150f030c090c031104060309020f13051902210a060b040f1706040b040813090501 76
    0x58010b60303102c0141004041c25103401d54040c0c02c80391000070400010003510f0400310304403482401c114006194a2070040050298108003520364064801004000000d110400b482184980c0c151040b999800301c502101e4003810f0302c040c00160300e105511809003499030045800c00ca10303400302c0d07a44040340a182d9041c1021038100320f6240352a1411030f0f0030001e00b00411800702103040040303e42036003001c101700c1d540c4849100c824440ea40784c0c901e01c50300c41082200e020141007000c4034000c08039120304140303000004c1c034403c041d080e6103000311400140c0e21a00c1401c03408210010980d00d41443c105040300a018030302d0045e80e021a81c1d518400d10f40c0e65007200500c0b9950b045901040300e01c0c14407a030b20855905001901c4d81280104444101c001a8520b11040e800d1004001600341e110048071000401c0d00381c115411528000070b0119a1000700f00c0c180c0110f0b040c0403140c501142101001503105c01081c1c07070040c0501e03d40404103000a10443c040c000d0b8002c120662607856607205460000d44400303 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 763150746 1250 763149496 763149551
    0x20a030e060c071d0105030601030b16120e0f061f0e0702010609020d0c0807230a050d2301090b0a03080919090b2103090103090c0305030703050d18032001 68
    0x281d00c1074000c61098001145c01850301310040c0080d9807464a4011514000070700400000021369041d20406010700b84074030880f212054104000c40204480503590180000d12035000c0c0700c0d00c0002000c40348020807c120803000031603d00000341c41c100c045100c40d14003808950a6540f255004134854800384007800c106451540e0118201200e0103010b8080b08014222908212403a0205004800c00b10724084241001040c1550740d411608800c44060161001040034a4200800000800518002d4070490b060a500c01449030740e81e10054022a00e00c800541c0d08140104410000301d19107801401d000da40180c118500c00b61054609011601d468100e40c180c00d039240712071138140c180582c02d092450310724001c1c3c00b45c86045140d1a0754030301412015504042d12840c00c1c40802c030410074403400942c1d014088a8440c1110720780500f55400c41503c0c1030702945000c03100520790b10840c0341c1c014000d415498401171001c142140e40066640401d07034080543d00c17000788901da1648410000c106a40 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 763151996 1250 763150746 763150769
    0x30706050a020712020a051203060102011409030c06061e1504092a021b0d02153c0d0f111c0b03210d060b28050a020a030e060c07 57
    0xc3e0b1402c44115a60705500204550181c00400e0009070300290700d44030910281c0c1c01d50780b01c1d0ba030ac0004031701400d4841c409112080303004060200f82d0200001074003403000b0308401e44865640e00c2040c40241c41c030407544800150998080c1403240c1c20300000513640d120540901510b407a0301c50040758143c840e0b04601c0a400444440c000d9100c085034a10003002c41d10500c0a42000c50000c920250800c0c40c45c1d00c918800c9a0000c0b0603400c41d940c044002d0000c0c868800071580f2254500c0d256080d2642040c60203c071503100b4048242c08408100c4541e0380e41840441031814032180309440002044014051a490b580d150507402d41100214040c103040d05c166240f0b0f00c45440d0343c071940402d60708070f690030b14081e9121118020724100c1810060141d074002d0b80d2907984078940e0800c0c41000c1e03c8181c0c083d1503990305c00241020b03050740702070401e0203464400109412041c210003040300d0500c1074046100040c1c0154100c9400644681560f861030400204413030f08000395803a400d4181300443c4c1c002c440004c3d = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 763153246 1250 763151996 763152007
    0xf060605070318141e0909030714060f0c09042a0306091401150509190e13050705010f0905100504030311060f0105060c03130605090406081b010f02030706050a02 71
    0x107a000d01106042da90080022a0b03d510300884d88540c50ba4054960384030b1525424005500c015200e180e03590200000c1003401c2a050040c4582d8899102050035201e00b540408072610709400042e03c540541c0010110b0b03d4580d0740c0c0b51144803544c0210b810740350f0250b140c0d00045583c034855218030441805500105040484148018044500c650700c441d503524144080c040c0f54810704407050b41103905482e08175080b055800d4040b04c1f64440c2c511506d43c44032035006c82605444500c042c41080d03800d0b03041503403420349940003d2608040500e000a01c0c56100c0c101c18041940300d9005154024128204041d5281d103030000602ca15008135500000a0008a000c209050b4002c0032480800003040c0600102d05100c03804010b9484140034403402000001180c0190740b80c10400c50f500802034581c4286025144d1034002c02d43e621120009105034100840414840340105000c0c02c0b107040b01c90811070f45085400152240000d0111402c00e5004c1440032202040e00740c001d041c072030f039441a00140c2ea40c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 763154496 1250 763153246 763153253
    0x411180114011b02010c080d06151b0507031202030c1212060a0f03030c23010501090c031802090a1b020c030115080607030b2101090b011202010519030f06060507 71
    0x1401d06410414041c01600d510034441605440c1a40c081c83c121a510000c0d062240c0d640c0b00b03800c0a10304417460038000080b0040000110711030740300556194403203114031907a2400f00c42c11004000c0c0c46a00110010400031f000c1100d01c005240b801d006036418207120406041c00c282c950603100c501044006149040406104940c940c0000c00310707501170040e820540d130800c3c0105107000003000c0c403401c1039018090280c48038154020b010100501030940e024a0340c028007a1100f0304c1807441e41c07070801c9503400d45140240222000d6207210703100c0b04d4480006070200108000003401d1860a0343c0d50301c1c0c400440840c000d0f048130407161507400800c454a181002c2c18219016038251014105000806001407400406c2c0750f81c000c02189004100690300500040c422060002d1503151490141c105102643c019004003902d1800f41040a500360381e42c285010300480d58080c0280000c100700400b1000941c00303101443c44038414980000d00c04030340c8914000f00c9480d030300a240030910101e07010080 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 763155746 1250 763154496 763154519
    0x60f090d022706150a0c061e0207050c18090a1115281404091a03010f06170115030201080a2003251d18010b031b0702090f04111801 58
    0x1014001d40134a241c042c6841000702105e103c2400140f60948480b228203a040a19840401c0c06000d00702c211750368802c91a040d80c0d203c072400c80303690048a4045e102c0c2d6070008140706192084501c04094a810486e594403c0448007000c10303a282d018000d08a060480681407010300952300d04840000009421314100152141541401000b041940d5112164010016041d00c081b21005c07a004a0b01d404416102c0f92182001a40c958144d0f290034100e0402c0c081d290800341c21540c031021070607920903440750721a09030b13804550f00400c0034a010000704019482002d0407a0300010103c000601e290051040c00d081e9040004030560030b01c00401403105d601c076003074009000243c1c400039040b0000c0d850100a06000d008050f12401e607aa803140d80f50700c50700d038440480480c410310a0081a250384a280001460b08107890f0040b04d40c01d0b4002c0d00314100481800c132428680c004101c500c0941e1071113146442028014800c459442210700d105010303480d440082d10782000c00c0e0b451150a503040000b401c41 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 763156996 1250 763155746 763155769
    0x11150f07090e070507170c1621120c1b06030c030e0a12050313050601080307062304061104180504050c0103061a220602030a0806060f090d022706 64
    0xb4420000000d102c6081d800000b155440c2e80e1021200c1c600c41151005424103000e00c00c1101458050848103422074070180107610b082d60800f8411840b8101d41140f040740c800078488000f0641c40103031010792441030141c2000c1d1005840b9a9888240507218050090911210344c40f19000c039460300c003800c04864040c020303c40c814102d04002d241040380c0d034070ba9111b072a051440c400203100340040440c5100f2030032445440d48a400004840040d41d6400245649074850300c002e480507490900400c2840c90f0f0441804684800c518520100f525680c072030900a08032a41b00e03101d40703042040001640200c2c0c0442010103494814000b03124605401d2560a002c030010b020790405150080900071140c41c07584d00c0000d4152104066154a001c10350711550b14201a0301080081044400040a5a001004100c0c070f00751551910401d490300401c0c4815405294040d18404000707000043c1a42080707070400d05110300080581e08030300040008d00304400031840081c03401c20b13102d0040200d40d0506100504 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 763158246 1250 763156996 763157009
    0x307090207050d052d1306172a0a170a09020a0503030910050d140910060905010e06130b04022a0a1e050115090c0206070f05040611150f0709 62
    0x10f20700340c9210200507010000c0710f0300102101c103000111075141c0345d01c01507031924410550b50364880c3e503c8a20260400d043c1100503001101d8100000d010b04d4040184150400c00c09489074440b000180041903280e002685080c0420081622104400203041c60362401502e440e1000100d10105005210319160243c1009000780e0040229000640301c0c0f861041380024a0b10702075490300ca0202082e00501507036208440e403101c24006005c0c1c0c214002c0b940e252815400380b4104201aa9000030740243d1f0000d1103100240861480040c103e030401d40c89006440304c0e610130000d0b0211100300007038200c0c1c00031000501814800c1940141500c110b411400c02d11400c01d0080260b2042c81d034450403e013420034107a01402ca4403800e144108070003500507060040b04e10b40c0c0449015125a104070003000680310510040c4150000704d0415406040681c1ca40a040d5641e1454242421020b540c00003075961036032118030400000301400600c1740b07d600e0080c8400ca114450500b4100001449500c46801c40d1 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 763159496 1250 763158246 763158257
    0xb40061d160303120b04090602040914090a2d0605090706090801050f072318091503060a02031803040f080d180e04030309063303020a0902031003020307090207050d 72
    0x3800484d03084940da01c1000c0380018013103245030751040400c000d05400000184507a00104001c0b40350515500165170004031311030b080c907607583e03035070101c41c0c0d688501200030b04280f00d500708551400440300d0071180b81d030745843e40007900c8031282d0351a00100c800484060031160803c6005100059010042c0002001c081c0000d22660422510003050414003034161010301407a080b400350f9003039002d03044840c2200707450b0710725840d0682d01c0c00103008001c0e0b0980d05071040c0d0000c8000360704540f110380d031401a004082c00800f540d40e512801c2000941c805481c0030100b0341419614070a81c2c81c02c000800c007818101640442c0d051510100600c1c01d1048602d07001400340403503c0d01050740c0d160080c44100e54480c9554120b41c0c840e0304050300201503024014111604258840841070705901120f0340003020115201d40061019140105c03000060000a40c4010044000c0000f00b025401441e04001030141c1d0b800ea45079070703500192402000f684640700b2180c000c078008050200030300042441030f8403130270304 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 763160746 1250 763159496 763159499
    0x7030c022e0c02120403030e010816020309010f02010e0d0e030601080606150f092706100c02130b0d030207060305090d0c1203090602040f030b40061d16 67
    0x194140604981500d15540e981c5042d2914094400c01c41041c18808210003540d0f200c0e00c82c1001400c1414004086010501803c040390703c821940182c022204160b60142d402c00e02d0020044825070703a108040c1045640301d607110105654188000910005240c0700c212150b2820700600d818000140c0c1300c81d0898103c0820407c160f100c0130b005100c0c5a040c414660303545e04100d02403400b1405502c40b46600800300300409201c414103107a001c0b2a0302d10904c03a03401c02d562580304011201c0d03c4036503034000183c05141181c0060030b101000c80000402d141e00403420311800340c00305442c02c0e0154402d41c016030221500700009a010300c210b9820100d4040500740201300100c0107002e030500041c00403c14800008415602e5210354000c0b29180d5100b1401e40d0388990702c1812004294040c00306480c0b204191002c1443c90031001400d02844042d05488a2080720301046503001d02c000d00c0c003038030740030300504000c070300284803485480082085003402405c10411061403a1500c915984071380800d0344840c40 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 763161996 1250 763160746 763160803
    0x209044116062f060a0c030b0d0507050d08040308160b090f1203040503130f05040c02160515120903031626070908100501031101080f04150902030607030c02 69
    0x9940440c3c180f5018002da0040c150000c102d4003608003038202c101402602c0600807000c009401c4000840314030b030740c244078a50441c42041042120503000500a61228800f00242e080c040b010303005450050240c0c6003890340c0c94840000c40c0d84042c01204824004480c400c0c10000520101c0d5008070801c401080008900c14200340d8900d18128215140c0310044005010440e08200302e40c200741403d0035407100969220360703400e4402c00d075004042c8500d081200d404502c42c8002044400c40c0400070300c41c4002450081800b02034024104904090181004020680c0c608410341d00c3c080c102800045a480c641412409a0b00320041c207d0807c002c0312185011702c3c4203400c040664001034200100109031150b0a0507140c100c503030340c003c60304d900130190300f0b40b00328041c0c0e032090303040340d005150300040205000011910b5250840c1c0413070010aa240c0400c1c0410b400c600e100440da5132000c000112024150002031400c4c0b41200c031000000d856a281d170104a07410300012403a079804c0300c41d00401e4500001c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 763163246 1250 763161996 763162007
    0x1060810200f0d02071131110405121c09140d050c09070201180b010f050301051b0f070204090b060a050621060d080f030f090a020904411606 62
    0x90340fa02603034001c07880340144020400442d80e01c80000304000c048a01c003107010a075618803d03c0540c800c8003201c03884801d07041c090041c07640340d200201826103040d0600341000599150018411840c2c4540c0d41a030781c000b0603550340b0000b400c4031500e40b80e000e90b2402d02d00301024207100e00e4490060301440030b0480014030004849074142d41c00c840300c0303031079503111f040403401440942c0e4a4568440607455500900420301c51150580703860010040d28903031100281070070707900c0c15540150a010b030084109144100071002d4800c40841e2849076150618940005060b144a084c00750392240c0140248001c500c1c01401d990000c000c20f43c0d195050182001c4103580c40d04540b6a02510544c1c0503000038040d41c0c5000040070341c1035002c0c41c569110000c900c141c80c80c1c0d42040700c01201e440850000728002d05400202e09514a500400c03988480d5129039803115103540003c04140144903803c8200c0304c0c070440f400d203507409161011405800c1c0085407007103864100c06d041014030703001c6421003c5c000107a004 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 763164496 1250 763163246 763163257
    0x30a1515031802090c09090108070f0e1b0a03060806060102060c030c0a030f0c0c02090106020a120f0e03070b270d031407080c0109020906040c090e060301060810200f 73
    0x103060010b00c0640c601681e01c1610000702d002903009034018104905508804090040000240d4110340e440c1e89510f40d0564070b600700c0c060700e40700700c20002e400c0000381b40c140c8485e40e0004510504010540200f4103a080c0b80d000314207034a0111307498003014040034200300040c56002c0f0b02440200034a04021120220381d1001034440c009007000090242c0c0118042e4220400e081107011040090041b084002040075100d480100c0c810f030019030000032443d10004200c000d541d0050490424019000b0b42510301b0300c030340b9080505002c0800c50b000c030a694244034003001801038507601d6030766111f5142e41310b614070000c103102180d02d00d100700e00c0d10168446841d61008c055140c200404480c0503800502c03058018420010141d6000140f840700110701034028501207482503501c0c030004d4584000304410794910f0580900040c091070006c02c0802c214090745074001001274000160b26450f000030600f040e910700010f040c850303110300c2510241034840e90484007045070220014282a5038814141462050 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 763165746 1250 763164496 763164539
    0x801170303070f0e0411120a050112050c0d0c03051c0e0105040b1210050d050d0f1d011d041514010f0918022802010b0901080717010e03030c030a15 65
    0x8013600e56681d80c070356a10500b020807400061b1038854045078042583c64000701d40c004491406e00c000010380c00c072000007401c00f0317962010240590095080078041c618850180903120071481141c000701182c414403401014a04002101516a10200011f007440c0300c0a2503041c10054100700c1003102402100a4400210780300010110a031034072076107040040042d070052603100b01c8075402c0200b001000940a502c880c026100e88650701e40c01c402c29100072240d41e8829560021350900c40045620a0f544e404e030340040200b80000141e440004241240c1d00b030042039843c451009000e00643e0458107001c0c0020609203801c0c0d044104070840103088402c14440c40c1b0810320100c0d60203004a4054060310140215008010001ca00600c90035800f142d1300f12403075015520f0803505c80003604140441c0c1f8103a0301e407a00107080c802e00d00700c0203071400b00d00402401a41c1d540ca0154171804042800114002d8580700c000c00c1e164244407804030300b01e40e25034411050f4148000c20403c0090300f40e481c5201c2c0b0011 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 763166996 1250 763165746 763165757
    0x608061909050f0d0c330b0d0605151f0507150603240510050f12030f16020a060f080a051f030503031f0e0a11040905070801170303070f 60
    0x110301e061850109041d0001460f030250207540801940d100300f00d00003072801080909001d48050b010044520140d250200b00b410b20b070290741b840d26429800440003a000680b8403103420b400f03500c50b04201d480c10394142c1c2c403000000100310002c0c0b60101c134540c0340490b4217264418842e190100608036100b02c080003415112103c0103502d841c01d699100000440c0c00141c9a0025840200d102201c0d100d6405406406494440481c50b1000750201c3c080c150b078409002c0c03c170b4900c0c6103401c020b03900c005218010501c0c03100308040d000b1f1161100140c0301c05000c4000c1a5000e01712403041242c510301340e4100000b00040d0410b00d58401d82e00078202508103040183c00649602d4412100c0b00e21540741c55036240e2081c098800108000001004502c00c02d460303800064002d107031501d4002107211601c01d814994800e03501003519a00190b01440350324801403400b5140c280d0f1811100c05490040b070300c0c02d0204003400010003546610540203c035003103420026501c0c5203400e51000c0c03e24600004c00404100 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 763168246 1250 763166996 763167011
    0x240a0b03070f0207030b0903070312180201050f0d091505010b57010b040c090506030a0618061401030b030a03110f01061212020c0d03031a0a0b070606080619 69
    0x14024002940550f070060101c1d506c07450b01c050300603640c1d40094001c40001c0c501c8444000030305500d00c00d0403800c902d88440784403640451703001100c8a401c0f01801c0e41226604118883c0c0c03282191003007944492040320035030380005125006c5412618164001040000c0c1002526190200c54100049004010031000b0b20300d43c1c49a54100543c0110a07a2000c4c03041d14611424003101e0b042d40301850801d038100a0003e645204140000c1e59a00061980814049001030041e07180034405158001500310380020f110390b4500040b0740c0300c4906483d103001c46544000a02c0300c00312070610b45010703e0082c20b05020140c0e2603008641d9616004001408124203012a60b0b6070f55801e021a0306000b004030028440c9507100c1c0c0607800b05400100044510f85031031400503840074002304076130b00d42031801407002c0117040154400760054469500d660100b5100c0d1504140c980d640c08180c0c502420031140300d9038031100640340c0202100e11079000001c55a11490401003114008103c03508511200300e00400d034030 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 763169496 1250 763168246 763168277
    0x70906030c120c091d06090705060a0509040b03121908010302060d020901030e1c090e150607050c06040f1403071410030f1a09011a070821240a0b0307 66
    0x624003504072040d01c82c181410000c881700f40a0b8070785210f4946805079aa07a498000d64150b84080500c9065049041404201c4241d0300860240606c020080d001280351104c0c000000d050000d00195403804102c0441d614001c2c04403084c0381d030614812070800050950454001415030b000f10304418880c82d800080d0004140d2081e00710701d0206801108a405100241310b03080c145101003085440010b08801000038080741c100180c2c1e000780031400000b80f01c5c410350310a10810354050755064895100c1c2c5a114111a02c440000380000c1a64072440d03040c480c240b1182103044001d100c162417191340400000c1c8440d50012074101900c91382118508840d054081064002d4204072200e81005850060b0003162803200d1408080c41d07810481e84180e0036070f210641b1a104c40c1005800d441c0c0a0414001c510005041400601c1c030349000000142ea0300000980e81150340500f101c80d04189150481103214200c00800e51071102441100d42003034440c00c05107030250902004081c03c040040c00040303c50342 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 763170746 1250 763169496 763169513
    0x90f050d1a091b0d080919030507061805010c0528020a09020304050d0f020604261801020c0409020915121b09060909060415020f0417070906030c12 65
    0x3003201c556940341042c500401840d8480c00100e00510701c00b000400480c0e070030310b000f180c1100340e2544070891a0900151784113001c2c3c4040c1703a0140b404450320040d40480800c0742084180001d00352641d0340e0381c0031031200178034244070b06060707100c1c50503c0112106900041c0300401c00e49209103100e01040001c0c0c050302c2401001c5820401c0207500308600b0380002c41d49800540095120301d00540854840704640c0d05c04403100c1c0120004000180c000380c011a00003030030200300380c000c02039420100c1c00549000c0400a15580040c44031882501d1b00c080c0c104c00b558061190705100d20041320304001c0c12803240c004c2089460002c00100034800300c55444105a0b41c0c0d00610b080d19482c0108076503142d048404201421a50185020311400340c8500083c040d01e06044002d00c10010358000d841c0319105e5903121000350700e2000e0f001d0400c0d9000c0c05502c1160b20010081e01c01070980b1101ca2000b05038264001e07040c900617030458400b1a08007941840071540343c9005104481907412007007220041405c05514 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 763171996 1250 763170746 763170773
    0x12030b0303090a09090501050c040305060f0702010f020c340e180f1f060b0d050601270e1e06060f120a02030108010b2d040b031c020607090f050d 64
    0x14042d010541c0030404035903a17032050842a02c20402000161036926102026001d2444005c0c0703141d00200002d2108040300080d0340e040040d900011840340c000851030000d03030300102a000c600d944040240305c0e010f0080c0040d40d95000c018000c0340881c80c00c003085015010158001c4004400c4e291010070969034050850300e078251420380c15546248108030046845840c030745807880040459500c20f400301c04807885400100c9021070b1040d0f19001c490404180684070003800c107410700a0720b48954100076a040b114000200d00070a0000c3d0107810050407580c0441c024046c0200110695800c4103480f9041d15803d80040f8115080c544404419807d00c40030f01c174411040640800000178040c0243d40c0c2d4001d1b41c16038141c10000c1c0905007450044c00340c40d044c81c0000401900c0e90b4803034145031481c5101e404400f10005040440c40c51031040c0480c2c6000d00401184401e0300c00410007204840e414000030390428a03034940340c0d4a4501e05002c4c81c4109919000d0948240c1c1c601c2d21200801c60800241130 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 763173246 1250 763171996 763171999
    0x51e0322080d0e27060f0402090306070504182304021201020415030c0503070819181101110601030515180a05070f0603180b04080c030c2812030b030309 67
    0xd0040c009000c005000c0840c8082c2140501152100074640800b040c000f0306540c203034004c4e1100155901030810220b462051071442e080b0707900304443c00c6152418001c1c288164007640b0354594882c504035010703031503c41600601e4a85427601e00340c050310700100080746104201705038202480b0380340c43c0002825440700400d4590389606c0054000350380380d00d1100740c5500740c0540d101045542c0c078090007a0344520017180d681e00007a9000d40050407801d0b064554140f4685075840c0020102524008032202c1ca050010580300c00b1044080000e0075070344030328400c10325401000a00003a500d15a00c05a4440e80c02d0410100e0401036030001c0c0c1c0c1240c03841c02c017a610401480440740c9000090a00c0c0b0340f030f90700501800ea200c42080d40d0220f0024068010801000c09001e41c04c0140501a26610071000001d04102c07040701040000e0440280c00b00050054103421201520882c40020828442c803c4500c003041d5480d816140300e040443e4100040c00e0034034189050114a0a44a00c0000d085104401146 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 763174496 1250 763173246 763173253
    0x4080715050c0a0605160507050d030e030904090b0f010518010b1c0c110114090a020402090a080106180506011b0803060d12030e060903070804060f030f09060207051e032208 76
    0x204244131107500401d0040840c0360a80e003030180c04010844061282c1c200190032584009520701c0520703c00d42c0201e020440c0b60003500d040c0004000010305946017968166011414541488100c4141450741401002c0031a10401d0350b40c2c076071511941c0d0034014424482e05038030118041400e6024001c81c2501c0f400b843e041008045640c14020b441d214079040022400e61034403010280f2a034484050a016014003402481179241036801c00c03010358000407a580c1c11115540d00000e194109000d810051b000d0080b4540b4070b120302c45035140441c1d0340107005c40d0401c14048564260780708081c031020032844d084420184d49540e443d0102d44e20103100180180040c0c2c120311102c82c803551540c000410054854156440d603228815030940c0c038010103002500040c2d0401040010601400340d58806146508000c02e003018003100d0441101d01c800e0040d0383d90380e0009503960800005204141694105041114a50301094446560383c007030b0581c000ca1030b41e581c3d9009442010b80c0d6810348002c11700c49044 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 763175746 1250 763174496 763174513
    0x6160501060b03180c011e2f0f120412050a0b090622021507031806021b1c0b06031e0106031205030c031b04081e07060504080715050c 59
    0x903015030086560311600c0d0105200034521543c003140420540405031f42d490355242d038403d00d640d1030403400c140da0018440801034007080041d01400c5040d034040b036501038070103640b6510101401c10000c0d800020303003a00100418201d8032850003c2e0b40503140c4603102c01c1403803440c52501c02d02c4c00d5402e00780a0700612405041000d04000018803a01c40d00c2d031248a00e110f440c407090a640d80444040000b58482d1241c151310400e02185c0d005407103154003c3c5491191710b0045d100c1040b180055030884030040e0000707580ca04070700c00c1040740c100030200c090312010340e4503000120422070320102ca00024407981500d004102156010000003046220000d0707001d550f4451640b0041c0280241d00c401c58110300304040d60001240a00d0070340703100e4041d0503101c030320350303039401413002c50f100000484d4003c0c222003804041981041000201c81c01c080c10181c1140341f0b01c080806524000c1075603c031310200700d010041030121090215030a422150349400e880304036000c030381d403e039400d018142e00c0c0710301e61195501 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 763176996 1250 763175746 763175759
    0x3190e0105070f0b10120506010504091e050c1e0d0201030b040e030a0e0a0f08062a031611010605130b0f060313030f030c0f080907030605010f18060303020a020616050106 75
    0x40c43e80903040161702103d40541d60005040c090000c284054125003002d80108064280b80d04000304682c8610704c0c000020f20140034804945070481d10641e5240d1002061850a04203050218061074805807000c031000f902d440042c98074224501c0082c10035444002e0b8010340e84554224901c0c031030b031640a5035110080c0280041801145468161042c0c04040c0d00140c500381904078102500c9050000d0b0240b0343e1181c3c0440b1800846046040c207402140f00c0c6480600440741c09035000300128204209140f8050100401c482c2600c445c07000d061345048400c00c0203a81d5918610351b401a0494003244ae081c400d000580c40074060742440d07401840001c01c008113400c2128444160303502c40d4031156030304494218110704490344035480c100032038441e880c1032060500440380103600c0708031714003211011600da030b07104000d0f00d0007a80701202c60142d814091100754100078940100c198090000c004003895600d000f940c0710280307071010f40917040000b011032a454142c1088208a034006009002255030b401 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 763178246 1250 763176996 763177013
    0xa18090c0e0a060504030b0c0c0709230621030906070305040302130c0801300b101d01030b09030408010615200c0112020d06030f0b0903190e0105070f 66
    0x240200006611007052035071850284040d40c2a41d05683d03802d4203080c1190365032601030001910030511500140300e003c11022007080400003030108507a011030001c4030760300500d401044141d8429072551132030042064541340c0220300c0d03940c4410300412000042072f0520107030451184607845500104000385041c01e0540003801081180e2094903090b000c601040000411218400d0002000071005801009960005025188400380620300003964030400340c0d08080386400c15001b1030f29901c020b400c1200340700d0382d4a8400000d090580242e180050016040e00044405010090024004002081004008105560140451400801a0316141e0700e0750100d1800f06a100000035010001252038421400d08400d14041b04200411440c660500152440040d180001c0c00a07036080c0442e00600f003490242600841c01400500721402d40c0c0c0c1400c20240c00c0080000d04140d00c200410040c080303c5c04401d0003e810685480c0381c0c9000404012145c42c03040302c40141c022410b44000005100114 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 763179496 1250 763178246 763178261
    0x40c050408062721300a0c0207050102060612070305030301081c0e010e0d050120030a0605010c260403080301080c01020d0f02120d060308120f07030b090403050a1809 73
    0x14081c01d206038a024100f00e54442081a0108110381d040c9126490011550054880b104200a80c07844840880d0401c60300d0156111000506120710070034081c500d5124842c09160781c810348042c0510600780300001c0d54803240500030381d00414446d41051040b00c41440044042c607130040980c4e94a5a40d4100755542d0001280004100f40c0c4031004000854010350990b100400180c40345000c03000032508000505102180542d070954075071445020070702100c1511101075000f6070419031130342049841c1d40200d0304150402c034184104001071101060202240d209804219055440c1603035111100b80d80c81c1c0269400100342060100022a450300c001c0303020740201d003080e03089130700d00070a000c4116200402c42e0a0075000d600703c030312003001d02900340c00100809180828042800c5980303030f840f5a01c5901441154059502036030a2080c3c9081816912b40c0101e001c5c134041c00256070140001f04804400741008060000014612080300c0c055002c01c1c2203100051940e0100c40c0d6500a00740150090 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 763180746 1250 763179496 763179541
    0x70b1003120513120c0513140c1201151407051507030b09070e1018240807030e03030f25021608030c03030c0306120a08071406090c040c05040806 64
    0x140000c640071821003241300d0752903040005004140d2a040900010107403000304045415268850044c14281e000e500d2400740e03551310442503075400660340549041c0c2040c0c000340e0b11410b06100490f0495170107a14200040c2143d504140d580629180951510451910000302c0e008580c0400424640550219000020942c1c3da00104d68494500304e42070281d0102d00d542c0042c280c01c40c1408a445081070803101501180c0c8144850348030302c0c03800e03960050600304860b007002030b02000c0c0001c4d5210b500641c018015041c14443f0030840c050071034690100801000703500e16443c000407407809802c0800c082d00f896889030110203c0444400a4441c01591203900703a04140890000304048000304840e40412404043d504586529004020350b40c800b4003803950052800d45541c07001003050200c2038010f4030a51031640e440c40185069a4101104080900c464100030308000a01801080c1881c110608803800550042e90500035260390065401541941c464402081035100804041030704c405013 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 763181996 1250 763180746 763180777
    0x615150e090a0b092a07080a03060b07030906030545030702030703020f010c0212030406020c0d0b060d02131409011103070f11030d0e010b13020c03070b10031205 71
    0x1180b1441c0c1c4159628000d03256000381d84400000c0352003a009510511890080d01180c040410111810b05c803900503c2080d900004c0005101c0c00c001d806205203001001c04c2081141003240d130340c90140540400b0300c81d4900b41500c0d2000289000011012004a0003a80d10070b000004a103040380601c84001101d503564540e600407803201c0300c0c0310000c15a01015030040085c06c41500b035074244a8861910380b031440c140b1984412000042c0d07110b036903420052a80f24029519180b500304024600090480307100c0c091180002520046089030140783d40c805410b0311250b4000041e440400c03103c015900d8242011303494800318071000c8540e56503040c040c0e00c1d03100007400780e6001c1000e030450510081c2d8001c03010039080d15402600a0041c10142445e0210b10b041e60704280483c4060825100380c0a40b40017079955400a2803018689540301c0d101030040e6100460030003d200a14541d240305a0030042d18080c40e02c0c001a0f40f041c00030f0910005103500050302c03d0003c1d0b10070b10240481c0c011441d010003001 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 763183246 1250 763181996 763182001
    0x81b100b010e060f07150903110d050306010f08130813060e060f03160c0501050117100c050324040c0e12010905070302010e060706050411010f1b0615150e09 69
    0x40c46100c291207400c8006000d0740c908402c000484120b40c3c0070550451b80c1981581d000000c4000b00e10683c408203000f41c844107039050320b100079642082c0c0c0b504561400d124090050080c5039902c03100140001605040501098580d244055480b4a464100038201c0c0000101000380000e42501e41c2c044543c00d440e0148118101020400306000c1c84443d401486800c0c00001d81c0141800382d0100202c000e410602d6003032603652101c40c02d43e41c00360000403071100c904082d40440d20b8104600c29082030700180800008004080083c0584009040005030b0010590000901d001000d200da04000004000300b00c0890103040140403002ea80906912a40e080520901140018010b00e4041a4018090f240440c1503034019109070000c4811320f500480e09002600001e0800d201e030601603805a43e003484101401e5000400b02d5100010850401282880a41c0203031070307030742101c00311030f0380704002042d150350001c0c1700c05401a4540c04075001d4010f02c0e210108550708022148445441590141d403950b = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 763184496 1250 763183246 763183249
    0x19150c081306020310170a0c05010e0d0611040906080f0f240a020904050a06093b0a120809070906050f1908011a100207030f0f081b100b 60
    0x4a8040358000d00e88030301c100c161800114180d0055078000c144003601c5103003903112001d152081075043d010346d2465101c0140d030001d12280c0450140140424600640820200350225800f40300002004068030b4840308483d440a1200054030f0107001500000c0000541c5d8181455661040e803020524034020000c01581a003030104803038146d42100c00d4483c5640026101e40185200f000388804807a960034009000c403903555000740c074050710503035002041c12030824520404442d550245c00c0b003003141d090780201d1607042c600856810501c5004184000c0c080000c002e80c1800095038004150100920b1815201a0051003041c040c1810004503140503880d00c0c8880d049070105d00403940d002080400342da08a20302003442010400b0560b9a01101b075513190314a5007918000044009445902000900a0b0801901460203c0258401429020301d992036030400003034020009040011941c400500f4040c20030102d45a88100d091a50b124208140f83c2548908020b02c86d01007503800c18100300e10b41d = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 763185746 1250 763184496 763184507
    0x1303170c12090a1508160305060a03080c161203140a050d02070606150e010305060910121b03141b01080c090a05040c03150f060c020904030219150c 65
    0x414400340001d0191840150400529420500b0401d80c05010200040703000c9051199900070000c1d19201d42c5003509095010341d1102203030354941c10030503140404001c0380b50340e0b9100c12400c030307600402d4480c2d0364281108458140602d510151800040b00c2070006006681d200d10901041e0296507801e104681c1c0005a80c43c910840e103908000071014405006959510340c000c2c500380c0d10842001038025070303075159850426244011007010500b0500300c00b01d43e5806000e007c2d408102110000b00394908407031005428407050140f02101d0b49602400c2c000c2000088061888550100800745865503901d03044403103040c4000028a50b015204410b05210b0710040442d04a00c0d050b10f46201507a6078003511442c0d500101c0c881130307102c981000700040035125032065800b15411940c000c1000e90903da079429000100381d0001494055081e0208002503011001507500c42d411a40740003d9280e0381400c034600840120401480b8049405190400503e9090300c507032407010800034000c0c4503e080c010388030f = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 763186996 1250 763185746 763185757
    0x4030207090b032d0d021b0105071a040c0314060402041802030c280902030114180105011d09070c06051b070f03022d060a02040b16021302130317 64
    0xc066100b004100c644e103e610301161080a210036050144a440660151510842240001c003580000074803007141c84900d802007107145c10a08100c0e1a201e0140c3c1c8903204460507264115200e0441c402203030800041c1c0b00110f00441e00b1981c1c4480140c2d0080300c694076900e041d242284514500440110038100100e21442000d4008018000b2444020103001840341d038100d10b4201e00c8208a03040c0c10309600700c00b0791806400c661500680781d41c100310802d030448448203c581e01c030b18007040140380110300120469054035000c1c03070454504c400a03551034800308800b25040c1e40c403034940d10410802d1503015044802c968055401032120f515248104100006003078006c501c0300b6030800c413510124001100c0f250b0094030034811a501d01041205205010b030b50740086a0400c0c0b10580100c111090401c9415004074490b1411072505145c10071347c00003445284070500349802c04600076003e40d914170b41c0f140f0103074150305415980c6141c400d00d480d000c1c0e10b150004030313106500c0814841400050300180c81c0c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 763188246 1250 763186996 763186999
    0x703030906090e0f0f04030e100905120f120915070506040b060402040b041707030b0702030c06071b140f030a0c1b080c061e040303080121050c0609041107050604030207090b 76
    0x8515803109017142d03d03000b10080c801e506200c90341c03500f131130b064aa44810202c0d00459640300d4201506000820072448240c58440302254042c40800c504c0b0600400c2443c0780e140714203e025600c01c07420b00441c41000084840c151035440c0840c6039000d000c004164107210b42e1103403440d912a59560404c000c200d00841c0140f840c2d66030300380300c14082040208410b541018803803086514090b40d90360f0b60b0003800d00849402006800110b03185200210030400503030410018100a0075010901e0b00681d45410442c0300640240f02c003912120300c0306000e0003850100000e030025a0b54031418144040c0c43d0403202d40d82115805540001c0c85030070801c0401002c2591503142c0031302803080c00380081002d80e0300302c060800c0054118100c10240c40c0d40c5035004000440c401d44481741103614001c5404064029035010010058525642800140d80031400700300c1081c003102d8180e1100458408140282404601005946070003d42c003014881c0004045125910039400c0b01c1015407240b02e003000b40c6060340c9849 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 763189496 1250 763188246 763188271
    0x4020a0e07300524010c06020c010e0a0b0a0e0d0507030c0c06030b0109060c020603150a08190b01150f081009020309010605120714090612010c0917030909010918050703030906090e 79
    0x8003111740c0b05144c10ba0b5038a00400d400345c00c114101c1e020703e086804089903a20a070340107004110410440c0090980e01c00d041c400d080000c540624a095200c052040c4034400b00100018040d0406000d400e0303491040307402070940c403542603e54401600a1207941030040c080744e000200011418810b0030100111580508810304585655005402c11008801c281e40d00502902011401d0348040000b000750141034441c140c8050010304024004c00b10682001840c0ca07915450941c203035030401200c0d0121119450500364640d1041e0540c6411006504080c15060000003409070709801500080107550084400036441038005280b41c0d80d641088c802c10030105c5003c3c210030082e02d000301440740e00c10400380444d5590031119000c582185e64500000000ca5415001440b29101003038820510204520085162107101c034000707141840144641c404003034607004941d0420844500051070550300c0001c507821140c680c0740c0a8020041c6000c1c2800081e00d05200260a1042242c664041d04a03c401c0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 763190746 1250 763189496 763189561
    0xb091812090307080d0c0201080105040b01020a1b1a0c0f03131502100204031a060909032a0304030f031707050a18170703110301020304020a0e073005 66
    0x1040c1464114824155040c003501000040e81c500a11031405280c01c990740c0d840c00c50610344005480d034032060300300d0f5009516081c1040b4407660000784251582d034118035261014815031410340013002464200b4400303080300074990f4000c00001005021100d2030305054600b003030070580a042d0750740101581c0c5401c48507588010400c0c9112b0700c245035100c1050b407050340c003000b4481104a040c0e03401030b0300884a085144841c03089000760f0044054000d0021030b141081410043c4070f282d9640100a02400011013002d0810071062400603944c94585820003560f40701c0e5507034201034100c2d5101c054160301003101c082000c0c1c0c00281d00901d5070310510194980a0500e0982c010071610314040903030200e90280320302e4006c642e91220100040d9000c03803071002400c041d402c41c942400039040790464640aa0b005106100042c0e0b501b0156000751040008000d400d540c071610100c3d0070f890b50062000180000961401000c000700c2000d0100300241c0a041c442d5440c1c41661040c02c00b4440d400c4520b84201007103 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 763191996 1250 763190746 763190773
    0x1b010806090705070c15031b0504062f061e04030212222405070804050f0d0807060c0801120b07050f0c010f020d0c410304060b0918 58
    0x1c554100c1554500349040c82240c0d13455200382c1c1450341000401c0746903208520102d503414001c0f0960300b07002c0300c0a40001c020b0401d0280940c0500e01801d0107201001000b42802d16490701886024641c8000300314042c0c40484d11203442c0e0724155024000d1020000e0901c0d0780d00381c2c4a07001c0303009980c140c0c000c2051407100400400d20360800092688001040388198040703850074107124001e40629242002004910f013403441b0000c1464010109018040c4403d07404035001c5020303a411a0340a659aa00d4441c00c0c2d000240501284a0000d103003010200f00078043c42080d0b80300e03078051000c40c0c42e4804903907206c240c19030b04021b02c008014805122800007aa801c0d01c90406405024411081c01e41400d49081803a402d41e0b04a2a411103d55804100d40d20300344402e000340341c132030300c01d41c00c080901c61a8040580c08085c8020382c10300c10381a81c03125140113442d020702000341d0014070310249626400d05103400d101402c09140041e11540c0301c04049a51203e6602410440c109480004e041d0541d4599 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 763193246 1250 763191996 763192009
    0x70c0e0601030209040c0e042004032d06020c070b030603061918030c0c05040b012c0a09020319021620180f0c0702090406020d1d0c031b010806 63
    0x180003904142e000e002240f81d0303031242c1c0550101006075440b000c2c06202c51205000480d138498042c544404402c0380e02500f003035070300c0041b18166900300c91120994140100c01034060200c2288210b411000d540508003440807903805850280d8004081e2400f4681d80d004c8845507000981d036442d41a000722001c034024900c6aa0020041c1d0181000400c4841c0c0f02020520311500d072420960110309401b0310307001002401c0100c0000307418211020040320710450002003055800084030100001600c084022030b0b1194982c1842c4154000d040c0940c2da5100d0381004065002622030390501c0e08024540000c1810300c2c02500c480c0300100024a030300340115281c064074040a4141440d00c210765444541d81e940354040010001e42042c21210840d04150412500c0001c0041c41d01980000500c5094010ba8410b14490740180c0c1005c00907031999800308400000700303400840d40070b503c40c2c8040c0c0d0704542c1c0c0c40840c610008d01030460544900c01e44d0300e45110b843c400d130a0300c0c0c1e42c002145440041d1440c035020 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 763194496 1250 763193246 763193251
    0x1204020310020c160e010305060c0a030612150c02011e021308010c0207031406010308040603240608091002030606030f0c0706020c06011a070c0b210115080c070c0e 72
    0xa0841c1c10160149251104076805039180c000c0c41d40110070080c1d2601da1410b104001000d003a02592101c4d0714545626454640281004005540c00500901c403030780300b604114090521501c1d420412810352038038039415040e00c81c40000480c100395001f0203650040c4900510341d1004072500c044803c000c06a040250301c01d41038001d0030384409401003020442481510303030400c1503800070021182182030080051072400b0324066154040c5c0014000541075000b0b07a03084407182d04021541182c0e020043c030004201d480c0785640e044584100040382c541c800440c5014001910039030b02012040b5005805030b2104a0340c03941c00480410104e0a0f1900322688503502680c17110550342414000d0752254141d9201e070300e816a07580d02c81e0340140285d45444640302c41018400c010145400543d0b07039901140780c01c40c814610240f801081c1b8000c0b9035400400b0101040c02079009000541e1107298405070081881d05140003d000400051041591070089415858011815400030361504102c1540040f00 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 763195746 1250 763194496 763194499
    0x30310060e010543080a030506011103160308060109030f0f082503021905060424091b0506090a0e0a061517060405071d04021b06090d0302070305120402 67
    0x300000c01c0002e141a5442c2c4030100284501403004050040a418000300f500006004000b21344400000980c117000b22106201c1c00e0601250343c3d5241c1c1d0050300c0303e1001000d8100b490000140b41e900f02020040d9050444c0e100386c9035148a41c03600801114446030324000240441c00f030003915000708290100d0b03142c41a1080c80c50500d42001c0702d9061850140e2040b3700417956014220400805405012043d20034400044106030100c594880ca41e40b08000307070004d800b40740d00c1040c2000c6503131081c00d60600c142c00c1e841e003480211103d1411100c06100004034202100540401107030314581241100c507003e0004240c9040c0714104a04040c81d4440036014007009580d5000004607030130b8807000800d40c40303650740310300b000050411956844140018201407040d4500004c110086030001500e41980c1c03103141a4201d19204075000c00d00910031054040345901d4515024014044002840d40c42000401e0595080030700520040d0180d026030080100450030a011000e025081c8040d420381c001d00 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 763196996 1250 763195746 763195757
    0x801091518061502150601080f01120c03170a0201180224070203011b080711071703090a03050a03091703031801092f031b040509100513030908030310060e01 69
    0x9561000e000c00321040c1e40d41001507081610b400784a01030414101d50700046c01e0030011154a0440761400e0032171414000c032410500c10904500a1100c0c0c526814041e41d800103c11541074410004a5041d07001480400015800c04800000c140444101c400000341c0c060821800c8034036500082d4a6441c00d01c1303003080e0950040c0440703030250b6000d0141850b205400000e110705036101e41002840c021008048400b031104c60702c403004006100250b144200c52411200c141d0240700d00703030003d00f144200c0300c000360701680807040401401404604070721020b1083e1a8404495554150710120768035144c0074103020742080c800170b03890020b0040c4580d007e0020200025407012507503901c28a0058580c404801d042c44500c4040c8002400e40482c44603240840040204805000840008054824a01c1e000f0380e200c001107444e902c003c00a01c804030041c11020711480c50580000300000b07240c03841c00c0d07001441400000400460110890f0700540c00c0c074010305642800e02c141692070701c1010416904100 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 763198246 1250 763196996 763196999
    0x302030c0f0d150603060b120a0303050907170304050315090a02100e031c02060a1a100905031009151413290103050c04020c0d1b1a07080109151806 65
    0x10b40c40c0c5481c184083c03c41c000010041d0a40c103214007111a0581114041c0e8003280024054404c0001d4540b02c1943c50b240126003031766140c1c603a0f400c0922540c410544407801102082d29601e011001c0c1060724000da04440d00d40644645001039203034141d030840115003165440700054142024180c05403180c0b810580008031414001c07a1510415152502c440018481c56242079503050100740d4102084210902c1014900e0869181c003501d0901800d1007030b204400c00049040c020031010004042c0181540c0c0580600c00c0560302500c1100300490f80075591050f401c081000520a007000c10201d12080442d80d52000348a040a0005000544058001c107000103040c07480a10303112402c2c0300010b4400300c20b515601d499494211850f08452040d4018860042100c00c00104c86044035020303e8050307440802045017174006084050701500d500703a480455a0042c403021061b601500c2c25640d100144e0b0f0f83c40aa5400b100d003005112411141c0340c0d001045007030b4004100709101c40b040038000450b103 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 763199496 1250 763198246 763198253
    0x314190809180a0905010b0a060f05031915080c0904080703270807081c0f0c2414060a060e010e0301060f1203020d020d080c0a2601140a0302030c0f0d 66
    0x100c50494440000303588800b130311010010b080c0904802c0b041c054a800d1201d85c04c006001e8001d185510390041000008400143c40454542c140c4d110364402d81010400c000f1030700d210004c41881400703000c11521601c8030740da8071800c0c0012401d1045810401b07140c03c0c1003103564202e0721003102d42c10400311441b0800c03617410351450641c4008020080701004000852a01c0407950801c1e0001806443d100303240c00503180c1e81d540010305020b141c4210b00c0d08403641c004601d40221041c201c68000e802100c01d41e07184032111001544204620301c0c2d9a400100503030340d403908000d2041c8060284e85c00082101c4e00d06030607940104101c0052580080010801c00c0c1c1300c11206400304c406500c8421220076243d08502415010300454500403000d201914024503441c001405152014010410b180400105004013500c00e01c40908102c180b44200c0752001049403000c00399040c00e00038031405805101d9000100d00c2d006803150100c2c1e501034060704034a071a0358200048010031100c015000004422a03030b000 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 763200746 1250 763199496 763199539
    0x10b1605030d1e0c14030a390e060c07052b0b0105010f0923040f020c010f0b220f0605090a0f0b0d1a2503060314190809 53
    0x101000e5600c1407546480c3c0505a1054840e07421603101445801078a00c405854400c0c2101e0f8401040c41000c59400303142c00c4489500d900c0c0d0059032400d842c142d8111040142c4696408545001c20340d50348192011a0040000c203200f118402c6d4000da0180f43c08000e1810010070850951050b10300303240012100d2505034403a0811a2812a2412001c10051042c0e613046920b40304121403502d09005c039079040404521551f002d50781000341400440300d41031000c0e942d580000300810341e049070554940526299450103482c0300ea800b00020750900c007400d2814141200040001c85501e034158a080d200d003802400240404414002201d88400d40840c59807240c0b00801e005441c4100006050540f00200740111903041103c41d00c91b0024500c03072008203904210340c204003202002c1018130b51f1250580300700000c8a515540d141c180c40c2e0201c81c002683c01d40e001ca01200d0244230420500b2841812141d2107621481c1d600014014000842c00424951340c09032005010142400e16078542d0900300ca00c2 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 763201996 1250 763200746 763200761
    0x50d0b0109090213030b011a1b010b132f220506040303260705030c0c01060f081e0102090105040b0d090b040f02030d02150a0f0b0a260303010b1605030d 67
    0x500860b11308100100000100403500402c40200401e05000340030102c00305600c209a43e049140c1c8808292410303100007075010300941c100c003d001081b880c6078036110002030a50581c1c9140440c02c100c4154030030030b8242e241c201400d0002c6490307030300e03040018100c1e041c400d042d1410b14a0a03280700300f020031076846400051011b14040d40725051001e031900c4030500d5103c1042c8120311910003c900307100c402500701d010350350012050200c0c42c0c0c40d20f09211100780180002e07401007400284003507000800240105105041c01082020f098400d07150303004641c00e0b48685060940050070800040201810400250110b6144d0f41c0010513a0b0800e40c4544100ca00305480c181c402e0300042507403100310325007004101082c23881800070381070748480b00c00040d402100040020348034030348403c40040d080c001c65000c100740c4440101001c4e00c10340c440d040e2102e844044a041c0b040031105028482200c8400001da0741202c82c205115450000e070b010200369540050a001c407407a100c01c0c014801049014042e400 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 763203246 1250 763201996 763202017
    0x6010318080703180b13051e0a0603020417030c072c09030d0f0506090403030e0102040807030f0b010f0e011a09030d0e030d0309030c06090f0b10060806010e01050d0b01090902 77
    0x51071030142c8020711101385541e0303003e403000c03900c2000083c0c009510714000c642100d0341100c0308207200300a4140d41c4076000340743d001590700507646140800c0c3d40e40c040c0e0150098580070101011080404181d440d130300d200b400c9404940354800c1004019184502c0d40100703600b100141c0320300449440d28000da120640a4a65005c60b40012480807002d01c5240305401c009000090148164102540400c22114000c1c00180405480307800c600c441031400d4040b0740c01080d42000329001c1d02d40d2401e01d4031004068401c21500f264450000180314410003078800150b030003000d0780004603481d01e5029407800030142100007000c0001e1010311010344d070510803059074440c84d071285d1546802202c03c05043c6426402d0401c28035103803440d10360200780e00c411705403c0c03941c0c003510010310075007282094175000c0321821000f07280a0a91040100b107800008691003141e00703588403d4600d0311000010344140146c105414000f42c030a100941c0440d4494101e20311040040c1811000103440e002c1c140c050781d01111015 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 763204496 1250 763203246 763203257
    0x507080a0c031e050d0f0e0709060e01050901050307090905010b0901080a060c03180f050a02150c0106050103090b190b0909030417010b18092505091b0306010318080703 74
    0x40709050300b101c0249411040070707918510241200901030401c0c0503402e012400c1a80d5804c8041c0202c4242d403010440d030000900b10703404655641000c0c00580110301519058054280c000030b85400c00d0495503050f207074018042c11216080c11170140061208402c252500c0d0340711a604205901e4805c0d00034007174443c00010f405100c2803400c040090b106801140010989003070b1390800c002021442c1c2d580303040c1c0e00044030303c0c200f0000e091261400003103010183d0301945150786d00d00c0c020328440084c0401e12403031009020303803a5514010340481e0300d015006011b1075011030004070100c4000c1048041141d200c540003031400b03100c030041961446c0407103085580d58400141481400142c1590500903840da100038020104c1820104443c10401081006424150800b00e00c607008c003031115000103580c041c000c00389000c915200045038203003445000c1c095408540850004001c05030008000458180058590b03200c180044008105031480d0241c4d25400c582c2440002c0c0c00d00c801804180d0180d44d58 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 763205746 1250 763204496 763204517
    0x409050f0106020c1f200f0c0a0f05031b030307060618060f08100c020f06071e05070b010e18010f0212061206011e09021c06120b06100507080a 63
    0x2030b1900011032804c070b1142c40c0c00c8164010300d2410b0a0705410905403481d184203000c0d01c2c0041d0411020750000c02d183c0c00d0088060340c1da8070340b078000f40d002c142440445400060640e5080c2d80507030700e0714502426805400820f040c5035059040400110600e101404503460680e1790740b1005d04440e42074005103295050340481188040c41405000d0181410040403d80c103032501c0050351b070310402d581c440001981c4450f0906001d60080c0f002c90051030110b41510658071700034500424641c00c1d805104100c2a20b0494404210700c60026500e03407680c4000f4401c826420030012501c8014028251481504258120502203600303000d100301503201c0b03a40160f118110302c401000c0307001004103101d009041c42c40b10001722803400a60107044821000f4020800c14410040c05035580e600e80040455500000e040f040031040303101141c00e0700c05220800c00c00681c0360102680030b103500c400d010308800720580100e0041d1500c007042d180d4440180c10a41e00d440066074a440442c0c200e602031002007001401d4 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 763206996 1250 763205746 763205759
    0x30a2c0615060a05090d020a26070f060e150f0a0e0f010e030a08070318150305090d0903150f0908070c08160303032c0304090f0213030f080409050f01 66
    0x129806a07041102d0b001d0070001207020003007090180078481841a0308500b8000e0564440c00d16000c003501150f680c50034400c0540c14000c0d18070345580340301009440f614000150522011404000303aa40550368800030101010800c110f080c2441b0745050030205c10403065080a041c800100000f01c0680c55071407840c0c078800100b00410103420403290601400c00040516664041030480d2019031209400e42c9448560404403802d4401411003444100b0990303011601d407041652803d07d00052f540c0a11041e980c0ca054280c840300b00415110100f00350743c0f01440010703101c400c020007490210030009802e0b5150311410090f01d442800640380180f00007a18428401e1403160103028040c40c00051640091886004c407845130349120242c10590380d124941081c0320201c0480c0c07420303252400e030301c82c5690103075440035101c0c0d02c5440745543d001d2a0190f40c00d20903406000341c0d5452030181544060651840d00c803001074004c1c189044034101810000800c0c1800075100e2035020f5640c01c442600158140349 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 763208246 1250 763206996 763207021
    0xa060f1814010e061c02030303070e0306090c060316050d090606060801230d020102101d15011d071e02010b100305090604020f130207060903021c05030a2c06 69
    0x109007140c4140d040c40180501144903040d01e0f04400309442000000c140d0303075903003c2da00b004500b009615020020500801c241d102d200e4005501c4200d081d2901c90f25426221a9100c152100590b04804c0900000f40051801e251410031f0108074209149005001d21004045a04a2208541041d138961050200547c08103225014100d41c00300b031080020107049001409600c00700c11480b8004043d02c403003c5900c24803103012400e00d10f50051101c0c024075001800d00c03554003da240070a04c00da09407001104041400c880c1201c001801c400305e003180314020340a00600003080e600c180800d40055440c03e50309051160b111005a0f40001001c0c5030f0b000420244c000b030307039049a08040c1031805028003801d021a03103e030490b504403050002c83e104100030689000725941005007551010510000f400301581269940728403a034242c42040034489018036205031100c4581300040d406100113180e03003000364070000c5000107901284489140018020032289990721900c44950050407e1103000074001 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 763209496 1250 763208246 763208261
    0x1e030a121e0516060f0f06080111070314090a030c030f05070f15081f0e2a040603090f0609061401080316022707080f0603061b030a060f18 61
    0x850780c09440021940010928081c00d07002c0e9a100e1001451041000004e620810500d40c0c030740300900c074206555a00a0081010b4800c200c0c1039400c2c00c6584c845a0034140840310102e50644400c00c442444920000c402d0f000b01038581c2c0c03c07500310381020001c100040d0086004500c140000d5032103040358548103041107001d40c01412042d807424424003803601244e8181c15460940d2802040c43c0d90341d0381d4502004c00c2c0e407a5030540c24285410001c980c010311840c1e4948641e880f41c0305d100080c02011b0f0b08480342540703400b0750011a54180010b1002071312035081070482500609101c202c90b5265294401114400c0b001150407039520031060400c000e402e00001e00400130440035508203201d003241040c40341510309000f0b11640200d40c20509043c101c00c2c410924001164000e161031a00b4174020f00340d81401c0e584c0d43c049400450010b1103615001900c6440b44002c014104d40c44d62124041d54090f0f00080e201c41c0241752078500c0810455895602e0000030207040300d06040c014408140042142d544 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 763210746 1250 763209496 763209527
    0x80a0f0f0507080304032a020108060d0201170403140d0203090607090510050d0e0d0305070212070c0b0307020a061401051804111002070b04030501060e0f0405060103021e030a12 78
    0x5102214201074015064400c407a8115014956999880c0703402c80760640c00080046902e8a081302c42142000c60007681c6020300e00c00e032030310501e644071a01000318080c803da00c001e00241c00d6081c400b03024980341035510381240c070030b0070408500e4801d1903100055820070080301e00895404410010301103400c01c00390b6007106150414082c040e0411000c51171000e075080003141404000229079503401400d03400101304c0d10045090303840392035000314018007522007a03030690010b2042e10039200030010341908464840740d0001a400c001c91500c205c000c00c07078000074070b20390541c05400b0441012690074011184001c550100c102c61941c101401c0020080c61540d10600e400c0000081000050000d00c09440901080b0b0300c004044c192000224908851600840c0c55058086000820040150040f8055502005400c500d0ba81c034500907000000c4126805003007540840300400250a150000345000000b2030313000842d2200b2000800d10300000d9002c2201c0d80d0040c0301c010543c1ca80d11840c0718020042 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 763211996 1250 763210746 763210757
    0xe030f06190b0d150218180714040b0405010f09050414090f0d05180628032003060112020c07080703120801060c030e010201200a020d0908070605160b04080a0f 70
    0x1054a80c021420b854000d844440740c0d001a000f070119240c03100d40d880d07041b0010302d0368401d900c0c0402401c03032070f0344103482c40e0f0702140c000c10000c0f8250712854280c0d410703103000701c40c09400c0c145840011640603211180c0780c420f1099611000c00d103a140c2e4021900a0150200e8403526824007040581c07401d0304074200c1800c6900000c0b2600d80030b9900c101107a120071400e085030401c00c900303500003d020b481030b80c800144000840802081c1c105908040421010045d2000c10031600002923001c1e0408602100e00701810041001400941c015a40c8404c1e03420840001401d050f030a0b0401403505841d0b4001080c3d5a0103c1410802c02002120210404842e45041e516035458150041c00d19480d150004081c002406100b078680d074030035444108156950300c094480b03103041319500140c640c403e6007254014003907800c0703100c6a10700440ea0441210702800090114902d81842102d640c2c01c0300f083c0103c0d038940a03002d00c0c0859600d009a60090340130f0754240e0303551851001c01502d080c2c5480c00e80f005009 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 763213246 1250 763211996 763212019
    0x4030f1d1203220f1202060c0a050615010c0312020c12040801060e06040209030601180227031006030804050d02010c05010e0303011d0601081605120709260d0e030f06190b 75
    0x620f44d281c030854240620550310003440d0710016000d400f030a084c4298610450714500705104001a0302c07030081020010382a40404401c0044441d01448440540814002464040600e6032640200001d650343c409899244c00d44404004880c1c1c00fa91200c10548c1d100e41090255074425100103070484d034212421440c000320b00d40480d498003014442c400b512015a4031031403202c251034040700c4407102c000c611075031f103c1d05410f401024a881c440d4060300138490b402c040c00c06054144140f8007a41c0d000200c60707040c00c1c58a0208a00d800c0500412410030030030410080004100b4014244400f034010061900c9604001002603141c1001e20151640e01e601c4003032220590b0480c0d0a990001c03140185100410144c003001d484511034582c088103502000c404008559600036040000d0750071400c404041c00840710708600e1200076072480c1c0320b02900729204c01c0c80140c0c000e28559040341c03070142c01d131442400e5003284d580c01e00004481d44030f4002418003074040d5a03c0c0b5445031048004040b0b4242d98400d = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 763214496 1250 763213246 763213259
    0x90b040b0d0609051603060218040c17070512040c080606030d09360c080a15122603090d0807020604170c010e0c130504030f1d120322 59
    0x114074114050606980d8107000300a1000605c070380c001800c030354030300301c0811641c2e451b081000798003c2441c01c0003030351002d103841458505409a4008001d06a0f203c080804602c03080c02107001c0d0142501062103020008403005901c0c20503268415030062a24802c21072603d20110f0a204004040074825000200340d624110b030031590035000e03144940485c00109000403810040b071070044400d0000041d00313000c41c0941400940180b036040798280d0351800182c40d402c0240042d581070841c1c05128041c1103a06020180d68000303800701540c02503020188807950010310b251001784120003007003000300010070800008000c100c11180d210329480e2a01c69894102c40080d00d52a0140c402007442d10807000304511411607005480034050024020003070030120304001651004403242d068000c06407803502c0320800081e0301c501842250191540e06559000010072140e0f00450103114103248504400c500725522580ca01e21000100d41c0d00450761900f99040e079252405110700310f07031725035401c1c00402e1114 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 763215746 1250 763214496 763214509
    0xc0e07080412120b150316050309100f1b081503060c040b0705070b19090f061e050c060c09011701080c040c090e0f100603060506030402012a0c090b040b 67
    0x7141c02c0391030030b0420b01e031030110010050101d0403034465100d031482c4103030220a0440c0e8000c40c02040c1c00404401c079400308500545440c002116039400d103401445241056140d2900406115281c10400003055004100650394001c2080c1c2c0c40c9001032074003020040c0a03548088070752404282240100103e2408012014040c8203030300132180e44020200f903542c20400700b003021801910124802c10303201c0c0c9903416210391101c1c800d94604005801c01000080c034071003884480c0c096807010358074401c90f0070955100710910a48010f22404101d010031895101c00024001c2c54024110012040d6413494240001080803122081d851080361010004205a05002450b4140c410003079401240340f91000c0e000703540c1040300b5801807038145400d404000000034038141a07031080c0c19514102c244145c84400441c100e8000f8058550482d00800c0840d01560180009103000a002c1c5464201e20381c51b0460142c0d400711164040303c207808426810304c0aa0307858040c006045005503000c1120140c0f02002550 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 763216996 1250 763215746 763215773
    0x608030a11031204112e09050402041d060d120c0b07020c01021b031f05010314150c1303050a0b0403020d0309050a06050a020928060e0117220c0e070804 67
    0x90b032603a15044603425111010b0164040d00881d60b001d030156070f01403041c04104007095003140040c0c010031f00440c80c0d00d4140300303541c2940d0560040c818000f03995045200010409080643c0c00340c41e603100c100000780c002242d8214461696205032296a00b40f80c44440c41e80701922031015500800704541180c1d034000b503250151a83c8840710b20760a8a08c0011900345540c51204c0030f20a0f500d841c44064060803070300124120780c89109140c10315012218070301d894007220380400c1d119003003800104805103115005040c3d11640c1105103480d0907669640c4501d042d80008003116884040d00402c001e1580600000316003e0490905000c41c64040d070754a074844402c0c00004101596410101da03000c881036050380c21100000d84402c0056003000a0f14252804003030b48101c1a0000d01c2c0e0120f0618400c0205105056040c0c6a42c8106210580c0003d864200140190031940154038012a0f016140d070054009034000c0030398000740c80c1418040264082c004081d50140b0900c102400000dd450300488003 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 763218246 1250 763216996 763217003
    0x310905010e0421030e01090b011a0403080f0705070510021b030f1f02040e0f01181406010e041e020c15011a0703091a190905101209060608030a11031204 67
    0x800c0440303048054004020105100490790b10f1f05000e24100080006081e05890f0704950080248013910740341c5206200d80d00005000580078002100036042c564042c041c0140302d04103840700e4a4664000c0703110794800c00400030040c0c1c80440700083c03130385882c0b4000303500071025001740a00c1c0700a060360a82d1425145002500990809080056070b8150340c1605c0261544042c4040e4a040107420b4024900d030070300031036150b140d03441e00c401c003107181901c1001030070140d074412103859544070310041d515080703c3c1402039041038031445102d03021118074800080c4111100001038643d4601c05229190600c0c202603501c2400c01070005000c0c143d05a0704407510200c00000840c0d403600342d842c045030f00f003605e58000740304200c00c0c0b80d41548143c0716070701900908004103e0050407540c3c01504894818042c4501c540052160b10140f018034807801c90440400700d20074012504044641d108001c850325030b4000c00803504040340e0743c501c036075100d00514954a088402542000c40d9280c002c0f00c690720241008 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 763219496 1250 763218246 763218293
    0x6060e071e120902060705010c0f081005060d09051002030a11040e0606090a0f0e04291603110c150c07080d053c010506130b310905010e04 61
    0x2a0812030043c0c0080c01c946038041c240a444800c0342c60018060504108000040740c0d407000d501c0c1000d446295210300c51404074124021451400040c45400d5012489d01c4445a4440603d000481d4082012101e00c080c0c1440c0182d0b02e14104080d081243c0c510801041091000c010410011803800c1040f6044081140c0c82075035080240c0c00101c40d400213600c80d03800c60b80001070003e0f100340800b003101e00c2140200410502c2c00080b804c0b40740c1c1d50003d41d0302d088003807000002259451440480a01c19180181400140800c000701240f40c150000754000d01207070b00811282c0c81d51102208215040034040d01030300d0503c00f51341d1341d41015001e0035801d04200c40d0340e480010803982441d42501da03018036858001151717610102d9168441942d000c0520003500c0400000105814023004550000a0001c0d4403c241c905018440c0c03120b6000455400103800410700030134081281422001e0100000c808002d00589012122401c0c0e5205a1128920030002030410001c203480710f0000e4000301144210 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 763220746 1250 763219496 763219517
    0x10150905091e040c1d04080a0807030b030f1c18031407180209030c0303090f0402091512090d14090f031006090603110d052a060706060e071e 62
    0x14282c5410964107101040c010240500060184400c0c0c540705950300140030504500403140d0a00100b201a10000c140f10010010303020b00718421340285801040358a400310f1a07400a100092a00210b0b035141140c0350015403450306c0c0d0f04142c586140c640c010700d040c4108200c4000e40320301c0080c81d0510000c3c01814130380220b403144950500002c805061035140c407440019800e0702a00082d0818010b4074082e101740440c4111500e000025200c4a21004000e0759015481605110182d040221581d4000b091707402c005040c85c95000c0a803d00c25001c40044009141c204080c6181004003201d14081c00518428001003094040803503014070030036180c080f104281000070a03d022591b005400d1900e18001f40410005010b801c41c2c1c0c101d07405103c00d81d007103189000070003c5210101c20010a80d901c020041c0c00004051201e5045036014802215900b0b05100301150082d4458901104c0282d40c558050040d20366042c1820780081c03241c540102d4950021900604070085102008103020b4044071 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 763221996 1250 763220746 763220761
    0xf10140714030d020a0315050306010612020c0a080304020a0e0c030a09140607030e0714060304060e0a1406010603063c050d0f0201022806090314121015090509 70
    0x30300550001d800045968403610507a0a20081d00401100000281081f190181c13500840711801d0940314000e0283c252640781c95026038034040710220084699409102e040e40e246c0080c0601c034035281c064080a0b940e40381501c10400c40030070301d80081300e1041c1403c003400b074062080070681f6880301d2250b10010751025203041000b01004030a81450325031050380100400c1d142c0c50b42240d0006240401114625500c03400001c1107080700303d40540c0c00a0060001501048698204010b04010b220598a40b105240c86004c0c102d0004281500d0a600c0100100810380c0d151141400415143c070000d0502e40041240e4619014504400502d414200e00001248043d80340640c0040600804042d95240c8500d0310442e0700d41805400d90150040e40d01040c0c50300380d02074041130200082084c10684011698070040140002c05003602000024074401c1c900504000040070901108000807065260640881082c000a504415a05100c44c005900c0291308101d000b01500e0301214a03040aa68100d0b = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 763223246 1250 763221996 763222013
    0x20108060d150504150c121b0e0f060f0403080910050a050307080403110d0c0c060c02030a0803100902030103150c110c091923060d031b03030f0f02090f101407 70
    0x1a00c100302601c4c0c228155080740d00182c425602d5a031f003d8051180c06158550040c40d414241251804a0710180841209180801803119000e800800349803c20710400700c0015141c005401c00c640c04000020320074030503d4001034a5002890b81d20340305162540c9560000d00310300000d0703c007405020006000c141018014040d490510b44d4007011035074444201c140c020034140c008501a17039070108410000c0340709841408036120883c0c01400901c1041c1c07190b9140a030582c00182088151200d5032804070790341e0a1400194001c5000c0c070a814228903082003848111480c07510f001041c0a00c040c0300007a075080c082607a00200c4021281f502d402d80d02c400d0b04a004080301400c1c200c11501d090000b442c0000c0703036030032140101e102c2082070085070b03901401d200001c14179100c081c0106a90444c0e400d035805400c9210310f1200c3c40303890081002e0840c1e203401016244610010402c50350080307160b200a04142071031620101040322040b16003140076101400401c05460211407000d000610682400000c4 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 763224496 1250 763223246 763223273
    0x90501031e23010b0f0904020315220606080c030604020901050609040902060a09060f26092407020c15030105060f071506210c0b0a0309140109020108060d150504 71
    0x1800c8045500800c2c40d000e00a0040810091082c00d0707603200a601400c0120b0414895540980100f085003010301c0d180c2c009090040c0800485850403244880c50100b001d07411000f640b007041302142d81414011910704014010b06114000c2c0d21180c10480941e40b42651241100c1040d600b45a4458295021a010702460400a5004040002d0000340c0c00d910840c0c410890b40e942e80c03404110840108110b42d10056608491403070786884840c1c8000e03100a07000c05070045030000032207140da002402040941070f50365451000c420111420403442c2c503010b00c24060400740455402d08034201d40c50128015000c1070180c103006400c040717880900e102e0764008841445811048803001c03180030040d124050070290050702c04c4642500c03160b0550f08000002c202805030f1120701020b2660034001d080179650070410b00641056142c120201c085040c0b84080000e0f400c1e818008640500c542c0005803800c03a000e03220030701030480740341400045803804600d0040320b581c03210301150f20b44550a2400602504c03 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 763225746 1250 763224496 763224533
    0x50f0714250c03020405063a150509010507020c28030807110a1205150403021617010506010e0105041404110a1112131a0408010c05040807090501031e 66
    0x1c0e404030410702c050207182c0011280f00311001d010550703c1d18203014910320034410801e000c00e1200703000000506442006220702080c05081c040c0f090240d1036a001c900c1c0f11040c000807035991082800360b07200302801a03070f90200d400e0008000855200005c1942c40c01104048504000f2441201c0c1e56003443d200004010364100c01e58684401d402d00348544e0030b03003100c25031a11031006142e0006905890122404005800c800504000c0703803a024141115000100308500714002c50304130803c0d07488020190130203049120b01a5080e00f1180308181e08581000c0c0049040c80140005140980c0c0d00c0000c40381a0740d29501300034821400200441d0241190043ca144500030108005102c2c1e54062910b85403050703548110759420058003154581071062480001e04c81c1c2d0600014407040c281703500c90310b00788a0407001d00c900d00342d070b80d5050038211020703a03841c02c001450024041082000410215000d40b071140c004100c0e5515540d034020407007280e043c581d00480d50710403101c0c042c0005400c0c4031000c0b522 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 763226996 1250 763225746 763225807
    0x1c051b070902070507060207050117060f01020705030321010509010b0a050a0908011a030d09030c26070306150603051014040f11031009020705102403050c04050f0714 73
    0x3d852624940302d242a028000051180c52000a555032282c02d00842c0d03a05135040c02500341c0c6501060210066090f9007840c1948a90303040041c480d281000180300c101c05104994113015410b400b1003080240c10381c800c0d0f00c00c0c00b09500500012001c2d01c01c5900c184100d04200d59207441541c0d060724000c09591204d1403a501e01824515040074500810003445811020b482113018150000d80e43c56845001c06403850440d2802808140b42e01040d05a1032813081180350883c05100e01c0305171400c031780c0380c008a803a00d85400220101c22404e01022000c3c009605091086181000f0f8140311083e0f24800c00c0131030320300001300340031a445580c042d9480b2010660b003400142d130081008038096006451420110784064000900c004451003507501c0b450b0300c400034021031400c01d07c8440103400b0803602090b03940340404000c0b2018003c0301c8a48000d52242c1c0c05003000c50034010400089a000511003503602d4102c0040014466014803028924007121250303d80f501d001c06034001e0f0001880454106a25 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 763228246 1250 763226996 763227007
    0x15010b030406050f15010320130905010824040f060f06080709020721030608031611120a02150409060806010305010b0d030c06090f0b0c0c1c051b070902 67
    0x9460003148254000c8074180030540340c0102c907425842c0c0803107107003071400a20703020448158403a4101d805c3c510701c442c0340b00b64503d1103e2100740d0340e507010007003420a413440700600300705481c824000c1600415512018040b0401c1c0707203d01c4e405800e07000003840a01050000098200b050040c04a10101c0d089481004050038a01d00c00c00100782c00e001c1c400c110f1140d054001042c40c42e50007281c00c100d0340500700c02102903008005415010703c2d201c42c0c205060705c8070ba010070b11000420152881034203031000110605054100050010308001c4000e000c0c0002a40303120304000700080100381194181c0c0c000c8503600c0442c15207044c9024903085404c0c000c2c140000099111000206107050341e000300001c02000011340c00f000706400450310000d0200315038012078008030b00f880e8042400e00340a160301450751110759490b4000301000312200f180d001d001260740707404408108014103214a00ba041045079202c80c0002428901a1910011500a19850104400b2000d2140200074201d0400541d12074 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 763229496 1250 763228246 763228259
    0xc1502070326040317090d080604020d1b0f0903110607020f0405160801053705130911040603080405040906140114030f01290111100615020102030603030f03091501 72
    0x45409882c01d8000a90500a030005d541c2100185030140b00000000c20740b0818100d404d49940c50000c0c640c3d40e000da400c1c03001d0f00b074100c100c2c0582d03100d4550724082c1c20807020384070303c024021201c1f5a003031904103c5040c1c014000950b044c4410b401000044900a4403450584006451520b80e54240d0b03421506050034803080740700004082c00d103065581c4580015a88a00030f00000072260003046002c02d03015100c000c00a0700181c0440c480342503d0200440c0d05480e0404940d09542c040400c90304903036160214803e1048036425260302c000d0480301808110b1a507200c0808030700031070140c1481b880e40c9600e00b508020850348115003441c00b049485400d980d403001c81d01c6a81001c607908a02a028076402214446010301c548924010b0440c00c903440708540a00080000211048003070520030880034419603110301300443c81c003001103520081685801c04184840074050032180308190ba00610a02180b81e901005544a81081074103e9440c1d43c0c640708441e20300011001040030b4102800004140c0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 763230746 1250 763229496 763229567
    0x1020a0f0227071b0f02010305060d080f1206030a02090408090607051f0b01050c0a120c2a1e1205190302010b0406151e1e02070302030d0c15020703 65
    0x101820384809034520b14103c1030b54804c0540c12401014014400d20174801907001c0e40c800c2d03800140150004401014990b9131001311b50280344d042401c9a00860030383c50801c0c902d0f002c10740c0590250b000d000010300950125440b0361011f04001c094207404102c0c00301545036501555842a017140880c0c4d42e0004403120343c0e241c0c18103d00801071460a00300761a40c1c40d40a041115450b145040081502400c00d49600360118818400c1c1030402c146002c4c850007042c1500300e0b03000d403183c114030420032a1044103c008404840c650000701c4504000604904688a19032030a0450b1941840e0103202000d43c40c1081c20590201e0784400c01650342a0300b541030548c1540501041d070003e90301040240c0d154144000700c0d8124609480c00582e8102040719000c11605da848111800350608024103c0d29002c0c0e20101030580d050075005a004140c10070541ca0100401009000e484c10a10b1003a4400d4032660500c3d14411200329049800290b0402014030501c090540800e0042d0007642d103001e40040d2962 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 763231996 1250 763230746 763230751
    0x90403030506041e050a14130f150204030b0906060907020714120304030506010f0e151216080c090a0626070f09020403060c0f021b032812030b01020a0f0227 69
    0x81ca6103040f0541e82030040e0349117414060810010308c0c032004071040d583d01c2450031581204540030841610056130020710350002d40080c40c41102c842d209442c03d10086490000003c2c0300910032103100090001c6e013500480c07550162004141da840d0a140b807180132901d9002c4181c0356000c07501c0005000000d00c01c004c292541640d1381d24081c0f10b400d80d030325501d200841e2010b80e8500d1184245c0158000705140660501d500c1e8000c40c07059420303140d1840b06600e03491711154444d92003a00f000184001e1880d000700302c0c543c8000d08242c10445ea41c01c054200c0310707002c020b000030f08900382041c41d06500510100312882c001d00c01c180603482610345440000c4085d401902c0100c0742ca074105144001194000d00d001111010640d00418450041410a40c0301c80d03420803c454241c020042e06001d000b85074600e4550455200c0c001c0c00d81c40b1014036010803043d90804420701050b1505801d841183e80c0441c0e410b0081e0b420034042001384445000054561905000e50161101003102a00c9004886000b00380b = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 763233246 1250 763231996 763232011
    0x1515121213060509010f03091a01081e150606210108030a140702030c191a12060108090307020d110d0c0302100e0d0206030a0902271005090403030506041e05 69
    0x1000d682d07503100161000c1c06812400c80c00f00b140700f00b107045201e2080c2c4c400c1000c40d01070b0420800350744038120001440d880c2a003001c401d5800c406100c0044001c548500903994588000a01c546240b445c01e980709031001030001880343d0341c001500321584003c48004507100c5105800303100036580d601c50303917035a9600031004800402c0c09110750030300d02e0700e03502c0c02c0d50403058010700a824076905810810011a20500e5440ca17441039500700840c202140b1840b08000f421221641940d0b011083c03541d81d501c6c0001000641007200381c00400c000c03a400401591485070741510400311080052a040c040311010354011604034400150f83c0091024400d5041d044070300a6518101140c22140c049440110446040da04550607d03220b40040c1464802164040a5024002204035075540003500c00c1d800e610101220120100a0140c3c400a4140c1d003600494010040c0081c0391520002c103614803002840a4181a07a40000803059100c5030005030028911a0040028000c03482c1c441c00100001d69410 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 763234496 1250 763233246 763233277
    0xc120903050c01140d09020616030201020d0f061805060303040e0c0306010f320403050307150b0405070f030e071a040e01080307050a0f03180b03160215151212 70
    0xb841c040d4081d10440c0c208009003582d9070b24100e2901402d001030300030f0640490300440200048041c84041075044030380c16103e507001580d07500007400540140c2d00032003500041c2501d02001045448810215207842c440c54641c0403641d587c40d03000284c1140180e50001c40e910358000100000480044001c51099000b40c03100c009114000108580800306849100403110540000c0a0074052029203158034143c0000e100740707026200d5482c181190000da40854903840301c014503442a45443c0100c00c4e041c80140c50800851501410003008400e59200c00010b240d5101e40245011809001c0c81016207144c0b001c2ca65101540301321800168080d104e8010442d40100004c00c2515000c0120b5000d90782200042444c03103010380780d040700401aa2000c4080c4a03228610011038400682400020160310810341d81720f2400b521000c214004038050350003103411600c222643d034207803084020b8220b104c1d2011a0302e040c2134240410800090110b510300d4a205100c005000f4400500007004481301c40d0501 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 763235746 1250 763234496 763234513
    0xa030c17011e031a04021809070306020309161412010b03211606090303060506070c09050603030706050c07030908150c130b0705010b090c120c0304030c12090305 71
    0x112003400300418005490031035a401000025140000100102c82003042c81884541c2e0303948524114400b4000c41c44000320790001c000640c50070011a00b10360403520034600c1540391080e04140c032006c0f54040106070550100105250303410400c561020660002807002c20139845070305050055803a00c600d0f0784a0052801e81c203203410f806008104640304090300400860600c08001807484081718400c04541c4012300460f030304144036540800c40c85000719400540c2580c241002015540c184e000a40134840420a801c001914640500c2c2140c88241000a040c0c94244c002800c5200d99074016040900300b5080c0194428520000e010b1a403194a4081020b581e400c0081c1d2039280c0c1c070004844d0740c4a47c2001403c044030f10700080c800220100683c5109680715001c0e650309401c080b10940f482c1e03540390300e1100b090904006068120008a1107542004020000201042d03001000325188444c0440400c0805020b028440c00c07075540070002803c40911044000c2203018107220a84091040c0d001 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 763236996 1250 763235746 763235771
    0x30e0d0c11180402090604090c0314070b0901020c011d061b010509060108030a1b0b091b0402180402070807170c0c0f0a050f0a05041a031b03061315050406020a03 71
    0x120b4030700c1c035003150b9200256a59000c01801802c018881500251a008080300090791803069002444c41452036150428204040c6440e1403100c1d0400452804204044251aa00042c00c020704620900c0d0400c1180c12140909a006020340002608138001150750707540050250824881849000b008120381c0d40d400050650303034002031040000540003040002c1c84140300d0300e0303c2d03050021007000d1850a440755a541c08003031402103840c000380c0c2c1c100c0c0c0e04003001c040d00855004413a03c412501136040201c0c0703560026040b44095a0b00e0721496000812104220080703042d1001c49800ca81110321019102c00c6508050f4081c0710301030440d0017980c00104041c0b0f400e072000b000c040c90140c000c4118034200420300a0070000000103a80c0150004000a516a41c0d4025a088400c840c0c854090f80b0219000b41481d15490351505031500f400c0018052081e100081c4850340410192040c00c001842405c040d403840c3c8cc0400352003907080c1010704210900c04a50010706d1007003510364040141181025 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 763238246 1250 763236996 763237009
    0xf050f030918070f1d0a0603090311010c050a030207050c10030b011e08011517180d020606030a1209080f0309090c130e0604020d06081c0c080316030e0d0c11 69
    0x11110400700745490350740a00c25215001c0c146600c4401117060414034072110020754000e007180c2c4424006a04d0314a10000c0503840594141d205000c28000d22120440740302c050098010415004101a408503504d002d0117400c214000001c013024060107501030540800401800c5060329182c04903207903841d49035610801d05072030504078085641c0c880d5180d003003070030360720182a07104d61070f00810000d441c886900300c040012180c000c000d24156202107003894528241000039034210300707055411007003c1221300d0300d001c144d101ca1507500ca411030072580015801510701c02c5030354008141a200d03140e602080503100100425100300e0840c1c0413002503403000c080c0c000314840c0150342c2c01810b5011808000a4600c80d07d01904000f004001508100d9168581e804690305980050966031181c001e40c5100100c1c8901d00881c03450703620f0f03e4010400350751a0100244000380150f0761808401c1140c20900d40b1a500c41407500c8585401c1c2c030f50700081d01100a25550302181d0944402c070142000c0e500c54900301 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 763239496 1250 763238246 763238251
    0x906210e061e1b0d020409051e060406050108040b090a0c03061a0621062409100e1018050d03050a0905060c0703020d080c01020714060c070f0206070f050f030918 71
    0x1900c880c844000900203601044c1c11200358919219028040460885407074051039105074480c500b032000c44034010b00c20280000010380f207140a01c2c0780c48814895641d006a0590b4850307041502034240d9156400003900e040d0a41501800c2d2a00b551004010000241c01c02d14090900b500304a1806a40d001000b50920400e00d0404d40c0044070100020071b01d910441301c41e44410000e1000c0418041d450322150214283d00040760944d500250f600c0c0c952404000990701400d440c5030002c0d400703107208003040d02c228290340ca5070184081d0715031104c03900c1c07410048040a02000f07056024800c0451030090030301e800251113031021400e00036012505041902c00d840555006000402c0658619000d000100045000079201044200001543d01701e090000b400e0481c4074054050050420700c00072030503c40050a40904182c0c00c00c6420042110115101d0409404071145035450344289042c030402c100b001d2005011380a00d03040417a04800100151100840981e80c2c51056854807410840b401001c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 763240746 1250 763239496 763239511
    0x1a070e240d0b032d0d1b0f061104060c050637090204021c200d15030215031f050310020d0f063818010224010f080a030906210e061e 58
    0x10004c3c0b50002c509060200d042c514023441002641807118010020f85501540141001c20203240d100c008000c41006000e5000841d2040200d03902d42189420940c880b01c510301400ea0350a00880d9200c402031648400ca402ea0f008000719541c040041d100d0303c00e00141c04008008a00d000c905080394803510342c1e003403c048001c0091358544401c500d100802000390b09202c40c11418001004001612251503040b1002410349005484c2c0c40c1800400c084034500c403030b06485440b80500200301c1c64a000a40c0c4000c100440000358440101a028031f004190703031300c1c00f45515402c1c40b000044200c200c1e01e06103100328206400110346c644941d40036045040e98944800140c0e410003020b49440944202600341100c140305a4000410b0761424000c030000049440a41c2c1c0040001000342c2150001e43c0c80c001c2550341c0240115090f40c2d20081c080040911500e0180410103192071191040f2480d031817101c102160341000411100480d4983d030f00f400700e5a8003a2000000d0510a1b51071607905403620401c039 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 763241996 1250 763240746 763240787
    0x7030c020319390327080106170304030809010f0e180a0c031401050d1109010608252106080f01270b131a070e240d0b032d0d 55
    0x1240e6138101c60904928029282c81900c5080402114605840050052404c100007103207943c01e1002c48c100f1103200f02a8484035078001c0204000040e03000c015100640400d091154400300c44071000c1d20504040800c2c40e9011800e42c003a1041c80706145034041c01101440420825282146c0054007241d2081c004c22404844107001046189410021040800d11600c0444103089514011802d078082c01c1e0840000729a5120821031009076007070b00b00078414451240d8088080940e0303005040b102c103001500d0801682200380c81c1000c45150040401414070704111a0f40c4040a80181d0081c4165903d8030040103011029861080f074201d202d008280e00050702c050244ca40384048500384803190000c030740c0c0c8140c6042c40f240d44a0a0800030f0300c604404d481d03440178400c00c1d50402c8034400c01e4901e5041c1605917600d080a0842c0b5150548030301260340c0307400140e08040e03072002134500461508956004084000e1440c015404502c030040d21188840c1101c41d00c148409050710b1907514070011340303120b28 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 763243246 1250 763241996 763242107
    0x90e01061106060f0604120609020402130305010509070e010e061f020a0510060e1311090a05010e060d0b010611011104030c0513020705030f0307050c0a03020f120c0607030c020319 79
    0x181f2441c200c8015102d0040040c1803e180d034003103070503600324142d00c0c84680e056581c20420301101703000c3d0b0380e44141500d011700100c80c1803000c44110341d08107003c0ca86c0310680c420005681d9464a05e981d06054107811100c0101c0320406800a40d00c602402c001c680f0781c0160391a0140340500da000300403d0768003e80c01d41116985901040c811908400300590740311013044c1c5d84001540300d030428940510010f036004142c66041c210f41c0f901110000d000c190060f8240c01003040807401c20340803d819240985003640100080d00169405408048184480c0d080c00180000400c82e41550f00b800300c410941c3c00200201c40c0e150130608078064242d0141c4140c00400c1740030118071031000295880341c05820403500340509403000307a00c2d06400b042d0403405640700700b80715a42e20004100085e5041c0c0d07074510461521441c048900c0e03c42d6805450305042c55242d1104000590003401580c2c5041400715450200b0711302044000c081c180c0100d000d40c1d020b0513059a07035003103821240030f482c00028418072049007030 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 763244496 1250 763243246 763243259
    0x120a080c070608040f24020f0d0c0c02030604020111120c28050a0618060e07090b03010605030c0d0c0e0f070924110c130f0c08010612020a090e01061106060f0604 71
    0x10002c2091b07940d1042e400e0b0305941040c41c80e80c405407042d400d0341e909640c2c4035000803901c43c0884400c100020309120420203041d00580e80000c8450b8041d50a19090fa008080300034003924003042031910506064011481d50480c51000078001801c00c0242e9030803060b40c18981407101d0030340755008081c115400900c1c09074042001c0382c00c040300e201c0c59072146c111429429140c40c41110060300010a01d40c00c810f40801c80d216103805446034050044008114131842d00d0006952505902005030007807008000c14820f100d0404611001000d5a05c112021850001e03540c00b400b030030072a100b0011551914001c20000d420b22940c84014144151050702e0f28012102550030703a0600740c0c0f1003074500c41c89045250710340b1856040005420b210030003040e100960510f0005460560303d03030408100541c0010841a0341c4458034100c6094007940040c0d0b6510007032000c035a890072503001207050502c0c80000082065010340b20010b55039551066500689030482007202c51605030592660000d130074802482507 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 763245746 1250 763244496 763244513
    0x140c09030d21020a05090103050c090f040902040207050a0309030c0e0c090f0d02040608010617010e030a0503100f0e0402042a030b01090f0f03020a06080403080f06120a080c070608040f 81
    0x109681ca442c90040d06000c18a80001d9911406689001400c0410b81028a507018026280c1003407810101c24203002e03e500114850502244020344901d03214003480080d0b40302c5504560701d0541103000c0d00c41d010390034100503081d0506032004407100165180d00151074074480307601500803c80405a54600b00441d000c00504040c3d07000ca25502107032181c0d0320310042e60746108810080c04544004144c8510307000341c81c180d030700d0018080b10159052290326150182c001c0704403525560f0340d092264a0f91500121b034030f0f84411030b801900c0201c000350400700b8642081c100d224441c80c421a001e000500c1c81110000c004c030300686106100c2e05501024a10481c082d4001c21400c60044c50324a07007141c3e0360b91a584004580e40c1c46101c048000103414000e41c00c0001880004d880241400e030200d0500341d81c0141010002410681900180f42c04952540d0313030100c2c1c200003d0044e2080350f403802010b040444840e4442007554085200b1f0303010000740d040c043c000e00c41c07056030000401c2d19000007980380d1824 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 763246996 1250 763245746 763245767
    0x50a090b09060f16020f070801050702070f080304060315120506010e0a1b0f0c050624030706021b0604080a051c03150902130b04030c06034205030f01140c09030d 71
    0x85d0300689102003e1314808110f401c0c001c0201500100319070802d040081e00b4400f0942005800841c000c400344000034001044408a17501e6280c00142c01084030a590303401c1320f49402141d20044034114000c180180040c066041c0d40445241550503140e6000f0541103480b16881c981c0513185540c00000301c64000d0f410b202509150382084846a038560b602c00c0d0524100f103801d0b800201c04504403e42c4800f0304801804803910540081503a0390030400069038600340641200030020300c101504030703d13031640360540340108013034801c0742c244031000c0c034205860f200246c414001030507819610b072880510a0080d4546a60713210406c403a40e41c01c240d941c001962203c01003481001211200080030589640100011070140da03c40c003a0303508007140103080d10301566504003404051061608400860500e40985200b21461807401014200368030640481d55480140e2500910206001094040d0801000301410a0520903140c0d140480341406001c0e103000c0e99019403110410103003031381c044d4030b07000e0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 763248246 1250 763246996 763247041
    0x9060d03020f0a031817060c03040204021c02031e011203050304050a0b09030d150e1609080d0309060e1b060a030603050703140d2307020112050a090b09060f 69
    0x200ca0104658000d450704420b003504034009000c94540711040301d080484000601040c1c401702c0c610400908160fa47e81e0001f421741a50f0900000104045507510390484181030000131449524040c042d05801c002c0d08202e0b0408010350081c02e00103500a01004498141c40c0074110385100780c41c0c20303201100c00f80c01c001c0c4115102d209813020100407a107008419841804400019079035126181c01c85401c0e40c01c0c202441c1c82e030180c0c0348030920522490240503580007207651450100c0f15040c000403505021b1540c0403031414020302c8045801544d058020752035050240b0302c14418104900185607a8028960101c0d240b500480c10b5800030740303071050003095003401c03900c0c0c082509601c1c0d803511820401c290303000b2503c074152813011107201c840a10440b0034075409810481070810a0300d0070360b0140d01c0f426060300e207050800528401160301840c261400c014210317108020300d1500501e14002412040010f03104010510300190002c900001e00d54441c055140350062580c55444030000c1c01c00e002e04220 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 763249496 1250 763248246 763248253
    0xa110d02090a0b04080a03020f0309030d0c05010f0e010608072c09070f06031b17010608191503111c08210a060501090807030f150e0d0c02010905010e09060d0302 71
    0x40d0540102c0090006414400d006d003000080e18a0040c1c50b0801c01c040c284c02c650810f02038010590380200ba00700c1c00000a09050240030510b26040c5d00421102c592440803d2400010011500055100c2030581c0c041e0012224101d4881804040c046005400802042c507a94846813404460030750094010b11a1421683c245890714032541031031186400c0700c40025502c404e0b00d110410101150310800c010707801c001000140240d41820803103014002d03501440074002c085007464140400c60501c1d00d0f44a1000c100a004c1c20070014003d4020b480305541c000c48a4004075501c2c6041c040589444841d0a0500102d1040e40c9c0c8006068128034000300f80c480c03201c13206c00c1411411a950340c4c81000c040d50006149800c00700090011300caa42c1180103941d204190a0000075160758440c200c042d00020500020949240700f4005407460f1580200d0a0089150820301544c22200c1c004000d80300340c1761200c401d529480111000c0e5804d03406658405a00c4010460506003a01445600c03402071043c3c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 763250746 1250 763249496 763249499
    0x20f061503190516090c1e051b15070801081c0302040506072906030a020f15040b0c01110319051b1c0b030c0901050111030408071701050a110d02090a 66
    0x40e25100405800c10765894020b080c5078240b40c44200112009084810820010011120001400d01c7c01080c100a07050408170311500000d4020000d99281c0e88042c8101081c92250b01d55258a0307059850550000140600104d040745000e482030724143e07003141d00100301c0306c2d038081c01c10b409108501658500b40344d420400030519440301401002a94081c190b0860107c892050b00c1c1443c8481c00004108403a148081c0443d0f0740d004200304132003980440e05948075414000c000740155031841104510717800c000400250440340312001d4108100341c0402008181e6135001e0a8087d1320003154015800e0080804c440c0006400780d00054100c18034920120781404401511086d9900909070840720010281a5803071500e01c40c000d80020304410350141c000c009414011a6000506008982c10302c125003400d41c150040c1001a1401041c1103800c55418582e5400f482800c1021f660708405a0350030540000d03158030250040c85440030b44180e0107468010911039410007034008885465100080c143d0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 763251996 1250 763250746 763250773
    0xc0f0403060507051c09080a0320040e190e06040b0a0e060403090f121a06120d0c0b0c090306041713030804080c090405030a03021c0c0f0f020f061503 66
    0x540c5115007030310f03204d541d9101032035114101140b0464035a5501103052608900007e210700c0165011a0250b00b001300321145008444101c0e04002080c1048085004c00c002501e000c0d05582e2500800394001401c0311404003c0703074901520350000d4001c0c3d55a10013004500003469021a03190700c07640b40b05000030291407020210b07050401c266025030008a2004007482060740c8a40204002c04801a016901000582e01d040300200741c1e507000340d4003600c0280042c0c21610740c414800d559101d0102600d180c1c03461007001810090f034449050b07510100c0d040c0000d503600700da02c04891b10500028024126940c9070364070802d414813102c5214656032420f1204160b0b011000c4c003d14055407140c5a00e0380c449090442c15442c0c4000c4a50303652040c44400248404544040221007040d40d0034600035a44085000894040390940c3c02070a24192814140107422548a46600b01c42400e50352000003010b10b44008a0b0f59201e036030b0b4802c801e0380104000c61110185040044002a0041c040d201d1400342e402 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 763253246 1250 763251996 763252001
    0x12031305100c06140f070f09090e160e0405070f0e16021905030c100605011b111c020f120c120c030d08070f030c090b1e0f0c010f060e0c0f040306 64
    0x40710301c1204c80541840700107010341400c940c0c400083c0ca803118054007410b070010b001741c81a12583e0402e6983e101c0c2400c070301314140013026a404507851800825940c91209100c2da4a08650030341b81402081d201003000c42c40c07408440112003500400c032159840b812042d80c0700d4500750b805a002d600c25806440003501071545000f05190003036000c0c60300e4002a01c0303e24244800740003505440d81c50300794288400e03070300f20280342c00b80740b1040102d080714902c0d450304842d0300820409007580700034410b00c00c0c0034040c010440c100c1024402d9807500d0104e03d420040c490b414040c1103007001e60340c00c040d4a0000b0f5084c2007021208010790201105e92420744440401d040c40310100e09400000d40c0b010400028a400c03446202c00000f462a0800c4007100d5443c000f419041240100100100c0004003400f110000003d0240d04c10820b06c0c0f41340c0c1d0780010001c400c4041d071060351891076039400c010084000011038444c68049a0b02c544884809540d02e0342064500d611a03080220356100c24800880454442e1 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 763254496 1250 763253246 763253261
    0x110105160b150103060512030f0304080409020711040b01030501050a0510091d0915040506010303030c05071a07030b040603120e010215011d06040c02070605130803031512031305100c06 81
    0x3040c090b90368107003640010251619900058018412403c0440102d0000403c0b220b441c1590160140c4940341d51400c0c0b2003a00c0385900034110341d4000300e0050180002c603c15480e000000300e1741006010480720040d415540b00f4402e007507000b00c408008008500301884181501442071810740c01c0c0c95160424455806618140270300010804420050422020401900724030600c0e640c401503440d1580c0e80d59a84c650500000b41010380741d42c824611280504141c81441d940012450b401c041b0200e03401e04480c0c000c450707500000c1d0800302d04200c81e06141c46140142c1c0e42160111424081c100c10558058040e082c085046200d105a9107008603c40c18030907000e01480f10910500355104c08219145040103481d00303108500e410070004c20140c000415100712015410440d466600845d115410044c2980c0000010700002080100b0000800300148200d08110f601a400743e1158401c1a42c80c00342c0321052030344c610b920b402032015160240300d08020700a203150072482640956100819980310 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 763255746 1250 763254496 763254511
    0x18060c160b1e0907080c060d1d0a0b0a0e1506030a1b03200609090c192007120308100f06031e02092b080a111009110105160b 55
    0x48000118003800b844442e50441e440d0f0005100b95070030701601a0311941c0a90301c151240600050720314502180750400c4207a018800385010450301030440e015160383d03040c041160b0310b00c0080b00103a11840c0502ca00f00c902d152150040c80100505c41c460b58002c3c8018003c5d03549441001891000540b000e520b440c0004007141c1c0c0304030390380e18501c1c0070003040c084038a00d0129403201201e5140329803602c2050f40da1110080714440e440751640040d03a0018411001d100c84000703031940d134800491341c0000001d00201d5011000c0400344040b8080c01d0b8a81400d070044c8807940304400303e4400403a10038072410b50004640404c00e10019a5130f180d4055000603a0300501c04aa100c13100410501c821208000202e42180015441d110031200007400c181c107655440d150400e4020022180480b6100f0064041907221190990343c8815039000340c040e8800081c0c048085c442c8650090800946000d058080b40d800074001c201041d281005669a41100c14010141400e80032418041450300c26164000e02c05d = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 763256996 1250 763255746 763255771
    0x110133082b0806090a0c0905030d0306030506011e0314010608010f0b01260612011e051b040311010804060e120406260c0903070f0b030f18060c160b 65
    0x650201c40c00449a8010041c01404191020400c03251100c00003a0b502c142c2c14140098226007105080d60002c00700d408c070301d0f014800d0106c1b003842560998085030035a0700803c100c80641ea41c0c3c0e00351105400c0584180c2268000031502080066000111040341000035000854000d44401d070b945d0031034a00001402066403503000005a658000205580e120003025071001180c200e034100100c00407010f800b00303020b162014000d20030010300390300404016415040034407110600c1c409a2000c3c0a0940d142604810302882c00d03502110480220340c200c039480218071101080b107000558600800070001d0f210180c850ba031500b00000c00b03104d5410b60741c601c10782da0b5482d40e003407800091404041040b100940c0d02d80105c41c1004201404142d54010800e0085541e1160740001080c02c1c400d55600c503a10581139244042103a416502c0a544200500b260b0310346503903202c0c02d81400000c1517003100d40c1c0070f403c0b11020403c0c0c54203540041038910300c02c0309400307070454665480c554020710031505401036a1 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 763258246 1250 763256996 763257043
    0x2030409060b0309120f040e0414150708130201050405190603060b0703090306091403030705070506060d030c11041e0510060207081e07050406080c0111013308 70
    0x2414031072680a024030302181801e42c98078001d40c40d030700c50285c08000340703400d00800c1d02089180084100c030040d0103c0c80444260342403600c0c001014641206400381c0310301a40e03084544814809181900c900125621280c03503403105070003990b0b1020500410303410400700704030106040c3c848480031a100000110611142403500308000e00700c076903980062a000e0000c01c01280402e9101c100030341502d80220300000e03010751030301d8200f0031041c04015081440c00701008001c0c585412a018144581c0164141c0c1c801344d031664104403007603038540c1004000c620390820302c070701144800303070001404000680000350100800e46050201c4070750100303406096440304100104203540844100007414a80014001c0a040c4000e840d2101c20070800c1040e11620340140c81c4031082d08100381e40082c01d002d0000c10030340e074590741c40944803005c2d40e05041c042035448021140b4080305102e1200110300c149006402000c00f403510152120521211404c04c0e0544034020035040700c103000b001c1040c40c0448415028a = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 763259496 1250 763258246 763258259
    0x2150f04020405060102191e02040912021011070b0a14011517010e0f0901061d01090b1519020f060c0901180b04120203011b051e07020f09041e03020304 67
    0x20b0f64001c0501e030464101071141071007062042907030364404c0d5002c40a00c0891030300301d00c50300c0401c0d181403020b58800d0804903003000f48a5004191002c252032907003901d01c0c424000f24440191100c0d020030001c080410040c020114100ba1260750f00800340403400f20f04141104240044030f102a000026240034140c10805203e41000a0000d1003141c0c01c142c40740c0e589441e44030785142070014003100c40b080c0e00c080003482d0b0345800e5001201134401e0040380c101400e180c560090040c4401d001c0c090f40fa924005000e00d851410344a07200240207607401c400d03d00406440359005007421402414198415812600320204e41031140900c180b90b0414900d0329200c440000608000c49500d10b0b20711160100014443e8400040440d01a222205402c0030000428030210b80103040c8a031003840c00145150201031116030140040040d004800c030688030103600403480c9030303403071050841c02503000448025401850a0241022391700c90302414203d0030300f0308000b100404c4040d0480c3c0480050f08000b4060002 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 763260746 1250 763259496 763259501
    0x3080a050901120501171b06030106030b151323220209090a091109010303020a0b0720060402030c01090503060f0c0705060903130e041115041208130503030a080f0702150f040204 78
    0x1800b01a44803201f035040300c4c60228049203c103000748020592641e2103a08241c643d8503003003103010988010b80d81e5444d45a04204a942014042d0728101c0d044d0031910507583d42d006040c003120740c0c0b009103500c1d6030495121045500c0940d0014039041d858092040a20b650380304d0304018820340038500042590859407421090b1603003281d107401c1c8113503249001440400d038005410001c0076032084401e022615400001d9403580c10b03205102561180021150304c2c0c50b007003c00c007240154030075401c03280c0001071540150b504c0842c50003000d805070701103000969890004031580c0d030060b0024000918242280c0ca48038103001c1c080301c8003002580300140000c10003401e41c038000010078100c1e05800b907604040d41c580b502100498292886900c50b04550340308040044202d0300200040c4c1c205003d4181e140c03400e04e0b202d410601c41100ca402d11407800051a06001c030032a00d04000b03c0e911003985903203080c0400e5601d40041c01000461184146217180000c2c1200500d01a0440e1b20020729149000c2c8104000d = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 763261996 1250 763260746 763260763
    0x30901150815060f060403050f070807080c0d0c1a040e0f040807061e061503050c0406090605070804180509010513031d0f1003022203080a05090112050117 68
    0xc0800d400303080250070340129201a8004021048000a40780e5000041508511364616903200c2e50001d800810840005070203c40e00c1a401c023940c480c0c3c2da07500b500c10384502191040302d820b90007401030340700e040c07402c1505d40044c03511a9003000b00c00c07603c07a0b0030740c0740e0b030081c510306e0007513083d40010188030303602040301002d034441100c08a031340e01d07443c0c150b035048924043d4040c01048240c407480c400200340c0f1401c0c003c2c3c0050b43e6580c002c114141d51210442200049a1903c2d400310386808081100400320074201e4045c0e5610747c442d0f40410f85802c604888a074419402580d082805000c041504440844c500d0b44032030340742101046600f0302040b420b00319080034208002c1c6507001d5514038000703504903012030046400081c0e00000c0038007640110340c0388141c51085640c0032922201640c00d2940590191060340790103681001c003190140c452642e0340c1024040640f140d81c0030f004181446214400401040c4410300d132008a82c415840d264064400c01e0b00030f524081042011392000c0c0204101040 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 763263246 1250 763261996 763262021
    0x204030c0e1305030703031e090b07030e03070b060108130602040603020a0e0103020901080106050c01060801090b09281211030a0e040506040902011409040e0f010c18050108070f0e06040b030901 85
    0x102c1c0e0800c1d41d8629660340f180400003804d15489101666600e0404c1e840c9a2000011070000d10000e0044d242552610744210ae6103000301e80b81c09070403e65420000152010aa4490008921070702c0c3c070001900e100400070310194841050b51303030020024089001030001008039403070240c0c4400400d003000e01040856102c0c181090f20600c800c14003607030f00c0780d88241116202d007086991014441161400750500e07420006040d82070842081c1000000626a841103030000207490100210741c16a00c0d40402d04040d01d414900d103503c0340e8010031002040d404000c2c150b81401c070030716180e030003409055421001c0b01c4004140c030b0382c405014501303040c001d40350f01200407201000600302660002e4090a44140c1c04062130b0070105048085445030f500c410500306012084a0707695400115084c046c00c02c13030041c800081c5600d80030100400d2104103080950360161a440c3c0507950f002d90495464803030062940c1080302c0010940c1007621204001c00c0034052104015030b807486d1905036142500c0c0000c0030035 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 763264496 1250 763263246 763263271
    0x906010507081e09120a140c09160c020d05060405100506060418141003140601120201050d060e0c040f21080c0114011d09010504020618130204030c0e 66
    0x200000c4100701107407101c0b002400c162003e18207442c6640c6444c01014200c07074100e8540d60007031401c401c0c000382c003e0b80b25218116180e103050104080300c0d1911000300d0f80d82e8014a403103000c42d90600381c26a030703421800018a062842c6804d26000a43c02c0304d00410160b5641d0400c40600040c003d00744010a41b0b06038408041c0814100000421058070403486607000f51881881800c100c940d461300844c45070b07a0803d584200500f000c0b071081030f02ea5818401240d42c00c079091014451408042001070482e0b20800c1c1101c64424650019512030b80403c1044050640e03920b00840c00c2c3e000d6a140314002d08005282c02d07112401e01c840140da400080c0c0005c0c50f10b10400325500b0703003c0c40c1c81008510f0303180d0011f6581d4a078540c120042d80505011510200c00000c25400400d00c021a0700d4011030400c450030740301d481e80c3ca640401c10300701c60381600c020350046d0b010000121810303a00c0404080c61280641045010110690180e040382c0064008603490310803000c1c204030880c502040a070b0455045440c1 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 763265746 1250 763264496 763264507
    0x140c0f210703180308060d0309080304060e1807020304090513020406030b1006090806061912052b1d03070305060a0b040507020d09031b08010e0f0d092102030a150b09060105 76
    0x162456000416440c0700340300c00040b4000f09446455270030010f000440440380c6031610741d10043d20348140300d018580158a0381c0d50700d0700302c01b81030019140600d103960040c51800f81840c0302c84024003001091040040942105900103850314481c0c200214020301801c1d0042c20300d410203043c403005d161302000c200105208140000000400c40e80e810400031100c905940d4420400c102044c2c001d5880310b076104101181e540203000001c00c1d56020780d0300380ac1d1407071619903100250aa8210184c0c2200340003540300c840b214024010303280d0a45c03501100030200d07002181e42e41d031140e00e456030817604003403126207616503040182440d0040c40c0d00484240090700340f002d196400140f4203c0c0c00c0c803019081112640c10f00c2e10078000c080303208001d046294028007117002285011951001c061188240300d110386c140c0c040c1034034403400c045001d4800002240800340ea46182101c3e400700003030000c3c0da01d4010009181c0001e4131904162045010908000c81c4410104040040390340c4010001c0c2c0c14000e04020 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 763266996 1250 763265746 763265753
    0x140a030504090213170309010311041518180605030d210510030b070f1d0d02090c0409060806070e09060d030c030e1909050a140c0f21070318 62
    0x1920181c603403107240142c80e52038513048641846501d9200c080210300241e04c0c4001840c000c4028400300d6000e8900341300c81d4220b02414080c5100760b100311900c86030000b141e055401e10540800000c01141034800480030303103031203020110000500d500d448503560340c0410816070800b4007401c0c00c00b81c41428001c4802c4015059090030001d40e5191401c1166a100040e5000300240c500c44095034111541c0d002500e04140e002c0c2140611514a90126800d040d0b50700341c00c0c21441d07000035481000303030a4220100e180d1b428000382083c06010302404880502003c034800815106050051600c80002c1c0308074100303094050300076144482ca5a0045e03040804203c5152101c202e00e1080c5a0300d880c00400745003007400c0c1200c0d0441148403482c0d010780500a10030b150044003601d04241e82c036040082000ea11101411011074501c0d10002e401c0c411b19000003050303100c0c1315000d071941003100d0612615250550384252124241003400603412500342c418400d5603581840744100c3e0700220b00c2c0034030444001d0384 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 763268246 1250 763266996 763267007
    0x9060c052d300c0703020c0d05030a0f030605040e0a02090906010e04171b0c030c0108040b010e0c0706060603020403060c05130e07120905010b0f090709050d1e0609140a03 75
    0x2d4100c0030780d406921440070241c40c007001041a801950490350b0040c184114022101c1e07000c43c00541c01441641c1c0030309024030380440d01c8145990b004005600d04020002c040e11040c45280700881416940c00000495483e54010400350100210142113001075510402c1460000070302019120341c00040144113810800e4840783d04035401180900c010782c41400c500e1400e12070004404006090200030b10711010001a03044145c202c118241c2c1c0380286504011281c0100c00c8030060807216a42c001000707008c20010403181c2290288a00510741503082d1650000d68245910450000b940000c0800520002e0b100b5030800c000c641c50507500c0c1045000c2403001c558520300412000c2034160300032460321360060720001c603140c0c440181486100ca2508042c4c0c002c0030310300c002601607a2444c040d810302c1c2c54400241441180d1603250b1603441070400d002d000c98800c0c0310f0740032901c50000783d54001c41c40100e00d440c200d0491003924042039507201c6240200c0b03a5486868010081d60045100c080081c1e0481c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 763269496 1250 763268246 763268257
    0x3010902090607060f0501080d110c0618030712030e10120c090f03050303251b0f0c0e09070801020a051602040f0e0a03080702030a081909060c052d 65
    0x14400580c4407110034000031098424683e0040c40a03103483e0301e038940d4070103940001e41214034030404d40384109100c0d0f4050b0f03400462069001841d0b08120a0304016242200c0600094410030211000d104c4000010034604134641d0804020a040400070b4410107078000315100100c0c5050706d18103110007906c45c01902181e0b40030400c0c1e1070389071100444403001e44550160401081c1a81e400d016840d600e0402070384a1b402640e03065641124829034407002e0b90b0700c0003010555403050307a40301440f681d151407505200c80f52130012a40d03050302d51446030100700000d0300d0b08054441301c040c00da400d0034080301282c03420405620001c8140d005201400115400c5000d49102401407441c84510702010301c0040e008000c0c054680140c035207060000c440a00002400105080c0f113070f20b40d25000d448418090341e907406440c440c440015003c000140e2030791010007414410810706200170441003500d0ba9541c06958824544800161000c540682c503001c034100300314802e51414551944491002640780041d1250 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 763270746 1250 763269496 763269509
    0x7140f0409030320070c050f010912050a121e110715050912030c060708060d02040207020402070b012409030506150102030d180c0504050f180c04140901200301 70
    0x3a14070103002d05009401c030348050601804407000203a4000340384071854000070b03400d58400b4a140307004113150400c140c118601e0030050712020200352030300341c401c1c01800090000f11264003c03075018100040340e00142c0d45181c0041e403202c1c10404512000414107901c503800b100700304160101c1c1082259004182041a0b9075042e80c661900384100000b923a942c4203021405030803001107804036180d00408006440701180401c04d4a600785c0340d00070200ca2403c0c0544055a0102794201c3c1a0300600d443e034024a0010b20281c0050b04014540c0c94441c1c00303000980c800320000d841c80000004980d40c68003081e0b404d039014100b5900703113810758980039625880200303407810800c0c8426103031141e03078020400c0e0b80420354402424002d1407040c5140301048000c100e001c850b03861a03020085170314134150040ca840703030750101d10620b80c9a07190f22034100000c0005142e2543c034000c5015280990716680141d0034500b000d000d5800b054241350741c84c1c0e821644140104c07c0100307a5105404405003091007240e04407600c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 763271996 1250 763270746 763270751
    0x2406040b0d170c0c15030f011a0a0c15150f0b0705030405090709080607030615030c021b04020c03040603200c06070f18120501110a1b11060a02030c07140f04 69
    0xe0140d00a252500d015031080e4042100c040341040171031000000c51140780308240a94659030799002090129601c0c00030705044100c04e11840d41e1140c81008010b1406005169806803046000c003090f08035107c400000c0c401c004404800e12801e855150031340c0041002e01c100c68a0180282c80304c40e1240140d01401c2d03c6480c2002c0805d1825114081c1c40f8054400b0a080c0c03211420034603006030040c42d852041890643c0384281d210070450003807265001001503a000f42c241000031402e004444903141600b1030b40594240b20b401c866110410251000e00440e44001030b08401c0c0c45241c2c502e2a00c00301c0800540c2c241040b201004020203d174040e007101803803d0035503501807140816a201c0c548846010401d61050000040061651107505003160045000300a0b950410f81440c07410304c00c030186800800d03000341c280c0d0201ca00759944038040c180500030021141c04540b00041c0070b603100c400ea40700140c0c00420400102c41c01030005100030b02d42000300280702244100480e202900c0e98050301d1003507a = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 763273246 1250 763271996 763272007
    0x5032223060906161106041520010f0e070b041a030a09121d04290a050a260307030207060f05070b04240e030d020c2406040b0d17 57
    0x1140c07101030300c1d491203008100503290030710300c0220302110340341c0c01e03080d01c10384104c80782a201401c20100302e0381070300d04500040c900e41d03c4442d026034002d100b10151840703402d454080415440803c0c0320700e280e461a002d601040001211655a1600c1400d411140309072001304005c111082101514000d02d4901114091300c4e69940013160380102422072019044030450740c900104c5960080001040c0210421049018180901800200c400440908018190781030030000b0200030000e150021880083c04840e80c00d84980109443d130400741d100311a100c1143c07016004803a0340310b482c2a100900b180040d4248000f80c1c400039500c00c1d0504c9503005000c207030921420705a02c00d004139080c564006084143d241043d25142c1000c08168052100c80b01071907124901984c95801442603068998000f1401c0c943c0c1c1c03011041c002c0d4441e41c045201440b90100c2c07000e22100c092581c10083d1240c0b8445001454103000f407005807400c10f00b11600c100100c2030b0550001c1d43d0003020340314502000c8026034486 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 763274496 1250 763273246 763273249
    0x2070f051f0210060e040209070c2003100207230a0b060d0305191e03060321090e0a0605010e0f1e061c0902040605010e0102070e0a060f0305032223 65
    0x290780c030840010914103088002c00e52170140010780e400b807882640d0b921541d54a00700100c840c44400c80b002890440e01c000803e04002c40c110001350990b04c000c2c2550701e02842022100100d0b440350004440304540709410b201c0012448102d090300c0b0114002404201c8825520a000f0300c80c0142264406c3c18a050090705243c841c406440701c455a050340c0d01400100500027030240b99042c1000c0041000c048001000b9a219018030411207a00c0401490456036940d0103801c0380c004480d04204000054600151071240d2456490203174280780400071b20350b41800001071130081e2481d41140076540c44440e0101076183c0040016158030807400f051440e990410014100e8441d144082811000d450000d4101e0103507948180380303d9200701c1301000341c560345030010741e90a00d150140c5c1f80540c01c5800100b0500b91651441c6505c80340a901c005034854841c0d1200c03142d44030980003668654004030740300d40514040590038402ca00d20307800c800011481c0030000d03845072810058900b528840f0380240802ca = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 763275746 1250 763274496 763274503
    0x20c01061a071515050f04090210170702012c0705100207091a030703030c06090512040312020c0a1509030507031412030c07140f0d030c02070f051f02 66
    0xa4200704600701141c00314a41044030942140c5000d540c4009400c2d101848124a0b105155288000c24102c07001030385000b0801c0740c4a40c0031903a01750401e40702c01000005a072003001203100e071445911011800c4000e100c08240b00f0701d00805100542e81b412041c01d400b6505000340c9a610014040b03a043c14520411000b82810040e0344013980050b540c450341003000380c000c2081030544005583c1045034603001d4204481c0c510350301c604141c050f0401e0005202191282075240c3c0d14501644020940384c2507030307880f14039025280314188840c0d24003050500c01c00c00130306601406025944000c0c0501e14640000070f10a420501c200c61080c2c0d54000c140c20701500540200e402103070030005403075109a9900b4410206968040b03007196134094a5040c102071141c090a0f0f074001d04140c601c440c1400c54683c0c3c0d8200d13600c58000034008912a45004540048040005001d10312180c3d80118100b000c036900030b85040c1e01908440c118000501c0c0912040c1c03101c204c4824020800d071000c0c001240c2c0741c1d80c183d05 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 763276996 1250 763275746 763275749
    0x5040512030c060403020d12110306150c030313021e01080c0c1608030a0318081c0f090f0c0501030b03060a0f0216200d020f090403030e030a1101051018020c0106 71
    0xa43d003c1c1074108014140c0100c0c040070109501d4a903200d554450700d081a04507412180050002c150502c08500c881c1005c0700c988859401403404646001c5c0b0f000300403840c5410071240703e01c038208081110030071070801c40b9480410142da0b00100034000c0203000041c1030404c0040100c0d12804000c1a05804c0032004c00c12480000c4195125000080e182d00b0203548980c0031042501c00702e4105134040011100407600140c2c03050f0821009428070310751400e0709030711155154018061940303600d9000f8030b0b8841c600c1040c000c5440354801d82e2204440e071400029052065000c80d050516103a20303144c4903100400d0b519400b0f80e80340e100003203d10450705035000034013940d00080500445080c96604000c04100950f002d51895038900d00048503034402c2001890344440002d4128541da02460000d06080b001c007904980f00b4100441d2660b000d1a58900d0342d04050035440020b0341003403a075a4501000c1c4238242e00b1090351822099110b06000030300200c4c0c125465403015059001038079400148c0294022030 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 763278246 1250 763276996 763277017
    0xb15060703180503070f06050a030236060a020d03090f060e0d120b0d081c1104030c080102030705030f130b04030504031a06211f0212090109030504051203 68
    0x40d20303025203040050810400c11190888003842e4000070480d85000103440084900880c9002e0700036090190480320343d0401c4603c8030616400f44602c812203000a40f1060a2a0b0401c4072a0f44002003494801c500380400b0340b0709402100f0070440d40524503408652041d00540300d09000c18004410300d0081540400102d003c0c04240c9010201035280e46c010901c0a01000595038112010244410700e4049442e601e14841e400b44c409514980080c2c06440a0b000345010317403102e072440100300160041903440d010303562600a100000c040c010446003000000140c0501c6000f1030440c80c0c0741a001d48603200160942004007450800900c080b64000300381c1540319030081000c030490034240b0b4094680c0e040340c081141e4503e06005042d0051403295480e51249600824940c07841001860301c1c24040340c01034010140c1c0c050500400b02986500c0c540707003410b100c02c400050750380c444a0301402074540007400c40703541c99040110343d07070100f80c0c4001030b14180c5030212002c02d12075002807040c914601c0f5240310b15 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 763279496 1250 763278246 763278259
    0x6130801061710020903150a0f06080c130b030d031503080c1b01020c030d18091107060b090112110f041e0b060c12092b0302070e0f040b15 61
    0xb14020404040744101205140119000000c510443c1d805a008112a0542661000144080900c24017255039008113240c0c0000400300003000180c02543d00503000641c0c40c4c0d00040440c8040e042000e04110107505204080004460b04000a40c40301101180d44c400c043d00e4482107a40490b21a4000c001181d0010f803081e56200130044450b01d070840e0024903102c072003045003004020f500125a142000400801500208540b0f8006849141c032130f0b0080011251159804208010188100c4840c5515408881d07224401c0d8a41881a1541c00340110b0040040c000100311868a5010030b0204941c4090001c0c8502d10541c00b040c030088a0400080d48a400d1003142407007099403681e400301ca01004a070501903503500710700b031000390300c1410400e00c429480010310102c80305000015200701c0344018948244c40368000d01c8081c885162030312550401d140ca82042d410141c0412080000f0100c548190366580f81030800600311440003440074207103074164400a90142d4a81c01c110034080c030300a10300d = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 763280746 1250 763279496 763279499
    0x70203160e0f1003030203071b08011104050a140109060c060f06030f0c0605160b040c1a1209210304020102280317060306041709130b0102010b1504050613080106 71
    0x320354884002d03200d842d180c200400c0880d0f000c401641030807090b260150005e5107003d10700c0d03a0b05d0b0180400000e00300e0084001c0074000c100718400303003d00c8001c000e400e9100c92f00c55040000304001401598820008070301c00c00014200303a60842d54080481700c0c2410a0714071100c2c1e5081900207044542a200b03501460700c400402080b180c191141c0880d0b000300342030714440e5111030b4141d50510580d008540c01341000308491001039081091035902503c182c410402d5960380d504950281002c610310030220000104601000a450f0a0415071201c4290024003225680d10160701440082e1113201d0003070f04001002509690003080988509544521114240380f25800f214400b055003200440028000341c003038004605811445600412006016066507240d6540e810240c04484281d42d00a440a00031b00c03441d961880b00c0103500c903c500340d011404090316000282100c0300450614401d25464090700c141d680040c080d541a1201640ca8a60320502148a4403040b9043c0c0d00c21411076091030380 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 763281996 1250 763280746 763280759
    0xa120503071b080114060a1e08010f020307121506050f12010803091203091804030c050d081b030f19060503030409060f060519030b060702090906040203060a090b010b07020316 77
    0x40c2803c549840d0004c201007440020070031640d0b44169202a409100880d061044043c1e01100c001040781241114070f403650760b501c00070300350741c00700604000403907002c030801c0485034000c91100741100303a10404000c1c6604002d02d00b21903032072b40d0064008000d40800e0300d5160f0b0444008561080c2000000181150ba480b00d006076250300c1400024000c0710f50b070940044c030600000070303110b0a14005040180000943e0052000940c00a0055080080201c1c080300410000d02c80000c0206c0b4a9031051002d2410f480038544106400ba184c0540342820010850503200c03c030609034100040e00707250060f045849a114001d804240c00c1a940340c000024002808441a44001c0c129183c12030b41c0542555030315404d603114068034100e102070b51481e0b945008150300c01d03400309442d160001c0003a4103150080d00400c101d4081200c802005510800c20300040d80380030081154044003d80c0140300001c05036a50521200e4184900c00e85040c020074042c0840d5000e02110b4908550700342c298210300c0c0e0350302 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 763283246 1250 763281996 763282043
    0x302120412020d031e09030e180114010f08040f1b090516022a0d15140f090705040e0a0501090b0f1e1f0902042606060a12050307 57
    0x90707044000d40700e0b105418603510b00a00404500078a50107110b40032000d450240c00182c49044022020031841800131601580c9420800c030801d161403401c81034540c1040600f850000412840d00d042c00002200400c40c82d90290302c1d5648603600c0b442c1e092401d00e092403c4000f003590114416010705030003401184e111650b601c9140b00d515039241c0300240c2c81600ca070a81c0c40340543c541d00c1e1502c000d01509055021080218890a460090540014004551100c0b6105521401041d81c556100c6000108910040c456160020403d00700007240303040c801e000c140c1d50005403040a000360340300c07108020844014040601c501c1c1d0094002d10840d101883d00b242e40e900d04035000001f004034100465a407100c0300e440316500c00c0e94040449859152640404c07a00c41c280342c03000b0040015a0004501c81d00c50380060401491148620308011518203100c1d90b00c60101000002e0b036030300c00340030001d4558501e28102c044030344001141003d103256090150851140c958060030403c1a003440c50030944424 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 763284496 1250 763283246 763283273
    0x30102032419120515060a1211060a030231051306120b09060702070b040b0d09050d02030d181e080f121603150509130507030803061908030d050703021204 68
    0x104145d40304000030100395900a102500d620750401e54003035083c00491200d04610a4240c0540126209114524009007e40d4446c8601d500040d0300841d1040b005282c0d40b903142220804502520321080d40d1895460110115100d41c5104884a17590100803103125803144000c0c10804280c2c001c40e100a0a00c0545160283c500c01250310400703000031102403010a0a0b0180c0d0048070301c603443d0918046651201d50004000740e0f0000f9a907810140000383d007000f000d10180b441f90040d60311511300042d10012a003051904a86483c040000c0707800144a180c400303209500700c4809030000c5a0507041958040c05030203812040d14070b000650f850340140c52402d0a204001d40003404800c54040e0404405603041c03007030981200303046007409110a240000d0f542e90300c801500845410340f00c15803a014940001c541c4140c0c2c00c0703580041400954205400c0a05800c58100f110003000c61030410050790320b105524030104c8444d56807001c00d601a102e601200c41c40303000d8040c2d5590b54101410a00d0603410107 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 763285746 1250 763284496 763284503
    0xe0d03020901230c070b0c0d030c110f10060504111603260402240d05150d0b010509160801060305130b040602032e0e0a0e03040e1503010203241912 65
    0x11045c2c00191038201c00c00300c03019161307e000a040e0f440302291059000e4041d15101c442401320030100f5001c004c100304200c006444206000700b0340ca403e0f20000d0030031980079800c034078040c600b02100c1040601c0240e080399144814151110102129402d0441c1d03808028600000e050b460107210714141d085a10003180610700890b10700042280c249a404410072090301c4480c6040c806005504480001e94000b50f4080f002c0110b42c1407050449002681307404216004583c000220401401a8103140e04003d900c42c0c143c43c4844003d001c2e01002800091051181c0307404c06454900140c19038843c01c7e000362404d9030240340b1103500d0801c0d20b0100c010390001c0b2041102080b18620400074111043c0440719200300300701c2d42401035400c064480103241d1008003281ca10356295200c1641c5541c00f00010b00081282003180940350402140f20109810500c003a2842680180244044080d086c01a042041c10309100207554601d044003042854561024102c003076030301d1010005005092040a0384511310 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 763286996 1250 763285746 763285753
    0x61211210c0301030f06020307090b0a030c260f13060908120708040215070303091a010314031c0b0102010b12031308031201030219030516030b01090e0d03020901230c 73
    0x3500140041030740800d10005d02520340f0512004c000c1405caa00458200d501d074503000b42c0c1d40da11103c02c0e400b01d5000907050b00000390344551401d038036a84180600c02203160348400117500b602c1c8102c008160b08001e8241c011030103d200200f04400340ca480403c2032254484014040c400041c01c180329940c0010315094002408000020310b11480b40354042d03c100e0b802040308100d4101000d0014a50300103403c21414143c1e50581400804d442c078507644022194842400d00f40d42c15072520520084440c1e0012a441d441840304904880c901481210480e2844e04005521480c901c0100c0c094400c41603001c1d0803428090b001c0d001108088001c00d01400d51038480c8900c0b83d59052a155248a03a00c00d615155117001c1c01800145800c2d4010380c510141c1c0c00b60518100d0312511517030304001414480504072185e40c2e40401c10890780d4801c01e401040095020441701e1100d215041e22402c4400080c020036500141304035a90303000e98078822511801c440740705603081c40c2055454855200c840309205a21 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 763288246 1250 763286996 763287001
    0x510060e01090c09150e0a080d02011808030a0504020a0315050901060501020a050a110d120509180112030c05011d010504020a1502070314151611060601050406121121 73
    0x4030369000740c840b04640c1da0b581540342450004905d41881142d4650020000d500070f0b18940c540d0f860291038042c0c20f503400a480301100780507002e0708442425141da01034090f142c01010104840340700303480d0320510285002c1643da0352032000401d0341c40c00703420041600c00350742c3c90f10f6100980c590007207119070401c000030401d01f5220307001a43c4d24024107d0040c480d5101c05030b0718000590310381c00c444a006d13000d0b0840032903000c50307a1000a002c125099640c0007420104022001d0b00d0b04400c600100c20740e4440c12940340d410a59012050822407101900344002028400300300802540040440e2020904c2116035044092030303280601401d8400740d1007141803090100d8603607014035100d081540305070000e0001901d15030300c8150a110302808410703070303001c1c000d95000c1e56142e4881140c0714502021580c4803618505402030716070540e403141441154415010082d2590304802160141c940c0c604048034815004140c040191880e103c2c070100480010035407100400c2c0d0718801c2014080074002900c820b6 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 763289496 1250 763288246 763288259
    0xd020a0809060c07081309021b12090a0605030402030a02060408010605130e07060c1103060403030506090a060303210609231e060d11031608010e01092d0510060e01 72
    0x7003900b902c0190120f1010086040020340c07a0000b0f154221201c404607458075614031603c1d049070043c1d4403a502010400d201009000c205200130041c04030f104d12014203204422001c108010403a008001c14401c0000101c0c0643d0340030800c03c1c0c1c07880e42c01009190b4564680039450302801c2c2c1ca00c5441e01407288001c020084c00b00c0c6000f408203000d0700703d0040881c1032034964100e9984158000507106000c11805000082d141131120b5031080e40a6203012980741411024410340720030081810801c9403a005051000a511501c440b1407840020741201c0301040c04e00121008000d0f5511204101d803924819600714044c500b0207029404041c51030082543e2540c100e540b1071151001580c4860030f4410020b01c0a240c5041024840360040c6100660101c04801003454005600889601280031403010000c1c001d00340240010850002d000340110160303030750745482d5541110741c0c040c0c460520100411240d015030301d6000c4240e81040c1110509c04189200600610343c0d8002c10500d0301400c000130400 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 763290746 1250 763289496 763289503
    0x10b0a090b0d030e1305040818010c0f1205040f0f03060b0d0b010509180312160507030e060d020702130209100807021c05090a26010522080d020d020a0809 68
    0x2800d101408102c8441c003107030b500312100055040540d0307000051040c0b01d89461542e03c580303849075104401c015a2002d04000050094141440c030904201c01d0b482032130006500c000c80100b030b2591050066000300024602070310203000d242c12102102101c1c0310009043e465600f100c10440c0e01440e0108600e8151109200d00c04447c0394002e1301000072180100428201001080c1c0c0c04021048554504a070f410082d41c115413200408045144a883c2840743c0540c05981802a144990a000e450541c4503070700500581c040748016489a240400c031b500b02080c0503012503072041d0b401000d00c184402c03e01c486400a400952045028041c0b05003c1034226004030050b074090715183e0018039064003d072450342600740800140b5001c024040c00003202030781364050350a000c3d02e026106440c01e8040c1c41000d044a4040b40d002c0d6a0310313810034052119400e9081000c102124221841c20600019070500d088140720300303540e240f0003a1001440300000c460984c00781c002a121580e596a00e0b48526102070365 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 763291996 1250 763290746 763290761
    0x16090b06160f060207120c030206070f020d0503101a030a14010f03110a03060510081606091511030a091503060305030315301c020a02010503060d14010b0a09 69
    0xd05840e89848903001c100c031850b60b2014144900b40152405006030b44442a0000d142e00390313004200c1070f041c04005c040e01840708a0340b0420b603191101c5107480c2d80c07000030b5598041140000a104000002c54100c02441d0105005802105d031404901c544841c1d0032042c03640300716000c86001d89050700c0b544c42c404d14009828100c0b261a24401103440c150b84842620320902c042d80c5a025a0b0b4000020004405010f041e01ca040110200b960f024500038010703041040140b2100580c454044080c040190072842140540b0f6510501540c1903090a00940703098115055200041c0b01c00310b84020740a81c850014000d860559100402c0c9041c0001d06809681d0705000c000c00036003040c030000f604c1c501909103240251f003000313000310003100300e81d6228042045aa047c4400400005100c070308038a00400000181d0900440d1703a80070032900c200001e442d9210040024100a8004080380c01540e4178005840703415002a40c04604c00340e0155154002c061b00c071800d0340a54103203040000c204030944500403 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 763293246 1250 763291996 763292017
    0x60f0923040513050105041227140a18020910020102120703050603030412050a0201020c01081612240609080a0c031106160308010e06220c020c0316090b06 68
    0xa1892014001c210240c000181541c425a1412848001150090140134003032400303000c8003001103c5441d0000c00d440000102013682182e032218441007641c0c0901c0c1c190031541106c100c3c10880c20b1210002d0554035071035210002404d030491100e5030f040319581c02041c080c10110750343d0004181c5480160300340d0080c0051540402d4041c400203d003e8080d8209503030080004080e03d103855156500e10100a101c0c801c286d03002d50050913000c086580400ca00070100c80e007400c2046a501e032401c0d2052600701c10000c1c290401200030040b00455109811103045070950611011910b0b5007001c07489848800c501c9514006144614005010a0089864002140c11030390250607141142c80b5030302080c80329003400b90001d20401900c0854154441d070b003103080c1c1c0710342e40d02c0c22503501d04040c1810200d000340041e030ac16203001036010f128280d0106000c0c4404550302020440c6ca4400a05a0614041c0d48203503405002d24005c109038103902d034600c20142c035407003101044010400c609100b282e018106901 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 763294496 1250 763293246 763293299
    0xa0e0c0306040b0105190918090209150307030204061d011401090b070c0504050c0316090605030a0c020a0c080a15050112150609140105010305060f010f030b010507060501060f09 78
    0x41c40604198120000310300c018141a441d240a400032110320000c0355421500281d44210140526100902d01010b00d003400501404591001d40004a0800000d0480f9030b4001c1d01c0c1100c4021520103200080040d50000c1003000b12030f682e006c40030880081d41c0510a00d0510740000414810354916025440c558181d5640f10010f00300103140200e640014015500f903258907100040b01d81c1d9034082c003071140c448418407507200e040c0030601c00000194809810144100702d5002e10a299016050b45e500c0066000b0110b21043c1140c070507401d14032642e8000e006d110398a440881c61150004100000341e1040025044041090650504449082c00b6080b1541d2070b281c80c000c003051418880042c44650114005102a62042c6030001c50783d11917924050500200010001580c06100e8581c1c07201013035480000784150322000905404006400740107144d910307011003107141d10402c01d03150417a030310140030442540c4480d40504001340c80f1070703614000780c410200403881c400e0b42034410b40c4091000012 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 763295746 1250 763294496 763294501
    0x1b041503050f2202030307120c020111010501140d020f1203190809070302040e1015050907020a0201090306051b070f2904081608071416050f041a0d0c050a0e0c03 71
    0x83c2500d0b003240c590705a84c903200910100b07000c20000c500c07019a0f02081d88511556000700d00c0090034044901070240d0169140c01d0042084d000c0c8060301c2d0110110442e01c071001b9813400d00c0001e1300d004022903480e420102e803035029030350040004020811102002010503c001c1c200728216030a00040350a188070b07030403001d010001030403d0740002e43c050030004269060b02c60445481c4080382c5101c42122000c03031841c00104101e08160800641080e0b039031002d403000c840c01c1d80004e4500082c41c0310080460b507442c03000407901c10581a03001042014006203541d5407005087c994282500d814003951840040b50b0b648c0404498094441d902c01c0c0c104440200aa031035865001c07030340c0c00000e0300b0402141030380c00000019140c40014404644241026110041a082e9951410040c01c0c40480c000790040d4042c0150f0b544c901d10f01600310021030b00418070140301940c0010320b8000d144101e812001c03e401c01d03010000601d1221040e00c0c01960414815a950804030100500507680e81e58852400c101 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 763296996 1250 763295746 763295791
    0x5030c220902030d08040606140d020f01050904020d02030108060606070f0803090a0f05030c0f0304052103070c030f06110a0801120f021009050108010f031a1b041503050f 75
    0x9a400d0101503580d00001e480d091034000c40c0c01d052041140074005071000e41003100304005486070030090240650b0040c3c4446505002c01e9604220403001fa101c1c83c240c803281c8889038030440072203510505c060010b6444084800a0001a410a0003182c03003500620000404908251003a41c81d0203030011421441c00d1025100c00c5882c0d44060701109003030041542a41c04a0389040c00b61103441d01c030f9002955200e0038208221b091849001c0c1074202500200400c101c20303540c5180100e0300c840c1007840041c03008000d1038207500d58426039500420394031481e003000051000c4003040390000c80c003418091242e2502c48820348040c0c42000d00321800700700c00f13a0040c05044d05104008401d03034414070150300000c0950700056115002e409104001841000c410300c200d50340410118014419a079075445e0301800c60351809400c4082200c0c0900c48804030340001c4441d44050362a00030003008070001030344d954642e2072810340911100d1038140442c1c14003020401d842c1c407070071100f0303c501150742d110380c091800441b = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 763298246 1250 763296996 763297039
    0x50a150c021306091103090c041506270f051c0f24050a0b03190209010b0a09151d09040c0626100806070c03050a050901030e0610030c05030c 62
    0x42184450b5556404080f500320040e208200c413030b1034100e0240d0745170314118104a1030040340e4030080d4001ea04101440c1213500444518005440c9141800741805010b00110308038000080f490000070480c80100050b813074031507048041911003e5a040030702401d4284031016101d80d1501c01070446032071100b0320003c15903035003c507a03274811205035050300704ca0301044003410703900e00b034607000c1c4103a40d42c0300d4860b401d24007000040700009443d802c2050038046900002c0c0b428205102d203400c0326800254040c0c2082c0b040d6444005016541d200d480d4036500c0c204000e00d486c03103248160b1608030325001c60003113a01d802c81c0000c0c8141e9110705040c034000d00b03101044a4680e00940c180300d150354070040034141080142c03d40391041c4203100b142109a45002ea84038036160000c1c29603400c0c005010320f0708000c00c1d401411100501d10600f07100d82d6900320301004030000d00c43d90300c064002d40078000038072030524600b00d220f90440380501414600e013034440f0101030700c0d605802c580c10b0380514044030401c0302d5003605 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 763299496 1250 763298246 763298269
    0x1504051008071e0e150a0f030201120b011103042c190f0b0a08060f011205150403050d09051c02070f0302011d0909030304061a0f130e010c09050a150c02 67
    0x81c2d404071410b582d241d20990444e14103030f541e142d0841501031683c0c45410100340c00b50050112002101c83c02d4510303000030305158032210182e291581c07180b072a40041e9000d15110a400d444034811242d455503100062140d04101200e8000742103103441408280c6c0d440d00b11024050441c0c0b0481080c283c0040d80200300415565100c0c80d10203403501c1214407140ea03030000240003401c858015105600d004000c0c036a44140c140c0002403030710140003000000c100001075480c010504828180b1003034031a414240d43d2801002c202ca41c6240c1040203900030028082a00c698010942482008062400b60182d8944043e4050350b194241607106c20009523120700a90b01c0d21000454923590642a00b0b8085292040112202d1015074400028001040403074840c410300100500034160301c5900503400981e80081016065200c0d8803150a5201325503201e80c0804000601d440003041202158400981601c02c588540791086108400000f400d99102c0c0796484548001c3d507400b203501203035a08011081c07090 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 763300746 1250 763299496 763299539
    0x3041506031e060e03041523160c0e07051909063207030e100302030408030a022802010c020d0203120726070207030b01080109020d030503090c09150405100807 70
    0x90301120b000c0b003c0c01788001d201900c1c1c0c80f07804e8010705103010b8014000c40c1c0394032601750134070400302e40c0c114443c1d000f030041d0303240c0c00006102200c501025080686261840382c1101e01c10403030100622480380c0d0800d0042c04840a01200c01c140400c008506841701d6a141c032408010600006040b074503a010550704810608004000007600c41051082c04040e4111210880101d45081e10b41509403412586090040c6180d26045d485c44c0f509039680c40c01408084d102000d00740e008a00241d6422038500c0c0c07800714140b42d040c032950101c00b5800c020701030502d06112030f015011302c40031190002e00c08400c85000c01c900040d80211307504c4e0206c04540c03400e030b115840e07010314280809150040480f04072050084880e580280541c07425414014007c42041e4803407001a0325180ca5040142c1320800c6410400d074042c141036803299203003c541410f003803101042503030140c0e41004100d0020f010000b40b4102c0c10041c0c0d070400503603a54194003820820302d0301581c001a0f012800400c50140c0204030b22114001 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 763301996 1250 763300746 763300751
    0x1002030a0c030e030a0c150206160207032409060506090c09030c0f010905030703060b210c01200111070b0702070e19060f1202010f0509060a0c0f0203070b03041506031e06 75
    0x6058031b1b4000305044582080618813001058140f240da410050f15070083e0b44003450150f840920b200103503580d07a11744402054014902c40303800300c000c01560440e1000e0038540e800d010802541c81e15500030402103c2e20b40c417a48005010401c1240a00c05940c4201030141c0200420101c02c0101b01c0c03100400c82110b410082c00383c00100c0c0c5a00e080c4626401580f003120045000700e038800410a00040c070703030780748007a40f00b4518032075400c03e000090041c801700c0c081c00c00301c6000e21224054030444d62494414400c541c201150b185092518100a11034a030207150b00d000300e5164810103d03250021446003840c4050040085945204501d4000f24501480d80d0b0000d051640c1d110030000c0c0c55800c0d4001000c0c050039085003c19541c0003c050582c007401841d007a8541051400010740f01d0140c1d0314040308000950300050308000e1181100b40c0410780080481d0300c207554600c0035980d25881181c040300d01050005000e00010450301078401681c0d03010b8600119034010961900c40441d02000c20b460194 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 763303246 1250 763301996 763302013
    0x90f02070501090b09010b0d080706020c0c04150806010e04050601060f020c0d060915051b07240b01140307120b210d0f02070e010915090606030204051002030a0c030e03 74
    0x840903c5441c0003940714000c400d426140c8144079508503280342c070086000c1c209a0700d4510015000c0000c030fa400c0c40d840000161502c40700e0703040034a021a64046141c00515182031582c450041c0c07403401c0700700e44840f001c460b0b407130781c0721701e201000302c1e000f80d4000340340358020b8005210281c000c420f0010f50680342e0ec101d5082800c8100066410b806604d07050703a540740d0310344020050040511102078404c000840074001e90a0401000d10f0300d0240d44142501300001040354810004038a0221955540c07401061300c0fa0795001e0000d07001019501c80c103e000c02c528002401002043c50140c03840b500c250f4070b551203551030b91a0044050104103032219405203070400058040016402e516950b4003e2a0062a420103074120191209013400004015507210200402c104124112681d0548607004004509481000d50741e109241c1103400c01c90002d4144800481d1061345075010b0070840c0c00c219440da0310b940c10004113a88901c43e044a61001900b8025210007090040c4115402c00e10041c0c02c40c0e1503903 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 763304496 1250 763303246 763303253
    0x6020f03042108070c0306062c090f16051906080a091106190f0201151214120304020109050901080606152a07051504030312020906071505070f09090f0207 68
    0x44d40f00711022545481075010034410b0101c18816a8042c0145c1c2c4506e149032071000d056642101c04032052200391140c07110000e90b0010080c003944021100d954201c0b40d48040c1c0b000c880702444a107005140c05088888004210707540c0050525045451940700ea4035103890b25000540542040ca0003540c480b40e481440c00c0c804e46034240100700c1481310300d000c040c1d01990b500000b4107148041c0410800c40e0f061000d81041030709030005d401c0c02c4070380c0980000d0040090740b07031841f10b080301c034885640240101409500c403281441c00540c41140700341c0e03a55108540300e0042043c0032000b800b8400050b404400000c60b642080c0002c1752020180c0010319042802d00c0d62840320018585090a07200c06462100c10804902040032034082c1500726460240880006500b9650340101d120281c100412032030000408003543d41100c04d00b000c05080c06569100904040c082c5054452800c10b00078600130014003402d110f034882d0740c10000c50313540c0c1e400041d2030214a0710180c50310007103106981c0d41c00c00141000 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 763305746 1250 763304496 763304513
    0x91107050c0d121b0f140c15181302040e040308060301140106031a090108072c0402010c06060906030c170f0606010507020f041a100504030206030627010602031306020f030421 77
    0x25110760052901b2104c0b10a074181060450740200e4006d6049840e80000c0c8080107090703420300072203e0b25040c006009180060b80030401c40da202c01089100180108086a10118052080d400b03510f5000781a11941e090508903140440003c07001c580d24401484141d1103a004142d142001c040c4200260072030200080000c2000e030710120a66200b03000410072810000c81089216420801c0d0210800880700c91a0000320f00a000904200102c5c601c00100b01c0c0300d03405040070f0040d02c10100502901ca103080005042c1d140030340b8500b2040d0102c05e0716080720000c3c4540d82c83c08500003500d1952103030300041d04c0d2a082520200e03441541c0348483d5026403980c0c4224034446098042451000030300c81306011049441019200c10804100003c0c000740c1c0b900703405c03650401e47c241c3c2c0c0481903105000c13aa06004002ea4010201408803900014000d47d0010150074000440007038031034181d41d00e003c242c0c0c0d41c055000d01c40000c5d410a100c10001c0761080350000140004000303c0041d113500c3d0380c0e2240d11 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 763306996 1250 763305746 763305773
    0x16270e130203061f14060306061309020a080601110c011d130f05160801030323070515060a12020d02040509030c07030302010e010b100c1b091107050c0d121b 69
    0x300e05601c1c505803070340c0103204c00700c8024155504052186041d2a020501302d1100030211400345500042052407484460015802043d00000464172440c261070002c0086400795074807030001c0c0c074118410003a0040414100c0041405858180f8851030146011880c42c08001c40b0591103504980c640101003481c1c01400900c109100c40040d1600e8645802203c0800141c0b420003040036040040c00041e4010b003c2140c0c1060400103c2ca48400c6205500502d11601d0001482c9004400009901042c640f074001c2c00303203404071040c81c8202d4503000401d5808425001c080c0d030010b00b80444c44054141680915000040a03085c0c0c0e1501280f6048545000c0c115802140181e64070725100c14001c4083c032544000000440340b04180030380c2090002c100c1c040d0410701811042c1c480745440340b00c0448200724001440201401e0103040b1802140c1c5069421217002901d00340542070001882d40f5181800b00c500d10b51000d100c0441070031705101101d003161042245c40314600d03d40f5012000c04c0d8000345584 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 763308246 1250 763306996 763307011
    0x903030409061508091005090307020d030f080105030102091e06040906080a0308090706050d0b0414010603230c0a200a06020d0c08060a1404021216270e13020306 71
    0x9030303040c502a141e00c0e191410080a804001ca128103105c0c444101241039040040750701d074007240360740342d08040b28190b20424600a51000480b800320080603003082840350441c12584404650341e0340c501c149800d0788118030603140d01c0f80200d110032100d510401110034481c1c1d00905800c0c202a25070000c003048550356004210b15a0019001008145d03105010179400200200904a140c1c500080a45180107881810741c2d2151070303052050b0a512a50300c844841103c41c1070454107540d440e0300140040600c4e0065000d00d03070040b0b41143c03444044001c824040d050343d40309903290a84524044514540e03002580070003804201104902510411048400c18061200180d440042910750422a09808107040c180004141000310543d5a000c0340c604035880c64810300c40b814840d400180003072084080203040c101e41081070210031810400b00151130b004544501202410200742082a02118500800700085010044c00f0b204000d0101a802c044001c1c40003070b00c0112540000d0400e9030031202d20 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 763309352 1106 763308246 763308251
    0x1e050904140711010f0605030a06050c071a0601080108150705030910090f060522020d0602090409060507180b031f0305031c0c052503050903030409 65
    0x8448958011646001d5841c0c4520041c08a203202e2101040d150320f00680354411205c81d120300810f5800c01001448501855a0740f603025050041c40030070b40758424005600000c0810b401d86041e112500014131603460940001082c1c000164003884c0564070512505103440001c0045541188042c60302c107030380c3c0d0b96412106107040002c8030441000391a000c4003c00340480c8c400300d011520711a45051005ea120820001d00400880c08010f10501c680c1617070400602c4c00d24408100c00d8820384001d810920540e002030110b8070029004e8030b420791207900300011140d0184407021501c44002c5509540350414040243c14040100010034003040c840d441061045040c00325402103600c401201d41d52642c03448074000c40548201c1c002c03145070170440b2141d139089c0540d041c0d0b2441041003040242203000c044c40d5900c614060034040e02803020410481d52552400d0bc000d102070702000001 = true := by decide +kernel

theorem cover : BRFrame.Cov 763129496 763309352 := by
  have h0 := BRFrame.cov_init 763129496
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763129496 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763129496 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763129496 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763129496 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763129496 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763129496 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763129496 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763129496 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763129496 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763129496 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763129496 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763129496 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763129496 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763129496 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763129496 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763129496 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763129496 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763129496 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763129496 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763129496 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763129496 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763129496 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763129496 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763129496 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763129496 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763129496 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763129496 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763129496 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763129496 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763129496 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763129496 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763129496 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763129496 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763129496 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763129496 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763129496 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763129496 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763129496 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763129496 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763129496 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763129496 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763129496 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763129496 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763129496 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763129496 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763129496 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763129496 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763129496 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763129496 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763129496 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763129496 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763129496 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763129496 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763129496 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763129496 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763129496 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763129496 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763129496 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763129496 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763129496 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763129496 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763129496 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763129496 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763129496 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763129496 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763129496 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763129496 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763129496 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763129496 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763129496 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763129496 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763129496 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763129496 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763129496 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763129496 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763129496 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763129496 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763129496 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763129496 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763129496 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763129496 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763129496 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763129496 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763129496 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763129496 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763129496 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763129496 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763129496 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763129496 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763129496 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763129496 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763129496 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763129496 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763129496 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763129496 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763129496 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763129496 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763129496 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763129496 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763129496 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763129496 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763129496 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763129496 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763129496 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763129496 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763129496 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763129496 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763129496 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763129496 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763129496 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763129496 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763129496 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763129496 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763129496 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763129496 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763129496 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763129496 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763129496 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763129496 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763129496 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763129496 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763129496 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763129496 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763129496 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763129496 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763129496 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763129496 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763129496 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763129496 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763129496 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763129496 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763129496 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763129496 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763129496 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763129496 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763129496 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763129496 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763129496 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763129496 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763129496 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763129496 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763129496 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763129496 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763129496 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 763129496 ≤ n) (h2 : n < 763309352) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
