-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3265
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:09:14.383432+00:00
-- url     : https://prove2.me/submissions/bb580449-967f-41c0-b203-89869302bf55

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 587050359 ≤ n < 587230215 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 587051609 1250 587050359 587050381
    0x2d151b0a0b01090506011112041d063a0c0e071110020322050109031d030a060b0303090915040c0e1e010504090c120f05040807030c020a03080a0302030f 67
    0x4800000d2451003540014000a482503004c16000401803402d00021210310690305d01c0d100a9450007056000042010088006607038403003603000301da2404403841401d000d03001c500400300c00d0320a40480e0425040c00204c401114200b2100d07010b4210360340040c2c50450a1020001e1080d00a8480301300c8000f0000f04a94000c540004840c00c1e03120040c020710801c0c504100007904050150107010541e00f541c07801c10f07600c803103010264500030700c00045c00d138102c3c0c84e024001c40c0928000c1003e0040c80c1d80b07514125a40454114071081c0c02010100700308602d04001780c2107105036814142d00400e03c1c03003402030f0a1003c00090343d07040802d840401000d07004220079105400e10794003141d84444c011110707002413803003c3c0d200e070003501041c1031050801d0740b20034880c1c0c01d590440c07192000169601c48035400a00c07460003087c0b08800c09a400300040c0c207094039400900d119000010b01806400509402103494401441c0000d6801ca800700d034440e103070b000006002c0d60090791250400009000811505020 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 587052859 1250 587051609 587051623
    0x5010f090503041710020c1516021f090218010303020d0203030f04030f020f030318010605040902030d0513090603030f02010b0a05030712061b02010e060108010204052d151b 76
    0x801c00075400c251410807078449060010135070240500403206918006502400070f0198524820090951000110034035031041c08014420380310020765003240050142c0100356020301d03500c102444c0c0d0041609401a902034400600020b420102e004107440b60a0390340e864841c140c278480c4d0b084c0d80d24200c3c21a0102d90b20b0009072040310014201502060000c0d01480c00007030484032a0054848921100035030f54110b07042181d06080458185181d008019820b10034613001e454207c504210038601500401e03503601d81000303040700748200003815400c040742d100e2042004200c0300d0300074040c29469203002411204c0314003401001d5820182510254600300307845500341c94000d40144102882c00d1141d076840ca154480503504141c1e80e00740300c1800c680f0160b08149205171600003140d000440400d0b20300e4403805038000346c0c0c243d2050009201c1c50b13072208883d490303007c084100034201c0740602c0c11101000301d0004601740d100342942011646202c1410140607031101c0c81d1154400040280c1140d511070031 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 587054109 1250 587052859 587052863
    0x30a0f0305060609010c020415060806150408031204031b0507031a090c01050f2a2a0f130f1d0703081603091a0c21070321090b0405010f09 61
    0x4024400010b295120301191b602581c002000415603484440d55007a95402680110001420310400c100e20780c00d20900c3d0400560039002460b14242c640401103880b8043c4142c40075581d5020300c040340c00e2506c07400035a130a540c03003d00806030a005a01c2d0075540c035040c80c8022100d45411100c003a45085000030828410100c41000d0000001e0000044950703611229a991004105008040e0004120005842c2880680b000321000e0100e00d89807a14041380c0c00003d40328054400c01013080c008490440351510702c0b054072040c2c141c0660000007140712028504403000039141120340a1402c02641004044008100f01c0c40401c2c01a0228240c030380c030aa000240160341c0401042ca0031595500200c03030440c1c001d15142d43c0e01a11000844c00204000d1404034a0010101d50100202c40501003139201c81907484401d142d031004071a02219602409001070240f00701f90120720740d809082e04030040b400c40d01c444200450000740c0f5004070042e100340c900380c2d013641c038140c0300c2c0c1004c01641c03294501140e = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 587055359 1250 587054109 587054119
    0xb0f011205100c02210a021612030e011b03110606091e2805190614010e040906060b071b03021003050907081c021011070206030c09060a030501050316050a090e010b0303070302030a0f030506 83
    0xaa0303901c06407122207000b02f04504100180c604244000e031040050b410303c600c41e940d0144038802c00c8088a2610b0005007070144a081d00005101c503178942040803184600340031001c0c803d240c1d034105240502c10b075211181030901e09070880c0140b44489541c8200e110749140b4109140b110301c50141d9034111100340c01194202c0d01108500c00666005103403151000800800110714440190f459100750345059100c002644c1010078204d0801c0003529880110200180c1c2072189140b0350303000030b8140c800c240c280310240340d03803800499080c00c1e0902110000d000468201c50402c0f1541482d988074819561701780005014080b074104540703505000750182c0700b81c001a02070a0002c00d8080054907032018003c02d9000380200030000302916040d021f40b17521012614005084d600d481c00707150411201e54801400640c0801050003941c0c2c40351141015544499000610390300c4840c045401401c0e24410340d5403510001c5050300070140e00200500c0894120381c0c45840601c04000181c0540303100b521056800 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 587056609 1250 587055359 587055389
    0x50c10050906180c190305030f040609170a081b0d020709110309060a020a05070c0f090506030d020a06020d09170406090506131814040b0f011205100c02210a0216 71
    0x50300c1c01c41801c0c14089103085c1264001c17903480c0c0d02c01d8030716800550b01e401e03408400b0800700401604035140c400205074814020303060221411301d05856a945c0e420050000e10701003400250124019040040c1031045c00c202d841c00c0c521880007135174401c518800c1c006038a050002510f1040309440903240220715080080005842e50b03201071001e90000d07040074040240134040c400216034071800110040c11602c000c013084034100000c40050310802402680280e10180f0014000c0e42d00240030004c01d600710000603122200b20700f4250141c0300041000d4a000b40c10f582078221081000c0062040b1005034680b0b4240d60794030000d000080c0140341c02c89041c54803c030307000c1011286800c201c01c15a141d221000841032120503051000320f030244c50584810014004101c11500403919241c0501200486013202c0710040d07480c6640c803c158146480d400303899034030441d0894020031245181e070b1035281155142c1405030702c050f54160040020200144180c1a09004580d9004003010a90b80b01c4c07039840c810 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 587057859 1250 587056609 587056633
    0x9190e060a03052808040924030b0414010e030a030b0a0609061205102301030b060414132d0606050a14031b04081b090105100f050c1005090618 63
    0x403140c1081c0c0520b08810b58183d5400003a0717240c00410107080703e020005116008001840700f1842c5240d600c80100c100e02034140b001c2070300d110500d6130040d4804a0341c81429910030960380580402001e0340c125100c0890540b01e0f19406401802000c44255030500b10141d4a00c01120801914811600400e030400c036080c84004094226070f0307103e8140030b050741440da92580341c00d070307611b0b00d408942400c0c02d1a003010141315a0716008100c0b0181b002c03201e041c00c0904000009010102c41481c3e42c1c400c800ca10544448131130180c02046c501c0c0c5640c3d80d00d015560340e83c8141107801b4100c00304010910319080001c290240510152680c040c001e03901c41071100200303802d07202c480c0c0c80070b4561080c9202441445c0c000d000218014000342407660081c1c0024a0844031040e05180c01c10031140c482c8100c1401409141c0310300c401c11440005921304403a010407400d2043d1114491083c0305150360050481c001c1c50180f40380c21050003507512504030384440d0340341c421600e0218030360980c8140c1e40e0004030a41d02 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 587059109 1250 587057859 587057893
    0x2072a05010f17010609030213060f0902070302010e010f060f230103090f33110702011b061a0f01170727080d022103070807030209190e060a0305 64
    0x10034555801c250f00e89681e8407168421001d8242c1c060b03000650405400d00c00c5041108841c4050040b40c00306024050510ba0003041d101081d008007420170b42e01041840c00d01d4800d4000f486000f4000e0000c010750b000c07019160340a030030f950040951303c40641030002048295003034015800102202102c402502036001140a404020300680e0740c40c0b41c0a001401003100c041c180d00745000d0030711200b04542c40c0791445554494000700004400e0b490900907040d0683d01104480364146d0911b001404ad0300c8052413040c04424621003d0407152a1000750a07141c209603500b65178440701100c442a4008031b8000444002002050185481c0061004140c00724016006001e8100c0f50b0f04080c1c90046801d42c445125035495440250302e64864001c5500c120307014800c140c542100c8aa007000010b07640e01c80314065110242400007081081400190418800e0741034500b9450000d007044e84207003c0d22403191528101d40103248800c0d5521010400d0b52500c0b0f0172903800c480d032141c003030004d85080c544200 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 587060359 1250 587059109 587059127
    0xa0b0313020a0e0108250302060c0604030801170601050d0501201201050d020f0420070c0e0606030702210405060a080a050c0903070b09031c0c150204180f0e0106060302072a0501 78
    0x10300c6e002e80b4180100050f51803030050003029403010000d055518060034000d2414006078012440da090f141c000c040c2d607410224056041d202c2c10703180d00e02100864074200f4010710071000c0c0160307000b20405a00060455900040c102070080090a20040e601d61307041007001c0015a0000b0b5100c40d65200000c03550906400c1016811060250011000e000410a0076176502c040811591b85003500c0b81800f1007103000340490b412134411341b005030441c508014040d5480392010390000418440c41c21512807255102d00b210b028043c0030b8501501e400c2e420324040d1100c80309492081e615828080050000f03d004000d0b101343c440024010700c5503038506603011100da804500e130240c06025040c000d03840d004000e0b8807412000c26075554201100b009043c11508481054121905540100030030803040c0c2c000e0700c4113a680302ca660000184541d00c207404030010880d282e0030031025420b18400140301905036002c0c1c004d05010314025580041050242001340b10645405904102158814000c9520540c455 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 587061609 1250 587060359 587060413
    0x121510242a11010c020a090e060a0b0906063f070c03021f061a070c0806071d0105090409060e0f0a02061912090804031a07021b0a0b0313020a0e0108 65
    0x1c0000d40291740204003917106030b8101442080d01c5001582e4444030070801ca50340200e1035601004500d4601d40055458032000d00782c64800d0001181c0030300c043c0a0103042c00d2640001c007158082200810000500c0805036030411941c0c0106440001e00e400c0c01850350200c0c0395815405801801d0700341c1c1468485445d141d48518034981d80300c3e004104200d6025002d00360032000c1074003903100c0440e440c01d000496007982100d0510b41142c0c1c28401115004255041554180d00d00c0445400e141d0740101d916018105486500c242825540014000f06034020b6440c01c101c0c00a507040c103403140b0809030b0345032500c00780250400010840041c0302081000b4264000599242c00d09021844003510003c0d85c0800310140c90b0b11800240400411004001440030025800074620311032401c0c940203912842081031100318014010101000c99030b0341c14000010b00b014200032070316410000958040f1929500c0304a0244180da8008204680764020450417244100010b216000241a2420100c4904200 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 587062859 1250 587061609 587061617
    0x1807020a02060c030408070305011401080a03090b0d0b0d030c020f0f0901030b0a0603080408010606090e010b16020f040f060311030102030c0d0b030109060603080711121510242a1101 80
    0x102044003101840081f00941c041c100100f0a2060400690070203032060303000c0c6006610a45080c0000b0381c000d0b01e640f04881c03900c0103c40d26031041c2c3d5045409080c8050140760302030350550314031041540040701801c145000f514000080310f8104240610340041c1c651490b40040780c40010000540c0080c00c0c0780e8481c0c1d4241e030200b2016034035a80e80d038030381d041030f00220110394513403100f401100c0c2d1219511004020039461070b1034a5240026007801c0b44500c510781054170030441d172547c040d511b54611084d03d203040030b441005400180304d03001c00100000c0c04200c503410071030b001503180e5203014020790380124855003003140f6141400410700010200c011580e034065407584214004944107108540c02503014285070b030f6545e01c1f18900307900091015040148282200c00034480180000505844800580659540c3c1e90321743d03100d4802d600c0119804015a1003e503074607086824400b110744052100661604111241102d015127244143d014001c0380098902c401c001c04114a030590940f00750040c10 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 587064109 1250 587062859 587062867
    0x6080a060e0109170a08070504050d02060924130506070b06220c091509150e0a0302041a12010203010522150915060806090601030203101d061807020a02060c03 70
    0x510740304000b00c1c9010130050303240040340400c9440d8104076a45c2d400340032450801e1030b0904200000e1050480518047d026000c0490106490380302c1280404060001d040c400f02c860440d0b592070b084540c4011001d5030301c0348815200140d24180700c810340e10800d40c810f50182d0250750380010b1014204c5202e6071206000c00541c401c8041105902c600702031140b240d9940b1110905103410324a1704124500c03020204443e1810400c00200300000c8503c58002c0d510300310900101c0800040c1d20307000f0356040690f2083c0b41c40000c8800380c2038403140d041005016640e0094a0701708c1c0d05250308038002446002c2d001440d14102c100170b00e182c60354210300803915010010340110055144004584241c211400c11551400040704109500c10407900403d85072921548510704030b80801c0851201070540e605064000c800b180d142102a4075010150603510104204100b034406111003a10301552900d000d00701015402091140000d5010302c40c8843d40c006025518095081c82655800000012003a001c180 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 587065359 1250 587064109 587064113
    0xc06030f0c0712020312130c030321020c0c1507080703050f1606050603060a02070809090a091e111c0b1503010c0c05010e0f0712050a0b070503090d0306080a060e0109 73
    0x43c150a0b2011a55802561501c060340130344114100094441d2001c1002a14444002400740c60190152541890803140c080303506d80a41000186800800c040300f0300101e100340e003801c0005994052a1000c03541d0f8030420500041d044031a01c904000540176000401091000c28015402048005102100c4901e8545281850f442c02c0140d150f0817182c45032603206011840c41c0422000703401080c4050110300c3c0402e1596400d0807449407504541c02800380100103036013400d0301d5008800450b0010034070841400f90324852000c010703041004941c0780402d0030421030300b41044050b4044403104142c0000309a8100d0311541070340e000003410520324054040020300786407030078090759100616640761200261200e1070318a080da80b80303001c100c040b607000c0d007105105070b40001100700c111000380e0b142c200c0783d00141c28140d05000558402908045a004c10f000e07160798000c004520880651082c0d032906903000200b03d05a031418070941c550f542c0301e010b41201082c09540100040c6c003004000040c2c00c12a5 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 587066609 1250 587065359 587065373
    0x3050903120406020306030601150f180515030708070509090103110f04020a02010b0423040209040512040b0301180c12230a0203041203060f120501020d1a10020c06030f0c07 76
    0xb01c0e0203c1e00716802105000107030400b0480c0074050112030200c0222404201c0000b00b4060741c40c00c0000822416120000b400c10781c80c04044042c082c041d0007002c4208005070100681d40c0103644560008211100082901c0d1051041d40c89910004011020f01d1740b031a01c1c5c0c02d5801d4440c042246e880746405c0c00002559407103200030191502e440d0000304a00301c80108000440da02040079a452054000d1050040905450140d6216a0440d111002d40d207a85c24402c0ca07082901e00494140d0301c0000b0040394000400d80518102c0360030a0848101825504c92541a9180080703d00080392448100b0b995080d142d07000b401200061900b8100010752a1800346039100c816035000d5911036001040c8001e2294441401da41415103040902c5035034603080394091610b00707610450a4186244848504010007901180e81d55220346d00c090003803030001c4a000d050014561100b40c4149a0fa0062400c90340c0081106039075040000c044900319900c60105003050748000300751900c6408100080f0000501d1 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 587067859 1250 587066609 587066611
    0x25080f091c08061801051309030210020301030b01171f0c0509090c030a0617030a18170f011a0f0f0105071704030510060e0403030e160e0f0c190305090312 68
    0x45581e00401da082c07072024405094000f00c0080900300002c8010b206e6034850703806d0b66525150040001612128908049040220210000034054000000042401030039900907040c3c410b56203060200010b88080340d942e0741c900180f441d140407003800c0c0304041d920f41640003042c01c00380e0342400d6262141303000003e41030140850b0704a80c0214088140f040c1c1004520681d005800041341050601003446001c3d40c0d42e009150400040250050040803006071418020005280c00e1080c00d41042c1c0e17030a030303203030302c0c1c3c071958911820a618141062008442d40711074180c041e9005401045100c486c102484081e020036010035062100801000d80040d00850000d190301c8030038100d55440d44d040d8900341f0700b00b1507582c0b903021b02d083c00c1c0704051142d10380c7d5424090300154107040005450b0701a0020501b090444013801e80260300d01800018071000303410b542481004c050300520840c1d5100c544554450040488484008003603031140d01540d4040c1e8807268001c0d080000b201e04111484000c42d0710510 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 587069109 1250 587067859 587067913
    0x1504020303130605120603010b010203071e060f090212010c09050f0d1416050a050603010501050c0a21031b020309060711030109080702041b05030a020a0c12020625080f09 75
    0x1000003403c549962480084503081b800440003404401d03010340c0002d60381d0007941e07409001140003503c0c1500c4920341c070249545469001005114000c030155602000305241c0505038061360354000c4040b801401803040d800310100c580c80d22000c050030b013070a01c62072550504426400190110b002c00105480d51180428404068010040244d410840002007200d5510240c060030201e0f005104698580058a05503038082c0b0380507844001040385a403901c5681100a08a150850756040c2c2203048114040e1038649903440502040c0104450841001008892040142c03c2481003d0301840e01d10020076110f4051403211241800050000382114480c00007119138a80002d000300460900303000e00f010307029811841c10420007241a02070b2040c4001441e070030805034000381d50034140d4000e02c51044501c0c1c100814146114440c5801780d6a10000d5960b411000310007003900500c400d12041d0240c1072000c6a80320703003558641c03109052440700e0180034020f0b580031300c11505007040c41a0038401e480da1 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 587070359 1250 587069109 587069117
    0x1905071b0314061512030d0507091a090f040c121406150a0903030f020a051002180d17070c270b0406031a09030412060b01080a020c15040203031306 65
    0x516528096215081c1c0380c800c0c080325041801000b4134490340f495010b000740340613202c0d0b5411030201c2a142c1d00f0343c443c0d0081c80c001a132038981885442984007046005807030701c25594400c0604880c1e0724000300d0090070716082d8040701c00014003034582071130341041d0890455418107480000d810a010790964401c0c8054040b8048004200101d52130141c5a829440182c91095840c040107000c0c02020780804e400003805014030001443c00640c420040000c41c2c5411200b07440b000c90440701c2c00230183d84240b188010f40f24a00071030815a241c207640303002103286e10500003028031034003440544290b08069415604c442e1050f90001d44e0100240703240c000f520802550b003030882c14181215003154006086580103030700c0d0407024400074090385000c2d45000c43c88090b10b00d04c0c0e40e9800b80e0358030314400c2d0741010040720341c945001030401141c0c0e0080e92920b403090300c0303801407039540c444081b0481c0114442c4011603400402100442d2403218201c030741060014007034030b2a0040b0003000288841e45030b8440c40c006 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 587071609 1250 587070359 587070413
    0xe090a09150603020907110319080402030f06060616060f020c1509010c0504030609140d0f0f0201050c041401020a0b090c0102120f041827030305100b190507 69
    0x1c50021a011058140c104080100c141160089007030000000c025600780015510006101c2d141041561041022889080000685c0c4540103102e8101a14202d01070b200d1202c00790b100001c049140c034842d04000c0d10321800d00314119060005c0035a413180907281d95070340303d4601e01110840e0004010740c1000500500368031590a40004030040000c2044507039034900001c0022061344202100c0440b90130003404204400e26003031201e201030490051580a1098450707410200d50403003c00c1480e840c2c2c5458079130f841c24000c03009a081c1c850486038034050940800c410300403800000c2c43d84442840610480301c02078903660b90200300080c191030003211580103005042903581d04010000d405a074283e1124180b6898016810340e5000364020b013a81c0a0305c032554203161007000d03404080030b0401d11510078600d008070a10100c1d0003e1a01056000904200000742c041c10b40c80c210008850326201418034080310403a0140483d14004842c004105040150301c0100d1070202020140254080b036480304 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 587072859 1250 587071609 587071613
    0x13031b05130606020d0309050304051804030809070e07140d061e0648030518121506010504031a16020613110d02210106050409020a05060a0e090a09 65
    0x149603829900101900d003802c07424032201d6408525812041c607241804203442c4064905241103000300c0d001a0382240320300c0400501021583d91450081e400307512109001e41301c090240f501c030301441c003441e0044140d680c0841e00191060310b603000d00c41c40154101d800c000d081e00e400300a80e0031a6100c00104500342c0405c54001c50010307003800040141d41082d502150315201c2101041c015410b000100c400e108459820f074800ba070440e02c038003141100321110410401d18001c0c02c1038210b0900c41c0d01c003481540d002e0310139081c042c1c00403840e441c2680080a030710007071100c01d0707408030002001241000b0017030000100103840c0b01081404403444c42d80381100d07481c001440741050003820844200b1588100c0a02007019620342c960b400103074000103e2200c610034280403503011803050070000d4202d07600058a6844141c0c0220030842003046038000e204696890040000341e0722442d10181d03000e00d00c03c50403c05803601c040103003804941820502038181100c00040e256a00880342c1d0b48100f80c4030040c10341 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 587074109 1250 587072859 587072869
    0xa080d091a0909012903041208070305060d020d141905010b091e0721020702030c01090501022e06120b010b04030f0b060102010b040617060a020a0e0613031b05 70
    0x20307106030108012401d140400300024284074045c0304101c04130984100102441d501d800040b000410304c070304000d9680c101071a01c6c422031040611060002081440821101032107030280d5070040344020403041610f14141c08114400d1424881110032040c0c1c414148200034040c0119500c07281d44628940e41803819003006420b5481c1410110310903540721040105440c00080d0303495002d0501c04004000b030f030b50315070140d8408000d14080110494201544030348000180c0044c20568403c0d0180c4400c40480001940d4101c0107008250151300000c1503024441210301c00d001203204010001918582c0f9042d059048640c40e070446800001c8180200042c815103040d16070052160080040c50700e481c545030040d202c0c84001000b00a40e0074074011030320583c400d40100407000c10050003044481e55514254040300342aa00ca541d1900401c000a11000441d00c01e84d080313082c0c20307181c524000c000141008880c0e40206100e0503048103003480440898040041066210141e21840300010304180c2000 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 587075359 1250 587074109 587074139
    0x10305011703040b1b06010e160201050606090d06153002010e040c0201140a0b010908031201050d050709050106050a120207030e040b0109081203041205071e020a080d09 74
    0x1d0600d00001031024100c4400001ca030201ea80441285031980541103c4155119a180c1c0551091140e4030001c5200d101e910701480c002c11200203206074980000800364242d51003140d100c0d501c000c0510041001c0d082441203500781e83e1241900250548407c070141c41c550505070800620300c1003034500e01d0b140c421541c8203000c50040101071130b1442c001ca940000e0440813118041400742e03840324190000d150003500002e070a82090411980d0718a05902e21200030b00c507001605000030182d4800040100000c000c85101e001c1400316005d80768240014405804404581102c051041c00e800054402c964400c0c107020b02130a0741c2d002d0b0380307002d0782c140200300d03464009036000881e104100f0900000d4000040680501043d20041000074443c801a00c440b401c65120b544240112107142c42d0311050301d4000c5115511a203141620140b4108048a940c011034800405000d4140b9048171020100b40e072192005d032004282c0b0484503202c403506400c0c585001c400d000862a400028089003d25030418 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 587076609 1250 587075359 587075369
    0x5061609080a080708160f0302101a090417030a0605150a0507060e010e0a0f15060317030603010b101701061e0309080c0d080a11040b040b09210c01030501 68
    0xc00401428100c409072220800440244200c81c005014000c000d0b10350309494010250090100c81010b160803d60300d100c604090807401070107200c6581b41c0d03c403e0340c0310748402c0c11020b0081c00741002d10032050001462001d8800c0c0e804241440c504068125003900441c800e4001c0200450706030316240c203204403a20780091202a0300030520028001a9100080d2241190031050128000b0040f603451401403045404800f9140105d041060a110041c8628484184a84819400760074810014000c881c814000180540e490840c0441e0001e0640040d51b04a1002400010602c1400c0c0005440303800782442040896410700f504c018101c8000d4500c0e004280d035081101001c500f0382d001004214990344e4031000d00d903a40c40d8042c18030180c0e000340c950044041d421070701101c7c01c3d118090400d103000c13681c03c041d5904007040805903210381000c0d5001c03150b000d0100d90400c2d041400c410b0480e045043d420340c20451a400312504916110650802c0c5294800a4003469542c10001002d07a4816000 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 587077859 1250 587076609 587076617
    0x302030c0304030516080406020a0314090a1703040e010e040b070e010f031109090f250c200301050a0204081e0a0b061201020d061701090209010302090907080a050616 73
    0x200304a90344020112a4850b43c03610b03119070f90718003120b8807006103034000c0c20181620034007240108642d03800203207c020890094941140100500045a010348111a006504985604002c11030400c02c0e1750031070310401d83c60054070300345502e500e2540d11303501c82640030304046081d279420301080c0009000c442d031b0003043c94038012a03d03403580c10010b02480803055080b030070140e50700342e00a8014895016203003000402800010582030828403405000b5050b00c4a000c01c503528001c000011900c2d040b03529106c002621107102c2c3c4072240d11049040e0005100320783ca1240d811062140c243c0e020701c2040d02c0307181c4e0484010303200e608100ca0720b403800a90180c10400000c1d0004a41562400003400071910f691107040100b840d0b8602c4007140e600d82004d041113070158000714036075900c10840d0700441e0036030b00030100d16114500003401d0f0740d0076034200a802a42240d10303440188094100220110ba0146800b8110f03008240d48140382d03894001220310617916604040180041c1039080307a00c40900205034a0 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 587079109 1250 587077859 587077861
    0x40921050406120213051905030114100f060819061e0303090b0708120705161a1014010807020717010207020f090c0d02210117061f060c02121f050106030203 69
    0x20b205c030102d2081d4091244248410300a07a0722013084140607501403c00a0028003641307003001e000b0a4901004e03200400117011003a00450103e440c0702449080307501c156120202a11202d03401c01000302d5405100105507102d0301c02181c541c000c1807000401e080741d0380100445524605006144010315040342314072400c10847c0c1c43c0071410080c01c1c0c0300304980c800310000d0252035000c0c0c00d90310f034418128662400d00900c0740c04c205102080b10b1030503040100140c401105d5440244e1000515040c0c0500d0107000c3c0042c10794409544605012503110210b401141e0899466441480c600780040c2442c10b541e83d0001610030850401e540c402c0050300080da1031803031905042c01d51403894010a07c00d08031071507020801c800309444400c9048490b0654001c003081c1c55844101025a0b0b076085441c220480c03180c035000c00c00300c550704410800742101d441104540c090134000c00b01e603220a801e2061b644002c46040d0850164818440f800010162100c8140030b205854062019941c05078803010a2600c140 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 587080359 1250 587079109 587079127
    0xe010c05073516050c1c110d0f08040f060f0c0f230c01180b070206070609082a0c0307210602030a020304120207230d0b01090e0c0901080304050409210504061202 71
    0x444401c6c01940d004406055007074001010480000064038040c001d080c12405082c00d02404000400c04d5409105c0c2d205850f5484010555010711000071043c0014510359500010a98a6458100240c130500e07007550420031000c1c2c0e180800c0d44014540d1758503080400c0b8400c00f90b800104a01c203042603502041a580c1c541802d582440c060b405001c0e004c1c2c000002c0746400c106407030f400071510701c5e8003112240d107980c48107072004581d0031a00a02d0301c581202d1403042280401c001181001c10100600421805041031150700901c422a05504180503c00d910b44002036403600196101c0d658805005807a442c1c24140001e02001605042c000d40d04845401d1010200594660811810078689850642444800300d041e4040060f000303410b00c0c55035030000c0b8a1311001e1708000030f400c1503141141c0041c1c3c040d030104000b80400303109840d1213500c204420095030810360081e0280034090391003000f4001c094041c0800607800418441d0000c1d000244c203022903500051040d050860b452021804c0558071 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 587081609 1250 587080359 587080399
    0x30607050415090e04060507050d11120618040602090d0c082407020d0e06070209070804060605030c0102030405090a0902090115080a050720010b03010c030e010c05073516050c 77
    0x64001b5000742c0d11800001c260b54000c1040703501040000f003040002c1550700c400990a904a0441600709418040109100e0b20700140d5440d04203108840008441d1290740d00e1000a501c0541115042015a0008408241c042e262000102802070182c600300c42d4800c00d0800030400f040307056110044840510094544c00a102d80b18245141461141000302c42c000807814055072078020350000b800e8040103d020742c030090030760040e4420381d4280546a00c034010503849207550482103005a01c140020822490003203c0030f60003460051b80000c60000c26004140c1440098000011a061466102c25401e40c0f00b4211540140c0085041101d418018070043c0100c840c42c159800d404042042c40c0001903080d03001d0403135150020004c2007411441400640a0f1400f204010110351a040340700f00c03040c2c0100201c843d500e1384800c4d00c1119642040d0003140003035030071304e00c40a120000b524800030717669030300000e100400f02030801000048180c9401441c0002c40a45140100c3c080d1000c09a42c04031 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 587082859 1250 587081609 587081611
    0x822091815020307120e070308040915090605011407150905060403020d0206040b06090709081e070803030403020d0804060209040501060e0306420301050c311a0702030607050415090e 80
    0x240d00e60100d1050285c6c15480d00d01481500068012500001c00007542082c0303a102d8250140480402c2c48425520307030700e85003140c007035200722030203c0c0485041026100d811b0008040c503510642818a041114906401c21140d400204403101c0d40b0a03010300050540401a4842aa4051006103007901e0240d0f02d0360101d11020b00b0041c001d11420022500090085008001908183c003c40e11502c0640c0d00c01036981006141c0c1404038050407102041d000d401004492107560160000c100e00e44490703a003220b040c0001841952941e9080c01004e603155254040c69000302000c2e6210101032780030400709820a03c02500d101403400b082c001c0d00c144102445010a6400304a03482120703456020604d000141d1000804558154030303043c10040740c48560350140c082d5100045044464101c82845400c900c2e83c4001c020207a803e83c01d50800c88400400107a61040b80444100d50400d0300b558040b9180031740546807100810401f141c240251f014110001c00e07406107901c1c04c0b45c60b4500d40b40404641c880 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 587084109 1250 587082859 587082887
    0x15180405060d05060f01050f030a080f03090a050109050706090816150c0c120302060f090601091e0c080103021201020f0f0d14010303090f0603090822091815020307 72
    0x5280c00005005540e1461404981c03500007066407031a00d0100150344000303609019051047e1200700d017034071803402c0000e03100009a603c43d100500d8103420342500c40307054200800d0140188210103071900082d03802e0160303c924a1280d00104506800c0107006854103220f904160615800350700110042148022000100c5800b20a40004103d00c1201142c25a0081ca0007811050350346800188018480380030b072281a00030b40c207648040d196140c00b1640403006450442640e0302000040c0a544143d6001c514820415503500100c0c5400c0d032404803e0b202101d54000104003520010419810000390740e99504040000851810310705110546240c0202100c5003845c440c045007060709101c0139400301c1d40c00100c1071001079507981c0da46001403074508140500303c0c003c0b01411000074030300e01070b01400c151a980221104d09205070303401c0721400c0302c802030402013120178003240014405101c1c0c400c0c0703d80c80040d680b404050096034200b4003040c8081d00c11645000f441001000041540203030001c25400b = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 587085359 1250 587084109 587084111
    0x60f090406091406011419021b040c1e02030403140319090503070b090a0e042102120a0804050c060d0606020105060f0a030b07020703080d0902040e0c01050a0e12030a090302151804 79
    0x7000706c0c40c03400c0e80c080e07002100c4884100e10b14110045030002401516041c5540203c6000e0800e4000c1c00706503401460300c00c0c089030680719584c42214009080882c0e040d55481102d082903500d0b00d40400b02880011070201540000074681c0a0400d00b182c0d00c074140b800d82c00c040700d07200e10700350101756109040c0c4540c0000803404504c521480ea034614104c070040c1003000c1e200710181010704265008074219290701181000700342c2c0c20a00d89001141c032510700321094060381c2c00d06420184c140c0361140018002c42c1d0600443c00301c80825543c14010f0100441c0071800002c0c11401c0a0b0003908541c1c02400c01d62081c0410072a603012603803035030400e0050302e40c8680c3c5010a9220544d00342e14100883c0c0000b0248a80407491000c48481035100c004410b008035000c0c002c58140076104d58a50f4266102540000d40c10000402100d0090084e030b0b54100000e0304059240014003031180c11358000307450710300009900c000700f00103520f4981080c0741d00815201c2d249240c507140103186441200c00840081c00750b = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 587086609 1250 587085359 587085377
    0x11118010201060503010614090f070e1219052d07210807081e210621030307090e010605090114040e1906140612060f060f09040609140601 61
    0x99100f0b4210b00002e000103402400002d49030062422030402070000f0394007070700ca00070004004005044000e13024030701ea40c40720007004919005103c80111845202110751040c00e6040440f0164210b4000300c050140000d446d02820220780c136814500202012841903241881400c0b80c4000803800700201c81c02e16400f032219040c0e40025422a0784d203010f000d41982e4010450360207102e4400014800411241c503425078501a0481804581c050822000e15074019401c000d8908420441c0c01074101c500146483e480032084140000b2440c020011084150008418403100395044900d000c0030307000c00b5560b080300d903040450041080c000d000c66641000f0203000350400f800080c0c011503000e084441c2804500f86072484224005001e400c0c0034000641c585400050700000c401e140c2807010760300801c7d00e86084614058501d0a520281000f0f9001d01c4000b40c00300c85070707114402010204940c01c2c8441c1c0f00d8500c41c04000464005904c184c2c00340741002030302003014110445441d4040030274281a549 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 587087859 1250 587086609 587086657
    0x905030c06091f050c1e0a0b04080c030406031409010b01050703081009110c060a05190e070e0f070314060a0303031812020106050915101b0b0a06080f0111 68
    0x10852000b405040c040496a000c6000c0c143d104c030041c20850b030038030221120b01d03a841131040115080f00c80144003035004800f4a20000d402c0c0a02c1680150080300154145035048040318110790042d0700c4040800d9840000e8000591032001c02c40c0e0180301003000308646505580040c2c510f02c24920000e0070003010710005800d5450583e5201f01801c00c42c84104092010b40c04000c00c207074012941c02c0d0203441002e0005030545014011244201c04060700115415400308402c0090454280e10b80c00318010312001240c071039500840d092140c81e41c4003004500d0305010707002400b00e0b2000380c04202080d4843c420000c2c075895a0b10207008503549840c00041d10301351141503c0c89690301e19001000b500c0754803071a0100c254150400c2007564000c0380c0301501c0381c940303c0c4101c14040d0400c0301103800c4903a42810381c0c481806900d1101114110350307490500301125a42d181f031100f03011110603032503a80d120414800d0301d004000002e11084880003c0049610009652840303000f8201d0394124040e04450000d8 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 587089109 1250 587087859 587087869
    0x50612030306061c1a042a03020903070e0708010e0c03131514090106060201151404150e190c2f0708150901052a070606080604030809010c0905030c0609 67
    0x4c44c103c0d80740000c2081d104503a91540c0c1800849403400c2c030541c01c0a50b12014101c40a0840c1100a0782401d00a0400c1074100c0c10b4029402c00c05809515000741c044c0003c0b000c10401146200381059512050b003036042820190010314041e109021244051041000301d803000c42820315005e07081001151002823406210000e414074045414640b0030507800c2c01984141500068141c82180d0001c1c40542140c060540f1001c0e800d1051800741140c420b0503980c00e0915034004002d20406080ba800352540350710801e50458000c3c2d0364103c6000d825840c220665445114a03555130149142c54075a080414080107203420070300d1554480c82034000c2643c880301d1010018940140100000d590320507013001c0c600001ca5070215000c890650800c40021a041a5800a0540784100c10700101d60f20210851860281c3c00081003151450303610003010400c801c5c20020790307100e144241d40d601c1191400381d0380135080d0340301000e5400500c150441f046c880303980d000c591a1031504081c0c0395a6101e50600001403 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 587090359 1250 587089109 587089147
    0xf0d140306060d0e010e0601080d0507080d02190905100f2f10061a04060215100f12122303040f06020a0c03020c030703080a0503040501090c1805061203030606 70
    0x196015281401080c2c8604046d00100881c59a1100b540d106030303654036096454001139542c4e00009030f020070941c0d00140050000e86010f601110006041c003240d00d040d184d05013008815a004220081020400c51030072982640d601015803030401c46620300c00342c000e07007502910860b40c414594004401d0f0707241584940c047e031140641c0000c4503100626640300b030009015600441d10b00c046580003521604000004440c11110b403503000f030182c4000e0300454003110401901d400b40c610366000c400a45180c160303a107580540403a039880460701c840c80c50203019000c5940070745420f0040f0b01c0e41000e40b4a510441041480d8a81202103659540c1c1c4e107007841000b0550328004101d20304c081410700310190b21030701e01c49009100790221b50311841301e10205556a01144070041201360108000e58040d80300e500a0340e0011300c60310010446200070781d2084280070380c54206940c01400700c00007054000031400307015000311040d203500d2764140740c00001d80d4903880000c200c180504000074507c000745921402e50 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 587091609 1250 587090359 587090377
    0xd022205100305010b0402093a06020a020f06220302010b0a0e19020f09012706050c01060f03050d0503070525020f0f09010e1315020c0f0d14030606 65
    0x20026494009071041d1001c1d11404103860641c40c002a410343c508062080ba511840018410071084c94000800010742c0030303141c0c82d0031600204000b440c19428500c0790340c214061140c036001d40c80301c1155034001c0c54243c0c0011116503a9015070f06004600041050b0007514001088900c1140368580c00c05a0240682c0c1315134a0300100301c0c04c000a20100c05820b60742c051046803461000d0014504000002d03800b5144080103604010484a050741d806400b11004103a000400c0103183c1c9001e81040b1f14501c1e50703078411000b0400000d4a00e4910a0a1054001500000516201c030301c0c15038641c01d9440700114141e0040c0040003000c10421030060003981e0111a45e444030030000c0d13030310f00a0610f1a070204801203020b003041d950728185038580307000501c075450b0001d88440300903841e200d43e1480412000e42003030300d11b49682c1c04420102d0303050958204500303070aa401590701c20200c0c0800c1c0c41e044c039a00820f181b0390000b9903801039550b40410400d40c440c10042040e5200d407a00d030001046031080c0601 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 587092859 1250 587091609 587091611
    0x90307060c020d0e04050939030a0809040504150e06180d0206040602220f08100612020f01030b040c0e0a0609031e051002030103050a03170c0d0e01020c0a0309081b0d0222 75
    0x9020790350740c0c420123141d5010014440b260032140d0b11024036a480d40b48620041545c0014000c3c00046e040944c42250f0250240340c0c01c4140140700604e8408030f41d15146400b401d600100704204803081408012501010010002e244010654200035141c00c0064030040c00f80f6000125012103034141d0f0380c0070440070031036401e9440c0c59540c0c10403c4c0141100344178040f040d014101c3c902841103113500c100300c222103a028420009509076400c00c903800542184403410314bd903602e21003880e82ca69126604903a15551182810b9000301d208100c1343c0c842035406282045008402440010312201c1d03d20401d01c40785506844210513440e04c0c50600c0b00c10150b2700c100a10200c00082401400150b000c04640241c0355042d040d040300c0714054440360b084400d5034861900f007001c0c480d0440160f00215a00311140001401c1100301c4c0461030800e1007808094000034401482441481c2d17092050007190452000301901412a07031022800807010b51801034450040811901000c21400c40c000b4407840c0e0f8108 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 587094109 1250 587092859 587092903
    0x90d0509061206030c2d060a0c02010f140d020a0809060903040317160c050405340903020307090b090901050601020c01110a150203190608030702091b03090307060c020d0e040509 78
    0x59540c007551400c038442c44061102e50821b6805e0500c00c481e2614441d95600c44024015001503420b41d10424080040200c98041f22f070b440e00003400680403180f68802d0141c1d9a440c8890010f002d07140c003078000d0101d038001c0014045034450001c01c940447ea409801d0815840d59042049180c4c02610000000c0c4c21440c100d090070441c14114420945204aa04025517280c81c41da0b880c02440c3c42c2c0301a02a044900001210358031100f801da00c05048030304d00b64659640301e0340400c0c00c145155000118440c0c540d18042c0c03031071030040a00f5030700840003402000146030040000b545c40c03944007126810b000540c8132141908105000e4013001035003086d4810f032311002626000d40254811038500341e6404c2040c10012209015011709002c03502a140191b0800b6032a400700001c200d00031303050680d8101c402036084401e4a5060103144502d64030009140c4808550815401f81d94904420400315002000801170007a009030340e0402c82981950005410b5482c00b07025454199032918010289030a00 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 587095359 1250 587094109 587094139
    0x207030b07080106030e1626011103010f05062814030906010510110c060d02210703150e0703090309051e040c0801150e0303040f030605090d0509061206030c 69
    0xb242d40c102c500550341005132075400d03116140c07035020f010424100b12000000c100324001111104500f0401c6001001002c81d070401030081c00c41d003610070207170180f03000400100a0203251020b09801003005565282c508501c407480008203005402c0290303040c0c0c09500a5205a52141100000341d2004520040d03880c200908815980c1e10709100c1c20744540031403503929400038401e030009402c10400d68000e0004140c00d00412071a0380003031054924039a800d121061034124040032070f10081d900c0088910050400345002410b860f0388203000420600010307010012400d0404d40315602010394500003655402074039003112001000d500913a03215800c0e0301004100c90b18403541c41c40d030700000c540801a1610f0038009540404c002d01c82c031707000046104200e1011a00503a28200310840c010280c901c6c2546400b404a41a0a242c209030341d032942c1c0741d040214100c3d0400c02030340c100940c0e0501c5802d10003204d00181c00c901c40d11600900d0121003c010580d281c80810a0009614008204d02c401403008 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 587096609 1250 587095359 587095367
    0xb0d110f0310061103091c020303040b03011a160206071103060901140a0c0903170c12040303170c0405040f0906090528020d0f03050d05010311040e2b0207030b07 71
    0x30b0b1400848002d1100d00011031600a8058841c0b0841d104040c5042c5400202002848000300ca60402465400141c40c1c0040c0c0e000c0c8014005026220072440d1207505240480c1c06c0d00c424101107003c03690040110380d801121040b025041103034100c44c003d545e80024908001d00d914082c0705642c040c4112000e110f070104040d0007809650040807403c0c9c0460f501d01500d20240c848075000710000c9884124140040303800d4207450524046802c401c00c0ca80048a40d1051600c12214035440303d110010509004041d4807559680151807080c50880f100d00b02407406500c075205501c101031040d591150000060b00300f82e0008003c40c4c0e00440c0800801d2014103155449601000070001e00d21f000490b60041000d0040252010359005811401c0b58a6030303694556001182e000140c0c01d001007032250213170064040c0901c501952141c1904822047c5460510088d61040c0c502c102c030130380154140d2040b05480c00d4040354002d9030000a14a0194101410b0b400c000c6181c101810f01001c00041180385500 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 587097859 1250 587096609 587096611
    0x2030d0e0c01030b010c0209040206160b040309050a120b01050906040908040b03040209010e041203050c22090609111602010e3106060f080601030e0a230102030c040b0d110f03 77
    0xc20f8030b081c00310104881c01110000f02032440251700441440102d809420460080c00c02c40880040001d12000b01d0780b10300d480210b003281c0c214001400740c44207018a0800b04840c030024403c11a41300050b010076900c94214000500410b409001c00a0001e80107035a41d40100d0b8403c2e4200c01040c0d9101e880300e680503140d81c0700311b8003a07002e0b0300890000180e0b96a07045c1030340d10450304803442c50701910103c001117000e42400362032400304620a10980105402c1c900508020b440b01604000c115403501800005072001a03000034181172401c3c1100511000120444085848207100c0d00344a580340d00c01a2511035040c801039801c6402002c0d50608501c05103402c1401401400001110300c01401580301600c659005400025130b21125100e43d00703004003d032541040e4141004100c1480158895250a0030038605481148100c12201481440400c4125410030000d0084d85107190011207005c16100741e00ca815814040012045981003859110711201e440011000760b440519040500e200d803c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 587099109 1250 587097859 587097883
    0x8070509010605120133110d02010c090501050c0a080f03040309080d0f0309060609050c0711180103020d050f031b15100b0d0e191412040e060102030d0e 67
    0x409000850340c24024030644d42c282c0001c01c1c140c5816820300b2556007020b1440d64142d00f000415030381100c1c04902da040d0081d61070000c4ea4905003980c2040000c1c500d00640240010150b924208080d201c0c580c0c8254102d0a9a801b03090082ea1144840c1100385803107440c1101034540c400c00726000c03600c018414015400b6a009585000c00141c546503560780707070a00d016017580410a12155200c423980260010000039004a5001440e80c0e27072440c008003030f60b83c01c41d1460424030380000c1300c104001c03403140102d81c04881034500c1c610f40d82c1b03556160882e03100103010107072245104032041c100b0060208100d8141c50240340980762079425201395540c0c0c081d001422803a41d0b0040d07a40d4208c25031003070141c0511400c00b4140441000c1d2400402a88552050f0b900010080c2ca40e4543c40002008201f001c030003009040d01c001030042181040784450b00038451318400303500a500c10400d40400902554241d070314520130301140e43c0b42c2d140140d01c1d6100d0411030701a0b141c100890b0500c10303c00440c500c003140c8 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 587100359 1250 587099109 587099119
    0x30610021606111e0316030e0409060203010f0e0c04050402030c190507020109140d1b091e060503031804021b190605100b071b1701020304031b0807030e01090f080705 73
    0x40f44d2101808120004280c1c0207099801030000c1070440355040c4442084600030700349400e41400ca900441d0582e1f000007800d0300c0750754002004003c1c030b4003284105401002041203540f0182010b0645410501c41e40c400c0a2240341c011000c00e060366010001c865104090040762040802100c002410300d410988080c0d0200328403500008401d03481400320540c2582c010300c0c64030000380030f954804070f1480810601e00b030310a20600102e4031b4106440fa0501c51001c819031917044a8808da141820303240240c2085000c0d80091005032104992031294001c0ca0030201c90240e11a040d04480c45401078116401080600c510341e200d034050400c80441c2c0a90a000d1502070029548440e03c8a06000b158480c0c2c40c4490b50800010000c00d00c0410045030121045040c10380f5250f4862040c081e25101918000c07241c1d500001b4801090741068162180070760320b00c80e0b010000000d40703032541e450084030b50203030900021084202660307104422680241005030f41c04c2c1100741e2100c100d1507952242c1d0040ca8003503 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 587101609 1250 587100359 587100373
    0xf0f0c0b041d0a0e190507080f030309010c0309030813020301020f0325090f061808030a0914010f050f090a03060507090e1302061e040b07060f1d0303061002160611 72
    0x43d8600d000301c60300207a0482c020120100010031300101c1d607009030415141401100c0d030101d08200c0030b01400144607540030044ac1c4908001c280e45007100c0101e8904014980703030141c01e0b40041d4010207a1030b840501c54031008506c2da0f1600100780a0322503400301000140001003007005000040d2070b8200c0c2c501100c5800c0410302c05403003094034925054091001c0e42440342d0401c204d1540300f140c2d6822594100800306a80e1503448211700d2560b00410042c40c04212030030014840d90a4400064141220910b800c0807501205040a07001c0e1081551480a00000064201e080d4686000c11f071b00540c0c0c0400d08118a00d40150700401c1001e10340541031a02c4a61004110050720000f00d00031259001400b662500c4a0a1102d008000350000780c004000d0003403000051549216001d0024107002d40d0700032403800748008480d000c99001c64028800014041135070715190000109480c0c0c0310300150341e240001010348400b686850b10541d8030501e0030011034008280c81da4003002141c034103840c0c8000c40d060 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 587102859 1250 587101609 587101621
    0xf02030d03051806101509030f0507080f0c01080117030903070303120c050711010828020a0908030a021509030d020301140f03030c06072a03030614030106030f0f0c0b041d 75
    0xc984081c1c0341041710062482c82488000d0348502003480d040030504004013915a255100c071451402102c0507910be400c080001c0202c030710140162460407042c0c1c0c001d801c400c040200060400e902c180074a51010040c0121858a2203040080343c0080341e0042c215041907a603450002d10b84a404a01042403030f0402c001c41d03028502980036105850340c000e403c1c0702001040b100450712403100401c030213604901542d800305c030800c1d6080800302c81c100000d009a0f0301c11140754041c20800340c50b803001041e03a20030031600c18580d50116102e4198500d5801e80c00d09615080c1d1091700d10302801000307103003040c40040009010523401030b032403445074020388201c189002c1080416459002c0d04c144809582c1007513001940291141d807140d5110b43d541074070442c0e1801c0801c4104501c20000400302c000c242c1d940400d0089160400d1000d080f0407007280240320300b44c03c6644144c400300b0741e6440140341500e003207144001c0205801461024101541b01d06840d03507034498204184220a1052103481c01e030701804950 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 587104109 1250 587102859 587102863
    0x90106060311220b03070c05190203060a1a040606020f16030309180f020a0512010b03060d080306121f05130206030c18030d03090b0a0e06130f02030d030518 69
    0x210b1010309141da581802001000341d0203403404000040d090b20340718407003c9007444000700690300464071a0f0b40d4406055482c9041d51400e03003a003000005c001055820000181d500017400c0f6401035174004081092142400041d00500394076404d658094205034001c02d05550004583c070000700440100d41d680c941da22403120000c501c1d800040c0026103821800e2040203001404080d5040482c6000202509036130181000c9030840b0100800040000601074004035450071210b026010030300e852441c43c00c0400005103101200d48000300b82c01004400250250350760600c3c20300c2d2001000c1075451a001c440c29188010701044802002c0510f0b04000c034001038403198040c0c03c3c155024145d41c0c51515221001c0885802c9440700d620002100000d4901c1900d0510074491911020b860110b951049854010b0610364014113400d581450501b48150a0200050003034100d141010211100041e030700385403502c1c101002000e9010300c1404c1400a40c030b54164040d5104885046050010785205034001e9 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 587105359 1250 587104109 587104121
    0x30c151302060f04150903021314060d020a0f060203190206010f0605030603160e0a110903030403140a0b01420513080f0c2803030e1302030a050901060603 68
    0x2620900c801010001810150b000341061054030101074106a950b140c0588074210840b00d050004050761000c10460034241c15080c40d8100045080c07000345003884070b4800d071020040013140310b1009002940d05544560100d24050710402c0302c0c00c890031f901c0d054082d5036544500201c910b0001c040401e4202c1600c0032903154142c51118100e034000629140044401c0e41000e400729900d4001c20041c10030327250600d060900101140c03080704102c3d10302120120225903c492010304c00e01e10801040780c40d42d0f0003104131002c2d079900540300c178a4000ca0740c0318645410801d080007440008220004a20145402c241c0701c0301800c07601c6801010589200003028180905030700301c00320307030322200c0e5191420301a001602d202c41014a804a2860352002540e140134074041120300310f50425a0f40740c9050a080c00340d83e415140ca4071100ba845110140c4255000132140701c0901003000d1950076070a40c0d9112a181c2c00c581409a60079505c1c0c1c140300100c4001000e01340d407110402e43c64181c000803081c3c041d0042e0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 587106609 1250 587105359 587105371
    0x61e021902070609061e050d0c0c0b06010e0f6307030b152b022104020607060c1d10090506070c0509010821070c03140a05010c02030c15 60
    0x841051000e8003070f0315141403006c990801c280300080c01510202c6020f48a42d00e82181d403544c0b40d907100f0070103050140003550090b280604115841001462a455481c1d0110342150b09a4500c21a001c40c0c446000600c120071500c005603809a40b80c1580644444500264071040304551030918080c0e020b403010306248070071a40700304c1d0070800c0002d811140294454080d000001d4560541094100d086a20a40c80075009200ba00038558851211100900240400c06d4520008503d0038001744419550580c100ea03001c01c10511940002e0115280c1034265000c880d80079100344410045103038041c000b04d60041764101d110101a482c840146089010120000c07455156051138a06010a2000a9001c401c0540d0364980710840080d1544845c0004e82c02054180d01030151510b107001040c0e4030309000740c0070404100702400742d4004900000900400c803507001c00f4024034040b012810710b040402c030032000340c1954a486902c941d04c039000302c0241041c01500054450300c07614200d000c50528815188 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 587107859 1250 587106609 587106617
    0x7270606080c09040603120306081209031c0207180c081e1303110f0304080f0a080405010c1401060806090d02060f04030c0c09050901060501090602010203040f061e02190207060906 79
    0x410102d0062100070701041c0e030f016102045a81d20b94403104031040407440c0c05000a80d0b160720821102e0024452a40c25140b4044854605105c0c00000b03951079542d41c3d060800c030090140030b15200b9008115103c010102160b004510681060f190401842005142000b00e40300800058800199203080c0381c8448014251002584038045095030701c0e0000b0b403044051000c890740c2085152401c01c014881c0072926401075903113038180028641000b0501420650039800421400f000403081030598007510028a0180d40ca0724071428000300e02460f21031503103504d52900001041001e07002c00c00a100d500c01d00111240e40501d600c04a0703481c4000c413130041c80ba4000001060009214140c65241d20780981c0d44500403e89600549044403004d680c4119140e550706020005560015150001040503000071400c510b000e46812001c28110f01006200d5651a500741c5c010002c0c403032445e00200a0400c045490386080c0c80340c101c03070303180011210780940328031800090000d00c07400f601e06c1542c0b03c0d661 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 587109109 1250 587107859 587107861
    0x20d111518190b042d03030c0309080d0b10170c0f090a080a1e2004060b04080a17040f03060f090b04080a090f050d1b080727060608 58
    0xc40c0109092076008050800e01403000c1c1c45007005081d0b4400b41800303001c2c00250140e0b04041c40c052104d910b0b84181201691410000311a01501d02643d1044058043c01c0100d04c1003040c500c114028035140c030f402004040045a400010382d510741c41456040f105903000c00003031041081c1a01c07142d940045180301d07a000000000c482c620355901500b6004010001d00b410a120300b400200040519048001d5540c00701d900401480300080000e007107158482c00c98110014a502c802d8941c1184e102c07140c040c0c44082085039182e80700c4d913104000610000c0ea880380c4441c0c441910545980200c04103845107104150740c1240040440201ea044a2070761201808061541e51aa400341c441c0841020381255580700140c042100c1c582801e00c1103100d0498950b881d8100d1501810710b40b41c64001c00074800302008140529102d08500604c4160003041c80c02895030700c040d520441a0b03603608010300078020b006000a440440800146000c4410390384402c0280c42e207000036080710b05602c10240002c040d14 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 587110359 1250 587109109 587109121
    0xb1f05100c060207062a0507030806010e030703060f0e010b0406050303250503030a0c111c11011e051b090a0b030a09020a0b0310090608030d020309070f06020d1115 72
    0x8580c101c81075114900150030240f66403102e41c1125611044400c0700d100e40702000b2559618a01b02d241d0b1241d43d814010300b042401d803130040210b400140004c0c1441344001120207070780d50070003800c8021644218103208503482000000003400c01d0b04200c2a42d5800c040140a5902c0c11b4010481980c001a008500784440d66070344000186803100305500417111b010003180405c8080c13008600c0b4a00300340c0e011400ca501007900906510140d180c0316041c0c1c012105448110a100e44821018440d40c603000f0f82d101c505030546401400ea00050708a001a00388034025005e52a4109500c070b01c040881202e10b04505092244003882a90141039201c0c1c0b0701b2030b081c40540c0340d601c00345030407100100b80081c0c0c1001990220ba151140360b0460b4408075804410401c022000d00424005811044401e20040d45012205070782da00800c40141822038001c0005003101c0410400b520080c04031080d0400c1d002e940c0c46c0c019444030100040d200000380040020b0010140001c3e401440c2004c071411080b42d90303030306 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 587111609 1250 587110359 587110367
    0x60c0e0a05310204090531060b0f0303030a060614040303090506130e070806090114090109020702040212070f021509032b1103010f060c030f0c031b0b1f0510 69
    0x3840304071440d40c0080c124a0b450314551001d400a081c10b618001000d090040c104a400180400d1304075039501030514014040d401505904000b5900a8010410801c5000040d900c0565200010340511001c001c020b44c80d4919013101b4202c4440c0c0c1c440f4202ca200e00038014105126a020250200b00c036100304100d20b080141c003c1003074200060302404003076242c0c081c0c41e442640a485081c0002e141c5002d1040e1850302c40241401015a0b10700490011381d40303008035908003030502c28408410340c042400825920b0399012100500000c07400d2016034688024050300d0118444802d1005100d210035030014410202007031401407010324011030406a0f13348900001e0404214111841034420f07034400c0809059014002c0503440410603661039604000351b002407404164001001c00c08410403030720100780c1180009440a5a500e4104407500303140c22b041e510039400e41c0031380143c405904240400d100180c100c0724020310301070400010000c0d9600c0b14030401445400f425503c0140001d01c12551401 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 587112859 1250 587111609 587111659
    0x321060f0f1815090103060e0d020c100c080d020703050309010e03090f0d1506060302040923010b03041e03030902030d1107051306150f1e05040317070f060c0e0a05 72
    0x400f004209030014080c021440c100c5017070f0300031a207058a840111940d04400d0288079516607161000f40300c046030020003e0042d041a0642d8010703c0440e42449040c00940300444601c0c0c1070541c0199510041c1c0c0c42d0051981d03004a501d40555484e0010700380400101004483c5803081c0105000702e180418801c000503c2002d100c111040700700c1268610802401e07000c3d9000805003610f0044e00c452404981c04280e5a10410360400314507003000c00c04081e00c05d00c03613030380c1991052807645480742d449140043c010411040e040c03070340f80078505490040660542040582e58402c2d0f080c0e8949c0d801c005026945000640007581c0160080c800c00e00ca0750400f9030381845050b452190209031341d40c0d10542c0501c0c0501442c44080061001950b0100481d000444038611541004099802401c0c1c0080101180661300000b0088404075400c804171011500548149030307004001d00c0c3c075503401450510000c009006d03842c404070700d19580910702c0d4030b171244811048400240c0516030705204080c4030070090079 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 587114109 1250 587112859 587112871
    0x715140304020f0f091f050102120301090c0c060e07032a0e0a06121406100b0a030c05070605071806030e0a06020903190b1b0a0f0c03020321060f0f18 66
    0x1600c0010441d13207581e0303180424000ca00115610320061181130301031201d0502900a03d055500500803440400903a60860f411105c640c040095401040f4030b084407200e10300c86000e00428244080881003101c00f1401c4000c480c0300b40202410024400410f403d02b42003481c41280b0b43e2900c4504111056180d1803003980aa03400f18001003103a294032081c4d18244240605450070f0703660356113011142904002403600128100c403942e890703c2c40c1008214903885080011400c06445031080c510a9006405031019a40e0090040c45240340000c07004180f00c9042c540800740b18003140001030340e640a8459240500d002002402d040b5071244c0395540a503002d010410780510808406a10913903100e4a019403040c403505806005060100480c0400c1c490f0a50403101c6410810100d11210f420101440e03604409040c45030b039205d920304013030303046000d14088000c0f405040d40e00d010001010319015486000c04031201d0021184a40a00650300d00181919400c1103640403c10301059125503040d9104c1 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 587115359 1250 587114109 587114119
    0x301090f0e0a24020406090e25050f0d061e14030a0209180609060f0f1003121809090605010b04300210030902040b03121c1b020715140304020f 63
    0x461403c00400c0340d1040d4800740c0010304d001e00034000c1e01c4050f0f02e04d80e000318490b8a824160605150f80306041c600000c0c41c101800000200b00e800003009009680340110b007888104150350303a601c1000007004044000ca9400d40e520070001c9030f00c3c072243c803224400641c0640101003108144d403c0c050000000707064145210800845640034203010488184140c00300c0019184a0611400b0700e00d440c05c01801c50310300c02c02480100441540b501e120001142e400c203a85401000b02d0317203000c0d00c1a100070041c0060500c403164000c04e01c610b00d1340141104d103104100421490ba600d600701440f0340641d014854400d00f03040303c84c00030810003420312002c3e00707049440070760381c085a6400140084800071980c0040b80d16004240150310f058400c00300c2d8254164050420341021035482d900c2407040010307004140401074448a420b82c00c6600c1345000d52920b12004c001d441d21900069581c0c40070717205020216101103000c18850313119000b50120399003466212411a20f03164200080200b081c92415004 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 587116609 1250 587115359 587115413
    0xc020607030f0b040c05130b0406051903020c0a0c06110606031e120a0c150203130602130803040305151803040e06011b0c051c02090406180213020301090f0e0a 70
    0xa690713910031201060742c0c036102e4960f60a108003020781c1d518030950140d0203014041c441000201c0c0c2003412100c4000f11a03a2500102807902e01c1034000780600041485c2d54820030f81b0800070030481508840903034040340c032540140e040003d1050380d2150119145038142c5c2040c42c501c1e009002d580d032501c850159042c00d0325180b42c400300c0d00c031106400c02400b050020300004400400d00c0601c0c0001c030b4115071a51019450361802070a94a8101c1040c803009004960002d40b50302c01c0319040f002d0102908242c81a40d0781c8503603a0805580e0364a1840480a0030200304e00455008003000c007404013429105406181058079160072000c0c411030082840341404400c0d2a90b01081e05c100b0a62420a40f041c23590701e459504000a103c0c26008803103c0b0002c030000c03840e52002607500c1c50b020590203980084d000c148819400b0b04400780d16100400290810101c01a0140b00040d54002c0c505a03802480c0c104216910300d42d500b41500d801c403000703003600d400c01c24024000c1143c04661150b0b1101c0c480244040c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 587117859 1250 587116609 587116631
    0x10e1e011b020607030b09041a0903093007030b011503060e09101a0d0605061c030503150612011707180f1a062502060304030c12030c020607030f 64
    0x3000700c640540300503040030703080241294143c820842d1994081d114034006151503540c010601c030b903028005180c0d05c08140003c81c0440c0c1001104c2c0c0140e00070300f090402c0012005100b14000d4074186131400d120039a641a020000002104002c60307401c1218100b213a40780c0010240861018581d8808040e294000481c07200c0390308800500610304440180f140707946901c44103007164190007400c3d1403ca946400740e00c4a5840c071041c0070145d40c0100c030005540c0c4810000039400100360300c0000500040c1ca416100b4160804080c51141c00900798140c20200268108880b61284680307088102541500500c42c0075003944612440074010003c541c52a52203841c4d4002d40a902e070000e0055680b5110108249411b030b004200c6102e0712100070034601718440c4006005801000c56400d0f0b1048004c44018150b503420b200d416020740c000d00341c16924100b5040052031010192810b4441217014050f400040f846031103401541500c95026165644903205c3c00c40140105200da40e00403500e51800e410 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 587119109 1250 587117859 587117891
    0x607150504030806030d030e0d20060106032c0d030506182802093105090303060909060f16140f1902030a050d02030c0d090507060e03010e1e01 63
    0x80224040c0c0c40f415281c1ca00801050315100440d01c2d6901014101080130070000302c00504c118210300c99040c07251009203c00c4050451012074040e611403071007580d00004503207815902c0044000e20040c04000c0c00400541d407a8a0201c06810401040d485030106100c00d034402da1046810100041c0b1404109646c0c140514003002c05803008100e20b108000c201c2c80f140d0010100581242c102e0700b0560030549200001003141c0c6042c0c03802e00c000d0581000d0703c07284800c1c0703464601031013085520400c401d04111000301c1d52a042141d040780280240c00c0896840c48002603d24498145c52445c0311290b640c401940384644000d08588003403201c10442d68100f50850809800b0312081016515140c0c150880e070400d6081d01102c2d400159001004dc43b40456801030407108000c0c1c580d007000da40c1c2c1c1c030f541454071041d10a074280114450b180858260401c00c4c0483d0003012514130b9905c682e07032585000101030880301da80c0c015030f821351300c442418501901c2c2e01c00b001440040a800003e542d41344000820 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 587120359 1250 587119109 587119111
    0x3030f06060c0a050d0905011701030602030a060e0c091914210f0307170a02060103120c08120601080c160303050402060c0a0308010f0f0609060c1103010f09020f0315040206071505 79
    0x1e91302d400010240c0c905551201c0d401005100034a0f001710300061405e0740c4401a8410300000d0901a000000101d28070b1198000100030a4051600da82514015545181c2030b00003900c0c02c2c3c0714011040c91000d900920030121030580700c81411201c1285407920810140d4041e220b40c07030a582195242030500b091041c0005d00003000c40d00091a80c68440b4505810f03111b4000f080342202c1042409911450380d400954030741501ea02c000180d00c24821544c0a852038052000014407010340024100e9180740c110441c58051142a20390701c45540b1003000c0300c1c080e40145c00d1241c481043d0314841101080c071a030000c9400a0019000614091740c40e444075003080300351070b000d03000300d9048030041100d140c11080341001000040c0848681c1410140000c0000c0c1842c407038202088082440f28051100a0042070003d100041c020010071525102100c060811071009a1045074040c0500d401801c02051a040f020121024584196526401c2010175040410107070b61030b036048103140b150000c0c0d0344161 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 587121609 1250 587120359 587120363
    0x51011190c090203011a03070311040b0c06060a150e0103150801060509071b020d02010e030d02011a06072105071506140301090506070f050f2701080903030f06060c0a 73
    0x3100101060303080103001481c142c0d10115000340b04000410042250840c9030701002e0403024806c1d07880d1a0301d4070490190500c0c51100c4100c0d000014005482d0344410010105207250342c00f40e454a83c5c40c64100510304140b44600d10804010b84071481a96105464010249505050000d0703d0550a030800c0071f600c1440c3c1040c036442e90758000a116074a45503c805034800410702d003001c1c01c80380031442e0400000e41c00301c00a0085154000e02000c42e8041ca40e20301030520094203d40c2c00c4190b0010082c041c00c0c3c4040c076010701c8143c086000c80142010b5040340c0c240c94009041c0380389401076402581b01c422802601008122080c482c070b2000408001942ca01e0000d0300001154080c18a1074140c1c00d44050300d002807080e03160a10300c4000440100d20703250300008900b803d01601510541c03d0b0f07500d2107850b8075296041c0300000e022003110010524100081c0d0760340c0c0da400b2402c1d02400107660500041c3c2d68036009910910026821aa560700040e90100300500300e1303030400d1150210341e8500303a800c0d401 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 587122859 1250 587121609 587121643
    0xc0b21130b0c04030c0515040306050910110c03310e041b030213050714040603061a0f030f0603030f0408100e01110403020d11030a08030717010b04051011 68
    0x40c00d01407044415205070080120401c852416141d41c2e41c45582884d640b1545000e180c8186002d8840b0a109058034002c54100c0c405121030710302064525102d5051005510744140341c1007600c41115a4042a40d4000b60424002d524008008002c04007080c40c0c14801512040403510101003900000781100c000c050a0031070b0030541c1402c3c9803140041054240111318504800b408002503554102c41143d2000c480c04001140d0721201e90423240b0610036004042ca0000c0000c000410750790580c0400e04070340c0003012803461903084d54100e0b0b10512416803080441c210a0001c1038180d02c40e210710503000f0303c3c0101101d03e4580d030741e100c140840d0030542c40302101d030300904580c18056206004072240d01d130240008003c3e01d000c3d00c05414540c050342c00040d000390009105501041203040d211070540741d0080403501c0801c083d2915000c036600840f00940014102c001511f4621100f15805059a10000c442c0d0700f0a42407a00b03005c105401d9a9480042101000e50103c075070b1800c0c0041c46000a121607 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 587124109 1250 587122859 587122891
    0x13030f0503180603132603100303030b030109080415020a060c050a021029060408070f150c0309030b061809060105180411040b0303190201090c09090c0b21 68
    0x100720401010412042d0340180f408000b0000d00100382003c00d00000d600020100c140310398414590b42c1c80090402004501d80c000051208155503650fa0004a82c80307503030103200840302c900c181030a85020303001c0144001e900b4802400a10f02080740820311070102e00c111441e440880d100c1c5002d0303c20300c021601c08100f0000303900d0f0050780d052000c88440ba01e048414480d04451041c0c41c0903c000a12829040d10382c8100c01a07295513505003190024242c0504940f05a42c6803208103900192501ca024042602e0b01e280302002c1d805607005001c07171901a220700442a1443d00c520010340d00003031039181c1c080b90540d0807058072a00e484825001d0301240c40101313200d41c1403000303001103000102401540410108200800100c030003c003019000001d0700c011400c0c0988601003840c0d03019295546c0105a804982000010b80c15070003e4140d90280c0084111650707282040d40844488040180030110400d5050003c80500c2004106850308005441030782240c10f0034590280b54140c0302200386010180d = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 587125359 1250 587124109 587124127
    0x4020d08190813020306221b051804050c21030c070e010b1c201c11040b1b070504140a0e120403060b030309040906051b0309030f13030f0503 62
    0x1141255210b90b0741c41040343c1614941c3c00080c0c0d200f0000704010300c0e900c90310f54022921490252404c4841754086130301150741008600300c4102d080540a1340c1d020b0038024a142195180c0030100c00c0c021904240980119442d140520100740e1780301d10b1503e1808016804071200e000c0400080130011147c00151128600b4925010350803081a8002c501121090001c18144032103410310300a80074080100060318941a18030003601d004441038042c0140010818101c6884265901403171040165002c00003041c190340649040d003d640503e83d00d41100307101402040b40050207808105280340200d80f022076940c00014103035050400400e00703a486080074050503040030b0243c0308928a020010341080b000c40c2e014520319009510002d80130548502c428420f6032018030840302d07448000740c0144103904060811002814081c3c44410080c40f52801d031062910040003641c2c003c1c0007000144d40751022000d00f4910030b402011b0070408030501d075840000002d10000543c52500d2091010f175440391004 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 587126609 1250 587125359 587125367
    0x9170d0f050c0312180f0f0f010c0507080315040c231602150f03010b1b0105070801230d03031512020d06020304140607021006060302040b1204020d0819 67
    0x550311414480c05009a180c80600401034802481003d89810080e0395056003031600400c04071442d40c07179801410620174401801207103680d000142034044486141d04e00031850300b200c654a19000020328148414800104504020b5421440450f5080c0c00322410034000741c101d50100d1841c0300403900690182c1c1c0d0b0341c0000048080d000d01c2c9001090704080704186000c2d800c018404000313128800315002c1d0002e0360403c0b400c8e10f040300661203065480790303185d88610000c4e600c159249200c60b003813021040441e0805010b00f03131054000c0d940d40c4500d03900c2c103c05400140c06100004040b911080100c280d01e0700d80d0440003100d00d0180d80e0124404c80703400344220f1f004100c2d41002e9041c803400c2000e1009a21160f590150322a8002d10042e43c80c1c1d20b50030101c0840001c52680e0200d400394100340452242d000491031820009021304200140c1c1e104001c5e0224415807164130301101d0300340110404650800c101c076a01600140000c0c210441c00d564111a946c041c03010180202180620007085a80c0 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 587127859 1250 587126609 587126627
    0xf020c010305011802091519080108033603160f050d030503010b0304031b03121508120c24090c01050a0206240a09061701051605030709170d 62
    0xa0030100095410075145044480501c3c203134103e030a40018030100e4076100c4011044858448481e0180c9509030000c290b0750104901001000040c0c0c6600041000300c004011a202c5044000b0b203224015810301c01d00148600c000c10000041c8424035400742191010711240c50011450060944d00d14203000c4000282007490300201e02034082d170401880007039004412241903407a074605d0561240e40b180303000c4982c060019884042c41e014108003608064112408003200700007050f06101c24100c88a59802c02c40c05803103545041d9106044107640e451070384006026040091048c0c80c00110b50a103000562040b0f060040d6000c007034a070410041c04024080c100000760240780003440c240410100035903811015000c0c81c4480d030f54407090300c10940c4007150303044c50100162100f01c2e56503855030b400703004280910404030b201c0200e1614031806036042c0718981c45032444800314013400d1007507103040322981c00c001c0442043c005a01000309103800c154841e01d001000e0040100210721030300307400811641e0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 587129109 1250 587127859 587127883
    0xf1504090906020418200d0f0e06190b01021506060409020a0908160302011205090106031e030206150907050a090902030a020a11011406040c0c081303030f08040305030a0b120d0f02 79
    0x840c0900110031500c0f1700c0f186d0341c404078041800341d440d201c0b4249510b000708080c01141594900e08100302002042c0800c20700d02ca880029070510001507140751280c242c524069000e03006803c0040300001400c4180c20041d00702401030501401c00d5143e2038804126800345ea14031001c103c0c07512080054000c10000750700d41c0c07291250040c00b0783c2d00d942d001038440a048040c00f000c403a26000080e00303160f001d52142c402541c1003654504000b501060f0341d80036040c50f100c1032700180035a20000f070000310341ca80c00d10340883d0081c0101110340d4401c1c90856003a042694507104010b031402c0d0005513050180003442c0500312001e40140c3c0e82803000006000709481540d50306581c0d04198481d44450300044190382d01800988001c25210241c00c03045405036403040d0000d044031400709007a503400c2c0900c0c00070020303640300740c917008070910818900350750002d03084800400080d405c000083c00c242140e00200c4410402808101c203080140700e000342802805202c0000182e400c21582080c2c0b41c2c108000080c42c1 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 587130359 1250 587129109 587129111
    0x9040c17162003070507060323130b09070305120409051510120b091905180c040c09080d0c1203060f0314120c030414010e0f1504090906020418 63
    0x94800500604400c2c8112084450641c603910400600ea02c2401141c5050f40d001007629166915203001030020700c078207100b00c1c00e80da1050281810b44000d051030036010780910300c0c10301c0710304e15507680300c0700c480400030030f810110302803020000002035080151841c58801c001403591101e08041c1c901c0b0450700001c11000446011a4070404c00c1d40b07070507243c490003c00910302160319545c00341c8080041c15901480316004a03c11040103811008005141084070b001358081c0b1054641c017052403403625096103001c24035004843c003061245003d81c04030f4800605810400c8030241d58034a018100a900300364140814241103c02c0104586010815114401801d041115504049092895501c240030060445c08010703242c0c07d58040400c411095160080f5a00f40c4e00c1980c00c1d00c040d282c0d0000c0c403c07848450130480d10502c03d580252004843d15802401403015085da55040100b0307a08140d0400800e40740803c004204541d8074000c110009005007070250f40c951502c1d41c20800a11400c101e0000b0b1 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 587131609 1250 587130359 587130391
    0x91806050117060a270c0201060b0a0e181501030605150a03021305061909150e1c05060a0209010813231002120a0b010903020a1a09040c17 61
    0x30341c1c1c100290202800400300300030350320364604000c210740880d10741106002c0b00c111810072841c101550110140100b09803014420440f1080702a403d0b26028060359120300010b000c0c14008074450540b10300a100b0007015080c606068010342c2c41ba29400740e40c05903200141011960603540c050240c4402000195a548040824500c0d517601034000d0750400030825400149480e800008080404080c0100410560340d4880008596107440d03804603000d80880c2d40780400090b03541c403c5601003180c0c0302a44405c1901c90b00e44040141004144426141000000062402041c1c0400040b44140c0c407925005070b544203c20005044240c004090108001180001a00080408000308501a500034000c480c1103030b503285d42818111869035290a00d84080385044c0014038042000b40586075020b01000a17640403c01110084000d00010b0b4000098510400c4160011490090810364194009003802c0388040000c090b201c003107040c20b000a03240e0035581911510481d00341e40080d24404c3d036910b0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 587132859 1250 587131609 587131619
    0x20403020f1f0e010c05011518020a090501111c0302210417090109080a0c06090801020a020d120b040e101b08041b0b0c060708130201140706060510091806 68
    0x1110b008034a41c90100f2180540781c259036406107048803440d951041c000d206503203242d01429000203140c411040c20b202128207400da0440c4070302c00c1350b034098a244c1d683c0b0843c5090a00660b06841e00310340c8503029115440021b02e21229040c01d001303021400e5500541d59040ea181c2c003036141c2d5035500789030030310b400c90078140000111580a1403105c60300540c8099103c81c403140050310410416070007c441801407842900c10031607100404425601c954079150704860710307212150f08034003c021011001d64009240c50384003030b00414040c180c0c070710740d0900804c140c10210082415a100015400c61a601c0741c45200600013007801415081402d1900a03244c001060700e005011701005000500342c8250400c4240408812101040c054160000c02d203070781c3c04009119a07a95142242c003800002e030100046144e0a001d10039103111590140d495000d802c181c640d0786006644002000c841d03081c0e55003400100c645452240f41048149900d80201c500d180c036610b8051180c105400d0070440e46403020500c1 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 587134109 1250 587132859 587132899
    0x6120f0c031b0d15020c0a0609030210090b060411300c0f1902280203010c110307140c0406061e0912030807030906050114031c080c07030302041503020403020f 70
    0x408030341c00100810242040307600c000002d106d1100326261034050710041d43d05200094100d469102d102e54200d450500010100604858170b82c54001c0040d64103030701080c010315254002007100e4414000081c60f03d280000d00e03c0c508240c00011040c0f1019411402602c2440c500c080741d4071400a020903031034280c28089048040c4203850410500d19004000203e44501c20070402c03103402c100c0f1200c0071407090000400c110080740c0d200200c1c8079600345418145114412010241c40380b00c0e01c0e00440c05d1418076541d40d500316030840d05041d0f0a11440300b04440d542e950f070007400d004043c0350720b888121022680000d400583d5030244030b801c0c05440c28080080c810328480e002b00080d098502241140c440b180c04401600d016139000d0100c0d41072500110b0324590091200a03082821070407241c00c1041240d5070800022000d046202107000701d00001c03148903011005114042c86490300601d003585031824424010041a041c0c00001da0204040c0118244003905412445040311100017440804d00040 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 587135359 1250 587134109 587134129
    0x102030a0c0813060921020102030a0f0e061605060a0209030c010503040206090409241b0f090315061406090906040b010e130203090606010f1706120f0c031b 69
    0x40200011a10340205001d441d6040d42c0083c507880e2008665150390f4080188036071154000c0b1855a10051800c20079030041460344a43d0503410b0b006542840b1445509440f965100f02d0a1424441c6220020070280d48a4005180c001881a40c03840126914180741c0d2400701c005007a42002071040205010940e4001460070324540d0901e0880d540f9542c1e880400c02da8025034508a81050500014000f00b20040c80c407450b8403007070170b9038203400301c0341110030201981c0407610780e071020b03103034506c4240b00c4244150000c195a0105080002945607030303036500c101d1544581800e000c42d40d566041403025030300a8140d454200411100d440c00d28083d48009036011300d003d890f00703101c1d50f078400300b81d1440d0b4080d0000107402c540080c40b40e4041200420420f0103540116003201c201d0290a0000300d5541c090008a2154481aa1100d004540c901e092134461803000c2e00503680000287d18900309040c0800c0180415a40300000e0f101040a103814549040300d241c01c450340480d01410f1f010b0b504e85174a01d10f9 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 587136609 1250 587135359 587135377
    0x60c11070b070209041a0a092607080304031407150c08072106170307050c0604030c03060203060103090b0403020a1b1a1b0a08120f041505090c030714011202030105010203 75
    0x203010320740b170303901d48241d204405000454413029001e0800c180003c19030301a15000b4007500b24203240540c0d0b502e0001042e1301140050740c00d440e00340560408101c920019541c032603c01c0c18a444001d0351080c8900c3c06401c4401e0446a84081c0922214540e1301400750403602c1d486418060780714107108a01500f0408840210742c8036000030b0480c000c8052712904070000500c40e001c51000000090f00009480343c4c00158261040d00c1458451456410110b00321400c0b2500210403c81003401d5030f6505000e90f0001e400d550415854401c0000403410641d030113400780c0d01c203130014244286186004032403640307250000f0499045110041040ba940b004c80600e240d80140c41003a5602000004600440e843c0302d080c06c111301c40d2000070003c002070300000700076107001c40041d2036003aa580180c001204070304860052207481c0720098404c4038030041e0042900640c0080682d108808a00c020902c0d020140d8011013140c000701070388035003550f00102c1c400d401a400700403d615540c14140083d60303910441e005 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 587137859 1250 587136609 587136619
    0x171005010b1c200d0605090402011b0611031905060306040b01060c0c0306110a02071208121504050415140907031b03060614040605060702030a0605061c060c11070b0702 74
    0x101c0d250b8948a40c041d01000840070074030403807400c0410503440359030403280010040718580100812070789003188516124a50580d00d4140c08018000c1c0315281c04003414084820a0300c80030507e9052a8500c0914460710700d0740e500d15002080c910a54064403000752055009402102c1400085642d6810040c155034107814480d461201c9494a480703006182c4e030001e8005440d1030596200c04510781c00030b140c0c4405650841d2103a603111403808201d0700032410004c090303420400204080d00d03031140711030368071408156003160940c0d441004a01550b5044408a40345521540300c4074802660f44a02000007048209102c890711740781610343ea54140601002d0034078044038400d0080c05e4200d2800300059a84410305200403561416401c61600041d1802c0d481142458070108460800600791090315400400030a09144161640302c0140406840141c12000c030f5005928211a00049036096030301c03601300040e200b440d42c80c0041c203d900c1744584007403580240d001004405188002c0d140d15940440b6 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 587139109 1250 587137859 587137897
    0x2010c08090a17161d041b03051c090603060302030c120c120708070b0f091002010b0d080915090a030b0601090302120a0201090b160807021306171005010b 68
    0x400100744240540c04a40704503180307100f072500307108045100c0d4108a503c600f900070b42521003111000f1030124404107512005a5000100440c40c001d064030203414090480d0051143c81c5d4945a041c0506000381e8100c40c3c4544580c8e201265221036004000c000131300c2c0803c1101d0135540041d44034400880350500c00c40700c1500c003088446043c0003000c4544030050109101c10751504800da100d80140c0b01d54a21401103880000c0d00405500c2120701030b500d1001d0544c501100e4400700080b0200d010f500c80c00b1036603248080c00310360700c400e8500c0c5419409480340381e44030100101085000441c4101814607078200703000401854841401c6102601ea200d55002c7c001d40d64080103c400054030360020798444d40520019100300c0c0007184408809000381d803408185900e5003402203052040d4020742e03031440310030103e42000c51584005004100d10007860301002e00d240170703205030582d42d050304240c03152030710000f0007401d000e0100310342541311889030000d0015600d0240f44480074052503134070100c205181340b = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 587140359 1250 587139109 587139127
    0x16050d0b15070b070908061303080709030524060a05010507170c06010e06090f0106091203020106080d0f0906080f0a020d020c0714040e0c061914030115081302010c08 73
    0x841c10181280030801d807502d0740c041d0305182e03024400c25101c52002c0380c2c001002285e10345012a20b83c0c030031060356000005240c1941c1d4200d40f0600020800d034100441140044000741c0140060381e00b0106001450301ca00d041c43c0e0480400c9140581041d2090030784540030040c03a46c00c007050f280903d800400e005400490619100300d588640c1078420031701c1c0540b00c000f0a850641d070680da80030715000d84050740141e481c4148904062070a009540106103280c400300480140c5040b601d8115210388000320305169211001403600c9861040c400104d48200c0000712010f44c800c0b10000141142e04e007090060030604030b020700d20800034000b1040c2c0303500002c01c98107003600741e0102c45101c1010003c403000b05076102c0c0309456180101130300610031420b00042c02020840011b00011a1200800c480e181c80140000042d1140d4190451340034400c0349030070906100300840c00b55000380584001c035540000480c00040c46a00c008003803002e5a1070324404400982d078051516990290710841d803075510300030300d = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 587141609 1250 587140359 587140369
    0x5070c0314120d0501030b2d0a02090a080c010e030607080c0706091a0f060a0e010e1317090a09020406020a060e030904060303120b0d03021002090d0f0302010c020616050d0b 76
    0x41e403210a0090702c0050070810001e0941d005604070390288052040036102c1c0c2d4060584014480441c0c22004c1c3d1008501c49600807050ba455000240c54800528201400300400c800d8a0103600c121107581100c80700c920705507080700c803164a2000440140c451407070070308005014440041d2105180034070102e598820013a05521482010f504aa401c405a0301b40c030b0390440e0000310451740115034000c080c02103051410400c14000a07103843c16020b0f011603092120041944c50003c0100b17078860651680c0c40302041015001510020401806540e1000c84005000000050741e020140c82403041008110b1140d0200300406901d500c00b10105950091006080c958064034a196078014541a000400c05811054990114401480c01d03c0048008803c01c901940c00242c040c0c0580c015009100200302c481d03006048407880103101c03c1301141c0c42e807102151100a40c00480c0540c0d510704403100d40d00c0d01080349640c85081e00c42500800100000010142d0103000c1c5007400050302e0706402c4400d5911 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 587142859 1250 587141609 587141623
    0x705070905150a0b09030d1b0b130807120e030d1b0212070801090c09020901080403120e06040f02280504090c08160f14090f060303160308060103060605070c0314 71
    0x741000c00745034403441c628000e40e0003008042d2091003000701f4014014084c00c5035440310b0b0f1001203082d02c4500729450300003468100030710390704860f40782d072a90f140000d42c1c1d600130342883c031b00407043e10040484068001c4c20244104052a100e544414081d07203001d40c0c06600700c14a0748880c02408801080c0d840030840700c11202c101640b481c010f44038081040e401c1540200c0311301e80504140c3e052940d4843c00f14040f40300d0081d9143c00950b0010008000c00e0154070311080c1c2c1d81d900d12002813081c01b8032101307038100075007a0340442c0e078810714100304820b5250900703c0f0b2010780983d4040061400707100c0c031051900f07021842018000d5403244280800d0191110030080200186000d0b600c02d40c07240c0d04403a80b07881c4180039a466a0280b040d0210312884190076081120030060a03002142d1030f003d0b242d075030451005080380e07850302c02003090080020202040e404401d11030384a000301414287d00140076255a5085041000300500c01080801ca2510150f07045940100c1c03241394114034030f42d5490030105 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 587144109 1250 587142859 587142901
    0xe0109090515160e240306061b16091a1207090905370f060204090213050a0b0702210703080301180f0908180613080105040c0b0705070905 61
    0x1018410007110310341ca80400c009060040c0c0e02c4c0e0b007055603000b08106212807080801c0d1001e404d20f80080e000000e2002c003c580190004244600b0300310201c10310380c0507441d0030030304191a400c00e04584a140703416844c003d0261100b40010711000c485050400c0c1801d85103000584100b40e03c0880c8200c035003080c0088000362070428030501004005c2d0410603a030742d441010800e0302c44403c08005a070307815101c20303008169801400c0000b401040d40c840702585c2c00c12103000da50b5543d00f00400a505031a510080090300715030484889050324060070810035800ea41e21400344140c2c10401e40c00160380ea42d07001d0740040201c42d40b2a80048006629606d0001d15400003007030201c00000100d948442400f103100c8900507058144007251417050802d0a031001c1c5c000060880e02d06004075034000c0200e04a0942c0424043d0005041807030140c013810303288600ea0700464240e55124203000510180d610300c4005005080961842c3ca01a607442c40ea40f44407903c034550420360f490380441c440d1210340026108482e = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 587145359 1250 587144109 587144143
    0xa0b0a0815041208060d03081902030106030506040e0303100302090a1413050f0c0a0b0a03110301090b091509010b1309140f070908060106050901050714010221010e01090905 76
    0x448400740000381c12800740d409a820744a4480c0d0720810701e116040751486032001070040080c082560360196160742021701200c083e0510b4a0320000500c030302c2c1c4065402014907035000304660602c0f01c18801240c82095640f420f41d0001c20400018000394a00c43c01126411f6070f00ca006aa100706100c00103004014140754140e820b0008c3c00b48114820f0342840803607010701e050390342c0008002c0d1225a9414610801038101d82c031600b04009400038030018182e15140b40c100800d122501000c0c0741c800d41d100b40c0103401520b651365801c94143c209007414642c004603840094562100020000302d1981d414440c004e652000000c608446600d007115075001800c10a600f44a080551409003080b04012950403c0b00e01868001462652092545404030fa991340080c1c079159081c46001c40316031b0302c407006240c1445010010030000989182d2208040c8107031000050700d6129445440c0001c810804040c0c2101c40003800500401c03008880850448100c600300249407032040c0303041c40c10000c1900c2550f40381 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 587146609 1250 587145359 587145373
    0x41413050109050117150601030c0c0210120e0102030f06150d050c03220215090f060f1902070303120506040f090f0b0603150f180f0c012003030a0b0a08 67
    0x480c00603003149050710170056401180d010803603100d0340d0314103241000090980340d110109004d940654401802c491080c81d01401040d000d030046485210500903d00015a4803400d8800103011441140e003040103810096145080200035580846005402d16228007808950000d0384029041105d0f000c13207a5080900861901d50500e22561b04121b441d045400020403000c1e01c090030b032003400d00e503055000302072140700c21030780b01042d80e10307044201c2c0c10ba0004124070700c107102681c1d082c0180000b41e103803403806503035911952000c051202003600c41c0400d5500502040c00000d4005101e2800821140300000d2180d58540014028140d481d2486022520b0030740128244038024241d185040d016030324007222a100d13a0203141c0e4030f0180c211107503003d480f00804a42035208158905070440000d10403c03a04418281e1445e091584040040c54030341c4c0810f140d1041540c22150144a40b05081150101420940c850580b20700c0700074081000e0b04d507a1007440c0c16903a5940d02200141c10314400b1a485 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 587147859 1250 587146609 587146619
    0xd0f02090705041e0603140105031e01110403081309090c1a040b030c070309081906020906090301020f0c01061202011d01030f021b10050402031f0e06040b040311010504080414130501 80
    0x45580e20303001d1781d00000e080012070b110140401448034101d0704050020038200842c00340e106007040080540d001d2070354a030f08200010724800d20203000a1800784401d113994400d60044242005981c1c0c2c000e4410070f083c2405800440e40003d4002c048507107070b0800c904c010b84015a600010700c920382040310b000002000f80051100d020002d400914400c0d192072071500c5d25403400623610011004400e50740300d0b6500d0741d24009200c030340181205102c09407035036040100321000207099810100740c2d4200020040303120889080240101c0b0b008002400440c0e04c02295500000c0c9840300401e42c5480040c544011112103034881d80c8503040e40074244604544030500005020fa030681c1620390819140f1940b24028040c403034620803075020f194020010204061051500000822807074031185e00a952613856824203807040c084644200d20425440c00a8078041c640034103210307100703180c00742680c3c905020000001c00d030108075015100418007003a0050a0034001954081c15840f2500c01e080c103140000034 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 587149109 1250 587147859 587147909
    0xa06030210050a030518030406050d110406260606090108070c15060602100e070314120403050105010312180e090316261611040b061b0c0d0f0209070504 67
    0x19011a0640e001c0c02652919036002806000008811010307030400c00c230030400540282e000b03110807070020300c2c0440c0030340c0c540882003000d400c268403110214065015013060100201910296101c080b041034083d0300741a400b080840c081e04014034140140c01010410b40c0b401480d0301e03e0705d00c0d407012000e040c8521519695018150b20b1041c81e01620504002003662290341c000c03039520000c58401840e20354a10b403500245e02c1203000310400c242c01041100c218884a090042001d9400cc00c0042070551451074001c0c080c90654203400100b04140c0030740180b00440b1a021012107856030310f403540c0c6032200031582c0d09600c0303042c6100100700303800d0011904115643d080701003626090a01c80d40451000040e040240c0300d40c045c08040c071000c611400c400642c0140865030400c201610014501c008040407482c03940c4410200f02100c40ca03a50381c1c0d01150b40c20411f000502d81c0070381c0c0080081600b9a1883c110f9440c826000744204130b5680014080c5100b0340c2030310b0041841640b8244c1031404005410 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 587150359 1250 587149109 587149117
    0x10b07020a0510120501090c080c0703090807090e07052b230a060605090915091f140703020405060a0c0528051908160c03020301050c120108060f040b0a0603021005 72
    0x2081c07074180000007072118060b1161980054040d109c0c5030b155542c2e1030920303034150301c030000880031b00840c03001c04602d02c039080106801420020f000015102c3c0c99000c0e0b1480d141046d40a0341c030130041481c0c0310004030440c20600e030f42c110f00301440c2c00402095241100b00b0060010007901e4034283c1c0e281c44148900d00140804481c0e014000c00c005030741c0c90300705001d080740c0205c07031840d1280e000348182c03428044200301c0181c2c44003a00f004d503212054404510260381e6440000c0ca0394003915400041d0200801c040541d0700000c141c14214601403400000c01c81e1801490201818060801b0b540c1c002d2040601213240c00d01e0040003103044212203400c89c6034000001c04c0301605e42d442182d8180807600c402d120b00075892500184400d08004a81000c02d5806040107011190308072180c50020050710240545401855002006a100d10300030010030f0b01581c1c1680001201d030301c80f9051041a00f070400e00150880d4103c202e08a15940d00320400d40507100740c1d0300c0250000c08d52010729545680c084050 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 587151609 1250 587150359 587150387
    0x2031302130b040c3903110a0b04060204081501050a090b0d06020c010603051e0c0f0310060e070f020a020a060f1704030903060c08040c05060d23010501020111040806010b07020a0510 80
    0xa041718443c6141c9071105000b4242030080201905150100070a000c0da020103031060030703e400c6078098046a540c0060b41581039400700c0d00741d03030040f8051180c00c0062003078051001300c0d00300307101b4258542000142c59411611440343e41c5561020700312200c0e1100b24007124000e81292096540c0c0c01190900ca0081c107583c402614680503404030040351080f50041101aa1540701c02024601c5110702040b0162001d0201c4c5a41446014000b440c03070032880c01128001c050b4801c51201c80d1416000181c59078290150950440d00070010100050351032510f03603815120725252044940c640240f041c0c400529103a01c80010b4094181000f0416601204007800d5900c10340c401e1041040201c010b036074002082d140140740010040d007d02032410141e0203444c00d07580ba60004940c8120320240c51030305444506495151080450050205503024090408910041c9482502d41850800502e464550600800c0d000170b00009035141550744002403c000703014024000109100c9d44440504401e80707080072 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 587152859 1250 587151609 587151647
    0x405150d0b0324180a0f050c0109181808040e010603061a03130204020d1401150503010b0a051c0e060a1401050d060509010e01060f06030f02031302130b040c 69
    0x110000c281000f00d08001d0000c100306800c4011000c3c0720700440140320003800c5010b1125201d8504e04400020069180302a004501040d0303003041509005051902c248002414010099020030010f906500740d410008568180010a80c0203c165010945c80b0410040d007804800300300070030300c419440b07000c3d4121011910100031071a0352300500781e40700400d1508000344e141c0c14030018a48011a000360080d80303200620045ca070841d0340800b0003c0b640e0311000e007501c200c003545c0103118050302401d003c69011708504002d829585031411400d424401c40e10440c00304000071501c0c80700c100e03071a02c4c1c00500c094078020030300c00300100600050b541d0200300d0307401c5003080c11b016a4154401c481d203030081c1603520240a020a90140d500c84038054040a807011080d50769034503003000740d11402e100b4030020b4040e2108504906240c0b64000307098540290007010075504c10010302541003140c06103980c072030f0350644043c210003c0811405004000d203c03150760700181040d90341e09481780d000d0006400d10748022a = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 587154109 1250 587152859 587152871
    0x7050609070e060a032603090a0b0109052211060712030c090b0a14090904050c030607030e0c010c1401060b0a09061b02242106090412080703020405150d 67
    0x10081015405640c15904680d011900344041081043c42c0030261102141c02520b006c05101d060000358811140301800e500840c2000781000040e01c07070070f4010203481e0f10600c050705103041508543d0b401001c104400e40c40c100022410404040103188034480300500e000d4690040b402c00d199007400880b1090000392408070034a40d0f660103052203400b036580144640303080810350f03481603036407411201a428400d00b05001c00001951074125081c85203201c1d401074419500d41c181230515060028040b14140350408440c0d00b500080012a1614180240b030580c1560b1139508110f0b003a2402000820345a50900d0000310708a40c0c04001445440300c1d60b5900102c89541d8641110b80c00118103800200e1090030340380307030050301e003490803407450601001e5407000c402401a400101540541c003a02c1941c542c40e010b100c0e240401c901440da00a0041d10742104074600780c3e440c000460f4070700094100344000708000c550050b21a84c141d5000c2e0401800840c200b14600200700f817590000d8001003032803400c1c00 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 587155359 1250 587154109 587154119
    0x250302090c0721120603050a030305010f08060a0209061b06070f02030703080a091a040606030c0906050d0b0907170715020d09140619080603060f15040203090a080705060907 76
    0x401281d48054010311500c0e00d503c141d0080b842c50210301c140d070104000f10b41120084604c1d180c490440154401e9008007400c881c10325000c1e0a44205130f00083e00041108010014044040f480ca58082d15641c030060755109440c0000c0d40e140200105003603804844401c00b43c0d02680014014003078100341d00d6481825540907002c0342d907407082d420002c00003800c0c800030420021154000340220ba2103801c601356150429075811074640302c115002e0312240e448400030014403844000c02e4014008441e1b060020303a0402020a642d422403d8008291001240024151420521081d009480050080100e6410b40403000ba80d5420600428280c0c0c6980c0f8103241c9982e00000b0038a40c0c401d01a1200140d10340340c00340e0342010f8182c0c02d40381508488204408201c50b48400002281c4d600c1c07a41302c00d07a45041003014103160880050040400e000300000b0b000c07200d8080c940c5070346e0080303040350050f98030b907510180981000540c1d10010034441c0c021900030204400030502600c45c805441c112821740340d0b11 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 587156609 1250 587155359 587155381
    0x806070e0411070201080402060903010e1612020901230603090d020c0405090a030507140d120b1801090b06071e150903050415020102190906020705061e030925030209 73
    0xb01950149444041280400650084e00415401400200b49074204000c0e08003083c2036920160780f25001c0c0c0c000d83c6001c0700c1406d4004025014242d20b1074851692451540415060030042c00383d60701007111004410410100340c841c0450000c4040c003010f07243d0901c0c492241d40d500b4101d0202026014606000c1a2800c25100700d5101c3c3c128900141150080c54a09440b01e40c00040140c60030402410394410f08003080250a0174070030b090b42c03440710039551203202004070b40110b456140718080b000400080c088060580e14103468000740c002442c0801c1000165445c861080001c0c045107030655144098505150440c600f240160303804c801c0414001490b8007280c0300c100b4010081481800141710a035412180c03600b000545000040c50f00e0514a84400740000e15901d00300010800c030400c1c042c80c1e6050003d44001c10060b940d040c00d007820b10308c814003061212a805150230b00301000042801c40100000f0300c00c0005040c4200110540084c01402c1c9039140c0816801000746030b020800c5000340b = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 587157859 1250 587156609 587156621
    0x111905033006010c022805180f010b0d0905070b0d050903030f010306090305070203010e060402030f0f100911060f031005010f1b05120c01020d1104030c0b0901180806070e04 76
    0x741c810460a036880300300640b10350240b401c00340d8103c0110701020b00364503441c100480c1100014120a01000d141004110f40c81007180ca200361510300000030301400c1d500070b0241a0644096010701c540f80c0103c4054080204001c0801400c01c0c03041210026040b20920010001e9030310b202010b02199032142e840994911054500309a1a02d002e001003010a042d42d0080c0700040c0310380340c00d0340381c008190006401c3d20320000c06406160050f2092004514040042040e071007409405083d007140b10343d40c0039864503090703c0b06003842501e81280c1d1040141c24501c1d22050702d4000c101c15204d002108a01085030421280ca072851a0a40070101e0958002c60011031182185c0e903442042d500f032541d9012840100d190100c43c07610601040c081e91000c100c0141860781e045100050b00c03001490310600580d00003001900031610200310030700c082003203012032809450107001402c0c0c0e01c9801c600121381c0d9503660440c443d070000c881d241c003080101c404601640140300c6941c80d000300815504c10401151303c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 587159109 1250 587157859 587157937
    0x110111031510080412170702030a0e031c05030c070c0f0614070b061e0301050c070b0a090b0105010815090a0902030c0f01050315060c1005060a08070609030311190503 73
    0x1d1500d0005000440c3c2c00d040c0140b00c84036140c02842a80c0340144400e11701000c0d91141f0141c0c0010555500165004941d0f1803d444210000c24140000300c419042c090201030619042000c000001f600c0002e6000440c3d59003544460319091141d600d440744058040c250145400141001000e0074581d900e00c41a1401c45410800c030311080d1710303210100709068041003050301e504041c80c40b45480940d0213208451040801e01003540d81c4071840d1400c020701d158001e0140490394a0610100c5c045451080300c07a0540d02c00382000d8080e5200c003070f8407400e034500701c422a83d0720802c2402000725141494100d91500e80c42034045a10511103181081500e03a0040a2140000c105100044250503070b006503000084001c0e00e15898013121030b00050401c283e48140c01d84498540052101a0420842410044c48480c010f411520304010000344085042c3c031029040040306400d8110411050010000110400c80f81c1d015804080ca411600c030f402034001c2c121000d981480c0c1e003900940da005070401c130750 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 587160359 1250 587159109 587159117
    0x90a03020c01051c060627080304060f090305120a09090203060906040f0e03041d060102060c0f070212100c02010506060a02071e0513060504050a0b130c110111031510 73
    0x30322007800458098029400c055000326803c030348181144c040344030702c3d40a000d041ea105405c404000c40000c4940c0300e10090540d00c110281d070704002c01040032068405490151600b055194a0f1020031a940b0040d600b01802c54019003440740300400c4c03400020800048140c5030316141a564908510407808112000394014448500040c810b262030b42c0b021407042164403000071281d81005111703146421a411504040310b41015064031040c040d01d505600110134401040d0915050328a07115a00440c6142044010003241440c21542e4440c078019001d603080007100e84180300c114400c40034240629102000d940780001250240c1090800c98003040455001004810b14000440c0307920704801200e110005040140070408ea500da8100382c4182d0901c09004c0394071410b040400040315805004884828508008822141c485d092418480290b4400015001c2001141a40c90510034201ea051a502c0c0405562070300740744a02031401584a04a0b03200d00000360401e0043c0300030a240048045 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 587161609 1250 587160359 587160373
    0x10e07081e091f05010518060d03050309010f020c0105060108090c010507030c154d070215030711011a03071505160f0201121e020703020a020901030c0e090a0302 71
    0x1441d508200c0d140c2100281c811112105030310301541c01c0c140154071807140426201c0c0010401c0e481c00201d22074220170240c5000c130381410048006a001001d20314001c050000104c0019200502035000701c1da0512100d609668800032602d00f03d0003000c007102d10902254803036021403100c580015a01000a40607104c0a29044c881d0b1810340c1c440d00c030100d0440b000550800d45110174034103801560002c0491500c14880b02c814a44120f8001008403480328551001241c034940342040c0c080da40c1d00e2a6060401c0e036a4604040c00031846088111420014008c4000103100007150b0040480103192400740081100c0e400f00100030a1001191961a5042d4452101401483e001161500c075420a505140d0300c0d000303c0a102c92142c41c400c41050740c1d282c44480b0000c00790b50300448200224030302c200c030421913078000c582180d41c07202044c010700e0306050707020444001305402000070342402500201110465a5203207015a4440810300410381d0f0143d00c000424030031100000d004210382e606401038210 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 587162859 1250 587161609 587161651
    0x5090d12021c0608030a1d090105040b27060415030812181c0306080a0335040b15010c0305090906060f0c07090e03070b010e0601180e010e0708 63
    0x194000b030070100ea1500001100d60000b41c403610560004240c00c00117980c6034041c02e10050304650440308180311100202c0c1c0b84107880c0e903501100505507041194002000c40498000c00c0346140c0e03c003010b6800701c2c41c00c5500c100308490468914811802281c00744603400c01c29040112000040c4401854048244507841c0494404003000313600441c0b04800c9848160f8000d000c500d060080440840c1300030300c00900b11405585801584050070240c03008200c80321043ea0005c16120381d1030410040401030f0071082c1128031805402c01c0c01c502094894050700e0810b03041000001c3d0040c0c5509403d841c030a40601c4981d4003440c3e01540a0f03425885032410240c078642032145004000b0070183d0300c0002008039100300d0210401421140e4040c000605825050008810840e006049100e0450b4030a07c1a01d002440d1a407502d03054520108800c0115181e0b1001601c2c8500c208141400c0c44500420100740c445841c40c131107048541c5074032410610380f40d401c400d8a5010003030301e020086ea8111406104 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 587164109 1250 587162859 587162861
    0x41707052112460e0622091d01050f010302060301090e01060504021911061b1804021b01050109060b072012070513020a0f11010e030a05040905090d12 66
    0x122203001e40c01d070301c802042c1d03525462051012038416003c0c1035406040100c4000401c900f00003580d500e05140c54140321801c0010068000d00c0d8580515040701c2414140d1224420310000081c142e0003003d01c03006120b0b50302c00580140032120311000c1e44c81c001c0002c0c459017007800968102c903009040c142c0345034242280380015000c1e08050f018650f403a0000042c10b902e0b20310003001c40e0103d0000400100d00f807240e00414400714000c0c402006d6024206100310146814181180c581c00c12003069604c1c0c508000b58091a211303d00200d03807042c8041032113200090715029001c9503080c0c000c002c1000340e0721002864201c03400d40c0104c8480300301c02d00c82071001907081000d031080c008012158441006110002036100208408082400d42207008100a03905110700f192081d000342117015030074101c0044e4004c010340d800311009d00170800f000c00ba00d007140c0020740c05056003802d4442960350300e4503a0840070b0800d510500c211a00e580c07078040001c0180c640803e2014118525540b049a52094506418 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 587165359 1250 587164109 587164117
    0x1401082208160c0e010302030c150306011d0d0302011401060804030504050f0d020405010b0904060b031608100807060e0906030f0c100306090504050f0c09072102041707052112 77
    0x10300c2d0040c9021903000b04001e4494078004069088161002c1e60462040c03500348002e8051071030051103a10b0b507010280c0000410740c0e90003a001c3c40c1000070410102c1000741003044480300c0c07640010b400b070840014168103401550310741c4856a0050790342e076a124011903a0b1802180c0243c00248148000d00051900c0903840d4660721004201c0c6000d14400d4001504850084c3d2081031610000101228581094080c00008001409106085140000582300c8400413003842e081081840c00000d010741d0701c0e2000104c064107010080382d032030685421000d130160420f8031022b841342c48004000389040c0b4001402403403801a0501400845100b0000e1140c19001c408180080c55102e03440415042d6162140d85d204a00503001019180c0034a8100c038181403011480c1d50180c0c002200300464143c00002d508007100d4040d101ca540e501525001200034000d41d0020f141c1710360009121034800b240091500b003a100100c440198a00081a0780c1a50802d4114400c40681103a40c0b01041700c400000a0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 587166609 1250 587165359 587165377
    0x30d2a060e01050a06180b06040b03040606081e011401270b1003020702190f0b0d32070801180e03160f0b0603011a040e01060509011401082208 63
    0x1007481c1c06001c6800b825110116903a014403951503500b00144284070030030403d000703080d0f0303020060303600f0290105040e0320035402a075100d280c000011a0070000d66030710410085c02d290054030149140600c4e021001034002400c00b20660030b004051882d50303d0300d50154122102c00ea40c0c9801400c18003080040c1410003403d400040d503030380d524103509031140d00d580e19150300b0580d401a079940b40e034410040c400100310304020741c4a1808000f0301008003041e0b0500c003501c01d2100c1083d01c480506500303e018144454070b00902803401d25078801462041944002100e00581c4001c0031907a60700c03012107280100f4400c0e28503c6480c2c080e0480001501c0d84036040e810803500540313250406400c4001c1c40402c1d8100d04031f0f940500e4031031603030500c0700b404011908560100c0086c81009580f00c980221680f043c0107191045a554464921000003540410000c0a025180000c81c0d0b81d101890040d000401d05003601151645000811108480340d5245055441052100d500b0304143c490031090f40000b404 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 587167859 1250 587166609 587166611
    0x5030601110115060f03060b0705150406060f030b1e0906070e0114031f090b0112051e0c0405131401031202160b130501080603100b040603081602030d2a06 68
    0x100c41401d101d811a183c01500654844c40c0da0050140b40090490350154800130744c17000207000101c00100081211035600340102034070441c1d07403140c0c1000b10041c030740c03540f119140c0920000700004001d2040703001403042c0c0410000b040d20307803101c003c1e0315038900c811902020250821400644003a000c2c0804000010b418984014440a00c05400c00150f1060320925043c0b440311032004010b01c40f295a00d0090965102d05001604403903002070a50b901408200b40019183d4002a089440c0d61200d000e10108000c145009410550b00400b5981d10500402d409840080303038103020300000d4001c944800000605003400380e1720750307100d015019450b00d014100314061240c00340e11020070f002c4664081d1a5103035580d0b5985c0b480201d800d140000503401941802a040c0400503d50340200c0c515800c00c1c1001004a40740403004009401801150001800000701003000504100042c5000d00301c6882034044480e031078003001007556071741c90309006c40f0703450030310100c55100914110b03000740000c51043c54 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 587169109 1250 587167859 587167871
    0xb090403230d020304080d0605030a05030414040e1510060306230607080705060603061003080a12020c102007051b010210050910110901090302042003040c14090601050306011101 78
    0xd4440c051383d03c1a10261782a14000c00c0f0109802c1e500d125220040c6400c034000c0c042da19083e9a41c41e1240654426110600404040c44520340c90704e81081e418501450180c0c0d203480c80c1800702000086040d2951050054200f00215006001c1e20030b07042550300d4252162401420342000408a4951782d2200e0f03000401405428000380551000c0c04030f15120710064003480c9032007800c0c0344c5402c0307004048403144000741404001182c2c00303000b110401c04041c50003000d291448900840623200e4800030816922902d01d8048081c0011740c03029032030000e01d541003c03110201c011007070524022264041c009810400302c1c0c00796082e000e0600030460354180159160052038102c0081103440c01c4a9180303140d0405900c4000090143c820041d4808401c0c3d00f0f0342c184420407000070301c070038501c0c04024001e03541e405506040c103080f400b81c141c141e0305540300740b6038914142c540540d1166452059140948800b2006001482e10342022441108180c0d03c440c2156605801102c040418910082655580702 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 587170359 1250 587169109 587169127
    0x110f0105040923040f120309020f0409170301061d0a03030215102102010f0906020c10020a08030a02040518010501050904021b0708011d010e030d0207080c01050106020703060b09040323 81
    0x1660b2280700c4d60044041c1c90011644d4104100b10310780c0071252004252a0104100041c0d461180000c13843c3c10550f400a01c2c101d103850010044003810102104040003c000007c07a141c4c000f58610300f4010040c004d01c0354203e040180090708005001c0200540c020485540c3c1120320700b01b800d80d00c1104000c0150300c07507582d9800e2401d54141c1004a06800c803501c038200055580194000c04c002c1003034034020002d1460403400039240c407070421005102c0c210b460303051000907108021800350b00781c00054a50342c078208840d60100950003845854024080507201c1c1d11620600901035041300c03010b07150300b4a000300340f204010095000c0c10106000c4844040e00c19401d0b28100084400380050f000001820b98202c00100cac0e2560324001070034400c0c2c0c107100124000010100c00c0da40804003108016071581d00d1460000c0c1720f4001e2009010b529840c2800000e01c060340007410200300ca010b810100100303151718061100a06088502901040845187c1c150f1105460540440302164402d89400d021400d = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 587171609 1250 587170359 587170421
    0x461b1113060605090a140a0e0705130f060f0807081b0c031909090b01020714032e051506070215160614010b04080d0c0302010902090112110f01050409 66
    0x54101e540041c4001c107502602e03041800304803000c0c006c0d91100a070411640c80000304040c00d20b0044ca41c4014004021401d0380740188183c48012415407840c0380e0701a118020b002c0c512416104410008040c0f03a00c0d901064080c1c00c465000d09020343d220711940d0343d8030390350305200c0d0107074100c800d25000200700d040200c00c1c041c00a0410311290403401c44e4811300b40c010080100d107484c1c1050a2462401d0a80f450980c1c00244060849005203940c072140e80206000905200760346c00c049101c070340c8590408001035103500c401c5500381000041006a0746880103000000f14641c01596000b0504101640151419000518038220240100391418040c0c074034059a6115102003215460784400d12400280103401d240e030701515044442c0e9040c1881c14991960361100221007006000e214510101498400c0d0003200b445600944184c3c0e682d6580e42a03400304a4840350f00391050142050303802da40f441e2002100d281110140d6515051a050001c101d00130424240000e41c0002c1c00d050b0f186d481d140e8 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 587172859 1250 587171609 587171621
    0x105120702030316142502061201080d051603050309070f06030c020c03190b090f0723090c09060c100c051306091a461b1113 55
    0xc0341c1c082c5499041084440d110072000134412001c3c04000182d014083c042c55003039400c00120419440c600802189441640c425420806500002d0000303020080e02208031440b412a19107000301d8580882c0c49008a425010310038200c0c2c400b071008801d100c0402d1069010b103030400c85d01815641c460703981d8400c07640c000101c0e030300104c04607840b43d00f50324000d5010b1103100b08007901500a403010382048070790000110300200c0010048196040403400f072400400c94030a4001c0c804046940d02615250a01c4070790300a0f444803204100c90110780314990a05a600c640a062540910382c02d2440c800f0400c01b468014141500140c4100390650303403004298002d1442c207404039160030759103c044070510560821103070089000e1002603401003103d280648410740c905040940040d44038602e21015489081c0a12003501150750303888002680c0e041c0d132203481c0c0c0d114101d1301c00040340034008010550340a001c094041d820b10b6038114400d8081915000440b4034950010141402d20315960200021120 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 587174109 1250 587172859 587172871
    0xd09030324080303011205032b0b030a020d0b093a050a050f071103060a1a0111100506031c0c0606051e010311090d0f02030709050c18010512 62
    0x1440740021140029071218400440180c03040124169003032402d555034a22040c41505002c490f00c0b2241000e200007401510100e060144082041441032120400c9064036500c90b07610003031808880130024500058403070342c1d42d0342c05005000d130041180c944100c01031005140c182a40a4080d004842e0560111941c00c46040300301c4040081040404651810081c004140d007405001c01c81c6203205a007120a44a2603003040c0e00c1180d95040500c1e00040e04840c0000e0030f40c06204401c00d000e03c03c1071540001031031512902ea0a214111a01e004464140f54444d15016a402a0300304598420313207608080d5105402a0803549541c59104c074041150490940c243c00007140305c071a04c800c000241c0500d000601085401200b1000c0028030207000820386242581859902c4000350364a1340e03460700395105600d004140300101e04081c03c1c10480c54031525001c9110f40100c03800483c11040030f104040c0180c141310f000c54102540c145d94103184032020340c1402c6c1032020074041541c0840d00069902c0c400c0d6 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 587175359 1250 587174109 587174111
    0xc0504020f0309010b0901050a03330c110120280f230f031f0f0f09140103081309290a082a1002010b13021305060702060d090303 57
    0x110f40300e46000d00f1200300f9824a441043e130030004010070790325141310780107694000c0316007041c40391030080200c541400440c021400d21042c941c0c0704240c11150380300c5203859031941c0b00c0f6003040d008410000c3c200d82c10007408007071003405805030428000700d036800380c1516a80c13000380800188605005954031081c010f200000141d186c642856034560052a0150041480030030000c0754196241c00c50341030060f2108100001004000105490640802004070b40c0140090020f59074076400300c1d0b41701000714000c9036030703922070342c00b0009041140b0b101d00018a1086600500941d0843e42d42c107446a000d000a0300c00844402070100d81c1c440740e4420902018520704080c540c0b003000161003070810008858052050091034020800008003140498107810305521141e001c1c2082014003605070500f00c00d4581003080441041e00d071680550211001c46070803602c0715029049040c840d0181e100394a0903041084407500200304a0900c1c6000d0b10019100409541c10011140491401c50320707140300a070002 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 587176609 1250 587175359 587175361
    0x32e15090e0703021201050f060603090a02090408030912040e07230412060e1f0203090a1403040e06091504020706060909111c0f120c0c0305011e0207030e09040c0504020f03 76
    0x10b1925050900040003c5c3d4000c0c07005281551003600603240003050b290180c42c0000c00604581c3c800d10900f0f211603030091040d00c140c1400d0405228941084031031054510407503009150710341c40b0400703a0381250510a10600542d4905004a8225440240e00a08a0b5001c43c280200d1800301018002612880c101020380d006e0398106602560480f0300c8400150300520207410700488000c250904901004201581e281c40f0420040c1c03408240100241c01540d01d0703e88416400d0011004001b10303100f0b000320780125210f0030b040241c0d0a809079850705050500c0040d000306030034140c0245c6a441c4c014000001c01583e111545020744010880c1100e201040a01c1c03600e1900d0300620025100098800d80080711860760307141154508640800340540950180300104184600e403908803880d4821031100310150740e4604076010301803c2414446007591582c4000c1182d00c14425551030350741655444892200080030f0007003051010304107641b88000d0950220b0715880d540002c180000d1813003013076aa6 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 587177859 1250 587176609 587176613
    0xc0c010f0e03030901140d06120c17151b0a0c020a35010209062808041505070306090204060203043305280e032e15090e0703 55
    0x44a00c2090018003400a40c1c0404402500c00005a901a010a0804064080780095000d0b41c901940000300840d070b080210210f901461481f00f10100c600c81c142ca07038401529904080850b00f50502411555801468001110141e44000c5604203c80841403544606544c00600b03c5030311a040c540d005c1074a4010404c1141000c82c80c0000400694841c05100380000600700642a01c860030030100c4100d540c148182000c0c20750468621000c000d103561b5079410903001200701c0c03186141e0300b25a0f0340310010302402114052a0860303c99681310244100c40485061420000c1c10050000c0d010103985680110391341c01c4500c0180b0143c076a540066450b141340c9204500104552643c01c40060701000002d40c2c0b0011007404079007070100300e00301162110b0348010f42688143c01c80c1d90100c2100660500c01418641280b15161103c82c141e050740c8240b8860b1004a40c1d05c0d503071a2b0205c1d0500c41d03095a078144480d1039888900c0079407082410444855482c0d0380740e400d0700c8206140b19400d4000c41c1003002 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 587179109 1250 587177859 587177867
    0x5070609170c0a170708060106030b030d031404022e0809010c050c071208071703010512010e062e14040b0a0308030c0702150c0a0b07030b09011205030f0c0c01 70
    0x600e0301407000003803240d12402000f03d05a4030aa01c203113581e451403488240c0e40c80006000e5000500400801c4854540c0d41e00001005410704014080c000d00640c1d80d406503043c402d0040d44c40c185030316020f5180e140c44942c04c0c803ca40d030204030541c10700913007003480318580c0001025007180b604640d543d0010380e0900c0a00d03142114449401202401802c000b41000d1500115890084800315102256003140c9414041c59501c01c2c4d01c4010441c900400340c0c00010060040a181070716001c1d100c0007105a2461480e41c01c0340c94960040ca100c1d4800400600800c1864190600d03640440221546105221540381c403880c9050b000158195282c4030000c12600741442150f039039880c04ca4441070218610b0311100c00e244806001030308151000a40d680641d244c141c50351101c45424440581d841101082d003540f1010042000c44039400b0103008030f038195110f801030000c548070080c840030103a4a07207000124986030b2268201c039140070510400507880281000b030203a503220180900140c820042c0010 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 587180359 1250 587179109 587179139
    0xf0f0b0a0b0a1202040903050c031c0b04020f090f0307051302190e100810030c03050a030e0411040e060415030b0f0601030603230c0301060923010302030604120c05070609 75
    0x1a02503003020300100503403280310b20f2111500307805850014659580f03040481c0c040c4191070242425100c001b6800314217582c82c03460413003814080c040400c429031485080200ba03102c0c40c40f08190344801400300340040d140c034104100c1c640400808841400e540c46e03010944040050b8070002c01598081b071a0980044040c40c2c0800381501441c01589014800300003071421694a803450040014030000250380002c090304d41006140c02924501441d5900d150450b81c8604040f8201e00042c0102d452180030708150003440c2c5c400c100402d0450034142040700071061210300400d456407245c1c459441d07040d05420004460081c40c00b1300400c007564940741c001c1c610184c5020b4002c90400d850941c3c1000421510340800c20170b441e000c0c0c0e1008074400d14503045803801c1403694200c2c0e0305500e40440010001c04680c061054241c10203074903254410440b03d0405400c80034440a90142c014000180c0082c18224039000b108040d82401208039641e6210303079182c46c00540140010481c850310621203940001028 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 587181609 1250 587180359 587180381
    0x30706200a030c0f2402071202160501050c01020f0301090b010f020f191110020705010e01030213030b0402060415080103021e0d0b0c04080f010c03180c0302010c0f0f0b0a 75
    0x5152000341c40c0e0300200361809100019241ea0360080750003080014040e50302e0107500800c0d80790700d00c5040040318040294400f60301140c5c000580802c0d81c001c140041007440b000c060400940c45510314140065619601141218100395030800c50741000c0c1d0111405180a08018030740001c20803891000500158000300600c0d0555001c64607003a2460000181215a00c1100184145107812803811800f08032601c40201e0380424030a9a40400645c0004c01004aa000361380342c9a01c0e800311401542244102809038045110410f81030002c210840d40c0107800900c054801490030ba0f441782030400580341c420156000501d01001001035250a000c00004a180d4210301c50910620000188003140303004070080c901881c0c00e00154040b0a4442554000c14024050700c1442415852440c024a4445007200119180215100c09201c0201c42c080701f487c0d200240c56801402c58006540d00a0f01a074103c804141c00084200092000c8074911440c80c07058859400c10300b088440c603001d80d174400982e = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 587182859 1250 587181609 587181613
    0x21509220b060f0711010504180b0306100515090a0b04080307031d06190e0301090303051006090f09090816030e1f0e010503190e161509060e0f03070620 67
    0x905000c14034030030100c0b410650700905c0f1301c0b00f84104070700507a11801554032241000101081c44134000311590888500c482d000c40c00d407605a0f136001c11410489105019482e00294408070200c0903020890050224a0004040000b070503942d1540b005103034400e4000b6015500045006410550003d81018005030415000f0500e000d80a0214406001d0310b840415003184c12443c4000c000c4c080c1d6078601b41c5105c054001c1c000310a0728240500035120503101c4000050b6110000100644501c8200c03041e282c0712501010010304d0140740001801400360182d825200802c44150030080c01c1403160b14182c4207844071031465080030308110050002e440c4001d4829003417548540319a41c020700d4402191403d082080c0c49803106440c0c1107141e103684407025141864103045420195000464612141144488818554540b40034290400403182540045014144207001e404c0c0542d150000d4000090088664038070018000f928000155101d40302040510900700b411030441910712900d4251540 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 587184109 1250 587182859 587182867
    0xa11010c081b1614033001050d051212011401090f381e040509010b0705100f0e0106050301020f0f09060d050109020a200604021509220b06 61
    0x40c480282c079450b0840c50703100c0030001240942d05202d0301030780d90f10035041a0044040008094020340c0c9a10000e210a019090744500301d2440040042c20701040545032800501c030b0346808103100d40f44102e00c0d4215010700903c90300710b0103400000040c0035078010740d80c901d07906035141041c0260108589101c1504000000805001d8002030800a10442c0c01d900307050009191401841713041880c528003070f04040c8041565a10750495480094001c80424001000d1442c0705100003410794402c0c0d100b50754000307224100401071101c44201404000c1d0090050380c16071200031782141c003221141c003036aa018550703401031a07240d84001d10076100a4501507000f1407a01503480e008007018010014044a01900082d00d589581c07108400d0310300038400c5504c28010b03944c440400602940040040b600021a500540380b100113015481c96184000803001d440e03107407550740a1058030300c0a0075441d074400b9400c00400c5826120303c0e41180000000c28405c041074a04241d443c015158005e41540c0f01780000c0c4 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 587185359 1250 587184109 587184121
    0x90a02030607050a0e0301020415030b0d0b0609190c020105070207050301020c15040c0b070804180501150e0616050a02090f06130b030a0206030c030a2d0b03010e030a11010c08 77
    0x2540703a0440b6240c200981c490790740c800100c2e410303102c01701c01e5a0903500101d03000600c2061480b80e89031000d115101400300001602c1800191240d00c0405042c040c035140c080b5584d810b01c280956009024121180c01c00101141000141d42c000310311000140e42d00c504118007582c3c18041d400192008900940c640324031910f00c507940d82d03103801e001502c803045003012400304504083e17100001d05503131035042d07198141030404103542d030000c4c441c20304011b080c161208001078041c81404e061382e045808174000c0e2807034070008a0314881c07240e00340c0360450b00400c00e1300719420403c05154031051160008003483d994071310502445c0c0e040504618507030300ea6401488201c0e9106880c014100301007010010b8400346402c00079140254020000e90010310001c00e0002018039480110b115501c501307c28440d00442c50142006410b41c030184110350181c1c007843e80000c0065403c0201c00d070388001c00200300743c1481c80c2074a055502c401749840100341c0031000d0465503502800f91341044072550600c60f00c0c901c0c0c50 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 587186609 1250 587185359 587185363
    0x30b0603150712050603210d0c18140d060f0f152d09020f0c150f01210203060112030909051909061401030809041503021807020a1703010e090a0203 65
    0x203201402d0000f510b80d40000d500303450400045002e4101c036079030702c41c407c0741d000e1410185070300a05261008600b03145032031a002e401400b00180c1d9545400c0300e4040c0d5494844142c103880964602964442c90034840100840c8550044501d1a00ca52000041180d40c04d502d8a00300e40030100c13459a56007111204005160024508981f044050b41d454044803400c1044407180046036004403103010b101150810001c0c4040016140354001c07030b012142c401a50000920a183c07003102c600ca003c40c1c203c40140117100100500030320708101100c02001c00c035480e500082c100f2000340c02101181140c0e0348100c05265120b58114010031009070b003000b10b81001000d14402c4445442030411031a1100e5075081002403a6006c0103101e110001c1a10a9584034030b0090940e42c000c8803490312a07402c0520550403c6040c1041404a0b94001d12690101d10032540c4062800da0007001e40040d4061114140041521103038920205e0100709820b50b600c1d03041000c03558480b036002c0c01250b17142d401250241c00503200 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 587187859 1250 587186609 587186627
    0x605101803230312010e07050c0c0f04020f0d0212060901030c05060a1e120e030a05041a0702030a0c0302031002120a0924020409060b07030207031203090b01030b06031507 75
    0x30344100180e500310300b11180d00d00c62582c119414400024103100b210452500d5038141c0e5181001c0c44400d8803084001c0b00c4900541c0b841140341d801ca0076001e58103103450110201d035218090805403c0660b103003403510031a04000d18181d4255000a0301041c441c21640c81c040e404941120030b0002541183c440c00d000b060280603190142d1000600c07075003101c0c001d2007031304803407003285580c2105c1501d8000010105076015210341c032014107007041c102d440d61003c0250f40e089829650b0303150170a485c1c10f8243c4403041c1100c000d00030407034080012170b000d61414010449481d001b94140010307540381d481410303c0c0003841d2111210182c814851107002401d061200c0ea0804282c0700042010019420310303980d411614145003400f002030010ba030500701c009070040c00031115000070400c081a5076801c61401c0b03220f003190080060700030810900000700202241c1120134940e10340082c5c030746003e42d6503110395030702a041550414031280030803500740742c20414842d82c0d040c148400c2096080c423150180000700 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 587189109 1250 587187859 587187863
    0x309120c0201050d02030411041b0c111306170c030601140f032805101104291b0607020c09130f08120601021e03040b0309010b030d030605101803 64
    0x1203088694425a8461402ea4100c8801d00d40210b42d03034280b174900740e03181c0c55000200b24040c5090169404400c141c017551180d581002c1d0300c6908903044555030ba00300000f81b075446140e0280c0c0031203000458032010300c141c0c80506003a00511040c2c2d42ca44654500d8107110050480c865404540103100d0301e081030221031045003060f243c1c1403400031145d00180c10092112641400500122005494a030100c0352000d0820b01603820b403500c00d05402d00400c2a11000505154000020401080904400031544201c03a0703104a044911804040c1d04a10302d40c461494040c2000d07040c0000f602940080c004250000d0050005280a05a08002c501c043e0300040c41e8161000c9200c00b0031042c0200020424001a03210300302c0356503041c025040c0590480c06507203590051149206126070844000064000d07080c400000714281450646814061b610081c002d0045548500c07091190b5181046102140961a01c0100f0258100070512045500c1c01003c10b00f002a01d411350803101c4503111080040d26 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 587190359 1250 587189109 587189117
    0xb130b0901060828060e0115050411030610020709060803030415140c1e13090507020307030206060d020114030f04170a090302040f0603022805010c0515090c0612090d030912 76
    0x24582200c91050341130b6481029100506000340302c020848194043c03860410b450000358001768803001844105d13130f504031410342c0d0382da0200040385031458403c84080d0000d4003031045801407a1281802815208158444005030b8004010f010801002c0701c071000e410341c00c81c101008004240c01c9010700d070820140910040d03040003d890300388520070760004101040303000161959031120b0f0b030300b100c281c8103503105186901d072400c004551000d202004880159805600400c110744030310003004410000c00d84101d041c050884c04003524100300e1702c0a9880741c05202c03040d590514050a203200e83c4500c1029001c2409020040a41c103e5080843c1800742d94060710002100031035918420010182c540010754409200d019544104444681c3d00120747c1c64074401100507030751400103662400e84800000c0250300007000d92030352a2407084806600c0412101190a68a000004204168004441400c0188001003004000182000f07540704104151901700941c500301d40700c0c0901590354510000400c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 587191609 1250 587190359 587190403
    0x10c020904020102010204081f0e010605010c1b1d090d0801061407080d05130302070905060f04090203070b0a0306080c061920010f0507300e0a0b130b09010608 70
    0x50f91003581640c0c007515100c2d048407200781d0203080d107000e0914035024540d241420000240c0139604c041c000c2d8001c454068540740c8020768195a15045403203403600408840d44200c400103002c0c00b040b4610845010010760414072030600040c3c0500380313020240c03000280207040700100032555101019034180c01074900c1040d2501c04610b80a02c0134465048100b0805040c00244400c40d54002da0b0102480d209130200d0300c27a560341c0c60f510310a5410171149030354031858009017490a42000c0d000181881c1c80101a10021902c81c0105000e80c3c00600300040042d079140401e200c80802040300d2642d64504413049810f1560201109400211100a8804103c506486e0f0580f80da20040031841500d40800288602c444244c4500d0042000310781603800114503125503085100426034000c004c190320750010030166440503400700038000e8020610204c0c4600601c003408255200d40c1e0754050802c0d448036a04552181c10b1a400d50a0003900911360369141c00004c010705c0c500000c0c3d038004910407801e0f0501e4 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 587192859 1250 587191609 587191613
    0x105100b0a1206260106180f1e06090b0a08060c0c0a080301080616050304110f031f0204050102210703030504030c0f050f0d1403040602030a2903011109010c020904 72
    0x107014400000100c159040110100380000c49000f082412078080c40c010100113544141582640d02c0c910038046170118206440103a15102e412183e0103014580c004214000c10034103814002200c4001600080da07100802d01400c41d46000c0c030f441d0700c40c0440741c2500356800d2072000c0e0f442e002c014221000002c00012040e00e40c00b03061180e14429900708100039180d40c0c0d030b42d01d040d49a420803a0a60000c2c14104440e49245000c3d03019280500d4000c0600d1403007084000c103000c039144584004991510407210340342501001400990b08510106030050786651900c000649003c140c04400c00c00850b102800031150280c43c410340d400300360507180c04603085e211070605484150000d4005881100385d400c0c04024090005a40c2e0524000b14084031030044008108883c681007200540030076100800120b00460b403180c0143d070704200d5510b4000b841326200780c92b0320048603084c86480f107031fa82c000341e02e03174884e03d000e20808a22140c01000c0c1450003504500003072200030b204900900c0303030002c0404101 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 587194109 1250 587192859 587192867
    0x1d1212060f1f081006080402040f0204122108010b03041205210417090d06051803040305280f0b0a14090a140106080303060d11060403150e0105100b0a 66
    0x200c110050702018103580c0302d07610240c06281214082c0e0200d00400701142c480b20100d28003504548503a030b10086240c0f1685c0c2013102a058450042400c03c0d02070001040151400440513a09445845403401003041d0341d00050001001407501010322511f034004000800d1000c04403030340a41e100804946550004070292098018285d10b100d2040c00b10301400300424440100902480c0114403040c83c2c803070a901c8456180c4988162150441142c01058000805580102da04590400b103120070354840c2001c0286076030890751081d242644110355201e4408541d814010345856042c19000385400c2c0ca0f11594980c14050b0001442d806021000a14105455110143d03080768046a80c0542c10710000c0642d484003104010394070400394089c8030001d0300c014840c5104031050400554215a1000c00f04111181034850607514400100d5404000f951034400401c0614442c0b400506041c82c600c094804036661503106035003503803400c024801c0c080d503c0082541151040c0d60556559805814115 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 587195359 1250 587194109 587194129
    0x3030f0414011410080606030a200117070c140106080705010e040209041410080307020f0405130b0c04060801270b060c010e07170706091401050712031d121206 70
    0x1070303007824002800210350380e11044001716140300c2c080711070303544502d07041540f600c80c1c11000502d01d080c1c00d019409440d09107c4211010081410070078500941400c03040152081200c41000040005055000700410a0754100680001000802c02c0d20300b0881e03420350701d290078041c2030f040c8030582e2002d007a950b03101c1c0c045400145001c0c10600a04c0b100700c0789121601810358015151010491010540103000015903800350b4004088850f00700300714042c0801014041c161a1082249400b01d401003202c0d552528082c150354410241c0c2c50740740200c0141101d8041c0c000c0014040c5201a0b51440d521b00c0e500025910340000001440942050025031030f4850904e07040903650034142d0307500150340049030f414100d903000307191001c190801d502480e03143c02281c010f55002c111350440c2400f504180d00b41954a03c20103050032450292561034101e414039010f01d400c00003985504155201c018103a00f41040300c000701006100b94030490120f40a1400380c0600030540b0308400000541e140e035440311903 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 587196609 1250 587195359 587195381
    0x151a03030c0c0f0d0b0109090f0203030309030408070b04030206030711071706011a031003030c060b04021204110a27020708030c030103062d09050c040c0909050903030f041401 77
    0x40703588110429403203807140e0340c0c2884070f0711940000c0d9102050b414001c11105255038002c0d055410b80e030a0100c5c1c8070017020308110584401e40050103a0f001610304000a5018a01e48230045445501c0d04181c3c43c6841c4140d000256081d505000c100300607212542a243c129040d820003120701d040003c40c03549031544c03030751040e02c141c4141100600d01c2c40d008071b40541070301c2c0c501804400d0030f02c560320300302107601c0300761507100c54040055010000309100f0140c411000f440340c200813030034180c0500002c0c2aa00500160f400a040020a00c4100070320140301c1c845050003a151807000d03a240210004448201d1611075041003000c4904548064941d8111a8081c2d80008411b84030308200c00c185825400c00d01003180c0d0903141080c1c007001e4081c030740d21503d40c07591502c03510703a11000d2000101c0085c00404004035414458000306040940d164040c15a0001c41581c0c1e1280c0145400d0a520640314041e050200d140c1007081485400109840240c1d40560081e004005000e8540c00090040541d541c0f2 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 587197859 1250 587196609 587196613
    0x3070b04080306220903020c030714090c0904230a09050c19030507030b060319020310020d020d1d0d1b0b19020c0d03110a021b1302180307060903151a03 67
    0x58134403500742a400301060a00a50842d44482c01117002e1566607000ba0155880340306032600c0203002c2d450115a140d030b128480c086020700f440c2c00d9101103403d80e07101144459130040f00840c02c5030741081c50402503a10541e000f03000e00c280c15643d02d481d900c0e407031000c449078003841ca0003800c15014071144088030700071540a01103500883da42e01380090303c01810340304640b1078051110300c406c02e905100e40f0649443d070010081d02208054010340310007540040c4010441e25000e01846c0c02040b0b1600c44e0100c110107606901c104203040e2a88142404444510282400707030100b80240c01c01c2e4400344401049500c001468019181c401c24003640c3c00a8240100c1994000500c418000a02150400107404140c03414480c0b000504040c414600894140c0c00040c3d00c40d9250f918801094011f14903d040042c0c03200d141c0c484041d8140c000d03680902403210b005007207c3d00e241e642d070400704424002407800d850119101415940d804045003030200c0e50411450303c41c8035191161402040400c0691343c0101 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 587199109 1250 587197859 587197909
    0xc05070f080a020606030304240e030a0b0712090b04080a0311032a0403110405040305130f030b010503030a080c21090a15021903150306060b04150203070b04080306 72
    0x78100000e070340300310240c0b0014020500441c2643c180001903030151036190001c1c0c000c921080b181d1602c4010b4100302601041104d0b07407141000c2d2428060501e019000700106086481e1400d4060b00c00b070900035004a0491501030200f011443c54440e15400c664802e2a1030b90300c00180384210b000c1c0400d40e443c288180400420301c41d2040b880d0445220311a0020085c00020050491000386130090340300217820620039607c4080381e0f140075800158410311a003449420480c0710711003145202c40d00d801184240100311403d00901180b03030590307801010214000d41c5422601d00f0024507116000d0101a100007000c204000d078104410020280148140c581d614036140000c0d2040ea60340c10b160055540e54010060151150014021241064076034008051410624401100104804400b403680420f07516000702c0000c000f030250034024003400c2e400540f224241003210044141282d00300c07042d03600070025070300003c0d9046600c0381d12a40100c1c2d400e0b101da840c0ca002c90000710840c0d1030b003078046039401c07 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 587200359 1250 587199109 587199113
    0x306030a08121608040c092004080102042303070509070909111c2a030f1104030c0f060206240a090c020706020c09010302120f06070e13090c090c05070f 67
    0x2d5414400c04800d0244610029042d000762114901900c005d00240c4c00400c0500120305103401100800c403c101c900c8081ca1003d80110340a07800c240c100102036500007400b00651030744064074013241e00307030070185050030801c5d0300000c2d5a4843c4d5104050090302074500244041317000f0f2080314010400c0707150a0180c000030603400b40c0f550b40400c420032485440c41c002e4214100c80c0e446501c1d00c500350302407128640f4203454100c481025220a0b00c00405840b8289104442541c0c0620800070b092920296203507820340c541840c4010285c0c1010900e44034103541040701c244d001074403507000808440d0b1001d00316000c40c81c914141c14030f1101203800400074540001c00b1242076110601c00255982980c14050f20350130200d840d4050003070308a0b4008800340060000d03242c40d202008118080b0021070700c07a03240d1b4466482c1019001c80c0c440c0c001c500e604154a5440c2859091415100e984000070404a0416601d00314241c82d00d0044806280e0b03070b0036000d40c0b15801501190700042c1c000c2c80c0700741709444074 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 587201609 1250 587200359 587200387
    0x30f0210020a0c0c0e190518160302030607050c1f0b04020a0c0605010906050d0b0604021201030c05010207061e111207081c02030103030c0b07021606020d0f08011a0306030a08 77
    0x910f04807030400c00d04900003002a6440b8182d401603c2142d22124040c3ca4a4800130184c4400703020181e8040b02c101c0540c04020341004101c0e001203100e10042500c519600401d810306800031301c00d00510a04101000c0c0251010502e101a1a90b913a0646611014001c02c50018802e501200d40c125100045201c11503403c030800407540d6220300020300c0260b0700d03409000d0a945003840791540203090410700c440003962240704242c2c000760242c0014102043c0c410b80386070708102a4030507945900c4808080c0020750303050121030098a120304003481c00240171078000b00e007030f00c450000008000c00d41250001d545020700c02001d0120201d001a52645003505045641d07611000036000d00d040c8115031140c5111250007030383d04890301501c03003180d804041e0301ea02d07984a40003000041103020710b0341c071481c0700e1030b02c2d2604a0141034140c0c020b0924042071500503100004070328100051240a000400a003a131104005082c40d00030100f80d52282c41c0c5401003860005540d0006040e241c0c00720340c2c95040741113 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 587202859 1250 587201609 587201627
    0xa180e0a0e060702010b1005070816030f12060e0c03090a0c1707150807120b0a17010b0f0a090c0509040504110108160903080f07140c04150e04030f0210020a 69
    0xc2a02602c2c202c2d2202c0d0400d030700301d5003d86151500320f9000007002035518041d0001d00760042c0284005840c186c0e1001d900306d801e074103070071080340403034880741910ba030342580849052003800314281c0410a4a003016149410301c4002400c48029460010003d61344000030303c1415181d80d8407284d405045615541e40300e1419001120310145482000400078500c000711500d880074900585607010b0355210518200d6980000c540c100311001e480d110746207203a0301c440301000001c1c01c810412003c1d140820945900f0f541d0341c001098800ca52032009940030b991006000f00486001301c1e80000d506c01e0600041c0c5543c000e41844507401481c0c44200014070400400010000c0002d07071b507008007a41e4404488244d16064a07036500080c804034018000a9034070380040c51114500c841d410f0a20000d0b544028401c3d985400c4203003107821520307103105e6a00b0300e0301401c11089005440704030300350300b0070040002804d0010000780c2004189001010401e00031b00c4105501c0d040510107560720710b040d100c09009195 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 587204109 1250 587202859 587202881
    0x305090a0905190516080702070308070f0606140306150111060f040201090e09030301051504080102130e1303080f0601091a120a050c0a030e28050606030307080a180e0a 74
    0x14155030f07901031102a500c100791054140100091440700b19800c211041e1000a0082080d0700c00c1880100100e070980028040322403084000c081507101c01d280050540c0e05c02d40c00340400440b0396060f104680c0c1e020a05a6014941c20340c2d010750001000c00488810000482d04e000f1401458188100080c8194074030f88254001e898200f50306555506178001c88008a035107034015003060005000701d18050300c041c4c0900b0282119942130a4441c0381c42422a40720302c03818130740105a04003c200c00200104080d9200c0040e40142150a55544002c2c1c85894001e001014296402c0300040c0703503a00480780c210250040c02001107007410031610b81002507015142141c1501e200134001002c9001e00e00a940c8141c214921541c101a5110401c3c0c01901c000c142081c60390040c0b410400c0c5040003034422100c0445010074200c0e00a002c0c1c20842c0c02c0003005000e00340079410400100010503213803000c640b1800800d00c3d0110034050f12804a04034291240c10042c0303e401520244221100780b41c0102003045 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 587205359 1250 587204109 587204131
    0x705091302040914041a07120204060804031719090804030c0815130f021909020334051c0608011b0215010f1a131d0714070f0305090a0905 61
    0x84c0c808034110106110469009000d004098080080280030001494001005082c881c903440b001c40358034026a0001c4d000b54000500741d004000605030f100c40b8009092864850152660034110400100c2d10340710850881d410703880e03a520a041081c1c01040b14015074016182c841c0c1c440c0c9800781c40303031100e03445031390307040300b4035560011030000303d104400700e80d4040d80000048802502c59081c080b03480282e18014548102c401d00c000703001c0803940021071065032121102d01d10700c00103d080352040240c100c000400610000380f01804a608101220003282c0e0305456098002c42c1c1000100140101e604569041e500300340000401c46013402c21402440c840ba000c0e5400710070320007008051620240700d507250f004c02c4114100101c000c3c1c624416060515215600e00d4400f10810841484907564440060b10613018000010f00c204900402c0d0840180e280450500c41c0144507994a03000d00d54010f01b880c6c4180c2c0c56001094011001c5840607440940b6981e009507807540745070020101255143c00302 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 587206609 1250 587205359 587205371
    0x30a14091c1b0b03060103050601030b0d050705010f021605061c061e0501230d06080303041a0112050a0204020d1e0608010c030b010512040302030f0d06060e010504030203100507050913020409 84
    0x90082c445035800e03541842401811642c5050046020304005030585044c9940c0e82265200c40d1514400c40a90500950003803001728a080001426542d0122120045401418060302e0200c10340c031501040300c030f080f075030340d910b50005000201c00107200c0500212840d1500d00e00059104d01c07090641105030b141000c2210041d544c90055407041c0c82c030015446130783c1d150740000d03824038000d00152080d166901e000151032611a132a02d4910703401078034155244801c41c110300c2d40515518005c54090910001d0075942170722107a40360350381e4140b40d0200a1185030003240201c0058080e03805032f203a1454a550000c9060f0104020b0340051804d4040e124495007010608001540640a031010201044c0d51710361400820a00401c6aa8000303041107003180410010100c1c81e640d0b8401500c0c480074483c0c1c000900a16003400948060040d40307070141445410b01007040540e0b0041600c4603591681e0a010600e9982c0f40e1b800c5606119040c1c0e599400b1360300404800b441541d81d2f011f4015160b810340200b0070 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 587207859 1250 587206609 587206643
    0x6060605030f04020904052e18020a0b03070201181a06031b150f120901061202091f03060e0c0901090614011215030f0b1305030a14091c 60
    0x603110850790b0030094601d60b00480c2c010304241c900a94003900440030744407841c64003c134004202c465803504401c285002e0182010b0740e80244200c8a00c1d50b020340030018100040c1d804101c110089205e03003620700e180800090030050013900b01030318071200700c4506074002020785400380e045080c0ca03030041c030010000c00006101c3c1c180000c07048211140c50a4010008240c10b003004500240c01d150038100b02e400f03026422a090408000c1d0440391418070344041c081c80d145104a0031151154407040a14042244a5001da2200c2c4009600207002003c2d00401c070100041001c1d405183d60b200400c0d40d0700d84003110800313803008203081d444c0520494038071b41d103641d0303510b48441603c8581c060001080380c420789420700c40d80280442c003020020541c0200340d101030080c600b08c00191036802580c100640c030504004100049002c0c40d8001401040c841d842c4206480da00d40d24010380742100284071351003441d001a001085c040e9024010700408402604a07681c527141400041181c0032500325803c242900740e = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 587209109 1250 587207859 587207867
    0xd050a0f09181a191805040809010806011e18290c19060606080702030307080114130518010c0f0f0e0d0501020a02060411010201061a031806090703060606 68
    0x1120001d11051855480030444100280250885041c0e0030001c0101825240c8070001c4540704001c078800a031311054581855000818400440442c4161501d01007000040c0d020095800078035082c40d05c181c03141d0f9140d0041c0c9200600240248802038580c0c1d001e5200d9500c10280d071045000003040603401591207104071010003101042c5124a860940298540105d220280001000300021952503046170103550320100c01d41d002c1900d540e9151441400768540000030550484854801980307549098140140203540600a002794100380620140150f07540c3c41d29180e06440100c0d041005082800115038150000900d00b4003d50074800c0f100d20680c021a00c00901032020b032541d0801c0c6a01c4c0c00c0880d034240007881000d50001614110902281c000d201074250ba4080d0f800910321804c09052801c0481b1450031201d045a0400b002030000075481203c819148901510498403030300c840048514441d100c0c8a18005482514100915101e000424a003240d00591003040a03e4940004607 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 587210359 1250 587209109 587209127
    0x9110120120c16090f0501150c0605270c03060c09150d09060204060e09010506030115030e0a0206070c030b06040c081f030b0a020a03060b04080705120c030d050a0f 72
    0x1580d00078400404501c250800140030b102d1500c002c0e16045400d400204025410503002504400e60751142100950000d1144601501c0115407203154400e003a04000c1040c94500002800142c507407020074101703c40320b214628200441280c101d20b00500d4284540d5030214650840c0c80b07489110042504158ad14003215001003028228822001404412126a92005004210055030b0b0000240491411b03c00b61000d80006e90310600611521010030618880c1a04aa8800d6804200412080c1c1c88407100e4076011901e42004201a61000340c50345c00d103003075210042c0d00011f00003250001c000014020301c003520f00c43e0b001c04000392681c0c820702086818240009000c02d080c1c40200f081501401c43c4c20072040040700000030465240d5942008244003078440107051900810101d1881e40c050040c0d201414035800c00b24105440c000c0d0140d80c2d8400d6100740b90045007001028401250b040c00f141c9000079000d0100e0700380c98000c40004021b644901001c00018400d1654002044d00c40c2c000d10b = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 587211609 1250 587210359 587210417
    0xc0c090408070f110a090e0c0901060210090c120809030f06131e0c0602030901031805030d0903120e030702011209020907050a0c0c151b050619020d091101 68
    0x741021001e41c0e82a4207483c2d2580180d44904400315140002c0c3c1e900d041c58406000b1141c404211048140320342850510200d840c1446084141c006204013a80001d28010071140075402141c00f0b650340c10711111041c3e040c1c11507090048107120380400d00c01c04000810b000c040a4049a06542c1000d0b0010380f280004e5402c035513030750300c02110400807030070040d20034040031000d1420035600b12041d59504401105035005402582002c210304402d0340e018030a101ea80903000c48095071440c0d0940c0c8407900c81c4956601c070203034a6600c20710001850711405002d21a000d07200805c200d01c0c0d410300b905641e2074016000490000c3c0d1011140212102d0b1409800c039203540c054038124507a10b950000740c5294000c3c03070f0030108011541c840702c40418443e10122004101400d41d903e007211445000070b00d9070541c0ba94456040485091440c0014400203034190300070480550825005450700c4a00041e10032040001c48050401c0090424060038844005400d042603c0700c007843c00d490f008040c9030f5140c4900c8 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 587212859 1250 587211609 587211623
    0x901082410050f0c010501030c0501020706090314030c0d031e1811010311040603060f0f030506010b030405100905030d0f05070906030506031518071d072607050c0c0904 74
    0x340c546504000054140300006400c10074101042d114105031a600021404520b603034441c0010001d001c1d0001c061000342400307101800e1824140700b4058110a0b2901c00182040c801c0c0140f005031a00c248160340f5010629030503100c03000102100140582120000342600e00e15850482c0e00b59602da11031104c81d403071080040c001d00001d030f484404a0400f064842c6060503120001101c034002240000c001a19054400140346400d00142080001c06c0c1d800c042d802c0300002c90244045100000c2003811200301e0002c0507900e41d5030303141c00c5042400000742c070031050b0300307152080c1700304940800945012000c8285c10800b4055000030001a40c070207844420214100440034000ca500c250010b9a01100150407603000c202000703071403c00b809084030610400d640b5249046160003003030003200b0041484601c0e0940203054000740e4a00c8200c041d1900381800007400f00307103e4071001c40c41140040c0c0c91021032143d043c9800c03800540b007980140391900050080303441c071050610b0310b0401140540d400c146 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 587214109 1250 587212859 587212921
    0x3070c060206282a12050403022a0303030a0e060901060f091d0f060708070e09182a0a060503100909050703210e0f010c02060a0e15090108 61
    0x900385100c00b0244211402c640d00c600310359003030030840000801c0c52031300f2002c0741e000342407107210007070181740c9081c50000140e0401080c000400d6000400d46910303401040c00c2c00030142c1c00745101240703506001c1c00da0f4142c0008400c101d14040320340d10444901c103550b001e840f003036518014030a08807003203401121050030718500e0600c110100c03680042c40800c803100b442e052900c041d20402d4900750700800707850b0095005a04215416501c0511583c00810b142440a845440e003000070380d000340300038141c49403d824000c0b1122191020407012294403942c15a213441c136403074003011071030000c4c1c003002140c055a01448009010785c400ca085a01c00c1c1500b01c8240c904500f008d65400260034240001d990364401c108010006c03507038645003500c2a065642c800c4070361442d9000007400f1808580442c0344a000041d602203001d907040f882d1a03680690407118240d0310f40030441e050f00e1820346900843e40098403074001c400364881c194020440b2072826210780016944c0c00c400010701c49100c41d007008d02c1c480c060b5 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 587215359 1250 587214109 587214151
    0x1090c11070608070203040902072a08100c0e09040501091e210512010608010f1719150c020c04050c0906041809061103040c050103020c03090112140903070c060206 72
    0x20ba4032900309134288182c910386555440c04505907003041000b03550101440d051000360b04584405810001501d040c0068210300cae00206648801c503260282c260180c662019020307880c803800c00b2042c907590007008490355082500b0014020401d4a0003200d0070702502d0100802c132400c1c1c03600ca42d1896400711016905890701145c00700082c00701007a01d0b01380001800000954803052600340e003c2e1105603103c56196241ca000200c060090f0350243c8041700f460395402000700e0011885110040f00568051500c40703031441e2134aa45040b00c0308602d0205d1030070042c030780b20f640c1c042000c0da0166812038060005071980c498840706803003100055540f1040c1004100421030596484101d141c00301d0300001a1100315848040c01d85a0012215580907800001c00c410003262089a4001c1d144c01c0c0b03811424072550b40200c503600d02c100c0003d241404410410700c1201d101a070005065401c50b5000039800d0f04000d0640c0c2e5a0390441c0340b046404a001c160086291407002503030303521a03444215014600c400034 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 587216609 1250 587215359 587215367
    0x6091101111e0703020901060f0e1c0201031a0a060c0302060610211401090903180b040501180314060f0a0513080f0d050412020d0203130e100314010501090c110706 72
    0x41d42c20390b00c19010300705000016070744294100b8000c00042d2203408500d0f80c2c442e00209191020032160b4031503034200c0c1107424110f10032001001c10560a08001541006081c0511654801c601c601944800b0984d00410541c0d401059611264480d80881e01c26484413420020310403010f216400c001001b46030000410f80800c1c041d01d5a0101403400000d01103e50804c0240e400000d8015000072901c40b00c3c031804241d806909480ac8004800207808607500b04005000c4c0c0b44034a1103080e0400c60403948007004801c1144510005552042e5038041004520403850340b1114215200401850040000f0700c400718540103d40c030600008a03000c154a13100c1c0e0307507040181c1144840c0311800c2400d0090300c3c200ba0381c512449014900a003000310700001d44090092520680070a0441150820310440c10300d40003d6143d00241c1340c940040f401c00740c1d02c8804190341ca009562020b0070b03454001d18400c044000647c0a981a1781ca000c2d4140264089244140c03502224440414650392240c8030070400d01e841 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 587217859 1250 587216609 587216653
    0x50f0103091a040f0b010503010c0806280e06011701060c120e30010212130201050c060703060810050606030a0504020f060f0d060f060203070b0601050906070609110111 74
    0xc198141c0c1810207030303402c1c01d95010b002140d0868611a14810040610244031040e600404088000344044d1040d45002002000003801241c0030700c003032142107a42c4102c02d4650070286812480e01c0b2900603035a213003448500c40300303a6581c0e0204a080b510b2769100e07511380350070b203058034495141e6000c0d0411550b255410a00714100100400c654444030114541d220500740801c803220100d1501140541d501500402c001c6280c08100d580c410040150f56001100126038000030a4689203114003150005035007911a80300401094014401005034090f095031105060310005000c465546050840250864a082c0c40311540071b101807000426107d02ca400541c1d01a10103040da414004c0040c01003802500300083ca00c1d82040045250180480103110711b030010043d402405c46c92514000000c0d443c3d10034002e016104980d10740004d4405c5e40914112143d800380a0b101c2c95540c0114207003100204003c142c01c8400f403280d01c500d060107603c0b40b911034061501902c090041c42c050841c5001c0c00b610 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 587219109 1250 587217859 587217863
    0x150507030522050901080d11010b1e12010c08220b06040504020a03020604060201020c1b01141e040b0c0607090f14030f1b120d170a0902100e0a0f050f010309 69
    0x494000803d01d500c0320718881e402000c1c007000400141c03842c5000501400c0c107949040500e07a1416002180c103030b449803482c00c0d007880e119403200211401034002c5618200c0080e2039400035824842c50000c8250b0162145104620010890720003181038014017010122140000c0d00321111030000c1482443c26074016508584014220104590790385d0100710950410340c028000340c0d5010905444c10311701031000d8903c807240308201c43d483c040f0800000c0c106a6a0342c0e1071880d4080c0215600424440c1c00761038000020b024a2000e4560b0f0b40c0702c100b0452603000702c140c031205014000c08a088140141c0d020800d84405450407401d250420341011034061141c0d0f00543c4c54861a400e01003000d07001d0010b00390401c00d01c2405490256010144041240b0680590340e003544009000ca17001a031200b415010004001c805003081d44410440d400070301200e020107540001d82640c2a04025000860904101001d841c9c01c0ea84a60b94580040d441c4031501c240c0e07812a5424103c0142503110b07a203d100414 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 587220359 1250 587219109 587219167
    0xf0e010c0c3e0619020d110a0b040b0c07050604120f030c02371a010e090604030806041b09061b0206160302030f07060507080a0912201203011505070305 67
    0x7211458159034580884c02d0350350003581125404080c800c1c0d00ca201000380030311900040c050080c0c29554a011144024800f401c4800d1460104100d2943c0d07108480300140c101044070280c0c201410015450004203448102040081e004608441d00901076044103c8a13034018004034110000800030b1304a40b20442c3c00a1121903030b0907401d5a050348000c0c0140c078010746540915008845071041d00e48410781001c00000280010801c40713040001e5050761180d450b113426200e0741c84190205e40900f442c000801c0082000d056140170056014030340d5000c48401d076031703610785000b0514855107410300e00010180d00f20604114641c0417a01001c8040031031803203441104e00d03240c2e00132440c1d082500f140c1c90403101035898000340580c8551000e421030300403d48500c1049a030510390b507032598034400c540d01c0741d0612400609080780103110030035007902c114a038006d8a558140310540590654001d0045080200320a04000a2140324205948005615440300b519041903440700741000c04420b100c0d140d0030 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 587221609 1250 587220359 587220367
    0xd0e010c12051c0f240b0c070509090318040608030d020c0f0f0703140607051804200a03060e010305071a0f07080301090f0b030c01030f0e010c0c3e06 66
    0x3011a040c4202c03007075090310000400410300c0c00070409036101c1601009150b010109800403c0b4088102d503000c481500506d6650b0b007c0101c1c03c28204038660b4460780d8440e006030100b040078030020005080203009101d031030b1a070441203400c1104440c401c2c001d1100c50360060281d46081d070320b554010314840001600300c40c00c04610714542c3c0e280c041c503a02401496000200704104100340b840750400d01d0207820010340940d1500345001021070040601043c6460403c0d0160f5540d916107511529044565103500c01c3d10403201c409240e441da02c0311050344002440c0c414006510a150201c140c1a80d50140150244038079115000595804203c00e4003500c9804010b61201e05216100409180344692596034481d8540100c240803201c0200512590a003030441c40001c0744c1c0c0121341d001c000c140900b000504010b40013141c40080c039807000240f14961825501c0c015054001c0c0f0300c61015440b610038521044103100003094001500025041820203100716400361641d040316281c030074000900341c1070074 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 587222859 1250 587221609 587221627
    0x201051201080a034e0c09050a0914040204021b06041b061d0103110d0e0c04200a0c020609180f220b130203070303030c020d0e010c1205 60
    0x6030102a448a68141d001d61010020940c01107521003c560007002450548001c000441d00005030000d07420040000408400000212024494080b402c01361020000e804000401070080740d221301855206200880300001c0014140c003590404400c8100d1410b0b40381c80c1c0c0e600b0b00010350000c840d01c1d80b069680030442d1100341010062a841240540e038000241c0c071845810740c4104d4065002901007040650400d440620011604501a1400e00e00083c4042ccc410b8500e0545000f20314030311440030305080b00c01050b100002240744207208221810061100300038180c000f050f841d400180702c1c0c00c500b44000111240140118400c0700d001404c2580703400000340000307420002c80e4041120381320041081c001d450700d51b15503080d440254101e4005424400c00700039240304501c0d0400901040250001641160314a44660001340d030180c119590152a4038029000d04002029840180304e000c1c075184400d40700340560100703407d042e103507030201004589070408500e802410b80c00a0080410540b20 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 587224109 1250 587222859 587222887
    0x2060c061302010f09050d03110c060a0e130b0a031e06090b041a0108070e060a0f03030914060910030504022d0901081c050a0c08121806070206070c020105 68
    0x4401c2480c000c2240c210001e0344000b4100c0200032201504016152505004588480c1c240925031501820401080300c800d0680c5031405001e5030219411600201d000c45565401c0343c41c900c3d0003c0202d0b5404100c801040c111000c48044c1402103500030607041c0c1c200b005c41c59a000031016401c0982c0b120032240142e440d00000d5903031100040742c0c4900700c40104070038000d0003801c0d9494020350086039805945000c03003440c4d50701c100703000d0784011001001c082001e03980d9100030000188940c80300240b440da900e0902401e850301c0342c86110705404411849840d107103081001c4403a0704170020a00d002020180720120001c080080c000c036048881c4982803844080004052458076216506024100035500b0610010315010f91041020f07038056032059a01d4282d00707105541c1070959180c86519403c40e00421940c0030007008024002500000d03c440b04651007480b01c5100e48a00b00040c01e4540c141d201566403044100d9a4a00580262010403040f41c802e0304e1200395503005142440c14010700c0c4000345 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 587225359 1250 587224109 587224111
    0xc020306010608040b0709270e070e1f0303050d0f020904050c0a030c0c2105071b09111e0d14090106060318051c0306151d0a0803040b0702060c06 64
    0x20120f40f111040104028003444001d900906601e4589003051801d54104150068400d5a20540c0540501c145025610740c0c00301c800c03d85650100c03458155500d881c151025016601d091180c14103c3c00d85103415000c61074030048070b51540e1258035110a80200a0003444550110000d01d80c08000703140540d40d0780d018960141000c809013950300ca40c81c61713026044546509400c1c1c10701442110074400310301d601d03040c28401d081102c4e80803210007035070b001110039210380300d001060a56070004510404000c0c208150640713802002c20004011118018070140c056a03442c100c0c2d080840d50443c00302000507011340507945000c280800c400c480e84c40c00d4562103d0482e21800702da07540e044100001030307141c0140d28500c0f0745007100d11480100d83e12000e031905118640c005c010840342c001c9801682c07090380100c00178040024400b922210345034004081040c01d420113007544240303491120b2140760801c11501150740c0603006629085c40c00d26014482d400c12507090b0f80c451020703c01306440c864140011 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 587226609 1250 587225359 587225369
    0xa1a060a02010605040f18080705071806150c0b1506090d0812060d021e031608011d0601060f080a060503010e100501120f020d060b191a09090112030c02030601 70
    0x2040f0751342000140000c40e05881a0390f034529003480e51107041605c00764081d20304503070001101d070707520081d500b4030314901581036100c0f44c00306504030210080b4405179400307a030a841440b400e0b070032114a034040031103646000e0000908200d51010105840e0291144107100500d0058200c500b48106200000e0800011070020f58280700001040c00000280403040c030781c820f90444058401c1c00f81c0d6001300701000f181c03c0188503081a4921030b000b0aa40402c142140c50611014200c00e903a1200082c0307021300154a20413110885000c46404882c00c00b144c0079042e1341c4a95190f10036508020012030341d041c009000004e807039a64100120341d603102030151440300e03d40d1030000c021584d10f01c8489001c40b00141e00c003480d007400000f000400200d0b035100f20040a034044608001c0e420150a09600406049051940c041184401102d1001d004000b0008a07240c5109150a031401014495454070030304d0340d1907511014100040c070090f0140a040c140c42c6002e85407802c185031044c1d0209290100030380107 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 587227859 1250 587226609 587226611
    0xf0f0c02151902060123090703060b030c0705010b031513020105040f08060912210411040c0f030f050603070b0703053105030a02010903081c0f020a08090d080a1a060a0201 75
    0x1d885034450f010404c1500600791a454075110145840504180354055280d003031181d10120040b07040745210345c00c12000b618080286035500c4c10300c180000d459501170441140d8035428500d00208030700d80030800d8101403443e0060610740f5074032852800350b114000001203051141c107110211b02c00d00744000203c040c0c420003004046505003076031184d00e010241e50704070a58071000c0140c1e0803421140e003416030240c0c050908440f05622145040c42d68600096100c80c0c0051404441e4880950700202500c0b914015031002c003c1801c0803003091041c2d0750125540d64240c2c1c44258100720800c0808006e011080c007030314080d800d01e00d00c501401300c11824401ca0040f04808000b441ca2a5054550b0b07c2004150440c02000012216400a813091183d848040d01402000c2454501214540300c403101ca4011803e081115804184802c0000c0d000100c1040000385404001141501c00140b200e040d03141a440341c103002d66800072014007400f0380c2c0c20003115072900301000c0062512000083c003054189500 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 587229109 1250 587227859 587227897
    0x515030411062b060815072109020d06050a050a06031a06011403010e0103110409050c1509041e1401080312060613180e070b0a1103040b0406050705010c0f0f0c0215 72
    0x80e285081d81d40082601801b031031405101c0c3c0a60071001ca0308020034218061003450201100040080ca9015000ba4228502c50207002c10001da950145118208040e020000ea0300c0300c034600c00444080d400010100c1402c00c466440408401c040315030300040c1498858800310444504689580080e407204406113600801401080455864101e0202c020784d402c010a0440f0b0302c6580d590440800c86a00a1401d001c0d400281854001201e00748103010b48180704541894103131851041e40106032103159440c00d2800240400010320080c102c401401c0103605008000420718034000700903001c1da90102e010804000e260380d03891507840c000c0000105003824103266002075010b490b0f0003d244030260308250340c180300540307100042c0e4040400914188075045d41d0000329074514807643d00f009801820100d000512154010014003695103d40c000f031080ca00b4180d02501c20000640c20800400d040461203d1014840c0c6641c0b41210700042805520460b01c1c2e01075403196000800c440d0310401484 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 587230215 1106 587229109 587229119
    0x20a050106081605100f050a0507060507031d01090b1305030d05181b090402010305190c08060f090603060103060c090e010f0515030411062b06 63
    0x84000c00080b5111944595100c3c3c00340c0600c000007407420808940c1e803d0a000c03103c034078085501d0748040408030120a0b01c1a40103841072004000c000d000d840c0110b2414003a483c040c2c10942c90008207038040c0d4110440a20f0401c1c0e15900683c1809001c000190051840702d5102e0051075100f8940c01403850610700307504c03800f60a24581800d0105115001800408a4901004450848500d50070365904180900003e020b144c0d4043d40040014000d54040c1e0407107a4040c811035003802c425402c10074103004440c0c0541c01000040d2025040202d0380c10032074007034032400c0360854a81c04d90385040302c0001d030340f0f0905000080c5015101c8140400e0a4020320703085000d04984c121002c555a121048017003144510701c15107220f558004104191032034550100da00031900205010760710141d100501401c1c0c1d01c081ea0441500000c0005800d901401680684c80700c0c4680c0004240d01c0d24107 = true := by decide +kernel

theorem cover : BRFrame.Cov 587050359 587230215 := by
  have h0 := BRFrame.cov_init 587050359
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587050359 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587050359 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587050359 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587050359 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587050359 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587050359 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587050359 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587050359 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587050359 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587050359 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587050359 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587050359 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587050359 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587050359 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587050359 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587050359 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587050359 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587050359 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587050359 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587050359 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587050359 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587050359 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587050359 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587050359 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587050359 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587050359 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587050359 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587050359 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587050359 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587050359 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587050359 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587050359 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587050359 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587050359 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587050359 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587050359 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587050359 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587050359 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587050359 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587050359 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587050359 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587050359 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587050359 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587050359 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587050359 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587050359 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587050359 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587050359 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587050359 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587050359 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587050359 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587050359 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587050359 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587050359 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587050359 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587050359 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587050359 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587050359 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587050359 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587050359 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587050359 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587050359 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587050359 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587050359 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587050359 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587050359 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587050359 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587050359 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587050359 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587050359 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587050359 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587050359 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587050359 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587050359 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587050359 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587050359 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587050359 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587050359 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587050359 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587050359 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587050359 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587050359 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587050359 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587050359 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587050359 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587050359 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587050359 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587050359 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587050359 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587050359 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587050359 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587050359 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587050359 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587050359 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587050359 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587050359 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587050359 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587050359 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587050359 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587050359 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587050359 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587050359 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587050359 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587050359 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587050359 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587050359 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587050359 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587050359 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587050359 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587050359 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587050359 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587050359 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587050359 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587050359 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587050359 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587050359 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587050359 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587050359 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587050359 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587050359 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587050359 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587050359 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587050359 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587050359 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587050359 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587050359 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587050359 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587050359 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587050359 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587050359 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587050359 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587050359 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587050359 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587050359 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587050359 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587050359 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587050359 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587050359 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587050359 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587050359 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587050359 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587050359 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587050359 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 587050359 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 587050359 ≤ n) (h2 : n < 587230215) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
