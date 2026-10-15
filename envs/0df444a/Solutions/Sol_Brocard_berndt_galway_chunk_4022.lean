-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4022
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:21:19.745323+00:00
-- url     : https://prove2.me/submissions/7ff17ea8-5a8e-4b4e-b894-1ec1c49c9200

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 723201438 ≤ n < 723381294 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 723202688 1250 723201438 723201463
    0x4050301060e101d0a090804180618150b1602031f050c0306130c02101a10140406080705070618051509030d050a11030f1b07020a17 58
    0x1c0c45503580e202c5072403101c1d5a048503007020b1041c2400c4042602510068074403000c1c041084403115030345910b820680102403040048460080030080003032100291181003d0001c0303000742c0041c0803840c3c035884440024280c3c00e2040443e00e002000c1061000da41c0ca03a800b46ca488080080e29a4540030203001c010088800107903040c810f03030321074440c0881590b5a02c1402d0388401d40501040d2111120940300703020075927032a0780c0500909101d0b08840b0096000d400408103a2044035140d1040e48900003c907101d000030004581d0740c550340e05416007003595691402d01500d08e1701666007841c560b42d8400c5030280340031701400c02200c840894100c0744103100350345445030805000c0000b9210240400c0070982000021034803801a041d05941d8221403002c40352003001c0d6100590710f44080c820421004000003070480380066500d0307026118400f4810007442c82000705002100c2d5a0034180128140c5d06030850352515100303001c0109100503185c00000e00300700e440c4540b0204904400505907801c10941101c0c4 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 723203938 1250 723202688 723202691
    0x5130504060308070512091315030b100e0f01050a05010f090f0f0918030905040c0c060203040803180f0d0818060405010516030e06061504080d050a09050402070c0e0a0204050301 78
    0xc0b0522521100402e4900d108000301d55202400c40030903081c900503405404c0d4048090041d1401742d024a40140382d819490030841340291741c60f6503900303104003003d41300b0035100480102c0c20b00c0340c0c202c0c540040f034001c0d1042c09890200c6d80341c02c5c0011142c04003070017524100031070010f41c00c00c25400760101401401c00000f4010705182c03112001c040300349213481400030035400d00c120001209800711b074058605400d5030303406544030708200601015100d02c804940400440c000414041107080c405580142d224854250313507400d00001126201c00c8429440101d60091300c00c0619406002444080c6552181040d4420b44d071001d00040172031640e0f402d14a018010b8108110030403e040d4420791103081c500c803c070300d45100d40c83c17400c504454820302100d040740e2298010980c5840c01c0007500310b81d0524441554540798407454211309190413254002c001c60800716000002d00c1e00228158087c3c6015a130450528107251581c0c0300801e1130f0722030304015460520101c1c60721007c60b01202d01400c4082c00 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 723205188 1250 723203938 723203951
    0x170a03090218060a05040221130b0603070623090607050d092117090310060e1b09150910020a02040e01050103151107021f03050a05100605130504 64
    0x14000e040e808404a10903050b800035030200240306140b180c00b034000030303100312002420201408000d5201060742c812800800c1e41030071100501a00c140d20401c00c1c07425256004010b1314100020000103458584a908202818041c0c90751004000c0c162074503e4000b8600442c0603c0382114500c1200501500403c0010725041800b10009200c030f06c21416949800016030703150a01c403d40b0f8120040f0018000d07842000c40c001ca541e10903000d09440740c100485241510800000c0c5c90b1810b40410103c3c0340d6110354003000001400c80800d82d009000f040f14451450700e2480600341881090f4a9501c03850300102c079188410102010398080c04006400b0914201680300d01a60b0b0741035266089206a042c94a00b0101c0403041c0541412244d20800c08250100700581a44c0030f00300d002650022000300780107100c0075035180010051140507203042160424420300c070007019500000c2041175000e0404041c0558000f030340448404030346c2c06103040394a42100020001507aa0103600507035001d4280355 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 723206438 1250 723205188 723205207
    0x30315060f020f030307021504080909042d0f03111006090f050109020901080c0a03020706020f030405010c09050a060c021201022212050d0806180a0e0c151617 70
    0x101000c10702009902100d07a043c580e10000c076502d10045542400680006510b0200c80802204141d0814415040340381030030b88400106500c0c1800301d4083c2e840814006007492070244500101e040c5811031840b581c0340000c10748071600c11a440e60300040402441500c2141d14540601c00d5411400440c502800100e581d4400342d0301602c806103402000901d003000009a0185620848100800684030790545a40d989a1022180c12603128001455002c02070240012068802013000d10320f0700e00f82076201e0615080889c00c41d200040307008180440450f00388420707a601c280c0c1d80200c130f01c0e0b840e10030030b1409a440814007209480000118541c004034400c00562101075604403038481c107034074150301c1c242d440d280e428016481142c081c00b00e420010600c40703640d11402c901c5034001d038050440070140c1d0955203800310512040344d4880c60300703981d070355a08004a400d10190100004c100c691112607240301d0400003441c4110111485102e46109584d8100070340f075407511701107200c4440420b480b60341c4c80 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 723207688 1250 723206438 723206447
    0x10f03080f0a20010c030c050903060c0c0a1415070c0b0412030f060e01030201020d0f0806040b0d08070b01090f02040602030f070f0b01060203041503020f0304241d0c010504030f0f03031506 83
    0x1100f40300105e820041f02c034104512541c141c0788000c500030010811511384103103070440c1c0c0c2d01a400031003840c0541d07207030342002c1030b1065110300000c00c240c4000c0000ca001103420a144500c003034425400c06c20164403d001195007040c00700e4010b50030161490040398028001c1c3c000f4002011260100c42c1446400504440350162a80c1240e000780c00352030a0706d810440c200c80455800b024003003c03031104808a415400d0941c0803012950014040e0000c0c0e280940b284003803500301c40811070703450020100600c00c0320940d000340c89894007118820342c20241010304c060344a00802c2080345000d40c012030074000f17000000e00c2d65244150003005990f090b50312074000944a43c49401010400c801d00545104914070910031a8182c9050303040107800d50b21180d580e9200c1c3c4000c001c030303082c04c1c0711000135030f03040198140314108603481c0c0864803014070798140451b2810b02081c4a034650601006200401c0498803e19902e02e0507580618005003102192070250001e040d800d4400c00a4081e6000101300d19401 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 723208938 1250 723207688 723207701
    0x2011409310b01090e09120c0d031b0504030201081b030f090111090d032706020a0c0806150d06110a0309050f0703082d071109010f03080f0a2001 64
    0x1c04200007140218145074100791500340e9000380c005640b0030000c2004c0d4030350310740702c9800c03444110030303203803030038054506003070780d60800642c3c01e44941110700602031071070309132098004403d0340b0441c644d030904400c100944140290310000e814404041c00080f590480000301e2007a6020040e46180c40c1c1c2010f034503490a000d001c49403d0b10075841d0040e02988150450b0650340321315030040c06c070300740964142d03000c542440c00c5101004a412070001c2c03428200780c2012074803019040d1680101aa241ca60130020a140000d900130202070700600144241c0603460009502e4000083e1049107003005c140c6049401041024902c0030010b10208810102e03e074190080f48400d4042d03c22900c81c800c9120006446602622000f80340c4001004499641c040c016991000c0c81c0c040000045143d105481d5200140c6c480e00080328495052078180c2c905280808105015000c03010800e000641959100e410500c03541c4201c2c42d1013100030490085080c802c44409000c1c5011401c030026249a0300c0394540640300 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 723210188 1250 723208938 723208999
    0x3020102091c052e0c030c1b1106071e0c0521100c02010b0901031b0b0a080a18053a050304120306080d02030a0e01080402030a02011409 60
    0x7103488032070340322288820002030215000000b078900e2111041d40c4e1081c0039036941c0c12030040801c1008108810035240301d0443e4003181038074049030018070040014001ca012408002010110200d901d021600324215069400410745d01a0364480351820030760064013480312640003680044414908212446003504111002580c0551007002c010f020018990984040080141c9c1b01c0c2c100d02c2203c0303200303402801b0320380c1680c00001030311408040821103000d426003065482d03041048003440060420b1840710002c003140c5c09a0b40c02c0c207410150046c03c1c5e810281034103a5403504c3d6404048510b8241013041c01c110b5202c012034403401c45440080104003160040c0c000c5041403c02d6900907500410100c1646a00c2903689a207550380750303950442c45421100b21603007015650040407502040c208104e21480b042d540045803218006c00f0001e00c03504101c604a41000020814480103850000300304078201e5090800545074009000d0303002503405000c14080d44020840640e15581c810315200380c0407100d = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 723211438 1250 723210188 723210199
    0xa030c050a02061f2112080609010e1b0a0e03010c0e0a06030e010e010e06100504090b040b280204050f060901081311090a0605010201050907030237030302010209 71
    0x101501040d6014001d0000c107034003503004400000c000c030500c840729010f4910981c114840e400c1e00d450000e160120851039080c1100d0f04a101c51060244c0c0a0410742d059040e445d14403c5454480007181030b00d0810300c2030050482410300400c40100c0141041c072503800700d00740341c01d440700d001000080000c0350701300d8128081d528007c443c00529101c1c81d903a5140503400b0f01030b00c0540d4548170088000300120012066207541e00e5045403481c040038000e80c503c0c00070010042059042c41c1b680d00803401c10b1035000c80e100d540b5054144000035502d012039036203d508428110101d0380e5140307090aa401c0d8410580700e8003140003032000180021940a8030039103106486161481407001e041c0724076441a860640e0200b58a800000d1142c680000a100c102d4441c641c10000d0b0145400071541624060391a0081c0a07214078040c8101d5a09100f5142e018444200510b0600d01d950085079002c44001801130040340300110810355505031007a0002403001c291075030b003941680d03410028000d40100d640c142c401c0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 723212688 1250 723211438 723211451
    0x9060501210c0611010603021e1203040e011206140115030f0e0c04020705070f0f090b030a17030702010b0a091506050a17190e010e010e03070b180c150a03 68
    0x1480d00c21125807015a02c00508404281048401da0b901000c2410340e20b529925400c0110040c0c89140e00150f00703140d00d050812046031114100412080c00e55403000d03103a03205100801c640580c00c41075504460307100d40b0020240401c0c1c100b5001408050058543c1c000d041400010001d0410700076802c1405a07581c10040701581c40c01a40503180681d0306880c0329400030060118a280aa00401509201d0000c0b80d071031130307502c401044030368015070b11422000400d00010841c1070018000c00c0c0010344100c2c05096100c0f036070f655511001008a41d034100c1040040001489035000b5884040301c5400106401c2c0030307507039440c42140505050125a0f019503145400002d05c94040d03400da900d418040c0e122031300d00740101c2250718818000200342410007107000c040c0d005040301034401d004000c50b400e0000b103100b50251201ba800c0d2901d00c03040c2d1140780d0042140c2d0001c60215525039800c40020a40752082e0150040c0191070710852601099010031041c4050041c6100c1ca002004c905030305440510070b4 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 723213938 1250 723212688 723212729
    0x12050a0905060411180109091205030c0d0f150b0c0c0109080d050f161203050105010806060d050c0f030f01170304030b01030303200d0f061e0e040f0609060501 70
    0x5490180034000e016500450120780003030a0345031000d40e50355001d8502c40c018100600b1a000c101400c0e8001e8070074503510030424003404088486003085c6105400c00c1031860400413100d1000e4031500e000e81c486c080d514100103142c0c40c07d07900803105d03241e4001c424041090302c60214044030b074401248804580328012280c0d0756540904031690450b0358401c06803820302110802505c050b40142c2d201483e81c10108108135406505c00c130b003590b41c030b80200d4401c020b100d15040e000d42194410381220b810300165600700011a0343e407104a4007a000c1071741c40400c850700d6510b200e4106004201090501c03032400300c02c20241c20000030502d03040324000800240110820601203440e4440d07408088c151020460052001c20b0080d00301741c400c01108540004955000a0003820541015014081c403a850340040807005010b40905005440a0b038414030b080310101c40ea0200d03164941c8200600c80b05900c0c0040c00780071015002c0000c4542060301804544007e00d852001031000f4003848034201c200c40d061006 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 723215188 1250 723213938 723213941
    0x15040507051c1a101101090305030906340c051219030603030e120c0a0906090605030102040f030308280203040b070309020a031b0f0810061203020a0602090402040b0a12050a 76
    0x1004038280c1100300c0c0007500c11090204c2c0d025201e903980140002d02c841e045201d6070034800c8035442c0d4000d83e159603c9040c0340d4041c50600e44054100d0708074500b420b0048400c03c00030ac030040d020080c1820f000e1600581d40c0d070291107041060314081d040d409500040b003000c90104004000f0070004044500508240c503a042d800c130340c01ea00000d000a81e0707540442c880da082502c00c0c2c1c560b6888180448041c080010b0000e840d560854200a503004d49816080101080b20300410780030300002c40095081500b01700b64031145002d0381c8000740c03c1107488804103880c61a094200742c500303400101903800350300782d1109500203075100f642d003200d00f0040c90307000584251007803145200980d07004250311030462464580000e0318200100c0c1310201d01e05610300003480340b0455010740042950402a02d0300c1580c40c40e0b040100c0e0400c1d13002207548044411280c0000381e0110328170381150745c00600141ca0307409900129000780540d8000c61102c0d4800160048401c2d000154884244100202809a9501e8000820 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 723216438 1250 723215188 723215201
    0x10050106090f0e190f0509010b0306060f0d0615150c020a0e070c150b0607050a05190309030318050d0b0f0601111f020909011514031e15040507051c 65
    0x1140740e090f00d00411000801c02d088031001403101c181c0803c212601e028420202d88003940c040c100d5030340d60740701d43d03099007024008558030880460358402e4642e180004a0078100c4000c40040800795030307110101c81400740d0b00c1d00c1d4010b03050000c50101030031001c3d40040d01d5408114416031207101e041c140000c8144000184a00c41e910700d5441c00017240003661200d8154800540360443c054840301840810b440d01e40181030500e001e20020b00c80070307145040c1103060002008400610102c2c0042d0040480d4101f2012412240e05241180c1a04008414024107401e02d42025030b00490803003440f0f050043d944980c5000b44800340e18820780d920359100543e860864401c0300c2c14070741c00050494a40900710b046030b214080e0b00340380240c0781c40604000902c01800980089541010003480d003030300c2540c044a0022481e01074885a4074608005a01d0200030f00b91071a2801c2a0303000c07800050026584200105500c08007400a01c018100720300050310b0340d080700034130002e010f0307820b9a1842c02030032074010390 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 723217688 1250 723216438 723216449
    0x5070f05010e040c02070503030d0b330309011b1d0306061c0f330209060d050408070f0309051215060d020d08030a1406030a050d180810050106090f 65
    0xb45000488003042c0b0000d032104091002c25405100000909920184000c1100c0e04c4030031400615004510f0030003e808808425a502800e44054801010443c8010176490300b41410902a21f903903901c50350342d0243c4250311000143c0048600083c08203030301b042800156540c1c010b01e03540d0307040f0b00609140c1d03140807c581141d13111100700c0b880c1102290404c0b09550a601840042c2420152516034040e0350403030300c200661061821008012102d0310800054000c0130496040d40b4091a04000906600843c0c10100c043d55485000c02c00700070242d421260001d078030011281e5144898100988415031910030320b0b0246000c0c050500c1c042c100411403459450340c03081c2003040b035191041441459490513008070303000040305584a0100c0c00600c09184120000140810800c806186007849640080d16a034069800442000001500440c01c40440d0303400d0300e00f081510300f51180c0036030840655400781005019204440913420f807907410490503603034140c07100b00401c3d5072202134100380308041c07041 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 723218938 1250 723217688 723217697
    0x5011202180c0d0207050703060b06120c1c140f0112031403130c0f1503021c09050c130b0307080d050f0904060e090105060901080c060a0503040606120b0405070f0501 73
    0x300000340c1e4805074016040031844048a090442c620b01201c1280d004030411b4503175600c017100400c104040c50103101282d55080d1003e038104040e03204140b05828000c0d08151a8079800303d00141c80c42c0340f984108402490001061200c0240c40e12240300403602030b85c0849584111b00e00200700865070304180f42c0c0d280d605959050f00c0318400c000b9051240c002030022088000c02c00c60040106203561640c401500f48800c1e10288586021400d01c1009841003440f4249401800501041c412841c04041102c2000c50081040c04161a00358240048140b2040e801308820329103c6030103131350b0342c07040c00205419011500e1060700d82c803582d07564800d81c9002c030f070002d02c0411000000f1034401b0003034908401d01800208042e03403a062180c00741ca10450f050320480c5c1d59001000740d203103030500d0100e0041c48607201400d0800907200c0410954800c0c2c2040b0000d00c003000000c01c0820034039512500050201d40005400a1424a03003511150410340b0143c44c144a6100c0104d0445222024442210700c142c5030f = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 723220188 1250 723218938 723218959
    0xc090a05040b180a031101320a0c0903030e150309030d05011e05010f0c060204090c020c0f0307060e06040503070f061116051005311a04062d030f05011202 68
    0x170221a502c049110f00800e80d504e0700c010103030300844004240e40d003400550624075130104940e0305544e040e43c0200403440b000d0911180551490308011024203403034062800c201490000404100c40368030054095610440000c104040c1100100c042d148075249540b0600080c0d0382c4403000215091901316405c3c3c0c03240f05080412142d800740c00003280a174110309000390015445e895500803a0003030307808101015256014a18469414045c14074401c0341107802192441d80308000c02d0381d0303c10728004e203001e006881080d07103041d5655000341d4000300001412240000e4590240030040c060030303c00c140102d001030f04001450500807074407021641ca112480c0101c54544402c1004a00307405c4400400c0c04410050601729050f00d114103200c0314000d83c5404684500100030510150382644003c0083d06400a8000c8242c201c50445084910710324068151a2060b0001d030009520180240b42001c85000003108854040d0811440d0100106003080305a9a40c0c0f2841c0b4500d5142138020350000c08150b = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 723221438 1250 723220188 723220193
    0x2310021903061809030c060e030d0b060a271205010e37060b061809070311120601031b020c190602060612010b03070806040213061809050c090a05040b180a 68
    0x61000104c40d0280c500150003404544401080310741182020150350000076000c019154039000e01e011448058903018600300e03c242000740306081e0100710140951058410046409505810300080c202c03000040410601c3c030300d48580200b0f80d00801681030300440d00d0140500040d030150011101d18042038408003c1d841752980d1650f00000c4007191010f42d1a050b1380b106407100e41c040c1511904201d40381c050700381038404210030144002c001108150514040c2d500c010090720664400c100440e108040319222140107a018080303100384030444800d60390400c4111940001d58440b10141034402d04046040703070000d050b1031070180c001d02c0c001d640040c0210358a410844a509581c0314003800015584d48079000003801e00140350701054060b0b000e101070100f0761071b001180ea40038002c0e09004000790f074036016041c001c424801c01d000c0001940c07000c1150500506000d0a110f0300d4005128440900e08408008028001500e0a9540d0b01c801800503041020401e4400b9000080d0300c02442c0c0a58a503 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 723222688 1250 723221438 723221441
    0x30d0203061c060507080619050103090203030c030a18050612041212020c010603050c0603010f051504080d050414010f02120702060409020307030504030f090e010323100219030618 79
    0x14014641007544001c8441d50303900e0b1468030358000c61040402050380d0a111200416600c40542500e03c0365004282c14404010340c90443d0b421030340f080c2004070301c10025000181c210b0095822080c49400001034445005601000c8100311500080000162648075002e008040c007498440959202000c3c0c0032030302003144141e001f184003410b4900a0041c1c034429145005a80100141940e9691524014020460244001e090082050784c0143c21036141414a2030140e46611803240241c1b040c8007010444081c1c50125009810300400700c41010705582c8008005900503c46c030100c101110740105610f6101d052903143c040c03400d0303009041045480302d0200c007603440400c2c12640400304110014000c1d08500103188503614545000031103180c9402c0103820f05000301c0030030080240001e4103005400b68040c00c2415650080b1050141c00d5440003001d1443c0700c0810020000d00c52102c042070b6408840e0018005541c000301c0138500c401a005058040d51031902580200c001d4440b070b22002d14209 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 723223938 1250 723222688 723222691
    0x60610020d08070e06210a0c0809030a0e0d1a1b0a120b01050d090b01060e0616120302040302040e0726031605070b0d060518070203090f030f24010f0305030d0203 71
    0x7403980d880d0031140c2d5514514074504d84551410031506104111b649a402c5c4502311020300641000c100d9482c001788041e45a01c074440d43e00042c001813003d6078045898103620602e01d00e50040706400c403814070900700100120121291101c00500038003201007a50741c4015201840b00c183c40d070f0718014030a1282c2d00e02500c0040e00071810024180400700c802c400c4d46c0600091030b401540c51031820b505081c030003031828001c1000c850103514104406013010440801211030581c001d5039440c1c42000000049001e4429580060340c001e00307140300d80f41c0c02440401c503101222001034480070342610089040c5106040b1141c95138440e00f003230090300d80c20741e8410080e41c2c2240c45034003901c15298841101d1100d6800105600c40c00d140c3d914001d010304c2c1007006600310083c0050560192500d41800c0c001c0d0f69109140a0b98001c1075400c00d135131629101013140020044c0440281c82100342648d1084444982074024459541108400040d0754140c2c02c00d400250307170700310000c4d51034030b40e403c03002a02a500 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 723225188 1250 723223938 723223967
    0xc0721050d0f1a0a0b0304110f090403030221070905090a0e030a021c0207050a120c0f090e15040f1704091104050f04050114040c0c02060705060610020d0807 69
    0x40411901000207154880c0701d41584041800181441583d50389254081c0250902c9018401071030040c0b01c0b59001c0000d5aa0059018510100301c409050120341a40720200b61682c120000390140001c164254002c0c1c00320404a0001e00302c4500d400c1114406203200303444600c0071a1501d0024466410103401e096800301c000d20000c1281018654820b01d90343c88841c40c580140c0010310b100c0c080c0410761480e10a0012a807000303006032802c200000d80350003464440c051103007016100c0c01c001c0203594031035031000300b0304aa190802c640d680e00241001d0400a40103100900805c43e00340381d107a9440c0942030150750800c1003024566104da0344c031000c40f1001c40c02d0b0b454400003840300042c101150702802c1c07010822540c0264589184c242441640c910b0007520521640c01c2ca0010312082002c400440000f0104860100e010311000d41c0075200c00ca03039400d0203508000d00042c0f41c0140704c00010583cbc040c85054070040100040c40200300d1f29201c03144e54400016064002042425100c3e0209419040 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 723226438 1250 723225188 723225197
    0x18120c0515070f020d0206010819030e03060f0117030423011106070203130801020a0f030209010e060d060f0f030b070503181914010902010210150e0108030705060c0721 74
    0x11501c510450708840116450800907150494010075142c1c1803210300c0c00311515000500342541004412358503403003034901703c0c0003502c64480041709245c03003410180d1000002900340c0b81542040001180681d80034001c0071b100741c0e1401c40c0074040040c000b00300c40450b04c8491880c40c44a080078481c51035a41142003a034104154034148508060742030040e5030040495400555485079400c40200c207100c3d80f5480880103034418015402080d410186400181c0202e107001652162400300580b44600030852503500100045504010349084d076018500750b4100b11031481c403140c0c1c4c68000c17288a41c01c1d40402070010848402158200e8041c0c000345400c17003640b001e51320005260091a9191250200c80c0c404c0300544000b001051200401c00000c1007c002c80003032040c13000540020350381b14424100602510364500811011407040d0121401030501c00800080342e581d100d0a0b01d0f075903044280c0985230f40c05071f1000f10b010078a141e003c4402c030300d038086100d41502080340d80055031007030082c1c115030510 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 723227688 1250 723226438 723226453
    0x5100e1c2108180a020f011214042102074b090b061c241802090d152a0206060609030304032006040312020118120c05 52
    0x40c646400c41d4035860301241d00104007030386408008042c02d6010b0601801c0d4800c000716031401100102c1c00801454040e6078008000ea56074004990200c441e000f50008140703801d5003006842c203110341d014003075405039000c01380d1030080c10f070a0342100c7e0705082070360b01691107503c04003c0c1c9454918802e44480c2d411192940719091182c0959460440403610b801c43c100d100703042c0070030b8501c180f8018090001c2130400c112007000340004c50703e548940d14000744034003409404c2a1380c010b80307908003118241011042495070406040181550300c464058100e085001d21010010080c1e14829141c0e04a0000d140500c01400781d212402407009901150050307a8544090101d5846211503001c011004800044e035160001c050003418100060041e40c0720742c0041180382c6a130350380081614181c0e40c0000d82e43c1c0700091052001110691180d15894114101040010500000d904410008a4590000c0c0510821048801c3e00840c0c000300042c281071841c2c20908006100f22802d0181611900c02c507100c2 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 723228938 1250 723227688 723227693
    0x302210304052b2a0302030d0e13090b0105131b0c050312011403121206040209220203072d110a0b19112502060d14090705100e1c 57
    0x144800f000301a80c0c190f104406070040010207803a0b202c0b8420001201c0c2c020710f811540066141e4401104500820124101d840556a1204659451090341c220100b0018000f440c02600e1801e0074407407a44200e501e40c840d81c541c800d55009500641c0040740c00341c081c04140b28400e680700010b0b0032059844d44424404c1c1c0c0a41103809440c68041d061109001c2c030703e000d480c070415150103d40d0400704c02000781070024014480e01c500085801c01c1d411600540c40303a80e910b0100b1036074030720360405040c03800082081d4500c81000d40e000f54090300d4655a40020350320201c0084110185000d14447d4505010010000300d5103d0240c0b0407903a040a01500d04085003a00d421528242c20b80c1c07181d0f652000500380300300880062165801c200c528502e0141008442e20304041c054689420601007408a1521401190343e10022945888200b80041047e400b462b04401c01502c01141c589105208032900850203107003600e013208140309581c1c1e507224841c07030120030302c0344184000500c15128201c80441e60f00 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 723230188 1250 723228938 723229009
    0x60f072003160c08030901080c07061401030602131208070609171b0d0206071d010309060e0c010306050f130b031c02030307020d0306031a04050f010c09030221030405 73
    0x40d03009002000507051122400d000b200301407254800c01c034545c002c014008850b44c00c41403481d481201da103000c5031142e00c00d080010140c907942e518103840101d420008420018160301408199144400d9299903540720200d000454401c481c0190051505000032800552140c0203000c9103882030040d244800c0c0000c05e1010141c103c10021040c049080d0300d14411701a042043c4d285206551008061500300214050001c1445c3d4580301d24140700d590303030407049900030b412070b958441d400742c0d0070000d080c4240c03000c0d5218200901e52900180c24080e00140c02c3c540380d01034a0800100a018008108024050800610a040641d50103001e54000000c04080c4100d0403440078109070045c507a45e150088000f800c0c21011170050741403500d058024400b141c04070700d684217a03506082e520743d060f44a80c1055880d05c440840702d02d010303600349281903495030b50001540c1c0440b4820b40d00101d83c0d00b80d550069400f166841010540e9900c11b20080010b8900f07803140380c0b500310201007001010404c843d541039 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 723231438 1250 723230188 723230197
    0x91609030501060f030524160201021306050918070210020904090203030d02071a0c070807062409060803030c16170a020607090915090203100503010504061d060f072003 74
    0xd110410101c410002d008050102031410b03034403038103402c1e011405c0047c1c0c15051003014159201d01c0644465401d1707454000d5040300c0c4c08104d8169408180c40c1d490000514030741c41034003101e003d21000d02c10081c190300b90300d07091401510560040d100c100b8112016400035005a20007a5203c1c0d1900c0d9541d015071802d00c002c0044102c0ca0002590340c000a042450080d600741c00c070642c42d5000101001107020f0b03c802618107084c0d02100b12541c900660400f80c000c0c040680b00d4110500400e40680090406c00071003d04440038070406002d40c0f41c0d1540034649070301003101c0d044110ba01c10440d08604440c0c21425840a52080341c814075040d40c010114400f940003002d074200564405402c1c0203026070021600700060409100601c544104030215100d140103510941458517004804101d10450540b011806043d002c0e000f00301c1c902c0c06043c4240940748007501040c0000107820520350041c80402d03002e1060440b02c0c1240a5521441c201f140c0c201d01003a841c4987c0706441c2c3c0394148002d000d10081 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 723232688 1250 723231438 723231449
    0x5011b020a0914071106042010030902010f0e150906190201050105091605191214150901081209010c12032c0c01110a02042c06010509160903050106 65
    0x181c015000300081111080242000c070902c0001a00c2002110000880da81d100350b110000c040b2823088040a8907409103441d4003075901c44001d0445c0811154950302c0366110324000d03a036213030442048510548000f52100d100d10341014440801c0c2401686000c010442800c024103e9072500e5581c29904031080540802c1c240142d4554004010500c1c14a1380316070071050728012540a041210030140051186410003500203010b25200030840f07001d00385a2041ca800c15005201c88074244204140c289012174201241c101c00500c0303d20702e42000b00070903058588100081c21034101d400050459a000424850b0420003010411000100c1441c2d155221681c5c0b07460129505001d00760800040589202c01a11051020380c0501d0030140050141d0088800b820101071000344d90f00500e0030100001d4020b5002428a994440c8000348000c51580400710b04400340700e1a40007002c100e0b00c5410078410b1960001c484c2000c030b0100c400202d02c1182d624100c5c10581606a03683e55440e080d11042e038002e = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 723233938 1250 723232688 723232691
    0x2041a0a17060108030901080f07030b0604080f07090c172a03041e03091e080d020f1b01080703020d150e0601021b0907050c070b040f090b0103050405060105011b020a09 74
    0x70010409081116a001d0f014000140d4180558040004c003132030b00042085028060034004180c1e414000c1d802058811400342c512642e0720b4560441075910f070b1142d240f071001d520916000084a102ea880340d0707017000751981c0d1000c100c40c18000010405950150210b941d101030340c070191484800a440c0c1e41c2c50048900e009a07203e1905051000700221080303121007003c420702031a180002c1c1d0190520b07007a03610040c0d8604205245c000d0500040b10315800400481c4101c203801003050f038000803450303031040d60901102c0149540d80244c840d10701c61481140c1c0414050404504014060740140003403415000e400240584e000000c1160804241d01070660500340c903040c4907055a05014041c42044065113034405401e144000c00e42e9220000d10110400070701254540c00740c1c4061041ca4004d1400b500d5450302d4a80b10b501c80c41c1104580c0c421070b949645040703502105540280115031040d030304600074011903880e110041d28841001e02542d01e211461550520040e500d106001d400781c81102c50 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 723235188 1250 723233938 723233969
    0x3050d0809150405012306010806190b3408250812061908032d040f0e06041406010e04021e0414030106080a060e0c18040b010e1302041a0a 61
    0xd001404206032409100700c00b41c2000300111f50b6040b42009400c0082515182801110b05a2009540c082c5400804ca02e95001528401000800641e007142580c41601c10500d240c55403280c0c50b010440c40c00042c059441805501e500c0c01c000e484044a01c41d201221286203562692641540c1c0e1100c440242d4031a1604244802400e1401198901840004560281c0c609102c241ca540c1d004610b00300c2c4800074002c108840b030800004886c80000c0646003070540f80c54503460220386200183c0604c0381c00c81e03184c5001640b45e1501d8020403688410610091685403504001121300a960302821a0000e400f04100c00c411000d8030046861481e14031112a21242003082c8040c0e000100070b00c141c400d82c10103105024042e00400c03040100d036440280000e02c0c00b1605040e600303180c6010003a660007014092100010203002d401c4901c82d600c1206d841b612603072a5000b850f80110180d843c000740f684820302d840700501341507010001052620307a0180d03d0101500015a11100c240c00540740e81100d181c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 723236438 1250 723235188 723235211
    0xb061204060509010203090304030b040c0f082b050702090907051e0a090606050301060f1407080301140901081c0504090218031002030915040f0c03030f1803050d080915040501 77
    0x8500e54019043e84000d5240d41006c5400c2a030368000d502015007682074102c04102041000c014040003003c0da45a140304166461842c141c0f902403048006104c43c4c3c40c04400045807014104040500030203444250800b046d0341c0034844001401844140c1500c01da100119440e40c420410031015443c055018034962280d500b88148102d4680c044071410327041400070f00005800c5000d030b81c196040780c030344800408101101201c04107202000c5c84014400000d805003405048001103040e0f60843c06103505d03225489080c400c0c1c0d10000d03c92102076400000041c08844020080070480d04907500e07206050544404048080380c1c0058100e210046000c2d00e15011801c041c0103100c0d00382c0f940c50003103003180f500c0c800d01030700d400c04803c00c000d030030010900040c2008070500030f1040d141e40080207503115540300c0c580a4040c3c0c03070501800c40891007022884400250fa40003402c2a02c1c2d121b0068100c0361840c00041d034280c080a0310301507482c020303044a0b901800240b0080c9200390b000340000301e0702c0003001 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 723237688 1250 723236438 723236441
    0xd060509030c011d030a0302030705040b04090c0801140a090b03031b0d020c06070305030a1805010c0e0f0a0302030c12072d0b0c0c010e0103150902070b060a1d04060b06120406 77
    0x1d51456101001c2d444200c3d81c40b0044203a030450700181c180036a9034ad450300000c40d440d101d25002000c00000111b000300340510030354401c078070f0468181c544070900d98807800d07910070303184000c0070740c1e90b000402200a02c10601300c1d41000850800140460303050000c00f88400300301110240d103000d1250311110718a08480c2d41044a0840d085040c1c40c128980b07101ca0701c009241d40b0000b0400303880740d80c44205c0f1104074018003010807a40f54004008000184a46c0001480050303805101c62042340fa200300c1605a2825120304800c80e940240186000081c1070140070b108129203890304260300a0f6800041c80800c1d9008032030002010001360894400c1062a44407a1143c0f0b400c045080704c024043d4081c8140005100130f0b041800f4240720104c01440001200500004802c001c550200c84100041900c0e054015150f0b40c1d11614681f65260b0f03651061164130038862140c1c1611003420f80e034110a0b441c10070403064000380500c42c0401d0060100010441c40d03405080005c01d05240741041000b401880d = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 723238938 1250 723237688 723237701
    0xc070f0c17011e09020d0b06150403150606020304301b06030c020303042d05010c120f1b1d150306040b0a05010e10051b0a0b090a03120b0d060509030c01 67
    0x502c3d00411407030906401060100711142d00090908a050000c1100384c1d4440588d101c7d9404642416681c0c1c5480345004500310040c0c003005040241071040100720a4004010b0341d003500e13110489900301c2c0031141c0c56041c2003206190380020482e190f200710310104014034003050807520301e00d03107807543c0300d1403c00014120b4030358501d10001c540040c428000081c10a0705507601c1580030800f40380c0e0184107480b180f4002c0b10105c0d001410b541c031304038550000da608100043c000c400c40e400100711512103091040241d0790302800140081c00d4040200102a005d006d003100703c6101183d0070307407008002c0c0c404929075069610040690701404800c00000c0e15050040e02441001503030030503610361400e00080e11240050206620074028440710520041c4250103450507100c1200300101100031210708241c4440d4500070580c3c049003c0301c00101d0340c18000600140c441d0b81659081000001d06001300c005109851500703a0100d0f09507090710200d0318500480740603c3c014005140e0b1200142c80950842d920f = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 723240188 1250 723238938 723238991
    0xd050301030507140609040b030309100815030f03040b0a05070606030303090209240405220c06030507050c0a02100306120b090c01021f0504030e0d05010e0106060302030c070f0c1701 80
    0x241689071025840d00d4090320040e86c002d80f070126036408910b00203815406a03c4142e03810003d0b010118034459442a115405800040c0c4031504102d00c1800307064603600e6500e4444010b074020401082000e003641c005010a181918045041800c2641e030031090351034640c419000252a081030302c0a625102c41e09a4012520b030500e02540300510800e0562148a9110b580c480d0382d0340c03070000302c00c000c4490123a40c01c03500080031031405a0311450710754120b0050340140c1000030f03d02000141006e010b001202c000c00071100c010042d901282c0d003000218088044200704042e00c3c4c01c0000ba00c072440c0c0881c40d1117544100c20849503803625400b014500441d5850560466112012108040402040c81c0300c000c41201d40100d01991982015290827503090700705a00801d80d0342c3c0103400d00a065110006150402000f404510f0380d40c00200c0c180d000c140c0d402691b03010300300a10b0b00010440200002c00300e2245030740c002d0312a03070f911881186c0340a5061040d91742c2d4407003000c4a055a0301500403440e000 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 723241438 1250 723240188 723240209
    0x50d030e03032b1a012a05061602060121020406030b070c020f030102090a031704030c080a061404021f020c0a06031a09040c03080c0f0a0c060f02060609070e010509030d050301030507 80
    0x355841d0000c4c41146030741c115050281a942d07210040c090031600c011940502030b0000b020241d41d2030030070354541c2d0469050b00400d141c0c0d11194072703403480465214125007404d41602c00e2100100700140360783c460000c04aa1103507072102c00100294042c02d140b0312480064440b50000c00ca1070041c000300488400400e442079204000c01180d9984140e411070580350842e0103240540034680e041480340c492a00090310700d1a20220000e2031510004040c1c0c0700910824050003080f2500886115014007520001d5000520100e42040d20b400c2070300e0070340301a1040c81150560b012140108140b03554a412441c0000d844950170030305e0724080e0f0841d07402c000003910030043d90f207020b44803180e4150090000070321119001446141640c0201300000d1408801000d59400011602c0d200040e080349220f03030000300d1400316040c907120340082262032017680045c0c140840c1d03030759201d000c03220b0911000b19541808000e01c80f403000e83e2010058980d494070240c56140c0d480d4110f0410b1071030700d01a5400b80e04880e = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 723242688 1250 723241438 723241451
    0x1150e1f080709020714030c0717070321170408031f0b0d0b06040b0a080a0b10020d030e070f030f050712050a11060f122e050d030e03032b 61
    0x30380000d451400c843c0c100c0401030700c1d5190341c0b622082c80f10706551088001d05c4041903e413010000800c0c408112072a00c01403002040c020000b00d501d0705c00781d11014004000c03038041850f80046080f81000c074010f00d4a0030922602404404110b03418041d6000c7d542d0010100403c1140b0b2000b411184503070701104882e056240c0350428410851240d0054016440d031500d05051b2281c483c8420740e8060824400010748462503d0002080e1002c2101d0910f0000d0500213840c80c9828003104009180f440303580074019000e00440154003500a00040c11014442ca001c0041c0a0100154482c06188924100c20204905082c214548012034014160901603041802d00003a00000c4005529030701002c039201c0110b60100003540c03400b40240010f0084030020798005450460316605200d0f0705c0641400110459199010503494010348540244200040080c4601e10300380702402050fa1080c50400b030303003200c00d0011034155000030150b0180c8902134122180b080c0032544154005000210040118 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 723243938 1250 723242688 723242699
    0x1d01090b100f0b0a11060c07050c06030103020d0b06190305010e060906090304061d0901290f070f020310021308011a0a090f0f0c090e011d010308030901150e1f 70
    0x41c0c00c0702e1141c5004040c1c0000c0c1c00d0700241c000c40c2c4085c01690600c050b1940ca281003112041584d014141c00c8a1038043c1400600c003624050065030f06981d000360024852401c155240b03503144c8405481140d1041d0380ca00f036410001c2001600c080030790f10a0307001203501c21485414030300d4410003510821071600940c0822580300000000e9404842940c90030003270641d0203c0710030a00d042400d0199070081e41800010445105501030700c107095046a0003001e18030341e2000c00c100d0a0080b415882c9040c00c1c10131003100469640c81150b0301c0325000a0546264038084409031080f40d21440030400b50b070091030410090500e003031042c02086200346400c000381d480c4800000e40720391130500ad0712045a030740300040d013616801c0d948440c04125050800300000d10b4200c0000e445481640301d080b4030242824008103403e040e2041c4d07c8440c07442404c42c0d482c81e07421a0340301c44e810b41000f041c0514a42d6200d091403a45003461219000800c205000c0340800d0410410800c03400c1d80b00c0d0003800030b125006800304503 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 723245188 1250 723243938 723243959
    0x607020f0310090c090b060f0a030204050319050d020c06091e03030d060f0603050f060409030215041b080f07090924051509090c01110c03010f020309010b0a06020c060901031d01090b10 81
    0x2300032110030407035940c0003c0d9400b50024040e6800098162048440048032207201c20301080d20207018501310740100000101c1241e4550703152800c9908240140002400b03070404215050340454007a0b4482c510540e6240417030315680100d00000402515564104103205000e41c120024000030710b0180010301d0120085c07882200050551800b40d07903500305240a00d4420b0290b40c1003070720b845011a0403801c040c2081c3c00030416032800c400c1503401c9030b4070008464400003040004003c1200203400d00a1400040e00700401c074003031098521414402a03a10119500c5003015807032402076034000360504003603003425007000410020343c3c0030740d040c5400d2100f20040000c02c0750300345109203008413005039a40c2c5414100180e880d502505582009245125045543c02540c40f407200c140080003104520001c2125824041c031510000d0f07041260f06501c1030030218018491440c040c14007140c151204c419509506440b40e41d4004241d6607100c200c5c0401c100080a02d400052060140c60341a0034401c0415 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 723246438 1250 723245188 723245197
    0xc0109080a03080f0a0603050109030c02210601090905030f0a0f031803050304110f0303070b06030d050f0d0213120b0405070902040f06030e0109050715111b0607020f0310090c090b06 80
    0x1000b640e6050f00156200001746c000c48082c41d4002e000740042013080c039001e0700c5440d46920491042c0007882c440c82c441c0e072886003508a10503404000b0180380e40791100100040c20360440a4607140004c0001e110b240006100a0850014590380e00b501ca00005038020304135400c141583c01d2039400c4241000c0860340c000c095a400980150303d90354198028800901416544170540d905030101285070002d10040c011024410a800ea0603a10840e41c0400101c55910428040c00420300c3e00f80402d080c002d201340c0c00351941c8801144114080c40c0c440c1c030050310080260004540c1d0401e10400c11041020a00991004140b000c1d019400c050a0610290800315103001d20020595a03046580102c0b178250031420100e6085030503560f0207900c070036020000d05050b400307480c0414440c0107000c1c9203000000303c44e541042d6640c5042800c484d0901080180d03404082d042c1d0340b2807800704a850740e0f65028010064902034082c00028440309500d41070740c0305581c81c2d100740c8485181c501400629101ca400f2913 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 723247688 1250 723246438 723246451
    0x4120203090105181914040b0307050d0b0a140c0c010e060c04090e010207021f0f05130e13051605030d0504030203280b1017190809030109140c0109080a0308 69
    0x5640c20200400070645d042c00414400385d00103178405e400140030b250035840c442800010b5405225122040c014941d40317540c1d81c410907810030102007514010031094024150049411200032172030410388142c070700316801e0594001401c0080000c3c420000c3c0e10034401d880001013850046c244c18a080d40e05c11403180580e00c90480304940340c07500506d0f41c0000b035044806850740245030440140052022030310852482049501007000300c159428014000d206a600e03d444d0707141140b00341424100032000f80040034240348000052114801d0014200b40070f4400200c00d0110b000c0ca4080c941010549810341c030301c0c801c0043c84010041440981c402080400180554003c080c030780c2e50702c0261000000040e0b0704040c1c03682c0f4800c000d100c540416040c4603021203005103240020070300b0302c2d009551922803e0701ca031018500038110800002d000341c0082c2c206000300600001c3d041c8459150004092034203140485175400c174200618a5607080b03042000504400303c01400e40000c0e07030b034002d0098403028001c3c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 723248938 1250 723247688 723247717
    0x10311012c12010609050c0901090b03040b13060221070807090303051215030307030c02030c040b18180318090109140a090c0308041d010506130b07210804120203090105 74
    0xb0000e0780780c09400ca03800500d840d400c1000a40740c40c0c401001039420042c180b500184a040000a0303106107001500d01036078000c0d030a9801502c074070388800c04032144d00b6411240389c1d80038001c03489100307a1210030b030019a04994042146180c480d500900c07452000702040240204502d0900100b5400300942c5c00d203600780656042140c0f124001484100141100c3d140d061100040ca90105580012a400c042d41709804450210880307200f00020340c1c01c00705405030002c04440100054030130300703240c203a04440e143c412030605c03041c600d46950039170b07000d22030410201c800c000d02e44c1100d0420b104480d004112026042100007412015a111842c0c05029141c225071100c907000107000c2480301010080d64803034001d66a6554440d8002400003207010074400818000d0000900c5041c401c1c02c880d03a14060000542206084c800006101d8000340701c260f0300b0303101d1015110294071004c42200303045125510348006070304c0d162034084e8044e0a500000b4045400500401038075903004000c4c2c0e02c4503110541c0 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 723250188 1250 723248938 723248959
    0x10c03020a2a0f0c030b0109060b16230106180c081308040f06081f08061f05131e0b03060f04080d0c030b01020c0105071505100e010311012c 62
    0x2e440e010000d5800050080b4002c005880100131285080b0005c0ba8400c0701c4520060380e84811800803075800d880f030010702d08010031202c5821080c1504003030b242442119440d428040c2510080880c604081e02010541c1d035400f818001401d500d0440d4004c00c400003000c7c00004580d150040208401420300d41c48080344020b4502080110001c1c2c0c3c010302288000d131000c25950750002020711200b41c4401e02400380e40d0141d0450400404100426034000d45c0003004551640748141030041145100c0120100410801041580d10711034040401d0341c500310701141c00c1da1181c08010007611641000954145841300d211341d1510003280141e4811050044108250780324104030400384030750760001c0043c1c3e14151500c0035403030701a40502140c1d0004e0707013240c40c103075110f07001520a803055610242120080e11182c19000d06103420503540541c1410ba5010701c2517407940145d054141c00c0e08119805000d256051500356401800070450030000a40d4174844070050054941006c3e03170703901e414086d180110 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 723251438 1250 723250188 723250247
    0x63002030c0f0319050c03060a030305030a0b1503010503010605011701030602030a0b19080c06040b1902160b031b0301030812041b0f0515041503091505070c05010c03020a 75
    0x40a40d4269000180039907030f245840c1007520f910f8444803c00410346407502011444030004a0141d074821030015000e40141d40c150745040c0c50980006041841c4162a012110344581307039200105010503a9001c007a40700d50600003010f0070341c1e100303810540c10004e4280d5070205108070030f149581103c0c3c02020050342ca0700c410341488058802c07004c03d41e41001d408614100c0c030440c0c10101100701c503112010783e400c0079040703020400c0b284101d1007018603946090008080100324503035041d0030099940101d031500302d022180088508441c0d03000c1c0d40c03c0c03803000c01048550302082c68110000e41d1122035403407940d0f0550361130000900070315000f0f00d02044240002020018a4640c8003c440324990103085420740e645545030340c00c199030189602400e490f0000e0162800000d085d10107032140c2c0000700e005076a07400c1d000c5000b0b2040480c251401d45064003034030200c200502c103a5003d80c9480d55505190212070600d00d00b03440c0f8050400d02050702c10058004c890307a000b41e42410701c00d52012126a01c2c20442c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 723252688 1250 723251438 723251461
    0x51b09060a090f1d1b0603090a0308130f050714010e132004080d11010b01020a03080901020403080f0408150f0601050c010f0627110d0c110d020706300203 68
    0x107003030003543d024500d10040c81403000084000310403a007030070171007045103011050210900040d101c0440c5540b001201d540002d01440d0580c1e41b0000100d800c000010b49a2a0081d00031070000c2c0959040d080640140140fa01e1280e1840d4006001c3c01c001c0d4000d0544808515031a12150300f511180e07544002501400c103101072240d40e04c41c08602e0481d203941c0c99882154803809428140d0300815044042252418010f0003510003000c0b05801401880c0d05940b025103103424020b14000c1e003950b0030403021002454940c007070501d441b01000004d407a18180130285141102060204600c1101c0c00200800b94041014542c0c1c020401e107002c50b2203006106019001d0240c00c10703421291800c00d071020402c0001240c1701152901c1501807a0035000741225803030100d402c002c0b0f850902200c03c1105140212154111240c12a460718102080c0400e200ac100c0c10020030104400050f04a28001c1060942c8802182d4810841298014030900800070700030002902440c2c00e06d00e150041b001640303031001c4 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 723253938 1250 723252688 723252701
    0x209060d0e07060306140f0405071701080105040b13050c0f0f03060406052d0105010f0509030f150106050a1b020a0b030f100f030506130c050a03051b09060a090f 71
    0x21104148555418952182e40702e100300d000b20000241340c850000b0700d07180d0b114204d007000e080145c203500752681c142c001d200143c100102a1030038403c000c2640030910021182e03c500078041d110000405003000c0c0b60020a0f40d0000e4142024851403416602c082900401c03461080241141e040c910303940508040348003c6100420315606019000c200024401d558114a1090b41014100c2d0204c6084810f9201110322040c01e60940c6038140c1d00600c081d5014051b8001c0d2070b9410300b012400c0480140000303240c4140c0340d821405c1c0f80c02c0a9824082070341c546070070074090080b50070100d080500d420b800a10380c40d030b9003030306607142201c0030705c564155203503107903540090b10304450035036520700e40384149002040d0140c50400e8485082c00c400079041d03180a42820503039500c200075140c2c94407461003000840458001c1a1840c046000c000200c5031f5900d80440001c602c0790700503250300c1c1480442d0403c9803c08000d02401100400704012095890460070b00079910f001400089110101b01d2080c0280b28 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 723255188 1250 723253938 723253957
    0x90f0414030406020c030f0d02071206061503090b0a05011d1e0708011a0703090302040902040e01020c0d0306140904020d05010b30010c090b090d120503090f060705030a020906 77
    0xb4020400940c0032404800f029000d03800c0b1901140812015a039642220103110016001000140311618000074404440c601601c2c0116002d501c5682c1c00c090002c03403d807004042542e800c0d042d804c02505041c01a070107c40e50000f044a58907045031b603001c1e50700780080030307441462420000e290000c2880f040c42c04035031b0700341c500710340f41c900711101812070b603003c0c090a2031070041d01009240100485048550f0643d0660701c0401d00c41c80d560134000a0302c8892022072388991500d03404003a0440900c050040f0b1a2108010101012088405021140290820900781489038121400b549800307200c0c41c3c0103681510307401d006c0649070030010b006103003a5898a078001809a8070560030303207461040510041940b103100350790101e10900642203d00c5a0510000b08100b003000f080b131100d089004d48585400641001c600c00c2e0107985149401c03c8800512000c903c01000380142c03200100500c1855940300d400509050602803000341107400014401e01c600380d000104d245454441c40140d03090400d = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 723256438 1250 723255188 723255193
    0x100207030507080c060907081c0309140111090406090b0f121e0c041103130201050a14031e06030a03050706051302060310090b0103021615020f070f0507050906090f0414 74
    0x81d142213580d8581a0030f85a02c2d060b4460341c940411101c5020540d064022100004100c42440510069001e0305600340190340400302072aa4102c01c2d40700303001e103800c05d8900000d0140d0300c0c40e140082104542c610b80180c01c03058900b418040458032038800703a84401c00f003200d503440a81c10484005162140d4440d20000d41501c90a40480420001a14201441d0229018004080c00030008903a5010881e50341140144160b441c0c400340d40608020031301150301e860003504c9040035010307a6259900079240b4000c0d10303031490055080c905001d410303260807100840140c00b0520f190340340104940030b0054060110390750f8801090741a4159280d00c2105540600b03019260318002c120b000b1350f41d0480c8250030f100313401e141c1840c00961080c401c1b170701d1031925820b00000041c0240c50700c1e103040b81e80e505454a04ca500b0001070402c001001d000e80341c0d880c070a079070229140741e881c0b410a040144079030141c0c0c0107411090070b20005945491526600c040d000d24909101e0752a4100410240c900102111250 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 723257688 1250 723256438 723256447
    0x10b13140a081b1c121404270e0102130b0d150303050a0f021f050c09210d030504081605011b09080105011d040b07020a05151e010810020703050708 65
    0x40b015490800f030350362002c83c2c0f04526004803050120313540804800041421100c0529800e6250041740707080c5803040c41c4080b050420380c450301b800d09210003040304105a0280d00d14042c001401c1d5014103913040070520b00942c20b2180b566406405480c50f0f0061800382000868500e100758050b9201510382c803c001c1406030030ba9070701d003005020341c0d000c0044000007800e40845444402d000140c0305140100540f00d040090b080130400b60002c14001e00310270314041003049401c0e265a40c0003103c80f60702070701d05c45184811610804007440c1c54088490402414180420400462182026900d03d440c07031104070030074094a440c0172801004480c440c8541c0701c4e142c06070b20208543c07040802041e110300354000c01041e62600201201c07002c0d041001981500400c002500055101c07003c1604080c082c0115110b050b015540d540c103220258549a029051020400810080ca681905054030245800d140194117001019455201081101c075070b85400280c1c2c1800c041c4520101e59030b10707412031b090f035032134 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 723258938 1250 723257688 723257713
    0x3070e042d05060105030a0e0322080f010506030a12020309030717070b03010503100902180705030a0b0619080c070f06020a0206011d070e01050d0f0c0305010b13140a08 74
    0x8020164240d070303804007403032580e2841208140c4900b40c028807050b1601400e5903100035000c0003401c8180034030001c9000501c000d41c034450b0081d00c443d8034003a12540c1c00010030300b030410151400e52210340d094a207a040c1030a00c591600c2c0450004406600150000d040c030300000c105034918403500642e0b83e0548030750640040d0620a03003d54104001c00079041e074408030382d00c210720380303041c0804e002c0e0550507009558101c5014144e540141d5010748003030000b88564140d030143d5005100100c81c078901144002007000526059840740380c1c0040d5045034070a0070030050400d03620300b4030006017444090103101380204d440300a10805a8504c25840404e51061041914100000e9003280303c01c030002d803080000118540c1d099000a100c0d02620100c00480c0d41d6074030790200c0f00c4050702c12441341030000801c4145070068007801307012500c01c259513000c07503542441c540040c2144c00517484104075010500034004064203c0031110115410050b42464906a0000043c003000c51540214418401c01c580420b1 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 723260188 1250 723258938 723258971
    0x309030610030f120921110102010905120304021906030b0f09011511100c1214190519141501090503071a040f060801030c06140a0305040510151703040b03060603070e04 74
    0x100581f1134500040c0401c2420010382c246c03800000000d0282d00715088061800d500e0b00f0107182d1250000340b170001003603081c00d03120708034548030341003400080d131510004001070510303540c07104840b0740a4030050415807501c008128559468810b110401010544c03c1024401c10001849103401c1141c0c100142040b0700d90240404c030600c00d6a8181c58140760203a504085501784107845054004d000c00321401d01803800500502004001d40108020450b440080310080d120307000459601822030740090812a501d1040b54100159407410840c4045080c4441e840109030541241c0070344045c1c080e890103807440c00413540226004281c04140b807410020b002c55006494604882c01445815401c84e183c1c01e08407100002010481c1e1392840410254105034441d901c0298418050415103821440108240382500c0c1c58980c003640c0545206400c2c841c2c055501c0010901c0710801e00154540341c98450100305600009109a01c034402c044000340e00302e400303a0f1420f41c4221000b03104002c2071840700d14130312 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 723261438 1250 723260188 723260249
    0x3030b0f0411090310020406051b0708100f0e0c0f0126160807020c0a0302060d020d11040611060915090f0106030803100b1303060507030b0a080309030610030f1209 72
    0x340b04e4450321000c003000d006035200702e030203803091551002d01d41682075100210701040c60750b020071a0b101c1c1c0000040c03184400e106001d20702804060208046600100302425500c5402c800c0c10fa0350400031455a16664800d000d180c0c1c1e03002801c11610a0604c03446260b6060548900d440607218241c0c100241c2c001411840304110025865552258072a96412656240050750081c1c200000c0b0f070050001d03203411800381c0480260000c0240c68841b0074420725058460076500075002020209050107016003000c49410107030301c40c03401841c0a162400a003079503070440200d11006405041c01040b0640000e0101e09038080d0044000d0181556918102c0050b51007154021004060f8180c04144545101d0889120500400302010130a046031500c900411014156200303240c0c1d42d9181c2d24181d2130b1044035400510401c4042c50720340d0556400d0604040c001040d00c10340301c40020052001407420320004044d00c0c0c000c1c551000c1011f10100c1980c00e0304e031503003220a800b0168105c11100e800c0103110316 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 723262688 1250 723261438 723261457
    0x40204060602120702130b120708011a09040605060d0209070c031d06030f090709060603020310121e0602090d0b060111032b020f190305010e010b040303030b0f0411 72
    0x400c1466518030080ba00c500c0b10450b0340b141158100065009850710340070f18600c1d900c101c100003e2008221700060020500c810400c011a0020f100401c2086028450204c01030700030031401a886000f40001880888014401010a0784e070343e0116400d91034174080281c2059000d00140628209801d010f4001c40398080210002808003c841025920b183c2940482030004fd0440b800c41d11242c8101801c06802849140a44103507000080c200c10706000f282c001b46030617140142e484c20030581010361782c0015000251070280c1d00c186030000400f0814040c00d003581310803003201c0d01801854104040c0c0f240c602d4055000070720307004d00800e1002c40825030b805840b013602d50303013104600703882d50603113a015a10301c8006210982240740307400c424900702032030900902c6400601d802d0310b50840c0200d6030446201c18010103000545140c10b2a01880b0b0140580441d4060200940c5402210081807056000c01400c140d10743c1c1c551807260700e441d050492642e00040c003c0c00765556540e81d010712600300c880740 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 723263938 1250 723262688 723262691
    0x20d08091816021209010813020306011e0e010303050405060a030204090627050f131104060602031b07050603040305090f0406230436061e1b02060414150906040204 72
    0x42c9041c160001620b03034581c0b640d06034001e00703124a504c01520240e0740200751000c4a0b0070424894010703901800010301806015103200806d101c145c070b400314140100d8101d84c0500810200600200c1c0e0000280c40485000304c55285d035503000c0e15411406401143d000508107070402001151600c043e040e1a02036002d803680c000300d030781d500c0018801900c005403440400c800001003c02c2400380c06001c46a890741c09644900460f004010108048070303042c0c1e202500581020910307041404107106c1b111000e1044a0042c0782450a00303000072002c0c480070300020103201000401c10320741d8448201022014100070302c20032510340c1c0c0742d030034080400e082060a0305800d01410103071000c1c0b4041c4682038034144c010b804840c07003c00d40000346000682d4089045024000342000c080050030b10f000d510150007076041c0c110b110907140c88031041518298088001c0d9071801e10481140c50340e00041490344260005140c0b1a41ea41c1101181d003004034215503100c3c210229010054001c10010702d85000d04e2080d81c0 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 723265188 1250 723263938 723263971
    0x6062115040e01090c0e0601030209120a0201090b0c0d030b0a15020a03030b0402070c05090618010f0e0a0207080a03110f0705011a09010f140a09061815080a020d080918 74
    0x110508803240c051004210040409040c018846e51607409a800365040c1001403801e030142000440d0482c0700030354285c40e076200481003802c55030700c2240e107002400c01a4502341402c0300441074039103a40558100c2d500b05603450624840d035a99241c844e600905004071003c882e038220080094a41c40700702c5086e00403905001050b1490b08181c4200d0f400e15070410000f0b62007a041c40d0402c2076200340070b00030a40c04250403038140c110181015410380240241f01c007521106e49000080305d40e440e0010036696415105000c1100412018030403140881418900050010500304060740c4a0141081018110002041100400005601c06040d510b00075120101803000202000a00402402010701480b03244204204004159148224440005000030400354a0321002d504031409a40489028100c2400e8a01208528480c494540050a50b840f1205050a14581e503510013590300a01032102c81d080603003841042800e403910b0403801407601941c24500e107801c030a08001543c440c0d80124007001c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 723266438 1250 723265188 723265211
    0x20d0b1f0207080615150906034b1003060203090c0108010504020c12070c0518070e09040c060c060207150b1e01391506050f03060606211504 62
    0x50351391060f002c40341c04070354451310002485089900d5035408a84040c043c03003400d04503510a00034520610030181035000300d2018000c0c00300310380a400c40601c1c03404c0341034094122104083c503400807500398a20382d018543d140c0d215640102100c0c2c3d8406440581f01106100c0a40701c0860345942d131002c01d9954009c00d903281c0040000301d120f07032510b421080e8001c841d0654101c600704050510640a9103207009029a5000412201c2030442090a0020b50041c00c02017500d4224480341c0410768169202c0c10f49107001c0d0b891500b021150700402e000e1101141c040010028640c0440b90b035603500000344000c4a440108610140041c01202441800c1e103480d945071081c4113220403441d2403416965044031160801030080440840b2002240048101e00450900000d100780000c41d20320071590007901c0b0058080350030403103d40340c00282c4650720b954804c1c1401e0740d00091080d0090011a49a5526034640c1005038080c42c00d007260030364027021082001002408105404050081510305004080694 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 723267688 1250 723266438 723266443
    0x10e25050d09050c0f01080630100618090b07110a050f0d090608040305030c0a03180b1503011103010b031003050a0f120915120609090803041101140706020d0b1f020708 74
    0x21a8116045200c0c1184800c1827940c400c03050f2071208140c3c1031121245c462000141c06c04900d4444003c03a5515140100000c0c1d40b8003882d80704001c10b0140c00c0110100d66034480303100c03000107000d0780300300710005180c0009902e040c00305214540e07210381114404092028100c1d02c0c0d0804040e00f03000308980c6a0000b0b82a1300a4400038400c50341541d45514658901203580c203190402080030040640d0780b4007941104c00740c100c8080215005010070b00445ca003030707000f070075452045e03440d900c0c0070703034101044003156420300e40980b819250307118840ca4036907903204100200a0134070350018090b88500554901480304098451b807142d401407985855100c0001c4082e940c2c04160303c1a40b8400c88120342c020f168030712070481d40d442048450b90208034079640c1c030804c40656902400603a407040c800001d120800800341c903000c0c441c407000e0800040c101c014640c240b442d4003400c40080c0007540c00042920360f03001254400e003a0880020705071655411034102c031420000d00a010f1402502c100070000c42c00e020700 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 723268938 1250 723267688 723267691
    0x603162c0609180c12010209090109061503051f060c1209030b070f1709030a021504230304050a06050c0f07080c01050d060b03090d0206010e25050d09050c0f0108 71
    0x1d0510046a100c0f43e11110007081200ba084405001d9000c040d405991440307142c007200002c400025031070b005180304000d06924180c0c000c003030143c42c00d58100282444040c40740c40c00700040c180061941d60b48015010490f1010610f122154840140450700b140c000383c2d03055405000b0034010b100e201f40d00406441400349800003402502d208030000d1085481003400050700304151400004500c8030301e268080f001425101104160070100d02d038a6444e81c10490940a0400d6203082103080c1065240c0c1a24800c5195191100c80d04c20602030702130200c204203c8005040142c0710001650307560070028015081070a45241900802142c4100120b0000b004030a0340c0a0402600041d010781005554a910169424140e591a12000100c84414101451081c40064090060400d84001c001d044c0b0005800c0551122000018040c04400e404040011100c0d0813560783c50411440c00d080d87e46015500e500a505803c2410301c030104800480d9600140c181036070b404883c12002801034071107100 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 723270188 1250 723268938 723268951
    0x20d140f010819030509040608070611010207080d0b0a08060403030504031205063a0507050108090601080d030b0114070f05100b0609090a2c100203130b0603162c 71
    0x2d00560301003030f40072030b1501c05518440d0624504e00500d0001083c19106942d0020002d50004101009640c0d04111041c841152401c02180790120b0360355104c40c44d00922034040368460b0745004095158659104a0000d00b00c030104a0b6510b02d0a890000c0107000e080340c0031000200710401c40c8043c01800e01555001d0600103004c02c9403030407890b0740d820360303004140250390548008040792819960610684014280500054200f40d030403d4005011090043c022103640d5110900410030300704041981d407a10328103458040348c00c0c40302200403185641c2c0c2c3d5500700c658120002d8410b04001c9060b82c03191685128000fa92000c01f0001c6e4000b045680e442e80c43e44c0c210808020403015880c101105039881031403030100043c02100401d9440912650b000450b80001b001803581c50168010446600d0b60901c0032405d516501d000700c0421a480000c08000344803000244c0030984a42c1c05009500b0a11100280d21208980d1522003240c4c6150070000801040d80e15402c862000705078150700c40c800c03030 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 723271438 1250 723270188 723270193
    0xe1609080c040515060c0a0b06010f02070b0901120632060901050702030a060207080304111c12171003020f0603010605090607050307050a032006010602120a02070504020d140f0108 79
    0x12101014000540f07801401a94000b41544e00ba02155850b0b401030b00e2040241c000410000d520351030000c0394204054402418849010380d075503951030303000075640c0580740072190b1a0f4841e6150701c0141c0380010054040702541d41450000704202034003401840100da078200b640c04280021a80075003100d2800880d0301d030403d2081004088a50282c8d000b044801c0c40982224040d81060302c8610480c1c2003e81d0454242c0000010700052100903810100340303002c100d440301c100549400c840d040c200301101c0014111140079418184d401e00540c2071075544141503819443d90300c2d0142103a0380c001154003049120b6404650718000c2c504040c1e0549050741c440b601e40f24600440f407410403202e030708006011a40c510081055400042041c070800070158442d864030761545507105840c200303202a0b41f0146070746511240041144541c002045c440c400e034080b0685590741030302d6104a04084590300810303041400003484c0c01034108154403000101700002001c200c41c0d00c3e28131030b000c0300c001c084c403c0a8030366 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 723272688 1250 723271438 723271453
    0x1b08160327052b0804050a0e0610031a10080a2003060616060c0801090506100c06020a2f1204030c030219030b0405010e010b040c0504090509070f0e160908 68
    0x103060202d01c40c100c0400c41d80e070403c4003c00015521041e10340302041240d010102103010011410036150007006004040300c11503892800324003180d008c4620010080030581c42d03006040d0400604c0c030508030300c0c03d8007400e0180e07070200c00c201c09015000155080e00c02c242c5400100e64604600c0d914400340a1060841503296803554010080c01c0e40081aa412110600240041c0003c11f0b6115180d030760314030340d10341810f1503140031684800c42e140182400d0043d801455600341c019802407084800ca0b600c80302c0141c42d41008030301141c80150100c5948500e50b13504884409000e01c14042c6040f04800340200c5003440e00380b0509030040c0c055440300412241030301c4018001440d0004250b00421071100412800b141d594441e06110242520705841c42e9556000c103a003083e6084c01010318016007502c042c002a000203000400300c1c0306900c9100b402035515404901900760900c42940103090505002e40299241c10a855168a00340e410707440c0e18605040340d015050250040c20119941000540b842 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 723273938 1250 723272688 723272699
    0xa050f0d0212070201090e240609060a12020c01020f19020c010f2105041406330301090f030f02060912070605090c030f07060206130b01061b08160327 66
    0x56044803030300328140030306c500c3c01056034811088401d205181949000114540d01c0760b5940000300100080380c000c1000700207048903a12580c08481a80d001c070702c0c0a141041ca441b0717203c0002d000d40c040d14540381d4000542030034080a071101400c3c108c000f040070f40c252111030020507650340403e15003003400f0841c00003800c1a410b000300c10f0070713890704141026445800b015200410840e0340448044515050b042032009828108004159020f030483e11107095075080300c402a0303400f1490100c1c1041e0308209a100c600d03561000e40290f14190760080c21428410002e14001d4040d900ca081242c005200e80c130001000c2c1c10000072940000110300c042c2c14034019081e100c100113440000c01e42d06c141e00c00c0148200040e10704201e8504408506800740c0301140c18400000d0500c007018001b031000d5003842081c40c012900c1d1041c0d4038112403042c02c1c035021480e8803440d880392003500340002811036000499080c20655800507281c140500c01d550360a0140154000c0700142d0443c1c1e60030950703594400205002 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 723275188 1250 723273938 723273973
    0x1b03020102062d0c0307200303011509030501230f07080f04060e070f090c09031a04050a21091502072706230114030708070903020907020a050f0d02 65
    0x41401e40080c40f8038201032030102d1812240001d488041501c88008200701c0d1342640a07540e003500c2e01485601c01c6080001c00c803200d60728001809880300803002c0d9014224441d0142c44032a00842d2322200a2044580c2c00b1140c1c0c010080c0e031850000303401c01050011b50113003209150644075800c80c0d220106c02e0303110078454054900c8024800c4513069910a076110072080100184070082440c2e0300d507414418104043c0340c081d03808084603c41401130004d400c0c40043c000450045510801210309421a510b90030200e00e00b40c4000d00c007802520f008000080006078122052107080d40e0381e111a000c20f82d0b82c5424020740240f0f040580b0041e04403070b000307011407400718188044403419810000220f031005a0900110b0300c46074046034445e05110701ca0365070f002ea8020040f005490074201202c3c50710f54640c4c402410303c0010150800c00c403030000040c0c840e602500440001d550081c1820115181481c0d01070341c0c928112000351004c1c0700e55441601c580c140010a001000380c2c56001e032500740d941e0722a150 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 723276438 1250 723275188 723275221
    0xb03090a060f110d0f0f06050d0f03090b0409090516050904060e030f0d02090315010308070b2205150109151a090904050d0806090f010605030426071b0302010206 71
    0x480b415240c0226100c1824036101800180032040c500150246036202c64034102d0f00c1d804050340c0e00d84e080110801941d600c690107451801e07080860f81d030317401c0c0d01031034115400381c4282c01804464201260114290a80758000f40b41580324204884e5140c43d01e0070761240d10262440340a50101052001900041040d00300020031001c141c1102d00b002a400c80221154000713040084805a000c030702c070f80036440c0c20884200e40004451052002e541941c40c1c100080c4a600c6000d0034100c00040416010820004421b0b01c0c051071b400c11f80b649101c01d10781070b51280d20b41c600c18100c4402000c0041007154131440f0310054111803072010640c0624146c0713154608103429000920404040c4802007007038450310031051040b403007200582582c941d00c11010341001e00103003449000780410000c019014444190b00703415201c450070440d2b100e5503503103840e03680300441102ca030b042008040d0362845a9041030019080d0f41d44101049450049144802c8024450780d22019005078098008200d20202c0c2d2000c06 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 723277688 1250 723276438 723276461
    0x60605131d070507060b1c0c1205031b12030f011e0506091306030b0c12011d0103020411070f0c050102070611060606030c0d0e150609130308060d15150b03090a06 71
    0xb0400642040007d40098254040d5010495500b207130407042100081d42e810240484502c0d0030138680c0340b52210744e52402404040400c080e03c2c0c445942d0303041c0f02006038040000001c403d01e030fa40e28001003000381201c001c0c40b40c42004006044115a4190800f40c0e12040d51b00242280d810a40c0f40420441940031305810805800c0e036902c0e001c4049081098401c1c8a0901242c0b40c60ba109086a048184004168020303450030344018540308000c008803410504480d01207074045500c010101c5554130074881d022000300f150314981a0181000f880b2813505089071000d03000d0318484c51340d5080549140c04e50070405e641e642c22290003d138040c540b00c0050364006001e00001d50030840582c0c0b041d400c40c0c1d40c101250100e0750180042d04910708a50a0317141d40f080c4281c0d810b84d22410903008014210a2540c0c0c010113005502002a005498102c24108110b80010174407100403003100130000105015207000030703104020302c4041040e142c1c00c41200c0c0155141401000304034490b440b020003c05c1790402d007 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 723278938 1250 723277688 723277691
    0x21091c0f0e1917280305090609120d0e2107090c0e0607030e091003050606091807030b06150c03030705031b07030e010810082509060605131d07050706 66
    0x49a0003486203443d5901040d041e000308900c02c0030b4400600704800c18070344019210340020000001950080c00d481800300705440a90301c030a1104002900703c040303044024818840e00e507086140e030390310030b0707452a80c03040075122040010300c40b68070324000b42103415458016502449c4100680300640e801108030030540d1900c4080041c503900010b0440d40602415400100300342c08138a407601d06106542d800c401202500c001482c0b555407001d8548100070059407080f038110300010f0740342a10341c0d03440c07050010b4801130b1000c2d44c5d1a0300e801c988500c400d5030130500510341c6c4005030180f80550300072141040f10b00c0c1c2c0150f00f560758442003210b507507000400d0b49a14134510001c200c0250040d801424046210f91104100e02d034001000508422000341a200c20340c640300001c0144000100b5480c2c003280001800b1805440c1c0c0303c102142250392907216400e19031800d28009101907000020300881c006c2440105801c80c0d46401c09172025007980380285600794031201003810207004a00606100348905e50 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 723280188 1250 723278938 723278989
    0xf070606080f0f0f0c1f030b040510060801090903020c0d0c080a060b040c0c02150f16030f081e0c0a0c120305101d010302040221091c0f0e 61
    0x2010b0401d40c658044031801d81c070000c02c0703044031202070260040002c003600c010815140e442c80080c034010700d9900314003c40e240c928503407a8114400e4000140220303001c0c00500c03a6003484000d032400c190041c481c031000540f080380003092001c624015854001d82541c0141180d01a0000700241005903c0c812a00300752510400035040c0828082001041e005203c0010920030100c140401d441c10340071094200052036080e070700180e84290290b85009800b42d500e0ba2205d141460656051141206201c10303142c0075003461040540c41a070415503060b950340c54206903128410064560b861008142248044900c0092203011120006c0d10f80060b061a2510001c41e81c0e46920400c0070070b400c42800001e0f20741c410010511119075440d4014841545110b44108104682d149500d20600001f84031b00d400240d0406204140300381d180d07840c42150b04822581c01c0102449690f107140308001a01c1c1d000000c005921580100c40b40b61314101540c440d07504c041b41039000c0010003064407403240440e624041 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 723281438 1250 723280188 723280199
    0x2091201090606050f030a05071511070b030a0b060f030c07060b1815010903030813020a0503070b0a030501210b091009080706060e0613020703030209090a0f0b010908030f070606 78
    0x194104030703070088000103041400c003400d00846404600300b0714000d40c02100c110b00050000038801d0300700c460440c0f10031002c81c00c90608483e9526a03d140c0c40c501d11904402003038a100301c50055000d500034840400a00100d1410b0001c680286804144454030034400039564000c0000208291445801d0009030100300f0030020b604242e80b04040140c40854400300410190a000ca50f0140c040900340031028610b0b60794000c2c141c7d000180080000b008080d4404215103400c001d120143c43d005040d603039141d031103c180e1259604803061020021742401c00024440030f150b0b40c101c142e80504030014590308841e45a0301110309024220702003e103d61200d070072091481e0701c201350142c2d00c1040001c0d50b41c17026080c603000303656030b030b40010b042c3c10040000d21000d17545124044003005085000540c903020281001c0e00203009916074a50082c0e4001c00f0426841c0c901d0f80084443d80d0410340802190082e03400441d003600881c010715490307910412032102c050300300f41c0140031900c0c41b5100c003068a51325031 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 723282688 1250 723281438 723281441
    0x1e0b0702060403061b030f0b0d11030a0609080c01060b190806131b020c120a0311030f2b05040213093f0c02010f120b030706110708030906030a02091201 67
    0xf80e141034200d100c0717009080c6050b454041d140c0d02c5d65400c8414404c03585030342c0c0003400208090708001c142016410001109440501900030402c0d0007110400c8140040e06010b0429404901c022025501c6d2810200c2c1c40b00c016001e41c5d80360581040da28400140e000d800307940414024150725440000c40781310090281c842c1c0241348010742203205e0719100c0d400000c0040d203446804904284120070429584143e10300020300060650b4162030700d00c405050481400381140704041c84806480400034100e04100d042070701c5c0d58a442044041d03201e56614041c01e200841d40c0070b0f203000358070140350700c0885100d551680042d0131380b90007001350305580c0300f00038640c500041d815500050005c90300e001407180f0b003030a02d2000200130001c1c142150400c40c1540000c02003004150480103000d840710070f81c144c10329036034485402500d000d0100c51050b910344002401003107003100c01c0c103440d114000d00402e49a00200c1a00e9240c48041c0000741161241c001c101d020b50481100b09401c500034455000e004a000d = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 723283938 1250 723282688 723282701
    0x910020d1508070801060603110304030c0812100518071706060c06100905061009060302281107080309030c0d02041401120614070f32131e0b070206040306 68
    0x10341005200b01481c11313021900f526015880241414a8200e10303800c9400c000b02201d42c040c2c2c2c0340c90501c4610704640340c00c1c1d007980034043c04d60000c0306029040109a88040c074002098420840d03581c0c0e5159602001c5050200c070803903205000a8805030740144000c02092280d8100c0c500030025820700900503d190700c0c000088031141050800c003c410000c16440c0d10074590800c0003aa10782c500c01c448a440502400c0702445218200356000501c2d04050400c18012000c0540b80703d40380030a94450395009004811014882105000d02c501c00a240e510002c115005040040d01400e180e45910080281100c80b459060f80c2068540d02180c2d0013480c510000b034041c0ca40c2000e1085c000310300d4145601155808411600c0d141090f90501010383c9c0c1000755025814a5407402c5095001d20a241c104070042d07240e203d5800300003400c41c04d1440b10071103002c0d191a0b0b200680302641d0582d40d150049001c2d0204035a20341480444000340500b82d000002071803154005043e191506a030390b596402110170 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 723285188 1250 723283938 723283949
    0x41509150507020304060507080904060f03030e012d1215080304030507050406060c1112060c071a0103020913031e03021801090f12050a0203031206010f080910020d15 73
    0x4034540e54001010140728480c1c02810620082d0b007000c0c01d10394050315a01c00e040d405440e00c0004a900c0c40281e40342c0d04010b014040242801d400c2e41c1c3d0743d1402411007060442c00b903001c43d03030360840d9488100c0c2d003041d441084000340d2041c10001c00c01400540340c40c1880d0a80c3c003480744d121440d06095032a03505001000300701140003140d8030f92950030001e051080a412052285013401d4041040030b81c07240d0014103c58001c03c0c0310341414a4980090060705440e03644a07124010001040803c9181d04042c100c241d00800400c000707810030408804415509000080d484019040800c140002079110200d0179482403d0581085e132184403e00c24200340d40b031180b40002d07000284080d0300700c010100440034580030f00707041c645039040c02c3d100240c480b0305010703c03002ca0820710008018003104101501e141d87c2c01409030380e5180b80e046031455a000049030050b0105034012060191503104207101d0f40304d600004094071107802e041d40101c2c0030750f2080c0d22214070380303448500c010041c45028650800500 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 723286438 1250 723285188 723285203
    0x110d080105031507091505090a27051006031e0e0d09170c060d0227030f0a1109040309051002010f150515030915090c01021e15041509 59
    0x41c900010186031a2169900746409007051052110740e40d0020420320a41d48004801c0610703202d40c8104540b58004e14610701e6028010440004681001d001640f03d04540480001d6003c01c000c040d00050fa03000342e505910041c14400c0c10000b4522036440098124042801007c0d4950709460010940361020b05050075a000111400d1013260814440703002030030f02d9282c00300d40040314110700d911140c0d140c0d5024003943c0d00050028a0072890360441345400001105030120a06080300d080d440c51041000d00d02900c92540c1007a1625000142d040025500008403103480c03264900f8001d244202800031030501001802c0461641d4540e090310300c45680341d41c000a1007036031031080c3d20f0031303246100801c03d00d240d6400b41c1480305460701190700b400f1808507401f481e502d881d0b130660140b42071900000856441c2680d030600c501c681e00443c01070417401c0c2c240e00310340d0200410f4114002c0c074814075510103030b65848085c9210301b10529201503540103004000a200040000f00c0d4441541c449050444840 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 723287688 1250 723286438 723286441
    0xd0204060803120f0a0501084c0c0e060f070507050d05062517100509011701060503011a09270304081509070b032208120f06060301090903110d08 64
    0x1d07442e43c0020884170510141d403401105075203403036195651900c1c40f5058500c1c5408205041c5140b60442c1044980c0d180504072044136848040c16003070801001e13400c0804000180f44038005d82030100b48000c1c40c035031a0071110640c41180c0c0e48002d001310b40d94003ca4030005220b540c0c20541070101405480507001c90301d010200d0044100c00742d034024075070511860000440715440f094180c3c0010b10001103103800e4403000318114401000780d12495000307406000114146d10421240441c211060009020258031941003600340c1c1c004003d4140c20800d448081016460000c6020707030042c00c804400920007403984080700c0c00c60000c010003100788e0300014040022005c00c00201071901d0342032200a00307904080e140261521514460000110000b00224031203126101c1d00904040b110140e09d03d45048a1a0022082d003058400800d41402d00001604140b10781054501c6000002c100c14070f103a0814000d040104541c500c01d404020b001813654280400400812164200e59110501c46 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 723288938 1250 723287688 723287701
    0x170c1801120606050634230109060617070602030c2d01050c2a030a0c0c0b040e040c08010513020907021e0106050901060c0b0402241201080105010b0403030504050d020406080312 78
    0x204000682050300300d00c1c4020300100428840840031151142c47c0e0181100083e100d001a0301420140d00301824051030603200180c0d0000b80384046d041135040d0341c01d44200d5a0760f00810303600c0e80201d4020006a4100700410454044620794001c60150351000440401c45016140b600310f90044981000750000000d4140d03841c2d4000c0201c1a04002d00760740685c03998140c901c095124040c010007c01800450401c00c4104138208401101509080301020b884540e10340080192641c02c0d41e0503200e0082060010515800c1801464420780d0015402d440501065080c864203000042c100b5045016040001c0c04070f040406040301c3c204400400800c01c103003080304010301c03024181c0c044c3d0188454400401c0024881481843d40140c041324120900040c003c04034180c1c84180ea04884442c00005450100d141945e00c942c2c16510322400806c03090b03032260062400c0e840741e07001c0030300458014042000715150a1300b513691521320240002c2801e65450510300c0c0b0319041006800700720810081000341 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 723290188 1250 723288938 723288997
    0x3030e030a0c03080906211909080316051308010b0f030102090d0b06040f0c02010c0908030903031c1805030403050606010309120507020f0a170c18011206060506 71
    0x84981200581001041640e40071444401840020080c41001c20030800fa0380d03410041d034074070a440b80c5861000880084100c12142c0c0e044400e0782040341601c00401c0d003503483d841080d0303126510040e21403a64503580030213850b0310100744080e01000003c001c4034070080070800110780108494000401c00d07040e85020000c0601d8404811781c042c4c1c1c07050000f600c0a036542400c01803120b81240040340240c8480001c14040d00c0d0011030030350324a0030b040d0000000e560540c007007250344d4003607980c03201281c1e11154950345034414601000e80c5a4000c0c404034840b401c41c003c0303410744e00c0f10701d80e030020314000c4503c105013003020151000c2c4c510350008102003051000c01c1c0150740e445202440e0800102c3c4042c3e50341b8a8000700e0400220403c80013150380d2045484034800b084c4861030041030302000300c5e0740b0a6142e038a2242030340001854090550380c0c42032410300c030003034404003030070703031082c0d00250b820040345d900510f650322010307a0050b8440000142e10380707030000100805512007060340100da16a210000 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 723291438 1250 723290188 723290207
    0xc06020d200307030c050307170c06090a08090f0a03020d080a0f020102482a0a030201080c04090501031505070513140103200c0d18051311030a05010303 67
    0x51102907070050320505041d002c41110841035141c1801d50f034489103400c0040c5540640f0714024a410000340c403810006a03030310040c0c00c10b007844000304c4074955a808411138841c20030180040c84003005101080380e40c503008140c04c669200240220050300d550f900058101c060407503040d6282c0e60005542544103900290704a6000c800c0d00096141c501c50351003004440383c0d8104c104401e140c01610804040d0042412001e131580d40080a0b0a02d44c603060100385c981c140c410038201c01100644040f03180f1609106c0d080103038a00105500d05007481c42d001500e12040091016880ea0b000f0800031540382900d20485001c0c5018030005016500b014031048200d400c0a00300005000c810f01000800405014000003510908002c11803421002c0b001030303001d01a0803c407030b004490500580760a465174000070788105110030003100c000c141c06043c2070b10207020000d551496040e580500b84418103050640d1021041d007108001003d0720340d202000b695407c15150ba4003002d481d80010801c0c56880484030303 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 723292688 1250 723291438 723291467
    0xd060b120106110304180b0d050c12010c0e061605100905060c070f060c0509060f18040b06121b03070f0f080717060303040909240603030c0201110a0c06020d 69
    0x118904420554400d6490017948180c15041d841800b010340d1800036500400302e03464020302803c0303442c00d940c6070040d141c201103166030f8003400343c80c900c2c1a40742e8414002d8040070b600035200c0c0440c1c01042014001158801042c02c00d030040e1204840740002c5042000070b41e081110f03070000801c01e0061920350306214014200c00743c41102806230781c0200c3c030081d644041a40c0d1000c80010220007e040a49580c0a005d01d80c07a408000400c900325076008110080000000a0181c0f0070034001c0003080004503603208011541141050000c0c0c201e00000070800c940140b031b00451340403109210038040c0d0050b802180c0c81800200310b01c010a14082d0000c5201d282e000190a000302030389481580140134500003240c41009d000600003240ca20b8909104607005046d60031000c0c02220084e0801d603240b005240cac0300d0094807008850540e89031215200328030a0307940c95503d8100750801900112070342c030914600c03c42d941c01814005000100b443c82124007c0c400358024007060189464080c001c6a8501c004 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 723293938 1250 723292688 723292697
    0x12010b2502090c090f090a0e060a150e040309091a04050f04150c11070f17031c0504060f290d0c0b031003080a05030118180303050a020d060b120106 65
    0x31580140d94a65820b03a100c1e51601c016622100a000080e40409010b580550402550014031640746081c2d0840084900b090044a0b01a103d100c800300454400c00340c40c0310500c10106d0103119403101c030788007070390014081c2c9032101e415030700c41c4495400c035000c01e0008800c042c1ca04903000303950b05090180780c2d8851f4840c82c1110780d62629848a04050301203000070b030486982e651110420718040e0104002c800c4080b130441c1d58058443c000004c42c484680280e8509500e0111a02e803405e400101311484156805403940c40250100c3d501c802038138001d0310845110340c0396028008441c0091140300c3c1c0c2d00e00d03a03d1101848072110780b6080241900c6840071400340300f0144c860740110302100c001d1003c445146803030a550740e45240079607060b01001e0700000c0c01c0a0307000603400d172041d80c05005541621f1354a81801c3d0381c0280d02e0042c408803021545078144040c0480001c20110340261f200c0c56010340310103400361904021020700b200b107420f00d42180309401c401181ca06101050001c1d410301600a50030b1 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 723295188 1250 723293938 723294007
    0x1805090303061f020a05120301030606050603011d060d0f0308010f050d0809061605030a0f0206060a1809020102030f211305061b0405040c0c0201082503020c0312010b 73
    0x401c51140c01c12103d0034840d141801a000464420040b41c00d03210b80002c180c81400070b80301030f4400305610070b10043d20401d00f00b0801007007600d4440d003107034103c400280440011142041c03021402540091103030340c0c0440c81591800218902c100d02071155842079807038003c5581041040c0103051032942019014402000c003000004100790300700d42c441c40e0225401c0f0746424210300c84050a03001f5000041c25400b01150340034415420103501800f1268940a458141c3d80e0740d0f00b80b2240303500301c0c410247c0c41c09824404204042555200219990061041d01e20302070b143c030400030050f845040d06000d0784480d826842044118105083d4110000c6940c1c0790b807410320760302c0c0e00e44d4461f40a4403405424940080c075001c50305060045500500d0013800c24801840461130103004464644d80c01e0f40464280000200543c90f8101120042e514003e6900100b01c3c501d4001c800035044083c3d012064403003004828501d6900c050068020140d210500c0c0d510340002c040c20710b07014801c8046080c4401483c1 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 723296438 1250 723295188 723295201
    0x120c0f03020604230c0607170408100b0405150d0f0221062518052e091a070212070e090f0f03040611010b0904030806040b030f0303060d17041805090303 67
    0x2400c1c0302c21103002c60b4030703036187c2092341884580101ea040c081c848080d000140086c2c0c40b400071801d9004141080d104224069020040c881a0b4608840605070343c41c1c00c1540b65503500c0c00d81c04610520b401000c52281c07428660340461150754001500030480c5e154040031003140901088a01d901c08094060002c0f0f203949824001c030fa200c08001000180710382805e40220a0050140d950001e15001b0407220120a019039886100d40c82e001850b03810b4066000d0b4050300c10701412540d03003110501c0380d501d0b809102e00e07100c6d02880d41013800200e90102c042d241e624a00b00040140754003601c1c400e00030070858141416414130705046440700001a400c041d5918034150b00100a903400c542d43c5080c0380a05102e5032841e2401008a4198a0340c400e5400701440f06050380309500c18840e001c01d0b0f40402003d48201d00301907691070301c8400721344d11390300820001d1382d03a0a141d400c1c9103007107202d0826403a0a0101c03100005464116802c10038190400a08009454500340111034110403824041c0d4507604080 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 723297688 1250 723296438 723296443
    0x30919170a122a06020409180210080901110c0d0801050a0e0c07020402090d060504021c0c051002190302060702100b060a0c0c0b0a050c0105150d120c0f0302060423 72
    0x2440e0042400a07007078448241c1da0f00b04002c6004041a00241083d4080c249080c8000307402c1801299142494000200300118508500c1307030800b41c00402442d6020800002103448940081c04114595247d0b15000101000030f4084c2814842007406804d00d40c2041500030000b0005921440c4594100141000008040b080c50354128140d07500d141e94581031800818041d20400e001150003d85844004083c80f40036400345018034803c03625100034424800d4079044c1c4100600000e800d004a90608001510b8001c14841c01518240181e42101d4034120103c00c01d5030f620201230700503030001400c0201d0340364103018007640e0040a03001000924001d0003c6940b900451045105001c0711002c984144010105244020300d29107071050b50b11030182c1d43c01485070b00301020082c01c5600300320120b5403080c40001d1215241d400a0800142c0c00016180e00040b906003580c0d40051152000d1060041055410290b000d90b010b600184000d092901e012100f0f56203084007141d40800d45880703403100c0c4070301 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 723298938 1250 723297688 723297713
    0x21008070804121704061e0c050409020d0e0d092408150a1806091a090c13030512090f01030606022a0603100501090e0601050d0e030919170a 62
    0x4501c04820a01c0e07110000e0780c413a4020b101c48821041d5001c00c000800c4581d802160351087d407030181075820804201004151245481c1034804500c081c401484000d1095020304103801d0280400300d41005080321880c01d016103d202c07400001d0039110207000241002034900003000241d10710302e000d51288200100941e9025162903038030340ca80103440b0195038540745030b44090062078450040c070410a40b590b10003001c4e103200e02d1168504203840819101100d0281420b80c50700a80020416900c3e00b0319901d49a00c58050450484800300000c40072482c204040d0051380040a07800782c0d540d4240c4108000d4000780d082050415090034400d0001590104415802126414484001005042c100c0207644000b2940e1a00500d02000300301e401d0401c5080c1c2003c41d04284c80700020580c0700ca511074400c1e0000c4428602084007040000602e02d41070748000d03d402607000a4a0a1071b203901e00251000417003804030648445039038002d10202810320407012201c01c44030300420391100d45503140031800c0c0b003 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 723300188 1250 723298938 723298943
    0xd090f05060307170a0615020a15090203161e052d03071a0405040c0f050a0509040f090f02031b18062209051501030305161b080307021008070804 64
    0x7001c4086050035001d020074200402000000e00124a80081c1c210000d00c668070850308911108401c070704c62180042880001e464200c94058042e864034104a03000d81600c0d04200e8061040002400302194000e14040c00303441010301407080e50240f00000881400303a60041c0d03103c1c440260116681c0030036031070400ba0044102e680d00300e070042c0c0d000009040248aa010201400c1c02501e000c43d44685840180103039070084504014045400c1c104540e501d1100d0340e8207020500403c104c6101034082d001500b0080002840800c041e07001144460955029480c00c881002c107202d410000c6160900075031040d00030a4a41c222965054000941a000181c502c8100e0180c1c440108840e07841c0d50039044170784a241003403c1c1840f0300002006000348417089064410b80290210301d15004c401700c62990490b0b80540c2e0320b500b04130708580780e812080d0038004200c4d03686d0040030070b050040d650054607800a1404101170364481c1c206005210750101119413490030004210104106280c008140c02e40094 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 723301438 1250 723300188 723300199
    0xc0307060c03020d060e0f160225090c0c020109050603130f05150705071a0709030212010e070602010905010f0203013203060f010510080105061e0702060403030503090d090f05 77
    0x10722501d05070002c0c4074030040f1503401420000c0c003003070840e52400704034020007805041c0d541c241e80d440328103003003003100d03100700401a0032021a841e510381c1041001c10503107003114801410b540d5a5808041214000c006910100d07440f880090300303568001c000720004001c00d80d0040d00d07514110343e1410041d400500b004203195101c00c51002480410031803116000d422080d007581c00d061446000d001604204402c403040c4182074a00500800f10030492070107403683e41c840145490440d820400400c90407908001700b5940c4840210b440300302000034a0007044540c000003440a41404c0083c2076480135000f05d05d00900400040102480b4a2803c05046030482e407520104110383c92016051940755250f2a0706d84224024042ca0907200703c2c0f141e04880d0111640d1200c2488044242c0c0c1c4400d09106941d402003090000c00050400d82c01500806441c80c3c00440c54001d07190300140d4103810a800a400041e0b02008200c11000c0c100013002c8a00b2841c205010201c0c50700c80b0303421303d8910340e008050154 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 723302688 1250 723301438 723301451
    0x9030e0a0f0b1e031f150c08180a0308030115090513020a05070813260a03030c110307050706030b0303040305030901050702063c09030304140a0302060c06011a0c030706 74
    0xc070036420000c280ba15401c0c028940e641421074000c08861030b58007140f02c420000036800100700100007904606403066880d0b0300c40c0e414950700d454626400040e0240811603003c0227840140e0b07581c0920001a5200c0c0c85c03044d86a504002c100403040f02240c540500b800983c150a02295844400d5030b401584400e4000d40e4451b2004ca00700d800c2d0054420040101e04089152a01c0d08800d0040c40296030911828800316440c001100c10300840c003503209219600494045404a8466001400515101e0401e40c0045a0302e9000714910b0f40202e200795403e402150081c81200c4c1c0c103005802c0104c00032002181400e0554079080c0c0c592040c0c1400c1418060000b400d4401c41d00d80300b05803051a035040c00a00c07821031102500c000d40e40b0b020040002036103034400c03074856100d0084e4155038640201074002c3d41024140030f09001901c249040c0f19501000040d40000140e0b1410002d0000c010b00c24081c282c2075141140c00b034084c10540a22224201d018040501020000003e51f0a242e401c50f60104d5107 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 723303938 1250 723302688 723302707
    0x3010608190f0c0f060201151d060a0f06030504020f0301090218070e060d0e1216080c030702030105190507020307030503160c020a0b090307090506090c070312020304030309030e0a0f0b 81
    0xb0004188000d10b401c001182c000f440002c580007500440340b00fa0005c0c4009855500c007029052103a0083c200d14410410109034902d0307440c115194031901c09032003540d40c9030311005120403044480c0c0c0041c0002e03454100b00000c40c1840401500a540280c1c000e00c00e800c4a070380043c0a08585c0b0b100d001030003030340400140603079101d806030010030030010340041c0d03851180142c0325000e050218030000551142e10689844011004c0c21280e10817180407455182d41a540d9612055501a01610312244002d008100251344d0a1040c40e0050031901486020b8401442c05142996801400707a019034000340804008640c000040766480341c00300c180003c40010004060b01c03c0e820701580a0b400424000c07011135108802e10080000c690202c1c1100c500c0c540ea904c0c0507003501c80c01c9a0240c0c200707403601d02041c0030341d040700c016248051090400e40d1207002d903041044100d0f001241e0039000603840c3c0901806064110045040143c019140010100d040103110b01d2408904d204060540a0001d0203188 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 723305188 1250 723303938 723303953
    0xe030c1504030915120c02061006050a140a090518010803090603090f10020c150112120c080f040905010b07020d1707080d0209190e01050d020d12020d020c0301060819 73
    0x60031131990409070290800c90000c21400654002420a500d0300042d03240781070000480600c200e0250b112a00aa82408011038158000182141c244081d042034205803145d48000750489140310342e80e5441c01e80c58003041015180e0740ca0100842114810010701400c10302000301e450811080c0c60450fa20385403817410030b2a0694006142009004980c10348407c0440c41c1c0040011404000c121510700b41c00580109006000780f0628201c0d100d0102800e0016000e0b0360060700c80c021500b0403d001050645642d00345a2201381c0d100c09060300003505008a0f281c5110762800b5008000180f030030582c807035010a00c5d07201c0d03241000e0181600c819201d03d0080d001c200701e411480e4003403000c43d2201c0c41151114003a400401d280e0740316103181480d2200501c102c0440000f160480c062001c02d070303442c1c402400505940755205903004201c40106101160300d130346401c2ea040d10980e00600a40302807030002410000b071f0740d84003031082e418001c00701700f41c40000909855241313400d440101c01d841346252801 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 723306438 1250 723305188 723305207
    0x204050c0d020c011d0705090f070315030804030203010c030221060a1208030402040501050607021012060906150f05090609040f0b04090b09120708031602010617100e030c150403 78
    0x107101d000260141c1104419086020034020070552200f00380700001c616500d40c3c0307041c010a0f1301f0040c1c1c10f00160652000038065030300481c260030001404411001d505c0234101140e04140d0300300b48000340820440c02d00348606803910307070b01e844e085041c00302c004200074810640105107a0712289240208125030707103600056004100300d86107001d0b0b00c4460703d8000121f0f0003ca8040c0d00c02c2d890b10000041e40d0801c08216104107600a01c0382040c044907200c1a01d21030b280010700c9440f15507401e008201440244183c802810040c0744011810014010050407400c0c049041000c2140600950180740c6411058800c0c3c11707001c40c3c02007a82d00010070350200a10081c10320755401402e121700d500038803264049140c0500310041c1662440341480484140c14410100010b11100040000902d0650400604050303564940f002064a60351003034200c02c2d40308820005e842940016485201c00c04180c4a00501c48901c80301441c1413100d01c0980fa61505404a62150740d2129200002c040612a00520 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 723307688 1250 723306438 723306457
    0x703080109201813061d04050a140a0b0712150f0b0a170f01031e080922050f0a0b0f03070506090a0305060411010f0e030a12090b1902011b0503040204050c 68
    0x58034131005040070040504005d05c40d00d007142414001e510961106030b01e219100f507070408020b042121656403500301d40340d41d500d80078045000d207154000c0050140b80e003880c0914030304c1da6015071150400200d030040726031912524110b00d08013142007041c0219a00a542212038810b11183ca40c0c100807410b80310f00c60059018001120b40d00300b00301901c400b284a081c1030300d001d1080b03040c80c1d03590030150b803400010028000d04580003d0203070003000d2401c1241d0340300380074400640411880e00d04e0240c1c000d44009445031050320040b0010424803001c0c3c0d01c0340780d00c641011103e503405000c0c2d500100351180c1170f80c001c0a001d40c06c0024403a50548a070580318006540c054115091403505040c0711a400e2152039040c1d00180401103003090040c4610048460440010007800c50071442d961214501d401c000145414001c40040001d01d003403600e07014100c0e10440c0083c00414801c090802030841c4c940d8011540da0b1000700c1e401c0c3c040b407a805030659030300590658000503985c682070382084c518025540ca1 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 723308938 1250 723307688 723307699
    0x50706180f0b07090b042301020d05030f100e04060605011d130b061303080913091a0403022404020a0602060123011e020a020906040b060d24080307030801092018 71
    0xd00b0609224030920380c00740c2d04100c7c80c03e040e03281e80126219800c40002c0c0c0700180e021700203d041e1800c00c40781e403034000c008040b28400081c4c0d0380b101585080d00c1181d050b01c00c0c40d0740d004100419600803a125803c0c403100780c030100da4008040c000034070446a40310980c40642d03840340c080c11603481d903000f210380e40792300000707540006035aa00d40f0320380d19400700114034091a0b2100a407450350280e402a900540e034400580c1c9400d00c020b21802a4998000380150118800c1c0014000c072600040d124100d008820004030304030346028014840d0203401640310900315488807004101c01c800c46da6040c02c81200c1603810b0340700e074459000120b80c2d20f907011142203170f0008120003400b4519000900d00705410b10035624035134940e030380306c0400c012280244070103900302d0340c100440c0c490590284c1c443c1c02e50b0103108840ba10800415001400705120381d4202201d558030015842050607005040b00d40180504002440910801d210790181d041c005240d10808000104031300070f504510700707840c0e0b04444001e8103 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 723310188 1250 723308938 723308947
    0x160b0603150f040c0603020405180402150408070602010b090402030d1409060414120c03031c06030f0b01030213020a140f0705012405060903030414130507050706180f0b07090b 77
    0x158109829400c3da02204c2401141c0301c0012018060300980d000c03208010031a0081e00c0006102c1000f00c58002c1c4100d91204040d0000e02004141d0006040505011002400440d0420700081c1c01c4600b504401c41c460402c8104000044c4e80c001000e50030380640d40351640064110340d2030303d09580505900c0c01e5014001040200b04801038442000d24038a045541c00f000848401711035031141041022180c02d90400c00c103c0345142560341d4030300804200d0110000c2d90559949511404c000806c00441d01105190010810b504d0702ca142c0b801440b151410440c0342ca008070310064000003240b2170100c1015008107030400c014051300241e42e64540c00c10024840c1d50034036038100401d095030128200c0070304800b10010030749040510944bc4c5d562030150003940f07854186400000707a4100790786800d80c092070b4001401c1c4150352a004041c09442e99441d80358030303140240751030301c02d450302100780c13024030075411a08401186680d841d4046150708640001c100d030b100d00704110780d81c1350181c100d06003403030700000c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 723311438 1250 723310188 723310201
    0x6040b0a17060d03020709022a0d031401080d031107060c02010b01020f0102040f1e230906090c030402133c0501180c0e0d110a0902160b060315 63
    0x4901c0d500046410118030419681c000030040e440100800240042c1c0c4000e90502c42c7c4900e0381d000748041816224045140c1203801c17824510406070911400c45608580307903806040c0c0c0c160080c81c0d8110140b04070b1103c03543c1000e14455480042e900300c0030401d52908200d01039040884d0484420f2500007409011002c03080d90040c3c0a007000c000880d00501c00d079034160008ed4010300c00c2e50152401a0b140ca09010720300725515061000d0f6115403410745130710b5680000d42c3e0041102c3c0d0114900071200450100c001d0808120480c0300040100e40110180001c100e8108254400c49a00c59030440314290081c000317007510001402d101403040c203410300c121144610100280003a8070140d1601d034090301c80340d16880d07440003a2082031185d00706840030f44040b521070740c00680002205031341600d003100b000c0e0313080310029501c008106026202442c040100e000317141000d02680c0301030120002d043d0328001400c0302d0802c540140700343c0600a80f0700b035004240740d680c0a000d100484d0142c81d00c525007078140170 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 723312688 1250 723311438 723311447
    0x70303050c0f030c09030d08090706032003070f08070912030804141603021309050a02090c120c03070f0c12030f0204091a0108130f02120c04060306021809131106040b0a 74
    0x20310110340300f1f00c105d41201a00034030883d4a0b038850040e090251001b41d00e0207105502070131035100740120b5144611022420403030b00001541c07048080b55501d002844107924068401c4101a140d8410803201000c14080e0b40507412002140942c5403a10b81142d9580d03083c11100349003011506080780c042c80c14014009000141800e043e02d000b00ca901c2c0107410105c0d403c90480d84102001801d5401860009026140c000643c45e88415508d1450785080710358200101c1066080301c11500049002c0300b80800103900040c0b40c0040c445034109080754000d9511014542c40d03070642c0f0320003003580320b0042c0341280b065034040c0c034001c101d0f0100074011601c2202c00e50551402e242030303c60001c0c02003000035450303c41c1d1000c0283e440d500500f05019074895a001d1201c5a18800e2000c921480384a2003450030361502c4c421000118000c50006886890720000703201000841c81c07140c1e1103a10070000303201c9116800042a1810380d0f000541000545005000c00e919000f80c0d8060ba00c015400700d002034486410 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 723313938 1250 723312688 723312697
    0xb09220b01090f080d11100f0911101d0d0206070f1e0309051c1a06031011031603140a021321061a060c0102041e0308070303050c0f030c 60
    0x980b5215030a5464210100c0c03106410f108444c0c09601900003554410302501501540391044400e66260010012058003569540030740e00b03810039039031103410050040035540c0c0c24240a01311405074407000000401040442d010506450400a100c83c030000359807420410702203994041c00480d01c0341054180741c1c0b051588070205a41042c1d08204032a4120722010048024a03850303240d1400b514146010301c030f100701144012021210400304800080303104070f1111b040d0603c0036000e084062520005143c03c002858001c03010407030038035200f211180404403e0703d0f07110400385070030001e100c06400c2c103d018102d0003203407a134845000d00900042c00201d40040040300c92030049801c0007981c4821401460a500c1800420002030303a407210002601a001309810101c0000342c4d4050380b55050000b00554000100480d03d6940020304116007424600420290b2005844051803a451902d5883c20b504c40c0e140010304140e503400004070244032480944100001082c14141c40f80f0b04642c141c14694003 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 723315188 1250 723313938 723313961
    0x109030917070501080114010c0606180f0501081e100e060403021618050a060b0406021005091603330b1315090b0406080a060219050c070b0922 63
    0x40708000744180c5000911a000c480040c0d4aa40340c50386001007540009003614101030401c00340184007404180035000b04400b0745100060803858181c003100203421154100c054410603410030380108825100030034404240c1c4075606170142c00780407000c0098140041d0b0b06048101c903203003524400746c809001803100d2049120b5004c0301e905c01600040c81e04982a00d118070a000d010f18521803069000a82100e50804030800000c108984c40d042c5000c443d8001d90400801a4070041c1d4050b90480240034a23908246130f0409404000c071200301d121003001480c00f0207094040c90722440b481c8003010030a12074200c003001c001240c1c2c0c04440d9040030080c0140300c0c401c40c40382505260584a2003003c0c444d2140c0c104190500e14180d614240039003001d0301e401d40e0709a512550f03039800081d5820f024880078841d03c1c40f0364401a65260602d0380c4c20a41c0f80303c5c2005e10300b00101440742044802d030001c2e0002c192942524126110f0140400142030a04100101038520075070940314400203403142c01080951a = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 723316438 1250 723315188 723315209
    0x3030c01050712150909080702033009030303010b070309030c080d0f021515030304050603130b07110307020910051903111c0b07022a010305150f040c1101090309 71
    0x12504400035040c1c401c50034100041c1113503c801000894156804040c81a04c82c16640d41098800d03000241050030003104c005907030010140d84441d802550201101c080340c0442843d00b40504140444d90380d000501505140c00703000142d440c20700d401a040b03003000b158050010a000c41e1541c04050316440076492000119503255003d48035240040780004071302140741101c400a90720903007400c0c5542100c6c901c240d014042004041a81c0d00c0c0c85e402917209480c40e00340711101000c5450700358400b02e8000c14034400c20840d00e030b148541c5000441151800394045a2072007507070300d950002e500008034981c04030b58045000d007031403400032840c1a422001c681c00740b10038400300702c4010144000040402d55104000d811074584d000042e245600f426045602441254440b61182440300c041c01d0312603850a024a41981b0007590035a4140165035000c009040c0d65140c041c07607500451300c1e40f082c400007141b04948843d6084900745c8191199036150b81454020b101916050030050a0f03180e0307a01078040404d = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 723317688 1250 723316438 723316457
    0x40f0b10021b061801141306180801021201180b061206010201050a1a040f1407110d02010c08340c020f033705011a040b09010b18030c03030c010507 65
    0xf4500a030656101303041d000401680d21401e4801140d03035814403400345207514002c2c000340e020000494901c0c0302a091a8940c1c03112031800d034000c00440c00041e48007290301c0c0c1c010082c03c401d0300301014035a81112100c115202d0110182d00e40380028018585ca0183c10480c042980741c1182e021582042c005c5800317030004c000d507840ea03400d032000b03842d064013076401600b04041d44031510707051580c031200720902d4044000440d1001101c3c4010007060a03a8010001542c444840040e0314080c040d08008611900003000b441103400400380c884030000300162441040c002804001d50004081d80d06940b1201c020765544170074243c00a85400070b1030500360700038150038500c500342c1e040000e101607004000d240c00c0c1185140710b03041c1c044c4071034401c0070105c00307940c25060a0700024402d0040f032028403505a000e0780039459150034481242c1285140d5882260f82d48010860a044803007140e03490342075008480607001032070340864a054400000346070144800038500b80c0000041d07120f580985640d9407800d815 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 723318938 1250 723317688 723317743
    0x1e030402040b120c0f030c090705040509013008160b09210d021b07090f0e0c0d1b051302090a06020d0503011e08010c0201060501090503160302040f0b1002 68
    0x294210f503490303041c90380b000f10b189901d0718040e041c4014a203001422a0707420004c0d02c022403a2100b060f1790000100e100454103020a07d414101c080c05404984040c07040c112100f00364805003012080300200207200010400d09000f50744d002c44155039207991420400540c42d280404010b07408884e15515800390071481001c2201c1c00d00810780041c2c0c10341083d0b080050750315103100294804a20340c0f81b00248490414049c080c140400030052a1450f40050000007200307440c0c00f60b4039040036240030340d040030350319a05954400e03500070301294105401102c04d004a4041010356900c135000543d010002c3c56014402d5000780d00101011201541d408421603913a000983e5266004681e03400800c2d0f0a1005002c14418489140090b01c0700b1650040c0095941d001a42101c042c00d9403200140d441c0d07202481103507082150000105010fa004101106072002084110702050000a2066071115151025420507400c010401c03d8020311080c01c0240c2c08134045d55405103a80003411809258410244 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 723320188 1250 723318938 723318949
    0xa06050103110715060f09091a060303030f1012150b0328080d020a021b01110a06180804170c010302030f0105040b120105070c140a030203090105030a021e030402040b 73
    0x860a14099401c0c00d2601980e101381000a0507500b1091036990b69a001621140d204030510007802c1341c007000a101c034183d00b000d561100e609190200d00341643c405009a9442c00821aa8807003214020200c85d9141e04840c004017003c02e40c4107440160310f0450760000e00c9101c40d1024599620200100a085482c90500d07031600100e0100d401c141d1400040000d41390a00c0a040c820705108154907440c0113001004141241c0190140340c0059000c07941000001c050130b8840e054200c001d082c602002d80000c851642d4501c4110001807049850f843d074401390f12241c000100407554004980e588464494800441c1c02d0b0720441d42410920400200f80110350181c13088902610381d130314040038546c0c00e1805002c0074190101c0c100d41c2003282d10600803030240c000e05c40e580c041da1050740c5d01d008490300c508061101600c9005106402e80080408000094002048a10004080c02c08030b45955900d07003104000c2c0102d00c2d4100803240d140c3c50342e040380707143c000c02540318900c2250104140154030707040c0030303 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 723321438 1250 723320188 723320201
    0x70f09080c010c0210020109061401050301050612100c02070f03060e070902030618090a0b011401090605090901051c0506010807061e0921080c0607110d0e0907051b060a06050103 78
    0x2e011522000302040076007000324000040d0051800042410021603803004c0031500c42911100150403404010301c000c2c9003e000e5117400090455500e5060140007071080e8441d0f80101b0140565541c440180e0045402800184014451055815031480c2d80b0308002000d864007003aa290180038400340070540c0c0c0d03001c0c402d4a000344405003540100c411500d00e000208480508074001c14410090700c0c40025401c2a40d941c0030f06002203c0140c02c102010014111283d81d4210f1401e00a0a01180c80240c07610040681100d800301d034003c8440021041d5000e0401c040c130340290540c003e041c004580c0b80c100040d0102100e45543d03c41c0480300610410602084a00800400084000c1e0b0b04001d503929520240b44200d8454038000050001691203501e1580901c00204254010008000c2d0f05500002402003034800603002d0f100003004000c0c02010400b10800c1755200d041c0710004102618420f4042d241d4a10440302841440180c1c85040c2c1d9440204480ca010b541e0b042c9000840c140d4860700848 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 723322688 1250 723321438 723321463
    0x1506050d261b3702100519020d02070b03041a0a0204050414100506160308040819030e0c190504110f1201180c0909180506070f0908 58
    0x2010103004001481d04203180700803515a2800c24002540e4030441c04841c440c8490300032008005401e40c041180d1072514242460742e0301da10103002080a41c4603d01c11201655604982d411030800c24003005036050701401c1c02d81c1005464400819002a80000c1c003d03450480540850381003075a42c1d582036800d4803048070018503100c40c015a1484000e102c08041d500701d00140c001500342a211004582124000d0048a04101005c1c01344107802d40342e1000c1c04094081980d903940703001030440b422918042d4001c8003c080000210014040c000700400740ea540c5a0407045250090b0490000100a4102040000c49500850980100d14509038280f101c5002303c2a62802249190004001c004e01c4855140d0034400c100700940b002552104004020703581e2400c05180036941040e000314101509508214103003450060708030340c4107420000c901f04454214a01246060081114210b40b1a003900000e200344200018403c94680200301c000303907114180d5807603480700d90b20111230340d9942600d07100 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 723323938 1250 723322688 723322703
    0x91701050c0f03100302090c120906090a02010f1710090507020616031e0509010507260c090103020c0703200a0f0b0306032506030b041b0e04060506071506050d 70
    0x2c04034102001806941d20200d5064806425070380d135008500c820400311191040a40f0001c0c0707180540b00c600c40c040360021040320051105180079580340b5624045908082d050001c0307400c50600c12403007440c9010502502c4e64a580003801e00e1419035090101600400700c40c4c9080100268030984006143c40c46441103446c0b000100020410907401082d40c0c00a043c1c50041e0380c6c0030050861107500400703004104020000441d8a0301031001403d41c00e0030084000c0d0030b504102d41300a40b030324004480c0d420442469400d0f60316420f24005030000c0c4a0019014824011842d0020900108441001c49901760a21000303200740003208214002a240c081c41c01c8160340c1940a206418a80015580c00300001d411a120251800c00400c4480d0300d55100c8011045071240602940358940542401c082d0192400d1011040f407021011151036a01000020010480c40742c00ea42e5440c0d0f00244010440a0405a910a03040c14030b0000070901e12000000503041c440001190f04000d00280c00c641d0704180c1 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 723325188 1250 723323938 723323947
    0x504021c02030a0e010e030c070602061608060409021804050601061106010e13020d05011e06030b0610180e060405150303070f06060f1503240504020c0102040f06091701050c 76
    0x2080c8000d40000e401c185109030344281d01c0c0703e613803001d00c0740c5101c0582440c01075854a41c8082d02034500b01e0380c1d400050031500400d080c411549418000c03084a54214200905540e4658010400601401e039001c0d500c03000030350040f101116025600d0380518040e8056464680e210b00003a40e410740c2c24000c541041e17024500401c48211071050841c2c01038003564034500d042046400207001d00c0010181a90b060b591421a02070103da00c1c1800303410821b100d030023480624a0f646411681c804000d2805015452840300c8030f0754507201d02e11034003000e1300035000c1000741c51300c070300350140b804004560b200d0003989400c02040c050240250f410100d030314020700552818040b607075080c00c46c142080040754581d445800c045041000803d80c4800f0b400e0381d08620540c480203500040aa8580c080c03034040f016100a0460105011041766100b070760400d581c0940d03500308620081e4028401c950000004401d80400454816885401d02c0103c0390041d608180490080c510b0508039207040d00c011100420422 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 723326438 1250 723325188 723325237
    0xc03030605100203180f0d1b06020a020a05011805060a1205090f2a030303150f0f09060607051f06084809042f0a0e0c0d0e010f0501050402 61
    0x304170841c0100c0142044007034800b09408070718081c0d078480c0216120381d610a0b42c0000a88120b2584004000c00c3c40104900c80c9139030041000e042d0701d0301030039040105844018810141402500c802032101424030b44da00c100062000f40b6550406081600c664241400b040501c0d000080000100b6450005040340703c800c0b001484440400807102046182e0032086080d8540d41400034601c20b01c80d134108005082915003c120400c0000899a803041702e4901c5110507903110158a907a1014003500c0c03080c0c1d00c150a040007032515088070b05060702214a00f04012075000130360416801c1f28912811140c540f00c01c9041c82a1403003404808070b40c1d5100c02a0101d03110012042a605881d400b59001e104500d00d01d408600002c004880c2030310241482103401c80d0110841c0b41400d03034503a62048d0311b900d0440070b10004a0640d914403032a51000980404603a200100800303d03610301002d00e10802024500204060203000c01d5900240ca107850880005240e0a181c0201c9141000e014003803070f40c1944c000c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 723327688 1250 723326438 723326467
    0xc07060f110102160b0c180f030a0605250c03050a0507020d02090a06030308011e03060f060e1018020315191a09090a0e030d2a0c03030605100203 64
    0x682801004841034144070401020710050034a02d1070b6010006103003c06081a400035540613104c0681807604118080246403002c1c0e207440c00c030404650400c45c120424000a151902500019012907d084140030310030b01c0040c1d50b0b0031160000e0b4aa1b0324400c14591060398010710700741014010407020090700300c2c054822402404114801000503065603656008140e4500007240c0b49da0200d50785013002d206250308002d19030b004005030b46110702c5140001c5d4607a0092840c612004207019190308003400c0c4c08038036030010f50203070030b4021211816242c09052010000c0d00b9210b80b84071100440c000d81c20380090381c002c84c1d01c5030030b00c2c072240011a556481441a600e00c1080940108420b2a00100f20403200c0e0341c811016905294075076449040240803c00c00480160141096520f0000001d01c42e040100588038003907504d80e80010700c00e0050a20f0000c1030fa01c000e103909080c2032a040e41c48240d400103507414295000e80c0d801c104050b120028007a00000c400b64500c09a070040c0324035108227900 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 723328938 1250 723327688 723327707
    0x30d0c020a2c070302030f01090e030403081605010e03120609010e0112030309080d09110406050a03030c050309060a110609070f050d031e031d06010b0313061b0f0f050c0706 76
    0x403142c000480b110000252421058142c1d003003000030b5000020b202c10302c1040400d41340500031890003089500130503d081d0340d69104611004221480c003265540d440d903072807810007494a81110007030210b60301e9802c0c0c154903a80580e0040c40c10148003804501c1e02d08081007628140c0d80c501c58408039503402e0010800c6000e8125004804054070b411000d40000d8244001e82401d18844c5c4011509080903e030114803034800819040c09540b50104c10441960345003098400c4070340504000340d454406041540c10f42c8a00d0272260303004840003c120116a80c82102c0000c07007500a0300303035425905e8103030906456619510400c15940015103061107546480c000250700e1a04c00e05000c80e1209091803107405400b41108080086540c904150710001802c0310550a41c22901e400b4001740e40c100208140c0f280409047c07583d070140708511801c2005680c3d4000252000c02c15852042c2a0156400911030100c080c1e0550020b074034181425200f03801141504c0008a8030006000030504180017105c08111 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 723330188 1250 723328938 723328979
    0xc1317031306080603191a060a0b07030c0b06030a11040e2805010c0206190b010309081308011a090a0c230d0b0105190e0a091802030d0c020a 62
    0x8004485488070781810307610050507191a2460285001c400b014100b9001c404e0902500302500c1c100f400182082e071280e600441020b4641c101d42e203504020444060315504560302d11200004e40c0c07400d02d07800030003a0414038030408521415542c0c1c1c80a05803030b070543d044000e00c0c0c0145904800001c3c50650070600040000c0c5080391401c06c42d04c001175210741d000c04086054443d40c01d403101c043c40700a00612035640d406000416040c1000e44800382202d508800d00c3c0c180556403801e000031684030f50080728855030406071994940e2a808040c91606811b40700c2e00d03041d0740c6000d4600081c94807075a0010406000105411030340d654001408003e04020584203081113003c00c600c403540060070090b00600c503055174201f82c41fa4107020600b01140ca19458403030511000b449040b8070a4100780112006920501d041198031910074045010319505030441b060940c102880502c1c5040200b241e00d100034009c074112052456400c006484100030840040d4101e0030559051005c00300902c0d51902c001c4 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 723331438 1250 723330188 723330193
    0x611030d0b0418381b0f0f0a0f09050609010e06090301050f07090e0c0d2c031206090103030c0b18060f010501030509120316020106090e01020c060c1317 67
    0xc0c3c0e001c144882480400c0100c0d070f0804d0030b0581011510300d440303c01c210131150028128112248902ea203028201c0105249400081090440741c50701002042d118400a00254a40c072451900e02c2103910380c00009040000801110f0203c8800e44598030a0084440240186140060b00001110307000c22440c41306811000820100802d0340b4244035140c42180c3c50080c100c01800c18100007000c0c00103592101421074800340a1198401d0458219000321189070000a0301d8800359124030107140b51213480300c412403207101440c0e441c80004401881c81d01102501d1040030b5032000304004940c4403e0002800003004005100c0001307010110141c2c122060407070701440e00e4400c0f0450352401901700c0d0520b0940c80403500400a07546c040c002c03990410102d80c041c00c031348680b81050040398040201441280b61f8034420001c5074600070342c44030001d088962001c0c8000010a102107000c1d43c424003e00f4102d102d800d0006612212250540d0540e4030420302c002082480e00c440c034401d05585031840da29a0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 723332688 1250 723331438 723331451
    0x1030b060c070609051314060409060902100207170f030306061605061014010e0306061009081204080d3612060b03010e010c0e1c0803041103070611030d0b04 69
    0x711003080032034001c00207031340d81e58209400c10060114052240050140720350034a03c440a01e40800c5010503070141041d0f40000d940e010341e0614801134074660301c0c0a5005141c0d0901e841c000d550100e0743c502030380c1c8428924a600b94100021170354074411450300d14025001407011a05071310b0b085000b0b1a00442c03020076083c1445042c3c45a50034013400b40d034101c40d04102d0300d01c10083d5414032492100100d8090a01c6051550710201298540c0c0c0010030151050380700d0303850390700e409000d840350001030000072007100c0307031000c54034845050341e0700030f0044c000e261007102c002c035400074818109900120614950007594072515050202076004103610358848030324110011071200b05260344140e00d10f01030080812145151000d05003191030302e80b10000180d040c240e00302d49458000c181614160000d0303c0c80301c1c03490300c001c40541c00c49c0c0d810940108a50400000d000a12506005807000c0030380c120162080c0b83d40d03035103040d107c894011006c0c2d8401d400078001d1440c03040c601e9210600c888006003010902 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 723333938 1250 723332688 723332707
    0xe0a05092a160201090906080303070c021207080f0c0d08070807110603130201090f050a050603100504050408030405010e030a090b0c0a060f2004050a0302090a0b030102040f03050f01050c040501030b06 88
    0x207400c40b02d000e01c2035804420010b815580d0118040004020b01c160820069003444078007602ca01c03009285100340114400b8050454441c601d034210200c40343c4d0152000b80f80c585c250203072138407510581c1c04042c0c03060754104141403500c00352013100c01782e01c4880140307010301d00d0b43c0b000700d240c00c441401d0b50b8402140101c1a0300c1d4507500011403050300001c400d030b40c0111316440007600c40600d5401c0040e4003602004180003d80301c0c1442401510421140251a075031030a88920904c0a50340009401130f003001c2c240410440e1020285000350310980080c48044640c40041d9941d000e10041540042c40000d0301f04a0002d10800030300070414400d080c0d4000c403403285c5448007510070500d055201e955441120400c009505014405600000195130780703014504400070388a03401d140000303480b0b4103e40c40400c40c1429070f42d211601108000d1b00030b41d129962814112500001484140d0b214080e0801c00c1d55a10018407416100d145061905401c140c10100110001c14140c074a9507000720b0100701088a = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 723335188 1250 723333938 723334021
    0x10c1206050a2102150a0f080c0f0d020708070f05070e06151b1501151e112103100501030c120e0f010f1d0d09031101090308120105010e0a0509 63
    0x11155404540380d582c4402c6c0d0301c0018444140e0002440412038000203114960150008440720000d94046031a261a00c242c83c10001f40b040d03030001023004800003440000c002d410012140d600b4010029a88042d559092400c81550f08071042c6500103201807215100c8403000d400340c10b601c00c558001d20742090241035103520386080c2d804481004041b6200400c5042180e2002d507562152502d01b42189060030b61100000c000a030b5010303000d00c003050319000f91640d8100150f81c1e642010510241502d8004805144250300668030703036549014410010440754024021100c0c603c0d800e50719002288000710001009210341e0040c0841030040380c1c0007440c407003424010340c2c55403140e000e8000303080350508a040d4400030b103000146803150402180703140100c0e001090841100e03003080981c2024034110004841e030403c0c82d00700910304400403130041c0e1a520700201040c107030ba00c00e0b00e030310705840f500350708001000301d09104107544032141c040010200d002000b0603845903c0014242488031462081900 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 723336438 1250 723335188 723335209
    0x90504061d0a020f03070f150509030a21030b090a09020301240819051c0201061203050c0601051504440d0305010308090906010c0204060602010c1206050a2102 70
    0x1680c2d4004500101035160201d44031308400b00803002004c89510b0408001c40da95500e12400704625260b0400c0b455030b500801c22a148454002d00390b680f40503ca2910314840024014140708450100d00400c007094001d106142c05228014030204499881a003910060301c03414071300300d0b059501c03a000c4c0170101e210340e481d10f0005441150314200460524420f035142c8543c4d548035014011864110701c01003000030850302c13115440c001c00030110884040c42640900800d03444000b805c0030b01e00c441000e050f07000020f0444114100d064030704c666a00c108002c0b255040385121030014130104003c12030200f80c2084600c2040c0c00c80d00c4003140c001010040c000740300c5190310307460740d04100e46030f014200b00d014058012200c03002c0c2000c21042d41161141c600c0d9004141c0710901a40540000c91420781c0aa0894800607600a0007030003030075100c1d40d00034041c041801881e0701040c00141c0c03c00c041112402103006850010b000c1c1301c20545045400e84001e4080589100bc049141000c50056101d0000c0e02 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 723337688 1250 723336438 723336491
    0x30a090905150f121212151c030309020d0c1e0528030f0506010e160215071b0615090b100c1506030c0312020a0b04030e03150a231009050406 62
    0x107034407501b0009a0440c66180101401180ca81d004400b00069455024803912400d1001d509110030001d860309800408000c88041e504c80c50340c140c10002c110504c40d480081d13403904854418a8080c0004260034500c1a010f0250b0008280c444490329441008051300350a0040303405c548225074075110940c080c20361007010344141c0c20440040c44600500c4654942112200140c03400100800d94001d49074510540d98010b100c0c030180106002c50710a1003909003002e544100b6142591035850080c008180c620100b030b96403c41d40b500040e034900d15109a40300c41001a0054ac8100140d043c02c441d0300000030300882e8100c07070007041648011250312440d0302551041181b01d24241c29401d0031803020f80860741d1a000c6500000d51000000c21101c80223800c998035080071801640c00c1c0780083e0429002e01c801c3d10311070307803400700304281842c143c0c008213250103580c029031140300100484492149802c6801014442d50b46004012070682641321507400343c0603000001d034880c095140001a80b060072f081 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 723338938 1250 723337688 723337723
    0x91b0519030201300b01030e19020f040f0c03050603011a01021005060607050a08030604140c2b0e1b04020304030f0e060708041503050a0e0a08090612010602030a090905150f12 77
    0x5e0180744d609441002c2d070104204004100a61109000d0324404014034030080c003904551408562a03103554008854811070b0403800d019403e440440200145400c13503030f5510960a04100c5043d45018202c400203000c03043e03001d07040791845a140c01015143c00303800150400ca08006401c00310304140300030560070388189003184d5a030514800b084144c403a0300080d403006805e914248024046500d040352040c0f0180c0b20030b81d04040c2d074510482e52040803504c040189030f0030020001041c08001c0b03070525002400354500488502c14000b80402c07408100d5004011130501d0000c080000d02030807040380a0b080042429180101943d42c08001c1e82041d070000c20a000408004443d00e5050b018a40d03101060000400101c0800f400c5140c0d5904400720180101d1000030300c40d8071945900040381e01181611759220020f5946450080d42c07071744114030540004140d0a40444c0344252401894020304840043c48010803881041100440c03100c044164040940c0c014001c000f807043c0600141c94a00c050b8 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 723340188 1250 723338938 723338951
    0x60f03041118070c02060c1c0f080f0c091210020f04030212060903090904050c10050c010e1203010b0d150b091003020403020102070e281a090c0403061104030501091b051903020130 79
    0x30042c203100f0001c0c1c601500030030190300700b255133440e8805980c130080e0119249500c166040d00d2070b50070080c40f0740191703090f5400019084c5202e04040005c00403680f090b60240076134048641041e403503040036600200c4a0b0010012156103291800720a034100303005805030b6132840149400505015650240e840c040f501c04940c00002240a120b42101030030f052010b402c3c041a001003241c0103101c140110741480c480424100d0403546550b000b6103128060700a4084020340302c0366804a0f54001b500c2181c450500000c010070480d00ca0300954044070fa042e0000d1001c98103040c078040da03c0c00001d00d49520440d07801d000350346084007003640d03001c05102c200c4002030040302a000f80000ca48500315a43c06001010b0030b00050402a00c100c40c116508140c0000d0302403040c003c80000c40c4101c1c0c0c0040c14660810340d510f003e0000500d207a01942120300d24064640303540b04240442d01c034100201c2d6940b402c5085d010000365006050601c01c0d142a8030b002c2c1c03141c18196104690f01a808010440c1140c1d81d142e = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 723341438 1250 723340188 723340217
    0xc06250810260f160b030609180c0d05070311010c05030313020609041a01020f012a0513090c080a0506060a112a190b18060f03041118070c02060c1c 65
    0x480c1c0060700b0b005c0a4a07245113003400108014600141041103511213106145281007000d10509449200003020101c0b200c00754148981d07144040d010550381c8900201100b0344a60141c20b20b0b808140c2c0c0720001d0750856a0ba4880290f03031210002081e80c01c05820800c0e4a0307a580d40b032007071502c2d11183c00b2650050540c4000024644184100070305040e83c50700080f18a580c00314400303040840c4880c148507001ca14110401c4859000300c5441d0065010b8102001c02d00c0003850700214030b00441591901d00036615a004003054039416240320390001d0381084070000e200d2146140e20802501c090403202c0d0800e0414102c14030030b030080c2019060080d0780480c3e22076498108454400209078405408c10305042040758102d40c41548003d80300d844c039407207000015407501000e65024281d0140000c0d2286000c1c1080540c500010944a200b1407482c608460b42c4400c1814003409100c140e5118480400581c2c00e001581d33020440c440054400c03c1c240703021080704420980e0442d038039503480441c00c81458 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 723342688 1250 723341438 723341473
    0x1407051c0b090c0904060e25091d010606020633190302210f0303040302120a030e10020c15010602030a03021309111b1c0c0303020c06250810260f 64
    0xc2403075a08c110980c841c0059124000301d604415909015030000ea00e41c42101000036440640c4c062540070350a24000081054000c0f0380d480c45520290090b03040683c4515261b440c003098041511021032180008074039a003003c2c0000190410100501d4072955240d40004403902040200c44414202d15805c032019a4001d00c400355005e03110310015400d605144e90007039107802003e803030034481103000308016034054840c2d0400c001e00b04000066482c00c90201e48050007030350110b0700e400002d03c250000a5452050340042d51304031903050307000e541070984140044029600c01900e804100d00d040c2c1001c15201c41c1e51050b02046400b500302d8580d40c180c1405041b6208038880308254041d0032021482c0c0e400d1200d100c0c114001d10b214500b15078030540903e4141c0090095140201d400d2083c501003020348640307902c0186202410020ba074903088071003002198051011200d4820340360b000c2d08200030144515100c00c007494103080c4408100f8000940c1c19260403400b100000c8141d00015151500703500c403 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 723343938 1250 723342688 723342703
    0x30f0f0c100e011a1f0513120201260106141b0102030a0605120c19030b1e10270908160c06090501081807121407051c0b090c0904060e 59
    0xf0200e220320110540300099040e415004600801c40705030458600d480c6c41501140d1005000440d140036103034840d02e52000c8030002d508102d0101e5560724980c00c1c00421410410580403401003842e069a0800c1c1e02119200100303120f45d81c020b24107100821621140240c10b00b945010440010380700d24041c0305800aa81c05e6610943c0100480d0341c42c6501d4150228a414070703014190b90800119259542e00c0c0015500c2d0b600250800d0890824069048802c0024810704001e1012001d40c58a94505503d0000c40c24450843c0c0c407144504510601c5c0e00d086100c83c004039280100040c414010748030401c1c0340d4070500d217812032030124001980401101d8201e84001e04003d15151000d603082c0070000e01791b10800303410218980c001b00b118840c0c00d5000c10055001e040e440300a121960764a15000060b112824030b80312190203017003000b14841c10400d1380e4169084c0f15204110440140b501d0f44d00d0346e50700103400c9080c1c50240e04a80b0703849803039a19200d8081d911901c00061540340011449007070641 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 723345188 1250 723343938 723343961
    0x60406140109091e0509060403020c0402160f060e0f0f070f0b07080304240c09053102091906030c03050708010b0a0c0f060207170309030f0f0c100e01 66
    0x420410091190340c1c071081010541d40c800000086194801c010a84e00740000400c101800d41468100302d0581c10124185000d03901c240c08803100d0550070760801c0103030300940342207070589031901c40308101081180881000d004e008001c0065043c01d071030a4681084100340c5000c0d805c4e0310003408295080020070448000b00641c010b5031039500d041140f91070841c40b40d000c0103401c011000c00410103102d0004c040c10704030030321443d4190700742800040344005040ca84000302c001c980085400586c074200003044540602c0045c0c981003058136242c00000070340d2040017941080b140d00340210403460700c4801c564400c0c0711018070400f142a10b400c00090603912001910400c1505080c1400039668001c243c8038150703160283c0450300c031620701070222079015580b0809031501e01d012440d41c050155503402807501c14001d20b01103911101900303650b10f040c407003626040c0407035000300205894400d195001d480076829041d1013070b18010081716064a004e0340080d019000d01e83d00c0074140700d01c038401d205e28a802c21 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 723346438 1250 723345188 723345209
    0x70801050702031206040f060e150a15050f041a030604060618031e020402030c0702040b030a03021c0e030a120f030905070b070c0e16020d0302091e0102030c0f06060406 74
    0x41c000000a4890040740c0c1e404440005100c04030b030039aa41c581103802110100c8400700308203980c0e4410080c80340750554040f4041102d0b018035550303506200c3c030203509494501c00e103104040300c4e03c42c0446541d070001c2a1164904410302001ca100e1119651014160251980594036820600108400c8a82941c03192090000c00280c0000a1145804a00449400104009035244c82c80d005000340700218000945c020b1000040041d141c2d52180174001e054001d03501084208002400e06513912444a00640507a01c00c0c5240b0307160340120a4240070208261030f2028600c003070b03000400d141290940382222404551924109000ea0040c2c0c01528024186010301c081080c0e030701c40b2a00c0d85180d006d021918580083d50b001440303400d1105400038064440906043c1c6082c032801a4001200100c0c4401400380489500005210303000351000500010710b0401d0f002c02104044401c02da46c03000003410b5001c21305c615071042d901807202e2110089104043c0403a0301e8041c08220481f516600640342e0f0300c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 723347688 1250 723346438 723346441
    0x11180f040627020d0203030c03220b04030f061e051503010510051003020708041a04080f0a0c0b030907090c020714090705041e03020d06020408010b1815120102030411010207080105 79
    0x2c2c12901a007007002c94041c2c80020302603040780003103401c1d8400c0c2401c9a00c18440000d102c01c0c00245003100380b0100601d402107400182d1980007041c00c070701c51484080c0200c140030036241c000c2000d1382c1c4041940d1040428038070190318503030004d2080d288102e8910403404030413052041c1ca0b007000e0007450340c407801e0006d42c1240c445c103107800661031a860310505020194081400802c04c4222411503024212401220340d44882c0c854500340c044c2e0140c016481b49000b00c10504a840c080003500c1170001d0b9220710704481c01c1c1d081c80b11034415034000510740002841782100c0020001442e00c00c5908180d2550b018041e2982407440c5140e45d041e000040c0c0f809048090200b140c40d030b50000640f415110181600c20380345400312070103458107190360006540701d0140342d0703420100a125401001182c041500074082803441504004902e020000b142d06854603080000710303d50210f4128041a4100400450441d07550300c559034220b0b0011a030442d03080d82400301080740c541c0c0411049008203100c0340240241d = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 723348938 1250 723347688 723347741
    0x50106081503210f04030605010f030210021908090402095407140d0203041104050411060a0311040906030204050105060c150c04150210230411180f0406 67
    0x2010f4040c3c0454400d040410b0b1005001c1c06203045a004641111060010b541c551040755030f10070701480124407684154440b80901400820000d41d040091102100b80700b140f07403504000c5078003401080ba401176082003a5070542d50b8100c80c1d04040140303404034260f07040e08242c01c14800c07000a91244424818030840ea4030060004602c0c0280800b002c002c140700d038455035400e48002510151070308900c40e003c40c1201440305a80d0186121305c1c041c400140c1c100e1552014002213030000d580142a010300c1104d900e43c80d007030038001049030920b20301d000650005200c551030702542240c0c1103444004d0316640d0800c151300e0280205809050200c2e2103d00d0b103480b01c040e0305d560751242a00340d2480b00460000a4115003000d043d2402805207c80600740788403034004c004d40f21890050340703803007492030300082c0480918480c17400340030f4242260f084240c0b0384968480416000c090342c20907610241000007804410003c1c05100c0c080c070b410302c24004950810749816000d803501c182842c000804244814240c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 723350188 1250 723348938 723348973
    0x1090c0512010e03030403050309060a050106230912030d050606040e01030620030408310b031f030506040302010f1413030c0b0108300a08070201020d050106081503 72
    0x1125412566141c0c181c441c09075442c050310251084140c60700000c0208000d140c1c2000041d8801d01c0d840e41520840d5658140300001c0300c00070f01404001400c42d103225100340341c03201c95524001d00740192031814046401c00260900c3c0b0b50f41c0302e500c09600042a00f880312105406003907002003003128a1802d00d420300c000b0320351610f014400500102d48171503070400c00802c00c2034003070440c00002a01c25528031385030500b41016448940c07410300304241e0f0401030031880d0364001c03460701e422100c80c0c0240750545800380c00d010f80d07007024252201a05e00c21003a4162004218205002181700c5c0000d01042d2503d801e01a00311081c19007107a041504040004038030480c4044441d60281d0603c11260b6064030505048410001c121401441c040221002041030310780041e99a4541804607100c0c07400c101c0c000000c40b2140214521401c0c0d05006004c180d800a009074003440d071240203880010304000f0303038071000c40907a2400e03030245010038644e01c18003100ba851141480390780d0800f03600401c2e290006141502c07 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 723351438 1250 723350188 723350213
    0x161b050a0f0807152703050a0b0618060303181c2118030305030c1c021b010b0a0306050612030a03050f071d0f180429040c0506030c2a0c030109 63
    0x8140048100c0f541c0c541300704085c0d810180d03402404640000180f0305d480307a000d1400340c443d18030410740f5a18605108070070b401d40302d02c0b40801030095414501078800300c0361103240c00c266055105040c000c040003800c140d10740c6a103606000b03160421a40329001c0008040303a008440d6001040008584810100f25244001d0100daa1500d00306d031356583e40410900e401d001d88203a044214003000620401c00145402400314065500c240c0e4144442d020f0140c4d00b04e0341856503094100ea10380b4002c0020903541da000d503600050150404070713620060b0f8100d03070541d4400701d48600403d94844c02d126010030018042c0d540040d15003803400b6001081e44440f603088091000c0c161140b1207020900155846082c1c2040f0044007003804401c8904080c03914444e401c180010764554564645004a203160040300410f0007581c200e0000ca8000341400140001903000505588a0720802c200002c3e042d070361040300c80144100706521070450b040518206040030b180d0310300c0c07510a03030400900c440401c00641d05e50 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 723352688 1250 723351438 723351467
    0x1305090f06010804080d0e0706080a091a0a02090d050a030801060504030203030318010b100504030b06010503040803190212090d0806030f030d09020d0f0305070b0903161b050a0f080715 81
    0x303001c0380e44600c1c180306548039560450114505003503d600340d00174000340c1207040d078815442e100d44075075580440e4bc007290a2448050700c143c20807150700c5800e40c851080305802001d000ca016241401000c01b0600003011248100d5942e48400c2441e42450740c03040fa035038054296444e101d441c082c95500000d81c0d074080a0316110700d01174081e41010441038254041d0145581c0500590a4151a40400340c8190040d2205585d04003841c00002c08940c4904101c134070480c0d02200351070447d110780c0c10507202205c4c56108500d0481c2d01700164100c0601400083d03102d00703c007070010002000036003070040040f0406001c41d8000d40c0140c0300c07004680d4000c01515051450b404c000640403903107000245c4070f1b0044a1016200d210306114801c18554030000500a182c02200c441c081d41d2a4110000e0740d07031046600c050107590f0141d01010000c0c00b4511a60f00d03101070000618105911600024a040300d194840740d1112480c1e041005140d07810710000005010720055031a10368002c0350060003e80800381e21 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 723353938 1250 723352688 723352697
    0xc1505030121080a051819030b10060c15140a0c020c0405090303070e21060f01060f090b0a0c05010609020307020f070f171c03020d0b040b010e0609120609031305090f0601 75
    0x5101c900400c0841589a908000f0600c585a0b503101106001180088c001a60006d03420400283e903128004501c1c1d08596040d80c610b42c4101090700ca0305103400c02844140841522070544544c0c00d01c91810306402100c3da94000aa082c040d071a0191502d058040114010f500780720811089180120a0326070200d900d0034180c402214540008181f00d8010038a00251285403081800000340050128801c240131602c803800d9980b00c040c15a41e501d81c440b00c000c0000d07000c260034807960015078080c0080b850700e030a000b010361a1503a10642960200e400108295901204015a44e6410032103403982d9400350000d8001282082da00f0101c903003480c003c02000d02000f1038044800b030410424280000030050b0700070440503070342030b004010b9400394061444860900400f07001901d0680302e01a0707036030016100c080e0700760501d0301444800d1704040d4100d40d102c0b0240c6904801c80c10140405031080c031100c0d0103540d03900309080c0700201b15107c1d6080140107000c40c5041040111620340c400390001000d080 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 723355188 1250 723353938 723353947
    0x40b13050f010f170a24170319031505040f09060c110a0b090f0d0216150206070c1e0308010f08160902033304050f130f0c1505030121080a05 62
    0x4560701411181c40300e0100386c0040440c10300e100482515a405540b000f02841c1401140c0c1402d4036507a0082043e840001e40310140b03030001c00d602a0b840b0648043c0c101d0001401c16994400146c121202620070140c3e080c0c684c1c1101c1e0800c41c5d1445000074203a000d00b42070b0810242e8808580d030703d40b20361200401540d149008501421030400c0340060414441003103801c8085403d500a4031807000f400c625512103100b86012816a0071800d50007894540da43c010718599881c4d4000315010300d101001510b40c181440b0018031401d20600c4112603d50085e1903400c0a9403500341c03d051404503e91120b415a0048a40b151150344040c0664003181d0000c6000b51b1607448551155a0b01111807201c90360212004030801c0704414031210102c0110800c035410411960780c05540c269888048848600148904051500180601d03455884a03802402d1096403161622170900c5042d000c9030500d00480e00c040f00400142502c2103119003590300c2845900003124940d600d0072070300d006543e032400c103003c1c0108 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 723356438 1250 723355188 723355201
    0x1b010c1b1502070c060905030c010f030c0e030d0905030601080705030d05070809030601411005040306050106051b01020703020714030f1203100e01121205040b13050f010f17 76
    0x840e01108501c45180466491000f443d0081c0d034010a031081601290068400082c58503010074041c0d0010b5041c1c60303002014440300c5049008041101a1009000d921070900c0c199490420a400502d000354a44152540c00c260800d031529505a12524040e40080b00030700480d1000f003230892031400981852600c418192401003a14000c200d400c94161160b1400001c4400d6122900550030f10195508000705418101207220441803081940d450401420b0110260620380c42c000f00b1000300380b5007142455143c0e6210000d4440a80c09100042c0300440c02c1e10403080140407002031a14000c00851401400350707400b9480f080e643c85094208003201c5510034540e10180726800340d002d04c001c183c41c01c900400542503400d4000340c440441c9840116404501420003c181c80e0582c0c0c2c0d000b41c091000c2403142c0d00e808818904605010401c04280030000c0d6140010024216080c0c4910418006508210502c4002032004240c2810004103071405240c42e90080684e0314102480b14000b0301c50341c3c541 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 723357688 1250 723356438 723356453
    0xc0d020102030901240303030b1f0f031d061504021b0106060906020706232101030b1008030906160209010806090114010b1b120703051e0c0d050d1b051b010c1b 70
    0x80d400035040010203610740078042d070320511100403074603503071030401c4981c0e05208849c0000dc1c0845000308540e0200012403d100070000c2c1003100c0160092003d440c00005100768070003814220f000b08040d039140d0105010081d0042142c0000c1e0510384000d0240c14a4000c008200e0411400c09a0340c0d00c08000b02da200083e11441204c41510000c1142c0c3c03100f500c481c1c10051060707000d01c0103541c1c140340440405e8040c107483c06601c0407513490000540c104901102000081e0740110700c1e80844d602030007c0d450040c1c403140040c6008002182c05001c403032503d9072250f42958080c0554010192040e001800030422807010744a4424914026014003140c4100d0b840c504000041000101c0c68085441790805a000c40188a00c0d8032140309035100c0d0002c0c40110300c0f0380c082d0071500d848a400c80c12003841e41d144180007030400310345880710110317850300001c109a0704940c9480b01240082e00c00582001c0d0707000e11109400090b00c00c10002c21520070075440007001e002a061000d41020101101401030082c1c9 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 723358938 1250 723357688 723357709
    0xc0607200112020c0d02120f04090f0605031f0b1c14012009030f030414060309070b0a08180d020c0628051309090b0a05040201050c0d020102030901240303030b 70
    0x2c2d50b10840d622045000000e80e13890412010740010300c04e20b110a03400b500201d05460018240707010705810603080c010072201609484c42c0b4003800c59030b0b52000103110b0f07a0801c124003240144000320f00313403d01c1002e10407056594160006000390100403800108090080d110000e898100f2941d8001e0305190800c24050103410100c001c14030034280701b07040d06610302402095001c200300c04960070565080d0b00b003522030056209002c00143c42840b148150f080103002140c0c46005001660701c051b40365103254000d6080511043c1c0001c44076400c0000c1031110700500c480c0065080d0040121162000009540e4100c1d01c0b80b1a005488c003207a4201d0191115450001040301c1d808001c400c1c02c00504002d1154114583c03600301e4000f060380004050ba21031044092040e003040c00a0f4565860314003401c0a010050422810024100710b58032a6210030b104600748030307001e40d00240e601d0400303aaa90b800d5840e0300343e5550203400d0a441c142030b14101401104120781d418180891003452200004004200 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 723360188 1250 723358938 723358967
    0xa0608090a1505090c091b1c02030106030506131e0f1d03070203280825150c05090f130e060106081902270312070c080c06072001 57
    0x26450340d000003285458200704d00c00c90340744040710a00c1c007142081101034070382911480c03039489120f000304680d8801e0100800d0054821303a050800604200c8100d0f0490344242c2c8000001380e580c00c00e010f441d180004004000c0c4811031001e2000d8201c0e981d260096030352000440025170782d5285910400016508100c0ac0300f407000c4140b02451540b2442a500c83c0e200801c100d10070300514040440341c0b0700801c5e1014032081e240c45c6000300a0119500c3d06441c1c0c2c080f00c3d40c0c0c0d145480b901005140f0980700343d10081340d184258101081d1000c864030b058242c6414801800c140502400b103150300f901c9902203414a21001c4803054820101c0f045404028040181c4c19212070040c1d9001048446c0c03c8219940100750102d860f00c5a024850b002c4022405580c07500e5440c072542406100000b404480c6045041c20000e0950308451a45101c0658075840359500f201c00d000c0b488420000410180400d07800400280c5a00d860002d080d40c5416040141c18904078045106d0030095101c0e901c6084140104c20 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 723361438 1250 723360188 723360203
    0x70209060d02012606041112040f0f0b091c050901210603060e28020901060f090b0c010e151003020d0501060902070f060b10020d201002041a090a0608090a 68
    0x803104c40c02d0200342c4100c030036070300075414a10340313010200e151402c40f03044a194119003481619259195112144005010b60f1009455070b400d0001c2125601c00314010306074030f0300030324204403007024044030903010035842d009004082c40001340c0d50b6040710b51070100703012042810b6080d8942e8406880148415000900f0451800141042480d8001900c951102001d00030341011980001540540c85036810000d420076600341c01040803a008900340707000c00f00b01e4104103c0040d2106c03050b0499402c20048010960b440b020040280701e02440500058440b40c00d000000d4504241e2034005054903103c000d0240c0130f03001002090040c290303c0b5a015141e00c1c50190754499460800030b201300a0561300356803141c901000001130746011800d04014590701d4003c0e200001b0000f10564188203d0108464107050020a40081800a00039145807020982e0010703151810080703410301c2490550240025580100002c8683c1d5940135255401c41c2d80500d041d00f03c0ea41e5108801c0d017010180180140400d = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 723362688 1250 723361438 723361487
    0x90d030f06031202071d060f010e120105040c0f090209061b0f0a11040c02010212060105090103150b12010f08100c050d1d193212040e010506070209060d0201 69
    0x103031301040c0340049454540709402d0480c02100008804070050b80c1803680302514941080d62940110701e0040e85800081607101000c0c01080e09c182511300071030f0204d03044480000309110204240e80c800025041d116404c600b814103400200d07016210344061a041c070030050340b4581c14410204110b005003104e400980303820003214a021141c41001454892140d400c040012403036900c14805e0b161039100c1c04881c0400b6031191801510181c1c44844118100368542d00b401002e00c0b550300d142e000800206076520b946086401c90f00c403415406800c14a2603c04040342004844000180201e10b505a00d40001e80718181103420ba40c148205486101101d06258045041500320032000200040980658a514201008404c1001c40049000303040700c0f0201c0310f420840040c8000302010070200740d0450f0307481c0348540c6a54903000084c21a1100d600340010144240c505440c1702d94010310b800c0c2c0b00d160500841d50b000890349d4200500305801000c4104410095a205014105030210010140c1905 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 723363938 1250 723362688 723362723
    0x1b0306090612112202070f2105070b0a0225061109060d05090111120103060c0c080a0e04060b04081b0d02030a02120c090f0103120305090d030f0603 65
    0x1401891080c9520280340590005004a40524916605910500b0012040c1280d01000a5008400442e1119402d00c100c0565419010f1000b4810a0300800003d580742c1214941969074410100c40c22580d40c07801c40c038030507985400c0000d031102d0a500c03100c034003019500d1114603002401140907040054038a004038501c030f1003082500840017402140240300d60003071960110040d200300b44047d034001100300720350b1902c2a040d90049400000741c0001181d8a412001e04070011341080c1b90b5400303285440001042000081d106e1140b1440007401d284a4098064130f500340303580101c00c1030000740030421400b5a003030fa035181d0200c000f038054a1030b00c82d00c403901c58980c02e681e00110f4414080810681600e0300c0302c1c0c0b8000c40007c2115034018000c1001940f40e600f80800d03164101c842c0251881210785100c00e03943d07240a5240300e90304081b2a140c07203600d5400c00840c0c0008110050007070619043c2480a880c2d400b240f519580c00c0c00f8100442e002c1d0305484030702d004044c03a600140044840d00e501810 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 723365188 1250 723363938 723363941
    0x40f0b160f0f0204060308120a1505040c020705040f1d0703030e0907440103020a03031b0b01080d1d030a02010f050f121f1206050c0c0a110310060e010302060d1b03 72
    0x151500840c40741056a17a031500608201c9211180ac102d03a406400c4040045107841d8100440012161050301d1034140da40c0003003001d40341c80d090320b200c1c041e4540c510a00b40001928202404103000002864900d01e0f40d10054189003020b025a4015079042e000a08264003921200c031031b94044031286244c000300340c3c12035084c4030301c0043c0e007401c3e0451500c0c400030190303006814581030742e8000f07151080c074a01e59034040d100e4000a11642c15900c00301707010f1001040303c2e81d40c0c40e4020b20728800034014001a80c48010318071603c8071800440750503051380803455600c0004a00080d25030a00b03000400c040450800d8401c0e0003484062007903000c0000300009524070030040213004130006019050b41c0b031501c452661025011f4040c1d40748080c0841c00390300208007140c00c59034000d08480d007968540302d602d800d11420030010b007030b080d24001e02c28654081d450504110186107854503d4003000741600304142602140c50600c0068405c40e40440c260310700070090b034449418050940c80c6081280766494004d070 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 723366438 1250 723365188 723365197
    0x13181d0607020c0d031209170d1b0c1e0c09020d090b0c03130303021e16050705120703020607050c09010e0118050408042603030705040f0b160f0f0204060308 69
    0x1030041c0580500c28165080680300d44030b1865040e00c8500004580581000c000e01d01c8070f006945896410b00840100320458000b8030b641c1c2740035800131030f04c04000c0000f011007007913402441042003100b440400104000045c3c0d61505410301c030804140074803034140b48065650b1074208064051000a00c5130a401d00c5500c54011640704212032480b660f14002d060b406030004486417489100b0b005c103400d001a20983c0105499116210f20358a9400b840c801500300740c2040704501c140000042e54107050110400c0a4401403404a80040502404204076602c4440520009003d50700c00300341d1030100300c0248104510190042c280c0c525030360307440000e009004400c0c4642c5c0c0c01c103443c019001c0c01c80c0301a0301031580b2540d0014100741c41c00d458140e843d1011009440b03481d20004005410001c081c0c4240025401a812965026116402c2a01201065003558800000d03964100310354054203041c1d8100381100ea0700086205580180c90400d01000f00403104025403061130000017108102d8110043c1 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 723367688 1250 723366438 723366451
    0x2041e05060f0304080c070e040303060905090109120e0d020405090d1106070503040b151f030c02070503120708160b040314122a0d2013181d06 63
    0x2004240d92201402060b20910365448290302d000c000150204c2c40c02c00c02040404141e00485426569030010400c92590644003240001d48803002001240124010300e60440c0c3c03520020010502590380312200c0c00f001140c90000e00501103080a000d569078100740d58003940181c4140100e03c1c02141d4103886400182040380898400d1410070070780ca00010300c047c4100c01c140c94051541e200c0d901d80304810300b801421050356140a2403040ea440e20f03420007103100807850141101038909411400340c20f442200d1a45005c6500081c010811035500007900000311030b01c0d0380d11950790906420b114500c2c2c42140c1070141480c240c402c4000c200402a102d0310f1040d8000c0e0349405001e0704001c4000e5a40c403940501058030786124001c80d1800d20080d0411003050340d02c42c46180e9500003291007140e240c0142e86190541a980c60006100c1c400042041400407a1142043d143c288100c8004280105500070f1180b655801e1075240021401c6078041624000c0c507543d024100c0c00c0c402c0b1760710b54902d400c6811 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 723368938 1250 723367688 723367739
    0x10f020102040e0c1b07360c0e0307080a030512060a0510020703230319022416020607090b0705030403170702040f1104030201030b1906180e06010807030c020705040204 74
    0x101c04030100c0c1560a460f040051420801c00300b0721410007401d011f5104103950969082c44a04550180c800c1a031400001d464440d20b1302e550208150420095a00012094220002800c0005d50010480e299651303000405d0303000e81c460308081420000c941d0000c0b40c00c01041c41c03400703c4040e00000c05c042264032584214a034605100795402645038450401504ca600901200d28071014913103c4c848101035610407220b0915440121240c4201207107100b2289030062810301c5006c0100c40360601c00e540306800282058202014020410000d0748540e608144001c90900700b0001c06000310350045400074a01d14504240d4000e03200c1603480604124462450001c0180300c03070000340030b210b02500e02e5110a80c10304e4550340064000e81118040c190b400b0b1780c85c058003e01d840403644907a010340800d5480c0b2155031100e12100352800250740041000c4d9103505c040115580e03025824580c0900b803407601007800c41c3c0c910000e078035105894001d180d12600116000c91090790b80c1c0d107040c1240d1b031036008 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 723370188 1250 723368938 723368977
    0x1204020a080d12271a06101b0f06051806090118140307151d0c0f0609061204031e02030c06070c06090b1501200304050f0d08041212020d0905010f020102040e0c 70
    0x8107c0100041c0040b040403c4151295085102c1d80404920340280920f01903840000c03150795a204480c0e003107501128003c01101070b800300010810003140e11140d0440200b0100100e014500351b60701d80c8640040c02c0102c1c0d0111201a03a41c2403050f10000380d4410340b44194030504825038000307050301c0300054190150401c00c2d802c3c28800040d58813880a030182c00d05401c46508400c1c0138450303010040c1c9642041e01000f8841d03080c1a00c0b0582c1d48914080d540d070324004901060340324030401d6404d140c03a0441d44180400c07903400380c01264013a0050741605188003480840d20f842000750440400240c22402e2200030841066840c40810408520903600d0052461000005a0001101c03e1a0f411103071303c00d00041c4420b042008000e41050401032501121300e0082e5039103900c50f40180c10203950348001604c0281000707181d4034802500c0ca101d0028014000e0b898000408079039640c4101810004481d808825050003035040340c014003a0482c50700070034a0042400c0074594001e4007249802000d201 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 723371438 1250 723370188 723370201
    0x190803100e09061806062407080c070504110304050c01030203041712070f0c03021b0a12030c020415080a0f110d08070507060908030a030f111204020a080d12271a 71
    0x29081c0c1c8106d000400c5c0006a85001001c4003903800b41c0c410728036080e6810400350011a5881025081c4114440001d00c020f0703061a061000751420351078917255503201402031200003107002c1a9600b40e0345080c40c0c016181e56550900030000c11072400c42098101000813080c1d00502d00310041031003034405032100c1d50036001e0b0302000c680440b041c034409001600881c0901a4540c1c04895070207550718014000c1c03c0b59074486059825040e62020210080f50003103c803101142814082c842c00103400020307409130103137811042904c44880340c000a028103801c030b0402d000c01010780520176001070003800805902d485841e001e41c0640c40320304256080d1103010740018204c3e12400301c8d0741c00d5454100c051410241d03500300035801340600110701e1810305d4640c1100810520301c600640343d20180112000e000741014014007044102036001070f0071540140b1021183d45030054030722642c40c498030000080605c03480b95010700018540081c18040c0e24030740280000c2c8051500c0200c800c0307070010074501039070300c961 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 723372688 1250 723371438 723371443
    0x207060509011b02030f06071101050903041404050601110123060402161b0315051609080705010518150705060a06050306180313030507060f02190803100e090618 71
    0x4109042c0051100c02116224242e00d0740600c0b078451000c0e04840e003600c1c0e0720480306d040241c1101e03020005142181d200071401d02c02d00a054116400301d0165140c10f04010051034032408401402c2d00440e1110301151990b445403076003c0701240240c000f040400340101e0100c0c0402074400322244803400d40c8000c07401a15092080303500c00500e0b4100c0030100d1000d07603600305813102c017202110060400b013900080426011a2204202200800300140518105205c2c0b10050741d4040c42000304604410244000e0000041c284c05461090a010342c413002d130003103030104401e1b00560050704440c40340405022140c91001402000c3c0c414000d80f606540e85180205c2120303074620500b40d240d803100d00400d00c401980c9580f104000d216600f85c031301e000742c070058400110b0180d41c0308654507440310204101941c1d10650a204031070841c8042c0c505481c4501040303c1180907400054400000000442d400045440c1c5110041c001110000b00703e00d802d040c0c007510750404946509290201e413041e034100500c003 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 723373938 1250 723372688 723372697
    0x9030a08130b0f07291608011d0c090609030f0307141207030305060a150e030f030f07062d0204090501091418072d0605070201050f070c0b07110102070605 68
    0x41c55a031400d004454460303011004002d44603407200c00c0019031691817517440c2100c43c0d110798a25180303889441c464040080481005a0101c4031a8204815015900218508840e00726038a483c0e0240c0750040000001e0083c8034140e440381c1d0601c2075030801110b28a000c00640009406010800c86811b4031004542c0c54100310b000d040f0100500304400000203000c2d0703000c00e82101c2c000e000e00012a445981c0e400c4080c062005042c0882c2030320090302d59919003003111010054640c0051410102d10401500715401002300040c20b564035144021346464014007554034600c0600d00d440000c01c0c0c4054403200941c41409550340a50901c0e0001c11001114040c1d090a036003003480340f1055640b0115a400500e4181d080c008aa008410307000a08200c054050781d05c0b1134141c2c68820064684001c8a11001c080360301110a001c07083c0311500140c0c1c0c04c02e0513601420311844c50030765222403501d460000e40c200c5402a900c54007000c42d80d00c09206140740c4905411000707800300d40e0416100d09099172140a13 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 723375188 1250 723373938 723373957
    0xe060604090803161809330632070c150f05030907030506090d1b0305030103080a03061a0c0606010810120303020d0c230403020109170309030a08130b 66
    0x810104540348060701c2107440c49900385c64020f5410300c091049480c076103099804180d0558403400104410b4442414040889440c2d40d180080b90a0380c0c0d11505400040d4840c510078094407101144c040c1900820203402c80c9624003282e403415158060641940c2c00204081e641c00d1002c0e900880d100d00e66065190101c800c946800704480761916040343d460340f0090074840706c2c3c000e40c1740000c00030307100f0002203020b4400390024006012070003100828100c0e0b0074003481d0000c8000d80b01000070036000011641500d07045031446030b0314010080305034054281e941c860f5410469491442d4001214000540814040171040d0790751600d4800044403485400d5030f942c44040ca10440801004c2c9080507500b440610030308016041c0820b203280d2804890f0b00d0325070080828005d0002c0d040c00c484106034402e4803a0320485213414a82142c00003040c1031043c1c041c1c8002156000040d01000f42d04100ba100c007840010100e54103030645144c0100d2907003001d80c502d002c1000b010f201080c18404507080d01d03000b80 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 723376438 1250 723375188 723375203
    0x109020708030115030e07140f0d081b071a0306120609060a1d1603021807140a0c1209030b07111504020a1a07110d02010507030305190603060e06060409 67
    0x4d0810300c0103030840012120981c1499a03892a440717011009100c41001444d51918168082441800b40010b07000c3e4114158403519908002c2030025500c90140c620300d41c0c6600911a00c03134004000c56207005070540001391290101c0740d40407143c4041e08001c5104850a940e030511401d666070f04d81e035490b01c051311101d886821070400a4484000c50380701c15651110101c500122300319815805080403185141c0b200c0300c0c0041d0a040c010350411200f4540721000c0c0000183c1585031105004040f50f041440e428800200090224002880b40c1030046520390000e200c48480c8607000c0c03000d410207040f84011107a288440b400034042c98018044c6020241d40007024111488000400c50262000107004030780c081e00446011031200400c254a03038540c141c0e040c049a5030391880c00c0c548020740d04041076078400c003410205070f00141d07808002d0390b03c0d02e40e041c00e001c200d45d00c40c04030b207643c1c0c02c10401100440901e00b01c0d0001c144026608141d012003462400c0d030f015078a8007010b010a0300c3d0001c202801c0e4a = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 723377688 1250 723376438 723376441
    0x3021309030f0c170c0606030c03120d0b180901020a0305010e100b0c1005091e0703080912010f0e0d09120803180124060f030510180209090a0c08010902070803 70
    0x203078062143c16070f0062141c00c5640120301c2e100d286011542005c2e85c034000c5940011b04200090400f0040c091004200b00d000702920890402d82080c1441a41016505a80c544c8660f14041c0c80d28251104074104881403e821840c0600100b4000d40250809800190a00000144a161031003800d801820b1500161010508118600035140d1005241c241144500280259203044c50311400303003d0307101d41d0060540d4600103042d091516550503228181500168400c00004084030b040b5460604242c8403507121b40d06020b000d41c01810121030a075100d03414520400803070309010543d03500100f500e48810345080e44880c0c00454640801400400302c0c2c1e4100041690326000011811000c503440c0004540301c13070041039548403400c446000c1002005070324418000e1941090010381071f01010b140402c0709181c20207649036060701e140b01d0422018040b070700c0804882f9254045031110100601083c1c03a6040c44942140204001840f900000d11024004540c4442500071100402d03004151241036 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 723378938 1250 723377688 723377717
    0x9120c04090b252c0d0c051203270409050d030501080d08010308070b2502060103060f050702121e1309050f04030905011b0203010c030b0a051530040503040302130903 73
    0x2c1d90151219012440d56031000003001d640c454604865080c41021880606d61500e401d0200c1d0303203490219201260014003684c1510b402111220b00482c100b040c41e17940015440020800801d2100c03005002800381c10215612a901038100740d04807a5100203c074030210031030000316040c4000707010040954004004c0301c0046009010003503001904900107600f00b8441343c2d0b208a01c4080c074000e600260f00301030010001d000142c400c040005c90345034010b100f207144c00d040c000d403201d501a11506403a1804165040600704a042c01d440a03007135000e03560780c0c0c3c40c403220319003031104154410100798608040c0000d401050682c84a03004917410307268000b52604040043d43c003280341d480c0c802080d1800003c54409650f0034040c4042d41025600c00003164209007040c08140103858115502400700101c1002c02c60100c40b0866060b0b0a44010544c100f41040800d940c19a81e07141003021000200e03002e1006001011004100720b07403003110700381002d0800a0f16942603c0d03034130402074046040200032018 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 723380188 1250 723378938 723378977
    0x210222050f0310020f1204031107050904080703080c0405040609020403050105070207061b080910030c181d1b0f13091e020a020a02211501080309120c04090b25 70
    0x2441040800046c00c00e02145486c03280c01070308450940010f0000303c074441e0451301c18020040030742001e03243c0074514a040e8480c2842032055410040412105c400000c81c0040c596050b603016000040c010700c4400e07510300c0920060b40050009950a510740740216a02c1d5000081150468415803034040c030300c041a2880230207010030342b0310942c0c0395030781002094074681d612810003c60b8075003901d0020b804d1788005c03801000342d00004c4100800b00c403e02014445804945a4980c3c2b2000742d040300d0359165100700399019100c0300110044040d030004900200d1811100010700700c200680721044003582d90706d180100c1030300c5421401c0781c2c4035050f0b60709031030401c07009800511040500e80100e602c609140e5020411924100b445900401e15904110324814000c0c00980010400401c4003180e550419180e140c5911403104e01900c5500e055800e8040c40d002482023060044000304208262484d6041241007200119044c100010541000783d00c031200640f03001c0742843c0c4036030b075210b44402c4d00207140d803 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 723381294 1106 723380188 723380197
    0x207140d0206071b06060806040b070f030b010e0904050118051c0e06031302031204080313080109050a061802030111070203010b010519210222050f031002 68
    0x2a99940c4050380004c1d0001e105113a00440c550391402400a00150740002ca850082031300700001e1240504a00d40300d41d105441b80e0480c11604501207040b50b8034882c5003400709519030141c0816050900381c4a500c43c1c03107040001800800c1c1c1a0702e00000745180011030b802e5102030900960076082035100d03200945071303003000140700c1c1550001076018040203000d02c0c5c14030340400c142001c2d95010000c0d01ca10700c2c162a901a611500c1e2042c1a0b1280e1103499a0110150240c90000d40100148291003499801c0809407a00c6d5810351794074006460310101e194030040c1000002c1d005a502880b07910f040511040c00c8556460491040c5400d443c5078410241c1444000c0c040c440200350140345003031624078680b41c81020005001506016010440c030782400300d80c80401c0c0c000da00680c0d040c140c0041054032000140460344d940400c1100340c4034060980c0c043d0420104045189403940280 = true := by decide +kernel

theorem cover : BRFrame.Cov 723201438 723381294 := by
  have h0 := BRFrame.cov_init 723201438
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723201438 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723201438 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723201438 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723201438 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723201438 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723201438 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723201438 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723201438 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723201438 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723201438 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723201438 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723201438 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723201438 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723201438 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723201438 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723201438 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723201438 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723201438 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723201438 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723201438 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723201438 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723201438 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723201438 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723201438 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723201438 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723201438 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723201438 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723201438 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723201438 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723201438 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723201438 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723201438 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723201438 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723201438 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723201438 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723201438 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723201438 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723201438 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723201438 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723201438 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723201438 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723201438 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723201438 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723201438 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723201438 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723201438 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723201438 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723201438 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723201438 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723201438 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723201438 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723201438 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723201438 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723201438 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723201438 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723201438 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723201438 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723201438 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723201438 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723201438 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723201438 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723201438 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723201438 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723201438 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723201438 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723201438 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723201438 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723201438 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723201438 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723201438 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723201438 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723201438 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723201438 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723201438 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723201438 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723201438 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723201438 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723201438 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723201438 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723201438 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723201438 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723201438 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723201438 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723201438 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723201438 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723201438 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723201438 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723201438 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723201438 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723201438 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723201438 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723201438 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723201438 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723201438 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723201438 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723201438 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723201438 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723201438 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723201438 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723201438 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723201438 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723201438 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723201438 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723201438 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723201438 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723201438 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723201438 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723201438 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723201438 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723201438 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723201438 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723201438 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723201438 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723201438 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723201438 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723201438 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723201438 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723201438 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723201438 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723201438 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723201438 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723201438 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723201438 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723201438 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723201438 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723201438 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723201438 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723201438 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723201438 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723201438 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723201438 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723201438 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723201438 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723201438 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723201438 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723201438 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723201438 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723201438 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723201438 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723201438 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723201438 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723201438 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723201438 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723201438 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 723201438 ≤ n) (h2 : n < 723381294) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
