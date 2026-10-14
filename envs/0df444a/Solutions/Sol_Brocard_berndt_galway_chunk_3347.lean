-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3347
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:23:36.719663+00:00
-- url     : https://prove2.me/submissions/d65bdd55-96f2-4bdc-9400-377c30b183d2

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 601798561 ≤ n < 601978417 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 601799811 1250 601798561 601798579
    0xd0c0201020304170d1805010e01030b0d05010e161d0604020d111b010b04020f0304120c0b1503010b010905090a020c01091709031b09010603050901020d060e060a0f0e07030506 77
    0x120307a464405400e07120444c000344084a00b80741d028049410030401c000e0b5805030788a04016590700088207034410780302482c00282d603012640028a0000e42140060020b602c0c0202c6c103040140e0004081c042d116544084154050b5940f0041611f06600000401100d1040300450924200768014046012259170081070800c403000d8141d2040e04881100d45449960303001d8005209002e209201c20f11006803005d504e020550480d0190030300c40504002c04d000601c907004640f161155400802d887e0f80400e0030241800c090003065070f58174600d200b80e4425440d00c0428000c07580030f020f200c0b0032204080c00b049056903e0420300750094000119042481d521610b0715400920043c1250801e42c5103881c490751600c030a0000d0521b86172852140c146250080c00e184280d40d541d10101a0448040780b502003001c0d91a1002a4064002c41c3c43e03266006003040c901150b203040c2808094800c80c0180c41c08500c01d9940d80120400d0049403007900c90300b0084c14081215980310380c10403940000041d0514078 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 601801061 1250 601799811 601799819
    0x20f090702210913141f08030301090204090e011e320106030606140d050a09140c1002011107141203090c03071205100518010c081503060403020d0c0201020304 70
    0x524004050300028000400211031081386803c01d034110500742160010041d11410030824610458003524075541046410105000c0011902641c00981818000c1d292a56584c0c80d035100030b034215015070540c090500810800c2e03c070051240320116420007800300820000d40d0380800c0249a80340382180501080103ca219920880c0210b550007a11401050038070343c50702c41300401300e4000740c000300304015942c0484513004d181c2406a1f40f284459400c00100c80d202c41801038001c119000d0b00030030b550700904010950320004a84088491030030f9800c80801c1c00c2d0000c0072401c0340c0a06401030703580042880500f0205040348840001e40c4801021900202c01082c00510540c0048448600c00c2c0d00c0304900060a003800d1140c98018a80e4407091006400a586c6441e01c422180342e4500350541e8502c00100020414104e890180c20502d008100d00d030520300008101042c1121414070070000c01004420303504001940b5032041d070700755014201c00c1c41007040445840c2401441641144010702c0045 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 601802311 1250 601801061 601801093
    0x23040b150a021c020105040525050a03050109150519020309010e01020705061b0702010f08090109060e1005101215091a07021e0601091e0203010f0509010b07020f090702 74
    0x89a0219001015116408506240703038290303d9544400b16418202800001503000410074201042c1140740c11950b04804460040011190320166100d1354994002050000644c002c0004901a07000003282d40380108100094413000c0c0d4440c601c0d000b0000410030070f0f203801c0d07019580042c03c1130000300c5d914940010043c26a04840030641c2c054001307406004141d8004000c142601d81074414071814100c1d10707000030340702070b01c800444428040d0100c0000d800701000c0d4047c010341a4020002c22603805990304a076a1074149030300309144a03140c5404a042c0d4004801c402085585200c04220009080e590f0510700d00e2806551443c40c03912070140b10300080c00282202d11042480020404900d0000002483c1c403000c01940a4040f451503030041c800d600219074281075581e403840100302214000d482d07121142c40d606070301c101c55201000208038041528040c1e400c4850032500c0c46d216903241c0515454034400d001c0000e5200600b030072080d0450804041e0254425058015182241c00c202905 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 601803561 1250 601802311 601802317
    0x71809020706020c030301320d030815150d14270a0605090d08060402070f0210050706020c0f1c0c0605060d020d0c050918190206040b180a23040b15 65
    0xd032045440c07100001c106023000000310410b511088080c04a6102d50004140000140540a8100801d000001b01122032103120b1010600b005080c03107041800c91841c00140e40c1001036107507840341c00c20030682c03c8040310645190103001001094004602c107040d0294000c9203690b24507030702d4055070035068040f54691040c18410419040a4a00c19150290060805000401c0144628814024003000c91070503176000e8800361741039031050768640b840101505c59000313806008003150f0001a095240f8440455400c0c12000034100315641c40144070403401510807102d08141c0055004c02e00c1101184c43c41c0c1015421860180118851903a40d40115004002d224401c0d2450030700e45c03001700100c0c200095080c5e40100003c25400d005e5542c0c030b21007a1210842d103040c105820400f4083d81c1907541c0d140403500200006902a5074840c040207403101d094018000b5588035407240000050300744d811640b2242801e50b1b8000421060400c14104002850300381016500600d988070000050300c2c462000b = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 601804811 1250 601803561 601803569
    0x2062d030c131a0d050402060408011a041d0615060f04090c020d0305010f050f06090d0302070e010e042a1502070923191b0c050105071809020706020c030301 69
    0x1210b9500c1c0010359000c80c40044503480a1441c0c00c0b40c1c10410a8000403000740c60500794661400306640e00e450000900307502440d040300c074555180c4295640d1420115100c80c3c00d425041c3c3c0c0505c03003909281107042d4642c5201c001c9820640010001648a0a0042101c01074050040417a402e203c0b0640d100c01c100e42240c0c0003111842e5031102d460004c240c0400114450324040c4c0f400348680c0d030402054400c4103046200b8079000704540c002d0500e032039403507809480040070090003c0303c80714142c0c20300a41e901c81c113200d90410014908000300301c400300c48030558410354202c8110f1203030001113098404480242035004440150622010540080849040b40464410780c0103240d401e007001c0980e000c50301d46074500e40c0d0260070211503240308886041100d0344000c010100b0520351740400d4100c00a0014800c910500400c3c0503d4100501d400c40200300c030090140000b0092940d400000791400b010326255114000060542085044e5032074004010540c8100710260400301c17101d00d854650380007030700 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 601806061 1250 601804811 601804831
    0xc0b030a06170c0102030406050a02070308030a02250b2e0e100506042301050c0d08011a03090606220f02091c0b0420030a0f061802062d03 61
    0x220801180d01d0180403003100030a00c0c0c002c1c200c2d00200f000081e41d64480c2d44910002c0c040c2c003091070352a150090000c50000c42c1c1028506030b40b0302c0e000d00703036800950040c05440e0703648240007510743c0000562800509a540d02001c42907107615940604211004860203440c242c810750b000c1c03064a0108045080014001c0381c001e1400c030700b400c01d4450300c110390b00e07003040d400782901340010054000104594500300340b5070140c0708d00600226004035000d00c907440d0b00001621600a41d2101c056220705d445040f18403620140c040c46119800091140c4400e8540d15910382c05040825080c1c90409003200d107070010100c4000400c0c1444481070b0950f148034140c041d035580e011407260b0850600c100b5440003203404101088212819681c2d0080c1690064006403904050410516030414072680c0c039140c10f20014101c0c0c844420526009241084950089420b5804c0c508450300041d254001e0f0000700d6401007810b42400c52500161402d5020b058445008440400190500e02c502e036000754042c244100f = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 601807311 1250 601806061 601806071
    0x2030a0b04061a0a090f021603050a020d09050d0b0a0b030a0b150316090504050109060f0519050c0a050c03040f0602060f0c0a14070c05041e0b090c03070c0c0b030a 72
    0x402d02d442118604030400b44046010300d0206269503d440088042d41c03202480055410122801c0754001c2c09901603c905030440000c4031010325400070050000c0c0030241d0308407441456030150495a1001511070a900000070089107170004110f5201c0903845011050009000c00000c40040c0c40d0444940f01621103821b03220502600c01c541c8072001041481c141e0040c4031900c1840c880c50414201485801d0f0499522004030b81048000c0d0415083c80350070003424888611805c4491004000a44000b0401101c2030f42c0048211118001c1c00e10400c1d100c1c113024203140143c6400c0d00c1c51741c400b92511450b80420000454280000b0071440b000e8a0341d68010150391500c440000c02c1110041d288007080701c01401200e800591080c60340c000c1c400f89101c400d4640750a172034500681500c0d40c10030303035000703082010800006106880c1c8031868a8111030901072019401c0500000580c169030f07040c8000c0f020800a400c20780100100070354588210034042400e0f584500d0405160415580260020b8480c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 601808561 1250 601807311 601807313
    0x5151e0112023606090907120c0e011101090816031701080106170627010e0d1e03020c10091403030403020d08180d2105010f0f0f1a090d02030a0b04 65
    0x881c81500040d90020114140107043e0000800900880d40b5180c8600c01e49800950310714414900d900c0550342c0c0c10400d010030445058003601203540c2580480c0010314841c20a45841d105007e040c005641141401e071401100030b0312603400d005c540d4016810f00c84101a004030304031386001d40500908000e00000344e02410140aa20f040440c80b42c843c41c61341c007039014003110003d00b4541d0502405240c0b4034110301a42c15050368050030700301c039a0a9040c0038005aa0089a41150b5006a020802810f01c261003115071426000ca000303a00d45d0b08010b604ca040380c0c98060030140d0100e88180d00820544c02147c807038180041c9107070310486017100141c110b0400c0c024180d030803150664001020151550b232300254a010242d8502d0084200c00c20000300301d9400e00070002d80d03100314003141c102200c103008640e107c1c07240702d084102c0c0f84103c0c909a06110400100101c40d050716034240d409044130400500c200c8840f0309032540110b041c0c00d900c1708002041400517501007100440035840303440100b0040c949 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 601809811 1250 601808561 601808617
    0x21c0210050f040e060d02040f0b0307050301020a0915020f06010b13051804110f040606050910030203070504031203020d23090706053103140105151e011202 69
    0x3184240014008240100070144522a00341d405890800b08802d54541d5580002200c0710309200e4065000b618000c07281c003c50100e41c000f0b14504000360203d417080b80d0b442e41490300301d00c03803251003500255040e8805c0c82a1324403041c9a5907080e8807807046644007082c4422503800c000007a881a2500c5030000303681d00c92083d80030750f81c8000781401c03142001000344884614540c0c1d9030081c8020039002a2604d41041551120701000c0d035590050402c0001980f5140c0181041e4043c800ba513105001001c0003c0806119008072886512a0303590325052618584d203003007c0c2c82e003140f0100d045c182c0074440b015074040548900c00c003420b1809411b400f40740d40711001c0d080b9420042d20180d01504048400c1c041d0682000859800912144649420303100b031005000c20410340700d903207021007560104000b0a00074500c68500d0214204002041540c43d810070078010240c0c8845c0898028500200034424440307031117442240528181050188248101026000c81e803089070300e10110703032400340e210000303000b = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 601811061 1250 601809811 601809829
    0x70608060109060504031b0b0d2003060d02061c02030c03073e0c04090302010b090f0402030a030309030e0301062709020a030b040f1203020909070513031e021c02 71
    0x18080c2060365501c0c3c10040001c3c900c3c81280809000c0b07844615280d00c1c4450740c0c4003883c000381070140d0b009071646907441102c5c000c0c00f2a0340b12503a0790b800146034580c4d2170700600100c0e8003406006182c2511001c541c0d003401580c1d0003402805103c0b0021000000010005000651043c4500c0c91615503d203403d481c050032080d1401d42d0303122030341d004003440410320030032a036603400500115015451480016183d03d141120b0b801190f50131a0070920b00408142c0c05400203041c100c4101c2c0e40307060990300d030350700c103001c0450440c2c01950540c060954007003c00d02a074084d03011140207203000703203107540300c0804203007990061741c0400203044015107201d40e0500d0104105200c1c0000807418003114686800040d01c80a4900000c3c015500030f8000c241008110520326011682c0030040c0c42807c4000407000d03000b0b40140b880c06018101000000369403610948c1221100c0c038024424a00b0a41103072141407101122000e20044502180400005603942103403400c02071000301380c01ca0020405205020302c184d = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 601812311 1250 601811061 601811071
    0x3020a1502070b1f03020d0b15060315131b08180f0a0204270c0f060509060a2f03041401081303030b130513030f0503091e1002040602070608 62
    0x94810b020070000a0840c00209800030f500c0345600400040a040c0d006050015900c02540300494240503002c01c25403440140c490207841d0000c03140e4040d20300511203184401c5a00c00701400d04400d00102614000010039400b003540301c00007400300c41ca16600c19a03542c00d0b5440b50045507081d41008441c404880e014940c1901e200007505a892110700455a1000404c000910850b1200001903508244204068802d0f4480544102114aa0030180220082401444071400000e10089582c2d409003003104d010b01e101406841c5000410002120b03401840e01c2c90700c0b0700600d11555400390192031500380d1500d0f0141c0c00a1a03a40340342120250340409582c00482c1071055180070007580400c1c0e03811444406070942804030303c2000b0305002030700c0074000d1544d40040a241c0000d101d083e9504504003e010362094544015003d4503960940b52400115601c0310503500424502d405070502d142200e03c4100380004640341c01d00c4015648060781c02c150000c02c0140d1009000f003005581c010195038000f = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 601813561 1250 601812311 601812353
    0x70b1915060c0605071b0201050c2401031b030206071104110a050c0c10050a210f0902130b0a1a0f030c07120c020901032312040906091406010c050a0f03020a 69
    0xc0c50740d41800c82c540740506d01000e814004080342d0070300c40910a0155a0b450300c403259404006601d40d03085400e0200080c0815100045149000070b8011a108035501c00d0780c0e001040b4030300340580d5680d03c1071364844000e8aaa08146c59030320540501c941100542400d209948466844a01d036220242c68008103251280c4117140310305c03494105a810001310b8824991b146041856100d851380580c803500c0c40214888010f600d4102c00c05c01d4421641d002c80030440c822601c41c1446203554401d401526650106075a1203100c06030204211207800d41860071901d0b07000d04a50030f01d1320f917180c00f05080d04111240c0c0015480005e0400401c1300403400c2030010b41e09410010090f82280c0c01255203030005000003803150303c46d285801c8501414041402c2e60700301c03000803543c07500c03c001b503524a950464840ca00c100f030309100b004113400c1024090000a0541d1101c0a0081ea4171180110341480c20520b056829015681780c04000ca50008400d42000b4040c0c3c00401d0782044501c0c2505221540344018159 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 601814811 1250 601813561 601813577
    0x3020102030714030f01050603220809180610050a020a0507120209010e0f040809012d0e031906091a09061e06100f0e280b070b1915060c060507 63
    0x1403921781006181918000c0d42c0154a83e0360b40b40045100c1420f80108020a2000b0800d000030000000028160035800b41c41e80000710380d5802508522002c1500d0727036648406400300e0300480503c03a80142c407449041b8411205200c403075440791801c01c06942c00011600c00c51034032440550070700c2c60b9800d004000d107134050a10380c80c208040e400500405000241110350014856815038400c8400101159a1101040b40e42d4085d803201e6401d501c1c05c00c15400415002030740c00038a490003145c00e06210440001c3d0341918002035640740020503034404100e609540403c48000c004800c0c034030040c40f544406000f40020b0500c038030490002c3e4444402c1d641105030b1103041003c0ca4407140d2014046041c40e007070881c208240c00c0c80907907003070103ca1041504040f410060b6034141d03800110108501d6000764003c80c02c41e0702c030340c660101c51140a00180c2a440c400c2d01242c00d11000805203411900142400150b141d14802404403101c444c4d0300c424006080c0b002c82c401401041d22415030041c1c510705003022 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 601816061 1250 601814811 601814821
    0x101817071202010f080604090605181c020a06051009060609091a0a21020306090c0a1505071e063612030902121504050f120412060b0d0302010203071403 67
    0x4103050b20102c04000304885c020100f141511a038101810f1140d00550034001751800e42058200540090a8403100e840341281c0e400b400010001c8404503901e4641c05007040c2106501c48001030030300074000c800b40014030840091240c071540f080e45d0280c010f503034803100058602200e030400d8550050700d04520444011050344e45a845250810071540e1b981c810307400c00c080840c1c1880c501e03040103001940501501080109402e004503c10500758012a4004006034403040e054081c449618854030100b081000071002164031245000021820101c041c83c840e042540c42406680d01081207064150060000403440700c2c4410010b054080071000b202c0c035140c41c4d9114200030044108940d03046c540c3d0f803071580056448000010114010f1170f0120350001c40c1100a01e10494402c803810f45840c00f030100061145600410341c048540010303485d0340c0c1001c1c1818500000c910724944211900f0359140e5006816481307130b46070308210300e00a800041e01c034603000c0e00150140c0c00003a1948088000ac2003049 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 601817311 1250 601816061 601816067
    0x61905130f06330b0f030a0509160b040311040902011202031b040806010f080a0f0210050d050f010816180b0d0c080304050315090c10181707120201 65
    0xa00800d4110380c16400300c0400707090040c01440f840c07040344071008481d00d85040e506110409420a03026141d601c1c420300340e45003015003103405007032162820100e0800106440d03085a811050304008084142c4240d00c40258400c0c001c00c8032075118040b141c001240c104140903112880c440d0305042950140070a1500d0340c0001c2018000d40c00d41ba054981c00f101141c140e40c040b51040f03e12040d560701403036403143c47e0781c21150b5a07502480350804003001a200402d40c000086a200c500310751104200700c12a810341e0070401960901d100381402c214062140c0b0341303109150300803103024030264003c5051550410100c282040c09901d100c0c03150710415001007040b60356410303003260f01404502001513000d104100041c1c2510000e02c3c054168060202d000c1490f400200003001114012000c4501544c4c44910b002c0300c07060100e880c070341540c006405184880c104201690142c0030726151521400c3c8507110b410b01c0c400d4080c3c11501121081000310756801e601040308201a0140128015607618168002 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 601818561 1250 601817311 601817341
    0x13020a180c0906140a18170c09010f030c0b0a02010b10030209120606030304140f10080703052410111c1b11010c03030e2a0a0f170f0d02061905 63
    0x403504124002c490b50f020444501d46c03540c05018003213006200d0303400b0324220760b40c1c0d003800f4100a807144001c100001504080f42041c24202d90340100c0f088030261800401c004c442d04441171883c159500c1e80c120001640d1038000442e200404c50f01e00681f900d000100348020504500405031450b4451828094940d0380041030724115000c000c540313101c01621101141c4c0c8036004640f1190840e45510b0104072090300815a9442080d06540401040d91104007084042c81c0c910301c4103085212101c1c4516041c03e0802e4686594585030401410384000b050140703107042d0b002c2d404600400b02d84c201c44c01c105644000c1c003011005c600f01000345e0000b282e480f050035908210140c103051101b400b1080d41054000e40100c5100d800c14015114081c021080e103c400255210f22035005105004031000d1925098a070601503510317600c03844034031a09101c484900c0884031a01d4031003038810005104021481007051b040005816405800703181072030040003c41281d0340203007003030f50b83c181020002d130ba007400c0c809 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 601819811 1250 601818561 601818577
    0x2401030b1e0301060b0c0d021b0a05090402010e090a0209100305093304080301060f0302120105041d011107060c081e0c070501020c010b10110613020a180c090614 71
    0x101402400700a0300181c0107280691000794402008a00c0f081c5100b00403411008018064003514403c1da0001088800112090100e0364840e01650083c800ca0502515003540144181002c4070103414410018100400880e4000c091507000144030059082030309c3c00d1369403020181414080790400d403682949680388887c000e107064403210070288850641c40c0c000c2c012075034071801034003a82c00c00b400d01c0646c0380c1c800d008040201d42d040d250a85910702c04c2c03080340d18030004010352010503401d1004000283c820401201d0071001a410080c10440081c81850340c003034805d4510540e14041c038540f220568120341103400520004030b0400c1101704c02c500d40c41121a13081e0b02e420417039503210281910180540600a0b000e50f2020480c80d4020005601c100c1e03510030120b6881c0d2695441c40012a542c008800c0d110a06420030804214020034580360b6010840c4010110078400f0b0f03c070b002c40d04100c8200c440b5403155076250380c2c1d00900641c1110421002d04446c4c500402000442d40404856110b0034003 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 601821061 1250 601819811 601819849
    0xb06040f120809060a03020301050103050606030106171b0c0109022b11011e440901090b0408040e0109110912010f05070c21020c1005070b2401030b 65
    0x107145040010b1035040319000040242801e0319000d540e6030050082d0000d00605000c1b925050119034985480030544c0d0480d441c0e5a91703004600540052a80c8044c00541b40e009840424414089814003003406044107a960380000110400036004014203c04e0318070040603181001440300114102c00d000c0143c08030b800095414001e403030f00c00101c81102000c80c9000c03008007805440145203901c4017100041000703042c0c04440192458500000c0100f000b0200d07a03c07002010004100100400303201070b400303640300000080c0c080d420388602d9040742c02241e08503800440080c0500020002c2001203003d02440402004001c5081008081d40e00c1a001c2c3c981c400c80c1d400e500c03056150ba09421290a0762030f0182c050106050608002d442640e42140407501100004008034078030004410450f0200c01650003405094150000d00038094407a9220300c0030490100f0201c0041340322202a0307400b03601030120300c00803031010801c1c210419961165650400d4100340025150350b9030060000455001c4032 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 601822311 1250 601821061 601821089
    0x30203070b0c10060f030501230a0c0e030a03020105010f0902210a1514150c060c0309030c1b13051306020d02070c090209210d051308030c100b06040f 66
    0x4400c42c541100c40031003c60450402c00042a0160428920404c90344070700028001c5c01d182500040e01c82c220340c941d146c03600c110b440018411070309a0308240c80d0f12003241040744031440e50303501180c03c00c2c10b045002d4002d43c0d1a0390040200481c4e1150400060045003001c500b400c0001030072441c602c107209140045c449580d404241081d003654480c101614010304108440c1e6511188210a0002d80020501c22004400f00d55a8030f4071487c1110b00703482511024011b00e07035a180500d29140c0000d4912900f6110500150303050080400c0441905800d90420740c40c4164072804001c2d20115060840c3d01c16810201032054a83c440742d000143c0300d070300000141e203800303012385c1c808007e004880000e80f11442c0070f400001d40d00e42c0c56001300202e4806030764505040c01e101085c04082c01440100f0005503005118104143d031146018054000b080c070401d0320322581c1d400c00c0c0c52564008085200c8643c1011850a1501745070b0311490410344400d5500c2400c0910700310402071059140d1040500001e514 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 601823561 1250 601822311 601822327
    0x3040e0c0d0e070302030c010e060d0e0c03030714191a04020102100612150b0904060b06071703180706020c0415050301020703080405060106210c020c27060604030203070b 75
    0x80c030903034040441c1e410041000d609807920581d520315240c030080e8080e001d9038280e96001d5210b00e03000e0300c8099003e0b2190345001440d641240040c1460700d01c64640307002d5032241d89003c1c1d40510003002101d0050183c1c4d044130802d98182403c05424903115841d010310501c01c0f0000030750820790100403500b42d04102203580d540b400144c2c1016000b03081170182502c1c2c0748000c1080e9200100c260902405040062005005d100981007122080c42505a00020035000100001c605401c4100c40b4000500101c1c14448984c0d11401c2d01d64a185035400380340c00101c2040781c0d0f05e5101d2603081007240c80c5401000780b246030007800303034030381030041445806241c444030032140c80364036a4250b05c0245400303802107640d0a40b5040003000040244c0d0700b110035000d80000000d001e4420269441c909075130b600b4660051011403419801840070901e003a06500031481120801d580b00d50172441e00059018036030304e140b4400c602901440c10000e083c0c621a0340180003d00143e14001000d0058809190f425aa6004c80b = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 601824811 1250 601823561 601823581
    0x60d020d032304060e1e22020a08040516030210050c1c0f0f0c030905330c1006030507090e0304090207030f080705071a0613090b04050f0f03040e 64
    0x200d002e401407001440e0b030022222071402c1c40200100c849035510000910814070400880d102a00e40c02c0d0350140c44410f22001614100c62040b01d4840045041c0d849149103243e404140d0300003000079004030b00110304010902c00c0900c00d003c0e107241c10200a07101103080d40d00182c5000017401c001010060b000c40c03e5142140100941301e14050000d505446c02402220010320544c54251114006090361a6007481580140103901038650b140e221603850a05043c180326a401e054034900816079180d59a80c0d000340e41135422800c4801c0f00e6002c0e00c1e80c5400103440d4515054031541c0101045151010400220301c0103d140c106495982d100401c03000240c0c60103c1c6180100d401c0405914400a0040109174000d048054200100d07180c8012030b03a9202d0080d03485005040c0301400d80030410604850844201d0703200c0ba8441801414400c40380800c3c1d44800803500748043c1200c00c0b100100c140070500034100440380003609c03448000c010800344c0100454580c05039206900341c41000e01d01042c0c030900 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 601826061 1250 601824811 601824827
    0xb010e040237091b05190f0c061506030e0304050108060f01020a020315060103051b030604150b0d09050c03010506030a030e040b0913120e01020c091504021c050f060d020d03 76
    0x516041c05015111103511000340300c041d0444c2d0303010504d405880300c00d074080d1007504c82a0308402003030304d001d52103c0000c7e80d2600042c040f0a08002d03e0801407000030381117206107074090b6281d005001c6105e082c440c01030700300c03908480307004102d42c01400200101c2e039002403919800301c01903503056042c9015500507864440c0684e4000c1d4180a00c2080c00361089030102100e100306002d91b01440f40c0c0d01ca42c0ea46469425512240d000c0100040000a605041c9a0803211400c0c0030506040b210f16910440300b0f6154010683e01c40401d0340b50728001d0f09024041040000000342100200010f040c048006550740b94000b00007014401d46507140d013a10b50b116806a502140c01600c442c480d4503103120081c480b00c940307440c02c4a052407005d0b40c14102e103100304401001c85806800500701166003908100c031600000f0004051803003610344160890311240043c00c000728680503803801e030340e4a01072307038409494002b010300500307141d8801044582d03900c5503c03805402d0b405440700704d40c01e0310ad0708045030248 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 601827311 1250 601826061 601826149
    0xa060807020724050d060b030c071b0303081f031202070f050a2d05030109080d141005010c0c080715020f0a0b0f070c02040c0914090105030d0f05040801090506040b010e0402 76
    0x8000710800278034004110040c4202c078814162028445041030040840180ea40805000a49004005811101046d0041c0700002c0d05828001d0302c030759243e03501e180301900048a500140c10561003005407500494032000540030032642c10070360505120702c00904a480c204c41580147d58074102442c00b15050490701c0c0686000f40c000d212400060901102d9603010302b4800384400e24180c5130000c0d0050510300c10f4010030850400c002c0701c514001c01148d441100c1a429141c82420010000c0d00e1507081000100030414101900505041a9000390818208104842d1141c000c030102400044188041c0da84c010700d8040d00c0b03140c0d900c4040c0201d60040304518003d4210f441d00d815824016001800c05084070710301c05450b1101d008010501403681c03403e1290710f070150b1112518544550051800011580052402c5801d01d580d44102c142503601d650020b48451b001b0105020900c9515041140540443d4846600c1400c15901043e0180343c070a81c0102400b0380554006881c05940c61809081 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 601828561 1250 601827311 601827329
    0x190c0507050d0e01110c01020c0108150d0c03030807050a020c10030b13060806092a030a0c090f180809012a200d0b040605150a060807020724050d06 65
    0x5842d2000c025155180201006012075000c8440031050700000464002c07402069018001c00e11800005482c2900041d1058001048800000300c158442d4201c652099004200c694255450350802408141c1c002e0400303020024200100c146254001901c1c5200301000c1e103801d80c0180382e0035011001400c8010010b90f10014044003080003840c43c1d0400360a480900c001d80c0c0c96521000125960384070801c0c8002c2014003c02c609411490b003403031402281031405404e540d244002d41d9200c1a02c00c00a0300807210322a40c07040c1e81d0503440387e1485042401c4030345030110240c620780c1e0749034107946000e040403172810004040b00b4014103256440f8a031690680d1402004615200d91a255808100040020f003034801140c1b8407942615140f0b0407440d0803500300c070285050f44c86d1522400042d01c4020072084c8440003e201c4032002e5103a103003804009106950340c8403881c0c14064002070070800c6542c8140d01c1080c9142c0a505840381610021500b03410508201d80d41e114491a00c001419480e401800d034 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 601829811 1250 601828561 601828573
    0x5160809100e0615010203041d090127060605030601050609061b010606050a0e1801180209031c0f0804120f02010b030a08070b0a05100e15100e10020303190c050705 72
    0x2c000083d01c1070285500c0700081601c05000401207a5902440c40380d140341c08400050310b000281303009030b0705411419000010504820a01e041040703042285c0101e540c4030034a104880500c1202c1c81458013400d400c03030150415501d440000b6116000340200307a0f110350300010b54003a8400c414070303540f00c5072140407000340700c40d60f5116070182150708401900c101050300013035450001e1400c404130301482d90030946030202503424107051013449001407404040c013036400c2000e0159980d040003040c50381803039001c14020780c0c644100300500c0848502d4449007880056828480010080440300503080038620344855283d00802049015041154500b605406604040307418803107281c005200c540c0c081c2500c2c025a4030360200e4481204c1e41201d003d80c040900d041d0030b00c08080403618050b004072202129a041e24290400500104440d01002020641d08401c00902d800c2021b21070100340580d0000e582540b800c01d000c00d04180c00c0e14410b0802d5030b5a000a4a030281c000c00c291240c00b504034041b13071b403 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 601831061 1250 601829811 601829831
    0x90f030504050109090b301023042301060506270a0303090b03060d06020c0c011b0503090f0102150702100605040207151508030a0e10030516080910 65
    0x100399400390296900140f2004404103640c4124010407025860191080e001421072034410801440100c03401060310f01003840d1094000707002c100e000601158a1400250709070040407140b000500c000a6520020143d410000800c0707501806a0003040100000a0b4008103c0601401481c494104c554810342c00300b2400c0823501020300e089545800300817268142070b42e510401180c5640740c80014006803c40c10705001769894000a190000c002400c0c2526034404d5a4803881030b45c000c02a08580c540c0601c08509240d030780842035480c1c000400d42c10000c0c0e0302d01038440039241e00c115051a4068901e00c00c0c10b88841e40300b000038038002020707850302004c0c90404c800020b450f0381c40524903c1c00503080a0010443d071a0600c00c842555611444c0070060710075560003840507080c03200711020074032101d00c0d001400c80014002094280e0b080e690f4401d07102140002c001200000400c0c8108041c9003000704403081c2500140280c0c902034504107460543c0e01c0c81c85480ca8148400c018189150600300c43c02 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 601832311 1250 601831061 601831067
    0x90d03020618010510030f0c05060406030f1b1710080f0d02010c020c1813150606090e060d08031909060c2706030c0c060c0e0123120a090f03 62
    0x15001c1c210065410800078102d0851909039542a21010381c0f030b241411041000848446404512610030040060f050740d5800001d1940c2e00191301400210740c46400030450190948625400490141d0031103201d0044040020000c421404903800d6030000351010420702d00c1e0607081540103104100460b0041c3c0c1d20400c400b03803109010300c504d001541c20a103541c0c90160002c920013410660240034401d11540d001080460020081c1c0f007141088005001c64000c50300b401180c1500880d1090f01084041c641007008080000c59070050a041c1852001c2c0f094664031552039241c0c1540091010352651901640442c3c4c201d086000150b4640c43c1c8400941000096008000705840382d40301c68001c1101e4071041c103428074642c06400c0681ca0150b1040c082c00d400b1ba44441c1c000b00052400c1c10600c011550707890100d544040034840400c01101400070590b80c46414228480c6850001c8450901c441c400110716002d03c0003c05c0b0203034081c80000d10380d44c1c12988206030081e08018000b5a16000342009 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 601833561 1250 601832311 601832323
    0xd0f02010f1409060a0e31020414061602030f0607020c0301021e03040c18060f05010f0c03110a0b093304030c080f07030804060e031204080d1508010608011d061803090d0302 76
    0x2507005800d02c1402d50308131f00b032842650200c1d40c0b07198445021103103a4040080c240d0122291107100c078848042d1402680782000300c4051204408020412424840d00282c84e28109400389482030380100060350303000584024078400c08040f98000c8c0d072a034856140803040328040344c0008021200c016585110307000c8a400203000c440800072020041c644031401100c0382840c4040040c0441c0c00c04100c0c2002030f01c2a0000034244400c44180d0341700c0200c5176140300310303002c1c2554100cbc41507100c445c81c80f00c0b10005414100c401d000b5140c0c2c0e490284880d8503070b40320003030f0010030140c14030140142038824000014100e901e00700081000b159941001d02d0003800c2e13184203440556007a850409910345480b00001280c1e40700510a281000584e0380781e41d14403a036840700748400081c2d5101c0c12181d144440250030b15026064050010170810f040841c40ca007116040c0c06030401d44041c545202da90080301050042e0808001c00c132104181c1410f8a02c83d1442c8100600a504034042210b0a01415408110 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 601834811 1250 601833561 601833619
    0xe100e011b0209041106041a22060c0308100f0602160509060d061d03041706060103291f020106170312060603070e0d0f02010f1409060a0e 61
    0x603009001c000319051440500781020007500302000c038001c0340101d0440c20600110b1080100003a14003919180c440c881101c04000e10302103003002080c7d51510300080c00c107100e01104860180c3e40080e10b014401070841c0300d4103002405000f040740206240d5419035440300080c20758528048180ca5803010004d41d5800150b2019140040040c2c011035145410b2a078a030041100410040d004290f43d141c00000f800d044000050b000d02c0c40c8000100c81d2010302c00f0b0002843c16a24141d00e140211007960b0406070000c4c5114101490107004002e1503840311050031400100510150544840001044850b20010100e29681c6010421fa40039160b05411080682d65801d985850342c1d001700c0e5190b40e6030700440080e00b0703101c8100340004900e420100b002d5540002070b441d241d0303242842c01e4089403c01907001070640d100300342d020680b025960040094481a82c40346070040c2003001030940d00400307009000480d803060500051410341740d88120110041d080000340400d10740800e40040d030305422043c502c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 601836061 1250 601834811 601834817
    0x1214041119122121020a05090a030b0106020d050a020601170309150d290603070516030309020f10080103150e060c0705160308030103020603060a210303050901180209070e100e01 78
    0x1100d0000e0f0344c4200c0349604c034840c0604185003c015448040d0b00650003820407075041207024891580181d482080c100010b6014903055601941070800080c20550050f08a005002c41080200010303a03002508604555107000308030301c0010031600342803c41c13007419940e5a0050006a0400b0310500000007484500c1c400c41040107080032034078800c1c423212805a00308405801010f500070a07030502d0300007903074041c0e6180713045450610144180c8414181c20003090380000d685280c000b0450030585054004003104464075003107129164001401c0c003d05010050000310003100c141102612608180301d0050039606a4070180b400c0000840e4a41003203000362103d00c038048420441e0700010101c6810340b40c1004500385541c0c00e5400340415a0300152007150400f0002a00107100c402060110080381d541c5600c0f68401110341c02c00509860002e041d03185107900d8888400344500c0d0540948240c2641503546000c1542c815105890140341d0740146a00480b082010684c47c1e54818400300204009803 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 601837311 1250 601836061 601836113
    0x90b0a080906070e181503070611010c030e1009050c031912090803030f0423010507110303100909020607020a0f090e06150d060f020a121404111912 65
    0x10001ca46002040220a800200c025008982403a25040030f41c5c1c44881b0384002c0d41121007900c0401d1500c0b40607805207000072043c00000c0f103c0c83c000c0c02103050546061a041c080c50325005034058039080030840782400c5c280c0d0b507407060003041010b02c684150860001c09483e03100002d203900c3d55903121a144c3c1183c034400c4d00a6500b402d180140d09a038140c80c0c03408021400d40d0b035142c85001a00d2750280041d40c02c42d041200d42420020301c6910041901a0480080b0341800c0284001d440e00108100c0951560424020400d407100402a030800300e03142e440012880308518000710300c00d40329080c4083e400c0101c8440c0401c030403c4c0400310760106c2e000d0301000c00c000f0042005064a680c1c1c00d4030000d407a9080682043c041e8606240c5100190f07000e00b4001803044101c2d40b600c01264095a042e6020481003012803103035031031520860324450030741c0340f02c001c040c64150b039035026517015803402c07510a541c0d1005111601064400507405400000100e081c5000c80d42040088256545840da4001c1045 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 601838561 1250 601837311 601837321
    0x603060f0115020a0c0b04050f040b061e09130b10020d0801060e040e011419050402180c04030804140901060c03021c120f140705030f0115090b0a080906 67
    0x244840c8184021040205240d00b0001d4088520102e200c8840840c81144651004210b0502c81400104401034145a4491400050040720084004264030481c07070040078580c40e403520000c983c06804104400c4c0342c80c85911408034141d00030220440c1d00000c07401e80340f140c4061107501241c2e079110f0480d011081c2c074224000c202d170340d140c05c1c1500e040020001d1004012040c0207118424100b20010030100e001e111003240c0304d084849031642e984010b00c000d000c0c042c0010354101810007820405d44248428900b580200c0d0a2500b0628801201043c40700001c070080c00c01c100b52030255501c1007180b5680ca0340d960901d0b11240c08548401e200e54204400015581e00030f2003c2c4078a554507401030004514201c0c10382182c0061401c2c4402400081c0558041e11800c1e4800c03081c900510301c80004440340c01400c205050407005080105014040003171284091413190041d0450340d0f0030034003030709d8030b8094803040341c21088035030081d02c6860380400e10314002a00455414821a0213004442c229600c2d = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 601839811 1250 601838561 601838563
    0x1009050c090c190c050d17010506040e0c13030c03110112020a080f0601260f010905090709020706110a0509030d051c02160f0506010f150e0d03020c04060b09090603 72
    0x20b0b6040c1403070450403c000d444001c2c4440b95003c00301200d082c84e241105403a00e03060708080d240f290300d0000072808541e00d43c0d101d6641d807000340501000d41c1d52038109414551003401100016003001004000070405441d002140308031080610fa000700b81c0c0d200c007680c03898690b09028000103600d01280c00ca04100c80842014425140308111a42c0c41100f0313500e450b145480a1100a401c0c241000001401d403c00d2075041440020640400c200da00c0c91450004a0011940c5041c1c100c210046d04100c2130040d01000003d422082d1501d031000169030302600c0c47c003c0002c3c08885c14082d0b2000021456060840c1c020014180b602e400745c2c107843e04003a00640485d1a4070561403d04089400c1c0c040c2614a002030754050a0701c03c0307140018001c401c02644812103030b0000e001c001c403103c4c1c1c496001800503e4070b14110100901c4090001d4035411000c0c407024111503204004140250046000402450320800c42d402c4101c00180003001903686400c0c038078299512402080d80940c0c0c0c0c48012a070b46040c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 601841061 1250 601839811 601839829
    0x30a02041e0c17040b0402041407020d08060f0a0531050403031d06010603090c0b040b0306120606090a05090102120426070803040809010903080a05030f150a06031d1009050c 76
    0x40200043ca80550762980d94400368803000d40240d8110ba81e95a40124940174400e800d4052040d5400620403554201001040044000e00443c021a52244540d01c0783d00d48000400030307960210343c000d1808280c603101040a40185450b9034900100f00c100c082c01020b0360748200d00403806980c0038480391138400941c0c003a6084041145c91282d02640041041510a6001802d042e2180c5401e83c04195a03900441d91a005600078010b085400024410f6500d0041c44500304c03400b00714090285031400000042407400c0060001c036455488a0005820000a5045600c1e90340b040d5111a094145401e1041c41c15000528400c015200390743c0c54440c02041c43c081e0740c4d100e64494402c0346156210341d40d64180c0e41145c3d1040c0c1c14000c0c8000c3c0480015258800303042245400d03074806840c1d1908500030401c40c80d0281446041c0c1d80002400303601a102c84002c2d105a4455040c0800c0c0000f074454148000e190001d0307104210300440c1075130828824281c012a800c54018400c60f0501c0c8008410405500 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 601842311 1250 601841061 601841087
    0x150e090709090f02090a0b0405010e0d0507060e120f210f071b05180f0c040303120b190b030f100506071b0302060c010b031c0903020d02030a02041e0c 66
    0x503400c820400007000c40e90808003d0070080c00c0b02600304441a80481c03544506500456592000407605105c0d55a0103203100c1d4440504503032540340749846499040e01c0e40020702940c0104121111512003d4440c0c550030141c01074000c04442400701030b001415110202e00c07826422480c400c01c43c1c54030240340e6070161449059190f07038542c1b0f07100007680c0d030a1042c1c1034400d0400e010410a0310004d0643e80d8801c45040481800504504900c1c08840050f030402c0e000b016084420000c0c841800420b0748070598659a20300301500255014144001030308071500f040042198194002d408202c1030340c1c030302c06180191754864144000352100a5072034410411409010740100d810700c4100b0110303c041310389075285003200144e8041c070313500da0700402d4181d408901c0c00c0249a4446c016407005050410980d030403100c4184070b0044142d080440142035034420320010740315070b4619029906654084c03020100e03140d8000c00c1000242200c800346003510741008551105c244c600911803141c1130041d5001c2080d4 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 601843561 1250 601842311 601842317
    0xc0b03010e3c13081215091005090402030717030a03050a06081c2a150b011202091203070c0f0e160807020f0a0b060301240605160507150e0907 63
    0x1840e0440312442c20250028002c41401d2900d00301100807410803c001c5c40d501c2440c0c801590580390a0b050030b010580194507043c000c07030001003042062808901c03a80c007030300e070200c40700c0d181a1143e00010303160030300c203401c90515112116410240283d0000050681000e5501c00340480e51700c44044100b03c801c0da11498566810400c6180014101a0300032132409000341070812841032003607a18452025881540e588681407110b01070305000303802c10500c155107080c00301813248844450000f04051a0308e008100d04940101e1600443d946040303401e0721116100d811a91500c01504050094002d40d108504a8412058002c104143c0069619200701c5c0261000b1440e51940442240c0c03000380240b0440840c000d9070f042d10382c40360302444140d0581c3d01034100421030b07050250806003190300400000207240100c80c0e44051031040020a07100300c9100e03040c16500c803101200c10b81000404050000d006000d40c44e004611203000c60503a607894155035640712510f0414a0900180d0b405c15034150b804 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 601844811 1250 601843561 601843651
    0x203060a05190905060606030405030714030d06170706051c020d1a03060103050a0834031124100308030112050c040c1d060c1b041506050301120c0b03010e 68
    0x600d0601800a6030270502c60b4040380e1074207001d510344040b400c81812040c21943c01c006030340007112030980210300107450768503603241d0b024810440b412750340c0849105420600c003001c0350321a02500030700706281041010403002e540c2c4980308490705000f0700b102d01200b80ea20090b83c0802d0130034200000c003241603d600000070302e0149160b4541d1041500b002000a2140f107242140450040c09645c02a9881c004210300400d20b04403860090850758144416405030390040d0881507041c41d1200c0a1181d0500050075680c082e00c4103142d4110036541900098140c81c0e0000c00001c0412169101c1120180528180c542004507002000300307803240079403002c000440140160150740e040c0c461403007000d040208018038140c010020942041c210410821010780e142c91061003d090070302800300b50824043c034a560b501c0c10080c3c0a001e502040c028100144048214081046554022040509034001c1000e40301d694035034140030484c404a03031440c0503504030b4451014005015083d0400981c42c6081c01c00 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 601846061 1250 601844811 601844821
    0xa0804120e010c08030c090d0302030c1506010e040e0106270b0105040e0105040507091802090906030c061b1f0507020c01090e061203070f0303090c08070e060d08070203060a0519090506 81
    0x410b170806005c4001100c0e003000484242d680d41b00c1c05000d214842c1e00650340395015245114244800180d901c249040c0d00380c1007000c03681e070203113076190490380131a0000303428901d001840380141010b400010100390710b248a10074041c100e041d0902d243e102640c0a00000551a0044405028a03c01d000305200810b0040c44140380580010307a010b1002e00d04004a544d5811040704108a00558400055800942c816041c14071500d00303540500181c000b09005c403084804500c051084080b05417121441001c2400741c100c050040c02c044000c3c52000420380f50381c03c030b00c180c0102000da52010240c46890240700140d40a1046882156400d682d1911980c0c1ca08050280d8610310005c0c16109000400181c400038946107031010009001c2d41d00090107015a1400d04c27040075264000034540e1b44114010410000d50382443c0303030301c803d0948548407110118a402401401380200080d03040c09600100241e0904aa01035071081d07854031004068024200708000449140c1035000d015038101c40b000407 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 601847311 1250 601846061 601846073
    0x311040504020a0e090c04082a010309050f0a0b01180504050717010b0406031505090f07060309110306180105150303040e04020a0b0a050301181b1110020a0804120e010c 74
    0x2c1007400f403909180c5010f000200004805410444100040d5000800e050111813010050500c01c0c1c807440000317030301102c0035402c1e1006542008020798105070f12031070031a040040c14404001403030304001c00c98440700490310304081c2088003405140d080b410880800400c0c1409401030300d0103160448090407180d07003041d100100180122500300305664841030030b88502d44440c8254002180202ca1031542c404104e480d683c1900c0021300052219800203000c2d000618000c84c400044800a05002078044080d280ca80e00c2e486400741c105505000d42d804209001c1415000e90380c0d4203080800030461591820f03224600040a101150b4040d801440700f84541252615601d80150000742051345050b6515004600c940c000180480000c401000401c16450142d0083c0d2101c803040200303010188950000e813911048100c0c0b1201001070007540c0500d40345051200580301080020150341e140f117000c07805000103c0945048600724082002440803520404100c002c0d03444c165104040321302076840300 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 601848561 1250 601847311 601847317
    0x14250309080c0d02010219090303210b040912090f12080310080f0a0606060815220203010923040b070f0306120c0e06090115030c050c0a05060115031104050402 70
    0x807100c00104102c4202d8900081000014122541c1d00141e40c640e514901880d03c04581c50343e0805003d040c500c00e000090b00810001c40204800d0411070303008000010300da014204050045801c03910300320040d800e120081c0c0c04a1401000c5468104070b007a0f95000c58094841140310703485100320003800440c0050481001980c02440404a0200094407201c015042c45592804917802e6881b40301e0b03d00070890f0030300030b8100502150a1065062810225100504081d018403600c5032000740710314800f201d00b00c00380044000902400310340381d68540200400500034509040d011655002d400345030b001049560a01c6143d011010b191291035111040d5007a0345150910024541c90702404103000c625582c0585009009944c103946291410107911604c40340030303107050700a600000045c01501070026564440a61500e000200541c10200071656070140c91220021400b90b07110f0364041c44400121036068460481522403691603e5074180c0841d105042d200c11141c10600c001c002038034240d030103 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 601849811 1250 601848561 601848563
    0xa09050306070f14090a0e01080706180501021e01090f140f01020f07060506030304091505120f06010302150403050a050304030b24090c070b10060e01030902090a0e03040b03040614250309 82
    0x106c1117084d880f0650301c06610400d800811a43c0d00070f50040254641c00381d0b24841d00b2002c050b020382c00074240b40000391181c948030f540a021004540344207020328401d41c444030645030420f001c00180c40d91031a0507080792002c51a80d41061180030681503040106100b120a4905001c03652850501c0c541c2e40c0d000580380c000c0c40c0c15494001800001046015401035140040c621500102c501e814035042110074106030071a104140d0080c914115080c0b40040c0c058103482d01210075880e4ac001c0400420194840c6400041c41402180100c43c20000004094029641300e040340d015103a9406006010b801d80901c200c180e031029080c41c42100e0b0030078a52a48e0403003420701d00d1901d00360540e203904c00000f1080e01c124141e030344603d00800c441b80d440007030004001e0f001d180501500203a0340005420340d002030201c0d5180c5a039508080b9100d601001150014005100100c1e02c0f0714003410140d008064181929610344805000a000040740c4070300d014805000241e00798002d82c1840d8210700400a80710 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 601851061 1250 601849811 601849819
    0x60605090d0c030b100504050c0a020a111311030108060c090a03031b0218150102010e0d0e030a06090503070b090705150918132928020a09050306070f1409 68
    0x102c04000701d4059944548200e0080c413545200d1454a0300703100c00c0310303070040182c145060300380611008558003003261000305801112507807044a00d4400550020440b0200d14521447c01c14510440d100032009141210108000c1e070380682d4030050420814410744c0c0240781e101104810a000103030080001000c5807490b290740c00400b082c1640440c85580e4119441c680c210301a004010591103a81501140b004080c03000388140440d06070041d5a4095040f085001e200d01c0000c5014661010802000b0075a0000000e01520595085c031a4a0340e00000b01601eaa40c401c10000300341510000e600c1040705d2012340b07183d500c0c0b4803a00004419030000e42c43d1690106038000707060503100781c100800780038044e211060307034000006203001e00401d6800d004154031041c11002d11115040c0002c0d465600800380001803130810080701014200500c0e50101c0b0380c50520118140d51015403165601040d07810680c120354480d190800c041e20040d074140b921070006607410044001e8499120040c0c441424050 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 601852311 1250 601851061 601851083
    0x1205070f08250306020f1812280b10180c021f0209040501150f0e0a0b1e030106020615091311040204080708010209013203040c08011503060b04060605090d 68
    0x184c0e070501030741d00100380b600b02d1160124205404041d111280d411b96030040359906100d980402c3c00c1b41e200c1e030440d11800540828a01020030348541c0c2d45c401140c0d0350344000142d28500d800d00242180318824003c1c481440b810a803440d41024607441244980b0700c0c941c0040840400840c20300e0f012155495000c056581c0070302c035000658440740a02c0340a4050410142c4080e985c69000402c00c1c1800e041c1d803000c00501141004094a07614100016540b00c00342d155a40d90009844111448200c00030559054000000042c40d82e030108086002c0e21120b0602e4480d80d90007010403103454001d039072503041414090001d400080704400045202c00002d0405030420b81d9542c4a94141403ca1f030003031500c0e9400003000141580e1004504c0c44070620303c92454050702005140302c2407150b841785100c000301e100002141c18061048800170081c08000e00034064000d00301c0d92100c0c2114030388403c640490400c01010803c2c60503004003010780f2013945d030349414403503c2700030041340820180e0143c070202011 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 601853561 1250 601852311 601852313
    0x2803081b010c18090b0105090d14330405150114031212270d030915060b030114010e0d0f030906091815030f0c0314030f07110301151205070f082503 65
    0x1034000b2742c01c418012003180f00380110b4500d94600b0241584034034a000c14643e00a090300501140c544c130401f450304100a1850b0b5241d2030014900b130703650127800302100c0761480002224281d96a081d603c1a0701079081c1d800000400011000600070600706003c890715400000c1e19946070007845400c034044542180b4590404640d54034100848110060300080e114003000003030240151048800403021201003000b14a001c140311401c1c001070040050f580c8205440c000b40d45e108995802400394000c0c58905d814184d8a0200b0060943da0b0044001c5002000002800c0b07015080817005c03241d5072401d41e60303c0700340940490010048607601c88810000001e0100100307400b2143e03190403510403594824414294104007160313031514881c0341410752081060000c400040c606550035076a002111351344032012080006d001d04030a8025000f4407007400c074009030b0341c3c5608485403080740c000c00c1038403026921807100010103100c2e4050022103500120000c5128030900c0301800d043c44940317103440207a0f0f8803 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 601854811 1250 601853561 601853569
    0x4050907120615110c010c1502070213060905070e030d0e01050c0601080d02070b040b0711220f20040b1b06010605040e070305062803081b010c18090b010509 69
    0x110340007203c500e80c11240041c02c4a8020a60f8650364450a0060441e03d00d600b0008049280e00d8000900f4210360240d0320b444103500341c05844d10150b0041c110406e02c04a14400b00007000a44501c191082c142404140014019440c0d5442d884014002c0c154480c14260140d94000c000074540b030401c80d00704141c1c02e01100510001c1d000c0c01401014210641005030001e00d840e145403c10000024100010003104080200315411139511514011000d03103020000380c5d010b000501c01040d41c6841d100c0c082c43c2c003811584080c0018010190411003001c548650603840b4161110105c0303690340400c000c0c008508200c01902050310002002c214041c04545568207040081e80150003040011509012035128444116804501440c08000521b00807000407004480818903081510703010b03c4800303d8560407424030000d1071704058050341d03807000d848200c110034000401140855280c01aa01d02461080c000c12480d0385903102035080e050b0416120304002c00401300c003a030600c001041b200c1c104e911 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 601856061 1250 601854811 601854821
    0x60204030c0302150c030d0b1302030f040212010e0c0609030a0f0b010801050f0601050a200318030d020712030e03011b0503070f050f071713030c06020111030601050405090712 77
    0x700c03030107900404920303610500101403045a40310710809820310954400c80383c00019078031042080400410402c0014012406822558a9500106000004100f00c4600020403035015520944182c11a9400c2000040c01c96801d242415865080b440a41069103401c101038452618014181c038280f151503512008a410505000ca0324020410b0042040d6003080c8101139000c1074090383e0483e68940500000d0191041e5403800c810700032000202482d0300d00c0c20010414030794118080302d60b00c2c8902c655080c5c160101502480c4240f041030324460340580f020480104030344942c03803110840c60300c90380e00340ca001400301629505903686d1011245003051041072015002280c0c0c40e880c1da00c2c140544010070020384034015509004082000201c000491303811500c0f03140e0060020790004401c900104010710801c50441940e0b4021680481400442d030283d500301ca07002e0700200108500200c0f80d1810340002c0324200e01050081c00204068285942306070350007040c61900354802c0c0740004484044031 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 601857311 1250 601856061 601856063
    0x2120a0c0f0c05100f0e010507030c021c080307030b1f051b1915050907030203060106120b030d090503070f0b0f032d0603010c091208090a03170a20060609090a06020403 74
    0xe5005d140184940d0304000c0c40308030040203180261401c001914040d1070624100002402162001404e0550301c40d14001c942907664040f420139a2428405030050240046a4045101d1401c81041c44103d405600c1e0701c0b440720703010f03071074003420014500060100f8984403400100180103d20714100310030301c0e5482c8100300c10f100d030102c040f07800c1121800008440005009021030b90007400203002603900011020704540881c0341c400028015499100e000e81410a00c0c3d51700b5200744150f5080d408c1e0440c1904068981c207408860506a0f2030100c00845803c81c071490440610070000500044000b00045910450600c402d021201210070312203d40307850036a0124014041c081408800d15083c0250000001c0a107000801c05048c003105849100000f0380040408038002164500354440c405c00c82c006680000c10082c0e03035141c1401212403036201110613400202c3c3d00710301c40a4941021003c1103442c0d4840000c20701a61450203100300701401608030700d158450b00380281c0c0090500d0008001071 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 601858561 1250 601857311 601857317
    0xe07050d171b1609062c090a1707030212030114010309020f2805010e01120207030e130504060f060b0a0c0303110f0408060105030c1305130c030302010c02120a0c0f0c0510 75
    0x1181ca004c6440088403010b81141c4481c84851501031290310a42080d500ba081c1a8044083d65840d0a55024130380006414000c2c89100300c000400c40080d244400350a41500907000d0791102104001c130388032240300034010788090802e5a07003241200c0d482a401030300d28520103865569485035400c0018000752070051404011700c800084100e44041c400241c800038070003800c001003510300b1200060104241187c50440d01503002c00c900003031511a80c2d40010701c402c058054010303245100a45000742400326801c4d90401e05001c10300415400c1441803004640a0034215800d00c0042001240d11407042c000540416032101340c08440c0c400b22400070011251025110707540e591804c40031900b4060141e00c0300c2e01c20703008408402044c0c0c50301e240d000c09440d0001000105590b0310301c0c1908404100c0e02014003036204020000c410981c0552002c40075020640850301181041e40c0710b59510300c9038001100c001038501c0d83d588001008c0541540280384141405240243c0314008240a6440c01b4061400 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 601859811 1250 601858561 601858603
    0x51e031201090518010b03100f0f020301120c0f050120010f060f06181a0307140f070501051b1e0705010c05130e040c0e0402040b040c030e07050d171b 66
    0x1800c003d0303040707881d410201402881106c5502000030b03221240200e6280556440d8030310742d1b102603007070340c0030600c8000c41ca04119282c0d619100c40d800c0d000c030503038411a401032043c0c1012800e05500305004088510594844901c0060505948482c01014080c0030315903403105070300f20f03001c83c4900658001d000c01d44400303011645061001450304401107510701c4418030415080c0005207041c0700808000c064a12200d6072611000002c9410040000c0064441e04011401c19a0113502400078040540158001d1005884100c0d24803811031a010400741031010810454a00e08020301041e4406541410441d04000355600d51509452803803c04000041c000aa12004410301e02d009a01912aa40b40c000c1c00b440d060f03551402e509164050078541d0701d008000a01155515004400d08040c054414002140c2461014000d802e4401d421070450050718004512410714a0504400e140c00241c44021802401c0c955902e643c00b0342510030100c1c00300c0b034401840040070840c000030a5480e42c20011 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 601861061 1250 601859811 601859821
    0x7050615041406030304170a0b0f0402090a020309250b070b091e07030206030c210106030c110a350a080604090f02010e0a120c0918051e0312010905 65
    0x8200d41c82d890500e5881112401031000c2610300009540c241c44e016144c1c044c1682d14954090718200b940c190051081e14540f00300084815400c080c03a00413882501c50f12104d031504081035080e40401c640c0f02c001503003c040411481120200f0100210b0108117284544646400d029083c503802058246d861401240c20300251f46e404000d8240c503003203542c40203e0740e02001580c5c0c58652045105c01307481400040302203203007a6000003c03039506083d002c040c200340441d0291511280c590034450b800c0072910b000700c10055a8029244200c01c3d210340d102a01200185540e255035002840c106d0440044007200d410b00254551594003103a11160b003002a11105903010081107601b0044c211405541002e500c02c000903000307040710b2055503090070183c940d0300500d004203d4001403941315002850508100c0c006001504903003405850200c2d0050001400b81040c141e116081b41d940242940c0c0301c3c42045c0d004062888007003240074403142c1640d10704803485400341d40c00c000a030414070700e05a464003440 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 601862311 1250 601861061 601861069
    0x150f12010905010810020a05040e0103030c050c04050705091c0b07120e0312150102010b0a0b040608130203070501050a0e09010e0906060a14010e060c060408040509010f03020618040207050615 84
    0xa4010321a02806026035030402500b00d07180c1c0e4034038800b0400d0b56004220407048502603011f0b03401410001c8281c090700e42e03580c20028900e0018190a232080c4c020100042003508003130041301c0c42608a078030390918000b420002d0200208401580036459560b185203103000465242d02036018400695900b00c0700035948a16804550400c03100008640c020000c2500e15505504981e40c0030560102034010b0050f0040141e01400c50b080702294022595400420102c85440140c801d80f000707559554030540c5c4402100c0d00d000c04074074001c1d50680c031042d0104030303a605c02c0707000f403121203601d180001c0340d1300840000c0380e030004083e00310043d054034503030800003016002c01c06a6401390081750340c000e030a403404591202c095110800d8034100f0440d807001c3d2805450304421104002c94900c01c5078503a24142c1002c509130b0300603018107032003a00d820000003410080380380e0039010b41381c000740f15500e04100e45181700015110740c020340703411540910900c00810010700041c0e01c41c0201201080d00c6618980807c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 601863561 1250 601862311 601862347
    0x1111204150903030e0d020f030d020105071814040b030709090b06281725420903140f01110a170601170c0a030f0e0a0b06150f 56
    0x1c4000c10015902c20804243d01000c440e0741e8003000c0d19440c0c40c100060001c1061804003201c440e03007510a25822800c0941e0541c81280f217090039589002c40507250092a9868030403e1195528091001d18403001528295102101c0c4400080c12180706d560744881c0349050301d49491080c0d454042090403c501400c11012400480412201140a82c92504c11441d1403010071302400b0300286012401a0403504208000307542c8181013100042e030b084a19505400c10200d5000700d024080b081d1112543c4c0001c0451a82904c190b0b00c6641c1a4482c40c00f5000118000170780004010000262000030100d200b070aa00501c0c1020b04000e0000c04403041041c0d0700352342058000a5007000c2c20031a080d00d01707502c604807607540036200c61000402d4845a00484040100401c0c5441a0311102d0038051090038400051643d228151418002141400350300306c116010740088881a8000080705800501c141e2030f0158080e10041034008403108940034560190070184042a05200014040c0e1754010f0561750303 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 601864811 1250 601863561 601863599
    0x5091c05041d33030f0709140c03041103071809020f150f03190203100612020414060d0f0c020304051804050a08161220010c05030c0901111204 63
    0x2100b56900346510020107080c07070519205252a0300320800c1d02e143c1000003124091400003801c484510304201400c41c2c95400c1c9100300d01d000361030303c445403407210810803c10b446440b1050400e4195034460b20340d611081d5007924016490b0107090004240c6021b003010801070340c0300e00708000400da0141d00c140189a087c00c10014841c21a00c0d6100e084040a43c0071140790305280a4400c0c2c03251039041f403000e03503150340d130b03d0b1200e480b8004002c0060401700c06018504480c1c680da652a5140300c1044000d003248101d0188030703021036000b100141c0a06100d0020500c5045a0707400140303021180195408460008161f01f0041c3c000250401c414a801d0a0080140000c0000401c950610b5940c0655403282880c008151340408100075241c1910102000314058002c420b03210f01415180c00109070700b000203842440c0a80400703100d0010001403081c1c00c090080794640318656207450109031025040411480c6c10000d0441c0e010070320200034040b246400c5884400c55407a28100355105880c0c1205502e = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 601866061 1250 601864811 601864859
    0x618090a0c230a0c0f021201140a090b0112030c0507030804050f0f0609090c070b010b0904180201080c130902180f15090f0d050102160506010f0e0a05091c0504 70
    0x1030840e40d02d0000703008031142c101850401c24030541d401d182c00c0c40100604207020b54003c1800d49051110351064010070241810310300404100d64607540031408403110001c020303003424030b910014402c0c034150142c0c4020140c005e0030024010030072644c0380e0b0314124268000b1147d02e540400c0070405410000030001d100320086640d003c001c0c0d03800010440a0085604e110312846103000451060b0001e58100c0744620b8000050b400c0660312801c4c00c1d11b071a8031056146020714038001003914100050805c02d40310640c141d4581c8181d0315804403401c07958000c0c1580c0121544c9a0300005600f070114401031402ca4100000719403690b00e900300b0072440000b4004400d00801201801c0c40d4058904000c8071695a02152281c149404d4100440e0012690b20700050035503100107024068145c0440b00010210300c00d408545150303881c0c042401411100d8881ca01c910500003000c9103d80c04a42c000581c001d05090490b10f05d1846540b8001c826151501e1310700c049540020103020303000094007001c003d410310340707 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 601867311 1250 601866061 601866107
    0x70f050612041e080a02030405090a020c0c0427030915030e03042d08060f010b0c070306020c03160c0f0f05010f0e0f04020d02040e130b04020618090a0c 67
    0x402003a80344280200010449404800200e4601c004121035000e0f69411446007a191994a40043e60780d900a0003907034818904000041c500c1e031041e0080310103500c0d03088003904c0e400c2001400e12000c3e24114044050710519005281c2c0d80202003825051128000d503500c845152600045902040074484590300305828452080300740c54000044a00311160451541d040b6040501580d001500140458040d04090707000014626000511980032716411465411181d98a03900141144038070510b4400301d4000c420104080f4400c1d0780070f815600344079800c0d0381c5080c0e07a039044116100041c4804841d1030003210000d00c24a00c0c0a412100500800f480c0701403024107050019011030360f0000020104200442e40d030166440d91100942c19506c090015922101c4030411440650042d001701045040d008002904114207403000d070880907000302800b40740382c40784d80078444242e00000c0010050400d80f1000001512a0311140c2d12500c04800001034012614178014009648032614400d415610 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 601868561 1250 601867311 601867327
    0x1e1a030a0b0f0c040312081501020a02030c0411040b0406051b0d0207150203130f081011040311150a08040b091609022104210206190b01031d070f0506 66
    0x3484040d0b005454018100d80700e94a411010101d4881c0703820040ca560440f051400801d80c00c494040c1c0144171a90f00e07003040f24990001241ea40d0002e03040a98960300282c1d0880c03d90415a001000e520340301500e59160a46600c8207410b1503009034014000030300e002510182200444e0600d49070542d4080c0503144540c40024001e5965840b401955180381d048180354081c82d0081040300d100d15000c6941c1000c482d5515240c0f02001c070b00b4412600d0350300034081e610031040b042d0320031958107601144085080c14116100c9220f1411316800d440e802541c0c4030141c1c00441c13050f4006d81408159a501c6a01502c0d10346080b6510b21006000c4010551120352038112844500c01c0510a84a18003c0140ca501203041601e07001080c1c1645000015054810702c814041c0c5d6242d46140c40340c60301150368610030301d00822651188100c6001146e441548908000185690480218080145400f113410301c0708582d80c0e00d1060341c8090030010340c4d1154904200b60400d500c1000002c2104485031402d00c489 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 601869811 1250 601868561 601868573
    0x1c06050c0c030304200405090105010608010f08030315030c091302010315062c120f15010806010b07150518060703050c072a080a03170103080714011e1a030a 69
    0x20161000700005c2006822481184080040820b40c410050050145050040700d00e030003044203010340400100300400115080c200e920001003150f084100452450390b480004a19030040c0c008815418015210415190b0381c94008042c011021490384050058142c070000d002c4a840c1c142b0040700c000100d50401c03803603800c0440c119000640b40b0300f140d464545c24030180c0071f08201c441d0060f48000145610b02c01240c0000d030710788802d00d098044500c0511180d101c050100c40034484d0102d968010b8005010400070080038182061092001d030002c01c25038038110b010356404880c401080c001c582d2004802d82070030021980c12800380d08003003046040906410103144154400508460046491201041c0181c604100c0c00310006c10914506074440484542361000107006070006007210f01d400346c07500c902018503030481e9032150001c1d190084650715030003c00148506015155a03410b81d60203024100c01901c00e003100200c0c000104240120000403814400f168818041d0b032000d0904000290307 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 601871061 1250 601869811 601869817
    0x1b02040b0a1a04091a0a1223070303171b0d020415050d0c03050106080106051308070e090609010c090e04110406030606180603080f2b1401080a020d030315051c06050c0c03 75
    0x1e0002c104244001e0f181022350301e0060b182c1003648440b0300010103500c0c503a000314205082d80d100340c3d00c21145070140c00040c40c0303691060b204c40c002080301d072142c00007840c2c50b10f00034050300119203005400c03d5035075550400c0b00c2d106000d0000110f100001d80300c00c001c04e83e02c41d000d510115801c0170003031941081c60083c0141c0c814060081484400100700c1804404000e2420051805a04550b101902d945402546070780035200080a84140740c0440d00320507060045607400d10040e5104d440b000c1c584ac840b03448003003015005071405c80c070507010081962214000d83c030156006107404101e65241044813018858901c0ba0350310700515142e01400080e203868101c0707842009040415884190182c11039076070101000d41e0519001781c8001c0344890b84107940142066102c00c01d600301c000c1c0e81c0d90a02ca40c0307450b0b007a10025032000c242c03a180b6002901903800a543d200005881c80861a142c50106800010030308061044039100c0c0d08420400041d405050f600100c3d6006040c1081105802e050342d80c0 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 601872311 1250 601871061 601871069
    0x2060d0902121c170f1801021c0603030305010e0106051c020c060f01170309060417030c1b030c04021207180b040905161b0303020a02011103010b09101b02040b0a1a04091a0a 76
    0x51b0420f080da40700e003400b501601c10306103a01000a440040c07003071052004180500c411000700c0e040400000720881c0440003181207034001d0301c60b82d15064814280c10f11f0800c00031000c0098650a010020f1491020018203104044582410780554184050305055115610800c081580108500c59061b1079540030740d4216421010f20401c10548101080e0541c00761031000c66180c455500030700400d1007505c0c504414020b0950030f8941c04403956061200b42d2084030101180d1050301e201042c00c480c482e8003244c010f01403e2401e135602c0c60321521154400e90056001029058640d41800f40d84154010104148005410840a602c041d40b101e410410000719014041c5580480c84c9900d8034001c1d001400520000210b0654941e19145044059000300d101c45005400000780c0c800b40d140101d0107078038140c021001e1140302004039070800025021502d040783e0011245400012400c04040c00310f0023026411800c651074508003030a1504980c45040925084103c04211900c1922001c419030280c07 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 601873561 1250 601872311 601872331
    0x40c0905010507060905060f10060503161d0402031509010f0e010b0c010e0319020f0c01080a1d030309010902011d010f0302030705090a0324050402060d0902121c170f 73
    0x50b85140c1040401014480170141c02400b40400b0400860545440144209100c40b505030000d07070ac030304044070b1034041120381203144a44c1c00281151140038680d9040b5115900d0203442d04070604c40007140aa8000b0303200032400c24018684191b140c5420640303280584030004030f5201d02c6260009003019140c0c10310884400c0400021030500c804001c0d00300068098586d01125520b942d0780340210409903942000c03100500079901e403075040d268003240400000300e050b501e041c003a444008560008220115802c040c08011841c0c0c0042803c06101039482041d02d03000005415855000151005203240c4144000c2c152280d4484940d81e007000d9601d2544010f40390060b201d582e54401615203208901c40168890800b0100200304402c0501000f24140441c1c90016909800c03604007080c1c80d800d44000358001d0090018542c44a1141e02000060380010b0428181c1c545526a0500f082100b03c0c00b120240200840c00c0056600622441c0300c4480d400302080b002c2c504405501c603034080c0a40481d0017 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 601874811 1250 601873561 601873567
    0x909050712080409061e0803130311030a0507030b09010509060118050709180e1018080a200106091d0d0e0a1503060503010f2307090306090818040c09050105 69
    0x10310240c2000da801030019444100903a9407100040b802410070440040c1044c100300794007042d81f80020081e01c02c4c0c000c0380f8400d88a207d080d41d8950070800752000c00c1c2c507010700c121007002d030100314108280340003103005e01d07001213081c205040d1031402d5444c020005000c6521003001041313142c01172028010600071490002030b003600c40c0e900c119181c54640d40071000b0341070003066410101115600c103c900c114005c00f21003480d90798604000035540c00300c00c0382e00d1229070a04ca8801042d00d9030000c01d400c100d80c1c80d0000c01c0080d983d643c00c964213100603500040e69550761003400b44606501c02c0c1e070441a400d49410840b00108001d00355a450025620020090b808403002d50039140e0004010103000d6005056030705244840d4001c0080070507100d950301ca5820f040602420340301d80e201d07000416160002da10003501c0001d07601c1c00701c0a006001d0004020038a6400004a40f07940300c0e80c0340e014440e41a55958801c500708255600c0d1130041c110344150724010a0700c0b07a03070340c100f80c0b110300f102d4080c00e040d51 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 601876061 1250 601874811 601874813
    0x308040f080f120f06090705041707090204061d040501050a120312110d180b0c030c09040c1d04060b1c18050606031002210c0d110a090909050712 64
    0x7569020300001c0c40009000030811542c690000c110307292090200102c030b09102d07070700c4004020036036509850030004100d0402c8140503100580e408005000302c080204c4080d42d40da0b0007240c040340d105500010020b6040940084403e602c0001d01543c0320003100d00703000c40d504040025510080ca03100d03030b01403d51031810300e9041502410700500c3d0381120002c10808104802d407240b4144e0b104081c0480c0140c074100725141040c0c1d1011250f907840703030080c3d00e000169030b40c82d5a10b0010761010740340c00c030404402d0000144950b1280511030b0382004642d80d044d40e1140089500074080c0d00502494451400c04806101c10600501510702c40b00398180702865500d8a50581401803031400d0981042c940380d040380205001c00060014050007043c4c0c110790030155840c4040c0700f00d0164880980b00d56408c0941c040c0340400b0844500d0308206411a118903005107420309004540f826542844d4110300811a6400c80d42c100921400a01c3d1055043c0315109080d80e03001c0c0c4170002030150035104180c8000c030748 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 601877311 1250 601876061 601876073
    0x12011b030c020f070e090708010509060f1305070801200a120506040f0908120106080405070e0424050610030905060606210a0b0f0423041b0b1b0a0308040f 68
    0x1050054500040d20b01c0035446503c01001e080c021079070094076210b1f00c1c030001401641440340314881c80303200001d0003903078a5440b0700d42c05400e03004d0070304050305c0703d403d043c580030034014031012009210b12030002a00d00f00c1340740c2e880c10f440d0080c1c01042c000081404075185d81e0341c0015060442c00c00c0c3d104c0025403a44c0d0180020000c0032807480c44a54a45130010580030048404001c00c400980b12038000000c2c3e0740c81008032a840011113000b0200c0d0000d40d01000b0000c140e441d42c40e0040d106007070f4902d87c04044003144000000341400d8500f001e4031003003441140c0c02c1120120381c02032024541441004115103440c0e0f0348500181c0b1250040700b0020700010364046040c0c41da50413420a80c4030003520305200982c0c002500c61800000d104026104050555190038410426940c6101d9603080d080d03640158000c0101900420a0f5040c2d02c14907410450483c80308e088101a1400c2d000031030b203420380b100016211144014020649038411708150300400c0c0c002ca1440c0e48186c0c41148201452440c0c5008 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 601878561 1250 601877311 601877323
    0xf070f1101091a1303090b030606041701150506191103130b03040317040f0b19022208070e0c070311060406020a031a010516051606020c12011b030c02 66
    0x34496030751030101c000003044480b108010441c02510b41855458440c0701400c006000305000080125031019410003800282001641e84210010300803410140e4400f0700580c0090599903020440c1d640f485078101d03100c0c090650740007030481656a58106904890303054502c155161110051010707900d00c0080c00b250400868166038a106544580030ba51010405078540068a088000c90b00c040d0703914000321011b00d01e10748940d80213040000c14100720744441c961b12030050030f802c280e0ba521030b1020925801c240000e00f0141000c40310b004060703c1681b00390b0303002c072503607008040503400c110400c208000d41d1801c52500030b10390b1b02c00c0702c0e034600980c40c080e103a000c41d1040300a014003034602008280312455010b085102551f4805200f00a6081400000503407401d65482c0812002e00800502c841ca03c6481100035101e60115482d00d11309803140c4210110592180c1c0c0144c0c0800c95102007400d1074a50b04114140c1d280080c01010f591007001154804c0b00d414403c00c05076203281801c0814820001 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 601879811 1250 601878561 601878587
    0x919030c0312111209040c05090d12030c020a020d02040e030417030a03060b0903061501090e04080c011d060c070f1209091a0306010306090606150e03010b090f070f 72
    0x200c881616070302d140c0706401544502038940422180c80b542103040102040c601d42d00424020b60601e8100e1140c200300050000180090420a00b0b10544105444200201c0388040c01102c585810341124100207058440e101c041e0f000310342040c200a00140c44200b0200c2c032403a03048401145000242040d18958021540b01040c00b001c50801d41401000110003450414020381d4240446511444204518400d424040303406600190006040038540e8142a0808205140401c4407540da20502c05a010382503c040e031f03c44100140110b80c440091049440c10380014039071140c0d158082200c03c1e201d88005100c0310703501500040361005c00642136075140000d0392000c0c02c100780b1044103100031706108881c0a07400e04a0324008a034894547e0190110480c484000c00510310340e07082d50740b9000940b010340400c4030801e48554001c521051014a80075003c4140c0d0b407202441c0940c80308241c203592181412a002d4a49281448040340311910640e03880b08040c1001146000c1700881112000340070300c1 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 601881061 1250 601879811 601879823
    0x70f050c100909060b0c10051b04080115060903050a060c020307080309060f010e1909083010230109090606020d030f060e041b0e01091b090b091903 65
    0xa00e01e40ca0079000390300102641c2c0751603800c110301038507695009428821645c050030b00341e02c50b81d400f1407038000c2e42e00115800001500b0300c030035065020b6064071050b0032a80201300c03180d441e41d0202e100e000c200405031005186500d04850b59521319140c242d15407840c150050840d0307403200080c2549a0081080301c520540c016107050780c030b01d483d0840300d88460302510040d1011080900000704400d4501000e402602c8440d2444110000b40d01701e0401068000d40488500c002804208680a03206054a1075801c5545074076042110320032122030303080c0c0018960150b0b01103801301409418800b2058810304030480405c0042c06d119100181e6010140354000c80e02e403801c1080200c0c04580c040740100e0000000d40b024800400050f81000a95490340980840001054000340c04290149201c40850000c070089400d001d4551074081c00c4a40240c002c4078030240c803028a610020744c0021000c50605107841c11030700003070500786e0194940c450350080038403411482903d203c3e52108645220000c5030b20013 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 601882311 1250 601881061 601881079
    0x23040e0a05010e0609070503011401140703051b010207050a2003070801062c040305030402010c1406010f0801021903020913090f0201020106080a03050a141b150615070f050c 76
    0x800e51002a0000f4015030b10b07412103080100f04c0c90f04192041c40d026030803e480d1380c3d066030b007801080030480d48417011041c10440000403000c052030401303008000840c042d640301582c0b80c3c00b103c0d6a61002e440c500049085030710401540e0041000401c0410b00701c1e0707001a079001d03c6884d54070b50304443d041100e40964140a03105001500c510158004801c40e014844402881080000c0c0c40d880d0b8610701da6000c481c07064600c0001d00181c4124000d41d031040c03050400440981c81a260b03080b03c000c2c44014045c40707500030380041c01003800222101c001001d4500c000d500d403582c1900c14940342952400900c09040d004212036826a458103803d805d403210710007040151400c1414126151030364000142e000d9442c000000c00c2071080031034083d040c03c1d003540720f00b45050740e025000c80341c441d0b8000b2900079148013070110b220f0300c0540070211900301c10300f00c00601c10501c007102509100b900c06030900d841240d88542007400080078a09540c1d81a82107596202203210904116086c00b07200a41c4640c09003100d = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 601883561 1250 601882311 601882321
    0x3100b030a0f150602120405150f070c06090602120f0d0902040b15041a0a020304061206090e0f01060602030a0c0212011b0908070b12042603100608060406050123040e 73
    0x100e40724049403001d508881c2c02040030700202801d44548d00400f50402e604000f0351003e00c1d0400000d140450000c4602460000c064668068420554228000044c41d0000820034554100701c4422901e08034666103141603040c410403d9a44142d000c0261196100c83c4001d0540d5680d511841844402400d00340b01c0404c0d1305400c040c160710a001e401109076848080040b41c0c0704038070694040300d805da001185040d051000030f4868800301040d070f00c6103940302e0402103646e40c8180207030068030386c140008120b0111001ca43d0b86c25166103422110441d0700900c400c1d0344440c0e000300460001901074810f4900522500703191405001c1c209060015008100c900d2541c00b81e00c14040c02c211004042941c0d4025291201c2000a205504080a2121182e8049004030f03055410003918605410704c4541280a0141c0c8601290000c0300d141e400f03880d951008101d001e4200403140c0e884541141c04006840c28000003800b0007840301d80100c59100303843c0502e00341c880d0340f0080b41e002e4644407690601510f00 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 601884811 1250 601883561 601883591
    0xc0f0c150e031e040807180204050a061725050a11030309060105240d02090f130f0b010801080a0b0711060103111206040f020907030b04020712021203100b030a0f 71
    0x220000704048100c45082c141c00d0800b81000f60b81c05e45003940c000d0400c59240200d1284240320501c2000d504650070400028260380386100400181010348440200303000100c4044101d0200402c10841174200154405160040601039940c00c19203041050301d410050030122600c04151105504a01c000410710502d4500040d03c0c90484004a80c482a000450400b155800d01704102c0d01e4a4101c051140310000c641d02d03000303010a214084c05a1f160f849102000903045a03203210100e1b101a03076101c06220f81d00060180c1c2462850038200801d0551510007090b54440001c100a4000000e88020480462040f00c50903850034420301251401e50310b03420507040e95602040341d40d12450b0b80700052100351300041400362165403c04c5a01d03038070261603001c0c050b110200030040801c041d039841050945a65a10150078414011540a148280f4149019103016030602c0c0d1030b20145028000c009980e207241401205448081c034013603440340c58512a1001900d80300030072003406030408200308031a40c5 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 601886061 1250 601884811 601884817
    0x15191b2615030c191406070506330102030405040f020705240714160503041a03090736090b01090903140a090b09190b120a0c0f0c150e03 60
    0x1c1101580c03154400c1e24100130301c040c1a98034905803005070f03030410090f100d8610108500c0002c0544002d02e030000b03950386d5604180044803840070001c2a00d2042c0048007410034004180e00d008038000d038940410400207540e078061413280c0c03482070b0345800500d1048002a0140c501941e0701c58122110035800d004958049000752251183d8060180002015107104140a080000208103c10320704016651030f090440000c3c1c0060311680b008203c00588504800e4502e611021744000c5951030b81000f510a41c01d0600552054466402e91564040303a50003880c40144250042c0c800c9a41603440d1200360005000415006440b009040c0000281e00540341c0004c14050b110380e5406c4091031403c40215950b00400480d40300041004809200c0e480c0f810008050a040050404442d6500708540050710b80407604824003c98002c075152424100c2040c0716034003e0100102800f106015440090120951345a46803c01c510f041c40801408844501c0c0100f21041800c00d01642c8094804550359078 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 601887311 1250 601886061 601886101
    0x30405030a0f09121509080f07020f0402070512030405011404030c0203011506021c0302090303040305030405010f0c020906040b061c051f0807151115191b26 69
    0x1600340b0110640300e610514040781611100500d0b02c4140c00780e62541030000c10654060007485170b84c0d265900105106001520304030005050840d80e803166441400162140c410182d030040c0d00500000001480c013007400c44910342c8810f070560b100c3e62107050a034054034140003003800f8007030380005001c241903002140016090081e402440610100d20341001603402901c18800140c03c10001e0018902029020b0708031080c243c84c0250620340c00b080000e040d50f0003a407080300c95a000050800603560800c2c0700c008200214200005000d0310351300480c04031800103203440d2045548080076a580e03a290003c5e5002d2216401907644502c24440c498801001d00b6102405190085d007407003082c55203048070000554111201800300c25140c81e42504904601c1c0301c0000c180603803580c50612205040009204145040c4580c40407810b000d101c3c4446084510b40c928001401c0817860200006031076065140034016143c402060b41c0d582c020301100c0a203038480300c860f01000e4014425030700003010407180e503c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 601888561 1250 601887311 601887317
    0x19060b0f1905040518070806010602060f09030f090d15050f06040c14030a09080a0918050403021c050f070f1a10060c030212030109050a051b042702030405030a 70
    0x1008548040090240c1d040381000c0d030481c141c01062105041540040f504069092121040756002c90020350510030035070070801050f88004010451640d0401c401c6412a00814064049080018407a902d9105240c0c0740ca01001c80000c0d000700540b2900f501090650300095412101c400d007002003030251105652009084880201041c5186090b1180c200c3d08007007a25410030b101c800401c00103640e04010400030a0782d0780c0384c00c102d01140386100202281062952913001c0b080c02c010307000d01d0162150340d032413464a103810100300001c2e4000400d1000121400d201080e98010000c00700ca8a22812a14007210000843d0040c2004a24009246650301c610101c009002310610490070180c411555100114034181c000c1081e00c0c014401c90000f05c0c080d1050300e406070602400c4c0b1309154020b13400032040315900c4c010030032426031503c102d9800c554a8611000f200c1898040b440300c030300172405000020030300e0540c40d600e100b180c0651000c0b5540429402e5440e8a001c2c18030b9622500007001147c04 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 601889811 1250 601888561 601888579
    0xc06060111031801030504021801080d0f0201060e07031517010902010210090807020d0606080105070c1209030c141903060b0306100f12050307020910061205100509070219060b 77
    0x5004070200075102d8104804074100280380d01e140044011349809001a038100300c0c00701d00000d04240d54403100f406440c1880080050b41c104400042040c0310300c054a1045924110041c40f4007030754140200c2d0804d500c1c0c9004035211202c10207469200c080c5521030f40c807080303403070901c081e6038101134004e81000d9000741c0a40d070314402440310100640750048070091070700390200140b900600c4d101356031506060007100c001515a0710381c0202130840d803040d40e4034004201b03415220303020001d600c1101e8540c0001c910340210780501d5552010f032003410900800703d40420010510256846054240b000c0940065084146507583d0030002c0c001c15816036968042d008400010f8124049006100122080300b214021749134503150030001102005942110103000802000c000769962040c120b0007a2402c40c4011900d07494514064007a41060710440d200505043c1086005481200306e2400ca55080e82c00309901d96907000102d08240c09004c16140412000c0d00030014007580303500c85015049c094400d020 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 601891061 1250 601889811 601889837
    0x10b09011e1806113403080711100e04051815010602010c0903030e06030a090f0b07030b010e0105030f07180e060405011719020f03030c0a0b161e0c080c060601 70
    0x2a0400858a0a012179001c2805031400c018000c3c81c0003583c84694100704070304411108148141c0117107500c140c8502401241ea0414040b62400261405c0811a000203041c0c41e2010050440008030030410b10442c0e6a90014000c4c0e03450961614040d8200b40a4640c941d6500344c0c401d059030428020761005600e0540c458100e02e024200c24011340c1c3c0c00d80c849414802500d010412907a0009200144054507201d88500290105507207031203070740c4a41402e42880c13074414002402c407000100f01904100e0a0054860242d801104698002c50601a000346a0365030010540d072000032400c90511102803064001140f02080300e0082c0618070840b024002a40c1e11829003201c100c240c2c02e110700d240c2025000250f0406a40280e0500314409001c1e611f80041c588002800d60b000019404620f8006051590802007419013150f13000000b50a90740ca031401c4d0001c000c00b41103904c40e80d0450101543e203031060700f900924041c1c4c9415402260190746103020642c0303507150341e410b95215021607a40a5206 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 601892311 1250 601891061 601891067
    0x60b03010b010503040605100b0f070203010b01050f0f07020d050d0c110f060d050a09241d0303190e01060f030506060108150607020a120305130e06030303010b09011e1806 75
    0x4100454140e43d6a4219203550f02c90400501015202c003c10003008100020f2405801016200c145110754a103a105c2402e4010305094542d9440c0da41c1c1040380400520f2b0400c01c2c507006444458050101680d16400320b07202140038001c02c0c07035020b48030b4482d2003008218150700221004a462241c1c10a03010040c565062281d048000d0040c0c50b8442024000e90890a04175030116522410070180401e407a601c540781c7e00b41ca241905440b07890190740300c4000c56994114004c02c00f040c0f005c4103103010426420340e50142c070b0340070140149070b09121084058050b03a200d40c0140100c82c4500000b040126a20030600c036149602d4802103c0074003480001401940c041c60400b41701c0d0005104684c14506e402040002c641d00c04c4000b00e0340030519200200e12450350031401780d0f445204e03440e019980d42c0041c840480070030030340c1e020f5041c102d400c208100c0f0a031404070540e41100d86011031192514000c8005840c10848190603d0802c40c010203014005640603210003070104181100c003d0140c2c44000407 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 601893561 1250 601892311 601892321
    0x140412020c010516021c060f0c0504030f0807030903080c07030b070216032a080d0908030a09050d1712040212013b1903030c1718030c010216060b0301 66
    0x1e5808601c0501c201110721039080342680c00d0f00e00c020904041070300b1694111468000064080d01d50b80d90740c2c48010714042941c4500701144105003400d5082074610307a038010b1001d102c03160060000b80301180641c101030160601402841e0300007a0b06441e58228540d84e55640d0131070ac4280c40d05264000402d0600d0700100c1d010481c01483ea240c82012070458950904403401d01320311054603a481c1050360050070b1040303070304006000d10b94041d0001040202c00140410030079000712171550010407118001d260802c942070105c64003605c2c0c0554001140c2400e006030216046031040c00100010715185000320080990b22562085445240440300003803403d00300d520140b0b8400f41003114460f003804039207410703500c011207040c07490030f4001064480e68a5800c0070200342c44007108011202c0207008164260152405c40e00c85441d0a00150074500344040a481e07000d40043c42c1d03180d803080d4110240005008441c4d1416448009641e240341e100a20070701075101401c00d454207460245081d01e545018012 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 601894811 1250 601893561 601893583
    0x1605070e0114090c1602040e100213081b0d0b150a0608100905060a12021c0f03021c0f1d030303070504050f040203090c0105181806040e0619020708070614041202 71
    0x203500310141150700303000050a4904921085101e98182108604034600040c0070754560f4044a001603833030007541c60f150411164a40e00c0c841c2da072001d525441d89840b80b0303d0381c85641107503032181ca54a5501c002401d81806d560a10340007110040007042d8103810814080c040c0a2000d50660140d50325080003003240c50540720503a11a220303800411416800d20102c008407800101178108030840c200245501c03d5101c14201c900c07246c4428080145901400481403003419204c00e00020800810001c1414140280c10385c14843c0b01540801c2552081781d8400540c1c80103411250349080045003e40340b81c00c68441d40e4032802c2c03c19541401418540242c13030041604030300030200002040c0054480390040041c051a030412566510700c1a0340d00d0400c0205600f00103812542c1c0d080181c14041135511125041c542e6030721540510454101066080a04000600005840350202c0c50322012620036260003070200d0b400d040c0c580600d240307075104460046210312404400800d0148043c0d803521038440f4 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 601896061 1250 601894811 601894837
    0x2031503160611010b090a090515060a030b0705160309181109010804080c0141040305130f0807050f19031113020a03090b060d081605070e0114090c 65
    0x20701044102d000d10404144481d540f070001c100e89041700041140244125200010310b91200100003d000c41070089104000112240e80035501c1e12070701182d0440700382d11008101030210070029070307101e11900c16943c801e1516000f25101c140103003002040c584e03c03405840001303895002580c10409180c030640c110b500b5440e482904101c001401511010b000a00a4450003000c100759a0b212500381702e03003c1100e070080400c1e2041c403528a102c281c2c03400320080100c3c0021441200007c801d40d0754529a5115900d4541395035076040c0c0201c0480030008070340c00002c800c018000040352203100420312030155041541c52000c0d640582d400c014844084151b00c1e40c522010690600100303400300c43c00e40715403070301411142c2802c40c00000d07a401c903408820360000190b603030302e004000c0010300c4039001e40084044330890300c44c3ca001e840b1404c041c480c441d000c03005800d00050210810000f44007441c010009080558002e69503140d10441c2c41295071034641c8110a480005a50b4000300c01c1036804042c0f20305 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 601897311 1250 601896061 601896103
    0xf040c0605120c0a0c0c0602030301030c0909151a04090c1401210902030a08031303080606041505180306040f0506010b1204020f0411030c1206040b030a030c030912030302031503 78
    0x41c40c520390b0055040c0f10401c4605c04c1004007050b080ca00384002031102d40d00841e6079600d117041661200c54503030040315440d8101207511011421a020002c0000600c010000c1c04155140103044145202100d841e041401c040a01c0140490442e460007100ca224042d0000e0080fa03800444400c21500301a9440c0015903400309580314160303200e0740312144040c04580022003181c0b107082440c0c10480d0790001c0d150080e00503000300355012800b903400003000e81d4102e060900300154069001201c841c0501085404260884d0101036800f000c024103201400756071150800341400a2018803504c3c1c10b5940e4812000009251810f62045816100324002e00c0c80c4a511264200460b81c0c040b44c030300c07943c800d85510412070021148070085000b985110182d640d1070081298241d55400004c015074490707460502d2a03512505c02041c0c041ca510b40c9890049002c1542d881c041d2410650b540005949102c507040c038404040e00f5500841c02101e2044c50003010901c02020107580300c807403150121580c0390b21 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 601898561 1250 601897311 601897321
    0x2301050301090330060f18110a0e0f060706020405150c070302010507060e0607020f0d0c15090c030f03030f14070e06030c1b0c010e03030a1707090e0f040c060512 71
    0x258130101e10700c03441c03c0c2448805210303000c1d1800b51103080c0c100d0306502008000410070035004000702d007410144c0c403106100140c1b081c640c01c400c902032503c041040c840b0704802c024099880e4403100c3c000c000002c1a0f0740d15076126040c2403000350401e0007218015160100c64241145a480c103481954844600519000d0300703550044456400c4000200c40e09900c50b08041084801444000d2042c84590300410982000010300d61030031980c00202c0084c46400b190703900c041280480708035110608a200403900900e14030b000f0315022400c1d071001e0820305000c4c0e40d00301015030581040d001a40910f00c01d000f03610141c4003000c5680300954501001c94011b00c181c0d001d505090b400f560780500480c1002d4107020706010031600c0b0848590b51120280c003d03401c114150343c2c100d0300c1c1030440700050b00114142010307034201800e03e145690030312007420842030026181522640400001d4060500107108074142000d0814070f4240c19102164042e038501c0011665074400c8090f02c000c0c0307a10314a400308980320 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 601899811 1250 601898561 601898597
    0xb0a0509122a0105071a04030215010b0d05011a030612211e1201030303090c2105010c051905030405070312020f0705010e0109090b0a0923010503010903 67
    0x12034030459801407800005584004800c2c00001c0300004881c2a4030070304101040341a0381c19003064a6681405014840200071401b082c0303007800d600c1920010210341c1d40726402d040c0c2ca02200510107804851f210000031414200c48000f91200d44c0360003a0030300403641c90300081c3d04440414444141c1d141401e200241b842d06d414481c41410140c0e41d41911080d01e0340d0240e03080d00705a000b21440740c544000403a2400407200c41900701e80d1002d40e04055003804181c1459026469041c030000e0304142d2940302020600200200080c014003e000340e04c6040d14901804043c0800000c0003034801d5480c001810189501a008958140c2c510380c5100f5545601b200051f5010b40020340141e072f451080090100014501480007a100780113a0000e01004848440880c03501030390ba04040d040007201c948429259801c41c3d40e41007039510400000c02d4a80c02080840c684490560200301464100350103800c0e09281511080c505d66903078401040e5503030322402458260be0502d0380040000d00204100e60560314 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 601901061 1250 601899811 601899817
    0x7090908030403051b01020c070303120b01020d11030c1006140301060b160f02181006021f0c03020c010c050903070e0c1603090b0c06010510020a0506180703060f060302030c0a0b0a05 80
    0x61030006158416010b1700c242d0742244c11255102c96240d0001c04140281908900c80484001e0840002d002070f240c1c3c0c00000351141d5a000380380c81400700d0b4101e01c0f11404400e2050b551141920000c4655008008074408040c0081c3e100300c0340120721950031900603060600946054454641e00d0754980981c000101800d4a0f0b583c1c410f41d0100090104000140d44050080c0c01c4103c486440e00413a0074061076401007010160310038030035540241032440c0d031608a02c5607246a0705a101001814181c20507080e0302900c83c000d0320070455403800c442100c49e40c2c3c00c00098800320300d051b0115240341d51600031450343d4982c00c0d00c18440018090004025410640070403907906442032500c03001090395015503081c2d0360000c1e01c52488a4204800500440c1800d280c1d0700118143c0e48010100719200391107c58071090701504680300308114010004c00c2d00800c000803402076501c800100240e81d00300e8200002046a4082207100b030094003c110221b180c007088540986903401d41103490300b9411281560268 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 601902311 1250 601901061 601901077
    0x141002070e091501080d090f03030807031d06090601240203031603061e15050406051914070602070501050a091703070e090c360d0f12110709090803040305 68
    0x80306150142100e50b200250f4030340200403400041a01ca01403080180c25130304960004010f0510043c820008aa48100440c1d0002080e080010724070300d11407105202c9215860f070002c2c1501c83c1209200444500264250407501c4040801c050f00a540d41140c03407100fa00c1c01500016801440810080404c0341c010800c9050301d8240061051f65600246018071034020103034110040906003040000c48803100c00702222018a005440c09003000005401d41c0200030700001405545030b840d0404500035490f1031070308450181201c0e03c1d90042e1410078043c0d813150508035003650a010128010700711a025410360558030054400c50ed00030f9503000700d86a003006080c1e00c1041100d904205840d01c5000005015410ba01d09469483c88007250317444007104081c14803d40b81e14403894645110205a030b6082140104459485000b20f490410307001420600c0806006c0d003000ca0300318021507030040450154a034404041d240d5041e170720420300c4201c524072500030342a0141003002400092007a00100440 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 601903561 1250 601902311 601902313
    0x40b04020310051e2a0c120913020c10060b0705070f060f0c11091006082404020a0c080a02030307020d020f06012d0306021c06080c04021c0c0801141002070e09 70
    0x170700300d00d03450400c81d090b03507002540502e10000341c08a40e0320418002c038803101e28403803405d41c60302050402142c00105400a0009525070204124038001414807030101001078165080c00303000e440741d0840c2032561142074112068801c1500000c0c40c012804d0504040b40d003d40c5a0320741a00c1a05420344100124000132135001c3e044e109880101d64581c0001809000050000d4902d203003840fa0250005101910039000c00c5000000c00203034110030f580810101d90140c0d80540c90303200c0c04070296428160b0200040a0380c00202d00703407402c00e82c000065440390b9941e44c212024089521001e030b80300c100a801d00c0e01c03640c00c5000148111154020710703440500b0440d000c000904640c440c10a55401560002c585480d000280c0d01015284185200491807042c842004502e00e02402241d580a03d14031150146130040351f0501415001c1002d040d644010100070302c002000c1c008004d103590802d001d129484580c554000305141801d071001030465110b50010600241040c5240880c0c5000038803208003 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 601904811 1250 601903561 601903591
    0xf0e07030b1602150c092704080a030e0639030402190302060a0f02060604110711040b092d0f0f04051e1509010c0530040b04020310051e 60
    0x1940d1113040480780300b9407a0754010f075202e18007242044503640d8141c0703245604075141c40d00307079003045030310b2a010b60401d0740030800540e01c084c0103406030701926950042132050b004210400580c0082200d8603050f51a030301e03501c070148210001c2c02c070040d036501003420059904180001401424002e600740b0818402620074014140c1c0c0f03900182143d4440618900010b804803a10100c807901000816008101180e0030f02011200b0300c000750b468052048094141c600007c100000744d00e444d44507441429019200c030580f4a0b122141c61402e900001c034030a050030b500170541040040544d1501d004920a28400d0780c5621000404c0852040c050001ea46600038081d6a0701c10500490500b03070b8006500028104070a50308550080070380c0000d00031080e590412041400180c0d04c201110900012481da00ba0418844150347e0500007405c0040319420300c4400c10b11080c40300c0304194612032032080f01240c40e4500180c0c0a2003d6500940c0c074010310712600714495107500480100c05600500039114824 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 601906061 1250 601904811 601904833
    0xd0c020f0d1202072301030f020d02031003050709090314180603090703020301151d09030d06030602190e0a230604090506031603080418150303030f0e07030b1602 71
    0x120304209241c04540c03401d000b140030108680c05104041c010090040204032603c1000003001c200544020300c1030405660311100b1500710007030346c140c07440c040e5a444110f40b41c1c0340ca076907071080c11074450009856a00c03a0b444001840c201d540114000c907941696031159010100d00b00e00d4260704a2002e1024a0010050801c056101c3c20003035486451000000c00d44a440c600500d401c4070100d8000d8500400091000d000354032040350900c4a5200302c40c00c0d203007560340720161681140a0010181d51003410001c0c00003c1c008140c0203800b4850480c800c502d0412000282a82c00c40150000d440e08000c0360b032410131072469080c048441c80f000340e0040e240010301000008449a00c2608840d015507030300d005202d11410200301340e580340c0c070b0740d2840c108483c0d04607201d009250142d0710642040421200c078410701d60a06400c0700503005c1a440c0c0e0402000e41702c0c5409005000c10b40551450180382c1004002c18040c00140141203e8020100c603c00e5100c1c412403460b0503245030054015272040c0d00200c0 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 601907311 1250 601906061 601906069
    0xa110c01021c1b26030c16020d1e030801060509010905090c12010b040303030e060f04060b060913052211040209150403030f03050c04061d01210518010606020d0c020f 73
    0x915540e102d5240740b01d800445943c0c0780e860070700010880c50204024010840c003442c011040707480e07660408074050801d160350300c00aa03182102c018002d15040411692b410030020769443d46400c140f0036100d131001a078a845086580d03004400c0064001840c0007000c000340c0c18030342c0c4401e80251400075403519000a84908000d40042a806034031201130014040050580c544a0385225189040c00340410b03003001c8020920340200070b40050303c1c85594549041c2c103940c60f50112079880c0e40140000751a01c18405900c0005d0000b00d8007000c0b8200c1d00d40c1204800e4000c1140305c0d21280e80010081084543c0000348002900000320064001c4584050b55620503280320152006501c65602c0c8000354641840040c01d6440141c00200c1d030180c1404140090b980003001c194528a05150700c0020a040400480d40d0312080c22a001c15001800309aa401001c03c0d001700c0d02c5444522101e00b45001d41c0c1627618200c0d14944113190040c0c00004d0300303288091140c1e420b51706107400282808035204941d0009 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 601908561 1250 601907311 601907357
    0x10c050a0b0a0b0a0b1306050403021809010209041d06010807061205060f040603050a03090b0304080901050a021617060c130509070c150f180c06050a030603050703080a110c01021c 79
    0x5c039401c810101d840c001d01c2c07404080000c00f038070480c03a0050810b0b1070355010640d02030040e2040000c00400100285034170800754140d03500010020428020070f41b00b0440d40b2842040384511440d80d0052900100700500005407800c00c42d412030b500c2a2185400303058200c01020084e2010b45d0201b00c0180250082e40d0303d0190070059400356020780303c01510703403602402d0b80520b035000f20858038040c030800c008038a82d0403e40b14408130a080c059920703a0450030807801c5c0314038200c1401c00b800c0c0304132012800800c0c80e000c101d91072110000f00e81607500c034041c00300f21038055010800c0310500c004a00748440d0520112240e0488000c2c01c0030340c183d009907a1910000840041c0c407010903035540900c82c81092080c016800603100010840d240c0001513200c0a010300040c0c040d106c140f0000265207501030741320354000c80c01503411501b0f58030341c107890f49401000c5901140c07008000a00880440c02001d0010901e00c01141c0140c0040c4000d15407260844030b5070341040c1c0010103219228034907101d052800c100b1 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 601909811 1250 601908561 601908569
    0xc03141302270f070305011527080309030c0607022803150b010e2e14070819050a0903030c0f060c030c090602241b0a020c04050105010c050a0b0a0b0a 66
    0x4002c010701d0f20455080c550000280084109410200108003000010300c01c22012030103450709012035075640884010700440126008582681205c0001e10003402101130101c0400403000d82d8142e20425081008500175020041e5012000100072f054002e007403204141c2070f880504d440b00c1401e41e02d8450a980350f440705806807041e030326038a00d801d5940c2e0080d000044140e08032020110b10049000c40d00d007483c400316245041c080c585140350616409041d42901d01004070710280d581d41b9072403801202e40d40180c1d4042e040440c0c0c00b068801254041c4042e17075440301069603012449441e5440c102d40300721802c80140c1d543d402006601002c10788500071003d503c440c5481c0843c0d03640741c20000402d061070552100045420220a8841d6a0140400301c81014000c5001c140340f0b480d00440aa103050740726404001d0200d00060b0381900640100c0c484603845022541040b81c0c0c2e81c0c640c01940c4200100800800641244a220f030000d1404000243c2007241c40000007103030f0a4240c042045a000c0d500 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 601911061 1250 601909811 601909879
    0xb0d050307030906140a0806060c0304061101060b0c030d021e040905060f100914150a121521150c09030c0f06051b121206040c03141302 60
    0x1071001d09040e001001c05008181d00d14200c0390390b007004603a5a0b141c1c0900f402e52010001d10300c0218886584400c00d54200c88801400d69665968500b006019042c0c0f800c1e00c00a103508010002803101c1c2c20005455503810358801440c80c0507840c90320349000f94401000d50100c0c4510000c20246d003035000b4050009001185000140360404c0c204110701c0241241c0e0f0319104180206460000701da00215403812a840500f01175907400207440058808002524540e00c0c400c07000c9988140c1c0303035010021160024021108001480c401052899420b49034010342d880d096405004900c203130303d00280d1740701c1c550080c0080904032240303402240569510000300e80000e20381040910900c1030381c00c02d260041c10100d980342c40b601d18101c40039120340111440841003081110902080ea00c09010301030000e007002c021242c2d2105000003400740d4140541d8032078003d0b4944105c1d01801800783c403945080d1143e00d20280c0d003036901d60307002050603004010300300d070481c0c00d83c0c45103043ca02c0034012100e40620501 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 601912311 1250 601911061 601911067
    0x303110a23010515130c09120b010f06090f05010f03091406090111180105092106070e0102010e0705040f0f181202120301150908190201030b0f0906040e010b0d0503 72
    0x203030310600707542d806015042e0071110341c0701d140300300c2d0b03105000c1c410886015600411002d07500042a81c021031192305c00d005100480b80300004200520000b50b041e9807217204858005919140d0440d451079560190350380030904100180665801080d0401d020002c03403030f0128500d411740c1d40740540316000c2c400c0c040b4540c2c440c60610003025400e02a070106102d0701070045042240100400d02908140700f12107041c13100004040549898010300e507404071090700501090f481c5035103059903844008440c000002080c0c41c40042031580b06002d81c80441380005c005082042c20081044000d01c40b09012141031507542d06000a41141401081c0c4c4024110186841c1c1c0c00b000d092a080002031040342d0800c5401003a007d00030800400c2c00d4078152403000030400700543d07003044142c40e0b603002da4002c05558482e80b0f003003924100e4141c070b5401200f4402e27070f03060102d050050b0611000c010b0341c1041651121040001074161304141e84005880841400041007000005010ac0c54143e02c110058410707400c00 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 601913561 1250 601912311 601912373
    0xf040218010818060a020919060e0310090305031906090606031a0f030a060e03120124030c020a030c060b0a06050d0b011d130b060a0207170303100303110a 68
    0x40740d4400d030311081694900800e4400000d8944c1c959000810b03d0b803940707a000c00d1130246a00c448600c038aa0030106500311030000e4480001808006800741d2461180c450404050009413050041482440c0d264452606540f5035607803002141c8050203103114141d64401c0c001a02030101d0043c0f0004ac030207a10f001500520b001030041000f2000403200340291025204a842510002480030540d03800c0007001030701207540540f0074207503c2100481c001e005c0c1541c0c004030b030440200d5000480c0d040c140c04868a02d9880c4c507400e4040e035a40402060160b000b03252240003003801102003075000c3e4031802c000aa40e010b43c400180002100e604400e00149010401c9040c501042c8944a114102401d01902c0179841c0070080580c102d81c50110340c001d000c0d001905980401c290001008040c0007820292502b860b424029519203840c4500c10341940c0440002d07200e208080704490040c0342c00004035408a0440c2c405491106036030300c0300c0c0c00600c1a600d01001260180040652480910200c410002e00b8 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 601914811 1250 601913561 601913567
    0x130e090f1e06150315070e040603120206250c0501060b0307030c020d0305060d081624150312051317070321080610030b12060f0c070812060f04021801 66
    0xc010006546514005004101035a0006020070390140d90300f60010b01b035031440c004071840030045082c540c0160400401000f006911800c260100f44a5801c0310102c0c0d0b564849a5540e2828281600c601102d005031207600c54800c0720001c05250180001150035966903e040c20541e0040f01c00a001a664007a014002ca03818004400c102d851450144020304003a0f00054000c0700f1300c41300800203040081c903106052881c0891030b8060f900280009064000c0342a490741400e000c481444030980b4101c1d5411640d201001094140c9802907550ba0062805003c10b846507840f200c8124240140b40c100000e03403c10064039030f10300c0c9101501030b00c1864614030303040f2003546000004d482c0d03100340d904001d10701581c06080d00354000412610345141056543e015002400c0da104182d030003610501e0a40580e4100043c800d000304859426000303540d50310a480900e1f03001c0d0302401040c0310010400d1240030181d4107452070700450000c00301c81000404100180c00c0740e016010420f000c4c24150000846503030 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 601916061 1250 601914811 601914823
    0x60d021906090b0703020606060915070303050f13080405040506010e030703050703051507050d150825140306070c1b0305101407050702061c050f010e0705130e090f1e 73
    0x203e140c0409041101d02d50700070307480d0303040205410300072440403413481c07100e5032a51314048100414142e00c96880405040050103403e044070558025400c440100e0780c906000301c003e8100c0c44d00410710b5818541440d041101501015103e14100300500d1038501903545d0501552004501c1900201000b07451031a0440c141000b03091040345c8000400304110300a07030800c04032a0042d41c26400060004c10f000c2100c0c50000081d0080c2c46644a43c801d00c000452914050301c0540708018210010075540e91202041408042c50941e0903800ca030300440c5046015801d5281c10a03c10310300d81c400b1049030002030410400a0b4403e0710117a20112100740041c04034410140c801510100403000b9251084028015205410000340511000a64420400740c248100c415401441206000c0d03410003002c241c007884420f0182108900c0880089805240610700b1a00908006850b10740700c18a080010b5170000e800070003145150040006100c0300c08800d0100440800391030707140c10150a503002c1c00e80c0c6414 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 601917311 1250 601916061 601916069
    0x5030a05060604050d0b0601021c02030c0f010603032a020d0f0308071d1513030501090c08010c0c08030915090706110a05030d050903040807090902090a05160503060d02190609 77
    0x16001c00050240d0b440340080c40000ca038010041b000a0348460004030328040c0101c0b41c2c29400b601240f101e0049a90100c001c1040d4030000d4111000c07107018801041c22941603100042c00b01d07081c055101d03400d82c07a200300103884c02080341000c5506442500809d18224003204100d43e8a000149140d08054100090a802648034500b038070480400b00c00110910f0b1905080d18031500000315001e4004110204480000c0b0201e080c8007181c560764a001c1d4040c016803a070032611030071a0354021070803010500c00c072024aa020b580c0d0915800041d114810a0750010308012140c0c0501e5414804015800181600603000400104400c61030f020340180b0a2000400b480c8182c0c00142990000c500b00205803503880d00041c100241e2a158240d400380340d845940d01c150345502880c0800903481c403080e0b0185400398004c0d01d100003560b840f100980d08a0b64210344c183c4580c1c1c816001111454481e101641e480312014240103116010b58000500900c06000c4800c1038540000c424051241c0c0107071610003c0c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 601918561 1250 601917311 601917319
    0x201050118020a0917030706140105042301060e0f19091112240d060c09052d06041a07050f0a0503190e040f0509061501022a030d05030a0506 62
    0x1003c000350052036086248036128020580d41e944000440081c800c03150304d01ea00400400082d061000a01c526034001d20800340b140e440c100a40200d0400360420180b00c175100b041c0c0444aa08020003500c4203083e081d2174079013107458035500070200d80342c25140403002e4070001e5080c1d2840345825020002c1d102603001d650003141062011801180c51010850f4100d800d15801c0441c60804403000c11380f0b00c40b0460100c0d07220248001c0641880610b0780600c034240100d0390307200505900c1c0c00038041805503482c900c001c02207602e8172004928102d007507a6080d01d04014043d510b072907903d400030203400b490300e61050703496900026400100501002015200b00e0008050500c181880d201c450300c1e405950281d07203500d028071204051300f030301ca50460106500001c2040140c0d60803010300c1802884122140c02c2280705100100308100c1d0032020411100005a00910804c000c0462030007081c40d1850781c1130210200f0580300522660140140d02260280390b8a0744d44a240c52102c0d1070503a14060802405 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 601919811 1250 601918561 601918567
    0x1a0a09110409020306150712081006080106120b03032a0a0309030b0a0605220c0e03060c0c011803020c190506030f0c0c060f07180b03060d21020105011802 68
    0x400303162040c1c0d02141c2210900503280e039621808101e5454045841000303010000501004101020503005420300d503942d6402100d5503034014050a000c140e00506011400c01c100403c2514801d0b200342d00c001c1034a01e4085240302d20000460700c0e54100940c00f40b42e06070000005030340a10030200342400102000001d151a032f4468030003400d404200d010182c1042625000290a504130750481c100809000d00000e080944d8009144403e901070001540700d581003210040402d03228605c810440030001b0080e04250b101d100c0418290740c000c80c0e1200c0c00e55280d02104591100750984040168005d07000b400c80f00c4000010814086519442c190921245150511080e1a50383c10b6940c00305031004140c5180c1c9450400d402c1034081e00c248101c079480f820341005a000e40380c0500b580100c3d041d0305c032002c1da40c6401040e034110840f540981d54454000340001859441c001c000446414000c024241c11030301903403000e1401d0390f203000440016030745880042000e01f103e4009501103040103501141 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 601921061 1250 601919811 601919831
    0x41505120105011b081305040501080d1205072303011406071a0c090904120e04091e0c03020909070503070f12122006010503060a050108071707091a0a09 67
    0x35858806005003410008252100e40701e0007008640c00301e22540101d005500c0768902c22100c0300040a0740a1140154240400000c2071a0005051996151241c1744e0300b0801030b603c0800300061000501980800942102401c203041905500c0b014103a0001341c0316580f0b42c10070380c00d07890842200260500030701c0200903040215158800ca1881c10b141c07440c005446031216218454240940425070740e000101500f40001c0011204020000c640c283d1107140e400c0c1401c00400084035224013001e000014440110034107000d80d00c18600b84140b20342d0740002380700d03101d0300424150001207031411415400344806108a00d010019100140b103407143d201030260810400d119040c503040c4000b0700c85100040a400c07401d004800194241400c800800c185040c581d1000f84e56640a10619020380607480202e0b03980303c014026a4180c600ba440105002171404940c1c03402a50ba0a03200411405010400308901c3d00c503020b24074094141c6104080101d0444c4100311251610f0f5000344031051900032004 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 601922311 1250 601921061 601921087
    0x80408030a02070c0b03090a0308010905010609091d0a05030301080c0613290d330611010b0a090b01020607030c210207020306010e1902072003010b0a0308041505 71
    0x80d500040c0c0410260f15401c2d0380c503040c40720a910b0b800112210b60088200b00d0070074400102010705034003a55858503640d1303a50003410100e501c00c0c01190001010801c00b03001c9101c02c0d40101c0b60441c010016600501d58250115040104421084030190400001040540b00c200400b00c030703600c01254900e02d040020000b41c1c40150051042c80c070504031504a90550b80418024142e030541601c501c141c3c0c0314844038407040204071084901c2d005c1c40f1411044007040fa49220800c3c812200810359002542c00d010007075034075800d801010101c0350340ba4000e00c5550348626044900038440400080340c0e50800c9400a03083c02030040c48181058642104452030950005241e08000a040c841207503280440000f00c2c00b034803d00901942600c5081300010b141c102101d201807090006145028075008180c5c1d2920592180070805844203104c0620261040b100d0300920011010060000a020754140046000f2400f00e07803040c4c07034070f0401040400c0b0400c148061081c0340c6038580741603031409030108072203 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 601923561 1250 601922311 601922317
    0x100e060f21070c260a120b0d0510240302010c080d0e07050112140402011b170a02070f08060f0a24030611041d0c130b0d0b2706241306080408 62
    0x1004000c800c401b00300e4000c8180c1c1c4840d08410303025010144540b41410007a80e07511080340b404605500e031140d440c65040034500c100b90340da00752440c1080400d10390780046030801e4040105a0b82d0700810030981409001d58450011170740b41d0b0102400003d40f42400240030010040d00030950070f07041000141210550515036a40030750309003058800341018103142601183c4010300244030300841c0100381a1420f81101911000012358229a034954640000a48560441c800c0300c0e02544203d0110341c554070304400c842e91142c1c03981300c009403031500002010241540a5520340c01c400081ca0305005104640c060f8440c8421101c80c0b0314a0705140003a60100200412400415090f2600100728401d034842d08490f000c0313800c4520305458070745800364501141d010585114000d450b14007404450f04268014442d15454000405841045110415103034840100030550203403c031036603220141c04914601d1082c100a098154888607600031f40440181207401c040203003c0980100000035100c1d0080b = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 601924811 1250 601923561 601923577
    0x81b1c030f0603031e1e0315082b141b070504110a0503042108090c0306161b06050106020706030e010e030304020d06060302100e100e060f21070c26 65
    0x380d4031070a00d0901003210714260202d08000c0141846d0460014503a1581082c040728003e68a1040d40568850782141e4450043c0c034100390725a0080001c0514505815042c40c55030303000d0903d2806191083d203448010750200310301820f02d82c80b1700e060b10703c504402c01000c4041c00013a5420400202e032032400750264001c0c2c52252003000310000000b01000f081300386000313000c80f85000d034030401c090391070000d46403d608880d151142e100707000d800201f03440d0002e049400f403000054280503001881004031080b450145911140e12070300003e13000056001c0c41200d00070700d0503034080c1c003c4e40e00740f007801019140c1d50709500c031840e81451020300c00a8000305c101e0b6003159040302c44202c01540b0307103410405030610354800303580324402016074440e10b50050b000f0066800c003250184280000c1c0b0600790351102c03a2081b06c075000f0006001c0f4040700071080c00141215040c900b40e03445d02c601c0860003061203910403107004000444c50388030307001001810f8000ca405280310120303a07942040745118800c418019200 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 601926061 1250 601924811 601924847
    0x30206160305091201050118020702010e0f2107060311040305030306041e0f0f0f02190827010209041506080c0906090916020d020a030c081b1c030f060303 68
    0x1501104050103881103940000c80074205104d42508801924000d2030248a0b186d298102288410f5050f802442143d01107030381610340358004810482800940c1c54200c0326140c00000c000c04031011940f803c070703401003213801c9071000b0181c103410400300034243c84141c641ca041003442804184000b60011054950040081c2d0b0000741750500d941002c0d221419480700700e07403684c0c80c05d440c8000a4440d07400c03001910008030828462041c110219400301d110300101409884481a90442001c1c450505241c00c0186012000b20300f4140c5204400c403040c1c8110a0781045c2c1d800034400400e0708250103084807032400b511040c501c036460180f0240c00c840d00101222401000014117080c0342d40c910301911103051001c1c0202c4098a070031840c040810701e60703420301c00c058440c50304007070203203440010140d61440d03048c0d84100d0038007041c1d501c148441c1c0100281803580089207003400010b0380c00704040351030640e41d01110300030700c100840017404a6141e14048024a4100301e000d0003c607400c00807030b03e14102d8401d = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 601927311 1250 601926061 601926097
    0x70e1504140303070f0303020309150c1206010e060a111005011508040303061d070908060105030a0b150d080a0f1b1104090501051503120438070305030403080f01030206 74
    0x7030000341180303d0820020072040c900ca81c500281681540a9480303030041400b1036503100032010101ca51354400329a440a41d010400803c100c00210440a80c1c0080301030502421952620001031100e0300400751100000d034600c0d030001c00061080010140348038a41000304600e505141003c010106da20900d0018016600b0105040501c264050b03801090b81d0441c81c038090308c6483d11019007031030035074202002072840b01000c28140e07808286181284c10090041000507050b5803100c50064005110800c21150034018003429240c0810400d005403003229081e03520b0311201d2010700345040714000e040400ca4030b20182c000e40351440c0c050f00010b0b904641c030107004101c2200041c0203400111001001035003000d0078401d200c07040d860904071001046040e5119801d002846410340d0107075106458000c08005500310300c11042460004400d01d8440d1500c0c0e4600c030100541c0f4459124110407000100000100b200381540209910307003005198048a49035450b6800250300f500603c407210009100704 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 601928561 1250 601927311 601927349
    0x1030b06031015170c0a03050a1104150e0303040906060f08041707080712030506040b060f03071b060e061501031a190806010305010603050d02060f041e020603040506070e1504 77
    0x7815010030544007821503a00e207840c0c500d61490341c5e0b400142c512408039043c007001c290324020a000b0b10030725112850109040624244140d0501c05242c120b0005101d0807046111260701c00740300400290036084c80201b00342d8a803020041800026170541410800c040e410f01000800c1e4000d03c044d91100d1025081d141e0403241032002d103500c1003c0d00105950f869600140030907401d0340203203218140444040102615920501c800303032081290007000b5075400c10005500c0360103034100450341064107036103410f003d50035038881c0201d408a042d9818140d000e00100214801c464440341681c010030b1900780703c10044003110240c40d84504c0692031040421326254484469074005240040a0b4403040790500e5a607400e141d0300a05442c001985e240c05500f003200a410300028202c2d020349140100c00c4a47da96030744605003121180312041e401d6899008040c805130b0b80364406180210b000b10054030060038844006030a541c016464180148031079500c0821000d00c1e01d0a540441d45a15020a441415 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 601929811 1250 601928561 601928567
    0x4060e01170c0f0f2113080d0e0c03030708130f030b190b030706170c03060d0618121107050a0b070b130c030503130504020f1603171501030b06031015 66
    0x240e0a00c0f0000729404906092a00101c015030700302080320b801c0c0c42d174a50b140c001d200d404401b03111303401820150040000c00203a0341c041d130013030701411524016609011003d000103800c0d1b500c0100c05850843e008903000340301112400c0d4a5000b0102d000f524044646959161504074600a050480b18034846682000b5042c243d003084003d540000c054800d9540c9400c0c000e401046001a410008080e43d800255032002c29400c880c081c841c02003046000d5052543d4227406040524030b100c080510312180d00c400100141062190031040d61100c2c544d030007480d2202c0b8a054060f0f03001c20321800c80c90781d040101c0a0500708503400d0039000201d190440d6101c07503191080307008042d001003800e031000800205000c400b2015207040c1040201243c1b086986904000680c010360454034402002003180795100000f4a1044140c107109040c8003014081c000040b1000c6041200c0a09880c3c01407003007a507a80d03a00d4030600090759411654203065052020140031540b8282c0104a02c00d541d42a035809904c0c0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 601931061 1250 601929811 601929817
    0x2030402132912120d0f111b060f150303040f06022a03060a0207111005090103111e07031403090c0f030c030a080a030605040603050304060e01170c0f 66
    0x7025000610a0065880e003001212802420364010294200c9407100d0701d24000000070b0180080400520030301c01644031100f86079005041017130096617a1040c002c1d4400307a034003038490841034448805032241d144103d1040c11641120042041d82c01003010004110b924000d2540c000c6624241c024600c1c28040110307141d44559000841c091030304003400907115500013a0113809200380c0c10080c4001120700c0b462540040002c0046078103030000b6000900c04021b90380a000da4601445046210a03403000c040b4003100685942d0000107580082c0d03095803940c00d4003074404d400c5228a40d082c0340c05060071308203000381501040790022200000d041010301d8400c41c1001314148406030500c1c0d8908003100b502d61b0725842c121000d4003a50020b0008041c900e40810b40038922540900a0031001c14940c0d1942d44561212b01c4560625542c0c603c0031519460301d118034009140709800950707482e810410007605225a803203200f810005001b05040c43c01440c4491203411a100040581d12800e0103031003210240 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 601932311 1250 601931061 601931089
    0xa1a19020c0c1305040201030b090712090807020d0b010515040b091002070b0301090207050c0a3f0f21140f040911030a05010b0a02070e0c071b1401051201060302030402 74
    0x82800240300f5a2855640c1c4454050351007602d04201c90702c80401800300004080350103201060f50880a03000b85405a000750310400c0c814400c0f14030b0200540e000900340182800c0590320901044010721240c00d00403c03c0b10144103038074000303040900e0641c1008aa1244041c00c5014201c88540f1113105170003048840085e02000c3c031495269a10340c044c0c20020740000005031564498202030010314240621110309450000000700034414076089030b2048105111201408100f001054180030411403038601100b43c803401820004450383d040295064107400100e201c40e05c0800c0103035401c0364201c900d0740e00d82207606981a03115031441c02e45110b140250303444240380034200074060880384600002117100d04c00103101080300c1d98a928041615000c0c4680110250f80715203000c1c403007091802d03030303980e44500e004907860300d45a0729543e400755005142056020f0160180024414443c4094806802c6842032030440c0c28103640e903d2507072503440d040c46030106040e4000f020405540ba1101165250 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 601933561 1250 601932311 601932319
    0x312110c1f0e01110315010e01090509100302040e1005090c0d030f270e0f04030509040216061817030402032a040c020d0e0103021201030201141204050a1a19020c0c 72
    0x20319a07000b01034a503072048030030060f4a1804c25032006c040d8040c03803c011203401c047c3d642003035042c00c040c14410a202c0147c02d8500d8002a1200000166210302a004203400814054004000f41401c000b044d9100544121032542100842e54265124001661040c81d09403416407180d109076a0103681c240e000c140211014032500c1c1d416107030b00541400e08800c80315505800074007551840d00c20a49200c0648000700005c404001d00400e80c43c0503005000c101081005031012540c03245d27a1311040754003c0f404038140c07401d4104544180412440b41400340a0301203409807070b41c80c00d0307030000b81c50711120404691800d1040f03001c4050306a0450000c0f50803200030384200102e00301201c0195076050307007414103000255010300710080e551103402030f14440c01c01c0c014070031041d90070b5600642d8902011628022010004d024241c40000c1c0030007040e0042d400782002c1d040c2c0200900f0300040a0305006a03a1108450200032b03c138840008a0440701e00034044540180c5800d0300124450500c8400c4800c0381d40 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 601934811 1250 601933561 601933571
    0x4020a090c080402131503020f0604050612090c120a02060d060e04060504110a08030403060203060d0209040c0e0610020c1e03010207110301061203021b010c0804030312110c1f0e01 79
    0x1c8035801295850007a402207400c0b040d585e0f5000c1120b41520f94040750b08001c24103006040005040c1030704840030404000f440c45082c161200b0210b24150014100d4100e9090800f092001954050060035000c0f01c00b0744066a1a015140c4403550b01d40d0354101c02806150000307910580384829a00c0600905107220000704141070a00304200900010b5500351032060802120b07035400e00d0420303450001c907081400518101441c0d0b0312068020341000b803003c1d411640016801c0c0044c0d0b80d40414600c201e12603007014845a05180d41ea01c02003c1c0101158016196200355000050700003600f40001c08003155503141d81d020311602e032106449070501c000e41540c00812070400b04400d507451046618401d800802c00381d43e84402d1030030000900c640203400b40e00000c84c0c140050007500e205005c20581030402c0303251102280d40d51003071580301c6d501c258001100c4103c007030b480c040103006440c1010704034041141440080815540c1301c0344000541641c501c0500407907020018940c0083d10f0003c100c40003002 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 601936061 1250 601934811 601934831
    0x118030c02040606081b0c03040e04030216080c0a140301060e18250e07052101061704020a06030e190615090c0e0609040e0f011a12060c0304020a09 65
    0xc4403140d08141207100750f040100c0401c0a520030a81c2601c40c400201507044191241a0680e106074803c003507082e9140001c02011032842d210b4082c880c00340344a83d005144400301110720308900801c0b900a2040c81d0810718401505942c0d40c0414030980d803082c1d280c4140c2c6033408001030b00514240e4000d0200f840550100003807021854060a41c4038200005d880385100502d4a0110018501d1f09109070f00c1e10144007400250220150294488924140213140c15214030501c680706e040f981c207442814949000601c10b09074415100c202a8000c03281c0518203040ca58002010013800c0c0c020803080543c0c0b0504400144000c002a50090240c860303181c45d501c1c010305194001e08004112003130881008180080c020507188115217031400107a8a00201030f1a51080199950000b11020361150f01d039107a515070303001d041c0001034440200d64000252a2070740304844a129540e50442481a60b14149007a1280c10100f00164045820000160f03680d440c0d1000601c084425004541d950340740c144802 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 601937311 1250 601936061 601936067
    0x6110f120904060501080105060f0322060204060909050601020d080a02121509130305030a1d030310170106081009080c0f0109170918070519081602060405060c0309011803 75
    0x1545030709450511000e51540010348150030b0a1103a02d404c1002000402c00b81d01800005c6c3d40c001950600c0c0496400b007489a006a070718038100180e6540364000390410941d41c00a40b00002048008014009450a00e0001c0e4680c00c0c0c03c8000420700040308001118103071194101da0113103824a100005500b8a000500b80c5036640c40038060003240d91101059080035015820a240765060ba15140b840e914805400e002c0c01284204d084003c0d8464003802e00300d04c0505c0514418821f001081a130a8030300039107200c9500c2c0074030494036181d1504000740000c0c18080b80800c0c062424082c08999100d191034045440d100740404a40a8020704001d1204c001d07064000b04543e82c01b440352040004030044118030184a00d000d065401300303118150700403030011162001e80c0400030f400d05500381000c001103503010304000c030b202c1000035032544100481e441c00c280101030029842e200074400351500366a0290f0740c00c1d018102e503040c1d0b0030200015240510035006688241c01031450410003412600c5c002d = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 601938561 1250 601937311 601937317
    0x70e030a11040e060f13050304090f0506281719032c0f01030b041b020d0813050c06030c0705010204090f0f0c020d030b03030c01060f26060106110f12 66
    0x262149042440000c0108800a84c19000700b0200c0c3c0d103012140c540c58911300c1d104145010444950001340800a034280d61442100000b103070500002c0f606107482003c10102d04905100000110b0001c00c800544400081d0b0000c00d4850584016007060100c1d4035862030240d41403410540703826040014130070183c1c0840514102803d541c0f084000d290284213043c607804614400c6504007030358154600456200390418491700350090400180602249481644000013205080c056400700580300d1400da4007440d00c2c1c2d40b00c0c500e0048003000b4100c65840c60b888640074015613110300340200c0401ca90041c240203d582d4254000001c41d605ca5540c100c074000381c00410030100c0054075111142e01c01254a00518600e845140e000d00442084100254002d04040c0642c0d43c1510081c080c1c4440d2080034454403015114a004201005151501d600d800e0072001740300411f0032416a952112004000808a054540b10306103c00714411041c1080c1c6000e071040c1748204140300d1800c2c1d01c2e1024140d4002 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 601939811 1250 601938561 601938593
    0x25020303071b090e0a060c05070b010f1401080903121803070b07080c0c1002030a06031a150a081f0f0203180106051905040b0d080c0f150106080609070e030a 69
    0x42c21504943d24038580e07044030310b04540041c1541145840d82c0018010750b10038006540382d820928105903403600c41410b0404240c200301d1b9249a207900a0152180c004c0c0c0c501d0040300240707003a141314608a032003240c607801800715550b80a12100301103000244000c00e6041d50100d6401226209d2246062000340758070181ca00c2c0c00820900c6021402041400c0101e50a290080009181c003440010401000350f000401814015654200c0407000444003802e0103d41941480c0009240c04e00b01240360002101c2c4820310f214141c00340040081c05c40c045814400c00c00410603038080d0480e80d500100c040c00001401038a15440001040f094101c0440401008004180200105515241481f05403100e01504d2420841001006c020310b00e0590044881007501134041404071003141d550701d00c0e03908000c0c0080300903040711000070716072641000100c01c02c80f80e00c0c020318a00d501d042d00240c001203010345014010b0340f00100244c44540204240d8400c2c2c0300240844003400254213007211510910a4 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 601941061 1250 601939811 601939853
    0xa1206050a021b210a020307260703050d051012061802040e010c170c0d0504050a020a0f031407050d0b09012012010e150d06060306060611010c11032502030307 70
    0x44c0e04a14002c0b900300303072a0400b1030f5400030352514045c1c1d1204401c141c140e1110846011503101c1070000c030031102003c1c01040f4800d464003034a1345040709141007034a0004080d001d8803074590300f0402044080c10407010310385422510018001030710303070582c5180040088029401908094024034460015030202c1032030300c120381d568801c200b000042191035410640d4048503100090001f01820003055100940040c8904120343c078814040d8080703121850706a12185800082040400500a5074030b454071644110502802c400e50800d400a60b0003000d90102030601854440042c03100d80c025402003041890f1380307644002001c40802480741030b034400c0414100b0b403462040002101c400c1c04482a00034040c1c00ca11000112111080c04044a81c00e80c00351841900c4a8000021030114420080900302e50741d100742029104404050030f40d040c0c0b211001c2080a1100c1103440079001000303595285803400300c1c800e102890403000150001d10040041c2d450b000018a5404018a800e4120746480c4030340 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 601942311 1250 601941061 601941103
    0x6070c080f160b0129032e03050106050112020c0d14130f06020d020c03062a03130303240b1b030d0b2d01050f0415030f06050a1206050a021b 62
    0x84180703072100303884a600b006098240b001c264080007c45241020004828078901c000700c50083d800c1e0b1200c0f5950054501d43d6403410140620750784060240803031161402c040d464045410004c5585c2e5420448000c1000840f0740b104071255942003c64808050801e108084103440340707540708075501d843c8030b100c01521400120403410383c00840c5010000400601506050f50380080302c0303110088603900c0c1003158400e06840391042070100c2c040c3d4007132401c808a0381c4440c1003d10340a001c5418994041c4500074083c3e5825100e0f9601c03c1b0000305555202c3d81258458042c1e40300e48048106040e0905440e02000c50100840501c9a00c10011404d00f00c8850490b1688103102406089810050300000ba850f0302c2d039040d0950041c8000d02040340d04c2c8810a140643d103080c4400c0c055000c294144c00030781c8800d010a140e0030207004046c0138050884041d0804d40c5000c42c00e4290200b4440002d00c030304e0315240000c2d5071070410350559058808441c2d06e4a1a407280c554034544803004280001d103c1e210701 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 601943561 1250 601942311 601942349
    0x2a020c0f090103060902040e100e060c0304051c0e1e150412080304031b12170c0d0b0a0806040c08070e0c0909101e090e06070c080f160b01 61
    0x16038000030388040103040e800c400e90a6807510701c080d05c883c1c2c4090b6009603d0f441d940176000c404010030300194a04220004886250f25030306420000040c10064815406009000c0070410120300c49071100e134460b08101c0314003642d40c1c083e600d007881c02090f190302c042401c00c1244060803101c1d0540c4d8218086030042c0d802c607900440410346000740d000e00b886190389000581d001aa8007001590040d000c0d040c5110311111078114243c1d619500c000071600304c508201c0b000c0320913411001c20300305546010100c40303041c13a2003840e00f0464018058101045038136071500b05141d80381e0524400c0903052540607502c00e0301d40741c2816001740c00e281c46003500d288070707080b40001c8002c0110609401520140003940c60201a08208440c0c000007901480d03224800010002d01d00354601403078183c040c1030480001909281c85c0f4003404881c0b400000982c0e0360014820407122503031007000ca04050307a102d04076544446041e01030460a00480b00300c000510000d911348001c2c07119404a0b213040720751520800d8811445 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 601944811 1250 601943561 601943569
    0x301090b03061e04260d0219020a020913061b1e020307080d0207080c07080105070306060c02150309100203070504090608030711130905060a092102070312032a020c 72
    0x2c444030b040038405400814001201c008002c1c144003406680fa1726418814022a030b041d50003012a00c40710303540081c6101c4664090701c0381607140c00940c0090301d00889160042601141c0c022301c40d0b11102114000343c0200106540180065910445400e400c522030400107441100d9281c4810307000095580d1155540c0e20000031190b0355a4020384850900c1c00124008019401004084507001d07414050024154000c01085000f01400000841c0c4e82c1410000030302110920780000040120b240c0c41c00740540c5a44d41150b0750a51000c1e030041c0c1e6640c400c3c20f20741c00c00200f0036940c1070041c000014481c00c942d02074041c109035110300342e040042568a80c4042d50364465103200a1400c1707032484082d04589494240400c100000400100702121640d44283c104401100c0d40e82e24140c2d5020490b040c44816000d40f1000e10030629080380c042165100a5a24041880000c4c051410078002003040c03032180e001000420461302c04600c07107800c5110720390381e036040f04007085e0014854100341102c6458 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 601946061 1250 601944811 601944841
    0xb100803070302070501030c1407030c0b0c070209010b0310080a0c031208190b06090409140d03020a02030d020309010b1305250e010525080c0606030a0305030f090c060301090b0306 79
    0x6410780041c40c00c4c41c94400150040c10364403007000c3c00d00c01400c100000c100f2100f00103001c104d2203a175407404228828a410305407100d003d001d058a8880c203022000050700c404200c1410349a0701c100d0140c0303d54034214903440d5000c0c4c0350007544281c0150303d42882086074066081d000d4038420f503070b01c5420010300c900456003a41d048820b0200c4195801040d03400010a49c00301510010103040f551801400b140440c007500c07810316007103e9040644002000040301480441e8a84246160039803400030344010003941e81c044c00394441d800395400404100b0004c030940c001800ca180181801e507008900080e0507000702011120200c84020a04940d40d00d00c01c1c500312215400301685404070340100c00401100c86810060691101c50361038812403e01e003010401064600b8821030025540d110120030503828500b01078229800b0713500100881f40024cc10005491b0702041d0000000480d03510b181070540380c01d014603600350300700c100000042101001e5400058000105404452140c6c80b0100c07c8031000d1 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 601947311 1250 601946061 601946063
    0x12041b0f03140303060d020f01030e0303070f1103160b10080d0f0f090b0d020a020f01050c04150311030112021c050d09050d0507030318090f1a0d0215091503040b10080307 75
    0x46d5100d50740c400181b42c000d8014003005d80c10b24000406440100c01d1600d160700c151180400704564480c40905071b82d1000819030709600c548051800c00e881458080006148020700500141881d8000350a031b20040c020000201489d1301254491059000041e012080c880c0158001944070317a00004540d00807403031641110f1003500841d1034502400344040081d08071200807003c50291400401c40000300340074280c041c1c003101c58610342e0359107050b44807000020b4906d1000700749801c15046440e83c4014006482c1141c00483d089241c403145d1344005100d02c15100740c0c107001d01200358444070078401c1c009040b07140b045181d2500c030702c4151500204403e45a03d42001011580082010300009128a540c400c075605403440e800841d0381c5a02c850360a13500745030100098603584420f0300d04200680c581d80b284016043c2c0c0c0f0b0b4000c2104980204401c0d40403890465008a00000c1100c07241e1610700802030500d0030400c1c440c0c0c880c1494500b60840150030f484c8000844c0c0940000700f00c4020100c115000f032 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 601948561 1250 601947311 601947319
    0x20f1009030308070207030f0b010f21020f0a1508310f0302011103040305030a050a020a020a020f0f0a090e100e2109060a0206070810050612041b0f0314030306 70
    0x400d14550b0210b0314220002c000364114059000000006031445e140c8100140c440e100b20617196040c040754840c100025130010b0810700345200b10001100701c0940c0c0c0080d03150181c1d4002e005011140208a146d0307a41da00a8154100002c031141480b503201c456a400f44400d0503102d040624414501c540004400d03520200d0540035514007000550500e00b9000c2e80346c0309000226040301031340d070341d258682c108941c1900810b5000040109064140c0314072035002d0060703003085080c2403460000131354544040700e0007402515100320b40c0d00980c0d503400500c2c048500007400030380210f80720760402e4080e01c0140383c0300095109803420b0400000c0140a0b84840610b4100108580e10262084a0070341a40ca410412030440411404420b510b9200c010040010700e50000d001f142002074008001020041100d00c210401a900340040e550f40700880d411071500b401e840543d80c6482c2064480c00c900442e60f0f0802080c400400550020050200800c0324041c1e408030b403030300c24810b05080c0c030380c48101ca6507544 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 601949811 1250 601948561 601948577
    0x60804020a051002031204061d060f091501030803180f03070203010e010603173f1b0307140918061809060a090f060906060510140d1e0504080403020f10 67
    0xd107007242e1b460b060b8880c2c0590800300d000a011843d511041501512083ea59000001082030509440b6155504010414000c100c0441440078072102c0032b07010301006181500000c08034114a00444090109103640d40c10348006110f8000304960360750007500704070b000394204240b03403c038514180711340c40803a9000740d804031400d983c0c039140b2559940a00c0c02d501030b440c80c00840c0c400d0302c500c0c40c64041c841074070340300c101200e905d8001d1140404407004282140d60302104001801d480c4011094a070041000e080c4402c0800c0442c0f20640c80d03008072450300d6000fa6107024410154440d0912003405440c040d50020a943c0100d00003c543d1641211200000d82c00b410101e9411401580314007105402054590010941507403804241c90803041c054031015111401482245003031035001050011a05000c001082d55800100311030240c000103016a90750380d40d1040c00e400c02c4851042100344510000c000314603040c506000070350850301081c0e00170a051041118142000140c50190340007584070160 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 601951061 1250 601949811 601949827
    0x9030d1d041e0203100e0c18010e010212030f010e010807240e0607060501060f020102070c15091212020d0509091f18050109050606070f15060f060804020a05100203 72
    0xd03000144410030507410070210110403802c9407010b5401084d80e010b804e20308a1606045640385500580050700c1c0d40070421040a1910701c00d88490640303c0e0a09100601c2001e640c011f0381414214040780c00c1c030041c0041005001c102064581d41030b541007403405030300c90f6202c1c941c4580c0c8228901440c07019214080405605c0720b5820800c2d21003d556207040014099040041001900004411a10035488800500076036401084501c000402071000b1400c05000352200200910b26118261840010b0690300008611552f130a10140070b0745250182e8032162031030f002d80f181c0e007241080c030018000e0440d0100e080303200f08100e40108000400700609a164640060f0500403100e000c0b9030100074880c40056020115602c45102c540380b03400c001859071401501e0002d0b204010406072041c3c00400c250000186002c0a4406054000c3d02282d44020703e140408000e00f0b1a0304140b03880603018a0004640741d0141d51540f1851007590b01103c05a6140c040c00700001e200140c01c0c2c09070300300b480011 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 601952311 1250 601951061 601951069
    0x60e07030b18100c0315050114180a09050f101d070f09050406080c03010f0902101b0b010e07020c0306010f051504051302130b070201140a030207020a0b09030d1d 71
    0x880408802c0041d6400314201c26880f808603500c10b4802c1000c0b0303032640c4880d203410180c44d200000418081c00d0400c440344403014420a680310321110f0044260081407503001c95203035801c04034098030500500300f15605082d070003202c00000c22a541c40409104500120344100516101c1300392055000c40d41c00c003521802026500030001c3d40d141c1e010422884000282c56030b036400340394000c0141001034607002000b81c00349400d450340360500050305803c02c0b11400040e200c94141d5204003010389009045912480b103405481c20390f00e0b07406072448d0020030003c0f89120180b040c603801365180c4d0302152800c0044006141c0c80705d10902c500000c0301e203035038420859400d01150740004010b40900c06450300751200c00190b100c10071400603031800d5a0115030800002e600000800213049018140c034100280da50000300004900c171850740b80d4010100300111802c1c025010742c4c44080e4000c00d075150307107071b26206220f45980000b407440d8820320801449141d00ca02400010f40f6404003824464961000c3c80d00b40 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 601953561 1250 601952311 601952341
    0x91c18230a0602010e1b0f03060103060c020106060507150519051e01270c0c08030411010e0a0b0d09080f0c0a1211070302090603031b07091b05030403030e071d04060e07030b 76
    0x350b00020100351800c02c42c8c0e01403164a010310b01c81c05001a03400410301c2c00030308480f00b5800401c10300204200190118800d081c400780d03a500b61710804102d80d61754818030758189800740d0650342031500308414440c5d0840162000c1c400c0010507035541c840c9a90382c00004030782c0225038054043c402d48611943c1d010074039a403c40900074003281020f0316640c80c00c2c1c1e2107104992049806903034807400c4c414100415a400b07000806903507800c9a00e0b950302400c02084100340d202c1e0500501820381d5500b0400704102108060b80c000107031201515444400b000350340350310313051101c4007124558080c10700380f20003a004001d45085030310302e400180602070035a0309000301890003603c1c0a605110500c075100c0e80303102c00040b100d9604500c20148c5182403405080800761209911142c58481c260780e01030391581d9116050700d030310a405160106d04807000481035070400c10380d5001b02800e51801c80383c03205d44604400c1c095018500c130300010003801d8401c03500503032104900d00008220190080204a5070a070301502 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 601954811 1250 601953561 601953613
    0xf061113081504240e0f030c0f0705060d02090121050a060b04081b0301020d021306020709050c0a08041505090106030c09020708030718051e010206091c18230a0602010e 74
    0x175142c048031180b50f01d4862101e0300c0c0b0006610004840445040a20804e80203014410060006034140000202a8040c41d5041c505007580841c00711016840740a00400303d801c041079440d60a401c030700aa0700608022100d503000b00382041d000140240c0608100c0c0d040301e41c40d0340a81020440e50b20040c0b203132490310544a030b15640920000c4110202c61004000f40c035941950052400d02e4903101a003000d4041d4045038406140000700100700052a0498920b01140c1c83c011405a035145003000c14460007084100855140c04204015a40c055026400740c902402d443ca03515a5a41c003000140d00c698940201011020f1001c590704c280200d418017020880d13404c124103180d40385c00c00301e501440032a4040060300f01010715413405503010302003a0380014003100517280e4492042c0c041c00541e034041503410200044852118035075042da40700d0b80080c0220044a0b00c130135044401524072808c014482600c03a001005001440f00c2c0140310f248420b8000902500044400410050b401e00170780c00 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 601956061 1250 601954811 601954883
    0x8060a0b0a1b140604050f01150501140d0c030e070f03151e09050a02040b0603070f0f03020c010e0303010801060e07091202040b030105090607030b15070f061113081504 74
    0x10042e40018800c5402640080c50103008060310300c1e250404a04d810345071241421a40d16100e444d10920084606000941d50b0a081c2401890741c80d07908600c03980310b81000c946100c0d18002000d2800e3394941c11483d450b02c2000304139014952201c400a032030b1100d51000074a00b020001150680d00b09036003104158442e4015000450000d000c0070000b42c602003d0100c1d800d0300300e004403104501c2c191052000c42c0200f41ca03100c1c110304d40248090480c1414803600c5050001c01910003140038800e4044504000428000b03029072443c03050f010383c2d00d800a009005c11542001c0b0702081e285982c4070307000d22950003641c40700000c52501c406000c1104d210b02d42030360841e845441014181e1424010301c1d0080c804000204080d251015004045504058a05214034282581603140c0c218070030550300c1c09500701c00742002d41c605a14200780185903aa25001c1c0541c0d02082110030b2030a8078118030219441c0c00d043e24007101045921002c0810304850040c10a513164000101c0d04190040d050b04000d4400 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 601957311 1250 601956061 601956107
    0xc010906080a05150310090b01060c020609121c170106022d0304121104060f0f0e06040b100203070c0b1312030c021309140703080304200a0608010608060a0b0a 70
    0x1c004a818040302940c06e040858440a98008200d001100107005003654601003082c2446030303001075401e108400d1038901c16030444002d40e001490a100c4140400c102c1500081c112a100304090a40890071400000440d180000052214004600e104109003150014103140d600711254400304440c6101c04003141c403041c000858007142050701400510300480300b400c040702400f070800040e1140e603041401400d01c040010401010641194825142840b0380b2a1499856001140003803104850207603201e8034100c003a49001e074001c8020000a4024151074114a1321070842d50304a110b24000c0c1c3c1002e144141e4100070b218171800320820610301c01d1404c50501c03009600029000300015280e08a0b81c2da80d14010070410035040c852000071501d43c40a0080c0321f10350344502d40c5502000b03202802103061b19034001c009401c0107241c020005401004e0b824007035264000140951005d0242c4400700300c900c40400c945103040f07200ca40031a43d6941c5120300c1c280750b85004403607a810161031015042064 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 601958561 1250 601957311 601957351
    0x90c0423061b010c09030210050a0c1e12031404080703021e0303071115270111072f0114042d0e0f0a0209060d050405010e0c010906080a05 61
    0x20030002c00e400900a80210030880c044051282103c00b403800481c10301c1800982000162074028000040d4204e5040a80e10b6480c4400156a0000e55140c01810445240102003100340a5441004014000d80710440b0b0f01610322002c0e0101e078400d83c0d40803000042c0c80002400a07004000506041e0710030320584000d00da0300c95102c1004096444846007941011080105441e0300110b00000d50754440e00412141c071140003455030843c1e015204a092081d00341d0305240b580c08030707041e05d0a111503850003040319140800303404c0590703005441c0803942d81456a800ca440300484a87c00c6041c0b8580071180701c110700346800151604440c0040100c4440f4051000240401060320031070041003070135810401c154923070b599070b008030b02c416045201c01ca6054400c1c4058400d54152166001ba1040801a03482c126500005d0762400740c070700701800301c6061030b040004000040d001454420507a808480d002c002d10001582d907080c40d0f010b5038000450382c000143e00305400f60002900300d04c01410b900e18810f68 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 601959811 1250 601958561 601958569
    0x314041d1306050a05060306060a1a03060a0e0f0105041112180106080703140601060216031e0b0a09110f060703180506030c0a091202010516170c0a030e090c0423 71
    0x204070f615101c4580c0e20301c201b141a060a00c6069401301089442165107820450010414036420503040d95000010000600644850000b100038100b0101d4540b0107240c80d00381e48421600901800d4040e81c281030b0740007001752009040d6140c80307c81348100c85596441c0a070080f00780420716034040c4159250304002944031b0b402c2c00b80f44080d40c00380f82113010000788800c0003450724030103a00178400c55004102c81d8100c3ca11220128068907440a610704a1100140c0719035044500c60a003d803510030400280206030025901106085100c0c441c00381004503240100000e0709110042d80e50003010401850300003d00c0b40449584060004d00c500308899241c2d00803803107940041b07030350302d2000200142d0700e0400c6070008007540c01440c0031a00d00d6403800301035000030a00d0207542d041102da001810030a00401ca000840f0094001d154000c1c541c40f101050503040e52481c1003441030300070840740d10241ca000e0814240c21803082050040c100c0c60b1500d4815456070303020411a07400d040c2482001072030541d5072 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 601961061 1250 601959811 601959821
    0x503120304060c120e01061a03010501090b0d140a0608150907120206070b070c031b0c0e0c1603050d0c051e030403050c0f070303031a0d030516021c0314041d1306 71
    0x20300000001d0543c1040c91030075007408d1001c0c201a01510910040015a910009210030f03070324034044050f1101e903000b03044005081c40c581460079280451003007003420050f42d40550100c40d165000c540c21117480100c1c8111484042d120a105504804010b2146d01a01e210300b0001e94800341c4007910748151603d9140903040241c0d03200c40049e8090b0f00440c01d00d0780c001148201c40440c040720750012010b61307603065032034086442440b04151007040081e03081034495090302c07400c0c41b111b600c403410106c3c80d01d4014000d0340800b4107920b040b40b922032648052849401694404402d40e5440266203003912529029600000c2003241004170070481c81780302e45d000b8406030126000505c024a415401c600d0007800340c81d80b40c1d04100203035410040c1040c01d59201d00c0c0f0595220b41500b4070700c1e40c594007100e0047d244010310b034001c2d4105007280d12a0390702c0e40d1641d800b0324620740641e0754070034040084a030500481c41144607240c000a2007201548031072248800f40350308130300071107079980d12054255140f5003921 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 601962311 1250 601961061 601961081
    0x2070e0a050a140c04140a150903020a0b040b09040f06080d050d05010b030601020a020f0103180c17062406070c0e0403020d1e032714070503120304060c12 68
    0x1944400900001c03500da0f02811681c210001c030082d06070700c0c101600b202c480c041c1d0300c9101101d05d0b0341d800d0b100d06a15582903800241c284045c0c00014540c030303203801904805452004034010203101400065907110401580c3c1543c0e240000036150082034810800902103801d1515401662814002642c0b50100704001b5900300c0340d240c044e02c034001035003c101140c105a000400010b0708004000f0300380e0340410055002c950481c0d01030307000824803004900901030002c01c030010702d4804540a0910569100b90012070360070048100c00d43c0001c205258945034140d540328017440c211500c1d50205100d00c4207601c000b1101034100c604110442d1158101c0c0115640b018107c03000840520090560602c10520f8848042c01d1140541d9800c1c00c90400c0c515108100d0410184e560320583d07800380940d42030740c00c5007141f1203280c40c85880c10300309000702c4008440340182c5440b8810300025241070206924540040800000d421a40e90341c82e00c5014000501c00c1d50104020324091204c49045440f401d0405 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 601963561 1250 601962311 601962331
    0x109050909160806041a011505030907050a260a08030f0c0d09060e0c0f0f130e030d0506180103152a1d01030e060a0207032115060f0807080702070e 65
    0x1500303107400c10380034416040d120b80100070346110050180740c0e00d0382c142c010082c0c001d14242b0341c0c965030344281504196141d007000d0b07404003d10740001220140c1d241500405c0d4800c981607407910140c01915070f03a4001540004040e65400c1c00090341c401c0001c030103503a01036100c80e00c4510300b200c100c0c60101220401c1204403015503981d40c0c00303e160b03a010045922060815242ca6a209254400103a040482c1001d0a840780b0f0394140e0000d0328040f40c0c0c01800b07910941c58210390f120700e02c11040034040d080450b80303e40039003451010b011ba1050b5491803d8109c80d0440070070224801c100754050044c0c00c1110491242c007140140c00ba44e402d2a002000e8480707009070343d5204c0148182c60240000d81c40d2a21078038101820320f07240390031012000c03410380c3d0007100c41c400040c2c3d40e00c0e80d880d040e03d24009410070b07044055002c80b0880c20901140d0801135000f00380e00d0200640541320003080d224079038000461000610070318005101113006061454112041d0700407500360640c0d84800110807041200c9540303c0c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 601964811 1250 601963561 601963573
    0x7030516031518020f03010212250504060819060e090a03081302031f23041e030c0b0c0d020c15310f0204050403051e040501090509091608 61
    0x24860b40031000302400e00d45a60501c00300d0140c040c402000c07526050701074499001542c04040f9a83e00758126075403925800c050080e40d19042c0c1c0f40503c605045210780d441ca400754012020858030a80446064500a445504a6481d1402d0b1b44000030f0b620024080e9650b518140418100140c202187c41003202d00000c0c00398800c80c0c0386c006d1441202400403196100c11849490050350b0100310315a991021315500c40446070702001e000050500281c8220340030f243d40d0302100d501c0c82c031040328130300c224014088002c0100f9001c48101d000120080c2c040c0009100311400c400003050030307413080d40069000040341d0405008200b900c040764403160841406a20002e40f590019452107001544000d203200280d585500d2401450060040702c1c80c004414030000100d1030030480d5140f001034209802400030072091500d40390207800d41c0c0c4040481c40102d810b1005640d0418600f408a60030381e40181d4418004a152100b031100710710003d840b444041c000c41c1c3c0c08031940d880300079403d00144541070003081 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 601966061 1250 601964811 601964813
    0x12040804090527010e0a02120c0a0315050c091c031416061503020306010b030a02250b10050f0607030509040f09021008070e0d02010201090b07091805090a060e0703051603 75
    0xd00c070f0385184080d0340f05905001c008070342d84001003001c2c2a15030301a40e11000e880000d0345114200320101c101c0c1a484500c2c200c010062010303841c403980302031900040030401500c0b0441d160340c00d03004442c0801e0340003284040c6200c125000400c400d00c04c6200c0d00b0024007184014207040d50b5500101c556032036403000200940b00f4400c45024601c00403012017900741c50380e400c40d00800e480b00c205001d035000c402400004283c190f5440d504a50003000b03424500071200710903028412040c0040d880607070318540088041341c050201c0b031074440f01b2284000c01001042804905001154010381420b609102c0140101c030303225242e034003458072440345040001074181010303c10440b804600c04184000c001c190f004100032641c20030305a0420350000c4584072580c507010720040303015080c0c080008050b03003842018001082c0d000540b2800b511082c10405656804444108003161800c40760380c0e40302e07031154000c440456401d81c08400c1800c840d00580301120344035200d40d45000da007580b4110602034025002c01c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 601967311 1250 601966061 601966111
    0x7060213060513050a120308042301050109060e091e1906270c030201030b06040b130806010503030a080118020f0406050301150c0f12180e100b040b120408040905 71
    0x110144c48112900c000c040e0a0440c40091100c0c581c00003814042420086001d02500442154003448031920805410b9407940b182400f1f4002072044102682c1414804104003040c601c01c1c40c451b008600042651410b00240d0402c084c201111039a414000e03907903400201054a039262881500030100480e0051800316400010b01d0f07082e0a8040848100c20b80a0008090440c404e04482d024030b0045414076071b10300040e0f258807a030740c014165490001003615480d1300c0f4211090440d286031741506c0c06070380e0342d03001c0c140c5038424490f02c20005030080d0014012003501e00480d81c0c07040e640c5180103062030707484001c181060707000380c001c40049800440104401000c5807610320f10b0031110306e00640500c05e16591111480840640200040c0040700e008809600c18114900c001101071110b000c8079076030700c0e916a17080d441501c16406010700300304c0c00b10b5000c0d00f000884007240e031420308003881c0010b1000d1218900002a00031241004200f000151500c028060070340160707045810380d5004440c0c11181 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 601968561 1250 601967311 601967347
    0xf0c010207110f130c031107050c040b030616080a06090e1006051c030c02031218030f010e1203040501140109021c0509030a0e032d060702030405090a02070602130605 73
    0x4248111010a46103042e512013110300c1d000007a0819000c1007407802c5000a40140c0030000316145841c2010440405103c2c0004412030343d5030007604c04002181c0c2c024181521014120f40480d405c2607400c0b1900c2d03540b842908401c0e80a0180303400000c4080c0c80304a060140c82842003508002d03403040440609001e424402c40d0004d203c11146103004e01c164550b0310404540c082030160620a81d2004001036407000d201c0783d0300700d42480380084e94a40c8007107140e0615030780c61003203d03020748250903144046aa05101e00c04e140e80100004100f034400800c102d84140d80010401c035880d548480d41601c840216036600c9010700391680d00961503602c140030400c89540490401c2004901704001c7c400c1c0100040b00300c61030b110007890440d1a898484002ca03141900d94401030003032074441d03540d040003070107802d4000b07a04440310310a84d6035070b03210120b04036500d00450080036800710117007001c610002260f40c01807004511401c8050b040004071240580b401460740d11207808543c0c00a044040c00d40300c0c90003 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 601969811 1250 601968561 601968593
    0x11070c03120c030207031205161202010e0c0d0f031106040b06100f08010e0612060a0902030c010c0b01060c03090e130519170304050f06280501080307170f0c010207 72
    0x40b6088045031402503480442d0b10002d006d5098000702d03054810301c208115000560740f6203940103003240904d1702c48044400001701300015480d0162454161402150310560003000404500b256038450b100c041340f800c03400342c0890500842c0b82403980700d05414040c0900c00c902401d40f03480320380b4140c401d000c51120076240c003070100320b0401e407010180da03004190f06040d03600f925204591980d548020902840c44240c400c4000c0c480c4800300040e0b902913400000c2198800c1d010f40340c0141e1960010350701c240b56a840148404903040060242600c10300d0840000f80c080d00c1c00c45203059580180b40301211050b120a903400a0103003041050001c00c20540c0c1910740d0303051454041118036228050503c0004406050192000021034141302003000517404000c240019501c0b40c1c1003041210742c08007518a083c5002001039103000c410088107200d030f20f0498400101841c80c080301c0b07584001301c40451802615440509000c8610700c071040001a05c800070100000507034540c900e0500348012540c0c009 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 601971061 1250 601969811 601969817
    0xe09060601020c0f0306070f030b1504090f0203010b180301110c0a050606030f070902031312020601060305160903020d06151d0903090a0b0f0c0d0c1a091b0411070c0312 74
    0x68840c1c04c03a140024880c1e070241142c90a00b4200308000c0c0120003a01088007411740c0104502104d011030405200104203d0b000b15104015102c4045030240c241e010910a1040d00f0400707200d021090204c5410513640d034040200002214610500044141c0e00160988441640010740d004100070b0f00f04100b540002c411070040540e03543ca0b05056035a42d445000f500001c507004800b285210903941200c1c014030354440c2088400d85005107000759185002d00c60380b00081d0038040858042c0441c0028661070400d503a45441c0da01e402d6800744450b00074a450125941e664410348120702c05250075181d4041d00e4128079070003060294030000d001e5114050005504d582003004007501c150383d003010001c11203a40310041c0b0f4858041c40c140d0541d6001c1d00d018940d0030300484c0d40380104903a00c4145500128410040e55550081e654550243d9100c201c441c40d41c0e5a02070342040041041450b1011140d1400a0000c0b40c00138030010f64039590b030844036049034882c0c501801031003000a1501842ea03c481c1e90b20b = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 601972311 1250 601971061 601971079
    0xd0f0504080d0b01020a0b01060201050f0109140a05190f0209010f080108070e1f06030209130e07030602130f170606030d050703140d1803030510050a050402130e09060601020c 77
    0x207115420588150b0900c0b604881e590b11412507982d0080c040004040c2d0026181c0300513681d00c1d03001a0103803800b12000074500e41502e001050a8000340b158880340300030003244145035541d00c1c42100041c41d000d80880c0300916188459a1444210b0103240c04910241c000541c940141d400050000a2124a80c0d000d10900400500100034005003030b900302c9074440a41106602c60302046807503d89541d9800b4541054010045204c1d81c141e001403045060a0f6142c129a96034018020119042ca9102042075002400100086282070f0060100001100000d001c116a6aa40ba5150818591001c503080304260010300140c0350a1204d1a03214405030064128010003440042052007404401024041a00680d9031103540d400203451000300310000030048441c911400c411004a0700c0c1040300041d04010009241d15504003100d81102d0018115582150a2204120294100c2c0c501c00300e012248010004014080c80343c114028020340d0003074a0107080482c0020705000c80410584d010301c03030003 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 601973561 1250 601972311 601972313
    0x70e030307020d06020c031611181816030510140f0c0d1b021f0c09030206090409050105071d09070509091b0a090f14030d08090703020a0b0d0f0504 65
    0x310031519516811034415002c400d482c40d040380203000d0400c03005000d100101c0d40e140700d44910781c00580c503070707000d4103401e48903144003020020211038050040c6502b00007800402d41e504c0e01d50481d0341003440c0000075140e6074440d481000600640d1948240c4036903000c0541c00c4d585442c0c5200c1d503070040c0034881d40302445180400e02103900f1440605041c6110400003400c02c0c01c1140c5a22510700c1202500b0105400781d02c1150081d03503a0868069070b220030a075103150364640003092251140103801c6888005400d40342d0f8003080a01e03041061030640050b100c030402c0340018000e1060500c14540750b26100c06511003540d0380460f2202da2082140206140014024026004070503920307081000c44a21501c2d645076240f0500e03648044035406108a000324072100e40c140c01c1038a0070140d8541641c50314250303545c0c1141010760310301181d4054060300501c058240b041e110b1032105a012846c0320446610540d40d5012440c0a40076911411741c0c4000490340c014096400d0050000152103800d05020358100b03 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 601974811 1250 601973561 601973563
    0x130f05040b0102070b07060e1209091f0b07030c140106061806201606050c0c0d0807060c1710180b0f121e01090c170d18121406070e03 59
    0x10f000346500d013540806d41c0d204002d05500600550036850050391a400c414200080301c2d42c02c82501140b25070f901400040030703141c00f003e2103c0035600181030442d01501d4004940d1003540040c03c11340c100203810a1043c0411040c041c2d0f50300b1840d01000010311245803a10040031044d442604000043e402e00003040302c0c943c041000fa040b10104803107003040c3d10074406a50f2070071500070360114003c00031941c0000c61075000710180106a69610a039000c0c8a20340041042c605424500245550018070840021031002d0380302c0e150000d06030410031010810703058024000c0c0760850f2f0103100350141d820144203d03101c015690b05070f031501845c1403005024100015803c01d0300d540445000d4190030301180c8541c5820860440005c08080c410045507078a43e0886010301000c501c10b0b2038410009200045000b0315015000d442814000a01a6150070b00c03400c80b2500740025982154154100003c01c08544400f0105a2503100d9030740c03400707a1007440c0045400c20707400400740410710402807000100f40e28 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 601976061 1250 601974811 601974823
    0x70e011409010b19050706140f012111040204030c17010c360b07030306051005190c0203070e07032a0909021e040f06030f05061c0215130f05040b0102 66
    0x42c0300403011340c00200c0103d084540d4002e610b0041d240c0f40c20700300403002c80e007030f400081070007104d90f40000e205580e25502d01c20680c1440701d1000c00d03040070a1540c03001044601c0a4140031510007000036140503540d45500044038070a41180780389102401e800d201510f4240f082a1181c00070b07003084c01c200c181c20000820361816075610000110345160160854107403039182e050280c440403040c80d890300042d0500030014096801843e00611f8410403030035119003d0000d6802201d64510840010050400d040346c1410310100200e8040c0b00c1c40d01c021500c0142541c040c5e01c40d150998000031428800990500380c0385040d4000c0180d1510495201002035202300510251024680003503594141d00014204c0705001c4010320016840108010900000c40c800c00d000f21000c590301030000e240c2d682540b0003110401e03140e150b44400c84000190314003c900b00d981c00301034001801d1440d00300315141405580d60080b00c80000014241106015510b10342d035820300175103000d0720100004120000040d503113030 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 601977311 1250 601976061 601976077
    0x5010e09061906020a03110601030c061103130605072105030714040b07080a02070801060b0301050d02030c040e1c050705210c121306110627070e011409010b 69
    0x104603540000c00d80d44806041e585244030800071081c016035203c82c001d490f4000340705c0071000688180e107040549440028401c2c1070303039040107401c1c0c94240340140c1529140c03404150114640014041400c1030f4030184500c000034100d40d15456503500462910246250031440d640002c80c518134003a60b0481c0c2e2140a9951101103420400d10720301c1d50001d046854002c0e50302066031260000b400004201e854805004030304003e400300e510054444a00d182030321914041d9421807641440100180c1c900300c51558080ea0000e41620300700002000481e00b07803081011030b491950b01c055900e0620414126100880142c545070450610426070303240c0b0b0b180c0c03a0400d103525280300343c1c0c01d481d50b4441141007143c180003051011950b560584100740444c680250f001d0b8520440c4d1071200081c0031b401348e604c920700840c0c001d000e0001c3c0daa9200081c1d440700b00d0038418031203046002c64042c1901e0380c20421680a000400d01255084d858441c1ca0000205106002c601444407070740100b200f041d009042d02c1e2a0 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 601978417 1106 601977311 601977319
    0x180115052233180c17041a0915040f030e060a0206041106070206071b1a040806060d0807170d0501090507120c020c060f040518090d020705010e 63
    0x90301c01d510400c0e00c03007200042000070350b00b0389600190701c520070303410500221001c21203488001401242c00302d8611286142c141000c2c0d1a00d0289a402360802008000030b0b404420362a03440607010300020880c004520b164030806000746201c203841500904001d450f108901c400a54850741074400f564003c586180d400294200b0b90121100180c02a0803e45800b10740d40e01c0c500800700c40c0d1206a113002001c000030502c007000102d0013498a00032000641c60340c3c04c16606504113000a0300d018840c07880c1d03000a0740003c9032882078640030394200c60b8085428516080c420403178440c801208100034034103400440c28080f81e511460052403250b568034500c0c0c000c1c00c025821502e01c40c0007880503900408481c006454040c0040c52007071601880e0f1030a10350b4940200b041c0031441108042d040880c60100503d0850420140c00f0940c2d5500c001c1280c60b2030000082c02020001400f9801 = true := by decide +kernel

theorem cover : BRFrame.Cov 601798561 601978417 := by
  have h0 := BRFrame.cov_init 601798561
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601798561 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601798561 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601798561 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601798561 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601798561 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601798561 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601798561 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601798561 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601798561 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601798561 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601798561 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601798561 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601798561 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601798561 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601798561 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601798561 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601798561 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601798561 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601798561 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601798561 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601798561 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601798561 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601798561 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601798561 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601798561 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601798561 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601798561 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601798561 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601798561 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601798561 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601798561 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601798561 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601798561 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601798561 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601798561 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601798561 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601798561 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601798561 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601798561 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601798561 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601798561 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601798561 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601798561 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601798561 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601798561 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601798561 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601798561 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601798561 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601798561 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601798561 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601798561 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601798561 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601798561 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601798561 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601798561 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601798561 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601798561 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601798561 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601798561 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601798561 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601798561 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601798561 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601798561 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601798561 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601798561 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601798561 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601798561 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601798561 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601798561 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601798561 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601798561 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601798561 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601798561 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601798561 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601798561 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601798561 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601798561 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601798561 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601798561 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601798561 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601798561 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601798561 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601798561 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601798561 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601798561 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601798561 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601798561 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601798561 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601798561 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601798561 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601798561 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601798561 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601798561 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601798561 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601798561 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601798561 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601798561 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601798561 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601798561 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601798561 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601798561 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601798561 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601798561 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601798561 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601798561 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601798561 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601798561 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601798561 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601798561 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601798561 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601798561 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601798561 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601798561 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601798561 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601798561 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601798561 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601798561 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601798561 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601798561 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601798561 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601798561 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601798561 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601798561 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601798561 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601798561 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601798561 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601798561 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601798561 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601798561 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601798561 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601798561 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601798561 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601798561 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601798561 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601798561 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601798561 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601798561 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601798561 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601798561 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601798561 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601798561 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601798561 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601798561 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601798561 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 601798561 ≤ n) (h2 : n < 601978417) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
