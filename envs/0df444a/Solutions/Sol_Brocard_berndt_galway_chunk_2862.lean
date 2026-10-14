-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2862
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:58:00.046843+00:00
-- url     : https://prove2.me/submissions/50f814f9-8ca3-4f22-b537-e987a067d0e2

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 514568345 ≤ n < 514748201 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 514569595 1250 514568345 514568347
    0x7170c1e0c0a0506090a030821270106050901150c0204020a03060e0a0203060105161a010303030e060702010902030c1e0d05010e0f16092c011a010c081905 68
    0x51522492620095880c00c5000c41d40100480d2501d424210540c1c000381c40d09540152504901c3c0010400094007844002c200c3c00c000a559030400620540030317608608917400c6240e4904090902091301a01040c9802c41e0064050385491080414401d0604030350028213044c004da81780c200004150000101013105002507248070350b006a480d403004108074086500c00052481c202070300310a503400001d0481d510340d80304106200c0b042e17821109407000901500301000e604100d0340307481d01122640e254980c00351444100080100b60309038003c00c40000b00c1e041115041d03514210201d0076180c0072031000e07400d80c100e07035120030b01410059462001308082005a41c0d016040c0302c045030b0940e240b40d0003948c0c1d0ba503440c2242400c1000921924aa4144003030050481440f0009401c140400300e00c1380b10409a07590b01084c0824190b1104080c0c40015244d00c8201c0b864070741070043c0603240548080c070841c0244440d4036141c0d805202e42d1400650080f40341d9081406c10440303d202041d024007a5414000 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 514570845 1250 514569595 514569613
    0x20a0f02040e06090f0c011404090b031501060815030d140309120c0109170a0e091e0718150c140a05100e010f0e2d1e100207170c 57
    0x800c2281600440c44c0c0401000d01111040301e59017005030341c0f04180e04002a00c58078a00308504d00c001e44003903410040b80000e8607000840003e1a000023842c001e9114410340c0c00005020ba00030030a06e218240d000050640076454804240c1c45003079400903000803e0318003503544800f0300c5030000355038414034410817107440b0f9500544121032a0400c1044081581d141e0001000b0003c41c600303c905130712040240d0340d05040c0341c0e00000e00520000c03a40701d8000d49601000406058200c9904c4802e030070080703000126410110802840212100f030030007420b102000340050724825010910911b0b180316510041110b1083e540c480240004210301c1d615403050f41030000100d02d051241440c503048008001407007000c504101803d4420a58041000341d28000303207900550030110720f24044024005005046034400e008241c078020001c8408030003407040e8408000480d850440f0707000104182c404030380c841c002032104441a40b050b068010091031220940d4a00d501504018103c0701c103200041d00d014075 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 514572095 1250 514570845 514570871
    0x70b10081e1b0919020702040c0c1a010506090d170c060f09030922150f0e0108060c040312050d02030a0605090a060b090d170c010c120c020a0f0204 65
    0x41004030590310124a10503900d45100002c106a040450101042c0c070402103030040041c0c80035900400d80c58240c062110320520300034a6a040741d440c1d40c1d00500030000131101820090054140007011503200901d076038001c03c9010882c840c181251801020709140c0040401409440541031504440c004800c201c3c2064242410000e00385060b1500010551480c00d003140520030360020b080b03811150005c110000d0252a400241d0704900b0014680460601c07a00f80500c00078032502d00c1e48501405602c1001c1408007004c5548401c031080000902034590704d17200315030349450301a030340e03810303294400c0000f000024443c2c1a0010041780508200c0c0c00d01084c12107910503a48100d40c8404495621101405180340030004103801130441c400070800e10b0309056444000e0f1048005040c403d1480803c0c0c80d0400004c5041ca84005000003039941e1070314050203200d0b0103070001c041e5003000304028110300705c075000c1180304a061114050380180051030035a12180d40c070000070f101c140e80090721411400078031 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 514573345 1250 514572095 514572103
    0x606070812070302032d01030602070503090405040303020904060807050a14031009111c02012106050a0b0d06060c050705010c02011403090f060112031e020c2206090c05070b1008 78
    0xb903080351805640d80c5404e030078000700d004100785e1600c9010201030311000f404955031400c3d415a41e00030b400503590f1809080c4580346000c4c00c61403643c41424134003000b04041e4143c010344290320068806014003510340d1f0b400380e15107155000c5c03075811021050b010841c0808000700402850b034042c0c10740341119034040f220401e4400192081d034080c404c2c004084402c0c10081c4600009010700300000107500b00310b83c002050070340c1c0200004081000a40c80060303411841e8803032402002c1c01001c45103550390343c0311821a15040306250410280c901200000e229005034142401664050003070b0902c641003500640d1201d441c81030a0703040010003002d243e21f07492103030021802008104001e0480907050388a691909505070803c141042c071790410b00c80001e400a901c031a0070507203a282840c000001c280124940125644e0319684201f02d0041800b08020100c0d42d8480c0502c000d0080c0081603d6411050a44501d0301c019030005030100144d0001c5880410701075044000c4150030b0014540d40c200a500d0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 514574595 1250 514573345 514573351
    0x702060f070c14090a18121110061a0304050703030c080706020d0e0c030f1005180d08090606061303060c111209040510050a0510090305010213050f0d0b0606070812 72
    0xc0701a105203c41010318280224650190b0f800c0b00910550400144000a0f010300780001000c00c040c2d45078500403503005141804038030385000202d0320b03c0f629240e0b007140985001d01c14142c003098500e4142c0c1501c8090007c4900c103a0700400100391880c0f07540da048840070110441075601c41005c2c001140000c1c403900003020710b24940480450b0301c0c21260081410820300c0a502840b80c0d1000b524813110741d101281f2020b4268040800195607643c0c840390034112848091008042e0241c0b05544580640100d42c1900400301d185c11101e0313580d645001d2103014402c0702c40d12040f004104070208001040e5411042d0b45182500c0e07d82c5204901c580c1181c5005543c43c00c0d400110004903922001d4101071180580c030510b00364034442d1440c40d0030049510700f101c0703026031400b64101c00c1040040314040c0075200e008651050085503621902d040c0100d00a0503802914460120821101c02a02c0d1140c000005544c0107034590126854900c2000300c9940001e40844411a0034801c0504071100c8284140c4 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 514575845 1250 514574595 514574609
    0x12110a060f020c0307030b0a0f0219020715050304020105120a02091e01122906120115080a36060203090102032d04020112020904150f06030b060702060f070c 69
    0x40c00d070800401905250301e003286a4020350001c8000c2000c10600d480c0c41c1e4101c02c6004000036059040c1104002a204203180240035503c0441001240c2d680011118101c61000f00c01d4988400c200324200c80307522060390042d0002e1000d02c500c0c801c80000c82ccc5100c0d007005003541c00600d0125000003140751015004034801c040c50140318002410750701703c03003c510002c10741c2408021f45040c010052061082e482c05189105c000740d02d54000f60b4980c0307801c5074045c0003c800001d40355a500c0300607103a458a118040ca00050460000c107086100f240943d100c01440e02d4401d00078482e107800c1003c0c00b030340800034a0309110031800c250301c00301d40c05200541c010540d10001594a180c41503800c107403001c0e40400400c3c20000e4070580305012001000703072504146d091074040d50765a0300e203c0c00030181c040d600d0001d5001c2e10304009007184c184540c20080072613402c7c0004290050b610107046e801c40704168001900000100100001403900340000d08000e82c0460359682400c1c507035245c5a80d2a101500590 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 514577095 1250 514575845 514575857
    0x8070b070e31090f1419080901020d0518090c040b1c050705040602030a140f0c010207020f1e060903011b0527130b0d050607021e070e0112110a06 64
    0x780d044410100c2c610341080e0340c18024410280d40d035030350500d080703150480a01203850788804844d402800707200508202c071040d0030341082241039003016031050344485c06130390152280f0314106607141c0c02601a6003000c5802040d0504c020f501e081030048405d4010f0a80141440402010a0708506800a001410002c030751220a03040b802ca00b0504849016102034207000b810f000c10800e09900104480c0c2c108140d00d041e411203198820034042c54050038410003188000410360151040c015030142480e64001c4036080c00310652078013400300300c5401455095252200e40340010013800c00b403008003419400940005480b0040c400340e114419111041c61740020360000340d94200054801008480c10003281c14251054003910002d44072280302e90190700c40f85e489450681d100e0303544080b034aa0383e5801c5400e4403120b1600b240c5c025101da007001d040801d0030917400385a80881e88001003040a5404507401320405074223000c090314000050000464035074502070b4807140c840d158010004001c00b00340d1100 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 514578345 1250 514577095 514577149
    0x1171005090304090b240c120424080105030d030c020c03030c06010302012303010909031209030e133309060e0109060b09030c04020f2205030c09010308070b070e 71
    0x100381c2c1c84030381d0500d102e03a2001d4501104d4801291104400001d0203103000d50b80c7c020a13021a050000480d0100e102c00c03808940011848403114144400420000c1c8201040c418a241941c0184003070042ca60503074090881c00301e01d24000c0e480012045003600440b80048240c00000307143d507100c860004400d0708100010411540c120305103002c45a5043c0103da110050f044c0110940d01051140c102c01b43e465183c44814140110841d0448000a8005004401c4241806030400d80500300c62400b644003401a4403011081d8840c0c4030380c1c1c1c041100301113410304561140184150600074804e00c0003030054400208924144225030040003960a0300c1d05640c03400b12502c1c1200c0d22680901182d01c07080084580070b036804100e40c040f4890441c2c0042e124403104840c69614011161a1000c9010008c10007051201a102e040b0449400301c1c11035035210040c6040c07148000007031100511a400070b0250900142030003c3d815803100780c42ca84400e10b00c00130b00c0019000f0316102c0042e0301100c201021 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 514579595 1250 514578345 514578359
    0x219030c03020706110d18080304021c140114010506070b01260d020a03031b0f0c05070b0c070f12050d050c0c0402031509090c13020f040f0807090507080c0301171005090304 76
    0x243c40b140382201c41f0790052586003922141900d110042000b441401002c000c12201d60074084800001c0d81c000316036240b540f04074000d1034024005040708060020481000243e03074030342003085500203940f0002c4500180d18000340340c200c4030300241c4414074400c007040445194403800c2240614000071540200780c414007070b007009411100300c5240303106664a0902c4c82100b035504500c410b203000c6068505002c000b80f041c10041e08108064112144240c0000340e6400740400000c3c1d803900790307280c901e07900300250354410302c1c08516001e01da001000741d00b12421014140780501c000c2c0101403d0f1901340e40c0d0a0900e4000101282d000712605150910984c0f0811014180101c00c6036005108070300400954200c100019000361000394020304041d00040e000051201540c15200105000011004442d481d80d80c2c640e11200c1034000d03414410303e040001003e144c8682c54043c02003240c809030500e5a42060804500b41c0700c0f9425180340c0e4440c00407540b4816846100d02407103070391190702543d202c07030801e04c0c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 514580845 1250 514579595 514579601
    0x309030a1b0519030b04030333090225050a020a0e1503010c23041a07030809030901080105060906071704050f04053105030c0a12030219030c03020706110d 68
    0x24030b000f101e1a01c02e040e80780302401c180c00c00f900c3c1c00c40c1401c0040d43da1032800310054254681070519181e60103a96140b02c031006001c114249070014181e403826034480c2c001901324010356030b0500c24035401d000350408011609134140d000d60300520a598800b0a180c02260000755650311200560b4261020850100740d09a0408140e1904030000c0c04810304980c002098030b80d005503483c2d440740020348250103205009080368014580074244040310440c108400c0203603002404181c020818000c000342c1c3d00d41d000701c00c032400d0140503103400c1d5581e400d01090207070079001031080751740106081001d0030120741c0f0008600c1c50300028000b8071b95598104424000034200e100c128902850504040c46200b40c41c01285113408504502c461030074580080e040c0302261103800d030180c02e80c0070003d2421215580800c14403e05805041580301224542c0c2048049206218540212850915200050b039200381c10800740550180340160070300740d0315100c80040b50181c8225102c12400000c034802101c100780 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 514582095 1250 514580845 514580849
    0x609090609020a09140d050a060506040510030b0103030f2d0f0212070b04050319020d0e0904050a06050705040b2a161203090b07200a0f06050c0309030a1b 68
    0x40040d030802c0c881c420080c04a44e06801401044240340321900030540ba100c18041505400004499034031035907013008001480242d03405070040e41803c1c0040c0c2081d1802c07940b1011a42d00100c404490b0b807840e00c00b12030040c0400504000c1041d89518201d4040850a41c1c4542500d90001d840341e51001000142500001070440d5041d5080080c1e11080d10061009540109030000c1c4030307500955a030700d40141944900501205022540c0d6100c40111340d0025014103c100d081c4c40c1d4010080d465420051641ca040b50000d11a90090600100140311a002240c0001240c01e010b070906880b8480d0007030347c0d0000c90600d1241c445020031500c4200c0300c0c3c0e240c44119082c0c000503010200082200380c28002d86801103042129142413240b040500c141c140784000d25800c161191100b032541703010036404081a00304c0102055110200d80c2601c0c1810784002214a0300e45d40704401c91500c1c1007554030350082d40313907821940003d01552100d03071018041301404070b11a100101c2540701c0302040d1640c4100315 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 514583345 1250 514582095 514582109
    0x90103031d120d1d0301020a052104170d09021002160e0c0f1b070e090f010516030f15170d0507020d0f080904110a0f0203120105040c050706050106090906 68
    0x182229510120000c40c1d440360f43c401500d0502010280c0f03200315111640301c0c2d6a00781c1c02d584002618a01d155021015044607008074603104aa246044a1041550000e0b10080c0940c4000c204001402030500c000308107921201c800403481c45a00d4002074865041d449206c0c000d0f801c174074084164815220107100161031145510710175404e19841080e40d9000c1d0040140d2900300004001030510840140d280c02c040d88402203072380c003d459491f1409d25000c04d6039040e07446d1255210701c884000041c001c161040c480400b4400c01c8402c20b1008801038034070011400480c0350f45000480040e0100d0301300f100a0241c4104081e80c204041034800d18000358141020304206041c400c04005980300003400c540c1035080724501110a070641000d071024424511150361052801c2c1000b641c40d04004058242c00005460307038200320741604410398803403043c1c0d0950440340c2440801880140382c6a03209507240c010500d405410f01107071350344010403180c007a0011400b1130540002000340f030505004010140c100 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 514584595 1250 514583345 514583359
    0x61b0801151e050a020307080f07030e031c080c090d060e06010e040803040308071e0314160e040f06120f021f050a1215030b0412030608030703120209090103031d 71
    0x1004031484142c1e0300b18011000c02c5000a4024052482001900c1c80650800c1880703aa4910403d000450796100820445c00309444000000d282c0ca00401c50440d02c8088140c1d01c0305208501030100e8980c94018041c000000040c41201030f80d0301c44840c0e40c07900070322503d0005403609800c800035142201c164003204000c40340320b00701701c0014000801c0d42e82241d4141090702132910380b44015502480301d03122604040c05074000050f004c903403540150018002c1b0039403a041a403a00f1100c0f80c0c540090501460100d0209086030b08030341840c2d80404a0140b86610009546441d4500200702404041090780c5416141440c603065180425400134650061039652400c00d80301880035086014000c00c003401d0002c61075001544030401d0300003034480d225411400c00300d142c40f46003041c4006025039040d038440d40400f090442880c023a02c50a0b00b038401c80c100079800c1c4001560704607004074055a0321725081f07400344a0355034262603030600d0324080e6203c0e0b101d01d07000c9081c0710041880752088103d03061180710 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 514585845 1250 514584595 514584617
    0x302011e0b0913021e18071e0206090c0f0301021e0d0510210c0f1503050c0a051b031c0905010b040b0f04090309120605011a07120c061b080115 63
    0x45c551201d04a0080b400000e070300300702c0c02c0d80d000a162003100340c003040060030307a10208290b0b260300860074000217141005030036030a90004400c07a9100340849002a450b8085649071102d45812a60301d40700d004001c00151404040c7c40800200b4030314004040380c040404900e0002140c03a42c016142d02c0038214820b515890300e00701012110b034601d10b04c1c0e9140000300c1a40d86090000e0444500d000e01000c424080c0c101d80d41e80c0010101d10021408100041d140201041c258219070085030103000d0150340307840c20003110b821007265841e1070788074040765032004026a541c0c100b00f0404825440240d14070000e441102403d10f1400d444030040c11910462401204084a6031000d000d50329856040d10005a01d055900e004e5441e020380e604050003220109000b60104800c0342c010740c0c140c401c00c01444080d40e09440c40705c5114011488000d20078501d0b5048003c0c8280b10b442d440e141c2c540120000305240305803041c20803120181501c000300260007640103000f68900e88501c2c6046000528182d20164 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 514587095 1250 514585845 514585849
    0x60903030f0a0b0a080c04060f030b0c032208090a060507020a0e070207090911031606090b090a03020d03031506050f310e040c050a080c0d0302011e0b091302 69
    0x4480180540c0c4400c4815001c100d00c40b01503408440e0b254409483d5103003007070f2140302555503601c4081e0321922a40c1810004a03c00c1c949503455070803298081d029408d43d4460000e1881e10740c100800310398650200302c01c089650340c2c0041c42d414860380900c108581c3d80c403084090103030303c14194111106101c0d00b00603500046c3c581488400450b140a14655815180c40744100c1c1801484d900002840e0300b01264441441805007840501100c120700700c410184000726007e160701128070034000070607458002080f1000958000b00724101c0000d103814030383c60300c0f41e000038044244044140c00082d9181c81050081d0016075595010348403a050403418003039011601c007614850605400303003c09184c1f41c40c010b07005400ca0f00c4900008100d40704e4401c03d03115a420510910100d400351000d80c0d90709000217450400d1a0500c0070b4a490b140645942040c00c010300c082d210000c0009c4045640e10f40340642411034800c440541d00007041001b04801c00200200040040d000c0e0142065502d006040001a = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 514588345 1250 514587095 514587097
    0x60114030d0e0f130b0a090e1b1509040b060a0203071103030f1605010906020712030b0607120f2003180f0303030105010c0602040e0103060507080901060524040b0c06061002060903 79
    0x501011124940304c1c180c02442100580612040e8a030403460407103000c00c0f64404c58020340c0d4804501c00458071095108180e058200700380f164404c0e00038501c4000d13a1003203d540703002414014005000403513114040c40110b0a55842002c5102c010380010400303600300054a40141c00f6214100d000b1801c09000700f03005d414034441c41d403205141e1003005203e03400300002034211030703411034000742c0c00c548a4255040140303403650442041000280340030200d14140c5000016501199003001c94042c240c0c071810303000c0d51092441c5403140180400711000c0a07011480d0602400d0142006000e1a245c2e5a08404210b9029008048170720030211282c070804241c4000096030304490f800d103030502c21405a4140a002440b0340d4103c280c030044407000110502c034554002d18001c80e541e98421070940d0341c0110307440c00c852090003140d0b402000498000813240b80c00d82074260a6410440c41403170640e4455299409611450702164242c00007020010f03a40b4041405030340c0c000003400070749aa458113506894503 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 514589595 1250 514588345 514588369
    0x1d0402180121031407080901080919061107060c050d0b030f0d18030f03020304050f06090307060e1207032306101e0b030f01051309110d030201020705060114030d0e 72
    0x2e5040e040a40006040c86042c800c0b0755200100c801560328012030034a0309281d8070444809001c5540100070070b09140f00020a6421980035103100d00140c1140d9841e10b0203405a4100001c078610700b40038070408a44148500c0804c1d100ca5103880c0d0380ca20092500101b907906508042c0c1c4681c001c21a144e9600001041100351000d180c0740c405d80c0f100c070070300c40030b0704e840001d800241c41056502c0000080540003c010025648111403100d05c40100100300702891140e841f140d078154110020400c4124010300c4c0549d9072090007071620a01319001000f292400f0b9041e8011b580005410f000c503440050001c00000c040100d040c081d000c18170745401a440c2211407817084500c1c480c40700e440a4180d070400c0c2d6600307024040c44840c5039500d041800c000445c4a5003801183d20851401c1003108850b6428403c1e500e2255100745141d205008480801c0040b000000050301555020040940066800d101503400b07803141c01410b81051080c241411718081000e0005414400c04007401c910568580b004552 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 514590845 1250 514589595 514589639
    0xe0a0b04080619150626060d031206090e0703060c030b0d120507080d02190504150c150608030703020d08071b02120d0e011205040321061d04021801 65
    0x41e0070301d50300f45008014103240c0240302200060140c08603045500c21207040b405001040040d2185030f64a100e00640c501c242c0303a59901220186107400000d0081c807101a601c0306030880094090ba58840c80340a83d081c1d0f45148040e034020030401e20030070003141f02d08510b02c405403400b04061200b110100c0c0d9101c0560303a01401445040f004605285c0c802c4085611080c0c4c00899a901c4412204864020b50411070050030401190102400c41e544a80250b900b1a4010034000251414070842542d00040200302a41d6804122090083d85c440303500078007000b403107000010750b59141c250800908014680c402d00d420044400141700c000c9902c11010f0041c118548102c10b0902c01d54130008079071120240c42d00e80c09024000d072020103a604003070300200741007003030300c0e1800c07480d40c2c0070503220440360204c40040c0850200d0061a80d84a07003802a04085d00b600400040d900f51100c00f0f4101031100c3c1044207140c0d807181000c020440c1000a87c06103460a0707003c151500f541005112403443e105050814 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 514592095 1250 514590845 514590871
    0x3110d0e090c04031203140610050a140d02040308040f06180302120a020d03020106060905090f0c0c07030c0305030406030b09190e0703060608062d041707060203070e0a0b040806 78
    0x182e0204400c42c1218002d40e840300d8881500030000d8405000b81c104945145c440118000000f0851700f03021801d418003d02d242d45440c50b01100c482c00355101404280c3c0800a00001d009880c07403229203100070b0000e90300845825071924985130350820864101c0d00540200901c05040010081c040c24809041e01e504545820031513000d215a5840c0884024019501c550300d00c0c00f9106064043d03000d4001d9402642c0c54a0030789172500248095400150394a0090108020000d40c07146042000340c81130720f80d01c02c16100d8040c0e894850403d903d036160029a5107400000d010050a81c252107259002c0d40292000125454204035807144460702013084844c2c00c1d203503c2d014081030030a000000c042c50703008404000307071038640423026030350041243ca541c400410b1130042c0c40d03d1041c1c42c1100002010b007200b8101c80e95a1070f03580789105610807403400440c96050105000207a003030300245119070b002d5500c8000c00f070b81980800201807040d900c040800341d4208410710940c040030400603482048141a0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 514593345 1250 514592095 514592101
    0x1202130305430506180405040c0608060105070203061311130b0a12082a010e010504050105061804030c0c031727030309120a0b01031b05010306050a090504052803110d0e09 75
    0x1741c000e16030b511541c2980303c0e28060400007040700540158040e141c596441007103035950f40d0015a0039120b000c001075411b912080015404218002d06001458403400e0070100c0d02c414400801d001403e15098010002d40f107038910003040c1817509003a8000d0060003c6000c0710b55264031200c8081c42416810f0b940c40c0a0345840182c2220380003a00903d2500c00da0080103a88902c81d2080e00030041980c08460395400c140104890b0320380b03124400701d0f03070065038140d8078961543d0754151540c41c0c10800c11142d41000300380000c049040030501079800c11782102d42c5583c825003c02d1104c1d6200720351500d2555040d00c80d10304415510008140c0f200d604e000e070761a1a070b050000c6180303072801e003240c072005051301a00300000c41000100d00345485011040351180711610303201e00c01501942c000c0d0060355001100c0950400100c03456402803500203000340700381d8042030551809658590030051701381d1440d420240c030342400c250344400c0342e01c0f031800024054031800005210080c00710401500580c403c115103408 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 514594595 1250 514593345 514593367
    0x3020301230c0403081c1b0c06050a061a0307110703030c030206060d050c13020c030a270b0d05060f09181218010f2a1103010504031202130305430506 66
    0x1081100c15401003503426844c2600c50008c0541e20b0880044549070305101c007040100ea594000d400607100103540300f00c110541d05100307213030542005000c641044410950103075840001c0c409030b0042c6000b5550300e03a4800c1b41e404c0103450800013a00c0d1900030400c0d4800503001c0703480460324545c1c018048644003104a550802080a4010284006000c1c040010140c048a4100039007000951801105105001c144114401d100c0d00d1071040c11039541d810029100494420392141e90711071401080420442800347c081a942d00b0300b182e00c401030241844010100100802054410754032401600780391802514a5860704000485414180440c40a0f255000c0e40a250308800d207000e0769007c000f84440b03a003501c40044500c41c80a075001003d100550a2508043c0207891049415490f801070b142d015001d40b40081d404502c00325802d01d0030340340c04000100b00703020f0081000600014034031100e0155007130018450b02984105918002d076660312286c1c10750221840120754089442035103e203c0d1140b = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 514595845 1250 514594595 514594601
    0x21020a0501171b070803090c01090b1602010807050f030a1a0d03020a020d170c03040302041a3001020d02030906060a0513111e0705060c032a0403020301230c0403081c 73
    0x48005c0840c4408001c04c80b071920300080e1042100400d90394020340903956a00081c0d00d120300c1c6211600698040528009540204011500124545000c030300d0098210511400e6030402c8c0c0796022704a49950b10707450320100380304040c1da20150803103038041034000703940c2e01960342c00d0140300c000d0090401c90300341d01c03d01c40c036038030007040d10245c04031072590300d0201c0600241c4951160004038422881c2480c50301000d800e0040b9079014100c040c0c8101043d6035032a0718010006041c425900248500c2c0002d00c0c00c0d9202800a80804451040d02580300c2c240400305506201001300150b0082c50314610400c0b4640d1110310304410010410400251000e03090a40d0049220307031000c403198400c0b0080e07020103d04850004103e100d0080e400d8421a4a8040c092489480161007650305451a8840c00f2910141c450300d00c0040816204450719180d03895002c6800e41e040c10300d01c20481250b04080b011200c00c400c40752a4464500d03c00300d0310309400c566408401c1d004070b01108110a4000c21050507141da9a8 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 514597095 1250 514595845 514595857
    0x1209060b011409062502040c090f09091509140102130905060d03210b030703150507030e0303060f0f0a171207080a0f1704051b09060f0d080421020a0501171b 69
    0x980309022380b070b60f032007005000001c4501c60f480d50003804100008013201144105a040c2d0740c0140945443c1086240071005801000c4040d100412040002401a08244010144526925802000c1d0780c0303002030a42c22204010300441c01120f4080c51035001903440350710340e0408000c0d4498000d00441c2000244020894801c4164140c801d40201006020000600d89074080244c0424482c0307a946000c2181a50011100006a07074420310110348289841e00d401c3c1c0c0750280c042c080310704c942d9280e00003442007c019403012180318001d80081c2581d190070b000b140c240c200e84040c42460807005c1e40c0c0700c421601c150b0000404000e401c03c9807504a40c86980403101002ca1b09038410141d040c1403c0131519085080362040000c031048120041600305042c81500c03984006000d0084101500107000c005260f65100301c405000412000c540000a07003c03171742201d00c2e17855910100110610501c9070004898010700c1c103108003542150400b41000c82c0d01c1d580300300e1100299007e0260741c4c1102001d80204 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 514598345 1250 514597095 514597099
    0x203040c030b09030706051e040b09160b2d0708130806150a05041806050a020f040303020a0c05060306130e01060b0711150307080114011209060b011409062502 70
    0x42e00c14000750810010162000361300411082040d602c1e02e19441d8602000c2c003503d880b440414100080201300744c2119035603c4200c01044d2100707940c811415005a20385504141d02c0e6190206004850000e941d0f04900c007a205414040d40500d40044458580d00400c4c10040420600041c0c10041000c4040003c006000f200101e681b60705124107040450581c1c0a10789000b008e88160001e042d24007402812102c01e00c0310b91481e2041c42940381c00e005001c00400100d031176502088810424128034004100a40c041e6001e40220102440c01a180708c105038405807281206006012190fa40c0c0745031b20014283d8601c00042c11504261a5030140ca09039000003000c0c080800c0f10414018003664041403842c044566807011450921380c00218001603841c0000500c2460040c04440c41c2ca1900d510070b444141880c583d07251015408401380d4221841c200c0f00e2075103c0d10030441a50300140c000c90640e40a0780a00d041c0820180482c4036030080c0000805c00800202c43c80c00e1102000c0c115041030360300 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 514599595 1250 514598345 514598363
    0xb0418020712020a0b0603060601090605030a090b0103150507170106050c0a020a06030603020418050c09040501140703021801020f1915050a050603150c1207111501061202120a0203040c03 82
    0x1519001c0d45a161211301910b610f0301e40000160649808204071740f2411051311038040c054207001c803c9031550002091800c09a0f5a1019040464040580d00f40210700c9070750541e00345081c0759a08000d690001e440348003400110341c0c1e800307050320302441441c1c1500c1180c50b101c0e45861004100c40d280000d40034010f07401c041c50280115a0a80c10780024050341d0003074900b8070000420b1440d0500d0114001c002070460b41103424000da40d0714141c011031fa04070340158000b01c0c1c810540c4510403401c103000c3c0c61480c0803035800034000740700c2c02505a028121006c240064184448503013000e648895a848500f40b44201d0200344004000701002c0c544400303a1020400c0000e490080015001404181c1d1810701c41d11039207901c40340b0709903451002c1c0c0c070a44070702038040d0601d40002d4050070082c40c05080e4501303100e200c17205180d0180c020080d132805010254503820301540352100140190940e4805408110300400030101540713b5003120580000e070300d03d80140d8036130317070390401501c808841d800c010000c00c2 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 514600845 1250 514599595 514599623
    0x1e130c093b090c060c070509190c0c031106070f0305100e010b04063903090305060901050708010503070608011401140409290904030c0213020705070f0f0b04180207 72
    0x21100301454482e4001c20101c8440300701c4a01004080d01901d100980d055110102c00d00050a0440c60b00e0742040c44000081e802003001202c900a403080810000d001034540c50604003819480000d0401c64003803c0e01030051410000801132011440006d880309154030351011800c03404da088500c1d00205a42000c800e01541c580480c0c013030907406840340c03000142001c41d50803001c0c46031584050f84841c108005d42064000c0184840ea8440c001100b501400f1100340b0000105d1014043c40340b043c54954000529480c1c9182c001e005a80180c020501a42c80084240701e034036003181e052810758820780b8684201e1444c18004a03035080094070019845140401d001aa40071150011a07007500005c0e048400b061702c4054a641c1458007504869210161402050201c0e000d140b038584203900144c48020040c1d41000340005985c01054222150b40c01404204203916040080002601d09000d0000c0305514098840a44d806140910412000960080140c120050307040f59255a4010490718001c0 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 514602095 1250 514600845 514600949
    0x1050f16051605070914010503120a050a0e1c0f050d030c05121b0a080f09160b0c2b0816020601230a14100c150c0507021e130c09 57
    0xd1b0a118441c02807040060342c090f00790b0703108155885408a96100350800e01c045104585078200030304c140360402154000c6442d0841e885003000f01d114010122400042c03410314005240006202850007098039211512030702030752003400c882e031614804213040515229228100603c02241e03012007007103100050298022031f0059031191280310003030441031484d600e441d08a078490983d04d00740d031264401090144400e1540101030104441180100e4085c030402071035030680417480030421041550007a5075103005950181d5600e0703010b007080400f40c3c29040b0030346000c2e5482d00180154141c4120701035072940c00351000400c407480600000c1c8110f0306182d4640c4a00e420b103e19003d42c0340903400c01d1000c2c108040c003c0c07440c2c240c52a4008031000c00c084005100000510340300400c002007201c10001003002d179a5041c5461314110721780d4400780c050301c810002c211207011800ca5544100c0e040420760051301e42c10030a4201115020b0000d1841603c1c030701040c0c5031444d40d2000d4041c004450900d00c001074 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 514603345 1250 514602095 514602131
    0x6010311040b0a080f0708090a020120060109020c3003060312131406070506010312050c030409151208091e03061302010f020a0506160c1401050f160516050709 70
    0x40da0040c1724141c0c00e5110341104540580b0f045030072441c664030010304480154440c40d49041d010315000000501500221103c42c00c0400a903c0f2002d680d401056600e140001403020b8a0702c106100c0000c00f03110400894425404412041351120035000b000041040c1c0b01445442081c862408506586101f030102201281d030882c0940c4201e8607035003450b80c2407800d03d90308944807107400c20014400d981c69941c0c2c0b2500860616060420001e092114604204c2e0420261014041810300490f141880381e448040000340d540c40400014000840c1e540441c41c6041100c1001c0b03010f0350030444804031403840140740203500000300d815106602c208000c2c144804800d87c5040c2c400d0380c0d50303c144900c2c4c0504a070f40703c040d1100a4040d03000703840030072003441d070468082d12500094200705132010b0700794032034280d1807020135035281075a5110010086c0907182004120390001307044040c58854118144020100d006904074001085008013045040c4081004010001c00d2400402d01c05888102c540800c0b03 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 514604595 1250 514603345 514603351
    0x7030b28050a030b010819030c02090403030e030c010e0c03010b01050d090602120406020c0c0f0f120709090c06120c1b020a030213140c030f070c062315030a080306010311040b0a08 79
    0x4901507859001094942e82c00101c80c1701e0b406517a90318940c1e027141c003040700d800c0d03000e0811001e1543d40d0480d903200c2038051000c1e006da04043c02c000203070540043e1016080000600502d40300781d2500c0700c124101d0780c01c0005d549015580307d10014640c2410310700080248910a0000b40294178072042104119a80d0014a0340c2c1c4002030603900c5000c035250901c02110f2220b0b282943c04144c6d03901d0194142014156460317a01e15950407a00c91070f503200404811922001000d51b461a960507060100680100c0c2c2c0c0d0800300010442003058104039080200706a5005800d80580000b1415039400d540ea1084c892014640042542016100000504c00285070441003d000c0070400000101d8940642c0140c2c0c2c428600441d02d04d400d0740c0c4400c41100c040014001c1151502d40d00c003240e214240007041c05403200540035007101c011b4144251660b11044005880510940c4100000340000d02044144c07074001d1400c1c200401d000c2c1403c00282040e00554106052071100800d000c10450741c00048140 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 514605845 1250 514604595 514604609
    0x603050c0a0b0306060901020a1e03090e040b16020c1e0f04180605090a0c12170c070605031902340506011a041d060907030b28050a030b01 61
    0x40480c810306200050000c1c2c441c0c098540001d00000c0d001c2d08289001b400101c40510588161b500e40c0c3e95000159204200044050010540c40c1c0c4c0425402c19541c0d000780055183c0c0c0300712403501c0e54540c4030110004042c00b0268841c3c03082d2360902ca00801c094030114030b008102c802402c0b50741d80003a0140c1c0e050140948624403894040100742054825203800064403c032600e0b424880d61540700103404040d04040031846815021310220300c29024000c040e00d141c600c42a0380380028103000792019071030400c40c43c0c0c0d00c0041102d0a540100081c2604c102e544900300183c40e82d0700d4520548400700c0e0440c000c21928000220240001d80142a4001c5840d00203180c04201c04580070440550001c0e04005040c2e6001c907006102c14100307030302e1203900840c502c840c003891300781c89a1a0844032264003401101c0ca078054014021146001560160b000c03140d031508000a40240340043e108a04000c0380c01482080008041c07106140c82d102003000d0440601070180d510b80d24a00040f11001c00d00c5401 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 514607095 1250 514605845 514605853
    0xd06080d03091b080c100e270601080c03040210111020040510050d02040f06020604050c0405150906040912091e120b0a060e0a020d0b0901080706051c050a060305 71
    0x751007000f62a5204140d804240c0105a4804040240b02c0c0718000070540c4414001e00f80700400d82a0784280394041c1a903600ca0818183e00d9020404024030392000e803c2c18144900f000c10400c070b00508100b178962080d0119241a9210702110301960824a001451f000d9400760545190704c82e41c0d250081c1030342d014500340e40c1c9600d0f0504038003441940214041c843d4000660180204c0741c034441c00c003508089171080d900502d0130f6903403c09145114129804040540c210300204003e10100f0710401c251038100380e806102c10300e44032911681401e4000c000910659886000c22240e8803030354000c17003d056000201107000840994058100c45251103044d401040102d8142180c0c02d0034a0158101c1d47d8160750744d0041c41d450b907108601c560005100e5a800d60303580200040b12003000d1005070050075041401641d41c440d000800302034500e5095014094490030004102c000170020301c0300102d40c0135180c00e80e2541c0b2107214003580500030b015620700103400e020a01650201d141e1184080301d10030011a = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 514608345 1250 514607095 514607123
    0x30e0405150f06210901060f0e06010f0305011a0d0b0603130c0605070b0a2304111924021603030206010e01150c030f09050607060f06051503040201050d06080d0309 72
    0x90b0038404e9801c01c030b00c0e513403845990121664026010a400443e000004580c031900c5024101c0403007129840390385045010414400c455810004004140420b85424002581040c0c90050561005032801d03018220003c3d02020003240c6902444810788000e120540e64148901030101907004c07080141d030054104000000d070345020744201d030f2809600050a120310703a90500c001c0018440b880036141e500d03150000a000d8060b1009038107100b14440c0740140c03514461841407100b6580d140220b0306003103842400a00c414144104802c0c0074942ca28400d9a00c5001560228100b1440d819441d03d00e081404000c010903401043d000c2c10fa80c0d10500c03042090723989090322500b44c2a400006008a01803041080110388994195151f5400e03034280800003075500c1c0017040d155440301d03106440742603a41000043c40c50305402406d0092604031089149083c02280c40710041c400030300028140207000070b0200ca0007441d600040000d25051050b9440e070b000c07241028004d45214401210001401e0b006 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 514609595 1250 514608345 514608349
    0x6010501090b0a080f13080703080a050a0b1c02010509184002190605040911030603061f0905070804050708190303150803031008070602010501120f030e0405150f 71
    0x40e0f0381c01c00c91540c1d50b540f42c0c0d110012803400400001c0d0070700308030081c1c01a0301004694030310010508588641e0b90710500c0d00e4006000c0086400c0034200542e0a420070b180c2c00c0c819074410f545480000e44410000d0300c20a0f032440144d0b0903101e4502c4c22038004200c60041e032941d0207a20b4410b881207100301c00e240c3c504071001c0e015400900c400000064410150001034801462443d6603041c1030344003034107000b4440990f11a240f415641a841714000400c001814048041c1500884c40d1507858040b1590960030703d0360020342c46100040040c50180400104812182020f13003014006056140c0f0030840c2e802c0090008244142c1101e00307841920441c1c200158a100002e8408a00034140f0720500705c0280036034084018080e104264801d40d030488001081542082c4019406228142800100180307010111403e2140c0e50b884503007564503000040000f80c07988845007071941d40c0082d120328603200303c2c130b41550b2001e060900f06030028a40b10401c00b00a111603040384010404403640c901000e55641 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 514610845 1250 514609595 514609597
    0x411070303140f1303270f0504020c07050919051e0f090709020901050409060f03230d05091206011707091b03020c070e04080d0621110303040b040806010501090b 71
    0x500c07030341c42010710760003c3c00c441c1c0e51003550102e040c4285401d00c600c111400c041c41b100310203521044402000070310108070081d202c00d498001400e003a2400e509003082c113500c0f40d845030200e07c0303140c0c001d42c0e6400004500160140c085032615102d01c50402c075909245003500c0c0307403003091004118225a50404244a2517a04071402e1040a4000040211034102068280a5004400300c541446024000481c0780407480c055000902201000746200b18654100300c9414134191005240920341035042c0d0514a1b008600140307a8066414025901c03e240804900802d00f640750099260064400118030050011106c3e06004180c2007121960303078407070490904a4500c41c5201a02110314000140094001d4014144520070b00e01a1428a607480002c03451154044030200c0d008400021104031702d01103441224017038404030510449640c11041c080440180c9a035000e0000d100100d688c005683d410000c44000c0c2c041d41c1074030713a00c403a903962105541d441c0a000e510301003600b503003001c290b241b2100c0c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 514612095 1250 514610845 514610851
    0xe01110a0209010612091a091504030c020904020607150b01020d0e030307020906030c0a1820072604030303150509040206031305030d0c110106150f031802041107030314 74
    0x2c140c40c4a80c2d02e06603081c3e5088446985040c01030341c8910141c0040340718180d24400c2c03a580c806001c1118a8614000d82c100781001c480798102500d101d05000c0402c1d4008541102d81d0741c1a030f681e559a40b2980005440c50280c80c0004103025a031048001c2801d41c59044015021400e03001c0b85d0b034410406009860040b0328450542e09030384140100c10141c5014400b1580040003e010340b0211218a80407520181c22504100f03007003007441d012050700404520401c0300541c2d41e044804401482454002c50318801d03450080d21000c40410b00b01030b9401c01e82a0240d004115102c0d940d55a030b030ba0f00d0003a01411901c2c010b0301c0140584070b03001170b05d400d0400c1c5952103940e00074241c03451582d41c1c01070300800140b008000e845a10003408558100c60f00362040000404003a101e070b2640d4040c1c40b1086007036520320307048440b00c4541e10310601181a0001c1500c44c0c448010300f000300700702c9808110001d8500c0039800180d070090800110000744003c4000609105000703980c180103100303000100c603c10304030030f03 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 514613345 1250 514612095 514612099
    0x8031909112e0302031902070b0f09070303090e1f06020705041a2d06040f0503011b08160e180f0c04081027050313050d0507060f0507060c0e01110a02 66
    0x30b00c00c00e103807883c4a0790080d6404440505910300c03a52600000b50b040b03802c442c6040302d61005041c14080d040c100c00c002d40da0700c10f004000810354241184d81c000c3c141c0c81144218131003843c0c1c81010464810b0b181c10412517240c100ca40150300c00d036862200a41c1e44400340301e0180102c0c134150a80410b100304120041c401c0d1005400c41d0b01903002c000007080b064000a05000b00c00308001a0070082ea59081e000304024100030010800c1141803404050031950038007050107060044015860400b41c12a00e265480034142581001012500c071702543c0317040d0000e50559100d260178481f1841400140c00c4540a00883e2002201660310349451891521803402500c45a030702581d40d8000c804207a410805440210042c82001d88440c10f5185000300c0801000721440c2d0008130f9807050340c145d50118140109021182d56a1203070954980a88a403100c1c0203507000c01421b00f025152050040d421102416417001d810401c20044610061140304000240c0380001c91501d5000102c9000194031550b007a00 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 514614595 1250 514613345 514613419
    0x18062805060d02090910021305120309010e010e130203090607170f06090415020c0c10021b10020114070c1b06170907170604060b090907030803190911 66
    0x41e43c007003109428005010100b00d00c5203030180d01c2c1c41c00f41070000d06568200034418940d2a4100000c001b0010750311040001c60364001d10401050740c0c2c0c0410b0113080250300f07003400c0c11009801d02c04200d44030380350700880c20058000001c2c0308103500c00045644c425a5548c2c1d403036108210b4407000031403503101901c640700d40010680108070a490241ca00c83c3d0010f12860010b00c03062125200e05003660814154040c41d074200200d035400a00700b80d94044203040c16417000c0c08108010303850b00b0604141c65504240501d90b000c8202c0030b114002d500100710b94100c0103c0060b00d1a1084008244050f402000c41c0d4142c0400d40340c407405689600b0745000d644c0d841c4c8480300342c12000b0040c8100708400910008452048002c00200c0304203000003810b514040f04041c2c5054500360401009948408000c140130340600f80070800d0120003c900481940c1e44100d4043ea60786840003003105049007071802c400d0091800314140204034409030080703000002922080c0004003401583c5290745000d0404000d4004 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 514615845 1250 514614595 514614619
    0x207020901061404150e0a0905010605041403391c030c030c020a080d18050d0b0406111c0b0d200105040306050424020a171806280506 59
    0x80030f842940d115031051000315040c00c0d51030094588030210742e21140081045600c5d1004c0a0901c540688058816403806101d9540750200c0107116100742d215106582460710804c50040c0d4051082078510444001d035602a8a800402d094181c0c0c00050f64031125410568980642e043ca908215582c248030365a074500346951741c0b030913207811240c500100d0800c0300301710100c1c00698415011002814044d0024841000140c2020b042651a0480c40c801010361120810241ea26808030300741c0c456200b040a80c00351a1031400c040a01000140089a40c00101d19801250414011f444401222200a03c08201c0f0001071284071341d01c5500140c0f25a10300c200e02c004401001c1507090b02c0b02e00600d00f052a26680740c4a50701100d8003914115030708010102e10f441c010081d8041c044030701440590840c03030454580e10183c0300341d1740d100a03070045a94580004961840e090214140f000d459029102203103040040030300c0d441c8014100441d0807071001c034410030111040c4942d520894010b010814114 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 514617095 1250 514615845 514615847
    0x81909170a060515040504060203061804020f0103020f16080a1b0f0209060d060510050a0b0f0a0311040819150e030f0705031903050405240f0a060b0406020619020702090106 76
    0xa0080920900004d00c801149242e1502c1c4a143e04c80c6006850042c5c0346d040080400c2a4000f00c5112a84a0900c030030500c0b01580d5001220f001481c0300b401d0043c0e40e41901d0b48541c00c070780a101d031181b816801000183c0140040c403001405141d1890f42d91181100c0040c00042c80c408810030080d000d0280d500314840181030124070240c104400a1411440b943c090740d503003007954000c4404481c1681031000030401c80c00c10361001030185c00c1d0010039905001032003646482e81c0c0291070048041644030742c44021400702ca00e040301c0140040b20262148403002022007500a404201c088070009000541e840761010988101c2000c2203608002d58904641c19080b04201c1e0868041918031b40820811181000e40c10382c03240901c00a603840201741840c25040042c00d046041c1800e2040b40d5600f40d4403214110840790f81580f01c2c3e50000c15850a0300c4024a540080a1030340000b540c040c000280440c40301d03000241980302e0940e000c100d80032814803460580a038042d44500039009182d07000144445 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 514618345 1250 514617095 514617101
    0x60106030f05010623090301020406120e1f0f140903031506090a12021305160206060105160b131407050a0909170304170a050a030b030609060c0f07081909170a06 71
    0x85c602110301c1c0c01c1c040d0340c100003400c83e4059400301c00400c0560349114419502c038015850081e0b000c6018210b0070789244043c070b80744000e00d6040b00c04c96580740000030702d0552540c00a4450904a07450301410320740302d0300b01a0b07294030603504c080c038254400b141600c0c14074000e811607054004c06000405000e1415101c070f51040c500c51812030f800801a264000002c14070300c1607a11840c203c081b100e5109060400181c01c28002402560400104101d8010410b2640b5042d5820a43c0060100d5040d5207641410307410384d5407020010074030a00d8001c46111000006a404203461701240e014801e250350f011300c482190001c5400404450300800c4982104801c1000f440c0c1c01405699509059101040d69070103d50103000603402041c804a03a01d542142c1c180f095401d41e40d030a500078030050400701e000350344d40d400003800c82c8021040001e01c0500d50b02c01c0b00c1a104200d611821460700e42e07010f2101c10481c2c182046a84000030012030001031a42c40c626819a05200c840d80603001c2103044e519030f0000703 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 514619595 1250 514618345 514618397
    0x705060a09231c022b0c0210020f0a08031012050a0b0612070603050a0b01080f0c030c0f0d140702060c120411031b19180213050d0302060106030f050106 67
    0x3041c05510076a8040000c0302c00740150300c03909a800f5003a00b0178805490041c5200003405d00c10b512480002100a0940106403089065011910300d0308954034008100d10340100c0910000c0f00d0701903065444100440d040c05140900039400c0c0360825031ba00c480c001003207141c491001034219030000329001e0124401086c62030704987e0140150b06804110150350340340151710b03840100060703030310010020440154407400d1106003007440c1c0100d0906102c0303e00180e0f1030029111601215001000c141c1c030b481400216058880d00b41c010a440f407002c0c0300f9042c01800324002e0507405502c490700280901388081105031042c25581901401e08240e00601191200000c00c00c49041d03841c03045964290384c041001a0b903c90302a04941510354070942408100c02100c448030400c00103c460900400200e8800c0084c188650a0010384540b00c3c44400554007081d0b41c40180c009101c0304015003403590204409060301c060783c409020001165491000710b6400b48921400114a0031032201c40640c50003100603 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 514620845 1250 514619595 514619663
    0xc0114132d06030903021507030609090b0402040c0206061c02060d0e1b0619030203060409020a08150906060a0302010c060f0c110709050702150c04080703080705060a09 74
    0x40c409460318884515880c0d12030041e050346a07600840014040c0050400c40600090325052000c241c5507600a965880e001ea829030320180460000340002c5d1007a40034000070883d20005000003401d500380350340f0b1110165002c3e0b000c0d0307083c0314607200c2c401d00015400e406040040c0c08114002c048900b5410411444d26080317034811401c100174547d1807082d01945030381188480240082c8001181000384620703440741c0c1540602024058216005028007140c07400c00218200540c1e03955a002c00078000304004078000b54022030044000c2000c0900243d6507070301036807034010f025543d141c1308010303070383e0f0790040f01d0160344459a20400e1005504c5428800b290500c42d00001c104405040c82403010390382c0486001d00002d00c031041001c075954003002548010000750710100300600b48050020f4036a00741605500400c441070f400300e0320600010040700c004105150540d814203450380760242540c1c2c002034065400c0c0c402c020119480c0d1006119001c0c2203a40180e45c0380c80d452518549001320401030040c0c507 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 514622095 1250 514620845 514620877
    0xd1a0f0d14030a030f0e06280906020c0c030607030515060a0c0b0f0610171501050c0111040f1403060601030e0c03060c041a1608070809061303140c0114 67
    0x140a6480c100081d10030b100507a18086031700a0000c920400701c40c03032010340c285240c1c4801c00b8003c102a03562400b5426003000c01081c8040e00641c91014082c040920008010034030000b044d072410b49010842101811040303080c1d80342520b81c00310890607104161111100326a01602552944c0703060001045004241d08040d00396100c10780b43d80d152440121080e03460001c9840c200505032070140c1444400c00f006042040549240d200050f12541c001481d42c040b40600d0062101113a014005803114140000020300c0380741000001c1e00c2070703508944500204482c8a040204004440b83d00c85882558064002c0a00da9030f80001140075180f00c00c020328940c000c00703000e441503480510280744200f0844003942d075103e1030b000200103a450400707180149440e080c00b40c0349104184001d0302c0340444c2c100046603140c4a807410402003503c541c0740c403143c1c081070001d07150400d482c1114280049a004407200441036450b450056250a01030500d0744c00605030b01007101310882004090052410407100701 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 514623345 1250 514622095 514622123
    0x40b030403200a031b0b060d0228060201200a0e22090203060702070e041203021308061506040b0a030e0708070806091b0a0b1e0307050d1a0f0d 63
    0x50310400e03502a04030005900102400028180c00600a01c4d5007100c01a42e03034002c2c05d80751a540c46000c0083d103054880c1e1400222641135540740000c4503184101100210040340c4a100782d01d070f0b0401c51340301d404050350801641000c2d80c0548420b1006030640744585c0f40c80d00b07400000880c0c403441c800f03900300d0707024600c0c61404001c241000c1c420603104481c2c203400550f184442c0101850910020040c4085501440060089202488450b604540e000c0c02069910394000c3c0180c0180c003403030007055001c9080c4180054039400000d111402034001d24400518a064601401002d214600039440c14980c00c00205805a1083d445520769130080000d44d602c050725280201e0420079160b0084416a2090742400b4001c2c40500c10700502e00602c01400181807540404074030051240d00c14400344c0030000c251024104511501100c0000752443c2d1a503403442c0121000d0305582000281c0d151140c5442c64046506912204210715003c0042c041403a400301c22003040304200c070000e02190703e1107c00340d030 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 514624595 1250 514623345 514623377
    0x140906180103060305030a0e0a14030715050702091510140a050901020f060a0c090807180507030b0901032a05031216080406120e0316061a120d090503060903040b030403 74
    0x6810612010307684d41d4100c2301980304002c40c50250b5044188000d082044003411550001010004c40f010244100700045400c18180c0c1d0900604101035005040d88040140103c07203045298107040c1d040b41c4103402200056803c45140c00c42100c10048904200070b2400740c01c0c0101c02034140d000c070502c1160000045080860700b480c4060b03d24801c010707110001e0116254100c1c9640c000752100b4001010210b280160f940c003c0c0c82100840a421591040444c101c0c80c420b40140d500c59202170540861541d403403030001400d08010f44600c0072000966424445180c5454540085502c000e00600c016103c00e52601c0c2903038441080b680500ba2040100d500040c140000b40000705101d440302c095080041c1e40d00c50a4a400c141d842c0c015420400403c03018071560454100e00c550000c2d00000d80002c80d04029264140c4c004007154040d0f1092044004000b00040b10391180c800380c1d0310901d58555036001d0541d500340a0364038104503041400107100c29046040074641c4207000749040800b4a1240394 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 514625845 1250 514624595 514624597
    0x915030703050f030c0c0607051c03060305010504030806011404030506180a050d051e040e150f031f06080a05060103031103121e1f1a09030f030a14090618010306030503 74
    0x303c0301500c0c0d0001704101c14402d00a000c4070403054419185903141100a50302c2030f407102d8101900a80360803014400d541307890302c281d00000103558060020071150034a410043c01c841c5040314200d0020340083c03032980442c42124103460469034010000d042c0f5840b0b003404400381c2a1200140203252003422100b401040c8d0400030b0a0306106242c03145591900c41514010400341c0c41080d881c2c580380104010003032050300403011075114040c03c1a601e03035580d9060001d00100d0a40d105181c1c14450b900c25460840022060064030000e040f1041101542d81c4a1b035079145d0040d03a1028203142c0089004001003030158010501400b000e0054901c0e00780c4c00503042504007001d8034103210380201001c50101070805000c549421021140034134004020000070415401c4e01c600502c9281d4503e944c0d0301c0030f81215401910625440103055940d07510351691380a81d2034110707000c401d00043c4040e9903801003003001d600f203a00c2c9070f10207400d042c50310541c45401450480485400b81c105076550b2800804210280 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 514627095 1250 514625845 514625863
    0x180b0607050712150504030f08060112051006080f0403050906032505070b0714090f060403050d3203060d0f1505011d1e0402151909090b091503070305 66
    0x6459840c0451550410350b100c0341d25612420191885c11081c000440e8128050340607140e254944016107954850040792390b026030001c21400c0074100414041400340c0a1007113415100a90f445803195941d400402014030710aa0707000c0c01042c0d080100c1011424000700840d48400350107908100d146070b100900942d81d2012100000003007012400a0070420410b045030f03002800783c07400080b41c106c03030a0000342a11410074141d03c5254101c40700d0103a80c54410964004641007800c0e80c0d8507889a54015100d0a40000000000020b400345c00c1c100611aa042d86002403407000341a003181d580d00117000390f140d80c102d000d442110b44030308040001422208000301503282050301299a516044192040c1c041503d0f900420244900c2000a20340320780341d0a40003605d04000680c1e442e25507002054440310b840e5080400c004d8000b903c2409003060b00d403040d02e4056642d82d40001e282d13484009008681062046592204d466004624992580c001c10b03803e01c0d000030195501c8a03900c0c1d44a9240c88688 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 514628345 1250 514627095 514627109
    0xa080316020f0714010201060e01090b04060510050f030a0b030d0e090117060604050414070312020601360e0d02060f0c04060210050c131403010510180b06070507 71
    0x2040031000c010300c105080340125000801c01015000703441074a43d90380d802000001e001c1ca40c125441a0302c02d4001030000c1409000048103542c40d040d003100582501e451040c010b0341803050020b0b590603e18458140c0112aa0f901c80c10400c8400d0712482d242e01c0a0034581d64030341c030740080520b940d03401d101071503040f26241c035450042c1f1501d00510800c044160f0144d80710884400400705c032080c005c245594400421500002d5580c0c2e1441e050590700e090100d480d60718400e50314080104110295203003482c004036001c480141e82e039100c80d8030300010020500c050040d407000b000f42c1040000d01c00c0d46892024100040b9844031155100d0349000000c041d5080142d10160a1000e044203030400d003608060308040f02840c0c1801d11700c003c2d544051840503044075540d503000050241140100307959200005582c1212101d0345c0c0d0100002400701800f8482c40795103080049040c06d40284030090071547d80100c601014040b800b40d0100030030350380d01c496400c40070070400303800000c0c0d050003088094003030 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 514629595 1250 514628345 514628347
    0x9020a0f080f0112110a08010908030f01080d120f1e020d0609051b0c0a120906020c09240117040f140105060609040b0f0a0f060f140a0315080a08 64
    0x40d8060042025001820446404200b00c0050040e00c8070064401da1054000c00b14400141480c4046201d41c94513a111311415460507107032208000000f4010350080341d034100c1c2c507203083e44c969803103d841d81060a04403012820360f2000b203480c500c09801200c00344484100001d40086800740c00c50404903804510146143e00044080104a01c6e100315030142c14003200c00c0050f0300e0440700d400700c0082c03d4454003140150100b075110016104006810324035601200c4250800159240030702600c0c02805044058000d81ca510811030400d08400c501c179254170b540c00d581e04d4001540c2500d4004101401c2810000d880b110503884158140c0240e00462064092181515035400c00c1d400307081135800001850f904010178404180d6415041d2480000c0454000809064100010f8002c404014119801825140c4001010a19000084222025615541690004940200d499481c800305141b4074080500c80110740d03520951001d0380c43e02c0340c54100c0c0c05c0300b5220342c002c40c5007034403c210482e16654 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 514630845 1250 514629595 514629617
    0x90c060206060a230904080c010603030804020901090e120c16080705010e0102030319020d0b0424080706020303010315180b04031205060d030e030c1c02030d05041a0309010609020a 79
    0x146a038000c002480303400b0074540b83c0c044100d0400c0d100c840d113104040c03140002001240901a4050480d80c4010381d2074001c01c0318660780e16010700441d00071a010791003160f03810000222044c860040e12a00c2c1c00b580301511702401f080c03903002a0303500003c02d841064480d1042c40c1401d1500c401e2500b01801984008025051800c1c00041020b40c0711014a1f0440d0014000e1000700c5038032000c00c9004034000100980c43c0c1c80700c40c1400d0b000b005803103c200d5000741800414421044400d8104122542581446003d43e407507100490b6550b4491180300e0050740200700400100c0d01218442d10b00030b06400021908600b8411054001341c1e00080540304850340b50180010542c115010a006011031002882680b034001c00181c0c0e507491403000a4280001021300c480304e0b980520503049280c0c00108500c01c0c2038103400031807032880d6510344101e010703114000e0900c1e00c0d2405082568103c41c011180c400c410241c07580a204540c00c041e04e14071f001d649440c4049811209070020309002c2a5035612045001 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 514632095 1250 514630845 514630849
    0x81f05030d021006080c01080106030e10020706090c06030b061b07031b06031a060d0c0c020901080c0a0803070503070314090603010608092a040c120509070312020f0d0e04090c06020606 81
    0x74103aa01500b1700c0d5011148240c850303600285490b04407003050400146107144850302d5800e00e000c00d52820721040c030000c1c440041044d00d6104003a15401200d0000e40c0b00c3e251382c0198100c42941e154181c0c4850140108400c0e5100d4408542c00498210103441c5d07050340d641e81d5002e00b200303020100c10300a800e0941c24000ea40d4140300c0c101d4040b01d2900b055104105030f102140e150f100350f0030910135460f21840ca10402500070020320201e158041e0200e401981c1d40c00810b501d41c0f04050540e8426608400009255072001040d80c0402d074101000d035207481c07402e80e0140e80350442519400b02c001c0060203524182e50311031000d180207140070317211484030b0310b40301c10000d0820001c0f80d0105941c5904000303411107060110381421000038281c1d00010710303943e0310340144c8182050103c103a60141c01c003400c004180c0004500701003142c1c804d4100c40080640c1e04000e98541181619160b865489001c0c0031000030310806c1c409280d80c4003d81f0004505003a5124400461042e8100a01507407105003884414 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 514633345 1250 514632095 514632101
    0x1020d0c1710030210050c010e0a03030608010f150e060a1205010c03050c1606020a121503030207121104050a0b0915120703031709010b03030c07030b16081f05030d0210 74
    0x740600610700510700f180e0000340b076611100c0b902c2c81040404621550610000d501c561008041c090440e00d031081c00d0b1800601802d00390060341d03565400c05c0d25410400c3c00ba400355114582c0403070b45808509040c80540c03100641c0090081da446078030760800144080c0c01c0c00180c01d016014070f0000c01c0c4d52a07000005010f641000e801516014410807001c1914602c18414940541d8010340c05a914490104102d403148020680341415a151050b01c0407209002c4000c103003164420b4081e81c080c01d81c2c408142c180ea2521141c05007080c0c0c11608400000c0c0b07440e91015030b000f40f08201c0002d028419030041001030500700c418001c2e403c0644203007003491519032080104407040d140100b042600316076004060100c0780240081c0b180b03084000c102c00c2c09081d045108081c0700541102d85544c00075002694030802d0348000d89003040110301082c5a00c8031443c004404100d00c1c1c03198141a110303550400c05024074990000d84e00b10980c1d0001c1580d41d41481b4420b008009680141218402c8500030412 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 514634595 1250 514633345 514633351
    0x30b0402031b030a060b0f0307060c11031204060e010c0c082d0c010806030307020d03080a0e010b0f01081e0c09150c0705060a1404302301020d0c17 65
    0x154a500c918410f0742d40011019409a07101101181080c1501c02007400712000e10284c3c0c1e414065802c1c0451101e07030205001c01e00501490807454048075104c241522400d65070300d0003e41c00d00801c0148410380c0242c40100240ca0185001007400c80c503030721100c818020381c2e0814401750708441911104140e414002c0a1000d00300d04020720020700c1d4040b036503603030700c0302984c01414040b100002a55564091090302c4c034a64001e451007440b81d40a140c0100181e40481c0c0310070590703150034100f0001d071005210f00315400201500b04a80340e40071a0040d51f04020003000301407902d1100804001004500c0703100b900442c120740c1c045032942c0c0b0880820a010301c11800b81071a90300184200f655a80c0c0018415017241c1040d6040e66948a200c4c10441c0c804400043c5d61105c80f82c00600003448104050404d03854104590158840001040403a40c000540c01030140007804440e085280c50300040c141111840c000000051402d0780d10725070b40302030b0b8212080074130120300c1143d841d80400d50740d440d0b501d81c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 514635845 1250 514634595 514634623
    0x91302010e0a0506030604112505150708010911090d06021905070b0714070b07021f0510090e0312190e1207120c0f0c03030f0201150506090316030b040203 68
    0x400360503c800320754a0b0000520991040380c46440c41d600c20851351003100d404049000c4500700110741c2104c206000040c2d100700302d40a125021041319a030102072001ca00480d4582e40c1c61076142d01c0c1c03030310341d8000d4548800140121002040341d11040c1d0348007075810012a114801c090307262120709100d0380c0c00301005000c031000d1240400c84000015a042c01c3c19500c0300e000d0030302400d55010403201c90707560700801074028640c440c50400d0103246500080d00d0210700d150040ba4180210071841c0520560301e00b55213142c150011407070140401809030b0401075010000204807801c02d000c03070381003c00760442a24465403480c0e050f000c0345034844840c0a00a42094040000c11501014000481d003512030404044c000b030703000c24031801c9194400c2d140c092b541a040751705100b0105207814071a1030a000d6100031004101c0c182c0c400c10500d801070041100890201e460181c90500d00414480c0b00d601c2030800b143d041c004d03548003803e6070f803507203075160040c6000b00385641080c907151050604d04096141950 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 514637095 1250 514635845 514635859
    0x150603050307140a0c0e10050d051915020d060f1a07150b04020307030c120c0905130603080310080c0303041503020c0f0d020d030b040605010503071d091302010e 71
    0x210200344004121180c1a42c4103038141e50158050f040301e401c0090350140100400d03400030000480030400c84c0054064640c0051840d41c2581e40c00801003401401100101141c018051915001c0e03400300d0300408541c05041d400751032210052106040340d200f078034038403105659100180301e00200c50100790040d00305540b006000c114a13452400243c00b031107500130411401c200b490511252030707030420010480080d00c155100c0c00c001201502401c8500304403000900341604010901b00640900d041243c0c103500e41c04107103410002840040049811130301c91003503c40500000242e1342c80e0040d0311a2502d083e14a40b6241003a95080c14074100003411842603100380002e10251200580c007070300400c03640c02d0050341d40103040c141c9820020703100d041c2a0301d03014030004100ea1503008100364410b512181d4041043d0301c560340401c002c0301d02c2070181d40e00090091000880300c6018040302031402c92500707040841e2200040c000b4030a034000721034086071b01400c6a8010f0031960051208880644111199 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 514638345 1250 514637095 514637099
    0x1506031b080312150406060906080618161e030605011101060b09060304021311090a2405090607060608030702130e0615191409100e0c0a11030310031506 67
    0x6542c0d0107030f114800400042c24000c0f84075180310560050500001030406d1040f56a034660281152003541314490120b82504000350542c50140001000498600c03030310170b225103805450148503d0b82145003c107010080301c0d414000500c502c481c000b0f5040d43d903030105000781468001000c0205d01c8250603816810403d00340a00500042912620302042da80b50b5101c0d91240001000c088841020410313052502846110a011107802045012001e0329501c0f842d581d02d01d00700a11650840039544070038001541007100c240704000900700f00c40e005003514184a0a1344800088a000361f010859a0740001030300b00071814170003000e1030360140c00368080044801c01070000c0d440c0c1c0340040c441b00c4007403900e2202c014990340e22521000034183c81020980c019840c4c501140c0e0701c00b1012603444c8201500000030301600800c140c610150341d41c03524030000c951210101d10f40940c020b0096038040c020080a05609448100080c6100d01c41000c005d2051a18605200d000b00300b0450112804c00e0601c0c0c41 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 514639595 1250 514638345 514638359
    0x40b030303151005120f070f0905031009030c0507090e06060a030f030e0a0b0a0c0c0503010506030a03050903010204030204020a0c0201030507030e15040c0506220905040201200a1506031b 82
    0x5102c0c80c0010035914440200380c1c0003021201446014840e00d13410000d1030602101c8440700c015244140c04544503400321590301a4161703000e81c610b103c0d044d4103600c00b000b0440000f809030030181c0c10741e109040c03000401641c3e6035012305201d4076070002602107641e10210111020304114090704084140e843d14001415602d50810140c114007010b001c0c03001c2c03031801c058980c5410030324070010030781116038a856070010782e8014041543c400f000e954001d007106010400d03181c10320460340100001401020801c1e100e42e000e0303500b030708410b4085606550a00c0700102586850000341380e03441255403a113200d00040d10014086802c05080e0709d04041c035103040b100c5116800144041c01c0e0140c01e41604095a85140103810080d45403c4150005c2011443d450400b180c0c11840d101e11000200e113000542d107902c6410f00300c640c2160007a0000b410340c0103c210003000c001d801d020032501201941c4080c82c91762100c0c0e0761400e00b8058010416500d6404100740300e10300d001d10003008454034058038602d1030000 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 514640845 1250 514639595 514639621
    0xf0a02011113092307021e0622140a0804030b0a0533032401090e07050f0f09010e160201050f0a0b011e030603120507020a0611010f02040f05040b030303 67
    0x38503c40255130308140401201200e8290042d010000d90507511450202030003515001e0b003941c03601c207111925006020324070020400303030311130307401e49020007070015451180c2c1d4000103642030180c1d0304d0708580c0100000500706020b1001c0b82c600518800d5510741c80c5207444000440c0040c030744881580b82409010a00a05c884030060581c2c1181c03000300c1c90100d4510f00210503050803085c03645846554071400c1d0040b240030111414201c44020442ca50381d072940031070151420034a0344c0087c1d420001060140d03107001520b01c1c00e20000600441502d40202d004036006c04020382001c0119240d580c100040e8001c0381c84060202d0b22a4030081c015420202102c01252030042c0031803040740d80314000c04842d82d00c60b0000705a02800711000c01042c08200001500420745404162841118488411440c0340070304200c402646e409801d600300107242103021240740c81d024a1072030381552641c140c2030101da481d001500240ca9914010b1162525080810046440c5004414003d42050040105000f6803003 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 514642095 1250 514640845 514640849
    0x1416030801141e0621040c050f0a0807061206080d020a110616060b0607051902011e17090c04020703020c090601032a020a0605190c0809030403081c020f0a02011113 72
    0x40c0e0310036141d6107880d41900000d80c417100c1e20034082d08928100720900030b07850f1005d01111001d40340f114980b0b100400740314607803402d401008465480602c041110503c100322840307240403d400f0002e0700a40311101107040c121500b84902c010307403061580e00c0921001e8403105c0352205003103814900c1c24000d02664040b4040c900300180c0500c0e41d600c01c148131911090101d401c40c691107006c0e1210b00e0f400c528030090f4500601000d03400a2a08000c84000034200b01503c0c5141d0125103480c442c140d072120308103000740d0008006034001e000380e0100141c15180c0740007030488940310780c018102c62500c440c01c0c4003290100606490400d4180400d000c0c1513006200d0380c41c1400e405070445030f0200c0e01c001084e40340802c0018011701c0c951500c4100011600c51241204c0380d07040e000340030311001e018104110741e03250007540d111034260030400c402c1001441d02e40c0200800302c4d2810000d6030300c1d0f00e0f101c015001c0340c02c00560382d80800300001d11a80c1e41035082c4140a00d00c403442d0f5002d41131102136034041a9480c030b03174 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 514643345 1250 514642095 514642099
    0x1106071b0809030f030a030e010b09180a0501111b011407120213171e03180103060302090403021510030f03030218040e0c030d080f04031416030801141e 67
    0xc0d8100300501054108803050350001608a030340c0407291103501c9540381d00c5241020002407522009030300c5a00c060140100d251402810320219864a0a091400090180704482584109070103080025400c2c044c115504040b681030f652901040350705100a012400f0f0b205865915000d68503400f042c4203075400e500041c041c603000c40b03035410700203144000b03200f040110769140c0b54003480001c1440748c0d0415820703401c030390206842c10610000c800c15140c916149070f03040e09410612903880c8100380107010030440281490046845541ca03008911000c0302581e0540c0160424505000503440c4020055000b4069608120700540346403542c40c8a0048004014100b64000500d0000445601591080e88030000c00802820b040007446a6843c40b841c89920f009000319104149403e00500f5143d01c150b01d96410756406540e0750f40e0488413851501480120560184a0a0400200f482d525803555200b0303180c1c061294188081c0c49089201010054400c840e012400003001c014080a4049000f007 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 514644595 1250 514643345 514643387
    0x108040f1b030c0801020405011b030c171201030809010206011505040e0a0f0c030f050703020703080c070515040302030306010206151810092405011b0b2d0403110607 73
    0x180c4481003a40703100035480a03011208049011812680650080048500980303800000c16008100c1c6800c0000031180940807072900403d5001003001e1901a03881580d80b480340720700d003c081590004c01010207801c16100c20402044c0d06041e541c0422465024181010b41015024140c8d84020002e1059000c1c0f02d5803408020702281001565801c16100840200c00c140001504540c00034020047c0107403145da034609010104440d82c1c080e1003100c16080d050344e2070300d03130a40d90400009003e911980b012610b40c1b06012265401c080352581860060744a4ae02075503503401c1120009103030800140c880c3c0c003040c01013800d4503044d41e10003907203490b1030605000c60440355541810f0103110040f141d008070071041c202907160001e082c610705511001541c0603030000609458800445500180c1064517000502130344201000c0351458018981c403296040070b029003018040fa00034088900941042107440551061104141d0000c28079440311003030100074020ba140c0340314020315540e02e11118080c20b0107 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 514645845 1250 514644595 514644623
    0x614091003030c0c0321020706050a090b0c0f06010e0a0b01030c120903140a0f030e0706020c091506130602010513030516050f0f0f070812090f19030c050f0108040f 72
    0x24842895500541d003206c00480504240040c1c01d008442a03050140107005143c808a5624000e0059414004465490070030150411000042d640c0c401580c0c000644980c0302c18000e0440704000241c043d000d004c410b000075041605107203058800d0310061078141400e01592046182c0d0142080100021400d00030070703a443d01d82000d540003010040180420031000400302011500a15001a010b10703942d0104009100465404d480300172900685006030448542800c1c645403c500711500984407000b0400d00d40b440c0d0000441c02c0c1d2000c482d11007250745034882088065028407520350b00010391a80900300044031ba50060891040941d005a000c0f880c074046002d014040211030700e080303400421503c403d070700c00707041070f0f070b81c51050040d44041d100b0311002003818038012a10300041900300b1540341c11300030280104211f03035190740401504404d607000001026a840310040d0700943c0503440b004030a034213200500269806200000741070203903c0c0203102c00038070303020340407610181c00c4501c004100c1 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 514647095 1250 514645845 514645853
    0xf1b04020d1e021801030506030606010320042603031b0a050d09050102070b10081b010c120914040212180a0f0b011e0b19030b10030614091003030c 65
    0x1044080c8100c04090440d102095110440d600418130340240701510114486034074011400e0302c00c1102d03030750340641042020070803d50007904403e040c40e0b4040b0981d0306483e135460307001a180d00310341d1120060307400c0c003491a40b44c0211880e00105403175824000c0c42c610f10b07000d99400b8491035512030803070b408071002031100004c6110394141d5000f521054004d0200007514103045021350041b80066a80b80041c502180d808400c1e24002c0007240c503004d0241c034011146170f000c00c442040d20072310241840071001904c00005c0c03440640b80c0144c40e260316019101c81c01d042c07580304078103c0b510302a80a148100081203a80c032200c20407590001d40c109040300d1301001150800e05109c2304440041a040e980d070fa00c101088010040103040c2c60820004002d1190150311050000b00c107480380c11310501c001c0110144480d150501d8449112980c2404a14810550040390340825114620300000b99030700c07020301c040441d03544c0454032018116034000700d500300940c012034891140c2c0b0005003407103203034090700d0204 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 514648345 1250 514647095 514647101
    0x412030f0e03010f051501091a0c010624031a0a03260304080c0d0c113016120201020303160e0405041a0a15060c1b06030209030f1b04020d 61
    0xc90000c2c00a0111413500180d440152806a035410034a4103c0121443c141d44626001c8046401d88800458481542d0710200721a60003c0d41c4a0780c1c5540301e00d004140180340c1d40b584c150020007000d5040078071340e0b042c00c018126540202541c907010420305050760700e030355080361800a82e900308480002203652911040300040c02c20f0019540343c0804000c12042c44602406400500890000d82d214151458422289000d8144008144180081140d042803c002c0c950f4141440f002030100d11031860b0107007004845940b81c541501540c00342c0c1a91001c100f500b40044010040c41d0a801c3c0004060b50020b52a404010318200c4261140b80380c00480d00c2c401d031116880f04801801c104640e0815040c1f15885680081018034100003035004540041d00510644106240612062920f91705058048846a103018030a50302a01c58200301240c0341c03d81840300b0010070b0951801a550a2840141410440d034080582c1051304a07071524020f00c548440c890320b1840703044400507031b910030301e602040003 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 514649595 1250 514648345 514648367
    0x908090f220e030424110c090109020a1b110f0d02030709050603160603020d0501380903010203130b06090103031d01030e030a020c01030f110d050a06150807030606050412030f 77
    0x3e41c082d080c0c80300c42c1940c0001042664209a451b05458210301d4500f43c1e0720295810116000b4901300c00412421105074081d003003c88980c505480084556008103e883c44101020748507a408a05988514580a0409452044155111100042235400103074681c81d051048554854450700061000e503000e03c0220704d402c02e41207811503002e0300c0e084018000d402104440890528241c00824102220100040e214140218400c2904000142400300d0103090380d18a15100d014086245965803e00103140718050350004070214125904150300c01c54809001a030003080b6140c0140040303980301c500c10130982c081014180030400141c0040b07004000913145074845010100320307a034810781d0120b074400e40c2c9c8400766000e1003a000f0884140701200e41500c0103540d100c100f04a14121003009801c042e0348581ca42d07200246603a90380389104207031070301000410002944141001140c5c0c2e01445440040c20440c5006803c00b42070014240c0001019140a020300200c40d4118111500c50020071007 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 514650845 1250 514649595 514649609
    0x11010f060b22050904051507050322020604091a030d030e070614300702030a0c020108040f06090b041a010e070507140d0c060e06060f120a05010908090f220e0304 71
    0xc50b880c05e8240103845040b91001d0020210901c030206101e03521520941e0b00803c0d080541ba804d008a2100100040745000000c80c0c00c86024080016900e0051149042d2201e140c0e126901e1900050304150030560102c1c1c43c0001d151034440114a00400042c07400705030360087c20500c62210300d0b41410080303402440b4000032202040c100b079a0390010701c48188644582500300c0541940c03609102a6141e0080d05141400101c00030301410143d0b204240c0b03a44c009009200035600a00c107a01d45006541ca07810040d1460340f404020b010800001308003412220707c0584140f0b2040d4180813007a4420840501000c04001000c41d60b40c0c140f00307095036841c0a0030028030441e0150039083c170024189200c070000079039440d442d2410009400b180829254402c2000404503646544170100f044030a1180429a000610a60b1580000a00e0910812010900412004d5100c4125400304660100c00800c443d01808a60080c01e0298252400b8551429072440300800c030150707813125462650243d0381c0518 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 514652095 1250 514650845 514650859
    0x30403020316080c15042d061401230a03060902060d0516020c1801060f1701080114061903140a0c292508040e0711010f060b2205 57
    0x6003c01410720000d181c00c42c50041520142102d1081c0d85100c080201e401030480c000d20044c2c0c20794090403006c80e08280f6020680150814096181d4404440c403d0540410300002c0c00c0c010310007405100c0500d486104000050100784049002140c0d020060f03100040c0f0060f2a10000002c640d2103070140c604240802c0c408214518140c8030360be802009070744000015008400007007030315050100055000348132651405c6a2039280c004101c8080310310600c0d100400104078542c56558000b48040790003042c00d8000440c1016a4a004005030071021b06a94410a890f920170350000040d1002e0400726500b00440ca2501200b0001b004e0038000d0108004103650051100400d01c1c40a039031032218401264200071030500105000f0b90300504c1010451003580c030341e83c01c0450201e0078a2580d0006035101d044400e081c1135445100f20750000b0141e60032000300d18644010035000d4824843c03c140564200700c18003003a0701c3e01e411314009104010143d01181c0e40c0310b1500700e0000c11000f0440003420701419203 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 514653345 1250 514652095 514652137
    0x90913081801030c110a1403161209090b0d060b0604051002070314030c071202130606030c110d0c08090415081507090f0909150204080304030c05040218060304030203 73
    0x300206501d6000003030b0129190003002e988481c850100c0301102804c4034001c088021443c0caa124100603509081741180c4020032240500340c03000305000b254107204020382c040303070010400040c210301c9084d0045103031185001c3c040e240943c0d83c06200111a904154002001c0b64480007041541c400c0c0c0d003010b40c02610180240342400e42c001544011640140441c601c8403142d8180c031a00c902c251b210440b03c540c0b0003002845403070024290041050710040030526841c607010390702401e5482c01c3d030083d4080303652468003000350368020218800d441c4503031002e0200c04034442d50191101540307000142c01080045924101c030f840701e922004005910100f031142c1c0355681c00c421ba83d120700c9451300d42c00440580c40400c0314140944941400c0d1043e40403009501030400b41d0001c000c1ca801d19065841d00445a4000e402c0842440100058400d40c00615500c0b402e505201e1041255540520301583c0b04003e240c0b25a000706c3c4440c0b00822007260b1040d03890b115400c089203140203542e0072044401c0d1071484 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 514654595 1250 514653345 514653367
    0x60406090c020327060f0d0b090f040201080604090507210f0b01030c1215050703090c08071a041203030c020f0102030a0f0b01050c0c100c05060903130509040809091308 74
    0x5090b500e0404c503583d15411200c040402c42002441080c2504401d092120108140e9031201410104402900000319a0118070001e0140c9109544455402a1500512045d96800340d5010303800002900c080c40419096a9180d5480001e44615000d002d10402080350304007580034803212041d00543e292100351014104644803131020700c02280c00e400c140400140049050b54030030605500b013400400413100d0301c0314500c060304005150008140e5104c4c04400085e8000c4100c0000d41055001003c0c854144805558100c0e807103008000000703000c1c082003146043c840d0048180560502d0007050100800800760b140501c501c03035003520780d400442003051090a070351040380f46000d040f1040c00307099444401540c09216402c140d500c280c01c0804600141d0800d545200010001c03858115210001501c80c64107017102a20170301c0c0d0a4000003240071b00040500000b001a10003200c1d01071850810b035941d20098422a08494091403d20001540e00c0340d0540801645a412913500303a510b402e5041 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 514655845 1250 514654595 514654597
    0x3051e040605092a01052a0c150c0703020d0212100209010e090103021309290402030d021204091e05090102130e2707051206010807061403040b060406090c0203 70
    0xd080b003c03510038a01c01c03c1c00041d050600f01003c0c1d01c50944801e403640e1040046030303241c2c45a10341c441081c000c080420f8454000c0741c0032540756081700c4060814951003504000041c0001d144e1035500400c00d1149542941d8041022400ca0b07a04807030b01e10b0041003601c04201045802c200d0090b16018100014981d42104c0e0010180408266120341246c10b8110420202080070f00002c0e40190945200f07408070407003680444601401801c0c141041441c80310440341404c504c07049e01c0d9864045400740300031802e00f01319246c0c6100650028102007100700f03644481c03070701952151500c1d4a4980b0020024188003120220ba02000c091091006142a01d0303035a0107944103a030700d6154001404c1c0b0000b600681c3c825105c0c0030302c2c07140c1c1c06d41040324032445501441c24101c0444214a000c5c0c050001a1a680c850800451204050251038190314040c3c0490810f100350f407211081c00030125220f03100400c04001c59174060790058215035140c0710400400d0042210341c0002445034509480c1a9005070008 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 514657095 1250 514655845 514655851
    0xf0c0608100f03030909090f0503030709030c0803030f160504050301091101020d08060108131a040c1701020a020307030815280611070e0601180e040b010e0f060103051e040605 77
    0x785807007050740d5036082484241c14041c440500000c1c10f0342c105100c0c002458015441260142a104106040079118641903a0094500102040c40e00300308000300000300c23040c00010902400034500b03610780034038001c00945c4010000190110360300e891039103050160065078094840503000300103286241c50001c4100f03030780380612405485100c154404151240f01e10320302c2204182d445510548a0020940e420359215608071039446a90300c4404920301e600070741620a50103610080c0340c1b07500e4580035000c1c0c0c2c1610440c02541340d00410109003400d80010132075000b0345e03061405100d1035403800c012036083c98020300510741c080d503480d8408140d101d031000403500c81c080c800103e00c060717035030703444251020b0980c0a40c4140641280704100069810b845141d64840811f0500590843c81c584440740041c089402c083d0070b044180f420300c03050010721343e519030140541c0322002002c0c0c1003010801080c810010b01d03181c1056101d03000201d070400c40f40801e15004c00c2c10b07941c10440e070400303251040240400b1 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 514658345 1250 514657095 514657111
    0x203010e06090a02070507050111030d1b1403160c0c09090b09070f0e010b03040c080307081e0f120c0d090c030b060603010b0316021204150e09060f06070f0c0608 71
    0x20300461410300d0743c3c0c400c4840f41c5034030600410034589040c0040d0f55141e03c18403120708601050100322026440c50003080c1c000c400c2400b44000b03507180d4400150046002c2d40440f61a06010704c00c10009203000e44003d100c08002d81090002e0a5191611106400141d0418001e003402d080100342007040c42008240104000c2c01070701c00058035942902400c080e05e118078080500540010080c000f100c000564026000d10144824107481d0814640f031030703001c028101c5a5600c0016070880307808031104146911060480702c1e500c2e100440d07404510500038a420126002e0499020a44101034282110340c15484c0710014890400c1c90306158000c00030f14070054940803003010015455140003400c503070503940c400f4507041c11601e50021108501c0c000070700c09415845404800c1102640410242c0010b10344031031100e140705500d81000f890400c440c1d0120b400b6070b031030005016180d80c07003d0081560080507900181c40709114100b0380c40083e512340f005812410b0f00d241c04650598848051881040c2e0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 514659595 1250 514658345 514658359
    0x60b150d0501053a0209040b040b090102090a2d09060e0a06080303040f14070f0602010e07060203090112090c0b0a0f180509070215070305060a0f05130209060d0203010e06 75
    0x28410504c43c500081c840d00203503064024280b110004840c0920545100f40c2070290b800c8101c0c2d80c0c0c08154685410b03682a940c48a5001c03c0000b008101d007446a88652840d000394288840c900114107921034502803550010588100c0c5403801010381c504005507064824a01d402569455926004203040c0c041d00e00c0c4511003c0c00101100c09500440040b200070500661031542c594498107883c040107074045504174004481c15801180421242028040c4e207054000f985142ca80080e084a0150385008290b4001000401101d0340100a0b101d01d02c80070b080181707000410503d110001c0561600050220550010110740b00000102810281116848070b603c01c01c01130340146c410045401402c404055440824452420b00b0062150840002d0044403440d0795441141c2042400441d4058002591141000010310b4903100340300c0284101811b40724454241804281609510f038503004c1c2154000910800316181c03002142c901400b4500119169619810180c101080907030344a8840c01c0 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 514660845 1250 514659595 514659599
    0x30109060b0906030c13080609060a0f0c02060a11090409050c0108092a0d0602070f030840140c012d1101020c0307060b1f1704060b150d0501 62
    0x4020007200d82e800801450182199103080c0c4009460340004850485915107020002d420341040101d1806030600f40d01904180c980900182c04503400120300030710b16428407402031185074011401580042c0840300102d298013003038039107000a114801090303804c185000344040034040e0102d01d58030421000d9803aa5078945a112806640303000000007004c10341c01c0c105816140c0b01005034890f02400c0080e020440704101d0780c40b810100d03080010195034000307203400c11800f09a8004d5000d030b80981d1040f91704140c1c2004400207040b038448038960030203c1c0980c44180b458051401d40e1a604203501ca15000000c06070340ca11940c40f4207074800840d0102d040640401c080b610a28400e00410034030782c0b86400342c1503000c5801c0f100940d19688149281d542009050303210071003800240400c80c0a208082400810350003841040c18040300c10f588040d214440704c00c40c0b294000010344803201c0d407444030625902d07641002801050740d0680741d60710511254100341c0408240010f041002c030201000c01a580e = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 514662095 1250 514660845 514660859
    0x1d0708070203040b0c0703060c0522060c02090a060b0c0304061b0305090105030a091e02011d010804021e031b030f1f0903090e040807140307020d03080702030c01050c03010906 77
    0x4041900e6000240e0010b020622003030700e0603006800300841c1c0004032404955243c43c0c140442d409002c41c02d00103200042c2c02800748444840007100c02150034142c0e1103d91420400070000311004a0091240b241030001c40d51007d460b4100b20060701c0c8041080d90b41344081c039091640c1c0e6119110321000700c0c03040720309882040403068a00e019141c240e19070b18030344010308004582e03581c4001c2c02e0840c0e05640310184e402259020300c00c00c0f02e6108680d16400740c09141e000262035920501100001c002c0b060160750001e0364000002d94004c0e07815102071204c0c100801203c04400d50419070150588140020015294901c1000340402d540c1030b41503c0b0014001914592220152004841c42e0f0000281c0400117007081d0f4001c8200c41d0003880d0140c4180e484081c81c42040754140c0e020707200020042629002d010250a03048043c203011b100035883d00f2110fa010070f042c07102410300941804019000640713024003d0040f81c01001c2600001c00031403900441c001001c3c0c00030300801000e24a4207a000c030b04c00c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 514663345 1250 514662095 514662107
    0x18071101050103080f0a110a060609060509060d020f150c0601031406060907050c01150b0703081f03030c020f09040303140901020c07090b0301150609050f041406011101151d07 77
    0x2c0e03034001d44c00b1072421510300050110fa6105460b540208030500040c2a004c107414031400181030b01c541800704005150951140681c0d006820180c0700b400c0e04805d00c40c1310760300e90011003215a0b0680c0c001c00300c01102710000342802040d6440da004c07107500050600c244200455264162031003003195028090004c055140d0707451045402c1900810340724003007030312140184040c18060303540d02c001207144031940300f42071100b0886501c80c05000c0780100f041420190040d041580c0b100414040d0300d41700c019144102c0110307110f444090f0a0004001500c01951260350008210f40c50140c440f103c50f09003031400800507c1403075880358040380cd210105500800c1802101c1c80304e503800d0b00500c0428100b0480c1d40041c44c0d6400080e51642d0b85400b0210341020410400005003019100c2c407481c145040b0901950052039001d1910441c80c20792030b581d1144400040c10b070091420303c5e108484a03140b0111500501114020914501d038010300010340540e1042000303100c1a400c89a82a1072306c9940c2c2c241c80c2 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 514664595 1250 514663345 514663349
    0xc0b01060c051515120102031b07021309060b1c0605010b0a120e0a060c0f080105040615030510091802030c0609010903150618060611060c1b010b180711010501 70
    0x1c143c00c40f050410041d00c00740c2c2899005410049580401d07104080001c01000c5030052654080e50084108145545030f4030b0000b032004020030070545000110350000300074000b101580d10704660340d140c00d8070600c8441d41c4158480b900107025a0080c81c1100100341c1c01e41e00813001103445509280011032055071020070b40c4d081501c01d881b41e0800b50070f4612103801070614140400c005100c0c400300704000c100e8074020201454840d495441c030500043d10010b1004005800c203034040c0e42001c03800c100d641c528041d090308030383c528507002489840d00340440ca603d00580c1d0050f00c5c001c0c2441c280c03a002283c26120942094421000c403540d80d881101030008a003c1c2000c1c00f4081050030600b040803842c0e82da020401034036010000580d40740c07503041005401601aa68141050340c40c10140801d84c1c10414a15444064a000349a5890659010740c414401c0108908803011180c00303106444109410030b081c8088002c0c90001ca800c4094031158029104543d0800000c0444001003140c0c10706100b2541 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 514665845 1250 514664595 514664603
    0x30902030115051e0112020a05032502030403030e1f05030105030c040509030301090903050f0c0706080c120601111501090c0e1915050405040516021e030405040905030c060103030c0b01060c 83
    0x51031020a100f84c0d280406039090750500c0104245011141054401030041c503070307240c4410740c07203040c00b0904000c3c4d882503180b1400c1c00c4c4175980e010020280c000080d502220380c5480c141401b0b00103840400c12143c0c0340c650001400320781c074a400c000d25810001940c1a03c105504440c8a001360034204020740700182e42964103500100014010703c03110b9045403d0003406030425520f000c600344038500c0b83e03138085003074161036800203c401e110142c0e1042c000e54100c458030000e10f052550342c065444004e000a0600d605101c4182c5962034a00c0d41130240840c0c90882074000d12566940b07001c4072000d4000b1318060000030f541d90b17151019915201c0c0d50210418009d01d59068150b05140d0b120903d4144400305e0380a0103003d202c0003a690b0b0f5540242407050100d80010300c0c01c0d43c806200030b4034000c41802480408520581901c00b4910008241c800321041180d000c11040c8143c240790381144902051055079024a50000c01495000203c0100307281c07145120b60547c0ea41c900040360410341e4800010 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 514667095 1250 514665845 514665859
    0x7030b1308220506030c0d0b100e0108071407051e07030512092b02090a020315010e060409020408061602070b03010b22062a0803010303080a1b03090203011505 70
    0x6180502c482d40090203000200703040301019295400240c03c3c0d0030454080b040d0b9179000031b808501c0c1800c2d0144c2d550b003910641c0d031000b1034048008003074a1403881070780050400240c0c1000540c0076209406c03962050ba080c0d980c45a0b145040c1c10041e45070480783d904c45d80914180102e0346010140041e254007201d412402078043c1030106d26204175164840b1241780d91240c5a11014220913a07240c0d020311600071144000c85280038144140940c0040c02450082824810701c2088100355414080d8503030341c0402d180c4107020811210005415000b190442c2c605c1a10110340070800c80000036130103000d80700d1802c943c402c0c4141008202d985c0d0906005000015030148010417000c0e84410281c0030384027005000e0a444102179490200700040340d0311410001c3c000c0c0c1c203411109901e0050f040302c03084200311000790511050f00c0b00d425034030062000504102029000402d003aa240c4d00c0440181c188030000c0038110800c1078020041d01d505c0c1030a900c29484c00c03420507030009030500340c0c01c111400a8910 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 514668345 1250 514667095 514667107
    0x8061c030311180102150610051c14010501020c151b2a1306260f0d021b040204050a0e060d060504050c04050f090706030c121121070203030c250507030b1308 69
    0x840300740c0c00c85001030f402b0324004c031301d84841501c55004848115000c00840b03005985003100080c5003200c0944554010280180ca040403110319000300c504807052030040346080800062068904500300100074443c3d644600c8000c92200344600c1041e00150482d20700350000c003406a010105c50300c0344200c00c0814800d004584c2c94203d030301010603680e01100b0655070a039070301c00f1001d41403446980300c0000503000b4180403c00302026000b094154002500d0440c1881d0a01c40410b802002d01d026100201c0001070005c0c0e0265141526450b40a911020600031800c00b8a0000d9880d841d00c08020301c1242442c0011382da000f14162500e12500601e270051115031b2911000782d005042c120120f9080101a0703a195140345c0b4507000781006803460020440d900c5030400140c41444070151040c4041b0401e100030300200b0b950001c02d4039008110303055520781c0c9040c0301e003013199040da08454410113074401c4a036078010f00c003010645070116030152041c40c0d1960359114100301240c48811000703060140134014 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 514669595 1250 514668345 514668347
    0x150911180103030e1c050609070803043c0303021b010806091605130b0c070527060307030204050903120114032505030f1b0108061c030311180102150610 67
    0x1104c051140500a4540c0c040003070041490303942e4050068805070300440600c05041400c0014400070504840a10304040c2800104c644020880b41401c952000003c0144150840c28104100f03a4a40e40d00c2c84455642d203242c0a51210801004400b0312124817076080c8c1654011040c01d407040c8001000d0034025650032146010304415a5010007c01c80280504e402c4602c0304101d200160141400c100d403902011743c1e0b02840c001003a0020750081034985242d103650091118114a6506c000c0c0344295150740342d00120b0318040081d400650701608110038040c444c0340100007088020038510002c2c0d05683c94503500980c80c01d070381c1c0e503440e0036610402000300d8502c0c3c4555607441c00d1041803803d404251b03031140080e00c5c00d40302c40344101c559086000c40700f131200c00c2002c0d41e000054082c00c1c000303041d240540015000d070b503210324850b00c191a4446502c00305403180c0d04c5054400d00c0c80b2003035525240029905840c0480c0710f803085000d80b00356582c41ca03034400d100410903c075a40003000c00c2c07200907038900 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 514670845 1250 514669595 514669607
    0xc0304080a0201090803010f141005040b0c010e07091e06140f03010b12061e060f041113060801080f030909070c0309030c0b0a14130e1315091118010303 67
    0x1541e0046558600f00740000821200045008000816502c81028184110000301c400390354041f9100340410440c401e540ba4000003074074110740240380740588844400121b640500103100d149906800351031004681c110311603108a042e13074103c10071010581290045402120309900403086070b19407031a1360244515140000141180020f07001040b410103030b0020070710744600403036401480c0d00400204080c2c03000d52144011a000c440e00d0b2a0b0560a01d01c0201d01c02c01000bc0409010b182c90b1a4280c0080c0302d143c08450000040721030402219036545c00c0280252420700a62416000b2000b42103400d07071000040d81c80c1550300400c8109552150792080c0e403840d030040411000c1c01060500000490503801075100108820041c0700da1710b14107050001d0604c1d213031220700015048144041001102c040b0b000609840c6074a5401c501c3e40c03200d0240c0310464544400041c0b910401d40790f100e941070300030b420042000340f1038246084140543c4c020422980c0303850500d848154906070040001c070781700d96 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 514672095 1250 514670845 514670857
    0x50901080a180614090c190e0a02071e03020c03030a020c0f12030304060903030b310e07060c060b0406120b10050603040f02280b0306040e01020a0f020706080c030408 73
    0xa03450070b030700c0081079585405440c0c0b8080c0075100c044507482080640f10007409504402101240c40d00c80090100325000c48003049406444064440c650000740d9018265045504603500022031280440e44400c200c4010258440c044005020714650080c4506001050391404011a0090548002c0d602d040c490080b04044007103a1004083c214070b20584030500007103000f6401040003250302006400e02400380c0d4072401034940906031170740d10034908a4018103002d4560b003505164130b11820329056501c014004801001070b20b8020420700080c035941018071003400714420401440440400f40c10401203c11510504000d5200c805c0d1074000a100b101042e03a1201209145090440d280c10210394141c0040300d084540b40c030b01e0101e4500390300d080c404030700c0888030410003030104410301e524003201002c0302c1c45501c1c81031001001080c00756582e608175044620002c8000c540300d5420007401426000c140e08040c001d8041c481000c14102d1080c42d2561291a450f5a0380389162210340d60b5000c0340c2d12071 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 514673345 1250 514672095 514672121
    0xe0910030c0e01090b090403090303050c0c09070e01020f01060506031f080102070803091e03091201060b0d050f0129030402060913050613020909040b041707120807050901080a 77
    0x10000c800201d03000c1c940c00150410800c622a190704001d40c4501701c4880300b0740c030380c403442ca01010000042d41c0b2a41c01825264103140403625103004100b03c501c5d00d000c042602c2d9006109608201500f81d120260308d007603100036801c032504060204807480c200c40c0d00c3d0107515008041000060700c1070780056402404100d2406882d640300e07a40f201000d089070403130a02110116000414000308043c10400143c14820705100c0c1201003042a036403507640d1044503161b40c000c400722402520201429840040108070400d1026600d03100c41c07200b000108011603c07003400030b0844001003031006442c420507500c1580c1c15209040b405250400c020142c2004200701c2e40544d0411080190341c8581414008034040c0b48404101c0c1d0606000b00300000e420b810032444000c0c41800b10340c071540d4419a0b542e0b04a500116490032507142d5041460080c80b100d01302203c41d400006100040001c4803403044054034180c0d5889403241c8801408032064400d0300301d41d42c001851100072980c18002ea500100f110000 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 514674595 1250 514673345 514673371
    0x402011b140a11010e03070e0604110c01090201110f0a06200a1707020d1407023106050a050d03030c120e010b03060109060308030109090201052a1c0e09 67
    0x4680c0c1c9000c03810050018045841d0030070124002000b0700302010b10207520090034040010480100401d944681600c41c8002041071100407907050b45070313035105102c03c520070080c99541c1c100c00d40d0030038003916029404900140c1a6061504140c0b000b15072000a0900100900a00305190b100c8d04082d01101400d0061040d0b01e10780754411007a0310300108003050007a162103d9a0500240240c2640c40060a5205541020700740405c421351044a15401410801d44561184414000300c2c452300b1001460f0030a112010b540d04000c2e900c2014148502c14203c0c4090021540f20000c0c2b0020405a20805800404060703003400040c2c000d03004098400caa500c0d150003000e20010480040d1250842000785a940d03406603041c040c10300b80b10003805000a0b4a040c80064a9580c0725002c512052080008580c1d81c0c40c100011a8821000c4600c0510306210354001c3c4c16505840100c2c820f11000d40200c10301c14095000d003d061007400c00c00a809264940459668001e0240405108001d14040303000301 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 514675845 1250 514674595 514674647
    0x3091c1a0a14040b040b09061902130f180b031b130b1c03080c04031e0c0b030103060605120c090a090c03050609060106020601060e240d0f0e0c011106040201 69
    0xd20b0100341d101c3e0b40201c84030700351410a42881580880090440384481c0c0260040180700c000e60f04a044192841f000016600c012020100c00c084400d03410071a94140e0352580001d40c3c81c0308080c66070703034100d26520410254481c90200b680d034140c440d01c011b084180302c41130611075241555034096500711540c0e002c82c90b003101c003001920540006805440300442d1200c0d10090546c0044c0c0b00da4001d190851051901d41140c403a8041d40080f201048055103a00d07a074802000034522800c00204480c03604640c917541c50b49003610140901e070040314056a201e0702d080807a1000068100c082e8003004d4010740c51515103080113405400b0852054074400d408510001c00140d00300849441100e039400903044a50400308001e043c00d4040e4080804c01c44c400e007d44020741d5422400e511400751400841402c03071402181c51000340070342824131a02a281041d00381185a550f08200911030180e0240c0d9049840d0b00d005442182c04032000004650000c000507006500424601261181103024801000 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 514677095 1250 514675845 514675871
    0x10f0309020f030d180611060a0c05040f18050a020702010903110303090603090d1b1a0a09050d0306031e08040329130c060309030e1315030503091c1a0a 67
    0x15241c00c00c40800540001c03170a001c0b01000c01120006011145091441803004040403036456501420900c0003998845400c0a014005d40445004001104200c0e440d07a07550900403401d100d0340409031a43c142440300180e90340c0c03102d108443e01c0c5035050b1156844c55055446580b903080e55400902c0d0076220400a54440b0703510000030f5442048080c0080c250320841ea003005005007a00031100b080015006003181c0000c5009403c1c0c120014401c00104840e500c2100d1800900881c002c054440c0c001d0016107d48240e043d00110b0a503070207180c800d103600740e41c0d014074154005054409004160207000c20300005103001c1381c059401180c101c0400c0102030141d02c55100e25025a404086080844c03000340c1005140c15620004042a082c108880101500c000d010b0034140103509110b1060100c0d10702150400c0e52004108950052035003220300c5c2c803450455075a9100d026064411f0248218540d0307001c4d0b0404200100c03907404079005100821031100c07004444405002c079114180ca61701461810 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 514678345 1250 514677095 514677103
    0xa180c050f2a150405010b06040305030d0e120f0a02010605010f0207030b040602070b010f0f0603020f04030204090c0308030a0204060212090303040e0c0c1f0e0601080721060c09051c02010f0309020f03 88
    0xe25600350f810f8090410745130050031550300310940790083e44140820004240c0c04010344000500c0c50102041c038140c40e5480d1030a0103410b24007840c80c0300d0042200907159a10f10043d001995094008124040d261130064800501c030710f40c821b00507401640c0c02c0c800503a5041c0b020703400600c21038015081a01544d43d407211103209030405101000d00c00d008000243d141c00540d0018602401c0031894808032a44003a242e10860001074012038a902040781000701749006d5a0043da0021403180d12401c02104207400303940184102401841101c0350080c0111440c4100c5010480040096280c00e1910009184c0d20b80000d060610124007841180c14108040c01a5500c83c1c013240091410b19200805100c203c3c0c114810303028969015100511941c44000390b0001039a502604120841030600c2c0034451058038120020b1078030703040c907032010035440c0c005102d001038802c1114290040c0b45041c250b41e107150158200640041c140c00034944403d030003a40040c1a050000c1c0c03025807100400008a854 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 514679595 1250 514678345 514678363
    0x907031a010c060209040f02120a0c2f0604080a030e0f0729040905010501030c082a07080c0604110102060405060610260a0f060807140105090a180c050f2a 68
    0x47c560300001c08040044240346501d1b44080f0014040101042a06c030051684800303105000801201c051606035442600c500c4030101015401251000d2900d46060390700d941001607014080b9007084d150940d500808240240c419034104003c0c9401454217403100f284002020405544503101c49582c2003104c89400188098801c020f0042102e5142c500014212a40c44110804104420b402e000600c140304003141a040410010750108100c1e11840c1000c622440304000c200308400a181c20004101080c86d9101e20b0140c078009000c084007800680c2ca90740c0403900280b00750895800646149001e036005005c241d814038180070200050440305d4010b40c0580104c01c0610300c844204980c001036070180410066210205121403450488281e91f51000c50051074036a114068806010307034861001e0300c1c1a4000107104000003a07480c0180140c038100410350341d0000d410103442446803405142210b207006400017100307281407202c2815030030f0320303081e015808065604220a121140300400801c55 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 514680845 1250 514679595 514679621
    0x1060203041a030103120c06061e030507050d0510150510121508120f070c0e04121e05030a0608060c0a020c100c03120f09110907031a010c06020904 65
    0x26036103040007030b00c2d03480d1000314001500d8610104014000155070080040f1b02c244103081403146013041d454800c01802c003e40103852131400500103002404004a004401c0320300600c1905d00890710b070f20034070845076038503240508958880d440641d0708030b50541c401610101c03040340c4019610748400000c0d40c004d08130280600002d4090a038039440309501e01c00c1e0b01c0b0b04250301b82e140e01d4440c50003525580302d6160300c2d01d4030f2602c0c201044000e903c090042c100c42c2c200344d104110301e40607501c0c2c1000130844481582d041da581c00346c6202400146010310281030030b1060400078440380c035410341000c85065000034049000c0c00d440d00c0c0c3c0064010010012540140c0c2030800301034413000311000081c58159040b280611802c48101030380426500251980d100c00d0700361510b08040e042d89022080a0300540203c0c0f44c01300e25003242581400241d4424854601040b107003000c1e03c0d19030f0f00b0120250707540400f10301807407900904500429030145c042981150701ca140c000d0b0400107018005070071a0449200d500e = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 514682095 1250 514680845 514680847
    0xb0a09030209191b020706030b030a02040c09150302040803040b030702011b020c1009230d050a0c0501080c130905090c0a0e01060810061209060b0303070c030c0b12040809150301060203 81
    0x1450350110b80900c5140c41c02d1361442d0b00d03031101c00480081d5680600d10412080c160307a19448102520240031102c0307820740140041c84481c40d086401850f458041c400c4840a90703141007030600b454824000c07a002c83d140d42005609040c1002d03045001da50000d0106000d641d41c0340400c90f8804c1e6071030443e509000b0b041e0003400503607900e1820b00c800b0344083c255003000c002c00220f0030f100f40c0c01078034206010f590313040c030b14142030701d000e0804900c4511b03025070054501c0c03240d012641e04100d0007041402c1558000c0c0c0e00c000152701d5611003600700d4010a00d0440207556000b0082c03000d601305d9449281d0241b546030855807030030300520100701030310001c0d009158004c4120b03006004568215020079000512400c0b040c00c40c1d840c01e00001c080484003481c2034039240d101e0010000307200007074200010703e80c2d00806495503079160f4a440d1600922500c0121000c0c100b0000000c2c41031100d20541c2c00b18201c18100c04201d40d15550744013104d034002208150700440060401c203042c80600050360203000160011 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 514683345 1250 514682095 514682131
    0x120f1103181329040b010507061107080c0606190815070315060305040b09150c030c04090c020c040e06010b0a0804050102040f080609010e0a0f080d0e030c0a0b09010c090b0a09030209 80
    0x190f0140c00c640c40683c003c03420120700007481d9030301008a035581c2c3c4d00000006584600740b03421201e07078030a80c10040c1007000081101491040042841401914100c4003514011140c2c803110003500c01e944640c071a81e401c640f0031000d803c3d11032030009034895420326000a41c50341240a5510740e00064100c0c5000a0750703070742007000b0085500012600084808001c0c1000768003440690180f580007002140d00100101c0807800000314402680c4c040c0c01c5006c804e10001c851000000d580f8244140d6184c841c50409036451400c043c00300b0524140d8880e40c0b0760f00e01d050040b6a043e00c82c218080c20844442d03508100005500042601c1c01c4d0103464228064640760604c207511600390f500416143d5140e410080054001a03001c5101c440b54913440074545807a425904c0140000305421308850010307000010703803841c42c424042158000c00744100c40d0743c48a074484520f000c0c2290b140e540443d004c5400803400340700d40d024501c003414045100b0700c6d11108a1f41c8070750102e4040f09094856170b940401101075 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 514684595 1250 514683345 514683401
    0x1110d0f14060904021c1527030509062208030919060203190c0506010b030711030306130e03040f06030b0f0d02090604020c1603120f11031813 63
    0x280101e2600810200320941800380001e04240301c060802807044038008440c800244a1031805189a03800000c594511304c580c040c0f04002e04008183d23651b0741c1100c2e42480303402801e424908882d0b03e400d50380c0d050612248209200312a8000c1e91000c1454031003104407500901d15079082c0c0050306820020350f40360340b01e00382806400c828038000e49103690a5040d0500c40980c3c0003059418410f000308500a0b030118194041c0d81c404840240684540038440011403580d030480d00460041c0103da445d120300c000c00c59041516800142c50305580b081814080e11414903840d0410300c403c095800c141d034a055034078600400320307084035400580447c0c0c440c8034100b0940750900100700c00c0682516140c10b010341589c0085c060a01c01894141310b1a40811614070300c45042207880030350040ca01440315982c1e203e050608030030324043c6030700c000510840d10304102280f0940240f41310703003043c00065080c00d000da20031001c09100c0304040b503041800d081c0d241000040c40c1c001e061516014284002c03a44100d214 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 514685845 1250 514684595 514684601
    0xf11010603062c03090409020f0306070f080604020c061303051b07031e0b040609140109050c030c0f10030f1103041202070605091507080721090e07050a0e0301110d0f 73
    0xc103482050758031403c01c01d2600010003100c1e050801180d00081590107440051100c1005405058040c821340041107180d5070004080c990040c00e9454503a0107035154000c0100781c3c4101602c810050f0030200c0855400304c00c0c60014450580300342400b9051444e060303231414008504244404035540841010801e11403103098120800035400a0301800d45015101c142c422980500020495590340a20034180b200180090b150b00c00761a0080c4103406003410400d40d504141905548a8000c10391005070381e00c0c00070b080707070700f8200c016018013040183e800059001700601c4446650058441d01c0424200e80e1303d000542c4076910a51650305000344d035000007441d140c070941100c81400000c002e210003d03551050700c3c0d035082a072581016a603140314a8441d265000d4a80020440c82031500c500910104081098292080c2940d6444420740c0e6070800c0107452a00b074800b50701040040000701340c41445110040c4941a0140c00070079003010301e84a1800d070358840c00d80b901c1c120750340d014181c840d5580d0340 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 514687095 1250 514685845 514685891
    0x1e18020c240703152d0906051f020619021608030f18061303030e0307030804021009050d06180c0f140102030309030a030c022503030f02030703020a030f1101060306 72
    0x3180070001050603c400704d000913680d0040600c03081052100b4003000c0e0441e101482464a0095264110b039a2500c4100141001e80038603403044982e456030310301403200b2070781b0802c010420b81e000f0201c98854401030701042881980b01082c02e0b1f0200000803800c0404840f40c04070910508107150b0340e1910088404031501d0190810026084007400140b2150000600580213510251031903054034030761a0903001001d0b03c1c68250000d020104201080c950070500380c900c02d90082d10301f82c2071034808520848094a01e4002c6d0f0703603c004041e403410003140c2079501c4011440142001e02004451640fa030006840641d88250f018001c0e19905118407207070360050605802d000e000450079401c220310031503100c0c05a18000c004040e0389420303008056100b0041001340780c00c1c10110120701000195000e8002589010a4001c034000009400764544004105c4201d650180d02400c8042e4039a903003141c40c1103841d0040070400a0080300101d21480c00e20a41004502c2003034001500307030a14a00c031182d1103800e = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 514688345 1250 514687095 514687097
    0xc0609031e030c0c0b06011218120512150f0d060e300a02031603020a0201020d08040305030a090c230325032a090203040308011e18020c2407 62
    0xb28103d4030125800840b0004069481980e0607040e40d07070b4000482c4d1501d14455402d001c82d0074140160100301d242c0e42900909030045c3e100d1049174600050650b580e210702c5c013450403440d0607030000481200c50100c40103030150009260503080000200041c005881404003994081e65070751035412069400c00c03410a605140c852907001001450320102c0030b4141182507465201c4000404440c031a2082c4100c80f07400c1c1c9911030161800c0d80761709000350740e00c0028400303e001d1321070203840600003070003031040034400c03a4559104d0f0710b16920001e040014059052045405074240380c400b261b40300c6a007003103180d900142003241d113030344100d62708151a0001d00b40003070340c800d00481c290342183c00c6281451019690003c841c06100904042c9040010140030345501144d240c004010403140c4c51a0011402940659902d0310703640d80f628484800c8580307049601d42d98218442041150100350f04034407131741e02c2080b20010b003060008201ca40c10414a410402d041c0c026a180103034960705440348007604074101d = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 514689595 1250 514688345 514688351
    0x50109050702030d0506040213030503030a0c051608090307030510140105040504030c0b090c0d2306010b0a1812060204170303090d030b121b0102011d07050f010c0609031e03 76
    0x7440020b034403031040d00a001c102c95142c5c1d00185294840360129002920804c642c0059940c1c1d9080c800d0300c80c3c01c01d48100510600340070001c4910342c4a002611016280801110301e0480140c0d6012291750080600da60540641000000402c0b024032886180c82c0b254640892180c1c006c0c15031044003081600b03c244034038a8001400080f99000014941c6c5c00e40c030241ca8034981e118100c03031928010300344039120352242642c00740c0010011040320f82d0b02621081c038040c0d10b25100c0c00244584070902400340d040b125005004c0c819099100d03068422000c1c6595034001c25a60710b544040260302c00c12030064540780e400245c100921228201d152207c00c0c9400095419070605201d41034031a042c20254078105601d40c4181e003240d03996880a1002d010710001100c1000440c0070078207104003c045c10850265203000b141140c5100140c02d01011074003070801912040381070008001c2004030781000c2504009580301e402001400034490b8588190182d01c3d1420203100c029950030b80100213075000b41c20181 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 514690845 1250 514689595 514689601
    0x31b0c100608060a38031f09020906010c2609030106030501061401050708040e0c0904050708091204050612070207030c030525030f110114040e060f0103020a020616140f0d05010905 79
    0xc044803104a0070525012003100e00301e014000b9103000080712801d4030b80d07020070407d0045c21a4543c813441540b84241c2c1d045000da9606001500d520000101c042d050000ea41a80c542c402c0c18200c44210580c3d000c8420340c00c0c0703221140440e003120700c0ca40085603103a640301018400627503040d103004080c1000346000c5140c42e40552b11050140514411840c11090141c0482e000300c458000703803815444064010001443d00e044010005101603031690f4050182e00f008405114010781103d041e01c1b8050403d518200005c2800002034038003c0c21401103014005000c800142e0111001c001140164010725202c0700c102801100c3c0076450780c02d220904006c0ca0100700080800c00744401e2503402602400480202d500181c9826001131103441100c0800140840c90314070803540d40b4003d8108ac1c800810304444500194101d218a211a4002d6441180010001712410041d0441e054051070020785001040110f140c20381c02401260841c42c401046092001c402071107000c0c010103e02d141404941 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 514692095 1250 514690845 514690901
    0xf1503030d020f07200a0b03061509120d0207030b09060103150209041e2a0c0b07020a0f0b1504090312091112061b031b0c100608060a 59
    0x4824140c0c1e0a01c1280c020603c5440b0424070f20035507907400e42020300000c68100402c2d010b0840d490304403030302d0311070300300158041207041860064a1040d8006014003030f0111404411101a4016180c07550740009500c140000c8440144445001c2000540050a01c1130440c540070450010042c06500e82e079000f5801040402c0c0c5054000b5001c9068102c01a80c49e0300c0076000c030300640300c07034403040006800300d0004040031b210300d5220190795940d07409210506000c6a0203185007108840c0030b40300003429080c02c42c020650448119070842244c0c0100c500c00740e0140e5810f50307803100d05001074403107400510801c0003080003401c541c441580c044904001c5540d40d039401500200154040c1120b640d903600d921300400042c0481445103c4004286058001000590966941017110f080e42100d0040702481c802606c0c1d241964001c0144100c00300d40c101440400352269007101089030914850000d100d040b141a03481510050505100a010145051200802610b1801461000341009020a0100c1c0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 514693345 1250 514692095 514692097
    0x13080a0809040c021e030d0f020301050d06020a05040801140105010306080d0f0f0c0206190e0a08070603091109040501060501270e070903050303071205010e010803030f06270f150303 80
    0x1460782110000f0b0078500c03001080b403a10882034a400c5000501c4402244c6009000000e0f010b61200720307409104072015400c0c102c0c03d1340003c2c030030540c000740001030320400209150040c152050140c030707080c2d040541c0d80c1440c03800d42d60b2000c00082d1141d0b540c4014083c47d60b1500548019200f00c80c001c1041d40c85040340207040d4010b04101d04100440c540c180c8142c00d1144011070b8040c0c5c0c0040c2595210082c440b100e05d406840c2c1100c3d10081080c80d03503030703000034180960408212404d48019001041c03034000c0680241244a1007103581c08059034540c4400c2e40c07502c0324580918010b000004060f4240800503043c43c170480d081c24503220310a6420024101280c11080603940e50130899411034403240300c00e584002050304000c0042c0070100402c01d030194002034007010700c9090802404280d80e92048010002e02c02e0049060903042000051686c071705c0c4214103600200c020b4111000707514140340140c03c0142c1204104030100c440810300901e90106403d0720380040c0c0307541400500c0c0e500c020020350f80b = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 514694595 1250 514693345 514693357
    0x17010b01030903020316060b060f030901050105010309031d15070506060102060a1b030e070503030301030510050c09010c081b03040902041814040b1e070f0f0309030516080d020f13080a08 82
    0x21400e03001c661b480030080160040203001902409070758451941001d660a590011100c1200541c64900005581d612034050441c0c0c064040e240c10a0901c0440c00c24130100034418107150300240c0c0309203d03115180c4400c00420420303019001816050905800080c05c1c000c2c0544140d01846c2801c0d19590041c0c00d0303640d085018001c505002030150742811440d824942184d01441c0c0c14000800004207004021030b00822414a0940400040c2d030380c004004540d00a000815000034201e40b0382c0350010754280018a815802c42502d4045c0071482e0061500d15481a004010140c3d00402c040000141381c5000702c3c2c02500320f0005108802c40c620701800400382c000d10141c00840e101010550b045512990b01042c07900302c0e41e40340d0f070303d10300b602c3e003d00040200011000004c0035078020840c003c2c884d01c2410001640350303039600c1c80d04410800d40540045483e2041d618010200115100001588003c00103141c01281c2d154407865081d2060786580200c0d0300c946c069411a94000713001401030310031184 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 514695845 1250 514694595 514694617
    0x70213050606160f0b0a0504030f02060f0103030e060705010609020405040b0108060d0b041505040f031e0905060309150a060501140313060510092c07060e040b011817010b010309030203 81
    0x403030202414070354800d03182c034040070346000317018400e10056070055000144101e000c0c0d00e900c4828002c0c140e040760f49203802c860f10701481600d41c0051000911640c2c1280002200614990400f4580c1d100c2d14210307501903004043c036581c005000c015900307007409848520102420302d85854941000818842a11203078014044c80c0c60500040030850040102140091402010425460145860b40c81d501d540413003900800c6a1070110400812a0003916141030440d0703543d0000b0515100030301c03100b504007400000c0d0034012901c6513861a44040001445060702017000301d00145401c002425050414004255404080040040c0048420b54040030310354404400901955107842d0395040c18525040380b405181400c104040c4241030003040341c200441c01100c1d00b92008041005035a6912911031030300403c0c4e500c0000c100c0762415a006030800c0c2c0301030400402024030358142a452100c1c503009000d403c2500b054200c61501c091054078000042800c0800c074510f01d41d10069960300602030410 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 514697095 1250 514695845 514695877
    0x60a03302a0c0e01120302010b090c0a0c0816030e0a080f030f0715060e0a050601110705060f04032103060609031536031206030c0e07050c06040602070213050606 71
    0x404018420007000c005090f0a520111556180d0510040503014508103400541c2000110714841c41c0c12801a4054039155004c0b510b03081d241401070302c80b00020030003a41d2010b414002030b4a61205d4060210f200e40c842c0e07603820310416089080102245141d002442c06501c08080403042410001c11100d03100d80d105001621003109240c40d80c146410704a00360407181c2086000036051601400780c0303001310803d50043c4055a42e5600465007681545255000d90740184010401400e00c2c0c402072000001168583c0d24103a03c81c0c450000300a0312032641c00803c13107800c01007001e29500d4171800b4081c185518000740c05503c1c40d128561380120b0744500000869407a41319040f11880703200302006580135181e10f440405058043ca007032100c0c07012021350104602c2c1171120303d5901c0c94401c41c030035680c1c07210003400c0540c20138001d4440c40000429501c07e01c103081000c0d4540402c1004480d1041c0d00c00e0034003580e260351300d04c144801010b502107441c03a02030408090003000d40e00c0905070b480d4100a00740e20 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 514698345 1250 514697095 514697177
    0x60321050f1305040c0c060c140405010c060912021e0f1e16081e060112031b0506130c0e07140c030d0603080405041b020312060a0330 59
    0x1a0a9482c0d85070f000c43e0740940b13001d0301041e40d41d030001302800c9500c0c040c1c0000c200301c00100009840c0c111900c0c0000c030503a0341c10042840b1940c002d243d09010680a181d000414000b07590303c880b00d14003540b0419015a00c1807041c600944014045490803d0443d000703400c1030f01c4103901850703403424410015017540f03280d05000c1c188101c080110f13a10503c1200c0e100c1540c0c41d84d0b503541d6038403401074030200024140f285000d00010100020880e040300e0390070140131310688042d1421200100702141d100038130001c1c285420701041c0100145402144064020910301c2010b21b041c1c5c9449005da4405000c3c000f0750410000c0c103039000104000d103425071007030080c0c0d210140003040c1e013075100c1d41c40100d0143e840d016000c000d2203400c0c8040e005540086d58100f0210006600f190842110700f20003400581c02000125041054451a9500b1080151803101c0c09500c2ea6500c00082050702204045406642c0c1c0c1d501803d1b4400881d01244003541c00e01254140000010701d05600110220415210304181c1d4 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 514699595 1250 514698345 514698367
    0xa0506010e0408301e01030f110a0e0703140601020c010f02120a08011a04080a060b1f0804050115060c020d23030a18060c0f0201020703080d060321050f 67
    0x1c82d059189550506030680003c00c000c100c0c0c104e030080f20003064050740c200069901c0c207151921500012500f03c242610b03032071651361007128005242c04a5150000e00200351a80c3c40d400c9245019060300354100310245444400203007101c5a005440701c0000c0d465082c011981d0300071824008942c0700380f80100c2d441c40c11500691405d01c901c1d8610b400781c00c00246000da01e650015445042c0c0d020300b01c0c0c05011040d88500301c00940101e0041c0c1d0800c2d001803030001c00140003680491180f21000c0c0100720040c10301c1603100f55003210b00d0040d0002c100c1150800040040a02c109042c030814605508151400e0510041c00c0d1204540028045c0c00c14502210512000400404e00c83d400c402c0b0b1444c206410100d03840d100c1d000100740c0c40100344200101d04e62120707089600f0040c0c81195441c941c0404103502d440e10b6540c0d20079421707030550180c00c0000c000b040c4908000c00c217004461102190140c603500c0c05542c50324000554901487d801004814401e0788403044a0300501d01c40d9615468020110f9 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 514700845 1250 514699595 514699597
    0x50a1403101412030408010b09130b0613060807060302030402040b040e070b1b070602150703020301240c05010525031b030e2815050613050c040308220501020a0506010e0408 76
    0x850f02c0b000348404540040d420700150014800c1102c00e440410040e101d0300e00b000d804500b0740c600180800394200004840d030510703004039400000d501c0000300b03905903200d000604145064102d0000070ba0000204815818035000303075042c980c800e8400708000b4000c07903c80c0392960350703074081c14403548400503403c44402c4000280030107510b804010788110580e92075003c0e5485040700c0210301c101d240c50001500741030092003964100c0f1104107040d000031401401c4005000e11045914052003400e802480104200b4400c0c944a124800608441140110314000402c00010341d000b0805080482c8200341d4200c07400000f48610f0ba9003008503414848101d128109100c07205803100c1c4a40c280f00d111001183c0001000301280120003551440150301b402c04140c1e00225481508002b0b181d035024902d08441d44a903a00c00314080d03545042ca80c8980c0c500e4044c1c0c1c000300080304c101120b104644403d100c0e0b03c4686008040900080c440c0310216035174641c9907038051003200803044c640c000060134014110 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 514702095 1250 514700845 514700869
    0xa1709060d0f02030a0b06030103110d080c0609011d0c010c1e0206030705220312180915150e0d150b370f0b0f0d0c050a14031014 57
    0x10302070140b11a1940804000d4008407a041c80903030620903e43c02e40d051600031641031380d803c800080d00200b001c0060120350b0724150000c0340c80b2002007002103203a0038144490742c00b941752100003041100d5038250500b0b0000c008200e041840e0000600b00c0304980e000512000d1142d48607101d00768002907009150012030318404044c0d0040700001c1000100b5a101c0d0081044021190305143c80c1310642c22041c3c0361050f2800000c20329400c01034038102c3c01d070003003104c0c4100380d1110011502a9071240c00c0b00c2d05880c05a07031f92110201e04280d0034092031001d0000c40c48002c029181c664200100070001820f07130415428007900703440051902c11034a00300c5c0e4101420300716002d459603204040c0510050340c40d20030110300c2c0c008800000704002404402c2d01c40242191a1406207544550a119024809a004000d800410342040003203402c0e5460341d002d00707001690a510742c2c5490328943c000203090b0a00f03070018006a10410000c0010743c0c045600d2031815204c1c0030700c900c03094a01c9580490540c032020 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 514703345 1250 514702095 514702117
    0x100e07050d26030103260306010309050703050d0207030512130b070c03021806030d1106071d0a0608070f0309050a030c03030b0d2303071227091d0a170906 68
    0x9080d40682c2c20341c03072000440c103c85c41040410302030354000d9542928940c00c0c2c425242c07180303410000318203150b00c17a0300300c912200e020340155141155070303503134185c580000255503502581001c2810424008280140407841d444001c40600d000501c401c0c20041d80300c2402020300300702000c50441e052003004c0807400040c540c0541103030a180780300d16000d291640100c8103203220784294140031105030301c0340440d000595210b000170246030f160312600781c1c3e040c00c0940c01a0f912111035205800b182d17a600003507000801c1c09458003482c609007502d00410400f2034114460a050400310810009840002d440704055098602000071102c0c40c078084024001407803074a43d00568031403c3c0c0082c031100561880703071110960103070029000c0410205450703006003007020f0f240b188514062171a06020360300200320060844000b4000c04080480c070000320015401240580b6641c56011a50102807100c440e0424050401000e0046090340d82d03030140280401195004e88002c58128215284e84090380c0091a80c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 514704595 1250 514703345 514703393
    0x2060a02030f0d02040929012601120c0e1315021c1d01090b06120109020d1a1012170d06030503030f0606030907090b0d020a090e100e07050d 62
    0x801400350f000e90028001c401c002c1c0e1604420302e248183e000c51441b40d42c1707586062090605500340054595200406843d82d42c030703024203c2142c002d468180001c0c0606850520000000018100441e42401a0f04100d0110403180240315141591400c011030403070780078145c221104164241007004e03002ea07840340503410440f101400c004e00c040750096a142da50100e4001122402c070001320b0300740d408802d00503281402d40400300c0c2450030a0105401003901341d600110352800f00d40c1c0410b001c011180c900b500e0340b40a500704510000b44900349103800c003003000021404a401d084007030980c0b060072200101a1480035904400d80703c240b034107848030032403101c0c41040710982d40d040a64503540122524844802050000780c514a001070960f0300507071b020300046c0703400341c1841802d4009000f2852515030003a800d00100e0010ba4400488038080c0c295044082807a41c9a03468032454046a07880541144e8181101414030391400035044040300c000b10380240c0000701030f050215056640152200c0e4506c2 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 514705845 1250 514704595 514704607
    0x302010221040212060106050d180210050711060406120b0a080616120509150405010f06090f18050d031d0106090c021902030d0302030402190e0105150702030a02060a02030f 76
    0x34070341d0202442540250303000d0142070241d20600d900c0348000d004401c0428001d02c01404621440d500c10500380507165510b400c4105290001050202a0488007000a4002414104000c001e9140104610301644d1031070a00381041809480c050141c0e840807140d55885c44903449a03500c0c6101c0400421603a42505c40c541084414000d58409440c070303c1012941c00318504421600703074450103104842c0e00f000780490301c4c07103074280e64501ca00162064032a90340350000f408201c01c452040703d00074801c80c07000040c8c072040001140c0c182d445050014661b9420035580e038000c90000304000803120814640060b1031144040c1420b8104118040d01c11150720b080e03404154241c1d9a40285070702036140d000c4030103843c0c5810b440c04400d202020020742580060800280700c2d4002e40113075801901c010200301242407403d001a0080e10b90341c2c4003c0b001060500100444c1c02c205202d41070041003120a00d1900030f8980100c0e07903c07614050000e00809000600f001a81d10a0080e00c0f0b02c07003500c040155943c2 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 514707095 1250 514705845 514705897
    0x21002012325090905100509060d11040b012f060105100c0b0601030b1804020f0103020f04030b0601030908040f08060c04032604090e0a06061205060f0403020102 71
    0x1007010380502421815840324903215442800c5058401c8501c0c0782d80c00540008500308803a4101c0c00e9000c0c4003032054000b80411400d0850003441d110b940c081c40c0360140d940ca8003041040000e0080d142902594030000200e0104c0c0701c01000c105ca128007079601050700403607040120744a095091010b150742c44034505484c4000c150303454030845c0a100c4412240c8a0b40c80c0c400b04001d0303c4054041d0700114907042c175541c0029011101c4540e11030414100010010021404a1011022406490011070b0400100710440c50108100d0000c40800e10b4114289031400c4e40b018154850b0f80000740c0000c03003500020b50f942c2e05c40e4102d041c03180e510140305030300c661780c901c8480d610083d10f00946034a4003440c000517507815441c000341c401712504501034405596524614140e1490b00b442420b00e4850108804640d4400500601c84214002c400034040c6401c3c40c1845021280b03682c201d03050030201c59180d0800b10328001040e94000d078000300300000c59100c9240036402441500c040310214468a29040700003 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 514708345 1250 514707095 514707101
    0x1030b0111010f0501030b010e010e070f020a0209041410020c12091c050303040b070e09010302041a04020c0d0e040204050f1320070303150608150402210115050304120c05030702100201 81
    0x80b1f20030105090680d881e103070784101460090040d0446030104100040159106445600c448049401650b0010080341c000c51444282210181c848030f90f000802d45100d481001244880c0030780103400c500b89503036a80c0117501c13501981050020010007150500c15980c580b1540541c1304541618500c09480c5841d05035140e8004440c01e072100401400000c0b01c09008006060f4154001030803441c05a085901704001802c410742030320a12480100c056200c0d485030302c01018070070400e0b401071840c2c1c06d440c5401041440b02402240c001e40c0184020081c2e5200c011509030510411a0000c240b011100300c03100c014006403948840c0d04080c03030045150303a00114002d2491034000d0380c061041608008061a1070f001d030b07101d0f52001503c51000560b8200194081c0d0041400c020005854406a0840300aa10305014170042860343c00c8401004034000c08020b00d03281c180b03130b424101c0c154902611021060800030001d1014441c0027a1440100315050080701e52850307005088450785150460000d000b = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 514709595 1250 514708345 514708349
    0x90b0724060503070608040f080309011815111e0c1606030c090e0f011a160b091510091104030b070e01030e1203011401020f0d052a060601030b0111010f0501 69
    0x3d00130300001145162040e6240f6210343d030850b10a221641c2159a0800300c2d41c0014152102075680341e640301c83c108101188245414003910007102c00d40a80348400d804c40d2442c1d242140c14400c10001c000848243c82c80d40f2003000740e005111a15a016282c186041040511302c03500c0c019a0f1400100c1c0464040d401081007201507580c2c1402c813500d035900c82e28000000c1e01d542210142c01d1004006044000381445004840e042c88141018a5a800c80001c0300300140f04540071400a800c00046135410030420a452030340c844101c2c0e483c1440d80b200c4030641241e00505c0201c5445a644511030074141c0e007120021580b0000c016030b10715040c80700070803800b18404001c0c0000e040502c22620303c40005003048180c0742d04501c1d24510391038025151f580344107501d411410f6004400d1010541d017824014101e0300e1400380c68869840c0c00118034030b141e01200d03000c60341814406000030b00c036030040022900c0d4019420b0800040d04460400103030340790f000660860790550708217481100901410b800a0381 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 514710845 1250 514709595 514709599
    0x40803030709060f020a020f03120d02030405010f0c0c0b09070b030a0b0a240e18190c0305011a09010306270b2407060f090b07170106090b07240605 65
    0x80c020340c40f5201100c0c00031903800980010782c0003a060f90054a05800f403861090720040480300c9007540358802560341e40280c541e405d00c030396001c402c000502c04280604101d0a6003c0000c00201c050710ba0040c00d45030700d100010701a082d6000009030914010040c140c09010b08800080d00e86c40c1920300240949049000a4080d2a14160024141440348202c5d00055080036405180c481c46020445448241c215615440f819004060402d14014a0414041c500910608200d40b8401482205403a68081405d0404d40351070b0042200c1440c51452960350702c061503144d55203500100049019041a4004016003070300c00200300b0001e0390307070495140030468400090042c02048800c000c0c85da6460700f10201d06490310100d005103c40b5000007455614410800001c1c034000c00c5c181c0c0d008aa043c00011030740440c1d8802032060542d000680c030749039014090800d042c198141a0001c016141a12464040f407001003110b00030407481440703a10000400c400c0604001414516581c017034000c030b1158034 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 514712095 1250 514710845 514710857
    0x3140c0307021c14090105160303090b13110d02010e0a06030c1202040311061b0708150f07020c090a021612140a05040b1315110606040207110d03020c060408030307 72
    0x203000e210f2100140104104685a035040101940000e10840c2e020301d071110704000c07040228000c0141d9508441e44031a0003580e0000c1c0100e0a40f0b0402c80019014146625549200d040c000000310110541c04202e0016075010300030445610068410355504110140d11100304580070400540c1644a0b5400100607038031118500303034100c00c009c03ca12a901024154407500a480019820300400811a0325004004013207050450241c0505124039900300f45a01d4122070103481d04036000811007600400d110711444024140302e10065544c13144142c0d014010484100001c070b144403558152200f9225441c6041e260105030300c2c01082d2600d00f441c085010807403600111071003010700c01c1540d1058450380c44c1c040c078250a181c08002130b900f10410380d2961501c844404200d0309801401c00b00b20781119110414030180c403a00d01800c25900030240780c05644140820001b18464000c003003210103084d9402400181c2900b03003241400191000310750022400940080c640c07a0000081d4880c0ca03090f40c0e00 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 514713345 1250 514712095 514712113
    0xa030b1303030f1104140a08071503060b120f0a11070303020306150a091205101d0f0f07050d11030607211424040507020102071412040b0a03140c030702 67
    0x10038122042031060a484e090184420320503114a52501e0010300c07402400030249036650356440c4e2400a00d80c101c003c882c2070782c0c0d4298504a400d4012103000d0024206c2150800c1c1d4401c032160100c010040c07030241d10b5049034011440c042c0065100f0180c00010600312a503440040c24041d01070360050b9085406200b0b40894000405030401c00c1ea80819081d5807031410642c41c11410302e500a4403100203075064041d0304120405410030348201030a071405441164100900204217906200200e00394441a4020000c000e400303080c0414690180c810494825041d0340107428441d416202c0c681c0072a03010710511080c444100c0d00071020110542450002982c5a07482e943c00c44282c46103250340000038000400030904e005010120f5031480c40d80c02c42c4109203031414400080940d20b0a840b000e000d40d60000d02e031030a00c004860840500d02c103003002080071100b80d8800001a02c01c521400d1050000468114a61072080c1c002400030aa492916112801c01c910281c000380d00075141d4201502c100005 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 514714595 1250 514713345 514713371
    0x905120f1207080901050a0e04141503070f05101707090e09010b0604030204091e0813140d1407080610140919050a0902060c07031e1106090a030b130303 67
    0x31140480e40c04000f003400c04014000564554000c1c1c1910420b00581e425881059280c0380304501c43c070701c0c01550728485810046800161014204030590007a04003200908c182080b0b0364511040340c0d02522800e102610348801191081c81c004600602c060000090140721548003c41e901941c0308042d0100b00c3e6200c01034420300b00d81400008035080341050008001501d4181e000207811030144480b00070f00640440c100c0d400d40c030005c208070f4100101041c003142004c8214000c03406070501000760310030118a04006a1803011090005012904040b9071610802c018001e43c0c000f003030408112503c41c1412000d0800f403482e20b020349415812011810000b9190107800c180c00340501240d0300d011800f07000f1a0b48094103009185480f0651500c46100041e15a05c0007420b4050810b400303488040e06514200007120441341d0700700d01c000092083c03c4045590428155145039084a00e60359400512002c60b00c0700d4150360026081c0c007070303060800c00d51300c0360054061916807207558204010301d07195032 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 514715845 1250 514714595 514714597
    0x26071202091e0d3f0804060b04062c1806010323030d2004060c02010309020f06072907050f030703060e04030309050729030c040302120d09052e0905120f12 68
    0x1300c035000031a000c001c200400c61960081d995014050404102c6a44070042d640380000207400001038408030381034181c5504000911680c000c4200a0110f072141040b008081d07550006000103400081201c4000c1039944005410820034454001030780e0300c0320070294040e0000c00459104551404080f50b12071850041001103405a800603119103100b0906600110300420321190201d802444c5041d40d0115580c401010300394003071040c0d19518040c0c000800c6c0c0322018856107440441c003a040340620042d1340d00721080d50040b00030000076036165030380c6620840242085600100c0401c6400f000d1109041d85030300158105070003241120300590341c80441011408084014100424510f4081030004022100442c3c00460b0051124185034403070700060400c08201803507592a90101c2d08050a10b41c121207540000c04049840507000c4128003580c01000d03070850000d080c49051035004100c16801000800c014240c00b5029080340c0c1a4501300700e0340c901c0800c1740d85009214240d00740005c0e11002e0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 514717095 1250 514715845 514715963
    0x1150821094507030906060308030c0912070303050412080d150302120d1e120213180218041805070f0f0f0308040603020a26071202091e0d 61
    0x80b2682500e6a0300d103c101c0091040904c120381c05a2140800008100c540c8080c0d0702444404055aa607000e0700720401500858030f0340a820641c00901c1c040000c40e0308541582c04175017200c10150445255442d203109540b050700e1140504078a03009803030305100c000000300c9003900d109495190400983c8110710381d8564042402c1c80024400710324038401143d130846890001c44141c1820340054064401010590b0040101d4408050350310340304028046510962215100b809142140b4104240981030081e4512400c4640a641c803130044002400c5200465802070350028152070100392a058000c0ba80d0001d0f1084030940d0325208000310b82140c11400d09012261700c001a98074003480c10400340d02941020090000b0b0004103290482c6101c10b142d5000c15005000d842c0c01d1040c981003101810703402c07080012003007480c03052048650b9038076504400c5000c07000d1400303007500f608032000000b4911440c03000c0081c0748042c010b14860310681c048010300c3c004c000d40d01201c0c068542c00d4000380f100071580e03 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 514718345 1250 514717095 514717219
    0x30301092415020a0c0e1b0a1407170c01090303150602250810020a1403010b07020405090c1201050109060b030c03010303030c0210110901020115082109 67
    0x508410071405140700c070035616501e0240141c40301865540ca03103030b4001d07000d68032a80d9140003034010850360030304d80c07000701111280c0300c480241420423030b8400505494000543c2c0c07120080c001200c0d028001754085020104003041190f40c0d4800e00545064042c2052030b508501090034101c403031001c80c031404150001c0d14919030003401601081002c4010a9440103078407007038041c8401000c5408441404580340c0c560384243e0150b0781d80e001110041000485503450100704000b44018450f100340307402258507442d0125000310300c0b61100c941c3e00d81800e60300030344c050344020078081a52803004107420050495160083c10402291340740d00c4403c1521089903100b040800400c01800040d020780e1141c0781d0354034244121440302c0c449082c14800c90790f41c07240390300360243c010920030240d6174240030310445d40d40345032102c0c1c54040c941001182c3e6141c0d820000898007910207494aa1880d19802f62904040300a1401c0c0d01d0882c2403448920356100c814070351500e4560405910b070981c0c106004c80c28007540e0 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 514719595 1250 514718345 514718411
    0x3020c01110c0d03030b210304060801090209090103111305010f030c120809061b0703030c0605060f030c0d020402210f15010c0b091e030a0207061b022103040803030109 74
    0x3d10b81d001c40040000c0c050855001e500003103240f2080115807049809448000c00035540c4504020010742441e40c140d010403001801000100420707200d60b15003a0440350b10014109810040d10300140144083d0000e00e811030b498800009454100510031008030f0340034030103a403242c588a44041e4255012024080e24144081003c0701c00d50801000601c06d0710500811900c11005030403130681480f48980c41500040c0c0b4405654007031007014420b0355002030b4100c858070340421540d00401d40b01c0005d90406032065030240e51410a42d1960b804983c1d142c00c611031985040c00c1c00c0f26000d540c140e000c2d140701e1040b034509800a55032164000d2103014118058407101100600b44c4e9550500b40401814195240101c4031103103010100c4403840d50f45030b101c0101858682d00318240003490200307a540450104200c040032000380001c5c515401c1081501910405402c0c0080d1601040c800e014a41547e2039100c000340000700c0324008400b03941070f109050010311180180440d608541c048005041840820f = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 514720845 1250 514719595 514719619
    0x1120e07030b1b04090b04050603010c0c030f020f01021b210d02300109051f030b0c0f120402090c2a0c0d03030e19080406030207030509040903020c01110c 68
    0x200302038100e54450f0b10460381c1c00948500551802c000e03000b507030003800c0003900c43c5c1d03540220f8501400b98a0340315505070000c00c90b0981d00e00c001000e00c2c0d00140d0140610000a40c10910740b031003132003140e1191a20700700035943c40c002000a00070311540f50303c60b4010360241441400700310a0980240c606502040c1040d8108462120210025070219400c5141450252840316912524807882070004041c028040e10940c1b6000c81301c7c0c1034590051200c00100049558944140d00d00018182601d80024000020f0703942d0001003c0385104501c0b07410300740080440c00e00b00000e000308509100fa03100f6141500140c4846107159000e0013860490680c45044c1a0584c41c0c00c0c419684902d03902d05000101c48108000201246c030f0100c200384284c0000317440d070b08025190320381003088102d40000840080b44040e0541c0b1421107074051400780e07400305500001c80f60245440780c0290745044000400400080c561441c0183da242c95105600d8045500190401c445a20204110001c0b04014003c2c018001c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 514722095 1250 514720845 514720853
    0x1704060804060b0d02040c12200a0302071406181b010c12031103100302040b0603251412090d020d081b0f1201061106090c010507060f1a01120e0703 65
    0x2e0f07509041074001c0001c40d40c690169969000c0e0100380740c42504c03101d650f400000c1081d01982c02c050f48400491410710756104000112400b00d50040302c44d8580140c40b41c0d524600503c911007030780c1d050442e5204440600c4040e51500c41c2454954000508075081002006000c2400340340e404422800328040d440a400415282120720060712014640000d00012004100001d81c0040c1c801c58100424201c2c20300c2181040e100303400c1000400c403901d6045145c4544120701201e121900003c5204120301f0b4608000e0044082102004560f62210703102c1c0f80250443c10841011202c40d481c0e80710711414540706c00d0000c50041c0311a501603660301e1455a43d8254900000110440404880c0007040000c1c81305c0c0c0c801002c0e21141e201c4003007000e1503525240004040890f0301d12100d0254000e01c007070000011000034618001902820410b0700e0341440c0c1096001001141059601103040c41c80d0000e5984000002ea04168400d072603001040788864a003104130341d840a884c4607103070b0004d80240041 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 514723345 1250 514722095 514722101
    0x1a04030509030703121d060d15030b25051303111207090207022e080403270510031104051212181e0105190207091404170406080406 58
    0x10502a06000e4038005008002c2441c01c1195030083e14008004014051815808030b0102d07001c080100340d83d003200130104001003140c441c100100c0c00769907035103280076002c803019a14080219081600440d0518003409000b1290b08107162805030203000c4c20000c0301240c004ea007502c1042010544a0220750303319074804140c03881040e1201e80c0504080c140407c00a030030070804000d03110300d200158032440f41d841400b4801028415101006203100c03840b0311b42c49004c1c031120401143c903140c00c000e01d48650605039001ca1821044d805202001060403009a644040321022188141c90f02d039003540500104404035000c0d90450743c07060b90200410402031411170ba1010500c0030003825602d542a0b043c908214951160300c40c002c0403c03020261600506d400036005400e8181a1004a07a500d1641e0000300a0300c6007060340b001130b0b040c0041110701e00744204030b11000b030140400100018a1001d014011084041301e040340d5035141c01c000c07a00003c01810555044410b80e440301452900d80d6030780ea20103 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 514724595 1250 514723345 514723351
    0xe1303030902220603050d08060321160b04030f2f0705030304030b15030a0c2c09011d0705100813051006050315010510030e010213090e0d0207031a 65
    0x700c254043c880e1814103403549025003024200f52000a00e1a20354a425400d01840444140c20b1007255070030841e15880220700801000074807841030b00345c60310b4120f0216603070094903103240820048099110400c010702e445a40202c0c003940303941c0380c1500501c42c100c4020101241000400c6203c01141c10030400c003426441c441083c400a54104646070380100745140c111707074000c0e42c6100380e80d01130102d41412001c61240c62030054001d0821007041d600c4130000c8640b10302c1407105a410340041440010f036002da071044860141c00400a960410b10300303040c06000440c4100030799511105960302c035044001240c104840c0007510f5200c00140c0c030a41030f50003040052029800203214104100021814050140c04004600d40092924281070138140313031441d40c0c0300440e00752030010010300940d592084d1943c5211000e1801186a1000180550190082040360364400c2004a4042071109960704840e005141080072240c03800c1041000300d0343c130040c92002520006041c0501569414a2643c50754 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 514725845 1250 514724595 514724599
    0xc120309080102070305070c0e07020318120d02060109110c0631030c0c06080403121a0d080306150304030e011209050d0c2001020601121109070801050a0e1303030902 73
    0x400d00303903141c1e126400da03442648224001100000c8500030081d0fa01140006030840c0c13440150185000100695179210b0400c160302c4d580c0c220b1075000341d40e9540c94190300d44003c1140c00c0e0740241d504504083d550b545c0c2070042070106810b200c0e102e403841d00408190703103402064000400c0c3e1901c411a4400c0c08818491441409610040a88500c4040103608d85800f40c8a540d07028000c0c010707420001035140c17845d0020803c1020080034400071071340c84490940280301c0701034005601c4040009501e40c2c0c01200107459004003a405c2800180070320707900503600c10359043d034221005541c52089110a403000b1100100800d83d8003925403e1544a4603c6c00e110303045640e00081c9851044e01c4036072824428180740320000e440c9002c207600304412485a0000b19028200721118506040000f03900c0d240c050044000803200700c94040b0a0204610299200240c00380284003641007082c002041420309008190140d8a100e0002560b81e0003110301602c00d40c2c0c4074840c60460f0072a654210007801c0c10704000d030303 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 514727095 1250 514725845 514725857
    0x70303060317090102010b04050903030a150f090f0b0406080a0b28051504020406020705010503090a0b0c0304050c010906050414031006080c04140f0402010f030e0105072a0c1203 78
    0x2000003401d4a5584000d84041d0702540d0f22020741500090030b603240c0000250040342001c0031321500309800000e07290800720000003c10b40001a800340d00c004403450b031043c41401d07594400040c52001c99400ba0f45403202002c01031118540c240280300070354003d8824040c503540560110f402103075006c000340ba004541107a240c8442e8044220034200400201140c20f82c175a0b84800307100b1403098805110249500595081d0704103071070520065151400d511a541c1030020000008500041c02c1c0310808449a021149000c41c0c10f042071154080d8108031030031101c1d13104180180c1200e60007141c102c001c035455603807020314103401e048162a082c405141d2040d0148544003d12100d59403074001c3c2c50261002c00d009000040c01c0c1c0782040103440d8694401d18141a0110030701ca00c03100a5008154002e8083c05c100a540d0003100040300142242007148045529150521510700da100c0e003100014000c1d4144140b0b4114403581c003000780ca8001000500301080310104000410040c1101400c050281c04d140d = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 514728345 1250 514727095 514727099
    0xf061e070f0606050405070305090c041a1f230a0f110601320901050603040c0305010908070213021813020405061b0708060906042d0605010f080102070c090207030306 73
    0x450301d0200400811100652207940c00c2c881c80c1001c0c42120b51120b080d103030a025500741000c900d920342010b4422607000355220754210305103e09484428091a00142c6096000c084590b074110b1000700c02d40c840c0002502d0307400ca102060142c0038078090910244004580340100405080d00d01c440c5007880c100600c036626403200c50541d410f10441d0b000f0950004511840010710341e003850820040b043c1049031b511501502c420340d84420503001d0550300705503101a682d48840c100700d50b050710a0f82c8010615030a1891110410a140018110880c425284003140081d60b40b010b8042c8c1c050800100d0104e900300000300e6079031802c25a500042206110b00518094072000030031006d6100b04021031000d241d03147c2e03944440004020710350040c0b110f03102600803401e02040c3c00ea210700019001030f000400014040300c1d01650350030030300d0911042d84803241e0064032034a00030014000034852071303840105001001805001c18001c482465074407142e41c41c44e250500c5540313070081d001004194201650b8501c0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 514729595 1250 514728345 514728353
    0x2514011403090609060c040f0b0307180315050c090f0d020a09060e090c0603040203060a0504061104180f0501060c03031508060118050109020406120b040b060f0403110f061e07 77
    0x1140200700710b80c0a4651880c040c1ca810703240000290846a20380d404210403c0f441c0e404003140f8040d82d08510200b0b6480d1501481162160030319030307200c00401200f43c4000100135212904128495402c40d040c0010750b19802d0440c03042c00b400c48840d4218401844080171858002490740381544020b002c090416159903001c021038900742c00c184040b00d130038014040305d900c0400c40300d004010101e5031a451844d05902080e291007024202d944d0068071000401d0810000760403554480300512030080d03c9658819014091140395410f5001181c500400e80040d00103074020a81641c005407603070801003205036412001002d030070f5410182d408051300c020680300801c0c01001d00a001d0465a400d000c0d6100110008503101030340200030017441080b041140c1900000861459050f00000192005010700440c01030420390481e907501040000c4c03a400305891000203001503a0050300035481120074001401505000c2c02c0c250ba42c000028010030001c007442c0e03541c030a0b81203800c000150514a5603a2 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 514730845 1250 514729595 514729597
    0x90f0907110d1d04230a0b18010e0a05010326070c030803061305162607030608010b0109031110021606020618160303080c09060c0303040525140114 65
    0x8440c600060004200c16249082d4102900c40903504480400c00e4511700881302e400c56040b0320200c203403000502c00180e11054540d020300c60480c40a404400c0c1802c0d5100400c00500c1d090203582c0c40b1101e01c0c80070610810b03940c469981a241e100d40b41c0201410848045091100b01c2c03d1a0300922000300003800003c0c4603152140c005601c0703641a40d4590420030b040001c5290100c000544603443d0808010042c15560034030031041041d410103901380030341c4402c000f03041c0003407a040707501450095003800703071a81d03059019000301c45014000308100c901031001100c0e100100c1c40b02a0521903003404110003440c00c09440781c0b0f0101da03030046404210000c20b90b45000c425950003003025070069010018210300d581901107000320860081d00f44801c001c03071061940c1c1880c1c0005020040d8031000a490f0380381039030488129480040c0899250450741030002c2d626407080710103c4076402a001003d0b0310321810b24160155150784a8050b001d80c0c02c010b9002c481602803259241000351150700614000d210320 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 514732095 1250 514730845 514730863
    0xa03061104060813120810091d011a06041802070506040302031210080307031101061809060c020102030f130f0210050a03111c0f060815010905060105090f090711 71
    0x421541d885901d80703200076042c6000188000514075070421a6000503444800c102c107040c65500308001e80340c5440c2c0d52103034003420f5608109003682c503000d404208100040c8035110105000d9001b4400f85c1c404170f02c8071000020321405190011010311003807040c10345202c040b41d040d404402c0d0050170416151203940ca06542601c00b40d025800c00106400296070f0701140a40c0072940000c950451454040035079a02d02c01c541001d1300b0403219070b071080180c003401c2d0800300050514001c0d05828090704c401540040c092000c045900d030b031404800006150060098910403c09903140c02415911404100007010b01e103141100d682c00c080d0715040c01660b42c4448600282250744d40c0d0b503260f0821000203070444626651054000209200c415450800300c035811030400c200341c8021405943e0154814080c0016800c060a1801104604a07000d0109848075040342c0e60081b09100c5620b812005541a2041440c0305811000701c0e122150a03040406d04c3c207800080303d02d8503c4020003601441410a1800307 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 514733345 1250 514732095 514732121
    0x1b06090e1b0a050322080904090510110a020709050702060103030c14010f0b190315020a0905030a05280507060507110405010e0108010b03010e0606150c010911270a02090a0306 77
    0x4001d100f031176000182d0807480403d10462103500142542c44007115800340c141070078410303030311007010b00204801403140d1074180c83d072100c0500c24000d852541c0f0700d05400c0201040700500c140440000d60400600a4600640c8560040c100603403e50300c0131900062941c3c0c1c1030310100c0316001e07029200c040034801d10081c0c414401d4001049014401080301ca001c0c03021001010b1540c00390240007148003501e00d030007440d901200c010703501c40310114180c400c41095400a42c2c1743c0240140201800b0010942c5404a500016001d10210034130b4080151101c10260160103903100707400c00d1000c10f01400050203a68002c0c5002c0d25800f074008001010b0b540260007100c1d1410009004100e104424020f001400404500031301464280c6d6841c544d55200041489225104418605246150b40000c4510b075842402c001e01c500f800a0a080c0c0400380c186540314003500007241040b400c9503890303c58216802640e0003010854488041100c086c1d040040345a81c050b140500c0000042c07600c2c480c800b100010 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 514734595 1250 514733345 514733347
    0x312030114100f0e0f0d0204050405030706060f062c030d020a17040e0c070c050907030507020c060c06040b06041b0332010312030f090f1b06090e1b0a05 67
    0x107002403020660b00c0312006418002e07030449090419070800e2200031508000d4400c02e4203817100f000010342c2c0003c6000d000c0e400030700e040140018001c02000400c00540075040901c000390303035507000c824112a903210745030000341583d64940200d0714505242c01d00d0981c2c0c4a400078130030341382e8000909000c1c90201000140c1c2c0700801c91810800104420040e0000c0b038400c060030545014280710042c1401440c1c400340000c005200420040f01c20701190280c03a020700a440240b410b0b00001c0c00034a4162500c1c1c02603c141480070f0345a25065044034407412030000a070415403a20f5a85440d03a0002510055105488082c0d826038100450015080c0c14030995000c501c0c0e00e4a054400e0744d000c900c0405020460000d0701204140d58101c0c40710341100d901c10f00040220f07880103070480082c940180b00b0040582270013103031418080103100c210300c0c1c240070325140801d02c4101d0030340600b03a500c2481000c0220f06038800800071280d500d58106d40c03141600c0780c540f0702a45080d00490141c0d0103854000c0200e04 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 514735845 1250 514734595 514734629
    0x7030b011d0903040f0302060f04090c050301030b010803090607032322090b0307030b13170a0e030c030d0c0c0f241d0616050607050d0b010806150903120301 69
    0x9580a030740e04580c080010f14549403c14800c000b540d80d05000c0039008080010701c500d0b0024a0008990041c809107804221001c42c40b50300070000c1e40284030540715000b00c5000410101004411a8030b98a40140500d24183c40c039a01a18000b03003c000103d40b00c160400c0415100c9940f0b40202400040190201c605c00041c5200040e05d19051b081761030070031303c6c2a050895544000400105071b90b040744d180703042941c4041205620380c030f40d410010815403810303d100d0700d010703008406004000cac144d48415a0008030b5a0506540b89450410b04d907040c0c0c04008c081142501800b00014002d0007039061072240b58485506092900d031960100080d0154242141c0390000250a018062882e03860402031451100c21182d5400440350b07491841910006101440f403c13105152000d4180c0c010140c46543c03800c0e010281840c0c001002002c5041d091178030b0104190700c1a019075214040c02008e001d108200c144415a0b01d8100607070281e0140700311480403d540700e50001035030090440e071101040d40b032 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 514737095 1250 514735845 514735889
    0x80109181709030d110703030309141212060f1e01090e0c0406020f0703031e09050d0b0604060902090603040609140303010305010501180203150405040303020f072d02100804020307030b01 82
    0x1341d40c0381e90001088440c0819218804000c2294003c49825182c01f02d0341c080306091106c04840c0c0d60310900f41c1d0b48036204c003230301d146045440546200e03411074003046240e61b104000e2000c1004040141c1c1d901c0706000e401400c80108203d00844140010300d004080161910016a02c40005492111025a0215041080d00e904005210708603100300007500340380e851694040c290040c2c40001410098549203441c50261089130351800070310004190840c004c5041c140f20349900000d0f43e07a030740200d0034a4004200307000b181c000c5840d02000038251900c0c5a403140c07030341001498103000895148411401c951700d11541000514080c40c014400018194942120286e4000319010a26101401070003003200070004000d8440400c0015200464242d4461900314000d100e00d0203410281e245c04035949051290b00d00078141c1100008010400d0b041480d000c0c2019150154002584036850140544500d481905034580003440a0215050541c0320750b030b151b070140400d070020000400d02c02038000500d = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 514738345 1250 514737095 514737103
    0x51606020f0f13091e0c14030403120b03070501140c1e100509120313050718020a0909060b162f0f040603020a1415120402030f0102090108010918170903 67
    0x20000b00c1d034100f10880145001100f010305800c181505c2c5507949001c0381c040c9000303201040c1c0450f4200d0003a41c0e00e1030589409065a15070402d02105a840e00000368500d060008611003668016100c40320362440d45121203100f179100c1c0d443c84c1494000d40010f000030f4141550080e480c002060041c0092003045440001110001412500c0990203600f0703425842c2451003c0325007140040c041c2c0744031411941002d500e003840c183c0c8900101d8440b6500c00d10040d00c184d010f05080e21040c3d4804020f40da4600460058911034020003070018801c005100c409402c005038446aa4031070b41580c5c41003501c1390240d9920441c0b40803440c641c8503110b001d81324503140810050349200c038111000c1103020305680200c4e40c0c1400500a4182a009181e030440460303460290000c24900c20011441e40c0d581412000c2000d01020b50f4100d000b841114508841100306000381c409007041039440508603032030b00c200b00c0c000d010948034600c00c0200d40c0602902046072040e0082001d114172001a40d190700c4042814031b0 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 514739595 1250 514738345 514738349
    0xa05060c040b1b0129100503191d0d0f03060e1303110a021f0207120803060103091a07020a020a150516030e090103030e130c051606020f0f13 62
    0xc0c0d4004000a001a5000b4001c0d90106210701c12036106550190743c8207801419240c800030041d0340b10306808244c040c0f1081000c90304400030740d151031420350910400d0724a400207407108415910407030038140030450183e00c10709421090740e2404182d042e401900d2800c100b112602c0e100000e5032a0610000541c05000c1c41c002031554041a062074540440041a04111600b008003000343c0285c41d021448401c00c00c20054940081900465111000a40880b50740303405154001d030043c03100020750340009188041c00150071004203031855582c580110b0003044020300480d07440c03150401c3c0300302101030603d400c0c0c4100e02d541c0003080c034441240100a9940041da0040c05002403121083c0030180e0702c130b0203a40c07142680290400b130300c40310f5160a030340e000e4580e030780e1039084090302c400001030603448100c000d0a0f800648240090026151125091322907811050000c0f070001c008010b13000701c031101508072880c009e100c0182008050081891142c0c010030660f21100400300d03164042004542003400 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 514740845 1250 514739595 514739611
    0x220507050901121e0f020403020306060301090b0109090503042c060f0102070905100305120406030e03040f0308090a0317090132071e0803150103090c0b1b030403050a0506 75
    0x3040000240000308801d40003804070b100307243c840c1c03003406448124040c07010407140d5400c0d0602818803225903117002500715100591192040001181d954141072048024080d00000701059a0b030800324000c01400c80744e1401c580380d200c100400501070514011003680c1900c0400c012a207581b00000704040d03d040039184074499811020502c0380d9a8000566104440041c9004105641c5507441004001180e03840038200d4003034440d200c11403020541c002c2c0103550700342e00c04000900c004280c07281e0b64011400360040c0900c00c0542031000c0f0f5840809080f8900700204201501d82d261750b101850251144e0f986140440085281009503070011a0354600c0150040c40001010550740001c04000144102c00d5641400080403014040c4008600388007003191030a8082207601460076034010b40c01201d0010a0500042007200c8d2076100c0c1c01503400d000d4000405840e030b0360600c014544250b0000030540d2408010b080003507030844082c00603000560144000d0a00303000740c1e00301030382422030080401c1 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 514742095 1250 514740845 514740847
    0x20102210301060f030e1e120c0703060504060b130e0c180a1e02070b0403090b1905091c140105071407110d0213050603010e010218040f060522050705 66
    0x2040052100740c0b41151040d142040a000b0411010790003040094541e4196000700084003040780034030780761b038010400104101c40c5c2c00d00e08280d40d11854024038808403825086040c007000402d1081e004590010700840340001e4a0303c1c0c0c0b40000b2078070800006d071b82004170b840d2a04500ca581e020b001c4100f0303000c810b0704c242d0b00c404102740381c000152100030701c2008030903070791400e5500250451140841384042010215944c40b1103003810054041d080710102c0009605000200b5210b00d900141c0302009a20108241d40700c40484082c4c0340c030f8118a00304d0303411603c441c4003001c0176400d072402d0455050040c1c05032413034512080740c203a09585c4000d0018090100611017110340c10190b00442d144c1c203400a25000762580c2a60001c0c030048a4000069031102115042e086040310a5014902a200480c003c00a100c4107186140c02d0303005e141804401c0003800d54003003d1509141d0408980b84440440c00140d01d5240c60006011520401020386c038a05411906078000c441c1c0c2c0306468105085040c46 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 514743345 1250 514742095 514742143
    0xd1d0607080d0e0703210912080702190e1503060a1d0a08180109030f03050f0d0f0f06060f0e040f020702040e0307030e03120906070c090501180b0604050604030b1302100804020102 79
    0x2070100c1f4103501c6204002ca6400301d05c4000d1040503425260030550081000201c000380000544035450a40515204245244040381c40740e40c0c2d0000e4070152200250141545940d9145c201009103400d0140016010a099080484580c280019260948282a02502c0c0e082c1c0f0700e40080c600322030124003814003020000c2400401e00c1701650000540c5d25140241e5a20b00004038140e00707025443c00b14560342c0c148040880092540e40060031886140718040001c83d50f0303103074100c3d5001c03803101e07a0002181c4c1120b00403040b41025049046085003030304026140c40c45c0399010401f15007036662800115000800c01c0750800d5132080000c20b2202044008002140caa014000101d100303810800b4440c80b4002101410030261003208401070500c002e0402442d1b95541011b003c282c0d48c400d080c815140340011541e100c0c135043d000c1e2401e0324070291a8a040c141141e859000800000e4680d2142400c09082030300180c1d15508c8281041100b50750320003c9003058030000e85031884110209011001e01005 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 514744595 1250 514743345 514743347
    0x6094e0b0a140c0d020f1318110d0b0d0c120b0a0504020f010f120603050c040609060e13020102161412030a0e09060a180e0d1d0607080d0e070321 64
    0x2d908980c1000e660b40d640e422000c0c12000074410000315601004010816107425880300400c03c04440c1626140c1c40751901d0000b45204a9800d10080041c800d401d20180e645040182c2c0106041c0c40040c207651081102074680a0002002d44e100000550410b010901041080305030513030018000300045c401c03410203500241d00d843c101f402e00d604100604041004082c4245800042c040c03000c3c604103c0307180c590034420344520f00d1902c0b1500890400d800001d86070350710300c84e0400301c511444140703006444440340c00c80500ca24080990441c410039100f00f030b5110100304070100800c03e041d01d03201d41d0f060010078840c03004280d4600c0c2e05190020b12108142542168082c040200d04442c03a04140d5682c1c0006210310400b07070010041140030450031742e003000c0581d10031500c540a80044400c03a481200c001c41d02042100e040640840301d02d030144480b41001e00151001d6031240708030a0400c11041c020001b01d9032110302c3c0354000d41c0200010428400101d5081c00c840c003544250300a00c002c07040c5c0c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 514745845 1250 514744595 514744631
    0x20f0d0c020706171003020d03121d071521050601030b040504020f090c0c0304060503060a21121b0503270d1b0306020703050409050106094e0b0a 64
    0x101520402c10440090701c91003113040c6000156a008101030304501107422700800990251411200803440c0c2514080e052600143c2052800519002890100c0c00c0c4116068502030000502c0140443c81540c040d882141c148000000c1d0049207000401d1f00e01000010705807440584200c0c019860301d4280000358848030900a0410300076120815603032110301094506210303002602c40c283c000403074089035140c1c0c01701c01540504400c845030b8040c0c0351a1032950702c640074012843d540703808565100134009100e44011104554481c1001400381a200b040c59040d00d03a184c508903510341001034044100a0011501010799815280383c04048240314041000c0181c0a100030b007001c034595108082c00c50840d2081c3c800345a10920542d1034160f03c1c60007030603582290181c1c18240d401c10001140d414402c40402080340c0350301000003056401b01c0c204100001c0d861442261400d185818411155902c2d0764441c1424240060014a04200e04219543d180b020303042c0084542401603409080407181 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 514747095 1250 514745845 514745867
    0x40f02040e2d0f070903021003091a060306061e090c04240203030c0c280c08061527010806011703070f060e0a06050a05060103113901020f0d0c020706 66
    0x41c2c881a0f2180d0b002951401c1c0c0c2580008d5100302054841e00d034856041d0030042c1c001d441600728600d441001c24014045100c200c64036501365000d180010140c0c9048a620080031108622141000c040e08000c14906801101c2614241000090401c4840074040300c1621000205840402c0c007002c01e14020b40302d2002405251071242c001c50140c1510380140b20440c80e0300e00c61054403071000e040d5641d52038000c0319501c0603907441901c04400216000c02003002881124099044a580b010002c10441d56180d410000c00805192105210160700c01a415a010300310311001404150f242c072510400000604000903002c0e0400e11171880040c4854a81511041e400403001c20701030b820a00c1513140480101e0302801c010b0038001403001400241e840280200c80a99050110b01040200d0701850f10622503030391941c40b1105035041c1e6481e031345c1c1a03440d00103003e014164031340140b90481b107081e6001075000c01c0c62400005001c0001d010075121300b107a01074050000c1d0030303414a0046c000d0000c158031 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 514748201 1106 514747095 514747111
    0xc150402210c09180609250e01060804060f020d0e010501091104051203120406240501120e031b01020316090302030d051c0608030c01060b030c04030f02040f02040e2d 73
    0x1018458151408e0814072a004e920306107040714840b1005005031402903950035800d44020340ba0005050800f104040440c1083e0828041e40c01c65006921565145203401b41f558412808403040c1c4080b518104c8120f000c04041e044002e0441c40341c444101125003516042100308209540b08501900c005420b00200300e0b09420300c00e410740c18038003c990109040e142c805c1c01c14160344d003200d202003502100340c6e41400c3c1104c82c416840118003052000f0369401100f0420400160b0300c040e44002c8851400340039091031074011948440e1040540c8081001c0001c031206520300c1001d00318204510700c142002100e40d15185543c0303a4100c0b6854550039400c0034400200c000030801a80e0184103050022444c1c9480c40d550062440103405d001ca07009901c9001c001e1041c0660310140c4000c0c107101409050515001011182d80805c0389040b02e15420f03181c060010907a12552040c0c2e000d519 = true := by decide +kernel

theorem cover : BRFrame.Cov 514568345 514748201 := by
  have h0 := BRFrame.cov_init 514568345
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514568345 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514568345 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514568345 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514568345 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514568345 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514568345 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514568345 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514568345 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514568345 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514568345 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514568345 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514568345 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514568345 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514568345 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514568345 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514568345 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514568345 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514568345 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514568345 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514568345 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514568345 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514568345 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514568345 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514568345 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514568345 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514568345 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514568345 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514568345 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514568345 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514568345 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514568345 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514568345 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514568345 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514568345 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514568345 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514568345 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514568345 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514568345 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514568345 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514568345 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514568345 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514568345 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514568345 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514568345 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514568345 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514568345 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514568345 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514568345 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514568345 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514568345 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514568345 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514568345 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514568345 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514568345 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514568345 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514568345 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514568345 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514568345 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514568345 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514568345 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514568345 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514568345 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514568345 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514568345 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514568345 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514568345 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514568345 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514568345 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514568345 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514568345 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514568345 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514568345 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514568345 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514568345 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514568345 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514568345 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514568345 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514568345 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514568345 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514568345 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514568345 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514568345 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514568345 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514568345 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514568345 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514568345 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514568345 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514568345 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514568345 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514568345 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514568345 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514568345 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514568345 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514568345 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514568345 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514568345 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514568345 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514568345 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514568345 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514568345 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514568345 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514568345 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514568345 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514568345 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514568345 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514568345 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514568345 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514568345 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514568345 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514568345 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514568345 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514568345 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514568345 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514568345 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514568345 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514568345 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514568345 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514568345 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514568345 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514568345 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514568345 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514568345 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514568345 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514568345 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514568345 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514568345 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514568345 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514568345 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514568345 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514568345 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514568345 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514568345 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514568345 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514568345 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514568345 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514568345 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514568345 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514568345 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514568345 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514568345 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514568345 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514568345 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514568345 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514568345 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 514568345 ≤ n) (h2 : n < 514748201) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
