-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4550
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:59:00.948048+00:00
-- url     : https://prove2.me/submissions/4f59c2ed-286d-4048-83d0-376e73fb6960

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 818165467 ≤ n < 818345323 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 818166717 1250 818165467 818165471
    0xc0301061701080a0f0303090b0a0e07050301020f0301091109100e19060f080723030103060b010f0c0b130c08030706060510020703170d02070f11030c0f0918061801 72
    0xa44400c800c501c0c56007031103080740940c00001007002088031060f405032118030a150203d0382d03c007140c445d044210030030344021902c0c6944410764178054000f045501c0041805800a5041290154103404d0340d010503c03915061030345902d4203815000c4070f2400c0b039200500007007600c514140200b000170614546841554000d001300c4202528194500400320103d40d85661840351640304280c00725141c0034007421040c14000d1581404084a0407250384611101a041c103442d1039600d0744c109602960b406841e0300f030610440d0401c2c3e02c20740b0b50100200000c4ea0f040540c1c42401d45035009200e1000e1520b01d0040c2c000301c010700000c05e000300048018407009000f054140b00c829190800c01402c101004140809a40549010000900004400b011800004004504080d440003520069900c00d00b0f00311040340c1407410200400c010710b6000700c3c0846042d40200882d0100401050050003052002c91041d00701c00f00180844403007900846d182c190349415148941088010b41e21403140c00006401c0b554 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 818167967 1250 818166717 818166737
    0x52206050603160302090d02130903021204030b040f1104050a0516031103011703040e04060b15090907050f16051e0f0d030914011e0c02031602040515090c030106 71
    0x454200306503806950907540c100c0f461102d0550940095000032069904070b500031307280b0405a9120300c144403801000d01800300768071041d442c00900741314010b0006000010b0034801480411014501603a00c641d01112050364100030f41007080702206071300807041d4041e0511040024501c0a40c100e14083c450181d01c801c9200300c51041681070b0340009140c01c101c80b00a200400ca08403015440c414100741a0050744d2510780c4900140c031300c0540c2240c0c1038420715101c240c140c4190900801507045045907902003400c04400c50005000040081c0c022030800038040f507010041075040741110485501c0806541032500c0c180ba00319140d1f1001e00c400d840300181404e0340002544046240d1070f041d00c10001034540342e114584140c001f08012081a0f1300f26420340300304924804241314a030301407a85105150701e41400340c10010181c581c6000d804045402c24403d040d0b899144a03618807520381d0444020034144d4031098109541400050140d501500040a1203a4141d01d60000c50603608559150f042078 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 818169217 1250 818167967 818167969
    0x40c14030105091c11100608070f1d0a0f0c020d030c050c0c1903120e130902092e0e24090a0c021e0d230706021305220605 54
    0x81c0c900b29110b0185400c0481400c4145068a0382444080030760b08081c6418010324851707030b240c101c4031a0080d503066501c0e00f00703120040c41045400d0042426641c80c01d21281404500d44240220b0720400038038422080c040307800c1c0261754001282084148004128454a0841c025a142c108500420101e46000098004280303d1411124000ca44000034400d5417150001d0001226544081d1100040090310100005650b40701515800710680e0342d007900d0100000410607d0000082004045851b10741d0150058492450503644a090000c3c0180003003c11594900309808841c030100c44c101081401003000c8503400340807030107140c05006110540c800c1140041038801c4440ca070341c1d841500c0d4000111103400039006820410007600c1583c640c440c46101d00380b900004503412800b141c12480c4016841c950000d507966207811815103024541440f0000c80071240f0801c10003504007900051505280f15809c0b1444000300405402e02c0741160482c2d00060554203040041c24025003441800036003 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 818170467 1250 818169217 818169221
    0xc12050901200309010e120105070215010501020a0b0c03040203010f05010b0d05011a030112050f0714240a0509010c051b10170a050405341703090621040c140301 71
    0x8514000b200542c44c004041005646052000d0201030740111010210a1280c0080c01428080d14140d0014401032902950f001505881600030a04552100486002040f43e105107141c100b200913848598a40301c07030011901600302d14401d122824241000040c541800e640104070741200440e04010f540d80f01c00c10700b018241c03984013104e0aa1420720050100032440a1104101c03403080e4116070761100355029090811099501c00c0e4012904072501160508080c03400c0b0301c1c0c01300c51040c005417001d0792400d050a94040ea09010702040408601c80d01140d0042c040d61003e07640050460301061a511003c045000540c0c0f1868020960359101c1e180d00740c02208480046400c608801c00e19985a4a80078002c0000400540e81d910824607047c11b200343c01c1c0300c14260700501c4140b00300c504082c0340d1080d034100a103a005414039280209940c08088021084c2d400410080300c69540c2c1d401262500c071181c0c0120640800c4250018051004010004105030211140e04203044800346464041600f = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 818171717 1250 818170467 818170517
    0x305030a1404140625050c10030207030207060f020a0506010b0a03060803030f071404120f030207050d0f020d06060e16030c030513141e06010302150703020d050a0c12050901 76
    0x408402580725150b07490524003400e05d4899080b40c21488003608006000d1406142605603140c0d0021200c219003410b1425600002d0110382c2019440e001441e90001d54030035080c400d003401c0040c040d0395016000c0c070a000780200e40ea0424100e84e50703940c4541000c3e040381e200c01100750201b450400000341640300842900e10411041d04d22000c10340d00c4000903200020102140180341b070040001166010141c0602c59100b0302514801c0345900b010b2902a1034030596800083c410841003a80134005088600a0506183e054070701944c25121868020040e0000307400c48180001100d0801c4a41310941e20105481e0859650070312050035449030a908071002a502c540c501784a41514001284d19a055280555902d6013101c0d40d0b03104490059414501c490700000c0540c000c44010000d514003804400c070300700c06017502140b520255a80182d61880c0800344031082c0400801c041201a010b00800c140541d04151612601c001000d40103007207034000509507021441d02c0f141000d0b58030301413107a03035 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 818172967 1250 818171717 818171729
    0x1e090302161e0902091302160311010506150c210c07290705070e0711151608280f0e0601080c0f06130b031e09030409050c0d060305030a1404 62
    0xe141d0a0500d00f03210b020354062201355405c107036269440340001d1514802000b44964020300e13203e9a500d0f40c0f0b0001c110540e82e28025180d44c1c1030005102d802d90300d811905411911006029a6595614a426003000d940e0380068070a150040c008040320300d212002040309024440549101d1750321994031a40000c3d003d40c003443c0300c00c00c81c1c18640c8060411001000614010022184c4c1c00d0307503c1c0d1076100801d00403100c41d40001c0e0090159940180c08120a916554405158031030038600a0030b2100c0e4000844421000c1002010110750800c2c0844620307041c0858694450440c8203800f689000904410841d10700034524109030740040c01001b0600d0350503124114041d098042002080150441c0c20341d400a41c4075100b08107080b0380d49841290720004101009000da200e281c004000c007140b58020202413196400001000001440442140c081e11074030400017906494212070540103009036101c20381d90901c1e021010061140c00009404101c1e0b2540d2048805011141070000b280640e1142c0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 818174217 1250 818172967 818173019
    0x20a090315142d04020d0b0703020a020c0303040b0a05090a0e04210c0302070501050f0f072603010b04031e080a03090b090a0f06020a0c020a03110f040e060601031e09030216 76
    0x5126500810705425006800241b00905441c1640c031040d050100941d001c0c00130a81c0051040c0d4070b07540500c5010a2184210061800c080c540302e9a03000a12030610310718104200051000441c0e528281e044015006840c100582d51825150520541007150082001e015102021782505845208420100b0f681607002e80702d10b5150070019105c2e604012480d8600302170074004284a031840f280074005450041052000012a000100c08540c4104000c12098002000140304044140701210220f80d0700811164030704c01504069501041a600b0040c0302031400101c5c246141e91581280c04000d0080c40c9482c0036803070703480183e42c1d90310002000901c24420004071070045489503000e00100069410b1a000b07547c140e40c002009400d4541049030600c600000d800701038100074400b100c9075003040d1410040d003c1643e244940d60900200110304054503940804000e04004035040e001c1d404640080c0130300e19031468043c1d12007d2615810000d041e074400001001c074000e07104028201808010 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 818175467 1250 818174217 818174281
    0xe060109090219061e120e030702040c03020f07120212180901050405060d0f02120d1d0d030e0d02010c141f0b06030f04240606020105090f0709020a09031514 69
    0x424aa01e071814030f80803091040e04070045116024500421f0001001070014550b1070400e441048102c40c0a802d80d41c0c10141b040c443c0810f4902c541e000c403031401d03400595030a666034605104a240400c1c9402044a1104c00306282074200300396403101403040c80454051080c5d0fa203d4041c0811580119a2640c0c0300969082302c0300410b5403041005102400509000440d000400c1201c0c5840d01070054200010120300c0203c60b010406155807440b15004c91b400401d00205407802402d4004100003240304041c0b0b40300803421a030240f0343d00b011259000b01c9020386a02d502c1d071429106c0c0340302020350502d41c207291a92209062680326031041002c0c003c001c1400c544886196600783e80000308100c901605000301c411590341c215800c018040d00c0ca0001144060a2420003402e486000d0280d1600c3d42c000840300070400804200803043d241400c40060f241c4404800c11a9004420360024003c08140d005031009004560000c43d1280c4040d01c41031191707141c2d98150050b500c003125610006000700c1c10 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 818176717 1250 818175467 818175497
    0x3020c01111002090d020406170f07030203060f18010c0306051002070f0b070c0909151d100c021207050c010201061e050d17120414032b0e06010909021906 68
    0x4084c0004640140c09040c43e0131099022a040700c14a0700840006000303440100002c4100b000b401400304550b1000e40a02440d41d400300e80c1e110340141001c1c9808030742c0000910800c80c104108040784205500038030031100c12400240c0141054011580101880c04484007905e00001c1d442003202d6880d01d40c07441c420301d0300302c070903055402c04003007111406003000001490071070360301a03030021500902144129aa031a070783c49040f155080c076450702c09680341010461920000c16101d229000101000c10050020a0128108030795a0070340241c104c07000c18498280600016030403c0c4860a0f0000c100d0251905400340302e400d109100c9000984039108140040e0070301c1c00c82c64120602c1005900c850303840002c054a1113402c00e5103d12040c0c62900d0400007480705040c50845200c8403400514504078450b00c00c40e6024650b000c0484020301605c100c02010207050340105c0c5540f07140300c2918041d503100c4044201406020009030320580180209120843c1c4401c208011903034551100d410f2001491 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 818177967 1250 818176717 818176721
    0xb0f0708070c0b030a0e15060609040b120a030309060b0105090607080a03060906080604120f1209172d09011b0204110f0a17090a080f071e03020c011110 67
    0x2608030b441151115000070481109030113907000300f10030341001ca180071200300103501c0e152a08015004908140d02400307a65102d2000321000e000c010b507030115060f10f841000c04c00300d141e0107030b4101c040c1c89290a14400d140d8150302c400c403200d2107454244454100d4400440f4140100208268040300400111000840703500040032010b586081c0850390581e0b540010044401586c02620b2541140b002c10040248250300c0351142205070a0080a507110014010a00340400c50214202030f038440d00b05080c001048000040d01010b20340701d554401d40210040c100840300c0021202c0e440f102280541a0b1074003100b599240e5806039501c040441c181ca515155410384001d0503038000d6540d00962041755207000080103030214a511a80e034171404404024001a03208440f00c4004250000b030021100d00490040c61260b044030702540c68115030461f6030030512815500a064070701c0443c0300f0342480458584401918082d80035541119900801540d94100c2002c8085050b000f00540c85001c509075 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 818179217 1250 818177967 818177977
    0x2107050118021f170109060501020d230c0c100c02030f122a1203012903060d14060709030308180705011d03150a060503071404091110180b0f0708 64
    0x1c1d1906202060000d44c410710181801e810848610740c41c0c603000e0000b560108a02e02c540f403258030740341c6074411981030b6420f0350320141d64002034030020024031200310203010066602c1c0d1540050202044c0d00c3d4040700070f0701c0b0b05042c140c102c1c02409800c00020005201080000301d46030100d0f0706518203014044241e4407881d0960f0481401c0d0400c880c0704012040411920030804080e01045681e541001840180da40c103800c01807200b074001c000c51030206440842600e401050030703502800c10440a282108007581f01a801d10900d01c1a40c0401c903030b0a501a00c1d8808407806916015000e448810801005002076010800750b903100e08820840fa51064407416a03840380b4482450041441c10006800c0500c020941e2004542000611502d4a401d11a010050100300c00815900d490000c40301c0c607034141d0498240c07042e0ba440b4090001c0c084451070000b0304e1040144441c1c440784c0281d001030718148860300400581031142e80041030560003d070495025110001c03483e42800c1d65555222442d0b408 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 818180467 1250 818179217 818179279
    0xf09030b07090602010b0406030203250b07120318020619120c090e160207031709040c030f05240904080d020f220f0e09210705011802 59
    0x10101001010549a1800502409142e0358400c035041c41c1c0603009003550500b8007914801d91030f1010800c0160303400910520100d03038142c0344040b04040d0443c180401e400035404140380703080010f070000400030b46503901d11001d81e1a890401214014101c44ca00b004100800250000e808000b031030030302c0b015001c060405c00700519080b001265680488415201c0000240c404112070030b005010801840c00c6540d400400004440c0121b60780348002503903004070307101c0a040300000c021144140285402241e1410310060400d01800403030310001030003004040a40d000e02850314001c0395070885260b04490000c0700185009024200070810402c0500c00500100e40414007049049501221800508654040a0100360300c804160001081181881c0105440d0011004081c440c05400c01c0c1580d0a5a01c4000c820129135503200c09540b401000d010480084028200c21501000e04000282003451060000744600469086040c0381d180225600952110300c030800281c4050400f01e0201411103 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 818181717 1250 818180467 818180477
    0xd020306040f0c03060503011109010929070c03062a0f020a0203100605130e120d0e0f0115050901120308061c0507230a03062d0b0423070f 61
    0x803200c207001203c69036249600841d480e00c10801940c40c00f840340a0644aa080040c1e103442030303160000301049294014010174020749407845040040c1410b03100c00080c004202550340341c405090810403800c0c1d500c401c03243c487c00e020781c05130a0703000701d0207100401c06c2c0070300081040e240d1603000b501c0400c082a24602144100c003100d202680d020010710481e081020400190942000c05002280142424001d2143d0030242083c0050b10001a80744041c040740020321b844680400171880035040102c8031520601c02c0e00311407551400190311103040108102800004242e90714107002d0086400d1081c901036082600c83c4001180c000d4802079401200180003400d49401c65650480c202c5c0444000e803210b074001ca0060207060321041c5a10058120b2484100d03829070040009000c40c102800000c04454880312a0301c0080b5101e212038500d50710219600c401440b000c8400c0000784529030000b0712860400304003c00c0c80a01c198400c0b2642e0380b503503100107240e4504d903040e80c024102000c07103c1041 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 818182967 1250 818181717 818181731
    0x1605070c14031f020c0607020303040816020111010507081f03110d030e060705060f13262106040c0e0904080c0c06031e090105070203090d0507081912050403080d02030604 75
    0x10075040c1d0f2620b0085807000d03006841e500800c1c090382c64040e0060140042d50300800c1407001148201054030404108030203501c1040f100c510049440f0401d2049010701582086c06024190780c0005a4600c1840306411130800307500880318080d0080c8180c400034000310090110440b103400c0200c815001a4082d0814040d011030181c0801d070564400c44040c0c1391303030300680f0501520b6240e070018181c0010748650110b60000503511041001d0b002c00090100f280e0b421000440c203001e070a07056441d150759030702044c08401e6582c400401510000c4429034812460a038007807856600608560315242c2d8094040c4045a65658510899600548074814036200c0e2250701406640c0b100019403060035141d900380f81500c14284014481000078040e808582d04200401103035580c00010b0302c4000004451921600c00d0b642006401c0900540108060b03008030416000780e0f5680c2500410031900c01c10200011b045500c80480d0140141e0000810381c0310708000d2881e540000360061500210000c100103891 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 818184217 1250 818182967 818182993
    0x30b0a05030d0c0c0e160c051006080d0816080601080a0f05040305042303060c091206040503070c06030c0906030f020d06170709090f0308180a03081605070c1403 71
    0x480b104018001859040d20f440c100280440e960009000200b11407400781001d509601102984018400c10408545100c9003400020844004200034440080000e80e840c0e0707a03c00c1c1c40e4418040341c13030042581500803840c07001070203e032800103084d1940c90414544541c001100c410070013602ca003020946031441f058600e03095200d10b81c011440b9442e0184d40350703d08500f00da8501078140c42c0c448401c02c405030240702610f0206245074845403248401e6641d158100001c0d900b070562010b0303400781d4490351040008110f4004000e1818038001c086210304980e07030700b1046054600030428a00040c5c0310050030400d290103500060003c0c0317a050009800c03d0440c50202080300d4044d44400304000c8801049440c480c8248800e00240c1103641040c000010940c903400c56070380b203001004040020640000b1480c03113050302d507440d075030f00707410700b541c541c0403a40c1402080e41c00191001860342505040d0b2820481c000c1d0101c4080319030007011212640d140c8040c40020000e103220282d0940a0240b0003011 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 818185467 1250 818184217 818184223
    0x60115051812070324061d0601081e090a020f10022508060a200a140d0204030b153d0917011a01020a020112020306180708040201030e0607050406030b0a0503 69
    0x4094002a0315145c04040c03104018281d40960f440503210a1135040800050420426a2540000f007800c026038180c8507100207544003c4250b00350864659000140104818086201c0052a000f10341c03100300b108030039081145000e40c014404026a0013481014041c032524403103058021401c04140300002c1e55025041d00f401d000700d4100415541d900b204100400c0070304a000c05206141c280e0b03a042008000018182403003005070b1010086003c64001301060300d42d0103e6002c0e590010090b400c0e070400910684014040300c000c03d2050540345980c13803800d4018842400308841c01810844031555864945020306c6660700c0131410012807120101e02d403070500c0d04181300c02108000014034518074400c2e0008442c0c1154549045401c407400d4400941e900c0720b0400301f60700c000400103903251a40030000da145e80e0000c070741824980b50401002402904980660320643c001e803021722140e91192035991720f50400302d880c100450821701040c0161442580141c0b03030118003420004400b500c1d000068a = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 818186717 1250 818185467 818185493
    0x90f09020a1517010f060804050c031507091a09060702010e030d09050a080d0819022109062a0c011410030c060c020a0b0c01020d0e0601150518120703 66
    0x1030030035009030303560401984190b0104203401c0100f82080349505021560b02a890b840c400c0c00100005100440c09100042c0622400c07020001c08542d042c1280514100006404490300000304903030000024007090000c2c0074480c16001c1d5400c0a1400d03d080d0f0170841c1c0394100804c00d0341040803412140075503450030800605401015142c0004c0c09181c041002803920b100d030000c138041c0e0000c003100101c09400a01807034100801c080c580c0e041e41182142007000b80110301c00f60b0f80c4000e219111408102003155000c0c000c0d04040261007080e512140c1c81801030042c00701040315864030901c45450544484042e00035904644000704142004058a014688040d04c641c0c6104580190410400143e5121580144104c0c100440d80002c0c68000551010142c800c2c0e81200100140458041c00f00b9811500c51380700140e410007200002030415541d4013000d0003400344400360340041d16407560042095807811403410389080c2810030744030140601141d050352405c080344100c4501000041c010181c880d = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 818187967 1250 818186717 818186729
    0xc01021f0f0e1011180d02010c0510060518040f020103051f09050a0e39100e0307050105120105061e0a05120601090b0a18170114060405010e01090f09020a 68
    0x10a4100c030440d03d28086401c042c491519a030700030012510280002410315085000840d00c641d100c904900059030880c43d036100c014114000e018490301c1c0c2c2040c507440f8034241d070001e0390038404125000c0c1c12070508080c182c4000d803210240084560040d031081e00650b501c0302000c441c4242004c2906090a01050f89800c180601e544400400541400f50f2007480d8040103283e00401c92124400c44481c001d642402c05038195000d64490076034800300d844421100d890000e0011103420545403801802c11401c0e8040602c83d019041c2d001802e980300d0025650040c045003d010345903480c0c1410018603601203955421480261010188031604001c00381c416a42d05494442da290002c200c4511a05c0d0000d080078148001400300f4003100190070f003980c00c96440d80c10901d90f40c40c1c102d00381101c00801584803c0e108180343c90030741c11840e011b401048244a0419070001c15450f003400304000d82760300b4081c0700e10b140200c1004020855032900704041416071804002844c0845402040c160741c883c0e0012 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 818189217 1250 818187967 818187973
    0x50c0f0703111c060c1b11211018060914010b03060c03040b0714040603060f2c1306050f010302011722050f0106030b07020f0c01021f0f0e 61
    0x70000d1108100da9402c12440031110451071400302481909048644280a0850307075443d600429a82d0050071516026005121906206040c031b181036a5001035090750340e8041e01e5140000c0f40d50580d4080d4540d03022102c1d44c09001803d00700c80c081c1d002084a120a41c0e600f4000400c00da002c12518882c1528046c0143c000c0480b80d14052071a600303440840d4803403400f039800300e03080043d428070600a0b80d400a03844520101c2503100e481d42222660080c0000b1403469000140000302141c01d54000e204a4086004d41a50555901c1584204107242018000701c14442c001ca402c07044040b80030f0541c4080b07146201e810380c02141d1207400481c1c1d011515507080b24032800041c4107568102e1664a1103a00d2510072107110b00e08072110003090003030311481c401d0188101c1851820071205110072004104c8a0008010326950b03803e203490041c000b03603641c8000d13010341501405800400b0035842244001a001060201880394622318665140c2038401203a5030b0b10040184044000d000300d803035440e211801 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 818190467 1250 818189217 818189219
    0xa05060d061706010521030301090b03010209150d06091109061c0606050d0501320109031b0f0b0a02070b0d060302030a050a02030606041808070f08040f1511031801050c0f07 76
    0x6200c00c4110a0440e00f40e40c280c0807080a06d90795001085034150344413160082051458400401d0181c00341501c0340c0d5124502054094207520088040d20000035006402c1c4401d9a03a0001c000440d804414501e0803c0310401003c1940d04041c00104001e02c1c8042d00900c011200048440880307526400c15400143d0026407841c211000c0d0080902525600803040c0c10009480520300024004181004c813814485047d00d09981c000c0b62800021900481a034007095402000302244d84081d000b0101c02000d0503401041c944001825594640c1e8550010610305080c400183e0700c070f41080d4143c0c0c002036245d00e0040016101400841c840701d11a0340101a500c16500c101828107a004168030b004074642804080e000742d41d000700c1640a1b400c4564a50f0301c458908208543d8400300f0b401030040f1030f002800280d040d00c1c0602100444168004d8014842902d080c11580902c045c02c0380086030b03005000074540503400610f9001454014103000d4641100070000700c1c01c01c020010781c070b405138103d900 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 818191717 1250 818190467 818190469
    0x803030603010c0815120c0402070f05070801060e1503070f0b070606080303072a0b0c07030f0c0b040b0613051501030605030d020715050f03150f010e0a05060d0617060105 75
    0x4025041c035182c01d01000501d0110005017074031902441d1035102d09259482d80c81c0500b03041c030510a48100240083d5a520310500742904142d003c00402c84891144200000322410188184400e071526010102456101c842c8002902d0f40050307091545801201c030001040c1070800c90400041031200061601e1f0000ca090030000c407a07599101c1c0d00306410030002c0068091380100c40010802e01d0401c40f005645003940c24615069908000500e910044418801d642e001c0c0405800c07507030b202e65105031520880c080c040320000380707131900100b41c81030440100300086c5000e44051f50002c2c0160200d220a020030303100600382c1c1e209481805040014441001003560705020386800340009030f0080407640310400300255100e002d8404ca060404051404044a074854011600c00b40c1030801d40d00d0700c0e42002000715262015041540c0d104001c0080003411550140c504c04680e55001813441c1d104e91315040500c44d030f0754440002100400d540313140c0814850260b244030000003007800001c2c080c0e9030501e4 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 818192967 1250 818191717 818191721
    0xf090209070e060d0f1b050c100b010804350d06050117010e18030a050a17100e0711030301120b0606070c0b0715180b0114240c07080303060301 63
    0x24040e08108800342c02c080351661180c1c0200c0d01c400066140c00124081021380d003400400700120811004c001200304144c20a42c040302034004402c50b80300740c8909040307242c0700000f200c2c40c14500d54003060741c01c0300190203c1d091069080046418884010101c1c2d200f0100e19603001c03110207101031146020904030240541c5220b448050b10bc00c1c202101182c042e9100c1242502c0d0501c1911391901d55803000031044a00c0c0709001d0168101c4400300d80e240c0700700010281c0b43e83c2003441310708001401003000082800a50342503901655103e401b0950f454103100303581c200400002d000c20140240d5080c50080010104007d6008000900d0880c00307481e051700e041c080c401300c0a41064400e59052006c5404648210030710802c44400650440c0e50f40c5803464905484182c0c8118198503618040d06190300411804289007101c2c401c07020f100c010384c0c0301d006e00b42070801d002c10351382c1d0440c044403081c10071070464149080c211207000c400b05e030510b11100d040300d150007000d4120540310341000c030500445003424 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 818194217 1250 818192967 818192971
    0x150c031b07092d11040b0711010c0809010e040b0a0905091912180510030e010b0a0f0b030406060305010e100c0c0b06220606050403050f010b030a030c1103010f090209 73
    0x1040140601d6041010840040800e00140354803400c0000c86240300c403032940c0c0724a20407070420024a0715950b49610a089130b0300a14019681d42d079007c0781c0c480054ac80303082e82c610030b03d07032200a5509101300d00c0c00440743c0c0701e0060301c255086540c0c0c122070b41050b500d40003188010903011034040f94518010210074146004002c0705036907580c49000000000e9540700340540490414079054407250109001005041c3c403c1c0d000541002044060604055068109003105007058009109841078034040c01510405481110744280c540c10b0148010300041008681040c09100b002c94590b07240d4542c2d07405c46000701c01c80c040561080710361400c0044240103928007400c040c1043e1403c2c0700191251000e01c1e80003002ca0344035001111050481c1e5400210410300360011510030459651500000342580d80540000c1d1070350320580710218030600301400f07907841441c4081c01600c9a40c003295001c0d902d60311014070441d0200383c100b90050880d1001d02c500c105580040b00042800141801882512140 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 818195467 1250 818194217 818194229
    0xf071104090c0506030703020927090c0a090c0c02040e0303091002070f0206090409150b0f030708031207050d0903170603010209012102130f0302151305150c031b07 72
    0xc040c8030701c010603003200c05281160380594a25913a50382d140000c8009114071000c13a80c2c00017488840c201040c030341c071000a914003145800401c95484004110783e40e840300b8482e1075400713583c402040c000101e00303030001a603c02c407508182030410050b9000409403032101003040030550001c010000c4c0038804100314050b000400000b1403030070303100391a0b12006503403620020b03004860002c0c00340c0181c2c03103503444a840b1035004011050000c50b10306801c4003801c0c124804c03034858030100103a0007403840c020039014215014074004500d08200a440320483d0315004106a003403110a0000e4401c0c10024000c1c0c0f18003511070342e5411907034050300f074104884460160145020340e2040c802210166003000031610817441d0600030f104015161080d4030084d208400740010103015076400000c1e451b01002509040e28401c4403107000603130300000c40c140d481c090a802c0b11291010140100802c0c1052000101030107144682d0714509124405507511f10b034050707441c281800d42102130b0011f00c20b1082c002c0c0c00c06821 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 818196717 1250 818195467 818195471
    0x2120612160e15010c050a02060313150b0f040b03060103110609060d060906060e0303030f1005062113020312070218090c1e0d1e052506020610030303051008030f071104 74
    0x4246c2c55140d56450b00e5000280950740000100b0045a40640c071051b003254840301c0d0111044108520101510145c03400d58000c04d4840c580d103e5915117800b441d0b10b081c1c0c020b8001c001c56031840c2c9407240991499012580c000c141013011010540341c020041103000d030414008a905842c01c80070b44100e41a541c04203041000c0546100c0440c1d40210490740c014001542000140c1c5446003854045502c4c3d034480d69001500040395240e405201e5400506150004141d5000f507503540c4500681c40c208580003907140d0044102450900845805084940d0018100c2800e441114540842c030301c809030740d0281c050b4442c1800c45001d140000c1e0300228207403855074500d900640315002c80c03480300781038074020030b5610107580c05080783c0716072841c4051241c1c0110480d000c0e54020440c61182d00703941d0354034008100f03c0310030100b2154000103040b401401e03090082e403c2c46246403001c40090201804011203500c1ea10b1000801c1c0004101030481d180046030010366038426480c050b40300031652410b060141d4 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 818197967 1250 818196717 818196737
    0x103110a0b03280204060201151a04030311190b06032401091e02070c0f0b030402030604030c0f120f020d02070b0426010f0207020a0902120612160e1501 67
    0x614900140c0f03070090314000034400314502c0c1c1851441a240e1068441c1240740c40070800080140e4150000c0c80022010044640b1003600c41007405000d00242c64840465031007000b080001074410800c0000e00010001980c040c40c0607049004262501448143c0b40d01c40d114050000c1840c0030311070540102000ca0803820300d03422aa41c4041f01e05014416203007440c1d504c03500c5107681c00550407411074540740e4004c119924a42407510030811189801504100c80300700c04040f440341e122508407405207800070010142680c0e5580d0883d80b01200c0d40045400f00a00b004031000240350321480c150380e22598441e83d140c028032601c02480d00c0650700e840000c44d0f100d600c081100c0741488080307030203036000441917050307c07940c42e03c0d2003403280c4580d00c080c840c81d0700c2c00006a8036401c00768040c06907244211903442c02d450f5201490b2041c2d010700103090000300325260100f0340c1c92520a03a00e008910122045c0c4580101544070681c44010700c4d0701110f600c10101c020013510980070380080d078902d0001d0910702181 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 818199217 1250 818197967 818197979
    0xb150f04140604051e011706010b310503010e0c01020105090d081308130f1a0306010f03091115031602060c0a0507050309121b090721230103110a 64
    0x303910082d02c0b1a000d16aa48080344545001044541c0701e98860f88600d1032550359103490b24150a060702a500490050200100e000044034003106d0803107429540018038000d0145050078540c0b102034086030b1071a614080020103072000c1c06541c1c80b044000c40a040008200030000e4295580100300079115005403445201998011304100d400100d84d480158203c8040d10309a803240c8144000e852210304100b20020300b2140b9801c800c015102d000500308480c42211015540b40e004c11b0b1216804240001510f01f0014445e510940840d40922002162546188007254103030707509402000c86200c0000800118500c1054002c121007010f10080005161000d001e010b0790050b64202c03001c0040014a03202400010800c2d500030b91001080018030001e8008141d60300c000f0200e00d02132041c0d00c03c14072080c5180404d0001d205203055181c0c0d0804041138680784184101c0811512141c6503134080a031240a100721b06ca1400d8000e524046a0355415402e1200c0e10114a03884070f0f224000441c024825 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 818200467 1250 818199217 818199251
    0xa060f1401140306030d03022520010206012d050604090c030605030a030207050d030e0a150f1404060c02012601170303090c0d0201020a2a0b040b040e04050a0b150f04 73
    0xc25401e507e00161103181803d040d10805084802a403000c152049504050140206460740c4403c04507445460341e001e503900580e155a401d12650285865842d10f140b401074000041048442c8002402c40c0038a4841000507810341082e000480c040f90355001c14003120ba00341c03040901401d4124000c1803d54800e6400960f1400d55007c1d242c0030b000580f008030101070291428001d5410018541007000f9110603580300a015155207241c002101d00d00302440660098050001a00118030341ca40340a00300070041ea00400804c00c205d0405c440d000b4448100343c0d21840095000d404402c4c6044203500d0076030210b10461075040f034445a60020810b01000c800000703901507001c041512161004656400140d00b013050b0003001412405030b8403000c01d8004c40c0c43ea40c2c21911708040780001002c503241c1c0613400e2140264040c5800c80f0300204414080303550b0070501d0551182c80303801140c078110303025a01c888000905480c10319040b520415110258038002e044580d40340700a640c100001c00740d280030b80075 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 818201717 1250 818200467 818200483
    0x30207050709150b040602060a050a0c0c0b071709161d010519030506190c030606052703120c0d0309080723010c020609150606040b030a060f140114030603 68
    0x28590302c020f61111103103040a040002d0500c841c00e44e441e90340c0c400c0c0203511003900701c2e101006203252000180907444180301d11403442d000c0c1d0b503030041842107564480c2c901e03460142c0140d00b48845403182c80700c1c810624000038860f1140c03c02038116030410f0300d10b00c501c2542540040c01288507005547c210f0000040005045400844184800300c08082444805003c5a00f024020340242020420302e1114681c83c0d4559510441d010440c21046010803011202c49004050001d801004032035041c1c0d501d2600c030a94448020606407917142182e00003441c01c0164162003800c010041440c103001482404003810055040c00c040c00781101e5076a4954191207550402490b15180845000c003480c01c542c075011404e40440001c01c40d0011404010f5031700c0301d0840c1c0c518154402d0a004242180040306841d009441c050f00355411f00d4100303944502290002031001c1102d95aa90b40012003070172124912008180344d20641c041d20800c0300c0014410122078400d846441c804000b0f0020b41d07140000e00c1c01c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 818202967 1250 818201717 818201729
    0x110f01080705031506160f0b1f030201200105190e16030201052206050d0510050d03081f150329010c05030904020409020a020d0f02030720040c050d0b010302070507 72
    0x594024130a002032140e0041c0610001100e200300c05200410000c041c42100080c002c0092030b007140d44080302d5103410800a072030741404184001e010001540903402101504100760140c0c4030341d2100b01400e9007100d000b1142040d40c161944940300405d15039101d40207031a80f540000d080450316040380315480c06a21b01c002410880d0009049420205550000c003050461450401c41c465642360020001c1d00b02c0c001c90320f143c030320b8217010411602001c000c10080b5240a4072031192450f82c0e850540b51810001e0843e009a00404000c0807510b140001070360260071118032101c042460304000804460360360b0001101400c0740d2201c42c1c0140d25104210104490034a400b109880311032030040d046004c3c0d01c84a0790014008140030503111502d4010700445500c40d0f00b122510010417500b120741c10f00c424103450141e0801c0107064003003044000580303070700c0c088051199041d0002002150480b00100131182c0090b84c0071034202e05550260190450541c0c003441d095041c08400e0300c0301911040544602 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 818204217 1250 818202967 818202991
    0x21804030f120203090615060714032a070506071b0b0a08010510121a061c15030c140111031207020120040905090f100c0801050108011d0702011107110f0108070503 72
    0x8a1948d03074401d400c9404040d0300511071510300302049102d0344d903900521f0500f01d00900c04034044a5240d00c1c80c140300c626500c8503004102040c5000d040c41032030351001405950f20390440000000d1300b07501e58284401030090000c001e17a21194000010090300068200510032002d00b48244103050784503003500442101d00000140780c5600080200266000c42c41082e00031a0210b8021840c1103c0e00180c02c0c6081c40301401c1c4002040c0b00c10a10766007220780070003051f840c3c0d000c1051050b10303080c100d0940320700010305003113039444c4500404500c0c5400c2101c01410000d4001e0403c44d00e070782d0a010b0481840c404d450741100c203c80f54003041605000300d004da188415079603400907030098800c000d004510703840401500c04200c5442d400b003024240c90305d070f0b58011998a01c00011030394800c4c0c0c800360480d2100344180311a000c00101100e04408003034007280440d0740750b407021451803101034018581b692080c2c00c05c0000803900341c14482140e0040d50044d05004114041000985d081000caa900c11503c1d1b0003 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 818205467 1250 818204217 818204251
    0x4030e0a08152a0c010c08060108130507031505240d02240a02151f060c02010903061109040605060307020a24020703050a02010e0c011b021804030f1202030906 70
    0x7030f590910101503465001c40340d62810000080038404000c000061901000307000c1105c5444051f111050240c5880e03000440c2a00003d210100c41e840b0401a140300780e095030766299580d01c8010400105c408091a0310b991103081c411200b0441751984030081c03000e2071720405100703840b00040d1007a00b120006806241c9a401e42d103107450821810003481411000c1154503110740200081d61008568845420b401d07030328010a00c110801c41c5400c0043d800c60850b00112410568100c44491036418224103000c040000400080caa5006a1903480c0c0424035260721201100e08101c143c07450f903400103010310810018405110313400f0038040416500018406950030703c01282d0b10461000480f5041c1d13092012403d1410140c2c040001e026000042d0f00a002901844024544031350341c0c20003050100b0804440c119000c80448110780d0380c07600040c01200d120441051085810100320ba08900044031b1841d082081d5421030680d0b9966803003242c1c118218a841020b2540d00d503406019000c0c0f02926582c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 818206717 1250 818205467 818205481
    0x12102060c0f0102070b15030d12020c0a030f0e040b060d110403050d031a220b01030b04020d020d061e0506090d140105150607030905060c010902031504030e0a0815 72
    0x8880d4200d25607001c075500840c02c0007201c1c1c000d401c040c074200d841005d02404100d02c006828151072013158000c020301100740340303a1020342b005500b006040700c00700c0d000c0c4503100c40070005004500315140650ad070f032448512602e800030302140e54290750b10f104610f0040a0381c11a26000192080300c8160b007000242c14000400040550146910040a920800c0f40c0590441da26402c00031442c80310382d12038035501004800b0032010f000880c03801c015107040b00c1100c0741100ba1f19006424090010304002502c8040c400100b01641d01c081008200546c00042c030110710a801d206030001444000c015100d0b548000c070030702242040c10704c10140301d52001b2444280325510444010452a8440749942c1404c1c0c6c541d40e61800382900b02c50380904900d2802c82c0031001c0c200030040300c0f281a03240c0d44116021713007040200952034002da29920b0303141d03584924002c01a00c1c00c2206421074000d08400384220314081c60024206500a000580255150581045a0300340041c0e00f90901440300b2401c0c089640da20 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 818207967 1250 818206717 818206729
    0xe1b0715110703120f0911210d020708070f03020102031b07091b0807030b030d08150d150f0606050f18060409021b01020406091703040806180f06012102 67
    0xa1a030030060000018210b04140d00600d0b100f11400101100b4810324401c00301607421682d282c007000e01440c2c02204140e001d807074002c40400d0b002c6903504c180d4840c6045284600c3ca0009100341003800340c0e0103184180b1002008101250052042081944000303055070300003904c0e03015400302050324020030200000c80d03110900c995006407044000c10019841401e0142c2034400903140300d1303030205a111011400052213030283c181c659001800030210420324050850340104018891400c600c1460302c1401c2c55581d00075070070001ea0084203605000c44407010341508603880040d0002440349401c00412080b500a015190b0903441d5160b0340da218111007540c0c1209101003010030350310480004d40441c0c02034249d40513150f640d01035484011520f880d20a564200c0c401c6010710404107840c410200441d240205030300c031244d10f00301c0540741419504c000291070310100399081d152032016141d94200c646410015607415680940080025514004071130389862000007482e0045c0c5103a80500c0c0540d20381c8 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 818209217 1250 818207967 818207981
    0x90812191b30050316020a0f03020a120f020d031e1e06060c15110c0706090e0f071202030603031e070b010e160806180403090e1b0715 59
    0xe03006040a051189090408036016108401141c90100704030b280c079800c994480c0e4804a03841d00c0391442d54840c1c0c20201030240c0010503000840c0f20b50301d0003200140906000071009842034004084048040c640914101d80c0291480b08000b110303c41c8a0040343d00043c484c481b9000e600300015000c0c1d0000c00705c088442e400e40c0c0d40c1c070000c0c01c058490300c0c0001102c1c3c405020a002c3c82040140e82d40743e113022110f2030020600a005044081982200c49800d584056444c100c4408064a0000f10411660074140380364043e03000316010140c00c0040200d20980c0c00d510560310412512140381118019041c20480354810750003540c0400000c01030f450410403182020440808200304c0c0030420000d800b503070300c0200308072842c1c0d01c420000618005426038160041c009900100070103000030b2802c407800c0c10002c1c841e50f4400c00b05015034020303604090700d06000300e00a0391140c102c40c1c10101804044280075100c42c140c0b0318503900f85120b0301c0d412000da60f00d640c1d00c400c00b00c51010400711008042c1c028 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 818210467 1250 818209217 818209247
    0x4060515061b06010602070f030206090d140a02030c120d0f021603150609110304030e040902091e0601050a020703081c020a02060403020f0705090403082a0a09081219 73
    0x8160a08968145507800b00741809000c0752a07503a00c84208a88800c5c3c2d80c80382da5982400d44400707000620306100504045080600081c0c0c1d0940203448207035220b03151000c0e844107600720310708da10250305040c001100400030503681c40ba5007843d41059241c0e990204c60300a81040305c00802080d14910074044410309040400072210501d8513820443c3d082000d0404090005240190029604074580141410311107004142030640d44d4903142650650455140c83c1c3d4407940d81d0100030010b9513104600ea0013031450212400300280f0610141d02c910030064150390621205011440c6241c1d8001220b1081e030764010002511900888491140c2d40c005140e9082d100d07001080e40380308140d0000740544968041c0c1d00f2150010b260640140e00c9141070b0045540044403000044c010034002c003000b40e00035600d056107400c4107a0036240b000315804000440c0100d94000211480e4150f80b00411300090411f800240c45010710b0000d03501d05511942018110480040c41245003c5020309008019502 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 818211717 1250 818210467 818210479
    0x7050f0304081303060c030b0148080d020c10060b09040b011709010c02101e110c010c0503150312030a05131b051e01020a0204110708121b0f0304060515 67
    0x94910117005841540c03603042c006242c0d072b10407451a000c0340c2800c42040c01800c69800342005103083d0524000e44440301c034020320a12024005c000349000d40100b51140003002d0040e1110070310401c2c00d00f4885030701a001815800c1020070710100d641c2c0030803220124000ca50008001c1d21150050702c4204500c684038042d501407004003e040341d019001001d43d0000d99090707a030102d802c0e03500e10741241c5040d002c90031800440304000a94944950102c05020700c03c800c481d080c142d15109007030035a07180030025400100040280300303d00761310340c1c2401c548038403c90140881d09040c02004109000061064103e82d4852000c01c0b00c5642141d81e0040071a004840c1d1182c0ca90340030380c0014007041501c01d0038020010b804120043c80700d501000c00d29040c050f409007070007901540070400544103800c0200f5002200b04407000000d40c2e80b5004000070101d42d01c01c40e00e24a4505801c407005030080b002410354803c10417001703484890750000c4070761040d800385000a00b620390140091a0408060286030026 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 818212967 1250 818211717 818211731
    0x1b0907030f0906060302011403040b070c0804170f0d0207030b1b0c10061a21040503040f0f0302030106050f090705160b04050c090105030d02070303032412050607050f030408130306 79
    0x7150001c2085e41d000b82ca5003140a03440c196403020b503100860740074195001060228001c544124a68180d80f4010084a0f003001d03181c1100044801500400002550010548171039401e014480c8951803803150014003011461501c405415040040c1640204658400303280303221040b2800340e6480c1014030b801c9608441350440c40c0401002903008080c50f10364010450140f021000b0221042ca0982c00b889203103101415070310300800e0b17030041e008440d607010512001c52000d0000d1450001801d86945144019281d401803500b140c0850f0000390144175001c900700031f1520382d0150031360070072001d00d005a03a03074078080a0300100720150b0900425010301d1405010a1100019400110344411070b03260115903070300c1c030030941e80f8000c8070307280005608904401c1000c68000e6008008221001010480f0100200601507200f90030b80c000c0e83c80c9440300140001400001c1007400d034130204a040541c0f41801d1086485102e010042000384844800140320f80d0340c00c0140d114000855000314244446 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 818214217 1250 818212967 818212973
    0x206091e0f030a1d042a020c1c02010806031b0d050c1509190501122301150809060c030c0d0e1614030a120c03020f0304180e1b0907030f09 61
    0x61110b13031056079610520b0625120107403a02c0d22840560700700c0300c8101100c12401103da610019441c660744010360103042c041540d0798464140c114040100042d0702d907103854061002402d2a0303000b07410b0034001c1d40100702185009029a00b0950400d40858038030540326010301e04070b85814842c038407d6030821000740b0959200e14140c006481031440c00c64020700c00390000200005080082d205142c0090621080c0004075051a03221180540d05105500c0d80d00c0c51507040c4024141080e07010034008100700ba11040104e5100e01160303080302c141c402502950911019015440c00040d006140c0342e0000164800302200503070080680161040641e03c1c0e8841002d10189010345500c01d280380c020841c040c0c0c440902e030204205421a901c003000b0740c0c80206401c2e08807015aa00380f41203041d882400b06219031424200041c0c00100240d4030b00f0302d0840c2225010300140e64140062590740da01c085610010400c010440c0b80a106064401004954071848105e024040041d0345540d4070340f420b00c0103070038 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 818215467 1250 818214217 818214227
    0x20f0c0d2a0e06040b0901050405070c050105040b06010f020304271407022d0a08090f03060a0213060f050d200c03120f0403080c160b0f04030e010206091e0f030a 71
    0x111440301012030390b141d41d5501030005482080d070109500c040b15400510461030541d0005400a00a04c0d0034051040c080d070364582192401d440c1560700201ca0400c20415603440300c0c1d080c040c410107101071810b00780740900310005001c0c3e0100c0306010320408500040b0f40c9071203034031207001540d10442c08240b9042407140030317441da05081c055000c2140e8400c082a1802c4c8941a42c00d400b241c0140200240d210949514589812043c0f080382c2c4121010071003049903404019060041080000040c0d0380c0c0c44070420601d00d981c00e6400360081c841c0c2207da4207080364120f005e44a0004e41c1802c0414100715104441030190440e0b11203440030040884c88050040000010304140007036203072a00340580300c00c0d14103420304000712401800a031040f0005002780c6880d40161190316103201c0300c441042003079a291100c03040c0844010403217052200402003896400512805104000c1c00a8222802d10407146502d44007200b99501c8001401c0c02141c0e550641040340e480d8890001c416241c56185900300101 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 818216717 1250 818215467 818215469
    0x3031b0c020315011805090f0d0210060e10050108040c210203061b04061805030a0b270330010605070b0c0910080c2116020f0c0d2a 58
    0x4007030302c14915168100c90460020380e0688035940701c030f6030011001200d60409406c0041800e0301074094001441e000710400c119840c180d0000d60050b0081c100741c00300a40c1240c800c4d03441100720700100c105004c03118000f0314988040d40c0003072820b42c0c02680c890401115102966100100980a616200c43c88200c940100554a4800c41c16200740f903c8a4a4a908405104680705e0440004000400c1a180074030030302c0b450040b980440c0e45d84140d0322070019041621408058800b01c400c00d013000380c00030922468050900c010881d0424865509680d40d030b8a0017204000206520104000d0088a401d070074802a204c00848949180b5030311500b005069801c880c0d400c68000c3c542c02d01280c80140120180e070800d00000d000450130401c0d4110840b000c08001d00300c1d108414040101d40c60b02481044401c036007400b81041121241001581e60031000e40310100c03c81150054003042c90b0055000c03030444400d0303104488982207070180303041501c004000c4400500c0c00d00d40118481c0140440340ca03200c4 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 818217967 1250 818216717 818216719
    0xc0305161109040b180f0d0c15020406030609060501030c0f031805012a080f0402220c0906020c1c080a090e0a0903090b1c1505060f030a0b12070b0703031b0c02 70
    0x205c5004c1c0c4803044a45d80d10420006c000480e00a00143c0615510900c0c00181184c0615506540032240c0400700041303038800d80000c0002030321060f0074018200c0a01890005010a01c2e0800044d080d40c00c000742400000804881055150158090500c0c45200001d80d8949c01100821618489100070380c8080050480c000300e20310116101c1000038054030303100744610340c500b0050010b580e03503908000340304000505942e0075907552200c180512119200c2c000000210313882d0504400d08090020340340054105000b885000928000303801000016621110540c0c8004040d45881c020701c420383c0c0b80d000b6500300501d09841d0004100341d1400503002448407a0003070715481105a15150042018400c0c0c1011484525140f003841d0015110b59101c41132010b00e040188a2140d100d200007403581c1c3c0072207615140464040107000d441d401521031280385041c00c454010144c580d02d0441c1f81c0b2a80c051068440301c22000c02e00d003041c1030098020b8068620b100207056200e1180c288040d025601c910420f03 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 818219217 1250 818217967 818217991
    0x50303071404590c0d0501120215090a14120619050a090201050702131d01020a030b030a11090c130f080d0e1f0215250c0305161109040b 60
    0x80a04401c0c2039000710b50014045400d4441440021801a1070f04003410035421690300700f00903032400d191480b43d2806402041d0802e045c0d0041d07401003002c1c982050300242c40c86941006103280647e10849900c3c1100c0414210a44003a03000d8009082485403a03082400d07801000c04000c89103c600504511000800304200403540f00c00349040112503000c00c00901240080000c10058a031400145a06108210000c80c6910191000303000708174071015021441ea40210301e43c0d8907543c043c090444840821703001040c0d4108281c492a5600c0c0d41d65170103d0141103028040741c15403100f00c0032258551242640510115035590b0341c6280700131305202d001c41c6c3d4050102140d03409880750346191000d9400401e0407012000c60b2841c4050104445811400e42c42070002c07504a110100d050180715003100f0700090091510300d400c010501314241031a4082203e01800c003000241c10106030f070303003904207a03a0f090328242851901d1014407120700c038415440107000302008100f0102c074107ca8801c81c10f40c512 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 818220467 1250 818219217 818219309
    0xf132a0201060f061d0a14280603020a050d0203090309011e1e0306081506030c010f020703061a0d14010c05270301090c0e15010903050303071404 64
    0x800c038200d444900414050070810902008514410b1400480750301c60014416650604800091442400c9600c201000c004955003401740d4900369040e54107040c03c40050001404000c00ca00020a849002e0712040c145e010030005007080c03145007170394034000915000315920700f084801d803696a08a200600d000990508180a5003140c0b55002c54440c42280c80308001c45104050b44190310010301011810540e4400000076024800c204a14418134540703003411a034201182494180410b00c1c2c60705040c4035441420402080e40015036a084079000030780091800c07068440841c0f942600c404566100b203481c100b02c000c4c80095685202c10000c0c14000b0410125020341c241c4150180d00c160290007500c8020340030210340c40c0d64000b904c0c010010000559840b4507920060400269000000b82420000401045045150201c3d0008400742000c6a03000d10b545d5400d660781c070005107103404110130804018200c0c0681c0080e0b070b016050300d1013030102101c08044051501c580038030342c3c240c0103019408 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 818221717 1250 818220467 818220551
    0x4030b07020609100b13111c05010e0a0207080d02092e020115181509021914090f0409030215070f03150e1314030301060804030807030506030c0f13 65
    0x800c61005e0394018007802c46000c0c4140c1000000c00306040d100c6941c1008000c046401002c6500341120f84a04040005240d41407a0140600713400003002d031a9901e20400c00304021820800076144c2031340c1034201c05a9038010100c04510016a07181130381a03c000a90001303540a800c007540c00600c002264000c00140750b0184041d2404442445802080840403203942c5490b2445c2e000100d2881400300405c0c040360f40c8890400899101289100c83d02902404499001d5440f0100b41410580b1401c094180080003001074101c1807010a01840b990390b0b4180181010300a00c9420312081c00c1d54100d800a00c1c0204000d002d050070b96280800280c03620080b41d83d1046820130309800d4808810385200030390b503183d080001c0c00d030312040c0a542003400c401902e0b5030030500700000c5010742800d079164810390800b850042d02110f80907103d0300615083c8020002140c5001170704070704034281240c00748120032058001c5404070800740741800a8a003014600d485540048006882260008580304003000e4260 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 818222967 1250 818221717 818221721
    0x1030b1f0e01051201020c0d0309020307090b061b0a0506040b0a06060c120522031209171f0f0e0607020f0f15070521040c1d0c030a0204030b0702060910 67
    0x40a40701002088000621603402d041030207080360303542040010729000c0d20760081440c0c103a6448030303940000c4d200d00d90356046042c10311800300240b0031400203002c10b80998002480314015902070300c0c000302290121035003120040051040c03468000b020b0b2100c1d030030a4100020703540070403a4190185401d000340080d400d0302c070310300e04100160850201d464905022008698a5100011950a809010400342c041e55441c0c0c3e8004002c510031014410111100a406018030742c1c0d6070f002662444e8506482c64400c0d0000c5045121703030a901c0f1016034065120b8038010b00074110000d511460b145801806110380c2000030f0141d009030a1074080345d185290403008503603250142c00d42c04101c3d80200302401d18040e62006d1807904818681480c1e41044401c138092041e04440b003501280448290b4284414424400708a4000d850802c911040c0c0544446141201c82009041d220728032038000700288034040d8036815030f400f079540903160b41c20318240000000e641340c0080e210780c0254001c0c0181214100d01034 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 818224217 1250 818222967 818222969
    0x51f0c0f030c0f030804050f0d1407020a0f06030e06220f0302121209060f040507140f040c030b12160509040f060e030403120201021314121e0f031e1e0301030b1f 71
    0x282d07481d43c00c83d6465884e0ad003101c0d0050350040303800516080011a2074098000d51034080c1005230340c0003c600c0103103104185820000381500d01c015240d10103c00c0c8000600f00e50302000368020003403d80130802e0303107002c918110400d03851001c140804112054000f10041c0028000c00c5c03070a0444549464401030b004a0280903140101240d00c402c1d000c106100e0701813902a10303041e00a1068a9143c94040428160713500344402d03500195a55509003030030325224003880c03c00e00800c801042e045400c0c0b400304001d807907640141c5200b80d00b018006002c01c072001540c06405503102c4800d1141c400c080082d15541d410600045562100050f54100c5051051003070310581d002050090b14594a0007034a159000c000601b0b603500055007010320521050100410400c003800c0007180c0512022105005040c4070100c140002035810130400d4118244040da240c010503107040d00078a41d1003503010a0b90b9031510040154051201c000301c000428048050308585c03090058121810000150020040580d262 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 818225467 1250 818224217 818224243
    0x905031b030c0a0b0909041103121213030203030a0f020405030f030715111602040b03062503060806270a030503060a050f090a050619080304051f0c0f030c0f030804050f 74
    0x30900601174940b6080030056009809a11300c086000c1c50817000c24184400b00c0c41c040c900c014001000d000548080ca0010fa0000d99074103291003990b110781c4c000b0744a01c400381144030300c10b0f00d0704905c0c0326400041e03044400801c030041c01c0743c01c40b20040c29200d07200c0e000700009450401e10066414603016407070003181a0000a2058640b4020040385100140c1c0703d040f0081c1d81065680300880c0b06c2d5241040194002e002c264540200d130f90003164814686803a0b11084001c05051107002c0148000024482e500311401c6c5280c85000030344a5810308104e455064292001d10440c82560700b4103401500440c010b4000369008600d142c4c880781440070780c000c4c071895180c0001c0d2500020305900110391105400010041200c140b00080760400503411060340c20206075908005410441461318018000030342e2544182d842a5401d05a4003a02150105001409008816003907a0405215145821100751b21803a140001d1660b03003001802c0900c1160100d4507441031911036900010001007800d44484 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 818226717 1250 818225467 818225489
    0x2253807120c060914070302040c0f02030904050c0705030a0503071b05101517030955060509030d0327020f03061807050a0506190905031b030c0a 64
    0xa642082114110030740ca03825140f040d5542c8030700000a41c48420450140f58940040c40c290703003940100801c454204020a09020b03502c01c2201400350048240c5200768811140000d080d644c0b080340c1c440621601c00000c0187c00f0001e21800c03c0c5420030040c40c007030252607440c0d4600c84940e070b4015850701000d0001034010f500c04c0680a500c405543c1002100b0b05030365100c0500156034801c1800496100304486645802c04030715030686040106581c00380f0500440c500101d4072f43d0140003450050a101c40054039440414250051900c07200038204110442000007030b00741d5500f50044c030540101d00074a03c01d0152089910b1514486d001c0c1e00d4070308241c820f103d4120850803030f000c52103401c440310880e0084611714180d4420780d030910069200300800c4001488540038404507509050f083c2d00079501c00d2100401c00e000d945c841c1030603550040003101c0b0803400e440003403030183da04040c2175218540c103110700120380c00d10706c0349200358108010090342140c100c86411410881c080c011400740b000c2c064 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 818227967 1250 818226717 818226743
    0xb010f050d080c1213050310050f0106140906040906051f02030d0902030709021621080601030207081306320901050a050d02070c0314060702253807 65
    0x14007494001e0483c954000211081c8103c5810780444ca5009000c141203500108042001141001e1240d222050071101c0100074031b141c05560019520418010107040000c080c041c10307c1140801c00710340c10210b00030604c0740c4555469881e50f0240425005041c060004100134a560400501e4119280c2c40d198002e1410820545c0c070303040080840c07100c107a90502c18900c0002c0c0700c140030310040080890b490020711844405e403c10352108041c51036081036203245400f2410304035512444440d0411400d281c0541e40e00100d0402482601542c054402000c0c20324a00044043d04252011031040b00b141403d1b2520102a10580d101d0480c5501c090300142e0800440c0320390f620450003011080342a04000f400c3c078001e0007440040ba0002042280d1051301d508092007840348504802001050110091280789000c140080d21171495400384100741210903513454800360b03150040805400351941e41c4811140ca48074132a5a00b0700c3c3c19503040030400b4401c1c00203184055404442165400928200441c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 818229217 1250 818227967 818227973
    0x9022710020a3305010f050618010305130203010510031e0308060603040320070f090c020c3001022a0703032d120c021f0b06250b010f050d 61
    0x40d908140c001c01024603401030004030341c0c012403c440441d125541c0000f601c0d40c100160302c02c4011860300310310301c560014070a504841080b642d44520b01c40d420f1802050304d03124010200403444281c07200075819420941001007408800c5e0b2680101c030b001e100c4444180da08260324400750b100518021b40002e17120000600c030390624200454000303102c0c0c03601801001d03500200003d21076002c0c1606409030001c44041050b03009450b502005090a944100004001c131743c07020b96200e8098980c00c2c010f40412100c6002814610103510100070903e0800b105154840d901a000b0b601194002e41c1003400c411190694546100c0000080d031840f6000b45249030543c3c44c03d4034400014a10511548250f603480402d1f040c107402c4a0000040546510103c20003d1a180054940b584071160440d030003a201051540510070410000741e41803000050701510540110300c0503c0f0303040c4003103a0f0402441ca1148005010b02005a1441c040c0b40b200e0216601d8844003540190780d8450aa4860030075200c001c04 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 818230467 1250 818229217 818229233
    0x3040e071b0204090305071b0b07030516050a030c0314040e0105010813020603090705130614011209060c050307120509060610110d110d030c0c021201140f191107110a09022710020a 79
    0x10f080c020b042045001c042070394ec0620380110000110002000c40440004042d00680d000c1d6038401f40900e142d003418240020500c059605108040c10420140042a95005240e5000c841030390007410442d540d207054025140c0e0ba404600c0341d103006100e58400c2c20800e460310b02c100b40c04c0da00c681010301c444041c007000440301c5282e510490107034a03a4601c10f04000450030f2043c0c1c104d038903542d00d5880e240d150501d80a0038503810b1844100c0c1d01c6081500f001950030300415443d9005104035282e1004c0a207440381203030b00500202d00c0c0d140603c6400000741101c0e8101e200d1044130410f1404452f00c9400403e8228141c8440520703540115000558000041c0f80100000840001380381c000a0721041d24804142c0c541d4069480461524411080c401c03c100c081940f2140c420140348288070404103004a604188545400039104078080811700c40c5654a0341840b0004051910080d516440101e46022480042c0d8401c0c00e40103103a04001062800c040105451844054018001c010115103810b99 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 818231717 1250 818230467 818230477
    0x708070605070c0302060f0d1e0507050a170a02041e050a0617070c0204020c0d080f0601020106060c0602030702072309102102030f010c030e0f03040e071b0204090305071b0b070305 79
    0x50b141e035062050f4203d008080c4500c5102c07002c03480c8010340c0c2110741c03012710046903405490281000001c210020400750020501000e481c15208000600d940e8500194024003c0e0740040160504007130440f040b803145a0000000d0704d004480000403d50b8514059540c0e00000d0607011f542c20b484000110030600501201450350300240c005850501d0b02856507040400b62247c40c8041000b0000303001da0b920701c0501503684040d0a0000f00525400c0503405008107105820040540350000000303440c0ca4401d120b1070005144600300e10242d001c0d2202000c800700c90601c8031b24094104800001d00746e4022880310000c40e1405401e0a10404026130341c01c090b6014040103036054403c0121800b00c4480074406c865001e207455400090180f4075100f001e05080101c03d0600455000340810b0024030f41c40400c5640003111400d190410120016451039020000307040070f9485403812072102d06154000c8014801340c3c2c404c0d030380c0306420a410704020710092143d0141c100c1c10001401040001380c0650000d003 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 818232967 1250 818231717 818231737
    0x3050f0c090d0206030408130902180402030402060415020307050d090501050409020d0902060f0d0f0207052805060a1b031b0309030225030c14010c111206090708070605070c030206 79
    0x9005403072a402081300e43d4810359048800d41c0d0000b410300500451100264003500c9039103015803901130300e03104103e0490481460944140ea00102042c219610031049900401601e0040f0b42c5c440710710540a500d030340114900340c0d001c0c0541c2500d403800d01d114170700140c140c4105071940c034280750904038800000e41286001d400c105542d41d8291016030344820240400c0c0d00c0360b014050707454408907001703400d48070325150b0a03040c0c40c0103100020000d28081108103000511a4070781410503402c442c240690120030a0191030b502414040c065108a20340100000221072408011f2500070200308408907070428a030182d001d465005401d070124802d8001000c4a8020700c11038040c2c820102945441182c107910b0f846190900d00403c04c108840c1210041c0101551100354070309002c80d4002a1224144610042800422228101c000e0340c0301040003080480300d1044490a24010300c2041c0e841c440c40c012503040c1e01c24400700048551041044520b442ea0214100210500d158240213454006160340 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 818234217 1250 818232967 818232979
    0xf03050a0c240e0a0807020925020c01081e18250806061005180a030f050d020606030d05180103060315020d051b0a0804080c01020c0f0d03050f0c09 65
    0x201e00071510701c2e031040141040722203000303031010710111600c81240c140440801980c1c000e02184c5001c07a043c2e000391002c1c9601912600325a40c0c84040c0700e00001d60860b1261181040001d034400b09640c00204110540c80a88401c2d019032140c042140000041740e0543e060f0030008070004600082e01c009092076a0211002c03202002c2e220790f1000350072050541d101140c140b070200c0030464158100809504248292105044540e500074018018031403075644074100c80641807684590303141e01c030b4508000c680000c0c1001921100c3d01e001901e0785a822801001442420081110344c034020440c40e40707415098803020b15000ea401c0c060f00e03482c0506900355061542d0fa010020108100c0d03400f19050a503022001691244001b40d920100c55014000c200f0141c41640c3c804101c0110108407200107526042050480e03a50745400d04081c4106500c40c1450350000c506a205030f000083c212440350f14010076500d440c1c01160040301115012034a040c1c005c0030b2040491a0011f2500c02800440805400 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 818235467 1250 818234217 818234237
    0x11070f0204181115090a0b070503070204090303020d06090c0c030c0c030b2a07111c020a1202030c0907020304152d0f090807150c0c0305010b030609010501030f03050a 73
    0x1d0b640510742e0410b4140d40d411445014400c10f032402010300064420740d00d900d5030400d4407a40100701c1240361030098515008000900c038050180030016510200e038010011b0056810350300e8000c01a403c40b5510341061402c01ca00488c91a0310783c0102d042c134018964036140c5580345620b00312205d00111006890298005801001082030380c508944545000c0220562481b90140c1100407442c1d980c04650300440203100301000542540c1010082000440b107601c0300c1441d4070038603804440d034414003e42c07040107200002880c410303c030a0811828021410754600140d03400c02c1c40000603040740d81c0001a00104428400c403945a03444080002e8240b403c0c44242405881d0340c940030415030156040102c6180c00b824145500000300240700303440385030040d00300d0300e0030690720ba61304898012050503045580141140701e1160742c1200e841c5400c003000c00c140079542d041c114001c05061820a001c0e00561b80040c031039002c140a0a4101c03548029061100e0f105900c00321001d0304048460410000d1501c8 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 818236717 1250 818235467 818235491
    0x20414010312180b0f0307090e01050f0603190e0d0908060f06061e030a051501020a0b0f090c0a230d050604080d0f15060905040e0c0f010302070215031911070f0204 72
    0x4040c3c40e240a8407174815079281014007014041040383d50100081450702c1700180324684513880c824401d49010f5801360349a443d510003d1071410045540d010352145070020ba10b4105500282140e07015806072039040d4440d488105558842001300c0303000e905080f14034089011424002c004000d155942014084181c8152810001d1a032043e1007203014a40c4420510680000d1201d240140c5102400140001c0030305070703910754800320001c0c031040c50420dd140024005904c18040140d1000b00242070134151a224101c400d01040120047c6019000007000039265080c02011201040e4009004103540d56656603801c4c4103a03c20b00c201d200c840d032103071f0308000c0f0f2120500076200c0d0402e108040603045424038800a2090600d6440a4891403c0650081418602003038410300880e0035116800844441e60068011380308a80f8003d4002a4121042d041c00203900042c0d40034103a880d91010401c1000e610a000340c50441c000d840c12180104154000507030f080400c920154800707800030030380c400503807 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 818237967 1250 818236717 818236739
    0x706021c05040c0902040e070e031c03020301031106032403031204060c020d020118020d050309090c040f050303040303050d050a111821070302122802041401031218 72
    0x4140d144041c0c0354414081080310085281e00075104010302103003002d14021100c1104440130380303554180301016400244035101400405003e00136a00c9514141c03144500040c020340c401d202c03d03a83c10701000b407031352290315200084902800f4084240103090880c4412600d18000d0000d0322541407200304142ea1035006001c0485104038095140010482805900a410280040030000c00c59140007420300081d82401b100f140120b405441c10880724003079203041e034a107110300f502c400d41c00031108013007284d0740300150300500c240d4490380003032404180c1d12014113580b400345020060201d481440314084591082e40920ba12048248010a00b0380181c2200e040592004000e10f034900216a00b010791402c0600c660808624801b03c100b071070401c0c420486454202c28000248a070058140300000e02e10308211451000034103250741d9954140c0407519640340038100c1d004074026410106a10365076014002004d048a0b0491078540c48502a400300311508500c00490000c2000221710119107041c140d = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 818239217 1250 818237967 818238007
    0x503040b2523101b020d0201060f150201020702130518031309020903010912020d030b090f1803070506070801030b0f07080c0a030603050a080904052a030601050d0c2f0a0206070602 79
    0x10303a1128050104c0111300a00b480210603005095a05110041140a034001e1040c0100c50703c880414400031546801240a4030a03894060f521038040010f0480200d0305034882030059400f900c000f00e50070101c400c01d54580c022403113000f84004a03035404018807502500141440c0f00d00038000030382c18040d035803084006551240d007100140d000c402000c01c11601403203000c40c030090803030740c51020b40780095852101400062140407190345860740202d046004000703480c03810b0341c0101135581a10b031100005008000901c401c0e0740041d2a80045081705501c0c610080c06280e0680d40c210007a40c9109450302d1039841007034460f081542d10000080860f50901c40d4031955803180004c1035a03481d1050030842a1100a424910321140c002310002102500e080811001d64102c0d0030281c4035922000185c42a01034000d0070418036007004050404250700405912140e06545885035030341161701e07214104c0d5000c1c611181a2070b48000101030140c07030080c0192003054800c0038050329241c08041c10103806104 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 818240467 1250 818239217 818239241
    0xe060405271b04090f0204020c03071a0a050a0902063106021506060f070f0c05040501031217070207120c08070f08012d0209030a0503040b252310 64
    0xb010b016408004a41c158060840111001d1284004e641c07100002c0324443c12009104a6001a1180f8682c10900c140e9010f1030300000c480038103180c80f00c0181900ea404540015406103050001010003040e4491030040030340103030625003420310041c0102d030240123401d4401801020000700400c0099802010006084140c0c0a0031203090840582c00c030781031010b051144106428800d4401c00544501aa98a6600010304c101c50310780609041c80044600e81009403c9400c1c0300002c03092203100013207428024107640c0c4508030000c1440301c0709803c0300c007501c94100507003041a04202070b051010689280d540503200c4030190a0b41d540445241080301d500400c060075042404000b001030a1082d103c00144540000000416030a0441400c0e0310340c0240314a90390340402c0c0c0d245a42c40802c050500c40f0390003022a603030f580d101d1160880300d41001000039030340d58003006e681040c0700da10740b4400e103010340c40002e00074001c50b500050b014240d454001c03042a0f01c68121200304201e02401130319100c4c88 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 818241717 1250 818240467 818240473
    0x60c0c03013602010c08030c0c0a0b0108101b0e130e061605041508090a0b1504270209061f12111215040f050f011e0e06040527 56
    0x10000e54003408421600c44584900e07030b0001c4540701503604040c0c1c1e054481e5204407000d9480d9280300100c2c441c0d0281200b0f500591041c00c02090801582241060580c1ea90b03504442503071000c403002d4001c6e6075020102d21615800c5001550700280140728054507600002c2038211200442c4403440e0844044001c02011580314038240000d00702c000d6482100d04003030746444c0c0d103000d040c841c0301e02d83da14002e461a41080300403c00140c5211041c02030b200e885500410000460600c000344001c200880b00001d4440e6180560180401c1c2004528002d804121080c1a080103182d400b0483d40960040046420080e1005c100640360401c500200b402082d580714100c140c3c2207090f400d412038980c243e58102e0b001040081c44150034440744041d42c400c41c4000a00009140c2c8400300740900b60000d042180720341031030140303c0c00d041c28540c040d0580ba000200c10255078106145621a50350a101d80c2c5095840750010a01c01e080542125078000e03000c054807841082210030301201c5091000311684613070 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 818242967 1250 818241717 818241761
    0x604140f15030604031b110402190e030307030e0918060405060a0b01052a032502030d051303201314090f0c1e06040b0706050f15060c0c0301 62
    0x900c05400030010070380c10b500a2002c0c0c542950044d00d000001c0156124418600e1917840802110708419104020080d0040d07460703072070554072096040f529145200204060403c001501d08000064500d0310f6011b1b901c034001c0f480c00506014102c1e4010307120b04909241c002c00e2112240d400c014050145119a000705624905040000c00700c490240d04103041010402c040484040440710380b60090b04c209054801e06111004c0682c510700c80c03403500480340741242c00080e981c04011400ea500c0140203505079510307801c00d030604503103501c9000c1c114502a001c4400a05c041090b02070104000fa0f0300284421740d281a500006012024542040c009036454074400784807109644802604410507400a088003466084c6468940c968a5013050250329001c45410400c03c0f040c1054040c2100501060341d43c90300c0b0380e03140103a540300d004d00b40c42850170140440c0b8115258101d841c03240d00031142c014041c0215004215039648650240e910754480c8148107030700b0707980030301c40c004000080307203182401d003 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 818244217 1250 818242967 818242981
    0xe060307030c0f140f0a210506010f080c0406080607050c0c0a0b0a110105070509010f090317030f0c1c0c030207051005090c030a0b1f0e041b08010b180604140f 70
    0x30700213071038680c007035030240382500c01c1a11400c503014280c4058101f03c000d22440b42405000201420030090494842c01d40002403508413854014280c81045040d11002103090080c002940c00302c3c41000300761340c403080008000e40c1c8110003a290044c08241a1540b1400c0500001c0d0021000d41110000c4100090701d440820740040f003800544c03010500901c454503280070013030701030b00500c0345981c140507003042c01c0d884c400d1141c1140300186a1140c244030004040d4240e540c440e410443d05040c95142013070100301020009020303036121401440814540c40e01c99000c0e04050f140940c011814503409002440001e60248044c06401404040c00102490114140d9280407c48949940607403c40404a40030514040b803440d031008011484810140400200480040c0356a00840e068083d0000384000c0111000c2030382c41c0102c00da05a003071800d464504160899564140e4075a00c81d12040003c00b0655600303031419484580100f000070f50340d600a81311100e0000880f403802c1e00c86035040421601d = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 818245467 1250 818244217 818244239
    0x29180a050a05160f050a1101020d060e060316050d0f120f090b040b071b2402010605401d010f050601050304080c0c041103061005090a0e060307030c0f 66
    0x1108407819200c600012543d0300140505140b075052800f009000590505518011080c40c0030540406008541d01c1c00c541160700020311003800380c00d034410f4146000c651503103800107c100b521500b000e90502120303d040b0811a07603001e10309040781c910403040340c4803001c203040501311200c40915443e040015100c00d000140000c46580200e440102d0600042c414490b9190036100100e40c0103020342c003250071191410b0142c22182d48a0080d2041c1040d258045401d40c01c1c030004502c480da0020302445032541d04101520840384c02412030400b617442c00254442480391051420704980041d480901d04601c82d0301d0a5520f11407100a1000300e03141da040c0960b0007481820107424901c0c50800c01818076000007030091001034006411080c02041100300d0315000c0c0721800461200400801c0300f2101c01801030120380044540c3c0e44144101e9404680303050203041110b10407034008020141a60401604140c282d101030402d44c0c040c801d1402c00700009401d8005880904284442540d000b482c0c0200c09034 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 818246717 1250 818245467 818245471
    0x9030f03090c0d05150a0e0c011b14070e09061b0a1e02030a081803091203040b1b0d080c030c0705160306020712020106060c0b2d010906080129180a050a05 68
    0x1d8500c7e0590000b004038001c281107504c8882480c1509101440b2003884c1e007881c08400014003a141012450210410006114811030713640d00341034031482d079600c8016a02c8004c12140d4441e00c4010100143c007607904900103003122001070921442d03c1420a45140608044043e90800750b4800612802481c1d04003c14030b5104040ca803050a0701413071803000d40d03228007070101c0c0c050090042a485545440007801039034090811840810303110818181805c1d0010070200100c001c5001d907a00c0d10b10054440c500b4948035080344055940ba503202c81da2580220750107000c09031030a000c2c20201200790b101c0c0c16990802035024020160320358940d420103803100c0c50a41d1006055a01d08041080b0081d08402c46400c45604208901110f030f990000000c0350341c00c8000900810850002418003c8108440f96810b88031075000411003262036083c106c0c204e03603440913140d03c07919030205980010601046880c1d500e042c080d103a111101c00c440e40b907041c2110103036588031a480d1600100029160b0511442e9 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 818247967 1250 818246717 818246731
    0x60d0e010222080a120908010507020c011e230405130902190f03030807170a0c0305090a1112190605061c02130c140706061d09030f03090c0d0515 64
    0x4014501400f160740c0d460301e081e00501100800c198004558055088000208181e500038001440d10304e200a407100c001141349404541200143c41010990014140910010791981216001c0f590804011090b8007840340644010801012485843d00b010900c060400b01e10701142e0078030148100180b60124a4443c03442c1d15840504006014248851030101c0390541048009a220b910b0200e038124071444810600d03560410600c07620399000d901c050322070401503500b0041c1d83c035802030450300c0740000000500100c049031420070403441c2c40000403041c4541141140c2184a04040340412880e40b2041519061741e02c0041000e503003400c005007400320b1000a020841c10b0000d500040d4800d0300b0003c14208c03540d890034030b500e10500903100710100c1ca50f0f80302c8507900d80e1b51034500040581000d0041c0d201156650a1104a50b04c0140441e8001c8841c50040c50900c8414140109581c000416070b4100384604030303248500e40c42d1401c000f4003080c001c20150074803035000808100c0d4004058204 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 818249217 1250 818247967 818248027
    0x1d030c1014060d0605070504051c0c08030f04031b090903110118032a1b0920070803040804050d14061e0601030b1207090e0d0f1409060d0e0102 63
    0x110302e541e11814410b6440340d21483c000303103035140d40d07100302c650340500e42001c0d4120703242c4c1007000c507041986031030300904505c1000c0d4100c0b00c50300d0b451101d882e40501a40142101e01c00e01c410b10009001d485500c00c464030310800f0803409540c1d60303440c0d41964860030f0117902040d010301001072980c0c020300611072403d40109030303116a011103642c000c024502e150341c000038400b401c0c1c2e0500c0601e204400c130110100c0d0071a0109080b80865109107196441c60300c101c081e007a03e041c03031000c040c02c03002c42d03944600c1280460f034a00b000c8868584000c41d030300052040710038084c10000441c0700d070780d86d90900c13041038001c20808003008a17101d0300624005000c1c0c5603100024609000c10f9041d003016400940c072920070b180204504441c0f1010a9454402d2a102b068600440300e0104500032954088805c294504d0700302d403408681900c0030b4440e100340e413000c0390008036020901c9070308158100050000e00c5029112510b1311900c0d071030b000100e0301c001514004036500000c3c04103218500b4180c61211070a08014 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 818250467 1250 818249217 818249221
    0x110d0305240f120f0601030302060709090e0a0206071b080a060606021f020903010207080c0604030207050d0807110a051c05060c090a05040b12030406030b01020d0816031d030c1014 79
    0x16801d600321402d418440c03415603049400300082444603946501000c41210303a00d585928001e515643e003100d800c0000b481e019030010b443d22007800340c4551140404040c1c00c003031242e80c081c05440d501c1014240d0302d1011000d000c0301141c6c440e80601006181e800058842c1d00b042e80b412405030796103030f4809400c55010f5800f80034000341c4000740800c40543c610f80180c2c6d82d101007020038064058240d0207006544045000d00e00500302082c951700c5140b02c0d17420380c0c100710349a0b020456001843c20b4003908104080c0401e100085044200600b555401001b0100103a074504c000740c00c01c454500111070f103454101c039140408c04108407083c1c2000003202014140703801517000c00c1c4500b100f81f0070319100300e4681c1a18081d60f203c11007800c460214400540f640c07292600000303405004041545801442002c08200d030103446403800c58059580b0041c207041e00c074000131049000d417694111180a40078440340c402541d00e030420040c40700c010710318040d25081c021100c00100312003c070380d24200f8000074801 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 818251717 1250 818250467 818250469
    0x7081c0302122a0403080309120c0319031d030a180605091306031718010f0801090509150108010c0909020a051c0603020a0909051b0a15110d030524 65
    0x440954046141c1e03410300e5100f0200c8101d02074a80741030240d118150390024020061288a0004500c102c1040381103440c156004c1c0d8645c0c01c14801c183c1400d0030741e00b0030b21240c1c402c0148034400000486907441c011405066503501b2000948843c041c60005a0001650940341c9802412009490060014036680d81d03250030401381c11031268a00c418032a071014010020038008a41c8480003864000340d4211038680c0d5540321501903031140e00f5a802c1e0354403079076a00102d91711828440d803880c5840e550b20b00d40da0b480c1c41401005000068014501c0740260411080140c9405030264000c0000d000081610000c00c140a40001c030540c11588000740104079050300c040d002001c8071000b4049110910f0042e00000010006150303130b41000b5070246070319900180500654200308095030240b019581c0c02440e00389500701807000405d000c1d804c8500e005040240391410038005860910901f090717460349041c008401d08200e0003040000c00b1a40d1340052211042c0340041059090a00c3e06c149401010b01c98 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 818252967 1250 818251717 818251747
    0x15020f0f0607050c1914071202060706050403110105040b100e01030f140f1209010f0c0b0c0f090433060512061201090c1415030105060a02030c07081c0302 68
    0x30282c1090000c00079190415807801c2040d01c03034000254858807616039040c909145864041d40041d1502d01c078200004c80c900e0081c9074031510080d8001c191918000d110b43e1868081e01e4000c0c0180c0c24031440301c1000d5412507084c010580b00b14450103458005207800c0007141d11645040d04111001009000148002059100d03d199100e80000a81c0110001541c8003440c2c00f07007440e10001131f4040c4998450310070700e81502030300e46443c098940400f1040b032004211307584c0308000030107050300000001054424600c1b0b00107101100300c4801d042d180014940109099032543e4411004010040000100d01500302001001d50f600d07040007140000e02e80f50300284103010f03818600d8220f03548600450741a84d03400341c2e40c0c84c004000754020b1101a1250804071114007040c4152158800030104c1c5282d9843d0036403203c0e01601003c580316082d80d0a02042c0540f94005600d654150302c4100064001403004210200050640381c1c001c060582011418480840f00c2046150601d801408605002c02241d = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 818254217 1250 818252967 818252971
    0x80705090f041704060507050106050f0343030209061828050901141b0706020d090219150203031003030c0312021c060e010f0506070c0504020415020f0f06 68
    0x5181d403410b031694246400503412043c181105a4000180050380d117401c4005091030a000310000c0004035622018840c901e0440400341d40e040d0000c04013106102c2442c44d00341032022081c2c0e071100e00040640d4241c130036150300c20f4200c1003400114904001b14544030084651200096031110400c2030000d108041c4120041c051013540707040030f10092500b8003854000a0080581e4506120300c0c100a12864020300c10500e144030490701d480b00184c1110305902c1403503008001003108503d020f50a03103c8000a400c24120032620b41d84075201c000c0503907264448240825526803621904d10b1802c0d280d908409155844001035410500404ca6040c2d81110030004591701402d10707a490001510f81100e03040c51009459100d203201190f0300800c1c50b49a2004031644800b4082004000d0329a554804440c1007442000d8103140c1191041c4401c0c02d200010700444c911406489444949440015084e40c005401000542d030503060345c20311041e8104030b914030751344100014105102d00100700648030000 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 818255467 1250 818254217 818254231
    0x90c02070e0a02071e141b03011506020d27090b0102062503020c030c0a200909030d02070510051306180c052205040c151719060815060a08070509 64
    0xd400002c018081c2441c2d1b143c14016019003134440013488903006c080010101d0129501a6103005202540a820721200d602500c405400a00600940c04030884604000208a512a014038000c1103250320718101c0c600c0240814040c00701e000b522410009142400050111441203140c502c03540c8102c0b261440042e000c00d4618000d40d0b110701400505155200791303161a00144a030602c0081800404140500d0804e0030280114405201404100e0100810ba600c0190364008202d07220700707400d299004001ca00c0c8680283c2d0b102106010145080b180201c07800301010030741c50000c8040207964842c01414001c16451b5480300c010a441d5404e070f0080e01e01074240035007510b1a82c003a46890620300e61600b500070300418003a41c64140386c10002000184a444020340050910091141c01000c2203040d141c0202680362099484032608601c2e40d158401441c1500d50329000401d981d04c0612034a0b409610307075040100141404814403c4001ca41d502c14805600841000d201a581d6a0606908460 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 818256717 1250 818255467 818255513
    0xc0318150f06170c0a08010e100c09031202070501023f041a18040612081e0f0310050306060d02130b030109051005090a08040e10090c02070e0a0207 65
    0x71001e003100a11807504004503002400c5031000e00c03400002884072084400b600c044409507070b103908003400d8412092924120f60490b80079030250b6100b962220001141d40d140c1900516903c0d20760702c813444002d90704500181c001c04000d200d00d580400c07158070080815442000a00c0c0b503101006115407800c1c1c0d500300c0c400810083c49a0400303000091f01d000e003940c41404d0307040080301487e81c0305992010002201d98008281d89910300d1400d8804c3c0c00c21107902902807a42c40440b45c0d1604000d0384001d078662811000c0d95640c00c820f64541001d0400150b0309145039550741400d20700803500900c035a0201d0b03c2a800b400400c5807a8031020030004046606944900f007100104460001400152045039059840d100c401014010005950189841d402d84100100d88501c640320b600c0710755281003c0c00b02d00c01040100450030704142c00c580e10a03c0d10003180201d5807140d0b070a6055403000b840100060348000014420060b8040100d40c10844480b400c5281c0162980ea030102146c1507007060000d48 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 818257967 1250 818256717 818256731
    0x501080408030601021e030d05101a030a180b0414210a02031216170702150402190f151b02060c030c0709021803010b01021507170a0c031815 62
    0x640204130b41b000012090b6042a201c448403600b407130766600404206500e0504280c007150284030140a010f060f100d5940104c0741600b00a45801007503400906400202c5507161980040701e103d0001c40030440c1d1182d04451581d082c981030134145081c10310300000107078101c458840c60010342082840c8103202c0c180d00c00c40d240c11381d50400340d040d4042c400c00c1280e0385504108224058155804214010080c3e8440c142d00000649001c51043e0381120340b02d000d41d01610051403047c52640e202e81c0e0062001b000c0410641282c0d04120302c0d030361154030100c00288441c01c00d0003181908240d40408840601d032082c06038000b43c1c1d00b00b94019071110043e001d42400205c414003c81d05008460080181c1412102d2007561100301c00c00039440b0106840300c1c0c0204003400c0101c0d28044c0644044c900050713004250008800c011744020440103070180302030200000c0c06800110180c503041d413280c02a00c0d00004e440c4402480941035416600d00801031020101c12070b00000d4068005421255440c140007600b6 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 818259217 1250 818257967 818257969
    0xa1b170d09060f050903010f05060103050c0a08040308131b03170c0c190e090d0924030e0115030807020916120213050a090207060b09011811040306050c031602060105010804080306 79
    0x117105a0850a815500304500d00c9600c52079030f0002401858203a07010482940d411070802400c0c0108100d000014000a0224010074403a03500103801807070300b0741d00b00f2000500356101703002174182141d50001c1140b114020000c0c804600001d1855083e10b1186910306a0b080f40c2140e12040000b90940c440c2c0d9020001101c0c0c03422054800000c2e11440542c0e003941d040500080f940d6411400304100000c40c001e102080b00c904190148807422500e880702c05658290b08400d801801420034034524541d40d80101603a554000d0105030011802154a10b65410780c0b4014003000a03c005c110010301507031001c180103100c1e800300202e40d401c0c501c075000517141c240e18080d054100e001703540031982c421841c0c20003003801d10707480d402080400c0c41400d00304090500d03403017404203d0354248289400400071403010007207500f054001c6030321600c800103110f1519880759290400c0740c0c81a04c3d43c02d4510700100030400780102c1a0303807141510100780010175280d0b240c000005c103c40380003000100500000f2000c5012 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 818260467 1250 818259217 818259227
    0x1080304030611071416051e01050a1809060501030e0303131209080642041e0218090f04053f03071409030c0609030a1b170d09060f 58
    0x203150350001c5c2006000d0f0050307034810354421152528030000182c04400280078900144106008040380508016030341c0038800540d003a8201c4111071003480b1200001500c80710f1800585005401c21362400110181401c00050481e075a02240c040c00754410403c0c0803010701041d803001c40311640015aa44941040c450445200c40700d40d010355224840da40a211202010078141d1000d040802c000e10960007203242c141c0034414007400101c91158040c0081c0c240c03401d20b50011042c168441c0b82c0074a41d0f14003003156004aa108001c964540a26250010224a00340005913005201c00081180c24142600c4040e1603c0041082200c0ca01404410f5041440d424901c50701410603801550142090f042c0d5001141c1c0c0112011800110100d110301001420081642e542e904050005c02c03015001c003080c0b0403d1f61203130507016498810b4103500400114524000542c00c21600c0c1c4040d2103500e401c0c68075201c1000001d10103029003180c3d90f00c1640136071102c4500107c1d1950300e0801d02e00c181e0100c065132 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 818261717 1250 818260467 818260477
    0xe06190801020c03040515031303050307090314010b03210921030a0c140f031608040b04030507031709010e0d02040b0d210504150315170f120301080304030611 70
    0x907540003180d000010a8080041d03c02c0380c200760355000748070700da030b8110405920040380c6400041540802c1400070902c1280915070082440c1815401e0345d4594075400d200f003440301d02d40c8900c0e079141c030a60507003800c0a10840c088484030380c1905104109003410070042d4050440340e1406803800e04600051507215094032009200003409980d0707642071304030000740500042c080a0b100c044415820494540001a0724902d0040344405542041101141c0c03044207158a003041c0c84141d0b052101041000d042070040c4000c0d807090000304686480e40c5070201c00310700400d1241c080300c9401d0040300d4a50360040e2482001a4003200c07080d91040e000d1001034028549032004a41101e804000032003001003062071507240100c4051246410108001c00300c0355846a03010709200004002c485c02c8000740650041d000c1c0c405030351926500d258075114007455401d16070995807070903800324040540c0c0c3c0f1740c2031108000092404e54143d2840d810030300c00503030302e2190348402800d43da6503243c1c440e40f02020f841915 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 818262967 1250 818261717 818261729
    0x2b08070e040c170108030f0d1104030c060c0c0e07091226090f0904022206051305180109080f1e0c0307020306010e041208130209071d0a0e0619 63
    0x302802c07510000400f20000c20f0044440c042100002140444000040e00c92644e90700c000e192600d42d039914241e0140441d4401040041000d010100002c0c0b1000c00000180080e691145558140d506200020f1002507008406400301c11091080c0c0e01d60221061086d1030500030f5000c8400500d02d8110034400e01c4941c681640b83c18480303c200c3c100d03a564000c00601a081f80d2020b0151340d801c080201c90002610000d5006018a9070060002301c01b40b281807442030300c202c0004080c0c0c3d5841c0802c5000d13203441039408419076560104510048065190b001d41c0705250020420f285041d030b80d0381040d100705103180c80d1100c070110748082050400a50740100800500580b900c0b01040c11640303a9070307082600d080744a0701414001017072060925070518426034004180890b42e2046030801d49003001c0c0580b02c082040400b80c05480980c586d03005a0f40100420b6a41c00c41c2750541e00c001000b0b000d0034844442c0b0980074a0410024192101602c0da04480100c840741002007003046000041e030326a078051 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 818264217 1250 818262967 818262971
    0x1211130507050c010b03010e1b03030409050903120a0e060a021c020403080a0e0312040e060a08060907030c06020a050303040b0c04030c09061401030e0d1116172b08070e04 75
    0x5209076000003d440e00100c102d000388000d01e010070825003038801d0341d0702203030695000c4554400300d43c4030030340a80d000000c040e040d245044d46a0900d04181c0b241101c1d40e200b9603200080c2040c4c0784403a5065a603001c9241c16003040409403007407203652101c1000d080c92101a401040b80c5020704e150310078604080c0c000c80021075540daa40e28110300f5580018084901107440030080c0700c00340c103011408010307040d0340018061420381014890241d83c403004d0030907904440415000f140c02402080080c2c00394400000408181e880c40c0380c03801c1c2d008034503041042103410070000c141c000b94002003642d40080e44482240e10b00da461200e80d0705140265030010f407070329000c1440090705100e82e502c00d80c1a0350700d1102c61210099104019810b4034400c190031055030340403c1d202652684100d0394604680c33210b00a5030300c1900c80001008030300c2500d420001d4000792038144456900d1003041004884c851404074410103200300c08041481d801c0707111905050160060000740c14511488800c00d21003801402 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 818265467 1250 818264217 818264221
    0xe010b0d0c081005090703060e07030f0311010c0504420c0507081b060a0e120f01060504110405091807060f08130b0c0d0e0a11011812111305 62
    0x80c10742805503100d10540c0b8000c2e07420080b0626101e01034284504031000003482c00525541d0b41e90700800b4403103256491406006404030029070308080c4041024001e94490039204862980786c0d00f10744880d003203082841004c00040100040d40d40c25074940c2c080c1d4040c00c035102c1010065010f00e05400c1d011000b26186414207480f0f640d9000004040b60300c2c020021120f100b41c460410503954668035a40c1035041a1040b030000d1107103002c100410909185151a15003116600007288403141c071a40c0040a0750060300b4800d001c4e102c24030400004007401ca41c14080b2101081e503e40f00d521841c000c8500400780d500c00030302e014400044001020190108858803e940e42500501c50310700c0660100024090001144400515000084000b5048820044582c079222062902a0b200e10800c0010b107440b400001600002404020003450140142c080c1c03080c0c8000c00103203240c40c0c01d940076a21554520b07040c0013a00d44021481c01080c1d000b0032581900030f41c04009441668200200e03101e050400d01 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 818266717 1250 818265467 818265473
    0xf18060b040308070c15080105040f020c0715030e07180c021207050a030e06030f0a020a111002070b060108010b030a0203060d0f120210060617071b0602031e0103030e040e010b0d 78
    0x40c6a064007440c6000c40171a10b907000b0000c1850b0b0851351000090401005101d10b01d810390158100c02c41c112401860700020340c41e42810003003564084203050640140c2c800701c1503018050700301c55000200c041d01c001030420180901c2112080c0758802d020361707a141c404802c18002c1201c0c0320785c41c030741480d5203441d1486072424581c1c0e008113400440000f81011744d040100e040c42401e0700c1c000e2206c0044a803403071391002c000c0030094105129080402042941e801c806003800c6c00742c506044011040540d0b1080c40d800c2408007154003070043e5041084440c0100a1141c080c020b0341e0b04000c40da900175a607603c0760000942e42e1101080083e0030800761010100400c1001c2e282d0201c0065a5020b50349904074092a21003142c1c0d181c811000131494500800c0c4142d412010034035848000c3d401e100e0521b0342c410307184c81e0500716815000c9603a01d9000092004c200c000b850024585a000c0b1944001ca41c15a85c0060950324184280c0e40550740300c4600d6000c541007900075080c440e101038942c40310508142 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 818267967 1250 818266717 818266733
    0xf030a0602090a0905060102061603110a09030507210303091502120610050c0d08180a050d090b1c0510171b030a2111010609061e0f18060b0403 63
    0x91162040d0720103240020008018017450388a894140c01808803551012100c00d940328444a00604065682c0588603e112000c1c004c1c000541641d912040414207500c0e0440c078000c1107800c01c50f003040b0b070700418035001d0000d645004549a85840c0100300111141b4018503480e0154800e2a01d4600210f40307500d07004407482c00140b00da2012118101d07043d060078420303030301c510550100340344c65042911201502c46c0640105500b04280c1a1501500d01100c03840da41060700c40b10040301e03d9005403451801040e4883e186001070b20f81410100d1804500174900d802060340400c0040e00e49840340009082c800b9000211001005640c221004409161140c1a1544139541e40c04a10100300c2d05c3e480d10718100010081d42d540d50101e1400105607003280b881900c0c42c0003502180800c050401d85140c1b0350740030b0060800408078010003141d40b505140c4040000190090281d40c511a450010001d40040280d60000c8620230400018085a0702c0310460190055420800113a0700010b40007080189034 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 818269217 1250 818267967 818267977
    0x170d0501121b0b030a02160f05070503070b1306120b1011070608090c0108190c0c02010f030e0c1e030304030c14090103030e130b0d0309090507020127020f030a0602 72
    0xb403840a03070120444000014050300b68041e80140300d00610024008071000c0e8000c000100c00e0036628800003c5617a00c2c0c040042801c1802c4982c0e401001d420071141c181004204050100702400f81d041c0490b8520341524131440d8400c01040004a00181c040550317940e002c925440d1018084240d40618600003408010020b50038820910660100113406846080f02d41d004072105c2015241d005070040044034028005080b003c0841074120103010030507a603202e4041048100c0d1608401410f8a0002402101c0c0301031a5005047c10680241e01c00140441c200440080440d0186208242d5410317802080d0844a003d54240c48009004006d0004c02a1400110350f000312141d002c048045080c480f03038407820f100003008601086201e0401c0e00d401c0300091020040c5643c0050a00e200342e0004445901c680005e0b4007094280100f80071505803409115404942ca00092051481c9502c3c2c1402c0040400380300150007620300c81c0d1004541d290415116180001011900c0c84582030408034000d41c4a = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 818270467 1250 818269217 818269223
    0x5100501030c08031c0905120313060605220923030c0606030c060a030f0b0604030f14010e3408100b010201051033030c1b020904170d050112 62
    0xe15440041c01c10f00010071501110a43e4800900000c2445c1c0c1c90000f038032070803200700c60034000c10381d036544404111005140318070701c0500010304101050030031000304c84e016004107028900c140c802c4203490010031085403030300c203282d4030020316140d06041c518508000d01100e03290018015070b61540c0c1c3d610000143c00c5507900301c0242d40c15a2655802c05a84a00340303441c294102106000da00780075402070703229000700125200c0228201ea68003001840c0c0d503010703420031124001110307401130503c848003049105610301c00000b04120313410550150303512104102d490f0012680e04200300c4c0100e1801c4200002802800000380c003603900c07004d4050301d4084800e01528164500548180d5a42c8140a9940102e60b802501c02829041a0410000300d034114024103840c00c00c00c83c000c8001869503081000c682c001d40d00080e450190100040407402e600121400c9ea1000442d582c01682e40c44d40c40720f42180d40865580c88086003d4100406401040d10b030000c40c80c54080006043e0040d510703810702c42d0348 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 818271717 1250 818270467 818270483
    0xb0603270a0b071b05012d0e0606060901020f01020408011e0213050108090a0b0a05070e0d020a0b0325020319110a03232d2502010c0510050103 63
    0x400545400d0791070803004000351100d4000800310704218083d5041800080d1820f110a9050390191601825100050807c440c84046908a1700c01481d4031408440070401e049014072a40c034007808900e5032000e015201601c111800a00303406680c5c02008500440d20280009648595541100768001c201400b8400c41c0d2035401300121b0031003d0180b085074105034083e000ba0a01030705007001118072107801800002e80d481b9800e4003070b003c10749040c22248180d40b4008045007900e000342004001c00302c60001d260007080341c920f00c2030060b61644c0548055480e0007040544a6403016000c04a040c410840504151004010f450700a42d0110003059040d081d00c00c914041580548200c40c00364203210940000d401c21b88035440022b00c82c0024080103e50500f40010140c035074000c800c0d03154441810f5080411031803840707103900c030520042c4c0da542400d000e1341c0a0801617100070351840e13403200350300580068803c102040c04580c0208440ca00140c3c201040f2020511060410f034000c0800b0300049e42c0d102 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 818272967 1250 818271717 818271781
    0x2010e01020d050307030b2d03101a1c120908010510080a0f0501020c12040503101b08041a0103081803070605040320060a0c140604021f030b0603 64
    0x25000149a200c40b00c0301d665010300d16030310503a04900030007404940780c2e40003003030080c400103003c007500d000c007800300c2c00280c00da8140c205041014588011003000c1d250a41c01e0a04650181070940c0003441800070a0395102d02c24003001c0c004c60000c0820b1540200444030022040b00200d511101003020f56029074002c01079600c1f100091000300101d881401c000794000886080001d0314000340155880c0f0840c000750514411440381410b0000b00c084c440800d083c081000c0156240c01c005118000028090400032409050020f41c881ca40c440228407d002c010300c0032034200014a204131129501c03000406804c1d5031245407400e6140e0200d0350300107060034a80382142881c41d01154040031560603444503460140f0315590b1034091041e005007946850b48a6040444588a810050028165603038a0120040181c0b909013013101039003006445540c01401003100603120042088400300d80c400c0103c29213500300008a0190428144007030308102c1c040140425a0484000302c507079144540100d42110f = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 818274217 1250 818272967 818272969
    0x80a06050402032202010c06020d15230d170a0504172a040207050a0b060a0801110f0d180c09110304050c04020c1606050712020604150b0409021302040302010e 70
    0xe0f02080d200340b40480300c40c8011648000c1c0c1c4942c012009131041c1030124500c00d0329260780c81207811800000b800325880d01c141c41c1d03912291080d00c00c003514030703a11402d1034134171026001e00446008903115801914151014020301c00c0301a5810018120800c3d040d41d04c802880380202103801c2480342501180407465118541400843d0007041c010100070b02c103c17100050710400c0151b9105404c40e03900305501300101c2c03012890921480f241d00b0b000351169056410b226041c40740d60802588100c106900d800707503291440c01540e0403074228901c1000d125413103080804004009101841d00c0a4032102e1842c1401c007084441200d42e0100c41e9200e40c200080207103c14620068442240c008019400c5040040e103585850303400392031204d20340703030480b8014070014000b48404030340d5410110201d14082110010071604a0780a41105080d1003d041213082c1561071031105d41c89107414104483e200d84020015803665880301c604d554008101c6103e0380c039010901ca00941c030500080e07002503844410a00c1c9 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 818275467 1250 818274217 818274221
    0xc050903061f03140c030609030408060f041a2502010207080702040207060212090105090c010e0f090c0d0c17011208120c07080309150f0903040303270303080a060504 73
    0x104405005485540e0300c4103210b02582e244014003440c0c034400000301102084040031088400d81c001e8000741203003c0910109032410300005d1509590703a1003044203104480011170740540083d10070038a9111a21146407083e1070048203201c2402d100d40c4403040280d4403050103868094545820b24652030f2240b412002c03800e074442c851001d00460320420400b801402c0c264000d040d4140074a00050500015484c1e260241c1130039101d41029039150014004110001d00030840c40950908000c001c41d400e134000f0840ca03540c2495514801d0100c900080c804100400c111403050000d0700f0100100c0100c1c800240030741c900011449914615200080b03034000c10640300001030380e000f100440c2884400c801640d960b0b40010400c3c0b403084801d01c00040041d41d03040c0614012105c0b14060035642e0b507820110202010004e021046031030412043c44118080401150103803501403030410100840341c0e0f40c1945c500c0e40c0020800244148450000906500040c0203001c1e05290000344051669103081000f = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 818276717 1250 818275467 818275477
    0x5160f0f0507020a0e07080103031206060e04050603071a22050f062107030b04051501080c07031e020601081009030f0c02011b06020a020c01031107290412030c05 71
    0x2240340400035100241c02034001d030040c184000c15510809858501401d50703108151440004110840300500c10150446c0d010904008000d80410480d403a0002c001c00109140e031030940102d6846002c100d140c0c8003848000042e0404008540c5683d00321a941d6400c0d900000d80140300e0500ba50300c1401050441c0745040031550000c0210314400081010040740e940440044482c8078041540c5803041648080321a1155800c0d48001504a28034000e100c1994801015186a0040a1014100b5a81014405030400800030100352500010314081e10720111608090b00180803005141515603030009603c0d05a40604080c1c611504604110009454403a440100461246c0500b284014800e40c21007030340c0ea00516101c2c0742020b01d01d006041c03550410205840721a000900e4070107a07601003190040c618420328082000403156a40d442070360090303003001444004011524074460100c00c00c801c04082d646e080380b003040d0426150074640d1003a030040703010200b030408a914203c5405039003691 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 818277967 1250 818276717 818276747
    0x9030114010509070503130c0602061b120f060402040305010f0e0706110c090a0b120715090e0c03091e06070e220509031b07030606090618020304240516 67
    0x14503641300d091040d216504014983c0300c1d054400a9241c000c038178450541d100a1900c1d030007400050800d0020910510050702d0b601c802c998003000070040d403116100b607213584031842840c8800b03140c480c0c0000402a104941c4040e00642c242200c00c4141c848035400061294004d20844403840d9883d00180d640307500e0031100e54400e030072640392079080e07040c800d051a074042844940003e00c0c89070500000c50310014003001511a501545c000d00101008a000c0c03c0e1107d800c2c20400005480d04c0080300070198018205001000d0200205200d14000c00840034541c9200700340b500010340d0000407998504c02118840005020342107140c4203410b007c010401705001c00b600e002c0310f12901c410441c000d400d014180d589117110400072440041c20640701c03545010b15900280c1411481d5082c01e03800d840b00c60700704104442c50701c4030400003440182c40c25003052104a401680307958480c03d06810610780c20b4902584400303e4420701c08000e100da40201e1003a58204000c0101c000384c00011034442010360004 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 818279217 1250 818277967 818277979
    0x100510060207150c06090f060c0905060901142a0c040203011508100305070803040306060f0f05010f05300702060f0106030e1c03060e1b12041a010b090301140105 71
    0x280600b86120015001404072030604484413095a81c0d188100c425800c016108000c8060315241044024007422169401ca86000824641400c000800c6441041c8101d418001c80005040c01029200262001100c0c08100000080084403844241203210307158414a401085d810b05140e16161003900d050f50b4181101c0007030356040d03c00a882c1c0c01000341c1603c0e00b00c0c0e808000040020303420065480a891078074040d54079186907240c208142c07803007608080341c1449490005c0c03203280c007a400ca410403600241382c41c0c040e0308901c010640d02c91007601917510112400001131340910b01840c0084640d22403c0420f001c040d80c030803c08903200ca00690300218102744a00042184c0d43c426048038000c1030420b0240da0604015200591840c84030b0b03500c02d00800c3c2c440c00d007006020b505412682e030161102c030080340c1d2503203041c030003174141d12441001c034244030754480101d01486800c2907000704483c010458028203585585641d8819007040081510960030445a007400588450700c00c1e048490241c00 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 818280467 1250 818279217 818279219
    0x224090f0109260c010903050c15090c01030908040902030a0911060a2f06040f0224030a0f060902180405070e0607020409110307031209120b070e041508100510060207 73
    0x50f190310003050800300804400902484040b020284520b007241071203500e500313a9986100c006903091201422000d0591683c02003007204001000c1800442112300b442c00081c07106c0145802c0d00503000302e40102d20018404001c0041c120401e81c00307500f44038021030700b40c0141c0c95000b003000841e01c00c520000e00054a2854105c0f039911000b11a00d4004040b08404407501038800e010350f1802000300c46c140c0c2c1c150710780459a0154104201020b408165082101d480080d00c00100001480f000e0440c1907407554030390078881214081e03417018000c1c03d40401c09641c0c80f00c20080420303a607080000130921991410b0003140a50340138110113581040060310483c20400359400b00001016140f03019603000c44a031034580c06030340d42409448003541c801e54010740d490000b24001010101680c000c4403940f800309000c840414a82d2106590003152841c0c03000758101080049400780c6942203c4c0d0008441d6102d0100d50504086250400b00100701c0c8100920b66a030313505109500d08a2240380c001d0303000454 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 818281717 1250 818280467 818280503
    0x1c1e0201090f1511250311010306060f0806041d060a0b091e060a03020402040312090e040f0f02030708060c042d0b21040305180d02010806010f0224090f0109 69
    0x840d101c4c2c003407410002d4508080d200300307400ca4507034240400c10b820b03400402024401c03c4140049401e604000303203800c0040303d046c110080c041c2c4010803440c0041c07158010000d08547d5071500200400200d29405030800c64803400070071795894098030820042810413240510303505000d030320244540e0340e1141d04250f40c0c903e01d8000d028901d0141119400001480c00031015880318001000118400c0d80032941107890074000800c0959590481c0c1e00c80d003c0c11051002003020b8912069940742c1018400300d2000c20f42c070019251144030f0b848505d0a009034001c100d6035040d01e4002c1c108a52210b030000d00078241c0b1a500300301e8070f44a02010f000e4001c0b0b0520a10100503840003a2003d003264000040714144502c070f000b0f500520403503007100002c50003c0c840e134519260083d113000300d00043c0c0703806400c0f4006034006440c042e0020103d9042140c814a144080b41c800c010b03281000a540340030420401c00703405d007500c0d800821241d90341e05129142c0302c0600081c0510032048400e400a40e580d520b4039402d1 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 818282967 1250 818281717 818281727
    0xc0313030905041d070b1204060209241806030f011a0c030f040603060504020c120d3e030c0414040e0102030a0c031b020a021c1e0201090f15 62
    0x440140d040084019001c00c09480354803460102050303100c80c1c66008061400740d24500140c541181940340340a0052000c030b9845200929080365000501580300d003002c5020520440310840344100c0c0d0b40110100e031078442a2032000f04491583c0541c450742c010003002c02c1c048030344400e0303480f20607088941d80100005024020010490076440b000d1a10b0001c0748000703240340d608a00e10742034100e134000504028494043c07180e200200015a0203508004482d00c0b525101e0388109554481c0840008000c1203500c0e86502030883c8520240f1426130b0724421105440082d10a2090b006c0c17011011400307040c090700308109403403003000402501d1745802c3c10140003000d41c00c0790054071508551107041184403404203001440c4502d9030440002240142600d005043e103034017607444c10801d140611050703440740e804128541c0c215010303520700280f8807403040460550040c081d409440ca035200d00080e009071480303441e5041c400e8001da89440c00291203121422a280b020301c00c2e12032102c0341d501a04240b84c0a4 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 818284217 1250 818282967 818283001
    0x16020d06140c0711060d0e1c0e0901180b01020c130e01050c031017030405090a02090406090b0f0411070507120b0a0506211204270b10051612030f0c03050c03 69
    0x4444003042c2c94841c2001223140070058200311071101c018100092035103600c4600301580c00e40450b008840c0c4e51400070b01009210b0320980d03442890303850303590b1109182d00810010b0744042e4040c20b016400c0d164034440d04000d207585007040000354203083c04140c1000101d002d03030f0300030310b040e00081c90058a001e1000c0c918583c00d01c10000350340014032000483c0c0d622541000d1180040d403601603600d00f15082004100d40c5503400040c06c1c54a44004001a6203c0618000c1000c0d8191400191300e130709004812054081c0c510028014480c580001c41c0300342c0e0400303c204200313200390484c5410b501c0da42440025248121000d40e000b40c1c10304004141c2211b00069144442442e105681e81c000b03020714032103c1c950094205103400c3c1d2910b84a188900c0c541003280801c0209540d08200300ea4200000802d03400010740c003082041070110710108060b206458600540e50320001924000c4007290001d0050081681da101903e8606003845803287d02030f00035640302e1483c03180f900d0700d10303561580d5503d900080 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 818285467 1250 818284217 818284237
    0x60a0501240e041d19050304271503120905061603030b03070e010f061125180606030501090e0a02040f140108210406020c0616020d06140c071106 64
    0x200305440041903e8030300ca800c064008408824042c400c8060310149030501c81080014110b164000701c4000c141c0100944041d42d04504090801e0702c0940528404c000c03020320201c4486240108001ea9130142c0c402c0d400031241b00d460012000352a03c04c0584020703803c3d1250540241c010400390650403051407210640510034100020a206107501092800d0320940083c0d10310084880184a40e68071083c01400400c881c3c9000e030030f52814101c2c030355298100070550700240c1c00304011035265000340d09692006007844c41803c040000441d2108409000d10b03101d0440807070b16050010605000d907000e50011a842c0200820054500364240710060030f5104403044d859549880410b0189040c8100c40e000b810f21000810f41f54004112208032803062400030b0382072020401c01040225000304041199103411107106440d07801604e4a000c10140c1004000d500444a204203001c11900b03a0090004505507100c0d0949540c8282c500540d600c0740080241807204500030a034024541100100323407000ca = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 818286717 1250 818285467 818285477
    0x70b0a020f030a06080106140612090f06090102090112092109080a05100c02060124031401060c110906010518030703060501180c021603030c05120c01020408060a050124 74
    0x15590a10605600b082c0c4603040720036181c400c00c00410409000e1000900601d00d00d441590804500044003031080740f0b814003814954200080d00d4440c00c0c0401000720043d181035441520340046034030300035882050711a0101c1c01100c1c04100074020751007202c040c50381c03104150b14000c900b01c0c280313070703501503010a40d0b800c0241c40e4501140828050044500c07040c802c070300600c0c6802e00366500c1000d0310404068001154404401003098030400407580d8200800c0c800d141c20000351b00c4000b24050034244030140c4059107148000600103900c0301c2d01c00320355070203560301a82401c40e140c10000110340580c3d0140c0010814820f040010702030710811010030700020225203400303659a54800036250300341e1081034031000d51100120703d140240521100c20000c0c0c40a0501da100d007500c1510600c3c40c5020107130400c602c01c01d1480400c0380400c9285241d4208840d00c0d80c5540508500e81e000c0d42c850f0080d0403241c010480461403c0c0c00300d01544d4140c0d04032880e440c400c030b101c20700c2c10b110a410a80e0070004100c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 818287967 1250 818286717 818286727
    0x9030303180c061110090803040f060e190210030c121e1503031115070309060f0515030f0c0a0501030b0d0b010905060a05091e060a03021203070c0f0308070b0a02 71
    0x30b0040c8407958020319a6480e60b1a4500c5500005410501440700c20f040721414103e80f0030020704008201e9a01c0782d03008100d42203411a40c100b05004080300002504071b0310610200310b1a280c81c40362295074140c422180503031036904801040301aa800c00036010042000e28100783d001a655800824259007100314803211000745141800c180d45480001c0d404a030078901080c001c2c107034400084c414078442c01004241c0039541200007801e01000030b01440c10540d440c0001c20401c030b1250410791503040014020b00c802c0c00c14601c1c0000014100300740d144039102d524140d010194001c2104019844010b1100d80741602c0c0000540240007908a101d03032100206903d2030029102c02402c074041c0208040000d018500f0f1000e02170310460030f4110310b115082c0c840030807041c50341c200c46500070f6240301e08003244aa1100340100b9040383e099000254002c41090341900c101c140000034111141c01220440e140030703a07503030310a0501031707990001619086040054002003030315500410741240728444014900 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 818289217 1250 818287967 818287973
    0x120316140a0b16090501021609050402220c11010b03062d09250806271b040c110303010b0703120f0b041401120f06020f07080304031403070903030318 66
    0x16040c210f5041d00c00b40200e190740c4250315480890040901801c2c00141140c40300c880c44c01703c4c40482c80c40f03601c0f106501c0c1e0000a085450f010442c0202d0701e114000c1140594605c5001005040c0740d00e84075000440c0403203014110001405841580c01000d0041c00450b140c006145c00940443c04201c24000000004028854125030700f9a02c00e1440d18080c04540004416041780e02446101c02c890140c0304107818442c2c0f48021496581284440e24a218035120f203000f811034409a0016811045c0610340c043e450844150544840850307044808100b410030300700c002e03109205500700c070b030025500034001400714150b402e0040400e5030007401d0406d250480442d040c415146202a1108907a40320340078111507062500502500c450401910031082d814500390240b01c1604040240614213014600c41c01c0c0103090b8121141c02c0c40d92001103648450504009840f58015101100003500141c01c46c000c81e103221050324000d203556a03402d4500b61441c0c0b022005803420301020354582440001c16000 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 818290467 1250 818289217 818289233
    0x110a0c03031d010305102310050d051807060c050a060606050a021c020319050d2d0203011d04140a0b0a0c020f0c01180b12010302120316140a 62
    0x1144241d41d880c0c1c90015500c00c0b090b0124210307890034189401d0000740081001000c0f142c106132000082d5a1140ca0074484502c1c20a40303d40d08000d403c46140c816280078140e000d80202151100b42d0b00a0285444481c0c0426540d031504c2075544458000200034408a44511480403145010742c00703c40f00646e1740d456080c06c8650660091010480020300341c0d10494050200c0c1701c8a10482e460440c1141c400f1502030f480303100724004442c40010140f901c2004c1c5006006030b030507030702c0300e004104112032031103160102400043c0d180d5400b8552004060030701301d11302d0007140c2c10780c0e03102d402c1c00148842d0f88040418048010308100c45108985015200012003000000300c100d01406d00c044e0181030540c4500b007114080fa03026400c640000a0a01000c078000510140e146428030f06030789030601003c21090100c0c200d0700500e0329502c001400c0788425608900f4a410703a4000c450002081f581810540d80d24450a08501e200b460800504004982920008ad1800544506684403040c0f02da0325403c0d = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 818291717 1250 818290467 818290469
    0xf0301080c010806010c05063c071107030c120c12050606040e0a050606120304081002090301050a0203190b13020d020301140d0b041401021608070b10050d03110a0c 72
    0x85562240c9090400741da409990280c100b4428200450048015201d0984500703004003001405280010031005025084501200060303c01150700582128040c3d2011011004d03078000000030000702d100c184680300812100100c0c1e50010000d0300c941e2070800b45205152035035905503890890040d00091280b00e480c0c641544034803070f40181c025441e00c54108402c480e9002c2c03044016501040350040024000140c064003d881210314207410001504900e10710720aa4200c400b03140034840203411110f0854010b880342190440090080d07030740f40002e86089004c12a110003010040f40c09070610b119907680007518901c40900360200c080703641650034003a81e00003800008110307800401000990321002460342c984c0c0d070803140c00004401940302c0002c3c401010748082c0001c02c0c00305182d81034107025812119800000c61404100181a00b4015202d820000f402d5405110b104002029000f08400300703400e4540c010001e44030005c45d81c4041303408001c404d0028403540b0550a400f0003154919070344034 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 818292967 1250 818291717 818291729
    0x29070602030f07090b040f050f0d05011b021525120515040614030a142d0114071e05091801051807080106030b190306020a091e0b0703050f0301 63
    0x18910f801c0c004401046880960b000c0c44482c0c509010030302841a20409a2040f2581200e180842802ca00d002400e000e8042c8802040d66181c181d4414400d03c0c034000c05c8800c00310b40c0e000e41d42c0c507000c9101408110384c0120366011000c21941e8950701070f03445014401c4903081da40e241882441c00403c800500703c80040e6600031940c0c7c2d100400303425a24040c00fa90b000380807102941118030003010701290350f540d1815401452902d40f0103c1040703c1d8010022030b1000c04410302e0340740300f04000d0f1184c5604604d038280c00b011039500386000004180d0941c01824040c0d40d4036516814101d0a6582031401d2881d00c4101804000e010807030494283c0c2c0301c200030340881d4490024030400d5498001040a00507040319051a0800c0b0801000b1a041d00030003180d044403a0340c10049400302e800c1000075030782041d45a446071a50200b49001c0180310042e40502208052616060642c58035291812030400c1d01c03e66005503241402424848413007010b001d001043c0c031174181a828200b001e90b0941c103e4100760000 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 818294217 1250 818292967 818292991
    0x4020105030702011b050c0c0a050d020603060d1e06180201080610140d0204050a06023706230c0705070b0d09020a030b0702100203090606010324062006012907060203 73
    0x407c80c0c0b004180401c2c14005801c46482005034130b00070228010038820440640702d8000030000402a0f1941140040a00d0b403000701c8000340000c00c0680118000400c80135600145055011410803002c100032018154050f102d103800c0c0d80d520410402840700c4e052412080105102603a106014204064410000c00341c80150305c45003040280000407800b80d10450455202c00000d603984481c044118821410b42c40c40c4000e02000000625190074802000800007031401205001c0f0505800c40c50701000309584149507640c031283ea00007000d001e04500500349030002c070340420509581e4001004884c01108000c120b80c1a90380002d29100102e078010790324031885000f0408180e6062102c20528510040d0031411412300204056070740c1c900504e4141416920400c50311009401f040c51604200348444c07140d001c5440344d82c000d007104407031000c0d000642d56884005150020205145042e2420340f0b41c002c9610700104003d1034426440d48080c4011401042498080f503542c1c00214401d108406407 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 818295467 1250 818294217 818294227
    0xf020f0d08090909010b1c060b18151f0305090a12023403021003092001090b030c090d08040504060303171305030405040b13090b25020604020105030702011b05 70
    0x203004500f0030040071113029900d0130040e03c84a6881500345901d0850086280003078800b18a0902d0060404280c1720b40e0010410466205c40c00002c14070307620840b036090301990300d05c1000c070910501d44a400c42c900142068958130701c9134103110b5802240d1081044c0211064510141c0342c018041134581042c40068000c5c826101d00b01074007030318201c0481c1080c0c00c0003a0241e00300c02604000403860200911455000d025103400f144284c01c4110402c2d0008070720001d01160051500021943c400c0982c0851581080010190013003001d41e4403036480c130829240303071500f203201b04901c0c00d1503803004a8592078140030208241d02e641c481c1070b010394429254585626800e03c1300709141d4030010700d10303456008041c0180b400240c0100903542210025038004c101d01e000d40c000a0344109164401d07030301c2649408034250501c0080b01c01d13075000301c12101c0201c00c9802201c0701082042d10800e40080540d003c0d101150055114030003c0da8020890720000824540c08402e294200b941c180030b02e00051000300f1 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 818296717 1250 818295467 818295469
    0x131802061810090b070b07031d03190206011802090105041707090b0619031122091401030c031e050a120e030d120218030f01050106090e130f020f0d0809 67
    0x850b10400c0c0114204500b04514000b0101107901c210720005080510303c00205010f90b00a03000b00c80e8155141022184400a0000b17690303982c1c00039020850210403500c000600c160020070a075040c0e44581c400c2e5644010380032551030282d40000d42190422a04000019038802100c000050a6080782d0107400034520307200d00c0801381d540781c03d0024428130302081441040303688400885a2444c441c1000703c5c821180d80340348440d90040140030f132998032081030304003401001a04031200760f8108d980108803080d1901c041403031000b424000105a01c49060003400400c00241c41c045809040b601c82c03045022655070f44c0c506003520070f41d045580350b6004400011160b04840c040850362000c1d00100040b1681608c020300809000c0c0c02044c0c12030703000a034400d80c10708118501481604c05011130b4510200d0403285802130a00741f2802c0001000d802001c1500b01d4000e03030842c0110072042c0103c4141c01c050b250809054200341d0201c0c1d00c0300c1d46500b01d98464580e4100349001c0e0b40290150758960759100 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 818297967 1250 818296717 818296729
    0x5090a0512031c02070c1401082a04030812090d0207030f170c0c0a0b0c0d230c15090a0803040206130503010507030914030406210212010e07020c030c1318020618 71
    0x41c0200c101c40c50941010310340e03640c0c40328409e940102070308094150b810541010404450f880940801c806e40c0014005c01880030205c0200301c0c0d07500b00c0d5009940d90b520301c0821500d443c40f4007420401608802e20402c0440c1140000e2080103010702c04150b008091202c0e01c002c40d5015801c243c80c01d40000242043e11319040b1481e000500001210301d00c0d100200442070713145c50121300724100b03120348048c04a4000311490024128403110b1440c59641c1c1464090b05a0b49801c40c0741d84e01541812074001402c180404949801c1c0381ea404007034241103807184e07820001caa801003005481d5040e810b5500040d165824001c5500036551610005040d0b80030741001c6001804035000c031070f0194420801000401e0340b0202c04004110313041b035000c1d80d803508000d00902031f109041070040003804401c0042014403e55294500518440d02181c6c800d4480070b040c1a110f0078010000c507800035029883c1b00740c44509400c21651034260074490007407489c2a0b400500366030024400c0e105103950820610f64113082c22 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 818299217 1250 818297967 818297969
    0x1f09081c08091f020c101107121e0503091c180e0402030c060306030f0714010e0405161407080c0706110f030331050f0d05090a0512031c02070c 63
    0x800003810b83c0000000d40180603c0c040c400b540c441943c00902c031006140d00b402482803101c81d00806201c1c030300a000680607190010082038518140d4000b03623880442c0580c3c803040c5c030f4104074084007980b44c1d840481550301e90001410401c3c0f40c00703844500400180e030741320b25a42c1d200b40d588606003048444490308990301082e800410a050b81402444050f031390000c2e5980c0d10780400c480041c1d4030b41d500400309080c4404980e00b407a0a100c1c10101107880180015840c81d224003e07600e40483c1ca41100400c03003640c006a4209400d05e504450329081944100c202001403411801500d2031300301c90350f4401450754040a26000130b44c120080510880f5404400000c0441d0410002c1c440d1444d810043c640702e00c0f0240450000340c2100319501810321042c1c1c914000001c07140300843d8407030458240f01b61941e10341140e18801d4054180e1910307080303010350305441014a016098180440c02c160a0225841c15a080c195840c8001d000a050750508559018142065440050707261201442c20035144091 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 818300467 1250 818299217 818299231
    0x30206130c0b032514041a13031a150d020d0507120b15010207180c090b2a0d0f0c080c06070507030e04091104051302090705070b151f09081c08 63
    0x35110441420305c01c51420741e001c1c0e0300c80c1c00680e401480311f2604c08509204918450b040641503074000418008006900c01040c60384034103000c80751f07440036840b8060090b0500c03846c0d80401401e03041c1025041000805000c1885a01118030882d02c58400300d61040c0a16000c440078000301c000c015000140c02e004c030000c0301c800c0c00100816410300c0c0b2148203e0000c07a00c0b42c94216038071010780c0011440340054100801190700015a00e5050098603082d032018075042107500c80302503481c609800000945110759000a941e0129505454541158000f212000603034401909000c0c1c211106000d001203401109140c44441d96280700f490003521980300290433511036454190f1040214200d4083d200b401e1904031000035160b0f03181c1c01c0321490000012000380d0004a40d80030024036030b800ca0014040d07503004611394009582c4889412602d100ca03820003e410103030890100071034070420900c84a020f8500c2c1401c07500c141d2a443c18a16100c1001401d041e4004106d0381c510315150049151900103107 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 818301717 1250 818300467 818300477
    0x5130b101a03010e041b09060e0103020405150609010f0c0605070309050d080f07030b0111010903081f1203050c030705011406130212011401020c130506031603030206130c0b0325 78
    0x304d40218420300d0318006102801c0d141c90740e8449018180580c2e10030014048000c000c00100d43ca8110411010001340000ca02540c40c001c00310f034042c2e80c062010840707904000d0409140c140104c0045507140107607041402031141c40809580015240d0103418898000f59500080c02d650070704001c0d03d0305488020178020702103030301d00b2300c10752038012011550b000c3d131942000300c0c2e803030034100c01241c254894144c000243e51a0002e0300040641c001e18450040001c282d11320b4418132a0701c241034005201e441841c940030325015070b61002030b01400c0909100b402d01c07010b0b01d08005503504c80500755510845072030310113502030003006a0780c0f40c05a00d402c8602c020324401c5040080c0806c401f80c9010b0180216000324001c5e0503065001d03842080220250311001d401c074212510307200c9031600030703000c1901d5480c824064185020100b5007050100d0007140d40550041c00c881e2640f603015624461080700542c0c0b02400aa03000c180a13080c0e40045004540c0880d000a169103c006811700200328032503a8000c200e = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 818302967 1250 818301717 818301719
    0x270b0f09090f01062709030e10020c0f011403040f02120616020d0f1d120106090603021e01140c011d030315150403060f0204090e0708010f0501120605130b101a0301 72
    0x30950701c0c80007a031540c005900065081e128203007079418070000940249d0107144401d0000d181039021030240d000040965481c106840300000640d44001c4100c07124000b01d005000040102d540e540381e40619500192000e0481c1100b84d03203481c2480b004a50002544000140c450407195042000400411142c41c10303510070041c12200400000442c0102c0006840365024a0482d603211030720320301220125002000720707aa8401c2e980f000380825200c03c3e4410980b90407400c400601d06003121192400c16980d0488804204400c1e20164000e80e03c6034010b0b6513618028004070301610038162a000702180156220300d0700241e20008040d8407028140150028580950040320960a80c0d0599074822000324404000c0c0000100a00460780b080c44c0c0e4a04106090111040204103c0d050340c01200007801100c4a880c074180a8450a12034104001c0e4007452480c04100b49500c8607800007001d8a400300c4050355a00c461502420a03214901c4400c1d0340c060421100c84103803810300b41000550308640c155 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 818304217 1250 818302967 818303009
    0x15090609051f140d060503190c060c080903010207150f0902060a030b0f0301090b0609011a0913090507060513120b0403081003050f01090c270b0f09090f0106 69
    0xc0007a5242035519140e8004800c000240110098543c001d1074141c01d5031115405000c4102500c0e4502c2068000e009083d440d46960708010110000f0035000030070313001c003185803060490b1400c0c0d4507501514554810f202c1c1c8410350383c013030000746020703402005903d164112200c6208211141d89018a803140d20303040751039005813555010b60303680c001d850600281c03a007102c00100700c40d00c44444201d5819482c0003081170810004030707030903400780006465102d4030303a80315140e2039045c03111400341825011042c00350814528200325400d004e00311003540450240c0307080d66030700d1030320140341c1100011600104008240c444031603000c03002800381c1c490400503420907860f41040898080c0001c0e00300b08a00c1c000840002d400b0401000550f0321400300d5911441e404172440c002e0200304c1003100d401030181c10000e03555404610451448003800690050183c0342d07400813009103508894035800c24000010ba902513503405d6444c5108100d400050040346220020907400c4500e80d030030506010103071807584002 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 818305467 1250 818304217 818304229
    0x3010f080d09091107050601090606030506100206130c03060c0206041101181a0712021c09050609120708011a031204061d04090b18060903160b0a11041509060905 71
    0x316290003c3c006441d502d644000c80e1203109005002d0100d00c1003000005c4c800c0483d074888001c03035900d0758080100c0d4481104100300c86442c0308401005a00420101d818012481c0d1280c41461040d02d201c40c03669603e5640c0c0341950a40d28810025800400801090000704000b000d03401c20240780044c1d400d1103050500110a9a0f030107003072400314407001100c83d0034032450101c40c151904500040c0c54040203d000035600c29036100c0368528250110710720400715008a02c1c4006880008000764240301c009007d00c42100350040300c0d200c00d40304455001921200a200703056480d1134081c1c0804c40f41c180390040c07510340390302254030030000ca000b0003041001980c880c0800c07168640403c140d41443d2441800103018220455014021b10340c04000d00080d0055400011940c1011000366440d660b03807584c0c1c0e15100c0c0103c051590030071014020110005081c520480d911003921900010840007039000880385812a82008a00405076100741040e5500b002d5100010012171600701c54690804021a00c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 818306717 1250 818305467 818305469
    0x17100f140603030c150a0f0e070f0b03010605190e0a15140a1e1403010609030b15060a0e180717181e010b1503010f08151b1b0303010f080d09 62
    0xc2c00c0d5078030350040b800c001d9031508502111f0801e40d034288030300b40355224403a03180c00032445009261005801d001400300322000c00e0300d040b06d06540f41e0070708003e07240089420400400c0320f0b01c3c04003c01c00610084641d5138550f0a005084688600d000301e01c03442d1400b8003c1d9841da0070f0549801c90078400c4441d420350242c6203c0c8143c140b40c010b141940910a000c0d5950381850200d0540400088000305195a100a4841c1101d015840d808060748a610144440000401e0a01d810000801900740390074011894405000b070007030310100d4802207542041541170029611b6600182ca401410f6510b02d080040842d0002c1401c6420755544202c10401c0c0d6503101c0b41807003148110540040083d0840e804e5101d601c190310050010314581da034503c01e4107560341c02401058440c2200081c00300d00300d00001548000c6038603120a060300350303d841481031103281429611008424080040001002c401d11407840a030400030300031600e0754104800441101a9a080a00d19610400b8000b2119902c80c0b000c44c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 818307967 1250 818306717 818306743
    0x3010e0a0507140312190e04020a0903020f06040f0306050a140f0721020c1f06050108180c03101406060720120d05070b0109090b0117100f140603030c 66
    0x812080b518007003810f144d5500711903101782d80003003421a6400714440448208510346d42e2002d04419109040000301c4c0280d03014540001d82c450018030040c107002d140c542500c80700070304041c11705540c1c45014001c4034050b04201d40c41c0351520148103410926000c2c01081181c0d4581c004514542f2008010001c03400802200822420048000d030180f03200402c0a11112000402c1d076031200044c0b5034640c0c070084a005100c2c11740c204481c81c1500c003090b104a100341d540c1691124503644030002c494a201e40f07441048050344c0902c007541d0000d0303a030800c418583d160401d000413a007400c00500a24449000074510b81c0540401c00481000075040e848040c40c00c4900d0800b40040700300e1901050380038540d0861486103100e00400b1100c440d80000281518a1107104801000d80e00e4600b40c1c81610249540203000003070920051107002e005661401c0038481540458481040b04c22440c0e00380c0301007905e589101ea50b12a0b0a00c0c404248003a0283e00403000d60046107096140440c051b92303945070b05510 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 818309217 1250 818307967 818307989
    0xb1e04030c020609150a020607110a0305071b12150506091f05100216050f0f01080705070b04110f04091e020d0213270b0c090d0512040503010e0a0507 66
    0x110215564501641d80044c0c004d010903000c081300800d0114a58488030880d405449280c00081807244204480d42c0d018040c0c0f40a003462901684d4255005d03000a1701c102d8107440b0001c1c1c1d504c254010403588000801242900150010711800c1500c05446904441d0052a080c40100720640d101e45103241e400c0b064000071000c0300c183c405840003030301407a504101d03403085100a041100c0d030340c0041c1114140f45850f04c50070301140d5030b508100010804c038880c2604889030700014a850360043c060f0070f034008030070b060141c80c10b001c0d551040044c801c11a0704544058a5400000c154246a0320000c1d00110540c0e00f0405220703251035102c010104401d00002d00c054102c40130045448003860b41941a5014100480e84202c044410b4080e1002c0c10100328203c2d085041e03a00700503200028800c2540d0418107044030f0b504e0390000410783c1e500c5551413030f030800e170318003c0309002800030031609048190b00042240c0f942d040100301800d5500f4400b2004441d8041403e00010850200b400c5013280e94549007 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 818310467 1250 818309217 818309237
    0x31e3c0628091505070f03150504051e010923063006100e090d0f0f1b11040c050f040b1b0304080105061906021507110304120b1e0403 59
    0x111401a01c8031040052001c1440c031070501c10f118942d00114004c16030b90729440304108000104404458805544a02e200b5020f90100180c0c102a4002504020910b070744804881d24803108042c070a50a03807107494200c0c0d072400b0404448181c942629a48110b0700e40b40403103030030720500150480a01841d440440c500e065002c041209510b032015100e08481426180b09280c101240d0304903880324130a00241031241d100040c0380c4100820388424640306500d030b25000e002e200c0002c43d5401142c28208062080d820195003164980820b04c502c01480f0380380843e24100d00c1d90030320094407200340d4000240300083c40042c00050048054a081c1c64840b000700c0d0b142c9842e002c4404294504600e0801c46010025003c01c42c204107410030791240000380c40308200c400c5200905010441107114560041c1c20001010400d248081070050b00461107180016411244202031810750b030099121440b011600307030761882000710821003070f54050103070b44901c040388075803e48000030020001c1000b400c03c112040 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 818311717 1250 818310467 818310541
    0x30b01050c0d1115040b0403121404061506030507090504022109060106021b090703090c080d1709031801080c0c100203010314010902031e3c06 63
    0x1500e055031003103402c5558198507680c000e050550b081106981c0f41c092180e14000c1120011a203500450741305180250076603940d02c0843d0f0290308074101c1c5640780c0e10340c030210304451802c4030b29038000d40c025403000508900407000ccda0010340c0e03103501c59070038141800308110045820031701d0507044030300645004d60f0321751101d00c5440412440c03401c404046540e00f82413280b20840041c00710f0586606800300c0d150804611144403d001c00c81c03600c0c540c0145007000050041344282c01000300c01e403103030b050b1a01182e2102010741c105441120305000040f0b007048000026a00200c040342c0002042c1d001d5031801d0380016101c84030542100d0b0890501031404080b80c207030440704040391a48a40380713003602d01494044840101039442031106542c000303101c10625520040601c42e00c41921707401001082c4c084649140c0a6070344c01c07807220f1000c02e40107404051503600f01202104610001c21040c10040c9082064801c00304509501d403102c0700c3d03020a04104002c445480020085a46101080d0305240c0e070381 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 818312967 1250 818311717 818311727
    0x80d03020f0c0307030e010207080105060a090e1f0f060501050c031e0c010603030203340204180c08010b030601080d021209150d0614120601090b03072106050a0c050901030b01 77
    0x80c10000c42c0e120004910b401c3c154800e0032064040c000740d0030b5400142c0e54030045404d86030300380c0352140e0002c00d8020800561000c0e0380136407007502010069030b40b44501c40b22029100301c80c00c4448050a601c540c03040c40f55404a04c5075202074482400c20504010325210450742d640034801c0901400340070156200140c0c0000f8096031382800c03114000388105034691500035101d4000c060355402c031402c1d10740320814100018080034801030045600392540382c03003034003080b029020740b507402d440c0c40b0040a01c20b00880c040c0c080c800c015000303500010880b46808001d040c5003800c160b110400c65044401c2c8049865404198280320f00c1c1c00655141d21010b060002440705000c0d1203030080c060400151000c01401a40c00c0441202c1d0524295a40040314005002800903400454003040d000000140110300880e400500301410180440b0541c540f500c0c0e401030705540228942912030404015401004802c9c043ca5601800960007131040e854503400180c514090840031606141e10303055408540d920030 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 818314217 1250 818312967 818312977
    0x4150b09070203040906060c05030a0c11042306011b0f02031c02010b010201151203120608030a0c05060a0b0f100201110a030902040b040e07050d0804090204090e0c0307080d03020f 79
    0x108490401d040c0803401a60741c0c0d010f07110340c150003030a101000034014012800305c801960007601440c034011941d44110380c14040034600303c50310303001494015016140e910403d01400c403113007d0700a031040d5841181441803001011503040003248400044804018421890501d600580e0204006290310009003001c1960a4200126209a0141d01056415080f0030000d0b5001c0e0000c00640c20702c4058600407032101e00403540c095108005010020b031150007005079000c04443c000558039250081c090555101e00407000000380791900010604c6018403485401c040110000c20482046501249160404941b1144100c041c81c0c4020030080c000c1d004524070ba50016505d0f56078030840c001c06001805425426801a40391480e144050304240c803d0701c0d0f20243c01d000500a81c2d05e40410020700288054045501c20b50034000024000c141e80040d0019209084000c942d0510500c3c030741d8909200e13404458865484030008004210b0041900d100c9400c00740b81c0580d07903480150a0b44440d01c42c4c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 818315467 1250 818314217 818314219
    0x50405060703030209040c08040b180115080601080714090112020d0f0303200f0405041814030301242a0b1504110a050a0c030c08030a0f050a060e04150b 67
    0x40700010194994010542c0c1d0313004480820410210038401c4405010485004000101c410003164038141c035140c40b104440c00a17000810306542c1080b4103404401ea6034031516007640034070014041c0000c14442940070b0040c0b400d125031050348003000102c0c048810b21a0480516a0f00c20b90425902d40b00070348038001c0e03046030317050040740c180740350080040c1803c1000320101d04801106032803568005c001c440ca0541d00c0c07a100c0341020b00300400c000c0141843c054a0041500408d02c0d0000511203a50042101172042c014645175807403c40303000f40c070080b0b600c030070150f810380440446101600501032a81360000040e0350079110105294035960b058510074050244826082001050000318155880200c41901c007071050800881020354035000d03080001d00072503414080c4110312071284544114060080c98070301590102c0c1c0c1c80f52885a4070a440c0400b080c0e0300d4003010a940c0000703004280d0070a200f00d0003003003c24942015103440040240008110b25103000802c2c041c66800d41080c6030040b4 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 818316717 1250 818315467 818315479
    0x10e1b270f09190b0103020907020312010b042103081306060503010e1c05030106020615061c0504110901050303070b1b12090106050a0506040302240c0a02010207150e060703050405 79
    0x20074880c8208003403000ca644010740c0c070455000700c4102000b101d0358100b07a6484840f4800c141d003507a00f04034801c1e000800c02811072005001c0891002604940e160007400008072050340d0310f080170700c2510f90344490460280350010003429840025801004160700c4400c00d80300c1140c1110619100010704000d6115590660030006a91045503010810302422040c240384842911644141501d00740024882c500250300500c0008150064142c503e0250180040c0181d14252a1810056001204002c1d10400c2c2e40e03035030100410040304940b49001c6410444103d5155072401d0002652031094080081942d1018008116000914090720b100074607046611034440224582c40101e5110450710841107600b040c00018140c103004409000351400030304124070702402c40d020f200740c0c50700800ca040f01c28210883c0c02054030030320a0240c82520208409080c880159000092400d5159000035203c0020340301c15125090b000103960740d80d180e045c0c0d1481d44815183c28185c0e034074002c2c0c1d030019030040c03 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 818317967 1250 818316717 818316721
    0x30a0906150504060f05100507082101030b070305042f030a110a0f14010f0e0301050106022113090e12120f0c030708190e1002040305010e1b27 63
    0x181803401c94605440050310204a20395540d116400004200d00c102500000130740b0b103203851913109030003c010480c06180700b1454650260403088400761040f4620200c00100c00c014010881107001181d002a02d610b0180054186901c0c7da01c5131810386030304000070030b454032410308821030040c1d2440c107001d00c003c3c01da810f01d01c00c600344080508503e0304e02da84078580d94035021a0702101d080c202002d54000807a17607a01c201a8030010b4551400d14030034601401071403201d80300d030b50b982409268040d00003503003d412042c1c3c002800d0031840b000d0442501008170140240004160100203200c1250a0080e001c88c1d0f0902c21100f580c02c0800743e104501c0c8200300002d07a004585541c104890040c0c0d106448100035a031041a005210300099543c100081c0c0c031080841c0c07240800d0501044805000d000005581c040402181c0c42c0c1106041d60b101b9054000c241041889001c0c41201402e14106024000c0000c11045102c4050300c40443d10b44107840c403074024001c41c2d80c03800362a200703980f071321400600703078 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 818319217 1250 818317967 818317991
    0x4080a0c1410081b0c0c0a060f0905010309030e0d03171302090f0a15080106050a09020406051c0b0a060c1a010303090905190c18090c210902060a1d01021908030a0906 73
    0x1b4510881d603140a8221154006480c034401c42d1a4004442103580320120b00e410070004501a082800040d07080044212049481d5610700c84010b648e54801d0f1034201c81d03481810f140001c0e10200414070303c012134804d00c684001d6142e000115501015540303e590140d03a5031404000180504106101c1c00c20358500041408001584850306507201101c41c60815a03448070058181d2080b80140340c00940103100d004101d0603080f4003080001e21750329010440001c00720118020010a611034400030f20205581800c0c0403508402d203040c401510910031081d03040d62009000385141e4410000c45035a18000282107a0020004d07038442200c41909000000c1404030042100c017a40b010100c200300c1582001514003504e10a50445071000c1d150004410346d15010fa84041e80d1105d0000ba055484102210059845000500310043c40d41c548051b0616001c60481d10405000b00c424103549c0081d1446ca0440104035000b40602e03070100040d035030783c0d40700781b8040c0c0a0595814020589810440980d9003 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 818320467 1250 818319217 818319223
    0x121608130f0e01031e020a080d0207090b030d0206011503090203011e0e0c0a120206040911071a0c070204020c0f1203090c010507020f010e0a0b04080a0c1410081b0c 72
    0x1250a0a00420426910b52516044402003031100408003203c041c0c1000024903501d0380b0003500c60004000165543d0b4a4202d141010b42c046485001038014240501c0203054034442e031004543c1c25001804110503e840c0030790b40742d80600903141034069100f1381d01807180c8660000c9019540c060009d1022400d204510f407041d0102c2d80395003500c0f6051142d8080d0310240020080001c500041901c0111441c03e1b80c8207581ca20b150400303036000303038080102290313128090007866014401c0300700144e03076200c203030030000c901c410001910542d0f0303044a0140020f054002c0c0980d2009a0100d40059a0309007846034246001448006007a843c080d8030503086d8072034124005507101b400d800d0107031404085844c00440d0141309150000b03501c041ca10540b407009500c1121407012803907010300200d0748a525011015041e400039440480144d00c400e88810801400000420050410321001400300d000e0340001840c080c0c072380c084001002442e0b00050900b00c040b026000c81c00c00442d8106998000001c211070f1 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 818321717 1250 818320467 818320469
    0x1f08060103030e090f040b0601020a0b0f0402150310060e060405120d0216032418080403110108040b15041d0f07060203041d0a1b03150b0c12160813 65
    0x1012a803290f81d8500e45080100015115000a80e000d5541c0d40d129610382c0702418018000038114491140c800e800258488825400341c05190001141c2d442c280c4100543e131305401194007080744040c41402494106c299214007914803d040151120300701c8030125006005582c41a6401895a5164140380c2004152207020901503420380e01816800c014000380d40b0094031000344440485400c60f2004907400c200c1c0804541840004120120081102c0d0080c00401509582400c0c0010b0100200400c400c05c0c00201071081c2040d081030314003925411010203005008201c1c1c012380122019090b5180c3c1d020502480101c1d45401598040d00e15443d903a50700c03801e28101701d00c2840c0c0c0100c0d01500000940f411651290202c03000308070300d401032003c481030207440e10f0041511840c010740070001d07040c10700b03c1c3ca51642d82e0010740c03400c0d10004140300403101d5019900c0e40c00104034284000700046244054041c01e42807241d69841390b0b000c811342a0404800150034440e000c80c41540307940e05408144 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 818322967 1250 818321717 818321723
    0x305070b01150c08090409050d110d080613090c0810020702030c0411070f050109080d021918060507240b18060a0510200c010207120b0f1f08060103 65
    0x36039980e01e44484010808600c08a400411040300343c0b040080c80203002000b01500140c0007003801c500903956146481d0301500340c4d4010444804084102ca1010400007902ca403080c0b03410f06c0141810300220f000c4100c1c020b20302030381c2c40d140c004041c18401442c0d10240100400b40484071741101c824010002074100c0b00c0220303c2405040c02100e250b144c9405206103007409428018640402d9603900c40a00c8403140048819548940381e40d400b05002c0c0015010403d07a4140140e510801f124901e05a040d41d01d918905100c401055100da540806680d001030b10118185140d4610080c140160070213050b1100300b8030140008640c20300c10806400004e11108143e5003000c501e03034070220540072041d017200d5090704140020010042c0d803900d440c0d15075041c0000e062440f0440e08001d542c3c000c203442400c562506a00000c18502503590400440004244021001100b5001aa2905030341400903000c0d40025072200701003a054071180a807140714846150f002000035980e8600c89854407070902c030039 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 818324217 1250 818322967 818322983
    0x1f0801050114060c120c0f03030103030c03090e04120f09080105040f0201080115080c07060e01050703090209010519141c03120c17070305090c03011409120c12090f040603030507 78
    0x5080c483c2410010754200e04580000303008400864101001c0c0c0786c0041c0e110030254411052008613025060000f0b5000e14000c2d0f071011540049824041e11505903584200d051000304410040840c81141440204c0001807410780c5d00070444140c01c40302841caa030040c0256529100c14441003002e40048030f80154400c0e25011282c1c0c2c1e03110304031790841d0403102d02d40000c1002480040d14420f0980300401c3c28511034600000e0480d162511182110812a02500403a6481103040103528017284030364014101202d1001030009081d50000311404a407243d070405d2143d800907600c0c96510b002c45501c0b075000c0c00c0200342445e140c0341001400b0130300407614030b4012413404441000c0c1d0303842100c1c1003520094044001e0361301e880314501100104001000103c0a0003821200c02c01650207001d100c5514612010816250618410141c10050111401c031503c83c02001306008840c13010415000140390f4408060b04d5001c5100820900f80d4140c611039805843c0c5a4007104154028010b401450301400e15 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 818325467 1250 818324217 818324249
    0x3070602010605150a0203041d090f0123040c03020306040b01030b1003020d12030906020426030a08010303180305030712120e070902070602040b03040305040e090c0a0e1f08010501 79
    0x103a088500d94000e0a40190303550b24040802c0c0c00400040280c040d441c4101d03481c103541d404002c905d02c0710a0450010942c0c482d400c0c4084020100620510010140020042040d102a00600d6010325115518070800e00800140520030f030801206d000350703005402c0e940c007890186061815100240003c4404c91a01c00101e04e042d07503407224040540340d01600a060002e000e855800404a803240c40b201019240c5520b83c0c0020b1319800500001c00401205824550b8002c903045010400e2a05013283c69000b4459400210b50191030181101c0d090305124040c120352641e0308020281c02e0304040e0052200180310070420200400050030086140d6918002e40944070810040c1c401c0e241c41001d03ea44811414001c0101c194028400e22b032040800514040c0e80d5808510250400c9500ba000304501003010050b03034130b100a50301e03801412040601140e804013000110106090700568541c82c131450005044a08440c10003203c16050485010202d5a10030801e4040d040901441c039105901c044 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 818326717 1250 818325467 818325479
    0x22050307121b050d060908130305070510021501050907110607020714030f060f0c04032003010b01050304050a08030c0d05281413051204030807260910030213060c020307 74
    0xc1c00600383e03500200818442c031040e84541019103013800e001d0b104100d042000c0c0c51a464141c02c03442c0103500c114043d0a0651508041101040c3c90b80c11140540d003104180f174200080311003000e070550344103c0d000410740c0c99015040324000710111007480d880c45000c003848540761700054800d04403500079051b2101c06001005158680e0b004039040d1300203500100101e50912860710025a228100401141c10190740c0d0f00c1e001405e01d002c0607245203070b11240089500c02c1c1002e0103080c00d10002800c0142c40c604003995916500d40c072030300001c1e01d40d040100c0820003c2101000701c604007203019406011504001036000450001c2c40d80d03020200b80001c0949003215041d00802d440020b050f01644d03856039407165160341905018000302c40d40d00880c043c800e000c034802d9001d800031b1401458095250b82c00d500d04001c00d41d03551000c081c0c1d80300c600c0e40309007816101031045480151058680750031a2050541c01c3d0068003070020f210b68101c5011001080d40f43d0700528401da220700071400c449100b640c070703e = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 818327967 1250 818326717 818326763
    0x150c0102040f1836110d030309170a020703080904110325030c02101a03060705120907050d081803071206050c070c061b0629040507052205030712 64
    0x1130034004e0080c8202c00180c0e10b425601c0d6080c0031280075184031515131100320001200d107403500f0000c9010a0365a5050300a01140d403882080406010300d840e8035041007840081e42d0740d0a584802232a6640014241542e5229500220442141d2995864a07402c02444600403508242019044000d8400785486214420302030040c0510264015110700621040304101801e178084500030000126054034403651010024544103101c0360361240d450b10102c4400c520b141700e01411001ca5036024000910456032981099000541e000415654503e0114022214400c20545082d40740c0184800015a20303000020b803155107100d0344042006036620064000180240c26003e8040f10540a081c00140e0180010690362002a4030014640c40e295488401381c40d105507200480140f080046c401000600d60b542c25030041c11a41409503185c0f0b020300038030600030424034012100003050f400051092928015010700800b50a481505490344000c007040c06002c0700448540000301544e2400d18200 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 818329217 1250 818327967 818328011
    0x4020706090b0702060f0a0c050403140a1406011d090120090a06090e0402010f0c0602070c0f2304020a0309050102120103210c0609150c0806040e0c150c0102040f18 72
    0x140c2c000710703910b4075847c94020091500d4542c2c007041c050104400f0000c10321104074415112a040d00414264100c1d2a14943c1c2c008541c4001250341c4c8020018440301c08200161100c9242c0c40b04a01d100e80e640c8200e190251001441010344002c16040000154400341d0080103900d109888541183e41d44240842e611070003446020340405210340403c005610940a034124101186013414000d481364584100f2039208040c1225035821200c41040388a100d410040000d10f91415007059003201c845d441d81400b1490240c05209175070000d484041207000398049192039410600840d00d40448035100e01041c00c00380401d41c2c20f00c603414800700440312600368640c804160b640d0303080e0540c10580d5580b40030384040b0705c1c12680320100300341c600028039591240c0501c60680c5e50740ca000c542415800e0000b21103400303428001c15001910203075103940b1624035144002030224042035503082ca004040d030090103950010741141c010340b54001492100c07840480b052160b402410030803030220a0040c1024010 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 818330467 1250 818329217 818329231
    0x211107030b0402010c150501030303110c0c0409051905030310080304081c091805161d0d020a0f06050c15011203050d09050f0f1506010905100e04020706090b070206 72
    0x20090050002426016180d074005206040102ca815160b60f00c001c00102c03003030b42000d0345035600d5004005265041c0210101e400c040004240341c040d0394030125803a0031041103054016900d034110181000004c005072085010900909035510320140703071194a86d07109031182d00500700d9031400426592008000c46048a0000b4010048030011824032510840c030090318500740941d4000001da49014074000880c04d406440c0001410328080b0306d40c81e07100107071034101c07010000107420810f810800303004501405202160b003101d0448040c40001c001240940009195086040c070029046801c0000380503000d1507002900c0300040f50231007031200c964003440391420f91180c160003c030100b4007c01c0103008800300d0110215000b240703a12540d103400d0303059078010a2a40802e600c03a225004c203005c8807644c038680310603002c2f050a00800007420040700e03000b414840c465490406100030b02a0961600c07480000d0419519003010341049001002e4030385041c0c94986072200007911013440880d81c03900c1154 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 818331717 1250 818330467 818330473
    0x102160f15030e07033906030b040b0607030201151520030d1104140a080309040209012d030e031903270b040212030403110402130506072111 62
    0x31501c40080040d039411003001e424103a40d0200948204414010306014500590003907030803034600707807400719151741505c80181030003c580b20481500c101e442e00c10084510074a00420700924442c00500202800030090382c1c001d1000444204054064104a01e90031980500501040c2e41d4000010040c540c44445000100860580000b07044091340c043da0001c2d0050840e818845906880c004585480c1d400040b010707400b203000c009001c081449030850000645e11100c0c403a1070b0801046e170324003074480140e11494001c40c1d4001e4592091144803c03906101c06803104414a002200400c019680b52610000e400c0040030034080000200301c801c203180c108150000901000c2040b402040f642c1c0603600800d0003028440f05c1c00030245004071070540503080e405085c1c10310381f04210824290000c020443e030001e0001700003082a041e6259511401030f203003d03a0741d02d0980b86007402030020360401d9601110124945085c022a525110380d030005c01d104403110304000c004e0a0320341710028001c00c901070f4 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 818332967 1250 818331717 818331719
    0x10061203051611040c0e0a0503030405010503010e06040e0a14100c0e010825050c0c0312030f060310091208061c0f47040b0115090302061303020102160f 67
    0x19600745641660a40074844480f20001824005400c0d038180441450008520903840c0c2114038100d400030b00241401c8008601c0c1c64603190000e82079002c14400c00c002c1050780400910503031544c2d001040445841400e86650001a142500f54110802c0910345180301c1d0310070b404820300d2a40304800188200b9181c1c01e1603d00e1020046911000c000e00181c071605100c40341e4804250f441803040f01b040c049480f607544030380c84041628548280750140c503109034400310901d40b110b114041226046455902c94891035611030022911382142c000b0600c080d6407078018000e0500c400212500c884803410f0340c50741025228041081428081c031286c1140c2d00054400050005107880060510b0b54850b884400700c80c1041811011889015040007108844e0a160001201d4401c1040014000d400800c2c5000f030a0540f603140d5004414011340c4003804242e04109001802403100400940d801032500d6a1002c1402c00f2030a450624881207000d0f2140c115002140c410039082c80c2c0503a540c0403041c14071a = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 818334217 1250 818332967 818332987
    0x2030f0112030c0c060e030c1516030215070e0103050f1b13170a0b0109020c0601060e03030c010606031509290117132d031d0a081006120305 62
    0x8000c1020100e0070310914058010004803507190581c02081d20741c0746d100002e0306810501d0308020a03010b005105090541401c030048803103d0030f441254120408001441c078180c50180d203011030400709c0000300003c000810031400c1d880f11100302001020f98052250303884851034080c16000544820901c03d01c901c0381e11031b0b9404920054a00006518101d42549984d101c00d5099803a00031030241c8280c02c800c000c0070500101101c402d0050180c80e07021450007562440c020303210141802440b0811040c000300d65115603042080e19600441c0074000c01c030311395071139601500908111450210f605148480003c0c1c03d481d42c41030100300c243c194030020440f0b41c0d0442202c9032000d501c40b114140201401d0704030600101000c410301c00c000c3d9013800d06030320b2218101038040821404460010058400f48600510b40300c40088613a26450308290318800608095003510100b5035000c0ea0b04001c082e1000201c2420004a100c03550b1800442000703c2c54503a2803030480400030b00000b0307001c994108074207580 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 818335467 1250 818334217 818334239
    0x318060b06070f1202010c0206012312100b0a050a05030618070e010e04050714011e030b1306140103060b040b0315060c0c120607301407080a02030f01 66
    0x1031000030041450000795540d22000306081d08410f41d8a841135890000d0030030b030248211b2600c1c19003030004001e1907141c040783d0215180c00442c41c0500128013025050291900070f107241404c11528240d07103031030405440c0c00005100351258a071284143c1180000c460808800b00d109a0384050043c20044e80c0704842004010038800440c8110702c1129170000d14860551403c5018011003a140e0382c40b070502d810120300c0e218042d000720700800c07010700c014800d42c0c0e04a071b01d00c1c22140b031018a0780d9000c0c3c0b10000075001000074007401c0703400c20300300e42d54661000c8007540000196400c600c034500b401400840118211007180c0a405580382c4200414885820100c020315480448414103507651010500030a842d5001209a4400c40c1d00030110700f00c080c40c09a40000d03500c18408014201c0740751220004010428510900d60101280c43c04d6509605078001200c40100040748248104c04855600b0702c164103007100c00800144503040842d14011550003101c3c024903511030050404c0e401c0000c5640 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 818336717 1250 818335467 818335481
    0x80402280b09030c0402070b0f010e150904020301141611060603190602041203030608010e0a0201020c01110106030b010609030b0a0b100f05070b0a0f0f0b090a20040f060f031806 78
    0x1e454410640c120191740d07114002401c1603031064420b03540606007007002c05402103047c1c21400d00c2c41b101c60300708020000700801c400040c0e01c0840e22030b0907540351400070a0040c0b02008040c0882e68001c410071018070005d40c1004055805d554403040300c041185001500d40f507040e24220340c95000b1f060034100401d40e000e0700341415802410010710b8681c0c0d0b13800b090f0703205150b02021004039450714400c000682c000c0c400d800019480501034000b030f11861b40001d442e114a10700f128140445106820a9401d096000b50045c5900c40a614200e50712047c000c1c00c161070a100866400344444005481c074101d0f80100c05480d5005810f100d1181c413045e5003940d401c5c4400120030b042180900001c0040b54491210324007484400000055880e21988000c007901c2001a401c801c003410222140416102d81080992000300420005030480d040c00c480c10148100e10400070900b100440c0c00702d4101403e40020301111096250485840c9120000364240c40f0700030402c0d41c1c0411415a1100402c101d500518 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 818337967 1250 818336717 818336719
    0x604020d14100501090b1e1003020c0304090e030306100c03020307121101090c0503010e071a1303080d0b1903020102060f220305071a060a090b1302040303080402280b09 74
    0x202c1c00c02111510707208aa900b603000d01001525034009606a047c6200d50f00c00700f5240425482c0000c4086000c1303013010b1001c00040f006c1590000c2c40f208103806c1481654050100e8807424818103071b0b40c0084030b80d00c2c1c1094410500c9800204102c0310914010030f810401160700d074000e141461200e880c0c01d01c100000300729080900000c00040910820300784940c05040d0f108612101c3c465041c081814212191405440329981c40341c0c105000040562986a03682440b5141c869030b2403002d03005028039406140d1000b13050a03c0800c440d0b222860130741000ba141d038000c1c0d42c500c40c400d040100314043c84100d444080c0c00342c0c20400c0800d12100c501c40046500240c00b6100c0007005d51140c052064a41030000140c00060022030498100641d241d40d00780100301ea10013401c458208a0700160403807581748508845c00d6070302c00203813401307484120f411040354240032011920b460352400d02904450085400301e10403042c28401007a4800c07000301c1e203540304980c040d06203040c078142503580360141d000c88082 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 818339217 1250 818337967 818337973
    0x30905030d060b070c0f0501020c040f09020301050c07050f01090807030305070e030d02031206030115291b010b04052505070c15320d3b0604020d14 65
    0x1d0740d076a2601c2d0140030300400d001c0211968904c41400c0406680206030491030000b0240e00c4c007007040d07a0740081c000300310340011100000e0307808010341020000c0c03000000003034055092000700060050740d00050b04800d409071064910306408030300103500721402c991006121400c107111042c0400c2c400d6101a9204040303040121054001800103894406a100c942c80143c0c8002640d000000c1141e1819812040a600a00c200300038406681c01d60103050040c44000c4c4000c0c0e540c1c1c4031125411010b4000e240500b200c4594a1600c481c958a183c00428a169269800d0111a100c03a042600c50680319042034101c40242d00c42406c1c040c00d04012855a110411506010b601c1c0890b0101001c14014104140300d003015208444015210840b4080c0c075142a10401064145503203004094490800c01018200c1d81d550191452200030700020424ce4200312000b0400c0c0000111a01c0c03400e200503100403446010340404802c40c0d502c10b02250025001030b5540d41c403030005410000f40324411500217040d = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 818340467 1250 818339217 818339227
    0x12030f03021c050c1305190e0712110d060b1303021c35030709330201051009200c030909090a02090106081614221d04020102070603090503 61
    0x50b0801c1e240c058a0072500c01c500003d18440308200c40d070341079000348001da903d42900748001d034940310f0703000080c40380840300f280c03c1000423075642c41400c103a8100074400d001041406400c2c04428101d8101441c00b89000346405808124039022000b9221101402c21002c05400d046a00340801400f10040d0030301669a04200341c000100400d4001502030300c0d10558071054281110706e0300c0800c41084070082e103400204184400c251f4015400e000b03450324007c0000c5115005401101e01540508500140600202440c04419419007086025150205481c4030068440ea4041e00f01c80503040e99645e180348641105440e20052006082c00c05a01c50503641442040e0001c5103003c1000c41d0300c21480d4100c1d03002c0100710f10780f884c8010301400c01450309034450300d810680c03424400b03d00c003180f0050000c0503280710301c40040202210740c2d81c080410942c0da48400c49141c1086840540184419114000c0c1d891014090700801c80d032103107030168000c2100c0341c03a141c000e40c02810710ba902a00c0c50b00003040 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 818341717 1250 818340467 818340517
    0x2060d020a050d06060c05191109010305030d060f060e12030706020c30220f06120506030d05120a09170301060e030d0816020f06130c12030f0302 64
    0x102400340c081494480b107982d1900e1105000403112030780c10807414064040d03100c8000c100c0000c0c4100002c05825510010051703641440c1d0200e00c410509954440090070002c010031001002a1030100003528041c810b01d80ca902e090300308002d60340145e00000c0c94030b0f06d10100c2c40c0344c40700d00d240000314500140e900d09907072a215034090b03a0003081410b140da84040101441480f243c41c1014401c111606030411881d83c0c100b01403450b2140110038440c444180d04410f45e9004000707840c00040481c80048207031300359202c801a01080c0c0f0f020606003a01e1510000916500307020030038204101d42541d50302e185c0858400401c0000c1c4004c1c116428441d981e4002e200040d03294450a003555202c161110b80300e40c94400010710380070100d810b060203604015828036480e034012a016030000380207103003608100c114040c02c03071820103190304091091240a0502c141806c08105840d24240104510080c0b00c0e15400c02407003080d0b8203c00100050341d81716031420043d20a42c081d020742c00380710808410b0004692 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 818342967 1250 818341717 818341721
    0x3020d0209130c080f04080d0207080928140a1a07140c10030e1f020702030319090f08071203031b171b0409090317070e040f0612060902060d 62
    0x140707500e42c496a91401816a1600f08001951283c9a80c400e41454070b0956100305290003107008030489260046070100401242805440201c1800b5048201150003058504001c44140740130401b441e8642c4004501041009030390403401c00080c20061b0030500c1c10080c040079494032145003561000a200c0303600010f040007d45c0c105012400300030310200c401e18040064144281c4070f4082454940070000010600101d0000340310010340b14801c401c0e50480c410320000c1d00c80c00314004c1d80f5000000e28060741d004004c0300d40044070950f44e00e00780d82e552201c07103204030f5a92900810a1a0340150300c00c1065803091b0300034070b204078400e14000c00c2c0207022002c0c84854035080c2e034464004c540f80c5804040044120a126644030303e9860084095000024103018503200e2401514601e50300c401c0004113142c06810251040d5a04800c02003040c40d04601c010a2100c014445030302c10b9003043d10741c1c005400940281c070b0944610300403021480c03819981d00d400a112444081760000c1050100c03142003403282c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 818344217 1250 818342967 818342989
    0x604110d080d0c020d09050d0b040521030108010c17010e0c04030c0e0a1104050d02061b060c03090c01020c010e100903050607030b011e080f0a020403050316060e0f0c0103020d0209 79
    0x2e002d001c2140042400040e0a24a00e44d40000400a4100e030410007076903484801d0541d241c11030402482500c450408904004100c2c54940340c0c0000d40580d680e03299024001181212a2040204003503803100d141100d0481400b1804a02c2025100041c8400c2c85802e405980150041607403030301e42076aa41c1c0c0c205869003264803d8003950050410400118002d025170495481c90b2041140381c036040900050401801540190040e0b00c04540d418800101c2c803031194100c1000b00440d08140340c500c44400c026403040700c0c418802e0055181c1c01045500014404280c1c49050715401f4004000d6401d0104141054062800b080740c500c10000110b4002c0c080381d4040c00540d90089244458035001502040c280351a030690f00d010640a07070402e50b400441e44c1c0d04000c03601018521b548481c5840c10190196400261450000050901d22064460481c203903813840b038442406140b100b1081d00e5160b8512000c00e011540190003843c20039882603008145906070319034018100300300880030030300d02804 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 818345323 1106 818344217 818344237
    0x80a030e100f0c020d0c0203070501030504020d2312040312081003082b050f0f180a08040302010314100302010507150c080402130902030604110d08 65
    0x3003844009110514600d080c481024000305030002401d14600e1400540314003c21180d40d68000c841c10941550024041c220315480c0030010f401909004104031717844078804542c40b00080d5601146920342d442800580c90310a142c500d92454005028030950010009000800009540b2244034008442503d41405551120302c601071418440d60001800514085080100c04001c80302c1d00b420340614540c0341100700100614401200c1013510108944201c51000501c40344141d4112500107104030b5200030084a200e4005060540c801c3c03046484820000c1c0400666a150040c58805900809000b0f11030a0946a80241240e01c2c40004c1c141302d0040780600c18018500d08182a4000940c1c040c4a4408612002003101034200c4040748120344020300307a110850503200300398649034098005c20b5140ca0315100e2494601080b44002d601610707141044c000511241d024000c4019 = true := by decide +kernel

theorem cover : BRFrame.Cov 818165467 818345323 := by
  have h0 := BRFrame.cov_init 818165467
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818165467 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818165467 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818165467 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818165467 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818165467 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818165467 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818165467 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818165467 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818165467 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818165467 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818165467 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818165467 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818165467 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818165467 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818165467 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818165467 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818165467 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818165467 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818165467 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818165467 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818165467 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818165467 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818165467 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818165467 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818165467 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818165467 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818165467 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818165467 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818165467 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818165467 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818165467 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818165467 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818165467 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818165467 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818165467 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818165467 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818165467 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818165467 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818165467 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818165467 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818165467 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818165467 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818165467 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818165467 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818165467 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818165467 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818165467 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818165467 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818165467 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818165467 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818165467 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818165467 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818165467 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818165467 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818165467 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818165467 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818165467 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818165467 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818165467 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818165467 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818165467 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818165467 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818165467 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818165467 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818165467 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818165467 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818165467 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818165467 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818165467 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818165467 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818165467 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818165467 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818165467 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818165467 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818165467 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818165467 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818165467 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818165467 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818165467 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818165467 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818165467 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818165467 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818165467 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818165467 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818165467 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818165467 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818165467 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818165467 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818165467 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818165467 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818165467 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818165467 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818165467 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818165467 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818165467 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818165467 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818165467 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818165467 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818165467 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818165467 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818165467 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818165467 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818165467 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818165467 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818165467 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818165467 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818165467 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818165467 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818165467 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818165467 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818165467 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818165467 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818165467 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818165467 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818165467 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818165467 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818165467 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818165467 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818165467 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818165467 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818165467 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818165467 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818165467 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818165467 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818165467 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818165467 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818165467 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818165467 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818165467 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818165467 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818165467 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818165467 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818165467 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818165467 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818165467 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818165467 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818165467 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818165467 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818165467 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818165467 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818165467 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818165467 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818165467 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818165467 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 818165467 ≤ n) (h2 : n < 818345323) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
