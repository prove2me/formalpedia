-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5370
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:38:49.349085+00:00
-- url     : https://prove2.me/submissions/96065741-8d39-4e11-a01b-26bf1f6e9dc2

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 965647482 ≤ n < 965827338 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 965648732 1250 965647482 965647511
    0x1f060905090f1905150a02090d150507020a050c150906130f090606052d0a0305010915050105070308090712260f120a0f05010f060e0414130204 63
    0x800d9a0000181c1c21035024203010b410100065914200b03500e82c04520301d1035546590b0384a400c2198a0480001050046001d8420700d8041d11441c3c5001081c2002041c41450042e40540104c80800c00081c100030005943c0740c000302e901d5003044d82200203040c00011040422031040201141d001003601e0500180d00551500c4010701010040d0780c04072007100d4100050a012018140d20180043e41841c1c0d00b4003c03240e20006441d100d0040342d002d111203a10901c0848083c03280c945800d2460b00c000300f031a02005a050f009181224100c40d030822409108808a02c140329080c000d031401305a042104030300007480790341d00f50f900c0303d68001514102500c40c0c004000303564002d40155081003401440004507613040013085150903443da4a42d1504040103844025400b40460000802c00301e5000a08003a12b550003540b01c101810008200542c0c407180b00900080103405030703400144481c0e20541007030078188501d01214640c01d42d43c458503940e07020310913514074080d40120380094654858203400300 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 965649982 1250 965648732 965648741
    0x3060a08120403200a0b07020a05090c0d0b1e120a0503070807151a0118030b04300203040312051603050901110c0f0105130806070503071409031f0609 66
    0x403103004010358462444c1440954002114802208200d031138442c9040b95494281000445d0150300e55603444001b64000200c1c20a40ca510480d0000309141c00c01001142c000018090041d940c842080400585030a1001c0b80315500903900c400d070405840d1840f5071510044a44205030340008a0742e0701d0350f0b16550b0b181141c00201c000c98445038080303111030410405131401c03c18030a441000704409000c00048003821030451f28505e05100001000c5041e071403008007542c01450300700e98440f03d14186071500012a48010b0b0101d003e04101e120044000b8a07a4400600c48010356401103080909645518040543c005801401d01408003ca4840d0740121420910382501940b20345454094180002d009240c10b900c01e00700070b400501103010945d030b4190002c0742d13a400a29210791250001c400e022240c039540c2d0440781c40ca2040318104001c0c107a0100046124a5880d601c4910001d0314810600050107500705595042c0c00c640c004084009410b1072403004409000d0010906960b0340f0f0703224041380c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 965651232 1250 965649982 965650003
    0xe0a050703152d15260105060d0f02060f040909150501060f05070602030601020c061204030e0a0e06011101020d0c0905031507090603050604020d1407120510030803060a08 75
    0x44501142c07500340e07810b00d20403841402c1400d0040007410700d4040c05402005183c9018a5265030b03a00380c034130144207881e034014018043e580b40c41000e085201e043c0c04410002103400f5401e560a01c070000700c00742040d101e0b0740013490f445a8101035807881c5a0810072241c000b030740f00a040c0b070b50900c40059580954080c6e40d415034040d402d5900c80f421500401000c0c1c880503000f802c24400c21003011909181d20508880440380c00002c0140c698840c0030040341040745018100d41e0180c00070561a1080200d00c00f518022482629070004506058050000d442098451702d01c2200400c40080e0341d9501072000200d10542c03ca0005261268410002c000c4a040c01589800203072020f401b400709003030812800c1c030440d0554407001480d01d05070000070031014960007000101901c2d107004c03441d130361038a405885030780f5403804050141c80701c4101448003a401c201d844c0350005800044d110240e00c56072044900903503103079440f007280300d08545800840b80e002070030040c1c10090868000840e0003080c88460040c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 965652482 1250 965651232 965651243
    0xa0b060f2803050f060105161104090b011e0e0c12100915090e030c190812040803161d010e0a0807080a050d030b0a050907170c040f0915090e0a050703 66
    0x603070604220800e44d880c80181080d05007e400c20aa0b06165140300100f540c01c0d5010403034045c28012003021401404005070020510707a420b0b070001c03985074107000740185034414400c000c000240e074600f04800086816036103481003440403c40b0045035806c04414030761050344a45500c200e60b5a5a200700700311160703407110350980c487c0c80005021022150107440d4203015148021420811110030a60300c41c807008c0040303401e00000072000710801c03212005455041505500d0320b0b00c146094200364203103500c111081d0104121400300c101d646400744180c25243c82504da003000041c0c4841005407050398201c3c3c6856071224404000064a06c01001104007804030304021703216500741450284d190402800400003854141a0f51258135211006801d007181d800311100034040d1502c038000d0321142e44001d48580ca500c200000c1221700c803940c10082c021101a58540402c10350355000f13440441c4c021031042030230740384a0300003005822141e4021190700e1002e80d0640742d10702e80303e0b40c5447c40c01c1250380c0120341 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 965653732 1250 965652482 965652491
    0xf130303020f191a0402030a050a11120f070603050c130b09150705030306012307050c12120d11093601120204090602040801230a0b060f2803 62
    0x2241c000520941c8505010181d42200c15001683c0f041307400401c54000b40b0207608240c000900351368042201608140d00304c2d041d600090b404d81840329404074800c41c01c501541590480b100d1048000810344000d800c0d0030058a944c60410104070007828014000158156062041d2000c5507440040f00000702024007000d86d40c2c0290030203000d080041210250141d1400f84000c101291001c400c030717940020240790491000a4207c13525a0f0120020802c94031f00102082807000c02400050a0004035002c4480304280d02d0341c1c201c019507601d28403032080010201030003450400385007a00990310300d254003440913080000080204458040400c05003600c002810b2a006100da108090561050320100320302a040d81462550079001404040003400360340e0b03c6442e0f5051000b5a4140c074040d00d8403c0083c054450242c80ba120042d041c0c004840310141800301084001341648240d46c94030307070068a0a420403072040b0100400d80c21103004020314408810008043c070340401080c201c0650240c50006 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 965654982 1250 965653732 965653753
    0x31b080c10210e0c010809070e191a03120f04030b040c0302030d170109140705090a05060406050903011b0c0b04140102030f04051515060c010f0501090e0f0c0a05060f13030302 77
    0x1480c180c4035010031340c1032084190500212040203c0d0340001c0d600d110300001411303100d04d00a51103a004002065060700c0c90001040d4908903013400c024604401201240d03c0030600b4500b4400ca88510034902040c0081000100001058000000d50280c005d401051099a5a07008a800c08090341d5036200020031440860750540324003845d40303014168641041200c60303202e149180e188400a0150310512101003402c00103a9a202c060314041c00000d007003291115076800c03000d081a004100164869400c2c402d55180e880302e00c09000c0389030700540c5e6501500101c1900c40c656082c7c0054000e881e5034982c1411401c1100f001d000130340c020030800e0f0000190380707010304201e400c01c1603400e10440c0d803608a50510105100c9400344140300c0c41c0031100c403603030345000440c81d500400700d402d0b1100d9a282440c0000070304e582035031300a00452000b081a0f94402ea400e642d45510f1b4001441c0881c0d02a1024500348040e007440340c0900304503908003101c039103020040d85811400d0ba10b0355104800683c0001c1010 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 965656232 1250 965654982 965655011
    0x3010f0903091a030105010c0312090609050c1305220f0c0305061506120a020c01020403020d110109080303160806010e0d0b061003020f16030302040e0f01031b080c1021 74
    0x42059410343c0e810790443d410000020301076101d00d00060200030415045891507c0c0381e511070b404803507100c5410031440f18075161190b1101c2c1c0104030345110308031501c0854980b08003070252521840d0b001600c0e482c030005907038400c10782c10320840041e1a9000d4030242c500c0058140c000385c50145020b18010050351502c3c9451480086409034654042c030401d0040040a03d03200f2801904054900c0000d6141d5901e8128940240102d9001a510080c245610030038040b04103010740314400281d0b03450803084d0715000e40c280d892105440130710f00c80420b600141500b074840d81c4c049401c820145002c4101e03490100003e03c48800b4810250364541c8520280800351a018080c01a401c12a040079800d00020805445003400342d07545508046c0394038002c01c41010700c40d50442d00503004416914203181000122001980e0302400204da05030350059502c55820b5042c06004200d0321084020100c0c0c4c1031420520181c00308011591003407050758042402240c2d02c5078040c001202c6101c00001d026200304021 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 965657482 1250 965656232 965656259
    0xa020f1b071202060313141204180903080a090f15020a0f0e010903020d0501060b310f061b0c09020903060112020907050c12210601181403010f090309 66
    0x70182c209203101108005072658410359902190881500190792502d090205140d44240112801400780c0e074a2044c200240d4009841a9070b290505000c83c501090b85e200d0485007020b00280203d075111001031100c1c00f0300e8001c24015441001420100c0380c140d0f0354003022245800010401640125905405907400441100141290700e01212200d803407100217030040c00c482c04081d008044030130304c04050110941155004048500041d0b558404480c014188002c030a01200b00700e0b41740580000006807804201c40c02d40b803c4292800c0901d187c100107039210080b4110001100100c400b545000ca41401c441c4002000c9003032000d07030384100d808200350505a050b040800c25107040d0701d0000c00360b00d42d03a8105a100c200b40c104280e44840e03414040e85003407004503d4054012001404849150800290f500c0241c1008813a032040d07100d130340c01500d052035540e15040c40880701640030426200f4140c44819040d0b805400060700244516154003600d111901c1503000c100c0d07603501006440042e051 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 965658732 1250 965657482 965657489
    0xe040204061106131e03050705030316080109090c05061b0709021e1908040c0f14042304020f0103140c03060f060703120b1c0605070207060203071502030a020f1b07 72
    0x810b41642081307030b41d0703c48a20760a801c80c01c60842541080741c00300b43c0a40126001d06400c1000c480d00c1e89401c1401d000700c001c4640c0d4140001c2c0f00600001303544842d83c000c42e801158482000f1003003c0c102000e05c00660488026401540f60b007842c03c078407005e0244840703400f03402f005a001d03a6421f80c04143c0041400344d4018070f0501c140400c00a401240781003c40c547c070804074500800e940d1114100221142c0300ca03084416030a07840c4000085000752083e001e03156810517102400041841c0c440d401074a48400342c0320f48608240000038005103010740d00501c410307030141400201c1801c102c00c00f2150807404c5840c0040c0e01d100000303001030741c90a00c404403a0348108903a042c0c60103840742c1d0010200072040c202003980d241c8074400000d01d030352102c80c2520080d42c40c0c8440071302c64002d4200200a0882590300c030025020703001c0041001b03072000c001c40741e4040e004100d000c010b81c5140e48501c02544018030050000307038213200300c0c2c0301f003400140200600c168403200e10500c602d03031060130b5081208551 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 965659982 1250 965658732 965658751
    0x2205061c03020a021c0b0106020f06070801080d12060f06051c020307090e040c0506190315050f0108090f030403030c03080127020c011d0d0305090f070b0a0e040204061106 75
    0x128440001c2d6000604110950f8107845000400800c00c0f200759011105c0d201c01084150300e0000480c0041d4005000156115800c2c06c4a81ca0744078075805644408080c041d086e80c075004845007a641500038207540c02c140c140e042000072501da030341c44408604c040350b4018200083c4c0c0050700390702822400d9031400980d20815411451424807190240c00b1070902e118010f900c00f03102c000541030000251011000740000342c041c980da200c1010240800700301000000d8003103441e0a10901d14000880340710816104090804e110081400c40150f44a4600034801031a034482ca0b00c0f03001c454031041c405000210301c40d48540b9135110452401401005c0c5c142c008426565044e042c50504005030044980c1c502884000140d403060025015809041d8154481c51919800300201e9003c1000044541d032122040e0382c2040252035420059443d40711501c080b8019500010f014811800014020800203840c0d0800c91041c0850101003001c1c0d130415441040848d01c00440000641400d10504d6070042864 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 965661232 1250 965659982 965660029
    0x1706010b0408070e07020a05070e0105040f090b0c0711031b090c1201031e05070b0c0d0201110a05210103080403060506061303120c1e020a080607020d0e220506 70
    0x2c244607070b41d1502845058021000000410801402400400c0f001900401a18001522046100300e001c001784103d034041c901c2d201c0002980c00042c4644030300e065011507030b19141d40325181c81c207442e900403030404d6902008240540e81580d6042110340c003c0948403081b1264450004108402e40c80001d14140c80c0e89000c0000c0c1401c541050029030549034419140c4081c2910b06044612185030204001e220b4070030701c0001318180070303240041e1041c2c1c5150030032940104095281242680c00b921a60440010144640c2103010701410290105140d1469030405442c07845a403004026801e90045e80c01100004041c0306100c0c0038002d8551110301920302c20b00e0035030101c49500c10410305100103081440d14150000c038040c40b402d1045002504605040301f00803140703003a540c6152003810120721548045c400051600404030b8010b22980154003e0300039055504020798580e409901aaa442910100440404a11500ea113012088031260000f02854500c0500802290318001004c582c0b000 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 965662482 1250 965661232 965661239
    0x1050a09061b0816050c0f0105010305071e050405150d060b0102101b08100f17010e0d140f1b01050604060b09281203110d03180f0218011706010b04 65
    0x100f5155006522941e01400541c0c0281080303072580100804c103038131402441c7c1c04c40350360001504218140c1e1f0080c0c049d1161140d5607070b014020782001012000c22110003041c1000149000e0340030b6035001e402c03108000341080360b40f40028200040048200c7e04141c2e20001d5810035641000034034421074409104102c0b8141c116800301b003500850807100c0410000d1170000d0310381c1305400507104c0180501035403450000d4660a80300ca1925482403441100c2d8a0041c40c9214010f002600780980803054480c1156500d555003501c0c6940d100d0460983c3e69601044400c5110802c01c9540010701009000051942081d80802040c0c90070740d4800c052204050011200b82d60303e0302d00354070f140d0b0f41456905401000411001d4020764945e070140c5103105907007166006164201e680a818034001c0c1c2c058825000062405400303c41600007402903e100401c40c0d1b4000078040111030310900e000030406455524905050220300400340c000981160950103410100181004100d0141401600007403c027400e = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 965663732 1250 965662482 965662487
    0x81605030a020d0608061317040b19020c1e090a11030c132607150912020f0d05070f08011b0f050f0a050301140f010804200301050a09061b 61
    0x141c0503102079940025105a04905580180000c1c0304940a8803001e140c00a100c09140140f58401c0c2d91810164140403012001042200c0603140c1c42202c05081142d90300c0901c00030484c1d440e1543c04c1d403054400b90300305940d8000885140556403000307010020518014800405005800d80612a0920320007000d0000c4050507a0380c0180188802d0761100d900d60110342036011691700004000c1c505400c2d58245080507600c0c10103244402040b80c1d60650703920001e0040354826103002e0000b8205002c14000160b0148403a60007500045c40482824101c1c0c00150300c0300100d00d0304407120f90141d801040380c01d14000b6550010712510000300003490103a403005e2409500c004284040000d180c440d00c103040e00881c1520703880b84000100d5511607900078070180c840e50084c06410f900324803e08001c0101d1500e6001c0501c0b09c4e0044c1c4d200e103651b881d660351b140c2c0e40104400c070322000c2c2c0084464034101a1400d1003803900c15414a4004121007030242044000c0780e44040d40356244015100c00d480c0d043c0e4 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 965664982 1250 965663732 965663737
    0x11030a0c05060c01021605030d140108150a0e01020d15080705090606090102120a030c020c0a2301020c10080f060a03020a03110f04020403030804050c030d120b0402070606030c06081605 81
    0x10401d861140d510f031602c1d072a9034024886c0c14800400200c20321800c5c001c0c86000009031140c4181c00c0d00c00c01016201d41103014082209208262182c2d000e000b90001000c1c1036400240c02c180e4403400402c01840240e119401c0e42c0102000c402044e9441790340c12040c02004109000900c1c0c0f19019110b07031800c04003c580c2e0140001c10701d81c001d81d40052083c0c00b6134802c01181c5840c0d0340342c07540142c8034161004003d020303050104c11035005216102c0001c2c040e00c0c055100c41c4c06c0310001d41c884140030b1440d00300c81d070940303449d107100a042d07009128040705680c41d00c24001d0250b080c166101c010910707200d40c1c81e43c0c403840081e09060046407004414001a20740013044c00c152500003c8259103032803031138006104240c1e6502110b4105001242c00010550400000c600652245056035103107030100c000e040d0381c0d0b1000325242c00002e80c201c4280c91800712503449440e01c100c0140c0007514000407519a0302c15544550300840e03541042034030800606501c1141c07a03030040950006080046010340000307090b0b0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 965666232 1250 965664982 965664989
    0x90e0a3c1101301e0203010e01090c050f090d0203120c03070c080a08090909010915050411090f07031509020a050c0f010b06271002071a0310152a11030a0c 68
    0x5070380d1400d601c0c10240030812010300030a561368055580f076865046400580394203200314661203003405080d00075140070b80d080c0c418039035849806505003000b51082041c1c40c03a0b25141a81c05002d02b100041040c00c00f40000c002c80c0003408003d40d9608410b2410219411a82d404201103800185810340090f80040c102c07500c09008481310341503511292030050040403005801801002d8080d00300c00c401d92260841c521031402000004505018503051005020342250054403400140001aa40d81c0c0070740d104184403884400c1e4a00040d45607004242240d00490360500840c2c40866041040a402c1001c1c2c41c05e165058001d00c0040d03c02c2d8086245070007014004240b400a10351440040e448081102928180c01010b141081c2ca141501035141c2466002d030b8900c94214185898500c00c2e1141101d00900401a0000c0401e14043c0d071201c00002c44030b004400c101000012a40484c9221510301004807200d050702e8a241e42031038500e060003040740c9010700a401c4800042d02203840c150241045 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 965667482 1250 965666232 965666327
    0x307030f02100203040c0f140d02060d0608010e070302031e06191b170705091503060d0b01140a06030903082e0e01090e0a3c1101 57
    0xc0d50018101a07007000300a482510030b052000c0104000d0000c081e502c141190300b034000748241c141d121501070f0b0040811043c1d03141c0050120b00044011309007940101803440d45c02c00d0000350252502c1d80f05095800d158a070b80c445030b100f0b05061003035140c00d004001e19649403001810854082140b0613480701d80080035418801c1c4001404600e06070b950300003010012049075103022400c914817000d0208403081c5a1401c222141c640020501402502142d43c00310008040200e03c004e100c05841995100425503504580010310000003c0c100b200303951701030000d01900204000c611001e0000c00417030341d44904209070070443c00c080840d4000c110036070003540c005144010080d91500103005015000e949810b603d1500d00000390304143c040c401b90603121708030001d101c003045800406a40340c04882c401307040b16600d000b0230906102e41e07030051881303c4141042c8440c44210014500002c41e1040c60549050100e9885a802d560384281601c40107600f482e5110b0300602081642c503068008110700035413 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 965668732 1250 965667482 965667497
    0x41d0609090a062301120309050f030c06070204060e04050a061413122c0f0646120b010c050c0d14060a20070b040326040506180f030703 60
    0x80218100d1050070155105130703840302895944251000c0991203801042c2c000641140000c50940f6107080c2e0241c0010009009108204000013007100b6980221022644155a0b6400080445082c203000c1d1080b40103501034411070025040480c155068010a43c10910b0001d0400c240481c02d9101035120341e42011b123245403420401344c01e45100c2d9080c0241d030083c0d1414510444100840402c0300d0ec0b4507402c3c0c1d02d449490406500340f0030039009809000010080503520040101501c080d990a108403440c20311144100c02a580392102c0e0a40b0140350029413070810340c0c00d034180c00c1e00031038103140d0080c070380795000003016183c40e91036102600b0030310b02c91821040d03290700b48181580e0090343e150003181a80c0341070403d181d100c802400a80080071a0880e000c65002c960312403001600c40241c2c1004c100c007110b50340c540d421036954000c181001d0400404002d0310182c5589511020322803440743d0700410081c01c0154410a11211002013440180e00c0b0055200c040382c0040140c03200315505040061 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 965669982 1250 965668732 965668751
    0xb09011101150e09010e01051503071d0a0c200d0305060108040f0809150d0603110a0609060c140f0a0606080f031605031e09100f020307030f14041d0609090a06 70
    0x4e02400c0b102071b104850350700309024462072030086040c100c0d241e802201100c0d0711a903101801c207440441140b0b410340e00c100000c0040c5c3c07600c007950000000b020b503501d00440000d03000000d441500b400c03404e05060941c00307283c40c1c4a425803d0f10600c1d8103c0c0d002d00b0b200c00d02e450141c1e508540d6010340000142451004516072103142c031050f9072098030104522006459482c401102170003444548410348000a0701e0404000c941400440381040e2150b55a41200030307070404000fa00e14118680003210241c8c003060702c1407528072091150a000401c104042c11080d0180d050a000352107031504120701d0f40e0080f0700000112800042152812025408984003141e01800c0ca24150301074079200b4101d03044542000b4031a2008540102a0140304940e0031035012040c001c1141c10700d4a5050340750140e03000300240c0740440d00503800400305030703241c0c84c201c41c0303501c0c03560744050480c4c11a034444c4100c078403000640d07802c142140c84000d40c000c00c1540c0e03061700307450071800c1c50359a46403941028045954989202 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 965671232 1250 965669982 965670001
    0x100902030a021311070f02040605010323090307060e0615041a0405041b0b03011503020909070e220b01030e0604050c12010e0d050a0201231b130b09011101150e 70
    0x6100c4814121968803048242401d1621b03500c1703664100d104618112010a1540c000d224440b0b001c030b541039141c0e090120b4400c9410054074060a01301c44d81c4010302150001031218001c18418459190140510307003403840c1ca8a41c1d090003122034500c85d130300f808084566505140a000c3e1204012200882c85880303500701501c10342c2c8401c18801d50041c19a0b40030544803030480080d4100c0d107440304c42030304008241c90218100d00030038608a034020309110128036005c0c441d0301e8800185400030140e00100c145800c45c0a0116a2903850005050f141e006045440d0382622450b4000011180a41401d02d000d0790764507103034040501018440c183d40e5840b90311028003548a114410841d10444020444282024240380c110b84010801582080101c100104090707152441e01040f0003000c103920b0316140001c8a038030030800703c00078104105100300244003010b8900e0b080207045131801c603560b5043c6c1d0303c00103160740c04001d502c1490340c0c181040e1036080000d542600c4200c80048200350319a854640c400d = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 965672482 1250 965671232 965671241
    0x60a1101020d0f0507084302070509010b0c0309060d0f06141002010911060f040b070515061e09060609190e09061005060d06090f0e0705030d0210090f0b0703020c100902030a0213 78
    0x3644030b11a501e407c102d820303038001900c0d9003072700c07000c0320b012409a0340c444410300588100c840006041d0428010441e003401d01c4070180404414a4401103080414920144100e40c1990722001070000044038261050038242c7c01c11200d815070b84000d00c0b4219040d00d5120080000451440c00f03000c00090001e1040c0c03182090310060904000b049030f9400c40b5082450f5540003c00d940c10600c220500420514a4800c01d03422000b50000010440d100640080000792900144940d8201404010101141c2d407149110401d01480150120450381081040d40620100925480b130b56442542070000000707001004004960045801da680c400044084030040c155079480440c481c1d092400138103600003079410420304080f952b0b0803180704680c0c440400d550f440d072980120000d41c000c60300604003031429030000740c1018021118000d03444c105079030701010000d0489032702e000240d001c22040c1181d0400d0092094210720140140000517140d00066103039181154000d00c14818254154034804142c0c00 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 965673732 1250 965672482 965672581
    0x10e040c0302030607110d05040e2a0a0816020102071e080d05190c0203090d2303040803190c03090e1e0702010605031203010b09060a1101020d0f050708 67
    0x3618130710304202d4001703850490700803440d41d081e000e03000c0440c0031503218200b5241144c1c031800b14a5210340302c908503034000c240300d8203880c14030700c1d07100c0d040030131121280c001000ea1003140c0d5116007803031800d20983d8015011100c3c0301d10442e4010000300c000306104087e100655010480c0c00030000340c032481c0c5501c440c40380980603030809060008000b80078000100e07011003413402500c180240684c08108a03100d1081c540482d50042420785008007052302c80200118500c0918060aea06014042c1f415165401a40c820011035100081158000c031b0300d11044111b1000358103100031400c25684c0c02500301390380380c010034400ca0365020002e400c1400011040340040e5010480d0055414001c10007800b07401d5501445000c0c1c49017188840102c2e02880849048510002860381000020000c0152540c00a02c00908015031245100742054080c80240518142070400098032036a048c0301c0c07402d8580c01008202070005000800a41c82040c0036150485140c01c040d50140681424080d03000388500d08 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 965674982 1250 965673732 965673739
    0xe0702100f2c060711031c06061d0102030301090e031603050306120609071a0f0d05010f050f18100305060f010806100f0302060a140711011101020f03010e040c0302 72
    0x5641034107106141d11035400141c0421001060914031074003502d1800b038400a151140d4031001c0021400b900c10010303082074017130040c00e880c80c115941001010103a0680e4011b150543e41c1e4208109080e0004284010441c100050002000030707200080e40702e00052082480c000d8403441550243e03001441141c000700b081110040001280f41401840c0e82c00c01c0364480d01848c40d00c41c801c1201e00c80015900c0c4900d1011004112803030521305070506410030301d01103d02080c400c0c4000805105100007500d000101e03aa400602d540c034003d6120000282544203034041d00200b1901e031050385902c0c2107009080750000170f143c9203860b100c0b074010300641039038006800760103014240007811030340d6641c00d030485984404a5501e51543c820711560300100b072107000c0c032014110000304018180400509090600341c240611100c10070b4182c01402c0c2d210001c11540c004603c030110501e5a000241c03811452501b000850810000caa0801000d20045c060202c20510b00d4000400708501c1030070b4080610f9015 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 965676232 1250 965674982 965674991
    0xf09080d0309110301150b0f0c03040e06041407020a0b0903040902070803040c080601050102030d0c032019050301050d230a0b0702061608040303050702010908160209060409050303010e070210 84
    0xa1000800a041d8074500302c1d03100f00c10003102c04051505018000c551400740c1c0c4032000c905c1c980390b0b0040440e48030660101440f441800300074691141400540010440c05c480c00141d0b1030000e04200032280345d8001c2001c0b040c440005c0c40106913000444449099100c0c0f0041c3e299240c00000b10b20b0b500440d4071460005000181d45001c100d0014040c601462040034007818043d02c031b1551580b0307500240601030040c0c0c4140310700300c000301e6281c0100380c1d50025401c00080350401d08054035030f02301804100720610400003613145a140b85080311004407005c286021425941000d00180c140208468003030706409403000102030350220007103d80342150018040f11048400b51034154400307030046501e180035001d0240000d01ea4989080103000d540d0310380e0384410595682da5420f90042002424800c11903680d8541100040d42000040c4401043c20b010841ca0244d00c0c8100029110003c1c41d444c050b81c01c0c40b684800051000040c0c0e810340c0c0303203200032620070355407220220b18210091060a11250a0 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 965677482 1250 965676232 965676253
    0xc050412210f0908010506151c1104031202010e0d0f050c070e01030c0e04020310020307030e1204090b01030605031c02280b0a09030f08070c2f030f030a0f0908 70
    0x104a082142d070030709803103021903599585000d508130b4104851680d008514411500619070400c00140400c1c203100400d50f0401389132910420813580a0055000e00200019051080c085900100c0500c60402d20080c410140e0018030342c1c1c1c03a101031380b51400c20f0141d52220442d41038051020354003045100c4084840030751341d95404060807242844150f4080001250118244226642c2c07540b18580140003000410b10794890403009600090034401016502d020950301c281e01441002d0640c0d030714030f403a640c03180d04140e0a04100d4400700d0790703241410300d070840410083d20003080740d01d0703211000651514500b503882d00686c2071540f15072509401000424107190030350b9818484050490040e4807803d0160740d084007140440303420040c00703400314484094010140c0d1040b803860750300c44120700d0310200c0d0849603500c5140380980c1260404c50a80100c1070204d01c0d014461820394000301c21401000307079a0746000aa9202c2c82166800c02c00c100481098082c00d600130010300b401400d0310740803150441340 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 965678732 1250 965677482 965677487
    0xa200f0d1e1d070e10150206060103050604060602120f1c0c02010f0b0f10110a05060f0f041703061c0f12090518090a020a24030c05041221 61
    0x1900c20008001c1e2401d201c440341021101400c452505003030b0000d000940c1401c610411005004110b14480401c400010455803160b98035a8110003440c5c00419450600790005819108010312845c026842e107070082010780e0b8001900360320490126100c7d42c3e104500c0c20101d51070f03c5448181810242d5800d81d400c032040065203c0941c80c101540200f00544080151030103481c8078004c010350002c02911803411500d08000001e07820019402c0241d005034000c0542c505183c000d140507907090308407000b0008a03002c0199980d5000301c1c1c000d03c1642c1460907588000b07a20320310102c0304128010100000d00305850b016448052a444044402001021860003440070340034131208441d0b074404618072510039800f03000b5000a03904003c2c119140000300c03041b079a18440c0e008200038090b00c030b480c0304403000d82c0784e030516040a040f40c00d0000c0c456100806450b010090080660020189401c1d4529070042e031241c20b5030181c404c50344940300219014240503640c0c06110203856407066419022504554 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 965679982 1250 965678732 965678771
    0xf0b0f01110109060e1e060f06220c111509190c031a1608190e01090204020f03011d040f03111608161e030602250302070e0a200f0d 58
    0x1d0400d540003030301a1545000e440c2c0c40107488523180e91026101144891620241420a82424800141082c2206083e001c02d88140d000000c0c007080e404088806648400e118030302209084981146040c189020090342d41d0351014090040320150070022400c00451000e600001c50f040b00303086140d035a40c544641c101e14030607241242c0b143c20102d1580020360007035281611039241c840c400d403015400d4080040150094140400c0c003550780d4503800c0010f0fa224406030a0041c0301c0310703a46440b5070401074209070130700310590419002c0000c0740030000080c54007414002141e0b030510340515840001c1e144545480c15020100845082c8070001140c3d4000000300d80c0700a8017440707681200c0a0b903a000b83c502e410801d40d40407140307a90400c03050003c695280c000b016802c0000303d0a03000d5481200322101c00c650052400c40040c3c2060700100940620b2200694102010200c10072031921000016148600300e103400481a000108030103c00c110800e095408a5490082c107200b840c1c001410002441e = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 965681232 1250 965679982 965680003
    0x301090b18071d0a02131a280e2110020d0c090e24030a0f020103150e0c0a020c190e01090608031c150f030c090207030206010623040803030a0f0b0f01110109060e 71
    0x44611450130380300b4a81681c05662450043e445427100c2e9183c00c03083c00100043e90f004043c0d00304a178200a94405c1040141d03c2c2d1010100e0b000507183c510504a48040e03074030903d0504100456031509210080d00c200b020f5422202e42240601366551500d0300314040303505540050f17454055401d881c03042c00b480d07040030003401e4401d036810030030b03607681e03001545042c0418002e1100d0454600b00040c0a0315100c0c1c0203125054181c011a201c200caa000090a050a01c911960381d40400007001c10104401a40641c00740c1141c0c4002d01c000c50034000c105a407409645021052140410814011800c2551007807041c4070ba002e0005900740e0b112100100e0300c901a11040320202126000026030741610b109550045a06a018041c0e9920340402254403914504d000800100f101d80f516586490401c018401401c403980039648a1900d404120111030303032080844036160501c5d4041403e13917900f85440d0130030314017400d00001803811400154010860705e2030041c040d40c9411b04d000d405210000c0d060b02007 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 965682482 1250 965681232 965681257
    0x5040b0411031218030c100f020c041a010c0c050a12150e0c01080c09220b0a0305030d11040f060c0b0a0c0f05090301090b18071d0a02131a 61
    0x74503000400345951842c0850b0b294140c1c070014000e188050950508142075810020304659240d243c402c001502e01c101c140340d44e0301182928400184443d014451012550402c07141000061124940b070940d01240c085107074100701280c2c01b29420030801c000e61101802e0041e150884054035125884869111408284e4441c1c1c100d00c000030207400c05001d41445540c180340940641104000190380580d0040c08100c4161010700010000b611000800d480051441000900d03110000c3e4030030b01103544000d04903014441c001c1c000c1c03010841c000304440c81c6414011000074105075040c0120124021038020407005220303880d000402c2d69101c04c00302d50281c0500c0c00e4121a07190080308004a4001d9041c94000c030707820314071001d41a80518003030141c0c960050008100301006d640c5903204428111506207000d040e041041c003003410300304003140240201c03052025910b1404515240a0040285103a900380c2e00010044c5602c0704004c00e90000f0032006222032000751003600701c0030342604000081c911 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 965683732 1250 965682482 965682503
    0x51011041a071e0f050604030e040c02030c07180e120705160f060c1e030c1e0c05090405160e0a0b1c03110c0a0f1a03240d0605040b04 59
    0x156004900032955400d9214080d03140b08110b1030414001054480000d483c04c04000c103d00c0003055092140031b204504c60341e500340803611110204000c4483d041e60070400c40d40300340203023a49208001a804255403036594020891070ad5104078501a0010900900b2140142e003042c42c50100c040c1e020700040782c8a2029101214404452004045064800d42c40c506104c0d44040001a00580705007141601070300780446a03810301510380e0071540c05880b040380000c0c0410b8405041c0b0070360f00024503660303042c11803071400100e15480d800b0100c40e0703501516100700100800710702007080030018001c5494250b0043c50005a9807150013845000c111303245000b45040084c5c550f140e240100c86100c1c854510038015900c001d40380c5080314554240c220300741d076074419001d030b4058554a40c2a41d400501b12461200c01007810641c0381c040001c101c1440c03d42d010400d0091000c030241080141d20341108400101000c00400302c0003400c8007a00d0613003d0011450035041c4030038095954210f9220364040c1c454403a = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 965684982 1250 965683732 965683769
    0x18030a0c2a0e07020a0b1509070e0307351e1f0c14040b0403050f0601080c010c0302070f0b0705010b01020a030e0f0a0803030a1407140406030905101104 67
    0x544071941045803645000364814440c40303400715907003500240300d0b00c11a481c0c152155500161104280e44072407000462812421483c9001500b180d44044a40f400d2400c1c10103010200c2d0340c0f1103c1d401143c0d280310112100961005c0780401108140c184594415540700c44480d14503165000c5408564500314210407603001c0c00d20024142103015042c80807523544580c025440402840b00c00c10701010010080044103004140d80054409440c041072415685d074990b142280c901079160040f1012a00400e004012020003c00d6100e4144000c1c00d000d080c51000e460201c0c20034013150810a62903680034004030314151408094001d81344100000c1001440303c000581e0b461000c400e00900041c07955034000920705104556141d104000b07010a021aa150520305003503030000c45808900f1603031840310304ca0501102d401c5580050117070410015a9a524070714840600c140c1c001c00701410b44450f4040701308001002103051080c1042010440c01c038480201e28001c2d442403041520b81c0280a400380d = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 965686232 1250 965684982 965685023
    0x3030f010e0708130b0703090f0302060603010f0902130509100905070e090313050f030a1509020123040911070f0b06150a05180a0b0706140703060b070b18030a0c 71
    0xa4050105070259400c11300305580c41074914800109910205601c0d80322043c00038245800c1d01e59a18800e4000e4062850a4424542140c180280c203103681d43c10a0103840c096100e201020425850704200070480e07076200da03c0a8034140700d040d119043d042c5071040d10000d00501241c000c080c3c0f4600104a0f05948403203100d155a4001c0c1039440703030080102d4074204010b20b41603030050300349100030f0151403108601e500e80085038942a454040350544628900045613401444041c0d410ba1101e07288a1928584021110a0203223004600100ea59080044160560a015500b217642d0106081e0010803040c9051001caa00940e8003a010f0441150300d018044008001d641002c000e960300d80381070500c40564110010090302c4e480307030000c0c0c400780007144442c003d41c01401c00034000d42c170200e06002c80e51240c6540c0c81c80105401c003007510f054002d11159505904a07400340da00801014050386807400e8542c0071020202500803a88030001d402d80700243c02c1489510303142e0265200041c61100020b10 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 965687482 1250 965686232 965686247
    0x60a12262502150a050c1e06070e13020f07060f2708131e14090a050603010e060106031e050601350106360b0906090303030f010e07 58
    0x845106442a4810001c44044112035051072070000f01a0310751465858291905a030046141d280060700010703441d0305a820402c155820902580c60088203038042d040c00b0b94580700043d114204102800b1072000c12591250403c032600d0050301c10031580c400340c01007030b44655403005600b11030361803d000c00e00c0ca001d03c06102d00381940d000303070b100c0303135a560b15020070305503150711841c000ca540c0300307003481100c06000301c48054034058800c2050070ba00b00f8001c0c03801d859601c1415400726500c40030100044225440350520503400c210350100102e11500c0e52000223000d01b10b512020003440c401c0744000500294160807a044405d04e106481950b80104ca86a5042c8d03841200c5a502003424080768203100d40a03601220015100000c050342031110085070b2151054081e40a00009444c0074080e00c0300d00d5002d190a8059500d00d441d01003040e46a0800030840e09032403040b034205010100d494441c81c0c0303d01048480307030b9500406032647c038908150f4440d2450000c2c000e4000c002100d000003010300d07006419 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 965688732 1250 965687482 965687497
    0x30c01030e06070c080f040602300d0e190501061d010b03060d0201091703190f020a08220920040e130f020d050609010e070b0d05060a1226 61
    0x2c1e00030369507070210594a1079030b40242201c50f207204105030b80f504440e50000c1c0c40503020981c0606030f011203c41040000842961002201483c405010340c100c140c02c0c2d0884104002c51300003c1442d0a09030011820000010004070404101e41216010040103600240c26035982c40790b0100c80a60303c203c000c0b03000200f40904101c0b43e6041001c0f641c145864200c19210304e1051520007201600c5a4580c0301c1d2400c09244815181e0000c80c0540460b042c131118184030030704e50b00d01400746d80c0d40894003d68808803510302420000001072801241203020f00d1001c0300e0b022201070b85150f00d40d039220302001000031041c0c009001c4490701c1c01c4100203442004403800c5039003502c03071280192203182d6502001a44104c080b04c6d00d412441804005072102c007569081300780070342d018000e1b91411520707040c2903070708004400c0c280b9080f0380c20601c00d620b4860282d40321900c40d010001a02d546183c0484c601c900340d50070000c50046040110420001801180108021190403009603070341c07585110302c030074002c190307 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 965689982 1250 965688732 965688761
    0x1b0d0606082d0406021611152803023609071d0d12020102070c090e07030b0c040e040c06031103450d030b030a12122405030c0103 57
    0x80c2e100300032206004158020380959401440c0809080390070340000003940c0c04450708883c0b000100003514002200e400d400c008010440c0c5000301c8010010800519240b004540b501c0342415510601e210b40e06403880c03800720b8188032072004000181c4100981110005a1842c0850650708540b4109017016502582d440d8590281c682914118920303042c005101a9820002d00e240c0600462a181c4505001450f150001a6903020b1418185c0704802d40f50018040a800c10100910404000804078103c0fa003101c1001c00c00d880308109a440c03441140e02c40400d9850080502c030510220905501c103c46141e10100080306810a80b602c0c280021500b600c000303040708009000040b00c80320307541c0c4180142c1c84400586841454902c0103102080490300c8198804402e003c800d0b84c15109204865030110b00500c09100d040d6a800a040008420310341003000a291540c103480158100c0c045406840310032004001102c2c2c142403100c412441444c0c400d214120340410194040e200d113072004103880 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 965691232 1250 965689982 965690041
    0x20f070f06020d0f17130b0a0c0203030a090203250f0611100b060c16090c021f0b030a05030301080a03030f0e1c17040507060807170703051b0d060608 66
    0x1580251200710012031301d0b0080c0940b035450f00b83c1500c0c0440c80c0c07911420015000c48803070885410480d2090000138000c403119442c1020048020b0b8000080d40e5200c4510240800c000303074113102280c1000c08804c0f1920550702c00c002c4201450051410b000244c07181c0224000c600c981e00e001c22a91103503400746029054201c0d10498414006036000722a00c0d02c0c0c00303050386203014410340009280c40e2062110310381c10045003c09009050050113880c0c0c2d20039107403000b01503e5030040f188884040d01d4a41c0900160303604c02441d030381600c041c0315a01046800000f5261a50ba44115168403641021006c90005e458403806460301340a61140c40c20814100e00100092041c05104010002108002da82441081400000d18034038000300d952103144180040e0080500e03003100542038500252502e0b05005141040414042031941d00581c48070483c9000f20369521142f550801d41c078074146851030003040c000382c0c262441805400080c210741050b036541e485035035070b8014643c080d150b4507480d18106500 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 965692482 1250 965691232 965691253
    0x20405060d03140a03231005040e1b040e100905100612021504170c150405180601030f0207060905120f1c0609020a091a3412020f070f0602 61
    0xd00203031180710054100014411b58070a11701c4080301006001100b000340d5941040380d628550310012000340b0084e50240081d44800e08469110005491450003070502004042c581d940d458100d94600015901a121880480076203980503219441c07080d01e40b03105503020b01e003d0115a204a000b01e4001032603c07000c810f030a5003003019000d5260f4001071801d8080c000810035105501d0358034180d448000003800040e4110341030100c0988807642207010380c002400108000c1e142e0100d041d983d2004100800d1103070b5903a00c01600140003ca1a000e0f0f6644007081603810400d03903a00070b01c00240601d084480a5080282e40d030a98030800306048a03080052140190f0607003007a815400180b11200d000c112107850303842020898010031f4591000651011b0100214029038044040300d605103041286081d056000149248800c400100d011900e1011601005000d85441c6d4604076444181c2c9210f80340380520080d0b4404110047c00c4541c0201a0002285501306041c001120b4007a0080c0402c40d00 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 965693732 1250 965692482 965692517
    0xd020105040513140c12010b090d021908160e180c0103020903011b02150a02040302010f0e011b0c090605031c0c0f050d020607120e0c1c080412020405060d03 69
    0xa10740040030095180c4c1c50303030250196140c80d01c620480c000c952860302e65689281c04240d446041e409003402800030400d12202e51102c49101c0500707038064648408001901e204946800b0041d4024146802241d0003030341201c82901189013220000001442ea94698500300754208030309160541841c0c0c419007024015501079001b411401000600000c1c440c001c0300f001d00c480840e11b050001c0180c1090809081204810303607625000210036500714245421170340041d000d81040c1c42000c05021000c002102c483c1c0c441c3c80c14200d500d030410240c149060f01807030b0100700f40049000d4241001d00701000400caa04001030300c1501442901150001015064400ea03006869540b054902d020341c40215408070320f00308070102e0320750b10650013803855180a100007040040d5040360400803d04040c9440c200c0c1200041c40805050300303c0d14800314550355071203541c4000038140000d10710880801e00040c0651007104508826000352014032140c2d8801d000c100c0094540b400040c085010420308401121 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 965694982 1250 965693732 965693749
    0x80f0a23130e2a0a08010e040b0408030a0b1c03080106050a081f05030f0d090b03010e1501121104030c0618030f020f060301030f03090e01081b060417060403030b0d0201050405 77
    0x41e00d4805441c0e0642c1032003d09204804101140707140c4600c001501c0c0541a80400114010b00e00f42e6683d58843c1030613601d461500d04041d2029107160380102c0400c070300c0c04565001001800c0000c020091412142d80c050080290780601540421107010000902d60f00950850f009400e0307175503605e5104c1c5e5405201411a035110300300180100a080e502250f10313241041541280503d0f800204032142d4070080040091100f90051280150300780010003d1071012201240c01c01e6040f00114150303004100100c80e070740c0070841031590041c20504840e802c41d50284c014800e0340c4c003c6149502c3c89866400c00d641c078a040554500001c15441d0041000c2903d5086c513440081c4000c01c800360203d04100002c005030400e800c280e590342d0764180103008041e0090341640040c0100b1950f54015031520302d50355203490308031551070910885681001051f03070300d030030407640034101c24a50b601c2900500354000e640c554048404402207031811190b908186000c0c56800c000941c16594246011700703110610640c0c0 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 965696232 1250 965694982 965694991
    0x10f051b1303020607030c140c010e0f030a05100c021005010303050a110106050402211f090902030f0105040516080106210201121b0f0503091207080f0a23130e 70
    0x10800000c040b006980b000010075040b8042e50314110065114100350707561488080c60342545502c158110001c6980080140c5100c002c1155051005154540800d081c02c03030200c001002e50003003403071140e200f68080d448038940c010541e003212194405561410f044800c20b001c0680414818429244000e00c1600c07400f1055144000215401e5074400c00318042c1d8000c041060f01d0401f94008125003802d010010503481000029034240628010346c0c400d0000e84940200c17801c154450f0080c0f82552000c01c4880070840c203900003000075207014105191202698403040880d52001003000800c01d03014020b0388141c1e4100d082100c0036491034520841141c402c0c120403814004010445c91050b6040d10442c002c054104000d07029800800b40001c01e500017000001c0c0a004080c000d2061021000994100c6030042d1602c040c1d55141d2410150120300880300c05014060f000110b9246c542e41c0030800e0642001c0c08040c140c80340001174810180c42c02265a00490101051010000245c8682029800 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 965697482 1250 965696232 965696257
    0xb0301050f1602031b012013031b08030d0e0606011e0818011401050103060518010909030507210905060315040504060b0a0f14030708030d02030432010f051b 69
    0xb44400f040c855001719202c9200e9101595403090540390000d461048074041c41d006d030607031501c0c0c0440001d209101120350b000c00ba02041721100131540030750f513040780e0b07070302400c5d5100480340c4030220401c202001d07058015450400e801841e0126003507500441241010403140711081003442401e80046809040c01800300b081c901ba9000e2400309600280302d441032880c089800d42200d9810b2030009019100035a220030b00401d500081c0071001c0340440340050642c1c0c4c00390004a00d556680c201203074180288003014041d0011800c201401c40740003140d80c88a01c517103403503648185a54204004081c04219440c0c0c0c0e40c1d16450511588a142541c000c903401449990300003410b20900002c2505590190002d5000c03901d00ea000b4094040d0f80300a02c10711040842c02000d170743d81451490350300d902600366911101c640210105007005001c00c10350440c00d0300800c142c2c0c104000601140e403681c14980a128041d442c1a1000a24000a00807a40316a84012072806100c11a010141e81a400b040040c1c00303 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 965698732 1250 965697482 965697487
    0x307030603080703030e070b030c040e19050118050c0307050a030c200c15090f011202040302130c030e0703030207120201030212090601051c0203060109020322150b0301050f160203 79
    0xc0616003d442014020f0ba000209002c01e003140b0ba26148075600a40c030442c00030700811030488a20811103040c0c440c609d07401a11074407a070201da50020b20480480703200382e05100c004140001c8412008820705442d03202444291145004004244416900100000d0082040c007130064084c0e00504a41d02c0d152400c33068a41c1c3c2451040d400201c50b001100994028124035641e904d40340303003003125150740c0e460a94900480f40c03000a0301020301200e901d0500c04010300000c004412a8140d90043d600940b090000702d070709400b80c900800a944884012a25000341e00c41406000103c030030035a9490340090110394240103240f174940c00484012410144c0030402080c100c0c04104086004402c580010200365040008014410101080c9010148100c1040034056030b40006d281d0f04441c884200160380791140303842c401001d00107501d28242c03101c001241c00c0800400e0030002c100000300a00402284010004243c01d807007003540c02c01d031000520ba006c50342c0c1d00103030300c0d184603203804070f004607031 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 965699982 1250 965698732 965698739
    0x702090c070203011b0e1206010e1b0f040e0c0c0d0e1215042108060103090c08030a1d06040807141216050a21140f1005160302090d060203070306 64
    0x13801c0d5802d800003000310f9041000000c01050304038103200c665000444025690030303544000b180d501c120510503100703ca42d144020035000b010210506050140e02c0c0c07110b6544044000980540f40d0151040c0090102c00390009040d401d00401940c1c50030001d8009800400d0305920111004518400040d6000c24030000650003903100f000b441c01040202030078a0810715182c108104040c1810f803c240305407030b40d00c0c05044036a500c803e00c0c99008a003402c001680001d80e0404008540081d00303c0c102d1803100040a2895a03041000c142c1401c18100d40300c50810480c40c18041c081c00746214200e803503171294074203010810084040c2c03020113801a02075410910500703095441c0c14911054038040003134110b410700c007604103040d01d0742c040c0c035620188018155a01180c2d5001f1400c40c0703406803001086d64a1148402c005002681115150004444a8043d90417065000f06010380d400d028100500c00c2c201c1c1e600d806030090315000c003c000c0c010040441d560322440041d40c401810101059501d10000c03 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 965701232 1250 965699982 965699989
    0xd050405070f031a0906061f021204060806090106030c02030702041107020d0b0103050c0303091f021f06080c030d0e01050706150308030603061e1b270a0b0703050702090c0702 77
    0x4004501405402c510440c13444103400c502580a0000150b64000904210090320342c0ea104840150180e0680000101c0c0803404904002c04124002c2405600007000506543e000401c1e43c001c51049a03000c0250342d0300c080a90403144083e0884c4003603041404a0000351426070700a01c0c514012840c145d2900388164001240b00415650440f09007071544010300910504001202615405a0040d4940015840007850b10161045c01c1240c1e00076000d80000001c0c42400111459034132090645221001030101001615660041d40c0740c034415203040c2042c91600090200360300201d80c80f1010316484e900b00440d0a48c1c072041d000d48d6203a444903030b1100324480da01c690400441c02440c0e06a100e0501d10105030801e003000c0c00c40c0c906030500314000a02080c0400340c642e0003080b04100010070101c0a840c055060103202c0f01d04849041c50301a10b40311005100401410407003c0f103401c0030107500c801c0705014a004010028000500c148018030060074107082d802c0c1c2200108102d1800c19030b0a6000 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 965702482 1250 965701232 965701259
    0x30f111204062a0b0a0f140f01050f01030212010b03040f0f080714060402010806010e0103090507030813380909071830020d0506100f1a0d05040507 65
    0x200300288030a401443d6103800d4440b58618666059030003142c0902e40d4907060000800a06a05840c55a80101910b00b002980c0081c108058441040c1c00d680380010340303170803241000d208813401082e103c403401d86150b20078800c9403021303ca81124410264201040350781c160300001c008075060b001d1a1105001b03c1e60714a101d1011500c1202030341d0b500c00e060314060310b044441c2c503001030f52031740013406000043c0c0e08240811b1b4850320070300e0b04540c10304001004a0180c040110090054014210044184194400144501c045182e000d0310f41c2580c03028100c50212514441e0030b11300d2030b840040c1d4003411880c142d8201c4010441e58444c00c0032440000500d403150181d03022000704410310301c00604d40c80c00e05601e000401c00d560b400001e403d2180d080078800c2080200c03100f828510a1a22811565042800c0c08029004000c0b510b0614000b000715078020f00500a1017001c060156000545c8403039182d010442903595040982040c5154081c0405024050400c64490040850116030b410300d1806 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 965703732 1250 965702482 965702489
    0xf0f03091a0307030b0a060206040f08090a0308090f0f03060f0603010603081b1002180f060706090305070c0f03080702060a0207180b040b0915060a0309080a030b0913030f111204 78
    0x4900380d0b40c0c14801d6015080700c0403c100d00c3e0149180080c100011900491441c0d8000d811854a00109103207203404803861280303000503580902c2441c0c010003030000c0c64000d800c04070340070780e4100d0070401e0420420070349070382c0c501203164554410000103604801d5038031600d40289000c1c0c004150103850303030350301c0c1030f6604504500e1400901d40d40690007060743c10842030162400b00e20086150805003040b038003414110741106806611980070007210350b110102210502600044104440d5502e40350080c8264400203095502c011861004141c103a984441d10007240d6002d0b080d00c2c90005154284007198000b4000c01c030541c01134540004180540342e4a002c042c00c0c0b001030010759450000c2c01c0104a92020707800a01a07201042003000c50703e82140400700b4443c003150410f45420950784114040e040d580c4009000c100d020407511042c5415410052840e0b0b030480340d03c0d0f01aaa6071a8000840000b850098002591040940f8800b4040c1d51032010030220481980ea0309000a10800c3d802d51040c2e0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 965704982 1250 965703732 965703779
    0xd02040915030809120f1c08100b2d040602010903090b030c0d0c0201021908180c030c1207122402031e100e011211031b090720010b04050a090f0f0309 66
    0x5007640c110754849801a403052190000c0341e10070b4184a032b808440d01580c2041d000c03044c0313001241e51030965a6400d0301c0d1700320000d0041960f1035485000090280c442c0100c200d001c2400d00780041181c1c0c00c8201940d00c5250000141800c15000d030b4141c0001c0d00700c0381c103500c5c1595420019100169a50408100c190115844880b0541800d0380c00d13403441c0000c00c90404041d0007a4000078900e81d40451516290441140c45002c01c6e045021403504005240e0f00982c1030f584900c603840c080260820b2480b4001c0c0d45162a001e801d02c51195410aa05c002ca50b1400341d4a00e0a101c0d00740704001e41c24103500441003604041c2083e8031030f43c110000131803e801183e59003c10a103244e04100c54020001040003054016120480b40d180d01c1103612070348a02490f10407080f40000071401c51141265601c103119029540800e802030300c0d100c030300800711254400d020300d080000044d107014403402040200d5522a0070500001c403903072550014003c2c80c2c20110100240f80307d0009030381c16039800341d089540c0400c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 965706232 1250 965704982 965705023
    0xf0712050c0a1103190c05091023040c0804050a150b0d0503180118180b09070c05010e012702040902040e1c020d0f110c0301020d02040915030809120f 66
    0x4108051810b08003000e00702c00e42d03813405d500b500054034440c030320001c0b00c209031820180340e01c070b05103145500b044c503070407859040800205a060052960604034500041990108070302c20041300c04450004d0203c0d0068441d9101d000303040001100240500410120709900065449020b0000340c0c481003e064295005e9201240c08030704420b50303000407048001c0c04d00b0300c0740d505013052000782d000105920904070040b244a00c0c1e80f205100e150810984640010204451031410360409000d1030784449043da403641c64030b44600061181485601c81e0058134180c0a24072103c901e0311514810900348040342c0041d29000400d005031660302402c0e0500e1700c0d844c00b900c5140e040d90305902a82203012214000c641c48089101d1040340c2015030009a642e640c81c0c5095040d6100c0045440c1140700d0304c04640541c4001140d65400303000354040d2094a030980e4046c0005440c1116684104406000c00350130f04008200f0740c1c0031441c00c81224102c0408400566005100c80d806241c1842d08002800c0e103952060b = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 965707482 1250 965706232 965706263
    0xa0807030c0e012409090912031401081228170901060e04060203040609150f060501050721090e0a020406110604120f020309190504110f0712050c0a 65
    0x6070506003014040a1030044265894554092280e03450b10300c0c03881c0040000315082250380d100300b003014041c003078005040c0700c201e040b0b00d40005003642d410f40c51000a4640032490411080c0ca4520070304075800000108003642d049c010f5803005c0d50003071580310035001d10601e0540700201074254100721903201c0d80b210060340940782518514154002e102e0355040c3d2410400b8040c40e803100303458175002a0440401622170703450f4a0403000170045004042c0c02c04012a4811f130600c81180c10912250003010428070040f95a240192103a0141000040100c030300c69000c41c2407403a181035501c0360103403d032410700041c0b542d03001030564105064850074041030b00000e003846650b0700320f00c3c00340d50900d9030001040c4500d060b4440ca003a050b09414a0020019107011440c041d91003003090b00c2c103201c0004c10007a08041d501c0800350601c3d6a505c5258015800d0481c2010740d005c194090710900c860540e00e051605c0700d19555006034030340c1c080c01071051020a00c00a11855030070084074580e03902c039000c005e000c040c0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 965708732 1250 965707482 965707493
    0xf040f0b0a03150308040608040c091a0103150b0f030417030408090406050a0b071b080f060405011a03150601090b19140310030f020402090414150102150601050d0b0a080703 76
    0xd0705501d10202031501c02c0b04100107105c900403101212045d01c1e0000264481d4504564030811580c803852880d414550041d10f081944407060020341c0098070100702e4155240c50429603080248112888007400f40480034840720030b2801141c0c01072003445c84003481c40c4122081d4005800503107080d9444400810001e40b03a0500e44901c1c40900301c226003241c091391821003c41c800303201d20741e8001c282c0e84145816009004004c0705481c007821501c81981e8050004d00c016683c1d4000c12030701030780d807582082c4241a03a5000524a00b203e000c01401908130300c2d2054a441000060290034203040002c500f00c0003801c024480080c000000010b003541c009442180c000808040d403004481101c0c8604105010030b85202200c0401120f50041c0303403404c00c0b000b44c00003900a00510306165049824001d60112034032420078943c4c415180c9080616022120a0049a40b0310380340e0081d802c4050302c40040b504075070107400905404550040c02055084003280400d001d9581030307001012030b03444514140200030 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 965709982 1250 965708732 965708741
    0x907080f0c0f0406030e010f0618150302030d0522031a0709060e0f010c020a1205070909020a05150d1b09060c05030d0518060108070504051509010b0f040f0b0a03 71
    0x110039010762800d1024824103041507200301d100356424160780b8000303015860f6082d04100c01281e01c15400b00030280d5921413140305140c00f0320400c480b4914104520b41480b46a42e414030540fa0041e0080c0010710b03130035005039070341c0d0b12030a09445d507a0030307051440700745c088181c06040107184100c0d040e81004103540030110400380054030741400d00858940c11300150391300002d52800c02108071f6008042a40c480c0041c1d4901d641403070f002e03411a00c031000124440c04802d01c5104080c0c0300d44200c1e00790940e51068082103861012000354071094003081040705241c2641e0000d42c1c01c0c0244001803400034842680700854030b28203a6424110249040c00125503007043c0800018000c500b06052941403e07901c06440344100360320200c1d040e07030324000b203070003288504114504480080b003220055611070080c150349540a200342441541420001a00344940e643d845064036070140619110b41d0804101d1500c541004014100000051000040c90190030f10204001c18080422640d0b5880c5000000c0c203a4 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 965711232 1250 965709982 965709991
    0x303071e0c050a121101091415011a0703120c0315210602030c09130209090709050607060506031f060f090603031409030111030f2505090906060403020907080f 70
    0x7046488800030a002280c640302d030641c00142c510400110100c2511802c020007082a02586481038031410481d8840b0308503014440345080f1503a44406000601c1752810074010350140407154012100008030100c00350201c1c07071290500b0000b03603840d07a905400f2110030344460b10004e43c840c180b2003101404001910050001d51305184002c0119182c400e6504d084044001d0500d0303070020000781a9154a400e07030b04480401400405c0100050025001a40101040034410004071012900560240c50300800b03c4102a082c141044001d84400000309401022141c040c041e00301d010a40c0d40400706000c4440d0052680005d07020b0604280521303403500b81d000080e40c586003210600c00f081c3c008070300ac0d9403440e0510036560356407860301c00b1901400f4450b0300e2400c004004014010f60300d4016181070f1027003c50b0011803580c2403401d000c44223241059907a40010079410064581c3d2030920f6400a9401000505160f03d0b20b680e81e40800d000440840310000090506070174070045845841d08142c00 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 965712482 1250 965711232 965711237
    0x1b07090f150f06020a30080f090109030c02010f0210020c070906050f030c120f070312030b0307060f05090409050607030603120507030801121505010f05010905150703050304140303071e 81
    0x10074180580a56a820070203c046d0132031a41d0149140ba501070380c201c614403400b041020554a20703020001409031002550403c840e1700f5090001404c10314148510b0440b035405a9558208290640041d28242d1860300c0145c2140503a80040382e011a0750b000400400f1012030003013025034a001181000c407001034200501c42d42c10004803c019a030005046040003c044070750307050074106940040d260124116880c1c03840d00680c02d000003800203010008924000035201800680141010191108100c2c000c000c0424a07140c0e52084080c0b1a03405031a02c200082c2002404d072010740c68881c0386c10b00481e0300100103a1114000c0c800c004524554204516030b60030404d041548598010300300d000140030324403c030351810f40304c102070007030700c9416203809075903481c003080710756150200010652800c0c09600c2c0428050700300021903040c10751820002ca9090207405042403402e5074100c1351540b0140003a03511004a41041c014800d083c0001c600503d8540c442001403800400c444c01c18030000c42c112801d = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 965713732 1250 965712482 965712509
    0xb271c0207120c050f120a03080a0c080f0103260415170408040e1e04030c1211060613110315040b060a020607120e070305030306120705061b07090f15 66
    0x54043c0e4100b500b5504200c0c2c09407540c11031880483c5600b140c0707411804c828843c1407403420525030414031150041441800600a1118200c000e80b040c040035141d1078485c401d188010808100310408040d107100d40a4104030b04814000c082c1070700380d046500300d800381103500c025074a0704d41d42100740243c07800000483c0002c103103050303215000c09025521904080410004c000303802d58040114000340700d0f4051f040300c41700e41040d00f001401b1050000c0b00321018681f00ca8060f04250107211141225800b20006284565600c014015000e0f100302c100044a500e401c20402c46a4009018500c00c5d40325195400780c0300e9a01080105440c030440f42c17180698820411307559601d5002c0381c0d20741d000601c1d007810800344d40c4c0d20a1680041840da9030100050081c40000301c09c1000200045000b07d800b11912003618910300030054440c5654481c0c00d03030040042200b5001d00161100c0c14103621007140076940d260350359220f00403e540d0f0481c55408025910641c1d214841c10050401021f010100c08100 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 965714982 1250 965713732 965713769
    0x18060105010c1202030f2a03031626040b0a061a04030b060f1c0311030a020a0f0c1d070f08060310020702130908090901080a0b271c0207 60
    0x1d02c40100c903800500300d403202c1034034448528020022902611422282140e41e070306035040240d0104100c071014036000d0f141c007030520413500700001603d0090040020380d40341c0c2148210183c49840b1050807001400000760540c0507591024041c80c0e00c56402460b030030400f807074480c0c03000e021140c940d0051a420380d040380788240000b080c6411780d401d0340c0d4005410340035900c41c140051460030041b0310032a88071303090755940413080494611000d1168400e40390402d00c04100a401612401448403800041c1d002c16848004518036903540240c460040340d040c0c01032a11a140c00e103450710f07001d980034111001801840390107940896111b54407401450240040d040c40d1001031345038000010031108203500842c0700346c00c0d56548000001c1d048000b01081094109a01d030065664100b035035041d01c03c081020000480703142c04640f041c00184d0110030040b103039840201c204c4070403010012400b100b66105000381f1500c64100402060f500e02c40d4a0440010112a8001c0c54414150041c120040d155082c40 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 965716232 1250 965714982 965714987
    0x10f0f0b0f0d0b0a140f060f0703210c210203041a060f27132103020c010c0905030706090803030c0c0a02191d15240406081806010501 59
    0x495030303021101e00256460b0302400d40701010344a01d40ca00c940c0705a0840d80043e030100f84807081070130490f05403180d411540300c86003041540e0003811001340c003000080045000281c49900f0402203800d5540f010009210780c182480d084030b14152401c0080740310001707003880d694241800100040e141c1c1106510b180b9050b5a121a0080d03c2200038503000c1c01400803d00560700c655450000c00c0c4082c280c003082040e84500401a880e83c09100c1000011b41004140d54403d18019240d0039500702804910203000703110511550314510002c8001c059007030001005104d03007800344603090384041e942c80ba10a414a000c01d41016003e500503000d020005804100350840402620791110603130108903107800c1940c038840c0c20564204002503002800e54600318011101c40310090940b4503c01488180e0b8202c42c1074640c405500b502c20035120940d140d2031046614000800040b8143d00040400c0740110010741c903850f982243d0440c50108010f5003c10035050007844200344003a802500900b01c079490b04001 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 965717482 1250 965716232 965716237
    0xa140a0519080d0b01120c0512150603041502070b040f0203010c05040602070e040f142b090e04050106180e16050a180605100c0213060b0910140c06010f0f0b 69
    0x5003441130349440b91145144c0c066001020790301ea10f070b0400e2200c2180100000c0060344000d4005d81e8240000c4045800c1411a51030036600c8000540013038619211074403542c12481e00c41d094502c0b00e45c0c0030052480040c8032005068000c1c1e00c956000c1e440c90f00188105070941d1100008a420420103210400c42150300081c0035045840c0c3e55860030385501d0300e041c20f000c01da4141001a013000f802540c0d9144401000602c1e40c20325444c0ca070310071403d0207258031094808407a5851a800900c3d000c0e800e0050341201e5a400b40c0252058000150b071681d2120713290000300f000000703520140d549610409007107105100c801da00f1140c218a0300109070400e0300140344d82d032660245143d980f5100c2e441c2600c1c01c44d1a071001015010007851000707040f18020300149080e4a80788201d014051020511078000d005005d045c050301c0100050509201900040c04a04101c08104008000a03000c0c080d60104804004181c20807089002e08541d43c10b00e05414105100c0c0d9001c1e80d444030010b0000c0046802c02402d = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 965718732 1250 965717482 965717497
    0x111c0b060f0301140f0414070b1917070509040e0718020903030c070e0a0609020901143a0c020601080d0509010e090f09010506060c030d020c0a140a051908 68
    0xa01c022400c81410109004241252a644890302c2d010280040303520601c0320184114403804030100003901d080c0280d5201c0c0070600c1005040c5400784009165425200b841611a080c1032401c0040d140e01c9024540d108c100c141c8000020400014550006060500800003003803426401804400d140c00b04824450100b0441030b60825404142002d030b40d074041c01124060350090045a03001601e82440035003000041d5031602c1842d01c1c1a8001606000078025900f01010507145c55411b8150000080101e074080c100c040d030b03100c10540b580796400d81030110300440b03840b46100c01d4550003000b20212089685d60b001001c15940000010084000000385400700c5026505d841c6440d09115401a2002284040d049030f224010303404012071240426509480780d040a0f0007405603071100750074050203100e55484006a0f4204002d0b01c80e8842441c4c00a064141c11103003181d2210300705455110014000034000c2403a5004450760324280305007080f41300c22208400c03000d1079114680390741d80e0465110384013 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 965719982 1250 965718732 965718739
    0x103091515050603090f1603050606010e121609060506120c070807080309030a0f0813060e100513030801090b06030a0903020708032a03032818111c0b06 67
    0x180007400d901940342454010000501100e440341881ca0704103446400d44103c0440510900c2913028140034103c040308100d0303810401034003154481c5401101c107a1707008008940c01c00c00030340c02041641c0c030401c904807075100410340100c0b03410304003c1c80a050b2142540107520070070091141d2000400c002030803c0e0030116844a003a91444070380b8211440d0302407540c01801029000c020405c3ea00d40100040110660036039443e69013103505003054076419003d982d00089264803041031030001e50507600c40e032500c041d1074013142c00c010441d15191090740c030700310340b24603c0481c086100c90805401c009114090414824180610f00c1e0440100d001c9020040c9142541c0d034503140400c040c18001d11042c0c024203850406e5955400d00010b50649140d03601400c072400020010b204907030b401011050300d028403184404201100c204640d00a82d12840c0400c0f000c1043d41c1c0e0441c5d4580070400b21b03660301000d200e0742d101d130a0b8800c0d0601700b00c0303100c080c884182d09001c1840d13801e400203071060452035800070088 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 965721232 1250 965719982 965719991
    0x30306120106030c0b040905090d05041a12010b2a0c13090c06030204050a171b1801060f120902030a150f11030402100c110d1a040c1401030915 63
    0x140d890a0150035250b2002d091000b8100002c16162007190003881580c5101d0000e20a035140c0c0c07405145c0c0d500702182c1010000302c0510040c803141d00c1d90104480e2145940c014035080805468104032055000e0740b0500c007541001518904070861785c19501401d042c800309401d01c01c0d115101040e110490700e610103100d420b0100100c950303445158000b4004175001000e041c00d00d40c5800001c0d00951060003600d1060340b014400044030002001004106640d01c00501072074041d42e03488003009000103003801d40c02000b00d107501c42403100007040c1600900c015a01e0310460307500100040c01c401c0b40781d00d2040540341480c15650268400081203941540d020ba241076520303e0798000f06004103c41002c1c0d01546080c204401c41545244010710b02440c001c8408194140b10b8241c10764100410040003080c0c00705122401400e40303031411143c07666601540c2c1c1004500035441149080b002c007190308417121030424030148a29518102c406030301c4d07402030808000222036500c13440c05c90b000e0300e010707114580e484 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 965722482 1250 965721232 965721259
    0x5030c06041505070825150b0f0f03011404240504260c010c09030210080601090905042d03020105090d05040911092205060a0f0b16021003091e05030306 67
    0x41c0c0201c6e12010b0b0780450000c680360b41401c1c41c2c50000b8520380191810090251a0b02e14000c00344241c0414502c010308140172440040140195005c0080d41150306540c1e0300212840060b503078111510880c840e0828114501c2c4c130394000c400d44422410041f4040e85068104400601d5a03072a407044080403440c803c1e01e040c0566909407140c81540a00101542404801918160040d1050b019684221005203102c0a109011141c400040721214001012550200705181d0ba03075003e950850b0040004080642d03151001b405421301c40c0041c2690541d07482050030078164203115040d001404072015207140b0070041c030000c0c00c6010303a025401c040d5030345080040007104650304441c1c07864405081d02d0320001d141c00205040569030080c044103581054001007441c903000800d801605e64440c103020b405410807101204941180e403004160540b045a0200583d07120742032103808145c1c0e6500420100c14501d0409103401c140341c150440222001e40400001d040441540d074098001d40380c0b009101c18 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 965723732 1250 965722482 965722493
    0xa0216020913211d010206070c061407110c09090c0118080f0604150b1f230310080f0304150c06110a08010602150105060a050c010f0605030c0604150507 67
    0x140301100034050f01108441c1d403568a02128030540882007a103c1c03046807016201c0d0401060310b15080030f80140c000c00000365006024040d00240709004510019500145814030584000c007960305e8004100001c090743c0100d1010490f500118500351800140307070500326401d580c0c03401e00d0305100b8140051413006031540940070321410300805541080710200700c2e60390703403042c1c890000b030b1402d03160742040390580811a00386004920f103550300604400784000340d00d582541c0568540075603a0030410f004a40403041041c0c003035000400300c04405101e50342d05101200b0781114019501880140d0001030701402051404403da40440c3c9400210141c014121034046030340c41c01c10788008000d02d00c2d0101100803040300710040c00100c1c4450f1251034081c0d8a0f00c0d001c0c2d03980c16205502288581038800184024203219020b09940e40b060304009040841c2281c00b582502d040060300d070140f1760b5441c000c1089103010010b040f030392501524078524007802c0207683c0f020007003154500c1d0300713001c03000510104111 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 965724982 1250 965723732 965723761
    0x8060607060525020d051c060b0315010207080c0d1101020f030c0102040509010e090d180510031e0203010b03070e030c1e0907081005011110020c150a02160209 70
    0x154003000c2004540b41c1580c41c1d01803103052901a00d075043e01e10850071100340c0001185d4101c00700a84405080625080139020004000c8800d48074880d203421b400110251240080d50064001c00c026094200c1c56900080c90182142d01c003ca40da07201c0b0301620420740b903011000d151182c00551145c00a008180140d10f400e203629079070409480005000340c2c0030001036001d4000c0c1e0320110340b80805641e88025080e02841d00342c880b515035802003058032468600031a90300c8042a42c02c1c48546800f03650f0400224012296201c44010903128018801ca1025541c020301002006400131410355040188a5209001c001c02503000d210201500c200903a40030848204005401003200410741642c1d040e201109060070b590303074040d015034008116070303a00490b00288039115030384050244610302401110f0f040c14001c2040e502d401440c3c032405d841c0c01e4900081c5814000da1004103011001500c00c201ca001e0010326543c4c000384144003500080c00b405281040d040c0d0100c40228403511800c0c540340005 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 965726232 1250 965724982 965724997
    0x2061b1c0b0603100305010b010e01050f0702010c020604121e05120307030b0409110f010c021c021903060e0607020c13020307030f06030308180303161817030417030c0d080606 77
    0x94004004c01c030307880c0e000d40034200c1030b84d00c1100244400b0040e00d006542d807080f80745036103002c00d40c140110910424070001500704280145004e0355100280e801040c0a9402900840201c02c01c0c00c0e01101417065214801194076201280b17184100c40c01c0e1580c64076591800c2001945180c00804105d40501c281c00001c00c000008000300500046444c0035004034100b110900c3c065a401e036040c00c060360041c0c43c41c2100301d4001d016a4800d0300f2000c13202d03000b06180d0310205c0c0d00180e110f1a00c8210028600790340007540c0b213a0800101725001c0341481e031030420000c00e900c1c21948103c440c2110740d214802281c100703e094804c0582c807521428420750207000707007004001065123090380000515502c074000b6030051030455402c0c90000c6154201c05d45030f200446201010822080c07540070024842c11090001d20100903002140640791440d060702e000c50a1b40b900e216610208040c00002d25005240d032443c55030b00e004518202c1e2080c0d0741c0351210300e070294441c00c0c000c0040000700661120402c0311500f = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 965727482 1250 965726232 965726239
    0xb07030915030207030e03010203060904020609010311070620130b0a201c0504121202030c0a060618291203040b0d0506042702030a140303040302061b1c0b 68
    0x1218101004000790090304045d00060074204242aa90406100b107d0081c44060640e96280e641c680901160f0f61080e51030504040d541c007007540d40f5164400c050050a0311440010403055001d1100c00450454881c05d1001c40404100410020740300d00001c0d030889101289180c1c99003500740059030884500d9101c0c1c420300d46090400042c94201180360b2402d070481001c1c80d42041c0403400100c40f5800b45d13000d00c03012210400904408521807008400040c68507204480c80c048001e40c0c80350424191843c120784d241d0700c40d0014003d08103109200341070200544800c220288140c2a101504504107030343eaa59000c0f1201d203080140c139074454070384511005c0c504580d07481d42d442c0d20940d03055200b580c2d54803495141c00e012070702d1468a070145254081140421400c94842074140542d0f141b00c9600882e0305108500712840081c260a00501c0b07510b5100b00610f84a10749030802900b0100c004060702400e02d40343c141600d072440b0f00f5094a2440c7d82c280303202d106085500110000800d010481c1036071 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 965728732 1250 965727482 965727509
    0xb0307030e1216060c09140904050309040e1b0114071103100203010f0608010503070f1e0305010c0504050909010c0f050a020708031612030606020604170912030a090608100b070309 79
    0x3c10482c64480c0030381c03071407081030100304614000a003150380110500801c01c1d44608180709003140d103020080140c1050054058900e0f00c480080090704a900318601c411203074104100030400d080004801419540081c00c022456861005d00c45038117115080c4020000007110240400f01d03241007154525111000a08540e2540c5940c40c50b08c01c0c44e654400d180010342448008555420086a0241100d0030000000c9001c1d0420210765248486d006604003804200720000011503001d0003003186081d43c5464542d0b0790380c01d002c244014850020903444081c1e04001d100500c1c036921603120f290b525642e1900c25290121a0400c90601580f40d00c000c0c81440085588140782072452008000107114981a0f0300c840c01e00c54003034040c0c481c00e114000c050703041100000c002c5248051005002180b011402c1d141c511b40d0000509041140c0720009210f5002089200250b0b070482c44c0e01d03000e490103040547c06132400402c4a284a00b090140741111840407404008040c05244074a0181025441e000d4 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 965729982 1250 965728732 965728747
    0x705030115030923070602031c0b01050c1218062d070b240117010501030b06070f1a01120f081b060112050114190c0e030d080a060b03010b0307030e12 66
    0x4c803000d1200c041c81658014120b00003003950001049030030b403492002801003c44994400303c1d00500450981d10f05015080051640c01c00c41070040c1300d0140c0810301e40c3c3c0d0b1200300359021039404032a0080c070140114410842607500b0005d4a20800030a031940a8000b150098810014890b0041010003007240f4444410b00014620044030680c2c0304248600c0c10b1194240d000c011500388210f081c0407a0000301540050013254480e0b08020061117010f4801484d001c4240c1d40d0f10792602d01500d0944000c01c0200b110120480d0600d812801405030800200d0700350250740707440100d8440401d004101c1d48001801d2550380d501a00c0001610042d001034544940e558030250030180c28070b000071541075103022201c04d141e64a8061140c09030103040350181d01c0b00c80c41c221070310050000300940c0d03052110100003e80690f40802c80409800c050782e664100c0b07420104910300640354603420031200d080f414401031004482c1ea1098951028003407401007660401c0700b81081c20304451400032101c152001401c40c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 965731232 1250 965729982 965730023
    0xc0c030804030507141e03070915090c1403181e16060216140a05120616020d08010e04031101060b1b0106050d030516052409010e06280204080703030807050307050301150309 76
    0x40e4100d441c464000d000c4113303c0701d005c54080f0317001085040c004505001060401d40e50700000c520407850001101c1d40300e23000100ca880c01c007031010706442e0315078402c0351044441d01c4d00c407011400800990005000e0005201002c0d0800d00700b41c021302160320900020380900da40c9203c0e26800410014080d000b01180086441d6100c0b5030403207190306070903070f241c942e4950790303100090042644a403541c840c003003a420490703c1030392070780054019420020b24042040100c00203120300401801c03030011542c0d580308245d122640500204d402c105090340740503020030060701d40d1048480016858980740c1d99885a90910842c445c2d05010003928900c07070025141c80940c41304034500070b0340c100403070a1080d5503110441142600d22603100c820b40c6d42c00c40d50202e44480301000040c1d41c0003507640c42c00c051080306e002603402281c0141e4800255036000354010014150001a155046241d9251033440c0d480c1542c4003604a20041c4034144402501d101d0000d100380c402e9001da962030307602c802ea00416100d0031001 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 965732482 1250 965731232 965731271
    0xc0c0a020a0f0e0f041104020706090c0806011d04050705060c0708060702060609090609070303080c12090606090c040b0306130905010f0509061501020a0b06010c0c030804030507141e030709 83
    0x102d14403c0c51500c0824610020000369610803940810150420f803141014080170350070100d412038600381c841008100003190b801c610000780200f5002000315601d8031207904010644003090000010f407990510000c900046804d030705a44050b902c0d103544075001400305281c401254001c000d180a00c005100c1031950104506000301e40c210b07450f80381078a4101c2e906071521800c1d9502540c0c0d5004850410000717000d400c205500491403800d190424150210b0001c0c4008210340071600ea0308200c0800c8a6442c06401842c3c2064040b14203a090500342000040e181c0303c09007000703100e10303a1728064803400c4d001d68201c1d0710441d5202c4000d0050490340f0070143c000e02419502040e89000740000590641c02800ca4603d0092050303000b00203544050f00c84504c1e9110140007541000b01030b07400030001c980c0e41c1c0540b00081d0b20a0700d0280ea59482c60070a1802c080b1641c0200c82c4240c03203407202d40c00a42d40c182d82d400c0706103a81c8242400c0ea0b00c80d0b5000900c1c003d0254040b07000c0c1404d00c6502c04d00521800031 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 965733732 1250 965732482 965732489
    0x504240909020a0f18120b09010e0601030c03080d0207060c021c180603050c0906160b06221d0106060c0201030501050406052202160f11030a02090c0c0a020a0f 70
    0x4450181988034401c1d8400d901407034200300005540e221202d0442c40c89040d0280414020b0f1400003004d076218001c0e031916202c04601038440c030440c4014850f030841e092040c0080d403408034024145d1035046560701280101c0c0e5100240251401241d01030000a07198100d402c15648200c0400c8508200f40001e034031a8081c01604800d040c402d03180d2503400d40103e00b4401c20303280850340d00c10380c4c038104001a40100f8014040b041c100006101c680c4440d00c03000014540482400700a001c00207680c5001c2c0c08144004002d98001c20b640740d4000204280700384c0c4803c01c0410708074041000402d620b18620342d403220f1908020f540d070820600062440d080307080d903030640d8000c1c0da0070300c0560380300e80038003058400f184035040d00640c94590340c2e41c40d041c80440055240656400c05483e11281540e480b007149403035917090310a540101c02da40d040101403001454070240603800340171425407680009000c0c080c010304541d1800c01c009005513106506018400c0010b41c010028900552a40c9140c900d24400d0700 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 965734982 1250 965733732 965733737
    0x1202032d0312011401030c021e01020702030102220b07020d02013b100e03034f05090610031505060309071d13030c06020d0f0b09160504050d03050424 66
    0x15004c40700c4d442405449601450381d00240003039015411401d02e0b007403104500c0c990070b55082c06084010703039007030004045000c034100008e803d41c0403408040c050703155107602150094008004810040c2c4404080304041502400c1902c0c0c4014141410110303580344078440140d17080e01c1d0140e81245801a40b01914403c0181c0f403001d000e490110096031035021003545141d260b40f081c070250005400b0340700044003254203000c141c40090201c5182d000c01b9104e82e0115480302601c044101d40c03281c5d1202c007100040200700e503003400505020313022607822a0303001d8200d8101030711000d58140d0f04104440c15070082c200036100d26640c0c5413641030351351142a54000c00700000c81c0284110010740803620700d82d0080c1c0c8412a031380b01403003040e0390075207a00e00f15060480d6a260284140c43e158060341c0b00b40402c4000514007c0340400d149004c000804200030245000500b6100c072026500c0d500405640c140e900686c1c9250080d0560700b81030300c0d28003d5501c651100e064620500007202d11001c80300c218419541c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 965736232 1250 965734982 965735009
    0xd0c030e0f10020d0f1b02120307050607120b1012051b0a110607031b03091e080c010e2a060d0926040608041203110c03070209011202032d031201 64
    0x4c000c1159480740c1058215068581b219000000d07141543c440300c80c0041c0c080c212417800c84265134403410700d04100c0e8060085600c0d910300342402141c5001e40200b00ca0112013a0450450741000034042c0c050460801506a56500009000008441e03200c11900558010b850701d41c40076140c010300c1c251040d41c4429841c0035000c0071070341042c001e010303590500d0701c20f00840b880303043d5401c0120b008218298082d120b8144004410b00c21410441c0e000010b070b80a040740340ea0394a034001c0c909003500c0705802c0c4401d21354820410145e1107692038840510fa00d807012407074241c20440000003140c5000301d841507100c140c41c1a500d40d041122040c840010710b80c4162030002d1142020140c0c00300d90007140700d0000400c0f40c400001b40060611142001c0c41c9100e410b00040105440f540ca82c426040000421081d41c00061500103615240042e140142051203000f100c03031313a4540c042515440300100340005030700707404800b5581c0e00c042858545c50b46550f0003129116001c4640e4013070341800a02c5024080c4850 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 965737482 1250 965736232 965736257
    0x1b010306080a170c1014090607021204140d120c150524120604080d060e10030605071b120306090b1008070905060f03090106080d0c030e0f10020d 64
    0x424403081e00382d040318481c00f0880340402240581c0e4850a680000b5004840100f01c0c226002c0c4039210b00c18907509000310280c43d0592856240041c00781c80a400d40d40000310303200007410340d1811501540c41212038100b00303056020118007a0112501e00600794035461201c0c0711080d5210003012000c40c040c41c40c01c0c020f0441030f03000504450041d15039501c003462101c2c14449450030301c03025082d540009003801409184c0092a141000000c0d203088500d114002100c2c4d110141d0340c000c083c0070b4542e98099a8181c10030000d0b41e000f882036844003c101304d44036000640710354081d00c40c1440c021021401d400380f100c59480d05801440d0700800702404240740040c041003410082c420801c0304140075045c0c0408443d07601040d1035244008003c1d4080201d94203010800b529100c000d080074503c4030b140d1644078100300c074038542543c00d580c00601559100002441c101ea60007400d0241c1075400d030a090f6189120074010a007504540d1000d2500704152407000c05030180d0020384042c407a40c00d42e0b00d44480c0c061 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 965738732 1250 965737482 965737499
    0x1e171305010f08011a04080d0c06050105040c02070e04080c030301031113020f091207080a0302100b0f0310020f070f08070201090605030615031504050f041506270e1b010306 76
    0x41e001c0b0b2040006414500510440d10b19101c610416041040c04d05d0400ea07880f1102c0d440c0c000001d04180c005207000f00c0c0a001c01001d8043c45d40500011181406800032000d0001d40d144400d12035005800d250070042414030103844100e070410400c1074141c2ea600c0d0385a00741303400141d003a1000726005154440700c2548040d114400d41313800d50040c03070310b040c60203d148080104a01c001038410b2260b00a0710340c0010400410448010140e210313030090300e01c0c2c4042015102c1200c0046035030780d010790200d143d14581a40c010a4002d682190480016200d03441c86007541c8580c0241300b0300910f850300c40d5614009002000e8042e003120340c0300366140d034105a25000700f01c81e940000e6807620b8002c80c000b00c0d251140c85e0010043c6a00525030210403034501c03202400141582c0c01135811910740040c1c6401c1c402131280240e0f50240b07294004609000e0784c0e10341805800c00c1b4040d1405514504984c000c9070144900603000806d074048004112000050200340c803078450044aa400b0303000c2864a140040c8808 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 965739982 1250 965738732 965738747
    0x61602042406230a02011e06051804050a03081e04032a0c21152307090e060d050f030a120915150b1801030c0216031e17130501 56
    0x8a8080c3c8901c81100c540780928881d044003400300c1c10b65489001303100c800c045044180200450099001c038100303103008140110703107446219058240c185d034401c00020410004540d2103281e41450205c4007a42c0d2a00030b56088144001d03600d03841c008104c2030005241d4020f009807440c40c0c018507403040302d815240e440c45a00211040c0144080c12202040100c2c900340c544100c640c103406021048440310036038071214038006807484e5016540e643c03a03140842c10501d201c510741c0d481d542021300341300381020100a8900007c0d8803c6108090050700001c810341c035520000f03d002c5901000b00c0d10550300800b900c84e104e42081b644140010040260000b40003203902803c8046a0002003c03a050400c04030903a0180c0001d940c22108a101e60301d000032203008000042200d500b810340300c10703511401040010151980e1140820441d4441c011010b0308820000c510307001c81350301c4440801440d1811107030340d062000b0b89002a041880c43c125201d402c0251800900d543c0d00000661b680da10f84400055901c10b = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 965741232 1250 965739982 965740007
    0x306130b100302030903040902040306060e0708190f1b020d0e0307180e0705060703020a0303061703120402031f061805010b03131110020c011e0509061602042406 71
    0x1507082040070090600980c01150491071010641e0301c1e154441680c0d40507a48141e10444e001580c0702c3d003c04c80800d410524980005041c9000e10340c80c1802400b04420742c90940703441d1f034256a1003445100c009a50fa1050a611020441d280b40480d040c00010b5200c41c030008004020a80381c90701c1201c603203400320300d42082d00d18100051218210080c91a001441c2c80ca032004090b1248017400301d81039641a000c1c056580c0310b9401040011440e2400406440090784024141582c1d501030f4030100c1008000d0f100138000d07441070b05945e59103600003e490100304003050005203d5000207811407901d0368010000303940744407070300c124200382c0103004030219402481160702c07020050021400086c5c61030014508180169501640c00d0240d81c005004480714126070400f40e40400f00704001542c1056400760011b68030988e02032007501c0140301400b1485030084140c03048000051074850140340c805806241c0390003402c108100155400e810b104814494100c0002000441d00020110300c90342c1d070003450 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 965742482 1250 965741232 965741239
    0x60e01050601410f0703020f070b040302010302130504020d021809102d0f060f03290103110c03090108090703050c09070309120305071404051c080409050103080306130b 74
    0x34440403c04500d070000000c1c00b200c007042140c1e010b80c20f03408006004d80700525603d101d0560b07403c0240b030301a140101000c074511240c0c102401c00c00c0002000800d40e401ca903020300700565141c105103d49081c141c4103810240c0e002e413011032642c4400c0301a601a1201554440620004250180411000442c1251600710203c00032906000a4840349600c0306102c454481d01d141d0b110503007005541800094001c8881446400004c124455101e4200ca0701c1c0801d90604001001e881c5007071500c07035900741c02c1c0c00c01020083e50340f40d10305900c07a500141e690b0072400c0101f521025010850741c2c482d8050224540013450280100718018004038200301100d60000080c50104c0350b0030b0a2100b040c600030a6001415903481042c0c010582c00085081110010b603000100740c40c2192000d802c803000d03000d512a0910051209001d141c0380c00ca090310000085804028800201d890000003034172868000c040f440b428600000b04121040e00658015072040b18035800e8950068110300840744855a481d62 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 965743732 1250 965742482 965742527
    0x30b0a290711040e0f010f0504060507050a0c060b01090807090203012d12150213050114070b010509040f08040b040306060b2104110d141212041407050d060e01050601 73
    0x8152520b584650801c0002c1380903140740300200c0312090700719050740312440e2045c0e840341c04010810400e032060640c803000505045042802c85080140f88882c041c3d001000300b9500d1000c070300e490b800b038200200102003c0c4200c0d0441929002c10b5001380d0001e10807440e000c0c40007900d1703074445581784c0a0201c612000f8081145003626102c0c4a00c04248982c005841600c3c04001d40d1820242e036000800140742034440c4100410720705000142000c407a90790103255507400b40082000520907040c42411120100c49a078607503140c908044000f5001140010a030800009001500400e240c025104880c0140000c201382c540d80d410340b82252040f088807410581c0000000c0d4000d40301c074250140c10078010b66842440348034070300119451145001d8160707084603100c42c9840e00544100403000120501507403490070440304914445c03501ca0050002422030b0541d54130f028114100700a044001c003002488031208100c60f09240e0000c02d1080b000e0b40c1c040d401e280004e0b031554003c24840c003000d0310104100d02d = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 965744982 1250 965743732 965743763
    0xe060603031e090a081518030d052205101503080904021b0f07090b0d021012020708030a0605180114060c12040b0910090b0712030b0a2907 61
    0x8800314800c28107611a101c0038001000c0d0b6884e00e002c103002510744200202440c246008a010303a9900c010400d441194240c210f81083d030030044143d428203400c41c54045a9a26049160031410882440c403810b01b0303141a03c40e00500c5800a04c940c10340ca66400100f1103c9500059110380702214000902003510403c03d00c1100e08181d4010103e80488000d42500003284004031801d058841c0381c8186140e00608007030051440034420300a80c00421100c4a0f40390340280c2c08a1341d2800b48550070001e2003842113081c0700740319880d0100c80419030b1041f00940d580c0351284208000300000d006442c0034990003600d80580314048401036060310b50024490715007411203000c10000394890711040315903020b1000c1c0300740907000080190025024125030592100c0c0c280c0c0902002d554481400400c000040f0000c0041c1008030044a4807550028514142884201c03401d1b030182400b80f00d00c2c1c2d0442001c560004450704400c4203c44174211014048010001034250408540628000600703201c4d540d42d41c11 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 965746232 1250 965744982 965745007
    0x503060f0615270402190201021306051201050f0d0602040602070312031406060a050d05010e0402150a050414041b17091204050f030106050d1a07050304030210050a0621060e06060303 80
    0x2441c0302000100050f02c6d001e001101002807811a90094000d07039008212602c21401e076841000140401e031500e0350401c1d810b080c250303d880030184501c6004071412a00c411464032010486140705800441c155a142d40e0b6140c000d40d51280c6100560f003050703841e030700100014840c3c040e98011084da105244143d46501d81044010744c001c5a4480074001e0130000c00303035100402d000e00b40c0203044600c03001030b50340b5080c0144410860384503101d4070203880411508405a400000b9038064500d10003681c0030703200900001c14020a0644998030b940708000c003480f0542c80d40000c0055010020b01c0134503505442e44c051080d0744d4131254194660304c810600042c00301d82407404500310006001000401d680340d0707c401180702c0da000000c090710202101d00402d0072607a649600c40340c00034268a0718901d10f25050f00d00a40340c40c0f0001c42c1c3e20009403103402090705a4069001f50000d071060b0410141c04031990400c070100d407600148102c84403800d200e043c0018a4002c52460f1048a014000d1454050566446c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 965747482 1250 965746232 965746297
    0x80a060c08090a032d0e0a0801110f0306011205041515140d05030f19020c0f010c140c060d0e1c08041b0923060901030c0902070c0503060f0615 63
    0x40a030a031008000c4150400503080001c07201c1d4102d4035070200c011b40d40300c00c1c031400b1921034000070126814100019803c42504e804c03039442441d140461034034bc1e103c00c00102c2d102e0791904801d24a044c14042404140030313015500d01c00c0c895441c2d80c10041030003250744180f105004c0d07100300e0b644d910032105c2d094503604110350f50703120303481c803410a4030302d4420003942c038036234542242001205100d16080b461038800d1b0104034004460a089a403480c505031500002003600c0350340c40d002003003a003141400310316080040001c0640500003c0c20746445016a1000c1401410902c1c0c820000c0d1040c00c08101c104042d01090940782106035440c8a400c2d1703038940f280e00c500344101e941c08101450401c000038090b070701445000040000800c40030301d003401e0f1041c101d1041e480074002d248512248001007002800c1c140b5440e0441d0b045000c0561070300418100410000e40c0d9610007500350188908026020b09034070200307441500101e9400d5460000c010f12501a030003484c8000441c4102d5008403800485407850 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 965748732 1250 965747482 965747507
    0x807030e0712110607030e100c050c0402160c0e071d030c0103050c04030c0803030a0e0102031017070815010906062c120d2001090f02040c0e0901080a060c08090a03 72
    0xc2e281035842000c0701081c3c4d80c0c0e0240109030001010815070501c0c602d401c202400c03440b0707403a01c0c003100100802d84030640c40d442c001400394450340d40010400401c2d030781d0314440500950003c0b48075200c030759903040f4600d500408540b428005032003035014606003240c4596046103100c02400414000c8641001980100805004a014100c06000000006118004c01c1d0003a265000195441c1d00b0152082400c0c2c0e45807101070341c0564014010850881d8016212804071908008049811180e4105e400d05081203600080310ba8043c0c00351b84108400030344000f9048418403502048000c2c0da420044a1486413030b41905050300703218101242c03a8100d0402c00508102c01031294400342d10303c0000da442d080a0708540008540da81d10444000c025043c454050030085000912100001d43c1d600110180582e40092003a940da00c1103080c010300c50300c01c1050044001d0409415035840700511540e0b445a4041151018100f094540c240c0303220f80c400a0042d81d05a00130324000c1c1d819034003030b00c00aa1030071 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 965749982 1250 965748732 965748743
    0xd230f01050606070b041b050901270c0c0b0a1d01060312020708031e12040f0201080609150103051b0f070b13150207020f04110a02011b0206070f0323070807030e0712 73
    0x3d00403807603589e0b084095000340700c074411038a40c810390340d8034a000303645510b040700900d503203406103c9110726000380c07040d040c0c580c0c0a8802016652040c01c070800414420744101d2000c0410400d45003642c805601038420f0780d005042600100100c000200d942d242d140c0162401030300700781701c5100e21801c0c400140f41e40049a40300c031810144600380c9004111011a000c1d0341d8048284621010344d42c101032aa40c010070207413401050303807a201800d044a140c1000c0c0d0035041555500008809451403485005901c10603c40e0607590340d080b45500106030003820302510440354842c00f08000311004030490180992041c03035001240d401c40c0840000b174010000c140c0e00b004060034902019602c07441040c140003d02c080140c0c0f10041c20600070b0031a19010801002401103d032010380305900000c49503841034440c0780000c6032089682003280940046801c007000c1c0d030300c40340e0b4011303e103040da0200da0f20901065881681554583c1c5003207003903655084048155802019062240d0100c050340c8494143c042d4 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 965751232 1250 965749982 965750033
    0x1519020f012706140a0b281403030c0a050c1201020307020a0809040b1801090f0915020c070e24091603020903120301030b090c09150d230f01050606070b04 68
    0x8002000c051001719882000d480e502c50884046140c61303202d0101c8441c0c4d4400004010000e0040600005003c2c0151007502c5100040000c041c0d60403c200d840c41c1021006840051215140040d80e41e03102c40001c52065401c02080d00b60300a05209803841101e080e401440c0c624170903180c1d00115440704025075000740c0c5416850406841e80b5607410001c2083c03080700d00c942d624119a60003281c40f0001c1c68400941000c0801c000300f00584181c008030144240010394500403c00c1c810b180840139800032884480500c20801c0b0403d8001c104a02d0012030034016a0002440d000c0041c0140f04650103500d00c03800d141410901c52295000d00710f280c00c0a41244c0341d4903814444401281c00981c400c60b5100262010800080d9090104000d5003006035030501072400c0004944200c1e040200b400da000710760b0f0000f8102440001d06940e5810340c4c0c102e00d00b08110070144130158668110016602c85582000c000c00c119040c03140032101c04503044001d044e5640c9aa03900c41010300f10010074843c402005 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 965752482 1250 965751232 965751251
    0x30a0f050702100c0f021f060513020304212f0f1606020c01051b0c0913120e01120e010905010c0504080601051e0f1519020f012706 58
    0x144500c902400d025001060110f503101c2c1d8240581e0880481c6030704000b10001d81d108207030b400103520401c3c00c80e20054030520b16103524104004111551103a503000102e01d240407803101041c5d004500560003200700300c3c501c0310100741580c0032250f01c03034000c800038544a034121038034040c64000840503d0204003410590300c0da240540d10384508114942e00940100300d0000070080c202d4051801041e603030001e00700280c00c075030001c0c0450044e0010b00361207030b4244a990a48242c10701045d0021078000708400703a2820510000c2e101011a201c0c22a00c0c40421140c03030700168020034030704149030300503942d0700c250704000e5052801500e401540e40729159255424030000800038000d905409603c0c0d45c3e01e540325468015450300e81801a48041d01420b06145c41c0100845210346280b002d100540d940303034158603014046002c003149080e40c4070b00c031a0041184074148404121085845000394202da983c2c1050404803800c0724180c8040740c0745048680f040740d5100c0c40ea80202442c0728003035000000c0c90801d = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 965753732 1250 965752482 965752511
    0x6050307030b12160906080d0207051507060f0f0b030c1003022505030c070f08030a030203191109031b031e0a0602120105040f0c020a0b101a090102010e03070512030a 73
    0x16031204c650b01412180001d201c000f202e481410b00501c402030041c80c5141c3c0450001e5291003950003070500644001011845810544040b12074080c1c1c0700c1820054641d17903a280000600c00c21030700c40707103003410242d496000d85400102c407014a08014180300b450007824505900170740c02440304900c1210200c60a14640c48018451105680a00080e41d91034640c030040e41c2c2030010607000451382914980040c480c0c10300c00405e039008080c81d401c0c0142d403030720340d400c4003844000b0350270020300c103181424414aa880e024030090220000c0c1a0221070843c44074541d0ba01040080300300b0300303405a03c6101c524408500d000000c003400300403502a210740100646605081ea801020040a140407001c0108a181007500c101d803168580301e03e0410040806c0f440003512980009000741181080030041940301c0c180d0900701d002020095501c110031031242d110341000350400741005000d5442c0c4406240760150100807030351856032210281040c2e00004088c40041c0d04068074200c0078a907208410840a00d = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 965754982 1250 965753732 965753743
    0x1210513030f0221070c121103070602010b09190902060a0c032a1112010204090509010b0603040f08180901080f07151b060b040203070c03120606050307030b12 70
    0x1000c441014080e0400350401610180c2c440e03141008551003900301c4101240200c801d050f04111403c2426961405810640e0000d0b51941160f8489008500680200a81250b12800441d0140d06070750481e40c0c0c400050b0b080350180d022190b00040c0a9001581544102411031040c9000000004c0d0745101070b000301e41c6580081346048049540f0507240303000e01d5000810300107180301c8001034251782a4100912150041c20b0a801000c8c420100301e020004e6940302016044043c1035402152100d0741c580700d4401901c1d098038182c070b01e0b500c1d01c000360140703007041c10450f48a55041218141ea110320b6580c1c2d2895644980c05260a40c1a5481e980d81d081e44c42e451200e000306420070041c1103481d5015260713030404070a903001d981e030340c60640c00317540742c41e50410001c80c01c02d40300240c500519141ea06055000e02440303101c0b107030b1103880002007101e00c13a08588a0500341303000c0e0b9a041c0914803c11003410440301a07005100c0030500910014203014429044508400b1300504100d0250740d03100507507485c00 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 965756232 1250 965754982 965754991
    0xc0303021c062c0c120a0605130906110307171504060905040201030f0905101e09080c0f073209090304180204120f1403160c060e010806012105 63
    0x1071209280503885120042d0b00c85901d0007000880c0e081130308100c0c42000991040315a0900c0c07007490320f4006a400342442d8002d100604025000420130680242d0306401001c110b1403c40c0d1052400500c000c0000145040c1e81c0701d03131030549402d0100003145801c032001450041040b0341c4940b0769040c0c58070351788413809006c009080d02d078004500ba00b094400503095070440c5002d0710115182c0a0f050000c2803002580c0d00d82611f2110f00000c01900a00382581c3c40b01452007151402800c00203404200a03c0c0001000515140800d4400c280050342c440e036110003440c8504c000005410580f90b009400d030340081c0c005142200d00b88068200b07140007080c0824012104c00410340c2001c0380401a5600c142414102c0300b840000851a0500341034059194500124018044128079003075001044500c100b0075030301c40c01c1d00080340e449540402d1099400c0c0a865000c84801d4022440018030500610241288890507103d0100a644140044910903490100c400b00344110507400c2c80340100714031489005 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 965757482 1250 965756232 965756249
    0x50f0d141b12061b0c011811090f01030803010e270d1803020901031e14010507140408030a0311040f062c0303041e03060e150f0105010c0303021c06 65
    0x144480441008034810402c4600c6200360407030804c20001d18050100c03000c00300808207070745460f03d240c603100764010544d020780300004480018162052000059082c040c2c0281105c1d840b6081e44d41c2540b420390300d00b00703101c020404a400d00051007210007582225920800b00a280501043c080c00307180c1003650a2040c800098000e4890208080e51110f880f042c1441403011900340c5074659030200383c011a0502c00505000740c0703803c180601141c40582c143c441c2d6000f5400740b140c001034a0b1002d00038803003030b66480cac0810045445061520614800c1d00d04803259240a0750030b16420a600b9800303000c0d01145403405c0e080c2008046480708a5070030000190090f95074896600c1d454002c2c0107403c084074245070040030030001c01410316035130000441d400d03030340401322202144440f0410120742805a1304020000340c28298881c103104800035490307691040f03020002c10141c0382c2040c0c4034081d01c000c0c020903000455084138480824041d80041c0012080e0140c1c0c1d20781d01e900d107002c0008403403894101d810b5 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 965758732 1250 965757482 965757523
    0x180a09020442050a030507052a030724140606040608060d06020a0e010909020c0607051b1027110d08040812030403021203100905091005010801020a18050f0d14 70
    0x700701e0749031160662020341410014501544a2464441c3d1305e02d08001c0d0140046480d01358a89d00300500946211507030005a03010750440c0907000c800140407045000702054a0482d80d900741030340e15600c55005000140180f45000c0c10031804840403400103140c15081b20040c0d1030b000002d4090700c0104111959552080f00074079901000411900c00c9a0040b00c6450061010640f80d003400b00741c0507048805410040c1d0307682e140171034118214051044144950160490001c000181ca800a00000c503804810b150650302788180600c0c50481c0600142004c2c4802c030b03184100f82020781c900f20384103000d5000d003801c00e03544415007886c0005200d1810001e904c08400d100030550104110b4032141b942125503815403810800c4965030704860b220789195940c4030740215035042e0051000d40610440103600780260340e11000024086e61002c2114400240c4418803440c030306c071382e980580317050700c00044c88003904920181c101720250180c1c000c00e0712400070000500789800c1c800c0000803042c000740c415442 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 965759982 1250 965758732 965758747
    0x5031303020a1211010b150a270f052e0f1403090d180e0a09030306091524051209070e0f040302070b030c0d1104080102180a0902044205 60
    0x5003502c5540d1031030342c00340080c8514405d41f106110b007620145501840c1524004c08980d1b60800e418030315144160780b040380d201c5c01090001010552380c09658042da0318094040c0c514901d840407034402c104018014494a0380030102307900ca1a61099044490714202c801c2151128440c1c1c0303140d10035140590305600c525521158160000d00050070740304025010081c0f50300d492000301d0182401450303000020b5941d42e40c00c2c201402580610003804040c22704008403400c20205604201320390180d1400c101030340034001d00b0180c50704481d8040b2038065641d2410200c14100140c00c007600035109510a006002c0081a41c1107007014491051540d2050507416050034103010781840102d4102c3c1c5c00e1302c1020409c010a088486048642c0e0764246980090b0400c914004806c3c03500998100c0c01d20341d400001c5160704070848503075115130a0021184107202a5560803d003049100d28800e403800c0e08402248102c40d604c0c11300103000d03101c03402803078030100c07418010012080058503a51030700803036800310700311 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 965761232 1250 965759982 965760017
    0x804080d060b0c07120c120813061106060f010c031b05030c070e070f0f081e0a020d291c02040c032403050616090e180609060705031303020a12 63
    0x14401003020002e412510310817a1500c80802001d401a454040c7c0404005000c010040c4201c680308a80c041842c004151124001000104480003401ca40d01c0f8004c04210145410311290300e441c4070584400340e191116507800da40315050b4034404a40c04001a0700038010400602c0140300707600b03041c00076119003402c041147c4c200e4200030f480704082040030701a107840360380c102003169407003040380c28940c440769078004074258171240d20002c800800042105102074403060707401074040c50455000a1028000d58440714040c880050074203c1404e00390261011a07052140315000000d4000d10001e07800150f44d004201038800d50448517001035510750720031980f0002c0c00d0103031290081300810100c0240c40d585035583d44038070142062081c42908007500c4815405030500400401030744d45801d505180c0380401d000407189482d42c0899a0058400240f10200e02089062040ba02a200c560841e180c85d055156503000412041f4158032038102488040b4485641400080100c0c0e59820990156001070 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 965762482 1250 965761232 965761243
    0x30402010f0804150b13141017060a0c0908030a020706030b0f030d050a09050405090a0605010e0123040212041103010c02030a05030f071b1407060504030201050702010804080d060b0c 80
    0x1181c20442410140000038080038110900c015480c1400320f114010100050b400c090750705500e118070392401c000720300b00c840b4070f1400c2485035205095005030155550307092a40345461232002c2980360800c0f40040c80c0da8510341c1c08480c0021303851500d458507540f1207d00c0703131a65001a4100c0090307403000c001008810350601519038880b20a8510040070000d85010943e030f610244480301c00d01c10f01180c210080b5114000c0302e0000c2800402c20b000ca4204240010740390011a03c0543e0b55500b0b00e000403680805c2e01e0110782c1280e10070443c281c040c41101690b2140c0c00c0071524540d1740580c00300024005409002d0307407540290300440c0c401901d08070b10010542114a10354a41055420502c441180c4c50f0300a400d480e4003012221004002c0e42d0b030b418045903010000c00300038251044030b01c0a402446010802001411090f80445901d25281c103400c1e070b0380d4019441b00074000340c010407a0600551141002c2034119110701030007803c01e2000348210069440b5030700300003415040401c141070003003001c120 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 965763732 1250 965762482 965762507
    0x702040c02120409051911071119030303020d18051209010909050f091005010501090611010902030a0f1109060607080715020f0c121e0304111f021c02210403021503040201 75
    0x10400c0a61507c01da0342140b8020030101a1a91300b18400b0324406444600144910010b0038801d03103180d60312458064020340002c0711140c1c0da10710740132890842c0000200c1442155810100506444a040c40d180b44264000b4012504010b2a12130003c1d0450701c5006c1c9500991240e4088440ea1809017102c0d89003489007407100c255941040b00411169800610f407206076408e40c03402a240c4414034078075030701401c40c840000350144104070051050110920300d007010a446108682107504680e0100207030181d090340c0d200d0b800b44c4200449000102c08030000c2650b10710032100d4100c92030000280d40202e8006c11460f002507000024403505114046c800355000d940030341d842c030b07081440d95542d0301c800209520b043e42400c44000085410311180100c220602c0a000701025824085c0d4200c5007440c2501c0c911000c050300c580f5903401e10b80300000b203c2c12059440da90003080e42d004410745285001114091508645600700000320260b260000c40346034403130019001e182c0d0707802d25100040501c0c0e0000c4 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 965764982 1250 965763732 965763781
    0x41b0e04110a0c080927130506011502011b1110141501090b0414090115080619170307050606010f05090d1a130c05060f0702040c0212040905 62
    0x4240100740314408240c8080d50842d1925004102d00703803402d00254480da200c0d4544c041000908070340050040040c0e50a0031074844100e05850300e4160003a10b1b8003101c00e2004001d904007000511425219803000030000b1414400400c4403503401c51003400e0b145e0240e00c9000001c140c1040e44041c403404100c61003c1d00c1c0440010440c0c042520111a040040545221031284903045161426842003210701d0261050007825695142c0d6013000106180000316a24000d1066000015081103091072164904080b0f442d410844c0d0380342c00403c071030b60500d0141c0424a40000300c020818000850710140c503040580000c0da03039114a070030841d144c01001400750381008179501001003125403090a0300d8100070142d9417201000c88070300c6c042000c2a401c8104044508101c420080c00400c100040ba54050007908008000ea48030403c0c8003462040d2210440018010000c000050401b5400400c90700000d00c1a1100307120011440c0c5101e07031089d0b0181c0c10403500d40082c0301207411045006da000220b8103 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 965766232 1250 965764982 965764991
    0x91515060f0807051216141e070203010e0615010314090d030b2103030a050a1b030f11071a010b0f040b0306181e01051c1203060302030f01060f1703031305010b041b0e04 74
    0x402380422014080e40141d0007032030080b03620300c21900d00f5001a00f140411030f090b11014070f80307007203094042d80c840c05c0c1c0c0d10f00090502c00015120441c50b003003070b40921641400341000011009043c0c0107800705680094000da01907801501001d600c000c211498410f0002455903030510700254419a0301c09006070f484c05103881e4100269181541e04414040d51071b050203d044480c0301d480c0f030000c7c41e03022151304141c140001d02c6410401001c1c0a0714000741c20384009500c0366201c02c0382848502907119481d412440420041c09584840b2002e16405440181900c602000c1211140d6101c9015103600f9202101400303e804412016048940580010b4500c400c0050030300015036440510031034064004c1000802c001152407013500048095a00901150543ca9546c40d170940281482d100e0b81c0740c6003a0340c02001c12071504003007202c505407500c03100450450301c4034281100b561403401c808503078641d07a03481d180e101902c40b40039000c407080080d4400c442d52506024090000ca005200c07580c03085180 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 965767482 1250 965766232 965766247
    0x150212010b0f04030318030b010b04031505010b090402070c0801090311060a090b220c03050d031d0a0210020a060f0209010f021f05060a0504091515060f080705121614 73
    0x1580980f01100c0d094030301010b0186020105000c1c0801d25000900f80726118000402c03402c14400050085030312500c07400d190000c5a1030f9100450740c0a01807141c0c012003c006244981c0742c1600a04a0302d03008254142045958480c2c690031100e000108401041101b41c001d03c0c3c00c941030005c2940f00241c007105100392440d83da207001d48200f00400301145c3c4100c01d548a105c250110f0388210501c1e0f4002d8480d01d400b61a820400c1d55403900d00302e007100182c140700080f03d9590703852a10711342d001c3d90700000b840b142c5403035800c100c056025074484d1002c500c100100702c40490181c0c0070300b00314541c00e030f4801a40d4504c4440014501503041800509560103100d05421025a01030440e6225010f49000225031f01c3d00310018a190900d0350195500905080e00c98080c0020140c034101d01d103001800412160700c6681d10150005214800c00020889480e2500c018034001c104159002031180b60407490941e580e02e00003c1c6c81c00030b44500011140c0980308603040317604000c1141d403c0b40108081810245e0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 965768732 1250 965767482 965767507
    0x503150106050f1204060b040e0a1104020c120406120506012127060617060408030106050919230619031d1e060c031e13150212010b 58
    0x20600c558010050700003018402d1441040c2503030080e0612400346040350a06041020281c502c240c5a00c0c0300b1b92510000500078000040d0071080183d01160350005000a070741000000d40102b240800180a40c018160841c000100108040c0002da12400344040c44a01e00030200d400050215041c0406950b00020b813880510b46045000c44007c000715281488210001b46c0d021800803994040c3c20031a05642044819003000040c0c0703464200d03030107074000f4485115035181401e039030281800d28200300600c034552050008180c0c041c006415104400600b2020b030602d008664000780048a803503030844051039101228155031241101c049042041c46400c03010301c202244c80c20020326075108007400c0441c0d0482c00b00b45808030307100d056680c06130124141d12403501210100e0302050052400098000030f014043da4042c07401c0700303814600c85080c0100511400c2d400341c0060b0340342c41d0400e40c04002455000100090702821130000d40c644047c110402c880710010b8020b000d00300c0d010301c9160804003 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 965769982 1250 965768732 965768773
    0x302030601081909080a0c170a0519030e031306080702070501140d0b120f061e0f1e240103060302030309041808030109060312020309031e25030c0503 66
    0xf10030403004401c1c121000c002002000000c20003000407502041d030b5007815802a401d080b04a000c0c00603842c5122101c0c0340e07420f940c4106100340c00850070074005420141038051141d03050907c01c0c02c00213107a12640c841e0070700c0c5421074221400c8000640c0c1e424845140d0203112203400020714001080c14a0a1800180040c03001d0a030a1441b402e010440d003a0742c2c2501d4110344140c0700098404160160000f0768142c6a0100d10b100221500c2000d010400314684001c9403100c0c80001103191020740c5842c40c507070301c410a02418000b03403d44c070f490030703c450201a418014000c2612100201113445004190f002d40305040401e1814140b03040020030150f100803080301d140703c2d012640010300015500e103000c035401c080300000c2d2040c00302000100b07000342168421016a801404091121090000202d0341d80c0b14462115030180c0226120b540400444800b0b92201d1201c0005d5031588004510003140054000b9080346070840d0542003041400034545555000d440d0170b0b0080c211045a0b209808940e0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 965771232 1250 965769982 965769991
    0x6041a010c15060933060804020f040f0c0903050607090e010911040f080705130506130e010b03030a210606020d0f0c080a0302030f09030c07140a0e070c0c06030203060108 75
    0xe40c04030a0b810342c2680c0d00c2d40800054105900200000c0d04000d04052081d800e04243c0e0112400c140b00b12041c008484000300225495079032460960b581d41c0d030901c40c0182e00350b50425080398460038074400104040c000d01241403402d640d20360300c03d450350078003138940a8050030043c02e11260060600c0f01203000c409081c192015034201084582101081407803074030680c0d2007815001d05089010490300340128216045580455080341c6c0803072061003030000c645c1c080e240b6503032207002003801c0d64030211785802c0391034a81d01c5c01e400041c40140740b4005c281140d0101404c00f0008010f4016040d0541e240c55101c1d00b03206000e0b004210040c10700b4800b81d511900c4a6106c0306000e901c444080906100340b00c0103ca455203e2040ea0303d6581e8480003502940040d2017a6a405c03105200050304400d00105890b194000200288181440c01c1001702c210b0b00c1c0014000c0e00410044000301e28894106981c5000e100d6550303a00d608081e60741804055040c03141c000904060040060084683e030140c1c20a410 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 965772482 1250 965771232 965771243
    0xc03020a17011104120f1106030f1005041b030b1305130204050903130302120f0d050c0c01180510030905161a2a03360102032502130f020306041a010c 66
    0x8858041c1084587e03454080f00c400e901140000802c21401c03c03010285000b000c69a1190000c80e49036410441950000176240103070a60701020301c0a824840d400c5640d80c007901500482801d040c80b440e180544104a0300c40014421510b007080c11410540b03d2903a00203501c001850804407040c410212003140b511010380702d01a150030105400406000c60580d0703c0e0356404441100706922005003850f0000d96200d441c502802690031b5095006054000000c50450649410a8101410024880c10f07614080c0308065030b64403580000b039801c01910790941240301802c3c030424600f82d0841009050030662401c2100d0034441104100c5008900d5903107802100e1148541039140c0755070751b1443c0142844519500c90702040d000090514030083d03861000581d2603100d400c0303032140040e40c0da4402c4040c440c900307009000400e40901c1072400500402440140002d501c480e05100c1c201c1035440a08170010400d6002007400341914052180702c2c0341c2401490000c80d047c4003940082d1058900080c051308 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 965773732 1250 965772482 965772503
    0xc09120f060902010908030c060105010906021501090f09171e0f0d0504031110050f0a0c02030306040b03120c0d0e0405010b03130201020c040903020a02120601051003090c03020a1701110412 83
    0x844e070060400d0005840d10314100d07a280c000c40b08602c0e941c1c120070b20030f05003c92a94240811810310110b601803401ca43d00c810b0703400d41d07460b200b03110000384280d07081e11810603502c55a0344000786c0340c0b07541d05c81105100a8500c3d1182d80414000010303a00d00ca071403941c094010400c00030350061140644000219a040000d1550303a00e007000d4558002507940a5050300500301078440411441e40198018031048031041031a6413225080700071118018a0030740507074011f04c00030720b261401b40c2110085002c060300340c98000030110440b220b103800c2101400c0d815001818520300c032680c0520030000c101c0f01210300b80b1495140c1810840303288000b0f02603e011014505501c0300b5a4000c0000e1000c0780009002000060f08a0800940300c080c0040c0c200c4c4070f5445240d002400d41070004100d4144c0b04000c0645c0700429038001c081c2d00900070317140e007103031044901c031000400340e5103e800010051448040d1038688031003110340c49085a9005000305e0442c0024030051012482030910417200780ea0107207600b203 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 965774982 1250 965773732 965773751
    0x50a020d110a061d060c090a050f06040b04030b090f0a1a060103090c0b040602100c02070e1b0a2f030d0b06040b0a0e1e09070507110d0302010c09120f06 67
    0xc1c1402c800c2c2030007070000760401000b02120340130f01e44400110420f400a849154589500400d41449841802640884000c0c41403000740741c400c945c0700039804003d150743e00d0541d0318020b10215802c9903009440840d0f2200c10800111030521610b0180d01410700900b50715495076a8200704c07125801500c1d106c000ca50000a00584d009602c0002c2c1550049103100e40b5a031b855000b0300c5540c2c098042c40c070050041c0c01003e0000401c0340203a41c00802c81d9005408850305007440d580c001c0d03400a1080391440c0385465540916a0301e01d0060084101681c1c540007800c8059000403110744242508102d05110345135a5520000d004c800e440100501e41e00110350813001d100001c0950185030001c614051b00000c0449a283d0000460816008251100e0080005802c040802143d00c404a0303600410f4000c0000d1215110300c0042c4a03592052a1080c0ca4151030360119180000c0140c088004d40e40d40c8402c2c030030780c3e9080218074005006559203401003680590782c2ca203158480a1005184c43c1d02ca01a02 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 965776232 1250 965774982 965775017
    0x50a0b060d0f080903100e0a0f030c1506052d10090306050a0507030b0d030207090c1b03090602011a031209061c0207110a061d030118050a050d050a020d 67
    0x30501c154110b030250110200504168401c0e40c030070808184248662201c448103c500c80c0905d0203001010000351811100540f100c0280703203041034003182007018000380303d000031303a404407000d56070202c40200094003030403c82407041c0007195080341c00c41c40d4149001c1181c05141c180c001030300031030b041d50300954500440c4005e4500442c0d640000704070f107041c1410001d02200b1644040d01c07030f4106940c04d110b5a043c1c00244800c5030744169021300180c200c080d044c49110055044500040882c1c40c00303013101c902018021181c3d1b40f0720130003200000c214070300810100d68240115020b040004140703000b0f0550345000a541e40f1242c61b110030b10000d02040440c050741e205002d85101b0b11403417400103c40408021128000d52005c041111421100700c2c10910303a0808400c00030580342152a05c584c0448402d1103c12082240c1282c680e1564039030042d0942900c003610fa10b82034074800c00042098140c0c600d0030a081c12902242002003100a012140b980790f800181001e00300041c1c20311080010020516 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 965777482 1250 965776232 965776249
    0x3020f030a0204231f200f010b0406030b0406090f020a09050714030106090e19020406022a090601030528021b060f0103080a020102040509010b0d0506040b0f0f04090519030219050a0b06 81
    0x10710310404602400c00c6c0c04980105030819100c40a4008024180941082000f1141e007800301505200702d00d40090005038107035001c00c40d40f5003e2140c03602011150f40c00a00f806003990405411507840708207020140d40c01500c0d00795520a0400ca82d401e660409034001e120122920030003244035903640109a41c11062803d007284c940d030181040d5034964550314003035552541d552130b900b4032510b802c0c042e040e0405c00d001c8007480f85e100102803500c503480300030045000e410082c2416840c19241410780b806a0803510b0010140d0740c0c0c07190050313240c03124000c1c286c2000d002201140e200d0b400100030004180420400141580d900000c02d64480b000410128024004d07904402d4001c1361100002c2100c1d03020001030305038a0350b901c00038000d1399600418031082d0303000c10b40003540185200c1e6000820386401702c1c0340080500040c0001520041c6620388a2810310414059400038648100c50400d140d41071024a502201000705104141015907034030380c0c2c4a0300e10b240544a42010000303c0c101d560740000 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 965778732 1250 965777482 965777507
    0x6090f060d060e09120414090c0d0c0306090f140f19182102070b0d3308190809010e0d15180804031203020f030a0204231f 54
    0x10005a80c541044001205003030b079100010b8030585034024007017003100c021101a50f40204d07142c01c43c90924000e000d1180c001802c02100202c00f4401d144030039030244900080040e188d80c020800a250040300c00455540c003c03641d078032030300f0540824511a9009856074100000c08240180c980c1d61502d14010250161031200c0c0c01400c0c0010700020340160540110254000c51a07445101c007841d402d914401005010000503030005101088041d07400405031803030088881c404216001c900300c108801c0006103442c0c008030356044130b605448110100508000d0083c0f0740040100741c40318003101135840060306004007200d00016210181b40d00c502544070f480d8501802c903140034051480d160300e0043d280d10f0740344012494440080010032013448035032802500009114038103811521032842d0300d1110000d110503d6001c1141c0192000351130015882800c1d032510040e146e504050341804003601c2c888984550100c198152503056a42c0c1104c4011101180d01180390090ba000c0180c850800c00785 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 965779982 1250 965778732 965778757
    0x510030b040f171605011a101103040b0a032004050a090b0607021c140c060d0504050102040e1609050901050604050402070204060503011a0312030103050703080c1015140f06090f06 79
    0xc483c200ca14100d9210400e580c070410081c001c25411041030207a031f045080195074031801c03042d9413069150045a0b02c40764071500409903850542c8031400c408165004400030400265151004034103900e07d02141090742441c5000349140614100000e4200b4800d40070b05001d10b580c400e460142aa10103003210701107035000c1c1c003c041d003243e0704090342000c242d814001d0350799641340007007119120030116101d921604000c0c040d60a03c4481d1201d0001440014822207084d0350800001c05c00c000d00c007503414428801c2842c04545178003080c000400c10340d01c2d030388071900030901940180001ea844a061383c00b580c50589006840e411310380001070140c4003e900040e019440e1102110820701d00354040c2c8041c5c48107404a610088cc0c409030303a02e83d440709202c00341040d04059020f0001031400e0004102448041045400d641e1130045180100d03442030f04051404000c0d6581000541d5400d500714455160071181405036010300d0000c40da0601c01d0900181c400e45801900e021942c3e07d05040e5104880c0d6170 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 965781232 1250 965779982 965779987
    0x4051b03180a0305280203220503010905031c0b01020601181e380909210409050a0209030d052a0d03050f0c07060b01300510030b040f17 60
    0xb418003a0055200740c5c03082c600724142c2c1c01e5211000440750048200c8a4542c1e0055203401020780c91504405c6c05502d0b080546100100d001401d5542401121241030162001e10746e602001c02c1230b0b500c00110b03012450041c40c1803250303a10f0f461b0f03004104141150a0b05040034401c62080b070171000285a180344502d20f08105c0300f0440e00012180d40f0503201c4014401c003095404111940040350209040b45024a50071b4400d41d4500c181001c854164119850000f20b0700613903001e503240d001c42c42605203c07034188a004030301004903002c00d001e007a030000e0400da0110310f00502140032a440c0d5404019401c10301c500003c4404880b44140038000032540361003c01d04520324040340b03542e210038040002c0d80000b4148004540c0c480021601940104000d080c810325141d41c0750b84020142c410041580c0c14042404866600444416085462614410704125480184503510011190301410f15a03141310f0125003800041c03824a50641c00640064050321214801d1a1080000c00c102601c0c18510502 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 965782482 1250 965781232 965781253
    0x8040201360618030b04080c03130b0702040b181b0c0f0102041505091c02060f0a0f0305150a0b030a020c0a050f060601230a03090c120b0604051b0318 66
    0x8211004042e10840c2e03442c144070f034500d500b00324200103150101070500007a001c04140000ca001c40141991201e020540c0d060003038404e203052158090354041440e1100c0005c1040c11842c00b807140295000c81182d01403154410b0131041c0c440d00c10010019090541c0842ca0200a03010003016a1070902d4080700b25007100e082ba50b02035000c2d4006208020400030b201481c0c4410034020019a01075080251102d90300381c1152018443e041441002039801c99003c200000140011170010a40140503032102520030780354190003011124000c002f882481c00080c00d00c43c0560b0381c0301c05c00c0201d9600286494490b00d03050f007003100a12a046103d4000e09c6446558010000041220042e200040058a083e82e0312030005458002000300a409541c0c020200400c0000b200d20181880d40070918001500f40c01680d1400580784a82d0814641000c03100d100d40100102e4401280d880602034400f44424100030321000540030b1004404180000c0c00700c0000d501404c80c03411441800500c0b01102c11400740e = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 965783732 1250 965782482 965782577
    0x2041b02100e03071707080f04140108150f03010e030a02010c0909020f040b03040f0b040605010f050607020303160f0f0c0e150a0504020904020409020d0507081608040201 75
    0x9040084090300850458844040c10781c480c40c01604a090040c2d072510107666540712101e160981110f0035850203202c0c060109081c440030b0180741900304175043d42c560500e01c1800954120240d01410403c00740d04120200c40c1502c0b4003a43c0070800d035490507030f6820304c4002a024014801c4800307654031002c00c0d005140b541c150414100701000d42c454001e00c1d52500c480805034030034030b1072961440d00200410090034480400844c0c3c800c0c0142520b54994160313648404e4200010784040d10190380b81d030010300017141540740340c0c2c004010468185240441035030200f0307164060a002c0e140121100300b64181440740340c40c0c442c01059441102c0c504030104903c1c005488401900614025070317182d00015104d050f40e0424203100c00c00092600e20400d10b45410080a03611244e8001c0d0010b400388070010700600303540040c2c844170038070502c003040d14580071200806014000300440b220360984281108002c0e000f11105030810f40a10382000c203042e070744446029000880d03000d19803034400c000826403400b6 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 965784982 1250 965783732 965783771
    0x90b0903090f0114030f040303020c10060e010602010204030b010b030a0e030a050a202d0727090206030a0509010207120c300509040b0301061d09030a120b0d0204 71
    0x10011110701d261000640011501c00240964030040740c1802c00202e503008112100f80b0350302c00d100e482d01515001d42f00390a00c2c00d003940f40403d01300b640d4669006002041c90001e010f4054981880210b00341440c6440760903c0070300c10300c500281524008041000d940c100e0300030448032004482140c0d07179801c0110b4001c1c6031360f0008282400042562030b00001c80701c0c50403a000035105010004140721605102440c202041c0c861900480c40e14011126040340024041503005100190320444030081d21508000810108074045040030319151094006940e44029a034104418071030006403941e501545a00a118202c0d02402c011454802c0c00a420741c04a092a0703040c0c0304040603101c4c048000ea0b11342c42d80701d500380c00c170408030a00041c44020f544100040d201c22130008101050320000d00c4040ba00312400c0e5000042040480c0600c0503202c2120360704076800003981c00095281111a020003449103038501030744d050f010349404544485507500c64008104c4d0307030001d004100e00e189180c0c4009608 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 965786232 1250 965784982 965784997
    0x4030f061401050d06020a030e061807120305070f03030b15091f080718030209010f06081003050705010c110909030901120b0d03050309030408030408163204090b0903 73
    0x1035050281d107411561411075014120342014152604289540e503900002e5044074155408250390f40107000d601036000c1200760302520303407000300c0481c00c500c0b009070b00c0c1072034141c2c1c0010040c1c031680b4040e200000c1e0301c1001c681600e504210301e050b8442a40c0344c1200a0405800569070084412655018000c01c03440144040d04e012110440b0800d00038800c141d0801b141040c0c4000b244c60304000400e182d025408603001103d842c80c131200042d840340c1c0010740781c10080c2c1049800c419042e40600480d5046120190842038040000081d2441d41d132343c580d83c4000e6400340074104042881c1520422070004450706a00d18014840d850b0781c0340c01c01e1f6003a035a0b00324022060000360f2010201a4101d06881055a4410017400c00384000340340b49c500340d0b402e07440a004030502d80b00401c00010b030040240094030140c0410409058030000038414010301c1803554100c495021059202410803864012402c10384a42d440d2002c1108407807800014010019070340050401d00c406c1c02004114440400240001d = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 965787482 1250 965786232 965786243
    0x40b0a1a07231005061e1201020d020f0d140c030a1a03010f090201030c05072001141b1507081b0405030304080709050a0e1b040f0603030c050717100e100204030f 71
    0x8645da031004008034060040c040000d00300e00c80c0e002003490f0070714414082c2134101803000986052042903515080741d0000301c004c0004800815100c40c51101402042001450301c0411021410444002d15151101501d19900e069480480f16148440704c611418495802002008101080d641e844060050400102d0020703140c603115060048c00342c0d085d500456042a01d4560744c0000c1c010607101040104402070601003100400c814140802e4010b01c24900307007119401c4080340b480b560718a0070329400120090710204004220115601000d09070380000101e4507211411400d80360300c4400c4c8a03a42040d6014000000c2c04104402c00040301b400301c90041200300456954000680211001000c10084135049600d0200125013a1000007201c400010b200042040404a501d4101c4030907034011404202c3c2a04038000303004090150900500e10322030a8805441c00005103915185030795500700e04503550f801a119826400c0102d5040c8103102c0501f15502c5443c2c1c00d2520300140b0000c0102c45c0e = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 965788732 1250 965787482 965787491
    0xc08030103081c110f0f040b16120503060d02010e0a03020603280c080f19020d050a0e010507270305010501060206270d1202070c14040b0a1a072310 65
    0x100707030003d44298040301900074071140c140300d002402142503034001107101018003020b01011038840c801000070b080c0d40207481203064610702d1600d40175a18410254401c001e1006c280204641a00d5054507280116424130785003142d000384000081c08504641c0020b074000402004106009007070900032261140513200e0303091203000019801050b20b4845142000084584010401c800220514550170000100c042c1070315a00408a51040380c100c140d01800032601ca00a00400c1c06d118820060400341180003840315203806007000d803103070310616003001d510341e108141c12103003106005500d406543d1200081c855540c3d5803000035036070740e03003658064000c0105000841c40d6491700400303100e0045002028003a060b540d0381c001c0d12101843c014044000d6000c00c0003030002040d85e892000034180c0080034180c50320450050100300e814040485010b000151428050000c0300301e0b03025800f01c0c00100d0186c3e160414a070001d80b12003820007002c50031715109181019500c002c91f1103040910401810070 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 965789982 1250 965788732 965788777
    0x60306050f18060a12030f031107020f060306040b0d050c0a050d030909020a0306030204140a0b030102121b04050a0f0329040609050c0d03030b1002070b0d05070c0803010308 76
    0x1d100d00181511691082680d04000b03088015040c240c0e41c08a00101601c4074107980c1c0c0e10102c20a40c585030224001000c484840f843e07690188078001c00001c00b030399440e0402c0d80f0f96021440e5028505e181c1c82c840c031000b1000880b103a850390442111008003500341000100141b501d01d590701ea10b040480d108040980300450181448802c4c401900d4160380c544100c1450085007900943c4410381c80020540c032a103010001d83c895000c0d8410303840010480e04c099150440200c0116210001d504d84242d00410034540078803448155141c00c043c1a808071407642e4020303019942070344207507402a5040303056908002216450f45007070754100d0b401100c4001c4260404040c0801d070804852036445caa101d1000440c0104a05500c0150b04911505c1152240d4100c400010340c442800e6104500080e2110750022950034001c010348101d10060009101c02c03800c2030042040f50069102d645403503640c410020b502140700e00103c2d984160007040c100d82c0c0c2e5851b402e00c0c80050340700c280c514100581408820 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 965791232 1250 965789982 965789989
    0x70305070e0601020a0b0403020a0803041b0b090a0612060905010f081204380c0f12030f0112081e28022a0907020a05120307090b0f1207030606030605 66
    0x40703110b0101607020b46010744a0760f848171011a0301500c25011032094000140008107490003c1d8019400380020062041c90a080e20f014010f40c0c0c1c004e170500100601c03014a40b61281c50514080d1802400d0407241c1e400a0755170280207105551109a03c07900f03107000006c104402042e02c02c1540c919409940911301d640c52928000d01c030390306c20044491324400c00081c50b00401d0311055003523081b46480440c03800c020041c280c495000051030031180d401c1540780d00b900c030004200c0d2066a944225a0500310700e0420040c40d8001c10502c9184040008a05840308209060086542011030070784120a000c912502c4941117410803c0c0c080c11074602140d0b0700d00f150740780b0310b0140c0c509041395006000031503819480002d802104a40100300c006606028991079030b6a14a00e0300ca03d00c241c3c020b01c140802d500f017641c50521000000070513403000300300380215a03038040c80c800f0a85030a0001182d80c2e0506a0100c801c5210309503441c240301c45140d00f4818141e90641044048a006a4040c005d480d03e90040 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 965792482 1250 965791232 965791259
    0x6121b08010305120f07110612011410020601180207030c0b010b071a09060103020f040605281a0703051b03070614090d1b0c0816210203031209190507030507 69
    0x4005c014009100c20400541182d10200103030801820250400c0c1d20846000600d090a8202402c0e015040580700c441e401c1003c8040b40020452004080551400045041d454102185010920380008180c03080c1805561031f29041540529500899070395241c0780c1611750040481240c404101c4c2c409200c64000c070f42c04c824005c403039071405040f05e03929550030400f0f0a021240815080794450b00d0019042d542c400d14186001c01c03558040c582d4005041c0648003078800c0360080007034540c6108040e400000d00b6010b0f12141b5a05003052960b80c0c02d0100e0164084c0300c3c00a0a10305480009051004c020845e08180c82e82d50081000d002c0907103d08a8460711090360ba00f010300080c180c144a18000606404200c480710701507000d1204646c1c481c414039003040c035400069070b50011a24010000e143e5404108034441e000c0b0380d1a40303a11030190740000c0c0c8900c80c122156107010040c1d40400d0537100240580754019203c40004141c0e607540e80340507031700d451661000740c43c1e501404134001200601d0501 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 965793732 1250 965792482 965792497
    0x11502010c110c010c02043c06150503042d170301050f220516110d0e060d1b0e010306081b21062e0b030106121b0801030512 55
    0x5041c1c0810600f004403004001900140d0303200e03880d010002c98654000850048441c504007902003021004407a26000420042891240c00c0c0380c49401c0090205170741d940d11804000d46030a60f0750f5261400d040c44181d444400940c0340700290801c40170103003a5411100345080c42907946044181d044401806580000d201c0c0503040b802000f5405118a0091944000180d42c160b5488100250180a0084460844012505441051005413007942110512111a050300d004025a12602c14020401010300c02d2044c021b0b100458401c1c201c200642100c00c0610a1040c12201d81c402003e00801c0304415582c001c6c0800d103004004034210802094000c42240d034030700300200c160b04035418840b1140141c0800000c0e441081c10002615005200c41c83c06071b07001d90a114107181752a03241e0180030382a032a000e400d450300100b0400803803e814041d20b044a03180d090010b206010504c141c0040d000101c0081c07054241207130022580c40e0044c0750780341030341d010300c1c00c030354000c103c00011848500c00d011 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 965794982 1250 965793732 965793767
    0x902090708061c030e060c071a071b0305100f0b0414190204050a060c0c1809292a07122703060c20070501030c0e0d060c1403011502010c 60
    0x50010000d00300314004142d080c08190495234800d50301c50800c48003c8568088010360f0300009801018003441094400018840e1040d2603010b03841c598030750b41d480540d0541400203540395244200c0360000c9a2014804220241c03090100104008108039406070031100e00d10150081048205000702c1403080d1020340300080d01114100d07003008001d54120004541c12100c1d84c00103c0e01050203295000c61a00c02243d1206c041803180c103500d4140383c004200703140342503ca1a18020104400c01c0c80d00d105070803801115000f562460780d00026420030034009442203420400003900c10400100300c02100e400e05956882e81c517032581c8041407441d11030700e4040c4000b2442d0102424030100fa503d501400c04400b03c0c0c24004945111038201031321140c010980e41505420500080210b56014003c40214040c245024401050b0172800903010b98404400a465980c1e24a0601d01050103a8000000034140921007602ca44e99410000f0002c1001e0f5070010055081c000f2000045001742115000b807514034 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 965796232 1250 965794982 965794997
    0x5040b150f0d0204150b0307030b042306031207030e090901050403090303110712061a0405012105010207062406090605030121080f090f06040e0c0d0902090708061c03 73
    0x80401202c50001c02040c1d07030103035403058002c0d0000116001d540003400c49600300ca803030b4507050202804907070605000600503801c24203000009901c4c95801d03540074100e07204c111901d484040c0400d28021480b010561180b00004940c0140350700500d0381c104442084810346155900c5444607426031f00240d4006000c01c42141060000034000c07900140250440d104484507680d4401c5011000100c102040c2c0c0c1090f40d400c40715506c194007a80e50b00314604156010f0180354507014150410038030000d015848803208030411410040290101ca0b61203400102c14880c80000b0751500c20032520382c003054020200c1e18000002c03464052030b0304804513a00c5403100360442c0e18115031030310001c9208c45140782c01c165501011000485040c0608082d0480c01d4171a03407142e00c40e000388403210380c03044038291043e94103106c104500030154104540c0714080f458400e446404100c105001383c610408001d50040e41c11040200c010360180c3c4182c891182140c50022403442c2031042410580d841c080600082c03901d = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 965797482 1250 965796232 965796259
    0x17030f030403020a0c1511060f130c12060510141c1b08030d0b031b15070b0910321b0c070501020c0a080a060c0e1305040b15 55
    0x2902440e80240280156100d4082c541c1d0750381504490b50f00020642640b8078010010785512040600d040f00ca00c070300420703207403c00c1003d4103d690401001c40880e82d900c042c01c4d030204074080e041840109040380c040c075480e0803986042c202400c0125140c2030401180c20b030000b42c092071405241320b134401c05414032947c02140104242c031144807102c20360340c040d40201d42025802480c00540c004040140256071942403000d40c640c2981e9201c502148241c0c000e452128003a0b4011001100521007180c1c0e81d4054401c0d05c011f45214094500003414000310407081064100c404601480382c0c10b2481800c01604070400310042e640b0009000303030303c42541412201016180b003400826001141007098008103501c4001004540e07014210321a03c50b0042c440400c120758040020840810003224000c141030f04182c04141e50b10310201c40681080e0702c4810349905180245800c0101101c05020f00710583c055074030220140c03034180c40448008500c840040e886120a03100355401000003400710924070303003 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 965798732 1250 965797482 965797507
    0x4030e0d0c18060312020d110109111e0616060506010f0c170c0115210b040327091401060305220602090d0f0c06090311040218120a020a1703 62
    0x1800c8800c0700c0c0840e0f5510300440861703210200021044896802007110102568008003d0008441c007a41c090703041100075000034445c3c00303030258400000c1e120a90305e6880581e00000201c03c0c1240b46411160010303480c48030554031404440071900900c0c041c031068407440011240225154841000140742c1c2c13050340001520f01c44a01c8900d00b40b880982e04000d980511142100c1c0410004140414510410001d9409542ca40c0c150b00c2d680000c1d50519981c02d031528403134007500130401010014020222540c0e5008200481070000e006070000c4803d5850311880c6008111070050710113501110f000018826100c0c0c0181841940100d030900c200c504100c4411040002c407442c121510764090142c07032090b4880740014110035001c3c80c5094410703080d5040442405000d504104200a101c203424008502d506501c41d032480f03003d9400507901c0c0c03100e5001d2400b0b05801881c43d58030100018100c0d12249000034040b000354000c54905840c0c56450a1200c0c4418240844510307070b0b081070012130352809 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 965799982 1250 965798732 965798759
    0x706110a02120a05180f0a12050c0d080919270e0c01052d030a021b0c1c02030a020409110f180105041806020c0d030f0c0e060a021204080604030e0d0c 66
    0x5c1c000d030030103510408240c0092080300c0a41c0140502c5030005c2400c00c00d200082025005d014400e80e80210420f80d81d8070342e81464030551225a0140f150185a080d1390031040d16554000c0031207900034401d001000c110341140540d00f01a080307a60742044100041034101081446181805844d600d26150f040854180e100110003d071425903d40400340d40400030042c80214030544a07002d0041e41c2e0b40d803000d401211040d208081003840c4d0300102d110403080d121030700080110303080902c000204408a02c0005c0c03412075600c000a4025007400c0150042000c000e580321010b07101160030310070300702c0e02109019100001c40400c20004000c10010030840c1090f0340810b613038140720103000011107195102d10050360f11018801040794090b194116880d940b40c0b055044034071341e0b548180603828192000900039016201c1c2c191084d00009101c2303086900821030400564940507496403101c1c0d90715070702030f1600d07011a42a000710f0781201400300310780740644555407156400100b8000b16800e00310541e400e071 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 965801232 1250 965799982 965800027
    0x2091201140103240e01060608010b12010e060402040302120d0206010501020f0a0605060303210f0c09060a08180a11121f05060310050c09040f05011a0904020706110a02120a05 77
    0x301e01145803240302c4c003040c040c601d041210f01d000804d81740c1ca072140003895010140e1014009d034405020000c803441800b08050b0460740040d40c250519180c1c080020000e2056610007507100d12038454100140300080b030066407c0790260261021a0b0382d03080160385607000503510840076042081e001c1d001030003aa129a80124010341101d0400703504000f002010000060a126404440e0080140c0c0310260030405034010014030b481810043e032400032034142c1c000d4520080520103c580000d5100c6402d00b0010301294009040380e0518140d804c00c042c410201c0c0182c540105890212044513800000304007260f03114a0309030003100c0808206210040030003500295040c01a500d040000c40b0803409210300840d00403003940c1e0f07280221804c0004035801c09000400c403e0502004000071130000301d40384100402081d0180d6a03c0400d80018001e114010004110b1880c004690220030030250103001620003603000c5446c221540c20301d1041d94040c00e20b00340e00003441048002d0f80600440040c4110 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 965802482 1250 965801232 965801273
    0x809060910032a270e1e07020109020d20063006092a04030b090f01090206190908031201151e0c030201092f01050403020f01180e04030302091201140103 67
    0x14036102c04041140000a840c01c1c250781640b07440000d4001c40b1b04600750742146060000b0001180c103540490241c401c200d202606ca800110703005180c1c01101144892101d01c000e2038140d0740d002e501c208511040c40c40d08142489a5402d1504c00010003014030140540310091901c2850355840b002c20465800000341144c008038140c8181da0b100320f107000a4409144a561100154501848181d1903c08480c601010580c109019480542c031800103ea000c0080001c030b40c2800000b580c1c00355510030040d4000c1e1054070000828201c03540e01900250f0507030b1240c1c42c408100040700d440031241c4c080c500414030b848021000101c00058020012610b9191007400007080b1444c294540b5402e2203025100c07141c00f408040d2004402d80d40191261007840c0d0f007401c016081508640206504224148049050003950704d0b0b10004400c4400f078810080501e03003680741d0285010b160042c00f80d085145114000d01c0410104c41c84a941070103000003107200300100340c070b00c0d80c80d5489280100c49184001c004 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 965803732 1250 965802482 965802557
    0x111e03070207080d090302040b030a1502030c0403050a050f061008030405090a0908030f04120f3f09020a1205031c061d0105090a050903070809060910032a 68
    0x2552201404204c00034040c0d034a504124615500520054a1150084134400d030091900f80d00010003080703140005840c0c032540141c8139a01c881002000f84510b400191031440781d0b9580c14100310b0001802c14100a44505843c22a115040c00c000b40d903402d4020840300350030610040c4154141207071000d40c0480e10b00e8001c62091519241c5000c1765101342c8441c074020140c882044140421110440000c62542c03a00007400c0d842e9050003886031012489580045112000552541441c10504940c0c3c0c00b264501400f40e28210b0140c01c000c040c824000c03809010007000005180141c0d1400900342e07504a4040e51a0020081e03200c815801c14071709034990555624004100c5203544906030301c003849071b48440d202a50505040000c41c1400811040c0c265041004120780c00601200b0f41c0c1c030190b840720805440d4862500000c80c280124401079800800020070140420303455000400c258000038480b60f6070705110300500c1c40c815000200d0301301140510700d2a1442d40745e800344490445905151052 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 965804982 1250 965803732 965803739
    0xc050904050c031e031602030c03070b0406030c09060807081f12020f0405061810080d030b13050103080a12020d0513030f020610050d05030d0f0609111e03070207 71
    0x180100000c0d1410303115a400903100e04420f05040009109400800c9076100c0001c038802c86090b0340707100d4015500000d000c01d0440303001710349081080c01c41d0808001c0541d0200d40c1c031080807908a030000c0c40745000003810424454074503030181e03000f8010780c2d07400c2e940d0f00c240303a1320b5480030384085070301900321f0030b080711900b000e1450002071540404c0a4204c50007101c0d81661540100403080c2002000544558078003018480130717a48040d51000614070300340300b50606540d90b01d110003a0392002e5021090380d0041d001d00c490260f41c1030780200c10700382c401c94001403803040e2a03070b2110464000f404020040902000300d1807441d801011140301040304078a0142c13a00c041580e40106441c03040e156000c50502460000041541000300c5240442213840108118a0080e283c0c00703112480388101402450516808020700c401401140c58590b1614410f1001c0390701010404010110341c0700e41c00c200380c5000054002d11100200f242d92000a00c04a0f040a507424500040345520142c0740c3c20544c481c001000 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 965806232 1250 965804982 965804989
    0xe071b021008012303071217030906040212150c0906071401020306330708040e04050601030b09012d2018010318260f03090c0a150c0c05 60
    0x1e00300201a9180b0b0425498002240c098821300499000030413683c11400b03600b0b403400504c940480e00031107810002d181050901248c1d07824054400c10580700d000042200032a030001d0114010352080d0785401c0600e111000d1641c030743e84080b01d40340c6c800d840d04000c00e001c40049009041100c3c40100004c0c83c104965031242e03200b070050110f001c0507035000b008108481c541184c10010b04c83c0c3c1f640c642c03002c0c4c0041c580b420242c859000400816040e0200c1c68005100854040c1c070040c01d205402440141044d040c0b5a0b51a0424803040f507104a00000103062090103004080e24030b490755008122544050b1078146d10028014141400d480da90341c0c84c0340002c06480001da0700202e204041c00e0781c4d4007160315041c144082c8800c4407030601d03040508071400c0f080c42c9204d03541269013182d501035004070303804840c2d40a071842e07140210340400c000c01c0e83d03242c55034440001c50190104204a802040f141c100788000d80d4030b07034410940c002c5e240d200d080108600482d036003501c03240f1034611021429140d5000 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 965807482 1250 965806232 965806249
    0xd08090a03050f0c0604050d0807060213090f0e030a0e061c0c0c061112060108040f080c1006120b041202030c0106060e010e0d021509030a0f0605100b040e071b02 71
    0x1030301c003607100c0f29000042d900240300301403c2032402e45e403461415040002240b900070800d04014044c890024081c41808050f5054036401946414072840c00c0e5907443d0140701410400340781d0318101c1e14081800603142000003c5414810346500c400d407090740d60b10100715a07030300120030a9aa010014010401d105424400d828600f4001d88400c0c070100400d0800d401124048a2804100d4200700804128110000c50040d07000c102482c00c02103665803440d28400b01c1911400c01040c090020810920b03200022078444980380781260108011a900d030009080d2581e4150090315500007c0081004980500440004840c00b40100c921b4606030801e20307401c4503010340c090340004002e4040314043e507a0000e201110810211502ca00c00c50301500090080111141054029440020040100c3d00e00780070703d00005030031440900e8060010308061002c0e190865000c1201000d2290120340c00344940244c41c01c3c0c2d4404941c413480741e0713030388201562a08680114410041d01d1349400c000140c0e1080701 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 965808732 1250 965807482 965807489
    0x702060406031b030510050913170318060112030807230901260a0e0a020603010314010506030a350304150f06051324080109020906060a0e0d08090a 65
    0x5002600e0000105603101c403200c000089010517040c04140100c00d003016800c0e030190780c1c08a0300042036071140e008034000c03100e0354003009258110406040300d0056814002e1441004010380f20b0080c0941205803980b0341400b4040c1072098201082030f00003207441290316642c040d5880c103200000c0d401100d0050340030181c40320a06032b00000020040c01035603000314503130042030810507080d0801c61042c0d480031a03900d0081002e014940c2d0341e04003c0c540c00d0100500042c51760080c216036643d586908000801013250304407120b5560905000c50301909000a400072029040340d11050021005491042c4000074081130b00b40100194100403540704c03214004501443c07084031888180c440300580003090b41c141400c04040310345020b108114589400302003941d00b04203101c000a00b059011410989901d2a81d161900c3c4400802c0202da120030544c0444030040c001c49018505a03184000c01010f403140025283c0010100f14018420742040380ca900d0405114a0f1f0b01d45c01c01c041d000104100c0c2d5503562 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 965809982 1250 965808732 965808737
    0x408030c03090414040f02010e0103110f04091a030a08070f02040e0a050c04110d0221041230090501090204020c07050a0e0c030f15040204121a0613110702060406 71
    0x2d00b4206030325040c4128040c03291600030400c444d01d05515288510700a201001e814084518449200c6038407030391084c001c0700c60b84601d068856a26030b5030080d890b0410300039440e82e64905051850340c0d1141628001d0152001001042d068030140d444000c190844ca408490007120301e0b20200050f0744900810060052090041a50700c0740c50410b80d10f051042000940201d00c0d141c41144000c50003012203900c000c4010b000b6948090b03001010300c00c00050307049504044440e02c1400b080084040341c003141754000e070741c900040b0b41c5100c08080e90081c0d41d082c03540301c2008004000d82e116240390000159540034500000d418100d540110781603a1000e00089401d4000c484e007404207103400c02d00c0c03401800c104000c94140f840d00c071414441d18400074101c5400100d07120006a9090a0001c5049c025400600299100c641d500304442d20f040c00400c080b04c0803804c1664202e00c041d03407421020710a610041814101025842c640b80080c05554070f404540d020030054040903898210060000b01007da = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 965811232 1250 965809982 965809987
    0x2010e01051311090709271401051302030c090d020319081e03041a090703050f0304061b020f0103150302041805010b061c05060d14012f07060209060408030c03 70
    0xf46014030041d00b00d2200244500c85420601000903488502d510548084030f0b6030402000880c80da984401c00b61054490f1514140280f0380322220540d008141240d00c10754aa5003c2c8400710804000d07400221040c0500c0b440a01a04440e4030380b20b1210f407030290024003614000070507401d40c0e69201d1050300042d5540c2c8000034031020061a4441020203400f503026230365045003407503941d08a010461449107001c415020700481c8800b082401410021544501200c0c0040b0740c1c80e040344c0d100d400510860000c28444102c9a0310380c441d055981c04101e6004110000300b107056001980144a90082110745446081c004001611140315590b400108600ea980001440e458103c2c00d45240203421030145106018020b81800f500048102c00d402166002c65a0f03621503011070258204014040c011040c1000300b41017071907065008010b040103103420a5440c0007410b840e0903179800e608680880388101040541b01003203490740507200d401e00080190b032400c0c1e03540320344603d59000414001c0c00e94200 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 965812482 1250 965811232 965811271
    0x30f16020705030a061a10030504050115080a061515050d2403080c0c15180303030c0d20040305070602010507030b0a09021b012c161502010e0105 64
    0x208a0810045261803008011403810900460b8865044c82001482a034560780920710880001c4124038130403034090203841ea400d070a8400100a88000d6030150707815480c00c1005e2568040302105401910944e500420041100e559548002c2c51040e000070b0161180300320100b940b046001c1410340c0d50300d0725501da544a005c0c1020710390445a001107020640199045001d00c406065901102143d030000811525820807038820340c03c01606c050250303808010b52050424205600c000707001da0300040c0002e50030f00d2010609040e620321041d2240311092109010400303030158190070222024140110b00c4c0307000a241c0100100b141c026800448141d00685010300416a09106460740403000e40f605007e00800307203010800e0240c05d0300901c401c080e00000d000e01c0800400d42041b40d10345a040003002100100b61038210000000d60442002e03034690302881401031000035240611801041418410b1890300001c05104120003074540c00355501c5010a501c1c0b000c9c01c1c40b80178451803816882080c01400e = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 965813732 1250 965812482 965812501
    0x1606020601140d150212040f1b0b030c0a0207051203030702060a05060a0303080604141510050c07092f090a060302390105160e0109030f08130803030f 66
    0x160010342050800509419450b91101c0741c4101142c1c014904503039089015241138068884c00c00302d848460f002c070702480204005408465242805011034a8440300030041c00b880c1c480141c422000704e000c052021a94290102c0002c00007124240111800b0341d50700d8002c00c080c000c0c0440746411641012041100f815014440f00398000b904110802181c909480000c0540da040c1c0800760421421000203003458407a035204d15682c3c443c0f02160310340792400504081400340001c1c104d0307000d481d0761100501800d00030350179940c035020460041d00506090111150003800407034641d042c1c2c8910900e2000d00500c4220203c1c905c544090043c542c1c030207880e42404081c0000c0e0f4410802c040c8100a80b4a9040014032580341550143c19200c0d00419204c0d07007800c50100760490780c44103510700020b000310580c480d040c4004000c40350701d0b800d5842800c00d00546961b012884040d0080c03480018840000750940e008000c26101d61442c019499140c90ba1646142c1080b5003c900214480c000d1084641 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 965814982 1250 965813732 965813743
    0x30e01140a0b040b010c0302071503020f070f020312070b060f041d160509040b070f0e1003050912040e181006140117010b09060d0b100206221110030608160602 70
    0xc4e0a00700a020896282d9000b90b490601d8030035408014140a002204c25201e90120381d03155981c0e102076520b501c01da0030002074001d1011012072091150403100c100080c0810180c0f112103421200c014840e40c1c132541400b5411810a40265001d070f03640c000c403c1050042c622003050502c00e00028241c150b00c520800c116400b035600201e01c901c603000c0c00c100014041c9100164440003a103050807024800540940d00001c00b25034456001004400840c40c0d20381c50380c0050300c5980c0c1c04044954191110300414010310940c05640807444005001445a01c5c910004968000145045070070b11120698404212050ba410001c0400040c1e0700b00d28280da8095004c00084918126100d9035514000742c219041c411902007902888000c80d010301c0f000c0301548000b01003031001c0c214564107100d8120082d242c2d41d0842d81c07001144410017284242415910340c003280e80b80d0060305201c00b100681c003006107890042d045401050f032a80700100d21800203010030418029203c1880d42c0c000e04106010f401c02 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 965816232 1250 965814982 965815001
    0x606030c0b072d060903032a0909050103051c054506090f01020a05010c0f1101020705030406120e011509230708130c23100c03030e01140a0b04 63
    0x40c00040081c407504110350844410f0300e0388200002600b640610f03045e0054a000c41590201c0301e5005070b00b1002110320140010301d030717200340c0d1400c081c1a00ea20f03001d002c51f6002e010107001c5070300481c0c40005070610030710314406210300340c180a400c041250700c44000e05070180c0030801c000e0892440742c030405d1044244002448000c864096404190306001c140700d80141004144182c64101c40825903034020301c90325040b585c204001744500c109084010302840c140140c010005140400e54181020b010310030341c1c07402c9a0110256207082d160580459604c140307804030411081c5d0713a58098443d214240b00c2e2254503040c4003051500e01d403624290200701c2c3d084601d002c4002c802c010507594000d0048840980c4401142803901c800e0710340f109212030004600100a0445a5042e004039001440b0044242c090640c1401e01d20345541620030310582ea85c4004c0c0200204065070045030002c3e000381c000c441c103041d00354000111684010f0104003641c00a8031940c0d2001da5642201032642000e008a6128 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 965817482 1250 965816232 965816273
    0x70b0703020909061009030f080a0e03070f06080a0b0628030209060418020705031b060c12070f140403030512010803160f0c05210f16060c0606030c0b07 67
    0x207002e80e101c046500c99100502052269103000502407129020310b18a10241d500700e00c0440000e05107103409034441d406400c01c000400c186400f0765943e440c00140400035201002d110460982c80e006058801e040060b2602682e2030b100c9110341d219803124405800000c040140301540002c500e0840c0d90300f81d0307003ea50a010180104290300e00350b103460301220115000060708214074051034000030024040c1c200002d20a020028a14082007408809120307001004400e6036025102d01c400300281d40305ea1034510504104130400103c407a8010743d0103412a1101d0305106021041c00b89001500c4c0c1d106410803808100302045403000461440036246c090b10030702c2e00840c903180000898440441c5c10b65401000e0070844a010700c10486088410382c01000c0240c600e2001d5942240d841c03203200e40052000409200b91a03014036450350004d12144500380c16507860302c1a600b081e8080741c04205410059030380c1a2510320000c005500010080300416180804a49510355840c3c161005c092201c0301014 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 965818732 1250 965817482 965817487
    0xa2d1706030d022806060b0a020606100c060c0207092f09030a080307170403080402040e0d080c0a020106080f01050415020f030c0304110a06020607020d02011b05130b0708070b070302 80
    0xb24603800140610011040c510321240207100d0001203844542ca0801c0148014108000040d101380c80b080a0194401c26800340c4035950350740310601100010200c907a01c0060066410200071030210350003819040c2c01441554040703919905040709880c8607290700e92440290600b40c1c0c5e40702002801800311910700404040c6841d180b800041e5680400c0700740500007003000404185000d01606129401d2500c4c0d1020082c289400d08005c1e02c400340480d0181e0099007030540003148844045075019001005d0348482560340c80e502c0200c41190803281905017991350f9880082081d41d020002d9030021003400001050031700e0302c0c0c81d00c2032000305084000301201d40103001139240414040b0503039a021030b034440c08079100d55643c205010710480b44800d0f290030000402000c81e4580e0701155961042101b0740880e00e0301a100300c0304034200d03624410030941c0c0c094032262440b452071007407000b00100080d80c07012900d42c940390f1a1044455214038400ca415140000300102000070490980342c0c88805801d0450 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 965819982 1250 965818732 965818753
    0x70501030b18010627140a050d0f032708010c0f0c050d0c03120e0106061d0d0b0411120a02040f14060103090618080c0c060901050a2d170603 62
    0x600c800b1040c080c94061000c441c2e807000901c17804108032800c1d0341c040c2c01681a0541d44000f903040d54116126114000c2e4240c030b0000c141030800e95845526035520028605440100383ca00325081420341600103002d102100318071102c10f110742c0150740079000344000042e500218003409800003100201510a004a0740d0200d0701244010aa24400202a04114210b40028681140c041a03000c010403019881c202a2a40d21001540500f06075010f0340c441e401020b01402405510384040f890055000c2d12551104000590314801175400c64030500c0803032100c606900000f003814040803c1185a544480c032100b055142038003504108500c0c1c144104983e070445d4480c0008a803006008605040e01c901c100c00130090250300ca20080c41c00d4200a01d242c503034601d0705030010b03800089529058801e00c2400982460071004482400708142c40303085c9081e07910039059643d1b003541c114200805070403081d40c5484214001140a507070a00b030360342e80c54103940d40740c403000c50540140025011b58000754421 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 965821232 1250 965819982 965820019
    0xa0305010b03060a05130b0411120c091008070612020d0204030317060103060f061b1b051906090e040c05030d050a0305091222052115040803060409080d0905070501030b 74
    0x303c10242e0407c401c401540d5881c1810044c2c0f900388902e443d0800c900d0914480080310111300f80c070301003004880008103a26929030484412a06e8001c010540e08691000c03c0824003c5000c401107014001303026003800c26021002c8100c0e049644240c011a000c6941d050311001c8051045500c00800d090802120341066144603d049481c060b08007405409048280340020404241c0003550b404030400c0515003505030500041d072a2482524064040351420300042004c0b80d03d039000b0380350030766100e4408928100d01604110b0b0054810b4400644084010515482c140102070994010381c485656420305248020100c4600624241d11038010085540c50300d03407940229040d450703482d58880310740140c0710150b072130f00c120a07805554003c2400029801c0c07078080000c0e00b03a00c4031003036059032188090107030042003c501c12140201214000c000003025407034a5840040114010b034550303402c00d03410440c0c0700103d03040c002c0180d03195400b1100c20442982d141c007500318103140c1030701c0080d00d115040507003 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 965822482 1250 965821232 965821261
    0x22404060506060910032304080f0a050f0d05190504050c041a040509070302040c020303071b06020c15011e0509060d030e0a0b0c12180d050c0a0305010b03060a05 71
    0x1060240c0307410210381603507181410307160815402000b03801c40300505a805802001c0d0214020101103c1d00c10310a861000c410056101c1c03500003032035500d840304004c00ca0071558405040201803000a00c02d5040184104010b40303202008072400080f181025041c42024a070100300e90702105040004110000d1004039145100c024191004520041b00b00020f000c030000d07008a5540080c907102c10011031031400034040e81128000c3c0c40801a003a900c6404036128403045440030041140c400d45e01594903800c0c01008512409003500608080d580000d0b64141800c00300d0604101000706c00500420040c00006521403914074800b01500d880e1201141039041c001b09854030075000d800140051501031006100020750041c101b0005507101c0695034040c0c0c00c85400d00300c103441048080410440e070001203c1644664075906a0342201103c00c000903582c0c209811240c2d4007030117141481ca074451540085c0518851400414191440f6051620782a001407202c0d003064100810312000700e150307560 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 965823732 1250 965822482 965822491
    0x15090c021f0e0115050f030a0b0c0703140417010606050412060f0e070806040615062c060307050403030806060301050f100908030a09050405072309031e0705010224 72
    0x400080c0c0e070300304000d04010b103446600341803a94282200a4040c52441d4801300984500300d8030381003a85080740500d0742c0c50034810b80042c100c03c00039020400010700d030000b90221a110b1300d0504d504202082850801d0340003948080800d4815404800d041082805010090b20040c5045420301340b4103900c0170070a0800c25805011281e58524900804480c0d801516500c600c540403034440035a244403c80d5240d00488080e20300529240d1400d5144266005180c00c0b6036003a1380d41031044403d5032851149404d00d01c0c0451040d100d400b9008526264403000c0c51040c0b01c292a0b89466901d50f043c05002020000e1070136108640c100014002550380600d101c860000517910f41444d1148014181c8200c0e0064002107440d2102003204042c9035800040201503903400d89080c0404e4407600000d03640c0e00064000d40c6001c1e501e12208600307800c00c10001c1d00041000030100d039015440d03c00b404011486d00f02c0356440341d8000190a00965804100d0088007240807441c010441c065184800300c5c0c100c0280 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 965824982 1250 965823732 965823763
    0x90d0801140d0f12080c0a200a0b040309090c020705060d0c0507170712030b130c0e060f03011d07050d090611031021030c022e020115090c02 62
    0x30304407126511810300280031254090b91584104076103003050801c8040c114118800501820009000909001c0659174003400f40e44030039001000c05081890503c0c0d420030508036a100340e1000b030001c0340194074086e010760301944440141c507091181c000306445890741080300355800080100102e0b1283c1c0112468684407203c0000c0100f1101d2042b200307031003030803000780c0034040e0080e8140c40000094020046103120f91516072131460200c0007a01a102c4c1449002d511a0408458086841c030f180c10071038030f410300307441c0c04c1c0042041100000d0554010003814280302c5000702c0180110b030002c011740c000c0d81050b0010f842141c500300307000400c135204090040f42c0070f40e1602010410001c4641020406c074001180860300d91130302200092101009101d00100500f482202583d950303c2107400c04100768240d80c0342e4041b000d0540a2042d00300441380710b5114103128000040d0b140080b203015004c10741c0a1307400415941c009115444aa00b515000549002d283c003517189852900024040310303036020304 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 965826232 1250 965824982 965825009
    0xe100e1c031a0907030f11070c2112270b0d0f061d09010f11161502030112020109060e060726070b0702010e0c0108070f0c020310092604052b1208090d0801 68
    0x245107241e4000c4109600403c80c0001c00c0d10440b081e03801400384a601c0000d41518500e035043c50760740417044480351007600c060040400010ed4100004d030402400018941c1020400998804801c0030807078000322070052031107142082c000b001d1030038040e6414401c00300d1000d00c81c5c00031801211032184540b49081c0d400d40b40c8044032400f040781a814051407206100c00454980d0b9480c043c03c0c07409200c52030124006045120081035070741c0944040051031101400c0e050074640955503001009000019074030358107415505080038084c4a00050544038800c023507040707840c1001c05000e42516240d85010800c2d4110000041c0280d902004456008541c0d00d44090b000641c4041664a81308441c0c01035058004d401c800344d206595a005101c041d0b00c136404a184055007080b00145488603d0007040003601d080104002610f450b0307007284090a03000303200d0800c40a401102a03200442007100b1a95250303004100c5500681180681d94041b00820140c0508480d070100280b64076014024000c041160 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 965827338 1106 965826232 965826269
    0xb0f070908070b0a170c1b01020406020309010822030908070b03011202010f0210180c080312010312090305010e100e1c031a0907030f11070c 62
    0x74001d411600d090100381c3c4210792003e4000d40c00c102c0808070010800610214990058034050401543e95140d03030180a15684065030a01080c0d00c1070000300001a00441100e4880000346011072440da106202691003038110480d03c248080050300e040101504100c1c048191403052084803072055680300a01080d00c000d004d0b5404011b000307039200d40154015201c90b1150800c6005882e91007002000b0001190307c11160000d94929004004041c41342020503000070b8806180078600d8402d60320400c1c42101010700c0000e141000052a442540d8403034849040035540c002d009000e050244494a9541c8000c010400c482074079200301c02c60b60440001c4e003002002111800590a44003200c4140c00928940340f40c004410282000c4400940d0303558000d5100303030a0341c0c8002405d081e40080040c125081d0100d844250b40c0104000000304104c221040129401c001076400500da0 = true := by decide +kernel

theorem cover : BRFrame.Cov 965647482 965827338 := by
  have h0 := BRFrame.cov_init 965647482
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965647482 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965647482 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965647482 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965647482 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965647482 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965647482 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965647482 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965647482 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965647482 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965647482 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965647482 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965647482 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965647482 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965647482 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965647482 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965647482 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965647482 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965647482 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965647482 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965647482 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965647482 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965647482 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965647482 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965647482 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965647482 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965647482 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965647482 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965647482 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965647482 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965647482 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965647482 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965647482 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965647482 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965647482 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965647482 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965647482 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965647482 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965647482 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965647482 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965647482 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965647482 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965647482 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965647482 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965647482 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965647482 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965647482 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965647482 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965647482 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965647482 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965647482 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965647482 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965647482 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965647482 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965647482 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965647482 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965647482 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965647482 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965647482 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965647482 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965647482 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965647482 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965647482 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965647482 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965647482 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965647482 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965647482 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965647482 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965647482 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965647482 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965647482 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965647482 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965647482 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965647482 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965647482 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965647482 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965647482 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965647482 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965647482 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965647482 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965647482 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965647482 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965647482 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965647482 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965647482 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965647482 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965647482 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965647482 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965647482 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965647482 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965647482 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965647482 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965647482 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965647482 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965647482 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965647482 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965647482 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965647482 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965647482 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965647482 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965647482 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965647482 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965647482 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965647482 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965647482 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965647482 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965647482 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965647482 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965647482 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965647482 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965647482 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965647482 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965647482 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965647482 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965647482 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965647482 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965647482 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965647482 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965647482 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965647482 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965647482 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965647482 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965647482 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965647482 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965647482 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965647482 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965647482 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965647482 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965647482 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965647482 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965647482 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965647482 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965647482 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965647482 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965647482 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965647482 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965647482 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965647482 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965647482 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965647482 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965647482 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965647482 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965647482 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965647482 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965647482 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 965647482 ≤ n) (h2 : n < 965827338) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
