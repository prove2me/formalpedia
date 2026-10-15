-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4551
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:59:21.367674+00:00
-- url     : https://prove2.me/submissions/b12c263e-cc31-4fbc-92d4-da2b4c1ac0ff

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 818345323 ≤ n < 818525179 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 818346573 1250 818345323 818345351
    0xf030f0912070f18060605090108040f24050f090102040f03030810030b090c10020613060213091805010c03050c0f0a0201062706091401030209070e0405130204050601020a080a03 78
    0x201c0c60b0700c02001c50b903c0d1200003882c00700c0c80c1d0000305803c50a1004010840e01c0d518169064025043c0e810300041ea11000100021074140c00c00d1801c900030308842031207900742140d15004104000d85901140d48600c2403080030b020340903002c0e4211000034001d508150614444118480862201508005108010070260f10322007444901640d0000b060f0006440d1100c280c507a543d00041550780248030f0840c4110b021840452481c0c0190584a1820480748143d00c80348040d401550070112858010000007500e01c100f80b2401c3d100603800c25a607480e4991506007a03084031070f28000c403000e0604240400070440d0072082103500155840c1c5200740c440c18000400c900411083d0802040048c0d2400102c48201c280d0300d249001c511b14081c1400a2070305e9290036000e580e015403000003101c14002c014001460f1050105a200040d881c14a024039401170000d005d880050360601000c810f860800030075400d26005003a0b0005003800105a4010156208401c920030310b0206010595648074000ca443d03 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 818347823 1250 818346573 818346583
    0x4030203210c010504030914040c0f03020d060806041b231c020d0803160203040503030a0c02011202030a090b01090b032d0a060203100f141e1903050f030f0912 70
    0x1200340b4020412440c083c40e000c1d20b003060f58004d100400c40426213122442c070b001c3c01220b03c005030300d075918100b0062200707007030b8041e41049010500c400c0e1200700111b2001410002d04d4451070090b105c40f0940e80c140000c909244115400485191407607540740c1085014448684001160036600c0710400d41c1081004045403040307401c000d41c05440b003000321051102c00f0020394002c292100c030b010700112004070180da491003a840b5841c0c16070000e000d0950260b00410a0216460041c10000002c108211508c0d040f030307104031824025180c0d101c032083c040c08100d03000f050160201420403c00e1000120000f0380d54140621040c032108180a10410b4038154000d450307401804040480340c50341c0c0c940ca00107020b904101c0c1e202410039050080000c0d0721080e0014181143d0700c950303000300700da03008000f80280625648490300d05601402c2c0d9500c482e880d0203240c03111204845d802c502005003146026420101d00c1404901c41d17078818400c00c0c050308940740440f814920122050f4000d44000701c03041e4188 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 818349073 1250 818347823 818347837
    0x12060105130806101707030f0f03110f01290913050c12030d2a03150f0311040e1609090f17310b0d0f020406090602120403020321 57
    0xa008400a1040d00c40c4c24040c410152840030484042404410030310b10b90310300c81440003428464007001d60701c1c0400c86140c910b4017464002c0c41d214409804d640c004070310f01030714045402d1203a9542c0c01600400d0074010840421a034402e03440071482c500e001300040c440038000d001c050a600c4020040c004001040140e419841c201914800c0e0002e14840403e84907003289071f100c9042e50030711803801c6000300a601e031802c240c040da950f4404d90311210b9a0880080c10080002e4400c00481d0101050160748d01020100a61003800a80c00206400043c0800e480c1c0c0d188148260f940311040485054201d40440b5040c0d40305124000f806900ca810a8070180e610201c002e4040103805400701c1240d403802000300500890702c540c00820045a140c6501818138401510394550f190345000e0160382d0414000700f04070300b580708010030040408061b110480c0d001c0c2d40103030081f0340311500070406243c05000c220700c100300c07480748282018076507000319131a1640c0f5018044640c1031080000b12071054a0142c66074 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 818350323 1250 818349073 818349089
    0xe090a2406050d051f0207051c170609070302090301090206030a090b1501020606010305062101020c07060309050c090c160c09060506031003061d101b02031206010513 73
    0x610204184111030003a03045080364609003003190104641c02c000d04006601613104005110250031903080c030071220181440f0305030444d000c021a01c082682002003403625600d06d4019115145220381c05009003207031090743e180f41d400c10320422556603a10403010394088118180540c5d12403641001034014010400300962004020060240d01000e070303842802c101c0d06c6080038100a0310350750b692100d10714a242e8258010b900c00400a03d03913500c641c1006402001c054281d0040d408065071100b4003441b0340c0e02c07100c0d06a40c00700b103d52541d9000c002440051072130703003010020000b071501c1e80c549079405150303890f0007850f00e4400300303240c555100b049800105203040d0010114019141000c041102c611840b0318040c00c00c0340200b854901201180d008281e112149481c4a146a413404054010f400c40f00d82e071146085814502c64206200010034081d40c02c1001a02d800e078904603444c406500c4074401e045603c04d100d8800b4158156040350b801c0740c82420701c03e40382c54800c410b001d60505030b900100700d = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 818351573 1250 818350323 818350343
    0xf070512011508070311030a110f0d0f0b0712150b0a170108011e0b06120402040612031206060807080f19020706020711010311041a09040504030906090f0303090e090a 73
    0x3d02c00c0b07030206410064030300c107100342422501c4201c101a44d80c1c08401c0007600784005c0c04200039052a0203942c1d0340800b8806480c10003101501e03107403110302c41e90780d60007a5102d050410400c2007181e80800d5600100190b003404002c018078070380300183e20410307502504481000000c2c001c00110701078428108a050700c0d03009516251f0b155001207010301715596640f826002551008071030041c050080b445800c0f40030b03040500305039500e80d03c030b0300240000c0c009a80140d51444040780380c85402c00094181800b0340c407482d65581c6506141c000b19000765024504101e549018800b03459130069034030343c0240a54080c5106a00e405805610740c2ca80010380444452000400d20200807194001d011440e02541c038440007040e00ca001541500c49981407588190000c01040c0201302c02e043c9115800b04005086500f07000c00b50000c43c04468042d02e0032303804180d4803442004503590100c1c558024116410301c1148061469030080c15000c1d06000d080034810740a00020002401004021348864210400319 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 818352823 1250 818351573 818351579
    0xe060c06180708150402370302031e03090d03020f0a2910090c140c060906091902010318020a0f080106060516030c0c03051b0405090f0705120115 64
    0xe5030361142005030600c2c0030340c0380002201000856000d201028501c400700003170b80c0b01d03800c000b844408101d0b90b58202001803030203501c400c1c0c080c4905507000c12132a00400720f203003540105881d0944401d80f48040d00320325001c1c601a01c40c0403040e215005070644000d0080c0e8202c1c5010f909215182d204440070f4425402110f01340428960a80d115074030300e002d040034000a00480c0000c2d010704489050407200d4854040001002035404010400041d1404005030168561110a80d502090191a0030f074010340511a0240087c0b1050348c00901410080c1504100400d11101b00b50081c54041d040c076544444801103006e40e01230a1003000d9009140303125268540c82c540d40e12035254040d4030b40941c81c1103400b149031806001183c0e00390114aa81c404940c2241d601150035484080d4202c409680841c80040041d508001c80304400d0100b02d1241214640d600500045401c01041140154040b07502040303104070115107401581c00136500050f01581d19510180905010803c5040020a4481c00 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 818354073 1250 818352823 818352841
    0x130b1c0c210201170402030d080c040506160c06091409130807061401050a080703080a05040305101b03051e0c1c0605030c06070c06081012080a080f010b04060e060c06 73
    0x808407491007602c0711032a0050040f110311905500303c60094045d0f0108200c01545c40c00341e0009580500041041d40c5031986410100d2407903000703203981442c03444208010b1001c20040b86551800392801f4a0520281440c1408003030f2052580410303940180211404128040d0a607080000d41c40c0d0841400c075510070130313840c01800500200e1000005210100c001040925144840c1c82c225a55080240315850039619a0038465214507010402e10500300000400648180f12500380c00c54074800014540d51000242c0c3c01074118103001d00100762a010400800f001d40c0c2c084046005644000124070b0340e10001c2c6800a44920010020402c0303030540071004010090300a4000d80b00180c00b0360301c2224840d01442443e0103001d100602c1050031907000c2c00101e2040c0711940d8003421a10102d0700343c1d655003e5940d919200e8101c1a0754580c80080c0883c10180c01c460350f5038205442c1111301c42d543d8945840c0700d186020303d00a42c410000307030040c64140c9580e400c00317544403802c9a005941d1241803103008 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 818355323 1250 818354073 818354129
    0xb0f0316090f20093f0106082503021512060301020703050f0306010309200f1c02091e010303090e0709030b0c0d022205010f030204030308152d130b1c0c 67
    0x310060380403800c204102c801010300410701212142340c010308a00c800341c5803810a02821034107041100078203900001c09070351901e01aa02c3c1072a100701907995084101c940d5000c1440050009000741c1c010400072001a52003821a101041262a52030b104e0311650300407005400d6030240a0848059a20000c1029204400c45c4c014000c1c101d8030001c02d4800341052140112040024100690003942c00c1409403c01c81042e0341d1204941e07030003400c07074820200c0d1056000000c0c0c10550010708001c100340110070784440541d030011820308107200c032140b460759440d1b100000102108070040c004141c0c00c2c00340c00290140c803c1d0f203800514400800d089014002c2d20010f080c400c2d40d0000f01c01e00035162141d80a8400c5400303482d0142e842c0c42843da580010312041c04256694280c00524800840c00c41c1c80c0318075959801109003040100c2500301c038030100101402d0400555200c9454010200559070f100003100d82407505000c0381e00790041c01400c00000305203441c1e002280040008803030190003818161303 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 818356573 1250 818355323 818355409
    0x61d010e0c010e09040b0c2b110c070b0a020f150609010f030c2702070b091e061b09030709020a03110304080d0b0f0316090f2009 57
    0x108441c052a00c0707000444100204284468101e148100132402003200c120141d640070010301c00035490409444101e088404940700c0100e00d4540428003084600514040c200d0703400e00b081c04d01b5080007400c081d15600c0344c0c1a48070340c0d100c1c00c0e40000c03100c01d8240240000c0214410120540e004036454800081900314100c8a05110b8140c41c800420004094152082507a800450700ca2080d414116014049449101008112501e80c2e0129a1a0303002d40010405141715042c1c6003103500b4142121442c0c400109926030984d01d41a0701000d00580000d003a50303003d0003000e4039100c0d0340e25121140c48984190542c01e901401840c801007482c00c829001440301342c2c9640d4041000a1701310280704841d01040d1030090210804114141c5c4c0220300e81c001d01803280d0002c000c07003917041107203000901d040301d08d5101c0c00d0f180d22101001c06c5000303564894020554002c0c0e03424410050600b44480c0c198007103420350511a000840c111649440340110640000b81c0200c88034000c035020455007e507854411 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 818357823 1250 818356573 818356601
    0xa11010e1f060e040503070807020105091e01030b01030e0d1805301c1d120703110303041a130e010e09011805100906020d0504060b0a060201050c0406050304061d01 72
    0x8400040c9001d03050b50441d04c990b030001e01660810615076150340e9280c0c004842070741044070910000000b603a500e201d43c40003400803c070a044002c40f000000d415143c01109150500d450710305c2c1f85007005400310b03441945071901d00c0e002c0b81003003c1000c20482c14615401c465003002000020f5001c03100d142403100c404840254036510144d03001d5031895a603020841d501c45101c00481030b15162540501900100021401c0351a183c00c0c04600200f146904080110310083d40403440400c14403071071800180c26094260040c44c80c160906611210a041c8034400745040b4400040010030010b4001168010b040c0400e40300225580d20a4100c2012034140c80c1c180ca1395107803000340d002d16100401d041c601107520a010b0401040020401c60091100b4036098440075000c010b0300e191103d0324420644101d03c40d220000e1242c1c80b0105100c540390598001101350380c50881884040d40b605803d613012503000c0d180207a540d0361a454003030081c2c00c2e50b020a80c4210782112078001d8807030741904105c00100c211 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 818359073 1250 818357823 818357831
    0x90507050102300a02211909140111100903030b0a170c040506060d15030b010503060f15010c0615051e010509130e030d0203060a0603110a11010e1f 65
    0x400300c01d600000038403c105400c2c0c808200d80b007440c804008042d01240c0610f00507200341d240d08110180a03405034001320010000c0000312926040d0300c0d41070512460340b1919109480d541072402c6242165030301e001180c140401c98810310001c010800021403041015501804154414500a0064007048214600c40c0741d015078082090813100714510404404507008201c02c0040c1410b001c010000607103426000082001004050002070180c41e80071906400078442c41031450510400a24041e0816842900701000303000d803566082d42d81940042d03240c0308000c41d90016400589002610031001400300f400c04164011400081d18400100c2e00f007658000d04956410300e10303011000c402e11015022070301c00c2c400f01c08282000c010984500c2c01402c40001c3d900c03039400303401d440c607004451101d0010b6000002c02a41c4d0400c062400c008121034101030103414852203418005000d001002d10410007840071522101c182500b080e000d40c6002c400751107201400003480d1310b400c02c1d41400748001d6814 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 818360323 1250 818359073 818359093
    0xf061b0901090e09121602100c0b060f0f0a08030c1002090108040312060509071205220311070816170102130501051c0f02430305090603010902040302040f050105090a09080706090507050102 83
    0x2940c07003044200d50004ac0301d170a03607442104002a405546c0c01140d00032506040e1070103641c49000000c40078104503001107444440801c03619141608100c1180462801884401030698100304856040390345400c20311480c21003050080001c000030b41c019680318110101f40301c4644d4001e80d186680b550f481d403081c41955a0700c82d0310858040c91429600704d480c0e0b400304d0a00072901c66054411468608010f0310205555000100d2619805800340284050220740400c1010021812a210207291000075410000b4001c010800c1044902c40ea50500c00d002811841c20f4251072106c3c1d048011031a010003403002141a60b00094000c3d85007020346040c512012500841d50b0004640b80d000460540d01d050031404104500601540c4002ca0074810f0a1007842d4203035944d84081c50203403900d0080140c0325441e600400044c1c504203610300390940d15240043c0300d0340d03c60301d1510764403030f0038200c0100c0d40b01c10300e2400781440d2041c490003400aa1808120a0802c030003c05c0c3e4008642d0240d0890701080e00c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 818361573 1250 818360323 818360327
    0xc1c03020418151710051503062a1803060103060b18060a090e03070b04120f08070e040213030510050a0e03040b180f030f061b0901090e0912160210 65
    0x38030000442e00180060f80104941c0c403001070004010a180d50540301c8091441801c002600c00594000c156503403415140851414100280ca50102118010a24a100040c0f90003000d601030100c201b01014005000100708003049240d941020001d17044030f80b50369490070700000501c3c40b40d001510584c420300790100c0d03645002c25494021076008110307481c100e250550b02c3c0c00a01116900683d40d01081c400340d4040f82e001b80701035100d540074042c80c044001c0b0f680d01c000c259080d03085814062000b00c2d8188410140c2c03240c0500c1e403420041d500144d81d1410b2603404e640464895000820310b1161000203801001150011801100000703414000d03100074402c96a2240668066440d14420074000448072140303036103c0c035a0420003c1d100300552080400880c1c00c1004600b200320fa0b0354881d40a00801c42c0348041c1200004142d01030307460807d2100c00008007128802e12030079081c1100c813808644031600c1408508204440e0000b6507545144c980e08841c1402c0c1d0b81f071010307881411800c0340c81d86c5141c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 818362823 1250 818361573 818361581
    0x30c021810080a080315010306030804060c0203060f0103030e0d23030714030c0607120b1c0201110f03040b1b0d0c0b01120b040b0702011b030f0b0f060a050c1c03020418 74
    0x31380d1100000c0c0c21aa500b0b49a284075070300501941d07041644843c030010100d0340c1440208090310190b66440018507450051504d010b074050f00003c0010070407401040460380c0141c0104000008482c28030b01d9808030b04240411007003214251240c0903018810107441c0b1000002031250754030410524002c28500150240c49019103140b11000d07404c80030005010500c40d8050304481c41c126080002c0407844100840d034038102500d110050484150003e0043d503030849c000000e05003000c8020054007540481142c2c070b070b010303d1080c0821000081100d500038151250303020503031401d2100715191500320340d80c0181070706101a02510343d04003490000c645802a49007031034902d0f40240500c01d4944460343c0d1190200c2c0c00900540440d540e03018408000807910b0840c056081d419a40071584400e02803241040710342c40c141c8039101e1000303541c0030042a25400240c0e13108041506060352600074100e0740d181883c601040000503544540c43c034002003501076002d042034500e51154024841140c0000108031 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 818364073 1250 818362823 818362843
    0x81b030a05060609040c15030f05090601080d05090f040c0905012316030e0306010f091d06070f0908030301030c0e0c160b09120c100b180112030c02181008 68
    0x40e400c0700c0c002810f00c0c14401c0615401c5803040940c248450795540c8084003019540184a0000e6107850f6016520581d60095982007401c180107000b00394504030301c0c0c030b07a1540300c034002c0300601c0000304184446a90b50041d520403c0000f50040c007181c1003100005110030218012507020801c4080c80012001140f0030b0489080f5111507154035060384611010410404408201c0401010195040ea00d40b01400001e000740480350500b10b03210305100d8020180e50030b0074070310603400d07011141c5407071011000140940c01a1240c2820052001d0000040300c035280260041c100d80d1100000000404c56140180001c0301d1440030024600e07207e000303c040c0b181c42004503403880d03055101e820001080f030a80506400c02102c0044844922001c045200c0613040100c60030001c0e0003000007042c90303085500408940600448003000ca2082c07001e81001015010300030745d0700350310841c40305008041c000c819404101c1c2d0000c120f00385502040c1410951a40102c55010160080d02c400140d42c01d40001c0c5a41c2c8 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 818365323 1250 818364073 818364083
    0x40515070903410c030d0311030c09040e0613062003161b05010e120a0909050702010b060f03060a060f0215270304030614010b180d0606081b030a 64
    0x2a20050380c481c41c2040e4040d02c0c10f00141c0011039100035803c1c451100c011002000003010b8205420a002091300f04a502540482032504040305030090103821400c0b01d42c040503a42c542c41d2680740300404140100010b400740201840b82c1c00602156506a2486803019842118207001d9082c1700c0300081400220b17021140060403050020400140050404484480b038500c0d00c42c00d41d600280c0c0300030040c00300c4030b410394560359500c810805a4605101c450900c9000c003142514011104500030a01c0c84a882070803040d564560100b40c00900c02e42005003a520300800264a40c121004060401e62040d02c20303d1240e041c400700002c10740e005018540b51010583c025001505c11256803a42d601c0e0014910404158034140c20080841003ca010080d48021402540c030341e8250b15003c41203c0e541160000c1c00b1210100411001c040081120081400480c500c00c1e8015002c011811602e01d16500510381e904008002c6803003200068020081a04116610a60f0011005058481c1d20000d40504 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 818366573 1250 818365323 818365343
    0x5071712010603091104150501021b010c1520031906030b0c1b0a0803160e0d1707020a0b25020607060e070b0315010905100206040b100e040515070903 66
    0x2e45001c1d501c10384c040c41c05503001d40c203112000d40c001411103a641580d55094400c1c101c05100a590421080f03e0320404003e4102410100d680040d01903044624010903038010040c0408000400303400c035030b18aa100b8071840c14442440134048040790012100001e050b20f0030352311046088a00c2c046c503c02c40c1e401081085c0d01c1d4640750000b01c0303076500c00f21104024070b9603038042240710181040010809805081c04584074184109904003074011450307030310100310b0f1604038402e03190b40d11000792904940c003481051000444106004c0c45014450b00698882980c07400022071100c903030000c20b211152480228050100f042615003034202001c40a5000a07061120700c000400c1039200c0841400c00800702d07000d03183e0340c2c0101000d40d40129844014081c074441203184c6035800c44540000342000301c5030803c90f8140d40c1402540c8180081001e00ba4040c0c003000310302001c003d801c0040180801408009d5186498245a5903c5400409035003026a04500140c034041c0b0550005040e01d43c0016000 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 818367823 1250 818366573 818366579
    0x1b05010e1c142407020f2b030f2405061e030403091208070302210d0506040b06040305010605130b0907050d15030b060f0901140405190c0507171201 65
    0x8141d5400285909407520500c80280480d05402d241034500d00509a0983c0151410400007410324618001041c403540c046100721400c030210352070f14039444404035032050740c2e104110b908802a000c1d50340c82080307062a0151080244c0820441880400252405016510342d10f000703028440c85403002c43c034400d04419440c52101e014400065400c64042d1611441039a210a00c001c2083d07211803003111030783e00c00100d6408140e01841854225450604a40480150042c070421180b00d01d111a480c00ca0352203001a005030750b59445910040700c09021192120b84901d0300c0c41c000c0042c0c0c002c0d0f601c100c8a06400840c501400d0161040000700500200b149840d461000d9a4581001921000c05a11442e8000030104100e60210042d406880561400d00303040040c40303c0320110304a854011001c000060003101551079040400daa8103882c0003c481d5a0854080401a091a01c024a031070400c048201c20942c401c0c058803c0743d000d622411184480c7c0400c80c0200c0c41000202c1c201d03801303800010 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 818369073 1250 818367823 818367833
    0x20d0903020f06070e130b24031b12040201030905150106090603110405010203040506160b0a0209010f030515150c030318101a090a090c06020d02010b010302041a0304050a1b05010e1c 80
    0x7c245254000b03803a8140e04800c14088a6103e922400100e20b40c420110400ca900304495101c0d00c121501140c00740e14001c400751100380700600052010341456210302c50607040150402c040300901c0c8401c01068400d5860300c00060040c2e0152182500090030440d000141a4068082f501200d105800951805180205000f2950010300c1001543c2c0c0c200c858820220b40303030041080c4205040900183d54403090b50003d8901e02c07144000c0002c041c60241000007540600c0f000e2103c10004944045960034100c82c0384019101d107000c180218003010060049072000046805400d0385500244c0c5d480c01c82440c0d21a04441717003d070900000003403450104ca56410600b25407600460320380d00101e05d0b584951100c1000000e543d011400590109192800e91503087c820508994401d20701585800e2400d07220b1110201c481c118210420000404541004001c000300c6041c00c2d44040000042d01c000c601d0344240c0700d101d10078140407072440c1030340c4c07481c616020704210a021510170401d2a589050340740c0c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 818370323 1250 818369073 818369081
    0x31a0f0a0509090f0307050703060c0f08040b0a021e040602060606030c041a0f1303060b010914090c1603030603031206030b15060f160606120f030302090103020d0903020f06070e13 79
    0x442d004d002c0d1111103401100e0510042107414050001801c1043ca10702d03080c4e040b50f03880fa00c10710800288100580086a0240140742c005410030400c01c8140c40d844007503070003481884c5160020041c84c88480c480965a00080c00841c0e41c0354080c0c68a070380e00d080c1405402c1c807003220310700c00301c900400092101211020781145a8010f08a10314102455907003490425485103651901106408204200b00846130245c0d203a40ca8080c6014411a49084081041e040107171320720303034400c2c010f440004000c9840c00d02690942810800e898504440e241809802840e0f640415030010b080d400320005034032150301480c001c403644a05185515681c000d10340342c9204c4001240d81c1d00800c01c118001e1100150b50140816200400c800c011941d01850b0040c100c0f04640d0101c40c1c400c2d4021200400300d488014413054003605414050398815107080100c00a01c2144640c1c412286001641ca0030f150340010350100c2c0e1440d00046a001c1e403281d030002c0e109020078024090340a4070b1414082c1c017490050708 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 818371573 1250 818370323 818370331
    0x3040f0f0807080d0c0c121506080d300219080708064204061b0b07080a060801050406020c010509061b07080705030d1b030903051213020907031a0f0a0509 68
    0x8101300c402d031f4842d6031109101c05075103001c1c0c80f90407440141c601c0a03800c41c40780400415401004040510100e40090001d400b0801c8882146400c1050b002102c8801c8580d1200903143c0c42d021561072101c0d10031010103041001151000a8151001514641c000c026440c081c8000920b4640c03a08a8441d4410304c800c00000702d405070020b8030890312100c4404201d40c146042220240c0e40c1c031203003480002410030b1003140c541581c04852203201c0000c104141106604800180b811510350b60740d890040c806410b10317510411141d0b181000300004e0240039400f0f40b411002d1000240419240c1780d0700c644da120070079103242c5440c501a2080c91955007a075401004402e100700c8000d070526019443c0e03181142c00900d1061040c64a500c40d12103100c4100c00403524449c840c1c2410441c1410f1514014140e014820320807020380741e1040480c0030840c0d16418114041d03030007403040d4054a44190003c01030003e0b041410750415810f01c0a4038503242c9800903c1a0700e4004d440e030055503107001b0030044680e0000d0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 818372823 1250 818371573 818371583
    0x108030a230c060f060123030f27160504020c070b1b01090c1a0c0c0d030909020c10230a090323040602070e090319090803040f0f0807080d0c 62
    0xb000c2810300140011841045400d4410f820340c54150005051b03406040c1c03a00300b0b8241400d14006017a1202e00c1920b400103043c848440d04c50782d0b000c0035000009200350009061354100d114418111344001042c01440450248252403039985070203005c241d00a81000c10300e01e4100e04818490f448810b00501440710740300b40c40400c01500c01680608407980035a0030340b0807184481c01882810501c0701d2030400c611807000c1c0586408969a4150784800111501ca40300e015a820750300709152003810340402500503031303c3c210340d1103c0d404091030762003e1024000c29903c0c103105240d807000070a81c00030262103a903044680580c0e5a0703804880010031000004070b0903c12602c882004001900414200303444054018640d5281004000b03454924070f503012030403002c2c105003040fa58000c0401a0380d00031050014412030024514410f49036031001b6040f001d40d5100c0894001031134007050524030101c61103e0341d98200152a280c038152a06040d004449540d4048081044050b108050401c0464062 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 818374073 1250 818372823 818372827
    0x4032004180b09071208091203072013051905280519090309061218080a121a0f09010609060809070905010e040302060601030506031e03040e07020706080108030a23 72
    0x1050ba00c0f1700ca41451105917035092010454041d10f062442244800000040045d0702306907a66481401c401c0181011040024152a1444840c0c903200c47c04d054048044109125900c2c001030540c600c500a14481142e260a050210700c0403076151440c604032003580800d404015030f0325494413014060103031034440009018455898107010740e210300869981f02e03607145001c181c605100101340328501c5160501d183e01e01820302c2c000d4801c40303690802035a4056011a1181d00791881919410b42a0051100d038a003090351541240744400c1e90340384401400c450b51104000c504d028040b03080e03001d02130325011404001041c0040b6004074442035000c000e0f1802c40f0302c0a900c441540c0705460081e80050446004003040c03104058040c08455480f50081c40c0802c15407801000095a50a031903502d00c5403142d1001c07002840e40824012a006410100d1010745203081003500255280101d10460000903481d8001080015000c4201c819144669980d038142022000f85102003070040d910101d060502 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 818375323 1250 818374073 818374079
    0xa290c03011a0d14160503010b030711030c0a0c06180e01060e0d0c0618090207030e010e060d050c09031e030421300207050105070618020604032004180b0907 69
    0x6030113041500c1c032011490361503034104202c60081c004111960881030010602c01800000101d400352644a8581c0c0342640c2902e64100545045129003240b1303400ea4024490038406200000080390b007221010340e034811000e480303603010340310201d1180581d860940c1c4ca10010407086100309140102c0410060140a2541c5107595540c103503d5540c3c891808070304007611095820b9108407451006000e417040561038510705681c02004609051507250502c0800d15245580e91180019100440f0411104001c203041c4011000f80c0b9801c4045031520a219604a0300103c1581c003814609500051000b1420141402000344a0903550054044003074440591600401c25000c90306a00084001090744001c2e14000c81c4c00a5220444100044d94441c140800c1030b0b90b400f104071411a9080740000600e50400c0c0e0403513035100c650f440040d520810201d80441442807400c0311b1803c40b6400b00340c1c0024607521500348819030b10b03080421400101010f0268000c9040c0010321170344000404103440700389132 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 818376573 1250 818375323 818375347
    0xb03070f03050601090e1603060b0c0601170a05060f09010219110d05160b04080f03072001060e0103032007060507050f03030c03190e0a290c03011a 65
    0x42198060009000d000e40d0800a64040c8152a0401020710704000d2031410154084031040c40a010500c91070b503000e080c0c80810740719503c101d02800b1121401c41d50f40911781c80d031581c0c8074002c0c003d1209000e141c4c02d044141210000f140a0819482000b9180d1a907403040c200351400b40040c201c0c0555502041001c103800d400d50500c0d401c961b042d4035486050740c640c0b560180303054003010503101400f42c1000600a161035022084c41c0301c070f03030061003943c0903543c03840d10703980714000c104a03030b49410404414815150b81045003207801740302540d04000420180c2c030b1900c4c01d84010740318685103030a485005001091044000c03c55400307610803405440200f003900b980c40e141c0e6507800b400000e00302240300310801109015043c3c41454180045040d400c0100e5100038030f02c8040c0006c00c00e540044c4a0501c680c8076600101c00002e1001c09940d0540e40301c0c02c280607220030f00b09001124100041c04002d2008036811034501a000a0800d2410341c2c1c00c040c40f80c400a0148020f45100e044140b2010021003 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 818377823 1250 818376573 818376577
    0x6040314070b0f011805090c040e030708030114090a051e1e0921040f051c0c030609062a050318030d060603050709030302030a050a26090f010b06030604150b 69
    0x242203d0030090036985840c405801d1a9071103440c580b5003508240034400300f0340c000203440c1c00540b011900007400c17007042e00c2c40c1e501d14852030307a0040c1803401c048000200407038005480d6202981c2560000041e0f541e02c0f512000721036007100c0c8401240e28003884003400d039424800c1164043c40490700000031038906620011000b808880c14042c40d44076072481517032910341c0c042000e220020040d1083c01c1a0410010003015131240c02918080c4170070049804000b0011810021419000300d0300c2c41103140c5a0034070f240a4019a4010766000f410042400585202500300d940c0c0c2c1100038041c2c505103000c0c12021070310342d40054494043c805003a41c08d0111004244020218880d001800144161400720080e0135240018281000c0c0105042c0c104003198022045401100c010310340f00769255041c000a40d025020191040c060a0044546a900c01014080e0a0040d00140b003110140040c00c4602400c1c2c0e008010f017076070400000d001058150609405c107103052000e8005001d640b580b00d00100352a5 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 818379073 1250 818377823 818377831
    0xd21020708191404141203040f0803030405010b0105030408030a0b0604080f031908070909020f1b010c02010e0726010e0a03120507050403020d030f090b130303021204050306040314070b 81
    0xd01d41e003181c51282c140e041004500d0b041e00080d6070604180ca09664440c00b2110403100728002c4980ca0400d403c0f145007441118041c0c50f040c02071494540d21072a100b556504220f5084a0a40c6444050303841d641c00f4500b075130302c26680a41541e1030369484111060107090319451140d0040c00601000c2000041800341881c5481d400e00215187d03141c07400701050010b910b40400b8203202041c0c040c40800340d40215030f0720650341c03032000c0076903030780c80d6280581000d118415200c00c0d503a0309807110322000d0701e06401c1002a11004c0e802445002d11104546450b0b51003031091015800034410500c0b118440301a40550150848000141c14100404801d06210040c1c070100c00040180c80d80c024410036500c1070075000701d42840e01c0e034103081c2503a001c86d03056039040c0c03c05410b120b80040c0b445155449a2414009007090126542c2c80e03c0c101519031091500c14001100503020702000424000f11003001d841c200c4000a0041c601510f80d620240c030601e03a610b8440c001e100080040c3e002040310701e0a0103001d = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 818380323 1250 818379073 818379097
    0x20a09091e0b04020406050304080304210806120f101808030103060b030706030522020d051204092904020903030f03250e0a060e01110a0b10080d21020708 68
    0x592464500090454401c40c102c0c901c9944140301c14811321307030300000b80d90344150300408099590320350f4104034200ca410750304032440140340c0050500900c1d500c0301c941401920103030ba0740540305440b0011aa00c41002014003052544250440103c1031100d81003e200d00d034005c04080d2810145442d045c48130380c030903081030329440d03103e50717060300c0034182003062400800075890f00700000e04010b07a2141c005401446404d10344100e1000820956840c104103114180d4054225604a0701d01041c0758070f160080e00c104406140380131000382c0400310301600c440c0740840c1d480c03240303061042003001c11000390003a03820382e90140310900004810b17a40751070086000b0a0000d29004003203038030150140c21349241c80c50340b0041040f5480b00c01c1c50340d11681c100100380c036440d00f45403541e01d481d100100c0c4d400240981c6040544030304001901444560f81c1c485004008800c0003084003074031355000680d90b0481001040009210045030004240300160350000400700590151805100d6252130000750072112080c80 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 818381573 1250 818380323 818380361
    0x22090204081516050d14041a090d0c1712151302070201120b12190b06010219030f050910110c15070b04150c09140103110a03020a0909 59
    0x100004003044140c0b42080300c0b41c020000c910b409414242c0a000e03001a11003405004144400c24a17001d8004403a9000e500e0040e01e00341c501418840350040005031005906100c19020a07071595020520040110250329541d85912072923480c0c0c40c0840b411a40300c050180140002000845031410040c00b030301d95901001944c032400400c100100040314031000c0300c60300c10841100181d802108040a102e000c5100181c071002400220b0306c08070006002400ca400340c1e540309000805400b20420f00d09000340c1190381c4550303c01c4010381e40e03650011b510302c800300000e24a2030300081c405c2c90b601601080703c2c60158185600c1d031000c035843c4840d5555030000b040c103944041d140440100b00f5403508110842c0c1195807030030301480c009418451610041c020f2185034001609000c0c80c1042d9445d0601c130404100449038030302ca8024454001c0c3c0c004c40a00801080584e903140d0320078000d411422400300d0800e0700d0144640d0040d002944450440001e0080a0310300150300c070030a12030300062880c201e003200 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 818382823 1250 818381573 818381579
    0x603270607080c03070903060b15030c040f0803181c02030d2109200f0604080a0c0803030f01060c0302160f06020c0406030506070810180902100804120522090204 71
    0x81e05024000b0f01c0240e03c19010310070800c0584e0f004420701c0880e608404000b601c003661070049031140c0b03404da0720005162030000078400c00b00310800c020001c40344040e00c070f07090303090b180c00b44c0e01d88074414800549220003034091109800c1c0361500c84c4a8001d201003403041000401a40400c0c01e0403445010040802c2c00b8001e80894a0414404050061110801003200000310760711130318624040902c004541c01c50310203070340480c0c8a94400304406a0001d01d8a40c440d95501d0400d50350f250700704822a200c00003050001210800002680c0c00340703204a51142d030aa00300041181c142d464014282d08600c140c4009419101480e1030041c090b02000342c8041c94241413241c007901d05018000120b010310714001c0e00300081600031800c81d80244192828002640341c1c08c000515203040364019605c5640b41c0b4807080d1510400c0d030310a207a414825a550181150344240c151a040310844010b403401e21160b0100784200d10400042441a2416180703051111004c02d041c0030411071600905d01140d8001400c0c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 818384073 1250 818382823 818382827
    0xa05010908030f070c030807050309101a01020d05070825021305060f03070f0311190f060e0f0d020f060c0307060b150712050d020405061c05090c010504050603270607 73
    0x890b40c00443d0381400c0000c0c4480786d500514110008100004020b40400844d090ba2010b00115800600b00344e0240841d892a050f40d00030311810b09062405881458100da440d02c8c0900c05448482c2d401c1403202c0e0511103030010340010b00c404001d05201d0072007920014401a50b64140020324207030035031070018451902000f03100380340d5101080f0b14403d50102000304002d50070303a1003007801c0d20340c001d030955980c0301c44002080840c0d14000c0d0008030300a01c2d210208280203000c1c1c0c9101142c0450342c5654154134841d061000480550480d1500248400555009401c01c3d13015401c1107600030b0a91481c000003050600d085400014049031601c0c0c035031050192a10b00f20102000007000c6c03070505440e000340c0b40d0700e101500180d0710003801803140102c0d60400071b484550580b0010000503007034a6a9201144520124802200300b230002203103480013058004100203a1a4011311043e1100b0385458101406c001541d000240030101e4a559503003003440c4602502045c10f400c07101c8100601080c2403401c40 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 818385323 1250 818384073 818384101
    0x721111c0b010206060f042007051b06030c0414030c190807080f0606100918020d1a03072327150307060c0302010e0d081009060b090906030a0501090803 67
    0x2200c0c115130051050000a944440345116580e0080b40d002035a45003416169807030346e40d0441c443c0c5100740041011070900c20081410790304000403400640c00c2c03011700c1040200c540401e6a20841825092000f40610700301c2429070401d40000800310303003550305140300007040c8103650800c568a02080700400c116040040200c1400f030f084110140c64454a824101d0783d0300c5600034803903440707041d98040e5840d4060040c11094003500115606202e500c60345800c68010754001c1c00e60038004c0e0702e040d0010fa000404500a0707859041e0060190040303034509a031501c4900e4280480d07c288001101072161260f40e981e059441401c0d0310703d40e2180345041000032001c00200280a800101e1544c81000c0b043d41c0c011400d041911036504144c188040d1500b0100d00412107440d00420324410381c00100555078001e820148580510500f954410751149200815544135108116445c2c1c0103220100c200d16040c0b0545500000107821603917041c1158844900b59048030b031040ea02c0280010908c0451003400c04 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 818386573 1250 818385323 818385341
    0x606170105011a070c1206090c15090e1801180c050108090606060a110d0c150207170702040e0601090b010e0a080c010c1104060e0a0f050721111c 64
    0x2000708840d41c5090070140c0407415031800c62030080380009042c000c00904030450b10180900e4490ba0050729460314140e0010300e074401c0292075581a5074000101001e04002408400d40340b070f07861541040c0b070700042d840b510001510000b40303071341444541c5c9542d4500740316150900c00300715800c000404803400c03d0500b4001913001141000003140801c0401e0b44005a001e81240080d22090f568901902c422500550042d4928416002d0960422030060348842a80e0b031190098145001514100c0074a108a10442400800ea44101d01060f440c08180d2005025802d001400c086001c46c6a000c1c40c0e070921009800c003070a4a680c0b01003120940d43d2100c0210000c0b0307000e40303481080c2c1e402c00c8002907586940f20348203810000c090001234204210a52a40042c143c003400174484191941d1040d103181104991940e080c074601010780380440d42500400d801080d007529514000c009100c101c181c0c5164440500707000384d4a50342890070410065005205107112101900040c0d22220042c00c00e03908400 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 818387823 1250 818386573 818386619
    0x12020d02010221030f0c0a090b0a0c06020c061009051909080405030a0b09060a110313170307090303110705090f0709031e0332070204090b0406090b0106031404020d050c0307030606 79
    0x4420b51f40015080f00ea0f500a4401030110030b901c0d01d40c1c0c29822502d440025000400d85800415036011070755000800f1400b8540742d45c6015001501e4640e4541101c404890310039080b045071003181c0b0909074036840007140c40c0c000c511180c03400342c8a2010a1030041c01352011a800c6040c031003042000c000070301280d0307004034802c2414800351000c1d83c1110054000609602144070401c02800c0410900b040320008485100e0701503030312454021800f0f02250610f1005a002c203500761215418000041420360603140d00a01000c00b680311911150489c8800410130f0082c80518080030021850307800288007000087d0300d4000d0020a54a0000c00f5548451681982d92200040e040b034040704444190484807100c849241e114400342c00010042e0000e42005848901a0350620040c81610b0b00022041c900503002d40c00240d0307031203c080f000c0381d000395a54900425600003103001803a02042e0005502d0141d4101c4400f5841c0100103814000e842d40202c072215950042049008076507114110b00201030 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 818389073 1250 818387823 818387827
    0x1e050c06090708060919030e03030d0c0801060207140a0e04030c06020c0a030e12061503071e03290712091a0906070905030703021513181512020d02010221030f0c 71
    0x160f113603420514981b80102840100101c40001e43c8041068940b40b481900003400720f21440b42c80500803203002c0c051240107000301000401c5519648140b48600440581000812072030034411400d4500050011020008090803010111340c03140040c110003519400603100d40055881c02909482c0161000750040180c1c8100764880640469000c0d44015200004903007a680c03000081d0030072030b2a0b040280c0310242e11501e81030421800012034280e910420141c58a080d101141c0490396495071400241c4c002490000b500107442203440c04030800c1001d002280c9070380326580d02103183c03c2c0035820103050a8407104004180e034080140035000f048508250b840c0c01d040001184c0c032420203010190180c6118650f0a0490010310210344841340342c00055070681d80c4640781e01200ca030500b00c2c224030190505940c6842500038840d104202c45000c4824081c0c00d001e070b403d0010320300b10203400707034194000e04e040d07070403405001d180c00281100c020b414556a032401900010f000d900242060000b0001 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 818390323 1250 818389073 818389093
    0x91a19051e0310050c1e1c020c030f130b0a1e030203090c090c07212309011b02060307020d090f121b0b160209070309031e050c060907080609 62
    0x4003041805a81d485050f0205282d030758034441e044284600c0c07120b000340104104072940c0500c0080050700c840e209004010100d42003008072141030b402880c00c0d098182d0000c00c11032040c248410b000b403000380c03440f901020015944100c0060b031a000340f94000040740c2c4104000b0602c030808a418002c500307003030500710b0540c100406259621074040c1c1d0b115026042010110b541802841c3c25260020351143c440c2c00d240e2800031075041081c850031903803800300d03035004810b00d4000d0072003580c6506110004c924900742000c0d41c0045401450040303101c0858040d0b0500c090143c4c458000441c420044c64005107140c5406c1e4400900e40c400c603900c07001180103810006e101203219828000403090b00141c080d4403610001e16480b01d80780304d942c0007440b8000c0004810409501d2143d541280a008480d0f1107015900c00d03c0039425103400303100003000500e004030010599900110101c40c011041e103402410001d41444039454a00c0a03144000e00d5403155100300881c031000c102c210f51100901001e0310244107 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 818391573 1250 818390323 818390329
    0x210060f0501080f0426120108070512120307050327010b12060405070303050702060409090b010302010311191d09010e040c06050a3504060c0f0f0207091a19051e 71
    0x241c90300898544840c0c0311021413408a0380d016a04001f40c1c1c0640010696500c460141e980d1055101c0c40c0d000d1081c14884603d60305010480118804038111001d10316510f00f5012034440e40020002510000c41e1074110050b0703585041c1e1400a50b561000000c0c0d82d44804d010082003c215444003c2107a00c02c0703007003000040010a0603800c03240c0c1414550746030a614800074800d4003454208101d410301d410a480c0074403012000060490f4000c5e20100701644008417a41e034a403040c41501c0018121642c03031060020700c40c0a0304212001203200000c15524524002442000d0a0b400811500104011302082c011110840402800c40d81010303498060808c07070107440341c8a10481001882c4061105000b0740454100d05030b4030f10a0942c2543c103030300c0c25187c00390051445c2c1a601c000100301d0448540340901072041085c1e00782d415001829204e01d012104809001d40450100c4090344107040c520483e2900000c1d00040444e4a600c1c2c2d10320350501d018080d0302030480300001e2101c440c582c0307203e030291 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 818392823 1250 818391573 818391593
    0x90e0405150c25031709070303030c030506010804030c05010608030d1a06040305060a0f020f07050a0501051b0409090804052218170904060b0f12010b030c12070210060f0501080f04 79
    0x21444481d150036880c3c9508040c3e694202e40c5102985a0704c18408210704104040b6400054922a44013004110304090b02101110fa040311410301062044002c200030034000d070a00c0c80301900c98400825040c0e03c6164841c259080b45044440c000c2e1103443c25031244030b0507d4411000b15080d01c4081c2000d2842d00c941d40e6406028003a086115954145440360724150307011182904154092039503074000d2441d146644005c0f000e82525154038060101d00c00000c1c886040c558519100305203810182040c1451008000080007120001c804010004042d2105481c07199000c81201c0b00d914210441c00d404029a81c0c036412900200d08025103070380c0095044035504031807a01301001561641d4030140400c000340880d810070f428525000c20712880d0100c0340f00040c94440e2400480d1501a640c40a25180a01082d907041d44100360602c06480070105907042542d200d921403040320b8407521740c441c00b0021112150441071603985036800c20700c01d03560040405500000951440b03007051410b510b410080d0 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 818394073 1250 818392823 818392867
    0x2a0c02130c080115051204080909060d020a05060901170106021f14040f05010f110d0b0a0b090d020d301805010302180a0e0411030307030206070807090e0405150c 71
    0x1013a5204001043d40c2d216206895031001c2d00d007009460781c2440d082c0040383d60801d803141d600c281c0413207002610508200e0b94113000c80c1e5010309526140740c00e001c10807100d0740200c8a40d60400c140501c0ca8240c0303410b03a08529000305542c2c8c0180041038414541030700e104e09c3e81c111404807603040c01c00c0b00003d00c81410456a0007500301345d461554116030b15106001d8000c101030001c6060038681a50040b91000b0f004010750a080d078030402c0550076041c180219400700e0711692070003050034001c0c1e00a0741060680c101d1045c0c0700070315801c0500019075078582d0761622428074030b0213000a44a041204507408403103030030b112141d04044041900403800010102c200e8010241003540210718100c15103040318490402010050004180c5503c0b040d42d4040c05004440a94100c148420800000c2c03c1c04000ca03080c098069000c0c0000b07507210317901958281c1020385400208800c141000a101070000b0b09240180c0c03291000c1d00f4082c4400070b0503000240090400c0316008002c00c4501100c446842182143d = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 818395323 1250 818394073 818394089
    0xd0c030c11060c100501090c0c170d0b03030d0207030206060f090a090c0801061202030c060a140702060702150903151911040f080a1b0e0105042a0c02130c0801 70
    0x50749420008a003036402510304410b46845a20104244842903410081c1170f2426000d007006540d1328014101d40d8440085809001c0002c0c14810450015600005003000740091002083d1088030a0109107182d220340800328086170f01045072020141d0600c1196003001c400c40d48540405040000595402800340c1813070182c6039200e0700d81c0200040c0401010003400f1a6000b00324541d40c402c1249039840088104a102e0302900111400c24544076069070051071169840c5002c0c4040c0c0814401c4a6020402c1640d105409102c4540141d41f40488043c45025009110b900c441c04603041c5032030020000c2c05412190040030410901010164a8160a18110002046200c1600c86c00c030302d0b900c601e801a00004120f0b80000c291214000784120780b0034815501900101207a151540f6502c4c414007840f9805c43d0310b000104203a1034030b40c000142014140e071007007400c88844000301c0c00000d001c24070341300403500c1c2c0c0050006501d011007440a0342c070b01071041400080520070004028060502a0b801 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 818396573 1250 818395323 818395343
    0xa12020319020307090824161b05160f080c0409020f040b01090b07050f06090307050c01030f02162405061011031c06050901090209130b01170c04080d0c030c 69
    0x12000e80704172140c200810b040d106482c840a03c21840f01c0700d180054061601520104002c21901d6402d0180b41c0d0414605030758662814400740c854120030a0480f00c15201f9114800041544615000c00440144112201c190a00d031801c0540da0402c00d079000d10b14802c51038041800c0141c0c0703400010000b0010121170002d01c51942c503006030f400003040d40110800b00d401064410410600042c010619503c000403548a40e449800f01c07a0b40e4031403000c0003801c0d42c102d038200b030066500035000741300d1250040c02c015007440d102005a5010050118082c2d032111041c2d0780c860b031501c034240855001e1400000080c480741c41d01801080c402d071041c055030750030805650b40a0700d10401c284156880403005a00700160002d070403030b030302e030180c0f80d203015180c41100094000034700c2500c43d02c2250701c41003020308a004400d41c800d90200003040c1106607035051002c10038100c08060003c540c000d1060003e02030187d16a8100001546466500301041090110161800c40440c0d002020300c01d0150b0f02c690110703 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 818397823 1250 818396573 818396581
    0xc030c020f06040b1b03090f06090a031b061b180603140103140a0f081207050703020d08090f030703080a050705070c09050604021c1b080c04050d08120c0a120203190203 74
    0x440017020b1000040c111010110a0020035000418961000b06407a0200d81041d11071400080d100c48541b00010042000c9001403440e00721900700c41c494441c003400c00021140400d0b2502c0280c030810720b03002da00003101020016460510030350f24801070289442c0400c61621715070f138524803001c0103002c05807035025403c825141d00352081040b40c403840c0d442141480d04c1c0305035140c043c1003a00512400c400c020a9900011a503510480507100515055070061118402202c1c043d207007003a000c1c0c940e100350302500007a803400183c200004d11415100b03680f06041440c01080d040110340b40034042c0020040c0422064001c16414921802507840c000c40008003602c0f890300040091040c506620480007119600011501c581d90154035044119090034445110341102256003180071551042c0e419002d000c00d1000d810030045417081144246081031520901c45800c0814600032204000614030009070140400c0e400010030101c04120003041d411800d100c1c0d0310408583d20001d603d256268040005 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 818399073 1250 818397823 818397841
    0x915010c17040506070f111f120b090c0d0b0a1a22233307060e1612080d0b0609040c0f0e010c0b0c16080a030c030c020f06040b 56
    0x8600070f1100401a99443d800340c81c2c40380410504040684003044464100c0c02c0f1070810104244185080030803c0c42c0c900c0d501103050f104907825200404c00c2940d81d0b0305a1109072254080c09001300c040404d0799403a0781d00701c1049015100001509802865000010441e25043d60010440c0da40d1020419848161603003240d440d19544c58410301d181580400001101048881020034040a01c08001c03200280c0c0703c140240b0313448005005550240000c0840d0240c52803401040e010800301306178500c0c00e01c85440e100152001100000d82c2d40e00b0000c090114070020a6140c030080800d0f940c000516401c91b182c24034280568080b202c7d400d41c8440a82c03e0315620f00c0304691030600010802c00001a50100003400760402e503240d4000304104566100f25580200310f01c03a0f001d46d0080070000385503181e068194003500301103103040c2da013114110400001444180070705640c0165940008010140c0d12008090b1000c540641055401c904808a0085030100c1e207140e0107504000329a44580b514800 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 818400323 1250 818399073 818399077
    0x409020906042a0e010e010206040b18010e0f061e0106020a1b03080a09030c0915090b01110d020c031e06060411090d08040f05040203090d08130b010e060915010c17 72
    0x30003800401c908290075007594002c480045140001e903201c0c103040c003a46d001603a6450054a0191001d442080041c00c902c13011f42800c100c14020b04004a01c0c1d00d0030903402031414000c0801601071b40c000204101e4658114501c0f500c40d0540c0603c0d8a049514083d4065103a0b40c401c0c101a01042101014101441c08020804011644100c045c4e40e0f41014640041c00c02c40c050108a81120401800090840c014040d01c0301003130041781000e001d10328102104000346609400e081c14000c0c0c5c07400000e2581c070288940c007450019500030300358028500c800c160130324500711040600680344500c6000348000000f0403030380c854015a4006000444014407091501840341c2c416401000385103d001080485400b510031518000101c07183d80d611003003080103030301007168000942d51001442d80c04807445200e0503600a001c40d998620b08090903150080454803d8104c541112030100a000306420024500d03940a02c100c40a50040d282c0200000c0c50b20010000c00781c01d0941c1c0091040000c105202 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 818401573 1250 818400323 818400371
    0x70608180114090a033b04060b030124021902010e030c030d27030b0705030a090501020703080f310611030906090d0302040b030408030a0914011a040902090604 70
    0x30a99542e07240840300a0396610311107908800040c409000380c501c3e0f051580b9034156200d1040160010481c00c111086814000740000c10382c4952180800118400307060021030182489245981001d42c1e80401e180051054500000c1107501440702c000030200d208a0480385554240b801200c286210741c0024a090521035406905009408910250541210321242c07040c10180940c00b0f02d410b81032080c0030000c443c2c803025000c051381c040003d0032107208000840d484031101500265440320380d26260f08980000e5002c8010803c000f050116009180c40225444450320160709201d1a02c0800c0201c5030f8856500040c041d0251000c1c0c000300030268000d13584810000c04595182d103009140300e580e40105480300901c50080b0300341101d116109000701c900741c0c0c0d14000710300c1c91350716140d4400a43d5480208800c008582d07a2420400192410405881c118803420011409804200042258000c1000720302c0c40799140c40a8400180c44410005078032040c2160f000400c050342e40d40502e00244142 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 818402823 1250 818401573 818401601
    0x110c130f09051c02010e0a0c03031110090308010f0b07110402031b030a0903080f0f0105090606090904030201090308010f031113020403020307060216170316020f210c030706081801 79
    0x440300c03801c1c030141e0f000d903102401c5441c2d0007070040d0034980d018991034881100c030203040400880c4062003c2070040d03008040f803450790000ca8100300c001041d41000c44001706011000200301c0300041007402400b4403e58040d01c403100303419250003040d507920442e181f42c440102d8002c640200006888090100c400c850440466100b1642c81c40d08803624070062501c0c010450100d90070700e02080150070a060b0042c421b58416100103466405c0104020241900802c100e034000c00800007060aa12070902c00d50040744a0780022880c0005481c001e4180c0d80142c1100c442d800c0e01d02010404210303030442110360540140c900c9040038084219401c0640310307941010790144245c050010b441d5500042004000791031000b40c6039501d0b1101d03030580b09508840c0d100305281d81709208805a003865442c52001c03d520083c1300007045610314000c07170822031040c43c046440c844212480d081c100d109009465101104401405c081810030304050a20031700a09410804c028804035880c2d03810f42540040d91f414400c0d = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 818404073 1250 818402823 818402833
    0x7110a080316082208010e0f061315091a06010e030d0815040212070e09071d0102010e07090f14040302060f18010203040809100c0209010b0a030204050a15110c130f0905 74
    0x64182d0054480c120320640f44198600047ca200c0711030f0114207503140b120000c02605107520f5141c3c9d1020341c04c0c1c1c105400d036810300300b4158001f4441d000c0d208600030f180c840e160080c500003a499654112640c000e0000b1306009080607061000c2e5404101c40341c0d0100307203041030059911041c3c02d40760b42c6040d8000c2980c0151000450042003a920750030107104111750350341c03014029015800e11801c10815a1100086a01c41400c45603804409101404460041c40000740c401c1030041c0c100d1819031240d200314149941c41c4040c1e08550014001c0c204001d80c1113030019a581025a4002d56440005244c114000c1a03200440c0260215405a080e251170500095440e402c00b41010b520360381c0401c450622038011200364540960040c0b43c0260007640040c400d102580c84c1041207001e99112200640c200f60b0308010206940e582c42001002901101071f0700d41245902030000350030710204070720114660f8040140381c5003550320440c42262644501c036002c110104580490307406864414401441c60007a = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 818405323 1250 818404073 818404117
    0x190309062a030903050607030603081e12040b0610171b040306020d06060e09041101050306010e0306040f020301200405040c0c060f050610050c120705120a0507110a08031608 76
    0x4058110004d0320700400907520217407104007068040724a42d1000508152041c01805045840c030220325031142c1c1d08001d114540390751195442c0b00e0f10002c94040311001c0750b940c00d014060401c061103a07083c001e40d0619049121b84020948105040244220850450344030149000b404004c107032801540e02c91825512440f00918106c06080580a040d00107020034285007018600b01040d203010301d40103080b080441c444103004403802c1d03000401c2581072103000046001d098504000c82d900c594001c441c50901103d00c0e01c10142940c0c5005140b10600d081d0320841702d10008628202d0301110000c072030000381110104015074400010803406024103103005654100a0140e80015204d040119158205484c001000350f5950242245410035540460404841d500240008006903402403049035a032801c0901c80a0701075001d028150000ad078040307608820070a81c41c01c00f5445a030111035818449080c02406513883c000e00558880e22081c0700402d4081c08000e0301100d802000a14030a464031803 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 818406573 1250 818405323 818405327
    0x1814011505090705090613140a0617180706020c090903031608040f12200102030c0405090a060b0c03250b0408030a1b030c0908070302221814190309062a03 68
    0x34400c8688005080481600c6442e09e41100c200707844a03512030345102e180e1481d200e400031000500641c1403080401807050104020804403005164540c020204855488203001100030041d0152040390300510134043c001241200392020072505140c240314680c0d5a04080104004101020701404a24120102001d0b840a107130100c9a03403900850300518824140d8030b00b00c0c482206c91145908042c48144400d140007158030790000042e06000c24410789513a04030503181d101d01070440e9903074400120b22040c1058131700384480e003079194110200c60900503140c60407503c0d002003000b03010940020009043c44601c3d070001c2c0103045403011810b814011401d014004004d03010b03108020440410000508400002d83c1f10241d030790150080c40000003107c2e80000c240e030b910500489954a404000c0c080034601c4d410705001500500f04440c03030480001e000c034100b02206017400c80303465107100c9030f2001c29001050007007190064034000d40a9102800f02440380285425820034034081c1140da101495 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 818407823 1250 818406573 818406607
    0x1203040b040f0303180b150d2f090c040f0801090c270507080901060e060d02040209010903062406030b01020a03050d15291c1a0418140115050907050906 67
    0xe6802c2d1920b030b94103224410041408140d10000f031140c0b012207146ca410071809c0da4014070300010601070b0144007003904005484190222401c140041c008a020004400b0b461452402814003a000b08007000103500c1d04c1401c801300740075141008900c1019000c1000d10700341c14080d0b0b01c40c1c031b0004001908100703500070030104060b68030a48a40c01d00d040410100c425210003406801c0090050f00034540030b9007032002030340140ca082414804400c50001c049a90390088030310750900c0820f0720741c203028402c1a207448403803180c005100301454188181c0c2e00e645c000507020b41090300b46c2461a1150361541d18900031704408901718801810b220000142000900c002002841c02002c1c041c614102060595005002e001ca014110000311172400d804c6e46100c2d0320035a02a4031103001804019900000308083d22000c152809160304160600002e00c900303030b20b0030000c034036084000f840400d11094000c1c3c44180c15020786480b40b8100408204918040d5007220800340c00034000036154419002412084 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 818409073 1250 818407823 818407831
    0x30c04050d060609050a0e0c152a010c05030403020a0b040c0506040803030423060103060f140705070c0f0f051215040b01030c05060a1d030708030c030c1203040b040f0303180b 77
    0x9170b0608011500003146401200d41c00485c020082c40c1c1c1201d074030204044130600c8090018100c81c20071a40000031482d40380b002081802954604802c40003070f00d00c40c01c50307220001031410400d0a0091100007a1702051608045800c8000d40130035441d9030038903c1840007164000e9900610014002640e01c0020003c0d40c801e42c02094081d910700445100345045075809100d18985070080c0c00107200184c01c950000c0080c92104078001015403000c5032480740300409848690105101040c0340781000038040280025102c41c1c00c500f01003510b41b100c0311a0300e414a010740e5210305298282618143c200f00074030703940d81110094010325820f090401c5441c9800a010588400c1040007021503030341051000c90f2000f0180d43e4480b0401d4030f01d202d00007c50740d50b11140b20782c1409041000645521b082000e8401c0400607009907946800840547d403520b00080110302100c40e040c0200070115260260341644580c2040d002c1141140b2490103d008003120303280f001030103201040803014055940065446 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 818410323 1250 818409073 818409089
    0x10c330501050405040809150c0703030c061505060a0f021203010e010335180a0b0a0f0e100c03050f0408010f140f2e08030904050610050f030c04050d0606 68
    0x550b600d03003092100f5540201e03030240c0710031020080341c141810300d4407841c0002d180c0500c01d070b07003442104441c05003010740325030042d8002085400f440e000c2c07040c030b44102c100f40e111b410121000c207450440800c0c09030168400c0c4606001c0310311200701c1c88074001c0c0440700400c00049a140c4d600d607101d00c40c00f02040b0081c081510075021020030685e0000c040072510f0b40021080c280100843d20780c0860030901d500c41c04001706c1500c41100c0d98410380d104e0340c0c0400d01608821880d1601c41117140c100504012000c0e520500700440907086481680300c22805c014800a07500e42902e942c0607130704058880e03205500000d00201c0000500140d941c13410343c80540100c416690074841c103050080405400c02c02554016203040c02040840d0480c6c81c0c040350412040c0100759241d8080300e83e0b80c003240f42d5111680c807401454000242141c00b0703181038801c403035000c5002c030f0752181c0c01c032000b407001049401501082d44000340d00001142228500c00c06440c01440000d0040681402502e46000500102d22407011 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 818411573 1250 818410323 818410331
    0xe100816051326210702060d060810050a050a14010509070e0604080705030111092206080a050a02040b101211250204060614180d02030f070806090318010c33 69
    0xc510864244c0441c4d02422804181c02c290305034013003140a9000d000c1c0300d0043d0307a032003800040583c0d0600940ca05804c0140e00064540317007129621080c0c5000030800d00a251509901e81280380900c42e000b41510710641e1290a03640c1c4840c0d098603034050807502c2d59480b41c030101d030006003a00001919803c3d25415030080c00900f0010f51581400d0041145141e40711004590b400e85092500e2f0768031818200320480415126603034450300c1c0c1082414034090b42e0541000c00b0440940c20a4064582c101c542611500301c40c0c800300000521100c150b1703106d0000d0031f41380c010160481500c030056a541400210a508082c1c8a040030108460740c10728049020300c0c10404001001c40c0140c80f005801030b05030300450f19103240d50590000c000700e002401780c0d021890766140b00c0581c40070488169500041c50040903036504250382e0524002c0014480b114a41c01000042e9152801c12500501c46400b82820340305030721302e40303404000c10050319011503644070030078020034640c4d0990071000190410468200 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 818412823 1250 818411573 818411593
    0x30301080f070b0412030c060f0f0608031e071109071d0a08030405040902280302091f03111c08031009060f0e1b03070e100816051326 59
    0x40c0d1615494480c008000000348801c0140c0740c1807404103036617144039260504c41308141e87c1d5003204960003500007000c06507035118490070400360351003000080c00303124004500f07295545240c5010b4081c1840a03609038540440e00208200e2071020b04640440300030f20105080c500701030b000b40103200d692030405005051241e503410900708030300843e05550010b0040c1d403400e42000c0500020380031641c0300b280c1002c00d40200010a0045d814007504901402c1e4000810b41d1a41c01003144420010b8200107006160320080c54245854144001c01c981c0d000e601103000c920800c2c00074542910703240040900c0142c1144207030410410030010b40c441c0008004007150240c440c00c0d44400c0b00c13068024030400c0003481800b0320200440e05c0c45c0c01c0e84102e205015200006c4d00700c0f0144801d803c1900d100c0c0c0821184440342029240985544c0a040501c0c5480411460b041c0d1502052840525454090100c0042d02080d98240076620002800420011a00000c2d4520000c110044203a9403000c00c0c0c001c0c60720103 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 818414073 1250 818412823 818412853
    0x106030506030c010809070810021201050a0b090409031716031505060315040b0607030305060406050d0b0f040215070c0510020607120c030b09040b04380603011d03030108 75
    0x58014100a4000c00d0490381e0503006681c0c05c10302505103030f05403090385000101414100088400151024805030301d544680c0c130b1442120f081171300058401e5100703200a0002241400a88030491800c41700450000b0240c2425110600030120000e40041c0c3c4508001115148000000e00f4244c039503010040d00b01c24590100d0002640d00941da4800740c204007240b01c0e1400040c40e0b0440e034400400c0001e001d054440091401d500412007100400e07210340c02c000c1c3c0351400348614002002c007a502440700354a65a50260460802400803103a08842c1001c2000e6484861a18180301e13070f4045410703515803035410503400310007032803203094428007440712104141e9102207290390040c455602d9440216092145840160001c114180c0070142c1d650642032056860704800750081c1e0044c6800032950500342400c07000e0400e0301071031041c00701c150f02e8031b071068000410341009419101d00031802c0e40e44400000a0140c0250780840070f101202007404095104040f0003941242d0314041281c40d10000c0c2804 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 818415323 1250 818414073 818414081
    0x112151104091a27100b0a0908122503030f060b13050414060d110a0b0306011b0c09020f0f0f0406021b030a11040e1b122d030c011b08010603 62
    0x1000c182d8803503000d54081104c0ba40e8681904040211016001241c44080240194010203009030025020b080d0820001a0500943c3d50b2103072100c008031315002d404e4a01003403240100000074130800080032441c060500c2580a1040036030a02c0044c031229695103800c1909400c00b13108080e0507200b1500002e0140740a1003021a00989030141c01c40c0c6940d0201080041c03a000e000640d824aa00d0781e503c3c240d65035130000e03c00900042000d20b620380c1024400102a4003100402010030049a082e850200311000e000b1421a5800c0c000540c1d25141c21711b03042c46501404c1040f0407000303004105150004211b40150040e918581d080300c48010040c82e07103850541c150700146030190040e190701408105441c1d100040720b00c0107400441e41d00350006445141a40c6030b0f030900710754070651104014130b140103404040032102c140700805041d81c011150504a0300c2030190b4021304040900344100b100c00c240103488903524400001c1121210248116802c0c0b01c3d4141c03100b000501d0340e0000b0030344a0080c46 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 818416573 1250 818415323 818415349
    0x319050901020c011827141e1b090a1a041a0f0301030b0c160c05010e010306140f040917070605060d051b010203041e0f09050112151104091a 62
    0x2072000049854006e001a80159000503000706141c003803201c54007100035001d003201c840b60907105e540b814586110340402141d0300354000c5000c80c0c2040103000d992000b4441d1a210079600402482c0d86030505800200b8244140c0c0c00b86000003e0080c1599440150a000c2c2044400300c0002d40c14081d00110301c0940740c45207402c140c03500031081c0014004200203251056000800030039017894800504000103140d8000c610849a9a4012500348a1f0f964401d102a0b03d100003030800340841c3d03040002c105a41c06201d18100d0141c075000e04030046550701d0f60005100c0c55080008203159510254150b0445d038062441035520307a02b80000310380300b803c000d460040102d0f00301019110b903110101030350400110038900e01c3d04600c800d12002c1034186540c0c4c0d6014101d60007601407084c080c81d007002100c0400c401d81c06110306600d00b50040181c00b100d09242844143d004440100c9000544444001861581140351120b44c012801080c6c0101070780c0407007181041424811702c1030f01101c0800140340703603401c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 818417823 1250 818416573 818416607
    0x16270b1206010207260106050405090a121e26071206060507080a08040303090c0906031401050603150a0908040f092018030f0d1e0c0f020603090319050901020c01 71
    0xa01010500b0b80103590f610310413145070000c20000d5840723002809451082d2501081900224056405c000c1c1c0603280c0e103402d00890601c141003c0e10400f000d483d040d031412000003070012442403505403609950203002d04405e0001d078002d150609000040440002c3d00b556008145003290200340940200705032000298025812403500a018008031040303200078004a061541f0781c4000e0f0001450701c03840e03e0203020403d0b00060410b280d0b050485107040c4c00d01d8071a007564501000d108907614045044440c0000684a02c1050386403d40e080b401050041c101600740900030034003044e01681c1c580c0c040100c4018070010310040d0030704c40480b880b15900f00c0c484030300c41c3e1080003401041910810102842c21004041d20b200b2003907903134003906200e0381c031111100040c003100854084642d0501503d140d10401e10348865030317034480d0b5074452410222900113840b400c004800100d5500080003215250030040720183c4900c52403030b40141640e085411000e001d409541d40880c0117510851805c0c420303030240 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 818419073 1250 818417823 818417849
    0x61706060102160302060a0e0d0f060506130603080f070201021c081e15010e120f0102130b0408101d16050301110c06060d080702030d050909010504020316270b1206010207 75
    0x10101540e0100818801e00c9d0802c4080522002042c00c0644488916025110112751440c0140411601c1460100e401188514298007032011a18500c00c5d1441c16004086140c0d5420503400145c0c80c2a00c0054240c99601000000004c003d80c0721610300e00945c40b040307441d00070086541000d01200d604661041200751a00ea24810b03e600c076011620092030080c01c0c6980b1a12019a5103090084005901110780c1d0000b5181e1941441d403c1000024840ca03885241804e040510307a544a21501008181181c0c0b1400d450080c0343c460030080810310708401c00c54501c1a10901000b00001280c481c6030f00c01e5180801c5c1196040031142260000c8800c040030b092140d07941d504009980da50704a064605590034000e0f280162000c010078000d600e06e03a2030701d640711103003001081090342e0140c2115001d81d00520500a8a5902614641018485003800c0348108505c40480750a20050b10f005075810001d4070001480090f00c0c4002d01c0018032560444030a50744038801640c2e5143d0070b101d182107808803 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 818420323 1250 818419073 818419087
    0xa05042013020f030f07090305100f0f0606030b01140918090f1905101e0506030c0a140f0906010806060c010209040213080c041104150306170606010216030206 70
    0x40d1258050041800078001411040c0d120445030498100c0c520f00c4140040000610501011507020542d03c5442c500e0400e203518219078405480e800c00381041c0d0f440743c1d00d4030340b6403104080e107400006401450b20070402205940c2c400043c0075040c02000380380480c2c8500d08140388451000300701c903503501010304155826209d003d10f210114100401d043c00030b0040d0050264005800d11030300c0303c114400c02e01c461500d02c0c1e6080c9203060850002c3e014150f6840c050b218a8480c400d403e502102d9404000700080560761075010171708100491580700d070301029004006c12480c0a410681c00c8054060f10003102210741d810511400340d605481103808609844001002c0b450103070000e007507494050f0005810715451101007016a00444d4228201107082441402007850802810304412001c0300c042c0000c2151496a41d114807450180e26034103501c4004c0f0305c060381d003c2c1e0001002051101806058010303400100c1b601c2c2c00d020b6641500500414401781d69100480d4441e105170307900108090b26110f5 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 818421573 1250 818420323 818420363
    0x5090c06090310020d060f09020403170903030c0114011403031c0e10090510111206060c0c060708070b0f010b0316090e040302010921020c040c021f020a03050a0504 72
    0x80070007110303450700c244107801d6201030150000d040706040810011400a0500c4200c0d8042c05241c0c000d038000c14410b000c1000401d446a6072561400c41d2444520b54aa40040110f0305610400034414080d40c2008a003000c14110b6140150403150fa004c1c00c2030003070415104060300d134815000021076a082046130300d080003400784d02403079a451102e81144d40104100b044d00040d00c10020041e14560444030485550080d50300410781c0f051511620356240142071a02600d050304003901e0759000340342c0400d0a1402034000c0040d504400f000400d80d540340c00701031038030f842c0c42e5029080c11100c4900640100c0c500304080902036068403410f41c255400c0d59503141800c020584120703030200070058a408000780e910004030800d40101d0081c0c5c00462294042c0c10403034899070328100511000b14580316004501540418000103130301c000c0750042485003810104a11f42440b81110040b12019600025000d034081c3d8010712032090347d910700f0f005d01c2c7da41c6260541201e40c03c4501400c040c01d039150344080c6807 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 818422823 1250 818421573 818421577
    0x170f010f110d052208071a130f0503040f0f1a03060915040219020d030e160e04060b04020c030d0b0301020307090306090f0506090a0218160f0e220c0305090c06 70
    0x100d40131510306101a14600300812000301940941d0a0360f0001070b4171040c4040c001c0110312014003c070781d001403401e001c2c1051015441500c1e01070706075014039100314200030702881240c000f0480421080d404c1500e4120540401c3c100f40305251144003550444964003e441055a110b004001c0a0a03281d40d10801441c20b604501100154000c0e420058150a880031400800c079080740ba90041050b1402030002400700c4020040c0203005501010906d542e40310007403500415101603100d851403640312450603c020705840da0740c059010340041110110140000f001c2e10005220303503000d012000000003403600300d00c002c2d1070800004010780818000321302d07560010b1581c10302c101d468004514281d241d240c1484816140009190004071140c0c0561030310301700c040541c00240301042c400b030510318400d0100102c074540c024180080c0044101c28240988403004842d100074100244601c40701c80c00041c400038203401c44860616241d00310300310a102c0d00c1014411118070000f040d07d28101400c010300b84d = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 818424073 1250 818422823 818422831
    0x20c0d0c0e0c040816050f0f1c03020f0d0e1e09010b070317150f04182607060203070f030e0a0605191a030105090615010315170f010f110d05 62
    0x101c41d0810000540040c104070741e1000d1034170003441c080b0003803d00c02001400c2c0171078400030b80b2680c04000d018400b5130b6900040c00201860024031150101c0510b4141c1c2441d200e404182454090b45c482c407120729030041000e0090b4402180c4010200721650b620000000d01c903081150031240e00c0005014240c200d03c028140140070b4188240d0644d4098203400c00a0400c13900d02145621442541c2d500703051605c0100702800080340c00f070113504c0c282800322141c4c00e05000e0141c000e0650032820000843d10700310142d008406a4001940d850b4035041c890082c1d481540c0000c0000c00c030b1032101d48464440e214a0340310004020150000b0700705611001302030003000d0465009241990904c07a40c0c9a42ca128003075010305019001c4180c20420300825085400c02450781c042500540d041120001d00701d4550344da1402e0034280020f5503100c03e85a542c4040081c0c0058609002d030f0700c007008400d10001b98503211401c000300240b0100c160f0a129805682806406804015090110582c40d1481d41c11181e0703c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 818425323 1250 818424073 818424091
    0x9050d110601063905120c0c040b040204030f0605060f0103110304030c050c03070603060e0106090b0706050a0b09040501020903010b011803030531060201110412031b0506070f020c0d0c0e 82
    0xc4100a909400030070243d00304c04440550810401c1002c100050040c0c00c1c00b220201c4010341058141c0c0051602c030903980c01d40074070542d980d0703818005668450341690041d60300003501480204141ca0031038000c04094031014410140507581c0c1660398468040c02081e80c0100060a00b076458940d02617132441031207402101d00d8010011210a1600c042200e82d0060401c2d50340814a103140041d403a00c07908040c0c00910800208940c2400380d12010004c941078540d001c0000a020390329036285000504483d41d03072680c000030450034401448415000b518004e07004400810040144100542c1c2a1049405a04200c840d0000400100c0e0242c0042d020b00060843c0c0e9103031002d10f10742908482600194507201200c1004d1080c480c8a90921641d51b0f0404a80042442c0508003c065a5988010320008042000c0001451a00c9514000c088a40c0e94400201c40c400d0406080140021303184541c0100184a4540245c400d4503120301c41503466030304100304424850400401d4521002e004007940b41c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 818426573 1250 818425323 818425367
    0xd03030b0301290a0920161506080f0106060806010e04090203030c030301030c0e01032102011e020a0f021504030e210309010306090902031b040f02040909050d11060106 74
    0x4034a4110300840368800c07200d0341c1450340341d803604029907007100c0d8114111780751501c1c02e022855643c402c0800420350480700340c05c0c1c99907000b4920984032401c20301d0042c00711540807880c0054503140e070400005c0d54607800507640e003100904c032102c2c00c80c0c03585c0c820300d00042c481101107a0740d5401914100d203c0e0002800100e64040c00c1d80200e0300d554840384859980e94400070040052004814094026003d190b00300440c0b545151a40c3c031405d0004204000c0d10303407040016100840c002d61260254245c00c604541e841380710300f80010002d4022910050104140c2410310b543c5500c0880d00c601c0300281c500004686031510786085074170740d23002c0107019003100d145040c401000c08003185005542d0704403002143e41d1010000010261070701035000b106c80d1418401010b0040c0d40120b00e440c00c6050b1554a0000c009440001501034210810b105800c5071002a021070f070ba840e03d410011019004000b26000c035400031208840801c945900325105810000052225911030003e0668403001c1d002203030 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 818427823 1250 818426573 818426591
    0x1209090f2c010b18180d050406080c0919080705040908041e1a25051f0f0c091e1203081b180306060105040f06080603100501060203030a0e010207020d03030b0301 71
    0x149042c0c02e4030f0007416210000030101700c050000000c103102c610b10ba03500940024948841c01410b940150b008081c144461400003611030820001519410000103100800100c5001c8520640010a0082c2080b0340622000400c1a00b06030081c1141d503640302c2c03012413420780360140890400d200e11740100500000c540c070008a22034059a21900740c1303882d10081c2c0e030b0390a00d044202c4040c0b0582c064640391040b2141c07444c02003800419020781c010004a9140b05150107400d0311001081c115410ba414203207840d8800c507606074400d90340d02c207596000d5010700c44000e2148807403100007080c4c85480d4540e031201a0f9200080d10038002660040043c0b0707030601c03500c08030f02e0140d1641c0c0c000c8001420420041600b00015203420441190801802e00784586010b090890440c1c048121f80910820301c240303403001c80c034291402c000221181c11028410845541c595200940b40d0f0b0041d02c5070b40d40075080001f00301c803520043c404c840505a0061085211003041d80e010703005004401441a419541c0c1c0c2411 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 818429073 1250 818427823 818427829
    0x9011a1302040b070341070501060317071703060607032714181519030501050f0702100e06010501080c070b090309010f021b0603131209090f2c010b 65
    0x1d091094030035284c000e401e05020540000148205030a1407001003c440d17401901c602c4600c86c101c01c080c4000c011a501d01140c00c007507015003040d0340000c112541c2c0016103180c55800707002816180f0703c2140c03c0b0004422180703400103140426150943d000c4c3c0304020f0319002a014850000114001f50560350000444400c06040700b40d07213034461030340c0c080520700e038104900d40f940841d40d8125602c0c280100f50b00f484503040d810380e20780034016070041c00c240300805403007110700410030000e51780140240060300d015405541200010340f480005072055005440014020740548075910686800901c0142e10b00801141d0b00710029000e0700640c03000300308600120702ea2a03402c81c803581500d0f000355a0b4000440004200b491042004401c642107600b0050740c400141c1111808200221066074582c0c6806102d4207001c40d005000404200c0c40140340900d0a0f080003181c800c886456030101714036520076903c6000e4230048084d90500001c005481252265a0761004946a12900000800d8580b82002c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 818430323 1250 818429073 818429077
    0x81909050106090509010c2307210801170303190e0d0f1206030510050601110d0c0c050114030610090911130b0403170703020c0d0809040509011a1302040b 68
    0x4280c4040c0d445840a00c49030029000e451740054290008100783d0428a07802051001d0003248096000289500c6010907150402a00d10041d001030016a514014190112980e500c2c2c41100300407a0031340000165032803900d1070020b44466441c0c003852035a81e9440003003001140803080b2640640c0d032810403034012101001141d440130320030b0310390319112000498083c03c0385440b40310001c0740c01d003000d03414000684046200744401555101c0881c480d100c01c00140d84903000200300380340d035210f190f42d207010540d80444100313001801101c10000b420744032001150f1441d920042e000d004501080400ea0604188c984d0480d0210701c0e18101110980303e84003401030710703038185203049506404201c1c501443c201450304401040c0c01d1110518103440d681d10070340d0840382c00ca011605200c010514030f082c140280490504400010000301c48142c451500744901d40003204080d004a10303040c0040c40d442030510540f201031248440c130b06120910031080120354800e161100303113202e800384400140d03c60a880 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 818431573 1250 818430323 818430341
    0x150703182f060405010203040b1305280e391c2405011d03030d0207050607090e0c07051c0201020901110d0801050d050a02030f030307020d02011b0819 66
    0x7028000c1121005000c00e40301c110480d51442400c0c10081004581e0b0000112011a242c2c2d4541d107427103242051502c1c0800b03d03103500c043d41258440c1f04180f0612985001d14030b5118071070400100107600c6905a80d4614411241c4407200e1074a40c1810810396090002141071180041300c803e11480f18401407480da8101131030111030b034000d400300344620300250700803440c42e40428000d180e6024280d8002001c950700900c100c90500c001000c007420140800d11071044d490501a00300e959500c070035805500254001c00060b9020300481001c44d00f01886046590100c0340d0000300b00d045a02e481c2403600c21a840600200d5007807042d2235040032459880c0c6c8c02c102d0100501d800040c2c81c3c0390400d001401204011090300c02a40140038180140b681010903241520800e6a200a40c03c0b0940f1b0081d00c2c14401038400303541489403840031545031000100442c42a01030b41e080d108012034241043c0c2c00c3c0c81d08d20840751507290003212a0300340c05204611495000f42041641c00b8041040c00100c022186218 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 818432823 1250 818431573 818431613
    0x92d0301090818011b0b13060204061223060405070c0f0c030209010b041514040b2205040213090c0528090e0f0a09030207090c03061715070318 63
    0x803600740d15900f24201d95500440080c20b051084a119921890341c41841000040c031030090311020541c940c000000050130140d001e4811961141c6800000c0c0480b80d04041c1d0240d650b00f060402c0c00201d001101c3d1581d0300f035600080c650562622402c203c09014000c06c10420000c00d80720350800305d112502c0c00e200c81401185002c051504500520501080c160007594070031004020401083d02c418410710034042c2e940c0b91001c4805101d03c110003d80c41075a0141402050118075050320002881b07030f481d0f4000e13101515811407907494060000741d005241012a084103400d0040009083c140c000704104a4245032162802603002427403004106030036038109008038804804809035030001c420074041c0c144c3c0f002c811204e141031800030040c0c0c4001008150350300e4444030a00b0405000b000410058103802c00d0502c261180c15400500400b140c0c0710700f0b19051410340050355011004104c580869800c1000e00340c00707a1350060250082d14031009149245001c016861010500f04008000141010303 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 818434073 1250 818432823 818432827
    0x605150616050c270105041b030903090e070f0e0f0a0302040b0402070c0b0c010b011d01050a0c080c030a17040c06051303020303030c0c01050f07022505060a090515092d03010908 78
    0x20030210300c20088141c0100d401903240c004440300158030060546623041051a020071810b803a803030110b4407210141e01c0722032400400028811141d81228400088820355640d9500c008400d90820080c407030104180c03600040404401c0c40507007040c0e0480d102e42c4030090300142c0381561035039a1710300d02c00541c0c0c0030b58030324200841d49601c02d030001e0081020034042403a1400305200d0f007070002d01d07841001591160600c42c00040d2819039074011081ca44015410000c0c1c617403240020340310140c895201440160000d41c0c5034030941c90280140e00c00600885d0008502a541405e04a00f500c19911142007030740c0700451988004010b80c0e04000851041c0c0304405525251940080a00e0035540c010741141d0925070b0540030403500b50740c00544a00d14203540400900c45610189001081644641044d030f0021030000d4203410258000f6020011640150360000d1150080e0056603100c3c02242c08560b44140003410281c850004105a821000f00c00280c400d00040301d070b03000a08491281c1000c407049000 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 818435323 1250 818434073 818434129
    0x1b050307170903090d0f0203011a19081e07170a02090105031f0c05130b031b04061407030504180e06010b04050d08070f0c120605150616050c 62
    0x1002001d8200705035000000205400d241007955102d0066002c0b0307500a140030150002800100314604042e04d4000e402041740040c01e0b05150300d13890000059038021402425002125048d140c24a0101d800b15030280c2000d514254610440c0d410300c0000d030385648110700c8007080407030b020801c2c03075000c0c074203500180046461841404640b40d41603210034881c1e001001e0741880c00214001c0c8504400d090a40050702455040d41600e041c02036840c146030340001000b004c2455007041c00198055035103249000f2141c0362010702c10515102d24025100081c07200c4c9941980b41d00104064080c20b0b10900b003031410586c488045041a00221210b6001141c8070721907207408620510a280c0507102040310317030b03282a00300030100d014500411030090542034001214000d1002201052010540c0000c07001002c0e0f81d1002c8035032000d65541c400344c42c803600d000040350051511245000607150003508041c00c011904441006c2402e140c803003a5140c1c01800c0c3c1602c404c1c3c0c0d41404410300009425003080e0200c070 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 818436573 1250 818435323 818435327
    0x40f02180f01092304120306120303020c0c04090302150a110a0203031905010503120f040503010c181d2701020301180f021e0a0c23060f0105060316031b050307 70
    0x21200201545000603038014581280401204c55016030440b000d15000d9140303100c210000c140d0b81d4030060f0084000090701d0304043e4542c0003008420f400c00304442c00140c04104220484800365401070140e8461010f0b00300c0f407a0107640c2c050303010008030b1000a02d80340a1314940350552080d1032502c01a00000100030311500001c181c414509440720040000b0740c1090b0101e980d030401101c40500c40a40801c0e090710701c80b0602d00b1034025200160003800903800c0a080075009580303000d5a104450300d03030040490040c840d444d022195440c0380030840f160303450382861810400c0c000b01145408044080110034602030900003940202a044201c8540060002e141c0c01100c03028820000040e0040140c2c00003000b104410360f942102c03000c0036070380c0d0b03070030480c0155680c0c10040c20080c1041c82c4003d025001407059014001800c0600c0309666a6940d60184107079503500900a459100d00144049114854444000c0e00803600e02e0500050342621520310358015518035481800180d0000204042d0030303 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 818437823 1250 818436573 818436581
    0x1303060506131401050f210c01080f070516030c020d050f15010e010515070b19050c0703020d0503100b04090603030f08090316030c2f0d050303040f02180f0109 70
    0x3007400941000040c1c40158405058001807042600c10103034070207103201d103a960f01a130342404e690014515400154100407142c82340c000f2072035217001c07440070700c00501022180c004140c030030006a81c41a280c2661190551016104900240c04120003840d465005880b60507980d03612502620007040d0015035038403460b242504035840c848141440720010030246020000c400e054400881d1000d41490b00c07a10008c5540c007520341c0c0075000618000a2205c1549200c41d81803000390003210034452641c072010b0240403442181c90090042e4030902200e40890304c100040d540140055000b4143c0030f80d101203c6081e5042034000c1e103111a41c6107410410142c10001d0404440c00c40c0c10b240c03009280001005440c0c3c000d4030012003201051516a03410107214001c00385c42264040c0e80681e90300c3d40d2501c2205c200c803120490903050012084016120719140f448400c20036880b000540c0707540e03196030701e94008054148049030450303002c064003226041c001140c188900c41c10041d41403150701d8070940400303072 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 818439073 1250 818437823 818437849
    0x903012a0c0f1202030f0d050403020c01031a01030f060f03030203090f09010b0f0310050901150f14090f18181b010917121903141314031303060506 65
    0x120064080c078800090340c066005280c2e039040342070341c860642c4603942079045100b040201e140042d4001004c1080100980c0035501640c080d03800c81d240a5130303850065003110049800d09a40c0254040310080c95032094100e085582000c0501180d050b5a41c0404074400c042a0821000750700040307031034626410310040103540100221a4078885500d07100d41070095228905020038041c03000400a10001c481c6d1060100a0001030880003056940300d0b1408112101d41070f89c500010003c03081181c4c031901c03840c064001006001c014a1804036540d0801034510440c0a03840d070424032024038604018078005900d44515481ea640e281032000050115081001a120550501c030b01c03030106003c1c59901c07581000c1543e414261050002c545000f03040c0c075000700601c8500baa900c00094440081000a20521104560b9181402030b444c0c140c41122101c8011245602001d100c00c070303284081009500c0c841030f140000c400b030b41ccc607081e0548071000045410760410b580b051740f42d409001440c24850b11051603 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 818440323 1250 818439073 818439077
    0x290d050607090914160804060603051b1003060b090607020a03150b120708060609060d120906020c0103050910051f0b0301030312181403160b01150c0c0b07080903012a 73
    0xc1c80c41d04a16050158080745e8800040003144070005041280e141d1014001c0d68201003103a8200d207002120f84210610303000310301d0090134a114030401c810302900a01060b503000e40340b050b0030020794500303000c2d240d00a420b05a80c06030006000001082055003a00c0c80d40c0414503021407100402020b0280e810518800b402071540181001c0000c4100441ca0302d40000044aa03054107844010005041c110f20030406080c081b13903003584020844e00141c500701210710640070b641c50944501c005404031001145c1001d440e0700200001244948582d0001c0e0388081c01d4140300c800c901000c02031640d401e0b043e8010705102c000000041c02071607007080c1c00a5072029245030600c82500700c908140b4a0148400d001425042c51070840c00116a06005407102d2403440c084451380300c03515041c0307039075005021f202e40303842207040c00700c200c250b9031250039443d078101d8114406e00d805901d41010740520f43d11003a410742e2445000e114141c00351350b0038029400d06e401c8500440c510203d20040507043c1c1d9110644000c1 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 818441573 1250 818440323 818440361
    0x6030c0d050d0c081c0f0b1806150c03040314070b16060e1f0911030313060513030206071406010f080c0f0310020406080103050c04290d0506070909 65
    0x1d280012503010b011440c1c5042504201c89150440f8140941d00585803191152001502036401550003985034915086090001c1c0c001c0300c05022201e940c1103c2c207036640b0341c0a40010b40b01d0801b0111035070410350104d182031402e1813031007041c3c0c11600590402c807a021621041d0040181c0204081ca0107032030350740c000624007900b1140560090101d8000144100c0d21860f240844142c10311101810f901c80d440e500d600002900e4508000f040130030b0040782c000f20290307074400680c01c000059034407220b5020f490031043d03420100c00b40d400d80c0124120030800c8001c6800800143c17500e2002d088480c0c800d000d1001100c002584140c104001600808507042078010100a010780c00582900340340300950340100c43d10480d5021a09101e03d040c1c002040700e0000400195050b4400740d128102d03800385065070403442d000c02c100816200348260280e030100c07603c804410302e211309460240010400a2407112015503d40c3c609050060488480f0041041c1c0c1c4400c02042c8030074080c001e200d00502144103 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 818442823 1250 818441573 818441599
    0x60f0e010504090b030a020423090c09040b1005061605100b03120706140411090106110703120c0f050c01090b0708030c160f06050106030c02010203150919110306030c 73
    0x7092030045200b500340b00e94441501c06000e45061100e5115140c01820510030313403003040540c041005007880c55113044445240002c0d03095001003404118600700800c0820241c0b55520381c149480805801c840d00021035801c001001e59034100207082c025204204424269080c0c1403150030012403440140031a81440d012900075a00446d0b00504000c00c40ca50a40300c11080c1088001044161403000c0b8144d0702c01e05000c14081043c100c6800c2d19021100e081c2903a0321408100c400842d080703006025a8410507041c40041c0740170360200e80e4540c19287c5840641d0b416155100320040c5010b0640b4250001c403200300c01940c0c002411b80151007107060007440c181080c1d503100d40340d11004003801c0250360040303600c01108040700d508a0070580c0050442041850313070700300100185828892117001c80c1c0391900c00c900490042c002d90384101c004104074001103482c9014070818920013480c031403074081c005020350b10310a25032051901c810000342403a5120300d00507080c0b510308a08505850f2140c0c038440824 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 818444073 1250 818442823 818442827
    0x40201090e070804021201020d0906020408160311040207021201020d0e07210803060d080409050928020d02150a090812030907090c03060509070503060406170309120c19060f0e01 78
    0x25a042036055410041981c240d4151b58024000d1000001c0b03440e0902e6800424080183c01134400d46148000f916a85119218583c00c5c03030100c3c2c880100455500104082145030a40c040d0082600103041031074068170081f86642241d0000b10707500499079941c1440c0319045002c0050f60081c0c110405011080b0144500c00c0c8a084081780340184000301c0007001075095201c803603184500380c2c1c0c00884142c0b156201c141610107004100d4400540d0b10503101c4001150810900c4c40d6103a00c4030600c8208004199000c1c030801000d010000e0340c008441180c00fa04200c1c6902c010081054035a460403601e90030402010304160b0340240c1018850401d0041c000c0c640c2003c00c4a40440d0302d03801e00090f0401601c130003603000d40013030360006d9481144101006003141d00107004510454040710100306050b04d60003043c1c0711090720b104450700c6500a11610056003008000640c84a00b10012141494002c000154481c410041c556000b2109102d0400020f070300044110b03070300000e9080041d41c0140103400 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 818445323 1250 818444073 818444087
    0x80102030702150a060503060f0108011b1706040b121b041a011107150503070e0a031101141b010605130b011706041d0706091a0708130e0f040201090e07 67
    0x18029500c54003e0101c0da14248907440f0200505026041e05c0d40c52038074110200d01100c0910441c0d00c05c1d403e0150740141c5131b000c40403844e02c165039a00d418426415458101c4980d010003810345402543e114102c0e1000d0780c6006c1005103400072880285006446d140035255020100940d160280341015a01190344031078400410000d0002e1805545110300b040c41c0350b05e00302e1035510140c5100e10900786400c030365600400a41c421062a1543d43d00846840300b0705c5881000b52101401101c0c4601044515600c248401001e41d120018400d081140c03000140d020f07505602d690400d646e54a000410035030401c202008481c00214208015510018002a0907007800340c0025050780c8102c0c0c000f442e19526948620362001c0c044d4000000302490564a9a03240f401d801000042040301200040309425540b6804c04c0722a0414a103050200c0703995841141c0d042481c2804130a0800440824141800081540700f07410320701c020300d40c030f04041c0000f4000070001c0d0005400d071400042001052500020 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 818446573 1250 818445323 818445343
    0x40506030408070804210b0c031003231c0f091211060c0604030c0309050a0f120503070b04030203040509060909030a0807180e01031a1b07050c0a06051201080102030702 74
    0x100441c3e442c0d5481c5007a00a610540c0c0003550407007100d59450b0349102080b460b141556210343c00b000d100f41c961042c1c1c0007071401b0071245040f0881d03600034244002010010300035002111961006082d0441c01c0c07085040a075002031a4001c000c4024001c0061540082e902081c110070381405034030b40741098400c100d80c0d5203082d4060301400031001c0c1e9003900c1d250001103440460108060311440c0c2407520300101a661080b40682c002169103a0102d09407903e0320005048850700709110010500d080b0385111010968070080c0c81c24003040c03180c50049080c05842501c03683c801c3c1c2c00303195254141410061004809803581e0702540d00d45080082c5494000111200c410302410000c405a58214080350914502f400940c00310380d4007880010710a880e41c0c0300034113980c460a092064440310407800314040d03100711413918051043c004100c1403040e0450041000e14091002d40c1c912180c014041540392500354044800220300007040428034800b400307054050b001d80d130300039440c502b0140c1d8000e5036842104 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 818447823 1250 818446573 818446583
    0xc02010f11070e040b09062508090c04020715060b09011b380a090c1806030b0c0a030c170c090a090f151205070909080d1a01140405060304 61
    0x803140c0c514004041200301d00809920783d9280307a038901454a2000c0360402d81d0305001e58826038020a080071809107800c400d1180d0805c0c1051003500f120000ca8085201501d44003007402031441324100c1c3d807a18001400900c4c0504103078a141c040c0b02d54000b003290400d40c00500c0e42802071194101076070744407081d00b12055000e55013101120345030a003400810f2031020f101d916400340c0040e0360b49546c0342c500c18650740c0d818002c404c0710b50b50391581c0020550342c50001c001d052040e4954280f200c030050108032460440388400004240b6100d5075000701c041c1054503480c00038000483d9951103d0707454000c0825000451400e4004110202e1030100e41860181c02542001c0f400304410304a9114803402100030400800c00744800780303140c0e071080300501c40c00e08418107042c8200e4003c100b08250f00b4804d0f690319404401450890300c0e01b030811000341000c47e0101c0e0011030400609410301464010303504a12041805030141003c80b10016001c075103e04070309205000140410400c650340c600650b6030198000d = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 818449073 1250 818447823 818447837
    0x3040201120f18061e020304080702040c1803051b190501051605070909261602131b020d0f050f0703020f0a0b06100504050d020d05160305010e07060c02010f 69
    0xe40900c0050f00300e010000c1c4680460f9840c06080c456260010852903000c0c590581d00346003410040d070b051744012500900780c1c0d642041440c1c018101030307006400303441982c600303140d2002c0800c1c0d90211800056109469a91000403c8c410a084580f866180d00c44120b44490750000d4079a046200c0225030310860f418081d0200e042100c040400c408203415543c0031045e00c0c003803500c0e104000020b041d044000d41c0c881c401c10398100003001b807501105404210705000395080c11591020039131000c2e000601260000010444000c1c002110f000304001031120035800031100c00c50b050000e02d82601d00920008104910f43c0d4900c1d070035040302c04c9404079a0280e003815550042400e00b40c0c54002415420440340c0305507101c0400744261034580a0151104803680240701c4482d00007110f80c0c0c0102d001d0194800b82001c1c281b8018a8800401c90f0710358131860507035020080381541e41420612962090310265100c9940c1000d0303640030300280002d0603080c00d14510301c0b810703900020500d10703190083c1414403602c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 818450323 1250 818449073 818449091
    0x305100b1c080c01022a0c090f06010302130b091503070c080d021b030c0c0307050f010309112d120604020111101805060601090605160204140f01030b0c0304020112 72
    0x1940b0200d848110f200c0c00250b594a003070503001201c0300d41e0b000c0001003242e991404000b002e04d0100d03800c004490020690006900c94424910b400f4401400e03480c14550308020046a40c0070709403c280080104001c807940356a689024080005103140d4002e44242c020401c200c5019000808189111307042003185d40ca80c070784080c2d4507000388548201c00500300f0380508080c4410400000411100b210709054a0610041c0c0c000e156852640e400307403070f0740019076003c9036409520a03031006840a024005000c0c00c2c00b86480854605140740c130b1100030940b14000d08500816841041d0b0354500015210514092080d10807070362031309030150000341040700211030079255000c10468150001842d01c0c04106001b0380c1e0240502c150300d0400c080310140108000500f066014229550460320700342c036450f140414808603003034608403401040b640250b5030442c07900e001545854440c41044915540c58140d410340c1011441003200400c0d40408040c00c10070040141d900c90200c100c2c80040358804078160340 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 818451573 1250 818450323 818450333
    0x21c0b1c0218010f1e030c1512050916050d02060a03090201050c0f030403060f181403120c09090c04030503160c2d0b040b071515030b010305100b1c 65
    0x20310702d05101002807500c000b00d1401e6005a200c8215100d0f140034020450300020150b909110070701c005041c035401482d0802220b1500a8000480540c51402e16100c0701c1030b04110044610554094150b03030b10803500601008900c00115015000845031550706100503400a0060300c91640d1442c10180c88000207011640500240c5a54540c2da405482c3c050802c0d0100700d6a80c0c000d40f10a55103079041c6038443c149101548184c004181e211340c0c1100507880742c1e0700c4403404034000420034151880200304403103070345e0030507281c00d4007444500c6219551352071018108a102580602104100e0b44108800c00020342c0000071110030041c1255030700c40c0f448060800c1c3d001245603610007441d5100ca0040740d07510000c80c801200007008040c1036424440d071501800d041d01e02480c0075901d0b880008122560104a4031072403010703800170808001c5410248180780302070070991648216015044c90005104120080c0300c0081606d0107640c1c1000300d6207280000031030303071046c190200022154041c00901848 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 818452823 1250 818451573 818451589
    0x503060412050f0307030c030507050c0a03081b0406120b030c181017340314011b1808060408070206090a08010e0c03010e0d081602071503021c0b1c02 66
    0xa200b003c07405441e4035140d03102801810054009200103458500000e9840b8014000d80700404065001084442c076559401c0d42d002c900640b800d00b407039080704175101c0111803040040010300315581e41d4034000501610404180d464100c0d1b924481d40100480d1415500c403261260a0608403039550800b0f41c580c020070507a00d400a4000c000e4448000d40c00c8121f108002980f02a40e03540840f15000c50030494202d1202d920020710000c082025a020800c0840d4003c0825010728a6072000050b034110965400207000b401d280c0c03807002141c0824003c1c54060f40244c0c11800601401028102d145466964542e4034411010024030440e40456040e02d0f42c4c0b500e04100b03000c1c14829008005220b2400301b243c5e0b0f00c56218140ca842036081c00044030342e800c404501108610003903111282c040e00d41c20700301f4a0920a800c1300d6021171080c0e07200000e0301e11019403450f001e0080c9442c016656030310a4110040d61490300c41d00c1d0304e00c0341050700c031001030f494041e5040d01501d214016612010380c1e03480010950 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 818454073 1250 818452823 818452837
    0x4030c05060103240603030504051e090f0f090f03031902370c0203100902011404180b030d020a020f041e0b040506030f0a03031107060207061b0306050306041205 71
    0x192040310008002c0200000c44c009039100a150100d0110000100b442c0075140603010080001d10240030401c843d06060800d5024041c5286802c465461140c000c901e08001c00c07108990344000d02014091803a20060381c039a0049001409810300f81442ca044581d60321001d03001c003030304116680858440240a40c1070b03411841c0c4030000700c0b400900c0c0e25180c80581005c0301000944a00d01c4444181890107221801d102c664090003403d00b140641240e200282120030069040c000680520000e42a00302c3c0140090b10358a044203103050b4140903c0c004440005440500913809400d490f0441600010b420800c0380d0b04803054286d0070100d0001c10701030040c621411042c2e05505c4c0c60104e02562507000b00c4000c68041d507040140341d54907002c15684500314403000c1e03410381181c221180824480e802524060004e4030001d40341c51600d580b00000c0380d10100064460560310000303062a4011040101030040341440c1c1071150604180000b6160f90001c0e00050400a82151109001d40624195116 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 818455323 1250 818454073 818454083
    0x919021201150614070f080f090a080a060c0c03120e0f0703051b101b030e0904060b09101802160203010e0d1205040b010b160b07020c01021501140904030c 68
    0x3250b01e000301d46030580300e01c6000c2d5102040c10074850800d031801c000b040c0c582240c0c01404c4008425010b8556030300c42d034800b5545140d216001c200914494440304012001002d00c074000300620612804c1220458100004038010000c183c02c408012a0380a40c0b08000c21080e15000140c41340507100c410301d000006800101d060044000000a10902140b1541100070001944d1240c03640001042654070500c2c80c40d0002c1171101389062240710301ca441d0001c00314443d080040c40345441400240e07034107408880c11101c03103807182401c241500b801c408181d0070500b2065503500c51420455101100740c00320004482a9074049408000c0c030700f079400c1e40002c50343c001c0d000700700c40080518401c2e150101410044081480d5040ba030b82507840c0c1d40709161146070001c00c0c9105503403c0645000d5960300081a640c002804551801c001c25140050b00d40928410b0b0000c20507801c604001904001d1001c0f000d007040b0342454010032080c3e13141100d40b01000401c43e10500b4130740d110716082d1075a001c4403602506c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 818456573 1250 818455323 818455331
    0x603010e01061e0b04061b060e1006030203010c03090b13020a1208070506010f060c0210020c1302030105150c0714120105100509060303130e060a05040e150f0919021201 74
    0x801c40c40301900440703140d0000f14a0741c15184c848000100d81d204900c01c0340b0008034000d00d0703c1401e1030701014107007101d07110f45000310781103060403c8145451010300c4c2d2800c070203035183d02c1002180340902c40c500c400c180c2420244400410794907a6090917100030201c501d41603c034180c540441d61040f00e40c00c05441401c00c00380d0700d000346050042d50b6401c030a030129001c0c4985000450b44401016880044034480e6451001c114015824803000c0340c48240907000750b229403504110143d030b44401c5038000c000c11050050301d0350714041c10801040d41021308030340220b00c10801e40fa92824045584002d44282203d1100601c0c021030208080c25a406650785155191034140000d441e2901d60aa0071100308447d115402c0c3c075030004041e1240f2031480c0c0043c0c3c8640700f100070030203504c1144002da44414000e103044c2e440c40e903030000f041c16600114407400854200884108100e0504a001a008004001102c10034500454041c2d0b450b03c500046200c81040c0c06050411940c1c1c91100e03080c840070a4000740 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 818457823 1250 818456573 818456579
    0x170111040306090c08060f04170c0f010b01030b04090201080c0c21090102070e0c1b01021e030a0c11030a12020904020a0804030f050c0d0c020a050d030504030c081906050603010e0106 80
    0xb8020320429000321942034040d01c00043d8900c2c00901240904018106100107489554404580205107880d01007110418440150014014000f94511000c4100042440540503000408a490b00311030a440384e480d02c44680c0c0540d030b000400561005101001da03956050040f0300511b4002071301a004224080710998002a080700c0010740781c850400e8084405003502d915240e554140c0071a403400210b03c1c103001c803680101d03c200d90346002030642c1c40010703c0c0032640758000540c0740307030f019058240d11000410300a500a0912582000150510f000c0705800c03e4a4005a00c9100d0010b40004100e550505d0014000c07082e8100c44040d40000c000315a91406814043c214000c100ca09402158001000d007500710300685c100d50070701c4a41d00c0a042e150600c0c1009565070030700800181d07040401d6a00c0451161506910801d005001e610f0b0203481e01d2030351502201842d40794010040c2504040305000308000c2d21130303407400116030002010400740d8440b400700780103084409042429600b0b04c4000 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 818459073 1250 818457823 818457833
    0x80919030e150f0d0c0504030f0b1008100c201f02041212021c050a210e030405210c060f07050a0c14040605030d0e13050702061e0702071701110403 65
    0x100b084414041e0140052a12110162014047d901c005402400c003140c103100000e0319440030319809844481c68001d001c2d240d80d561440c0032a8510464501984c407010f036035451390403d2814081030038a0300101d00800703d5020359074903061184001c050741c0d40030034418039101e040e60701610082c240703602995a64003018102406840c2000c01c849016011b20b00340c6441001c80086401a01200c3d6101c003460300070280c0044900b1610441508c00e000e1520600480d136840f10f004011915803442c0003540c46600380020080a8440f03582034000d4403164105039940c0d48400710300d200700341808864480d1104440e0184002030b00c11128020302500410020100704103a01c0000801d580c0c0e00f0111681c4120003a003800211800342c01a154907900003991424498840c0b809940c0540e8044d1040180802d0080e0103829200c09541c880c0140e0841002c2100001d2030b0940c1303008410301e52005501d581041c50006c0d49031000c5004400c10355034401c14000d05200d09400c0040e50071503c420316a55250b8900304 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 818460323 1250 818459073 818459077
    0x3080714070309051305060f090c0d0e0a0317090703151e0c080114090a020d0b0904060504030f03051e0c1b0a1106070308151f02030307080919030e150f 67
    0x44a12410005c0d0680160b1070079442151b11851028000302e02551103003041100f200c1c00101250001c0c2c2e404c0011400480c11801048a50204900106015011407070007600c00201c441081400c00403040400c240f4000014170031086139004240c01e0b00c1030b90700c00d2134200609000c280f0603107101c5080030002d0145480d0fa200c000b88007469600d89a8036600c4040120806107038000b901d07071006458001c10381c0c20240354000c1c022642811400200c00c050389000c103441d40001c407400da40c229602e10800042c0741e00014088640c900a181c208800d2400120145010842140e60100300800c000007400003c0b21004545600c001400c50100d003825094200f0703900c0050301021240c170300c0c0242e484030907406c000c1d00b80c9155681c1a22103216a03510f184a82110701c1c0f001ca2140d03403100b0126200304010100c180c02d015140800d82c003955407441c000801404540c00a00001c0b100d92044502000850701018642030003941480d10071600412580024201c0c10401d11803015035400042e002000d98017940 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 818461573 1250 818460323 818460329
    0xf09080309150108011107031d150a030e0d091514180f03010204030809100302040918030f020a0308060105090a0810060f080609100e0f060c1b1903080714070309 71
    0xd8000b00c580c0c07980261400e0314910250125411010b11510b0006800791420aa541d18240103c2921003154000590130800c070350070007440e40f80002800b1402e150705010307000a44205c00c00070011400c054000030601c1d400383c4079482019800c1508050440c2c0700325422031108450032062901c0e54100c21902c102301c907802d0309251003000014280302d102d003018003e0364200c5c3d130050400c3e03081c50f203a04c0c00e1054115411490b2010541e00f000701040c41d4007140324514120070302c0c1200544d240c2e05072401405614045110000355449980c001c00002e90141c00c565009800b031800e11f0b1200d0281c000b140004a05400a0009000e070202641305681540d00400803240500c0d881c440703140da0369820980701c0e4000d403109242a00301070300c80e040c043d138950800307003103030611700c08488041c845061014108070082d500f04021010020b2807560541500d11440c5041440c07d02405c0c1c3c101404c4c1c00501c5d00d0580c440024113012210001401c201d01800505041802550040ea940c1e149890010440c40443c0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 818462823 1250 818461573 818461603
    0x141c0e01020c1603320a1109060103021801030c050d1b1b050d0c150203090c0f04020406050d1107050a030207030c0905270c030313090b0d020d060f09080309 69
    0x1c030108480103d104920011650840910f842d0035060741078181c3c6100042ca50080c14490807241c4844a034010012801c0103400f9240d6101140500410040100006021141010300502c01c0101520f101e0782910300f07001090030000384c41d1041c91010340d906d000380b035a00f0b40e00d14600b500e0b000300c0350400c40e480304226415945e6800e000c011402d49422403101d00e580982b080d40b00c50030120505028040801d4400c3c001c810a1015841c05400c030410b17640211140308442c0c018515499a6080c121268442840e0841e81542030a0802c0340042c2903000e02468540c110b919030841d014120041c100300c8040d25000000c2d0380a002190502039942c0d49d640c80100d4821110810014444040784107141c06a592515122004034101380a4000c1200001d604000c50145c52100c0b80c090741d08100601c03181d99010300511500345018450b400300d6203e25216070041c08400002c0c3c0c0103a036982ea821a01650000001a040c3d90a0044034014036040b14000d107134480001c280447c581000500456070b000300 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 818464073 1250 818462823 818462833
    0x415110a111e03031501030203040c0e0c19030213090e1906020904020703050c06060a0608010e0612060718090e0a0201051e03010b07050c010c0c0612020c060c09031606141c0e01020c 80
    0xc1e00044023244002c54014202009583c001d00041c40d01c108c545411000d4442003a04101401200d4100240e00c040fa5902003540090320303080304c049a0814070010a90007000304850408920380b15101c10122000700403041c01142c4201c100801d0f80d0640e5500580904115200c2e40c1c20316000d0031550203d14207117111b02c5408001051880d00e2000c000590300d9a9903040c01c240d10301320649070402c401500c4680d1200c0107002144903880200100d138030030081d60303544442c800c07510b00140c01101002c0c0c0240e5281420841c903c0540c8200044040ca0164207180071a9145440c8080701008604038003045260003000000040070300e204009000e0342e03402001075074244100c14006664203002d0100050034601d0901042000a02690072640303484820700c0058034008020510310300b0420100c40c41d907050400800d04189034202001104000c61080001d00f0703210742481ea02a2000d8035440d4102c1d28403200044508078005000c0c20006041c108980601552900011150107508061010394992182d = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 818465323 1250 818464073 818464111
    0xb07050f04031a22051c0c050a060618051e060111060a0b09180604110a090518120f0d0f0f020721020106230103060305150415110a111e0303 62
    0x4000603107140300d07600c0002401d1007001e5038050540203c2044905d020b00c11f5003041900814428811280402d00c03d200008160b810100d5200d004814003544540b0680b80c0000c01020400540107101400760f440c04420003a52074400494460f281404e031120b41c1c6c0039100a200d074070b94058014601c000e400319800310307041d69441a4403c04600b000d403c441c040e4804000320740440c0c5003001c20740350741c40c0c058680d80140b91140ca4070001c0c1c402c16100c41010803c2c5080d1414000020306c91341c54036011242030286404040b500020701d030700510021010040e41e5050442d0b0b1240c00b03510081c43c0c02c95400c01592200340074204401040c00905c110400c81c842d843c0101841031043c07040d0020307030705404414154401c03c184a09110326207c2d0f2018145a9075140210100b44100f0211200020116201c00c0b103103458500a0110782100500c080c040d8140400c003c50081e5440036186208200c0c0340080200700e00c0380c041c2d450082c1c09440940602e020420310401d16001000951140d1a1008041100c0c80 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 818466573 1250 818465323 818465371
    0x3030709050105070b160e1e0f0d0308010e060307180b0102070602030f0a080402031006030f030e040b1804210c020306060303070209010b03090102040b1b06130b07050f04031a 77
    0x306040d4000c2c002117841c0f0000c0d400c080f0720385940c02c0543c0c3c203107040600c2c00c11a8001c038005c0c060210700b1000c8134400c440b00c840540340c0308600301d89059003903914400725403a541e0302400440d81805402e0001441c000040c4254504020310b2008100c48007045042000a4032240c00621484d03408500600039911b02140310741c000400c8622280740303006442d00d003080c003c60480d03960001401c2241d041c020058082c11080c024094140070794000c00e880c0b1044c0800f0324001e00b0019000e0120780c0a58105100d00c2c0b03260351459030300c042c0b00c2c2c0c0c100024170041e82d491904621b261302c910403c0d0b0701604590103111035980c1c001d02c1110b1140c4281e003102d980d903c0c0c480415969014240000b503015031000b005100405455001e9a00300c89110005170a0944880113071680d40c1020074148504007410801c007800e03020422207180c000034003035a0300d07501e541e42c0e444061101d44014103440501800040013030440e100c14044500441c0c20a144041d160305400c1074201c8140203690b0070a17420380341010441a50 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 818467823 1250 818466573 818466577
    0x601080709020906070c0b030f0a05070507321e070e0703020c03191e0509030a120e0909010903020706021603020d03030f050a15080c0a3503030709050105 68
    0x14080400410666240010700c0d0040d6100d01000c0e43c000341d041c000e900004080c00031031005003c0520350300307480f0300c1c016805000b0b030710000b0011f8405500308004e000c907554101040320f4506801011b100e101713490b46110300039035102d00e2a0340c000501501c0350941c141c00000c01c03240280000c800030200e038401c4c1251080c0d43c0c0c648038000c1052103030417580421030b407500950091141c640184107603814040d000c145185128000300b10710b00402c000d00441c040f5403031840207040b12000c8900341942070039004404039565540c07960004200b50011001c254140c0c0c020405807030750003c011b01811981c03400540043c042c04490b4003c42c094424000d0214246001180411a1f140c050810fa11036600d1502040210b4807003034002c0d01410b945101410007100c20707000b400d1041445230400b0071000414001c06078200d6184d801142503402401820726a40e030b43d00201d0040380c81c2500300003104440c0303403e5202c4841c64075000045850307110412420090000c03002d14451602c2c1d440da800c00700d0b991001502c4c64 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 818469073 1250 818467823 818467829
    0x212031b070f200111340e01051801140f040b060a03151a3a0903090e010f090506040609140103120e09181608070e0a091112010b0a0f05120601 63
    0x5811802c513003550307800305800b4040840b01b01140d1012984200b400c03109070701d25039000703d401c00c961007006111030b00780007500d00450000d2013036154080d0315048020780500035042100c1c1c820b078821000c02410313641c2e507006400c0580008000a40e0350b204210040d0041c0102100201400e02404002480c42000344030b0900c80c0004581d02840d04c0c04d521036010750811880c03800011140700c0c424051001518054070494011002c1000580c082e1074240a48a0b1702035501410b041d400d00d07001400310050032003010085079120380012580d03489400000c0c0103004180c0004070503e10308032601d8629103009600c181264007402103584a25a1070208480e880c0c41690095045071603a004a5041c190308c0b0018012010458140d0302218110b804020300e200c0d41d40c1c060121a80715048c140310591440c02c00b00d030805890401042012403683c5c40038100d50001d00018455042446504191042900f0898007004014520801c20761203c0102c1140005401814011050300d84c02903440b150004d060b40c16 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 818470323 1250 818469073 818469107
    0x10308070305031e04030c06050f01240e0d230c0603071b05071e0501180b22080304091b0c0b0c040b04030b01080606010212031b070f2001 61
    0x10300311603901d09545039400034180132041c248600d940c40100e50403014280c040d034441e545525401e041810721406035200502002c4001c070f210401002030003600850316906e4000c03502c40000b040460b01c0280e035a0020080100d400c0302c2013400030400c00c003e10702204820f00c10b41160340400781002c10030f0303642c400b1340440c184e400140c10004078841a000b0940d01c04011200d160040343c0d10403d03990141025281d520004204d107221150004005003040d501000e44070038600b03034990000f81c0c210105030b8000740c070801074603d000180300d02451015443c0c151546512522140201d552014050b61300c2d4001e00c105117950340350a440c214950400000e030300c0c55039170b6683d64240d001810b80301d1090011000c0d0000108000030030000039212a044080c00046008403100b00c411740c903080e0a83e00b4100011302150454015000480c2c00841c0e10003030f80d41050410540a5807030700340c3e803c000514420341c4009442c3c150740740b6a0300104001c44405241507403070440a200203000001c01580c5810340f0102d4002 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 818471573 1250 818470323 818470327
    0x3040303080c130b0d0c0801140f060a0908030f1c020708073009030203060108060112030f0c080f0903010c0504180902061b0a110907080f181002090f030303010308 72
    0x1210034840014183c68032404240303801e801e9032071000d48681d60003403280034419a1144008160700340c100c0d04240c010a8100c04843c01115910001071800c2a5041410b2007040c1c00715401124505c24126000a44001d000301e9540f02400e24072850540c21801d0804808a0694803221401409000f50741100f9805001542008042c0e52890f5004003c5580010007008207101100348100800d0315800b10b28540d03c4070b80c60076007503006050500d841600000a15031203000100300300d118002121408581501d000c4071a902d05c40030032140703588903c0000c0c01c000c0c0080740902880d603180d401042460800c4000f00a81405510b0940d418000e038030403002c02c002102084001111150404402a0b100520203403800d44060400a44021810110110395000040038001c0103480031000c1d03154541250481c0e41440c0c8140e004100b900000d203140305501c0780a010030040b0480c4102944000340c05010f44e80c16444030b0401000a401803121544664542e45400d8010300700030044a059030342102e9514 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 818472823 1250 818471573 818471581
    0x10050112021605060a060806100302030604140f030304031e030c020c040903031103090d120213210c0b0d0f02120a0c0908010213090e0c0f2103040e090706020304030308 74
    0x100a402910060242c460420400c80006030113000540c803403190500c1c00a002c030304010300036184c2040280300031611402c0e2181400941d90008400742d01c00d6225080c0070f07002d0800390030981088010303641085180300c080180800c040d042404070080c001c21407248480124140000c40984d41d2003141c4401507089115100030f50700300342d0032100c4210700038140450005003a0859050320782c011540c140c850f400c201100e81180d94494449505a420304e18294141408000104003408035481030390321145150300c45203030900114403140c0219411880b05000e641c2d0354221091030b98042c207220704149140501e111403082d250303c00d5880d00703c294840000365507240b0b81064000d010301c1e1071210030700441c0d241c000f6280809000a1220040c4260b030f55021074a03055a080c1a00e0ac141c1c90854240c100c1804040b2984070649011154141240c0950f14003145131400503140c040d546c0c10003100d000c00540800c451618410582c041c600d00001c03100c40c2d82c1c5c0d90b07808036103900803404010001981e220100f = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 818474073 1250 818472823 818472857
    0xb09060111010e070b0901080106050304080906030a06050d0c0510020a24020702030304080f0c0f1003090303150305070807090507050f031015030f0f06050303090402030c040509040f0506100501 85
    0x51081c825030341c00000c2d01104900880e280ca211940103041551000070101c1d07940d42d2200340075004000c1414824298102039403003240d40d010700410580a40e41c0840003511041c486d4202200420000d00368020248180c01d00c0480c8180500407075010b4900c401c4120081480001c40d9a5003c0c1c014500d5000b0440148989085941d4800354036036141c0c0038400c20003d03a0b42480100003c0113503c0007095a14001d424443c202203104104500c03c05604400c207402c0d0310740e848902c0c01c019052400040e0f03646140350603801072a2a50000030282c81c142d0000c0104800050780d0016030b10751000b02d07400140e035124820165002200c0c0a00040c0c0c003440400d8070300b40c100c00a507400100742020301c16865143c00d5821100501d2701941070001b078030348190042e6592684100206a121800203006984c10580401e40d288140e8054600481d400400900800441c00c250740c0940401001c1180c58185424498280e1010308001d442c2c1d80a140003040f14580d210b80180304442d0107840d000d030020030510503 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 818475323 1250 818474073 818474087
    0xd0e01121b021005010806070c020906130e0a03080109050903091005040812030708090a020a060c02010e0d120f1d10020f0706020106060f050f0d02160f05011d010b090601 75
    0x34a00306610399052000304050005014981d41d5107600520310000016440002d440c1e06070311001d03c580211f4144240d196015080980e02601a600b42d580741d201c04000c40c02d0141030f40b010010143c42c03c0d211f100f00d0341d40420040c0c2c0841c001c1d40c074049283d80301e120300300889106580510b1113900c10807a50003181842124040213005a050450900d640e4800d01c03410481c011103007030b507100400010402c44580188a960300102e6141c010b18000708682d01098091140d400384005000c0c9001062085a2080c070159910381c0b000b4000c80c0400d006480e0450041c0300d951008e4001c503104180b861415403090005002c040ca120715440440103c0c00c00303110327002c800440207804500912000c4130b07507600100715050041c40030f80e000040282c13410000034000500b11030420204034081003554400000c200580d460301c01118030040c3ea601c400389056030b015158401c0200803003600405082481810350001178950030105441d5001040380c074800e405c0b07400c840080c07540f01041c2d0f008500554403542c6 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 818476573 1250 818475323 818475347
    0x81005042303041418181e030301030320060c0d0e0f0c24030109020304020409140606090612060a0e030408150f0f280f06180c09050105031501090b03010b030a0e0d0e01 74
    0xb0647e020280c10240744030200d8042018001c16500c00801003003010b500075541e0070340a02601d00c0c0e05100744000e8440b0388441c4060081440c1080100d452010b5540c142d111203c91540c0c0b6044881c51000c40c04040e403600324000d40c452048424008400505c10182c03010030701c00ea06006130510350380c20405d41600039000030300180d030416a41d00e001400215800b48103ea06031500c80140a146442d2040101d10315000300300034000c040d0013403000050880080d880342c1104503940d011440c0c41000c01e5841c07440c0140d92050351a84139900104203c0041550018003e1440b5032000e106681c03035170026800144c06461000051255000e400652032124202c0c140b0100d10401c04200c0c0144a4269000d5800d240c00200a49040b420141c51404803407094441440d83da0401588141c507000001e03146000062010003028040f0800010580c070508001d0050420b840602ea00c03941c403980000d15a81048a010307030000d2030400e561410500015035144a442c043c0d88882a05aa010046518140d489 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 818477823 1250 818476573 818476621
    0xf0617071208070803090606120c0a030b040f0c0e070e0a0302010f0807120213060e0d05120a12022709190b13020a0324081005042303041418 62
    0x1016100004e10741800650044c0c1000c402070580c3d080050030070149030f0069001c0c40c2603034009219031055440c1e01039104100ca07048000d00d5031641d01d6041c9512003100700c4400030619841c40c00042103860001441ea400f40d03006941d42c0d421070b40d11000f0f0110b0841a4007019010401900800b82d4082c41489016030200300703071500c000c0100d54411113000741d800c88202c8400b01c0b0303800c00d418404168040315aa60b05601201c8061414400fa1200340d113030001219400c00e40c8000007180d00b00c2c40d000e21001400d44420482c2190b8900c00d040d01c0e0101404807800414003a21554410842d82c40c010218501505d0984030904014809104c09001010141249500801055960902d2604a101078034100e1016100400d10360920398144940547c07a848903181028105018020030700c00203040c5400e08200380e800626911a4144140038024210510300071503d648030350701064802001420441d0082c00011024107005d000b0088501240f660509004601c13600081e0850076962140c50303091001 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 818479073 1250 818477823 818477827
    0x605130c2a08090607060608030a120b0913050a1a07090902120c0c010905100207020406050303070308010911190207060807030b240f0a0302190509030d080703110c010f0617071208 79
    0x546e0302e020a9940591048000d900041140c0242581100c1c0d5140e40061740304017000001e1070350303000030500d050241084d101c0004e481c016400f008000c10900d0311040c1c101102e003038100d0151080d61601c07481214135600141544600061109140c02034070410940c130703400b81c0d0081d0f85909402c0001e070000e24090100e0340d2507003182d4011030018040c400002619010140e941c0b015801032000b0707500d03a0781c41a4041e510801c640030110703600100d51415208814008030b42d0319441000d404031030140c02514014280d4a01c1095005500001e202e81110a030391100c001c207079900710741502291006907040d078214101c115901081d1441b140110b00803400030003c0c6080c501103131074107160781d000320f4080030100c3e500040301c003804000b44281040500f0f052624a10b03011501e00231079112903010700a0401d000000e000b003078045000e40c00203691000e803e00d040d0784a0045c0340d4143d01812000710b00710300d040c1c81e001d4080f41c1200c0c070006909000c41c6800040030003914001c2c2d561240761090b04140c50b03540301 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 818480323 1250 818479073 818479087
    0x50403140c0d0309021f03050105090c0901021b0d0b0c0d0506011d0609061b1f090c0e040c03020402031f05042309100f0b09090a031409040605130c2a080906 69
    0x40300a1001c00350850f5a0000e60303036060402f44040d4460280640ca1a44414050f60f038442e07900085400750030511500c100900b001d10004a0684250310400a1201160004008425072200090001d903101e10360244860780f200030041d50440300e10007811000b0300740b07480380d9102828020005c0485031b0010740403915000c0e80e00200365804008810540d260341050b5400f50ba280070200c0080301100b040720381040103e90700d82d2141038843c100d1140042c400300321000603090081c0a014036004580140c829562454200d2480c800c0505044050446600b9160082400e0421b4401c030440e1501001c038102400c80208400000070b6002440441148118a580509400f190084e44a503088408000c20180c5124081040f600802044855107520040303a02021a40c0150b15000c19202d12144030303600c6441c000402d000c1e007440d80000b9000003541038841182910380c0c3c8910f0b280f080982e51034500050034007076041d03404800d09090088800c50b599280200700d000b8020008100020106850148 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 818481573 1250 818480323 818480359
    0xf24074814060910020a120206070206150d0209042315040b04050f011401180e0705150c0304170d05041203200604050f011104121203060f0801050403140c0d030902 72
    0x841c13040318030010f0700311040caa01080310801034110015124000b410241c500481c00a58981005082c054500340440d0001f0850700c07100c4404542a0b0003511221891519092809546260612410392a034416903a50b20300080803800040361103459545c40b00b07d480d01d0725405850700000e40140d515026200c4030301c120170000d00c43c0070744001e0030342c036840c40541c03416a04856400c2280800c864007400d0542501240c803005c9400030039500c0c2240c00100c03d83c0804082e05081c000c03c244081c05100003d030200c0c591110300b0414411451080c00c540241010b6241240d06010728450f94821024040110002a02420090b01c940c11010039080c054070500039021f240c9170060303c040d1000e4003d2518103400050038050044807000c0d405200342707814030300b00403004100342d40d040251207140141c068000c2d0034400c1d0010300041c6101d0f164524800e441d0f01a640c0208002d460850202c0e8402d6014a03a0200707000650b0315081158001c1d004200021030107801521084400302c1e48a85c4200014156403 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 818482823 1250 818481573 818481589
    0x2010e0f040605091e06010c05060f040c0f0e0402280e0406020d0908130603050105010f080a02040503030c10050a0b010507110d0b16030b0f240748140609 68
    0x410100c43c45c500e00001c0d00d0f040003c13004041d01560400c81d101080c0d201040c0002440c640040d62800307082c034035a87d1803e10f035410031600e40184000950201002540106840d203d5000d03600851701c0700690060449a41c3d050352140c242d1141c0443d10400030803040101c80440c2d6441409007002600d405503444204080300c044110464003188041030100b41e0a165500c500c018242c03c0c10208100c1d41404000f910318083c4800a004102d182d40014803c5181034042d10f000300409412030341c903103522603001a02c0c0d4101081354160a8901000150501d255000e00b14204106071506442c02c001521401c00304200c0780800c5801002c01215400000c040d114000e10940d1000080305041d142006d00030150b403143c00c2000d2040c0d4014400d11600d1fa180740c0c40800b440c040c42c440c8600780c64460381403e00c50280d10405800441907448641800700c80520480100006541c480c100101e1000513228404415210029008404009020990311440c103079914000c0205458113044c0140d001800003 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 818484073 1250 818482823 818482831
    0x106030602120411040507022802120c010f0f0c02120109020d061b090b0a03150b0d020406110a0312150b1803060c030f16052205090a060302010e0f04060509 69
    0x104142d0310401041c4800c0d0404201c207414115002c0c0407504140c10300968a00da9285401004800b0022412200065403c1c03002c0c000d80c0034081c8420a2010209552940100c0b42918003050b0b1204015500c0342c4504544545e030081030711202d1078022140c00b40081c0203125486c8029642da03840300d07080942d484030009106a0b1150f100441c540349001c00544052480107850380501000c2c03141032010295a10079102d103601da074500090080c180e410300e0400c5080690288004010009680e010707800740c2e030000c9c406d64002d0780710000320140002c03155548040210010740000c0c1d40c0c50003012014101d4202c40c15814010440c0001c668a0b5180c1001d2a800314000010001c00c907091664141014031125510500005c40c0e54110301d05100a80602c4200620394410168400d071002042030180c400e4405004c07044440d000b89100c181051a01071304039019840c800d52100c40026102c40700ea00624064030307410b03940c00f40ba64011109116210700702000803a48103458000200303881d11100061845 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 818485323 1250 818484073 818484097
    0xf0f12020d150302040608070324060f1e14130c110304081b0102061009020a030f020a050318030a050a050f160c030c051906080615030907080601050a1d090106030602 73
    0x1e043c03a40c410407017140d555038480d41064101d0403080011904541101c280b1203985d0040842600780c40e00241c0081c00c00d80c00c00d0348074401c02c490200c2c501c2408421041c0c541d548148100c0280e0b16580710702d010f1440303071050f10f0740019403855a09540700c0e03541110107034010500b80240000d40000e0b4890031504150001c034070300e501c6041c0e00045108400c0c034040750248280050640c03828400282050925240031b00b0300c241e5000142c181401e84640d109440b1841044001c548070400c1b488020415881030b2408030110003000044040e02c0340c0481150b0f03600d0700c261181ea1030031031401401d8915810407a60744041103414480c0c080c0f02c0e004010325148141c8107240080d151402d51038842c080b000a81c101900404991030b46503403001034844048143c1d0a54182024103644003000038030220780b050030107072454a01000f4401d000d0b000180e43c0041d00c035000150391041e81c95005000c0072070098402c44019015503400b1015481600c1400c03500891940000308046480340c8a000c11390b40701c2184940 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 818486573 1250 818485323 818485361
    0x1502070213060b0d051006080402100908010603080304020f0a0e0627010618080a0206040e0406180c05150304080a2006090d030c1715120106080a050c010f0f12020d 72
    0x4810b40080c81582d90043d6402c80c46c00c82c080c00c25000610690303000f000203002c1c0c400d0b100007103420360090a110000300620350091006270744a2800381d0543d002510120f0040c480202041054900715503502e0640b003044002502e82e50703c444c100805124090034805545107402c0d14031a8010f81c00d50307414007030545901d5070b002c007000282208420700742d26440519640c0103540000010703640c440441e02240e80e0040091200c0e01d9a08000d0300504c2c0484042184a200305480403c001c4000850000c446023251210846011302402444c00d04c003c4070300501c1030b0020041c441c0380c9401400802c4500b00c241200d10b00d4100a403582610300041910a0800c55100700712b41544d407a403501072054680241e18000c10303103248030b060b5403125000c00741c0200d020091440708508980c5a015508030041c2c05c0300e00a108941e034404000f901c2d694074450a880e103025090101d56154080d019104c41e81c1e0b65a59591400210070b10120303061100e00c2a08101c03190200221403030461103000320701c510010004c8000e = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 818487823 1250 818486573 818486587
    0x280e0f0c09010e041205030c0c030d0e06010801020f040b0c0307050a0506010503120405210c1003020c060a0b22140108010b090106030c210204050307080304031e1502070213060b 78
    0xc8500303501640f201412500c0ca82c20000056000c00d8114144203c41c01c1c4180c982d11a007048440318003415048034018400800c0840030b08009401400040034650141c55203a42c860350394ad400d07849109409160100108020071481401070001c003108000340c41502c2c201010350b074030181080a400400e40b03855014000501aa2505000c2c040c1100010701040e07190518000c04200d4881c0b001d0b64644800d40b14140c0c48100301028020903001035002031190b01a5440414007030000d40024000104522070170340004c8460030540300b500750f6080020590080801c00f00c500340c06002d000d0088070990742c4c94003e50341d01c198031903441c02c1c00707400d0302400032841c254184144196540164801000c00d400d017800000c840742c024109010705810080103e140612410311b1038003900ca40e03446180c16100b02c0c20001106000840a801920306c03a404030240b48810007822052a4000e94020305903072130800340311000c810558000e121140c07001e44840704590b00c0005800c00c50b03405500603061810001501 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 818489073 1250 818487823 818487829
    0x8090301051305060a0501050d0201110a05031b0c0901050a030f26193204030203070e012d050904020418030905010f1b03140408010203011806060206280e0f0c 70
    0x85a40705e800700000f000190f1400c400030b00c140040c544064140440d540d07541e1901081031015081854001d000c0380d41c0c030082d00c40682d1500c0c01003600403105004608141d9903919014034440e0484c1c00040004d00c02070704541f0344e0aa01c041c1003904a8861505010a181c0008c0001d100300030481c4010520b074850651501c1403460721000c0107000104800c0700320b0a102818005006894420502c03d00c64051581da070145900f4801c5401c00396040c45080800504000480e070010305849202c0d07070201c401201031a81100a80b521070009540900c404401d01c054144501c03420f50040c0000c01c0492140704601001328014010881030740040e81a04091010b542c10142c0085903105624100e0084403a08070801c0d51f4001d400c0f0b0040400c40550740041c07148162500751805006d581c07001b1543c03565280c20940c03500211500703d080442c1009400210305001007101072198807006008100e0780d2000c1d802c01d468003c885081e90400707641b00740095100c40c04004000701c400c03540000f801034440070010 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 818490323 1250 818489073 818489083
    0x1f060504380c1911030d0c1a062128081c0b10030605180103110121060b21010302010c1103010609110a0f0f0509060708090301051305 59
    0x4800c408034030074107100d41d41c01c1c8814490161006582220340d00c0d1504060250f040c161944000303508a030190000c5014802d51001003051030780300314100e40c42a0141e4a094480701400301d4041c0074100180140c10012007500c40b0198801002030080400c00c82c41c0c4003404113030552050340d400360380c03265054a00014052986d00403114004000545900e400d0b0744144c25032040030b080d4080401c1e084842040503529821400d1028001050303011a0030003034000030b0060006100e500d00c40d8a8000840c0b00344180d2000503416203411840b80c501c1d00c40300000544000f1941d449030121010344110b00c542c0c50782c00b4481c0c10003608854008660360f100d200c0d0000007061001591098081d4044010030060ba0003801c131985599000302d0548128000300006401003045902c10142142031020b05629030720440000c1c02c641c003483d1100c0076004540202161a85900003405e400304404010040c81403030808040c02c0d8946c40703518034500d4511074401190968009403440c101e1400c00c60070100402c082440 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 818491573 1250 818490323 818490359
    0xd0311061012030c1a0415062103030c0e1002010c021c020316030504080d091e06140f0d0f062306030604050a090605070f021b0f0105031f060504 64
    0x20006500d00d041402118200d001040d0003402c1c070205090420400004000028514a9035910202149400d09060030229540d1080301c144520f48403020603200510049c40d040382c9a00c41d001c8403200740e9994154020082614050144620385080d690195660300c002e40c0e0164540c0c1c00810254481d810280c07a1030704810a01900044100088030f10035400030948107280300c102c140a00300700c410300b0191090f00c01e98000340c0180c00b40c11018261203400500482c1107a0361520410001e60b844661580604024018100043c3c0444c0324810300140e500060b080c2003440d200c02c42d203042c034016194011655013415031414551184020001050000820a031056500190603031000b40f030000910345100c010030140c46580e4a1010541c800c006038844114a03501007010400c601b04560060b001c60803800c01000140f0890481a0486058448202000344050054018403c884005548507000282045120300c240c0c1c1050fa600042c0d4101000201030703989039166614103299001d03401c040284 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 818492823 1250 818491573 818491591
    0x609031f0606170103050d0e01052101060e190612180c030302121804020304060e010f09020405060f090114010513030b0a230406090312060608090d08190e0c0d031106 73
    0x3c0010404940301040d0310450741031514002d10082040760040e44d207400b4000300405441c0c13070a020460146c001c01c070a0b506a40f0380d502c1d441c1141d8881c038200502104000d00007200d03503604803810071981d40281c8803042d2407444180c01040501d62840c410031170200271001602e555854a50400c107141c1c0601500c0e543c81d05484140c2d20323182601550049003150203210034000e0b0b074004001028080d055124a060741e4101d8024042e5a022080d240090a400c10060703101d80e180c6000718055113000807440360004005000301c80141e1030316401c0110320141c580c43c181841000c00c14560030700011482e48000e5403040700c0c030329103c6c145070580e10304450800c44400c214a42c0134202a500019020f010b5034001e03400306022482d11201e1408440414001c03040c415100d0901300d002c02d810303822040040c130a4840100b264a10504003a04980a40041d40c4090541809000243d40500c1c2500b061303040881010458844000c0c52020a16201461b901640020450401115401001d1012075000480c503 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 818494073 1250 818492823 818492867
    0x200103090302150403021e03090906040e0a020910030503040e01081002130e090106090e010b03150402010e0d11090103080913051501110f0f03120919020609031f0606 73
    0x3541d010350340c0c0048150580100020000040415108020200c8840c900c00b40480419070719082c00d0b680c94005111241c4180340010000303e05080c10300c101000c07110340000500c40c5001030707001d005246401402012960512010110100d80c042000340010304454602800940c54a0842800c0c03a1300703120300c3c2c0c0580340100f1012024240c02d00079201541e080c0d8100e03a40320303100d2190107401460180e10a000060400e2000c40310608194003c2c040b042c4164160b4543ca41d22860160008a0458009000c20300b940035059070360420381c403c400300d44d00c9401403050394481c1100041c0400403d0f03000320385c0c0c0c481c000703010100e82c00c2c06881c821040010190a1155081980202c01090721024042d4104040050450703048142045407042c502090403d88544d80080c6460540365840700043c440c1104244010546e000c500040d9607540a450243d03440b01840b8039401c0043c142c0c06003800c00d52520074407141040d1146141d0036480580d58414000620511b00701c0b01800440c0c032206400d4091401d = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 818495323 1250 818494073 818494091
    0x5031f0506040311060d06080606120a05100c0c080706090618113d09063b040c030506030f07030b0606030a060308030708040b0a020a120b0a0909200103 67
    0x70807040c0d03000d80f0352100c1416586140040480c100d40200f800040c0c1c45428040300151045000c0b5071103000e1102502c040340042c0d15544040e65030b1100300c900078520381c80503202075130320300c00740e03129410b4240a49801c45000341e80d5103501605400c81d01c0e0584440359141005400c010280c420811b00c03040c1d15115030000360b00740c2c4542043c0c4091005840c000c43c200800c41005081204403122a108144400c8611006080c01c80803815205c2803042c01056005502141e400e01440c021700e170410b10032003424441c034034801c1188035008a4145406200500312540240c070f070780e5805846200001607500048030301e804c00c1098540403900a000409400644080c40858905071103580d101e0f005550940e500c0e200e0031405002040d50790b101800c415008400c0c002c46652103580c80d030285000d510410078588035218120200d1044820032804a5000c1c1c200c40d2885451f500942c070840002000c808030310703aa0b50801819220040811150710104c1d41944d030500e604000201c0301c4007400c2c40c04000781030b4 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 818496573 1250 818495323 818495329
    0x7031d0d0f0f0611040305061e09060705070f150504210c02010c080706050708070809150a05070207080d0314010b0901140313021e091503060115020f010c05031f05 72
    0x30060b0607040c0d00c0700070b0360600c021900006942440c141c0340740d90741c564a0078910344661040e150807030340c001a018220740c81ca140e441d40a005590510280061b0b4035409000d8409900c2700340c00310303003080e4034040100c00f084281040c00070141c402200420380f0300e413600c0c101500d0a610312003004179400311030040da07041d540481100d62103982030900760100b101c80d0070050440c0c0520f04c0014a1213080c88100710401c2d41c8900140d0103280350751280a1a500e91800b40342e1101d4160082e01080b1100c1800554440d00903000240c1064075070050300c42168940c090142840481c15410000c00e0b03d40000040e08000141e08900405008410728281520503000030074201c0c98083c0d031001c03a074000c00485e01050300c00388032450007507005001c10030141c0b45120108828481651140c801d515100018a41059aa80e4a600c5110060180c010b680c01d003018441429101d40c6c203117003140f040750350b441400c1c9400d1060801860740b94a43c01c2d107078039090341181820003d4040c0701c0300306861b0b0002082151 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 818497823 1250 818496573 818496593
    0x1140f04060b0d020a0201090b09010209191a07020105070210022a062b020418050c0c060f0709053316061a130504140a02010e04090305090607031d0d 66
    0x10f030358180940d450310f62000403409004a400c018003158205414801180d105500038071a8840c2a92941546902000d00030bc24411510406240c00401d400f01c078440704c0402d00508000784141021410000305801084400c5c0d0968500c00150f40b00222100740700706d225100c0300200440c0b03e05804803510032070201e000c0f401506004440000702800c0d0420648500c00b02a00442c0c0b91402151219640d100d0409030641000c0c142c4103041c17400c0042002e1a0301c1c0303030460341250441001040c4603113031018020903192000b88940100952000f0205181d502c82e40c00c10110221084402441216901c1007184a003503020281c0b4951010040b544203c0c6c0c3c0400c0c441042500705500103911040141d00090350300a0b8130301c850740440b003880c000c41031030100e50099010324026141c1119045801d200c0300c0d502c529000c000381c08500c03400c0710117000e442d0a401c00d07240c0c0d501c00d02c0c0c40c500b00402d400c08103071a50000d074812030200e6428a40282d042d24480400507400724225040d46151040c0c0c1c503000f00a03 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 818499073 1250 818497823 818497837
    0x61e0901180807020103060b1c0c090803181207170607090305100e1009030f0905041a0910030203030a0908120a080a15152106140d05120301140f04060b 67
    0xb1940100c2c000041da07003c1c0e80700b41c000384080d0700c1880e9900420300e403a01c509011118502405490314841000c01c0780f10b50054000c0d00c08405c0110315207070803100600c20304191061720310782c0007504403d20242000c0c180160300040600400c884251160600354a0810000034101403c1001c541010800318800103124160500c000382d00040000205c00301c1800c10304600b01d0542083d0501da000307410503a001e21081ca00c20040d64070001c966859004100079508042c0340120622200080c880d071a181610000d5003043c0d051004c0c002e11540d0341d0120b82150001c6007036001081440b40b0402403401c2c02d02c8480c051511030304081d8030740365007200090400c2c0c2000d02503085203030781c8845c6007044190340c5170b03244094520340d0900b480390614844010030000000c400800c21082c181c101c0300d1200400d0052a0a03110300084c828020500081842045215203009807520f114446c10301c035501d00d5641c011400f8040c500603403496a507062080c040300c4520b52020328052441c0c0034040202d0001001503410b9 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 818500323 1250 818499073 818499083
    0x2030603030f0a030605210d080106120e071a0909010b07050a0809040e151611070504051e040c030201030515101404030804090c030506060f031302040e061e090118 72
    0x16240410f000b1401482c46400c010303000b51440941c03d44204202400c4068640342c90100e403082031402004580c151000e104000100d82c1c0185000e0f41c2492a810801e2000c400c00d0454109569440800072840c524904100e036083c1e0009410f41ca6080800100d070150814441c468580300413640d445a88040350304c0090f01041011840500c2a5202d800483e40090103100315810741c90f40401ca03200c81b010540b280c60844062002c60360500b8001c01141d100ba030071010252210f40d02e007030288405440001d0007001e01c42540203408550880140709a8041c500034006145100d04602c005011148050440108100d9000361803669680341240c83c40e0010395481d00f84102c600030507030312840380201d410041441402040200b07000c002c90703125122030541680c0034802c0d0346400c020300900d4030503040c0d000f4240720f00f000003a1000e200303440541c641c00e20181002a640a2910b04181081001e44d00641d15110100c200c450741d1075184101074003e1026070081140c0c01c14600d00711b142c15a00d22002304 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 818501573 1250 818500323 818500327
    0x1009050c04030b0a0e010c030c0c080c19031d010c08071401020f1804150b0f2a0c090f01050a0302090415060806070807020307030801050603060d02100f110102030603030f 75
    0x100c200361200c2514015075001c8103200c0b840c2424501340000d401d2a5500f03004a42c6040c9444241e640700307006800d20545107455074403201029850761580e9900100180e5124031980d08110002c8203104001d620860213642c90200a0881c80000850040b80b9050141007201e100344100100b500c8408441c4001e51211b02c0301c00c00311911628501a0207807071000000c105012620b01004a1183c040344800340c01201c0420100c6680d00030385803100c1550142c010342210074402c2c0c069800000d80145031803440c2d40720303540680085180301c440741c0b002031800c50445c0d0083d000c40c80c2c0c282072a45080c1d40101c404031850b4402c0d8104004100f1001091002920403020b00e0045401d0219119103d84648001c600611281e07840d80340059440c01c09941d800c0000f80c00900082c00e070ba00c04030541c0c04055041c2d0300c041090346401d007041144e41025140c50f0b4407003058203491005980c0c450440c2c9041d0500c0e164400c14460044015001c01000042040c56900400070404551790200807201148441180c081d = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 818502823 1250 818501573 818501581
    0xf0303100b070c0f092a0509060304050109021c05060a0b0f040c140f040501020607050a0c0b041a070e13060f05150d0905060609180604030f0521040317100905 70
    0x103125000940c4c000d07040c00342080c001241c554496049604034000d91249400012154100d2040c112400340072400040c0040c40415180d00c0c062004642050003803001140380c1d450340d000105a0440440c3e00c1031001400d4001e0401c2100911100b90f2000c0421410005541c100c0c0200e000c0740a2035180c144180d58613604000d501b40101d410302c40c13901041000b907480e00518190650a40d00030300403036004d842541d0014940c01d115500b212841d00312651600c03402217180e0307507280190300b014104940e0003035810031585091641d9075210f44946116982c64202c56104000e10005007008103100701002c4c14502c040c4211540405030404561059031500030011108179540b21b01d000c0c0001805030203041650210a002002a8144c0524001c85a0700d80b19201c917001c4204100e406009040700b074100c1f800280100b4040c5041c441400c0300b506003d0f10305100380100700800c11080c045800e054298100303100134144d01140484034241c50468020700c0e410040320b03601e00c03e03409114070745089854800103 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 818504073 1250 818502823 818502833
    0x2040f0e0610030516270906090c0509010506070209180304050d0602070308010605030f0403030c140a0903150e03030a0b033f090604060503060a080d0c050f0303100b07 74
    0x24035040425100741e40040c1024041c1005080262005940324030800d00164100c0a1800f09041201c02034000c0940c0c0c02c203d1441c4a4400c2c0d01d5661280b26140d5580c0d904000c2016401001382e040d109109030316540e8203100c2004141c1006811150050710144804001600c0d0514a1074200c021000d040010003040803a15145102e0b5401c2030340c01c2109040000d003000300980142010901c41d80315841c851380c0b94441140e10313010840d0b10b00c020003042070202d008203000b50300480c164403803403505000d080e40d0320140c2500c2c1d42c0850995030014100781410014024003c0d1400113482c0c02100a00c0f41c08110801c141e075900024103e4414160ba501d082c1c40c49170b60802800210141d00312440e0295244600c0030303403002c22069000c900f1107420500318021024140704540746040000e2000b42018180041115613400c0107003140d410140100000c103003000200a1818101079540d1006c10f05c0740386180990422a42c1010a40564401d00900c5071120a00c0f420100b9259800c62094690300c290504c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 818505323 1250 818504073 818504081
    0x61b0f0f021504060e0306040309170106032a090218101806080105030609010c05030a020a11030f070512070b010e0712151707081209030a080d0b0a1203020a02040f 72
    0x30007075100d5074001c40703112469500e0002c1d10031076115840c1d600740712400c8005e00d52100400c40d001000181601e40034401c01d07407040c1c1b0903040100c0003c000a108da4523591402c0800041c0d2100038a0f078a1220a560300256003030398070102802040b10103500700b031986550089541e18501e0300a02c19600800710b040300c00e1207082c48080440310b154034208403607501c010150040c402801103601034003076031b0001500000c0501428440e2003040d80c030f440c80e550318255910001c0d0450440c0500f0000410340500a6030b86c208064000c8440b07a2005c603640d51003900e440303803500c000241101c05000701845450041140000d009044480c18164880d15a42c0c001003200d00c00d4400e0440920103151000c51541c4c220295144020355020410101c0c1400c42451000c0e5034078124490342c9180c1d0f00c918008180c07a00d1400203840c1c41400501280d500401641c0d81e59541d41010141d84040c6039035508900d214903012a41070002c012000150501d0b525580b0002d442d510020406400345403110214280d81c01d00d540 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 818506573 1250 818505323 818505353
    0x150c10050a0f050108032a010204030c0905161b0201140c030304030f0e04060f051e031c14040612050c0903070803071703010b0a0c0602041d060307061b0f 68
    0x100800462800c4a04400100601000ba0101d5032816002280c40c8600004031040c05409110740d01001d140c1080c0b0b00114800c42100044654091100000165206603010050681c060300400c4610708601000038070040b00c0358040400c41c1d5050402840c48580800610264080c640345d42d80c480a0304001b852446402501681c40c80000100000d050344945d08862040540e5620203030b4003d5201088165200350040e09a0210000341c10003180c0361a0211a100c0300030800004074000e0391030002810400c404c52148000c01440c0503420002c0ea0008540e004440450071036400c4c2804c0c4240140203514500389240c0f802d07a5000815030700d14818059543c3c0400080848608a40711040940c403038020700b0342240c4002000300d4411024481c1c3d010740307042e43c41403100141420400040ac458900c1d5170002590229030030440800c1c1e0070a0f018080340d88941d2050031074441e040c10000e251501d5050740c8080c2c20010740700d00c21640c241507290340c0c5800d19000103251030004007905200070003d80c1c6e41 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 818507823 1250 818506573 818506603
    0x70503072c1305070e0f030c0f0a030b102d120317100608160c03180815070e010f02032208101e06060203120c0909090c0f03010209150c 60
    0x800120400242c0c002e20303c01c1003039580340c0107003c44100a001d48800051b041c00e626801254900300c003030070202208508180001c190303080c070345c0d070b20b854a0401c401e0039141048a0810300c0c5052100c00308003081d5030128116800c1000070400c0c003401076903003c0300e2801101d0090004001c0001418468080328201d241c0b1034503240306a00304000220162111b6100b01d03004210600c0010300344039900703500da0b002c1c9040c944800380070b1000b40d03030115804501c02c81840c40c80440e40c00003240d2010704002080c50513900c81d41042d094207040c0030140505501c006868101f0605510680c4e4465020060707030020901c80c0c40b1000c1050750821201489105030f00a031240340b07c3d0007150b082400d40d41d0060020720340340601032501220300000c0001580e0741c0303008600140c1e0040112441e031048106503030b94088140803244c4e050401301000525100f40a80d0109101d41c051074421406161614852016910481c000c500d0144414045850108034402e141001c14011481141611050201701e086418070 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 818509073 1250 818507823 818507839
    0x90b0306010e10020102090f06340c1d09010203070906080c0403060e01060306061211010f03090b040302060603300a110a0b16030c17040318030302070905070503072c 73
    0x3c40c0c00030300030341101d2400c0e44601d0a101c4c0700c0b040b9052210480b0310f412051441050000e4544100344282d60900412050f130001c03001003040820901039a0401800140b00f2403038285500800034500700c9405451200300f0b07441042400f1105400c10485000c0350590309144850782d031020b01048450045034006809541411800040d0040c10f601010517280b180c042084000c0c0c0b1103002c80380c21802c1e00001401001d5550f960402c44d8000d20b0410040132103848c1c0840c00c056540e4540c840300400707442c12409a07210005200d1030b4502842218100c8201c07820382010048084011031500b140b0340c0e07000c80c1001001801030399007445007242e031300d144200000321a9084074610780800d01001c212a422442c60742c9203020400e4600c68003e8002020407035030340c41501028103003503015100d03028000710705000d00800100c1548162080d8a4001c3d8040d401a1042c1803038a0504001d8820041c184810081c1c108204010341e40c01c040544c003690098078441d0708840d001e00e10340304030f0f0510782c1c5890740c44400 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 818510323 1250 818509073 818509099
    0x304022112040509100e01030602090406090204081b0328020d08030907090b01020a03080c360f030601031208070e1522030b0c0f091206071e090b0306010e 68
    0x144401481100c0c419500c107003e5554007000005c03108080d00400d94a40e540900400c0801c0c2160044c3c10765900c0140b0015a660ba0f580c10342d8101c0c0d1040c1c4c4500d0480d044404404840101085c507140b840000313a020706044070416404210003000000c00d89001c0d24600004c0c4107544414140300c40d0103500c03107040c59490500c03540b155500c3d10180310319a11203051848a9035694030200c0c9920b00740340e058032050002d40304e01d14104601e03000340e094411000200b41404100d04408401e003844042c1c021009481908142c05000c09400700984c654000d9201c080100300095141400254441c51850200c140340c4072040c049a003002d10350340b030513031180303804040c6010b0007030045c000c00300c3c0a4800f07072900d180c10340c0b4226501d080c5010320003d408200c0d0b200002e00c11034103080083c00589010003c152404075071000103404410645a05001c1c1d41c05641000038450b081826030b15040e0110068807480b0489100c0100503001d98060351082c114040045001d80e401810300401d0708000620709085222 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 818511573 1250 818510323 818510353
    0x60301140306070203130e070e040f05180105040b1513091101090602011a0411040812030108070602070312031d0a05100b0a0602030910090f0e040c05060a0503040221 73
    0xc604000d0034424014000415a01c90000045400c0c159001321212200340c50082440d00e03001c402055081440280c003440e050a6480b8440e840451030a03401c00280303424854071001f000c44400745040007603032401041c07001207610055102c1c1d100720203600c4c0b48411045640865038205038003e0012690303040c80044410000303100102c0088003400c1e0380d50040b2668581c42242aa03160410f400c2400780503000001150400d1b0704134100c440e002204884c6029940d25540e468141861550b5110001c04001801080800d00c0608020f001c144000d0203c0c9085444004820044400030014142d850017500c0d4094642e4039561510501c0c4020f40f201c0704d41d1820031548907089890408103c900d0140820f07010700d030000c0074105039141c41e4011070800e80c80c0c609125400030744810000030310185d20700009104008444140141501000c2842a0300305454000c3c00307040c0c00d8012a00c182401d01c000c05d1056444416286d000f43c0488145800b0130008601c202c20011610000741103010ba8609125103c2c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 818512823 1250 818511573 818511599
    0xd09141908071427060402040812071e0804060302070f060e0307021206161d041104030b07050405090f0709080321090d0c1407050a14040b0f0306060103110702060301 73
    0x403034004041141900d20310030004c2035446181c100080031400706032095000907120000b0362109015000602e440e0300c0f0607100d4503207208034002d140304034000a0341800f0000b060070807108040103035a901c558140240e5a1800318011401034000305540890a0414404a0344e0801001900031704201b01640042a03d01c1d00e952020100303a005480e10b951302e041d03414000a185200e000070882c5842201120001201c100e0040c03290318414040f2074407000039654580c40703085003085841c03032020781d40c03880d601d030981c100d0030000d04402c1401000d00c801c019a07150001415800501c00c1c541c1100c0c0d81e40d484050341ca110301074006400d20b12012400d600451083d08040004204261a568196444030905070343d96120f41c61080009961382403000000c1c0c28101140704182e801d00544180d19141e6021035204c98503648600305c0c0d05144101400c05043c24840c41c00451002c1ea0761910004031030010907600d54018200070f04155403002150000342e440c005541e0650781c01010f107a629651038020079080 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 818514073 1250 818512823 818512829
    0x3190306060816080a1a280801060821130f05030f0105130b04171201090b01030513020f150414010806100f0c081c1505030d0914190807 60
    0x1052010700480c036018410807803001603c0c45544c420155650318402080074084110842c0300403408543e150f080b680c0e03080d14032a54441c1005090300d001c0c540c644010940840c41e401005541d00d440000e000340385003c101350300c1100c40007080000d445961001d034a2244039102c1400703081c50008801040641038a802041224002c40850340d144000c20311680c03c850301602c00101050302e40600000045100036026480b60160706030394404030300401101070320b60011044588502c0d03400c005110200c44c0c1d10801c40d48035400e11f010016494032001c8070b41420110790010307111b000c51100302001652920149588400319040c1c06444030341c0c88000d4000010000d0500c1d008c144042e00140c0070b82440b2548048500d210350346c50016207440305007900d40a980c0801900c91520420180848200c4501100710000d0000400960000d130384800620b4418182c01941c0b1035000203191010841e03101d01e180082d074200c003103134072030407443e5100140306055615440b9403440c0e9039450002c0c00401c0403a9590803 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 818515323 1250 818514073 818514077
    0x4020105040320041109030c0f030f03070302011506030e03092b051c020a17030406090f121808150a0b0a0e0a0606210b03010b0616020a080109080406050c0319030606 73
    0x5c8810340800c0c0795800d000b050306081d0140d0000030501842d140043c00700c0c07681080901900e030440ca580300f21a045a115890035009070f9101c5103010311182c04115440c008100d9850100b141040c0055420384a125014401d84103000c000c80200100c40000c0e842000300341d8501d04503614030b8807440c0054a4031082079001c00c0c840d4004441c68020760000c5040c0c95095801610148584c412103c0c00c0110341019005450903603a880070400028142c0103480700140c000c6400000d0011441001886002a804c8271540003410382402c004403100041c591003c1514801490070726030700d04603c00d00800400164aa20985442d000100c40045072070150185501c50018001d0780c0c0c403150140c81901d1455190025a2441e0744051249801a400545030010080002c1403d890200028040340c06c40300314a1040070700e0b06030003011454035510311001022440007d00c40c04290f61a03054080c044c911403181400070002c0c40b420358030410701c1100c05007910307460800c84450102c6002002440036000d0980 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 818516573 1250 818515323 818515331
    0x1504110a0c11091824160c0b01060503060f04110306011b150212070305090703111305091c02121803070f060302120a0b151c060b03060102250308030402010504032004 73
    0x10507017201e0480101c9800303902990905516030780c0e188a0580624101c0e07404001d05d902d44038000607403a100d443d00819542e0383d1240ca9003060801c0140341125a90400c0c829450240d0071701805802c0c00990b80d000c0ca090801c0f440c8803450344004110b000c030020b40100404c200d00c0c2031f484421144d9002d061148442d00350103000b9982d441c800c1d01155401d49030184aa4020744040001800d000d031820301982c0094011950407060001507820b48074290703088400d0ba041506404460300c0b12034040580c40d1031074401004121404202d4850b07034840e600d046071075090a80c8021072261002c1000000410100030885c0c1c0300c603030302c00e4024000d401c40345001811640a1000c52004103090081c2c0c2c4590200503c400e81440400f103800600da4041e0740e003449801d00205298400d200305100d00001022403508103587c80c41d00c031000a040c03121071041401d030042000c4444800c081840c02d40300c241c0e50300c600b0150b92a111400140d82a000b02c3c1e00080045406918442c0102d800341c90200d60000280e600344 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 818517823 1250 818516573 818516593
    0x10051306050a02133624150309080d090302031b060106090501090302370801060312030204080a0b06041d0a141f02090a030203151504110a0c110918 65
    0x80d10400d250142101710240d100f02c1c42c02c2d4082e008414607928000031500003050003501c4c1c0c1b10b412415544080400d810040082000401c1d000c102c0d14585001c41c0c6002c200c40002d030364480d0382e180a0070072401c090503910009641014002c02c21180d2440c0d480440801e00082021159903030042401900300107920814000781c0b42d409030b0580070540380d005110504800c584c405c2030f11840b07100c5021003112002c031701d0b80f10b41028801103010040c07c0400000b0031050f0950070040c0f844182008040d04141c0b0402c0100100800844d580165990114202001c0c1e2174400c0000e0243c8240800a0714021003030900c110b41120000d03911820380d01c1060608000c401c5a100203440300041455103188906c18a181e9500e01c0ca180e00078041100c0052110244540f42d8010031b1820048400319903151802d0018404500001860040c810130b044800f0700040c00b046d00d090066004500118042c000501d00355020041800e05140000c480501840183d1803c2d60140400c80b040105d4010180140341c000 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 818519073 1250 818517823 818517839
    0x30114030109021810030212010905011404080406050a090b13090f0e030301060e0112050c1b0d2f0f06070e09010305120310080f0d14090310051306050a0213 69
    0x4851550001c2002d6404034801c2c3c11144c42040080108806514241c00800140d0f111040b90700c0b140e80080001072002032910f089400c5403202c2e141034142d00c4681c0208030008200b0400c440c20b171085441d02035100e00301400191804401178100d42100d00020a80118103d400404c1c10201e5865000900ca04040149034204580d2002d00c0c084880c0c0040005005c9140501c54215840300c06150404c805850542810111401665000340c00480061440040c0401c020781024403541074002c0c00c01c2d140d10b010041c0a80c10560011001007103c924030740710481800303c48000308a04030040d151a10200c1b000c50703880e1002114824003041c2c1800c00b61040d402c0c45210139059950040051405005c20600b019051300000c01c4080034414081000c100c0b10310a000700103c0c012071000520410280f400042d010200c00016144450740c01d1014483c20741e40010814081c204480002459072562154070b09007040384040138100500313000511a4030b1001e6401403100407061402c500041d9195109 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 818520323 1250 818519073 818519081
    0x60f071a13151503080a0e0d051b06040602071431180b22290705030702190c0503070f0302130603020a090b0a0e04080a02010e2a04021e0301140301 65
    0x140f0418424401c1800000e01140c0140f00c140354034242588490242c9000409148c02c0b81d00840303468105201115016005048a21500c03800f01c0310302c0d0905041800084d5038240c0c0344100d05680005802d61003003a201e0b4422030310601d08808000c9403541d4804144803106c1811050130a10038030b405142c041155a0004850015038082e1410002e511401c940f400d207050440d91035011680600481e800050503143c80c18844072040031181820300c400d404072448590b00404070010300c94200104030940e540418800d030342031611a9881018005800c0440751911340c0e421254040c41550004548038071500b00700170881788200c48001d1811020412003041c0d070a2840000d4104e1000300007070049600c0e5401400a04901030661542117540714041027581100303503410f40d40d80c08000303060f015040d828007076689400e141700028403500e40e00d01240c098010448080750510301440003401215921501100c00b01c2c0030b4031650b014951940403540c1e40c02ea05c20700c0380b170114044000d40c9108a04060003 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 818521573 1250 818520323 818520341
    0x41205071a07170d1e05070206060f040c0c021908070504060803191205040b0612010b0a0605090607081306020d08090303011701020702031507031a060f071a1315 71
    0xd60707420001e00703a544484188030500e0180518100340b06514100e041d511920340c5d9542c1c41d450300304441d441020100206d800150840d130854000c24204170080e200c158003100c40440594000800c000b19000407a00c02004801c000d5000e6821165205000000110b5500b69240035040e5a45240d981007000100c4a15110701c0995030010700808400010300000d590b21440c03103041c44000c036500d010301401250b00880b002c0b03d143c000203050000301d05050074011440e02e8500011c001505200780010b400d005c040c0705400070030000286034082520b5980503030349803e6001c04420b07100d0311900500300c1d000480f4000c0d200148590407150640500c40c01ca541d004503c00d0700518610307400c280d00d80d07400612090b241811503408029203001a1020016200200c40329500c160007400e044500070280d490307149800805c5100d000400b071050383c0e06412940c05503607501100355200182d19028140e00c0c82c8001086070165074400304109510154000d1441e40c3c42241c03144c565208012841c422684160 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 818522823 1250 818521573 818521619
    0xa0606021501090e120d0204030b1f0504052724070e010302090d050d09241706031606180608071e1206030f020a05010e030d18050604120507 62
    0x3004003e5980140e210742d10740300b003240c01d640038040940c4150385158021a900640b480c0e00082c10418040052049a01310301c14501c00340c5440801101207104040c82d0056030b102e00d41e10400300d44282400020151641c01580d103031401c8159000740541c403420002c02208800300900d06c241d0400f03043c0010f441c0f24007420f03242c90084609404c0110000e402620925411103424208080031660821a0300c00c2031000303990b0744017240e00b4030300000b1280c206442c06000d085040a880c60450b41c00c540000511444c04144c07400540c0d8100c0064076010b01c000a07413075100349035100841c803981d021440e4450300100c20290b620f581c0c2d4490080314101412500100000e003080a604a0592008840d540c4e4071420310f400c60040c06c400840d00201d960340c2d4012540000c41031449021410700707000000047c0024280954000756040c0481d4403180480d07550b07810050010528502041c50300c03400e101500e80a4261903c0e03d407074141400d180c0c1c126610a4499100311000014804814445200071000070 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 818524073 1250 818522823 818522863
    0xf01090e070f03080c0f010b010e040f11040608150d0f1214180f040b1c08070602120603060a061a181e090903070305162103050a060602 60
    0x111054a00030314800c00480c566010755400000d6100328074060074069405402c0326aa00c3c50440945072400d07603c2c400381e015907410183c1001d6113a8010a20380b40d800025036010403250402d0701604000c1c1030012802d550024003250100b815544035001c2031041e2404e0494080231341008007007049a0301c8109000b0304101d2008400307030000f02c600141c2c003e102c0c2d030307030a00c6210401003010541c103a800c50b070918007005040b5401c40b03903185000032001c48e41c100c00351342c10071000702c19a02252122008600104800110b180d0030350410642c1011900f08541251046403104c1e411416005000d000381c410906c24030a800100c1c01850040c46400115000c4040c02001c0940301c2600c907101c1d0700000e2510107100c2d00c0032016050b5490b410b00001c030180c29240d110050301201d5081040c050700140078000c82c0e50041c4501c40002e82c01208a070a9006621503250044e072203440c1138041207554900c480086c48a01c4440c21049405812480c00f40001d100e003031040caa00e41008a99520703030036840407145015 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 818525179 1106 818524073 818524079
    0x608150405041208061311120903090102071a0c190605070f1b0606090c03140c09030c04020702010e1c05010605041814280501140f01 59
    0x8450800842c1015115100210b02290044050004102c00300f038007680e865544144040c4819401e1120f04818003890030300f42c10000313403240b540500c100810008a80801030f07078a4804180d00426526291074184c13000348508041400f03401d40104041624540c0500c20003840824071130182d60700801034689501201c5d0b00410503020001801030180c8400d603c003404019210858080c4000a555814840f00078041c3c0e0f400981c29034a0003c0940410f50035400411600c0c941c400d01015550742c548080c0044c0c4520802036600d504000a052164034003640a0322900d4018075107120f20503442c1002c06c00c01180c2c0c021013030781401e6502c000400c1040900603800a0001540c05000c0c2518199590300540e4860034000c00181a40c65000e903a61300800c0025421040c0031100070840f480080c00c8100c254410000765180c0d4240300703805000c954030104031400b80306445995001d60386 = true := by decide +kernel

theorem cover : BRFrame.Cov 818345323 818525179 := by
  have h0 := BRFrame.cov_init 818345323
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818345323 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818345323 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818345323 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818345323 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818345323 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818345323 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818345323 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818345323 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818345323 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818345323 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818345323 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818345323 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818345323 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818345323 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818345323 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818345323 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818345323 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818345323 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818345323 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818345323 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818345323 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818345323 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818345323 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818345323 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818345323 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818345323 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818345323 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818345323 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818345323 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818345323 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818345323 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818345323 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818345323 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818345323 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818345323 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818345323 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818345323 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818345323 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818345323 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818345323 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818345323 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818345323 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818345323 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818345323 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818345323 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818345323 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818345323 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818345323 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818345323 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818345323 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818345323 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818345323 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818345323 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818345323 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818345323 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818345323 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818345323 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818345323 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818345323 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818345323 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818345323 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818345323 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818345323 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818345323 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818345323 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818345323 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818345323 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818345323 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818345323 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818345323 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818345323 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818345323 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818345323 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818345323 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818345323 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818345323 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818345323 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818345323 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818345323 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818345323 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818345323 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818345323 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818345323 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818345323 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818345323 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818345323 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818345323 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818345323 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818345323 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818345323 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818345323 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818345323 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818345323 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818345323 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818345323 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818345323 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818345323 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818345323 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818345323 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818345323 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818345323 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818345323 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818345323 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818345323 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818345323 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818345323 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818345323 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818345323 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818345323 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818345323 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818345323 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818345323 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818345323 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818345323 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818345323 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818345323 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818345323 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818345323 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818345323 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818345323 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818345323 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818345323 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818345323 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818345323 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818345323 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818345323 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818345323 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818345323 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818345323 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818345323 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818345323 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818345323 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818345323 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818345323 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818345323 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818345323 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818345323 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818345323 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818345323 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818345323 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818345323 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818345323 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818345323 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 818345323 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 818345323 ≤ n) (h2 : n < 818525179) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
