-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1047
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T00:59:55.589096+00:00
-- url     : https://prove2.me/submissions/e3396ed4-1352-4829-bdb5-8374824fd957

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 188129496 ≤ n < 188309352 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 188130746 1250 188129496 188129509
    0x10b0f01050c07090e0304030b060303091e010203040305061f050913150f09051b01090b03010306050402040213080a03090b190819020d020306090a02040b071b0509180f0606 76
    0x21100242480c0d515985500a500d00c0e0600c26045504602d00700b41049a011170000082c3c01524440c1032100d0032070780c8900c10f050380c901408883c168488070340c450b074a10000d0350b0a4601d03c4040184140c034905078594a0306071a1500c180c420003041c03040700c080143d0516620340040013074482122049020309000006142e00b030640d83d4003505940800a60f601d01030f1043c2d00c10b41c2081d1100c902841104110b003041600c83c079518640c0100340304010003100c82580714205c005c2c261003c45d541030b41580d0071071300c90b000242130013401242c1095081001d080511803540c06080184035070350003802d1048007880c0041c24400240d2051b20070f11400c3c03200b910301b100a1524884860150320f0300d29101d0361250700000e403068100080b0003102d8400101000845100d80065205100954541c5c1994039811140412171207148222411504144100c0d030004e8410203c00c0c4507082101108001940c03200005044150b0035a081407100c4000c411141c5c4080060103c41400260310000d8482e600d45000890403 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 188131996 1250 188130746 188130769
    0xf040305031e011205010501090c0504030605132406330212030a020d050612250803040b091c0b19110a0e0a0e06060a0507060b032b02010b 61
    0x52040120000b52010920490202468442c066002c0d0a595620407002c00240194040e9025402c000011520203090b000708600b0642d03076034947c0e00c0c10745146c035000020080981080c00f4140d4503000b0002041c0b40003d000001c610020084940200c209001c10480f4140d900070490b107402c0b204100103001408000390440f222501da0360003504091001241440241800d01001c01004414030008028a90160450a070502002c10442d140c440c10000d00f140000035100e070740e5010740c250024104104151070629070f00481f1102c0c47c540c1b691500ca08540060300b0a032100701001c28042544e1038410303074a048001c130485207981c8422042d01c600d00e2180000b00380940c044580d00c4451400072381d07584421041400c100342c051722000e6042c4018403030307055651814402c0c80301040102d00c00000d0fa649901a500c0100158a008403081c01964690000701c019a5080e1341c0c0d008405450300d0501841101303c200300b400300300011113010040d010000c041030380821a890704018800d0364a60000449 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 188133246 1250 188131996 188132003
    0x904081603051c140f0c070206090303191d01020a0b1b0c010c02063301112401080c0108160f0c0209070f140f0f07081908040606090c0c1202010608120c070501080f04 73
    0x580c3c501e00c1001082c514841c816104dc400000c1d54000414650b001210f4607404401100250342d6081035401245d072690552400b8003802501070102d20107112030301c2240c0c002098158881e00f0301c2d4010701d0140c210f80d001103c400c0036820980812100207c00c0c10140000309514180d00200013982628002403c044441d41e41408900881e41c8008081004480585242c1d004101040f24004160800b20303402885000240e101d18480608a503014013041440340d1466240e002c10503100071001c079039a01003028890103100403031140b14051784034408114842c0c91581c0720302201c00f50005000307080c074000c40003d0340d4031340702400700b42c1e1885036400840e0404035140400b2615032095041c424010304c504017000301403880700b2a40700c42003508000e210740305900a04080016903614100e500941b0000500030000980c00c402d40e500044206d6024143e1460314030001400c1d98548842500c1c1210308190911030441c00310302d40c1170000041000c1c03c090b10080c40d00081354104411032000c0742c1009031005 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 188134496 1250 188133246 188133259
    0x3052d04020307270b010c031b0809060406030e060a020405010c030806040e06070903030215060a17011b0306030c050f0303040b1803030304150b0904081603051c140f0c0702 76
    0x1030195074041001c20050301000c00301051602d140c020b42c0220a14035005109294180100c40700d01c2d60140301102e04040d050f4480041c1007012182017412501c000b0000c0b80e02500500c0383c05801c0c0c0700c0c40f010300f01400702514005080f28600792290b250040041a2070030484c0100000e10507640d00c032500e0b01d030580d0b050500003800c0c0c6641c0d00150241c40702241d03540301849100301700b000a560007004042100d01070307003e07140604d104800c00c10b10b4401c1200d02c40d40041c041c00c4104140700d0b81c40d4440c400f420b001c2d0700009101507104c42c1ca042c052202a80000000d8a0b40310520034800d0795158800141400c036100425420b1540200c1e403640914841c034a2041000701b0341c019001c103180180c00d1000d10042c20350384d032440d192900104291920203940d41c824130f4210000d0b11801e0190005001d40e40240300c590501d4106c050443e900780130b41c40d0450400c40140000740107400000025200402d50b0b00f0b003ca606205040e0003580c4203401408048840c88020510252010b040110f0f00b20b15010780d40c2 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 188135746 1250 188134496 188134501
    0x708180a080d110d09060204060f0810050f010c05153705040203070909320c06090109231512010902090d050a0605010315020405010503130c030215030703052d 70
    0x11400340280c81c3c65031800c60030022105c0411042d94001c0c8107841c81a20f030f400d82c0c00c811000407228550304440203c00c00015100c1884603180180c00640c2e0307007905151010410002c0e070b88050622103100183c155181d5044140902103080ba5940459048011615941d2522203a4500c0114441070f0141c41d12541d25000301d02903480c00c1c000030700907004024062284190301d281882c00c01c65040003610044200c0324060f01c1200700311003020650a5401c0c02021041b8006040201a070700c1744030307554184100e4020009000083d084500d80c40702d440c00b00d02036142c078500b046c00352582c412505410760110422121506800105a990640700c0104c40161982c46600125a080c50003680c05801440380054031020890342ea0011810b883c42171302910742c1928584480803d138002d41c016540410814400500b4005100c018814524054485000490741e00e401040c03184840b5541c200042c4800001c109886404d80101600062043d025041e80385581c6040c4020820000e420006085032a02 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 188136996 1250 188135746 188135771
    0x90a0b01140a03051203090d0905011e030e0a0605040605180d110a08042903011512180308091c0503040305030414010e0106060e040203060603010b210708180a080d 72
    0x42c040080c0d075102c8201d45010040405904194004443c540c20350303c5881c109242c858420350700c4500315041078403100b0403205aa005800540405481842055a142d4040c14440e0040014504982c001e0500007054180b60038610103848000340a06044081c2c02e5290b655a42c001908009004683c5440342000740460702450a01003d80d2000e400180003060100d084403c40c142c29444a40c004020700715a01c0d9005000c02c0e501091003248981c4200c030104060301ca0064104600c4c102480702e0024a80640040701d0a54260000342500000d44000c204400168108520b0000040424003881d5071040d600004040c2c5c4001013006040120110101d0704100c1c014036002e0780e04184c400280004980c1696143c0200645d201d01c0300041c003440c00041d15420644210382c01550098500c03446d680c2012102012540415000941c80c00ca42d90214440c2e03480480e020b00079842583c400d00309040900e1030840d20f44c112007002003140c00c28002c0400003200c803400c45007008040c0c400070440c5801e004 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 188138246 1250 188136996 188137009
    0x6120b0301050f0106020d1d0d0215070f0b01090501050904060b120601060203130906050604090e03070b0403090e0c1602040513081303060606090621060b0705060f090a0b0114 77
    0x500350598200018840000c40040403141138400a40c2180c11004540c803046400d80d1007542c021021207401e43c0d11850604040200100d041c0c005464440c20b0820b545000415502041c0d041d940040100781c0709041180d40c560890042000c00c10500c611350404000413510403001e00018441e60b680c51040005448100d0300300344140b500c03c240c6a80390383d21540692680d01020030200b8403c1074030004295070f40c00c0e22030301c416148080e0000f4100703418541540010300c3c035000613000c188000d010000001d10b0500442c3d1142e0712a50750000103901c0e10300300e2034004902600504018205210814002031000c245204081d0100c4001c0307510344078004080e00303010381c2c160003801c41000090003d07200701c004840503040383e124000030016155540c004444010050040c000042e121200103420502d450101009903110440c00288061341c80740302c0503150303021190441d8190041400c10000703018560740e06a201d441c8801511003110345e0b65801401c0030301400b40802000c0403d000c0700c842d840701d4 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 188139496 1250 188138246 188138261
    0xb010605030a181101030b040608070312090e0a0606090e2802040f170d0c0305030106050a0512091606030b0d2402030f0a0c0203070206030a050703090203010606050c071a040612 78
    0x4180501c2683d00e041120160741081c0c501c0d0301007400d12040603420305086c42079004031214200a001228195a10748180800143d0900e0030000550710209a41d054800c0640c00750002030000150285080000741403611141d001042607005a0100910420600d50048403020300000c88861401c400b0b58a10090184c0c1d00521500441400003042e58005105015034180c840000c68100c40c3d24020100c82c01200c44600500040003803004010090192029128607107182c10001e08180c031400c4240200e4004560700b1080d917004c0c0042ea142c640c2558181000b505c0e19160034888001d105010442c443e03031a002c01480b440b1010038403012250517410401481d01940829550f030704058000c0144c40e0703825038003002980d24102c00b640c900b0f80000101d5078240e40c003400280c10759072a80c1b4130700010035000700031002389621400d5803130040c0e400b0b101d60009005503480d03080c3c0f00d0640140c014030707003406604481700d8214151700300c3c1e50440003a401da9040307842501d09075051440044c4c1840240954 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 188140746 1250 188139496 188139521
    0xd0203060d0c08070e090309060703080408070512030a1d0d0c0821061203041404020318100e010b062706040306091a06040c090e06010504121208060604030b010605030a 74
    0x69000401ca4600200310301040b180341545c0c2100d25100c1400c060f49910070300c001e440c1d2000040001c400040d001d4400954014001c4568074205201c0707072509420160700c04e01c011184200041081070b0443c07140304641c0d5081080d0620594096440f10f00d5541d641880710038000e201c13030311a00204000903e401ca0740e0f9a12070658125507005921950000d0302415200d03c0d100c1c0c080808021401c1e94008140c070b0488808034841c0c04030f042c4e810140402540060640102016925004008000c041002c42c8504407120000100024000f11040c00c40d503142d62018420f003001c2282300e1081c810b84484400c080403d0b849800200c02c0c100c00140c0d03a100c0ca42c801444a414000c40d00c040c41151850744032940c20903d4038140c04c0d541c0b14200011610112440b10101e2100c540a1101c0914007401c183d1161040c10b240346840d8442800c4c41ea2500000d0f0200d5039038022f42000c0d08801da000303c003d6005217080c0d07161400c0c1400d41d40d42c48028070050140c40b007042804000945500440d40040c08078840 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 188141996 1250 188140746 188140763
    0x20307030c17040305010e010b0a0b0304080306090411030a050604030306080f0303180c030f0703020a380d020c06011d010312030c0e0d0807020102060609130b0406022a0d02010507050d0203060d 85
    0x6202c52010b018089c40301c43c1506c5010000c0b0b000820307030303030460407244030b0743d4490300b00e0f031855590034204255124080c2c4141c40e0401e20340e000c603046460410170600050302820003015a850f040c85c0c01400d46005821080c4580c00c114030880849600205603500944680c0841c0d089103805c0324114a0708001000c4940c1c1442680901030341640302054407415a4029150581902d44680701403400c40210401e4410132428008a00714011102e291803600c0518107681d01e14040b1300329003c10682e080030842c4141d80c0c100300e0040000101c400100e500b0016a100d01c8800d5614540300e00511111803c5210203064495a00103e01031003050403014201d0300a21120000d01c40e810305070f01c16080b2250807405849003802081d1545000010a403281125441c2c14240448540e0b0340d10b140e00001e00219a266002c1c42940080d5007640c0d4544101140596521a01d60f13481c0f24107031400072102080d0303055900d4101400a010740c41000c0b24040c0d8110b080c0543d032500c40b10003184d111304c29628007401280 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 188143246 1250 188141996 188142011
    0x2505070f0303080a02030c0403060f14070306051c020121110301170f1b06090a03020603090606030607052701020f0106060f140f030f0402010c080703031b020307030c1704030501 78
    0xd068401080e01e0107a80d07040010794801c800c1408a10082d0350280c0358000a100230000542160400d000820400c000450880181c208005448a003592400042521004188046d0a0401c00d214060340844410418040142c002034059064042c0031004c503130414940e031030301d142c0e10b400400b2441a05181d041d40c960795406595400150355040342c038540120413000c000d0801c001040320164540007190054070f10003904100700c3e603000003549034210310b0513100000580c0e0780d0707806540318002410140c0b1180c0b0703011040505000e0000c21078018000c1c2840081e01a00c0c2020b44407207809a81e0340303d500b81c142c43e800140d00d806040c01c0072021300d40c20580f01140031503004003403404141d00c40c0c4603482c4000c0c048203021000e0040a954411040c400d000007400214454403a903005801810b210b154541c45440304800c55006039020b0b40170070f89500420328010040c0290380b0002d00140301550a00c080703030f0b4000b0010041040701900446c408402036203014030040c205c4000b9a405802000b241 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 188144496 1250 188143246 188143259
    0x2010c080106020c010f03020a021e010608010e1212070c0f0303090201180303021c1407141203090c090a0f0903091403010522030201150306052703250507 68
    0x2000025110400548204000a00c041c0005940042524140c540151001c4800004c40c020340100d44007400314815003030340c40602a5103040c02180c0000480000c1102c504100050b400d441c5103a008844135401401e00c7c4480005040681d500c000f04404540c48540fa0100116445100c0350000350581d00c510707210f58105a05940070b103c1e524400e0b00c0b40b070307a41001c0c0c00700141546014403025002d600b0003940307541e010621000e0801c81d0b28041c10007240307442d120034441140d0382095404079114012001c01c003881101c100a110300e0165a00d03010751841c5424401d568070303106040c3c00315000e0407490002c41c90071441d1b0380100d03510b80b450200403c05103070107060007480e464062050400c203035007500c032420150506000b4644030382010003030983c00322500102000208103a55040c0c045568800d038143c058030100d40c0c2c8400840c09200045814146070f12003040100302180c0040100b4500f540e00f03811040040165106054103005400307200d0107070407429200c4032812a008056000d03001002c01d01 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 188145746 1250 188144496 188144501
    0x2b140705030402040605040507051c060305030a021f09080405010804060902060c0c04060905041a130602120610110606060a140a05070512031003170c1e010b15040605030915070201 79
    0x42d6008507002c3c442c280d5203c040c0022201d0540d400e0780012020000c1000d90044416842505000c14a00041203035807901c0300d81c00c541008030410010b070840401618490800700701d5503d60000103408011003000d40c0d40d8000300d032003144640b5061010810003c0c0920103240d01040703c050700079009603035418451f040c0030b48800342c4010091180780783c40701c00b1031417420510555100300e9021481013542d442e49014040d410700300410401000400030b0340c00c000910b01d80003802940f11440c2003c90325041034010440340110200c0d01c0000c2012006041c2d01c076560000f000d50b04040c0990b610360351400e01100031640c50500c80600820080d00241c2c01d080540c0c0007004003c140e01910070343c0c0214500450b01082c900c403c0d00c031319440c040603580603c041070844a00e01c03442428882d1071841c0210301801c007400e0482c02c154204a1070306262510314900400c1c004e0b6441800300311404a100d40303000c0b095961364084c50040004205020001034cc2200c4200000f400b1044403200040d903925100300d00a01 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 188146996 1250 188145746 188145751
    0x17030c0f010617030f0d05040c09090c030b07050304050d1805060403080702030606180601030b04140703140112150c14030903040f17060f090106050a0f050a06052b14070503 76
    0x544540f0f880040381c01c940110a83c0d0440442e400e4440c17801001c0840180034244c081c0c03040c0c4c0c056245e100c000410410b184207048109105142c115000703861401c00d19920b5000404110520000b0001c21001407008a00e1080d02c01036410306404801b004840646500c140380c101681081c3d0026000c000d2000ba41c0c090316050b84200d04441c0c25585120500640c01c0c00f00c0100d420480c1200081070680d8081d07005204000c4000e080003402e09044a000c5e604100140c500340701007641d40f00b55020310519084554054140304181c8500c418060795a03044140800500d8000107950b101013154582c842c41c0002c20301036a442c60561a41007070b1050b40d807680e00c00d1280600182640703000213000e030500840c0000000a000c00740c0901d6445201003501414002c2003000f1039540d5150105140c0c0d18503802070007901741c02041200007806c200038810034080a4210301e091040a00c010556582c0720800c50850425030341d0000c200002824651025044c100005090380d2030b80810804200d501c200950f1 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 188148246 1250 188146996 188147009
    0x3030504030e122d030d0203090a200301050a0c32030702100606030908070f020f03030409061d061f03020c030316021501150e060c0106120218010e0117030c0f0106 72
    0x5440103244c100c0300700d0000c42503249410382d40050280b01e140101c83e0b80030f941c2c42802c80f000c0d50719a800a62340c0405026808100444040c0001d510301850704091103055800740c65417508004c90003080d10060400d141320201c4196081440c988990010702e03012201580b0041215403e4582c100b20394083e464151814030880c0b10b514021000032000d20a0103505900c43d002484e25203400c90070703298070807c0000ca0b40c050381c000341400300882281c0c50410090000703006100000a510782403004084048110700200281c480150050185517600c00c0c61900d42603407000f4210170b035101040001d40181c01401c0c1036983d9404080100b080007555442900a599015400e40e40e00080c90440480c0c010400e014098088541d0415402441d000da001c040c3d07043c00c010013880c10000ca0b01c41260a50742e003030304241002c2500c01e2040702141403880d81c1d072002c000b801d600d074242c540c14a0355400000205208448590500358a00d00782244c4c24011545004811401d6070f101090402516020300740620403034 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 188149496 1250 188148246 188148283
    0x405010807020730051b01030b010903020303030c0918010e0106110105040b060603131407031406040f080a0c0501051302190602070b0708211605040b0703030504030e12 74
    0x30401803021500d4401e5034004603050f0403508801d204d01002d00c2c81c0b00290130f480407000760840007080c810449030341c002c400e00072001d17044615980018265a081c10840b41403246500003400103035404420307a58044071482d0065121452034000030845203080d0001203100061400104120b00fa010b0224140ca04545499a01130000140c6500700e40044602800000b190000319000d40790110096410401c030543d070702c0c0040015203542c2461410031184540c80d900940c010010800178400c00e031450070401c00604001c1c03800c0e450b4102a020708000c0100006400500c40c9181c5000e404540011504400204124500143d1041303613280760391801d910034025002a002d0351290b00e54020151440c96025040c1d85190031840801a0442101260103500078400749900030458400005403d80d00003d038004c90602506001408a620b0227003410090108014052081700400326a0727141c1d0b0502d00010030380e9880c2000c680c0200d1401801e0341c412418206a41c1c0d94200107440041030890035000d = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 188150746 1250 188149496 188149501
    0xb060712020106120816050c060c01050a050108010c0815190311010e0a0501090e0613141626060a09020406110708010e0c1014030c0d0f0902210a020306070504050108 73
    0x1040f80c40e2444c80b0024403642d0104480e030145c0354050045280c1c144a04100c4100b000310800003503240d0015090309c0c017260364400401c010008103000e020700500e503080080001c0d0b01c050400070081c0d10300900b4041c0e042800c9564140c29180e103004500790140e0181c1309161103440e464813803c030381c9840020a000600c12010300c1030318035040e400350085600c140c40d20b0081910340f01d5175211150004100036030041c10100f0800b5101998080c41110b10040d0445824519000c013044400550381c450003000c002007071074000903203107a000b41e4001c410314641c004403c40d40c560000480d24040c0d07030400c8550304c1c00414005440390f003144c02d586a00c50240c0c15a40d145840b484658200d81d45001040840d81c08903103550010300b072118105102801351f01e851103041227042031030384880d8400d451600c2030000c0003945240c0128144541c40015218200c14040180c0e5500050108202e6540c20040b060062050010f20102040382d00b882e19409802e45d4410301d82003d025016411910903503002c0b4952400 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 188151996 1250 188150746 188150759
    0x312090816060305150a06140c01051008070828020d0501060f050a0506090a0603020708040e070e1305070906031104030209180c090405030a0507021512010609051e060d0b060712020106 81
    0x10350303a00c0c1d62011b002440a2031406004603021800c1c6032801282071020421828030680a0117480d02c545511303580340851a24005400d0324024041e1710a81e91a088416907040e407804184010074290303803070ba624100c104418000140800c1010388001d0582d8038009000901507000240c4908440e41118a20400795882041c40100e104400000741d00c0a240035040c049240170360301800f251401000880e007001c2d140d110200815400359840004076050f2001710b038440c50300b6003915032000c0b0303072400a201a040c0070402401d1010640100424141c4844283c040040e0341c1040c0c40c01583c000740417074242d042204044180c0351407003114014500400d81d442500d0b00381050f1540c0910f5000005500d407014450040303442d50441c29003240c4c090201c41411840000c8500a0240d0100f580c410704032651400302c001d400030040d640074500511089082c00103e040307211000b400c102043d1851a903030318010102030021b00039074007000e511000202c5e0321402c0c44030301c0e00b40a6080701a90005c00c02e0307545421 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 188153246 1250 188151996 188152021
    0xa0806130c050715060f030302010b030d030903080402010f030e011d1203130602030c0f0a03050603011d070e040501020405060301170d05090d12020c030105090d0306140a0312090816060305 83
    0x30445000710368104641d1000603030104405130010005440060707526100d03070072100220b038035030300a03001131303442c1c10f01c050f40d5240a220301160340030340303013002c0010601c0350790003034951400108060306107c11409024401c5020350400305841c40088002c020003807042007000d00034014140c1240c0240310f40c0c0b10300046400d01c14201e9000d103400401c620000c620340d40d5a403002e076000900302c003188182070148003070154805d0082e10203c00151030100302071501704245401c541c100d03182400c90b00d01c40f0868090100300800e250058542010030041c0560300c42c14114003912136075111350381040b400800040d0100310b00704148520000c10090780c62212412001300c40c28000c80080b254481c558440300000980105d607010070740c01c12401980c403000403210020b0708440c002c40e0a400c56800650320540c1587e071600c82c10b000703051400130241e00088500041200710109000042c4074140310301c061205680117086100042008170112000800020b4004890306210720494010a042c200451406500a03 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 188154496 1250 188153246 188153261
    0xc03160f0b13230a06050703030b0316090b01020304080703050d02070807260c0307240c050303070804051923030910180b1603080112050706031a060a080613 69
    0x100e818142003414100d803816101d040c3c02c298403103280c072031034440902e4660705a80c000411454a403d502c68a0a080180c192242c0c960b0f141c0c46504440c03052f01c001451403201d00161411000c002803040300e4540141c3c914480c50b004070070309100721080001002000a001011000705900f62080d07607a4070b0100030b540f103c950042418003070b19030700c0d007010180c00d0340f00c40900382035040c0456901d0518007001c0b9041c404180c00040002522050340d581c3c00424900d64200c1280ca850404a200b00545502d6180c1c00064244810030100c103000c0780c20701c2010052070b2414080441a06c60b103420a20f0495490a20030142c098486a014200b4440c54008020348050325005401071f400d01c141d541f001c40301180c4c41446241d103004541000b150040c100c4018004c200c0c070070a04543ca116107070401a21490050303020f80d04581290300c1d9400000e00110b2030744201c40300342c10040f45502601ca60b4054003140407810f2600204007041c01031840d40d11540e075030f01030b0720203030f8915580c81070b914902c3c82600d005 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 188155746 1250 188154496 188154517
    0xf0207060c0206090a030812070207060c0b0f0402030304030b070302030411040506032104080d120b030d050f07020319030c030e060901020a1106090402040308070b24120c03160f0b 79
    0x200c500c440c00740c1003c4000740f80e4088024020400c05459940d0310511360000c9003140a07040800080140c025010080364014201c903051005145072669198440d040b00240300030501082003001c81e0444d241041a1400345502004900b0760f40f0703002030024001c0d04216000e5600e07482c0e403120038005051074030171a40145006070241c02ca102c542d0700340d40c0c0b03400e41c1a04d110401400c200000258420b00f401541000033311551502040744940743c0100c1a00c402080d168400c0c1c01c401000710840e41c0080446540003400c0401030b49903e51800041c0c1460003101003003000c00b544091902c10150301103001d41040740320b44c49109148003d2002e04c02540115880580035130300180100707021031902413400d803089000400c00f5142160190108081c0d0b089607108940800020880404000310102c00303a074041039408216070708845440b2140440800024094016001c55090707000300d500900c41d206a0740009811114a208002e07590580d804c4540f0501d90b411000c0f5101080c25054001110052600d = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 188156996 1250 188155746 188155757
    0x706090f1a1312090e0106020c04061e030212030d0903030b090a0b011b02040b10051e250f0b04120f020609060604230c18120a06020307030612050307030f020706 71
    0x403982c1d009040103040d54140141305841500050000541c20312a01a007010fa01a1465060301c0d014841501c0130340d005651700003118852042c43c04020f040000459804950000700039050f111400c2c1988109181204102e0412a400c014182c044d00104618201615080301550303450711a0404c80303e800f04d4090000314050b109030400c0d00c114150081c9940000c0c40000c588014100060405402c051054041200410105013080e03004a141100f5a9101e11042c40e0200c001e04020300b0742e41404550070540c200c40f440c13105011410b050030481c3c0758010045011401d06003003400c52441500d2a5800103008204040c0682d407000c40c505000300082d2000382050b4594408100240c0743c6410344a0840f0706404940320b001032503240c6140180910000c0698a03403070b45000a40e5629001250f074050344881b40240741001000035040c0ca0385030003110040c0c0342d40b00d0030000c40c060300d081da10124a450a200068060040c0880104007291080d2611030107212442c1d070690716642c0b6442aa804942e = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 188158246 1250 188156996 188157031
    0x402091e041503140f1c140c0109030c020405060a030305030a0c140703081005092a0c1002030108190203070603051306020414090a2009060706090f1a 66
    0xc03500248800180402400070036198641501c40c0e1980185070301c1a60018001c1e1228a41d1340020f1244001d684800401340900d121000e01004d1000c912035098002c109a030741160520460140564451a902070f000780300314001420003c004103001e031426481a490300e800300d01c280c54213001d4ac800301ca500d5124241950744050380c2c1001070031490721500920400044450145007503034020901d461080d10b540d00709007400c8a481e0201082c5411090050340e8800a00250040f5100070090b94803144030000091039071062505190b0082e1203540c1340600c0380b451044585400354000e14140e48400d01101c0c0703005500140394800c14a40007020f505500400f40500c0003601c0703a000395601103017000019024103180d550b002c04aa0099210300c10b401d100c2042c8120340e00e0025102500100250018440036407044201d00d183d82501700d16030040403000440301c1b00c039101d0380103460509400080400000c8864106142010300310b030402c5510b0920907031943c40079501c019400d1301640c1c12880709040756 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 188159496 1250 188158246 188158279
    0x32a0b031603090c05190e130816140304060c03110601060f120b0d0609030e01080402030304060c1104020a090807080f030307030903030e16080d02031801200105070f0e040209 77
    0x800404109684a80600b032000c01e246c1c54590201481581500b01003220526150002506d800c001c0c00350300358040744e01c80081c00302d200002071f5182c000c07203800c58a04100191a0106180c003c80300103602501000c0780006110780c001503005010ba00944541000c5010300c40d0071a1204d000740212030208503e1388000c1030080c80b400994912022014001480d021610300240ca03481090100b2520785465145200801d507010303480ca54840d10a08182d80581400c0c4d00003512030040380144000c11804204800074040340390300d107111800001d442195241e02030307180100241c5940c05450344030706c1408800512444000341500c2504a4407000e54215210160100d01a001c0440300b40c0405032034031031a10440b41c0c24481c00c1704170541011003c03052440c00752041e04041c0310b8800d04003550418800e89031a43e5128009a03655002442e184400c0c401d0184049107440c44c095411507158070b001c00300001c403500015292082211502c607400300ca0964030030031050380b04030051243c0081101c0d00c0c20f52a07 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 188160746 1250 188159496 188159501
    0x608071206150f23041503060e100906050412080f0c030a0618062318060103090b1e0105040204030519020112090c030218060108130309032a0b031603 66
    0xc0c842e0890018103803994869900d440866250450b12070542d030564400d00c041003064908a50310b00640d401d01900801203e0300e0004406031001a010540341d11b0344a81d1407109005504447c00010020061503c40c0d09003003004107400c07641140c1c05030350034200d4558540261040341c8241062000907982d03648404000c400c41c0c1010b0303d84a41c2a84442c7d010800d03101c1c81c00e15818210104000044072407130410340c21540145d050b040c5000c581018003144d00c94503051011990044007000e40c11580e103510004230001c11480c0805012500302000b442107811a10481e00c07074400a98585c501940d032a00100700c03c0b48070710f200007006030b4040c8201d03c94a200041204401c40c0c01410407801448030f40c011308095416031081124407001d002c10506c214600140030f040342c1c10301c0701283e4500346049000a070040c4030240c8a140c240302c138560110200751290b41d00c580607550001c03601070b0342c029040d0071048019a50032000c0000b0800348020841090101c26a031203040c00d8840060041c8400d60240d00 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 188161996 1250 188160746 188160761
    0x50c03030913020d09080301031202010506010e0315040206120c041d060a050409140f100e01020403020904080d02040315050712050727030c080307120f02070b180904030203030a0608071206 83
    0x140c4a40317401d05034010895090240d4001c50246032034460000d0180030007801c5a5004018505001c2460415902d54800098407400c12404100325200c0d07486500001e1b1040c0110300b07440c901d400c9040104000c8030321203030140c0125109000c40c01c2c5846140305101e803140b04c04445454004450b498208500d15041c0c100c04990360158010081182c035042d001400d001180f99000318560190056041d0118203108402c00d070f001701c0d8000c41c280f07411903002400e0341c000600084d000d04c0780490403801100c81641180c00455100f000c070b07040040021324001c0600340490b180d102080581c10032224140c1c00e070250611610322955204041481d007080851182000c41c001441c81841080100018082007801000b4021180c001d5868000c545000003400c8103c02a00341004102c0703020f1100700da0001240030688200040594503044541d9800d2004250040c105910180c00341c1880107042c3c01100450081c00300000501025881f1641030340e8854141c898240c10030301e0058040042501c41e0b01c10340 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 188163246 1250 188161996 188162017
    0x40605190507060920030307080706021b0f0606040506010518041a0a1e0b0406080109090201030e250828020307030b04141c0503130203120412050c0303091302 70
    0x103003082c0c010303200c40c41101c44144003124100340c115001304002500e825404507146044000703500c3d000f00c035550290240195540184450307004501c1e040e00140302d0b40d403008440052022a4519074014401c19518031043d560303c0d010b5440c080100f0303103d5100e80111129042c40d050406080300d030007010300005044880b2010143c03010560500e40a90310000c0900040c01900c04048001d1240e00e40c80d008100745901402d25040b00b0041044081d8026a45a0444020031000120200c107400142c0140c6420011103001c2c2c001d108030344140304240804101c612894101940186465894031a666041102d86108001c214503500800844d10310083c041c50f40b01900791000c4c59540e41d10310410903020380c0c3c00c0b40c0b950380615885401a604001c00c00c28490720034800d0710b14111680026115100250020f8005d41d084021481036440400c5001c04003101c41c801c0c1a0395036a2600c0120316006140c004407480d000c0c0311290260b0740340000644000302001818101155504440400254800412078 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 188164496 1250 188163246 188163257
    0xa121b0b06060d09150b0609010f0e061207030c020f01110d0f11030c07050c040203070c031803080a050a030608010e0c091005181e07080a020f0904020315010f0504060519 75
    0x20f044120340b8003840c0c0e8403d00c604c00d0750760404480c2c0806010344582c660f449002e8402400138203080c1c1e038000c0380f40c081c1105a0a010710715501700e00c0401c5103403280c0044000c0d070b06420b03018002801e50640c0a03406804c00c0740e003036408410744c4945540c01d9540900f0a515400e800703014080c200c00c0310340e0101c0c02642202d4000030310404004c012078401c0c1c1089504d0321443c98040b807680d05100e424001d038a45403204031411803851030184005465442e5010b00981080800e8200c040c4010a640301c0c40d000d1604000d034252104142107004099500c0054030300d00090924000162522050044070500265407015008042c1000c060010b1014000c10200c1d40d8850342d100000c1c2c1d600c0e401c40303110409005c20000c80d01e504d02885031032a41c18001003200f408000c1c100400c030b400c65000c15603035041200748201590b5060b140c0340c83c11150240108140d07020b4400014080707052804a48003078640c00a03280ea2040f060030400c151114007070341c440c00001c1031301088081d048070307514024034903d00c805d810b00 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 188165746 1250 188164496 188164507
    0x301170f100b10030e030318190c08070f14090403050d0e15010e06011707021e0309041b0e31090203010e0109111915020a121b0b0606 59
    0x5031605006550611407640d4856120300582081c004401882440341018400f0b205502000c03550303817000070501000100b554103034000c4030b403040c00034500c022101c6070001230411282c01c5c111000c0c0c01a1051700d019216001000848255068640045075801d07036255206201c00d00600003603240c010030403810007000300500c51004030980301e0400c04000c488000c0248940f650110b240010042c1c0050403000c49640401c180c85c1c2e4844a003c40404903041207480c1c68440520991904480e04840c6000a140c14011825608000090452140f085030240300708005580c0203140303481541440c00008800410302e603094140f60208041041d1109000401c8150000c842e142d59446d1540e4510145e407504800c5003036103424050b0000d0754405500030003000d049030342c9059061481801103030003040c00b4805494900710310300d0600f0080c481444400c0840c8140400203440d2040c0c0c42d0210381c944003000300549503600c91903005a00843d08412f00324030540548070078100003001040c03d540070303004110 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 188166996 1250 188165746 188165773
    0x11041a060c0105070207091a0112020d1a09070906020a080a090b0c0318030f030901030e0703020907050a0f020703151e0c0c0b06030613020d0602070602030c0702091605030117 77
    0x14108101d41200014076400c008800a0810321264450300200c0c0c05e02c000d1141114410700442c0d13060500f4200301c400c2d480150b2144020740181140302110034078180f0460030712f0710041a41c1401d504106c80700409a13558050035529520140500c1005902040d070000004083e00c0040c04808018102064855542c00907441d4171f5100324004e1116400c085940300c8101c2c401c40c0d15071040318044016102c00100085035a82d01d0040780292030400d625805030017a0800f040c091200910340140a0720090303d00305202600c00c0c0c2c03200d082d100000302d0011501110600c041415019a036000314400b00c81c07818900c1c1b003405454508034102600320080304c16456806a44200342007440e00380c0311840058260300b03041c03280b00c0c0c0040800b03000e50441020810f80c150081655034100da4101c544031009843c41c10014000d02941000801c058400070a02520801d0721001c1e01c9994400c0710031000564444040d0f0b140010020380d80c50101d8002d01c014041e80002d101d10581e50110781c81213034004441400c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 188168246 1250 188166996 188167009
    0x70e01031106070327054b09040302030301051f05070201050901050d0c022a09040807030c05070b03010e0a20032a03100e0115050a0c081801120911041a 67
    0x2061104043c0310a041004241064036520380d0220407640300c0d1042c0300015481400d401e2801f403a102c1d0051903e13100c1c050381940c600c10202804009000c4806515061030065520391081c007500344264032140c003030500d0000307400c6548480401d035610503080081642c0191000e4114641450503c002802010001e60803481640300e050140e900030026007074203d09003d00100d0680b651840513080c0d05002945840f100c4220f40c000d030b4171181c941d56600d8503040c1140c540c201160014500c0c0262036002810480740b0002d9410395041822000c0c09484005001c8119048012800581d9005141c003815420228003e1540300c65500c083c1d039120b4116004e590800a80a0780031182240048148001d807000301211a000c1d000f10b003854481541840f030090041c0803010401d100f040800600808801d00c5056403911444d4442507441c0c85a82088205110002c2120010300060b484a655240d880031406a54145131700720a1140c0b00c1100d07941440044e1445295011580039822000f01440e02c401 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 188169496 1250 188168246 188168297
    0x30304050705040c0e091b1c0506040c03050603060f04080906070b0a06050406060207031b050a08010b0301050c041404020d090803070c030201050f0708150109030204180302070e010311060703 84
    0x3040a044801d0804003008111040c1203442010001190303080200e5817100c219840d0010004c1d4400c0c82d1940815211003003d00c248503a000c11b0960084810b0340110840c2c016134020340088034103006501d00b0341d80403012030f01c0c100e03426581980001e01060344155110b0a46421502030044c6514000e0782001149250707001010441d280303026003007040750725051407260724040c180c01c880c28003005183c07440080d074440150001034800f580a0140000c000402980c40e402000040c0680e00038a5460310660700034080500254003070350810b000510a007140b070b0201c030155007001e000d0141e490f44030303428400250041c160310502e4a82c1c5c0c0094402150924014500c81c000d15078400403606041d240007406d44002510141110484000340700303007a6040f00c44241c1c0103402c400d41600d4400d60f0702c0103d50300030050388046d4000789864070000c070440c40782e442d881000b4020b4080b1880700303542c0e40b40803000060034131025160210a103125001840d2101c000d1a140e8003c0c80c08140f0316060744041e94036403000 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 188170746 1250 188169496 188169503
    0x20a030507270203040f0b0a09061812021507050f120c070c080303040b04020f0f09040602250f06200408070e131101140705010207150b12070605070f05030304 70
    0x2a080580e02004a04840b0111103039981815400c50500da51040345c02c0070003841c01400d0000c0c090010307040000c0c0e03511205070290460b5080c040c1c03040c0c18461034045400483c0c20307180165500e41b080038882c000078034601d4592010b0344440040c1da401d20111016008060034500c0403104025000c07641744054440c501070090b964165683d00303410718144c00400126441600140c00a10410011480101e03034a540b1540649030240c031140d04200050000280101a0394804099010310041c009141c2c050502c58a8039540c00c84806d0701c1c0d004038001d2419139600101b01c0e02e1000010000642650040c0780001c0047d408220120a0740703085044030780041d0000303445544030303000c02c11080e030043d00d1160700300054a0040c513840c034854403218008410a14418140b04c8814015107046880754119110160890006c548501c00c81c0307810351602d500d44a0300010341e030400205242c149000c0c1c0e001242d14035000018802186400c00503121600200c03825203420220300c80380400310b8000d000451040b4131 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 188171996 1250 188170746 188170769
    0x32d0e151909050108040b15060423010305070207030f20060408030a020d05120a050601090b21070e0604030303180c09020c070b0306030a020f040b04020c0f06010b030c090d020a030507 81
    0x1098000c1581901c0d43c0414100226a030038800860080d000840d045015845414540d105010100d0202d00c2940e000d410a500284000751a075580c4540445540d08241c3c4c05022070b884410080b03030b942e090742c00003410030100410581e0001d0046007a41c55032050742c0d040c0f0000e00f08900300090b4960402e511160094100065110140e54180803071a440c884500b09203080009414600055440c001d1000d0442582c0788081103160303000740707448030080c0400c400565486841c100c205010541c611581406810f4010110341c0090090100210012000e80100e003041d1840d107089016015240d0b40540b172a11448042000caa25050306502500060102580d1074880090140c5051950f0780018020780c001e0042c04056500032032030304211a0129024140c038201c07040001c00502d50100441e503c00c1c030000d0740309480807000c5030350858031203d0000d07100d80d6a603030052070805103c110381840c0340034020040c040203880d024540b00c18260014044031081c0f41c495696502d0440c5030782000c4260070 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 188173246 1250 188171996 188172037
    0xc090405150f01032d020402070302070f17070b0301120803100e181b131505040609061a030403020a031d030d081b04030f0308041a01060903032d0e15 66
    0x15140203520050610445c4a0707050320021040d24280c2c10307070010001e105540002d4a030381814402c000240190500d56800d1041a541d51030f0304031420007070350030103045010f40c03d00000c4805100703060b00e0484106000c8054a034001da610f00c070055200818020319400300d04d801290b010165110355101c1c0c24448000305100012400c624070b4441c15030365000307281504440d050761945a00b0311040300702e000440045201010034050400420054100ca03420500d006030005060030150045030454044009100c0d2484200c50340c1c400344c0c070013158041c000d41e002034044030000344104120342d20b441200040460010441c0300117070818032101c034404009003224050040f0020715294060b01e4005202e50146803a103913503070780d480b0419030390320190605c6100000101270060f10880000c8241080c0d04960540d0307100e88001c0c2c13400303c0c40d020039000507902c07507440d14940a41c1b00d004008200283c403c03032441c41c03c0800845140e4002e100c00781c0c00502145545201214000103000400701c101904070510 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 188174496 1250 188173246 188173253
    0xb03010605160b010905070305180705090709090908090405010e100e04170307030b010e01050a021e010e0703030f0201060603140402040e0c061204021003060e1906050604080a060e0303090c090405150f0103 90
    0x1742c1000d85a08100078460022480405000078004210303001954dc0c14182c0c4d840c0c41d415514403080342d20000c5164104842001000181d20090244600403a0208826602d9000300d17915030008450340314502d10707107030350600044803645405a8032912800700075994161303080f40c122854000b6501034021a45580400f1015a040001e84858220a2800c1400d01c00000d0000355101d43c039821840c0d48403c582d110307959010b029001a032150324a68100d4540039a80d16006040345500c00003074006500c4d000000c03a004d403080c0640d80151400b01e140300c0080c5c031650200030051012040601642c070400b00484240d84819000e400605a2041071607468645030050000225525810b4000c2528040092040180c452050707a0008038096844100807942c0c0d1f0660010081c41d0405070303010340003150001d230000c40010300c04071684c4520b109011000030308802a40e60300045d00d07084401e03003101d02d0312416400c001c0035580c9d1041c01441118108040001c00c440c0345003041c1c9001040c0b000c040c0050060 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 188175746 1250 188174496 188174501
    0x180b060301060b0a17040203010e0307031112070c150c02041a040506060906030112050a0f0b01050112060503070501050a090e070816020a11090c070512031b040b03010605160b0109050703 82
    0x9005000c2180c0c41c2450400000b40400340c440b40c400c0e580002d105c00f040554409601680c20f51445504507a902d00301810050020707034151a26802d40c2c8154501030f481c120382c40702075480407a84042c00c2103059041c80080858000c03994a16000c00070100c100d1009a83d0398021b42c0d0f40c02c0f0a4240840762845000d0620041d140010b100ca07000c0c49041024041c0d644030301080b2811134003012805458184180b030300a06201e080325014103814006c1406405000c081405d20381229002d0700c0c0c0d0a80c10801034040c0f000e5802500c510742d403582003140c0400c85540114000c2000c0742c01d902e4070f2800c0796260300c8400c05000080d1440707400100104104814500301c00b1407001c5444140c0000c06500e0010780d10800c6a65141007240c0c06008400c001c9121500382c00d003611003a40c2e2103c103440414a4000440c80b55400488015034412a1003e101424400d0701045400b80c580021405103540e081038030075662079100003400d00034009907a02001c081101c140b410f90183c440f19001041d9401c01040c010207 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 188176996 1250 188175746 188175749
    0x20c22021306110c090f04021020010f0c0e0a0306020c0f0f010b04150b0304030e060c0f0d080105010512010519030f08031e190509190302030903160f0612180b06030106 74
    0xd8014501070081d01b80403100c2e80e45d0700c5a07041300d1074914440b1101d801c54400f60340080000c041d03c00481d800c00301c0031064002106540480300208a07446401000305c0e038a04541c0503075908103075903200a0021900c15001002c11014400c111601c0c01001d107a15450714403054030341461a55a8404482189403c1c0588080c0d4030320f044040c14510306080101540d8400a48018144a01120001c80c80d440b150181c0c0d04990ba602d003650004c07040880d18540715503000d00700310000b03444000007041d1036010f0741c02c2d0f8034628140c0f1002e4266a09000921052041d0840d1742500c074001c000380000042ca05095052401d8400d143c1c49480303007410f088100754200da98100d4047c00d1000c400708100d105040d10300f002101090000400d06803a400059400c1410341c600b0824410300003680311040c1a00040204031805058003100c9018191060703041d0940540d0013403e1142d5200d81041241d01d1050101d00f2500226100004034414481156410043d11401c01ca8a0050340410040249000e00c01c000 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 188178246 1250 188176996 188176999
    0x1305040c0b040b0a0e040b1201020a022104030b1503070b1c0240060507140105060901152a1e0519050a050105091c020c22021306110c 59
    0x2c0c00c080c101410f40c0e10300c2c0a184404010480b0300b41400220343e855400190f20640c02410518101007822a054040c0d840071070034002511450360319540c883c4101401544807074a49100c18101800c44d0360307800f1900d001a0406c110109102d034109445c0d502070150070b0041000065182c0d0780d04022400c0b40340a08250b01d54000d49206103d88031406403407100111001080007012050351000001e0b10151030301002102122103100007010a106402c50014000a40140c001003604600c0204c15400e03a08219807164000101c1801004007514104c03103580c45070007030305040410452a121181f21179080c0c40c3d17080243e900800701c140c01d0028011080c6285020458401104a101d8035195074402c00550903088084400311b40c0014000140f10741c12409a0100c02444070307081004546640d09036825019502188030352800c0b10150000074a41c0009001410100711420010242c45100b5291102c1c0c6c80300503000c10920a60380342100114000d88a60748030b8510381d40711004c40324540000340300307a036 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 188179496 1250 188178246 188178269
    0x1002061803040e180307060c03021e07080403061d0a050a020a0902070c060e0a0515070204050f040f0b1e0f0901051b040504020f040b03010308121e07080601020c1305040c 75
    0x24007683c0001a401035002100580c0e8000c000c0c4074040641c0b5610440602a00e03103807409a000170103941c1600100740c0302c204030401060496031030a03161858458404010035040c4200010000240b064006240511590080c8941407940a05c0d0034101848814126119003050180400314a0083c4085001c1c1050110440c1400c1032035031084d68803030f83c9009450034004011460515540c503540c03240050100030303020011085402801c07150700d17000884c00324850350030000061104441d1484c481c1c45150803580744124200c058544009030000a40500c0046e0292040c01d82c6d07400c0c000400b0786c01100103070303501c4509281450310282142d00c0504010b0203110302d0f8429400d5520003000350b0303003900d01c01c44006031745d1108201c40b80b00030300c91640328030b0b06803034080000411700210201a100b0031b0307140c48040069990b044034100c20780c15140780d40d155000c4a440800c0183d40314488040e1301590600450705202064000184081840c0458003000d50301d07441080100110032030400020f15005854 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 188180746 1250 188179496 188179499
    0x28090f1109130e0c0402040f261b040908030c030703050c090a0501080c070506070507030f0f0903060e0c060309010c09090504030c0b1b03040305070b1b0412020f100206180304 77
    0x441010600302c02e100300c01c2e00d0780341d100c2100906000c680c00025004000b107565076a05c030403154180249100d640a1001d08807404150440d44074119140c03c9403440c054803409040010942c5d09a0540f42580e400c1561503030202c00142000004600484c0d0103e2450744910742100024140c41d4000c100700d1401c003081c48404065181c81c651481918000d0134141c09584e50a10503922034090001e010304144500810b00003180c1d017000050840324040c2c3d0f510000e0301518032040c2c0713104000f64060000150501420004901c1c00d900c131302e040f00c0c000300c20f45e00c654602c20b00180650300103803032034804d40c0d54800c0048200b03500711101500030882c20909010614050700e01070302c000c80c3d40101400c190900c100141c420519510029080c5590300b0107103880b404c0c00d06004040d074201c40d0003210780c1040c2c82f000c0f07503040034081000c2c0a2945844ad880e4600760506002e02460a18194220f8006114283c4010180d4a280c01d0320690116035006100c20701e4508109008044408404c00064004000 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 188181996 1250 188180746 188180749
    0x9010b04150b1c0618050f060d020915040e0102031513020c06180c030105040501150905060a06180e01080a0b0708060d060c11030d02090a050d031416140d030b0406080c28090f1109 79
    0x70a07444840c10104d1080b407211507001c6370207040185a4203241f94400010011762a0b82c4e001c83d0440e14000340e4010480b12010210f94080b88100038000040d980840300082c002c000301c2d039030308002506102c00e4070000380c1c4d40300200f8251201902c08031001e94540003000034101c0800c0404c0010000e02c1000d0119042000104004485500440c802c20450200020b0340c41c0c0342d44116802410900b026034112740e50344a1068403012030410481b8258440d9011400503445900e2081c01010001d00601d400309480d0340e080020002592007200f806405480d030300205c030382440a00f0348007080c86000f503660f0600e00c040103200600ba070003080c450008282040c01280e80041e003075a0495011110075a21000c0c0c60810711a40b1401d00d004020141c100c1c51141e150342c02180035400282203031804d100504107042000217854050040d000568009004e043c2c45180005c90317801c015203c10315030016510310b0781d4210004613a9400590501e601d03140311080651407846108118039680c2d0076107080010340e00 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 188183246 1250 188181996 188182009
    0x31501051f09140109081204050f0604081f0e100b1503070c031b0c0303030c030c0906020a0f080c01050108030a080702010902090118060e09010b04150b1c0618050f060d02 75
    0x41c80e440c1440981000c0b8413a4060313070804000c0c24010080751070001c00d004402d40564450302555004d03140013201e41d24079042040c02c0d80d0039600f06001500003060340401480c5406540700a9068071b40d15510f600e105600d0522140082858000f000308950080c9001c2c0a02d078141141d0808213200b00b0401c01042652015541b031000b41d145c0703070180d06442d01b540c400c28000641ca1380640081c1419800100b09509a440b00061a405460500410840f0380094030f810441d846400c001d80c101c1c00006000408182901024501c948051030504040107000e40c00c4600c00d0b00038a02c0d41e8000070300d42d118150007007045a40001244002d1000e52000d60104294090600ca458031010b0075050719890701c0c1143e003041c3c0103000b004164202c58a090104c182c0030b0300020b0f07a6680113500d0031441a000c2c49003180844191105441070700c0c40c213072030060980d580e81c1c0c3e445011a80079503603100c08500c0c04096141041d0740308141c3c0c4e0104444c208070303000c42031081018290038803c1c52480c400400586600307 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 188184496 1250 188183246 188183249
    0x170702030a050309010908040906090e0d020c040b030f01060b040807150914040f05040c05100306032a080607020d0305070e0a171615030501060c030206010e15031501051f09 76
    0x514102e526502c5080301140500840440103100c990042000f041055459200c007040700e050200c00c2c000baa2113812480c3d00c0d004c0c0760f400c440050300044944025401c294120f5800703004090201d0b0410403404103002d0031500c003504488a95803002900300082c1d4000c128410151410200f08030700d8054a0380d000e000d035601882108c052040d02d07000a20035948a80c000314404200e004d0520031032400385850344c3d0031b90b0130b801220301c0780e42601031b4420114801e04c00d110580c1e07800400020720907001e8050000300034170350303101c0340300d403000080042142e6600744a054001c1405030000c2070407040c400c0019007656801000c10301000110100e600769661103000c40011982428107403d80708056402803801d01005810006030412910400141c400f60080d0b0ba040c24070440ea4108082c0c3d883d20f204403855500500003a0059206800600c500347c842c640e4a40c0000c50b080c00140c8130036914000c2424407000e224245155080e2400420041c1000010705080304004250410619560640540300d103026 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 188185746 1250 188184496 188184517
    0xe0303040e01030b1e0709030210030903140d110d15090b06190302130612050106091a092e030b0a08071a04030503070c031101030506150c010b060a020a0317070203 72
    0x810080341445d44040d0042040c10714081c005c1640d840c0c801c0300071301079180390b2008900900c403171041c4c80341003032007803160014603035044d0350304259090800010101c98100300f100000483c0e85100464404007103000410701c807541c106011920200d030458449030b611080d07010003e101c0c10032078049216595079048984402028529211554104104400034010406002c24040c400f29012a883d0b03005004000c4088200600307000030ba0721410201c0385c3c590079115010112500440f05080751001c480a40381c40c0b1b08c060702c5c0103ca995240080e285105040a272090703140c008482030300103180d150264010540080d240414042d14111105030b40d810702d481500303810141c3c404030080d1818200121002035420008598460645c2e0030585038208862008984c2d40d2401c1c1c0700849154001d0050600c02d40004103070300903034031421f0003803a055400441602090f550759020443c00390b0b0760078081c003106d544a0b4020141c074803407860050555507024038504032001c1c0c80000c01500f55400411902031141 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 188186996 1250 188185746 188185763
    0x513080703030905070503070f17030a05190e13050901050f0103020f0d061103040b24061206031f020a020c031b010309031e02060708130228030f05010209010e0303040e0103 76
    0x482d0309080e405c1541c0e80d0085545809411070018034580742007015010b1344c0407140c0c0304070502c51644a4980c0c3e44103688044000c248140f005050600e06008441180300c0f042c2042860b0550190015502411000c0d9003201d0303d50b0b0740c00b8020044c03404d10910b5440041c01e4840340340d03541075400080c203980880e41070034482c0c00d41c41c5082c2c0030040300743c010b0f809a000f01c00907140c50b4100741c03800d40380d81e02c801c0300c0c9501c2401608218500070390806d642d94001540c084c141a140610f841604003085000078011034040c0b080c1040c24031182c01801031014600504840182c95816842c4004e091441c80010303241319500412101c41500741c4100c0815003000309080000301c80086103010303508502c6504e541c51003190380c0f00c243c0c0e19080e00840c0c03035440b4940ca6501c04055660302002d6000c904003024001c5d401c040080134842c0f2030703640100015000611200c0c09400e595a0381c1c2c4074030300b54080f003400701c030240d40108880e0301e1560050f45410400300110701944c18a4100440d11007500706c14880940b0805 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 188188246 1250 188186996 188187011
    0x20a031d150309010f1d16150302181306151701090f0905150109060609061d01020c10090e010914070c030516030c030906030213060e060405030d0c06051308070303 72
    0x54096014220303406011009005a400700103940655403002201360666000ea4040d00c44c641d20b2004500c010340700c510a1030307405500482380440080d0090001002c02c070034820181102c0340e803030b019401c1d000750884902081541c10b00014070800c94049401c0c0081c000f800c1d4401026404404100c2d0544034144000075034012755040c408050000c07042c000d407040c090390954524210210386024183c500440003448510b59849c0110b1381c2e425148035020010f14250a540340c0c860001c40c524610a0052044801348481800050107000303414114002244001508000c0c441c0032842d010b004152011003004088244901d02c3d4994100070721190401c400b209a100825006009071061020f00c00390704042c180c404c0c9405024003e1080083c1c3c0032854421001820034031a008031010b200d85005803a5802e0701d4540180d8400700032044c050750041d420310001c24213407005c0000a0020b1a15034516030194031608180044031030141c101e031245100030700040c011a0f4150201da01c81540340c0350010307400c13 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 188189496 1250 188188246 188188261
    0x304060c050f1b0c1809010e030405090604050603160602010603110409030c020105030903071b090f05091e03070b27030f0909060103090b090f1009050601030b0403050f0a020a031d1503 81
    0xc80380121598004d5910360382c600507075280c0a6943c861b481250081203141c650200c0555a40034074401d03e5480b00c2100300007840303400c00742c00c1103401c03c1d005811250610706846c0b035544c5281d040d40007100142e6503034400304140540c0e032001200c02441560104070391040e544000741001390104020b414080b0000108846000401c102c407112604962030100da2461201918007480c0d85108450440d41030181521802d19140300d198001c9924000800c0100d161083d1108422a900814900e501060042d0000b249004145901c580e81d13141492170006c0c80e901c4036980840c180c5500764043c7e407040c0207124128603c1000c58044210803142500b0170345e28027004070017400084000422001949007480590303a80002c410b4043c400b1181a20792080e8a071042e80100c070358a80019001d0b074820341c01000810307452440b10b80c200c0e01a01d045440c1c04040c1e003c2d00b42541c070660346030006034040700a8070309061740318003c00059a899054903013444000000989004080c441c14010500008041040c0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 188190746 1250 188189496 188189503
    0x20706080603030d1508060a0f0e01140423011109120703030f0e0f120604050c19030803070e06040305060403140307051c15030309031a0405031e130305030304060c050f1b 75
    0x1048500700f107c0c1c040c038050700801d025007580064015150b0a100142d100b48106004d024074840c0d640c81b010718a60340e03035116210010035a0300040041d11449240710801402030140105610406180e0303646c62441c1002d1200021068482c1c010a410113041400002d600a800c038114000ca031030494065000f24001910502440700704590040d002908038400780c0c40400e840d8445c0c0c0c010742c281c8114100d00e0f030a00061000d13104001414541d1300d0310510004d840403010715001a080d1410001412180e00400d2040d4810b40040c0c1c2c2c140d0001c0100010540c1c00394520880200d0b40300b4840c21428030103000742043c00303600040200350469158411400d103159000b4000c6c446a01c60810300c0c543e40781030142c0120414041600d2800304101908010002c0c5d6032014020356011000318030f800c2da462401e10b42c8400301c07080149120740800500141c0c0000068030009107004001442d5a4102883c1c844222804d40100000348030f01401070314589960001950084001e00e032107220100d10003801c4506 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 188191996 1250 188190746 188190749
    0x111191b292401090602030a0c15110d060603021809090c03160509060402070302060106050a09030219150903021f0210110a02210d0b031615020706080603030d15 71
    0x8050000070030000b50104030124515800550400b030078403807050100441c0c61400c14000d0b0005648200810291144220398240302a4011000d0340c4010104411355002d6813504103c40550a90208150002e501507100b00001000c043c2011464018103001c4810302c4514692031511074010076002078002e01d41031103812841175009007540e682040c01c640915050500d8003d0602810018001400c2d41c200f91085138500f68241d00144101da10b012401c5506901c80d0003118204510744000100607183c0061104450314124030340090141041c00c4c5000201d040032034130040200300358081004d070310380e0400014203828842c10390a03106c030f0b01802645000a22020110460f2030045403c042c0004d584c0030b80800c04041d400d0341e5150403401d580c04100c2c02c9414081d01480d104100c0101d00111503804490480700140c10b42c4c920100426041d0321010b80c4d5444030262411002c911a101030b814007541c0e01070226410300c203d041c1800c0d000310f50382e4040d0300c04505800e80d49030303608141e144102c59040c0 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 188193246 1250 188191996 188192063
    0x219020607051c11010b01021f051009020f0d0c1d0909030705060112021207180f090602031005040506040c050403110102031303050f210901120e0111191b 68
    0x80e1640080024550f0000300e031300145a500e44072051400d58404102e01c420b1800a00650741e800d44505400e0380200409070050f0280101203600040700d01190020740307410607840e04003a4840145c89421000d031403d007500501080299020522981d00070110051413a034292400103041c0d451620142c074511400074080c03c41e00c908000000d1a40501200040040c8262800414000a5a50540e070fa0445008244040c064182880300a10056211040c4003010200c089031560036912140200d0344251282c01c1c584000381002d000c01e007054082c65401c048195402c114022170311130020310b1405940001002d113040ca1001d00b010b030703100300309070f507000420454055038069891501c10fa554180c118583c1ca0f034080c101c03004440c1e180130f021b414500001281660b2410041e8001140d01210340e000400040703903210300d80f00d8241802d101e0080300c121281145a07494810042e02c4c40e41e005420440d2040001024115090400598144884583c080c502d09103045040c0304420b80060220742c01c2 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 188194496 1250 188193246 188193283
    0x30312060121020d32040f0b0a140106020c2b1a15060301050a1205010617010b0a050d260906030f07031a090c0a181d07021902060705 59
    0x100842035107a802019400c03000380c010061100c0b02845c2a03000e44c42e1503a030000c040021031440550f1000980e4043d4094414850074031030018540d2107014000c3c00366040d0400d180c1e554000e10060725070588081c0507161034001004024010707400580c0440b024507100725002c04010b0010229800b00511150103070303214505008490030020a1886940215141d030b0000c10244102c454074200282200e060b190003134072840815062200d403401041d425001121990350b07556001851210759107030551829040c2002046114000c420040b110000c0c1d08807512803044540e00c100041c04400f0002c0619903c041c6523000d01d694840c8410352030045030041c175041140041046481201944100d110b43c00302d4408200b035031500c6184610448901c09a41c4c0c20210701404500300c0c600c100d0103000c0d103a20301d00c2c202414a00d6001048000c41c502c2c2d01c0500100030120208009901c81c1c1440342d1301444070f10007082000c103843d44000c1c1c4030030300d054080d000c1c0c2c0001644405101d000d002c64803041402078a503 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 188195746 1250 188194496 188194547
    0x100b030c1309181b05090105040b011206030b01050315090c0108090a060203040b040212030a02061506070c0e101d0114010509030303100305070501023403050d05030a0501140303120601 81
    0x5902c10210903101100c0805000e031513a07040380f03000414030080e03030400381c00d01e502c41e801c0c01d0600004000d14034031581449441c403076200441e0034601500f0080e6102c0e000c00c420a524040a1501e0210b000480ea24601202410401c00303010008003140d9200091134100204d40307035801c4940c18007040c0c10740030f410b05000000300300c18002850585805640b00b50f520140407211881455120701035000d4800060300000040f030b1000d81c0e400c0700769840c200001d141c185450791590f240e0104085550241188900907400c01620005510002008003000602c50301c100683e03028500c101001405000440481c403020b0361a964450b00644161000140c22a903032410444104010b4060030303c411100c2d44641e0030b012505510101711307203ca040c1c007101805032070408070b00e81e084800c1c0c6203041010b5072102c0103000008104100102c240e8130380fa81d21000d56038240a0f0107441660300c16008401c0400c40525001156240002265002c92040b070480301c0c10340790400100c90b45548800744950609030402e0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 188196996 1250 188195746 188195771
    0x903080a091404020a020c09060f030a050106090e030a0f050c030d0626010c0c02120f01091a0106020601050105030f10080709020405240417010608031908100b030c1309 74
    0x2100c0c070541d0340c00e81100c400340381c0c6101044142d01c1030500c0880140c104000c50700759820541c480c503400020003400c2c00540d9260302c010a1404c40e42c074100b519669103503401000405114407504006112540c040c51500c1030804028002c07024846d40e59003040400210168140010700560702911400c090034002e440e81c40390054000c1040031014419080403000001e5400f205100d0030f4842d810946554240c00d000e034080124a903490154035400c0d01500080c1c0503070640078810026041d100c0e2400c0c18003ca800300c03e102034860305801c0034003075500c03880040c0001e03a000800e680d84400c0f140c08000c40703642c3c0c140126040b4040d643c0b2101192044140119019603a500900186d40c402e551200040001d042100d00003201c4846901803044100414040710140400480004002500208a40d03589a400a182d680b0440c1d01650b1003000d00000e050460340028a44d82180518198084050a025032685603100c0644804030040002448800d00d5091000920041c840380404002210704c0c2c10 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 188198246 1250 188196996 188197007
    0xa2a170a0506030d020604110d020409020316030c090b03071703070b04110102100213060c03020307080a030605040501090504050d120b12060702070f081203060607060203190b10120506010903080a 86
    0x1106140f0900a4181142d2000e00c0040c40c503120340e81006403070f840d5500d20428416150140007041c0c0e00940c44815090158508004001e000c02040056480c001c0c60b60900715201500307500045241030505c07032080d07483c0d0740014000040d500384102000200c41c428104500d584200c1c480100607104c003808001c103206000c9241c010848003a001e50701c49190310300e071080403845404060b0507000c40c48542400024403800b9035a003d58420b0040700d240c012951560909a00590864000691140800d102c43d0505010340c9005040d418400d000c58146560307002e444d0707064500000c041040588410ba01c901043d0080c02204078003614050072007408210b007907128070007140e00b01c2c0544105034000620348008041c52044a880d03c02400004404009a004541c409030500350310410910040700820010710080d409000b2540025204144880d290010380350000701d1103200d02e0840b04503800e0a07400c42c0e0401c1d15810f406400080c01c2d44c50b1001a2624002d940000d060b9100100b244000d254104 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 188199496 1250 188198246 188198251
    0x30204150e0301181a040c0e1602010606090819080412030c02040b03060105010203040b0703020304091802010e01080714130306090503130803030106090603020d090501021c050a2a170a05 82
    0x5600038001d0b90944901d9042018134040c0003000d4540081010005002c1d056140f60040d200700010301e0350035074500c3c80c881900c0060710008a0300800400d0240c549409110752001410241060f2040310328004401d0380310034074800b030142c068500c08004000c00c00700200302c1d00035001c04160f04000d1061070030020002c0d4659042240500d01d84040d190242c43d00142d81030403520140d00940c0303002d0070130030302d1002074010140403010340c44144400f10b00e222490048100340a405003004110804a000041c000700308905558180101403040c0801107030701006807000e0044031540c260303541003100c291200ea0781c013903400a81103e240a00c00300030084080300070459008840601c5000035210001d8589070f02c02031080300085851460208000f134007070b40280c203a0710030050000510043d16101c0c0303402e991240000b6a9040714480e10320401009612036550065103009042020000c00040320020309044507005807032480882d5100d8000e4801c03000d00068070410045840789040c1544850040c081c107 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 188200746 1250 188199496 188199499
    0xf150306050f101809050d08071824050c0d110d0e01170a0914161a04031b1701050709150e15070b0925030b04020907030204150e 57
    0x51101103144440d50502e00b90194a5140c681100300e458000b4400d070020b50340c80084002512060340b070380401d0040c030105408088075182c5000354600b001009001072100c04103000300b560341c04e8080c480d640c84034402c00e410145a00e18412100101141982e060007549030000d0a8440e0031060000c640d0b014002d1304800d2907001c202e03107102d1a07002040d1041c0742e108c000280040d0156503e02e030b184080ba8030054006076074810001c5c00d00722980b503c0c00c949400c00765050302d9500804030070036200102851a001020744840d110788280307104c6040f91043c40345100c007070040d42040520702d43d0180e00e0921140102201e0710903801000400100740c0c044c3c80112a154040340c0702041c0011007120024800e0040ca01c0341d030700d401030003640c0d0017008a040c01d09068510403002c103005450010740e010911a000341c2e26940105052842c25111300d0100071a000d080c203074007049010401c0007443d001031403500141e044802d0b002d00da4a0620440c000d0107958401000070151050103508650403050003000c0810 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 188201996 1250 188200746 188200751
    0x42001050d112109030702040f060b0d0c08070e0a030f03180609300b040525030605011a030403110313090902130b061206130204081b01180e0402040f150306 69
    0x520080b01d003160486044ca403035001004400010f00d466405041d0358400d1640020b0785589903400714280742c004295032a5155980d187c5a05003030341103041c01d5846441d51400c2c1c010142a5004100d40205600c001000071405c80202410180a0b0545c0c0c02c00441d0010341c0008580d540d01e000707003e00014401d40141c007110401c0003d109207507100d03054a51801c2c29100c11102e01c00e90707960921680080c400e40380c5001c0ca4060714581c41803260115040c0c44418428459182142440d9081b02c030180d201501c1c202841c000108000c1500d03007078950181e058180a041c084629151609602c6407440b051500b070544100030440d2001c03984191403840c025601110000d80e1141c1c16802c0303440020480d1f901c0f01051105150030a004101e04da0b000385e02410b4110740369040001ca01c00c1e42c025030065207094000519400040c0b51110156680c0642481e003090000a019691616006030303000c1c641c0803501c1071f1b001509640302c03500b0000d90921184010451904071201030850110715010444403030b0b0 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 188203246 1250 188201996 188202037
    0x504050c0d1121060d081b1f0e030703020607051809070507060c08150418021201020301031403071203180b0405060106021b0609090709030501061202011403042001050d11 75
    0x11141c00140c4070b02d0015000c29498040b1b42c5880d0300315000f0400b5648080340800c800002d0400500243c2a0111080814180c524940c2c4116081e2040e0010210031544180400c02c04030380e0008426030040141c2c02c001c0e5992603868607425072491559000790700b029216040c040b40c0ca030300c80001d02c0018000c0703408110442e8245e004640b00039003030303991500581030303039554280920f0a50b0040c5010f503034001c2c4090040c07141d6404034440450001c2510400d944c04030041040c4440c60380e0f8520014417071000f8624000386a0344248101210503015802c2507960880320300c0c158003030301401d0102c0303030007442c1903130580780510307020b0707a50715090190800500501100c1150b1402449509c81126001400c05003440c5804007031184060008105100700a2440000004101c0c2071003810041c00007030401c0038007005a4000940602144250740110780020000c00c800f1620780d5014070504d07606d0800c1f104c0b02442c2400121094000c0018828030140f4002054040c4000c2400030040c03040b50030345440003203 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 188204496 1250 188203246 188203297
    0xf060c060515220b030a050d03150e0a0b0a0b162105070b10030f0b0105100809060a0b041d0c0306060111030f1608040803121006090504050c0d11 64
    0xc80010981d0800a06120454007030880c10320110960700e040310018800c4e4103100028508001c0c4070003a41c464010400d007900050345030007440c00e012290082a00f03803501d0504500503039030000b0141c0c01010b2342d0380c039501b803966283d00c1090000d114201105448034241c0c03040c540f4080c03c4400442e50a0b9444203242c0c02044201544086400d0740c0e15090f00b801c0d566210314811502c001c100b200078515902d0003000150700002c07170404450050080390010360501040c0207070110402640b9082c492a4401c1002e80d00001410f50782c01b1a4804011901c14010030110b03002e80403541145814010b581210140c203e070004044440100c00c4003160050b44402005560790001c190307640034550002c004806200a215005003030121144e1800c01e400c42e41d039110341010703420075001040590030010f002c103940611a0442070f04a51a0759400007a00d141400c098401c058a12030240150f44aa0010780b40701c48210a0b110a0021a9401e0110501d10000d00d00260701030a2101e90198002c3d070400c080 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 188205746 1250 188204496 188204521
    0x50307080c010c0609020910060e0301021306110c15090a0b18090417040605124b040303050f070302180d0203030c070923090a03050f040f060c0605 65
    0x464a1000140024034800740044071000c041070780640d1056143d184050041e180d03003d50501c240c40c04a9080359240c02d0a0f002032003144070a2050b4841d070300601c04000040e000c44448000c803060342c00e01e181c03000e4011903081d040078041140e140e03211030200420703410290000000c0500c2801141c5107940780e516608418010b0240615081c901403a11030a1449800c204816a801c00c1c02054901e08840c11501e00101c82d0780140c11070f10000d140030070340c84000001c446042d604458190b07400006000c4100611042c004034125031180d801c544041140c42c144007ca0000d00e054620b80c40742840d1606041c05005400d0945600c001181540001142a4882d109072041c0c040902c6401d207051449000700b240d45080540c1c240e1741070004002c0c442c3c45030020000700e002004601c0780810f56104000803405251074409101c41c0c80302c0b04804001c440e510100d2041c0e00d5907410306009031201400701c1c00c8101c40c0038030703004403810b02c44400000c15283d030400407544400344070720b80a000c0d50791041c940e03020 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 188206996 1250 188205746 188205749
    0x30804080c0a0b1608040e0411041103040b0c030709091a09010b030108070605180d060b0a06020d050f0a170a02030a062709062903070807080316020d0602030a1401050307 75
    0x84400c42030213082e91806414001240c0c081c043c14007241070507141c003c031a10f01401500e0460710425079640a44044c20140255023814001e829014190703d465114850f0b010402409102c00d03c8001000032652401000ba0401410407808208400c441c0e2600d070007459802e50940500c19801c0c1c4000141d8245201c08582c1624001c0000d484000d1404009443e203401651010b80c19040c42d032001c0e00c945c0c841940072070005004040218240c800a002d1165011194200f54110b40060f0b407811b441d07941200440c1c00318102c0030b040302d07650b10002004681c1c0078090840715400d007070004113001a420f807503005140184000c0104002e00c641c6c8150302d03d84583c440c61280820340000c0404542c0725078540c80101501d00804c00030411740380c14415018402c0c0200d541e1010b011403952824007034202004658041d203040741c020700b0800e086c41c909543c0ca010f8080d0030802110040703511011501c450400c0b00350036900480c10354407801d0a41c42207018090a4134441013004944000003080d180014a090 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 188208246 1250 188206996 188207009
    0xb030a060807050307090911060309031b0f0a030c140f070602190309090519022d0406141b0106170d03061a0705150a0207030906020c0109060302031906030804080c0a 73
    0xc501490021401e002c7d2101d034000b910f84159045903000306849480045109100340c1c00a91741c0c90b142c1d03200000c0c0030760034100c0d080c8240d44803280f02100c106000601d03024050301810800c1c6503804903e0700c07809013a04803060b03008034059619010407585001545006a5110ba02500c0c01c03141181151503d84151300c4010300014000c01003001400001ea005941144800c03800540141907040d00c5004d84e03000700c400500e010801c211103e0f0b40c10601e62642c1800c2c011028ac20326080c42c04100500d84407000c001c0e05070004c80000c58101d0003005400c101800074406000f801015aa2610350040c02018460044a805801442580c02e1310030703c01c02042e29039215492413a1064034450302d009402035042111140703c0c01c41210408810b0b10200c520901422802503a00d03031042c64003d105000c0da500040a42d8402d49507010f20360780101d07400c801d58040d494016103942d42c644150400c4000700351200c0245107070400c04800e104c1214014000e0342d40f00e07000c45002102a4041c40940e142910030391 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 188209496 1250 188208246 188208253
    0xf0705030307111939050a06030513060b01110f01050412021f0b03150a05010303090b0f030705030c09040c0e0312090a0315060305060708090616080a0f0e03040b030a0608070503 78
    0x158009690060481c4c414504a145030903510400885c035850301480d56512062189491800c01c014540001850042c02c5140340500082c100003803444a042842000145040d80721081c0c00000e03407062000d10141c1d202c90702141c1844034560481c0d070003094103a900340d42c80040d900ca09400f05000084016085105101c2070301d5401402c04070000506c0340c500740c16410701551040410483d01d100743d05000f8050035900140651440c500944500507992000740e4400d0b040c040d00c0d119035804401d8a03070011240c10815541c1c0c0d074612001203039105001d00e1a40c814681484011065881785000c6158482641203404020550a620110340a10001075602036076400301800042d12035a16105031100601d80400e4603900c0360384080c2085011038001c000110102c0400c800d10f07d040148079009184841d00c030040f03102c3c44a00a14941c0b004100d1040d803078540f000d44c00d0302e00da42d900041d501440c4505aa445645902103401c1650054518454070750a14101041210012580b1001c65030000c009 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 188210746 1250 188209496 188209543
    0xa0f030506060c0d0509131104030b10030623071d010e1807081e010f0b1c0509030a08010504050f0112110a09060305010c1818020f070503030711 64
    0x114080c050040c00705422040510030503058007000c200585410304181c6503a500d80e121a410303c2900c3c04581e80024909003004141c0d94881800d404403016290822125051a6070303041d188080d080302644024252407600303105014002c0c4500000c03500507150300050506440741d440480c2d00550221100c1030402e400380d60021a503001d00b0758841410b0001d880903101e1050418804c621500c00c942e03400c04901031100b0029407061310800012405410080444154102403541995500c54042e240f42240d00062401241013108038500500101c11010b1240e4a01b42628544a80000074040b020072001d00000c1050300d0140225449200c420b80b640c41c0d140c1c82d0840d020300d185207010050f150044440ca6075081521103055540c00b41c004140040b07465480c40c601582140c51002c424010001045c09918403112500b1010084601c100e951140d00701c411070b000c0000740309920f01284007550014059040100200186201c1c41541e1a414800c044a50320541c4919a011031109040c9036600b4 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 188211996 1250 188210746 188210777
    0x61a090121060203070c0209012705091e0c0a050904110625030e09150915030c0a030c03050f0303130308180a0620040b090d0503210406050105060a 65
    0x10080308040103100c01081d403141038441c10100e078002c0c1c9003200010040700a041c1503083c030240c03050040a12009244003900000800d102841441c41032024203030319a000304411a004000701554a0b0401101c140c0000003484403a540349103e03801580500f14000001035140340c590322480c07203950005001d22085003200308108042c0d202400c0344e01d41c00540707030038001d04030f040c40500503016110352202d81e50117500c4002c01c0403040004000d60203d03900c2020855154a8102906410a03200351075002e4066140000a040c15050301c5e14a821581d1a07400006200300d2005600c1202e0080050724207480c4000700307140e00c1e440120340c0e4011002c105132005000a00c146049a4003002603080c1c024001401041c1d103042c80c00c500300540c2c159499900c03a41444200c0b402e0f80782c4201c10311044524180c50880300c900e8074010020158400c000d010303000c4081c48020300c02c8808140d900c0705802a081059501007c0c20300b400c4d01c06503070f50b0746488008500303410324008407001d100803a15442e01b9a030034000d = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 188213246 1250 188211996 188212019
    0x2030303061302071b051c034505240301030f0213050a09060f150303140f03100617040b0408030402010e030d03061403120a1d060403060603061a0901 66
    0x42c039915031035403c002c64008180c10404040542c1403d00210505074034020402a00d480c10612130484802100c12410002c2d41040b150b100b00029204820482804d090040b088603c04240300c0004080f01c1d14103000078141042c56000741c0350121100c20345d12801c191003102140c0b200146041d2401c1c20001440480e52040c0c070901c05500c010071014a0003001101d95051342c1003907850026040c2c40328044806c0120f140235101000002d5401000085800c10301c40c4070328406440050300340200124080700c5842c480044452002d0404403466481c2404814444060400d21070f1074000f0340c4400750a0184501041d60500864001074041c070240c0f10ba032100341301540090030490500010046a91303950b1010702c21000707010341d01e440c001074140c0740c400d440440906a00143c0c1c4641c0000c2c94195500c44070100303481c103103015442d000f4103685401c11805902032844200c2907024401240020400010780c1001c001d8a110302400c1c0005074030f0041440c0440c6600390300343e5019840b64014000c42c031121 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 188214496 1250 188213246 188213269
    0x606070602070f06020a110a0201050417100905030309060a05271009031d0604030b0a02090a08030403120f0203090a0522050f04020a080307050c1e1f020f0a0203030306 74
    0x10000185040362550b00c00c030308408006011a8400e402041b1985581e402c2916031340100020f81c090000081c456000920314880c83c081e022600c41407481030a4802c004000302d06003210841801c0112150310300740300e5507980003240d00311064802c2000140d14600c5034040c00703000307045007610083d00f50080302d0398450850f000420031040348202c4040260300010b60054a54440c02503c820396000c60b11444da402000d44401e0050003074404000800026907820303011030340103481143c01038441c0401000607548200540c4228a50310010074080705000180d00600c0800005803103c041e05211108183d80f00e01030381c505998000c0003200b040080d810100c81c2da10352220b19128100d46051408148011104241d40f00c0c00480c19060411007142001d40003500548272080c001c0d41003d855540d801e070b840300000000b6000b0f83d11202c40c4a550150b00d04020000500100324214815041c160768905071145403003100144146003900c000c1c0d01c80402c110945075006405940f031581d480f018000e074402403 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 188215746 1250 188214496 188214503
    0xf10170a051e07120822030606050609030c0402070611040e09061003050a1b12080d141b0f0f0307030b01081005010c081b030c07090609050f0106031a031903120c08060607 75
    0x2c11103c3e808010100d00306d03d4080d9120800501d060646c1005021035505130040c03800b0303000c1042032410307e41d40000c03e00d0308c07007800715000b590340c41032441c0c803001502d00580300180d51a00440c001c40c40c07801800e41c26100d21403120444906588075040d12049505911014207a9041880084081072085101114541c00d501e1122203240d907540701e00c254031518010958031003402180c194007841c00303400762a04030203544041c4000d07410601c060314020b030400e0b01500d448030300000c0d10525042c0c1810070b54582c0381d0742206035078607494584070144c090700700c4418580c001058280041c0498054403212000e4441c103035580c03101d0035038a41e01c607443e95028081c02c44001e1115502e2803640e40d0200300802040d15040003500d0440d10b004442e1003510b00940203420703c0c6040204010586035880c80082c110b5400b8640840c203082c08140b85d501d03282c0071604207905401140482d00144071460001ea1082e03100e0740e1a510112030020000044610f400c90070b50000348044046110341c0f902c00b0160108901 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 188216996 1250 188215746 188215763
    0x604030806060d2c0f031206010c0302010908030c180103050403050a0e04061205070618030203030910030213080105010609050f0a050409021201020c070611010e060f10170a051e0712 80
    0xa0f80040408441400c0410079910b1013001c50002d030360a020b0200125000c1041c1c011418019001c44109031510000d000343d04102d00f10000c1c02c141032003500302000440c2c100c10032940c3c81c00c103800b03841350a074018115040315401031040c80105503c01e1003100e1103070b9010340c0c400e030511400c010211640707201c1003d0540d009844100c0410b804a110036500d410340e01c19001400b07002c0c030700b0001804022040c076400c00b00c480846000c00141e05c0c00f000b00d940000c003c44c2e91812130705505130b0641c02800b44200e405019003400c0400724100c04158071140c1030340d4058483e9035072165104100001101c2d000165500440d21080400c13080c1080c2c5c010300d01c1d542c030080200c201006000c45280c00c90300800d1400103076500c0070f0410030036584c210300d0141c0d03da007400c4024416070f81c140c002d056607268040d010001000218000030141c9440c0f41c0d80001614100308130b140000034410300c00e40d95012014007550030707005003858a24001317a100b440c049038007074280103441883d1403c06402c181c00034280050b80c27002c5 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 188218246 1250 188216996 188217011
    0x902013e070306180212120403080f19090305060603070b0d20031f0f03030f080c0c1002090f010e09010b0703031104060216172503020a0b0d0b030604030806060d 71
    0x10310f240545640400135050a42c007020541c0100b100c070341c41125003451039400460032000200b812004407010b8a4010040c250380f010841e103d00c62a1243c01108550020040001c1d00c4465002160800b268040d904448441d203a22080503203030002c6d4410401400400c20002001c41210340045a03051010429540d910346010301008455204032011540b103203091107449060388107130390198050406c181c800c180391402c594024080b00032108000060096110008103124501c2c4220b5500086e28020399140d60344524000c0042c6d004800024443c4440300141d01d15940324410b102c100719401025549180d103040e101111035072060300c044d8200350300d82400c0c10f40c0541120041004204a50051951420b4407000c0c841820003600081c2c080e96400840d03c01201c000502c000004508074003243d090340a610100c81060826030000703411a0700110300262005546020345000c204029090066003181d030201034844404407001004902c4c01c4001c03581c9424420701410307140291960024410303 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 188219496 1250 188218246 188218253
    0x21011071214010626060105090f1b0d091406070c080703021005190f0506360c271003021b010908030106021501030209040305030907090f0902013e0703 67
    0x54900380c0050141144082c00081703120380070149410740c4000c9001810b40c550414001900701c000113003030b500c824908a00891200740703081912403e1402d01c40441c3d90ba40040840000c050300031802c2c01d8441c7d003404039981400c0d0f140820b01e01c0c4286010340d9030340503602c1a130303031140d80c02c0d00102016001c51040384400c0d108005544200740c0a504200d990180c030003c000c051400b03403a00e10300c0403a500e9040206016280d00c0d510543c3e8400c0c00c14010f04841011981504800c000340c550322004186007250a012442180070010084440102e0b4003080001908040005c0c4404a00c07069800002040b43c0c400840d1095000d802c0482d41c50031962490600c0c1e103005401e40c1e4000e4400c0d50a01d00020041081d9034040051000303002601204007103035031442d0000f03004080b0041001c0c080c00400130004842000a0001c1c10140c0f580030700070480e070900c1052000013812403040c2203001c140c02e40050101035051400c062400040b8800b05810407442003ea41c00103a43e402186829104100020000 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 188220746 1250 188219496 188219501
    0x23010521070305150108030a090510050f0304060c03200d1a040915270204050a0b030a1b050901141011030a020102031b07051e0319050702101107121401 67
    0x2c0d0700400c010b290000000044882c200810b81c4143c2180e071041003074290458114100c141180c40440b10040d0107200c5100030742d000d2144031683c04100ea80041048208811a8000c0000300328550303081280c111003501491002105a00d042c1c203402060004030311004d4603420010a02e00c1d8000d40250b04100c400100d400d9039560308040701c0400c04e442c1d218012440600c038404040c0002200500070b40002e0342202e061042045000e4003c549640000d0704140345500221018000981241d48100c1281026004004070501c0300000e0f004441c000a4103140105440d4141d0764841c1180f03110300710110410600103061507407041030003495000403142e84420301c042c1c5100d402540000d039407407074400103180b400d011003020300001100a200d92004036a0000c1c0c1001c420005010310600a001c2410142c0f65010f40c5440240d1144804a01318206621002821013a032007904c42030079406003507905681c0100c0c0c190640c00705520981d010800000e4400440c81120b000380042d5840c1e1400300e17002c609 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 188221996 1250 188220746 188220749
    0x702010903021f270911041e1d040c2304050c0d05060a060e01080703060e01150210060509070e0612011202030d091412030d061401032301052107 64
    0x80d14001c21843c0301100b500100c0100030b4848a0f8280e076082d0403444113440e1249130a000d0120050b5485822010402190003168050003242d0302c01d88005246031042d01c00d485190040300030629101c8103062481d2510002c003402984e010140031005414081d11110102d10340300c0d250781c1a50100c0f035548081e1600d115140c014100c001c1c80079035416214120300140d0760060000380c01225205010044103502042c644400142481c3c0780020b1745034144110f02a1540e904952010b900722800000c00c910001e0140d80c0c8502150241c8805500d251604000c03201c60b880390f1500801030200141355107120340c800503901100240500c0c14a980703402080001c2100341c211490380c400100342001507250402407400c00240620301a04601d0402c0c40704c00f145242e103c0254020b0210711108040c940741442a94545d00203d4801c02019507281c810200380440180b000340803e1415481c01e01c5004404151804008140d0003404142d04e081c0c1440320400c1001024203c07500d5100d0b0903030040b48144035140 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 188223246 1250 188221996 188222029
    0x70f030905030c0d0b0a05250507020a05060c070312031401030501050f09030c07060309060b04020a0906031b021e0102041703030a060b0a020619020c010f020726030c070201090302 79
    0x801480c10481070603c0c1a0700c96a48504c5112040c41403400507051408640d0b024043c6000820144c40f030484503044512103202199002d003580c4052100030344e2280c043e1507003078001c407081f50703030f540c1e5485c288074491080310007440c43d03900150f10600110f2100e00d40c2e80c0c0301c510203241c001002c02d001c0c41c00c1980a607003a002141c80347d44580a201490007031694498114017000059850041d00c4000c0964840d1244103274000d050321918403805103d0154002e44101c00040e2013995100c2076002c005001d007100d030080d070340070901e448003030b000001010004130031701c0c1c00326001840c07000b035a800d141034912442071500c5a02e40d000c110200340710301003180703848404540d03d005544078204140203030141c0b48103800c04c0c0086103091141c6002190300040807500440c5501d455460120390075084c0000c1d10500c045100250b092903907161410710554018266030340507103030000301034007040313000054401c011071002d818241c144041741d01c000c802c000400003944141090781c5065629404501940f040e00e2082 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 188224496 1250 188223246 188223257
    0x30c010f050405130e0f01020a050a1d06030108010f05100b070809040b04020a020a120e090708040309030b070509040f0203070203030c03101a1c0c080c0c0102040b041514070f020904030203070f03 86
    0x94005c010028030755841a618020350406084d108014040e00541c100a010050f0f400220fa2006c0c240c08580e400c80e08020b4115652980c440f411503001c0e00c0000005d0503101e1400380001c511850200840058591004400d80780089503200c6c6600390308917080e0268001e59036400d100c0150340354030082a04d05440e402800c2c00d0411420700821140641c2030a009000802c0d070801240e5071800c22007030780402581058540d503240d50500321021041508001c000032110703010710015a4210340a803541107001c032014480c1c1e00c1e154004500b80e000c1075452001507030091001c980c1c0f80c42c1400240d0f5010840301078100342d0959807100f0590803844c4841ca01c0035118005801c1061850003000d0860000703c07100240517201d03c1c2d24004081d00001013501c22408004128101510401c0d011a001003001090079070b152522080c1d0a107503c4010034614012882c07a42c0026050036158040d038007440c0d0024a03264516089409100c0c2c1c080009004900318001002140c0000e02c0500e0314400c1c2902075a200f = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 188225746 1250 188224496 188224511
    0x141b0304080f06011a030f0c21150301091203050915070309021e18060303070b090705041506020a121707030501081608061302041e0e070b030402030c010f05040513 72
    0xc80c100304042c3c0045030b14040103504031180b030340c45600312604086100d69003100741c0e85510300038230540201c0c280b012070072030f10005404002480481843c081c0703d004500c4014400b0181c101400c0f5101400024102207010b01a10003243c0250b10956000ba035900645611007036014a2001c9400d08440328008244e03100140019420800c0406a142c034071680c207070061014010000c0c81000c02e40c3c0c6060b05d420b01d6000022900c0d2018410f584c00f256001c0340300300a504140640540380d2a05006070f502803854042100510b049012038030301203981d19000b803e2014076548034038082500800258082c007054100f206900c2030140f030344a00c101e0b0700d69000207041d4144103542c0d007030019030800d4050b01c01e59140e06000d1040e02003032054000720101000c051018252000c00c0241642081159111101c0038103182109196044440c0c0f42c5141c1d8241d0303550303a450b503c0c0e1500901081d10042d41580c0524542180e950260382c0c40040340b000c900b02907091036550300002d50440f0303100c0068100c82c0d0301c4904 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 188226996 1250 188225746 188225773
    0x3150a0b01110f0f010f0605130b01050f0f09030c0f0901060c0222020c010c0203041d06180f0703050610080705030702010605130b01020f03092d090c0702100807141b030408 76
    0x1e403401038001c8a407d2100f64a0a00000c0500c46010f4070460019900c1c1800c9250303070301600072249100040c6540a840b90001d040c000c0e080c0d0003228031070f4064042c03060051540c1c80c08108101c84400000c01c11407969003010422541d0f039810043c120381000c42c8018180c1d54055804107241c2a0340c0c03403100541e482e44801021403d41d0282d05051703043d91310511090010004002d80c4401c060680062600240d4580300021131102a141d000c6424102d880244070581030003600c11441907203c2c2d00e044c0860346440d0b040c40007840501c40000001108940459a8240300307000540d00300e82d01e8070011070507589640c0024420035000d601c100352155a44002146560140a01201c641c5c0b03c0c000f460900e0300d8440810b4010401c260384100e01d54500c3c500110100c60550701d0040c620f4041c08443c00d500c1c00c21040c0000d031380009420303840340c083d2078900301c1160720500c1d18a1040c0520740d00c00f10942114000f401ca15041800641d0f500d03070b80d18440f0f20300e0710000c0024000501101c00141400b800e00c01 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 188228246 1250 188226996 188227001
    0x30503250c090e0c0a0e010506090301020403020604030501020a090e131202210307030c0305090a08070f05030a08190504021318210305070f0c1509020910030b010503150a0b01110f0f01 81
    0x5113a4040d80c00c840302000000c07100c0c00c8503030444006846003942c0380000d100180c028841c5402c0254050b10201e404001d0100541c09001c0c1c080702500d925a60700c0d12511481c2e480402190305944074885801200002140000c07068411011070046680c4084412500011050b4042000110328004002c0204440e454080c1f141d4050b4103090800c40f500380034040f140c0386c00c01c144001d000b0510000c0c11508001481e60711090703c940000aa07622260150303001000a00155a0703605030911802d9650302d6690701d8420b080c000c0c0d0b402409001810301c8104440040d08521041d9a10314103106e40010210b00100c001002d00349111088200310b008810340a01250f802030014420880020f80516200740c00060014203990410340b40d521520711a410310000e0039036220001c1d04003c000040c0047c00d152009200142c91007070280d8002c42c1c0e2108141079403044000510310520114201007640894240c0c88070642510600d051904a84c50f100c049103040414088100c0070342c0706405410301c02e242071 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 188229496 1250 188228246 188228263
    0x3070f211d0d0f0b1f150905041a0f04150602061006030c0210020322030c0302010c0201020310030f020423150d020a03060e160f061701030503250c090e 67
    0x1c807101c1a1a000360f40765a00d8140071101c004054407031810208040c0140b071944000e076981840e0b18884220744454081d4150114540202c0100754080400f141502d414010400c070000003814903003e00e10b41100704015001ea114480340c005546644003036010b44005034000103016250020085420304e000d04c0401400c071540040105880d0103202c051181c0c0c0800c1c0f61001c2c0d1108078016840b5111750a2034140c0e02c1100c00c51514144100c8100c1c0105a00011821900d0b03000e50000c000100840c981a42030717100c01c40b058400903040000c02c0c4000781c4440403450466001803c002100360101c190076a02e200d002140512017500c802c20418502d101c04107100340210f041e2010284640140e001c81c041c0030540c000144116180c2039a480c441c2d0040040c140c0b035400703005101c0001a5076040702d0302100c0542c000e1100040c0c0c9424a0700746049503200c1e540c12603600000641c03034800340f18085c00030b8060310328801400c5400042c00802060340181100e0280c4070003040001c0c20200302c900d140c9000d0b2076 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 188230746 1250 188229496 188229499
    0xc0318040513080d06081903030c0e010219030201060503060f0402090108031801080603011b03020a020d030203160807020312040b060906030105240312041805090f03070f211d 77
    0xd220400402202c180b0070410a43d52200c034264841c401004000060700458000c03180900c21540c0340b9061400c05803440190501039203040141c0140890101c43d54a5003440c502d015038020001e5004200000d8010380415019200004465440d1340000c2d040040c25143c1e03d0240c0d008006000c298509100301031700400d814002145440040d11100c2040001225880c0c180079002001900f00d4500790080c00f03a158000d035010001d44c0c02400003400030b4100d041031000603ca58156000c500f030107482182d0080e070030450ba0791018002107004a40600000340f0705411400140610f407200d1000d000124026031040104402d80d00d403250500c24020001041d583c0705e42e0403c2c0074865801d0f0311112099100d0503005400344a1807803440442e240084010403500d11800018001901c0a510011000076500c201030502c4a40c82d61022543c0c3c4401001c003807030040d0001c102070400142e00d40440c504261041075414042c8000c0d10302150520020301110000c2801598107240084148200c0b2251120 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 188231996 1250 188230746 188230751
    0x30210021b06090409050109140c010906050f0c01150609090f051e061c03030b120d02150a06050d0305030405071a04061d04020703020a14030f0313020a050301020c031804 75
    0x2000078a03602500c00000c44103028800c0010369800d01d85803a00500c6500350003800038080c1c48154a041c21145000d2103807003910f4052408030b41115841242e012045407501d6841d181030100000e16608141d000280d8141e140d03507600d120f00c075400e10803041c0740010012500c44070b42c1c503490202400d0a4810f24081d02c10b25a1034902045195580d80340e450403a01ca0000e1084c0135940c4003000320700b203c0643c5d21400321031404000c0d0384d000c00d581608540002072040d9070000140d01d00d200c2041d5900c0c000d400a4026801001c017600c104080503413030b254405601800414840d641d9000b142c1404484003085c2c00141c00041000103106080100703c004001102403942c0140d040402010107015a006260030019400704043ca0200c5d40004003a400d00000c00841d604e803440d01d0040e61780d910800e000c40700d007a0200f045c0d02c90340d003020059802e40d0318080d40782d81c0713103a8030039800e001a4148040c08036401203c1d050b0101d0151424405018107004000045940300104810700d183d061001e04181d11850 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 188233246 1250 188231996 188232013
    0x4120509150711040f0b210a0b0a150905150306150d0206130905091905030703080601021c0e120c2b06020a0c060b030f0c10090e0c0403021002 63
    0x221188119002101d90a1990341c4070616407920300201d40f40c0d1484154080d0810004880c2450141d01085040d04110303040340c0301d05d2103400c028806001c070310311610300d64100c000d00c14089480306c0b901552160308184c000540141503545031005c0202504660361040c1d4410070010104d0000c0e80502d0b4600c000c60081086282602d24030581c49200d9480c10b0040d09144515411900d0f0311049c2e0b400f01d011641012841500c0b0304110000b0074044460b868a4810740b0f02d440005013a04514001e51a0400c0c0903520b080d90342c1d1070640300001e026205074114451800b00d41074075043e50103086540250340c4c2d1901d0300c03a448842004600b07040844040c42580001480303100c2c2d0366901c00e511404410002404000c1e40c0409108a0301582051001d8501030000601c200c081c0d46c880700a113000c034416281000703407510030f100b403550382c1290000d142425800385000014510703052036031158030340b100c1ca0711020b0a030b16400002c00000f01512000d014000200e8180114a8a0308803074212041c603100901e100f1 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 188234496 1250 188233246 188233249
    0xb0f091c12120f050a0b010305010506071110090302030609100b0f012003090d05060f07090510030902030309031e06060909031b01021207080a0e0613080f0c1504120509 74
    0xc050141c0c10240240d48403003502c01c2006811041d5214402d06040101e460042c60a0000c0e10080f05260f0010341307014004910b0340780075410340309030b60741041c0c035900b580220000380044000c105d6862018000c8105002005030b13420440e1600c03031000800580115000a07000206071240c6104907071140517004040041641d0220034405800103051407091184603c0c1c2c4260b0444c0310302f686558001c406242c02c0414030400249160160f000c00310280551f50311000d04441614490040f00e034414840722808ae12648a904412550703400101501e2600d503070400001d251000e020350f0b401c41081102800802002c0c144004d683c03082c2c0a03a020405441d0a48149450780328071071080030f14101c1054040540c080940c1034030145520780d488030034181403101018001e442d044941c10700ca00e0030559039070040d180210b03015000d001c0c0740380405880138161342e80d00340e503411440790b06840110910007121960020040d411084014007080003150800341070210041354100f038040c0900008000c5401ca6 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 188235746 1250 188234496 188234513
    0xa03240617180f03031501020604020f0405061302041e1401020a02120a0609060212090c01080c07030c0204050106030b18040203120d020c01060e070e03010905070902130b0f091c 78
    0x15046401c80910440c2c0c2d4101082082c5080352011801501c21280c910400010010040d400f6425641c1503c0f10a2004c800480e5500c0003100c0094000e840e80050340c0c0390381440c7d00601c1c0c021400811352612178202c0611542240c101d9400607201060841c01446000244610700014282010b86000fa054154001030740d03c50702c1c444000d009960888030400118002d104030141154040002e000421007801e200c8041c0d0020b40944009649103008203407503071000904103006030010f0715148104e584141e00e1402c603800c042000c3d01071120100d00c84006907980e1103202d01030640c42c4c070009280c12004c0140300081001d07650080c002000c20080c007002d40c3c4e0011b603c0d401c08a02a4003140e0326003403a0b10500c042d000c0d00d8051181da40c20101c021904240080f409480340754183e461814080d01c0c4800c00d0300f80d81010300060141c2c3c206020601904156400a05410300c2110791f0070030542d6a401c03821910792010540c04200cdc04081103844891411502e80c0544141c2100c00c61600354443e03d03100f52 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 188236996 1250 188235746 188235767
    0xc230d09051519050403060c0305100626060609060c07080d0503250e04020c0106140a030804140d1506030c1208090918010c020f0d0503010605040306090213020a032406 74
    0x80f803406002c031140d40300b88640c0448020b5070344035a00b031000366181c0f840600900780c190380000800c10046800320b03d01e480341481d800010343c0c00480018005403440250220314010740760f01d4110208220450194a8600007080074894082c002c21fa0945418001800c0007819800d010400074100700f8010312550800c4003c0380781120380410420303007030800d00540300c0107c1d00604940242c0045001c0d1449101984140c0460b41ca0720200c1109602900410148030300394040100500d1051006102c00e201da22281c0c2c1702030300042c0c0000403911107506c41d007856040f5030192805842e21400c041c410482004401e03001003101c1000c1c10900c500e940c3d100b51280c0a203c03000c0740103181c0d06000640b0002168814000700d400d0030000c01110780343c100000d4403070707414001445440c8651551082400c0c819821a812035009644650070a411552400040c2424000607640000749000010604034548000d00f1402d052b41c50028008100044800340951041d02030800d005100d0820440150001038072103 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 188238246 1250 188236996 188237017
    0x50106061110050a0609050108060f0c09010c2d0c1e0b0405010c0f0b10030501110724020c01110901120501050901060c060e0a110109080609030a0c230d090515 70
    0x140d6980c0303c002680c02017001e0303409115014140400004d401c1c0c0e001c05e4441c00380140a250104941e6840c02d138003040e2003030140d03850020380350400c03610201e240b202c400c60b00c60220300d845002c06864039007ca00301080040040d54218004c03101001780c12814070901c1c4081a040070007412682ca02066a015401103101c0c07141805542815141000308100005d0f40096009108014a041c00064085884254042110150b107840b03400700d4149480815550519848107542903e0480c16005a011881036660850b110b0340901500e41d000c00b080c02010003060100031496182c205510004040d041400190900e26240c0b4005100580341c00c0e81d9a41900c4a9003030810555040380b40440092002440810039801110b140c5420005140c4401c074030303141c003680e64094403038407a42c2e440e4507070005441c0c4500a910420180c0b01441c001d4100c0b134440f5002c0d0414454101a1410031074014501c0280103405402100108034940d4015025030003400c42510010075500200d081241315100d03031040715 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 188239496 1250 188238246 188238251
    0x2010504170a060908090a0f030209060616050303150901060314010608090304030503030903030f160914060412050601050102210301120c0803040e1006031812180e04050106061110 79
    0x40c440d060081003a20342c81c942c00700041086148504118a45801c0111164410f0b099401c0010b016030308042250190b94001f45a607442c0d0301c8000400000c1d900100780c2c1454420340d01401d0010030340604c0910700c80c884645102d18003050f0141040014a81600502e05042c42c21444d00c2c070121002860794107444086c00c00a140340c0f5042c0d0518035500403540300910622000007040b07994103011000e503002d800020312000d240d40f9184111f4080c048205010000281e0080c4e0401c40807028500c0e503900700b1406407031a0b150a8841803520050018140141d1710303603000200401c9156410400d581c0e120b20703414066500e0b807140920700078492006124000c0b4000d4001d41c18414428540118802000c401080b0303641e80ea81e901d51070028070700c1107a0b0380c0390400b0801d000041c0315000c0d0240313901aa41403030290120304c00a070b032204052540b000c1c40d80c0c10000d07141c9401004804441150010300600608000185843e24004d401c2d0340c61074001604000428218220190b00003440301280a00310394003 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 188240746 1250 188239496 188239529
    0xc0b040305040b0d0f05010b0910030f09230d02010219050c0708070f03050706020a03140c10020417010605040b151803030a0504060e0109032307091119020a02010504 73
    0x48071940502d81040069900000d821082010039a111540501d1301c02c2d818462a0f9076000c0c10942030103042202500b0001e44510100000e00c00d40c40002c61542d1020000780100c0715444030a9503526508000a0503291a59000540c1c6d4082259143c1c0c4407403480258070b803000e5212803504896082400c40180400820080c2203e001406280d010f00502d03000c569581d5551585011180940c0c4002d4076913004815011401c10300c00304160700c1d5103406845803584038203540c1000480ea4080b07007c4c59641d025007035840b0081212400100014005c000e0711601504240007100d00312412079004911441c0703020255038480d00c600c0b20070f13000c948199001603116000c0c2e01c000b4403490034684020303506000000d44c280d051a00480500f0a42d80c455552038000030040c00150703403514507400050941e040710241e113102021400c1c0300c076822001840940e445a50f603015050103541100080c1c9541e1000425410b1480c425130001d02c4903d4141c2c4004d015440d031940018000d031243c1d0213074040d4107e40301407 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 188241996 1250 188240746 188240753
    0x1140c0906180d0b16090303050f0f1e1b010912030b1206010e010e0708090a260f030108150c16061d06070f210c14030103060207060b0108070c0b04 65
    0x26160708a2000d4540320f9069160700d80400c400108840b5140040d00300380310321201e2481039070803800742c03a40343e00e8a070300e8015454011116500240326407002804204141c40e03144681c443d4140c00e074034800382d40340e84400d1980545a5200c0d180f00d104455685008542030204032a810f10001081590400158007a03e1601040b9003c410420002c8039205100000401c0754105100a04850314890380f800ca034ac948602c11240071809450380ca1042c1d2000400c60045186000090030340c0c50070300508001c9204c210341602d203d4000003105613110801000400c40c1b028140241121000c0c0144014211318040125122038001e5030410451004080007105c20480554424540e0310309050411160f50b18134183c032607580b0012180400008c0d0540d2003910014001c5801c1141012540040741c4c010501050200003030281115010421078010f0641101c04c0e080d10095010314042c10b40982d5660301030600c141034400342c40d502c904008000081004056004400d4420154401c40480c0192624203 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 188243246 1250 188241996 188242027
    0x3030c06040602180307030f060f02071a060310060b04080f0a080d3b071403030a080a0f15090507050301032d1506061107350a0809010201140c0906 65
    0x11402901441051b0010061000d8001441003a0344155014028071643d0f4020034241d00400c10014210811496060094441a000035500032806412200d07401c6641000e101500d181d036100454a040c0000e0501103031106103c0d04c1d62072840c0c0300040020021541e40c66000d840390481d1f0b92881c5030ba48544c0c0c2d080000d030400101c40406d2039a40414041d10711025005004180c0e480c2c45928450504001134418841c8451042c1c030310006c000d9400e005404105230b407040030042c9400a265519800c01e500c4241d41d104800c4030044400c01d09605a040013200e00455401401c00c5003840000e0004000081c0d03c1000e405a01d0f003a14000d500d04480e051103450b450445107001440340c0407403203070110041450342c840411561503640c0e1808030124102c10a403241010b02401c1a041c104203903001e41071a82101d40e681051440741c1c1c000e00c1aaa01c0341150900300020804c07a0f680e800010042d40b20341e0b09000c0c0894101daa000700000a0405c0624880b0a115120348280a200c2c0440d0150204c1400c8 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 188244496 1250 188243246 188243287
    0x11406130b040603061409010510030b031e0a0b090c0a03060207031b030305090114090d030b01020721120503070f1b0b090a030206010b0f090d020a05130b0108010503030c06040602 79
    0x595090b4480c1c0d280c81001c2c0140c0301a010f0b100078201d04803400e081c145001105a0b04881014050036405641048201d02a011446445400d807262144040314541002102c1202d0074989016003806c036482d2130405520034020302000c1040d070048c4031004440d81e5044c2c2c0711048039440140184c0d920101e14065454460440759034088035074000d0705c1418103401d0f8000c87c0c410030003000200507101900c3c04a43c00d80205551072202d03907004a03242d0740c0c128000d9100065400c014011a05010754504642c078044103040310140e00440e81c003411400704900850119003021160914604521b032210000b41103c0381c210794042084000711590742c2814244100590160300b00a00c1611071414868080c1c0c2c03100c581e103003240140302e030382c1c00001c0901d928015168a003805880091814181404202c22107800c0d001c00c0c0d074009801c81c03000607150f0300c5201038044d4003100f04000c104910960300241110303030140d11090007500100905030090f240401c2d466440f41c2e01000043e00c40340300d5840108046c510 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 188245746 1250 188244496 188244509
    0x7031409120303070f020d0c0507090b04110705010b0117010303050a0c03110f0f0d0e1309030212030f040309060801060c03050d0b0612100609140d050f100b0901080601140613 77
    0x44c402841e9012501410541c0180c084802c46020248105c684041e400000b416503004401305015140d000c0d0029440c03a080203102013000501361601c5901307030380318403003c4450b42e41d114443c13202540c000c41807040409c01245680200d40c51900c020b0260310074000700c3c504021003080e0000426000d80c1c200c0d01074030403a034111a94081c0e1061100c0c0c6c4c030110b11644000038070031407030348000541c410021000ca0880240401c020804650250310103803c1f5680c2c01c03020342c000c00070004d0400602401540c4150b0780103c09040c1e90030316003409080d036200c641003541002003140043c4007079a0012080f40b941941498a03698428264401c04000d00d0a500b10799400741d03000604040c1034550f09040c0780184124810400d04a0b62007800f60342c100c065201e20b9605c01000b0940b01c0061070160029410035000b03105581090041d62071481c1401c02c11a0102c0c0100c0d40c41d0f400d11024200240300502500e14500240b64035410800100c00b40a0102c103502e00c02d040c005650030b186065400c1c2c0200a180 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 188246996 1250 188245746 188245753
    0xd0b09010515031008070b0408011b09030f24020d050a0504200f0a0803030403020d02010209180603100f1517031605070f0914240105090103061a1e0703140912 70
    0x8887c01c90748080d5015116610256007400108104030452141442104c2a01c2d160490b43e01e1555407242d00109201009a50743c404510401c03a81e1300146503040703014142c03a0b10050b80c0300c900307010800480340058a000480e9240104010004088001188100b06e1300d002c542000c0502e60005811000b41da8a696049002c1120000345075100101540c020380c441c1c6c096032803c00d58400100c2c201e005000c4440d40c0240098aa01e2030501d40d10750300c9402950150654210045400d4250305881c5898035000c906c960350482600c01c0024010840044c1c1768618003082e60310440c00515917240510f11900310190b40c07031113100d0b08200c010401c20004003900921044050350702c41c400f100500c080040c2c48905501c0500144510310a1640c01010f10303002180b03000300f262031900441c0c26400c000d040c1414140c1d40c007400314000789042c990040f5180c504425540d220b00c007440c007044102d80f203842a400440c1c03e1200400094001c1080f4900c03103250740c0d000c0c0d140d48200780000c88404205c00c40c44010300 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 188248246 1250 188246996 188246999
    0xc0f0c11090c0c01180b090609061f05040207051b1815010207051305060301051e071413141003020301030f0b04051002040312020c091509040515010b0d0b0901051503100807 76
    0x221445d83c00700c8a8050040c04509a07200c500858446408895072003c83d04000009007002e540000c42446039000d0010204130192580c012508070783c050f44c0306a035194480f000e10400c5000042c6615037080701507c00d8185d1103240c40c410001d1000c041c202501c0251001ea24030916482000010000c0c08014030042080030b40901c450020030051b41c84502a500380030001f103400c0c1e031038070401c01a00c80402001807643e8812034115081888081c0ca00300c201c0041011012185401c035925024100c0e2200103400401c0c503404202802d0200f42d0381030141030046c07004001041d034901c4100e11541e08940c4800e050b5a40f1303c5c2031418081c0c01001d50a00503c0818040244003202c000c1c0204024580c00720740c4100e13501010050146002c85881c1e04400c2c0c4040b0390006410710001c81d6801c41d22600480342e6101030310300705e514455000d030080500c3e00381c00300d0312041c840d04500418400d824103548030785895042034089410442004880e4040050000205095011100c3c034817000f08050400d07280c07031a = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 188249496 1250 188248246 188248271
    0xe0a05010603081207030c081f080f011a0a1a180a18140c03130312140603120a0e060a0e0306090c1003020c1b031c030c0f0c11090c0c01 60
    0x10342001d00390f04e801c541d41c4800a05500d010f403040c82480d450301d03200e0000540e2007480d001051a8400d8075522075046031540021428820403ca000d00c2c081e600001c911000c213400810194001364010301e110f9000078a041140c0b00d003600b00e80c0c60120001d802e075566180c0344400032241071450110150400c20074080040d9010031340d0100310346240800000c1c450040e0b12003203244c0182069072078080c812420004aa0b4282151001450192290038807010040e5410420001c90b151400700e800386c01000d10402ca440d01c3c051100c003064003a402c42d030030f051a0115800801500c001c84445018420015901d10501d01886238a080d280300107084030840e181040e0216143d40401482a009038440d10610002c5070181c003d942241c08401c1c0181440c00f1640106206a00030340034150305030061840548001d1424084c0f108800d072951008100102040401440380d08554a8070041000c509501e01c0015100e441d088640c000807034013501d840d110b100d80d90300640329810344000e2540c40d10103800300301c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 188250746 1250 188249496 188249513
    0x10801022107092907080a0807080c034b0c0403080d02030618040b0603060604020f090f12030a0207030b0a0b06070303090609060903020c03010501090c020706030e0a05010603 77
    0x80c000001c0035900100c114036110a10020191569004030b00e010509100c05090010202d4191800300010342051310040001c0201d80d00c05502510f5480c00054600812a00181d680f0341060191500300e05628101a04c8039541c04040c1031101c03a0b501c0e1382c0340200120002409030740901c08014500c048044100c1003010a03000d007045440c85111804005004490703200d041d20102c0b41c11080441c9041c1c02c0ca040180207620041c00d29500259050b0b03005140000040030f18440c030312900a0400c0f9040c10020540f81020007441c0301d2080d4010420b00645602540c15901c02c0322090702c000c0800110b9400081010b20500b08160320b0b03120200e1f15025880d40043e24004981c05107402c2006a126100741c42c0542c0c0102d00c44a8009008000e04000240301382d0111003540c2c069500010f015149130b4440c4262070f03450310b080d00168480c000f5103007a480c0c00e00c951801440c03010000c100080d18594044d480d40341d80d03c40c080034143c0d504000e0381e1134081404840341c906e034803d000700207003502c2e460581c0320f = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 188251996 1250 188250746 188250757
    0x210603170a1e0c06270c030c09050c0702010f021e0705040e03042d0305030406110c0429060f0d05010317030c0f0715050103051e060f0406020703020f0601080102 71
    0x19a0b2012100d4407035200d104202c041d400340c0e03032401aa0412912200045c000c0204401c00b041603540d1030030282c0051110a02c149407180710012642441c500345198400c40c41c0e00503504040c0f8080900030710000140c200c80040d542820441c80712032040205030f0030001034100c2d03907a0b00d5171048516800c10307001240301419100c0440d0200f00301080c0304003075540e80c0101c0c0100100b180403480c0d80544516605000d45030340702804803d40c8c0c000d1b12651943e0a5820a910200100d0b0703c4025241d60124140843d00039520700340da00304241e502e456070f410058880124a01504a001d491070b070702e01d8940d6012101a1481811075076500e02d400800d50005000074441501d0407510f4200c0e20382408981c070100d034000d45590850300d051580901d103400c10b9900400b41101c41280362665001b00352154002c03107000350300030340c0600250704041c1054071200d58113800b001c14582091040041145030035160380e03085604800010703110304041c601030b071800381103549243e000e10805000046801d415001010b = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 188253246 1250 188251996 188252017
    0x80a0906020705102004050a091814011512050a030809330106020307030215100305010504060506040b030c03031209010b181902090d060b03010f14010317090121060317 74
    0x1400e80005c441d680c0707008901034143c1c0505081c40400c01032161780c00070070104404025810b808065607036050701d103090701d2006580a94403031411007001116001c0c11001884e0742020502a0002a03503001d8031603045000040a005240300800c0c1400410400e80302c1407541b101d0344140c100260a00f14441d41e046070302800b1307a190150008507440b84040141c40001d641a0020300c101545c500c058050940c0003032660b040340301440070010106100f400b45074020750181c1d01c00030361410250144001d440d44902e05501179030000010801c04d0320000104c564081c2058000c0c140754071003000c0940503008840c43c0c5548910300700545078540d243c00180c0380c0107180000c41c01c101300c94140c140e041a03010b031b2040e80f60300c00c03280f021075401714040750008000e280004000080d28005010b20744200c43c058003100f00101d103079a00500c00c00c2404580507802c500c03150100350400c0f800d00002040c02003542480d04559100d4505050200c0482d0030080140da408801c068001c2030090450300c154000c0790805 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 188254496 1250 188253246 188253281
    0x412120207122f07152d12060306020315030c0a060c0c0801090302030d050a06060c03050a0207030b09010603020102100605030601060c081905090f0f1f050c030c07060f02010c080a090602070510 85
    0x61841d000d0410070132101082c1c6603440104461002d015882c06d0401403a1050100240842d01402a14842c843c061032040c14010380b01d00b8080c0c00003141c45446069640242c0c44008102e550743e40700031424048510030314003030b8808551460482840b20b00380d40020815809c1c903101c0000c05030040003800644444000821040da6201c9030b00050ba4001d1082d04e0114822803129004244201c0040402110600480701c01c20303566940c902c0100e034220350b464482d954400c030920456074140310075900b0b0720f400031061001070b0800c000652504018803981c401d1015102e02d242c1000009029250180031800d500040454444d1018000e03034000c1c64280d1158403060040303001840c0c003c642c04901c040c090094a07078042c00480401c07008030010210402d1001c10b00c40014541d6040000b403040700341c044044c2c00620300d007203000303070807a0881d4440400796414480540001580548107552040c0d41c920040703012030542c242400284240e0001403d2805080989000c20b015034000402c24028800e01 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 188255746 1250 188254496 188254529
    0x52101350f01022d3106080711010908030a0c0909020a1809180308060102030d060f090606020d020604081602060d05190207020108060f04060b030412120207122f07 72
    0x103d613a0100b00302070481c1040f414060041025107072443d0790101420300300111032588602e043c818403854258410f00000383c1d103000f001171181e402075031405868001402409a080c940c0e50f40c00150200034402c0e2000c035520401a21440d2055200b07200510f0319000455850b004a140240702c8001030802160038000710000094424480c40748411565611641924032006907030110f4800c580501811304520040c081c0c11030070f1041d4882d0000400014420398195460500c1040959489a100d8410364000d0f8440307440840c1c011070129809030307100c04025905e4440e180000002c60710004041d41140b00800c9a09401c2d11550000d8090504890309940194086118a080c1d00c1291402400500068049070b082d0610854240046800500102d40280c40e42d07035180c0b04d90421079080d1140c00300d400310724444a8014204518036600148103624104550f19900580c11800707180c201001030b00e55000c2e0344200d8007130512160072540e00b04c00e4203031041082c006a580c5207600520680c04941d415 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 188256996 1250 188255746 188255797
    0x180903030916150804030509060a05030a0f06030c0303080a0f0e01050a1505010509060309011b121a01050301030222060b07060b030303040c12050c10052101350f0102 73
    0x4848040f5080020303d22800c00d800f180485803d10702a0040341401014440302c402c0b943d482019110100380c1ea81e0f0241c481c50180d40500c20f641082c8903400125241000030f00110b40da01e40d0110582c0c0e0142003801981d203449001000810414504010040c50803072409003000d0103400190240302142d0003800044884044508421070b24403440d804a9030400c48044282850409154880a80000020040b801d010540e8442c4040c98041001030220224124242440c0c490000c0d0803101c0b40c0368000700619400041d0607440180000391058550f951101e29440640000c2e07140c0081100c014040160703034000808080c4c0150008503a41c50a1861038072041c200001664491504440c85110403480d09184003055030210b80c0544050142c558640c40b6510b8003d426014440c4a513a910364601c50305102301001d203480e0201000c56624800100403e0079129000c5115560290390068a004e034581d24010000342070204c0401c90040210300d0100c8401940500b2540f4070065103070140702403a28 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 188258246 1250 188256996 188257033
    0x3030e031c0f090806040305070219050d03050c0a0212160b030c03010b090d1e020a05040203190c0e0a1508060607050304030303050a180609030f14030a0b1809030309 73
    0x42609100d46088803524292446290044407214242c03c0030700ba8551100842424200d0440d02035000c680b00107060411402d00c0320010302c000c2c4048c4500d0000380d0402e000103c00d003120101c080c080060210b841300000d6814880c024000d43c0c0105918101c031001e289107911800010b034112112005050001020203050040b40e214011045eaa2751840e0b00340814542039030402102a03401c5190180130034001880c1c0b01040c0c20304d10b00c190202c040440103104116001c02940c200c0e03409039005006100728090700c2030905900c1d90704c0300d0f80030428111194040340e2104660030344540c04500408000703610400a507010442c0941562001c1c40c039502c4800f402417610442e440103056038001c0200700b0203c0d00c26804960410308007100841c0319603e030b03110811080400042690705d56500e0154004041c1c00c440e05104100c141d08201800700c0080c000c0750101d020050007612142d13103c00c1e9100b0540d0f502c2031a00c03102c0030010841291410302021060b5203400c00c0b120701d80d140c440c0300059045031841c00b = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 188259496 1250 188258246 188258263
    0x11011407111923030409053301030f020d0618050a05010303020d11030405060a0e0109050405011a0d060509070f091e09150f06020a05071a16080d090c03030e03 70
    0x1030b8440d41c2c582d030880c0e8410110510740c510701c1648014a40c1c100408802c240020001442400d07400308660421160f0a001d0f00c084105041e03004556054691800c20032040d007141c955002d0030f00003940c440c08a008401391248500c5030884c103117400808070700c0c1d880341c2070ba403c58260410030410140d41c5400707056080391001c4c08003901603400100c6c5520b4052240c095100b291034404140c07410f05a9590210315203030000788032680820040105a101560311680c1140180340c00c813007c2c0150751505c12400c0e001c43c41c0c0400000c103c0350020b0742c3d108021640c0c1015008200c0541280062b240520b0000c00b941d41c0301a80a00190308940005a285106481d1b10282007282c4a070410b0380340b44c05c0c42c0c1c00040000681e032019100c0028000102600460703110b900608103600a45400521403404038103040003904071810882c0b1802c1e0301c040d04000c071810f0b036240483c2d160004405228a080c08090341c02400140c100150074103079103d04010526072001d00310b9109449048098244a00701602e50000 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 188260746 1250 188259496 188259523
    0xa03030207031203090b07170901060b0409020d0603020603010306062103120b1f08090f0703050c06070309030602030408071103030a08061009090207060203220b0105040c1101140711 80
    0x520116800e00c48410080c0584c2c200040d08500c0d03540c1c0c0c020002c4003201e000011a05c084040381c11038040241c119030080001008128035420f181200c0d400e40218000e4400141d03010483c0302e166103041c2e00c01800b458000308401c2d10ba6959150440182549014015205900304803000f043c20561650346071407903140d00c0b4140450754000c0220014410859507640c000440a8080419250509052802aa40e9031f40180d545810140240b0b0003811821542d450f178844507041010400100e58800401c00c01c0720030301c0e40c0c0c1e0104c1c10201ea44d4a2039800241c0014400403c0c00b040100d0000245010b40c40f5103607100c0f261415000701504d902071100e0517000300c1c000400081c1c41d0302c2c250309146c03200c040c0750601341509074a23500f00c601240c0054100302c80c6154008148400d0b0b00440d85100300c2521120180100c0b000c29944a8207001c1d01031180c54081c5481ea81000c000d14001c0b0400710b0000c1e0010001c02c400704c540c2c000304203018005e8403e003001c1039000c1185500d60f080814004060103e = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 188261996 1250 188260746 188260753
    0xb09161d0103030305060d021f020c031b1302131205010b060403030c06110d02070f0c0b03071707050f0c1501050103050903040501080603030d0c08090c0a0e0a02071719030b0a030302 80
    0x6943c03804d6001c0c140080c0402d03030203404401d900005984000e03100d1910aa5034658680d16122200c02074501984000c1140c829804011803160b201c90072020030003480802d46a0b00b503070381140c00c4407401901a4408a03200c0c0b440382900410306900004c0070144a9000310000c2c4503c2e0b2203082481094469030101130300042060000b88040740707140d0410b1180107180c1410629181c002503001c02241c00c400001c0701c4040124402d0401d0010b082c0d2520081c001c44803038103240d800c002e48080c041081901c08012034602200c0001c0e1924000e80588110200c1026141e03940c120840503940c4414118a11407070340c0d603640b00082919482031081501c42c020140c011480d0074141001521810b8005041d42e42c984002c014054000460703000365101c8891a841e54070140c2004140341d41080d80d640310060040f00442d01c10414030081d50000c40d00039080b8240141e42d01040d05046010a5440c240c2074106400064003550214121242030885c81081d601000300826000c2008103107040d911000c0c00592 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 188263246 1250 188261996 188261999
    0x70e0702151506071b1701110301050306040f050c0d080d0e070b0a0e0301020d020408030a020f010515010c140a030509010201060b07020303120601052b05070f0906050a0504030b09161d01 82
    0x1030900041000e140a05c100d04001201c00c07800122034a103a030032005941480102e5404910303c00d004080c0c5055400007002d04560600f00070a41d07500d03004002a0880141484510900c4400e0181c1760b480b0401600c00700f0541228181b00602d03900403000f1061301880e100340c80c81c400300f0210703490090f00d0254840b60b10308854500b00b02c0c0c00c002c6440d01c80358195030800c0000300003486440180020a0a0b03405507841d118111806401c0044003c001603a90341484204110b10b14600d0b03813280c000c0d0303003420302c2c0c84840d109051075198030405101e61a0240b050505110034581c0001c040c3c117041c1001da000340400c941b91083c0c00b40c14011b91303000035055030080c41030840c86942d001c442130707002d00180340c81410f100307407a9490000038401000c520041c0055550012010005001d900c0e80203c090818604000c0c014000808020492003600100903000c00d45c26511072060045800954001c8540b22141c10401a00c035107412110000c00d6400e0710450700059030004450113001c03610039112000b8a580e = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 188264496 1250 188263246 188263249
    0x403020a020f014d010902030d210f020706020a11160815060102030f0a0305010f0509060d021219050f0601060c08030711150702060a05061504030204090c08070e07021515 75
    0x6084000400141e004440000b110072101c040c0003410644c0c1031400401d00790710301d0040c14204000040301c4010024115104c40d0302506402d4805501d4154080c005011200105010001d00130500000c190307500019080c949160300030700c0c3d0104600c0721001d5604100100c00300480c0603c85100c0e00176140c000015400d03c003940c0b0010140d0100040c0103803890542c1340800000664003124050000c81e5480006001708103401071002d000e440191455501350074410002034904000c0c110091050f42c0c07500c001c2951032414086000400d44846409641e00100c1c9451a20351007107815558540c03042c3d10000480c02e01c981c1c20f1400c1d150308009242c0c50354680090444061154481d640c4881c4285980c0c22814620481e0161095500e0750141019007020301c000030641d20003501e8140310380b030708004590303600840100311400c4a604440c00102422145043d00424000e603000644c0d50050500c005910b1a600408502c2a00954262030190903004400c0c0c002d4803042d228084860141c0085100f80d = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 188265746 1250 188264496 188264567
    0x203121e160f030216051009050d021306140114032a090907050306010806030724110303090105062b0b13150e010e01090b071808060403020a020f01 65
    0x541d80002141d0a5000310303484550101151840440c0141d00c020980c40d08804000c1421010303100c00ca42c101c100c008900d0780100840401d02071070f44a51080046202155600a01000380a10004086c004140c1e01c403a1180b100224400b01808105d10840c852210748489040324403d2840152140c00d80852003035082d9040c00b04403046980d50380030003295046076103001e401c511412541e42c81d5581c1e8035000c0c000400208025001300e000c0e61100005004403807080b11824100f0541171a0401c14440000c021105c5d40900700c21442c0391f00000040c0805442e06402c120b00c188420364602080716404441c421089032004144a41c04074024001d00008000310003664202481d51002d1002d180661645140780d0031000902130441e684495041d40108203002c1c0032400c002c108002c0000c1c1c1d01d08d440d164030b0260010080c5e01044862194101120041c050f404041c00c1000c045070348034540303454003950751400410700fa480303904c0c1c61081c5801584078110300d80b030481030002c00460048000441185 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 188266996 1250 188265746 188265757
    0x5040201020a031d10030c0306060e2b1401060f0e0402031c0203040b0403120e0d0f060c032a0f02070e0a0c020312010b030f0a0207081804020912030310060305011505090a0b03070302070203121e 85
    0x90340c41000038400042209440dd1154010804000184c042e1408000805281c20355100004130703008102000056580031804805222100c0e10b076010f0303004a80002c0b0f0840c41603811194420002203800701c1440203080c140d950f10030f2280c80c1e6820054011301005000284000001c103124100d0403064001642e0743c02001c5220100d017808140307004d10416800300c0b01c003804d40c0700900c0e856168500340050b6210042ca407500960303001408000c0c0c140a9142c0c001e00e8000e2100d00c1144d112841c811080b44200100c46a00982000780b00755940c40d40d401e4680c540c000e85500b10041e01d84404100180c2c102d100b102c0049034010402c51030110007851503407000000c4120350780e00580c20702c0410002d460750b22100da07603101e440000c0c542e03e00d400f120076903c61140c0c0e00403200b003600d0440180141700ba8201c6c26241304c109404c0c52901c81d403c010029261400a0704a0464420040144000319030140c001d071148900c21816076240400d01c40e07000c22203005031042404002140350340d001404900a00408 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 188268246 1250 188266996 188267059
    0x100f030f031709060702150601020d030e030f03090304061e05030a0c121107021906020705130e1911090402090a02180a0602030a0f020105040201020a031d10030c0306060e 75
    0x9403402c800c14400c1c07110382c60440d0340841940008003006a03240c0d041c01180c2c9400d900103c94030541c189a00000d42e15107500f031090b000d042c0e481e00c0e0340d440c01500308180d42c040c5080310102903a078a0302d450348617100d400c54821100443d1000c02c0e08169003041e4080f850200106568081c290368840c0940f501915101c1d06202c184000d600e00c10346180102d00601c1c1100c440300201c036584461a04c14002c4043c08400d201c000c050b011401403204e1036010644004440c070171582e00c2215159400020700801c1025600800b52107258580b0702e48100d06412400700341d0048a01030701160482c4103000340480121802948018a180040c00104443d406041c803100807a44403510040102c010402c082c017a0303002500543e2000c1620144503500604003148889203100030b11007401c0c1680043d65401c844900101031010a4508081419014111030707010400200f103041d14081c04040036006010410b44140006c0c00c0c1080031410b90f008101c0c801d041760f0b01804444d014031040301e07103400381e11601c407c48 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 188269496 1250 188268246 188268257
    0x30a0e040209030d0207060e0f0d060c050f030907030309081c081503030f04091d030a032a0804060507170103081b0a080c010506300c0d050a0605100f030f03 69
    0x2075083d4600b080f0f1400300c49000e8005005c85410140e020300b41350300c0c1000d410300c94030240e5424842601c4884100c96100d0b4444008600e4079070154040d2142e0007800301e540007114001c803c00c005800001740d51012030740243c41e040300050316500780a84848800081101115248000c40c04592180481c95480550919070580a11035400002c4c25503100349561841440c0c0443d09100c1107143c3e1140c40c00328045003c015510410302d11320f09480303000b1890310700140b556649804164200325440b61f90801c8a0136100da050743d01c0914003800c0200180d5041c0d0b80c0b07901e40f170001080030b4011200200c0b013140420000d042c030b0b882c580d1100d071a580b001c040307000e084400c0180d1100d4100300304100d040d164898041d540d00c036800c0c02e402c1c40c21500010007040c4242c1d451aa10070700d09414a0442142c01c054944500c0d21040d2039200c0d505d02800c1502e000d0708405010100f4007801404282021030034442c1a0500198071448450360588255018503000d07201004801c200042e181e007000b9890f10701c41e0034803 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 188270746 1250 188269496 188269507
    0x70c052409070503010c09090207030e09010825060927060803040618030201050a050c070e09010c080a060e06270a061404092303070501020d020703170108030a0e0402 73
    0x4001415040031401984100500d05000c40c0c0e140600403000a00800d50007000305124465004000402c50710071405100d40c000741c6042403520414111208940140080050b541d580d401107546a03c100000c0340180c0b004101c0c8181c0d030710070340164000c941c2e41303503a4500440d08121001400500c0c040d02a0010b80040e03040c4080d0280a0003007078010880c0001a40d2500d140c44805840f0606148100b06101c03442171082c40140e0700001581c11403002c5240035138460012441d114901700c1c503900182030b51981c0f032040240c544815003010745c4500c51540d810382c0d2916503111140603030b00d0501031300070305009920005200b801c107094401c1e800c41500000c5075169486551036414042c2c250b40c044840c07510f0300000e0003030a9140c0c03004401d0304400e0b5400c00ca101465102c0d00588251008400c500c0c4010080c0b041c1c80c05010000e07a00125000402155030307203000c204080096005000c1100414001d80485245401412025048403174403005589005188481291070441c036040c40e0344d02c41d60034003c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 188271996 1250 188270746 188270773
    0x3020c030c010c081806070206010e0601020f010e010501140613090b06070606030302030a0824060903030d0609021b0a050604031b0b130c1a0d0207021804050d0305011d070c05 77
    0x740e961150f5a54803102c500d03061403d484008900300710507004541e4040c0f410b000803954005801c0c0e045444e036402c03419040e00e410340103d0814149445078249507080280e0006818010360155040310305031240071008414200905c0481d01410204140f110031007070301088091a560001080c000008100e035180204a1b52140c044403519082500181e20101e058290f540d00041441d8010884c044000d001038000d40c2400a8210003590b410f01400000c42d118000f624100180e03810b10b02c101106100c101d0b1111088002034000c152a030400700b01c030401014841402007003c241140d004005001030780d640391000d817400205850030310503520b0422303150b0b004500314144c4c640c00351042c40b003050300030b12060820001c0c51003aa0000c906401401c160300e86002c95100488020021880780581c85492500004d906034200004103e6243c40e1a0104000c0001c080b9a00d5a0740c05903440410a590308c0300c864041181a440340c2d070a0b5039100c03001091040f40240b0348420550b200d0011903540c0b690010 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 188273246 1250 188271996 188272001
    0x3030304050307030e0405091e010f020414031c021203090307080a030b030609010e0c121c1106091914121603140712080a0b030703140105060f090703020c030c01 71
    0x84095419400c041102c3d010143e105000284442003250240401c0c10f00c07444440e01d4205410304c103408031503005181c4a84100a40000940c080f0040d0708545456490079a240c45c4507001c1c1802c0d03c0390090f100e2101e0207406810000c8910300703141e402410038400c454054500c0d64005030040d0401e200610903900010307000f100a00310350072160b0b408105c6081510031716241640c0178000c5404e80c0d041208218560000248520380007904459040000c005000c43e1401c0420b2908082e450000c00070514030300c2038100303c1300001482600101c1e00d0543e141941d460309e480410810b130003d8520103800b6000306861400303500c2c1703200320314040d5101a40a0f4813905140d620049402d610011104020020716070800c050040003240807014a00d400c2d500c1d070710f070007030300d0020b001910a05c24604045071001d110b6601c401703580d0301c0c05011295656203900305609200e002000084007982031400068042c103282140c00300c1000054400703000368440d10780540181d040800302407490f12041c003180841100c01d0 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 188274496 1250 188273246 188273251
    0x30602040306062108160204060f0e040201200616050c010603030e130b1503130f0507031101030c020c040b040b0d15140c1624061502010c0503011a0702030303 70
    0x550340010f58030714242078103440c031104001c0d6520303c900d000300c00400b04038650212448200e8141000407a04001d1001030014801c0e50001c03070282240002c08180010207103074660041d4000d0701c64845080b041140c00a88074031284035900b860300040d01003507500524055070304442c0b68174200f29046c002070407290340c21202d556009a0004802c0c200080d05420841521561410320041c184010341600011600c0d070f040511a0b07510262000001402c0302440c406a00404d5074018056042d180352410829543d61140c0070581d114441205030140640c064031031600c1c5e5a0a9802070a61003a8080811008000c0c0803c1141c102c0d48401c51601c055031500142d10381c15114410345200f0111500030041121300d82c0c08001002d4030b0301d03024440005115010b40368880d03c074210b0722003046d06501e4141010380241c0b240d1100f40712902100c00003c2e2040e0400c00c02c2d50b04461250b4120325034518228243c9072a80b49080104070200700602c4a810680508500c0c40d5120524515009150703022a1460740304 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 188275746 1250 188274496 188274503
    0x1020a0309021e0d0b060303070c150210050f06040507020f0a0606091112010e040204060905150306060a150305062803031206140409050f03031509061503060114040306020403 77
    0xe40401ca011071030b00d4041c9160140f40c0b41226508250729001207041c619a041d0041c25549042c1e00080d032940e0104104e484060f0303c1806410f10a941c1d80c41c03000400340c0c0421001c0035014003071400c0c094000c02d12401c1d106413050754800800e40c0310b0340280001041c01a02e00c800714020b560308a0807a803402c120384c0702221321541000607082d2030b1158810854000280307003980000c04100f003501d681c1000c0b00480c1522510402c51940c2d4640e4400900108503a501424400c0d040c42e040210700008848480c50b190300540c08d0361055642e903000c01c2200c0655001d440000b8408001008030b10b0311950020742d2200010304a000c50082002504034101e4041d50b03a047c0e40001c4480500800d940211400704442200c4410311140b420aa08c0a20088070644001d020f555600720f910140141009030840110100c010380e0b942c0c1c28540e804150203200321419502680214002c10000e0900c0c600781020400c281254a045894040044409600007052440c03101c03402e21010012549910040c402580b2 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 188276996 1250 188275746 188275751
    0x16030b041407111b031c0207050904060b0f09090316020a12081905030106020a082a0705040c08090a0314120f0f0106230318030d0f110a1b0204090501020a03 69
    0x44892070fa10741088140b950a49154001c41c044c10760710006040f80b0110126121a480c071a600038040b4035180590780101c1d4403009810030305c0107010312940f048041c1d100640c0e14000d04c10441341803200c0510146c3d00c218040d0310400000c148008100c8117200d0052005001c912034594405508201380c112710410341344600009482642c0301c02802c00d0b22020046401c1c0039081d0b614188000c0c2d00c90421a1016008010018043c184d120520100d900b034109048001d09140031030443c4c4550382e61444c002c6a0080d842e025103c0002c90040d40c0741440b540c030410003050703480f560b0f075401c0702c201000407840140d00d0700910a0000c2c00341031120040c800c152041400c40189440c0989548e202c1041c0c2c1b21800f44400c809048005030704840b102c5c03120081c1154181d03030360740f106031200c1810180e800e00c040f428000030a0003d403591182c0c110380b0055030311103418000c1c00900f8800003007d110f4a0300e0303980440c0010906141554620000d050002d000078800a10f020050301c6503400c2e40d00c2080940006a0b = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 188278246 1250 188276996 188277017
    0x50a0f05010b3a091a04060f06080a080415111005070e010e01020a0b0613090609060b040204050616060b090f04020a0608091011091504030c0b0316030b041407 70
    0x1d4145811803005824100f0300440d0f20700d042811422188410b0050700a032600d003810240007220340d40c0c550b42c120424007504186040d042000081c050044c0283c1890700303008001801520009a118205400c02403040c6803e1a12210106c440c4841508100340040480b4070401c01605100c411042186003201250515004000030103024000107168103004c2000c400c0201c903640001d803201c510342d10501610b2140c4500c0300082c4103040a070000039146041451840400c41d4980010201a125110903c06400d0100812080e070290b801000d810600601021034807041c03095014100e640601d9000400020b94004108401d07400c494131205071401005100840c200381111500502251400ca4600d0924400080d03d0390340e090741800d10740b52907040608420080c1000c54044403170080c111040c00f44519044a142c0d0058442034a0400700820001000c15a00d012688503515031040d08481c039400a5040d40181100b1081030b401c40e54440c200740200c005d9007160350164015498508988 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 188279496 1250 188278246 188278267
    0x20423031903051b0316080904090212031b010603110607060f06090509060601020a0c060e060d06030b010824040201032408010f0c020f0714010507080327010c0c06050a0f05010b 78
    0x343c426550107540d8410007400002d04401d00391a005280e004487c15900c841c1000014003030030304241301a6024490440d5030b08d108500000900c5c1511300a10002c107284181103056080f207401e4400a0b10000c65030400070034924002c0d0080c28150722034100081c20b0301614020104642c60f542012614903924414032174000f00402c41140c0c0580309100034a02007040c4c1d075806040d9181da01c00e140911200791450551580d030740c0241c4d009160074900070401c0640d6403c000c800300c0b1007846060405d001d45101c10a01d00780c880042500b001100d0305089054071140d0045005040f200c3d1404441209003002c0d00c00b441110300410001d04541c0300124100031903031440300031265204a41c4040d5441203281e052914000b09848044500c5041c07460580650480103035424454003400505031100042002200001c00300740d0500b81031900c1d0281c290f80004540d070790032039121180410100300c1c0405000c0016a0030342003540c1c4162050030210344c1000030110841a65001e80110081000100d20790101 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 188280746 1250 188279496 188279527
    0x813091b0e100903110f220b09010303021506040f0c0e040510120206070201050c1e060c120f04230a14011b080a06030f080903060a02042303190305 65
    0x71224115001c8820700901c85000e031815550f8840104950360f40b40d994681941d410300c1580c00c50001805e840034203c00900c07061104500c904005100600d440400e500b40e0400c03005c2c9034140e944c1900200200c08080801e25030303210009003065403045d2075100f201c0c120441390150503e040400d865481030a01840304000550350020301503202c9c2914680100160420300405842164051740d0701c0d556041d690004071050b01c10390000343c0440c410360340743c0211855502c03080c1140000d840705980701030300e8064200c60740f4401e41030040c07401d03d20300010442d0311030490348041d0800d2184803000842200d00318120001040d0344282c00441e0030009100c03041c42035182c1c002c1200c0e81404001c00c410100d10b00d098500b000e0282c00e5a0030810660700150b0907003d240c1c020800303182c0000192a400030030f032410562950103110170318000e0050701c010031103d2180740291810340300724004600d003202c2d59107811003424401400d00d0b50300d4811080098900440080c0b032507000c60007a52629036810142d2003c188 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 188281996 1250 188280746 188280767
    0x30206150103050606180a091416030504080304060510080d050c1b0607120e2e02010b010e060703140307030c17010f0501110a060c02061608040f0813091b 68
    0x18141031000b0021345a0b9210200c2c0d08500b10181c0000d00d299204010032080b400c41e070003406505141082e600f11190043c0d0840b4410ba62115002e03203500c1c00c0c04402c40503228203131002004c1c1041480440c00117a40e82d000300754840003103201100026a104071640c54045c900d000300c80803d50000300409485402d100d602c4021001e0100e4104601c004000300380c0303a01c501840940700c0e00a451000079450310501c00000c0d4008001d1401c4401020171101101620311030443d41400c0c42c196021040e060b0040c002e100001030305854085007075690909110080e80100360442c00c12803102d0841c0000d1107081c0c05140106410340e8005100041043d020f07158003188600452001ca10300010032070600010241340035034200b0b2800c084111001c008261a244843e5001030a030360420042d8480346070700041d0749105a2042d40c3c608102180c598041e6038003c410f40d005051008030400c8980442c28410041c40c0c40c092120b0540c02c555503407280c4908540c1d0307044841304510901a058898190f00001480 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 188283246 1250 188281996 188281999
    0x809030a0f030e04110403170f0d1a0f0d020a23030106031406010b070b0106031a03011410090c0801030b1003050d0206061e0102060403031104050604120b01080a03080705131203020615 81
    0x303103803504545480c1c035045403a851308011094001580544519a40152501c2201c504ac0030f00500071300d91002040d200d0104241070150364030b1034413142c0c0c0745403091501d00070f00d030041c00c3c01d0f000724103003110000d10390100b220314142e01004221a64880c0c8003440741d640114001c0000a00c00d04400800c1428504180c0c01010151014441c48012900c0c0251540c115802420300144600c14a56092114418940f5180c1d242d4a04809840c000f0001000b240c17040070082c0070b80002ca1707140c0d41c4d40811038040310401d03070006609000600004460030341654120070620700b403440551356907450710b2a103000b007900a03005800590134004281001c1000e501501210182d020100c1000300000b956002d0003440a001c254071a420800100b40c01c0007280c02400020781815aa141c8440052030501a00c040403102c2c044603000004124801103601d41c04290b00d9686c64072651070302c020480b41c5400c0140505503219081e0000550940e907228068601d5100790003909052400c02a0030041c04445240503 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 188284496 1250 188283246 188283281
    0x1e03060c0702060d15090e151602210903011104030302011527060b0a02160e06090112050106080105070f0e041506050708040b0403050a0c090c08040809030a0f030e04 73
    0x501c0180c0d603407010f03144900d8400500090300c054804010403e0082a0f0050b11900e14281c074891007403102042003480340301c3d1804501c12548803480f15001e0f035172a140507500103812111b84800d001e80821102c41c01060386900c054100041c3e40c3c0044d0031500034036108040045d0000d81007082540a024040d8510445442c113140a481d02450800c1c8105800400040c8414200c000e500618254000c80c05010403c000d00d46460341035601940e104414000c01c0d0403441118000560300e040d0741401032007000040c00c0045640d2810f400c0707500001d0f541000f11515500e9050110b4002424400c0c0e9220b0b483c140d03503a610214145901400145001c50428015811b10100c0c0b11805039858a10003100c090746001039070b03203045040a0045000d20f400048200c00c0c00034000040c0600010a900c003a80620300c21060181c1e60070750f41080320100d0f07100d8004030b1030f0322000601040341b01e0044c007441100682900e4201100782c0d120b00381360140b400103c010070285d0240040c0e2341024840c0405001400c0070342e = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 188285746 1250 188284496 188284507
    0x120910020f030114030a14011a0409120804020d050102070f110d02010c0b0903090901031110051312020a0308120f0106030e0a0b15090106020a030f2a050102091e03060c 74
    0x103000e403005014402070f0708000918134465803010400e14000c513802208095042d0341c09002c05000c3e00000c00400302c503030300c1d82042961602c0d0601ca84041e00303034884000e250700c201d240c1007501e03131030801041030b03034421440341c00d087c0440c000b0700080c9412031240310440d011408034908401880c0b0101000c1c0c1c003452088200c4030050360841e512481c09a04003840382070f80c1d550000700b24558030455103c5030304017203410000800c01c40b1243c503498440c10225050480c1c09205501151240582000d41c0d41485182500b0070050001d021b01d002d15038000f0304803102680e241d442d040e585502c082044400f0134000401c1044219200c00034502411142ca800d0000740813030b11029658036000c0713001400214608000c5401c040742d102482040c4640038104044640c0d6a0340c01a468410705c0009070041803c50203203110f010b209048041440522400243d103801003089403510300844458100da15650030055091603503110a00000e0401048000b03483e44004201818141034014010107000300b014840c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 188286996 1250 188285746 188285767
    0x90b01050a0309020f06120105030f0610060f03020d0c050c0c03030a09061d3001060b04060804050c0a080106080709060f05150d110304060b191802090612091002 71
    0x445041c0307001d501d0040b034110090700004562030305200e00c8980c050b00004a4260a08015200b40e04980c0100d0a8801080c03c4020090b00c51004450f120007100300c009007071040c94083d1100716a2210b20386001824085414112000c941d00603402802142d0301081f00300d2040c034104400002c49100390042c0d810070300580c0020f001c5003080e000741c0f0184240214019030305e0718402001d000d01d4000402400a03903260b0040d10960000050312081c010742c02240110081805000d14012215841b040a14003440c28108644100001c0c1048455001d03a0600311110703560303003181d14080c0481030000202c040c544000c81d4034210040e07202900040c14074000b000140d404845040455100350b550020050008620600034403840601c0c0010903d000780300c003410380400020b548214803c010400c40f04a00c4810400e1400a007891200100583c407824440c2d81040c1e0400b070003407004601302504242140f00060384e1500705036440300c402644841008001d060400c40040f4003c800442146881404078 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 188288246 1250 188286996 188287007
    0xd0603120f121112010605040314030313061107300e030a33050f01061e030f09050604080c120304050a0f1e0501060905010b120a0902010513060908010501090b01 71
    0x900c0311207850340c1d07010040c0f14104850308031682c1020080c0c01d44010b42c3c40d0040509070313070002c1c0410780381e07410b100b11110f081700c1c2c00004a9002d85080e110b407041c000740f50340d151805080046507201200800348010700000340f005400c101001c2d00f40b581010054480c54141030105d41521945041052039007002c40c3d66140480d000008980000c550a15041e2003000e0900760000100502030311802c03444096610031380713684400d004100358001691a640d07161800c548590941c11a0909a0941c8041e0440740380250700c42d481c20001414040741100f290b0300c80c40c0c1400b50844040e41c05110004104004010034000b10304550140d007506821800d098071803c0d0744900049008010090300b4a00c0402d0013032444203580d4114100900e102c201806280c901c1c0604154800e40b4402400e00001250402084060350350325428054105001e60741c9a1103d005084680416414800e0401422090a10324102c68011346516260845107c0c40c10003e00c0c01c641050344401510351030f16503407062030307030740700 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 188289496 1250 188288246 188288267
    0xa0902090f0a1401080a0c09090831060203030f06090906180304090c120506091909020d02060a020f0f0319120f020406120b0603040203150c0d020d0603120f 69
    0x207486503156030780e41d03100c07650080c4502101410301c808420000079880c000000c0d41e594140c41003040c1c0741c0c0c070340d034031441941924918003001701200f209000c0749070355003642d01100c0c2a034443c0b444210880804003110780006011500a0746c0180c100104001c2e500402e100469041041074600000d0743c6451051180c643c880503201ea064101c2c2c0e0704c071002d82e040c4100240e80140c002c5034000c0290103010340e0050030061540054011980c00c25000540a1070a004070a11402001c0449410035a00e8024800101381555040745c0c07211104a104016840741400781119106c10340003080100720001e00d5038a1b003c0c40027003018059004000c0d0700000380d40910f264040383c0c401e0034030385030282d040244000944644104882e0891003c240000c82a42c000300001c0708490701da104001d07040c0071206110080c401204c0c040d4066000e41005c11011001e103481e40e078402d06558191741001d480c0c10b0900c1c241e900810060741d107291104010700034000c00000d034541540300e600b8484000144d80c100500b110400 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 188290746 1250 188289496 188289511
    0x30403030f021c0c061b050a0309020103090609031110020903030d0b0102150a020a09081b0603070210090b060a09020306011e0207090e0607020d0207030807170c01090f0303050a090209 81
    0x7200407980c1c0d07802046180c01c2c0d06900510b281500c0c00142c0010641062100c09a549030306110005090001d4140c658042030b5440d916240340401e044010340250551400407030400d550f80ca40032020505603c103140e0600c0c885d54400c02c200482003d0140340020300950071006909c1003002503107586e40041100c0118100000100740c0c2129000180e0500503214a0241c0440420f000c0001d064a0380c2c0c018540c4209075207070b4414054a4440007076540c00001c20a5000e1058516184520300d40340b07000d10790083c0742c2d00c12619841030380348154090742d041420441d61a00a181030195502d050200d49000c1c00c0104030460441c80c10030700017450081d0b09407200d008500720815040c902c40c400d110000c00740140e1001801841c0c0d0940c1400d0341e0380400c41364036005004c1e26081696040c07012451404980c0c01c1003000d0b08010881c2c031400301824000440c0107003842c0070441403d0f088400c1c003401f1201da024583c0e0400440310340c1000340c00c0d52401018070080c20729092400006981c1c000060790800007 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 188291996 1250 188290746 188290757
    0x106050612060d0f0203100504020a080d12050406060510050c0c0103090201050d1e0212180a2006070204230106030b03070303110102090d12020c04062111100203040501080906070203040303 83
    0x20340d003040e1221002000c03005c0c0d09070161441c600b86420840d00040c1c003d0f0704c00e03542c41c51656a98128551210203441401000842c203603040c04405605403c243d4201c1e01440d40090900d035100000350151030050407900204d070020901ca9030000013030214105c0c1c40d0302030905000c026181da00003047d80c441c10018401d09a501e07074540000582d0b8010a42e691140220b086685d0031550b16600b4001100304c68101020703160001004a01e08042495152613621181c4151004500c4103500301c00300c40303482042e4201e1800d0155902594840c0a448c0b02e002409181c07505594510403540c42c20030058100d01c05060900582d00303c15140016400222070709845e2803001403000d0132030a8060300c96a40b0655000e4000496141403222402e0380c818002c1c1c41f9002c882070345001e401484190390540c45a0381c041c04459500070301c4502001d01c020482e031302c100768891401607613500203070000d10a08060f00040c1e00c007181c14045540c01c82c07096034000c0c408000410040c0f030076100096030781c0701e2400020704100 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 188293246 1250 188291996 188292019
    0xe0a0507050a03181209090e0f121e0f0403030206100b190201090c0b0910020f0c0108060f0406080f0c040605030d030b060f2b050603060c03070c050f060702010605061206 75
    0x50310401c0a113541c5a00c503c802d81e29907010b940c000e04c00841c40c0100180c0354a446d00030010000c000418620300040d100c06031401960a64403c1081d4014180030a922001e01c1c1d444529011070304020404070881800c900d48441c210308009203030440052003001030115030003040c0302c2c040400b810351f4259440c0100e00c19220b030543e14124094280404018100d42404101192100d07010b0301a00c0c2141e02903e10501d5400580d03012640c54211404610540d008144841001d5200d0058180d00101c090030480038481003101240c201c5240c1d034420409a0170084031040c08250500c0f601d20152401c8809010b00340c100f1b030020342c42d0040c0c1c107a50400c5c50b9a82014082d107032100c1c001e50b50214140b0345071984400e04400000c01003481c41944c001c400d4152200001440d0b05880307618007131071029009150a40d60941c1c852090340c0302400e001d051000402103000001e10811081c006200f101d8080c1005051602e00a400d489450300024481c10003408020040c014201c0e1080e03010000715002400c91 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 188294496 1250 188293246 188293271
    0x610050405040906021902060c0f091c0615050f031507090312031b0801030f14010209030a06060317071203021806070f0b01080316140102090d0b010e0a0507050a03 72
    0x80c4140d50005411034244240c20060003000e502400c07290340302c4400303080b102811000890320381d54201c0e80c0403042c44090100d2141100030130080c1c034421401030a500c9107076003490f0202940d520034402c00c0f9055030711400c910710ba61109400e000000e0600740c0307a01d01218400b0380002d40314103040c0c0a04d00080e1403480003030303c41c600c580c028400554202d016a600e503030303000a0090251540412012284204400c9002c40c24450101141241e400440202c01261140e0300e0b100000340c03200740700d401590240905a941d94003032212008044c0f00380710000b41c5c680b651a150560300d60030051141c000e40240144070100c1e110001400150103903203801aa070700c080640c50105c45e807148030401c0d00010042401c0080111450889032a54002c3e1a401000d0781c0e10f881d195a20720034010403151000e0010000000070345030740d0210703a1040d9400005411b08029501052100c81014000e40e007a01c0704400401c000340b480e40c45560811500001448189803052025000f4843e40003c1001c1580d01e100c00080c2 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 188295746 1250 188294496 188294507
    0x105070f121803020604061a0109120303060b04301a04050f030403031709010b0f0d0c09050a0209010f02150403050f12180c04020c0c0103151203050d05130b0610 71
    0x146502d0212a425546103050007981c50100f01d804442c294540b0043d400344507148010640b22400c1607440d691300500b400c0c2843c035600302070303a03046041c10303100c0d0310106181c119000036001170504480340345c24008031800b2400600d1844142c0a9005c0a22030380300d0042058000c01e40046904000c9040440d00c075454454a4041205500122404041004030405500000d00703442c500000d2a40c0740c144d2140c00300340e400c950768200c4441d03214101d04002c42450500021107021030303001d078490061141c0d0768040103041d2031045640c142c03496400119400c066030868000c9103040c001e0b00c0186018004081000210400608064207011300442d000030512946800c407026007482c0708203280c082c10440003480c01d6002e64110244213001e5896600c11608081c826070750200e060300020406805c40e80300546c001c0c4440748902c0d0340070f01183c2c80401c094507d448203504503807003562040e0f510075591034090304a441c090265451030101100320400305220300e0180c0e4108404843c042c07004101580d050743c1 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 188296996 1250 188295746 188295761
    0x3040222020a0e0909060702060703050606040f09020d150b0f030604091a012612090a0803270a06021c03021b03030406110406020712020301020d11030610020105070f12 74
    0x30303600018280c0c408552003580c440300c3c100203859500701a00d80240403074560b4800c42e1b2410059001c0400a441c90740300790001600030902078049071601e500d8a290400714007079908100d03206a00001c04c1c034509001e6200740d4003801480550904443d0500b01b00050303900c504403645640450100229000e42d440364840848564811490540c0b00800311840b40248000d00c10041c40d01d0032000d0712074100323200c18281d150121a5a01600140e803804210321000d410107142d07140c100e041c10902140c080402c000410b8100302002c1e03001321a0b0401160f0305c0410201890b080c4c0250204d0008000d81500054100003406540132807054049007181e0440080c0521144520300ca0030003422000d10070350200046012380c0c0202001e20141a007001854520312441c80356100503440001d0410004d8001c1c1e070b46c005050301c0200090b2902100c16000c0f000d0300e6aa008a880b4940004140f000320318052640068000c003e000a100034541118094845104e00801c0010701000350a2010309d2041940541d0 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 188298246 1250 188296996 188297059
    0x702060d0902210a03020c1203040e040f0501050403120f0b0a060804061407030b01121b11030c06070e03010b0a03020a090b030f030c0a1209030507060c030203130b0a0e0a0b030402 79
    0x801140e503602e00a9a4012081041d4054024280d1f44200c600f8010040191240c000e40103501c0c0910b40920380081180050060b00d6000f400594840010400c0c01010b000d503000f070756180c0200c0c040c0390849044946540c41071601030b2078050018840d895030000c00c0125085800d003855136544604240b0050f250520740c0d88800c0a0000400061540580c000001850203a03210300c265540300b60503004444080e80c41d0b03a040307094007008444852065561070101221042038034242044a22218540341e07044d5a6040414110603409156003024801c00d0305411040341d0080440703141d42c021681e016080e0040c1503003035450b04281c101c203482c200540810314501c001265501c1031404003194030b4a09551045540700c82110021510700e01c29404078041d2034019024090051801074155203440044c00100c7c107500082c01303501050100307181d10784000c0419029069880566000080044003c42000c61054034031400a111152907441600c0d44258140d0701404940c86449100040009000c03403103 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 188299496 1250 188298246 188298289
    0x3060f1f0807060207090504020603010524070302010507080606270d05070b0304140d0206010608040f02040c08060301110a080c0c010608030d021804020f180f0a0914010b0702060d0902 81
    0x350140c00042c003101120301c1e03035003500c00840d01c6440342010b13208247c0b40658008401d0005201c5440c12009400f101c0d041905280b1043d008041c40310b4090704400c00035400f5035506c00802c1081500640c01c641e000100700c840a24000315003140b4182c5060400300d646e01d04684e51000030164803100000b01c07040760044101c0b02001d540380505203d640c01150200c0300f0112030000c1000d00000050011020032164018003842d0782007000403540f400004005130b03a40c0300b100c0b0010015880b0340c0300710001100b1903503e5034180e203405d000307041c00d6600b00326176003071070500801c01ca403a00740d4400c901c2a00020406c8581380e80b19213058089001d081c0d1178100c5106da00000810390b0512000b640240740009401801c1550401c04d4002c004c202c1c0a090f001d0108003a080104400d21503403140030f20032404005001c600a80c1c0c92101040240e4203940140103699500c0e044051100b0900c440c07140100049004180b03081d10a0380400c1d4a4040c1c40707000c41d0f1a984515080f030441d6a800c03040f44603000d460950 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 188300746 1250 188299496 188299499
    0x8090c06130807090606052b09030c0605070912080318070609090c0c020f01180308040602010c081324020c0307061a040605090112060f02030a020903060c070203060f1f 74
    0x206504840c240b080b90a68840e45200041242032800b07000125003640d21080d013040507540d1a0303d500c0000c010a070458001c079601074141c2e1849481882c0d52107000c1d584102e4001e0407880d0010031100040d250710103200f6403120401503011401091080990712100041e181e40710200241d4003d88281c140c88460700030050003280d0641e015084104440d90795405001c050342c1820240c0303100904440103500017042d001e41000550141040c01c3e0b044000c110006405566515181d000c0d82054100c2c0005035104c01403221055030001000740c12070025040c0b0765005815954000c403040320440c40724058420010214034144140e0305a4004111010540e9960203c502d0b00d0002040ba210004205001a40c002e860b541024410300c019981c02505044207a42401169601021080b404445081c1c0710340c200d40c0b125a0500156016001129000d41c65513040400c141c1004402800404100030034001e80000d82d800080c0b042d001040203096906a881e404644500400c592103000e040d035004220 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 188301996 1250 188300746 188300767
    0xc050607020f06070c0c15020307020d0c0f080c060706090c0314071a0a1d06070c090f06080a0812070e190905010618170313151b0201020d08090c06 65
    0x80403201000040c2c00d0721102c1d5624081a1800000420058900050403d081c000d8407000c6002c03081e040d010380116130a1403183e80c0025a403240c112011100284505420030100d6034641059018040040c0904110316400001c0b91103401040c00180000b621501400b040c00b410109120195030001c0349480c10300f4008001990303c02c1184208054968620b003011160b84808003034544640c2c0507030fa86000c4032002020301c00d030096801e80880e40050104481c0d0300140d000d59459004041048012078400e140f01a001c0c1290030550003a2807a81009074140c0c001181d19084070f4000c008403141c00c80d1620350120071540c0c1540780c904650400090251904121424640b1004071441c042c802d01590386c03109070458540140e5003000100c080e42281c10712440701c101c0030002003512040c085a04110040380450580c0d2015800404403031582c0c0c01c107130b01c0c0b2030f4008540b5610b0040c0065030380581d019540003d56a40700e1420400c01c0108140c04645090b2040c880003000a90042c0382540f281580300 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 188303246 1250 188301996 188302003
    0xa0821041a03060913051905030f04090b1804020303030c220311031006060219140d0903170304020603010e07092409080a0f0b0a0e010204030b010e060f1507030c05060702 75
    0x4400307602c1031345400c0c001624103410021aa0100e40c2c440082c04c00460114007441e4a446803d10454181c04180403c000a51540001c0d01c01040700070004100c480032501400510903202c40d1400140006400b000056140001101d820a0551034841e45d80c000d00900080c0108080b4425030025802c0f02d80001405060341142c8481c4808a05a81080910a0042044600b81d108900158000e42c0040c0009a001000030850340c0c014642d0344d4040c00c6001b001790400c2000650300d00451034403102842800b0380180318100510000c1d002a10354240303030f0001002400144900b404658084000a400d5482130307601100030440d1004646082891030303a803585880b4032581d44400543c0d83c18001a0b58000050110007440d00070700d0151100d2056180c003814150020300d450f060301c4c1c82d412000c1c0039210920040005502a0b490000c40f94109034144c818040301074002031003555141c0e11801150303a4942d58044640da0703030b10016034134482481c0c1607903146041c41016205000d0130080000c03164000c03 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 188304496 1250 188303246 188303251
    0x31e0512030123100e01030b030f070e0403111f090204090204090b011e120803040516030b15030d020c01030e010f020c06060a060c030203090415030516080c0a0821041a03 75
    0x40c88001c02d007854403c20720200000c0c0b40582d80005e01009080e0b0800e5001c3d501080d0383c45409801c2c0d8400d14045402c0350325003075050740010b50786005141000281a4040b04000400040c04090105110013002d650052100910601d00f215506c03c0000c0c219982c550001032007580c081c20901c508143c5042c251134180c030034410100304101e107800300034200350000b0591064400100503907021003103540b00e0f052103800c020021a064401e000c0160210340f0441c407840019403040c900c040301ca1422403807081c800e4440781c40013800303580a50091200c10307402085a280c0b9007030030b1900007040304c032401807a40580506903890001c503200060f10885000007003180b034400c0700700303440c1c24030340950300c2c1022070740e01c02e52040c0070340160030900c02007845240030b4001031028015003c500400d15120b44070107040c0b0303101505407010b04803449400c205c02841070001c464008401c0325104542440c20140d60384407101d1208801b14401b0758042c0c201c809000c4800c0c3c4001d0500391400c10004444103480c0d1071240d109 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 188305746 1250 188304496 188304539
    0x607050f0c0a0605042d05030709090c06090501050904050405030d09050309040c02070f120606211a0105060f090411210f0c0712020c1c0c0e01031e05120301 69
    0x10201140d0320740203004172002c4500704541407001050107010a040f488890030410135280203090009031a540800c110009454480d6001485c858189428031f603154040d80321350b092048260f030802040c0c3c1c0045c280c8215550544000c101c40d5070764a0140c1c290704c1110030b20344a103480c01450800348100000039099800d01903508220f143c0c075003082030740e80f01600d2184985104c03440c8020304c40c8440c0b9200210809129071030208000d5140d8080c402400401d0300443c00c44e55814034840d09200c2d8000700548403e40c4205c00309069410310020074540c0c03150300c01440122000080b5940780740c40300e920141151600c808102d423a064200701c0d140f181c0c04000f441c82140c174040070209805154040200303009483e800e10041c540462599076010a42e003400c40b04065001e400707612071003901c4c0c0b01100081c045000c152b4440140301c030f16041040034401e4110b00e25000074980148001f8064120f613640c03c0a1503d202a00e2120a141403441e0100c180c002408984011000040548034860501c540084 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 188306996 1250 188305746 188305759
    0x6091b090e06031c0504050414190605030c040b0109050904050105250f1d0409080a110f0a0605060607050f0705040b0402340506010e070807051e03060607050f0c 71
    0x5032481000c007580010340d1000d9040c0c2000c07a9000d00808051860608104941001410155210009800c41e01205603000c105064071041100f0b09075441040210158040020421142802c2c0030035a504c0031048001e0250756035980355280f0303030701402d0840b0081a0040c1175a00c82d00e03261512501910040d0b034030f940c00c40001c820111f21841501c444202e841c0c501e58602074020f600100c100c500a003074245041c905201124003140d80d84990041c0e122441c058000180e448484060040190703412070141003061f008850070070021034020030002030301500320300082400e40360f26001500c28842c20100400303074417980c0c40700805620040b440c0021110103d4041160204110900c0140d105107482d00809162045201000c00350001c4071183c03031004c41074041b00080d07040d6207162a015080c1c0121240032512000c1014250b48103c0d4160310801c1460f1a60034142c81a4040f50f859420204c440c0203044084000b641d85c1d113440090790034403900001111468a105581280c0f112801603400c2e00410 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 188308246 1250 188306996 188306999
    0x1030f110306130201030c090e0405010e0f0a150b0103020c0303040b04021801270e1605040b010c081803030706180b0a020a0509120a0c231903020f010306091b09 71
    0x900400c040f803141d190b404140601400590044005100b040713840410321149803004510300c04c0742202d943c401c40c0314500001d140780c0001900c500c0d14031440384c5c148840d8860480000040c20800d03802011911218000c100c004041006030086c0c0503001550a040c8004000c00c01407108403019980100e0080d1000034001043c00c001d151800c00c00d00594102d014520640c62111406000c1c42c181c110702c034980046d041c0e8054404600300201507145003a910f90501701806585407505c5600580300090a10410342c030751b40da03030b50303c494021944042c079600800554100e032070300c082c000c40d203401d40d000340c080000424414510824804d45481a603080c040c480c0000c0410b0418400c403180c1180316212503041c0003200b000c00240c05803030071504405001c1c2030016030029244444000c041d1980014820002601064290b4900044403005d403180313844040c2d000785640045100d105407034054444010800031400180d0207040170743d103c0102149092407012094a201041010031612035076060b0030203 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 188309352 1106 188308246 188308249
    0x10e0a080304060806040203011401110111031e0601030527031908071b0b0c1602090c04081e0d110a12080114030105100506030c04080601030f11 64
    0x66002081c1808116013080486601ca201501e04506541c984210108507400e050182414020301a0100c05461020341005082e0505048115a68182107114180d0030350a206440c0780c40c4400008a5421b40c0310b40a4036001d40f10210103c5480115294415031000000c005035035603110030084164083c00404461944100545030710f40b09241c500000350003100080100042960301113005400225401520f581001c2174400c401d44900010a81048100f0b031000081e62000203401084520504a001801541c16040660b105c00c42813001d02d010b0300041d0605481c0c180c01c1441010b0707c40f031140744115036110b014412a40502450307110340c0c22111188501d000002c0318080107009003540d068000c980480c05a00800c194505511044618101c80c000c55115503000400b20300c1174501c071000c0d00c0c00781600ca4250780965a4924041102004201c130460780220f20040c04c3c0c405 = true := by decide +kernel

theorem cover : BRFrame.Cov 188129496 188309352 := by
  have h0 := BRFrame.cov_init 188129496
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188129496 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188129496 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188129496 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188129496 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188129496 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188129496 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188129496 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188129496 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188129496 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188129496 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188129496 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188129496 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188129496 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188129496 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188129496 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188129496 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188129496 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188129496 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188129496 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188129496 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188129496 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188129496 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188129496 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188129496 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188129496 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188129496 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188129496 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188129496 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188129496 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188129496 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188129496 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188129496 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188129496 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188129496 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188129496 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188129496 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188129496 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188129496 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188129496 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188129496 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188129496 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188129496 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188129496 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188129496 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188129496 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188129496 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188129496 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188129496 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188129496 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188129496 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188129496 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188129496 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188129496 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188129496 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188129496 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188129496 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188129496 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188129496 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188129496 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188129496 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188129496 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188129496 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188129496 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188129496 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188129496 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188129496 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188129496 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188129496 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188129496 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188129496 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188129496 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188129496 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188129496 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188129496 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188129496 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188129496 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188129496 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188129496 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188129496 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188129496 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188129496 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188129496 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188129496 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188129496 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188129496 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188129496 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188129496 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188129496 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188129496 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188129496 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188129496 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188129496 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188129496 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188129496 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188129496 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188129496 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188129496 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188129496 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188129496 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188129496 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188129496 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188129496 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188129496 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188129496 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188129496 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188129496 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188129496 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188129496 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188129496 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188129496 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188129496 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188129496 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188129496 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188129496 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188129496 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188129496 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188129496 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188129496 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188129496 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188129496 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188129496 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188129496 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188129496 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188129496 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188129496 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188129496 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188129496 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188129496 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188129496 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188129496 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188129496 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188129496 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188129496 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188129496 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188129496 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188129496 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188129496 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188129496 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188129496 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188129496 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188129496 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188129496 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188129496 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188129496 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 188129496 ≤ n) (h2 : n < 188309352) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
