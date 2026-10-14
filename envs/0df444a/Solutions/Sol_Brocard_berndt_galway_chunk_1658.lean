-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1658
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:05:32.664973+00:00
-- url     : https://prove2.me/submissions/8c3a508b-6e94-4bda-91fa-f36fcd95119d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 298021582 ≤ n < 298201438 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 298022832 1250 298021582 298021589
    0x403090603061a0a09080115140301050f040b09011503080415080403020c0d111302030115020105070c1719020f070602070f060302071a01090207030e040e0a080306031509070504180b0c0d06 83
    0x7d50078420030391080800c018442d0b0544000d10f028400c1d0b52140e80c00d00d4201e40080310308503220a441c401041c01714440d0070580750400310701800400c29051101c014200005d440c0d0044424000000f010810007041900000c0998101d04e41981e4604051700d000b540c4803c88040180310b42d18002d103d03020000d002881c42078442000d0000301500e05960030b4080250002d2282101c58170f0003070314140140384180300e0a882805c0c10b444107003a02010744c95544c1c44400c400c0c1101140e41e02002010304802d03000c599129041c80039801484140201c080c4142025555403101c2d06650101d031052150700086456081078410b6403034011707100c42e61030030410038080020328503510500c038003030010034100115001000d806000352100b0240c0c0d4407400501c412142c0500841c6001c1c3c120b02c90346000070f500e07030f4001c40c0c00c80401001c46014200d103038510107844d0f00a89004207164000542080641400c2c007500c3c0c81a02d0100c1d01f040005159169210f952030020004a0044000030b50381812114035031204015 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 298024082 1250 298022832 298022849
    0x918030409060b19021203011a04030605090a0219030b0a020f041505090f0d120828050609010906060f11070e360309060d0f050f0403090603061a0a09 66
    0x141039036080c14100c0f1341e20540342c0f03a2a09420410b00c241c030340e00008101120174900995a0320b136a290000851600c7e5038001c4552000004001c0003000c41d64500410f0b0158030084040d050f00c140d103104110601c440907070721540f01280e405041021540000006500c81c0c1e9030000981d0b0340000e04200e03201841130fa00140c002c3c0500c0c1d00300d603c0541d406009051007140981d61140710380300e07100800071303929400380008111880d61040b00c0b034124412805640c00011003030454803442c15404116910016141c2d0482e58941e0740c00400c0403e18280c021240100000c4604000c1c00b400c1220083c2000d2001ca81d850a2000700d500d03500c0c840408021500040062400e441030509110700c4088002c51800c40851003d10744e10390b0a07a000f81041070b0095100e002e04000c0d0300c0c02e000c46040c04804d40145e42e5182c002951500d03803441c1c4606500605102d405581c14402381f40c039103881d02a007600c503a90060030406143c6102408001c0500800c1414580c0050426894000c4064110b4182c80700340c101540 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 298025332 1250 298024082 298024091
    0x80417160b250b0403022a0a0314010603081903050112231507030501060e0109050306060f0d050102070605010303080a050609060d0501020d0c050408010c11070e04050a0c06021b0d020918030409 85
    0x525a01081d010729400c01034140784147c01c2500e40c0e00412100e07206011307500c04820b203030410000746405144841c60340a580041441c80c0c3c2ca80f1003d145410881560341d102c52146034a03d05290f051281501500030320285c050501141c0c2c1702c82103003c428910548266402c0041f5000052003088031b100c402500e554407e203039103070410b0003c0c0503100030721901003c1080d0740c01d542078a40c0218a9003040c0c2d0350207030080034180c3d50780c010400d20460140e08540c012003420715407800318a0030300003402c44d030f401200e021829514515000b489040c0041c241c0030712034981014020280e0b40e00d142c1c0e44e008102218001c4000f80300741001030091242c980c00e140014035091423807814a401102400c211660f04008000000c904407050f140100351040d41c8140f40c010349002d01205258040d4590001c1c050811a120805d0350340d0b400c80300721195080f400c0980c0c0140402d80b0741012002511242e100c055031580302c030040319030100322305100240c50018084c0c0d403040c4544900800b003007580c000700308800b07040c003 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 298026582 1250 298025332 298025341
    0x20f0303042a09150306140405060a0f0209061603140403110603040602090303070c0f2702220f18062106181104052203050c0a080417160b250b 63
    0xc5540130a100c02c0b207105d420010100c003d10740988103030748a0764028028003025034640e10081d00034000304201e5152540d007072000b5180e40c1c4070b45010341480c64035101d030070100440787d0038058544400b840d21294070710f00401003400001c0151290b03180e41401a1801904c0c0d444514203003005c0e0294140450f05448082484002e014001000104807240c1e21801e100b951317103404080c112180c5078101c8000c0400c40e09022010341d44250300903c8040340c0a00302820100111280903445040c50b406099040100c01d420310102004c045c40d000301c03d840b540100915460007a1080c602c03159022200040c0910ba01d03d40d051201580010000300a211107038140000c151428014a0350101240c90240d4901000201d8054070f5206004100444110040640c0c80a81d81200c00b035018500e8140c0c2e500074621108000781c5000080e1000d8130550607048043b54100030b04e40d280c03450340120f400280a03041c030308010001c2590200d0307007091111010160f0003445420034120107600b5030310080946440303c0c01c11 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 298027832 1250 298026582 298026611
    0x1e0501020702150306032112010806070311090114030703060306060b1209010b150703111501080d0c03050a0e04020403050d200105010f05010c03120504030f020f0303042a09 76
    0x4000e002d20885621035424000301451009000440d180c6426602030100c68203551a0101c2c00012030b41c141d40a149810a04280301d24520401ea000041541c80642030050498050082d0f40100058481e058100b80500e00024400a05030906101049000020509151113504014090b40d0410300901c4926a203031250105a480b0068840c181501b007008aa03e050040c0207660440c200101541d4865008042002c1240d11205088040c00201c2444005c01e880a200702c41602041150300d01c0c8540c0341542040c00e100c80c6824207010418075082c5000025084003d0f0303130040e40d41e80350601c4690840c4020600034407880c2c00c06400c41c13140910403054280e02245003200c0302550360b01d0040411a075050203080c1d0b4070a00a0700a101d852000910240d44594a0b40e040b45000b880d04400f018600b031041300c1125015101a000121582c4203510401d40400103030340e96507601c000841c510301e0030380c580f510385442110281c1c0b00214000410801502c1c8610f900000c0c107000c502c1000844803c0307050 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 298029082 1250 298027832 298027837
    0x9040c05040609061407030807181211060a02060109181a0a1404080f13170a0501050106050a020c040906020f180a05060306011b03030e070f0801050105120a030305041e050102 77
    0x742c9001a15920b4085009803040a04200d42d0030107040d8182441001d81c4c09480900006203280c08000e1601d4407148262131441c4454000c04031184480320840322414030100d07060021100c10f000d01004c105503680954006001c50443e101e0a0b0009198540502007030254200510302400410f2102d115500a55000c41e5035801803049190410550720309c990021341d8600102d40161a1100611007040181c54000c01007003070240c03a407203002420f074980f9405200700030b2600719544140e102c000c0b01801c120b002d11543e809000e050610f5814000786c44030003540d80034511f0000f4022500d078840f1004008880c0c05942e0600c2c00c1007582070b150768881e458031152010115040d41314400d9907800003a07a0400c602100c0c0680c0040c0d480348a5070805600d0319905050803001201056521406800d21280a02611000e0303c1e03920245d00031907142212a03401c0d034006070041c5101c1c034442001404500b000046080040e5414100410b01d83d480b410603235000420700341300c18542801c030400e031020001c040d0300 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 298030332 1250 298029082 298029089
    0x10608060609150303030109020a05071a0912031b1e1909120b06040b2101230f04170405030709140a0b01051b01060b0c0a23060705030601020309040c0504 68
    0xca90b0b825980d90800850802e006a00403901500700704010710032110150024480c0c00110300300586000c0e8070340d481d6880e0792603564184802380e04c00400c1c003102d000c0a1200c034150119081d00c481c00c2d800c040031030442860403001e604000344070008414a020841516441c08100e080da031140d110308040c040c1c461281e280c800c142c0300050148a001c504d502ca801100000c2c10381020042400c0d41d504401d1000a141021030154400005040004500781010400000014020000c5009020000e090445008007964010054210020400440190044650300c07507001160101d81030201c2c00c074030010f07109a4000c9034040c06481c070042603045882c0c01420509440340b00045240e5140343c104800c6466041e800c0340040c5041081c0ea440400c5149281000101d42c03000181603940d80c0703201302040e0300404a070180c0d508000c19607001d1001b1208000c000c00313000c50403001d01d0030382100003d840d050020118800d100002c0041800d0341d20030000c2e03c080a90161040103140440c03140980642c00610 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 298031582 1250 298030332 298030339
    0x60a171006240212090d0807020405161701050907030b061e191701091d060406090209130308060103090609050d02070806060105070503090409020d0b16030f090506060d02120106080606 81
    0x21480014600c0051803101207803400d110740d4202207400042010021441c070050b11f82440c140540b40c0580c1d01da12a10b40030b034094188001c1070314202c05015142e101c00c086031882142658004001e41e271161552543d01030490302d0002540186800000c0d480d0081c801e010280c604480708080c8005458801040c01c40d40808005940c84040801114021000c02c3d40480c0350441000400443c110b42d00b201c0b880c4d43d02c0d940340c3c4900c1c10f00402c03414035004003164141c5905847d44505005c2d0f040100245030050a01c0da082003e8420386e40380a0b12000000d0701090415648080600c00e01402d5400300d00140e80c408203071000e80d50640700096650b20f0300d011b10001c0313025800c01700d5865801041141c04080c0d002d80510308210151080000500c6d005074266044188180810001520020109d2040b50140f40c0d80800410100c401400c94070030802c801c01403840c12a2a0703000c40d02c001401c942c485800c503403004101d2604e00c0400d14189a00302a52895800c200303010a0b044404035855110b40700a4 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 298032832 1250 298031582 298031639
    0x10b011713020120030d1e0b0312090307120b070f0f200309220e0105060a030803090c06031302010e030304050a17031608090117060a171006 62
    0x3104891a050064400c501045005000c56005500071000c2598400101d0741d00001c4200e03039040310381990301140151103069501c002004010090000102010b95030a208005851006021a47c0c8040700146001904008500180182c0d403c0103c8005003082101c080900341c240e00e421280107a058801301c011441ca0090408444d01c18030400c14034149a948861b0100003869240c1860607035145204003a002c100328864503901c604221403905004840c2e4080b100b0050001c078411aa40c040040300d00c0e034180300c1482456030310f0414031400d4030340101c106590780d140c2d0301a0514040040c0308c42d076008007001c4104405402d072507000c00744650003070302d503030010390506e00c00c240c0c5070700c202e00031568800d1911006200440c4461002c000c400b500b4030841e85003400e482100c01d101c0034191001c4520f00c40c001072343e0340ca9503441013005075464010540f0311000d0070440f000400180c510300800c0d0b6450442411984504070030004c0d10550a00402c0410503291640070441e90703084040f29400303100d10803 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 298034082 1250 298032832 298032857
    0x71b05010809010506031f09050627010e0606040f090f0c09110301032d08040b18010e01021b060708120406110a02030304060b0a0b030f0f15030718110c010b01 70
    0x40c042c0c1031017828010054421000c1c80849074a4800b80750183d80304060782ea040310b00001d01d081060798080c4103071070b01800d034180e41c1e140300801c41c007003030102d221240c7d051184114890100241085d0080c1045401249442c900f903c40d00c01480010006401550140c500f0414000803480400a80c0c10400042c40840310b607400030a007610080c440103000d00c01c49417001907444404100c101d0343c00c02020001c0f003400080d44600030307680c000d9042410300d1a00080d5413103004000d440c0c200c0110000f800c1134101c522860300081c0d181e1000c030700c03021644891082c00365016078421302281c41c203682c800f0b80c6a1b241c905100360720703844400440d01214400d10300b008558104900070b040d20101c1c00799500039071541d03466544e040301a00c00190203641040b0100c1c4089054503044020314445c04070900c2c2d005e40e500c1e048400081280024080900c1c101c10b010094903551000b040301d10a446001000000040c210f80c0c9840080242000c2c041045402280c3c1103426401034102d40d0368508240d0f104000d8205 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 298035332 1250 298034082 298034101
    0xf140102130918030e120102040b0f09040605150d150909080d0c0306030804090207020f04020d020304020a150c11030a080708120726070201090507080115120b0609090102071b050108 80
    0x420303c0c4003401292404142110601d000c6804030b82101d0854005814595182094401d5030080140044881c4d00403c83e80c030f140c2080d20501009000480e81441d1888101c81005124070034130300356400080e2100443d01c03095144484903001801c2045041100070b10505001c001a00100c0170ba40e0050700700280b10003201d11078043c40b015a80c100d201c0c14545440c00e01c0d0000294020791049810001c0f44890b486140d0b80c40c406844c032050251000b50341c0b4a0b0610400445c000c468008000d0380310603600210101e9804001404003980c408c1c40c9001d0505c00d040064505000e5400041001030001000000c201c500d401604c81441d003c2c120f10304e50744903a4025640000800c46a1072038011210020314039054110000e0b8100d81c0d203000000303104070f0340c0d140e490800f20702e03404c0079220f0b079190481c00752074581d444101e000030302c1c0c907100c6551003910a42d20b1a10150001d03082078030070400c600100d61401002e60464031020b03401a001110041000301202e000c0007144502c5002c1101100020004803 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 298036582 1250 298035332 298035371
    0x201061409060d15050708150405010305030f0c0708030a110f010c1e1b0c051212030703090218010306060f1e06120209120a0b130c030f1401021309 65
    0x84000300000c2080d40c45405010700058104000d032a1031951314600303580f490540c031580b4010b00140e59141183c1c580803001c1d607003c2401e2403925010f207240c00010408550007109881403a402c5d0641681e40c1c8086180003072030318003d87c10a60103404001081140d00740c1141e41070003007800c900281d5105404e281034103400c840c1d01407440e01c040360040c602c1e0110300c0030046058040f801e041c10201815074100c0203c0c8601c0c0213020f800c46070070340030312818045442d1845141414090480040c071020441e1615001180030140c80c2c0c0080c15141c008640440d03035044014001ca6520242c0c09000d9a506e080c0b01c40034050398840c03495422080307403011407149008203a905d003c0100b180c442e502c581c98040d084071032030f8550100702000303a424002c0c0c00072079070f5800d803450107009000000e0082d041d00d4105860a03020103012008030410304050740c0c000807800740c2d10b24116500031102c3d130600403440c14080d004510b41404c0700c030154400580c110101c4211a108800d458207402d04100020649002d0400c11 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 298037832 1250 298036582 298036619
    0x70501110303060103050705040e07090806101406030901091e0606050d031d040b0a060804021503011a0d0209040606110606030d170402030c03030301081f1b0c0501200a020106 77
    0x741c10801c000761143d4080e403c4960812040d01d02a45019034512022101050075103c80c000601d2074102040090030402004e604650144d08210886203440182c004002003410703154052400440003468612083d40544c034182c1e00041c9800d052840101c01642c14000702208031003180c5070600204480c108404240140355054881c41c0030400c2205074200c5c030100d40520b40f68800c2d05e0304448082d42c1c0f03417101c90380300500a5444040aa0500e841000b810309140000c1d40d000e1001800100300b0840c41c81a404103c0c1d2194102c9503507200c801c040140a1b214018031b2541060420302e0000c2d606070300c0001000e0446084081c1c400030340b17803401007548540501c060400060511201460151540400c01d40c00920040c1112400c8120340c0c040390950300b0907880b448040d0044805002c0c070100d100703039504589944403000c0000c0b0001c0340721044803515801b03502040180c5440304204001095018040381e400148540386500841e102aa503aa804060400019402d02034001041141c201414510 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 298039082 1250 298037832 298037867
    0x60513030f0813020a090e01050a020f041710020708250503091507051c0815030304120206070c03050c01140909070f090e070c0c050102190b0901110f0903070501 71
    0x41e04084207045540100c00b400f000c00403046200c144006035a40a402002440580b4000c208180c45100150031a5002007494201d14010805040307071010320012107050303604201c401d4518131051200c0c1850000014400140c0700c0c0300044d50410302440001400207250804145808540c1c840ca40b0b0b41501c0c4000c1c4000d02c558403d20240c5250301e010a2084114400c81d048103040501c0d0761100d42c501a18100502001400c03143c15508056014400c1a448490f44007060444084140866540c1c8218803071103034405242c41440b42103641d403c049501445c2c0100000c000562607041181c0c03550400c2e0001130101e98049041142d801107402501c03030320000140003908559500311700365400c52000d078080e0100300358848080b450b158238400140c02030703802d80d5076800401082d01e084d842d44041c1d0f41040307040d5130019003e0a03400b000052040011548121000c1d07441c0c031003c082e03e0240a245c01a065808070118034242d00b8000007000d446c29040440c1250070305a9240700558954a405061030385 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 298040332 1250 298039082 298039097
    0x80114010b09060f2d04030b010e070e04090b07090609050303120402120a03020106060806220b12030c01140f0603030d0b01051207080709060306080304031403120f010306051303 78
    0x60006076409082c03180d030064078003807400c0d050042c108680d80c0142c010341e00003a450903004418480c030044940300440c40000080c509800c6440740c40e9000c0c01489140201d400140004024610816000390b4240700607000b885901100d15200702c001d0300481d82c07400002e0b507140340094580c0c80f9011000480b24003802551030064040e1401648100c014070980e08401004005242801e0800ac4103071070354040d0b400000d100c1d0a00c0c0004003035100140600b031180c509000c00303041540c40320b07001d0042d06220346000590181a000424103035481103614a084c3d000204410790b240b50190000803001c0c52089518205503615840b070f07444018203443d0103030541d10078092403041d160141d10580c06500d050410318104107820000d20001a400c0314a000014000d07030600039801d4229403000c0c042c009500741072100c5412f0240040da240994840a8084605600350540ad007505000f203401001100c00340b80c000780390045004040110a1104a8080e41b0b4130000070301d1120455920000c0c03580c1070b6901c15 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 298041582 1250 298040332 298040339
    0x11e0318030c032a020f150310030c0b070809010e0a090c0f1814060304030912060c020d091a0d060f080a03020d0e0906121507080a1401080a030f02030c1605090108011401 75
    0xc8056400c04e0444e004900026001f501401d050b0240d0f00c548590441803140c90300350304e040340302403815601004a0303070070500910002039258401e9426030035007860050162244100065661030746507020003074141c80d04001074061030303010b0340e84090b60b5101e0b150300c100f0701001e00301c0703d800e50003504c91550221541424000d6a10b0002d0003150814002d250080d0000e0701c03556a4215010101d10843d80c15a0300e04100c140070381c062042805025140c20124181c0d450002c041d0f0b4801260b880001c141e42c3d00142c2c001308920790740d0294001d032060040840d841501c8101d003a0307032402d40c13010950142c401c002c01a0512840b540845a80110113016071135103459070b00a200c2c10240c0e26054a0003400744803000d4008900e9003003100d1050400c0c1e503c1029906189018100701c4048201845c03180640c4c500501c030401c00010031071800c0c1d42c10f180c2044620441c10b012030460081b60308640660281e0301c0815400101c3c0000d81080c0d0348120340c501441e9070303565007050032900010400211034036440c0c01007 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 298042832 1250 298041582 298041589
    0x60b01090e04171b0102191b1101030506030a050f0708060c030115081b0703020a0308130308011a071b060212031501030b0a09020d0f0e0c011e0318030c032a02 70
    0x4101e40103090004d01d185042010f070841c01e83c0c00802c003912100b82c00f071190080316a0301401181091040ca844001e04540e5500d030704c0d0340724038090805810306407600007040442d1010030a11480c2d50b0400e050350800384002c40c845807507003901c1c4284407240c1710b2040417583d541f14036022607040390542c502d92040c20b000c2440075a108000104020000c0c0a041050aa10200d4100818080d8400d50103000915603910703019210b88005800350310203281d2024070900098204a0040c103603044118040f14060510140710070301e20514800a02202c51b040f070020364403002482c2001560410340903250351448110031010700303000440f0040d601e0207001035444031650080d0301400f50030b68054910307c8a10b4a0b0300200007668884130b17100e8030382966080011117600a52048211103a881e030050241a018040000c02c01c0c6141d0f02024042c3c03900c030000c1c00129009130710070f81e01041d8006584079004000d040c003034281c5101074015000314140f8080c5580451a08116499501300000100c240d40c04039002d0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 298044082 1250 298042832 298042837
    0x90f27030504031712010b0901021218030d09030302101b0c0507080f0a020102070e090604020114090919050a0b0102060a09062703020d180902030903090d060b01090e0417 75
    0x203400340720041201101040008140131003144c11020b03425038500f8908100c1c00c1c0d20a0503400228106000e20036214140c1c1c0c04079004203040107840c0096291407840000881000307103d981c10b0340c14840c0300841040c850700309260004890007902501c11410321600c951090b118540c0391302c840039180300307443c00c0c03500c0c01843c130911281d000744102c0e08045e454401841ca17000403c44044e0709580503442d440215039040007040040e142d94620304680341080380e81f040c0d0740c902c0600020305000704111401031051030390040d14110314000745501902c1c100307131700c5258200440703130400181503043c0350001d20702d805240a045000c6406034002d09080d50340449890042155060172101d441c0c64560302c2d420fa0700c081c001c1c40802201034260300800d40789440c02038034244828044000b4011030b440176811841080307003000c2c01c8400318800942e8950311103844030700b14400c880c1882ea00995080422082c02201d60144008060030380b1403408980d11038400f046041011100100384140d007098040e40600d00102 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 298045332 1250 298044082 298044161
    0x70303020c010e0f0616090b0a0c03120203041b050904050607051b070308090103060602070806150103140f04110a080a021912080a030606032309071e090f 68
    0xf481c0c100f8070000fa0500b95104d14000966000505216903e0041e008030308031010310b07080c41c07031803036261104849050244c1d000c040c0c20300604407a60424503010780f000800041400360119580d00d4a86001006031060184041050600c05d0003c56141481208035001700c0c0c20800801d0701d559540b10845855000a41c882c12030510000c9506c0b13200c200700074500180d0700c203c40305070f00d13504a200010b01b1654694020402c641c40381404004003000412420b410910307084c030200d200b00500006030080e154251440307007203138500410000c100c83d0415205004910800510000021200c100141c1075450302540a19811220005005182030307103150300420002d481c460110350342e4082410404003600415070f60110001400c200312030381481524007502e005c0c00c040050b01514556507803001c0c21410341d0200f900401002c502551010002c540090511299902ca540c00d80201d050036020784d840741580362030500300240d0710070400e400780140541c0000585600c42140640e4800ca0249029 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 298046582 1250 298045332 298045357
    0x1804050c0408010c09080f06060a030f1a0a15050910050603090a020d0803071b0b06040504230106030b130b0c0f0d050403030605122a03010f020d09150e0307030302 72
    0x440081e182400f0701404843d14201e844500c17141d480c025002c1c0c10080c1d24604849a41c000008000e100e42d030390b120b0071042d41d800c0700c1c403600f04910364038260414010000d604100e5014500400100b0402d5400008400c4c12a502803441e49654030244041c0800a40d60881d00540010060013142070450146510043c030320200c5003146425004640c4c0824010000d6607a104000200049907811401c2c50024100100b13030f0518270707030041c1c0321741140b40e902414152003943c030742010400f840b038070181d0264400360f21061402c1080e01156103500805a0340710884481d094240000d55150703a00b00c0e080d00541e0806003402e0141d6410304004001e40c0000c95603041c0550a00440281034158411030b80320728403c0e20002201030078181042040413000d803070b0581641c000444a00031117140121800d002d2418003807204840c01c12800280906075a0030340c200c504d40301044001400d10f081d005080c1c1c0c01d004a692040850400c0368907800c0c0c40349140b41503401da004000100c0043d1190740208800aa070b003 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 298047832 1250 298046582 298046587
    0x90b0310270512030c031e040f020d0204020c01050114040e0309150a1404060521150907020a0503120f0c18090402310507023403020303030f1005061804050c 69
    0x1482007896940080e9102c10f00380d05d02000700404080b04030984c2940c80541801c080c1a0304c3d01e681c07154480c43d42c080c8020300462911052008540306c94041d24031034843c11009010039a12404045011a00c58840b0391085082295007000c1e004084111000c000c0c0150481e00f007030003d03154800031648003175070240c00c001c4807000c41d005450313106003c0d0014180e26542c050303480154483e1010b00e0003c0305101c102c038401185c00d00002070480c0950b0000c480040d280305405949501d0180d04103075181c00c0240290100240c0c8040300809a44501e204110720002421241c490112039102030003010000340340510181c14525040c604000e85961161004015003040100a0122030111444148001c90709403400d03e480344d0300c0902c3c016158045241c1c402400c01804880c0c1c21703203c2559a1011424141c4e07141542806880300400010146030050208c0f950380c10080414069204229502d03540804030700c40100351840c1c90811108103010700d52400c48201000c1080000500028140841c4d80804 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 298049082 1250 298047832 298047853
    0x120219081b011e1b08130b130b090906040e0f010c08101e0b0d060504020c1507030c0e0607050f0607020601060f140304200310021206040506090f1906090b03102705 72
    0x82c0d5080d81e02501c1e030582d4648e110700141c0c089a402c0b51203500700704058003081c00407001c103481d0041919404441194080b4a4503540f40c4c0450800e850096081c40c15400c003021009030030b410021060085403948082180c1a907a041507101c2140000d40a031b40c1640d4910301003103090402000f400d6010b0120000054290340d4000040032640140b00c180c510b034000103116800780c601d180c0c6041c1d0141e5581801d000d952400303900285603a10315800d861244001007400f1003444010000b01c081040414111890303401e0034040650742e810244030358000591035517601202c0c00c0c8039440e40b0310080c488207092411500c82d981d58188580700201d1096014811003412a081e9804108600c0100c40f02c1c2d100580c1e0316035080d017610003802c0003000b50340104d040200f07004051300c5825846510801c101d43c0407c07151204044000d0b03110201401c3c000450400344046055a515070200c400301c4011411a5201e0400100c1c84050300c0403c0010700c40303051041d409080d40b0040003658885640700c2c0381501e11540b031 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 298050332 1250 298049082 298049107
    0x80f0105010c120e1e01300e070b0a05070210030b03030a0c02030f2d21090621060f0405040f230709050604060807120219081b011e1b08 60
    0x558280f0102880c140c14401043d541c003d40170030801d40148094a01462044203001f41174803403d040b54108554a54244c0d0a00f071082c4048005410a402c8003a0754401e007402c020410b4000004c16071180c840e85100d060f415000744141b02601c44058050350919001e9603007628118100801a40c041c01194524803e1883c01c2c860070303c1d402040160505000742102200c40f855000e603001521582c400030b1518403d41c0600c2400c40f0004406401035569900d4601146250143d084155090400e01030041c0e40412a100e1440c800c140640b69851091002c40030041520b40640307010f00842182000b480124003480300ea10705034000030451038002d490212a0900e0580c90b5801500c0056071582440703442e00d40f50203420000c007080002000c425051542c607880e00036002c400248a0310074070040fa50000084102c21004107011000c3d507003400c07005661948840e02d100005400140744103051007004040101005203042c1699940e015074911111501480074849015268940140941c0c0403950 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 298051582 1250 298050332 298050349
    0x409061d01050405070501110606092203090810050f060d02010201111815070b0a0c02072402010c0503160c14030a021b0109030b0f060a0f0b0a080f0105010c120e 71
    0x540d2000003402e26181c20041e040104582181d030410104d0b1003441480c1c3d03c00101c1c10740081d8100c80000c40c0d5100c5500050f001c1ca00344c46c20200000450010900703054200006c0411119a403068a00c00d182000d2424103c510490b9030304140b45415012440b0350420b880450380300d910600000a034100c100f00003190540000e20740381011120b00c1d60301c80c2d950600384100a0b2550000340000c1c14111980d5078894201c3c4000d000d01d00265440000f07245651081088000030302404c03000c042105060441c51008030307910003c0c40055800c2c00c040001552150080741c4c03069080380625415810210380403944080506010b481c00907e005040800160501c020310000d459600142400580d4030030440d501100000b000b0705000c0700060420102c4d803900540d903030000e04000100350958950340003500c400d01c19000b13401c42521620000c6003880081c3c005103884185a1910451651b510140301c5c48400c090041c20300040600c0544000030b61410455140c2c004942410803440c20000b0128410a = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 298052832 1250 298051582 298051631
    0x303180204060f03350c25030b16140d020d061401091509090c36050d020a05150f0712030f020a02060c0c0f06010b0904060b0a020705040906 62
    0x800c10707400c02c20400c43c0c201e0020951100d00c24840c410344a009a8030402011801c0c8070f143c410500152600c03501ba402e201034030140c0125254500705424803100c400b16181f15000c203d0740760b0001c00108824101e14251010b0b5080e1590701c00c2e203a155075031a015002e8210041c6240003075000e100d20416144a030140d000a0b045030a4098041281107000410b42c0d0345990150410100403802d4222155100d0314550660740400b9001c80d071300305c0716002210101c1e18000c400d01003605504039844414041442c01300602d5080c41a00001c3e42c403001000041c0441140c020741c0030703400950411140c10a29203075207410105212071410203003008000c00482e404030707008487c0b114003184c03c42042c6416120750720600d02d01d28008c500f480540a0041d40d1200060000e80c0c096402095480c102102000b400c100303140504143c4c1e5855075140b80100b102e4202c0108d5034425070416a022030014142000d413045251542e004055045c80c142c140001811440c00660300251030302d40d070074111000000e181000 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 298054082 1250 298052832 298052849
    0x180201051e0c0a030f1b06051e1302030705030d0507060e07051c0b010b03090316051c170601020f12030c090618090c0f0922110301030506010602030301060507030318020406 76
    0x7103d51900520b40305d091000340b0140444c00c0c1d080002906004600b03d031040d0701030400601604c0d1820740100319244440344084680300b401c02c12403d82480e0f003201c99060b10070390403150742c00e0701c680c01c16486111621600000030024068036001c01c1d140e400055895005500703072005640c41e140450790510040d418150104000a28413040103030151440e07004001c0140140c0c2141400c00c19180c40c0c2c400c5150321507481b20b51464603410712034140040007020010182d154000d61070800d000e020b2420300440503140200840004109500100c0c00d0002e007401c2c1009840142c00700c58262000381c00190070b420005005001c40070480d1217042c0100360100124802c44201d8044404006c507884001700700310b240c0d0f0410b02000d000c1d8503203442651034070320040311140c00322b078083d00c42029503440c030303210510756241004002e44803003100e60700550507240210f06841a40e0303200c070344c2642d0307c0c4020712404000510400c24040400c0c46680002407814030380340c3c0f01544403481d4000400350f078801c0c1c2041a4 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 298055332 1250 298054082 298054093
    0x105130e01081f0c1b020112051305120a08130515070816020a020906011b08030c070314070201021906020d0c0f020708010e03040509091509011509180201051e0c 71
    0x2080c10451010b8507880303034840041c0803101940400a00504070740c060702d0000c03900b4405e803c5c216030040e8105c00d105c0c102050100014079240f6244608100f482500781d0705400317200003804000100504840e0002444e480316900b13601d4080307650b811460842002d50701801000040d0900680084a85d40654032955a10301c803810a01744200892103072005107011355011246502c01a100c0b0440c0030780c842001d09280001070b8480d0720130340c80b10814401c0104400070000410611204403c09080720501942d21403908044190a04075544224100a40541c0c0003485031501002030410081809224620150800c00790040d220300303907103c014403131001c11011603010418076410003101c0014040709000780030300c440b80e00d00d0365141e01c038034090b55024403d40000981030580811030000400d0b101c5000e040a8680705103901d008150a035404c0314403c0305d4a00010f0503420303501498030905414002500d07424001c0d401076402da031001d00e00b20002c00c044903080c240000444c010b0040011080d02620 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 298056582 1250 298055332 298055353
    0x1101020712030c110a14030705150108150c07080d020712083c0603070e040f020f0405071b020a0807030b01090f0507050712030209060a03021201060219020105130e0108 74
    0x400342c5400e00c084904018034071000302e164141c0015400111900110f61b8200002c2c400314072804c501c2150310191051080066904c000400004250304072000300068400005003403858034030701482510b2010003000184942c0380403441d601c00900f00c0d042442d0006260600070340d100c0080c1c5100d1104600416881002c0041ea0181d00d0080b40700700704c3c0404105200039413401c0c50701140b017100980300c068101d1600044c1143e207003000000003510381414000a80d24086c9001d07402014070070307001c900490b42e41000310a02e0400f801041d000d1001030b16500721035040e4400100d00f4200b0000141c0e4403401910300014204400d1108001560007540b40b625a98100242c62090300c1d40711801422043c80c02d0108540680d105099901190780500450f13520160440202d002e805075008855000358001401c1c010300d6099801024252100d4422410036039840400380d8858200a40d010401021252721400661286009209070a440c0d2540c03900d0903201c55801c8078080c426042107500780d00460800 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 298057832 1250 298056582 298056587
    0x17090607200a06110403020607080c0f160605090d08030a0e060c0a1e0201060e01060309030f020601051c051002030c03040309080606030a2003101d012a1101020712 72
    0x40c103510008401c150220300403800401e0391400310780d80150025959610504803450420101c400564000384200c0c0c0b04c411a040c0220309901007420600b6512030900418040000421680c0040d14500b43c11030115141c2541560b0560080e5102684680c40c60644000944840090b501039200c0200006038404600b500624010025042003808441802440780e016030001340f003191340681d129808604000194180d000d0045a0050380007214484000b07d40c1d2580740d44043c0304240a50340300203425484800c140d071104000e00075607401c4490940200b070a4140f89802c986058858000c031410001c0c41d44500d800c0340c0058480628541001061005060340b0900300c45c017801d4030341d0280c003840c01c00c3e00009669503a0143d00038400c886100c0030070051401485030500107603000e8150307520081c07500481801060400000c1030241010409054114414403d4415001e40080395242c105900700408002d84a5080e101c8100004038070103150700d03c2d007800036201048c441c5644d068440101c4402 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 298059082 1250 298057832 298057847
    0x1020a0f0c0510051810020a0b0f040b0601080f06040b12070f06090e09032502030109030c03120c05030a0e0a021302030f06060306030d180f080f071e1517090607 71
    0x8400421006018620601c05c5030071240d05011002c540d820030400c10b2410a80c1000035400c009400300860004100910103040c5950b0b11441c42058660169a110001907641c0c2d00700303440c10601014000c0c00240507041540c130800012800914580d080d031416000c0c1c070315000003a0450300302030f10032940402400c1d404c08904805000c010740031461502d0000a0f46941e400f84901003207940c0d021880000200c04820350460707982d60094000d0010b110745050190451403911002c030002500074040c510003c03103c0c4609002c2400c19620b140c0345031a44a40200135044102e07600c0d22900075200c2c042d00603515000d1004582c0d1300000050785038a000c600452f002c400040c1a02e008030000c2041100316680840c45990750700076810f00000c00e00160707080140c910510f81141040e2040d800c0041400040014080315060244003292070203030319813800036110715080103016100744d4003070f1040c01031081260b6002520200c1d403500e040c94800300605510000c0003030b11507110f0782c0c0028061244d2190302010 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 298060332 1250 298059082 298059109
    0x16030506280503070902250213020703082e030b06060c1603050f01020f03011e0f17061006050406140c010609020703110a0215070311030d061508060102061501020a0f0c05 75
    0xe0071800e10347c010511495540c1ca88040b00c0c0d6a91036011418115500c0c1e0340d0140704030108010840d00c1c6c1c00039240191905a09aa030208000c87d85546502042d2184d6400401441000303c8007034040e1665440343d00300713040900082c0c0e00041c01d20000003018010040c0c410204480d01d45030190528509250781404090803241c035260340100041502c2e8600d490031a8116900303e440c8243c7d04050110b401c0190b81ca41e000601d030b450341c0b4200000c004002c008807615100760304050741c60135150f81c0c5200d50081c155100350300205a09100c100002405085002c0301261400010341c03402052086040c00c5130000d0f00009080d42e03020030400d00b415441800c01c442110798500404400c00641c000480c00d015554552421010000301c08017018070030f40f41e00700c50002d03070022251916074a0f0300d4400546407d01890300c0e54a500c1010180c1d282c82140f5140c000d10060f000781c0403d489911018110120541156056100e0711400c000051201c050300c1c08410300900c141007416091200308a00da200410 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 298061582 1250 298060332 298060349
    0x12020601030305121905090c040605060c0709020903070306090309030b0a0203060a0b0c031210090b010813020d0606032310110f0306030c09040f05010c05031603050628050307 77
    0x100510020f504107003120b030604003038802c1c2c070580e54580704c1c0140490341040038101301034200760501405081c0014101540f510440e0180f1020b83c45000707021090040c0d540480c610f81c080c06003040035412070350003000031640160540707521070340302e850b030f00203440040713108a0005542100800901401c00358013904031403900400e42c0745007040390015900c5003c174001c3c02941c0f0800108000c03e10310070022a4801423944c203403800380f0700c0d0600c0386002000092007503541d85410103280110b0780d0311a0304140d02c504040180600a204143c0a0003146429900708440c125a140004004200d0740e980303a815088915030a0038200d8012051103090a0312070b101803140c80d04002c01c007020b00c1c0641d015a0140c0590890950320fa98850000038603100707030026420b4000b03500e08148002e02c000c1000c0d031580c070788c0103000034403030f80d000382388100e03038501c01281d02d1030b01c2c84403145000900502c01d8021071f070070a03002040c05510483d110603921700c001880d61030310000040303500200001c0c102480480c00808945 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 298062832 1250 298061582 298061593
    0x20606031209090f0a0e0f030913060b22050a150201060608010f031736030c18040c1a07141c0f09030c090203010501080f060f040b010c12020105041202 67
    0x4000c242d04110180500d040013124100003202802250f01c9a14041400011540320100c420801502c903072014880702d018010880552401c0741441c09a001101c048514807880c00e00390100304280400d20011940140203030f440001000c3c0c1d0380e1280307000504000000005203900842002c0e08441055202c13138203100d120401004240c0c50180c61400f100d41008190b500b0b51320f001040d003014400c0421101419a4014084020881300306082041c80121f200d43c0340315030342e818109070340e59821103031580c1d004444001c900d030040c44400300c070f6810a105600700004981c6070f00d0050591f01d00441200241c1c4001300e90b500900c039a60380b545100114040180c000541c0d004448000c0e00c8654070413038103018035a90300d00314803442140181c0c011030f0030201040c2295241e185030340c003a62084c4142c81c0090100c001054131402c100300b049010703180c01441650104007610a00028041e0701907210b040c030544541c4403000c01c03909500140540126400040d441c50b10b071811080e03404c052501030003158480c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 298064082 1250 298062832 298062847
    0x121103011e15030906020903060f19060b0307051810180902030408071b1d0103030e06030610080a0212010e0402030106060219060522050c0f010e0102060f040c03050601060206060312 80
    0x184082c40c4120301e140c50003040e50748603428100040d01c43c4600003078040c1b14000030408010702c10b000c118041e81c400c0041152251030541050240e0b84d66000f140c80300d00c001c1002c108011f0256005040710307044640c0c1e0002029800d00060034181d24665810081a800070114200c0d640100140018200c032190450550a054079503480a0045c14402404442d0b030052000000c5044030300940109001101d00e4003220200002188040c0b00384001c4000c030304003003940e5000c1d00c0c1032402d07039200f044058101c000044804100b02c0f0740617009800c051290b5400c1007074078039802c51091998085e01011040f968181428414142191800d40c0301404542040da0350310001c0842e01720074023805030092000300b05602c0354404040c100da1048070078006403a000881908000e0041a64200c1c20342c1101c800100401d0343c0019190310f003541400c3c500580181e0001108071940070403043d00240103012000c4126180d6442a2070044203801190150340280c2c10401c180c58100404941c90300440c0c0210f042c0240d = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 298065332 1250 298064082 298064099
    0x60303090306020d09050304091b0c0206160311030c0703050f0313090f020d0e0c15030106050a05031825090921180f030515100e0403121103011e 64
    0x200341c00002c04003600020104003010803034104002d8641c0180541f591a5070b82c46da02c200030080307105080c1d50030041c41c5160701034038081c140c0194400c0e0080c0c80c4500c2c1008040904c2d1140660fa13800300c0600542101d01080341c04200064820710b40d4903001442c0080c21818a10300e0040c402000c10030030740c01000303444254084000c0140c220348450f603020030b001620800c076001030300030001800340c82880e04241354a8240c00041c1c07100b9820303007134421400340b140c01c40d402c08941c402405541c0100300300b0000c007240948510011648445100003485034440c035001120304050115810f00e54103407203021300032140b40144080c0001000d15a4082107820384507614808070b100d64a500e0f0205052800a0302c0752580590344100c4024000c408192216071070380716682d1200c400c0d0000355110b200300d11f0480c25400c0c044d0b089602507003002010701c55040c80c00341980d44510f0003d2048040049124080116900500070b01100e01c1100d01d109440c0c2d03050a44d003000302208056039000d1280d42c210101712121 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 298066582 1250 298065332 298065347
    0xb010f0f0605160615030b070e01020613110603160f030204050d03110a0218090c040504020a030b0714130611010b013501030b0105211203040609150504060609060303 73
    0x80c05824080d0301e40000e100301121050f2a1440070346007908064070b203d1101500c01c900010389104400e001e8207a110014102c5030841001d413202e001d46d10101c08505c003080b240e015804490b1040a0350842c0c81e0764000810700e1a003041d43c1801010640d00d040746201c036000004a00007203094a02142413901d00000240060500100a014449070008c03c02e00143c0c10b002e4041c9407a0060303e28641d09071800611180080c1c220b400c24241e015100c034551680c603080c000c8900560b0005d2010f00c00c54211744403042e0540c0007409403c248804003d03610b28505c04140900031b0341d2031291000000a18003800070384140140d044910040c2d1402c0481c07802c50382c2040e444803c003a4802c12078004040300f0700500f244042000a00400346070349400010410031803003801816100203507011080b5402401c024042030b0040503000300310750030070608602000b9840018581c0300e0700030b540c0461459440c0e216030107200f06071040d1501ea140c070b403030401040c0709540c01514020580c000c810040a869918018040ca = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 298067832 1250 298066582 298066589
    0x7050a090b090f25110303090d090f120204020d140703020403020a120b19020408120301080d050712050705190f140f070e04020a030c0605071e0804030303050a060e070c0b010f0f 78
    0x4130400041892010b00c900ca101a003101c41c01c0460340d0f070742048890301c2d55440c42008404d00094440c0e070046902010031440c40202c4581c0900c8182082c0a5030820029402846803021010354800b07002d07000c10074405016016403d16140107984d2411401800b941807003e80110352aa02902c0d444d000240d2090031143e0b114000c0300082d001d0903214180580644119031040203148118105816040d4000005504948541c001c4600c201000f6405641174064445e011300107407518074807000c015004c0c00060034828491400c0e994840c1c50b8406d110f50160a145040d0740c00401c1070103100c00c024550034038240040310750000744170311110311503002ea81c0c83c42400303030034103002292011508540303540b820400619400784024040742d458540013010b581003214140d51440c80c03c83c4082c100c0c6404004200801c0c0c0104209241c1400d52b2001d4001c0c2c103000c0c100311111581d0b4000011851001201240501069911420404401e041c00d000b510700682084005000c07844e070410400310310a04c42801c8 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 298069082 1250 298067832 298067881
    0x303020703090509241005041a0403021504090c11030a110712061415030606090606160302070603110c1b01020a0804080c011b1205090307050a090b090f 67
    0x103610251404540c5008280d014541000c0f211040c040f00c1c0142e14402290000d0400103035500303007503520801c6820b081070700700301000c00d60400080c0a1000d55034010703855441c0301031425241a981c0d41c0440c4a9244101031401855004a004c3c80130046030f0103a801d1885423490b003104801c04c071341c039003035140d110340300070754050002d00242c800c40c000d02440951f00500383c036101d214103a4038030b0800c2c1c00600341c0714528000004001c0006240030f0150b0070f004041c0c1c8005002407440340c2d606018400c000e20040c0c5410740c0840248451408210b60709010f0340726910950103099005d1918a0140a80d00d040d100b0444841003401464050400081d441d0b880d0704010110348018021580140d0a0120b8168044c1440b0340005011800400014004007212003c2c0e072000b59010344080719210461460b40028110644411803140552143c03010f01480c070713402000e03035902d03507614000100903420f5540f00b450381030b40302c000800780d42c40d00e00042c4d64810000980085903140510b0300c00001122511540710 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 298070332 1250 298069082 298069087
    0x803091e010c0f200a0807060516080a12060b0405030303040209130209071809050103120c060f0207030c020405010e09070e0a061512150503030a12150303080a0e0c0607030302 77
    0x36580c4903181041030250400d40c00c40344185a0304041150181003210007601400c44010038000d42060540c034803c03560584050700c1c5460400e00211a5907010b0181802c0c2042c000740000081090500286040e4a09032030300511404503100b107400750707481503201414081d803d020400170381e14048201e81d030099040302c245900d5039900c00880f0444890b028041d40050f919010054801d07080006800307501210113030b40004036652040034050b90002d000041601e01200a0b400040e070007400c1c00d041c2240300f6030000c104840c107c00c0300422030700040c2080d00084d41c5400c5c00c200350706051240070701404100d002100c042c50158601d664584080c0300b020500c910a0700022074071001c55100e60050011019070392814040c44000801030000e400700442e585140490050030360086181e10811100094040c8d810100208001c2d01e0b202156058918441d8807815503016040b00000342902861103511921454248004c0b25001c03902e626200c2c2131245e00c8200c001c40181da8103401e59909030703414500941d = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 298071582 1250 298070332 298070389
    0xc01030b040609140702010b030a1509030e10050405120304030209070f05252f010c0c03050f0d17010303080c03090a12030b0f1503041b0e0903040e01080309 69
    0x40052100d58051840f0740e18010300b21041c1404400c40e5805000164024806400038000705910b5103840e007801491007804103500c0585130244c2d00712080d558003a04020740f03c010058041400d0b81000f000c0580000c1c0001400d1205180001050000c114140029070500b800d690102d01d44140180c072030002d000100026600c010300c0382d012100f07240000058603114a40610502c00050003e0170100c4460500007486410b074500441600440041c400940c079032260780e100103449154101c00103540c80c1a04244c0440403840400c19031884070584002001880e10000000f0302d15034040d446100c071011030303030f00420100b03138405411904081a140050b940362200351140d4506121000e0080100c102c130890070380d640e0741550004202aa00f40c4880f44c600b0f03800c80070007a0306224184a900d8401e414004100071540914001c00142130142d0304441958803101c48a0b18210121038004c1703e644005004d110304024a01c0e024010b0100c00000d5041000f00000620288010110918140b00859440 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 298072832 1250 298071582 298071589
    0x6140726060310200406080703060e060d030e0d080310050108060d050c01050a0c0501140406051302011e1116060f081512101104050406060207150e01090b0406020a060e0c01020c01030b 81
    0x545004d15243c024598880d95580c01400b92103040390020082071900d00d000070094503100001e4841c0c04010030589401a4a13a0b040d40d42041407080c1c503070400c24001003800003c01140045016425155007808001d24081c001807640c5001012507001d01c1842e0485800624009942d0100403800d00f01039445026130796007198a0502d40c00d001e4450f6082240d105021040b004d5440d006a0240c10140102c1d030300e0040341260400388410081c00180c04400a528880460102c42c0d030303180c0246464080c000c4101280303441c000d1b09071242d107001c40400404120749038001c2c1402e5444085420441d001d85404910030740d03280b1640380e0480c041d00c0d0800c0f07000a0f000c401d001c820702c0d51031604410000b6000702103104890b5082405050b00070740ca0701d0340125055000190078811140c42c10b440d0705460301221821607400c44aa440a4140101223002050452007038000d04003400260b8002c010301007050074294250b4a5200c0002c00341d401c40f08041100d0b990108644c01105402c4c240445e0614104020 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 298074082 1250 298072832 298072871
    0x12020118200918010506010315050402030a1103070521041a100306050703090c050405090601060516081b15070905061315020c01080c0310030b0406140726060310 71
    0x1465000504108000c03650f0034121400740c0343c035012402000f4a03910b06005408484160205480d0b40d03111420411052515800071684880502c002240c0400c441d17a00103010782060740d42801280000c01c1141160205a584008511140216005c0c80c10030341c031401c0706d42042c40402102103445100181c810303103210308160005c5034016800c0000f0300c1c15840090040041d060304444e0b030940800300044c10b14041c01041d020390042c0002d4103413a407802109031080e50243c4410810000d44400c02c0001c11007007005450542030280d008400300416a50702c2c0d0806100d09120f201e1b180000b81400300c001c0e88081c009050326020341e0625a5100b186405040c1059903511941041a10b030001015440c1d01198034190000c081e00d44054503111041d482132940000c17200d581182d01602c20030004a685030500b20b402500070740c00090028500c00030380318401c00498420340032542c08003d40303243e404210b005212034080501003c0e86070a24000090b2500201e010900041b0b80781e0102981c0301c2c808410 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 298075332 1250 298074082 298074143
    0x718140106050d140103140d0512060d15060b0a0306091b030b030c030f030a03140f13020f060706050405060603190b090f0f0a050717030712230712020118 68
    0x25030904d40d42c0e403490b05030700228a88007400714500410418000395070080741a01d13038480c03002840c5d5105541d00c005200410050b02c0c1c003990a18510290b01456280324407852000d01080944a9514000e0440103416101554050b0714102d1a218211a4200e49450020030301411482c003c924405582c0000b450803603030035041607240c003d201219040e28400801403960036241d4405101d52502d00c0c3e214040c001c0c003254102e00004100d00003500c0b08106041a2062910050103040c5003c1c1640210ba91768010100485460743d4420500081c01403c001403944032400700c0007802218914000e038070340c0c40441c40e40108440c0c951004904807040a010314103110040c803003182d90600c0c54403c000e41d21441400180c90a000d020301c003040000201c030200002c0844900218502a030680d9620161800d0b00412400c1003658440242d5115078101c074000782100c0321007a00d0f00c0305046d0402c20302410f07a4815010941e1b1400034a8580a43d81c0c4820281d11900a60100c0d103070041181803101103400d129 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 298076582 1250 298075332 298075361
    0x50f060304120338192c010b130b03060112020c07080f0303070816090506072d0302070b071a070203090d0b040b100b0f0f040510020718140106050d 65
    0x1180d030407001d810000780d00042982004070103691810701003170099040303240613006250860039109204049031800d1a0f051800703410070082100303038000d030105071042e401e8020b1b1004440010304680032000c40d24156000d000c003101003d00c0d40c240680042d203000312140118a555030007240ca0701c0c0c40e540034071003c0003c02074072042c2c83c00c103da4114031a449030f04c200e52000100d540d0002050102510395404498194291144107002e4101402c015598001c01800c8a071400010307092014107240d10383c002c2500d140e04600000a1000d460064104041c0c0e42010207440340612000307001c41d01031134002248151016070345c0030a03219082c08a05502c00c200c0d00940101440c0c03804010009c00e50007051045000d40010405611441011010f146161051a91565050007078203840f0b03007080300400503100c80106aa2800b0390300c50100f0440c01d9030031701804c0035802c0520b04110701c00510f411a0480c6072510340821000151141112214006020f581e04101c8041038500e07040c1da085c0e1003034041d5160170 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 298077832 1250 298076582 298076621
    0xe010909020a090c0f1d01080604180611030603010c0201020f0f0a020f030a200f100506030c0901081b060c190303061e09061d13050c1018050f0603041203 68
    0x2d4050030718291007000e1000100c1c4940c1740024120018076a041c0706c83c0513036448000d5150042080007500321001d043c0032211125601000141075446004200d014043d8015143d02d841000c250031219014100e0040d6401040301d06020744155044440d00d02c026440b1030744800c0c9043c4101d10b418a0302000004922000072140003a580004802c49911005150a4443c44403004401e4560040034200c0e1040e5000c0003030124090001e801c0b03254088400b60881d25562040c00c00113404a07400c3c1d000e4819604590388004080c0d01101c009010118280c6945181c4442c900a5a650f0714152004010085c001c7d5801410140f19402800c01032410082c550341820b400411408601e5080c80b030380000515249000502c0d6500d014100020300384850460996540c1101007091014000c0301168a0b002e00390a410352590b07a0100320101482c2d55039400a0307142241d5806450b54501c0d040144a2850381034074136055507561044170b45c0541c1c020741c5151950307241c042c243d0190928a81c0c0740b1801101 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 298079082 1250 298077832 298077851
    0x7030212011e17030d060b040b0d0509010b1008040c05010309020d0605070e041d060106021906110c060c0403030e010e0a03060f15060e011b0b07050711061803060f010e010909020a09 80
    0x4085d10600621500403c07899644480f14180b603c224800c10180400501c66680c4050050340032a6000c08880004181554510009400001000c02c104007245d9103505110501040e654807601400003800c0070024403003103030005203050140c0f02c401003107245c0701c80c00600014490a500c1072040400740c03081c41008808000c00404098a008410130761045100000d5400e2000403103040c0c182c100f903c1d084020030240c071040007030704d401d003800042c0490400c01c1c1e40394104104001c52090b002401102e0b1100d0444c5070003001d22840f40110b604114515812500e41e46d41d0720080000c036a40180d0010300c2d00c1e000035141010705050807920420b010440d10024415800c01d8000d1560482641d844180058209038200ba221035940043c0056400c680002e403128094002006568040c00700c1107500403c10b80001c02e140d0000014003004420100d2900e03140c00c04100464008044540090456040c030280e107420704030500c12040394a84842140040d5101c0205d54070141440c0d60382404407168 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 298080332 1250 298079082 298079129
    0x6022817090123041202060405030726060103030e06030a0b090709090c0c050a1b0308070c1a18011412251404140604050d050703030807030212011e 65
    0x1c9140503601240d801e18884025007819985079402c040a16245400c3c07909051a0743c0c420340104204a8200d0001c020204040c0d504000c10002408021281311640c15545409d0b0040442c1d400e004449034025401400040d81100904a00c0082640c109480b5651005001b001d000300c840b070341d0341080c41d40003401016540200204150385842906100d00c00000c102110b026410340c1010781141c2025000300c00140302551049001006d43d80c51600558403520782001c568040d400490b500540e000007001140c0400080d40180201921400c1c1840903e020410a12640c0c117100c41c1003140c5014000404120241603034042401c0f10145a85441d003004502840c2c42500c0038400e420842c240b01c0d2603154810200000388200c882074050400b0726180b030214046c6941c40310964000d00600001c150364032140b200213a081c3c000d0000b08100c40c0385040140c044480030f03001e8020180104007202e0601c004d003003410f04440d10481c0f280c0303040c042c40344044101643e0344c01140041c1040036062600d5403 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 298081582 1250 298080332 298080337
    0xa05092d0405061c02060c0c030d0c05060a090f0b0a0219020c030c0d0203030406030c021c08151912080c0d0c1a07090b0d11031614030106022817 64
    0x210107a40800080e2140001c203d49120325064042c15201c00300036030001410a603015001007081355040f100c8150f04000041e05002c0341e0050040062201c0702044180f010412409400060282d81001800c401e9101d581c105090000d01a0100c5004004160740151560444802c544800040f5042000003840203450350010301c501842841000c20622141c030f041c840c41c1c2c0b2000e0b0b004000790300d030902c5c10388242c0140660000700c0e0b095024880f410382c100c0f40d00c0c0500d51400503d50760341d04500d10b0304a142c450b83c41030500003d40145001560440c3d8110005c001809603078003a01d046810300424903104000c0d02c1031116010076400350704440340e00c0c0d40e004030079010103602c140b900000d0319042c6614061580380444000002558040080140c00b40039001480e40041e050801700e502202003c03508041e9000362100110031229440504000d90b01410f60100480d000c0082c52955140c01e034001e580307080301a0504440004005c1c000525501c54002665482d400b00480f1010307182008201d0b81d54 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 298082832 1250 298081582 298081669
    0x914130f0209120114060d05010b1003020c060a11041a040506040f0f08030307050712020c0904080a090f031101031d0f062d042a1701060e010b0a0509 66
    0x158040e50648100c0f501c1030194000340700f07132544800260b0b511801044411101d0200c180d6041d541d0300311506403034842030122101c044040c0c5002d45d440c41260826490100d0003020780c1402da14012084401a44403022101103130300c070f001042c44145021404031550300c101e5008641c0b140c0c1c0040d001980c0403811880c9011600c0460751100710540d01c8a081b601c034441100c2e804e00042c0200035020001342c214144810f03030b010b40d204030b8992284034004141d1304c00c4242d50a4542d24008240607041f0b541c4510200c01400300c000700090305a20310342c0e070100740d00d018a9903030f418103132140483c01040070102030144018254204a41e030a0307401c07044194a0784001e80d0342518422000ca911080f0140c40003101014203007142a80584d5580d07612000301c4000419803107142002400035541c42145100b8030381c4081c12004101049205501140508442085d07101310340c0e0740a141c0c0108141050201038840300f290a040c12a941c0c5846070014605060050345802045684d540800b0301341410190032848 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 298084082 1250 298082832 298082839
    0x90607060c020106061701050603070e09040605061002160b0a11030d0504020316080d120f090b0f130503030a0b04020405040204030f140102040b0702060d0603050105160305160914130f0209 83
    0x715407940000c441b600500b040014183c01780100400803828080004c2d6401180c41c41d0407200b0010403400601d1181d010749041c0c9009456000344001c0f454880344284403500f40b030009003c900f003c00280c5d82600c04512030100d42e5440032491303110316800b800104c83e0702c4c10b454050360768070101e014084000340020383c0c00740d000e0310070341aa1001c50700522031088190b07069030000382441050103038100c0e907408010a4040c10282c44a050000891b0303071303015111540344103a0844050f403501c001c81c02c524000c0240300301d2036240c55503400004502d000c012280c101d8070050b004102c090203074001c14040c1c4103a501c503682107440002c0c00024000010b02a840040c03185c1c03c90f100c841e0546440d14280d000c0d03805003c500010420040006140c0a002003140c0980444042141603607070712400c2c210b03002240c0b50b00760b4a01900c500c1201c207501d440f45035403156502c0b2440e21b02e0301031200004e104603a6800f540480e00d40c001134104c000d035203440701070560381300850050220001021040c80a9040b26042030301 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 298085332 1250 298084082 298084091
    0x430f0606080102040f030209131e02040f1802150c0607050a030e0f0615150a030507110f0c0f01030e12040824040308100b030c210f0402060a0302090607060c0201 71
    0x4a2001c180204c80c1100d10542e03812000500350b80030004c0d80c2c0000341001308942d4030000a43c0006810b1030b0302c951354144032807452007981018011300080e16525200c200394940703003000342514904840703248002c0d80c1e016641d4030440c0c6220703005601180314028540c0c0d40d40c419601004813640d40000105210250f41d581800b031900c60940c0c05a441c480359883c4a0140c00010000d10f581244801c200140080201401030560149000f201d4951000e0342a00019480780e042124060300000810800f03013017040103005422004066540300d06c0f0004905204496996142c80181c1c8a03801421941a01804ac1c0c4d40c000c05035408900c25521070310484030a1701507403600e490500c824440b40d42d11590410b020740c0b10f685d942c4d5800c482d0150700800601c54101c004001048116109018611030004100d81c660f581c42d200d00f1407003032090b4840c9880c103410300e032604101c2c0301c8101c40041908a541510303055180c468108090303004e40614101141c002c41c01051a1062202c1a044416203807001e030002c21 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 298086582 1250 298085332 298085339
    0x5061003110102030316080907090e0c0301110c0d0305060103091203060e16050409050903070503040e1005120c1302190e12010b01020d1214040305090a0803430f0606 73
    0x241c40380022103806c402c00700201c400c40f030024042e40100c1c0d40709890380700380e9218607100c80c0d0b08801c59031200d00b01e6405a11003003004582d0308092054050350340e6407100941c109580324040f40e95900080c0010410540c89101260b0186d000ea000041c1041d40328122210041c40e041000b80184018416110803e9103000800e20801c198a0040c4c241010f56807034628144c00d29406101410300030f0040301302403004000c40c101150052010344041c003070783c040010300c03801d040c69440c000c400760ba00010b100351001c1003044400080081d082e01c8420302610a055443c01c004083c2b4003d024036203e00c8405491a0380c074080d401d0344090860b19440089901d00550080c00380424201c400b4030301e0311030250340300c3c2c151200407a0092000c680c4080c0c8559001c50b80e01212101d0a03421801920110041040424200103502d4410b2101c009802d2400041d400c1c440d210301c030005403c0c02480c0804007000e030700003011b18006184081c0e19804001c03001d01d09580c0c06901d0000c104200b4918243d502d02d1030a04e020 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 298087832 1250 298086582 298086587
    0x906140f04050702031608090405010b030709090236031f180f021504150f020d0e0303030c0c0106050405090a05060709030302101d0604120e0a1a0f07050610031101 72
    0x21070180885074000d501b400c02c0b28404040c0034020700320a40788800248140c00d1241c0d182e0040601910038102c443d5202e0812540c0a0b210b40c215401c10500e503030043c800c400300d0800040340d5100341034060f58402c0b007400800071042240d01d586d0b82096010f015905018106060100b6146081a5111020081c11000c1c101814400365200c400400030f440504404025241c0301010880030000c0031507192401d5503a0283c880c400d10304907000b001003852040080d881d00d0701030002180c1342100c0d0525640320f80380b060000b503c07032000a255018142e0301003800d5028203025440b0304080c080142041100381040c4103500d50b6400100e0342259584161790010341d52500c6001d00e601103950540040c0300d80c01c003103003c042c0070785640c6420500a4544188a404c800c400b002454011350180c107480200045013030008003a03001c41c11081e406199500c0c0c04209000316070b407030884a0302c1d010100b242c644031074030b00c5241984a2100302411a20600f014003848625482129040303a00c5005000c41041450005 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 298089082 1250 298087832 298087841
    0xe090f060105030601120203130b090a03092319030c0f060f0c03171501021b010203070f062301090606090b030f0603010e0d0203031905090a0807020a0906140f04 71
    0x500458001252055000b080a5600200141009984c02201031810400c0b03070403c0b80c000103a42c2945560714248518450380542284181000e022114056207001d0108031862044030054440454500703524412030f1640080164000c00b0340000704540301881c003468805002c1503d407200c1005000900315690040942200d00c0d688980125031507640c000c3d10100c00c038034401d800b8413524031030f442c5501500b00f001034402d00e440e034820031400040c0d82c002841d1909100844103a049606c0312680d50382e0b000030a8801417580702c220001000040d2500e80040c001445401c940882d0306010442001d851035182410383d103252108120090303072600c0407900c54406100d250081141007011561a401c0100c149506c0900034001017001413010f01814603022921031464016000882171080b041c04c1200301034035440950300213201c01e00b0440385d11030f110714800c1d9004100010000d010f41c11900c5800d0f080780104035003c020031406030389111000031400341c001080d200e010f00d2101c610003458180324 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 298090332 1250 298089082 298089091
    0x2061b010213080c1309020121020307120b010e0909030c12030403030c030902060a050c1e0307050105060a05060a051e0301140405070c08041e0302030a211b030f050d0f0b010e09 78
    0x706040c503407448000100512100354288d041000102402c00d49942805840d40c80c80e140701d0340141c0d24a0032980062580d5880800035000500b0300d10055116030b40403540e0105000700f1a83c03210781f901e07040010b62452040a4150407140981d520200f410040311010310320840c0251000d003d803240c03412041301280c1c00c1c4000207601042c00c0c41441c48603031040b00a8810f2481e41383c212024404208514451800320281140d11a030001a98000300300d02800358580200f000d45a801e0700b03074140030008100e402543d03852010000c4c082541389141c5a50980c0318441c8a505d004c0316581d584070b400070010041aa06040c0c0134608000125501c148541c16050003260450a6141024203140c510b00702090405803401c080021403001102696040c413100e03040b18400e082c2e00cac0c60405030303841d841500040c41107880306100e840030764040c01001c0c5034111074100b64986804a120800c1c40720079940c50103142c41884885203400ca030b04020500b154400380030303008241c9408002601c02410001007200465 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 298091582 1250 298090332 298090339
    0x302010e07082a011b08270901030f151e0507080708060f010909140f18250e04030305070e040204060e04050a061e03030e09090604030c02061b010213080c 68
    0x15401d00003c43d600c1452400060145408030b08841102006202400000400d40e1520b400041079122841e00d4a080803a440920144016081c401c000040c0714540500c0003078020394140090130208015a00c8030807194040c01c800300a0031101449500c0045079401c03a240c2c0f100d10709004252645c7c000d42e01e042c40b4500395500c6a41c03030b580d000c090105469002c4056030610200c0280483c2c030016134002e8240850900d8104009440e00550b1107018010252040c11a0800300388015076000f00416079514050300c3d000f81200307106c4099941c0b400550140c0c001901084280d0500c81015455048540035a50a80d910b69150700d4180800080b4411807061402055030801c0500180c106034001a5000c0a000c0000400d2546e60034400a44000b991840840b460b17107480620405810401e64106002d0907a030190741446d1400d441540e036030000d04040c00f88550400460115a0303880c0440e00c0d00020081c2c032403048400f5210490103904010101b401c4d0b10294100801d070284e00041c1e100400c900103 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 298092832 1250 298091582 298091623
    0xd0b0105070221010f0e010b0324010e040510020703030b03060f1303030f0f0204060513060315090b0d0215041a03042402160f26041a0d06030302010e0708 68
    0x241a0340483c000c1c000000155520b4501c030401030541d500c100ea0480c5040c2d07001007004014202010305110303803882d4801402075000152844001e40e100113906480c2c40d00c0901e01e41d40c9071810183e16209041d00c881051900024030b00040591580050034411016411101140c4646607482604201102c55101140c005650540480d00c6a00607204800314a48001030004079490804180d900c2508690080759000030440001d04030060420000c05035490104981100c58404411000c1140302c1c0300c0042d03484440b5019559500d044092803264010904421a00d0005408606030454440e10031090003440f02292103c01d260101c0707102e42c0d485502000810300303d241200041040140032401284e00f40000740041044604512103140120304010140c0024074207490031080011901c00c030b460208100078910903403039003a24203072208184c036803d5040441200000746d0280343c4940d4122410050000705054040d8006207002007404191030034507450320070090b80c4012000c01d1046221a030f = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 298094082 1250 298092832 298092859
    0x303281704290402060d0207140a0f020901081207030c2a090c09140d05070b0307020303010306050711070302010815060409020702150f1905040e10080d0c08040312051303080d0b01050702 82
    0x507031f0b0050905a10500d00e40030005015400d8034a09014804101c891b02590090102549003142003680103080341001059500f0301d20840c030005015008005007801550fa0300c00301001f000ca24039110406680701b88902c0c01c0c407911008120480148245100140703855107440c0524410640842900d65090a0444c0070381c080051001c095410304d004e0b212801800d10114910349004000c3d406403031954015600d0b9411070034694121740003e4040790078481e5000c0000d81a1f140441c5031002c0320380909200115948002c0a099030703040320b034105a0301c0a000180802c880d20280d001d810414000c0c0c07468650044080c500d8041e82c4202031348400c03482d40034407400e9050681d2001801c2003d21500e40b05081c03d41d02d421420244005688415042d000802c09104201c4104040c0f10b222103640f42c04003607424951500c03000d5110301c0c00058540001448042241c501600880703e00001109414440c2d0b0742e00e0400c00c6854118000001e0303c5402d00c5110a965885002640c1c0c203550010b182d58841300d070 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 298095332 1250 298094082 298094107
    0xb03030f0f030a090507060e03100b0f040504030e030304080f060115050301090b01021c050901020d0f0f081302030f0d09050a0f090b04090b1501020c030328170429040206 75
    0x100501c1451095103a112000c00110b06204901c007d124648819070401d85e01000c05082981c0c078030301310203040d00e4031403000c0c2c00d9529005403880c0200e00365070019803612942800c5469038401c890f141c3d010710002400060380300e00000c50300341208899040e100b8a07600e6a2006181000000a0200048007400140821a60fa03407200020303110500481d4548004001c1e0501c2d11462032070410003152000c103500f11a540c0520070644191428030b08002d503036641e000080c00e05091000c0b84002c1014250028154020a607001ca001640040856610900c07103c903590303881ca40c1281250010300e042030000742ca0701b03203d18104180c4c0e14600902c0925818142120001c2c441c20045c6c5a1240d00c4420704004210758013141409000d000503145106113684001916151a08581da4001c1e8010049038581394030ad503245c070001c904120481c042a4003082d000303c8414400c0d405a9601d40840b400f48400c122085240740c14003040c680800a480d021450401340600307041320083d41081c41085844500345 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 298096582 1250 298095332 298095337
    0xa14010e0616031b08040203060a0c122f03010f0b091806030c22061d0402090903131e050103090c062f06041403030106020d0c060212190b03030f0f 65
    0x2c0e601d03000540321480481021100d02a41c5900081003d030030901081d41014400a544010b01c80c0c1c0034014a011000000d0544154030403000c0b56995444070000348140c0f135040700d8002c4400164100400c0740030040b42007954800e204459401d050010b0019220005400340d80500780300800f49200c8200242040c030710868000c082ea42d150080800c0015242d55041403850818086204801c90200c041c1460040314001d82090240e0003280e0071580310901d242c048150301079410303500600140c4808017954135502036040c441903078141051021661680c60810414281c42440902c4960b940e10300040d000c81c1d280180103400d12104110503c41280200965051009210611a00c40391603200c030b4041254000d000e81020307040032081c48180b24404c10504080503103880a1495545401406540c90300041021424030142030300f10810b0207425410748555030034440140026142040703640c05071040c040341d010449898840d070300e065030900106036183c1011038406d8030302d410014080b030b4100b074 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 298097832 1250 298096582 298096621
    0x118060305100b1602030c010c0b040206070609140d0e090103051e0f010c02160f050a0603051b0c0d20070902030901110c031b0c1509210a14010e06 65
    0x8400b0001c00030300c01c0080c41c020070044000d9000000210700030b03c101814440c0c5119514100501030340340101040c40e12160542182d8100c0f829507803003843d40742c81c0d4082c00ca1603030082c2c2400744064002005010102e002903036481c0c0b5503150305004400f40e04000d0810828000070389158851014142c070b030140803096180742c2c1c110000300c60982611201507402c0d40d4503c808480140c0140c03000c419440004ca00903005000415081c200e96414080440c0220505100710000c01d40c5500118012800711020b15400f01c2a040c501c50781d40050315040c99403051550552000515801030120300911205880030100071520041c004280c03a240c0070340080d4001600c10340445d5601c040e05050008a50014002501c4050145444001070540801050700701d1140385181c0e0044180030341c9503540c10b001c0b105000070f40001c440d1901554004601c0c811040301c04918180d5204442e820b841c00b002612844061003030181640410404001e00d0036104080700b9007002c1d922100104012001020309510032 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 298099082 1250 298097832 298097851
    0xc020607170f040e0a0b03030f0f0d0612050607030c050a2601030b011a0a0e010c06020c0106140301150e040b090f0d1e1d04110405030a050c0f0118060305 68
    0x201c02121203209590b42c0b0400c18a0b485032400a410040000e442c1034059100c45440000c210705400b202c0840d80f83c0c4522460010700000000f01e03460a64024025206541e082d540c04000954403100384e200d031014055400e8901d44a02d00010394414440e01511303812540039600d041c1000103000091365800c00c81d125400d298078001044070105000c0341d0459000310b000d10b00c0c0007801d5242602c090b00040c24040301e24210f1a0800c009206141c010400200300d500070301c0c040c0e010b0645401c02000900648140b80229420490f0004180d15089084a00814120020008001b81d2500c180d400c202c00c0c480c00c040c0614150010300070424420540340d1080540d001d54506080b4030b50082d05003004450b010010541c01c5012441d0b01c000c00366050a01d00702ca00700081d41605031540014840700d100d00c1a41719640742c0c0d03c00030300a0041001e0b200109005400c03200d4041462038046d481e0040001d03000d0160151002c180c100350302c01d00d03003810006407800038107040900b0b0007002c4000e0302c401050000b0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 298100332 1250 298099082 298099103
    0xb2d010512090606010e010206100e07030605030d090603060603021608090f090406060618030b16021006060206150301050403050403030f0219030c06050c0c0c04021b12041d0103030c020607 83
    0x428441141d40a100350420000b030300861a04400140190107088081c1b0f0442d8050401c20140c0d110050300300d429194040304903006070703548080840c06040c0c2c0e5000941c050190480408025401507510f80550313a803a05c09105154071050105c00b00c0c0903545500604000d0400742e140815644002040b074100042c0840c145507010388007085203100181c40455895a41c0c003820096980e100e1440c001c800d00c07060452900628580b02e00c9902034001d00170884480e174030340003d800c950007044100c04181d008881031044a54415011b505c03075504540448083d4000030313216040e0716061081500c83c65140e00c07130782c0c1805d045407400c48025007500104410740c8110034004c400201c10100480003148660394410245401d468040d00b0b0340c00103007010074030120600c9180c504070320120f46c1c00c0104009480041e10703401aa04003084040039200004098020010a0355a400e8514000d100340d07180408285101a030b03048086d941c00100744070180c00680e10301103540051400400070000c49008604121 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 298101582 1250 298100332 298100347
    0xf08150f0a1a210c091c060e030405040b04020406170c16210207060e0d0305070b0906010f0b0705030306040f0906050a0203100e0f040b040c08010f060501030b2d0105 73
    0x21181000404548001d88010540864000f039002c4400c2e501d108a1a0300c8009081c0074501c003071a03014243c0600e106000d004c11440352607511503612000c0540042c014400301c00c440480540782c2c0d129002d96030045051460300030b8903040c20700807a0100e031038a40d9119046812906600b02c07651002e000300000c40401c21803103000341521036501c0c078001d02a08010072416100c40350048001024040c0030290740100b00200001504072240422070201034804403059412464122000d11501c0c80003007582400c10305001401c41e0004009040e0740d1070111080d80b0382c2d2520b2240c0f080e40100140181103910800000b10780f8102900b221814040c2c5100100d50b0403015650482a503004492164129602000700000d900a024688000f0000300301c4001203030404900d0441215401403014043c114070034086010400c0401d000802401500001c201da4030444110348082d03d1240b040c64000317030409030880001d10708050741c165075010802c03000e16140509408060083e0020b0a000d05018040c000e42c0e = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 298102832 1250 298101582 298101599
    0x70f050c0d0512150907080c0702090f040b0c18040209180405150a180627050303190209030c010f031b050c0d090b070b06030c060d0c0f08150f0a 64
    0x1e80307041c401c2e110180c95000b211034400344203500400e8030b84211361108210700300391564802c3c1d83d040021807500d528076030750b40000c0509501c01c010f00203401590750030030090000c110390526030142d0721448085602e0745400c0850081401030200c0482c1c4000801002140c5160550052807040c8000c2c1001c0f513414242c00040c10422811141510690800040c100d4222290010954000d00d03124080101b018541200f4061041c070b0b80004041c0d0740d907070130002c0d0114031001004199040302e14039070242d00700c545840d984039007040e2003150140316405180c07840e090300342c02615544540035004102000c80400111414001d81e02c0c440107041ea107078956042051413020000c0c82444a0b1110350795038801100092420300b03c0e0715101e003000320b01031082c08401c2100342110b04040e04101000d0054481d07200083c100760039107211031340c071610009031403a1010716034000c12500d000c82e460f24291041c00700c8064902020848440c041414034400b5200c10b0314024000303644001c000342100e01000e8845a84 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 298104082 1250 298102832 298102843
    0xd0302030a0e06041503090204090206070c08240412120204090204030203190c230306131208040201020d0507031b140f0d050f030a0e010f020d150e070f050c 69
    0x1500140c1002901208050300100021503240058800e6450586083c01510020401e07032640d00426889401c8901035613503d4110310389480d00205039035a0740c0400d24005103100304c548035025942c01468000001d04044c4403926800c1e040b100c0d02c00c00b160340ea03540d403180712a0410707419106001c0080780114220007248050000b9028031000142e449065004051406807410301e40022940c0c0d070001c000001c0d070001ca014045412042240043e190b48103045a284400081843c0c0c16205903800c02c10081c50f2156001a102d000300c610010316003140380308032009001160080c0c0983e12409030311009601c640010310f00c09000e0701d000201404c00c1d01c1486100c1c0745035142030381c01c007080c0b101c0410850740a000c29088244910020402d2200028014116014018109007080d4010001409140c025003100811600941c001c000c503240c4d40d00382c04029048003280784003481c03030290054841e48040b142c1c01c1c10785940613500c0c042583d178100201c804001c07403000031080000510585800031401c008 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 298105332 1250 298104082 298104109
    0x50a030c14010e1b09091005100b0307030f1109010212030a09050a0b0106020105011706040602090a08010504260405030a140a020907020123010303051206011b0c030209090a0209150f 80
    0xe0184e2215004014031a8100c5880540c4500c41c00300c1800001d6100145000c0d803062000404545941c5082d00487e404045a02405c42041c0c00010000550340c15072285291a82c0e140040081c400500c002040e24040c0451030f90250713010030703030040030b0301090700c05941e00455440004c690a4001d5460f030382040d416641c00c40e0544038402c0103010854081c0103441c050308103840c00852902090340c406544030700c00380c800303000310758001111400d0340c840f46c480d0b20141480700000c3c4400d080610348958801e0b076440d145085401a03a00b452140c001403011a0100c0c0e0004000348000045da48840009a144800340c0465116052801d0016200c1c0b2001c0e078403d00b03440d000000c192082106960f0760701001805211401c034403000500002e07400030180c1b0032141c4034110906480d5541c6005132030000e0700e0402851641588004c036401c0080d1040f0b4801903e01c00d03a004c60f0152582c5540300c0c0d031011100700080d0b03c9040c900018003030315280a0700200c2000010f01c2940b51403810000f040c0142034060 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 298106582 1250 298105332 298105361
    0x40504140906070c17031023100306060203070215160f0303050601090621060f09090c0909020d0b0405150c0c010b01080603030315130e0c100c050a030c1401 69
    0x81009404042031007915844640ca00740400703013440c140d075000c00031219903560700080c85000c0003203146100d003858024041d040700048584610020171740070707405d0018101d0080c81a40707003c541c41c0b140d51003805039000b05c0e4145d4000b0b6040c02d0320b50b401c100d0000f4002507040c2c41d4400030b010311203c2035442d002c10f10400740514403488040c01d190400400fa40c50040401c1d05100d440d900420095074402c00b0300080201c05a401c0c00c80084414010b00900055031007842c101400200c0460340700941d51010f42030921032100100a00e81e1006541e0607a010044040d41c400c3c21030310301401143c0002c0c0e441d035000e81328105454444485009818601c1000c0e61610141d69000c00d124009403400d119200090350b0034203010031180b134130f60000390796480000d000c071304c0c0d54080c0c86004005454080c516006060502c000380300000b00c480906994080c0004070718030aa240c070104280c03031401010140d01c086d4001001d0018060140c03002e9414800910040f14108200a6040f05240080c8649c3c0e50405105 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 298107832 1250 298106582 298106621
    0x6031618090b0a020403021806100e031603080912010e070306020702030f0706120b0609090604020904090803011715011a0711090a0504020306010519141f03020c06130f0303050408040504 82
    0x140140300e285400324400b03d10b08c000080900c401a5100c404d81540c8480d140ba110000111030300c046030808520060302004800903090101c20041c9203805407544080c1660040d40480461944c00e087e11603a4401800503000641c0910100e050398000f0b199040c006812209880b0714032408924045c2182e100d42d0010300b80308c200170710828960003410004007089411609203c184e00c0000c007296806400c0a110390b50000c1c0407031854490303401035084950091015600c2c0d695a8690610600020f00e644020380560001c03052841d007005001c0d070680349248d08442880d844071444840d6940600002e40e100c0c1ca4414004100341e0781c0e820b1551207841440c0021689080510616180c502c040c2c10151144010503074045500707501044400442e04881c5403420302c03054000c00b240204218003004003110600c0189080c1d02c41e05900104004207005084420399603540301034261040d104003008000142d44000040441e2080e044190001e00a090031441c140d80d840008003220390900f00c0c0701e03aa01d0b69 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 298109082 1250 298107832 298107839
    0x200312040f2408070e040b12031908010b030129030a09021302040506121801051303020706090b07030f020115080c04061406190c08120f06031618090b0a0204 69
    0x90031815092042da10715400b20707003440c032a000c2c000c15401045a4100480c15a10304c41640d0386801182c00c00602810078070104089031204c0d5125071010040d011042c0105408868251140d2030b264100c13844118081d0a590901c1c8a003001c4036070051404105503080c2c1c0e130342502d0308154401503008202e403c40c00103074019980305120000c5141440c680707519205000c01c0142e40c440000301c52004c5480c10320300c8019a10081c0030703a811411a00e40008030340c03800d1308001801403200c00905460380250216032499070741d2070341150588554040c05007604014044038001174041c481100745681e460001149455841c1902190400e45512455040d88244526011401c0c544610340182072801003444040c0034403400324031144940011406010801b20040e41d60034400d88071421001d501c100c1984c0d44140110007840c4a044c02c0e01d00e401d850400002140d4949400200700e5451011400003180b140d20340080201004a4101c2e1503510b5030b150000300000640e09000a403042030078010043c2c0b103608 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 298110332 1250 298109082 298109099
    0x1e0218090313060e01030f05190e0a051002120a020712050304030c12050319021303032f03030709060c0308040b1b030103050303071b0309051909020d05010801051003200312040f 78
    0x301000ca0a4100d46030400f8840181c09d0140a074219651912022420020009180345400d50007840175020f40900754041d580b1140355002401d03a880c83d900d00e0509903c0d103a01c442c0491141d00801084e54180c0c4450f0030041c1e00a40242d60706c140641800310303a2107216200d102c1407004001d0543c0000b500081000040c07901604141821118070341c00718100200f035030200581000034007010b010b00141040000711851100c1d8444000060308555100c0e00104555069517904162a2140840c9183c9408030301107211310320100c0e45e29003590343c6441c16252138450841010b03007c1d2482c175500c5405030310b2a5041c04c2d0a8021802184200c0c0156928a0300010080002c03074400c0b4100000c504203a48200801c0e44404200e09a402c1110500000f007040ca0310165403030310a074400701c640c0e070012a8110b85484550f02950480d81c8402c024402541c4d0405002c1d10000309000040c201360568074040c1a100d9400880300c1d00907000340c02ca400302000050030700420741255111542070a49034809002210 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 298111582 1250 298110332 298110341
    0x3020616051c02300a0203040602060c0702240903010207210f05180627010e3a02040501030f172503020106051302071e0218090313060e0103 62
    0x980710b07101c200c1541100c68000e440c1c0003165081d00e0400c101544001c540139140c1512561200080c81440d81c5180c01c9002a4598120b80701d804054000e03500042e03d208004022220700660080c0044015002884003101c001c035105030381c2c2c5080c0700610480c4000e440900c0103001c4280038026246142071410420003400100d4100b84040044400139410030740e40010a803825114005160040302c0b1030000492000d01441d40309a0164080450504c121704030040680140f541c00c4e40d848848a902d50240085070310f014904500b080700d480320034449601e0032620680c00980c10301a02ca07200c0010340005054420a030011f0f0340e0f0408101030701003080032a90042c001b04100b42c3c00c150408000c6030510404240d260b102c0c501c0700b8070a000d03810805200303500910140000803d140d2001d48801d0388100250442002104c140803e03812201c241d80c00707031080307100f2280d0050030741009110400034000c070324001500350f803003030700c014001d07200e80749a054610b4000c0c001c140e03210040008108001810744 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 298112832 1250 298111582 298111603
    0x90f12020904030f0c051e0d0f1b02030703080309030c150f0604110d051602010b0118211a0a0b09060312030c0c01140103030311130911040302061605 66
    0x410429a910040e01d440c00310641c403a406003407200010038480c00c2640c1810007010f00503e54001d000143c48401179132455400c0d2282880d00301d52070f40ca6541d1080d60b010070b000614601042c1c0d01d20035892584042648842403600c0502590340140d42c035502c50406402c1a54001200c0d040410301c441c41c083c0c100000b51700403c0c3c5040082042c10581901c101c1d00343c000d480c42d8041c076281d0355001d1510510808586842040910030441c510703000f40812132203044076207001c0055007052180d214640c4910f810b000c501006100e03100c1c0c03261800f000100c1200c000c803400c41c2d4180007148900d01180e10f00104e0240c00c07944010781c04052a283c01c09a0441e205508001d110350381d00d505010803514000b07410304942d000c2d049103540d030382c850030304035015070060842c50310056003002020380c0c1c124509404241240c0c402e480900132401840d00d0740095000e1000001d410b085444010050342e8020780080c1703c608201001203180a80302e40200300700da40280c00302401c80748040d2031700c8104201000500ea03c0b = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 298114082 1250 298112832 298112849
    0x120c03030d0f0c080708040f0f0f06050106021605090f10051009050306100e04110f12010603050c0d1e0f02090c13090c12021308060412170c03040206130305060106090f 74
    0xa841d005e0303806403002030040e001420952640c03061074104402e02c0506805030f03030010f4184c45014481c0c90200301038a000d004050040c05000a03002c080c80c0f400d40c004003540d00c01410300209a4404000e920008001402141c07100080704000800f42c0303c800410f810380085568001d0040d04100600d40f4024014105007007079140650f0801040001080980e00250b2024110404102072000100b2405207440c24581c846e04442c00c0050b842c0d015806402220701c00d5080c3d42c08003008108001040440301070150070146000c042180d0740070050a44c1074240d20995001e50320506079004101c5c0d0300012254525946070004400b010411080300150041030414001d10800e483d4550017850214040c84c0d0540a03078020904e003000e1040c100c00c12000d4000c0a0840306646414188559124403114500001c01c0c0442c1e04c00311068941c190b441d100d05c0803e92458910303201c0340d0910a031907104440145403400c4510022000031001e001041c000c081c05d82d9070104107030034500c4449040c0b1150744a450f0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 298115332 1250 298114082 298114097
    0x5011d07090e03030c0f16060531021f0210150501080a0902031b0402160f0209070201020a1d0d200102190b010504050c0c07060309121b02120c03030d0f0c 68
    0x42083d505d004540702c0d9520240b0850f2640c1d40c2030300100b00c2900d01000280854140b00412421503000074106403a42c07403ca00900d03810055208007690003505450294100681c1d480b4210b80864000182c0c404080c0e0344105c9103c00310f80c6c40441d01f1162521003404244603124010001580d1080181c1d4001c9511031b8200300c1ca50302079001a5440f6181f8142450324409842d10061603500c80d415110003046200689803040c07a6450203214140751400103c1c81416081c0205491502c144251031512580c0e881e4000054420303480116511450842c00d0f81c0881c9a01c80603000070440d42c03518540c1080c4400700c600d0303041c0d004006030810078244165542030b040c0402600215074003a401604440040d140001c15407038081080580d8402c4609441080c0b10303240002030761a41c19070141020b070b4095040f58660344a480e00855010118440790340800c0451520400503141c01d128243c0b4039000c07241183c1c5d03201090f07400b00e41190000310f20b1003406030ba210561281079100b40218440e0200611b0540d0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 298116582 1250 298115332 298115341
    0xb011e08150f0310021e0301030f0803040609050a0308010501020d050f0306060307020120121501120f1821080129090402030f06040615020c0d05011d07090e0303 71
    0x414040d40284100981e90300096000c0c0c041e00d0316003009402c0480601035840c90013400c0340301c501a501050300424a00b52002901700d0482801003039034181d0741d100494a0485410703440f082542e030000b9200b602c0103035441550000107101084a03003400c51280c2c460324000c2d0b24100c000b900304001c01e04048280203041080d00302c50301c1520100c030707840942110116220b031541201280145443d518110a00c00046620310084128001801e180d940716111821a80d8400f618a24502c003403800c2039000c40c042c0000802540300310303089142180c4450304000703551200c407061016406241b00341981c011900d002d0b41d01c2803810060520301c3d546040c1c103024a40d5450180000320b2040d01e0864160b03000406c243c0c1c0038451303449204403801007000510a43d101e0400c0c03024515003450540300b562044d4038050b800983d510034001c2c0022032a040c4c1c0c016120f2505000d050191541e100c403001ca4442d542c400e00506101020380c148203813109400c009000040c01c02d95030344116121112880c04540c01402040b = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 298117832 1250 298116582 298116587
    0x3011406060d0509030d0c050d1b0c0807210c020f030105040b130c15080a0b10050405221b021006080601061409090108300702040c1407060b011e 64
    0x440c00740b80c2001c0d00040981d18915424114011440241ca040d403c2c03d04800c1d8156110020300400945000d042003601e0a0034540d440400400b0421000304020a40000100f132410002c1c04401c1c1c025440204031003e104000004645000d40c802c003c500c01110000945c1030915200b10607081c00c0c1c000708401d0070252200e101c0240c1c02400501d0038100d1100600802101c10481002040c400c00001c030f00ca5018140901250f00031641070340c01510707041c9480c40031b1400c101c030343d00007282c2030300d40e42c6ca06410b0106000300705040e00620b09030080b54036040103021419204180c0d0700c112850340f0307a45815400354000d042c02c51035042c10282d0b5051202c10f0103ca41d01044450448101c0d0904a500103244013039144240105086140d02c00924000086c40d40783c0807819000910b20100d41198548440c5103a292150ba40c020740380c5240c106026800060900d42e00007001d4094a0400000da44507100a42080b0380c0301c079004031410b17a100e0325a8142540c00240ca101c094013080600782e000c3d9000d5500 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 298119082 1250 298117832 298117837
    0x6140a0c1b060c051204050705131b030209060c120d110310050d06060e040308010807060302120103080706060506040311090f091c181d06030307020d030309050c0a0e04020301140606 80
    0x10745602d03541c1c1500f500890007002150392902014040b24605d00e400d003031841e01e6055500c2030b80c0c01410381c80106040b4001510544070b0b1200088118040030100e404110000c2d080300c41c178641c008400b0800700c11001410040501c2c00341904122690300c421511000c000d85d550704810a02d40c00050082c8030704e00384580c0c81d03902a5102030751685220389035820104068603040d8000b040100020044c00249580a5041d50584e05580110f231422503640804500300c0c8501d002d02890024150018000074521b40d004186c40c070b00a82010961540301d40004101307a00580c801c0350212220b00005445050980010760f00040d48100c0700504d20386040080c0d185d001c261081280b03a010b2608043c42280a403290762240c0054a2040d20202e403144904810110241a80203914a2100008032145000000c580c012540544146815641e51383c0036000341c440550102c5540c014910741441c240c0317800d03004e80000c285904c030172000760a00740185400c443c5983d1140c0b508100c92010041261950000c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 298120332 1250 298119082 298119137
    0x613090209011806121118011a0903070f06050316080403090b0d0912030b0307090507050406051b061603050901141b0d050723191b06140a0c 62
    0x40003d042d071411891400802c3c9981001002c40300ba180740c1c1013403000d00c0c0b044a40900080e0b908650b5501c850130400309020b1309115908541d100c0811039030f9000810806011505c6016080b520720715203e007205481040140c102100007040481088404040e24440700810900b60420283d40d00b00342c0c5004100e18200d014501c00040300080991070310500790f10000440e904649443c2e4a010b450200030041c03d0341540c5588603106400010403880c1440c45414000c100c5078448603d01447c220307041d58103800240c071041000500a120102c491424480c15102e0110480c8071116440a0803002c0d04441000c0d00d07544a5030314103035220205900c28000c442e0010032020b151000c251a8041e15405272141c2c1c000103100500b01000d101c140c40e0802c0f1030400894120180d04d005c8540508172588900821401820003444290002521805211000110590b6012800e040900c540303c000c2a2600901c50041404010003040410300d4944908021100c061070a440d8103c400c3c1445010403070000c4 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 298121582 1250 298120332 298120349
    0x1e03120c051201060504061202040807030b060102070812030f010b0307120b130906050603190b190b0d0506160507030e10020a0b010801020c24070e030c0d0b061309020901 75
    0x2246810080c020025542e8001c8403a512000c07541c0c4a5800801300d402a1207804c002c11000303092507680914500036142550703100401444034500d507031a42c0201d8000501454158000c9020120b0356200910035820306a02481080351b036400c0603130000180311016403012900403424030502030f015500c05007843c060b806002011901812600c002171311444810032000c000c500d890810700400000f6041070b80b01d6031048044c3d4031084031280c1c01c0f541e082d2000f00020401c408040019664850010b0b08441c880b14600002030580000302c086103900c4812030082d20280d00003410440400310750b41184455039007a00d8114205282aa409800382800e11460307407007441600c800e000e0752031081001840250700324002d8940d039690389503454000e40c01860401c00703600a651162180c200b017804819140d404c1c400346605107a0301d61000300c40317040844079600d5050080d0f02c02d40403295581400d180c00c442c0100d580d0400ea04281042081074038a04103542c1803a41054081d50141e52900d10302411102900b = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 298122832 1250 298121582 298121591
    0xa020c1302041d0910060b0d1808030408093a060e01050705070308010603091e0201170a02090918030f0c03040807090603020103140108070b0c0f030a020a1e0312 71
    0x200303045001e03008581061002100100718084040780070035200d03000340d0714681510b0106081500c480103483d018040c0b2481240200005415609154001501c071454078900c1c1d14680c1440d9100b40d120390007900d040e1104900802d03403001d14038100c0c0d1000d1000410020b4503031290545003c5000e0303c410601c612920040c1103024074240251508040c4840205200801481c50308150160041c2c000810680000d0903a90020529a02a1141e60020394015144889904850f2150114480b1001d400c0f4100401518014600890580c0c600d0042c441401c0240e141e410100c1031000c5403000030103060900030b0741c2d1003000d80c10030b0200488220a120300c501c00d548140c81484145036210380d9005040c4d920941c50001600c0505034820300c140da200343c3c0d00b400404500d0703902800b0440c007809111107a42200d41c08206c0307103080c10014803841140505407090006610034440c1190010324202000d6000008602c0400504103d840c0b1110340702c111481c0700c81c50f01e4800500c0e1140c11310070010b01c1da42c2c5 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 298124082 1250 298122832 298122859
    0x1207050102070c1e061d13090605240a05060304030c0c17030322030207050103020c151501020601080d08010e1b0304050c030f0102090904080a030605060403060903020d03020a020c 79
    0xa40448111a82042c244428540c2e1591a507036103c2824000d4032803c2c0c4404c4000c68190700c03d01055001900c05201901d9070a1454108650820182c07007180c000c030358414118001480b00e00400307204044045080b00340d09604e418440d502c80180600034455944180280000e50710f002c01c0c1c07a000b41c0c0601c2c08541d60921450130150901464010320148412070045500c4500b000000398842c1d02051a50401c075001208884c56240620b6401005a00b29450a101d0355120764080d1040300d580343e00300c42004094202100c0c00020660340800381041c42c008020807540c04015090050620703c1c002c104070342003800010030802c410b001e898040025800860f65407031030000c02900180341c5408441da42d08040c98841d40d94030714680428040d000b19030046500003010301c2561054800640b203811556140c1c0d52312580c5603c508245000c4c150f030342c0e201096035180e00000d04051803151100040349003180c140a858024131039002001c150040055014107035010078041c08201d0191071146000b100d = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 298125332 1250 298124082 298124093
    0x807020d0203070e240102101e1a040b03060403090312051e1308070501092105030f0409060b090a090506041b020109170a080612030d05010f05090907081207 69
    0x400029602d48a50140401c42926801420340102d0a00d001040d09544103110703001d44204840d8000e0241c0c2003401e1041072004c4a400455104500c007918401301c40b00d040c11071045a80c0d48208205d080000c601083c194101403049244580040b8014281c6242c169030040003007006000007400300c007242420401c0319000701c0035103034000ca484c03204441121031400b4502268029404d002040c801d8a07200243d200070215090040c1c4906039540c020142c03c000d802d2121074541c0500301c03401440c1c2c10602012032028001b60444006510746c0594551514900200340e8000c4d400a1241c26810000a00da5035038a550840403038044040214550390364a0020f0006e100aa0050200c11074480c0d01c110100e5043d401111014480d04196508004000c0e10003654000c402080e008220003101280d0140350010301c2810700407540c0100c92802d90f40d00c0301724040c0c41c02a400710400780d4054a082c0091300d400f4040c80e0f880300d00d440040c41514078004190382d40d0600c4081d03e2052400000da91070a008 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 298126582 1250 298125332 298125349
    0x150d030908030409270b0a02071e051e010501080a1122331a0c0708031306050c060402091e2e0e0402060f120709050102010b0616080702 60
    0x819000b0b8a807125660101c0302c014080305080c8001c0a91210060015442480c0e4002c1d840c80d00240c1410845d0b0344c0302c40c0100290700031502642c0302c01c2c164184c8110120742c010019400c600c40d4000d41101c1502c801b0b1404480303881800052164109001403005820001d003130b42c2e240b90070484c41440c2c050b401000c1307400b141c0140214000c0810580244184011640003501d6420034001c0c510150085031b514040c5147c0c14444c0002c55202d90075040102d0032021290402c000303286002585420b160b10040c91030215641d1000e640c94001003040450f0765881079001d00180402d003011458030032048501071f15008000c00c000e2148030180003040c83d0f0762050b18800841d013030301180300d0101c4c180540b000750850b907840151030484a1007900441d1612103a4100d404403180c8942a83d56519503908120442d0071240400e4803100040c010350010b5040074410703500507507444c0c44001600342031000081c2591301c0d010699000e40010064980c10080f00c41038101020340280602d40c84503010301c001b60966 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 298127832 1250 298126582 298126589
    0x3030203071e09050906010302070206030109020c07120c0806060a03080a0f050409020f04080c180a0209011209061401090c1d030a020406030803100801060f06080604090c0b12010e150d0309 83
    0x855214980d5603500c0d42043c09842960000c45644a00b9a81e9200460907403141090083d00032805000410850031181c0142c83d00f000ca0b1020b55802545450b240100d540043e2800c1e5035840c0000d004024109050005580001c42990049000c3d403c64848400c01e200300148181081750360710400c45450300c00e400791009040d500f4415981c41032107920f2400d20342c0050140c9041805000c8600c42d880c9402d20026821908046880d8400c0c1e0700c008051000390000c404103414407008400c1211180224424403444910402c000a000d40070000e207078524042c160030000744146041010a10720780c1200c18032410b03120794000140602811800b03c0e00782101410000c0d00070741080c0001c010412100003440c41070150020b1260500d40d00c03c131141c20b8802a22519111010b4541c041c48131610070170b2003d40c4800c3c05030000c00c00f52400d68918010310056442519900004600312000140841c0c42a0051480541c0c0409500340303c5101d0a00090840c40c45210740c40100000c003c042c09215802c004 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 298129082 1250 298127832 298127867
    0x150f0c05070834182c15190b030309060d021b0c0105090402180d03050301091821020f1209010e0913020f040e031818130303020307 58
    0x1c0076541c8000643d511454100c0203800005040b400c00d4680e600700403e6409040c41e801102c2d0702d8500305403655540c0040000707a481a8982c400104101e1880c0700d040c6080d04000d075a00c03181c1413042486803e00c440191410310541c1c0404c1441404800406004000300746c001c40080e1101d24030002a05d14031540e00c165401210110b000340c540c00c00d82c5d024254042d2502020506d20310700b80fa08544400102c50b40d1404200280074201c00f0b800c20350701070404807201c4000000050b81c5c1c04001441180c6809046000500000040c80202400d0299031031082c0c040300d2820941c0e03076070b07500c0301c100d00d80040801c0403003c0e50406218100d882044003500650500341958403612408034a66044d6200e03140407401300e105070b41a0317126410440b03c114840d4805101e41d401c4010f051307007001408d070072040d02650300548448501c46038844c1800241401c0c40c4c600c60441c00e10900006111500c12000ca42190008010082010038041060544403507640740c58016903960365070070280c13050096800006013 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 298130332 1250 298129082 298129093
    0x4020906093301020606030703050304030b07030209030a06091b0b090d0602070b1806070921080d0608031201080d020a060c090323010e0d0c231501030b0105010504150f0c05 76
    0x420324000c0c910081580003e03805e50342556a52070900d95181000e00c0000d010b03a10403c410004984618505600300e90b06140251030b19801d60b000914011034444181c400301e0380c0e9200740d001c00100c013086c104120800c810110455150004038051800341c45616401210111546000c108aa50450780c00720f5000b8458002414034054072080c02a20001c464014030820340818401ca004a592600704e60405080d4501c101d210182c40d000c1503500b240c101d481c84c000f40102c22803208903016800103030501d8001951a440480c9000d41002810ba21401381c40e04090815240702d9030100d0f088003240c1c1c00c003070b01080010600400b1203054055a001400305c807209009038071003000c4c49000407180c51007a03000380450503201c1c4c1e81ca0348901c0c4124031600402c00b00d2800d0740001d0780405075107510f010315003841380c3c03607840c00801d1031f01302152801c1100341500050010720070000300302242805040286021404c007810000c0e092403c60011100d0020302280724100380c02c40d440340240c0c0c80c1e00740d8001e082e9023 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 298131582 1250 298130332 298130401
    0x70206160f05010b0910150e090108030a0e0f011b1703010b1c0b1f02030705010218030706020703080a030b040b10020105091902090c031009061e0e0402090609 70
    0x50721684403001252294240ba440c0809450310f0400940540390942d00340400c1c0e442c0c041a5201400c8442298050040e100748a10b030f19603884221138024121840519030b54446034600030500c007010841b2902c145402e00690380c1590307024102624101501c425500c0341d007083d0420000b4609806241421711400000114071001140040d09004d01d42c0400d401919031462180c000f582c0040c400f090300011141c40c5e40300308424280e002d199504081c010360345054080d807035403070981c0d00c51a42803480c0065001b501c2090b05040016038000e00481c4060302649003141d995200d2031290079080820181c86d408403291981e02c035400110f07195001045900700c0340040030082e010f00780c122040d11141c06140418001208a00c4000e0201a030007001c0442070355480c10740015641000d00340e140130741080000030480d80301b40c1c0724034000741c4101a00c10078010006102c00c0002c00d1a41c111144040c100401e010068403507081d03490700070701c048850307280d16940c081f0301c40c003d01d200010701c2c81c42e0190544060f = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 298132832 1250 298131582 298131593
    0xe0f011104090501174308070e0702060718080a0302070e15090105060304140703080d0c0e1e0303160303020903010c081902070615090f0b0316090207020616 69
    0xc0044440c12031003800030b40e907104000440c501195104810039000030703008521030400c16060000503255070b021b100c0c10f1080c100c60001070982c1c446005102c559200814070154104000f11802024210390203511450280b200075107410300988074005011f044ca18006d600002c007014040500458011109507100b9420002e580b0f680074811081e40c40240001b04468210041c621941d1a2024000c9205c2e40d103071409109903984000c01c1070b2050305171851401c3c2e8920051104030019400b4913003003a00c3c0c2c0801000c030741c01c4510007012501405100c942c490002e495600c03a51900c1583c292901d446140700201090035441640d130352081c6034808695039401c154050340941541c90099008000d5880441401d6840c01001d40e0400040c01403a82c5840050002c1d800902c03d60f0720444000c6802c2c40c2d9030340ca6400410301034001402c282c1d265162442c5411051046c1c24588000b10010168001e0b05003a00841492074060b80b40101e400003003c07030a644880e030440742e400402400d1041c00700090b0408 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 298134082 1250 298132832 298132837
    0x12120c020c010f02071a070c030c080604030e09011a030a060b0a05040915141516080309010b04060b0306060a021204031a07031514010c230c09010308030a0e0f0111 72
    0x4150100300d4181070f035140984001822010b440886d0400c480c011018148000d403a005004100c1c0d0320480c2100102c0000c480d00b24030390040920100800f100c3c2801e04c1d01901550b07038040d03464001c104500c010850a01780c1050f0121808003840d4040d41c98075410700c004080d1049412050600740002100000d2541c0035005000301c4001c03030030810000070f1200300b007402c2000612580d0300240060141140c0380c900112600714080465243e14680400507811a00c050765115064840fa0804400c100000e05c0c02e01482e105440115401c00080d0300301014070300c2d40e000181072203004440100740140614000c000c003c14451024514548130369492420001d201c5408041501d00c0300d41c1808500507601070300a0a8004100200c180080f500781a0004a0f540c07003103540d5410061007120140c045902c0b280400030390054801c0c860000358840520620f800600b841c0303039001e804188010000f10703019809894003c2c0c0c501034082156008007c81ea031406c0720005499034103510b00007404c80100b0b2003000 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 298135332 1250 298134082 298134103
    0x603030f020f060c03060f130c030b0108090616081008010e0c10020d0e0105160f0303090c08030f03040209130516140a03120305101205010204180c090312120c02 71
    0x86a91000c00400346503165103013650b4030520020240085103092030700d03400024005d14007905046218021030a40000d440b001d26020011a0b0740304911031855174402c0c611940421440010036103411310106c60300310051909019000c0100e504042040c800104404034000c100080090120700400f022258907100030f0074070144501c0038144040182c900100700e1408140b1603443c0c1004030425140156520303409036509010300c001e41c0d41003500158100c00c084003940d00980d00014888090f1a04112050194200c40c8459001f800784802045003030049950055041e0350300ca0258407480180481441d002d50010814000d030102803000c4041e072040c880071101c0c00c260700b04d88a000d050a100003008d0320b00029203100c035410480d03018070340690485a0400c442c0340032001ca40c2c0d9209618658070b110700d10704481594000804101c00d180d43e426451a1003c5070008000d01d01c002d04020f0030b25441448000c2040300c4e1030b5110700d50b007805448101c1c0a1810907806000208003204000d488003074204 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 298136582 1250 298135332 298135337
    0x513050a140105101214090102030610091a0d020c0f1c0f09030609050f031c05060612010509070201020706090c0e1003080f0c070f0e04022110021b010603030f 70
    0x819828001ca0400038120b070009132a6140044003208220b81c04a00c940c007040b5115120760848400030380c07500e072081c4605003035800161a0b0038407008202c4003400140030710f000c00c14040c0f03060000a800c03105200e00380c0b114001140da51940b462400c00603004909142c1c501c0c0c0202d0820b845207400101c3c0ea920440442c0404000e102c08401c42941c810610004d81000264005024000280e181d402100120b004000f00c6050103c103218092460b40304402540c0300c12070340c2d00b80c03405000640c09029000312044030f400c3c0c140042100001d1020070144074141c424441c500200d01d005000391304552159400090500c8403015505001d50500854401c210f2825450800510303a103800a8800c015241c2c4120160301d0f14007408001c2007290040d0310605105d00031048002103540381c5501400007000b290300c2e84012807600b4010800151684601a00310602d168400c1e160040042918009680070040068482d201220030411821001304826419868003801100f4141c004a403100020101d5 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 298137832 1250 298136582 298136591
    0x81914030915011205100507050903010c020705040c110c1c06061d01060c03022a03060405250609090c03020f03190509030702010503060d0503070f060c0f1704020f0103060513050a 79
    0x213580b41c0c2a8207180540240646d0841645258254200d802031b6030001c00c1d51601e076040c01d4050002900310349950201c0c201590150000308640e0400740542a00074103a810104026101a48241e0b101c2d0442982c451181c1da440c3c401e44110902c62440460f401d4100404010103a29480000c0e0008410300c00310344000004d500014860f0300c01c00b41f0307002a03a41a40138003540d6880c0c030040f000d012210b2240e00107008900d0740c185070644042200034400c1e8020f000921511031040310300d03aa990030840f0020088801a03400f4010a5003281c8240f00301c07004030000054a48442d00218028060821200701c0b03188004107102d04040306411114407190300810400c090307252103c0d842d030340b4400c15000030701007542271000401c46d00e0250040c9191600900c01e603407810382141d0b50241c1d0104068021031b01c660b5210710b035110b120b0340310406ca0034a441605054a4106a1580d4407091348030080c8000d22421520128020741d91294206600a200141140101382500500a40a01011a402c03a01c103031a1 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 298139082 1250 298137832 298137839
    0x120a05040302120a0e041d03070f06051303140307020c0d0602090405010b0412020405060a05040e030403140d080414101b030510030804151701030b01050f040908191403091501 77
    0x30042103460a139815207138003100042c4034083c440034081c3c1001030265001c00c20740d2a44030381c00510050082c5032207030b0b000a00340000c07481d080049840282c8102d80d0742100303003501c5001982160081380b9445008400d0790322584d40030340492900810f21807241d0401824010755040092580140550050131a0188000d81e00c0f0303022101c850056200f0309115803052000d00c00036050a500554001c800a00515074560315103021400380c50148880715426400003400300284040f00c1c08a05c800054507018080d028011000101041070240001c0c0c0924200050040c81d03d0b410060340e204c00c040f144d4240f1851180b140c1244904003240d0320000801e040c0400100e28030a107034005010b40c0d5000c1c81080c1450b0810341c1a18101c07000c81924030078480701080b40750301d036074040c0c10780ba001b14070030020034400350b04007030510024101c4000305038000e0341000c0240c000560300340305840b0f42e40b80d60340c103040c04195280e00441e0040b500c0c01105ca0060000420b005401001040c00a8a20b0105003066030603681c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 298140332 1250 298139082 298139113
    0x507050319150b0303030c0705071511100605010c0b0621100b0d1218030605240405060d03080603071205070918050604030e060d0f0b09160c02090c120a05040302 71
    0x1000b03080d0b81d13040c4c10805c005000c0403000c00183c1002402201129501d50301c425082d41003c91500c80d010100e100c41040d00d903038101c00c00400071b50344c42100e0240586450500080c01201558100400c50b81d10640059180e4031000d015180100d480c01e203404401a014003070f00d81380e0700c0c8081ca0b030903054100210800c00d8181940ca43e0000e69000c0c04110071081d821004454a480d20001401000086003001011414500406000d112001200d044440d500320064079200700a11a050007079081800700120781c0ea600302c4001030381d905410104c55664904000030306058083d080784420310f20004040c0b083c807000103403c3c000c0c2d40401c1c00402c529016159600203140004000400d513601c20000100000d1003846039490300013000c0c1105050510741c48000080d1340c054810000320030758401000d020303480e100d000e040c2c00102d20814450040c450340c8004002c44da80000290080c084080801c000c541d840046614055801c3e241c0c070041c0c00e03c1c09219002d40070681b415401440303000c0c0702c0d5070047d9 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 298141582 1250 298140332 298140341
    0x1206090106021b0909070f0906051003061d0601020304120311011103060a06050a0311040602010507031a060d1d0f1c02060705030a051003060e0a060f1a0904050705031915 75
    0x40d025541c1c070001030082030130400c0480c070085c8956030302d0140020000301070f04503140c050040d2400850100b1b8190410040c00302e4882c14001810400d0309000d401c0260385a08102101d10340b0b0750540e0809035958400c0180c3c40c500c51036100003114213001429106156006140300c00342d0b80560000d100f00801c103045da0030300380002d44441d9031040d007000c4c0401c0482e01800c010618115603040c04550650825040c50b901d4010358003250241c2d44174400c10101c15818490705da9042d8403d00003100c0021400042040340c001d04105403105a9070b801400062881c1c000441340080c0903a0403940f4940000801a07140c540c0603140e039903020440c1100307604072400808c0c0140b00307190507030703400c3d05542c2e841f19a035028000c05041160581c1004c034000c400304020f0700405490f0600c000043c03080d0150f43c0740c604e003110307000e121608c042443e20a440c0d100c540c029000e02c02c1448100c07400312035074840c0c0c2042418410f40758003141d03040c452080c1c803003241050120010340c01409100c4103841b2080c80d079060003d65 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 298142832 1250 298141582 298141603
    0x6080717030f070516091a0910290c01020705073015062702070f060b12070e0411180f1308030a0203010f0b0705070306180503120609010602 62
    0xa070800d00c400d41060003120040c0030750034000c408076a400701c0484039078280136045801c02680f46d512000c01c10010700c41401e454062140c242c500b0032140c0f40141540c0c6200c51180502c00b03820f011003035600201704d400162021048100b040c1e1f40c1d83e501324031890394001d5100c6201200c1d18090802c2c00200c100c1816281c0351410840300750704905840140c0f0074103060000c2501100d101c0b2245084031140d5005224000160218007030002000240d901030380c1c0c91143e6000038408283c0108014000960840d00c6030003150750150001c0340c404000d400094042a01e092120b03098400d801c0d00051400741c1c00c968130f00980c01209159641d4600390140140c5005c0e841079001e03a0a2103a01181408500d00d80b8035510550781d1410340e1074407142e59610401f543c81603510b401c2c00c03900400140022040c000b4a14010400444014580f400a0341c0e000d032110030f00d200180c00c05aa8207034058280102010121505500c00c05482d6902da0640d211000010140c403c80c1c0603424490002c141c1c1400001d591100 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 298144082 1250 298142832 298142879
    0x50105030712201804060b0a0207090b150a0f030513052a03010c0c0c050306161d09070c06050c0c03040b3a050c0306102003030a060807 60
    0x741d4207201120b009040c22060210840c1c8210704040303229002800a010482c1c000407100001c44102010002079491a8004c140c41c090108100c1c15007c1d00000e0b1502140c0b010800400c0c40c15000001880d12020303a40700314542000018070038105035208000f5480c190007074408010320f440c0c88548001c04140c46034020201e600982c2d4404120342e030840d10142141b05140d0403d052400340000c00c1c01c2d00d01d0100303810701280c0c1c8100c85204000d00d0780c49400c050300090b0028202403a10000c0709400004e0201070384180502ca00107403080b49034045420b0302e01100940403490350706001c6401400c401074054191043d034680800303d44003100d8a0200c81100e1064001982001c1c03d2810310085540000d8030404002d40302c0c40c2e81c2c0004421401186c0c441100c88680140b80c02107604858185c034402401c1c641c40050804c1080101d68540d440070300c5269451400c81c4804040c41e04210040300002180b4000f0310001c800c205002d0780c83e411035001d44080d03101b600c1d000c035074400d108200140415403070110f = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 298145332 1250 298144082 298144097
    0x210090305041e1e08150c04170304050301060f0503010f09020a050f041b05030108160f0b07031110021b010e060a05060d0f030f0306120209180709110909010501050307 74
    0x10188500c0c181401200c9018940b03e8600e5651520f030058200710749580c603180c5452102007000603414000c802c2e05022121702110303145090390380503065100f180107d1111088030340c41c0c650100010001d55000c0c140260081100d0303a1111b07081200131900e845810b10960030040c43c080510403501410b90710390f50141c240c80449040904000c05c40a5023206250000e0b591250807001c0428202061030314500c1d80c95a0b6541d504181c002c50500f841d0b000c0380155444039030300401800f5401100c10084a40c210382040d1143c3e454039048540117031000c9251080c0c815150500080700c001d40c018a111100107110440c2c1c0301200384131900341e0340b941801c8140743c2c0044002504008441c0c010383c1c0d000400400810402c0015a1040c1d15449c9005041d00064210301441c245260540700e040041e040c43c10002001221560000e42c0d0504001c0620704080310315a50b5086440301042800040c140302d640074070040c0200614048242c0000050074410072212000052950040e411640a109103945660 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 298146582 1250 298145332 298145339
    0x100b12010b0a030e0709020702031510090207150c1d010c0515040212030a020a02090c0403021f0207050d0b0a06170601060e01021513050c0a060509120106030c15021009030504 77
    0x40042d080260001c041c0b5844012060b001142804440040c0c079801900680b42c0302c1a005142c600030041d83c42c4124541540305000c0c440105c0c00e100c0c0c04454804201607965156031070040750851035500c20f41c2265040c440d41c0340c000b940100720f41a208401c042048110350600004481105000e0b80180c41c0750090382c96285204207480b02103501038000341010080044942c00140346500c4444e0510050300401642411481c240210303603040354000300340e079060034207503000542501e00d03e1030301d60000e11080c440750905078020310803100180801001c840042d015410031800640c0c045406c0b1001c0380c5429408030310020900224205800c101c8002c01c0280c0c02c0960035a1040c151803031980c10751052480e19107400d250740c0031503841282c10404130050306201d440c0540c50b100003c6440d070701c110040c10080c00426030140c140d60090004407202d0035000d0140b890580100200c2d00041c20190011f903010680c02c170300a001d515000f410703038215004141d0b0401b13403a04813482000000c0010740100006c1 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 298147832 1250 298146582 298146599
    0xd020c062104080403050601030b09010507030b01081518100302040b06030702060103290109020d1a0f0d02060403020405090307030206070c0c06110309030703150e030405090a05040f1a100b1201 85
    0x550303200c0d2280e99041d02e020307203031b4844905c0c11609a00c1102e5038241e090070040340030000e004840d0050858101803020501c00f00018200583c02000c1c244601c0604501e2401a03841c88050a81c600d404009440d541c00c04c10301580c0340c061107010682c0940d00b0509014410308240089a00c0799a0b540d02a019903401c55494030800f514842c1d140101c0d00c0341a0b842075185114041450003807100490050351410f41c00c0324403096a070141420062905d40320703c00020350702c58460b00401c2645c00c896a41221030035100050b058001c580020350001d142108104008000100604a09009400702d8a0a03a6040012980f00060040080c5240f4885404000190040041003215040745003903c3c18400c101e03010a107842c4550b4810364405030301007084e04251780c2c684220310b00d0f4180390300918039040c2084041102090701a0101950903070b14000a02400030341098182d4003680f000405610300c8007280d20703040100041c0d60152005030511000101c0141074812135000a031200e1344a13401c1d0303292a181d03 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 298149082 1250 298147832 298147897
    0x50609121e09031c0201050105010f02030a080a0507050c150411031b0108070302071e060606030608030429070605102c040c080d200a0503040b030604090c03050d020c06 74
    0x11183c0600c100101e80d0902c08038194000551411940001a55854200010140b40c04e8031104400d40d0010410032040715404002a58403481940c0b0116454558400c2164544035a00c03410006004102a5024500b00c03240da0f280668003550a00300031203031b1501055264900c00d400080030074440a418500c65000b2400250700140600300103082040307981b6075619504020000680c1055110103400030050540302c1d401c0540101e182c100703d580d041801c1c059907442240a400f6908903480c8003074116080c0c40d51117215405501e08525100c0400303151060141c4400c2e600c45d0203412603041c020400e840c0f05607840c101d80c40065400100d032088681d44024640010b0001d840c41c0d10792060104181c94100706401c1c2c014034550b05c00a0302c41610140080000d400101074aa581122041002050000040d034082e40c10b803614684d0390b81c0341e2074001070003040c2000b001860a02105c1c400028040081400c400c02c0e42c0580a03151480e03000e004024071032051003410304d8005041c144299801011030708 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 298150332 1250 298149082 298149097
    0xa050604080a0623182802090a021e03010612020918090c210708191401020c1b010201150302060d09060b0631030503070311030d09050609121e 63
    0x100144e5a06180000c0b41c2d40c840c04560010b0b003500116000d003106601000014481e1401d1801244030f0502101c0c4140211480e100292149041402040d052032499045800c0c0e90000791140c896400300c03125414041c0c00c24860080800d40c0413581c40c0e05039a1900883e045582d0050010080e0030030041c0c6ca200350307800540f40c0740c145d105003039045000d510f030b0310103e0562200c60709400100a1904240624058107500240c180b038000c401c15001c140c1c03d100000301d0740d540c04004210080c060a850f64024014050381c20407512801200c0345071460380c100709040c902001c0c2d00a014000e600b0031004030b00811031200940240081160b200c580045a000c2016584220404100d0210384c0c0001001c41c1c001d44941454544408200c0201c1050000b400300000180701c11b02c43d441c1e2858403055168003c1100281c00d000085400b03680f41c07041402141c1800c072244030708018080b0f01e420069601c0e0001c80e00d0b401b5070700c00c0410303100b14028002d091304c1d18800328001d900e004191070307100c868003a0001038 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 298151582 1250 298150332 298150361
    0x90905060a02181e1c1203090302030d15050907082401090b070605010e1b09010309140f0a030e03010603200303160b060108010603020f0904090302100f0b0a050604080a06 75
    0x100c1c0000290340d40c4a40d44004850252205504081441000711700825509106452550042c0c01c40000b1456515442c01140a081c00542403050b411b0582c20362084014803c0450700e01000b20b00d00d2076a0350618400d441081d80e41100503950807205850100d01592f40c0c010000b1070f9145107804210001d21a2503012042c54465240342d0ba89000540700c0e0050f603070071a58a61500014415040340f000000d40c08100c3c507401410000d00e030304a17208648107407224181015140c0c2d03d00014021f5850120801c2d44105041b03070b000143ea110900e80700c0f41c03075450490000c0c41d52032801940b4079050050701c0a8a07080f690b0128040010025680c4404011000d550540001c1c08010410445c0000201e003890086010448501e4210700050807820160080e6007814818400c11030014503800035601400d00c103540c0042e0001a908060f460030000010241043e400c0101c0320344104643e4000c00000403080d03801d001132545450070010140658007038501c041c4c1c00149a003000c14215001801c8044441 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 298152832 1250 298151582 298151617
    0x60409060605030412050702100503060f06070b1005030c03030f130e07020a050705091b0702010210020a0509151204080d06080a29090706120f24090905060a02 70
    0x50104409a40d0254081d00202d4400310400c0103002d940c84403280c122000e4641246000320070341c0000c500b03a6000103501f0400002000190407502d8008402c4010b00c8018030360f50311001d107407411443c07901049529000d14105054006040c0c1000100031550400c010085d605281c000340310f40c0c040380c01000041c4401074410f0000222103202d092072902510740750380589481c51042c104103203001c803a0350000c2d000c0c030502c0c400c20002d02c2000c0000106119445005d0341d540d0b0b00c1c0c0c00104c2c80c14002100d0603001380e00c0011000c4407290050000c02d2a50010394401100d519001c4641002e4054004000808030341f000c0010002169180103190600c2000f00004200c0d4544060030314029100c002103d04400801d01c420a40c0705540303400969222031409040180f070134105154403504c1c40c2c800c110900501619032285124940c000b426403040905c81042101810980c900c024500c10404c000d0300d10700340c003010503030150305d0007003910b4150404014001a11046816002984100c13441c080714a260f = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 298154082 1250 298152832 298152839
    0xa030b0f0a05040c02160f170309010504061407230708011112060312030f0f0105091b030709090e0d170403020c150d091406100f030b0a0603140703060f06140d020604 73
    0x1000e490245c820049103847c00d0741070120703030b000661024442401ea0352040c000c0c2d050301d0382d0150841c7c0540b901071800c050445080396440c01c1500604200604c140b00c009a420304140c0d085510441d140308403012148110703626501c840c01c131030031940c0c0040128030170004802e101501d5000c03240c1043c0080c040310071003410414040c0158000344c0b6a941c107203854070240440784800503104c5000d42002c07a00030300d9508104070381075242d140d082c41c03039889a6000302c0001d00031400340104000805600b2030074401c40c0d00f4550322944030300d50418a000401e450240080c28a0102501d540c41203515800a00d0890030703c0c810401d0441c007030400744110081c00c100d0700080e0b00281c000c83c28820300c112005610307540c81d14182814060002e2002040c000c0c1540100710441d1801d1a05040303d8020b03e0420154803101c4c0d0303040140c111600003901d1090082c03622900300a0024510049030b0054204009100d04001031105481c0c09100d8805d01030110450013181b450b145514040c1301c0c0c80100310034079080e43d = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 298155332 1250 298154082 298154113
    0xa0903081b070303020f06060111030304150617010b040c030501050108010e040618140f0c03031e09040908130f0b03010314010e0607090602060903030702030a12110706020a030b0f0a05040c02 84
    0x40d03d4000b140140c204aa88071070318030042001940040d800d01b4042c00b409a030391142907403801700500151040c280c96880c1d2000c171605070702c440042c09001007501034131001d00741c1c0140a481045243c6029628004801d000c00c0d1091140c681600d20580d90780841382d21344240d02000d614054401d48100c1e0b524020a62a0000a0740c00e0040d00c0c8a82c14120120b440b80c40501e05000f01c44202940c03e41011b0003120741503070040100c40c0640c0c9545501c40c00340051b5520901540036100503d80c0081c6880b4010051100e8640681020300c04482500340240d00d805500b03000024520843c41400f1060005000081c00020449000e650140001031644400c5015519140d4251401c0f000b02c1e02180051003155410700c41e041d03104402d103005506d58145440020351341e00c50340c0c0c5040200418841403e229206030b4110160440078408555100e182c107041150080d03004d030442c0380c0824900600350060303080c43c6d15501c88400c0c00030940503c2900c1e04043c0005003154100d1081103000340e0f9030000c017501 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 298156582 1250 298155332 298155343
    0x5030610110706030902101d060703020703020d061b1803030e060d110406030b0d05070302090601050d0204080c010809010e12130503010501030b010302040c0801080a23030d050901110a0903081b 85
    0x1c0a0b60340031401e00e0083c011b121074444444950340411142020713440b04050078000d23012075000290b41e0f003980c40c0c401c3e0070101d05150041c0c00081d44580e1601c078540600010343c1060101c1d02528901c0c011a0400d010180d510101c05010b103050505103840c10004a0f00440804040e04005000e152809503042c00c25000c803116240700030307810f02e0041003e01105500d0f01c03910711100c1d015034103000f458100707440b0070b5510402d510000b40300b0f0701260300145440c0d00c200155840d6140b485000d5444980311000d183d200c485808100340080c2c200740000303840f074005001d803614803c00407001e08202a2403000c100881c1c0d200800000c080008a10b0000b210340303003403103840e000f18090240b40b00154114410403040e80c1203580d10000b00318541005022007500460100420350740030b4402c0c0004030130720705011030300503401484840b036000200e00e88040d9031a540001e449005013400801c44002c2d1048490b5090151008030303000204880028000620702c84018a034414460b0856200c503900c9400461800 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 298157832 1250 298156582 298156589
    0x12020909100f0b07020913020105041e050415050d0624060e181e06040f05041b0f0807050f0609120d110705010f03020912010c05040f080706050306101107 68
    0x40c103200070402e2031400c0ea03061000c0c140c01c52142c2c0c074040d4070340c00290308031601a080b6190520b0605e20344d030440e8065003c0310000d2036010080e641d03c50f07000380780048030b100510510703004904040c0c803007410100c2c18a8040c02d54200500d014513018013a00da550040442880c5d100c0b140c048280313401070703d050840e5503400810943e90f0707040480038807400b8401e00c642d0101c80e504452510b40140513440702c1c1041101404102114910941d44d290340024024184030b203a4003244510380760a102c00c2c40102503508030100040710328000d10f1955150340380c80c03030b03039881c4901c02c0d0b1500090300501c01e9151103a008003007038000034107660401c83d03540001a0000c140300c21801980e441a2468503600d5042210010384c690294007a0007503e203080d00190035005c02031f14020400d0b60006201604c2c0d0b6640b00320040f2010501c00030040700d0864000a011984240075540401c2914140040c048400094050903030703621355201c9003152580c10601c08002114034800080c0210007820b070140c080100b250741e004 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 298159082 1250 298157832 298157851
    0x216050715090b030c0a111203040605060f10053a0b121507052107081b09030c01110f1603060b060a091a0903070b07030f0807090612020909 62
    0x2811800381e005040410340c2e81c09902443d20a100300b11400d00c2d900300307444c0140001c0c188141107000400c2090305120200803101000b680220902007401003d40c070442c403985080e904070000e0005403080200300040c08400200203042000040500842c101d40841c2000700ca80786203507000340d000d4190310248510307028420315607a11031ba484940c0c80c1458151a005101c0006020304061402c0f541258090040140080c004000b82148070001b41151040b64081c01c211040f120b820f00b441c004050401c1944c2204c802d50200c0c40031030803a42d900702203400d0841c00800801030291024015100141041110f00c410b00807400d500000c103005000d99a8840c2981002001d0542149013003800c86407a01026801400d0910442c034030b864002036608280c40301c5107001400341600142d941d40a21451a8054050068401c00165030209070042c02500b0301caa01e03000c80000411804950300305e4101c40c03590024440301420815203001b04018101c40c044084050b241c6205800403c3d85c185042c0e40b240740 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 298160332 1250 298159082 298159109
    0x2060f1911161e03121d030a0905190b0301050d020319060519020414040e240105040e0115030308190606020303070809070b0f221d06090403050a0302160507 69
    0x4201440d03420205420740c1501e5400c1c80c0d14191001040e1703400004003205881d1395180c001d603140c0904803601e46c40902032021a560f40c0d0000d24002c040c0780051040c18005c4c1c0594010803400501002c13420250b0340341e283ca40d421030f03103030038100a800f0110100c241e03050f00910030f540c0c001c0300c000140114181d0007014041803a0400b01d03103000005d4540118503800a106120602408000302004000f44804440100303102100050990900c40c1b58132503403407002c141c8031000300e400c1242c81203281200d4044404000116608004500340d850742c43c1003004942483c00c0c10303c0028007030658580c118000441b0312082c2034a04d03140c0c10440722079400c40c0380035074000b00c200003040380c4c4410645e61003c0440040d1204c646404506865401090000c50302454082101080002c40c010601c031082000f0300841da503607582d240000c0c5901c1c01404021070004d140c80020700c85061404001b030140b645503484501e080c680c00030450003034000203094141501046088000f0070001c012000240201807000139 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 298161582 1250 298160332 298160377
    0x16030e04140115090509190b0a0b0307031e0e0a02060304030903060c05090f2d0105130e0402120c030309010507051c180602060411010c05030f04180c02060f1911 71
    0x3441030031945d000324401e100034410840d041c41c0000c5140620340003203902041048a802c005541202140c21100c521030011041050555240e0811078148188100030304244440100c410292128070038502c0040d48102d5984006040c110001c40e485802072030400081e940b02d544400581d180c0003800b03000144007141d842603520b003e16642d0f0440c20100e8407180012451301454501c102520221403a1604800152403943d024104903515081d00844000e581768a5080800200c50296026406100b0056407072044040004840c0d20860008005508202e40075004503110360001100306c0f9a40921321200c3d80d0075040b41390200741c1003295100c0c00700c00c084841407400102d4896000c01c085511060900c00030407801d00e902c0da000d003028a442e01200b1b01b9030038424030314801c1c0c0c1c1260241c10700c000390014a44010f40b10030a807145100f00c1c14080a001120704aa4a400c140c0d5400c0b1208943c00109018502d14401c40c5150000c50002280080d03800180ea280c6e40c1014240c000c22205201c0d050 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 298162832 1250 298161582 298161587
    0x409060929010503060301181a090321060f040905010b190f0905101e0f14090a09110a14040507020f0604030503130b2a16030e04140115 60
    0x15007509040403120714011150010030032240078521001d818490000b0110741316880070340040040e08401d81044d12166903500e85480030401c0c070f5a540c60100c45180108940c407502004680d800d092003480d912130001c0c1042800d100c918003600f010703440360349031200b449251034900412803864000c1000194a4407680705000212040600114603030700f4000c1d0510007000440801d10940721851400581940d402d01c5a005a508039000349450003d1011510344c0030803808413100c01e44002c501d180c00d82135681c4854007400c0d525a06040ea0100e0002c0002e120441164056101e03203004a030700070000800040440c686c48056009014018469200020f140c00e050103110780080c12840142583c8070004156a11400040c000400b00100000800c150040301010035045c2504681c00c0c0390b6905107281491800940c1c98110728098030424405044001c1410540302d6000740100450250711641d58100c51500c1e409080a40c0281d807074410a40701410080b07040d01070484020039007400d080c00e1001 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 298164082 1250 298162832 298162841
    0x1c05060a0b011b060f0b1504081203040b1f031b0302040b060a170405031905070308061005030c22120507080102090105040302100519180e040203030708030c07060204090609 76
    0x12905001c503c501158002d16001c2426401580010001601a0390001000040d080e4100810341c0240950460a80204d14100a00846d0461000c80d4004400700d03098900a0004582c040d10000068002440308558500c2107200100015030a6070401d4403a036030345140c0c01601024420004600c031007030045040520880e0880303201100c059040a0025400802144981e801c84500241c48004101009010426100b40c211905011101c8203104080140f4036008000241c0005001e0710205a860034564104024400a50389a901e03544c3c80c14140156503000d01d02c05050540762614007844034072100c02d4503011b400b0b403400c5081140454106546407850682010700140d20400421b6000c1e070b0480110f0341141d0f03040d1409850380c0404042070b18103002d52010100b0b0b90801211144c0c056900148020240407902603003081241c48200c9410351900440300207400d6842000b0b1000800d0200f0040c642c008201181c407407905032a0741d280d030146e801c03030b501c0a04200c3e22032405000b8088140034 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 298165332 1250 298164082 298164101
    0xe090f011404090c050621010803070b0f0403020a031b0506040f021008010e0601200105041a090c09150a03020d03020d030b04020a0c0201080921120a0207030504141c05060a 76
    0xc05103d650800d031139413440b0210500c1180e204910002e01121000c0d40d006501e041c9004d550560f0800d9030355000c1881c1c072540210421650307444850005000c5a0070300300c05500403a05039000f0200d001d074940d02a5540c040300410024040554102c540008004000f50342c030451081c10117550600140c0705000da4130070184002418090444e0041c402c011080540590101007440c050b903080b009000c12203050148268903a81c15400d0008220900049000d80a68040c08030b26200c025a03074049a42c1c1c46004243e855540140c002c00421440140383c2c6500840b044014800d40c98a9929400141058501d16003240543c01c4141d0020380650540300f200721010f0242c0b0f05528040050030014003420030628000d0601c414800400c41c1400c04004c00000c80c0241c21000d00000f4519541001705c0c5c021450035000c0300a518001039400c2014003e0f101d142d90705840d10760400b400c0c402c0243c0c121284d841050740040040201d000183c42805031916858000c03005003100c2d00303003402102e0a441c00d106 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 298166582 1250 298165332 298165339
    0x5070203160302091605130603020304020a09060506070201030b031501031a011406030622410c030717040803060f12060a0e0a021e090a0504210e090f0114 68
    0x101c100003507156451815031090f0824845803034240b1030f00003940c01c0e0160016020540d00f101a0100b10140c041c1c5c02180100c0c000c03a0010b8195603558985429909a40641d5400c104188210030065010760012020428014262040c00002d41d44036554220300740d00984512429083d0055403c18200b03400340540081d010406c00040c42a0126080303100151a06002d50b1000b500240c029040e0b85800341c3c041c002801c284100d4950010324540410200748400c070510300d00040d0520314805406440300c1d10000d00b4100c1c55565400d00704007050f000204440107103c0c400d10fa000140000c2c0720700c0c52056201d2001c50340c482c28a2024030429140c09407803640206400000742d03040180020341c41d0b90105104502240640f400d51100d800c01c100028001d401004a40c8181c081401560300049041802d68032002c03c4c0d501c1c5248101999001c3d034001d05114003188448904103000c1c401d121655003507060040603628440080750150384100d40c48400004007000510a680141085500003078086 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 298167832 1250 298166582 298166623
    0x220815010e09060115080403050c0d0801061106013f200405040b0402060d0b030f0607020c01020d0c0204021305220c030c0912020f150a0e0607080d0c120c05070203 72
    0x412011000b1402e205d034000b0711400b04001020144039800f1a5802485102503c4548420f400e001c2c191036420b002c3d0f000490754000b028060042c2c0081c03464100c0c1d60f00e40c180c038505810140820011000045410103880c0d00840b0400c96000c4d100c1c000e6140d42c13185100581c0349c1c5c9102c0c208039001031240344c9544240d04060078003000c2401515005d8015404480321503640300d18440080042841c7c050841d054084c503008140004004604d00e031007002c50740c0030f91b03500c03480c00c100480e1501c400c50741050108940d000c560015041c41e901414008202c030380d203c03078140c0d1600b001826100d10345880350028804401141d65280640c00740c0220750085081c10702105410000c0a001018940100e400b03908681020300d085d961030308000c5105500140c910041c6184420400700203078010712a40c00401c0d00b141400086007095001c4170001d51300120903505100c3c06044800150100f0704c61b842c20081d25040340341100c0080d218181d200c0001c0d481c3c480e0b40310001e1050504002d10b460b0a15042500c6 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 298169082 1250 298167832 298167839
    0x48050309010f09110f03030c0f1005070f02060106120f1803020c010e0604031403040e040804090c1b060e010603120509031e060103080f0c0307030c020315040305220815010e090601 79
    0x10341340700c6190040c12586004420314010100e4514060300366a0b40c614401c00c000100c01d0f2001188407000740e80301000031702042c0d03240c84042e900d0004a64050005a201e100100b1035a4400e03c3c20704184a0f400e1000f06d240302c0802c51040691394040006c01c942ea508041d0001055010002e42c0f0f0940c80c203003000a05013802400090190140d80f0015280950701104041c1403041401110064809510552420300300360034045c006170094010013682d180352012407120507002d11017004549200360803030201203d5503995a0041c1081e100c0403000c41d900c500000c00081c01104d051001c0100d107507a8580c41d941e94200300342c0b90603031910114252009103581188007000106070103041d07982022925680b0304041081804510414900780020701000c00c0d04820541d01040e214802402142151210140c130140c254211409850040c0030640400051403002d41c0000f20074904000c0824045110350713500380311810300002220b1504c0902401006000e01a14000d0686c0c0021204000384400c0d0704 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 298170332 1250 298169082 298169093
    0x703060501080a0b031501031a10180c0320030a06060e10080c120108070905150901290f03160903150908070204020c0715020148050309010f09 63
    0x5020f040341c03034501e890303800003d040d071800c001d6030719402c45030b8268078580d680d43c1c1041a40a200c0c40e1060321151429004900700b505102d03030381c0b019607070343c21b00491600d501e41014000804502c50203005060b1115058080c2940d107000c8a00440003600e01030342d032440c08428050131030304281c015200b0300c0b00f5140f040203151107240043e0340898145c00c1c1071700e042e07e800c0c4050495015060651070b601003080000b240034040070070010b08071784038014284070a80340d00b0030001302d103200c4c4884160030070030407001084034074207001d080c14900c03030030350185003644550204206603680140941c925490000061020b012540504181c107050704d441d01041060540d542e0820f01008071240078134564a61040100740b20146040b00e4141c0d6006208559880e1102829502d540b150320610b2190b6a6035610800c2860060142c23405400d48031110b507807040014503410000048c1d02e80940d0b8812000c1c6101c010007900010b13001440141ea489582d01d9142c6880d00c0d13800e50f04001c281440c0d0034144500d1900065 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 298171582 1250 298170332 298170347
    0x3130204180816050c030d09030c090c0e0d140d0512090a1a0604020d1a01090e0c0904020304050f010617060106050a05041215050c090f04021305090c0d0617060703060501 75
    0x5000758034005803c44103040503850168030f0329526a040c01030145040d25160854a8031080b603201e8284840980c0d0f0b5080305c903048481da0040c020214260800c42a418580720500042d01c0340b1441c00d652860490285403031601c20812500000b1800c00aa82c819812020703801c81e920034002030090103030301195600c1311a06492b000801d01400d4081d40442c010b5a90f68058075100100311034200710349107141000d1541251810350300fa02186404501081c0c1c0d04104e0a018410b42005045d40d00d007003521814400207510050040c4d0701c03401000c0042200700030038010754008140282c0c810840d400082c00f145d08140040c0e02030824004200319102400d070f080000e9504131000701a0180d04902c007414210008412070010038019490403041001c01c20302103000c0c000c3c510090710503209007400c00090100306e03c1006809a054a44118200020f103002a06e459200881400c1c0034188500b2085080a440341d46d0000b000280010211540c840000c101c43c942c04199480d0030b02c00b0b586410300180040 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 298172832 1250 298171582 298171597
    0x2030114091203040c031a01060305160e0f010309020402040b0915120103060e211804060b032802070b040b060405040c0326180114030106080f0417031302041808 71
    0xba00440000e00b406a80d82d0b07540029034011107890103040f05c008182026000c2402072102003850240461b00d101140c10050550301c505488280710780c0d54500411006030609031016042540300c00b0000016112400588028400e401042e51504000da0411400000c0044844801007050000755400701c007070082103045a401200018219085032042c3e4102045604160134030060782d2100d440015103080141040d4040003010403294039510104010344059200320310890805001140d141507200c5202c00b424901c0c2d401c0c0030035114100c6808002d9810500003075400d40c043e60100418402640d0200b80c1c4000c0c110f500f00b005281581d02c070300030070055000250060007911170010980724101d4003d80013049842d502034450300304614201504603000f00e0b090005401c4030045101c5608070042d0f038141c0c0c00300c3e120344103030b40d07112046100d52a0005105803800d602500402141c5400480218050581509894410f0015006010070744901400303031640c0c0310071070f41c001010074000d83c00d4a488 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 298174082 1250 298172832 298172863
    0x606030d120b1f02100612050622050703050c01090f0e0f06010203091e100f0215070306090e25120b130c0602060405010608070f14010c0b070c0203011409 68
    0x402c0c15142c04698007000301c3d43c0900455000c000c040b40000d8001a40d18802004280280701e06919001c0d01d05240e00b0000c8028429071180010600c040c511100c140c42c400340340030207074002d2201625094035002290340309070781076048400d071000b603942c3c000178900203808007042c0744110034a0100940203201000b4407004040c0c0400000c02c041e03070700c00c0c800c9816200008003401c0c401204603100b00103902c9581c0007a8400e5031a0301e0103440a6000b007012074800110381e0054005040c0014881c11400742c018100720400d41d68900c04595081c4906c917420071000c1d0000141144000d41c06100007092a480c11202005d0302980e041040c1ca482c86603c200440d4069054140c2e602c0320007540743c1c1e0301c0780d980c0c00414003111030a0216142e40d00003110742c0300320b000d00020700040c0d5407220324130786440b03080c01102c903074086c2440c0601c4040c4900501d034880a0040c5050b02c010700c00d944a642c801c07803055842d00e00041d02d50001c2d200350f24003405030305120101004104030741d0404000c610f680b180380e501180c20 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 298175332 1250 298174082 298174091
    0x50a0309051501080705030106050d030206010501080408090a0603020301061b020307090c0315080d08100819021f0305090f1501061107090f3303062d020403050606030d12 75
    0x30000140482c224040600d082c503a050758441e0000ca842c3e10040c01681e00030b40c60300d000014686042070030040140e4041e00a044203900302001110725000c010b20a8030049400c01148000b41c07a52240d8400400d51941c0060301c0754189500200140340c00c440b4000c100a1409010b80035135008130380741c0300b01c802d0503400240702e4038424002d0b00a01444070a04008003055940000d250101003003074000318001d07503204040e03aa90702d5001400c0603200d00441c441c540c0062036503050176a414140c0c85000d4002010705811700c07941c20601448d0003207405604c0001c0d84039024412300200400c01c030b10030884080050240207454103c1742a24040c1480703418104500e0303e03c6480400c10501c480e10107011207d0301405103240003003502010f0540411002010f403819607040880504410500e0b030704004c58868000c0706441d5440e44409082454040b0310001021046582c04031010b003504880c0d041030100168803185141441410004014420b80c003030f0708002d44c130148081e400000502d00e25100e910019 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 298176582 1250 298175332 298175351
    0x5090601022805010908040303020c01090b0406120902031606091d0a0203060d0b090c130c1d0105040906060908100b09180106050d060902031023132102010e060106050a03 75
    0x4003142c0344a4006051035107000780080500ca04c140081003528065000c86001d803030007000454035801540b00d66511404140030038004544252aa00c0c84004a102c3c0030503504e607282c0010703080603941000c10502580400007041910f8008440b00024607114907042480a90208c0800c2103800041c100911540e0010000b402941c501c001481d1198112440c11440d140c80c401c10b0b65502d00805840744625010b140415030040c45001d100c402c60403a581d00129103510040d138000c030701041102c1e103040c00b03818017020614847d00e00c6070500400d003c0d610141c40f075203010740300360401e114144c40020107401c1680150040e02c8809030590080d07030311070b285c1c03d03a100030080003030042207107400095211042d44008000d1007032980104090701d0080b03007655102848284108111a405980450590b086031622a0306130014000b50fa800b03400c3c0712403040804036540c0c600740c4100301c1801501c100c1a82d000c1600d4101e80c2407151409024280004120550525201400c1030045000c4141010b0303d40d040003 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 298177832 1250 298176582 298176643
    0x30709030212150711010e011b030506041e06060818062a030c07031205090607050c0a06050108010212010e090304090218090103050708010f020f031515030c03040c0509060102 77
    0x40071001e0108081010b070b0a11346001400100282506207096003454910541c104041c031911900a003118070440c05048414801e0f006460024460b40c1c1c0f09a0300c0c0500a851000c80c4036540110680040004905082007001740c691703400540313010308204114080a040c018005200e0380c106d039120016041180e040c114200352101681d05000c00c0c02c2010040c00034080000f40602011842074840c400c5d0b07004c00054070001c481007152088010b0340188080342e100741c014002024948440b500b51040040a610b0315403d4030400c1c0d010700c03050703980003e00e018480103109980d03024005c440b1030b8604900f0074a409555074000c90040c5075443d903000030b000c806000c800943c0b854111018000465560b541e05015441e9201441401000e500b0712400e40e11042440c0b08030344000808a01c2c2f681184ca80080b003450000344a81d16540002e00c0050080754901c00901540c0708085440d0050354034509443c1c0207190145660050b40140d03141d000380852686c01040f0080c102446042ca03900b0110030801c030 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 298179082 1250 298177832 298177843
    0x50f010e22050a3003020d020405090103050c0f06070b010e07111f0c0e01140904060b130311010f1b1b0902071106030408120c0708040905060114030709030212 70
    0x464460740907041c1400801a000c2040c410450040d0001c200d54080340702040f401600e00070b0f50040b0007000131401580d65020f41d02070940c4000c207050050034252251b003c5141403c007a0019580346e80a542d1059030780c64410300e0008003403c1551491b083c0b0a0503560403807105c6060041d2007007101004000f880f004d11882d50452050441c0c02103e900c510024081c0e4000013120301c0304285030b801c2c4a100320a650040d00100200c1e0011b070748040000c90080b9120155422a5040310351141d121440003c15801d4040a40043c0346825580b074013007440c0d0b10701340d41c80406001d841810702c00344014050002d5000410210391a00b0151003070040681c600e40211701c2954801e00c0c9070b1031030f43d8000128003502d59a020340011032050303070700407075030700d2581e04001460004440060803001c08000c12461207080c00e40d6503410080c43c14419081042e076940b5036509400c140c104e907040598680030000c6560744111018008a920207801d880c49c1008800202411190b0001034050040c14640f20000e04c0308105 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 298180332 1250 298179082 298179121
    0x1b03030a0509010e150c10061a0f0c0601170c0301050403050d0f0e0708281e03090e04200411030a0903050f0d09030216050d060b0103020c0d09090f050f010e 69
    0x5d81c0c100c010141586407508a40c1003094071b4031552507107521501152240205541103900c08060102804228500075841440d01d000e01d082c061110001181e000c000041c0684031044a004145001d0442d41d458615502d00d498426030505040c080403a4001c81106c050700006000819001c00082100c00506aaa5001c0c007481c4240140003070041c80c085812540240c2d0803881040a140b45075441e0a5a03031400c81c090310003003006016200010071b0482103036500f4440c3c01d018030150341d94140c0340070140c0112019641c2802030710f60074076558120750b2081da840034111402c001c0c0b11107206402c1d0355400024030401c0c10707654400c2c54605050040054450426a0340b03a103580d1313000c036140c290000e000050360440241c883c2c4010700e1405404841480c05452002d00070030144000c9882e0400a0180000c20a05159003005041d1004030240002450400c158450103d01031405943d041100c007082070a0022038641014002c003e14080221411100c0f04091181c02c0c0d120004209100d050556 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 298181582 1250 298180332 298180339
    0xe0105060703020313080d090e190e190308180d081b0906210106050a02030f0d110a020d1d0a0e0901150f08072102090c0c010f0506031b03030a0509010e 67
    0x111300084108001421905008984e82c0f00c400c103950b5502c9c014203009080d900e0303c040102825028100e401158402410001d10034121416249011300c01c56041c0000c11098001421a0040008201081c440a520844030a00804051228140040481c0310103000301d00074000d00002094090032401c20740e070324400004c02c1c4a941c0c0b410190300b000141d00501111580d6100d141c0001166405070098580f01ca0880c1c0113103240c4040003400100075072041e0960801982e80b410505010a140c0002c1d1407500c0030764000340454009800058810b204003034107a980bc80085440302000d49801031000119010f09a40461075120f6464160140c071401041a40342c0d02c881c680003a4950100c1086401c58018200b55094251510704010100301d401d4000701d002c4045040d10300c0181048200b041e40850111407407030621100c02030782e5003528285007011510586036020b1010902c0c06001401c20f41d0921b0701035185c0d1115140c0425240e004002c00c400a00001140300446a40113801c40307400349000a = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 298182832 1250 298181582 298181617
    0x71211120f041503060f0e06041d0d03150b04060507060b091014010c020f0f0a05040f0905010b0a060f11010b04090326090601090c030902061308060c03010e01050607030203 76
    0x40c001c4010a4206110701c4a24031158900209194041d02c246000c0da0744d206921034009003820f80c81108010040d18180c0c0055503800c84882a0f01d655699403001c0c1124800390280344442440102560043c00046101c21440c01041000031101e100305c0e4112981401d280b901d44129050500041a207100341581003c402d504000c00f155000b05034000784c2c0c40a207800c2c00190061001140c000c1c06c480300081d00301c07506002000f00d500d080f80e2000c0c1d90550080c1900701032915117020400f40c9260310a2103e84588610044040100a000b00b8076401000d40d0407824041c5080c0c0002c0444241016405c10b002415500511800e0b0a401c03105c40346d2800382040c01000030510b401440b49008004041d000d003201c40d450b11101e1680721056002c0c01c0b2010042009909041103500288510020711051507a41c210700c41c016101c2d8009000015100341d0541001417802003410300b0214020079201101d00308000511400020240490540784160390399620b40d0410720381603113584a00c01e103000180c2480c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 298184082 1250 298182832 298182847
    0xd02030307050a08130812030112060906060905061507051002130b040b13060206040203150705130e1506072006040801050405010605040e0c061804091e120507121112 73
    0x83c4001001469620070800c02d0955560140c01d85890520131708201f405802c000422001200303000e13080946014003c0091200100d13950041100c0143e403120f00840d484400304016454441c0021640c4105a40c82d1490441e20741d0302c80d0b40f91200c502d04070820725400b08244030382c0c01401c98004040d2010b03004039a9520b494441c0c0e010107400216103000e91200c01b83e004555544045496402654060001e00100e2048007107240c00a00c018000410072074144000340b03a0780300019407140200303010910301c8001d0614000c0107505010450015020322010040e0500081c108803200a00982800c0c0c407941002c8220009030f541c0c422070b4011308156080000344828842c06511600803240100d6080003800c04000a41c0c0e10f074100e0940710340d8800c1c01445041218000d00c1590b18500c1002440022021840e94544000010b102c42044c1c034866484204410040310b817075a403100711007908209041ca0304540d6240340d00d0030f60410580c10001014500720446408000f581d1002a0900d421a15001d0 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 298185332 1250 298184082 298184093
    0x31e0e0d0f020a0909110a0e0f07180605070c0b130b13050d03030506040509070b0d110d090308070806061602060c01090503031501120c081807150c060515010e0d02030307050a 77
    0x921001b6121a141c00d0003500c918034082080f0f00480c0c00070f580f200807980c1c41401c03007200c11200404d000244554a10305070544202e07108810003502140d19100c0d2907000e036046c0841500d40f190000c22881904202c51031003000c4032205c4c0d1003281c00000b00980d8075405000c0700c1d45003c100d80e00460b009060501103008164068100c0b6100b070f00700b40c0b010411a41d81400465a511540c460101d490358104a0b5800c411040d4000110058003401451720301800102400304440c0818025070001d0703001428800990b41c4500d4072a0071840844585080c1070341d40c4990f41c4203072018580241700f450002404c94101c0c000b90401c000749908402641c4d16480e00510041a100e1403140c9203000900c9010f103400d22203501e22440c44100700e80d5807521484c0e6a08801031641c0c5045080c00c01707043c070034118000340a809918000c6042c035456514120702c20170900d8518140c2c0d1303000c0c7c683c5400801c90f40e5440704a0741c2c04100790b003040d0021210210f0906c02c90010a0031441507203405811070090b00c031790205018 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 298186582 1250 298185332 298185341
    0x5010605030a050603010c0f0c05150c0c0f03040311060702220b040f1503030327051b0409030c08030703020408160510020f1209010908010c0c031e0e0d0f020a09 71
    0xb40501d106024569030740d01014202c545040000d40440c0c038000400100328440c000e451081780c81a012521400701121100000e80403c694281075005d00007100d2803084410311150800d08034003c000c50606003160354110000318003c0445000e0100810340a09541d43c100f40b4220b00e0001c0c3e200d8409070300025038000c1c0030b089030442d41070203541403046000323100b4040d1003890000580c0d802d01d41d020342d00319034044001e815a85001c0008484d06010502c0d400f4900000b541031074406c500a00207514858900a02c40c00030311041e522644c500f2610001003904900c5040b0100d52005099903607a0f60742c08183c00074062900400958418410307411510f00c402e000c47c50a50340e003142d4002c14050350500c00c0340c0d0b42401600300101c540103001d08640c494400409032a03c000141003d40d425074441500500b11100d81c5030130390000d407480018905054001440700101010310702c24001440c07c0c184c01819024445424900441401e0040c6090040050032001ea1680c0200355100d290f54805200d030107007 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 298187832 1250 298186582 298186591
    0xb0d060f05010c020a0905041103100e0105070903020102030a0f140c03070c14030a060c1407061a060315090a140106020706080907060f0f020703060629040f0b0d0f0501060503 77
    0xc004400452250300034500c02400b00c1d4020100495941000100e07405014054011034140404044940e226501404081d118944400d400500c07030801c030406a0030b48501070101030921001d0401440541d0f03011080350b0319559207080c000080c0c00c1441d021907a070150080d0b16070001c040854038a900060100c010030310310740078540880d246c0da100c10442c802c0c0b1820075070450b4103500010f903507000254150040d6010014a090403213030001500701c51a81c2da4070010040724842e6131041100d0000c0c0d81c12544505904065682d241145409820a2006103003180040e02c85c1440c800001c500806076048030645000c151301e080c0065961b024041d41c0c5003094065800416442e81c0004c5000d140000c202007200c0403903940170010200040142d500401c0c0d14008011401903c3c004404a00c041c001e4100522020002004084610000784005004c407071707500c0d100d007070104010001c20313064803a8641505d404c000500c0c2c0e04c00b404080000141404003840c603100382040300004216400401a510030b = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 298189082 1250 298187832 298187849
    0xb030109060f080319140702062b0515010e030a120f140708270306070203040612051006390c15120213030506010803030402120a0506010306050408040b0d06 69
    0x3841d1128122620b03801740caa000c1c1010111040c403907500d43d04c034081c000d400e0740821000d58601b10158000ca01c02d58050310003180140d800e80116950900d001d43d00743e00021115004102a09200000c144a503200d1101039040004084040380c040e58144080e400003648a01070b6880c082c504030010b00881720b411f0b0b03c000450f00486201d202003080f10304484540f9401038050345403280c1c41c1c00a207540c1021428044941c0e0504860130341c5038904100e05802440e0680045803203616081000342122991581440080e04010034811101410a001400e0314003a00380b0189482c4441c8a4131111110310001c0040000e84040d1844441407100200d03080a009150300350b0141d849031304d1083e43e4a651800c0c9000100b0620711031000f00328682c081c01d440d441c882c6400b220241d1326190146000310a0700080555003000040c0401c52400100c80003101301d840e00949107c45041d2a040e80358007051002822041e100e2002038200302e0040111005480d1194041e5111402c03214200024092401405c04 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 298190332 1250 298189082 298189109
    0x2100906150807030302101508190c0603020c0a060b010512040308190e1906061205010b04140c0f030603010920040606020f120906162402030c0f090a0b03010906 71
    0x4840b1404254841a00e8041d0003c1c1144a80350942030010001480280200700d400503011444490620141d03440086010707412250001b40e081080482c2080c2d803101050510405c0f044045801c0071034020850b0780c10100004e5031040300b20050722944115900199000083c01c02c1104041e0801d000f00e001d0b050f555116220b400808840703004407051921200001d60228102500300300400d00700040d614031450f804246030f40d40f00f014003d0048040c60031900d41e5103842d407080c4181010302c03a08a8408203081030032501e0610036070036039440c400ea01028401481c0003001072960b4500750403a040c0d60745e10584a0029220b0003540105a80b400e8141a2046042c01c1001a4035440001c5222429031640c0240240c0b03400145441604e500c44040190040d40a0010001260300203040000542c0034030a03070003084062a00c1281884d411481d1041600e10510501c4074101d02102580e110740c007601050f42da1060100001a000000c1c4d5020b240d80c1f4100200228112001c0e4000208403602c03d4600c15 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 298191582 1250 298190332 298190339
    0x5060a0e0f0907060810091508010c020106080c060a1e09120605011728170f21070c0f110a090213090605030c06030c04080f0d09080613080a0210090615 67
    0x440800d406e607500d1043c54004a018440345805034031001407c2003c26919a1641da1a080c66003502c1101e104400540d44d113010401142100380800e012604013207800074504400d69a003c0c100c80005400448112500c00030300f013442c1e0080b070050700501000c0c006901403030101e203000300140c0802d014403e0a03c100ca00021115800041c14094030080022800c1d54048901003920307108451319401c0c0c41004051500c00802d0600c80020841041c680100c00e0b940d00d01100010480c42062034501a00401e050402111950282010b43c1d27050303010344040032000443c10606150001c0000d0a0343c840c240c2c132000200003e4941c000c02416040680006545503540e60038003c03550700c1d21902c0d401da000041c3c005064034008000315400501c0c412000d0070309072241a982d01e480b94800c030201d6680d20841c00482e00c0c81d04604e0040042904200400742464090015021031040c49401440d007000800d407031003464002e0220f8450081914810000100a410008050150b000300915000d11810022 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 298192832 1250 298191582 298191587
    0x60806030f030d06092405040203070e04050a090b0609071407080c0f010b040b06041409070201290102010f020a020309010c330e01020405150d111b0f0106140405060a0e0f090706 78
    0xc1114000d101c40d19101a4a00001e08c00a903100070300507000c01c1048085070146644500c40d42e40121b00120700040e91308240c0c9440740410760090065441084400708014615078004122043d450442c00c13a03586462403880c0402c214040c1814518060245c280200b83e00303881503010350a910000c071428480c0d006544244851446a401224410741002000141c941841000507400c803041e813000280300347d441d428001071039018461a40030340003044041a829a424081d091850180c0002140b51005158004e5078a00c1141c848038188484c00c90944184a80003104429170008580c002100d0f614110181201c510545001903000385850444d82e0201014402c0e82d06a40f03014005400550310701d6100401a00181c03502d5241c035490302d060048104012010b0900700760f0400c03178a42d40340c6d80c0b44003060606d030680c1007841141e89407400c10414240400031030300744107400761000503483d01c0b07250210b144000103420000400c100b0320184001609481c0f11503100740c0080040c2c40380c1d15202c4004 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 298194082 1250 298192832 298192871
    0xe0c0312040501050904091412030103030806030303060d020112271a0603060112060f0f0c080702150703020a02030d18120212040312030b030d09140303070804060806030f030d0609 79
    0x60794001402440313815442c1c00c00e540307c2003144e4007a03070408140d03500b0002641d2030510103165255240101000403c00c051b08209100c0c2c201e04110301444c118603180001c240d824000c0032001c3d0400804d810b51442c000d030154007003c80149920310b10a410001102038072030050043d0012078004003511b003040e120090300c54255002d01c00050107419181d103401c421402c900c2405800340d8045581d1207001e1400c11071441603010030b9901c0c00e80801c60000302d4101a103002401007400d8195040540e20039010215616440d0340303e041400c00503101c1744108070413072850081c0260901a0340c5040714030411300901000760030311079108550940c010061560100c0c0c81e41c1c5407000750004040c042c40140001482c0c20845000d800c92817030001240307859040043c7c80d200100d02207030042920400240000c2c1034804221034014005d130000c515041c568ad450102074803852040381c041105036800324039250340a01402d0701040746042100e07120000d90018100401c0d103445100d107070500d0708410702550601c5d81907 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 298195332 1250 298194082 298194089
    0x11e0506131e0b0d0504021305041212020909010b041a040807061b0605191a03030f0a030e0604050d09060c02010e0f0a0f270209060a030e0304090e0c031204 69
    0x10210718500018410b103007075040c0344282807248070040424038100030700107031100410f1514042072604140c014403942d000010403208025040030104008258140780061811a0358540520062501c015510080c01840c1020754803120600000031203010307001c0948180c50380c0c0032920b103031035040400400552041d0312400b1a00d4010031410002e1174007802d016091009506a02c42c04407415980d10130403220f00f00c0e9443c140c40c6010581101501c0c4c1c911400740d4820b0001540c0022650b004c0019689005650040881c02e200090050038144640c00103044881c00c42c00721013080c102850401c2d1544401c408100c0064000c040009010b4803482c440c0381543d8040e1189940b4242040c1840148400b4404860304295041c200051200c4c800020200038000c1402c60a8210061940a11914030300011480d03401d006200d28840f5a9400080700c0625003241400030380c0d0080201b8003030840c041c59000d102440e1a103104001242c00104200012120450070703607104c10700411f40103909004030301 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 298196582 1250 298195332 298195357
    0x306090c03040c0f150f030b0f190905040812162114130302060a092a0b0a1707020f071509180c080a050c0a050918011e0506 55
    0x49150421608025a0003030f02440700d0740311084d02d5420003074070200780758850368248140100281c459580600b2100751243c0611701849121482000641c0809104520030301c5140002803d000d4000f0780200d00005080b10a0284034a1506041079405500070000310501801c44600003026178201c07140402c1e480403079031240f070f07150401d1b00e00900c0c040843c600c0c0034420329034404450500805100e140342c03044e005000c6200200205c0d140080c24a000a0034900020341490000307000117242c0c1055000e8520415500500184280400c00d010005030307000c2603100a000500406071903005003030090365480404403007481c0d1a244012603031040c00e00900c4109811250060100f100c1003101c0a04030308240c070b4520019520364403264042c07140504011a182d42d180c0b00401c210390044405e561042102c0000c100034940a5211035580c8614103048080080005d00308a00c2d81d6080c04941d0102d8500d0500346080da10391023100d043c20708481a050030303200e00d0000000c640c90720b1412904020a1030 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 298197832 1250 298196582 298196599
    0x70302060109020304081e0309010c0504180b03121201210b070f090e0a020301081510030201080705040e1302040b040b0d021e0618100314040b060a080d03050a0c050306 74
    0x2d19460004e410150080b00c0641040000581010ba0901c00c4c80d10450095171643d520304103030100c0350841e0749040b41c0000380507062104103c1c00c846100084c0143c0114140400c2040403400081d0038099110582c0c8160100490615161880d0380c440506030703843c00b0210310b0041005a5031040200c00b8a000414220180c030024146910581010f0011141410a481d000e230700c0f11650510130b1030484c0c03641281940840104880304080000c59601904914807001c03070b0401900b042402604ca000c00b80c1444016404207481c98401c0c0d003218010204130b40802d81506240500b820f0310003c681040c0c1c8118140140da24141c0750520900c201c850004156a400100039424441c980c0d2003025054000d00740203402081d142c8400c002051800360300b85025000d24801801c00003007440b0900310104141c500128080071147c800c200b40d40041c0c000703a2041c1c1070740c2c0b058001000382c03c082d0440c10490054107642c80025815170410390050610359001e000350011101d0031641408112162923001c08076 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 298199082 1250 298197832 298197839
    0x81902090411040b12061f08060a0c17160905011416110405090a1a070804060e0a0212010605090a0213060c11090126010e0304140d0f080418020703020601 68
    0x304101d034100b2806000032038210319000000c0c030908203c00d060031841d000a03040003148066400405c05040140d4000c0309403d0400490716a07502004104032401d07075641007201c40c024001c504a8000c90781c4c80000381214505544110030081d200f00e40c101c04207000c05400729140d802000c440c034460b070407000704609224014918138620301c5000d40c10354047c03052131016540c03500c1d1809064401d440c05402400d04c00d29515201183c0301811000c0c10081c2003c0051026440c0e100c08000d4006410460200f15400486041390505000620080d401083c40b5046800301d00190010401c81c0c10845220f8100d95412025409030301c60300300a4404900c00b400f00f445024040c20041c001e0714056460003003882e28860200303035090420b1f00282d803160400c2141004003264102d071252402c245030020b00981506c508640e590f40030f14007681b144882d500c1c1c0505084d483c1c01590300702c80c44e0440726108044006050200e00396006001d4501000c00342411240d030316105008030341129502d503004251980c82c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 298200332 1250 298199082 298199093
    0x31b0e0a090215070b040203061501020613140a0b15010302090a030611160b0f0106050702030c010819060b0a0201060503030f0a0e060d09060605010318170a091802040819020904 78
    0xc4041c002c0360f00c055988900070802055402800050b441080c010046091900400d8a405001444483e0309e00185044560699000c00c103a50000a040c6507512802c1c0302d0300e17045403413505001c1e41c1241c2b80700d11811700d41405814408240078203040300c0d04090030703a60074004500303911650b10f055800426140f03040000894590180711240c03018644941802c2401ea45008030404001e03040d00d004c00408140b110084021025078010145820801c0ca08151a8003003a161040311003400d042c401b40a002500300d001c560944221a17408640811403941c45e11039642803900b045000703c4c0190300c2c10801080030708001040310701d01100503034094103164203040215208100641440d800240900034900302c011030780a164001031080c0300120b0b02c1410400010100c90f16000c00444030754a201c00340c0c02086101c40a004030310b140b1004240e072403045a10540e51642c490340580c03045100080801000e10040d400742064a6100081c2d801c090303d141c1c0c080391200c48144002c4d600c140c01c0000300b00080c2 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 298201438 1106 298200332 298200341
    0x51504050a080f0c04090201080a0e01020d02070804080c030607140c01021c050609060108150111010b0603090d080705071208090a080a0c03201e010b09040309031b0e0a 74
    0x5146d5000240050005030040385820381d100010900d682e029011078000d4148810207645d640c0b5145010300c410307405407084102d14080ca0314410114a0082001d50081143d503445607e03807a070741130041c41654004598035045d5035007040480301f400c403070341c45206503d8014100000e4502c1d0034803e000a28000901c0503041200311010002d4232512826019200b031020300c0d10101890080703003018014040a07031404d500100100030007a0b41040080c03050420300541c0c0e1446581c0e250302405684a00030458001d1041301c042518607815481400c1080d4800c168404540c0004041e4407540055070100c1071507400075021100701014581c0140000c0c51041440c039107140701c3d80601b1001c0385c0b6188500c00c100000703480c005820340f0792070307003500503010710040140002c00c5401c01c0d14001c0d00c1c541030352108039040100c140d04244042400341c2000211107079505440596541d4950040092 = true := by decide +kernel

theorem cover : BRFrame.Cov 298021582 298201438 := by
  have h0 := BRFrame.cov_init 298021582
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298021582 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298021582 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298021582 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298021582 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298021582 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298021582 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298021582 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298021582 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298021582 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298021582 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298021582 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298021582 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298021582 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298021582 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298021582 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298021582 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298021582 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298021582 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298021582 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298021582 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298021582 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298021582 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298021582 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298021582 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298021582 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298021582 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298021582 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298021582 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298021582 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298021582 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298021582 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298021582 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298021582 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298021582 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298021582 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298021582 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298021582 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298021582 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298021582 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298021582 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298021582 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298021582 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298021582 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298021582 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298021582 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298021582 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298021582 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298021582 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298021582 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298021582 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298021582 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298021582 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298021582 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298021582 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298021582 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298021582 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298021582 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298021582 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298021582 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298021582 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298021582 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298021582 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298021582 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298021582 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298021582 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298021582 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298021582 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298021582 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298021582 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298021582 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298021582 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298021582 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298021582 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298021582 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298021582 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298021582 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298021582 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298021582 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298021582 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298021582 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298021582 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298021582 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298021582 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298021582 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298021582 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298021582 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298021582 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298021582 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298021582 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298021582 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298021582 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298021582 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298021582 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298021582 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298021582 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298021582 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298021582 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298021582 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298021582 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298021582 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298021582 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298021582 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298021582 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298021582 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298021582 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298021582 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298021582 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298021582 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298021582 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298021582 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298021582 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298021582 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298021582 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298021582 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298021582 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298021582 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298021582 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298021582 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298021582 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298021582 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298021582 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298021582 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298021582 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298021582 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298021582 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298021582 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298021582 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298021582 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298021582 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298021582 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298021582 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298021582 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298021582 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298021582 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298021582 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298021582 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298021582 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298021582 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298021582 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298021582 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298021582 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298021582 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298021582 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298021582 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 298021582 ≤ n) (h2 : n < 298201438) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
