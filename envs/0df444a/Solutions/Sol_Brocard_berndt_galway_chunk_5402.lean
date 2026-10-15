-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5402
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:45:21.542396+00:00
-- url     : https://prove2.me/submissions/43a88a49-153c-40cf-b6c3-e2e1185eaac9

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 971402877 ≤ n < 971582733 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 971404127 1250 971402877 971402891
    0xf0a0605090f010302010320030709210b0c1e0406080603010c0309020f06070206070813031502040b040b0319050403050319230c0c07140a05100e06182101 68
    0xc5800c0d040144503041044990401e82c4c40c44d001180035120565004189002d03a020003410030f0031040042d8850700580d212100214a081c15180c07501c0c81d02041c01901c24591a58800042c01d20001150440659404642c44039031510322034140102291a01c00002d0300001c0002d0300d65000b10007217201d484220000c101d0014036000c2507047e41c00a02c4002d5000030034482d0000309242c404040c04000d030024101c00c0c104143c540d100b0183d5800340303000364a03048003061b0400401010080c452802099110150f04107807415011001c140114001d120500c1e44c00310004841d00c802c88003518608800c0c61050215003050704000c2c1c815032059480b5074590081000541041c5510701520203051041c4800c48218003002c05849022400500035212002e802c0041503601c0604102c0d00020300a89030006070003400700b4080000e401070039484107010ba11200b40c01d292315038001c01074440d13810f000d460141da40c03200110004100f44620322103503800000184081940c0c200103c1d01ea41070030500000300180 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 971405377 1250 971404127 971404129
    0x607140f07120b1e0a02030925050a24030f0908130303091215050606070b090609010f0501050d02040e010f110408010c030902090a02090301140717221b05090f0a0605 73
    0x8000c030780c41403804d0b54418004910392003201d5004550041500041d10304008000c010075985691185082c2169801c1d13950501c42032610a072910001c0502810214400440c955416220749000d1400c1c0107043d692610080c01240b0368000d02c141d1a031122602c1d54490030383c9080070403000a80400c0d0000703880d4400108140c80c035907000e078480c150010003104065255401070005000d00502c000c4d00a0024060440000c101c1d40c40140190400e030040e2200c0d18190061900312800507102168207810000104801c0d10f0b280c0d20b8002c0d01d40c0503200803900c111000000d034090405010b4440803580340060032007200311810043c07c1078414032802031000100204044080d034200c1c1074040d60000481011502464582e4001e15401c0744c0a4004a0b1400c021819041110800c0310541c020030480300145a050b6180b050641e0300041504102200140b03150020152960128005141480e10107803420f0715000310003404010100107103c02100e2410300e5034088072502c280c0e250200513060103008142 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 971406627 1250 971405377 971405401
    0x30703061e05040f0b030d0906030c02160311150c010902120604050c060706060b0301030807050c090930040311030f06370c030522020607140f07120b 66
    0x8100700841c40360707036942000c007008010003403903581c3c90f1300743d54481d11805a600c09200e45190030364191508884685090000380035140b41400881c01c5400a81c200340328440100130103c260f940110f004800046c034840400c5265a24926400d19030300c01042c240c24201054029142c254420349095103001c0c540d03a81140e581c002690010000c1d0801075020409040c1007002d062802d00a00000c07640650b10071305603890394020781060f1009030000550005029082001c0b4001d502c044d1100589480d164602c2ca8403000300c844141c072030842c0c5900701c040a500b10400e0300a94a100403806546590701e10780703030758202000d041040c042d01411151600510001c10514401d10340200040c950690038a1001510190158000d840c0c6d51002038009038158644681d2121a102d03032030014042c101203020096080c41c0e00620102054000c0c0d42e8001a04c8030303030135034085e1503018103450301d0040c1104401e0300b000342c01803080302d103480388a5001a500c845070303000c221000d0107004a142240c91b92030030021 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 971407877 1250 971406627 971406659
    0x3080f16050c030d11100504020112090503070c14090a020d0e01140a0c021b060d0e0d0e09131a070c0209041b0603090201020d0c0c120f020f030a0201080708040807140303070306 78
    0x441038202440c03806c0d0b24643d90b045164090704c14980041c8e48071036203000700102c50303410109481583c008502e01c801c100c00c545050014181c07680c0e0039040c28032001d0020b00745c541e000b40b80b070203026004545541a40c0b019000700f41039000b0b07240203020001400900c281100c408035021846203041c034441918150020611700541190400c8402c0f03059003240c24010540e0000007502c1c1869654a59000300740310512441c65240703916030760040e4034111f903000c00104a4003e401000c203148030958500c00030b10780700d02c1003045401030300002c41c2c2070352551000d07612000052030207900041d070301040004001c1047d1544503c4100021048034590b16032804400320340d08100000d0140c5c0c40b00d2100d00845000305500305003188120805104692611004911505e0310b8900316868551041000d0841c81d01c0c0d8105a8440c1c0181c0c001c00f0f007800103400080885102a024000303101c10351003c10705211100003144d000c81c0e000070302480d803001549038550b0b81e40e00807070340c401c0001d1418801103004d0500b40540d030 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 971409127 1250 971407877 971407907
    0x61501120c0c061a1503090709182f010818071805100e0f0423030409050c03040c1e030506040c0302031603170c0a0218010e0a090203060103080f16050c030d 69
    0x50a40c20760076003402175510107044407a1501c994000011088624040d00f01c00551070f00c26003d0310080c07403806808420080280d10a40c041e010071003001103d211425407010502440e050724140ca40404402c0040e0340500b0703201c654018001e0208494000b501000c20500046030b00f000035640c0d030350303000c41d4144243c0102c8070007407203900100d1001166a4400c58015020f8240c4802400d01501241c009000400f02071803180c00100d800c02c0b482119210302076004a250140c5441c42ca0a41d641c500e16086a000389000c1500c46203200b1030155083c4101409140e0100840350341d42084d0400354030244641c40b080748030707100d1182002d0b002c1e04c0d2400380d001101e42c040000c10340056104502007694106400030596440b44802c440d0240c0e441401078a000d20240083c40d01d19410031319078031015a0010034515039141070001403401038500289050460f500683c80648520104801ca0706a100360826042c076808159114014084045034441c02e10208400311284900c0060701540e030300201a02c81 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 971410377 1250 971409127 971409139
    0x303040209090c120601050a06020f0d031e020d020d29090a0e120c0c0102190b130b04060b040506010e0102030301120c0503070609090617061501120c0c061a 69
    0x4200141051110365030440107650548007440310b108003241c00d910185541c180345500100c01040203040209949001d040f0602c00343c000311203104013190369450681a034008055884500358000e0013400c40900c400c0d18021015550b420403000088080c0d000074442410151418000d0700b41509511030144020034400d1050707937801820320810403841c1c80248058400c5840c0c40c0c03684101003040c011140b01d03403420000d0603180c18060011a240640c00d520f100d0565005051691301c958000351203600c0942c2c080100c0916036507050f03c40350304040581d8010100710a0b4000e1004010080c3c201c00d01e43c0e00142d40c1007207203a403400011640c02c20002040c42c0543c00820061007003054641c7e91992450051800c80e40142c0d03030350007091800320940c0c07000001540320001801400315902692006040c400300300c13400700d03449001c25078417000c2c06401212a40417500700303400d5a074000c2034525180741c0688403c206031300c1901c00107001401c101508840d010314040c1580d085080e04c00b11032000d01310207898 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 971411627 1250 971410377 971410381
    0x30c021b19060206160c151e090f0b070c021f0210061211041107080d060e0403050310080303280f0c0f0e04150e0403050c0d0f120c050910030b300f0303 67
    0x204c01d002307022100101c0c507940350041710400100100d0141d282c0d031500c0303510310b10b003040b03000c0c00d00000350030001e0400010000e503080390b2005689c2e00451005080c0380b08c0f114144142c8140001e80c0351198401c0045807407402d107000000c502c1c90000420741c4050050600121048004041000b03c90000e00369400b4a2420702c40000440c2c00c140261021001d00400040e071541c850181280c1d81d0011070701200014800820002c410301c014480c200145045070003142142403000700080c103504042e2002920b00f080c12070401100880c0c4d04260754a001c400b20810580c040703d04000c02c1203000300c8240c40801c400301d0030b0b0281820b003407041e220301a400c2280111400c1c203001c002200548098410344c00c2020900c07208960100620690700861003a031502510040f02800140110440000c80300354140340101c04a1200e812108035440b024044132424840c0b16021820380080c00000076680e040f807501203490020b51221005a00c3c00e0034900c0302d61550001c5c021002b50384044a090b08900380e003003400 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 971412877 1250 971411627 971411663
    0x602210a0f1103040b1903050601120905010b0a060810050a1a0705030d02130302010318020108070e01090801090605090705030f03071209080a03021c030c021b19060206160c 76
    0x1840e001c4200e1140b50215408070365034580791442d0416000648a00400141080c280f040761041400310001c5007410312091034640006891700540303d0080b00301544440d0b2030304c10860300703506c600f2940400906c000030b0107840d40d90040c1901021542d00c410300e2001c1c10040f42c1c61038295942c504445040402c000081800088500c05400441d012155440240054800e056190014050240002c440c9108080c41e41c00010240c0b2400100480d10045048650016076841043c4075448a90781c10101c2c051058640129504800c642c01880e06501c0d01100904101c40b5400c12406421034074101d0300d420784c83e1002c0503100d40780e00c0c1c6080b210764001c2042c5d00c001b400744221290001c0d07048c205504007907504c0303001c02d050240c84481100181c03c171111242e40190405192001100289030030400603180c7e0310003941c0c07100c0300c4241001500c3c01803040e045d50b50b1144084902c4402254180f42c03407c0d515032010303640b488103883c802072007503511001680c0d0700d10422215407040e41050340400c010400b54 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 971414127 1250 971412877 971412887
    0xd120f091e061103070f0206010f0e0f040804120b01090b0f031b04060314150f0c040513091a090f2d01061710150f2606100602210a 58
    0x1800c102c40840d2038000030b0b450b059034200918031468031902e072182d20000c1c0c3c000003401c11405800403100c0d60410541408a04162150907502034442e00e5010403607203990a0580681c003941d84100b15012002c644042042801081d19040320227680d020300c901e03410102048407041d400241950192f000480141c030004540c0320038605c452000d000000d80648cc0c1c0c070341700d2040f4071030f0f400524150702c01221442404d84003038501764051100d2202d40041e040c80290812644202c0c4100da114681c0303890140d03a03402c165440319001e6035200071906901d81c9200c05010305080b04030350314610360103603c8805000711030110311b800100f039407941c68180c1e00040001c448080d4110044c0e8038079540d030300c5070003007002c034100402d00b00d6440035440100101c00c010441c0100b80c41d25803c000c030aa6000c0c04003001300d031789548552015521309a03120050b0100f118240d4907902107903c0c43d100301d07204000910580c80c500d0b0b8045801c1d504c00380e0907030b40c00201c2012044d000b003d00c0d2629100c140020401003500c18403070 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 971415377 1250 971414127 971414183
    0xa02070c0305012f09011b2409050d030606090501050901051b070314010b013c020714040b13110c030304230105040c1e0807170d08190506120d120f09 66
    0xba450801c523480383c0320700450981d401c24241b503e03410f548141c80000d0090800402c0981d80c9549000d03c019800d01030000c0c106081032040505006000c101c5001c40e030f0180d4140d0b0700072500441d1030052010950101c40d81d072001c070300c0151440f1000e80040514401d042c0074031004007030b06841380c064400132034841120340380444c94145441d001e444c41c99840544e4847c90008100c071a0b900418009040c4054511009032180320280719900d0301c041400c06403680100d1000020840000203802c0003c10740d0f5035068803404000000301d0000004000800c2040e5041c0c9890164499102c6625000381c04814225001542c01404480d0450b000304400d110300074210007052034160080341c0650751801150725140d003d400c1400400c0e0100468284414100214040e5541600e0084224240100c03000b2120a04103e111146502c8600081094039062a80d44c80100710a00f19403031207900110007026940c0704011341a00504040312050114018010056548e4106c8440c0c141c0c000ea0b105501d50032906 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 971416627 1250 971415377 971415383
    0x1c03032316090b0a09151b11010f0f170604021e070606060822240e1207031407050102090904030f08090c0a12020f1009030506011d0a02070c0305012f09011b 69
    0x47c1d100759420003000c0800e84084620a04940280045200c0058808a00e5041e2a01001048010220802e60142154074a2810324006440607120040414083e102d490422910076510620307018043d00d00b00002c0821500a080030045541ca9010484a0f61415900e41c904c10040c11080b0031040e1400152424042c865808040504600003907003222804200621040039501d0b41360040103a8140000c08607059401040741c600f21060350003030f01c80c01485882034410340c404150302c2c0411009504540107001c0c01010a6250316103840d000301412240d0550b400000c0300600072a01507540081c050f0f889001c02040d841c1d1440c10075030900803600501c1801e0343e000c00c156a82184603101e000c020072503d0541da1300d4030340090950820500c4c00b001a441290340d03018140d00301c06108030181c10755800c005000380140e41c400103400c1019110007660000303840c0354030300002d0b100c11104241e8152003a00784054031803000301c2011101842030007013680280c08602000740c00bc9100c07030354060070501c2c00c0c4 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 971417877 1250 971416627 971416637
    0x6040c0308211306180503041a130f0501111c12060509040f0b070203030106020a0201200709050123030a031107030b071d1c03032316090b0a0915 64
    0x2c1101020020020103407141c01c03282410402c1c88003030000b03074001e003107200b00720410003e182c030304940c1c0302030741c0340302e02c1c030403064659103600070400a019180121004040c0310705150740c030203031900380448894507a4410703507001ca0302c0c1d0710b000d692520000c40d0304006419010500e42e40700d11844c0c41554524840c01c01d5420041da01d000110701961228001c50265000d540c82520080140c030303015514120280c0244151f5005100402030b103075002402c0d0881560a1130080001030f041c0782c0c862b4155060040c1015036001b030000c0455a603450394801c2d41242c042c01e4205689907441550620103039440505180c00d50823149414012a007e1001e140b482c0030800c3c01c68824981e01d89508801400603078012000403030481400f00c132403094095680c41808110340400348850801c00c0201d807a01200700080a01d900d9190030790346d4110703804a00c9080c840001410705a0305d05001d45500c456113004408003c940413010100c0d600b0040c6c020f481000e40646c840c030034098100912000340004072000c0001b008 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 971419127 1250 971417877 971417917
    0xe1f0b01050c0f01020403110922080702090a0c3509031201060203090a05100f0c08040f06050c15010e01121704060314070f02031b0a0f1b05010206040c0308 69
    0x102c10405041d034605003d000507211411032501e100303d1003a0301d01c2c403841031040b007080c010419040308140400017035428212103040154503200155009540c1c0181d4413000180030888051065041320340450f909580d5002140c181100c1e0200c03150300c0c58401c90801c100e100080c1d0b04003c03aa020a500541c0b0041103e0900c2c0901496448600e0260441c00060300040341200480c1014103041001d070400f200c54140d00540c04200401000c00200d10790200b00c00c54103002c2c244174842d8206c4001d40584d440541c2101c0c5c88907409002a40001c000710758a2081600c2245c00d05000c402140c1610070201d03450790140d1900c00c0c0e6400314415500203403540390741500d400442c1001c1c45c000b07000030700d0030340c50101e0080c44000075241e15000040c00344060111288941d07422960200854100089503030490710105042c212851030b003240c03864024120303004a9060824449402000d8200000307000c900301146848200490319040107603002050380300711070028400038802030003070910b2100003111140d6030 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 971420377 1250 971419127 971419147
    0x907050c0c150d060312030e03251704060e0102060c0a020a02010c031101050f04060b011d15040e07080f0112030804080f0913060f14061207020a120509040e1f0b0105 73
    0xe03139455204443d40151501c2d203010310380d01070040d1382c0c0380c0855402450800001841c00091244e100e050f0141c162401102c3d4002c10034400b40b03140091391200e01303060303d4039241e180281c040303490f2000c01e50161080c00009075038004c1120884a840a80b680500351540701a801540c082007030341800c50600c4842d17010740030249000d00c50700348030b000031307409030303400c40c00c1901b08401220300d4500610304011180180700305002255000e10124102502c280303a400c00e50100c8051140169005207180041a070103106905a1041040340500750001c40c3c02c2e420307680e82c2d58898039021040e6008005ca0010b0340010003054860f0054200c00d0340c2c04c024a0328040000b03000800544011040d00009542c072101401002c50001e910b8002d011118841c01062618100056050040a01d01c0c1200c0c907030f0700d000414151003030240852003544140740c0c003000152554064006d80000941600070392504421b05160f000004121b20107100b0400107145400c200340750903004c0c05541c041681400410001d900034 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 971421627 1250 971420377 971420381
    0x1a0306150712080901020a09050907090f08031315020c0607030509180108010e0c0102100b0a080a0c05041b050d0b0102071a030f070f1b150f05060907050c0c150d 71
    0x1c860302c01d60100782c020701d2803180a446608050080e0340d050388140724840404d500b01d1032240c103840f400c40305403ca030382c0c407070704100c6401e403054110600e08030403150300003201c3c900000a802060441c40030000511b4030340e204d600740504070448040050f4440c4507010303c0c0703041c50401408600c0c020b2800c94034003c0c1752800702d45028031001502c5500d00c3e8074001001440c2080c4107040c42840f07140054803000c002d090000b961810561890390517250b540c28850f03080c2c0c0e56400b29000614409064501c050340340c1c00c0104c0e10a041d84201d0340240c1c1041181711580402c0403c0a1080e810303920342038201001000c20074024180c01da512810b41c812030f0030115040a0303608030008224030b0150f1150b502e1400c02426041d105010740300c8010701050300e03800e4103c59000b840d0740001c003004d000d01780b62104441c1840c00348841a03000611405160540c01290500140c00c900c3c4600070584603010740342c61769001100c951040e454a58103e03003000041070365a1600d500240901410703401141c1c101200e00e684242 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 971422877 1250 971421627 971421637
    0x17070b06280632180102010e0c0108060d06050f041106070305160611040b0c070504060305070b0c031201140f0108041110020c060a02010e0d050406050328060801021c061a030615 78
    0x210f06000b042e07140400c80401460a40c0701c50070310003030084010b8075503003640c2e54909030201810310031000c00280b610748540c11350f15030141d0004030611060404031076070114034a095406a40c0329074400d5891541d8248041202c0150794596900c6142c90707882807012915a40c000011640591290703054509544c00c68098070162100c0c0380703650b0b07580c154910758034035000c42548114082c60801c203041002c210041900c1044504041e81d041c0e0b5410b02340665030451050f51014880030b040b04001203980c1c0301a20000b810840c06480c04000804584019500320008540c0140700a1100d02c0c0680f0034207050a0540c09603a11780110350601e0301100c00202160402041000180e542d42c0242d14810020000c5a410b09160708142f441e0a0406400810301d03c0010002016046080c544c0107080900c41100d8003401c0c0b0800e410000b0680b92200d45002c1e510401c44c01c010214805061001000c00d031140200721011440d04d02c444005080c0007401d66000246481d82c01a04c03000e030b81652103a080010a = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 971424127 1250 971422877 971422967
    0x9190507090b060705060a020d0e060c030601050a090e1e250e06090307090f1112150a05090a14100803091905090108030d050c0313030c17070b062806 66
    0x5038840c41c401c01e40d40120713040400940cac06644008240000c5590305000ca0350072160a180041d950300c48801d06030b40c00b10042d444a090004190100000142c100c0f2581c540c140380c54940e01520340b00c03021410b1600300b00d4151407101c1c4030140190100280542c0a4050306103000d002103003007024020000c0c0c101602d41d0b0044108540340c6546141d080d034144038040310041d04c0c2c141c0b1814203003840030107c0301c1c0744000c140c4480c0c9140303e011043d5558070000020002c0c10018000d400c140f0f40010b142004d8903000a05041c200140d0000c190050b064000720820798006000840c02e008000041103903d07101c2c0400d4035003000c6840d401180d241c44481149002e4202c00d4011342e6507001c0c0141000407075000070001c4202583c140b0920450340d50441e45881000e40501c1c0031500d000c1582416400d11038500c090101d1032400107142ca0030054425a42e6115480882d00030030391084202540380840002c044148421702c0c00d0b541400102d014100ca00719a00e548043e11580c1000382ea50010b9003c550b0200c0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 971425377 1250 971424127 971424131
    0xc05070f0b130b040e040f1b2402121204060e1c23040b0309070b0c0706090f030203060c030c09060d050f060d121d030d0809190507090b060705060a 65
    0x4154401440b0410b4000705074410f00d80340740c00d260110351014000c0c0034000030290800d0300b0069040c80388009480450b0040b4150080030181c1e00d03050300c0c8401c00d241140403541c81c041e01401c0881400030890f0703083c50380420300310303441c0c407603110220444500028022196141e85484d52110743e0010800104081c1180032043e038aa11868805001c0001003100c4080214807814a10744c0d0141900075142180d4081e2000e40d2aa2100c180907410900c3d99002100040d01c041030880d920100040d024088030000d0302c6000440361a0704d09440c10b0768082c040690503500403000703d41004462001141d224156804041c09d01c200b4000203002e560022000d000e640e0303203034001d02080b840c450410782c0e0011811a0311515042480c0d0327031001c2c0244044010001d01840c110600c2d08040c03003060300301c41050010141c030b1880103110f9018207200d1041c0e54508007440b84035440c81c1401408101035804980080081948620340300b07441025100040046401610030f1000b1000103604000b030034001d001c28400 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 971426627 1250 971425377 971425387
    0xe0423070801090209100c11151305010c0b18160f060e03011b080c040e09030c120a051905070807050714010e0f2b0302010504050111030105100c05070f0b 68
    0x8024481e020680021074100e104005400c1180d9031110715141000c4181410b11803121036042c803d09003500c0c100c0858020024040130060310760008004e00b1fa01d1f0749043c030202042d0720b410046034607240040c402030020b41c5070380114140c0b02e45244040034118142046900c1420311480c81841d00c403072580b0042d0111034100050007055081102c03032240300015002000040850000981101c0e08034140b40c00b0300c0111008070751204e41e81c00869024254000b0020074900b4015990741e9694003001d102201e6000b40c0d003c101410584400322084000301d6075a46003854400c0105003041c8149806000a2180c1002001b00098480d0b024120b643d00a10240150b146494007822170703501c0ca205150304010304030403141455600d811100c0c04101c019147d0050607050666401c5030640004100240250040303102c0c01010f40c1500080c1c4582d110f90001d011000d050a0a030f500c500080c007035075500945064100844c10322580e00d082e400c500850498244640c0e4074805102c601d942d4005000c0748100240b = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 971427877 1250 971426627 971426641
    0x8010306091b091413020303090d082703012007060b0301020d1e0c02071a13031e1104090807151e0b01020c0d0c050628030c031503120e0423 62
    0x1a20380c4400140d400074a105c202d640041d4407881450350b200e1003240000340740b0782880055411703102421030b1540700351030343e0000d0301c090b20701e000c02c21305850303c650300300788004c5104102e00c4070030740c40c0032000b52080d810600c031a0b84030307070103003082c401400d805641c01c0c00b603138035146100d00408501c891580440c1044018100b03182040d907415012120565121100030007024601d5022840b50b50030107982940c0396000ca4840949040e074039407015003400b0b510784290b00c0c803c490310000c00d012880741e14440c01c80c59000c0c1c140415101011000341076504240514001b084d070f03c07803c4400da2804c0b00710014010600e1001040e207902c218401c003c1c45e030350303441501d91256010044011a501d0440709042a85081c5d038a101ea60030550040394065103001c07840d40365031150395080b065803a1061002d81e51034201240000c00410340290247e00090414407130b82e80210030321071080c050703c1e007011501042c1e0313011050a980c0302c1d0b1401d1602e80c1050762501124241c510a4242c0c15100305036100200303240c18240 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 971429127 1250 971427877 971427911
    0x2041403010b0406050913030c05120a02071401170703290102070501020c09040219030c030308070905010c02130203070504030c1d1e070c0201122f0a08010306091b09 73
    0x140480c00f03146012801c1c000c550358542c1030340d40300740e14031018030310b448075894102e5100c84480c40c028000e2190f02a803004c40300b0444050903800b58658201c81085541f034540084810085418030b001c140c0e0301002e070058040300903103c3e9109009040101d10a03a019100d907001441c40120603880400006170000a50313818004607005240074802010003031004400220b0501016100030b06c2126116514403142201030005802590800c00d00d005150381e03818003400040c0c1c201c40d9800044c0c8000c4020031158064501c1c2422071350050503c0903901d4a00e1507140003548041c040c60240b0000b030000200091102c0c0308000540707140a0f0000b2185000300350a0030000002d015501004200700b00d10038800780c0d02ca1110b0340441c0d146003100e120f046500050320070809085a040459003400605c00e04001d070140c1d0031411030520108802c062040c5902c80c811400b40d0340340c1c500043c8041d00100080b0300c1076001b00c4800d9000c1d0340c1a0440305003030383c1c0c06600d8540d80c0d40121503203521820200c00440d550 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 971430377 1250 971429127 971429141
    0x20904141608240a0c03110c0a06180f24021629281a1203041412030d091a09010b060d020a120c0512100b03010b070807060204140301 59
    0x4a480a01880c0391400ca607201d1800c000c040d42140380c1d4a0351282c5c4058801d0300704049030318010880b15611400b0600c03603510f480c845001610700d5414500c0501d4280610100781c0003064222040741c40c80c0c4c045030368000f9031010300ca03a00d44810011406901e11280705200a0038101c64500300c201c0e1038103c516242488481c80303075601c1c10207070751503800140d5a403454080c150b0110342210301c51200c06034448c045c03000c020f2412429007101c0c038140300e1118252480090041c440000c030f87c80b0150465086441d0303600c0c8030701d01031036030150300d0582a11054203240208080e0a04004142c034209414008108115507450310291810a40034840e8120403c500d6502900500703100001d000e801d030120007203120f500c03440b68174400003540002c070340784503610824201c420300e1013084050202130540c01008100390004000a10001c100300046400d202d81140410f04443e0702810250a5a20381030a038070302d43d0004042541c2c9270034100103540010383d0302e2000700040e04a207019400c441d04140140341c00c503260 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 971431627 1250 971430377 971430403
    0x3050c030402101103070b010b07050f010902011b1415060a0906031707060e010f1d0304230604080d0903060612030c0b15060d0b190b07020904141608 66
    0xc109010150729414001d118544280c1000000c2d00d01c13100d015840c502c5900006000101c0d50000460f22003545401050114011002c590040c485c400403d400c03a4404003000340490840070950702c811000c2e1a0100002d4000d0500c001040100b4517414204103280801220b241208020829140317818126400034000c00d410400000342562f9800f12040c141c01650341800c00c020414004114980d00148915107000009002901e1105c0c000d41c040e00d01400b889502d03401003144d80c41c20560010a880032555a1204181030240115403030072000381c614155500b10104010100f85e03200c00b044455038002840e50307040c80c014070f1414620100c660580000d032402052284007004a580f2080c983ca61540003c03400c4580d8882412104940c00210985a04980007095244c00b0383d22a0b8480b003480e6906841d0000d0642100d02d10010b2044a8083c03829248403d100d072101504000300340a52040c401d461600d4001c031a880c105150a5500040d47d070b05e03111482c01440150300c284012490841 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 971432877 1250 971431627 971431651
    0x80a0b0601080709030b011a0403050a15380402130303020c0109092a0908010f15090203060310150509040f060f02090307051302040f0605030103120c0f0305130509160305 75
    0x17080d90b0b5a41440f0340180300d0300b0380740900f0700450000600c14904031001554040100c03410039189181850514902c500e4445903a454800f83d1075103602c0000070210700340c86d18a01220200f4284441c900e0710b501110909070450b5091244041d8895180640700196000b03800030100d1083c81d80c001002c4076500d41200303403294180040b0318189031040a1031880c0a840c0000210000e82c588000c0b20441103a90011010b50309000c248103c80d103d030f5211803150640c815030341c00c2c0c25840f011005d0030703031100355101a0140e00c400f0031700d40c40059942c80b42049044120084004e5545e40303001800000050b2029159a20740c0e043e240100540c43c070503e8810101018254100b0401c4c400003911801780c1d208690245140c501840041c0c0c80c50303411580900000c58485984036100d040050540e0424003084030380d003004d51813140141d40034001192403a0751100f000100100039940440e070580150401310700101201101080b180d442892248c1310340e807000c1c50110010b01c4040020160b403c09020558010 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 971434127 1250 971432877 971432879
    0x210c03010915050601022b080c0c06013b180601030c050609060c010e1c020102041503020c03070501090623010308070201050c070e040c060e03150a0f06080a0b0601080709 75
    0x1c0e2000c0101c07805441400c00018240c4e803943c0050341000c3d825040700b03d9580040e0a04d000350f1070518040c203822052503650403519500c1d00c0c4504064411040242907507800400100100c400035807035800c1c8008044600881e141c403914900205004036800341c100b02c03484004010b024521481307001440c01010740189103551458445c4851701106000310b074064500090720140d076807101800c441c0303c5e6035208020000e116481c080740e5140e811405881f25041030200c00310004034414001d4509940420501d14150303d24283c003500258880808840d15020601025010940078818402481d02419011800b0681c544280320149809200903418080910040c800f0800da4400d40c4c2c822642070902c44e613655140140b8074030b0f112069009001807680a002c0004010011018400311101600c2d50b080e109601d00c109078542c440107003070120040e50140081c1501c1c00c1a007180380031100105000803d03507100c0408508014080e8002d8621880c01001e015030380d64007046940d8402c007545001d003815 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 971435377 1250 971434127 971434133
    0x1f03080f031909201c06140c0f090105090111010f0507120c0813060e0f0c0a06030605030c100315030305070b1506310e07020106081204091a210c030109 67
    0x80000346058510340050300d07866901c1070700c0d80400703041d840c5c143c0d4210f121440981d1070860007a0100071141c4c8a007003003071004200281602010f88030a00088a1142e08026403140111200d800214200341041340403031300030308400300a100c1e103120301502890108413440c140202030002c080480949800d1842c000000030b4107580801d040d41c001017030b141e04aa00d40b00c0c504003480540107204824110380200d50241c0342c0240d000a940144680c1510300c00b02441d40c8001c00c3c3c088403018814190075402a8640c41140c0c58040b03422070719114079042c0042c07000c00f000d1401c183d005290f0000c49c0800c90009159040c41a500045070340644800703920440360ba00c00c804500e05008807582c2088440c0c1c52000450340034038008503403194224240c0c0c000d40050b5200f03440090302c0e20558a441c0594a021408507a00744040b03001ca100c0c0c3c502d0b000036031070b2500d04020070b401007420540c0351ba90881c1031043c140c8141c6d10036440080c401000580108071346c0c5016000e90074460502031140c460f0b0314004240e000 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 971436627 1250 971435377 971435393
    0xa050102030d050a11040e07081501080c070c0b0a05090a05040507020d0516080a05360d110402220e07090509060607060504050d02070b030402091f03080f031909 71
    0x4000b4040d20082100d0301d8050000d0090000790105c0c11514801050100320040750b00203061258441ea40c03900215120030b11034001c0308484a540ca400a48031000140341d4414107001403003864400c13000002c40c15950302c00c05505e5080000008001040010b0161b29440d200143c40082c00302200d040200d4181403801a6840140c1600c400c03d00c440450910950102c6580941009401000f41e40e40ea40440c40020301c140e206c1c071030a01c100e10007400942c5d00480c446166108005080e131016100a1200081000815814002316846010b14480d0085600d490010309113500d080002003000051003201c41da03182e402a00901c01d0104510104080c580d0302404650440f403054503554440c0d254100400c45030321400310301410081c24a024042082800940940740400170f80c290340c4a10307210035a000c8244803e43c0d010b9070046d403410114060761103c007242c004030615203618068041c0e0303a507584242c5411140c2c011140d1003010080068103090202402c0650711180010080780400e030b510802 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 971437877 1250 971436627 971436637
    0x708010e150c04210c09092406090e0d020607050a0c0f020105090d0309080c030706051923070614130b090c19030611160f080d0218010306050a05010203 67
    0x10801d01100204480100e0310085501800c51030034802907a0812582c44038950301c04600031148080d00d1070307000810b107507140f19140e03850f540420350880c0c1c03481d88040c2404001c1740000d5007008a0b034855001403115040c0c81b60326400800380c005400c0300c13520800080c0c04c0000c002c000d4000e1040070080c404042d40e111f20b9440c035242d801005004c10380c0a41c0012510b5008003121107811200b01c10b000381c145030308400d810044515202c11145020303418428541c450440d40b04010100d4000c0c070084148800204c002078a0a0741450680040030140e01490340085030b05c2e40c2c411030a9000503c00c030601505000d03054400c0b24901a0036902d0030454400d542c442240900603100303083d1000864109402030180c0c00007000000c0c1040c400c4400000502c0c11600c0a00c4121002e520f00080d14207050381c01815502c1c820070210000c0350684950316020981c0702041e508070f8040e441002403c81c4030305144040e003085103101e49c440070020a400005411189580c2105205048114041046a82c0001150 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 971439127 1250 971437877 971437903
    0x9240708130b090313050103020a0c06090f02040203011508060406180c140c0d03053d030503130303020613150b01030b03010e0a02100905130e0c0d140708010e 70
    0x3100d6541d005022040e6030120038001c11165200d0140005002c0020181159100c11402030001710f13500d000550491050b60003041c04104810305210101c0c010b07a02200300c05014002509244d131341e9074000b0301280d05c2600503044010041d1500d010350340e440325a07258086c10a480400205042000701c002902e5910b003100c2003140c0390b042480c41c40380304a40001314442e1001c40f403a11488468a01500c485d10081000002440c14000a0551027413220f2001319002e907101280040c021445201880c10b07403c050040305410900c03000001440c100001c1400c465410043c124880c11460300a007090030203400301e456001c0d001071040100f956a41204084242030400240e1081c0038030040c0d003d0640891030540c55440c1c440e1000301c140000c20525000c42c8200c80310b480c0c0002d8544207458104185c05191782151141401d0081d00311203601600e28100c5903030446000581c00f90010304480701c44881100d4010300c01000c071010a208000d0b1740007400c3d200b4028850f2071841c03038145586100c203407844 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 971440377 1250 971439127 971439137
    0x70e2d0415090606030834080a1106072c010f03023015090403170a0914010c030f02161b080303010e060102160b1207090f030308092407 60
    0x481c030424440d80c03180c145180d2080e41030020303550345e0070314a41c0c0d0303008042800003001507040d0904c44204484018500f076074040255500c4031079a0b0300c4000c07080e00710403501130a20029101032030001c041004a1446642d695540500394040031200d0030360360b0381028401c030111041e481c02e007000d40c0c1c0000c2003440700c04217860010303100c01100b210b01d48500c212a84aa0784551072000701c0e025004018040b9120301031000c0124042800d010030b00c031040e03108a13000380010341e45000050461b04002e94a0760000c06450002c503000c621500d40e820f03007040312641450669514000c0900b155054010076141e544000000c50a052212132220000b4010000040641d6200003409111000090003140030b02070407000c4075140c1da154a07441c00d4040c0f041d10001e016115002000001c400110201802c8e60f18410f1901e092580c03864011611420240011081c811451070101d1000805800d02009502035030300e446240c10300960080c140814103489100c0d980c1c0e846a5224691158407945422158034940 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 971441627 1250 971440377 971440403
    0x303050604150602010b0913020102060415110d360b0a0615020303090f2427010603060b04062105010f02130305060601020610090e0a05070e2d04 64
    0x1400a041e0070030301030100c9031003101c08076030f03d58154000e40c0d100350295503000140e02c82d10114107403940100f800a00503401a00050b001036110301e41030a03ca05454008990301c85000c5810565800c11408812210b40e11840d10184030790404505c0d142c0b1903005041002a50140c0c145080003270503d00151007448814080f440400f0f490780000000e101502320b484140318008002501d9a206030345940c1e2078440d102009800c04408542c11403c0c44208400c210130b058441002140314100400702120440c020129444d0360101c421294150703003005000040310740c15850003104590076030004a019a150140c24015005180c040c0050701c50b031480218109003040c40d1080c054884044020b00c0395002181c0d52007450511140407081d240f1036810346040340e50b08001281c2c3c0c0c103000c0303900340200c50f590403041100070700380c0e48106030490030a0305072206a4100d4441c5858240b00d60301c4000010314040410545921503214080100014521102401c3c500c0030700e1100e61034041d0003c3d095540d0f01003 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 971442877 1250 971441627 971441629
    0x3060109091b030303020c0706050a05091c020d080406090614090411040b160605011e06030e07241803050307020f21010605010f030204080a0b040309030506092a030a03030506 77
    0x100b10000d280400402c680020340300d00d03005010350804030240040c0c0c4101c20300404e5460040c4241e524400042d0368240c24400000c0400803a01e103c8800c20101083d0528400056151a68030a056074001e40303407142e8075842c02c0c10003440e007040703070b0700610400c5040d91401201202d82003c5130302009003107a022500f040030210318099841f4a81c804850101e0005681c80c02213408400540210301074401040f941e82d0320b420100052802014900190f01c240c3c0007803200e00d020b43e219481040c6640c0c01c0318249034843d2482d40d181c03004000d00140c184010710304510001e501c4264403401551501407440140d01c2c55030343c990b680c007038004000e114140380038031107250b03844051090041d0035440e03480c40c0e4102c29019565000340031601800d800200b15410240120703009008407000c5403000002007600070350603141c3c0340020300d024008a01b08000c40c20000046541000b40d03e020b048140e01030311105804400d400804418200780b40c20104140441046656000ca10131000c60380500340411559103240c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 971444127 1250 971442877 971442893
    0x190e0109120f0318120b0a020406081812070c0906050102150a052503020901121e050a0902040e150a110406030207111201020d060f030c052e050a08150306010909 71
    0x2c613100d004d01c02c5034600080c0010340008840c401d40c02a80400c01c075844414140e81684191300418012a044001003103c58642d0200e08581400c070009941c10000d0f0003241160550200d24241d1321481c40210500007488036100d1000100800d000420090985032050050902700500c42c1c6100c541d03440000311045d0071301040d40d098000d41e89582c040004554400360081d009001614001400c00000c81426401e40c82a43c0201440a00d00c1e081014100e0080001d4400145400b20041e11000310f517006071030341e0054943c112811406412100c1020380c5c01c001441000301000b80444c10041941c14803c944d40444054611138500543e6680180c10180840c030050800150000300e50f84074100100010b60103002c0006003c0307401c0c40710640c0e90a8202080348a40405041000014020405841e14100508298180500d45482d40310b01e8900d5103041610782c40035502240000440456042e4013403400c9500100001d40c84014400c84004203640d0441401000c800301d030b8030700ca41d030f080c00310381 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 971445377 1250 971444127 971444147
    0x10f030e060703020a0e0907020304140616051e120702010e240c0d140a030207140f100b12070b0a0c060f0b0415060807180506190e0109120f03 63
    0xc00c0031581c00707061a00c402002544031580d40b000044000704c3c104018580100d001d4040d174020741c011401c081c100349903a1b140010b007585c0c40358032003c100194041320020415044005000d80040c5c00c0641c003000050078185c28140c41000a60040030071030440700408816038008913020b2820301d12150b000300100b1003000c20a00c0340ca10400503103480414004a002c010a59440b411090340c2004483e240c01b0f030b40c5528201105040c0180611000909a1190303001d0000d41d400741900f441005900020f4900349030002c61004205e41000d907035004104201e000ccc0305940801a074141240d1010b022100c1d071562017074000d40300003d1000804030380b503611400c5980071140c4c00c654100800008400c1c01c400524542d25554080ea003801491040f40b1044c5000b5021075040d520348912070365448038102ca40b16141c100280000e0b620078070200e550f44800c03010300720380e031300400710300580010b03454015041daa6841c007064100040940c0034051804901c00c2d0481056000410301d00c100b2141c0380035100e012003 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 971446627 1250 971445377 971445401
    0x501060504030804121109090d0e030a03020a0b0a020f070f060b0a1d0414030a170702060702060a0203041505041b0803030c04030f02180f0109050106031803230310080105090c0f010f03 81
    0x587c000e0041c0e808c8007085041e00e00e0103a880c0c0002c0e100038074041c16203031b090071340000e405a00182e0518010841e03c0f41390b9640b24103110710051034440384007078280036070f00450810748030042000107140411846119035003a520b0304071055074101e868801011981d039121074601d4042c80c021000705080150429041b044c2c04a0402a03d49440390420020008106030001c030803468036800c08990011300100b1298007446c1c143c0c0c0034044999890503480060340c0050030488040e115840c1142540445206060085115a02d0191542c034451507109100400e500000e00c01c0c3c102700207000c07100d0452000c90301200d0740081c88044801050000039001100301000142d5a2001c2c0100305000e00c80e00d090304e06a42c01168100096600c0c1d00d000c4003210640c0301c4514454091552000c00300e805411000180490310900c044080c0e501040729480d0740041e950302060511409090082c80320031b0061a80c032040c44401099004200c0e00000c82440300407400da070512400030140f0030f145e442904200c088500c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 971447877 1250 971446627 971446639
    0x6090a081623010906180308060d03090504050103080307031a100c0807210809160e06030109170903100b10051b03030f33060d0212040c05010305010605040308041211 73
    0x14502c00c0a01900c10400100c0e074061500c03a04031602881d1250904910360907a072041d8651341e6075000d100c541400c40f17500b90148074080700005855500d60199601035031080c81d41c180c0300d051489020f4150340c000c0071854210300c140304901e0b6054440d480b10110041c4685054100802d45080c595203910500701c000c3d0401c40aa070792085034036a0201c80c01c0980c0403a40d52511980d41e0390b05115140c050700c14400b02410610642003185254901c10075420400041c00068550f91540d41e1244855110f111404804400704080106207014000070708d40750841c10080c8205040d200000702d445120799188400d00001151401030008024a902070034071516013200e40d01d050079100600c151030301b01e6440084030310250141411204001454408002918601c0c8481d000d101c00c106261f0001c46907024080e03420301226000f5043c410016020303d005008200880c1c0c00c000005081d150b05810141c280034080104000040c8500121402c8400706001e9603080d04142c600202d250000c10004ea40c840 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 971449127 1250 971447877 971447933
    0x60f0a15050d26120105040b0111030a1e05120a020d06150206060f18160e030106030305030a050709061409060405150c012a031a030610030506090a0816 67
    0x1854951034212001d82c521030f0210040081c115441c401c00f200c80d01032802840c010000c034146908206400001410822003140b004030219146401414603031000444600403611300344060f0020079108101441c12a2070a4500803086030036900180040313105950010f00760310204891350052014042000e40d1510045510b54020340c4d54009a501c4c40c442e0541c0c200011503443c20b1460fa4882e030020000365046070307442d6200303c450440655651818404001107251403641c080c8188000746110303407600340c6c507130500078511411290002c02c04810310038174280c1803105c00d81010f040c1d0000404031403619940d041680211300b483c0604d82c0819088021701c0c0501550742800301c00707042503010010081100d0080c1040c5c80000d00101d001141910307914000d000d441030b00c280c0020002400c03c00142540800c0070b00401c0c58480112564095901c1c0352400b803081100502c9a59003000414000305010030460311054030b540301d041604042d0341540012403007004070301030701d55443c042c0c00030f200d42c210 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 971450377 1250 971449127 971449133
    0x3070903030815100519030b0a0303080601110f031b0f120d0f0501090207060f060e130f05250e0402130c0e0406032001021506060703110627060f0a15050d 68
    0x7680248220301b1078528194148200d1758468450707010400401041107030b8880c91520295000c00c0084c000d6810440703a401403e074103080c00c00c40448032113100300042d5511410030398042c55041e041c200c1c10380b45800814840034600c1c1300241200e503004440301340503503c80051141d00b00070008003440c0d414007800e10000007007011095004e410b00754081c900500820749484458400c542030342c00b4400228483e10049410b001c8802c08580302d0600c90160b0044030442900e80c0fa280030006294406100d9082c0501d84c1081c10340000d55005007441c441414a904065000a641040101440d402035039101d5055500b18030a1804807580e0314094400c10069440f030802000c10705400004843d0174a0b40b4900203015440001c3d55154042c205851420948442041004070703841500c05808018241020444514042c8040c0d4040c3c0141c03403004035090040002c91019032819010034015401000820a0f180c51441000c0d502501c90140040c2c88012030500d0040c01c03500342c00c001d8014458084000070 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 971451627 1250 971450377 971450387
    0xc051501031739150106110706080a0203060f090411010f02120708071a01061d010e130509250f08011b0e030c090c0306150307090303081510 62
    0x603240146070920110080344102c8809102d40503216980840c0d0111441c01c0a40085500c401c400460584030014025000303040c0c5052450314102c12901350000c010042e40340c1144031009500b00c8140941401e0345401800b400310440140701e07000c1c032a000000148680e603484101c00018a008100401c02e081609080d1144083d00e0344042c00b141114186a030b1480c00002d1003520a440c1541092408406076209a402c0e04110022030b002c82034858044107180c0701c016403034064071075941c1d005244100041e045100b1710504040302d040c448004c0f2603080703544500100c0d1040c0001e054000c5050f0710740701b04081c0303040340105100b5400d400c24400403034800ca4221400003201c0c584825180d4150301c07200510f08031140d00204400031b0000d1240c801c4000e000f5680642c1400b0001c040d200039404800100d000508111440c02642d40c0000401c5590300e015104014030041c0d0b410168294030745041c016080e4a0303180409414440000006041304456040010110601a00c281c010618110000d48 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 971452877 1250 971451627 971451629
    0x627061706150f1011030409020c2103040c090203150a3302070303230301030303090204140613020702222f0d020c100c0810140f04020a0c051501 64
    0x1a0603000b55500c0c000c1d1400404a80c003002c0000c02501c040d6264200640b88501ca101c000070709804140300001d0209070620151031304840c0c40000c0c280c011000311002d50130400d0100814049035040c0144404101440c1841c01684c0c0480750050303598483e001d02a20250503401101d920450059012650a5482151404c2d0742c0b0304046c4c400310003000c0030000102810608440c40107a002d040c0800c0464810711030444a42036082c0302c00a03d01072004c4100c4544c2c4240c1040c8c01080c3c031020b1030000c6040500c02c41036040000e2002c3c2e401810900c1c0040d403100c61090112000c6074002c2080c81c19560703040401405840b00c141020001000382448d04080c00c0524074240208420991808008225541c4002c01082c0301a0051414080f002000300030740201029043c0c40c4078654003441220114891007020000c035455211242c0b0f412540e540c20b03503105400c02002204042250101c83e190f03419001040e041c2102c002d0b86884e20314400301c03900c0c508504050264403500b40c20310035501c0c2c2550414 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 971454127 1250 971452877 971452891
    0x1e020901030b191d220201350703021303081b030d0b09280f11120117010b03100905010b0d080a09050f010e0d0c080106090506130627061706 62
    0x35680d500c4d120558466043c00c80300c020700007840c1241980303810000c181c0800c41c0344c0b050414400d80100040800f00201040d05070003507140480b44010903e04540000c9984959185825450b141415a0751640c10825210007030221078003051480b0b02401e0f81401090203040041120f4450170052803a1001d420712658150082032060049090f1440d0100707007001100040c2030000100d100d100401005003804044142d40030b588222381040340034000c0003041181c540550720000c0f94141406500701010310148800300740c1c50400e0700d5010b9140440c0307010420380203102c001180400b0342022809006104001940403c86000a4040000c00c00c00b1303040c181d40d01c1d0b0300c1401c07554403441130125030707400068154046000e00049e0701051400b042c0d191805031150b001440784642d1a08405d080d5038040d0840c80e011611345c810840c0b0f030b051000610511254088042c40890f04d400e00c0b900c50044000f00c001c0103442000c82c0300d8100d081580110000300840e840044544060100180c0ca4035070581e062 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 971455377 1250 971454127 971454149
    0x20d0f090c0f0806010b0c0c09010602010903030506040605010c1b050d050703051203010b030a0b0d060f020a020f150103140c0d0c0e070c1101120e030a0c02030d031e020901030b19 79
    0x8500d80b034400107480c0503104408020308881c0d0800e80d030079a198103c609100301c1c0c0e11500c0140c10300394844818103402400d854001081c1041145800340a82e0002002c40d40941d1806904004683c0d100001500d21500408650b903142c9525402ca00100500d410183e040020b09224004000c0001010010ac0e405002a00c104085100d0058110701c802c1c428404841800d0000c244031891540c0b110b003d980004089061030085995080c056840c448100384040340d01107100c4009035010301982013500c0e0250080c0c055070740700c00c201001e04032040c040503001d418002c0b0030651100c0c0c00c00002c024442d00801039000c0107110301c1c00041a111501075004404001c002050086000d039004207519680804131141203030024004507120643c150380d10405c0f41d20342c0b00f0074141c0d040500c002c01003a882661000c0c088002801490716140c0d880b88094109403902d24200340754101c07191551481c20714104d016940e0700818004030080d00007000c8056105026140090b600030001007a02c00b228054458 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 971456627 1250 971455377 971455379
    0x60608071e080606090a1119121a101b0b0c03100b130e0c09090c07050f0d1b1109090c090c0903060105040c111203072c1201020d0f090c 60
    0xb6803a20745100359101034000d41d81401003203003c5850342007220003e0303101074414206042030822210003c00340c0743ea880840c07206000f0f1120414180101125880e46050540100c411940465090a082c4000404101a001800c0c1c840004811000092a000016141d10b801c02010340c400691060720b042400c2c401350207001a4032212401551143c000d00c15011440a18024403405c920000501350540c4003002c1203521803990f91a6000360040110800050729270005160a500d481265804d03502c107940300d41318081e400c55004001111111050340b492619019902d02008140a8800c00c0c5500c8044130042200030711000604650421003260000c1c8a81c0b996200d5581c144a0f04522617090703000080180b03c141002e82084411100f82e1900003035003241c90a0312810100c400c0b44040540b6030000501209a07800100c03d440c14400708480306014642c0c549940600f20164034260203070103640d49035400841c0030341c140e6000000c0c0d4141880b0303030180300180030001c060403075084940781c0140d84 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 971457877 1250 971456627 971456639
    0x7030507020d110d0f030f060303020c0f06030103082203060515030d080108030a0e0f060c1b0f061213060204080109031101051e090703051501032303030c07060608071e 74
    0x1e500c036002603c00500013484101000300c0d103504000c480ca805041d00c82c03400140401e83c03489502e0096000340d010700b14400258007005010400c0d10b0805104002c14001800814201c0080303c02c200c4102025080c521120319650341c810030a07500103480240f03071004210a2544142000d2002c080031002c1d180b14404031602039600b40d10030701a0940c04c0d803040c001e8400a60044142d05007202c0002c2c06108040c003182c0020b421303940308190b1110340760030207010881840300c801440124030808860203502c08505001060f40d40c01006511248041501c1c0400c190b019215900c06c0c240c0e070007100070f5544648a032041406045080c1040300066010b25580c490200b0621419014445d0201480f000200803040d034038030a00c02030808122406403030000400a1820084181000d180c1d86000003d9072660404040080e084003038201a00c4a031407200d0050400802140c0d4816080c0c2c82c40c607241c00ca581020300041000b03400084051251b200041420403240302400c0713901c180c42500c0c0c082107072140 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 971459127 1250 971457877 971457887
    0x30b03011a030d0f0e130b1215070813032610060207080c09042d05061602010e0c0603150d05030c0c0d12052116030605031914120307030507020d 64
    0xf10f800042d1720465410152a00d10141d0320703008180d00b0045044501d0000049040491301100ea00950111040d0b42491442c20340180e407003801400c102c80d075440c00b08610854400c0407903009040001d10542ca4140c0c0004280340000c40203416610f004500d00048a0f08118419015207000b600c80c6001c0002e544c1c20000c0c45410f007003005000036680b03880c0c075625040303910285141a00c02ca42c603001060300c0c0a54844a07048002c0c0640010f05080c1031665180140000e4130380d4040859040c02400e031005040010015010f0a0980d1940d50702e90301c00c03900b5a410400f01049590111481801c007050240000141c110107040c0340580f41d890581c402000a007040d8004002c000050110104403200d0181c0701400c0c4140304940800120443c0300b40200711108211000044401d02d0f00c080d1184c6981441098080d0070290000d00c0b200d22285522a02040007280007091b40b101c04d0400500c0d003a0620079880b00003240d1402d140c4034100450090040e082c21500c41005110b18160101c40c41d12503 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 971460377 1250 971459127 971459147
    0x426010b06041202040903110a060c180e1f080111030a150e28020c0a0b0109021309021804020703020d080a06050108010e180f0a020112020a1b03030b03011a030d 71
    0xa281c010f0745940342d9900388070103410114815418000c031030403a000c0f454420302462610910032400040c0c025010712002c0e0a000b1907d46034580310a52140500184545448003604042c0e155100302031050302c0340c0c49100d1400b054001e100594286030425048015040245008922914091002106254403951b14820612841a8121914010409001304081481e41e00103021542880c20400c08442d401070364024003003001558440b040c048248010440c1e06409428030780000d51401d294240c00d01d154074a0340c040c2001059001a4903a8012a100464010008090020340d101d032098200a519060003403030b5030f0f01082080740000e081403034378899102074410507102c103c2140d0a00d51503000d1544002c2c200e00001d80000310240d2026020050701088025000051003851068400188032941401207a0b600e140141301242020fa00b024034501040714080f58040e00080d1820304902401f00c21088a030154a418071007180e5026460b048101c803117055044135038990312418103c0b041400 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 971461627 1250 971460377 971460389
    0x80a181701091e030c0b130618030f030506030618030409060314060c07050709112205030d020f0a1103100f1a0105090f0f04020c010204080a0507060906020309090c0426010b0604 78
    0x54101142d0005104200c40d1b6040303547c10803110640002952000101c40121501d1010300d1000c2c0c02c0300c4201903101d60054000700f0103107070500c4581086008641e9a43d03002d003040d41d20f0549a50340140c20700301041a1001454200d400b8400b0036aa410200c2c90109429400c80f11401803100060b41d01800b28116450a135120000b08005840c001081c0c00903c03501e5004598030104000c551078440c40760171200c21048000400401541c80c1c1010945070400381072448041d500149290048594007040c40e510068010000e54032514030324000030b061044038080754060380e107400a0300605001d6075004c1c0380c07002882e224103086048800c00540c0c0500500c00c08550000074080300c001c40e804c0a011940403504041d02c05401c0034005018142a40c0098004200c0d942c0036a00d41018403008005807001084035041c1105042d00b0700000030740303078861003000760701582c0940d0100300c50502c2c1000b00e0300103040c001110310020700340c605c11400001f02403040681310b40c02c0075604030851901d0001c813802c840b0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 971462877 1250 971461627 971461637
    0x1060906080c0a180b07110406090b0a050904020301231501112d030c03120a021e090a0510020a12211104050a060908010f0504080a181701091e03 64
    0x101c0c0031000c591014131a500c2d1004065002000900300c0c0c9004054100d082c81021459080c126181c24801200c0303165214200090402249403101e840302900d40d0151402620f0780e07122581c40c0d002090141c089042410305035440c0e4111a210040300000c5603000700180c0b41108130000c191401181d896906a900040c142c0003c0142120509101443c4d050312140503010fa1100c40e120907030504541044a00c481d850b04009401050002d804122030303409545548114104201240184150b640c0140010040c00000030303c81400d07500c540710a4004c020041034214030680000000751a00c007192400ca07680314042c0740d071302540c40c0030701d4a016401c00d80400c0641e000d407102036020064160000c04034820182048046990380310102103c000c0c00a0b03440707101c0c0c00c2c1d1414190b182180c103030007103201140d0310f008140000504464102d6100010751315140e07032005440c40c450307851508154842c421401c55204000c0310340030306402016506005144034042d0980c1006004400c15202d54001c000030 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 971464127 1250 971462877 971462887
    0x10f060203090a0e1008072607060503040206071106030c0414100f0c060219050a0f080f06120f2b020715051309060303020102090f010201200c01020c031201060906080c 74
    0x840d4400d410780c05180040400d05d0035955040450600d5003036000754400d541991018000d031050450444481d0061900800d801403605034018450300010380000e11411000800702c0600c00f40c011b0080304c01000a21080e07880c18003241e403050717580c400c0c442d2000c2090031040949103171030f104420122420340764485080042440c40100d403a10040c90701124501c2e800c0c008802407030542c0191442042440e100d1a994085061014000040c100c413054104008070040140f092610a03840303030072210030340310880120f00075540c41c1d0504498011560091064101a004c242c6142d8641402c4018802c00006130303020400d0126120b191901074041e40740c0745840d554030480c0c07285000b4030405d6050b40f03071124082d844500301c13800c7c1d407155403003580143c0d00030074043c90b1460070082200404001f40020458566262440100305041081d0000158404250a00c045100390100c5181524003800c0d203603185100b010080d41c0e500203020302d10001d80007102c089484c60203581282c0c002c1003042d54582c108 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 971465377 1250 971464127 971464139
    0x605130207200402070804080601030b16090501080a11030906010513060f0506070c050306090a05060c040e060103090c0803041d0c090d0b07090b070303020a0e0306100504090821010f060203090a 85
    0x2c8400300e240c0250b4208403080201c1c803444042d0001c1c0848901808407545181001568000041c281d50320b0b21500d1641680040c1d00b041112081345c0080c28561301c180d4604600e4801801c0f02c41c040383e00c0e440000b0400081700c5010030b106050b11011203020994142e030700030b10007c8440b02c2c09504954050032909100c1d034074001d0302900c805407007048500c1000d5141d1020034100801a60b951809a1001010004001c400c0c89851380c48240d111086040c6841d269102d401010701410440c181951400d40c0e00502c01d0559485010705035040c00c0b655980ea443c42210104403055201c10f01102400c1c0205862617500400c0360309207003000b400700d81c0d0600c864650b050a00d030051303e01c000740440d400700080c07111031080c00f6010303407030203500c0050f114581100d018214641e1103245600c01c0e0884010800704003040c451322415034405540001d201d018902c0c14070f8045c41400b81c07549540840031000030305080d907944164143d81040901040240d95003401383c0c0c4d280503c1040c0351b840f6001050a1051b = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 971466627 1250 971465377 971465423
    0x91410060c0b0c07050706090608070806220e030a0518030f0c1509090a0c18050112091104150815041a130f0c080c0603010b040b0f04180605130207 65
    0x400c0e003444076842c000041e41d9403480c2ca0346e56803084011850344e40d0b0400c420b82e00001d10030392040c0503081080040c60b00400080501e1010380b01001c5052003071015581e0000c00d0b40c42103000748054001c80c0c3e41d403400c80c0c030302400942003504c0f1a4103000901400c0314081c180401c4203a038007240c0d40000d202c86800c080c100007105009103118091020203100e9100d8030755a03120042c1c054250014005200701d583c0320003d000c529102500f404914001d030341086607903404111519104000b072030010340e2107014070382201c94030403441480b640941000d03484092009102c40d14000c446074501105e22a481d6a0b131108000c100840c0c0281005102011540021003582800b035444402c203031980c1d03491940d6503600c081442002a0568203848098824801080308001d50403c080003191b403a4110342c03401041e01047d00c603502400640c42400b03c3c008001019100646001d80f810101d0041ca11042030100401400d640c428188074941881c0c0148606009100b12520160000c40e01c80c1c4203da90300012007 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 971467877 1250 971466627 971466631
    0x140a03030e070f030b01052407060605010e0904030e04050c16050705090915040f06060b070b0f0603010905030d1d2b03110d090c051201150602060915150a091410060c0b 74
    0xe92300b056101d04c01103001d4000042101612411001902a007040001004481c50700c0000340218038803000d00001c6a0401904c0140d201c2c101c40100e295600c55a50090314042ca14001186215111402d0200b1a000c6500000c3d1482136803501800c2ea03602d070340155981041507881c04000b180c10042000f15010b01d812507000ba000704004070700c00381ea450340e1440c4d5038001c41042d100c00d0070010034010030741400613505402440072002400a0a01511059100d2183c05103841d031441d0760340100c41a000300c03603185420031038a031000d50b80d50440c0000300344400846c69900b601e0802c03c0708004040c45010b442000401944205540d00701140040840e0040c5079031281135499415464001480f5036840a50007400712092001082c10f500703215000c20124400d404c40c10942d0449420032100308400102004183d00704d05400d03400d80c859800170300e4a0381c00003e00381d8000c003040300040340d15001c582041083c078994800300e015a07a1a84a00e01240803503010301750015007105605401b080342190207039 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 971469127 1250 971467877 971467909
    0x9110307061b05151302130b030706030e0109020405090604030e19151205071110060b030402130f2306010906140d0b0415230319140a03030e070f030b0105 68
    0x201c5920500d03605440c1035100721115014520003480100031410f250700d4661000c8003104084c051810088c0001e5190044c80c0a0501016501e0000d14600c0e20250021a48182c000d4002c01c45403c15441e07064881c1d00480d0b040e00803500c000d035548400e09100782898401c203d2202618000b03818500d8440a048002501c9020070a8100826942d01e44a10071140511000c0c1c8404503405240c015190600b22440c40c4500c131240782c5242045101c4075001141d610a0b070488003418943c0050f000b80000780401001d0001c11803400800e01040000c800b08000598210402c184030b0b541c520004403540003c50140b000001c0c841e03002c40024040040192258182d240d802282c40421034000c2000c9520001d9501900714030300c1e10400c08122100300c2810052550070b00204841e104c40c01190345c2e450301c020a550718600081c006000c1c0105403130055400d010400c00c0e03a1034000c16040c01009825034045081c002c0c01a4440088c14000c4000c800c1c088a40c08022103009a28000400c004104010204c0c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 971470377 1250 971469127 971469133
    0xf03080a0f0c0215090307080c03100e03040e010e04060e0d0e010302030925031101090317030406020f12040c12050a02092205010507080a2304060f020c0109110307061b05 75
    0x12001a84c5a808994141045203141611240c0340c6040620749074550380075860300d4001412000564802143d02a00343c0c1c3c0f0003c000c03030718106034040c080c6180300b1540400348014401c4000b00d1031106c616501801140900360501c440a2854001030301e074803915010b00c020407510019190316500a802541e4090f10000c185c0d51441c40d0080b4084002d0010b4000714000f44903880c0c00d108202401b111f92900c01d00a01e8a404072505540e0345517410488803080080180d00400050100081d80c0c04a480c1c8944007a035640d01c488604024070020042070700d00b12406000000040f40281d1410351340b41cac8003600400100511402602407103038460010300307076180344c002c014000c103800448180748100061107640000342601c3d21840040ca4041e01030b105946490402d0754985603107000091417403c004186101200302d4642d423030a4070061107420300200450b8004507400300720b90f4040d40001c18550007010b0383d40d400c1c11440d0400d6110040c90050030702080400d428900324024580905100c00c1c801c0703040b = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 971471627 1250 971470377 971470397
    0x1b031f110a0809010c020111030109051b04090e0d020111040e130b04140106050102060c0f0307020c03010f0221040c06300c020f0a08191205040302010b01090f03080a0f 74
    0x140c035005520988040020808210034094282c00034030903c100d0714070900c001c0000b0b0340d00c442481143d11040c80388070702c165114004501c81c0c0c12041007448120310f19000c103542e0703640c0d80d14143d005448010b01510b8140500c0c0b13103003110b0a006000700d44903402c81010840ca824101101c450441c4006410514118141079021300003840907a0090700440c02103007080030840e080c8000900391034031604094119008602403003000a00d1000b656050480d41142507149c0d03681c603c0880c6001e00505034242d05600b841ca041b0b00900065000b02080917600b00207450380500407000b817404841c2510028040040407078100000b0703200e4288038040100c080803010000d104100f400c1c031b44000b090f2215080035501c80030340a01980400517400b4840c02d44003e890781e0240741e00c03040d4103030243c1c0c1d00c490280300d202e05920b001c503442202c1da80e04540340703841d040010303003480c1c10020b000380302d240c00090120b003410001041c00410384c51100c003186d62080900d07103003582055007150134401d400d0040c002c1c01403800d0 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 971472877 1250 971471627 971471651
    0x21e0604261501050a06030c05070f02311521021309050318030109020d14070f09020405030d1103040b1c09060f050606120408130b040b0307021b031f 66
    0xb6841004920441114465060800300700c0201d00640c413080605140c038250440481c0c0240030350708040d800140e800c151030001e001041c1200405070500d1860110700440c10703640412000d124a607900240c50400031400414500c840c1d1090500074008a4450341c0b2172580c005810700442c0c1040361015180c031101d60310654580c000d461912000311040c0c1c20124840e00c3e2450030103d0300342072010440003070203070580075008150344100c0e420b0060700d203049610080c902d81004000020050004210702d14031241d84401c910003d4000d0b026092090144000e5080b8152254102d605030003840c2010351302e810320300040c1003000c2e4082c0c40c000741c03450b80e8440710501c001d046226000d21103002c1e082c00314070800e1420100c4111540140810b100e21018410340640c002c094841eaa445a405586d8550b603548005040c68030162030b500c500c8888200107004100012000d001e54080c800a8084610161011403402050b0500402150f0036a00c1001141a03446184074148bd103007500310400601103041c01 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 971474127 1250 971472877 971472883
    0x210903030c03040302010f08040209181c0c0c0806070f05031f082d0c0f040b041503140d050a120e010c0201140c0a02150a1413021e060426 61
    0x203001c1d440190408201001507503048041410b00349070380c0c80c0079000c9282039400141440340240804540740c84503440044444000c1000c0b1b40e50300c460480206000540034001400214030380000c8941e204082c074001a009030010742d1600451180c2c4912890b80d01400048905400003440e0004201d020280d583e515a24050071101500843c805858080301c003450f10007103207540c4d8184140001104400e13218001012441d42c06404044401c0084410102c0c005000b4102031070080e544185013211180e00045400f0034401141c0c880c00b20400002060181c0d162a2104480c0c6040894020001c0d0320000f0711440d00b9902e89020310400242c2c2d460b400c002c02c0c2c01c4400c11108840036079520a411400001921055503118840d007140d14a05092502c00a40f240e40d00240c40044e00c40c02030110345044400c0e08003030000a64039041d1101031804082c542c500c9001c0b2401a80504488503041c0c0c0603a80250380400c00320703000380590b89000d01d8401c10052281196019100707084850042c402d9908080c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 971475377 1250 971474127 971474137
    0x10c0b0a15140108041e150f0510141e0414070932121507110304031104050414032b020909040213020706020409020d06060503040c03030315050924030f21090303 71
    0x310f030300001c0c240c010754a28400c6840241c8038156052040c4e00811012200c0c1d180c0d49960501334032081c0c0d004080f01a902e15581e90103100a07400303070418004d1b001e000290340c0507500c5080c42e5601d00d006d03180c0e0340341e05400c81c1c529108a05008420341c42c20128914801c4c82450960740042c20716814080c02051031800e180401e501980c070368041506200f402a4816240120b5035121005146040d02d1a501c49034011594030349140134503207483c009001d0140c12840d00502c08142d0381600e5035850010f09003c2e80b1903107015001d02c00c8441d030165114020107442555100780018240640319200c40e0200440c400c010542c0d070f014039400f080181c0015040e40043c200801c540040980c40b603800c14034240c181c4009411540400c2000c0c02000040741e01e6400960450380c050030001a003201c2c00002c0b800816440e00181d41107d482d105120f109541107040707241c21007111000d094079040343d0b8205520341040f00f94a5540d98001941858800800c60320079842c21444c1108903e0001d02c0740c08a8195004 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 971476627 1250 971475377 971475413
    0xc030304030c051605010504140d0206040e0603010f0e0a1716060e0f0105071202090f09070804020f0a06020a0615090608070f08010513080702010c0b0a15140108041e 73
    0x402ca510070000d0420a04640001c0c092076041d0300c0c1e042500090450059100b4444020b41642c044a030701d8461850240a558025041c0b591716502d6500ca044000016281d09000c1c0d072804d40320241702c1000340b0a011400c01581c0150441c041c65844a40c20700743c00204a0703034102020056510512520b43e41d5507a507d01c00d0001007030110120202c1400e0207810401c21200343d0414007080001940900c6055540b041903400603207680400d004213034005014900580c000c0141c1003403210054005812034441c41c822150512031070b010006001400e11709114000160340524162000140540c004a00c9101843d0400304815610028030080d11400c1d40319800c3c6401c03940090050510000703000c4003811055000340300c14285400710017802d44202002400c03040004c1540002c580c41400403a10464200c484210700b824240350000083c0070070028820300c080081e01c0080d414280c84e0380320380c03645016140c208060341c0340d40f00c496107040114403051001c0b08550311140016a030206040c04205 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 971477877 1250 971476627 971476637
    0x1060b0d1d0a050c0d0c0504021b0d21020f12071106090f0a12020321070e0904022809020703080a0b0f030c0105130b1902010501060f0c080304080c03030403 69
    0x15111040a0031036010440d501d80e41c0c10224000010400001d1610780115054814200f41c038002d003400c203c84111a00300c954050b00000321004540314000480c1f02c0d000c4804c050311500d208651099070340440c01c2010509005031000482404100bd9010b8000d401c5542c2c461481c002000c2c0c00c84402042c11945a40800d1981c464403da1140c04c000c41940681540009e04601d040805004e5403540403101c02000e03300030900d42c10b04140b0a01c01d0b030326074081c21907041000740c4a45a12030b00007141101d82500192800f002401c1f50b141014580340503c0d005444181462030303c000e240c2c180c4002400042001030040c0000405070828801007180c240240e64200382c1d814030301140c0081d20148a0003905c1100f0080c441e0109a801107114400f00409007084c0396180001c0c40302d00003441c4142e1100404482c041850408000724040c4000003030358540c02017100740c1e210340090310a4400c0b91070203400030340d81001c0d0030b0002d20200003c47e0090700a40c001410200882d003c5440c640c002c484c1140028 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 971479127 1250 971477877 971477891
    0x9090617010b09150906060912060f16171003080406030b0906060703020627011503060c02060108030301060c050a0b0c0705060105040b0f0f0f030613031101060b0d0b0301060b0d 78
    0x40c402e00c2807402c9a8411902024581855098000180443e810720391082c0e80c103901103645507035030508076800203030043d0840800d00008880700352115421201604400a00700000d01003605002862045054903240d006003244881e40f0030a4007540144005a500c00e071078000b00120300c401c0003601c0281007607540410494404002d000261801401e12030003050144040d00000c0d4001c10b52560012120443c1a94412401c160b904d007101c0d407070020301c0d140d480c00e06ca50316052510340043c001d40740100b5060002020104049903964800d104184040c3c00500052240d107200342c4851000070b000ba8100d444903102a03c8400480e0016520b024248600059203410084280001c40c0140401c035800c208030b58540700410000c00c1d1f12840703144151600f2403490a15592888090000e043c0941140d1440c07402d007003901c0d6132180d0b07a1411f50211b017609120b540381090502030081a141444202410110780101110151946040d911b03815500c813000411840f1f08000130305141a10401d0100d000c2c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 971480377 1250 971479127 971479169
    0x601320c06180703111309060218040510051c1b06080103020f03070b090f1306080c131e2a0302130605070c0302060309210a1d01020715090906 63
    0xc0b00305001654058004140400201c4c50140381d102c1e000b0001d4806d0000c0c00e4070100c64034014005600c00504c0140f0128800d1541b50303aa0042022102040d00c08100c00e89403003003900429500f0b4482c5940c0710a00800c01e201854081c490310491601c1910410600403e808030090140c041d07801c00c1001a24040040066160000c0d00407590300b401e50280c0384260a02414641c40e2281490441c003800c1180c0b10160b03951140d00d280c0310319a88180c801c1122540350364180b500c414289600c5849501449807030f103c40d4100b0f00c100139070b021282c40c400240040c03041240d000307002c280034848007001c2a07800d2046e54501c0310385d0070040c8034042d40d0b006a90301032040681c801001180c01c4003007044010300c41200001e14080e602c200f525011207046449039904601c10b071900c2000b00c400e05010204501410802c2c07800400b40000310380c151035505412024541b0030001382c9a0079082030050f880340400f00801008429904151641c1386062726803607844480c140103940e89940f01402c5103d80070900406 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 971481627 1250 971480377 971480401
    0x6150c02060f0315131a150f040906030b060303040b18040b03160801110903030f130305030f041a03074d010605090907030605060307090513050d080601320c06 70
    0x41c90500180030040c0c030145800d814980c60780c10580c83d0141c080c00c00d20b47e01c4034400f8410307170300142c403410b0201d42d0b503e48907280280600405e1004940e021071000200c1c5080c54040242c1c0c00b0b0350302c3d405020b4103004891000781290445102c0564001781c0c1c130540824180c0303003401860f5035110b00e02d003010b9241d89001043c80c2101c2003610a20080c074001d0150340242e982c04001c541c1640154094261143c02800040c034001d1704990004009210002d050f0602c400010082c004464910039020240381b201041c2c405c85101c00c481d8000011030400140f000400400c201113040000c000078040c043d003440440d110203140d61481e1800e03904892130340032201ba00074000c2002070401515140324500301080c0c015640c15007400000c1040780c6400020300907032810000b1000a03c2c00f602c060000d402d003030f4074920300820120000d840c00e0080c5001c29455030b0242d1030031f90103010306030740e0310641c2c10000c010b1106600840e080c00d18500300d20103022034444a14405841c4104990303000d41090305244c0343c0b52403 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 971482877 1250 971481627 971481649
    0x315030c080a15061d18010213090605010305010b0a031d010c03151406040b220308120f1b0f07061505010f020c011205070315140f0406150c02060f0315 67
    0x110f075070a1680601150510352044061900381e001300404540700c241d46c100c941c0640f021200f42e10340c40482e0103d036052001c40b0440031500c65880c01c200c1281c580e801141594424001d59800e0042048038244481c0720b80d01545a40140c1914001c03144d440c14031043c01d40f400b80c10351400017901d805002c012041e2000405006100c03a0413651814040074003c9402c41c052403148030700c04000403840705101c2803201c8401190302104c12441d030a458903850301c9555904142c241086944002c00068107403080b00041500911540c142c4500301a00222000703d1503000c2052543c459505008600c0000c247e40101e041d96107960840c0a20542010001061140880340703000440d030110b1441101a6040314100c1d4800041c00000302e1140e0707403184c0540c090700306014110309012840300c0c0011549d030b01d90340090701100c081340c00320210300d00c40c2e00b00410303181c0303a000b1000080a40c01c11007901a000303126040b052031000c0c2c1458105050702540222503007040340c5c407420f40c04281e04069540c2c034100c08101d03 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 971484127 1250 971482877 971482913
    0x908071203030b030f240c09010e13020d09060203010914070e0603070c02031f0608210307020c0a0909020306071106070315050d051605010e09070315030c080a 70
    0x989840a00c500480c09180090141a03031824031a5081c0c60a02c2a0036001c0c40340411504071004003500f41440855103107001c0c2c0140d00a03808610084211b000712200400142d403115082d0004004100b016148080c0103d1800d03400c02c0090100762282c00307100304003801010700588a6152500b1202580c0c00c1c3c203110385481080f42c3c10040229003010305440d100409441061716a42c0e009000c0c0c44114980d180030350300d03101d2a00c90003d18202c5091054840c8c0304440c050000c580e42c0c00c1140e07030352654108900c03848400811440c81242140001e1644104544110f40d002600d00001c14421503071a0840307441d0304d48036003805055060400c40c81390415541c3c81d24450316054001c00c2501c50720054204400c250700d4800320642c90360740070410b070301521008112480007074075450b003183d6070350030314002e56000000464005201d600400380c01c50078030000303003800480f580c07501003c4000304503103070701c2c2e2072450702035200400841c200c401080050450b0000400b814411800c025050b10740d214226 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 971485377 1250 971484127 971484133
    0xc01062402190308040203071a180102060108030d020c120c031e03010b12040303110a0203040501021612080f070c1502211611030f0c0a060f0e0603130b010f060908 72
    0x420740350b0000701d14081a0030303010728104a80e80c0361440024208166036005003611001581d850905400c0c2c08004c2c080c445042d4840994804408016078480d1424410890789420901007005490801d800031700d0b9241003074081e103900c1005070b600c01040b60010507c6072416400411507101c400c0a89003050f034420401d00e00d03103041d03614284601c00c0500c640e503028003288850300041020036019800c900c03202a68148550f48a21182000940d070390010702c40c807030040c407445442c5100c0b18502c0e00c0070400c1c1c07500c00030090072841c5240c450002941c8810480a180d050402c000008110400401c401408041c0050b40540c108002d000b80360020351030510666080d2024088604c114140840d114054500e4030284800c800f0b007043c001c0010f1070b00d1056058058103035803266100c0e01180302488503004072814035500d52616011242a50f25a01301c2c2e0100303400500c10b105c549407820283d44c5c40503410700c241205807090750b900a841d5030f0a80c80980e80050300441407002903005010000030f04202c00007 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 971486627 1250 971485377 971485393
    0x9020d0525121223090a06030b102006010305060f0606091e040603060e07050913080337050703180305120a2702040b090115140c01062402 61
    0x1903501d5009450014900f0552800d0154400d01036100d001a001804c000c40e80400c09840700403541e03a000080140c8501d09040300491081d01912070090001000b4169002000c1c605505403900e00100c0c101c107140602a40041100003010409103020b58805c0c1c010b001903003495266138020042c05046184101810b200080a60300d4410000d141803050392042c07080903101d040401c00030102c0340c2010b0006420001d00f46103403040040c45008481041e00c10144642d00c0c064440040d1001c404d0090180f402000401d03490311021508400d044421958200c0107804d4281250301070400c901c0c0c10032043c0c5c0360001c0080c0b03e82c0502c504180740c0703440d03884101261300c95900248184564414a00c805403108040b60350692903a12840b0030710400c450b0050200e03400300c5011035a80048908034855400d0007554140e0382045000c02e4102d078020a0b07010030080703020a003510003003200d01900620790300500c02610315103c00d01a0310010040c403d801203071007200e0314280c6a90b1050841c03140541d400509 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 971487877 1250 971486627 971486639
    0xf0d030e21030712060803040b041401180311041b0e030f0d02070605160501020403050a2901090c02100606030b090c07120807050c0703200a03080306060d09020d0525 73
    0x40320307400710035460068080700d4504038050040c0300e0f50704014043c2c40301007800704521b27441d40c00420079104010550b1803c43d880780b0045580341903081100142d240003003010000100302c50403001107d03500a001141c5440b5454215441001f00f1000740006090200754540c40e050074001e40d15044d00303a1001e024200704d40480650b90305403d10a5108010000541c503400311800710b80407820507030040095655590b00d0800c281d644990b480140c81429410840c9900300c2c1c0c10b4080c9840c60551102c10001582c030f0015030000500c0e00080b050b00b540154003280e0700130f0045100d00e0700604110303103001441c1c544d50428042c8000004140c401904410032080000c00c0601d1683c4100c0032052506060a68500728101c6507401468030340300c150b20603940048204a40c0c06031164004d10142e180038181d8240300304218010b01d103880701512038441003002c41c049080600c000c10000300b440300702180304130913580070440b40b000c0300344290b505c2d811410740c1c02c0014220300c17280e04502c001308804c59602400d080d = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 971489127 1250 971487877 971487943
    0xc21070f0c06060305071509080d212406170402090105040e16150f05092209050a05030a0e09010e0c090406150c03181d090f0d030e 58
    0x5a108144241c501c10032040000d90781100024541c0101551281507442c2018010f0b80c82e590f411030007055080704042103012001a004942000a42e244003c44251001d155070328003c03d065504c11640301d940c194100c05190420100c150740400e0036803601480d203900248814a03001c103814403000d080c018040540d40e03a030b0041d41034483c101e4001441c001040503013480d080c9981132180344112101780003d03c200c40e100c0f10f8585084c02c0d442d48200ca200c0c00604031802d204140001d07511506140301960700c2e40c48080d50a448030014035002070700380f5060b250580303000d4059034115010303400010038a40b00ca91041028500d190300b0b940e0a01c0550500d6138280c00320034020302d500810100410481c05c15915600103600404600c0d103a882e00e402650380040a1400666054020806c00c000c1154007051082c1410111a0712101141c00602c0714502c0b61032903600901401c0310380c86416801e40c0a000c2c14000c0c41803108150b240000c01a00440d4040e00301a400c0120103e1000d40111864140c10340b4 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 971490377 1250 971489127 971489147
    0x5010b1e01142529041712070c03021b030604060c020102211f03021309060f0203090f070f15081008010c20010204150e01021c020f060a0513121202030c2107 69
    0x10000f50910420325203d503c05001d4080324105004c04401230181e480c0e001880304111034003e900392203c3d641c0860b003c0d0312047e618000d80c2d400d90b00040014000c940540c1c001107007a01e4a20001d440c0a16240b82060410062241001000a0f0f801030140a4a400442440c0c03010781c01c0b0700c0b0701901e2658000a44041c601d2460490a5450b02d04203810404180d0083c4c032104d104900440d1203081903002c0d42d94aa401700b40c0c00e1294403910401040d07511103010120304881c0a0309056401c210300d00720031100c0f03c0c40130781120024031080705c0200d0800401e0068040c02c8503a81e5594800c1618000e5140128000064070340c1c03580d10400c400d000600e101c085040c41c0b00c04ca804c080508192400040b850102c08004c402d803050120500303c01c440d43e01160302182c00e000d031011605562240d00c2014200c80c0143c540c105c040842c0c940e800001032a6403500d0700d085c1c00d18100140403007948a440010f0f644210341d03405801000065210b0f0071b03000c001d1581604000c886a64001e07103007080001e4284840 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 971491627 1250 971490377 971490383
    0x6010207060c0309050a150807030b09011403070f031a10030510020702061b030309010c090e061513080c12011e05090a051905010b1e0114252904 64
    0x201c11140d40603d800340c001800100030140c103018500399901143d8880701461000100042c0c0800302040380c051290041d004090001404026141d01e040e043c0509202d1840d0102d0f010300450000007281032040409900450160208008010310350440014540004020b0301e540c40807098140040340c00044c1c16203401d100318400580e0380c41c540c0000307800390007900d4085050168441c04080c03c104003001550080001000030701002d030650ae821f8446801e140100c820003040100028424a0f0100403840203842c0100b85514107a8210740045501805401c000003984c42420054100d003842d0041c641c24009140082241080003803500e1200745446102400b019100e40200d81e188100744242c0450583c45811120600307011400f000d049805000d0a4a070b40d46000c5020409080900641c003110400102c80300283d40e2000c010748025001c141b500280c004203101a2071101d000c2400c6e844185403d00d0740841403d068900501c0300b8640840c42c60001c00040d00209030800e515005503003141d4 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 971492877 1250 971491627 971491637
    0xd051c02030604181b050105041404050c0c0313030201120501180c120f050a0e0c1c050a1217010f060f0318020d140f010902060a180f0602030a0909050601020706 71
    0x40300790006000d003080c010600c3d04a019603222008001d00c070b002800710951031759102c20a880c0d8440041d1214041d81c85007003122503840c05600351500d40343c0c0c0706c00e6000c009058450f007004400110700d03185070010400d007182f0410032a0140117568104071998007000e210780082c4901c0d0f0509003680140380011294955a40d00c8605142c1002d01501d45c8103100100082d042000b61082e060203000303030005455590117507140c2042440c4c543e0000c5800300303040e4000b4000318101074020110800d050521217003554140541c2c1558030024009803590160885103540e42203980300d8200340f0800110b0103911130171288403900010011241c0007400b81100d6502d5007000603c1000b03880100441824034100203600907201c108075030401401254040000080f00b0868550302200800a8221044450040e51100301884800202c03840b405100b580c00a054900860b215562043c0f4403602e1059000b00d000f42e00f000c6280041c4942c0840410000c241410701070249050130700010b0345a070403034000c01003040 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 971494127 1250 971492877 971492881
    0xa0504120c0f050d02011a0f0102030717041a1c140c0d0e06010801020403050715050d0b060d091128090207030908030a02070614311a030402030d051c0203 68
    0x4800c285851800f500001031391020b11108000034000c1010b0003004184680303d030348044040c284281d560300280c4d01070700110b05d4240e854450f0300d0313213204100c0e803001c1007082040003080102800510040ba040d4000081e922240070080c80d080c040c02c040304901c203417880e102e030304c00001002804154001240e2200541e0320701c03100d98060060030822044c540c251188500002e2130900c15030080049902441c10b4400158640014084600f682d030741410000d0001c2c85160b004030b5071580a0404058000c00052600141101030006d5441c0907200743d0f1503510400b10036015003024040328201151541d101e01d078408a0b08036400340448180145028954081074840c02c0500600080f03006e00744040407241c880d240540025507030041405490b0004844140d034401150711201610095548051007c84491065019407092103002e403501600c0c44031218002428910544203644c080400003401c1d17a03919282c01403500d4116a9404042000300c10410741e400c101001801482c2445080c10241c0e8035 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 971495377 1250 971494127 971494133
    0x1f030303050a09060e0a0302120c0303010e071e03090b01120312050a0902030714101407020d020f10030209030c0109080604141c0c1401020f07021302220306050a0504120c 75
    0x4100f0410010240f41c07400d182040405800524800000d2007682214480d00d40c154400321a0300401109410551050005104a0b08680c0b0603d0b804001032500d00440043c40c00c2c14010f6030f44540c101d44c0032075540d201e07140a105025000a001d803046480c817030907400183e50020005064820011a480e6840021890000c0c1c2034000f19440c64000f0b003100c9525861f91400303106040510407181c4111040c0000410b90350080d0f0200420f24140545181050710640038082c44461080040360300507443e003918012541c4441803480f0a11007039500589800f010428145000400c07442c05040c000550700c2044507550006003650f00c25400070b080392002c50f8103c085032170305200002c0c0d4001410040c0f0802521a40090740c501214000c4200756540b504030384c569800c0303100b0300e45207518003001044030b5409802d0050134168008044c0d1070051070083c8201c40100403503480145000c100000220401c14001035020302030b0015010724040141d82029600c02000c0306400f184003051140303005a120038 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 971496627 1250 971495377 971495381
    0xb04050612061f0503071e08060904140708010209040b030f0d1202160308091902130903090e090a1b0e04060914060a052202032512030e0103051f030303050a 69
    0x1982e50381c07584400c0490f0045005440b0350400c641480000310ba03400040500f00050b0480080300d0f0068444500b41c0d1200c00521010880040c07056429840b50058110800010801d41c00140038840c00162507006150400007a6070981d229035100b81d010071070b0355044000c08940c0080004071814801010160b102d5008041d0084400300303014041130400b60803d1580100560303100e03005490560303130007031903800388a650106d50040c06500820001c1201e145503500d640205071041c001d04042c1000d503900c0c4910500d103075040f15000100d810402c0400c2c1001942030007000001244101c130144c01d8180007003012030a4000340041c00c40ca866200034400c0c0700f1f21403c01082250944140c0e0101e00d07104481d13002400c401d03100d00804034891100c8070f00082100c5401d0800329402070103410f804850310304100c2d8032a0400e61740e42c1c00c507a2408000039100f1318010701c1c50300540b09466000145143c50300140031650000c15001502500060320441541408402400d0b03990604000903141c41d86401880 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 971497877 1250 971496627 971496649
    0x40e16081f0501180e070b04030303090c081603030e030a05070810050907080c0415090c030515060705330117070501090b0702130b2e11030a080601020c090a150b0405061206 76
    0x1031680400a401700c0ac0c554160880d0349054069254680515a164040e0356103003d170001c201c1c0200c45505081c4002445121048000180203049585200540d103550782400035560101000c1d0b405007603040007468440c02020760100451300540b48661030407441d907403908494183d0900c80c6030f41308208818030307202205c2140900f80c02d0a0410044401c9040600200000e035081c03041000510007602c01860000111890940e20001410f03d078840201c42c5070f081c803610300204c0c40504862040490312614074002c40c1c0204075070402c42d044400c8041c4540d042402903007009040150a403410701c410385010044490140c0e0540f800707000504038102d648000c00c1640f443c150b11030800040048161800b5000081d4001214829002c03068000020f031050080c505d4000004e13001401070004003400380004035407209040c0161000422804005001c0b0001200e000381d1080d655001c542c10082c942e81030101508803440228030f4941400001207940c000d40c92500c5400d074211000403c10703100c082d1480c0c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 971499127 1250 971497877 971497889
    0x1502010207060c0c020112020405180c0f160c05030c0d0308090c060a09030510020a080609151c03080f0126070b0c06071d090402040e16081f0501180e07 67
    0x880f54440c1007000302908500350050740050142141059114128070844045840083c2007022080100c999081c1000e4000d01007401c03443c0230300107000d100009400a0008428000070469a040140303040d1240c02c1319500101d02035400400550920f4a038411a1030f802c41d0075040c076403101ea8510305510700d429a000c4049030842c00c00f05140c40c0243c0c0001070310f000d684c4a58190f402030612b41603800308901400c21200c0c002009240030170480e041c11031300160820308030204000c0c0306080c2404200340c40c203100c0d5050b031034650307440a0302c05140e4850300300d40c3c1140103a03c40070303401c0d403501e0300ca11020000209200c7c41011001c561201040b0308110440041000d0010305031552421540c5075107030001160a4000300d0303482014500040c0e0881e640c0c40a0b86c100038452105a1140d400b848000c1901c52154960341c03040d805903004000106400d034004007c00b200905020780c0e0003415034640065800b078089038034108001031005c40305ca00e400c0c402d5000c030349d00006044c0e8652050145000020380c000 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 971500377 1250 971499127 971499131
    0xe0307060905100c02031602210a0b06040506090912161b030c05060301030309061805090f0a0608010c020c0405070c080d02031b0a0c060903031e0617030a0801150201020706 76
    0x40040208090314109828001004501c84d030304001d03600c0344583e915034000e003595600c400c40180351a05860041c100d0030303034840300211220010702d41b601c0e444030803d0750f00110340360421026103024007490f94058030940700300d0307903d04013558459a250f029003482c2c209200040f82c04400003a0b071170382c15031410341c2158110b0b4a0610744503104e54a9050b0b03000030758a920031124003166500f8204100da04072079140d607541e902e0f1440c10b02c00301c0782842d0744400050604100c007070004866580d001414041ea80c950030303000031410501740301402c5800c01d900074522a4180802d080d009a004a5484061801910b020950340d890400490350480d10342e00040000a02042c2400020802c2c0d003c1c6106072405c51240d242105125007101d4035011303c0c25075400041241c028800002c607143c00681482c2d1190901088440d400030700c080c5440113052582c64502d5075000200064214054aa086040003602940c03902c0310a14004141a805010b801c1040803962100712200b8802d6040700c0c9417a4100000f = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 971501627 1250 971500377 971500391
    0x806040b060409020913182a03060b0310060b070818090c0a08070203040e0117010615020d03150e06012105040c0e070306081b010504170a0b01091406040e030706 71
    0xe140085d00520501030290318550001c200c031032010300c154155204d1100e445481d4802c1c95454451800e6600044a0603101d45805210399240d200401c40c042c40c81003030045403a91400c0706144c0b90110310318615a0300b03802d009041000c2e8501c04101c90210b42c100e80003690315880740104c202442038100d081c1e60007459490400101ca06118003030280c542d00c40d510100ca6032154881240c5c1d030b000310700514040318109001008240964001404102d6500c0c002150260380e45a8408603484444142000b50300030403c000c00070340d80352156840102002104114080c00d213030809160718401480305050111040301d01d2403002c1c502c07007a4032482003505800c1c05585403624180b03820b04014441c4c040303d050175802050805019000da50251501d4000811801d01500c42c4801e400c0c1003003840360b050050820010400c44448031028034401d4800e030040c58208001e10b41000c20010590108a071185008011140140424900fa0f0010021540880c0c8030800090742400c1d4455070390010207141c03522113 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 971502877 1250 971501627 971501639
    0x10c031e170c072d050604061e0207110f130905010b120606100f0e0a080d0f021f0b1305071d240a050f0c010504170c0a030806040b0604 60
    0xd1070346541c0180c8541006a89524a1450701c074000e002004024a0150101c9120381500081c2d40d21a020454101e90310381e00292a400c0c1042d20586040d43d503103440e484850941004e4105244500d0111107045203400c40c81e480b0401c0c00d031500b0003c0b80c46049140d242e070925643d58017115031850303018442040642402d1034124020036019601034041c250000800784280000304841e449000041c21901405100482c110303a00200000510300340050945004425240d0040300340c0030300b403058003d02c1a48101940900758016281c6000115440b26040b51a041c0000305038040c001c94100300400e800701c40c40e000810102000040d18003c43c601410010144d80c03054100c12803851081c0740000022140b4240410a2891110001c00684101103407008540c094010b0008400c18a441400c0480403030000f800e5034015a4403510b13580d100d20500c014000445000341001640400d810320b0642c0e0f6446031a02c0c0c14040902070305100380400043d07165202e82c0c001800000000700040c0d640c0d91200 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 971504127 1250 971502877 971502887
    0x30a06030b0c04050d110114130e01290d060b0c0a0b01050105090303070213090206220f061e030609150e0606180d0804030203060c1b0c010e010c031e 66
    0x8841901d80c0c0074000c011400c600300040444050300c1e8064040c1074132403403035110303010100103000c6070368104001e05003140c041c0c0b4018000b070080c982da243e41d0040f00925100c444034850030103800602c2400801e40550030340005140030742c413400c01a2000b050f26084010101c4000301540e0340400c1078110000360486a040000c0b900d01203041c03180c0c0c00e02103542d80f00d03401164240680d06010380c05a000f0882800540392510813003002c45ca0f00310010950561550100d0002c1c6c0180e1480c4085100005141c160704000250f084040e01c003000c000c450488c60705500410b2010003142100c41c1d821b100c11404e090a200c1d81140b409041500818445000d01054440c601010b51240441d844800c5000c105d880ca4680c04948584c241c21690788900a003000c204071040c0e800e9201100d840c1d404101c0000180c03000e1000910074109000e546072149150083d0003805035441c29800e446800c54200b00ea856a013068090260410a1808071207c0055150a442280c03642003142140c2048900755061140e000d = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 971505377 1250 971504127 971504129
    0x307030b0f0f06030d0e0402222d030215191d1504030204051305010f0c140304023118060617250312020c0109051008130602040803030a06 61
    0x2011a01d00c0d00c0d600c40c01e1000c0c10180903500d855050700810013220702180b040c1d0b2003d1000b240280700524004100103060742c41021b6405680095100305010007c8410254020140110140c00c0310b25645002d640f021a642c1e060000a11910302402c1d020f030103000c0301084c1c0d40083c030540400001c10055103005170903040f440040c0101040c980c1149659420007450100c042c004041c1c506003042d0565081102420b001880480c5010b008200b00b0040b507008d000754550307100e07a00b034009861003804400400c80c50540e0007500c421541003040c440140c994889115003004050f403401001120040410496241ca901c145066400c0c0030400141040d04007401205910804003045615a0740ca0120445007030104106455007242100031820428030110b200011004401d81d24115200d0b036581841110340c0c0d5482005a00045180b04696045541d0902500040340d4403031507500c1d2180002c148060040c6024251020900000b041242c180c0580700600001c01c141c82e128648442e03698010049 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 971506627 1250 971505377 971505391
    0x411160609060515030a14011104060804170301050f150c0d09050a050102070e070e031203010909030e1210020c15040b04050d0311031807030204020a050403230c100e0307030b 77
    0x9060082000c4c80e42c04950b0036800300018000d00404581611107000766401043c01e880340b5503c54116101c00f01030b82000304090b00c0541c480900742c1c1840d081140424440d50012000303130208100600003550307a0002d113506040201c441c01d109800c1e81e01ca030203403405282d407011a54840c086007a154144c05c21210015160240c0300110300d540e07610012030f69055035209040000ea284800b280c202d03407141c2c1c07000f10000c00c0502164800450070308500b02c0b6900907404401a50350b944080020168444040e516080049488001c60045908075580390000d8844410034198002400f0706100c00600c03410440713190550880c2c0b020700d054148000780990440d0122003600602240100040c0240714124082140c0103190341503070390301040700c2e194000400003000d442c81013240c000010781e9540002c02c5480c01d942d44241c0c031985145001100907032405805c2c0d028105410b40000901c0000500c0703400700301d08603201c070388a804400099502103410b2590a40501840d0b5002c428019260541801024 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 971507877 1250 971506627 971506631
    0x90703031e05220b0a0305092401121e030203040513060e06060702120708010e1b03030313020d1703071d15030702070803190206010503030f09041116060906 69
    0x4011640c00c40700788030001d0400701041c402d00c4000c061040c5180703406060526140281d4103152900c121381d0301900b240544000185d240c10420500c140305022030758203603060307030504c4101d0441009119000b4605001d000c05961860301c00c0800d0198009812900543c594144500c1c601a810001d49a5100d03000d000e0207001c4a40c0806d401140910800013100d2080040c4510343d11070908010603548090000d80e070100b440452a69440742c1030140c2001800c1070000010100404090b030303800c20360f1000c0c200e60145400414000b803520084122644a8110a040700021442d8800100103840c40c1002a008500c4400d600b10220301510003180501d801d500c070350040603030380d2a80c18010302040c003d941d04007400c3c0d420091100d05400182d500003013a801601c0c89141c03100c400364610b41024170b404034031139089422030440c20307014403045001d8842500514501160200076040601c14111024041ca03510b40c2004c0e013002d980b5066443c1c5214034002e07441c004c80f060078560040e0207030400a48881e4 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 971509127 1250 971507877 971507897
    0x152d080709030c05041a13150512071401110d020706140403021f091a0306041b080c070807020d1514060d03080a0b060f0418090305040308091809070303 67
    0x35008a1840c41100d6100440106a0b418042440050aa00e0f04040540d45c17150021040664880c1c40709040b40304a10703400904038140384024480181c041c1d1003e40100808042040190f0000c0b4400c03003a211705001c4000c1030003034480100c503c504000030150650240014402c8000e40c0480e0300c40855440ba5644c80b81140c0d08404241c4030320852100940c03020b800f4541c130000c10140d424440105090341419401701c0d035210801410745210b00400d0381c990100208000c00c614041c850144890302940411740031004401001d0300301c2101a1090071080804151a020013015104803002d0720b0340a80b000c00000301d1840c04031420048010520001390505d0f005601c4003d02c120340d988100d0005082413110461038605850700c540140901c0040c50300e8400d5840962241401013088207000b441c074580d40d078585050000075005103003141d40000d00b412801d10100e0b500c60261070580390070040c0c0541c0d54480c100003407491180c031100800f9409811b4104070b04a0004545842121f0080d21065141 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 971510377 1250 971509127 971509141
    0x40f050102071a0c090603070813240f020304050a15021c1d0c0303031b0714250f0b0307030f0603080d0605010504050a171e10111201152d08 62
    0x142c0183c0768517540080c000e000043c1600d215404403500714201c8108010100c0040d140c442a424030f140100311058209203000c000041d03a13110b19903000f40152411815030806a41d484e44039008100b01030404a10314803c9100c0e495140d0441d150945030b809240e48110005410fa800b81540c100903c030030042074041911801e0b400f1030781290904004024520b9961480c2034120f41407015001440900740c1403000c0c00004080303503003101c01c0504400040c450a100c59030b648107100d03a0180d01624080241e041084042505403d480a0390300c0391349050b40f6580c502d14210004c02c2e8140900f41e4041c04e24400105114060004280d0380202503000e0009640321801500c031031043d8071030705820000c500340800001d950b0342680c00c0261190000e462141c03c003070101c00e01502c1c1100b00021140c21081c0011120b0400b449468121500801c4080c1440d45062985030003003c140302d01600b014202c0710b803035080d80c4079001030070520111100e000b24134920205080030503d60b031201c1c0400310b80000b02050341 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 971511627 1250 971510377 971510401
    0x91502030c2107080408010207021c030c08031e04110a06090b0d020d150b03091501050108060f010e121b061611060702091807050111030d05040f050102071a 69
    0x49107100005001d12940c1c05210030001c801c00305840d050140610041001030041c0008100500c1000000340e01e4180d54010811140b0085858961240d18400c250f00080d4215100d0540940c200605907140e64070310300800001c0c4050b5491070880c441140800040282c0c00700703218810402940c80318080c5441700c40c10384110a003400703020103440d010f0048034465160743d0000c14000715501c1e8042a410801106070741150701130303000060200e00c00300801c62410400c10102e0700384480300c0300064941d454040040c00a0f207002d801d407406003c0072246481c4690040c0b544054544000e01070003141442c20032090340720300003e181c160b01000e20340001265844d0480540d611102c0030840101d10362500d6540351061020b01482a03040101071208102580d03c1310065481000d94481100d50000343c0d020590800c0b070700d604540d0500020019100074208000161100c013074440f100084d540d100e6061401e1101e20141c0000c24942c00060010f04010a43c045040c6070402004991075a0700ca1602d0368035 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 971512877 1250 971511627 971511637
    0xa030c03061b050901020a0b040f061b020111090a050f0301110406050d05060d03090b031503010c09140d2103110f041d0702152701061d0103050d0302210709150203 72
    0x401a0710185144000c07035148e50540d0b402910400d82d595140003e40d60701c4069503104406611490001102d42c442c0b550280a800510350000162510f0030100c00005501019140189401210a0015110240c800b584442e018007680503140d500c1c1c1e560b07400000c1055100e914003074405414080842c1c03175403c000f0003600000d45d25481c0c5014090902e400b44480350001840c650420844881a00854500303114640c00c40415946041005090070100c0010104850425010f904070400810100e65080e070003e0130410010300050b118400d004048002e80803221410500c03150000b1140d0b10001d12500800c12662940e0920744051601c8000070020030040303a0000c056041030014801003440340f1071701607100b050615005035a0340900c1010390241034001489480b40c1d034032001440f65000d07400780e0200c00c0b0120325008003990b042d5039402e40c40d40201e1111000f03064001c14142a40c15130903640b000c520040d107645106904d00761000810409082c4141036003030303907a40b2107401074501c00310440d2 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 971514127 1250 971512877 971512879
    0x4150b03061510171302040c0f080601051c0f060e07080c0f1b030318010f0c0203040e06010516060f050c0702091501090521060603070e0408090a030c03061b0509 71
    0xa841644030b41c00c1c400301d52480840701040102c21808003001c0c2c00c000ca0380e180107200c1054000f181180d2441400100c171101911981407119007800640d41690066003541e0000003072825548401d22480266030800c61400c0d03100a40d810410000e07032401c0c8544c000c0040798441d0412a200c1c0d00c1e0b024094a401c2000e6510354405a020000d0322a002c90090040c5061070202905404100045041509640080d40c3c0d460080c1184d60303490701c07425407d015192101c80501c404011103107072801c01035600d00c19031040740c080c0c1854000003805a801a0b0a8800d80388500c1e00581406015150200c0141008054456542e02c0d00e13011400d0f540001d42078556040d800340101800e61950b006003080b440b0524121810007040004c00314a68440c1d11402a014a030703102d0001c02c9800e4144000d0500d00c000b050b0502030761048004119030800c44070019045600f100005a03128903031408100c1480150704054190700201b107001042090301c1d070140d03805d20148650358400f601c8841c1c0403651ba100d0700e1f08507 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 971515377 1250 971514127 971514151
    0x103050a0b1509190623040519060303050a080106020114010e093f0705030703180b04060504081902061903140f100605031b07060b0904150b0306 64
    0x150340000c20411a55820041014107403101c00d8010700001c0f14040e04490b01e0b1440a804441600c2d50000d07401154050400020340c1c1c420802a291041c1e01c3d000300b80900d030700c40c5480d400401c03c40d07862024100000a40e9000506c0116224200604690700064000000650301d0000055a80c811b1088007030003500c030f0030091002c0c0d2170007180d0030a80b40c000d0320b50200d070b0041440c01d11044045100c500030584040324244214031072000c000e0021a00350442d48608401080800c000920101c11500101c1d41420220301003550061420302256498100d643ca507a070004021500913000301c0a03000300e1719414200c406100c0710045c0c200704550f840350003c0d00040148012780840d850200030441d1074410f8078000a50360840406680400710943c1c00007012828541403010410000442c3c00c0a4541810f081e8614100301c3c5900c06803191b08103880c2080c02001c01d9102c20032441d80c0011f004440d0003014050141400e080c442d9088009240c185015403400072451201c1c02e001c1078003849004004c0310 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 971516627 1250 971515377 971515393
    0x7030e070306092906030708150402190815011502012a0e0603041101020c010206070c0b04020120060f0619030f0303060b0f030f0601080f1b0c0717010f05010305 71
    0x1501e07002c0d0080350001c50307400900c2c10145660b11081d4110000030b9a0150120f10726083c101705050a180701034000e4000307074000074444502d000203050400d0f0042d605440c0c0415016240c500d48000780703a1500030001e140503011a1003050122002a141030741c1d50350540103554010000140d0880e13801d0340c04240c0c605401442a04030248141d400c44000b2107604040042500e010000b0384940d0080b28125000440000004a99681004440f41240081c00105042d013040b50020b480e65090440c000c100940030710010f81107900c1249041000480c0c0041002006201081c035502d418003103502c100c61040c40000030740305180018580d1034120002052040481c00c0d40c03101030a448200f0f40a80c14141c4900340001e50032040fa00602481c2e1803c99401d8490502d10070650050764040d00050410640106105105404980c00c60700600203106900340e01d80c22201840c0b0b03500901c000b010789409800e000248084941e9000c201101c4004020850320384118006003c6410a01000c0c00e681d00c1004 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 971517877 1250 971516627 971516633
    0x10030b0a09060b0a06020328080117122a0d140c160824060901050f03010902030d0903030206100608071202070605150f030c0f0d020d02031207050607030e0703 70
    0xc403050708140a008041034090141c000b00308082100c0d03004c40c0040c0d100151480b5003c80d48d0080214514007404a2100b400f0300010003040c024041c0114a101c0700000c2445480510402c0031041d81e03400c8440044e1201c2001c103061405200551a40b0102142440c44010362180401d0000e94207606486c1c4808000458482068980000005181a210f44007170092400060044480108880002082442001c0c401d41c3c0c00802c03110070b48014101c064061261310795070585202c2c1981c0041e20000c95509035200000d0140c5040b481c081d42601a09182840456000011900341d0b0f029400700d8020380c036000b9000389034401a10406001800c03600128042c81d102e00002202c0c14112500581029540d8644204a81c0c00381c6840342e400710720040340c0d503079820131000880040b2021005000035402d0840400c00c81c40641031021320580a03840c500c02150303100c3c00084141b9030060200c90340502018061030a6500c00c1005071958441d0000085841d80b09008608060090a000c0e02d0006d1842d0f03 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 971519127 1250 971517877 971517881
    0x1061d0709081b1c0f050d0c1a19110c0c030c061e04090c05190e030a2409200d051f060e0a05190b18060f03030a0f030510030b0a 57
    0x910f590141950200c030b10b0781e001d40310f194403030b060080050208040c000e10b080c502e0040390360221020320070509501004500f203a845416040b8024404d100230395100c1101c0d0380f101c1c182540500d038040c81d00c1003901c801481407010345044165481101c242400c610101981c40e800c4012950740b00e5800c101d86884441054092400c10003110350140c1840e032a89240021384540103a020005000803808518850f00c21440700705480650800303801c01010640070a8803400381d55400340180784000100703d02407442c47d4002c040e040c0c1900040000b00c50514040035144100c0c44c0d800307990a485c04c0a01c08a1420040c64044c01e5170000c0100071000c9a4600029016941d0301d204078802e5030750000144440503109014403507a100301c000111842c0910348202c241d01d80c5440d12a503a444e042095400f903d41e1203007800140049036071401c1560390007001409100c4190703552501800003044d1400f5680d0409400c084420281e10184a259035000b03215098160070302c800f6051100501c0410000d510741e03 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 971520377 1250 971519127 971519173
    0x23315030d0c17071707060c09060503090d0e0f130905010c0305090d0c08070204020315031e0c12030405190911070c09020901030906110c1002090a051302090301061d070908 76
    0x81d10400885c031500610100f8a4120343c034290b070035544a0b04500c0c01180d0040d810f034050720150500b1801d50804504455465000c9440c000c107212890451b0040743d51401ca00d12111000100342c403072000c107007031a980042c0c00c04c03417402c650960030604e0f00182e0600030700400748940704000051240842c3e0a030211640402d404050320540820401c50b00540c8403800214030407100b0a03003028041451005052034050030300201381840d01843c10f00e0100e580081113854040e00c0454000a01d07000c91100e8078158852503004582c0400010810b1440d0006008400304072a2402800c00c0000244081118584601d1000520b0120210000c1c406075486602516013040d040c90700080000865440104440180c0c4c00101e010b9404030340ba803002641000180c8001c6032104c0c095041240c2c04001c038a111410b4064107219100a038811501c641c019415135680e240d004000380200780e910401c0231000c0015848611114580c00001071300a401035406070100d900c19030082c54104c0d804603020340c1d1505a = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 971521627 1250 971520377 971520383
    0xf170111032e090603080909060301050c090411130608060102160b030606160f05030c1b09060105090d0b0a020403150c090302010e0a03053703023315030d0c1707 71
    0xb5191010452440920500020314483da0720750365102811410414842c9000300038901c20b80c104410040c0c0c0c05e80803400d840081e9030684011030101c0038131400080714000c2c1b030800d841261503094006a5240e000045600468017030b000d0301c2d144440c204046032010000e0103804440740c010400b049041c02d10200070b1101c0c001c0c1450340c50100401e983c903850202002c641c25030381a400411440408002405020307030341005212829004880d00c000318260000040c842c5040c854041008841e989a01040d146032035440907000c1004d2a00301c009000a411030f00040ea0400c00c9104200c4484000384100080c4248030f07110107078243d1466004503915411244801d402100300300300000011801c105071012030f500c4103100c0e85440030311055200c50b541a0211039104d00140103d42c0046034002c40c21081020300101ca01b080c2440310b4180014007404041e00440045491040100c4036400007003400002c5412400d940d046404a50104c501000c16180503064500602c02300381d10b401e0003401441c580344 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 971522877 1250 971521627 971521711
    0x323040308060a031401062105070306183f1b05031b0102040314011b14130308030f100b0901030e0c04020406090e010504051504020a090f17011103 65
    0xa103d0351640b00290707440c170950b5000e0b0f440e50024000303c00240c0349005c44a9046590100032043ea8540a540d42c42a00c000f83c02207a036140d4080000c400032266140c1907400801420303503030f0203203400800c01394069103051414a0089240001c42c6040c25240c2600360469a2680250100c0e01840b64014080400440e25480104144642d80ca940034800c2a280c082000040e152403071400e0524400e058814002d50391f0745400141001807800403445118145030303240210520226907000029031141503007408210b008480c1c00010420207030000c5101d01c8a414281c01c1f0350b01e071001074481c02042d0b03005000b005001030021207465442035101c941d0011010040310307281e42e2030740c005c20700326031241d041a80050008042848405041c5407424018142951300b003003030385082e1180c14411100d01101520403500010000c640c1c91080844502920302000da4900c1c00340c8c0e90a01079506040c0c2d1001e4440dd508202070072200c3c50700001501e00c01c02c00c645e00c918030321100d007641d09007a0800c0240d0181041c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 971524127 1250 971522877 971522879
    0xd0c0209090708121b0c1f09030b01030c060e0f090c0d11030a090507080d0804060b270603100501140424080106030b0c090f04020309010b0d120323040308060a 70
    0x10030f00300140043c803251941000d6841201c541d90803081201102404015408140050340c1521240c0058003000e8204107880b0b1221003040c4115404601e41c0d00151050031543c0011003441120f00b26582110a95154501c1d41c0c09031400344926143c0304400c80c1c3c1c0c01030b00c0100240d904503c8400500e407517948020005070401400c1101a002d400507601c4005c01e0b80d0b60749440c01048020440c07c0c0280140d80000c05401c090104000d2074010024402443c494403034680134002c2d11025502c5071091040b407071f039690341940741118115102c41111594403d106000e442c2014017000e120b82c030305861f400303103c2e0442c00c4e00340828003000e0101003918401310100340300b180c49120704040356000540104400890483d00c2c5080515182a002d400d504070782c03074108944002580c034064009170700c01c0b00f624090b0b144e80d15034500341d00400329440c0701901311034056071000800403a080341d10662000394404002e811740c0003100900c4110711400c00080d90050303002180210b40500c0c140e41d40064010b001260321 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 971525377 1250 971524127 971524139
    0x30702010b1206071103040b0301060f0e0607062a05040510051b0a0303150b0a0f02012c01051006050a05030901150321180506160215040906080d0c02090907 69
    0x400060709550480d0400ca06000c0a1540120340c01700c1410714034000c40c2003a007050315551140c801132181c6424003801c61802c55949000703100e1281300780c400425094680314107080007000703403c401c00b4002a00b03110038003884940501d030540480c0031145507541b80c00e05007020b0070700c030b51003d1000c00f2800340b01090240d000c040403060800102e40030b400c0c1c042d00c0360800e180f802405807603c0c1c139065440c61091309018003c21000038107540d244805844d1010031b1082101003030b401040c40e550403424200b1102e241d540c1d000030842102c040070b2040c00082003659038011112480480b58021a00010030400c00e030410203200398040c5800c000c82500000d042d00700d0a182c0131039120307554811100c0ca0011201103001c880524003080c0b8124407814407000307030721506907450704030103103805120f01c542c0000ca00c40c1038400380400040451a406010182c4091410b65064104d0304248203185609041520100d0b64a00109a00540d6003c546078941c03003048070350810906840041028a0a02c40e0750b40000310 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 971526627 1250 971525377 971525389
    0x60339060c12120a02041202010c03120c030209120a0f0201050310080703060504050c121e0709050a020c06070c170f1603092c0f090f030a080f070c020a0506030702010b 74
    0x4038482054425070301c4a10031a10800d07000000e0407802c10385c0c8140010010360400d0012028080d03424030f020a0955040d240030743e011108002c0070302d1f141e0319000160107280c1d010b0340103040400b8111041c07458401c40e401555a1560b02c0c00c00140307280e2006003d28010f50054001e19000317003150103504000ca441c1c80c0300d14070740780303107580155290758654080c001488000d004e0324a0051050721280c041e1a507a107411540e0741d0900000005102040d039041d62448802c0c001c400142183c54414850b0307040c03002c040f0000e508504984a440e008075008201094041c0b10503003c440e86c0034103030300c4c05400210610a2290881106040c0d404010010b0000401c00c0c01511081c0030310030b4480000103414003108140841d1006c1e055a503407081c49040b486504100b000d07036903000c1807404170155590360340c041140c20f084a07643c1001840c840402c90303007200d0342c01041d041d100d410342c81807a29903650b45580454030007000203800f94200100200a10403030812400a55210485000105c0c4001d0094040740c6 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 971527877 1250 971526627 971526643
    0x70311060703021206090f0103031202160803101d06010e010903022709011416020c120a20010e010f030237030c17060f09070503060339060c 62
    0x10000740d0000314060781c1000c1e0084c6940044003039910020b240740100008403400c0041c00040c1c240440c000c91032072451550b4040354045111595004007045151a00c07000a070419600d282076810740c10004610280400c485088a0000750101c48a980703c103001503441004582c000c50402c20b13940c8021000d030301e40d8038407140d00c00f84600798030b01600301213600b40f003c082c0042e00c40c40003641050321425810300102c0605810041d600c2c0d483c2c9109815506c164500b01c02c00a590340c20801000d01095040301c089441c41c50280121100091002203580074a102d40b81030025070b020640100c800f00d0294031a021200fa1b0002d18180145052040c144820000201c000c0601144521284010709000f48400803004025030307080c140f01c00a07100c9009409042203450100c220310080340002c1140d6602410103e0b60900903003215280d00304174070000d040791320449026000340700b0300f0030300d90b29440303101070032081c85031996406220080012225164203030081c004940c801d90500c02a0f0017960b06210f404 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 971529127 1250 971527877 971527891
    0x50307031b110705060a02030f0c030409050106080901060608060108010312030609050c07110f181321021903270906060e0a09061a0a02030c07030b060109240507031106 74
    0x2c6003a05012002030300e0524141c0100d402044103000c41c0c0d02c6a80c000081e51420046000300c01d0b1580210307841c4914601803688003c0390b10741020f0000501c0c0f504540c14034010110640280001612400d040d40c8904041d0b548a0001d6070480042001c100300c19841301d21004603240c00318405640d400604192102628904c0c10090001040c0080100e85003011120100a0743c0b82d1480e01a00030009112080b243d2100445184040c001190030030400c0051140c56800510101c4038052044100c0760000c074402c1c6840544a41a0a0742ca40c0e004150b42d1900c00b035060b40c92403018880301c1010056a400740300080d100c1201c01e030707000c9540c0459020310f10107041c03a80d5548580310300c036008204c42c0b80a42d070321655809240031803d0150030740c10400703154401c121800e0680e84803510602203141d4890280d41c5c11031401114408000c03c2850312880f4044d61099a615502c1911240c4000440300c142030781400c41007030307680151002c0e0700075405003e0260003410301c466583e40c0301d6021824644116421 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 971530377 1250 971529127 971529137
    0x211608150907092303060129070303020403141c05090102071d0a14221505040501050906062d180f0f0106110307061122030b0702060403020a03050307031b 68
    0x40c01180385884041c1d00c200c0b8480130004420a024021031344650040c000c0e509400d0341c0310400031a00c60954045a00e50340742c00405940e981441c01c00030001c1d0060301003150283d12940d0a0103241100082890b440400c003404080da403500c0c00011348242e4001054141540140c40380090b07815600c184140c4080c5007204401c4041c84d000480c08102d424000d9101035207000d68060201f00c0c00010480100c0303d5101c0c6019450326000d00f0282022b051521501d81c00701d0800301080208401900090301840d9038804551050310b0381c07001c10185000d10341c4103a01741c10115185e908001c00e000411440c82c84042d0411a003d01041d20408480d0401c480c03d0a00d011410f043c094900c50308000c1c60b00402c0d8514140760311048050b070041d240d01c208440a0641c035264940c15022502010440780e44003903206400d44001d000c000070210552a0b88000d407040801e11000035462800816168800c941c1580030f170603a4251a54240ea081d0070250072501059611500301790200d42c40c424000301e40e01a504c2d1 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 971531627 1250 971530377 971530379
    0x9010e1c0f06050711071203140c150a060612090215070f110604050a0e0709081b01121407230d1a040c092105030f21160815090709 58
    0x403002c1501c3c0050403500c1000b2540041c04590700001c02d0500546201000c00d0b0742c01d800030300341180c028490030310031000020001088080318000107041d150140c21800b900c00d05544059400084811620840307021601e0380e0700003e81000c16a1080541034401409904044081c140d00306841d00100d008943d014001c00010042c0b101400c10300c652040c0841d621854a42000040b0721401018458001024010350210f220107018071080e0001d400040115403c0700e04180300309402165191140e80421112120b0b90400c4050740070707211440150700341480d00c0c1c0d100c043d4102c0306c42e500d03144850031888407030016503c440c0340c5500800380114258030100710303004105c80101042d20490b040a1182d454801070800c420380100c440c1049070704a6a41e284c0c140030005807040345c100d0300359006180340000101c40c47c0c4e143c5050040c080114403050f0030256400c54a40555890100f99100c070300128402c25903000c02442050071560003000a11011001c11145021039103040b070a540c803801160040301c1c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 971532877 1250 971531627 971531633
    0x9090f0c08010b031513020904150c0509030a260c03030a060b070b0103022209150e07060207050f0f04090605060118030c29030129040b09010e1c0f 65
    0x200c0c40d03018101c584020441d810101000a5a5200d0510041840c0414500007400c1d202c494448102c001c0d00a0490f00c440d1030646004d00f1900381c420828600a0b01c2d2500c6082440e00ca40e05940071100f024000700180f1005441d00c01903048250700c85200e0003400406210000394031006401c05200100045459081218080090340c18642101201c0a002d2185101090040428a04490f0140c6070400d500c100c1030040c4000101e0000d40c090302d41e04209079032040180c5446803850b10300454404106820712100040c0d2030300250f10500700180d10204050107289880700b0000c5002c84000e0a440c449801c810204040d2040c0510a4641a40c4c960402c12556004425055088024600500302034250f545123240005c90303004141400262400c1006007030b13500010700b01040c0d81410044d80301c1d82d544c003003e10001d094030080358050f004d41c281000c00451020130354041c0e8005000e40b03420304143c0700046441d040c03104480d6a011002280f0300c0001102442c0c113110480c0030303003000101142a42 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 971534127 1250 971532877 971532893
    0xc0513020c0d051602090726010509070801061d03032709010509100303121d1b040207081b0a0204230f0c0702090a06030221010e070b0913020409090f 66
    0x50780c841444820050a11303100003a0790b0084040d5130407540c02070540c0340d410040301c0c07061070b0612419010342c1d614200040c0c4c070701e00c0c0845030490b041124040c6141d81c0d000c00850f031540342031040c4404280c405c01d403a004100c0e501c103003040c0060090200c1381070483c20b401161004202040f010006890202140c18505009040501620060300c0c501c1c0c0909002c1d041e103a000301c681c800a02081005950104400c02e503400a0811601140034240b40001400300191119000b5180071443c409002240c0081d041a00aa03440c0c0c54204d503841c0e09181000718040c3d0f8015440c0002d0b00d0900400703030300b00c0050340c0e1071084007da003070018420081508503030340c02c3c1e503149005440c9212015001d42000100c00c4100100c07808a50b0503a80c00340503445011006001e4055600000d501800b00c06070150282c42c5015904010000c22000f0321807070552000b00c41c2c8a107414044e801640500b0080c4c0011410440151a050711300150300516055880410a0031030340c0000c81110071521208040c018802c0b10 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 971535377 1250 971534127 971534143
    0x17041a0c19030e0318010509040e031312030813111518030106030c150c0f030c030e010c0b0402010e1201060b040515030702060106030b150a0e040e0c0603130c0513020c 74
    0x2c0c1020440050b00107103d541c1c80c02910304084110311040c6010303110780d01c2071301039800c1d0795009031060242580044102d40c8a800130380190200f1b10340d01000007024000042000d070010307059220000a5169841c1903a60b522103180140c5803401e20400000640d03ca0401d090207000d00300445a07160350460103d2484048a214018441d0b810580141b001c5040d41c040720084803030851004501c005d60311410785406110901c00b506142c030703504c8107109042c0c01c1984440b806202c0e0341c3d240754540704c400042d60b5400c103071000608904a8040090700550140c0e610009070741004101010302805000520b080d01c8070b42c1c008001403200850100064200080000f0000380401c60741400c520340514020340d100340c14400c0702c0030161070b00c804041a0302c0b4445526152641071540d04c0d03a0712020403001e0680070140d81d41d1401145008200d200505c00440c0d0040d451000411251464980040308106254400402c0e9408030100c440003406595400400701210640c05001d40c44000400403e8200012 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 971536627 1250 971535377 971535427
    0xc0905070c0201201908190c0818060d0c09140a18050408070206120609010b0f0a0c1109010e0a0609060f031506231f17041a0c 56
    0x2100032401e00603070b0401483c5008008400a40203c2148082400d2901e0300c2e1401d000591220b000d0502c4c140106c0c0402031400100395201c102c0e106150600403210102002d5014042a4083c04503407182402003010516141004007060301301a103070521a0111446000c20304045402c06904001405400005006d0a40300301c40340e0154074609610413004040d40a0385680c007a98400c00501008050b0003600d184c95005030480c0e894500381440400403680907285a0701c0303507000f0400003c01c240100111004030f51003200c410704000c211030013902c851040000885204600c25503400301ca441d0b0103044c0d4000e02c0e08242105c3c0d142001003a600455580d03820a0a031207080031402d102080b104c0351448104c990200800c82d0080c8810d4400c4c3c0100f4041e080807020850641801170520100711400803d004201d501107000d01e040c404004200c45444611004260a10541c01c4401c00a850913a809401110a4501040402424805088101c4841c4281d8002240f1201941d4083c0d10160300d03220 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 971537877 1250 971536627 971536637
    0x90213090503071e0614090f0f0d0c0c0902120412090f0b09060d1a01020c09013005030c1b09071727010605040c0f0e0f1c0c090507 58
    0x503160312069107074880d03c007000d0071030822005407260300914201401e25982d00200200114401181c0c0350311015030603030b601c0316140b01d10140001a12004501280c8207a0180b00505410b00050019280c081d1118419180f091440300c000501590a0004094041c586100c400719450541b60501000c2c60120702402040101401482500100c0c6042010ba640060301243c0b115108000140c00c0e2203016103100c40c00f03007040405a65101c0e040c02030b00065000340c0a0b51503c058220074090152024483c40c0900b04104001850b01203200302601103989082198100b84061520303540c1c5103034060701c501646075000003906800c0d405030b11f0f002200c2c1c030350450742c1c11000e003031031400103148512414810030fa501782000458040305c074000815040c0781404040b400c1003200401118003c2ca800e229140c051818180c02202d020311640e213802140c0140e484820f1580c041d102404115680c03404c034aa000f44443c1c01ea1071307220803a207440349240351003510f0075005c0e9420300e9800010f8880103054041441 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 971539127 1250 971537877 971537891
    0x8010e03030406180503030a020f1b0606030708010c140f0f03040c06091211040b040605040c0519090b0a0e0d02041a0f0a052206031202070821040306090302010915090213 75
    0xa080070044039001616060702689500ae0700004804500c26551a4625056101404c18248901080300c80c8500b8044054402c250740c1c0d0319546003a036000a18810000d1b541043d811100304030700b800360502c000100180b60900320008000030700c0b81d105030b03400d88441b00091020840c0c650b02c10020805031822410002ca80f1015984a01c00c0a00c406881c030f12490701c5d076034403d40c0c80d112039100100034a402031050016041c2400d001d407983e4401c1e6400c01c1c00d0140450307030b03c1c0101e019608003002c464131240140d241c954002404c485820000d010a035105d10040e50a00150ba660f00804203146c0107845400c403041c2d0004104540c0c913041c0c5e41c8c0e41d07000f030bc1180307420081c0b0f41e0f90805241c0e44c00402c2c0400c965101019521000510071604001c19070402500d10500031075000034128151200300c421241d001100c051405034100c0040200402800c0402080c0300288254000c01c10081c0300c0e00011800c0d4610365104000041c20b001c406200c02c0c1c1d62106801507240000d420803008060403010070682c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 971540377 1250 971539127 971539133
    0x31b0f0111031b0f0f090d150614040b090103150f1401080d110303130510050106030209190f060c210e040609050f0f04140303072303091b04020408010e0303040618 72
    0x207003d03000508104c05c0b004034840f03000d6100c02420800c110341c41885a440d114101214200070a5a40104801d5a071100810303841801c0ca8420400c0d5144014204140d40e880c40c0c1e02e2684041303459610480303054481149207405845400380f44504aa03045014603190305048131399192040c1100244208201c0811004881b1000300c200c039000001030700c0d13481e840303441030034030350b02d4000ac20b089a2a69480c0100003ea4107030726901070904403c044880a20fa0030503900d0500d8442800e004e00400c1c00d807503400401920303001c1e500f1280301d240726051480d200300c0f5208401011501603100c1e180402c2c80580d041c0c1d4145407903c2801c008d8204075008001c81e007004a43c001c52180020001c012030b114020101d824051015080115001c1c03002c00c4a64078030b0000f2005000c1c01e000c10a20301f07126041c0310301440c040311380025240b2800700900203282450000c00100c4603c05810b034856041a804c11011564400a005401200481000440d900c1c2460701e8554111040501c2c90181c0100c4020310b4000 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 971541627 1250 971540377 971540407
    0x1171803070b0a0501030b160e0f0d06090f03030c020f0a060f06050303030a1a090105010c0b0a1803050730050306130e1c080702031b0f0111031b 64
    0x82101041440100245240124514403640c500649000c040800304030030b03011140c0105060342c0c0b140b0780714100b9481e2481418020411210200c2c042443c43d08202041d003011403504079140001485140d0800da183c407140229090b00300c0aa039402d1216001030306064041c01a6602000310b44010080c3e000744c0c02c3c0c2240c0362003a50600038400d83e22403540705582c03035941d080840038041c0102036070f03503e007400d0340c2160043c801894404904103014229200525002580a041321010303147d034402c0c0034142ea5000301854004010f0207001d90341e90032003401c601c0e000121100e000d1198407030907900c05140c1004582c0108003c51102404d00390715003590303002c8512804001100080c144140c4036114040050542d107501ca40b0800f0080c40c0c0701b42c1800b402800681c10040442e50300181801070092030080701d009104403200c10142e4070810001e07400d00080c4100102503a6040300340c0382a400301c0440b09e425929401d04000d0ba406020080c03080d05c0c0348214034408a1000400d206180180f8801e2a1507 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 971542877 1250 971541627 971541631
    0xc0301060e0607150606020a05160e070302070f0c14090f06030a0201120e1204141503010513020403050303070302190810090c03021902010e2e0203060303070606080c0f0117 76
    0x801407001240c401d082111800c0048400c00c5030302c60911003d51101b000940d80c040100d8103580138031515518088200e61070104000f5207058881010b82035890320401d0f006907004043c01c07520154880d0748200411020382c0840c0141c40300042d81e0825440340410416904000b03060001d0959608040c80116540010340314003040d03081c24840c0c0b840081901c0c0600070424940150b6941c050145400545a904401041503660f40da40c2d0300c01002c000d805208e440c000203810031301403900400052040c0c1c50054502c0c495040400e002518081d1030750b8035103045400568140d40803035000300e07030f405984585050031100301c80e540c40d214002d4076200c200b401c1500d260340724454032980d6030f04000d01c1c4075219404440440141c50740000c0c0074420824024001c01024010000c0b60280302c041d01540e000c02421080c00755680c034458a440007840c0c650400a42c0082e00c0183e140c0b100700b1034600061501e00850700103120280c0949026803110091004032805104070504024680c0510610a2140300380f0799 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 971544127 1250 971542877 971542879
    0xe0a0303120b2710091104060807050a08012315180d030e060a030e030712080106020c010e0609060412060b0a1502060f0709122f01082e0e040b0c0301060e 68
    0x3045911080440150400136410180c040380c105243c2c40528031542004004a45141d51100340a035144102169240180010003000402c0c1c03100401101014021254034148110307280020b0030030110005603410103010a00307a40313110104101c10100701900d440310746888140c5014402c2c030402e64000b4281803178140514418103000c00c919040350b1089d40041000b00a06007280c5d921129424904043d070003181281001034030500001c02c22038408030313030451000300685070350b002440c1d8181001300c2c5401003d15650001c2c424000011a0020107905d03045590040c1c0300001c1c050344000030300c8040030307150300001c03041000d880799050400ea001500c10f0b48280881c5800b101900d40c2441100d810300c1ca603003d045003403101c03a08401072081144a42c00381c9080c40c80c0c4d00080300c2e01c2d00e895900501c0c601d1402030128039200000b504c4502180c0301c00d481200c460000842100d030070340d001c590f5180182c000244508a2204100030417080c0706440b50000d9550000c142036624040004000c0d001110700d20b = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 971545377 1250 971544127 971544199
    0x10503150c040504090f050f0d020709050c0c0307201504090b150a050406171308280504031e05100209030a0507080c13020301031109070e0a0303120b 66
    0x2a8510850708156405008000c2c02807050343d0807030500724090301c044070042c0d8807401180022310b541c4800051050800381c05070080c204107440d140100005090081030340c02042c40030040e65004410a00082541c00d10408034040b40145420010740384000c80b00c401405420280c06143d042c0a0241c1130310121600a140421450940c20204131a00302001184009210205450051070b4101001d0400c0e6015a80c2e0320a81c105d11012050b205c10064484030f0481c0003088520000c40e452030008c048407141c442e440342034040484100c0c480840b0038004030300000c0010800b0300c2000003008080e440100218564910340130640c0f82d154544103990b0341f1034942c0d41d00103042507103030720b09103d031409058000099459065941030310702e0725401e00038111482600e0305041007850340500d100b0790f03069a410445003d411207080050041180c000b502040500600d020301c0140c990720040340d07401843c46a52001d21004050660f042039504803d103c2e1310907009070010985040401d0801e18a9001410320 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 971546627 1250 971545377 971545381
    0x6090f0606270106050d0b0109030803130212030706150e070905010503090109140303090d17160c02060d0605040c021b1003110a0206090c060c0c1003021c0f0c050301050315 76
    0xd50b12925081c2403040c0301030303900070001a5260f0000054420080d2202c0180300c1c00810000468203c0d0450000604d9540701f8000315240203203400042d48000d10140c442d245d4040c4440a070b92858200050880e26a500e41e42c00054130001c01c01150014513254034040d003a41040040a0030581d0a0b000d41c3d0304001e4040001a009282500240c0344d50b40c204100310760302600110f51503100d0f801111000d02c80d11940b11180c0303025100b018180c000002003800b08000380c6980700805810b06a81c1c14840401c0307000c5a042c0090394844004102511680c0400130f021450202440140c0d245c0c8001407055411421900c0007400021108007507055013215132959003140040250000c140200d04e11035008004940440b22030b40004005010340280e01c03c90706a50f12038410406940314140103120a50403140300d0b41800e040c9400c8081e003405490401506220702c00b070100f49004940d5900c0e20307460352514aa02440072451207050034042c81d5207051880c41d03040c04046070b0b8400f010503c1001389150000 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 971547877 1250 971546627 971546659
    0x1a1c08040f140411030f16021c02030d050f06010207090b31050a021c0b012c0112060f06200607080f0f060a06030903050702090f0906090f0606 63
    0xc403000382001d0094145103545804805212040340400c89010724584548070302e15680342410350f4450102e110400c1c92554600303030015070780b103c40c0301142e003988105030400341c400036580d5a2441841469000390745170750701d140040d01a144050215280100030398140409641c0c08034490090726811140132a03070030701441c003082c03c5008001070420102d950041000064030300d00140c0c80c60708461034090015858664021040f0700c00e110248280d084004003128030001541c010428092050400402030f61034400a8000801a003945481d84070103260660203641e00401c1584107c29901010840b4904100f404000201079000e100709021807250402e003a07007944441c0f005001114070607107007076040100b030241018a060f1916500b800404001403041e107202c01500d44a80c0000348000c10040c582003056004041410055040010410010340903851700007144e400340103182c0011505103807031011241410400b5140403442d40181e10050000c0e9000034240303400010440c0e98103200d1070000 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 971549127 1250 971547877 971547893
    0x50d03050c0a0c0f0807230303060d030305040503070204060f0f1d040f021c05061009020a02070603020d020d151502030403032f010e060105030106060f12112703011a1c 74
    0x10000170305600c2c00066240402a8080d1035081880708a040c80840c620401550b070345a010880f125038001c0120440d64012030b201e500300d41d81241c025010749203403141a4010400342e440070f4010150300000782504211010901c008030004040f01d00e1604280c20844031129104d03003000d0805480c0340103001c4040103550726403042c11400030044071048401100d614205448007004c0312641e07030402d03440c1400103215400380221002c4d0005640513000e070ba81404010b40007500401ca440192590078000c0c41e040e080144503a4171070a550784131031101a49030101c561078940e5081d4030700e01150003e01003000081c0c0c100548540189003000c51035500c0e1020b42c0d180568002c0c0c051001110346c05c0105000100c0000708010303050300d009a00900a0513210135003681c4100e41461107600007140c050245421100691103401448070b8a08458030b802d46904e06c0d0000b403c8a2452804148040c002c2c41c1c1e0325180c00d10a68002c40040305000101142000000c1c100071404a8802000340640c0e1040702004213007 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 971550377 1250 971549127 971549153
    0x607090f15051b060a14250e220b040207050703060c1815020f070812030a020403020409051501091a010c0201021005130b01081605060a12050106030504050d03050c0a0c 74
    0xc0041d40e143e46420541241d603400c0e040d510010300724689144240c1c035029a00c0c4c03c44c4107036a454901c652100074108507000b80c20006c0c01724010000b04e1015201103076501000e41c407a134101a10000500c02c03543d0312140840700300c6e04c1341a03c04e0b441000050005100811207a007240d810000020b04250240025034608801000c0d5104100701d107080403456413410036013101030070307000d0f030880d98010203840c4116a03c10710760090a14640c02041405582000c03c802503034030202c105405414070382e0b2a4003113000d440a0110848031a005003040a03030041e00301e800386005003094031040c041220217001501d1408401e011947c10040558111800c2d640200016044550191401c000f07d1070300750589055110b076510215180e90702080000f9200e41d000850701040c5141002d1080440d10740b0003004450f500004d0540b05100351301407010681e441520500740204041d84000c2800c0c6410301e4801d04000d1400415000e00d80740205001104402400f624080106801c1011203160380d400c015005c0040 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 971551627 1250 971550377 971550397
    0x3070e0901080d020f0303070e28030f03030e281407171c050f03130c090c02190b2805150f0301090b040308100b0c0f0c0307030b04061a120a050607090f1505 69
    0x381c1500101f04001002433080039406a40d0070000c0642151003161101e03000300030b8040301c044d12200e41d200d5640001c3c90010440c81650b40c65100350312000c1040c03c09210b0340c007441180841c01000c440c1d420042c006117054061200c1e0b1600489220000540a80117092803070607484004400a801700e105240300111803900034030792000c400d0342c5d40360000188c0086030801005002d614591b0106a070600c08007045075612014500c420303640c41303101c0500714007541d0a803400410701c64000b170141c407243d209140c0102440720022108013645400d100011100d00f0b8018001d81c5081301031300c085007002100c0c6410070740c07500e46070640d0f850b5404040b00581a40d0003003403680d6030008044075002c100050340c891812405040d911a42c44030b00070992982018031010302890b18000c000b60006025134420040340c0200310200585951107000f10764281e0f9401119070165211382011801d201c410004103501180c94134000c05824281104a08100f460b80328080b00100e1584221468a009070b080d283c15241c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 971552877 1250 971551627 971551699
    0x603021606021306021006050a05121203040309050108010f1503091401060803090f060a0903081612200c010903020103020903010e12040920070803070e0901080d020f0303070e 77
    0x3d68072005104000c0359118190140c410024025038903d80c50040400300c0d8030040072501242c2c40d18003030203e512101104042c2501400b95004001d007022409140101d0095450045803410440050014001a0014a100060040d08000070f0310700d0f000c2035112064518004c00c204078540703002550401844c13440107283d400c00002192007400080076103004c02e02110800c0100300d050301405064401c40c5c0704280000c00c00b44041c40442e1401005104012003440030301b00c54000740d181e84c515078200205110014080001441304106900002c480587c1c030600500915128000064008511032000906040d00403503080310303d64081d072003c10111101e4054440c03111800c0d2810a05a00078012500c8103854121410484910194104200391804040324900081625030440c25040140082c0411884c0000c40007107445150601c0e00038600c2c0350082030320003007240000e420052007401000c42d1364820f00c00c0082d039603800074a000103000c095540030200c6684107286c0300302490b000410701c0402 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 971554127 1250 971552877 971552887
    0x70e0d15091a0118061409061c02041b120b011d0d080c0303160903030914040f0e0c03010b042a050d09030f030f02090f190e040501140108030310060302160602 70
    0x281d10910390741080701829010404280c803642c46c0310034214012145038009203000c000880c9414103072814400002401d600e9012508164006170680b480c0c05021041e03c480e1619002c1c080f80c201e0071070014104020401d03c0f1006081d40003c003d01e1702c42d10311100b04400511807501d507403110880074511030b07000340c01c680c3d807044c083e22026526402504c4860842000c407014206982c0b194075500d0560307505643d4024400d181242103c0041443c01d0115881955142c1000c1c1090051144110034114080945180d940304410503085410b134804450003a0b0030030308210307400100d204002c15200c0d04200d245c03580ba10700c141c00326101e000300031422441c0c900c0d041c807a1042c5a0008110a00410781eaa070034000c0e076413030740f0504007079014540c80a032b00000c1d02c041312043c620303220118580a040d10101e03502c403265076a4104e04500400d8a0075240d50355182c0c0c5240e100b40000d210340340501244001103166041210080c003041c1d400e4071406081540c003082c0c000700d02c600707404011074072604030310155124 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 971555377 1250 971554127 971554139
    0x1507330e0a050706050406020606091e090a02130c050d0e010204030c080c09010f0b031b09180402100201050606030403030e0a081c0605030705010207090509010f14070e0d15091a01 79
    0x50303000c8400c2501c083c403409000040c010302c00d070121000d490080e8040c12507a00e5000502c02002005003001c1071086940d0030014800041c00f488500c502018801130804400034014020096907180c4041a06420862064100b075041403c562810451000000b444151000e07928024000c5070402800700c0060304001501800c0080c0600140808803107010160f66510f9022562203a240f040381305c688824000150303001008a0108821080c048a00e841d0554020005120b8070212041c861054480002d010039800e18550386500e83c12a40002c020071b081440010b0140e0000403c01000c05403030306221403c0400600050610940c4481c12540340d036000b0790703416110000407024994491401380c2c0082c85140020700c0303004540041e00036009443c10b0060800140a0007820b045240d0340355038038240100c410b449880c125404900c03462902c1c2c01c00010040002041d07031881c6100b6aa90400d40e0b0220b514002c1c02401c07403a2030000000c040f02c0c40c0c40d000c3c160001503d80144880a0740c0c000140d8 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 971556627 1250 971555377 971555383
    0x10c060f0510060e0103091110180f0f090225080f0d0209040509010603120f090803030103060207030807050f040b07021206040b0a0b03030c03042d12021507330e 71
    0xf6100e00352568409520380000440480312410340282082d0103d444101140c10103003000c203031207501440d14499145d13142000880086082d0f000c0c44111000302000c100c80c440440c4840041c1001d081c1c01d610b0305c818840c01250003082d100c001c1400070b030081c0481042081c2502140d10051444c4c519548444c0d58032103070301c020b4001540084c000c80c2030000145031458107108800a07030391700c0611a48406e1082104a03014030b00303010100d050148100d80868450400c2000d9030085114070f0000d0307610259458001c2000101400003800c1c4001440710200c401e104405480a0319440b0003204d454203070600001d5070a100325110400e43d40980400d200c00c0c04016007009100d00d150003824402c48182c442415507a128172055048070742c00c02d11007440400341d181d02c10380e503462200340d6910010130b08092450082c0e26681c007410256100d85404400c40c1440c2c0308000300c1028003000e482c2080c2440c1c659942c441603010003007908600d410074207000201d00c1c10040e00050030030301042107030400c0003076619a = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 971557877 1250 971556627 971556629
    0x70305010e090c03060c161b0305070b030f04080f190e0907090803071211030408010e01050c2d0d021c110304080412050a0b07180501020705060702010c060f0510 71
    0x41510740000810000002920902c440c9001e00100040c2d6125111040e4036007229092003511105a0021804070b0207640e021a5403000c058084401d0340e180d450110714006640d8080030710403506100304550740c1060010243c1c859004200c60395592040e07103a080c40d80c032845901c00f451142c86040e42204c21750240b80004100c0c41074403403460546036088140d410b81100c1c4a007035041e030b0081003138100140751408005072910850401284a910044240c0d08507040307034102442980d07551103c2c68000ba001d0060700c5c0c2080c1c81508641c40d015104a4a4140b00c69904440030804035500703020358090780344c0c03040f51104a281501152900101d1600207900c826101440a040b81041740202055074032508032802158032080152070145040410020314405140c251aa80900c25005000c2581e004010b4454822555100c10100080c0c0d080794006145030405811036100e4a01404992103030303800c071108140c090030800c420480524101d00a40003041902d0304840c100320611010342000c0c80400 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 971559127 1250 971557877 971557889
    0x201170124090510110705030109140105070e0901170c04020c0d08060301020a090e040507090c0c0516060504140f040c090509071706012706020f0f011e0216050607030501 75
    0x201e01000c151044441c140c05002e01036002c0700d22596040003134029409076030a1200d100a0303580140d03480740000e01712030014005540c40304024401583e025002c0c86403a030310040380d040907464210940c0204103000c1c414010310a4064498200c1310601c03900b0000c1e04640d5000034010341d034540884a03503540364803141d0300701000708458502244061a060081c1c6007450b1160b03441c410380c0307850f0580e600715480c0003400660703880c000d1200106107030704107003d102c00c000b10603145e5264140e6a450860700e4090352502c40d0311b038602c1c042c1040c080300d035200c41280c04507200c0401503112055032500081440c45042c2d070f1a50310901c2c2c01020f684080d006482d80044404c116460419644ca00c28151180c4c501c42030303141d4801d20200c00260f041c0d0b00810700c14490301400e098a82d0b205c0b04242c1270b00c1840c008c9410000259004030105080301c8020043d9480d140700001c001d0150381c0c4400c3d0f20104002c020018480135603004511408000600c61020031000d070404100c5600b414840c1015000302000c0c0246 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 971560377 1250 971559127 971559179
    0xc1e0309041103060310090f1502041406070b0c180a18060605070c122405091009020d12180b0405090109180609170c1515100c02011701 60
    0x60020b0111030303054a00c030304070190141c0b40650415072007000400281d0822a1009036075650032000c03490040507641c60407405a00140d030740e070808100f0b0048045503480da40c0f00b240100083e000251041912a401100c2c508280c4e0f02c4400c23062070f03441580402140c440d000008400002002103103001d2000400382640e90410209855041c04c0f44c0303911561102404007420940100602c089070302c8404041c50085540090305c4668002c0d1410940e4528a4618416120400d0041319882800803640070340c0c0d00ea0080282c504650f0114000320a0310703c000d071035940030040502005014005c0001c0011200305e40e081c18a84071040d404540e00140200ea004054250000c1640d07150346c07060002004001c4c460307009820b59646c0e0b01c0081c00b1004006c40c0c860712040607400380c0d0240500a080d5180a041c01703850058041f40c6003081100c8000c0000400c510482c062500179207070807000d90101102450007030815003850006950700c18150402c60744403c05a03000040103511404600c081500300203031 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 971561627 1250 971560377 971560391
    0x617132d0809090603070803120a140a02091009061409030316030c05151e190c050c150c0301260a0f02012003030c0d061d2d0106050c1e030904 63
    0x3c0c1940c2d11040e00a802d2541c0c0100a040c80026032201127980c0003030a5500820320343d00705140703e403140d201a2103620310941c0101f01500c840c90810b9481c907951480d450122961458070400401c05188640b0b050808180090580000e440501c00c070703459510460700c2d00c1d070082181d01e0018042c1411680c00d540c50300801c0d00c042c211400c508030302c5019a19003080342c1e1501d898080705244121015244134184c0a03c680e108c2c0d4030300c040380610041c858007601c5081e152080703101001d050403c66022001c02001c0f0341d04200140c1019000c0e681500c0c1e00c054404112148052128084004900000018031405a8010410050b400401c2e4080c0c400e90f80c5a0801b81544186680500300703a8038402c09400038000244e12012007405485654402100420015503038114041e030b15600369030030100d01d61440c0030423030b821085000704154000e0303442d05c1c004598400c140c600712625060003900d04010001038070b10041c01e000c003c2c84041a8407901108070f00001c2d101c21941d0b9900584504e0b00031070402c06 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 971562877 1250 971561627 971561629
    0x30306081b130207020d080a170103030f110307050a170d0504050a06060503030910030e10020c031201051c031407021003050a24030b060a1a03010617132d08090906 72
    0x1d644d01143c0c081c205442c060441ea40b0707106d01d60084075656017045400e41102c8404002040041d000758041c1e11000c041030b2042da4010305500009052820652081044200080c400520060f1990300250b0352a1440ac2c0d00440b181e00d8414205080001d42c20074080c40305002000ca145007040f0302c150001c0040715503820500d40c9a020346200d59501075801908206018002c0d001080300c406c210046d101d54010b964021400c903088003031034074000d0740301007186042c001b0316202685c0945003c032002c0a4079a400300c2a846100d01040c0003c013003005a5544807003d80150341901c01040d4010a01d9040861014006004100840e0150045400c0aa000e052041d50700f0181c41c048117810441341d282800e40d01e620310b9a601c00740000303801c01c00718032002038044c45458244a07208a0200b1180d903a5240640041c502d0204440b5600000a0b00c424020150280803120954581c0301290300c0c5620140c6903010040d042120b040840908049210420002140000e00480710304031070a0f201c0b51a404 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 971564127 1250 971562877 971562881
    0x30c1b070f23100e28060c020306220c03111e0303070305090609040e0d1103120a0911060f0a03060f030f03050309160f06030c030b030712030306081b13 67
    0x141d00303248030800044540d070603400e0a4860040f002c1250401092130f054060100d0084c44290b90701c0340982c141c0440c0c1c00d04009444498070000d0655141c0045219065000a92900300140846400d0408000d54441240e085191000c40e01e4000d4008801e10f0b680e424401101c01c8811019886104c402c1c5110088035940104805c1900c0c02500640c10480d81340e4007034500354881811250700c900140000c0310035640724024140128811409000740123103100010f04104030290549915030400d1100308108150160f00c07070f5101d01d441c4000b0418000c00d05005110807810200302e038200b031001504c80910100c000040202c90003c0d42d0411229644110401714281140001014844015040340c0803a11800185030801c9864064440f00b03502040b10f0001c15405a1088480c801c004004000e01c54061081c2201059207040038402c2c1221440029103900c418010440704521844d41007003450300c60352125002c1d014400c01c4894410042c4128000740031020b408a02c902c6400048a403004024 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 971565377 1250 971564127 971564159
    0x70f1815120e010e0d121d010e06090a11010305060105070f05011d0c060a030b060d060f03020f19034107060c1a060409080304140f070302010903020402030c1b070f 72
    0x148000d170411102c8103004656404c40701c02078010f05611104034000e024006410041000101c00001400d80c00ba01141400c080b001003031113066402200c0c0081c0030484c2000c0c0420604024a800076140e07072007a0060710b060040c05030107070045044000240420030305500c400843c0340d404034880000c9046070821a0340e5880c128540760058030a100c540d0b0018020b401454401d1344c0104050708010403c1d42550854109910640c00c0540815041081d42400440c508100805844400012101183c086c0510500748002442d1550a60401680d8030418110300000100b100404030381040062009900000da08014407041c0104580068502d0080031002e4010364011685140320100d070f49403001035030b001003016170041e88415510b40022050401148a540b098142d259044820340d00f080c9002000c401c9817102d5406008107001507030b00460110300300c0b80d04450142c4d495941d1420000580a99035080007581442c034000e55481d4030229a2100f0303100c9811814055640d02d0141c46c11110344 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 971566627 1250 971565377 971565401
    0x50114010522020c070b0a020d0318050a150b030d030605090604020c1509071d07180f0e0414010608030c100b01050a11070f180605030105070f1815120e01 68
    0x51030014034a40c00b42c0e005415122548020b842e411650740c0403050712a4060700c00b020040c1c02400558003515058410b28074901043c2e15015a280c46680d14245d4440c41403101900d0070307500f240002144106500580f0414402800340e030104405840003801500c65400713030714420400381c0d000131318a040c03d1089d41c054103400e000500100700e1151252282000241c68500340f80110580481c8401e80d00e031189200241400340c4103114907080000603d0440d00700450211485040310400050307440004060940e1a4090032200076101c51808120803130101c007034041d065080501c005207505000c070203064000389620a8800c20300c0d590410000300c078103500d05240450820322406000c05d01c42da040c4d0b141d410040c0100da0305a03844903088000c0810303d0b0701500c4007401a0001807003444850160030000c040030340003409581040207021349a0410011000300f0003800c002d6101485040b070150360000c0c00c2840b4102c56204400700c0062004002040e81e012203800c00b4248010100140b046060841c1 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 971567877 1250 971566627 971566669
    0x15090102010f020c3004060e130c05191107270c020a080a05071401020306130603050a02040b030703061407030c0e010f0807030b090c0901271206090f0501140105 71
    0x1034031100741032000e00040d0908500c00c00417540780b1014101300500181900d0b031205030f5420881e41c20886548010800203205600784003130803280c16040426907d001ca8428405625210429011600010a0180322980d441207a40000f0010b20080d0300081d03c00c840d010f0490040d00301d1318840261945a0b024600603400782c0c074003a0105000002511b80610365282c018905011340e201e040348100411000710355a580041400114a80450a0789008841d20801e00006246444441c0c4441d0b034241e01a004a40310501d101103030343d00340940b00141d07a014000700302c1c1c1694801e802c08a107008841c0c05000c24688440072215038080c01d410700c1c000105035110716901e054014210b41c0140041c0c481400c0c5a2134000300d0b9501c1d0b1380c0f0980d0f2441004c0038260961242c408500042c0700c204080101c23900e1b42801e90300c60502d00e4500c240d8005940741c3e40559081840c1ca45480030042c108aa80038201b0f4148080301c404000064020710703169185601140607590700c8008000c0905040172407040f01103 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 971569127 1250 971567877 971567893
    0x402041508072105040f02040f1a10080105060306060405120d0e180402010e03012c06153601030b0402150405011b1112150a02090d0b0a060515090102010f020c 70
    0x280f503540050754030600c110712415103844145d021a081d14a4031000410080e01c840d0302403a04080040d5084003048102d0700003980d0041c0c45006440032406004071801104000f000608945030041194020200500004d911100601001d44c80b10049584940001d00903600c42ca1189000304200d00d080314120000d41d8191616401034940ba8052907410740c15540790038034551410300750544160088070360340c032044805102e805401c0c01e00c1001448000a040c01405c841e02c2d5403a4444242e1001c603044008801069441c0c1d9013203d0b03441050441800790115400100070041c0207c0802c3c061031098400c3c210f01c14a0301500c0e0b20320300131409000d0000d20138101c00300a0881001c00101c03180e020785d055210382a00c0e800400d41c401040c0c411110030380d00208040d030001d80c0008a0540c4205040011800c142c040b10000b001180010006042c00f81c54100bc07603681d90003030303002c04003d00e0000c0c550114021908100c06c01d0703030454440d40c6e0142d481c299090303011400c107000712103441e501c1c403001d40891 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 971570377 1250 971569127 971569187
    0xf0c0f24031a040c0e0f0301061a0c0102071b080d0804020603060d060212011706070804050d0804060b1f0f050430140a0c27020c0a02040204150807 65
    0xa01468400c42c40c00e030034503095800c542d280c0e44900016020b5503074803050074201e49800d11441300c1c4013108450103a0304d000400c014100309009041e5549207151602507507008030340c0c6a5030180c0035a0102a01c0001c2903005052204c007002c0210b03040340c007a0310940342089019a8240c940000c12503019402c040200001a090300d0600c0c05010510310411006046c04007008c0c5498070184244c10104208101204880304098208041c55110209140142040c0381c16a20680c54502d103005100501060f000032070104000b6030070202c08050b000c1c010344003120f02d80e19850000d01c0d11464a10200b03040203811240f45114100301d4041d102070074250f0902040408001c100c800b400c02d41c45c030b0601300645c070000000d801729080c0b08560010030010711601c0c0c8e05091503040000158080c10450400e00c0c01c000701c03078840b106002640c100c18007006845840c148035207402c000b01c0030070080d0b000d0302c001008143c00310219610310301042c2070303540d201c003643e101c1d41c081c0c4d60100900100394410903e043d040c40030b = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 971571627 1250 971570377 971570381
    0x7080c120711100629180f01050408010509070303140f0426120316050403110f013606030b014d25050d020d0f0c0f2403 53
    0x220128600403070781140219441401120940c0d0000711480d05d0090605100c08a80c03225851654014602645880c501c001c9400c694030360408002e0084107104003045481e8018030503500245840c5009000038a0140b0740d0544a0aa03804202c01188000c111a690f04410100b99288500035554151a0078204085050300c8880c0c1411903503003034000e55460360b14100c144001c80c813000406a505803241000702c05803191410b4a1601d40422405102c02c00205120291011041c0c4059918100c400203140048515a25000d0643d840407052192100500c001d40078a070b454280d0a02004043e0751509c40450558451841c9903000812200401c1e4100070450390603100005011f010b180059003000f90380507814501c1601102342d90400381d8107140c6400074030110300c4007440015200c0d244d0a8424078050172046034080c150040c55a0001c40045481e9100c0301d6821540217031139030080c0101c603e40702c04520114080c18034a40c44881001503a0039114100d2042c000d00500034000d0b4144840c01100 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 971572877 1250 971571627 971571647
    0x51b0a090302120a120f0306080607050307050c0715120f0e030304152d0c09030b0115030f020c0303010602190506070f05070204090311120c1002030c1207020607080c1207 75
    0x140502413940c1000000d40d10505c80100003645854a0301c030b804610313001078100c40c190382c02122541c200d4400c0240007984941220740c00511030905d280c950110388030042c0b80c580d03290010001290340d91888000103401c049030740e0200c010140b06104500a508081e4103554060308011000e500a1000c40e00044980d548210141c81002d00043c040c0441d0b0655000f80c082d07918403400f03027640c904104800e207450f401070080760080e500780754403c40c0c13460380c90f548860414890280c402106006a841141c4a6004080c506410242c03d5448640e0241e000d600c81d4820312441c3c001d80310f46016040c5424040110001058011002d0301103580e542c40701f581c85066072411030b4200070003000b400d00107903298455010003034042d90340c01101140b0345c80850316200354071080b465800b40c1031110641503500059035034031503810352034096104d440d00a0341c41101d000310900310518400d160100105554009038003032103010f643d40e0310749040e02c4a402d00001c0e84500701c07815441402180020300601d00804c1d00306 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 971574127 1250 971572877 971572909
    0x605070203120c03010f1e0302040c020f0105010f050307270b0406170f0705060c0a020607030903080706050f060405070c02010305060102030f040f080f0c090703090303091203051b0a090302 83
    0x80d14011048038035924002d021580d030901024040014042d107107000780d41001070041440b041c030340381000c1c0308080020a982e00c0300070b00c920340300c0342c404641510034468003082d0782a4030700074030181d615290201040d803c5400f5081c000c1c802d441001403144040e407081682d0302d04a551118181d85481400300182003990180ca8100e81c40702800a04807080c44120100506600d020300b911030000704043d400d0641d41e61149100390f0040c404e004940001140392035040c1e904841082d5a0001c900d02641c00301c0d481e07480130b040104003081a10900000b904013700c03940d400030306441c00307940351010001150000e440000010342c1181034800154001c0d484590401014011a814804546540d555070360142d006080d022120f1981040540d40810503840110308900103003a81da0159004580c00e01c0300213080b0405c0644800ba00424036001e644024042070704110f0f80b035043c200d0750002802800c0145d5540200880c00f503184107101040c0825151104081d03075606510301d165400308003440903c50540 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 971575377 1250 971574127 971574133
    0x1e090807080a0201020a02060a05062809091b050303070803150f130e0c060306150f070f0803040203150c0a1d040609091403030405030318010e0d0216140d06050702 72
    0x400204140c1e502800c0c0b0400c0c41e0340007594904090390000e04101c0302a0800148074101001c0c8011030b521714481c81441c9010010440040882044e00b402c1444958844407105140100d000d05000f2001149004514580c4600240300ea5420515549100c5e0b0740d009001d0701130500104410401c200d100c007040f02c00c000d004d1011040e40390006034000c68498604d0450361307508d04e03101e65940c009214803810810202c44550440c0340440214494012100700ba000340c0782c000400c1200c034910b0609551640f500001a900c41c01034515040d0301d16070080c2d41c00d030f01c280f05410411309006811040716100e100308030345141c100b10a9840a68201000a40912152060078506c69903600c81d40700b51001001100c2d0f000c20400700c5800c02400780313800090490714a80082041002042c40041106e410015451615030b0200d900440b0a00401607040f8148083c043c03941401c400540c0001e142c8170503d414030400f03258690b144400c041225002c44080d41000d000b9890101103000c1d40c0c00310354040183c0c015 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 971576627 1250 971575377 971575387
    0x80d090213022101050607020f1203070c14031902040e03071a060f0d0f29070f030609090302060c130807060503010612141303270305101e0908 63
    0x901604000040c03070074140d804503040c030405400611002c101890040864055410040440c03101c1c491444040e01a0a100316081203545030351651080c00c0a0b0081581d4841005140003910020644200101d400c80d6a06040c801d1501050216a0b1810464045000555a401d000291a221140441e180414031171f01021030300c20450f2201d90000c80c1c450459038a0503c04010185d11030340304881c09036140d880e14000090119941e284060b40004d00030b2b49001c2907841e200d603401d90001404020903000e0041c001050b8010121440b205950b4600b40a210340300c0340071404641c5500b0020300180e0246001c02c0c1c0f20f1105c9130080098100b0341041a111549803036040b4501ba52961181c80054000001003022542c4003404a1868141210030300112085039500703040c050000d0a0707641d0a102d0084100c040600401710381015007a04041d01044900a1400170516505880162071600483d07a07044680e084902c5814400c5803400c100540200c50f6845c100300420320034070103d41c1c900003001 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 971577877 1250 971576627 971576629
    0x11040e03030712112206030c0503041b090e010507030b01020f0d1d060f1801081b0c15010f06110a0c0b0a050f07080a11070303020c040e10060807081c0c080d0902 71
    0xc002c01024040f80341d140300b80d240d1074045d00c01c807001541c0964209803410003a0880c0b250b00c01c08981d0040e030003151480407000c8440c080c54414410ba030103010414940500c1085401041d0080340c815402c580f01040b503c10754a005903120b0b802c108a0030040e4201940c9249081d0086400115107500381c847c115140c400d100c0884e2440e400010000d00e80704020030400d04a440c000e40186844900b0b107010015030425440344080718081240302450f0f06004240c203294002d04000c40840382c1d812022852032960744410101070710030707a405042c0005003801c0d40c074060b486002902030a0b0b560f00481c081d005525000003004207400c800d84c40c10420004001c10050300040340d015000190142481d156a0303030514a002d8403031003000d00e00b00c0254000316420000310342c01052442004a098a0104040e00d44046550a043c040c0f4154030503285000c82c0800d041c400081c9040c10740b81c2c5482241d440214400032000100400401c0c0800a18009040e1001070364103c040c01046035041400714503d41c05038 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 971579127 1250 971577877 971577911
    0x8101d06010f0f0b0703050a0e040f110309150c0414030f01020f1201050d03020a0204020d0b0307080f0111030919140619151404050903040b0c0a11040e03030712 71
    0x81d10481682c9070000c028000150511100d0f801441c1c19213150b46014807590303000c3c0442c05403020040501208280100031515035801c40b2031815075690003001405c2070005003c0341a001a205203207140300e01c0c000204801c0c1010249800340707400c1202542490300c0c2c801c045c504d104441c043c0c540c141c042c10380301d0b009409090024220162251400a48444a20001e410078010591101d44075444451039080801d07008035801175001d030181c40160b9a064a52a404040d01103500407036014851000300081802c00802e11380980d558400c02404000b04040350344503a804103031190385490b04082e80d0000d112280480d40e4480320300c01d052000804a5241455091143c1102c80f14800407100000c2c40650f1014482c01010303500c05510041210b044c0b05620000d2407600064038040c682d07940114000b030104206950040902c00c414a650707008480b0240d44620081104851425090001b9141450b041c0900e03010015040d00640c150b135500801142c4000c0740651000b0107680d189e18148809847c2 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 971580377 1250 971579127 971579129
    0x40206040b071101031a09040b0c0f1309060e0f0a0504032109030212030915060a09050c0a1716030213090510051201020f040312030609090c081608101d0601 69
    0x48010040f403049080014054951400b00404920019984c08a255a13116903494006030441c00682203591490712107010340c45103d0100e5801c66012400581c03800032a164501076a540d80270a00143e03940707080810041405549140043c540c02000542260f1150312440e4014020700c0c200c0b03420300e0021200e0038007020040c0344680071510f035182b5105241d010070842c981c162a500005203140307441c1c40065141c9192442c0d503903c446040001c01e0440e52402c60202c064010700c0400c000c04e04020b028005594043c00780313080410040f02800c81e070b0340c4190317100d0b500c1040b14031081600c540b50300d00c0c01c170007e61050b0745405510a440d038000c109100c0602c90300303120f400000c50104035a418081013100303c140e21151594568010051481c0c8d1445c980e007510101c0e0b500101c001c000424000d000c0d0084c2c01c25800460f2858501228001407007400c110040481d10060295002141d02c135500300403030380741170095000c2d0740e2000880c6016840c00e0381c4141b55060714902107080b0800c510015038181242 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 971581627 1250 971580377 971580383
    0x130212040f03110a032309030607020618070501021518060727120f05030f031f150f052104060c02070617010608182a0f0a0905040206040b07 62
    0x20340c0780060815800403095042003074440010400302c11250f0300102020b420389440c50f201300b020390408a6101443c1c3c2900c40c00100102510301a00d8404030003584c480c1c0403503c0300d1460700d5241e41c10700c201c400800c03900265141079016048018100c40b0311140d58030041c10019044c6444000d101c604c6600707001040c0141c1d25542c03a12007410300280170909503c100c03c2200a0b12005081c200309440381c940f41d400c4030302e50040801c142c0030245d09003d811405403030240250840c000040100018030580717200011031062680c003103801d4407200e0721208082901c003400f0204002030120204103001e0700281602d820000500c1c00280b20b06d8508003034400080c0d070700f02c0314541c8130805015056010300c03114000c7c0c92103103098400c0e02507480d0905103006044c410384051064150100360b03c0c1c0c1c228440d04d0702024000d07048170305802c0581c1c00c4c544442c0c1075a507000d10440404a104601e8078000080406090000b051620040d0811000d10000e14000e001240e101c0400c010028144107564098035440d40 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 971582733 1106 971581627 971581643
    0xe0a090518030c01050609100b121b04032d050d121407050901090807050102070308182d010201021c09030201061a04030614010302030c13021204 64
    0x10700c4454a424070b001c00101c128000303a054000ca80154820f48500f070036650307120000d803109141c0f402100040e80c010080910529400304a40341c0018091038130301500000450002200d902981c021242080319100c404500102500c0392071f40189002e00c1d912440c0000e66860ba202c900031044002171185003000c1090720b4220340c3c0200018030a0038040181030520250143c40c0ea0040052140000e02c0c3c6400441c00b11804515801201c00680090000c80d05640d94030705a60861100401030343c4424114030307199a2405039144251903800880790400c0c0d0300c6000c900b1003a2100b840d09056a00402c40c80da02c039103003589400b00c0303840d907103900041c091075034542280508071607448032070161001030f01e61500c4c0422000070012a84261810072856000c007225800c1042c0c00d11001e54580c008100e0010ba50a040f6642000d01003142801413401030362140501c10b00c103054805851440c = true := by decide +kernel

theorem cover : BRFrame.Cov 971402877 971582733 := by
  have h0 := BRFrame.cov_init 971402877
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971402877 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971402877 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971402877 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971402877 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971402877 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971402877 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971402877 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971402877 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971402877 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971402877 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971402877 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971402877 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971402877 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971402877 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971402877 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971402877 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971402877 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971402877 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971402877 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971402877 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971402877 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971402877 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971402877 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971402877 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971402877 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971402877 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971402877 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971402877 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971402877 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971402877 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971402877 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971402877 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971402877 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971402877 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971402877 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971402877 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971402877 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971402877 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971402877 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971402877 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971402877 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971402877 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971402877 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971402877 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971402877 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971402877 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971402877 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971402877 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971402877 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971402877 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971402877 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971402877 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971402877 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971402877 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971402877 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971402877 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971402877 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971402877 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971402877 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971402877 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971402877 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971402877 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971402877 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971402877 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971402877 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971402877 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971402877 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971402877 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971402877 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971402877 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971402877 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971402877 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971402877 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971402877 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971402877 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971402877 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971402877 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971402877 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971402877 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971402877 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971402877 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971402877 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971402877 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971402877 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971402877 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971402877 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971402877 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971402877 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971402877 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971402877 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971402877 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971402877 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971402877 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971402877 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971402877 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971402877 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971402877 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971402877 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971402877 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971402877 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971402877 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971402877 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971402877 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971402877 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971402877 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971402877 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971402877 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971402877 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971402877 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971402877 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971402877 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971402877 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971402877 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971402877 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971402877 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971402877 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971402877 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971402877 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971402877 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971402877 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971402877 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971402877 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971402877 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971402877 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971402877 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971402877 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971402877 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971402877 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971402877 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971402877 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971402877 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971402877 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971402877 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971402877 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971402877 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971402877 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971402877 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971402877 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971402877 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971402877 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971402877 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971402877 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971402877 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971402877 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 971402877 ≤ n) (h2 : n < 971582733) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
