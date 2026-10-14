-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1227
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T01:51:55.366433+00:00
-- url     : https://prove2.me/submissions/607cf29e-f674-456e-8b66-bc71e11f8c55

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 220503597 ≤ n < 220683453 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 220504847 1250 220503597 220503659
    0xd020409020a021b0a140f0f03060415060b03090a02040f0605030a210306030506071d13050703140613050c040e090d020f0a03091205070b030903040f0503071a0f04 72
    0x50b00180c204420107000f21001245641080034000d100d4002d00d0002c0e004520414001007e9500ca440c1d281e000c00001d400c40e10285810b04113560443c03000104c81c3d0300a4504040030a590b1301007811a846a60f0000052041403401e41c01d1100a003100005444216940d40000c60103035010b200c1f001896000c0c0c440c000450343d244010380301c1d806d1501029010f041c40c1c030300e080000890202c1d102d40d00c03014505040c03d424444101e000210350240e010302c0d0303000c0c0010704604a004c505501003802020103540402c030b104111440ca1071804025560b05500594010b100305051010ba0071040e400590707140d80d40e0910303960b00304075160240c0a4800c0f903c030340c102c0f0041541d05a4104109000a0071600003080e4580040e18040c0a4808501030013209028210900043c86070401c0424010030380303008026540d140503407945489800c14000c0c920380c03a840704400181e5186c0069481c1c2a01c032011704600c503200341e0742a810460b07400048103020520f810b20000544e01c241c1c10a501c00c2c50700c4042c110100b8 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 220506097 1250 220504847 220504873
    0x4060c05010b090106023004031202010b030c0a050d0813080c01080906060612090102073002030c030f1b07080309040506041407051606050a09050c01170604020d020409020a02 77
    0x55800b441c191802003004000400580303500041c243c28002d03031520306c5801103140f41d100760075a10030000111003405e0700140000c10016051201c0c0d6801920340e008108a0302c50b2010142c4480821140c158801c40c01007042c4078501c0c0c02c090300c40c0540d104640c2107103040c10524027010b182c4095445030700c40e038200c03500840c115600304013981d07031022207040504214070300316000541a00812188150010910001840c401425812165000d4000744201c2d09040c010b40d07194007204900c210008044084a81c100d05a17000105866100003494091402c00200700117a44850b00040d85035141800051240c1301b00410500000000d41134000246a607205285c052200352440601a9030046160502560701700310080502500311000e840c000c1d96a0b007900c11145005404a080600464585418441c408085a10044d40c041c400c80c140d8030100d00c00303001521400040c81c040000311a00340002042841c042d40280307104040382000504164450300214100c0c1c10448414026030302941e00a50070f = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 220507347 1250 220506097 220506101
    0x1b0a0506090106060206010b0304031805040207061a18040213110c0d0201050c07080702090901062c0a02092407080f090307050301060f0303050702060c06040c1d060a12031404060c0501 81
    0x141882c0d000901c419490f10723480c50f0017880014009820400c4015a14811010405000008205c0103105544480c5142099030041c544802d0041d50301d0f64400b000340c1d03142014035401114000000d04180d26559a80a12a00c44a4002043c0d05207550300200d800c041e550780050203000182e54024118011411406800c45134090000e140155062046600040c0030104403020300303505551a000540340c041038280506010b4104481c21100400d1104039108040d082d0384c039000c00b1140390302480e2541d402d01d00480c400c84803043d4105106402c20301c104108800300c5403040e0310349081c0c589003500d42c1c0c8440031703140c01501c14020030740e000140d1200b03145400c200080c05024124020801d840c9402e82d030100000551200070144600803508105566855055504c10071110040d24000e16052920071120a01030042d0300c05005400210b00640d40d0303c50031148964030151400318607508040035030101d200c40105c210100076468204040c900c4102c0042c2004041949404c488c6030704910f02242 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 220508597 1250 220507347 220507349
    0xd021614070b0d0e28110906060712120507080108010510180b0402040506070501020a090e041e1104060915050103150510140310030201140a0e061b0a0506090106 71
    0x415030380076040c01d01c4910a01802c894518001c1c079800140c4050b04e20081d420100120500d804082c2d01c404114148010b074032582c120944242a865070103022001005401c01090300d080b500150300340400f400117442412010304400e003038280394800c0e00002c3c84e031006881040310280006006100100300c3c1e40800d02495070882080040403440c00e0800a20b02c3d890450284c1d84800700b41c644907500a240c40781d40c121405880007500c035542e210745034104a8081d6009049650001c5c420394000150603100816060280e5070049625446281c198060f520840c00e00e5410b4460824108a000e4503035214030a0030f004048105010038408404022011b11403000d074861414942080d0780c604010300c29036861419104111481e8a000c040d41c1030807034803980d00303035141c21030902d0000a0201c490783e8124540d0880380700742c1e103201c00e41d42d42104090285c044d8101d00c00c00704040c400d00d44124608100504ac191205101101a550070310007214940081f10701c0503a0141c208a0a01c8070412080c02010 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 220509847 1250 220508597 220508633
    0x60e1c030e0a0e06010c08160b0c040305070f0303020307020103020a03060b03130201020d050702010e0d030c0c1e1406030f041b06080402030d09121e060518010c080705040e04020301020d0216 84
    0x50380c44c0c081d0010706466400030000f800041c000940d1100b0440074007500c413401743c00110002c1149001900d400c0700e5403040c007080c0c5880c4038070180081c000c1c0401c1845c0f000d480d4598091400d210302540158040d4001804500c02c0c1600c031000030401d43c5158000e103104100020601000c01024000a41403030000000f18081140404c01c400260740c1107104070140d02c20a988030340d109006030800316170550950b20010304402c885000001d00c0d0b005500309a90003000343c150518296a10752240e02040394501c855a041102440000c1c0e0215000c240a0303889401152401051350300034510700410700340c070b40041d800b00380e40314240700c10741c1820020800850154180543c00c1c505141d05140a00d6445000401d80c180e128a5101406440743c20388240e42d901000c18440307424580404240c0349d8510508220541ca0700d0b11081c5014881c0c803850b800745140ba11014501401c190800c0c0034054010816605507400300300800342c144140c80200340683d908c0d4038001020115190511141021440c1c00c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 220511097 1250 220509847 220509869
    0x40605163218040b0f01050f0c0127030e2d040e1903080f09120a022514030a0308070e011112070b01090219050a020f06040302100f1401060e1c030e0a 66
    0x45026036000011100b103814a41c04041c0c1300e1990010f400d01601d191300280006100300b1012542541c1a4101254031510035103c10701e00dd42c3c1041884103039007070480d051710325900000d5009202140c0040300240e14401900118403040710520343c520341f800308106601c180d41311003002801d140c2c6c0315140a800c0021944011864200429603e545004240b691200e103c000540485128020050703070840b80081100442d8010f205078440d280b10b034041c406c1c2e07a1b41001d83d40350080395207400300c6e11a0200754113031036a5070a601da080d0215110140c2650b4907051003400f21442480b104100306826000c00107140e0144d81e16154a05003142c0340040c0d0003050baa0340107001001da2181d45d030500343c2c02c44d41a450200e40300c0045200403450000c2502d20b20788280076001c09d100c04e00d640443e0400070744011940a020300740070441c03020111030b6038092405441d0068401840054824540341c00d10107801024000b00c40c980ea41c030704418a1a5900480204041e2008120079007440300d098801002c0424107 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 220512347 1250 220511097 220511119
    0x60e040603080f0306032103100603140a0c0203070803010f17070303020316060902090405070e13050a0b1315061805090c12190b040605163218040b 65
    0x20342e400d5401902554680303000003100003030407a02c0412426510409000002c084208500001ea91a910682d20403030070349545075000c100701e4000d02803101c070f010351880303183c0d515550f0b002900010100c860030340045000401201c808074042074003840c00707030007060010981c403483c050f01c1140511001c0307074011031600003010030000302e50088160317400c04200703900c1103015030b0780c03450024010400300c14000e5112005805200620400040351415600c0e12900c0e079405403141501d504001c05040401481da074450080f05000904d8222829041680000d0300503c0d1001c80e9a0b448000c08000031424249079a80000c001e21803c40c050480440d400003c10000d504110700305039110640102001c3c001c0d00d441a0300350903120200518801d100d200382500c41c40c0c000a1a10028900341941d05450381400c10000c9032042c9a800e001c600c000c078482d21060043c00003e01d0201390340c0100a020781140d440c202c42d6040c0c441d060001071a08140782500500750030709000420040f81c000360301540c020429146 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 220513597 1250 220512347 220512353
    0x5040801271202010207150b0f0118052b140c090c040603050403110d0309020117070f080406021905120a1505040902190303180602061302010804050c0a060801060e040603 75
    0x1031480803180c0c00551880412841074826806841b80e0880100349801d102801c003111f0205034084603005c481201d50828017020180119006e290b40d01d10410442e070959410407561410000d8036030b40f002603100351510340014118040204100400680321100124441900301c0e0080c0300b01e1025003000c40d0208854100903c04032541d00850180b03405165944c03000c501418020141e000e103401c0c10404490303030304001d280010301910649a00700d000c5602d2046030b84c0e003401d1000b0b80510841c0700d45d6900c07146c0081ea40741220324143c050400d0710030325401c200b854905070350b00d1520360700c44566407240c80d13a8100d20541c6c00d0b40075200508241046140c100401d51072080041440102c1d4001c031004107502c0783c140001843c491810402100302404100000200740d00800c00441030340b2070f003008200303c99454901b070382c44a0003251480f070641c070140c00460066000c1d41c01d0f113401074043c0c0211400500d602d0007050042030039400c1030000c540322800412849502c10f240f1600164251414006280342da5 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 220514847 1250 220513597 220513661
    0x30803040501050f0a29060c0111040f12171e0403030e0f010503040f0b0a060905150f06030708040f0804030204020d050a06090c020304090f020913020c01050c030c0702220c05040801 80
    0x314142c1b602a0807014040c079196204c1c015103402c3c080070030081194030000d50f202450390340300348a01d030078404d0000380018204903040d80d078502980d002505801403080d0f0403510300480e40300184209090405900b203500700c1482a01500c003a510035200c03c2d280314159410040032840d111006410841c0800030400010b6404945044455010160001e00d0321b40498a80c05071041e50481b4034412f103047c0800a0321030504007001c004038415031b40300e024480c20b18140007043c4400c80387c0802154a010101b00081c8032290300485840c0142c602604042e103d038006400c0c2d80c08500f211007034540300e009008040321584154030003488096003c121101040d007001e5121b000f80d01c1000601950b410800c0030342c02440e0101c0340e04807001011541d5650103500200300079001a28071948540c6084005042da152030400c5034000c0a942c030310141010302540c01c211b0080c4c4500820655a09c1442c000c980c5072181e4096902010595255191110f0030f04e0300040c21508204009414071000000341503a0043c14 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 220516097 1250 220514847 220514891
    0xc1c03051b0712020c0d0f12021204060810030c09090b1f03080c0114010806010e0a1119090801020d0f180f030507060b0303070311010c0f05090f0406030803040501050f0a 75
    0x2050a0300181004828240d04040b20703883c69a4006c0810034840c2c04015209500300031262141501545a010301002240c1c0c0c1e00a294200008860812040c0122409410b00d0355000780b050b00c3d503d466580320350741c00304d0924040d482041000e48a007a4102000001e1217001c2d881200310340c00b8074141d25001d4084440100c24440513000e0500000c03200d110b0075003900700141d0156624000c0509503541c641055071a10244240480c5982d84404140715032264040e8031041c0d003007044503d0404410815001100009403001d100b40103035200d00113402ca00c280090300c0c0d101341c0c1090000c2c400e11096461800d48030b00544594030300c3e1109024800042c107940c0403a050b03a0305441e116403a0000303490003000038960b954a01d54184004100482016403080d5003400c3d14001a0082c8000c01080d0003c0d141d060758481c00c1e07000b054051044804070b0074242112148000c1c02440411207903545c1e1591502076200703071420346003a510303034041100c0300019210340d58201b40b43c0075003041003401c140c1d08100c0070140 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 220517347 1250 220516097 220516103
    0x30303010501030b0a0e1305390409050607020601170f19020a0305070b13050f0307180f0504080414090f0f1e0a0b030606061612050c1c03051b07 64
    0x2030344e141491540c982219180c00341c2944045007115050aa8041403a00000d05c8110740a20844c1c0680d1981064a4010f41e032507600a481e402d40c01401d40440031103025901001070704035981d08007000204034100451401003080c2c1c0c014082e1541810141126084040384000351035028243c0a02148400547e01d29061006c1c41c0400d00e500c0c071440004c414038550380c005402440707420b0000c61503202140040065004000d0f0400100b03039503030f052101840303e945116603d80c100b030008104800c1196064030000c001042c002461100c00d140160890b0030585080c0d1795600c1c0414140721071100c900d4900c0d1b0000d4200d6481665140580c04040070040007840320340c01c1001e001c0030810340c11840d03070340120550102841414070300d008031007030004080c002e49440c443d00c114804111a410300c0821580780210810030f9001d407607069101c15051004071050641005002c1100c42d4a103441804130091400d442d03d4200301d51100c8e918000e058070b4002d0003142504036081e200216500009007150f0549078 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 220518597 1250 220517347 220517351
    0x711060a2003090c031209090a0e100b0a0819060f02090604120302030426011d030d09140304030c0e06040515010c0f02270a0b100c050307020d1a07030b03030301050103 74
    0x910f82c00e06604141d00485800e0b014864411405655440300c8007404c051103080e1200c0c15140d0b100d2000405803106c1081104258112016403400c5075a01d412038143c0702d8024200a02d1190f640f409140307464241c000c0140c00c500c14982c14410020280111210300701040b02c19402c04d03e01c00000f0ba094841c2d4400c01c048010790090075420503000b841641c4c024040c0100c541481e00310a1190070711501c412a01440359446c0020350000c01c1300e41403a0446943c5800010350030a50b0107580100140408101501c5070640c0480820358028100000c1000d0f6105010411505207403902d0500706d1a0050700e803d114608010801c20000b0f480c070f5019600e0f00c0f00340381c0071980c0c0c001d5040115840442e42c2010350032121107981c6801c40c00070f400d19001d0070990a10101400c1d6104a100c20469294400c101d80c80b20f010001080301a00c20042089068050001d680c03607c40164000b07000003d450000b2620101c44140480c40d500c40001d246ea8444102c1c1000e009503040c0d040000d85900c81401503605141d = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 220519847 1250 220518597 220518601
    0x307170a2007060b191a040f1401120603030e1314090f07050114090603190c0206012301020d110c121c180605070f0503030711060a2003 60
    0x144650071a4001a8511034034104400200400d850300340d002d07900070386180e8101514118a801c0001060103500c10440440e4036850418040e801d101d0201e10200660030310500020680c10101c0440e08000c00b03018400851890039100054180e031a0701c4e110342c1640385008000c0020a41102c0c4501d0812400c882d060350903001d203e9100001c140312820011609500b500b0440c03500c01c00651201100804002c5a00c23180c0d890b001110b00392022401d100c100d6006209401450806001454104122a140c149090b5420942404039070099800700300681c000717401000600e080e01514002601d40360b021b006000e0000002035603814201c1d050608102d09640114003c55050052400c0e898004100c103903404240f0010070f40d10300d0366501c070280b8402e02d51100d40b5010701600c0000d0101d0022950120018503000007500c1c02c5c2c04c451401d41d0549120303000341c00020000e100a620418643e19491903080c00403441520f046402060507901030311b0004a03036a1003103000c1d160a001d40240350f2560f030769 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 220521097 1250 220519847 220519861
    0xa060c020904020619080910020f0d0f060b0f130b03060603070c050c0d0c031202010b0a0905222415050d0809040e03031f030308071b0b010603060501080606030717 72
    0x20b44580074044175039982d11007400505540c0800150301903130f43c1078112040c1d01e08699810003244900400c95040c40740803c103442c0c5002c1243c103c15801f44503e0340c005001d48c3c0d90783d400d000c1c0f9070014081180c45c4000180e25907180500060302405440180003da0441c0780c24004035940d440042c000c50140140c04414030304015003042260104040035045a0100d0301c940303001850441c05010898213513114010400140740f05104903855400d00419200c8058038200c140e200910000c1c00c2d800015002c9036990526580301901440e410f4414000003030548219940110442c40c051512424541005603000c414a15202c412083c2c0344d0450301840140100e01e40740095104400409800a050103c0000401c0c0c021011314401d4942c26890f5480c0c5066420702d000c00162804018046803041d404212203d1280d0f00515520031080303002214111030351110103555000b41d00600000740c03a51002c0c082d079607000c2d909a400c881c00741c50b0141141031480c1d000d41408410398500d1000b10105000600b1 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 220522347 1250 220521097 220521109
    0x130b03100e0f041b0b0406120e0d05040e04031205070e090f0105011e090509091c0c05070603050703020d110d0609110d2004030b07090605120115181d060a060c02090402 74
    0x5208201041e5606e5542d0000034010899210b1004625480d000c000c509c03500c00820224541307903003a95041e1800e4204010036401c180058025400c009015526840c44c00d07280c4681d501498450b1070b9000d20600c403504222914a004145020340300320b000040181d642c0002c41c0d00c448882642c00c000b07490000300d03411560b4024541c445680200e02e401405410f0754042400030321a000300f1010360100c0d00441090320141d441d140e00502c3c42d40b0180381003041da407007a4030041e0014a14075015150440c1350000d80300307a5800e06600107000100040345c50b4441844c1c403506005000e0344000344801c105094235500716000e1804414982034503114245d8080340341001c0f44a0501c1c02c8801103031070760f4030780c1007a800b02c603812035180012814100340840d42e1409403041e0b49030004c82d041300c80c2490b0300300030800942803851442d0390280070000340a007411127000b80c0681e001c0e101520078492044544c1504011546000d0f204501800425000384100c07136004985d03101154064600e42c805450760710200c0c813 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 220523597 1250 220522347 220522349
    0x705010501090506090606040605090d0201140c15240d05150406020d0c030b0d060e121b120c0a03030b01090914070e0108060f0f0303130b03100e0f041b 67
    0x5551909002191282c8680e000301d00415081d9608a156034900044c4000d5110314007420300843d90610101c15140380c0080c08400130b5106141c8a6a04000e405159080703401421003043d10740c102c0561413800c080c49100065004c08a038080d19410007a000c82182282d443d02c80c103a0007806552000c00071f20808115540f01b610717601200004614180c140b11000350480c81c01c0362030417070400c2e04540c0d0700362290280541c0c1c0301004090f21222191540c0b030000421221014214030301400340e2030062039207040082c0074050789851b09052031907e01d02e081420a88461218621306030103025010740c502000410121050341b6040003e005800c4030016547d40c086039000200d6107040020210b08041d50b5290710b8000c2901d030300c4623008400c600d0019a01c001c0110340343d40c3c00c09071103c000500b51400c0c3c1c0982110785e6016090320300c4e182c010b18001404513207541281e01280700c00030a110301903500d4a0054000c0921202d222010b091050f01801420300140000d44000d03621100e007044000e1803c2100 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 220524847 1250 220523597 220523603
    0x210230f0c120406030e070506030a0c020c030105070c0606050d050a081b07030303020403030e040b06161103070f180e0c010507060209040f060f0905100b030405150c12090d09180207 80
    0x141d81e81c02d400303100302441d840760041200182c140b180c0a5485000061540240d41c00105600d007145d89408400d00103190005000085100b900e0b001d100c5600c00b8441c040c0500c41c203999480007021a4205541540d202c0d5029034042d850b01100304011810100381241d40340c0d07103d280c5c01d03034074040600300078001512820904428006c100c1d00004054040d40144200e9200b40c907600508c0c4030b020204001c0f180400c0c80c00ea0010000c0050400d094814411203801c2482172801c2000041c42c00003080c0b600165400004120118000a01c404c0303c1e083c0300030910506040702408640e410301c00c82501e42ca12502400d0601c030f0046003940410580350161340840c070b805001000076128084441e03015151a10440d1400d10000d840422824100d0107628800c10003001c0c0719003081c5ca09003000803039034030041066030355001321104e010944890403407190040d883c0011041d2210079555200704207035009403c0d01c0301c0354440d007404164507800114601c21030b9800e05404681c07040c9116000041d2051040007 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 220526097 1250 220524847 220524853
    0xf0303090115230111120d02094b1f0f020304030803061504030f05030a0210061d0c0d0c02060a110a0c06050c120f040210230f0c 57
    0x20420340c1507000c480004000034a400d01c0c10740c1c500e20240c000300d001501c5509909540c5910708154083d0304101c3c102000002100d98500441e588410305420040b001c0013070b5600020180c0b41443d00741501d07042c100010764001110b0b4992280380340020042041e905050318644140c83c210840405c00500800c00900030020400b405a00f6191000d510140c80c000301342c0c003940b030300c1c055840001070b642034903482005c003861522418200550100c9001000d110041c1c10400400062134007001c911a180c804c00045403142e421031806401d140710000350100d000c0c0780241c1081421029101d00035000d0368903c04e50031f2610b5071800049a4440c004c2c031492090704105011807150f034001a401d00c940c202c11000c002c400708030721410096101c0c6484ea00c002854142280c00800c080754405038110480907450ba20309030044140c050100000c49a0601c11030f00c4800b0401581050340201c03c40015900e45001e000490070901004a0144440e002c0380403004209041c0f0103c005045030040503014040b = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 220527347 1250 220526097 220526101
    0x20709020307020f0d0f0906031805011103040c1a0304020906040e010c2304152607090e1302010504120206090a15020d020718020904090b0a02210c030a0b030f0303 72
    0xa13581d00316002007a2041e20545e484849003912441c8603521401459480c0c00105240603c02c9003d00f122503080910f0302d03102c000501c0010424403801207202c540c00c01a54507841c15040c800800c200c2540100710748105034501c1c3d4012000740048076405a030403100c00300c0b95142d05002c28024458040541441d43c07031f109900907020b8100030341001d8003c500e6607219984440e1105c0840383d005502c11084102c20000078500c095019841031076283d04401d03144402c6280784404034500c2c400c16107000c00800d42075203050200c1000c410031254045554400c40e8800c441b6a80020140e1107a4840c154030448044103d100f1940ca00e003c41c5da608800603c1c242c007064640b041ea00d0440d000c3c0c0e0460b409489440c0c2040441c500101e0150102e400d04281130841c484012040e80c069444488559442030342d80c10300c1c400080706140440c2c01740d031130450016120404601100746190310103d0740100e40d41b60000f08150350800804030707640031301e0002010032011207000c04240340460011baa1540c900001c01 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 220528597 1250 220527347 220527361
    0x313030803220830190c020a050c0f0d0614060102150f070503060d061d0f190f02030f030a08060901050d030c062004030c03170306180402010207090203 67
    0xc003460044204650807410a8034102008400c0c00480754001c108400034403041c0c03400e103800c41c611519002021144000f05411184030f807581c101c00c88000c03030000c501410411221030944119558160709000406220400e900d58568484008000621a65080414403080d403242043d10b0b450380d038000014007801801800c05000c1050481d030184c0148504549101d00c8480b0104860040000102c0e418540e120f016044074540d200402658004444400400c0040c9251048080b030b81c0880100c131b01c3d40c60a0010712818442c02c3c103001512a401142c501401d40c01c000300300b4495550000c170200c010b0159201003403d041104820305003c1c0000b0a109440f250030420b410b115201c1212011843d80e2a042040300c804107184010740001d00e0301d1607400c000748055000b5074a21102c5062880400100401e904e081d40c0a41c1040301c0d40380d1000010400c001e441800c180b4031914841c03d05081d46004004900c1c0b00c2c05a8445071491a0f5010108041da4020b120100181400d24402e5541e49082c003 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 220529847 1250 220528597 220528613
    0xd02010c3206060906040b0a1404021b0a0510021809040521030a0615050306060901030e0601080d021506012a02060301060c050d0c0510090c0f06090303021b061209031303 75
    0x5440f94090080783c2c00191081c45c0602c1151145400100700b4209a4104650b0340400e08048002c180c020760b080040d0107440c3c0c1b0200ea00620001d99600808880c440e03032074140d0038503480e900c04650382401884494806d00c143d22404041f0b8005840f103c1081e40c0318103116203000061071700c1c01c0500034070081e004c60000100703000318414450a44188602ca40d540c1200380013400c0d09003036500107582031000c1a4245805401848004030500d408500712041030392543c10071030283d019035002c1d448105072200058040c0402c2c0d1a180034000500c03042d02e000800607081031417180003690075044110b02412041c0d900102940d80320380191030f0300e480c0e43e1034010107088014100c10a4030390b48119423510850702d100d083c2c002c1c1c47c168008040d1408004080e0034501030045076504841e282d42a04000c55503207080c541e040001d08090b52900d10b42803641c00c0180c01c0000c42e03a00900140322016030f1054a4840b01c0494050041e19a41080680d076103503005415030190070094800c201007080d00100b841005 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 220531097 1250 220529847 220529851
    0x5070806030715050904020703120f020306041107020306040803060d051605041103040c170f0f030307080f100302060f0415090311010207060c0f020a150315050d02010c3206 76
    0x5500b01d401260311150703c420850a200c88020002e082002203800c5410b264001d001ca1510900f00030800351100303d08603042d21030686203204065804002c0003903034034043c000c1d09424403040440516001c41600840d032580ba005201502121000010417220f80712001d40f01580754200003501d0301c90140d1160350348400080c1c89198400d50038101d8007410040c414040340c3c0165804a406007841d490300c1c407002c0c15680906c0c92540140140c1d204428014818801c1c6044500c00102659980c90200c00240c102d000c050211841c10000c1c0c0d0802210b00c064590400c01d69404031010b80d156030345651410800c0c031031078104450350050380e24030700000c40c1c10040500560703200d42d8080c0700d11483e0000499030360340c040c4a00c200150860a044000c10f0f0910300ca415214009480c17040341540710064441425083c4926400095466194101d1303501194249000340c481212050a070a0290700024102d104441d00078280d150022030364405901c21000d800c548984c48103032041c060f4924469540c0311030013 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 220532347 1250 220531097 220531099
    0x16050f160209011a0315010e03072c09031b010912020f071a070f060216030804050106050301110a050a020a0b0106090314071d040f0219150c030f0c020d0605070806 72
    0x4500b00124807000d6469848900d04621300001e4110380c1c4086001c9005125080128184070320928900030a842c1400388a002d000001c02014000a4a01c0c1110401f45030b9240c40042c07001850902103d520044122404203e144055000c000d080c0c419031801025503190040c41c1200780108283c08a402140b28102c891410090b1481599230740d2960031000401c00241182a5042026a00292545d6007904a2a00801c0c0040c20040714000398106107001400960203d000c290030403081050034014040544800d034002d1000c3c2c0c002e8140c0185c030b0b000b45075206050000215039581c50340e200f080a140032a404c0095000070f56990b8001900d040c0c0640010b0750341500e0558a19080000081c0d50710480707010309183d40d01040080c281060002010300101c5203c11180f40a101517501d824140703180301d0113800d00300401ea29040d1490802c8802d84021014070003244000004aa0000c0303011013001d089041030125001141300060940c80415001040640340c0f5052104007a031200420b481650 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 220533597 1250 220532347 220532359
    0x1061d1e040f0e07051009092a020708030301090b04090609060203061008010e070507030908010c02151e0f0910051305010501050904050a1203020d0c0c11010903050616050f1602 78
    0x46407550302900c9010f05905466030018600f0402c0307042c08031070206200c0c000e00c2c0182c42c043c1c46400074026030700c0145452030401c00a40208030300780882d10081034034091078002800d6031131810a20039181c0c0414882c120039140e41d0040320315a5200c9411004007141c0c1311208204401d15494090000e400c1614060b0007010000d4901c200d49016100050680c1d184c0d007108001e036590004219071a61000c0000c40030011552070000d041b0a0901641640d21032079009840034003640c2c1d121210109006162060030b050501c40301d070204c0440d401041c1c0104026080d081559a107110003032a00c40c003090006400c07032410042100b00403509450140c0c40c2c0c8034400902490760b071032042000c0c0c0ca0b800d440250068214001c110001801160511005d40090a02509024500c001001140d0b03032884128049545101d030501004002d010705465a98242400d00c949411900e034503565400042c40b03800307812110100703c0c0343c140c06002543c08940c01c50780c0c0c26641d507950018500b03151b05200d5003240a84 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 220534847 1250 220533597 220533611
    0x8010303030b04090c03021002070f180c050405010e0f030f0a08030a0c020c011b020d020603040317090d0f030b060f07050703170f0304060b0f031227030601061d1e04 73
    0x464540200f042d040e8005c001500c140b8115000c0000c05060b0391244810343c0301c0c030600000c0002050314450010150321285a4104090917580010313510702c40025010000b04000901081c0c0c3c025240c040d11081c1540d440c8120645540801e18050000b40f1900140c81030712580010410480e00442c400c5c444a14107210500c0000c100342e035500310501000b4042a024003400c0201405014600e005e28001805a218074003d5000b01e5900e500c1038401b500003410048503100b0300e0015103c501c2d040703a41c4800902d894107075010300038a1600741c550240101a242c1f0081c5d8059030320001901e4841540702c40030782d60b0703147d00d14040343d41d40240c0c8001c030385440b015011f000412000c03400340c412152410803114035656655884100501e1a40e03600381d8483e988070031550442d1402c008181018403414400f41d0b130f4443c046444030074444164041d0541c0600d0051007002910301060460454000c0e060083d45070801008424403600300b8500c698002c0ba100c90040300a0791402d040c21003454058900304141 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 220536097 1250 220534847 220534849
    0x415020c0409081204050c0a0e06040b031506010c05070906080102090a0e07050405130e010507080714030c07060b0a0810050406180b0103110103020702040204122108070c0309030f0308010303030b 86
    0x40c2e0000030300034003a480240801e41007141200d240990051158040c0d0742c210700601d00040500b15590000c4144441160403c0100d003003e21403103000610403001055a18100d2000071250b050003007581741000090741000c0d00f0400100419400741c80340038020b01410b41c403601e07524000d4101e11b0200b0310a140050002071305059020322035024420701e80c0c5043c0b07454100002c6c441000341081e00c440c145070b82d0310703201c1c000c0c00c1d028800d481c040c520655607100c60b400c10703650082c2503481c91603a60400000130400e10026803840c01c100c4101551103213000c600d1000301400240300c07424031f81c0840824002c1d44141ca20390002903010f01d1081e4843d90080001c241c8001184001740031100d802085890307150014400f19101c2040304c4c101490501d400b6181811542c0820140c1c7c01036449490001c440c11442010031000003001a0000701c10b00e100380803650310700740c004c0440710040c126805000c0c0000c260b0043c5885440500d010319000000b1142d20f800901d4004d0a804003407100f5000207140011080b01 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 220537347 1250 220536097 220536101
    0xe030c060709060203090618130506030705010f050904151206020c0709060305031b071206090b06101d01140301061707030c0e09150312070302010506030105100b1309020415020c04 79
    0x5450003980111b0410000006121150384421440c883c0385175000d00c1c0081c00e0b503c4255900b41c5070301d18540400c00d41440405c0c1407401950750040c5040c000c0003100304003c0c41d400001e80d2680c140443e4081420011a503008410681036040b10304100b1092540c003040c058543c00034044020844112090241d540350750b0821214a40030007400d680080181035910002000400100c0c2441c8050700c480701c0d501c15400402d034101d000110b44242e110b401050030b0140110503103510042c1074901101d86c1d010400000c0000d422440004d10015041c4030803107099110304d2480300e100b08404049036580d40c407000040c003410701803071280704c0283c03100b00051046407003401000c80010780c980703038920000f0310b0f6000c000d07490300300404c07020105072400c000381004d0703904000c2c06070000c11481d45240e0703841540c18002d0948a0080c00b1034003d81c1050f060010b402c051101e00700403100c0440009840e81c182c2c0c1425140d5440c5940a40201ca001003004200002c850203070700d44d40005038007243c42c10701c00c03c0d0038041 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 220538597 1250 220537347 220537349
    0x271509070e04150b101205062b0602090301110c010b0109050109170f0102130f0e0f0a110903151005031203010608040c120b010603050f090c011404090e030c060709 72
    0x198400c41d0354003007000103148441d2909140222100490680d98200104092407094294000000d07074400446860280794480d0300d400007425903119121284040c03241005072983e646002c2800c4440c0ba111003801100e40c107441512100800a000b0b041d0243c1b400b40c25030304000305d0580f55520709081456658092038103081120810707101d1040700352400c0b800c0b941e24913407112102414000c0307107503c2800312000e00c000d02c07000c445100c04206207410b2078101214008a604042100c0c100403082c45500d20b0010310965120500c1d8401003121070b01440d2614990085c0c0015503010710810400101d83c5403045c01c2e19114031204495051100c3e922020150703941c0c04600c2d5045112403c10040c41a10b201e07800c0341d81d005000311403c40000d595a9281414544a0001a51b08005060040c01a07603498040d4941040120720050443d04001d0603054988409043c060b05214410484807070390761842054038020700c01d10be810494040004c0c45541c40350700c4454814018007620001031516401051210 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 220539847 1250 220538597 220538609
    0x501020607020a0b06041113030c0f0b091c02091003050c0114180a0806010906091107111003060510030905010c0f02061602010906050705180a05060d0527150907 71
    0x121400001e42c07241207204d64003821082e001615400402100c894810040424800a00c58142014514109145402140c3c0c00c1510400601c400401410320208207031443e0603400c444810818072882014a4079021816001f50440800020083e504418180c4c54084038065015908002070060044481101048040e00b41c0401804000c258284011201c3c411540182c4103130252a101d000180c6852070990108030364030b840794802d2100410b180aa514124002d041e52814250180d032118962801e060b80395001c1c6021808144850740b090300504000e0401a081c10680401800003c01402144600351855820301c080d483c80c0512840c41d00145a00c0d66010b071a040c1c841540c8200c40980c20803c81e4115074032030540c5804100180f0a65014079020b84070507544031800821060b19680292006125002c022010003264480400b120740400c0b05001c0000c03550340d1410300e500e80e42481081c8121080c14446404440540000c20403840d081542019580b41e644816140d0341c0e540d18009c030 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 220541097 1250 220539847 220539853
    0xd03060b0301180207020d0b090a05150f0c030a060f090b210319050d1b080f010308030a090c08061518100603020904020c120415020f0303040f0510050c0304060501050102060702 78
    0x180c2c00f115a0340e0301030980300c2d00c020035524608403030b9100c072040c2c00c10990b11800240c0104420a0410000700005030107612000c801c072446141c052607a18001000800d15207880c50000001112800d090f4043c4020380300f001c01c0d029000381c03100b1087c07005098a0000303d000782d900701c040f02800505091400039209a4600070b5150008515071074420380ca50b1400c2e04284034060102c01ca295a9034046d0914080e40050200c517811106a070041441e00c0151401300d00d015900300500104128404490303021240040219a0742d07a0b5203000130321240c0c00d80c0a05118003440086c0629110562600480180121112a0083c4521a0aa48000d0180c0f201c807291003128004220701d90094001d0901c44a0080005040c03200304030700b00f4100521030702140c0e02d0701c034005000e00c40b00b011070116850441003403001309071512095091039a2403002500261110b8000746601c1b041000400600081c405010410b0025042c10f2111040c240c009035011030740c05d0309003400816503503c00075055114042d641d001b = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 220542347 1250 220541097 220541129
    0x6031009020d060f1505010305270a0203030309010b0103061703090438040c0203071a100b0d0608010c0f08060111032b0e0a0209070f1b050d03060b0301 67
    0x11aa0040504110880e00810300c0402100824424460b5100c0269084c0300469408544800121551501e40009050501d030070184019a02d00311308103440680190703440314060f5140542c041c80c1108900300254188400801c01c008090103420440321118280c03414030110351107903003808042200c912001242d0b481400000c007030b442d2a0700701c800f0240c84c2c040040c102ca10701580690401c0c0030031004e1340008c2da540c940325605081c070740b00380710720b4042c82c1c8041c40c01d101250b0b03141c00c1c41d0245000d10305d004940703010105021610000031000140f84d841019660b941082e803180307018040a100f01d600c0b551134031110003116805518403007168220b81d03a03030404076500c110040d54203405c3d2808240680c44140040301c400707180840b941043d040c009420540c0c1c0c3c091601140142d035002c50710700b035454001c488080d0041c0c690700402908881981041408031100d4a01261315265208007006c0504e40c00840d60180a07020903042e1107442207540034045c041d280d20484009120a100f048181718107840 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 220543597 1250 220542347 220542373
    0x1d06010510050d09021e090a0b030307060b040e030313030e060a12050907170c0a090b01052a0615240405060c030409021218010e10050a2004090b0105030603 69
    0x4001c00e0195800c2c500041e008801d84c02007014150003480e02c8001b21008000602e030b9252880c100d80c1d00c80c8010500744100c01076039000c81d8481c003034810000c0000c0d85030200840b56995642105070358105005c1100c0e02c80c9402811000d040f52020010f401080f4107544d90080d90a00d0000c1384c0d4200d1544c0c80d00d80c14403031608002130080000078201c0495014004000c03540c11270108200a4070040b20000780050f10080041102050f1355a014410b2103180440c40c0f099030740c0000c10b07034051100f007500a440340b03408a030345019440640f0707c0c111450700490301000061a0020031012424105a80741c4110a41390003103140300800310101408080000c0c0803c1249180030002440b10231020002d5074101030381d40107090113030b0300114070742102507200c8000c2004558003a0003c0f0031094544009216410001e01c0460310ba0542c414403406098603480021400f0200d60400951000c6420300550003030030300d40381c1440b07981040c020f0480c07850400d04602c0c0290310034815207003c0c00c0002c014210340c00c2c0d815 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 220544847 1250 220543597 220543607
    0x1006080402031603030e01020c0d05151306060902030f0c07020a0b030a2405010f090e0105010e0a0b0d0504030207090b011403070905060a1205100b070b0406020417011d06010510 78
    0x380300700d9061040f211650080c0c06014030402c0154401e4461103058035494001a090002034007115029090b5980c011001c0761002418000349201440320285603111460340420030600c0407005400e0303d050110005621071540d000703610583c03140d04040c02d562550260200c103440381908c06940a0750151052108000440080d9040490007070005200811040620282c0501c1d04446036044001e100400c000d58000a28608000d4203140c529039540c14904417040340c69060003000d04014444419014035100e495418003d0086100340035101c56408042c5409000126030440050050035000100c0409500420402280c140c5031400805910004100c0f9508010411420450840d40001e041e844040013046683e206680c0d590b4021080c41070141a184c01034101e04880303030340c10020014403d48605032000c03503a0041e281c3c0c049171039a003080c10290149070860301000540c00003c0302d80940550148821715405c40805005401c0da214058442c4c42c01d216082e00034103035100c000c420610038 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 220546097 1250 220544847 220544851
    0xb071b0e071d0414010e0105030114150402040512030904110901020304090f060338070504030305070309090f060e091b06070311071502010b0d030e1c021203070b0a05100608 76
    0x30202c030b0b84581070200150139036003003800a10300043e0403c014000016403c1e401c41c05070206900a01401800580c841a5500c004040d030742c40441c00c1d00b086120399500e4040760000c00c002020616110559480241c6a40c40300a00e9880b0303070310b003000190401c00c1d07010945a00345016005142028500b08455003c0c1c4400346040614903a0780303002100040901290240d40749402040841210149580d00c261031042035000252803104003c1000d101e51001c1150241d035407500d0004d03210b00c154603003030796002d9042c1c205012031401c04000d805070799800e078400802c030f42e001406044d080d01c0e14001c89865803402ca100c49c50131401d4001e192514100b000090803514400d00e131054500c4000742c4200d0401c0b030341b500b1002039052025a800744043c2d0900400d810010100c03924a50904c0d02d0740c000e0030180d00045164016134041f0500c10380d00d41040070076003101d6006000600e05150380000c8a4a070380c400131084440c814100c01042e00e5400e6841010300c03c030340c5903841c003400504102007071745c042d000 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 220547347 1250 220546097 220546127
    0x11106160504120b011a04050a05010e13061e0504050f0a1e090302032701020606130e0604080904060f0608040b100801020705010b010809031204110406030206040b071b0e07 76
    0x100000100c04401c0c1215400103401009544211750402d01480c2050b20440003412000c2c6044c4424403140c5c0d1100c1d5954111142400d2a201205204011880f205000f11903040354601c0c0140006800292401042016880204031640301361144104400c0354400e446460f049500d4800046001006920001c00441b10701c0341104a0307a10f03000c014003607400a1a0450050b04041a10a00075550700e10445905504900682c0c07500c13038010000b0350750113006080901c0b4151244941040030619804081801c032100706846481c5010304126101d44d202c081e103140aa4684034001460f101040c03c160140c0d00e03595203c200645441d2682d0514840141ca80c9801152515001904140074401403005512420002c2404103000e00054082107008000b560316400070007280c1e4441c2284d070b503c2030b803295101d09116000e150319404640107091940000350030900c0000c01194903205800504141c9102d51240c0844d2002014001100c4003148201c00154004101142805000345092500901 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 220548597 1250 220547347 220547357
    0x100504020f03070303030207061404020105070201080403030e1212070305010807030f0201051201060309020427020420030c03250f0e041509020405120a020d02010f02030705070603061401110616 85
    0x2070340400207424200d5070b900880110340d00003001410440c26004000d440d80f800c4c50807002c0c0f4600b50300082e10314412800002c1c10400305000041c03c043c02580440001c0a40350100c41e01c4030311007880e0071016030014810000001d00c460000c1c0e4124440c0c0640c90580d442c00000e00401483d60307032450344500080e44224184a414090118802805140e042c002c1c40c050380d010400030704074014001210300d400c4421292159520151641003010480a0a055415180080c0303002d08801080f51300f61003003071401c2040700000180720024030080c0c0a940100030a03081840e40a6440c41040764a100046c0c03144042054600040c6071070380650384045800202400c041074035103c0740c0205a500806402101400c0e0707021400344a141880d5034120480540b81d0010400100350390002800c000c1505c0000f810800d0381269070800a2091050300c4040c0d80c07003800c8851150b21100058068101d0703000b17104c06242c0f160900340c41076100d0b9080b88007a00c042d102401c011303240c50741015140c01c1102c910000b401 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 220549847 1250 220548597 220548619
    0xa1503021909060e01080411010c1103030304030c12090302030d050a050904050103060c12060b040e0403020304150305070e06160303110c070b0405010f0903050705040f0e0604060b01090501020f10050402 89
    0x21540030080001150340d692031100007400c1080141031500d40c0144c090400c0550010000010f141c0c01150780781c01001d003000400f4000514040041a101d5090941c01d400003005200800d600102c011569074425503003c41440d4400c03900f111843c1c80da200280d81a4004448500128010f4008018510007450800d03e024400030204054071002ea02c1128510340c0c4052441645900210a0096500c1050244506403078419070390420300560050783c00c1b44078850045030406000f00201d071700620025810201c08112f0890140041c801160880080340c0d0500012021b45082811190699448801110146071544044005003003800701da0f8641281045180103240e010089907004000014a040c3d60740c0c241000100601c080c68409000d0103082071080c400140c011030004113580d0300f61000107064020000103c042c0c80a0040c040460060101340014400c090300501308041081e00c6504c2c01c241d585004aaa503800c004100155400c281c070902070021142e00030a400c280001e000443c41 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 220551097 1250 220549847 220549867
    0x315010509040903120c0f0206180a05150a06120b1527103305090d050c0117191508060c03071b1208070c0c091413020a150302 56
    0x150300c1c0c200150017198411044218400d03d5005103440c240107450204074616252501a40d5520068100076808103014203511003254101310f00842c09400c24100d84182d6082a40c0e4a8054800d07540c1080050416030045a054055a040d0380c2095000500144030b0391040041c040056003045110f9102540317208031003007040481400031a00350704c001012607a0801280c9519150507581c080c102070b68a1240c1d48182d040d801490840415404404100001c1c1c2ca034000c4840b03100d14200981c0c02240040d02000740719000489214034882030f03d68016076800e500010310f004038110b41d000f50740c00c8a040c0c1d102403250546c00c01040d81620a60218105071190ba5541c208502210030070f0481da804010031a035294000740f002c0c1101c00413008400711113010b489060500482603015028890080d000c107809612980381f481c3d500341c001b21100010f60301c8003a140040d000d00081007001c030503c10080380822030f8004650f4031441c1c0c0144040c2c84140b07482c0703136003041e10540401c29080c15801c1c080d42c1d182c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 220552347 1250 220551097 220551101
    0x8100503060130020d0228120204180b150303160303090219060203030121050f0303012303030435061602011a0609130f0501141005031501050904 64
    0xf030200600304602c1590b4607111004100302c01880c0c2d8810304504008880035807988420720b41410f40590300940100c41071010102c0c0c05104049500c84103003080c0001035884c03100480162194404ca07018015420310b240694505024103001400281c84400031032240002920031501416000d020390b41801c008040000034581d1103101079010940f0340d41d0040451030007000c0c0e010300305590b4203004086070800c40020340d00e0005008000200510040558046400200c49440079500c0002c444801c981c04411a840ea0002e229203a910650300700c50681501403103101045446020f001141420f00d044480004c521a4946000c00340c0380600215117000c0e441d04410b13091111403c0200603178200b00d041d642c1c81e0041d201c103030700441e4905031031020200751078104895560b20842da0592600023040016001945c500e82800c5010315041c41d0784401c2c1020380080781201c40300c0f410018407840034020300408040d44a0141c000130410000158860402c0c500300f1036040381890f0060406206c0d40100d03003 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 220553597 1250 220552347 220552349
    0x1d090f040209010806011202040f0b03190606051002100c1b05011a0103050c1e0409060f080708011103070c0f080a030905010f0b0109030209130822090203040201090501081005030601 80
    0x849454042209504001019a0040058400410b080d615000e0401e80c1c1441c0080c00901c6180c96280c0c281880c220f03600b2106803210000c042d26444d5110440f103035030001000004236001401c0c080000341c00e01c0c0840380c4890b00001c0b9000ba02c0340d800b00320b80100003010101804014400001300c8156041c3c90098080182c600c82c0d800020301e050540010041c0500c0142c0c024101420441004204181e41003a10b01c51b0074018842d2001088103810400103006a0700442d076418076064000070901000810801265200c0f02036409058a501c1c4107400e039482c00c80350740e0401c4801c102080f1542c1c41507901004850040b0401085a1001d41d500c2200d07501c044c083c100000c0d15983c003036051100c02c0c812000c003654429800c00803c3d60910010302640542e11003c1e03c10100040061002c00039455a00c0c0071541c031980080c1e507000d4224240d040c0b44007004200700010845600880c2e049102e10840c2c1c0950340507142c4000c214034100044488400090500309080c9001e0800149610100030302c038 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 220554847 1250 220553597 220553611
    0x131a030706050d1d1614040b06040e0703060305030310051c020607080f1905030a050708090d0518100c150603031d12070e060f031204050d03090f030f1a090c011d09 72
    0x4d010245088290900d180302d04404500c1a860100e03c88c8a9a43e520110380c101d4400340051441581c5101040d001810301d54409042d50200004000d10800300d1104503054031070441310756a1500500008840c1c032034845e1002500200104010400710b44408003805200703c0090b1a41d20703140d00d400010240040c0e08007074001090700030051085c8078005014596024525150003080d03031a1000d8015541c4001c14091824000300141d500804820700c0d80c060745011001e0445c2c00b150b0301100000701080c8a80f80103980011642500004852240c0a20b00c103e982540e02e410000354200102c0b8829420100b030958445500d0822801d00e0070705118002c000d20000d03100300c40506d8114107100391031501c3d20480348a6040481e007003505171505010f075002e0b200c041d5251701083e90039141c02e60f040003060b000390314042040040081040f0545600e03140b0a40f00f64598030501c10803e6015803843d2064424005030707089075200c0c1c10f2551281c2c9006803c0e0702410450303e41582d00c0c0b40842c0d038449098a0786 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 220556097 1250 220554847 220554883
    0x304210306030341090a0b070302070b070b16170a0501080f03070c0b09040b0a03200d0b1503101104090c0c080d09020a05131a030706050d1d 62
    0x10418107401260780c640da80c64003d46050501000100d440d4403070310b139000d0748192203038035010076105184030002e5403d910000751400c1403c54031584410915000402c0440041c45078900106411170900d0035500440c1c0d101d68080d9154860081400a0501300079030181001005000a400c0205c2d449603e40a0a040000003440d5414041c0450900030002c00c004000d500400102e400200c2d21803841085501400343e843e190440715000030040c09170080d00c568040c005040100c01d00c284030621040800c2c3d000b600c81921403015040c00a090501200030b040a5143c0b00010f00040b40300e560f40380220002016580c90b2554040c000c8200c1d603400c08868401400420300707104c01c803218070640303110b03142c2d50414445804582c0e507440090303c01c0710854640346440e01c0310202191600c2c1d86a0003c0c0074010546e8401c40250b00040c0006d180060440800383c2c6044001c000a00f808500c00060b12a19514180752041d41321709070707015102640121741218a0032503560003a9105101c207210450ba86101 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 220557347 1250 220556097 220556099
    0x19150f091a04020f01020309030d1d03071508070c0210120902040c02151f06120605041109011d090a091104050103081b03160f060902090f01080f060402090c0304210306 74
    0x51100113004a1032031819580100000c14190303a0001307080800d1151407030206c00200ba00e5004010302112800b695030144140d25020914640c051111001c5001c81d071764481c03442e622210100c418401800010750010800d0952880c03452044406030741c04460400c020480802036400b190403202c18a1040b00144c0014400722410a42e6034a4142c1140c2c80d0a4036258204126203000c080000b41d21032401031103030340a0810051005c1c1c0e00b040e00202401002040f1400001c04510580d510101c1240c0c00a40301c0f00200c0046071100014001c246400b908001c0c40ba075580404400820b60303010103450024440100c400d0a40d500e000d054080c5104600803a150440208480042d020b0016445901e400c20700540300d80e0150701450b032000300d400416404960115041c058000c1440c120080d42244c00310040142d855241e0340b00c64100c0e1005021242c01c9180114890b4650009840080d4007440240204480c101e0700c0307000d9034010380160100e03405045d02801500c0070140d903881c1c02c004a91a448 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 220558597 1250 220557347 220557349
    0x50102120903041809020603061c050a0503030105090106030e060c09040e0313030203010b010c120f05040b0c010c0207090605060f07170304060509190f020907050d0606020c0319150f091a0402 84
    0x10303413001e070341c214240c090141c00016800107409010040809008603807265408165095840c500134040c0e4111059410040781403c1003a1a58401d01840d0300984003c400010300e0317440382c1301e90080040c0f10b0340034190b280c0312000c806d019030340110100d5901c030362503066100b46401c06000421140400c100c0b040b40c150310394414507003554510a889810305c0f115240c4140840c2c44003100800718903003494100c9555206110a0b1250b024640011281d0503000c100d106075000b05500c442c1c2c0307800d4907400715001180c2d612040c0303081c0d40150041d69041074041c070900444915000180c002e83c3d10404220f010f800080c000d40c07860760000c0303409450b0baa0f1101300340b10b540c100500600045c1d0302050704c14524800541c407420005200540000d010780a21800200c40d54841c80c240e034803032180d202c0103100e41e59480c0c40096803101e802214905c64000c81c4644004100d40041c0744646a034040c1c40c0690001c2000070b00802000480d004818903522090000e0016070008404031031211280100307250760800340 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 220559847 1250 220558597 220558619
    0x10504111504121e06050907050405070e040203063c090106092705090d02071d180c06040b0418060b030606090f0d0507030b07050f1605010212090304 66
    0x111196000340d00c05501e00c05804200d004642c16101c0c0344020307540000e0310340303049000c00d0719003000075a0443c194800c00081044940019000d43c001d0f104443c800c41d2250100b10403201e00392200c0c008a02c4e10b81d801040c90605401865010900070704400c42001c8855400d4020202040c6071880407900c6443c03807400084100854421020a540b08031540d810814042c2445a0b14003440041d10111481c1d0746510b00301081c640c01424980d4020b0140e42807070340401d544c0e003941c2d02064002d805401404126410351021072494210031400c0318a80d912a500e000c0355002c00c0e5407540249004140c2108541e440d41d800030801026907200c4030303a40d036141148101d408a41c0313031603122206003010b0040280c1a2028240d0303400a00c2181c46594030a00540018140d80f800f08005400806044901d81403100211350304e800c03030b4040e24002510381e079955000c90b90342c480c00001071440b280603c2000400320980910403a00389c480c6000600d0140321404060303615108a600c050250300005040c00401204 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 220561097 1250 220559847 220559873
    0xa0e070803090108062b0302030406020f010b151b07080309040e0c0d02040f090b0f040b0603060705070f230c040e0102040308030109090203070e0702070608180d081005060c010504 79
    0xc1c50402c0761040000707040090150860b840340059842881824540020522100e51914484500c100d21703443e0181d12504548540720143c010607440801e401018040e0156a00d0001c1c10440c010240f101340980070303000140034100800c40c600d0b003a15810020884600a130502d5001151102200c034200804d0740c942c0d011540058111019404094036000040b090f000c0e4120b0780865096158103106000b040a40c1c005000c000211003400200641001124003a60241070030721002c2d40c42070f0500d0350704c8000359040c030f0020718100100c1021800803020782c88203d1280d010b940d46028402141c07201504103640e181403580001c40e8640f00c52405110324806681c030a802903040c2482c603112100702d400144910f18185890f400c00c1401c540c5e003070107210003a02203014080c0403403c1c1084025907502d61402400049141356002c103128060000000c5030002c040310003800f411032200d90031281d520024002429103441c100303001c41d40d60340d1000900034140300180005018a8103041c0382060200ca = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 220562347 1250 220561097 220561109
    0x1406060f0a030b1504020d060303030906051003050d0806060706061401230405010c060609060e0405070504050f072304080d031104060207030308151e10020d05041208070203060a0e07 80
    0x40340040000841c0804416400f43d01030303a0003802113010b000454042d02c106074103800c2d01380c90300c0303400b01c209a01503218208450203080c0070040b070340d81d01c0c0100507040c409000161259121600c1d0150903403240c140c840d07104101810030307814100d0554648003900c64a4001403014440c0e5400d090301035030700290403885200a408180c00741c5c50b461855152a03c590b004590410201e140da01c82403180035009400102262401002a07594603041140840002d41d4100e405000e51680004e00385090301900340a00811700c40c550300ca4540403c00c3d1281c0c0d61800d020b181102c2c00f00c003101540720181d009400200280382c090300c10410840c0c00102151035103217801c0c0305d6240501c400d1000690000d02c000075a9411b00301384005c0c0c0c403810741d032048100c2140312407540a4148503c20340412038962850b401f1540540348800d194000340b40c140e03250b1100465060008100b803104004040d070090302c02e1441805981c0c6c0600d41200390b008a4148242214041101e503141c0d14140e0300d0302c1d400c001c034130b0003092 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 220563597 1250 220562347 220562359
    0xc180307060e090a061514040305100b01110c09060105070f05070b0a020d02190303090305041a090406050303030f15010c0b130302120301030309030b18010911090705070809060f071406060f 83
    0xf003014000701284a15501b84010000395085041501c3d03201400c03034001e1904003044503855500a400d00c4094a8110042c40c00114030220f0760100400014404c00708850041190781542e0755034004540c65006a001541d41540d0b003244580401c40070b221130000343c10f60340c400c0e80d991404820040c1c6002c003068101800c560214003e12800b40c158206d006801d036140c5000f141d0160f0343e05040310540190313006080c41c2d50000500200d03120154005200d008021348040c1708056941d01050f4490100b00c84800050750301e18002080200300c1312520022810504121501a160f51580e8002a4085071500e1034202d5104812090540401c827480ea4441100c01d040e18542c1107907002400352201c2c0c0b00081c18803c2c40d0021404009000d519903100e900310200801070700c6640d007000580807119802e003e00810841010511240c030610455450130f0b0050ba502e880c0092001c1403000300c4d440b5451098800304103004500000e00c01002d10f9400c4c2c030040000306894200001000301e5220f402c02903500c214 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 220564847 1250 220563597 220563599
    0x70e0d06021602090c21100807060f090f05061b1002040311041401061e260703050f01050a03020609061b030403050d020109021809120c010c03050603150c180307060e090a06 76
    0x620404090038002103c117100c00f1840d210000f4100341403c031900326230458064500007140041d401144848035200c0303581c403160015036407881c0d40c1403000507006594000300c04110440100c0c0b4024001182c070000c0b2400c070b80c8401200303070350502203811540046404140d0b0b801e1b0807615240c90700450380000403a0b0741d00f09455243c84005800034076141c41040542d5030805d1044904d5010f440b6101ea881400d00f43c036044d40c46040c2201002c41c1e421109940402d18000101d13041e071540d25403c034141c40000d44800002403e5408010a54110b01c2c02c1f981d018408200003503000ea80c5402100c003909240008586031070952511034142402d17140c504045a03d8001c2c5107015075290b10100c07400f009121070701d8802d511031005541c1450940d803142242d10200040d94201c40360150b111002c10000c80d134007000161651400c044d1580401141c03110880d503d4000302c0d00c0400c401004140440c1c06005034581e103e20100400d003088003a0b4400701c042401c2010130640360030f1480359503500200c1c84000700501 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 220566097 1250 220564847 220564867
    0x6080f03030112081204031119051e03040902040b090a0b0a080103080318010504032a0804271e050601030b180703090506090606100f08070e0d06021602090c 69
    0xa40014400c901c1040500e40b594820301001c030080b510951124805c05009140070304001d4910944a000d0124500c101c001c60180c2a14024001a865a012000d0080b20086ca02541c45045009042c0800340c00104400034042e14039200410041034907280d51a15480070030304001c600140b90b84010280307a810030044c1400382e03200e141e49043d0303680150701580307030f03180d181024943c5200b2130b89030700b103643c40c01e002e01c001c0c150008241070380080f4840900301c612001400d98201d1042040c4000c2c54a00c05010a00c018540030108017244c182c424010000c84400c1e22441c0c1c10b60310016460014034490348076908940d0014041d60364441c00a08017440032a41c040c0100e42100700301c542da02c07440424a400f040500d4481d8200c0c01d50113030040201d40c02c81c10100d5055860794416100244076486d03117504421410f0103820920099001c80d203034840c00d40d403028400ea030000741c0020940c0c0d00180c000d6010002412030700c060481c014542101d4001c4455610500c2200c940280076940714820602c848816 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 220567347 1250 220566097 220566103
    0x32101031b0e0423100603050f0c0105030f1803040e1608060d030806032d150c04030b0702071d070e012a170f0d0b0a1208090a03080d0c0306080f 64
    0x22952000130010710010b028031060008490b0641c103100d50061445901c4415119001a4282c03800340c01510004040c0c09115076071600c400c80d915011a10500c0010260455601d10765030202c1c20320b001e2150503006a8030751381164860740000700c9889450050186480c040d098520070300400b07040c0b03400c981c1804800100c501c4803480c80142000040b60000352070781c40c18042c0840020034403000f4644100090050171440c10140003c240b648503800341390400580c0d45002e14082c0c4c04150b83d96181c141541c480c900794140040005056100b191400690f03034030004180ca0000548a1000c4442c0c00c01c0b0400408000d0344400c41e50400c600e010744031484100240e054201d981c0c20007242a00a401440c11440c4039416841005011300041020703d41c1d403a035000240b04890540208102800040c41001603045040c0643d458008441c00a107001039204801809501d00c010320240d80959a035980c83c0190707001d041407258080d2504101041d894050080c034001c0c0c03058101500e070040900074802d503 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 220568597 1250 220567347 220567351
    0x50a030e1216030e04020d0c030e0309010503010b07110907030b272e0e09100905120c0a0c2405030103081603120203072a111002032101031b0e 63
    0x10308140e0300241e0b60030180200c00040704444064015511a440303003030b0080c000c201110314400400c0c1060b9050038a558080216101d40c80c058640740d00b0340e401c0407100701030394000080440d207441d00a100c52943c1d58400c041782d8030a40c1c5c1c1d65804904034082a00f8000c9070386001201e11485a1070182c0020b40c00e1190b007945600480b40901c4e000081140d880031916008801c840c074000549640012450307a000301042c62003010580101e501d440c440030405801c0b50601e09016060790007003030001c0020919800240004000d5400f1608142019103c11405120035442020284c13800d4030241c83d004030000200001c050700e810118255071443d00c070001c03141706070742c400d204240c8031442c610304040c0210b400880110b5841c5003151203140042c00544a01d00c40c2c0640b011402d512024030400c86400c0072441440f41d0b10903078031004d000d5140180034440024500c02c100790301051100f8a1795064070146020b0b10580402422140d51550400d00700341c446007403d5003007120000d5800c1c0924a1500c203015 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 220569847 1250 220568597 220568617
    0x1110721140a200708060c0c030d051e0f0105120d0c0f0f1b080c120d0305070908010c0201020304020f0f0a06050f040b04060206040213050105221407050a030e12 71
    0xa03507a070150708000c40c0e1000f0300040e00c00d0700f20f40381c0d4100c3c030380d074400000ca20040d51058401c948403030b10f0301c0c01a030605003d08103d1240702d50007000800300034401c542000da0401480e1b50351071a0b2940c4181241d0000c0022a0f0f0300f104140c400004101501d03010350b00c031031007030140c2019146038000000020020351454001501590f04a07210000b0451104524850700f90400122600640300d80c000035031030740b00e40c441d0300c1147c4240e581400b0076103011070b61030041030448001082000300c5c40341c0607009001e005021409100c504000000d00300001c0c080c544824110740e0005030707a4500707881006424040c80400c580a00c05440c1c0000042e16001c41c002e09841550030a40c1e00c0b912003220905142c4a250130400804501003400162940c00068940c004c0d0b00c2268060001d005101c0701004581003407148640c0421051400b03001c041404520a203d15100d4002081400c880b200c0000e0f152005d40355000054030000301280c1640e4540b10301180c442e07004000d80105190140c8950701ca010fa00900 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 220571097 1250 220569847 220569887
    0x1712030606160c030615060f0212070308250507200a0303050c0102070c03141e0c04020c1c051c0504020a0b0901030f0614040e031204030c1401110721 66
    0x2a10901a0f510900d6008681c0102c040c810900903200300f801400c0c26108030700104081d07c030160341450021580c1413012014204143c1000401d480c11601080040c0c00d0000d10207080380c280544001c1901c600494843c540c456917500c58541c50b01c03d400400c031540d80b20820b54014080f00b41607440702400022a5010b1815035103800d1089441030080c41800001400140305640000400071620398103054055040c0070340d05e104030640380302c0b80da2400450b403e0400e50001200c0400300e1500e58041e0603c00701d000121020340a081c058090280d880702c0103803010a43c0442d12000101286042030700d00c4000030b0003032003181001d50118000f22194000c500d44401c0200d07000f10164400d9200e034002c410240300c00e1041c0c0f641c64015034000301d0b540d0310031401142041c0040c0300f03009002080350004100001607011700c0d552910700300d0f00c02d0010081140e2440b1803013480f0410007402d0240c900d1640e61080c04036a1b60070240342642142070144d246030b041c41c0e00603440389881504000140d0541e08502c400c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 220572347 1250 220571097 220571137
    0xf100f1802030417030412090618150e04050a020c0c01171303030207020d03030f0b01020102070506060603040f05060c0d0c090302030a02010e3d0c05030a03020a0e09011712030606 79
    0x101e41124000d83c0c210050b40132000c4100001d2001c007501100600803540c035000e9129448003800c43d500b0b010041d00401d03100501c0c00412941d42e202402079000e800510340b210900010000040c05e4440c10780b0b20f01102900400d0f6025545800c1c000c160b40040242400e55618019190b01c41d07044a0080032802410103034414042170502030f4041b82c450960040c940001d03801d00d450042c0c020200c03400c228001c0c40c0341c240a050f20303500501c200d55103503170400002c158903911542001040da0008108070b071820603070318540000803800c01600380034081c2e07030045d2038030350901c280c02074100c03520318400724200441100c040015072000b103206000340b034080c82c000007107220407000b042c0700a11000c2d00b10104000308444511100080c02ca0340003482000b06100303e031042d42c080894005400b4100504039400400c05c0803000c0c2d000341d005084405150400b190f04094144c001150350809912018039244e441c00a001801e00c284995003411014040c01421400c1000120b81d0754001c042c02013021000d10720b0 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 220573597 1250 220572347 220572353
    0x6021f0c03090c0303030e3f0706060e011404060b12093f03010f05060d0f090b040b0a06230301180f02030709050103020904061a090f100f18020304 65
    0x502003940c000f403403e804540e4034503004008000705407016801c0d000d542450003078552500b036400d1000005080340c0c0001e004c4202911040036020801404041c010880d207000a6101e008140081c812800c2c0d086641d85840c0030004010505018241b2840c540700080c0408448082542e0000d0355009007c0c0180d61054442480c2c1440c0c030240521544441400810a80c0b0345014440c103415103004852030055034030038042c4c65020a00a100c42c0482c0708006200a040400203002c5a00080714080b4111300341a124074121160040103503003007081d40040006100000942540001401c04108011780c688540b0347c3c500c41440c1200d510103d9190458041503809410444c280e02c1c8004480c00d04540a1800040744c2d540f1300c000728000c2c0149031001401d0607651240c241281d8010309038603460341e2240d0b500002440a076030940308104001c0300481060710340d402014030400003100e440700142001b51304041c0500813603010360103008100109104141401011868071501d041015880762110f00d = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 220574847 1250 220573597 220573601
    0x606040323010e1b1c030807050d050c090f1e0f0301090510060609080d14090616060903030e0a020a12030905030d0903031229130905030702030706021f0c03 69
    0x24140ea0301d25800c1c6150341000c00000714410145034684419000300c01c514005100045611a0014814000301150800400d0141261030b078070000381c0c035080746400424a2140120b41066a940ea480c0f200480c4040503814812002082114119a505d003e84d14140e0184413040c02d08040c08d008910054840b00e254500350084240a13902106440c05c0d500c1c48102100184810700c28240010b610110001c0c40f01c40114408102e040156110803404595240b445d0b25540418101904164208854940681000c110484d02e92050780081528841400c008060303448032005500c1c5c035000700781414010b80d15201d1354811200c60340e01e2190403001604007526404003540c8a82d405020312641869040e0b8400306400039a803103500c030090000b07002d03400c2c0000c031100302c104003441c03d115240c80313803642044568814050724000c0600b40a01405038000702910428030044486074804100d6408514040c014140030b0180d03840205243c1403010110202d00e0b02c1c00e5903184206a8524814808034465 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 220576097 1250 220574847 220574903
    0x1b010206012124061e0501080708070507020d02090705130902180904020d0212031b070605180d1b05120604120c03030605180901051315020d022712030306060403 71
    0x10b042c042001d10741c0c8000305800038005c0999a0310100710b64902050541c06014200d0007400c281e9030301e02ca1943c0d000c1e000e8902e6485003806aa00c900300d103d8040050b69651380c0c26100740007c0c2d41d102d440f0003c030340070766514140740d070030085485005100c1c001c0844a1500c90100385a402c4030401415159400400c01400c00f202d030280d000307200d640a860a0400000c020010501c004006041c01070001c0c021a4491645000e09400184104140090a115890845200000141206036044d51603481d41e521209e69060407031842e1280800b01300500c0c141403e1078045641c100070b4100e07850709030395808100f2501103500082c4044c5846c4801414402d61200c0041c020192040052074243e0b0002c170103000003100c94542e80d60912001809003582d2240280c52241d1001e4020701945182c2d8000c1c0180d0051090000400c0c1e09001803281d0080740794260f0b1003442d08104d00700040300e5040038895659607862010107240c1c820001d106060b12140100d0741125040600343c0801c1d55030000181c000400c07 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 220577347 1250 220576097 220576163
    0x30304080c01141215010216090e1015051203040f0308090a1211011103120411041b090504050c09060a0207140f0306010b0a020106081b0102060121 65
    0x10114010030002000141085404801d07200c07842c90b4881c80c0603000207071041541800400140002184240c0416144a030741c0e2501401030b01c00303016003030000c03140c44050303036000d0340710f00303454030f825910740c81e000d002c4915040000d480501140d40f5900311620441c825100c1e603030103040c00300021b42009509005680281603410318061005550741031907112034100d00303081845241400f800241d180c1d00c0b10f904110349544442c0e1001580700c024010359114450340300126141c041088802d00c0310100015291040d031082d01c00382c400943c1d05052004075080720900300006200c0e00040181c2507005003107002140e10440f00450340da0f4070a000c45440d802207183e0345400200101c0d03010360454000c9002010f0756812003510b4104503110b81001460001c90504a41640244005000b104006401402c0384007031800049502580c400c03400780f80c140c109600201c00c801d6100d04100940c0d041c01a9401040d1001000c94050042d00b12680382c021200d60041c0341e500200b100c0d41d080e440a040441c80c07000 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 220578597 1250 220577347 220577353
    0x31b01020f0309150f0f0a0b040b19090501060503190b0d15021908061e120304080a0b090303012706050603130203060a020a090317090a03080406020609010b010210110903 75
    0x91a44803d5552211400501103402e8000700184680c5030040b042482041d41c007054101136100c0307822101c002c20070010041d8005480703901c46d000c0f544035010301031000c5400c803008070340b9146070410701c500321201078210b0f108110040051000800c881561100d0070101c90b41d00082c0c00c3c5032000010030643c50040d00a24907400958050480c0c0066400b03040d00900000744420300c0004403800b1920490b0071650107520000410709000400781c9400e090003110b401811001c0804600c08400303207140c010303030300c05030241d800610784c541040001b0b581117401c400024015404d43d4105078260180001030081030390450898041d0740000703601d82c1c100000901c4041c08035562030501451141c480c184010007030b07001c2c1c071400e00480c0b070201c0584203c0f0041801655900700c15030442e981e1890780440c021644800080c00e00c040103480e40c0c1c2000d684001c6124280ea41d946070301d42003019051043c01002c084144e450300c1050748103039802080c640442c032421700c80000c5003210040745107581c0c0102c0100a030144 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 220579847 1250 220578597 220578601
    0xa03020d0507050307110a0c14060702090903091003060f032a090b100e0d230607021506060306030a06021b01023c04091e020a0804020a060f02031b01020f03 69
    0x40e00080258005d0703005a94450314038001c55111907031550300380d1004009040e030400c01c0001c1c2000786001c03000c2c00b80003040d02d0314185440c2c0001c0c05503c401d85640361960000107040201d440c101205040c2503156040a0103494640a00d80030039518520010b41040040303ca01032910207140000703081800e00034017003102d06440712165401046c0751101280600c4075059002903240c001c45200303552050050080194100580d0743da00d580260011400c3c16540103213400484000038041a8890b10f019030092101500c54105607a1008024252900a0b0b8081051105036100491000c0c2c550380c00140259070b4881340d6404060082c0940c2d00d40d0074551000c210030083c1410140317031525252400d140d20103240241103490960311241c9910700000c403802c000400203180300350011813521202c00403000c2c140e81c048041c81c00340c2c1d00c480b50705000140e000c0308120440c9499001140640340c6894020724402428101940da0301c503070340a14440b20f44413405145400001d40480b1201c03400885869107078 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 220581097 1250 220579847 220579861
    0x2030c160b09060a0605130b060903060106051207050910032007030302130902040b0a0e1903050114070f1704050a120f02101406040203370b1002060c0a03020d05 71
    0x110141c0e03490b44540200c1c1c002c0340040041d1300409050741e000410035000c10410071447c10042040c072240941003501803207038020319502440514000c2082d6200e03903941c0c9500352804104c07084020071110030b01c002401051950788448d00f6034120840a8140050842c41c00d415084025a01d00707441e80b4100c000147c000c00f0103605030003424440189610020505480d4111507040e801140603d010031a01848032101c0b040c07040c5481340143e44060400642042011001b42541d4110380080d54581c5d1104415003484401c2161264041c250703240c0032051500150008007203441c010320340c1d210581c801d40840c040c010240040540e999211a040c4102d1102c1d40340030b0042da585200e07500c094060030441c5044000d03940aa018203034042d880c2603855640b4402080300a42000e403500c9002320040c540c0c48100300724000c111a420b01e0000f0714070040d007000e401240603549180840c42c082e46e01c441002c8001500000d5054000c078020500949840400200f140280136030055550f246007004180f1001e = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 220582347 1250 220581097 220581113
    0xf020303041d0a14060d0c0801022110030206030a0207030210020a09031e0503190e040c1817060105010f110601140a1706070807020c090103110418030206070302030c16 74
    0x142c020003070000c1109030f540d03280c810122000c0015400502031400d00007041450644400340d10b00e4400c20760341118a07200c01d266400c9801100918082000d94202d0008400d02c072000c07254800190420740021500356808510140805803c070b903d61900420110704040c001d004e40b1514040c1214110b440d2150141d004285105920094400d60104000200da200380c500c0202841c54009008503c0c0502d400060000a80c001d08c0300c004004440c95004015038450007640c2c0c40e078010369910300c1c0507420001030805181c4680d000d05000c4240d6407420070401004105241154001d01708400003128104055070540940d1001082e640582c2c0000705078401031070001c2500a1042d200428095260504000c0d01c110160504103983c1c422000600010301c038000340341d400314140c81a80d0000c2018408500c20b480e00b0f800803500581d8508128410381014418104c000880117140198100103460294079503002500031000c0540000010b90101080c00c111940380f4401d0b990140d0000440c202501 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 220583597 1250 220582347 220582379
    0xd0b06120a060b07050307110406120507030312060612020906070c030606030b16080a0b1302040303110f0706050f030a090b040809040c0f090b07060e0303090a060b0103060614070f02030304 83
    0x18041c41d2007000700d40380c690310f02550710300c55000700154030301075154842d0013004036104459503015850700380100e207008507101d6001200e4802c0c2c006203400303401d51801404802c650b842010207940381440170000254010b4800d0ba41d5464500c00507076030230226021850f41d110303103d0007a18030b0703e400d0000000c0186503440750003101d0143c0074a00c00c540341c460025400c2540244c10000203181d0034040354450105a001801645000349000c01c480c03200704e42d80003130740c00607031040e800310300122181414040e061003081a0047c03d00c003e401c2c0141494005003050045409682860b04040001005010f00c1c3d4440c40601e030300107401d40040d00d418030b000c141075400004102e0046090a030a12034030f41c0109110a444907058580c036034002c1c203010f20300003640c00c41c060a640c416240d0104c2c4d518040240011402a06114043d00c00d092881c03c103841587c2e0352049841c10180f03001401c000b015400381202941003c0c0000b1203581e000c03107081c1103002d0804e03000b001c1d6060200290000d200039070584000c2c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 220584847 1250 220583597 220583611
    0xc1e030302070519090b040b090a09030e030d051b0f0307060506041401211707110901330225090605040e0c0907120e06010504050f15060d0b0612 64
    0x8182d6a210340074408150f504403103c100d01d40e0315480900c501a0290000c00702241c0140c000510021405c2c0000c1c0700000560b40001d0f0982d8a404031401d043d841001c1c000808800c0d001840000ea0090740140548a01c254149203141000c2c040b40d00c602c41070144c5030304020a601100c2c0c941107103061480007403034285d81c000d2142d4070f403560154101d43d00303a003094100e50500d40740c58a44e21190800c079080c055001011500c101d407054041c200211410080c0c00c0c6140038a0b0f000010490a000744400b10074103800c103c140080000595078843e80c907982d040e000302c0c514040c409480c588100c003030b440c10022042c40c0d2000113011420022a030400702650b0100d411581083c4030895540e010310044a00200700c1502d150440c0240c080c25040c00c00e02c0b1900718950345443d4a0301d5465210382004c0342c007016141145034200400400c82881d20b4001c0540042200948948a040a03128100d84e02c5d242030556010319004601c2401074042036000c00d018100203010a507440d00e0000c120754000320100c900c1 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 220586097 1250 220584847 220584853
    0x717030420040b1305100f0e0709081b0d080903010509010f061202010504050d11060d0501180608150a1d0604020a0b040503120d06120602070201020606041104120c1e030302 76
    0x700540c5800d0046030849030380038021080c0602d60132404c10103440010a18040c0f0740b0620300000340d1540b000303889030082403000c80c0580702e0300300454014101c0141d030f40000481d0f0311500b00c803c03000343e030004490721401084441c040c0d00000c43c60f00d071100d0301811030842c0e07255181c541009494401034204c14007501014004200317258880a01648007145404080d000420a00045c0001c0c1808c0c600075030460f0240e6140450070000c45c1c001001a401258041c0c0c10036125801000103001e2800e000341d80c1004a94103000003810700000c01d507201c0d9061451100c418840020a11000c0300d41c0c010141d1507803651882441d04040b03c1c213a03a807204d058a080b8090951144002480d01c0038000341c030706940c0020050308030311440e03403966130b880d421242d0961015696980c00080d0b160075120720010441c031a500c0503072248003a0002a05180d001400e03207010754204042480d588a00b00d08803400c2e0340803501c5001c4c51140c94184141075414640204065841120500d01340c405025060811039221f9422 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 220587347 1250 220586097 220586153
    0x70e1e1002060106020706030506040f060807030c1a0a03050717011502070905010f1203030b030a030305040204140106050a050f04081605090702010b0d020d02010c02040f0218030102030603060c07170304 89
    0x1242d5a0300244102c0005070000c480030f0010398031940180360840f030020008103800500030600000c8510640c03000c8400e83c02100d0400c100208002005c000301400950152400c0030340c00500803a00c200c3d5440b00030550344130005804280582d400c64520a6007048007606036031100d105441001200405402502c43d480c0e0000d900f81d424010709e0b059038201d42840806e6440c0500603c0048084901102032540312292a40d081c0c804002405c4045d00983d004200350034140140030803207044003a00518000f9210040c02039541210481e8030800b02032411680e030340c070036004045490040340c015880c039026484881050801109a40701a50b2045034551100d840725203040e800c0341c100b0043c00d90050b0054905001619003032a142556500604007031204c03001ca980040d0444546c0c190700345006070302045002c000610320382080c12909040c2c0c006c51071810709000107a600c5400801c140d00030800007420504100d1045408080181140756140d01d030700f003600e0110b100d41d1060700c040141c0e0840c000 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 220588597 1250 220587347 220587379
    0x2010b031204090c050705030a03050601030b0d030906050a0306030f0b0106080903040320221d21030c2104060f09080a0c110607060b0306010b040f090203070e1e 71
    0x5181802000710403a000d281518046100c000740c0324104030101401030500c00d0348007051003031000340001e01c010350f070004d043d14201001404484200f221140205221405200060303003042816050360f42c0c40c2401600e658030088210060001070f0001809070042c0a00c1d102004403a000c1070b410780741c181d00c4244a41d619014070701d81d2170049100107482c154100d01049884000241100b81102002e46046142c0700c01c0b2000e80012800c1c840301d6407000317079606081c02050882c14035002c1007a000002810504c0c0314448003241107110246046840c10300080030454074107002c4201d0304d84100108030a0b01092a00e004245c0c85002220151005030400703608131204c500d140305112405502c641c04504000c02d44e40103d070365034081c1104641d034921408500380c0070750318400a401841d00c910404034103001c4110615081c800c060b8406000c1c0c1409200034020040c105c4046029200c14150051301d81d91207200c1210a6030300041f045812080d050740403070520980c54011001014161854101001d80b00d07 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 220589847 1250 220588597 220588603
    0x60f02030f04060b0418050609250513020903010c050301030b090604020108130f06060b1314032e050f0916030209130201020705180403120501120209060402130b090102010b03 77
    0x8661601680300407000074001a2594002c1641440191001a001a80550f180720210901c003080e00c0c554881420820031400800044403ca6109110a80200304188220203040384074000c60748605000b40400742104916810b0f42c0d0780c240010000d002c0b0045100014000f64400c1c0825a07180f81c036000040d1403008005001809941c0c103a4640b41e035a902c0c90307420308081c0080c0034120740310f009008a03840852218007401001d06100000547d942d484102c494141b8075240c0c0c4284400360010105074444d660100e940003869854140c0d02001541429445107881012040f83c0c000d607181005100b045030700e41c20000d03c2410302000b240c44007252205101c1c41c0c4901840020b5001c0310071000a544480300c41041d070900c0d032041c011103004a072600f001a42082104214032060010031040100381988070800260510351070004100300d505110009100400c41034010f4041e52410001c510745855640c12114003400d0340c0840b06100d80c6401a1401e10b038811144a4015800c040842c540342c5404 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 220591097 1250 220589847 220589851
    0x1031e060f1a071511070b09010204090b0a0e0103030503042303040501300e1006120201020d08191e0c021f02130302040f0902030307030306051005211f060507060f0203 74
    0x200c601002404c044800883c05007120010b5443c0c1c420040c03241000040070340c815903000d130f00f03c0f20001d40c03283d0401e10300c0c0f0304031101000782c5403080141000030000800240c1d0101c4c1900d030541380c01682ea0f030b500c5c2040f01071040f40e03080d080e40070001400f0300e084000e0048003034020340d40300741c0e50342c00311150702c50b00e07a00c2082d04046641c40c5624032105c040c1d8240d440780e100034405010f41081da43c0c8038502805081c116402a4450b0700a016060700b400b0442d81c0c1403001c4060b148150400301c400b420b00c06051607068024808191405988100b0044145a600200c1e01c0c20400c6c4030080c0000103a42d01d00a448000c1859074040140d1400c094072420308943c000d5440b8503003c8150120f080c2e20b190208005400b00034818106180c0e50303141400583c80c188010f00030980a074602107112881c2105010003129131030030103c1041801d125040c070070642c442915805103d1035015044540300c081c254040184029428241ea0040250009042d9080405481c0d66030090404120480030401640103034441 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 220592347 1250 220591097 220591103
    0x1090504050103350a02010204030c050303030f04030c05072102121906021606061e060516030f020c100c060605030a030c14010f05010f0503010f110901031e060f1a07 73
    0x1070b43c542c00001d003220f904800d2091340d2501518150f010303000c0422070a038002408600182d400103402c3c818041c0c80c80b112401400103030025890b6240403030f460100480042d100030104203260026100f840070811240002e08078010301c2541252821a541301c9040c0000822801003003166042182c41d0400708001c6d003042c2e41d1004040d4021220f0f41d4800013580003000c2c00280841d501c40410100b0018451807019220071481c1d070041625001038210f80d02160f900c440700300132081000c0e044004450240880755541800d00062124a4820980c1000b00064240e6084203038041a01d603615071041e60142484e020354410080152507405141e242c0d14500d01c003070b010900786111000054450025445030b43d20640002680b25084810401a43c0080e440300301342c3c01c40326006101500e03007885041c12010b85a0810440c4071184c0070b0400440c041d5400c940d061641d203c942e8050324240218203104041c0c40402001980c4e200d803507840900549000d480001a00030540080a6003c2c0c01203a18440e0 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 220593597 1250 220592347 220592363
    0x903010c0309020a12030c0507060201020307020f0105060d0b0c1b010209130603021503090f01060303020d110d12020310030206120114030601080703060218191401090f030b0a1407030b01090504050103 88
    0x10902511708441201303000e00314200301020064402140080c480340014004540c00940d480c20300940c000c5c40c0ca001400c0006d480d07403500080c00342d2503441079500510740307510101400881e5540400c2d400140603030b200e01c821103417501000e0b145180040d030040840c0e0604803030401104161600c0c01c02100c5982c000250400041c8100c225140c041070081c6038491200700440702c0701d80c02078032480c1c00d442080d07208501603444140300350180c541000f6140c1e48103803940024071116031154001498030343c4540300d2040d89607000010881c441c0503107511102441c0c001d00300079034074200d01074403e0042009101d24000c8030324107040742020345030101c0d0341812141081c00403c4807500750b0710340c0d800940c0300c80103a0350405070308039040d400ea860f2000c19040c0001c80418201c4050302e460401880b00c0745500100f070401003040f000b0f00c108940d510901f0266600840144031913503d00701100c00810001310050006401c032020003198a9040d00660790f15102a680c0c1c00542c3e42e104180015070b4800e02004160345 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 220594847 1250 220593597 220593599
    0x30309080304180b0f03120403060c08090616050412080306030d0e060f03060f13140c1c020c030f16120c080307030c0c15020d050c1e0703140307050903010c0309020a 73
    0x28007a4009500d0313400003c00c050302c000d068400080c5003906642c828400c00d50040703800c000b404402e110341110b44540741040c105030310b40740c0400c648444004207050114000c0c0103002c40d1981c0b242080d240a000e01c1480c0d84c48492450030000b103942c1048601c9031180c81561078041501e48110148071803060f01800c84d50178070208031703000102c13a00b0007444982c0001c01ca0192074400e64400e1035840e40d2002c0c0d54800204101c203000748101110300102000c0c0b60300003c02289000b044802080340d03040d045280c0050b224103144c1a424214880c06203503020381c40b0045520110749541090b484d02c00d51084540815481c2d2090b800d49007084080d202501610040c0000b501c203d0003034021926108292030300203940c0d0310302d594185010180201182031140d000c2050104100c06100e85078122101500351802e00c00010308454860201c000c03900b14022001c68940201805a403e01010240c0d07004099100d1801d4040100540c0202c2c1c0c013144a5800d040e1036082c080c1c028401c1850340c0341c014246c40005 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 220596097 1250 220594847 220594889
    0x11b0804050c0301020f0a020105180c0d06020405040e03040807080607140c0c030a11030d020f12090a24030506190905060102030906030906040b091b040b0112090c030309080304 78
    0x10900800503500c6010321080209503640c280300805243c28240081515010b4a200090860360b008013211441c0701c10b015520050600041c2031090310404540c0148850034501d403220103402030f071f40401e40040c01c00d83d50324210580030003c2c00c00d41d1080811900b1080e035640c1d1340ca0340c0d144280c801c0340114030417000483c03651a201000300810b92100303003244c17140640d9001007403414520103810359803012015540c0a06150502070340806000c80d100400440d201d41c9040b68403540d0000203c024403c00180c0101681c807000304050003001d81041c814079003646e144407035000103643c0300c240e0002454500043c00304e15095442c540d201c84800c00203003609062209d0300700140b00142c200c40c10342c401401101e0160384e4203401140301d01c001d580a80a030b0706151900321103800c000303881c03c021074214100306451510382603400c100c1c0000c00c0310080381e08080c80c1d0050b07a2400440090a035800e00701040201802012040034007124402c0d50b9140e007995890803600d0b12030043e40244508403080d07205421403 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 220597347 1250 220596097 220596107
    0x60b07120f0503041115031519031a04030c0506040308160323060613030503090a0503120d1104030602040602030909010902090f091512070306050901020a090605160506180c03011b 79
    0x5e501c010f03042120352240070401c051715030403c44901d0b0149000c0604051035003801300c281e00c0860014095600218110307610801c1c000d40f5100480030070084c000010f1700b4144600c0c1e03030382001600103041c2d0b080c40c105418010281c010132a174002040c5a0000030b81d802134460b20031460310f11003a14030b102c2c40c2500070400403040580900a6540038030305209000158052244401c01140300e0782c01550381c0d07001e0009000d5982040d900403840b03a006410440301719040f0b1400c0f10729170301c09640001303030001c1075402c0c13942240034030340003c1d03c040d00c00318022811a400100900020344225075000080c0e0b80c8800c0001680304860034075400822a10b400c00752820001d25040d0046541298940c0240a071000b08888049081c51403c2d81e51202e90200180b19603481044d40182000c8002d5203440442040503103007203214030030b503010018002182d41c40d1101e001e00240d00c9503486801c3d0380d00ca04003d46102011500120740c403c403801041d00541092505125100030030760502d07441400c2c4c004665060320 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 220598597 1250 220597347 220597373
    0x20a020a110108040b16022b03060807030b0103080705030c100204060e0925120c08040b0a0b0904030c080712020106051c0b062101060308030403111f0b010909060b07120f050304 78
    0x13007940314901c11455103688c0f07042c2c41e40c1b042110101b518801ca00d40b10004069800340e0b8082c500ca50482d13141400810301601341141901d40211146546882c20700d01149984210100040740d4020255141c2d440006030700104115000c1c7d43d5003010308403030310041001c22001030355251304c4c908031096214100701c40411240c10548590604420340d002a6002030207440c040807601000500f02030810042040c0b01107490780001000d0010410700b241440030031071407000500302600340841c12000d0003c000d50740302294112980000040400c840d03146c00a4080c005602502e40300d00368070441240301d0501c49031075000064010b0b0340445203807150028064907406c0c081031443c0c216082c03034030000044000d00032000150300c00d12105a036840c080c280249007019000d491421070300b020505000d4503043d02c6900700c4001c440440051011a00c40058a1041c2c0d10361201202c2d5080c4000010f8820058000d444054080c076981e9000b0082c001048a02600f520144e4000c1002800401c0100c0c42d0f08607514 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 220599847 1250 220598597 220598641
    0x10602060610031a13020a020706020703030c201309050706020c0a05090c070f030914060c0604032a03020f300c10050a0207050c09070c020d05070504020a020a110108040b 75
    0x700c950380c19403005c03c0b40e44030f052480d8482c0f2500082d07011161b6504000c0701c0700400c118400ba000385421690001c1c034000b28480e01800c894012340d42c1d50b2003805039440c406ca940e0b40050070001c0380011180e80002500710500f040e100b5000d14140000c3d5940089070f02c2c44032550041c5546000350600c01045007040c009028505140424000303440014146500742c00624041c0d1100d0400c6031404c59150000c1071031458080c05001e003404141d107118000109240c0055040c1405400c0240c00c56848142e120b182d10580c0e10100900e40e03102c185170b00802d9101c45910400113441e0100d1040d010615900100c00c6c1c01c140b04640b02e4001d88159076032002422250101005542d101107500c4030a805641301503900c1007117a64001303006c50811001b004148020701051740c02246030b01e8001d00c0940b13003d201d030b1400781c003075003c1072442d80802c08203100f045c0252100807c21512040c01c000001e541e5910304604072001e2001102c041015070144d44c22038421036220101000980d20000c0b00910100d42042c41 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 220601097 1250 220599847 220599881
    0xf022e0906140906100b0d0f1e02090901090608060606070f0203011d060a090c2c07020303011a04081905010e06041401140f04021212030a060e01060206061003 70
    0x7001d50103019240d001c0c5600d50380050404810150402030041d0001c82101110002084018003003419204020500480007e034500b4a400320000b07002e14083e40c3c7d001850500003d0300f01d4000c0e07400b42c0300b0b4450076985c0010682c0ca40c80740307000321000390152002690084001907a140b90940c0200b420901c207413004075002a440e07001c01d081d991051040502030030107080d0522510420811958412494501400302a046494403c02d4000324002c403104a07020040d444d800c440d080900021035105405000107500c0c0400009407242c00038014100e920f0304085504c0d07a80c8600b02e0684044c2e50066000d0a100d0f200148803015854504400b25440e5407900d05092000006014072403291340200d03040b000c0c06414401090840c0c080c807984105111600c8117105044c882d82802c0d60f4001e0b030650720540324481203401c052034804440d1844608440020070460000302542050007244d84000850308a0703600e034001070780c172644110b4132a90000300321818000014802d8005002e0541030b00c0c60 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 220602347 1250 220601097 220601111
    0xa050d021c0602030106140304020906010f020c031606080c130e04030e120f0609070e04020f060c070602030711060702030a060902060d0207061e1e0f140a09030f022e 73
    0xc88540c032403600c0180d42d0b20750301000402c05550880ca1001801d035a00034414070b07500d040d07030006c1c4030080c2c041d1103141044000c0f101c2054143c001c00c540c0c100420014200e13044a00341d443d4503c3c0c0500c050143c40005000d00c008141a0004081036400140311420102c00303260800c501001c49450040081c0d04101502c1e270800c1071500d401c841100d43e0104a40903000b13050f40e84824524004014103854402d0344039400c01c2001c044a8048035401c9603045031580c010900305800507156010b41c0c010b010050041c4030300090340f0740c2c00100624a0600c40c410f070180a001d16801c1051602074080c000c0e4250704200320b0100005c825600503001144001c040e2410310904587c83c50413a00100c1007190010754503002d103c4050794000c2e02d501e4494000c0d5080c8000c1c1d002c01c060030301c6121031858050515842d44200042200181c01c210104a56411208030700e00d8812801c82c0a000e11034016004529403018001841d403012940310304418130701a070300301c406108910110541030208180b00582c2d5540b42 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 220603597 1250 220602347 220602379
    0x80412090314060609010b03090d031109090f01060f050a170712050a090b090703050a02120a0f23150c071718090a05040314030a0e15091203060a050d02 67
    0x1116045540884003d02852600c00c2c240050414183c200d081000d1082c82044070140002134104100b40c11481c010443c103107025070071001c6000c1c04840d0740e4880b09881c1045841d10011001504a4101e95035016100741011015143e40c464011030500069034030110302000454480c0700d0f07402140d20301e4400f20302c102980c001002c54800303485001c20030703132156408000d00c142c1e0700105400241040142140364a0f50b65120350704c1282e00303402030107030030045a41e000c840014002195556080301216594010341e1030311108104002910308004480c2641c10012164002000d15a0400000d00c01505407240c11a801891300400b5084403800c2400c41003402c003903140e1000d810b1022600416003085400c3e1000c220400c0070040200d000203140000700000302e0f50080105518174011074682da66038032418541d0001d007410b140084418800c00007007000191107014054890360744001500c040b4102c1c40c98a8607075100544005520010544003400766103025540790f0100c1d0700c014001866020400 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 220604847 1250 220603597 220603613
    0xb061906030501060e01030e0c090c13062c0901031e0602220602030f070f23060712110f03070302120903040503010b010e130c0504050d08031501020d0804120903 71
    0x180080300082d441d01c00400070240c0109810102a20034241800444070a64403a6660180030000b14810501840420b02410074002116030f5240107661050005490320320141424102c0403c6c698442d000941d6800413007000d500280485038000c140c0c078100c0c3d2940d11600c2014002c100041c00c0c1103121034074140007850074802428000d4080d41365003d00c00c0c4840343d03004078034907503440941950020800004516140000c88050680c0310030b16600040d80390038006140b58800008264094148003000896280010054468102aa03542c50800c0c50700341d00700700380d500e1030400020b410020301086080941001c05580d01000615006007010382074582c43c040c1745001d5900c4960307134000007000e20960a0a0040103184082800e060408181e80c0c8041482e00c0040b2074502440c81e07562041d00d500610800031100140f50083c00303502e880d1202d0038215581e61003618039810000348a0842c0520303500200b407035100125681c8510046a0f2580c840c2c00c140983e042c0c4e050104441c039240800051080 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 220606097 1250 220604847 220604849
    0x606011d10090503070e070203041502030d02030702210901020d030908121e0901050601050405130f02041412060108330a0f0b0d0809060c1908090a0b160b0619 70
    0x1594844800783d250406250038804d07143c00c03425880400008011809400000312011031702010003035110024030500c101c0c20b500401000c1c10704035000000707000f04641d00040120f000d05400f08500c00f00d059464148210348200d006090158016030328520310746001c4d600c1001c299010782d100d1441c0110401000c80000700440b800369518070085a1407100348a80e40c02560b0109920000704010f040c0300001030585c1c080d6108143c400c000941c040c01480c50707150004024032104610554440341c0b110856850081500385090190300c0c21541600390b0305000541d1030403104440b025049044080305414a100310301c0e400040b03040d64a058006800020a0b80c3c18802c0500303c00010300302100f81400000c0d94001883c20b8402c0e40745143c02e20100f61540c00b152000e03407044074115030310940d1303840c6a820a08108100840c19441c1c000010a00805200074110b13a03034101c61440882c1c0d200c041c0c034645801041203210300d140381080c0b042c0005040ca20455048030008100c00d8284150200030583c03103400f = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 220607347 1250 220606097 220606129
    0x30c0504080717060c0306090606070302150f071803080f2a010f0b0102010c0807030c020106260c09040812040f080309100506030c01050f0d060816140603090606011d 73
    0x400346000f81d5010070322846820681d00c024851650411800040800310003514151040342c0018500c420075000308010001c0240203c4406401c0c40c0900e00d2025090084a03007202103999014018000080802d0003c142e942c0884007a081071404103198030540c020700c016030ba00015201040c500034103403881039940080d41000202d40c6010208900094661000c00c8a041d0ba0400fd03041c0300c0310380c209030855400302207490000b90080ca0705100700e0141c28030754050180c1c00190944002003000b06039291a80e213082c841140c20380c1c1d407840c0500200d2030044a000d41451014003404502407001c10803940c0003401002c200003903c4080d150641150b00540328544598809940c00c1e402907083d02909900082c200c015286100d400c01c0042c0040c841d40810400f002030000c2e042500300510f6100d113024241c0c41c0111000d6051410031541c03441e80c28010b2442e07906420b00411103a203400c0d404c40b4403403444074001e070881d61588401960f8100c1d401211101c0100c0b50b00c4108a5915030038108226139403 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 220608597 1250 220607347 220607369
    0x100e060a0905060f04050a020d0c06030b0402090f2e020c0a0f0f090e010b151306091512110a050c070e0105060906030a140c0a0305060306040b13030e0d032c0a06030c05040807 77
    0x45400030140403100c0c2213700750701031801031040d51103541d1400307049001c06206440340321480c14203450f00140d1041c08005410707000c01c4009403140f01a03000407025440041990b840c41c100d9200c5800398a4806684a03204420350301d0b0005001a128a400119800c000d620000c41d0b0b5868079000200b0031201a0b0329840142004a01481c4440c035140c814001042c0724200000007034105040c452020407202604000c4c02440c00f05411054aa507100e030054004806075540c948004650040c51907000f94190000343c4102c403004141c81d45d4420440703040351030041015113002c2c80103042c0009904010101b10091355a200c0300a003000071084900e201d48000b012031903651020107000380850350702030b05081c0683d04c41d90420000910300e640e40b42c1c020b1102d6941c27030001034540c50308685180034101c2d0160030400c030f80400400c258200100d4040828024209428040d0011060440d4190f400c6c480341e03c800203d00c04c00c03240b03000303a01190400d500d03482c005c1d10b440d40710945580703441c01e07607070000007092 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 220609847 1250 220608597 220608599
    0x60f14030a090203150603120f0f0409020a271a0d06030521040f030f0203030c010e0a0c1512050702071a0a081012080318100e060a0905060f04050a020d0c 68
    0x102c4e00740042045207052040c01a86400c020307021070307503410301d924242c2c4402200143d01004941e841056454410001803d02c0c0c0e25510356000c00c0194001401c01408241602d0324044140d01184804c0e424410800c200a009440c0486102c2004d002c001c0702d1700890000c20214001c14440e0241d80c001e50b0080300206144800001c4030802410b0381c1c45030813403051060106100514403e60f150f01101d400405404014046000280c01c511844c0341d0800650301c0e01054090170070000c501505214083c00742107204503500c00c0e00000507069514104009132409141182d03550749540401c3d0040317440d00c100c030340450f10ba482d600b0048000c5403202c6138449000c1086405541c0c0004100c0d400703c07540f15038400c46441e02c0c040030840e0f022080000d20820002c400030b01007460540c1d6491000108100301c413003401d49142884c006000c1c0e455100700700e000b0200050700d017400c0d901822500d1603100c03004140301d581e218100d4600d40c0c00600300b26200d004500010700560750f10020901c0e1740740919190080e103 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 220611097 1250 220609847 220609849
    0xd0207050d0f02160f0911040f1707060f0503070c03140705010203040b070306050a120f0b0c03090105010b0f04050d02061b060f070c020913030c05010c050702090c0310060f14030a0902 81
    0x803081c0300b040326510071004c0d401800058500f54901c1c0c00c5840d04000400c50701891100d03205136001c0c0c0c0e004441c510401c00c900041d1043c106003800302c0240580e099900181d181c00d4211032280401102c640850f5080001c1050540b01c0c180c5056074501a1420000200900041c001c042d4043c040903602c1d6900401840b0034045040c2e01e00c0d401140c2400d04010091801012400c0100300e445444002c3d1644407400d070a00014844e8518140c1c0d0000340d011091030480c2103010160410780d6070002a40c605800442c649400030115021803600c0041c440c10585005c04200c400048604101c1e0800f00910602e10618544110310800303800c12000b810481c9080744010240903002006841000702400380c07400941c4070040c065070020716003404520310240303605090761520302e0110028a15840c111030300d0366090b80b1502429006100301c840e006c0300d485005401095000960f400649080824820071040e0300816014803a5400c6040000c20502e014684825a400032a0f488225a466040c17135021 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 220612347 1250 220611097 220611103
    0xd06080d0f08090a020406060e042301031b0b04090603120e0f0418060f090317010b071e021206061008010b030f061203040801052707060806030703080408010c031b02030f0d0207050d0f02 82
    0x10b05444041c03060005c00f4075003912f200756103040c48090b0980d940d801643c20150f103170700c0404025041003080581e8030780d5a0350050000700700c0b501c01910824030039913044002510500c0300c4282d4003402000b82415410a0081000400382008080d042640e0811800e001940a015840180b0301d0102d000078680f40c0c5040240050b500030200c4000f02c0403040041c4405002c0c0010303a0119038101c0c1c401044203401c0d103c586c5030952b0301c1300b02075401800c101c00072301103090002d030041c0300d0311042e101e2a0091116a00644078107100b07014034107000006000003034007a00300b0403c103540300c0da000b0000c4000100d060301c41c03801c41c0d20a8100750f140b6512030041217180c0085481543c01e424450f040034a500c904141c003191140d480f07000b11020030544401141d8656004c01c0a00080c68110f922641e4a50f43c1d400c806000305024510140403e0030000883c29842c2d501c0c8442002c6412600598a09801e90b4200302c80c560001c4810750f1a15030900400e004140100407202c0c0f000842d40300c07030101c026040d030007034a = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 220613597 1250 220612347 220612361
    0x501090905011103190f0603050f1c0c020114070206040b1201091107030e0d0c05041a03010b010c02011407080f0a020105180106060f050310090e030d06080d0f08090a020406060e04 79
    0x520400f0070000d0004220020551071440400c004c03000074618030b0200b0543c0038120343e910141a030b1003401c075003850855005c110840c189625002c41a0b40240c08901521038103030021002e40454030203440da21070035410800400a0901c010201071a003a240c1003412100e41089001c40035000f04040180714162140c403801c0203c00314200200c0c140041c60f50003c00c8100141f041d18011a800b0001c40c04000b07950785c02101030480107105008460450480d84606100203000500c00d40c03c1003000b01d55540a07441c006480c0d81c069442c01c18040880307281408543c81070b04210307030805c0e08004600003c07028401900b04045558004641e904000c80d180e55054240a50214140d00d001c4c410009150009626440114542001900c03581e8014910010050903807100d6555400e0440181001c4030200040103d5803c3c614100806a04c40448940c2c6101c02a0500081220a004244018058524158081c520000301c07050020b05038042400c0e00c0041d070014000c00c020014010440c902402190 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 220614847 1250 220613597 220613621
    0x50c010605091b0901090302030609030d061d0c0a05040b0406111e190303090204090507060f051801030b03100c08010603060803070f0b18010905060406050c0c0606010f020709050109090501 83
    0x41454208028030410309801d0400c2410303d04000510100c04c1e9009a500c007009503002000c0d47c0c102e10708000348607180d902101004510318945003010800940500c000100c20303400c401c0034021647e82280f006003527444138004009016084c8800103161070400300500251031300d40d036081d41165109a481d4035103024a0740d082e110201913130300b01c0c1000c00d000544007a14210802c404000c00e4260600b0380003000001c1c00a50084d00389410382d01071200020303020003125929a0360b442d0b20b2040302030440d141d0107011207400d4801110244940b480d84642c100180800006060f54a4180e038105440b04644283ca881004a00c204004000664152007400010102000a1450b0020030390750525451303c0c2c40801400c00e80d04001240c0079004a0f0240e2400c920018020080c23118142000c46d41e0380c034120780c00c0302c2a5040800103440814984240c8910544034030003800303143c031194010b403458900710003038070210311031a0340019118030709000d4140205103030b120005044c1c2160a180303007901c501d1047c1d1 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 220616097 1250 220614847 220614859
    0x409090c060203070f0b070e1903230a06051e09010c020f03160210030908040305030c19020d330e0c090105101805180f1006051c0605030d050c010605 66
    0x1004213810300a0100841c0c5d10841a500300da441070747c10394180e070310411001c0d000381d04040203110300401403039194140c0303003d0410a4a1601d03088034500302c2002002c20002181c0217006584001816034004030b4004141300541d04403142d0380303a2050440e00d0119009401c0d80e4695600524103078050040c605d640b0001006145015803185282c0340300c46003204003d004003035484000800d90b00c00c1d444903584982c840700c04c0e03070713100d81d1703400c0c04c4e070392500550488240341c0902e0b4110034008804600e09518540c1c042c040c2c092440f01500c1d00e80c00c840021602060442104040c1e240e00f4148020309081200c080d10000382e06030640d440c031b62400040800ca6402011307a080103000590724002620601525454003400c400303e40c94004103119a02c2e40160740040e595600e465200d12603501c15841200644100f000542d110343e0350010400c002d100303d0002c10740800c914102c6020801e1a8000e201c2c0c01e58000c5040390350394010a1510b44000c80a82c005100030607401e600da0001c0c02800014402241c1d1 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 220617347 1250 220616097 220616107
    0x509040e030f040b09030f01020c0d020706170112020315010603140603030708040b07030c020402030403051c09112b05070e01061e0309060b030109060f061a0a050c120409090c060203 80
    0x680180f08900800121031000700f400107081e03904114002c61255504000d54645409020940d40c40841807891405405000340116216206030a00001580244d40d044d4940e443d11020002140c0f102c001030f03030980540000c08a0103816030910038001e114695000901d90005070714200f0182d805800b2600c00e42040055402080a1400341c3c5d041d1081a80c1f0503071740741d10758601a24a400c28440080d00180044100400c0c55008005800240203801100492900b028045e600700c030101d600040840c4416502e100a030b061001c440c114045071a1000d80c201c0015103443c000007101183d007140c95510104e0306120b95071401d41114010721040c2040d40c000104000202c104a0440e401481099038581194050001c25006008910000360082101081305c1c2040c402130b100a984100415040901c00030700072007243e00d000ba41e004414201e42c185150781c40101c2d495401500761305041e224000304440c103541c10303500a01c02069100c03400903504ca200d1404460000e0f15074420700940d00240a = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 220618597 1250 220617347 220617367
    0x6080906060111071505090f01030c02120d02040305031803010b010206070f140d1505030f0703051b12070909030e1005190306150c0c0503010b18040807120509040e03 73
    0x661a40c0050003400c03d6200e0030a5141a189428950760241c94110317620b0180c0c241150b0000001c0014203001d0b207010071000c0000d00150240d03a94508000300503804804112601a80a405000340400a210242c9800e0760398560310f15582240b00c1c00e4403138003a008800d00c500c0c9802d200d2095814000e002815031480d1034400030380002c01c0c0450220510443d1114200c0b0701e0064030032a0441c883c050380421000960110300c410902d444d00910b8040e2180039500400680300054040480c0d0f4000c0041080c000840c040801d5052000112500800c440380b0f8042600818030607180a004440d000003405541410018440300443c8151802810402082d070469a846002c0b6048503030700300c200128401854408800030031003940303c0940000c0d03d107000004180c0c403c2010744401d0203441d40f00440790b203031001c15080300c1442c035101e548204840388203030300345250005899006001340141408c020060721030b42c51300030585491000054001458000d9458248501d20790380200100039400d00700003030 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 220619847 1250 220618597 220618603
    0x90615070303090203010906090303090c0608010f1e051005030f1302100302092805130e06070f0302120f040516210501060f0608190506010c0204020a0c0605040516060809 75
    0xc000501059100c0000c00d05540382500b2043e42aa03024a003000190a1424010001d0038207503001c5a0003e5100d00011307005200d20302c9a816154520b01d0114514500403007660b0342c0107610b081a00326402080300040c1e0b561a03c958485950064a99a5884c83c190b100034009080082480c0388040c1e540d0104400340e220540a03001702082810300503a0744000030b000443d15500120507a0104d8110305400c10300f0390000b10382108a403400d4624003140416850107070291400020360742440d6010500081805105201c0e40101446038100180f50100702d8440b40406501110601d24180e40710042c842040020081158803680b02e08566020078104042d9080e410751700c66211700100802d01611041c02004c2d4019070041c0f0003000d03c4840e890b40c90718090480769003241c3c0a1940296568092a00b0748107000d00c034880c280596404020405950070000250000c04d009010090303d0708552000030228890b02c3d0060780610f00130400c00c03030600fa42201d1103030740760003944c2080031441c14010701c1c0c5000 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 220621097 1250 220619847 220619857
    0xb0a091e0911070209431407080307020106140103150306020d060f03060902210718380f0a03141504030302030f06091603050601050f04080309090615 66
    0x140100c0c90120806800e580d0303020300040a5070010701c1c2410b129618000351b8a44900300103d5204003090201ca21942c0340400d4290384090896a2500d0090000c3d4400d425070180e817210720018908210710341c0c5810441344c00494919003d80e5540b001030109060b004459440d0031400d10b010f00c00021344891108445c0340c1c51000071700c1d103a008100e20705020f51035001a17019005015400f980d250307890500354058420800164082c0049906103004000303d9202d20442440d070708000e004192801c52243e0b0ba1490205642400581d030346200304155500328601014140d426007184910700c448402c0110742c1e43d0050a1500c60300000315075549030748034103d81d02c0c1200d400000c8e1401500402a50b00d042440c0010021180c40d0640c0411040581603406140505c540080780341036aa42d1380309001145405a4240105103540c02112641500c25084142e0045041c9456400d00e50451400c0c661038101e40c02501c80d0342c00125403014a411309a41040e0702c81030448640d240b6441d141003181c114451 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 220622347 1250 220621097 220621109
    0x1815051902010204090c0801050915090106050a0221070311070513110f070308090f060601141b0609030a031b17070c0b15040507030b0a1403160b0a091e 67
    0xc82140d020198002c0d03066400510300381300c00303101c03600c0200da008001d600d0034020701d489526004007269070940d4681140801c100050002c160a034201101540c890300310b038050408520030b20b0307050b0140044144c030107416101141d850903210032907031138050b0040352904011180c0c1d900ca007508100d070303544510a401e107640c03e80b44000b90f44281d00c201e14159102c1c07403030300d84081c2c440042da0307200b0154000801440b5141010a0341d4800c541e03407000d0b40e1100c078203403a81400901e40304002140501008000c1100411180c06010034645801905040c80300c111603140c0150004640682419094011340300c0110402e401a05031b0f00e030640014101d6094004114005e11606000820f00c0780680750310710b485504411200c2540c0340c80c01c405c4100310114400d02e8003403410403001c200080d010340078440103010000d00c11421700742401c03031408403202c040004039030610805002070f884803107040510300900f2f4413002141c0c0d00d07903070f1180103818240c846d8071a020b501000c130b000406150300c0761406000e40e05c0d = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 220623597 1250 220622347 220622377
    0x10e0904120509040e03030c1b0109030c0b0c07020d03020f01140f04030f050c0109050a170711060c0a0f0f02190b0403032001241a04090209150703181505 68
    0x307040081380040c50701d81000900c41c80000306100300f0520090144c0104d000308400c00c0d010130052032010f4240c3d50070b40001404181e515121000080341c408800783c2c44a021105c85017481640e40009801204d01202600540c0014044000940e800e014194004454108900d15402d0803080c4c0c00700f2610041c070103404c1040380280c0d03e0040f8450f030100d03611010755070002d2041d01100d04205840700c0020400301d40f5803001c040480384040940055842c0c0070b81207100c0104c81c0703800c0f5040c0201075100d4001a1040d018403218840050b4641b2086d0301410f00130050744120301c20904c1400780c181c0340c05041104402800038204511840f5804542c10b596042c6407070215030001c081c01d0002881d030b580030501c1c154200a400654010602b41c2d0144000c0085480e0040e19641c0c800c4080030310b520902e212406008003c03d0040741d04940040450000240c07600c00c54150900994100782c05c0558214001207070540d4403c2e200120010032009810021400042c03107003054405440c0b482074604c00000c0c19 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 220624847 1250 220623597 220623607
    0x1120501091a0702150601050a0e13090606051201020c1902040b0604180c0504060f14120405070905010902180f0f040507090e0112030f0503150402070305030402010e09041205 77
    0x79000809026444016000c810041c0008568810340840d80400144a60280804041200d40a2500070541a1603652510340804802c5401803195078105400108890300144a511548180c2004a004081c00250b0700d080008106040c084802d1040044e03006000e96041d08002181e6103140b00c2050980e03c1e0851110301c0810060031509401c5644800c0c0443d00140481444003c24a07801504100b04010300300f6850a85a0380254090500001c00000e00c0b0f0560034051100b2900b80c4212003246410000361419415805004903000c0f034031500070000402400150b4002d190241c0305142c4103500f42103441e00b0346441031040b0704c81188989038088014401d80c40b609038041d06140301600c1408070345800c040280021241c0d2140300340000f0034200000b0b0110030a00c0c50480719500d5615104018880c4001f00c8141e00041c0c65260f11144141c1000c08558880c402085224032079100c00341c0b82c2c0350078000501510745441e04e050051079081c0400c0000303801e41049080803011401c0240d110 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 220626097 1250 220624847 220624853
    0x32205090c130305010504030c060b090c030a0e030c06161209030816030b03010f0203062b1106130f1d09060a020307030f091a1e0a0f09051c03060515030112 69
    0x2c0425400a4503d502c0c0c1001e200074580e01032031490703640307001b030b1000e100484d049000c2c480302510441c1c7c2e0300c024031024400703d4020076413600f20902c4c01c81404100c03030504103061076440c01c00b1410350b4801c2000412031810a0b0300f9802040180340504009010404918030351806001801c0c01041100424141d550480a1078020f91020040c0c41000d8000c014500d084d0000b08025482a1901d501c41e054070404042000e400202c40ea02d41203803200b810001c0c04043d62900e0041082411b4154410414840d8444803140701c42c08800a140f070308110b1020f50b14010003174071a00800703522056000c4592041051009000801c01e42045000e1401070356980c8114089009204510070450800d0400106000f40021614601041c888018071000710b502c0307052645072410111104905031040140004640e60029031140b03d4808483c00d010034200c980703541e51810700c14091101400d85070304194507a40f00b5414411030000e40030641c0d0011303000740e10845030003103800f05200728032080c003c5030311074010 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 220627347 1250 220626097 220626127
    0x3020f0f070b041704081209030f100609060510050909040c0911031006081909050c0d030f0201051501171902030106021b0f09010e0709030c0602032205090c 69
    0x40d010109410354940c441d03032030030030500034060364207840c00700c0802d0081d580740240f502260304449402000700340381414801d000b030080d04494400c40d03141c001d1103200c8540c04020700c40340c06480058080080c0b0ba90400c02018201da5450704042e000381150303207800c104e9a400000b191500303401200d804080d59600e290114078400b4540004079000d080803000d0758000714907809180284040641a505d250f10340c00100c40e980c07021a00000780b0141e0302d00c2c982441e0241c3e405281c590b13002e101500c0d06500301002180c1d01a295080c2100040c1c0540140070300030b035081c419140c00c02001c00301d070383c80681e40a0008001403040417207142e0040c40d5801243c200050395002805c9114403207415526580d4446002c1d48030020f4103020b80380410020a1240d00c0d15088a103d4803059000344060203903403c125096058000052901c400d0007107614001c030103d01f8038206200144141c0e402150b54803440020f444500c200c8190340605601c4a801c103014503980e5000c2150b2104640801302c1d2249006c000b1440 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 220628597 1250 220627347 220627357
    0x70b1e04110603092e0b040c080112050c100f1707080703110403020d0b010305060708010b040902090402281206081905030403080408010f11070309140d021804060c090f0603020f 78
    0x50010f10340e201c134605c6010600301c0d107181421503001c204000001038050005171000f107109080000c0d074140c010301800c1c07400260300051501031130031500c1035000031012410b10030480d00410b0104541e81c2c2d140285950000c3c0402242e03e000b102c031401400c06020280c070200c0f001d049034050585031740d00b01c565041c60409503030082d500249040c00c0d05c092814801c80500080c00304bc1c40d86e004180000c6c070424003591b0341d42d04032179140304010316103840c084005009400c402e41c41c0358800e4080115a20202492440260307203040e1909084810700c80741320140c0b960030900700e42d03074001d800d100c000c20031a600400c1040e215811b403940740031002c0e81c0785004c60441c0f140d0740004005034004200415407010560140000c10b8118504020410300d06081800f03074010f5000050028103c2c88050000c1d1003c8070400854402c06800e004200c51a6800078180e00c41291050024204540800050000c17034040c281105050342002c0d280541400083d140150740d030b006203014180c0001e841c0313503d8600401121 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 220629847 1250 220628597 220628623
    0x21306021c0e190308041e12030f05040902070b0108011b020a0204050402010c020d060203011802040b091e0a03110405070e1c08130909030e1e0d0c050402070b1e0411060309 76
    0x10900e81e441703140c000785942080c01080d81c00c0c0b0000f05403254102600c4441c41c00c0d20080c00d00e00e00705400d40d540881e10745e0f144841c00410403405100004000900f4006416050301c280d02007041c943c10102203a003164880913501184801e40045403040700d03004940f03a000d15405880100312a074841c0010ba440340c0001034025080300d030140306c00d81400519400745058844803450b2100c180c0742c1d405190300341e00a41c000c820b0301c100208403045203403030104103c0c94002048520604007001c00700024609403904c1d4800c0d10861400e454045140c6042e108d2580c0c0000c2c282051110584203401140d03a0b00c22062000300424403c180c6141441410380658080010207180601515152040d010150882e00012004581c01a00203502c0303103043c2c5a80ba0301e22488441150320780101000300b0030f80c0684028113030345035090014041126196070000700b803064015122141d45003030407601d03000c0e88003085400b00c64200000007071000140040415004a060848500e40c890300c92660542c10000c403c0e00075 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 220631097 1250 220629847 220629889
    0x501110703050c0d0203270406090e0706020705120c120f16050306100612020f0415050a08090613020603041e030f030f0501050901090905160603021306021c0e 70
    0x880c20107500c24020001070b03030444291041c4c104100d8041e0307a41d0250031403180c5505010440944500a88492060040d02c01040402c45542d81c83c1401c084840b180c0d4801642c2e00305403070600885404001075402424140d828144103000c00421585035202e10303440d10700c100c10411320361450020800c03010300030141400c16a004400d00908003865078131548145030283c010b03038000445014221841004544158a4450014500c0d007920002580031107101d80c240750b000d100120b650303002c02428a0182c030064450f190380303011643c40982900002462041c0c0c550090013000188121422112856079054450355240d486510b0036481c285aaa4205040c64285071444428154481602c1845486a4a08002b8003c40c0c130081c0090b200300b4011681c11540420040001100e2035000005540c000d000f69201a0381d030080d201c425103020352000c00029004200074810302d82000824006200c2030000b4140d0320722540c00e458211340745408050600050060986164072240c4407401050026048 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 220632347 1250 220631097 220631107
    0x60d050903070c0e0a0b04020306030a02190e01030b060a0b0c0309060f1c06090e070303020a02190e240105190e1306090212090706090b130e070c0203010e03030c070f050111 76
    0x1c04040003405c50f80c1141950a000e00e4161905003442281d00a140140c041d0500f0781181d001d02150110306074a4a56034100c84100040301c01c02584024003840c40380010003218145a400c01c12070141c16007001d0140300040043c865060000400c481d07607110166061034031030040c041d480409002d402030701c04100c2450f52030000c840e44507030b1012050785c20690040089850f4900541c0d40e4501500005025038400c00001025107001c2502d0711039006100540040c05482d40b10000301400c00360381d00040c241100390f0511440c40c4190340d4084005081c0b030000c1c02d12905000352164094004600018441c56100e0181c0395201c0c9412501c14100c2110301340300321b40d03450710101c009610901c02c0e0310412001001080d031410001ca4084103c41c05561003035009428203440905c683c0c401c061492100740e582e60002188038942540501c40c24050329122403082c60341c0117142c2900c114881000c1103400800c02c0001181d4400c054a03000c41d0404c6000c05148020301d0705a00420350400058003215020070 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 220633597 1250 220632347 220632359
    0x61d0a060507030201052208030a09140604210504090905012d051302030705060c0106050a15030c032702010311030c1306051206040b1c051c090302060d050903070c 72
    0x600309188244d000700003540e254800c3c0b649100fa90108019080f1904071420003040582c00030316000500f00700001104103d5580b140f01e55003a040410380c00d41c000741704000600c0401a5281c031801800e00ea942c05088901000500c144542d0080c000b18607070f9182000c0500c1400d500c0744101119544c110304005c80d050fa031125601014540100300c0c5400d0100007040941d034050381c6c0a00c15400b40062814138208020400c0310b41148000c40f4441d0340e5030300000345a030340304410302e001040465012020800c00c0c02c2d00070281c41140008506050502040a0956040c9005200c0f00050002c2c0651400007901c01200640045600200e260784040b051141115100700241207050b00480501032455880300256241d016981400c41e926008400244960034243c002160303081004200c60400b8840b03201112419040030400e03140c0c1da01c00c030420620441550f01c0702c0e41c2005103040c1210791519590005000d403040c3c0c5601000d040d121404075109100401c1550302d00790303000c03081000340e980740c1c1 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 220634847 1250 220633597 220633607
    0x71203050a0b180708042f010e0609030c01200601080303090d020604050c0904020d02060d0b01030501080106030b13080c0a0821010b16020102030c160e1807061d0a06 73
    0x28811142161800902c55032030315222480108003103e6600c04100c3d0703a00d800096440d844010000d1783e08013003050030004021035151603080d4402842940602d1170014100041c501009608090b014200821840007140c0c4d00090b1a08000d84c2441c200c00b04428071500c10000586041c1b402501e4440d003000400c01e028040060740c0704000410499440c07a03140c10040381d5410701550054416040055081410708281034003030303403150000d050603508681c90ba002c5a0158415000081c8255032902403030000c2d82d043c01542e0050641e00002c1c420b050540e2200e482d5003002a2a0520b003084e200c40b5641009051003ea944241614060341d8120b441802c0c0060150321051001101c045000c00101007221800b038042e06841700e444205061007684801ca036004594000300303078107601c414000006460300801c680c0c140e800d4130b11280d02c60140381803207040c41244064219540190140700d40c130305203070b4005142800c80d10036182c92201a551004821041c01110720590740101001c0c4010800390703086 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 220636097 1250 220634847 220634851
    0x405061620070512060103080a120b100c0308090706050a030f0612150f050c070f0f05101d010c0c12030908030a090302060f04080405060a090b040f032010030c0507120305 75
    0x4e907582601c1c44031850b1007541340c134424000103011540600001c18594880c540c1c1000d580030034000012600c07160340010f0a0010b0324000303640003600f000c4828041550007220303135800c01c40c080000c040030b60900300041c00b40d000c1c2c10168010140d641c2298071400c134840d005000106140044921456070324203003040210f0300704000b10009410248030ba0141059803003018400d034125034409007880c04540d1240307200800010262007258901d480d1101044041c08161440110f45e000043c400140c4041e00041219102d0070499a9160000c841d42d8180c111074840c4400d0361250492070b00000700c0105400a15503ca80980b8580c4044200402040d06070320100c8241c4c000d40031100d10b5680c1102c20001c540b0101d034020000a002c0c001044141491005030543c0c503511300304000b62903100d02a030071240d00030381d10103410441500c3c0d0400910265031101100403140112842071440d8040c0410341c1099010080f504245d0780344800521240b084c03003514440e6511600b449003204485200601500c2d007 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 220637347 1250 220636097 220636099
    0x3120228032301080a020d0213141915092d09140d090302060f09060304061407090b070807170c01060f0f1d0a09140a0606090504050616200705 63
    0x2011048074403494038039090b50480f00d200000b0310054030580d0038040399962204040360000d444095144010030385010f0b803e2110603458503607409140c40001c102100000140c071100551800b09420070000c03010542c1010340e00419000300302e450800d441070b41c00c400005503452103d54440240080d111007900007480d5640075001c681080c0c2c6030b5504032526240389020003808514900820401030902001030400d41c03042c0e24180b410942c0f03000118083e44d10803101124207a9994101c2000041c08159a0743c01c080185030030030641c0d040009882d40d40c4200f100c0070b1300205001c00c90504000d45c0c01d0007440107110035031603182c403400350145841c040c0840b0300966402111010011139800804c42589048072108105140c50340c51070100900c06020140c0000d600700e0315421500f021031704001d1070640c9100f01c10020300301c504d9035007040c60807580030381c101c445d54038106011721001c580700080460700400c074090208c1000c04003000c25681c0110b0721021600c0f50508410010075140007050100c110740b0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 220638597 1250 220637347 220637381
    0xc06031306060902040501020d0c02030304170a0b0a020f0720060706391220030901050907062021090a050d03050313110d06050702190312022803 64
    0x52182c3e81c0d60244e004e24000c2900581c09000903050341c503c5052000012800503050300c0c90070b034543d0001c580b51401042c03000515031000a880007004845484035503c05803001c800c50400322210410840c1d03100784c00c00500400315403404003981e0072603032010003014540102074580e0303002c0c82d140c060007418690040b0505420b401c0c0c04c01d0554081041884400780e42003c0854040d0300112050380c41d154800e004290301c60b5699008040000e0344440000d64443c90406e0313649074074040f9462401c0d00c000501540189d00401c0c0d040180e41d4116209014034004001800c4240e8416642c152500c5004d0685515071030000c1c06110000000e10024002c1030010785400701619147e40601204000301000140054003c00c0019090300345807c12881140c4688100c1c01190f1110001452040c458a0f082d10a03659800038807000613010080c3c4016420700b81070b044096005a200500980b4001607840c1520ba000100c8824034030600780c14207641c41310030701c00450b48641c2c5030006006203114200340c50098 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 220639847 1250 220638597 220638599
    0x10501060806100804081e0405060309010b0a09090b01060c1110120c03090f080309070b0c010b0f090403090603020901180b0c010c080c0403021509100c05100218090403020c0603130606 81
    0x2e403240071344034892604004c0d454a80722520148042818020b030040781000418840403e860f51918001c500401c0760300004030303401c0145030400480f40b80c0c542c0410440d9180c41032400000720a0300c100c50441c3c2c154180303500848c078941071030240c061004c410243d024410081d48040c03070b50480300030415250040d100300903110041c00144c0440c1c0d40f00790f0140c80c00505150105c00161244011680227043d0001d451581d540c0e5035500200740c01a185240c4070341d460301d004e010b5608040c6d20030344400d9001c560b024440d0500351009013146040d03006080c105a0006900c2085074001c01c11000302710801c005104c81039669044500003030b08090030400c5030b94245a400060b651161081034015517079604090325243c1303164200400100d040352034050355542480420030655400854a2a0746000d80390500380302c0584c0703030207800d000d40100d0400e01710784180040c03160100c600820310a81d40090f41c4000301c588450a09902c0c20341c403c805150b000ca40001004141d8461000c200b958500c503000a07c015 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 220641097 1250 220639847 220639879
    0x80703091a0405060c310f09020904050a140a1521050706090506341208060306100608060609040606120627050a06030c1511060105030d0c03020f010501060806 70
    0x340301e10840c84241450a01c91a041401c1c00c00c13002c40e01b6811003903000313845661860b0201d0b94049640c40390062590108a6032007508050107542d41c040700c003010800080d4022400800b207548040d0121a001d03a0765400c0054112144c24118007500300b40c0c20200d100c1c40386514140c0d00b80c90303240c0704490500601c18001000c5009100d00425a01c00626003410a1000071041c8103103003400e0307015240fa1141407074140f0205a54074503034080074051501d65404007404800030b052200083c0034103010364021001c009400115035446004d5036180c1c0f0300f15600c1d071180c8002802034000c802ea1150321519102000030402e410526489004528820a0154584d100c4100e072541c8164904c2065010050003003641c1c03c2c50550006034403140c5480b0001d01e09450780c0350b459031070f0300315000455842d18808086031b18640000b900c00c400c0d00030000515680d0b041c84046500c84e280003030100d0500c042c040600c400c0600070701c044034500500d94000c00456a403504002c2c13410030142c4445014400b812055141 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 220642347 1250 220641097 220641121
    0x20103150803030402090901020415050c2e0f060b160201091401050708280809010b0a03020a03020f060c01020a020105060f030f070b0307030b040f0506280303080703091a040506 78
    0x100c1c1c0041001d103055681d6a006c1c0319080c840100704281d01c1d5400c20001ca461400c0410404003185241d40d0551a484074030b11451601406844540c400c81d16006070442281880c407141e1090410800d01245c0009500e0b0341d800036110541080c0910075020601e034000c1040da00e003408695000742e86241206a0390080d08030410007148140740080c02c10043c603400304904130014043c070210f03050115000720f05045009035161418541000217045202800100842406203181c00b05048480c400319514542c00106549410b1100074040c100c6041e130340d035056554000380e81d41145004001e541c0c50866a100034000d101c220341040c450021218a841e140c1400911101004050300080101d40e0504442c01c045400003400041059260300200c01c04e52910f014914840000b05004200c0b801c28201b0080150400c5001d42c44002e01c4040242c142941036124004032030309810040a0350701e41c0101140036086101002d01111180e03070445004007a459074152090b40a01c003030380d4032502c5810404071 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 220643597 1250 220642347 220642349
    0x1e040c090e0f071106090115060e01021005220c060219320d021c0c050a0b0402060904021810030c020a03120e0118060b010507021804050a06020c0a02010315 69
    0x10207001004001020b40a41d0b010841e0407904904051500290401c4d40d00e103418011100c3e400d41c1c0e5140c8205c090000b9902400c44090000ca06044840180040000350380380c103007545c8008503684617000300c0d4486850034104030411141490303c40300c200702400c1a810360b100c2c611500005100329414145800500c00710300016a52144460b0101707040c82c0c01e400b02d9000c04c21401603a80c8090126120395600c01c01001d001803e454025104045150034921041c1c418044404c00740324621001c4000210003040c0d004000d54020307060b25182d107950010481c50f0060411a503001480003030049103000195102134000013044440341c82120203032000b06c043c0d400501403140542c1c8252120400640075039010301c1ea01c1840b03240050700300d040400490a4031b42810340f1b0b1201403d6422a8800d100e003e007d020041c240c20700345640740070380c694082442200aa42c21032810682000411308001c42400410301076030b0080c00554498402c424515101d4480c0a0200d000c80e241c610b0812000d4240c0003410 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 220644847 1250 220643597 220643609
    0x2030708010e04060b040e160e0c0708180307030303020426060105041a06030709030311071503020c010e060108030301050a050306040c0306050907030501060e040209010e0f15010e1e040c09 83
    0x240a40d10b030025410320808050011070703c05440d0b00390310400361514826000c0104030383c0d0050030380420074111001c11691541080c07603501c2034001080800c145a40444640c1944042015502c6001c449001442c2190b4440260b140c040c16034000305240d41500a003058415000880289c2280b081c040c004030100e038000712509412220041110b031616038080b4441c407020038101a00d45442800040c0e2640c070440c2d150002c1641b9520078024554804503c810060313581c001440101d080c51040b04150030175207161020540c0010b4640340030720013074100003000008030741110401d503150070f000e9483e90003d01030540a80c0c1c0d070380c00c005050324000654500454006490008981c11a00c42002600000746820303180c1c803400c040080050320134410000240301e110354071840c03428903104100c010300301030744159030800c0030304188640c1c03500e10f044042d0082e0100c031031041c01c0107079940182e0325440b12203081b5610081c4021840a030b64a03800b81c040b10084116405c019403000000207840c5c04509010b15 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 220646097 1250 220644847 220644857
    0x2030c071a0409050f1501050c03070f0c030506040507080c0f061608040b030405060403170618040606090218040e030408031c1d03073c060b04050403050a0210020307 73
    0x80000004021200d807481d01c6060400707103050740303403441c410650b0000d46441e0320a40d400804c0107495050010761a1818809280c114500a88400640d03500c0c040d4010242504182d62011000c211100f10490010360344001500e92a02e024140380b510f031645441002c046014158010f0150300d07012103020209180181458141080000454583d0143c41421901c1007010007011034004907800185208030f00c14001440f0900d4503180c02040406200b4102c0e079000308003818096941e89520780d05010110b1000d44140c26900c0c2d08104028000903130040b4202c500c0013441a008102c0306030350700e18200c01035805018000c1103c189503560310443c80781005941060000a80801c540d4804480c1d1030700308000421540c00342c0700c80350340320090f00040140950000400034104003440d82e19010914039042914012080c003030301500070480d8079242c01e421101580300c2c10304000140d8050060800044c2041009103050318001c0d00f01da011120210151084507255003065105008aa01c90301d101d58030 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 220647347 1250 220646097 220646099
    0x6010f0903080c070b070b1f0b030105120a290606030403210f060909061a0901050d0309120305070302060c040b1e0d0908090f040b0f0f0a03080f0a0305010602030c07 73
    0x20142d550b00011101d45950141002c00034041755003034040d00c159030141c007003501d00b414000ca4070036601e58900c641c4800d15846103410404140d14005880c1101c1055500c04450360502c0c58460400200c20001030801d81045061141310840742e000d000c1d600c2e0b200148410580b607120401406000445c2c0003400900380b107000c901c825000032801c103480145003801246800701d81e030f4020151281c5402201119030344120060074044140504040160360351081452190341001140745c0d1101400703120f025052420a030b00070503210780020401401c00e2002641001e40030700d4003c059901c41a015001442494007141140c400b001c2140c0441e0030003045a071034102d000304074444054012800c05104c034014061030282c0d8070280201181b01c0d100c2c4500a5559030508100415031141621460145182068244a580310a13401408404003211845502c1d101d04000481c03022050300f009260034004030380341c0072810005014141845070f80d2800e00c9281e8a0700c0040765240500e1422a100d0b5005580c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 220648597 1250 220647347 220647353
    0x20706020a052805010203090c0a051e0f012105070807020d020703030810081501060318020a140301090c0602030a0206070e030c240c030403020a0905010f180605121506010f0903 78
    0x461160042d800300302100200c0d840340c0313504e800c90b00211621102c0e0341000da1007a0462901446100290100b250b00d00402d40c410f84a00c0904c07403140e05414021451072041e299140e020f5070304051000003504014494920541d001e9000c0c000503501100403601d903c1c0450740c001e002040b0155a0845130b40245001482d68804581c2203070f0140292031a04890340c400305010300c0c140040e0396080160364103501c0300d524100c00102203400511420040c14070501c1114010303624a98004211000081b18401c0010094002401040110402488206006000540160048054619001e00b6025a1002e580b240026102c0d481d031105055070580120100034030628041541b000801000d203140026402188203400555110240112003540042010800c51610b048881c01425620400384200d524208280b1100c9407140608040707401d00c6e540c140d46a100603800b003c02404010900d0707184012508a19483e40208800901c108005100098031540200202444501c903541d039481813500d035072 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 220649847 1250 220648597 220648633
    0x80d020702010e0402030f090f0303010f1202030304090c08040b06090c030708070306031b0302090903040602031c0b030a0b15121f0e06010626040f0809130f0606020706020a05 77
    0xc01c9050220701000794100d512144060341c41103e4000d035080c0303e0708068000616000600941c08580c2d80208010300816400c00540b0b81210384481d0b0004040081e40300003400e500441e00b00e000385034603091070b003100d055001c101140a903000c2d1289410648561050004542d000ca4268091807000c1020441681c03007010311960141c2940380011f5841e8032940c0d2402010702c250703042d030540c4800c14420b02c02c1d8030b400750b100c1c0e400400c280011403400e40303030440180d03c0340912588032803407081031001110031032415007092000c1100101610b00c070604501c0d207426061003c0c0d513801c1101042c103c0c82240b0b030802c02c20341c154000d82200245540180c3c440e019500d90318110400303107034640350100300182450070000700c0c0c060f008036101c001c81c031b8205850454200f020303645450800c1c4c035803806002c04035024449001c0250303001460540e4401d40e1001107402c4046c00c108020040b80742c40c0104200070310a5018605448103035007920105591401c041742d4410003844080c1503a041204141010031000d = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 220651097 1250 220649847 220649857
    0xa020f0d0209010e01140d17070302030d0c050a03060e06030c130f0905100c08040c030813080303150310020702010516060e0318030106050108040506040b191104050906040207080d02 80
    0x80084900d11615030110310840c4081e072000c04034401c00c40c014030200b40c0001102c0c40b6071038103850b601e040043d65140c00d0012008005000342030a00003510b20113040c4280112051206101c4040c4802880c1101c014030641c85124408002440e04c000401c86c22100c2008a0180000600814802900700c040100da400c00341000004030f5a0f82d64402c11a2545001c0c50450a000314040c06500030041211029180c00c03107241010000001c1c200310010f80140c03016020780780c0012646403200a45024032241e040c0680110071148004820001da00c0c442009100c80900c094064400d01d0000e140c01c44281c0c00b980b44000c1c042802800002c0811109140c40031005004a10201d4605000c01000382594420f43c1e0040c1c200c2c120b6009000342c4d0900340690001040286040744143c6415101d55454070806480204002d001c0408540d40f60300c0d0410b140c042c5021148100854011401180e0003948988600b900480c08400002c010b45494403c0d14541900100b907186000741c1c2a500b04025404 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 220652347 1250 220651097 220651099
    0x3120604020d14010306050c0a08040605130c180e010b1003020c030702040213080f0d0c02040209012706030e0d0f0503101e170f0318060403060507082203020a020f 72
    0x100b8040554030805900421a40740050f03102240a0750450410f4000e44800402d45000d00c0d40c10004c1d000015031201c03c007030788582c00000009850f110024080b00e075040320384015084242440011071290000580560748401410f8100400744641040500b1389020f80192648520100c0b2480c0f80a4013a800500c00f079040001600c1c41d1001603400039040b82c0240c543c610000312900000d01c1901c008210407051008039800412180980d8613004103075000340a0000c0c0102d80200324540d10307900800c4002000f5004052284607450316070041c100c14502d91040310006428030049200146000c101950824050f40c2c5074040d103c0162416125644003500d03103c51603000c2440000c14181d20003080c1488030007030226000300e61800007002a1505003203019910f40e080100c111034514000021140021095103012440048142c00100280150390000d031009003800e0030403000c9907000e000e40d4460701901040e0700d00000b800e01100003880070a075004016070711040030701e805803414121000000320 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 220653597 1250 220652347 220652351
    0x7051f02011d07050a060206040507120602070212010e1023071b0602070303050705130e06060403020d05030a0305011d22020d031701060e0315040206070209100602070905070203120604 81
    0x118142c840d048200008210280e034000f10b00501051a00650310300040010748001c00c00e5050a49403291282c0043c03041e10032201d011590f810402403070f501500d4405070000e2011060740c1980140b24040c1c03004280c903102c20300821000f440b00c81c1e040e201c1c00002c2e80d001000c00c03d00e80030300c00141001c0000074007814240219040000c03000307414401d8075100d15104240c05a1102e24501d40502a2440a0700000a01009002c03940c031710004ac052030001c0b01d03481d4090740c42a03150342e400319003144566000070b904107030007000440034004008000d05607611644e5042240360b07641c040380d00c03080340c0d03650f0071300c02d5101000301041103407042560395080b200d040d038054008068550b001844400c0f18120440100341c6140e0141e505040b2602e8107401004581013110000e07041e440001c0d02e89840715184c0005002e600c01050641d10ce50f030940d1540c96000d44100744030300380030003400c0c07140e5418428070005104608000c5580b0099005003030003400d194005604003800403810509a0070010840b03a08a9 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 220654847 1250 220653597 220653611
    0xf03060a0806011202011805092a0a0314060402070f060e011401080d1403090a08180d05060901180c03110114040b040503160f150c020306040b060f0307051f0201 71
    0x10402d02c0000e000b440700b40c88030084101c6604c0003410b64800c40a0000040c81c25072410481d5407603191071a0b5101080d00703000f0340200344c0010494400c00601c6c07168007562a02041e40d406503905540075020480c86000103a5003642e5080400060703204024000744600841e0107590300060071500a016521098800415a90382c0d0400c015500c0a0991041c11182d10400b10303015119041900b092401c280760385944d24516240591076034604403413030000c0c0800d100081d541000420250340f440983e000420001c0b0288042c01c00070382c1d500c4203803100081035182070101a080e00705410034400c030b103a0007005007003e10318540328030340c010382800455418400d58602c0c0018040032540200040c2000040007600c0702d040405162402ca8909813000700300950a6080c00311503002408001191004410b001d050100c42404441001d101c40d00250540b1420017807108200c03102c5403041c41440241c400401d1079040c2001c00d542d0703c6041c851140c0241e291610004103a44142c04000303000c00a0001007084 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 220656097 1250 220654847 220654859
    0x110109050a06051504060b0418270b092a1f11010e0303010308070b1812030103020f010c0f0308061914030f031e0304020411030405300f03060a 63
    0xc4420100d0031580d041c0d48500300901c1c04ca00c6803408582c424203075420884141045c0c0305090f40c1c8950300903840040000c071a0042c420b841074118400d90740c0c0c10000081e188009480446a81001000072180c202c81039002599003140064112010708000e5800441445600c081c02d05a240100d00300c0e0f08900034030200310100700380300d0010b240180f1b955200710200d00d8141407107086403040b6248484e20740040004101085224042e00d00302c1e60031441031580342d01c07104007008409003425010f12043c0140c0c040b81e01002800000395040fa4001d54034602214071440c0116101843d01a00600c1504111880303c046481000125480380b000342c884110014045045078030952580d100015005c1c02502000c0a0b0600340820368001c9000c0b0000d41c01c0424001c5039009500d4951407500e5a82c030040000707400d550703c0c0c1d040110111305583d01a6564241340c18a580c4078000440a070851602008000c1c901b500541c2112004034548911030b420310500d60142211948054541640019000030201d15 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 220657347 1250 220656097 220656103
    0x1050d0305040e070e120a08191704080304060f1b032c0616030504030503040f02030307061103100819150605060f0c010e0105070813030c05030a0315080309030c0111010905 76
    0xc20803a151701180e1145181008a02025980d040d4000d410000003400060200420b4640320f051007a420b008001e8904c0301141c4254869155040800003c0309000034807124200450065014000034007401c445500c2d0803080c1c400c0c145550707009040901010f81d00500c01e50110340ca481e4802009519200650920446900d00d4401d07101203030890720034017600c3c026640400011a5480c2070601035443c2545010b0018000204040c0a003401c49003c4421981d01f8802c60b411a0340c40340080002d00004403d552254008840c40212401104404181a040041c01301a81d036107441f00d19400c071415984101c143c60409441900c0c01c0c1e1103020105490740c450740500781003501c00c00016164066500701a094408a18520503164505000d100c4120341c002642540200d605045048000b460715086600c9180502c001d80580404a22074000542c1504100f0180040d40104a80540c40e8061940c9034030542184c150300d640004441e084030350250002c0c07a42c1c1003040c40001034140440e02d46a003 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 220658597 1250 220657347 220657351
    0x4061a060f040501080105040902010504031202010612110120120a02010b03070e09120306030c0103050c07020301060e060102100524030a0b0103050c01080c0c060c0913060b070201030c0809030301050d0305040e 92
    0xd04601c0031405220959201c11900d00600c4122014440391259400103881c07441280005030150084c040b003203030742034003d41055000305104054031621507d41d0412910104960714080d002920094a00d6010104103a00545806140e40a403a120105404140b110f130303c000000803c1d5501c13225000b1060341c082c0105002040700c0c0c01d18032054606101894100282241e48003080c000034010711905840010ba0750782d8990003800d0004154851890100c3d00f0f0050783c0c0001e62641c01c050f030102d01380d0848484e035805100c0a8003110300c255099203c0c042174130801c5580700070b02c80100900c1c0c13950005004011250660260540d04828400c0c0c407400004d5409030011b03100d90b800006080045c0d60b2103090b0303950090389140840d0a040030743d405ea54860b5406071540c003400c2c0d8040755641159598189080d15080302000420415680314000c05481d0001501a0301091424254440e43d50003401e80920500c040400b640c0307140e082204105494262803c10b034200b0505000200d406040440c01074 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 220659847 1250 220658597 220658617
    0x1506120610090b010224070c060207060b0a080f0a120516050105010f241409060c0604060e01060501080403050f04090212040c05010f020304090203041505010308030405101404061a06 80
    0xa05040c101107040341038502c1000c0084c11544040c4840d2520030f10740c011036a08490001c0c02c4034950f00c1e180d03c2203035150105003001d804103200160380020031007140c2c01501203040607280150102d40da01034090b00d44a2003000d80105400100b4a1030004030025000d0bc140d10540c00c12a04000c0c44503800b00600c0ba000c00120707041c3e95101c0051000c20781c8800310304000c02a034002c048400b0f000112840e40c40c0705c03000d404001e00440410100c01c810114013a11a440c0025101d59200c80440e0b0100e079681200340c0c4d065546910304a543e2075450300c180104019504180c42d0103840f5102c566048445900c034620001000c0e90074071020410900c1c2d40010b100540c1e2400c040f540c1c41c00c4c141081020400107a124034140030007a00750f07001e503a03004000c4d40c0881c0c3c040d980040c3c03283c5e02c0c2d0070300034410100c0307000c80701e030840c94040048204800c007000f460080f4001e6003200c401102454010045441803490060462100000200050b90b1500300ca560981d28511508402c404940031602d250401404a = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 220661097 1250 220659847 220659871
    0xe0c04080327190b16200411190807050f0409090b0915060f06091315090e0a0609030c0203011505011413090e15070e0405071115061206 60
    0x1020402800c0e14200a551104442c1c15201c0f40469400c5002c0a11510038105080300c04105044800310070700362a19101d421901d04101003220780e40c03815108001c4001d140c070039481c005035844006400d03000c0d80e03081c0013007085d51110203100e0341040d0b9070030000400c00010403100b0403000c605403034180080c1004040610340401c04000c0c078503001c906003c00400c51001039010203445c0c8440040f1810154010030140e406903045204a4007146483c425880d54642000701322a6100206071164460351419000c070650412150302c500c5070344140c0e54031200170005a0701510a10b008a80c00d64004156203101e420070903c82185a40420700b500c90000049100a1200710308220a58100b00780007041040e6041d8940380106c10303a03625020012034043e461185070340782031080c2c0c0c402d4108036461011101e519010720a03d0580401490303840d10221582c0124203100100742003900609442c01c545140f40003404011031641d0190704600c400904099001e10480903c8540c80000d00101d13000390310100030 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 220662347 1250 220661097 220661137
    0x10e0628030507170402090c0403020607050303010e160906050f0c0105040b06030d0c0c1703040e090c24090d150906050f011a031f0b21010605130e0c040803 69
    0x10140031518000c0441044c00301c103082d516070124030804496401030b070482c0d40e6440c0782c540b4508080035014682000307410100c00100b404c00c3c02400000303107040314070f07148100c4401d6559900c10899111a20404400303c0c448403c2400594001c0c006407405440042105007001c110002c910709640060380d090360385400c007400f44035490800b403091450324005800c00030125101640c034a4440360301e82c40303070b681482c42141c9004c01c00b40090048070010900ca05201c4070604141c42910b0703d6000171540340303200d80740010301e1004030680400301c1103c0c00f0325000820706168014003441144941420100c0f420045040c0902000c000b030700c07605426a001d44400601480c06982c20703d034200060300b1107041594144803190382062020203da5001d0350901820170151041c0c05070000c4a209500440c140d0340d000f04070a40034010584d029040204640c240c4429a60390b4a41607695128080c100c84000e84007850600c52504185070b4182c000314001c0080b850503507208425811a0000c01e0303580034004544003 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 220663597 1250 220662347 220662427
    0x9010f110a08070503100b0304020f06030106090806160e120a06020319050a02031302010f02010e0105070c0b071d06160221100204060c0308060409050d0503160c0f02010e06 76
    0x10360b403a030003501420140c0c603504156140c410b52001c503105611181a002002400715241c2207542041500040c0c8516100d5031202c402406c856901c0c000c1d01402c0c45100c0000e440a52411482d280011840d100e203180c031000300c018806007845114541030684100c5a44a0016044d44000d48c0318460008024410348800c000b43d0003a034101401c00c607417050040c803e0100d800700c283c4011118690900b82003241e000c0f0114142c3c01b404014900b04525481c1c401000440c54005200380903440c400d0b24481544d40d100007003602c0080b4503034034241d8480c201c0750491499050100007000110344c402112402c0d58000c0c0d000a8030700c1440c441c2c4c1c0e41490703400030b601d410200b010800d03c1400100c5000c25800d060400c0c8000f4144030f195040a8100300d003141c007050494595034842040c45802a09440d40340c2d5030500050f04036802907a014022034801c942d0781c03010324440d141c0b0500d881c2e40007080c01c03c419200d8004654200d880d1151640c0400304016140c0b8030400000a04503000030500301782c0c0300f050005 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 220664847 1250 220663597 220663607
    0xb070e010e1c02222a08011a070506270708030909060402160b0f06010f0507080a030615021b01030504080304062c07030c0602070503060f09010f110a 66
    0x20265605106400381e0200e49661030010842a0940380025221450424000a90f110070b01140109000d004200707540d0400c5107980100030380e401d40707175008000042c801d8124400006800d40c40c400160b1801d0044c8002500d142500b660501d41030f00719410800141c5841c0c4c20180b06440d0b40307041201718048120006d40304240c2100c3e800c1c0c4403000d044528a40342801d9100e10510000701c0c80f4143c0900020714690b16641a81c0d8400b6241001a102c0489460302082a040c25070b80100c0704042c0c4800901d10398410b14000960581e42c1e95031500303003412541c8200c45504a40061402c0c90344904011a2110301b000540381041d03200d030f005109150668101c1440078540e9010541014101001c02c03001c9051181100e81043d4801c0340041d01c0712480405c200b18146e181d640141c800420b100607a20100009200e83c10b0300c0c068030440ea00d09a945c02d041c1d1340e40c1228403500c0c2e0507400a00000d07081400b42402544d01050b010000306204208501500c2101c10003e4a207020480128041141d15484 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 220666097 1250 220664847 220664867
    0xe2d0c0d0506010b030c071e1704060f030e100c021509011503110a0f060905120123100e040614070c1502090a050604090209030609010c1d011b0b07 65
    0x54440341195140c0362601d544642050040c0030031a20000301040600c0091011107140c59008a4000b039505c202c00d502260005001801703441e4100011031007070314a110701080368102e42c090340320402500d0b49038605070702402d410301601082d4002c0051401080066004085450659501a110b0700b607103a0040c1c45000303805082c0c0d1030540c3c5010b0008c2822146107401034152900b203406010412600f40010b01078034802e8109401094060b080006c00c0303a003014210003501d40803a000f150014041d2412400c851803501c440d81c5551070882d02c900c10581c5400344540140d8600001e100c0c8a031100845110210155402c48009659008604c3c19420b82d0b00032940100c5980342a600d8442903032a40d030002c46848a5034118aa400110441d05603103005c1e5010044c000500307640d443d166641403040c029040302c15181c0c0203000741c10024151040c1807048019542c500d4980021880405d00303800020000e083c20300d030612104c0c021509c441803c00b50000360161103031004200500d4060001020304e200 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 220667347 1250 220666097 220666099
    0xd06051203181c05010f0b040f022a030408030406020d0e01020a030c1202030903101b02120403060207020f1210061202090f060d1a0403080c0405130e2d0c 68
    0x50081800b81c2c161003031160725182044425204286804007080031208842e40c0050140d80703040b000002c41415900184403140c0e04a034204441d14031101030b00c080e8441d0040082600c007100181010150100c0140c2020303188150450741841d44440c0411300d1a84250001409648122140c0b4a003e030301183c8451581c8080c4040c00c14501181e801411074418200d0040c07440121442109290303200f0001d56001e40c3c40101142c160364903006000303005000510070400c416120403010881c0500000d0300490a10104122510785071031511200001d411400049a010400c0700d10012030b5520349400c12401c018020141c44208460415001110303460742c04600d84004207551301c0d02594034010b060380d0150f0003c00b102c41c0c554603100095084440d440c00282416052403015a00408190b08548901d00ca034503484a1030b00c03010b41002e228085c1d803261603845968250a03ca044005412080e10340c0401000c498441c0b060014190311030214040048209007a41540307086108100a800a0848 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 220668597 1250 220667347 220667353
    0xa02030619050f010c021207031112030903071512051f06020c0f1e06030f0109050109050c160201090b0301080a0b180303060d0804032103050603072106060b0d060512 73
    0xb02d06004201222043c9034082d041c8507101070900295111090041c0d0240e241c00e0a85244584900d062081001c1c4418120300620002640c801480790000c21200c03010b000900400500346030985814090130998141c104000c01c0804940c6200702c00c0c0106801640f940035002005040407510308104402d60340150210750040300c910303d03180c449285180c0748070020790300e4405001080e210600a222808035160704000000300304100b00319020603441c10780740d0002080c40390f66624211801918804e442e00055904100aa0030901c19440c00000229106040400680d6903034541c440494200340d01290480d00b00c0392148007002035042e0143c4e44000214090030b074241c0280503040d40c9000080040b4021000b0003c180240407080080e03800959011202ca2007441d2510300c0070314510001198400402e0030032011030401e01d00824038000b9a02c0107260100070101c61100824625129541030361029698400803441444070002010101000c41c400b1401c00d2402c0700780a1500f00441c8121a660 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 220669847 1250 220668597 220668599
    0x41401030f0b010504140a05030a06050402090a061505180307150e0910031e12021006080d020a0813030c0e01080d0c1505060f03151b0403080405040f0605090a02030619 74
    0x2a07000021754040e01c0120200ca600703ca07070700c004503010041c503400080c2d0600c00c101c6c0f5001004100d40003079104038400e40c0c9081d0030752911512141594907601604096441c486010280c0e01c0c400d50140001104e44042100c45203111001300e400c09080790070003410840c0c500c520188041e00503a00e4288074206448806151174010003009580006010040030300380071040c2d005502c1e81a0044219581c0c12442000b04007080040180d0396402d00054070a000c1d003131980005042802144020f8884640e03000340c40c071035400d0b40d91200942e00400d11000c0c0804d61803c08008100110040000b42c500b00d10312301c509504000e601481e05080040520401109074484400211504101c0c0e03021000e480020071356844503c0020b000400c003514450705031207045588542c0e051030700030050050302c090b5500c001102c5000010710540c4aa400081c005003002c00040002c0d04050f030045041c0c10a24030001076003174903400001c4001c181070f10f0214065801109000b414500b500d1100d98440045601645207 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 220671097 1250 220669847 220669849
    0x9060203090f0109180906151212090f0603020c0c03120f1e0c0a0c05092406040909080a0e0609010c0204020304020a05041b0809070303090b07060908041401030f0b 72
    0x1c0c815403101d90b014607500e5240c040140d02852150000d0009032541030840c124410307103540100302d6914145c581d42e04281c82580d130607068000140645030a84185030031141c60380c40c0d221030341c40170456180800070030960000306c024090b050b46014055941e40540d0346e034000010710307181c41070800c0385038803070b410590381c20400641050894481200e03580303803903881ea00c41085d0200f00303040074030b038141142e0030020b4221a494030100d102003a00303200d103140060158403101031261041e003c41d0307201c60340b01d505403c440400e80602c0c014450841d009000c075281a480e04140401d66640d842c00301c881c2c00c4042116075115801066a9280c81c2d01584e0f468102041000020041071400d81c0183c042e030323400030108041d92920301c0380c1e1002c2d00d400340040c05200170351103054002c1d0540c00c14000000301b0b15008510381c0c1c403010459038101c03074040d581c800c03025042001e481c03c20790210740201c0303195030f0b00d050301c1d40010010b50190004203500c00030341006004090024007074541e140000c0b00034603c0d04004a0103 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 220672347 1250 220671097 220671103
    0x7140406210b090f0a06020901180f170c03030a0503040201111603060b0105130f1508012412050f011412060c0d0f0509030315092a04051c03030c090602 67
    0x1107800030262465603c03107114007800d050b1400e091035480e010307907440d8109102c0241c00508507810207076207803410320814443c61268074040340100401e201d000314042001c150202d50034074100100000f5240c107a104180000c1c510b80c44100200045200030040109541e04085162030032541c40c4046c0c05603010300348030341c01204000d0000814042d502c000040240e40301d00c4c10b6408991a00f6804440700d0388501c0d226180220324495801107003000d4541515407481001498100d400c010290180860302502400e02521040581c1e01080b4007502e03400c00b8186a170003042c0c0103102113158001d00b54100080680300080c510620703400343e808140d0300c0c1034504000403004e40c1f0150200d10740b9192064a01c528010f440c1c6401c000240905020600400310400300040d40110058041d0000c400300420512420308400c80d071a10311203016889a42d1201c00f000902140707251000c1c2d809203459140e100103105d07510303000c00b150f2088091461040805400d4420f02012840070b0030b086c0d581d40d18050340255 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 220673597 1250 220672347 220672409
    0x608030a080601031d100621020f151e0301030501050703020a1b03050c100b030d0c0201050a0815040f0e060603071a0d020705010c0804031d0904030804110307140406 73
    0x2c101030303a035010f00c0d070307020518108001c03840d00004c1902d812811b6007161402800c07890103802640c2c400c01c034542505132503444d484455103078082c103041e68180240d4200000c3c140e00303501d0101580410459941030512000c0d50346214111101450f44035411406e060342112402415003050601c1001000b51558001940500801d201c0a000d80d14055514003280d060182e16800c00780c40c0319110703c5452504031900024030109064040b544203140e034003c101c030070411001002c3d0210710100190320a261283c408160700c0504054071507003140300d040118007114000810084070a503605507556482c5400e0000755000a402c17401011020f007040c103020050500d038aa088060303a000140031602921903010b45500580107402002410900040580a0b04040342c0890010305490a0a01071510261200c8101e070800ba000c03091582e507541d0155460180a002514036403921500402070343e90401440c0050480d401d107000480c1d40007001e0205445998001d02c0c0b481d4190402d0450744151400a12 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 220674847 1250 220673597 220673599
    0x303010320012003040305011505090f0901060503100b091003020a060f020a08041e0602150c03040f02030a12110a0f030305040c0806150114030601021c12060e0103060608030a0806 79
    0x10200c41c010030050701c040c6565142418032101d00d800b01ca0712114040301500489004400a220200b07004203174005010311401156406103404c00426404050440680d80c402c1c0a0000082c500d0789401c0003a00c1d001d6800c00d140394445d10b4003610040c6041202010350401c82008480c90003d0440e8005028034019000300c41c204181e80c0441c0c22454402c2010801090300040c0642e41c6d0382c1c4940700710000050345ca40255010345040d00001780b11344009840b1140908400200d607007034031106a0b410070307940080c1041e2080c030395030045000503a4051018180b050310030000007544003d50348002d4488200b00c10084102d40151021401240150368003a041c01c2e40343c035001a0b0b41e5a5842d000e5490502600b00c00e070b0074420541003046610300d003451041000c0098941c04440d10440c0a040024442160100e00582220344014141100a41c1036669071300c3d1317400c00407141380f005002c840482e103240d482041041d032160010420b0000360302c10b040241100340099841d25100c0f010240801c0d03000b401346 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 220676097 1250 220674847 220674893
    0xe0f01121113090225050303131a090c01231903060f090902152506020421110405072307060218010e041e05040501021b0a03080903030103 61
    0x4810000c00c510440d00b410b9100e111107480c0d1600d0310b09480082d04200b512141d80110000804600e100b040132900c0c034140e01100071407540d9070751000c440001100742c00403501c0c0d605030400c29101c4035800500c2c034130070340c0c2c980c00405070301042d500010402c032403200a1007a00440f0340030780380c49a40d10360201c3d500d80c040080550340360302e0000d10440c001d00d001c0e4410400720211400124001100d50450240c541c021039040c0d0b40c1d40e007a4641240e03648079003980000301e1286102c2030034803400c0300c651070a94103015050060625640b0782800744140e0000c0c81c42031440c00314000100c208032001c40124850241920b00304030901d403401010340002c642005440c404c030402a6002c100d20b0707480c0220303051198050415500c40c0342e0222450b1301885c06800080c0854600c142c04101420503210300f0300c410b0308941c804070513640b808440c24000d100103001921195001c004d1020110060401194081840d00040c40c41d01c0f41d41c10010b2004002a0038008030360410001040454409040d1700800b590345841 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 220677347 1250 220676097 220676111
    0xb0609010f141e0c0706090e070c03020109050102130302090a090b0c0c0c030a23060705191812021f0c080906070c030311010b04060305031b0a1a01060e0f0112 70
    0x880920f4082d21940d803250704203040d081c01d0382c24102400307800300c003004200b29105903885070400d5540e20032074010034111008030790010703040503c5041c2c000c030040c2c0a4000080c583d01282c44660a80e4400c1481840103084884100b003141041101c040d40103414000070040640c0c55611900e02e12005030059000320404a808514030109108c1011440030003002c941140c12945404401407156034044080d042500f80b602d01e0504022232014406c00403552940d140054002c5030341c0d5142d0920944d1001c0182d00342c00041c2c505103c2d040c5101420010440c0500d0312414810004501c00c03941c641e10448200c0e0480e0014241c000c040b450105038007101d2a42c03188104408078038507000740070014106106075803000080c5900b00102c11104426180248080031003501400140d070050300c0010101e9208108041c101d42c4445071607011000c0b5001991101030745621660003190608565140003c101d500400002d5048602e07140350000c140d41d40b1385107482200010f040c09114080320882c80d41c0301c0742 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 220678597 1250 220677347 220677377
    0xa05040213020c060105041d0703150906050c1e07030e10050d150501030c090815090f0d0f020d090b0a080705041511010b090f13030e040c05030a0b0609010f 69
    0x100307071040e503070401004640b500040d10f400d9983d02c40a1080c18025890454100301266041c564401c14800300002031101c13520710755402e64074000c00c1a81c0d51556507101e00000002e6013501805015042030341c109611403c2c0c0002c8001c60311605131230000000c0c4108150700029801c210f038040d81001c100d92014001c414100151030302e205102498070300034504072440c1c070484844598082503490aa80c2000015040c0d80140c502034010701601c0c600b0ba11803a40751003207100f02d44050340c0c000d120038181ca10507010280014505008001841c020a00c00080302032116810000201c000c0260700e803164009190400c80541481007900305400c0014640c0003035001801380d011100189800e0310054800c9038052001403040d40d100ea4080c0107542441300b110300b5403912041c2e0f6409100040040c109a0702c800c0c26401120040340411010b01c42999509506640c4510a0500140c4683c80c1e169491422208403c2103580c00031a407481001c09004100c1181d0388400d0400240110b07080c1020800800c00d = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 220679847 1250 220678597 220678609
    0x100512100b1906051c0c080405071502280c3008041211030609030c0f070b04060f030b060318010506010c030203160303090b01151106010501020309010f050912030315090f0a050402 79
    0x170014084060070042c80e080c02e981d1141c5154469030184055440305500e07000e5016811301c1c1800e4000059104112075104001c0046034140e82040420300320711a90381c00d5451982d15501c0c0c1d0b0001000e160700703400c20901d500e4101d8440000030310319090703800c40000c943d0381c81441d80183d0080c2040742803100038501c1006142803e503500740380020b003200c14900c0c1c403401d0255240d01041214005010f0303d1a000c044450016403803013682c807041081400c242c18001c0c100d400c1840c45500504041d120b020001241c0c4034400214020400020080c02c00c1c2c001c4a401403d441018120604001c0001d800c40d000c207a0120684230003415a40000d4594003460034101c0107040400c0000c0c2242c6107010001551488070395421541100c070307803190711000d003031014a03585412091040c507025070000c00880c1420340c40340900a1086400741041d13070501c40c4002c0490307c0c0012800700405030303600000c2030003c0458540218001c0c00d40c212828515464503407034a1400850181000c0c0e2025107a5002c00d04560f0380d4 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 220681097 1250 220679847 220679887
    0x90f060f0301052401020304050a05090c0d060e16021b04052d06120a0b0703051902070323040315050408160606031205040806040b100512100b190605 66
    0x10024002c50401d2000e68204076040340c1c0907030b0440744844d01613410394004419201110702c020702c041c0c0f1940c907201c18000c0c2c00300300410700c550610f010010940700c03024071303c101e001805804108910318500584201c41401c005030555082d90f001010003100740c0e61150312401142000d460101d1a80c581c95065443c102d07030040300c00035050f182084928100701c040c000782d1055804030340554803818042000d43d1500b0040401070b10010300840050030240c080e411480d040507412100c0074548900710400e5040343c120100880000700307065040203078404488030b00414002d417600240d00d403500c0c41d1b59694020f40029080c0f030340c071521100040c09000c0d0360815903800202d0a0b0b00d40b800c039105440c0c82d000038029070100f2101d00040040d0300200903c59001e40b419140e07018005c002d551115240c5c40d0026030000d01c0c000b081c5003642400701c1caa48960085880810000e0002e00d000144541c404044e6295400400d000c0c1c0b1030340b060700900e0004a030070035040718814104207a0b40c000100c031410b1072180c8 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 220682347 1250 220681097 220681099
    0x2812030e100c120b0f03152716060201020405011d0f06031e01090516030b0a0b0a0302040801050a02070503070f06020d020304080a081f090b012006070807030902090f060f 75
    0x14102c025403510f90001030400c4a001010b034108a84540c07841000141c0030021441c940603171107110a81c0c640d151618055401900c070075885181c034140c6c041d0945042d13402d4085140981c0010425141c00000000410054122070000794103240c00c0c140000c01d03141c010002e00709400d101050320082500e41c2c0d44010340011002d45916070f2850194071144d01c80501c400181c0c2c5c5182040000100600705225150146007840c00203000707103901e120202c0c0503000310501c03264810092507000070034000e10b900078500d041c41e0703880140c0c0703481c030f00f021441c2118402894501420300401060f00080d402000b2940e4403548041a0103201c5031500700302d8000e000340203136107080a1000003408203021030700c4042c081c140368035070700d203191a640c0154100c10042010b00201740c501480e141806080715940044282c0b00c0c061425110042c6071640d1211003922800900210344c01c02028400720300d03846802250300c201142030a103d01c0da19a0f005c40e0700d05130f0081c0007030702060b48003010440d1907407240c041c41d40c400c2c0 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 220683453 1106 220682347 220682351
    0x106080a0222050421030908040302010f02030d06031538030c36070206010b1b010c020f010c090f030b2203022812030e10 54
    0xd0300504016821a60305102402d000644a001d200740d0003000300804601035108492101420020030030b00f007506161999011a07107000031074013102d03820b203008510342290b49012421801120f0700000d02d00e04020300003051105040c0012040b8104060400035000b04000c540b08010320b04c00700d400d100a422210580103242d040a030b42c3d4a000142c01d07158480090000104d64094048403e03442e504c01c0d807280e142040400c524045900191111111941401702c0d010355101814402c03070740c0203100015001c02c0080d40c0807202d8003414110009101a402407031019444481030082c9050562030310014615451007240000111030102d40c2d030500c03007400d54541d401c40720302c014100d000410b007908100b0800710f80641f0705c0c40654080e0f400781c85170f4805030440c142004a100c8010b04900421040400842d42d0300311400c1060b03105090000d001c0c00d100403c0c90a000214404981c1c4034 = true := by decide +kernel

theorem cover : BRFrame.Cov 220503597 220683453 := by
  have h0 := BRFrame.cov_init 220503597
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220503597 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220503597 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220503597 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220503597 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220503597 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220503597 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220503597 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220503597 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220503597 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220503597 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220503597 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220503597 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220503597 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220503597 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220503597 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220503597 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220503597 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220503597 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220503597 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220503597 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220503597 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220503597 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220503597 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220503597 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220503597 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220503597 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220503597 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220503597 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220503597 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220503597 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220503597 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220503597 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220503597 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220503597 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220503597 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220503597 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220503597 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220503597 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220503597 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220503597 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220503597 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220503597 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220503597 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220503597 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220503597 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220503597 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220503597 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220503597 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220503597 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220503597 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220503597 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220503597 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220503597 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220503597 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220503597 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220503597 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220503597 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220503597 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220503597 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220503597 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220503597 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220503597 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220503597 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220503597 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220503597 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220503597 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220503597 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220503597 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220503597 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220503597 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220503597 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220503597 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220503597 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220503597 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220503597 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220503597 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220503597 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220503597 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220503597 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220503597 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220503597 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220503597 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220503597 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220503597 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220503597 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220503597 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220503597 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220503597 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220503597 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220503597 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220503597 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220503597 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220503597 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220503597 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220503597 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220503597 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220503597 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220503597 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220503597 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220503597 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220503597 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220503597 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220503597 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220503597 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220503597 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220503597 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220503597 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220503597 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220503597 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220503597 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220503597 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220503597 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220503597 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220503597 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220503597 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220503597 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220503597 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220503597 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220503597 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220503597 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220503597 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220503597 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220503597 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220503597 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220503597 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220503597 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220503597 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220503597 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220503597 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220503597 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220503597 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220503597 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220503597 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220503597 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220503597 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220503597 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220503597 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220503597 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220503597 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220503597 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220503597 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220503597 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220503597 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220503597 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 220503597 ≤ n) (h2 : n < 220683453) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
