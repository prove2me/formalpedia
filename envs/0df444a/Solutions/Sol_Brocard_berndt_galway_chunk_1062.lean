-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1062
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T01:04:22.148965+00:00
-- url     : https://prove2.me/submissions/488fcbcc-6c83-4f13-b42f-6a0c57980ed7

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 190827338 ≤ n < 191007194 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 190828588 1250 190827338 190827341
    0x1c05061005130b1f0909050a0b1f0e0d170a02010f11070b01090b0d05030a0c0b1012020d1e050f0606400f0c0f21020d022505150c0301030204 62
    0x46000c84d42c13804d0007615981c1e058090a0352010364022a02070f80355080b5416906007524081c482c18440c0040f20596402d18801030f282c1d000c0d441e006805002c500c0400414040140c40d0a80e00c22140d48c14581c4c0c958007002c009009144202c0141d880c6418103100b00c0d40006100140c45090b40c121032500318591030420120003d0141380e640503005107035042194082503082c405041d800b00303d078880404075143d80c03501d12004240100322a0603604003060030300c036005c0c00c2c4c1801c0c110302c2e50540e9034400301c0e44541002021100e601078004082d89000411204001d0003144800c141810b6004030f9082e5243c0c0420400200480042c031508030181c1c03065035070350b050304007070102e088800402e07590f0124000305560002d80b2444010300e05001e49840c5036030742440d44680b400040c41c900c0d19120403801b40c091641e460000a400100c0465a0085480a480c0d01c05a0440d018203d100c0d020308460301c02c1c003072445600c5400603815681030103070815209d1f080c41c03200c02c46407241c20010300e00c40c5035030b0030740c0d00300310 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 190829838 1250 190828588 190828639
    0x20606090907320301090b01060e030a030503010902071a010b040303031103090c100c0503070c080d080115030b1207060f08150315070216080610060203070b04021c05061005130b 78
    0x2d400c070124a410f0111a2001e2090014881c0218080703221903052000c0036141002141b0414020760020340300c02c2c0070a6000f4180d07030545000420250399034890342003408168045c0800007402c1c48803800005640c684100080084900c6900e00744401d0302103004206041c0411106089036810100200002d840c0c8030748181117480c103d040c48030070400e071601d0b07003855504504003c4803070941609040c42405020445a000b07149c0b18a0040070341d40c100300c00c14040b0700d64001280103040d03c80310100580da031271019200741c054000b011510259075819008020054190740d035004075030200017203864694031841e1510403002c054014055411014981c0c58511070081c144030442c055042d55020011840450314010110000105503c2c01c051000c61000c1603a0b41c040b009541c01007111000080c1c185900ca5880703501261205da01018108800f40d405040c50b070014100d00458042002d08010304c90f100b41a100155000c4050700024001c4904587c412180c869210244102500030202206800c4 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 190831088 1250 190829838 190829909
    0xf0b030c120f0105100303120b03070306020f04051c0218010b120411040f060f081b0d170304050105040605070507051c03060506041403010b0a0b0d050901090c06020606090907 77
    0x1a21030030700d80e5507031500f1144c0c03d81d03c0d84110040d0382401c109056100724001c5560401000410400d030407480009d5a03030b861484010130558000c02d00c002c401007510181e40041c90060042903951407440e114061390300010000b2031041121440c1b00100d411080d940710b05039080800551720300b400c101707054403005d04010001c54801d200032040a50a440d14012080405154500495500d04188d9061071110140c0c01c952456440650b41610b41d032480e04601583d014160b40c20740350030065060080c8034002c0715a403130180d804004140300400c64150700880c8500d0062204024580b107100048407a441201c0740900b00c1c1e07200860144410044000881400c1e03114240001c6180c0d42d0f0010841c0d40d00590f000c400c0c1420b81d50740c20b80a034107083c021400c02c14070032610f60317070080c5c20706c00c2d03900c3d883c050f038100c82e000e070703076855000501c00b2002350b01054a158010300f00442e5a03980300c00c003d545101c2218a113000b42d0880c0045820058001600000d440180204180c04041c00030700c4229501080e400 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 190832338 1250 190831088 190831093
    0x200a03020721110114070c030e04111b060c0a140a020a0213020c0f0a120f0e0a0308030601020f0607120902010c06050901050117030406121a100908010f0b030c12 71
    0x221904400c2c62904224103808030384a06154401e542c190a0031100d112030034000e00c07140e8600b0030410941c410040105268507003410490294001d001c1001011b100e0001103c9000028600710b0711001860f034a9900c01039481140d40c15a00c1c8140d00c03807d401480402070100307003111520002400741001810066080388110703035000e10140c001604034100c000c10001601d60008280b40b5100c401d00901d88018164401020811510b03a110600200340c29500001c010b928002480785038443d42c9002038039080249095031041e100d0070315502c280d1040e078180f4050310038650000c3c0440710103d45144108000c1c0c036414408082c194540c1c000d0122442c00300c0c1000b007180a004009581445002d0050009400015281d81041388620000001c9a1401c4507984140400c000060303004904850004403460082480207100d1324441201820848181d84444142c9690f9a07481c1d01180c410110345290001780003d0b641a403070b000480d252000da81d0703019080241c4414944c244551045005c5520104 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 190833588 1250 190832338 190832363
    0xf131a0f0d091b170106080c090a0507021005100510030b0d062309030c0106080a20010504050d0b06030115080a0807030203090d06090b0c0307050307030c020f03040602010906200a030207 82
    0x72a60508803a58011300d00300c0704043c202c12060340091003004003610303400b0020285042c0359030028189940081c9111800b40c0c070742002850b0540709210a00c2c0004105000340b020781000d444200e5031050b240145801000d80c5c00130b0010003403090080842c81100982445015081a210301015040106007101420060507443c0f501c0e00301d481465110310000780c00340d40c070341e4001e600c00c40c00e544240d400700e5220340c418402103011450689110a50810104103103850881407030040e6524001c0e6805070754048034205851060cc580d0f059070034402c0004038001c0020b004070000d00c807080a020301034420b081e4054070103400000d06000050215501900489041800400020f084808041e804490b83c07078458400e18100442610308903008451040110705610b00904000c00b60f02000700800c0c1010b0b1541008a0118020302088c00c64502c2901502e03035460310b41c200a8060b0018600488003c0c0c03600140c00302098908000c1c0b42a0004822814504030013041c00b00c02070f401c80c1c0c2041d5501190440c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 190834838 1250 190833588 190833623
    0x40c1d0d06060b040e01090c0311120a110309030c150c09011214180c040504030f180b041e120203120a03060803070f1e170f0f131a0f0d09 61
    0x8003400050410601014282d03047c0081d040545000a0103c01814149041d240380d2b11402c0042e158520b258203d00a5513035038240000c8050410600540041a00002440041280440140900b80e100ca0843c1c80401c044421b4000e81d2400b218000420b020500c501e0410f03610a0441602114030303024081b910300d03640c8844245552044d40c41742c0c200210324a45000202d010310800c0b81c070f19021982008549490340b0042d00301c40c1b611001108119a84068000d01404408040040c0c0102001140c0380c6071030f61132840c01912031600c11049001c080b480010840f142100d4419841e0f030140c0900b4103815011084c1d02ca940007114807205040d01ca50740030400001c01c1000c1d0500600507610b4110b019110305003d48200b8400160b040c030b00d4140f07110600403410000207006007200307502003207070380f00c074100d03003160007801008102d00f14074400040011286880541a8044c3c1d07489407102614200c0d0742c8100400e520607035148861244040c018280d0350a4540c0c8082d00c1c1070700a1656440020906 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 190836088 1250 190834838 190834859
    0x504090c090b0c07050a08010902090a02090102030c0a0602030702010e07050a0b030903041205031e03151309020d1a0c03070e09150d150605040c051b03070210050702040c1d0d0606 79
    0xc3c000303101c1e400380004000c18039003000180b00826012000b042014129008940000c40060a10207020740010700c01e64142d108000b21140390700507505480341900c06141240195000b030b15100015820000e04e51005040440c02e8403c48070000d222072100f9103041a070b12400e030002000c00410340410300001504003500c130181c07100c8501c0780d0b01440d075400e0100100800110301c1105034040040138030401c01500101c9510300c90070202103403c03444004002209170042e0484030310094208e0750344543c0d0010045410b40c1042104100d0f4100380340c941d990110307014640021115000051000035440343c0c1e0342441c15100d40c004101c0c48440d041408110042614812850701c11079070b4440b00e826032940c002c1c0c0740c85018090728040342c090100b04404400107206000d08200c807404000782104805808504100700d410182d4084c10b500d00310541c21a000d043da800c00c800682c00341d82010703141038410348524000d0554601100c094110403240b03106002c1d4103800760f641150310b02d54070b850100320122a07 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 190837338 1250 190836088 190836097
    0xb03030307030204060906080c16051911120a0f1103120403051b040209030a020f040204030b011d070302030f040f031229040b09061504090c0e0102010e0d0504090c090b 74
    0x20303520b01583d128604078004080030344030351201c1d08100f084414805080301610844103441e0301d00000c202e124603a414030380d040c0340880c50b940f4104c0f8130310300b0004204007451031070508202c0126440440c80d24001545900d07040c2c04c0e080248440203482d41e880000d51649180c003500200030f4100e03841030007122241c540301d90060304240e4441d800380d031040494032490400e1001403d001d60b400d5050880440109a9071400844000d2240e40600ca40e00352940712a4143c0740250b41203180c1c40790950b541c40d80254840140c1c40000d900505020010341031328000d008990048100b03800c200d400d0360302c90311448810000048100d00b0002c008400d5000340205016030720784103016103034002c0010a00c49070144c5840c0ca19800c98041e5003480c03910303481641d030b08011039400a01a100c41243c080070341715264803407180f40c000c802010300c0c0101d400480b940c403001c9a42c90440a070020841c00c8101c03040c09a960303030701b12071010000c4d10402050120310450303006800784180070f09103100030b5a11171614075480d400 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 190838588 1250 190837338 190837351
    0x60a090302031212060a030b1b070204151809050c0f031525020703051506030a0605040c05090a290a09050103050d0305010e10060c020a03050307030309050c0a23040b030303 76
    0x3198080d50583c130315071031503080001201c1c02c2c0d9a41d07107541c0d03901900c6540280100072550b401840003c866003494119000079900400401c024441d034100f8410940303590040b1485404865080d490000300d82c494042c00ad500b290080c8810902030080204c1c134100c0d19030481c0c040c092134480310450800420071070702542c0507a21500c60b105a401c410050444001020300455201c10420008500301155104101c0c079440110002c036501c0c60701003813902850036801000b10349070800300014010180045000e940703048a040100d43c9403020b8501c261904649820348009100b43c5640c40359410402d2082d04907070240040740500d903119003000440700240d10a98007500905840c0b10b119516100700c50160103056603240c074a0400b483c052006159500401040c030a6400a000555803800c03290001590f020341280e079600103614009020380580e890803621446141211085032810800000c140d4466849240300c2c5a8001c903101308917001a0390840e0420b03074803040d10407242c5040c0000c600c60003 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 190839838 1250 190838588 190838623
    0x2061602090601030b13180b04060b01031802090a150803070308040b0a021303080f040b0d0b04060b16151b20010b0901062007080705010314010e06060a09030203 71
    0x1000d005021600d40c005201904152602080c0130303803661466045403113011403000026581080c01055207061081a0002d840560380b54200400c20106030400712000a00781d030280712a21400b4103500604100340350095000131a0800180107801642c8418191429840e402d1b161035961100e8905540c00340c141600010001e600f000288081980c0c819040903005800b14a000c100c08640c009041d5913001c0240a1040000d0800b6022403000a8801800020199030307601c07a10650002c2c0246009007841d0300543c1086000200e182020b0700791074001c220840820061455682d6a155021002c9820040d090f500c4071107000c151004c43d900050081e698552501c82d4021446101e4500e000d45000803850303052110203012512070516440c1141e2071414400760b40c6001310700090005100c985142000d03c2141e4000a070340b40300040c0c81b021100217823404c202d601000c4081840d00f08003405400003c850044c0465071504011008000d00407844c43d02e9210107890360b001a0030640c800300d0240084 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 190841088 1250 190839838 190839877
    0xc120a0b04410106080603011b180b03130b04060e07090c020d0f0f0513150f170c0a0c02010e12032106030604020d0c08060106050d050601030e25120803010602070b040821070206 78
    0x302010b0050740900bca02001038117601d011300c0c1148007844910801400210300c0c1000c98108411500400b1041c03451400b030358015030710750b41c9440c01481510500303001441920040380710030340141812000200e480c2e40742015000ba441d000d44082d480455180044084004e0000c0e0444182c07810295543c1c6594400c090849001da0041074052200c44103005280424140980620910115950480b00d070400760082102c5000513107031160f60004140c1c109100c4014400707541c00110042c48500e81e9000512a00c40550740041c503100011107900340c0540c41040441d01500c2c0425046007a14130600e40401426156040325040c54803e0b4401d0000c07800c0450300301546c21690080340d034080003e180410070300500a200313650710001c00240001391091059519800705220b4607135001340c0a80340c100c020103100c41c1741600b21940b091080c035005006035200800c0030407119046408440900004000c4454403041d00301c407011a4080c02103101d4010001080141c40700380142091a203040c001a154 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 190842338 1250 190841088 190841117
    0x70b0a0e030a09050f0a03060f090204050a0b0d17280f0c05100b0a08030403080c0c10050403031202092e0302030c120a0b04410106080603011b 63
    0x64403240303603100580750014841e42202c180d120302e030402168000c0f81d0131209882c600c03011400118860308060000e80c140901180c00054a42298220500c01d0702c040116568001086048505c0002c0c2c00307522040d00d000003c0418002010b1114240d81554030f14a044100b0420800c095410344408510440c40d403607110445812a07041000c07000c40d800e298480203550341d50a80c03102600c1d40e005924542e0b0700003070034240d00c0d1840b540e009003981c4d41c05c030ba50380e544a00b4040d1080d0081000e80d202840794445e03c041d28201131003c0090102d0a17200e15080a0541c2e806942030500c180903403886590a10111545503180034055242441110f40c3c151081540394a198100400880c80c501f414010000e00c464115550200d404508260134074020b191a010820030151003100031f80c0745c0c05410b00c82103060036511410111031110282d10900a07101e66000c9a01641c22400720340c15910003810b00410a4134002c110382a8071a1000b00001004000055564110503200c20000005807119022020 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 190843588 1250 190842338 190842341
    0x804060f0c02060417040f12030903200a090b010f110312070908010e0c0a170c0306042108070c0b0915160f08010f03060207081b06040606052e050906070b0a 69
    0x1810244810b0443c40d2500701701410301f44c4a202e01ca01064007602003004c40c241031280c12203030040e42d4898031404400700c2d80f0010070300403c641110035210f5481944c0015560b00071384191161200b040c1c40341c8521f804080c070241c42e000b50881c001082070000f040a48940e07441021518410800b686600207413a060180590841f034512412102a80c80f180070001250355400d03030b23401141c100c1010010300082070306e0040c2c1440c252460050b05881f402e01840304002d20140c00350050414507140006011a050084552901c00d81d0268041115010348201190740d8410b4558400c9a40b0200c0700c5440e1581000e0218010895210220003114066145001e03403191200c0340150f4075141542c2194103010030015007886c2488020501640000c44d00100008102600d4010041c12600d0301d00c1303030560742115225103080302c0880300e0a161030740205843ca001d201013040b02d40700064161440d40418144030701001200300180034401e09000101503036403040c001b0441c03a407285417146a07509042d0710340300 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 190844838 1250 190843588 190843613
    0x3071208090607091404140a0b120a0c09180b130507050a06080c0a02150106020a0209060409031b0809030a15050c0301080a15020913150f0b09010804060f0c020604 72
    0x788a421580074400c2d0030382e200f00100d094403100302545002000f8000001e00402241d40700000c400310640c108904144154019000024281c0f00321a07103103030482e0843d490741610746000303120039444002481240c440e030b4802d0b070303c91104190b121001c14058031203c0c2c04031000c07118a0100015102402e00f0000103102035030080c00c0c00d40f100c1401e03505185019219041c02030090b40b00e21408507284180c0c901c2005180c40300d011755040540f040d41c40c1c00c4000d455000d025010b03405084018041070b000c1c01e00c3d12580c01d4041d0980e4601310018800d0107001d49090213240c040d546260b0074003801100b035070107000d42c200142c42600390741015403120001d40305403607004101010f102c00a000401c4200004980c00f010140e02000e41540c900003460410002c0c09032412094010010500303002004905a10803284511081c05151005984a807041c12640c06401030b030710314010501c003074a100d5000f5080b4680092240038081242d1142c44043c404a070030180400380140c0c010010300050008818959 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 190846088 1250 190844838 190844851
    0xd02130902270409020a2603040b07080a0c02101706030705090708090106120b01240e040b011b060902130903081302011205070806100c020f04090f0503071208 70
    0x640c102002820b032042d0a140148080030318018011501c2c4642c0d075154000144540d0091041c41e000f5100d001145818100c440240e01082a22194030a14840001513500715040f000956107082d2007075890881035000359030032400b4080040004401a0740325003a40242c001c03565951854401d511030031186007000500300a0280d00140c0d03061226407181c01c40c1036484131440c00c1110103511201c400500401c6140e011000f0780d0703051403010081014284c615070407512004035030b10241840c00c00701070348512005424400309000e030424402c03034185908911004d1005041030300da506030000c4c1950b8845c0000c001254900e40e105109021803500288072170660307030a410f0400003000703146d034003900e03a5001a080300c0f8107a899940e4202107a05c1210701b01003681311140c05025605140c54040c00c0003030141d40f0380b403150619400e401c2200744207114625400360010100c2c0c40054010b01448001c01010380d00b0f070781411140d8810380114108000800040384070b000034a4500210301001030070050050101c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 190847338 1250 190846088 190846091
    0xb1612050108060703090c0312021b09090c0405091207060c1106010b0d021b0d020a110319110f06040e0103030f0306120605090102131d01060c240b060d021309 70
    0x1802903160029034684d2003943e17420300084070a81e0b400c01e00c2c0700c2d03115030348020984e1000040440a080d4042078124010250300c41400c2141e10350020412194030403a081e58056200719041038407450075400c4640c000d00d00c4d81c10b40350f030b22b4041c500c0d055155124100c00e036102a11001d40045c60340d4402c10414940107520040c1c2025410a0841c2001c0d2250750407804903180c0100e5980310031541002e08001105d40f00d03048403807900302e114000c2d48803d20403105840c0840150341e110210704001c102903a01660400820104a00959030048506c07001805260004010700d12100b0f50341311040100041c1654181d928510340c91031800404411206402808150500e1020416040700240f601c1c9580ea0020020841da80c400006500900030300c145091403150800000500241d940054448040e420401440e280c0e2900700c1500c581d01e241000921011511117103401141c0c03100e41da07083d203613030100c0045a0b8060260018107280c00c8490040d0350198001010340b0800d81042c034940040c841c0400 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 190848588 1250 190847338 190847341
    0xa06090509100f06030905070b070b09101b050705120301180507020109030903021e13020a0201060b030c03130302070f0e0105040b0a0e060f060409060e040b0a05010f03030c0f0b161205 81
    0x40c02030000c025413003150180b40e1602c500004009042c84032002900c00c8104640c1c0703039550350410503000e0340c09480c08401c5005001851076000355500590b14240c83c42820409800c01c0a1000c45181e4450300c42660b040c0201b880030544e010b80c1c800218021f00445413005504989030083c00102c0780b025009030305580c5440388440c006900000346008981e01101c200c2038180078541e035200310030100007516a101c01100e1054501045c0c903400352078004040d5008125180d21001e2102e9107100c25144421295828400204c03000300020056070000d10a2050711211071b903522004510220a81001019280c0100103010341c2c01c00344540304400000711800c2c5502032502da008039840c1b40142130140200780c00d540800d907a0f2510310445008202142003008020395507600403402c0340040c4c6084071401e98003008a0070307095950183d103040e115034640d807404140c51554240da1011b0401c00841d40c003041b04c00000086052105100e100c4e420b07005400401c0d141440380100241803651010084518000 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 190849838 1250 190848588 190848599
    0x20c010c030929061e0a06050a0e0d0f0b0402031f0506011e080106031d1b0f09040506060d172208030c150603011b03022703190c050a0609050910 64
    0xc6404d030440420340c1c02d0829280c0045185682059503408180c11089268001556650001c010444204540c1c0d40700c00c00e81c01a410003007146900080034241740c0590f40075001282000c9030551704144010b04803103034801b600c0113250504849110880740306680c2e400308191b650f00081112607030166220280e244180c1c3c51400f5002000602a000400d0350f42c0740d02c07600d0500c1c420b00711914110402d0031180f0b141f654040324500c0c03840482c11180640c1c14400e03060340b5820200149401541e210003e00142d0f6213000c240481d1040040e01510342d86a0040101049a0120020003080105e0300b0010070301c0e000441041140095136200c10f005034010401240074001c0420540701106e0840b00306602e64440b0b00010b40544080520070313850a81040c00c8101054156005061030507450500f0a10721018420190782103031030085994042e00500006d10b100c84031044101d110324441c26a03070200645501c00310f034000b1a143c02410110750324200a00140c90199003141e40011a000c0c694402410301 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 190851088 1250 190849838 190849913
    0x6040506030615010e060c161203020a030c050106050d11030606011103160804030b07090e0a061805060406150906020111030709051c120507110306091f020c010c0309 73
    0xc0031080f03403041c1440014040d80c46100f4030700603000000c149646591516030495202c40b098211a5030213601894001001d015028400741c2e1560140c0203048041a1900c003644c1d133081c0c2406c102c074155681d0001150541d079014a40e5090b078018203c0749010304032281454900500a003140e4144448051008100391002048983c040e40d4411600d24210395807614895074051038000520401840d0304000d0842e81c040e84039012501456103001d0903444000d0041c0071100c240c080e600040c1c69045503806044955000203401c01c1c009400000d1480c0c0e5500001c0c510018146603000003207c0460401c0815424011200b109451110441c518200010041c080d190984282d42c0208040e01c01490003100c90546c02c0f2041b504005002c86080d04604014520b03403011800b12201c01d800940f9106505000510910483c0542e005040c0000320000070b1600780300a142002d0300710340800c2180246042800391600f001d0454401040300391240ca45102c4445940341c0d8459042032404c02d42001c1c0120 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 190852338 1250 190851088 190851091
    0x2060a06140d030e06030a0212071103042d06120c0302090f091801140402012015180a0506060f030d050915040e0f0105120c09062b0c030209060405060306 68
    0x1100d0302c98140d945031800342c604110400101da40080040100300700f16550780c000b801079030014010800c0300d0b07030740f0f560690b00e46036000008206c1d94010301007402104162091500e1001c40b42c0074400c2030740018990034104099a8002c40009174480c103c0c4034840030240128144201182029803c140113880030030800b90414806621401c030203030200d80507200f0740c0041003401c03081400030302000140c1c40e0390b102c3e51201600d04030700060305100840c00d01c41c0340c0c20501e0651240300018202034010b00800e80041c1c107010b000854a800c125128100f82c000030070402006c0780c4038101815440c03500034200a4080c00705202503000c5c0d00701d41c401078200c0782e2000441e1540d030b00407684c0f0a0350420800b50416280600c1d00403082245c0d000b01446070403002e40240c1c0d412500d003141c852000c01100340301076494880381c103a40c3d5000115880415010710b40150381c5a04600500700c4c40c2405000c0d00751001c0c0444211030160b404094150b001d1007036081555845034031031800e0300d06010034140000480e903207420 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 190853588 1250 190852338 190852379
    0x70c031b0204110301030b01140108060310270b0f0c070c0e04080f0f07122a15111b030304020d1115030a0e0c03010e0a12050c0105041202060a06 64
    0x41110560045540d9503003d1086001c2001c02d00da103940c1c40b4949443d00142c203004904181c585d4101d0400c02d0b41c81411080d204000c09800360140e0301800803100c01500a004141c1d002e510120f401c00c1c0c43c01c002c100d941480c0c078018150b021360ba0410309150703111044090503145214000f0099800820010750349503080f40d060a404c80aa59914182100c0c036005144c10040800000584003038120b0460b0040c04205000b092003031481d00078a403045c0c40d42103a202400c00c0b418a4040540352640c0b6102008070f080b8080c611100340b00121307010790803c64186100d402a0040081401c800c4042820a10b04036034401000451079801d1035000100c91844408008150200c204014400d98503602c0080d81a82400400507031282040c2580300c0203001807068428007442031124401091805010311102507001c4406481040c2058a8255841c10202c1700741d030500c4020420302c140110244141c07071095014149110007038400700d0000381010300c05001c9025aa0400d0360601000400b45030559081c00d = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 190854838 1250 190853588 190853627
    0xf04030810030c1203080a050603060a020c0a080d051609081b0310050901020301090f0212010501050306060c06010303210506031e0a080409050a0b03030307020a0f030905031c08070c03 81
    0x355001840c0607008980c0e0030080c0b48a00c50301d0002440d0062280003400705120b03844401c0301d84d40790000c56046030f9044580b9941a0700000105120b0110340e4020001c060815064556040007900e801000754444203120000550b140d08200340030b0342c0c403118202c0d00300c0b207071424190851401c10319550703480d0000300c44d4204000e001c0340149160b4042000e5643c21072403540034001032501481c518003e4200340301e906441130814000300c0c03070180b40d031003250710080c1d40c2d00c0c0a070000c2c3d081000444641e00024031180e0403803010000088070060800c01d25000b103100b50748610010440c8440d041c507442d49540c01c0c121841c106014052607a40201d030400c200014a52602258400c1450861800c080e111014104000005010614203115000300303100e450074030b070103000b101d1382c076030606070313280f108407864001600305540010004003590182102c040c0286000c90507291103000190928078031181c80d5040403501c0c000340030340c82e4000b03150b00d600c240a800c140d120340c0786984003c3c00d07850601d0600010039 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 190856088 1250 190854838 190854841
    0x305030411010c0f0b100f0f03060207140304080c130902031b030715080a18030f051309020f0316020105010602070b070c090234020612091c1808060f040308 69
    0x60f4031641d08948401e0700706414007124a581d0500c5541a4800d0307505a01400603641c010130002165007440048034061890910010701e103480d41d000a400c6204101c0d20f104291175403610015081014201909030380e80a40140e40321101000808804403401c0c2da22a800c1c062114017503030300807034500c10b06021000c08904001c0b0341e100080c140504c54021210106881542c909540d82c886500d03445850001810032114a00ca12590380b07003001220300400042201940c141b5491040c0b014003094030012a403811030548035034049083e60820424548160004402c000001100c01c01c500010b14540c00208800c0d410814025151300c40c5002d44010400e0000e0110100909004406c0c001e0016040854640b0041d460000481d60705203180c412018400c071500e82584141c610040025500414451820500305010224500c0082860266004580c0c82010b416043c1d6110040c04815568945420009207182c0803003036010b800225031940b0100400417a44000c00d02035422503003500782803071035 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 190857338 1250 190856088 190856123
    0x602010f14060405151908060109020427110f030a15031104092604051503060f0409020f0d080903010c05071e020d0c060f1713021210021b1903050304 66
    0x2981300510709402c0318000c983d901b401d068402c07003c829110132105a82899903681c002109900a600070221005406c8c001c0072040f41016400c0207405040c0d08003c0340005440e00c41d4a6540c10804803410590b13800002c20145c4206846441d60910680c14080b05050961311031002c018009049a802142d480b00801e09009040300301c0d012503011414070b8001d143c007002070000e85030001e100b10b6015030444040038107945061015603110381c0000d407411000100050401003e401c0c0301500f40d80020022101000507240d04800c100d0303a60240002903034a00d40301c024942100d18507102201041800c0c040d641c0015109241100c001c40503003411031900c110380c00059050000c0d440b00030b124000d841c100241c1c007604102e4404900c170040c0c03180c090040380c40565490803942129150000300680d02e0a0006203080da0f044030301c044510f0704903003840b06400c11900c04c0307901408210594403610325003540c1350401040603010f103100f8505240200f40c0d6543d4080c1c203d000c0508003c10f4164042040f842 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 190858588 1250 190857338 190857361
    0x7050a0314011401030c0f1e140d06172a0a0521010605010305010305030a20010905070905060109030b1302040b10030c0207050603010518060a03020a030506010602010f14060405 78
    0x360011403001d1901ca50352410300786144042c060050380800d081c03810000440340101c82250040300540c82d1108024042c86d0f107901d00c000d50025070421301901c590305402c450101c0c00a0404107107450ba0004919003004107001407209001e0200c0e4843d8030072122002c0d160702e0880c154116588401010424855070700000f840c1c07205075041260402e1094250f06920840d9a40200c2c241135000000c010681d00c03200118242c43c02400090920740c800c1000c20400d40c42030f1440c01001e042058068400b2511040541c20341b1100b80d015242d5a00c02074003407015585a118840d0000403d080a29050b8038503910b00d62240300050116103020f410694000a42d200c980014400d108004c0142c0440340049001800400008403584014810f61f500400d0030b04022007120306070340b401024200b0844812680c03c00201c4002d04007a00a140001d00000627121691000041d41c80741000c0d000942c1007010007402c4888143c810030825090402c0f410b407100210b80743d650000d000395404120303a5984050440e = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 190859838 1250 190858588 190858601
    0x12060f0611120c0a061104060e0f010306080d050c2401060c0507050604091406090702100207020409050303010914070504051f1b0803072003030109150305070306050105010e120607050a03 82
    0x2041060015803d00e1041d80400e1661404d44682c000700300140400341a0001d030300850007035401041c1242140c40141c5401e80030700030703903903014580400c8a1303448000050615100c0c82e1031001242c0c010401c42e1044800b44031200d204030144158002902e00146105d02113441842840305008400e1032040071310034180318880182c03002070502552595101c400358000d20510940404c1c400107880840c20610341400814001d040640c001c15090501c01d0309207009601c616001c903442640c0f000b5150024001f840994000c0a0340000060151994603103103105240041100080207820041400659240120031381c0e0500103243c2e81d04c01000165040e20f20305411504184410a100091410803d51500039032040c42980e9501c440940716141ea90904001c1070304a00c072a0300244010b0007013440c00c0c0d001c00280b0844101c01c008080e03403521802d0410180350019104542c6410041c00656046140080ca404060701c00840c039104484800c0d0f1a2403000e425501009800140d0220b118420340028 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 190861088 1250 190859838 190859863
    0x170106050f120709030309060809070302091008070e0a06062a11040207141b010c0b06010509090403030e061509042423070c0b040f081201060e0112060f0611 69
    0x55540c18408030151010040d40300490014620031008100c8900c549c0708c0c0da0243d620b01c8001d2008030708603030030491070400040142824100000000940d048200100c01c0181840400c140280c1000e500076016100150085024080800303400e0050030500c48447d280100e501103045200803a40c41c0214150351041c00080e8414004180341e01480303503d90744611504040c604449030f03220707a5441100590440f05005001c070300c1601c0d021011800300c0507503651000301494154907140350400041c8000000360380650010b503840d091040160002c02c6256005094200083c140d44100360010340c8190000b040205100403a00020704464101440c40205c407000b10400d00900e0880408a903c8a0800312503410521600002c241140d00800905a4460304150b94584550710360301c50745103070301d00202c00700c98220b01002540440404260024082c01c00c5903141d501c0490791200041604001d03544489440c1c0c5800b50030400050040211030498079541850903418201e107004a00300b08941691 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 190862338 1250 190861088 190861117
    0x5010f06052710180f080705060d0b031608011107200f0303030109091a06060a0c0f021306061e05030112020109090c02010b0109090605060d050402040e100c02010c170106050f 77
    0x11000c1e0303950820000500c08103013074250390301c40d03640d082e0003900300c103051203000319a400c5440207012509082000300300481c1040001f0500300b0540011038602010784403104c550000b040170600800d04203004880c588503441e001d0310b007003403a151600f001c03500303e21a0684803e2041c080c4041c0f580c039280364000445c040103084c1c903142e6944e001040b000d0481d61038129820611f0b400c409030303036185400f2690b00912015102a040482095003680c85031000c06042e14055000340d02d40d001a81c0307007001d400f0440c2c1c2100000c0b070306524080000e40701c0380003464140109900041d01c0392129611200f43d078110744500032030418840c002c3c00141d40d8040f40c0e812a54055040c4403042d281260150000c3c2501c42003a038801000076500d403c0c0004403005030142071707885103040011049078a1250042500b01d400240700080111020740001d25001c104100344500740e4994040c01c42311902841048208011414000741d02d100c001c0041302c4000050007514213004002c20300600130b40c10b541c10303a5504400c0595 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 190863588 1250 190862338 190862359
    0x50405011b050a150e011506080910060603061401052b091e02010905010206090607030b041107030c12050403051e0c030f0c09100305030a21060b070605010f060527 72
    0x30200390f440e414130b0030542010f09003190800701d00014410365002d10341d501151070a00c1e040c54000c440d00d14014140c42d030310780316443c0142e401c04450310940000f4422918002a0340d407600002c044070248038110303181401303030030722100b05800c0b541d203070200000480c014000c4c2000114500b010040200d2040540b50380301010080d50544078425240510b00d0007602c92a0250b0340d500012030762604121000700041c0c0245002c15125030103504400251034004002050b101c0e04004da001040d00103000540000310b06000350010700c15251001584680b440c0344c0113140500f151103a9a4544181215810711580d43d11034206004083c000a05902002002d0350700000484a00e01c2d61a11042c8480e403207031107024041040410505140c1c0d00301c0394440003650030010900c0c4c080c1d5500c1c1070038132450824410b1402002990300030b40300e004050031001e490191035800034140700c012150705030019001001c51035828420180c2010035980d54019405000007243d90110744541203104248560350040980310 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 190864838 1250 190863588 190863593
    0x8030f0c15070f0e031507122703050f0d06030c21020d0210020f0f03180f09161b0606030318050108070c03050c1506130c050405011b050a 61
    0x60042244021610440c0e07802150200380708a86482503400c0c401003020000c1100100703000f54945401850000c044e11a1845041d03540000030b40d0480c0c80300300240360744c030800117072031000d2054000003240400301c11195001e490744284c3c03021000701302800380f10000c181403100640766000c46601c15482681030003126524035004071040890702a020f00c0c0e601041c5111111100300c0403001d201070300100610340000840e02403059000d1072850f20021030150345103000150804005040040403d5002140d6580d1003142c5015113140015525104198240019030242d40c0c48003110b400c51103c50f007483d50f06007000c0095454440300400c00680342282404501440080e40c4130302d0847e4045e441e00c0d070b081c9844045207201445076004990100710309c44007003070f88640b08030405080b0701d101e030410901d0600c1000c950b074541100703140b107035240084d0201000f1240c00d1102c180480009003001c20300410080000145c014040c40c001d10b410403841b90075401e800070001c4c1d0150f09054101080d101a602c0721f0 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 190866088 1250 190864838 190864867
    0x3010b130b0414150315040507030f090b1506090a0918050106080304090506010e150306030c09040b1006050406051c0902060307020d14091c020102030408065502040803 74
    0x3240004c0c82110580c1d00d4a2140b41060200ea100d604821440011800c81c00104401440c019004008041c2e807248030208240286c4a000000c0340640d800002c0c03441c11001003d900030302d48240f40d002e10001d2044040e1a200c24400c0070950320400c10200b1564011114403d1100c0c1981001d40030b582851000141c8010210091095074480401030019660302001520341f0a0303903191440d008500d0183c0c48090303481d01006960402401000e0300c0c1c1207490000080c2d0b00070026541500e0204285d400e02400030400c0c03c1c150010411414548d080518004c4081e11740c5c0076010640711a1103000e440411340c0c600ba82d220006541d8010f01a544070f041c086002540e070000c00781c001d4003007030007400380141c3c00b0000001d81c0d03130544001342280800300340c40803074511044031641c04905502c410700010590100034461140b064001d25580d2040c0c0b14002c3e0b0384400c58824040310f03175001c4400300200035030ba00e400207501e174020048081b145000b61580004c5000340310b02d5101c00014003001c951011030300d44c103 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 190867338 1250 190866088 190866119
    0x6080a0b0408090f0a0e1b03090c010e060405151903140f1306060b09040b011e05130e07020a110d0f030e01020a050303010605040f0510020a1410050c0306030105070305090303010b130b04 82
    0x207003140700c0512058041e1083c508c0300f0344100640e548090040c0150b90710980110f81034200c041d1260741440e9840c8081030920004282080c01504081003c501100340c24401c4041103145150510081d800c4008940761040302820950034140d411001901e118500c44140b4907240c0d0115040024558035000d074150703508030501951155040030305400e0740c0e43c450901c004031540040440440c02d403903541c040d183e640c4481c40010055400c00e1000075506909105070b1300c43d2010323401401c404016850314107181c102c0c800249115018449181c4085403420f8540811140e050911109004c4000d0060b884d00c1802a0024150322000001095103940074010300101c1c0c90003d00b48041d252201c0411030318110711042c2c8001640f104603e0f41c04240010342402031b003d403000c1520600700d070b00c543e0102912402c55060030010000400d22203d800d003480b803a40d002c4440c1c5020402400d01f4801d10303449210600c101c80c941e100c00b107802c2d01204100f01502c1d00402080d1022a0744170754441d0003424050782c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 190868588 1250 190867338 190867351
    0x204030302010e150c09010216060306050a0e090a15020c0601030c140d0506070f120203041b080105040c0e07020f0f0c0102060c0c1906020c011e06080a0b0408090f0a0e 74
    0x24921843d00c0301d0400078881000c50a440d051005680d03540a04482d107800071002141140304100b50300c2c1c550103c0d518814040c20160360041941410318050001c91b1405a01c4058110214001c10044e6a004121041045e0f4032950044219000c002414042c0c020036885000c540251000007003040f0500c2c030300d8800c4501400c105480103242c241088403100c41080b02600c42e8001c0d000003040140b013610003425004070b03810801141a00020131101300c0c0c004aa0480700030b44003035501114880c14040e000014802030000340311a1500e42d49207a031841043c4145214040d588001c222260b000740071484645020702d04076800d00d411004a1940d0399001e1325444e0141c09035001040602c5c0042040307844440c0c4504c001c055040c0b484090748001020400185d07080b42e424000d440100380203000382c25000426054074021000f89040000442d490780d03200c410141d100d008102d0001b0b912001166016402500054403101d1400100f0105d00c010120245c1c811410310b400710380301c0a603c149502488 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 190869838 1250 190868588 190868591
    0x5100e040f0c0f020a0b2d0405101107050a060c030209030d1e26090709020f030a1b14090307120b040c12080904020a09150512060a0608061005041503020403030201 72
    0x11009101079865444907007020307250780c6d409800181500d00c40e1015015072104582c0c6003600c40c2a81d00b0b008034201059501b15141d8000949200c203028103801002400b1911940c0d140c904841c1e50b45c0c03a82d40c7c08440308010452074480558807102e5000ea41030b1106010081d0640c1c1c00500e0184c802040104070003440c031942c100e0f40c07061240492140e039039400c88500180e600c1440b04000718096040020040c200300c0c0b03502c242c100201c1c0b03504107400688003079000c200344c850b1641880307101d070001c0c2d51140b84010b90b5041d805020441207540500701c01030741000340c0072880d610b11140c008282061450341010080b40c11150844d001c003c900f0f03c1c0309100324002c003000d8214945410212802c0a401080505540d2040c449000b040c50940d00900403600701d03042000b405513460010352009500c12a407680440d0021405802c6402c52140059010000f1103090f41403e09148003e003280c10050f11440c02103107484a100385407401002220050200120125801030841000801a40c06800100c0055 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 190871088 1250 190869838 190869857
    0x801090b030f07141c111c0204090c181b1b1a07120e0a0206031306060e010f270c05070812060a060816050c01110d060305210405100e040f0c 62
    0x40903180049284e5980b00350040009006c807020402800340410041c0f000181005813140141c1d07a074421200c00303c2c81550f40f1044035207407591010b0508217280c0c18110003400c1000c0920f004030000c43c11681102c9030b040c14a5485101e1015071120003c0d94801082030002d0084c0740000b98400c0492485188103135105a031143c4212181803d0720b1610072031059540c402d04a880040c1750103409154440100c0c5403520b06010303540c40708420344000f40c1c0007900160901d80180b00c3d1220121038000a0b221103801d50300090640c40d2502c02c002c14100840b01a90341c0d03001d842c911148201d00b00d440305508018025150018140071884001c026942284144c0100c4800a5410700410103031703205105035a0b43c068011081c40040e241070744604003c002956a40f00c0ca0000002d200014080100104800040c44c0b070851511f10f00c0e1006842d0f0002c0d1910b13560314180010141c401c1100c0503140180d9007aa2081c070101000c0c0c46c0c8154008110303600c11304090390001580010351000b90032000030b548107005c1 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 190872338 1250 190871088 190871119
    0x801050c18100c020f060c15040203010f1401030803061206010b090301140c071b27052a0708040f090c09050a0b1b030903010207030207030b060109060801090b030f0714 74
    0x804540b506202c0c046111602d25201625041801c101000360107000c080c0380c8400c0e10007181c2030200d10341898000b20035003824001541000d10966014090f204020440c4c10100e00000070390100502c001001305800000042460722184508411010302c0400c071051540c48072440c034517039040049118040d61030b104400d00c050100c6806c950250381c0c0310500920706103064540803078282a400400d800c880224400280c61019884019404400072600c2e40c105000c04038010203039400a8108000c03011202400d82c46000220f580140144550a83c06d80e6a0158130781032800b80129807000c00078080c000400155002a5001000500f1150380c6605203182c852080244079055070040240c000814040200074000001e041f00114480300104c0342425080000282a41d000300d07022401a0040c60f410010084001c004581024090a0100103582003000c0202035581c1481403001040d2076404048041d101400b96840b84600314003502d40040e02e42500c001c08114a0780458082d400c040c41c1d0101 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 190873588 1250 190872338 190872349
    0x10e1b06030106050a08060a0b0a0f18080601060f02010917070201120e06160903080307090302100503060303091c050a03020f0d020c0d06022116030f05100303180801050c18 76
    0x1070324101c4d207a0300d062440c0f0003c11621071000601b4290441c1407004049520b00c8240c01030603064415560702c071100c4000b503c0c001c2860340100b01c200006141b04509205001021441e203040d10460300c0c1c41c40441d440d0300e400300c0c09010092000303020340756500c1e40316a1450a502c001c2c00b0060007030700e4102c0c030084e158198100700c071016004401070380c02c840c005c034034890440300d440305075030b41645040102c0d2034498503444606da00c1500c506000c141001020421401c02d982114131780303c2641416030541c94844082503ea00c00e051005105a98100070010a425171450750710310b00f41c20404480400030580340207551500345040c050014407903044003d024500c001641001d400e4040c5c500c02941c106603079440040e40000c0c0c0d50300041945504804c0c0c0c900000981203200700350328034140c150f1001001014040341c90300ea0405c040d036410b080802450b4400e41c0000c6089950610345081c6400c0c01b04c1143c1800c00032a00100c42c694280028030540e03000100140100241c1250000f0030784a0f070604022 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 190874838 1250 190873588 190873591
    0xa060509030a09030213090516050307240804020d060f1401080a05033403090608070504060c020f060f0a0e040605030c0a09020a0302040b040303030c02100501120204020714010e1b0603 81
    0x5070550001380010306100d07480c2d45d500c801c0c8020100341740c1c9150f07a50034240304a041181c0443c2c1505501000945401c1014034000c1028008501281c20300c440c51034109205030000380144a00280418210341320180804466074101c00200103005a0003c101c0c09004685031070081444218000304900354003203018000c00780e00800452614081450b18070781244020007034041100303001e405108001e00241d200200314400c1d41c81301000ba042400141c41c8110281c070810400600b440103200c0c443d04034030442da00980403909040d8540c81c0c6000076210740b0615901a0b1b60a5000c11b01601841c0c00445500c000241140c081c840561103800f8180c0d035607090300072941d00000002c01084013220740e0b030060040d0200d5140241c6050f8031400c82462581c0a030784201d00180c0d440c1d04103005280c0c14003071410b41c0c2ca8a00c6041c002945002c03c10f4204c1d840b9900c020740302d15800502c030b600700000c41c0c18000d07915042000078051448450401c41d19804c04505441c003802c03944030410784514108080340e = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 190876088 1250 190874838 190874857
    0x10905100302040908040f080f060a0605010c030e0a03020411040302120109051c03150b0c060a060b0d0e07050a0305070e0106031506030504110a150f050414040506060f0307020a06050903 82
    0x104441c0c9103800304405080e070158240c41c0350380708001c0880c41c03460001000b40035204210042603020003041070740f498000300424a030141c84c03400c0e8050150740e0380324011400640e01440e0a40903254042d00084413519690300c025171041c079082c000210858442c000e402142d0084031031070380d45a1a40b13600ca09854076100014069001008614a1680d515040000c0d5044519001030000380c22204040410440e4100107846100412081d10884040181e5584840c14038018441c0510304845240306000707580303450204a4a03074802c001d042008000703010003402d00038079180300280d1364144251600d48034080d068112003800000b00d481c5010f801192121440c10700c4074540241340c080218005c11014000700e4002014030101c01182e601c08819038068420005c814580c1540c0700700c045d02902c400e4242d10240320090104210080a100380070060500c1600c010846a0380c1d0000149944103188454019000c040144081642d0018804003400e101c2c1000304429102d0354182a07881c010817041 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 190877338 1250 190876088 190876111
    0x105010b090913080a020c0f010c020906060d0e01020316020d021501050d020f120609011d060115030b1302030403090b0721020c060a11070b03010303200309041a09010905 75
    0x4900c140c02c10b0440d481c0e2201c0c2c806201107041e496691000c00d43d90015042c1c50041e4000707441101c4618088100040703004007401c000380e0400490b0b0210358007000040c0450702ca17180104180130b4035101500071a078581c40d01002159030303181110800c040d460f4010b090a00520071098103000706800014030800c442c125601d075075075a030319040c00c210b0900c0440500b241c001d141d0003400465a240c22030505500702088000d0201072400d105094215107039141c000050401e0075100752910a00803d100381516444c0f5100744100a801c0001d40180003000e0b006500b000c0880d580d40014081070340070b1405184039586018004c0d039035041005450040c3c2c18090102c000c0498040d0310252450140d0385400c070680103580302d400c0c408000410581055440c0b00200e03822000c0342404d044140005d43c080d00859050509550564400900c1d0820303500b4102d2900b50403148034980340710100b06688103454020414000502c4e03035240b001c0f021540380490760141098600104001440740541403003032004000 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 190878588 1250 190877338 190877347
    0xb0906090a17040513090203011a13020304020d170d0605060f040e040f1b14040c0504050909030c07061706150a050d090b0a1b020312070809030d14180105010b 70
    0x842d0341d00d8409141d8529a2036100300000243ca40780c1000c8008580c400740c00000d040c0206005140c20740e1002c0841a11541140c14001202c0d0340f00a4045030200b400382e80181c40f95140e10100b0030500c0004005800c000c51300216084010b0030a0040c070403101c01040a000d03042e6500700b230152034066466440c920810a1005009200a4450b0f031544240600305c01d090506140d100c0005100c80c19514078400d24035a10180191000802284d62100c0d090318200664007910200501900484c043c081c40b6904140c08035060b0b507000c0081d104c1414441e82950007566540b03001400a440b030307007803c0c8a03440701c40740040d80f10f217401c40140d9000001c0351015171070100300074401c441d150700c107030369126070180c1c5c0d5100391002ca9006a406071080511400002d0824000910f092400d50400031820841d481084006100da4074007040c40d4101d032440c00c00c0c20450b180c121246007940182c0c4903110250307207007466031402003034040c054500607040348104071245400b1502c05070981d41c1c00d02500e46004d03070030403 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 190879838 1250 190878588 190878593
    0x307020d0c11060a0e0d061a010e09010902070c0e0906071b0f031206030f0b010f1205030a03050c0d020a0c02120d1d030111210105060a020a0b0c1303030c0b0906090a 73
    0xf0010300e2030303000c6407030000c0041c440d9074002010b6107800341003541e92035510b88414041c429401c001d0f144006003408c181013031040c0d11000518441c0c05016030803482d500132070000100310031420560050181c0d8a01c1000525246508658a41048644000041d804c40401d5000250619401d6085070400031404c035881c41030300c05a8136034004483c44240b00c0e41d501c0c00000031507040001c1c54002e920a15050342c035035140100c0303500c80210700e07004842da40c2c64582003100040e400104440c0008103e0402041c550384542038a00a270150305a8071840d07a00003d019020650b002041e504502c2c800c66128581265030358000790344220b204080c03400319069030512240d4080c50150090b04500c000e00204202d1107901c03060072190800c1c880601c8400441c0c0e2107074488081c089925015001c02d803903c50400040c507000a584542880d40a4021096200428130b4a54564100c82c14880008820040d45a4a14009280000c00c003018ad070b07420713200801704440b44004180c80340245c40c1f00307000704400c8a1a8 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 190881088 1250 190879838 190879849
    0x15080604051f030b100e27160902032502070303030e0307020301110d06080a0209070c020a08120702040e03040f1e09050a02040305011a1005071112030307020d0c11 72
    0x10301100d10100d003004111180010803903102c8080c510039a02c1e0019810b02441d800040c06164100c5480c0c500100e0802035038107104003a4000703401403860f109220101251000303044c092204030300070100e035081c94045031040c400d8000794041c0800d81040f00d0b07141c000d0005565401582d200401c01030700711310701c10404248079420081e980e030158000da0b841c02d41c450f400242113440350840d0401600003c2031040c104105886100000c00a201c05060142d210303a0014080030001400300c030612160450071000d5444618000000d0f00703000e0102c40c800d504244212845400082007284603909080640c0e24000003c81035804940030110f8807140c05040c58603801c010700120741c41c2500070f842000000303000455030290702d014000031000113940740c1c1141846404d694401c00981b040100c601003e0b041c0391190704a8491074881c80ca072950320327950b161034510030f00460b46010130341c03140d860800c2001c080408030095026000355000c5030340030320402e0425a440d11411002901072041609460001e0030710 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 190882338 1250 190881088 190881091
    0x30f120d0207020325030302060c030705070b090c1003060515070f03030506030f03040906030201080a0c080601030c02010f06030804260c0d0c080d020607030f060b04031b1a131508060405 82
    0x10141c4003945c54001d0125007508007580e1100908028103000c209142c0c05224850f00401160141403843c541000003404511171010021306584c0b0100c0007038a03008092140042c4110001c00031200a110410000c024000300c0c05128814002201c0c0c519008101808907003449a008a0001c0301c007816440c141c4c0208801002c140e014050320384405501c2205100030f0001e890f01680000390a811070000400c021001004210407034648040b240d001600f0540c0e05034416006d19000c80c0400303032003008a02418201c10070003100c80c20440b02100f0800058060b0040d2428854180e13800c04a038030641c00c0700c440180c612109a085070004a056040a10400890f0741c052440d211804e95294849460f10314040c1d0000010b070441800c1c00030300b5a040c0a01042c1000034202403101600b0600010303c03510840c440203021900c070421040b03000c0c25100b680c200070410900c131301d10f090954030641000c03a07004040c10054017000030707000300d046e4440c420780d00242d04481d030718185030356254028030008250 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 190883588 1250 190882338 190882343
    0x90905090a0f05030a020105071403060906060903070e160302070201052d03070c030305070509031915020f070c1208030606030405011506020a2d080d0e0714030f120d0207 75
    0x41c000c001008100036040155201d440ba83c0256941c15030500000d00b1104044c3c4900100030030f0403840500d040d171150549400020858020b071284e1500d01c00104640324002c413080d010f0140d03110004518104520080c0308150041e400c405001c0f915808400300d00c00d4a400901042c070030700a41302c0d0450101007980760021074401118814240c030020b110107070404c84400c400204c2d4441d05c0410554540103a035000070450030a03908090f04040000d445e800445550b80c4040c01c0d0340200382c00c1c020050030300c1400d009901e60840d1fa83c8030b68222150543e011500680f004c04607110000380c1d00e440f400002a849030400c42c00760031501c44104100403030b03001a0042c0d900390749178050510200b41c3c0045240003400c1c40d0b0020003000c0703d5403910103140000c0224400b5500d03800c90740ca40151980000517512950700007110741c0d51300c02c0707140c506000f0031410700e448007244140c00c0c020508617840d020040e15054120220341695000a06075035440100d9001e90b0048003040c000d1505541d41e0350090070f055403 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 190884838 1250 190883588 190883593
    0xe090307051c080c0f090d061e0b0a05060906130f060908070602150c07060c03020d0b0f100f02100c09090e06060d291e10120f03030608031606060503070609090509 72
    0x100500009a0740b0703c00540035250559911101c027038400104461100e6889608000d1041b0034a6070001000c220303e81c0f080300e00441000414841c56074401040b110503031185d01582440340d86604602003808410b014250116101c5480410380387c1e000200c100443d1955030082076440c1d41303403800701d240180103815410012030078084040003a0450280880c21400f5940041c0c0750503034000a0340584000e004014020300095184909a485007440300c0c03081800d0f402c3c001c1c0c61075104c510403071801c0046008802e58500e80b03442d040c03541358410010800c60700740f1708080c00f00704210041e40b92210301c1550f45130341c0a080c0f541c2103030008800c4401d940b0340000380c100c0e21640000c0307200c40c1c1641c80801c403620186007502c001c104041804100c006038000044004040d8028280a40107400d40d11000000c1d0552564a0301c03801018420780055001d800c00909490705e41c0703103101040085a0700341404035040c4d030500c0310120315801c00003400f0080351850365400c544a0724100b601001070101a200d0102030 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 190886088 1250 190884838 190884847
    0x60224071b05030c150a1109040506180a0506030d0801060f36090c0206060a0e040809040603050607030605150a050c010e120a12020f0d05060a0e090307051c080c0f 72
    0x380c420f01c05490581da03c030703000d002e80802c2c000c6860070480c00240094941460f0007408101410f014051b942c0d4503500340d170002040c0d25280c0002d40c410b4010960702b100781514004208541c400707900240d00846044d001c580c80580c40c4a02680d0b245030900404000aa01c05245040b0b2407003800c0c00e43c2d140e440c0c0600d503003401d00086150310030210b001178045001110060204842036280c0300e20b003201003051000d040c9a0030050001105c640081c810780141d0850580483d00784400a41210715000d0014001c0003110b95030714001d9103441c030480d075030030100389440000229400e100c50030380c00003541c29040030315203000840180c80780d4000f04020301c80fa40d62224009680b00c002c11241c1c0d00300711800c40d203a80759450481c00401400f80300e18100d030002d0040c01800b490034062402d0ba9500040c00b40085103990700c40020888103445540181d0b8100d0b5801d043c4046010080001c2c03180a001c0e90656194080303400f400d1525034081045c1c440003030741e900700041c00500782c00050072200d500c604100745030 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 190887338 1250 190886088 190886093
    0x2030609041113020a093201051c090f0b0604050403080714090301050c040f150804020d140d120606110309010c020117090312130203150a06030c030606060224071b 72
    0x80b81c0005c0003c0d80801c80f141018040403542c100741c2c642c80c0740c098004109000801d004a810030943d002c50307030b040c03042c0455049030610020700300c0000e10301c1c045010002c078a424201001c000400700c8003a104521244041103150410707000c1d0381d03c619050386812000352102c00080b140d00f680104580000342003070206083e20755080c002c3c5401000300742c5006460710300300310702c5100740700966016440000c0d0860b001031649403c00c99180d0b01540440d840c02c100c20782400c01c00304004800c10024018001c00504035120303600f141003000c100c440f200040240c503444036020341c2d8801181d400c120340d40e40140817400302c9600c14210758082d41c1c410325004034982102d100c500a4281c2c155100f254030723003000c00c40c004603001840c0d51a40c4001d11f060306e945030349050340110740c07241010640c0c0c107603540c000310008000d031149030008070081d6800b80b000a0019540d081000c000d04041c081c020042c000c1136020b04601c00c114054091300c50070300240c0d40c0952540003080e1100c1054030200c0c4085829031241602 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 190888588 1250 190887338 190887341
    0x312010e18011503031707080c070c09051314070807090e070803030a1a010f0e0904031407060e0105010603050105011b030e0405090c030f0f1f0902150c0c0402030609041113 76
    0x42621940c140c0d842803130709515029054031408881c003480700703400008214020768040c03c400d41201c40ca449055139010f160501891580840c0c0103a6001401c100c01d0240034805414511051402034045285100000d00060f0320b03850140b1900c1c0c3c035a03001140520100b1007aa000c0c282110414040b034040ca6590422507003150021a040071840e55261010300131440d0740f00f1040c496407001d1a0030a540310314030001030510754402121a0017500040001010076003c0c0d11420f841901d02082d041d03c801207071810f00c0190040d01e5041c3c6065017070400026040b8003074010141612816100c5004001c0342d0010100c401401c3c440a4042040303400c54551103403194407034030303000380180710190821100f031009052030400c0c001043c40441c0d0003038007880c03d035030000320700c1c3d440610829111400b00003411a581c1c014040c03904000c0c3d030004801002e00f400d400c05e4001440c80303ca541050b16140c500c1041000201c2c00102d5406821203002c000140c002015404600300c030160090600408072140c901400 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 190889838 1250 190888588 190888601
    0x1050c030403020a12140705060313020a0806100617091c0c08070311011a031c02011d030c06070903020a090c030f05090619020f090405070507080a02060f06030312010e1801 76
    0xc40707045c5100c010003844051030400c0e080000c0c440003410702c01d00c1e220100700e80d0b200040c41d480d10401a0503001003155540d0b000302000705502e0b8211442402d00c000041c641201c1071060902090310086148841d0800456941c8108900409442800198039491009030016810003040003800115000041c1e21036000d402b94501036681c10170a840004401c41c00c5500c1c0005d800c10b51403160300c42e4042503070b00050f484c1c0c0303541c1403580300f140c01d041e05103099000d001c0568017620313140681079542900000000c05810420420400c41e1003a807a6110191954116030001a400c105400b00a01000000703403c01c803000681450000303540880d144181080fa0340c10b803007a4601e0703000381c2c06002c84409401d01c40e9441001180c011480c06113106044d1b016440ac59144502030b54035070001460140c002d0301980c40c030503040351420350344c0d01011800030349035035040740c990540195080c003040550600005070380a01d14020b514000603402c0842500c074182c070042941d5600c00303013140740945200c020300461 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 190891088 1250 190889838 190889849
    0x3020f09060307081015090b090402130b030a300e04021e03070e030c030102090d02100302040b0309100507080106050703030e0715020106150809190809040504050a02030706030608030901050c030403020a 89
    0x41b04101c05031000b04508007548210b03100d03820040c0740500c0e60399500d042d94100358121020304807040300700c90000240c00f4685215034140190015101071100c4411001034a541c240400443e154903c89081c2180c5648441c3c2c100140c1e4050103610b5070706241c0e005140740c1c581c0c0f003450b081152030151011090384c8200c0c1c1d05000101c1c03415480e14941000c01c007181710700700d0440007507082054a40c0451081303058820081e208180a04401d4281802581120080c0c1003d42e291a074034a4860025030759005080400750451b80b8182c002559184114180c5041e0f40c901e80c1c0b5145442110784048020748002c610f5114240030381c071400241c600e540c404c540070103010782d0008150545880716110784112042c00b1001031101c043c080243d070200200e580c0c100d01d65002c140d039509030018101132020380103a004080d0031621f00010b003c18004000f80040c45280b0883c2100c04123621b6810072410395510f842619041da0046c44031a4240d03004034003404648030030004603400d16503203400007500044150b220 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 190892338 1250 190891088 190891091
    0x1b0e0f040201231c060612020f0d060e15010e06031f2402070b07030507021309060906060e0604110a0e03030910032f0301090f0e0d02011d060103020f090603070810 72
    0x180c41c03000c100e486551504e0045084204801441e000010b1b118072a0310301000c0380d96030b000807405c180748000700035269a0021a40c04024454450041c1c2500c2c1000b031720305c14000c4001002e8268551301c217000c004030801c00a0407043c11902c49503565500c5500080b11800c40003190800403602801d1041844002c3d4400d41c500044640c5d0540302a0a02c5c0f11500520f001801c03c11882000c42d4000c0c0440e000d095060310310b45460a00d2140f01c000804110070001c00721814091900d040c86000d030001c9060f00d20000da8900582c8070482003100b140c01848551105403c1846004c20050289681c280304000180c2605d262800303490006a000603a80c84200121740c0d50044405075084003402840040010707c62068844101d110001350743c0014403503890015100c203035000140e081781e0000501e03070b00074001301c582442d05020013034060001041500b080b5502d0040c08035100100264983c103c2c1c3c2c0290180b030400d002102404207841009003400e030907109182000580f1142004001c00d4085030060 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 190893588 1250 190892338 190892347
    0x150c0a030305150108010b070b090f0d020106060e0117040b060f0d0b0a060501050705030f0d02071a0103020103050703090f0611090d05010b010e220e010e07121b0e0f04020123 77
    0x1000b20807040d03140d43c035a0411502c000148511801c4008858450341c1100e0319030050340d14044094a0300c1d154502461086c0a0110600d04650b0150444025180e00e0340321100c1100d2000c1c0111288960922019400710452005c04e002c0341045200c41d8000c0380152001084480640115030b003881442e80849001600204020148405106a41c0a0b19007480c146140c40d20036140c660f901e00807010041040203002500304200d00e050341c100e0f180340b9401004940c11200f01045120142c100340300503800301e406c1c80002041c0c03078420701c07580800540c409a100300010341500c0e0a2300034844070403001d080c50000c200801c2a079407140485141a4402ea0001c246090306c140010981d04900c0314050280d450340142a80d007420100c241c08400400020000c0c130185041c2a29000d0000c54250480b40d0080040c0400c500c24200c22010040d80903c40c0760a5030480345101e182c550110748180b40c0d804c03420802140448549040060b0443d00504d05085009180381002505154441001d8a08a000a07 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 190894838 1250 190893588 190893601
    0xd050703060f0b011d24120f041218031202030a022e0902180108030c100506061b07050931110907140d0b120604051b0a0b1201080f0601050f150c0a030305 68
    0x141412341c02091201188050304061f51007044842c0c1e40344200050003442212044040301402c01c0d00002c0da0070882d54801c4c9884660013a490381d100c000c14000502981c0311000d00311518483c803011101c81c0070714485100348400c00100040012440890b8803001442310300c000300099108460281001c480138680c0d0368200b840551a06240c0e908081e0940d007040108202c5655a8060301c1143c0080c0d60283d031407400c1c00000750700b8200765402640d40000e1803c10b200d04800c1022143c000e42000c045085c1c0710300500040c0720f20304d40f600c8e00001c1c021921b03480c07101c0e0700d4148a64919007021107400e12100410500c9030241c100c2c0c12010341311103800c0d43c44c00515020b28018140304030304c000302c50140940e0300303143e140c00ba10740494a0618074810001a80040c0c41d45072814541d00406221004c07039101d010b4a9580008080d00307115508052041580204101c040414000c0c12100c00514031440001820140071242503000f8012300d0703400c1d003844248540c00d030510200c0c10711071203507400003114501f48 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 190896088 1250 190894838 190894867
    0x1e030c060a09110f120d03020a03060608010b030106031e0906050a1107020901090e0309040f0504020306010515250503031023030604060510050d050703060f0b011d24 73
    0x1d155280881c180b120101c08a540d5420103400b510003500c07562804402e080c04110282c401170641449071064031100132030180d150b40a0701d5100e45c1542c09000895548104076443d0900b07010300d4294010400040000c14042d600402c0c00003a1555001140c13410b00c0005022900c58403801d2750f0703041d158410403151a0302031081c80001085d08503030b5414030800340c020410041050285800345a40c40d01020340101040040d1001c070003004000340402d503000205c0c0d0300500003da40490007846548008191460030940d0034280e17030314901503103040100d01048006000d032548c1003030140e403046211a4000c03030001d10085114003916914101441d1030030100d001c0349001c0909594544610403903171b4915076000300303038950801d400000100d900e4440d03518540d0005000c2c0d000c1540710703034280151004c110b070114000e801c0301d005100400c0391020059484040c0c0d0f907a030b0321050010395450074101c5409100b0312030f07010440001c0e000e900c2d010481e0005c2080440199a1740c14041c40100c2c4140d40341e40c04 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 190897338 1250 190896088 190896091
    0x1a030115030216020f010306050d0501020c01050121170d0204150f02010221040c05030313080105071701151103030705090310180807080d050c2101080c060c1e030c06 73
    0x4500d421803418403072410b420155070108800910941e000550310700247e220703800a001070000100b89000130801c51034564002d5010b2400505a0b500303001c00000d4164584c00180301d602c94840104520a00c3d5171b0301e00028204421980200004c140704403205c0100314406440a441030190110700740c44412006403038054950204805c580c0100310880b41c2400a003e96003641000f60808806c1da1224544110140401c0d008a07415110110f10352010700c0600c18000e080300c041d0402000592070700e2008541c040d04500b100c3d00031110581c01004648040c503001c40c0100258270340311400c0c1500c400e05a0450303209488031000540040f410079034905d0144501040525110800c101d031300c0072052091113002c3d00c884050042e80012640e8414410785000300c0c2c05800c2201d0040180c1d2410348001c41c0c00e90810813490914120071480c80080b19100c100d2541664141401080e44410180030081c1ca80c0c09140900e440f40075800d4284005540d001c0d544158400c01409191500116290103142010 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 190898588 1250 190897338 190897379
    0x310030b10140d0c2303030a170a0902100509010c06141f031703070c05010509030318030a09090c0905120c041506080402060a030b091e010602070503030306040f061a0301 75
    0x3800302c0f003400a0030105104080ba244801c2045004501c02c03030900341400d1128603a9018000040d405001ca64050003070030940321403945040450300c40d8051182128103e00000b504960003080e104000d034094006000b0491052500c1400715550365503810666035130404a000c2030b0300c1c80742441111441070082c1104109000c614081030352858881d111544500e003020b0f02e4040f400400300d101144190700c2c10013501d800000030301241c1003031580c46540350310499400d0210a50300080344050310000c802c03203807280030319600c4440050419900d08001d103d900d04c0003090141c40c1c0720000e0543c680f641c05180c410743e154090421b90101c00300348825504202c5034186101000c84003800b642d5085071244e83c2080c0c044c0c40e030700d031030751255581038000b003103a048040d03804060141045070545040d000d6400c2e50001600200059071707290300030f076a522400d00905500d03400500029070613050607484005070f150b403000b020881c1070340c640080751200a00300e860039001c0d10000042c000e80c814801311032003032070 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 190899838 1250 190898588 190898599
    0x2e0501021e0601030b060303070215030702010f092001031e0b0405130309060c0206070b01121101050c03070f060209060a1d0109060503040b3c15010503010b0310030b1014 75
    0x410003903072946400050000604c0d03000e240d0040703416900d0400039100c41e01d5018025648270381c40c1d00c1140442da0411585180158281400c01c103407030010b406404840b50f4411380340f4a442d07401054a954098040c80d809040541d00d04e0301500701c80d000e0b41e625440503125100043c07241664010b0006884000304a6505407408107031107800660b01a200d1001c0b1003051034007207403220041c8005003070780c4500e61000c1c01e410fa040001162440d410420414654800d190004140450100650b100c1c010343c521049190000d10000c8003180c10b450710400040c0c41080e00514060481001512540107030712410001244508130740c0c2d0f9800302d41c0c2000606c0c5ca003420041d141910304007008041d80300080c0000c1c8800401408190a2913800f040201514030540c900300c28034600c03460309000d141c119a406040d282004000c80d001e2444440320003042001a9a0546903a0030684d0132071042d07001a21103210400440c0000004c070320703240407460042c0e186440400d0400d01d4291621042e002c219101441030 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 190901088 1250 190899838 190899883
    0x50402030105030a0f060e070609060e100e041505060a08060a09020304020306070309051009120207090203090307060e0a05030a030603170a080703150810051006020f0a02092e050102 80
    0x190703400681d080304241d010a25150145d083c0c602080075100d841c04c86080e0344a140740204401e80c00014460a80c0e840c2d540303030741c041801c0000300801481004000d0700400c82085180540c1d04140c0c0000c14441000c0500117149a071700e801084555003c0c21812001400b041d081c4645890481c00040003468181c1007981542000d400090700d9590203480803042c582e8905e4820100401803148058440c101710301080102041c0c00d080c0c4440c240c10917040010b000b401c0d4089003200c514400e49024006d060000c0d418900c0b039948400c010320341c8501821280c40345600701c0e40000d004200404a403000e583c6d0200d030081c41e628142d51284c02402c0301090700a400d20038a603c055000200c5948030503249070100b480c582c0d802840c01c08801c1500881d229004003080000d0b2100203800c154020304d100141064241da4a04c8100d80b03e030340205014100b500060303130070005440c02e014842d4100070245903140b11004a01051680d0840c141c03444019020b11100401070307980c0512843d03400b00c168a4050084 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 190902338 1250 190901088 190901099
    0x41805090d090308090603040c03061d0c0a0e040b04020105040314010222080a110a050406060c11040506010212030411040e010c020f0c0f19030f03050417071203030c02010908180a0504020301 84
    0xb41d005d40001240500e4021000070144040c440d640402181c120b00c080100e000e10500c0900c1c0e42d500e0901c090b0152150126a0140d410031507003010880310400e2014000352240d56404582a030050016410440280b0000c0f0209074000c4038440004180000160b50b8054481e40180200800c08068145420f00008010031640426074107000c13035001c000e109030311003000e00003140d40039107800264025107460404500c05421010146015002d028400c05000c2d01e00308103c1902c104540482c016040041c6540c400c800c524050760300240304110703021804031400007040c100d400c0050901729980d1102402e080540d0144410000310b16103002800c0c110f40030f2000b080c00e1400084c2a180030318604c4944012170b003940d40880d0042c5602c002c2d100600c911a00300280070303802500821100444403038040c0140900000c042040762103e08030315214005640b000e0340103000c640e45400640d502c40078908001840300000300b401100d207003182c0d11215501420b0003c2400c01d9004903008a02c1000103000 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 190903588 1250 190902338 190902353
    0x203130605031e0c0703090b0a0903080307110a030f180e0106050903031303080702100224060d0f0303050a0b01030603231e0109120302160611041805090d0903 70
    0x950320181461580c94079200d00300d0840b1071a0810343c11001d1007000c244000440c40c48014492140207580c0c00780d580c0d480390302e4180c09106203102c41021901c07907402080012034450295503c90f107103080030061800c03d8011603040c102d0001c001c0b4001a02400000351850300908094103250141c1490000c96050124904e088841030098038240000400c400702c05507800c00885545520610720011090342c0da140103649074021100880c0305400c0011100041440010745540c4003020710a40513500248040c0c100420f040900b180c1d4210b400c0e00c40420100300d041c081150b495101e03503000606031a000c468070049410520b0a207041504000040002c240c440c1d05501d1030b01c11490030b400e181c56000c510a03250404a80110484c1c900e42c09040b40c040d0ba040d0320004806001d400d41c0c1d41d8040c00340008804134030900c0e044000b040c031100d0304240820095071007021403200380d80e0300e02d02e440d07220114054664454942c01c414117451b6410030051030824000313810602c1043c00c1c0348075210b055a0780c408 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 190904838 1250 190903588 190903627
    0xb040303120920030f07080d0905010203070302071e0b0a1715010527130c0305060d0b1504020d020c0106050a0509060d03030c050405211b100e0303120f1005010203 72
    0x72160000081c80f0440c56600740400750300004c1e4101180c2c0c01d07a999000094590986480303041c0825505140003855500110444400d1a4194040c00300c4606003c102095a2103140d0203000c00c4900101c0428043c034601c006000e00355050b00d80840200c540640a03881c894000d002000c01c1400326600c2d84140d81005c15117202001500d5100d506141210013004c20500e4034000ca079004154a50100d007a0f03050394040d10081c20241d4007406181c1c1c0c2c003001d01c0134581e0007041c0200381080940020b01c00d11000792000740000c0e0300400152500100c50400d00a0303030040401d1070501e07595141e0402036454000315801c0145416a1402c5461401000180741e00350714100242c103060f01c80c07071540c1d07000380315a046034060003009001300a100701c3e208510506401e5510030400394404e02800068100c0e40b01e00101940100500270514102c00e1a800c4031302c01185007155030144020f02162001040413440306205001e4031400a034546000346100c46030541642c84941076420410000e00007800050307481 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 190906088 1250 190904838 190904873
    0x90902090c0412030503180610080f0c011d0406030602130e060f010804080703030b09040c0603051f061b1a27072601050c03060a09020f0a140f040b0403031209 70
    0x5d0340341c0c0d85680820703010b810116500e003098000c1900300440124400d02c05c1e02500c94000454a01900307030302005903241c48480141e40403600340c0c1060b8007001101ca84076014030402601c04103500380c0d217544803416608181c02d0400001d0f000b0b101417004d500c01d0000644d00c0007044400b82101d2031072500180c03450b000a003014041550000d907400902d800307500541c0441401030036402d2140f4050501c5140c580780c42c018900085d0511012610008115030140e40112144400c41d00c1139181c00c01c140d50840520920000c007502c191a0200800d200c3c0190302c40e0078040f0b0011011514002a6809a900d1200d14415082645418000404000048450031f454014030034030410201c00d81140014419032800d00715540c01c0204003c0d94403c800c4c00340d4010401a1989690b060300d803880301c000c0e0300810b444468040010300c00ea14000c0c0c864140300007602c00c8030314691b19228010010306e05641c0943c01c401d1900200050400405070711440000014442c0c9804001d842042c0e40d50200345501580c00 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 190907338 1250 190906088 190906097
    0xb030c0d0605060303120f0402130b0f040203150d1202070503060112060c1106090a030e0a181104081e0601050109120b0402010e0414181203071b0c090902090c041203 73
    0x5103da071010812501e41e600c803454050302d68507001c003440114410417075040b80965112032082d034080c40729000380141203400a1000e401803481c0302c00c1c04004e401c024802d03d007080411210320a56290841c0140c00d030b50043c100d01c1c10354061a02c0103450b142055006c0c80c083d030700010040010000503042429103642c02000802c10900045007114030000c1812880040d000350010300501c188005501120203100c1c0c2c50303400350540c80c401001490440361040c885682d0303d290104c422020301da03000110a8221401050406884144091402000510b12604590304402548005808011140c0140401d00c6c103003840307034204404050007280c1250000c104400d0000070404584c001d14808001480280040080320b089000c2907102d02011f41d08101c091404001030320b900040402c17010545200302c2d044504d1358030b80040840307250000009500c060084120160001280f011240d00280300004002c54002a81c1c01003119402024000340c4010a04000c20001c020050100400c5180c06040 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 190908588 1250 190907338 190907341
    0x6120d0f030906060b040b0711030303061509030a0b0115090e01060903061a150a08130b01060810050d0308070f020c030601050423040503070510201b070e06040b030c0d0605 76
    0x201140a0b0045401240485d107020a020500e20b000101070f0112500030044c10740fa803c0d401e0306054503840103484042d04001c0c49048285000307003c000411800c0805400c541c0348200390344902141c1c0d0340a070803590740740c40c02445c1502243d500c10b80c0031001d2b2564094010040d490803101030188a1948801401e083d1182c502c00300307211880030042e00e0a0005003440c842412894058140340e44a1129000481ca4400200ba840a1034503410044176602c0389104034141d0a2500c152130740c020003098120010342512011400b9107c8401a03004680300c1d8072401c0217800c1042d005003a030940f01030b0900840d4059803900c0c080d0341e070025100b41111402c3e540007030320b40b10000500e03420310081e0a1142a803040d0100788410494008001d141050040301610503507411891030381c2c151030844040c14408040e494800d03000050b554024401c00581c10700c000000c0749020500d81c01c2c19442d40c00180307105032070300400419050600400845a000320041d107000c1086000240808800e40806400c003540d500 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 190909838 1250 190908588 190908593
    0xd020d0903022704050715180915031205071101020d08010b0d0204080a2613090b010309020909150703110f0a020a0c03110415140f0a090e0606120d0f0309 68
    0xa0a02143d5541c0a402089920b000c0c10300c1d60340c505407407040303c840a00703241075504101c0c441e8483d0a290481c0c00885140c06281102c0385000d4000788441c43c100e6030380c1c2200000025103d100800107400f1584800d52200d002c0d080a03c0004210260241950000d06200405590100c059410b4458050781e5545031230402ca10040280542d07041040a4171420601c842407100050351145a451304541e002c5515002d0711001400c1d024a0080150647d2313480803e0100707543e260800c4010b460107144c0002c0117121600081c0350004141e41810300b507006076a001d4000c0c0500701000350720026508050107805120002a44e82e442441002050b02c138011894620440c0b00b8019030720304c81d41000d801c581c1c0e5030301d82c00c0c0301c03500e10000e002080c400e51400b000415140c1200c1c403c401142c01d25090888001000320038454800c0d00e01c00703120351204d03034250301086481d01d5114502444501a006095030300d420b40c18030080d80080829480700d42c0c06401490081030344041034030040700c054540419a001d083c0f = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 190911088 1250 190909838 190909879
    0x112060f1503150f0c051626070309050102030a020a06050c120403092c0a0903030e010219020c04050411130912050a0f0815012601090b030d020d090302 67
    0x80030341c04440e060351000410302034080c01d182c0720316602c00c3e4204607030707412802d040c02220801c65401d800702d0014001c42c685124070017811910300d8050104403601c07a50b1100c2c103114081170000c58410790007010646405260380300b0402c501030a020b000071443c0080c10100030b5504c3c03028a0006002c6a29000010b07010708144003540e1031a0b4003884006980c0c1454600a8104c403683c0c024031802c1c42039249581018103010018a90015030401c46107440d4640c884100d01a20300c0702c1c021307010f146c0c6801c0100c01d032410074030044c00d140001c445500e44207501c10038001d041c01c000c81400340c8a1818070702800301040f040e40005c07040840407152948184120000c5601901c005400a051032901d64600d4040c10780000c0181030341355883ea10258070a0001c030701030f42e0024065940601c0c2c846c2c00499000c0e2540a80488480b1404000c99840303104006024003060803000d1300020013aa440b0f01611000341800c02c40e03101e851003140040c1410240001004040700514480a48192814400558201c101 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 190912338 1250 190911088 190911101
    0xc0302030307141207022409150306010e0612070503070c0812060907030903080606090406030b090307110307060203090108130501050403080609070302040b09100e0604060c1502030112060f 83
    0xe0181c80c2c4a00c2e403814400070b080c1950b09200c0c0c00d401030752070038000d00242c03c044800841d801804890400b103410170050710701031a810b03003107071135802040000b040381d9840382d1416605020080b0295a0f25020b000141035a80c4990001e0040c03009014000c0074115074aa4281d20941e640790454696403030280c100d80e07044000c40d02900340c4500249021200c80c800c0551440341c101610a1340140e200d1010440403a20003040240028080d040440c00038a032050041007d21801040841c1c003a4a035111106156070a035942c0c540342d80f00183e90b9041082640c007500c8250802c901410000c0d2400e20081d40b68170070803800c14100042c4400141d180002512100d8401d034012000300a245441c0c40d018144c000281d4500c0e100e1044c020018149500c40d00846040d160842c1c0c0c1a070800301008103201d060407895507d80103002d5801403209103510340b4405007009144665442440c03001c68200103030705060a4008524580c010801032102035110b001100c0d0a030f90142002031300d02e04000da810018001c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 190913588 1250 190912338 190912343
    0x705040209030a1407030b0f0609070c02130e0c0a05060903030f1606020c030703020606100e01180e070c0c09020a170402030a060e0d0306091b080a0605040501061d0406030206030109090c03 83
    0x341080f441034203800021702c00c06891060790444542e48465a0710880100c1c1192441d911900a13400251128481c1030304aa440d4409010030448a580302208410394400000e0707900203900c0240c001030b19180c00c0075000c00402c407d807030061510071002c2c0440d0300c901c20005140840380700022010003518004e003c1c11400c90704080115111132841a1141e2640e015803000d6005100c1c80d03010803110701d01151241504c00442c7c40d50b000c802030800064400345041c5a080142c15981c01e40014052440d00840c0d21641503940d41100b0b4000342d00e4a11824001600000106403052051600c00d6420070b071412000d0700124040c030010781d0385d4400207281401c2040c1c000d040c241410204855010006003031008c1a03072944040c080140c0b0b0f00d031003600302d5280e280f22910003d224083d0118690040d86003c4c5c004a040c50042011a126800300d001c0d20002e901c101d00050030107252034840c0032041450032082c0800c58052150526640001d04103010602a0910040e0303a0f50801040020215140c0300469 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 190914838 1250 190913588 190913603
    0x110c031e13060507060b090105060a1101090209090705031203150f0609031b011106061008061804080304060e0303092a03012301081c05160813090b060c0705040209030a 74
    0x2a00c0e042e006150b9009403104031a0241408808029440e10328410ba060b584050489070400c0e0400d50300300d40d0901c5202201105541c0c0304d9000740943c03140b141442c864001c8200800c401c920b0582803520304004030700710061100041c800d000c8038860040550346001401c03103141c822480e210300010128842e10003040d50500c200320340107640740a4000304166042d405d807124102ca00c100a4403580320507040b10601c0d40803011440e488221400b035000c40d60801c5016160040c10540100202002c0074103032815a401400403007000304000407400b4600c1d00101c400003075420343c00c0c610115a912904517901003100303d1401284400705580482d1003003c034138014000d010000707120f0155a01200d81c54860310080c84550700200361600009440200600c03404842c1110480d00542254150450300c44001c03c80035000481d4040354000d000780c140c6030781044407a51064078011a0078200c0d43c0c00b138462070080000b400392400401d000301c1c209080b2142038502590741c1100c40c0003e420041d00000040004 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 190916088 1250 190914838 190914877
    0xa050603191a0102031c140c040503100e0c090718180608070e0a0b060d050a02030708011a042d080a0507060206150f0d060f090501110c031e 62
    0x81010469000104410003400c401d00741c0402d004265030302c4090159008024060440c130300b81007143c8030074a60741800181541804c04c3c11804c030006880c01030750044041070034480340c5030030f00500da076090740b003502080b0b00c0815400c2192a109174030891480b800900c0005000940101c0e10b9200402021400c10040364030303951010b019a08128a00c0607440c0342003004994454000b41e5a004d8601d1211000341d203940c2c802d0741c0c9024140d0000030366000b0500f403113950300f1019240540b60085609600c0940c076850300d0740b0005c100d9101640703d1b0768140b01c041f005012030600e407000c49090325881a4050022112100344038000405032941d40c011804500000400c082c020890381443e80c8100191040b41d9500c400032030340c401c07045d138007940140ca10301c04900040c0740010f20f0300c414800152150b10b0544241e21918121000780c0141030207541ca80c0000c2c4204038003842840f00800044e00c05908080c00d9044941d6a40118410b1146207504441c02c01c4201040354142c44030440c486141a404 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 190917338 1250 190916088 190916101
    0x402030c1f120621140109062406050301051c0c0602070501081503060a0b040f0903211e05040f0f0c090b0d020d0611040302060d0203010f15020a110a050603 69
    0x88072281c041000000c0c840d40340d654250003160003540101d403d04044080c0344036507150342c5403411411103001c40710048a0300c500405100f0a01400d11201d0103998000b40843c0ca00c88203c00030041d5500c001e0724004030300030500410390040242c0341507943c2940e4000d50800300094140c444803206902070301508000c400020f0b0079600060b0a425030b0003e0f0b071409401d44401c983c0303941100c1c280200c584c0c1074201d18009000229035612203030b41d804009101103244e90128202008881f69081c0550000e01070003004007541c00040544015410400400c002c060038542c07a69041d241c100c030341c00242d0368488000c02c0074800e003259016840313500301c20311140689a40c501000001410700c280302005003013100303104c46840e000180c0f0901c190054402c1c601c0c0c0350107a450703000504004c00444a0044148400702c00b5855040140c50b500390110720040ea654105500b03400300d85100d600824106000358a941102940410390303100d599441522100d0b810121000200d0410a68200e913400040c0441080070 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 190918588 1250 190917338 190917379
    0x60d02031f020c06091c020601030c050112020f0d0603230a0609020a0b03011203020d030c0e0d14030f0702040506040c0915021002030702010c030c300f110c15011a030402030c 77
    0x110120070f800c06c0380b0251140c3c10184c1c0c444000f48400b0b8840013102c44100b0055010750b119090001c0074000051820906006440b0f603604103031104040d00796581e10038410803218148201c0216442ea14000c0100300755003141c1e40d1242d0100303000b4500b6481daa4144115100c0520240103807801b00c544548075a103891000c14014500c5e90180c0042c4a0707800000100d60007845243c0314403100781c1e078803a030051082092102440000c442207a4049402403143d9a01100f400a02201c1c5010b030324466441c8600d0041005030b410140c2290b10680c45c00700b0321003000d50400d200c402190b403c2402c03101e0300d680b1740000ba4142081c00b070b4070825040c000400c1202207507040d40704c00549070b2603480c02c1014410008040701c01105030b003149070100c0024080d0a26140102c0c4030341d44800461403010030060401c0700d40405450f40f102400459410124645031884810310004005403d94080b149440d85405000c1c4c20040020500c140c403031a00002080135514140003802d16120082c111845180714601100f1 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 190919838 1250 190918588 190918603
    0xc0504050106080a110f030c07030e030111090a09020a02060621070b0c0d0c170c01110a1e0c110906180103051b030307020904290106090905060d02031f020c0609 71
    0x1300c4951030011103011442d00d04043d80c1080c0b00105a0038116940c0609048503507001a0050703042c040140ba103003000e542e00f40aa440390084000c40e590702c40b58540240030540c001c81d00074000382c81c010b00440076082d50014032250b0104c0d0803940c2d00d48500c845410503242c0402030100c060b0b1130203010004608541024010001616050b0032030f003d2002c25081107a1050703100a0040500000c1d4407600c03003294a0f00e0140c1560050607000103010809072800102c6680040c50740d00101e46001d00244110841d40581403000046041c201400c6149580d815151050b101426200c0e07214400451156210440c901070b944144281c0700100b56100d04109640b4007041e10a13008250030246101158100070003a941c0b03103503000d800c04605444070790701c0740000f0007800c40300b844001498045843c0f6042440c2481e0003000142c45610455080c400301c50180e5500030b0110b4043c0a00f5060800141c400291159801a072880c04041d050301002100010b84603a848000e12441400180a110707800410130340c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 190921088 1250 190919838 190919851
    0xd030e1f180b07030c020f030f031209070609061b030504080a060b040b100c0206030408090d0804080607091503200a0314100b03040f020303090a03030206040c060809190c050405010608 81
    0x14400d903982d940c070030307881881150401000199810001c0c0010300b40412180e03801c030030080c2907400d5a540d0404003440c5810107600c02c00310740f003140b05101071003206100c0100030300319901d0144a000c3c00c10300041e141c0c001d9007420611031940410200141803081c1c0644010b000d01c1000d90f080707070f0305500b441409451480c0d0078900c02c03072522025026034a04000725001404d00c039180c5c000c402d000c035002c008160b08001c0044d141090304102400007595010310304040544101c115685850609219270704d0410010311110030703c90050414004000c1c030174902100041103150100d403000c211707c142c6200c040c0348101401002404911880795a8164000d10b40c03003022111400d07000d80d030304a070040d581c001a20a4802d5603900704041404541400c2011010318006070842346040310b19004501005c0661740140d0051f007002d400d000410802c44541c000900782071602c0003250070720b08030701d648841418085070810303440b11142c40200300c415003a480007428000c00c10045503a440304080c00c000000c4404 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 190922338 1250 190921088 190921127
    0x9010e04051f090605030c0d05030f0313050114010b030f04021527030c0607080f120a0b03010507080606040501030c17070314090708070501030207080d060605090f0603060d030e1f 79
    0xc00c07a0f1500d8455402100c100a0040c4422034002043c402c0107001013906450900081104402116081c0b00441c0902400720b08080040c0150404a003101d81c001101c2d0b40e408a5400100044080d0344242c0e40c00800c1c4003c5803034079031103d04c0001c1c08002c0e80710b600184118041602c210200b000040d61316808203030a4880f888038004030800da11365507801c40d6141d20120920041020074882c1002d04402c1d10201d018034905440744008509111007110501c00c002e0b121003c0c207100f403c00703025668101034181840e8034541030100010b0703010f0095018260403d41da5030654a401031145440302d400c00c60102411b070b16402c280d1401405028060700d00b075209298440406e06254000405104503582c1e00c020b04416410500114040d600c0100700346c1d0390795030a01441002014601c144001000e19844240c0c0d640883c6051108050640d00178901c640001e000700005601c5507540e41d45465490b1600b5041210303010001003d1900c0342da8801503140200c207045880b00d42290301142c2c1d0007601000d = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 190923588 1250 190922338 190922401
    0x506180414071a040603020a0216081c080618060d080309010e060106020607080c0310082b0306030b0a110708030702060601090b0705100f110d0203060a120c0b09010e0405 75
    0x1d0860600e00b09260950816420041001756610a41c090020000c407441564150081c85901e41501e8205820044035078106d00700222224441448400001a003030411841500d0141d0000344440c1c21b8079180c4104c4d0103814001040b170382d64600320f1410300313a1141d0b08035100d050040789203008040450000140344199030000c980f10380000303105032085e9110354410b611642e6081a5000307581029005505c02034080303401040e49031007800000b20401c1c200310030510520020000300c00c428600c1540e0000d0515000040c40401d4074600b1581d40206ca00313070003042c0c1c41c80290006c00144640f44019001c0b19010091241c00c950109005d03004602c04da03220300d6469190315000c0300303510a0a0005046030300ca8034180c0b10030a0b840d08070511103042c1d920000780c00001c01428002030f034440b8858404d01c40d400000c12000c0e00d80303800300c2c0e000f07842c0824020b0510007042d07aa80c03094a2141c0202490780382c000c10f541e60320742e21601c0281390b50003026200740707c9404c02e40280c0a01d070a0000e45010003070766590 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 190924838 1250 190923588 190923599
    0x3010302040506090603100b0d0210111522050307020612040501111c0c0e03011509050c0a09030312060504020a0806090a0c0228050105090303060a06180306050618041407 75
    0xf104c45002e40340040250021300c5961288034020f0005104031a000b030140705580015942c1c144140151400a481d0101c0c4100d10302c10380707800c0240042403600440d00b40d0782803010034002030382e00342c0c04008070a6010f480a10641811891030081a900943c000350001340008400300090105002e503101d28021b00142000b04180c2480d40a01e80c04401c0500801c61280601c0a00d0341040215034240d090805155109402007420740314401b410550041c001034003000390f000c044c400d16038002d80c600300e0b00341003c42c01349005020030a1440050104104151400e003a601c00703600010083c44000c004560703034494080701030000d03c41203d100313104801c03000015400c40900d00606803821103e60140c40d1030078000c0c80c25035031341d083d5280040b07852800314414000103000b4401c090150002c40002e640317030300e8028200090b94490360032a408200481900c0308145c45400c2e400001d40c1d50048021400384e540c20007041d41e004c1441c0c01030904141c00c0003844144034440b48a010500b509000b80d9030880e4484 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 190926088 1250 190924838 190924849
    0x106030204140607061d06010f0e100618150903110402180108070e09040515011a040e04080903060a1d120304020f0d17040617060618010302040902040b03010302040506 74
    0x1e114402041c2c8005071108030720724000c030040901030710a1800164000f03140c040c8019440c049010340e08250700c11001400003140a9035500c00402c1c3d0a19199440c0c9810100803e010b0b80c9031141d071060050b142150803031100005c054902030b0039a00308041103034011500c0100806802d11050314180300d466580f085e1400c260088481181403a00440c4c0c4155945004643d00040140050704002846c400030003a130b0f0b204d920f02406180541c000706001c01e04ac00900c0300161042c2d101118aa1000c42031030a00301c02d000c1074404a80143c54692130550300d81c184440c0c0b52240001a03645409160104509030505134000c401020441800c503109002c0080d03401d590360a07a00b00c06001c2142440000c00514201e007000d4002e84000e0030b800c440c500669100d008120883c100341200c2d103070104060190380d42c4000040441d802202c024885401e080d004908180b1940a2640d410a0b050b040d281007a4003d030104c41c002c0440050441d501c5030fa40c404034000e40c200f03001c120f20072400d100100d02d0070700d4803 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 190927338 1250 190926088 190926097
    0x10091d0411100c12020c0613140111061305070308030901020a031b020a1104090609030203030a0f02041406030a15090b0316051005220b0703031d031b070b160b01060302 74
    0xc607111180e9446494985404c901000d2040c84214401d0071001c0c81d103506c0720b1014150201c1c44403114000f0f0743c18070300100200b007200c03ca118100500c06004800690000a11a4000e210900d240c03440031241d003422420700d04070b40c0024101034000002d02c1141801507000f0700d00d5605070b84d0100a602600c20b0513140481054400ca001680140104000720f112500702c0200c00b40c008000240c11076441c2e40740000e94a05440c03e40141c0c00c040300b0050070100034040e20b40e000c81ca2010861400d400c109000b0400c00c014858540122004800076000700c01e01d0b4000c2c030040842078283c0862503a5080a4405000c0c0401943c7c068003501d60001c2486151190701d009603440100500c150180441e8110740702c2d005450000015044103d08000200c021450391016103005085543c0e10b1000d0300f006030a4440000c41c01100c44001303400b1104004c40481980d003180d050f5281901111114600149031841580024043c01c000041100c0a21000c100011181d440382c100414607a90b150001e8040b4083d = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 190928588 1250 190927338 190927369
    0x12301170c0a140102030c0a08030412080910020309031210050307120803152b030e0d0b070819060e0109050709060801060c1505041407050307050f10091d0411 70
    0x4400782c040c80062000400d034480404103204803802d102c0700700005d80c6400e9840e40c094680c3c0c08004188400d0014281c0350300e85c10301007804c00f009541812402c269030340c5111510440318542c044089818034a0a1044803e90301050540005a040500c0c0c04114100948a41c51291140300c0001a60050103c0075801480e0880c569500b19540e1850f01c00070058404402c551041e00c00c510800d00e0341900924005500e5400b01e600045c80083c940079006101c0d02d4403140c850000d02d0707846400a8201014254040142e04d06020340d03845101102c05110080d9420300c20341414040080780d1280b5000906040b00e1401500384415294882e040d11150300c40e01400d000220414018070001d030082c00c1300410315105071440c8041204561020046400c1654211143e86503540d0305a004202041010007906044000d40000b40c0f40c00700007031810207074150f918011900b50051260305401410210300800d0642241d030f00411703a0070340e09540345404650490f80c0c420402c1945c0c107242806485241d4240 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 190929838 1250 190928588 190928599
    0x1a040b030d1d0d05060907180228050409140906070504030b010e060105071203090c05060301080c040915180c09150b0d06170f0106050402131205012301170c 69
    0x4240b46181a00031107041e9a42001c43c0b140114001941003286520811421000c1c2452900b4a0f0140b2201c07081c16058900503401409650000000069240d460b002c44c1000c0308c0340203ca810060b10326004681c0526601442d124884800c0a50010708910600f41d20b0300b5210140e440600658072030180e400b0141020395140d0051103150b940710700054020a0505201d401c1404070380d90046c403a9a01d40f82e550000f038039400038404002d40e40c6c800802500040703480604640c1024045603540c0c00b03420300c85201300d440e10540300a20005c110106195180d104091086507242c00d6102008118030000705c40080601500140d401030074031078a00421902900c14100e645440000b98171900b201201c1c2e0030490340e681000541710700c0c00c02c0c01801d4480440142005004c44074105084071541c0e4001c81c000c1e401006948603030400310060070241c0e03200c840b6207e500800b03030031f143c0d006041d001c440c0d8400042c00c1d5204001185c06d002c0c018102c84403c039146036428003002c0b000b03484035030b45030940d03070483e = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 190931088 1250 190929838 190929857
    0x6060f0d290913052805060406061d16030911060a020102040302090f060904060f0b0a0e01090e0304050604260d050d0507020118080a030b0d0605010609050a0609060f030b041a040b030d 81
    0x60301c0d6800d00c0302d81040c900d6500805d14003511240d082c0441500d003200c00550700c0a08018081c1c0d60304c80480307040003246445500d032800d003080c004102c00d0700c0c890208041d643d0140f102001a4030700342040903500940090384800c01790b032000c0d0007984640001d074030500801000075820399544035514801c02c4090a41e048588a41c0e070394501070710000780d48100040d01c680c28120b81d511402c8810b00102081444007090703501d4410803100b15080d40100804540080105000d151603240484088403410000344050300d8410200c2c01500d980464400c005004807048101e00790f50260140c402005011401c01840d02d41020903800c848d00900b0706d140200303000381c0c1800810782c207101410700200c103810003007558074103280012000d103004070003195141da4a400521031180e000c08800d01601d0140d40c0950700034201500a8001801442103a0810849440002c0224400e400c51584104003070001e000c481d8420100b08103540350404003030301542c034202101d5035528000440c06404603454880e284403 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 190932338 1250 190931088 190931113
    0x5060d050d080c04030b04060b01031d071403030c03040602010203010f12021c02120d05120a05061809010204050d120e040c0905120703050a080d0507050306060f0d29091305 76
    0x103032200105000f007000001d0100001088520700401d1240703101d00000181c004c0c0d40b100142c111b03094056400307a2a200541103406094000130a801591000445550b042041d54002403443c402d04510310500d0001013070000c3d80e2901500918182c4810b006101d010680f100c00520b01c5d206000c9010b07601c25105060b00001282c01103a06802c54000341c800d40340f40c07060344111442c000460044030700044000031221821442c40c404140c0101900e1408d01c4a0f052110019080b1151394290950701e5606001084c0520000d41c1142c0040c980a0004203c40c4003d04048054030b88204134840401c500e00c2d68528a40790a2140d02c104081c80d4564100da41d0821050041c9960b0800f207404040c0f10b00c070030100200c0c108201180e05c00707204082680c1e8440011401c6400d07180040e00d03030300c1844403e000b400764075991207007500c1503600d04441c2d6585030741090201c54082c00440340c0b2074080100c1d46101071016485005892003a603030588004102e078441c101e82e420b0f0704e1000e2001501c0358100740020440b = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 190933588 1250 190932338 190932347
    0x10201021206120a140d110c0f01050a091a030106110607050d02090a03060f05240d02040c0c0b0903190c020609041509020d1e18060c02120706050a05060d050d 70
    0x503d088200c00c6414100c0070f03644040040c030410307070040c1031680210081c00c6400d9010a14071035100301c800c0603000c584002008605910311181c03041e4117201011500f15400d40c42280300400410241034160401814010f03100340783d503c00e00a140000d001c0030050f41c01000700040d014020065951901c3c0f9101c03800320b244000f500b0202c40554406424540040401c80c0e601442561a0414100094070704142c2e0b5010f444201d01040c444080310008400d21180e51286d0544400c81d405031001704040d0170380482201e940c0c8031884020001c980902c180720308088000041c140c421920b820600c1311003201d00007501c950070510802076008500304002030301030034540c0050346078010000e03080c4100b944550008069802a801400f18559284000100214250000124818030400c10003003414005800703c075050f113410000d4446c0e616a0340c0049591b10802541c5e201781c06111140d80c45000a1404c20040d00f016500c20b0303407075810a80802d03807619100c841004815400001891808880760041d00e = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 190934838 1250 190933588 190933609
    0x5060f06040f06080d030b01020a05060a0213080f06240f04090c082a0f0108040b100b0d064209050402120a050708010506040504020906092d010201021206 68
    0x50300940c40d00d4020b60040d10b54090b002c09031016201814080140c844006d00300d4940010250456000500c0b03400800c1d004102c081c4c1102c0c21032030160751803d80c0c1c42154134554250340500c4d400d208203441105101c0e400320f030a500a1046014000550146c80d50303c00d01c806040c5082ca601003000c0903170100c1c500e0030f0344c0201c2c030b11803141e6844080d99980b80c440340d052804294000808121030301264620080c80d180d90200d2140c2140c4848450041c000000c2c42c400703000308001c2513440c0c2c080c0401c5a582448407039800510301003a4a81e9901c02d1600c08402a081511800801c0042204502055500c0c030041c2c00319082000340104107108000d010318101c002c03004103402840100800429180c075140010004a0300307000c1036803924200015401c0c2119002040901081035982c01840303107a0b140000c0b0340844000310b0380981c6a21040c0c000135805d01c05c4007501036000b00c46200790100780c402e02c00300010300e10700000007209042a8030010f9090b48242c52030134584103803001c00a07585180c45038100c0c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 190936088 1250 190934838 190934851
    0x12070501060f080a05010608031c020d060816080114131b08070e01080d02070f1203020c040905150a0c09170a06061707050103090c09020f070501050a0b010e03030705060f 75
    0x4901c441d62000c007079180410581103181e01390860458001407160901807400142030f0880110b00c0d0102800b000f0740c0c1c000c9201d15258410340c000500e11802c4100c0e8002e0005003040f103054900301c0c4000c003000042d8951512424009500f03190041d0120314001030003521038030041c984540d41c9940c92366448200189140d0b4402364000300c40e00840ca4500c00c00c050b00180440000004495040000d1359182c480e1209c0c40b40c0031540000000c1c0541802c1e030640d0070464540c0703c0d0748035000182e454241d08040310909210380052074024088244100000e10700010780180d2824112a101d045400c800d550385110140c01240b00c0e940100400001080150240100541910b00c00b0085036660070139a00154055000e83d10110355005d10500c1c280000c2c1c1c01005c090030200040044e980d0b404100c02d030280314041e0400e6001c2511a950040034040301d410540c800020071644c500184800024801c09400b2030001c0c1c01e0407070440ca681000000c607403d40d90010b00038030b000d5079000c80390300102c2c0004225 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 190937338 1250 190936088 190936091
    0x10c080f1c06030b040c05040c1e0311280801140d02060705010213050108060604180b030a0203100509070e0402130507030e010906091703011a070c05060a03020a080f0912070501 78
    0x141e8050310310622402010b18031401030088035003400d05003004000440e0b0083e0703115521300300c1c40e0000d542c0c01943c5464050b4801f10400e0701d80f01121f1045e401044907807100302100c03500188039402170310b1043c0050b00010011000c1650440e050314211407183d000d00580801e400b5180040f142c1c0d180c107118070803500d403000b010359150064503507885007640c202e8120300c14161071241e4280f06660b00698140d5100c24291035050a0601d84408042004180840c21006030b54910581c0c00d6134070144100720040c0d0300076084904200c4401401c4004000131075890019000d500700200e03060f250f400000e8001c0d90010400d4650160240215000707060240c141c1d4181070b903c0c60200350742c110a001d024200340c0900d00004091003e8103042030405401c1e5600c8403043c5081005010940d400b0707220001545541c100181c5869480c41c100c500500c460300b129900c90000320303c800c00340350715400030100c0c0c83d080d585070071994841000b25104140140e60040c4a90452003005900601d81d034040c0001e240600b00 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 190938588 1250 190937338 190937377
    0x703030507050c13020d0e01051513110a110d020d0e060309010603060f0209180f011a0706050a020306040c09030302100c0314070206071e1b032303070905010c080f 72
    0x804a0748800800360129801041036290520503118201031f00d80120002e2000345409040d0043c40000c42c50094401d4041070a035030b00d90f21603540700300311043d643c0110340c2c3d03601201c07103014054103003164500703456100b4550b416100070710110f018140c0c0401c1d6110b0b2034100ca0341104029084d00000d11540d6150740e603134000808645180540700303040d11046001640c45142d03900f401a01220000c0540c081350901c800e010011542c0c0c1c0505045641984110f0b079020144018000d40784074000c009420b41d8100401d0102d4050345d44d00440c05800e048804100b04000c22105a0703202e0000e110190240c0c102400c140d210421700d401036026842589000581780c0d07100014914042000d80340c01006038410410400141c1c1c001c0a003038048501c0e60b101c510310494103800205583d00891039101c85007000d0000d01d08060140e034440d00400001d109032103165918440d80d15540d00120340031400580803940001e5554041e000b01002c042e00080041c1c17620080803503a500c0d5604c100d004a40c011008070 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 190939838 1250 190938588 190938613
    0x3030d1e0b090a1a0306182e09050343121b0203010603060c0201140408040504020d111209060106051c020c030c070602100f0c0e0906030c0a0609050918070303050705 73
    0x81c0078885e00c1d43c098810307c01f90121010074604449003007030b99418201d80340d0f000080c1680e089040c4034010060800300303c813041c1d860301900390701a14103e001d0f5555246c580e42e000800c021000d041c1002c52103480d584020b59410038100805004002030449010580704505843c0305011600d4881464542d09822061560100c1d007140c00d10743c401ea40c0c40e03561342c00404030a542070240c803d41c05008040e050150034951942c4509210783e100e841d1240c1d90000d00080d62550740e8100420182c41c015529403200d01c1c108241c200c0d4442120201c0550050100200b2050b0292040e2120121114107103a150221501c3c104c00030751010062440c80d04c800d1207c00c0b0104410042c1001030f00f141c0e405402002c1d482c10224046d2000801407a002c503080c84c4039400a10781c02001c0c29415030f01200d014501c1c0c2c03600404242802803a00403da04403462034404200c55400005910841d002980d02e10450b9540f940c20345120182132907a1041c035040244100082480784000d865002e0080c000c2c0d0f940c0c40c1001 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 190941088 1250 190939838 190939843
    0x30f04060b2706040203040c090209040906060b0c07060f20030d0c02030c010e0109020d02060310320d021c0302030f030106030f140103050309010c1103030d1e0b090a1a03 75
    0x840581c2c05010392401c00034000502030005070040001da81c1503066040035940c000041d0110f0280508040e0301080c5080c9580d925003000100f41e8000400300440e50721440c4010b40c3d98883c2c00824951710455000280b15442898114540003943c2e4602201070b664091450341e12040180742078030344c4810b11040310089080e100b65030b14600c0c9500115629a4650131860a41c0d002245c03440f4140d00d0420383d4000b41c1c031110001c4442907412640030369241d5481810741d410706099005900400c031a12603503081202807605400035881c06110304240d44404404112440782352100c02900800140d442000b80d24404c40358070101446401078078240f88000003208507030f42099101e000041c0d02c480d40d030018180c0728811414074803102040011158110b803030700350f17491140034402410003c406800300180985501d0b441140c08009060300e654403ea49007003000340c042c1e81c2c102d4003041911840070044c54884c2c0306105108030050f2035800c1e00e559030185440203150040b5601c500d5030110712000c802eaa801e = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 190942338 1250 190941088 190941109
    0x209040e030d060302010f020712060507022104050415210816050105010512030a0905090601021f050708180601030809011205100f06050f04050d030903050604060b031002030c030f04060b 82
    0x4035900003e1040c5940001080540002285401e541000c4824060303d5042d5080c1c810711900608003050325120140d00724a041450811b04d1510054a9120b41c1c0b2260010000c1003142c02c00c40301030080f0600440ca42000a44500c1035200400181c41d04401d02c1443d0b00c00034403498003400d00b003070522f00c0450804003680f01b0074500700c800d41d54990040c05285005500b00601c62810303001182048a00e0700081d02220b501e000f81407140c403045002030340b03503842000000702e0610080318410f2442031604402c8042c10040e9208000b00d0454000220795212454148a0400304a001000d503030b4a1510741c60125407142603224104404003000d0b407400340c2030b03005050182010b2408441c09500d04001414010f0743c6030844030822904101c26401740710020141c40030348a04132003900e48132155240603910340b4090380c0010450b0054004010034040203a0183c00364034025000d803100301e681300040100300d110441e41104612424004105c50100e4440520b5103d4440d50001504520250005480019 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 190943588 1250 190942338 190942357
    0x20a0302010510050307051c170304060f0902030303060922060212090c0112050a0b0d050609060f090a140102040918031202040302101d03030409150f060f26010b0c0f1f0209040e03 79
    0x27000410320040001c18460a1540d0151030070820072891a5030010303484c5d1001038040741c810b50084020407a0140010150710703c1700d4651003070403200307690f61070000069040b1030400c54207460410000303100810003140c4995103a0050b912001540341c40c07548200107141c0078009000582e45c50544c59030b151110315295941c42c5c0107400401d040d02d44064024901000107140b035a801100c0024401c2c2c03003000040b045107960344100300500600011844600a000d290710910105042c517240440c00314441d4100f41c641c9002c0e50380c2031241181e000d9501c09910652100a400001c1000d60b915080d21451001c0f4401d1810358072080f41051040019246400a4100d52500c90341c81c40e14100302c28039a80c1d080024085207100f030040b540307003400180500d65110400801d214030ad030380d414280c001d1070100b12182204140000742c2540c40f0740f650300c480d40204030040d0541c880c020440410610025421518144229a0312418480f142014001e500f01c890401c0d0807544500c55028038a100340082c041028 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 190944838 1250 190943588 190943633
    0x90303080c0412080d0c0e03030331030e09070507110402031f180b040908030106050a0903050613060e031206150c070b091008092a060a020a0302010510050307051c 72
    0x11441c0074440103c640c0b454102d01401307d00340444c4581c0e00c004c130a07283c0c0104284000040348280403010301d045041c14145038403c0900c0241c02e010960090310b0102c0070034040d0303861416566003034002e860512410740054110740940403040c489107030030340045501401c00400f9080c2c803001500f0f811403821a07508845140300c084d01c40360005542c5031240d90460b210465017030003290384a4840703190350b20060091200300440062060700460041c1c01c010000c41c0c0c0101160030710701e400d061240c1d003150302180488581e8100800d4022031480041a070f40000c1e03460010744a50345684040028802da07140c00c01754003200912051381081e4080c426080281003010002340e454030580c0c00c01014600c416404002c1c04900d1040c030a13410030000d00c84c03825a00000282a502c01285071300b02d004d42040d141c2c6540042c001810b0010b4135404590450b1f01440381d00280056100c0401c80c0044030000d00411341c02d50b012041c204503500d001d850704c0708500c0d91403501d988d041080d42c44007005460320300c2041500c00e = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 190946088 1250 190944838 190944847
    0x190e0106050108060a1d0402040e070621022712011d0f0601030f0b040512031603060510020309040510080706091d0c030103080318061302090f0601090303080c041208 73
    0x2542c001070f10740d9000d4800c603180c284040c00c182e11010108400d14000c0c028294040010b011900d1350707446007040a0800044440b001d64400e03000700709480c80b43c3c0586c22a010710711010030003400390007500c40d0000c4940e06005040701c40040c1c4050b1404984985030700010b015504900b502003072046503014070303600d4603040701824030300591450050003007268603450b40040010000f04038681c40c0c0c030070b13181c1e03000801d020355442d1400c02c01d00d00b06d80e002004a03043c2c00001800580b107603620000004c2081504c042c84820398420802110548030f40700c440150b003040102612a182940c40b4a9002c070720001040c105a8484031090300d808019004800030580001080c0300c0e500c0848116111300c02330314040045850010070b20109404107210040c00050084003141c0c021300c00f40d071058840e001040031110320b481c01d039045140382c80003c4000c1c1d00030b0401038046000f10303003e000210f01c54003040e102e501a103495076a0454070420028000c0004075001d02012031411b4148040c00456401429001d0300c4 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 190947338 1250 190946088 190946099
    0x1090e01060c02010e0a150e09161d1f120504230708011a03060114010c030e01031b0e1003181e080301030b0106110f0c01080c0d050112060b180a05190e0106 69
    0xd01c2d048c2c1c07000c3c0d40308842005c10020100444103007400b03496030914003400038a080176005030803403036a489010b5201440b6120300341101c2c2c40e00b60700c0d0f51001f00c1c0c2e44c4082e280305181403c401121001d44000d0300000c8584403a5185120b4903454201100d18034040302c2c200c03640c40001c0c508450080c0c10003890b1030b00c881264829403404000d15405043e007001d8107910071040d4000601000341c2c00c0401010300c03483c0c1106c8201c40e070003980030020002c41c94060703074042407054000400001401007518801c01c020503111310101d209105d201c54207503004041c070050721075649650300751043c40300c00c407112208001c0c5076000007103c2001460003075104211039842d6506000005c0c04034a2842038842182e803246070806242c41001a500c958a0400e003084035040c0c480208403802407113888071691016082100015500400002400c40705001da40304100903400704c000c1052070038140185600750980c40c0c01240d201c1c104c0340e201d16000f2510042e24584405c201803220241c0e030340786004a440740d41d02c2004201 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 190948588 1250 190947338 190947347
    0xb04080102120c0a0c1214120627010e3c0f04051903030609061403010608150c1602180603010c050a020d050f16120e01090e01060c02010e0a15 63
    0x80100d02020610b0801510500c01403200305800d10103440d04840156207000ca90103042c100c0264001f0341c803045d07610049201c4d00280d5000a80e000d0313010314280e43c04854107800c2481c0028000d07480c111002000d0b440c2100566003480301810502404c0380095003c1e07082c40c1805a00c400c0301c1c0b803c09050368803c81ca8140b4028025004002103440a902001c201c0010008140c400c0504000c82c846c001c008020300f021801010240c2000e00718a10306a00071072840c0308040e00f5800d0800840080c442d4540300d0304101d813103800d115910115040b410000c9404020220041e003031000040d48060708205003500003c030b1422084802c0200c007480300c2e0a00c021814280203004040d20345017004c41c60704400c1c0f9002075841440000c0442049004188240198452802c84040c03280741240840c0302c89c903c1c00d001c01c080081d0008600490306054603000d40394052400042203411002d44042039a103407640c05da403001a02c6408904001020060101c01c0d55040403a60280001c4041a1944401900040d1 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 190949838 1250 190948588 190948591
    0x190e1e0c0304030905131401080f0f0c0f0111030910081e0403080703020703020c030601030803070f08090703030c1e0803060a060302070b01140a1d10120209010b0a090b0408010212 79
    0xc08a6810010040460303001181941110025910a2190004021014010501040c1036090390421000000303800c0000100319004401c641c1c255261405c02c070412603034504040340c4440c1c008021000061040d8003d0000a144c0000e90b4240c924007140320300010103640c881040309004c180004144000102800c0c19100701e00000110f4907540c2c18692000351a20a00410020400d0f40000d02c4104040c400d01a90600e4440501100d0781540c481c584810660011121000001d038884a0440420b100d0301c0340d10f0280107004003800400307046440450300030f0440c410588040b4a101031900300c080c0d041014408040c0204405902ea0070041c08102e1040b005074040c4041500500c80f40020413007140c1002d0445007000c8428801e950351402160455509511880205c00c603a01116024106040c000e4812108250b030007100ea6100c00c070ba0629040821006034008550400501c0200003a0b0010f0241c4d42040c14829030245c0c0d503402282103a4025040170320035940104070280c540d110407904e607 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 190951088 1250 190949838 190949851
    0xf1207120c020a0513110c01020d05060a060e130b030f15011a1c0902090a020a0206100b1c1506090504060e0f0403050f09060301060804030206010b0a0e190e1e 70
    0x124501d441d07600000e44403c858000c1601c1450301007105441c20283e41e0100705460921b015054890b0400e02c02c0038003d41104400c0501941800c00041d4523240045807102614400c0d06d0780041c1c81042d8040c06681c0100840610307640e035440222004a03a402c1295144444080c001059541c02e200199841e00a040e07100301100740341040195200c540c1c0000341e031700c105005403800003161240840180034010740c000280d0001c58100c02d2009000643d001402030032308035002c49070340d03840d0102d0459203805244a0145480c009000b140c0740c1c2002108440c0700e00c20210800b10740710303034419024019003032945d00800200309050b20422203800c080c05502c1c01484100c8020043d4946501c0c0c2c0c032041038004000404000001500c0c452030401d0f08180c50840d5000791001d0f44030741c0c4071000984420302c2a40d00750054070400300002061800941207c070130a8895030340b00b00d1a070006040c882c1c0c0001d41c80c251500000f1484011441510515820703106400290602d032000c600b0320000d0700d00d40b0015060 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 190952338 1250 190951088 190951097
    0x10b070c0f051507111503040b06060304020f0111070b0a112b08040c09061701290d0c03020301050c130b0c03030f1f0b0c0f061302010c03020f120712 66
    0x1007206543c2c0351180a00b50042840044e514403043c40c180a00c0081010040d601c40310040441d490510480c004e10f114500c500d00c00e02c01d60f103c4030200101800103c40007940f10b514000c2c1000c1551068020b410003551f290100c0d1000b42e1a00900ba1040d085a1356001c0001c49d040105900440708101c81c04000303000c10f03810807079014800e95034021a03101410310030500556402143c1081140c80020008101070401045441e444104802d20500a00113240140d0300b020301da041503880809e2410120000091002e5135400320030306005042d104180300381c83e180600040080943c4003809064410320340b0080390b9035110841402d64104d200035130040d10b5109824030103014000e50010841e070301710303840302c0501d00c05583d403c080541c48800304100c45900280140001000207070a40038003851100b131011340b40d40f000c49161155980f0021036001107c400c0c02c980d01805940100f19000484c0d009105403084074a007100024500180071a900d44070b0a000941c14081c400ca0a0301101d5a000c103180 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 190953588 1250 190952338 190952369
    0x1b0801030210050714060a0603110f090a050c090405130606080706050a08060a08010e0d080106110a06020304020d050d0c03021005010b030609090309120606090105040e0a030f03090b010b070c 84
    0x801c107030503002e4654005209000400b1803d001c900660b505011a020040300c50a01d06503000001905252004031550348081c010440c09103008840c081c0c051002030241803140e42d6041001018020203002070b8801902002554410b4849000301307403195881200e100744900d89440c1ca48216516075002042c41d8000c1030381407080d1507109040320100d0f03605280c400e23100d8075220009074850748a0340c40100710303610300f5030703031034088500820760440010403501c2e02c00040c4e903105030603a940c02d0300e2114207589400168403403001a40f6617003e0742c0c1050014045040134140b41e0341d40c519040c203111449000c200d02c84140d204040d810480b81c1c0004030359070010f000d9945083e8810701d03280401f03400c1e18890840f000024011580400650340012070044c1000000070030042030640b100d00550f41e240c040c500440021429041c0790241d907010314540d4000746801001c503103003219030b01d8045039003004041d1110150300c04203111008140c060422115025920806071421908082d0310741e000304a604c16103903 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 190954838 1250 190953588 190953593
    0x40b2805071a04060b1206040b0c0301080706051819030b1b0403030e12010f0c020f070503060403081504021b01050f160e0411030106090f0e10090209060705060a1b080103 75
    0x240c510b940c141891002502a01d652901d01c01a240c00d0349229017029a060041141010024156024502860014009407540040302c1020710003400b41c411aa031105600700b00a07481a4010100341d00c80000c0750700504003000000d20000081008605103400d201810700c10302c14000300c0c0d15005000f00e4491440c410410350350401034000e1b44030290512041c4841e003d059168154183c1004080800030440002c02c41c404c00c00501501150780014410319410070107100c80024454150b481c01002000030760360b181c2d01291204001850260011008501d0700b00765102c0b800a420031524024008034240440c01c0240d084030801400d1200c4409081c00707001c2078000d001c3c003500d651000d44c90f009016100403000303c2c01801842001081500d0b00000000388075600074290300555026504003010320350b9581c20041200410382da5001c10503000c003410008285903900900f07181d040a048981002115103a242c107001c01150304160150310b501120f070703041d2581c04c5c0d03500102026040c41c000d40e50558 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 190956088 1250 190954838 190954853
    0xc070b0103080d1803050421020310020306060f12011814180307020901080c010915170627040b0a02040e0105090703090203060405210901051e040b280507 68
    0x180700203450b1001c0083d030603081a850790000c1070100b5100e9419014035200d80b030000d060b03500921036030304d00c0e02d200c88511400c1480d000100008540080c0180740002405980130000d50024204550101003001074400c504210000303000e01090240f0320340f1080d07140040c8282140041ca4480c8500b6280140e03400f01141205406170700620a886000c42c1204001140f620f51310a55901940c0b04100d0b10001401c010002003492000c0c07802e0f40c2da002080d0340e4402e00d100a8440000f41d1001c1991005250000380d080c070700c000c2e4060380041c82040c071210b4a1054488000301c42d40f0340740c01d1007030324000c00003802041d01059400240d00e103070441c942494114940c00300036049c002c2350710030f480e4480464955840781d08903d40311354000b025110a0f04151400c15602c91490745600c2543e141841c2d5450032841e0081610300700c601c103840e50740c6448001110901100303e1000e259401050a11000c03c500321540040c2201c124440d0364402080503210b455466035407220070b00400c0020070020b460005180 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 190957338 1250 190956088 190956091
    0x705060910030b06091e0f060a051b07090207080d0b0a0609052106090601091103040c0e13080c0102090301060b0a14030c040302031b010809010b1c0c0f03030c03080c070b 75
    0x200d00c2e0002d1988541d0300080c8080c0705042c0307680d42c00f40300449000c581d110680c0c030105070104200c51810000b603412060042c4c42c014109000f0200320140100400c2e0744000103039503d0401d2003001d84003041c0c1c807003000700b04a8014040584100c100420102058016032041c03820307101040342c81e07141180c42c04e04014140724036401494010b2010a5001c1c0200408100f41c1400d00c01501c280d400380d01d4400e5225a5400e002d20601c0c0303455041120b4407505058030388c21a806141c000320400302c1e06080c442204000b40c0013070b107401c00c00c0b4101c880810110b40410080c1c04c4441c05a4005683e4041d610708040c02c0d1807a41d004881815410081303641da41c1d030013008140d45140140c140d50b489684c0d0310509001c5015590029405000c2c4100518902c40481c1060b0311159098940454a440d004262401c90b8441c0d0505500316041c40ca68480c4c0244800039403030106c0c4a000c000010710f484001e5400c10801541c003ca0100c0e0900081c5010160007c0a1035480784c0170540c0315013881d0850700c6023000c0100 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 190958588 1250 190957338 190957369
    0x1a07061404033c03020910050909011208090d0809030f06060f012f0304030605070210050a09260d1a031515040c05090405040c031101020d17090703050610030507050609 74
    0x4002106003c042c0c02501a40c058400041000f071f086c90321250040d01c2d5501800700c1070f1103801d100c0b001184043e0b244070864101a045440c0c0c9041006040a1140c1c100c8880820740f105c0b00b060100d48019038080264203030b40c01c1510041c10003810070030240130300aa20000c1841c103010083c050442c1312940f0a0040303400c41d114841e02c869130a60700c03042d2030441c880c07900058111400c1204000f07a06400103100301c02005100c00c100016510a02c01608503a18420002c080c41801c81ca01411242a0145602c9130001411914070740100e03a440e9404459000c02591100d0401c910341ea403582ca0140504140c03c24211a50209407606d0920300100c0c08041c1800ca11541e40c1e0202c50800303503c00c1381602c911440c003800400c8a0700f00f9040004450b03c07244412514003a041e101c1226951010499441c03440054503409000030742d00407414024140213103130040d10312031a1000808070304200170460003290031044804030755043d401e00500303000094019034040c64007003241701219101d201d0710003130052 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 190959838 1250 190958588 190958687
    0x902030307260307030204050102070b0f0d0b0406120c14010e011b032c150f0d020304020301020d0203010b0307020d0e010912061b020d1101090201091a0706140403 72
    0x10040b459640380542c1d501d07010310550002100300a00d00750181d000b0003d4840903002c40e50032035039444401e5070a01c501d240682600404ac400c0140c3c039036468020b0003000d0380c014008100345403103d40350190541c41c1380c010f880111072100104080c3d145a01800b1100313800703107401e184004c030900001c1d00010b003030b000f400c594a402d540382000341841421381c40812005ca0181803001e128030313080440194070728100c00d88920000850004011100b60440e00380340d07401c005090a100072545000025000100240d03010f54007086040d11502e92480218082c15a620840340c481c184168000d180103180280c403020700204181180b00c980c1c0010410044030381d490108041c561061034120013a2202c00c50202c00c060310100c40207280ca401103482d0100b40c7c1c055480c1d1000244285035075007a03a110a401901259010f40b05101d10080c2e01c1000c06041c640c207140f00d140449560350202103580c00c0d2a1140f90b40d1b400014401055413021260464402144150721790f12581e02e5400d010041c00c0b4101c00c40340703 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 190961088 1250 190959838 190959863
    0x1303030e1801210515160c030f0509040e0601030f0c0b07030504090b011107030503030610021c050a020a05100504020f030606010f03021615090606150906050a091e05040c030902030307 81
    0x43d0000340083c24038076403040a4a14003c15000c000310b40400075140703281c44150100d1800c007000d10074440b0060541d099071f2500b200c0700c000303002555035a02203100c0c140c100751038028004501d101003015a000f50b21400c0020b909088a08260b00482c0042c2c11030f103004d80b0704000150100e030340501540d003580e0f203410340007941c0c000403001a02c0e0050b000307401040e5405503c80c004144000400518420321041d20304004070200302404030303100c0b00201c80640306882c055408070409480760020301900c4006004561b40d0f1486611028500486850b01416003038507a003c00c011400c0025010b000600c003580186001d007807450010303100300c6103031075801c0405602142040e80c0511144e00c518209420950000800c24601030300740c0980401030302941c0705400c00c100005c1507101084842505005591140060390805108071125404202e00c00200144018007041100824800241105a203604840d040b850407080c401561013085080d41854071381711028001d0b8402108030384a140d4440c035440030302d = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 190962338 1250 190961088 190961129
    0x1209121e0906070203010c02061504061a0d1401120507061d120304120f0b0f01060906051804020a020a0302120412150e010c02060114030601180c0309020301021303030e1801 76
    0x19003e00d620103545582000300d0045c15a13008108103005048616441c180309080c40b0030f00051740c0c494810140b09900074041803100100d04005071a9548020001040012142d01224034544081e00704944500300e0308015000c000c42080b0f480024086801c001500f00d1003100c1d0101001d200c1042207000741000e40c9481008601401194090481400540203210060404c8425a0034401c01202c41503210300226695107018400b0b5812a682a80c1d245149820030740112107a03001400c2c0380310707190034400700148030340d4803070018140040c4142d0003800c0c41c4041c1c1c14000e107441c146480043c45404200401d2005100c501c1e056402107400104040180910b1925400200101c40d201c4080e9484c040707481034003075400b04909040f42c28204030400395000c114101929a00d0a101e448140741100428400400494105000c8800f45042c00109807009030007013030980e405445000c02484060398288101a000a0240c851481c10744002100d010007810510a0340c406000e44008020300d6449180c8 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 190963588 1250 190962338 190962349
    0x906090e3105010f021b0325150c08060108070906050901030e0f0303070c021201050702150603011503081e16061806090605070f02060f010e090703081209121e09 71
    0x10190b5204000f0400c1031348640f4880000d40081c020a4400010711b010f1110140001060710f106d400001c288101da145840c4843e885034a000e2000c8403d000f1081c41010440c85910800d08620a50b03280e000d01490a80001001d00e50020420720038000c19280030300410740c3c0042501c0c1031410a003000240c2140c084001858880c000070035034041e2000004100503150300604000e4100e00c20703203d41d14003c110001290980d2022903600c3c005a1000f0040c084c060259260981c00036130180000a0710409a5442c0c1c40704072050700305035540389000807501c2d0641a009444409a0100c020082c140f90241c07940860042181602424040cbc51b00c0301000e506c0480b00340498242c2d40544108846200e03450544050002216002c0110388411103a2000900100b20a8451000000b44e43c1c6640e00b490701c070701203800b03000e88140f0031480b4209002c00014032a00090801c08a03e03aa00440c51411110041c6400305000ba8580c0c0343c00280104068024804d271502d445c03c1d010915140c680403071801141 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 190964838 1250 190963588 190963681
    0x110117041112060108070504060f29090d0b1909050a0204020a1e0e0405010501030b0d140708030f1314010f03020903161403060606031504021c06060906090e 69
    0x10841c0104800005c4217000040c40100301d030710641e0244a180ea640c0c801c1140400d0714840c0c681e180307010004140c100e503240c80381401e40e00d00140c03649040a0326040419110142298220703411030010082c85403105c440804803000120b1a4022f0041568070382d00c003910341401c10030081c0110340210381440c506000724400350820704041000140519002001030400380d20505690003180f4000020640703511030301034642845800303000b94040991079038501c015541089001e4060380503041003c41c40c9803050000300099801c2c8004180ca455207280d601a80c110075511103c0b4045e1a0a2008402c0c0d8008280d2a03070f0300c0700c0341401a00c4500800100303003400d1a61707a43302019501c40d0070104203c03d100044200724401502250041d135504801c0c0400b51000741c8a101a030000f20080c101c0502d850380040c244031802c00e00d05900f407071100c4414400c2e07445a07088040441c0c03490300d0610502e548031300d15400504a4030080c51190404003400100000c20300300100400721528102c14ad5210140b180302d = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 190966088 1250 190964838 190964869
    0xb09011805041107060f0c0813060902281514160b0f0708180c060a03060b040b0a1b020a030f26030a0e0c06092407050a1101170411 58
    0x2c1c482140320884a81c5180d100d00000c85c0c5442c604848032130910014071071801d102c40940c490b0440c0703458080d244a884c8130b00315070858601d610764001c0c0c40181c0b0740d40101c014040300e081100b40104409211a03180c1d9440d50426095800e050981951860f40403511a1a500c0b45a003032945d1a4441038510b9040b90b10030b540a0300b40b5100304d050003003c00042c640503110304940e42d0340c1e0100e81c80f07140382c01004141d1048002c1c1a644a400215410710b0f01d4001003003100210f040009105a0b00e0b107002c440c6802c10303030000032402400303e80b81c250701d5008200710010288400030580c51424a500040032032015010181c5042c088c00e8041c010010028001041102201c00d440c1013060604200301c0b141c1e02c11180c2244035414087c200c4030808000071071080d00ca400410316410102a1818812202405204110560b20702140b013069410348000802606005d1000b900c02c151107810210119620041a10304101003540120514590a540c1c0780d001a400301c01c1601011110000403006840104d61 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 190967338 1250 190966088 190966091
    0xf1209190312050307111518030c0f0a03020d090f0b1e030a09050c0303041d0c07080403030804021905100f11030a11071a0313020406091121010b0901180504 69
    0x4050b80d0300d8106000d0740c41a10999650a4405500c4460507250140704100a1052910b0008102c0307090401e004110b00384580408c0300d09011b00c94520034a801e4400d445804030f500304080702421701d5818088400c0c010158144098054030f825031058400003d0b2140c450000000301c0c6003803107031901da80c0e81b1021401a003e0541c0320b06081080301c00074840703401c04444070f108020300805281000b04c1910111000160f40d0f031240b8850002800c00781c68002c3c04401041c004000e00c0700000c00950141020794001d41d6100000e191034414008d41c002c01907030740f084030f092038801040b45560b4030002200c008100d00e0070720b07807070000c0300010b03503c070040c1d085c250215000114022508541c403900765207000426804903100c05545401007071a14200c1c60f1314503505030f4100000340e0405080c00018070140d1020f8000100380340d03541f0b440b41c21a40003845c102403604001520741c60000c010010071000c04000f02d9030301015490444088081d01c1981070003410b1290f4100c10340c0d001100c0d814040d0003440013400 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 190968588 1250 190967338 190967363
    0xc19050702060f0c060106031a0118030503030711060c03160c0203070b0301083403032001050103060204090c110705130f0c0207081506030c0607020d150c020f12091903 74
    0x940c001643c00541c045040c501c6461700001d1070078070138000c0308a81d01610540d01c2c10041400011104070003440310802481002810000010f4030030030003507219940f181c1e40e03111b28600202d201810190090301c40055008240240407030b845004908041e0400141070a002d640014800729003001038035800703501c117914080000650984080303501d41ca00d4a00c040111440c9104a40000944604041b115100d01d165401480044c1c003a8490f00c1040f04080d0800c0d9440c00701c0c0305814207441c400d070012036080b81c01080c03c104201c120301413005241d19070308107251681000d611003940d8003110300c2098405c125400e0030b40900351140d030140b84032101c5401c0501500c0c41824019603643c503240314800b80b81c0b10703590900ca1050000b000c014003138403004000d03000307524500703080004035005280287c0e400724000000000042003082188840a03201c0303070205a1040c0035030080d0901c00b051643d1f4145130090f15449103242d912504039001c6040403201e22a001200c03d0282c0c0758030f503203600f00500e115007101 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 190969838 1250 190968588 190968607
    0x60503092a0a0803071709030a05061509071b0605190608010501031a0c09090a140f090f0114132301061809020105070f05011518050705030c1905070206 67
    0x409003a034088060700c0e0401882e40d40c40106a591080280140613451810303011403880801b42d004001c101002411500350440d2901c41504051050703e114280340210701444449050250650f54020034078140308600720600d40c2c2d40b02441b0030588004103c1a50346001074929040603e1400014108032400c00910351145807140c024082800103803610000f220032004403540010b0350501c01c88002610071704000451080c055020f901402a0040c5507d44480f180081814481c0c980301d1030382c3c08401c00b25800c084c0c0c034403410407101e8032210915906069811081090059003c1d07001017504d2540d0300ea5030603a040c44842d07403001040c6680300d441c1d02c1180d000c1c00141504400140d4060f2210300d010310b020b0f00d00e90b10850f480075034003e0109005101040c04120b4407030581d001e090040001060214101d14445100c090f56003200e464a000b02900b40c2340220103204040c0d1000b10747c00c0061460130000c9480101d03000b842c0c180b031002c100e8000c00f440c000d0321840507281c400e54050010394a4400d40c4 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 190971088 1250 190969838 190969903
    0x2606030f0d09031b0b040b130302040e010903030b0405070203090f06070f0503030a0b0f100c0606030b070207090b060702091609090612050d020705090718050d06020316090305030406050309 83
    0x6220a1321213900e05625054100c1d032204a28049600648400340342c00e02c0d151020b28190000c05490154840c0720a0000142c0c4860041030700345540d038000012600f569103030140841d01c98814407070042d07103004108040036800004494a40b5011100011140031060020341c1a11038400001c0c408268080307441e04100c000005580110030901047c0704030030050741231252000150030784a42c01180240c3c4440024010320b00c014072140035100101d8240d1b180c0d110002c0400042e11904016403280c00100905c0040348102d0400385000c5039040e290001c02d1700003c480d0000589070755260f0b5030b280c482c0c00703186000d06031100c02001200000e01036140d5502840310441c40d000c40c2558180600c8180181d541d10201d101400c2d1080240b0b401e40645403000200c91211f4500d03401c03010100b5292010a141c1d40b656600c0014510038500541e580c41c2210a44c14007585118a0340240908000103200050700801908c0650b5801d1619640f030380d4500000074580b0118000d041c4501e40e4041d800c070503810b0b02c1c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 190972338 1250 190971088 190971107
    0x4124031203040c0e04030801030308091e0f0c06030603120a021c090609050102030c10150e09060403030e0a030c080307261b040b0f0d020c060a020c010501062606030f0d 74
    0x1e81c0f9480511a42c564809200020468000300001c1c0c0c524014000a401408034076040012107044aa9a494031908a41745181d0b500c10001030b603000d003440018141c0100052000d028080c1c076510f0440c246800820703940c03000c3d012482e040c1e910200b40700d81c4851003000100e811030304890ba042041006940c2c041c0c50408140584070004801000100e0503500010844141e604124010501000c502000308001c0a03101000d907828460b2810000c1c0015040003c0c0303002e200440050015818a032070094212000a1112000380d000350465078046900f01c0141000c180d00180030701e075641c0e9074500c103c5062410040c0390222044020307281c03505030f0f0008a81b5200700382c50210741680120b42e806010544c01248554074444000f000307a14400c16141c030150020b25207007075003d82071540241d0514100a822200041031b940d01084909015070240645401401d1900301015503003101c0c0440c0104039001c0800301074030034451010524a0301e00b00007640300300380a030090340c01c0308094403802040300d0345 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 190973588 1250 190972338 190972343
    0x3070f0b041203050403020613030203040b0a03051015080c07020f0a0b0a120612020d02180702032508090909070801021606060f0806190609412403120304 68
    0x6660342c0c0c00c0700c1c9a000e4820940a560950010100c0e40d17a0114150340034484c4032011001c40c041440b000401c24081d80140600a1013038402090f90b11b0030740000c0001c07001d071340d1203214450001e207070076044a030f0050b900a400c54481042590342c0e610701d0010640d40d02048041e11f03046101c115000075480d03c40c0c4081c04134070400742d80d0243c1d400851003800003581c8441c01090a00c0394000d00290051030001ea040c02503901c0580b40070400f111009982d21200001c403144005600000340584100f00006041c0f41c05000e21003074000004d682d61200e80d60b90040340c0d442070040140300007007104050100400c60042071018003c0d0741d1900800e1030300041c268510421281a4248a0081000420070000f102a02c04040c0101015076405070308503c0115556518140c040c1d030f8110200e4903010030300920340d90100e047c8100040c80910000d1000080d0440c40070310101041264820b01401c2d41d554060f0030400b92000403407800500003807109007040c00b00c42107500d0310034044a281003071803110295225a0 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 190974838 1250 190973588 190973603
    0x9031109040506060111010b060d141b03060622060306060e0402030103150207020a0305011404030f030b030a0206130b13080c0105180126040b04050601140d021203070f0b04 76
    0xa08260038880400815076008046400010000d4100d5100303002d0032941550040020601e0301441c0045510750f845841c044050a03101c09158400035280707113a19410180110070f00444603c4502c0d0084103000c040c0c6520310400c0001500f501444200300700004035082c00c0340011040c0d0395018003800801c2c80c1e02c510340108010182d004403c3c607080c801c0c0c0e8100e80c2c10030300030b0b0b0250341e15101c280001c0d4002c15040382e020784104800303c0880d81c00d100307250210140801c8007407503040c02d080260070740d1103000409041600713100c129411610045080c00b000b550640750303180c443c0d201c00b2000d29841c12079080f8080c0070b0380105102d4441d600c0803500b1021250b07080c5c2950040c40140d401182c1d00c1c4542d4980d00c1c1000910701500d01e09503c205506080710280c800c08040d00c40b03000c0c9401c83d6180080d00e00b981c080000f0018003042c800c0c24081e0340d0040007030041c101000d8585030042804203560f0080644505245603139100302400a20449a1040d07002c03055000c24142444d0180500c0320984099403503c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 190976088 1250 190974838 190974863
    0x50712020d1d0c06040306020901051c0203010311120a020f01050408100603120810180603020a090b191a0f1201060f0f0f0e040906060302061611030a0c030b0c04080d0903 75
    0x140883c07800001c142c041c04131868103040d9160080030398041400141001030410080808034106440100c0c40c0c03074407080260341d9500d9800c080c00c0011a0500c0d59118441c42000c6840c079890001e5500301230307581074895005038030303024006991074011940030799101d000b58441214182d52941c00703102075a00c0b40300c01d00401c0c40b4079541115441d1049829461400325a1030911024140c40c8000648410b5450f010454a803294007146051180b40d00c00743c038035516110211903d151407812110801c0a024094480901c2c2000c0039803103506225008240c42c80c001822003092011004a42c0750003844241c0204650395010000d06c0d220395007420000061351840702d41c03061881100680b01405a0f5912903000401850401001b007030140000c5075403035a82c4000000507102c0e0401350812a0400101c0d40c0308204c14204203019940b5103e10314441e0300022035540000d02251051815207030010031440543d42d03100703140c55940c803403a0441100c900c29810700454583d88001084260f174456140950031 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 190977338 1250 190976088 190976141
    0x90a0605070906081b030105011d0d030806041d07060c0f0f0302060105030d030b0604210b0f090111070503030f1803040f1701020306010e01261504061205060a050712020d 75
    0x10f405c56225443c0e4203a410030041016620440140c0c092003020101c4441080d07045000030410404800114082401001000385920f040c1c810950401c46000e9410110012100066180d105e40e0007200103125081200130f06001340768402d6081c0325030110900300302843d5424084e6944400340b0507144680b1480701d880c05074602c6800f4450a2040240900381000c1c106000c02c000701c0b560b01c00340102900036489003000715024403040e500540303640f107011000d0706100011380d0a44549200940c120082044100c00095002080b00e40c450f0b40c506903000161502d001d40c0d5550120400d8001e07a501c408600802c00a860425040407518802c042031402d152500015081c2c0c0000c851880c041b403030110707a100f00d9502034004074011040050400140804020480c1d1240c10103441c031164105981c644901c042c01c0510501c1c015142c0101c550304801902d5403005d039100706c010801c6458a84030000704040c1c3c1d0040303451803000d40c1300392815900e80c402d44064100030080c6802c10302ca03901081070000039 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 190978588 1250 190977338 190977361
    0x60207021516121115061002032a031b01150504090b0a0f020f04060309050601061701121e0501090b0711030406080c16050a0501111201030b090a060507090608 70
    0x2c581501481c0704450840d0b01c2c0c482c2c02d54001800706041c0a01e42101d006034580500009808440140e0b000d001810083c1c00c1c03041d0001c400c0103c074250750080046802102e00c2c00c034031003110301490134402038041184070b403a42140503400d031600e007000c83d1841050990f4419000741d40e12108180d40c0c00741c140d50314010081591006503010b481c0031200d40c0030400c4101181c210000b41c00c150000545820200601e40f101c6038842da21000c0040d035925915801c1013014000540100704525000d541c0031020000407107030301d1061289051301d80386520008100a4188010701590b00150000941485142040fa010302040c8004a501c00c4840001a2031140103800708a56081000003c604003800d00030240c1d140c1c0ca01811a820f188400d118451440c0c480000d850044d510a00c040c01d55841207162513070035203404803510088880c0c10f00c00e0480d00c40480c0e00071811a07401032842107045c0c036890846410003c0300880500200c1c2868100320101c0d03049044030048170303e80d5807182d000d0703500e00050f0304 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 190979838 1250 190978588 190978597
    0xc03030106120b100c060b09090a02130204060801120c051305090c0102010603240603140a05070905060609062d041503020f0703200a050d03050105180a0f0b040203040602070215 78
    0x1580b01e50301c0d1168101e464890101e1424203403203904005426104c030307c0000c460a0044800148907480401d418045040072a0390400d201e00202055042c00c0c240100600b407248140140004114002c5541c0b0910035001803010003000098245c17070f46c103c0d6900d18070014041c2121100000c0c880c1524a040d0740d40705105403021a9082048420328400c40c585580c00f031019144400c50645e03c4900c00710102d031030404507009210544d00107140520180c41c00c0c03818081c4503400623001c1840d1804000881d103519049584141045405a58401103802d408c1c42204042580c5260364544160403143c000d154001001038230301c130741d020201200240c40200c0036403195207076680d0b108100380300c0c54000a00035421041803256908504141280c1c0e03a00c4145440c0c4841c0040d42e050703002500c107094103505441000c1c05440141c07980184200c00241201d503012018200d8074080e03603107900b050500d440e141e1010710910030080c070940d580c0c01e0608060300039410501d001e88c4206c481d07c5504004007507410840c2d = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 190981088 1250 190979838 190979861
    0xb100e010206010323030c0d0207050d0b0a0f0e0607410a0203160b01150c020120240405010605010315030605150406080604031103131e0801020c0303010612 69
    0x24080c0c3c2e8256a1205484081c1d42c1c05088403500c0c4601101c107491050001c0c05a240e00d4600504484843c0b040007840e21301c1d00d0f0702c081d01400d218401074003c10381c2040700707aa0001c100c410120f0000456030706103008111555880b1b00c14000d410074401500c0d40115034040941e0340b20b4000d0f07403500c007000c0d8007100e50300c9150420146c0a4200d0200d20180c0002c80600781c00c0909005603401e0800d40b000044c0d070740c50a1441101ca03100c4950041c8580074462a040e203081000d443d1035240b00c0c2e0f0f9603001030316490300c18806124260980c02c90404004040040c00740034024030700c1104180c1c80c00d0070b14074908402503e00f110f19500f04240843c65511a1003285454003203031100c00345d06403554964030300501003d081c0c0d410007102203501c0c200540b954060340b0010141c1a00408161a05040007054084110501c03000c60b00208005d1405800c21240322040d00d8001541c4182c1408031803580c19036007019441000c9a50002c80c500280710401301c003030740c12070384207444001a006e500c98001c0211220507904 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 190982338 1250 190981088 190981093
    0x50a1416060309050313180510060f032a030905060f090c0909010207080403140c04050c0417031605011b0201020403030507110f1201061403070e060d02180108010b100e0102 76
    0x700a014420b420110702e0b2401007050301d18100300e84c551880300030b449401c403592040c284500e80c0c0c1103d203548506903114440c4a00340c5071442c03c0c544014591301403600800d00b01a1540d140e0702022118070344d02003100301090103841c10106081000b8001d40744180c4140e649000d001c00150410489090003071051580c840070705841d4800707204000844101420ba00030665080c0040360000b5140c1d0010000385002d42c03042c400d101e282d9140d01d827410100903401c0e8000d40c104403d1062a4194005030340540e0380070b40800c01c002820480e1079186025400e5100c00400d102101c40013885070660040d40078003000381555510f400404000d0303090707100c6c5201c018001101003060b0340210350380d1980d0290401009100104150318800012200380710601e034880c03a6550b0360420420b0100441410070b40344016805400128903203030b229503081d0b41c02488030b030041001c500418115901e13007503401c4903030030400e80144007540c503842201d0090507802103075030040301250846e031000c6005035030403240700c08140e00 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 190983588 1250 190982338 190982383
    0x80609060c0307050d02040305070504050106031a061804051302040b0a0e010911040803190e010c020607111807090509060409080a030c02010209040608160e09191e050a14 75
    0x8031861070b40010049020040103100d10054903032580010001180504010311505083c0340400007200d0040c2d121009040c5459904a082c0019514803010900115150b503112814108241e80d071441046039560701918007000c100c840e0500e0032060320340a00aaa01300f00c07442c0501d0038004610014000e9002c3d030308034003004012580440d04110b00604004004038105942c9501c8603180d40c000f02c040440000b4585041446207500101c2004854000d00e04900c0b82c40003a000310b503151050300b1000c2e0281020b2840384c0a103445901001c01d9809081c0b1000c00c1070f103050032004100c40b0040c05001d21601495000c14160700d060301aa0f0400e80d044426540b0b8050160310a074003c0601161000a55400340310000c1c055845109160080c0701103030140901000c40030340448201040d4114020350750300351701441110030000541c00540c0202c40440700e08000b07642092040644a607803d10446218a140142080000310311040124412540c628200d815040c0c183e032125052040c1c400c03404030041 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 190984838 1250 190983588 190983601
    0x50c010513050a081e0a0203071106090d060e03041a1308011a0f0a0503070f09050a020703140a121d160312180e0a0c12021204021302090a06080a0608060906 69
    0x42c000d201c1c2c0341c00700464180f030070010b280a20b17080c0c2008444001580001c502d400a211100485081080c411103000b8a861440e02c0090010480044080c11880d03881204454015040080b213029155401c544507404001040e001011303404240b102c40241e1010344001111401401941500300c034020700c2c0b0b0b80f0390001c0d00900c24641a0603803003580c02014158001240d44050102c48c0103000640590b5642c0c13400c0c40124001c5c0c0300003504c1000303901e10400061012950101ca11309014040d00b41c0585d440f00701d0401103409120380944500c441d40b600d006440c003040c403240154881074200c020b89008000020700000180390610005d00103080c0304103582001d6114030007a0304070107140c081e100e03105502d40315400145041140c01510960303581044651003a00030541ca01c5402230000c05501e40350b03003810441c200c038902420081c042e1a0b80e4005d510140116010754171f032441d000e0581ca1200b55210401007588400303488112401d490044d003c150041e001c182180314040010041465450b0710 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 190986088 1250 190984838 190984853
    0xc0f030606080a0e0c0d1209173a050304021302090f01030e0f0715080610170a1d0a03031b17060109150e100f0c030c21050c010513050a 60
    0x8803c51340d9a00074030f0f038180031aa0783c071100c013800c0501462034010304441d58900a403900c40c80d60460b5080841103207140c07e018034002107080a6040e80583d40b00250800e00c0401e6040e422041e080309501800641e020885074040059481180202c50715644140503030000c01c2248141024603402907051503001040e54002e0300300c004504207000071611840c203104041d44c280300f81508030001d074210001429a4280c0c0c40101c05402180482d182c03950f0402c81c44000d481e000745071040e60104085000080d10412140d4084e0f1051086d1500203061f40034800c003100e403a8060660120042403408150f80010800c140320f2400680075a1100d48a4030346d49221046085070040c40c440c10404207000c0800e290303e02c8a0781040c54195074880f0849400035004004c0915141050b0b2030030410101c0440840e964000140f82d03100b6010302380a100007a00b4240b0460a40c860b400d5100350311400300b100000b0b168804010701b040d42d00400204840c0d150300e08044652107540c2406020750b404854141d0115108 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 190987338 1250 190986088 190986101
    0x1112040222020304060b01031e1107020a171c05092808070e0c07020904030c050109050601061d030313061101090b1303080f040c150905040f0c0f030606080a 69
    0x512800581480c1c1c1400141c015545108010441c0c001c03080c403040203180c1c0200480482d003420280300003040c640c003000003156058844800103480e540180001c0808204459100d6005058412802e403101e00c2c4112100503d0010a200e00c00c0c1d60004086640901a64002d02007659400349480044410044149c8403280d0600d8035003001c480d640103050740e1001c00e00c000c013054005042110301d490711035855140001c1402e540d600040100e40016034031840b07a9644170f507240c00c1c0004c4452060070139a0040c0340488009100b40f01d0200049036081e0044004646103030364182140e10510603030103064480c020b24490380c10700a02c1003814001180295502e100610001c4c000041140c0c9075140c8013001d40c404d27500441d002d20a90703080c00074141d0010130385034010845003600440b4107250f0f490740300141e078510890561300f45400300b0340c001d144203441400007008002d10a12101000b08003403402040244c4607000030070300011035081d01901034007618046450a488440d003079074510312904003034502c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 190988588 1250 190987338 190987343
    0x50118060917033007110a06021c050a0b0f030106030c090c021002030a0204061d010207051315081507110c0103090f0b04060617030403210e030a1212111204 69
    0x418414030750321403114049445840000e101551441d511660010101c035030141205c2d04020221001c03d02d54000003510244144d0301c01d01c016035074800c41d0310050b00030040141a40100d810b010a01000c22507035084000b8550046031850b030940c181c03a003014221500c0b40720003803055580c503008002038000c9900032a20317238900380191a80504d0585030301d02241c0c012600a611154086424440150700c4001c040c100400c0340c009810441c12000003035601c865078481c41d03200340b1081c018080070407825000481d800e55044500d051468813106400d85508481480800f50000a80003401d10761140038450450051100600580e03000500110043c0014540c10b582ea59510044000002e07451500b40340318a010700c400249a600b00f0861020386408810203080560042c00184041118204000002c0640804e10700311201070030360942e4000c0b6040400c503454003a041c40c80b410b0001a80e8611500300a075510420045500c0310340d00203c6000801c49241030809000c610752007080807645640050 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 190989838 1250 190988588 190988593
    0xf050301092d02030a0312060515070b0a02040503030703020705040c0503060109060807022d0c060406050a030b040f05070f030c1b0b0a0b040e10050109020702090f040c120c050118060917 82
    0x2c0b882d402091a0901170541100001e040c0c010807140395115104000140504848402d03906003c001c60131f140d401403902c082c00c80c40b00c290118440395160b50450b40200720280590340c4a80b180e04029481d28843e20440b8010360506211201c0b0030710031401c070303072080405071503045205050041c04c40e5004401421002540b0079101e0450b0285104c140d440b070010503540145c0e0940b03180c00d0b921401c2120419206000700400d10050002c0394006003038521141103850b00040200f52540060040c001c686040b900d040c3c540800d00046690000031401c10b5560380c2c03002d200030070311820101d45000805601101490100101d07200090b00707050100e0300305208590224010b500000042c00301c50800c003000a080d880301410b1f280d010420701030140100480c0c4811810040d00b5000719904c8503008002c0001d2741d0114000030200100c054528005c0e01c0003a4810808402c545040c46101210b03010b207038041000510000d42080202c800002500c1c296950b1044040c039210204c240c90303069000320030050 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 190991088 1250 190989838 190989923
    0x7140607140c0a151701030305030a15030803010f1d060a061101020c060c03011a0f0d020a02150c07140c0d030f0e03100f06063002041706010f05030109 67
    0x1503540b264854041c181d80714413445800c010903406400000f20509510f5030550081c010070202c0d42180680798056110240442c0f146201c203062010100f2940005004900210020a802d02d01400c01010341e00d0400300041c124400204160072441e0403903645503c180d0485083c4169485540188144036580d0300140c24551030b1555a410500b0840d0031004080022004100c500c2d00b06500d079404030401d45a44d490100d0120304880c0c02d110300000c02e5001c0d600014110900352080018140311100c210007400142009044620103602030b080648070b220494000c0d0303141d884049103001b408032006080c0307040020380e6601540d0203c00001c038402030100d002c50244141d1400d205c4040b82078028400000d681d0143da10240071964242c10030001c01a024140c9001c400d0707a800d00445e94041220350801412060340c00c480a03101d00d4010000c07081001110220700d41000600505076104542e40123001e5880d401494202c4000034409404e01e50508003801e44120407000034042080c0c401c2198900 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 190992338 1250 190991088 190991113
    0x602070c120f12090e0412050c0706020a02030c180402010c150e030702121603171e0a08010806220512160501051b03011503061701020901020714060714 67
    0x80350000a00366225403840724102d040003d40141040f4058240c2410004207080c5561403201420040000f05000c01c00180790113101d005200344c4605a40c13203000c980c07456445400094440391a054100e0003880381c0100003ca074540b00303085080c00c00500c0e03c0c155190342c440d00112780c03428400105456a4810500f007a6171510b842c022036a090146400960361005217106020b0550300004011603586c20160b490502d40f1a04482c0104590b0000d010001e003003900c5900c0b110b140b00d41134030f4240c5000c000000c1030984401c1000742110f49800e466403001c40e82d03200300403504c4e03450807030300d184050ba0112480c103c4046a282c036001c100c1e000d6011600041014001e01200e0780c080640c1d00f03541008822141c0411000740240e17071340407080e843c03614100c034141e0702c4240c214001030041306e045000c0c0103481da0740c1070b11907070140008003114207681c61074100c5100014002e40c00310442a00501404201003030308051b0300001c14030003802402d654680307042619400d2407004a401075407424095201c03012030 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 190993588 1250 190992338 190992359
    0x4050a0f0c0905011107050a0b0a0201060509041a090d050307031d0a0609050708030a02060a180218071b020a031412030c0d18020d060b030a050f0303090c0a120602070c 74
    0x4600c1c0c025190040803900303010024100d0b40c4d00140c05c54180d0701c0400309005503290210404122003040b010580c0ba004030140c140d001d8941c0d80c10282d0440c400c43d00708014050f544613903200481540402403c1921040c03409902e64400d180d001000c18420001b0410051295020b402404681c1c02c6c7c003191030498460250600000f00c00580d04103071100d0300c82090250910a0400801c154001145401c0c4113843c042e454040c0100102152540c8032031900017100c00c0b482c2c05075115401408095080d50942c055400a84183d425174001401c24030101e02c000030035020350b610240c00500501c116441c55807906e1022507094010700440c0030380d0f02541d001b024082c1c0514040e04044046a483c0c04002c0f48007030413240d2007803600c1d030380c00315210110001d03803260398030045196041800480c003c0b1700480464506580988005d09904c0392403424002c0d524040080d42c0213001c0101a2130780c2d04c1d0f504003041070020250040040c15040440e020300042c0c0554004c10000380f04000c0b400d00e26903109918079 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 190994838 1250 190993588 190993601
    0x108131407050109080304030b040f06090203060a0c03060504061202090a06050306040c05040c0801050906040e2103060301050105010906051209120d02030402241804020c070621050c0904050a0f 85
    0xc59014400c24002503811400c52000341c110b01c0011800d140c50354842d0205c4031400381000d000c59910f24018406c2c000190401d403012074000d800c03510a800e150405400070b016003925000001e03d00a404526480d190117904210f4070311403406d98415090703800b00600c50381c1c0602401191a074442c80000c040e18181b05c000c1c841c3e030040c5404030340ca40c542020301054171124000d06e010440700d48014060340c1c0d25084003a0f0802d2064800140042c412003000c0c0c545101c01084102001040e000301d8040140c9100962103080d00380c0003481241d03620300044d1040107090041b84003203101802600e00d15002844020791069030103044648020390300400f100300d90f0281000081c1030f5000000c10040d0704003503140307410180a0300790305c0761041c40c2d240c1880700500921280c000440820072020304035948540582e0b40082100e0180c94076607503034101c081d0800143d01401826212903010030301da91131061043c244240d41d46c401d401d00e003030441410400101b200400c490001640d070508509191030700d10506 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 190996088 1250 190994838 190994873
    0x60406090905060f04240b0412030309150f090c0506030c0a18031b0602010c020601030c050f03150c0901110f06070e12010509010e0f01150308131d011409060f010813 73
    0x81c1c682199032003014a860545030040712010b04d0408c001c00443d2503040503d20019054500098604890320f0102200800c40ca80c03000001d0800d04a032170200c44680c0302c004413902c18078010b804503a680090214502048522008040084c42198440c2d8010500c445810f0b00038942a01d5040d01e03503590304902c84400008031803000d11203138140038080c0c09116a005807883c0e0300080040350700d980d44030300484446004090241d56803e0b69400c01d43c80410400001c84148981042c3e18681042c90410319044058050300003051280d02c6c0448020119121000c0896170f070140c0141d46d1610f20590f9070400940510f03421944844214641200c03e110751401003400c00004207070340002801305450300041e01100b4007964901311040c1240a4001c00c403404595100d0002c80e01ea1044400341c44813050b450348051100d541c008070f000ca01440407120141651002e8507025000c161003014032098a40458034541c021203094940c200b01d60284042503031011040f00c00075409080740e40c403103100c070300070050b0b0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 190997338 1250 190996088 190996121
    0x30c01020f0307170622110708220e0a05060a0302030f07030b010501051216051b10050112050a3801140103021e03060f091302040b060406090905060f04 67
    0x40c483d080780e2107000b80396880c440f201031038450704020f800106a07003500540c00c0d1052042000c0380400f100a074000624001d0340e40621500c4041d1070800f48841e5112080c00c0c8040d0707440007444602e03070990941e0381c019140c0300007034220b0f0381d0f41c1c0d900000c00820004d001e07070303a00115540001005235010000e03104d8482488000d4580c1c81d1031481c11100c103500c10307008281400814001c0075402c0f4a00140b40390311204001c400c0c00c40c01340082083c0d6039849050b41403c2c0e905100c241c00142c01500242c2240c07540c843c1502002a80e80c1c40d5121640d50702c41b17000042c080c1c0c00081000c000b081c0d0001c2d8a44200e607002180780171212900a903800c181e5101710700b003110741031190300402403090b901c1021400d4040a08042d032800042502c5003441c61a040303003405a448010010944a4030303522004900300794054100d00c500d0410101c48680c8540000c0200d00c2242040c0302a00d070b40c1810420754085440580b00c44080608050303041c0d01a00f40140071b81e4000c0d6031118507044030355440c0a01a5a80c180c00320 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 190998588 1250 190997338 190997341
    0xc060f05070c0605060121020d090c0e18010207020a0510021501260a021c0c050d03030509370303091208010509160e010503061809061905040f03050705030c01020f03 73
    0x24440184c074401001641030012004442ca0002c421544100840207140c5d03005940d800240740c5840200802c0e130001e0040036400d440031a07890041c9171882d000d001010103181c20032403010344040c241e200d00300009400aa80d01020021414074a2109008864900548030b0500c0000703061204030200342d020200e003005580301100e903082185070605001800401500748406690003050b00c112011a50740000000c1e00b0340702d420f00c125a40e0510107020020000b400e40c00050030000c020341401d03901c034a46406204000c0d050b031044c280d0031401018010f1400c43c0759010700740601c081d06107004c1c000c2d814151119410000119415460f034041d80450b203540d6281e505010501c000218020b080024020200360710302d0103103070403801c2100709200c2486e0080c1d41b9550a0041b9440d5400050510380c41c00d01c3d0014085100c00100f9a1417089143d50188801082400394101c103452042e00d01602e24a42200343c2000703e0f114400800001e0300420032280780c001e0010003182203174001901e072440c4040210 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 190999838 1250 190998588 190998593
    0x21209030d0c0e0a0506030402130c05090a120b0103030302091909152c0402060c0609010506091b0301120c0b0d09021309030818010f0603050715030612030c060f05070c 74
    0x440c010582140349050031100c0c02c0744021884c40956030103401e22402001c03000504542d220940d140d800c2c5101d0205010741030655401401e80d40120710b40e9403183d04241c1000c00d00c244072460b03244520b07070001e060142c030740d281d518150025400f0143d042d40151016192084003103001d9558401042d03007440001b6031007041d0301c2c40d2010041356000003242070b00c50701c1914544443c8d0011001030603250766043c0c0f026103651002462034131802c0e44210706c90080798104544080c0644c441e61156900752462090307075448200c0c14100503844040c9221081051005004103400440350108c414852000d40d01c54584980c1c440300d00350018000303490102e856010020860814491a82d4002d00f240c134107000303004441e43e025100e00c0006008468014480c203440c0d050071000d4102d05e0000c44041c4080000036100c1c10110344810707260141640510010084013101c034440d00c038079400c80303108040d001100340090358100c0390050124419240240c03640d0344100b0100c0e00d0300c507003805081c15444407a02c0494a1 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 191001088 1250 190999838 190999841
    0xd030212130f14150d0b130203070206060405060a030303050405030c01110309010b0d080f0d0f0608010f0b030706022d06190c02010b03071403070b0304110306160c15021209030d 78
    0x3504403280f010000300d2000e400f9140c1e130100303d588101444405880309021070490b4010551040300a62004d8442e0002c031400645500860140940303a080d01d04690301d003c01d2000782c0d402550150b4010070320940400c0424426402aa0890300c600d0a403860191007140032800d40c5d500040c4900e6031813001080c01000c0c40301b485509000d103815501c00646000039251003ea50143c3d00540101d44c8000a105600c0c284a500000401003061420000b050312104da26008003020f8108000507807070b2482194062a0014440c41150b01960040c000891942444a030030032200b56042880910018101e1010700c2c01d10603d0b10400fa602c804507200d0040c003076810f00703072a056403000c001c0da45401424040d0341c50101d2103100b5105401038041c00714080b8000b207403400c10796074042c0c69114008814403081042d012032004480e5070480440d201c41c0c94803011040007001c3c481c2200301150301c003541c0000060110700112080c80d040d40005003403145d0700204200103801142c9411054100050824060b0102d = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 191002338 1250 191001088 191001119
    0xc0c0306010608010506030a052815060306080a0f0206130801140c0c1e0a0503030a14060a0b09040b01120903081902090919020f04180c050304050c0d03021213 70
    0x110f01d4401c003994540f5001c81c0440c4000b610b907807425a00c541c00603640d101d186175100000c00c4000300c40c1861018240c045401000710482101494054141c0050114464003800342611041c001a1095200f90741e81c0e41c4851203006001c81c5c1004050000521000c21240c43d48010503400c00007188114405864a00402000700900380c2c03204180100c0b510110000340410420280100494800340404d0440e8681398030842d000b0601d2000108100440304145c1022518800b07072003642809442d003501700300c0e003c0910f01500703c0c4040103101560300c6103032a8202e04404034042c10b003802203403002130303085058560525041d07006c40c450005000c000750740404003001040c0d001c2021030400d11803c00048001c0c0000c4c0c03c0000f8071800038810000200594100c0d40c0103e00920119039541e5200d074030885c80c01d030103003a0398810303843c2c01d809094081c0648202da11690340304015181e0300e0040300c1003240070ba014150075011031091080913965207040b00020454401000100a6840e15244900300031100 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 191003588 1250 191002338 191002349
    0x60705030705090d030905041d0606010f0210020922021b0607090b0d0e070807170304030807020415030c260106060e0d060b10030f050619090e030c030c0c030601 71
    0x410401c10984039407020030340351460000c80d040c00d05030b6540d0404440c00c6066810050344540303440d440e0800598900381e98000003642c0d0003552183c2d6a8580107407049260741d110040035820120300a8030606040d4010404414000e02002300ea0414480050441001290354400e160340002e590764001d5002d401080c080c88d441c0000c00061800030b6006007003e54904c0f50030b40310b000100780a11010827541100707500c442180200e8175140e50356001c3c81d0780d66043c0c0c0f00f801c00d190750791200201030000c0441140c0c20340341c010100d10315105482d801d000003043d41100c0091102c004000110001c3c28101054004100d00300615034444080715808110344401c2e10103030001da140000c100482138100d0a5a4070f4132000302c1d40f020180c655810684094803070400601e03030015417034501600031505a4008046112885402c110607075031031050000000c3c2c8000140744426000c1d0b010080b2100540084a4000025040e24101200d0708002032445d00f01c0046551581c21a000c0440c01d0304042100c18010003 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 191004838 1250 191003588 191003597
    0x605060d1212090602130302090109090308060d03030b0a080d09091407030c0215040c0e0a1e0b0102070f12050606090f0403031a060a02060f01122114030109020301080607 75
    0x241554850460001000341c01080c000a40080300c02402154050200190803513819551080c018811280810325030100304d00c40e488580011405030300910032100c59a507d80c40e1840d1603124801000011200c40008500b01a143c44000106d5121040000000e0001500a1101c154080c134050580310b555004025094500409808409044084140c01c4034182c1030000f41030038030070b82c00c909000010491403034004d8034800f400100b00c0e100401c4000c9801c842d048011546448403840250341c58201e8690707800f03000400300c039101c0c5820b0344801c607440d07414011036020aa44116070001a010703580600201402d050544003844400d0014580c04003040b035044001e444c0200348035410010182002e800c05a1700c0d81405011548241d020014000081096845000d900300003580d0b500211501d038040d0360120000200307034a074281400c0314184e018a000d2408034004101c640400140c00d801000c01420318400001c4012100042d0b02a244440016030350f50b040c060150b141c600c0142c121820131 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 191006088 1250 191004838 191004859
    0x90c03010b06030412050421050d08132a0801060306150b04030308060d0807062301150507170a0c060b010503010302090c09040b04020f0702180c1c0906090b0103060506 74
    0x241d03a42c10841c0d0340103901c60783c0d840d6086456401104c85004a42042400c403220900e075885d40c0c0d003051980c403c1e1600c20b40c201d03005070f030303540408a03040081961083d19155819201000007032000d22846c09000c40d140c40301801040c01c0416001e04003041c0c0c44002681d6480360107101707020140c01801d844d800000010702d01645003000e8031007180302c2c034070004d010007030a074010400d03698840c1010800950007642d010380302c00341c609000c00240710311444140d07c8815981189855081005414120b520900115511050440702900c4d9540600c40840d880700181c01c01d070141003a510003500300309055580300d06001101c0e18000c0c0440e0b8804400b075042c464180010401643c5014800390300801c5501950703107481c14003002c200505078040085d0350150002c5603031402c02d401e11000c0c100c614021214802c02e41e19020000c40006c1c0280e03002d0110700c030b04204180c1c20001501c0b004107403401c40480020750640907260b00e006c81d20030f02d0b801c036107a282c000010002c0c41002d010f03441d000802290035003900c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 191007194 1106 191006088 191006111
    0x10b0f040914064b1503010e0f16050c0109050718110403211115010303030506030d0e1002070521010c050c061506040b12090c0301 58
    0x5840d4040d481c0c942d5050070002d1400c80e04001801030001811603816160b41c28130010540d144041e514100e03060b41c4804641c078042c02405c810841c0c0380d5043c00d4100c660100042e246108803640c40042c030074510703031540b6a08559013146c1401547c40c80d00040c0d9501400c680e41d0302410310f00802c80e0004014600010000100940f1002004030b9840e00b034800700c06001e90701002d803140c01e02c08c0180c07030030201940700b1002020342810300d0044650011079180ca0f00d500031452860150400004000709909401039070b41112045002d084034041c0100d0091840d9000e00e01c86201e080c0b41134036000311074000c3c42600081e18000e4070b1040c02c0802849102480501400b506446628050010002d903200c2c2d81524503410303201c0c024021a4940090084040f2855406503500007010000021840b138403100030094442d041040480520341501128108115604210700990410100f0f82c035 = true := by decide +kernel

theorem cover : BRFrame.Cov 190827338 191007194 := by
  have h0 := BRFrame.cov_init 190827338
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190827338 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190827338 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190827338 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190827338 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190827338 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190827338 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190827338 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190827338 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190827338 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190827338 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190827338 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190827338 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190827338 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190827338 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190827338 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190827338 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190827338 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190827338 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190827338 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190827338 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190827338 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190827338 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190827338 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190827338 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190827338 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190827338 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190827338 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190827338 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190827338 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190827338 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190827338 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190827338 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190827338 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190827338 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190827338 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190827338 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190827338 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190827338 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190827338 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190827338 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190827338 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190827338 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190827338 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190827338 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190827338 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190827338 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190827338 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190827338 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190827338 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190827338 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190827338 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190827338 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190827338 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190827338 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190827338 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190827338 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190827338 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190827338 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190827338 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190827338 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190827338 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190827338 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190827338 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190827338 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190827338 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190827338 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190827338 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190827338 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190827338 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190827338 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190827338 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190827338 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190827338 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190827338 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190827338 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190827338 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190827338 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190827338 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190827338 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190827338 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190827338 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190827338 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190827338 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190827338 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190827338 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190827338 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190827338 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190827338 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190827338 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190827338 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190827338 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190827338 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190827338 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190827338 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190827338 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190827338 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190827338 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190827338 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190827338 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190827338 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190827338 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190827338 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190827338 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190827338 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190827338 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190827338 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190827338 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190827338 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190827338 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190827338 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190827338 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190827338 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190827338 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190827338 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190827338 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190827338 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190827338 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190827338 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190827338 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190827338 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190827338 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190827338 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190827338 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190827338 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190827338 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190827338 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190827338 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190827338 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190827338 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190827338 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190827338 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190827338 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190827338 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190827338 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190827338 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190827338 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190827338 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190827338 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190827338 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190827338 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190827338 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190827338 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190827338 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190827338 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 190827338 ≤ n) (h2 : n < 191007194) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
