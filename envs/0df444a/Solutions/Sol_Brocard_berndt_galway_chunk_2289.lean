-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2289
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:15:01.200977+00:00
-- url     : https://prove2.me/submissions/9cb44cd4-8603-437b-87c6-a94ec90d649b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 411510791 ≤ n < 411690647 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 411512041 1250 411510791 411510793
    0xa090c2a1406060f030d020c0d020a050d030915021f020d060e0a06050f0a0509040b07021908040305070b030402010c12030b0406031505090607020c011409031c0807020309090703022109 81
    0x143c20b1020801c18401c0880840300e21a41c060b2514124040c0e003c03a166402480903a0341d541000050300c00519030540c141c00c003d421038030180d1004181580404810200c070700c0001c0b41c1600d00301c2a84100d0706e5004115400039500a0304000703030764081e8942c1c000e0a0b0710340761420002d203454135000310320f46402c400c0d0351416565480304400d200b286460768040740301010482d640b4107e50b280c0008260351420082c406410b08141c0d40005001c1d5000340302c900491a0b08000b1800c09209600e0603d0072900306000030386151141c0000480c0603081c0100f241c2c0035030303016100c4031031076800d0703540d5051000140d0108078201754856445500301c0e00e0324000c00001e1407003003104c20b0050004600d03040031188000c101e0b03003099101030240441990003082c030b44000c01c0f0030300c3c04801003550381c48464003501c11b035a10140c241c0714102e840014085840210340d05408a980d800310300f5100e5040490340d900440c9030301d50b44000014003050352140280c0c002e0a403010040000c0410030f4800e4900c4690140403600240c003 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 411513291 1250 411512041 411512053
    0x904020613060903030f26040f12050705010b1507020909010608030301030f030e030c150d02120c210103120e120f01020a02010f110a080403021207110a090c2a14 71
    0xc1542002004111031351610302194000311006174207454441d0030801687c026500380200d0148900e100d08012001d40140d001c912188400000400c2540040000e032815464060300607124501a4400700300c0e1204034074040d0500c0c000740c00308200800302520540c0e0540d0f0f1108000360760720050011b14000c5010344002e00c1601450b080141071260f480301c4861080d00500181001341c0d440405074017840e03100c25045503c9803e007000c184002e10501c6042d4404048440800c0040d4038081d00402900d2050100c0e041140d210411680b404002804001c0003000f0794450605410701c034528880c0b00e20001442103180040d4105580c1c00c18011401c003620a03500003a00503180e0741c09001d4100b01c013624660822168003131410f02515070140314500c408102c0d0360004036060501c2000704c3c000401e0401d075a19039490705441e0120000e0103d8003003500a202c11000043c9000b080d10600c881c1e000691909a208190480c850a405110198000140c8041d025090128101800c60711707280d2004402010 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 411514541 1250 411513291 411513293
    0x312070e01120c0c03110705060325020a03080f0a09080a09031b050a03020d050102070c0e100b0903030d09080c071d010909080a08060409140102120601021b0904020613060903 77
    0x101460008120402e075081452a03100c0540c04245001026054607000240e8030701251185d0a1101c90341c08140d016030040309010b07040024a140040b08100c4848890726501c030b107841070b41c90301c8156201401054003200041d111048240b8947c1d40040f09003000940030115a407841010f4002407100c10000352040028000c1016408681948902d02102e600e006403405000408810440c08001c0c050110003151000b040005d405036060b0990005144104079210494440b48010490300310001180764a0b0000300b645074101161103040d809070196190210707540004003c0d200c0584221780800c02009608901c450a01860300a0080f403141d02c24118415a03800e03202c59410b0f0012620389181c4080c10001864940c21551140e80c9818100700595400000800400c102c400c007608440c4021010094880194010070780c21034114101c8500c0c0e11fa02004a80d214944803183c0d9500c440510340e640103141514109074860f1004140a00c0c180e244a42e040e5030707143d2944100e02182002030140 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 411515791 1250 411514541 411514547
    0x206310c031a0702060610120b091e0105010302072f09070e09090c0d150e0109030302040306140402031b13060806010503240c09010c050f0705210d110312070e01 71
    0x75801804510040117142040000508000f0380784d041d085c1840015014032a11312103e0f0000c445d08400109040b1013444c1c001040c021041c1400c180c070781288003000000c10550300a1090341e4000e500544800f98000c0703200c1698900317800030881e0b44603401000c56001816036800b402c041c450055a80c4070392040307000f0000d0041d1814050540491504240d400304001c0c2c07111100b800c041303604555042405043c5442d2a4000c000f480383c0c5000701d50a09148030141a05a0020411284500c0007004441005d905441c0750080c01e0306e00031b516030013038214102c82c0e0240100b04403198100900c8200c01c0c0c40c0b08412003040b21714907449541e090b01703c81d00402041c40c041c05048103000c0e0b14000300072201440d403400100014010100031074048045110303a00350b48103510170010658418122910001480c90065981040d44111031203451480009138504508400c030342c8207400480c0043c58554214a800d0340c442c2450000c2c14010720052200c0c40c0415405680c0a000e1030613078aa4040b0001d20348001 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 411517041 1250 411515791 411515843
    0x60106120f0f0f180f020603072703140a05070513020906031f0509071218020d1113020a020712240207110d0f0b0403030615050306040c0206310c03 65
    0x201c6055460240030f007011540301c445e1044416411a000c0b5030703d507035403d0192000c07011416041d00304403040228034548a451006802500e005118000324000300030280784e0740c0c1502e080c00030324581010f10304000c1405c20007124010184512009418882000041540e580007162aa103505e05a03800d101200d0007c85c00304000742009690240d860319000c10041c100034030001580c0301e22561072440c00b03507584e20b8003001001c240d801041559003c40c241008421016091015132040e00140d1214100503003902c2156007038121500a890094684803102d5901c624941c1c0070b07200510f000803c1200b283c0e41940d101403c44e1861b0b40140c40e85041d0901842d0103000c50701d84d81c002d0300f0060b070050104030030754003180781907070300129225180e912881c0447c060082d030760105203890500c40440c411990004003951142905a41c100508250b81d42c0481c3c0e1000190341441030520300c44403071019034151700a6020440400403038040c0d5490180d54002501c2e1041d8011381c0e10000210380780e610603847d0244 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 411518291 1250 411517041 411517061
    0xd02040f0b131d0303010e01031410180201080c0c0706030509010b0a06080103030906050930160302031006260c030d09051c02100309110d141c02060106120f0f0f 71
    0x1117041d50b060000d03011503180180406400ca08480c44c45100801d81000840146a9032840500089100b04202118800c0940007203020801e283c00007544401e00d54103540e001c0105030000c21403546000400d400812002d08844180c0d5220070944000d5125907031500d004080c00c0d9143c0701c1c50340c0b40d403c00030400d1b0843d4010340b0801000b0400c80138195140c3e4550041c40074001c0110407211822034104403004c912105146050041c42d1442086030302c507510b4402264000d03020344403905c00d1a0542c03001c907080c5d40904c121241c000d8180141c21184104d9041d0310b001c0300340488070500607001c0080d183c06040024400001c1c0c1c0422309003d03d01300f407031005180380007510540110084c00d90004945043c810150420940d03101a52b00a1100c1c0c1c0081003000000034042d800c80a586050040202910a101407800d1044912003c4a00071140707881c4460703409c0c1d43c05410541d090900c1255807002411040300314640b1008400030074000c40c0700b40d00d403181481000050f80010480702c00182c038034a400d = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 411519541 1250 411518291 411518293
    0x5270106050705071505070f240b030d0f020f06010e07090506070201090b0f040b130614190509011103031014030c13020906070f120201060909020d02040f0b131d 71
    0x640400a10f00107004419610b450b001d4003410201c95200301c900340110365010b89002580c07601c1c00c081c0009610140890030700100d000d80e0a904602c400d0098a6040000c00e403d40e001c1c002d0000014826810310501050320720540e00d4084000203400c3c601242a000b825010188400f844403c41d084200e880040100752003071400e208298001030a2031750140f0501300d03071000000303405a02c0c842d01011603025040010410342c40b02011660040020024000c1001054031103142031141c001583c02d549002e81c2c1031405102d000d0200000b121940c100020b4a41402803c45aa0700040f400f0700145204e01c119000520790245001e8484a45503003c0940ca0f0080d0064a13001c4015202e50aa40400e02c40891016035074507201008202d052061050103810154009c103640100103c11500314100003590780240f180301d468041100c12540548002548680030a18440050801d9004100c101141441c00595803041c80f0101c2d0781882c0c94010594015030781e8016100010302c8409460f83c2c1d64040d8 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 411520791 1250 411519541 411519547
    0x415031409010e061b18010905131b05031306020706021215030c0109151107030803100303031109061213060501080d090806010506091905032b0f120903090527010605 73
    0x80e1017205113218481d03401b070b00d080308034100c0ca031580d00508182c40109006841035003410703990000f0000801c1000342c0c109416102c6815420443c1c8100140e900528600c4050f00e403088842e681c40c0003d40c048a82200d95980a0007030506014007400058450074000903600d56080c1d460b0109801e202000b09040c3c1405031006041c01500a0103045000f25082800c1c00b0040040c2d45406503d840c505038001440d0b84000401c00648910075020603044038403a4406010040602040350501d0243d000304a0f086202400361020381c0d283c0d0792250350091050843c492031541300d0745580d4142d0308241c02117540d5501c5055041c0919a0000c0004014603a100117041203504144c002030706889480c0700030f0303c44e400c4030b100c0e1030707030f030380c071401c02140201310007000c03200003085d50004600032440c1d500026010941d0001d82404103400360814918000c6241d8848042c3e042c5515503130700400014100360100092120041552b0b1210305445528510450412140c03004442001c0d100040580108003003142c18 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 411522041 1250 411520791 411520831
    0xf180b061e040c0212040f05100f0c0209071808061b1602090603030d0e0607030606020a030c02090a020f0c0102071b03030f1d0907030e07050a03080415031409010e06 73
    0xc1d21012000125008a881c1d031010341e00320314000c095002c21900c8840081c0024940e107000d40c10404894041d84d80c891400b4200c0810399001c101403180801099408240400500d401e503049940724101d800d000d002044040e5400d015002d26400220003503011034184460181511191000c1c0b1043c00602442c0010f07407282c002c12a0280c200080c05040d6403408180310340c2c2d0074000d541030030842401c100840100c3e6030440b65075000075101600800c0c984140898503a00c0410300034032032501600d4018108d40d143d82070050403940100640d00c1c8641c01d01c010382804180b80c00038a40265100000358464106082100c40b044d0000d502900043d110442007000a80240c11498090410305100c043d00c200c0c04000300b8407100d07004100b03131302200140410210035010783c007400380720100744125101d031a280c505019039850580400390051605200130004407170b504411081117140381c580415031045d0511150340341d420540312405640d441d410301c800114810000541c2c400c01d45080b5282002c50 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 411523291 1250 411522041 411522079
    0x20c0607090f2612270d05060f07030b060409020405090f0609180a0c1e061805060f070f150c0302030c09010f03110a0c0308010807050f130f180b06 65
    0x4480e0501c0a0f030418503601060f0510103015134410810207036820b5a50b0038483c2c0c1c8800c80640301c82070001e03000c44540d89001542c2080480d105186512000409003525820001818158020990410552681015481622a00054801050282c40140e203880c105030400020810080618806200c00800c2002c2c0743e541907009504259044801d861072902030600038105894000c0180c03041200000004900881d034801c11501e00d00706035048282d50315400704a542c41c4c1d00c41e5a013441e20412134402d11036481c14030010090454100b0a55143c070031a076548284c01c480005065507034880011404030100190b00910688004615046146181046840d0201d0040d030031200d0400201681403010a4040d6000c03010403989528403603298400403500034900744050400310005108440000b509074000191070081d01c000410710500c00380ca0209212114140f064140052601c440c0100d85100c00b03440b4408040ca00c0c1c125204101c0c2580c00d01d01300700c0e1005031010b8058040200c0d40d40715405 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 411524541 1250 411523291 411523319
    0x3030301030b04030e060703050301051926010905010c030e0d140d02091201050c09040b010305040503030105060717041409010501361e050f06040e161101020c0607090f 74
    0x5401a02d809881e12981000c80d0703407141402050340c00150004500c0c06058000010714100e0300f040700e02241171091030107070b12001e030058032030450203500c042400c690490400c0381240088140300000921b1039225100c141c00d440780c00c0807042c0405da654182a0324102d0a024200c0340625506102c1e0017150500300a0b48244500001e40c40166070104035000166030b50f8500c0e6041d203140600a0003181015044121550711046d40d680c2f00ba4900760622404d0750180c000c1c2803190341c004000d542103a21f840f0600c103d6901440048442c80400388a01e142400c110000d000a000e840e09200a961544020b0000c0000b068028505000403c03d0785200301241101202c2c0042c0440ca40301441c50b03450b12080340c200595006008681103000c03140b54814a240c403901708403642115004606180e09c800e000070f44c449d500030602c030900d8000024101007905003030840e5901c21440c5c014170b80707200c9028450890b00301c6056410f40340c020700140500550b00c001600003030329507007204a01d114500034061413502c03 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 411525791 1250 411524541 411524543
    0x70e01091107120e01080a0908040b090406030c0602060402040501090516180510050304060b0d0b040803040203120c060a06090c050703140f03090d08160c030309210504140f0303030103 81
    0x152103103040300201480780c099070300316540040c1c2035008441503800503092803510308059002501010020728030340750b0350003140f0281da0050080781c601800d041c001d06069018410f40b0740c100780c803013000000281e40300c21500e001f8140ca5014000904184c410001907480607405860000d0800003070003000e12049400701020307160350601e26294401c003541000c85808035031001d58880d0b8030302c118044294201c8000e52003103110b01c1e01048070854080030070100001c100d078064400011240080d000601142c0103680050005044031a05100c0e800d801505910503100e0b0908c5800410612860790028010080a0460300c8028494140411402017681c028060054200840303590140f012031301100844800d02451441c13a5038a01c0c001e011941d07076080300c1c0240d400103113034000001d00c0304071070900c1642d4048240d0750f00801c0c0c1416440403130150031019410395803405d55514803660050142e626201a10703003038542030f8403540380600d50142000c02e1040d132400703100c14849452460358080200d038156 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 411527041 1250 411525791 411525809
    0x5060405070f0f12050109060f0b040b03040314090904080c0f0c060a0c15050c0a020f010b090a020702040b0904110a050102034f03060c110a060c030b180f09070e01 72
    0x40d00c10303c40304550785140004a0041a032400b0300101c4e0054281d00324009844048031071040c1e01e0340c1d4551000e00b900c902e22500704214800c5c4040707000244900318840c2ca20f66454000d6040c040924009900c80c10305403401c9504000000700d40c0b001540500001c42810348480180c5441a00715021035460702c0b0f1801840308100014802d041007003400515182c0b4000120810003140c40c141121180b00e6029984a0000d0703c00e418529964001c14081e030f640f964000b0300160b40a45030a10180c000c0c1d000700f00700b26841034845103150516190380c9030540c440c5029442c11007c01c071001c0e082c003080e008181c22490454108000484001041d0103803080b040480c18000103a21003c080c22030340380592181000c00d40349000d503241800000d4400c40109490040300d0411187c032101506032104d80304800b074041d0030340298440ba030201c0c9003035003d0340744140e650902180c00580f080024080480c2c0b9564080b603c0c4001d0b0500c00c440740e000403800d80c130040800007041440c2c204814100259030500c102850 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 411528291 1250 411527041 411527057
    0x908010b0109031b0306150306060e15040c12051e0106020706022a0d080d0c0305150f01142d0304020a092304081210050d060b0a0e091005060405070f 66
    0xf581c1d40102013000450f0000420464102c2500083c0303071408541c482521280c0c2400e2010070184d02c40c0800500441c9900e102c08104243c0d0002d000142a80010950500140480d60340d0421214044c107442560031030606803110ba12989955040981a0003110840d84402e4040c030001c2e03000070b80b8001d408541084603101208901c4880c209085010015802034500001003003044003180c003900b0f0316001004148042040450201c08a440071680710700c0c0c5801600c81d03e205424042c0b14030701142e0061401003000040b81044460035400740001e41410070840000741c8181400309a0402c040c917510340c4040c0786045c140c000a9602c0c00a00410107071660701c184501c000c03a10803051a001c4000342c205540c0c0d500d0319080c038070300981205911800348085400091000f02e02c00704004252000240720460400341a11184001c1809182c0c1c1c941005401c00041a00003403030015901c1406004001c005444212030642e054a00142c0300300d00540c1408107100c1c0068004203224803900143c41c2102d0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 411529541 1250 411528291 411528323
    0x218040209040b1002100501061b02090714030117070806010e0f0c04081f0c080106021b010207050a0f03050d05030103020a030204050a0f090c1502030705030910050c0316030908010b010903 83
    0x40100018866012054403084c4942c4c035004694480480c0406004002ca80c1c0c0c0c9c1d01c42600c006104020341a01410002c040c1d400600d40020010b030061264a822a802040045803000c140c3c001c0c0c01002e60080d1030003c1207641c80341009004090f08910300a010b0700d51510f850406040740c007400c5008010b14002c0080d0300b1051200549005040141c111010401e20b440d012044e20140c0d010025003e090601880c0c056000c2e0354001d048605a900034400000c03012081c94455042d0030141d41107001e040d10020f00c0e0b5852250200c0500740b9500c520400351701d14904149003945404616040c030400740010005a0b0b901000081100e0301500c005c01c05696060483c002041001001e42080303140c4401c030340c180001222a0404c0c1d4003201c0f40e442014060650036a076074050340c40c000b00941e10801070504541095030101c4440d41d4107042c07880c140b500001c041d50075900310a0024149400c07159020f02410f5001c0703583c200511002008000b81202400000c042000c180005843c01046407040a = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 411530791 1250 411529541 411529549
    0x20c1e030a05101a040b010807030209030c030f06070e01021609110f0c010903090501140409091103030a030b01020706030209011e1e0c0b0f0f16020304030c150f030218040209 77
    0x4019684081030f10b003000d540010a9008000d01081d5506000900d040f0032040c1c01c06105074000d000d4144c440b81030581d40c4010840c040c2d8040c50701150503015480300c060168404100446000c1c0c4494090074140c80c07d25001810f20202d203040d541154409a40159401e40b50300fa0300c42034071220000480c0c445181d00d413160389845200807050f0880c0001400c1b4001200651002c1d10b03c0303100e552145491655080111081840c1d40c0e06c41c00c1c4c0300801c0204120a002c0742c4e02003500c1c24130840310880e48401319000079055800c010450000309459105122196030f044c4201c8000e004141030440c140020400001d14580c01001d0f10b008480d504444103008a0040c000d044540b094501151980315503100010312400360a0000c0b41c4034100c1d00c02142c161498113002074441d544202c0007002582e20341080a5804202809040660004100110102d03101c0d604540240000b55514201c4e00342c202d400820041101090303000701841072105c0c0520161101001e1a410012a000340e01c500d4641d00007 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 411532041 1250 411530791 411530803
    0x60f230705040b0c0a030909060b040b0c0c040e06090606100f0f020a0804090c02011103010305060f04150212060f10050313020402040902070b0402011d0a0e0a021b030910020c1e03 79
    0xe0041500419030440000d00040c85c120038610a5485111240c3d940c04a181a203a040c065241d0300d00d800c0c0424065451910040c03d00800821300f280d001003503d00c049011102d21000006107134200b4020445403034000c201094100c8400e03213a04482c0340c20310800030269000c0040040803c020b200b00c0c50401031003088400b80c40364000480c02d6645503959140ca0003441202c1b0002c015500b0540441005171952003501d040300d401801030016980c810307036110400a0024422981000004450750700b02e0003910140081c0c540680d00c3d0403203820443c0c100701590501000282c4903011801c21702e00002e03400429a034000c1d528464407038040c2c0007440054040d008a4010000b9207102003002c07018801d82501c1c080c0524002e0303c070b807642c140100c18130f05640464031242ca5088082c2c10410019000c40d10046607010b2144007005041441c500c3e240c40c0081d1400340b207a4801d9002140a24092401004904101d20180000d0803412607040114031180c60007880844080010307050384100351828041 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 411533291 1250 411532041 411532049
    0x140a0c0b0a06060906140909060a0b0301081b220506120105040b0a05130c030b070309050a050706031b27081005160306050d020d05120f07060f23070504 67
    0x245011914101e01048000c129a10400e40050220000010118010f0031100d40421020081900d01200c100c18040e1200003c3e0405411401c4048002039101c90080a54013805a100203050a1695040103074003180c00c0d10303101e038450f03d00d407005000300400c13004014400007103074507020a0a503102e400146800c1c81c1d212050003694201010002008800c81c13046102c2c1032900d80400c595240c49501801e01c9024440c01021003408400a002240080c290b4552000071031402183e102c1003503440508002441c04112219840043e0902078071303425000d0995012400c018005d070a24030040000c0103c010110380d41d4200044492461610414001040103484240c04881e0203a06100300c41d001800100c0d034010205160488180c3c04500c240a60b8048402c01800610303031044d15020044074080e03040c002c0b101841010448030729130100310301801c40504038410403501d480160820100b500c810003d1801500e1030f0a07500d070100290b00c0495040c00209e80d022141c01e0796100380c291910321481d00 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 411534541 1250 411533291 411533303
    0xa1d0f09010f09030804051207080a080921070b1b0702010c0f0507150206060108040b0a1a09131e051c03020c070b04090c02160605092b12020d140a0c 66
    0x303903c100749600228840c0c0210321400850705280e808442c541914019920018020002040861190740c4501d0603142c0110100043e1150b80300304c220544204444222101030002011800d5024002c44013006640941003510071911400c0d0484480c04510844000905014614403040240314401402615280e0b2040c00c440102381c0b40c9002698030100c170500e050043c49000c0020b00f4551040383c01c240140c1e40040010394544a8036188000f4120b001014201d000046420100641c0e803140050b006080000354205041414108170608042c254034000010b400907000c130b00050310005403680c058440c584d00e424503040403601200a4031480005403494850100301240031030820700100111000340400b0403c00c624460183d071555401044c500380c0c40703035056041080c5406000140808540180782814801c1c013407043d009180340740081003203c81800440c480401c04417074000d10407060305000500c840030780c008004102040e03149110f5910007003c0350408446018000780014075074049 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 411535791 1250 411534541 411534551
    0x6021f150b091e0d02040b06070611041518060e060c030f25380c040503011d07030318180506090106090302010509041a09040804050a1d0f09010f 64
    0x1000714480e0040e05466110321642640d0100e14000410700001e10800a4000385a4620940801008103120700009411810401445000504030b2003003c0500030743c240311507100c0341021b1885420010410099090000c0030403842000f2450302c90a00c1240d5041c50559501c40200000c02c5840c019000040c81c0d900c070200301d000328800c5c10000b90295940002c041000880c4401c0010244034040074041c1813000c084030407402030320303041100305d08241b1340c110100784150304040c220740c0000b4100c83e200c203498404201402113103000e010b03401000f03817a4030392180200c00140c14907440303040603c401410b01404103960304a081c8103254517401400c0103188040c02050b42002c48010346001c441c0188a00c14860010412900842c0301d00b05030303074040e910141071120401c01c0c40028105040082c1ca124030302c00860207561381d22440c2e50b105510030741c4003d4030780c0d15000501242078242d401502c80e2a0a004581940c200704152003513200094201041d526112031880314010000f11607a440054101 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 411537041 1250 411535791 411535799
    0x406081504020f0d0f05070804150b01050c030a08150306041509020a1203080a1512030503130203010603030908011104180213030210090807090c14130e01030c090b03060106021f15 79
    0x16038404c40b29a90803085c140440d589252049441038012140105916282540841d1007003c0b81d200701c08000d0b040c140945420038135080c0c1c074a9608803a82001c00110580204042340f40c1403540301843c801c00350010861030030a640c60132101d400240042003615943c650300c03403e554582d00510010701144040c90350a41c0725090042104030200e985440d280c0c140018240c1040d0001c078200100d80381c40390100101038250307030115520743c00980a1202c0f0b20f6403001100140e5000e204000055211b03441c0e8560a82c90300303a00d5800e444007031800500189080c402044004851681c264040700c15400050796074400d506207001c40c0c2140d41020790001680d504440c0c3c92904501c000d804c0c0e40c1800c089411490381e0704204401d44e11420600c00000d01e40c0c2c042818001000d002400004d40c8030046103404685461241503141c0b005d0748250740140b032010041104413098404c50148036010307030107011a0340c104040030750380d0112807201c60700c840b004500760607101c5e24981c40303100810350f41444144500e0362 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 411538291 1250 411537041 411537067
    0x7030306150905030705060d06170a120302030601082701050108061807080d03020c030c0d03020304060501080105090d110721030e01091a091c060c02120406081504020f 74
    0x4901a0042a04202102800e0940500b41400c201d510082c002c060b41c03801d101c2030040310741005e200415029110f00303000c00c00082c404607070b0110076100801000c0082c00781c10510003c41440302c00e031050510400a003d500e0340c0c883c1c403640d800621400cbc1d4640400388170b140704812044000b8600103c2d46807200104800a01003612401782100464021400880301103030303a100c40c094800d0480943c00380e03802d240464000d40141c12213540100540f07007051a50740b503080c18040d80301c0b01e2800003036001041004022140c480d41c1d01500903000208000d24006400d541d0f248203804841c0280022168a17071204142003242d54090403801540e80038003200326000c280c147d050701200300c000c141a198410400c0d445041c00408813081904610350450f404800d0140c154468002650020066030300c0108542d2504004945c091003180d002924400c4500001c3c103007002d14040c641c0c4e402007080200031481d440740c03626400685890a1240a11741c69001034000e2080819402120901040100c0c05800c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 411539541 1250 411538291 411538301
    0x10e0726130521030f0c041e061b08090f0a0f030506190b030601060f12140f0f1306020c240106120c090b0306010c06180201020c040507050909071202070303 69
    0x202c81e0085403400c481c9120441d5820482d0388802c40c200d2410700000780380115200c1031075080038402080324900781c1c80b101c003034002100f00b0318903c1c200601c81c1020442158000741c070702d0f16044462051a1030065694a49819101c2d21000b01d2241000410700034840c1d481140050091101100070004641d0300d00e09a9142e020490346e4114a024051206058050501804000690041c064103440e800c2c01d1003030300c0c0082c41d003000c9005c010012049074850b40320380c441c03280c9465120a00203200d01d41071904e500030345002000c0c2100c4a50b400309212642a031900c246040d9a401480581c490301c0e4002468038021175034050000344004ca0b00021400b101d540e070150b058500ea036541c1444080942030b01d8040d42c04035110301000a24412042202d985800003031034110710149072500039040503807180c4041e101c503401e998001082e10682c0004540e01002603011400060742e00380028900040098824050000014042c003070880014111600c101008d4a00b00b50080b0119182c0c61107041c0100184 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 411540791 1250 411539541 411539543
    0xd020306042901020f0d08010308030901021306032c0c150c01060b13150f050705190804090b01080103020a15020a140a060e1603080c1e03090109050603010e072613 72
    0x4090170b2071503420380e800401c01c0200c03941a500c45c260b0341e91030b565410005600050200249560901c0f0f444003da0004054000a108a80d0040341200c4010045a1004c18002c1c40d03284d880d442c1c0300700c1822190082100900c2520440e012080441c054156051500c1480e8041e107140d440d01c0000304440305040040d102150380d80d80500c40c200c0c0c03258400d61000344e013181c0c1e4001013801c16040824551098005100e0581700e10700707a4148070581c0c0c1d600b00c04100030060844280101203001c0c06640603d11511940050034070307107070685c2e52540e00402c03d008058014008038003180710080843c28000c12180c96031540c8091481150202c0100445d2109200042141c4440c06c185190b04a1000000c1c4402807241c0c00a20441c440d02d5a40c9003c403903402240b0700ba01e81d0240144440d030400b0703503415030050b2202c4400903643e114803050004081d80c80c140c120368840d100a0005120740a00c040ca015440f03401401d102480540c6d0b14402e00c24145034000d852844240301c410410355940c4070705428040d07 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 411542041 1250 411540791 411540793
    0x40203041b051206190207050607211a0d03030b060403030503010f09021821072d032003030d020c1b01030c0f080411060c062a0d02030604290102 64
    0x180e0b1124204001080c0d011100070403a030110300461a00d12000b80c1801255258400c01841c10340155035141c10071908076441e102144205000451000c48403403030907883e203041c5e4810803030701425000a0700c00350903c022140c0541e10040c10802094003a601c08800c00d4801444d407500c07942c0c0d900c0c0090480d0b00900031050500740d01c075000914541c050007900c411101c0b040100c400c0200030818010f0184240c8803401158406100e0400d40d0710003845180054111080c1001e40750b1f260061203800c440858400c007006030040381003040480c00190441503460000c645a1240840c60700009256016007141405ca49200060b05000024002401c0c1880102c2d890342c1079102400500541c2100c101e040e84130301181c405d000311000980304060459009100b000200300d40c02d042d10104026030400c1008070919032000d814440200303001075208a17070800008040103903c18000d03404a15000d500e051070711468022001c50980e81c1c558000300300303454400c0e00c07006000f04160348100c690030145a070701d405 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 411543291 1250 411542041 411542093
    0x1327060e01060216060e0d1a070f1704050a0f080405090a0b030d0306030b1504110309012703020d030209060c012a0905060315030f03030a050609010b180105160204020304 75
    0x1004413200d1584044424503290b9620400c034a0040c0580e00b124807104480c0511015440840e4500111960b03002c0d030f18a0343d520042d4941040013400c4131008203201154040c01c44100320029900050001c1d0080e80000200d03040183e42c6070a005501842c0c20041c0e00c08648030030814041d04980c03000c4020101101151046404014194105c1d00d40307020140c20303e05114005550003046071282210101c4c06000001c49200c0c041e10301c0c40b10342060f0b6100c0940c2c0d441d8120401441c202c076910000103481021000d2a0304250f560103540c4100055401c414541c000c680071145641d04401d462084c60108000c0c00070341c400103e03007618034200c1c011805012a4a0404001c0584150314101c15507401401491960301c412616500b40300080031425414071a20491140fa074000348040c5004000245021030070341003200400442410582000035241018801401d80460261001c03540c8002130a0071030b038421456030b03004040340d2040e5019400a0001003444100b1035001c000c440a00c1101e0b03a240d030 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 411544541 1250 411543291 411543313
    0xf06040905090a230c0105090105040909060218030303010b03041e08030a0509060a020a02030912190b0708070c2001090503030a08060f0d02090403032a1d061327060e010602 76
    0xc0400135a80c02444039502c5503520301c51035400340c0c3c020300d80e42805042648c01d250351500c4c0101035500620003100c0654000c1004840001d40c6d2074041d40034a0200c01650866050415040e1a408002c0000d4540f541160140a16020840344c1c80c60058000080359581e1500010720409040240c400003580d115800010f00300c1c90311032080c0c030050781032580a9850081c00d041000380180300344129010074064040c45594450300780705440e01c1076200b5441680c0c2480c03c0390340600841002006032003400310303020b8018000780c0d00031031424205d50a080307841041c07040203004a5100750700f42c20a98040c0700000311481d050b60031818041c824241210403890311041e10342440210b4120f2040250021240f4000c01c0000c1e000e60010800048600402010ba0340540840e41c801921b0a46440c00f0800d41e100c41440652455020241040103407907051405600300c2207903a100d101c5e8881c1041c6152030764a40c101813011b810b400b11010408690521030302da285d035104e1809010a10031240507118480d0882 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 411545791 1250 411544541 411544583
    0x91a0708161b051603050a03030e03040f03061814031308070305060705180402120405010b0d05030f0705010b040203090c12060705180105071407090b0405150f06040905090a 76
    0x42000031041c2d480c051441c2c400a26400402ca00d0007003190700d40641010100515a2004007000a5005000174006c0089034280642290355854507100d00d07400801050001942e6400303024200e0750711960025400098001c680310042503054000d0134802180fa40c030f650420000090000b40150503c0d43c04503d6a59810686c0c488607840b00038800c7e0071010020b03407064040c101a000b0700d0f08000c0582160160207001031b049070710410080d845540d01e0000d10041c40800d104224581c081600e0f80c10051b04507031200c03680c902940200398402c6000050303540420000707402440400b04050030075516828071080a54940d58480d11641c061004500c1402c25058000344650203440d054841501e0b0029094001d98a00010b0700031605002003088214000340075040b0510b0032040e5038016151890a100315132003a5050354013018403982c00e00d001d008003e0103160107003013041000c907903200455540c0780c0403804600480d4040c50001e0b02e0441041180c3d1404500035100b60320601d03006802800e020864 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 411547041 1250 411545791 411545821
    0x11030c0f0d0204020307091205060709061115150901030f03141809060630060a06080c09041e09021801031e05030c07081c03050405060406050a091a0708 67
    0xc80e844000c9240250143c14240d000f150484418030b0401c1040c0e45845402ea4a100389803000c403450b0b80f1850030400104d5111090b00003400c0749182046002c1d03101d109150391000b00d2100030591010640206409903446145000f4844000d060b40441750703076900b03010035a0f8400c03080c150040f5600c03440122600d00c80100300c030380c0440104100c1e805503107090103100182d503000345000e0b080201082408101d10350b8040041c01c8030400b8001c00007160b00350030310300080c80010388040d0040300510f00078020181c01001080c0d106201150322511105040c1c0090080c2000c2810750f201c02440788801803401080303804c41c059407402612459480103000f0b2802c01401d100340f101402403601c080165030400003080041c07100e2400740007280d0070083c060303030200e003055807952003403010764403c40f91f040007019081c1480100580c0390500304001d180a445e100d40303e840003040100b4039903030b41c00025640c40341c40e0f004d40e02035900400101c8500f079004c1441c50554a00b40c07442c902154500c0700055683d0500d03603034 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 411548291 1250 411547041 411547069
    0x2c0f010c1b02180901091a060d03052203030203071b0b04090b03010b060c071d1509130614010303030b09071d0a12080901180e040210050d0911030c 65
    0x90709800c0452032100c485020400002242d001c4042000f10a145401048003030044803220000182c2201c01c0c940040802e025000f80d80c1210000e030200009075803480f840b1405e49802d400c200380e840b0210007001710581d406821011500c0117401000c028954000050f00c00144030342e810300e032401c0440c080d8044041c91481135032a0210100410300240040341c1052040c120060004251000040e00158040e08108010075171640014820050180c500100081031036000282400c0c604160840045e0003201c40740da94040e102580104010541b050844500503800400810903e1285242400741c1c07007007803000b03400181c1415803203c540d00e0700550440c01699a5141c85d090004207889070070700e070414131005c10f9010800303a0b0009034809410410005940c410f80d1219910b038862800504410070a014600c0d1315106244144801d03806100c070950027940464070300388401410002110113200d124107095516003450000c9003080f007404848200303100110f0988040c1075040c2e00b03000003805c600750 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 411549541 1250 411548291 411548297
    0x61b03280809031c02120115020d0813020108091c0509040c030c0215071704080705151006180312020a060f0b01020c04020d020708040b0d180209192c0f010c 69
    0x13101815090a00404a541003002c00e0054204254400401c0320b42000b40e00c60305540044e0000342039500c0d41845982c03d1030340c1d1403c1400303581c20300e554600d200d030040385402418860f06802044030100304000c6200012401200c991244444c0040240507421076407500f4000c608002d1030324440c1d03009020300303807004041d5401000e44c000202c40c0c00310001c2c2d024240c4000e101070380da96003240e00c100c00030b094441c0b0701803140c50303503289032514009241c50244010986940d04900911030409400c0c1d440d0005c50701c242c540020a14165110b8110805550340001d21142d900c4034802221900070030020090350240c40d00300507406000e00301e00169504426100d00603003046182c05a10300c0d0a03405404091036450300141042030960781c1e01000d5101e80c000c64110741021a9036201c1031094042e0714000c09008841c4185030640b0340c041003454a01400c003500881412600403000310b000d5120100d1155940b0914008021000ca1800442c04c00c0c88542070a00030a5403403040b071001400f039100013400642d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 411550791 1250 411549541 411549547
    0x31204050907030507180305060121020a1701180311070605180402160c0f1701021608070614070f03050108070b071212020a051801031a061b0328080903 67
    0x10400c8000f407031300910b01c40510040c0340764451000c5a1394405006144203400400c0300d075040a000401e0441110061400440c800c02c0e100010313283e840c043c004442090641000000c0c00c2c0c1e2403176014101e5003100501c00010030810100b8598000c0c5401802410403094502484d1520401c0300c2a00c5068800205410211641c04c183e06007540140f181032103c00014844881564468410b101a0342c45040780260000382401900c0c940d2818500d0b14030204000c51420040c01a03034a0800a24200503000c602e010590030309100e1146c00c2404510120071240c043c500e00400090444a510300f0702c000000d1818001180e503201c006890400c0c0c820712480e083c01c204e400e0761807032411a8149004410030101c24a20103e2007080c0c00034155440a80c1c481c1034031580001c08100801820307a60340381c101400c003480040c8034200c007901251102002d8403d551780b03030601c00d0800242c55208888410718403000a51000040319141d0803144d182000c03242d040042c5030484202c0b91085c05a45a4a854100b0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 411552041 1250 411550791 411550801
    0x5070801060c05030c0105090303070207080c0102100504080c010e031b0303040f1b030b01141e010f08060d020306150a05120d050a030b040c0914010507031205060406051203090312040509 82
    0x340c0e1481110511030f104403890309095881e030500392242500c10180991010050140181d01441002d020300b4a2400900c800315500c0c0c0003c0d0b5810b4008222814a90313a007011a092100c5001160b51a9a88000a03c618001079010566071350000c444400354915032101010f03840004800c8038040c0f504503a2048141c11540c40c0ca150318402c9640c01a10b0200c44c00000001401d688542030090142550000040014030280020342c40c984110185210840c200031701c682c2c2c1c01440b02001390b1014070b4026420b82d2150040b448141c3d9801e00654076101e400100401905440300103400c0d02c40a442c00c682c029542c00071710034402c40c80d5018120703039004040d619450310f205e08040c103004602e624000c2820b0b211240070500311000540600c00184080b0030522402505982c069620036080c80c001d4603046040e02d00070a160a8161010300280d15100412100c0d629a0050400b40c18010101c250600140da1001e550742d20405416000307018010030301803204509400d850031280e0140400000d0f43e070b0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 411553291 1250 411552041 411552047
    0xc030706321906050607120201090b0103050105010509060103061d0426040504060f050a140301060e0103030e12070b16080f04060503041b1815030c0f0317090303120405102d0507080106 81
    0x140c2d402d031f20840d075071803c403d8041044181640e008601600002070194140340620640241c01000e1605050801ca8200901d8620100e280350340740710038036a030503941c496250412241d01e8517a000d052880c400945525000c0d90303140200201c8008990402c0610b541c2c460a0565500c58801c080d4003943c0c21748100a0310422203075031551a04020000682b064640e018501704070401e0300141c00203120703240d032008682409209219481c030391800030140640790030817411584c8a002e1407100d0070820320707a0007010056240260b07402c50001005072a126525510000c19070b42088406641400690481201e01105017446006070303444841a424455500d018010282865605551038121441400800300d80803c441e04042e01c0c07000c42c5038180c00d203142082003000e1042c1000380503814003046441d9050390000120b48823120320440d100100c0d40d40d81410350800f0000580419168100101d2020b801840424030709501010b02518a10401c00d0101c0800c6800850b05071001c01d540000600000c5c3c0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 411554541 1250 411553291 411553313
    0xb130218030601120c0510050d090638060901030207060203010801020913021602040504230c041d10050421051209060f220206070c06020c060c030706321906050607 72
    0x1f07035040652408000c10018000c6a0880e0b0050b56600d50310003101d9041c00c501d55001d0303a00e44148820700302040404400300041e011040c00584610b000150001959000350103031100700760007650440d140d40c2d480c13204c50b01035448511081d1180030443c88080f00d4a109109803400d114155145403c098115400d020040070054030540740c68000031700e0100d00000080e505550918050007070030070808607105110036980f59903803a0360650440e520b5003000748030026040b480c02c003c82001041548413800e10300c0211000700811054400800085003890750082c00600c446090b50307601e185540e03108164107844101c10383c5c0c4000707074002800c080f40040280100001c00044803201404a11582e580050019070003803a0860381c0c144400750401c203464045c40600000002545c10510b885903030388089859114a11005000f41d558505084940c202500302c1c404840b0f0b1054080e10b854410b0384100c0c040c07201241d500150700502c02c2a401004c115015190840e64081d001d01e003041401d075584a0150 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 411555791 1250 411554541 411554569
    0x5010918020306121618021222050d1106010603020418110c19060506150f0a14070f0506150a03061a0d0f140a030507060b130218030601120c05 63
    0x4000452002001441481711401e03d02c046500d03c031500340343c0800d804954000003003420140b817042c0044800080d60103400c5901a05079041000d01d030404804964080c1a000c8000d0418411a4a2042c2068214044480000d408404c030350721681c1c6d8090450613803055000324074058407103a55980a40482c1c0c1c2145041da03941d0000d0f00c2c1418010580b041c5040d415904400c2e2800060a48034240085840340a40140044c0c4041003818011032084c9414428000501c0f0f18500004015501c13900c1440e00b603d42e556980040c0b039450410b401c11141d600c0505000340c030240114004030300302d0f007200e0400220980016110601c501d1031500c95500900301340103520a001d000901c07a5940355504000f030510a0300c161545018141c240c14042c0110543c0e00300070145078800b08004001c01d80010950b0303001c0da07000c00c000c201400802e01203149003402d0b043c0307200e560340041600324210a2400050442250942c2114066070342e0f00181d00d82d50601580290034103e0740700c2c0a02c0345003042030201900c2 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 411557041 1250 411555791 411555799
    0x3010c090611100203150f120304050111010603080d090203011506020606010c050705090903131d1303120905010e0c22051314010b01030b120c0909010914061005010918020306 77
    0xa49a80c6031500c10b81c3d01c100c1d030810748010906c81c0b00f03c01d8541480030469019050b03c40d9120050a8004030341c2e24401c03401100e05020a4000941042200b50822005160701c00085915214000340c03400103041c03200c10072846542060785442526040030461403c60b01c013507004103543d455690040d600e0032031242c2c0170785e81405002d001040e141c5800c000703e4003035020302c0b0040d6690b20160407418007070186a040b00c903041403007094503200d5030829400a90400005501480703803a18503c1d0175540003100340c170b012100c1401c00302c0b40740074040194070024840481005840b0040c0006040081c50b4040b0080381c50b501c441040b00560310302c074541c000c1d0b40c003c102c0103080b42c1d42e41113502d5449502002443c16002da0b0746401c51043c04d943e040c00341100e1510207031208180c0c0e036001913505845004920020340501245400248050001d400c400541500143e020050001101d80f00792035090440702b145814041d044005100c0d4801c80d000c43c01c49000070085450340e41a54011000707540080c001d507500c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 411558291 1250 411557041 411557053
    0xb07080a0e01140603070b030c040923070c1101090e0406200403050a200d02011206050d0605011502061603051e150405090106150e1c140c03010c090611 67
    0x400070920070180022600c1540000301d03e440b1041500d0460150440d4078600c10a006014487c00101c0036241a13604146010800500c00e8582c000c0520202c00e071040f5800030328040c00fa10642020451040a004803103541050580d5001910311107070030320440c41d104401c0c0000401140203507001c5407015031016031600c142c42e01044208100c3d001a00180c0715508990052020041007107400c0d9060102000c0c610031418486c0d000a0110070b0160000c1e05111800078101c101075a50751100020386400ad0113400300d400c030760504100500c0b09000300c86004400e501035010590002410b41c1c8960b403200107484102d11104412009040050031005203460040074401503080c40c9402c081c80f5a21040c141c100c1862000c0400c0265030000c1c0400d8940c0c0d140c00801e01c41c0e040c01070315244030981c080c2000044405ea21020540345c80304481c1c070400d00081071b070103202001484039100000448410417162800100c40425007255600c458a40210310b08000c1001400c1c040c0700146046035180f0f041d244 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 411559541 1250 411558291 411558311
    0x50f01050310050405010e09060a06030b13242f043f061808180604090908090108010f05030a20030a120906031104090510080a05100e03070b07080a 65
    0xc05d41301e01303030481002404140c0030040400001c1000c990300c100e1002c07080c0600f5245031038040d03040c48041c06181102803030b503c059007440340c032040b402040002040604000c0b1a4000780d80010070114201c80c4001c0c0d1302070068000301c000d1442e25002c088040142d0307454989050352903201d1160300c0c081044080c09850254400030030409008002d4044000e600c0003040481c47c0c000700b241d0801c042811310005640020303011410300c00c01d44101c59980a10407410354a2400094010300403070303110b09010b1341000c800c2400c2041305c0d00500751140702a2961041a600c400c0da206088440340601a01a80144280400710700050042610130104010303080c0101320440200b402d11038400d8054441c01d80c00c00401012036400300107800201002e00d4100816403000c40c4d000e41511842c45036003415604c520100c0c4090301001e9140c001003281100b198904d604502d42503445000c030141c5007000c980380c4a030b20750460302c0110488191079402270611015507640038080c0c0e6801c0000e4034481c1c04582c1c80072195 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 411560791 1250 411559541 411559549
    0x5040f110f22091a0301020a021020030406142401030c030209061303020f120a2018100f030b0f040309080a050a11010504050901181104060509040b0a050f0105031005 73
    0x402a03c0c0c1040040f90104006109075400310b10800000c0c040c3e8410400300401a81c0862154510340c441c03600402d4041c0e05c02070301d140c000290b0f4010005100000b09000410281341d002207004c4800c03100781501c0d03645030701602c0d94000102c01440100001c02c040422190301c2907008101103070041c10300600700f0300c030f920104000d50481180c4600d41c99015006205600e419003e00d048003104540010b1040c1a400f800e90302c8443c80f44000b0818203200c1c2c008040490300d80d2070040748400151aa41e1215890704050001d0002916a0b260312040c000c0042040c80c241c0410400303680e0890304401854031500801925100c2c02802a0200003914901080c05d000074481d000c01c0d1400341c0300501c640e91090901c10030850802040d5810310074108400c000c40d1b21064100c0341142d0004070580706c3c111140c90031a0103400e5440c00d00040420008001c680d07990090041c14015400340c4007000140358041c28081648a540a443ea0000305458042499031140c0700035648541301c0c24800039001c2da00c0f4049 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 411562041 1250 411560791 411560857
    0x711070306020f16061d0c01091205030c010207030c1b030f3005070515160c11040203010f080f06070519140c07051915050a0e030d02060105040f110f 66
    0x40710f17507a40b50400c000c07101d01402684020b1882d0360303010380340d00c08104d4006050600c00e4482e0300000c80d807001da444103005091081c1c50100444800035551201c4500c2c0040144951100c05c079500400c408002030340300e0910124109a0350700c12144900031100d43c84148504541811480c106c101090940b5100311070071030142c41c102d1a545841d07403100e103a80340040c00c152050365a40c4400b0304080170032000c201281c030780310310380301c02d03400c0030400741280b030070400d9200d40b0440760660000c0c0004000510f00541e040134508540040054441d00c0034840c03407507a2281c006990100028106014100c44210744102c819641141c40c108001e0f002d1003041d0b8200140c200d00c0c1c0c0b60645d40c015100c00c00990400d2026010380703104640004559601300701c0c1c0c0410207182074070480304000c0e005c9010302c103141c01070142981e034110040c110788420169107002996000240034890095052640383c80148410f07002d40840d000352540340130300f0a5420f03480007085801881c07030702d120035012440380d0401c16461652 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 411563291 1250 411562041 411562043
    0x3071e0c0b0309010605030102090604120c1e09060503030304111504050406080106051002030f0304030c2d030e01030e0c090a06030b09011a010801030f03080a02130b120711070306020f16 82
    0x121901c0349810480c41d4212205c560040e806640104816030060742c0303503c100d5050729846043d400ba401c0742810144001c1ea078942109003001ca103078030354004081c0750452100494401603800c0c0991030302c034400c0c10b84a00056900410b403180c00702c0700040d28508100d20821281c01500564103066a400009090703860f960301441e0344d41d54814040c446824200501050089a800250f14000c1e81c1c0b09003041911000700003404001e0008034404c2006100040c100f460031440805000c0f0206280c914041d41400c14811004104001c0745068a94000c2c018051007465500c050312218109209002e54250001d241189465683c03e0100004540300c0405008a411000010314140980805110a0700c02d00469043c000108010030008040404100ca816410b1034a40d48603141d03208044041d0069601d10f4020030040003011405484180c09003c1500c45e0391a6201d03252940c0324280d81c581d4004a2001c1a908040000d10104100ea002840f0348098002000d150640725200c601e402001d20310 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 411564541 1250 411563291 411563309
    0x1a04061704150f0609110702060f09190b03090d0908030a050319151517060f041b05181503060934020115050f1e18040506010902090303071e0c 63
    0x400d0262000754480d100e6014210340801f41750080f10b03000a40d11b8040c403502100801c00000303200441d47c982034005520140c503c002c1008494544c403503101290411203e8100900c0b90760f0441e040c0902c2340c00c0507011160b921014604e0030015801c200c41690008001c1d200c2100750340003070003001d08140304e542c2c003442d01d00038a0130f03e1500308203001c940c030100c072246801041219107803641c030001d0034490f80d070300083c003191010304040300440443c016105907880341800050b003085556915030030400600c00c905800a0300c140c82c00780101003140420500c21309a0714071501340005022401d20045141c3c101c18840c100c1c0c9000c204030340010303044942c1100001d00d0641c0f9608007202e0903409000380b51480c000501000021400c040102d1044101e04c045a48150301c1c40500342c1c01a180501003071243c62024080c00394005200101d03003c412815a0103c40612541c0000640c030400c0c1c0c820395068202c002d020350300d0302803140c81d150862101414802c2a4580440000c00002e52403100740004003940a = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 411565791 1250 411564541 411564551
    0x4052b052b050a0305090a0506010806100b0f040302041107050d030209011d010e1018090b15130303080c191218030c0b0a0e03040602071a04061704150f 67
    0x8549041d03110080409402075185980d0401c55040d00b1405a0b00030b51118500020310340e5904203000c0c0382428a900c0681140207940010134040e4002c294a03214162b28021100c05503640c0c010718107a841405191608590300744414401440c0039000b01000c1b440d040c0a0318289605911445e04048041040f103000c00e50009844078196003103990f41c541000f6600720340c00d52905150020349a14064142d01e88110441162081014051054403020303580740040750004640300c150f00001400c04145280c0b1030990a0100070011044004680015a03515100b101245c556902542d503103c01800d84821b000040c41807078926088188480c42211007941c504080440b064603010803240309401300342a0000322026540441c0c1c01204038800e80e9130180c005000303035075182e007800d0080481d505c14440034000000c00140c030a9001400c0800c0c4d6440603d00c4059801200c0c6141a0f40b03d28403880021801c0c602040400f5042c4000d070582c080d00500484010041c0300c45070303d088403000a04442099030311 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 411567041 1250 411565791 411565813
    0xa0201090c060e090f06220605130c050a050304080409050c0d0e01020c19080d0e1005070201050f0c09010c02061308122104051c090303030c030b0604052b05 69
    0x884081d200400c0c09040c4102c000401c40c1c08940c5124008114895003070311000400d0003031311900c8110444800440340405190040c4080b50050440e5200e058402c451400d41003000300900d2260074082101600c4452909501d8402640d05410041c01554402000d0000244c0a5000d011309481307a40200341c0c20340d0710742e024010720045501d1410594416031050004031130700d0400083c503504601840b070428018031041c1c9044001481200030750b42c42e46050101e501800c2e0000624040290364245d8180250355070520128200c400450703005a202c0d0151011560601d40d041c003c1455880c185007501241c0f8480e000304505610520f580600d1a100d1201048801d406020b101c01181074401c6151034110340c2010968140a81400c0200203c0c00c1404030701000010002c40715400c148003505880007082c030070301600f60071a5220a03000300b0304040d1144129482440b0360180801e0080a00d41868100024030603445d842c20000104d020441459140f403001ca0145080080d105800402007540300c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 411568291 1250 411567041 411567053
    0x21010603141e0c300703030f17180307120e010e030304120605090a050a03020309100e090a1d030f04150c03050f0a050d0e0106050415060203030c0903070b0a020109 72
    0x11000200702c2c0c1d00c1c03200d00a042c12007000c500903091050481e02000f00072007800e60102046145050700000458021402c00030501c0481c2e44401c17203001e0b448041c81420075840581e1a582c1003800803400d482e10000080b010301032b005106440d80b082e002102d05120290f5109010f24511088804c040b42d80d0049542c4a0f6074030108100400106801441c10b040c50880c18a44c5001e8441c80200304586400005015110800000c000150000100c1d104600107040194480d4481e403060f81c0070310482c40645400038060707035007406046030141499480c3d43d10189000d004001070b041c1888404141c030034004010100700060001288200046585c461030003840a19404c0c0a040807403e01101c4003c010109030000306803100c6d001c0400025a42e400c40312800c95079403148810741da0b11303540381c0390400601c101c1c154032460a03210142c80400251001d90030300a61080b2038440e100c0140c1c4100b00041c620b01c9101d001d400301c42c501030102c036045600c41c0a421140d420401c00400180e64031101081800a = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 411569541 1250 411568291 411568303
    0x31e15080a15090501150f0509010e090a110f0d11030d0807050313110402040e0406050c091e040605060a0f0e09040215032e060905060a0e2101060314 66
    0x440c040180740e040225030300c40c44100481d51141c00b0b4141e8400c080000d00030290803c600703a5148030200d8a0705034a944c280084003d09001c1e00380194501c40002c10320b07054041040e401a59240c0c0108642982039441d40003684d0380144850300101640f0045005480750086082d08a01c221034902e01c3d0034000080c1490046d40c0c00d41c030320412089a081c0061181c0040480382c010021601d1205040380e1800c11810304081e0050554026200080000b10180801c1c100c5018621805042c00345880d400340803219400380000e82548401c1c00d88030303e11115443d40100b4035050010300046a525500c4d00011030b05e0304612b0260003c60100745136844060343c84071803038100318412a2100f00c42e080940105051a005400c581340c2103c000000c103041c80c04040c03120344401840ca6010102c1d10000071400c9000d60640b0500012400c2c250b004185407070b0880a83c1e0040c4140c2d42c608000c40710740400c0002c44203180c0c0c2c610030342d41c2484201e4801c0100a00484001e035001c2d08921040414212425103891 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 411570791 1250 411569541 411569549
    0x102010f0603030c0201050a0201091707051c0509130b04050106050304020a0f15031e0507021e01050f0c070f17040609061b030e030115080105070e0a080303010510031e15 75
    0x152601c4800d000007600002008299a0286802030310340e101500143c1c01828500d00c09054881200d004034400000a4000d142041c451015100702c0f100482e003040d00100b000790070502054052129000900f843d103802c14a83c0f04c2060045851740d528400700d002c5032000e800030390009500100b08010b50400c13103000d81c0100510190050440e01c1c1001c0c5102d084040382c0340404240c0c890f11104111001a409661040100902003009080c07402d000396640d15600b82c0032010780760800261200c1030041c864503220f0746020440d00c07500d40d01c0c3c0651300010360042c0c40403a82810300358080800b1400d403005002030303003509000c2c3da903541c2d042c00d07805418a030607a44180c4c100182017040e06d02d44241150514280c80c1d04d4141150b8501844000901600b464022201c056208040005144005401c0035000d0311050303e400e82030305003c200b4880d480655001d000d420303034000c000400c0705042c0400411840c40482c5800280ca100340c0302400820450100c1d003108851700d41d101c0c844c06005525400b0014 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 411572041 1250 411570791 411570821
    0x9020916180e0a0c0309050d1808030f070204020702030a050a0b0910020a20190308040b0105030a0201090e0709090e010b09013503040509040506092a0d0f20010201 72
    0x5036291414660000c14010300440242e80c45a2080c0c803134074060382004104135031010a07260000f0f0214401400d190b403003280100c580103200720009001c9004011580c1c2040c0703080c0524541541a003d00011f9440108200d030076102d00060480401d0080c40f140c1c0034241b04289101c0e003030034801a102e29060840000101d05841007200c2d40b4002d4202d007080d0100c030840b03107000c0682038032513000600b41034002405640f8941c01c01904d000301640403141622030b0388030b8400903c890340c807002419a0390345039440090114031419000c1c071540c1010709080da40100c1034039100a00350b07210308803031041d103102c400107454503034682d01c080c112444c2003ca024090451001c44042014000c007221840030041e00903540100401c3d00540d128074024001c0b00c0182602810002d02c3d41841d2401550b5550304035181e8826005079040300740b0f411210201c00c00d0181020800254504401c01041310813001d81c081280d11030b001d01e42d6100054000f03d60a5807109038240321031140b010f490001ba00391380308420000a4 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 411573291 1250 411572041 411572087
    0xa0b0109060507021311030c0d050a0e030301180b060409060302040507030b15090a0e04050f0607080402090403030209030c030706030225020310021b0a11011418010806030109020916 80
    0x441a0b005040d941010b404440c6100200c0981005000814200e0b00c0c19650410020811000c10030b003038001d040041564104200399500d03c0000c608540407588410641e8004100402130134240806500015004a8000074240c13103034000241c0590103a8071581034591030300410000d41c80c092103082c0c0c1c8441c007800c0c1400780310710707680c0080d424a044450100d0415400300300800c3d240c642c0004107015100c1c0404100d40350600f818903da4400c2d034000303a043c00c0d01c101d00006554605c10320156002d1075014201201e140c0365590203034040e40080c104550507200e08180c900d02507908012200050020f510010395420032030a6410084141c4c201444c41814441320000040c0c031b000552030170080240c000141c0b940c8915490107c0104100300009036031042e40c1d210424081c844d83c1019802000b41c890b00307902d04221108041e503006081c1d00d8070141101900300000c950141310f20713580c094001000051a551144c2c00a06030140031782c0c2040b80c0040d449005000e03150008000d0569050011040f07403 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 411574541 1250 411573291 411573299
    0x50112150c0e10020709110d111920101409010605032109090a0e070e0402060d050c0d060303050d0605010e090c070804030b090c090c13170a120203030a0b0109 70
    0x2c401c000c404500d50007000a0500c00c0020f07032003444540c2c041d14044009220008046924400350341140c607510051f24548458580010080000c48500780700c407050805581d80c26020955102c001c03261002c40c2c0812040c4c0f031005040041c4000c110f1045104030026407112644000d0082007002008215203a14200081c030042e54000b815048503441014141448448156044100d005040c1d000d500105480c040c000102025000810780110000465001ca55201e0b90708035443d03020f071340c080e4120304104150081285141c00103540940081422850400900211000c88005038800c0c0c0000b400420f210011440742d001c0c58000b03040920300b4000c074840c50000210000006000e02e191503000003122002c0100d000300b030300e0095030031103003405243c81d04032003c41e107403940750b00480e110701c247c24000703104145032006903507100043c4101c44000c1800e00e03420703a19a40c2c003078034810280c2c0306411400001030202e80910f4052440d50340919200d080024829064a5080e0049410300000b10403c2c0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 411575791 1250 411574541 411574547
    0xd02010606091404022a031206040203040201090b090d02060d020d05060315240d083106030218100c030206071e050f0d0507020105010513090b0604150801050112150c 73
    0x401840030860380141e5401e00e0014400101840d424450350600f245101d420103000c0c08006012140c12344001d10550303680300000c0004034401150000c4c045003110f4418090a0a0038006c1d01c4c51a5014043c0c0a01c1d607682d40000c0c0c2150019880c0e072080680004c1e812000350114003400781c026900b900200404608078036030100c0340800901000031880114101c80c580080c0c1d0004a80c410405130000c01c100307215042040469000c100c081d4110000c10240e01c00008c042c1010440750380c80340c1c2000d1040c9041c980e0880103035020a41044100b11880380b000b12540e04c000d0008211803141d01d4407520104a1300c1c002c2e007030081c001d0020007031201442001c0110700c4600c003180320150a80c600789035601c0110840c2e0f16070b8050011080011403404041083d020b80540c8441d0603030b002100c68000d00203507009944117880401000401d804007920201c0d60a091a41046026049a100404001d515a0045403c64909138040705065892004035010b1003410004c084000031051402d001c1105048005 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 411577041 1250 411575791 411575819
    0x6130203010b090d0201270911030601090501260a0507020c0d0b01050409020109090c021506060406050706090629010e010305090a1529030106060503040f030507061b020d0201060609 80
    0x30f58020400030710343c8400c5a01c14180a041c40100c41203440d100180621125180380c07050068070401458010003410081c0340d44266442003905030b491a14160500c001100c2040c5e0f0415100102e43d02c0c0717505030324064010b426840c825250042c0c00251860300f070000a1904000c00f0141703019007030200c0514040b4081d46032803415210103881c042600000da2004841d80e000c3d82e440303e20510b11301070070340948950200d141c02c290160402900c00740e441d03407801c01c041c500c00d42c4191000710b0300c2000a54002a2690000c200301400381c0000904050a0344403a1004001c14484040b06c0521980540e015a088142003c04031028a01044a460031144243d5650031601c030180426098181001200d5007030b03001991507840540d0801741c150785d030380840380c418004800114072035400c0580203e01d0522840039207203e141c0020440600304485d4400f904c056004e80c5003510a55107840e85c05005460085000d100c0c01002d900610a01d007d0400c0207007100e03805c0d0422410083c94103000c0003602c00918003 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 411578291 1250 411577041 411577057
    0x60806060f03040507051203071106041203110c10050c060a1b0c050c0a092a08130812010e1504090c05060a021e0307020108220f020102010b130506130203010b 70
    0x40c031662500c3d00e0410501d4060140d110741d600001001c0d8507403608901001510711144910314142d4040c80000402c501e0b80201e016030004400b4203420b80b0003291040c0c040e8000003024070155210001d031180441d181004103800180401c40000d2140084141042001d90000c001c90080100d01c8039007803000da031050076504e04400c02c2041d000440034410144140680c0b184014407074134206070740c0d5081e0b50282105400302c41d6800c0e2044001d000d032100c07480f00855058040d0b5610000c543e14004d100801e00ea10714010b03915800180b1401c2d030440b9a1214060280a218a00080e145800c41400340415038000c100c5014a05200c80400014454021301007511001c4900a481d0921804102e00d4040c02c03100020f00c5042c100382140300403d000c00200701c154000c6c3d84907085613983e080000a02c0c40081d41c1981c405401500000104131000d5110004a01c14400071508002001c0000d9080b41c0391705a982407240e40340180540ca107401c2c9a1031408820140055003198035006168019000d603800e = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 411579541 1250 411578291 411578317
    0xd090b03190501030c060e011e0804081603020106050906190603021b01020706090501180b0f0402060c060708010602010c0315050402090a0b030c03070912051c1812050706080606 78
    0x225090700c150601040210300e80901c10800e80d030350b9060003044445148540004030360514102015035119040d9250f40c07030546803140c11480c0002c8000c0f81d4254004200b520900b600b4041014031140c100240208180240c1c00030591500700000c00240040c0640382c103100c1c0c982041010102d00c1c4041ca600d085560754200180c41309500c800c070503c14400000e000c1c0c500e5100091b480200311450748100d1425010f20002c004102002c0301990f0910140e10024241064040028064200c10701d5607980c440d101500803401d1801c003802d003603d0000b094404101140b2108c0050142640c240300700c910000581ca002d0255070000000380f502c420309405224000c980009500c00b458680074840c070014011000c400d541c0e843c109070f10f800290001c0d241100000e00700b010029200064000c01548250050043c0c1a0804080108104c850f20349007070ba0b05006490f0980420720b070062400b44001c0c0150004500844041e28205042820b00c1d080041802145000d21407940c442d0000c0e1842480654 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 411580791 1250 411579541 411579547
    0x2031509010b040207260f0706020a03020d0f090311070b16020a030807030203031e011409072a0b180703120212041d16020c0d060915020301170d090b 66
    0x800640e026050042d034080d00b00f40001508800c10039094031072061079600301c0c402201c22050180400c0c90b48941721140345840c5007480701801040041d40149034502d00d500b00145460340d03102a5030180c603c02690400c0c82075403404817405042d08005481d6040b0000f4025040803400d0541d036000718081c00340e91995208105411200319142d8110314406181c0280c511910350ba90b62500a540c0d0384104c4a048001c10303405030341d4101006554200303050382c1d82d0381c202c03103100100101408a00f0800030600410010050480c0142801c1e074180000d1610158410340310501150800507507019000d0a07091298440d150751044c0240c000c5803c20650703030301080c1002c46080ca84012807800b0602c041800f40a031001074000340100c03036510100500159084200c074165a400c1d51540282c2003000c01d01c0c0983c1203c02c402d80c0602e0980001024580f180c040094014026107424030704904902d881180c0e20f50000060081c1284280e04a0f500300803100103044100e2a00b800034125006845141490702e808 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 411582041 1250 411580791 411580801
    0x9070e060403060603050f0d030c0503010504050406181115070b0103080a09080f0705011103070c060503060a03060f0f0b03070303020c090705091e0f0a030b0f071713050c0607020315 80
    0x21008507001143c01000c01c0c0b000390707102e0a066464603100001101c00380703d46201100540d011303025607102554140c1710507083d80e207480107000c05404010800c40b04241d940b8040c01007000002116034001d80140900d002d140e51760011301a2140d000c080800060200340902c00000740705000700c505599020402a0b15070606c0b050076280100f107504000c83c207000d02c00700b405002c00d0000703401045400980c0c0e480c18013106002d0041e202e1090507c0038011704421103040c41102d0040740110b80201c1c015141102c0d143c1e1329154541111b8110748280065031f1101404a13030100d840c0100640300308114042d0000900e1654082d6a41a400c9c0f4524061402440010083c40c001c0b015214451405858950072144141c0c140043c2c04240441c80d01c211000405c040250a00c072070604103072a440401d89103507880341034201082000003410710703003005400340c146401105a494602e000710440da010700300035801403400380d0030911000c1c0000d021350014001c01c005030f03a0001d8012040d8061700c0007c00c041d294 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 411583291 1250 411582041 411582049
    0x302010f030e0703120e0913020a050a03030e04090203030d0e06040b010b0a0c0f02040b150a0809030f0f090406270501060c1e0201020c1c0312060605071e06061205100b09070e 77
    0x450950b681c4000140d0822441109081100341049e20031a0101c132100d8880c0100003024002e40005070018081c0412030321141010b81c0503c24260008046038201410312580b40141c820003100d07448250000018007040109064100b03000d0088107500b5030902c0000b44c0e0050030385425032400b9055268615500c010340d10345622003031103108040d000a409090541e100c0e00d06501c460262000601520009003d92401105032031140510301403252030102d0070039a8001c19082000c1180c1c0c410780d20500040c2d031404a0061544000000381070000d5070201d039000000301da405070700c00400d00000d1a03210002556948004c140e06001d1500809000fa0a0004034545442a4141a00581c6840e01d020300380100003903c0140c1c43c4030303039103540c0040300143d440020b46070144510408640184482030004130b42014030f504402071491910417181043d00c8200642c0c3c05640300c091070a83d030200350024414140102012265034402c01e2041600541c085814554014814002c00c5100c2071000001d5907 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 411584541 1250 411583291 411583307
    0x19080a02090d0803070807080103021f1101022206050a020a061d1203100f05130905030c0d0507031713060e0a080d23070804030f09050d0c0302010f030e070312 70
    0x21000c0d2002c03001000c00d142c04031265000703540c0d4101045d151700004038080c2c0302e5806141a2031f400340540d04048091440141800c0380040b160062000b41c180c403840000c02440500131040c450b20281469600e01c144420301d040d480e80061007006420401c0020b12500040d055124540c0100005542c607a50ba00c098023522800d446108180280700807101b00c4031036000603501405144040040789603070b074040441c10340c0d41b80c82040c4e007009103001c481c560800158807031503010340034a041d645080540c04c15203040000056010010480114051040c5548184960803950a4000181481c24041030030071040018201c000c0c211380e10b903c1424882c40c41809061902584540503607114081d10601c0070117454068510500202100d82602001300c11112644c082c505503146d4035269101e90301c00700d81a224680300b903014813281d0800002d40e500e9030596803d504e4003803036000001608610004001c0e5003810f441a0815080c0b1400001c45000071031104d0850340e010a482511a69500c41525130134 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 411585791 1250 411584541 411584557
    0x5030907051e0603090c01110304060905040c02011814100b060712051c090b0a14130606030c0312020f030408030a0c02030a02150c01050105060a0c11130e1e010219080a02 75
    0x30324084288008440d0006006c001180241c0b503000012441000345031303a030300541c03190500140c04040c080000d41025032052404040c50f10021456107180305003000c66500e0301504a40d000b42586505d0b0401300240f0620502c0345c5c113440140102d8200340000740407170050807009451761645000804146006004940100c80051600c10108180c11500390042012101c2660f0001c409000580d101e1464401c11051052000c60703681e5a40340d14801c1240101208012130f40a84c1d202c0010012914000300072000f0f52280001004070b0700d0394180282072450f0700f840d1000701e0740700380801c2c070a100000c0140c2e113003032440d464031542a200c940002442c01140450107500710803405210500d25070240014661058020001c1c0134507681e440501119104da001140e00181d01100400002441200d087c54207541c02030940d030101c7d2040a00c50200c6100101c07004890388002e41815544c540d0718152001c0300c40c1c0000031810542c82100055014541c94211420401c031300f4002503c8100c0d03a8155a019 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 411587041 1250 411585791 411585799
    0xb09010329040617190c080625020a02010909020a02070f1e0609030b0a05090c100305061903020d03110f03120f01090519020c03070f050a0b060105030907051e 70
    0x882042a4007001c040d01090040c001c90034038a001c41c0d080420110303050003a4449004012440b0340c0c0c0101310075907800c10421940c0070940c1c6400074074100c04100041c050500003605640c01481403c2c0c0c003044107440480e200070354000501ea20007503a0030800d59400c50340c0540340941c2d10a01908101c2c104440c80d0050305850111107800300e045c0d02c003107180310800c4140f18810f4410a486200560740c240c0e00341710040c01400220002046003100da00500e4003d1b185004a035165600e1400207001c2c000b1030380c0580c001956031407c20400745040c0360301c4010180d00088142e00a0f0460f00030500441000902070148110012a06082c040c00c00646040c040340c0e005072a00c844107035401c09034001e401d46020308843c08050005c07440107101d103d4903018590068000864800c4000803c01030340000c9200c0e00280400d005460201e4070007044c14540703600c9103010b01601d40c5507103050b1441d184003034090390400c00180100701c4d0080000452000780c4100b1107d840c101c00008070915865444103140c1500 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 411588291 1250 411587041 411587081
    0x90a051302121c14030a0c0c02040519050a02040302151b060108060a0506090601021f020f040b0309071509030f0c1505090109050301150306020315040203011512020406090b090103 79
    0x4410b00414110304101d080a0402260040c80c0d00844051071134942031407901d42d0420101d1483d003125481001c0112a504012100c10110740004088550403520b200c2078652680e02c80c0321061141c0309981d40302080040450070716081d5001f00348200d06594a00524210005040c844c6502109035404c0e690301481c115a80c40da114694251500750694410342d2280c10f01c0049812031516080440c400d1360184d0061442c00c05280b0041040c030994a0600c2205501300410080d0401d550b000f00054424440d03a1503070707400e21034041072030254a54031440e0031441c13001c507092900c0c0c3d100b0046000c0b20780040e524480311559040040d142444c43d4030001c00d40303519242e9400e81030303007140282c480b00100f42c81b04482140d89005050aa036044803840017007030041c0b0b03403d000260165024580040d1b0315449507006481c84001700b004c81c0d000781c22000551101400d40c441d0284d02413003654080540d28400e6060524044c400b40c01d03841c0d18010f43c071140c0404507541680da4401e6001c0822008000c0707450300 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 411589541 1250 411588291 411588319
    0xf040e10211b030f03260109061806060c0210020304181d0609030a18090f0e210a1103070204320c090105070c08010c02030a0306050f090a051302 64
    0x121000400c84102d480c0c21140329880d480100d025040b100303c80c1c224043c1445100e072550100c40c1c1e070782400d8070744421070107600c00c0c204d07030000f08440035029200000001030390700e00b0f101340348424140e10910302c00e40c2030500e8000c1c0000381e03100c502c141c2c0c113030f605076014150303d030408405034114061500100360b0101e400e40c503c071220300290400140e00101c1300010704855200e0030280c1e16100211541400c640c42001101c0c1c0281c4030f9041d64620101c41c1d8103103403c00d034544c42c01e0001d4852070500d0300c103450f454048100c1210b00500c0303c1041041030051421828103031f46010543ea01a0030041c50a2151900c9002044841401114007541e40100104490b1001d5400c0c0e1145400e0340d52202121007550034812074041c81d22824500a904404100f420300700d600340111110380c0501c404480c2001c6160340023500c00001d010754190213280c1e80180d51140040c2c00024203e6559a02042c07040d000540084c0d450f440c4c52002d260400d01704000411076950b002102030071002d000b034009400400d010313010b60f = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 411590791 1250 411589541 411589589
    0x401713030204050f16080a060509090f062a16020916021c050d0b0a0806010603051609030b071d1002071a120114040f0c0503040c0b0f040e10 62
    0x209891085504200c241c40b05503030031115100c1150842043c0c50810050b0007800c0c000e080096220b00b00c0040484c0c950345a0011840324601070300d92056a41c000c1103002c41c40308091200c164411010201c002c070440c005000d4040c0e4050030401e0b0200c0d1500010301c803d2000b000b03000c4400c103540240c1800302e43e00b440d42405100e000340c01090001401524030384140302e820076600f980383d035915a860300e040c5200098900c4c014141c416500d13074841a81140000d81314414440300e80201801d0310002075610f404070401c00c0300f20042c0341450400000d070300248002200c55410342d8010300c2c9031400c0740e000030843c20801d24003aa6125425480440511300f460b0039940000e04200742c0b841c408104020080c2c0080c00e00460040c04080c1030074600702d500601c00001912020043c2c90002030002c140c0710701c001524000c4a00328540e88000400010821003403141c42d640c0c45008143d2202d0302840d02000300030584c014051070113032080d29920100800d040c4000d04c5441009441140081c0704c00001c860818 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 411592041 1250 411590791 411590827
    0x80a170705090108070509060d051305010903110d020601030c0b1602150423030a020105030408120a09020108100f090209030c09010e01061202030f1303050d050408034017 75
    0x2400070f001d42000808a0780710354151641f0300381c054801800c0480440941c80031340340c02400c03201503054021204001c18000d01410014a000b9103a20f003200c51000010f9040c001c00c00d15a40640d030141c8010400a080308008108889003401d019464081d07041c010b203c4000c00343c0c0d001c0d40c4409a08070302070900c501c00780100f04031001d060686084d0840c0d0550180c940c0c0050034400e034150042c0d80a03401550285000719032280c0714842c01490807207100a510080442510f1880701213a84925040841d6040b04501da00000b8031481c101e40503140c141c0d640200366450203075500481e00030032507103040c0d04c041000030145000106010f2007580c40d1452500030080905c03412000800008a0120300c11742071088900031149030507416615030303403c000e0710040e125654003282040302c02c100c0c0d44004c0c0c0d11445103a00540c8581e60241d6242080c0d1400c880c030501107040c08100d111031010089a02d03010900c021800f070328065061b42d841d88242007035410f4a00581050071800c2000901190032821500340b = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 411593291 1250 411592041 411592057
    0x4031107060f1701031101111e0105060f01080f180304050a090218060703020d030b011101020304140d18050d050a2312030f040b06031c0503060a080d0c080a170705 72
    0x8584030f0000750240500d02d0f103400c0c440074054940d001008950303944254114516603503000c044404440182d5600300041e1944507004c14603956517000d100140c9098810303c410007100b407078401e0103400c15880350040d400002c3c3c0b40100c0510041c00d420b900c11024010b03500106401803031450503a9440c0007401c040d40c401e1062504140d1100882913283ca0300e0815519590742560003480c40c41d0040700c0c10341c0144001c00e026414000c004604541d0f6031002d00003103220754891010701401640d0b00107a185012460460300301031000d045021a5901c203044d049800315031040301d00003152525400d00f0380c02d10b100c81c40c0141000d56000810400500c05a940c040c01047c2c02040303417400444044103149500060703404040070350020001c500821840300c000d03034100c0ca00070103451885a040d41c3e10107150040d40c030f03a04041038006c01004003514200107440000c054440c00351040032110703d001480d600441c50b009280100100703c000310144962078000343d00722050007084060a00d08005407298010047d = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 411594541 1250 411593291 411593297
    0xc0a0506091f050703090f20010822021f090807060305040c06031d1c080f0709032411042c0117190b011701090f0b04031107060f 57
    0x3010401d0014002000340d0882c020364000d0100c110079400007005444003808030010951102010030226004075083e1100394842c107030814540c5108105c0f4000045000e40141c1030043e0f160400029080e1100090305e01254145045181201c0d1701c0003504401200380c007805002d6524402440c5160010f0320002034a03844011942c140d940c4200803815100111401000d01103415410030809000b03400c001260314028240c04440203040c240f03507241034040784010928800c0020f620110035000a041a00700f4492001c6802e2440e00130b4010344101c01600c0010080384c2e91a10351440b41480d0101c041d040d090825084c007065a2403221240190000d00031304d00d00d62054080450030b0700050f02c0c45e02140b0500545a09503a2030051009409854038a03004294000c03010301500c6800c0ca0403a840c0380d1480317141c038182c80f035041060400e501442c4204512043c1c3c0341c1071011004c00d02400b0f080701605d81c4006040c82c1076a076441c0445600f40f02d528015030754440e464020030150707044411f00950001d01e503 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 411595791 1250 411594541 411594553
    0xb030c030106090b0702010516150f020d0c050705190222020307030c030221090a06060e150a030b04290a0f0506030a08041206110c07080106090212150f04020c0a05 72
    0x62138110507110341c2c00028007142040154050385041030b8800c00000340620002c250302c014400c9100c01391940380300e40d04d4626a001602400c0c4090a00c20900c000d40c242c50130034180041959119034540c4c600c41d11035051101050580215600d800c035841d21803403043c1b1201103807041240007601075041a070703451010a007840c0842c0e24451191003603820540140d28041802c0d02c10b40292a04200c015000c988140141070316000404c01038080c102c014403003801108081c0c40d08199800c0000c0304400f4181c41a00081810070115030760545564000d500010708030700d0034a200102d07201513048207032590601544e420800218401c954003906281a40983c00e102941e07400303040580707502001c00c004006040a02c400d0200454510347c0030751103845a48000b072009001040d042058004044458070395002c00d40610400001380129030007030040c08015420514503410388481d0b240c0080c85080d21714002c907031160183d0b8030f25408000c802005401150781d01480210551100c01107407060303403288649 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 411597041 1250 411595791 411595799
    0x1305100c05122a2107261b0f0c0109060f030203130b010303020c041a1309050c040603080304060e0c0d143c0c0906011101110d050f0f061c020301060b030c03010609 72
    0x8407038178035901401e41c18100003452500c0e6940070b14034000c142880c005101c84280001c01e101400391510388a802000168031604089281c000c10036007560420145142c1000095003007d502070501a20b17090144c0c03259146003040c090710440e06400b0b800e074840440000140360300403614001559099030288030f00000003052200c4445800d40c015000306581441c0d2013600100d901c03480c0c103144200c0540d0031140c500e07800182558103c1e04151511030000080c0000c22005201c0c04c1c54100a80f0003411310078102200140c140040c103d03010303020310464035410300c02d00c0d410700685410311040300001104206184007400d0381c14402d000f4400031700005a2a0300d201c0000039003d01c0000d0000c04603c07250381c8083c01150841c02c0707060040082e41d02c0e0354107800d01d450400040d11400c407a12a00080c103192581d03000001c20005080711988817001e4092003000d8503804203150820760344e007490101811051011a00500c150343c4010302c026400700c01d000e804a01200203604840251303441107891516 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 411598291 1250 411597041 411597103
    0xc090127090b01090c2001051e2701380303090307060e0303070b04030c020a0e0906040303020f0408030403060c0306081b090613021305100c05122a 65
    0x80030300d020b00b075108003000404c0305803001d4000b0585814189000180700422400c00e910544840070220500e035128020400c440c04041000e600c06043e08890b003c01c1e0074003941154002c0f24403030000f040110401040003100209401000a0020059000c04605410350a2050302c00d100281c80d229205584555140b0b440e0002c16a0034048005001c1c0c1840f81c40d050b070a50b4450403030084290940000d004980114000030786c0390340701d14040c1e1100341c846030340c41c41001381031502d03500040502d00259060029240000030069440355160800582c0d44018801510240c041e940c0045080e103c0090f000c030400c419600038080811072a01c0900a840e21010503940f01d20422000c0c2c2d00c0c2444408904465103441022290405409480312540f000382c82040c409070790042e84014400e03942080104124206010342c151b40144600c0d01f00100102692115151000190090707202040450300d02035035516088040400382155040c40c0c000c6200303000407600c4c8c50740d144c0c0c10000104840c2c0c51400700c0c2c00c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 411599541 1250 411598291 411598301
    0x608070b130b09030a050307060c0315152a1103061513020d0b09040605040c050405071403041106190206090a0f1218090609050603010e07060c050c090127 68
    0x44070001c450501410000c0000c000d0300309082c90396061052a5000004c550180000c0109900400001ca194400300c00e014094550864060300c0752000b0401c1040f02c3c4101501c49200340401d071034259856004103402021020388103031456844403101d1052000c0001d080408410071038142d00340c07403095803102c042900034005044482e40058510703003c020b508660f41c0c003e01c660076100100051120018002c40c0f40c03403204a038204e41e00c0fa690f80921050fc100c0201400c0180000c030303414005440d140034014000c060800032404a16400700102e07080080e0410a040b9007d40a481d09484580c03106000d0425800700d26441c0260094002281e42908089040c0c0074240e004030348803500008075600e06120302e607000e000d8010840c0d025110344441108a0182c0000c240b02500880c007a800e025051085a0340540881d02c01c0c2e240002e400940c6001081c09001ca8003c0c2c140070911040d541069400c0100c42010070350b001207148000710321b6070103c0c407001c682c145100c0000b407484072110710b201c0101c1e8 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 411600791 1250 411599541 411599557
    0xa05070618050c090a022107031a130b040908071208070f170405030c010e0106090e03030f0402040506240a1d0904060c020102070503190f140306060a030912030608070b 74
    0x60032a201480032800c040c3c201d1034001c030041c00010f281c10a1f4241e105040c1c0302490400940203008400d010003151306000b090001503020340807621041104c4000781c03182480d2a21001e91301d446000f0400c0550341c42e03210400300c90f08045060340e40d240600d000003050310001e400c20041184030303000c90441807055068940400d1551580856001c440401c40800c01001b80119801e2000b000405000d500a01840b40d80c4075015001150050400c22600152601058880310759030040c4100300d41086d1500c819908550150303000181c545600c404035000040c4074070700004a0304000041c41c6d41c800c0305002000c03103e0080c1e40b102100605a1034103880171000c0b410a560081c8000c011501140484d808070810301040c5c00014980f0900d42d9800742160803407441d0f00c03007448442e02c0e948080c40d0402d4108010030301034645087c85100e0040701300c40c94040640b1140c0155000319804000358000d502c041c0715a60050400c1c200c4500c0010001d029054170b02413020503000d0361a0008481c5540c0054400b42 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 411602041 1250 411600791 411600793
    0x70c170f0613020604080f0703051c0c11040212042906060910090807060302040e0105010203030606040905060a0f14100311070303180b01030309081c0507260a0507061805 75
    0x980b00c4a81c00740b0703446070b5a02d06980c44482004002030050f000c004004061802001414607940b0f5414600d0414a4006c0a403407010440c50f00c0c021115402002e840705198000c000a01c101c4114010400034095101600d00d42c1e4001e80500c4140414000d40071100901c00e00c1c40c00000c16000f080281446080d1021034100c20240001181843c0110044e29841c5091030300100442d901c1c1c00a9207404030a60101c804250700107002e12407200c105001e0350240000780002c1d81b8600701000402c03011302c100d200d0324145581c1c1d200032039860380e40e407003900d0b00524214414042e616101c0300c01c0c0200b18800039445104101c05d02154644502070b00030443e01c00240e54615051444c20b4406070b014021081100c04071a890403441c400042c45540c0c3c050186002c2d80d00c0c1071185041011551a00c4c204c00d218405405d041c0a4110003154040e0440306841d0f130243c0c01055002c49040400382c01030900e0a514040b00000c0782d0702d00700301e6002c0041d08540340a4641800b0200c500c080e100250711050700090f0403 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 411603291 1250 411602041 411602053
    0x62318011412131e02310606030b0307090b150711030303100501080a15121a04030503040201140c03030114040209150c070902041d071209050c0a06030203160e0d0206070c170f 77
    0x2c0042d80d860000e000306d1002d200c04500980c07280480d10203402c6400403950305d02c0da0f61010308080103200c003d0040f900c2e00b04644c440d15400240c0aa050b2010803200c0d820010b80d9034200702c412950b50201d61030141c1226142d00b8007220b6a1003030502400340d07030300042c0c2250000300b8040c202c0c040e40c0c086c561185844040c0c5800c1c84006107a18041c06000e4a4003500c840d08240c4002a002c805807240303000c0d941c0c4540307074100382c8001840c44102d500044207858091014401031240442207078115800141c0e4607020000f14030115029003e440340d00c41d07100c2040c4c1d181c1120f02c0b01c501e00070052540100259030340329031a012810103e008a0046075851451503821030f00c1518440060398002089043c002c542c0d80482c401c00054560b02e079800c586680221249064500700300c0b00c1d480282000c0d0805504614003525100c0c0980841810074041105400c51074070180c4031803051103429134001c2d00b80c0741d03240740170709120410010707a108028034100c800c0400008010003040b1001601c07818000f4040b = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 411604541 1250 411603291 411603319
    0x15050c131707080709090b10080606060306042403061b09050f030109080d0902100507080910200708061518041b062318011412131e02 59
    0x41d5a0008204481481c0b045030004284004100002c200511440c580415180950f01d481072400201500ea8100f5006680f011701c410740c40443d485502140980700a6180c2d5501d80008000d0a10006003440e4a480031400d4014805110500d80c140c90240c0014403801e24802500c41c400d04001d8000c1000605400d01401146080000311160b040020004a800b401c40c1c0c483d2074443e48540707081032005980da0300790421403d00020f0700882041310700b421400c04c142c0303440f800150321555843c9407149040c01000070480303004008002d07180c0c4402c07104207200c0d41414002a0782d002c1c20b024440052040d0800a65a5030b2840c1008014102c05081c4189810b5250003d4405c0500900b0448100703483c9060414010721382c00449008003a513940c1c112004040580401c0d0254100310241c81b180380800519100080a0324a440718410a20308985036249c03508040c55180207880d80540540018020701c42401c0700d680540c00c0041c004c0c000305590f4500008803c03808140944025080f0140d48401c030 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 411605791 1250 411604541 411604559
    0x406021c0e0d0212100213090b04050705091c1e0c05030a020a0312030615030b090703090210110102070b0403030b151306050a020f0d031e0905030f030c0d0915050c13 73
    0x1600801001200e8002c1701261400c8140d0b0020400241d011404c01d90400040045004440140d442a2810411130402c12401400da20031958aa40560000c000d074072900c035a203d54081d40942c2010442ca00c0c0b24404d1606419524618400e40780c0c280340c1d5201088034070700071510301f1400c0d600401c045078045c90740e91407281900d0131100b4241490f50714030000581041c00d0f00810038503001135a0000310300701030008102004101410942c2010724001010300140c0300d101c003500c103150440c100512010309018419000e44a040c00060031200f03a00c0c00d00c4100b6405401084900c00708484204600035040110000b50080690702c1c480c0040091042100d42d006000826a08005206481580b101e0480d258503106403888038600203a921442901e41001c00800f082c2020300448052000d035055864146e030b20f01502c0d5503000c440c03800001103100c4080060844510300d107a44000d12a4880300c0c10000c0d005a804410070f4180340c10f00000078441c032008001c482c0c003820303808104034103141494640 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 411607041 1250 411605791 411605809
    0xb0f03070323040503041508040309061d04060803090405180709111210080d142a07080606040506010c0f1205040803040905090705030304030c0e04050307080406021c0e0d02 76
    0x500c0e40e0510a0b040b0000214418580d80e229a002d640115515880c004009605080e040e554008201115052000007a0f01580f00b0040f183c40b841c00d00114000441d411000030721340402c0316030152908100041d0410040060825400c00721010440e42e5030340c0d403006c0c003602e00c005070100c2c080d0040c1c001030203070b01c001ea406200100c502280c954100b241002015030022130079900410107032448141004448403c001100c0b164a191030013031240c0d405811036240d0703400b800905070300b01c0ca0040300300b08001e0201d482c0009000840303821190b003c3c0c8e55001c115240c2900f61072b10390055040c100020380d59402401c006920590bc828600902e02c06a240c200b218410011143c041050810000a03244000c0010b000034100140300007441c6c0c00e01c1a00145041c3e9180c7c00340d4000d810602c0104085201011983c088442e602d01c81d00b8aa0b460345000740c2188546040101000300c0030402080c21540014040300007401001e06003900c01e540581901c410185410a40c1d00c044030722a441e0040c00c044500d = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 411608291 1250 411607041 411607061
    0x10b1c0905120706020717040b04061d06070b0103050606010e0d02010f0c05010204140a0e0f011a0904021201090b03210c03040f030807050d050c03030406020913050c030a060b0f030703 81
    0xa44440d1021400d418586511203c0280e400ea600031400f101070001c95030a0000b042e80001c401d074581b51030600a4100ca00079840b40c4414048092140560031030195045040154000d01250b03403100d0a190803ca442001e00040e109032003078100145581d4002c00c00d11a400ca401400411a041c8590044811003d69052081082044810078001550034000362000e4110400765040382c12000d400d0106440069110902c409000e01c180710b07070000f075405102d0540303400070558100c0d5150310310351884902c2034071003031a007103440043c03601c031014007000c0d800e03068806284050001500b1101055030741c40c1d01040000b00001421610402e4018590041c01d8504585050b6400c09942e0f00d6a0b10500e801070740241d0342d60b4400141e4408012007401103c1d500a0241840c070706001c002d2035101d5403030000030030003072000b41d0019541c8400d0360764010240206a5804c018000d0b423400c42c02c10b1505400c151a031020843c00d04e1004240c42084009440052261540060455540c03002c1107010341401c080c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 411609541 1250 411608291 411608293
    0x2100218090c030a0c031a090405030c070906141e040209040b06030109050f06010503040c12140d020a110f030c13020927070806010507121b03021005010b1c0905 71
    0x24804015240c8814151240c2000c4042c1900c0e40351080e400c105448007044504101840c0100c0710151b003120200c081013403a02510145007c0c1d1741d500e08075145200b030801c003074043d1040ca030002600302080c1e005001510440e1484103071020200c014004034026444503a80c100c0d140d2541e52100382400d034082c25881030020008180119205c02050599102ba048036078956260070402410720951240b0503008075082c030304180f4510345611040e5040b8030318040d28032940c190300e07070344402d2180c0610980c0f94401c0040a40700082804100603544200c02074086810040d0f0000210b284d1a0824620640d1607025000c0c0544c031a154082000c45c01c002040102e100d41e0910001c607407507c405a05d0110a100c055079403411020f100c0074070b107130110007e10040c20441e000c02000700e56680f00702540d0406a011520040300b008a010550f40c5410002c881c1151410051041c2c080c1640018a400354508411080055980301c000c2a03480388200d00350340e4a224140300c02c107120341105501c0003034028081c0e0 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 411610791 1250 411609541 411609577
    0x3090c060c0a150615090306051b0f0f0f041e090606140c01060911070b010902040f090e01060503012c030405010f0c170703030906050708010819020f1f0f03020a021002 74
    0x10885c0f2900d0229a520713000094080382061040040900c1400c1e00b00c500e01c5d00c0000e114455449042c400e100f5900c44660710000400c19500d00c0310070705c061740d02c561a41c9000d03c1c0ca071030311164280c03a01042c1280080c880d681d03103100007440c42c51031300c114001d82c0c2d26990f503c5190200c6602a014552280c04140041d41d614107000600c3c61051250700408030390780c08426071341e0b485420304614240040e0401c207a07862040004015801d52a880c29044420060020801c801142d48240c0102032b10b03802141c0650a140e0403c3d11482c06070f14a0280c00401c0892142440f618881540d4034040c43c0291404103005e800c030843c25502403c901c50b4001c0c400c1c0225844003101080380a00c41c1c0002a0440100380c40e030901404203c09401169071101883c41c2003940c03036152242403a9a04e01d980c000d00005410680c0ca0015526600002c258090000e000c00301d1010b07802252200d034a02c00001d210000c0d203c040c1c1c5e160424840e00032100d0004041e030080c0003903c10144480b0082d03000440070600c80c1100 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 411612041 1250 411610791 411610799
    0x50c0303181f02060609060d0b0c0d1401050d0219081515030a0b06060d0f02041203180e0c0a09080f0f0f011808070804050d060203090c060c0a1506 65
    0x410040c40100700c0a0207094200504000b400102001025808004403244003110b1245500146807948848200c54618094807140b02282e8508000e12010b025424020200002280000014070310600d48080402c400382f6594009081000c0070300905a001003103d48907400f626000d0522080d00e8000124102c0d96070f621080140b0b0807000700301c42c03d00092000104610300000e403980b00c100c030800b40c020303000c0b0b01c040b03541d01d030401c05005160307030b225000129980b04c84005079800700d9187e801c400021503555031556410048408500e00490000e001c0c0698544244443c00801c070407244c244006064a446107015a8800d030081d220035020007003000790004055204100444085a803800030f01101d42c4c40b42c00316820722000d4a006185a07041488520526006071107080070350350412200c079140c2180b850018170a100740d0303019a601100542c07400b01404080e9005502509480d001c40d805004044180042401034004c8041c107904a440098042201652144400207105c030300000c10300e4071 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 411613291 1250 411612041 411612043
    0xf041b0207060e010c0302060a0507030609060e06120d0203070807020310050c0702040c0306050d020111010f0c20010605090414011d010207140304080304050607030507060203010b2d0412050c03 85
    0x80100600607440080300300700d8075401a80300d0074509420320f401c9510407860f45001c0d568510107032109d00810703030306c80001d100b803840380e072100e4087e0030403c20522209a449201700301800701910014442d030403441d284400960001502c1e0001c002c0b0350081e50608446032603210140d00b1000081c0e805006401060074a40c2c80ca03c600b501c91480d08020300d0b2107103d01d00511007180c258a803803c080c940340500500140e40c50000c200c80c260f60910709802e0110a100c041809880f400e00140d4055040540030f0310079940110102c00d1030325400804110044041c03d4042c00c0e03854138460150820030f241c011402155000c2070001e0510b01c03060000c20041d00c2d190300398002c01d16008074185aa54049044400c00000078a40790082084d10300643c10b150511654544a110300c2c4101d5108100000d00c40c0d0425014000342c0c0c09560308070038119107a40c0d42d4848079489501051440c80041c400c1c1c0c1d108003500403140d28881420411035441c0c2c1c10182011007806c9858100142079503d803045c50608081a94 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 411614541 1250 411613291 411613331
    0x30819060306020a030b0a05030615030a0c09091e0305040302040b120604080c1b13021b0f1011130e0c0c0303040c090608070b03191112060a050109050604050f04 71
    0x11080340011382d161a6110010700301c0c1c08125200c2e01c00c46c4e101e0010003680d035002500315000041011000c081d00301d40700009207000c0490318001c1540d480010001140226541b19104180c0544006e41c2e007500041c00c0c04404040354000100450750600040c070150a01e176115005501c80640b86000b030a06020741a0700d00141180d08072a00e070400100e0310880b41062181506070401c5a2006541e2a00c0c0400100400c41000f401603205502140034a1010500070052200d52542030641c0e0710345204000690f00d0741c031912409400030341000740885c1744290306412270740c2c010400180c1025890510000b00c0011102825050034050144243c010029041c0015400395100c1c07500c040c6100c3c582010035090740e4156114524a800c10f510030001c0d00701030030071a58440030907144103480f0005500c4403c000c040028900721144000b042101c4110b00290140740183c0301100d030280400d560b807004480c4000300340560360700894180000c001e14180342489100c0c00c0401130000c158084040221441d1743c0d = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 411615791 1250 411614541 411614543
    0x10f0e04031b150e030f0d050a1d0c10080708070c0c08070b0306040c030506100c051f0e0c09090703290c0703141204030804020d1b060216030309030308190603 70
    0x4a0303040558000c10400e11a402920076500702650034481e17400028851030049180740351440751231b60000361140d04580c0c4002d0f001d40c00114401d216150100301155101c250107942030241024004c40000349000d80c40591060200741e40e104055910f004c0200c0300700d020109c08507402c1c603030004089040642440b8010190055100c240e1716450701800304415602140c40720824140307840103200c499203608041c081203c107c0d09195581142910704240340040f40403181650b189407141c00076400791580c009038210301c03401085410824059040140b001015901c00000358000e00003000090044d684032801103c400300240048060b10300300c1e0540070011281686162000956003003010b40103104400e089074100803050404c11810706414040d100074002400380500e020010b4119520b01c20119402c56114811940882c01c0702443c0380c0e441082d004102c0036000390142a2464035100c0107900480e03415540e000c00c4a132845e1015204100058007285001e40703101c544944150039405018011 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 411617041 1250 411615791 411615803
    0x2103002090a150203030c07170406030b03010c0e060409150906030f02121b09190906021812060103060c12020c0a030e040203090a060c110105160215010f0e04031b 72
    0x81c14080301004640d64098101441041d0207008a83c4502da001050303d030302030303487c043c410364800c0d2a0038000000c22030051000c0b0124400140816440e41c1500f02c204108000e4000b401108020301c0184d510780d09007440c46420940c10b101c01c0206001c0c541014600341d660600024071280c03506200400d4a046030400c1e110107203c0c01c0c9507011418103c00c0101c01d2001c000240004584105c41581c1c1a0b9416410902c6007420710041040111010341100c0c4140c03a8034000c000b603445510701080a504003105156080b038400f10211903e05052501800030324540011340226801c664402005001010202003009401e049041080055100810310200752200404654a05190051030f08681318013042c0251700600c10711800354000107000701216032007c6c0200d04822403000031180c0440b10150100d4039801c08042c8806015880c803c0f1001c44080d03402e032200100c61040c0c0c0102c41c81b00380b15031000404200f80c00c0100e038128006c1580c00c00d120385005c035a00600007600e10720040544900740d540c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 411618291 1250 411617041 411617047
    0x1306030512070c0b1c0207210305010e0c072301060e04050708011d0c04050a15030c0e0901090203072907030e0301061707030602071a010806070206100302103002 71
    0x1030084001c0003d001340000803419140401c981e01c800002040b440c500240c0503000705a10040118450500c03642d10310b54519240c0c0d0310502080180a08402e00c21502175140400c040b9090030800012958400d8001c540700455000580f0101c5521021441090440d5038411000c0f034698a1440003901590040c4024007025090100c51421680a000c603042c0b00305c45900d45900414003c03e210703c40c980200c1d400602940c400245101401a08400044850400d0300200c10007030030b8a004010b4031464600a038199840c60316442c201c0d91480300c0a90702d0b61081c03030100021920801c040f84020405555142205025011a55182c0100504a01144050482101c00c2c20700b4842c01d8020915442d001e128024803000c2180c070b4010500010340091740005401b4280002c0e03d890314012144101200074079a903a101c050385410307082c0d038240014024480443d090189402c08041502d4000f041f04040220b0503000769120107601100900000b4040c14a04006000d140302d200c01100365040565 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 411619541 1250 411618291 411618293
    0x31707020409080c101806051f1217040e010b0a09150903060b100518040b030d0801030b331c1202240604110706051906050409030806130603051207 65
    0x41000301150040c01403500e4440c0500503015140d903e1180c06d0340040b000500c03074864110241d2100c0c1074817813034540700011b02c0f13000903d03400d405d0841e055540207a040385020700042d0304d801040c0c8a00d20070344d0000b819800041c42411940b10050201e024142403400d80c00f90768201c07a42c0c4c2000311a141901242c089103081080c0a0315019041e07400a044603400003e0043c92000303800f5000b01c206603000c00102c50210300c01c0e6191603000c40c0044070004c04581026401030300040c2110b20900080310004151008030b8001001c522154200130401030701d0446400c0808282810b03440f80d0740099a001513201c1c0d171080e282903442c6044c130095018550059540c100403c1c042c3c030300038004040300d032444822601d0404803002d520380c1350b812003001ca81c04a0381074006055040030340504640030304024984000d018400080b0b40e49503a131b050040806000d0265200c0400044844090340030f804689058002009850b1400f40380d50b204415017000502c054803522454509110001c0e00c0c0c5100b1000100d0310 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 411620791 1250 411619541 411619543
    0x6190e0a1407020f0a03050307031d010504050c030f03070b04020a031b0305070506130e04030c050f070f050a0b070b060109090e0601030218010302011b0204020f0f0a030605030610031707020409080c 87
    0x980c014150f0006109a440b01d010b182da95a8507448058104034004c4080f44010784a40c010300076602c6a201030f42030351481400003900903c0e0658040740c0300d20030054250202c1c2400b10300b4000000503000a9801e01c086902c407840030b1940100304903401208400040000b80201226503007118540407001e0b03a09080d460424504104d94201520403c01880000796a000254420301600c40140000010b0f48503841d060b62140d0120b60014494001e19480b00e1f150342d40011003a080300c1d60f600c02c070203149941d03600b40b1103a5681402480e10a80080044001140c1e007001c0c03060300184185402071000c1c1c1e488485900b101c40b0500c148845810130401042941341c440521191168076441250007545984d0011f0030308614030600c882c075001001c284805664540c0c1c141d4030306940320b40040b59a009681c1101388c05a0040350503001092030110042440d0400003103680c411710010102c14880d0341991604800400242120452602d04104000040c0c03528064240b10a2040c0742040d2200c854052103 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 411622041 1250 411620791 411620831
    0x114071505010320041a0402070203010e0a080d140c07140a020316090f051e1b0a0305010303081b030a0f02040b0f070309090c020c0111010b123306190e0a 68
    0x154842c46c05c29081840102d01e81009012084040f9401a43c540807840401e001d044009110207040c00f40041c200240020b600080c420f03584024000c00031031003594100b02500340c003501e00d0004c0e11020b20a8400041580c040d18486040c0d010440e5003094140d40001e1401251158180b0f04400000c0c0400140180e801800c19040441c03005100038605195082e81c2c540c0e200c842210845116408615024660400a0200b1a00d040400d603205031007280900984428403084001950600015948441c16015101d16007150f0300f4451035030b140d1649520240c000380d1802c0441d95420000010040c1010004200124002040c561100d00d01d050242000c00035600c2807040c642045460a140d50707000c21001c0c0c0c462003d007090020403000118003070041c404140e81c00e40002030310304082c0c0000707000038051480b007841c100034401c80740d030039822800c2c1d10780c0c1d04032107001c41c5140001152485c901500200c007914820070715a403980d95a0007801582103002c0c1c500d010302980c0c5030300d2003440340c401d1001 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 411623291 1250 411622041 411622103
    0xb0c0c0402090d030807090905041115120403031a060301080106060f0f0210020703051c0b130e1504030c081314040606210f0e030d1a01140715050103 66
    0x411402c081d00e03040450844030488000408126031400083e60460246c2482c1c0040d0a441904110702d1070145001030741b60f40e07000e1100780f003116098050fa01c2c008510301220030000f1000905142911280e030282d01500f45030002c080c00400392440c200c0c030380c2c032480041c50091030300e01c0002c00d98038a001005007001d2000000503042000c240ca085078020380005202144010000c401a52108642012680e50050409551084403000194443d403400d5800111240c94203c904d841c0851200443c4c00403101c2182032043c00b030f002010301d080400d090741100c6a015019042c00b160844059580743d0640d030040b402c15151001c0c0304001d0111114003510880700900a81e010810070741802800741565040417130040d5481034042204c510307150250805641e6580241040c01034641e0f072000385850790004485103d225140c0b0540c2111032452280c040c0e03450f1010f0319050340d12890090349200c1e6a2151a0640e0448548503c101c4e03480403e00c5210f00070b5000f00188000c615840c03400c0d545103650110 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 411624541 1250 411623291 411623299
    0x110a0c0e0c1612050d0603052d1b0d0c0e1e0118020a03110d020a030b09060a15020102040816080d03200c01060f090b13020c06061c0b010b0c0c 63
    0x1144442c0304501c6900c10700707400e8001800101c0b49680c514200d81a200c0c01c1d01a60500c0e0800c01d0000030840000782100c11100b10154640d00001e65601c2c01c56501da035035003400c13115407003601802d2444024a103286100500609142c20788000c68a59501c8254194010a10300d4448005c010a65801280c0445041c440034603400d055490101c001d280020b02c0038901c851070341d0000d6074030b50450095010345402c002a0031103948034a00050824000d40210481ca03000c241400c2c8a1001da182c1694600c0c400c500060240c1c0d103990500c0c01000440b20850700c0a020b5640c01c00005c2070740301c001c05c680d14880c42c502800d000040e0806d0140c2d41050042100309042c1810003013101c1c031464103a209001c901c3d00c0080080e440e41c0090440074094080359008a40660750403002180104040d040030b000b1000c1a40c00300407140440c00110100c3c0b04801e01a65560445000704441c2d00d8410940140300d1310301ca54905034000306032a1020000c20a0348000c0043c440000c034684402814400c01050071000c032 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 411625791 1250 411624541 411624547
    0x3050a0309060216050405070203160506010504061406030c16171e031b03060109172407050d09060f0e060f010503070608010e1b0304050c0913020d0210110a0c0e0c 72
    0x81c1034404d0081c000c852003252a05c000a0a03c0d100300107441003800c40000c408540400d41c14400e454104c20b006503801281003800201d640c00003a540700250380d07400780013985960340b0069900f0480d04915138041044211150007004102085144028001d103d1001a56007040300315004070700000ca0000846501c0034005c0000341c00840b000755515070a1034421365038995500f00100c948404503000030011050300190381c06510400240d8540e501e02c0340740c0228942c000300d640614001c404407101c40003c5c0040040b040e022120380c004a210b50b1007003502142c1c00c1d015a07070181c10703030340180f5001d10954400b031b082081240c0036440490040801741d01902006080c400001d069030014094482141420030203d080c242403110340c50988500c24405588900b031500e025034072004a500c0c414415032003440410315004840d400e5550301030307006041c54000a015401c2c0007454400c4100ca07020300c03c1e590b04039203040c3e005001804a4074030842c41e9041c0d00d814101161000d54001d001209441418 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 411627041 1250 411625791 411625813
    0x708040312171302010c020310020a1e0201090804060311090607030c060f02030105030a02120a2301110a12231e450307060e060702010504110f1903050a03090602 71
    0xf900e00326110394080ca020240340e0a0b50011a103003101c03409056108502c0040c0d11506150301000da200a020403011000c81c01d160030300c0403426a0403551000c0d0200c04200070800c420790103584004007610407040054102520702e400189282c000034001c8d00032520031000b06003004101c0c826405c800310045400c600b0f6504100200ea03590003078000080c050740050fa2220b00000c2d003040b0154035184d10074058004000700d000a107403095482045540302d9820311b0b98803800584c0c00800c0d188182001e650b01d0503041c80fa4808100506408007030b040401a084c5075608183e2074020b40f00b841124a103400c10000740040d0080214104000c0a5140c0c049152142c40c4400e902c02400342034801e0a9521441854010440c0c101c0103054910380480d548400076200341000819000018901c018a00f540e006a0b10001305034240c0d101101c004045400c4564100c3c200e01c2c03c0d00c0c901c100c04402410362000d1a421210050855005800c141da941d0b11400700002003680c8080840702a00345031010740b80b08400 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 411628291 1250 411627041 411627061
    0x60f0f061509060901050705010f09021f08151825050c07140a0b0a080f07230d02040503070b0432060d020705011a01030b010e03060f0705070804031217 67
    0x8911000c1d00c1600d00141c801c104c0d80c85841900c000d6601f110003003000407901e051600040c41d03c01012400b9001406041000d0740701446040c0310400039894003901e5030750724400b0541c02030030b01c4003041d4807400c201e0300040e09680128541c0c1c411440000000191030703112300c18071036201042101c542007040400001d1008080410725404407010b0700042115541340e07400007801203d09802c03c180c442d070007080811102e0341c0040000c1c05040c445c0c100c1c1d17001d921032030300444244c2c40c2550351009941a042641555401c0c11008001180c5440401418261a4400241842c40c190300002801c580410240030f81c008203101d6001550501750454030b1421a80c0c0d50203400001800c074140f04d40c2001c070740c480740c4c560590101d654641e03003d00200441c10302804c2c1c60708a0301464241600282ca030100c52420395000d020036243c0c4040060041107240e0f1214110110010002d010408002080c450b040000b0740d600c02034001385201d041c490701c0c60010440000d10030710280c4580d0881d010580c05102011403 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 411629541 1250 411628291 411628297
    0x110a080307080f030417180901050a03050d110c0a0b0d06151e020102071208100b03011a0903070305060f090c06070c030b060415090c02120c030a110708060f0f0615 72
    0x4078501c0c3d070758480c0e565040c903c1108903400c034226089240081c04003802100d4603013043e41e012007118020600c1e40c803002442807405c0d00f400010116401006881e82c1c1c075020b0000700040450030b42c210350668054402291040456074410300080d0750202c1c1c41c00190300640581800303005414140e4420b100901d60040c00305908501010f00e80042c010301c149813500c05e40440e4400e942100c1d030b11410307041c401c038020040c14046440d811030b02422a4003140040a40045070b04840202c0f840f038000e500d4641c00040c0c1940465200383e0f2522405800000080f028841c1174444c0e03048040017007c038038040001c02d08040703118012a1040f041000220001500d08242400307680d0031940348021f43d030316000854000c1810b1090500f01444140c0c0c0001c144980b508501101d12580d8281c5048403014080744c07040d0301a03094411000c2d0001d20209020318411100101c150340064200c6410725580d80c0d41900701001038a00700840701c0d4000421050042c401610340c0c210703805490a0800703901d008289440e80c0 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 411630791 1250 411629541 411629557
    0x1030b0d050d0f1112270a0b160c120519020109060807020f100b030c04090b0a0b240a0f051201060503090705030f07050406050612040b060616110a08030708 69
    0x11090003035400c3e0507885039020346500815442141c000610740c0c40c030454160040c074403010100c03034020303602a04185001c1c0c0090b01050081c25080f1424180b034014441604002e810361250602107803010080340342005c000d0010480d217600c3c08175509c4941803107418110490140001c083d801c3c1a0600142d034801c020500316421403030443c665480b821000c1341420740080410070a489600ac0f4a000000d981d0b100407102401103080319a0304080405002c02e441c401500503048500103000100001c490350032403c0d00d070340020520029101c5c0f07506440c418401480c205082030340c0c00b05a01c2c1e0110b8112403c0c02c6015001c1c20868249082c80707800c0e58442405000c0d5404008003c40410071061080042c5005400c0080039103a5158102d1800c0c0d0303680c0d038144501c902c114100300000850342060407c462451050f20910301007541e594403144c0404001400068001104200c4007041765287d8a0f40380c1d000340b240707690324000301400040080541c505c0d00901125082000490009890003046036242 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 411632041 1250 411630791 411630797
    0x9050726070305060a1706060108072a0309030c030308010806010f0305030304120207050303070b0f0f01060906080709050d0b100602160e040206040b040b04180b151e0f070201030b0d050d 82
    0xf503036030000070414004003607202c4080900c0500d2202d030018400728409100385004e0360355440315580c00400301e0700c0c0c41c07095003c4d030f90412a0824040008a0b10080003a07624080d003000104555a59520400c50386664000d48c0001c520000620445506004d840e00405000103916400c0341591226500c81c03001034130040c12203000d020900c0001d070023400000020000101540e03140e94560519043c000412507246114092600001e100c050101c04014107942c0c40740d8655100da13080c150180d54064029205c0010b00102480028480d40c6d050131080e8180c0c0715034130b01d160506054845000d00341d044d070004415500318100181d4401711644510080310240e01c0048a00c3d11035001007205445260480591924009004901a8501d500520803510b020030074007140d03000c20900324100d5448800060f40f0841002c980c02011007081e01030303e101c014060141201002041032214294000f0104800101001ca10b0764155030b01071054500081090b0b84002902d0f000b503841c6a10740e007040300c0200038 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 411633291 1250 411632041 411632051
    0x8060411040510080d1d0406060c030c1511040306052406090d05010908070c0b03060607061109030d030e0d09030f0b190f050f1303140d15090507260703 67
    0x5518000c3d9840002041d841080c0c400da0038035000010500e0355140032414000160a1101c0c0641c20144205012220a43e4034a00e0000142d5011280203c4804c400d4a0114494000c60f032401418403c0d05500c2000c00d0145944a2552030306400b40d90300203202030b80660070810700007809801070015444501088078016681c01c11a40042d074140100c88001c0c0c1150318129980d0100135142009040d200e010b1102448165621900850140701c22a21140c01500c18441c0034001002500702c020300501009c6241c1c100030b103000200e4a42101c103910003000a072149041641900103100c0050311000c10314024015030306640b54a03d2600c3c0f0700c4402042d0840179000260310b800c45440c4c06041c081c0000781880302040d04021400a420240d96008031040200c02042c1400c1c4c8101c1a03200417685901d4149821904181c007102c0d90f006503480f2440b050300c2e259028195280064210050b182d00000007402c0e08050200900c2d50b200086140d28035003505600880d4510444c801540c010030918000c60 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 411634541 1250 411633291 411633301
    0x320090c0c10090c24050a0806040e0f06160309020d0f0201020102040302090907030c05180a09081b010608010b030a0b01090504020f12100b0103020a0c0f052401030507080604110405 80
    0x850910b50307081000000e0700c1c00402004000111046008a030121300c64100050041c031101c8075802103203d60400032440812140c0d1031103008454041d48400010320004025034040c0c1c006090054202c0802d86c0c540200d403c10030401e40146030062064528070f4100001415a4042a42e44003000806070030b20324901e40c2441168400d4040b0b40c09158041c103040040d00f0011035050351554903020465169481410200341800c01d50319407800302c5070803618003c00d07480b66880d1100030203030b4400c25100c0400030000b0340e1521800600c495405000580000354092401d21200d08407007049228501c00c5e00030382d6000010800000156054504000740054103886034800510a0410b00f1031444e0010b09210200490144c089402036080d0f000440c1840083c05a6004404902c1054010401b04504600403c08280b100422070055841101220311214101e0114404a521034801c1120004400c00600800c070061025034010303c0e01100800950230a50350304070401c0740c000011409640c0d01e1002807 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 411635791 1250 411634541 411634543
    0x1407110304030305030919121407110402280e19120308071b0f02130e03040603090318080c130504120c05190602030a110702060d020a05070512040320090c0c 69
    0x160b0980c5481c0507e82c0c480a6501c0c0c013004211841d086030011a0445002002556102046401d0319501148200c3c2c04031440040000940006100e91020403480001d900d090103070001001c9507111030348400d0302259602c420403015000700c1c59a103201c410b00001c02c002140c3c24148105180e0b500d800c0032001c079501c3c0340742154420810b0b0b110200202030200e0f49024014107040000c0d016000341c40010014035010300c0d10064550014040c4103030b038020002000560b100e80c0c01105103603c01c2c41d180342c0d41141c000544240c141360307800411040d003281c00490003602c1c1120031604000074164040c01549030944802404407465400c401c01d11201d031159a04005080c0700400d8844d60401d040c0c00c0c003281c2406d101000390400c950444046240040d04000d051240054504043c0e0090090340b82c03500801560003e900552400004e2000078041203002404c1404100380c1d0350703c1d10010a4490b4914100308440c07081d000c0e2407130040c1d4445540315180c0e03111054010350200308484000d0b60388070050322203 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 411637041 1250 411635791 411635803
    0x17060703090f080313110108100e060f18010e01080a05030d0b13090506070e06070510020f070503030109050a051e071107080d020a060b0a0b04060e0307120614071103040303050309 79
    0x246500000410804200d80c104111440d06000355100043c1d00d820a00543d01c004050b207050a0000c01c0401c20003031100c001d41500e50207100a040c00c83340c20001d5010521040b4446180b41c00440f5900c018001143c0c6101c840b030041540c0ca0082058034004c1c0c846607124840c500011021548450f80d000046c0ca45142541464010140800c805211070030180c1e180c10007078803140000707107110412106925100d0240c070788444c4c101c00580840703040e019010000b94801080c1c640303505001e00a850100d1404d00107940280b80041003c110b920b048500fa4048420041050b1100310180120003030080c5100107540c2d110310607090000000c0d1340202010314000300355201004030f01c18112740d1902680d01145001101d031280000340905425441041b071080b005000310340c80c451050008000e9075108082412a481c0c020702038800240d101e0680c4480e1501d204015940242c40d0110320040d0780380f2881007548000c0344c0c40c28051700e83c0303002d480640381c0c812840060704000c004804500c4104042c028 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 411638291 1250 411637041 411637043
    0x1050d0209060702090c0c0d020718020c0705060403080304050d080411040509010b13140a0203310b010f210803070c050c211015050105180307061817060703090f 71
    0x217852083e181030a05410035900c00c5514660a0103640d049440e141d00001e11502518107142803a03a4600f407200302a8025048044224050303c1100300000d0a501c07094003e00c051401801c1c890740c0ea2429041c442d1a0a44c404141420884d441c000c00c8003290304040c1240003810704880c0440c040c0c4444900b5405005102255a88008043c50607400003035140d006030402920300b07440c5825030b610318001030100d0004964440c81da5640c00f1000c04c0500c85c6040c002101c11007202100d159048688502000342000d8104903498507807a0130030f1001d13001415100402110700d210030b4902e240c03560755900c203502015100070107100820074200e04001003800400c0c01d8000c040d00307280c0e000300e4003041c1c020700200d800800742c00ba00600820540b44070590260f81140c0e08100c0d05c042c1c101c2c0c5003100444056010450460f000c0000c3d00070081d05640501541000382500e50b180c481e40c0030034100d0980c0b8000c0c1d641c000c12000c081c0014004034658007040495120f81e05040006070303c03c49007015840c681407401c1c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 411639541 1250 411638291 411638299
    0x1d071e020a0230030307020f0102130e090312070512010909030903030f050403080c06041a010602060408090a0e0f0a1a09040807060b0310050709060f05091e030f0124030201050d0209060702 83
    0x1411018400000954030414140c2d00711150420b106408c00e08030300c24002d07c0d41082003608014014140c240c100d10740c21491420071646800d104051880500f001a0b41c00c0e4006040016030301c041c480811081409054202c400704500c00e11658050501440e0380700080901c20b8900c5500d00c460302900a9a0080d07401682c890754922451003800d88030542101d04032030344c0328a21060505501c505500031705031745058000308543e0700c031621031042a801c80c2406962040c0c820b1f502103151001d08070540d01030740c0e08400320045030070700c60010816500a1281000c4d000f004881c2244156181e19000d40c0103030704103441d01e07a83c0d0100d0030a6005081c403000f650f50180b05007519256002c9050740803a200e424a0340d2124486500c50b481101c49041848071500000d00902c0210f40d1032400040c1c3d02e03564090100c011480c0742070200031a08048078a00c0200260350340346401c043c15200380241c940d40b8240c3e08001c8030a107096900281031030285180132400c259001c43c1c02043c54031607404451300550020 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 411640791 1250 411639541 411639619
    0x140118030201061e0b0403080d110c06071106100e09010209040501060903060b0d0c03080a023c0304050102061306090b2404051501030b01091d071e020a02 68
    0x20030080d019211070300c1480380071038034040b2400d15880c00300e03420010b031520001c54038a4140356072034400c05070b041286601d10742c903912800403148000740402000b02240784006844c85203080107000c0c1c881990009902030541000041001c000e031503c50080c2079600b10b000000c0c060700c0314500719009014214055401528010012868503004000d000c100c03031140b1424400505480d0512414211039400146105100703001440090658400f404050020340f0485030444210f10148050001007100e03201c69050155101a801e0003100100b0940e0403103900443c81c0c549032000003591540e005246a00340c0f0104503008040010fa6001115a150070468030b11701800c00455001907040d403005144241d40c8520b80c8044241030900800c0d204600d031a8400e0101c01d9000c0055015158405019040100b10900803e51640c41c0e080043d40c5848000500f54901d001b44003d0824030518200050300e0b8091840ca0300c00c40e0340000d50090050381039481c50788034590312040302d401003401d14095940c0e550038 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 411642041 1250 411640791 411640793
    0x1d03010204090b031002130506090402070b01030804090f0603050c01230301060503190905060619030816020108100e010909060609050a0c0e0a0608150f06070309030614090307140118 80
    0xc0d4000c2142c3c0103003141564080314048200780d04034032a01041c403e4410300d0600402503032505001030100c00e0302c05400036143c0042c0b0781d50f050b0504400d030000c071040d2801150a200003292840b44140041d04291704004941c12342c0c84040c2c0e10341c8441001070401c8000c104c40c0c100300d0100d51100000d80364645040d901c2e035840d20006080e81d0800c40341ca01e40010001043c01442c1a58040e80241d0b0f504000a05141d8540c001444a00f06441d102a25424117010300000003031210401401e180c01d0114110f0b20400b0a8070006182e0b00010701400c80c011400c0034280710010340400d01a0450741c5034940018502031900d0001d0241ca00c0e5804a0a070503d01030411001c00e002d90414500074091350303200c400d401025410042c04150f80e0041000042c90350340016200218502441480400108010150900b1000182c2d444d44100c000311300041c15028104100400c500030109800106103850015240111a00da9640103500d0040e1507810030030b001c8a00564298003e030200343d100c030002002d440c85 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 411643291 1250 411642041 411642059
    0xe070f0302091303081305031c0209120d081f0e07020a02150f07081303050313030b010918110f030f15131109040809090a0516020c101d03010204 64
    0x218030099010302203880000d01c042100382076a41c42a549503c401016840780d4680742440490350b80c0c100c9440c8010031001b04012902c40c854141403844000143e41d445011060000c00740030400c0400540e03004e200c64a142d1034000d034020f903000c10b000411071098505034910015000281d801064010900800e2018a660200300625480d000f40c0305e5070000114080302c1d2005103e461602c040300c1c41c1c2400b400d40000d807010014400400603108141d0082d48a494a500359030101c1c50a411500b408802001004503249120b40107100c84042000804055400700c0d034030070241040108011220030301e135025aa05c03035402011720080070781101c1c10210120f80b00307560f841680700f00e8101e0041c6a0005450b00000403c1c034031100b54000c00903030b84c084880f801d009a52001800c1250880710520090200341c8034050024410240d140b804030b6181841c814040d11445421030403001c5410007100e9204685406442c80e241c12100c0c80c02502d0454980e049485100520450701c1c1d155000180024901c04 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 411644541 1250 411643291 411643319
    0x120306051e28061116120c0e09060a0902040e150a0e011503030305090f121206060711060c070b03040b0106080f0f040b131a0f0c12010e06040e07 64
    0x10003956807800145185240350200e600c001d180d0340c900b038101c41c81802400e1054400b02d8240f03104804507256289030f03004410520741c1c1a0450060490b43d41c0c9008240030302c405004004202800ba070002900703140344103035240c0d20000c1140031040e40352a03040086449a5000e811140104020341d031040c0085448100790400554201c0b849904103540d86400c0038040c4109000c5100041000501c54519603041e0041c09002303100262a0040310000d060b03002043c0003035150500380341a026aa107c5001c11031a40700c0d0040c0016005840622001000482d04400b0950001e81210b055803a0304203104a43e2a084041c0c1000c0381a99001c0107010400806d03003541810f9624030b4445a28656900c00d4404d030000b030481b0810a08203210700418041101008001d80003a011302d43c4608070301c000e4a07644220043c12686110017a4040108140741092400058101e04a10700b0f11b460541714103001780c038400041c00b07580400300c610f001241a0781d440e5406a00b034582c000c800c0d1158255102c1181c02104 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 411645791 1250 411644541 411644599
    0x110f0307020d2c10020c090c03070801090204050904020d08161b05040209060a030f0b060412030e010e01020d050f1308060103030e03060f24130e011d0a12030605 71
    0x500703c4043c00c44950601d021030307080411028101c00021001c60f0800c1441d4243c00000410340c0501445101192a080025803041000c40700c12a40ca091408009101c00c105034050380344184180700502190fa500c0440700d80003a0100c40c4132204010506164101d403282c4404c01d0480307091a00d8000030803000d1880e02042c1013048140100d8140c0da101030005078829004072607072202080080d00d464070301951003400441401c15002a91079036090110310648d0040e0440c4060343c0144601d02c04140e448007840d100340200703291840300502d2460010b0740d1010416601010b0103008605001551241c44c00e4908640741d0202e40516559245502c41c0c0794507082c001500060602c0040b090709040020780c060003408580c0c040103c0b9540c0d59603d404080300341031080d2441202c1103428600d5901c001381c01e5640304000e24001803e03290010801e08458201e988c00341c0c3da032050300b00c5c03120011009c81c00000031038001b00b001c42d086400d000104c0c020011074001c2640184851180c80b41c0c211401380c120100 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 411647041 1250 411645791 411645797
    0x30a090501020f03070201050319110406030f05061036030303021b030301030f0b04050a14010f0b0307150311190507030e01180302130e10140705030405070504110f0307020d 76
    0x140903c030604584a00c2100300280c0804c4c002c1000c10814500e40c040a402030010400000310115030b0b00140b00154810390060001980782c0d5080c80d101c1020740b0400d03800a80444181200d41002c1c90f0140144e4100f0f502e031040e5110366015035100003020401204d00c0c40c4402c43c1e0880c81c507160304d400350007504a9802d910222071191840703489488000100c80c140c0390403d0000e01c121403aa0b684000880f0300600c11201405000144000912519988040000c404001081300401e844c100012070789120742d01c074441d9110040070010300150007003102c0e8401591078081900b107403114100c10a0310440015080c4801040d20780c1e61030a038004064452180310790795080c0c0004014004450b03c5254100e0305020f075250781410001131405c09041c1d8146040c0d00c40100e228600f0001041c18605802c28900790692905e002d500c1010142c111598803a0082c03e200c0d0440c107081e10b81c4c40c0c0d6040f06010311070040d61b5510039581c481621905556070860003040c080d55901e40104025260407042410f5004 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 411648291 1250 411647041 411647053
    0x50103110d0e0d17070207030620070f1115090d1a090304080c01090506160611070b010503060603030720011e03020a020607110a020f040e07030f030e1c11030f030a09050102 76
    0x41000c0c0f4401c03400f481246c0d006018003829500d940d00202590401001d5070f032800c040003548450000301404007a0b000f0003200000c1d600608205010517190103c0380d10811510100c41c00154103002528141d10090b500620030100514107915040c03140082602c00141d100c04100c03a900000000380141e03a10303170040e19107100209005491010440c0903003030b1300c9241844a810780c8044101502d6500f03001c0d00d0045050140d00c4074000050740000d45c2690403074002c4005104d541000c002c819000071003034004500d0300d095a00c8646021540d0010001340c1c0c66001409e8501ea841205112003450280d140c036805000100c002400032f45c4110280405070040a0002d00318a00584c96840b40901d4174000d080d5941d40d5608000e0210301c00c0c1c030101d42c8290740d208103546640c0c04001000185101d401c604050310031130700f0040d1a240301d02545130310880070b02c04400d10400750399904d40112640318840100991950340081c0c10040e000400c00c4940c40041100309400342c3c03150030241169820703000e84107 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 411649541 1250 411648291 411648317
    0xf020f250b01091505060a05090405010b03011220090703020702040b030607080c0f1306080403090e0408090d0f0f0b010f08070815070212070b070305091501050103110d0e0d 76
    0x310500844000c0c1c85110900c0041026081d2a00f10340360011540c01c0007030209480d0400105580c00c50700300d0a0014401140d0313440941000d10411340540454106079055614100383d0561010810f540205801c1c600440c0c55130f0011f691040c010300d0301004114105903e0140c00081c0290002c0405038861030811100404601b4041a40c030b02500c45a5100f54a81c1c0e01d00c1441241c40d0b100c1c1c0a40d0444440410841c000305060303103034030320142582d90340e000b06034103003403e000789010f070680c00c00c084186041090000242548044a50821041d03400140520560401707000c2040c0024020740511000c0e0542800c0045400050307050b01e0a1494482020b601d0740f01031540c401013409589400d512520450440181500c54182d0006492045580500a1001000c0f040e001f41400b12114500c12090108103a01401010381c002e04079030042c2001841020b443d611500103116060602d82d403a2580010b09041004a81c120064041d00b80000b4030001da0b6a41c0d2860b031102c00030700046403114261 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 411650791 1250 411649541 411649597
    0x70b0601050306011707270602160b090d0c120609140d08061509030d0201020a0305060f09151903110f0a080604080c2d070609180b040f020f 62
    0x280106810303075414885c01310100003c2c03005c04001d0300400c140411000300c8003c541d03d48103850001c8080a6034400c805160200107490441454101890b1000000d018800c940b51681070329a81c0000700c500345002c4121b07003049030400351140c1100305011240c003d0041404035a81016185a1144d4424056180031451031034440203441c10031400a111400814540c1c9450208980d611500024881c030307240105002a24040e102c11404015035008115400d00c00e82502c603407648400240c54026800700c032940041c00002c40140191a588030404e040c66407a1580d0801441300c42070300c00c400d40195124200704064100c41d454492061000c00c840300e02a007840381504085584181c010205d54172140e8404226030003880c0900c0b114824541402c03040128071f01001900c0c1703030078a18941a41d01500c5007604099054000b4014400705030320401c585d42c2d000e8414400d020b00c1d0100050391a4189000801803d101c0340c0c00500d00d0700105a11403019441002401c0640b400382c140600307900300c0361b900 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 411652041 1250 411650791 411650797
    0x361203120209130f1b0f08010e0c2512020a0b0a02160b0403111e060a0e12070302031603080117010c09150e031608011401080c280902070b060105 64
    0x2503900640b900e40c071409040e0964001e81c0c0d07121035045001c210b05d00120641d08056603403090040000e08034640b44500346800000c0280075001501030030f170301450401031080d00c0c0c3c0308552602c0c0d104102c1c2d044014400ac15225a035008560002404c0030b14501001d0080d03864140c0703002624203002c90b101140e4601e03290304c200e0304022010324051b00303411203a448001c0d80c03080047c81607091140c020b0395500c040c40d003482030800848500610078203981448046ca071a080b4000c0402015070b141c104d01e01105600020f80110130185503c2c1160740c2c01d02407400300e056000c0d020469884104d018500d10030550401901810795083c54045469281d0668204c2c4c2601d11a80c1030b0808550800400d100c0b42000028400d45183d04d424141d29028080c0082450101c035081d541d808102c00040900c80c0803020b00540000703410000d000b14072941080c0100ba216141603a4a501c204510b070310b400c0440345403001e103100b504040d80142c1c90b515541d07103408003e5403100c10100c543c0d80020000034115030055080d = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 411653291 1250 411652041 411652057
    0xc030501060f09180201140409020d020d06091e0c050d110c060c18090604060503150f06040207051b28080d08070e01030905031917163612031202 64
    0x110b41c103000d040c5d03001901d05207184181c0181030b100401c00420038002c58001800e40c040300c09030050392011190f134040c013200c4842c0c100d60340780c50074944015550380c192850710707401000c40c542c00a54000801801c0d40d41344075181c50260b0150416958a844e0094400a0f241450655041e82d10660341e8405201d42441800340380707034030340000b0050145030f401c12118040d4040d50103840064903d80742e80c000f92501410b00c0760209040070580800003004803400d4540c0e0480020368065007002e00396514a0b88440310314420723038060004030110400c10750b1a4159202c444a2020103140c00365002100091101c000e4040c0801910441c000313507002900c6250014030480c8580e0741c5042d440010310045000d084621015900c61005100d0200c0c0c014a0156101e107803c05501c0786030085103482d18004040c0c0c0000e011228090303104180d2444683c0005055801449951072031100056004e842c1038641d094000504502d40c2c0c04601160304002c0b01105914203000380c4038034074002a0451050140d03c10120 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 411654541 1250 411653291 411653321
    0x1314060312040803071401110c01020307020706210b06070b0906040b130b07110c0a06030b0a051c080708040e070c02041d071a09040f02031f030215030703090c030501060f09 76
    0x10484003c9044000401503681821b00045910b2612520000117a00915a5160207940c00030034002d84030340401c880002002030b4201898001150203c08100b52841400b207d02c442d1208080d001c01d564150407180711300d901c20b06d00c01d828200750110303a50351201101e0803908c0a6400c0d01251b000c03544000b12820075503110340c01414035984c40d4ac045402560000300c81c03440b4890008902410b54540019070b02400361a80c0005845181508200901c02c05902c8203000d4900950440c0c81c0411083c2000c88840d0014841079407101207180465882c03081e984002003c0c001b0303101344804150700070602d64031036008582c240f216110900300703000c0407400c207680021030b40d215440402940880384044001030385076880303907418801c560b4045019100c5440700a07005950020800100ca604c2654680106070b04480c002401811030340440c1c4509010b0101c24407050000c800107040700e220f5006021060b030b2000d1003009003035803440c25501030507290080c0c2204180321880407070403a405206540300003134102 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 411655791 1250 411654541 411654547
    0x21011090922110d0c140f04060e1b040810050f09010c08060139030f050301120303050c0d09030c03031a060d11040b0a020c03010b04090f111314060312040803 70
    0x198680c2e200ea003c1d202143d400c201c42c0c0701120041070200c80c000c40144071075141c00c00070010500c01c11604c0d0a8504031980705524105090041e5007141c1003e9034020700c00e40404404200b614040e040785d000d182e014440e644601030071528085005e40090b40904c000b200e0001143e101c90040900f40c81d5942042400074100380f00007020f0790720919614006405980007030117241c803000c10841c0b80b108000310703004500003c25654820944c3c0461507908201241c5405411035042039501d4900e81c0c54100060109078a9a010034050003404c07040b1900d9103004a0100710002651138094540380d90319905401207480c02003407010090144211030800c3c030700248040d10b070169001e80c1c5401088025100840064140000315409081c0002400744a256030010600030510400305070a480d00341030807a0007982424080340c0041d1402e5810000c079a48814050680c0802201091050100400340d201c500c0c10300805a54a02c10840d041c1d000d51400e90a9400100388458010018480c92044c010140d00030 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 411657041 1250 411655791 411655793
    0x30c0c0b060f190305070f050301090302150402040f0f15090b210106030c0e0f0916050f0301140711011104060c020d03030603240b0103110f0a021011090922 69
    0x519002101002d00405466500260200310300c10141550011102c0d9440f4281c14400078036240d00075070040908a00900000c0c02c0f69070001d4885a03000550300d007080e4901d01160841d9a00e41103c0640d584c50241044208050300b190800361118048100803604400b6000c6080c20f414000c1c0c07140e4840190203680740540865000345d0070502002c00940700c0d540c440022001454120f40301000b414680c46140090a1a000800c40300d1000b41c511001c0394800c0e14243c8010000000041c100e990807a2038030201c4483c20042805410019850500072103242e081000d070179000441c01d00d40c21103007402000200400121106248514007481c0b01040c00c201c01c0350300520b4014204244244179150105100c0d54039603a0040c04402e1244540d0b014100300341c900e01a441c070b48500c508a0409113818071145000004801d0144590b95840540c20000100d001500d4001c102860140000320810000c0e545640701403082c0ea00705680b014030070030401c408511441c034241609508001d54030290031040341b032 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 411658291 1250 411657041 411657049
    0x9020307120809100f020f0a02010f0e0103021c0501060f1701090b03031204030e0108061905012304150f09060509040203150d050109121106010308031b0a02030a030c0c0b06 76
    0x19402046800c0b0b00200402030480d110380f0045204400ca0b82c940b0b000000450401a080004e20b40314603000e0344c021450f0b000943c0e40900b0b144800795081c203080d140846510300480180c46142502903002d6083c1241c540d046074144e0000c0d040303c1640c7e80759150203515031411034400651130405580034104000610003c0c4803644132900300c420007800c0300d00d41110240d1700d0143e10b200700c03020b40c08a4a05021071031340b560040c5050f588002c0440d00f000d80544074a900b000b1207003440c0100c904114020a2000e4410307580c101482d2081003c840640e125551140c1840c40b0f009007102000000b203404c4c441c6400d66024a81b010b003621465120b460411000c0310521000390401010441c0d01d42d1b0480340005241c40749103001380498010750001c1143d1b440b90402407180e014090a4074100010880300c9603c00c040800d5081c10b6a81c02800c482c0e1701d032194190b10002024642c0444541080087c40c44038007600000140131158445d1400d20044030148000c0c0e0710a8250b0101510b0002c001c0c00080329454 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 411659541 1250 411658291 411658319
    0x20304120f090b2505070803040e06040501050102100b0a1a0301030c090b010c11180a09060506060c031b0c15040801050c130303050904090c090902041a0d12020c0d06140a09020307 79
    0x90041d841c100c5211076174442c0d0f45400040c0d0f0102c441a00f00240a001403500b603031890364002402d48080c0f2965140000003503456242180c083c045035580e00c2140001d82c0c4003c02d41c03008160140c40307201803850f1420000d1065000b8032003160307a1660032400059000343d6000c0c180030300341c050f150b014080f0969240c40102140241c06694068990300040c0d0304140d2080c1c1c128040e081c001d000081e94a0540740c104102c1c0c50190240c0c0c403450040c06031406240c00042110080d0380a40f1980c03003131a610042c0d641c90305400b6050540d101c00d41400424007484000c0140085400610080c412919251202841d520500d00c0004003030007400070503c0807a0148004014040b40540700007500006074490b105655001d400c00e815480d01c030300c00da009500e854015944ca190601000340741d81e032000d100050f4003102e15071000301485118595548024024007800c0f55103080038216103c0c1e04081e04d0804c00038103000f400035101d00641e0010840012251085242d030f01d07030140c02400407500f03140308015021 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 411660791 1250 411659541 411659587
    0x406021c080117100f0b1002070b0a050903100c030b011b0506010303030e0c0d0302100c09050a0e070504150302040501030e0f0706080a2a030605010815060706090501020304120f090b 80
    0x44503429101044d051107102d590444482070000243e94140380041141291510410b44e08561140c8014440c5801c0d400c221044060b550608640c1c60000038086404d01000303a01003015980b1300f03060600e60a402d50401d079a124001d030388602401480d01c0b02102507074008000942164040300042c4002070081c0d10949141c2c007244100c40740c0c003100324001011560b09020490060b08410080c050784e035143c1c01030300401940340c103040720140d00f06004500411214841d640001c1c5504021592040c040d0741100d0140c04801c24817038142500240c003a000c2d601921900d40024601145130b42c41e403102044c01c00c20015a01d0280c0207117031030980111540da901804012100d80d842a000c4108014071100401700101a82c1d02400c0c2d81c44150054200c2d0780590150741880080c1007048103102e40c9410780c01c034040d02115402d0329500380d810a0350060004003c024040c2d03100000b44403d216001030810610170181d501c1855045070184110f550b4a0716100e6811000d205202c09144102c48803c02d41d070070 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 411662041 1250 411660791 411660793
    0x5150d05060a05030d020d0915052a06041415010b1602011e0315061e03020f0915120108160302040e10140f06040603030f1b0204050109020406021c080117 68
    0x483d4880340001c2c2040c80c4414004050781c00401d43c0215150080442c200030000e00e06940751500401102400b00e10500f002805111040d070460b0380c9510f01c000b0458140c101ca442101c009241034070300ba450000080c8070503c414460419007242c44454010014140c0d803945040d1b44c104101584903041420b8164802c83c184448620b0b0300400303d508501186110521b80d03400324051000e03451070a80c0200c990807030b908001100d5907031115090041c1d480c0329041107900c0d006030b84400440e6aa0214015000380d290f11001030815416561680c101800e900c5080440c00942a40c0e01c0d44801d5039071000740c5805500c0c07010300c1400c0026107031940c000c1910920319030030703030340343c0c940140c0d41d807040310880213040100f06e90a000f88251030b080703850000d62020b805d4608020703041c159100600304601c084030b4141003010000c1c4118012186d81c807840104c90b4060418001c55031a101c2ca10060b402900468005100b02c5c000c01c0c80a500c02d115021090080343c1701e0281607424100006e81d5090110100c10403 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 411663291 1250 411662041 411662059
    0xa0b0301020d1a03070503030f030c0405090709080f0a02010e100504080109050307140309060d0b0409150203071403040816022107030c06051222020d050309040605150d0506 76
    0x4651820300081010b0404580700040d416400210781142010048041c0e00030341c44002c050080fa2000800c680c260303480103182c16100e9958201c1c01039148140c1e00200d40100c1040e0a0144581d00000e02000ba9112001941d104030300d9032696a541c0c0c18002e101a000880044001d01d2a040001d5401404100c40c030309a450329888034011401d503188004119201c0d031001174510284070b249a526140e209500001d180703894200303800035a05000705c61081c2c0405690301900109941c031580881718a03079118040c070006800006100c00203400841c1c00602080b4424a141c2c1d09032002070440e171280c1d92007864a8185528440300e003400100c240022600b0090101d01c45207025007401ba954036401d8034600400c001c40c00d41ca8802c110a007103a000b03405100d42030244491404403903d00c07683c40000c4100300070300c803103480c4030314148509007800c0030b500451140110030a2180220080002d504142c4041c0f104c1d598400901c02040060b000d10702c18501c05010341c0d06900220b802003a0080c5005100200d = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 411664541 1250 411663291 411663311
    0x4020a0219150b01020a050d050d14100e070203130e0907030b0f0103151e0c0233010f03020907030f0204030803191a0a05090a110c030a02010605040b01170a 69
    0x1c4040d00701a82036401441840452014000c18081c0440c244004c0c4042d05900c022030796016500e00c032101e102410305c980800c0715043c5140503485440d00d440100d1000743c050401e10769046a03844180900302d1110108800104114000812980c17482c101e10854803080e460440c035814107450181184d44240641d603000404666004440d82c0550032144031000305501d50319204da00410b9400444203581d0812035048a103400004010300202a00e820104841607038040407400c10030900d8528150b9a10700e040030000c050040f2000a41d82e5014125131a982d0700c940c613000c003000301c0d4400250720040c20000aa200c1d4865081341d00c4540c0004400350505441e03584a2959401c121155000c0814050030080c030400280540e200c501c0c50401101c0900c005c0784041892900103004450241d40ca1001141c14410745502080c076a1040c0e4042e5508e8030f402101c1c807034981d0b0103111158019130800002290394546482011560241611914403416122111444104008041503552551010121 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 411665791 1250 411664541 411664573
    0x9061d07051003152705010f0501050d0c020c03030c0c12030c03041a090a060807030b040608070504020901051201090c11074b0614160215270a0608070e04020a02 71
    0x554001282003e4005c800301102c6908444050744003d0340000000000c01c10340c0d0f0488100c0781200801040441c07903006070344050307240c50201d0f1880c90f05031100085401841c1400300d04c858240c041100d4020100d01c3d034030740716541c84c010710a102c482078000b0002040030501500088680e451400c515500300070142d00050000949a8843e0001c07030a44810030102c0c650521808103040340445003000f4250030101c9139565110f40d40038140c01282d001980c0f0a080e0f0081060720508a0142801d489a40c0c540040d0809800c0c0580b84d00d0114a01d0402e80405081c0860b00400f035079051009d4170b01704042e685045040740005640312800b03001c042144543c484902e9a0400c04218040c5803140d414a0100000c10000c1490704014201070b040c000410341c0c9240d000070102e40c0d50100c45000c00e6058a04082d540d921480070340c0e84c0062000840300e01c08c40340d0f001e20705003070300c40407a900030005654038400ea661580c100c03002e4000070390581c001d480d10314065024005d600141c1c81142d401c0b441c100d01c10 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 411667041 1250 411665791 411665819
    0xb0f06150a0206100819060b04060f08100c0512070c080c0a0309170304030b06060d14011d0604020c0d0c050715120c0509180a0f09061d0705100315 65
    0x1581c0103030444000c0100b070310754402c0c010004002034001408840070a880a4200d0004840c004103030310b844031624102503445820801c094924900680c0e001961b4410030b958a0200c3d2580c400f0140c01c104510340c01e1030240d41035820a521000310355200340e4a441088603400a07400040301c45a005001c00c105c1001d08101c4941c00c00c0c4280c0b075681e00c09082068040710103024001012071903000b00010310000d00800340241c0c000c4425076500380c0300c1c1d00c2c3d5440500075010400b0415064040f02000041203154851005ea4000003609401d1040e00d4020500040c3c2c85000701495095110100000c400d510820300e03107100134000d4040e152501c0e1a254100c900100310b104240000b10000c04075446000944a0b4000900250900625018030390010482c000144070b403d800480042f80040c0580b4015040b200444002d42420440903540f464082c0061580140c040507101d882c0d400507000709000119002642e500901442c02ea501c1c1c0e071400c41c0508218038000c03441044280001400100300e03208 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 411668291 1250 411667041 411667057
    0xb301e0607020c03030412060e0a0f0b010603150f05010c170309010e0601120317090a0614041a07020304121e08120a051005040b06120f160305040b0f0615 68
    0x9010035081c21030009151007480601070744a034204000800001006000041000364001c0b0007142282c0c0c1003403040d05000c55110040c1041100c010342000b003042d02c10710507060b518152020030032001040114600743c102c0740a0540e002ea80301405110560141482c401c0562040883e0020719010032060910340e00700342e0b4010a00e030f44844050300d140c1d00034095980980b0040d02009070100064400400300381041030025180080c00c80440c0881000344910003040ba000347c0b043c008028410207040c01510203d0301230300c0460420951403900781c10303414000e0041d04594015824a41040643d05d644d0b41e603800101c511407060030302242c070403001d00c8520a0041c090700c00d45845444c5030741400140c650041404090515240400c06040c8213403501da001c0d01c806840000ea800d8100c00402d5440c0306010307025480d26100020401c05418021280c3c0c820502c1d42040c075020b80e1050415000e4883c1914014800107000300040d42e0b131070b5003400c150ba200500030803030b120140800610591359400108 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 411669541 1250 411668291 411668293
    0x3081608070f061d060c04051c0b01031506090b090c1b07090902010305180a030e04020f1b070b070c0e0c0405150918150103050c13060201060503010b301e 68
    0x140307004d641100036030700020240d021805410140380c601e001c00c04603c982d00501d4894480501070202c0c40e1860808a8170803684141501684e58690400c040200780807900c1401d8107040c880045481a064020202d481d0700207482841207441d50a480c25003600500303101801e403440096100001c0c401000682e00a104644000400000f0743c000142582d000510f503490414213084c8402c503000700055524441e60b05498802c030240b4107500040c0182c03180c1030a01020311004581400101e80c0788030420110350709139045074081aa40ea003c070405008064025010300c2807050100000784017401c4681d40b012403400580c4c40c00743c40d40002002c07103c0900400203e402c01140065840c140640c100080500440300b0140c9444c000084143c00381c440030250341056100c4012440c2c55038010306031a424100802100d42d142d40301d0b40000c4c003c1c03403207114840c443c0d82403134104185c07400c1c000c055894a03149540610340c00a840442c0324405500c0c5960400341d40302e2120380d41c01045680382d4811040c41000 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 411670791 1250 411669541 411669551
    0x60f1e2109060f09030f250b0f09011a06030c0903030f0a09080a0b0703020d09051b0102100b010509060c0705060310031109090c0d020301060f081606030603081608070f06 75
    0x841c0a601e000401400030300d41c28440d1040c0101440008183e9407a9450b0a5002da078888109072030742620510004101c6171203078102c01800c00c1003198210f0380c0c0724040003442c04000c0d540e2a003401d4280c1d4404110844003640c3c0101903038450170001c005603031000340710201c0c0b4981100140428a158000c2c405e80783c1e11035010800880c02940040c030800142000c0b4010003040900f84c4880440383c1014041e0814550f000a041000080c44e4119500b2a5048815610b010001c802c94591402d82e111015005005415400d20010240e102e0001a6501030b950681421070350807d1013241e902c10340301a80c0602c01c1e005c0c0025903a8610300207510511849103000b00540c65817416460041c919802c0d103101d44070200c10002c880c080060094407d80007198411170020241c000b280c01008290000682c0f1001d440010034100701c00601d14040c40d0070703440160801039446a0032011070711940001403010038104036508100340003040300980c95000780d55142c9072404598445040040000003113550f60f4a42d = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 411672041 1250 411670791 411670801
    0x302010c0207230907030b1e0102010c090807051504090501260105060337060c09061d09100b030a0b0307080111030a02070c030f060911060f1e21 64
    0x60007a00300400a81e55000d07051000c9095a0381c1c08030300490b0a13402801c5803400111168070a81000c0c100b040003400d40c0410007000442c01c0194009840e4950141d8200020340104900ca00030340401c40b20b01c0005844894101410400c01c81101e0640c124540c2051001107155010391041d207000b800604111003d000e034000c0d80d110541c3c1402490045030345020108003003500d0208042104500282400c0c2070070501c0d41d2065080329203500c54441001c1401c03461002c10445900403210710003542c482d0703000f5650b06c0d14116140c2454030400700145d0f001e043c08110a0400e03124154105500040a0b59a503882d65056000c60b0012608101c0c0346803178501000250400b800144082e000c171b203000303020b0b402c2d00d0704904009202c09001c007102503500042102c18005415515809154021760914030a0400d050440140078403a034103644d1a483c00c0c0c3c0e110b800d8a0548100c404460100760250304020300b82001071003800d1500483c1c8540c0701c04100780014440b111421001074949250f03041030a0402c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 411673291 1250 411672041 411672043
    0xd0801060806090c03060d080c01020a031a0f031b0609100f1101020a020304030f080c0627061312020114130501050903030603190c050a0308120601020604020a0501030e03070803040302010c02 84
    0x8098001801030440b0818403000c400000101d83c0c6c05001524141d49207030030b500d480b5402d84034034900f80249500c046a0198503e0b030681102c2d0074107000380310050160303002c4c034200019424401e0351070342d043e404000700350700c1d03010200070607985090000c0500d800c081c141d0001c00d83d2482c6220842000596042500d0091508218100350084030740e402141890069a03000e0760342e10a501016091083c2c03143c004c0f0801c0190002c643c80001c00c0010783e610390601140040401141c01140342420901a078100711140e400501d1a02c900c409601c821001040c035124148603110783c1040d5401c40d52100404441510990032843c001c4c0442c82541e417040304581801802c4500c0500001c44942007001441541d0341e0016005044c10329194003e041d040311480c0c065401ea8113540460303009444d080f000418070030307000701070712400d1510340140745183c1d5080012a2540000c41c0c0003903001d00e410380705100a500c294869803042c11404110b920303092850311900e119803c101c034100c0c0180c0d181c6500e170140d03e82c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 411674541 1250 411673291 411673307
    0xf19090605061e010207060c0213020f03010f080d05030f040609061a120c0a05040c110601030303021c02031b0c0c0301020c0307060b030607231c0f0513050c210d080106 74
    0x1001e668400000d5040e080000d41b181c602e4070520381008140400ca400f0340d50340c5890001043c0790030000310342d1400d0311141c100a03500b003481a8040c90100d0703078000030b60390b201058100c15011965240707880e50742c9019042c0c6910002800903a80c50769682c00103070000320b41c0c1c440c4010441c80181040000300762102040064400309401d40300c590800011b91490341c0351010900d0a40310122408140a81005400c840581800702403460300e01c9041300010505801d0f84c01050541c05200c01c840c01007000141c9001640301c151402040420f541d0003098040440300302801c0341411060030390702014200400603003640c000600c0325409401c001100070400450384101c0349034407403c1e00600650324000c040903000f0f094038030001e411200400c074000c4900868100700c42c14100080042c100030780c01d510382c1c0c0740240325606025050501e0314000c1201c6078680120300a00da98400000d0804003271403000e002c5a10007024000502e4440d00f540318886040612007401b04180503031f1420260340c50a100201050 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 411675791 1250 411674541 411674569
    0x91e01050a050d0b060315010611070b1606110f040f050a05030d020d0318021008040b07050301052803060e1f4109070f09140f1909060506 61
    0x441c101400304102e0319412000700ca000c0d081541d25410759038040200c0c2c18030020016018080305030200102d01260000e040b40305007841a8120350500340c680d4018940e61256440a45440c501803440d0700000d8003541004002003040e000c454100310281009400039040b07600029000c45035484203012600f443c1d00c98800030f1000318000d100e000005000a5141d910040f44001015280c8034011060300d0091001d40017039502800e201e41a41c01404010301441090f241103500d002c0c42070220ba0180e1042d4180c034184e540c02040d089124800002c440040003120071905c0500800c42000008540d8031312601c1400104035000d0268403034420040d08060111f15030803071104e85400601d0030102036011030134141003c9824020624000504605a0102c0e0071108840c02000c1710208401d0600105224049424410802d08001d45840c2e01c2c2c401d0740c0c0f2080d012854403c620700000d002c40c01c00e100e02c5400ca012a081c1c410b104450039980400d44415000c2030318100d0b1600e080c0051400d1040d2024550 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 411677041 1250 411675791 411675799
    0xc0c0a050f030a030f1b0c050106030209010e09010e0a030e010f1b030509090a021303021e03010c0e01110303011802090d1a0f1f0b0f0c01050a09050708060115030c0e091e0105 77
    0x543c4506e90f540080481880c48404000e000c68070744003004000d50003000610780081800d4403560b954840c03040c00d02000c4a1001c429400d208409402100c00504240328640c151a60480700c800c150044424a030700b0b100708000c00c00c51f00b502a12f1031680108000405001c2d544172566a600e031002d1000d90000500030b6503006104001d1855400010b02001054070340c111843e10046c030350460f0684034100c00e020f9070f99240d460301c00b444041c00d40180710401d5840c4203032210107032000700c2d200b1140c6a00003403013020952100480aa40c4c0b801c8142c7c000d011a40004040e00d90f030106e00c0c2c4030401e00c82c0960410000c0102e403a401d20640d86014881c107580288500305100404a82080c140e4456510b8071a680200c000405e505000440c480180c030680384903440200071600c0c0800c0300101401d0f018606603968015082c011800382004151a03040e00c141554600040015010840c01000400404000c01482004555040e0342e030040641c081c195422003a03241810603c100c0c001e130710701070307020303500c1 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 411678291 1250 411677041 411677051
    0x20a08070807090f0b03060a0b130b01080a02090a0e010e2a120406060b0d1b020a08271003050a0e070810020f04150f02010e0c090c0c0a050f030a030f 66
    0x10003640003990344151101d0300008607401e20100440f0010349604182175601d80107420821801e24225440031711a0802200c42d0420b16180d080b0070011203100c181c0e0a8006030f6001c000801c3c00e54150014614424003404070001a45e4a0350144500e1000b0b800800ca10605001485003801400b041e802c00b40000c1c1c01c2081110840d4210a9024410303a0b43e0281c559401d54002428094294042c00007441040080e598401a45885000510360704155443d84081c25016900840c4002142c504040d401120107180848a50301d03141e0401e10425240702d80c40c3c02c0c100c0402c032900c484d00c5440c856103451310702044170704000c00b29105a07a1415010451341d402100304004800c4000340e00517014030340d0b42c00140e59404046002c00644604d40080c8007102c1010310b40018550b110700200700c1c1440f194000c0009031080301d49142c407140303681989c55010800f00301048510711548000d001984d03c05044406402c000d0b91810300703180c2100314540d566000030607001021354050060552529184200b040 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 411679541 1250 411678291 411678299
    0xd020706090302102705040513110607080c0109030509011d060315010c08040605040f1a0f090f100207080f01110a18090216060e010c0905010806010203070f080403020a0807 76
    0xc440003451201134460000021030700041c5000700021030100c0079400c0401240c4000c249041e0036085a807080602885c607110000d29809965100074100d107500c242c1c0360400c00704103420004141c0003100c05a0300010200101c1c12107410074400c0c540414401d8840710b03103c42d2146c5c0007402c0d120111002030800c00010309003422a540d100c046a80c012119650282004540801240d00c03040c0301c240100180b200041c045000754006c009003044980d0550300d1410b42d92507a00030580c0328000d43e01c81c3d00c2d4280c03d0116a80410b100f03800380c040a0b0001e0601c01103c41d0303c03400074501410000892001d6000782c5c1d81480b40d1401071020b821f804103002c00a024039018003041401d1842a40400c00800208114104024101e951054020f120a0606545428400022406400e0141d00894809181814640c0d9000041c0106a284c21080d2070b001c031000d141c84015507102c000142024111b02040008500040030442c00c4043c8a000381d59064440f8114410300104200c03641082c4070300c0c0e126a80c00c02c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 411680791 1250 411679541 411679547
    0xa02100203040c0518070c03050309010605150301210804030602091513080105060102160306200307020f0118050a11012f0c120d1817011b1b08030c0c0a140d020706 72
    0x10b88020b03412710388282d5a9450001307007401804c0e941c000381d0340050802c10f039144148600c0c02035811f8401240a00341c5802540464848407001d2501c0204080428032040000c140d103580540b60300c00d4058080c1e01c241c0342c400800d0b2084d84c4162404003100000038410b010200091140c035a00036402e00007403a500c1c083d07102d18035400ca01b40c4801003071242c45401a8880c5024411403512070b06504512036246d0a00040182d12460407003682d849030340c0b8164541c00c61828520416032629044005091104802d84601c2c400206601d45a4180030b441000a49000c0000001c00c40140c1000a00500703198104600c81c00d081b0746079412441400d40f112490307010300d400700b0310801715036003410b10002005103214064402c0702240c1c0005900900f44112032030006040d04a0341d4450000103429210240246068900c1c0c3c10005481300303204e0040000c0000104070600654008035006041400c10b2951401d0500d00380d00d0203c00ca4070f180c00a0344032111220100003401e84400e0b14005020224103000b401 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 411682041 1250 411680791 411680807
    0x20a03110304180b0301020403060510030b162c0a0611060a06051f1205010e010e0901200a02010b090106031e050108060604051302030607020715230a02100203040c051807 75
    0x301007a0740e03080e2004c5035074003581241c008551001c1e0034016450803a040c91661142e5120558404212200080b91602c0748039031203001121548808035020300c40080303200400c0c0200c0c00b400d0708094000d2590700316901c1500c1200103042640c0c544582c90b1903c4070540c01c04001078846a115401d0820502042c1ea0712010724030303201d0011080c0071041d070001c20210740c019540001444d82c1880c002c0086101c0d5080c0100d01c0c1aa0319000c642a4992a004401400c80c0c3c0311901084040d5001003503900c0e482056001030954800c14800841e10051140001e1180002a4018404070340d8403510080c0401d0680d0343c2450700407000303200704041d6261000040c0c940c00014045445547d98900064410f920351041c4102240c014040f18890303e07020030003a50303601d0b45000380820f1080c1002003d0302c65109071344880420012030310b00a0290a2007000b11070b44d0700301c4d0003000158051003184281d409894400346100d9402403100d1f44c0c1035407500082c07240c5898103040c00c510800c0072108008940d9004880 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 411683291 1250 411682041 411682079
    0x2301150e0d06020915032403030c0a030e01050d1407020f0714011412040309090e1b090c040315020901090b0403080a180f030602070b061206070c050709050403020a03110304 76
    0xf50703440381c0300c4001410610001c3e80351140e058001c81801104039100d25002038284211000464902040040641ea4002e4003c1e031a6142e0104030648001380c803501c50b40e6206c00040c1405410891404400001d0322407070211480da100d42082089000396041040075480700030000600030306030030a466100b0302041e031203200f8140500c00c114044d41381b081c1000ca45c0c4c0068680032003038885c01c25140c018543c200602c517400c0b044e410300702c1545568002007401e5010100c10395014003e00711034000c1c4403606000801131401d0704e1060000102140c0c1703441c2c200301c030103800160050f9204090000035024070003507004118401d800f440240300151a8104844584041c1e06103407003071145e2411955400d0f00c0c07540001f8035040b007204001007040102c0d0080d01245100302c144490036135801013400541e107051940c0d10211b51140011034441405159204810360054041d0b460703c80e15440035105641c0b0070744048005a0100e1450000e044e8414000001518007030051441d29140c40d10364031800d072103162 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 411684541 1250 411683291 411683303
    0x70e0405030415050d0207051b0405060f0904050a0203010203010312081e010b090d02040e03070311030f07020118050315060301051b0307110a0b0114130606170601032301150e0d 78
    0x10f011110140540c0035114031940f0352100b0342d075411451034625140c00003485001032105190070000303c989031030b02400780f080030050103001100d80648104104820040c0064503940110b4041c003026840a0009502031805032100000244080030300404158006001d092015001d8050310301c040c81c0e91410718110f41c4080009078440500340c000802507805114001e502c1440c155009042c0c407000320180074000d0190301ca03001e0850b08100e00035180d12940107401c04a01d81000380000541c021003418041072040c20200958540b6000800c0c0341c420318055480900c00003004001951600b4000c1540c020004100d119a4080400c07052010b400090010303420701a94015600710a8810028150b40e117410419020541d6035800c2c00315420144040401e0103001c50000f084001c251a0007104120398040d581e06503440c0c002d8482001292020707182c00e0415031955002a1036080f140e041500d2011403024015542d45030540c04052001408180414440c625800001ca070782c81d26014201150044 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 411685791 1250 411684541 411684569
    0x30304090b03031b0f010e0106050907080c120c0403020f1903020907050f1309060b030f0a0906020d0507020606040612021f02011103090c030709020424051b0a05070e04050304 77
    0x4070000e0f0840c0a00100c1008a070b44500d515130f030450000030062100104000200300c00c01d181450341d03084c0c031554010135800c12640c901041c151440740440325031150448100f241801c07446007102c0d80d41282940c041548010104080c07082d4501810600c0507044129000312040801a03120705001002e484081d20420f016800642018015001c54800704403440c46650f403005c91041c00242030441e070044840325858030a0114804200030100c90041c40c06841c1c14500c1d994445034503000e0256440100c80e9a40c00303012550701c031409402500d0042c07c51303401600e141d1502c002448200c4080d640f00c0c4000c404403050400160b00d40054011b02c400e000a0580c04900341c4d020280c2c09400e8100e05092064000010480312030300c0401c80080c2c0070f604405130340e58965a0b2a070341c2c0507070150b4003c4501c0d02c0528240c52002c110071034414a44584941405410a04281e0b1110541003e2401d1180381c6c0d00002606010810140481000307009000c0701d02c0c1071403c0c1610303926920301032401913116040754a = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 411687041 1250 411685791 411685811
    0x613030506280c1103070b0414010e100902040605061804050a0513060222030c0806090312060607020310151e030b1f1220090403050901050a09030209160f020a0203030409 75
    0x70f04c40807000d008180d0840f0341e070300c055141034141c2d01812034003505c416111031003484071208180186c2141050324801040e20000f090a11801824071110490f80300e55100c2000074607413910380240a5401000e000f60f620036041000303010070341e00300400c21085a440c110800c140c4072200b0030001c40054001c440180c951103a4454900d5120b40d0481c1d90100c480c454130000100302450780c0a00a80d1156000e440300c646504003010ba0b03900030030b400516680161b20020f51035042500141c480c49000608580c401d2024100c000110344081100c62040c0c807290700240a508140121060261702c07400c044182e41e842c540b81d8003006000600240a40b00d4140600344c403061071084c2031000740c075801c3c120034818102c1e032600c80e4580820240410403603402c50030480c10fa01d80380f500d0074810364240d26201d2030018800011510b661159000d00c00b440500b4001001507100c20002500c0307264581c000c1c0000c82445000548406106031f6404219403001000e140103071008411b490803075001c014082103280907 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 411688291 1250 411687041 411687047
    0x16080c091311040317070b0609040318060503150f0306060402070c18050a060e0601020a0201030c02010212130308240f120f0d030b030309091503030403020613030506280c 75
    0x50300312107681580c109020b03814006161402401141c0c410703d100c4000190a00c0340c10811300551402400c0e0401c00000510b03103040000b0420b510130320030729118041000c01d04000c801e150303691b00640e001603404000c2000300709808180851407041100e10340c48801c1c00e50002662010020031460265401068030301c00c10109180e050003828101045c1404523145542100c02042c0c221008070819050080026121400040c414041c00c01039001d440d51181c1500150080c00303007003102c1c00c1159420030900128401c028a41030090b080a02015004c0c409407c00414221000d85441c151003035501c1da01d0b0402002d4401e441c44020140d070b11641420325a00001e6401c013001e04034480b107008030301c10b0840d90390307001c03814022f00700b082d440400c01c80744000141035581c01009501500705405601141001058925006807403000904507840d01e5103c2d400300d4510b4002c011800c40e0700e941d003101401080400d0040961021101e6076948442051000c9802d0380f41802c690a01d10310f41d1034500e0f041681c8 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 411689541 1250 411688291 411688309
    0xc1203051605010b010e04050c090d29010e150a060f121a0306090c0f06070c051005180402030709030206091302210c0732011a0916080c09 61
    0x40c40e10819100e005824083c0c003900d190802c0e1070024090841c4441513107010312406001d00380300d080036070402850200340400540014019030b80d0004019401145510060482c0c1060344094a0000c6a504d040d68140394100058041c20581c0c624042615071902c4958621048503424500321418480340c3c1ca0a0710a10601c40a02054604014004100207240441018a080b05400b154010364420029548400880303007042c1d4001c0100003000b00a25000019011080c002c0c4a2101e040b0380d41c0001034541c0b04040503050202d4008034560b001c030105560354181014003503400b9480d519081d0302c01081e110321800000e00c101c0000c20388216503100c41e90f40e4040d2640b010310441d81d611503d01200900c00c03400400d10009880c10740054001782a4200390f5050b254061a030460014485502159a030b14007048120042d81c40d95280360400f000b40504d507035280c0b00b000140011020b00e0180101c01030010514146089022041c48c160760b800b051036a408020b001e400754841e50108000340c00d140e = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 411690647 1106 411689541 411689557
    0xe0c0312041406040b04030f02030d080c0d0504060f0501090209030d1404050907021f050601030b0f1509030a020d0503032e0e0c07120c03020f0a0c120305 68
    0x4400300b02c18904104004020030705068450b0980300c00c54100d0b5005032002940100e0030419410140141c9840201e80c1c42c203039280f40b074070204100c8244908200d10503150b941310700041c00e000e501c0c0c1c41204d00e1400b00c0d40a114650350740b101c0c43d02a410890606220340110307040e48440350f02601b58505130001d4054031504061801080184400c0b005200c0c409500501c800f4080005d8a502e0260500b070070544002241d0400c071000500720390801d200c01d40165042804940d5954868400380f2036000e6100380c190746e80da4401c1c0802d0801d41600d0000f50001c008181000410070040051131042603c1c9602050800e00e11740d83c1c0c98141041c0500042d50710709540203108103090414425400138200c14240e1600403103968521342018a0004440003824152440301090f5040c01114040405d6138024070312880542c6503003070a00301900c2034158141100720b84c101050300910542e0b0080d = true := by decide +kernel

theorem cover : BRFrame.Cov 411510791 411690647 := by
  have h0 := BRFrame.cov_init 411510791
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411510791 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411510791 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411510791 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411510791 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411510791 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411510791 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411510791 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411510791 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411510791 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411510791 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411510791 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411510791 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411510791 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411510791 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411510791 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411510791 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411510791 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411510791 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411510791 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411510791 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411510791 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411510791 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411510791 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411510791 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411510791 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411510791 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411510791 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411510791 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411510791 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411510791 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411510791 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411510791 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411510791 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411510791 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411510791 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411510791 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411510791 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411510791 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411510791 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411510791 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411510791 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411510791 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411510791 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411510791 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411510791 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411510791 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411510791 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411510791 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411510791 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411510791 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411510791 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411510791 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411510791 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411510791 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411510791 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411510791 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411510791 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411510791 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411510791 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411510791 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411510791 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411510791 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411510791 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411510791 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411510791 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411510791 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411510791 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411510791 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411510791 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411510791 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411510791 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411510791 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411510791 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411510791 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411510791 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411510791 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411510791 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411510791 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411510791 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411510791 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411510791 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411510791 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411510791 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411510791 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411510791 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411510791 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411510791 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411510791 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411510791 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411510791 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411510791 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411510791 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411510791 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411510791 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411510791 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411510791 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411510791 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411510791 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411510791 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411510791 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411510791 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411510791 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411510791 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411510791 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411510791 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411510791 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411510791 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411510791 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411510791 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411510791 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411510791 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411510791 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411510791 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411510791 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411510791 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411510791 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411510791 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411510791 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411510791 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411510791 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411510791 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411510791 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411510791 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411510791 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411510791 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411510791 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411510791 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411510791 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411510791 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411510791 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411510791 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411510791 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411510791 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411510791 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411510791 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411510791 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411510791 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411510791 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411510791 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411510791 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411510791 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411510791 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411510791 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411510791 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 411510791 ≤ n) (h2 : n < 411690647) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
