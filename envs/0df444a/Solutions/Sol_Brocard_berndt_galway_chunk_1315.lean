-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1315
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T02:20:00.074361+00:00
-- url     : https://prove2.me/submissions/41c37b72-b09f-4e95-bc8d-0fca41c969ef

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 236330935 ≤ n < 236510791 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 236332185 1250 236330935 236330953
    0x2150a02070807140d020303042001030603050105151207081f020405030d0503070f09140d050309040203010b1e030705040302210a0305131a0d0b0d050a050a0204111317 74
    0x540c0d0b00d40c0c00700d80102c600d00050300c05aa00d01d1020032058000030100c1c0001e500d50700302034070f0306a055403250507641d0980c2c1c040c4a1b10f1440340d11a81001d4000c5034000000e100b40d041c0380025807940500112040c1c001c2c2c06010140b010340c030000078400d04440c418070280001d0010b0298081e880b481180b051074440b9003c00000656031804c100d21004d00c5095910b658403410301d40c1009002c1101c0325a15010030182e030703030f0a0150000c1a008809040402c0700c02100d484c800b03150060440c0620b200d8039501a00c044000034041421a00400c00c114400c202803400d40000703a44801140800e49a0700d000401c140310074001401c0004201000c3c240d0039020340e40540300e9500440c03030030b240d0200c100c0008202242200c0c04441c2c05070060040d000c0f44050708502e17005e140070f5018a001e0401c21046841c2c03541050301c0580c030340d01d886401c8980c000b42038910480540c1829659141413840407401035250440c44050000702000707660054003001d140301c082034601880407100605026561045000303017645 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 236333435 1250 236332185 236332193
    0x30c04061802071a0403050a12020304050601051e0406030c0317030f0601031a0913061b082a0a030501030506060a030f020f032d0118081e04050a170f03040602150a0207 74
    0x1105d204038032076a200d59803801e0340e6000502400e001d40031350305403c0c0107000780000070340040380070380c1580e030140c4824a2440e55030000c50407481e0310380000e5400a16091011082c000c500e11a041a02c2c05645c100c03c0c0b03021140041c40281c0b10131034034005440b4840c40420b035158405c1c2c00648403108000d010092080c084400580304007415201c3d01c0c03200d00c503181104200401402501144039205103144122400940007070220500103019141c00d4026080e101d10001c880e0200200105880d030640307845404201001e8010402030006543c184508070001d411860f10544240039250711080c1608145529400d104e810380051089030782c5070040703e410407851003462072030701b51001c0483d004d100795241d0312032941c0c210785580344030025140c038441030f45d408542204102e8803440c2450508120074004500f429240c0e003da500a10791142036050000380e201c6019103051000c541c0074003a903101900781403000d9500c3c4100e104080143c1c2000d040117020184046141e540407080c03410151401506e1b9071 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 236334685 1250 236333435 236333483
    0xb01060509120d12020304020604092c01091203020a140a030603020f031203040b040311060f010518010509010902160c0e091204030c0e040501090606090b030c0406180207 75
    0x424000100041a22030180c0b401e240c00d80c10082403140038001c1040814002403100c0c3d800169221120740020100b000c6440306001c035801080e00d60010400c00110700380e0606034048170810710382c00c4800d0100389450200181700b140c902c00e520200400b480c12200318103070041d411456105003408001d505000e2021904130041403c600f0683c0d00081841c21072042000f5004000c1032a4040c0c1e0083c5103c5a40c403d144040703d80003508400491840e9a80780341c02c07608070144440c00716040c000c00e003c1c0012181030040c0e243c166070003181d40c241c9800406022011000003480b825030b100c0c9550b001007000580c15401441d1654995181c60140000343c1c0b80c2d86103440e455805030040c000f0420420410340002d01544c0b00d520103402d005c80c0303403500c0d40c3c4031599480003d01440c010070500a012804105c000d60240f040554440006e00c00750765100900c900401c04440702c94080c2c001c080d40d2000034a00b80c0300e41006e0703a030900f07030310003c2441000e41d440c002d4000c0202210a030b441c1407094007050030505 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 236335935 1250 236334685 236334689
    0x1a0c030c040e15030706201203070c02120709060905130b06040b0a2402010608060c040b0307030605130903030617070e0402030a1703100b040308031b21091c09060c030c0b01 76
    0xd111f40b0031660049809800e883c40c5130b0140605a0060461707400d0510b81d030320403aa001825413425070002d208500000c1d07011000441d01061900c02c054001400c0091030300407004444010100700195034900101001d59485c0c0d050040c15030017214006402498140e000844517031001d0002d0120580b22600840c00761444a0f154030243c003407080510017168240074400107440c6800c0070780705508103404c0181450045004410b8800e0b00480040c140318400c0d4070170001840c004200044850800d00c000005004200056000900f40000424207600d8407080d600c00c1d420020060400d40d18007c1842c0083e40050030499050203945006030102d07034240c4413982c0d1913403549410b5559080c000840090900d259220f22006c82e401e02081010a1140c410780b81d224403503500407038100070040d0403050b051140201240010f2051301448541138103010a181c030898603202154041418080c100c0300200c540310400000551800e410b10001d4072030415003000500c81d08103c018000c1d9681e840c280c0110036 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 236337185 1250 236335935 236335937
    0x9010c0638030c010c0f03030f0203190b0105041d0c09030a0c0e0f13030302090a05191e030f0312020927160806012001091a0c030c040e15030706 64
    0x698880d0750505080d605100319488220001d0a0b004604000600200e000c00c4014259001c001c100c04203041c081c2d00850a6200c00c0a4115900c0ca0703c011002c508030886020400d41c0361610b003641c0402c2d40510102d4098580701250350001c050381540c5c503000300400400500492009004210150310208400721000788600b1a50892030b040113280760043c0b40003400c09440032700417014002200c40300c020304203440e034041c07a0160f80c520b60720000c41d64a00c240e0380301c04d40001c200080881900869000d810039204200c48035030001d1038143d01d5694000b110700001e810050390644090000b03001d00c0c003401d01400c96400c054100340310600041d803c12083c14040107001400344550b000440a003949540c8000044d200041115540d500107000b414000c0070b1031306100050b80000580c419484801c15081c43c00802840180040e16200020302ca410b80c0f0880e140780c814000c18070340072881082d20700c2030f408070b980c023418585060750f510328510000d413103440c0030044071700010420344003400320030041c00803 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 236338435 1250 236337185 236337251
    0x50a1202011413080f030301061e110601030c14010c05032b02040e040b07051603030b0a030c090b010f2c0a120506041e0b270708010b010f0f020309010c06 68
    0x900000c090400005080705945031b0010070050102982000f0036603181240041070111408070400c06860030000d000e00d1440700c0c03246000000400c103440107a01d0948184407000c1e1190f2546030010344034100f46080c000c00c43d40013800215074018060500450300e41c0c04010715410f910320710a4810880c0d010760800c08800303800c03900b00000d00c42c90601c9a604100a0714006107040700725440b0b440303603043c4041c0003001c2544030070044506555260b1100069a040000d105070342e03a403030050030001d018407000345000c5070b02c1d5007150704194007601008201101480c60402107c1e400c203048101c1590b2020840d500612880d004940c0040d51001d845603140324600401d05801d01c0e0504408080500301411050710704601c800c0005031816203203980051058948010f00115180041400640b04a40300d03414498801c0000f081c1c44150000c070b402c04000c3e2510421501c0c2440120351441d00000c0c88009a40b040001081079440341e02d070b1070405406804000740300c0150b03910345010040c0c1c1d00c44131046250 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 236339685 1250 236338435 236338439
    0xa0b15060c0a0308070c0f020904140f0714090c040b1e0706090201080c0c030a0c051c0903030801050102010908040b0a09080f01020d1b081b1303030903050115050a1202011413 77
    0xd001009240c10003200d05100308003400c02c1d503487e4510085074500a010702e81801c046410046c0d0001805480f910a00555000031801d0750104d5842c560380c421031600200500e0309030001d00b40310a426016140303a1864515141c00c108121803a540064940d40062400e204411503180c5410007420030359100b10404030741d007403160000603d2050040c0c07861441070410842001b040000004490102c1e0300d500b44400c4500745130522506042410f1044110355001c6c0009602e00f0740d1018641060740c0c8070741c481c1c82440c0d0721640124229614034900915192040106000004c071920103000007030b40604d0018282d0352100c1d00f80b814241240305200f10344c0e4000c00d50548c11181402107070035130303c034200e19041c0710081080b004008180160140e08070403244d246515010a00000722401c2c035070f0800d9000c820302c1d9a845e0060481400d0322083c0c0b000c0d441c00c81c841036000c1050600008a501c02010301404030705201c00c0f40b804044d08803040f414414248101c0004001003c0a03011107050003a90340c09543c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 236340935 1250 236339685 236339687
    0xb0607020d050f0a081c1a1c020d050609100b03060a050411032a0d0510110f2a010c0c02090a09050f06010512210d060902032403010606020a0b15060c0a03 68
    0x9840e1803054641e00b01850241c918001c0d0716460001c000c104c8940340e4503042d0220284c00348010140103504442901d054ac0c0900c08001030b664010a180c0048511121208011074111445c2c2400554035810041c0411141280c40c2c02094000d0b014141c902c10019060002a2a100442c4100c088204401c1d094004e22801034010380340020060301d90007210b10041e034030181c9428402c202c1c2840641e0b00c0304007607070282801c01a10b95168000400964441740529188880080c83e60072100f000c00710200c000d00300006000310800c2d002c03240c8512403074840702c0d030801421381e00051402202d6980c4802c0e04011440411088445000f2000a4071595040c201400302d01c052103006174206502c80359914180e000445c0d440e0f942e4038400008644c440002694402c043e04456002a022074000f00c00d0042c3c444601c6088541c01c001035258086502211041c1030070f841851043c08050b81101901002192001210303590066502e221520501d421800140154120319140509540b00c482888209 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 236342185 1250 236340935 236340967
    0x10c080109052a0f090d03030e0601090603050a0605060f0d1119290405090a02180307050a090f060e0103050d0807090e150316090209030705040b0607020d050f0a08 72
    0xb41043c040c0c161184410b881c0700006030700d04614508020800130f480700d110094901a950070780c0004096100b481d105003401400b40c92440440042402004c0000a0990b594801c02040700d5001c800b802c000591520b4400051200810303082d0098240c40900505940d44201d04100300d00c82c41130403030303c9000c038014401705805040c4101c0c43c401003d4000d120206925080800300d015183c0703031440c0750416801541050041e540601e4008900c8002e008841020b90090f04501d43c0d0550145180d256a20405640d41245d200355130304006655028089a1940c1d00440c030000609034001c50510760751400c00c680703218240e000782d41503040004520402c5070300c40c609a0304440303030b450b0801c0010305154008019080190106174041600500d40f02162001d10000d0b100001004a04800d2607403204020042d40c0002000d0b0b209001d48000820645098810b0100c201c0c0c0162001e0700b840c5541d424000d4208095038207481034412a07405044400c01000680040d51150b81d07400e4550100010220b0f40c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 236343435 1250 236342185 236342191
    0x5010b130b090102030322020d061431031803050a02030d0f200a0507090f0e01020705061302060403080a050d0f051905071110060e060d110d060e010c08010905 70
    0x500300708001003082e030307a80001683e030011220761881c1c07003036098448216861200e03494002d400c030050078444403e000c9194444180c900e5440000143d030b030f56400e580c08a0504105500058010207000310b03100c4400701c441c03040101e200e41402c419840c540c44038140c9001d215401210325034010825070003103040a0003070340e1030400d881c2400d803200e004038900034101803142520200ba0340c095110240490704108600e9210a0f0030500ba14441034481b40300302c02412418075001b550034141408400c0c0c000c014421030310300582180c003405240d02c55404404980c5100181070b60300c004203100c080041081d20340208104801130708c0369030340c8110010342101a1007544000380700e040d15182c100b1480011303280f00c0709440c05a04200280c01e90741d20805032a00c01c0c0410010806d4401d01ca1600b142c03c40340c1c1d00440a84042c100281040e5070350f4410803007694220303540141600d02040d41140d4074103029560750245441000c000c240e1407602001d482c00c541414040000140d002c8004024003031003842502c0d0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 236344685 1250 236343435 236343449
    0x1305030c100b09010308160201030207121107081b0603060411031608240d0804090c05031b030903220909030c021002070b090105250c0603050708010312030e010b0405010b13 76
    0x410351714648410241d401500141803203004c141c4446001c5a01c01d0f81103420440c0c0c000740c003440000301040c0040100da0300b1026941c81c2c0c801d081001c603c4010024580012202c1080c0e55004c0bc01204148860b540001e0b0015800c6500d0310085001034200c0d1026612541c035002000224800c41d440040c0b500c04090801140603100700780c070412045070600000d001074401d5500100c0141c841c50b0110070f510403503100c2c06140d0319099400d0103c0783d02200440c0280c000141c200d42c241c20388280590944802c3d9940411a0b008000b0180e4100318420101100c0e0f01c0700c0c1a64441c01d64071401c54059a10b0700804400051301c6210300d0046181064119091501500c02806468100103550704107101c2d00562134140a004540003c3e0441007141d64041e8a07002e82c0c000c0c0841600b1700d00b40414500c18040c02c00070a05020001d09024420042c4a0490741c01500000c6810403003042035000b441c8251314550340307549803000c0c05e01c2602e0f14003030b55001340700d0158156900d504484400005c50083d800c00c0c1 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 236345935 1250 236344685 236344699
    0x212032107050a1b020d0818011101060509010e1f060c021206161d0d0b0f0a1e050a0f0504050f070911180d05011a090112020a0e1305030c100b 63
    0x49001030f84844c500c0c0080c0e10851520f5039000c102e000040d00942c032a40000c015140006c0da4007014145611004001c003c01e88908403071031a0049610300f83e5800b4007403030b40c100c0035080040050b0440c0c92400f503004a40300a91800581d0500e140c105d13454844e42040012460709220341d021801c2c400302040741c940018001e003600d4107142c2100c401c1d50422100c3c03071040250300b00d07012000da840c08240114500b0003c2c4034041c9100369140070705600308201c07102c18050940c1c50005907011180c2c014075644080c84200308012410242281c0010500901244001b59950048440c000c000f440b900740600e000b00c3c02001c0b015034112015162000c950031050415003040154050b40009030242d55041c05018000100c1640710340115031b842c0c80008024056600703200d1404400070004603e82c81c1d000f0241d070308084070ba0302c4e008103181c0c0d8103c0c0c82d0001e40110041e1070421005c00c8012200d604a242d4018151f10b03d00c0c03030b071030301e51440e0040100969070390440001181030704910711410542d0503040d2558 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 236347185 1250 236345935 236345947
    0x50a0f1a03040f0f050715181a04081c09080615041802040c0806030601170c04020a020a020a120c0f0b0307030e0f0d0305090f010b010903080903280c081f09021203210705 75
    0x22301035100d2510800421a040c90040341b85105560203550180c0403020032141729005015440c461500000c5c1d586c0c0c0850a00880440c0500700818050310440c0c01441d40e650500e0710384203200050030166031119114080d030302c0000c0107035128021a80360b01c103e0303692030030746061140400d4104501a44200502d40880500d144c443c8004a4103614440d012500142c5805561070b0580c240701140100961051003a4400b20340060980d0b0b42045080c000d00b040401e55803143e002c0241740d01d6070301800b0910304041c000161001e10980008940b45064130654160623607043c13801e894481c45190704c10200e625102041301e40703038040201c0c04206541c1e4000748100284040041c2000c40c807030101030040c500020301114140c804001d03008141c241c0030b40b00041d4143d13202ca00c0f0740d40c0f030007540e04a55040e03464800240c00080058042c1407440051030b02c41d0721607030315850800144010001240c102c42e0038103030f040058100740090700c03030851144103829182503804004e00c11810000c00e0b8405101052001e = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 236348435 1250 236347185 236347217
    0x30105071713060c0c060f06060e0d0213060803121006050f0307090806071d01080f01050f270405070608040b0106080702010e070f050a0f1a03040f0f050715 69
    0x84032020000241801c0050b11004804030524030001d0700a49400d007414400881c6680c0015076081c110b019510401104402c2e20b1900241c849600c83c1100103442d001c800d18192500941c1c00c9400e9200910f18400701400030b4115090303684690111001e0b40000c240003107007201c555401076000204081e480740075030034102e01074101d019001c03080040302c0011000400050107400420050000007040ba1581d00e0100402440000102001e00041c15014043c6a003940981172050140444149a55880c0c0c02e11003401545c610b00c010481c1d0040c05800e00b140340b00c2c041c1003000c007007401c40d40c0f0040c4189010308100f468021a80e02c0b031000c20080c002040003040400900074191202131802e50107948402c00c04030f001d4458035002e0000d50140c0b00340040c004180c0702c95001122001c0c3d640c652a1543d881410b117920009114404810489892040242251070015a8001c4c070540d5001c0c1d803003203a0b441c1c0c0c482415102404451551180005001580722030100340342082c0b040c50051030702d01c2c20501c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 236349685 1250 236348435 236348447
    0x80102040b040e0601020f060c0d061d0402010f02030f13031707030c08031003051006210c0e0748050a03080c1c021305010c080703050306040f0606030209010e03010507 74
    0x1c07803183c180d0410340c003140c0540c2c4240178440120b44100c00b218081d0a0280e85182140d100107802d01c038091405c0c0b03000031400e42001c43c444c000c103a800001c6a00c1c0c0c3c0e40b0b03001507421920784030b00401180000c00a8504005181020b032030f0030a21030381403184413825460400202c4824210031070024600303004c0300000075440346096112951040090381c89485c1d000c030070b00055007250030090282c01024001100707018030b80c2c1300904440031b450f4211480d000780145400005400080907184200c03d01060100041e54000c06400071010f141400b2807100c0b00da4121b9400d507901c50503c0064103c0d40d541611f529089191152035501d60340495400d1843d41c0e201a920400041d0080522001c0c1c40000c070022019019100094040d800105000d00c8000c0701500a6201501584200803840c8020445500c2000d11301c2d01c060b4000046881e02d2195101030720150001424070382e125440e19801001d403d654000c2200030202c2e82c40250301c48682c200050080000080e40c44d010741c0c982020011190707404a = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 236350935 1250 236349685 236349689
    0x20c030a1506090207120801140109050d1106040b180102010606050304140a050607020f0105010f0e0414010b0303070f020103050a0e0706120b06030403020c013c030207020a0e01060306080102040b04 87
    0x8503000039120700d580c5559014006551000c1411440441c12005010354490544040c0340700380d4843e04a6a02c98101000300180d0040b018005408140e086c4030f5400c014413080c020f1401140320145a40340940040c0c3c1070351081e04064803014010a03100c2841100c240f4a90026100b4002440b003142000001402c0c4c1c04000d002600c051a0b0360324652000c1700600c08041d070707503401c903041e10785519010902030f42e9008400240d43d5903600e40000041c64000c4101c040301920f40108100543d5102d94031606a054050a040f9080e175698070340d00c07440ca03078040000b4800d0a201e2111000100003d000140c200e03240200640d400d18285851480e4100d800315907901620b020307013403084030400e003950300d02c0007001a83d4049030428400000c5c00b00341900060f81c49640d2501340c2c2e401003203000007601407582c514802540071240c081803030b62625080c5500e10120300c00d04585001814030b802c940018805040c01c1d40842001c880c03401c01480165454060700303010700144402989010301d011090702e42c5100d18 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 236352185 1250 236350935 236350943
    0x9010509041b0e030d0809030703050a1107060c150b01020a140304031401020d0c05161e0807030f140a05090d02040e03030f01063f0e0d0c0203010c020c030a 69
    0x19103052180e40e6588886080e40505000202d203004900002d4051980440700d184240f09481c034440d00b86210724195803140340c40b90065401c11a050340c0030381d0310b81c002c20300c08000c0c00a1600c46a040940070022040140320b6643c4000918001f070800920591041122504507818800004003d9070000703826080c0e40d40c0918100200161350514505502882e000186043c620302c00e0340f5502c841c150058101e80d039010b4020030801001c02420388142c42506000310203500e01403201808160314990842409052003841d41c00300d5510b5a420131f442e0701007242100494000032142410981c005c15194240003450102440d1061111018201d4014210400d10600d20210440210f465641124010b0004441200d869051444048541c900c3c24001c010005d0510b03484001c3c1c0d1340581e0700c06410782030290082c40c038410300341031100c80c0515008c401004aa031502b509403060f00c0200100310750038065030f984c0c682c40000d520402d420340e070102042e4003c662044000207516500030480f40381080e40 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 236353435 1250 236352185 236352187
    0x3051e070f140a0302040302090a060f1e0909030c050c0604060c230f06240a05060c010b100306030b06030604110603041a0a020a1704050613060f1b080714090105 71
    0x240000440b150301550100391008040032520030b5100350160058410b5070f100712214101546c4100d8628115070091103002401d911507142044011546860600d010b009041c1c2d504040da201d00b0000309a8450315070440002d4404081d80c01400814488131402d66811141c0501e400d1510764010095840c4060180000d030f5103c00d40540307400250b1007158091451015034044600c0c007120030727440f03010846117220000701e41d1518058940c500480500c81ca00000d0240c0880c5081509104058000703440c0d41695643e5001411196030320f09410007000c4a80e5034006c1165411460b183d0035404020700414040da014000b440000790f450240c0d0410b0303620503140c00d5120b581d182000c452404c68550007848000c0e501301808036888158001303040119494a80007140e022607181ca40005000301e1b005042500000e0205813042140b0342803000e0140a51000700e1004605250503086408101c46950050740c545900c10f681504108481d0303000000c0e0802c42680080769800c402a80b159040035410048 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 236354685 1250 236353435 236353457
    0x260d020a020306220516080d02010c021209030c0d11011205060a06030b060d020301061701120f030f0c0b0c0406030c0804050c060318060a06030606050f06041406120403030c03051e07 80
    0x602c601c2001006600201240c40c4041e112000c2c01b2401d1041c01003e016002d100d8045000314014043e160f03501080f9030040c400c2070120403007895643c00c403190030ba81c540515200d0004541d5107440514840c1d005560103000905500c2c005005000400403003e071490031302c0e0800500b13076101441141150340c2400d0210b02d4070b82a9000810910403210300c503540c58404000800c0f0261f0220140102659440c16000e850b600e4a1440c02d000041d0b4a00810300d101d50ac035084000391140a03101860341aa08006440c1d0071240e42700400c001e400c40c0c003110700b81c1010400304181541405426540819410070b1072030390a0030f86803180c88501e005815401544d0003c0481c078400655600d095031005104155102418903550310400b1344003e100a03a24036041c020702080030710744240d01c6080868001d0141789401d01c2d0068040900c04030211050380440f00703001001c401c408240e416031280f0b03c06e54000072002000340c4003400300c03032014202041e0f03017045141600381000d4900541e500400c690070200c200306 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 236355935 1250 236354685 236354731
    0x10c020f040b09180d05190f110114040c17030421020a0303021b0402040b09010e0a030b0403080a060b0906090105070f050714040608030a0e19260d020a020306 70
    0xe000590b09030854403580030081d4403020152081001c0255609640311408241c0c001c0311540503078000e988060011a91280f601e60007907900150106050400c2c1c0000c00d200f40c501403c4075401e031422519003506a0402082206000d9000040c184848540c501d09042020b01c5960340183d000e0301c94000003801c0000101d1440e01e40c0140d0b1264010710600400761030340350081d00d480240a03840e0026480c69400c1c105403a140c000e64003540c441c6029623007006484001141c1d55070508000340c0e0130502000380400819031408000e4421070081d10303141014100b5020030304c22145160b104281c0300005020700c07416592403008460460300c0900e840c0c1c0c0c4480081c00c110382c1300c0d02d40310306c024100d10640c00d0001d8958041c15a04032088001c0358100003117690780280c643c40e4460707011a03200094882c0c20304685850322a224034a9502000078100c020381d2124555810603111481f4140002d03a041b01e0064020002c2000242d071417460700c003800b45c050700c80c0d012031fa542d40003402402000d058200318100b0301d = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 236357185 1250 236355935 236355941
    0xc08160c030609031205090d03090317040c230105040506070318060207060e0307080a0206030c0c1203060f0f0f0103180804030819020f19030e030f1506030705010c020f04 75
    0x540240d1205009a81ca1801000800c3c0400080380454070355074220202c07201742d00c505489140c0c2c030b1001d01714034842000210028415080b084061010303001c14540103001002440d8410b81c814a5214071850418054400d07078584c170840155a1410944103699699116040c0c5045580640705d258440c8841d14080d00c1030306240c041203481c402000c1000905503400100316046489030b40f110340303500c2c92041c20325855018a000e0143e40b0703030202913400010304003180195407086880960500741500441a1070504512290114103070308040281305d0b0b2864071a0900c190410f0450700b40889401c3d10300401d41c1c20554140e101d0502d50b858108d034503078205000454442c990710440056441e500c9180101c1e09030401c1002e080c011050154000c0c47c240002501c1c14604190002050311451103041d00d029444001000c90400003074079000075040c0c6040040c4900f060b0f059010780a01100c0c41020302c2d6a010003484144070341d209030701c20000c0740d801140482040d601030f01d00600e03039130b01c41e408500a = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 236358435 1250 236357185 236357227
    0x190903080703020601030309050a0e0c071a07080103020906010302030421030f090c0905130507031103160806040303050a020f090d0236010e01030b060112091b06120c0c08 75
    0xd1100040341c0d402c065020034520f050b40c0c0300c0d455909595072a1803c0c0034180c181805200117641c4c40401040164028402501c6290301c2205c4140e1440c01c0352150703460360913040e00e5080202d0a50740060086241c0b40ba2030940c0142c00b0302e02181185069103558a0b0764850403604c41c0400d11540700400c8003031080d0403840d450079000c1401e000014103849d02100140f5244141d55001b1314082c0410700074221144e2510120341c000c4000c1ca402411903d84500c0034402400c9540d051013000d00a1404040002040300203010500180c02503103000d0a0103000d4039001032241d241d1601c100305507032200c0010b009030f4002a106450010400e03074244003141e0402210102e480705403096181c4840d4445036083d82407400035901d02c01c8501070b41c1e03508510070758103001c2c00010b2614601000080e00365100d03070050704280c650120042040040341d02c0e0381081d040c0c11410201a4241c0c04018482075070800c04010001005030003c203d1a10210402840d40701c0b2900010301101000445250340e0068200d00d02c4 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 236359685 1250 236358435 236358443
    0x100e10050a0617090307030c1b0e0412020c0a080607230d060609170606010c06020d0c0e0a120203120304240b10020606010806060309151303020705090705190903 71
    0x1001e2901c940003c1d01c400b80c02d62000715248858000100c3e048000f10030f0b030710100c1d415103401d0600c05180c2c1e180700803c40d01c1140c2c0c404a0b0482c03100010345142c0e551a29000364000d0b000c2c064680c0000d40004e0411000c101c0560042d0380c40503007044030403c000303401580540c0314500700c10a030040302e1503500f800400c3e285500035100003294401900d1142d62217401100c0c015250200c00781e43d80d0080b00c03444c0d09d90920b400781c26000034000440700c2d4007800c40d0783c0d4024422003005103801400c980d240122070074040c12000081c1d003a420100c0e5030800b0040781000e48485891005041c555500090f62240f0150400390b4464010010400f000684403148150011801e6090080280c418250f00100704141c501403081c00001c4030f80c200305001290321401a84c2c1a03613112115a03503001882010b40c0007034000740e007521600038055420308010321200c0c0128031900b00101800d180e414000e14003015034102500c40e004103000c1c00043c81c1c02408486c4003000814400016801c2004c098070951078582c0058 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 236360935 1250 236359685 236359699
    0x11010e150105090106050d1a061801080105040b0310091b17010c09080a030c0314040608010f0807120b090a02120609150622061220010206100e1005 65
    0x6500000424510140803218400300c800781e0303039001000760805081c032900340420f0081203400848100c030b030880b15900f03900b020110344080492020071140da21004442c01c0c10f03502884424003039a840915540101411602030004400800c0002e4442484541c4149965500c19594040151040003407484ca0202c05580c40031030b544206070350041c80149040c00c200d510702940348071800d004059031015240c01c00004e20040071607640c143c642c0d0313003e01c00942c14401c400101411203229400248081c10140d5510216549806000403510380c054003c1c0580e0707007004100b4004c031350402c030212000541000d401e80c1c1c503454015103103082c03003030034100a90040304113000c003e6031a200042c814000d501344030071904a240414560090907078103540726a0700030305848a100c521401071070700301d1a50072081e1000480f15070364540c509004102c0700b404c030750001d8568010040e07d20404030002421400380064866841c000031341600f8030109005696030b460101001c02e11207405e8080080c09050050544 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 236362185 1250 236360935 236360951
    0x81308010e2a0a06022107030e0607020a0905090a05070803030f1b09060f090306061e0d0c0f030f0314030f0a020a0201090203060f180a0b151f090e01171b011101 71
    0x940345c1c45646011b00c20102c10341e014508600e0030030201c8048a4142e83d8046000c107108041000d20b9101a005a030f11240d0350001040c2500c0320311501d0b024240707010003001c24403680d00d0140d041c204240d10050346900184100902c481c075105102d6880104c000301241c07100085074608180c2d00070400c009400c0540404c0e01180d0782d81d1040208030208044040329610303919442040909911300d8159000e000e071940032806281407118a44100520424003d035400d6101c0c0245070313481d0700c1580181d80800b104111081450f0704810400c00d43d6001d5045240f8500e0044070501305c2490150150060b1640054075000032031003940b00c11300d8194010281c540c1818201400d203010340d07081d1240c1d90f09407001e00b00741d05601800155403600c698004100341003a5116003003800c0407150302c02d040f80c0229071200480700480c0c0c07e0b41a004c180650351102d240c03207130a180c0d4220282e00e0503040b00d04010041d184070058868005080d030880005400520100c0207920012a01c8004444c06800907600301111 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 236363435 1250 236362185 236362187
    0xb0106080405120a090f0b0a020d050a090909050c0103051006020c0f06160b060a050d02010206041e0f05010e0c0409030c021509060f070506070305130b04020319081308010e2a0a06 79
    0x724000c4a44440b00d030880247c407490182c1e11481407040100150b4040c17102800d819004601614440788207007017070941c0c0ea0740d400151003525040001111b00e9007100c5402000c075a0035200790380d0441c001c0148031320501e0601502030340e40c0790308131300c05407243d1418090584c150f500c1c80211441002c03c461007403420251440c181c48000c80075180f69200381080000861642014000d071003c3c960142d000b06807948030f94903884050380d005501101d54017103036003c1801291500707032400046882240002031b444580c3c05000d08103110084180e00c25030034150034201003507202403160344846d012644a00000c81d0034403160389038421b010340c45402c2480455586222292540a404024002d0b4242d42e869501c40b01c0440403160110b41c0510820400d0084501048402119651051005e411500301940076562821001c0f0f20001c21581d03640000b4112a00c43d200081c2c00d0002c010080c000e002543c100c0c51602e0301d03030391855600710399001c0003001c10304a291042143c40c003041c0d01900201c0c00c42c1d01c03104 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 236364685 1250 236363435 236363447
    0x3080a03020d0b0301110d0b0a03082208071212170108010c0806030d05040308070302010b181608100b0c01020f0408060103021c1a040203010b04060e010f0b070b0106080405120a 78
    0x28034180d039a2503c1c0d00318820f800c042c090f082d220728010840134035054440179450005d0105502954000600201c04800110303200000c0401111841040c02c034041a6240c1891548040d04044c81d9500810720401c02080c0240002e100d156220751070000503201d100b802c4032003021100c401c80040030408000511b116065004540b0b0200300e69551446603a803105240c4d80d4800502070b0302c0025000c0001b0804200c006029010041c0f02c1e00c0085001c401d04c0c000030316440c5025161790480021141803224403405119074a564089600b080605890042078518a0010034400c04890400004401ea500002941125410001c012080383c80e9030319024074a90f503075001d0004900400e411100c2c12a0540e00c0310050250983c000700407841c0e614802c03002c12084001800403a0107640f1500c0e200400d9a0700c4c01448003805290711000302540c9000c041110021095001012091040223102d01058980707214505617481070400b038a4980341c80c9401407500c2d421909140d44000080b601003c0c803a8005 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 236365935 1250 236364685 236364697
    0x702061b01090c090f1b2001020304150b0d0b0c090a0509010803070302071e18110705061006050c03031807082406041a130f06090501090c0e1c050703080a0302 70
    0xe104001d02805804d0b080c0c1143c6c02c0c2805041d082c1c140c41c030244081c0748101c000f04c0b0394220786c000d032203241a4210344040c01da80003030302c088800035400d440b0031080c4d4800748102d2290400450f040c0a80b8201611450003809015051811380440001c1d25101901e03240c7d0300d0700c000c5c04090a03d0340c09680d04e100503a00d0f90082c0ca0224010300446500048050300304182c060008010908041c41510346072008017000720303a0b002461840e45408101183d4040f001c00f40071254011006020245002d00c44020440255006142030123805d1140410590f000810342c2c0d401114a0510200c0c568440f00403841c003440799206120610070f0007000c81d0402613031144130b210464001c4000d81e00d07455000820098500d82c600281b12003410801602c500e1404000c10b40c003000c0e01540000302580f035007202c4419680980c10a00d100d540380c07801005201458400d40d0900010b41c502110a00300001c0091005810001004820808465110b081c8030301030050000456011440d59501c203000131018000c0d40200d = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 236367185 1250 236365935 236365949
    0xc0e0d260d02071509080a050c01110a0c0302070803180f03030903010912030b060301051806040b27010506070210080717070305010321091e0902030f22020102030702061b01090c 78
    0x11002080c4d20008078050010b600307601000a6080c440025800c40301500301c5c0c084400250340b2840c0030f540c0004c066001b030980d000715503100714a40d4030b18203000c0d2400207664042540d07a80308005601000c4d00501d0143d102d020116104d10040c0c2550001901c0c3d801004d2002d42d05505c0d10b080842000020540f4450307084194400380440403080080007618002449096044904c2d070440c00304100315000700a0340040000d20009000c505074012454056210781d03110070b03000ca40154440c0031548144071a0040c0f00840d815440d01c003d66000c104503003085030601e001c0c0400c2c030000c901064010800321403592034034200c0d14082c1c502120010040c04080c80240c50b20300140e08965250303900341c1d004049407030140c2c032000794251400c1108506002001140001310b2750980380820340c040103000070f5001e85030005c900441400c0010303984654800b0001c18900140110700700c500180d0f008401e9520380ca4044a6954542d608004600030005444e9000c0740c50b54a840c800c07030104207034903000c03405a0f030003 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 236368435 1250 236367185 236367203
    0x2030c1207141b011e021e03010b1204020123072d0b090312011701050903070b0103030e010c05011409010c050406020a110a15080a0c0e0d260d0207 65
    0x280103080d2180c52206003041141e4104103c0140c040c2500d40240e001d101c2841c0000490841103030071224410104603060005a4000071003688001816075003485c1d060308590740d05e01e15494501100c1080c4102168043c0590070680007809680c040c4d01d0000d09202c02440c1800131100c1201c844155610682c2e044030358425141012111004c0d80d6007220380ea540042044144222507225614900002411103900e0301c404c1262038840134030900414001c1c00030a5101d0304c0080c3c42c0c040386003940e200170049800c40e0300c18000c101c081410440311504490301400e2001d0401c1c50900100d4030402d40c0d0502601ca9820204210b0102a038400c51904c6081854001c01983e40060740841d2740b44520b101e1100180e000c0b01510012400d0b80c0c083c0320801e8401810400055528a9a8202d03000c080c802c00010030900c404000d0345402c18003602c80351010341e107022500c1001c407000240380c00c0003060003d0101985605984034074401d41855445210010b49102d485e46074030700c0200c001c0d50201e0000c8030b610b00 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 236369685 1250 236368435 236368441
    0xc0303040f090c090b0d09080903010c080609070203130308180a030b040201020c0109051305061804030f18030c060f0c141f090b180102040f0f030b0702060105060a18080102030c12 79
    0x1101382001402e5402c001c82d2145031100d88200d01c0003406440005491500d400c011060b0140d809124440071202640c8800189280c110104100c1000003410304040d504104045149180100140c030280c0c1c0c0c2c01005c682d210f0003000c030442d04880300103e030b16800c03c000290101c180400d000015103d2131003642212410400c5400458032142d8900c60950818481d409003920309020342c211030360100b4041d181c50340303110641c0304580c0074400964040e40400c05120303242c03105560007100c1055210500d00e4052100380703507554172208000540f01f5501081107160350034482a00c01d880c10782800d034004c4a401303412442c900c030b46078952103444862501d1410214400d4a140c1642c0141500b003600503070051d00990b9522917520032061035109501c03455500b040085907000b900f01a00028004d003000c000c2c0b965085152504040101404410655001c000100070b55502c134011a00022414071309030f800700d00101d40d407404110a5820800c3c80d0350010040009a4100340040c0100000f02c2c108814691 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 236370935 1250 236369685 236369687
    0x7030b010305013b0c0604320f12100903030b011101060f1505070b07050d0f0207170c03040f0905040c050d030807030b0a030b07030c08090c01050d05090c0303040f090c 74
    0x80c2c1c02011105050508070320070400c0c04d010341d018030380701c200110a81d80302208403000514294481d40224064035412080b103444602065041d41030345030741c542d03a8015840e0380800141c03491108482640708558a0032800341d0290b0038801001d042c99100ba00340081c040c0c514010b40940000c06038170340000c1d05c00c1d0010840020500581c42240c80c10340c0000000e0b42402081240303105174859100a021040042c140007500426010b4452012661401d460f82e10782100002503a5000842110082c014004400400d20658400a950300140000b0f55a121801c0b0700c5420750003154401512000d440f00002102c072001c3c0c0041d44101d00c030303440f405083c40d1540100405610001e0018001071391180001e08814000e038041e03c0c0d4550700600d80111581d480e034458688220417500000020f40740c0384424500f41d00110400c1d00300d003007080a04000030000b00001c281e401094003002e002501e80c4040340e591142401040780007070024082e60380c1c40d5201c41c0030032030042c1c0510618035440c0c500601c00c0101 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 236372185 1250 236370935 236370971
    0x702070b0418020415030515060414010e0f0607050a0b070203030103050318010210060306151a0a0c11090106090f0b03070507081e0307030b090c0406050703180807030b01030501 78
    0x140300c440c2011410141072895005014444500607018560308010104000102c00c024062240c6582e0b4040782d589402e10150030301c0c0b4200201c5500580052106002d42180c131402103c0c00c100c01c0c07a0208040002c14002500c00310303070002840c0c200c10005800001e110b170206201c90014054a02d884030394403000000c0341e80744400d100281107500305000021102c200c09051503201d050520440b00ca8410707a2901c8821a030003680121030080c4e030750072a0040c0072894108a0004c0c6850b803852290095010010b203401d101d100003031000c2010f104c50710001c004c001c0c1490200350101800c8060b0940e12104060b00000950068403150b1f5855000040c0d5840c070130007201e00c80c1e00950b03101c60800c095980c03141c899810800400c0d05031801e500308046e140050402a62040342c4940d004a00300240d50b040c0400c01d04040c0140c044404200400d102c0d40b90420100c4030001c2d070624150350085842e8101071100221500300320340130301403c0d000005010441422038180c0740507400800c0070342c00c0d01e4404000 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 236373435 1250 236372185 236372189
    0xf090605130302071d16090b0301090203160f080a0902060c10020c0f030304030207030b0415050702010209010f0513051c0f061506110d1d061606061203080c18040509070509070207 79
    0x2117010fa6800074071100040c800100000c0140c2c20716004c815181d60180101d1f420980140b003540307034080200f00400080d202d10110004113401e00c10198401c0f040300400d0440c00519550404e40c580b4030b902d0464a039041150911404601680d00d021f24a4681c0c4000e0351104812030424842d10541c40c0007031402008aa0041d0740c150020840640303141e8526502d0304000700192030624840014070050000c0c1d00070240f2440c201e5000503070720b000c1c500000d000c41080313903000c90800000340015068110703500d810070203032003044078440c620f0b6900400c2c00766000d074a4800145000140c0c48800100a0250007210902c40400004190941c0b9240111080d81c001a2900c01035400a40200540f50007000c0041100072010718100c4135142010102d004c03a0311241c04030342526450250401401018450f90002e08041103429024012545009003107541c080d141040e040c0c00080d680e004103002543c0302000c4a0058018456440d0600c01191070b016203224060056445000103001c080c408604c1c482 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 236374685 1250 236373435 236373479
    0x20406030b09090a03030507030e0d110609033c040902030f0105040203060f12010605041107020907030507020a0602090613030305030603121903020309120708030702010b0109180f09060513030207 86
    0x142d004c820351022030107403901406890600d40d41c1c4100e45141ea006010f000c15685454841d50752080059280528010b002001d085440c1c1050000080072030340c240c0c58041e0004407514a0001c2240c1c0a804001c00380044170040c40f50304006000218032016401a40c421400e00c0e98901e416a030389c00900c020ba1108580182c4d1000b43d0200c0d440d0b16203091700803144003580d107100028442ea00e46021404881a140c95240a0b1801241980452a00c045001c0d4130140c1458148982c0c10403180196840070244002058181c02181003583e0b91103120907101902e040143c520201640d0381005810b0394819903005000713004104000c035032044060116084082603480c450900c1c140d481d0103e009400c00751500303201c0c0c0032f007842c0100140d04441c090490700340500403242d41d078104a4006800c50740c220b00900d040c0051510b080009181081e155071480240505c0441e1140303000000744010300d0750100062061f89005c05000c1000c50006848580a11940032508a00d840760315107803600b80c3c1020480 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 236375935 1250 236374685 236374693
    0x290702010e090a060305070f051513050d06150e070e012f0a0807140d02070e01030b041529090c0f0c07080f1c0e0d08090f04020706020406030b0909 65
    0x100d0600b020a441ca510011020001414030740701e9071024209091030b80130118207101c1201c00e01c03940c540900d140100c4020304c200a4542440f008403001d6a22403403007007900c00c4907001120010b1010542280c02010140824411000d480304500d500c0520103998045c006502d001d98140b855021748104a26017103844c2104201071400c0c080d0300105034840401246a0148090700c4d070000d00a14050012113102e4844000c0b5250031184440c034150304031000804542c070500c8104842d00350340500741d0650b0b40251a11a95030380b20b0414254000c1c03c8281409403070310f80f642091044e04c1c2c1c5050001104104ca0140c0b910408070001c00002d01829680c00c1d440c0351080000c6070803a40000c0c001c00c0c034004c441044d200d0701036592076154201903810071602a56002041c90b06400702c070460806181110742d045c0310440d1190360011890a002c19500200322410004806807140d94107030140c1c0a040c070060040d51b5a9019142c40c00294020744510000300303080403000380c05490020f08152040500d50020 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 236377185 1250 236375935 236375957
    0x1f08010917130e1306060308181c060b011b030e091006051606090503030c0d05010e0c09090402210f060a0509100507210b030c0103112a0729070201 65
    0x9203821943c050001002d1050400c50000095080d00a010065006880d0503488111205200743c0c1c5806004030350f8424600c46002104180d21492107412198104000151490301000180e0b00440c1812560140d407000300703030030000c05034846015098060306450152182d250503600100061a5018034004160144501a1240c0c0d07072803c0103035501e00982010881500b56144c070340c1035034030590f0145050000046c400c40800018002c20b401080b00800e02d107418074003c010a41c0301e008003060103101c1d090389404101550746050076130a0f04035030388420040d11680284025640d2018900071603181c0150320000350349520a200e01482a504d44018044001418100c03400a00f0010000c0041c80302901010021100c0e1429480e89001100760028104008004041c501f4024402d440e0405003048108101c0002420541d581d10301c600d900c06220030460081d4500000f501c1c40240c40301e2140c21400507d0385130b4060010100c00b003103020441039120054040d5450710030044040d0200c2c0c218608 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 236378435 1250 236377185 236377199
    0xa0504060f5106030b06180d02040608010e0102070201020f0c030606090406021201060906021b012106031b03170f120c07050f1f14010e1f0801091713 66
    0x160b001c00300d110000c104000641c0d000644540140000c4001903080a09011458040c443c6403410034040301d0940c2800003240e0f1941c1d12145000f001402a02203004070710841d10b0b00e8200c4409800f054009000e01c00349840700c14001c1d00020001d134010701c20f0b80748903d910400071403004183d50000d0040c0880e07651b04001d0025803000a0011164694200600d006a0700720030a0180070302807035503d05e800c2c0d51600400070710b480100a041c4a109000300c990f43c0e80750780c1141c014214803110803e020030740c0c0d006a000c54000e154542c0301a00c480d44501516407070080c1801140d09803441a0829820b07188080381e030010328007441320034000c9005d007044442403400000d052150303c240042107a52a11003159961811f0082c1100000100c0d84250070000f01e6400c2e00d074200c14403840000c1c0420994449984042000700188102c481138a07102c0045444401255406007032114000c001c45140c0e5510a50180200941441691082284000000303060025400c66642e0814180c7c0c00b000036042c860 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 236379685 1250 236378435 236378501
    0x2d0a050702070e0c04170c1e060d060909140f060403030213030503120103061a0109090b010c080309070305120309100c02030c0706110606030304120314120a0504060f 73
    0x210305000d500c20703030b180002c1c00c0082440030b61060080810540d2a1440d00c10800c109510300b49104803035410400f494200e54592940903070760042c403420040a28400e55002c0741c80c900c240c50400303040c2400c5c030201007082103154100d2402a8403540d8203503800c40c0001e040341d4450300c9120301a00c95400c20404280480d100c0c1d00600301c0f412104580051160f80c0740d84052035640a5186518a03c00041c01002404668031401c3c4900d610107025003010b88165000130150a041d00901000c50740e100c4586680f82d01c1403040032070031544805910b5590502492143d41e480c114403080700c103446415070008003d0045026a0701941000000b0034004130580c090401030605115002d04500c414000e14028030b00c108110402003110b52a003a40c00e0ba1a400075070704040006150070300960040104005810000300c20390b2041c1d40500d00307225008102d01e5040403d00c111842c0c0c1490f002c2c00700c14001c140c2c1e5103a01c058006ca200d40f004001a007040200941950400581018440800b4403205011103000c1 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 236380935 1250 236379685 236379691
    0x6010315050a110403110f040c0212130e100f090b0a030f032102040305060105091605130302060409140a06030c0b18060a1e09080c100c05010906052d0a05 68
    0x20ba03010a82c0b2411241c101c243d500031794026100c0080381d4100c030402e801d04282c8402100c4e070a44050204907070029001c2d641c2d00c032810524001d61030003d8105401c0320192031003405031590b4480703007499080c45021440044003071701461500ba2a42c08c40003407841c006120700101701e0006890075840614580322080d00d000c60302d100360203114250032060280a05039a139071a07048503805005888900b141000b61070035005820084c0242504800d008481c1035040341e200ea00d20007072900aa84203110550b40a2581c0e003548029000742c008900450004519085030040810468401c096980e940c200003050729030701e20014000d42c08820341804000d103240700130b205404034480c0ea482031710b0040300031400381e5100c020904c0000e14222402c0d0807140300030324006512400f9103449030354a4101500d0030740365140c540c41c5912868080c0d8050326014052403045001a400030300811069016090100160100711507903c0300c142c6280c0a054002c8a504520700305038040c1c0d42401c61035690500e5100106005 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 236382185 1250 236380935 236380951
    0x11512020903150114010c02090609060a150503010303031a0a0b09060f070b0a0c110c0f0d14010c020f03180910120807020117070c03140d1118030601031505 69
    0x800079803040d601c0410490141c8003055005610b00d41c501190034041441c01d143d498100030710b02c03032440c015a40c0e40386000c0d0428012a07122071a529000000341440185034405c2821050310b050060000350080040d5040b01d021783c40502c000d010603110303800070b1085a40c80c558130040210f002c3c0714507510f0f507014140580015082c10f142c0102d2400408440e040440c0c1110801c08180030040c0503044e90080c0c0080920741c0c00d280c0d0364030348004042034441e41002541703401107045000304400383e961000b0220f400d40c0c1120703950503110041d400c3c00340a030800f04590400b41c85014050801858000105c070741c0803040c00c14441c0c150b60f81c0c0c0f08004480001600d01082c0700c6410001250691404c50030b075000741d1003040c01a6407401c451002410000c140d040d04003112400300c1c2041500c41d00f08581403142036140c0340100c0130356032061244000740201d110040000b480c1412200541c120540101180042c40180242415404042681e140700074040144000c0004642c3c5050144075085250007000c4 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 236383435 1250 236382185 236382187
    0x70810050627041a1201110f2104030206060f060301050112020c07080114040c0515401802032502030c030d0212091612030c06090c0806090601151202 66
    0x1a401c000380584600e000f10300e5814109028280c4d151410030640d0b6030001d0382030f00a0102020103080006036000700d05180700031075800203400c259100d80c1c1c0190000a0200c842481c200e00703040c00d00a64492f4202d60a5004421990f420156803a240054034103ca0050b0340b11303041240124482c0029412070341a88440d17200301c82022031190f1080c001da616a000c03020080300903140500380900e088025610850192502c8250912080c10303c604544687c040a01064615820000d00c890182503605401400c0c403110b0664400c4101604110402c0301c003201900c0040c004542c54600c200c0c0700036924500141c1c1d401d494040302008141030700b081b151084c01924105406001401d0540d8403040340081003550001d456650034003031411454100c0482c80042c07401d480b030080700b14000029402030402c80300c00b8908420030144940740035402c642d03104a00340001c424038581a03441d41928060348a4030f018502c00110744080014030b85e41242c6501482151800c0103007016642c44102c0103081c2c0e40d050f0 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 236384685 1250 236383435 236383507
    0xa0b0d090f0209073603061806050f0a0c0e09070e1507050319030e060402090c090a03052b09060f03091406010503010c051809130b0106080708100506 66
    0x140f00c1444501c41e0a25840f254130321040781d42d0408050180c072060300e0045000c0403441c1401440c407401c030001d4070b0b8464000121068001e509038804503480c0c100401e03682c10101008118500100340c54041e14010500340308151800d0800e81e511824030303008a40040403840080c00c442d00c519031580084002410542d802100202001c0256004000644440c1d2002400071404480090f80600c85151441e0030440902000d0310161104d1001d4800f0b0320a407503005c01705031000c1040c421110f42050003094100450740d2403800d1601c0b4140498114600070040c050b0403d1040b030410944042046d40da182490b540c107103007041e6200d031070030b0780c49000f050365801c4c0380d200255065130100c4807090078000a164940c500000c050a45100714904030411000303208912540e00d0740c400f202081c80048440c0c201d10f969070708445c9413452000034083c0100c0000c100000c0d0054001d81c0c12030054410b0b9442200720740d20042c2c182905000c0f8482c80d90032101c00c0202284c014520001400225062140200801 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 236385935 1250 236384685 236384689
    0x230703090f030203070b070504060507150b19050f01181a09041a03060108030a050405060309030d060e01030b01080712060509250e0a05070504060c0302030705010c0e0f0a0b0d090f02 80
    0x2404200c41140582c4c000500141402210007001d6400b80c00d074500320345414100030000b001402100401001c024a0181d2907407128650380220400810182c142215611038400741d03500041248034480c01101e80e20000c041035442080102000008000c40c0c0b070056140c09003000004c2289400045144410300246030196594041d0000280c030307409190104294060803d800c024060b408500c0d10307401000b19550154220741074038122041201c110703440f546e640e50001d0030342c4a0303d10010b01c07461400502180d8182c071207117054140c0703008404079005603803641c0c052a6512000d015507401402500e0954002030481e03081103500010070010f031101c031603200109140c0c0d40900d0071214083c0d03100d11014040d122110030705946c010320015081c000d070309041101030240e1240d40606030401c1035030001305c1d040c503008104072068150301400804c0304034502c410092908882000391845045250349110013482d01c0b51440e4261254080040d180921000f4218024043c030542292284095400e0300301503 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 236387185 1250 236385935 236385953
    0xf12090106091d0c0d030207140d050102070b01081209010e040c050c0f0606040b0109050d02014505040b01080a0216050f0102030a060f0b0d110c01050907030c0923070309 75
    0x803001c003c0019010041c0b880c2c0b1400d080745030404601601021040102080c3d001560400300d0300100c500704804e101c2c800200b01d45905c420806001c0e980002521010028030035841d9040303402c03070020b03a603440381c1c16540c04045100b5030808034000340b0b5681881d030003440c1c01d42c04001707036111a0424a1030844032414090609a250480b01c9144e040b82c010440a81014065180d083c803091824003c2c043c14240041c080c1d03403071240080e04010716145202c046412031940e0203001c8a00402890311420307607519071324440440384006030101018800000701c60500380180324140300143c40b11900b541c1c031400c4400c0290403031100a00004000310003080410410701c0320f40c407030303070800340000d0380d81d28202481d24142c40d1264001c8007070f16502c801c20402d455208041c0e640c0303043c4003800400c03c0e03d5245140d1040f401030380108030183d4a0882405000f481c002185011244601c1c2c0c42e0340000c0d59010484111041100003440b001040c522424481b1083d084140c1c3c0407505042c005400c4409884500b02 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 236388435 1250 236387185 236387201
    0x302120706020105011d0a02090117090106060e010c0515090c0a03031205100b1801030609231b0a03110d05130b060a060c02120111030c0a12020f1209010609 69
    0x8240c0000c0818803010340c0c280200d80c05080c0c00003e03240011040000c6804040b0014100d02d071040e4046503070750700c81c1c4c441d40d88071000c489400e0300c40320a418500003550082c041c6124000110341ba80c1c1c0754043c954001e0070340c2c03003a503a001b401034290303405404044030714503030000c0c4030080501600d00002800d03612014502d0203540a0381d0365071400015508010b08490010b40340240803050203030104051552a41201c134001000c2c5414620009403d005070b01604854200880c41c85c10b2000710350802e0000c0f0102074044020b810301c031155403200f0702c4544004059403c100101c0400f0081144118000c0d08082c1e8280128030a86207048880325100307080301c0f001c1d00d00b0b80f4860385440024003803004507006503811510071540a50214501040500580c0b101035000380102c0780b11480d01040c0000303610100d4030003007c0d4031640d0b80c0e251030070056525502a20303115002c02c0c01c00c0c4501e02d041c0d040380b081d1040796a01c81e216a05d0000f01410140c1c4405008080c00f0307056486050100703800c0f20364010511 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 236389685 1250 236388435 236388469
    0xf100c02090a020a0e0d05031611040906140703330803040e0601140c0a030c24020d06060c0507030212030c19030e03061b0a020a02090c070501050c072a0302 69
    0x380310075084000420303c103171042c000c6120b42d0041c05410702203013011044598415403000714102d5141c540c0740c029100c5010340290f82d402490b01c00d0701c00500c03c0c2900b0401c03405410b030010103c1c42e50f5048080c0c003240d280e0035030454105420f042102400c0d1344040f0840d10916031000e035078000e0f0790360480640307958065007108070404605018411a942c0000700301c404081480c00541c00c02d40c038a03600f281d0b1001340c1c2d00081c08019000c00500d06000078030004180101e8000c000c0d09c103407003005050001030745c80030464078200e40c070700a000600d16202e40d80301c501070356004001e8540c113403440c0c003041a80203417000040ca46010070811000f20390b1003007106081d040c0800903404240e440074103010388401c44c10080c4500941150003000040c111100b003a2140c00321580c0ca554440d04140704c00c903d04581010000c0d003140b50b84003440300da491104054952a8490030007404543c2e142040000315021710580100b000c3c0741e181e142807a06d00e0381640400c96240a0062010b4650f80c0e800040b810703403122000c19 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 236390935 1250 236389685 236389687
    0xc0109110306092103041e0308190b01140a1e231c1d010c050c010b060405060a120b0901090504030324050112020f030c0301090e0c0f100c02090a02 65
    0x354600701440000d50081200e0701a054034100b0440b060101040c65640403c4144000001420065000407620b2221078641d060340301c1f41071070702d0041d0010009076003182c0d00c250310f23040c00401441c680c00341e09a8520182c3d40c1d00c101c0740610590f40b2091700000107000a020850465400742c8080100c9a01c2c49583c6a071b500b084a4940000e480010b840c10b03803c5110744504001c0300c15190841c000703000c03040109640c0081c016000030b44c40204180400d40045080d42840b0900c850954050090900ea400c031030b000700b01e12050b001c2081410b1146114464004009104d14013407140079407801c5450107420302c0c000c2080ca040700300081c200f101c241c201c1d4054981c3c420030f0000741a07052248107408044000c0d40c4074001125090110882400e00c50641040401c50030382100c10f031240c040d114445416404951a81840c65074100c0c2500240680c104041c40c00701c0c2c0321007590300082c0101f00740c0300103841109071240d000140030034020960030900a10580003030315801a2509145280706812042d401 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 236392185 1250 236390935 236390963
    0xb2103070605060a060c080706091e110307080c0120010c110105070212040b0c031309141006080402060904091203060f0503070b03010e1801090f0605180a06110c0109 73
    0x7502140c0303024250318002d45802005220043d0412601112141c03c401741944452070303458080003803c0000c1000301116055a0781104220320700001c0c0e48a00c0c4101c032145105204c48081c542c2d918060301c910821b40c3d0041010b003800e94028035066826480d15000da54074000e8051074107082d10780c91b800302c2000802003403154250980c00c2c4500c0c0c0d08042c1e43e00c060000c0c0541041f0000700350041d401514034a2030b000840000c010f4041040340c00c1c2007255461103158503a00d0784050000c040e2072020f400d1412130800010f103600d0700943c40c0402d0f2056600d601c050341d1255001e11605400248409411039601c0010002040c00c0d81105950682159070109120382001c02c45003070318070a5403026000c2d5016107030030311518690030207036411344000b00b10f07001080e071b5005c0f902250200924091459940f0b82049502032103200060030001d207014180c01d002c141c0300c5001c07401718507000302c0b008003042c0c00c2025000002250340c3c00c403241c3c2d107254800c22400c14205071006400c45210744001c0359161000d181c0 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 236393435 1250 236392185 236392193
    0x403120203030f060f01080a0507091a0a0f0801120318091d0d090b1b1e01051005011407060f0b0a0f0315270503130801020901020601081f0b210307 65
    0xa03c1e50700c2441590481100712103400040d2021a025298900745911070001a4010740b2807400c0ea001131041948100141c0c00b1144048440e50042d107a8000186403040208407035402041000e0484401040c00d882c0f2110548044804000300729844d580703000e09010008104031280a0306a1107810401c2c132400d4940c44080c801e00c0e00c0c2c1c40c10300b145c007030102d00c081c00c02c030120451007034605c0c007628440e201410709244502c15060122002c1d9070401c1182c0314407040c4105905511003803244403200390b9044015140d600560310140742c0411014140c1c810420702e00050040d41096184a484000108010398403400052804c44160400030103182040d03420000d0240a07915042d045c1000401040501440c1c4954400c1d5041c0c1c461043d45407030503210794005c001042085034801105050840d0750310381c403426114040c0d449604982d005103c1c03200086216040411f080c1d29882c601201f80c04808480d0350780340040e0408200c00c6078030030780e0000940207002c1140701d50b415220001e4007440d51800309143c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 236394685 1250 236393435 236393461
    0xc17091003150e060d05010204060f02010c031103130c0e2e06050708280309330c0c08040b030402010f03020306300708010c200d0c0503040312020303 66
    0x5641050b04100052400c5521060b90006031014240e440d030040e5a22804a02a108000c4009040d92310000d0001403850f8050060003000001798001c1c8502c40c1c11283c11415030351000da16440440d0108007251030810202c0380c5005503440740403010b0540e41d90301c05410400c4d0341180d06900f50704295944d03600c0c2c115401d50b034004281380e440070b0560a90401c18020a54001d51100611a010000c3e40b6025001d6001d003840003541c1c0c4081141c0c030805808002005440d01c04400c03201c868000a090700d180c10841104030419000711086a007401042241f1f03005001c1500002090000303040b5444085000d0500403c00b0b4910360040300d03541c2c10288001051000300540d0101014418414009190703580c2e03070000120b000405103602031030083c0b10510f1004142150b00c01c054401c804000a0158041d0020303140e1140c00d40301d440207540e00c049840320390391a0512100d035540203100c1075911580a95140b4042d10701840c110b0781040c0d1039590340140b82c5800384417039001da80040100030496105003 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 236395935 1250 236394685 236394709
    0x4050705031203090a02042a0306031a060d02010f0c080c0303070807020d0f030903090504090b06010e040b06030103020d0c05060708030a0b06041d0a0e03040e0103020909010b0102120702010c1709 86
    0xb50028030b1403502c02c1400f40c48402401c8000c0c8100d80301c814011840032400e0420390421502c0d015001402c030a0100a03000700801d00c0221030303d08a404103064600089140c80b881008041c040b1040301d809070780112981100e002c1041c041c0b1102602c60f80114600340c01802000f0588001182c1e6410041005018204010110011588a60401d00b0f90b1790b409080310002c20b8003400c011502c56558a030a07030710070015410a94001c1d1a1415400c01d1140106055000705020388601a0444022081c841540d60554203140c000800b04010030040c00c01040c00710040340107419444080380c46034001503095001c42000d984841d0007006006c04403244c0d1291035a2150221a02071425140c00b00001c2c0810300e00b41220f4002210000054191036280c1052100200b01c1041c0c1c0e81e00d68944001c1d0384a1002030000381d01401c1c2400024000490520031404c0c80c0e40141c001342441840305018401e039038803c0300d040741048100b400507000140c40b204c0c3d0440f5640c201852030740302c646800522400400003 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 236397185 1250 236395935 236395963
    0xe010e01090b0907060f0311041505070c060f05070f15151703090a090f0e0f03040905011a07120c0206031015020604110607030207050d0b01030b0a020711270405070503 74
    0x50303402005015004010010028491f0030045150b2059603115050380c080c540c00520b41c40a0b0454107074007142c0c0400100f98103031080704c408030a10345803002201c403825001d80c0d04000c03400c10041400801c0303c8055550385148a008840c9505050311680400c1c1c604070300502c100015122400c1c45500400d001c6c40e449010620700035400c1004440000c0c440e030481d031003a00c83da80d80e103090210036400303240c000c001c10301d00400458000000316003e0540d80c2c2e106105200d4900d15060000c0b031032030f94001007507511152030f01d090380c2407084a03114080c07090031515a000034010750703809000060b2210406544110320312071004845529200711003100600800e03070003046411087c20080000d0310008805001d42d03003541d0312521000d00e0314050f450300880d600031942c001e5051384194100006442c0550613240305000e529503a841e070031030460507401840001400004984002c3c001e5080000d41c2c0320900100480800344698075100c003900d064800e4509440c5504000c100f4001400e04015024421000d = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 236398435 1250 236397185 236397193
    0x160b0117190803061c15060506040b0a0e0a171006060c020306041101090e0a0c11070303080a05040303020904050420030f06180a1e110603010501120f0e010e01090b09 73
    0x71955020440d07026010000300140004004200d0340e03120703400c00b102c030340e40100c10450b090521810f108811881e410312109030181007081c0400d403401c000058900705c500c01c418050900d40d444500360380d0042840703030950b080070700b151300055003007000d40314800b1401d8000090000c200101400d01d047e525580c200a081c84002440344005850001d25694400c0d00704411282c42290000100c03000c000303d501814088900c541449a821f240f0352011260001580b2a107401c4070740c00e109075486490508c80600031400320400242410003607044550b0080c8681790061810701d49900080403039006540136a03803002011600440382480b00f50b1020040300440c010701c09804c1d0071088960300c0100400d2006602443c585000c00e909007040280030059003d480701010040752203808010945805081d6001d2001119620060412000b100d0507280103940312100c0b9141c01d0080700c080c100d8000f0048105607244419030103074400b0b01c41d240f60342c2c8413040082922511401d0420000c28054440f03000c07900 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 236399685 1250 236398435 236398453
    0xe091003110f010504091e141e0916060203070614060d0809030a08120906010504020a170601200307020906062505070906060807021c0e15160b0117 65
    0x14286840d4010300302181e451074040c1c20b460040b602c500459009105090418030401210b8004245641081c402c0d03582c200900020840c03100040d2200751810b00f0484d200340c3c4040c1d0414854500283d000c403040c012141c580692101c2c803042d42005a10110060f0004942035040141d5406a1004a801404002e0141c1003010010f48460310400c8000c00710000004c0b4038034142c600b80310806009802840356a200d40c030000c0824a0b4080864001082e402040000700d182d1506109503020b040c010341d075001300d01c40c1c00503410b000c50340080d00c403d05111599135005074202581c4503450074042d8900107183c48400c184180100c0132406445603114a506100c9900c817090740c034081e2004e10741c00d107880d24030141060500c141441800d8010203075280c14210042034554100c1b4000d4081c614507400c4030035000c80c2d00c1524204040040311000015500800d034249458a1001200c9070308801000d285000c251154105521886100488a90780c0b06001009104c2c00d1800c00603a103505440900740e813403 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 236400935 1250 236399685 236399693
    0x50d020715030902010c060204030803070807052a0a0212030406021b0d0f170309010c1704170c10050a090501060503151b12070809010c020a02060403081e030103030e091003 76
    0x146042400000b0556144448819a803081c0d24034100c03250044011580d071516404c020400d544200c2d0b5440c0071800000225510600c1881110002d001803088405410401400c082d103020b98030040384d0080c072070303a003500d40565290702540440310031800c01036a0700c0d40b0f40200a81404110801c0d0f03001c140107860a52159100e041c124613816501840d0803100904030f01d480c0c281f034071000e01c950000140100400c01080015403041d0300d5401c081d100d50807119040c40d084400f0320412103008141c81080103200300c0b111382e02000342c440c40360000c040d225075148070b0042000310b950854a150101c4d8841c0c9d110014041c0030311801e0b002c0c00341540603101400a038000c10040c96000b80580351150500130b68201044a40d00c281c07005541840390840060401a00081c2081d0055481255551900500c40a9a4000129210f072a40c1c058000e03401e051441d20341229580000d0101903c5000d180d90031921300a08900450113580b00b5100e180505400509000c3c00d468000c2c81c0c0070785141d03100da081c4086 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 236402185 1250 236400935 236400959
    0x12030504050f03040e15010302040b0a030e1b030c1509030307050a150203070f0806040204030f110a08030a0e0f040f0606050703080106030b0d0206070c0b0a0309110d0327080a0807050d0207 83
    0x101800082e9806d2414080120000d2141e81c0c44070013001800f04825641c42d50541054600d0410b5074102c0f8024200250800100320511948680c075074842c01e442041e0b41440c2645841142c510714410f420580d0050200e401e561042000320340c00e401c406450420005040c60b0780c140c2c0c40c42880114110f180010002e4141c01072034491000740000500040c0141d83d507601103030080d6a01040301e200c002c00341c0c40c000810400001c5120310414030940045040b0a0020980311003940316a81c0e0300450980509000ca01c100c0c1c1380003035410644801030840c1210403401084000c2c18190713211a82c50405040c0104901d0068006000301810a5031419039a680d44a44100450f01121009da0b100c80c0f030701d881d55045c2e05503480406041808140c181030503070981e1140007000d000710713500410346008104010648080d81c4005020450a20504441c013920b82c041505212015544403080d0703403120708051a0410503c000c4071580c5002945008100041c88400c07410b02d4a0300003001040e0901d6408921 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 236403435 1250 236402185 236402191
    0x605010e0907121b060504051201150b09010e120c010216030302060402010e060d0c050901030f02211008011b090512060109050907091506020c10080f060d12030504050f03040e 77
    0x3c903802407010101440407650071400180841812411901e0b41c039580a800d580152141d40d00c15205414003e20301c40b0107000790041c4c0049621002040c80c00d1441901690300124549410045c3e01e0701e149002d601d4200400c5007000101c2c0c0184581541d19000902d0300307000e4510740800100b0820104002900005d9213500145e090a104038800e5440d400300d01c0600900318508080c9040071904041181c01100400200b9002c1c2da0038000080900c0b0821706921590b540c541c504095400401c940341c920346e03c81a00412580e012040c0540e8176411b050a4800039400c801c0c60600d0015607034000d503042a540d90040009a44021702c89110000b481c3d1115014410551213a0300e5400094180c5d0050040801034418094200120001038007680403910341401014094440c04a80c0d0703100e86081401e00000c0200d580d241201c565898804c8002a90042c0c21b19800240100146000070159030701100ca09003581d800040f90314190038200d2900f6402185011650410071090129148010f01d0f154 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 236404685 1250 236403435 236403449
    0x3061d0f0616090b0f18030a0b010e070504031a060402040b0c01060603051e042a06020312090f030417071203030506040c0503011211030a050604230d0c0f0318120605010e0907 77
    0x10b02d54a88011041c00c0e041181c6c40c0c542c3c1801603442d19001c000410042c64183c40c07125940146954030400706441a1199000107005000724516180300c042001e00341d0303980440050009800c00e6540c0624802a03000b20b5900000380c0d443d16800d2020301e40c10b22a00ea4000469080e0011502c1d070b110b00c000c51090003800142c07c8201c1e00000d80604e01d201400a9206c41c01c14024a082c00d9560300001d4503508030320825841091004081103060500140d84038074262200c0185107802c1c503000e100326980f150310f5116074407070040340800a800c0a1040d80034040c82c0c042d07200802c00e0f1800da0304000484d0091002e44041c040c0030310060002c0d4035102c09040c1c6095015142c181d24840d8040003034608030b41500010607074840e071300070002001540900070141181d0340e000884100d50000c1d0650710342d0180d64010b00010703001504040410f0790720000c4401c0c14080e003000000c144034080089201c40e03071a00040c3da800c6507014404104842882014010401925020900d0070807840180c1c5070032892007050 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 236405935 1250 236404685 236404687
    0x14030a020d0b0604060c170a0207060503100b2b090302030a0302070203071208130905010e07081f030503040f0e0c030402061b0f010f050c120103061d0f0616090b0f 72
    0x18101d58042d4044100c0b018010442c40d1030359601c0d2002414001203800c215800c644217000c01115000c4241900c2c448141a00a8010700307042c600201c0b100d0704010301d4a204078080010015011b00301e44000c05182c00c66a0200340405040d002e403140800c072440c1c00c81d0302145010741c01c0000c81c5e80481510389c21840d520f80540d680c00c040c00000d00d0102180c000301c068410650141e02044079040090580805160b4425030440d55959100110b407400d215400d514241d400015038024810761f62158401c003001115141080c413440b1000c41407034603410440c0c00ea0310004003485110301c800c01040c0200541d00c0c1540f41454001410a41d90202900013806004045890212a00020304084412844000b00c404041d806090f070340c060709104400c1328076245800f02003003c4041a100702c403400c051032049060240d1950303a03550010310444485814a000319444420010002c0c00740d103012582d407100401d002c1c10001002c0c14141d0201c01a08180948000d08024102150040c0e40c60300d01404041 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 236407185 1250 236405935 236405947
    0x402190909031e2001141302150c07030201030f23040203010e0f0c0f011e0801090b1804151b03021305030d0c11030a0215070302010e0105101a090301290114030a02 72
    0x1c80c01b6200708004003100480b04000c0080c60b80040740380c188068000c031490883c1824449110025105032282d101840c0c100703402c02d10141d4060781058550001030b80000410044401c03602e084130161811102e4003110b10340a100952400b40034810315601880083c005032403228014070764a81c4560041405680400b45400d0b42d80c0c019103854089c0040d0b20211314803050390380e50052104609002d04000c1a29000c0782c442207040c003c01c10f05007000511003041d0640c96a4031960f582800200fa2050040d40300c2100c2161500500048214485151000350b1540a5126030021215090b00480c0c0a40d01c00142d0315000c2d54046203070484590041c90800d0443c0d44500841e06120200318081c0d00302c400c00d603841e82040403090007006500c0c0a940200003e5040352842d900380c0300d003076403410494890b0500c24826001349400007070380503100c0d0708a0351070130000c00c010070f0950301c0d441d415801d51724844844002c203c2c032008410000301002d191003580c11a00c805d400300c2901010300349601260340840d40b = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 236408435 1250 236407185 236407247
    0x10506033f070b1303020115050f011b080a0f030501090e061603020c01110403020f01020a030e10120f0903081308031504020d110301090c0504080a08030402190909031e 74
    0xc860782541c00c420300498a282c82070007075012213074000c0704074010361800c0445080801c0501c100400e40da030007803a009480a0344801164101031680c2c84c032035031900035804c0e03000044d404001403040e82c905840d091844c1c05507003801780458105a100034481030803d00712645501001c2211503100e15220540048449030010460090083c0c65541c4080d40c40c0944000d0f21600390000341c01140c0c800c44035401c12102c01801240c451041a10003004510807580c5034245140414424241404920301200c0b4820107049540c1603520080e603145656a6a00c9140c0501d980054001e900c603803d0072813014128103d0303440d01102d10008054608030049250582d5042da1640c0407100c5699418005100b0144001140800740d4030a10480094900c0c2140c050b2030140240143c804813905d0780d001c5c001000c0192604802540020400c03a48500f0103c181c80c0400403403440c00020b440101c40010b9080900e00d005402c0030321542c0c0e10a0130b000c01c006032404103680841d80d509240d1889084480b02092a02c0e = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 236409685 1250 236408435 236408437
    0x1050a021e070e09010c0206070e030114151f0c02040203100e041b06020a1e08070c090b0f04050c180316060206190207030f050a1b0302010506033f 65
    0x60090300c0394200700003110140100080120940305803651101c03240e103502d80c0041c201d034580c000a001503004030000510f010b00840c0500c011b00030250001c90140074100c1c0300109803008a480d01407005183e284520a414428292200141c80700c0c40300f0751031126800041c21585504400a00c03c980000005040e028681003081c0144030486020019040515007807075943e0070049540c1c210402d100c000102c2c84c1c800924000d5042d00003001b15080d5410200030403140e600d0780016114100300300003480000f140b020b006401802202000241c584140c0e042040c1104a020560710640c28202801240c0318140c0440380210400c4950007801c14680d8003090900004100315510042003100009800d600400c103688030f03020090b0504402c212021815007280644074001d000035042c3e0010f0801580520020a180304040c00c0c80321400842c03843d0411079610300351080300142d440704c045c442e40e0701341004061508440a00f201c45008614240300d04a04208a981e41c50280c1d090310800451425078 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 236410935 1250 236409685 236409703
    0x402060d020313050d030b1305040602090a030c060215060f0405100b0a26090706050f0d0204030303020d05060901050f041a030105090f060c1306030c111015170c01050a02 75
    0x80340c00c0d0b44901e41103041c0714510010700c2094907140116000f01c01d000744a031042401c0458001c00100c02c1240c0d05075004000c2900600c00c4500503420080401556510f48881000390322a6034589004d0f810701c00003d081c103011102d08108400d18505020140d82c0301c002045c03200c4d0043d83d002550799245040c024080741c02d58400c5600e142d00040c24201d4545c822803104000e1943c10050a01d010404868040c50504958000564004040138406207205100030a20488080e58030341c00c000003140c0020807a4402da000f2000b00e5030024240102d85114010b00381d000e20f08555038200366244c44046152040581034242c07080303684000c80340c2c40343c421842c10b10584401900800282c41d10340b05469480070615201c0c616441028005018120304504455007a2200e21320501d0345031514605a000d0503490700a1b030240000c449451011000c10401042c0001c080100803030050b10741311009814421075044000c1840c2104140c91002100180c0036907207907020710740140d82d2614100d0403070400400c4 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 236412185 1250 236410935 236410957
    0x8060f122a0312030906040f0f080a08100905100501050309070b12340c020d0203030d061401090e04290f090d030e1518030a08100b0c15040206 63
    0x9a00700c0d100d00e03000c4004100c2100e00c142c0440e00307440c140400e441075500080711000ca844c0d00c10400900081c400c41e4903c00100d00c24840c071280b01e48180c0c0e07805c031705402c542051000100c112082142080d80d1a03c4400201461303038080006081c42d181c04018140280102414001c000004c03d421050402c8000c004052800205442e480d0b4060802042c0d10b0a88414040c0c04180e1146d6581d401d40c0d400a400752075159081400f4402100410723a407441c00e40c8020790744041c1c4040c290307000d40c40030f00c014101016200000503c00c4d040801806026082104550420401042c203019202c504103041c0c0e0070540001d40c1c0c91184a190030900c4442c1601c001030f41362034640788103100003007034807104803400b40e00000d007500c401101c2040110708898023000d810441d07920044c90301d60700c11201c1031155003081d00d071040e1148030916410003919592024103044005540e2000300806004000000c1c2c2c00744c0310718071a8629000c481e070403207541c400203080c4610b04401c503240807900710740d659000c4410401d22 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 236413435 1250 236412185 236412223
    0x90709090603110907020105010b18010c170901080c0309120d02091c050d0c080414010c120e01090504060305060708090a050a20120607030e0a1407050a0608060f12 72
    0x42c1c0c0740408640044101c45070045036130701d01045c281070040c01071074180c0d609070283c00d0624007c0f4011002c40000034075568107002d030103841400895004a56a000640300340e03600c80e0380b00240400105051002445400d200c0c50a10500c8400c04002c1807a44e5a40700b4221004d440e400c40710200340007441840901b0798003051844112540d03104001c0c05580e054041c9042d01c140c02d060100503200310208040040441d2070070002400021500881109028010b00d0040c000ca25581e0726203040b10007000002c40452074044042c49150b9004815a000e01070a46003405074624664451b41d440d04054412010300030550000384002008006401b10240c1210480c2e0740c0311018100000203080020303000440541c4000b4690340d50500c1303040c20305040781074001021560b030341003030442c003c00030b01c08410f140d8001ca0f82101c2c0800d901c400308980c0500e06e840901a0240780104104001c20030340d1140080c040c400c010042c40f55940341c1011445241501c00d100d0011132020036604007200264aa03800d201 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 236414685 1250 236413435 236413439
    0x9020303160c120b0106120203041208070c0605190e01020f071217073f020a03020c070b031e10060513080d0c060e03040302220212040b0f01050a03110907090906 71
    0x100102d103090498065842d031f00b49a1000d0700c4070300c050744011039014225203d004041524a440f6000e80d59112116140054190442c0ea590300160748041c2c0d086400d00070340c0203402040ca5028070405c1e1507040c40e00b00071480c01e2002036140c40359000d45600a042c0500d0100b031042494001ca004040e03804440c848408189813411010744512100484030000c1052642c00c00301820715811030741c80813231103407000c1e151b00032241215102952201b0a15010550240030294480c0700800c901c0f40509007810700f80e072b22858910303801c4510810b042184084080c900c0280b00c40c19060310500b805403182458031690381c06d8116070b07140305a406980890080d1140e1400c520400d60302001c541c402610480b400d0023900c5000c0400b41d0b5074059800b02940c410716004840c542c0304150891492000140c800c05414012a009040054502182e043c2c84c0c83e0b441c41d0030000300a02080c481d602520044900c03000c5941035440d54501106107221441c0100f4481d000b140001d4041c800078001442c913107100b400340c6a = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 236415935 1250 236414685 236414693
    0x705030c15071115151012050f0f0114040213171501080c04020c070302030f0703060b03060f0c030403090e091617030703050d0e06010b0309060a09020303160c12 71
    0x799250038040410000e49000c1040035200d0407001d400040c0040042805111000c1800540a40500b200071500e001012a2102d5110150081a6581c890b05e4100407440c0280001099400003401c01c1115002c400401141d041e503444e141d030550300551249428005500c1c0490020320600400300c0e980303407925000140c02040412146103417002d100a803034a90800fa1072000c41d0120a00447c8079a8018148886941c00d06501070415804030705e04603514613079203802190a06d199080d41d4803003a04150b0052080c030605004100a090058008000901d040710909000c114040c3c0901c1c0e00240010101d810f052190110001526a811a0980f64140b4086040c2c0d100c413500d0906030083d038020300029000c0b24295500345501c1200300076521340000780d03a04443c168081c05519000300c1d500c5079000303008541004118060400342d5071843d0b803428009a25498442d0040800c4d80c4282050161401031b1004400c1da0411315540300c0c2021151004d1802481d840c9944d007103680e184517880140030501c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 236417185 1250 236415935 236415943
    0x3050a17040f1e020603011e0902040b0903070f1206090f0b0109020d14090a0b1e0903031005030a0203150603030706020d020a0908070311010807030b0d051606050703140a050705030c 80
    0xb6100b0040301c0000842c001c14015105010840607601c00c0c1c0a03c0100b2411a403071103200e035020a0b80d83c86d00e562070b803520f400204036049a00800ca510901048056040c01d04114910107024a100e04005561030040c940d01c5159180720024081521640e03110104081c05120f030340c016a0143c1490b882e5a1140002e900030f402c50310300a16854240700c25401c1740d0500451300c60144983c400603020a00180c0c03140c01c00ca030341c007400135410300c4140380314810407086900b10240036031006000785a990a014114160718056900654465000071801c0001a07800003070f45110b000b0400c2c80c1035899030741c4000082c05c50150311806058280001094002040c0075030040100e6520f0341c58040070951115451a600c400601009245070780c00505140d1542c010102240c2c007101a280203d00b803607000c2e01103450444c024808458941c02810155003d04407041c4407400783c41140742c100d09148031034400801f00c0c170260040d20303c034040000342e1400403803042c3d0440b040640c00c2421295110108400c85a031 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 236418435 1250 236417185 236417213
    0xc030c08070c02090f22050601030209060603090d110106050d0c170c010801090b0a12030c0506070f0e040f11070804091b0e010e01200a0308010503030304030c03050a1704 75
    0x460380400208054064500599010340262929001e0780e10348004a0003054098006000303a00c41c00200751141c10ba04141380a403d00c258007900c0035525500c1480000d02010700803d2080030b050041200f0080700094413122449203260034100340b10452f20321070050120b50415608803410214810502c401d42c903840c000c40b1607440c000c480030140a8590780c1c8071114465841d002801c2c9000400610019030000324541e100109200655652104480030603207070560b0450110b50011040400e000050000b244d01084034103002044040000000746a540340c0b280442c400d565586404e09014665449069076401044600b50b443c0302a0821880c150050303c0f9a43d420b60400720481800c0341a0540198801c0d09615600c00d0310943c94010368003000440f01c094100000203214040740c49016060100340c5507520042c14032040302d8140207014660581006001b9801042031200199128501002403a01b51405580740e181c006000c54003074100c0b102c0062800300e40001d02050004601e80208 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 236419685 1250 236418435 236418437
    0x60408010b09060609010903080f0c03030f0a0c090311060a12020409050412030b09010b03040f060507051945180b010201050f0c09040608030c030405010e0307080d0509040204090c030c 81
    0xb0541d48560400003c1e10680790060f0000340a124200000341c902d40103040c0382403840c804c0f1410300c40c034900c840780780da04111121071700d0b0b10244051003080041480340202c8500755160000c2d540e401c5071284003605910004580c06003400041001b440d51086501c901c0c0001214415542c45640d511180c014107020740f416203a484690707100c526020301901c1801050040900486076503841c0c40e08141894000500a440000400b82184c0010b215407080c076100ea40d080d26a151200c1c40d1201a154202041d1440401e0162602440d0001700c3c81d00440702e05000841d800440c2d600545800c110200d144181410203000411408154034044510140b003410581c90100100320002004909981c0203840c0c4000e00080c281c0400d05035646000188011303040030b0000b042d21603403500d103180b460b44013603003400d0b40303400c003080a101d550b81c485055221080100c00508046090544158032101c1c80d1482c0c5091201c00a581300868072590142d03001020510b43c1008200790410020b4003810b04c8800c000 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 236420935 1250 236419685 236419699
    0x90f0406090e190506070c0204020c030a030504261204060b030a120f14090d02031606090e0711060a09050a020907020f0105060102010e0a1b2111010201090206190e060408010b 77
    0x4007404083c5011588241d4104004010f1626140010303548090711a40030390300580c08100200c3c03070000400080c0185011541c1c00507880c90a42400c02e40d2503000c0c42d11191084880402c1081c03015004141c42c40d6003880e003588142d0780c9503031400500805c4484c42d07003038040c01910300060511030341c8420709541403003640340e0b0b084084120300c08490300001980585030a0f501807101c0d08850030045801d5620b54405000c98014000344800b04501500c6039104000290100d0401d02c90102c0401c50190005a14101001c440303040294442d190031005065000a641d0f4030061418441e04204010b5042c0e005081901380d8200540002e4a422030041904255802d00307001c039581354814412010840703021400303042c0241c0c06c0e5480480c0382d0540541e80d1005501c2c3c1c0b80210328480c00004a000180d0a0f85608481807110720300348441205403001603040d645081034013005030702c8003800c0b514809110315461404030b903189000d0350090343d001c500903008a1302190101c2e110714150b10445180808a03108 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 236422185 1250 236420935 236420953
    0xb0a17030301030b1005150c1501290c07060c2108092413060b030601170f031201360e011808191e03090c0e1605090f0406090e 56
    0x80b8011300d45d502c1010b4106c2c9500351044807c100c043c2c003501c940c003a9882690342925188400d5050070b5402e0b0002150501c00e0306164540020317a00116208404540b074007400c00360441c05e400e80744c1a091080c10144407458034000104881100c0d0811184090710300e6040110388100c004201c10001ca410000d80e12901c0d0fa8805c030350312680c081c0700300c0510b401284a03081c0d03162407a5418002101300c0c102d81d2280c072030001d1800c503901480103038081c0c002e00c1008104903a26041c1540380c00358104504c01d003a0400c01c10102c01425400c10700d815601000f0040d50601488801e1490440700b031055450405048001c0101603102a0030050041030440c000b440395081810006528920362200105032480400003100f441c4881107034541d050032903040c0928182c54126482265559948203903000a40d034541c600b08003e9114071b420040e01410701c1410440c9850618043c40200140305c29040c0003011802c2c40f5140e407038943e04184001302a000303000141d65a070700607001c3c0c010b87c40c4002d070a01034a844 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 236423435 1250 236422185 236422201
    0xf0b030708130b070e0301020c06010b030610050c0601120213020a0e030631030309080309030a030c0504050f04091b09051801020c100e0a06020403080a02010608010605030307060b0a17030301030b 86
    0x4003000a410181484898481c140c0503191701840c101440d402d07540a011043c0078000034030030b940c0202a40749680d9502d29000c0100a100c003d044d0104081c800184044080500d00140d228103451000f00505007641c001d0000a54041300c4d0014508614000120f0200303190780140244e039100307004d40c1200c000b61100ba001004402502d2429040001401801d040b00d50703c11031a00c84840c02400e001038207401a0b140c5801c960b108031603103100c9902c001000e600850b454410381c0c400b03e505141060400342004d0010305850940214603203e0350700c0b001e4441c20302000100c0001d64006150100191680d61007120f4041c2c1030461303440d00781d1401c030b03040c00034030040c180222001c2e010528007400003115003107900303c020309803060002118810a0108400a0310902c010700103107004040940e25861000f40013805c0d58041d4010845a90500b08100490346002060b100050b03401034000c100500210f012441c04100f960100904d9102002c0b000114800800190b05032800f51801c00c2540d612103803 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 236424685 1250 236423435 236423461
    0x1b0b13150c0201050d11030705030f0603060105090703020c0f030a0e03060105040507050f0f0f12010503010510060801150c20030d05071505150904030f0e030a050d1103040f0b030708 80
    0x4480c40120351078022040c0190f12407402003d000d43c4081c0c1c00108502115189070107500116011000310310000305005a00e4413560855511040c100c0c0105642d41c14507011820342d000160601090640100700300903ca10248410060f1a1042040b42d8039089050300050070026844141d41c0030b07000311000410303a81003d00805110745020707100c0d01c0c80c2a2152050000c0d5038080c00c0e407680440030522991000c01c550100404c0030440407003d000c0c241d4100400c150854002070810740b00451010410424581c202e402581114030482d50b5107071911442c1ca09944400f10204000e00d8001003a00e00b60a5a00043d8038a5142d4404d404441000f40d580c44103a03098401c9100c06000c085503d1107610040380c85400c42ea6020b910118600c1002d8184c03000b20b0014a01554101c01250680800c44509540190084d210082c11030041c03a00c60616190f15866100200c00d1104100c05c01c0188125000b040040360000d2120b82e141c0b0405550312030490312990401d49916001131008000700c0c40c0154515 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 236425935 1250 236424685 236424719
    0x318010b06070206090a0e130c080d0c02120703082a03041d060103060e1602210304020405070e0a1d0a0b03100b0f0a170d0201090506131b0b13 63
    0x5010207140210b15000c10081d5002102d569500c800564804500e620000024034090122000075198800291811a200c041550001c001c82e40c0116405114603500000417416940c041c0d85030202c102c014928141400003a40029110041c0050100031813648c4950340c0b21140360040182e640d020704005c1c0b01c2d88900c100d1190f40b031450012032801001148240da11a00284141400500507a41e420030801182e8201c038180c100101d2201c298007603035014042c0da40040712078200c08a50440d640c00c0d500320782c000600302031f00859884000030215030181c14600700b0640c0013840700b10807076a10107100c0c41c400300c0540b45400700101d1801140c2c2c4040c1d0b0b030040111480c0004c0140140302ea5142e00c100c000d05c44515019804086803100030b40e1500c4070000036000d00503400c04403604811030003c1609c1c05000d10194002c580c50074884034042100490f4194002046070480300c50482c8a04184890880000d164410410204030004500c40520003e10186061440c80500306036144000903940c8016 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 236427185 1250 236425935 236425939
    0xb0d0b04020a09060f1e320118030f050a08030f040501060b121816080d090e2502010b090a1b02070b190c0b09010c110309010f050a051e0318010b 64
    0x9005c080c084489605026401141c0b8084c2e038040c080c3d03407890303200d2203c40341080f591110440510700800c40d246c40207000203010405c0c00d02c04440407085003500c4001c0c1c407500c0040d049005032980c10003008010f1100c6144107420030b440c03a4a03420181500321801e642903030102ca0540ca07101c000150700f40e0910660700e0700100c2107444003440d5600c502e00c0703010403c2014940b0440c02442c6100c0202403440400300e026103202d00c0106120b001032040036000820343d4010302c01010a41c0200031010240914900049e0340d21054101d1400580005a02400400c0005e642c00b42e811010409159080c0d482240001090590f8170308140250000781d0b00c0e500c0ca80204d107900d940800c800c824010040b135054280550b145000075601e04541c40b1480540400c0da2116816510b074002c568102c0e6000740e00d452200d0444028519064004001034103900e84d030810b260510030003003540c1c10303468029016100c10141c1103003440034180741c02201001c1d5038411140c00c00403582044210007070800510030f9249041e80 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 236428435 1250 236427185 236427209
    0x15060c050f031810030e030702120c0a090f1a0d0201050c100603050312130b070f02030c100f060f06170c0c100b011404060903020609031e0109030e120c01030902040b0d0b04020a0906 80
    0x200d5000c2c030512b00c420481d82ca81c0d030321460603c01c0c1c0300d44508000000500a28070b000950040e03429a59003950f80c06400c003002c400e2020608880c43e030b20400f020150540c242000780e9610b0f060034445041035964903104480d03e00c0c1540020034810302200030300c20011040a04001a990100d6a1006245503600900710140a8000039545405295510210380e10ba00441e401c1040301c42c0c100d403401c0f64810f005454140c95200d64000c4098901620014003005c404000740e8a04141d0000c01c0d2103241551444100d901401054586414404903046448640182c0741b420011000d104080c08460130003d00188a820303a040780082690192000d8801c10390b40ca10b0114699020030081c1e401000e5030541c14041c1490081e56529014001d011416059002245207a030506003e441d00b2084030001c3d008081090102600c40e101052111036483c0900700001c03882c0280c00400c1c018802204010381000f0516041401d2201000c141c0d807280b4030841f594141c05441c2c0c0c004205860b23207031144059070310b1 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 236429685 1250 236428435 236428447
    0x7061103190f020c1902030606010f050a031a1e01080106030501050d0f1401050f070e030601150305190f0b13150513020c070303120e0115060c050f031810030e03 71
    0x4a41108840c2d060b006405400c000c0000c0e0703c1802c2016900782890200d007541044e00031400c0c1403001c60303801071007401c190b08a00d00d04c0001500620904064004242e0f9034a88001000300700c1c0729a4a0144015001030f08810083d500e02d00c0c00d00785d0134103403800f061910000180c0243300b070007210305882e0041c01c240d4100703601e540d0380024a01e90f1b030001c07130307a1b401410031642c20320000f407007000c0c0324007019001600356091061000c1d01908145540302c0c0690004001031112204500b0010846461392600040310b644a0000b8540244201103c0446905100c540702c1c9458542e042150b07601d03411183e400c2e240305103c1c90101110301800344513882c1d20100c1002c1200340b410149c580780502001c0005840d0811128416017480c000b600106c0114001744501c16254900740304580050402e40000c00015910503c1140b01c111030703108810802441110002c00c01805018211010070088101ca0700c4914640c0d49090484108a8941c002c8500380c290240d128401e000b4441070a00703410181d85000 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 236430935 1250 236429685 236429731
    0x150102030405040f0222030b010603290d140610050103060e060f0d05060a0504060f0209030a08090a08010e0c1503040c1e12150b1012021b03070807061103 68
    0x400c44d0701a640c100c9900b80021030451843c0d086550308801013016035580b6608500e0486000501030b00088100340c60480078a203940200c803070000440718158503500b005184000080e070511003a10000b02a002c0e51001168404400586103014240c54501200707065112401141142c0c243c0c0300e0202c20301c1071000496618146a04c11002c140405810854086480d8a42614200080d25130301c04c140c0d60f9604020510000d4800ca0080c0b21204205524140d0400700013a0707905025031010304101800242d448581d550394407510020300e100b038000d00c070800b52501019280c03e440d00c003072405114402c0380d020700d1503401021244119405041803400504081ca0040c44040e0b100540c82c1c0440d44580220f680c0807040c201140c0141b00702c011a070208116681401500c81d102c001c28054011060032020064002821503070020700d0102c0113885030f898103010051b60468611108031804009140c0050129940061429902403a000d12200c14018003070b40700351008843c0c0748901d640300d0405a00d80 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 236432185 1250 236430935 236430941
    0xf010212030703090c0e0402130e0c1011071205060702070b0a08070509090f1e1005060706090c030308010e010b090907030f0603150209120106061e2a05010515010203040504 76
    0x2c03100c00d1400003144255030745c40060100d01c540203003901030740100401c01140f0f4140c8200006002c05c55060003181d0b00b0010712a42d0b010f00d088802d12802c83c400000c44064490943d0018909039a8220f408850382c6020524520001485c207032130340c0c0160400180070030f000048540c01c039182c1030380c1e071403404002900c1219174140203040f00c1c04000703003008058041d55442c01c030035000302a03480443c0c8244c00e003542d002c031500040c140065140040c0f0002c02444214000c840030842d44291280b55a80045262001c000c1281c114014880d4001042c00300c28183d1010145d4117840280f4203c02169803101c00414090003039070000390303011800d080050342013032013504a910a000001e070045401c40d200c4e603880d5160342e2010894401307030740c0c00300300001c0c10301d000d545d0381c3c070b1050b91035008122190520360001d0940d00007080040c1e4581c0d8850600320304d1171180003d04000b048000e4000c0c00001080300c041180b010f108015030b200d6080a000c11040006207550b07424020058005510f4140b810083c0405 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 236433435 1250 236432185 236432191
    0xb130b1612060314010e15010b1b06040503040e090604021011101a010306060e030a020409050a0b13060f0b0a0e0901290306010608010b0313150f060501030b0f01021203 74
    0x30480440c550303160040c50780c05010081d504c10703014013542c08401d10300c02c1d086980043e905443e5501c9020300c00d003d0201d010407507055400780e0891a036900c03200765503c91008250114800644030345400c000502c10702002070f2040d40c562029041298a8081030310b507450070700343c030081d44c0701100044618100d4020b003852008404d00701c054605460780d8843d00d004443c1525011051040400011465581d141c800c2c440a0102c41c142000010084800b01e40d0f43e921441c0c00901032a0707070701d801c01d0900000300060945d096214000211503c0c003c41c080100c01a03502080714040c1c14404803e1202480b80100b40b454039014010b8069140b812485919061000d49600d9075550307100b0300840d640c40c00c2c8440989188103035035800c03200b48680c0240751400310140d10030b00400100d00e0041c80b00b0341c1038404894118618442d841001049800c004c48018103040301064a00d150000f104841800398101604841090320104041034000c41030041904405140c5401070700452019521003030220090b60f0 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 236434685 1250 236433435 236433437
    0x60e011103040e0411130605010e0406030b06090907180c09210b0705040f06050301082b0e0402131d0711030d020304170406020718110a050c0a0605130b130b16 70
    0x881c502d07031001c1b0700c00030480f504908505031a64000d01c80340d6004025140d40b490305540800245246446500706014042c084e2445076140001040350f400d806c00548001e8001c4102c104002c0006542c41c0300141506c24801d004901c50120004070701140c0082500445507449090041050f150380d0a50008d00040804c4e003484070074400854130040c4600d40e54040c220b0303526219500c0d414120303140e141254450445000d50001c230301c4e000d000302260000021001c41c0d420041031507080913000030064041c0400e051460701c40f000e0300003208091124880c08207000103184080503211031100f15502e912030040c012442c2e10400c004615560f103a070013144c5c400e001c1c04014800c0c18440030b00080c181d015504c000c0060f484001c0a11001c004550a2415908031000406c0400004448103140740201603110085c84004076903812141c00a00103080c40641c0100c08100078640703040481030803a00c1807000c4e2610303e0440c001500300c226036003a008409400491240c1940d41e002140410b0203960b0007440 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 236435935 1250 236434685 236434703
    0x5010c1410090515010f030312110a0801051e031218031504030206100f03020405151003022205130504140a050703062406030b0102010e030f04060e011103040e04 71
    0x2104140a020404107441c1c1803001068412007801c0c0140351080241d068035403100004010000345400c2941c2c5400c5980c10b050200c40400342d80c0c1100001e01d103008002004400000f03e00100541c000b0266041e41c6044643c40c070198240c1c404240b200d0b003144011030b0990310200094008241c500c000e81010f5024447c140345040075079010070304200d110801c841410340c2d100f050104158040c0038556201a40400c10030002c3c0c64440c0b184c0722178125100c040c1c001c90f60380001c50640c10700703a09910307220400600720951080e80580024002e60023041240d00303103100355224664809a1138204030840710f0041c06003484036505003a0a00415000c0c000b1129000000c2072101c54440c1840700d4500c0c60302035005000c04e5443c50900c801644c0c4a5030a04007590b004414004094145170480401c0e03840c980340025040b882c45005074018066020103480600c0081072491541c0560320081042c0c54060307881007072180c0b03100015152404400e5414000b1381062109008035288030130210350003400340c4400 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 236437185 1250 236435935 236435963
    0x50d06080703110108011205071404020412030210060801110915120c0d0501060c031b050c0d0605040c060507020d0f03140d0203090c010e0d02010e0a17060106031107080405010c 78
    0x961510300750b0380c821915980d00366201c01003903030400412401001c82d0420305c084200a50798041d1640c102c0d0141d00800d1400f10524881511940c1c103940c00751060f40441400c503c400c1c10040d607240200c020b02406a4104900442d850f08180182034000000345440c9060080903000c201c5608520461549031080a100d0010b514024403805401078600280c141c1e5a0144c0c1040c8000340c490503040b103000e00c41901011000a44d00448a082502d4004801e03441000d691800d1820500152600c80e444140b41d01c003501800955403140703001d03070721403080024820b694520a984501542a01951101028022801041c03421260314201d510901c0d00841401246000103025000a00000c034401e9000c000c0211a0703a0401c0000e805c003400742030805c0c0b044540d8000603104209050300a0400c0040c00c1d100700d8980381c068070301c406803610385080004030080304081580c03041c092084000007030400c40d129801401c00c1d82103800c030355081403000346081d00702001951035900703403c800c9400c00312604003 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 236438435 1250 236437185 236437199
    0x803191b05161e0302070f1203030e070f0b0d0e12070201120212040609051921090e07081f12060c120f020d15080d030b03030c010f0506130c0906050d06 67
    0x1041c0c4941080c50021140e104113050003071412005d508544003452038941d0502a90000444142882d5494500412007204000300c00307080040903400110340700b000b00c05c0440c800c00c01a02415803200010000c001066118604960368444c244000b0100c038410007903403000d0751056102c030b02002e0444101501d001c00105a0401141003101c056440c01d5030341da0b103e02040420b110500c054241a40302410403081601c0316840140160801800540b2403a4180e111a008000b0300c0010440d8011943d101e2504203805406034504444450580180e0400380c48036000c0402850151f40f10904001c1c200a520740d940b80003800d480c802c07082440700e1030800a08158880c080d071032481d00c00010140e00d907903071091070000352110b070080e80000c0180402e0500c4642400200c40421284618002c515048000046030542c0f2a25820751102d5007804408030396150160003590082c90269290055400b00d90380c02011544c00300001740000d25007660030043d051040001d0601d12050010015401d42c0d00c000c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 236439685 1250 236438435 236438453
    0x71503180b041101081f05040f0e120d0e0601120f02010306170d020f010e032508030a050912070305070b061504080f0712020901030b04030311070803191b0516 70
    0x2504643c0d016082c0824031603541d01010f03940e00314174074610510079003905180c1c80000720300d0381c0079283c0125507407141501000c40b190400342c1c0044d00042903844443d444c141000055102500b0900000d0910084040c0c8103000035101e412107400803007200602c8250303603e000c61004441001d90405441e0034000c640c03480b04014007034128030281d00a1200f030703261000103800c1094403805d10100e0303407610061090099010044070f4407081c805c5040306d14070b04203009841d01060303212005006000d010003041264109070340298000c0300342c102105d0b05050107415141c40c40c486c1ca90010002842444510005001c500886801040c000c00e2510f2425210803000301d40e07002a480020366910840007018800070034480c01000d408030b500070b903890150310340100704241010b20000300070000d17000000b81030500c05d6001702c600b030034900c2c030056481c0240e05002510f03400564010341810301c090300d50103020781d451194003a0000c0804142c42101c842000c1681c807600b0100f40341440e90b0321403200c1d90005423456 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 236440935 1250 236439685 236439691
    0x408031506030a0219020c01210e030708130504090f0b071103130501090b0c2a03070b030103021305040b0a09060f0510030b0f010305120901030207062c071503180b 72
    0x100043c3c80d148906406003548805e00880e00c2036402c41c003840f24999900c5a440804401ca15424a0804411244240051070080c14000560102103442c0d410402441c0040003a9180910151086a21541000f0031200c0740507008100c0304c11404017400084a100f9070f942d00100b035050041c500c20541c40810708640c00114002084034440c5070a0005603008004000544086042c540c01c2041c44040e15607070f5184c06081254500110214501c90349001e01201c020f128040c0584012a80e10360402101b44c100f808220310039062004a04a0308109114051080f5040840d030301407074944d4148a00102840d14041e2060398403042c0c8024985080d001d414040c00a40c0b5481d0b000a156040116210074081c1032a4a9051508010008643c001846035030141d503147e07415603984020340c0164024420500020001418040c0d220914000980000d4041a18481740b2803c8800c0c0e80030a521102c050042c1d50000c0440d0510b2400c15100b03910075034100205840d580b0307046805459009142c0300403 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 236442185 1250 236440935 236440951
    0x1223010b131a1b0f0d0302030f07020109052e150e070206130201300f0b03070b030a111309020c24070806010201020f040f050a0e01050306040803150603 67
    0x2010030401116800c00d50090070314040002e00380c101841040302c43c0c85403e0900c4007400507040c00400011003444201c4040e08860101d5082c01000303070018010350822108901e0190304000014201401030280c80a040c2d44000a083c00402c614484032070000c01c0c10340920b8003002c8c00300750310580145106540c100c170021080603002c140f50880040b00804000d00340320854006e801484400403d0302004284c07940e09082880413038903101107181c680302000294994200e41c00035101c0c0b11901c55030000d00707981d200c26800d22080c80204241941c48420740b1a44059410400000c3c000c580340354401510544ac18001c249041281550810150385c21340105602d00c1c0d00107495103020104001c02d00c03001c8171a02c00c5511815580b0218441604024400010301051000081040c2c0c0b0030360480c1c3c0c400011400c240e8a80d61200c00c03c83c089604c50003042d00480a0000215411090030019412148024003c1049554903500c0440c01c1d0005048504d50b10748075000108a03580f100050b611030400 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 236443435 1250 236442185 236442187
    0x70b0a02030d0507090609030b040302100903050901020c0906210111070c0e060108130b27070e01050312041e080307110414041110110d0e0307080d1223010b 69
    0x1c0c2c00071400c841024000c82d061008100d000c01c401e5130804140812242c000e5000031084d42c0340c1c20249d081000400d803640742c151070107400c0020142c006000c0c11005030b00307a08031407207141c0c00010311014180a8030000c1d408030b40340c604240b54041d03103c20303000140e00500012980c00c03010a402c0a00341c03c21030007100c1c41d00f0421000d00401e81601c4245034000000d10b011289410045816031040c030950002070090050740000a4104480818044001c0d00b80d00c0c03030b1844c1350f82c9040860303103035400c1d806240c900068079000010a49400502200c2106003601114581441c00d2590400349502030080300c41c0140440d000504948107001410046014103407040621100900b00400c9681509a400e0000300d400203000100d50254a000d51007030095a5406540025560a96080b5000d05814545108034808401d2a81d03000c140089400c0060f801c981405442d101c2d110746035200c034500d880004004e041c500303c0003507a5800000b44d81c3c000100300c410030f14190010844100c0240c01440704608 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 236444685 1250 236443435 236443447
    0x9020a09090b0c090f010f020c0d0503030118090c0e04050f010501060f1e020c060906071e12050a0e060a27030c0501050c100e030c030c100f06060e0d05070b0a0203 72
    0x2e059181c896001084058071843d02216500007040c8103050a504c0d4100440700004420b001c1c003c02501417480d00050520b00b000916103811690f0b54030074080c20b25900110038041018800360700521644a600c002100d84c41d50a0401103a0008401842074641c2e108403500000803d80c02c0c0300e124003809983c0c5c0c50035a06040480084c00400d010405c0709002c0180510390301c3d2040c0d000c64140301c030689c200c52080e03039401034400140090144a4010701507800c1c030a40c0d0040003034200030004009105030780302c0780c06c0485a4002d40702802008198404200000d20701020760ae4044000d0505a50078149012106d0b44a4205030603d1104d84c11480203400031642841803202c1d0601c507400811092034034a14254448000c6d58645007e041e9a40501d1303290100044009414403d880420405ca0b0489840390f020070740b0141d4542003604030350f007505e1401d8181c41080c0d410b800307210191803032502c94104407440304080c040342d0f5040c00020303586401511408948034071311350014401c081c284d0b4005c1d41c490b8 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 236445935 1250 236444685 236444693
    0x20f070f060501051002060703050601050c0106090203010503010f1503060207021306080607080c1e0306030a020315151005091903061d1c020a031b0602030717060a0819030309020a0909 81
    0x1402c103070410344c481d40582e070000100e9940081c416078032204034580840c0070384a607030060b07441c0d0103020600c01065081030004200d8403c20342c041c50489000b01c0082c0b24454007120315104880c0080c4105d884216150b03014401320f002c0c1c2c3c005051752031001d0045080260110720003011500d481e00106940c1d0480d20a2040a550103480f45410081a40e41245408040b0348002013980c18001000c005000110008925a40034405030880d07580140990307c5003902d0350407003e2500302c200c8080d03558007030095545285003005000301144044075190340f882c14500c5003c000150b1550700b1303450001c00504402100003003850207001e000319000d80d0389056031044106401e00380441411003156003592100241e160550000d0b0300324800d9007509100d140b4002101410041528006015040600000174024615440b0907454021040c880c0c1610701d540342c5c1410801280e109101d020341590044069a010018040e078420300d00e8864100000d000566502056401c0b0150b07004140d51960740e00c244041c0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 236447185 1250 236445935 236445941
    0x9030a17221a271626121306030207030c0b060d120905131a09040201021e0304060f11060f1e1305010b090403170403171501020c0d03050d0b04020f070f06 68
    0x4004103c0107004210982425203500070080e1251501c08503c103810241440b081802052200c0b64181c01d585071400030f1103a66006a00c80500480c400350789882c0010300f60301c43d00c2565000e56056031012080801a11940f2107648003a20040d880702804045e44c000500b20350544954540c107845007440e040c6040304010007640c1003c82c040b42141090f01444c4c0c0284900c03400045030b2411181e14401d5211400104d10b41030f0348010304200900e0201f81040d00640001c058000c031802d035a0b1351051007902400c02c50b0b500b8100038014a807580f02c900418000045040841da1001000140340440c00b019102110034880554a4003002c10510f403043c0d040c03000a0090004060b800e9401c404d0600b0315550080c2010600b00304440e042c541c0030f010504051007804400388400316041014010300349050010580c030302c4c00800c9409032249004005e6182846204144e0103030301610b82b10b050094100145010344411101c448e0300550800c141200d4440010103401a07601a0f620254094840d203000811 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 236448435 1250 236447185 236447251
    0x2032a1605011209050606090c070b070c1203090b1602030f040905010f0b0c030307050d0b12030c010c031a060f04030506040c18020f0306040c140309030a17221a 71
    0x22484c1010081c8002c51310009019401072010345880569940383e4141c070000c5d001d001c000a040b0a072000510003000d620a004074800da016240c464202c4000031801c0e000c4070300441c402031007686254001040202918031500302d50703190340140c0e4604040d190b5840580d40c010b402c02030142d40c1e5034005200741e481d04004040079000484d02c061a00904a20455881c04000c180d80108400010365a80d40102608150019200500030010001b14006619200d82156000103410340ca002400c202c05480390003441d4003040c0c0788205004a001c0c1070280401680880c00c3d10080d010108000800600100100341c807403401160814500342c20912080c029001e440310560840d130060103410b2800c0d1603070003105e40051040320300140c0040200d6003a103209445003e41c1c4021040442001100c840200052400c0b522564071503208051204013100e58400565100b103075070892801d0700000022444d81552003501920300c5a6240c0c008100d41c15070204121205004000707a592201c50700c3c80701c1c00d40900 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 236449685 1250 236448435 236448467
    0xc0c090e07090b0a03150b0402070c031b140f240702180411040504020d1406100501030509030d0504080c0d02010902010e040c0e040f140c04060e030d02032a160501 72
    0x5801038000001e00da210b42400302400f50702d0502c0840716070b10000d6002c1f4021010150066440742d005080004c03007841144401e440d18008004940d5240311070b03e9041d003d80d00d134241c2d0041d0300304031038050150061404561030341128902d1514001f480140045286d04d0ba800341200350f45030258070500820f0b1075200b00000071f40e1000002c0c000000c0d4505c2c0004444e1005460000b41582c49000042c5418102c810280c540403a00000c201c907a8404207800348113031084034040c0c01d59a6100011021100111039840081e0820711080d01d640019802090704580a40d82040c03e101c0c115000d14101180540ca56000d40e44d00c80d0b400f011135800500d0b56101c4142120b040014240c80f5401400c05c2c00180d903c24407499981c02101601005948084e40750040a818480c5c6440c01d203c7c090070780e0f40103021300b00110303410601c40c2d00b59140008100c03030300c6181c5030702a502300410500039508202c051818420088141d51000e040600c0070094101d8502e5000d0404440c1c1d460a000500540b603800c44000f = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 236450935 1250 236449685 236449691
    0x10050309060c030403090e13061113050d03020726120309060703090203010f14101a0a050c07050d06020a08010e0108121e34031704030c0c090e0709 65
    0x1403035000450020b610586842015560313581c1c2d407a048400110540005401c98000d00510249484031240e0500d42d9101d000304210105413404501c01e10300521008a40d60b0181500c140b0490410b07003020040030744030307004070f03504140c5490781c07040c218001c1c00d150300210103000030341c0346ea85004000b80300e1269540400c0515500f8243e280e0341c1c0742c000082a003014182ca0368011000c544007503000542c44070f09100200321409074145a90745148068030301c129400e1802401180340342070390311442d5002c0343c0803201c1841d0801500b8107036120b8110341c61404042c0075080340040d10340ca40b101c452001c54494240180d60f54151000503120030410380080004250442c010b02c003000707000410301c2141c00f25147c560344401c0202c0c24411005901c407800ca00b04440442c03c080d144000015640054115940954a40c13080403a1000d00c0d801010f8080c00083d042d00d00310400006901140380c006000f450500c9030443e0130307155082884d08551144503c40d2362101c8100c039540c7c041c003400b000303011501d0041c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 236452185 1250 236450935 236450941
    0x80a05060a060822060c02030405030f01060f210c03060b031902060904020d110403030f0219020105030c09030a06091b06170114121506010e0609030709020307260402100503 76
    0x400000005040f0f0785100e40c1d0b80b1100b0140b0058083c0c00c00f00c0c43c5e00c240c003440040d910f410300a44070f130024410304d4004d00c40c0491603c94000d041c010181940d800003a51202285050f550304c403420210b00d0711480b07070111102e1400115859080c01c501640c01001c01240c0700c13040100341841c2c803210124021280003148001e10060303407080126010304208540c003503154001c4042c000003c2c104043c0a603810140002c0000030035410401c3c1500c812129020b0310120660910307199115808150028002101080056580d00300d09000e03210019003e82110204511aa50034041700e1100205981c040c0b422650000b5100c12030295002401051a02d0016254039503101146000c06004d44e000c40c0f40d65855010540e120901c003032482c2c1700c0c000700302e580031407219002608080007961100c0c0040c0000040b0741c0a81086c10440381e5200000c2c00030800c951801e09498000c0d003002d08200200400303070305803c0318a100024860703014078111550156608141c07040020b00d4130081c19040074040c00f8010 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 236453435 1250 236452185 236452187
    0x231c2316090203060612040f0b0c0a140a0905030604210509030604060b030c060d14010e16080402010201150306020909180307030c0c03171b160b09130c080a05060a06 73
    0x50001110716001c0e0258581d190400011030f9409501c1002641000200412003404035600c0000f91981c040c0100d40b442d6165501560308a12840c4440004158602494a001c1c4410300007000c1d590154546030703500d5a1200006410f10b44203031020f45442c018006103185c41690018138020f11442400c00303038900714a0001080e1030355401080544615035805204a2030346003030001c08200b42e0010710155881031103a03e1000208413085030040151469400800c1c1e0721580c1b0501d90044150180c2e61681c85e0704424100d41002d0020012411552900401b88100300b9000311407010310301c40c110168403038201c0428091080b100901d5074503e280c5621580003034803008011102041c1d010301d0102d461032520b003015120007405500c0285000300c050401c0d070782d080291020382114892801607200382c60a50b203805540b1408090080010088080704200c00c01c00f4000a0403039150140140e5501a0300307420752400c48002043e05e2020800d00401c0080010241c4203907039006e40111000d075135413814020 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 236454685 1250 236453435 236453473
    0x504031a37090609050a050d020106060201050f040605040c0506040b0d05150a0b0f0c03211501050a200307060e070608161b02031b03100204231c23 65
    0x154070581e94007016040c8103960f0000c100550f0000c00703c070782c0210b1600c0e1040d65600c4000c14900154617003400811031034410301480d401904181d50790082a2696240c40c0003d01001d4000c4841c0b804490000420b0348a4001034801401a4040c1580f45d0400c00e8181050754401030040c520f4084200f4448025543c1403681029a220070941946800e040b000f00c4089100d0462402c20503c40440d0b0140c41c51048071248800c0c514032002c4004c50303240c103c681081c0c1d000d01c5000c81d011a0b814003c0350859440784c101200c50399041c03c01c400c40c00986911031400e50b40403d800b0351320b00e51125a01c58140104000940003040c2518100c0c50500d00fa1001d030740c0e14071445510100f04000000d01c0e51009100041a4200030b03001804c0d500d218203a14074a140d90300800f21054041d000c0d11a9030150b461303036403080c0c504580c041c071101810a0340440004541d840d0a0b1031041d44200b181103242066440b01c40450344240c8100d006043c1c3c5001001480d0a0524400c80d8064541c02520344021170f0000301 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 236455935 1250 236454685 236454781
    0x90c05120f062a0403080310081b040c03060f08060106020607092706090e1501051207050907050705070306060603151d0a0e030c1c0801030201140a0504031a 69
    0x80714503442030b140c81d42080503a0707003003082040c0c90f900104010081c0501c0000031805001020014603045a41c0c2002d25114106441000108000c2d8505c03c22035003000e82040d0a503080c50300e00058003d8a96801c158840500d4002100d15401000188151030301000101d811501c2818034046041c5004003a10002c0e60540001006005007001d016201c0dd542c0c10030006400a19810301020f2030880449696030300060558950006a0000040c00c1c1003105540002400e0503003e85210f0b41440140414000003130181030030440104004c801180c814000300340510710038030002c55030724541040201500e801e030462a81e40108400300300700c00c03005a91104044480f00f4003070b00c0c0c140d9801000c40d004145000c0c450400c3e0000103105410b840d404104e1410341001c06020415003094403004a40440342400000d000c20303d0151a505e00d1045480036246a4020740b8110340b8045d202d5691f00950310603403c90103480c1200e041030114581d05444056031030722560240b2204032803100e009502c80714001d = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 236457185 1250 236455935 236455951
    0xb0a110316031d0402090105070206090f04020f04030302070806011203080a110c21090a1211030312070e0d0c050f0402040302150406091a090105090112090c05120f06 73
    0x220441028844050041e54005076400440055960103802c01a006901d183c0318101845801d0f0510300403442c2900c2510000c0310181d48290600380703180e003409590fa0001c00d40c01c0d4003686420b401c012596541c0000d2034601ca00c054010303110752951402a1034801c164001c00000e42000300180a83c400010910903030f680c062070051a99120030308030200400c0750f0f003540384448000042e24036001d4000189081c0b03100e00401c40c108400d403241d00c0809207008100010754000a00c0303000304400203500381d0481d18140a400580d18008100000a280d9408483e6440260720104c04001d12260003288a9803428016078604120558559802404000d28003801d807180c034080c60b5401850703c6a6060300d000d50307405441e40ca552444d056281800f90403500c02e01e000101c1840c000719190142020100456030300700800d03400d1203404e078015182500181c801c103040109550924075452171a02842c9d0045008481a5401d2801c107410300a280041c8041d08080d0340c02005a0300000d00e0001e101d55000350b003 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 236458435 1250 236457185 236457197
    0x41406030402010c0218011509180905120c0a020411070302101a03010509032a060103020d0303321006090e0601020a1b360b0418080d0c090b0a 63
    0x1e10310041e10044424480650003400c400000d0403406940b40c0441d040e43c80d1021680d01112500000320750044032030181070640c506074100341e81d003400c1640040e90300c0c82c03068003030395414550004026184c0c4c22292011074503071300c403001c03810660800388250868900f50903d5585083d5207a200a540c07040d100c6000032036181d0f1464010200040e542840392020700082c001d0201d0300b0100d15035613030303a08a400c03a0318004c1c2150800015103400400085440d80c0128090402603285808014001280202c00c2c0d042c07644585800a14280c409495941c842d80d80000100c2e00390724281031050201c0041c001002c00c2c07200c00041c4009a082400c55048502840741e0456954503074004034104184404001c00041c40c2140d03400c038042c2c5481b214400c1e20174101d0511448034850082c0c081c406008103101813040422100791491083e035400c038a05410000d030010914000540801112100c1904160382e444404500e5503141c01c00e03070058141414503854524006810610802241e00c2446505018422 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 236459685 1250 236458435 236458441
    0x80103031718010c0c0b0c1c0e03040f0e10060e0a090b04020d06030f050c10080a02030405010902120307020906101403041412040905070f1b030e0604030614010602010204140603 78
    0xa110000d60009940d24004d219038000714a02030100c411100b011140c804403a030014050300010030582d62400e040c20942481d00c180c42213110003c04c003008106e021404208000304040c4a0960318200034442401c10329007501d40700d5021940c8103a1504840700f005581d8250000640e5844129000d849410302e00082400c050b00006000b0310414100c490b020f401c000001050100b80c01e0220000d900450980c1c04c200b60060800c405402180703410030106181201007004c2c246207501555006204000005400c1c1c13040e00059004810030000807040c3d0b000080d0042141428180644c01450035510500003049210018007449250038000e141c0d00e001100060070b00011b02508088420880c2c2944e001002821200c01e003984540075a0760400d0514000c101da5174411828046041310aa40b1400900c042c0d1020754662035890800b0380410000c61180c1394940e80e0400100021445030000240c01070b9100121402101f0503803000c429a481400200001000e4400d558101c2c10111243c030b90b01d40d = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 236460935 1250 236459685 236459701
    0x9060105100311160f0201021b060324130605010f0507020f06030705160804050f12250e0c07050106060903030807141209010b0a090903050909070905150403120801030317 75
    0x20041131418503141001a00340c400748105c50102c03805444c002c1e400c0e00c0c0c001c46030342c1000f0700c20500c2110468100304100000f80410f0904d82c42048072aa46425100391120018002000c7c0c107090071045c0b110300e554110402440d070704580d000740c1200550405504100c150703000654100b01103161503025070030000002c0c0c2024841c84c1101c40070180700368482c100c082241443d554542050055034040e2005405900417882e00050b60381c14002501e008210448503603000f02d90a80d00d0a8120b210110303074000103e000000701103860b12030148022025141c0386141042e03800d403102c95200303005100320240d052010951114009074000141c1c1002c001050304601d05506611485440344082c1c9450020700c0f43c1070406410141200c0c5048a61514281c0c488154404603410000c0c000c010840400c40050030342803980c1210360005503820200007155071080032688004c08440441c19092001a05208001d40136a011140c0c42540c07030060344940c115a4040d04181c084031030300324a04000c0c00050504 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 236462185 1250 236460935 236460937
    0x40c111b0d0503040e10120f1101200a020a06030509100c050d05010b03061206010b090906030f01090f0b010914010506070203071505070605010902070305091905030d09030b09060105100311 83
    0xea5031102c1281d0355240d8902034405600381c20751740080411804030b400508881030180400b03d082d00440c00c040700d0358403551080041840900094144901c41314502c1c410f40800e01d15201052404015103000c1c1800e02c108441201c55811a60515140405001680300001a484c2d2a81d01c040750000700410401000e0780ca81c0183c5080304007441c142400440da441c2c0720340c00386000707400a541c0d2149080441d080310f9100d40c0240102c0c1030b01003007400071115615045140c2c0d60030032006000c3d189030546440b0b000b070a5509c490800d841c100034030405903003040b81442d01140100f04021040200c00c80f140e0340c01100b1071040c818544110b5010402c02c0c1035613030500841000388040512000d81084100016006410058040d215103281c50700010703a400142c003c403408203515070740d00d0b4500b2214108216501e101c40c075401c003c0c221404404103941e141001380d800030300f80d01c0d15014025491071510410f1004000e0204085400079001005203845200b075040105582e800e0109603c2200103034548a = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 236463435 1250 236462185 236462209
    0x10f021912110702091b07080d0b030a030509041a030a05010504021e0109060503041a09011505010c0809060f12011412010e0c060322060e0106050a0614030705040b0307030b040c111b 80
    0xc2400141f0f03201046014001800310401000d0f0611102d030955040540340c00e1000e00240100b281007190062600c1e060340918980400d6844801798007000b4800300e481c0201004003249d450b03540e4000c0c481546013511303090f00400d05c2440b8091032294589c0c0020490750442c4a840180400440854100904995001c403040e03105002c03003106140003015030b400383c004000301c0c44a00020203008940c95219244522959030002c0e4a5858440c1e80c5043c04110f6000c0645180c6400090100c5119100c8c01c04510740244411a060302000f80100300304698812608070501c3c49a14040305044002c1c2c0118000c40300d40d204031003080e00d0b0780e60840c94401106000c0070088545410006030070030000160b00031070a490627800204421505c41e01404401c030081e00607680820b1404103000c000c0365040700195800310780c2d07103000c60415030344120f02c002030342045c0e0303040011035100e0140d0640d0781094070079551031038100e103020048510002c0c009512048814440c1c002505007500c90301140c0c495040c080a = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 236464685 1250 236463435 236463481
    0x30c0203010903020a17120c070c03020306070c06050a020c06151f09080105010806130807050109021518010801320315011e030c0b0a02010f02191211070209 69
    0x80964072901d00203440d603100c0d4104580c1c0006c00035000c0304a00198054818003940c0030308202e566141c070402c1305484c1d04004821030321046001030100068070300340702d074501a070980c1d103811100c00a01d103000b0323003a910001c0c00c4010701403043c040c10f1588040003420507002031a05102d0b0041a071001d020030318000742c0110340c165903c0c0401000400b10b40c000c4441084940c031200802240e600c0c0d92510351580419544050a00c1030080000f000c07803804001021403d101314000180301170540c0c042a2070a420200c00442464046a0106e21540b0004041d0342584246442e41e1303190b05103c1204400c0158005020b407002400340f0421100550014400c01018002c04680174040c5110028031129001d005843ea801d4108170100038551710b240901040c0c036840b480d01445a410441100815001000c10000310764813640c114010b018540700074101c21140f0007070071968120000000d0311a00f00b00c201082101c1ca847c00480500b2001810b41e0a204d40c1210f2441e80d40c0c8900441041414403180182d07 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 236465935 1250 236464685 236464691
    0x515031302190f05120604030c0210030905010507030e16030312020d0b0603010305010219030b010e010302030a0f0c0f020c0303030f0c03070203040306021305011103030708040303150810020408070f0308070f030c020301 96
    0x400c00301000000c58044400403131700d107005e415030307440e42d16215101524010080b4124600d1040140b51129004440c0c403420f180000b80268651a16030950302d003681c1d0b21022960381c0c0c9100c03500080520480c80b00d1805c2e01d829202861444c1c5d03004286446091504850a501180c6144e03005c0c1e182c2c100400e01e1400400f02612940c480c20074600030360009503240040e840d46100c034503810703001c2e024901d800b81050712662401102070005401075807008160300c0b012562141c9041c2051a64410301c41c090b0b80b42d0b600d548218400a0010f0302e4800741401d01c511a0344240b042012009128001c03a51159412082640741d4580c5a01a80f8502072500002c0c41c6038000300707100b150802d6604484007224026680d2801c80b440004042d5100c4c48299080400249201c001401080c000d400c00c124000000c00c244805a0744d0703000050511524a40d02414550000340410903d4010026000501099108044070038603590380e83c00c0341e1141b0b6038020410f90210380c1c140c05050243d840b01c5c0400360094028 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 236467185 1250 236465935 236465939
    0x90c060d0f061a030a051306090b0f1f030f1406010308090f0406060c06090c0b0403080c060105120714010201113709091109100206010f051503130219 66
    0x5000900440301e8003942540c90a000007620f0100480428840100b8404880c82d6884049140d006003d0082805065a0502d10113000180f054861801041d005113140407882c103040c0b883e842c124002410107480d038565404c62846540700e11281138200ca40c04055440382c015646042881c07440c06103401151070141000000c01d1100380b40050540034000c0f1a060010710042c420002142c0da58003a01001510440c04031001860f00e0340050310490107040500c5102e591200f219929510681007140d00d81c40118107001e98036020051540035100450741a41d00c000070b6191156a0120f510a85a030780000700000c102d00d900030341c0b2504011084260103650b580e10104a02c0c0c10b0f404104c1450300340400d1012144007148010328100300035509940d600c42040c500142e030005416083e07100d18089101700720314485a51078144007400a041d40d0081e000b01d41c54115890368002e081d5120038000d06803880f01d0705904c85043d040780da00100713084ac1c04510903450300104005003a00e02c64041c40440310400 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 236468435 1250 236467185 236467207
    0x61b080f0301060f03110d090203100c0e0405011202030c090a061503020a1e1b030203040b03040c150c02010512180a03030e0d0e0d08030c0c0a0609170a090e090c06 72
    0x714140c0342e294544840383c1c890142c003207044400c0d1821000c5002c2062115000603805a08805a0720303000a003100c001c0c900e000303068412104030f80710a001142206200d0215414903015031801085114600d00c2d80e4045600426240c11150303031b0745480b0b00165000107039200c013613900800183c02c501c02054004254110060000d601c10104880800c510b0360020240400300d16550301001b0f1180d980e20030300180421040405006800c04070154002030101061109007080a144682e000d50031070218146002c4500c01c1f42c0b03810602c08010800c4211054000d42d07000b03004c0322180e03014100a0f0115a880a4092290600c0c3c07080c070049070700484070b43c80b0500d641034104c10040c4080341e054500040e0792000644900e460120101e40200403000079a01241300d480c051688040c020086034500740a030344115040c08802c6800b2659a0740c0c40e034202042c000d003600444042492960102d00d031643c2c1d61005002c0d401a40302e141e2151244c5c00016003207800c2440032002403c07003d8400f43d121481901 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 236469685 1250 236468435 236468437
    0x90908120a0b010c02060d0603051b0a06021203070c0309030203100e122b15090203041104020c060f09030c0d020c031902010807140708070b06010e06090a061b080f 72
    0x10308400031030406000314509003810320410b20080c00c161100320365813040c4e03400d201c0d1680102152901c0c1c0d03983c80c032001010640070f00c00704504110101d0320042c180f910404102800c0101e07088002158441d100c5001680400e4040b01d410640604000144a0003031508032401405504002c3d00b50050301745072000101036400825444415500717964100c0908001d40c506d40c002c01404800c8145898403048140006002c40300c4a20b12828011501448a03501126012155800000d11907030000803c4144001c0c8040000101000ca800f5440c003180c420803242d940b00b0140c030041d0304081c0d110100301d03000703420011903828003000170a450038680703000c0d8082d4540c50b000400c0d41c064000d00c1504540028004403402d4840e034141c544515a84591500b15a1038036940f4111981080c10030200020078205000342812500c9899071000c10303c3d00b0800140307840703041c1e1103a502a081c2400301706415602c04080b80240c0c1c1991030540c500c501c2c039054072640c0c800d00c94070180c41c02c8800140c2c40402c843c050 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 236470935 1250 236469685 236469697
    0x52a101b030203100b070b090c09070207030201030207080d0204030302280c0b0c0124050108010807080715120609091a09061b160c0602070b070305090f0402130806060111010905060a020f04090908 86
    0x10270b480c0d4801d5448284a004a41168240c0058002100910040d07000c1d0f0302034201035015081e020304000d9a007071441c0407039000d0303001030700980e00580c1a408441c1d006412906c488403000c4403c58080000d030341e821088005405100c14a81000c680d815000000354002c42400344c0310510040074440301e401400d603c00e854002ca41c0014142c50000c2a2404c4c001150b9048499000003000707858500b46500100302c05d0001e1003420481c0811260344035015038002c400250610410005021529207000301b44805400c401c4a00c503521081000002d07440444c0080d0b00c07240708040c004030314280d525105124892942c01a114220100d140c005200d4402c401100303840694081343e0410f61200c0048002c2d0103109001030018404111041050a00c10101950340002410240c00e040181d0640c00b00b1401507002604583d0200c0108039803917034080705500308062120000c0000e00c410351151615003000810040030784c1d40004000f140824480e0485000700350b100010085003909160000059100c0c0c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 236472185 1250 236470935 236470951
    0x1020702300601050d0303090201201507020d1709010b04050a092607110609040e010c0f0f050403061109130c0f1704030e01052a101b030203100b070b 66
    0x140703160400c030800028a0034140c400042c0038030390780c11031941c04401a00c40458224100582003003040d02c10000d06201100b8810300c2c4001d000300c54007000d114461000d0040402c1d08640c440384031040c01036000108000c4002003070201c0d001c2c5544480196002d05801500160054904401c02c07000c090319a200046481c80303440c5e0301600c9560340340c02d000174040c91308a924130000b0400401e000130300322480d503040d10700d4040c044504200c0710b200024200c4070315030000c1c4030994440b15001c1100358080f00500048501d424004c4000d910000010124069400b000300b899580f2405880403803056002c2c1d4400a100904104030300b110600a030003d000804011004210f183c50f48007955801103000410f9031010160f89181580e55840c2201c0301050407940c1414402d041000e40c401050701088000c40c21a40d0b01300000700080400082e240a0120701c1c12034031186414a00310341c0002c00181c00c15840100d280140c0c0f25101c00380c141c00d40c40c030b040c2e0054980d14000500d004c200007c0c201d24602c0741b5a0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 236473435 1250 236472185 236472259
    0x30e01061221090b0d0b0a150e0405160f030b0307090905160605090618150408010b010e0301020408070e04061b08070e0901050907030f06050a030c080609030c1002090301020702 78
    0x20380c4240c0741c0c1143ca01842d05401d4042c4100d2450090951048454400060260009540c4e54441801c1000b903440804001001114040090b05140c01401c1d08803100c03070024403121000c6900140300d01e00c040084230815403101c10562103542e08000c41d4002d402034034820440100ca03460070a590f868411810401822005000160640503c0030b6903421000602540d20b40404081c4000c00c0d400208110360b40161000e001981502c00311b800b810140c08a2340000544229880000d027007031000c0c0120758440c0c4e0040000340100000410003d08560300034440040301d84481c604100039046507411031180405070601143c45942c070000b0303a4001c0c201c0e40c0360301026210400600034400d2003401003c1d0480180408544490300caa400612a036889101c00240075407a20001082030365a90f0064802c0b550422041c0700e41c85040c000240c005200000940c644a4008452516400c01d8004021020b60115943c0e0140d1401e4040700c400780d40c002e180100345d00d099a040181110758150a03000c640e2 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 236474685 1250 236473435 236473493
    0xa0f080109020a0e040506041503080c150603100506030f060703050a0614010c08090a080a050a020f0603010e06010507082115011805130605122803050a030e010612 72
    0x200c61003116148416541c843d13035141a0b80b402e10001c2c0c00d002d800d8542156507494000d0100801c0d0b1040e10256100f40c600769516805003009600d00551300c90311713000c107d40340410701850b942d00051070a6085843c130400302c0c0036550800003e0401720014020300c0781d0f0103001c04220a0503803541c0094401c004000040100945070289101014002c801c0b040c0850402c04240c00844c400e2400b80810010081071b0700416915021101d0401080320021505684054110381c2146000b040422103140b099403401e0841d85450042c6000a002a10301c905101000071500300b400130510884a18007400000301c01104111266828444000c0301e010fa8403056000c60030126600c82d558155926414603d440451400c2104100341550440100f00742140e45000c00103080c1c8501d42403c0e40c0c41140300150018182105601c00794180c120502080b0226502c100344c0081d401c14151a600309280c6400540e00340414080c0e40101200d070401214400201d603284100070400c005008540da6071080d5444c415 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 236475935 1250 236474685 236474699
    0x18030e040513081206030106090204030503040e010605030606071707120206090c0102010204080309120709151d01030b04110f0a080c0301140c0319090803070309110d03020d11120a0f0801 82
    0x4440c0d540c01804400100030b26010981c1104015030005c00040001920a6841010b08100d0f8003030343c001c5a2503000420304000080c9030025141c01824103040241c40c0d80703480b41c00100d50307100f0050010114220303ca490100a6107080580d130b41e065111140c50008658000040d581d40411940d00580d4410480d84212552060003510110303051807005504119450003008200c11028001c0c6d0700a1180703410005107048c1d14001c05501204824417030044038104440d4620800200c0c581d240503944400041000038a60b21895038801c3e00452b56403404da05100001d030500c20f40ca01c00307690041c0400004940310101146803c0541c07030071802040b030305c0300342081280a141c084807501c0940b401807000480700c040500c608070080920450005401081d6136680c40e01da00192800d90019070f60f05188020006800702121000300100c4800d050f10410b03030740003991154000f07014010800440720054500d41c0402075a40c480d622681001e0b150903040500400e80b482c20000c00000480640c0009419 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 236477185 1250 236475935 236475961
    0xc042106051e01060f170c03060a06020d0e06070f0606030c080115030c03031b12030b0a0602011802120f0708010212100812130801054b0a18030e0405 66
    0x80b001155400300c2d030b130b18100c025294542c0c4016980c0500000c500c4228280c11410b5156108003c80d450540d180e003170031800d000100360107800400656001920090a00d40c108400d141001c2e4120340f015074605103407034500b0708034684e400002c001a09014011042185215948003680c1040c4020054402050300c0c1e02c0c0310104a1001402c2880b8024060000c6441001c0f0715181306000d264201201041c1c3e0340d41c1002c0d0004168001c00280d13a03d126954602d06151540003c002c0e603c028442400080b00c03d88880341044c0009100f41420040805080402d220341c0e4611100001035900e20b96540400038042d52101030300c0c0710703500c0981c070008800d03490082045080c0c2c0c220f0700060030203120041803912542d2008546d1034040142000004802409005103482032101c032044001441e100742c1f0107040309404111034140340d1003038104070201044c0c042d1000c0d01c889698010b9981601d90083c43c000410074140e41050386100340c40610b00b0301d50050100050058191340810090392144031050351 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 236478435 1250 236477185 236477221
    0x40b060f1215150a03060b0d0209010e0106080609070219050c060f03040b0f13030c1b03080a080a0b01050a030902040609110301180504170705070509012702210c04210605 75
    0x7004c00440e206202050b0f00c0e0f031089420034400f5261041152458000640581e0b007607024080700c41d62200140081d0754889401c130b80042c01590704818508156a0281d03d400714200703c101007100f840850350920034104000c1c0d080c2c10000e460070b540d80c210f840089182e079004aa090310340d200c40300d010540a40c80803002d42d03c680d2080e42c2000c8020100e507021039031440b0039030050300e540c9840350b076403690001c46036076400085120391002c03035944c5010080600326140080400088502d00031204100b66088011214040c02c145070001e017045040c0b0018004002c1c0d60000000185040c90f8681c0001c1e004c4003c5059500821400d40c81c480780d145442c0960380b084800400810001320004080015200640001071190741911922921000843d02c92a800d13480140c002d103c1040443c181c0c0034006041800200030081075250102905800f6a5154012400c403800d001600000314001c803c1d03000c6d1400707441c100103881c15640103400c0c0c01d80031011415043d640380c1e14000c08181042000268032207 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 236479685 1250 236478435 236478439
    0xf0c0c26220f060e010813050303010e0a051008060c07080c03121b070302120711032d0c0901060c051510060e0f090f0604090f050709060617040b060f121515 69
    0x441200f6030004645000000e03101f404200d0000300c1440c0040e0090000d035019020000d00013000d894a20150403e9030070107440305901c41070741d190070302c51b24a01040180d44001d41c0110581d440d110382c500804184201000741605000100307003003084c3c074420061580070316030302c5811205c50104080d0450349845076010042c0542d12410903000c02c41c3e20503020b000313843d0040000d07108041d00d04010900b4084034041c4400321114801e0781540440354440100c6040000300000e01c4d900e2410000b00342d4011060107a4010720907180100004c00c401003003148601c1c1e41b026281d210364141340e84a0040304001e0301500740803440f1061610240e0400340400f62121400608201c855121004100380080026260540080d117032807410000c00c45646003504180e203d031009007409450040303100304980079500030004001e40c0e6122845d0680c2d45c0688546c0082c1c115803003400c261200c00001e05d40c500c120f031a00e50402071509051001c883c010448045072400948013403004d964221075000a03045804c4940c1d = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 236480935 1250 236479685 236479697
    0x3040803041406070807110a0801020a050706111909060f0e01230405030a0803010306050a050f040b060a030c06081806010b070b1b04030f05010f0c0c26220f06 70
    0x35119882e01603058072000034226a280201c29103400d84140c1c4046001e80d084031042c8170a50090030800007120080652000031070425100001c001d0007845480000352545440d0b04c000c80344028408201e684c84040e140b83caa00e000100c207806006400103108140104804404960480f80030304080da0401d88142d55011001408070000d10f40d030514138818030f0700c40711309110100310b5460400c440c1c540c89001d900c8540e00d961441c64200b0a50b84002c1c00304150509120902c4410044d500c403203500700da0b120f9040c0c2c2ca81d584840c0840c840c0e074910317400078105820200300010884d030084940703030056203130950ba40a039441102005036134607001e11074580da210f800c22a10000c2585c118800b900400030865602c00302c81841102070841c2c1290300180c42e0305000d52a42410400d0901c200d919250510030180818103c4040241840c510b03800003509590b041c20512030303a41401480c070307020705902c001c14036214000709905151003d11034903000000c104209000c0344111b03804003108210750303079036a482c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 236482185 1250 236480935 236480939
    0x40c0903060506031626191106090102190501110403060506041a010504090f0b041b09080d0905040908070f05010e0c03120a11030d180b07180306020307020a0b270304080304 76
    0x1920b00010140700c007211a90360b124880a0f0120280312000e55041501024080d004980c14004034514803034910509c140020040244980d8001c906540c40091081d6685025122420071a02410005c02c050b107000c80c0c0040c000c010881a5884240a40800d80c0d00300301c030076000000303a0b89101403a00c0e442d009c148240010014440550441c42c6050810400407424140d11004941943c0c0600704009084100003012420f00354440c0f10f840040c0025002030603011189070000e0400038050190500a0f900c8202c001d0910501b641202c00c459800078141c0c02c21261030030031034003c011341852091140540e10b080759162400051044112880c410002d240010840c0c0036550310802c0c440f0081980010322021500d1510391140c00340000751000c1d5030000b013001d481e00050250004058605118103940c0303d0188845c0510110180c13540300f1001039482c1c0380c403041640740c0420300400030914120030f0704001c6400d03042e031082009200c0360035510881403c0040d185849001d903005140a0364024001 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 236483435 1250 236482185 236482199
    0xf120c1707030b0a0f06020f03040e0703020703030e031b07050a0503031911100f05010605030c1c02130b0c010b010f080f04020d080c0d020d0302040f090515040c09030605060316 78
    0xc5180c00c01e0700da040003c0c1c000c603120042640c56450303078002c0c150807503089010070034a50180003150321807061070095490f15062001000d00004003500901c1059400705494003011301075403003450503a15500403a601c1e00d00c100031141420341c0742c5910b00042e0054030707000a0603040034607540c42036030001005942003c5c60411646440b1107084c114a0030000c0e0b201d0000c00140c0107010000410031001c0e0081400441440c0100c1941d4047c0d0220040180030010031a580f81401c099a40c00180194089100f640d00081000079020f558002507100c21140070000d0000320300c10060405817807020081c072020211340f005407610305081004201140e8480c0000b142c6102c0c002400754414802400700d0081a041e0301c40d00c01640080c6a080040e034403249070219115010031500b0a4110580340661400307062218081c00c05c80e0a11030070754007984403004079885c0c0a1120341c070901114050400c11540346002c9000340004841d20007500c40030300e0400820b030f10381400704a941e040c00c8091b540361034441c68020 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 236484685 1250 236483435 236483477
    0xf1403070b030c0406030e0307060603050a0605060307030305030106030218090c040e010503010b090402060a110d0905031504260412060b180c07021c1401150e0421090b04060f120c 79
    0x7e03010524002000207100090592081001950180e001060b80030f03c00d181c54070440e24050700b41da00c0b99000c030004000080d40002200c2c1500ca2a01d009038941410301c401c40e3300d00c80d040c0001c80c1d00c80d00c41c03000c202180c80b0380740140c41241c108090f071007090f90740c69003458200d52000d244103401500d20780020340035044c81c1c401000400124034003000500c00c0d101049080c8540c500d0030030002045400104410719042041354400365a1040108660400b560303104100b071318140c0c182070320914440c2d0740024408172006a60040125164050420040c0c0c40c1c0703000280303280d81c072481c45030440c101c00c035010450701200d02e480342c0c100007003981c540000e075002c101f190080010310a007280c0203200c0000004c1da080488a042c072030614000b150042000c01d13800c007641c145401c07038000204030a0400000c00c0812518100d000c0d0a2084101c514070456021244490ba94201101a0b280020009116070f40101040040700507680e03a003211441c43c8044800780e0f24606000c1e800224404031081140c03070407907 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 236485935 1250 236484685 236484701
    0x204020c030f0301030606050907080f07120e101508030f180d1b050f060a022505030f0d030b1804150b03010c03051801090c06180f1403070b030c040603 67
    0x40c00c40341021120b010302c0a203603000b60001c540c0d10f51201c0c002c010a042072580c803500050317642072644e05890485010900070000810403800c01545100d995034002050344010808640301c0151017442184100001c041d0003401102280381003050302c0010b44c160044140c60f5000700701c1d41107514100070034090b03240f604200c0400c81e03440350072101a280003441c80032031442d81eaa1041d030a1b0403614604800c1003295054490454000c590801c01074015030360104900500200c2407603403040c03c0c0004a5908400c421513042f04d50107110325070329510126030002d9640c142c9008ed1740d01303110f00c4a4250a0003822801c900390404001d2801c000b10f80000d070741144004c800c601c1d032080052984241e074000303801c1d5000b400c03110010a581d4010300c49118140d0918118000d40107000344011019070b030361141c1c00907040c81904200841022030003529455010307520010078800f080f540c6995140d0340b404035039034103119100c1e01c203102d0703000002030885582e8180ca105856150741300741002e18220064024007500 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 236487185 1250 236485935 236485957
    0x30810141507051c0e0f090601050412061805030d11090901090509010e1f0b09090c1e0604090501170106031104090f0503130314010510030303090807051f0f02040b0403020402 77
    0x20038201c610840382c0d0f66800d6008950f80e10083c5c40c043c44800c0c803070012185c0075030300e004035021802c00c1010f9030003100300c504179888803000703266145071750514400810001490107800000c0400b16018000008080c190110030240c0811104115601c5003d1030300c20000c6668000c00200d004002d08112503004581c015001c60004c20294070780034540c1d043c80070103030a82c03520207012204514010700511a403450200d0030b9420034540e06201a525540d602e000101c0c0303100303812104c451080c940141300025548400034104a4450f9251852000648401d000300c3c040b0381d48098220790700c0d00050103208201c0750060310b440f040908020a00000d81410784090310000e0500f1515000034108000400c42281000c0e400705d007007421450410403031100075900c01c2c5a40e0628040c4004a40b41d03450761011a60305040c0011901050301d494011402414805042c0340918000100b41e0b1003c1d0004540c0041004410040c1421280a80041b03014500450440e0207051205200604041e401440c01d1891 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 236488435 1250 236487185 236487193
    0x91a01050a1b05060a0c090305070b090105210403033206060702060d020a02060c0a0e012105070804050d0219080a0314090705041a06070f1e03081014150705 69
    0x840c1e0001c04003642d581c0341141d03e0352049082001c0090320348540120070010749041c01519203540c0302d2546d01c941e04d026031150a44002460b0a580e80114115108072070031041c15041c20103007107074080720400300305c506601281c14051b038241801115108130350031a085204042010203045540c0e03408520003080b250f002501000404c0141e90382c0400303891440003c94015907201090f02d002420000c0240120368011710074000c181820303402510b0514900006c2ca440c08404071000086202880b5003400c45c0a103510705028002801d903c8080a4803560241044803420f5180c036500701d03070700c1c02c01c0000c0c403c5a450000a84002807225030082c119030303c3e10b02c2c3c00b28a002c1c14001040b035800e41522800e505610602e401c100c3c6081c18042c0840b0301c90301e2610600d181e840c50700810f115200318480282841d084a07100b0b800c110380c0c50b1034601d0038070b030316403a82c24146003070f01d40540141010366160f2130341002079000040340d0600c00d036000000100500006a554041d01d40c04a00744c000b98811101c2e409 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 236489685 1250 236488435 236488457
    0xf0c1101110a05010e0d0908100203060102010609110901080c0f0d0207022704170f04120606031707110402031005060d0b03011a04050f0f150f0904030c0c091a01050a 73
    0x1020031090b800e990041000180c0c44220b14805880e02c0d000709403e400b8402e03804c808014006c1c000c40c0081d0702c60800d400243c0d6030b47e00d02c1e0040b40101810342024005900d0140c0c1c51010181110150038800400e0b244c06210b80c0700d0b048403138240e0044442c040c200070401c100351413141c0344a0f0060001d0314405410441c0c2143e070075448900070b031540d100d520140d41d001800c0000384440381d490b04103015a008600781c64100481d81c0040a80703e02d00919070004503442420040205c43e42c4103100564000d80c0c07240300e89110f18610091503114031800e40300384490340c1005043d841d151003164010340c0f4106200d601c25141605010140d00501c0500c21419641c29003025691003e00910541030180711403480451003140030081251006090241601c10b580f0130421500707809003886400c1909a00c4000181c01044c0000d24a800001440751b0004070200a22080641103101000881d10031907550201a480325542411180f0159009000c2200c80040070010b502480c01044070b450030b0314103d00810707 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 236490935 1250 236489685 236489717
    0xc090114040b01021e061603090b0103030f0c05070608090d0e0916120608010b041a010206071808070e01050102120307021b060906071109060d030806041d120d06060f0c1101 76
    0x90100c0b40b40c50264002c1c90800044140847e0305104011203810100300c03c801c55260100d15142c140001001d118174200d014a60034041c010070389500ea80901203a14458607540d00904000c010f4500e2004c1d8440c11a0b40112540182518028420013800c060955a1080c034544003e49504802d4010300440e50055005029507000780c0e0701901001d0700226003da04003050204a40d0481005401003512052445141e80d02213029500002c0034031345040103902206c03107541414800e0344144140c0c0300300e243c0003030030b12100203009040340d82c00d03000da903a401044a1a904c21384011110f03003005030496020416180490244100c0050029048a00f402c0c840d0011645075441550186c491290081028500785010704a1940c80311003591200d24010341950040c03c8114041c3c081c5e48110b032a446007130b4566030b048243c04440e0381440708403652029105603105495100420380440d0605007400400c502d402122208450a55660303001780c0e401c400e80700c4c151201c0d84006081d0400c0310740441c1d60086 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 236492185 1250 236490935 236490973
    0xe0c0306060702152104080a0309020102011e0b030c03060c0307321e1c020f09100f030c02160603020a0908250e040f080a020a0210110c090114040b0102 67
    0x4c260b03e04046075941903000030583c60b900d412003914441440000400c0700143d000026180b4451031410042001842c5100507400341803000101d14041c03c41500c00d1078107525640200860310816070a8940403541401490f40f85d83e01150107108200c07080010852551045501c2e44040d0203540c00700d0030401d1681e10005003c410304004a1038400003080ea60031042400d00b04440300040c0c225800d1900ca000c1604d83c0c400e8806004020010740d0100390f600c01c04070203808880160900805200e0003000e1010060301440500c1c0d2072100107403a00081c086458000035140d090b5568070101072002074508038045004e9841502001c08029060744002607070b103020400c0340b002018100c1600980e14844100003082c14241d4810001d1a41c02014040840c6140110700a1182c0292200760303101400c0500744c3c07401004880007500888096000750000c2c1c4c2c01801c0150b1800c005090704c0e40d000320041044034883c028010304a03054100c645201c502d00e0309621408a11406006990400c04200810704c40 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 236493435 1250 236492185 236492209
    0x3031103040f24110c1903140f0d030501050d0b040f20150909070806060403050d020c010e0117010e071b080702100219080d110c070f050303040e0c0306060702 70
    0x4007401e071107601c00c4018041c2d050b82d088201d032a005004e4504107140d1561503c0c040d84140c01140aa0101c4c404000303008414805150080303030500380454024251982c926244860507514000c0d4004d00c061644070b80540c6040701c000400044101c20242c40c1c0b00b640610151040b19555a000c001400103980c0030720441c20059007a845883d2128036005003c107452107000c00e800103031800c00c00e4085640d0340304503481e008625440d1850a46d5605000b20700c2d140b0a03500090000c4c424a503102c000c1aa0000d2404001d190070390b12003010801c0d40d001500c070b24a481010034503040c0318200500c0403521fa181d1080d0310130340038a1300040250541c0b543d803a0420340784c02c06070342101000480009504100a466820320700300d1004009a0304d03070400140851008000091140000048003190714140360040e42c0d0b444400d003020f03652003c65042c02d83d40c414a0307104550003051070203c000f0789481c0101c00d0f81d0031140b07003140900069071400a60980d5034801000d282c0c0c4080140b00c0000581ca0344005085 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 236494685 1250 236493435 236493449
    0x30a020c0a03090e102301020304080a2406140f270a060803030613020a05070b01090f1103070e0d0525031106070206070204020d11030a0902040e0105070903031103040f 74
    0x105103410000079074545440200415102d41201782c0c01c00403c1c1840051444070142d40031161844080040101e045101310f500440042c440c080615040c04200d250105041909501d1540c003031078500c49800541d00700d03100c1d000b020b00a68080c00b0240c00c24202034401603000801c41d0806a41c8403000f84215405049420300d156214810480360704094032401c805405108021403d5260020004103024164404514560740204020517503a0042080c0c4003490b41c00b00c9206601e41c1c40e1713554040245180351498104a0a01105507503c10130981101d010b00101d90717070f8009080f2601c090040c8000085802c036160305c202012801014004a4110384184d960740301c1c2d1700114903500380400d00c18042000c1c503124410030041039005a685074121182d540d8140c60140c0c40f5440003847d84c008106c00350a00010000010800c01d441025901101c4500d200703d81c01c10140550000710b608840044074900e000c03038881641400440d00580782c0b054101692002c4038a825103591f1038188415403980072076 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 236495935 1250 236494685 236494697
    0x20a09020f220f0b07140102160501180c0519080a0b040b090f03040501030504150f0606110c0901090e1e0c040c051c051008031201140a0803030606030a020c0a03 71
    0x1280c81c90780684248a8080c5020482c45508012241d03c1200a0f4800d03010780307a02c00203c20013045800d50079101000c001c14000c64a81610004071402008003c0c001c0321254a007420040954418800410a9136080290700313078568204803d00403080707429186205c000000e0701b000a08c0c0c4104010506016119041800c210300705440d1040d00d01e0009020070782d46401400e4400549280042030ba0212442442c01150b41e4440b414454010002c001c1601c0015080082c081000c0415030451001c6401c980d461480c800c16948001d034407030a00001d900d90000d40c0100401c100311094102c180b44001c00c07400c0c0da88a00b4024082a075541000d0b00800341a0003400c0f00c40c0003403819120f15844140c1c513081c0540341511504690120f494210144ca02c02ea07650340101d25011006118903000d07180d04c000f01c980d6100740175041c2e241c05809204010002c100c09030b84440c03d05011f502c01c403c071341d40c4200542c11612100c5c00c101494000500c0f80c4542c640c28410f24810840c1000f0500e5694007030784540b = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 236497185 1250 236495935 236495947
    0x60302031f060f12020d030504170a03140a0e040f02160606260d0f182607050328020604090b010f0201020316032003100e0702070302060d020304020a09020f 69
    0x2810340700a0340c09a8121000014100911040b401813000440e6044071840c4072200180790076100c0340a00c4c3c01207589448807582c10b01c03803000001100c40c106406900c2d005c010901004c1d051004c0e01c2011070560000b15003c500398041e0409030403402440c1040c3c80b0160030303c910b540310000c050030081d50564100d42c403140204404002d00641c00300161100c02d106182000c072641c0160b46440340c030410700c10000a1000000018800d03141c0c0106056082900d4010700d546003181c004221503210370000c0340e4807400a501000800103040b00c11124044e01411010961001160780c911008460000043d94074120100603610a802403014124103003000402d41141000100041e0080c1e80c20000d41e071040003072007641001c52440c41c0e2a030400303280114001e40740400070302c940c0e811030b01d0b6840107030b00c0802270010710311200086c031041c2da03490034900c3c41d25036030f215049175280e00f03503c07000c0d41054080003d4031070612039800031030384540050100e11210390745001c0c4008991268185844030384001c940 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 236498435 1250 236497185 236497243
    0xd0503070e0109050a060503060a05031e19020d0b041b0b1b1b0d170a0c0308070e180c1306111219030c14040806060907020f100e0106030203 62
    0x41c00c942820b10340a0341141c00c2101040c0e80d00b40900401043c800d0200001c1c80315594512860042d00005e8140c41c0d00d00c9001100c3c4e107501541c04101c805a01540e07c50240800003030100c000c149030002d11044c00002c040d19100150b44000e8400c2c0c82d000e0f0702109110b551034503080f1030401010f03100b50341a65518038003804000205200c200c4c1030207400c102c40c1d02e0b0300d00144075100510b0040489002e40500030500d13040c40c03040021010300b1060030340424280407080c0c011101c7c22860b40a0b40350300b41596600c04044844a03006908190b02c4400d050365071f00c4d20300c00da1b5122540b10040d010303041c0c0307065441d51840103400c05550008000070201180d01540fa00306011451445810b00d0300e0500305260040c0303011540e01425140802c144c2d0b60000d021710f25200c0d4100c40b8000d43c0703103007556039030305d0f2110f00c4161a4642211558000c4c414280030444a920010714145400741e40c1029003950f4000c3d82c2d22401a104202021a0941d01c8120110140c3c2c2c1c24411001e600c142c40f00703508250178007081 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 236499685 1250 236498435 236498447
    0x80c21060414070f140405180603010e0303040f0b13021201060305010b0d0c03060f0204030c0314010c140d0e0c030d020606030111070201050a030506060d0c170a0b030a0b0a020c0d050307 82
    0x8941507040da1010038040010f8200c5030400d2000800d050501c5945ca801c21001618080c41c0d004692103500700c0318401d00e85810011250054805a00074084520b0404180703540380300a941c001d00ca4140c00c0d9420020481d82034009400c14058200b005480b04207800180700e01e40c1c190f02442851355507440410400009110700c420301d100070f0301d50040c00241a220540c115045200c0034207216124801000c4a4255a0441c0c01441d07100c0d940540780c03906e0f41000d200c03c007418000754a480d841c0140d01e08208dc001c0710559024265451402d02c4c1211140301c6801900c80a40c3c1780c000c9200d0030085100303d607810300411740c00c01c54036401800e446c078000003010f00b96242c0342c500807a0184d04015842c0540d0307102081350b50384101c07414080307816194540132441d01d10540310481800e507d400d100c149070b19403184200450140542e40c404940d1a220150021500b40d0321001c0d43c07650003104a600000c0b61180d090b54441d03524040141400c5030189840d00300b801100c01000061000400c014200e50812 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 236500935 1250 236499685 236499701
    0x203010b1b01050132030115030b0903280c05100c080c0406080f0c0712080f06152b24060206010b0d330515070c06080c210604 56
    0x80090000f9450040300310a0b5418441820319051100412480c642000401c1034901c201d002e0000c203d8054407908d108904903060004076000f0f040c046c042180b48900005560050107445a2140030000d601c609180304031034080140c06001c0715005000c0810000d108400d11000000c002040141c82c061009018a000410f0f641899070240001e010150780102c1c40c6900991980d10040c071030f160800d940381e50b4080c00c0301c014111004000441e03a0164230100c81c500685d200e60800426403540d8040050031081d0320306d8511010303400d01181d141d51550301d484800d0402c03180908648108a03540f40c400f40c4071a1103022041c0f0404940c075850341142014403000800151000d80000e504100102103544070342c03e842c80c5200d4459100318202c3c00c1c10418600001c0440e242a020880c120020408402c020f2250622a0244a0780748001c05008002c41d005140e1104d0042d601c0340c180300082c0c94110000c3d0105101080c1482151481248055007000c0070f651020034407080d250500c200400d4800711 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 236502185 1250 236500935 236500987
    0x90b0f0d0b01051009030b072a060c0912020d02150f07050309032401030f031e020c12030f041503270b060f090f0601050d060b09040c020105070516050309040203010b 73
    0x2072141040407d2251001a030402c0162401d0303482a0080d040c559415810b9540c20040400382040203c2000580d61008001c29856107130217070056601c8103004456117071210007035086450700c103848006107805440d00d81c800c1e04c1076239201c2c1401e2072071502d1071586d00210802c5450707500004440040c0d282c2004071003280b440d108800c0c4039190096200c4405008180300060640c2c00110b1308200b007501448441c00040b090940c4c00026440e503110003599406a030b11000d00541c46a201c0d280392810100c1125040c4800c001446c1ca00b910b0107172502407a035529200f450416542d00030350005c102342003141c0d0707203440c4442803040144491401c000541403800307413000744906955440c03000c0071384501d8800c40e840110443c040c8100ea41300c1c40144c8892046400d46d1180502e081e0300414120303440304c0a070100304e2042d50100044078400d40141d080710006e880380e101040c01880219160200c192042d880c071403040d4183e80c18800104007080a0717030802e0b0401c484150021600300c51201c00078944007441500 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 236503435 1250 236502185 236502197
    0xf03060b0312040306091a0f15030c1e031006031b0605130e0402040f180b0109050c09101101090f02010e0301050121021f020d020f01020c07090b0f0d0b010510 70
    0x40c0d5000c240b5920907440000d10aa40351140760080c010002d4118a01610038502981a403030030704c0c040310881c10122070390700c403402d04a49010014140040c0900e5031706405005501e0401e41c24000e03890300306600c407a455048c410307060060f40350070180c0520350045104094001c9007242699804e81b4088003504040c0070000e0030303c042e000d14101d0088120454100d05540041500c0f9400403501809422280720307002820403080800c41d42c1d80003280c0e13144070b000d14010701140c1d0303c5869010035110142d4038943c200b0414007607120b0384c0c6000fa00c1c090802110381032425400c01c074a05070720b094440d6480e0541b08a0341288504041d942c0003d4450501802140200300d198100a404081401144898a0700c0350a02051500710340710b003034841021050b4010b10007094140c8c00402582c541110040c0f00060003171a681d2065184140292100b030442200607042013418800303d1002082d8207280c2c0d0303034002201d81d08602c0d02d46445c009081c0342409031070761400a6044c20140309401007848044010404 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 236504685 1250 236503435 236503453
    0x60f08010510090e031308030307120e030a1818060e070216060e120f071d010608060d08040308030f060f0d0503040b0903030720040605040b010f11070f0f03060b03 72
    0x140040312000d49035031030f200162022001c40341c0707451405441c2c00503118504000002c80c00e05400805075100c2c04c1c06507a02d5240840c184c5034603083c2e88860860817910b600a020b419107880c007a140110b45014004e00f043e906940e60940001c980b001c02038000c2046641c1d030003d0180010040165030f04c020680010451907003c218179450002c00c500c242d00800c511941d5550080e82c560310340a090b42c20a07011281040d014400c095100c0c0c44034031511071150301008010311031400c4014403a0403144d41c0d40307070724801d40c2d108814002052101c2d0811502c00204101c0400000c207603801442c0104a4409140c03047c0c50302200380b00c0c10400101c8158421910020308100203040002103a00340c3d20111641903d8541e040086440c41c05109002070691403003448884100420807075941e6490001c41e000d0040b2596403090004032240c40d1803150004214020b4202881c0c0a000d190031008c0030308040304d81c0030740c1e110840a041b00c0107410541c40c0941c194010014010359000f000c0c08e03451708902902c03002d4 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 236505935 1250 236504685 236504701
    0xc0b07210b0f1503041401060b0406020f060711061b07080409090327090e07050402030405030715060510030209030c10020f06010f0e011811070b0906100317090f0d06060f080105 78
    0xc00018002040311b41100c00c00604044203400110051444610050f02c0c0c80d00d51707402a49428003509600001d10034940080c0944c1e01c980c00e02c0c001e007101c2c80050912900d0300030ba81c4101d10110056403075901c20400021001500c0b21000704010048441c0004040806d0b2030001c140000302d07124030302a044481c106204500205540ca800c0341c2d603500380028802d0023030070102d0411280d544869401071011041005204010004140861094549014000c10081d0140886046000b0203410000b0000301c50386282c001c0d03008140a2100a0456401030310110001c3c1c4180c515000c0440103030040048280003160070081c042c05051031003d1415001e0810b0080890010144a0700034094400b07004901c40b800700d0360241c500c1d010740f90821236842d507460802c403007489070594000b0800e1140300c0002e13600160941623942a01c1d80108044d80880350740a14140e1a002840c80356484180412a0049540c0316142c20b08006c0c8581d0010620b2864181c000115420700d83c480c45050f4144420040c2d00 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 236507185 1250 236505935 236505937
    0x61b04090e0a0c0801060f081501030803061f09060f0302090f0d2102060711150c090f060403050c01020c0307030308071202040b0a030b1f0c0b07210b0f15 68
    0x303038111180004200385124002841d0000c2d460001d022045841004600e44c03c064014a0980720048001c0c2030055403903a0305561214080740201a04c03841d2401480040c03160401103800000c010540c2540307070303400920001007071990840000401c0048104001c40d03a00540010850030090030304504149943d804070300780c886a0649144610010303401102000581c5041503040302c1c0303070440e40880711a0341d82d000c0e60b0f90005640140c04910f13041c6040260800c0080d040c9080c6000c0c0901c80030a44a0442ea917604d504040c201d240d101648400b03540c81503c910f0042e1008600510080101c00c84100000e828090705102c410b00030341144100380046908004111b402640524120307035017815050300403009010745c0e040940074110000380340d6000369041c0c0018081a00440e0000c01c0c4007a0758150302d0b800d0148604403808110446610030116102a15266228240b400d001e2500581051800a61500110000c80e110340d940d480b612182000400055000c10a688075400c00021044410507 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 236508435 1250 236507185 236507189
    0x15060503151f030f020f0d1104050403121503021801080d0507020103150b07060f0c02071a0c01060605030901050105010302072001020a0210031a0d020f0618190305061b04 75
    0x1200312400c0201d003141450b0748040d41ca001c811802911203948a15000004950382d2000764481d026450841001e850111200c40d40b0301d0344503014044414a040074000a8100100254140700402602010001c0e0300d0080d40f10469200b0070064942e41140704101e5015440f107501c000f030550020051220400c005601c0180c005a0705159071a9500c501c0101c003d40100c040d21a04025000000030702c80e24180f0190415178401c3c0c1040c041c020380886e000007141c00c040707950801640b00c3c000c02c001d1401b00104510f8070701074210400d86040501050725003558580d0b0700c6070000460010809c4189042840b0780c0d4090202441d0541ca4895141c50f40705cae082803206a807000703110004003031007000d0b802040007075a40341c1d001d4400c110180c0c0080000d4018940c0341500101c002c04812643c43d680703018903008001560042c4020405031144041c402d0f59000492160031031604c501d8049000d5440720085002c20f00c503001d41c109420306600d0303c681404806401c01c108011a40c3d081c80304042c040040d181 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 236509685 1250 236508435 236508463
    0xf030f0909040c12140d030912050c10060b09120a0507090e1c0807020d0915080c0d111804090b04020f13050a1b050703021c2a15060503 60
    0x14951141e007080c6a041999603c1140301340500300d07400d0100600381d6601544041c3c0b030800d0b9408118040c1007035003541d007034103002840340d1650401c0c6804203026802a04503010044101c4450202000707001c421102d1079088002000004204500246008440030300e800721176602410101102c0e40c1c400e565004180240411107440e18025182000100314162140388003e80c810b41c01c0100d224041c1181d031042d150203005014035282054601c4c081c0b04504211440804150000c100461040383c01120141070302541800c100714610411700540500400340084620081d514014800800040b941c0724154a0180341040221000b1810098581d0fa00c03a4041d11441040d0f5190b40019801c0d40310003a81c02001d51610007404180c0e1959445440e00192050212907512a407200668550040c01c00040c0140c0c4034154001c517031b001d544882000da44050a141c61140e00000c5010010440f007001441210710b43ca13130345130602003034103102e407800312407044d04000042c00c1c14040b940325030701003603490 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 236510791 1106 236509685 236509699
    0xa0306030b0c0a0801150207080a0309152d120207060506310903020c0604420c05190b0a0609050c030106030b030c0301020406050901020f030f09 64
    0x40070703143e070707a203980b602c5a283c80c01035821120102c41200c00c50044800c005000d00041207660840d0f44640c0b16450304a080090008540e001103611f441000110129502c516507041c110b00d98884d1b400d10003087c031080c002e00a0350b4060f065071940800b03900c005038140500c18070358000d42c05407000300e030700d10803400031010001d403078940355002400c904902030b814040300412a030021080030710030b0050f550154030210000c1c4040d00241d11940d4000140709480b0810b00d09c5648030f0781101c0e030500d0828a1443c3c0c40c1c04015a0100055002c4140008184035400b44001000346003030002710940d440b41140c03a507140500300d5210a90360b03401074505001020540a41600030b461013200c0100d82c0d1805c50f0b10703002040b07010f013000280301342e01805403a9001000f0f4070280000c0c005441c0c3c540f84c0940e01c151a1000a1800e4020510000541c0050245900303540045007141c1100104481c02 = true := by decide +kernel

theorem cover : BRFrame.Cov 236330935 236510791 := by
  have h0 := BRFrame.cov_init 236330935
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236330935 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236330935 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236330935 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236330935 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236330935 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236330935 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236330935 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236330935 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236330935 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236330935 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236330935 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236330935 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236330935 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236330935 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236330935 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236330935 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236330935 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236330935 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236330935 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236330935 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236330935 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236330935 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236330935 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236330935 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236330935 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236330935 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236330935 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236330935 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236330935 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236330935 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236330935 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236330935 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236330935 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236330935 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236330935 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236330935 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236330935 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236330935 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236330935 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236330935 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236330935 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236330935 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236330935 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236330935 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236330935 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236330935 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236330935 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236330935 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236330935 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236330935 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236330935 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236330935 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236330935 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236330935 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236330935 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236330935 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236330935 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236330935 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236330935 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236330935 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236330935 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236330935 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236330935 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236330935 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236330935 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236330935 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236330935 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236330935 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236330935 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236330935 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236330935 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236330935 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236330935 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236330935 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236330935 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236330935 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236330935 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236330935 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236330935 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236330935 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236330935 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236330935 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236330935 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236330935 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236330935 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236330935 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236330935 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236330935 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236330935 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236330935 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236330935 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236330935 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236330935 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236330935 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236330935 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236330935 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236330935 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236330935 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236330935 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236330935 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236330935 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236330935 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236330935 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236330935 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236330935 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236330935 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236330935 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236330935 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236330935 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236330935 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236330935 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236330935 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236330935 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236330935 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236330935 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236330935 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236330935 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236330935 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236330935 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236330935 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236330935 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236330935 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236330935 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236330935 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236330935 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236330935 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236330935 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236330935 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236330935 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236330935 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236330935 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236330935 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236330935 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236330935 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236330935 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236330935 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236330935 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236330935 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236330935 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236330935 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236330935 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236330935 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236330935 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 236330935 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 236330935 ≤ n) (h2 : n < 236510791) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
