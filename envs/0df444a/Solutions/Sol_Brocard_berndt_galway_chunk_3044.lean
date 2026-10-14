-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3044
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:29:52.363709+00:00
-- url     : https://prove2.me/submissions/239a9c7e-5dd7-4b41-aed0-211851842dba

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 547302158 ≤ n < 547482014 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 547303408 1250 547302158 547302167
    0x19080108120415110a0812070305090d2007121211070608011a1603090306051806042a060c020109140f0909010e0f011517060106030e0102040e01060e0a080d 69
    0x141c1c1e81604100c00c501c4c2c4490107440400403140107a4116010300e40300d13482ca40b502d200440d81101c1d0003002a05220124082c00000a01c0d03040100f4551962002503002100003007841224a00c2c0c0c03000c5224201d4002030350710800c0c00c008611402041c0041039221440400740044103070200984a6600c011001c1103e154011100d50540e1a01c8410389403142c508250044da42c001c40780307142e0000d0311002001d0304040d0826039050440388541c1043c48660349a1096480d100e28030811010346400c10b80003e0005a4801c5446920360804c0002c00000209070000c2010079500c0c0d0003000100b0203054025056603041500100140319082e0048004800d40c070100740162134041615010b0b185c8080420b04081d000c0d0001743c3d450b5254000c4814004243c00740354007030201e03642c030321141801070200810080a003080b03040404605800034500750340703420b0088009040c5409501039a5500f0b1202141004a4480150080116582c0d01000d01c0d815400c10401e03940a5204031a1075025860803060142c01 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 547304658 1250 547303408 547303439
    0x60e0702030a11070312081b0906070b090a0b0c04090e0718020702010c2112020f070201210c030f05070f0905060d060801112205180c190801081204 65
    0x40780340c103200e11071001203010724100c2d2a8000409442ca402d0888110a50148415200c2d075038480040408e68800d00104440303100f14414076801801c10062100031030542001e16410624071000c031511a01683c48406140b02c2c2650300366010040014100710311086400342d042e4881c0188040e200f11854000c1d25807505003944400e14060390040307414030540e0700944940c421281c100d4080182c0751240d0385c010810343d00c00c20054022170729034850b0409039080340c030035140440510100c551401e505500152800351070310303d1139450307040a201c00c0c0c241a0407030300944c0588902505c0105541d588240075005552000301184104070300240943c0034540d01160a004030383c010386020b6591580c0301203500c01703001240c2040c00c0a60030003c0380348503910014000d250300c20181c00d60700a0040c0070b0750102d5200003a445100e43c08031080320384294015502d60200d0300207821f15800c900d440c0c0c4850004207a190706680703080c00701d03402000412580c5030902490701c5034150210581d18007802d0101702c030f000340e10 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 547305908 1250 547304658 547304677
    0x7051605030a1502130303021006120b13141f0c110703200607080a020c0d08030703020a1106130b010f030b0c03070509061606060509010608040318170a06060e070203 73
    0x7009840755803c0b020326411a001101d0709940c1e80e220584905000e076603910030190343d4403054545640011300c04200c800f0300840c50740c0006050707401d442e110148081e070340100c1e406aa076100c2c0200e41500e002010450b101140700440c803a400c0301254002903508075100c10390650b0034000b20550180f044031012640d00243c903407217058050040c070a03d0304545c054624005060f00480002400d4092040d0b01005e80800b0400d582120340e4014400f00384580903c072050010320070304061020805090003600500404901c6140940303852100101c06441c0013020365140012080e4914044140290600b2060246c086480c5001c403040c0b1316038407000b901000500380b11680c4004004603880b01d11600371101c03080380003029180c565994030b2030328a0300b00440108907007880ca4980f001600d8209032117070324121690b81d15860160380d91a1403c2c0c442100440d1188031016014001007100c007100e960044204410000400d01071102c0e2420b41c0888440c0c0d040284185071b481c040000c100d0b400021680403c4 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 547307158 1250 547305908 547305923
    0x412030504111003140606041206020c1006150201110c100513060c0909180c06030f0f0e1e0312010b1315050a0e0103090c1202030c03010203090307051605030a 70
    0x391603040092511142e01411039010901c40e096034415030341608007910b0011842a449040d0715040c04115440c0700f18810050703012414018030b0003081d466400b40040c0441402941c41c141460710b01102141c903150000d9a240050355824a035180d8240f0585d00c07221007041070540f40c04000c0782169521040c5124030314650340c40d180000e11041c0d00c0080f00305025404078040c010034207602005000044a401049070b058500070300507040c501c1c0c0300802051a600040351131000c41c00c2c8842100078041d0501c100704120f4441c480100b0b00000342c422481c41d449110302820038110040c02c1e803c52680030041c0f01189600c00e006102080d0100f050050440e011181116903030b9000c5c1c142102c0510591388000c1c1c00620300819950f138a40c010008082c5401c0a54a00802c0c0c2800c40054044502d10708014042d140303508010b20078000c02d4648102c215000074101d402803204540000c0c2668030480700209030340c10200d0101c007040810080110b10044080024845a003081c0100e9500d800c013000181000 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 547308408 1250 547307158 547307161
    0x3070f0b070c0e070305040b0c0f180616080301050a0e0c03010509061507031809050709090b0402070f0507090e0f030706180204090c051207050d081803030706050103020a0e04120305 80
    0x725101d50008190000d040501407070203080c050f004100485040c0c0c2c211500c000013403c60310032501100d640019030b201c1a8102f18000c1502e062206c605000b0f1a0010003c2003001e4000d582542e59444103849901d8081ea40d60501e400c3c040359440750b03403020102e542c240050000c0b58a4401c15a07040d90b5050316a2001036a440c0f00150f1a4039001901151030400000c403441411381c0440300c46500904280301c170000d960356008507002c40d0b80407141032000418800081c410004a50042c5820502c01440503003498515161000e020044110454050b44644000c0003002d1480c06000044d40c0a00080d00f006440604c04075102d1107030080007480642d030380f034100c0082d00819950504c504d0b005401049031016030300e403075045002c09015043c881c1c050300c1c4540c0c0051500082c02415a070021700704040c1c0001a44c0c807060140c02840d05200c200d5142015095151020800380003030034058040403c5c554958014031000107095089010700c034002c0d10030030011403490f00c014015a200307803800103100e = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 547309658 1250 547308408 547308413
    0x30203090409110904050304090b0f10030903050f04090e0607034803020306031c4e11030f0106180308041202030705040506030d050a020114160e03070f0b07 69
    0x900050410644c030032082020b100900c20004003801c161001d01108000c002100010000901803003d94141e0203143e80f2a60400c061280d003144041c640300c2d007012410000d15104e88100c039041074012070000d0745e4528030b210200c84200a0650000c1d0f4a082c10080030001c44040d1498001d0005291451810704a03410f0700d80b0b6682c20052010100c00e071003100b10650139840100a5402580c0540c40f0b4486c072020f2024100050300e00c0c2040c0540d44e180d040410100e500c010141c3d00e000e501c030f00c0d88072100007003070b40784107a0400e040b40d000300f0154000c42c4130160404842c81280c0382e00c0300c103e407200e10034010050381102e201001070650701c035410500c1c416a44000724004642050704000c048490104000510400031140c14400900c00c40503245440e48030010b0104640b0120740042e45507004421400220303009500600d2003c40602c00401c03c2000c12010501c03040b02540d600303400804840e10800c500c0e130b004080d82c3d040c6c203080300070380f00300707840c10004406540d400e00400b40c1d006d100003402c004 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 547310908 1250 547309658 547309673
    0x10501142409041406030105061806041d030c01091703150402030c2209060504021806030c040f080d080f070c061a0904060207051c020d0e1c0606060e010903030203090409 75
    0x31080c02802400f212070b042d021204500c00c20f45d50180290f00b0040458110b19101d1060310103040e074644105025a0303082c081001519200084480c0c03081e000c103031007292a00c140003d125071008840003161800540c81c00400d441e2182c03004869030401402030011440da000c0305284958412100540c07241c03640c10341c0580c50b10580e102e4601c01044130765544003422501201c1c100f103e52844041025507603800a001c03e80c031032001c01c0d1214403610011007403d45440405075030001a4056454100b584480780031900c21901c4d04141c4441e800100100300d4103a1107408264455082c440103e46410810409007109404100040600c2e4445458101c5003903103d2001e0141c40000340065410f007020706024000f0b60140c3c0e81075801d8002e050b602e170001d06420b03c0511461100368010074450b04448801c0700c01c0c400d01e145003030b441583ca00c2480c4103036482e00022a0410b008440008800c6d03d880b40240104030034541d00c0341400041801000441e8001c8140da41c028425100810065910300d13207401c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 547312158 1250 547310908 547310917
    0x3080a09141c14040f05040f0908031311010906020a030c020127170303010b04180f06060216090c0c03030509011113290f070c0510030902030105011424 67
    0x41c514400c070152200c22a20303200ca680440c03015a141c0a682100500440450340310b18010f00d103c0c1011050104440c1c207141d4032801d201c00c07845000082c42421661a036942d03174410343e070301d400d45256075421200b4000b0040545002d2282400e040851601c2c0031006501c0300359003040030341032124100e041d43c15a40510a0204041d6620700340352002c1c0850b0941e0b031640f01d400d000e020740d0840010030003010010000200c80c140c8111061080c10246812416070300c00c00a0b101e04080b41d030b01e83c0907a07190f50390540900b40203800b194010b0800000b044040b5200300c0c01540c4000b0005042903c0041e2090b002180f9015844e01440c010810765907080200b4090a40c0340b40700d85243c180020805012540c3e000b203a070559101c4440e080380000710b06500004040041400005050100400008004c9140007002e07a80c2c440e1f1418024030750b503000007401d0105c80345001c1002c03948801000c0b08601d020f02c038550250564201c03a1402d000030b0700c0032614111140c0d5056000c81350702d50b0400f08580c88030f0141c9 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 547313408 1250 547312158 547312193
    0x607240207240618020a1404081506091e070e060a1d090c1b0703020909030a08070f080121020310020d0b031f2301081b010203090f0112150b04080c0d03080a09 70
    0x7e603a91940c0c0c070760302c0755070302c82d150402035840001101003020741c900518058040c2119081d0100e1881a81840d9540b01101070700302c2c0c080c0f2a101c1d21141e526190b400c05003500c613000c2d4490240c4005c9019042e01c0d47e0b150382006c0c80c402d0b036070b03075007008003100b161010749030300f200290010700107140a10b58030f42c82c14010340c001a520007035070f1007000056080000101162021560b5030003441d101e182054681240b15401a030114020384014400488501540c0805684102c1560704154950b0017181c03c15103000f084031300954001400c2c2e0120050340c0107100c904c0030f0644c0100700c00341d4014104040d6000d002c41d40f17006c554403021813003604001069107090818054490300d01550751091541c0d61260000c0503100340742c40706411015258004416541c03224009081246041680001156006900f030412541150b8850305890f110095024003009042d501220790355450030700c0f001174071340203811420901c99010260708000181d0b00c0074038103070020302c07046c2e010503110100d1606280885181d03140 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 547314658 1250 547313408 547313447
    0x90507091505032d0703050c270a05070e0d030e09150a0605070b1e06190b0711031002031b070827040b0f0607240207240618020a 57
    0x240300450402e6242c0c0307132603000c2064100640d00050408141c03580c00600c005071190300049042c0303000b41030501c0e95100c00041201c400c020f200312003211001107002270307e0620110b607641d0100700300960400f05070403000781d017120408181842136030020414462440c0304bd00407070110020412584982696040000c80186800003268a0340401803e0b43c12007581590315045210200d421300021400e04000d036501c5002403178907580c07001e060004010311200141407000040c0c200241c000b1840c0c01403e5490f1080c60850020880101014500310000d40c070004c45601c1081404501d401c0c000c01027602c1c002a101d00b6854940e40e0410140c18050100c0605c840b1210600412210100106070382c00d240c42107804000c103c11540c2400703040001c46542e41e401c0803042198201040d100c400f81c84200060000d09080051100d120344240c0c1c000d084210f1744240c0c560311003000903444d2403120803100c0200e082040303010304d0031030140d0398100080c01c0b080005038001200ca00c50f03440b460300802140342c40e004 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 547315908 1250 547314658 547314673
    0xf0b03060708150a18090218010b0409060b0f16050f16080d032702030a050a030c030f02030c0a030507020d020a0f080f06090601061103043609050709150503 69
    0x4001d0690001203c88920424500c8075080031464440780d6101581e01c0404401c1d512241201520024001080241e03841b6403002c0c8162803c40681d000e66000e4a0300c8441217480c0c80c80d043c40c503800d032100c580006105000910400111840f0300055811100c604000d500c012406818040d003441ca18210554507402980000c00b42a9200c40000044450041c01c541e036003420042c044044803000402281c11000c440c041c140301c2039440d42211081800141071b01c0b90003d19548507490702c402c0d000b046002ca804a40b0718000d15401c40003e0b003040000c0c0c009549042a02c284054988480032002428030001282000941d21002039098a9540c0a403440384183c0e1206d022541c050043d118282940c800d541c0000c00f05880414010f010311194001070025074207002d4142d80c0d9030706141d000d0410348000d010026141c4800380c040e0442c0001c080c0884854118840b900c0c550240d10544a0801800d0110850000d200002d0f0081206e4402400040898003245038008440482d03010940c14841e100 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 547317158 1250 547315908 547315921
    0x61c0510030c0602011802010e1c110306070f08190b1003060302040b0f0109090507030902190e180604140106150203210103150c0302121f05030303090309040f0b0306 73
    0x501a03010740340140210403005607076079012030aa80d081d590111450400380e07800c20055006d203202c9010500010100c0e041c40b00450300403100711088400c1030b2040c01c90103600030072a003810301107903802510304d1a09080d8009100c0e4041e1500c1d201400c8c1105000e01c1c0c5200300d42d0b0460725030181440542c0146140c000d4070340301c140100507045a00062348502e14000007801d09140900910341d4041060f100d5003801c501d807044482c028a4001c00342424580c8542c1300100507507803403407078101101d05009001401402c01859003c8401c00824090b0f816620508042141c40001241d0794402d510108044490301500c04650140102d607101e1000c94084804080702c054012003d40351400c18807142d0807070a040414030058156082c031000e4400d441c107200444021180b5000100411031904000d8134042948007464030514040310000c88000010318413050110000a010300102070840046042d0b080124840c0d07103906c5520b10403403059584009060050032141c000c074403004402800d0b2004c514100c6c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 547318408 1250 547317158 547317181
    0x16080d050c2107090533180d060603020a0303200601031a15060a02030c1216200a0906050414240d02040603061d0304030b0103082b0b01020d0e0906061c05 68
    0x724445104400f03268644406c8922001a44c940a4042c43c0e1540303104813a4041c0106e8040052080d90031503211f410100250301e03a14400c01c000c511981e60f0520b11030318104103800403140740c640c03200c094116000400109400a0300101c20b2014a000200651230f100f2240401c1300070401041d0300140302107556040503402102815440320508151001c2007030007628280c451150008101030385078442c0034480840c2030005078000d500d160070845186601c1d20700000740c01d00076641c00fa040482d15040144414105070103023200039910035031001d4281c141940700b204000c4a1810000b1a07058150041c80e56a4400307010b036011940150007040499140d080900291103110106070f04189444c1c10098845c07000030031581200e8111004965903420340d51409880d40c01403400e4062100d1040269204120350305a840e00200030318800201c2c0c20700c4000281c1032504100c8400b0500444107000c080b50340718140300f9603004604a807295a00c800e200301d040a158045504440000c1c0390508212090080 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 547319658 1250 547318408 547318459
    0x30c070507151709030409020c0304090603120e010219020f030321010509010b0a0801091d010f060e011a0301141804030c11040509030a0c0816080d050c21070905 71
    0x15903860610003d0645641c0e003070300d5002e441c084e056500400c030401203d486907001e0304c84c90481005032840c050751008011709841c159002510760b01c984101c0c5080560700070b850b40c070f43c03000c0a0000c0e2420007103007190703607510401105001c2e015510031079011046039014000c940b0040c0d00a403440500c4c014a00001d014501d09000c2c0364051142c41c000452403001c800b0a980441a20340e80c1c1c260980e007083c040e00040c0940b001c1c04900034001c61130b4282050003e0064601d1200e1002e40010064030340860444100d070113a1052180c4a1940700500a41c4203032422241581e041d24800d0610324076050100b808241d0140703110002c50b03104410300c8100340d4040203d01c04140158182907030810140200802c0b40c2c4103684401c1198010041380d04480e00070034224041c0c500030010941040c1260101d16001c00444104a0340218006068190101907118113504070b41040780c01c609001c40c1010071000f95402039141840d4a201100041d80c9500c5003445401818001c0c0040d603c85003815280d2102c01c41 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 547320908 1250 547319658 547319699
    0x60f03160603061502060103080708070528050610050102030f0f1605060f070f0509101202040f091802030c15040902070303050a0c08090c0f0a231905030601050402030c070507 77
    0x481c10381130a02520003d85141600d401402041c40d0000c1070b5100c64490707004c043c0803546401020800d41110000c030210007060207404041c83c190800e603103482400c0680007400c0307030303800d409082c0140f049907400801d888960341481e07186940c83c4520b141646181c01003245150360a0440800740741040b1000c01d200d8022000301d082d16040d42c4505000380e41c158440f484860020708103000e41702051814000d56020031a49042502c0f0760300501d980350f401e9900a420004640741410b8040106984a120301405802d50642040030120142c3c0002d403074200b85001613114600f040e0543c443c0e00f15030001c550041c0000b020455403450039133070140140c04100c40322949103140074070046071540100c0c0d80c1c0e407140c502131028001014180041201c054620321806801910760103000c9500400444000c11407891139207a000d242d006a01006000c1c10030018030300f004403800508000c1c1c0d45000860905541c0304960150312a41c5610340d42146000303100e80a0424881c0200c0000e801d1280e4403500740f0f40c80b = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 547322158 1250 547320908 547320929
    0x2010b011e050f0d1d0601050102120c032b090f0308130210110f010204140a0605040315020d020c060f010326090907090f0e091c08060f0316060306 65
    0x110381504008640c0c8403456010702141082094000224500000301030b207aa9110001941c03540d95044004040010742484285501100051000750380400100c00543c1c4110511032034000c014814640b00c1c000d41d5180d06512402488140000d80300d00c0064800d41514841000408603500f84203112400c13903074041e000306001c0c4020618601e10500c85a1300723980c0160402da00302d81c0c2070108880d07482c0140800e00d81d6000d1406182c1040c502800100010058203160219800c43e03403040000d0000903610060520408200400010b00b1413040041007650340e030380050720343c94400400000783c81804001845c0740107050070000342e07400001071a4140c0b8000c04105404281c0c000c5024146411000980003200043c0010401c030300d001e691140c3d200000f40b07840c10700d06aa0755140300c81420300d90001b00280b4422410443c040d48108190320040c06016000740e00a040720b00d01410041029006a0145095040d90381c81614100041c0d03044210224090b0401a039070140200207064030b008440034107 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 547323408 1250 547322158 547322177
    0xc030a1409012705040603140c040504020307120305130e180c0105090402130803070b0411030309090103080918100801060b070c05091506030a0c020f070e0112080c070602010b01 78
    0xa0900d0300640380c0019040c3c40d890148107004040064000c491208502d0148200380041a19101d9009000085120307801402285240510090400d4001d03002c09010b640382800f00b1015030340000301841255408100c00414a00e203040803500d5101d200420301044915440000d4064009110140f240400344481c00e42c01e428105100c0c1c807a0043c11a090000b9001d10078030680740340543c0281000031070354064242290751102b8050a54200100c26610032a42a00700014081c100801740c038180c904030083c62034460414001000c0800600020300401c1e0082510000d50300c50b00c84628204000402c80c82c4a031900101c1d040c0c0c1740050f4000c5819a500304030000500030b498805661606902641d5440e070b0034180350a00c0b20380000241000f03061203045030307250881d484c5d04c2e004602a56031000e000c07452012481d00a0718040308000084002e601040701005800c025100c0c460550344203500e85131030400c3c0343c10500f1650240003d030300110300031038400046050b015404860000310a89500240c4d = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 547324658 1250 547323408 547323437
    0x140610020706090915050307060807021501030206030112020301140a0516180605091503070e010905090f04060203070e0306150307150f0c0609060c0e03102318030c030a 74
    0xa6881c14892800407400010f002d0200c8007007600140241c10062110304444c5907107000091030818141c1c000004182c030070b001d001780168141b00403640c0d40c1109925281c59459540842c140e4881407140580c02001e140d11001150740a4004c8501314581d0503200b1003d0804180b500e0007440142c03008411b00054071100d2811070302a4503024807403000101101d600600d060802d0b125075004101456105c0400400948000c0c44800a540500600c2d80e03011ba8580c1c1407800075040805a0b0000d503c0b81c0014410803018904c2842c2103a40300d5480790300541c8a49804009035080b94503076281c81c0c8d00d4041d075810071000c90807104650410240440466690070780d0f50612000159030042600001b07035104100840e49400382c02d200e0f862900c02c00c000104410380f91180c00c21640e03e910100300007815006a090640b4040004443c03400e5865810486811252162a51580390781490a00100c0300b000288061145138019681e0201840039259030b42c0601600da84c0781e6002451900214071403444c0c9405 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 547325908 1250 547324658 547324663
    0x60b010e0102010e10090203030c030307020f010f0605100f0e060406021018050a1b0b12100b0903070905040c0803040b12070905090a090510020a032703140a0309050114061002 77
    0x1403020f01300207400014240010b00001c0c11405005030b0b018070040050651005040000b18400c201c16800f40c00500200c0d640b40b400d540c1c168119207034a03410010140820ba0781c00041c441c401c1c80074140403c0d03078400d0344002c5e18840b644059a60b071003c1c000c68001140354001c20b014040039a0f40c07074108143c0b01c44510300505440304403400703022075000c4201a4001062002121110300e42c40720070581050380c403108070a5950000710b416241d0042001480b03550301248107444082c0000301c66440c102003c040208c5e990360a0b42c491401d1441d03d4a01040034081c0302081400607003080c0c0b090300d0740e440c0c0b15580b00115500601c2603504203c000000501e000f4400c080d030200751071005042e00581c5d02c500c8a04c0f009400d0590382a0b425014038103819001c10520302c010601e040e41510041104407104103034040080c1621038116030522030098190010354002c0500c03040c8029001807036140e5012601c103c006000000700200b486d8a842031820013000e4042c030440c45031604580e9649030035080041240c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 547327158 1250 547325908 547325921
    0x501031d060f191d060a051b0f0d05010603060302120102030606040b0a120501080f07210807031803060207020f0103020c0d0518180703271e0f060b010e010201 70
    0x340ca40c106034081214626440301e4150030002c600740700d10510002141c00400c494401210a00c140800079803c191000117000301070b80503600032010001e529240192103004001c029403800e00b01400141c60400c0307098801910600c80c100c0004010315038403071102070b00600b4140021b034813622109140d000d400e901402164414038019080034203041c5014000703004c641000700c4e41c0341409264543ca0082150a00c103050013065068000e1101c00541c20285042c4283d40e01300c4070b0040c0120b02e881000b071102c03008542e0040d502405080d500c1500d82405c032500c020303008280503114030041c000800d0081580183c18480c0c000c54058450713822000040d003c901c00c8162006250f0441000c2050b414000d40207401a0000c0c0f1b05001c00c800080e2000880c000c0f0030306104d03a07541c3e030154244015503074140300707007c2c01c0410f4070800c40d00840c940f041044640d035100d8000301744035100c91100c1d501103004544021103550148516000310810314141000d040c002425600040d841c84040019602c14003908 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 547328408 1250 547327158 547327211
    0x4090e0f0a1e0201050702060d0f0509160b07020307180501030210090602060402040f0612030809010f0605032e0923120d0e0a0f03020f0c0a051e0d1506050103 70
    0x30b0601d0144810700c911a0504410141d040c00380a2010b02d0140e19410002c0c051400e0782080000d12008807806034003255806400c0102541c41054001d0707a20545001031030540d100309030a10b880700400c0c0b00080c0f0f081856008440000007a040c1c281e241d05a6801c4941a0381c800c5444800e200b8181b40115201c0b602c40c03003902c00503801403011402505050b8002c00310b4042d01c50010880c01d84682c000510848000421400116600200110b044080c411031070f10003c412800d010032458600003a41e2002903c030315810000307241601d00501c0c45c07821a080400e4008544c00e1080305c0660070500c03186000702142d41104407421001100d540008101e440c4180c151402c91400d01a030f03001d095005109040303807510b0f14442c1e0510200440e8017034101029180c031a40c02800c5440320a50400e0501d118880f0683c09120340310800e10455451050000681e030007488114003240c4c0510000c0c4002151100250800c00b80620b407400c0140340e0340001042e0384082c2c03414030404148140c80e800102c0c0200a0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 547329658 1250 547328408 547328423
    0x5070815010503030708091c0206031005011205010b040b0318060c0403120201200702040b0303120105030d03140a0c180b0301090605010908070303081b030c030103020f010c03020d08060d0804090e0f0a 88
    0x20076003140382000710303440010723074848034280044a260b021510710f42c0182c40c2d0300b2400700f52407410845580e210107520003102d41c102d0140301652514584150500417402130304a001c4001c400039030103002450700c004041054174100ea1050400300031060740c0c1d500500043e1500b418400301da800b1a8014000c540c4a0509520701ea451146540a6440385800c24181242c0c0203480300d00d0002c1503a000c0028000250080e02601042c1d4900000c05182550342030342c8000385410304588880d0240b14000d0140c1c4a0102500807420084045c000c803019202d851079040c404861510100d020710f51440030f0340c16507059000c2044110b8490006550642c00d030320503100c1c554011641030002038801c0780c880d60041c0c000b150001c2d00303884044103840c3c0b681049442e0440d00401000400551074000400d0110074405e081c494205203554030001e40315100c01d0880380070b121420010030b500d515140c401504d0580c05c2194152602e48031040240600390307080300820148540281481e484402040c05d240142c2d00071034 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 547330908 1250 547329658 547329667
    0x60929040c05120f0303010b0d230f0406060503060f0402091506091e0d050a110a0315050c04050315100e07080703110706020408210f0a140705070815010503030708 72
    0x80240ca83d51038a416206402541011450683d0420203540a080641c0380603403136415030030101e401c0300c0404100e080724000c1048152000c00002000c02d03045802e05407031000d15501d6003481c00140029500240e01445200c041203685d1004861190143c0e00c21102ca400da503c80f441c0075407042070741050640c0d01032410001c0440901d40045210120304691a01452840d8082c000031174541c030125007990b854218000b55004c00c1300e0761050a4036007004031000f1038141d041d03884034012035106042a100d0503507200c02095040308860b059a0042c1030041c12200e002810924506047d40103454840c64003602c114085003848506200a00c103140c16a6010110b99400004074050804006458290b1100308000340c00700b0000d000503c050301c0c0e903800500308a00d5080342150841d413003c0c0d18220442e401d100c08425066440c045440c24042850564031010514600d100c0603c41e8540060191040440014000c42c0100d03030340e207035102041c0041c041aa6030b002070503242e20980318001d080c00010007 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 547332158 1250 547330908 547330919
    0x105062502041d0d020f011109100e0301020a0e040b0d1707260703020c0a050f04020d180605160f1211070f080c0f280f060929040c 58
    0x201a02191400203102280d0403520714040038003021003c0c24100395400c800c406241894040101c0349282d140c280c000c00481c00c14258a44460244d5440d19114081d105145401c6a224604048054030010001c55481e4420480a00700548000002c1d00450505100701c106240c200c2d01d40c08103039009001c0b51071413800c8601d410f5090340103050450780a669624040b40c0c10705180180c00e004041441c0b61695644541400b034544107080412520848141400380304640340d06402d01041c8805a40268035030303801c44044400f405810f49540003d00700e0395200c00511003e500b159005100200c000391121190107000c40d108206a04c0000201c0e0b0888054081c1c5500f580c8201d45003900703141c40600701040381d9110900456400d801fa00c4152005c2008009143c0510480c0c0d400103140000300310b080c4060000101201d00d21005030300000040e500c0e00305001a20400c0315a1a92014003000403c0040c5040824280b245403042d0100113054001e101c44420329020a02440d00071511007101c80c50170 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 547333408 1250 547332158 547332217
    0x703020a120807141e01090f0b0709180906050f0f040b070509040213030204150e0f060d05030a0305151509150d150305160617040219120b010506 64
    0x3081c00700e851640800c1032102040c00034028809568507035019010301035407004640c20118036403a01400d02c1e40742410440000e01c03103091506101c1c0e449128852295a040401d68005003c0d500400c00120103c070b201814044c45d40c0241e039010711449080245417900c100d400307017000e421030301d50303040c400c0400100300800c81044040c0c0d8806203a2501c245000d91345000b050036a08046400e4540380189241070046140c0360007244206888444041c500a10b0080f40c2d03a40010050b1017280e5410080c00811901d0315624070011943d9041b0701201d5a40382d85010040c0180304c121900442d48001c02110b80a501e442614032203245c1c1442c002508160f0f4180030890584d03d00f001032100c0302410002c500c0e800c900340c0070308082010350700410071405145082c005d0803e003041a444601c0c0008110501055810000b0012a0134512016a55550702e61012075146a140c0030300d03541d091007403640020101001103402800601c121001d010300e9aaa20500049025040510001c03800d05000c1000c2c84503130 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 547334658 1250 547333408 547333439
    0x60702060c180406180c030c0c14010e07080708010f1a01120603060e0309040506060a051603180b04060e10050d020d0f0c090515070f1112060c0307030e0703020a 71
    0x201d6a00340318003942d2100041c01c580d850390058161011203006a03400071176602c40c111089107181030a20500844440041040403081401000b82c800f41d800c20313058032400d40c400701c10b2070084411180015142d4100355a58140c9100d00d00c21503081801d04056844c0c9405070b00140c1504500c400390002200005440070380d030210444d0b007201c0e51440004042181c5024501100000a000c0e559580c00d210034801911001404940689001c101040c00319070b2100448800607502c1842c05488561407500f1620382d0300c07001e580048882c01c09004940c220044c001001203136145d440d070101000c401800d00c00c03104502c440c040b000c100e09121a80c41400203400400c0ba00e0ba9852001910782e021410700d00440d5001c0c0103101c0010791101043c422410724481c2c044012910124403810092190b8030703040c0d0b288005100800c00c2c408425180003584800508001645902c4107035611850148040b840d6604120f51140000c0d0500d803400c6882540410f60300c0540390050201c81c080c03410642c0c00f01c1075100 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 547335908 1250 547334658 547334677
    0x21902070b0d1a13020a09051e040c0c050319090e1326071103060c0c0604030509130906090506100812070512030103030305010e1015110f0d020c030708060702060c 72
    0xf001c1d10b040f50140ea81400003041c241040c00016110114410028107a44054010a0151000b001c141c60b00c10002c510310b0010070821500402e07510080c01d0100c540c0e000101000300749100224840007610492500f082c40c2d48482c0d5541c1044590310026149620f200751940c14003545c0280619003c2a00d40c2d01000b40403651400c92050b242d01402d51034860340c06403100350b4000c1c0d91058140b03018501480080d8000e441c03112291f0804111070ba0043c0c8442025000a0a0003000200c0c0041a01c8080c0f000d21507501c114402c00154480b0f04000024142d0082e04a440c0d02072100042c1000015800200580707201c00700410144820800b844446e44c0f050100b614288100078090315408907002c01036003e18469a000300c6c155252020141c0d402c0e0014100303800800041d48203110045101c60480c2c0160f0852401d00074040e40c0203000360a280c1d0241c419040d50040043c00c0382292b17000540341800c07010640840d51010b5448011903121101034458000513000800400d002074003d1014001244 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 547337158 1250 547335908 547335941
    0x10c032307020c12011a03010b01050f18040608030c01050a0c0e090405120304050f07050a120602210106030c02060a020405010f12020f0a09080c030d08060d0503090d06021902070b0d 80
    0x45180000700030a1800c44002d00701da440f03001d808011b84a1300403000c00f6200550082c8046203403a800648907002c1c03030360880741ca280041050320000b00c00c4443c1c0c21a804010b4400c0041701d0704c81046640742d902c543c600c0d1081d907007030802061000c10184a1581c0d40d510741d81d201c1590f1651401084141c40000d4002d4400340706030000b00144008500045000790303c1200100401c203400c00549040ca00680c4c405480750000750420011a003000146420340755025000581d01c0d44100706c5c034040496803c00f2100030004a00001c01d103281c01d035001c0c500520503a02284c80316641e4411a90603881240542400641d520948064040c016400d00c14050807415000d41810944244492103400c103400c8840010404101013000e00e00901900715020700c29070240901c02e0010070060000c81015203024098040010750b8414000c007031007602c4004100400c01d030300607001c81c1807500103074018203225154401402940581240001909801c44001c40003031810316452540d37540c010003000040c0c03400c01c0d = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 547338408 1250 547337158 547337173
    0x105030621100b0109060c020102120306011107032402030606040306020901120f1407022a030106121101170f0f06011106091006060203040501140c120f0903010c03230702 75
    0xc01c180301d090000081640c0024400303004030001000c003800380d0b00c10410300c0044da45c80c0000d82d034049021030340c030035059580955030b460350300041fa014920552404030724015845c0200404c460054805d07003c44a23a8400c40d0303484040b180604c1203202c1601c060b03902140c02c02c020000501a030f000703006440d405040c60080406c0b081d01d000140c03120182d0560540f6070745c2c1c0c016500107108401a0340c100c43da0744010454900d61a03600042802c00041d248006a503140036456166001d41081e0042c1580c1c90610005500340c0c50014035250700b05500e10702048019000c3c80404203504452485a52846900b003519211041e4038180f40130701030703c0241044405d600c0b80181c44001c014141c00b82d441c0700c0c0249801c00d150112401181d01c3da0b0445400c642041204011680c0c2c03124004100c040541200703540c5004e41001d180c80c01c209403409842c02400441d640b80f0723122400d4060444640f09070b00901c01c00c4a80c14044049503034400400d0141800b1200070b01e05c0716000f81003540e110f1024011208813 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 547339658 1250 547338408 547338469
    0xf040e040501090f0b0403090b0705030d0b12030408100b010e0109030b0703150b180906210a05070e0403140307120207021207080d030e0a020a050607080f0406090602160501050306 79
    0x640344d0300d10081e070700c030840305090004059020107403200910074100500d007443c481c1d644198591144002d040000d5440311040d40241da0b81d44000b40f81c0310041d40440c5c0da915580d5100716141c07400304440748401803078840081c2803940907140081700e031441603440411300760950b0740e0034904400c007410312410955141600341c8441002c0f9220b0f000b40a101807100c0c0c03607801510520490301c260314010f50140000109100082e01d862410042524201d503042551b9462400c0d9a442c00880c110003070b00743d100301400050020349810001e4019030082d07882400302484403c41c0c40c1c00388020384821b000180f00000848030030081340c0c081c0ca01107200615582080144130007040c074062003034221925541004001d2001541c040c800d09100b2401c20000d0000c41020340c0000e0100c19180c4103241c001c400004014040000c240c8c01c035184040d03a0f120705900e5586074400101208400d004001c0544101c02c4900b4030726054815040448005940c1d031807856035414240804000c0c00000018204910b00380c0550 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 547340908 1250 547339658 547339673
    0x9140f060f0901200309190b0c0702131406100c0c060f030e0115090f09050304091806110703080f060d150f060b07170309150402180f0a05010b0f040e04050109 70
    0x10002c41c04d190751500c90800611700c9052000003145e2900703074102d12100c0c000050a5148560f803254035040c82580710f40150021885d11a002185000128503003512018208002d00c0402d010f41c2003a80c12040180b032903001522069001e04000c0d1041e201c00c407080124600c5947c8070b2210510520340800d0540200084a00791616110505040c90b8120f03030520403000ca921038280c00105070343c0184a6442240c0364140c9a104074092184a10344961610f0600305440e124410b402d43d01800400954813070090b14143d941000c00c0840000302d260300410b01c031608600185000340c800038007441c2c12f40041c2c2d40d00400c40104120110242d51151011000540d0300d104403c0240703446065140e69464602c2d0000120f0710301921010013138424818801c0070400010400480900d444200500e9280e90000405000d60075250300e0305240d0a400b00314904201081c03130360080000c80b5040c4a1662907074044001030240b00f508204503202404200030b0b00003100301c22a000b0b8082c1000040c0301e6515140c0d040d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 547342158 1250 547340908 547340951
    0x3120a1a090414011a060306040f11070804051003050103230f1009020a0f15080604021215011d0607020d0c0b04080307120c1a040204060b0a0309140f060f0901 70
    0x121828814540300d2a0694203004242844004460313860b21400c0e0100013441e00d0102601c8c082c02596140d0601070b1078500d42d4456401842e062441923110301861500714281c1d406030003841c2c01480d0701d108540c041c0b4042c1c000d0781d050384d9000400742030f01084100003845964250812448500c1a00c0d00d28104c01001e10602c140003050000100704c007030040c014803600f090b140c2c0c4690031401001504112440c052004400012070350301d8051101c0d120700c400100640a01c03001c0c4090304c1c140780148060036500803c3c08103940000c0c1c80382c0d41e00e81625410b01c5554044000003642200c0200b04020051402e800e0241d06184210420703802151241841042508107410440465000154101c03c4c03000d0900e00c800817801d245000d1108945070750719003a07014a00b401c03d1100c0c07601c8201180865441380c00150140c0720740300c0e034180c440090701c00040c0a010100c10580ba0050340312103452007917101040449058142600503e01511280d4002c4d608450082015006541c0c0d603030452a810b4000380d005 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 547343408 1250 547342158 547342163
    0x40f020a1403060115080106050304050709020a0503190506010212070c0e04030507200d0f1a10090b090c03062407030c03080a0903020a03030e1609140903120a1a0904 73
    0x3150004400d01c02d1600e00003040e00300c80300c81604030080d0203900f43d1000d17106042d6603085c0742c5144c49854628125180100a030404030b10640049955014668084003542c0b2507171307804500d00c099442c5410300c84101c50059a125006800070903054408028113801025482d1003103410580880d07a800081410361000d03201200020704c000b425505110900003942101c8602504091303181031400001228041400d400402c9152546c4500085c41940380180c02038200e04840804c2601d011007814031000c405005135801c0c286041102c0000381442e524061041d210600c510340b46440c1d40e801c125520389a00340b681800329070940c015003403000030740140100ca4425203c03220100c2652070090004140204140020751408020f100406c0c0d000528003201509410000350703000100c1103040c207040d0a50080d01c5c0004004a00103001050750340f2810202522140c181105e44520340c02da51244a01548244031500300b0003c1116216a030f800039440940d03241440c0140d15440d00400d40d0300b507045400307 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 547344658 1250 547343408 547343429
    0xf0e070305161d120f0604111e010f260603010c02070e04020409020a2439030201020f0a0c060c02010b0a1715090f0c461e060e0a030605040f020a 64
    0x70700040000e0310001e071800c16411200d0b03088200300303c001d45a100d0380e00d404072410806880312f43c403030f014042d101d8401d1114044051a964104400d141045000144c0302c450107513107020001080740741b0101c0c1c402c040d281d0b205041d01064a49408101c05484001c50a80c0d1220104500140114198428024481043c01c4240f44030340c6400002e484c0c941d00c0200d515001c84c0c84601c01482c00d0384040f05598501310190300d900c807400c641c18220300901032001d142001c120001400c1c40c0c241d0700040b80000e2544540340030f1010440900c07040342a1964480020f8102e103c0240c140804603000740b0a5080420040481d415042c030b410070702c1041c00d0203981907522900103a1a2401449080c0b00c0c0b02119501039440391000f6141c003005e0013121030700c80c2000c2e9480000001418190360301c0f41501c9a4030051007904082942c5683c802010802d1304d4840d01d03031004400b84001813541c02203016411515000340b480040b680345494500103418010400c44501424600d2000140c3e2000e6140000c1c001c000c01 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 547345908 1250 547344658 547344661
    0x4090507181104050d0609021002030c070f06020c010f020f0709050f070305010501080c070c0b0f0c060f010312080405210c190b1f0f0e070305161d120f06 68
    0x140a81c00e034031001214241d8030b04000341190106181c9045a04468007554098842103040c2485c10007462100d0000f58451102844801415400000340504003502016210075070799460004200160b58840c0300013580040c10220001d6000b0203001031400d40c41d005a8164a10350010305003084282d030080c0962641c1c072800c0c8170000064501d1a617000460381001c20030f07541400001ba10803000181940074680b1f00141c170404100e51080c40400a00503400c0d217980300d0f02c10b01091181070304034a0742281c9c24818035001500c1e440e076010f0090f04903908040e01810020004008988082d4002d0041d1183e106803039251035030b0288808042440500e02c00e0540c0c80d070040d0711906042c030035201c1c06130035071903107840c0d810000c41c0242c1000da801242e8100e41da000034150517904502c02610b0303071000302182c451010008a9a0741040b0b07240c480c0540e0365042082e955412960001ea24400642c07030001078035080054010600d0002250b1061001480b01043d41f90541500b403800320b024100d02440d420060 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 547347158 1250 547345908 547345919
    0x304170702011404180b1008150604050d0f020906150d020f0c0337172721030103034a150f1606023a0c0912050c04090507 54
    0x101b0b0540c02c200c101c80d1204a41c007003e00003440b061014207031151083c01810002d0a03980d4010484006000240034600c00b4030b01810001140038410409074001e85001380010014582030865084c450b0882e40c0362401c00c07290103c5030000750032000c0020803405041025420020301003020b411483c1400e0203c42400c030003149807028440109200001c4000080258a20180c1204000811070300742161000c41c1c0e07480c960000a4209440303020030401400180c2038603201c2c00404c070310380c4a0203840300e8900b400c0134040035641c05120901c0b010380054142c140c4440c0074a000640142c0b207500813034240540c2510f20400000e00c940c410524014032445071440310383c605000040c0e40300408005001420031051100706003551040020400c0d41000c000c8281c01000680e506840350400d1a1240030702800411059005c03500b004142c4044495080c445098070280c01c0c000d2041c0d210303503541ca00ca4402d2900c8080c07a04079801c100e049400c0c0c040c09554051540350307480b42e400d41358062002404c1013490f29 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 547348408 1250 547347158 547347161
    0x3050a0203150c09060f0d1d070b210a0b0603010b0c0c0603060d0b040609080d0902040f27021f080106090b0406050319020c0109150b010302030417070201140418 71
    0x4500003841c002c5164200440030302c1d00f00c203441050001361003050f520308074021030492a03c1a806a800c070246060006a42a030601c0003810300b00040d04112032119858014032010390069a0020002c107407003040301c0f01c2001d001480c640e0080c881c0c54021903100c228100080329904240c00100807000013048175414002d007080020701c02602070703404501d18145407004c10f61140e8a4080030b004601510f000c02c0c10040e9590000c99071035000642c081e03c502e48080b03454058101d1250592180d41040300140018581b441803141d0244031051504903c220300540780c40c080340008040c3c0c1c3c4002181c145d02c05081d600d0500040009482d41d4020040d81800030107440600c0641000304844410302c41880744a03048421a40c11151105120141601c10500c0e08040e1199a400346d82c03d50034228600100504110312680c00000e240003440200c1d904001101240001c840151000e0141209414403800440040817443e0061606480e004141006503205074000d60210f9501004c0030700c0c02c0d0002506 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 547349658 1250 547348408 547348423
    0xb010e0103051608041505100302040f0b01171b0c010c111603080d02041508010806070c050a020f040b0a0305070e06090f0601200a030810082d1603050a0203 69
    0x34201004941000076102890702e10410015080c000207201040034421001b8043c0f400302c165040c288aa45001c4c0c000b07452603401403204034091418043c000c01b40d40020f01815080c0e070300680d13078070284d0201c040a142564a0103006d441500f0001d480200c0c0c00703440c450040584c952403c0001c500607240d001c0061002c038100d154283e650300b115890320050309404000ca03049a82010510741c5950058021000a00c102c0d07014420360401c2c5001e8062050300085114100c0e072604040c5d5110307135600d00d0300b40e4249080910041c05a000341409000618008143c0b051000c0060320014804e40301f04003103a21010076030000e4600e03030702c210420402000b95450f441d60240e0240c401c540f50381054415032410400182c8a241480b00080c40d01070241c4503c20300305080260341e006c84440d40d80310304000e09000c1068441d0915034410b00d0003c16140700c0065034a40281e4840081a813040400507612442c105002c0c48440314018011091000240d0b90708540140d0301900290221105520415190526 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 547350908 1250 547349658 547349687
    0x1e05090a0f0503030313020a17010e0d020d05040303051303020d140111160b040222020c1b150307050d09120206090c0f0f06070b100815011202060c0c0a03060b01 71
    0x48031502844192000b005582c0c0010100341c020484d5002440002c8c00c0d51600d41140611002502c00590501c005411108500c05110143e900c4048241401ca0301c40340030b8070300701007c0f804c02c200c10000a1304c10801071000e11101955602c05a03180d900040700c0c1d0751801c10503a00b40000f18409801c2c0c100a10030314400d541001000e40c81c00e6855041d40c00740c502540000380c40070000b10005029074903441048001408031150181420189254440003900084c1c0394843c14811110820040c1021180c0c400610000800304100041510040445988020010400c000d8180704501d512300e0180101c100961080f880010043e11098000b4508580140300201c5076101c40198110344e146d4500d84185100700791814119000d00f0350110f0240e00ca02d80f0700502245880e001c102614a052180c0c5041e5030307160065541c0c0384103000402070700a0080c021b0251004240d01c01000600c0d003d40281072100c2400140d940601d5940c0020b00c0c202c9165005440442d00d440c040303030305580d0200715004290b0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 547352158 1250 547350908 547350929
    0x3040f0f030209040b150409081908010e01141f0507021503040b061203070803100303110a0b0c07062301060e061305061b0d0513170615011e05090a 65
    0x1440c0d0340020341800340c06440070b0600c0103440e000c1004c110869025806c511800b410070310450310f06203400c036095404009840400c1c4030824103080c000f0310403200b890403544007502000e44e607400c0414110480d414402143d601501c03100300407000c4100c03c0703074107081d5180544406840b408940140100605014000c0b102404c00f00104400640c0c42186550446400c2e145c12103030950088401d45117115a00018003948404020800c103501200081000d8134440c1c2c1d1040c0380b09541108140c0d80b04807a1000070000300124000501070303802603001c3c05030280078000100d040d0380300e1488500030200d008040e1001d0100c050050000c1c603004a120f00000000b9120103290034030303102d040703485401e603401058441c0344000b414100400091340b81c5074030b000f421410388000003118500917055500c2884001d012a8498400040f0b0990203201b0f01000e4003034001422180c0c0d07071225609070004803210014180412000503c030a8148109450000341c40b648500760780b80d1a030404c002c02c0c0080b0358420300e44038 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 547353408 1250 547352158 547352189
    0x1030b220f03030b1c260406030509030403172221060209060307021c090e06210708010b030c03070602030405120c040f1a090f010b0a12020301030503040f 68
    0x40d403100052018407600311040100309891881d0441c051300001c4015540601000801c0c00c1081d000102c0190940c81031006640403000710f900b46100342c01c6c200c51354442c41c01c107000c00c0141034065040280d006420303030309072840c140c0c4039601c0340c00303c09480e2036403e40d8440c081001c0002c929000b03135185451a620990407141c0c0d180205c90954880401c00358079004c0b020340980c0d01000f0164041c0c902e0440c004003607688030301c2c200c2002560f6030f80d541c441e0f50307142c0a1080000c2c0c015009140e5003040c0d40080c1c05491180ea91a000c0c4000b0307001c007044200e00d08200e004410000541800984090001e56001058041c201010186000c1c1080020b601c0ba0b0000403040143c1e64000040340c0440341c0548281d21030342c0e2070070b1002d401c140c3c50007462034110381004007403e5000d0300380e031080d80e443c1c10602007100070050308420f20080c03040c115198925040007034014404808402d000c0c01013400603107080310f41ca10403040781506980082c1c0c01226a580049400c0c880032850410945c0506084540c90030322 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 547354658 1250 547353408 547353451
    0x71d0d0b0106180305030a050715020306130506120f0f0d030e030a0e01110d031413020a03031206030c0e06030f060c04031104060b0a0c0516081506041509020301030b 73
    0x6540303041c4616030a20155402ca001c500c03c92204500c000e40d0482c05894841c1020700d40a001c40d4030106048505022960000000c20000d01c00da07401100003070254a050322481c54007000404002d0109a488450301b4140c403030300d200800c03001c43c00004180180880001070792000b0300d448406440d13001810700f0600b03071900f00703000001070344c01d00100e81c075005054072910f4005945c020018036040f01a40507510f07004000c240c040e0000c4001c5003144a400e8030130350b50300401000110342d040009501c902103c60030800b227403084803040038000460500041150303a9a031042e20b05101603100c02c402c03124074001c100161606000369200541000302408203407401403c0c4401c54032440c00004d040c100d050b9200034464440303a20840103008500c1c41c155441402c080013a000e009000d0f41100c40b48140f0340f12801c0f214000030b080c01103800c50030040c204c902803a0050f02c0c1a540082086802c02e90fa105403102d02441d04042400504103c100140d1725415410011004113008140d4101c605020150720720 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 547355908 1250 547354658 547354673
    0xf0102030909040c050d0602040e130206120a1d0606031009020306160309080426011e1a041b0206010f050108131103030c03090a150804021207050405071d0d 69
    0x400c28400c5401c581c26039207901e0103010001461304015003048005400c21b00b0003e0036030081c0152202480d60305610380d100e5402c20ba01080420000350000c105201c20b0b91003540000c0341e0758001882602c0815428510400c007010b10340000c1c10b00c1c409a12050a01c503581c1014041d03490303944516102400001115000300c1d590768406425990707403196071540034040328443d500119496900624050740c2e6a514509454120603d086100b4502d8a00e4a061134840d41481800d0741181310b07940d80300c40d11642c1d01001008000491105420901c0e42200c4901c0c1c0d40c80d0311904006100788c2d00445401280b0050007441c2540517040409140c140314010f0000360780004a4a034806e01400c0c100ca840703030541ca040c821040c41511442d8252102054003a00c50202001402d01500c0641d03902084950325248200c250164122032400306110303902290142c1400d10061036444554801c0b140b619560300d0108040b20821203590000600121030311401c810051449520741408a130010000c407510b403103004 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 547357158 1250 547355908 547355917
    0x5010b0403020306130302010209090a050402011806080c0d0f1b12060602030415120c05030a0e071404021e040306090b090f10020306240c0f0a210309080705010f0b0f010203 76
    0x8038000c5c80c1e1002c0f802054400d40480342d84034406004805035082000c1078002600040c3c60032402300b040385a144148842c4800d85c101222100d5880302c101d915075402901e02e9a10150091000548410405840031030714068081c2d5a500c02000c0d103600c0746c100031300401c85600c580d910720840d801d2042c04c000556000047e1003d60720a0320702000701c1c0405640548040d40c40410740b00403a428600b1402c01c89801a024510565000405000040c05101c2440d01e6042d140120564504007454007886400c150307021348441d05590308801018000700a81c05030640007a07104546541c0c6441c4218104590070080ca030b00314100d9401001c680b503e85504a8480104010b40b1414035030100000c0d103503aa507100341030000c1440d442240185648201c8082c042d90080c859880309104001c50941300000000f070384c0142c15003210a1160704081070003110380312000b11506900305500c6500807030115a000c00100509403061000003043e07404d40e04d0310004c0d20401010300e0302c00e0324181d04056441c0d030040105c8 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 547358408 1250 547357158 547357171
    0x6100f060c080a170a050a0f15170307053009060304060509011d010207050c01110706050c161d0901022a01090807030c0c0506041203051b0f0106050405010b0403020306 74
    0x1c60720f6803014542203504000c2c0700c01d0040403039a103034140068001c1640c00742d03009902002060052550500503130f02581c5000c008190800c0c1070a000f0008401c4d8042001452104101500e161008035241c01c4d1800440302caa07108011419851a4051001e1041680b61003c104404904041117803002501600008201404c142e4480d80002c480240a5100d40e0601001a1046034100c0684011a00070b40100e042102c0911506504111641c0035144910350750000100a011503414103404a5007600421802d01c50351040b01d010a418100f01100d1001401cac1e07800607840000040c00290190803006442100164410420b5100455054000501c20b20300c000418513040b0754400b06500418078440d014088a202249107800c040d80180449022070064024450395900c0d1001c000c0184994400d00c5508940c105003100028081c501510843c56480740c00c0300d10400320b1198505002c42d840c10074459075500c1d00144207c0c60180300703450140c081882414281419540071a548203009444d0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 547359658 1250 547358408 547358423
    0x11100507081602010908210f04020303031303020c041a1806090105010e0a050315060a0f0612050711070e011d01030c0909051e070611150a05070504030501060806100f060c 75
    0x1040b000d8000d4100042096000d202c0d00e0b90785ca1a45101c3c08842460388410302d0061403d03000c111030801c6000210701030394004015600e980c8603103000600100441904505501603442c41c071825544520030000040d10044045d52402246010060204c403607031362140d494003181381408550303122014914151007080c202101f4130000e0000007400300c81aa400503a0600c00c004200a440544140c100d01840302a03d405001c261600b58180c00070415000b1080003c011060420640d0b050b50000c0e03401406504020224011884146041600c1c54103e03d1410345603100400c110710003a0f20403200b0b0311a00c1903404080d419650f437805031902c284034840c0f43c541c8407803141050050510050a000103e8854030f1098480c1c655441d858807011b03c47c08002c22075480c040c005c9503402284020454054100c0c61440d0390305c223100f0300d0041101400f15030401801340030100019200340704500c041c00e071590040840d850125141c004204e0b80c0d8101298180003510100001c030340040d08a45482d43c80003a = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 547360908 1250 547359658 547359691
    0x50d050c030d0f0609062c0c0903011d0c0a03020f1002120403060f0c140d1d0f070e09070308070605060409170a02011a0f060306030f010c1110050708 66
    0x819155008030070002d040289402d0032001442029071000048400c241e0b02402400da6659140b2100111515070382c8004402da01800940720b000321a543d40034800d510308505000135100800e0840301142e441c810f000b201c0204044626404110300545000b013102c82a858a080d60b0106207141c42d02d804042c003444813241d801c80c3d654000d124060400c91200041c5440300ea680c01c1110141245218072102c240c07503c278a03e80c8070741c03040d0b00405482181c03040051520090030035802c001c1c20301e105000024041c0150325900f0312020302c400203a001c5080c0040c04503500340307090f40c00a403401074003c0b403290703104040810000d200d010546d52282d4006c130000035640c0d41c02e4080b4020b004002001052040000480300030f260208001d442607001660080014126030f81d605039805200d407002c241d106000914049440c41c2c407100a56000b81c0143c01c0e140c6683d81180e0382820345403440045004141c90b20310f6541400d808202020f0090b81d040020302490a0845000d010110050051b0149602540 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 547362158 1250 547360908 547360927
    0xa020a02100f02070f1b08070501080408070218010909110307050f0d050106080a0c060f030506030714010302091c12050f07140c0306010e01140d0c050603062707030b0d050d05 77
    0x10f041c0d0720001d4010b030000310102400e203800d00070906606020502e40c49924400310300504002541001d40710103031103818040c0c5071a01c0c0c0281d0f98110180c02c0744d01c106d468414604403601550614002c0c018464045030f500514070345800840d900c108003500030760060408006946e02c01003040703d1000c0c10b44000d40d0380e0b801824030501600064010034064440c40001c0000c01c542c00c80100c045070792a64841c1c1440d000ca5038104c0c1620800da60b03c070350540c02814180144135a015030720742407030414100107207810401804201e40c0c00482a0407994003948100e00c03014400c842d4030281c01c12105280082c50020003541c1942e01c1e00414402034072000c0b0015001d80480e03400c0080c00d90b1104010115406c640e03440a02e040c81c90b609002c1c51941c02d0400002c4140da003051814041350301d030300c0140ca0b00401d0409040c013510ba0001400254040c034113540d030304040352f814400248004040541c6400601c0c2c0881c001d001c1d1501131141502132103545e46048041040440d0010301c06c0203c0c5021750f0380f400d600 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 547363408 1250 547362158 547362161
    0x516060510080124080a15110d0617060601170103080310090212010801150e2a04030308040c1409040f022d03070b040803121e0f0f0a020a02100f 64
    0x160010780140d880c221000c14440c001580780542d143e41c00021366540c82c1c5464000f40c40d040601c200a0000d501900c041240c02c0741a0406001e241e04100c0075410454002c0d0030100348c4047d50301450760b01c040c894442c052040e092003030541c010800c3c04c04100421507580103090307240b014030020b44000404008110004640b00002c40140396546d000d645400880d01510741c02102031240307030340644c80c18040000105c48407004500300c2e036042440c1096555650b0070140a140cad2440014190800001c0c0407103500c0701703403000c0c00c041c60099441c00c900e0303c0d280c0f030008010440b030380245402d6800d90400c0c07101c0380c0e01d0650403a4429800070701d00940b1815440461021900074261140c000602000b400311010501201101044124111281c1598401c482020381c840d50003045144e80040241056580204844540010000003c140203035600c80c140311000710b003511a0700100c603100085c42040d410303c0d440c2ca0703040240100e00b10700c0d080c0b00d184041d680d211310039101070526484151198400a05 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 547364658 1250 547363408 547363441
    0x2108090102070f090203090106061407080d060506030f070206061f050a02150c0a17060609120307020303070809031c050301060309020d0204090303090201080f0709060503060607120503090c0105160605 88
    0x8820f0600002511140001d02035001112620800d45c6001c5c40024a0b505c40d00e03822029000c07030000d59180100903290f0882942c4803600307001016454100001c0c850303c400008500c40d45400d03241e0381441c1409031380203050407400f6110b9032041041381459904050710b144800c221621a00b0180d07541c1207000d45c16402c4c80080c002095103d0700400c00c009400c0344003401450361100e960340e0040c0c02041d201c09000d090100751800758200c04144094840c074141551041207203084034040340d040100940c0000d203950312241040320b83c0d103400716901045060800c0b032000310b00c80a0400c10300b800c4107803100400354017052042d04101904c90101d4015901e9403196481c04a8002e8414881140242030240140c42404c200301c3c0016400d40c001001c01c040f601c0004d00401c0c0943e01c81503828580041200c894001400c07540c6d000f80100104030000d00300116101001a0780e441e403c7e100d05d000700c240303800c00c0c00148010b070501200b0419000964442c5a100030004d50100c030000d50f5883e03480300d40484903403 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 547365908 1250 547364658 547364669
    0x30f0807090504271b1a0904050405030d150e01060c120f030b03010e0601030b07110c151c0b0312041d04080c062404111206010302092107210809010207 67
    0x30307114800300b07012220072101e07011600c0070030489240d6178440030b40710403030022008551b1060091010711514035081d008140c110340a4030490381070100d1007680c241103924070b006400c41d07039040f004104580b080c004031050040510f404d0500c1d00c01d505071141c01000e00c10800030003c1000d01740f4251f00c594043e84c440903101e64040d00811640741401002c0d80e4800f002c1c04240d8081001c400002c0701c3c140718541c201a4050b8020242a140c91020140049864034510072003603042c0510007501c0e203038803400f1203c00d00001c10300f010400380c0300c80d014141045003c5070841c6400c04100000d00c201c001c0041c0c14010b034000b10f803c1058658075410700d40c455001c0d400c907015041c040c0005200f0095001a000c100180c03500160030030007940c1c8000c0004840126007661803869007030040b082c04024014179594000b030306040152510402d0400181a505841d980050000c0d00c00501004020304111440291010054892202c0485010700301020101400100900070004002e44039910903c5010000e04 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 547367158 1250 547365908 547365971
    0x10206062e0504090615050427050406090b0117032710111014070e010c050d030c110a020a120f05010501091d070b030c0f070209040807030f0807090504 67
    0x4070420020900d510034032030490800d00300007011410300c5191055011072020350701d8580c9807624000011404520030341c1080760001ea001b001a00c991000e0060b184198414100000d106050746009038480c0340681122880c2c1c0c03541444401080800030813030310b500200032400e031a400350a0a110b03000701d12880c41c0f140c100d02c90704801340d9115000010442c02d84be21009076214a000c0381448c0e4200c60091501035003601c4100c01140d0018007030418030784801c4061503d030111480d0be8846603d04000c0c01c5100c00045d0b0342d44820a1502d030711020007201018010302600f4440010b0f000140108414000c048552420040c0d034410880c9820342810340356405802400990380d5015aa40101234075998020100d56240d5601d416031004280401130f260325501c8141941c888540301003c1d9000358003064050b030410460480565281d40c040ca205074403601d0074640ea011149001011200d48018420520000300148641c858019200030192441036500003003e00d00c440c608001850403400400403030 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 547368408 1250 547367158 547367239
    0xd080a020105040b1506040603020c0a050a1515080a060e030c0d0201090210020f06070305090a0b0c04060e19120201050d0c0c06060819080705031c0219080601020606 73
    0x103034042d0010343c4214003c0b582e07007400741e4035055080064450614082c6c0d00070070401c01400114040d50141810303211a070121080889590349942c80c1000b00324040c0c0705001c021045011181c400d000d112413203180302c61039050b65407808203072640e04c0d008080300500341621003000c01d2504404000744c0e4054581c9004541c214604144064002c15107075a00740e024518800f0071380015400040c221000200c000d009190179500d0410440090502074080c2e040c0c0c1c0200701d03091021a86201c1c00038000d55070b01e0078256a452410304050850354100201e540140c011400f0850f407480d030000302800b101d02c900411506030a20b0f02c012a4188103c0c4d4030100c52620300301c03806405907800310120703110764800c2404000142d1281d10342542c82c0c9a0302084806405890b800c07200044d500300c050085c0d9072069080301c1c1000d8100102025070541d0340803d20510303034042094002c0b00702d40e1000b0910050b060030a18603034180180000d465040c0248050300500f0306183c0c0b00c5481844145c800c8040721081c5071032a45 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 547369658 1250 547368408 547368427
    0x70b0103080712050702100c0813030305030a1a01020a03051602060412060e011802150c01141005011713020a05040f0f0e0f0c13020d180203060906240d08 68
    0x182d0304184401e881a25503446010003840c01034046401250700100210b020740c400f030408442d01a02d120341103d00d000c2c10300440003489007000000001d507220344c81d0507840e0b1800300900012a51400781002503003900e00c542c00b0559030080354825a258062030415682e08550392803600074480d1a000940005000400042d00c81c10501550380e00b502c01d0750709005c0b82d20310070141c034241c82c0b001d92103804502c03c49200070014988102c881801c401e9030030700031703040070b007104104e50031540c0e041854403140c0e00400800041c0081010000050502400c00d603400001c41d8084400703503c0020803114038100b014081005542c0c50300e210300700901004009000184c1c130991660054150030100d485214209101e81c480c0e0314001c01c203481004d0038a00101404280d40d0f081180515000c6021010141e0030020015034607203d01403240e1040182407014502021031061600e0b1040090001d907494012001344210301c4100f26586c1c0c4201c0840c0c031410b100300e1002d40062490500802c00500c0b04000013a82e661 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 547370908 1250 547369658 547369673
    0x62d03020c011503020604090207050c0a0f0f06020109080910030e0703060209012613020a080a0b0f1e0105101b14010e190206181314010b0f070b0c070b0103 69
    0x4001c2000d01c0248043c8040d500e900c084a1268000298008010301c0b0a0020420030b40c00b40031440e02030380880c3c403200f10510100c0c00c50b903d1600320340801100340900780300c2c2003599002c000090602d403000308151920790300d444000f805600c3c074180c03141d0b84420550710303580c1c8039420102c0c0c002c088005450825076030b890b040c402540031840a6010600d4071040006170382d519132843da1490007040c40c10f0f0341541d4603000c070246074106900032a8032205031072020070070580030041c003612035106158a841e10708104206186011300142070480340f112a4020640c2c00c150100c070181140e0b401e8420081450645901341c1c4e030101922018546006a4140308040c807000010781040c1d80002c800030000301002d0000c10381c480192481e611030104008100701e006007030401c010809403603a89000604c000c59180042c42c00203c000507005869150318012401d560300c00c048500510318043c150749880045040b9020f039025120300a4118014100050300d640d0100c02112002e95104c14803c46545c0c4a03c3c0014 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 547372158 1250 547370908 547370917
    0x50702031f0608070e04060203100f0f060e040209030d0c0c08012409021306081f0b07020301060503071a1e04180608010606080f060a05041a010e19062d0302 69
    0x51001d07007480c400084000340401c040e004c0c2c56001c8082289503507142c4900d000717584082c0003806031018011000410031a6802c1e80c1000e008140001d20b115490031100400c0d01c1581c00010340301d1841041800c60350b81d40051070481170417403070034031034a261100e080a096201c0c0c164004c1545500701401070007510004c0070751009000740e10030317020300c21510b50f41241c003207004006503070a500c0544041404503d00032180306a00104c06044081140c074540c044003440e42c2198031070000c001c004100c58085240a002e40380140809034002e0140e180f030441c90081600e0344100c4500c41d00d00004846003410f07042c0d4225100040c044807e03954860b42d070400d00d401a01448203205240780703042e10215410030180248070403114035941c2c0545640b141700e10400e85e40000740c0302c40c0c0d1082c3e0007000010b240d2500e024608254220884969066800b01e0026040490700002c040c40349500140845004400c0403465050350300c546003030540c03440c1504801c001c440d5103000d00e0b600d80c0c3d1321201000300c5075403580082 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 547373408 1250 547372158 547372213
    0x3090503040602012705150a060503160303030b040509100f02091002060702071703190c02090a1505060301080d11150a02041d042301021c0c1112040306090305070203 73
    0x4072404421460103c0340091020040081e00910307444040404440d82048d00902e081c2c2000651640d40c50002e403a045a03030404d61100003400c081001490741510822030386c2c0c03c0941d4103111601e414100903840d401010405411560b64069144119600c0e9060b5196003202508144031100218401b81d0f6a1004440c1080144108407000c50804640d2166075a008001030007103060103488082e1408908000400404000d00b54000001580d02d0b080000c2c0100500200060b01c1010701544e42c04440c01508141c3c0220001c0004000c880000500400103403200d251124110700c03141344e0203060007103094414203501c5111081c807201955640c010800c880461403d41c9035040050000980c40000303e6014182d8a08080f060000d45084106420103151b440001407400c1d645401d042c4104e65144034440e040366031609020001030b084118038007440740c400001c6c481942000c41a906238030990100400e86522030850b1810035000347c0a4038520350703000b03058030b5201c050540268102c00140844 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 547374658 1250 547373408 547373441
    0x190b0f091605270301111603300603150204031104090609021201050702010510030b060907031d01090b0109050402090c0f09060703020c0f01080717091009080c2503020d02010309050304060201 84
    0x100725210b4202d001f194810941c00b000d13007050314050b8500fa100b803c491410070f6403414400d59040b0642c400b41c0c0b1183c2c2c5c00c42c008540040c0d45801c5045c171400a21000d010114001d1040105101060f0380c5500c03c0d440580881c1c0100307840301140b03088005480000700094000c2d0496a040034441c1c1d040d04850301c04e14441d802008a50382e0b020b000843c04440c0d00c0058042d000450110b01a17041455a107640314440342004104020701c0d1034651f0341c45401000c020341d41d940d280d03075070820099480441c500500c01c64000b40014146600080c4800d60068180d07100e2070030025180d03650464490039501c031080c2c000c244a840c2d0714207080c06034807002c8036417005204158070f00490304107600440315207009410990301d00c98000b03003501800101c280040d01c0ca541910500c040600b9030b4155008000d0050f216100003911012401d8105103071441005008070300c0e80c2d207031442009803159601c4110880f41c040b120b1606040c200d00050f4010a500304024041e4000010b0200c0e89a80540100302d108005008 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 547375908 1250 547374658 547374671
    0x5030f06040311010605060a08100317130b0c030a0f03060e040308040213050f1311060415021204030f03120b090c0306030d05190c1a190b0f091605270301 68
    0x83c010300702c0c1d4460041c503a1001080c8075246000340f203100100da00820780b60180d4071050316500c40d0300c6450f440541c5080000b0000900711020b54144000c0401401982c00060801e2a01500c1c180c85e40908414074082090316002c820300076100707411a500070944c100c4284450704050074003c1c80e5190484003a030041e24040f029070b02182c203c1c452548141d100c09110919600c40c2810901788a400000645012103030042c03115955883c500107200800311020b5a820160b0381200103400c248402d2200c1c5d103000310074070041000c64481f20b61245102e60528080c40071103e5005040010b0800283c4181c00c200c2d03503010440f0b0419031400070340c0101022412503081a0b1080e90480da02d220300611400700e52a41841c02043c5070041141e007000c1d512400186111030311300b81011038580f20842c0c03500c801881c0c035042c540c012180c40c0300d01034100d0030541c1c0c2200829841808145082c002400c0004500001002c20a60a00c10340a076035001c2c2005401c0c0b070300031071083c0d0429410017004a056121f94030740304 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 547377158 1250 547375908 547375937
    0x24060b090306040b1308030124020604152309160503030a050412060e0f0604020a050a0503031c0b220b010302070c170a1211120a12051005030f060403 66
    0x1410345400060041c0180310503620742d9214403440f000908000d0200c0e20188006000810740e10185010300b81920b50100114140d08403106507064040c2c1311820b54018900784008600700c02c4131040034040b40d00022402c1280c1c0e80e6200d0002444006d01042140c000d81400f11007500410420495100003038282c0c0c0b250f40740e104060701c1c1e114111116000c5942000200500f00410041001160140d80006002507804001e0350801a04415440707007500030108220031480c00d100b9420184c441a02e100740c2042c03d00700401d50301c2c81385400f10281c04c103848030704002003402c0f13130004424003d014000c10313844c001040b0403030720205800e405030424030706103a01000389501c68801d50b16482d03000341324100c8040c5032800c02c51035041c0704505804940070310040c00c00030400b012845444001217940b0420340c07102e80c0082d03900742a040929050300000c20046d0ba4141035115210815a1101d2480007405031034101d030a000f2a00301d0f5102c0d5805001d607403070101e50a4000700b50a48654003c0c0c460000c1054840c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 547378408 1250 547377158 547377179
    0xa05120306010504050103090f08071b06090b0904150f0801090b060910170a0812040b07021f0e07030b0702070e130c06030c0c0b010308031609030b07050304050a2406 73
    0x201c0303001c0e001030001c2c0810092588030b41c0240c0245c501440484150524a4807520415070080c001501c002d44400070301c400aa050340d000c04010b104e1403510050311814580f80d04200e00c900c0c00d171707a80b00300c2d01c0d00c03040d864440420280400400d946600c00f0500da9591040c18041c0000b120f0a07201b03c0380440005140d402d0104090f48260601500c00340e080d414181850040c0410034440145485003114150005546400900c144d20880300c0a581c145090f00e009200c854005160381e046400000c010b0180003010803801c5040e21038540041a65440c41d240e00e071412940782d1002d030003014074a043c051815008140d06050328801c5071440758540d5920200400b002d840d0500400c3c02c03507804000c111661007684042c1e03218406241052001c100e5032038883c07125600fa00b0654400b403000050008c1443d403101414000d92050400d00d25a600c1e40d01c90000035038005003e4400c2c450004000f074200b0a007401072a10040d403040c00c8917101e0100340741881c1900c4003074172840c0b001803801001203070070341c0007 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 547379658 1250 547378408 547378411
    0x705010804020306060d031103070f06050112320115050f010f09090203060d02061201081902090114150307030506092401030c0e10020c0405161b230a051203 69
    0x40d00134403181c0c03509406d003c843e0a20000c19000c002102911080080c1c0a100401c0d045000c0c00c600c246113091800c00504403032043e8001058a0510259500007480c080001503c0492540d55004d1100d900115400c06090000744070181c1d510307143c0400e5280008038184420f5400540d1460511040c24005642c5e500d42c540340300001c6080400c0400c041d0103144c00455002c0406030540318040400d03070200d001170700700482200d910b00c5480c00600c900d02040000890610201ca500281c0c006603801203000454180101210300c2440c00200700d20340c8600a10320082e00301c02c640c0340d03a02c2c174040700010010001a2205c62144042801240e44600c1d03220896030540b00850000310b40d28410001500103090716407216007480382080c0c2080169650460260741007649401a00819030180c0411080342d00092400e5200c4036000d000780c070b03100e40c03000580c4105900503820001d68006420b0008203460514120710a02d40b101e10300040c0d4040108620407a14450400c41c4c040242d011030380d9426000 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 547380908 1250 547379658 547379663
    0xc0c1e19050f010c1e410f030f10060903080705070f03080304060b03031c0b180907090b030114060603070c0206040f06180602250f08010b0a080c03030d1d0d020d020705010804 77
    0x410100801c2616540906d00781041c0541c4c2c841c0b40d4040c18071520002c5500b22514902c03030b6003000700801070300d159200d0540b03910418481404002905001c0080c001c1b10b590300010b0008100810800c0401c94100300d6600a443c0c2d00c103610058540c0c0f4903011485a0085400316503590600800291a040000a44441c0c00150590403049102206110014411200304c10ba110b006c03111034001078108561a83e0140ca5004041c007000c17401e00c0d035542c098134a41101540260f140a240030700d03d0300061460358201c20300300c0310b46607a6110540c0484444c1c508000103503110300009000500b41e103034118a0400c5445a454a01d456002060160001b4032584160030168100c0208a04032404456440040359005000c0b17004060f2660031070750022105410254690703668840c0a0081c3c036081c2c2c0390900400115008203240c02c00d00300400d89034000c18650004644c1c4808101c14801c6141c40d5010480208030300300c40041034003520080d6a0b80c003000b9440058090510081010752180001c06d205e01d4 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 547382158 1250 547380908 547380947
    0x30f0d0212180402070501090209040506060a1a0403080c07030804090b0a090203090a0206031906030c060e061c0f1e0c0e030a020102030301031205120c0c1e19050f010c1e 75
    0x512011754810842115903542c0d400000380141c0c7c1794035600b80224001e0b0000c10741480d0001c140000c59240d5001001c0305c01d0001706001d0796032104011a025030381e010079900d031035000003010246030511540008003600760201d0b000c90324402d141e010111846044034544e81403550fa112403401ca01c4152860040e0750441e1012202500707102c0c00031500a805040900d500c034a500981c0422501d9607001160f450701480802c00039030f640110f84052000701188e885103006885180341d44803c0e5a4044c0f925560b0701d81582c1c0400f54401d40c45051121801c0c82c60301940350340c5850b070030004d094070f459640100b60344031118511820009520040b059060300118a982d0841e01c4c0d4030641d040001108041110401c03076401c08050070160b11b0700846e440d0201c81d864071000b03511070b420304ca00c28001006102c1e800c1e030750f44a18000000c0081c0403000c6001910007113803841c1840c504000b820340216041d9800d0400341c00441b40d22006550113043c071114228980306860808440002c0f01101119028 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 547383408 1250 547382158 547382197
    0x8010303021009020109050a0b0c01060b03060123271203040803180622090b0f0934020706090504020a081b0c060103080a021504030912050309030f0d0212 68
    0x100380030707400f2090042c01410035031009903403180003509985c0c0c1504030302032454001c11802c1c00c24000340a2200500100c0c9011811403818600080c401d4070450352550040d600070200c2000958602d04407040000c004014110701c410000c40e028002c90f90b002e800d03016240190500b201c450001c800e860036a4070000c081c3d450448ae1184817104602c80c0b0203000c0d0300540410240211100a400114454191400810150b0320b000c200c20129100068684c3c0544044021410103680d4640c105038004620540308450b0103a100d280d03421a2110344c403210201d2403030190644000c0d000540310046a0f540c6e600c007036604d0340301c8061005a00031191b0032404501d041003c10700310250884007044080030100b00324103001040358401d00c5c4c03000c00c0e03009803056000050303405807450781401141c0082034000320004140c1025607004007908603c2c800c45c17014007401d4a1074000c011092044030b0b0340c4400241200ca02c0060102940d13164108840044050701c200540345400184c201c0a549901c07082c0c25150074030 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 547384658 1250 547383408 547383433
    0xb0c0c19081903020f04091401060e0a06050a02010e0a0606260615031204030f061b140306120a0c050a0f08070603020d09080307090906060e281d0a0b010801030302 72
    0x3025039038000b00e41416024468460b806070400080d0004000fa9100440c071360004944041c0c480f83c1c180c10039020440c0c1150402e55503110342c001d840c1107648034039000b660380942074002c03401440030a00e4540b443c080d10b6000410702110382c0101c01554511000030003140c4240382d07010703005c0c11401d942245540003136002400c0002079208401241202031309494440789490700c20940780e40a80c100301d0754001d80105400503c4400d110314a8001d106a13030202c04000d4440340030384040381030f06d210074201d8400000110740da05d41d1000c1d0b18012085000b00c0c0e60945461410030128003540c01994041c101d600d60029000c040d50081c0800c6449070001f411002d811701d0011030103580000807203c038064a910900c130024242200552240d02165500d6038041d0410241200b981e0160703100307004100c0c008200c02d400d599400c0240d40c0ca40b040800c00c21007241c0102c000b401001280d03100c0c61241c100782d001440f42c450603000080c4103243c03140381000104503440c0151110300080c04040c006a0050340d90360310 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 547385908 1250 547384658 547384687
    0x1b020c1c030e0303030a02030108060705120423011805010f0203040b13020102031902160906060e06280c0506100b04090f152709080f030709030b0c0c1908 68
    0x1507000c1d00d000b640c03214504000c80d195078003d440041a0702e6000004000f01030080c04030036040380313180c58101e103000c20000084200f01e00291000c0c20f202c01c4440800c03482000408211400b11982009001c0c00c052403040c64101c8005402c1555154244020700b1038039006882100e118030362140c2501000c0e11791200c031110040718000301b2411340c8810064070000300e10200001c00c200c20300380e00901c58030451450100b8100c40642c08181c5860820009020850304411315900e03212059500c2071b10303400b042c0c00700c0058000841e621507000620002d0703405040d61081000d220345000350115038030ba4840c0300042d440b1254a1203141d0101005000030f000c80119600701c200c0c546401310b000f14080768006084d500c0407040717034800d4048170b81e941d41951139009408d54000c0456840081081514000c1c0c88110882c45124400582c420000000600560199107000082d40d00049100b10901d0704120001190740300300300c1c0c940140320310360f981407140012011300890f043d40060074505051207c0310410 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 547387158 1250 547385908 547385959
    0x81005090f0417070b011806030302030412020315010603020406080903090105030106121407020c012a03030c0903050d05090a2403050703090803040c03110118060c020402040e04061b020c 82
    0x541024003807401c002d03c030110b640503061241c064401c1d22007135450848245102c481d418a014006801c0540c1000425008402d407000c84001103070071103100c2040d10020341816641208454801300d80d40001c81c03010380c141e01403c16201c0680710004251030341c2c68490b41d02e0041c030001da80040c5041006122503482980c0d6101d0340c81208202207074182807428051400d4004a82807001640f0883e030049203983d1200c61120003964249514002010443d456088503200090140038581c0340e0101a8559120703001140042d6008000d88420150f42c0200a196500140006214009a400115040e0202c1001c0281401405e515442c02182c3e104150094000284014241a510b05010001c6000040258490303480380142c106184c0c118900384121345085180c0c1c80c100b015811091204000d1030703d4803003d1395010b080034a50350f601c078800134010348603a03040030840c038000b0700501c001c110254011045800c4460721b4251404007000c0300300d030faa0f030051001da6403050305c00c0107080d0030400c00407401 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 547388408 1250 547387158 547387163
    0x60d060f080f0d121b080402190503060609040c0314012405030a24020f130e06101d1002030a02060a110706110412030807020c15030a0e070f0605040501081005090f04 73
    0x405d015000550000e8074113620f01542002c86c0000080004600d00300c0c030004410030a161824400d03604000120341d0301c203170041103103003c1d00e646400b09041c0314801c901080103640c030102401d180d0007000d1841d40a4045900c21100c1e05240643c11648005c0c5100c1a10030760b03038090700400743c60303403d600c0b20403c41040f10400441001500403800c40f14109000424800780150760300c603500d6420750505481c0b10610743c0a902161880c1e002c0c011183d490b82c124490b000600e20f090000d655440900e101d1a41410601d16800421b00c07d41405454011018040d40c1d1420740a503011076a4502e12001a1076069540052210381002014009845a84081800a90b242c01c150429440d0020490243c024501c00d034049003440e010411441c1d810400d104008000780d4040400d105038408680075804081c100b40c0d0302c142c840e020300d61801420007a0400410003080c5146805a58850107451580580035480c00208050005000d550f003046400044803030103011620b4554842c900044503401c090000c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 547389658 1250 547388408 547388411
    0x10b07080904150305010609090b0108030304050703121806170f010e0106030e010e0a06060e0a1407080402010c02150409180809091906080c0111010c0f140702060d060f080f0d12 78
    0x407005c01ca09114010180c07000440000740410282824096100140d10040c0294020010440022808550300044a502864241a9880085080d24000030720701d04030103408156080020100d40c0000c3c50000c842410395000901e8540c2030042003002001d0280088130f20800c40108840303803007036021205419079a0000603031000700d5105281003051240e801d441d416220041840248610041e0942010b0347c0c1d0070401c264030b00444030402d0710320001c2ca65802d128110780041c0079a40030341d00d440d00079503005240500c603180702d44500909400c00e0094800461404d080918400c0072244c1186986030020a001e0a10303140c0001c015407270000070051922040211810000f0620f2802064003034100d04024080300d5402500040910b1039503d0720810030380c1000401040d03070790440a00581c403190344c50080d01000860b030b40002d19104154000b904440c001481c1c2c0440403081d4810020341301031121380004c40350354402c40c41e92880c5560403214150048035403407080f43c2c0105440078041c64038a00 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 547390908 1250 547389658 547389701
    0x60c0a14030108030a0e030624041409061012080d0908040503030d0603050105070e01050d0902221a06040302130e0a0210030903180b0d1a030601030515010b07080904 73
    0xc40c6821900281d0200c280c1d030b0f202003000100b0580007000c0180e010f9040c0d000b00020b29100c05000c0c8010304c1e26041c0404e803410242e4000301e545540d0480c08a01d0103c440403022400d01d000801d41d9000115001c1d007525100d90008502c100c001c0c221440d000360030400d0345040c0300702050ba070f20040101000c1250300354020480000c2da0344060020b002203400301c503000204070b0318500b046400e51740002d00040070800034500090207a030b001001d446401800800014080819201054141101511410312081030413a220340d08050364005800d6020070440300d0420400010510015000314040298040c4550308110044181507011408091805040300c004800503004a005082202e408200203502c0f09410818140c00c050b6094024030b1190380001d450b85000c81084903805035031140000c02d034480680c09040c0711545d2a080417040c0003001d403030035540e4030f2900f1540e4a41424200e000200c100c400055941c1240040d9181c484d00940b505103088440300401004104e4028110000c0f8840c0c1c5 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 547392158 1250 547390908 547390937
    0x51512010303090f08071a130315060302120607020307030c051510030b0f0106020c0d03140c0d080a090c030209042120010204030c09020a050d020d0603060e030c060c0a 74
    0x91058000c5000e5110800524100800440e0782c034550780080a159002d0700c0d040080c2c02c1604042d51050490750038a688415000c00300c5d0300c4548180d071002d40026118880722509015a5003c00300701c0c3d1003110004035204529a074540c40360004c40d03105015070000e120740c6020034000c0701d03501403032880b91007543c1600b04481c08064007003800741e82190100c4c04401e07003441007041010406800000c0c0340040ca50f1907141c01030081d034586044c14010700401380c15107040c3c01c041c001c80e504072840c55541f6403d5244c030380943da000d03a00c0110a4003200015110350110741e619100e4800c0c4241207410645041405045409020704005d000d0f00440d0300740500b03122030b008034418104002c0300800c40d548030301044800e61024841c035041d80d00c20021030307407040004100145080101b4412110b40b40005611003107842c405032450702418003c25401d0b80001208920f000d8154014420f4a10510f0108445042401000c0ea24001d800c20105954422004241c0150381440642007910151034117000d00e07031440 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 547393408 1250 547392158 547392187
    0x1e170a0f06090311010b0307150516080903010506060f04030f02060c011a030105011502060f06010c08130e0a021603140f0403030e030705030109080d0c020c090708040303050603010e03040515 84
    0x1140a59480ba03a58070403030200f6900001d002c0a4400c850f0080c8212101000007030780310708103441050300320300040c2020310b1102e0082e420344540d80361484402c003400d82182096111980300c03140b00352095280c10001221403500205a8404007a640b03c0701e828903084d69510000c1d1981918142d074024824010040710b5017090203000120080003004002c2280443c051500351441a0017560f0104101441c20701d540364000340315a4000c0240b44507008646030903005071246640b800e0081d10020303002030304450603541440d20030200e50402c2c0300281550348001d484412805104c0c800140c4000788900500420700c00d984803040003c1c1e41843c20300e41715080c1d8650605610980c0704030049080680031450307525040c40090010007090300203014001b4641c0e16010300b40b080540c0fc108055a0f8070661500c24130030800100341e0100a03103800540e082c0500094601502101e0071030000781400002400c03400c0c10701440581504040080d404c040c10542040860200310124401000c030900148440101c039 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 547394658 1250 547393408 547393433
    0x1206090201140d150e0613180b0f04031d06071103010b131a030d0f110c090f0a0b0307030c0614190503040201080711060712090b0c0904061e170a 64
    0x12a40007030100b9038400400601c1005a10101c0071007171403001c00c181a210401025612140031800007000d6400b003040301c01c0742d1407141c00603005090000c1085112100c1c1c04282c0e0203140039403502008485400e085200d2402510201782c0c20150038820200090381c481c00d10f01102c03d004001140389148900840c40384000d0043c01d801468840c126200c04000300b88000c2036007103095001e040c1e411390310b043c0505007103401e4000d50200160490f80c04240e940c20f011b90b186c48840149042018102a841e4003000c8006807000ba0a080c60300c0d1041c030645c5000140b160460354485106080685000304c261449081c01a145100c0d84041158982d13038120070f014407030440d00716298907450782010b000040001d80002c2086090042c030100e400c002a0340012040d90040d080d1510404031415113916801030805c008005009121001c01e01c01d444c83e5000c0a000b125205881c01c014466542a043c0081105211400d4840100060034001a82c65134402802091080200c030313500c0c1e455070b032242410540c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 547395908 1250 547394658 547394677
    0x409050c040f0b0f010203030c030103081309020c06062704080306010903170a020d0c0c0506090f060a030605030d0512060f03031314181e041b0303050c07080106120609020114 77
    0x50f15889450b0b00e00e403140090345480340030701c01141945406c40040c8840d110600016050810200d5841c2801d001e00303040402030905a002551240350701c02126a4a030b4083d04c1da1481440106030500300390095802d40042c40ca1103800349107041c2c0342c603200c101c507680c005008541005016040840032540b5180c01482003c000d03222a5618040101d0003414a140201203008001c185c0a000e40424a40352181c001d03100105c40783e950703468480d00045c1c90b018806a402c3e0b082a40400d141c914150503600200440e40d054040c9c2e0703d454801441110f0503c624400c240001c035803180410303690b040440c0380784d12a0401131308a92a01d44040c214071012003c3d5482004140643e60301c40149050a40c14005224280c1c2c2c0c030742c4403a00f030404404601c1c02010a0340718032090700074001014801059083d1844a400401c1c444c1c01039160f081c014000d5002e00c90582961041800c0043c041105108810858004c0d4030a81c80d4003205503240d0f00034020b00d2005038100981c084805a44103518001800c9002 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 547397158 1250 547395908 547395911
    0x1f050a03030203040e060307270213080109050136050304030b010e07090b070c0b0a0909021812032b140a06061704030e0f030f0106031a011505090409050c040f 70
    0x203142c903891720307007001c4000d11a50091300104020030044512044120004081c001010714110741e03103460078002c0c000c2044145160814070000513903e00c0650001d81d14901031402807002201102c822050b584610802c2ca80032540c02038540703443c8002c0d5010b001402d10a00c1600d00d0680d80751603110454900307800c605d9003400000140203007603420030124801040950382c91030070061140c0325200b1108161140a600e240c0001740503051501c203052020242022a1046403120310340191300c0b00d41420410114014813143d9814002844000280e4011305e070304010300c05036401c0e58102011001000f4000c000140d03111128040740702d040f1480d442c403d240a00000600030714141005103503201c002c60440319010b400090202082d80b0600d1380c4052001034611071400300d0403001080c60815084001442035281900200800c80070205060300b065035031192010701d980f9805900f03c04401c11002402041c1c08000c0720350b240c201608100c1085028600352000515254003040030358480f6034045034102d = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 547398408 1250 547397158 547397167
    0xa150912030323010302150d020d0905010e120c062707121118061c06051e010e010e060d0f050f210c030301031e1a0103110103020c061f050a03030203 66
    0x30400407104800c46220b41d00c00b03190f952440c0c000c2410301120130070008500000040c00825042203804940c04041c03050f20402081840d130401034002c1105c503615850034090110040c03c01070007038090758000c03807408000d0301c5507480c1c544031580f03012032200b0311540c1200c920080b10910744040c003ca4005218074141000c0842040c540340d01c010350007400d124890400341d618074405102c5400780f02d5011308161100c0400d400224822129405100c0e402808282490300300300700300101c068814440807420b00889000d98950400100c4043e0902a0010906c1c108000600c2c2d8039112029031010350007400c802894004680307030715040c1445886484483d5004000c1340710542c10b041c000c5642420178008590801b0044100161603110601c4050070440f66419400d4465601b44040c000c4103500c040d40e409014050010541c0d00700c0244000e61b035606010207400260f501900031680d0b401803000152620399140d05c42c05a82624650b4400e00200c02c0349008515a114601d000c000382d0300980055485 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 547399658 1250 547398408 547398431
    0x50f1c0f020f1203090f120f1c090602030d09020a0f151103090a030b0a020d0606180812070602031503060a02071e030e060f09030601141008060a1509120303 69
    0x520005440e0b8030b0103044201c000c1c60392180040f007510488038044600d03600584038a00040c059040070310b42018140160101d08040407400111801c40103040d5042010301c907040d030801c0ea40303844280728041c00b41e00f0403c100684095136a0004141910051440d034035261554812201d40c080754003c1d020700f0708280c0c0e0a011143d0004070360211a002c00000b9440d040c0c038000403c03a8110180300040114459170041018112250107681400d05d42d00b000700680c6544880080c50141c5900701201040219000401c0210001c41c101600c0003400207038620340074496480304000c2d407000b0950b28013281151921521942c050100d5070040750110400342e20744206040044c0b040d030041c0294039101c2600c1100c080040c0d0041605003070031004440c00c50b1562124948100036104489103683c0c1400fa80780081025280c00c0108190039a042d02c045011001750f131015920108103850751544000554010004c00c80002c0301140c010070507142040c0b0896444a030b1400041d246a801c9000c29200c800c02c1c540e = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 547400908 1250 547399658 547399669
    0x303040806221703041e05030a050913022109030a0f0c020102011803230c07050118121214090a0312051c09060c09031a071b051f0213050f1c0f02 64
    0x4900020b0a040c1b182d1034050398415550b442200208024060301107081c189603507a1800645054075010000c1d50340c0d80c581e800c1c0071124200190f0007500540680b000c0f0b1520500001a140e4402c1d032a1034002c41c0c100c0515054a1004d140360007241150740710380c40b005500f018100c11005c882d02c6911036000008058a40d05000c0300c0114900345980703002d00480325900c00c009981c0b011142d00b800c3c080b042d45a00032200c1640196030304105450074034403a81d10100000c58440f00134900d4941e480c40c1c2c200807240110440b0344207041c060360380420402d01c2400400c40c0a60700710035540b01c90414030320781146901c0c8006a80b610202200c1904e60340d060500601c141c1d03000d81d0300321118034606106903c0c11541c400c40b46012019403200c46c0f80f041000600c990b40100115101c03400f099405003200c01c0c0070718001c1d9440b98540c07034002d0307109044204640d014045000b990100c5203241c1801c1c9003a0300306801d100c1c40a04084550380e000311140b0b12340c0c1d81d040b080808200418010341001500e01d90b24014002c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 547402158 1250 547400908 547400933
    0x200402070507150c021806010c0209011418070e13061706010323031c20070213060605070f150501030c2306030402060d090b180c030304080622170304 66
    0x1d003408403d07016400140d0b0381d21006e529610890354580303600d4585200496a060b043c42c002034102220348004600000b100f600103200c800e0403140c44a00c1e00c5c2981400354200001d40c0c3c0f080110340006032000e01032520f10700040f0a200c01910004000d5961b040140c0300b41c40e00c0307880e03080d00c3c1c000a0051081c400c20179040a1110a14071440114200e544035050380d911a0311288141d101088410546820243c1c1000d80d0002d650340404220404030282c0407401c0d40490001c031300c210b0003900745901c01320b001e0003034004070380700c54545504100c41034039410401303004240126450084192101c08100051207040e000c0c40c0650300ea000d005003014a003c960880031503119440c446486413080b0b150752040c04a9a220ba8140c41c0b454440f031502c042c80c0054440d200000302004110f0040200210303541181c20046071402c401c44990b14006828540c40f40301d1801800c00507000741c400140080904480102c0303504040d0300c01a6014910385030a444028a078030b410703920030000030500061041072080307403 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 547403408 1250 547402158 547402199
    0x5190b090a080301170c0301090b01090b090910020a090f0e011e0b180f0901031b0504090f030e01210219021b010e040b060309030c06010e040b0103200402070507 71
    0x304190481902c450046020510610311002640c48040300c0310101030184910915024000388480e80c240d03c3e00b07003018102401a10880ba14152400c915450310041c240d0040e103802c006011400300305003a50f400783d4030102c040d00030b00c91114800903510882c0d00b040d1004000341d00d208001c80d41000d007810340380e0581200185d0340f030081c0c1c041807202400d601c04440c2c608151790403d40403e5411400710700d4012840e0085a44012120000020f0101000641207078110711502501581d40f207904120895400b024003800f149540c4201000290041c401000b52400c141081c1110400c06058440701d05031041c0d0b66078840790081356091074285025005283c58602c1c2c00a41100030345440007107078402c03400441504209a04800c02500d0f1110380c003142d0321a8000d08800d07030b2450503490642c0c0da82e200d040b800380140301e050300010301d40e4010460103025a61100d0240026469915040705484114140f8658502100354400d15580c0e5480203100492055020b00341d07071880c040b00440c1000c450f0303a98 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 547404658 1250 547403408 547403413
    0x1513030b06090f060904030c120e0f011409041505030604060b01170106021c0e060c0f07060203090904080702012a0c0509010513270506150d0b040b0a0905190b09 71
    0x18407040c1803104007941c4d40110141d030000c0d007170f07582c0d800d040304d5201400401908140302c03141c00001451348030941080040c003d446c0b00b9034003080140115031410600d41c074020594402d1201403010300d0141c1105030b07a2a091072480c08900d4854000904061003560100d491580e594002211960400d52000c9513040030b0480b0107440d0302d0001d000c0e44800390202c1940200400c000e0b94a5607078010003227240e040078064541074455a00c00340306503a54103249210066403050349800515070344000b0171181d0410015102c5034103a1030b00c0ea915092600202801c034144441a00250078100c0283c4074404e203110f40000703802080c14103081000380204035070030240c0103100d8200180300540311004240009290040001040c00030001e030308034003400396100d8086410781401540244840000c00340d000b09105c1c42c0400c60140701c1010880c6009074500020043c801080010340410400c41d01d103076001642480219440c085565907900300210f40d0300c50001daa000c0c06100c01844205101580c1c8401000300 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 547405908 1250 547404658 547404661
    0x1e0301030210030903090807170f0d021e07080a080702040b0307062a05070312140c0c131404141209090604200c0303010e150d111513030b0609 63
    0x2051682042c02000782c18182ca60981d034080510030200c1c40700401080041e00d10058407520808154001240310000d540b103410128490464041200050206280c00504020302e000310401509203039a0b64200142c0200403000840070005e00010b80312078803800300c059890010388104021609140301c07030b0340664491801446a150003601c0d40c00e500c0b9a0310485c0c503181c20b0060201c07510358404440104140a140e50000800c12110512426151240c6505840406d12902e1020364061002e660040f1340c040141414a401d2101c001444000f12880100d20302101f250210200441620105c914110700c12201240c80c80920100c440b640615000c14a45070744100015994203000c0c1c1054845da6075010b42c1c42c04a01650841800c0060540b4102d40f20000502c2d0b442e1a60024071880003100c04034800a0003000d5240008141284001c2c0840540481c5841d02141394218104040e0000c1c80e90440b110000c9450000e0948840b004c0c0e07038442c0841c214a8002606040a01414000c07000c440 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 547407158 1250 547405908 547405913
    0xc080a111c050604021303060c0801210b0c091e0310090c03110a170706021c021f0609020409062c150d0f050d110f031b0f060c1e030103 60
    0x180700c807000c0d0800c000c08540c07030322000009030091040c0060100c5265003880d000042200c15004040d40f041079488900b400c0c8e9981464400c1d070908400c00c00c1a14041c0d540c0075001480012400c0e41010700801c45504000403c0003040480f80400c00310010481200007200003403a02f00441500a59030790b82c14003510207a56940162490640001001800180304510481c1c84808402c0d009100d049102c145100000c0031341c50f1107010302d000e1400140103240f008807034001c01c001d0114910400c0ea00510b03d264002e1002c10042c4e004045c03134040c2c03c0d00c512001800f00d4403400540043c0c4000d42000409a1401409004106c3c030751105988000700b4960360742183d00c0203902c00d0746c44103032580041412165540052040b002c1d03564000c1545503903405102c1030050010301c0211010741c4e61180d446460808000c1640c1c0d0000c41c030000c8a03640204007456001c3d00b4480c10b41500c2e1120001c42d0000c0c66440d000c1d5050030f2040b600302d04602e40200d0500c0441c52410080c48003240780c4ca01c21071640d411074 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 547408408 1250 547407158 547407187
    0x1e0b1f08030702040b03030903010c1d01020a0201050a0305090703170414030736050a02182b0215190906170a0b010c12050d0c0206150d03020304090c080a11 69
    0x80b40c0191096540b100c0800c21510240200c8503e03070002002042402e0f04a2009007101005081540f5030107030040180080d0b50000800100c02c40d01611122300344880020200d0140100425083c494002c01c840040080d0140300000c44054031500d80c00e0321103042003842081e8011490245200c1e0b4052442000886500315202409062011400c0c01903401c2041840b407028183c0c214080b100d00c0c280030020300229582c090a901d81805041d4180400c0384c84c10040d2244089110b44400c004c513941080082c0456401e03203007500e1010348035803000c0071581243c104076004420000010082c21400200040d4460380d036201420150420b503014800700409104103440003854014900e0b9190401c0385268054a0840d248941c07000040106410301a80203006c1c0c2c101c120100590350500b208a1400380c00440e88e103108114124460400d000c400f01042010b00301c0f44c5098081d070108120208440300c81c2c0c040ca520050b0a6254030505081c0440040100d230040c86040303002d02c005020801000b00700 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 547409658 1250 547408408 547408417
    0x1603050c0f07080f030c040e01060c031d01200312010803040608070f03090203030a110601120f0b040314120403170c0a030507030621061b05030f041e0b1f0803 70
    0x20032000d41c030b400007071074640c800744102400c0819900002c410022444520401030064130494171450202e80da95041c1507070290300811004000c640e20203000c103d0380e003503a001c0c0c0d1002c81d4149441800086410030920129840c0002c803807080e080082c1401180000500311401004210700841c641403501c60001c09048024080400300001c400c65040b0480c8290410305403980c008007540c0d502e03100c443c000782031508003100d183d00d140240e100011b01000e44009160b00150011a42555059540c1d1042c1d031400c00100120140103580506180e14100707803014240440c40c0f000c4500c0a41800e080207021100f450f040c40e070400205100b00000e55400c2e0082d40c06803c1b09040100d640d403144c40c0d040c2d000d0300d49038000741540000402c1d414590346e130712400c51f1003a6018a008200f245a1420031184900e9140d0320640414010008905051712840680343c0c0640900840d02c41101c4201c822000e082c4441c405603519000002480350420300501a0781e0068440074001d1095490300610070340324001c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 547410908 1250 547409658 547409677
    0x120a0510051005090703022a0705012303010806011d06012c10020304060305010b071a040c1a040e130201090b070206041d04031b15050c0c0f03031603050c 68
    0x112000814000740202c0341003400b4000c01000c0d0159803620b074100a00940140355040c89102d0302d05030284d0800082e049103941d00340308101400c003141c01c0c0401921070748207440540300b01000f02d078265058a017041c400b65018181342409070006514000c0510901005280c8034801611080248003981c2e81009034105103a4200d5000d2203808030025146080807980c0210396049170072001c6008603282c2c048000d0080e1440c0e42c80c204840c0c0d8844006c10020f0080300c0000b407154820203115508248243e86a41d40b2030312075080601244d0700d400c0081407030101051010311041000c501405007401c480449944a46c8590340c2003c01e0781c007500020900d01492003040328250300010307180d055403601012900a407600180c04041065403040524a800f4111400e600040c1100c150391504c1403942001000c080c0c000301c00000f2842c681c3c954030020000603100703240c4000c08000801042c00306010098030007141102850700d03854202e0655040580c83c600b15800c140c43c090420007007842110171b84503801c2 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 547412158 1250 547410908 547410911
    0x120d1106060f0d081b10060608161b060c03050a06060e090403080a0f1b17010e0c0306011b120905100503040f0204090f1110110c0f0402091e120a0510 66
    0xc190410f9859031082d070005840601029a000340e000750002200c146c0140c0032401081070035958082120754030800e4550456900c4880000d880b4a0720869101c010381c2d02d400303605104510b865548004032151054400f0100e903d80040080c0e80000c0e2141c0001051a42041d203204014000042c8100700001d00c01028400070f0740101c1c8802040d0760003038400002c03160041000364000905808030380ca12551440c0090030365602c00b202440750b480040e048440d41c0c2c282610396240c40c00c98600c580c000403c96410048000030480325550305504403d4081c0c000c60950100f050702000c010311054481d0030040c000c01c0700107840f2000780d030700104a0340c2c840d0300407104c800d50841c248001006410841d40c082d1091124286480910a601c0c40c8125443e001726013800880141c6034054400d07451b0b0900b0552103400c100d01391003160412034601210f22500a0005203444040e100085404c00c03000254041058101c8082d50b80d4200350783c11045070b504110040120464984c1d555070ba52181454103500f07039 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 547413408 1250 547412158 547412179
    0xa02040509190b1006030c05121f03080306030c0a0f03060207020f03010203010b120901051302100903080a0507030e12060408070c08031204060b1906050a050405120d1106060f 77
    0x1490a1114010601092000d9400082e0b039040202103403074240d91510000c0d40d11440091031038040c1c801c032404044c542c2c8940382010305400c5c03a0181140b006050904024210703204180e140d29040d401e00c0514854511942c990070150103261500389030350401e17809280d10003000c0c00404040c0d40c420080740c0d07202d180581e641900b40b0119410062140c4810b8241d800480041351080809000c1e042c0d64400007a11400c81c3c1e5651103890030f0365800d036268040140e050754900302500303007a440c42d0100c00303060510411b441d0741e031740e6409202e9214503d40070000e6000b040240405034081c041b210380c01401c170f0b0414105400e007035807140c80d41d50160009103910b900144490420100b013696000510483d0143e175200d4002d0711a41c202124100c8003100d07510315000e607103080d81c5840c0d40c500071800f0104500c500c44a04003201910941d0012000c001849418480044c4596600c8410301710808044040e10b450041040060210360341c6500300440c035001f00c1c00300400390f04c5e000c6403a0300c49503007100c028815 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 547414658 1250 547413408 547413421
    0x1b060d0b0a080703080702090f15011d031c02190b070302031b030a05060a050607030f180302030a0f02030f070605190e03060f0103120e09061e1903150c020a020405 72
    0x540c1e1a50000d5618090500c1c000148560480a4500349000303450015155482d01c0c3c4c41d101080c02143d00c401050320900329804a540710360700ea00f0794010070b02200010982a5400249044c804000522071400c1407082040f44503814460300746880c10701410410707a4140d60390b03140507000e0024600380805a0200016076004100440c40003590031140d40c59590382405116800900412070350305008403c0c00c40002103a080290441c1e09440e05543c0d51405609107400c21940c40700d901c40d600c020404e0030b01003c4090b079014003d000925101c0c485040007480b9a10505041098190458903690403081080100c203410404444070003d4150124506000d07404094402c01038127690f05405102d2a81000042083c01c65003078162809005100130403040e0038000c42e21903804011031030700301890a002c50141e0420401182d0b8105844074110340c4543d5800200e04802015600300300d2120074000c007001070120140b2100d00c1101c2c41c64041c800d40c001a04081d584544542009015950f10400207a1 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 547415908 1250 547414658 547414669
    0xb0621130f030e27041b0b0c01091a01030506070e031006080303180123040204020c01090813060309120f0225050102060a06050d0b100b070b07021b060d0b 68
    0x506690101440314200c41c1414001c0801c3c0030703006881c1c000d0803103450301039840300b0002c0c02c8035145091500020099943d6900d01d040c000d80c04405805010000c50041038030b15280010f40007440102c000040c2600884c288080c5a290003041420301100880c018030200b41d02042c2c5e1680455103003008c0804951030b00109242551040106102a01d00107001c0381c00840400218003a0340700102035443e1007140d0084900300c800c10b000b00030540b0505884420070312200508513500c14001031006060007200d003085070940b120340b00120754401c000034800b0700360001284a40e001d1700c0a864104880c2403c2e50300c9410000f00000e1850a02c031119540156083c420004801207418240440206030007032080c038190b0030518080c10b80580100700004540610506c01c25003221002070482d02d4849180d120443c005001030a4030a000061003404500000300c80000c000c0d540c403400b0803100702d00d0200402400c04204085a980000c00400302c03061650f92541030301c44140743d502001421100700c800042 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 547417158 1250 547415908 547415941
    0x70809060313030e03011a120102040e07050403150509060403080901090c0b04050a06050f0901260c040f0602010c140306030106030b09010e0607050319020d2d0b0621 73
    0xa034400c0c00041048802407021580340030041c420703242c610240c10101c04044c00d0311100f00c02100c100792a046001c0ea58a0803a42622092691500040ca85600d40c0401402c43d501222004082200000c2c200304000e1003c46a03640c4030600f240401c0b0354208a6240d50721024098005810400c0d1400850300c5c2030004c0d030240100396405100d00158980d100d24409094009109651003401100c0000900301d0185e0203e4055a81c0f0202e25490114154010354010301d0b442503a011071031210300c01c10545490072a01e079028954120285407218540300d1202581c2d42e00e6004982164105281a4045030f003080a001c0b240f9a82004c0340d8072650b440002ca80100202e9101500f0940c0d00d10511148440640c0038106020140b4150b4801e40c1c0c1c0e4510984003488160f655030102406c96001045058281d409403802170009003003c203104011000e0b1161103505c4180d2001d011907a1414880c00c00e50510514548a0b0b05480003410701894020460344510109a0700c040400044001602c0f0603014080a = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 547418408 1250 547417158 547417177
    0x102060105420d0606030f18081e0d0905010f112715070b091c11011104090c11060112021207090c09290316021e031c02090a03080708 59
    0x3a0b0710f83e07030700c11480b01c0980b4540c490240401d246c43d030790701003030070050152401114080544001c607130401d54458280780d1020f050034035001e440350745001414015400034450144201d5010541d09001c1c00c0c92800c4030314100600303400929000000000c1c0076600c050b955140203000c0d050b101141c00d44811450106441d071020340c4a00d0558400d604002c03d0806060b0b0280905c41c0b00c0d07016507400c02456568002030030124240510807a800014512a40d64440340c842414008642c103d0440300945803904640c20072802c80e03480b01d5209510aa008071078454650a2000a141c3e0303524000358503800c071009081c06030095111003855545070204110140050070700da9410000040a42e400030812038443c003d00a607034a1b002c400f8403001c440480d40c1d55002e002040807a155407602e407114840034907131811308402d41c0503a421415000c03060080721482814804c01170341d0380d1000c0c812003000c0380314101e842d08201403060102c0e001585072400050180c1e5801040301c1ea0b00c0400d800c003040c1344d00a1706000d = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 547419658 1250 547418408 547418539
    0x9130210020a0309090c02070b07051006060905101d0f0406050a0e19020a120c0215010b04090c02160e0601141303061d1b01050c010207110102060105 66
    0x300c2100036400207a803507401d802a41c401c3c020a44a9200c00182c034941c0c4c80640059100180c140040288032000b0300040380324000f1031705050104481e0905981d0568004408654070303403404c1005040040001c40c01c0240d5161520a28004a6041080d2405000b0090144902c0c0f44242d41c2034846610000141500130407001c8015681c540c08503032010100c030b05140092000001d154403160314001d5900801451b00c4400400246a22450007001d9071020b1004500c00c2c0d04c400010500d0141030b403406080c1c490550380e95581810410015541e825913000c0441d40700850702081030f8004001d41003558107200a902170b43d00c84000484000701502c1c03a800704e40700001640e03070180d204181c81030301f101d1180a0504c103260140c401d4003100380c1048004400c075007240d03000017154101d20714048825101410840c1c00c210144401c01e0882e00041d9088416081e100c2e40700c0c60560701082800d0041800f06c0d03601022800c044032000088580d8500810828080da00d0210032401d071006001030010170010 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 547420908 1250 547419658 547419679
    0x50901120540030c02060f0309062a03041511042315090f0102100c0207081e120c0309040c081006080c12040f02181608010e06091302 59
    0x4801c0e60032200c10b6120b4141052000c081c800358081c1890101a41494a0a075010740100d51030644035400f90700c01c01c03684960104545420700d0701d08400f45014092850040015140895022000010b011220341680c000c5003640e1904070410400c496105074802c01521058011003440c5020704028610f5600d1054081004940e080801d412500d280e200c0a4500101c443c100c0140f086026518010301240013003042500107505220480d00d02540040c8112803000b41e14602c1441100c8070340c00790000582140d031041204100130007400907141e03c1c1c00d4403109000310400c2000d03943c1c55010782900c590381000c5008030024000307105890010b100940188030400a0900042c0300001c21100780b64040301e19040480d503548513031449440f03840b003076080b98074010f100c3c1340e0200801c20003002224000040c030101401a110031401c150740e01904140340c400d0703040007011940c264400318107000030403080d034004021303914050140640284064a043e4416250031100200482403404040c0d0004581c01 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 547422158 1250 547420908 547420921
    0x90b0f0301051614120a09031107060c02030709051608090a02060301092a091403030d0f2304031b020102030705060c030a0605030c090f0c1b0a1a0f01060509011205 72
    0x20081c08412110340d4540d0640c0c61135802801a500aa040c080c1030a4403200c0014010000d40e03001e01e0a00d4080c0c142150901d0038000c003503207070230b01d42d4018000060320365a07903108504042011601802c07540c1d41c184043d1400001c0c0c0303400518005d101200f04005040800c06000c0c0500244000503000761950369a981c4640d0000d014005441e051411141c0d00d40b550303010084030010100207003130781c0d0352001c1c50035150107084a0019201c0c2c1c00301c3d626020030006459007509a01c03640090104030000403d01c040c0d0120041c2b8000e1100d08174000340d0308010104000283e22440000b8280c1c0d15007090b54840810b400102d00d10302841d00300410910919051150301c0395864065440340c002640244840c9499005040d00ea906c0903900b6074200a241010400804203403550a5101c000b0001581c01c0c0302140d482c00c0600140c1d01d14081240c1c001503040018090001001d40c000320300043c1e2401c480c00c2c04400901c1e401030512503e01001404100180303c0e038800c00464454010b200c0c001c0c842d504000 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 547423408 1250 547422158 547422181
    0x609090b0303090645031b042004030c081c12020708070203030a0e040c0c02010203031b0c0a060207030e0405090a060f1b1107060c0305031902070b07030b01081b04090b0f030105 78
    0x40c02010b20800303048817160007482d0000c1e41e40a8680001c80686491402000b8000540720701c80312801c3c0040780a40d901640100e8401402c02140070f43c00840c034491410f4009070500d40740c42912080c2014040c03102c0555074000007086042610940c0069a40c030301410000c0c0c86010301c410003541030000045003203440f80c1c00100384070b0b08642250100540c2e40080015a2002171a480c02070240c0c00500003c0c4d030b118041040520881217000e2018078241508000c00c2c1040003180080b10300d42e0b0b01140c102e0a1641c8030642c0c5e82001001c0c1c0b0100142e041c2190000c1d503031410903100602c11030b02c5000c44030603040b59402000030070301c4510401c070000400a10190101c0b01101020842d40f00d0340d0320020364540302c2c580903010160180c440502c1d50b00c450b851a215944400150300c030300e54007040040001000403400f070388613810075980001c5540f0604001018045d0107002c1003902100c0da05e12080e941002003c6070121003202e20005110a5000301203502c29212881c4564107510b06000c203e038a5640c1c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 547424658 1250 547423408 547423507
    0x91807080c1e07030c0515090a020d050a0c0b04092702040509010f1d0c030c0a17030c07060503090c0d0302030a0f0e0a141f0206010527100609090b03030906 69
    0x5406940c0d10107a640c891f8049400200c0301900c0f244d00c0f15002c0760160400c03405014405014a040d00d803102410b403031f004201500741e4081c203000ea10016040080b140ca80c890a003002c600b041182c41e980880c0126801d02554600010380b0440d5100b002c036491180961040c2440110b184051080c0c0c0c0002400e03514910540d56982c03030718080c1e103180595600e800f06520a80c0c0100400c0818403a0801c01e003440d00414000511005100412540c40000d00c10442000100f0069842c41d40d40d11b00303010411f041210030004039000d030303040303a08460002e9000300965a8892551a048070701205960303040740c91292071ba1850b0b030460344000001ca003580100143c0031030900242c41b4151090800d514440f001e28808010900681090b40107021038a410103611140c4400b1242884498a60718030170049a0b1054480c8070310108440c1c0c040000325080300000c0b00401c1c1800082058002c3d500201c0c1e100e20070440d0341e0b1320070000040c0c0c88071341c00311306000c0c1ca40003030401000300207101100c036850780c0c800314 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 547425908 1250 547424658 547424663
    0xe19050a0e070e0402061801021005040c4401060f0906260a060c05090613031403070c091d0a0302030306010801121a04111203091807080c1e07030c 65
    0xd20100821000f10711032001c3c0c000d81c4d02034802464007500100481182010000f0241140682c2c1515003021115003c0c841c0190f0040345810400d902d4460080416101d0141c0c1c1c06030481940d20804421501c00c07229200160b08504c0c00b001500a8018a401040c442d000b101c103c1c161100c0218041809a01ca04161001c4808041982072040490b44600c0e1050091012590040754240d0004d05941c0115141000700d040c035500b0106050001a503603003018400d03150800d80d4000410070b01001450500c6a04200c0c1c016519000c2d41741c4504920420b20700038181c8482d103511010700b08610f0104079644965200c4142c482202951400035201c1c1d1050b02c41e02e00103040c400000c2021010302d0010340ca40355004450102d1041400000040b8030001401941c8803080741071001c40646584003004440220a8090340d0f581180e0401c11540c4640000d141c610400040c0400052a400c0740303030140c0142c10410100d0301c071100c80000001c2c075116600b0383c03410040c0105075001010380141c50f5101702803 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 547427158 1250 547425908 547425913
    0xb0708120106020316080a020a0209010306090302011d07271b02070807060e28080a061d0d08130c140418080f0715060b0c0709090305040e19050a0e 65
    0x241d0b40d1100300d039640620880c0c40051184821040c0c00200341c40000c003046200c03801514046038050f0000341c4c1c000c0090b4811741c4c4581d01d90b040301d010580c0c203100304184080340c1a144003600c140650710f07079640d038840d0003580034118030b14400c015024000030369010784044220046c000c420300007510098640403500710390f015100d502000705e503100020615000b69800741d555409d48101c004200407400703c08900b00144031740316844985100341c10119030000790080303c2c01003c14076084c1c036000c800c40b480c130203000c60b11039100c502d0f13214080c00110b854202e2200c20300d019000d9445101842844080e040c030000c0010480801c00201c24854107090300c43c08070200c40410a20362102c00d640040c0c100342d940106442ca04204004242810718007403d21603004030342d040d54240914080b202141c013240c109081d1a8400300340900605001c100020190010705003d00c0304a06694001e04103000d18050303845050101000100352007483c00c1d030400b29850a0000740418100802040f00078650b81091560320b0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 547428408 1250 547427158 547427161
    0x73e190212030a0c060b0609040911101704080a02030c07062f0c061606020423030d020a02010806040f150e0703060e06040b1503040b06040510060c02040905070b070812 74
    0x18070003000742c90080c1c0072600d1382401c9682940d14113005209410150342c0c081c40500c081c0300c00c0e031101e21a9a02884c41025079000b4115040c0411804030710054800c0108000300030b40085040c0e00c0c4030090b03005a4024511512110301c1d5000307074110b00548000c0c0e251407059000c005406940000850b40300403424901c0c4015040100187c45507183d01140301c1020351120309404130a00b040d00c024424110200c90004001049035155020b9911507440051b14100480040901400b8500f4552503050210002c00b0b81121840d4007031b44170703014240064180b00e5800c002a9842c2c0300e0340c0000204a200c144100151582005d5140304008613000c0e00919800e500002030045009119100550f141e0b074500280b540d07500170400000d0900e11100f543c1041000d00024214503605028500481c4581d41004e05480e00301c00f400101c0b44014550049840e0782c00081201c1030704403180c0c5d150f664041e00c000c03d100c1304606225103040c0c0207601c01c2e41d12480014840d014061801b0141003204100807401906 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 547429658 1250 547428408 547428439
    0x20304170703080f060a0b0c0c030d020c031902010509121011032a071b170c0f06030a09170913050103030e120c100f08073e1902 57
    0x5029000c1c008000c126008003260b45039a1800c41c3c15480300009000190345074036240d4a28860f080413005440740e03800650b20340d1907480e0074003861001a141e0310040c45075110700320000b680c680ca592203010078000300042c00015648104100c81302400007a110212503c0a8850255560f040080c040b6100e031070030840900e003491100440c0d000e402203c494444001e0514100300c1143c403a02241800e0590403c0200000744200032078801e001d20b0054001d038890b02d015000c805030b51088498000d103070030002441c072030b42d03944009440c80324109072000343e200c2e84d030a40790b08003c041c1528054510b5400d04658210382c07201d00001c204202040e01d0400c0139030010000c01d01691000e00004011405605204c506c03418519400e241d0f00c0c4d0108112003034508200085503c20036445031030000105000407800441d90080c90854000b440ca10345098614402584c11542403640e04411586051071501d11403102541c02480451116100030b8030704c016102500e41e8898010251700324050a4581d0300f9603074 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 547430908 1250 547429658 547429703
    0xb010801030c27150806090102121311150a121107080f040306050f2d0c180303030c0304050d050f0f070311190605010902130b0a050f030a020304 64
    0x4880d48004028120340c1400020260340b03034500c4a0380e030b0200c00c0c3e40302041080554022034007011301d140460307180582081e00c1141040b10040016045078010000680b16002d0004400d51042100710a0303c66410303a4603040d402c0700c040564040d0f01c068845000d07101c0608a100130311b4240c881c2e46a001500442d64070b0301040d11000e0a400000070010f011070404100c11078000c2190708401d00e001413801d0340325942c983c212035040d6050410524401c08004004100c043c0300084119500501c103143c442c2290a643c0b1554000d00c00c101d02c1c003001c140b42c66000001e0701c50010100f0010166a1685130040342005e43e03400850741503805100700d55204003501d0207002110b4400f41c14042652402c441c60b10b4050550f80031a40480401440840350704d40c1c0001400529101c101d1407600e07031035041c410f052140c01c0d2081071f00084140380c410007002c90740741000d108084c00c4a020440c441d8403860061404c0d642c03401482510410801c0c00030400c00b264505034002c5100314401c1c0103140010741c820f9070000 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 547432158 1250 547430908 547430911
    0xc04091d190b010e130506010803181c03120f020a0c0203070b04060206071107051e09070e030304030b0c190c0c0b09150c071502010c0207120201020601031205040305120304060b0108 80
    0x504850b001da0061100b040942d180d1350740440003103035400014607981d903424a444000d80c132800058101140001303014151000340300e00c42c0c0c1c0458008000041d040415020201d24090050502080c84100292075019800030128001c0030081151212000301000d0f00082a10310105e209020300e80700403400e11003640545040d039007164010070150780c42000940c0d440c400d0010380c0010384a0b0b400300158517a990311280a0005e404c403c0c04034044240c109020b1440005050101400200a60b40c161a01c0c000103840450390480f0507004103444918031040c4501c250a1100403034a5188030100e40315400c81c00203840d42e0b10500c100c43c01d56685041000150040e44040caa1101d02032142074008100751000e070000f902c0140c00d590f0003030f589922311614022200c0d00640940d459402d06c511451b014025100103041c2d00700021520743e81075000030b4176500c0500008009175041c01401d4800c5104005640245621008541e1544290340c042038007900100c81c1140c9541c00c000d1502d6007940301d0883d03117 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 547433408 1250 547432158 547432163
    0x1d0a060b0412080706020a2606091603231006030501080d1409030717010b1203160c0b0703020a1403280309020402040f031106030412080c04091d19 65
    0x180c1030500b405204414100308003015102c0050a000380404900e4a200800b861070880d02e910f21b040c103c3c1010360058030004d94400880c45c18810402649441d004e03e05030740170710214400f00451000001c00d03801040301c0800e01d10100c3c0c4d802d407610303143c003100714805001d40c02c03400100504603601c0004400343c40003400303014981c0d0061103010311007d000d20b0324800c5040303404c8203160801c1e840b01b0100345001c80941c0550202c04100da08400c0300310080c41400d10f009004c0c0d910070381c81540740204551b24460a28020748802c5071f41c2c2c800c0d01f40321b044000b40003d07042e07520216903201840c1c1002996082c07003000c01d490520140f121912507400c00011202032240041031000c0104142825070365034100380d0300600034581c6444807400166207503c000c00140c8a41200d400515080d42440d11280080365446409400101700340000318221003c56801a4040c0c40c0140407980c80200c0d07046280910b50026030740d541421a5004079006440d94a080c40010000b03e489421680b0a459084060071201 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 547434658 1250 547433408 547433429
    0x3030408030103033b06040905090604150b01081302040207020603280c0c02120708030f0d150501080c030709030b040b0a1103060604060503130804080604031205061003021602040203011d0a06 84
    0x4110b1410030f179200003429001002c2c107007015a203140300b8003500c000310391a4040b904040100000c01101082c0210407480c103a504210440fa1800060300e5110040c00c1c14418480b644018011550356070102c80c0c240b50f02408082d12402c018403100b4030209146411320340c0103840222901e8483c22481030801c0c00c81d5542e5590380a0000d80c09012a01a82032003e50582c014058041510350b4100000c015402040c03542e0740c5d4401441000000b10341c010180a221070841150030021a81e1000b520340d001100b200806030740b525085401c0c2c0f00090715a100900710b5010764100300a200d038103441d0034400c1d050958107110200d0410000300580c48101d1382554000801c0c8410b100481c482c50203503900c4501e519004800c2c40c207646501c0404d405c55404003600354880b0701000201644030f040910843c44840040c440d605207400000c2c0d0303500d00820340404160f03000c564140e031032151440082c001900a0001c541d80e503103d1040c0c2003080070102c501c480280c1c4440120b0803c1400f441000b080b66100c1c000b = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 547435908 1250 547434658 547434737
    0x10302030403020c040c1115010e0415140a090b060907120b191710020a05070f2603061002160905090a0c09021206030a02300303040803010303 63
    0x150025040503000b0303000c51082100f02090f9848511502055420988600108030f9060f1001c070b24007006a44114031040b0000b0040000124900026810075800004007004610fa10080b0340103240784240b0b107006403101c102f1b10a9015150703002c1142a03008055401a95a6100900c0f800b49429255903002030300e076102d10b401d0a40300b0b0380080c840700e034001c041282010210700c580b10051040e0b0002c09505e04860700700203001c04100001c1401c640310717100640c00c1014080029040707020794071002d81101841c0110500304050070200d03442407854641520740c0c41081c103580d1501600100c030ba0f98002c00000030b80111082c0006000e140400c05501710710540b44c00c000c145c0c005040080d00c403603c03612480d1008000510b010500c100038041d403c80068580d61142c0b10940064000b03000a070198110081d04005a01d4408214001e20788a50380b0308521521400c0c81d85482c011001d1140c031038000801800108401c2c0e000640c12603019030340701d42c0f80c0000d48400c0d4003107100010100d4244004040d = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 547437158 1250 547435908 547435927
    0x3040f02010305150618010e010c0b0105010c060f02031009060504141305010b0d080c01050112211103040803040906090b0a03150b060403060c020d0f051209030f07080d05090c0105 79
    0x108402c1d801442c64004e040070b9054203000c217400d80c100c1c0307400e4041e0b504010004200c55a0201e900c02d000a024139000c070106450ba1a0a4014401030188a04104000303000c0380901c80241c0104108440c15441107641780303018801418042201c5c081c03e881241030000014141c50107000381c440c00081003101c03500d1030300d809160002c94001d40004a80301d5403222180c000c266614400300035081d0040051030780e81e44503640290b0031038505812000b6400f1407d041c00d00420101060401003800170408550300e00c0b400d59040d154468000107001032071100190120702e500010001c4c1040316000c01c01800419150b603014419a03040302880c0e03421246241041010800140140e4042050604c0000d4540258404035059030311542056038007070340315440381e0820f50341001100d045c26203500d021202c0e0fa0355008006d05511801e80c454202068401c0421580d05041c0104c0d46054903459a10341d50790610b29101d5036541150054003d118940000618041070200d005600c0c2d10059480758584207400 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 547438408 1250 547437158 547437161
    0x50901140904060801020307050408060708040807060905010b13090b0c2113060603080c0f06160e010207170d02060108010e0c130f060609170c1014070822050603040f020103 76
    0x2030300c0c6294003c0e1543c10001e007054080c0700550084113503607a925a11801e10201502e40f0101a0098040142010412010a11000680d00c1403540804085810781c0d0341c1c1415400340c404200c18503802015405103001515081e441200f07150710491020500340d40b1150003891070b015000f504404504440d81c0803a5000240d00180d522508261070a100c4034140c2d110700084a550b604211040750000514a407001c000300300c0702d02c404158200030101441e040c0c0002c9100c6907402e8050703041c4614100c5155203680203000905c00f41c00f45003141da03000b444014250b0703a81c000b920544005801203400100307454406008030440c41d14554000c0101507d020144420154202e0220440b15514035400d02641c81500070200145402d0b0303160142c03075041180c83d080d90464070202c0c4002ea4000d00c1000304c951500302840d0008861410114040603007104004140c0c1304444000f4505440064910702088802e005c5d40694215000c905088540780d0b814052030340300c00d540240280303655044660041d0312a = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 547439658 1250 547438408 547438417
    0x4005060607080a120203041101090e070917101103040b1e0f070302070f0c06181a0a03150312080a0c1205040201020304050d0c1a07020a17070e04050a05070605090114 73
    0x7490700c00200c4813214204002c80c1c200356400c488409081202051039a40101e611000c0c2041208402c5142030020002d0004440da1060710888941955026840781c03040c0030b102c3d9017114800060040c104801c9039080783d540119400c0366070f1011480860300c03000f41034040c100d0700500f2a8441916859400c1d0010007154010118010107408000b1540018124402045854400c0c40d091180da803c100c8040c0800814404004801c00e081b00d00300f140d101034108031120524003910b0a43c0c7c40b1390070401280500010111003090003040c98000082151440c203609201101c0d42e5090035a44a109e080e406581940507040001241070606940f484480e6200a80003441401101d01d0300e6910004642e41c008485001d030f6034190034400400111240120780306621200000d1b080c6050300c294005a20000720f8000c4140050b10103400d440c20074001c02c0f400000e4a0041501400c9140070302e0000c0e9200340b4103208880700d004803d000600d081c0907105582c40058161960200c030518521451181e410 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 547440908 1250 547439658 547439677
    0x905160c0609170d0608010506010f0305060301060f03050307030e01170123040606170105030f071a042102180f01120203010906110c1203060603010311400506060708 73
    0x6458261000054071030514003003500c180ea00c00f58456141c10040d10444034158018103041c0d0410f81040f00c0d5a030b0280d00c0d00383e00c20300c0d4140056980c0fa0314011030b00401c07194100c500c1c040c860311004400e111002021b071488520076030719800014009001111150640c400e00032461081c600103210507a48000015501009401e92035030281d401d00c002015900c19a1014011909128050030403811203ca0f0740e000d4641600200300f4104540507065580d4207900c0b5410035519016080c0203c01d0702ca00844006001e001c080c0510892a4240200d01c0894507008030710880d00c8007074030300402c110010490311414442c101c000240c0c1c64961119243d0010071412039141d50b94a0880000800611401044406081c5100d4844851140e0540b501c1604a0710090344407050007040110b0340c070101104d0560b94000c80c0d01020b84481d41c00f04816070045c2241134800c4540000003060311444d00082140d00c4400c03011a429600c0c201c04a9049540540722240c00074010000500400d0311503001381511384 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 547442158 1250 547440908 547440911
    0x11212170c030a09170a020717060708060105130e1005091b030915090105060315010b0913020f0a0e2103120612190c0f181a0a06050d060905160c06 65
    0x11305507500c14083e03201180307118000e0708001c0f40c100e94296040152078042c1949000342954141410f038007a0343c401d8020040000c1048107030004406034451010b448100c51003003000c105075919840c180c40c003448100c541e441301c2046884c0c000f40c07a2409034403040c090a80d400040c5000130400c90030141d990700087c06075200e0310515001c151840026605240709207001c000004840c02c04400b0142400e01d0300d154140099422070043c0201c101d003604440c0c1105044a00c442032461324400180030340681e09840307034000c40100300c060410f038010700500f044080440d400e080302c4000d00020450410201d10760101984140240314034442e00d000c01c150803c10040002c5000c0d900e241007189440d0764150300380001102d44007035108004c910b4000a0107001c3d41d0411135100c1c0d04100034803030203c49102060000f00d480d5040078280b4003844100e0050268086e0144c402c01c3e807904805007866000441c03a1100da072070444005080e04061040b04e018258800110341c070020401c6048071410720b41c46040da20315 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 547443408 1250 547442158 547442171
    0x3022e09081303051b090402010206130c120b1609080712060e0303010303120b0307210201210207030e0f1c051207061d0f120a090e011212170c030a 65
    0x1030710400c6110b0055114500a00b80d941500308901071000b800c024543c06000d0020038400142c1e008242d880d480705001100e400e10040d5800d1003031600340113500858102c0001c008480c24005221000c502c40e00c2003c803a4900b080c5202030803248180035210313030300040e00b1000e800d0207144030840f412001da5019000c041064032504109505543c402c1e402100403500101c1014a03050040c0103590440c031048020344410707407501d500c0b0b00000c1d1038100310211054607000c201c1c046a0240e11071004a6101041450401d04554201030080d03000d69419404903d42110b40007032449e01154580005c3c4000d00022201054042c3c12564403e450343c080340d15014280211503003c90460141c40d40902a08010030107a00321051110381c40580c0b0b01417010741e000f41a40f100c45c01400140040c84502164440d07540e14044a4200c0302c3c0c1295821481d810000301d40000340ca10b240399481c01d0701034024280c80d500b0b0700c0898025a0040c060045200b44020040c3c002000701c1c00e1980a141d01000d00d1a010880c0c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 547444658 1250 547443408 547443427
    0x209130203100b2403011e0f05011419110705040603052815050609150306040213020702030609160609080604060b2704050d14030610030b030d030903022e0908 70
    0x21403c035180c196104c0c0e0008001041718110301c202255840d01c8600e0500c03400c504046084486180c0c0b40142c0f41804803100c2d03551051403c0400301e401d04a0213010400140710056002040ca02c1004038864503032140340000f00c3d0514061140200b00e950000040604200905c0100312180c04403000d00d520944101800c0c001c142c401c201006601540c030400a00c40c42c0540c1040030290002c0c02c0481d200c0c80d424003890660703c0c002202c9820036011100103640d040c0610804019204240009406000340001d0101000c00091041c3c502134010501412064030380b1011100102188118000b9900580110b40403c1082c3c1c000301416201400601755008503050112900010383da07100c520404410030001030140621040e0311400b400e107051244441d048003400b009000c05054103126003802094030130402c0c0a03502000941501a0a81d500c003038813014080c00902c00400300794003600a50b44444012103410040c100051000d90840401d844089111001000080011108418204800c800 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 547445908 1250 547444658 547444699
    0x6210c07050609010b130c0813020604120302011406040903090303080c0d0c020a030e01030506010e0f0f04050c0316090317031e01080705030111030f04120c02060a08040209130203100b 81
    0x811401c3c0c10010990454120078040b8420f10070303040303240340c0d494040e48100c07840c0e0108615410900c910020310303101c0901d0001414921690b440040c40c045881c54800c1016010740200030060a08551003680ea901c010078041629040380700140011641c44051000038040d100054020000b4a0481d003000c0c10054000100e07017001414074056405048980c00305640207680260242007071906000c2820444000307403401400d48152480b40034140065003040d284e0711262403500744002c0051100741000c4805e10780316407041c1d032282c001c0042054900d200d2806600640100d80d80722510164140b803140100d0000d41000d030842544081c41c5030040c0c00c0c1e0620f0f24449003c2c04680014103155841c103010135086a031403c0d40b0700031400080c020014082d514504040d8801e030484200124200400022502020082002588000f010904c1c00113036a001581911481c4241c1e92003100e030321003001a000300f4100060003940b56000d10a071001801c0c0076000322211b0701018007051141e8045041458 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 547447158 1250 547445908 547445911
    0xc0703020f0d171e01060309050307050601031a0a020f0a05090324100801150603150f09061d04050c0103020a0e030a0f1b030f080f0d020705100b06210c070506 70
    0x5509060303c0000401c6019075190848404844080c000f105810355413015241442160103041d0303904034040038040213108803071407541c2c001c2c10b894240d030310307440c1c060303014500026400803a2000400041c0e80314007a100b202e40c800103410700f40e420410100030460b200d6012a004a800d400b0f0010b5491035404030f11038607080480d540c04895407074a4144010804090198009440c90303051a0103a0510420310850780255505c916001c030b4a05049144d09400703013030316400001240601c0b800060b6241d0150300c0f001c15100e502c2007403d146500c011005010070b100f51f0b000343c0b05800c840c03030191403980a41d00900c401e03001410400c940b858010006801c2510000c026181c060a40580078200800d0500908142542040082c101801d649070056140c0720104010180c07d0001a07540000c07128009941e04034900c20801d5548a10394074082c2c3d1501000700c003080115050603000d2000d0719180080e12103191800d201e5408002d04940d14000c103200181508405500400411001c1482485110b = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 547448408 1250 547447158 547447183
    0x2010c050a1406090318100519080702010b15030a05180114160f05030a0c031104030503070303060b0301051e0f03060c1222060b010306080f0706030b0a0305060c0703020f 75
    0xc0c000c0c0c4490300b440c41c1c10040010841d00960300104400041840104c50464200d20240c80100503221f1186040d2040d1144000020100c10400c940c40d0619600c6000c2c0b0b4440c80456000740f04030780c111014804180c0c1000142c4040210a00018508103003170b90000c0d41c880420a0b82e5182002c04000d51801c544010310039081c42d18007001040309450791603100260250039032403d0071905008c004000c0c0140000360030364401603140e00c0c4846d4094400c2d00304680d40c40003c240d59135035546d01d1500c42d42d6a44058030490101e030405000003024000391090340e0403a10040e06820615103074000e94000400203d1a182e4002240c030702d41d100382d440c1001000c0c403a8120310f190760365820504a9103000b442d001400d01d6041003690701c03000c00300c49043c084010000e41c40800450f40154000059001d000c0390b030410b40796171090150106d00700300001510401c60318552000c00507039070564140900100280006080381e80420301003000d0407064801080b085009205071000030041d07041880c203290101001 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 547449658 1250 547448408 547448423
    0x2031021020f09010e011208040503070b090103050907050901090e0102070602030a06030c09110702060a020118030201150504050402060a050307050d180c050d0b0601030e150c0a0f0c051902010c050a 87
    0x40850402205200b24018119202d0b140740d1300d840d400480c1302c44140521282c080c00c0c03101c0403041010070401da4002e02001425644d8064444100c440550020074101c0d002030b0034030011440c00301012502805403480038003101500c3e82401d003840090901075640c100c0c42e660800070080890f043c3c1c4040c5006400c2989c7c040741081c61401d000324092840c2d04010345140c60080764903c1080500c00f1154441e41c1500d00c281c5425508a00b80c3c010000f00040c4d00b03c441e20b04101c4000c055044d4050061020302460b10240e150b211002c1c03208660040310000e41002003008031008043c001e40c051079105e150380c80c29a240c159040a10b4040c1c3e05245007112958040c808410100107121480101610b810b80d00361030300c0c2645855203010244040c0c1101c0c14590b4a04114425000600100742c61444401000f409820103084a541c141d2121995200180169403800d03030181c0318003514084a0b400000915080310501b400c5030320700034084030403414450500c0c0c0b9000005c0d4188010a0124029180b = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 547450908 1250 547449658 547449719
    0x31206010e030303011d060d050303092d07120602040f0311090c0a17041110080109060b1608090f120a0201030c050405100e04090501290a0303050d020310 68
    0x140000750406030a40c0b290700144018044541c61501500c00b0120280c0b04420a0300c5200100b1661903102a0103095800000104102c241c40012030718002c260805001c0d0030001c800021803400c1641180c2c810943e08145c104209051400440541042c021440189441d60300e0b011504c20030300b1684101c441000010409442d458000c4101da8070030800d0359054a030445030400103001c8841000c074284403864080c040390a2040c10000b5030a411405000c50314541c1e002d8001900c0b8210074400d4100590500d14042a03110210701610b014a602100b800710303a03801944d4030b00342508030344600e60f08a50459401809139036001c00305880004960f0240988036010b00004003aa14200010070502804000030040b0ba1180902d030585e05081d4a0486050201140054068090010054055030030a080c412120b6540c1490352900c04500041c02107010105050042e00421440b0113000300b40244140205e03180150000c60340325100340341d1032403201d84030381c003510052600b81c2c5401c3c0071800188 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 547452158 1250 547450908 547450921
    0xf1d10120308010602210415021002030711010506030a021813020a0308031501020601060e0103180b15101403040b0601120e060a0f0e0a02150f0d05070305070c02030a120c050312 78
    0x721240b1182d80c1146050074011891b0000c240c3d1041d4420308a40c404140c05407410103100380a041c000c543c2ca48000d56990401000003030500c041c01d42001c000d5440e03c03001c03d18a1500103886215694094070034610f0a580000294044030f000340100860010205c40034016912002c00f440a94072640c0e00d19201c2c203084000b41c60004100f02e901e81950302850051004076042840d50003c0902440c01013204650b45003030340014601c4c200c0080074040b0310380c24000f42c00b81d42c505010028405440c0700c0009200d600b0112500c0c150144400e0020b0310070008600440c1600d80d6555014206050076200741c07200180c108100c81d250350610115402c440306102800406000394018a00019003d000340c0510001e11a111140e00c00c009105081c2490034000d1807051a0a4684403c0c0703890032140c940d100843c11a02904040300c49000003454400041d0748940200b140e0344047d500030300240600301d02135662840e104030728003c2005015801010400044003080144480344400708620101d06100 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 547453408 1250 547452158 547452163
    0x1203010603021b0d0917011d010c0f170105040203040c050d0309050108181209030a0213060315090b0a1e020d090b161d0a0b0c030909010f1d10120308010602 69
    0x1800507502d5082130010114003030707100741c0a800b83c400e05072240d0103840405425038010103036204071001c80501a0464614024103502221080e005a25407003102c00b4094000c650714010b01c0c01807142c0c141460018130082c1441d501555015120b461484000c2d91180d00040a603c0c014008400090309030106100b079503400201d46800c0403007041031301c415200302120152281c7c060042c19802c248040b8082ca4195001c100c110301c00c640240205d8100c407082001000500454042582e207209117034085d51042c1018404c281e072590f0481d0008080c0d031182510740c0040c10345c1e020b00e0b822020958000c01e1180e019403009100841c007060000507404070394600180d44410040c001608181114142c82e61190460b10002c62802041402400c00d240c400000d5114050750300809014000455125443c1100000416519208449800d541c1c3e80e108141c2c46071490701e002e4500248645401c0c0300345803030721180040e0400518207900c8000c82d2613590184200101a80c00d07000a80d081004000d6541c06 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 547454658 1250 547453408 547453447
    0xc04022208060c1b011d0d02210d0b0103110d090b01090b062d031006020c04090201020c0f04020d09061b0f0f050903150907140f03100b03120301060302 67
    0x15002802c0740c0d03e043c2199807a14020301c0205040405200b0141503d14400c1d84503007803e001c1c42e0050000e2181000c8000d60301c0840404100240c40346420709515042072004c6d616800070b85c40c0006203480130045804024204514069042c16111403400d44448100405481e840301c40782c0b00000c0140040c00d14450400c010b90250045524003800b02805444403012039945104184c1e041d1034000040001075a440e44d8101888074101e00032081c40001400c0c403400c1400c0f036241d5400c44040ca45400100411241c01000003405039000c16034540c0c117420150306c603040b4003000801c01801c4c0101d084118007aa030080808548680d80c84240c4d00e0000720003104114010011300d0207290000e201e110242046024004001c2401004178100140ea602042030703080d0f5100b455040d681d035040c618007250380c0c0c803c00d010b07510301c2c0c07005002d034840b403420001884900c0d000018014030324030351f41c03650507002081141e0600d6014007078103550144a40c00c00300118001c24655a00682d1807500d8182141c0d90010f = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 547455908 1250 547454658 547454669
    0x15010e0a1a090103150c170c09060c01020304030302031b090a060f0201200a03060e0405070b09040f0e1b03150105120f07030c0e0f1302010e03101a090f060901060c050c040222 77
    0x8146a18035009a6924401d0754023442445004e580c64001030001a664082c8845501d080d41c0000100802c155068004e1030142c440c00c80c4070807000c00c035002c05290030302a0b1207109070003d003100340c10032a0074810005560f131110280000a034601c00001c1d0f1078407550049134403074090f1a00003159502140d05114010081ca0b81c0070700e495403420b095480584401080c410a040b13400081010281596147c0c00f42002c070740e86c04420455a0165244540c4031070f07101000c24100543c10703040f043c00c0d041c082012070a500345440b110002c3d030309000c108010706180352a425468450900b80c40f00380c94040000a01035070194410700703140c502e0503488052403174009222220610003401800400b240c1115030584007035090074500807490034000441e24010b0b42070031446095090400b8010b50b50b004001c1321103100b40644448010b680e44203113403100c1000941c2d03a1508203c2c00401001028841e810000c0c80c140715100b9a44100e4001001a0681e0400f0403041f0031110902000b5205240741d1428600600 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 547457158 1250 547455908 547455917
    0x3140903030415020729100b09101107051002060f060a0b0f03042d02030f03040305060402150409020f0306040c0906090501110109051b0315010e0a1a090103150c 71
    0x82c00765600c1a801d840c00144002c11600807601c81c5c20007043c03031402003031041c0b002ea42d1207801c002c190400342280300070740d0903540b00e9500c404080303a0f5007103403001c69201c904060400c1c0c800d5541c1c003008a46c41c20010300c80340d0b540d010f00b0310003181c1c6540e220b10047c6c01c2109c036030040407681800c400e070320003000d8040c15403031060707100349010880601001c06542e62084160341c640d49135030ba20b0404001385d0341100e560340041080c0d00a41240c07404004190780c0514000d80c101d81500100940345070785d0740f04070300026245500400000d00145000c001d502d0507410345c10292428640c0ea13000351802c0e40c10501c10f0b540c41da8004020403007542443d10440349603102900d0554945850150301601e12506801030301e041010f840540c0c10806c03000d410004c8202c0d4010708680305906800c00d0084102d0881d10001c0c461700030140012140420607843c0c606983c4442013440c1e0344d41301c031050740c0010030188001c40c030304070b00e602e0101d04995500b8107414004c0d80644400039500031000d45520444000b115003600380b0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 547458408 1250 547457158 547457161
    0x3030f080f04030302090607330212040b090a08120414031c0b120f150c340b130201080a1a040b04091704090606050c0307020108180d0314090303 64
    0x490300100e07a03604160903080041c0c1d52a002404074241c0d2140d0311000d0040c120b40c7c8000b02111207048440d015008105070060701c01400c160f2003e060b0b1085980c41036000070650041400319030f4400b02690400622000c482448850381c0c0c6000c001d801c4507080c034007010600d400304010f0000308020040c1210500000d98540491003101c0701c1e40107415008281516914440c5200c0c5803104020020341c2c84901045501d940c03410701c580c682c3c038005140f45d42c4003800c1c0310003c1481c01201034103481c02080403050b41c140c07084540e04681001c1c800851501d0b045103c03020580c0202d4440da1009010f00100c0340d034400e00c03211600002d030480d03802414500e4954600210649144601c0001404860b8125004581c00303201e0710020700544001c0b4005482900106500da8a06079000700810444102610038021075907200000e07569800750100065940d003007007150130010340c402c001081d44030360040c410b003072003180320030f0542e14003407809010341d0119580780250f040c003a5449001d99800f044140045155 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 547459658 1250 547458408 547458421
    0x6060612050603031b10090501060503100b0102060109020706090f08030601030507050405011d041b0f0e030714040f1b030c031404021f1e1d03010b0918010e011503030f08 75
    0x10307441703050f80a20b03800010224003488550144a0b0b441c41c01400700c001d0001c02038a0a050707000700400d1003114800c1c460384028031800c001d1801003503066003058005d06881c0c0c0ca44800f240c00396100c40c04c01c5904030350791010480050000d02e0010f8686010341001c0745c80e46070440000d804c80350003410b15001c0c0241840108003580c1d00454103d2440d51410040000380d46440101e005041200c0c0e81014281c4940081c28100c0c2e4094010304c903112180c1d0325002c00500034418140c5440e460302584100c40c002e5a40004582400c0e000840d40311800440010146584001c4490009101c075100c000640c54180a14500d54540941b415120a1a40405150500d60300141c229007400c01d03241c1085551504a14001e402081e8a503445003543d90400500c0d4505034008040220210f01c13604c4102941d00400f81e00d003014400d070032121f400a0a000798a0300c0341c03001d0703c1455011800c210710a648039280c242e00c085003070003006001070401800518050451502a090b01c1300b40c681d01c020050a0b00401c4039 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 547460908 1250 547459658 547459663
    0x60906011e050a02031b0d1b1203020f070b040302010c0e03150435040302120138040609060e0f0c0304020d1707150b1009090e0a0c0306060612050603 66
    0xd00741c0180c2499030f901c858280040c0d045005042010001614090079036600d10008101440c010f07155540e0958074208810101b120142c403500060000b04808114803006402a401020343c0002424864100380c1c00b5920104030b24401c0320b044005035144d9203490703415600648192035121003140541071100c043c40b0350010140d40180701904c0c8010200f0084c620b00a40b0200348110712440c41040c02441c81d0f4500a501903005110490051341002121610340d031042c841c00000240c040480a1070400300458a0008070800c0403081081240c58000240740c9c2d2148100f038010805401d0100e803e62400000d403001c02401400141d50304441c8080020382200001100d901075811144520050560308000181140c2c0750f420255082c00022500180328502541c85004950b8100900100c0c10070401d100d00045908400c4000c603a100d1820f0069613600c0c1c00224541008104907030003610144c640b480010703100e9100351500c641d103520610403183e20104103108410000d0040c029401c0400c0400e6 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 547462158 1250 547460908 547460957
    0x7050105070618020a0b0406140405010e010c020402040807090509100902180901060e040803060306070e0d0f05010f05070908010b03030a170603013206120715140f0306090601 77
    0x10702080d502c0362004491a4540d2580c0340309a0045c103070121054540a00250740c1d440f5015100101700340b613020705108907103041224149e81c01070355400d0891860743c0065544014440040380c0c407036000d01c0003041c42d40040088034010074440034085420308040c0d00c0c440c20310045a01e0701c1085818942100003580f591156406503030b501036210422913441c641002d0040c05d0343e8008900c41c00b03121052001340008000903600846085040d22015101c006003511048502c1109030341100300306032440045455040c154803c0b90090002103042d00001d00c014089030720403a0004041100c1c8842842000303c02d1007180030100080c0e00035441c001c010500541550072101d0f424100b0520311300081c4107903d0070b4010703103044074040c00001440300410813101c0a01c0000742200000441e150002103040c0703883c0001d1205045202e0240c11114140700040d41c41e0710042c0301b1360003440b002c80710031040c16103010b00600e403015240c0b840545a040c00f41c1042411840a4400c3c4c0c10048011880000c000340030710300b80b = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 547463408 1250 547462158 547462163
    0x2a0504023121230102040807030f02130911100909090503041805060901050607030c0c090203062e05160f061d061504151a091810060804110306190e0705010507 70
    0x300d14a4203215003c41c0680300300d400c1012140202034001007008003606503800168401c40301502c00000d104c0b5000c003268140700707010f06070203a58001c01701d0509003681282c40c400d0080c80c0441c842600e90b211401a03407180001203d80c3c0d813000504006c4100c4150b401403252104801c02c0c02203081600000f81d618106009a0b4405c000008000381010b000c0d00da400b40c0765500c6810340480c190b48400f220000d410480b08c5174004c05032421401e0503040b02c2c0e54091400c0701d1243c0300300e0f0360460402c0300300c500e904868101090301d400d440880d404114480340e07801c29a481a000801d168014207000740c1c07445003611001e00303140d02c803c06200e010b513250032185228400c00c0d40c002485400c00700c403002c440c07070b0107a00c010900742900c205510b9174a1070310010640360b4016a0209640907412030483d5041d00100e400d44076104070843c0911001d4407030f2240640050040490b240650041c0c1d0000e82030000585002010781281c006d50036800c0400d0085411000e0802d010309421b501d010000f0f0f105100d0304800 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 547464658 1250 547463408 547463453
    0x1030c1d131b11010c0f020304030f0c17030c010c08091e01150623030c0d0b0102030912060a0c0504120b0c0d090503072a0504023121 59
    0x812050380080e2012000400d403003a106a80500a4090300c040c1c43c0403400380d400d00071303490791050040d01c04110381c88642c2d000310310341460358442880d02140c0031002c41d002040075100290300c0540079a100c40c2d1414032000346580b650890b40030360840324030708441c4041c0503c21003004006640071400f408026003071a001c0c0c40103e031a400b1580101455004035205004d1054041011a841844004c41d01920300050181220303641008940f80003c0b036950011200400c896203003003c05401c40c0c91110b4040c011a81440f200c08002810252054000f0445a200400700480da40c0360b4081c98000d0519405d0052078241810400c40103c0ea10740d00c06007400e0101e5020403034040c4508126203006604850400a504039440d02d10f44940c0445400d59004da07140d030400e90011400380030f4444000000010440c003902e4901400060740241030110510403200700c1121082c0071b04400380611003c1003030810030981c10011030405412107240742080c0365800f8103d620016030f004001514200141c100c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 547465908 1250 547464658 547464679
    0xd08040e0a200a051c3e071b08070b091003060e0a02070f0b010f03030f0807091703120901061716051903121205010902090d11120f060601030c1d 64
    0x500c3c00c010f01c01000306031111807800f000c418028201ba614003003216200d003415681041054a4030514002454561042c0301c0100302d00400a9402860007068031040040d02c41115566a041c0b810008030343d0103403205000028442800385486c01100100070510708040003c0c5003851803810030300c14010715640089500040e000306110207030108a400ba41e00c00300514240da100c00c4c0340b450f61096480100c01041503442c840c50684d0040c041240316801c3c03039030390310280d914080031078021040c107056941c0103010030007010f407001e40c4407402d491142d000b407030000c0b80c0c01e403403d0304030f101d0150380345103030390076a00280c21070508500020f01d81c0b070403181c0803a086840c0803110110096250856800103209003c3da40c4180503041c5c2040c0340e07504a90001c9000c1082e43e9131070100c0001d0703105500405038458210148200044c0c07a80c4183d1844010260001d040c101205040a19190001d0616611584818104078866902d4044d02040317a04904d0202000e5022441c81030680b6009181d291040a0554 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 547467158 1250 547465908 547465927
    0xf1e080c0309071206020912150601030507110d0c0201020f0a0b0c0901050c03030906150f030d11010b1003060801050114030a031d090a090b0708070207090504020d08040e0a200a05 79
    0x440c3d000d0000d6081c2c1341c00300802403502000951100080d14040c01200d8100605041c0124003a80c429400182c034040316511403004400a19000740654140442c461160a50600411020380c00744802e45030521849214000a85000011008200c01d68883d030758000009828042c07054000c441d1502164951700841c00580d4035004046175031f08244008020010b109800041490140c8160b1880011034040e010901110090001400381c0580c040881c03495980d128103196840f080c421000000d4540341c060015204044010b0350000094075507105200e13801b820b12400d801483c4d044442c010704603415020a0b10f4044410b400740c1840741080c5110700c1d9204c2c0101a01c0010401030a0b03041600d00202480f009220741801601c1408130140080c00c4a0300138020705010756a990000c161a9180c0742c079481c0680002001240c1011f01500c6010000302c1050140019028490003442e0520f4141040300458070100f00007614128200140c0d00c00c1015402103800030a103070b05d0155070740d40402 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 547468408 1250 547467158 547467163
    0x7021e010905161404020702100810150309050f0604020d0f060204091508010b0907091211060a03021b01060509070507031e030b030c061905090d05010c0f1e080c0309 73
    0x44074050650702072480c07403c940c00d00d000250310070348850404040286003034405001c124094400000c4d042011000b003501024000c00080b68000c80c4802c80000854844810400101d04a40d107940442d8480c1465403c20900b841001c0c13100d038612004200d1440d054002500070200c07490060303d1a84e8001d9800c01780040c40e0112405010014800c3c04911000455421034018500c10180d680d40381c084400c3c0c1c035242100b0703010b0041049540b505c4103241820000c10408010f1300d001c40b0820f64400d294030503600c40d0409400d0515054900584921440f0701f8154021012070008816034507040b8280441d0b620141001d4000c1040c0c5009515000e141c40d058a0001071040868034429810101031002030381034200c0d030307002c940907015105004924410320030340340119901603000840e4102a540c9007885140548106031000f49255800003481c0c03070712803c40e82240700b508001000c01c50716595040e04a002030307110b600030848180850b01219801060043c015003004808100080805e1030030004 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 547469658 1250 547468408 547468421
    0xe060f030a0c052404080c150304020f1201200a030c0503040803040303051305010e0601030c060903020f0409111011060601050c0c04110d02131724090102041a07050708030307021e01 80
    0x40c130455a6954840107190b03551b0480280c40c612a40c0d02d00301c00851010204144ca0080d0740c0500f803003003c00650340412265480c02d045030a9959a0354070340f443c0c0108122746038100401152489076a070f0740507840c01419102e00071544820301904000348400102c58100312035005805207070025060302c3d200d0a4803102c004041c0094583c0d03003880702c0b0346002c1c0404158541241e1140340d40b48980c5a480400f1b0312101a140300c0a94030508814121031203060070307007000a0540c490014650315021504c00a80c0c411a11a04440012050000d990030984104009900038509080007410585400c40b820f941d00d09030145140a55143c411080c0384102000966018002e240700c00d40d03d0b501e400715030150b490510701c00d18108400c4091940d40141000c25540020004191074018020005980c0d0719600409044800a59030821001610220000d000c80307010344010b010565440040c1415841d100c240d8001c241240c00030014403d48a40004001400c0c00d00c180700c0046000c0064a0b06004008 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 547470908 1250 547469658 547469719
    0xf030912150b19060810030204060b03010305011118210303180712020f090c1306030902210616020f0f0105071101060608070804020f04060e060f030a0c05 68
    0x18212240c8080000710300400a01881c5000d08101401c51141004200483d019441c691103030079000c00d0014601c28440c0c164400050003410024680d00e60110f421a5090342c4404800030000c0018000c0007403c5c01500d0f00340054110140c00d02801885010360007015800980c410011802c0c1b86401582455820804c8402c2c081900d49034034110400300394000800840e10307094080c01c500440d41e4140600c001d01c8054028009a0700303200c40100340443d9100c0600601c981c8070f001e01084c1c644068085410002d045284d9010401d10041e1060000f42e000040218810b00c01d2501c040304001000900c00758042c4003c1012425800405400e81c104400c820b4078000e14010398040205081c01504a00d016414941c1c0d04084515440300f420b00700d640368041d0f0320001c0c0300b19011800081c4180125078110380000e10160f81071040c40e0028003281c03560303484884500341c1182006001d1400482c120868401513004e881901c8203079841024803039003805041c2c030640d101804020b04940c80b0014688669 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 547472158 1250 547470908 547470929
    0x101a0c1504060605120f1e12040f060806010804050a020f011101090b0103120f021b011713060605060702011b2d0c151b061b08150301180f0309 63
    0x209824982e001e086603015240c0240d2030b00240160f0008001500c00d0107074820009040003e0b41c141c001440c0135215000030500d4031940300c00040301c444c03a80042004000c03100f20781e9400b0b0b140c1030010b0440c040c0104046d0601408034200302c0403440115544006580c12181d10615a13182001a2810b030084425400c41d5072070700d0480400c210034150380a040e240105002445070400410486a610713008100d40c0c0107070041003503030b40c00d596608050351503800c0c1410110029078911201e00504070707041762110321030480d110380c0c0401d0000a11800c03024050685040c0c2c9400c00640010b0503241c00b04002500d004c003240300100900c00690309046c0a00444021400c001544020700c02060428042c10f4034000c4a06c2c40c0051011004002c1a01240b29a16201100d901d9041e03c00054800c00005a5a40c1c0d1106940c06d020b68607681c480a4801d036540380d0140300d050584070040002203403820640680e00d8041d10200d00c440d00c207aa00d0b241c82d400040450810500c0c54101e80001695004c41030b0381 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 547473408 1250 547472158 547472161
    0xa0b190207150f020a0516020612070302130504200f0405090906070201050609040210050c0a0605011e1a0708071106040603021b062203050c060403050c06101a0c15 72
    0x5046158040b007180d104905002040480004400701d12402e030f440004680108001800e00241141580c012070004090908160303088a50156215003100c8031b07800a07600043c5160103003526595500502400d5034108494418a0440d00340d00d06124044024514080355003292000d04000f140c0c0500405040080c10307003840788010b41c0d908801e5440c20095400c0c01c0019005040410256100302d40040209600080c41e4400381c401c1e9001000d010f02c507000d401051004500c1c98003403d4020320148002030f80d440007200c10941c0c2091943c11219209a140954040c001c040c0030039a50b181e0380000c00b07699994058a00b10a958103104078142d04540007180002d100f0b41c02da8054400480340d61891140560600c069a8071280112a00403004150124003101e10210943c0310195905c242000c91501c0b40140c06d40d4548082254110002503000a0b500307510503041c4005d03600000c00300c417980d490500b014040040701d07040800c85858010081010410500100140844007003d0b0000401a = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 547474658 1250 547473408 547473413
    0x30b0a1503080f070302250302040b0f030106140f0d0b0c0f0412060f11090d060b0103060305010501080c01021c1d04020904140a0507050426071505040807060807020a0b190207 77
    0x80d40100c0e04c10350141c05504c40c034080d10041c540558080c2005401c84600c4a0b04503801c200040011191140e04120f920850360301c5910f0902c03c4201510510b0a01e03011071004c0d1003080210300220b051540a84110010304000039404041c8a822005102409840c0c0030b04124280b03d0740143e81c4000041501d0094140c103004c03055002e0380e41c3d61000c600901450001c001641814441d00100c80d0704000c2c03120120740402c02c1c642c041010b1140514000c02c04682e0303500c03540d00352842030300080c1c2c05800500340141700c0c1d0380412444c02d20b80f038022418000401a2080648145c2c55205d40255031100700701114a01d5940d41d0440e001958014410000d0041c6241801d00a02045801000051030a0003140d0402c1c0100182c03002c9a140a04030440b100c1d04580300079807a041040c218284e40703d441800702e031003c1c0c40d4642c1e03448241242c4e0344a0300c0f030307180c40c08880c03070491294444014001e51900b442500ca80c0451094452900304402440c29110509226070301640c903d00c58280c107101203452400c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 547475908 1250 547474658 547474687
    0x705120a06150c0209070f030f02040801021b060105031f1409060601020d050c0c0d050106080a03050c06060411370527010915020a080d061e030b0a150308 68
    0x15070340036121902c03500341a00e905580c03040d480900039520540e81c0300051001c501c61400b480d507000031858003080c04401d01200d071083c0d8003c3c0d00040c0f40c80e500410062212040c126030b82d070030a0341181c002c0216502d040042034551010b9074103102e04200283d10f0810101350358008054140051200300490318001041c6a101c101c280d5030640140202100c1c0b460b4148a40142d40d245825a0085e00c1094406010400e4440c20340740100c0d010f54079008009028001808440c08840c00f0b034036038640e551007260409042c10b0008250511591420346004821003000040d533400313850100600300940001c42c000d41d40c81141140b46000c0001d8150801c45d02a8042c020744141508101c0c01c1040f401080315000c84040301d210540d0000c3c1c0b405404010b80441c4001500008500f80180d400003000d603140c030b0361694010350103403452541780c4c07004200030040508940024865605180e0600b81550b07a400c8448a01410140c040c0b600e82d4a006c0c000001212010300441d4440b248a680b0b0440024850 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 547477158 1250 547475908 547475921
    0x2304030b250207062a12090801021c05061206010602030406020706091a0a090b040b03040c08030a0206042603090105150604080d030c03060512010501180c08010e0705120a 75
    0x400d16000300d4890700d482444085144004116005001e100b0704181084980b04008101e44404038080007000c00d1800e255650007510380e0180c41840c0b00d00701503400c040d10110041d40804000e030700c10024503031404250321307a030b02092040400100e420b484110002d16000700c0111042201d0180d01c00000340540c000000304200c65040c1c09079251660380301429144120320348031f401111224201c0c03266180c03d103840104822034040c2807034012141c4030101840e032500a9080510001c500100380001d00140382407407401010420029403414190f880c000352075502c00b80005146c0800314560661071803c404020341c4560500201a8982c90030484ca18040c0506451854994049402c010140c4c180101298251002c0d035004001c491f041200071801020203038004002c0598070000400c031135540354004100b0030481c000100b1035504100c0344080e208034011000858038540245440781d140c01200c1c4a04459200f4020f55070742d91091000d036258400e070700b40405450110410860038000035032200 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 547478408 1250 547477158 547477171
    0x203100303021902010806210d0801180c020c090411031b09090a120c060f0c03090501060906060e0f0612040f0b010501020a0215031801021b1002090a05012304030b 72
    0x1c070340c20000000c0c00303995080f919401900045a42e40081c026041c01c807049a0814069032111003092820307480d071414440980841000140c01e003004000340344120401c2e440e00c440c041c0d003c00c05445820000380d034546003c0c2842e4080c503081400101400071351172001c91b50940181c107a518000c003210760000c000100703d0702c0038400c0b03030b103400403926041000800340c40d07407503020902800c180300b1b008080d941c0d0302e0860011600d540c1c881c000340c0b044851902075540c2c490056100810403c4a40c5442e500b51030850f040701c2d0449142110400500780d1051180311600d0040c2c4242c00f141d041400414014401c550b80010307407010131014441000030352a0400805401004036208903601c5400482c2c87e06074080000c0c0d0300180b0305040d034a1030051140159002141c111701642c2e0144050026420b98121640e11805464200740c035944481c024400400c040030085011032031301b115103000912602540c05214100701607070461144440e800130664030301004401c11642c4496817868540714002c000c8410 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 547479658 1250 547478408 547478413
    0xd0c03060b0a020a021c0204090b0105130b030601061b0807111302030c07150e0f100e0610090b060d110a0e0f100e010e0904260406230d020310030302 66
    0x103070054108040c0c0d0001c040e1076015001d842d00d01c0e020488110658840c030414098a03c101c0c000582c1c540c0301d18207800b40f2550148103250725000400c1030b200321f00d890002c00f02c1d003460f0609425130741c0071400380c2c1940c0b0141000da00c110306900340c03030700d840440b2030000308081000240d08003070101a007403800304440215404510388184410b407406901040d204640e13011018843c130800585591243c85224024090000d00302c06040190341c40d1440c0102c40788020f40048095180204042c0105680107031901d0040a045c10041c078002c20a00c60b5100d001119913548104c0c0c5003940d03c0808840324a2544c02b01803012050300c0386480000d030320003203205003caa8500e04403080c90030309080d210610400102149005405d494058406d03038040390b02681001a154194200d9564a881d014001ca0181814118039120040b0a910500441054140412051000b004500e9100385030003000d411000e040e1121103040303030209645005441c04094124004001c01c80342d0720340f140d03120048030f02076800c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 547480908 1250 547479658 547479671
    0x7080f010b27040201030f020c010203070e100e060f07170408010209040b0406061b0201031b03020c0c0105030103151107060911041518110708280206010b0a030e070302060d0c03 78
    0x200c00d41c00411025000c240b9030469002801641c0a03611a040c5103a42c00405450540541d201d142264002c484d21000308006100045641c103061a04440221842c00c3c008031490881d000200c3c540580784482d8558200051400c04110312242280150404000490703207407911a10043d004c2e4000c1a9180c7c025490500e58810501d4a401103034100c800325120f1544540000741030b6500e442c0040c000b61705054507003280c40321f4041d01d200c0c40c40324842c0070780d070040c0ca40c171116004900300b001c2d1300b843c80e0400c0f50030700060021449044240241e81d1051400140712406001d00079044c0c040c10b40083d2245180c910310005100301d10040d40000442203804111409602e6203030300410207540038000700040c803c8020481e0110960042ea1403121201e00b40381414200c0e03851154940c0002a000c41038003d0003291445140c3c00d21075000141542d0029000da581400a48030050160411309000c00d038803019400a51242800660003039900504000d0303072005503500744006418000302e5000024030380701c1e = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 547482014 1106 547480908 547480939
    0x2060d060509060427050c0307090504050607021605011413080304330e130e010e1209030a0b1e070f110c03070b030907080f010b 57
    0x2100400c0407410a41030008a0901402072030049041100c0c0d03111000d001d0040c1e00031404208481000034941e82001c03032600ba10040c00540500602030049a00c5140790019845140100c08503001a100c94404036551108640c0d803034401d050701201400360350300c200100060700c4041d4541c0742c04e00302040003440c00b80303034141c4c0421141e9000044c02c12a0b4082e10040c680d018291200b40e84039107000155900f800000c00b15000c1c108006120324080640e1207580075140c0101d140410031191040207122030080480030307a03007ea58030450a42c2d40007040703043c040303610500014010f0a803030300880d9a0b508a00001601c1c00d01136407411500010b89080c01140540300d2145980c80a4110300c0c0484040e00103800d02c1102c041ca40c0202c0c11640700394078001036550440c2c2c01007064940d2680e41d001603a09201090300010414010350400d00701c04001500030701c91b1b80c8401c49200ca002203149 = true := by decide +kernel

theorem cover : BRFrame.Cov 547302158 547482014 := by
  have h0 := BRFrame.cov_init 547302158
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547302158 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547302158 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547302158 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547302158 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547302158 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547302158 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547302158 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547302158 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547302158 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547302158 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547302158 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547302158 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547302158 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547302158 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547302158 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547302158 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547302158 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547302158 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547302158 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547302158 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547302158 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547302158 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547302158 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547302158 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547302158 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547302158 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547302158 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547302158 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547302158 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547302158 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547302158 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547302158 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547302158 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547302158 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547302158 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547302158 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547302158 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547302158 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547302158 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547302158 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547302158 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547302158 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547302158 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547302158 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547302158 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547302158 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547302158 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547302158 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547302158 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547302158 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547302158 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547302158 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547302158 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547302158 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547302158 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547302158 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547302158 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547302158 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547302158 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547302158 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547302158 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547302158 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547302158 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547302158 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547302158 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547302158 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547302158 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547302158 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547302158 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547302158 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547302158 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547302158 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547302158 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547302158 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547302158 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547302158 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547302158 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547302158 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547302158 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547302158 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547302158 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547302158 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547302158 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547302158 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547302158 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547302158 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547302158 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547302158 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547302158 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547302158 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547302158 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547302158 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547302158 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547302158 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547302158 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547302158 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547302158 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547302158 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547302158 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547302158 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547302158 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547302158 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547302158 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547302158 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547302158 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547302158 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547302158 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547302158 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547302158 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547302158 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547302158 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547302158 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547302158 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547302158 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547302158 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547302158 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547302158 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547302158 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547302158 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547302158 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547302158 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547302158 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547302158 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547302158 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547302158 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547302158 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547302158 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547302158 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547302158 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547302158 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547302158 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547302158 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547302158 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547302158 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547302158 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547302158 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547302158 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547302158 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547302158 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547302158 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547302158 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547302158 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547302158 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547302158 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 547302158 ≤ n) (h2 : n < 547482014) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
