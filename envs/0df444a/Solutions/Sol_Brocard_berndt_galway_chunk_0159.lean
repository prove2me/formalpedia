-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0159
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T18:10:21.820999+00:00
-- url     : https://prove2.me/submissions/408b09ed-d58f-4c1e-ab09-63c43175f3be

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 28417271 ≤ n < 28597128 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 28418521 1250 28417271 28417283
    0x40f080304021c0b0906090309100e0d020d050f0c03120a030506010e04020f0d0b18040807030203070b0703020403052a010c050111030a0b01080117060604050a0f09123b0a03 76
    0x10f81c901e00340a43d41d40022142c1114038454000001c01d030079030100030b8550115000e80002041c00c5440001da80741c02c894282140c00c038a6030844540540d1b500d101a4a080b030248001e0720312840e01d10b00071030919407a01322241c040d5100c0c04258050522503404c4900c00c107100d1a000032180c5911004a070451000c075205540207002140d021389050750388004002c0c5000c1c610003000101020300078403e1080c1c00715401c0318034208640024005c2585040103001c4c503446481920f10308401995900c05000b400d440400000f039000c0f806008201c001c220490100c1604180240507202c5000503182c10043d01004904021940d040d10040080c01d400041030036200c55001031700c1c1e1400101c20310080c0328110300c0c140000d0341240005041c401e12070803449101c1c80c03200175020f966155000d21001c1d02c4054401c0d00c1d001d50341c01c02d50216011500c0b40e10700c07c80c0f05810060f9034000211000344140401d1094802000b0942c800c1400041056211745606c1d00c8bc004020b40c0f2444031000640c810f000e68406000 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 28419771 1250 28418521 28418569
    0x302090301090b0a0c03140a0b0d05030d0c0801081b0f060c0123010b0c030409050403050909070c0b090705011b020a050a030b04020907030c080f061f03090c05040203040f08030402 79
    0x30801041c410921810a0a00030420102d045c4021015034103403200420360020b00102003801120a5086203102100c06860010040501e030356452540d4440c007003541603550350704200205e55601c0916540103201c2d0344014061000032406001010100c4c084440c81509032400340d900b00e4031400141c80d2010f0b103e034001c0046030b81801c07101c0d540348061032203800018021030020800d100340c101514200c1000000450400d8100105e040c01440e0162041e1309016050081e10070960300e5110140c4208019074800ba00a00e0a15005070410070150141d603940c1c11460052050f0799000c44002040e003118550681640103e001151100d40b55401854010b031204038040244102c0f0164140075030710942d031003401742d540e800d400c600322001485a600014076000c04164042400c060250b00320034024440c0610003c0080c044403a45a500507800c0801e41f16803243d4244040e45015400414042d6030a41c510710349503644c40e83d6407404d40801401d840002c40400c0954851101d0110351025407802541 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 28421021 1250 28419771 28419773
    0x40603050610020f0304060c080906070302011407050301060219020a0801060807060207060302030f060909010b0915031b030a0f03050c06040c05040b0a050916051e0c0d090503060a0507030209030109 87
    0x5400112252802514003a114050103440082c0c0d02c00022944000382d421b1a0604034111400d180b490070544071000103015800b03c0d0703039030180103042d2680719400024990810100208110740018201c0e803d00906000400400b270700460302281a05a40c0f400321000151840064045011a00208010761910300085401c550004605007550026001c94603800c1d41c8010440c140d100448032080d0314001c05c804134220f1300f44510a160004468000451344c080414041100240d00f00c400c141144990218520b0717504051103014002011540010380740389141c8082603aa214000009244040c600c4c0c04074185031241041e00c0e01c0229910580303000c1d003443c0c20000420780d02409098860383c0361101e220032030702d400c910030740131900e01030840416542c3e40d02031035109840c2c0d240580180907040190b850308034141242900300c40c2081c45400d85402108140a26082c4011a11001e0000380a8148400d54000803045d40c4094401c0000c60f0035034420a04038060b001e0300350005c1d010360034424000 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 28422271 1250 28421021 28421027
    0x207050604060b130207080a03110903010504050c1207030506010510051209030406030f0b0f060c0a061503050606010f050d2c0f010e03040b0906031308040902030103021509100819020406 82
    0xb02440d074040302c590384e80b1240c0340d4110040307104482e0b004000d090200301c03403180c0c2802a0030030711113103d0800d520360030003100501203402d6030b1048404540c0c54012102c040d26a2402d4980588178602605c01001003034215030300d0f29a1100e06014540c40341d0f0201d0440000d41c0d128a00b02c48900503032038401c9805041030191141c0d42e400078040d03d0042800c019002c0002c0100340300c1c017490340ea0300030004c200c45c144840601441d60300c100c0d1040748900400d1004000700e29240141c00c6141c80c0380070000746c0c503407031801e080c0d0402c42c0c050005410494a0a041d09540d588a000d0b00c02030300054000041855045001c3c0e1014541d5601001001228a0465500b1480402c580b0000305000009000800c0740c0030049481e0f105502401c211800c1c1030000000034107002c0080c55200800b140000c0315200700307466185154015500c400e10154000005000b14203000700d4010484000160103421b20716450005079a10141103041c1c410802d10b07100007100d0a00500f10500441004c05086680d1611341c10f0003 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 28423521 1250 28422271 28422281
    0xd080403021b0102061501090906080303041505091b040f060914150303040608100b030405030c10020403020918070302090702010906050906060105040303050f070c0608090c0d0203060a0906020705060406 89
    0x40d80940158a00140c0202c1d202d0b00b040310544050380605810360341c1da00d00e003401d0f03a01d04000604101c61481d0100314501c85100715009400030314019030b128038040c948403182034180300383c18446a04010601c4049040003507003050780c45003201c42800c07400098001c54018401480700c1e40b000350400c000022401e906070300c01220200315040d4120325336180c28500402c519040c00840e0160300800041100c90700c01c405450f0442208500c0703120300c86d07039441d040c0401e4009940a4074560000511a519400c040050a020001d01c040c25400e0034a1500050300da0134006144c45411411006000d48119040c0018405142d009003c001c0c40d0900400083c000d004411046800d9881d1401080ea050380000c2c2d0315200340016515180303024215079040ba2280c0101540c420341203000e01415001803203058400b000b803d560b80d2003050500e1b003802003502e08a0b002c207000b800380a42c0201c01015842c003240007603006544200c0442d1081803403030001e009210700c0c100540a40142403d000404c400c1e9044 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 28424771 1250 28423521 28423523
    0xb030a0b0d030905010e0a030c0b04170f030306040906140403030f0c08010b160507080604051005010b21090a0204060914010506030907030209060d021e0415050603010902070f050d0804 81
    0x8102000c1140144100440e2078031001e400b00341c6032141008503610424541c20005006000b208503195207686400b6031407416003250a000c8000f20f402d200d4444d002040b6026110042d00600901010031a80c503100c1c130003d46464011a101c01c068410300519400c8444100101c0b00c2c007041b5441e240c03c0060003019100b0715408101d042140d01c000340c62264a4881c144c54100707440c145860010700b00c04103911881c100c1190340340281403001840c0f00d018040c0501c0f440c06600580004030641500c00e003281c5058001e41c428070702c1400a60041d0b1040b161410050100310f040c001e15445078842c461511588000095006050040114041c01315030030414410f00c3d0620f41703845503621141044401d00003152000d1996100c2903040000d803410821850300440013401a070280241c94000ca03044014082038403d41094155101900e82058070070103024540498107a000a420300c40015220b00c010301c200e0280075008100c45040c00161701084d0f260715440411110410202c11010703108540441e0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 28426021 1250 28424771 28424791
    0x81504110307020714010c0506012606040602030f0f1521010e03040e100303140304060915020c0708030f07110301020c160e0109090807080a0c0203010501121403180d050309040203010b03 82
    0x40c01d05154000d8880301c0d081f0b680100903050340c1c1c0c05c001c0721400e034120002c0000310300c040304400000b8540c1c05005040c0160f0080074056a030f0700d052041c030f00b8400c201a0841c0b00320f50b0502c0812180d0341e507410f150320200000b1140400600386045040d0350f0300e14000d8039603200c0e510b00b80021490010010050007101c400e00c0b041e504954880001e100560030510001e03001c513080711000d603503008980c0c1c001d5074000e03c00c0d038001403600069180d01c906610800c1070080502d45c00a060341c00440d081210f01c00920031400110b1400240361400d00e86030056400c014545004042d10a071590750032340507280300c8031102c021502c3c40d9100700c01e42036014a142c45030900c0404d40c000045404c086030300450f81d4290b00101c0b02845d1207415038482c00c1582c0001009801c1020400072140165828000d2500a02d000e12042c09098414103080c00000317481d840b8091164010403020100103000c5401440003c001c4511b00c269548a040845c1148146214258810300c0003001080c0d842824003e0350140090700 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 28427271 1250 28426021 28426049
    0x120d0c05100c02070b0f1306050309010e070305030d0213030203030f040e010803040302030c0114070213020c0d020102090901150c080a0302120105030a0b0103170403020301020412140d0815041103070207 89
    0xc07205040b00c00030380ca41001a00602c00070301150401d50010b1507403441044100d454a5189820021607030310f03039040100010360020502155038000d001e00c010b4031618030058078100d0301e50707070f92130740c1d20b2042c102e4091101c0d0700030941a82454250315884001c1d600038003900d6a516a2440c551040e070700c02d0042440380926140049460342000003520207403035002e0000c3c01c0c03004da420300640c0c030543c848078615041c1c801040981c0060322101c0000398040d221800240e22009a40178580c00c1c0310420341c0c048216841403040b511659505084241111043ca020070041c0c0d10b007140032912800a0a4060446240000d0842229902d43d00400d0088650101a5110703600c0d01c0801d81ca6454010018110869034001440810414500242c000700140b002038940743c0d40c1d901090998105134858164500940840c0060280c0405401011301a0201422008840160190440d03401410004120400081c00c440c06d45032940186040f4a01341d0700f080d180c1c94640002551040070740a42c42c2205850 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 28428521 1250 28427271 28427293
    0x20906060d0911030d02150f1b0d0903080c0a0e040c0201021b0a0b0601110a120302090a06020309041a0a030b0408070606090c0908010203010609170a0f0f060501050a060e0f120d0c05 80
    0x1040780d00c075000b036011031103d076600c07618a80c0d0007064001e849e069103030400640702440c40b40c4010051941c20400800422019054100942541001400004013440c2000503200d070030343c0302200889580040b103002031990082142203009001d9810260500c6481034856501502c0008800075090303c600102c0103150f460000448801550300304080c9540d101180820000e45242003103c010941c0b4500141441d0b4a1400501511010352190300941c00c0042c4603400c038281401203510000d44a001104070300007e80c04100c602e1501d100c007624028404020030200f0110a045a91144c2c01410a0003021745803200302000b040c2800506000c921040c0e00024a40c0d018000d9034101c3d400d039121611003d1520010a00f040c0d060381f4600c07820b0040621520020b05140b4801200d68001d58014000c0300c198540030044600607000035101d01000c0108108036503000190114082c0c0554140c030315802c02d100821424032034044426064002e02444041440e440041c2000d81c1f809002107424201c03032 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 28429771 1250 28428521 28428523
    0x30c110411070b0402030109020a0f0e1303021c09030204090b07080609070f0e030c0a0602031207020f070b0a0c05060a0b1903020a03030c02061b010501090b1903020906060d0911030d02 81
    0x410061401410070030700094000c14403041c0044e902034005400403641c03200c0c5a00082440700d46400c903140c1124140000d203d01a4a444c8803580901e0036540d40601000581b0081d50b590903e00c60b01c001540150070a601c42c1d031240300008025a40a44140400c541c0d615054030005812100c0900058401002540d2890058005801032449440d100300321f440f40c01c000c0300d00c02e003080c2500e41c01d40305007800c0c0041d6894050000b8001c00e07030780c0d0146842d401240854a20074402402c840210b41c402d51040b40c008801080003001c841102144aa039a01440002e0303482d44600080900640988801c01c03010139070a800403044221308030b80c40e1081210800800c9850040b07400041c0d000003111405100107030045281240d1140010300c020f007003080c2c0c07050282e40002d1b004c8000c0c010340d44410042004030003600460244138012507410b000e0710080a441310280901e4480a44a41d030b02102141c42038a0b41001c455140340c100f14240002c4031542000c2c04180101c400365402403007454008400c41348 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 28431021 1250 28429771 28429781
    0xb0a1b0f020414060f06030606091c14030a0f08070318050a030909020414040207020d02090103061b08010e06010c020f03010e1609020403050d0309020f1e01080a0e0a02040e010b0303030103030c1104 87
    0xd00412491401043d9802c1c006c154000030a131a802083c2040300504035510040030045c40301030f08107002080b402a24208180f240700703100d200b100f580140001e080c42034029003100c0c111012440d1400c1c095954010842c0134185907445c03030700e00f0030b40c0e1281e0f403051180108010240301e0080e201d140d0010350755540d0000305e05c42c1d4880e130100401c1100d41288140342c560001c00c03005000400b00c3c102c80d5802d40000741c4441003130f4021680705969003080c1100c0f005103410440c0c040024248442658904103031168030b640000c041a0401030098050400c5541d1000344031192403024000700500e103c02900d99548810281040702031103209400010505c0980c000c030b50960350b0010160030060380894059015006c013110480c0c2c0403000d002c210b00681c4480303070303800f42d85402a89860420701540c1c0002d0302c64403000d010f00c0050307801c010f0303210906900000c2c0c003c01c0540c140d800151024002100b04d00402c9150b1f0f2076a82740c0000000003082c5a840741c81e03440d040c0d000755041991a40d0303030030410046030303 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 28432271 1250 28431021 28431031
    0x5041401030b0a0e1602010b0103020a0516150608030c010b040608070302130608010f0b01120605011d01170106080105130209010807140909091606030b0603010b0a1b0f020414 77
    0x402504480115501c81d411404000c1c10140202c41030036120403400e8001c5504480c0001e035030002c1203840580c1ca0f4240140f031b40801c003e090861400300c207441c0c02030441c42441c981144e80d1898810010030000c0e408032a18034030a0202040245603141e0346499241e40c08420b4030419076003840071140043c41e052241e4411503038208000d104203480c550038444608404d041018030b00780c0d1a030000406840a00911703580201d41d580014604400030b00140c1241c4060024195080c90711009010300d903004940400441c40000c210418400c0410041316030442010049071842044400000d0043e000070017681a1201155403190781c5441152180c2240100f0910b20b000400c10f00101e50305a0040c5458000c448422041618044200c0046003400c0707425110000903601c18440341d8100700a81c1600e01c0909528942881004812400648140818010400300100020300c104030302e0300881c9091a194108490891007240c9800c00c0c030306100c0361080590240b41064003042d035086844010520071 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 28433521 1250 28432271 28432289
    0x1502060105030d0f021204090209090703020313030509030c120a0b070c0c0509100308030708220c051e09010305030c070e061309030e040212010f090506060319090f080c0705010504 79
    0x7041600d0382c1242c603c0d03003043d412800d500465046403946c01615009001404900c8005a919a141c9003804103c0700014009820035105005100f0904031500c010001b2941500c0c5c1301f03456562000c0004c1c104201c68004603401550400d180e50301c4400413448440306401011a507030b05540b608001d45642d448494002c12589860200f40262310380b119078907801500c48448501602d03140e03a034a00e000c0d80103494007004039140d40f041103044d1000c0b034460380c0e800302186004a0b0706580390b074030407041c00e2150003954411406158000e08480d1180c1184080d220001c2c141000365940e424129220343c0300d1114482140200e03000888c41511801009001c0c0402070301e0f808021045c292280014032000b0f404504002d50502d100080355520b001030009110b030044105101c0d450f00c1c2030788211440070783c0100943d501300000c01955984800c2580d03840345294448803da003c054034420010002154003c004251481b0b61406108040c0080c2c011140301c0011a000591100c005464a02880c4104040 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 28434771 1250 28433521 28433533
    0x15060602030a050a26040809030c031f05150301110c0d050702010e06070606090204081b030106050d021302090d0605070e0d05030a140c030a03090308150604090c0c1704150206010503 80
    0x3561045d003c14005500d510024101d090112a50103500780c410b5809036145800803030042e1440c50184404234820f8812002007040c0484a2504454401000c00d130810b002d40e94000601d5805515900d1009044010000c22031130b92815410b44080e08039580710049881210900300c0c1882c011000c80b51007540507110b4440801c038000810119a00c40304c07046501ca502c81030f0008540e242400540050200c050141c4020381c05048141030301c50b00104494802da0400100700840c0d01c42d150802180d40c0c0603250024840180a030b0325020f485054851a0031001a01c0800b00f841025070000d402001e940d84c6140b800020407041045080d403101c8040d096400403c64100268015000140c004401ca8612410030101407000307403d6400488904010a444140380800c1542c01141264000c08400702802003400900100d2114015800380036034880d0f0324410741030300501403c020364083e607005074110710040e00301c4412071003600700388a0010590703840a9103444041c0080740e0f642c141c500140c01024 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 28436021 1250 28434771 28434787
    0x627050616050c0307060f020d0903110603040203070e010f0303030f02030603060a02090f0904110103110f04060f12020307030605031e06040b13050a0b0417030402010c0210180315060602030a05 85
    0x10707084910320031111840b0f00c0e03118000540301171140c00c0c000c210503100c1180c1c43e2105030029041041a40c5800100b0016900c240001010383ca801002c18209a50082d125a92440481e1500c041d0b90094a01c0010380000001d0000500f14514141e078825a0244500e4201514804c140d0105a03400d550541000d400135a01002c154003418101d00000c020a003040d40c210082481600165815200000001220010795805000750811140600e14031480c0c030040400b00500703802240503000c10400b070803248525507441002420009002c82c81c04665a0074240400f038000d2850344a41c41c00307401003d80500d00e01000c0d00403000301c108200c0107401c407503a555460b03412248005004050f401c0c0303c084d83c2404120108540e0015074850303584403006081504140c0340e5161444400c1ea45003000308101702c0141d0340491a003051580c15121000e4000d403100341620103041c0c800b03c4200700d41283e86c00105002d00e242e5900aa400748940c100002a2241000c036102c0c840d541407480816030401500e9 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 28437271 1250 28436021 28436047
    0x8040b04020406050612010306050f040c140102070e01060309030e03030301050105070615151205060d030504050d03021f020901091a0708180303390d030b12030406270506 75
    0xd500c03034030082001a002c0e03111000030762540c010905000117a0900001070040210710b109298202c25241030303484251419541e01e100700d00913801214440c80140d844840603034004c0005501810a601c01d6443c25a1107190007001401c440000b070300018604000c040003400c021085905842042c0c2d186403078142c05450b10740190400c0e01c1200185010560009558a01c8040c030303004040f0300d81e90f031202c042c0f03181e01114142c481c0501003034481c040000c03a00d80000d0b001400c80381100c4050b02c07613400c0545541003d80c03c1849080c160f072058040c2c03010f0b82c0c0c0c0d801c44030743c001c047c0380350241c0300c0f41c005a894505480031501c0412452500c03400c200680001b0400410142c01c10450381460300c0c806810800100707055800441c14074030090040ea11149003501c81020301400c20544040c100c22010301044203582e203c0001030000c0906544084000c40c0d900c80b2160b010f44444030804580e904c0d03549200083c0200b9001403000d1703002d070b11803200a001103481c1d0103c904980c0010700460030052411a02 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 28438521 1250 28437271 28437293
    0x601030c020309030303070305060a080d0c0b090c030d11010606080603191401020d02040306060501170703051008060c0a030b01141c02040302090907050a080a030228080408070f060f0804 82
    0x1800c15840280401107040c4c0d01000154401d402035680441c40781003010a200d00c40030396030031004840d04240c01c8143e4699015885041480e00325580344c40d680c80e003c40d07284c01e21300c280c500350303406014510001c00516000181c0000ca4005d0b100200000c6584903800c40720000140c4080f0751503041140000a07a14140302c00840c030900440c8020b424001c456616822640121400d50f40c403030f00808c0c204280000c0e44500301c0200003c1c00c2c64290001d10490501034200014800414141d035180460644010394046c0c030040e042e4581166a9810700c4108206960048201980042e08203509180316500c01d80c00201c82c41035044406040c003120004a00c9012a0391510703a91325a804d01c000000759071b55000d03160140d2a128045c0074900c0c241030600c05080c1540c0c200681d01e0b40603000101c0026400030b01012201001c0c00180442082c0044102010300d0510019001510104020800e06000707d44101201c484084c1c042c40a650303501e00740c8a041d0500b6062020604045c00240400d10750418 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 28439771 1250 28438521 28438541
    0x909130311061f05040b010807080414010e030c010506040c090303050c0c0a03060209090901051509040609020603070206070f0e062d0412030810080601060c0f050106060305040b0a05040308060103 86
    0x80c1d03001d0124514280d20308401101c040403501640c03d103002600303420003c8036000e4201034406000704005107001810010000d49100308100c14280010700b84407004622040c0804801d0080c42014020022942d5941280300b0290080d460074011072a249054422401008082d8450540c01842e64a06586a810a422000c070500410000240355a42c060718000075611544c001a1109030301e00070b11182810050041803d82c3c90841030150802d18003207641403102d4119502001da07682c1d40303002c1028000b0440000d400010100c180124687c01003041d900c1284140e4603065400041c0344110b0b0400c0c6c00450040d00488100000551081e402d180da8440060850100841c1810799600d61155070055005410608011100f4030030554400740b0190000e0b014038426840c0e5007001c4a00e511464180b10318020302002c02030307901c1004022402c241001e40c12000802280784e440802a0140c1801c907011507694083c03500280744514039204907400f5540580d92288540d6982c4015002854030240c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 28441021 1250 28439771 28439777
    0xc10020a0b0f09010c09061b060f15030b100b030601030c02010e07090e010f0b0a0b070201140706050402131509110c120c1905030f0304080d140106020c0609091303 72
    0x440314020541001c901c5005010310030480803540b40070344416007180c10914010381046030f2090200017440d07001980d0310108034000000e100c55009464524004c016440c02d00b0013071410110f8038809a15100c07031080c100c0b4003c501401c0355907503240b03099104038164015000b05003002d101060704c95200b0391001b8440c440a0000081000c40006903500e0054998062100543c03111b40640302030f002801001d0420607454414442440b000c00010341540c0c1c035008070050140b021a4001c207681c131450716590510290003560b951602281400006400101e07000d900070540c0c150b2080700d40c0c3d042d101e03540c20880a0312000c01c6d2142400400400381408554001c0c05003414085c4c904090010710103110b0606250000d40d0391030380d10418160520a644441d8070351a010415440c002c04e40c0801180c50103105402466940d981c1e900e4414103a008000414032135500d0030081074400d1b102011164140d80c596001c44000329040010480302d4402e0700e1030180c04c064224007040c000315098080e101d00d41d101e82 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 28442271 1250 28441021 28441033
    0x12080d05060a03150e010b0d02030304030b0403140406090e070503010302061b1e0303040b0903040302030a0602030601050d0c180e0603030a080910050403090e06060403030f0507060902030f0106030204110a020c1002 94
    0xa283d81c1c4c08000c42012040801d551042c1c100c0c541c03d400d04c1800b041e00b5043c0c801c20203001c0150000b039202e003c2c80c84050b240c50165000501014481d100755881b400300040c80940300c6441c0c41008240c000301d0b028100c141e0f15420040f03014180942d0039030b41200d50060901e46480f804601500c01000d0000a0098034811000070491401ea800c001c0d082c0307012044000c1d0341707a141504100c84080030142400c03aaa4000700802e0000d610003141c070244845d000f000c056500d4032070400485003071040d805420420751401c01031425050384030150003011848000a001d01c1c585a00018408400548609a050b0700030810140300e1409020102c3e4032a8004040ea61001458008241a15002c550440000380304c00300c181721940301080e800350024415980342c0c0c00c080c210758001c1c2c1101d030399031f45a500784040411000b0401542e90007400322560301030180d0b80d200070f104c00c0b070754060140d42c01700324440c6080c240bc841601c1414030a81e8040031441d4010f0004410310800e1140f490b10084042045001d12 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 28443521 1250 28442271 28442273
    0x60b01120204060c020f1e01051b030d020a080a0b012717010204050306010602030304030903030305061207080102090102010b06180405040213060605030726071404170106080712080d05060a03 84
    0x1610180006105644800100013214810031900e80300324007102e481201102002c4000d111014058102d4032002c0c248a5520708860840384a003a1003540c02094910000600c0310502e069a0043e003070842160311028500e807914480d141c140e8685001e00c5002074402c0300380d05000c4011a000c0c503441d8034500001d040390b03a199104124640c01241840c0800d81d0001802c1125050030400d00780184058030140d421810715030380040201d902848081e00301a21400445c00c0340e5a10044070a0ba03d00410440d5034031036030307140c0f558040d402c5214520b0141d440d10151300e1050803c0c4049601c002074020201880103521002c02c402054003400c01d0f0703000888916903400070500c41c42218040c00d03840d11480d4807480c05000081286900b807401541d10001500c44c0aa018680c29050f50859224144800c0b0301d269807280c904540104d5000c0410050f580341665400c10041d0b0200056480318000e8549003500d9540000d001d030034500b0001c040035070400c50701c4e92710007240d0b000a410a40061580d88843e6603 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 28444771 1250 28443521 28443557
    0x14030c04090501080102040f06141e040803031801060f050d060e0a080703020c030106050409050a02010e04020d060f031703091002030901021b060709080c010e010c080702030111030a050919060b01 86
    0xb090b0066401c50790f000405104406c600d520b08401480c00745003015090340a801c2b291076a000381c03002c5c001ca0001c4410f00e2603245141d4001c3d40c001d040103004813510b910708242d889c6102d444c40081c2c1c003404e500c1d00c000402d07901041c492500c1a244003800a400a070010b070349031002400e400240034441c2c0030b00d11403030303000591080040c40528000c1e4000d100031034001e0101401c4508036400180f1032440c1007a039800050020400240c80754090030850b000380e640c036021070701070300c41c0c4001d247c0c10500d82800802c0b0000349a07080d074281ca000300d00020f6401a081c0482c443ea00c401d031034038a0640c5c44144402400c1900360000e550281d9000005410001c94806460401e40b042d03107541510f03000101080f200b254041c00000080039204010301aa07a20400084d02c5a1041039002e4104900b5555240a00c2030303010889500541c00317402000b60403001800c03440644c20541c0c4500042d070421000c40c0e4403940020f084015140501d182c074541c051155110002006150280c03030601c00c11242880749540 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 28446021 1250 28444771 28444781
    0xa02120f061003030801060914040509070b0d090501050618061903052b02071406090a0e0f0402010f0206010303080105100c0b070302030a06060201051e10030b01080d0305060d0314030c0409 83
    0x40702c0040c02c40190b003980380142030308005030018000c010845404204c904181004102043c500343d8002541d6241c03c000c0d50300f0080704c0c1d040a055660006005411810300d907226901e114015802040540c40717840030003403103031290746404a041c4150710100b4010b1402000703410b1490103d5a040402070343e02c1d07071020704250040300300c2c08010382c030340f0420000402c6481d071040b0489254030103011064100780f0b001030650104038496004900100e002c040300d8842e0301c1c103030003d030451820074502454420300003503000d035084070300300d000419030066110210700020307480d41a203500d80c0b9a406d481c0e00340014071402810590003a4100b04d0b8032310400010891100003107000740303040c0d42d0150b600d10f42003803c1801e640003a40410f003160b140c4820005080c11503145a00030440c600100f84a903100c860212072510420381000e0004004040001400c560020b8480012003458800b03114a83d0f802040011003421118081c020a2030b142403040700c1151340005550200d0412015804d154a074a00380d41162 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 28447271 1250 28446021 28446031
    0x5100f1a120312040c0611061003032f060105030d0804050606060d091e03020c0607150203100320010314010e0403140d0603050307170f070f02060906220602010c020a02120f06 77
    0x42c05c0c03501c0500105a200c0c0d01d45602c1074484004008a00780b03070400d04560411880b0140411035031070b025040540d044001848179008841020f02075144108050303031600428402c6911900c244643c1020351030191114600c40c0d900080500b00703d940304c6051164030362080a041021aaa4a03005800156010000d080709801020fa92802002d1440c000e0300c1c0480302d00050384102014084030300022048422100030344224800580c6039110060901150783c0b4a4000526440c0b60000e08003541080a1000300d140800766410301c81c007440e081184184901c03c0c003d00001c80280000030340464020041c03200c0280c141071181e4070300825803110404540302c9800c102d8003504005018000c0c400c0c07a40408901c0300f81c2c02e03005407429020400a41d0544101200249900407004200d420b558903d019180d01d406c0c00340c4419507940c4007220740848a408110340d2140c01000b42c8010451604c140300e04400c562007a002081e03400d1207a020401035501c11000ca100c1e40c03245c443c5588030b900080c01024028 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 28448521 1250 28447271 28447283
    0xc08040f03080304050d050f070201180b0309060f010918060915060b040801050603010203010503060f07051909150309020307050f040905010207060212011401020d030c02031605100f1a12031204 85
    0xf9060600c0d0450a00000e00000d0301046010301000e001d80341000104d94039545e09003480388441000e113070048003013665a44000c02c3d401d008000c01800c82c1c030204819200d2015400c43c42010fa80300c40707118088940580c0e019000350104d03918900014680c3d405036600381d0085040e401d040281034441019524241c102000d28072010408008450707003402201c0c0c010204800a6055606010100c0e5032814003d01500036815182c012546550240c012104001003c0f03a0780710064005000141c0b080c0150f200b6109442c280b444500c5d8010310900c1641d4841d68004e014160b581e01d0700f01007103070f6105480d102c141e00c80e0340d0b2000b0b100003d0092008100482c4644801368950800b490500c1c2d0700c0d0720507405000c42200b030209900307440c4e0303004c208048005a1410700060482c00414120b1860003048030103210340c140c046e050000d00c0300001e100c60b51100508810301545042c45401c0f42943e90100140d10700618000f8242083e18081c01000020040c00341107e041815020140384071074002e8500b43e80c1 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 28449771 1250 28448521 28448527
    0x130f03020102090a050103020423011205090106030b0105101d06040509090109170301030816080405040c0908120a020714040b061c050f0601081501030e07080115050f01020d0c08040f0308 82
    0x500e0911610300e80c002c05c4242421400c19103400080941c020031202000758041c010803203072006038000c84142060300000740e0104810726004005a001341024041510076242382c100000305464480d401c0c44645801c1c0d074910030440440300080301d48900c00c2501d154071800502c00418035440340480340d440303407603d60004a46107015052100e20b0703010347c0005c01c4010f0810801403020031401d0084580c0c3d5468801e00d02c490a0550400291b10b000e41d0700280c1c0d0050400d4074581c140750340954051b05440b4081c060703039032518822882ca001c600c80c2800c04401368001c90130030820900c074240c04200881c2d0103480030a101802100040c0c0c564800d01c45801c6072902c1d8581b07901e4011680c1726540c2c0c03002010381c003e0070900380040080c141c51002840003000305292202442143d10a820070189117654400300c820341601d640180b40030308a80c0c4000d41880314030301000122483d0a028000c0c0d4204d041e0081d0201a41030407040b0b5048003000c0342038891000810000951036500340c082d1004600403031025403 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 28451021 1250 28449771 28449787
    0x80a0302010f05071403150a030204020301090f0e010e0c010509120f0307050d0c030c0609230a0224040501050d02040506070f14062401120f050105180c070308130f03020102 76
    0x460f40b024103008100105491007240e210689070460fa00101c11040e80340780780041c0b0300025050019a04025005030001c40002603004a50700983c400c0300740c500d424044140c0751884a4201c0301d00000d14005580400c200401d1940120002c2c0160355003d003213400c8914010615038a0120700b2443c0c0445a03000050090070f210b130038056103091041c030303290440b43c1c003085403401050040c40c06800f51146546981000030010030483c01043c00c05e0f074080344090300580b004d074aa15a00701c0e01d8203900914020f80d40d185400d00e841d9102c00c180131030500c034078241410800116800c0c0c0240380e1201d00140e003084081400c2d43c803e80600405849100c000c10011850325007a80315683c40031007034000b1742c0184e05100000041c254403030391f907158184041d40c1031290755004a444031400c08403142c0b26458103222800c181c015400c02c50680340180c5400401d9445280c2507201c0c460110707166280740b4024404a80020701c2807101c19040860485141038590349600ca00301401050f10045000d41c2d40010050 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 28452271 1250 28451021 28451051
    0xa0c0614040c060807050405060c0f0a0c06090b030c070609140a0803010510020c010801061107091401090516020d0e0a080f0a1401060f03021005130803070308010b0a020a030e0a080a030201 83
    0x40c043d041500d004400d41c100800081d081d40114000c00f80300380404181c000125000f00000700324880c5042c00c5a0001485080c940d60f03409540c05000c0003d001c0c0e01c00450848042c1d8122801440070590f0945006a00d880740c800a00841c58100c56140c402e41c0800d1404408118100d03145c0d02400086559500d4038007048441c450040000095402c502e180304996071b00500d0040c110303030751424100c0e0101070010f800c900700040c0b60815010540742910951084005420071070507640400c1c802c11403522000300381c0c242000360301d8611300143d10802e0541940c901c070704041d0a081402030700005519455024450901c03d450925641c1507011510303001c140300a0f90b02d9603a2a20051000f0000141031100010b210b03182c07400080d005402e15140e15400c14414001c83e8202c0b0360003094441c08a41359105941c0b6035028071001e900103035100002041c014951801c8680c440b40d44c0d001060f40c0c64095800355242040814042c1e4043d0a002c0d001404031f8080c8401c00d03c082c825400064280e0070b4000c1d01c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 28453521 1250 28452271 28452293
    0x121701090e010510050f0d0507090e0109170c12130b0d0b031e0703080c0c09190c080f01030f030c05030307030c020f06040b01031b090204030602070302010f0b0303040b0a0c061404 79
    0x11240d00c4158010030025600c8008440022100585410300b22000502380f071071408005600c02d50100d0300d442c0074450004c1041d446801a00c0c4180c1c005c1400504c0d000d443c0a880c000c1c03407644071070b5801c002c11100b0701c4580c000003040c8040e42662420205640d075100400325403c100302c030120072925030b0218201442c0a00488000304414041c40c40c0c1a54400905640c96000d4003009200d440000f403401d02040c0c0412514845440007401c210840c03804180600074150750349d00f003040c0b8a0401c81c90001150041c0d44041c4a1480e80f0045191a032a41e05c44440c00480e2420030340c14003006012001c0458814001140b285038262030120b80810700c060000d15040c40e00c80c2c8022950004003d00002800b1036902a046940001c00380700030f50350b80070810040700290342c052658544009400810860030f50060205907000790001c00c00c004841b0942001d45140502051b1315802c00c02040c083c040c004c7c0c0c080c0c2080c00042c0f502550640241d95250100c520741d03482140b00c0041c21040108000d804014 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 28454771 1250 28453521 28453531
    0x108010e0c010503100b070c0e25050a110a14060901020a0c03030b0f041109030c01020123091207060c080606090d0303050a02070605010807170321130f060506040510080703121701090e0105 83
    0x3000800b216407810ac00b041070300240c0640104903000a09100302c501c1038048100d06491002591948c0786075203002070860009035520300e543d00070400050204001842a42c182c26001d8031a82041e1000d035608030010101d60007095400381c0d091000d043c290310f0381d11900d81d9280c8498992691006450101490207240301c0240d411607042c44a000b03141c07464005480c440d01107101118180b0740b140000749042050700c0396001580c030004900b80050140c6030300460040c180540796a0080c4d182ea0f000c1c4a0a44607110310706800100303103150340001034400d6201b150300c0b6413600001800c00e0803a95506095420030390044031954460785041c0140e050706034281c4400781100008514220600c101501420405d25403080c1c4000306400248030701a4440c50702c25500e5225a008034020103074a00740009140c240c03a6035015601d010009400c4c1d1845065000a9640394002418400e1540d92802031a101c0c1e2014a0f0401101256048010b100303c0e000501030a500390300841c02040d8100801c0c01c40c1d1000f40 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 28456021 1250 28454771 28454791
    0x1203030708091c0c02090606041203020d03063005071a0403050d030b1c0c0905130b0c0c1209030705061c0b010507080a1d12070503060108010e0c010503100b070c0e 72
    0x190501a40744c00c01030101401341c0c1a1620304030366903035000082d6140101c0e404007042c2e40070f01031004c04041d070201e884c5400506946042160702d46960503010b89440401113000d01510f01c025010802210007415000f4a100310300301e86a0503259a1071903070230480d0000210766060041418000c10500784407402d1030048502c0c0030170081214100040311419400c9040400c03282d180c0827501400074008100d40038007059441031210303042031580d0422442c0c210340107480c5102c0d1040803030707507421401c0102c60407103018800900481541d8402d801066225001450f4188103400c4001495198103015140c0d41c1079402e02c00030100b00340e8240c1410749803080b4800741040380400400000a501605803448005640b134641e2014140486910800b007a0502055102081d404241d01d0b100e0700107140d030181c5c1c0c415802d403420340c1da0703640d0f0345400e807507920103d42180d0304460205006035204101965021062403800c200c3d0b241c0e00e0794903000d142d0005509903501c050048092000010a685442d000b48080d1 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 28457271 1250 28456021 28456063
    0x30405210403210203040308070507030b0411030c090c220302090f040b09120a0e0303120c21040c03020907050d020c0313170c010305060d02030105100905070912030e120303070809 79
    0x224000c5d02d91045d400001c0241602042e21001c0c0801008014051a40031340c03108050708050500032042540c80001d5031191007a003c00d80c0d003074141082a1401200305848151c140a642c6c8007890040c018400b080e551840d148400002585d103002c3c50501440c2d6104900c0e0b103d050a003001041c4403c003c202e45115031040a041181e80009001c40c0c0d40c030402880c1c000001d803e0f84000a0861003981c20550118003440e060055005514004081d5600a22102420300c0350b9012001074600045502a1070020b070200100054107015840c5503014809107856880c09641d40843d50407a0868079800074282d00104507040c0700c10409400c4cd001e0021259000c0461010304011030380e50304446d001d40d0403d07854401259840d103a9140903403c89900900a010700e140002d108400c4601a00c16502c00c0c50038040401e45260180601e241996051029400000d0050300d0641d044140d0550301a0040c2012182d5040040d0900c0a54024030091740c441246040801220f85807911040b041c40625080c0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 28458521 1250 28457271 28457333
    0x30a060203150d1502030a020d0504060b0108060a050603010b03040c03021c0201020c0904050307170c01090b040b01050603010503070e0702120301090902030c01050c070e040f140307060f060506030a02030405210403 94
    0xc07016104070741348510809030380c81d950020440e0280c002c3d078a8090b0a07900f02001c0c4000c1008940044103440001e81e0350000e40e0740c60204010441019110303654112500b00018040b41802c00011075109010314441c0c029184e9076400715100c00070a021111240701001010300c00c41d81e050000342100e0904546124240c00c2548465440c1e11540304003e002004407003014205490440076512002d009000811039100d050900364607107501140c0031034241e1f001500218542c0340817402c0d40d05860b07001c5c0c0105105030400c0300c0c101100788058150410343c49510700c440c4541c80c0f0b62008501074a00c4800c0443e21403080e10500d0b141a051211240c1400301c14030034440314080001c1c0c040c04480840c11030400940b00c0381091064669003440181c00000300ca1000c20015400000400c1c1951140004200d4154101007550480d01c460094a62042c010400314010004035000380d0340060184090b100b40089407601110b04001d1038004a40300032000c1400c00c14000c54030704001d402d242a003e10842c031600 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 28459771 1250 28458521 28458533
    0xf0304051008060301060b0307030e010e0303040305070b07210b1305060906041109030303010806010f0b09091501030b04050f06120a020901060c03050708030109090c060c03230702030a060203150d 86
    0x41d42240340801c00b240c400624255000d4100d04010200c0d00601c5d6600e0800e40030003800742c030200c03490104543c203100801d403920400204a034462505590b42c981003401a0750b507105801d1001c0d06c02010008904070990198480c1001c1610403145143c00103454110003060100078800c41c03059805040c5000d0030412940c0ba910000d940c030000840300020b111608205030342c510300074004030f02d40505c8080008244040c0c006003031b034180d0700e000c0c42c96450743c0d69031032100d50309114405070150025910404103d840b503401d8265844c2000505021650035140800f0600304c580803100d0f4203900d01c12800b802080e06003c60032007003814051004d00481a21500454851001071045004100080132003c0a15114009a80c001c0703600c00c1030150750b541d44074007240c05010041c03010313955814512070004009c1d000c0c05085851310703455144c50480a4180303c0c0d421020203840030b0b00386061420000700c0c00581e000d020000e00144103c0b001a01d0f4181440c80041040e01840c1490149640040c04804955 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 28461021 1250 28459771 28459789
    0xe0105060a3e06010302030c0901030c090b1c0b04060513050606090604110c010507090603061d07030e0102220906050102030d020310030b0711060c0310140d020d030504080f030405 79
    0x88190a614100c07444408540071203128202070392119080903560042d403400101c1c0060481e07008070126141844514100450000c0a200c01400c481c08800708002d07848041e0801c002c1500000d010007000c00c00c032555400304090007041150000110401c000c10800148500f9401c001203c000c10300141c0d0701d82e9071075502d00001d056548205140c80000794956919041110500d4802204646408203407038200d02900d010340d403407000f04112a00118405200e0b00c112411a01c0b000b0203032542130340340c0120454004020341050101900c803100080c01c041e0900003006541d040d8064140c074001401d448510324112508201681c0b41000410007941c0e0f800402d80f440322104440069890711000b8050103810603a600040040000b84204030400340c0200788408031544450a03603010769a100b401c07812a120484d0070f1350406040d494140080780310520140064030700074242038070b8072101d600082d4489001c181c08030000380000078140041c44042c000e444040207210020340c2064107040014080390 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 28462271 1250 28461021 28461047
    0x180106080307021207030602070c03030201111611120708071802040506070312090210030c020f061b0904150f050109080106060c0326070201021803060f010521070803040e0105060a 79
    0x120756102e41388250101030001c04000c40e80032004560741c8071641303007402c5050700a2100ba130140d4a400d1908002418042c104d509125114460710160421075560041810a8401c01e50704a5800001035041038000c00100c001750a50000600b54589440100c0c501810031030b041c08810b6005020811a40e2568001e41c1c0c8416807504028812003000c450744001031910100203584420315241e02003d2a405502010648180c3d900340c1b40382084260382541e40341000c1c4d4401184100c0086002401d0040001905200c0030003040840ca1460b01100706080e180140c111584861610718100070702d68105250f1402030800c1002031046c0d0b481c224010300b0b0312811a5001d410700030700c501c89003811482491021094400c0961011170350a02000085c001d40003500400c1c09900b82c5c00e8000011b10300011741c1481602c0b00380c0c900155070b0070a4148841d4480d06a80d40e07a40300d042d8021040c00617801e00414004c1d03c2e04000658445243c0703108560340d06410b07401980124070070042e40d4a00da510841d400620 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 28463521 1250 28462271 28462279
    0x150d020306160c05030706020307090e06150c0c03151e0c03011a04030b151e06030a09030c0c0e0703060b0901020c01030b13140f0604062102010306051201020318010608030702 77
    0x80144004195103030070718050f0081840c0000240d5404005903030f0b01450046455913100b4044945501d031200c8480c4c000d6901e40d6100c0341c1d4100b01076071000c160303000b442c020b0750b100141c4404482c0d00c2c0c080707844d2900404480c40041410401c202440e55071410516241c00c0e140700340380c154140341c54101024401802480e009401c03101404918403000400c0701c006580c4210f012040740340900407100c00c100f01d0f041c0640310b0b8104110303d0b01c88048404000040c8000101528515140d10b0100001410030b03180860a02072000800c902213002010200020600c00510309000d24290600a00301d4441d17404c00302c000c0350148200b613281d0b6400583c8103000c180030b080010311030a4030301c0020a500f184441d401c0029040c00c1803410342820781040d19000b0681c0910040c1e103911345404001c02d88425014809414154100c00004080b8000c00e4a10f01030060500051094450002c21607040c000f12a2040d50381d0000240850040c59060107042c513008200204440d0341400c0e103180e101c2c86010030203881 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 28464771 1250 28463521 28463551
    0x4180e280618020a140f0901030305030718061418040606050703020c0103020301150509030f010515130902010206040f060f0207030507030f031a240703030605090a18020607060221150d020306 84
    0x41906c48040b43c0306203070001000420a03603564a0001d1203a4011105600015441c02400d07211540e08501141603c200c1d44510415900500b03000d5003d801c101c040060002c1e900720075101c50b8440c5e00c070340b8000d4041e81d0344940e5106032500740645000443d41441d41054410001041400500d850401020312180740050340c035000c0600180c0b0700f045464405e0810b5103410b0510034000510f40400348031080556010b20501c094256070700484041e404040d016070482400240000c00290040b40c034288104000a00001c1c07114103103040342c010310021400b041c40054000127054000f8117071845500549014400c003104003036a41d000c042040501802400f121420b0303000f0300c035004c07001d003506e21445000c25115429414000c014202e54403d6601801c002c01c0450409401360207140fa5006c080d91a03018442072950920000c0e0740300c5042500c244d64240418070358008a03007403541c50b1510000754803005081c0a0710403944170b001c1c01e08036072080e080d410101e40142c80108900c0e600003004500408 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 28466021 1250 28464771 28464809
    0xc0601060c060e0601080d09080105010b030106030e030c030307020102030a1404050c040b04090b100906150c030507031b030306030204050705120606090a0b1c0c0504180e280618020a 80
    0x10240450f8025032405000b140008100040f00080341111031040e0354520034243c3e5500b10300c900300c441c01c1c01a41180c0b8030030001171000c14040d410240706c200442080740d140190411055096070001d0302c100d80141d4000003407141c60030b040e0065409a80a4840b08851402c1507507405607688809583c1c1c901558641ca1008000e54984d4801003216402c980403840c940b03031803101104001040d00642201a19010303020031807465151a04035104455294008208425181a6955003001c0c1c411000c00450101511f10401044004400d840c42500d0104406013588100015514000c1008bc05c00c4800d0210f1100e105a0961090f001002074074210354550781c9c03d003c14583c1d01d4a8100c401200c200084921040f0722031100c0714150a45034004000c3c0d04125001141c10344100d106e03030203020403d10814040f480041d8041c400c80620b00084903200c02c20004000350010403c22440d4140300002402c01c00e102c81409142d442c070804030070300040c2e103400e42d0018209600301c0c022600b841e207130205854 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 28467271 1250 28466021 28466033
    0x906020d06090605030d050304050634030e010c05090f060702180c030a0e01060303080105100306180c0e040501030201090b030c0f16020f01020d0206070e0406090603060615050c0601060c 82
    0x50022503400c2818802107490300403210141c001ca11855002e031180300041010244141c090f40d000c1c030760080c00b40c011a01d542042c034807560000d501d02c1414020380b550384404110301d4015842c803d8216140403d001c0399001a9608541109243e6418008100620a5140d650b0720315031aa070318003140c1c06e54489055001040c00034544000b20403802d0703d06001d00405204210103184900040c0c8410710504089840311401d96106201c0140850325a000511961030841d80f546d070083c24600d00001d24955504407851404005096101070035901e1810b48812580001c00003807880c000e031010710542d4919400244039820302e1103104103499020020401c4004c3c45c1040342d034507514410400742c850349004400304207050b4444c000c0303220b15081031400303000354008100c01c07089411035000381920340d4400030103541201144440590141d910840803c1c03c129501c00d0b003019500807600000c1843c1445440080c101c400c00074002407100c107021608411a0000709181942d256140640403a00d541c500342d = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 28468521 1250 28467271 28467277
    0x6060b070b0117070509010509071101090311150c03060f010c200a12050a02040506010c0c0b180109030f1104230906181c1e02030c1b0310090602 64
    0x518401000080c160184156414000d0685105001550b50a07282d00b82040c0e48220314840d254104a902d0300400070ba25264100c07661101690611100e003400224480e03084482007001200400c105403803030f20061104000004a109100280391214100329031100715a000003400e481c8034014841c1130cd0301da82d10452848841590000b180710034106403225101c41541101e4125008080d00100018a01d551900c040900c40c2c0040160880f01400d4081c00060440246007a041c80346e1101d8502c0006c2e211101c00d4020004c081c0c1c5c050b151440340e050301582d0510100b4040c100f142d01001400412144030310384160039808020351000541c4d480204015001480003c44000b408880190700701c0096000b45206c0c680c01400c0d6411995406228a00e500c03e0b05440b40c0d0903809003148907024200614603030329a9410f030802e00214508803400c0240c01d8100d5160342c005030408621503101d07240c2040402040c006150559042c1070013940420b944250f0b540a401c0b4044d00d52040300c0c14030000b5811 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 28469771 1250 28468521 28468529
    0x80c091008070e041506120201110111040b070b0603060603060f04060b040203070e0a0b0f04120206040306020307090f060806010522050a0f0e0c03040519080d02070c1e0f120606 78
    0x50b124101d075511141d5043d40340454007600c44211803461500945000c0c406c980541da440041c0c030014011303d0b0011518201021034240144d0740e569241c030503000c00e40000c0d100500d0f41c4500c00396558040c1c49c020035500d1003d091240a64040c0080c0074041da0007040d015407004890400d40c0303082daa00d04200c0081d00d1120411500244000180522164401c100b45419141503440004455692008440510502c12408500f40c0c00344410700c2149881048039075950b0004002074181602c90300c441d000c0380d0054814002081ca0420200189105189400000c10507400c2614407494005d0000c0e01c2449844100502c5031206030000f00840818241c0d403019080c090301c03621038207854820601101003580940c01c5c03200344145c00038003101c0910307007220302c1964408003403c030000d040c1495810b4020b00c0e002c00c490106042c040500204118805012a180038815400380355290408031400141e04035144402c5100141051002038480e40340340048030414100c1040001d02824808010b04442e04 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 28471021 1250 28469771 28469773
    0x1090b010e0703090f08070201020d0806010503070f0203040504020301090e0601060509010203160311391503090a060f0b090601020105040201020a0b060a08010504080405012c040908091207030b060a080c091008 92
    0x5c0d100503c00310f0005080c40b00d2007a000c5640c508010142510000e20071502d031800501c04100080b078151040000c5c40712a611030044a0506844000250aa810982129012030754a0482c400303040c0d03081103070300d0042c416800e0040c0741c02e0202000079100c0c803c0b04200496050f0143c00b0508140c03080c141002e41c1e0880310700b51074860684e070251005c401210110402a110101d030703a9260821140030510031581c0c000c2552440b07034000c000c1035035917030002001c9000c1400342d07658103004035110340241003c1440c0420f0004100ba0f1f1b141c20000c000a000d4603447c1160316050401c00140d070000f8101801a412026aa103241d45180000701060070031382003100075509203018002040004009081660000d80301c0b05030744d400c41070100c118100c42d040614500700e0320a140040c41c2c1407641c807102e2481e0103202000c6c50040350780e0100d88041c00d510000724042c0d100304010024804c01c80180d80d04441c048459460b4146425004e580e0744c80356a450034030070606074010443c020498103402d00100040c01c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 28472271 1250 28471021 28471043
    0x10e0d0506041b09150e040c0f0605040303020111040302010c0f0510020a03061403060f07110102070204090b0702010b0109080706030b130903081f06050301060c02040b1306061101090b010e070309 86
    0x700e003450382d8a0300014191503e954580c2c0120300c04825026568580c0e10301115242c0c00c62a180c07141c1c80442001d0001e4a40b20790700040402c680c5141c05082028048540368584c1d602c0c59454001d003100c1544086143c3c800040c082400181e0380080b0000c5982c3d000840d0996111b607500300f0b83e06007070b0018600b00d20a0310001d441340c4c1076500b51f0800b000320342030307e002215407045880916440791403c4440390140e0100c5400502c4140c010031803d5801504000014103001407540401c0c112400c440741a9032000f1031004000348141d090003480501d801c20f10340402820700d41b10b000c40e9030b071401e400395600b03040d110051003d00d42c480c2c00a0a0783c02503104018040064075040c0942800003d0782c500c0403107000c510f07032004242000f148a8007119003a03510a40b85030310307000088680b60007510080307030302588a030b1030740b100b41d40c80030401c1c124101d0000300000c0321442d0402c094580342c1d9078141100f084c3d04041c1950003142c03d5070300300d03811a5940111740f10b42d952400c10840c000c064141c0010f080e04010 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 28473521 1250 28472271 28472273
    0x14071a1b0304140418050c090405070b120a050a0c090b0a020127050f0318151b0105011404090503090103020a140d06060e061e0a0216080a020a05090c030105010e0d050604 75
    0x12800c205a48038080d0f41c00c020340d03103450481140d60178800d01c02034039681c03080305202141d003801680c40e580300d4021415564850344401a001c10350784000083c0c0c0142d41e0003400d22000c06a01d2103840d41205070490100329481c01c1c3c2102600509071485014414040401c05090440c000c2d00721289101c40705056001945e455007443c031b10550090b40c10384640c41003800480a142c0b0020489444404101c0800040e0340c0303000400054070801c41c44002022400d204200e412440800e9401e032550b5441c0000c02c0c0ea605103030740600d180c03545040700ca120342e040c0141c1c840411004411244441c1c028600582d640043d280d080e00c800c00002101c0e140040001a0600d03c411198400001d807041662003280b0704c164442005620700179010010903c0446440f00c07245510f0300070050000324198010781d00c110031000c00d105c120030350b180d0002c1034a4100120060441ca8900482c5019010440e80341d0441c5c240042d807401180014010070741400400403000d54075503942c1860b512a194032038202d074058986 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 28474771 1250 28473521 28473539
    0x10b04020f0d050c07170307030e010504210905010504090c03110a030203090601050409050309130b0402040303020f0601060203250516030303021201051c02090a022514071a1b0304 79
    0x8550100c44081e0301d03010204500381c544da01220901a00162a203030b40b00d000020341002940040e00842c181582c440c03c0700a000c40a008042c80f45000e07000c619000c61402c0b070401c0d039590100101004201e50317603409101a81c0c0010a40d030039981080710000b480031103141c060300245011400d035020281d0110b248520a83c1c036030010f51180c0e80c1d6009a803074a9984000340030a4454a410041858009003c4210541070940c0e581c0c0200c031740f040300410f0f142c10400200d412a03000b034200364010b0b0081240400c10510070000780d80100906c0c4001e41c98952a500c81d241580c10b0103204101c0c02c12a50780640a0141c03c005800e6044000d1800c1101180d0b01d150280081d48400041c9070080f02001c000103a40c5084c1210002d100300d518041d080c040b24540c200071910400034448140246d0070712000c0c500820b0414030308101410160701107401d5040e41841c0441c42c185003110320095000340130501201c081d42740050703c0c032789051020b5a1600078401203120b4011040603860aa4070012400040d0000 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 28476021 1250 28474771 28474777
    0x60a0e04050a140a1713050a0b090a1509120309270506030a031d18040c03050f010507140c011d06150118060c1a010e04060f050402010903060e010b04020f 68
    0x100c510f04030164a0801245691105a0ba10018100d1541c0c0c201c02440454140d000703240c42c030000d100030640c0c00c0d00d403000104205800e41242c1d44286005c1441c0b505400c00300d810b00c01820820301d690300240f00c2403800405842042c0542c440d01285030042d071003098003a801c0800a00030405070b40c5103036010500412141604110102030050815000ca00346d401d010800c4406c96030141e4450a50303509501715006050380d00d44e060754020b61a420000540001c00c0f44c5107000798881d170a10144146581046464190500362141c4283d2410f018440d003140c00680740d0a5441100084d551180d0204082c40d004180b44a102d102074403901c02d4010780e90502240340b03442200c000440201c403000d15801151203040c030014940801003651000e1001c1e0b801050505e0241e44074031010682282d103c211004030350403c0e480488100000c405002c1000f1550003a84550214007404001074546900003d00c15086448054415595100084501360b020f400031829540b02510940d0740d808001030070380480d4 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 28477271 1250 28476021 28476023
    0x1b150203030601091706070807020705030f0a0c0501091212050c030c06060909120301090209030307150203040c0b18010c050f01091112030301080604080d060e0a020702030714010c0605060a0e04050a 87
    0x140300c00c4070221720340c0079954a40e105112030304020400c0780e03150301040d40e40000140018044d403217035400004e125030342000354807405912030020701400c40103403a02e0801c4185070340009050052082c3d050145541d000100c0d00310540010042c40c0144090134191050703c940100445140400142560100030000d6050b001d14000d40352095a07985000300561100301c1071035202100078003000100000d01050b000f501031101300405681c90b0118580d034a11144800c3c40052603195000b01c2040b06100000054400601610f10003034a0520101c0c40200000012901da6060103d917510744418418100180c3e84c001b5600402000210000e00385058840c00c2149100c0c402d04962820010004010043c0c0c0c1c1220702090003000380c2c1c0c90b66680d40043c0c0e00b00321284414940c1c0d5110010341174098415180c0039244801005036170790072a0061608000e1136800c1900303d201307070b131120840c1c50f40c0c04607180400d1b60b0032003800981902e5182c001592601d56500152405008006001c02e0160110b41a00700d5 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 28478521 1250 28477271 28477277
    0x10507060e01020a0e03030f0d050405250806100303080712060b0408070806060d020a1214010c030204140d0203030405060d02070f0803091501030b011502010f0614010e0a0506071b150203030601 85
    0x4201501010f40e40c5c450044c1c07123101c003481484030b0b41c2c05c0340c15504019005032050b0141c1740740c018030303406020005600100c12412000408400c0001150074009680c01c000710300352126109080d602c0181200340081e02080403c001d454a29801c10541d500c030501074518031200340d56a40d038402c0d289a860038139000d80314090140c0c8000c90420f141158070000e549501a0520400b94a0301250103180100c196003502d20115402d082c604500d028414003018844903200140c03110300301351940c18400714401c1a10b0203044055000405607070b0000907681110400c80e152135a410005401c00040c4c00b8444004014100d500b40c068100600d41c4069440740c04003104071400c921805c04507244004082c03102521203402c50005001e00c41b012070040b00340405a00011032003048403081903049460707503803106999691400070480c8070743e17104402c40074080c81101c011020703030b080000059040c486e02034004c10301502030440005211001c03d1260040803210840c0e01c9103022580065102c1d0700032119a800 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 28479771 1250 28478521 28478537
    0x1110a1206050a090e030f0d05010f0504022a030d0f06030b090a03120b0103061d0702010c0e150a03200306040609020a0c110f03030c0304080c01050403050d0c02010507060e01020a 79
    0xa280c548285000c440000b0500c007211071a002040d0300504510103121200d00007006100e0045420000600705420001070004042d0314007031400202c040c00d0b401442c807807401040038014454035000407081028100f0581046e000300c81c0d24031480e61003590340d4165654100364424003a0f40b40c50340010116400ba50400c0d04039650300000d103480e40191a0001d011a14032080e004402c80750350f0000450711418140041d0180d16040c014040070460580412403100354020440c43e44ea0a02414082201500b030101c140c4030f8406c0002d00c54010034022100038000892910340c030300d1080d00444c0701035204205071900080c40c012442c080e0b503c01c0300c400740524200580040c01d44483d00c2192070a941d543d8982d01588110f54030b6001c0803549410150f0301c068400b1002c14150340501c020324004002ea4002d40d91586854001820070f101400f80e00e050003404c2c40100041980460190005011441d026150710190720050b01c09005404025000038030b411000782000310150f00804440055440d0041 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 28481021 1250 28479771 28479797
    0x1306030209030a08030c0d02070f110604080c060706150e100608010b07060e0a0804140a0905010614071410020c1504110f010306080303070206010e010e0c03010308030a0e01110a 78
    0x40e407041032452070b096440400b600020820300c3c0080c5801004080074180b0349100002007030143e0b0061081522344101000420041150f50b0000004070f400640c0d040d42881d2030055000e031210302940a060064500099000c1044031991000e82c100559000901000e6114000d60180041c01c07501d421034401d000002040150240841c241260038034450103282040d140e4440b00030b071840600e114001e110f400350303640000e40b000e80a0005440e4402c4040d203030303034043d80c1040a40c0c02c1c1940b0110703481d483c0c10010700003a54492103003003813580684529a503840140c50004213000c2e074801030105078003072500280d0800150390012300035004d894045617070030320500b014800852410303103006003d84820812080f85041261051584140504000400f40e5450103800d05548c41122040c0058008500500c18402200d4a890140003100c2012406241490082c07005100c10701010b844040301200151101c0242d030000c0d0020080c800c024050300f143c94044011316008080b5480c0480c01551142e1 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 28482271 1250 28481021 28481027
    0x1b0806010b0a03020702060d09030e130b0307030b04080d05010303080a1d06040303150b0f0306100801120f020f13050108071a0d0902010e0a031401061508150f03121306 74
    0xa4181d4050030700c1d151038103081d450140d00941c441c901c1240c0103941408902090f1643d40f088603a490b000340c0b14500041000d40400c81130f003500d2461440c01a2420030820500e880c000307050810f032540482e480ca066103c0d4140b0701e80030301440318505195424100040101a0b03ca500c5901511b030f50038041c02141d64a0b44001c2c08000328182d000103a611150015000c43d21032b030441c8440c0c03c100c507000700c0215121080c3d4400c07644020813038201c601c40001071268504005001c0016048035142c00325941d4146884841c1400341101d014001d8101e0260707450540d59a9010480ea140d4028102601c041900000401900092103110a140581540087c1c1c1c5e03040321f0008502012034409444ca0b0100b00300d00003004041128059042001a694855640d01c8400c4103801540c000d199600c1c10111020005007500e58070f401580030785c601c0b200210206d580110000d50000406c61400c85806924004a002c070419030098a0341846400c2d224840b0004400040041041e1103110300c2c80c4a8603040d0079 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 28483521 1250 28482271 28482283
    0x20d0c0b0a1103040c0510050313112103130504050f0a022a01051006020c03030708030406110f0c010606030c05040e04020103110d06030b010b0408150705070c0603051f030c050f1203071b08 83
    0x15000c542c0e918080009042a40d2f96181901d00030101104490130352041c1a4a03143c1010a4100d9800002e140450b1030aa08240000308001c9a0510551804020300420703a40042e0030800040e80209031807000000d00e00705000c4200000aa403078152440c65040d074044c050595a2096078114100702090003440402c1c4000802d0b005001140380000756a81e9958540c8003c1003a541c40c0c2e902c81d03000581c148098000c003d001c000e03d20103619040c0f030400c0182102c0b1140c1c0903005061601c510325000c117800400f40c03000c0b40c04a5001080f595510300040c2d01030060307000910041c0304000303014442900c00380c0c40703070003a40c0c06280c0212a0740c0e210040e01000340b26500402c03003264030076890003a54a900300c82d00c3d0342c03081c200e140840c10110155640c640700c0300250441004252500308104403000a05040c030540e41981e02960f04942c40c40e1220110a5628050391740611241e0414206685402e020041840c1d8a0300890b81d69001a040c51810081290001400020364030000500640d000902c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 28484771 1250 28483521 28483531
    0x5090f0601030e120306010e03010e01050702031207020705030703060c12050406020301090b09190203130f080301031502070f0b0c070b1906080d020606040c0c02100306080706020d0c0b0a1103040c05100503 90
    0x13050340307035032110001950088051941181d056403900080d2102d0f0100380529030007507020b45c0045840d0b4560120060046030300900002c1103500c0040c0802556400050220031260010000100c10200e6442219072130354180121404908002c14002001080c0d8001e504136500c0700010018065040c0070082654025a500f5070f580702c3d009074082c48042c045d0700450308070307184400c1d040440301982e03070342c0e42215840d90041d90816408401002408122003240d00440c2e81d0040840c43e026065440c0c502c44a1000405020ba14405c00022a000d107810120f030512600a41e5140b594540500b0841240e40103101055000b400c000000420141c00034800e000c42180d40c002c3c014075a142c60500c0000c0460f40c41d06401c100b00e0b000c102c2e01585484003c103ca2203c281d5003c0b4141c0c0c18045824500201c5901800c119485281c10602107980000c03080c01c4654480d8800340e29894005aa6010700304c01c0d94103c6444000005000402003503450000c1200c1702030b61114441c0c010f0000075544d0380400ca41c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 28486021 1250 28484771 28484803
    0x6090807060c020405060d150b090a140406050403051c0b030c04060e0406050405010207060f05041b0605070b0a061a070b010f030b01050603040201020f0106090905070b040308120a020405090f0601030e 88
    0x7001000614117500019844203001d000604d10840380d8a54801c5031806a03064800b556079008140d031641843c0c1070151b80111092014484d410780444802c075480001070000e40250b507650081400c251040d411100c64000c010ba064038844003100c1c20348020040480010f22078401c1c80400c0190703003068000c0004484211558040b80e0380c2e03e459030b00c0031300002030080310310755401c02040c03000502610440102d10818980015146028503142d03e07040e940c07110701030035203170500380800c41e26511104581015034002541c88540c1c4400c2c598102815050300510025548508464611502d441c0642402c43c09030380c1d10407603640e83d0504c901d00d8101601025158110b824010b120034180140155013092042c0f040f80c60022044a55500311205500844019502c5600e007000384040ac02c0418040c1c00f045a040346401e10b0365071807020a108514404141c0070005000034600c0030700d941a14000c003070240c1051118500901c00c0c940380481280c480340401c2c90035800e0284540c002501c203011800f022 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 28487271 1250 28486021 28486037
    0x20a02011202040b0310030b060409050c04091704030311120306011d1809010507030c050c030d15030b0a0c082202041508010e010b01170f06010c08070501020a090609080706 76
    0x6001110780324008800c64410399000c00c400629401080001e41c402c0c8a00c40344070003c5030847c40c00c98580e4901030411841581000032080102d900070402c0d160310001201c0019000d01146040c85654943d40d41d106105c420200340082895080f4101941030351900381581c4803500200c10640b1140000e40b50b060002c2c4c140c0c3c1d82c00c528120700701d0400c902940000c20844009000b03440700c0440c07003401c03500f40d911a51980207000303201c0d4241c012404800880d0904034105402c0c2404590703240154444c40c42203e4960381c0c1c54103021041040031024513042001a981494901048005802c40421200018032094001864920141c0c41000020a0508a61200380e442d40030080507256100c0f0b61340f030612561000140c141004d200c1c2e144802d203c1000815050f59400001d00044881e00318001810104810840d045038846101c0381e00c88024200100c0c00d9034281403e003010300402e03e008240d588002030750900c954020500300304a6800d40e07118075100b81c880741c030701c1c0d1994114801d075004030f0000 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 28488521 1250 28487271 28487273
    0xa0b03010b03040c0b0a090f0801060b09090615030403050a0f0c0201051e0d0903120f05060a1203020118051f0c0e04020d0e0307081209010207150b0307030c0b0d1b020a 74
    0x1540040d0b40142c010342050400070b17201e5085044582c031041d402e4000c621884c0e800c201034410f03004c490004000b03080c02040024a48a41d0001922800da9054494035200780043c025a403181c201c0200d05802032071107a241e242501d005440d6500c01c221000c04560032a254941041c4507120940b038450b41a5a8039082440c106241c83c0d4141000920050f2800140540240c40d0410b10400020500a0f900c0c040342c0011050345008903403801e40060b0105080504004242e21445039980c00c407507001640704ea249070355040490050017170710881600c100307203440d0071028400001031401c00c10302e040e03071901e12240100d180c0e80110341454061401242e1203000c404150724140d8003500c08420f0054011510001e450b40d520b00303603800010200c0e0813000c007061040c17003d03e40054803070340203103d40c1c0214542019038403119004202c44407040241901c0e540c140920780c405000c220000c603885000501d9554a039954100c4941081c10308418031448c1c40701040e0040c07100c6003102c070b83d20820340107482d2040c15 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 28489771 1250 28488521 28488539
    0xe01030504030c02032505030105040807031202210105030105060102010509060a090309030c060203120a021e07020f0d060219180314070308190f02010504150b0319080d0b0a0b0301 79
    0x4010320550034803031a003241d000580c17002e01112810001c0301c0c0311b19070240d03a5500d0f80e018040c0607400140c0260315250400000482c02c00490300302541600300000c420000b226110060700c00e681d04007400e2410707080e810b10116200c0030914180c81e000c03002070240d44e85c0e04004a08a90046a50200707640c0b00001240f484c0300381c0e2340900400f501034070700002440d84a80b40d801002d4000d80c060300043c0d0000400810b9030308011034494002e44a12019483d100111980a400c404815060704030140c0000c0c111045540d80642458620f40c050502c417540d40160078400300079000020514170300b0702c2a0f0189401d05118641004244a1004449030500e0640c1c85010031043c01040c044118490100080042004a0064a4400303007010350b030300c1d502100704002072074130310040041425a8100010301000640d0101080b00c04002031200107003981a080c0060310b0100345440c00d42c0030724052404a07050000351001440c50143c007082c10300c1001400400e014081540b8440d1a6844401b80018041c9c951 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 28491021 1250 28489771 28489781
    0x1401050f060609010c061b0305010b030403020304060807030f09060603020103060b0408030f070503070b090c0a090c050a030b0a0b0a180806061003020702040207020a06050a02060108030306010504141201050f100e0103030e0103 99
    0x2c180741404005ca40390380c43e00212802061582e18400e0300f04041980b540c1d06015580c090031028009500307600342513802950364010b600400061016040000340407502c81d5000302c143d546801800d01c00c008160030904002d02040c042a03002a04040f008115465000101c41c100c1d0780c8000107618207031049402c0c1c4503e40004c00221400d02040042c0000301d4090304446024200840c058089000031004004980e0f80580c000e8030394a08242000d107030342e6017004c2500c000080c00d04010504000701d0b800500c05401744d0b006000761000205804070320650105117403d1101101d5a035032110303500d07a41d005544031001c40d00d099000c1c1c2444540c20510388281c018040c0580b01a20150402030b0540c0002d0161105400c0203000500c046070b216030103070b03041000f107005181c401c0245281d410080c0000300144198000c0406e0040c401011000c20b48400217000c0030203002130020400f03030401103101d014001080d82d00005140c1c00e0b900100340031854100300d504881c0d140e00c6e0b080c0c940c0342100c0150003a00c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 28492271 1250 28491021 28491037
    0x307020906040b12031c05060f010315080105010b040501090b07020d0f0606051807080f0609130305040306060b030103050f01381503070201060e01050319050f07121401050f0606 78
    0x1038a41c0c20401858449100760030a01e0100310245444440821b84500409603805100b010f0900300b4041c06016100c03e0059110340001780790120f00c0340303212103144e14075070026441407031558a40000000d04180c2e04019005480d403d90341d42c00c04942d03a1452044c107008814000c1d40c03054114003c0c0c07000034080347c0150800f40c031401000c980181c0c0c4500181d580d0840c00303584a034440032442006001d03544640c0041d84400030350055599400e00d400400c2c0c03081d00040c16240e08140082c445006d2600500a0302d00640c0c1c0f00303e081c000203032075111410040d0400e02c011200c0d80301e600d0801007080e006000d44440c0c517a1007040c6000c019007125061014210451100d000c040329114003000f603841e200c50000340d20041d00304440d80e9040987d0000e0844040d45d000f009030f60005001403046030b5000c54242c0d15685281400000300c206400e2103404c10180d645c107500c2d0740c45100d00c000b40d1011f40585022005010304241c91445040b250300c0c50a98904581ca850500c2304000069038501c7c045d0090407080c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 28493521 1250 28492271 28492279
    0x12105090f0111030402010801350109020910031406070e010807030209060c0a021c03020304030b0702030c0f0d140301060c06110d0213030506010f0602030f0309120a1e030e0307020906 81
    0xa00025a07480d00710b81c281d618140e143c40f0008104429940c22903001401041201d282c00f242c2c0040503010780115a83c2c508010880100300b441c02d9030100e094111801254000704403030340303e0610000c0345244034041e1000700c805030329480900b030004002083d21032184409403500709040100e500112050300000f031021080c15801d001c03540d20340c0c8030000640142c0d10304100402c070710840c2e8010000403c24400880013070340c9440c024071340020f42c040240e030203c981c82249103880e40c50780c820aa00314054080000407511402054040140c800600320300e0079096038540e200405203075941c450203031000340140000b084d42d1800000001d031055212034040300c0c185c0940c90a140644110500366400fa40d00044020003046050040c001c00380110790042900b04c0c2407003480c0d440c1a001030b4072030049400388091110003000040d803000c0180969000c2440e400102075580802c1c0c500501410035a40b1a0020003241030266282d16010388038410440080301d0003181448000d0b42084078280c4000e10803504 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 28494771 1250 28493521 28493533
    0x6050c040e0406050703050c0f090d0f0506090615040203060117040201030e010507050403021c1101050d09050303010308070605060102070b0d0906020f0304031e020c15031302031b010e01210509 85
    0x120041e025100303030080d0321038030000c1414144841c0045c203a50000c0c1045e88050000c1000d01c0b09145040101e80c140b000c2550206981c4041e4203083c100201c0c0c2090103042c9009160800946200108540b0b106003028000b20040c0086031051004a0104445e441c0c00f1800100307158051034007a040b0550710620501d40400d150510746159803c0d20b50a0700c10b44049580424140700b1450010540c15140e405080c1c6104c5000142d101c060401c04165800c070b0600100103203488041c5100d4218032500790300801200d0f030700e582d24940f03d84550f100400980d0103915120110f44650b10208420741140d034412a0b803030500c180e0040b808010089458112801d507402c04c459214075003200003451142c0d01a80300e00b09101300d040b4484041300c420000c88401c5410603480401c16a0744c190341d00aa6032400c510f901c7e1240e0320340902c0c840e20054403001070350621986054034007c1c00e6a10b003071001c010080c0e8403210544540001901c0300072200304460210042d0944408010307a00d0392180340e0103100f4000f1948 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 28496021 1250 28494771 28494779
    0x50306120a050c030f1203010b0901020f01020c0c0901090209030604020906030106030b0f0f01060504080a030f0c050102121005031b0402070c0b0c030d060b0703050a0305040303020d0e0303010305101806050c04 92
    0x21030161101c0044036180c0058040b0710842c50b003171042c200e055007100d0103000703400a980c110100c2d40c401405010f0650b500403c101900c6d0340308210690f01030086034001c5640301185d07130441d580d4021308604180306481d144008110b00c0c0a41c001d803012040c010780141150b469607802c2108015000701699059940e4500c00000300c2c0305100414014500d49400d0502410860800c8800c0201600700b0002d01c00100002c000d40d00d0000b8500c4140354051400201804131004111111605d440c4080c20307941c0007042c1c01108940c2242c00b240120440d020f1003503002d81d20f2040c543c0315044c641202501040c4200b80f100a070600707400400580d03200303e54082c2c185441e540d085910b90042009040c055001080300700c0302131440d114003006481c00005c180d080103025500180a84601c2000008050720703100881d007014001d4066030b100c03032007009051001e00c07190790f40956250003d110039a02c1d8800c2c5036444e0301c44e038801c0c07103030703c0102d084441104101d107002d44a00000d000050681c4c1c02d01c1000b040002 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 28497271 1250 28496021 28496023
    0x50d060303050415020708150603010f0f0506030f16030605090a020303041211090103020603010303050715180302060c030403050405060a050d0504080d0b0a080d030b271f03050d05030612 82
    0x100614426110162500d0a005044941d407890112030313010355100000500030302e64005600121845c03010006100c40d500c010210f4090048441d000031190700b04001035404403002c0e04000c0c0700b5074041e0304452204000d40d064942c3d402c50000ba02c02c0a8042d204180081852508042c1d40080702030101d982e405040e50100385150f201e03a1241c600440002c0001d0100400107400c5246a40121441c04d50b550560300042c14900c018400142800303000980b107001c0000c4c044082c105450300c13003002c100174000c2c059106018141a00304800601503880052010b0140405a070f020b580c16079a6941840e0800d0300303100302a4044404a070500205000c414103c03007140c000c0c40d11603445490709980b541050000b043c207464001d030055106199447d01844001d03000607091600d0581c40c64046600b03036030000400c0d40300b040501c2d54440b5075480c08030305d4450900810694018483c4032040036600d40300148074000302040e07010041507600300c0d84c0d616000c02d1040000c2c0da0410002014290303010380c5802c0103 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 28498521 1250 28497271 28497281
    0x1a060706090209040503070c08010203190b01030b031506010f020105010e0109150e01090207060e0a0308070f1709070e070804110d030905060d0903090503010209090103061503020603010603050f071103030f0403050d 94
    0x105c03255840010541c7c2009460781302d0313a00030310001e0000d50039070800030010320314001401c5c40c0700002e0303a441d040c410701070f03103e500810303400032000d410785912aa1038554581807448c21180c007400300d26140c0030003d1003441407146034129900c410310400b00b0303420400503202401140c0c15100094061010100e494115040c4090080071407000050341d8002c0e030316003941960a0f6040b002e020341c000d008840c0100b078005c800300b5441001703450804141e4200d41c5040c0d441c0d200d074006419207100e0210400c6101240010310f542901d800b42000145070b03407042d008860031a41107400424815001042402e0390030a0480c591449100b4103008908641b1f410114001d5084107107080821602e441e404020b26400001c05405410143c00944ca4503c07c0008600c84d640184030040415039070703044c82d05190007004106809168020941c99407541d480380000c028007c2628001c0540c83d12002080c40305001d04543ca01005209000d50309540c1c0c1c030580307107100000050003130b0140328082010a8141e2200e21070 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 28499771 1250 28498521 28498523
    0xc0a0b0a1b0504060318030e04051801090609021e0a031205090409030c0b0a0b0114090301020906030702060f0f0708040308060a05040c031e0501030f17090607060605030f011a06070609020904 84
    0x9403c0d180e501c0c1100c02400c2d140c15100d240040701145c1c030a000403070380c000d403800c1c0c00c1c04040d607000c2030310344818100e04230306240c80307a521301654604a42542089490f4200001041c0200d8107050040006170603025031074011000e103030348040340c0c180810004035011400e90014000781031403070401058402080c2960400070741140000c1c01d64481104100c43c40301c5079078100390156010040100c81900107006048108600c18800701c0101e9410f00d650382c250110703005400c0240c005038482c03c010a000c0e40c4d0341c006480d01c4403021860b20000d514100e00c00925446080c1e6503859190507200c9403000c0c0d0311031102806a9810400940300490070f9255170044410500d0a584c0016000c100d60408131b8000503480c013000071842c01c0400405c08034446035100240190002400d064002030038421004501c0360b090f50b41d4210102003400c405200d46503210904803602038066403017004070240c4090072a0316100c40320b9001c40382c0c441124407a061060203400001c2c4200c40000e0012900c0e000150b05000c2150 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 28501021 1250 28499771 28499777
    0x81201060809010524120c040903200309060909040203010e06010806100803030907050f01021f0614030607090618260c010c0302060103060b0109031a01030b06060c0a0b0a1b 76
    0x1082c4281d4010900c51550f1203000e002c00c1305079401d45550103040780140507100038031412440c41801070428007030010410868008004111054081c034000c4c02540c80300c0c0700c418040d103140d541e0b00300181010049408622008020a18001d041030400a005030040c0042e038243d0b59449100242280400072940078017500d4005000c5881d010050172458801074100740015002030041c480d600100080c00010f46004454030251060141c4c0105c0c40c0a08155820b8491040360a40c0c1403001d1065000005881000c08000180b1101209150341c54030f054030000005040100c0802109100e20b40c102c49007031404849110060791403000f09440a05070950fa80c6c00040545c48000f003002c02c11010100260a080041c0340990548029445800501c4080e00b100d40b50b440c0400d1680c40303095002c0145502400301400c0300a46022160070140034002280c6d0070308148041003461800703034142c0b0000031b042d4009010403035a59840741603030750019148046840e00d80b00c480f45080e40b5140c0c032040c01c180981e = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 28502271 1250 28501021 28501037
    0xe040f080a020615041109040905030909180c0a050607060902030c12010f05090c09011509150203120c040b07030c062a02070501030501030b0601052b021c0212070c08120106 76
    0x20240e10f1a04440c0b6135118400c07494003c00f1020001890241c0d04c1c841411103002844501e14100b55045218400d0720b030790b000030f5020410142000403107107107101c94001000c40303080c0f2810b06d0500c20503c1140c0039246e4021018408200060790540000e54100d1014003619a819100d1000c600000c000300c101c04090f9455401c00910300ca5144540e40c0d00c5038407400200b0104881e0310100300c892070103002c0c490740d840300384402088590103203c000300107084052465007071046c050740003074032038202c40a031041d11810754012416075240d6509481c251010460040d1030a106a907080d1000707561608125a07542c0c0b254048114140030f680001c01070300c040704602500c2c440d0f20344006d00f03194485c0c00c020b0603d0f150200510114070908540d03580408282001075950300e1821840e15140505454160016410140b9000e00c100603001350810810034281c0416094038141d211040e07000d05580642c2c200101400134012030301c0380d14009503490143d04018503010b0300185d03103507442ca0300b40c004d400400c0c148 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 28503521 1250 28502271 28502281
    0x13020405090c0108040803131a0f060d080406030b130f02040609090903050307030b180414100905030909040c030b010e0105012606010806010306080105190e030301060503010e040f080a0206 83
    0x103000342644040120003a11a002034800040c0c442200540040e12441010002480001e82403035010034a98000703d1400101c400505840e0401c1000c44041345640038003030104006082011540d00000d5000b03010310704260034854103c00800303108080543c4040c1190051080612070b2042c001142c020b40070141c0d0303490418070302406c0303146658401c800ea1407030210740030003007540481070f65008102c915020034002101c50002d048042c555110004246c2204144010442d074805203507807440200068407030740003203d803004e01282c00d0010302501a41080000385039503d032503280759130312612130070034185480e8030303500c0341c9170175001c00d0300511000d940d01c0006201d25070700120550002c0103c084603061000c00d41052001c000c4000d042c3c14144003103100403914680c001e80210010b042e03a900200103a04d4070b0710b522410800700304820440145040148011042d010048a0680b96540c030740c41d00d164a092071080240c0700081c400d54403046120380d07000005000e0381c0181841c00e5a80d009000d0360800f = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 28504771 1250 28503521 28503529
    0x20a032702010305060603011208070201030b030609010c02070b090901140103020403080403060204030201140910030902030c0303070501230f070e011202030f18030301050a090203040203100903080708090102120610090306051302 100
    0x24000d17502c180d200780010801c003c042008002e00c1039014104980f0b0340441e2006070f0151801001441e49030180100f0460102015032041e40800340e50781c201e07070b045590b510510389140300303850141d500300b03500c0c030010b03c1840c1c5c5083c615600420103260051074140e8948070700045030816003003144c149400180c2001503680c03040000e1101485c000c1c0761460044c51400141003610440c0c000800c2c142c542101c582955001c0c05101003511000e01601d54070744803494032500a000c0c3c030102c6c844005c01d03400191442d5a0a42c140340c41580306a105072081d4646400c25a10600440d403a507040085210325200c4095407400554080d0590703800598081c10010110007998002d030140c503449a005100401c003d0ba25101c0399022128010b50046c0d8a40700c50012a02b0318200c524080b145a05142c1c8041c100340d8071080d0300d4400c13182d41c0e03180400f68403424001400d07803243d111916005429a0b01084a51901e4148000301c4025420486801030341e9a07a013800382c400482d4080b40d0400040c07411015410 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 28506021 1250 28504771 28504781
    0xd080a030e011503020d0f0b0c1b010e030405010c0c0816060305060111030910030f061202010807031406220501060915050301031e14010f0504150e0a06020a0327020103 74
    0x4075010081c81034000300103c0301010005440041c1c4a12a194281c81c140f200d08041c0400607500600740b829546010503801040360310030110522607070521003000c40b01903818410b804070107503e40040c0d07150603c5d10004640140074880b0130358110140c031100040503201040024403244840c03280c0030f00145400c101030105c0d8402041c0c0790501c603804e0019484160040112022107408896000054046010840007405182c0440451a02d89000480c02505d40422200320f05d1007640c4400c8540e0750303420210140c840110891508109500101e551450100c0342d0400c0030300c07000d00018661181203600c00681d1130a90120005c00d2400342d090294070040254000745110070f0800c1c500d59403550343d039009102e1103105010348010390004150100850040c3e22211841c00f20001d015071000004401c00070081520110346c2d000c0440d05508040f11140078166207504080c016054022030750319546c001c0d5100303000d0031f01015030b1010350301d02e02403040030f034900e10004a01da1a0000215440050300b00c1d4 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 28507271 1250 28506021 28506041
    0x30c08090307030807110c120303012603030106081b0703030b0306010b0a08010504050c0403210e04060e07110c030a030e09070306050a0b0c0a02090c0c0601090c050f03090a020d080a03 81
    0x14000b00028004a50000344054110350940f030189440b4801d044901e0809968a542548c070201c80358040c180000004003a50603249408482c0301c1d00c094401001a40388608809401e00b50014001001141e0043c203060b58407580f040e4100d5000b07144480c5010550380500e0b01200400d96400040480c2d050800999015006031002d061402c92249400760000d101441001c0c4030301d459500180e02a4024015580115030125030082020142c18911958400031000c100000b1510890740d0720740d1030a8042da1040b203460b000e00c03100507102d0000031141c7c1c0302900d5540717500d1700c101c00d0690016181004410200741c065654014005c3c1100c080044990025106400301810f01001b40000e0b9960034031a4202d54082c1c042a5581c3d20f030380b41d42030920310300d0003010707500103c22410440040084002009005486001d884860703032595200000c68140044240000b5400d000c10080030340c03268010354100010b4011a004140310381e00044240031030342d0046400340c00200360303072040300d8140c06208a81 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 28508521 1250 28507271 28507273
    0x4110d050a0b1819020a030203070305031b01060e07030f060506030a090201031103090c010807140a0c0203010b010305010b1c0b10050910110a0201050706020c011508070803030408070b04050f030a030c0809 90
    0x11090f00f05558074510701c0000070340c1300c8100031054115074a540c40031004641c0a03081d2060036580341410b9840b034001455000a91602582c0ca6a000e0313010310031041590300202400b8281d032503442044005181d20f800200890341e80394bd0100311741c0e50300c034042c40c41140c9c410400b050241641c8001025240c01c481c1c003029851050060040600b00803404000c109800c0c6803803401a5207408003100e2441d02480d901c0400100020070341c000903841340b65104050b000340e0090003000040001101103410034424080c0402c0c05204000303004049080c3c1c0900c122041c2404100d03942e040000415100013038021034041800055205a1400e02c07100605a4941a00382142c40ba46441c03141510380f02441c800a04010000031040100b003002e5040d10206240344008200400000c51030610700c042074041c0d40250311403400e000031014400011244520750180e843c0f800d007881552007001018010b00202c1d0340f4011440090403d180410190180c2c0400c0d960100e09600f03821301c05058158003030041c0c00d032 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 28509771 1250 28508521 28508551
    0xf030b0306010303051e041401170f0105040c0e060d060302121b040c0c061505011107081209030a02131a06161506050a060309061404050a03030504110d050a0b 70
    0x9030359010540a04403601801c18564a1303046440803000d10011240f0100c10040100740820707010b0002d5241120004207803103081002c1000304000411141c116210700d40d840400c1c00622140c10280c1151400707110908200000c13001000014030243c112840318072509070382750380070000e40c900000c100c6220210318000c1d02c0044591010390744002040159507009603102c0303030b079002c910384220040d645054001208001c264041a15586444001d21a413400100015030044610802003411030450b0003c4000f00728854101081c00b010b07030041200c4c1d550500070411054050b807140480c0403894005403100180c001c281d2105211075510209c031048c0108414000310b5001000410040d0f22190003011904904027140300000c0600005c0e00b10640010700713210009400e5401d170b00f05c1c0020502c5036005101d031841c044103001c10590200c0e00945075601000310719010074001d038441d41c0c0190084801000102109021410020402500315140c1d40803642001c18800348075070184e0030091000d80408 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 28511021 1250 28509771 28509791
    0x31603170c120103060b0114190305180c01110703060e0303040312020403080409180c060e0307080a02010c150f050103080702100804081b0f0f0319080408030103060c030902130204060f03 82
    0x4582c06050000074803607035480c220101070340c2c001c3d0313440c1d82c10710000f13191640d95a8000b881400c94010300070180010a0804011485180c8401d0b43e01041c50240001818980600c0c00119031801c400303001c240071409600004008181280650020f03440c6490003199a41801d180060000c100708081c907000c01e01c14402800064290f001301c4040710811078003c200ca1645500340582a02028001800300c1d40e10000003680341d800020180d40d031074003281507030100d56444442c42d07200d408400d8024001032050701c030040001c4460061207a01c0ca1680d4000070920f0b920710081d42210f4003a007060f01c1007007000c25441e085140c0b02c0c2001142c5c251510b4000010305090743c40b84024019030f80360252280290990a00c0900c040107a405001d8400040720707800900ba9503110b840390700c83c031171055001e50700c000c0c2102058010984d490003183d02c4070f406403441e860354603403000401003020020105601c0e0030040780035a86507200b038100218103d0f0016035032480d0000c040d00c00b41141141009050816005603 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 28512271 1250 28511021 28511047
    0x3110607020705010e1c03030606030f05090309060304050a0f1110030b0a091a06070605010806010506120406020706140a0509060105010e031002070201051e04090b090f040f05031603170c 82
    0x2c403c41d10f0030b00300444a0440d90000600600807400d0341c0d00e50004842440c0d0034554981c100300c0480717003161003c00110454412520a55070304a0300072140380c0c0100f09a2806050400003035a12038050404c0d41c10900155450b02548024104281d400880c034400e45101d52400c2c07001103404074018282048a07448040110340000f51074410030503000d50b200d1300c0001c5ca00c0892411150500014940c1d959030080340362100042ca42802030031260721804001007564109041100c02100410303400003429a03450b950040a5401030004a41c12902d40003d4514662001400c6001b01c0b030881010510340f504000c03641ca070842c16807100f4108600c240900710252004034483c903080c4000e40d00940d80e51907030300040e1410702c02d002032080c184a420310b2081d0400d1960300904140e071201034050043c00300c1c01c01004802002512a40398040441d404100082c9200c00c5008000780328100b40c17400c00c800c04407a400325209035a03080e00404d2600c1040b4205001e400e40d4075902c105088440c90034501120140 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 28513521 1250 28512271 28512283
    0x616090e06010804140106080f0d0e0d0807020a0f08030a0f02060705041a0c030304150606020a0c090e0a080a020703050c0a06020307080a05070c0306140f0c1804020c0d0306030311060702 82
    0x402d06225843c1c002c541840600c0c0c3d69500e1101c040d0000b413100716524410103070394084070050401c0300d004158589a940b0700c207003c6c0110000c0d00030a00e1403000c229807541c41c071543c000082240d10102c80d200003d54203420600800050001801440c1c903100c120780d001d00800725048094046402800c100411981c0010917101901c400c0c81c88003540107a0b05c9801c0400344540c0341310011b82c0c4804410001044070a950385e204800c00410144002030b034445003a0799071149004000e0400784090020b01c5406040e61015803040032400845200e6611070311406e00c550301c01010800107820080045c401e11600700242c400048064a580c0d919070310b80203000f5182d014050000b0100140084d800501070300c54800e42e114542c1005250101d0f603a80e00e05103004020a00410b915a5102070001d160948d40b5951144202a141c095a2070850345442e90048001c810112551141d800e100030042c40d035040043d82c0b518082610000f03052800c1d410301400001c1c284c00e04803001da100301d080203089a408546 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 28514771 1250 28513521 28513531
    0xc09010603020a03020d0905060108161809020613090b0406050319021c140303011404050601020c0603060a0b03040c09050105030a0503070b0c070602031e06010309020901030b0a0605030f0616090e 86
    0x1030f1158160102200640725090380000a9400c00d0f02c500b0500ca0089001c1d812905240f040b80d602d11031015010440320105e11a05410041c015410312110400e40c000c88466031004241034900611215414140b24050b0001103819540c0d1864042c0c50409102c0d59014040c110000c180c05403150107000c018981181c03000380290150440101d0140000105850300743d406401d000400100c2c5020581c2c0750001d1280105e213558005a07511103040c184203240c082d000603030142c0302040049040c0100c81e8005010b0035003001c182e07440060000b0142015601861017109001802031501041406407041a000035100c2d0f0028105040010400411546110b5210342020026178402c1800d00c076500480d24040c0c6a01c0c000410010801040c0c0e418410302c048415848074240ca40c80011002c4920f0b07080003d41081400f40140302044804008e00d601c41c2c01b410021591a80b18070200f410704208040c00d112560050003800b501100f1200180705266151601140c4e45140c1518405040c0b0040c203 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 28516021 1250 28514771 28514777
    0x20a030204020708072310050f06090709150207150509090a0509030922050906010b0711030304032a09020f0403120e0a0609050916021c03060812030402040e0c090106 73
    0x20f141040004c1c0303109403400c80c1d403c0b16401450861101c4404400f1003400c11565460058400b400c2d812141d038401c1c94000c0b03680c009000d026585400034413600200250602d070134000050301c00900c054600c211403040f0740155000e03040e44e0b868000c0300003043c0380020f80380d42406001e000d8503c090300c80c0a01035502200c46c0b9070114482d00d480915904610444141c0343c0c206520011141c40c0600b1180d44226407038241000b080305035126400c042c4c5501c0e0a009418034203030100404008210708003c00d40342000000c0659107440c1d540e55500c00c860101c00711000c080b241c00c6135511482814120040001c1c50034920641c6000111a01c1e5442c603c81c80c00014a00c00c0f2100c00c00103020320400400030f031a44054528190f081d00c5031809095811540b0446210700a51000591400c8030020311003105c0f091900200b03000ca603100200c43c9203000070340b0719204140e42c9440c0000e01903000c00030b0040050380601110303920300b403070700601c410303500d41446d400507581c003968200d00b00c0c3e00c0f5400d403681100e00c107207 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 28517271 1250 28516021 28516027
    0xc07030c080406050c062a0c010618060f0f0503030a0f02010b0a090b10050903060a1107060504200607020f011803061506030e0607020d08072001050402040b04020403020a03020402 79
    0x85015995040e0400c409000260086004240c140d0060014400ca0207080d048480384e50360310340500c0900008030702185590700c2825800801070101005820041c4500001149403030b1180c103458980000342005490142c0c032801708026007080d404c4070310007402034114140e585e60b0512011958900c81c0c440c0071000c005801240303902c458400c0d40a2981000d008000c511020b541f41d514030098001c0c020399920660b89030070400c0c4500d014800310350f4420f6001d07010b0081a59901c107034070020400c0c0302007200500404c008440000b042da20400e0710a074462050560b0195410716682412444044c5543c0120701c204040e201517900d010850030020802d1a01003680014141c01049080700e980c8014982414000c01510302800e43c06464250303011a601000f00c0380c0038a0034940e89807425140080940c008403a42034195106840d2150300c0041d03418081130f01d410103080000d40e03d44680710301095035507500901007186040c4c054803508850865096003030a003941c0014555110510000340700700e03400 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 28518521 1250 28517271 28517273
    0x30e0607060612050a0201030507020d120207140d0801060801050d020117090c040e0f0c09010f0e060102150f06010f2316020d0503030403110a0c140109080601080706020616080c07 79
    0xa80c101034007a0080448072407642e00c2c0c520b80a41e41784910720080b80130034200300010302c000b032000a8982c0103019941c0d848e154800790010380c20095010b07140c10b80b03800310254459900180300300703c1210782c0341142d510f0613500d6140ca50020804101070304807030f05c5080c0c03090a840160ba070085034501446003a44103c41035403112103407145441800680c0342c0e00242000b148034140302c0e0208034010b184412000f694900348021003005002d140c2401000c50004c00307090140450034103102c4090f80a041030040f18804410480c0c81c03c0003080071940d440b8113801c00304c00c1104550707001003821102c0360b95040100c103106964500307418220110040a1401901240c56480202d03900c0c04e00603c030f600a000c182c0e200425040c0203880764400c403415404503240c800304039a44900090840010354110310020081c0e82004600041c1e2a2100006410005c0400e0082445501889414000c1c80e02c10001c05589180c0710000c5d083c0b0740f001b480d40400c3d0403520944010a500480c1d560360208001c01034540c1e403040707 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 28519771 1250 28518521 28518533
    0xc02030f09091305070f060801090203060d120e0603010b1c0e0d0f05091201020c070f0806011412010606110d050306091303050c0303010909021806010207030314070501090605070813030e0607 84
    0x1c084081c086206100d07000420280ba8100f000c1521988d64404503141e0300d803807140c401e030300c025615a500042c0c00c1d40c509003c90301c01d1000c5001d0001c0f51500100711200080011995003080e004078043d210005403050b0405d550445a08070283c0c0c840b0144102c22100100a032501c1c401010101882990791400900d188074404444125a0084c02010f900c002c1a062a0017034000d101050300b680305d03041000c10b03081c80040361501120b00c2c8400801240c2c1c00c2011481100100c100c8a980024002d40132402840c801e00914001d0000c0350384019641c154190150328001900c0040b509101c07040080c40780a840318506070790320215103508141100e0b250300e802c075601c0c0b0031740c03a109240303010100c004505c1c10300c250400400d590003100ca4030320168034000c804503900800da4040e40982e0007031904000180c003409441d0103c03045c850b002d81c02d00d0341d2034075030900751251071004032441659942041107090300000a10b4108100010f148503031800d0b6034028025400346410345200c5c00001c02e2500c20004 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 28521021 1250 28519771 28519801
    0x5010f0e151209010b09010807080d05090609121f0b0a0e0405030c060109050f0f07020c010e010e030109050c040e010209010503040b04020f1206060406140109050d061503080304060c02030f0909 85
    0x10307414100e82d00c51900000c010f000f08200d00b00944a0b003000c070000161844009100340c2641c2034007014120045014030705a41c540e12001c00a80c12038400d0104006a13945c580241151281e040f003c0c0244105084002401050005445103694070703080b030b481030b02d4980d21a80d409030303401500f0044181c0c480c0e003050341c554068840703980c0e20b51041d8400070460051b903802840c01110341c44142000c0792103000030701c20540400c40761040180e210004c2c0c640b84d0b40c4181c13482440300d8018103003030300410a40c0c0007190031348082c442c003070316150700020600c08542054420400d01c0c2c0d02d500000c506200404000a002d440042c0001e4400811500441e00703640d01c4911a1fa0320600041600081c40d500c060469140c400441300b00340320354501100001e507042c00c00d18580c01240d050303450401c42230400b02040040041c1d418180d4900d80e4a0444c14655844200c0d0800518010080b440c1c4070300d020724040c0d0a07155070482c0c141c21074100707100c49645024488241ca085240864041100d9540e0a40d5540368071 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 28522271 1250 28521021 28521037
    0x912020303040b03011e09020a17060f1e010e030706090e07030e0102030f04031706100c0302070b040806040c0602030c0303071b0c06030b040b090c030414030f07050d0905010f0e15 79
    0x12002000092131b010208100b900c9440c000e1078164111f40d0384c0056412402086959000700d60b004850701c286040c8264010341c0018004e20310070340c01d440100031403006090a6a003801890207404480f00c20740e006009150300340740490040010f10309003a401020043c1ca445851492880c1e00040b41a05000350058512054014021074580c03600c24507642c4042c2c0f040e40c1c290007140174580d400c40d10401d60182e0b580300d1003014004190384110418100d40c2541425000d80c1107010710f0a010489514000c006e10003000c503171004190302e007406d0501d003003000b0041c4d01c50f50640d40100030700b61200d9004010b40764410b140d41400b10884010200e204080a01008000c0c044170002c88040359054055010f602c0300d0505403070412a8aa51009020703039600113031a0144001c1c0c0910002d00000d684207404400c164000301560300300702c1e8a01f01541c0c20341002a040344c26800111a50728032681c0680303c00c0041c0801d10707141c0049074420401400e2003490100076401201c001402d000250803420444803c6 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 28523521 1250 28522271 28522289
    0x5070807030f080f04021813020301090605010311060711011d040509012c06060405040c08150403080709051c030e0d0c0f0501091a0a020a0c031a010e07091202030304 73
    0x40c00c0c0c1460028207004810548001099a9070080f9030100c420039003451240d07a0240c000c102540d0482000711860030018070040e100c00000000100688081c001c01c1000b41c4a1040030038654118034191008a0400c0c83c01405804240403220210700a6121810f61040a080141d600f403210f003441101119400d460603005030922050049a00c0e05511820904030050401501d034034000004082441011001090076401800824001d140a5000c141c100d482180b0003d019503481c010036041001c1809102248045401000b0a03da0450341d050b0f03111100740b4144054030b0900d0f0010304050341c2d031051031001030050380c0f00c10201802500003868064006005440700764580c50030300c10f0860140101d01c0005081100050b042d4050441001941d444000001c06850080e0b4000d4441e0019240d00085103d8080d480001c04d08a9441c00003440c081c560030000c1180303a880c14148601d0690154007030720b000304204102180d0001900c800d9542c480400461008076000281c030b14050368000c07800c6 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 28524771 1250 28523521 28523527
    0x1a06040815070302040b09040543020d0c0803070201090816061109010807050c12070b06010216060206060d06060f080a020907050901080c0a030e0d081008030301051003020307050708 80
    0x10120005506412019041e0000316941c0c845004070264016071150a00040c41132102d001c5620f4540c1109611148505113003000c01248103081c100d400795044032103058240c2c050b0040764440c41900d05408481c207800205076030703850800006c00407601c800740501007103004804548034a02c00e40117100c606400014403901c490703003030403201100fa420f490100d0302680f43c801c080ca207c84c5030b4015540c00c140161503000440c0c5d12010159103a034000015640365004914040d40f4400080300a040020300a030151101840d080c0006460500325140c04001441118010094140d0004100e50721081c21f5803d016500307094603114014140e107800c0f8450174580a040403e007090001070100000b8000c4a0030340a5403940042540c0501c600d801e02e60000d02200c0010b581029032000406505219150020707171034480c07000761414038103003100b03050002d41902c0510608500e0304034564040c203941d030003a52444d40740c000041c0d00e005010345800141500400000c14541c042e0b010f8480040e00080c0c051350f = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 28526021 1250 28524771 28524779
    0x1103010216050f0d08090c010807050d02030703020406111f020a090509150a060908070320030102030a09060501080106050d0f0c03021f03110301080307020d08040f030c050907020f0307061a0604 85
    0x612800e031407029999500c0713521907402e40f45126680309400b43c0320050160508400400c011241484010305c60340038498100b110b1420340b1b8243c4004e6204002980d0010b0303c07282071000050000402201d2104243d0001045e0388401c1251031340020886018840180d98456200301581d4881e26a408182c0c841100030810016030142111182c0c6500e040303404c21340c925225201501c0424041c090b200c516803005100f840050a003124101e108580989240a0f010344100021709980c4101c2d81100041c1e02c55041004004840c02024050281c0d24001c0c0489803c110116070800c0b032000024020030300c8566a203007400034100550f000386801403c20312440f24008084581200d80d102020002485d02030103c00e811341030020b81c0e050f83c0c160301c083c51509110350208140020a04400d54014408100020340c5171855035444000314441c8415400b001d1400c401c10104500042c01101550025501001c0800000c0210307103607558000400620344000a403003941000d425104540c000100003808a = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 28527271 1250 28526021 28526023
    0x60408010905010f0621060f060b070302010f0507050f0304060204050402070f1e08160c05040501080d02010b041104170a0b0c090301180b070e0609030102041403101503110301021605 80
    0x24904a000b41c0091260070801d5659500719021481450440c0615168a4141c4a40c1010750704d00c0d07a00500c40412101480714081007211016031106101d07900000b98a820144c082c000c4102c44c041090b000c0003076250041000e070031441030f002001e00d40e8000100050070402c440d07041e2800303004041d004545500c0d0524110520b00240c101c25981070715240040188200c180100150640d40040c016040081006c040c0038064030707900f0101c079004403044010a0b40e0304d42c2e1003801d0080610310028120083d440c1c0340a0300b1501c0c8625041c3c001c40c00d120010f56240c000310211000c540302115254400428228220f04000c1c0c12080200150041c005002000e40e070711303020b014409011402040280c00c10100c6030b001c06041d410041040080340d0000c1c0300c050140100c0160392101500083c585040c603c00242240d01039080300114a04042c00c040c10b038102001031880c000b803610410044001e9040039241c050089100040c00380d00c02c00028540f9840a405591030212400301303004085040e49001 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 28528521 1250 28527271 28527281
    0x100e03040e0c09010c030311121504060801060e15030a171305010e01080601180b0408060a0b0a0b090613121103250e040201020c060a050c0c060408032706040801 71
    0x1d1841050a080800e802035056002ca48036038030140c503281e03080009682e0540c0504500c00c00f049a41c54188442d4100b220894505c6104913503003030214510308121404c100403124260800180baa250031001e0240c091034600c4582c00844011008907030b1451140001e00d0b0240d61600140b125a246084c1400e044400f23014190f034008402000c09203d440c0c40044600d094100505070004985001007802940500d01035000380f030500301c420b00c01075210145039102d075000790710000107a4058010012203d4441c0f24618045608842c201e0b0b00502e4124941d41c580250284a44191000501e2003c211407042000d0010150038a41084804c0039092800240c004009090f000e0b01500076200e05841290b0080c0008243d00748805c10140d0800404103410030000748224150b100c1d100b200070265480401414100701035540709542d4680181001342014003070a08140610310074002801a09004010354041c0f4141402e01d5101070910210002c40489a50080d90032250015000c0381841042d004 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 28529771 1250 28528521 28528529
    0x1e15120709020a0f111005041403120a0605040e0a0803090705040c0f02010e01061805060312120117061e0718060509180105060702090c07060f0504030e01020111090f0102100e0304 79
    0x5100704416149400c2c5d9280c4040d050810a0360001944004038584603480075802c14010884c90b038682030080316031803030359000d03003401c1d0803014621040080380481c0d1f026941c043d060036207042c8041c0c0c00300c415040d6070307880613000200244408000940303054403c101d80b200801006006000508003100c0c0a88000c0002e10480d0055080090f031154000e4140a08001c076041c2407042c03400011482680002458045c214940c50300902c420088018041070290184844445c001c04195140c4200f01602031400e02203c40b4640141040180048522000c4000907001c22440f040c0c075914104111078195560320b1110442540d1030001c0b603400da0080213070981800503200c101400d81300d44d103500c0c0074000034801d195021608010101c01800c1c00c4200c5c541103414a01883c0c1820308030303030b01d1a041d01c176101540107800b907941003080140341e07100c84c480810920a0000b00940b44800b40c0c820042d10541c0ca0035030203800c0740415032056074420440980707090350010041140c050036144c1e49450f40c1c400c1c41 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 28531021 1250 28529771 28529777
    0x3020f0604080324090c0a03060b03070504080d030b010215090109020a0b13080a150c09030b010305060403080f0601080a0e03090301020301090e061008060126030304030e091e15120709020a 83
    0x1102051044ea403d0318000566000f4501c0026940b455000e000c40e0b4006180601050713251400002c10340944805075006070201d868050f207903410824218600f0402c1c42035201054280381359a40710b80d8021503101d076100303418110700301941d46070304940780035000701c44009402110652000030a045201d02610186502194071f00050b88e1381c441c80c590b18246c521000d0b00050210368081c9484055a000213050328943c20201101a50b0380c07585200d03000241d20684054214104120801d5400001036601c2136000b00752090909020380003c0c4001c000030040c2c01074940c2c44a95680c0130508105a6a040c0e01c010001d558130f40e15000380201401c400101280688100740105d0714584407039a101098a6020000348142e0307103400c2c20601c4604498503201c0002c1d041c0006200d5210080c0021071003140030f0707260305507086101000c0c084018002461041ca15500801d0b40ca03506040c0007030990030056031b030040c417090100440051050200250f08500c1d505c42e0060004103003416801810071085952 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 28532271 1250 28531021 28531051
    0x9020607140d030c020312280204050306070801030f0209041e031d0303040302010203030a0b0d0807060c08060a08070302040f020d020a080412050f0409090314030a0b1e0306010302060703020f06040803 88
    0xb001502510307400314030030000d6001031001c441ca00d01c81c03442d1560b00c0ba07480200e01483c2c2c81ca081110520350101a44010b4040e0000f406110500b41003184c1a04180585410f01c8658515201c00f070054240301002445040b0140105052011981415490310134400c151018281076140142c4020b21041d5416104030120000303214a20f40401640c2c1101e406802840c5141d40d81070039040101940b82d416070780164052401c0010071302c06005403038500d2041070001004452010050300303d20004101c580b06610701c40080c000780c100460158101c030b40c10794000c0b900103526004a8080e026880d404542c151011448840040c2c1c0858503d00490180c500983e8150000f00111040e1062044010742c080b409c10003002a81c40c5a4803284403103000b40f070311100180c0c11030080b54440c0d20640300c1d003000c0d81c2c80e080d8100c81c51908081c0403045100d801c180309102c245040c0402c0c1c4585d01403001910650b008180d0a0a140c020302c11070081940003020b40b2020311f002e14210b07000b50019108144070074048 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 28533521 1250 28532271 28532293
    0x15030b03161e1412160b04090516120f181a090604030801060f17150f030106030210031104090606080a050903030702060105091e0903041a03070504030303020306040902060714 77
    0xb02c0c0d040c41920002500c3c91180c1002c5010f1140c011030101c40b131401882040d41408001451403a600040c2112003612a030721407a102980090311b0028086c60224111a00000c141e02e4200c0c002c542eaa0b10180c1010407a1041c0c80c0d0120000c1245004416034810002a000100200005c02e14a0519400440751042e00d0303d80c52207680700c4003110003c02040c080d0313005001b02402943c00209544852603d1400135008d0880000000400d480c8414104a40100c1e01c220b0b1070400c1c0846580c850940081201c01d1841d0001504550700d030700114185603444140d01c401c0c1490804031005003008410078031030107a40d1f40e07004050b89400c56a10310810f03d00340c04a0465100402103e01440855004155990030241000001d000c0544002c13540c040b40344070307014680b50100c03081e846650008099a140c034a1b186000146108111900d20801010810031041c0ca4100054400b9242c041c81d00580302c1e17946ca0049801000c900300c01940c07081c8003207042e030200411100218070500240041e1600d00c001 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 28534771 1250 28533521 28533569
    0x605070809100f060905041b0f0b1c060504090f0209090c150327031801030501050f040c02010b030f0c0306010902040315050a1d01150b04080304090b0409020a0807090c0503010f15030b0316 83
    0x22a0103035002031f000c00c00290100210640701c82c492a039100f10001101a0337580f0001d0229012f124040302c0c2480d1000c411402d510340000503551029500010704407022031000050100e44445000941890b00480414005000c0254880c60130205000c21030261028100a596039000382d0b000c0c09008440d04a00f542952007402440c0c100c40c0040c00180401c48481c08110203000c18009039004c6650b18081400f055034204503140c407040c80a8054031b00d0074510340c00c2c1418068141c0002c0c44440c0100400c0000030070303c80c801c2030110582840014143c9a101e085800760000114a0f400c502d10f000d10780c21240019848188004101040300444c075070384081c1c140d5540154411024240c01c10701c001c020300d62840d04109080c0307000600c00194070b40550300061440c02940c20610b901e900c2a5418806ca0741d0610945040e0304090402c00c0c00c5601d403030900b05000501c1e0203a240d02c01c071102c08203d41d070340c000d400c4600303c118000c0540340340484034604800d1405a0744520510755901000f40803055031 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 28536021 1250 28534771 28534799
    0xf050601050f060702010516230c0d032304090c0f0305100e0105010c0f15090b09010905060106051b0706032f030604110c030301080102070605070809100f060905041b 73
    0x800582884e041045903001907a142d000f5010072019020f0b000502d03c00243c8030309000c0940c50112160710050300d80c550609207840300c0f144100d40200101403080b404aa08085940021130081481061041900c03804000c0740c011507024500c1c1c10b00701001c4040b03068100300b071030f01e100c2d0b0140d43c1048655201202c10382d1100c07a5108a800c02e01c00301380144807a510491511b4400f0340608112009024160740310005555480c181c40b460a0703465201c94200561441d0070742d0071000d00c0000303110907440c90b1034a940702e140c1031140000b032090008681c04500c1009904c51002c0420304180c2c0e122075a1214060040c1061451869092801504200003c1180e00e034030619542211500b5040d903507424148002005100015030542e10280105c09542c001080118060f004c10000541c407140145003500540390003801d8103080c0301450003040201100040c91408510703070005c020544100f00d6070b04000828107600080c3d520741c1003004100600c8407000c4090410303490100410102c42d520100303060100 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 28537271 1250 28536021 28536049
    0x91a09040605070302040b07060209040b01110c0904060b0301150305060601030c0203190e03071206050a180204050705090a0b030f07050a0f0c06020d0603060906060e090d05070614040f05060105 85
    0x59104808580880c84960000d82c1c003240f0390800601d000e440e9004108030303820400b012222580c001420510604050043c02c01c541002c1c07d1821805211071303010364503030031007244050054030010006011b00400d90403201c1d0240b0084c008012884910800040310850b90000361514829140410041d5202c1c1c0314010310741c0d0041e8050343c1040c4018040130548401440c00004000c0181c213003c04955051240760010140c1c1d4159405401d03a5180c404180c1e0002014030240714904801c401c07070400064944010b1550440e00046c0c10755902c21300f96190300615100e00d8001a260f080401c2c5e114412000314000d0320041310340c584a550340d500840302c40c0700c2c2c204034a0024035080ca10703400140c0644000c1034040e10a01c2c0143c00c11030070010721000c85096500039942d41d03480d60380351400d10a040c40f48001400381c40004442518080d0301581d03441010340050780c100240045e50350140800c03176101c00340c40c0588030440011401c2900f02000700f00390882c426a010f000b00000092503181c220343d060024 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 28538521 1250 28537271 28537279
    0x2030907150512040f050601180f06050603040209070c08160b0a0510031e05010218100206060f1c0b04030203030f010f05010f0302070501150801020d060807030804030210051903020301091a 83
    0x5540f41800c9411800500200c0303201d241c0d51504000100d0600440340a84190004074070354034012002d6030191211604c00003d140e2410354140315a4990000f120340c080c0e0103541400030341c1c0f50039104803081c9a45440c00b405107240816000e100540c11007030705078101c2c060440390056494180300002252410f803002903404c07542082c00c000203940c00c0e0002201d120f088002a02c00c07002501c0e02403d81e4400c0e01c01c41681042c101b80320300e06182c00d005840e0101e410380f004103618500356012681d8428110a198030480c031900022806051385810340d103039582c1c00350b00e200a0b400c09150113581d9410690b0480c100f03950342c2002184230069140715100701c46051b902e06005929608041e0000d601910b0151159500c4280140341c0603c214000002042e45400050340d58030706d051404111121500030281c1030300071b090b0030000304c0d0340d501c251030136242c049881101d40017800100f981c9912031000080c1f40b003d2250105500d660b09940036604803081540305100a904404454a00c15207021400340c0c0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 28539771 1250 28538521 28538527
    0x2401050904030216060f090803031603020c0a0c0f0906050603040c0b180315040605100807140402120408030609010b0910030b04180c170105010b070b090106050d0501020309071505 79
    0x6a103000040c980d009402401680c0e840080e05440003402d02558104c0c40c0842d400b02640c2c3e503031b5980482c030b800051030702d1720196045003411041003856114241041040540216001c080208188200c4120581c80300c2c81e901c01d541d41e50300b250841c0207184940b000c078a00d03264002400f810050200c901c00c0703034031544950001c0d0a203110041c1c2034004840244500e0745842440c245910104094460b01c1804100030b9102e14041c1b401000343d550042c0301c82c401500f040b201b000036520000351941078403002d0141082c1c4569150101d002401080780003450842c3c104280030604c40c2c004000c5000d80002d9030000116a02c40fa00200c01d407203903000c400c0d000315a5248107110103210b0b41c8070a41122004101050115603007042c840c40f20031555090b0340c0d0080e824010400f0303460b0050010700d0394800c0c6000b4880c40d07140580e140a6801007190140c075600314400018030420703080d8040406440c0041424040a1603814502d000b5041110000d02070301c01c00038042417003802c0b21030744800c810aa60321245 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 28541021 1250 28539771 28539779
    0x30603030207120c03020909010524010c1112011b021207080a11010b0303030901022107050319060503070303031a09060603060d0312020a0302070302060c03100b0901230c2401 77
    0x1452411044040c4d07250703070510f0000700069454241250203a5088000805d190918400c01d5083c1c448008100f4080c04c025a00c2c4070303540e41c00007100c10342c041d0460361180791800104081f90b034143c10801060751951a149280300a00500904401a110240c8c03c94040d03c6110040c2c80943c0b280c407034041c0121106001c401e00303451046880302c00b2070b174240001007405106040400c1c51074100f6652604140d40110b5030f00398181c4509580400c50034620042d4203203091000010780a488064801c441c0240b00030710741f010000e031a410aa000741000390498085a5407803c0c02402401290503640c0b144883c18245031007445d159410a004260080c12680386813210b904101c588800c0755406c0f4144460004500d14108203403001c1c0c52801c40c00c0e200566240c5151400a0425030700410421403100180180311402d08000c44039001e075070010200075035580e42c030b0005031602d055450084074a40c0c511202c2031000590385018040341c2c0b69070000c0301c080d800201e22400206d6601d000201c00b0b031240d200100 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 28542271 1250 28541021 28541039
    0x140304021306030507140415050d05070e07021608010c0818190803060418030e060a0c0b0405010e121e030a02130e0402010e04090f02090405120424030603030207 71
    0x560014401010405980500d103082015640c01c1d9005135060380204130704000080040300c1842803000300315000c1144030010030380d2104460344c4c2e000303082c0a008101c481808115003000250080c2c0f4005055605926000b03000075070b1202c0500c0200004ac90304900024246c00500a10490100c203440712541541c3e80c60480030850181e41d403102d0103115980641c01c0c005403240600400d28010400940c1d41d00c1c0940c103100035a8441c600100801043d42540e1000c81d6120b804c0da40b01c5034089801d07540c0c40d28240d000b244c40071541032000e040c0b07825003400d001c00c003d0154840040300b551781c0d003030f03400040c075000e203800440c0070703650840c01481c080600002a00069900031a8004150070006051110900e60001044a250481c3c190313618200700340002c0d9178201211400860341141c007404002010795901000004608000b409950703020003040400c18240700844600c40050b070001c2d1120368441810407441c65000d01180041c0c0b0000d03040d54068032034020b80c01503a4058008200661401e9020 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 28543521 1250 28542271 28542277
    0x10e010e010e10021002120114030303040302060c220b07060b0f0f13020c0106030804090b2b0f05010f0606030e0a0807080d020403020a030f060f0605030709110d05010602010507020709090314 84
    0x3c14118018428109144c0649101130b101180144080450ba9810012030240605030108098881e60043c4100400aa400a040c0381e01a101004039a1580c24862903105c00030340d212041684000c4d504070200380004003201400941d03010f004244030220a41c820b02224015214038613812500321000060507082140c0c181c0c1e200c45100100600c1d0031600b8110078212941904215100f0000040400c00c10899005282c4002d004864442d84c08210025540552402c05e04a44144c1d042c0410003040c000044800b954a5411000030b020b07410031280c800d001400180941808039240000d10000910700140039241158403a0400d0b14000c5151a2400d1540060750f050034165001c00000c8010b858404520300190311076101d50b80a00614a020400d440c9411080202179191500800c481c0c0c0d00001c5000c210303054840001501c0d00c104151056606c0f422036490940350408000185660341580128400d40b003a03820303941080e0f110380c40f00c4161443c5000c017070f00041c418480c8070079484900001b = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 28544771 1250 28543521 28543549
    0x18030f030c020c0319120e060403021c021801090e0703020625140d0905040209030a030809070306021605070b0a05030103030f09120b0601020d32040807030b06010e010e010e 76
    0x1100e4010303031403d000030b2500d280f020080c1c50900c0c106440d01c0410030300d11401c0704003d525041c40183c0303150a40104185004612010b423203682050690941c0d80c05034801a0b10158019000006080b4001102c0e0440c900a114081c0700c503251466400703041c500400e020b02901e90081c80280b505505610310300881c0c85080500c0c401200d141c8850b40061080c004044281050030060b240710302d04010081d203000960782c0b205010754010800c00e0455078021a80080055043c01c20062a4582d081a10f203032100b00e410003007030680b0010390460701039604120402264440c3c81214459034039800101940d0246030400004214188018400240104440e002040040c40d10102141c0c2d00c942d0003d100100001c1036503800e0500091128a5034103028010185030342c0e0800704406860070044685100180030084c40c52001030074141c040004c214100e40050070075100b103c1d951500c0342800c203a0341d1400c3d150103010613819003004802d540529810680c40758142c503850608c45204007801440940c00c10 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 28546021 1250 28544771 28544773
    0xc060d060b0301090e07050a03030e0907030f020a090f0f06080f09030f071203050f0610120b04060602060907050f0d0605070e0405070306030c0801021e0a020a0203030a050d18030f030c02 82
    0x3401084406020014600800ba00c80d000328501000d07090550400301c054119900417100168244082500300e62069100f0f80142c54450a5a5640408400501c40511690f00c49070002900003980c0e41d200d940001500c451480da0484a652114000d1030845588280e4004c44e078540d0018098660048107a42e2005140c03007a60310741800064103070100d9001190484058240c0d4a5903055140d06100787e50348081e05004845550030040009030108080b2040b02c030402284a00118943d00f2a0304042e1400f94050020700c01070b0f46460010351038107000c40701c003140391044d20b00001300c500d815040903040b46405010b010302941e02d503c8440241a00402c2c010074403501040480309a20740d0310603680320b0b55240d5000264541140ba16036200d4000d6807080000303038010722009508007110a0b501c1c2480d1400702d00c8031f945540e01007099003007025150307019526000204001802c150030070020007410703020030800c124401a03668003040d81c1c140b000b40a400680102c01c000b0600b4047e6201580c0b44403140 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 28547271 1250 28546021 28546031
    0x170705010507091415090d020301060b0403030201050702060718090b06130f061209080405090403020f0a0b010f06030c0f080c1303080c0c030d1b0c0308030901060501020f0a02030c060d 81
    0x525440d0030749406856010004038400310400c40108100c07134256010a01302c6004600c15400070044200d4040c0c40e0416108064415440c0e0841d502544160010541000c041e0385072956410081d000301421240003000d40034542c00180d80610030703031066202100c6c0e002c000c14a182400340007001409000b0030280c00030410000d841c013651070107001100038403c00401c0e01c0121306198000700404010310060321110f08040d842d01c000b541800c00c3c3c8041d9070040c0c070ba02d481070b5a20b0030203e16000101950080034091080c02c0e0302030000700481136042e15200c160524409640e00000ca00700c0d16103640c0c03840000d0400c1c1c0e00c0c0000c188030b5440c89030003172003e441c41c9080910300c0000344038105195004486040000407284180c04007403080005c0142c045012341042c0c0e4144074041c1640243c040c000c0c0480200006201c100000008403001a540001c2480e0303c03460a025903070b00070711075401031a003d0300c261071001542220004106502076800380191000012950902c140341d08154030076100c1c242c4071 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 28548521 1250 28547271 28547273
    0x305030a020f0903011503050c18060d050307080708040609060e06180307050310060806060109050a06030c0c2001080109020c0717010902190608090c010f0e030c03070609030510050f041707 83
    0x1d0080800c00344c0510f074100205480e61410614010070321036a00d0282b0241c1810800e45110a144585e0001c01628525000c0f100d9192540c1948a403580003480800040354050a100b00b0340702401c155002501c40245c1d10352a00c10a82d0030345200442c20b58072103030801113000c030000405110000e1035005001c0f90001d9803100000f03800c2c108156101c800556a891041080e01000c204042e0429000e007002990503003001c0100342411450301903801811344800304407241e01d2140d100c044900c2d812041c6080a000c060340e01403100400796145500240e1031b6030010070788101d140700700d42025401704010701240c0d24200074a07140c01b500e280b81140e15507890424002588510008260403200e24005e11001428800c01034103070b4201819060107644000c110101d2641c100e0140811410b240c10280d021407410000640b810501040c00d5400d0b01440a000440a400010900503a4414010741d17000051120058044420440b083e444424100d00804e021400350810042d00b103640d84c168070f10b46009 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 28549771 1250 28548521 28548523
    0x70206031321020a0b01050a08030a081e04080301030201020609060c03150105070501110306100306150c0204021603020f0d0201051312090b0f070c050108070207030b06120a0b160207030305030a020f0903 89
    0x45140100141e0094101301c01000764860f5001c0c0502000c4410306511420f1031a03c40c3d40f8000c010307103a400c2c8042e503404600350300c0c92160900203840b82a040801940b800e80713403162440d04280710403405071060a000c50042007021581c00d2103400b01050076030440e1355041d402c10402414020a40c103008041050781c0109a0038050751000071140c2941c1503072802c041c8140009110011405000c25260810a100070041d20400580c0b1101910f072007503840d007060000800a214035a0070312075041000c070b040010950042902c515071200c0740c09503260101180800d03826904101c40036a450320802c4801000a41030080754044081140340007002c0c06e887e13144800041d4040350760002c4464003c620340342000003c40350400901020f1030244518149200040d47da44001d020080c030584105002403802d480d6007107a880d40c07810750805c82d040203070242800450510240c0e982001d00ba0300c0311070020f51038000076414046a03071681e00c1d6440c507900d540500e0001e400c0300103d003881c10b404220010490398 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 28551021 1250 28549771 28549823
    0x5060303030613270b07080603030c07030305090a080d09051003020f040b0a02030f0301031a010b0a020d0c031b0b0a060b03060907080405010609330605040632070b060103020702060313 81
    0x4494040d074017403800c007034002520907240100128840d9004000f000001b040104419084030740c103040158079113030003400103104041c5d16003111442d442041c0c2c82d45c004640c0304a0704400c039441600c24900c2030720940400c4040c0d1013815100c00c40c00c00c00300000c11405c818075000305004d10080c815030341003c00c039014105050780207070b000ba00c80407078010362200e0f160008110b9030700400c01c08115600d058a1124040e456a0710341d02c0400030311054a00c60014140101102e410694400001400b0003019261040c030211090761440b4541d860300e1808540c116400d0110782c024800144813121994413542d00b1128203200500883d059500d0340c1c0c0c00190300103e8061140101003a489010b10000420b5142c8550805040c0d01c906422032000f04201081d045400c44060b1561031408022015190503e401841014484000d00d1000420111850f01036100502410341c440e00e101703c0c00e81c940400440a9000d08800658000410000306403540600c4201c00c00043c85907d4000c01411000ca240d900c0710 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 28552271 1250 28551021 28551023
    0x130803090a050d0e0109050409030c06050c1e0c0a080d020705030f04051008010f14060f0a030c170403021009050a0b0a02090a060c05060103121403070207090506030303061327 77
    0xa8064481c0504212090010000c07840a40c40c20b2003840c040600000d05074040c0741700f05d901469545e00710b2014140300d2030300d086001da0808030501c80d500b045044101c00d580803000d901c3d044501200d2280d01180c54800711084105c00740000d103402117a0703071900b404941c0180c108002030b030760800800f00010400e0025207401555000600c3e100c03441c4c001840140e007162200c0301c1c10442003400502000800400e20300a58100100c44006034158a01051151103004000403101002140c5294500d6040e08a481400440d9541c030f481200e00c1410011049401d031002009030b000200c61280a4a4035442507005134061411100190419221004501d0060ba40072521750f4000800c0021400c00c0030700200140710600d400620700520b03466940e200d610601004103104000c500d1102c1c50343c07007800700c030019400070500181e40b410a00406540c0d60643d20440260a04003000203c60780340100c00d503440784c1406030103014007405032505c500c010500d0b02103e101e04040c031046807105035100202c01d00340b2 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 28553521 1250 28552271 28552273
    0x908070e0406110304051e0a0206030a05011e14090a110c0601030201081006090b03040c030c0b090406090216140106120b090105090102030106020307030c05011b0201020304060b011b020913080309 86
    0x142040d00700b071030583c0d1a800e0110001d00d0100180000200005900c45402000f24140480114601c140c1401d00b8500480607510110100074811000403e13404241214110030203401c0500740303400038045140f4070340700c3c01c810704001491280c0c25003898010254082c3c540000000d0101c0d1400c2c8120542d005401e581c10f8640c00100144110f5070004001504552000070b20600203141102c020182c401601410040e61001300c041010000e40c0700483c0059544030110026180e00d80d00344c85503541103c03907514803540c200000001d091005108584070321010303106280e135052a603155402180c858011020040d984d41038005441402051183c0000d442503070744000c0c6003407106c10942075543c054075500c1d240c0d204100410280b43c00004694405030f240c10f200301ca02d4051305103d4014180d00e8681c19003d88030102a01c4010780c10344c019440f0380e20901040218159210044900080005600e0100c03c0740140729005850f00c3c00155130303c4108a69a0703912500c0a60300c0f6903080d0810303500819070f = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 28554771 1250 28553521 28553549
    0x80705070803161107080a080f12040b04061b0905010c030c0606091a09070c03110304050a0608061e0f041a0402070f0203060a050601120b0f0312180d050601030303020307090807 78
    0x43c0360b910150300d881500ca1140209051420b140849480302c011b0708009250040000b83e401013100c0c421306a462030021000c040c0c0301c0b86001e00300002d129001315011102145001c01d10398095000b4419800381d8034882c0d41d0f1001c824102401901d2045441c80705400f413000034011a8005841801b030700300906000500418004100c100d00c251285008400e80d10400000040010655100d1f005424182d014074040e41510304c510501801d603c6950415070304021641c50203e071540e08030440600448040da0501154600350f01e000b407030035002d08542eaa00034801c11010010f4601038000140c20100d804107002c4030400040024100ea1240320212001d0f407200c0d0b00c0b03200750701c0c0500038030380c5c03042030500c040c0024035140300000c000103240244852010795405140105441d10107440c1d000400241c100c80155900103041845900082c0c1b105406040d000580e041500340705850040c0154808000c02803642556801d40194100500700700030840c1c90b05000444590030050040100b100c1507103a88 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 28556021 1250 28554771 28554811
    0xd0f02041b021603050c10090305010e070f080303040201021e0304080a0b060a080f0604021c06022a01020f0d180510090b1303050a030b03072303010b0102010b03030a080705070803 79
    0x400c240c0044080c11404483c60380400100303a01041c0490000011240001c644030a0001a6035100301900050115882d080000644960018025090340c010710b102c0c00001e50740e00c6c01590b42b44801c8078028016004100c806080b80c00d02085404180c414a05a07400c02da140c1c44114541220250b0540c1c4d082d6201c0180a00d600700031392501e002d41b05181c0900034004c0028191607032040c0c081d20090094009441c00e10035910745d0820804034551001040d5a503050440410070344030108a10148030980b00007040ea4806414400c980000c4100c102c0b25080c80d000e02d40708401070400d103400400140c11030a10000046c1c05004005800d21000f80000300010320303040041d080080107010f034452111001a04001c290804251008594030340b0700400c44040c030034082414480c0b01da02040d42e0480c40c03074404002171607410840d040039100703800800110f443c1200482c2a2117600c1402c1d500f40d00100700d00300c020b034460a0383d50340c40622410910316121250b80d4401203a40102d44500000001c00d01e091 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 28557271 1250 28556021 28556023
    0x20604051201061d04031b0c030c150f030606020a020603060f06070b04150b0f100201060b0310060210060302010503010b0c070b03040605090606120619090501020409050106120e03030103020d0f02041b02 89
    0x100510114161513080c07400f554003820814007503c00b82c1201e00f5120100040005000d410000b840c1d00c0340c401403207075548246014003c099070324450003060460f580100001c0c401d118003400c03611140d0003068070381203940030b0100a6001418444d040b2038010b4041406458000081c00114410440d9000e5480c284c10010046a00c001d8910032490034605051403a54942c5846031107120111005408103400c0700e41603004101c9980f00c030706c0480f000700400071045050030a4008454164094451501160a490080341c1300741c00000c0c0030036018801800002c40003009400b00c00c03803801c00c4910454540121a0464104a6044544e90b440c0c03010041016410b02640390022400e81d000480d66001212060b1100d50080441d00d00300d00c00303d00e8056449042d0400e032105500b001c021951240c45c0c03c0e80002603c0240142e40200b4104080703005450302c507200e2000d20000c61005582980d0966080042e030015800081c3c4001d20f0400000015944601c61080f40e090078079543d04003906480e01c00303 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 28558521 1250 28557271 28557299
    0x70804060809030f12150d080a0201060609150302090a0e040c031e0b0f090106030c0906030303050106050a0f0c020103110d0c03110c2d07080105010503010b060906120402060405120106 81
    0x855403600300344540c940300b85452042d5103a28840a0201c0c885541d40e14446409404050280c0c1e4400304140703047c0180014a001401c41c421954000d016441d20b4040544a21469100b01d6850b180d0702c07141461f103039200340c2c040e001080c1c0c010308aa40440d56840d00380047c11041d20207840f000f001390010800c114580059810018814003005030005260300c590064807401000d05480c8007007040080c58451080d071100b40555070040003507003615291072207440102060700040780070910703000011403058000d070250b0b0300d80f0920f0783c0d513100651852002141c0c1040b10150880c181511000040110403444014040d4480064800104c500e09500001e040e03c4900d107044070f00c5441001010701080d004a43c0201c82102000b00311007841105018030907403040c1d428802514000d110002c0360803130341904280e040712411002030100c0c02602003044024491a262941d22200810580b10508a005200c50780580010441400d2954990103d04100708004402886940d529820301c064140304580d = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 28559771 1250 28558521 28558531
    0x106060306030201020a0b060f03030a02030c01050106020705090a020d1104031103120307050409091103010c05040314030301180f0608030d0906110906090105072a060215090c040c02010207080708040608 89
    0x240080ca00d1a000170b901c413545010058100e0b903c07140040d90760340350100c80ca010050080c040341c2d03a960041c50f0003500c0e50440810035007694201000020400e10000f0140c0c00c3e500300402c002100d444e851100e600035804540950741290301c0382141910840310002a00095004e07801200031010000201810008022828080300b03109005020940b54000c05807030945005500018098060782440d282114140110300d070702d582884a048030389039002c00a001124070864020358a4103050001c0c0e9102d000900038850320840e441c038001c405160f00d8102d02c5c0c01500041002452589035000d5a05552003c0d1030b041042c0c4d1101001c0f01000040d105c0c0c01e01d04040850380c1401c19040344001a49441107900d054108900843d122007841085111403808024002902c002c801c5c0319072200c20000080c4c411000980502000042c542d60600071251042201038041c16840349a101048010b2000003100000c5650910203440000c407548002e08440e806000ea06440303c0c030b4100024941480181 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 28561021 1250 28559771 28559777
    0x6101115150102160f060522030c0f08010203070c1e02090a1a0306061305190204080706110c010801033305060a050a12030c031b03090515040e040206030615030117010606 75
    0x190400071078140e20701010039242545000c9039660003000c8d000c403d03000000301d0400c5549130a00c0c0002000b1135140303003e0403602182c01441c20070b80d1724070100f0701301d0108a80302030103d520981707018006901207810b64240600b0b500824040b5810f500401c1c01c00354111400b0300c11a030f948001322010640417540c2c2c0740d20320342100180058500200814459010740704103040e000d48440106101080ca81049240301d11b0601007151201d0307403003074041d03510030a5102c0c840114268201ea441040c001064442c1700c880181c4030103d890f480c50740e440c0c540e9002d0140715406501d070100d5010300306403690070a020030383c120403001c41c00b03040100410001c141c056101510071240e401d02006103902d80d03204660074a801d410b0606844000d41804c0e41c060300c200103490b0820b8034a910740001c00d0b402c4030580080c0d400a441d007070b89501800060400e54070542c0201d000700c900e10b40c001001880c00320700441e805100a004160705816445c3c802c2510741080e040820010320b48483c00b00b4009c0c0034400c001c02404585 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 28562271 1250 28561021 28561063
    0x15090a0201090302040e010b0904050a0209070311090f060c030d020702040b06130312021c12060b090609270f040b07020105010f0501051e030a0c030b030606101115150102 75
    0xa03001070019101c510000b401340381c031080c03251318501e07080d4000f40f030f034200241c4102c000e4580782c6030440d19a100740e841280701d0f01400b404100c2040c4a4403603244544e41485043c0d00d4030140004111461b81540c0c00164080d2040090060060341030024000703c0c1142c010158407401d03184100400e48070031205543c000c1405108030a40070740302c81066006c682c4c00019200c01003403004000c906243d41800a01e881c1106c200380010350031341c00508491086110002002415140c6003150300314480c55010b91b500001c00c1c041c1112503c1c24481c0d48080754203035030f809552500b94031502c101c1601c1c216540340c40000d5900401c4113100c0803110f0540c0c020810320003042658142101034002a8180c02003d0400602041524181071072041092040c0b010a0034180c40e4540b603034003640036140e0302114100207170811358996941e043c000740d6180503010081403070600c0b940c03441d0308a908416034030101d0340e1840f0f1504806c54a61808841c140150002d00c52000c4045031540003920f40070341000303190241300c00341c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 28563521 1250 28562271 28562273
    0x10f09050a030f03110403030807080f0403020d050c150405031e07030507060b131104180209090604021e03010e040605180a08090102150a09030f090e01060309060f0c0215090a 77
    0x72885540c0c09505050000518180301c40850081000a02c1c0d40c401020000d00072091541100c4120720442582e0380d460030682c0d420b500c1e246861401e50b00200964803184104500b5400340c80134003d070030000e100300c038840541060007148c0001c05440640d882e810000b4010202e4240310309001d1400a64003506280294940d402841841085805010140e5428400942d941c485030300002005114000388401c207401656100c995001e84101440d007142050701d103116013281c0c002e843e074100c0000c00003069580c8000034000607500c070b000d40c02002c0340741c0d00845000d100d5000145000c1d000b1b800140050345803a2034000e084403000f44c40b400300c0f00b8502980c0010340d00001007008a4030b42c000c0070b0702e40b41c000c0c5400617417a010304c41c411003000e050102c04000140003540e004004450090350342c0030360442c018005540d0340041d800b0f03403070300820310000603c5940e000390444610b040c0700c0c080001e40f44080000580031280c05249030070040e00040c081810403c00c14580540224024001e01504091 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 28564771 1250 28563521 28563523
    0x1a060301060e040b01050f211f0902130b0c01020d0c050301030809010c020f03011a0f01080c0a030207020a0302060d0b0415060203040303140c0f03040f08010c0801170f0717010f0905 80
    0x410110b1030301c500d840d05903881190344a40300740ea542d490712410040c1c07111181046001c011180400e601440e0b5100400514100c0d12000c1c242e1f0034410b61491000c400d8103140d1014082d43c000140c82007019001d0f603001400100c40b0004001c1070300034000040e2910f400c50004800e50f0f842040307860410006000600220b48018102e540b01e10090030035200035001480807541034054047d000b6819440c0201d00b4400f088a2a654441c0f14000c482000c40e110041d4015104103805662a00c0901c40501c01250a170b03000ba0300074048a40001e0014500a54a600040c415440070180c511001e407a0382da40b0380319003840e000d226441c00c8003840001c40c007820710300c0082d03407401244405407c00c614480c1d58020000803400b141e283c4421402904c5400c56004240c2d583c90380648980c200c0e00c407c043c0c00181c00c090622510041802654130742d00350364a08100340c45c041203081c100000a002d9104e4035080c030003040008a004107500c0010220202c42ca203200380c01c40e8514000e098440e030920f0500300c00500 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 28566021 1250 28564771 28564787
    0x70804060e04020a0e01210204090e010b03030708090907020309040504120305060d110d140a050a12030b0306010e0c0c06010e06011d0f0d080d020412021c0c0b031e01091a06030106 79
    0x403c3c604071001050099648411f24115204045410300c00200440c4070f12079038002c208c00c10003280080c0401000c91060664034481c0da000a0075144040c4a584e8140c07030403c845680003003040c41224104160100020708a90041e00c00312010001c1065124105405006040d070040c0700b141c0b074241d40c0c6a240c40307a00030780c541e030b1403220f00c200c10710042e01080024400181e0020f1310740604885046899207012661580207600644d40144106a08900310b4484d003c2e104000360007501512241c1d01c0c002c09079200100207404006400c074103216640b00030400f000894000c000c0d203c281a0070307040c0b603c009801c0c44101c00b40210601c802815009041d00c0c0e0040c1d041500701c068815686540c0c2d20b080001d6280520008c20b03180600001e00040c0101c940140c09040b54021240050b4a00c0f909500504c54407103e40010a441034582080040c4840d00c005103a02c00e140c007248041f142d800c0082040f11182c240c204002990340c2c1d407440603189100c0f40142d40e200100390b5035189594102000500490 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 28567271 1250 28566021 28566047
    0x1e070f050a02070f03080301140a12020607061805060105090c07080f070c0302030d02010504031806020613020111010603080316050f0418020403060c050705120414130908070804060e04020a 83
    0x2000000d2888401d9200300030b2940184000f0081902007501ca24000c8000c0c0d0080c881d040f09000c04011440c800d15224011008640805446100c800303100da00b4072401d500a504281c3d400c0d40c0c0d44000d541c400310303103001410b00144100040c220640c1003404210304c8410140c00105030b4901805100005101c203001c440b903800c1c4402e11a034071a0030500d0048036807040364000030b4060150034421110603405402250065109403100c0c0e03840010101c40140114480c0318080040e07004101107202d0002e0900c81034074003070040c5000d40341c1d222028641c1b03094510a900440f401d0000008000181ca101c0281d890b07543c00c0c40c5000c602d880581c00c42c0703002a0007180103507410240754406a600e0002d480d8100d400855018030b06004601210308050081d4200c07190a956a0040c2e001940c401401002207a0503207800d05d1500700d0448445050111320103514070f2a2a005a4070341c0c000e0b0103d04084080e00c40a880b84101d80c5e555410034070010aa403480710340c618021401400602034450b0440850740c400 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 28568521 1250 28567271 28567277
    0x306090210020f0a140c040615020106141008041401020a05090301110406080103030809101107120306080303150324070f02010603150908130803090301060b090a09050709090f051e070f 81
    0x5c600040210f420444072420440d4040d242210008280c0340001054100000c1a0000c020196481c148a6048000540d480f80c2c08800c00d00c3c0190454090710655800c035004400d98580031401c14070b62422a48041450000300b00085032516944c5424041c59a4192030000410309203850310101900c850010b0000600740146040040d040210401c4140d620034213003030050011801d40b206495540d840740c00c1c1034038060039444005c0005402070148030201c40d00f88004500d1650b4210008400410542c09550315008501000c41402071129400086000c00710821b291410585405080d241c1020403d50940e410450108080f0307030214613111003448040c6000c5800106464424a0b900c54001c0312041c44600e01000308105200102030054040c09038000c008403a02d401d13010800780564003809038080480c990038041030141d034015640060751420404181501d89031040e080ea50340200c8040c0a603074540401000c50343e406071064001d18509201c110509081364010000007004400c1014 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 28569771 1250 28568521 28568543
    0x405030a02100203130f14010302120109020a140c03040906080a0b0106030f0b0907020609060108070b0d0f02090d030c05010c0f0507030f180e090105070e1f020109020405010306090210020f0a 84
    0xb92030b0003481203030b43c81030a941010301200e0700d800b0000e000368030a020300611601c8000001030154041d101303d40010760400d004c205035031310744003e042c069404005a5070411498208404507441e101000c3c0003c03250300e6018544076810141404200c403650703405180b240c2c0c800e89010012495440c6d4150664090b85004228042c941003d40d01400811080741e8010007040d0810407115804105580241080c4042e1507007030342d23641380055407600d140c000c0d202034180c108054100008181e2180c0001584000007604055984001501010070740600b6000704a90001035000c05c2800e110b0200312841e0f50501301c8011050240062482c0956000281801410344540c0c01c503c0c06455000640400082e146000f681c95500d4108540000e0b1014000b81d030030300307001c5100d0501032101c3e2542d0180c086d01510058200082130080c48030490756190641d5640c0c022900940c98600802d4003079401102c1c0411009030701d2060001101d501c04000b0119000714210003039100020600461640d0080ca0034a1 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 28571021 1250 28569771 28569799
    0x306090c01051c1e0504030806010e10050d0906060e01031e0c0b0319020c0c01030e07050102060c0a0908060a14090607050d0f0617010501060207080c10030e0f070303020c0a0603020405030a02 84
    0x18081069001c00e11500c00704018040007151708603910441c40b070380d40d0310100d8a07504010342c0e0301407840c2d01c00c0d82d120b20015101140f152042001e0050088034810104a03050325407204801c8400a4100c0c000d0340349900d00500a0042c190707104042c20700d140c041d809601c80140c440350105d1301280034001c0400c40020110301000c651900e00b0149040744440ac41d6102580c25804c1e0780c814614080394003007400d00b1040b05c80b1001c007081c018100c65041c2c015101c144d980d045000b4050f0701c42082c040a1181c4400b01082080c0c080100e140f042c0b11040000500c800d4280c0c4501d0448401015400c00d58070000070001c0d640d900c10155143c1d001e0715640400e8102c51034540f00d01400c11500040c5070485452468440000150000390480f0034a4080e0391105840c2c040d00d9072201c607846202034100c3c02c0c81a425121a00c00d6000100000449040d038010800c01d0381420704000582d4802e0700168002854100c0070720b040d2003058001c110f40d0030110316091408001c69111541050042e200b100000c007520 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 28572271 1250 28571021 28571077
    0x206161403150a18110301050f10022401030c0b0c0a02010509060d0504080904360309080f010e01060501020706020703060b0d0b0a06080c04090818060d0f05060306090c0105 76
    0xb80b1003040100b1944800e512401c664601c40300c40604088010306103503802c5140101002220705880001c3c200c41040044402402001c1e0075180c401c00451007092002c0c603a02d00313000b112600f9000e0b4248500a194910309241e650480744d03402061107920100f00a04003400001081b5284660a003071181e101da9034000024914041e810481c83d901342020100002c000d0382d81c00401403140102d804003e204207405248100d00c0340382503020540895050401d80540100c03c0c10104984285005500151550505410f152100ca000c146507916030728030307900c00b847c2801110701612007803004048003454540000e5681001e8480036000559070327403031144191075000e0203902064206200c1103160074900c0c000d1004107182e200750360060040c0307850601d5601c0c2602a030304403d42c00c4405c4074241001540c40100f030100c4015034030341c0100c0410076070040440c1400707040c030100c546a00010b240d140500c281420b140b0014582c0300560040110b015035681c00005880a015203404c0c03006540541101c0c1c0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 28573521 1250 28572271 28572301
    0x1140322031107080304051507051213031a06090109110703050c0c090108070303030b0d0305071e02090c040806010b0301030c06050307020c1c030e0910060e0f0607030c030206161403 80
    0x325803038010f214012130301450000052088075003e546014121400802c40b1009002d140030060070358004c94045103400039818007511090000c221140d0000390b403580c4400d41080d641c0d0280844200000030041580347c1400074038014000079100b40580000714445e2a028811404024148000841c6d526200042007040ca01d04800c040c0410000c0d5031075440b4190356044600c422800223081c02c90504a9091101c480e140e02a4540c03509400c144441e940c2203080302840910034078607030310300c82a6005079a401e4180f0380070700038130080e0996550812510724140070058110201e9003a0030001040000c401c40041421142c01d45403040c0c4075214140c040303045c5000d02c0d511a034000c0c1101890401500f81c4042c07060010300c26140c1000a03e892001d11250000841c0c3c0e004c008000a0420803950b4003034400407010313540003800038100490700760001d05d0315004008150001041070094004040d0104012a0003c80c0e90942089880006800914080340340e84003010000d808030204041c0007240c690 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 28574771 1250 28573521 28573547
    0x80714070b01030503070203060108010612060c050c01060906260303060d050f06010306051005011d09060a050402030c1308060c0403022b03030e0705040b0105090405071812020114032203 82
    0x1072010036581d2800e003a0350b60b07082101c043c3c0c0310340540b2000141b0301c1c0e01481b0700d904455080eaa5424504215200c917001080003000c00000d2117000c016802c1e400720280310b244060181c28100140560070001c540c00602d51482c8001d40c110030f0074016503403141c0004140e81e8000c0e400c0b184519001007070300d071642c1420311146182155128a5002004000d0540c016611400c00c0c082410850381c0e03100700441d84580070441c60700c404541904141c40500f04500050f50008028080c9160982e950f0080341c02c03a4070841d08030120180c08241140f10a4031314010000070f0003d000104014100b11081c5240d601c070b20710000b0b2244050740031075109040100c1040010f640781c0c00303e0b0143c1410070b050140c054400400c400707000d03014440300070a091074140310380c14598006968181c246085d4206110082c40c01034109814010b000d1a18501421881c4403034020b0402100200d0360030420744000342804400801076110020705108104080c8400942e034031a08030b0ba2110705411003424142600c2105880c00 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 28576021 1250 28574771 28574783
    0xa0905030313020102011406090703090309260105330406050d03080f0c04120303020315030d11010f050c0a0309020f040c0c0c120305031f080d20060708071407 70
    0x7040000682010a01c1e41005000b07130024018201e0800040d050000d00f00c2d00309600264020204503001c1c0700f54880094217201e0b0400342101900ca4409608c01c0100b11019144048101081c0325072010030b009a80c0c10800e004085481d200070b00011490125206040140d21900111403d00950b99500060010305000c0c0c07170080250400c0c14000c3c9002d5080b280b00789030f41740403400314500381d00b200700301c4003100d180e507a0207880c030122690114042e42c00908030f10b0f10160440d070361180f07659091051600094440d00c400c0c40c840390310b02c502800e56914a40d000100e40c0b50504202c48043c6000848403003480720302c0c0020351444c40f0700c00521075003011006039400c0703854503c0081c00303982c0210085e0320761801611182c003801c4d56240400105007040000a0000d402800801c041d1b400c4840c11426450307101c01010540d43d22001e43c9807818105a800d00000b0b81d0110f030b05d003140365081c00c6041aa2441078040d209030f14092401410141001d0b12450400401003000a1424040400d59810a41c040 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 28577271 1250 28576021 28576027
    0x5061606091b1d0405060703020c010b060c030406020f0a05030703050c0a14010501050f0303030c040501031d15011406120f0c0c03030f04050c0108041109040204020d1803020d0e01080109050a090503 87
    0xc0107a07080b88050040b8980c045408003260482180c03819414031496024004010750b540c2c00b00c08030040c0d00101c485000b1036490b01082400759a541c00504020710b8028010f50719580b410300020310702160001c0b07044403500520003050215001002b00c03400300f03400d8140103a0b00d050031030450f460303c210b414000d0038203488a464801c00c83c0064100714100d0b4011036841c0c40307280059040640360720081d10400b12050080108004550194002e2000e0aa000d56a0034018400581d00b905218007a0802d04d018405540188040401107026202c484001d8403500c3c103020103101c1c4081c800001030700e200ac42d00040c90010f25a490b440c022101c0d00804170058a40300d0400740b0750130034104001c2d54221a640100c014592041d48100c0b005407041ea000b02000724040a428140301300a1005482660050307002c1114140602c00c0f030140e86400d4900190115903a485820000d0426071030003048c108110279009914035507079102e00740360305448502c5400100d070746440407800000d010103000207201740408 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 28578521 1250 28577271 28577303
    0x10031209120606050f03031206090a1d0a050706140304030809010e01020c0604120806100509030a0b07020a050d050f0a0813020a030c06030501090204030f12030b09010821040506160609 81
    0x1a0400004c54000391170345002d5590307600806460380288412a2110034900000499138600f07828200d400900101c1d0025030b0b1200c3c20340010300c4a0188a00e551141d1000c2c421400b00907040007180010003052a00c00d04482c0c000b10341d400e052001400140030010280302003204400300b9805415203030ba55070001c66494900100c0c442c0ca51b5021a01501c414280329030b40d00f4200c0c060f03c1202e21800b4000e19907104a400380c0002e64080d0801c5040c9901485111110b50020305200200e030302840c3c8a0b0010300d000a114504645443c07a46140b4030100b0405109007070b031441c00201551012401c9003050b00e081c2c2d4031105111688026568065480401032400000340b000e03854809069070700b5a5000d0119a8998100100f64400e900c0002c064001d81c403510b0022507884107000700f995543e8900407850603e4200040c503280e80c20b0300042555003003c0ea00407400012044051074980850342101e0400345068000b4500d4001c0258103070450717800f04510001c00405030710803403041d0f9100351405101e20b95 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 28579771 1250 28578521 28578533
    0xc071a070c0302060603070b04030f080f2b0c020705211005091006081504030e030d02010209010e0307080a02060c0f030406030603020a0909150f02040906090506090f1003120912 78
    0x107078400550150040b500441c08504003c501001602c260400a07031615185075038489039403501c1c2d00166901d40091000411024088001b44240800000c209010500784188100544001e2003660034003458001c843c1005c0b074001c101071007210300c126603040c00c4d01c0800340649040c003102d442c1c1e0b012034025100320303020008060b440709000d44d00d20000c48030b910111080c4c80003203503c41d006510040c0d00080070941082003100c08564858403030301c0c1984c029074405000c070b40381046c14040140503035004104502c480d42c0c40003080700c84102c00c5008252092510071031355100d00344090064000c80c1c0c00240c0c008d030340c202044816081035803441181c4e50380342c0d00d28005000300a1804101c0c814a00010b0000b0090258000c1084240d0008003001502c510b8001c1c1c1c8005010015050010f1a000e00000540c9021845010001c01e071044001c0313824a0008100540104000d19160ba1211807a00340004070000d42c0204054aa0140264503444c00d40c100a4481ca0300c01d07030114030084407160310b1a08101e0 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 28581021 1250 28579771 28579787
    0x609050a0302010c080f0408030601030f0f0618090809040e1507020609060a06080d03091506081b0a030b010621051807080f1914030703050c060705040308030c071a07 73
    0x1010381d0003008604d520003811a04210181c03550f103115110a0701090100d8890f0000b55080481410300250000400d4440746c00e80b0001d0028007403895441c1010409130746903801001001283c07400070040c0c1d86880c2c0e60000d060141c01d01803030141d992044c554031218010860341d1140745080d07080303007080c5c43e120340c0003940e8142c100c5020b0f0003030042501140458105002c1c07801034031031143c090580010440c40403801019004002c1c0c0700481811044420b4150380e116031000703041fa40e0301400700640003980030300241c0744a0402034080e0002070300c01c1020850345c0c041d0505540c0a480d0a0080983c2d220705010ba111861041014251030030060260b0440d0a52100c03843c0f90030682501d206540e90680340761140303205000c200841d0882200700300b00b180030612811160b8404c031001407009142c2c4036044d107103800010301240803600000714005c40e030204120720b039070101040c50018606410355451a8071030001030401041c0007804580e000c20481107480a00d41c51000907148070540c070b42036000a007005 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 28582271 1250 28581021 28581023
    0x31504060b0c0706020303100302010c02190f0501110309030a0f06060929030a050c010e0111010c020303100f050105041206020c060a021804060e0106050a0210020c07050a0e060d02060c07030609050a 87
    0x2105110002903013600110a480c400c500401d14000518070391380044da806070802d80f00300d80c8181c501c0b005d501c00080c003944007800340451020410120741028005410401c080c8035158950340309101c1d880d119640003803070101899110b0340d40c1e0000c1103180342c0032020340400d070441c80f0502e080c000c0e440e6044c0c500e041d0000c0d90010900e0300021084107a410f05071030320b4186102030100e4024060403503a550064840d2201c0d0181803414040e01c1403103210316821608050720303440c016040001400b0842229052040203051b241e0080b0721018a00700000c4c1c0144554071802c4480c105c101c0c0358609104017541601c120811000551b00c01d440c0c031040020095001c0c10518455651550341d090f0141014454107080c1e0b1061451400d140c0d0070580c06981581100e88000114866004c94540502540c0082d11400344804001c1c1901400c100421071041c46a8201074181030b000c204000702580e81e804c64070f85540d0142d9410b41c6d02c210780c810300e504002d00c0b5003002d005075092000a5040003400500c180040d = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 28583521 1250 28582271 28582273
    0xf02091302090904030e010e04051f0602032809080303040501050402120a080304110406120b0907060305240126040c0803040303020a03030221090102030a0501090c050f031504060b0c 80
    0x260903040080b03020340d180c0d00780c00c81482d000040010340903043d401d41c500300506003160040e01036400542600c4044400c00100b10400800c1c06000c00ba0062070360107840036002840c00c02e2a5030086690b034030344000010800d40207414039949440d0291406002a040500642e5900e1a15003000c2d4040d02007914202d0241a00c0c200340756140d0130210300300e604e055001b800c00745076031500e49817040400700c01c0f014540e000703564050019102ca00d8000c1c0080030f0b8400c40306120b851500480780f43c1072102552000041c582041c0403c51002800d102005c0302a10b00c240c0e01090300c4a00700121001000b00741d158010283c180700e00c51581c8000e10714503120368841d980403d10b042e10342d1120350b241e00480c48014090f030b0014081d040024083d40190411400c1c3c21000c02c03021050303c0b14102c2d2100c040c0c0b4800c0f40303a507001082c00840d003003e01805015101e8a0002e20070109404802821803040b003280e118a5400400415864103100a240012000041041c00740340d4403100010090740c0401260911 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 28584771 1250 28583521 28583539
    0x60603100b010504030201180801050103050d030c080403090e040f050304080708070506070305091203090306070816020d0e040e0705060304050312070c0201080a020a03020c06090d0f0c0f060c120f0209 88
    0x40902034000c012101034183d41d01c81c1403d2451b0700640340d407111101403101e280654440491405005d105090007540070b41c00030520703100407107000b800300c804980c41030302048488030403c8003290300403035400115805c0d07490190603543c8906180246040380c4000416038000001d002400702c60028890017611a54829900d41d1580c8200304041480780c11402000f00b00140241085031a103030300341402c0229001c0c25030b4034101d05000003a090500071100f02c03000c5600c01c2c0903c62254101540107400c0700e007900040041d082d403404003030900c0207000b820a01c16034443d03a94107980d0070140042e00c01080040c081c2a00d80c18285041c9440340c22282d51058801109070010b0040c0d8415418681c1c0c05406844458007516054070304406980000e00d07e1080c56000c0140b4150135204011882c0b1480e00b200140c1105516241c0007048085c810040d802040b0b4043d03110000700311155a5044015030043c400101d1854004d81071f81e0012003601d003c5810b074a00070b001e0306403a440350000c0c00075880403200014 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 28586021 1250 28584771 28584793
    0xa0b0111010212060609130f1401050405070206010e0c07020901080304090507090b070215070b04030c06060522020c1507020303070e040501031a040507090204030606030506010e161407021002060603 87
    0x4200d0054907003107841810060f000c1161424407200600c00410003a104007001c11600380310b0016581560960200150745985400041840310301c802e01601c0215401d11250903c00c000039030b40d80c01030248550075020b840c003051580fa40c50044943c07040c0d00dc1c049042a69690b00c0050b00c98000c0d200c0c8182c1c041c201400a010244583c40d41800d4075428440e85042045a400f8084400c0c4e00032100100d0b03000410008010902108466201c1d5202c1d80d10f1003001c401ca403070034106441c0740b40e20190041e003081d03901507110f009110781c64404407200b850050f210345c2c49203049072910100c1460081d50b840154140316005502000442c8079015503116107500049200a01c000c50300248405060013800700d00800905071902c2c020381d00607000384200c40a8940300c84a0000f268810360048442030341e500410000c10205014141c01003102c03410101c501d01d85211105884031581800008100487c0701000c0341d0f4031104240d9995a070081c00e10f82c5000103082001c2e6580c08103550062183c840c05524074 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 28587271 1250 28586021 28586023
    0x30f110304120207030302190305071406071106010b0703050c1c0f0320040627081509010902060f070302010906020706020a081003020114090301061503090b0f010f0302060f0904050a0b0111 83
    0x74017140e034150300030b04d1041d6a10208000c801d4075203204130700b08141008410041916807261510590707a03117010301414244075030041c20202d241900703072000344c100d071004000400200003a0380b140c3d81c2600300070b0764404528961508200c0f0320755441c0490441d41041c0c0740c0381944902088914000c2e40c0382040007000d545581404800c0b04201900360420400007130004500c00e0000781707552072800c0d00107400000a92030310001c4d035169030440320351540718120645001000401c2581c2141c40b810003003001da036258011070041c0c890842c54030440640013480b0020076101358080b066842e00b0503c115103803501c520786400031707521441070340b400607400700042040e40640003180c034101d990584600326441f1413000b64203420f40180803403c1d4917550b5001c001940c3c0b000800d041440303070120350b0001034061312803a21281d0818040c003100310b060240302c01402034170541b400480581e5012103081d52240e21040d05015030b842075000d919005801d0105000003071040d0f0700908500002600d0780108501e10341055 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 28588521 1250 28587271 28587283
    0xf040215040f0b09030109140616051207110a080d021801020c0f090a06180e07060c03020d03020f0f120f0105060a050d0518030712090501030e0a0210030f1103041202 73
    0x90600c0d40d070b40820120074210024441c418000d0004900e034032a648810181030820f8070740c0c070a180c01241c104540613616071002000d0301d00c40d090050500b60650202080b5940007071140c4240000d81d42c0348400c0302c01c1080070360041603100404030743d9624800804030194002010a140c00c05080c0c0c124142c542c0081203402c18140094169140c00e06120200102c19001500000703000b50703682400300e01c02126481009803504507150100303942c42907901d114038207807859200408110514041c0c1000941c01b00c0c001d2000c0c03515141c0540c0310a0000355588452082c4011641140c1d400107030f0070818040407200d81d100303c000d01801c9019a0380c03101801014400c941e54200051400c00c1801c2d5400320035400503070080260401207541c40740042c0c0d11441c55005c02400e4981115a01045c1c00c1141d12282400240200b031906100d0401e040e42425911400044002c0c851243e03a03c1031015148682d00290a06e11003606c10b008030240300240c650690310545094501c20a1000f106c000c440c000521 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 28589771 1250 28588521 28588529
    0x40b0f0906041e1802090108010501030206030109020703051308010c02010c0203180402030405030c010c05040306050603070501120e01150b0904060b040b0301051002010f0606030614090108072304050f04021504 92
    0xc0305010399110000c0100609000c00d12105070b0110b840183e04858040c4500d00d03140807400b00d1074000f040d0398010441c0000d0164440e20300c0368180401480103031100c03010303070741100c2c400d800c00350f2243c3c0140384c10f0702c46010341041384040e240e400000081a0005401112400005800800c04a014400226128411b8020844110301c0c610314048550510341d00550307001d80100107480c1000e01041c0004c0c25183c05941010010310042004e00c280f201c0b603c54a900700400724000c001e6a840c04001030445180c0d03114071407003265070301616a5507000a401c00356401446800f202c43c0755480d0240100131b90801c16080340224904640803400070440012641a20580320143d415a07192808220469036003805030411175480d20280c07544800750b4001e4202419075603c2c041003103402c00c01c0300600d40e040141e80364811290340c001008496808100710007901c408440c0e0888244482d0106a030000c1e014083c02d0f0000d141104000c9051a406241c41c001c510071103080c0039110034480d0f04030440c001c2c0d0207 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 28591021 1250 28589771 28589779
    0xf07020706050d020f030109090b0703090f060b120d02030c2802040b0a03060603080d050717010e06030a02090a0f06080a08031512011b0809030705120c03040f0f05040b0f 75
    0xc14070041c0c0c0100060a0005040c540141c0341c8041c003615507141d904280c1c41040c4094540b0692420010304000d01d5a018034103107010050700b070301c50b2140b01e0039080594014003569554a500410380d2034649004960a90800c210307010799040780e00081d502d6202e4204455603000d000c41122041e081000c1c480f40d10021480098a404100d400700300c010929001d4495003c00440e43c003b000640d14020300b0005c43c05004815200c407141c0b00d0690035508020988400c000d080c0c000200704501350b90750107054a414252000b141c1e981e0038003003494201c2c2140007a5020b80110f0800008004036000366681e801a032400344a1203684410b082c0c2e403013070003000003000b044082c80001e1400488032031406000e0b0f0300902d015150b00320303908010300315540e07003003954007480410b10711a010780d0704521000c2e000f81c160b03401140740482549031a6200e0000d808a60f08803000040c411501e88420401d88001d40b101c105012529903940e400c541000700d1034464a40268100210080c41d4600680d42203641040a0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 28592271 1250 28591021 28591033
    0x20c010e010c0b15030d03090215030708040b1b07060204050a060509010507031803140d03051b04030b040206070501020406091706070801121703100603110309031605030408011802090f0702 83
    0x15554080301d07080140301c0328134481e201059007195541005034590091340d41d24005404c01c04d03801800240741d4110641c00079120200240012668070080c010740c015040354068040f503c900000b400b4200280d001100c2d0100007080b001c0c10710066500400465600f110140070742030303603084161034901803c102c0501103002840020003190141ca0850f850a00030404504c2032900c980c0c408044a406aa440b20507030300c00c02c80156a20780611034aca4018085282001a00b00001c588042038402c600004155030024070204d8215110102503c6940c1c5d88000299215034a6820060140e507003407040842814844401d01308180021443c203019080765900c00800340c0c280b2602000785030100a044070400e402005002c035104210300694007420106810224043c079280000b0151034200746034201c2e001c0d042051003150a00042180c003004c401e07468440a5070100c0c14034030b056004d81e50101c030803542001e40e8480d901c411241a922082d10840700280c00d500c036440645c04600e001c440117000350307102c0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 28593521 1250 28592271 28592273
    0x91e05150c0f060a0f0b09060a05010c030c0b0f07091401050a0809100c02030c0705031b150403050a050601030b070315060503060411040e04050d020a030c020105030a0e01051303020c010e010c 84
    0x48001004114806000c585078040b6420000d031030580201c41309007001c1d40d520007606400c0540d0141c6c0040020446002050342801400125200491300c9124103008202c01c51404141c0180001d481194002007500c07854039003c1c4410360400003c0b90100c0c0020158200850b2007200210486138088069481e24100320070650103641c40440601003120500c201c01010340f0907003150090074104690344d0f01440e1242000c110031480c225041d040188290045c444e50088040c001404002021781280d42152403d4411601c7d61240700b00d8002a00e5030007951140d0703080c40f4000420b0380c100c9120703800b200025036698800b24101c4480300c100e04603039000b102d0200a541d11800141da04040300030030002e6901202040324009a01581c015804c080c00501044280001441301c40344008003070010700310b0705240c2c0c2d4000b05826041c910081c14002c000c004243c0d00e0a01d54002288415404000c12039801c0281d0038016038403450308118010700c40c003041d404803075110741d110141080c010b071180d5090703200d2 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 28594771 1250 28593521 28593559
    0x4080702091b030405100c02030406050712030605030708010c0f0c020303031602010b100e03060906100603050408040302040903020102091912031d0307060f03060e070c030e030a020907091e05 84
    0x282c104031a80044400e460300c42030306900210700030b61040f4003c1840840c99202c0001f56015102401c09540041c041000300d01d400c1822280c3c0b80f584441c02c943c0e500b00d159002d40050256030490343c0c240c4540c11020030070325415400a0000a01034440000e030311068a402c4610004120700250141c000740003081c44040d0744640c4683c164405e00010031035068400c003041d4510000a0316400041800802d26000c3c00e05101040c4c000d440703c40a00724902c0d110305424840c11a82c03046200305581c9400041c1400b0004040c0c601440c0d005200b400395036280c4c00c0081c041c0d08120415272007041c00b041c603c3c807815441c4083c0021507101c0b141c844089071007500c003680c0d072a080c84000d600b11888660081031655003801031a010b0001c035180c4039950f1424210003011241d003604896602a050014010b5607900584084040d03941440d10100c54010040841d0804040c1000290443d03590014010410782144440007a17500261000d4411013545807518081d40035840b8030f0390005035a66803844035001c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 28596021 1250 28594771 28594789
    0x50a0509041d01090c0512060402150c01020427060303090909060209132702030606060309012309010b010201020906220b070b0402010905090402031f0e0a080909010b0304080702 78
    0x50024000180c80c41e0300d46000d01e448148402c03046040e5541d502d1a030402c41000c5000340546000d585440c58042001c0e03c1550303030030015002910801c21952801c1c05001c0b500e00f00c5501d240108000e541b84c1e9542e0712008080144580c21459241000711035030220441c0d4450320302146d070117907503203d1031034605400c04004207105c280079100281c080004100644881c1c1480c140800030b5a00010031454402e0321010900d03c4030b44070740203071500c00c01e5480541d0b40010742a030858012141c00395a0b4a440b500c079030040c2000154400300000d03038418428000070032003105200b0b0140d003000303110550080700128202c1c424221034990100d018002003090750320940c2520b603581103254040104644078200e01504c1c0c1c004000480f0250448000c0001f1941d01c8030003c1d00402c0145d4450b50281496400280c444c1d4040c0410014403813040100010750740b1581007001400038080c16030b0b040800c14200340483c2d502c99050107000380b1101f0300000d80426084c4c100d9128940090259051a010340d003005200a = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 28597128 1107 28596021 28596037
    0x80f04060810140603190f060608060d3206090a0c090b01170a021603090801050c030c030106030b010507020405012303070803120901110f030103060b030d050a05 71
    0x4911101150f0912001202c40503241e5540c003d000d01c050780c03101c0000303444c0c41c209522044a1206e85c5e10800980300c1d2941e03085002d81c3c2d910288000c400d02d001c0020001303600700020760040000c00c0b03c015200c1c03800200104200e0b004a208519091098441c00c0171030700050511000c101da100501c000a15600c2001d12030f6006150018002c4160303015206a080480c4000606141a580c1282d5403408000701c19101040c403820002c25803001070103041140e620303107800302d215121400e05691081e611140d820b40b0310b82c2049821005089460503e0381032010a0000d070006940350702a01c0e01900d0074078000c5030404000144590088a100d1134540a9001b00c10140300304a0080222101104441e41c046c0840d01c620280500418503803c484900443c042500c02c0da1042d4003005504990203003070f090261103c000e0405407911f140036000300104600300917501405004078003601c560 = true := by decide +kernel

theorem cover : BRFrame.Cov 28417271 28597128 := by
  have h0 := BRFrame.cov_init 28417271
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28417271 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28417271 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28417271 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28417271 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28417271 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28417271 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28417271 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28417271 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28417271 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28417271 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28417271 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28417271 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28417271 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28417271 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28417271 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28417271 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28417271 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28417271 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28417271 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28417271 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28417271 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28417271 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28417271 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28417271 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28417271 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28417271 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28417271 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28417271 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28417271 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28417271 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28417271 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28417271 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28417271 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28417271 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28417271 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28417271 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28417271 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28417271 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28417271 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28417271 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28417271 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28417271 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28417271 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28417271 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28417271 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28417271 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28417271 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28417271 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28417271 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28417271 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28417271 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28417271 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28417271 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28417271 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28417271 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28417271 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28417271 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28417271 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28417271 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28417271 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28417271 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28417271 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28417271 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28417271 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28417271 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28417271 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28417271 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28417271 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28417271 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28417271 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28417271 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28417271 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28417271 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28417271 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28417271 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28417271 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28417271 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28417271 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28417271 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28417271 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28417271 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28417271 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28417271 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28417271 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28417271 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28417271 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28417271 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28417271 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28417271 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28417271 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28417271 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28417271 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28417271 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28417271 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28417271 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28417271 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28417271 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28417271 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28417271 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28417271 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28417271 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28417271 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28417271 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28417271 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28417271 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28417271 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28417271 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28417271 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28417271 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28417271 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28417271 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28417271 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28417271 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28417271 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28417271 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28417271 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28417271 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28417271 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28417271 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28417271 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28417271 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28417271 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28417271 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28417271 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28417271 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28417271 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28417271 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28417271 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28417271 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28417271 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28417271 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28417271 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28417271 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28417271 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28417271 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28417271 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28417271 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28417271 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28417271 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28417271 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28417271 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28417271 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28417271 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28417271 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 28417271 ≤ n) (h2 : n < 28597128) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
