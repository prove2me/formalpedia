-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0033
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T17:28:48.030572+00:00
-- url     : https://prove2.me/submissions/4b07e353-7337-4cbc-af4a-3b2eae8562e2

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 5755403 ≤ n < 5935259 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 5756653 1250 5755403 5755433
    0x3010c2a03020c0306011d0a0c09061d0a03030302030a110c0a03050702010203040e0708060f01020a02100503060d0b0901050601181203030c110a0c090e030421020105040e070e030c0904 81
    0x4015540e160a040c0d00b80b20180000581600880001181d4003841c5c0142c099041d1850030702c00026030300c0041c41c40443e0100b01411000482200d401c00040b84203d8466024014908074640c5801c00ad10010301252455801240460b40200410100540320f00c5078a460400c2c40341d04ca4a0681d003c030a068540620100050900002081134400e5910070015039014042d8080220158240504083c1018004a440740d100e50b00c48045d8261035440490041000c4e030303001d000000240300c1a1000d5511340c0004061581007107442c81e869001c10380440302e49025280c4080002030b9070610000040c81212001a0002000c0c2e94280400c1000e12405405584030b80514000038100303844042259240c3d03942607444410311550200009115030841c800d4100c4030000c40c10000e1140e01c205241d128000d500c50298200a1000081040b00c01d412215803400e10502d032041c5020346032884580550419a0054000342d01801c1c0c110460a08001610181c3c104480501040ca420b0350b6202c00010160 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 5757903 1250 5756653 5756717
    0x30705060325030501150f0203030a27030c0c0503060105030d0305040201090e090c18070c030302070203010605030102120411010302030f06040b0a030b07050a02010612080f07030210061403010c 85
    0xc0082c00a1820040d4400c40c01d0105100030071100c11854028082c00c000e0003544180700c00d58108420460146c0c1104a082c0c40980285045a0311000110001c0c07a29141d450100c0140444510440500e0f242d07c4101030f101c0c0d140c070000c0070068104410038411030780010b0700075400381005000d1380d40d0003d81d41050708a07614011900e550b4500c0100e94044447c1e219800d54040e44041c00b4500c600440c0700241d20301d0035a86070390384022003100b4001c42e00064a00d40702148a1742051000309200341c004100141c0060000714a240c0e8440c00720b42246e11540c1e00c1c0b0040300c0290f051100300007240079860300341c1001b40307000d504508044200300321307249001d007030140729660790f185070040c84c1c99182031580110740144203802c0d286029113005c2e20503480352183e440154138010001c00c0c01141d52152440054011200c28180000240f42c05502d9022200590039031280c500c60403a60740303a40c01600041c044008094001451300b0b03041c0750940e82828145401e0001390344140402502c403002801c00d9180d21 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 5759153 1250 5757903 5757907
    0xf0305062206060308091801030b13050a0c0803070c060314070809011401060e010906030614060705100204090204030b0f1e0c070206070503041a040f030809010e040f0e070b0903070506 81
    0x3951440c8081a03081c0070091605003010f80c000b050112a002502e484007058a0000f8140040e041610f440d6400740002003207510110042600001c844400c0d400551240c8119240361500e82c03501c4c1d0b403e00841d88848a03a40c40010240c0c10042c0a11440001b04083d0a05200210a05441c048140c8008022a04208070000062801c2009400c0503180c2c50f8440d10740402035031184802070140c0c900c04207549c0401c90000000a80c0f51083c0f145801700d1703072141810654071400c0010412158070600b4103950f54410011022204601071004100800481c24010382d16444d5240005600070001d1240c1c400048120400002640b00c404400f480003261104030500d40e16074071440b809000c1e950020790840004528981000000030042c0103442101c007820741c40c00003091543c0351900c590f00540300c590048000c03c100141003940603042c16081411f1101e68014004046000c941ea00504002e2403031300c80c51984403055003408a40d024010100a1603d0520f603007000c01e650740342a00c03405000f0000 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 5760403 1250 5759153 5759191
    0x7061e030216060e100b0604050607080c0f0d020606010201050a1e0f0e0a03080417030402010210020304020406170a0314090f01050313020a0806040302100504030801090b0102070902190206010f030506 88
    0x2011a10042c0b6500010070420000c960744180e640d64080ea040300e00492900a843c01c551801d08242c0e812a18010105481c0c2269a0345001c0983c212008043d81446025031000d0001001d01130345060342d2043d0f000700b0b454600f5200090035528080c02550200d071400c81c087e050f110142c3d060395980e07a032890f40813400070041140781c0000c4c030b45607051290747c2c0543d441391010141e10a00042c001d5005084441004850032241d1407107100c00c3d40c0003800341e8050b0000a2583d95035030069544180001d000042036665035400081c83e80350f81402d4003c581100d44000101354000c014640c20021450304a0b003440454808140000c072000012410700c04044000b401c074803080c0115a0401c0d60192081840340d80d982c0d402a0b80380b4050780c04038058003c075944440622100e2040520858050380c60410a074031304049200144803004030b11741140226100030807843c0705d60005040102c182c26042c0e808003143e900003410480c040e00306943c0c00c0d01c01c1c0030030000f24a0020b136180d00034000610307412510320 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 5761653 1250 5760403 5760427
    0x150615070c030b01091508030f030103020d06020403050102070807030f03050c040603090c050d030c0309061706040207080c0109050303010512030408031801050712090f06080609010e060301140a0b010207061e0302 93
    0x4840d920060107001c0e41c50001c6075417070440e00a00b602101c22401e0805860300e0764012a168095081210342c907220520042001d07181038500c01800034050180140784c07503181c1c1c03600342c260790103a00c05a810300000038a1404055200d04a9040b5648500c1d0801c41c500304407021141c140f1407403007044100741d100c043c50f9042c0160309090702d00404005140c886410142c3ca00500f08030080d0b1400d81c0030803444100060090b014111085000800160800180e91b4410030030000313402c18001a50212018001c1454410b03003403181200c401d00400065460750f24010403c1004c0828020303c0300b8a400c1444100310b8040000246c03640e688419800000700100500101c800340210480a400c0b182440c036501c0d0b01e50f800800d8441558a0f04610042e501d031212000c0d03c90800c2034550036003020710500100580d010041c11187c002800174008201c041c440304c42c03188038160a848440c0c0851303868200f61040c1da01006240c00038035090422902d161201501401078044202190061580000e14485030b85 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 5762903 1250 5761653 5761673
    0xe07050d0e0a061b09050409110d0303050f071412040614010b0408010f0b0607060b03030d0e010501080c0102060903030411010512040308090120040302040b060d020c060915061507 79
    0x82040c00341085070306100da046030742c0e8100362031043d0358091a03c44070049800080320400c0808000362901c2910610381010700000703011040c1c0030b49081c1c241000000071652134400d00d151803402075501007024100a44169540d82c0d01a04003005d0141a1100c242c040100e44240c03002c00c120101c20345c60707a80e518104440a4032003281d60354440c451a0001161800081c0302900c141e03004d40000f00300c5124403040c040125096440c0c51540000d0070f1055400240154000340540e25001c0c0c1528101501004582c00f80c1d01d42404407a1396035107039001840000e00411a811904074244000c048030301705034141903102c1c807024002400320074807070900560590107007046820f400c0c407101c0e090466203010308000300088415104000f40d5400c1c100b10395414000059481031000b44c2c40842e40c039062559003084010302031034841a801c02005c1c03103000b860606a01c0030302919181c41c0040c2c1421301d404202c0608040d0929200680700500b5418000952601141986015035400307584c0c4e900c00007810002c60718 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 5764153 1250 5762903 5762917
    0x50a062102070803040303050108011104030209100b0301060c0209090706050f03040f0515010302030c010e010f050a020c040903030507170415050601020c0a03140c180f041b0602010204060e0301150e0705 89
    0x30350001030503500304903001c0011440356000360341c100102d90326200340c2c0b0b00342c6440ca0420b620b8103106000a0001d031800d06010343d0498a5400c800c880c17259100e130102d00f00c2d00264041004100c202d8486001d5081a0f1241d50340040c0f1071000d4200c090030301c0006031080c091100180d141840200c005010400025002e100068010301181d4100c030103100c002102c1c8009000c00c074028010081110055401140b4041c07040c1016111981000ca0845007290031b504024a40d40440c03088058110303041d1a01e200f9009000c1c001d0307501244c10b00c0d03d03803009040040000f856460380c503025010003000c600c54400c07600c0441c00b64040814a0345441004070f1a0030030000115500c005030100000401c070401c8202401d00c0a100152118210b424041120751410000d0103ca0020a4400140045c02c49182d09134054800c4440f03c1c050301400c2e04145441303031140c000d040981e500046c24046544c00040c01245135004800a0080c40c610f20001840703d0401d1040e80d001030190341c00314003400d0040041d03502e2 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 5765403 1250 5764153 5764217
    0x20d0803190c020316021002010902090c0c1903020304030b040c03140604110102030a02100c0903050a0b01090b060c0a0b06010905060d050406050f061e0105040e0117070906050a06 79
    0x6a00705001500740520350452948030780e0b4949100c1c4612940007000351601166071050303451804a05400b4000110400c04410007155170318050704006a80303690007540280b9100040035140d83c08003180510301914214001030203589203074200e0000358000221800d49078428085409a01c851402c0d890981054000504080300e00310100c18039800003034260700c282c0c09038120128847c092001a42c89200c0c1113940c20040e001545040c51110488e04900000c0d0b0701403910075445952500d035a824400000407c0b80d00100a2004102c40c5006024915454000701d030300e1403034802c200066558031102e09000130315411101c0c0004070540e0107681c4a4009041c094400b95494050490030002003400b22740841d50310346004081000003080d4941c1c0d901c00c0401800c0c00d030403402c500c092006943c01c8a21400d04002c1e04010104120070400d01c3c90b0f00038003090f182030000b14681050780e4107010198000000303062401c1c03001c0129a5074003088034101c1e282424480d82c0c60134244040424600c61450500c0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 5766653 1250 5765403 5765407
    0x80a02011104090b0301060929030a0203030c06150306130303050718121509050601030201080406090807031d01030915020903010204030501140618010e01090509030c06040c0801140903030a09020d08 87
    0x80c1450103404c1000e078104214000c20016464010b0a01200c840c2d00c2d803103080102c80503803903010360b00030010805024001401c441607506180e0000745036500c2842441c0181c2c220310117014140b24645070b00c8114850450203071071145071208288054900c0224040d08141e100e50210f401c450040050700380900c2d003460211400c1c1d0311602c17020042c0314000011240843c40700203180107201d8521071481d4403070307218014101c40e9187d0707001103c3d5804041d0055800c503607034090090009007010000d1000c0c0d8403036140e0841c210a00b140141800240c032100c1c605050400003018005140c103219840240482d4400607241c0f440200440d0080c000da40005020750300c0e00300088070940c8540d552034811642101d020458a40c00107820741404001c0c403c3e0042a4511030043c42004201d800c11603010b00305000720390030400e03035601c0207240c400241d405032140319500700e040c0140c0344203000f00e09818141000c0422030342040720910b076903440001c208503a01aa245c0b86c220440d41d4850300c1d40e1003507070401481e03030b = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 5767903 1250 5766653 5766659
    0xb06011209140d020d031a19091404020a06030e0706180e01030501020c060108070608010b030604090503070f030f020309010801140a08030d02040510080106021b031f0b09060a0f03080a02011104 85
    0x40d925a00040c2c0100035116140380001e42c540301e030040503460566840901c0120081e0b605000c3d0034403000f48c00c0d4810000704070000c03d50054900c80c1c1d42d44284004c8090b1101d04050050000c074004680281e0100b60515240008604002840d04100e0344985030095480c88419460900a0400d030000c0f9002812040000280320054001e00030200348101074520690340d40a46950b914030a100d5140800c03281001004403d1212010751b90201d000780001c01c1a0781c0543c0c415003181e1000d078080301c0f5980c2003c1c4180c14958406102e15022000380000e502c0e041441002804005051107440c2400300034621258854a601a5000060403850102c1c1d4442503480c02600180d00300740181030148070754480f038810582c49802c2c0541240c5040d0040c1c07102d01c0c2c052441034800d041a41c0055094860b0b1201046040300d40a8008020258000000340b070302c183d0400c02661001c003a00c5d180c032602c040141449594402142507040301d034030001c215074840340b0b00000d07409812940300107418080081400 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 5769153 1250 5767903 5767943
    0xc17151306030b10080a0303020a0c06020a1701060509030318030109020d03080f06060301030b060f040b06030109020403030e03010e1504050715052a0d05070507080102070f020a0605070b06011209 86
    0xa032807040140010300d6841d010104031044c12403003040800d070310111b00d610206c1d009500406000d0b0b8580b410645280050720741c01d0507a440a0100000240030982034040d203072001006901502d8241b80051074022407a00203039690084d00f030f00d018940e5442c4400b615580e025404081c2d40381d800340a1148000f00c07810041c1c105030701269034511a903002000114940703008422207040e294402140d0380543c69640c28090314510035041c0b55005641c400c66011705a136641d01031030003031010360400769445040d468000c000b20b19550005000e80e040015400c140d44000c035a180800d185014001c03142d60b070354148103141c803040340d00041b03181d003242c49405041a40000200728a00c032a14022400c1c126025804040e50090340343c200c070a8001c3d00044880034450801055600c3c0250203e03102e10380c603843000038220780c03024804541c0d018a404403c411800c02d440380d540100b0050501d0b0342046211749442449180081c8840c1c1007084002000500c011141d00000c1547c2d04130f4201000c0c11003070452 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 5770403 1250 5769153 5769161
    0x10504050a0e060307060c0b0f060102030702210f030f030103030c15020705011a030d0906050307020a050106090b1801030506070c021f02010c020615030c040213080a08040f090c171513 81
    0x107244c06802040e5011444074090300b010741c00303140e003c1c081112683d00da004c85121088040d1400341140010080040980d942d070701e10040444080b0a101d908200f44401a4a4161001d861081c0d0b5041400320401e40d026032000d43e411203415040401002100745040b0b84107094112042c02410b10201e807100c1444015849181c80f001d0006040c0c3e980b04003581010754505140d8032650010b110301401b40841c600c940f01a681042c441d0040303682201113030340c91500b9a44550082d00c42166200d049804030714058540c450040303002e042100465040d900c9070741d15110005c00382070030321100611000c115114a0300900150b10b04a403003209081e4902e1f0700078041c1c11030f003140700010b22584010a49402d10101c3e0304540071401002881850340b00d0003800082d410009106250b2440c0343e500080c2c40d102484800b41441c23062900b01d90b034504004820766402410b8000007015803901482860654200d000c0c5840c3c8419048680784aa40712041102015459203215400580200301044a22041c3e04 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 5771653 1250 5770403 5770411
    0x203040b010605070809010c080d141905070906030c0207030204020307020303072003120a0b0409032006010f090e0c0a090605040b090601050a0507030c08030115030b03070305030406030b010504050a0e 88
    0x18a0240300c0c1d0340c48100f181e050182d08000b40007100c00b0403001d05203600510b081e4041d070b0f201e001000d080482000c81c40c41210308403080f26041113646801c22902a940b1280c0381c1c000741070203108100a040610008010500034080d45003850f0fa5a00b048034054000c00614000710f9004006664902c1c3c81c0300002e44942080d58041c010840c020706121441c2103070000340d28650340d4140198113250141141400d01c0c100178000d40c00302560340700b400039162101d0045035203842c02501c40b0040350f4084542244020030741181c003110343d04120014401003410140c02d004490124034080f800341c000290311803d0602c0890010b60121401400107081c0f8065080142243c0d402c840c1008000c0101c0280054034008542d4540020401c019210503540104042d0503d00d001e450a000d450030703150b55440540d4803e0b00a4061050b121403000c103000e41c18001d4802440080d005400744c076265903201d554038000d0703014101c20300d034075910784c40916480385040d90010074000308202107a5984090300301941e64155 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 5772903 1250 5771653 5771663
    0x304030b04200d0206090607020d0510050105180906070e040e010606080105010f02010207050307080310030501020a0302030604061203090302060a030209090103060209010906021209040f1b02070503010507021f020901020a080c01020304 103
    0xba020071660b18090703038203043c4150050643e07407070500700c03204105c1079900940f03080341d101840c0c0d0110b00200d03d00704030010b6030300248400007440303504000820481c44130415074002d1020b90f540412900030707800305416400501da07040c1140544c252a0000d400341400246c5207045600e0b1000c0040d240d9401035070f080c1262404c0c1c95001d070400300b6030302c00c074203034070401e90003170310b240d01c200304600000703810200a6a00041a81c0c41c034801c15120b9641c1400c1e039108816420009401206105032450a40301d01030052281040c511440c200940e0301410b5002c0c1480040d1140102058101155000e03404881c420840104071410325a180e14000c4001d41010fa40c160004042081c0800c046000181525507900404900d9041069090030400500704881440015540390312208000742d62103024003412150980241003600c0c20300301811700b1544001d20f401c0846d40100181407003044411011801450203890240c0d0350410b001c0181e00d04000030400a05583e40065181d2000806601540c040ca101d4 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 5774153 1250 5772903 5772953
    0x1090501020106030302071404020c030d0b0f0a030f02010806060904090b01030605100b0418110703080405010e060c0d0209030f07030302101a0604050f03071e03020103061502070e090304030b04 85
    0x16000482c2210403a00008001d41e0111500340408101d845011802c90030040000d450032840c00d07842400d5030024810f54200d140c95040c1c4108034074010f90031256107a400c0e6008081f86141d5110340c40ca0185003440a4148105140402c11a8030343d441258141000504103021800203490f010390038020901c001c1d10241e01c1c00010860180b50b444003202200c00c04000503003400d050440c4e1182030311301c40c1e2002212964404207141c042d050301c000703002c0d1107001e5210019240742904140742501c0380c0d02001c207001d0f0000c10800c81c1154000050303540000c210b0340016141c50304680403a28013845420b81c96860700c0758907000810181d001410b0041d18460050038080201e44013141c0504081950990b54001000e100c18800c0e8108041041e041c1c0740700074100c44904d59104003a80315480007003070a1541002c1c03108280250358060103854010409060340160610305404000e44a89440c010310740c030240c007040410305410040080e078018540000800300d03d800c1500d44080742e0720484c1281c2e80c0500359 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 5775403 1250 5774153 5774159
    0x70204050603011a06210f011503150b0d1103010801020a0f02010905070e09150907140105030129040b031003030305060906090c0d090c090c0801170c040207210e0109 73
    0x3041c001c00c100f02040011003880306402c03008000b0160405540c00148440107510244500c1c01142c6c4180140e01022640e5010f5042c02440e001588007000c07001c041c11b08004500d00140c50800024003100c0d401c5880c9070700c4400e8411820301510f5200000c40c081c000c0031001140651043d8000c241005454880d03441005545a09074240c8000c0c0a020700f0320340050100f00400e040c070b503446503805109542521080d002d903441c0d01da080c40003520550460b5106800521200b00c445400646c04502420054115890300d443c13044000c0032562001c03010064001d0304140c95801e02c0540c0c2c09004403032401c54072440c0000d40341c01e110140e44815000070381080c0100750603080c4000c0c5280541c0d40500244001d564924018980d9401108840b50041da210314a20100c1c40e40313410007019155084001c294044054001405400181c04c40054040b25070007445c1009800121407800c14001d407005602c416090902059281072800c0141804a032420309001c825440385481208100c01d0701d0700030300340391 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 5776653 1250 5775403 5775409
    0xb0a0e0c13150f0f06030506300d02010605150f0c060a0b0a090c0503040f110303040303020105010f0605030c04030b07090f030501090302010501090b18060d0204020705030316020d0807030c030b090c0702040506 92
    0x20f180310700000c0c41c45038003061080c0c40c1b094100d40e07405400541031114540a862650390b0400c1c0c11064144038846211000002d07040a22441d10104460f1000f4054141803100107004e65020907075001c80c2804c001006005900c0710b030300307803203200704803400390f40d441e05c1c00c401418050603201a071103200d1517580c0000b20701030310315200d0110308112a6481500b0356442d6680c42070740a200300015202c1c0c07600100128103d0340c040000300f0295100b079001007a0b5501d84180321300940e9064000c403050140c10710403c40000b55000a88044a402c5450030f4025184c030501a140d00c101500203440f100a031100c0803060101c150081010741d442a4000c0100e03a0340c840c2000200c170000c3d500d050b40203540b626501c00c8169170f135080580001d801000c0740d6408069500003001c0f68030442085980342c101008202580c401c180b0700520301880c41c00500424100385400800d0a00c0080c1038400381a518002035949510030f5008902002d4003426031801414582c1180030282c00c20307a0101e11480c00c0c0340c0043d203941 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 5777903 1250 5776653 5776679
    0x6060503040809060c070b04090c020c04110a0c03030e0a080403030206060901050901120816050f070f15050d090501110309010b060f0d020903030c06010f030210020105040b0a0e0c1315 81
    0x141c0c0014606060180c01002c026143e4440c5d19500b0842c801c803071021450250300c0c4014401070a244400250040359050b010b41498001d042d0544101d14242c04000d003460715004403007600d07066140c20200301109103020b400401d100240140688180700f036205c20030014000800941e03020f5000c955041d0348403410010940350901840ba08a904c2500400242c020306000c203108034400e41c46d09050202c0746903117290b40569070f0300c20b07110743d0300c98102e0b200803002c10b0120001510141c0e081010f0700c1d09000455104008502d446410010000b43c01e1103c12002d80c8200000b030352100c024001170036001c2c0441010b41040d200d910041d4a130080844407854041c0c2224416505004104d080a0314810f61900075046201a582c15000410203690b1000003840000d02030004098400340160031801070103031808840c00d8140540e854070042c4008504070b10745280e8031400c19000490381a070072400d0141000d242d0048660494108101030341e010240350007450314110102450350302943c1d0303444115102 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 5779153 1250 5777903 5777911
    0xd090b070908010e070603020c0c03010911040e0a05061303140d15050102030a021e01060302090109140a0b060d0c090503030a080a0506040605090705070204090206160605071e0804050114070206040606060503 91
    0x19505c180400c10140703000343c01030526061800c0039150142070703101c0800d09441c440702048842c0000300844041c94540751081d190320809843c000c04145100742c1c1c90b0340c1c2e1900080c0c0103a03c140c41840028040500c201300c1c500344d4151100c0c1c005d803500c01a01032348014022515807410403000c5010301182c59480082640c003001c04581c0100401000290b000e09917101109600c3c007103540340c00c40030000d40c49140c2d1190003403028003000144000740e0140e080ca071036400350020103c18182200701045a8410003a1101400460381c00580e118403a44195231700000783d0f224a40500000c0b419011403600401d110744100d01900c018401c4ea034888041100310346032401680d5000d401040800d142c24403860261440d584060000208038210350001607098006440080d0741e550308001a00802005000c2d40b90032400740c0c1001c08449140c0b2600301503030b071702c10b885000030448064006000c0c0102500044210282040c82c003401d41425a0000e44406003101d00f82c40e51800d0200000d101403040b8202d13441 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 5780403 1250 5779153 5779181
    0x8180c010c031409060a020307030306090204050105030610120c2c030d1b061109030115030c1502030d0203090106080d0c0302120a020a12030203060f06130302040c050d090b07090801 80
    0x744a55606071406a189101c041c8805024000d03607020b034aa032002032281c0b1400c2d8004513100e2000c2e207001803d440080d04010507440c01031000f0440e9981010940344c002900300d0f000f010f041510320f0103c9007030071601c0390100d031182000c003050152500141c0311041e0040303140c00f008070342411504520344060000d1225415900c007408442040d0b108541514809901912090b86143d00392550300580310721202c800909003000400b145689003d20031690001c401800e1b900085256403030b941c414964621484020b9401d603400424918400d10071a03d00003041c540c01c41d12410003500d028024032607070003071103054800c0c4221407002900814032604521780c56402482e1400042410510a410960002c0b05510545010303000103002c06031481d05129140e0b40040c0c5901e004010880d0350a51040c041340682400c110f207005d0310114a400c0001d0380d0f0180e030301054800201d042119184a003400110f02c5030300d000c0e104c1003000300709034400f400f8070b096542d140465611410b180b82240e0300c208000c25 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 5781653 1250 5780403 5780417
    0x9010e04080705070e0108060114100c0201030b0d0614040203010b060309030423090405010c0305070504030c09020a180303020f060c030708060d02040608030d0605030118030206010308091306030308180c01 90
    0x40001e0039080280b120034840c809650740039644140e0710910702c20030b802c9130003103030041c00041c086924034030700e040c15040e030885a4021304001800701402103540050044d041640342c0c1040c1d02151180c054030681d4690000c810800050603103a003200d0340c00c00b658100d100e5404d1003142c000c0c0c1d2600b4010789019440c141d001c0d524240c035002c0b044050418004c001ea1081680c80c03240be031b041d40c56020300740c400c40c000d80011404510303142004088402c01001c65040c0a0140800d1020626001d900b100791500c2c1840180c1d1030b41038003001d507000e8008030620f44a110b0403220103c10551f0129228251100e244c0c22544140c94030b209001035030204480f0700380090704200c00914240b9044044440c191300240c000500c450702e4510300e80c295401401880c1c1c0550325524100300d40e007824072800140850b903100540e07080b94030341c0e0029200c1c031040c80003030300000307002c5a100c8090761651604c020380c4140d054100078250b941c2c034000d0446001120702c60003c1d4010340c0c91071443d00c408110207450801c1650b65003 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 5782903 1250 5781653 5781661
    0x6090105090f13170304030e03120a11030702060a020d080709050f060706090b0108010605010908060106050306011d0402030106030504031206030519030309060c08190b0a05010509010c050115080c09010e 89
    0x1001a10001c3c22202ca0203051a140408a0012a0b00030fa00d01250800301d40d43c0e01e01424060030290008501c103000741e0114200411030010742041c1e0b44441e0191401c0c81c00000952142c520b9806841d00c003940c0001c0000f070311b0356920740001d88129001c00310740b10461140c2d6051030a0310714001d41e2107000c2e00561405e907034402c00c1c5041c0b401041c10354425200000c585a5585414a0300b1809030401d802d0baa540d00807d000715030b0841450401442c2580c01018070b981002401051408040c1441c0d05202409031642c030901081c03001c0c10090306001d04215182d41e902c03200207019210698080c0c02051255100e10001d00703c0307010f510160b903040300007420043c107554500140d0380d400759010b40030150b03501d4580c40050541d0141d684d582003207648590060a02513171008003224034607020007500d450001c0040280d01c41e1503030707030080b81c1c82401c08a0f100c00c2c1c8100103903200c0c010355600a059528100e040d1040084c1691443c040c0c0c2d61910450b6030f0040c00b4010b0040194080c0581504520000c0000d = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 5784153 1250 5782903 5782921
    0x105010f090b03150103060203070e060309070e0c07060f050609070e090606090d08310e01050d02060c06091605010306030c091107020901080d020d03090f0209100803040305030c060609010509 84
    0x404110b60190031030b002c0381c40f0f00100c441d5821003a00308079030550b000010700084a610482d07596135000d04565503031840c1000c02c01d50355102e045201d14909510301000180c001c1081038251860745400100500c4820b100f0b103100070091a08658040c4114151000f2840143c422004454081009410b040483d04d6007001c00c42c2e5508a01840e560019030700c0034420001d440782c000341c40080c181107601050300540705003080b00d0701ca6840c04001c50380c0305010100416950304405a04440b810344031081035030701030700114130580b003004840740e0305120311000d002c2881c8002419aa8024440502c07010003a120f000440a5602c03621010701004403810080c0211903050780030381190f0030003820315841d10450380d02081e6003001c2644407020942007503500380d40041d014010252400074624041103007207215a00c040c00d2105134030001e03010300c1c600c1c4002454a00402e4000340a000b8410450b41c581c1ea4078034200382d4030340c0114060059800381c0b5001c5aa1800e000c01007a041c0e81006280703402d1541c1d040c280d = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 5785403 1250 5784153 5784161
    0xc07080706050604061502011e150b071716030206010501080c0409050903040e01030c030b0108061b030703060f170111040807050607030e0a03030908010b0906010815030a021206010303110105010f09 87
    0x150390313000d41d840c075000640351512411540130f00450b0700041590245106204000080c01808603510360034000c00741d02c0084d4140c0c085d03056608180c0700b26205c041d58140340d052074038241c1101481300c100084034900301d1883c80103841c00303030b119900310384890780c88500441b03040c941038500c03000d440000d200034090110a9042036501c4418001224205644c410106514400c20b90058812260840040c405d10a11804082c01343c00f8040041400c0d01f4005a20014004003000080700780d40044003080501d88a43c100d10001c03e04401d20b110910388611000e9007502440c21415070940c0b912444035065100e060070f40d01141c290314007901d001e03860002885a507500250085041120700202203801d0703950180c44402450181c0d642031052410040c5003400c490950344e0440c82003000c8400c00450380c0c0c1c03000d10300382d00011640301b600d25008108007080c0b411051580096104032981284401354100050041c1280c4c007a5a80003080c8a421101c076007268000e020710746450344c110340300740614162508 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 5786653 1250 5785403 5785411
    0x708121b190e090103060209010206070509030c0907030b03010c05040503010b0109080606060a05071202070906080a05210904092901080703080f040803030712050a0b06070b0a0612050102070501050c0708070605 92
    0x2c042a00445800001c2c40c0304409030011604140e011445280c04d59040202540c051178500300180303404c0980000035600c040781912140b0070200c0e0000030302e8072842034100011a5001178000d0010b22200d5201030500d0708103025160080d86041040800396100703d04003421124984007404c40d41d1540b40c1030019070341c010612401401010401341c40010409003840c03003500e1455026120150070103414000755012544007260755030200c0086800708101180c43c5a60041041c1c1300102000d0007041030b842801010003096029113460104d00134002129002c5000200c2a280c8080518500b408900010400c0c00755080c0c03903000410500c002031540005144c1240c0300700145003400e64483c1554915407040b10f504001440c00d5403801d908000d58000c40f60040c1c000c8406000561905000c00c1c502e004030300008e00303001d20034400318000320315135400500a070606c202d5840e07491000d824000e010b54845042110190301e0580081c50f4806181c083d00d4090358400c4016140c000c0b980c0707441024046c064 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 5787903 1250 5786653 5786657
    0x210090b060f0f030709090201020d080103030206060d052103220b0f090703140309090108010b010e01140f0f04030506010501020601030b07030506041d07090506060a050910030b060708121b19 84
    0x318064030759030307020403034030008010005001c287c006061000a080c200181c08070002e002803200140000b0303030082040341d400b46042d54a80c038140306070b007040c602d82a4440752066038155080c410117010745c0e0003001103201307900c98003000d42084c081c1d00c00200b0b1000c91140280c54140e0940c0490041c8082c000d0303181c0c0242101d800c40c0c00e00c98490f101c8a001403c40105019580d01c00500144103040109001e401051000000c02602d10940000380c86901c9802c245030400c080c2400e40c04089140f038041c0d4141c1080c0f11310a907240c6d00320a0f044d00640e0300c01d02080e2801e108180c00054558400034030103040c3d03a8451b44003061502d0703820303094000d02400fa11032580070b61034900d078007020302c6901441d5001c030049000070001649030400c5441101d01c0546400d006034800c202610215170407404071256a402030f510b4944440300210120010426220ac841c0c1c4040005459803e20400b40064100b981c180145425070340c640442d5880507a080784864881024207110720f400385442d55000600c0180780e4 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 5789153 1250 5787903 5787919
    0x30f070c05010c0302090405060f150a02070905010b0c100204060c0b041110021b0405060a030f0507080709020703080106020a0f080f0c01020d020406030e030304150209010302190804030210090b060f 87
    0x107035105400d6aa0300110000000d50109202d0a01c0c54540a4135810039402c0d02c0380d06d425030f82c00000c642000000c2078803480113640000c155828078070820040000744504082080556121000030701250710011410300c49216070010342d00120002c0c42210119401501c0b0300340c44034441e54030301c009058028400c1d01c02220684007600e082e00e807200311f02c04001d5181d002c0c19100105800d070110b00380c8040005409149002c2c2006819200c1d071071800709890700705a07240f0a007a40c40c40e1041c60030341c158000745224040c001c000103281c18640c0182c2250740c800c1e00c525210360f8840710300302da03a21800040036008466211408012844120041c51246403c8030742510781810b001d866030981c1d108030b40424080751b001804010b150b60501c2800000d0700c1c18405140396040a03100c1c0750940480d0000c85000c03603030006101823030740c2c0a0741c1202c29103030035880b044402c45841c0790068132402d000c0360198003500441c1101070001c800d0b80b05030100780c0d50040881c007090f11040240003241492010858104000c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 5790403 1250 5789153 5789177
    0x9060604150206010512070b030c0c070317090a09020a0516030306090606050702040605030105060303270a0602060a0e010209010f050906070b0907031109040807140a02060310090e070803030f07 85
    0x110716180c0704015290014800395140009211000b0020408070040b5001414107001201c96641141c1d08405041d1500391030b40d02c8840340c1814000700390700061001480303880c5061700360b14a030040c095140342220a0700503541d44224480a9103e08500300c3d0016004010740411a5151400c800f0301c03074024980065420389030b0258170112050b541180c1d0201e040822080d04601c0c0c203000709400781c1002c4e070082c8424100040881d80e00c0c080e5400000c1103007411300d406211140c50401000020100800c14140da41d641d0714082d448950070344402d201107040581c00414100140201c038040003040c0e5aa032008610303030900702c54581080b10307400e034081e00070041e001c00b0030380c5600d0312130043c02140c0181000310720350700e040000360000c1e0020a000f01d01100030000400d040c0019113003100c0c0c1005041001d0001d000101e420941c0c0f12200940c440404810f100c1c0320071042000000350b45081c2000c020303210000001030f5031580f0f54450b05605030710130400100032401200340c00b42c00800f03a0500600040b5 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 5791653 1250 5790403 5790419
    0x80c160606080c150909070c050a12050703030c030c0f1d0405010603020909090a0c09050c16030e040605030c0a060e01051306020303150f030a03050c0a0507090501030c050114030609060604 83
    0x1d2a54425010b41d4031030140c82525190480205002d4001d01d01158604048440850701e901c0005101c2c6d814031a154840005100040c009007448507072169000c085640400ea0280594101400660020b49003100045a02d4042e101d140304e240c04030b4541300784012030440700316501c201c60101c200d1481051481a006500c642c080c0c82e0103412903880160f212105803040c898010740c0240348600680c407a9444d6004520310f042c0074001d64009040214080c0d4a0011086c0d1521804195a0000700102550380074160f01c1445415145d46c11078003409803079541e808043da9050031445442e07001141e6001080395071301402c0c2040755084181003a500b8070f0955402d0801100140c1d1016009da0000010000134150400c51000c20100c21921411805c50f060042a60303112410402424841e002460901c1d080d000c0010014440d800411140429103500818001d00f4082c401112802d074440b00204442d8041e400340411000d65441c590304566514042208c251405071110f600024202b2000c10f1800b = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 5792903 1250 5791653 5791661
    0x60b06070507080601060201110307080115050c10050a05011d060603070c0b040804030303060501050c19020307050a03051501080c01020307120504090603060c020f030c0c010302030406020c010606020706020114010501080c1606 99
    0x80410068104e40d8035108001e401d440c40e040030740040e80010000c020150360401815070664104440c40b562070039000e0001c2c1c0b41c0e44140312002c5071038450203503840e14940c2241c0005100c0e0b940c24009100303690380c500501c46d052400c2100079802000d40000030b803883c1489000b45034884424500340074009803c0c0c80344014448182c405442226001500303009042c1c150194000400080c42d08500d00a1b64480281d110003400122217090304030321030302c4015940d04102000c0607001c01042c1002d060303924504143e403910f0029655050700108400040d4104000c02c0c2c450301104180c015515003811a685c0e004464440000801407013006d21010503035070710901c02c080c00b45210b08000180b40703055a10207850042c1d0590041d642d64010000b801a0340004502c101c00c0540a00700580c17662224907241019000e4184203811540c81c0000014110364006001021103101b50000c2198502c240900d00d030500007402f4060110310f101c008070341d60102050091070000708108500c1e11030a444e03030b2040f007070b5 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 5794153 1250 5792903 5792909
    0x6030606120507051c03050a02010b041a03010608060c22090207150b030604080d020d020c030a02010203040c06080103020f09040615030507080f0f0d030506030f0a0b071205060d060b06070507 84
    0x6070180311640811030704019560140004032600d5000c95154005515803c4045400400304079001c0780d0045001d000b500600c1c0140b600403c18410341a21a041303264074038061984610a600f05640041d0040d80031810038029034481468600d4034520601400344402c40d1341c500740c1c01c134200030000a2078103c1c9101a01c40a031040f500d640d02c4001144a075819120f843c00218401e0f0494018400099070160031031341c1031607540b2000b40c5c6903084901300c100240914911280b6038040010405892135042d8002c0d44035030711904450304210f486000032a0500070900000350842c03501214130540d03103010303042a40d126100c2e000102e4070310300070aa0444000c001e903004448a41c030141040c03081c4036080c441225401451001007003a02c1d007072001c255550002107207000038141e4400c04145143c0b81442440b40d23045c0c11000f101d54445903490000b030251011108100082c1ca0416914003001c075030301440340241c07401000d40c41044407684842008020340307a1080e920480400a200000e44e040c0080001 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 5795403 1250 5794153 5794169
    0x17030a2a080d06080c130c0201140408030f0112080a030b13020c0c0405070c0308011401020c09070203040608070302040302010e1302091801090c0201020c070611030d11070c060e0303070209060406030606 89
    0xc58100c03012079002d543c225001151250031607070810700c054641c10b0418100c1c803070311040401c0101e00d200069005100c4003000d04141c0f10184104001e1080c000c00550117000c545400020980e80e034058181c008c1c02c0d0400c000e1610408114141e0070740e1194018000c4504028050304280c900c0005920480e400035030380c40c03003941144000318041d191911845600c07040341d0500302044041a9801402c005050250180c0c40b0507049860381c1a920800c8540300c0c40d400940f40d1049401c00d82d402070f50b6600700b840f0b0382c4001585400003904492090082c1c4040b0380d4181c68040090200790104042c1c00c0305190250308056080c80b8009282e51050203e051080014900138181d50525013414240e40740b80150000703580c010041c22141590005e1140103c0e0440d1803c8101c0078102043c85081d807141c4032015880600745410644200c41d0640140343c12407080504d81c400c00c0d5150402d03540740190081080d030507003052210102601b4800c034440d900500040002820035169a100b07070448403141c01500d0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 5796653 1250 5795403 5795407
    0xb0607050c04050109050105130f020705031c110a050304030e031f0207020307090902060a140c0105040c0e07080714070305070b010609031401020702030a0f060906090b090717030a2a08 81
    0x2405041900c43d0340c0c09010a01c40a102560400300810180314008256840550341e0f5241d14044400e07541c1658955039000d415243e1300c40507200381a8004522255000c0a6454055901c40d4084864101e555141203030301c4080c00c654881d00c0c00c7ea4038100b181c1c0e200303425001b45503186021179141d14482c13804242910005880310000d00500d0302c0c0c00c500d90402403903545060b65040c00361b50b4000a031420340905107490040840104986500c80c061102d05403041c1d030a140a000420003001d01c00000d803800da00300e60000e42d8500004550b07064094801c07501080442180e041486080700003040c409000341407091a15105649260708104241e028800041170404244100000d11142c1e4020b1000080254140b803e04e8001a0b01c4401080009003911980c1da6a2003c104031a0440381000350008402c100700341d00d0303041c181c660141c2140e02c03100b17034018640d011520100621180c0f400c420804000e40c10103c2d0380c07000740d4400c20790300244011508030030181582c0e684d504c4203e10420b886162155 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 5797903 1250 5796653 5796673
    0x1504080408161805090a0605240402070c05010e0a030503030c0a0201060f03030504060507020f0603070c12020106080601050609010903080318010c0801050108070c0c080a0f0209060301050720010b060705 89
    0x6080141c8602c501144001c0b600d800c00031010b1180402001c04148400001d141d1900300d005407031700c40030110040249040001704003106041c0d880d0303658501d59414142650903030140400c8100e1050305030003000a0310380c05040c40b0342e5200e4145050707001805441c80904546a03202d0b185150021220f020300d00f0070010700009902d80c2030054800801007032102c1001c0c103045d558003500078000c6002c0c8004001c00490451700359a81e08030202c8140e034000d0112a50381c14807110051511000d008242c40607084100252901c92051003100100d9030039a01500c001d9082c1800c021165104180050400c91645804008118650f0003980070b1828610613284d0301400700390403400d45000f030780741c5802d10030fa110040107640d8011500e0303a4015140d240c00d441d4444145003080600b41941c2002206110310750300441008100041c54040034021210443d095030388004041c203981c0103c0d01d000c009030700448508201a8003c0040340c0310400c800c00403440c0505a008114a60401e11083ea0780c1d80c825030501d = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 5799153 1250 5797903 5797919
    0x110a0605010f0f03050307150b0402070302010b010905120d0e04020903010509061009062402011b09030201110703080405010807020c091006080a05010501050f0705010204030b04060207020901060c0f03050c15040804 94
    0x284010001c3e804441109461602c0f020303101c0c0100400a80021402d50b200b100304d121546c010071154030300500c02c648541701c41c14000c1c004c045d42103855010460480c0040303045d2401d05a1000b20820841c000c4c10b075680080001c0320100400d205203074000c1d4081c020034805540c280180382c41030305200e0060850741352000040282144030340c003000b611440d00500344144c1c1d001c46015160244020a0040014a400d4003240103008403044c10300e01ca00104210201d541d4080e0082c4200c034002da0b15a00940580c9100c940c44905d11302c80108400344c104020003040d4010034410343c0c0406540140c03007011070300300c02107120b66200b16078076001300c90418410700800e90841d110076004202c541c800c00c85d660401c03002800620480800b43c000000120f110070403c403094040300c024552203040d01d24030382814030b003075006900422001c0388240d00c1e400010600030301c104550355485030015448071914500d41c5040c1c51550003007050018500804810001903a001c90902d070185d449071000c02d6a0754a001c00c1 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 5800403 1250 5799153 5799179
    0x180402161703060105070b09030702120102180f0a1e0b04060503010e0708040308011e08010e060402030d1e08060f060c0c0306010602010b06040b03151314010902070305031501110a060501 82
    0x1000310101003032040c80b43d5070740e0040a5801d81a03010100030a01d4507810140391a40c01076020095200d0300031005403180c144190042c2140b1034081544490507441001084002d4694050554201448640c20001c1c50b01b15107003582014100d80c0400c0070551101c800e4485548183c0141d008150004010010807804403a00b9920064910b0700000b9410300d940c004000000c10320800b03101c074980d85003038a03040c403004107520b0007810b004000b0043c8007144c00c401c0703484450445e010391203401402201403002d4028120b400c0c0c104040100c20000800c09201940d812001a00c016000001092200c11b603480d00ca00801c5501c0c2003400500380c00410404140c50068146c004104590519400100d10749038441501c050300c254031445a101e5030360344a0040c18200c7c0c07484507035105032a0350101c140615942c0c46072031400c22101499000340e0b00c94003050164850b0b040010b0000d00200006615501001d05034082150149002c4201c288804219841d00c0c007492000da03040e590740c00040009a00d4004 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 5801653 1250 5800403 5800433
    0x601060206070e0f040c030f0603030201090b060a03080301090c050f030406050411060c0a060b040e0a0b090105070807050304020d0c0f0b0c060f0c09100905060d0c1106060307060518040216 83
    0x2600a1200341d030f0744046100c1114500c880d42c060780d01d440350049498043d4000c140d0302d4910500c00c20a255032414000d01900d0169400d40703500984c45e02080d803a0418a0680c0305890b04910100d142d6460010120000d004917a6140708020f8144904d00c440b00f007010085d400b9601a480228042c181030a00800c0507005049051159004006625104002141c41c0b0398550f0001000103003023500d0780124010340700c1036040902e54052164000d081140d041c141c1805100480000c11041d40d0342201540c07412000d43da40c50209600740002001440c020b10710341d20040c812103c03591455503c0c03543c0440b840f529000030b441894041500f0220031420002582d201a0b0b60600000b581001e5810507441d20684084900903285411001c3d8090702800d001001000302806c8695503052408191005020070b14810000440c1d00c68100f04240c00002c404c4d00800000700070b05802440d180c010350355035000215401c1e2200602c0c0703a60000d5030b10b41c405408404000f0032420010406c070b282045424142070 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 5802903 1250 5801653 5801657
    0x403050319110d120b0f030105040b04140115030f14120406030b09060a09050402120709020304140616031a04020403060c030606020d0507110105040503060901060504050907031716020604030302060106020607 91
    0x26080e9045603400131204812450036900024400040e5001c80c012509500e52144c256081400388810003202c542c4180c49240550152480011b0214000e82078909054125040090801051010548240c004407240b480380c0c0613011030802107204070f403d0a01c01c006012400002240c1006020340501504400c0c504c2201c9030303050340c581000020761800356401a009029a41d400240454031403035510300280902c0c10464055540e15030111000e540101c9044441400801240031a560000b6440e0302540b48664528203001c80007030101c0080c00341200c0b0110402803510b0722105d540707846c401007018500500d00030503613030320221019040e039405500000c110740c03203120070405041c0e0180c2030707031107296201d64483c00094410004840900a54002a50502800c2c0c180840114150301c014100d80b4151800d006550760b188503103490701031038800a0300f002c0800020440c2503e81c03100401c0f424003000d0b80e07010003440540104075542c0041d08210b0240c1d10000040c49910303010401c0c41d50046140c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 5804153 1250 5802903 5802913
    0x121407020f070b041203030605030604050309040605040504020102030a03050402010504050409080d060605040510050d02090a0b1305030d0e09060307030b0c03040605010e040206070807020103060b030c07150e03041703040305031911 101
    0x71640e010f40e01c61440f0700503c040d04480382404040c800c0e00114020240182103466a080c9800c1c0507449a0007200414407607403038040002040e0415004007441160140c02039800c080f038624058028140c001c1c0101d0403c0010040410f0a41e070328030400c01150300034180c0640750b441141c41c620450f18241c00c400c0501000340401c1002d40c1d01c4103620003110045141094440031131010b403c01901909000d00c0d40446100310110390840c031000500741103a900b20000c001c03c4d558005154889051303144e0200000c4503c483c0c10054100200060b401160250450396030f01e5494844410505080d00c01440800c4004140b00500102d80903090142c102500d03101c4460400e44d0002d540e51090070002450184081901c00940e0b0003a0310032170003030407a040c84540c4c9180601504040d1b600100040324290700010511184c155107210b602522501c2c400107514103400c0010400c01d42c0d246620303840080c48100b0021001660600c0540b0002c1d140313100710300c0d004102c040e01502074186c2c079011003059400 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 5805403 1250 5804153 5804159
    0x60e0a0305060403050c011b0e0102010b01110d031503080a020604150b0102060f071701030c090c0507080405060f07080705010609060e04050a0b060d0515040512030906010b0307121407020f07 84
    0x802e03850380103545411305598540802e0140f03400343c0f1608005481d42d0070896802d101d080d030405034550030040241c1c001c000b00c45a01d001568a00c12000c50703200b441d0700c84104050380900940c02802210780d244404210300d50b6075a502045d82d030003447e00c07100580119080c0001c01000040b415202003000d0f50a02c4040f9020000070751341c030001045c09001159100103d200c103030050310b0701899800300c2d0390710203169a12414184000380061186d082c0480c030740070b100408244030300281c81215510035699480e15190204005141e0081c0305002300c4600100440381c0003c0949006008403441007001241403803602010f94100c9070203500ca41ca00c1051340c0e08010000e84007003071011055602c40150f5080e512100041054200384c1729004100f4451015030f0a00e4611b8200c040d446541300308216250340e8840d003400041c600080e504d840080e03000c0c0703006101c01c80c6280d0146a010203070303107041c01e81a00e51078542000d454030300e4200905c40b410341c010300c2413545d81440030303110340e00c0010000c012881c6 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 5806653 1250 5805403 5805413
    0xb040501140f07030c1a070804050d03020c0606100302090604060909060f0305030a1d060408010203010e0601090305120a020307060f02070209010503010203101e0305070e01091503080702061803010501080106060e0a03 95
    0x2003040742c0201049658044001046140300b881c8000201c0d86d80700c154203103000c6034003910661042e502600d8610a40300341040c228468021900680c0300400035007466214042072000c03401c040c801d00414103800b80581e04d8035480d0703a4042c01c0101040d90310050400c0c03910191354221002c9800c035984130f009215041c008514000102c40b0003410b00d00d40000214401c1c01d01e03640c190710208641c0e42c00500040d00003414101500510b05882484884c0003c0380c640d280192000c118511000f403440e0000110405401210b80c040c0040745218015245800044d68070041240c030ba890302030391116808100202503003040d101a03409000181c00841c61400c0007491143c03030118a00c190315034032907a2112908021443c891000c001d550040481d4015925104000000c19007401101300c4d0340e14112070042841c01500c03a5508403500200b5aa1900107aa024040d180c0d01c010a9031402c00b80c00da1850541e03403401d01c607041c0206035503800043c085d0b003003100051250603118a40380c4517800700002031011507 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 5807903 1250 5806653 5806657
    0xd0605010503060d08090a09020f0a030f05040201080c0304030201020d02070c090b030a03050906160506160f0e1005090303070212010204060e04050f01141203030a0c0e0103090b0a0e030d05010b040501140f 90
    0x42c1c11001c075a44a806e00780c0050301ca925140c1140c15454008950030303c1d580b510034041c003200300441e01e0910038400d58120520850710201d4002e8001040c00000c6804111000000d64105010f03100152800402d00d0010050764800700d0216a4044030b01001c00180c000b6104106512000b24040e141076245510020310034041ca01205101b1040062404802680515105031003a84601a00c1280c500480d042c0b50350010200ea00340031800382244902d01920807110700d800070000a00000d056400c01c2c0044465402003c01140c15110030891000581c2d614019821082d0051001680d22410080010104140c103019240501d00b80b1061007210200e0302a11415101616132842c0758804002c001500d10306200d20f0701c1c03007502002082c04400c0030181c00c0802000038548980c0c541d1580350b001142261800100034000b1076040c8003240207102e098004000c04031240d070849090408480c00c010841d0002c0e840350343c16000000d002c11480d40c102d1904514400d44005a600308003500c080c4554134 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 5809153 1250 5807903 5807929
    0x15060b0315040b03070305150901150303020d08060a120b1005010903030c02040c03020412050607080f07020607030b03032101080c06090603010e040305040b030106030509100216030507050709020a050d060501050306 94
    0x241d5203e101e840c50584040001000864100b0100d0b40d1000e0404141c2080c00c41c142c6200000b5400c0c40060310180007030380385501c00c40342d150340240b402840105088a01c4040502520f9000210f4080010b031440541d0300c000015010f00240340490510300c11030401031004d54451418845207000030000711f908440a281070b40d405503808602c00c413403440704500900c82c075000301d942000b20100e620148100040e41070310036089902c42c10850340300c49a0024500d80112501c60060f84060f0000b04024403d401261129201a048a003031080f91a44071145035408044810f51323152407801081030b42f81c2040700c1d01542100b507422614020303c51005c10183d22050040030764030b40310040420304044c8190201c40007482c105401c01c0d102d5071611001800740800359200d254502c200d500c12458040d1500c00c441d8001c1c0d950031022140012680c09980c0360300aa0002e982030b0181480c002140400780c0010300c581d82d82c035550070750344a00080014041340e005800a60411409000f0420700351581100e0f180a = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 5810403 1250 5809153 5809159
    0x5070906031109060309010b0405070203040303030606020619020703030605060d0c030518061f030204140405010506010924020309030105090607020609030403030909020913060b0409060e0402060f0f070c0315060b0315 95
    0x1a170783ea18400c0c6c03400340502041450300145004100003045a01101800035039100c0d5406010305079841380200e9581c10f0a898040e02011030300c0601682e642d0550051400303610174140418980c1e50341c40019080d0b000320f6464200c01d03499003240a040e0383d1500c9155403000d000d802031a01c001e102541265203080042903403030030045481c2002c40d0014441701500013154024410701240c1c001c08940c04200310140e40c126001d41c00c00340422025030040c41380ca07069500c0c004921482c005100b6100054624108215041d80070404c440b0101c0c0d1800c3c0115441800100300600107403c207440c00a240003401400707a50b003500140f20905c0000c0c0e1241d40b4404031a100309006d0784400100d000510200c2040c0041c4100c149482c0e40061071101c41d00140080f42d201d070a04000e030755654000c078050048101c80095100700c00304800c034907801051001d0310801c1040300e00c080c242249503841c81c100c80c6c1e40e50415540703031030000349190105d103c2d8010100079114403901203083d810b080d075000c510703d00068440c0344 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 5811653 1250 5810403 5810407
    0xe01021e0306031204230103020a0e040c03060306050103050c01020f03031e0712020c1501090603050619020702030f2a031e010e010f051005030c03030409050405030f0a02010507090603110906 84
    0x2c0d03075400b08079056a021550900b10b0740c469569824040a40300640e0844c9074080c1e05401310310942c000d00c01c0d58444641ca445d10a000010b40c82008000c01c51005031034280760780c409000c004100b05214585c041c51043c0020100c000e410000a8602849220f82040e00c0c0c0c0304004201c80d01d07204140c840785c40740707607158001c00c1515030303090075103000c10880c0840b0b28003480421240200000002d00306861440c000c4240ba650b6280c98011080e01c03200d00002d440c0c0d80c42000880c0441c084442c0e060543c0a02c0e00f801824100710b54000303401d0030b000444294043e440064818148041080300e0014141c9a041c107070070720600e85000c40d0b1903112815040f0551040018001f0f11200300390813216851030320380000c00c0b26407e14011000100300c142d44080041c110603d0100d26414006650090362100070015410203182003e46005400007c00440e524002440718800c4d500ea00d40141c00715000c2c0b9000480d00d450070700b200400341040c0d94070620815040004070000c005808085500316201600e94a07 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 5812903 1250 5811653 5811661
    0x5010b0706020a0903080c03070b220b0c0d06080714010306050d030c050a1203090309050301090804150903050303040309230105030c070503161109010b03070504050d0f020306070905040e01021e03 86
    0x1460030b813815400500a000b00061036803d0b014044020200e40344510074560322502e803c01500318a08404c68070f41058640c0018007004608000320050340010151006441c100b4500c0911058540561190b00d259100040070321102d0f40d0a131210851820a18080000510304000140e600c1400350018060104250034542031020901c0711100003600a416a00c100000c5003006009290090055000503142400801c1510b0180103840140703410500560034a420010040a07000416124200740505800c0000c001501407020b103104034003076100c0080ca00d28195403541100c0900d0181d13040f081e48064494260307078208050743c0d00a40c404500640f201e005240c4186107101c0d905070030400d004100c1440007000318094aaa01208081c0c031445000d0340d0794001000d440c002555070501089040c0024000d904045034100102405825030b6004000c1d960003003130403c4010707a0301c007000949030801480a41014040c620300c203511203000b1451700400e40c41c0d02403100c1c14401002182d00ac000081 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 5814153 1250 5812903 5812907
    0xa0210030b0405040b010501030e1504022b05030409110a0207030803060d1e12050304050703030f052a010605061e030405070e09060915090a0201030504170c010e07050405010b0706020a 81
    0x41c03100c0980500204040c2c101801c01003001a024410140000d0034034606179940ca4002c1f91200e01d0036050140301555840d554200300070580201902920440a07000c03078456880c0940e00500c440740103101459031607041500c00025605081d081102c0c21070100071201c101c0b5800100c14080301c0c0c114454980b82e89a91001610303c0e2102a0090503e002000285103219044030b082002c0d10700c5508119030b05090030a040c0d50501040320054107941120400300046409600c004800310b2140c90041e103481d034040090300d101144804a0303105060700341d801d1140760703c0c24407804003d0401181c0a50030140c0350208004c016210030348921550b0b001201180070400c0411081001e0446007600241070b251169149a940604590542132841000650302c20f0341c540c02100c502034031020002d009160580c0c0c00540c041e1101030811130740902c584d024000c200e640725024240c030320b01d42070001c41d080210170a07480c5481004c0e04160711840c5840010020b01c40e5000803120007941c48030015031500d141d1101 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 5815403 1250 5814153 5814161
    0x10605010e0120010213090e010c081e0402040b040207060504030f0503010b090607020d080f0706060e0106080106030504030e090106050703110d020a0212070302060304060b0405070908060703020d0902030d020105070f0f020a021003 101
    0x1b6030b803242c03034200d40041040b50300d0340c010280c1c4080d00300003005180c0404504a82101c0d0680e264040c403008241c441d0303414407110100b558018006007011420b41008004103049902400040d5003059603803091108050307005400080f0044549499400c550401440d41c00d24800c2010161003144002204c01c1107403180b120b060051600403501c9900c4013140c03c180d0910346e0108400304d0b4201d00c2d005000c981200800223240c10789015555040c1c681c2e00f0f00200b03500400c000784c01176041c0070320401101960385d83e19000502034074041e543c40c0d4a44406180240207041e51003401c1540d41c00101000e46440e50003d40303059a41d8045554a88141041100b0750a1aa0581020307400410000400052040c540c0158101d200c1c10390701044035944644040355041024000c0342040e4201101142c1c2180c481e80141c000c1d03490380d40c0000b0741000e8650000c1d2428440303805c26070141c1d45420401000542020100c0d840018905141d1000d00c4041802516560700c80c130024854030b0504003460320309101e580 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 5816653 1250 5815403 5815417
    0x1021002040e06010809070e070804030507170406140301030f120507050607030504140a03020a02060f0904060e06030105070f0212030711010e0106080708010b060d050c0c061008010605010e01200102 87
    0x2811075071180c4420516069240444005000c540b144c004601a0100000d118080b81c404070198500303a00c5819080300c800d035002e0002d4080100034024000403481d41e591a142410900416542c1d440c03903c100500304010700d4810281c0c406c0d041c001000480c0b0b41c448201d81c4240d224030080c9483c0c02903001500d00b8041e24602500303610404040064103605584190300440c0580001a1303c00c140302509651542e0fa00d1004005030001075045006007811b4010b0320700b03550f0360415103003841c84081c0400e0841d0060342c8a07400302c40e080030074080b260a0038400c40741c2004240c9071125000a8800000e50341c0c528403019510f003103400000040d1414070542c00611440c3c0e00720b00034400e15001c040028060000e90003281080c0c000d01c040082c90b5281481848403a4801400c014181000d040c0501d005260040424545031810000400c4800080c403454ac407803020740e803d180300941420085801c4a9594100c80c0c103007d040e600c0e0740c5113a82c001004800c4001c04c1800d51200c41041070100340a801044 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 5817903 1250 5816653 5816683
    0xa050c03040609080c0d1208090f0a05010902041404050601030b040807120f11030405010f0e0a03050a0c030c05040c1b03110607030212060916050a03060e0f0406180209150102 77
    0x7040110300320f5808800402210302c1038085500c00320b5917104200201701e400c00001d10894070f400140300c24a015120305540700c0c1090080d07414003000c040341c01c0c0c1846000d04084683c1d035520019003045103040d100b5404044048400c5103003518085c3d0b9540e649103410b000c00b800807210140041e04003e000c0003162821131340f0100040b801c81c5001c3d000b40107141c09185c44008224480340d004000c507000002e640448105070b42e40030130400d203030b48169810780c0020b21981d0046441180840400c504200d1710200070710400881c0c0005103142810306203900540c10152065003010141d07001c0b69482084812400b00f46164110622820b20302513510012025110009005007010031070300c2030701640a0308900307402202030310712036440070100305501400305c901d080c103401c1401c00c0000c07540c03244015022000041c00c00003845a11101c1480310842c0c01c07600e0f0020203010300704100400010f4040c41150506100c0504412040d035400500360302c00040808030007031943c08149050b80c2c420054075170a40120 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 5819153 1250 5817903 5817907
    0x6040306050103051005040309120204020c06011511010603030c022b0302010c1704050601030615080a05010903090617010504051306051003020109050108011211040902040212040618170a050c03 85
    0x10345410005480248016905405070404003541742106000d10f5205d25855540c4080b558240815000360703015070442a40c105900380315000d01c242d0108070f100e0180101c003810074110b07408824001d082d64542066895140d0401c48108000380d0000c000500455046030300d500b4400154856400e08414003481721509440c4480c50024160107502c55008246681e441c1c03d59212b01c0c0b03071000d00064055134000c01c5035202200403c041401944240c8502c0050b40f00e00e40c410380e841c4103a83c90051004030a5400f03940d1a100c5000b05038104c1070440c014a00b030b0402c0c0400503485030304c882a0801c1446107030301a94880c800105213904150008003082c0d4801c03010005402c1212808001c0c1c101800120b000c90a50500401c0540c0190f1006040360300041025005550a0b44c64042c2c030000045201d4100b900c80d00180c0040c0d41c2c80c005890706070361405a00c9414076107814a1003d0b100b00c01c2030001081240c50300c0c03034003141c052100c804924101c040c41136503e103900303c401c0307841d8450010155018000 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 5820403 1250 5819153 5819159
    0x1050304021305100303030506060705070b0f0702100513090501140f04020d060609050a0518040305160c0602100c09050303040504022a03030103060c02010b01050d180606080d110106050d02010810050604 89
    0x61042503030700f0f030b1b0302940d010403080d5a0b0005018040c170403040058050341c040303401040041031550052404403507580e0850700300f8002d0381c0481c8114500e4803022002c80e0003c14842880440c20f050304004141502061025501d03007101e10760054614000c80c6c0c092460b071440d0141341e4807560100c6903000d0490b1402c22082da500c0f03400a190255900503107100700450000041e04e4070340304009404c000098054101651070742ea60641c1c19502c1040c606207406009040000401c400300d20090003408250080c0010b110780c003201c40200e603101c18042003444000d510074009601d00000352015690113640050750380d803076040550f20b084609400040b41e2103c1340754441c040200403026504882c8a0502805280c54120043e0f0980c4c440340b01d4903000a00611038000b40009580044101522060180c0000580c0ea2101001d82e20103401618103070740142c1b0103c101d41d9006003030130190a8a400208202420100000d03841c400801000c0d0401500f040464040d1602041c007e008040080041da50365036 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 5821653 1250 5820403 5820421
    0xf0f12031602011103030705041806180203090f0d05040504090606090e0304080f0303060f100e03060702070501020d09080703030f020708030703020d0e040203060d080c01020f04030606050306010807031101050304021305 96
    0x4829000b00d000908000345008401c100006403801404241c5a00d030505040140b2050840b00c0c0e0301a561009407501000a00001e000010842c07100580c100940d4038030300600030514002400a4140305584540030b03810b2010303407080a4409030f420845002c5800f11090030000040d1450360001d10300b5a25141282105070000001070040320b418500f500c00d034a50081070182c8034003084814075000100a40340014030f1500152103280058a4144515154400400f00e071a080084030508007590141d00d042c0b100d0361301000361140703001c120310300003941c2d41c103040b120354450915210060902c6200c0c030302d4035502e60091006002815500c02104d80300c0b441424001e40d901c50b110700c16000301e0b00303c41800a050074140200c074480c2030050590988012159a545a280d02000403190755543c24410007180f006580005c000960080c1c42c04640725041004050405206a00982142d4040041000040e2540c08200d1f0305400908000340c59907200d0010400e5005c002c0d8412503414508002c12407103203 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 5822903 1250 5821653 5821687
    0x603010603170a0f140307140c01050403080a0615020a020d03030b090f010603050109090210080a111602090105101b020105040905040501021903150b030a060506040f03060c0c020f0f1203 82
    0x49903076148004400f80440965983d030200010b17520b0750702c040000410301401401e02c000b01110903e0084e150040b01e00d440c2c4e0031030b8410359041303002070070080501403050f25030700500300038141142258062184e1084065610320b0b103084002d0083e00081c1403002818081c0d408221109009031406910307103805124a03606070000d01031500424904400480d01c808144104d401032940902687c40309259000c081c2c486060092104483c44d442d00c10700214544513101070f192071942032010030b0320300e46144104100d854050708a24000c19140c0310290100d0341c86000f80f50b008140d2040c10b030140070341e070004884521075900529487c2e81440309020401605500800e00e030302c01c40411100c0171b10820760407001e86001c0103582445010341c84060142a0015000f19009808400005251035170b0b840807aa607504140d014400340c82c00c2c00d80070000d224040c06410110741c11132808410b0458968001001e546141006500071032a10361101c0c20b60321085d58142954961500720b80d100c102c5041d000c2c042c1 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 5824153 1250 5822903 5822917
    0x31e0618050f1003020d0606080709020a0206090c01080105130e0a03050403022404090f1503050304060207060c0507060804020f03100c0e04020708040603050903040f0306060e0903070c0509060301060317 89
    0x1900d840700144803000021111070007403400390600c000d110f15603020420280c2c1c03060401d4501995603400042c40c0c8004201400c001c1584400c0907884603a07900c000307410280c1c02010784685402030b030080702e0541c2c2e0250702141900c5007202c602c410749107414214001482c005006000328803600402106050304840500b007224800c440c03982401c034070070040080707075843c000309102d14580504c01840190420340214195034440000054402504444242004459030003647c680c0c000203814800158140500009001141888611210f0ba5079030f440d52104140f007040c0c1001a500c02240455859862510f103800009044034900c1d2003840d00c0030001d2051100d13450200d1404881130300181428001c0d02c0407160000800c81c2020724111080d0041d0078001c29100a90000b04400b10300c010740c1000017400303180030b0040090030300c0c28066007803510100a81055201d9100b441204001f6141d04000d00c1950703001d03602d100030740d210280428007401c001c3d0030080c884044c4542200703030150114090000 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 5825403 1250 5824153 5824199
    0x5031905031014030a0b07020111030a0504031106190216020405100f060e090112080c0303090c040f060803070f030905041d011508070308030702120414030708030306060a031e06 78
    0xc40d9102c2c520040d82801140f9260142c00204504000c6106007030f0751584101d01d400082440c61070030000686680c802c40d07080440c036580c3c0c01030000f8903a1003020304209403406c8004001d5400c16a070f1040c28100444400300c9015000902c0c80000f43c400c0703054482c01507000c1e0042c003503814000c2d403000c0e00381c0c0386001e50342000b0503042e030005072135110301442d404240c0080c00e5411030741d0070410b8601c1d508120b440c0644a00ca410800c01610500410080d846076012101920031080d81c00c04010035a08481850b04d50319003800814081d0710804811250707003d82c86403c2410010a5140581d00002e45510044d4014500410300400e035500c40034690800240744c1c000c22022268002e11b01c400001030041c400035a020750320910001d4208002160408410300403030303003000110005010700d5402030b0060051008100d80c8001982020004000034042c41805142580f0b003110104020340110441c900c00c041d15403000b81e4498003031450f40034500e468007200340440c5880e07900080d082c07100c1c5000021 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 5826653 1250 5825403 5825431
    0x90a0b01030e160b0f04030f03021507020604080301180b03010609020702041d0a02060a02033f01030b06010516020406120c08030a02030702040f0f05010806071101050603030f070503190503 83
    0x210034a0040b0381420800780c406002e003022420f103800f403002a001709400480001003040040086000c80c0070070013020340700303a0040c0015a035030951a500200054191410340d4401420302c00090790150999055030810300740c491404112015031800f800c0001140e030b4255181c2840810204c0c110780052411500981c0c0911034009446000506040445000d21203508500856001480d00070700420380e2a02520450b400d100d03118100e1345210740d002c801028007510583c000a54800703542da144184210704402c08250790b140d40c075004140d1800804146c104080040d200b54250401080020320702d0300a00201701885d210b1003030f611381c07100805050b200c004101c980010180400070403524410150342c0914100280c0e030382848003514443c1c554184442c4c44184502c862280341c0f00c0d060003070005400418180c1007030080642000c1c8100103044031641000d00700f00300c1d600c0020880e18103008810318941e40d50b52034100603045016a52850700103150b0340d039454982d40d40c000f010b540240402d0841072 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 5827903 1250 5826653 5826671
    0x20706031d03090108041718090106030203130212070806010e0604061e050105090d0605040302060601030b06040f030f0206041a0403021801060f03050c04051201091505040308180c090a0b0103 84
    0xc032041d88010710903181e0b008211622203948180b0040750020310a00c42041020b110000b10181504200240c4a00301e071400c4104032980b070f0a0400600502c51400c3c21480c0d810722800c86599114000d5010780118142c101d945440da4042003000010280d0304161503e550311110b0403109508180c810505c16401c00c5000b0821056145400d0304000126100f5402076150100654080d04804442613100003039140700004616140905e6119a110741d000e0301007450510f00150071030b0418070341d0030302800c810311061102d07001203e0000300fa030b604000e14110301509407001814502c202d401041200d03000c0305c0800418040c0101038816a407088451044ca50071f01c110414050100740719410005284c004084240c50003588403a03040038490303010516041c1c447d4081003806040c10040c5141d60b540f50610ba00780040c1a5000b011108104404e00403418192401008081c0c0034100d03410042c551020f45082c92010028102043d13000b90100d84c19140c50307081d0324020130082201c0ca0109017891614 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 5829153 1250 5827903 5827931
    0xb010504050105030118060504140603010c05030c0a110a050a0506010e010504090b0c071104020c030a03180b0402100201140c03010305160506030c0901020304050a0b0702150406050a0c050c0a030302070603 90
    0x1880c140d40040c0d5400782181e10b04030001c010880e610014a480c15039985000c1200e40b91400303000c628035460040d8011904002041c542142c0c0c804045004000040c4140f041c0b0005240c00c54403071000c94580141003682140c0404e081050071a0010150321501103031604208001c18403904031904441c006109a80e96424070058489840004108124803000118082c149901500809000b54000c03141c240041001c0b5049034009003100d812a070021500300845c5506005450881c0e6281400764070344c010659480c6041100500001d21440070189001a6640700b54403000c0341000d09080000c0c241480c1030078070010b600a0200340d449010395403150080c000d1501302da8044480203441c0b00c0c519034840c071141c5856040918030a0442c0401c00c000140c50392182800c030090111408410390b66080c900c1000300b21400e251809002c0c3c41d060101700120f42e048011f0787d0940805003083c100324461071038070328106165091029030280c0c0300d800100526a0014824003582d109441c2080038240341c0d00f034 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 5830403 1250 5829153 5829157
    0x21504050604020d050a120306050a05030a050307060b130204090203010510030e060c030601030e070b040816030f08030a0b090a140907050a03022106090a0501050f04020d0b07050d020a020c040b0105 87
    0xe42294850000314005042420400303450600900076125240700603550300d4007003640e101c22080000d8a540c000d20851800d003401800a040c01c030002c040122503070b500e854682c0222000501400e503240001c08140d1180f03444002d507807500c4101107540d030352160f03049002500280034040c09607664000c004030080c028810031140c00c80c1c107002000c9950b50704003c818240d20041140c1d0415445211041d08c500040000b80c001e804c01e0090292980c3c00c210700d15141009081503449160405241080400d0440e06040da48642014880e50760b80c2c1c0380c2c00c2181c041d10824200c0c54004042d581040400031695104030b2032000c03050181e000b96191a01069503505540c01807980c4000861030801c014903100c100050007441300314205030851004c5440d10b040190071241580d040c0c0011500200300402031140701c0e48041802e5819040d800c0c560040303058008560402460180b01e90b0105000300e001d5810b603103803804c1c84503007076644060340c000082d190b61404881501071030a0218443c0d9a602982c1 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 5831653 1250 5830403 5830411
    0x301050303070605040314120103023607030915090b06040203010515071506030f030f020303100b0c1501060e0301050105040204050906010c170403061a04050403020705010f1b050c010215 82
    0x30040d030400400c0e0300c9210040c400500300303c09000c520309003d00301204a0006d4400304084910000e601c1d03141d0b00500503207240158400e1a84803030881042400d08850454500c0424402c1c9084000d42d6045012b4008000400003d03081d4200d0092014180f0029005111171318401d101030b42c4a0f46410080c00240d000070700545a0000d0041440074290200c5000b402109020740c3d00e0086c00300100303140b80221180713508142c51245000c0300180505400013140c641940b680e01c0294039524080c20802e450300c1c0340e40100e10b5080400204c00841060030824280c0261008400f1142545d4544000e04568001201075000c2c0d4202400014a0310700f83c0700b554111000a000d40006e540c42c40011601d414000c20101e6003001061a01310700782c800b11000d0300281d44940400120090002c8220120000f0b10900c0381c842c508200403c00000d03400f1a6440884100b82000e4211440c0c284007a2209a81a4000f19240d0041c45840d03050060020304986404420303006d55180600403d103410407544121 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 5832903 1250 5831653 5831659
    0x30f021f020a122f04120b010501021603020f100309050106060206090c01020a020d03030b06040803040e040b01080a02010f140f030903070605060616020f060c01050703060303020105010503030c0a060f0209030304030c030c0605030105 102
    0x2a12184c04050344903001a0000a1649600e14050711081c104d141d0f0003109000707440752250324006208550301000354000988140900e440060b24550010702e42e50740c03100610303004510741d08035544500d000b030f00301e02405640140280030341a250310340207544641c1144c54161920030f00d00005c64030350020800410003500070782406009440c0e0b840540181c80e440404036005201003000044011060020700058100a40030a00a08281c1402c07102c2e114180c204030040d40140e004000142e070000100c6440405500f01310030645032100854005000ea5000500c0325a40041045003030a4048020156648640c4041140b500d90805102441c0140c54031520030014181d000e1025250218002143d0701c00201643d00e00500040124203403a815102c2d000800d40f60802801016020301616025180c1500110300340b0089181183e5658003030300028107000d81d81e144c0810308030050380440c0c40c15030002c2d04680c1d40301d9903498419400c442c42e200582d20101c0040340070400d0361081c01200d040f21402 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 5834153 1250 5832903 5832941
    0x306030812060109050a06020105040303050a0c0804110a0510050405030d020304050a09020c1f0b091605160609020306040b01030516240c06060b0a03061e03030f021f020a12 76
    0x20030aa0804034a0142c80039040c020303420400625551880782d9100541020380c004a2541880e150241c1514405040c0750001070801001c0e8080c2940705810740d500c40d03040b01c8115036280240011502035001600f02c250070000c92242e40840d5504500100f0440f401a81100c040d1451590200e17203d000d07034044d560b400300f481c150420a0703d1160700903151400e4083c043e92094186200c8151030349082480740803903e41c4562208400e403070715620440d8402c441d2803401ea204210408024010f2058052503035041010481c1315061140c00da100c540110340c081e04880d40360805003009130310000240701c116070512030071003041c1c0042e001300b180200304c902401c2c0d12448442400208204141b0307002908080151423031016010900f0b900841000700580da4045648400400f001003d81d01107400851f00007814044030700032842641c00c2d9904984e01864141044404003104909201400300e40c2800d60b6540c1c41124050005940203000610352034030b5881640040301d55080695590171800c031391030104 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 5835403 1250 5834153 5834167
    0x406050913060e0106090b03010c02010606050301060c0503090607050115080f03030106050c030d09060c1205060630090309010e030c03070b030a0905030c060109050c030c030403030b0103020904020a03090c050103060308 96
    0xe0484480c079034811070020641d0300a0300c1c2110b003110340ca540400328481e11303051f81000c0d50500b03118890381100544000e004450411802070401d22040c41140c080141003c0c0034428064140240c406c01c080040801e030f6103410504103039001c0d1418504001902c59903440006408000045007902e512011010798110303864050155090342000c1d041605602040000007040d6495104d0484160f05c125000102440900c2e0014000110010700d132540d941340c4014041071fa9a558103840000c0200d2250641e030750850b000c0c030010b502070661001d240f00442d1081c8003071520080050310042400781e036540c0751546d141c0c04043d0340b10581404540c043c0c0000e4810f00072020500002d43e8000d100400100b15025165100d500c2c6900029007003003560000300051082e41224010ba88d00215251007407415410704080a055070710000c1c000500307040d540c1421115503406901a00c0384868020011501e07070084000c040c010746004c00c3c080303803051700e200c801040b6903010781b040205480d0032281071800c0941c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 5836653 1250 5835403 5835421
    0x8031602060d090f12021614040209010306030209010b03011d160309030e03032a030301050114070201120501030f1a07020a030309080702041e052404050a0608010f0204060e04060509 80
    0x1205003402e14000f41c80e0401000800c405007104501988154001d520316403121800909011300d03038261426140314150100b001d120312014400311400d00300c900603076a103820750058006000950000390032070440030000441c031807440c014504170380c2c5425a070000b10070b8020b0b00d6418004100c900c2a2402982c1820030641446548041e105a00c0780c140b0201e400703109030000307103540c000a0440311a11000201d804440c09110511072184d03440f68020350440d4100b00c0040c148138041e40c01d10300354840205628095a00c11280200b00d0303507000d41e0400080d6120b00300500340021a9009840a100d203000d0741c2007044c000d21040d40315070210b60240c03e0381003843d54120060100610b003a2650001804083c0241e501d5204141d08400780c018a83c1e09806d05c16083c0098407401443d1141d0a411184035003a10505000f03440401d0800b2500058075541745001d100c01840c50381c011a080b03610304031540401100c031354001c000356003082d00c807003c04000c114104001e8a11a001c2e098000f0f4030342000c02c907081 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 5837903 1250 5836653 5836657
    0x6070804140301060f090e0f1b010f050d0903090303020d0c03080a330623030106050309030c070905010815060a060309051207030e09060103020c071e030503040e0a05010803160206 79
    0x141c020004a50a507944602d0000c1a80f1504042c214594803600f4080c1c901c4200f1183d48040d50b400064072030f00780301d15800008011401c14260600005000411200d40b01d10112000c140707500e0000c0201456038200100384134400d002c11405441503c144a0461740513002c2220741c0c1c0d034140d503010300640d00c8442c0c92028160074400c10380e1540043c0b09404803403245280249900143d01400351101d881e00000802c4114844a100188800f204407175148d803244504a03410740f0b03c01c0c10002d40d00e80310140760700d18510420304407041c45d0086007000304290800c1c0d00001e040701c1c0039400f121800c4a03114128801114240c4070258010395203041000018040d80102c02202d00590903210425101400c0003010360140c4000c0b00000d1003101440000c0c40c103030605d16080402885d0031070405000c5450199511070300d0040c2012401c0e4422486d250044100d8004080c60384501580d0300c4540e201c800800b6030318191040796007641468000300e0204800400c0d5201d0392880c0000468442040d02407101903 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 5839153 1250 5837903 5837939
    0x610030f021c020711011403070309020a0503030a2d05040e0a02070803010e01090507050702010f031a0a0e010503010605060702030a0b0606040e0702030702030105070f021f0207060c020d090506070804 88
    0xc0e020b00c0301e0b180300a040400e01c0b00b0415500005030780c0781a2031408070300d0008141403060511241205007409a0851710903a0307071000d02401c0001e0010344500000318081c07940e5000940c58800040c454907a650f001e0354060081d012198118600721580d00004860358001c8a4240010401d102c2000700304110300d00b29420034044000146401d00720b480b001d14551090300101e940d9062500100510b003054451241d004d131981c540079003020b0300c41d80001c1000c03072549208810180c035202040d000c02c040c100c0400071240c0c0103103004449a0765003890405400b00340b00e898031a502e08000080c00d41000400c480f4100c2e4014003403c1c40054540e500c0280e680c02a2803150054000d1001148022a0710859405440d00d0340003940c580c00036204141c2915401080c1400304a0768080c118501900000c20560050201c3c00390402100302140d510005c0c05100c038054461070034002c20b44404d613008a0507200c075004540e5500a40b42c0c66400f480000d1040d40c100802041d410002000911006000e040603 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 5840403 1250 5839153 5839181
    0x10906020c0d06060e0c1201060201020f03131a150306010503030f03011e0f0603060503011d030427050f01060206070302040602030f0901020102070501050405010f0e0a08040605070302070f0608040c0e061003 91
    0x340c0342c17115007030343c1e42280480b07811296060008110b0700c501c404411240c0104168402949040031800c1010501d02000c1c2c104d24038001552001d108104030850070603200281d00300160403d1038006184407402d090b50786254028003501c4004641d03820003000700d40c07410080f01c0c44145141d00c1c00000c2510905522265808218080f1010400d400c214040342c0041210342d6001ca2910700344010542180c06501c600400c00e88001c1c0d0340341c0c01c0440482a039046410380e0b40c1901c3d04480f24200b05142d119100c50341002c0e13519200c1006120030721142418184c605540c226000b990320360005600701e2240b4050940581c1c010b0240707400d0307040d400c0010b001c25403040c4009800c0401d255202400d407082550100c489035119600c921018070688940e56200c0f41f44001045858400e0300c40800e1031007076009210411000092400a042c02080324000a0209080c904000d035506d00b00100740a6066401f00c80e40803500c07000041401351010340300e000386c41c01407c59214082006054000b85111003540349 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 5841653 1250 5840403 5840411
    0x10e1b0c0c130b04060e04122706030507030506190b03060102010915020406020118030c06090c0806040c05130b01050f070c0b030709030501150302090601081906060203030402030c0306010305030301030f0606050a080c0906010906020c0d06 104
    0x12752000b8404106c0028140e030788000c1190708006202405441001304120700038100201c41c42140d5135105a07007000c85003078034050ba075a40c03a0080101e01510a980014004940e142801e01c444d01043e4001c1088441a85c004c101010950421300c00c122031443c0098006424220f17180301041a030341c4004101c500ca1040c19004ad5034035140300e42082c03021541070312888010b101c00c110a01784451301c43c614400200082001220300700000e0410b02401000501054000c9103060402c01c0c1603c8020251034109003141d00c078074110304020549051400101e80f15402c003a01021100c1134800888141d0754020b2102c05256550320044130340c40801468211108400680740c80403503540d1240747c0140545501440d6285882c4c01490310300000c40d0700e040d01a501c503000420104071701009881c15a40d01c82440309140c0110308001000d00281d4020310343c0207103000c0c40040d11090028803801e02c2d480507514489180e07a41c80042d904075105d44a2140960002c800c07040790352a110800c407000e2071003904005 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 5842903 1250 5841653 5841707
    0x109020d0b040c0201020d050603070b04170a02040207080d0c090b0708030a090b07031a03031e0d060308030708040204050901050402011b020105120c070b010e1b0c0c130b04060e0412 80
    0x941070f1003254080002503540051003030103d075142e0003100d034031200940040c5209854010100708038402c074450714010010b000d070f0070041d02c1d00c140100d402d2242c00400640d2a146181400480e80e03000c1d665148401e440c00d440118818051400e4030200c481c0102c101e400c020740fa4441d03040304e90005003c1a4a2642d0f00380c00c0c3c00090100b94031a000324500d41e030008103242c44400d501498950415901e2180d8000e100307007508900c02000d500c0d800201c950800b81c90b85180244000034000540001300241000702c20040c046911840061145000b2601030129071504038003242201c0c01a01c002e800500050442c0301d0f24003800710b6440880e032041c502645010581181c86540035000d0342e41e201c03126400150307041482243c0f4001805003d0b01c910328401410080324a0004403010105102c880c900841c0d0340324003890501c1406843d1401501d6103854041c8030000c10f0007000c403066024402c515280d800b1500c490800744107403180360700c0100c8400c101d07181c003402c2e20545d00e101004506506000c1c150 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 5844153 1250 5842903 5842909
    0x18020304050c0a03050106080114040203030301140a08011b080c070308061c0206030a020304030206090303010f03120309050f010501030312060e060d08040503070b030712090b0604050711010603050a0b01080304050105030109020d0b 101
    0x20703c0198043c0000141e620f040485081c00d488103204844140b900d00814800075030f40100489044030007820f420a81c0c80500c03000306d4400840c40d03000440c05c1d440d040880d10300030541002040b0503615513942e8103955445010f48441c0d40034408000e00043c2c40d04000a40c40d09001621001c0800c1080c07070110071451715800142d041c2c1c400c803580007199401005000c20076804200080c2c04c0150f01000d9030a43d0304100003040961200d120103403182100301d080c544124029482030301078503000030550b40c440b5880d072601406040d00780f0003100090f03500c5200740048074586c440c11090760320140c6038001075210b4008008011209080903600c1180400000400d540c2c204480c1c401000f070b01840548900d09130390003504064440144200d65400c025880700064003241c009940b01100301c50000b100d454141c412100c42110100c0940e140d8070f007103804428010005141c210307441c410840000b00c0d80c0ca030341c2215201e010b54891140420340c280014805640b044c1c018118200122600103060203400b000 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 5845403 1250 5844153 5844169
    0x1030f020708070c050901053a0b060a0b03070504050f0f06070b0f0f010e010504150e090f01050a020901140c0c0411040e090f0606190308030f0106020601090618020304050c 76
    0x2003262a01c0b00020f4000c20001e02c10440d90007040c04444083c0d4a40c54a0003144451038801143c900390f2540d943c0325410440d20000400030810000a030082654661900042c0380ca0240c0344107102d10f96040001038044c81940480384158500d558440c00d0038940400c0c0600f9204554080f5400b040341840581e9684031000079240050240580b000d160520704104100308001408400c070881e010700060168820a03041c0301d045400503180001e10070920004c01460030141e03040346000040220521140c20780015040303d240c0c4c1e045008101036110a01c165040b48031f40d01103179001c989860804085c090440000e0540050850180c4115141a2000400320b400c0c1707284d09140c1120100d410b02589001840d401d0340702c82c04100401d81c04403d1801d81d0340d10703030b00103040f188940558100309200f4011142d030301c801183d106d080c803600c0f410801e044c03039220721090050b2030043c0300322000080d41c011903000e050105c4082040200c03a06000544520107940000d105407034900c0382c030918090580364924 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 5846653 1250 5845403 5845417
    0xf0e030109050d090603060303020309010c060e06010602010c02010b040b0a05010c020102070305010e0607110105040b040803060310020d0e010b01180e070306120c030501050901150509100b0d050103050d0c15050601030f02 97
    0x40901903222144002401c0c0b001e031500f05d5002c00d4170b49002400000e030004200c2d075a07490701342000390b40110781e4034003c409403030842d5203098540a150b000045140d0150032007408000340e50000d0110320303803e805100c126150315510a502c1640400c080002d54010500c0c00950f5006205440d0340f503071240c80345420340d200c0c00f9500c0b600d98070071010840c807540e2003c2c00194503e2020000e120a01305900ea00c0080785003d0300281c004080080803801c140e40402c03440e414041c5045003551a2854010340c00c0c001c140b0120344203050350810030301951962083c0783cae800c08900c100d03c150301840d003400014034503001c0083c00e40091550710304000c04d0700303000030300c2150301c45200341900c844042c1507140040c251b41c006031800c1c01c0c584c100014540240f880c80d58450607110141d40c1100303240e548000101044000394040040030f940002c0003051a0010340001d4143c03800750040301d941c180f004c2421240d50315030f0800600407144184603070401c1580350300419000a0145408118001142c640d03000b240d0240d5 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 5847903 1250 5846653 5846663
    0x15091f020705030d030504050d0e010306090905010501030204050a0c0c0303020a090302090103050303070212040803160204090b0f040c1202060306040902010c02030712030207050d020102030a0c08070609080409050609090d0f0e030109 102
    0x11030401c850b00d0108442e80b4111307070301c2c541408a81400c0d51030741c2e540c9075004115400e102c088252451964440d50007880103007030b03212040c00903d0642c1030a5000b480b081c0402c0e0b00131130508000a28082c003902458164032460f56134040d00300e00d07a0700c00310020741180c0c1a01c0b04100010700000003507600c820b00c041c0a18000da002d11b940707090148020f45824010355005000281c00d0004204641b004000d845482800c1000d04201c802d003440041d00900c1101c60080c0440030400501450381c041c494071070700c2580b084200b41c2e01d41d6101c520600d0240900c42c002035108000704005009801d140e0440210383d071060504510790301e80b0754002070900105800c40220400c005601c44207056042103c84004e14003600c8232025404203400007516031103171100144c1400040c1000404000c0c107181101c1e002900071104020304141c900d490121a030092080362200fa04241c0030445515015000b1405054024024452120600402e580c0c40d407411108000384280d034140080744d078500f1300500001510a07 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 5849153 1250 5847903 5847913
    0x607030b0f01020705010e0f031e01050402030d0c05060103080702120109080c0c0901030b06150409020a050904050601080f041209030204110301030201020f07180b0f10020c130b15091f02 82
    0x1202440901e106140756241154015a000c2041da40c005244030854a8103507034910000c0740441c003081c5081c0000d030350404060119004646454019030205004078400c500303441083d005508116444041e100014015800c002c00400c0000c040400409403513102030146805007480040550843c0c1007a0300a803030304480013902e0290105e061101040040c411500d001e0254119203500710218401019103000341c4c08540403806e1615070300155001849900c00c15552141200c40c001c140e41c02030b4100302c1c05181403602240c125070091f26100d2081440305201a044e607200d403240d0f048500c048040c403040c03080696000c03015032128050001c1c5c8004100466a0341d51540c8002482d1030164020f034051500010790600c840901280001d1459004150118001003144009035034421a905846e901c202c0510741c00205607004511001448011203070101a041161045400e80c4c640d9100c013030b4000300010508070110380940103000c048001926030104003401c00320b08002140c81804410150b444 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 5850403 1250 5849153 5849171
    0x30206070317060604080307020618090c04090609060b0304201c0c0b0301030b150102150405011a040b0a0303030e01020706090c0e1605030a05040f0503030a0e060903181003020c060703 81
    0x60030102c2e50b00301000303a03002403030320b0701d8013101d2512400740b030200910070300d07000544000202131240c00403000c0c44014103051480c203004065943c0c940c028070030f00d80003e05141740040ca410a5110710f100711085a01000d20350794880e9901e0700b21034210310078100c000c4041c1080420b15100c10301d8192181202002c82514030b40a803c091441010980c4201d00b1020104014000119849003480c2c10a001101c139803240040000141e00700242ca444014041e8510403c10003402015000310640343c0e4540504852801294240029989610b0744540c204e0b04050040001030b00c6540152101c2600d00001410100c690350748006440b21702c0015100403001d12403d00611080300c0b80b00d0380001080c105442405012007000d09503000017842429407994810004041c03014658915042d50b5001060f01e5480c503107510342c07034000c00d4260441b0007103205140c001000300c4800001c0303c0e9004100403088201a204a08000c0d02c1e078016650b0100b05a001e100b88180f48404011090085240741c07008070349008 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 5851653 1250 5850403 5850437
    0x106020109170403050304170109060207060203040201080601020106030809010f0207050d030e180103020d0209090307050f061602030405210703050d0c03080a02030609220203030c06180703030801050112060302060703 95
    0x8a82d0101c00e10850041204000040e00002200c085600c0d14588903011003110103690f0040950802c06003c80d800005c000e82044010390041d44264401d8980e55200e0b201c0f000124202c0b20140401401d117801000710f0041d41d03001d1103504100803054411140182e40350030218541c5201183c0c00c0340482d4000e0200011803600c095482c2c02451244e40c00941c0d5851500090710240d00428080d0140b10200c020554a000034400ca0750800d422a01722034040c613895058030356420088a80211040200c07000d00401032000c030442e002c5400080c5a441706101510000201490f04c008421981c4a80d03c00003000400c280684651042991207a4940101a00380030384a0302c00280b0fa052528810010021070ba03849440007a0040e01072506004035200624203411a40c0009130007070b51611010030340c071255181c005506d03803040c00b03602c1c00b052941c81c0c0e0004259a030441400001c3c00b04130a58014003680d40300c2c405241c08001045c4000c510144d2340c0c0c0120320781c0da004540640005a0304407404000030 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 5852903 1250 5851653 5851673
    0x103030212030c0f0a03021204030e0301060801020403020102120a02010b13020d0b01050901020a11060906070f05010e06060105040306090804030c031b150207090b180106050a02010b030102030f06010e0d08030106020109 96
    0x346804a80b032a5240610110815214000140e131444e08045a000b00c1a480303941511040900300c402000c0504003402c001d030008114129841c8250b080c094041900030040c003d5030308603a41030f00103004040c41705c0c0c40d5070002e0700007509410440d941ca011881e280c1c2c0c2c8501244107032000494005a6401a505850096602c8094640d06100e0308104407421030344d00042d6180041e4201c0082c000010521002070058880d400d000c603030092000c07481c00d081c003800c11499035405114100802600700d1302c085c40381e2100d1040312143d0106505020410210b4110381100311203d110301c00300c502d40f9490350742d100c50380301d01c0b0f40081d51035400105030030400124225805000e403403070000d8008410b5148000940d1985a801104034960712282100b2003510b5042c00c8449a441140400c806036031269402401034009001083c010340c281010b80905c0d00b41031007182d00a4861003901d00150744c0710001941d04c1010083e05039048240d00082001203002c2e0b1011350301800d034550021031a0502410203070284 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 5854153 1250 5852903 5852923
    0x60e120a090e060f0402030709090e07090b09040308040206130315060e1b0a050a020109080a02010e06100b03070c050f0604140c06040b040e04030203160c06030f150618050d0b01030302 81
    0x805018090240f25941d07280d007180c06100c1210050303035a079504541100c06e8001503000506640c10880301d02c41c5a2008a44035040d6002c0c1c440401142c548401002078106040e500500803911002c046409401c05130000c000b80510520428062a40d942e01d020003841c012500301044d07a51040180140c801303180441d038009800340407132107003584058107c5040707100c0d41c540c00b020300500181c00c7c204a4000c5d0001403c160304141c1150302c07051a1613000e03018020b00c2c1c04c030701e00600503040080c60011460200340117985080c1096425a83c03070f44010b4130301000c0804284d5491091443d20b000d6120200b001500c00da115042e083d258110007201180f406d01201400b522a180600040c801c0d60503281c25101294070102c450105a00da81c1010b80c114450b1181400310750700030200090030f21451030333070f4841150144d950421007102040190b00803940c900380100c0121500c00010400c0c20310851661100120f4a050302100a070b131200019055181c1c00b40403104190a44010010f05030144124104 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 5855403 1250 5854153 5854169
    0x32102030702030d0503100f080d020c030703080405041104031e02030c0312180a0308041706010501050a0806010806010e030f0106090c08090703080a020115080a060b0402090d020607060e120a09 85
    0x3403103007030380c0000d483e5112949030303034100440070000030081a0203034001c00040051284000c80243c540541c59218502903c280e4054403c2e200b214a5078140019003000316078104150340d042c18203000800c00584444002c904051405110110218a401d401d44921078458000c1c1801e000017031050506000c03800307050500c203400c601050030323480c0010012244400d004003082e03220388607131b0307800284510880d4202030140707400440c010079040b611490803012075a0754001c640c25aa42c0c0c00c01115180f150188180000d25003001103003065005544264006805050000f521144500800d15000074440c454a903a9186c0ca0200a845620700c01d1440d032050a180c8030380c00d40380801e003240d0f4418251000408030f001c002500da4015101b9401f00c2c0c4c000c91403404078842d01d990349696a558688088099580c02c2c0f802c10600702514061007210b001c10000b404a2401131100e400700300080d0808002591101c0d00d6084101548805101d003d0701900c14030201d139210905503a00800e103400940003011 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 5856653 1250 5855403 5855407
    0x11202010206010e1b0306150a0906020106050607020a0303030b010c0819180510050a0e04050403080105030f070810020703030f050103030302070b09120904050402010507020a2612030c09010203070b0103210203 92
    0x1640d0108031703034020035110b84149219500d0b01ca0002107100c19183c0642d0a402d48408244c0d40030f101d0f40001c4490840740c0316402030000070b0f00c4504101c00d511801c04001d501c09440700b410070010740260040801800141000856003000d51107542d4290300c01c690344003411303075015400010203811840d0408400110011103e4072418240400d07880007513001114148440454001c0c60284550b010b4400908042c0c0309109a05003890060851f05003801928400c0c0594203140e04400000034010040305c0714240282100030881d002d4030700035400041c00780d00b003580300c0503010104801c40c024a0f0080d40320347c0d001a660449400d003078444c1000508409441c3d04040b026401203201c10041d14001ca80032200043d0646551005984c21b02c55548005c1d00401c0b440c00004080c0800c0b4a0340000d200801c1015098001000d040f6450316001d00340e81d1700c0c986060021681c0071103184050011460180102d07450901180c4590a240720700742c1c42140c04130000d6283c6007a550b800c000c0c1207030110040c00114 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 5857903 1250 5856653 5856661
    0x7030c080903070209060a170a021005090f040e030409090b0609060a03030c0201031505090a0501060e01020a020a0b1605030f18010807050d2012060301061703040312030f05011202010206010e 84
    0x242c0c682c0302e26680644218241d002180c401c0d59010031700e45c0202440b00c0c1c0720015130403403a0480e86440d0240c5050f07100d000b5418100c00114000c008481e10b003c030080141200d0040300040000420f01c0c06a03041d228031081c80007154064040c458440f21501520241d41c4034685202000a1024000d01d89409550b20380c408000194001004010b40f91342403d01145000ca1044466550500c540c4850b40c03084a0302c0070300600da2a980e0102c1e05a070901d5031204604c0000f40016030362828940c2d402900038001c400300700f100400d810083c000c804650852401080c006845d43c51958002e80110040c49400041c0c01c10b1618440c0854411001d0a003800445403500c5540a0b0603402060700c500509600d0b07281801e41d8808040400740c41c01d6100d203c940d2100d0746410300b070681100c100c4119000b076280c9140480c110f040505070500d90780d86800154541415992030000d945a060440c1e0207240c0c5850b000304110070f00b800350a010308040c080c40701502d00305000080c94504107038030040040082c0341c11302c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 5859153 1250 5857903 5857921
    0xa0510060c1101120f020901170903070308130807050d0206090a0b07080601120204060e0901080c03070b070c030b010605120a050c0307030b01020a0206040902130e090a2a03060507030c08 82
    0x408000c6422500d1400900e102200684568600192040410346884017520000d0142e501030458410213a07128600880c00c9090301c0443e91b01a40c80e00a141d0041c4000c00000b480b6515041d806001c5122030200034020341d0314026250070120080310103800c0840d907856003a44c1080059401403c030710040241a00c42d841d14841d0010244c02c0d80300b000000b4001034201d9004580790301102044507021075845640715401007200000800d01441200d0040000400c408005142514204002e014241c0d4618100d0301c0506984229400c8035480300c1c0000c004089001d40312141d00801c0292181aa2400342c0e00b441d5513a46002011030742240d2900c02403086900100003520f901141e1820000ba601c01e8040045c2d04c2c050a191000754001000140811403802580203003800c4079080011044031926601ca9154661040f5441c04d01a4000c11200c1c01040e503e10580100c60b0194188043c00c00341c0880c10441a62682c0065030141d8460b828884047c0c0c0c548201c0c6008000c03032400401c02e0070007101c1 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 5860403 1250 5859153 5859167
    0x31905040f020d050a0b0406020a02070501020106080304060302070c03050709061403150106050a032004080c060705030a081b030708090706020a0c0b03041718010e0409020619030605180a051006 85
    0x1900840000c410741c010800e08000c9080d145c1c0e00421400b5080c074207440d228010f980115810300050107100e20019903540140076075001d0b60078110145040509040041b0000e4204d082c0646010b0401d200000108400f0302c05075010f81004100402d00505211003158030420426519009500001c400b01c0c42c03c01c001c0a160649001f440d0640d650b03019210100c02a20203039141a80310321101c650038041d9542030000700100c85582c002e40f41030380c00f0310040141d903005080010340369400400045803014800d00d0160f40c080710380c0848013002748450280804540044900c1c0c40820070030f4050005000007003015030005c1c855031000300020001d0380e0765003540e4420f610035501d0841d00480030908200469120071004001c2403019500c607040c0f1001d02e1210002c40d41001d002c03030381c1392042900d40e04042c0990301d40c403500504601d10b4400c00541d41802d0b4001481020304050781c40c4030100b0250b40f0480054918043c040d8020050700705000440b0840e800038001c12019140c2040c10054190801d01d = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 5861653 1250 5860403 5860433
    0x6090c030c0714010e07141003020f030c0d020d050a020d06050a06090504050907030204090c030c0906060c030c050a02150409060b03060102120a030608030f040e0703050705090f010203040b0d0203190504 89
    0x4600030307a080c00c3e003100380d0151050406100b00307402200404030706010040680303607064004507400141911400790540403441040450304598600f000000d00101600000300b1150203d8140180742a807581c400b07034125034003a00c59902080c1c0014803550035400383d000700c4000d40022a01c4884031403602c940509030600505c221030107240c4640010303211420503c010b000560300608148070054643c6400141d00001d408120749a0f0718804000c906040c441c8038010030780d05070b612081c0b00e1120381d40301600e6140e0748820442c4c0d00d21416140c40c0041c3c90b161103001400d031501d000561240d080041c15400d0340e882d500b11100000d820710400106a0f80054540c10355a21200c41d65034820300c610040b0003802854115168500c030008480c2d25a030742d400000c2040b998103c045c0c3c80e19450303040c0102e00b502c50070365000f8000341d41032105040074903256035000070351541401201d00c3c00c1d0f969980070340c0941040e000b07000340c2907020007040030400000659818403480d00c3c00410892801307545001200d002c140e = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 5862903 1250 5861653 5861663
    0x10308091215012907060b1002030711090603031908011406090604060c0c030b010b0a030506120a0311070e0c04030309060206040f0f0c030618060b180f070c0c0602030306090c030c07 80
    0x1141c846140c402c0500796945a80080040b135994404c18208600a02000c045031030256a40401c14000c0074404410b8504a5038049008016000254104046040e0242c00540d040c002001640044410300070103180c220419110382c64190b14100111140800c1440c400d4040c4a041203200303c6941d4a034116007d8484504021220101034181030f80d4410803500000c18401501001088116410010304010705c15a50240034aa54002c240040d41d440c0c40701401482c2d102c0151500068094502504900190402c40c0d02c1ca640d00c20301a011100e040c1e4062048074000581407050652100740320014004d58001040f29040907581c2402c040d00c6224060040b00c3c6c80707001c0504200c0807100e42c500850300310341c06014400c40b4058400090740d144204070791080ca4180e0584a070304122101c4145945c6055124001b5600c0510783c09040c10002c1c480300400040803141c000050710140c842c0060320860340250b44921380300d014441440805040503000036014010820724a2000c822240b50503441 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 5864153 1250 5862903 5862929
    0x1080f0a0302030d090c0e0a0203041104060b0315060c0706090305010507030203060a03060902010903020a06080901050a050702030d05060301060f0e0a0510030c090207051005160201061e0509070c0b01030809121501 94
    0x290800d045001469000721140c41f400b5401d01041344960713009540921f0241d41004c0d1446001400c010840d000c40c03060780c1c00d118007400022a0b109844c1c05034011140094055413034a00a12082410840c46811540105071000c0c0c3c180b081c44024416294400c2042c1021440d6041690000711140810b1100414050301d0b10301c000c045910650b0f448008507405420b0604140d02c407071015105d0034084802d04613070340c038120004a16030b000b23014007400740740c00c1c1e006140740c44444401c0c040a4440140b00130f4041d03481d010002403034084200410014608140c808001d0700300501c10006445000e045096010440807080c00452030514a940446000b10001691445145002410300c400c099811400340c2c82c5c14104100b818034940305901841c02075000f04080368440e00f2044441c01c02140382c0040b45982c0f1030500007410300e8002d954101d41c03a400e01c2052000f195650342240c101c2604210361004001c2800d00d80360038002c0c00c400030344000e10b0180c442416030f1940302d80352400501ca00d000706400303 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 5865403 1250 5864153 5864171
    0x1707030e0d0302030415200c010f0e0301060e040302060915010806060d1e0804090b010302040f0e04050a0803090d09060c0201020a110103020c0a0602040f0506030108061b0d02030f01080f0a0302030d 87
    0x8108440041c18105001800440b40c00b8020380945440080f4020308900380903589a4890045030382303002603074140c4464100580c682002c86154441201e581c2d059969241d01060515048628034441c1d0b11a900800f1030f483c00c0c80d2080c0c2080c201c100420400f10350030380144480380340403a400340e0200c07082e43c07200c000c00ca0a00f880680d20071800f006d1001603070300b41904000d000f03941009009a82c6200000c1c0224620000110228407882c49400c40859101a040c800a0300600a0301e40050049040328440b1103d40c0359541694000e03107030742e0b050750700181d0103007505074024422000410150a0072342da00310440e00080d448011010000f0004c078550345800c101c1703a02a9050f50700d025038040c01c54518203807910b0310b0b100035400b80c090303d0304030b0701152400103061404030b0031203042c0c40781040604041c2e2249080341c032038404c00c2030703c2286120091048940b800103c1c4081c0d8802d000850554140303501d4565250300300500300b11440350300d8200200c17500100350004200d4443c00710030000001c00f001 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 5866653 1250 5865403 5865407
    0x2060105040f0f0c081b091f030e0313030203060c1207080601020f120d05060307060c0305070204060306090501020307030b100c0b090304030c03080309070501020c0d060f060e0a091707030e0d03 85
    0x7400d81ca00d03551207241400920301d045c0e0060b5114424100d0360103081001e142ca801c401240d00500044541c448a680e12001da0043c004602c0c01d41a8003505010a182d000640720a0071500002c01500b1049c010080030000c3d403504100b10743d009040600c6e002e1604980004846c2c2c140c800601c500140031526020810591080240d0017400c0741c0d041c266400f440b00700c2214641c03948048071003c034103410040810400e103004601d034822614651a40034113000b140d44c0c10ba940d40c0154a00303a90040d950321001002c00c07500d006504c1410300c283d00040c1e40f86002103010301158110f030401402098a0052550441c4c1c0001d50010041d03080401a19140d4580303000034514072860300020091800500d0000811900e84082c500a80c0c0c040c096928080e21407004a0f41c600c1c0d10f000d8640c2c89103413310b51101282241c1d1204810741c11800c008160303241c581120b030307900240c15500c11220a5407008400d06001800c2611500d00c0060503203c0c0c85e2820356200200320962802e1614490140c4c240024100f42c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 5867903 1250 5866653 5866661
    0x60309020f03010f021b060705030601080705120c0c0d02010506060405040b0a08030c070501090b0a050a030203070216060f0e09060a0504020306010c0f0308010317031b030a0209040207060204030c05060a02060105040f 95
    0x400400a1000740d480740c4079000a500002c050742d40c9041003411b080035074400800c0052040c6410350320681590b40c0c007001101c840a000d800e00003845800c020701d80d0241c40e14007000d03100707440c0c0600c6c007940c40c0020b03250b02e0316201c480000b100c21a4941414850b240d550ac1c001c807421108222004226155480002142040e0590122680c3e100000e6403641c0c030003000c5000411608240c88100026659002160740d030304ca11150800018003c01010190b240241d01468215240d841100c02c080c0c0c19039407882080f440b5802c810301103101c0910280000350f00c0b14541510800a0796042c50906122010599004203401418407039074002c000a03078241d20525542201540240406440012030b0502808054084c00240c500024202c00e60200f15a481c0490303000701c80c05884801c1036401950b0400c1d954001505c1581155002c01c0003056694450003d80fa12031f00507180142e80d1880d51414082c134108541c4552701426050194001054020403403504440040c1ca010920341c0c481ea42c2c4038010 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 5869153 1250 5867903 5867929
    0x5030106090504020301060501110d030f06031a010807120c03120314160e0d02030604060c09050301060b04092a08071403040803040308090303091905030c010e0a110d02090106030902 80
    0x540c40c0840000d40d501e020b03085070f030045001394002c0100300c2d02e4400440b03420640580404096004500501e070340341c4641d00020b100c181000c070014501d512030b50341070744512106510381010456100140f2440b64244920001071400680040c41c00c4082e0b42c1e05500d81016200c00b61118001014103004a80030760442428040400d000155504c2e001d80c3c0e450000b08840040b00002e207410b00152070038105645100c40450300203008106981d25a030f0b42070003601e900d41e005010418400b0300000d06403024000c85001e0300760f43d01020746039410444180e0031546451000030394415001d20b00005105090344811443c400b600d006030080d5200e075803e82d03002c20b00c466030304a408800030800042c80112406140101d01c69522811252908210940daa02040c1c44071034054014043e480d0390603030742c3c1c01483c030036522520589040080e0014060300b11105900194403a420594102c1d08014091000c0c1000d6082224a0201f01c41c054010410311001409002c041c541d84005280c01d5689040f02000c0d5 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 5870403 1250 5869153 5869159
    0x20f040506070f030e010804020d0b0415020d020c010e060105060a080702010209060d05010815100b1c06030605011806030302030f09060909160e06040806040201050306120105010303090f061107180605 88
    0xc2d40b11146440c82e1803060054090740011400e014455040d0701c0380380164050758009056501031a51074944036284000548100c8000745c0180310b681c400102c5002405107810f0010b801070b201c0c000b00b0440c90a549820b5480e036540d0308a00010301150b81c0b11000ea0b1400d00243c54540c1081e552001c2c160700a05c540ea40c0b4a0b40000c0105001660414a0704114142c4810b2816a85120640c00b014090074100360341c40c600351028440d0900411108001419480c0c0700000b2043c0c102c80d81d8a80e40e0304840603a00181c0d4a20f4890b4014820100b038422000020900d0403010880c051454900035100d0186c44510004036200041e498065650716051300c4c40ba0b000206109068144260400402d141000500000c103180d101524914500070041d10102c68000b000341586540e164011240350340300415081c0c3c801c10b21190003c13020800d02c21107000e1482a202c9100160402d1100103442c08a540000c04010041180c0d8102007004110b6a0480c0e03500e401c40680c8000042104000d007109030083c2da0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 5871653 1250 5870403 5870407
    0x111060f0a0609020304020109030219050402030f07020607020a050c09151206100602010b0d0213110703020703030e0a0602150c19020109020a0b09030a110d060203040605040606080c1003020f040506 87
    0x10361103180d1018a008000d1514100222582c42c1c03850003d03804101c0300130b800b0905914080016080c61001c04848115821022000d15100c1c000182280c00954480941140000400401680410080e900040f86000912100d10107a0b5405d81d40c1030000b00d110301900f401d1002ca00c0b10422441c000d81415401041c403c03034644d99000322655150300b1100703500c9144c0103a40018419006114000c4000c07000b400c0081e0f641082d40901410744050b0f20001c526555a40901e103092403400060722580b8826800380200500c1c50500070080d000740851188210000d14082101c5a0000380600704501c00301c0c5007d525540f101c3c0c45040500505170304404d8601e100c1d10500c14140e040d031211000701e100b07c075640501921001c41c1c810901684501a406502892a860106100170100c94990300c00400c024012642981d0715001d9803c140d40c111406504c0b207080c001007203190700840d030140c28080d008180c1112203c0c001001300410301010381c1416130004507a04084400800c0728060040640916 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 5872903 1250 5871653 5871661
    0x20304050606030c0a0602030703180f080303040501050c0f040302040506030a05010218010801090207030905060706060305070e0402120d050d020a0504030606061107080f06011503020d050f06030d0806030a06020702011106 97
    0x15107811080340c44610a00840441003400d00d02442d501d0290341c400c0d030085041c002d0b1680c09071280d00300440c96040001032301c0800240b5005a0381441e0181015101840e100c0c101403420b2429584050a0314400e003005100388803a000c03000c400c1e6400c494048502007065240c81001c05e0414009005c06400e80d40000741000343c401144130602200c0c1e1080ea03d1190070703a40c801d9400304130b0140c0c0100400040d42100108171511344900a401410702a200020710346070b43e40c1c4c1b414600116540b115a160503060308003c194034011541d00084c5808802400d5070300f1044000814500c10341c502c0075031440d4045007040296102d035041da000366600c1401005102c0e12814040c000b044480240c00c0345115004001c80c4404020500c0581482c2074401444264200000c5815014031081c208042580c01e01024a01041c42e0080a0003070001910340445030400c03009040c10004505036600c180207042091010b90307140001e412610341d820440058035611940f00403141d400130901050071502c60b0000380 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 5874153 1250 5872903 5872913
    0xe0a09050601020f1b0409030512090105150117070f03110304060b0411210a020d140108010b03011107021e120607020607090302060a030e070f09020c010c090e0103060209040906020304 81
    0x810700500302602200c1c00c25401c41c040c0390ba17411050141d07074070100c000b10341c12002d42000c0e004012a14481c1c20501c2c140301e2030140c85000c584045503071a01d1a0b440e2018040300e0849e0104140d00340c182881d0918aa4084400c3c1c0c00c2405009070a1000f00450320302c42040070f45c8a68418500ca015901415603a81800d003010780c050000c03420014411807400c42100700300401a02201d06414110402185801c0440342d0002d40003030080549c20025000c0010000070f064a110f03106c0369400000203c1d0303440d41081e035120708480e880820607000e030303161801030402060302d0420740c0c00007035044800c0240e0010b2840b00000c0404410703007903074011100d4198424603039400b10b03035035110344c0d50380e4211805a0754900044410340194440a034010f40100701d2403103200c0c8681c0007480603450050850b00e85c19a00c03c98448480c246601011046502140280085000303018041c2d03110294644298440d0504001007440c1c4ea0600c8014152940042c50400f10b8503503400c1981d840e50821011903e0f40307041c0c102 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 5875403 1250 5874153 5874161
    0x30804031101030603051005090c090a0c08010515040b0c0f0105090d12020703090504050405070302120309090a05061c03020111161b0608190608030d0c080f040807060b010e0a09 78
    0x454507108600348644003540319110301d80c1142d8010004011580582c44038500030100540090564000c0141c440381d16141c2e1920b45000e0b11604000251042923810010001c40d0181c01440c820184000070060301481c400c1900c0964004941850780c402039480403502d0100c81680c070004650a143c01c11a102c14080307130700160082e20740c44501540b14441d017600d040348607014000f004584491028811b42c102503200c26031241c41350041340c00254482c1c000503181c5e950070700709110aa00c001034040c0141001880f06802912103c0c090005040c520001556540595260184600824510340c103152003500702240681c2400d00580c0e50b00010f400c540080c045070102079540d4000444201070405c0072a03541030407075403d0365039807001e5200c0c40010300b29424074000c1510007549408001c01e644109000030600f40022000024090308140c001600b8824010b106612002d83e95007008003082d440822035001aa014000050382c066450058a20003034808520b0307088a04080302040020150f44 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 5876653 1250 5875403 5875409
    0x51b070f0602031207030606020721061b021501030203061602071e050406060509010c0305030c09030303090105060301050f01030f02010c061103070f02010f09030e04110c03070602030103020a060c0201080f100906030804 96
    0x800c200a5817030000690664800744501030050b0700003d0200151401030303289500319540d0442c42482d442154403038100380c812015164222110030201440c0c40c40c0c042244140a80c00c021002200358034680011382c131804004c0c15460300000c06241e1070b424520034000c0c0009001c1000c4001150354600c00003503803032030b5640503840c0543c0c50700e04040b41b014000d60a883c03407084169601000d0748039581d4106c49603080a44030703841e030240c203003d020443e580900c059072041c4501c600004d90b501e880750400d03007503c102408140381c07662198014004128480c440c50038003502800e201c80400c41628042000301070552074200070700c0000c000d000907554000c40003588150f003980244900740300e45440908503450114001c01107140021902c0c0942440c0d0000d0207101c0d1410302c454100028014107a0443d1f0103000121140c80c0d0020045c4214501019000081e1109180c0600b1641d029400138100c0b50f0058101b890302051400021030500001210358040e11040d0750505c409542ca1800e00c55540140c0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 5877903 1250 5876653 5876677
    0x30309060210050906061002010605030d12060905010f0e07020c040c0206040209150a06120207020405040b010f0803040302090c030a0603080c1f0509070302060304030c0209040b06010e0f01051b070f060203 90
    0x5140c400040480d400f51134050502c180203010b4907240c017010801081c0c01d10700900e0642d500c4140000b619501400420b440b000961140c0c2d08106076605e00f40d080b180d140e040382c150203207040018801801c0406014043d1850580601201c4d12030070401c6c3c0c40c003031035008810790090174107501d90140f82d40414500d006031b1003a60009003540f03804401114034030158002c550024009441084120300c1011800305010f9203240040c5070035180e4021600743c600c111429a0f1500d4410010804040307828101c100500c0510007440c06c142c2554001990010b02400c801404a8040f0100e0a0080694050381c000c42e4803000d419555000b64502d15100c000b1484860500800c03840c1c2c0f990343c52024000d880c4640800c0300680904c0341554200299038001030f000354100f0440702d28000c0142c17150038105001d180150b0501016140100c00141a59200580d203801540d0400000c0c1341a60030009644481590003070215210f0701040c895072401030942c1c022000807808510004038150084000c080c406d4a00c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 5879153 1250 5877903 5877913
    0x31e1103010903050a1b1205130305010203010806060312190e060d06180608010608060103060c020f060a0603060606030207020d060f0207021903051615030b28080106090b03060c09010c0206040303090602 89
    0x200b080c0c0015503107100c0e0007800039190140011f1405129100618254015001c0305180c241c6031784500d802c913002600700800315480340007448000c3c0b80400000c0c02840541c00a20b1810060380b101650412600384000c050007107086020b4071300d581d45c005442d00f0b010741c01070420050b656000c00e0303440b116080c00ca400100346403100c082412901805400140c48002d0010140d5928650b51000123052010b51082140501c40607120f00781c00030300c1040d000e1071041034041025811401c1802c00c403405640004280351040201c000161944200c0c1d5600d950083c0300084c90b0012101104082c2c030620380020340c0702c0c80d040c840c4954046894181405c1e20b01a108540c18440030008000300149a0301481d0000100500d50090651280c3c2044c1e02100c0064103210009510a00742e075880300d10480c1c5c9902c042c02604052120000c02d01c0340e03500402000b6024410099250301181d07c85001410790f42007400001562492a4042c043e5401669030150403955140d9581c00c0040c000034940c00f40000601903 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 5880403 1250 5879153 5879177
    0xd050f07060e04020a08060d081201030b04020a0b09030a030e030f0304030303020304140c012c060c0105040b0f061309060605060c0303070212090108070c0203120c030a0201060807031e1103010903050a 88
    0x1c103109817569190192903083c86610b440c03003045100303001c40c141200d01c010200300c031b010b00d400c01410301ca00861280b207640c0d00d01d0601e48100103004100b5041000d01d201d06029920a90740d0000c1e445c00321540500b00352282c00d1a01010034140a81e5900740d91261000080000c20541e00d6070080d84110300400342c0034040c20201081649802103080e8990011b034040b010321141030080b0744204000c006100c0c203412a00313a0200411004d0300312a9818400365952403c00c41841840340e0724a80c030001404410503a071505400186040000992661030540c2d265448010442290b02c001d0103440000d141a40380c060088510381e61f45d000321410001409807120780340c03082e81801d0a848039810161161605030b40c5034002180c8c0da6500c2003099074180300309107081d45102c0d03495008001140348040915035410541101170b00703650183d0b0204505600084c0d00304041640500c02540003202c100f4400300c10302960400a4290001d42c0e07020b5450352078540c800341090f80000c002c04001c941a00c074582d01c492 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 5881653 1250 5880403 5880409
    0x4030215040501020d050f0c0a030305070e01080603030a0c0309050a150f050306010e0609180702030405100206010503120a0c0501020a020a03030506040513020105030601050708160506010509071403060d050f07060e 94
    0x2492042d5030250748188035402100d80038401400102d43e2075040300b8148056600c0031407401c0703503d001c19400b1950b15014840e0711a408444003c80b01020f00300080035040c04000f10f0760764803a081c44001001186803001d8101489255088010301006082d1400715840b10002001e6070009900800820402c85188000d24050816648075000c16158012850741c0b600600c81c5a03840b102c0c800f6031014003501c4d00310308110703103030006070207a51668000c5403194100810700945001ea4500c047c1954011001080142e4001420340d030401300c45c4007815102d8202c0c0005440b07100c5130860091070f82d40085028900345a0000e501c42c241806a9024012a1036505c2840100e031026683d9520003000c5a04410155000f00011500102c0602d01f540c42e140c0a070301c684019400c442c252080303000402a0802c01d00c0800c0250724003400080302c1c8100700d401c014401900030540a9546e945420002c80002d08a5a820450045880e0410f007540d01c6080c0343c02c1443d40f03900030342c001c00c4041107070300d42000c040342 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 5882903 1250 5881653 5881657
    0x1060212030109020f040b07060b0307060e0609040c020a08030115030b0406050f0904080f0705010204030204060b0c0304030303090302030405040608010e06090c01020d080604060302190311031504080304051204060504030215 98
    0x60350001a5600d03503420004540042e5100140c29040c6501c00c01001400c01c0c0164014003082c0d00074580044c520b0741d060200340c1442c61541c8100300300030181411200c03943c0c03100f00316810b645d400c8400061101c0028400da0608030780d21809804c525001c4000960300320b00600b80c506503036181d030782000344001d507034200300c1290101d003c1c0c907811030703c10020a205e500781443c82542280c0106806030404003001e0200506611451003160300e030b500458200218100f901542c40030b00981140c0500340130031046510b5aa000380d00c009400c054684c150a02414001e1003110054000504140105904c404006006e07105483e00b904040c840c8100180c43d8040104180070f8007a8141e002e0048110032107012113000d0005880503900c9503603804000f0042e5171340603000c03880b0780c8886503070b03860107146082c0807880251003200c4074041c1e0006486095203024000b080c81d03000358403042c40358407a03c45017006464080c0310000b0410502c0300081c080f9515070040d02034030450340f088504114050540b01203c6c918 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 5884153 1250 5882903 5882923
    0x60405010f030f030e030105010b0c010b03010203070e13110a030921080114010302040801150303091e030807030507020406080105060a060c0b0a020313061a090903030402010801030318050901030503030f010602 92
    0x104050740ca007800042c07001c8900c0c56400b03020b4030b00440340741e0203000003d0031030700280c3c440040c0c5a000034100183c0c54082c0211800c90b4411402181903160150016100750200302110340314204000845a40c111694019100680301814140c0ca5403056034000c0d0007882c941006640744c8448070385800c1051032510f8078000560060341c580c030541e480d042c180301c80c1c0914099001d06054080c803011800072400d1203020004070345161207207030701c0b40740d800c000d80021429005080501b0440034418150040518000116980034540e9903407907081c1d0500b103030b640c058100000e5005007080c0c40002e80710015007125010380e904813002d219165480409079140180c020b4005e08404c140e40015413100500e0303001c0c0d640000c5001202080c955244d4905040360b10110343d14285141c0c5044403070381f50504e12401903002e0300101c0158a14286900043d190210502c001402c20400c5401500c0f204031148c0d82100800c0060b10302801561680f800c40c1d141d8100312000540070340d00300000280701e48005094521 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 5885403 1250 5884153 5884169
    0x3091109150609030f0616090503030a0207060f030204030f05010b040b10020a020904020a0509070302030a060501050703050904050703020d0207050705031606090e040615080c0111070f06030504020a0909080a0806040501 96
    0x1d00551003052054035000582c2c916894000c3c40d00030603003120280100c0344145603010800921459611019200f140303103410090081d4400d0014502d0b1a030001820350030390303903941051420649000b000f10083e10890b00024081c4070145c1c4514200013054000b00f000b4002160180026000081031190715152120f0a9006a02240340c80000d03080c10600300b50414006009043c3c0181c617000807900d010320903529403000036400000c10408090500c14500904400d281580c9001500d0f01c1c001c0c918000c5440a5201c0d0b030f034035004101307654000d0b81203513440c6028450030342d10380026041503501d808192054a0080c041c81c048240d40681c6c0c0c21803401940c0964892041103400c000c1c244043e144000d10484c0c030507540e608090310301c542941c20742c002000b84030010b00110841c400010060b001013480343d4455480101c0c00e010350b000300c641d040d09462582c540000d480d542c40c000614480c0c5580d0082180340d11341600401800313119002458110a00d4882080b0b5840e00c206000c2191024031a1141d = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 5886653 1250 5885403 5885431
    0x403020909010f110304060b0603040206030c0a0c0c091a04050103020901180b06040e1e010b03060402070501180b010303080112050303070c0311010507021e030c0c1c0501090303091109 81
    0x145412404507030400c502000003d0b4075502406100308030745156010702001d041c040100410003c0d14000d0100842d404d584090850038298040742e40390001a1080d400d861020480c003043c244600d81c019407030784e0050003101031140e0f00d401c408002c00d0301680d040c1c54072402260080140c11b003400b40504a96000d04003000c0c5a29020034010000c1d031412469200740d4864000620310307580c04002c0e1001c1c0c03000c1c00c445021401c041c000c3c0303520101c50003036111840103020010004110b14200b56a40300000343c0d00543e81e400075107002030041111000403800c4518515102007441a04510740381681d2280d100c01d00c05903202c844c04049948104e500404503841080007601b030324402e80d0b52002040c868141140751070981c462031230079500304039103420059104c402d1495038103260784107c84888030110041d600c2c113058041003548a500003000c072800307100c2000e038102000710001583d201d4150040000c1000422900c0c0080203800404c0b0140d8a1000c0342d4110340313943c644550103d00850588464031 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 5887903 1250 5886653 5886659
    0x6080f0c06090f01051c02031006020105040b0a1509050a02030106020f0708030a0c0204020d0e0607080c0a09051207080f0a03020c010306060e04050402040e03040803070507090506010807031a060a03021201090506010504 96
    0x101c3c026402410707040c10070406000c0502403866103c003070640080c11280140c1c4a2030401d8100c0003101d4164010b104580c1854280801f0170040f00820390813040c04200841c0d22490071607642c04d0b241c0d1a41c002d8031244d250030200011818a58080e6040c2c4109600b82c406e81c1c0c1c00703144400d0b500c41c01402003150b650420080f4010380f902440c9000d09561002d40b0250402c2d0b5244030b00030072070f014488c1943c0503421113410810030b154460700780350303101c2490070380d0605204180305c006001d080c00b80035440c001c02c1c00b401207540d200c0301000f0399801014060300300e480320898500a00c1d1201000c4100f01c003d8401d2450f8000d01d0341c000d006c5c220a4602550f507860040c40d0042c200000742602038410b07a00165140c14070201120140018030203001c8010085541d40403500d02140f0b84041940111902482d10051019981c0d200c0000b0341c0080c0c0d1480d011503612280e41c1d2050902070800c501c1988038100258060356950181c0145c0883d0400440c0d1942c16a681c05506d8256501250010b00080c4104818 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 5889153 1250 5887903 5887909
    0x60e0c0a0e04060302060a020c0307050103060f03060b030a02060304420209010c1209030308090a0809090a020d090b0a0e070513110c010f020301080d0203190c0201020c03070906080f0c0609 83
    0x441c40c2400c0042010440310342c4da130045281644081c10300d10040c0c220118000c003900b010400e0a004250a00e42006031034900f40408000d03000c20b0000800e0580c5134029484180d40400110f0703111600200302c0b9560b4105842c1548424646d50940b1040d201c1e40d140080207201115114002078044040c604901c0b581442100c00940c448120241030107498650b00c40420801035006214195941f03465240310300714140900194401002c0e0081c40c0d010b040d01c000041d02c1301c815164610300548154a20351a0704100f80c0181c041d110180700054078040d141e2041c00a400109801180b05400130000003108500b0240c07112460300455400403c2036407843c400d5061503010210100640406900704190080e100e070a50704400b0a500c0465004401440103600c10720030040f11456a0005518003018141c40c1c00e0303400300e200324913000c0c040d03141303104070942e4000e2285280e00310307008050301c1d140381e00c032080400240128040e10703615120b0070410300700c030580019086d40038510041403141410044420 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 5890403 1250 5889153 5889167
    0x102031905060619180608070201110f07080702210102030f0a05130b06040603140a0201030606020a0b010b18060a020a0605060f060f0c0102040b0d0b010305101212030b030f0303010306060e0c0a 85
    0x310410805203155245d80440b0208807600900881e50b110305081c141820000e0955103950203807807a03014100081001c805509040700c0c00d01d035200c4240c5403110b80500004080c0d4064039500d442c4c0c0c80e00d0055400e8050350640c015441828000042c0c00750361100350780181181d004442c2d4041c22303d071500c0400003103480c410295900070001000800e00a40301d90311784ca90700d000e590440c541684445002c00440da05801428003034a03e902c0180828202c544030a0b04000381071190030410b042c002107583c01c0b040f07a48842d004000001d4140c90f62a124400020341c4e80c0c0e00c050041da1090300d0700c0c001c82c84900c1c2c080c0f0701d0700c0c80c01e40003000b4038204180302551021a500505c0a040702e503500f0080021401801d401605107040b0305100020ba2000d0322002405880c001081c210350007402c48000e0000c85041c9650061040c1c216080c07041098088209900905644c244640e00d486504505a10407500200960680b0311880c0140310655a41e850000700003002da41c1940001e1051100320075191054403 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 5891653 1250 5890403 5890447
    0x50601240c1103030a090302130507080703020702010207050607050604020111030a0207090e03040305150405010507020d050d020d060b0301260703050a0212120d021b0706020c010e0103090b010801020319050606 92
    0x141180350011800c0000d113598810240540425041d0104005525060a54015440410600f80a903281c032100040c02800000c0558040c07550101d105e0040d64420400c400151030041c000c0303990344100341442e60b6100007c480486c0011800e000d05d902c2c51a01006540b0340c0709150b001000c0007410510120040c020200c0d030ba40d00c0d88402d01000011800800900c4148000448800700c40d00301800c0c80742c25604010074804c01c0d50300c030900b1514080c2c0d101084900d42c00707040e1801a2030714030403031501018009542c80f4004030b440100002c501c1c12100a41400d078982c84a29400b5401c0450b264292188000d220103401508052030b45000360030828400b98000d00b01005940701c3d041a640a01040c0e0003004c1080c030003560206002c1c111420401e410520b4501310300003410654500000259102102c0540078108000400704200d2640203802001030182d100030440301c10340e15890240d000750000c660a030321071a0486120302b5810810300c6194007071140600120724080c4c90f05a41051502400 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 5892903 1250 5891653 5891663
    0x7050103021c1401030302100c090509060102010917090109090506060702040e10020705030904050601031404060e03250201021c0503040b10080a0605010305010510240207050d05030403050601240c 86
    0x4250111500344500c68030420f907101ea40001d0081d41182402031070300b03214000020500303107003400165071b03590440300e0b040031210200d400003017a94070500100d001d8501785a000704004040164814107150050141140c2e0307100707070b1300c00001f10395401e207040c2502c406444035030f0010410050b24000d82455000710180461540407284100400d02001040381d0241b0000e0310142c00c04500c9002031b14081c0580e0f5000300c801d180c14042c1c000074030000d1403103c0010304000d0456030303940031054034900c061003901c43e42c40254040300c0801c9544000700688220600381240180540c05400180e0203040780070b0016020655101400c50ba1a41d4414401e030740c014080d03e61100000b003000503241000c002882c001482202c0204a81d495443c0482c00d4a1019000d10240001d0920500040c040083d0b0840f11742201021381c40ca1006002c000c1c0d003843c1c03035604290781080040c1402d40503c10004001c00c1200c1c82030301142d040b40e98440c10b80012030381100c0841c40b4403800c10b0300380d64168420b0050030030f41ca0240c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 5894153 1250 5892903 5892937
    0x140f0105070203060c030604050a0603120c05010b0a060503060405010b0f0421060c0309060e0606130b0a05030307121101020304020f010507030306170d0201050f0f0f07050705010203010b0301051906020705010302 93
    0x1c1d40000c1d192910840b16150066000030800055041600490f60000d4100380e00f4800141175544444c50042800603020400034401c0e69481803040035000340d4424000a010301d2601070303d03550003c2070307035104844181c02181818000200d50070303040f04640c1540d1910301241d04150402c1c40e80908500501480158904403050000100300c80340300e038440401003a100021a05401e20709a401ea4803820070958441d00321804111540d150b011240e00c0002075010b00190541100001555100a03504065050311003c5440d40c10480c15903034616002c80262038030580341c5a4420103d0a034842240c009410242c01401d40000d0f5000e28060400315100382000318940e40c0f0741e42e944800304000340c1d60f91610380c449416007907225028450140c221011030b125017800c0c5030800701110950310190558501d051940009024540315006075442e4507070000003550381c1d50b51a000101d05030400e0258911513290b0001c065040103071040c55904a034415005045c500e80b03000c0064000750001e41c4440304c0300440e = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 5895403 1250 5894153 5894167
    0x1208040801060902040303030b0a03051009020d0b0106030203040c0f05010e04020703030e0d02030a0e0301090c050d080403050613020103050906060306190f09051b0111060f0c0705030703020109050d0207140f0105 93
    0x7800b030000a00325200c1e005888038558240101981c43d01c0344d100d406003518440500c00f00c0d02c0415070482881c28890003180d50101803000c0382140d80034260141c003505d00c2c5400810010390640081d80140c1c0500b005021182e01e51103015000740151180c98080b41c03035011008054202078014107213881c000e0030700103115441c00d10024100b42c541d40c45080103070800903011071515007110701240304800540c000c00180e24a41e903480455403060082a1182c2c416549443c1005104c008450282d07030b01009444890400c00d0030b032101d02b000c031542203000c68103080010300c40420000d0703080d1083c48010b000341000d4664800d020360030520080018411038039040c0f40044c180c0e050041000c4a07100c0c1d00180700380c0c4007902108a1540440ca0554104004044c6143c3e280c03000288981e00301d060007080c00c010351510461040e8500c2032040081c41404082500810300d9019480030f9103040c02201500c00500b40301a0403a1078008074011040904c1d01034449074910305141012900f15041814990b02d00070f2 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 5896653 1250 5895403 5895419
    0x3010b120604270204050c0f0708070f0210030f062103030c0306080d050c010f0501030203210403141006050301050c04030f051204080d02010c02010c0504051003060b0d0b01080903030103020a120804 87
    0x302e00b80c04403c0c03540200300780c0c218149842203e50010b20307902d02e40d06108000e1044140d603c01c0d10000786c40041d000c1040301c180702e80c40c0c611440c2d01c3e500034204006102c5042d0003a02804c11070039003201c2c440c5071000010700c3c407010f1440b415480b0b000724422001c1a5003683c2c264014085030000c00205590f400001c03501e290204403172050a90952a4551103050811030139094074001403034505a98100401000162000030b818000c0c2c60b90303c1120541065241a4a0606e00450b8406401d40c00c809040404052000c0780020032151079400c28840541c0b0788040c58240c44065a0b0209114401c20041000c10456001214000d1242040d65950006940700742d030320303800c83c2c0c228890326040040603d40d403680910031a640c00285000900420002440c042c14601851003a9405052030040a580d4548a5440403001d4100e16240e1a191165200350800500000b001c060214601401054400b840000bd690481c1d900801c03200410b0b0910190042111748480201e81d004014003010403130703803 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 5897903 1250 5896653 5896691
    0xc1002180901050301060303140319021308060703050105130b0103110a0e01020d020c01051206010c02040606030510050607050316020105070606060804170309060c2a03040302041103010b120604 85
    0x40ca03050a100301805030001045503180d0182d010030f12980c90300b2000c0001035005000001000261441d280d10307961111021a0011000701040e200c1c3e80c80010104101e2107004512030527200f1050031224030760740e80082941210340a00a182e40418008102e90744505d0903080128071107410326000c00d04005e072070240b5007a5002031901c00080780b81e0503030400722540e040100160003e1544020a240d040c448000303030030341c0301c0c940400d01821010f0340040c00c07903401810618201356014004102e40c1e80e555000600404081d2007442c4031401c0040f0009140c90548191881546c12002651510070001d00c000b00254800d0f500300c0c14480203204000110300700d489044000c00c482e45075200503140c2450042402c1245485404011200348140031001400207004c59000d89890ba88503a260307491075140c541c120028400c500c2500400c151100f070160084090710403039200740c030148650300f04100c070210305010902075211204002e001c114902d440c1c02402d04d4000c4405000040c00c0c3c43e80c41200107204c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 5899153 1250 5897903 5897917
    0x30501050420060301030f0f0c0503031224030709021e040815011a070308041b0306061406070302060417090901030501020703020c01021605010e031005190c020a0b0604020c1002 78
    0x305814400800003250251540c10b03039588220380782d910703641c1155202000311485160250003090400d02c1c0c80304200c039a40c80365021700303401400c41c0d80300e0102902a0810035401c03600044054503078040c0c504501141005c6088a00d002000f40161302d0415042038000e4104400301aa200000301510414a01c801c001b0406082042d000e481441c1d200e00c600d040b042c0701a440080180080c042a004407038210056071840c59140c03500c0584c0c0e8445040c0f10081e102c180301c038a14224484003002080150070b0f030192003210034420707141c0010482201089901c1c014414081d015070846400500080c0e034100d0701c804a00045c1c84200d003000c00074000710702c10600036003045800341e60024611090540422019102e40c4c0e0910003014481e42542844e8031a00b290711803d41406000c10483c51507940030b2001214150440c1d50400051820040d55035a83e03500b0145122154a4980e00030a054804100062460380110910000d601c0302c0051000a500410035020307a400ba12044c2c1c4461062030005201d1 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 5900403 1250 5899153 5899163
    0x909080408011a0d02040203090a06020f040e100305030301031719030603031206150c02060c030c0a020a0e090606060306060d050903090103060b030610030b01090e0103050a0308070e030601090c03060305010504 92
    0x40d5400d2603525800c4601c000c01d900c0b0b540c1081c045442c010380d21560741007a041c4d4161000b5803251509440c2c545403508050000f0100c900100e403800c00860312002400482e02001c000a0182d224120300f10400350b0b86010250140e0402c00052021568880c8003846100c00240d4451501d0749200f00a0070440080b030001001a41b100350800c02e042e40202c0b20000116650020030103a4580201e4801c1c07a5080088102400842c03100714096550300c10590300c8030000380d001e0706c0e507840580c00c90a07124a03a81401724400c0305115408582045001c43e568440d0700f840000b051581c0b02c0104201d01c80d08020021a13005000b00700c294a20403c502889006641c050029070300c0b410341038005016200203800518034010180308000c0c5940d18103480401011060400045030b0742c0520040307529401d1504000d0100001c4000081001800203894548074003d5a8440594850380720440d0301100c0c0b00e220a6242d032010b001070101036800c1d8486c4403c2c440740e080000302103960359200c50a4500072074090316 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 5901653 1250 5900403 5900407
    0x306150a030204030b0105010513060305070306030803160206070216030201030510050d03030e070b070510090206070b070206160305010503060f09070810020711040905060a02030a0212010b0c07050108060a170304090908 96
    0x4211817880c1c01c602404e000d08107203081120700c0381044500800c40c41801c08060f103030408901c801c1d00990004003c1d58020100c26900d16241c4e41c1030441c0e800b5804100f0052060000103100305101007903414008001c16102c0050700d01d1a0011400f03000c0c082c0481d1b82480000e8000942503441608072000284282c9010600b004240107450070b041999006407502c580801c03082001030004218103a40c00310b0350303400007401003650000c11601d014540000340740d05980d20a00a042d0b80015816100c2d0ed59815904626582200c048081e58001c0c0b06041d0168040000310321140c40e0985201c0e030002ea1001101c030b01540c3d84605e289804118020051f030300f503000807003509114100d0002d003085101598244140c00b00c40d5034042d528500200350440161b03010012a10b40d100c15011075212040302c64000e40d555840302039171102a4070055010105203d20780b0002000d50241d07100b00d20880d0004c2c82e0f40d810340d14186000800104032008050180410080403410510600c16400014041d0101c19 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 5902903 1250 5901653 5901659
    0x140109111c0c020c0909030403080c0c030a0f050c0406050604030201030f0b100e01080c07050607050703020f060f010e060f0907030c030204170303090d02010501181a0904030806040f1407050306150a030204 90
    0x1904140001c0981350140c0c10010070410600d10000884080369800b0305a960f80f040343c0b009003402c0c00c15800c129036041c029504902c0511000b44071030780c01c150140058544054240c0c040200f1940036100c1c84c0d4100760300340001c001640c081d50010a000006403000700b1107410341c1d40000c440d07200310001403021440e804403c5480d5644205620b6000740f40a285514160007922540e9071000001c21003010060005980c1c0c0030035100b800300151180d00d200c111180c506081c044080504001d014001d1146202000182186400c409011320940060b00e140d0440e210960308401030200d807a0f4401c24160200000100000700000c007005000f05007000c0c685a040c248a2039080a0803026800110780c140001407000381b0f070041e00c0a811800341e60300040e07460928001c0800c1d107a0450802036010403108200418560080360180c03241c0c2c001c1381d08208003001b44440c9802c48511001d00f04c0700c0d0b02c41c500028540c0c2d00400040d90400d5000301000503842c17a0304200e40d10350303000300525000260003003010 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 5904153 1250 5902903 5902907
    0x10608060c042612040e0a0b010e010f0e0a0e22031b0201030905030a020a03020d020703050a020405060301060302120109020405180303190204080106080102090a09140109111c0c 78
    0x24058460250a080c2031454038031100340030354003c1108000c02000305075403101d0b050300b24401d88000e0300f040e5542c0e00c118048100203078205120f820340d44034044002944801161048500c1d500d0140c60b00d101c000081d0004464800000c0b40c60001d002140c1c0307a0902a9503900c09001c0140459000f4501c0b91a00d00070881d00710340d5419030910150f4144541d2000690402407054403012440c5102800d04441e00049002c0c0c600d2a0000d8640c1c04002070071801c503a40480c0f40c2c5001402502119450080f481e022a5100381038071020305550850040d960040c074040e0440740e0050001400032454580360b13000120131410341c0110f00d5081e9520410402142401d0250660007222500c103240030183c1070f404035460703110040030301e00da2024204541c94041d029078181c2c1d018001c000020000d490300c41802c24001e50103110900e1140032255800030710034881e8042c07805140c40d40241d882e440c1c3d18152444001e0f2280c64010f004844003070141d9000b030041c5030280d007034000b54608d01203190700c040640 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 5905403 1250 5904153 5904161
    0x80a0b0103050c0402030f0a0b0402090d03020d020d050c100209040905030301060503070e09010b03010303050313050d12050a0606050a0c1e0819080c030612010b03030406020303070807030204030218040305070605010f0801 97
    0x3c59008500510400c089131543c8199590300c000400310110f14040202d001400900c18031203815888075103003c081042c554006000900b5901c1034003161806410f2400917a40c50040c85221260360780250311646da503a041c3e402602000320081e0000c41c14616a90340c050460300300360000c1000440100802081035030003d004c92800d0410b98110200c4d504000e4000041c0c441404060140100000460b141c0312a20b0400d01070a41c20200b03a800209404000400313084007030051510017401c05000c104414400d12400007180e45540b24a4605003059005a4185036410003c2e10300b40490790106800043d0308041594040c8986100756844640140c001004298240072000304400d00e801c2016420b43c020403643c010000710f5003010340d540610f0055000d001042005905400042000034549400001a60203001c3da038407601e03080d60f69070400700c0890283e0b21001c0d50180d2202d8103c0c6240741140921900a40070f450503618002050b142c61040d6075003a84410300701c2445d0681003109800030300c5 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 5906653 1250 5905403 5905423
    0x40501020a021b090417091914042318060106030605040c0305100b0c01020c0708060f0609040b070c06110304030f08090a030801150c0f0305070c05120a030e030304080a0b010305 78
    0x9040340143c0c041c0825002140104000d12082080e03030380c10041c1401400f6502d00c802c0007003002040d1101016440d103144040c1c418010074102c55045081c603460b203401522841070f81e48409040303a00d100c0d6401702041c42e000d456400301b0101038210054481c0141b00542c0a03011545021604528080910080300e41c0d030300c00102090720f8001030010b1008444018412544210441900c034076542d148180244a444c59406051181e11400600c00001290152107001e0300c0c419441c3c10707a505000d120780810100c030010310500303840000548aa0083c82c0c0300c101c0700c0c014800014002103442c3c05100942c02034400b5000b00e600400c03c000a6607210440ca548145000090101c41515540142c00d201d410301030b01d000424424241c2017030500c0b503150300102980000981c4443c0080342000b81c510703403003240146d40d00784e001080030806003000d400c816040f02c10705000b48280d4034551003c541303100c170100803150306000030071001456110400c00c10701c041d0b005200920702075255161503460454001 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 5907903 1250 5906653 5906683
    0x60405120c0303150a050a0303030605120a05150705090409030507060c09060c030509040e010908030a060603020702100509040b030d02030a0207080105060d03080c090409110306060904020f040b030703050303040501020a02 97
    0x1e1044110020081e01d40000306081c42d1402c14132040c0014620103041c0c0c0000341c02c4045100008140355040d044032044807819255184001050b003c51604c0b10400380c000b0b030859200c1031078140d0300d140c403802c0164406103501d805403c00300850002410b035001d000f01580010b4002c0f600b102803000314803640488007803034184907140c40d24100020b44019280c180103024442d0204080e05261503540000d08204c0b403041c002c126240b001d182282c8280c2081d00c0c048001490001c002c60441e000e4400c542c101c9400034a40112f07c50107031003c690300d5206c03011581e0402e4650301e45004a44081041d804c0780784654014513100c1c54074a800030301e0700c18198409070b490382c1041c09008840c1ca41244e41454140c040c90000280d6540758621144c074425000e6440d00285041a20001d000503440740311850241107040c0e40d6a42c40d00401c0008450301a0343c003952210f1045821046441d1035440006c840030054207684100d580c070341320141150412601902c81d65000a401c030a000d606115080205d094a = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 5909153 1250 5907903 5907907
    0x1a030a030e0d0201110601090e120c03030a020309010b04110a021603080304030f090f06020706091401090b030601020106080a050709050601050c1b0103020c030a0905040f0e060f0403110601030506040512 89
    0x1500c000303104903034482000d401a0152009001035910411801001100c4d01c000c4405a596a80445006000c03040410010b8040c4590704404141c40e04100c1d400703c0f508900441c00d544505200070000d6002030101c20403590307540204039a586880c01444810844803d80c903860f20905078020f0304121700205c040405000c2c0c4681403002074051002c0da81c210f2380525040414006a00c400e803851101030300501c90710404e0144c00148643e0010704170b4155400b998901d508195034034215200c150325071800b64049005604180302015450000d16800141480081a80b03030b5202451414804000c40c1600c90342c001d45001c2c80803400c240505c86c0c100d0428a40f803844c01d202c0c0710800b030720740b01404211124884643c408075420b030300ca6015140489408ca065960301c4002c0c503c06000b4100307501c200d0380540e00708003415808a42e42c0c4030b2f000c52800044050201c555400001080c0c0c0c10340100100d0500a80303150a110b040350401985020394802e900a00c00d60805040c03031340c5002102c101c40c0e42c90301d9013 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 5910403 1250 5909153 5909173
    0x11030708040905040602070203060405030d27060905030f130306061203020d0f09030804120302060106050406050405061c050103080d0b06030709140d020316090b032107030507060606031a03 83
    0x2030404440481c0d0140d440014207483e203181c044041d1261030b00196140c499581440280480840180f52100c00500204084c06241d001c7c6c060421660400a101a0b030220118012940c4c50700320382695442801500e281ca14212000492030308024504142100004001d02c20008184954009000f2461241525080e20303a40207540d104003105007020000d600c800c0070b00031802100c03040091b640c0408000d84460b02c50003445401801c1040c150b0040c4101c10001407a0741c0150121000e4466a40d40d45c2d2802d81040280b0032150b2042c0b080c81d84070f00c800c801d03540701ca002038410280650320030b02c1c0c4241d5400d44031541a0690741c21804035071103540208248200150041d8011080721030641403100f42010b41c40c00500d03090301151000e5014015241d100401c000700a200c20161100301008200d44094402410ba890340340c400c603981c500351080881d0140740c204802503e00399119141061410206580345000e8032001e92109000caa100c4900c0450f4607544071481941040a8000f030160000d = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 5911653 1250 5910403 5910413
    0x40504060e0903031f050a030303020705060703090c0b1c02031003020a0b13090504050109050d020d030608030306060f03090307050f010203160806090411040e0102030916060507030504090b0402070203010e0c01110307 95
    0x100180c219944200d05e01c2c0341c88540d4110894040041030024140d15840b5a6030901602130361200300125401c3c05910002041c41d030181c81521300d61500210314015036403c202201c403076940154091a803800c0880c06c0e1031622040341c00154400d02a1a40d400d0140c2d1840c41401070010302c3d40c209860303500741170010090304003181a040e000c88004030008200c03500d550418500400340814040c000c1d029013840702607160380020702c00b813a8884540e420040140d032000c0c03141d02c80c04107079040fa50013102081f040d144910080003468110b0051015249040010703501d591411500d508101c2242c1d4000c410442c80584a96990405450909059201c0d1405900003402654020401000507002100712502511603900c0448a40311081c021036030703810b1500c941640c0301080d5a895450440051f03011540c1c51040c429110080d504d5210700d801d2509104209000d402c0a03600c9640059080c8000c2014ae50240141010022888040d0860001e181c000400b41c820104020f0302540c0100803810000d0 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 5912903 1250 5911653 5911657
    0x102160b07020d03030e010207140606010f0804020409020118030506011404020a0c0b0c0412060204080c01030e07090506190321030b100c02060c03030405060901050a09030e060901030f020a0302040504060e0903 92
    0x2d504448a103a4601c2e43d19050f0010101641c600340c1c658404039520003080ba030408900000a514002c0341c00030f07a141001120064148a800341c005550b20002c5001802c098000410f024814102140000c50b4551014110140b0703030300548459010750300400842000c0ca9a0800700d590540e415860540304680141900c840f070039004200ca0b11000028450054400a80b8050000c0003c0c07480300c00b0075400c24070044d40107806001d5441c0203980400c101580288108101c6e0214800074004c480d01d0b0407541c02c006d06004000b11703007009188540412900c0700000e0f50003e14482c01b001c1c145040102c500000c01c0295201d43c0c02418988120051186e4541440d00c0b16140f40e840e000000707045900c007141d2503000c0c0401c1901244008002d104c10403202068040c41084070100070882c035510030300020141c7d090200040c01060100c0d490300c14034100803005000a00040c1404940c494080c00200700300e81c4000301e908006540800c050000d460716020f202c000f0311440a01d00c03841e0500c40c040321345074 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 5914153 1250 5912903 5912917
    0x170103020904020909010e0d0201060509090c0d08030403020102070f03110d11030f0a090512060f0f04020d03030209010c050a030305060f0301020f04050d0203070801050405010903030501080f0606060f09040510050102160b 97
    0x1114402c1c0017070000c0000f5005400101071b0070f01076a0f0360341080603029000c0c00c4d03580039540c0b00d01c2c0c0120001300b5000000408c01000840180054880400d546480207584d00240007541195020008a40800c01e410030640d106482650b5820f0202002c050350b40c280101c4800758403c02c00c1090750400d4994000060b90018559040d006545007045042642c01040b01c1e441290443e0a003103000c4108900884d80b280b00e9003141406a8059407801c1201e90584001c0300c0080d403101c149030000000ca4802da014019042c0b040c1081c400110441e1500c2e85003192058044001030b48507010020217080603180319a041d1003d8000b5414000340d0485000c2a00513400755600503401e01d8440010340d178042211b0f40040140c2c030003c010509003130804078003030904214240d000c03908107000044c070320000240c10041c86140c44054003480d10b030300f010000c0544c4148003480a410082c045030740c650f501c034801d050160480150b039040c098902400a07041c041000424480d049504a04110f4051010101c07000 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 5915403 1250 5914153 5914159
    0xc030206060108150901080d021c02070b03041109090a030207060302070f020423010b0405031b0102030306010c060608032d090913150509030307030e010501080c0607050309030d05030717010302090402 88
    0x640d81c0b4104d0113264000b10691690f480200c907070000410241c007041d00c14615843c0d909461140688800c074031444809400c2c903100507400b80c44200903108852015680180c410703030070080c2c10107030900015107000064515000382e03084200610205901001424000c0085050541c03c00000d0f45601e900545d64440c0a4040c03030b142c82040004da0688840711102640c6e8000e84406547c41d010508001e40150040710b0181c4222400c4480407006601c074008124416401903186580f45801103500c102c0c4181c048030240d4441c40041040102030019201d044444d0101c0c2c83e902600c003814600311038040d0742e2a140b5040c1000380c1c40294880c1041e40b0342c80400c060100d04414014602401c07003840c11101d0345983d40c0f600c003d10201c408044000c500848136075605008500c2d860417814201e0b2001e01c600d1456501021401c082420020b0181ca1070a00500c02e417810001c0b4140824100100e254011001079000020071240b2608207006050702b50884070541a6907043d03902080102c03802030300c0644 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 5916653 1250 5915403 5915417
    0xc0901120b060607050604050d09050603040b0c090102070911091302040e010b07030e040603060501031104060608070c08040b0406030605090a02090102030306040b030f0f030307111f11070803040c050405070c0302060601 96
    0x4000d44480c001c07135803503d6000c01200d0b01c82c50942406925000036056402c0002d601342000030b020700d05581130f28081d036004094681161600b55502c1c5166009404190560007103905c0040ca4090314401e04803800717909090a40d079100e0503400c0013201c0f41205412500d69105202c1801043c003600440c90548550250781d030380d42ca00358181503403000001001c0030b82c8541000d01c08401c00200c2d80000d4100d0344a0710b8011824042072042000f075410600400b0001524100010781040c4140c0341c000d2030f0b82c0501d0a00303141c1501c0e0243d509060b030054118001007502c2e104100450f0400526240c2c3c44040d81c4d4003141015a0640001d403a0b21002d408140700d9522102500f8155505208044500c1d54000c212001280000d6586449410440b52880400e00e4003458021010001c1241e410000407003840c03c2642031a60304420042240d1038103618010020301c22100003e01100044d4015402529404c4003a46800b00308000e507480113100c1000c110b131030b804981c0001e4000400301e400c0f6a09082c504 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 5917903 1250 5916653 5916661
    0x17190302030706050108030403140105070806011407060e01020415050c0c01030f0209040e0a05060703060e04080a0302040e0108060a0c0f020307021e0d0308060a0503010506060d05090106150e01020c0901120b 91
    0x240386002e82000906400d00d000000283c12600200600231284604001c501008414407164206e0f042111420007159440340024000c2d84250034040d4051031000043d42800030319180c070011280011150682c0780e50018060100aa06900b007000e00b44a9152052400c908030b00070903102c0c94040e000301e050545801c3c840a10410a4058a0300684082e0040001441d003101c2c2c1641ca4001e0710701178940303015642c04244824805d0040c501a200c1d100d44103880d5445581e100c00f02640000725140c00c15034240004920030144c0d008050081c4002802020981040da052004031407122040710140050741140b00440740d008400c0e82c0301d903078044403954544082d52550801c600c0220896691202e01407000c1d40c201500009c10a000d220180c0d440500a906c0e001458200d440c2502c1c5107922000510140c0c1c040d00e07070b44e0042d561000a000003c11416613510000c1b24003080c5803444400314009c0c00c004042d6589c1044490008403086900d150b44e5403610010382c0342c215200202901ca40301d000d00103 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 5919153 1250 5917903 5917907
    0xc1003050c09040c05030a050a05100b0c030706060f060225060c06090c0602010c110a020d150209041407030c02060105010503180102090307030b04020907030501080303070c020409050f010c0306171903 88
    0x55042e20700e0180050207038428110004003264000c0301c0e80e0803c646040c011800c2c0880303600c2200d00ca0450405403103012404c01c03e800300250000110158a480100101000122a0b0140b58020043c00c02c100d4841401d054000e801c00e041a80000c050074070b040c00030440c40480300707142c1d401c9a0301030170302c0090001103040034070250600140150030080c50f07040006129505501c0360181d01d8540e99008081940015056200c03a00214060351051000c03440b000030800c0b030300a450b41440000f00c0103103000c0041c8089001d03908122103000108001c031081007640744d011f00400866824600c013415296040400203400d9000151003002980700e060b4009440490943c1158080b50b00102258903081e40d0345030416018038101c5049000301031440204800e54045e010b642d046e504000051810341d030344d4181c11071720b600416006076405526205000c001c20414000310b49902000800070417940c80d444005016514a540000d0754100a080c014130348600100f45810200858111504401c00074101 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 5920403 1250 5919153 5919157
    0x30f02030c040c0203031005030705030a0201030b06120106030606030b040b0a031410060b030103061104030f02060f04090504030206040b0603150109020d0209061803010c09060519020327030601080c1003050c 91
    0x20075400c14504000b40c0f8090f50008080c61007400404002c2c007100d51900245522440607204464250b40003050b00c90056003c1d8007c0c40c4511000b034821030415034034a11100d46402c013170307200c00042a503c0b02c0901c85280c0c035004584862000340e030240b0090030740b100400d13408415488041c054000044888500f10803d003d403042c00c3c054080c1c1400712a80300e8100030400d910a20044900a203081e0751003420190b41411b86048a8210f2041101d20b4034a8081c491b896001940c107840e801410400411355101a01c99140140e000e98010100c1c0d28284c81c08001440020b800321303200c1d0b4031008504030405540c482041c1514846070b005601ea03a51004008060300440c0380030307135000c1c02c04a580c00c0c0744480b035054954200d1080b40248188883c401040e00c01c1c151a000350710001d0402c001e50b450000c294a1504031581040c811213182514520075500c0281c0c02688082c100010080d180c085480e00f000024091b00c0d00101610656082a0000340d0000314910402e05060f2070b040042d032000315604c1 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 5921653 1250 5920403 5920423
    0xa0e030102131413060305100b0102070e090114060301110406030b03030903011b02070e060906190e0106090906050405060603070c0c0e070f080f090706050c2103060a08010506010207030f0203 84
    0x74400c95800d4660209442d0f10046019550007680c481c2c94503240320030300f4040e20084903040300150444a000f0790b60b130300240080030542c03415445903080c00a41805014080c42c441d00907000000361445602a250b01c03005005016144030341e041c08140705100d14000215022201d060400040c003140c0d80d40400d0560150804259042d480d04900d0b00e10020310010110000042c0d909466440303458503621410041d00b030f102036401c07900c0c6400007500c030b007400b1866030301500801c220b0085040d525040040c80b00030907000100000c043c2c0300c00300503808007401214084c003004c90b8280428982440414460b0000510b29000c0092035144c02c0c0c203100e078001420b40a400e0480c9911081e00e0700900c042c1c1301c509040b0310000007500010004051002440c40140200700382000f416a16103042c0003200e00307400001c65801785000d000055000017418400d11184550300380c001079141d1510104000803544285e03c07811040e41440100912030b0303804105142600d9110700c10254407400c07400882e01d804000c507 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 5922903 1250 5921653 5921677
    0x40f0e010c02010209010206070206090601030b040f120302090a05010c0812040f05030304050105070801120c030210030b030708010b0102011104030803040807030507050102120105030c0f0120010b1e0108010f0b0a0e030102 97
    0x40940c01c822607043d001400070710005c4e000c403861030721003c6089076601c0c42141e00301d0858010100601c002202c841410360014002c20000300b1001c0c0544806425000410450300800c1d800210300d4002d00700710780900028402401c0840860030b080d00d40005510420120405120220000408014404009511340c2da041021252a03207403928182d030080c1416141100403801942c0001025840821401ea41700d034003000701001103103140d003400000501c60054030141511031300b00f14510b8a003005103030000c0c20940008182a161030001a0845528420051000c00100014401308a51204032034100394050702e49940c0d0607035420308407070500403034400400b59400002c621b401c80e00041400c41c180c41040742542c4260300100200b0010130508001d16020441105056032085400200c10041891447c0040396603404c0b48006400501c5d504036040820480701407200c800d5a009041030301519040c900105603508012074031007180924911101040003500d00d80da039a031030a405a0302042d81c05 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 5924153 1250 5922903 5922911
    0x9070806010906050103180515060109090c02070306061401020715021504030806040501051e06030a090c0303020303040b13200d0605010b0d0509010207111c12050a03050a06050906040f0e01 83
    0x18404041c00703800f07103115040c0064100400304080340022040001d6442c2e100000781075110102c020300c050480002e2140303042c0040100000342e030f9159405001d106201e20340c0581400c42c11403408004a54281d00b10540315803003160700381309c00e90b0000b54400585140c00707c13508609660321412460521490501c0020341805800d0208250304001e9143c05031a0440301840240c1e00e80081c800118034848000082141c500c4001d84541010700066400c02031580c000310b100013081e00c0d518147c040e164012401a8000000c201c140b20180001340d400c030400f4511200340d0200d0381c072040a4580c5902005044c46860b4001903c80d50710b040a041c03000740d0083c8140070569541c803940720b817600064484a549410407000038a0001c040c0f00315104183d0040302c00790104500070500425201c801040440061911a03c1000c503881c41509680d481441c0d641c19a1080f00b2280103040e144042c040d03581150134140d091169988502c240381e0702081c262000950345200391101e8001c0c0001070706081242d40b80c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 5925403 1250 5924153 5924159
    0x1101060b040f0303020f01050601020c060c0705030601030b04030807020705010507140114070201020408071d0f04051504060204050f010507050d050f0f07110103060501090b0f0a050c1006060906020d0210050907080601 95
    0x11042c40c08100c81c0a5001d1b61040d01240650b5420307544101c42d21401030700700d200640d04130b02e4000c000d4001c0503442030469107213549030004240303060400c0c1c0040c0e0b01926080100800c05500203001948820280f02400c0040d2610002905a002d42d42008201c6000c00e001141168825484400651044d0040d005241030850380613000754864020703201c8602400b02c01040546032980054552011008002c01c80da40d0300812080c00d20015200710380300d00519024014020160782103502460080c1d90050f511858801042401150240b01c141840350078030000340403400c041107a0b0110050303814040c0c2c0d42c0b07042c0482d01003207214243d9a21100b00d008501d400038004000c1e51048502c400781c80810000da200e00042d96020980d114004540c40200800482050b42c20043c01c4e84a016042460510901407200c60800386400c81d4100c000c0c0c0e503080c0800040364440109030081c0080d0024207180d0311034501c02519519885501c8903101d4480b00810803040d01041904014103281c01500c002d561 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 5926653 1250 5925403 5925419
    0x604091b0501080703110d0b15070305090f0108160c031107060801030c050108010b0403030c030203040302060301080d090905092808030108030a1202040b1204030908010e010905101505011101060b04 87
    0x144a001c1e081c0060f82c071100089150b4082e00c01c103038124900c201d889003003488040c4048007610384c01000076001000440e1401004465401074070303009101c0c1d15855101c05115040c0150142180301c2e40c0d0402c0310550500005201d804080c8001043c2c51030180d60120407404c041c1d490b400c4903400e80702d26115200000490a034421681d0307060324841e4405000b500d035038900441d8071031820300070030004120406c001c10009000340d44206480b40310380150382c10259243c000800300c0d002680a00074035008044d245240c50f03481105003001d0008c040d0104654101104556a9219134081c804810348115810060010b564080201d44c20341c08040e4540e203684644200780c49400c20080000805c034560060000c1605030700036503042d140c4005c46242400706060f0700d43e080c02d101030416000d100c043c0e90b000c607003000d00f80038400304901d4000c00401c88811074039000780703013160714003d04c0002c910f4203802c1280c20075040c17a8078040326001d00e814031462207210348890050510303a02010040e0000034000510035 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 5927903 1250 5926653 5926703
    0x10815180a0c021c020c12070503010501030303020405041803050d020a030605040e010903020d020c0306040b0a0905011a01020c0d11010f0203190e01090605070c06080c0c0601080a1e0507030605060409 88
    0x50340e82a12290300c2d013072244140e00441c224404001d600080340418840c14261070301e000c0c050100c4215454a9900c03c0802e00b140d07000c0c2c20a40000b1b0300000c0034009418580900c0803000c2100d641c0052581607a1030090485c01600d0501209603000034028911500c2508450091712004000f00321103551104c0c424020b004810b02100580190000c0300403403400481c01900e5050041c001e0100340c0d072241e46101c01104024000104503a84072411000b15900744620740c2140b1003900d004507030b201003400191500c3c0800294510449200d003401d400101e40c8900600031690a0a0950b03000310300e810180d0440c02288001c03403000c1038800000410307036807240042503104000c1e00d640c82c03c0c4c1e41381c450480d0f8520420303501030074490b040c03c2d08204151244403201e50241c5410081c2c1d00340411010380606192081e4081c8407558043da40c101e040c4001c030032204500000e40010028440d01c203035074094445295100c050000b56075440091299207854101d00007080e801712116420760f21210b6091180 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 5929153 1250 5927903 5927921
    0x32402030a02030114010519030903091205060114040204210201020109080d0203150103090f030c03200f0f070e130c12050102030a0b060306030c0f0303071b060e0301050105010815180a 81
    0x40020980540e811b5024030100c038950741003a50b043c203071000c040718142c009c2c2c003080b40120700300896407400007140000398550741030403807044001d40a00d500d8920704161010483c4450b92045104000800508101054101c2d003d418003c44122608003800144e0040ca98440007a103481c4000620388002d01540e0b005501c00c00009150310709208032003004408541030441c004000c91802000c02c00400c1c000c06404403114441d1a140001032a103000d0111a410342560781c10007903221811107540e17040c0602040542140540c01051128174140c08039044004c0a080044043c0c45940c1500602c01d9944551025241c003003040502e2041c18a07069000b98002c9079800441450040803450710b00e0400200c1b4003c11004008026459000c0c041040c280300d03480c66280c1c0740c803007003040c01e0008000c211f102c54164184010020b01d05c0c0b41c1712014084485140ba02071081e4503120040c80031360703000700d42544c120451030f85111030f00c010000400d4000c0a1079040c004249a507204000a007611a00100c40e2 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 5930403 1250 5929153 5929169
    0x3070b0901060b040308070c1701020c010b060c1f02040305070b0910030506030c01110a060c230c0d050a020a0203010504080306150301030f02010509010909050103051e03030601020601032402030a020301 89
    0x9a454802641c22103285004600e41048208810008200e07044081c0600d24022003880128954403040005840745094050b002a5000f1038184103643d002e2040100300ca009856403490920803910807501c500c140013150320080b1322403504a08079099a810389018560140403074030a00d89951000945411542c0c04900c10000203071000c0c0a144603001780b6001e241c000e8018260056070070015241c130060f0b6079400700248101e24140020800c50701070401680c1942c2c0310014030201c40c24803004031100c3c21a00c1082d40904000c88040360500240c908185034103850020748841402c2c604a0600d005003070b01a62560134601440f09000040c0d0046003d074408a0312a14110382038200140d06000c02d07c0046c0000c080741840e00c0241d4040c4009180c2c1600514080880c5501c0740c605004a8174207800c103940c0d1f0741c400b0980d880b410103903060022000141200650030b615058000030340c0c4002c140402003d50701c5050203d00402071441500ba00b030311010009646a2800740d4101c07000750404d04c65081c0c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 5931653 1250 5930403 5930423
    0x7120812060402270d020607060c091d0402040b06090301020304230a05070506070219060f0228030e010201020c0318030c09070906050306060d06030302010902030d031a010305040809120307 83
    0x605882d0600c200d5800c00c81d0341c034950f00d515591030962400000103282080d080740e030855140c80181d0340e9400400d610346c0301d000000380342020064010100d030550381203040100d420007441d100040c0e104482e42e500590448000c80d0000410010a40324080c2004c3e9030703015070000c0148010070040700240456000c0c2d11460000c0c1d1079601d49032903551a1139200107041034000003414020380c20600002c0001c140090441d1030340314400e0480c4204401c0d50b81c895800030319020400e1944650500c88450f100010040702c618450b1207032442c100c9040c803020024184045140d0300d0101d64003e405407984400c25809890700c541441010041d22460382c4106486802141d084a4052410100c0b0b039016885c07079034035680c102c1d04045003958194809461558405000d00860b10314000714001e5001851181c1e0004c1140c03180c0e8414545404203c28a4400b40f60030800ca022040360460121540d208003440c011a60342ca86050803a00c52091304052034029070103400305e002c02e02c3d00000030410700e0b02c9420051 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 5932903 1250 5931653 5931661
    0x1e0c02030c0603010b0f16080f0c0106050904080d0f09050102031303090503030a0203030606030405070302030102040f05010e040e06070c06020909010608010608090102040b04030f03050904090b010f050607020f011107120812 98
    0x2542d440240a010960b5105014071000c0468a0700548035001c82000c000260510030344403807200e42c102d40000f070107e41740000d03866242442030103040c0040c08141e5040155041540d40d20030580039514098002036030b200c00c0d40300109541e802004500750080021944c0c1e04000012446c80754010b40d0542c0030a10880c000203450a001040b00e4003080c103503006c1c1d425605c4840030040180d2000d44141e85900c1046004800340c0c3c1c0a03c02800100b0340802d400e0307009c0b0b1500c0e00140000341c40071a000e10a502c0c2408030303070301c48802040300d688c014014940308075803041c0d80c600391009000b00a41142c12078401c0002003011a04075001038140c94103929090459643d03840382d50309030712450050b10912401440204001181c00e4841c170000b03482810030340e00f4002014041011039200b280103441240100c030040005001500c22134000c1c00040d5601450180160003044d400c13100c15130000d041106e02103041903004e00620006010f05052404e403e03202480742401c060355002041c020541d500280e0102e = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 5934153 1250 5932903 5932909
    0x5010501110f0303010608040c09050708072a08090604030614010302030606120a030f0504080f0105040c05010207060203040b030606070206030712180f0b07090801060602010212010e0408030f071e0c02030c 90
    0x212600c002d40d400110301c0c5a0038404220f4880c0d0015000b1181c080e002ca0011481c840c40d4001d061069040c1e80c1e43d840c1c00e04c0c00400007480c0754040455240404134022042540c0400358590300300d11078000d1141c40e510040c1d00c000c90301503c0343c1e42c0050a00c0d031400c1c0242008500b0300d544e150403280210300312203850b10b48100f0407c4c8130100324015112070b03000641c2c031000a03010f00341c903101174039490901e00c2c20669109505820300801105c000c605954803000c0100300b002800100c00942420310060071101d0400d0b0019540e84142d00801101c2c0c100407002a440d60b56450886000a80c0948a00c1d12030400301c102406041d8441140d4400f02d081900c00645031949400d080581ca070007080b01e249405540e1034810000302c000d013880040290814004c00c17917200c00d000c0c0e0780040c04264001685c44142c2e59a031a011803041e004510341039140402d0101064040082e0b907085558001031511940701c1501c02e40d4800001450540c1040e8602034500800703421007050f581d03c5000740c0c00e45202122500c10 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 5935259 1106 5934153 5934163
    0x30a11060714010b1201060b0d02090307080706081806040206040302120709110403020316050f13020c060a0b04050f04050d0c03020c15070318050105070303020d15090501050111 78
    0x20013207074100950b040801034640c400030040541054a00e8040c0c3c465581da42800917004036604009a80500a000080403050116080c1c16610307400646115030403a4066100e01c04440742500340000031803480d100e55070060101345000d00715400c12002031030480e40307440d09214041d004104518103108070726030020800d00c074030b807218554410546007081505041c42603446d1b5190410041d12100a00300081904841034040e040c4011107400c000e0103050702d030b41298460701c418491001540e500c0180d142c00103540c2440320345e8901a00101c11030044d1402012a4009900020030b548074401700c0d605988071788140c039441c2c020f80002840180e19001501e11f000700010b480b40c10190400083e0381c108010f24140280d403450440060036a01032443e016081c0f6400245594407100958407400240c8150400e0465036912821100000c1600b409a0f9020401898081e404a000060 = true := by decide +kernel

theorem cover : BRFrame.Cov 5755403 5935259 := by
  have h0 := BRFrame.cov_init 5755403
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5755403 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5755403 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5755403 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5755403 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5755403 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5755403 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5755403 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5755403 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5755403 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5755403 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5755403 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5755403 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5755403 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5755403 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5755403 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5755403 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5755403 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5755403 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5755403 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5755403 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5755403 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5755403 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5755403 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5755403 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5755403 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5755403 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5755403 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5755403 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5755403 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5755403 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5755403 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5755403 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5755403 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5755403 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5755403 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5755403 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5755403 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5755403 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5755403 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5755403 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5755403 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5755403 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5755403 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5755403 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5755403 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5755403 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5755403 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5755403 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5755403 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5755403 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5755403 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5755403 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5755403 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5755403 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5755403 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5755403 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5755403 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5755403 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5755403 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5755403 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5755403 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5755403 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5755403 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5755403 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5755403 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5755403 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5755403 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5755403 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5755403 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5755403 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5755403 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5755403 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5755403 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5755403 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5755403 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5755403 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5755403 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5755403 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5755403 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5755403 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5755403 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5755403 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5755403 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5755403 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5755403 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5755403 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5755403 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5755403 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5755403 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5755403 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5755403 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5755403 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5755403 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5755403 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5755403 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5755403 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5755403 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5755403 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5755403 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5755403 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5755403 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5755403 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5755403 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5755403 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5755403 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5755403 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5755403 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5755403 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5755403 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5755403 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5755403 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5755403 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5755403 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5755403 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5755403 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5755403 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5755403 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5755403 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5755403 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5755403 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5755403 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5755403 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5755403 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5755403 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5755403 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5755403 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5755403 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5755403 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5755403 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5755403 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5755403 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5755403 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5755403 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5755403 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5755403 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5755403 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5755403 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5755403 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5755403 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5755403 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5755403 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5755403 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5755403 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5755403 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 5755403 ≤ n) (h2 : n < 5935259) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
