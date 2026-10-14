-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3077
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:35:28.293147+00:00
-- url     : https://prove2.me/submissions/89189eea-960a-422f-b25e-8e345e83b7ca

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 553237410 ≤ n < 553417266 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 553238660 1250 553237410 553237417
    0xb041703070321150807031b08030a080a0b030111070b0a0e100e100c050a0207060503040b040209070e030d08010f05010e1807020a1b06080717160203070206070501051605 75
    0x2e00d81c0e103011800300350100c0d00301490304034080c0c0340703010303459844035160348038124040c0b00201000001440d10500c1c505000c02501403602071400d0b20130240c50248040d450020495800600c0c1d4135144005540d4000c01c84001d000b6a11069819401c000000715211803203070150030098016500b464080e00c407002d80c5411030f110804216601d411100d0f4446207030407241e11901ca00e04190054424245208000c101114000401c000c0441c0b4040344005207168100005000f501c03030340c1011807460415466440c180b07036004000a00c120321743c5001450080c840d41e1440481d80c2c0103400c44021490284002c1d0100e41c00740150400f03115034074000200d661041c9020190b09501502e04a40501d8100708150710300c100038102415440b03030309200301c00900600503d10740c02c101c821464000a0801800a0803490060070840070002c900b1441404c01c002911821b8100e070041002107050f000b012005c2c0c0c154010900080d500150224261051000c103400042c0f0400848225a181100348034091382c2d03602 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 553239910 1250 553238660 553238663
    0x1b0c0a0503092106010e060607061e060f1a0912010f0e1006051305041b030501090c1406090d0201023307030c0c0b06030a060606050c0708010b13090218010b04170307 73
    0x10f100d80010400e80c03903145042c0f5000400079207890718050150b00c0b290280c0300d00716a126089144042c2f01e0403084850f10030031000d80a051203a1071154644450790751032007048410441c000c1c2c030010b440c200d02c3c7c2c0c44111216114208030002d010b07800c0010130040003086580b40e01c5503035000d824065013440403d44164425180014188000640318424640040a0081040b10984442ca030343e80700301c00102200500a6200b0000800c040c0924600a0150415075100c8055110404155000d80d41c5010984070411000d0351100e408101c035000403850031280c070b113141100807a03a119400203681d0441221600c115498032001c840d03141e40c0411421204207101c5040090502c81c242000101302e0302e102e0b80c00210080031151054100d071624400c50b05181d1140340410000a400e0070030400c144200002480c07618000c015181d441d0000c038020341c404000f0603000300d0b03451041400f1596101c091008528144540181755078503400d220060394050300401000030320800c182003c0c2e140000407926160b = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 553241160 1250 553239910 553239913
    0x70801020c1e24070909110304030302130e071d030304050f06070302120a0e030d020607020d0e041e0209090c040302130216020d0302061506030108061b0c0a05030921 73
    0x99407008881900d526028002855001d0000d070240001181c4880ba5258058038103034031544e082c080c0c0068021000b0340e0008204a084c411340f945880100c00c191788d03201e901802d0169a51110064240543d00e05400c0f0741518131002c03040c04115580501d4a0380c14540c101841d40f117166501007010744d03a001c0c910490f580100c03484c00786007160500401400000b0712900444210700c1e50100c8041454202060040002d128105481e01501d0100000801a42c960001d800d00c2c0c103040000030741394040c076504d090501c03444039911044d5442d642d000300100c3d40d6079681011845d512165800c0030750721101045221b0b54629020800d8001210100d42c1201c0d0300804550030350b50325507031541c0030b508022155004a540c2000090168035002011420740e480707580901990301d400301009260303000c0c810607280201c0e824001845000000980d85030420049051200d048100400c6482188910f1780243e0042c020326408901704180003006d8003180800f203a8050300c0001045c4002800c9800c1841c09255 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 553242410 1250 553241160 553241173
    0x2011508060a0c120c2c030c010518060304050303040606060219020904020607021c060c02010c0c11031606023307030911100206010311010c050a1205070605130302070801020c 77
    0x180355103a0b0200b94983e616007003e50800e100d0000c101c04071440c00360080f01040c6100c1100b208044e103a1034140d01040e800030011001114840031944e10b0042d40c0c2414103001c2700290014900c11aa00c803a220250002d050560300c0ca0603107000c641f660030544007240c1c000d0402002240c141c0c00815429400725101c0380d02e25210f9001d0b004c2011401000d842a608024200400400741e2660700205481c066030b8220704101240074507101045400c0c0150311011a45007401d26120a580502107440054022466080d002840340000c0c1c03c1c081c0040070340c9541d81380b44600050140d000b00d01502d030114031401c255051240070b036580d020600c3d400311420303603896207000281c1094040e074818102c0b1030107110442e022810840200c0d4070804d44d1041a009030340002c0041040082031820748220032070030300e410701da04291540c542d940c4c0d11051078001c0003100003504140c4864814000e480b04507400a00078069810b00e14204042516a40f04c140d00501601c10003142c0084140201e07448100d0480c01403d5 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 553243660 1250 553242410 553242421
    0x60c050307080a2a05100209010e0409020604170d090b090d15090507171006030b0105120c190806070305010609180e0102040906210803010302012007030308070201150806 75
    0x81940b0240c0380300c2c10b00c0030813034403c1c0ea203500202e003d5040c0303c0c080d14181240d400a08040d0328103100000c0c521201801001001d41d10b903031040d00c0d25540d16050710302080300000b0b03100060303e41c040c9070000c00001c03142c01041d400741c0ca0f0018007207010181c117480c0c014109881e251544102d200d80c400d0181c118118480703900006104155044827070440020001d158403031942c130036041c45c1083c0d0040d803c55605880c00d80c1150010b110240e20028605030400c05d1914541e0303800d0556805115040c81a07050130401d10054209000381040300398001c040f031806184412013030f8a021503a004089042c4100400194414082e00ca114140c8545898100003d803901d0b0300c50022803640d00030101c1c0c071074071000d01c022a85424005000a410240300220b03120b410151191300b0740360401c50107007407c2c42800c1c0840c0840e00031000c5034103498081c6400544040703002c20601c003c2c00100c000e50110b11450700d000050550050003540160f4003940203004141942d280301076400110300891901c1c1c1c01c203a000c0344 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 553244910 1250 553243660 553243673
    0x1602100305011d1324060605030618060a0b07050d0311070c051e0d0b01050933060c0d0c0605090a0b2e0803030403121e050414010e1501060c050307 65
    0x44d800303c0b51204030064034544d5030310914003c0740c4524403026504d101082002058050286c64090045454090309510b40f140004140d00312880040b2101b80c2c404002c2401600c85281c00740203000303a806130340d65440d01454081da586411070008400203181c043c0703520f0400450310455a0441d0070500c1d07408000d0418003001026a43d012161048510842c0100c52a407200750f5080d0583c0c0c0035003184c1d40c3c0c44d0300d40400d011070358130001d00150510001e20b8401c4000c40d0b483c26456000c0719541c011750308121500000c904184141c048280d101d104040da880d80e610fa01c040c1c0c8807540c602c10301040c001921160303801a40c92002600c0240052a003e00090202221030310340d0410900255000540c20781c02c0c82901c14114003a01300071842d400020400c018903420200054800555080030400004040e441c1941c0400c030f140d28814198a072000704080c08019400540010b14801c020080c407101d071800c46569030035000b85c1e54507600c8124000120070b80607200c61070700160404041c61406200380d5504 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 553246160 1250 553244910 553244969
    0xc08150102070909050109060c020708031e0904020f090406060302030c040e0c0d150305060c0f0d0b04061703120603070b0307050d020403060c0c03030e01270f020402160210030501 79
    0x218114480d1120010f1070351580c1c01540541800348000003000c1c115428107a0681e20304540b01c5095504c103100401c920b440010440720700c0740300803a8014440401040b071f075141d8454294400c0c0d118ac008220740d10807103038010042c051034004940070816190f4901e01038007a8001165981003c0d4000d2104010302c107628005035901550b00107841c0c1c58140c4428144c804c030740c0000003400c4246400070082c000c10108000058001140c2030400d82008201d06001406108004440c0111902c520014108d52299049040035004104144401c0c5080c1d074499696a00290040c014200c218804107140303003404107200701643c000d81220f0b895555000c4c411b50b805d90100c4000c03070085900700000070100c0c2141c0300784600c0300120380d51400341911608004041e6010f00850402c070340d142c019805512441c00007004004c0e40849003591101c90701d410f05150075048a00065003090002890001c001304440e42c03400b01620848003202034880c100001c804481d801d0044501d03c0315180b09a4001d9070144200 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 553247410 1250 553246160 553246201
    0x100c020105152b06180203060a14011208070b251409010513030b0a1a01030c021c02101a0a0f0f05060f1c0504052a0409060204150915030c08 62
    0x500f0140e0000e03900e036001c40f11040028011440188810307421482c0a00819030403840c0e0076024014802d04103500d042c0100d041c07096109804a031400ba404100b14041641c1026030000c0e011078181c60000702404040001500300240c0e0b4640d4200c01500c14018105064141018403c1d00c0c24403140d04010f4805500007500c04003108109040000018074031815184035400c03055000c0340080c158403d03071346550040307d00103040c14108100540c00c0f641c00510102084021000c0c01200c22441d54241e0a0010380f688a0700e80e10300708040e03031500340c0f05a03001e80c682890580e1000c58965031501440b12041d903d004285217002c141804000700d1508001815043d110900101d00c0c001e0361450841000310903000500400342c0321070401c41032000038084403000e0f80801e0468610360400d9025614010301c2c0c001303010701c41c9560701700d0361040c819547e060741e02514041d005001400707500c54004d0304160140c4145100e40e200005a050218030a0140d0115507207e40c0320b20816450301c00702d114850701c50001 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 553248660 1250 553247410 553247479
    0x20030405030d0f02060a0e0d030b040b0a2402120d05070203131202330705070f0e090d020c1f030e03040b071709030a0201051605100c02010515 63
    0x2020038980d400b4802e900a0706620f40300d0240703203900d00740b0190074458000c0181c4a21868000030081c860750125412440e2111450b000542d0809900000d0045ca091124140c00c21100103002c00c014104004104000c3c5200003408416100700400301d035200340b0f000f140d5015000500c80d40c049807441d60810340d000203c6006407030608a08440c0040f20920a0b0f0001d00107441d01015102541003144482c01d044004d03241240203d01c046496212040c2d01c5134030b203a450306000604c00140002400880081c02070191130446166031604140e000140650764031205008440b42c00040c9400000d40349880c0001034451300ca00032035100610008408804094145901c171141c41105107402d00c0100050031440300c55648440e5a4101a22007103140c800040c400d184c20010090745540020300403908940c2468110b580d0382100b202044c000440610040c803c4c4034860101c0b920009070b030041c02d03989007207130b0003001981c1c1d804a00305914080d661016820201c803d465402d5028189941c044c0e2003007044 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 553249910 1250 553248660 553248667
    0xc0501140702060d05160c031e17090d021006061b0201051b070602070515220807060815031504022b080409050112110609011215150f2003 61
    0x300407841940c044030101c1240b03903171001000360188495070410900c2d080c0b403402540006041d60050122584852110300034400c1c80f018002480c45840340c48a190305254034140c1c24145002001d550b05180003001003d0b02070f1501c40c5a90b80d0540c400d64040301c0c030f16030b620070358400b07141700c1d0120004203050141d040240070814201da40c85c09101540d503010340b26006201c2e00b40383c05c0d002410a06250000c0c0e220b000c04582d1107803510035100544480000042801c0480800c950b2a402d0040d132650040d110703802074030000a40e85810500192291403003034000c10480001404140d00da1031000445070b0310500c4000460301504110034000b1340c0d034408090300c0400a5620490800d4000350000495004800007001c2c4403a074013074000c0500500021001c503184919a40d0307180c441c01030890381280103004c0440d1410f03650780718600c07142e501000d4040c00c021100340420815003c081e68028800c0d040c0d40b000e044801103106551341081200c00395144820090491384200711260f140040703201a101c02d0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 553251160 1250 553249910 553249913
    0x60c010207030903020321030604050a060f09021305150a0c080c01090b01090c051309020c070312030504060b03030f0703050c0a080c0f0d03050411240412020405130c05011407 77
    0xd100400c681070181d100e0701c1601e45107104041c6132442d655012040c600350000760a10716030000080e030350818001c450100b0a0303542d0081d603c1c001c2c240c0e903000043d030307000c4a5400620f245960740100030a03a18000c1c0000341a0b117030410b2051000c0da1441ca001c030240c0801103488090310490340c3c00c0040748a4035086241000c00c0c40703200d0079560440c0040d2100100c103001000221550700c2039000c500464100340c0e00748941002c46c510190035038481c24800710f4000802060403c418442e6201030341e80328122103e80d80000f44002c00804045038121529407030500c000d00c080c540003084d50800c0e020b03050400d103855860b68044400740c0100ca40d9a195215440c1500000361044024040c1321491800a0035800c2146860070314005000c0040400e051901050202140c000e40c44090007400a9940302d5010140b840320a000d41c8039035202c2044141c020401007152882c241401294134001c5805100d542c640e00d0001c98070504c103600003031001c102d0480800c0b01d0350043c0402413400c00c00c141014108600b9 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 553252410 1250 553251160 553251163
    0x11012001060611010f0c020a0b100e18010e0109020a0501050c0f030a0e2701121109070f030606030212040f050a0506040807020109140a0b03090102091503070e0d0c05040b060c 77
    0x150042c01c0403400044010075041c20034440d0140c540c1240303006000f82c2e689030b08041e446581441000d0030a03040200040c00e45a04240000000c01d09009ca9070540e03e000040ea911a03c06c00180e80d48650074011070340220340c014080c0050741c6030010525603c0700e103081c00650781680f00002c101044e00959100303815a44050010f05102c00d41510703901c10540031141000081082040240501d143e02d50030301c0940041c04031910f05607802c1880c091076aa0f19400c00c01c001080f20914030b948401c14008008030070798001054180b14806440620407503441d030340142e0590054203408200d803035141000030041510b1401c0000464001c2007a00c04203500740d100c00341442c0c000c480c140c805480000341d01c411940d015481200a00030440b000c00388000303420006e01002c0c06441f501c10040c4000c0040b9800f07400a5048544146009108004040106900f9102a00100c91400100d40343c802080342d503081100391358500d00d03401013108124a080c0400c0000400e00300c4080d03030f0015000c1c45900074a140 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 553253660 1250 553252410 553252421
    0x8060a03020904050a02090c07030512060d0b16080c09011d040e061f09050601050d052d010315050106050a0305190e06270c090408070204021c060501090311012001 72
    0x2c00141c04e40e0b0780c946c014000e00c28005006442001000c106080203c2d500c903003079410140e00c180102e200d5480e8075000400420516a000e00f070b001c1410144400e55240c004c603001c41c0840d54550114135a180d440c03650003805807130038189c0070605000d01078100100b0041c8140c0741100040c00058005081c40d4030700d203040c404841c80e0850303c1108000b01c003450608101c0e44000c1c1000403040c0900d20b01075000900d6809094074401000e0784500128640d4150760030020f50420038501d507001d0703075041030421441502080c40b0030744010441003401c0c02c0d8008240146810703112281c813a1813400c00009030442c0205402040b0b42036042d0301c40968400c0038407174000c240d20703044008004c0109003012010340010004e01e03a0620030903061020462120a004101c0d200941d008440410030703555203041200d507a1160300030082d071080c0300050442080e14854401089401c2c980e02c208601520f540064a84079414080600010b840825806056110b410222000032004104609481d60f072030645081d140d = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 553254910 1250 553253660 553253663
    0xd030c061401080d09150f0e040b030f0109060e150f0403020f0a03030e16030b011214010f0504291902090a090b010e0103060f0b0a11030c0a021305150108060a03020904 74
    0x42040c000e0068080c0d003c40c1e000701500c0100680050001446e10113410035031b00100010612480314414011036556500030240ea60b0050f05584030958a400228020003c01c02c0840e0054500003030600800c41c00144003515842c810b4201c4403540302c2c0083c2c03261458005204034110320401e0b0000a1fa8041481915246486510f002c599180381c91119801d0910500001c481c00c540951300300702048844606504440d010008401703d540e143c01c000302280c044c0a01a61f040d82090300e40304050381c0343d074043c5102d14050211400e003c00c801c200c4201d50203044038040110303844500401e1144000c00195204882c0000d03005141071000c1010500d03202c210362203002096601d9240059650704080b08904401c42440c0030080b01d404c10050301e40e0746002c1e001d0002c6118006c14040092402108006d06240ca07040440c0d859406920f00d06131384003c2000200d016050700004c4409403a0a40283c5000b103000d41511700d0780d88150001120051001802e50f944007640c002d0000260f100c1410090095 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 553256160 1250 553254910 553254913
    0x318051506131823062508040803060f0406031b0312020102090303180409020a090605041a03030a0c020105040f030b2d010b0a2c010212090d030c06140108 68
    0x103207000010480c6100914110003a85401c0c4103402d80d091500181070750300c003541304840e43c1000c119400d241d82204000c4203107802034402d100a201c01121b10000240200100015020546030b2440b13040b91008011346000785034240070b00200321149400003220382461405000061400d80d640c8514002c006034614410200c544a081801400040000c0c0b0980a80e2800203524214032040402d0340c91003062045401c0d190416507000300c655503504080c081640092805082945450f81907000740501c2c40f0300340c0f003503190000c0d000240c4a01c00c103e0706450402009181080b14501050344c401c006468128100700c020040800c0318052001030401860040c20a14260710b00401186000c103000900c5145111059a038004900d0803071102505540c0448102c0d41c13640d0b140c680584101c3c1c0080b0440c40a0002c0346103109484003110079019103140d00340e080300d440e0b2810502d140d0b0307070344100b0340c2313994102d0442507005000c00e019081d081040ba00c100b200003001c4407503003100000d281d001c0e0000c0016 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 553257410 1250 553256160 553256203
    0x80f0a1107060203160e0d060905070e100f050a0b030609040f050d022a030d050d0e0a140606221806020c010501060224191b0e010314090d031805 64
    0x301070171010010301c40b40a070305220034805160800145036841e00e0800a0603d900c13810b10700c0400100340b140c20000c00000f40c03c1131b00c60804211501c440d42c11405500b42000c0754200000c0e051401444000881e034400d641d80e4950344a803800e1050b80305c4020800d076240326021100c100011810011650041041c4c0d010300b00d100d040c100c41c1074210800d900552422280468000d080c1d50340440c24104511407401c140b544e40100500394000341000c00384200007070185802c41400d2002d104500000da403030100c103403000c03030b5296420000c1c3d1030b09001c104081043e0880030810505000d902c02c18040c0381001f04c0d00d02c48007250780e60070141e07441f030500e2041a035127400042101c01e80410200403111180c0214041c075110304914998241c0000703002401c0c41c070300201d0542207000c0d1588840180411414655005000078401400021000003003034006851b01d01c04540c030508400e480c0703000b138051501608045605250403405040303c0181402442c041806030303800158104040d40044070550385210740c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 553258660 1250 553257410 553257421
    0xa1d0d0303051b04140405040c080a081201050105070c050907050d0e0f010605030a03051e090d03020606010f090b121f0303031a010e211c0207080d0906080f0a1107060203 75
    0x60a40d209140854540244001d01c4290031502185d01344800c1a100001d1964850904003034014550348202224000d03480c2e60b10501640703200400c1c0c01100f00e6031414159984200450f21482a11400303440903060b03000900c06403411106040d0003201c0e5140444c140b81405070080c04660303140c2a541e540703900c41250442010b07400e004400081008501078410180c5545001c3c105100e41170701409240d01243c82461400c1202040d60ba01050181000000c440b192801075925030080c0d40d11404034000348051140c0741d104207008002d0b1050703401c40b1070800c0484012a2518140134011078003903103008008902c0c1c2055621000d00035400782d9404201940d40303c01a0900da00f1007881d240c1080300220f1042c80300d0b151407800c601c0c491a01703442d000041c1c040d03c03c0c8605010302c40c100b040011500744d61581040c2d5000810a041d103507208103a81c13030008001d000740d401852505c182c00110728404000390303404407441543d540c054000b06010900e102d1040c8018003030f41c040c040031541598040300703008 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 553259910 1250 553258660 553258681
    0x6012d0504050a09090807110a0911030714030c1c021b0601060311040e01060c02121c26130510050a060303200709020f280206090c060a1d0d030305 65
    0x3d004103c001c0c0204045060b0352641e0485118404001c2d0640f044010744500684071180f400e0300602503100100101c10984a0303a070031640c402e03107001e4001800152805034800400080300d00981c10306980600e8400445404000003035203241c070014150342170083c440c41580e003407e254606480d0030043c0c5190b6050400240489910884c54000d40d41c1c1404144034000010032041e0542d062030500368900d41c1d070361000403420400550100c03014042c000300441c254086418100200240b038031b40310140960340c1d1250702d0010b110040a400300d081e400200c0d0310f540b189500d01a11a0256090f20f44901701001c031803041c0c1d042034602d00c1880341d1b60001002499880031102c000f00b152904000c40e08903054000941ea02c0245c003403054120b5000031000d00758250b40c0115101007001d000e4103001411151041250b1421f402d41c104054000c200c0010806a400300d02904403203c000d295504000350322300c040320030301510003210800c0e0058100c045407603a80e4408100b0380300e00c265008910b503c1c0854624 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 553261160 1250 553259910 553259929
    0x8030c0d0905010c020108220809031e0601030605070207080106270c020c04150906090203010501080f01080d0503060406031a04020f040915020304020f10050304031d030606012d050405 81
    0x10810080324110501c1660790007104c880c0c10940900e8a080b440e00c030440c0d18010490042508041440401045002c2104070f00140c100100304505961142c000401d80c0b00481b0f9400070043d00030b4104000500024003d6131280c1d400244503c103d80850351148803150849641d030304603141c01400f00d00000707100c0300b034024000b185031030341842484141c1c26000c01a40c1c80301130701c0b9001d200b0342c4c54400c1d16250501c1094048001d0001586c180084c596500c2440020351080c091180043c12010001c3e0442c95116141412503085100400740700c486d04904813450742000d0310340d0382d000d03842d40720010218020a4203c84480701c00c041c03031b4045e428544101700c4401400303564207000701c1c2080c501d40301054071010548003000e10400c02682d250340d5440052901c9421500450380a03103031071000c10741298800065849640319484210f0140504c000d1140c4030808a03500c15816440702c000140e43d941310b1b41c3c042e140c013000d45200f400c4c2e60100401108908001c042d0342e0b0300040e40803400f005030b498401c102 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 553262410 1250 553261160 553261183
    0xc0a1410060b0c0d08070e2e0903020d0602090402130e070f0f090608060301141003140a0809060901030b03010c210204080d140706050c0417062404110408030c 70
    0x7043c6400032000c107481d2200141c400c070b402407085000000b91003034040e1444045c4040c004107400388150b20810340c00c1c000c000d0060040040c9060091400a250040b01c1d1401580c0c3c0040c0100f16501d04c580c0c07082c01943c8440c05617034120350203000580c6041068a1580041c000e421244a001c1c940f1f114010702c0403d14604003420048603c2c070345a96a07030002d0004090302d20a18040e80b2941d98100842d003d464048020a001096802003140c181481c199800903a4810050004003050a2546079035640780c0b124007502c01d40d4100500c901d6442d058000b4420080b043c1800b1a81088041c0000e084851840d203a5002c03c0d01320701800c00030b142259480d402004050070450429040507100d80e0f54000c0b07000040d00740200c070040b4111100242090300c0c42d60394400404d00091506a0b4580d1032038100b441713000d0325070070b0003207681c0400340021810611a03003c250504502220524900d160b0021850301c0d0740d00550f4511000204042010041000c0c04064004582e9072031060000351502d10745112 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 553263660 1250 553262410 553262429
    0x906080f0d080a090503090a030b07110c030c01030902040f1406120a0c0333020a0905010f0f080606090310150e10090504031106100303120b0a09020c0a141006 70
    0x591200c2550001c0b200c2c0d030042d590a40004e00c40c0c205107002c80c41e61103141a19940a0440703080081003090081d8230911030500707a920065010881021142d8032803c0545c003e40c5070308860f10382c3d078442d4400d512800d0024001030000c10046031503c40034045692900007800219805810000703070f402c082c0c3c2848003c030710b804001c141070515501ca003071160506020003020b40100001074580044d0109001e0850000f14120821424a8819800c025030040540402041e29108002410b40c02401042c407160041c0e141c030004e02e08581012140c2070710049c0f102d603100c5800c0c09003038640d0300d0820281071881c01d42c40000690840208149801c0d9800354054645400c1a03010003054a02940380b4100300c60b640f0340003080f80d80b1503140554449500d031000d050988250010005c2c10042c0d020703a1801c907406920380f5821200044103080940e081341640540003a444c000070031102025a00804011100030265a010606946e4142d0305078054040b0b00025403110010708005042c5104140081000e840c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 553264910 1250 553263660 553263673
    0x3090311060408060613092001080717061210020c160503190f03230909010906050a06180b030c0322020108060607021f1206050907020a120302130906080f 68
    0x10f0301c4503503840c0003e00090140c003e4004000150340650440c030881c60b441200c411841c05200401a0f001242e01d03501c60008602c3c6002c107101d68000d41c140b000054902a840b00c40703130303908010300c440921204400da00520510003a4185c641980c4094480b0044040103410f500b035160f03021740c80861b41504100d20a401164001d0105c01014124101e2a64407185102054159060544150309a00e40d240d1b410a0039844100304108140c00520190714100c610005030b03600c40228500300c43c0e0724050701d80c00015520051003494000c88202e070003a410100740300340081d1a0b02048825800a0340c0b501b10010000c03051149c0f280400340440e4039a2070750120040a441c0503000200480740250010b40205000203910040d03482300710200c240a83d842072107421600c04031200506000d0a444444403580c0791000200e40d80c0f030210301007401a440f030b9004120450080d142c09892884007414801896401c02008001c610610080720042002c0c01c0c5c0050158644003025040018500c030341140b03600a035 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 553266160 1250 553264910 553264919
    0x1060c210215163606031b080702070501050c010623132003150a060806190302030a062403030201020d0509030703090b0a0207050303120105010306060908060a0522030903110604 78
    0xc0d1035511300355070000f151440a000300c4040d41a00007016292001d0540b0121301060751030301b41d0042e216040340c0c4241c81c42d09200706103085440282c10b89607000142c024a504020541c4202c001e0110b0860f10300001406950700d0300d186c0d064460100d01202c8030050146000d00a24044018100768940f1007020300c682c40307030030780500e07213452006201c094440b00110226004006081da003427100c2d9000f03082002d200f0340394880075016402c01c440700b601c62102d40804007500307103801c40701804495000d001880407464a0b40d6420103016075100340a0004620003481d100c2100c94036941c0b005502a80006a44500401c809815503800601c043c07000d2780100030700c40000b44c0c044a58800c0740c941140703040d00c40c90751130740407400d10b841688040e50611000c04c040c4a05841822200e049500c26241080b07042da44400607102d0344510310420b0459081f010000310840c440350807080d80048032420740001100001c80314078050801103c00d800044810805101300080c91443e89040c2e40c04449090030245807 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 553267410 1250 553266160 553266167
    0x70807031703100801090501050a180b06040e0c1816050301061b080c010906022502031b0d0210020102071101050301050307090f1103040f050c010c0b01060c21021516 73
    0x101d420340c000d80c0d00080014488806607550350084d12a020003486a080d160624a018000559489040754034003a00121a0440c2250507003880b54040c0c0015490781e541c0b42004020008110498164000d40c0e8041c0382170b60382c2502e241d51034000c01e08a1030b100d082074807203203a1f039040008108080c80307803c20042c45400d8000602c2d1002c2a1502c100303485031b480c50314050744240240300c15042030390300f0080c46404102c5107030003074910306942150511460402ca01c5181d602e018114000e901600300b040e00909a494001d250240c14402a00c1c0c4450366442d030f4041203010303c3c02404040140d40c0841c8410802c8009140400c0888003443d0142c119410140081e40341c207503a1040030002c90743d810b6580740c100044c1d000003805500c1070480b2500c0b031070f042c240004003000e0404125600e02038080c2e2202a58003c5100d111703a44c1c0c014600000076800d004082d203011000d410281d030031500040a03507040040d41c007801c864662080d405450568141404000b944002810a0b6600d0580c45d00b00d0400030703403 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 553268660 1250 553267410 553267433
    0x6070201090b04230709020d11040509061905090f0402040b040c0915110321010e010e0406020d0b040509030c1203040206030a15030f05031201140a030308220b0907080703 75
    0x10841c00c4000940f66213100e44801007500e49580a181c000c01000081c81c412a502425001e8041c00301031000403005030320711980d44a40d0080d07a51150744a0007141c1d8a08003206403285c00301d0310580e4500829101c5000402070352084419507030f03000c07002040004604140c060f810040c4402d031020712041004070009803c000c002c1c05030310300c91020004102a842c5c4070706035840159014a0a8981c0e038450308a01032480036610400354150325a40000150340024204c00a0484850049050280e201da81d035050280d03121440c5200025102c4514044641d114420359019a40c080f00450380c4400500140f41403101c5c100303210060400510070003001d030f141c2c041140da1044101400044030f10025203e2031748500305820140034020041d26040400c00c0000040148002d10086050242e03607443c011010303030710113001d440e802040d18074003080000d015850880c0c01840c0d0b00350080c40030b180c01d07a01107111041e403901030f500340310701c0814800d036620184103aa0180507010060030034141540c030760041b00034 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 553269910 1250 553268660 553268663
    0x1030e010207170a02010609050103050c03070e090a03050a0c022e0f02030f210a14060904051e070b07050102040f050f09040308040521090103060906051003090206070516060206070201090b04 84
    0x820001d8241d4050f40701f03502c65000303007590030020000c558403820010313035030b0111f01c51090082c410300401203103505404103104d118684003c001e209548d40c039501200c3c0340c1c00c540500f44c18440200c0448006a80c4c4031241c90045a422071180c080441002001d01d8014074203c841040c0322050b03090000c455400b00c1110840d0b80d00c07084481c4c0d206a00c0b112850000009640c1d00d01180240d000d000c4003030340b25007010320720b50321001e55a000e0707407100020015100d000f90790081c0254464419166010280b9201204050312002034829040d42c0f01180c00c0d0a602a0b02c007200c0a07503001030180500c1e210360710005c0203800b066880120552041010030481d0102801c05070170f01000d200020100b02d001c100442143d00c100c45c80c0d600750244404c14120680209071b4941c00b1070300380305000c114048039207d074100300d440060298071001105142a00207001c442401d1380c002c4030821000700445e004006c1c1d5007100300724038400000c6c1803400c0b0000341400c1c0003a0241342164113188901000c2070043c0d000c0c54206 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 553271160 1250 553269910 553269953
    0x905161403060a031b03050307030206072307021e060406020708010e070b3f0a0c02210a0509060403050c0a1d010306020c0c2d010801081902011b080901030e010207 72
    0x4000621804170084070030350004140b44000200d200401d42c0c0807030001d011700c915441d0110000b6180c1c805041200b0910f00e030a6003100140040409450113240011040c0150840380300407100034000304104d940142c02c40b01c0541d000003020443e060303092051203d140c48180180c00d0040c02d0041c41ea460b84103080d40440c003040d0f5900c0c01403d250915012514007440040c0140d500d046180e500a1192800c8400c0000140b07880841074610f4008522040d0b807610060840724115007030005c0340340316000060107000b00704083c0300c0354019407501d000800145000b070300108080d180105c1048681d003215000310080044032051003105600120070541901e9102e034016803a5036401c120303d840c0c0000c03610100e0f40868203000c1108500144040107111070b03882d0382d078410303181903503401555164402e1060031555030018041101c5502e140030b4500d8002d20500d800005520b5002d850440d80f45000000c0e11021000140c00e105d968140c41080050100c2800075800d2142c2d54070350b03c01e0400d20313401f8034500303 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 553272410 1250 553271160 553271183
    0xe01150c080408010f1a01030216030521090f060c040602100f0b1c02030c060c0c10140309010204180c0c03120e01090b011806230a0905161403060a03 66
    0x822070010256000790210000800100c045100d10030064201d83c00d00504812824003440c80d2541b0a0080728581288025103003034458050b5000c40e01c03503004900d0307012410360341004c1c1460f4208000c0c030103018403000030042281d900103842c9182003500c090b0030403000071800c000030003141c0d4012a0410a5000120b4005440c03690f800606003d0414045050740c0400d54107088034024100108400380c1c94000d0b0b040361800001c00c014844036100d159a10105a407000c80b414019140c00c03290700c1d080340360034500031f108201d2107100c600040e0015250400c146e50040b03420301504020f124030900d1202a0305040c01084003901010300359400003080a810041c60b241c0e614000c0b51144c0004220400751002002680ca09040a2000000c28043d401420808000000501c585030207584180d4201907030101c600c10310706042041181c01c0c0c000c3c090b001090a240003c182c0d00d10710a5500c40c0d00815811403c0d0701c1c0c5030a00522148075100300da070400c80107205108240d110b01c0000c0301925800449580c5 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 553273660 1250 553272410 553272413
    0xe07080d020d08090709020a23040f05150705031606150b030a0e010b1906140c070b0a020c0301020d0902030c0a03110402090301140903041a03060906090612070303180e01150c 77
    0x2022000c1c0c00c01b203011400000c040b1000341c0c0c002c8941540d01158000c04216134004040c51301e46212300e1040180031003424a091000d450710518491011981840b4185081a00d664503400c5030441008442c0000a00740002c0510441d070040a803540c4201c5900038045040401c9420030f070002420750619281e96502c00c6a0031182580238502c550707001040282621100412181611507074042c04c000201001c4500024000810981d4003a007002d00140c0081c0341041104049134000c1145041184138048140d43c5c651020310051000c0c031809140071491821071b00505141034001510b00f40541c0d032000c0700b0000b080201c14081180801150013603078076921540020b024100c000031007100b08003184140320710044d0000041003220341c1100c0c40c00c03010b0b031ba00007c0034103800210362161301300c41500009041031401c039000540c0b20100400d0442c100e15440c80292130560303c0c0d0411030119903041200c201e1507005900e404000c01d2100d04a00075581000c280d068000f070314400c41400e00200c0708000c3c0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 553274910 1250 553273660 553273663
    0xc02010203032706010807170a080414030a061a0406050d02010206011e0e100630180b18010506040b013e03030105190608131b0602010e07080d020d0809 67
    0xf84041c0c014120394130307540c440d600755403070714598842c48000c1e01c40c81495040021f8046a1802102d4000e5441340c282403070501e0343c1444d00c50005402d0b43c14000e10700c000700040c2c8a0b11550074a2250014580c98044900080c0003c0b600e258205620070030840890600617170340062003506645020140b40c41c0c15280c5450601c420b00745800084607214010304208004000c80c5402d412515035941c3c651003142104040c101d50390640c18511000026000c1840b020501600300d54004540441400d04554144d241c03960b0f2000203841015500341759101d449034948c004d005858000004880820a4039040d80000e032950402283c00701c8100c547c0e844080c030108030002c1d01c0300c003c41850020b5100d80c006850054480e4404d01074640325038901804020043e9011a03208260b55807a03c80021540700c03501e1007440e2100e40d1000306c3e6003044680c0641c80d400030714200300000340b817a50004250240000e40ba40e04200c0d59402418031f5501000800041a03070000300401d4000140c201180103456607070185 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 553276160 1250 553274910 553274971
    0x9050c060d02071a0c070611040b0f070b18150c160b040b0703150b0304020f06180906030a0201050a1404030c060804030f090b0406030e1c05030105100c0201020303 72
    0x4951021000c01e00301100ea0340c68006105280c070039100300d0450600b404120f00052000e44086005d40d9003400040001542d40d8803568400c85000c02c55400c0c25542c0c5c42c0c05005900c10140059034501c0841d0103810051402061034000c06c8582c504105142c4151450b0b0340e910302c051124141c44010400b103114403140c0740131100110f11030340d0605542d9070582050135072504c042c0c0d42181c4000311100041e642c2d078428403500c050441c040f600c0c3d000140c98030f941d8015039040503000360785c00801c01000b109a6504c92005041c1610b00c1c21442e51070000ca00c04001145800403d5240250844815100180c0e400400c80300c42c03205506000c0309129241c00000654003698200030a15107021901158481e0480b041324800c9200769143c002007881c40004541c00300c20f510030014060310510003440700c14000d4012a088441070412652001c664071441c0781c50b80000d89803032000c1480080140001d080070346007240c03407148500300481d0300001a40004d580e88001030044500c8014104a2040100d03400c104 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 553277410 1250 553276160 553276183
    0x1707061d01200a140a020108060405061804030908010c03061208160b0a0209280303080703150f030302010e061b070807080d050f09072403020405060a09050406060903020d060905 78
    0x90074582030740c914042d40d41d00e20254107542950341403813010340f032480000b0b5010700c0f65410381d1101c2081d04da807024440940400303021554481c039952002c400510450005504ca24020703510100c0251615005508440141c10306104241c20218180003038004188640c1d00903502005d215070310f003902d00e50b00c1d84040c1c5000000342400c03406000e1101b903007116009480e10803421030b0310050740c1c4500303036544030f85020707000700c035002c015901104202181c02107501981c03100c031703030308021034008045000350b1421086c03a045070244401140051060640c244141d48401d5010300c0100085e040107200790a084074041948003210100240361020009510199441c41e54405045c2d91a81c800c0181e11b0040d0508440c041c140304610000914002c400045050444d42012450030020f10403040c03141704041104d209000f41a000c100002ea961074910041030ba40000396501400d5500388410007096030195441035040000408090015035180904c9150350703075000c040000c04010f0740c5882c42c180030380b84a4 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 553278660 1250 553277410 553277447
    0x6050711040e030c2d0a0605070302092808060f011502010f02040612200913060f080304090c0201060e072102040b0409150b12150603101707061d01 65
    0x600c0200000c0002d03086a03980072000c818011001050345c0e80e04070402c695a600031344e6009580400204607035a2000b80c110303825160140c84d0114140219401038583c5200d01b94001389003101000c1c411b43c80d403440d006044840081e059604090410180120042c02a5072182c0c12000d00845002c0c004d5012480240740c2180954403036549400142000c0000d1429940b40c908010700c110000c0f03079041c555a02704130036002950034400d008050106c100000c0c05412200ca41d909804540e000c483ca00c0c040007032408100450769a800c0003c2c07802620030b070351507040c19a810803d041c003241d1003503485190311001900c4e01c011060b540044a0600e03c01070030300c041c4143d100180201c1c002c9030703003001041620402c0300d0600580080b06041d81040896114481506009010b01c50055119801c820380106402411402900010000172496401078900b0006081c80c60300070403c85007186001010218164060918249010000342905c4800c0301070600560710851804001e81c020000c0041716512803e = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 553279910 1250 553278660 553278667
    0x30307200310060602061807060311090405130203120a0806060a031e0b010f1106060f0a080d03021206010c02010906080a020f0c0109020111030a09090b041b0207060e0a06050711040e03 81
    0x1e42d02001400240907035001401400c0c00510408900003000364504050f000810f502840c0c6039044000744803021003c9072114040261604942c1c490003814000d16203a440514041c24610401d031602900c0d60121020724004d201034220f10703800022a0342d20050684400da030702d03140c0c01c100302c000346201c061001381030780c0c0b440344141039245c594000c45060100303072600c03d04040d00c8d130340640300550801c4100070325602c68070014082d81440c08010300d07030160103059400c1c80c1d0348695009043c41c3d1880401d40009a020820f00d0100c9202c580320f81d000034082c00c0c0009400b00d1500000c0c910880741c000c1c00c050145480c08540d000c08c20398100c90702c41400400e4591a011407034005d40c06811541c205078000b1b0404808064404030100448400020545a240056140c032403150080c00c0b0101110398881d90b60f51464074880904540d0b0401c0501c02d601801030b00f41403150151043c420080914000d5805050500030701e90050121080503400c000c0c0809030440540c0040c1c040c007000c0841840070b01010 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 553281160 1250 553279910 553279933
    0x3090f0f040515151e1303150510090507050d09020307120305040302030f010b0d0f0302070f03140607030b01021005100807060809010612020618010c210306090b0303072003 76
    0x52003036601c220341210004c8100003021a051483d001703220300902203141c0060000907000c007030401843c0c000c03949024204e2060782c17604c1b03110780d074110031510304145c50b10b4000304298400440c1841010707149184007004203042c1410010014003608918410341507648030760000350b550800056000308542509900803d000d0f02c1c009000e40c101c0d100c00c074041e1050142c540d03402c12041c0208020201c0207002c10702a00490b454078084400921000d6055004081000c10132180722120600a54003030610000074a88070074582e031810700d0046c0290101403400140c1002a0790200c0d0094030303203104080100e40380e16041810024144650320802c45807083c02d500103005908115076604c00ca00c224002c00074150344241503038409100a50017580070004000c90b5046811500101580e1001031604d089142c09a40e03a0484840d80c5007400e0f9512880700b11810f100c190303d03000d140040c1c800100144500311071030004c40d94a002e5003a00509500442000f00c41034021205e513070078600e400170b046842904c6d21 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 553282410 1250 553281160 553281181
    0x9020406020f01051303050310031719030b0f0609031c1707020105160c030314010326090a090c11031204031b031709010204120506161103090f0f0405 66
    0x284602409030003503058042c068441031051500c83c42070940d5012100d8901c0e601200c1070b0303000a04a504032100004040301041c00300b050030551004410040c1d50b40d90220492407602800c10b10440c0030942014156980ea40b9584a00b4000300400c0d50180c2e00d03001c00d40006400e1015004429030446050840300b452030703610000e02c1c4221840c2c1514007c041c0c6030200101c0c01d80300200ca51151400e00000800040c0740b043c543c030400b040c080d250004041511104210702d0071003e0340183d030320151681c084a04590441c1c906070035200700189051808071030308003040280c8506c1c81062078040d55017000c0c03d82a03014a08403000243d600c000c1d41d58554a481c0180300c1c0c2c0c0001d5405400290040f2560307912090001d18600180b40c0589507980002d00440e0404170030b8500810106055400380000903e0103224580e05400318890b5016001c070345014805206400070406400c0100030820503500e4000901004a850781942507445000d82c030403200205074040803241e81d840d00249050200070b10682c1 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 553283660 1250 553282410 553282417
    0x5010203041101081f03290906060109080f100e010b09040b0a060f141201200705060601081e041a0c0d0b0103020a020c01110a060e2104060807050a180902 68
    0x10240c13540b1401e9215514844072079803443e098407000f10700b061014000700d0742c1d19000108181201415400c4020490100040e065042e21007541076030090007400950740e040f030154805004001c00a00e07004803007010480da203c3ca0150b44a44160369081c869100c40f0082d0021300420030060008000d80c07d1600e805c2d4443c07041284c9a0300041e103400000f0070034841d030042000c100c62044140710074501c086010041c030109442d10081e520f42d42d4006007102c0b04c441c0da9960307202d548481851520b4040c0703400c106080c00c02c0200103e040213000020000038107040e8141d003003101c0401c5524900c5507140c2c5030000d10605403009403480b0907208000c0140b810030031002400b01c206200024405160904015402d078010100f4420140c0c0181ca20103e03d54071981107552081e02c1c4c6012500754040c1c80e2034050484084c0034804001e604004c0c1c00c6081608090500d039440d05c04910303607910301440c2110003802403001620358410400c000a0200310144144600301c500d0403419501c01c460360741c68070800001d50 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 553284910 1250 553283660 553283693
    0x90501050705071e0305030a020c0a290603010501060903080a030e011d010c080103240f02070305070b01061803030813060c0908010f0216030c0813120201080108011e0209010302070501020304 84
    0x340d5051380d0785008000f420480c428583c55100c0500b540c0324912800080d401c0b280352a42903125a502420205d90003c051440c51070b80b180c0192003c3c500c4128160601000a0020b4026030619004005503540f0105000450343c0001880da103c03044144100c01519511082c40055070030036484070000801039000307404101c041b000800c0b100c0c81c082415120a00244400f03040b1501e194001444406a0b28015400711490b1500081c9100a04101c030101e030030420303065000a070081840f000308900401428003601c01c1e410003c090201d07140c0c0c100b00340003242c040241000a800d01150820095580909840354090414410300401c9000100078003184d02c1821406c0d03080c0400a9a03135000c40c402c0361150200c0d80d101c2202c02606440c203843c90400508110366402d020040000309044082c0c031080500403c4c02c4044440da200d0000408401044c0c001c0c1c100ca9140801094020740340780e480c10141c4001c81000360700d27180340d040140d0090040ca00064815400002003104210f03201d6201440d0340d = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 553286160 1250 553284910 553284923
    0x10e0708090c0d1b181b09031113110309010912031a040b010207120501060501030f023603070e0a0c1103030f040602070c0b030412030b0f060c0109050105070507 71
    0xe60761001810794408039044203d4002c0003400042c000300d150420300141446095800d8081e440e44d800e09401a10540c038107007401543c0d28150325403100c031254110340850807540340414089007182c42d000d0b00c0c41c7c4041e48183c030402e5400703030151038005690404460b6480f10b400e060340368506a41c00c14064007083d034044950b800c0440f404103009019110b45511040050340700038084281006100050070701c00000c0b41507110b0544001400f00494501909a52041e0000b00c1c4a03032502001405442c548110001030900501c880c2d88088480409400c0140c030003003140100c6415116002000c0551500c240d815010b12540810241240030a060180241c0d081c01c000c0c2540300700b012075110f0680445201d4030303042000419800c4400250a64026015090051410700d00f44d58070003070120103500c1102a080080108030034000c80c680e10841c480c0007800c040c001c450740a0000f4981140754059580718542c0480d002c075800f4000d510440d9501d51200003009142030841024160b5040910202c844 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 553287410 1250 553286160 553286177
    0xd1104140a05041b0305150a0b0c070b04031505040309260715021e0309060d09020112050f07120b06040f24050405060a020a05150106030e0307050705010305060a0905010e07 76
    0x40b414107114965041d08200c13601c0280843c610301c202d01800000e046402124442c4140c01d84540e03400350a8401404000340841d0764001c0d00c1141c1d81841800e90008007502c00c107201c20808624a42d00d0000860882640090143e941d45419645045c00c0c1c1c2101e4007123402101030f40400040b0240c940c500024000c101e84100e80d4070121100e90003500800a00107030441c0c40005101d40c1d00600300413a9107445002c0d6400c0413200f001040582d04021051070909440c1c052880c00c1d035170800071040584024150500161904050764856000040c02400c00c110007404820300c402d0720741e07100c07e02d0214014100c55495544000080701c0c88014002c190482e60807001900504103541e04100c0d0749401ca858042c140744ca40420401d2541084041400307600132004104c00045042c80700c000809440001d8920b55410004010200e03401d5990711712055000b0400680030950000d070407802c844003440d0100c2c05a88540c08140641c1040d840640e000341800c0001c01e804001c0595280708081d5035894164 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 553288660 1250 553287410 553287419
    0x705070b2a15090a170318010207200a0905010902040f12051b0d052a060a1b030302040510090602010f020304020d030f03020c030d020c010e06010506030a020d1104140a 74
    0xc101060480140c6a81c2c40400d800c2c1900c124201019802400350094a81900d482c0e00ca11150724032001c986117054500108100540060b103c640c0340d800700e000000c60408600d41d0790441000c608603035a01400d200088200499a944210b20020f00401d903021b2049503907a0105a019400500595006c103082d800040f031407803088496080800d0b001400ac002b40001e0031b1002a0801d80e140010350010a81502e40010070070411004011218500c00c03e440034242d04d60a60110501291107441000c040110113011680890f540c041022180321014048025203030a5000307100300ea004940040900b90078440050300610107504a4150340c000384140180c10324000201e1000310703230003584003e52030030900101e4824510030300140300a080040c504640308280c80c2c41d41d045078410402c0705070005460340e00f500080c059980d240e24144020112541000002605800001d01c00b04040e5400308079840e014407070340c120110300c00303038140b20a540da901d5142682e1420301c1c1c206a00c3c0a00d003032040004 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 553289910 1250 553288660 553288717
    0x807110411070809030309040203040b09010b030f0312090717070305190206030a051906082503030203040b0d091b1e150c03110d02030712051204060b060705070b 71
    0x144000075024102d14141556a80181c160442014160036110a2002e031405403120b05c02940034600540360002d840c0b03400c9000c0f60079030b4070b00898180250403000501c2c211990020958010304c244920580c00340d07a136140c03450f140003056442a1a52a107801c501341c01d0040100b0310300282c81c010405d80380c03c5500c1c222020030502c4e9108001703402c0201080000c0d05a2010750055402c121040d00f0080f0001800309140240d601c25046900c582d007200814400c1c00c8645041c0044401010300c58607205031541e01d029449004910540c071060500041000c0c0b01641030f440107010540c4a0004502d61801824a03043c24205000382d141071900411103a100300700c1c2618243c201c45055001802c0c80c10110000c8070103c100709011002e0000030182594540d10500c50034403030601e40d034010741e00e4000c1c90a04507144980300c001c00342072002c02c1100702d00c5c0c1c418100c01c255125400c5100410702c134651700041501481100e0025000740541700340881c11080c21801080007980500e8814043d15485100300b = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 553291160 1250 553289910 553289921
    0x15010f030b04020301231602061005010309020604080604150501050d0f030f11120703081f05060a1e02010605040e03040f03020405100f06080f16050304020405040c0f0308071104 78
    0x800284014801000010001690a0b501c40e00c098004620b48040c0c0c200350b006030440d0030224603c1c518040c1040b01d5444401019440d0142070b1000b0b15490402a07020b101d05829030056a0400d41c0b246031800c10b54548404443c01005a1800c64240f4541030a00e40c2c0c110207103031075010090f402d02c1c00009081c9410021070415681002c080603030b07910250340640d608440400340005001402203000f1217610b0a0102003514540c18680d690384000da0f1130b00030500a801804088801070000c1114214840049101c059440545950366248428042940c048145010307540d80002c01107188d0414a506400c4030341100c1080e50180f1841c0000071500c0d84a018a0141071074607410a1810405840c00e0303008107400c40310014400c03410f80e48401c0231144040d501e0300703c00301141a0900f402b003079502c2e075640301e81e2014890040685240d2850001081d511001d03001901c100c0e1500040350078000d00c444c0b0607009098051906003219907902d001459038020f0751041e034426880c8119550b040c00e184c003a0 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 553292410 1250 553291160 553291169
    0x605060304240e1902040605060f0a1d0406080f060906070f0e18011d0c090904020d03031d16170a0f05010f110d0b041a010c1e080c1501 60
    0x30010001072849110040300e080b6030000b1503407121250309000c0d00c144000d807070340100d07101c0c0c100305500c1ca801400140e41e2035900840c0200d101f00405468405124144d030924803280c5000388184900b003400c00020450b120000c2da000d8035140d80014203040010766030641c102014113448607580c4100f005a243c075022900b180200f035117102e01900c50b0b07101303240c003a0810000405002007441411401c204071042600485071440b41e542d114811880020391031a800919500c00514050317007000401c50704100078200a000d10360300464401014025082000080c20036990759803040d03040c20309569034005080e284002c43c455050040380b01900310240780a000419002000315440e150f5400300c45251100068800b9540c6501c848501303136184c09651150481340e261a502e41e19600d40070001c13a074600001c54404d0b0724181c01c0f00c8001c841018080d550f04001d007440c414401c42420584120000c015078206080c1c4110462010440340b40b018004840040084410a107214490305050760340c213009 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 553293660 1250 553292410 553292423
    0x13080606031f0b030a29090703030e0d0206121015020a20010908070806060109291b0a05161203020c090a0f0504051f0204050105040b07020a080307080d0605060304 72
    0x1556168400c503500a80510344002d011101026069182c010aaa0403801d44e1180312102c0c581240b241d80c2c5030524a41c00400440248c20801d296690260040356030b01d00090082c80c0c10303201d0805541e0340c0020340e1281c10342104182c2c0c241c50190300b0010102414040d1042e2024000100c0b91007034070000f440c510300d1b680080000b16000e0050070011040d44030460850410014200104500317100340f11440060041800038035207400d081c030004d00035a810741c112801e010040c1d48921140d0030340c1000f050040000040540d030b00d0440d07810345250f6841c00c2e103500d07503d44612400602000000110040c4444103982c02804030303038482c003085002c007040203000303401684856640e404619044802e01d4000300004d01c005410741008d840e00090311000c0344c042d680e81c0c010480c00c8034068600f2185580c0e001d00f456007140b5003424400060182c0c0118011901e00c5040031494000f10349805200e0000781040300110f03511b80e82c0a14000130641c0c003044500c1001420103500046500b44601500d00941d400340 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 553294910 1250 553293660 553293703
    0xe040c0e0102062a03060301090503040611070b120703050a020f0a09170c090403140918060301270f080d1103240d020907020c1f03050c03070c1e081308060603 70
    0xca10344c0c49404c0501a1366065581e0b41a0f00005641000100020034454845000801d05802518206480d65000d40840f1300100301c440c101020920026038018228140010107458499012000f0301600c540584d4185c030010b02c0074419a001641c03202180c06080c2040400c005c500c002584030308007801040d412010688c040f0780040d01a60258281c8070618440c0c0c0c0c01c28014000082582995041c002050891482400b4482c2000e0042c10503048481c000c400c680c03078003900c0450180581c41c0000d420f50550111070000c00010b44211084c10144e4441071100380480c580852003644140c0d68548810111080d040504c0d454080c8180000c400600010039520360f6001e101c4041001081d0100314002c400305240c0560346d00b024100f0422020090f207504040041010b02151005842c0761103455040c010003590aa00c0144001070a44c00f8a0515183e07116074841c240c840f000740b000034680740d8003191058903c805800071204682d0300500311102502c5034028141c5550050900006104110 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 553296160 1250 553294910 553294981
    0x9010f0503060708070e0406230f280b04080d0f0c0302061306020c0f03031602010e0d03020a05130815070c02010801051207031505040c081c0f0e040c0e010206 70
    0x2134081d13660010441c206503444806000c00502115950380100d090039024050030509010500341943c1400800c0e14255441c48039400043c0121504c0b50022050384080407841d0242003003103080742c00900400c6501c98656485107141130300c4501c89000e101c000780c0c1c104d26800305948228600d0340050f4140d00900704540b50034402c510f0030040080103950441e003c1148060010003044980c2d078000300b00e405583c4908140c43c4030742e503031411000c080c011607041c0105100e4900d400324010141100318180142e03030340d48000059480c0c1c05403000782e4492880c5103030300242482d030101f1080401055500c200c0070581e5801e1040d13461400426021340000c80789801403120742048200390340c206120500315131525689643e501c11130006030350390120301782e160024007041080810001d030240c03500d08080c22400c280e60b1084110340e141410781d030303003003000c01401000703034500804070002280c1e8007400c1800100c03114a80946139a400707030642c60041c494040003448030303200c20103403200b408807000d0f003250b114044 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 553297410 1250 553296160 553296167
    0x804060309080c0f160f03050303010e04030e03060403021c05040b1b0c04020d0f06090207120e15040e070801061b0602033d090c0807030c0e0307060e09010f05030607 73
    0x108201190b9041c0100989541540200300404032950800002d1424442d2280e428a05180a40c4940328030b06445406000051000c810390b03055401a600f40001950f0340d04045404c0c3c502c840084c2d405008031018041415070220300307800b84070068030084200c0d610711507041303d05204a1088500e525010710130340d903aa9040e030301c84c0c0d0215580d0034100d88442c00300710005412684403c0c0e060503c00c1e41e60084101d203c466004038001015444000c604014454a0308140c02d001da980784e100300000b030a07842640384d03203080d01c064015110503251510340b41c9821940b5000f01d01941d061010941c000c00019016101d0000180704c0081e1401d40d481991031607440f80d000e5040602500d13074092360b18025020101007013410000800302901d040304032004403901e0401e588283d401c104002410f003150003201940048180ba00040c0d0340c80d0001c0c824500800448108440f0382d002c0e585401540c9000039020307481459400402c1d001c07900003c0d6a41e03030b18120b44c00c03c1c82e1842400d825411613400201050f00 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 553298660 1250 553297410 553297421
    0xb0412030f24050306040f03050c0102130909060510080319050c06090c1e011e0201021204030306080d2610080a055d0d05012108040603 60
    0x45030801103a4500700e008a481951101c9540a1412a2102c81500328034500c28180005060035405858035080645940400c501e90510140a01c81c0c002200c10341c448095040b900e4140c14000b0f08402a6124004d0001400215030309941c40ca04002c0400d4107036001c0c4031780c101100c60f046d00540c035001480c1e103242d42107280c60066405000c420302c80c4c03d13071070f041c107001079445101140701070540440e0280802916403101800140040801c0702d520413130380d03000740c240c0700054807450001c1c0710150f00c21301c1240640b0403501e08882c0311503200f090204060300354008400383c07800981034030802c40c4400012151a00d44440c040c5004584103c2450141803040840b90080c0c012000c1080381621100141d2420212010840385039000a803400c401580360800d90100c424103100030525a10702144015005441a101c10400c40400d41c0d4aa290800c1038000f0380c008404020240c1c031b5442440da140000c003000d1081104118007420761028550042c40802c126030340c800b042c0c1d42041c1c2044403c030700401 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 553299910 1250 553298660 553298693
    0x3050a1407120f020c010908030702010e0607141305061c060b21100308030c03040309090c051209010b042f070b130312141603060f090b0d020613030b10030b04 70
    0x10760800440c0060300b8280144107c8038020384102d503503402e107040c0c000e08590400c4465940342e0440700922243c10b6100c4a600381300b220808800345c840801070100c452410240d401313280d110000007560403402d0010301200b40300c5c5090345010010a40d032a1b00c454040d106021f151001a00c00030002030142400f080c0d0142c105800a0074000029280e50f43c4160755031040c2c8180d1a001c2012040008141c1d2007031005000c0c00d684803060084052805000d8034502030104514011a091000251001c009511408a400c0b0042c4284902c8425042c0b50b06510220000b00344803501140c00724000402c00d100311f980d400e03809814181d48d41c0e600c200d01d00c44038407064000c030204540c0c0e070950a03c0b00c03507134051407000300702c510250220303400c0103600e01d01502803044000c070505003881c004201e101c41e002c0344a01215400000402d0461001000074803114140e0002075016002089030300c885041c07041401c0581e4440e1310300d4507040d00c900c540310104041d144001400d441404001078009401c04400700c0024 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 553301160 1250 553299910 553299941
    0x161101051603031802090f041103070509060618041b030f02040e0c1605060411040c020c010207091e110a080a290315040b070905041506080912030703050a140712 71
    0x70001380d0300186140c42c090305c6a019501481c000d1100f886070707024a02180c903004030014094245841c2c01701e03840540c0181010700c034100200d8210a0303420b40e0244d407980110700800403c40e00b40040d100740c030106210307407546c0d0029150084035201c00340c503403003107800707865502420790300d1035aa102d50b50002e41d1003050305180f00800004940c0c001001040580e0041e40b00d085c1c40c4410210072800d001c21200f0340200d00701103608c030803901d0969907004592801075864007071003c1042310309805000c00a04619180021445c0781c960188103845d02d0b0005040780d9080c5030359511141c4c481e2804903080c1c4500c410300c1ea8441100260020014001003d148171045000d016100310f040e500142150800c01100c2c00c1d160405250200a48507601500300c4000d40340c00c440400154880c142d803001100c048d40240700900c8070010114170007080c2084594030901032410429640d1030810b074004c000d0603040e02c61009041c1001c1442e1018607240111901c115100d44c1e8001003051005c84040c0544006070080d00744 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 553302410 1250 553301160 553301201
    0x5210408030d240b1b0c0d150617010c08100312031503020904051507020102120103110d050a03090906170a021311300702070b03040c0b16110105160303 67
    0x1c9050b803425520084c00401d801c1511400c0c24070070100f00d08203030a0085281d80160310140020b40d141e4841100a80d0040c003001c202001003540980101650340103485d642c149444030840c04441504039101c001e6055858820a0b100d006c0c50007800050ba000c000c6c0948104101788080394031981c4110028900041c2c0007041955030703008161090300989059455400c0040c512000c2b040740320205810440170301c02180b0301500350b03a84200c56a018040100200f000076802d101d1a0780d01e032000813110341c00c2415030323100c11842d24000d007400c0301c503120340c0e1203090401c000003605110030441052009102c4002d040995556802c02001c0059078200d1103c1c07a544043e03441c0d060075580060030381700361b00790f00520030003503078108650100c0041103801d169400c0300c070200644181c0c0480c20004541040804984a40300c0d032a00340340c80801a0003000710480c1c0400c11150603044800b6800705280503080c6140c201c064400112a40d104d4600d607030310300c540701c0084000005c0c804c2e406000807a8000d0145c411 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 553303660 1250 553302410 553302461
    0x3040e24011b03030216030507021806181305030f0d1505090106052b020c0105010b0f0f0a03090503030f2208030c07050705030106260304060215040f020d05210408030d 74
    0x8948100f0071b080d0001000030a118003141460341c03440c440074840c11802026441c00100044a1034480058852401581030100d100154590781c0e1410081d404001d5a442c0e2008400402c00e03500026401003945050000d004444101075100005841c2c0142402160384e0800c041036034140d00c01c80c440c10b0038007155403402200846070b40081d1010446013001603900d521443c503841c25640180c00110b406a410040c000200390b8007000c55080402065250362542480c41058005242c00a009000e901000041040c1760341d24001e001c0c0325051030400406180b9140c41194031880340880001c221000804c04210b002c0507850141c103846115808a41e80b00e070302d4078082400d5421540c44042d00091809580c83e42440e003c0c011544003d445000b542000d00e04907000755900d01d210951152103d2a001240501203030f0740c030360841c1a40207890340c540402c4514205541e541003100b4500c030582e02c0c4034034100c4000c2400c2181e040b5050000150706142c000c45003100144400004400e03101000c42c1d4103c0d = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 553304910 1250 553303660 553303687
    0x3050114010503062107410102030f040e0103030909050415150f03051507023909040c030201112a06190305060a14012f03040e24011b030302 62
    0x25100f0305103c003800303810b40380a0146003401c0412810707d074034855030321450b40b040c1007822180d401c0c21031001203a40d130442074100503030070b510612140c0000c6600006000c24030190070105141200d100e607440300c1e0060ba50f117007400102c4006a4001380240121652480710308240d070000c0f850050b55415444a8a0b80c035446001208800c0c0e01c101c0f0030346c01803a0480c001880c070031585a48603c1c07a001070030310b10500b685128900400202d050602154941d0444198418070000002050b0043c003100d031941028140038000c0d40c4240f10890001e0798010701900d44510200354050324a19180e4040f01c80304070780201a001810a141e81034100c001400034410750105400b4114460603162800a043e081540600c14012801e421500c60310b041000c1500560f42d003da4184100040005500300d0305e11007000b13400016488a240c0c040c20f21012074040b078118860303d40d0354001c4019021900100883d81b4801c400f403903000c1e0f0520701068660121401c02651811041d91007442454014984100801d829 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 553306160 1250 553304910 553304959
    0x5090411060c330c0d020c031c0203041b0b0405240a08011401022d1501060306090f050c030c0708040302100906020624040c0306080106030807050d0305011401050306 73
    0x1440700c0b2505140d10340d0a81d0504000320b403140f025088503159440c1c00c412919451080c030a0301115981c0c0090800f03001c980c140150b40451100d01034001e03603a02c039251010083c1d002034038243d4202c0c414424581d0501c21540c10f100841328070740c505a00b07091400f420448e6001300c1d45100300f1031132402c092611104882c807004204841d016105e40d5500d5050402841000c40d003482140c1c199072001c00e003c40d80070742070442086980c4011581e19212184248070a0401014002c4404081c00400000c075426416800101c2901c010351003c10410080c00c684109841c030554211038486010400309902c100241c001b8035499000f41c541e04d28240c1d907540411000d01c03104140400040101000784450b81e4140481038010a500c820f550100001464240e240341d0240324081c070403035070b48803600b051ba800390704040024401040208211541c03405e08415552220718112000d0044910500700c40d8064072805068070b5034020b0396044580e600006442c01c2d40f010f0030382a40420301958004071281040d021 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 553307410 1250 553306160 553306183
    0x7180609060905090d030b030601090c02030c06010e090d0302040b09010c0318060822050d051b07180c020601420e0a061d061b0d091e05090411060c 65
    0x780e40c41e01c1880325017411a107010040400d0b00f00202460142d90004080d41940c005850000310030385400410380c43c521411035207964500820000040c1b000c0140c0800d44039504401c00c0d16040c60780681c08a040b40314500510951580034010b018a80d4450034082103d144a03080c046403c0c0c40030440849001d980381d020301700007484441007104450001924031a0034100c0e0706080b060a20b0b030356680d904d407000d0b5000d9004005001c20400854081a200d00c103640c00700c40c05440c0c100c0d07141c5c207803003d02c05018200b030720000f400d081a085445100285ca0381c1241c6140c5111121b603c901c819039a0030307900545d2000034281d034070300e88190340050ba4003a210491003e0346421002ca40302c80c00340022200c0d940d0051301444180c0e0940d10710240e001450901c1000e003120f1080d40c41d403800c111421300c281f404031a450380c0e105543c09108065008040d070300603901c410651080890b1500c0350b51544c00f06902407150000d48100100f80014110804001c1c20300e8010082c0303080031101800c0c1403611418000 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 553308660 1250 553307410 553307429
    0xc030c1608100e1509160815090a03080106030b0d0204020a200d0c08030405030706090804080106091a2e091a03040503270d0308010e090a0201020718060906 69
    0x504004410081000300141040940705000410400d41020b8031610a44d4036007000304166000a1400c00d400e005040085080481038174443d03813a004003541d246400c4420102c0c907101180400c1080c0400a1250b559550540c1c40c0c0030181c0c00c1c8130044000e800b20301c0358240c10441c0b2400307c0c00142d645001400000c500c83d95101003100c1484140d200340040300e203080748a9000381540c80c00701d55101584007135443e000b040e2544d40303840f2031400034614800e210011b4021441c12035202d0801c10950001c0003102c00601c02441459102e180d89022075920340e000c14002e1060009412081c00c061040c90403010780c681c0c40d803100c00b8261409841c0245480c0d8000c0000740317422000d0140c2006008904124000303648100d04610303180e41da00c1e82e00d1284c1a440b054144141c0400e00855008007080034410101030200d0a8034516071030060140142030003500c100c3c04000c0000340e00310900080307440038107405074001c0950320b28000d40c440e000d02c0810f0045049984464010601c0c0e00d69008100c001e010050 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 553309910 1250 553308660 553308703
    0xc101b1b080f0901230307050f0f2b06052103070501140106031a061b0a08070302160608090c040f020f0711100203040b03040615080f0606030106060c0803010b0c030c 73
    0x180b030380105e841c21640f9443e03044c4071030700003540580a681d03101b01c45040299039010b00f840751040c1070040d40c550385842507000942d00d01c0e034494150903410045001e0304c080981ca815018090079181d190203030136080b203448035050300782c00080c1d65250f01083c2040260780ca404440d448560030340307521042410988400d60300400c01154188541c41c1d1074100c600d1803400c070040000c0081e00c1ca02c01c0e1a136112600240d41c08506c00e1002c244000c1c001c155008203c01c1d40c0e4052403134080c1d140c001054903480b035094000b000050b2a8050201288180c1d202800750219845002c10003004021210444a18a5080c0304880e1440145401440f480d40075a5240021001c440100483d50740d00d440210219041480f04000c4c4040803010740750003c2d40880082030b84031010954001005c3c0c284c0c012100c5200d2110005019000070420601a04d0b044e0000c0c001d0036201c10301a2000001540f0080c9070300010401082080c1128002e0150320201d035041c1c80c541010159803d01d44264171122100b54816132 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 553311160 1250 553309910 553309927
    0x6061c120c11030d1d06040803040807050109090c02031204050304170703060c0905030a030e150a0302120c03060117100506030903030702060601032306150f0c101b1b080f 75
    0x214058a00d02c001100244040341e0550002403a2114405c40c0380090700d41e821034000c40765140360580300900603281c1102d440d40e03039482e00c4030303516990791003002d0114078039610109130340d1950300500441d44081e400540c07404120706003150444c0d031300410075121804140300114480c204e010282d898070786540e000701401030941c01c01e03030101e501710f65440c024002440d90400c81900c02040e900d442c9a00f41c1840c00303e1180c4035010812407428482c0b405030364503000030310b0301005415a002d0500d5042001d00c040b007958420105001c0d5200950b10607010554640754440500d40071110a540301700c0901c403403d4407960300d202090030f0340c0040e100c0380425003011081080582e0b04001c02c9921402c00d01e0144402c8011000d4076074106003404001c003801f0740317400005071a61211400403d0800b90014080e558140504028900307030030058035019107000d031320003045102d40740703026100c4004214140c0b4506801d1495044c0c41000c20122540c90003155000840c001c5041c0001400802586081e040c0ea204a803 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 553312410 1250 553311160 553311173
    0x5100c020606040203090607051e0d09141f1509050411090f0f06121c0302040f0803130e1b070c03172a0a050a0f05010b1206061c120c 59
    0x109424059132040c8200000018001001c9400038918100955980640c408410403200440c0c2440c15081e4009881603c00d8400da10010507039020b88600c1d02c003418440b00a0303440e81039000309035240300300700f071000c11a1a1055008d8a600d04a820301c100401d9a02c1c42e202042d0b4000b161b059035240d2104203280d070641803004000358404090030024100740b8058660800d584c5c0040c01442c05200b90b001d010080340c200f048694000b1400807090f80708804140c2004002e035000d405142901d20000d0b0000544140c00403d850081491420f00922a4100343c2d8071100320000811082643c1c07003041d07803987d01c1c842c04001403103080d000d1400c04602c5c2e42141800342d4031401061080640c0502041445c07041d103620030b030311600004a24020040c1d00c02400340c0500d043c0a103170300a0014050050a00b042200e41c100c2103d80714401c2001348a020316910810902180c4441c544200780c014500003a558070b8030040758026252048003103034a8500c1c54907591307202c2300c8584400020450a40492007031108 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 553313660 1250 553312410 553312423
    0xe0306090c0f0d0c061404031b0320090a0c0201140406020415080c0702010e01090f0806090c03120403060b0d06020c01090201090509090d03051003050303040c0905060f0105040b0d0905100c02 84
    0xb02a43d101d00c48410641d038042c8140801c2c4111001c000011040c1c0d11440342000480d0300464200000840da51882c105020f0a64200d00c0110f071f80c2845096001c241c00701500c4001400100208004070a5545a4508001c0c1000070302c48070840d540d071480b094204148408450040e4082c0e00c00503241c44c00e00050a5001030305142c3c1e407040c0700001d010845850504400c54030a50f074203280085503c40c0c0040142d482e83c81c0f542184c0c881c12141640071980120000c0c0084c41600c004017203410640c40e00042c5611011035160604c0074003010082400404c0850b00300c00d4a050001c1c110003004029a20b4400c204d0300b1442c24410180d4640c565607080d503901102c00c038050300c400c8941c24a2401c0015040c0d55400310710700b00200303043d03c64000680270542d50b2290f000a40d0070206496803484c162502002c003841501454602a01d400c001c1011410005080540c080701a120545000e05010240d251600320813103594405403210010400900b041c48505c280401005020984c150001000380c1040c8 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 553314910 1250 553313660 553313689
    0x11030102070b190b040618060504061d071206031a340314090f160b0304080306040e010614040c14090105070f0b2404051b09010e0306090c 61
    0x80c010311492000c038004a41c42a00810030084002d50240e4401c007200141040340e035226031003481c0000005074144d00011540f00d200d00a5020007201e03413154104000c444050054051001646800300c680140345000d00c3c1d00b1148509080640640102201055a2054200300c940e11034402404091090b45018160030403031014114030b400000a41d05412003507041d44081e145e000d0fa586240e50039003e030703104405050100d84684090711340215095078412140c0302d890303410f208113490200c020310500000e6041d00d1400340c8407803843c2c0311500d94010f0380c0c002520701980701c0ea030394012000d122070074403440e40105403030307182501d800c50702d641008101d40002810100740028601c0320412282d543c0d044171188003090130620345170925070a00480c1000f1000c0c000344081000c00030301840009000c45080189040c40304051011044002c0c041030322429107410b55034401c51004040306194080251072842010700d068407420b1100e000092500b10709031040040754202c0d6040000605110150140c0403 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 553316160 1250 553314910 553314913
    0x509191803090806190b370b0708090409020a051801090606030b0105072604030b06210c010f120609020405040e03040501170705040302130b040b030729040e01121103 73
    0x145880302e0503062008914200061786543d4208075042d076510b01d403908111a02d041302d0000340d1602e0000e40b1100c000c6840c0c800c080408940c0c00020322200d0f00d402c4460441c0c0c09840743c1d00348523800040c0302c041e011004089074802800200411380c1d031541c190003c00c9450019848017554034228900c4211100758004408250130a0190305003a40c0110482d003140d0340c03110012244401c10030922840803607401131840c2010700080c3c00002d0050161003140540001c450405c540c0c0c0c82100103040310361401203003c3d21900944242040c0b58004d0034130f8a949543d074205070411141c40d8005608a8040360800c4c00d89690102d410700c01c50801d8891f920080c2c2880c0b0086d841e00f0304200018041d054002d181d0451080d40100240b04140f01d201994001d41d40a0700081c2c4141100c5c0703060307010380500c0350b245009a00d07003503e810003032400282c08011039040c001e800c01c0d803848030f504000018010030540c660f070840410002511a21115050340248544803019070070000c0761525030060244018014420b = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 553317410 1250 553316160 553316173
    0x13140c010809011815020f04061206060504050f060a140c030403110a0b030f13051606080a1a0f010512011502070b0408100b040e0d050310090e0705091918030908 71
    0x41342261001e904455800c9594003490b54102c07000d650191146552170041003501160000707015070818520200701d02c0401e004e000e5191100812180d5024610803694400c0400204040d1418581c00900038516240341c80e1000300d00b003c0b404c21295001c000b500c03c5030fa00c0010b040003132000c0244207400da0761049075a0214245403851000060001814072681c504406002c1000340303180b14104140164000709450080c0310800015003081e00130301c901070100704800300280300c2020520500608816a011030100401d01c01c041c00070007801c800310241480010400c0090744807440da0194001c222101401d0b003001070010f40282401c110340e00c00305407080301740000d012441c004207540c140c18040c0d040005610512400080240002400311800c600400b4211202c083e48a0000c42c400d03600725403e0501269905124070440740d58a41d081c4480e04111420f101e14508044000c0d00840301c4440d800d0001c0c80c2041d14000c645002d06c95109000300440304104064014103940f0040c03142e40c0240c00d4 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 553318660 1250 553317410 553317431
    0xb0c070815040605180706020607120b010c140718020a030b0d0c0329250207030f020603060402091c1106031501120e0304090609110901020706050313140c01080901 72
    0x40518001d08001c00503926034000904184501282203d21782480f000c079251655140d034040d40b15241030b200b610018804007280d5402820900a020b9840c40c1a99007014005d02c640f81c5085a030080891400c0d43d018008001800c80101109403900001160740140d6460300306a000d011201200e0403d80100344024040340880c00115418003101d07000714800040000f0444101d054491003030b8003040d54424407040c48400740c600b65401e440a9007902c1c10b4807507010341010a85c0c0e02d101307502c0010548084292000e005041450240d40c000c0c001400242c1440c10724800150780d811001c008143c01c07401251140248651113201196184d0240c641501e10f003004030401c200c01030410b100c9410b01106a43e1000000448c0d44451150110042600d071101d4481213044042c141c01d118000d40c25050549010910f20b1a4080f40c5800304140c008002503803401109481541004000e00c4408550907000c1010510f504101840b004010000d80002c0030341d140091314400c0090001c1035140c2c03401e8039890 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 553319910 1250 553318660 553318693
    0x50a03060902030304090c03090501050f0c0a0513120b192703020f1605131a0d0515040807140d09060c050a02150a12050c090f0d020a0b0c0708 63
    0x69035002940810114140c0c0042031443c4110b0b0721550b02d49160031404100d49900d03a0100540e81d00c075030000e00090b00c4150784265052030036215402488000c00c110a52180500c00038000990180b480942c100d175550100140246000415a0310442490410015140110780a9248000800c0070811010340d21044800900d99680c00c1c0000c00d030006020382818000c001102c80d1204c0725040311500c14603c1c1008400085622446008000e1113040510001c00c40c042e240c0c00703220f50308041248071200420031030b0344000e10310241c402c0d000b000c00910068000300c600c1441203005400741c0d82e441c2d00d84d140250b0700d10300c48065030341e840e04000740814a442e40428082c048558610b0440715084481c204181485880030009500280183c010099022000060f010051050720b43c1e50300000d040580703500340c8504690414080340f007000b110640e8a00071003180c6422202a00c0d0703030041c0b182a400700c1c0c0403802070f8100144000021035990100c40c2c007041580e010b45203810281200000380301003203 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 553321160 1250 553319910 553319929
    0x50a0b010e0c0a1713060515010e040b0306060f0112110a09050103020c10020d180b0f0705030702060f0a0207051b15040602070b0c0328080105010806011205040c090f0e1605 76
    0x80b60584138500c0841c3c642440100c07240078050300b0410402060400c0c00d0700300c19081140c180d5a011501080c140d060924042c400d5440d0000007401503e01c40d5200030070000c85200382e48585040c0a02e448011801031000e00c1070000c2d038804589502d5403552441c0780031b01004019070005040600400c01d180b9000c41c00710744c9407000c0b00c01d04400350b129191040402c001e807103a258804000c5c00400d5a80d003c0c801c0c4442c81500405c0d05400d1100691550070080b205484100e45030b001607844100401e08140c003171a58554024218200107040008642d206400c1583d00d038512400020b40b40100d440b0340c03502050a110b0641204005403509141800203911741d010b510504480d00000b142c65103048005001321000701c00340c440b4030080401083d03120036205d580188500e0002c3c140000200d1654080c01d8624000c2c80f050311071211030780c2d840e000300d4081c01005000b110f0b0303520003480020f900c58103401030031600c00d170024000c40c18a0300002c08d41d2400d001c0003130f0030411051583c0c08000c1078442c07107070b203 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 553322410 1250 553321160 553321187
    0x6140103030c0b070912060516080c040303050307120f1409011a0103020705070b030f15061614070f1413050c2d0703080f13030e0103020c0a050a0b010e0c0a 69
    0x404035a030302c42e0f0742a112010b6645c000107036040c84006e502d040100ba0307809540314402c03808a00021010602c0c1c00c44010008840d03850130680208020b02c0802d0041d80516070103411841e00c4241c46c2c80303c286800640c0c0100d04000009600c8100c213102c03030403890b80002d6021400c20000c12091022141c540c1043e060545002d050641c0000d18000b4480c042c04840e015281d000c408561ba814000101103030301c41c04940c0c802400c0c104d4501d011161070300c00304448280c00045803541d81403000d0344950302070700c042c000c5001e030911510f0300010380400250301d0f1400500c22900d140d01071500c0101441710107400e80070b882400c913180c0000c106070344c42410240c13180301154248201d04412102d102d00d960b40e203508045507001e14081407002c10903a001305c520384a41d030352031450b800d1030701c8100c4000b60503d840040103010603014007a280c1c25510076406400f50044400480c1c44084080e1501418003405002c240d840c1070500d00140b0950700190005600500700d422001d04e441540903008088400c140034 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 553323660 1250 553322410 553322423
    0xf031407030b060f0c0c0901090209132f04151e0e0607140a1a060d080915040e0411030d0c03080a06050910080f0304030f060b1804030203040306140103030c 69
    0x102c0c11156103510040c1c0303006407165034201d0369915469130942e660f07281d91040144606500000813420340154020b0350a10380014000d06040110041ea203009004032680c000075038164580c0036580c000b03080706401d0510340280c0e40d040d621800c158224a4481c0d00d48107c0051001c0e6043c6150b51561040c403034025803443d803420f0309a001400001980600c0781c02800741c217000b03041001404024020850fa10840c0c4038140d407202588150304c40d08158241200d00c00c3e40f1852940c030060125001074020244100001c000d0707004545882101065a041500100f0304824198204010442003001c00c208070001100101840403285400800040d080c68008042203004000705030341e90300680100780030b07010060850403607182128009810710300c140314240551241280d00f120001011089400303903074000c81c41012003041500d400d40500403100400d50000d0401c418000351050300462203000310700c00c0d0701940e6514650b041040c10b8418011002074540c410800400000f80c001984040b050380c03000 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 553324910 1250 553323660 553323671
    0x605090a15140a09080607030e0613020307080d0507060501050301020f0d0228052701020712080706021b1c0f0c170d09060e0a0302030708130513020304030f03140703 73
    0x100304581c2100d00210400400101040e000ca5244d0404c95840036105018100e418503038031100102d003a10744000342601c0941054010031071a004000c0e5290000f40043c0480d500c89a9a0301031300d180100e043c245100140300401c030f590400c4850b004041c01000c0450096040003103a030034021113841010040e4000c0b0b40d0008881203803090b400225034002020b04102e030300b082d0380883d010740741c1d603c05042101d0318900c82d151403c1e040002c0d5240d004010069004281032406c00420054000c038a01056810410921582000034085d00080112200b51303001054809641d201030b07450003002442c0b0407508009504100e142c0d981c0048810a01d0029140805612000e8100401443d46000342030150382d5002441d6080684c00c0e811000045220b4542080407041003603404d511549203010003070058104002640c0824800006440e2162400900301861581c0d00700081200545101040078282c0120800c010316420102c5c00c503514500e400c003030100302e002608a50000070014501014555a030 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 553326160 1250 553324910 553324949
    0x905060a050f100c021503010602011404200a2411030301060215190507031a090c0a032412030822020402030c0403080c010516020a0f0803060103110d060305070605090a 74
    0x12081302120580150804240d040d0203018021150700034041c0c103015608104000851003955600070344116040703000791360b4100c045c0d42c0102c0700340c01c5000d055038043c400c0d107001306d059011448400c40070440d041441140c1d18080001074080e20b0f00d8860351380c05030404d00040000ca500801e4049854548000e1680180e59011005000728001806900014908810081482d0309a0f000c140890520000341d001114034200700042d5240842d1100005441807203041c10090003038002d03841c1001d1207100820140b051500d2014146425030212100782240d200040606800200040e04407090f00c041c48141808842c42c441c0310265600d009014903170002c0000ea80d042c9100680d0003071a40250543e544428004400d40644810703205403082c21112130036458514000501400301ca80d11840303004034451540c441600f59007000380414180f41d1203005040e81c0b0007101004143c0c059001000140050a6003446460000181c0050007132040400c03010035956190189502200c298102c0f641d11042c80 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 553327410 1250 553326160 553326167
    0x6051e040b0d09060605190e0c0408250e0c03040f03021603060603020906030c090a050907030b04030f030e0c06250204060e0a050606071208071103040f0905060a050f10 74
    0x115803107480340700300108850603282c01c0c94100c07200b603901501d07040c0003058840c010800c0c85440d50240c000c40d29840c4104110302c000780031095600c004051140c50502c0d6440d00341d1410a0580c0d014402c840011480702008100c0f00c00581c6e000d0200390042c0455403074034005480c240d01c0b001d40080c2c1140a4043c0001c2094401c0180780721030100b0040c0c2d005400d6491621001400b5140003c900c030b02003907800100d641c100001d0303455503400003c0025a10742c685800c501d008000240c400c40d1540100400480821005a0303007a0089100b961a4006076211910082c1110207900580038150000c0c04004036641d01c40b0f00b40c3c0c582131440b0036188240840000030070440c2c003c1f190001e40190504a0005070742521000305031049580050503c000d80e5070301d08001c0588076214000742275070f02203485e55440c548107101c445d41c4001c081c00c05100e41101d000e141f503c2d50300300360302032162042507260511804070a4059141c12005c01e070f5220040e14240320000c2c017080e442c0b070000c42c01802a0803000414030310 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 553328660 1250 553327410 553327417
    0xf070806030a050d23030c04030f14010207030e01020d021501170106050409140d0c0206040b1813050106030614031c120204120c0512060705030a0b0402120105090f0106051e 76
    0x14820211484854401005011039844c882100102c140b08040d68040b4034605c2c049034425444107501911b4035045980c3e100e49561640000e44103002446905d884c1010244020f01415010b40c48548200b04d02100081c42c0c801400020021900104182503032000c6c6030301d600d41980c443c2800142c85215040348580103029a500499100703080030300b040184040c1030394050070214084d080c1d0300c40d000b881c88151644803495500030b401c0b08007088208a40c0a0080142c00400c00c190720000207401d012001640b410710010540d000d00303030b681c0e00402040c0c0d058801c2c034000307101c014942d2180314242d500080d120b14134030002c807051300e060100f1810380030321450110141407140f2a0464a560301c0b00c44025000c0300b408400c403603d01181a0100e51450b01c40d54010480c079102000301810f1b034a40200f01d0383c2e0342000d0491840d150f01c0e052506c1141c2d031540040c00300c2c005082014072180d0b25080801c0101000a4013803043c041c202c030010720159a1080c110740c1f00071440030f5541072410301e85489400520 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 553329910 1250 553328660 553328663
    0x80f1f180b0103020a0e070e1011061905060f0609101806080901112d043803041a0903040312051314030c0f0d080705071d0f070806030a 60
    0x5012210000c10081d01d001d000d03050741e0081d1450107403a40c540a28925048090343c441002c102141000d081d586408003420034109080d00d060004d410140c0c00307491601e0304c00c0d0794030500e41c00b8034240c0c282120340e10b100d06544040c08680c3c4034661f0b81d0ba01c000c01d0f07451141e440054051060200042911070040d004162450800016410329030b079140c9000703048080603900780310355500340440d40c8801c912a10035036088401041c640c10041c0c1c05441140203032800d10082e40c01e4840140800122005000c3e03828144070316100600072186070310450001500129100310752014414403d01001c1049160106040d03e00c144040383c540d00e402c03c03420b15601440d44010450041440310140c1d032540100906403242c601e07140d4168484e00c400c110f0740022216841d10350558060400041c4a117040c03114200071407800b400d0032803080e80c980c9039600207501420007550b840d0310102c002c000900c0f511207a01d4242d8000400100141056040111070078005460442000340001c04500c440c0c0c3c0600041c01d445 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 553331160 1250 553329910 553329941
    0x9020415080303040605090a1101111005010b0a080c46050702030c03120a14070c08010605090c0906070303050901021b0c0f030105040c0515070c061206080f1f 70
    0x40c0e686140e001da4981c0110350440e0000d040c02c02041400b14005019030140d540318500c0316824500100444810341c11030718800481c80b07030032601c05100d41d10303210702e50280020301083c65035225134100141000c4d00284c403010301441c080140b0210101e403a010b59840e041d510184000c20043d007544100402e41d2541410410340c8460101c00c8884d030048010107500340b098055407181c4054208068681030b07001901d94020808101003881c1910400b40800c036108d1410b000c60901c051030300d45444042c1e0b9a0040c00907a9511072080c400340c03510f04c11540d030000504144501e07052405000c600680142600107003032544440c0403d48184d420740580795a191030084c0d049002c400007a18980c0e1b8080415100e01900388041200c0c991300f030602425100310740011845d00e41c0740c540b60510902c0700c062012112800c0013400300c0c50000319914010700081c0880e59a407200102e400e004042200c51a90068400364480038900700070b10030205002200a0310705d01c0d20b90310840ca0900e0300300030302000c01e80c40c1000c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 553332410 1250 553331160 553331201
    0x1020703080f03060a0e060117060a03081324140306130203090106090608010216121404080f0606043e070308090f0703171c05250e0f04090204 63
    0xb030040c0340020314031810040300e40c400d4070b0b6074a26503403510700320aa4091b400101c0400040402880204425420910141c4890802552602c610315103810102c0c40506112903600c08111684078000300076035003500003032020000032100101804441910f88440c1300030300301100080450399400d80c06510f840d800c03034040d90341e40340003d4000e00901260143da01424a0205c000c111100c051081c2c03510201030300d800c000c0c0c0c04029180d52002d141e03e0710094080002c900c000c0d44d80f480016000e000280301c1c10005040c10032901080c84d090000c0100210b0085180503862413000315481035544c124020078000e03039081c102c1092022140d4003170303d82884415500003401c40030076900840c540c2c460100341094418010180d00e92688a102c07a20015024001100381001c45600e00c900414400c400c10102803051082004403806494089861000500300274448910b09401c002a1840c0c50400b0703d0100403015039840044c2e0b6040311000c400c2e00641e0380e00c00400031500ca40e444060104140d4120303495 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 553333660 1250 553332410 553332427
    0xb040606050d0609021806010c020609060d0c08040605060319200406080d090515040509070e030d1d010201050c03180c03010e0105071403100509131a0709080c1e0102070308 76
    0x1340000741000c038000c41c249803c804800d903106105901074281655035454540702902007164580115103800d501c4501046110010300462144400040080c0c980355160310309403d11034100c8000504d5140660407212001e418820b40048819403560310980a481010104100801074015805469000b80c940f16020445280c0001d00070954809940d400c1001526481802543c00f05107500508480c0c0901082c4032500d010305d0311903800403581ca840038200c4036072400680340c444100c1b6000003140c0d1500d42e000031490080482e904a0100303000a00590038521035820720786c0710051104404a11001c002c4401500510008100f81d40007002805141c05408200e4001c00c01035400344049201c802d008121908003909a03440b85200e40109510340385403d0602c01102002818416068032890b00e10f000950050b02940c20340710708030110b00b01450002c1004d450103040f40c00800f4180c0c800d0450b015166505202c820340740d0300b048180d010320441200180d2800703003903070001000d05501191550 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 553334910 1250 553333660 553333673
    0x5150402031f030b15010e031002070503071e1103060f27060a060e070207030f0201030f0b1906030513020307050d1a13020102010f0501060f081f032103180b040606050d 74
    0x18014440b417134541501161000c01910004845100d00d078040c3c2018034040c1a83da880d50107407040500500940e85050041c0d540c80304455221107101484103006c0c81c4140a114074400c6010f99844203070020000d90030303c0300b81d6506031032004019981090751400b480900c000c7c6801c1da504050b030090f0848819081c80f41000e07002d0b105030300440c205a9104000211080e10004410048035085001041c0b20742c440d0700110042d041d4030407420049501d449043e445500c0b01408190100119141001d202d810401c0007016541c01034031308259901041c191502503075000c02e0040c00c440c0d040362049910302040c03a142c1a1401101d00c0e40203040d07185402c00050700102541c00131210300c01da0007000850341400100085407400c1c01400c0000304401003031483c1d14091402c25820083c0450b4200031082e4030581c159015040d90400ca03a01390010b2452620788800043c400c0a10b8680d003000e0090105885856000203440c2e18041c21100308200418203101d910f0f480b01001d01400b40009503000150b04040 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 553336160 1250 553334910 553334933
    0x70303020d0c0509060d0b19030501020901020c0a0f170c0301150305060a09171308030c0706110102040e0718031e050610210c050a2705150402031f03 66
    0x10120349040015030300b0030b50720640442c0d0381082d0082c07070703541004042c15140008080010056400c1851440542c41c0f00510810010041d440b410003d6a1807201000080c1420704401740709001d440b41070824800c580050a140c0181c6118181042081c02c4100b40b01d0b1900386803841076605546011400404140c004900f001603e00407812a45982c0311b10266400b26012503030064010740d94601c0181120000d20000c040e03d000aa0024604a4852001a00b964068442c4001c59030100c4400c126840d0483c0c2c00408128440c402141410700d0711f845c080d8142001001d440030050104801520840403502c0600516001600000003d80000c10350401c581c40c3e03501a038043c403c0c100041c0f2040b003111122010b40d240b4460350000d1004104100741683c1d040401111b8410171110003150903161104180d00420009810728207034071030400904030250182c00040a01070801080041c243c61400343c01401c2c071800d46c1c0c0142d403640c640248098000101d0400c1e0000314407400d0000a120524480 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 553337410 1250 553336160 553336177
    0x110309010902030d1b200a0b0301081608070e07050408030711011d01090b03060102010e030310060938040b0a0e04150317070305042c06010305040f0b0903090607030302 74
    0x85502e084e107208002d680402243c10604050143d0106040005010400400d031025410542225000a0100080e128440358015026071100130004102082d8200700c10300108800003c0100890b0a143c0d0907611040c642c00b039180034249560200d2a914800c00486d802007002c1e1040d01c0e03c0b4085480d001201f03080c0903400900184514007106031204010b8204420128141c44000d03455107411050010f5400041501d410341d56500d60713800405109100462041c0d1031900321101786400c119024080e9000d41e04806000642400d441d0390010740250680c461140c00c00d40b10384100c20003400300c0078910894212042d680c0300410200903007a00b280741c00c8400c8800301c605010102002062541009032444041c00e1410f070a0f6421510000860003050f182c0c2c024a8000c0c54640c541c1741070060b01d03881800b0404e2449040030704001d040da41c9045550007020174070707040c400303070a0039212184551031030640907204c40d0480c00480d0300740404000303e8203040703400741120b0740315042814060001c1d00148603 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 553338660 1250 553337410 553337413
    0xf030201091d2e1d01091b031503080c06040c05030102031b070f02030d0f0206071409010e040906051e0c16150b03070f090e0f031b0111030901090203 66
    0x4000c1024202201054416041140e4402c5079582e407424100c40f003400c1811030304024488120b041800c0741d00f088000003400d100540080c0c180e032501c019550107003050388580e000b2442c1c080069035102c1030f00380c21450000c442c07a002c500301d0b50644070000c40c81002c1d0b2004000c2100012054003036100070408030307c101d02070704840e0400740d03544040c1420303888104c0300085031061030410740c0c1120f10048064495640204035062104940740d006c00e1415042418900120300c00280710a0b8640d030420200b68064100d2800d0000d440328110604802d000340c1002ca814040d0007500d410491b291a4448407045402010610860070302e01c0050141c898071010140e4401d900400190315038404004681480c000c09201d040b110010f501e4520910344048002643d1075140da111440340da03000c001a401a022508484c5080ca02e40441c8a0889070380c002d090990360081941c40b0500240841651522400c800403542c000c0207a000d1640100380904081b03400880c04801d01818400552050000030b10940 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 553339910 1250 553338660 553338677
    0x30b0108010f0c02190614070302030615072111070e0610080c0301091815021207170703230c09040608151603090f030e010e060c280c0f030201 63
    0x1608182640c1083ea030440242c0e10080c82c210000c03410b085020803035401002c0014640212000c882003990301642e80c035002030340200a101891420000c103903075000151003400d00d444000e5440030040b0315007118112080110b000740f020000d001d04004a441003650701a1566103403112800f402204040d01d8450242a910000440c030307038014800300d8003c1642c07a0640742903030310300b17801500070704000d8190000b00000c41038004000341140400d074421001005c0301580741c0c0d00c010f01c91107403c00010020001c0003000039543c00400354010301d0315080030603440c02040c00c0c0150400314007030181810000304007100701010803488505002c0900b00c041c078201c4041c40600ea803800c4143d52164198a21224050342d90f01141a0743c506100c231b5000d141d458140800c3c1c4e209513881302d551440d21120242e020803401c102400392076030300a00b054082d94044950a003400312070701e03a0980c0e428926491004c0340d850400004421070320501c090312800e40c000a02106140c07140c40c00c0a42c0344d8548000c90210b80b819 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 553341160 1250 553339910 553339931
    0x70602061032120a060f1407030c020106150e0901060e01051605100c08090f0d140c0c030a1208010e01180b041104090603020901050d080a140c07030b010801 69
    0x8451181c00c94070042c0300214114030880100b03589402d2440b00040360082c032052020356454142d96002d81c034214034081d104801060030080262010852030950051402e03034198110248000340b036030000300600e40028103000c03c42003030303006000940252102060000400410550085542c8004d640513680b00d90340307903a03800080e6620300f50000070b80c2c003146c1e0612451510844007480c8001443c0034900f10f9801c0076080c0b441d8400c659a078005640002c00140030480521030030440e41d8050b44040c0003c11072200100402001c90070045200101c4040c005010080c603a0100310411500307200900f940d00070320f114508041c1807200c000342c6101107100407000082205140146c1412141e001c0e03411005510145064002440d24078120343e0f20942e075004242c8001d900c900500080c044842001070302606600420075424416071207a4031a090400b00a0005403641c0103640004410303060040241240c0442045140a9202d0040322031107490000028840301c04505412102102c00810070394540 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 553342410 1250 553341160 553341181
    0x31209170d1d0a1b0e07030209040c0804050303181002180910030305030a09030201020d1a040e01020f09060705101e05090307031d01050702060c0f150f04060c03020d090507060206 79
    0x50394180741c216044121564045130308800b19455018581c41d00c48503079a16a00c035250a0901900c2c9a00020360100e4051054105445003e940c41c0450a05868500d400e0b6242c65480c030004000140a882c0c001c031030080b606e002c00044051000b0300c0000e640382d61705418100240840100b10380e21800002001c1940350903a190800103484e056610f66207140c3e0707510441303005801070320001c42c115035007040000e445400c50700c40d000e1444c207500c2c2c150196000c94000c03c0280e401417856010164410003200d03011407403200441d02c00b20f9054400c40c2c1c0710101c40c10858108808603201e250450306100c10b0403c0d252054018001c0c21648090811481c0c07290882d4a589020b0190700030046070160003e00d092048884004600120500d00315144c9031040e8040b480b2900700340a000499440440002e0303414905105040c0c40301b80300f16030500e092809400c0244071800c081c0c00035201c19680c901d500c21043c8a5011110903c4c00100b060000101d0341c9030540c1c0c0e4044034810b200c0180540008110401c01c1e = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 553343660 1250 553342410 553342451
    0xc07030801030209040311010c0c031d01051e070b040c030605011202130b22022107090306051b03040818040b030c010e03030d05010b0a1416031209170d 67
    0x10155551240c0380c0c00c41e401d0100c1408054403d5091140c98201b080380401d0900550004601564407001446141d107400f4040e002c0385400400f075000a45025615030741d0010075518440300402000c032018080c84d500390740a1156000246c1384038440d204100500058100540c1102e01c1078038104866070f030314000d04160b03044180c0c0080d4080000138000780121300c0d50300401c8142c0e40003011603803840e1000421400b0303182031707000940c12150081003418036031584007d894014001e4800002903031070107010052001a16005c0105826540c4002c9008040c40003c240140c60503038181c59900d05160174800b2264200da0285081c201d9a07107420289420a4041c0c0d160090015004000e101042030040d14a00e50080c0882d425200c2800400603840982c00780034024501c010385c01d5074441c04194001c1251000101b4000071040c1003004050115020130050070850301b514100c440d0b09640c486260240540590140000200403075191040b040e8100610342c2210026041110383c1a061003804140e4 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 553344910 1250 553343660 553343663
    0x80d050333040203040204060b0c0123010e0c031008061806060f0f0f04020f0d241217130321110d0819050f01031a15061803030711090c07 61
    0x8624030034450042c00d0035005140c1140c8001c0001c100c1079103600528000c0e4000759030003030080e9103d503a100480320700c503a08840030000d01d070f480d20310310b42c1060341d00d040c00b520292001a004100000252900081312107076070203420b030b400648a1307504059800c00d481915007002e0091901602000c1200c81c5001c143c10505d0581c00703848046014005c408100d80002e1140709076030401d408008058070501901c0c01810944040c441c00500c050f0101307980c20305079280d803e03055400d03c469007003400321407042c0031400f0801da4090540c80c0c003240658404e8502c2d0003a440300c5030074200000008801c101c0341e107409121110701c007001a400c1659000003100d808991651845481c0c100328003161b001c5100c0c002e05c96100d542003030812441c916200001c1c0c11118101c0c0c281e1803040780d140043c41081031000c80700c0c500f8204a0180c110030b040002d80d40050f246032200440c03054030b0010b4240401e481d480385640c03801d240103099035190842420a0a1151010440301d80b06008120004109100520a48a215 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 553346160 1250 553344910 553344991
    0x1b15070f1814010c05011415012610051225030c1a040308030c07120f05180a08010204080615030d02060a020901140a03020a030c0206090c011404080d0503 68
    0x1c0c0c1c80d122240c03460001c02514507040241c42e92034100400c0c070900441244490041c280305171860a4000c0c4a0440c124141c02d5040200c00541c0c004688112800a5001002c0d141d804109440b01aa071920780c070700d0b0f0b92026421091070710901441039000714180b0303980400403000d000804010130226410b0581ca000040041c0701c010310900c20000c4051200354131504e6807103d145850b8407902c4502cac4a81084415403074100b0006040c4041001e001e210740001d103654107149880c0c0c1c00f1080060114000e0030382c500140c441b03038001b4078410b9803103030217490081103444003c540c5c0742e0b22902040d454401c11241c0146609180e01c1204007420700140c020030703440f2603901a1103203450b8641228060b50180880504000094070629080c3c80800700a0140340e11640380182d41e001c50460160980d0011504082035401060401a103d4004904800101b07070900c0c050a4000000d4142d038100d0040d500004442c0c03107541400210107401c14015802003c00804485840721002441e0490704255910107400 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 553347410 1250 553346160 553346207
    0x30105010f121b080a0c08010609060b0d020310150509240a11070b0d02030429150301020c0a03030e2109010e04180501020306040f0605151b15070f 65
    0x2c03485140303415403040761560409000c2695034210510b0001541c4040d40c0c40321b200c0c0004c02492401f449003100a001c65141444038038034003000d002050190140680040785c001000882c80518405020013618800b5200080e104546800411581201070258045d58580d0314000e00c00d400c2d0065680004c55410b203030380c07600400c2c1004583d100e242014000d418403515001041c0903800708090020070108110050700c03843d29090004510041e80b10610305d00292451102206001c890059807211145003141c008a003800c2c0882d0080c03260190051450207210a01410907605404c541419002042141c82e0704005d54400b2000030411a079110191004110200c001e5005541232640a040180000782c0c2d03942030f0300c2da0000c0c3c18110000b00e0f5141d60002c20040b03a45404c0c81208101901418100807043c00d24000c192027025003420b080303103504c0c0401c56801c0b080b4190004480e8032402d80c20785010300d0a0101410596a054500402007008005811030321072058200d0520420010614000d = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 553348660 1250 553347410 553347413
    0x3030e0301420825030b160e1e040507050f040f060905100219080c0d0e01120207051005060a080a03090905060904020f1210020f0c070b12040b0c27030105010f12 71
    0x1518680142c0d0b0110b001202000202050b54148007e21540c1c452032001c078070303401e0f4400007089046c11424180c130600c04099940b450302d040e0000c030440281c060b42c0c0081e160715160f5040d24203024501c0c43d421500c00000740400c0b1213007200c0f004001c8407400e07103d826050f0b44480800225888000c0002c0059020403440261010100000c9640318014801d8918080c4804142410711100d440c400340401c00144d4085560f5a01692002c88140004030440c2003801d10b5448540f0740d8200249104403e4945011441c5940c1d5019050b008062002c11145039440602d0003602c18459440340c0147d0625000001d08942090030700917200d035074000e101c1e4108500000401869070000c9036580b80600c210008052100c03114401044016280c40c051900d0742c0d100c03c0100d20f0f00e40b403a0400d40d09041d080c4114544c0d194030207002a0460350005090a450f59000d031050b00c580100603c0100786100552680502c0e5161515040300300c0c000d0b4001d0045a0700d80d449841030707074414891400c0300400103041c00c0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 553349910 1250 553348660 553348693
    0xb0d02150a090504020c0309010206090712080c100617252106021b0c030109110d1401060e1807080c040c1709030912011503030e03014208 61
    0x190301141814403502e0951100085030072604034820045040d400003e03886915078040004951191018001b0120340c0d080007581010941e01030401008003401107015441c1c813009111884480d07404c2036040100315a02c1d980800700c04000303d0140128001c04109020011401105407400e078882801424028608801c000381020100403410090405044140001c2c5080c00104500340c0c00011141500312814803540c103010701d4404c102c0c4241e140941e03000c00645c10b154000300f50203048030f100c013081c0c0a074140218a100f41d5020b0f241e1551802801040a41c0a81106801030744031000201c42502d0302e8aa40341c1d19842c0c3e00640c0d0322079004614202c0b0a18260704264a075840e00c0c9080c07400384102070441c1c0340010041d2042001600003203100c141509014403001d007202c8030311009001116481501150003240780c08064100240b407035511016441c00d4000c2d030a003486403200040d03022200404c0340c42e102448000918100a084003940350f00315061039071010f841c4004081c0030416008421301 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 553351160 1250 553349910 553349917
    0x50108070210061e0b0711040b0a080a0b010e06030d080a1a090a0b0306090604030c0b0606190804060c030e1e150a0b100804230c100207090b0d0215 65
    0x1184280303580ba1000d00c00300d01610340182150072080003e26081da40700304503120300360030440c0200300901003c008581c980c08102540b010983d00001d40511240100d8404805508414098400c40c0301c2c410811480303048407412540c7e07018226500b40c03141c000309078990701060503140000f092400407508030300c585da10405007100f900c1c6000d002c542c051404500b0494041710351401d2541e0f22025034826040510010390322408000240c041031070141d901420007110610040c1030740d82c101d0000f6000c5c0e01c50f0b01c111800110350580c4103030030b0700d0140401009400129000c8800c03504210624203214040e00034071402c1c641800140086014052000d181990f00f0070b1184010300c00c01c50382c045d078514248500d0b4010b001c294400719000b0034980900000c0d42101d155501086001c80c2000003041006034510300260380404206c1c1c1e81041c04100a00e0007094800803640207918051070144203400245020031140905410320010400000300103458844a80c007a41200701c07040310115050320680103 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 553352410 1250 553351160 553351171
    0x71a07022a040c09080118020d06051330140a08060a09051306150b0d02070501060f140301110f190c06110c0f060103050d050d0b090a1407050c07050108 67
    0x81e10340c0c16100e4000503080d610400461004103044250a00401d2401c0c020100c0d008840308060100c00e08650220740b40903021000030303103016a200041003003107a170000030548090700040d920030303d03801e086003000d44401c18030300004100c0c00450105402c01d0042f41e0283e01c80d851094203174149201840183c2d03660000178507403940611902004249036507544511070103a400000c1c0e8a80e50310003441c00a00321007581381108083d40810004000d40c01080d411168503503010100940ca960039858400d0241025400030a49400c0410011803505060b008548010b40304a00a02c1180d503520f00442c600e00c81c1d4401c144000504000c03240400180146824855076940341400340190241c407220102c03803410b180340e4012400000c001c101c040042211340f00615840f005031049500d141c0c0c0342980c4000c6c802d0404144600415903410381e00342c0303901c2103140c850041c00301c41031483e01e89040001400c0c041600c007544441d01010034001c40c4114107884600030703440000c1600b50705203001501c034010000c2c071 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 553353660 1250 553352410 553352473
    0x216051009030501060608010e0112050319030b0d03020609010c0309020a03030e030703080d02130b09011d0613030b0402040e060106080720011a03070b0f030c030406060812071a0702 80
    0x1d002000071001d10520700103151030b40e100b1813a5418114144106030042c1c1c0303d0818220000300700408100084112011031400c0c0010038029100780d001078024285610b40c4641c44a505800e6102f495004140306200b1400f0f00004c00064200200030341c120307405480065003150310182d041c07000900a0540040c21040202194a41640c90b915040d0550110b21003a0042d500891125140203154410038040c2001400b02c80c00c0160410008000c004508803428503100c40d00501d4540b604e8500031a10703240c01d032168000c10b00342c513800d00740c9520805541c01c0340030300d1600d00402c10022000c540c81d4103a80031659201e886484d0001c04503800801d00e5080c680d1030102640700059890b0910503c03281c09000359004040603011010036041c65100e61018034a08070410640c4002e184413005c0725840140c0c00440c81d02c2c1d0b292030804200510303003600505524480c03803e02d02c401c2e0380020082c042e04e80c41516206c00d8418044092100008242c5400c03026a00104902c1e40400600b6a40400f080000c0c0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 553354910 1250 553353660 553353677
    0x603010b03031801140406020d1409150403140601050105120a150e0601080901060b0904180f0b04060b03070e130203010b150c0106140f12161d060102160510 69
    0xc00090559025200d46001c050110152035404e581143c440c1c16034400911038281000d19112010351600348440c21070381082101c08080c001c1c043c24500350741c2c00d9440644100008810a000350b40d25030721074003050360080407442d038180e09080300084060682d00107035219401c1a510850442140303801404480c040d0b070720380c2003d85d2111070640c0c0c0580180303040c890940030380c1002c10000d00b0441c8050100111a414150f05101042c0000d040701d11000d400c1d100000c20100d0f80307990316840c0c800540018814946040c0210034480d6002d1400e019038000d002c104815000a801c0690f901e80c40c1c800c8030003801c40c0e0000120404421404581054005000400e5200c10200024600c0305c03d5a9014281000405c0340384080c0002d10a00018225503010600f80400c000e001810030401c481e00700d0f2060100b0526801900814044a016000d113102040040ca490300c080c00e982c80642c051246e130141c00c41c400921590310024082c0c441c01660003240c802c0c0c5081c102070003e00807100b0464000d101040 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 553356160 1250 553354910 553354931
    0x90e0c060f0f18041508060112080408010203070908070e01150c1e03050307030e0109020f04020a110f0a03030c0305071416020607060b0a1203020304140d0f030e0f04061a03060301 79
    0x2040100f0701c03114030404a0900444003c100320442d10001418400f100500205100044c2c00040c0c2c207045d10710300f1240c40c0e481801e52800c41c402e0300c69500b007400c80b03500202c14064039981144250056441103000d40e0040743e150703412400d01031024071859030514852418188240e003d210400d900a02415914001c07140706800c204550004000440008100000300074203144d06100d112200011407009010018480e0001920549901c0c0024801d0f6400607510500b1070140610070001c149683c02e8034541036110744103688500b0100819004242401c07030807030f01d4034481d10a152150b02c141d22000a0420b501030403c0345034024420545150301001500300c09070352158044c0c12224403e0101040c1802c0c10070500c150705125900108040d050700e016200020b40100c2503030b003913800e022400522003c440340050308012104001600301d60b000c04292040c9544074800b859800802d55102c10214280800d20040324100e10484500341c0200903030407085440000119080b0400a00115809400 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 553357410 1250 553356160 553356187
    0x30a02030d02160609030c1b0302060f032a030a050c16060b1c0605060310050f071101140c0c01110301080304090506040f0e0304180203040c120f1209050307090e0c060f 74
    0x1170205030041034004100204102c034244044176884080d40710035200c140b030340d408a81c040c01020240c4a25100200010310800303044001110f913110005e00da00344003050040c40b01459030054032142c50320784c2482c00240070416a40300b01e45083c001d0103d920549070040c4c031660018640ca1421580c0400301070080341f044840210300b1030009014103000140b07801c0c0801007515000002202039085e60901c0200325415070a106a0783c1d0040b1203081c0a4214510445007a004081c0c00308140d212042c52001d2101011905004e00b1005405100820441c0e00030401c20b0701c41d010074402c92805500c100814842540b41e60070140e00300700c01800c0485c8100c0c1504141c000d540c11070340c0000325a88040b804105001e4030020400c00c03010758072011807031800d054031110011240350096903840b4500401c1300b001c2010002517010401d03004640c6451074080411300402402891050504c644150395000c501b041107881032405540000008144024201c4184480c0b43c00003070304a61540c1062007030983c820382 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 553358660 1250 553357410 553357421
    0x607020d0b15042406080405011404060b1002060105100c030302090a03031115061305060325050f1c1101051c02042c01030321060e0603060702030a02030d021606 71
    0x95035460714500c000092000301e130801095500c0310009008030883d50010016000c0568030382e840e009030580d03100e042007405440441c4000384260589000c10061260703a13404840e03407000840c2c0d13950341c038002000c04a0780c5110a001c0c0d10303445841c001039880c01030300072619000f03ca4800d060141c00c210703007000004e50b03034802c5030701c00d034086041d00c01700220507070090081078080d0300700c154540640d041c03020214a070f4282400c4071411080d540d6020525945d802c00008811204620900b1511580d81d580051200444e104080c01007a00129181d081d10300300e0010020301514082040c0c0f80d9200c1d07292112039811290f40f25040c080200440c800001780784050411555031b810f00942d4440c0740860f00a04000100a04080903051500c40c03004e640e6442c2107a030440c0d07010b11340414130320300d511507808107401250203000c1005c0c42d028000039640110a191031203054120182c404030f44d54114182e0b1203116a00c82440160010440301101c4040e9038003401d8800748006280b0600d07911641c03031408450 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 553359910 1250 553358660 553358671
    0xc0609080705070e01080c0409020a0b130906051c060c0908070609060801060305090312062106040203060702150f0702070f0602010b101412060f0303160b0a18020607020d0b 76
    0x5400200501886000c2000000070080c20f0b444c40c00390b62410304004d40b503810000045100e585c072000700c2c0301035669400b400c0010b403510700400c0b0f41d02c0e080c1c004094010fa22910441620b80d04211380000d0b90b1030007145040c05002000c100e5001b052035030b80d07005c0041403420b035000c05000d5284804a00d00a04210110103050952229502d072400d116003d001042e0591254040500b841c0820a12520100170f589511007603200e0060952101c90010b50004e080c07010030903a050703640030401c0300c0304000204940218000c1c2d00781c0c1c1c01a02c4a2034100e03101c20340314a90100301580c001c08a0044000c00325000e80c041c9952054590b19501c030748141101c000c1c0c9a0003180140e459201517802c80c039020f1080034103c0c40c1400c00700ca000b0704440d030301e02130b9009854143d907100d08000000b86154803900420400303030b0402000c0d00e0781c46126070244c590548190300181e03400603003880012030301542c0c0d101d03d0441d10701501c084450390b0746036803c1100c030340e2108a080f60000000b8004200266200c0031301c50094 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 553361160 1250 553359910 553359923
    0xc04021c0207120201051f150314092410030b09070911040302040c080907090b01031b021c080f04080d0f09060b010e0303130b07170301060804170307020706030c0c0609 74
    0x561610f00007402c2d00c2010705948210558805d0319011500f03400b1200e41100c0c13034100301401c1e00300000700650003484008458400c01045e00c003000184400032030000607013401d24a100c001d040030003850247c5c0c50070890342c000b030b0b84030008014000300c2c84851415034401e03081012910000c0e1926565030076a0880001c2da4079201001c502802186030034000d1401d50441413600d1000c070314050340c03c07a5503100ea6220b00d1044031f0b070f1901044a1a4840d410001c80f4540d40050000b100210b400000d654907000481030202140307050400f9203440c4074084150090180c0c1902d01010f44403078840030020390020741108182e07903484441e5065038003d0700a03000c9881c002d83c00001e649131900700250080c400c80b1031051282e00100141058040c28542507000d40c0e903030307620558884103e840e007032030b800111000b1062000b9000c400044ca41d503008000314412485400c00e10001d10700100710301242e0005980c42005a00000c4e42800074a101ea40024115001d42c6040042d00744141c5602048402d13580c41034a03403 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 553362410 1250 553361160 553361183
    0x60f040e01050a0b16021c1e0b060a120b0a1d0a0605060f3609010e12160b0604060918020913030c11060d05011401030b0306090c04021c0207 62
    0x154503100640c1d83c014201e04c0546841d040000c043c240c0100102d21009100318201140713100c0c1c1c6d18034450809840c43c1d11400c2c0e0740711580b1480c00a180880280022a0016004400102e42e070030042d40784000c94071220200e42840156580b2030401ca44d00521102c1c0301a903405154084950040903001c1c0c03c100000a0004c03800e96007095000d940b001840280584072807a5800c82a49640800705540043d506e103103840e240e8421030444000490310b40e403c0b1840741107000e22001c01c0e019400f04520200d43c0c400c503080c01c80709150300310690050340e804040009842031001c0120b500214042d50140300100006419520b408a10048500c090784601d1181c203007952580460801c4451140c001803074012000c0d60041595009000c41d26210000380300075008900c0c03004588418003a140f0768580040c05002c10368440408002c2000e81600d00d40c0000e081200404207410003044035801024030001074011081c01d40c05120207940090746410002d001c080d010b50b210714452010709002ca200b503070100c10 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 553363660 1250 553362410 553362419
    0x4020a030b01090503030f040e1b070c0f14060315041d010207020a050a03022b05071203021c08130c0504140712060510140c06090c1014030103060902060f040e01 71
    0x6800b083c1d0f00100e020f0340c000c01501e42141440342c1540c3c00c50b110007503070303000d40d99903421a144112060b200c659103c40c00458520100500c5600c4642500d240008441c04203550310f54015292000b41401600040308001144090b2101204084000e101901c0801d44007201c180c844c407142070040030040a030b5030100d0243c0851401c400c40360010700c2e045484105450554000076188008010010026407601c0c40491000b0b1103400c00320007140d000000d1b2503165075200344120840c07059800440060041d54814610307080000e150006840a0756a49034256450100c00a041c00c80d050701a60341a025100c002265038407801003142d83c003016040c2e840c0c0390038042e8020740b04151070f01e103115805040000511a644924489801a50551034070801014505e01c072401c0c40d103e0300b00c00d80000d010762030400816a80010b1400c18522082e1159000c0082c0030004807483d00c03840c407400580200030401000400c03155080b1500050000b00040c0c0303003562400040701d10344d00c10303406051108800c400410 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 553364910 1250 553363660 553363667
    0x17010608011508190203040203070902071a0a0e071502191a1803030f0a061d09120702030606090601140a0906020d090e1807081009210219060b04020a030b01 69
    0x10000b202c141000301441c10b1200d030949441080c2c0007040e40340c3c0d40c04000142555420080400185841c810445d80d5a145042646070000c0030742d52041811a494045504a101c501c1042c0e0303650107820240c44001c0c02d0000350821480210540e030114480d0b41c03441040e40982c480c600e801e551191010014501d00960001500320303004200b9a40d882c103118180c11000d00101c200e81c0c0c000360501d8a0301c81503840d085404024003058000d0800e480c2d0350300780c8049000304810458040c07100c5000311403140c03050784c0c00501c1c14480d1520081d00754001c500810024101502040d81144c0c050501c205441e814009107013460300400881c078002000000e081106a0301031080040c5070b52a0714006c110036061084a442e645000b6001d030051100e403810040348d402c414050744000d0002e200955000c0702c100c0d82c00c040942040502601c0500c0b000c1c1d05046110a1400b51b0813a402c1c403034000c2c01031302480c0030064580d42c5095809036426922440c031940f040da02d07840207001c1d0200303546001461404040006 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 553366160 1250 553364910 553364939
    0x40b0d090c0b0306130b0a0f080c0a0504230429070f050a1b02010e0303031e09030301121203020c2d0714060a1e09330804031701060801 60
    0x40b210080c0c00c100b4819184c680c2c0d01420303030041001702c021070758a42c20008254051565400081040030101c0045000d61000c02c030400120402c41d500b6a43d661a0700c10401202c09248a102480ba45420300a41c141c90091a059200340074800300d40c0c51050400104040d4098601240720030b00080c000c10480039000040d414030000c0030f2a04504040625102404440e136044448104003018800c0704216072088141550b80540038055035201d0402c1480c089403415401035020520413004002142c8000000030340e0304848a2040c2d012414100340c442210124040149004042d0200244081c11804004a03210426a5406400d8104100d29120304038100c0c00200c003000d800900040040304060381c018800781c0000c03504c0301d80d6003d1040d41900e000096114075050300780c650f0841c050240c3c0001c0703640111280400c11000074410a0480f00009001d140210300128290601c110328620612402d64898440c0c18a074604a41c050300d460784100c000da120b040040c842900601001060a40c50f = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 553367410 1250 553366160 553366169
    0x60403081e07050a06050408070501090501020306120c0a06080c130803030402040b010516080c03070c080a030e0a0f03061517011e0c0e040923071d010b030a090503040b0d090c 77
    0x105092103440d83d1000d8492140c41030151103940c9502c042014441003104907815250b1240081010b02503510700745010f90000c4031054031030100608989010400420244030405008004071059801d19900b600c10301009400715040c0e01d0184003502e10f00d104100742c50041c001c40340042d922446e003881040306035455a401c5c02e04000d0b050169540012100004910469000c2c2485864501442c0e14078a140034100e4007601c00410940002400e51010414142090195a41e0058929a101403002d441180e1150781100d010b081d00810102d05a40e015404203d40141c40649041ea68481001e500d8407500c4400c02d0b50b5524002c40018005860505503140754001007030200b20700444020340f00902e10714030075004a0711040b200c8100889081000f0030300c02540311078403040b411000c02d42d5030b0782d038280100c40100c1030022240d2599108006032038101c0d44c04059051030b40e511f08141d0b001130f10038004106c0d0303540320a20022030103800241c00752900342e801c2c40000075085881d003403a02110746940d10 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 553368660 1250 553367410 553367467
    0x607200616030c020112060608010e090102030403021b0a0f0605030a1a0d0204050c070501150f140904030309050c03061f05061206060a020f070b0406030509013806040308 75
    0x41601c07140d04801c6801c21268150800240c05009400180c0702004103030900c010f4149440008501a9040f15041d0b0503514070020345c00c15544c0b018001c4c1e00301c1c8403c3e2800b801680c00021112884210700911240e01c1c40d000c0e00140d0826520300301c07000403400c0c81d00310320702149000c010058400d01c2032050260000790068080a2000100c0110325500903540019008030713150800210700701c080780d080311025640308001700416030720342800c0c0714060418018400c503403400d0b440020b0715042c144955854000c0081030b0f00e14036101ca5030154000c5c0b594030011222030203001e000c6c0710659410301205215403a404204028115040c0c040e100103444c580101d441000c0c01d01940c541d8200c040c0c4000d40c007180680720596240c00300142a071402030000d4402840b032003482d01c003142c5074464002810882e600747c0c500b4801c6448001c60207081c1d0700008036120400c5e8944c22051500e84004500b0380c0303d502e01c82001c140450b010404110349500039041558040c0c000201d500f5150601d02030450720341d41303404 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 553369910 1250 553368660 553368667
    0x4350a0e040b0d11010e0619030204030312200703030e0601090f0b01020105152107090b040c0305070c290907030516060c06020a0e04240b09010c14010b06072006 71
    0x1038842c1100340313600341402d040209081020416880341d83c2203841d0302c2c0041825243d00c8205c000010701a5101d0300044000413049107181da0f00c5ca40300d0061910001f4401c0700b8400e0001810122841604407110540c20181c0703460404040d0102481110701a000c11103002c9a40b140e107041580c10b0318404045141160301d404100300c0b025000203100782e00f4000480d81502d00034540d58244442010501c80003a080c019940d0010b80500194048440c00e04103880a108548900d1400d800310360007200d03000081882c1c1801d5900003500c401e050491240712140841c2c4409108694044248040311030500540c08000c007803040c01020440b0352500f4120b090b10328035441c20318000030310840c180c0340000e16454022850b800300c14090082c0c2084100301600412505010f8202032401389500340d01e0a01c201c600c40d00100d0040c54100032504c072000c0603118418403d02c156182459203450300c807140e010355078640188070643e071210010218640111100044144c0400500c210a4028080d8030322410040 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 553371160 1250 553369910 553369913
    0x5090c0910140d05010b03060c18040b011707180e18030f041707050607030e0901060923030a02150a080f04020f040c1709010204080105090604350a0e040b0d 69
    0x2241440001e415584550743c24002e241060242141d00c3c405a4075001d41810494500b100b0009081c2038000322603030850420008042c4021a913038150828005911510082c3c00104c880b43c80c3ca800c00d08500e4400615007801085c001000c034160040b6040c1642c0500340800105981d150224042822014625002c3c11250300c12080c03040380b10340d442c541080103c003586818184003503002024040c1c103c0b0390741c1c525403800920766180800c42e40d00c07801c0410b0000c640284503510950544e616504850816035442c250340c42c0240c2ca40b0070203075240c41070203524001601e0788031900b900501101c0400f5154202080c024040f171200610400580821400300805a51550410400303171005460018442d0b0714014121200ca4000042000152007a0284440b80d041580140101ca00300c400030403840d03c46a294036200d40c41594080d00c5100c00b541c2a074180310380c00e10540100240040180b2019122507c58201c58000c0c00440c0702140010032200c503581060300542060700c0e03040b00c2001088105 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 553372410 1250 553371160 553371179
    0x50f030c091b0415030516030c020c060705072103080f0f18100627022a071805010323060403120e0709061d19050c090405090c0910 58
    0x1031103105405040105242000150003c941c003800f1114095004075a40d8000540075190a403288000382e110fa12900608610130721503400d008610754060004446850100b01c0e0341d40202400b170b1880d000b124000125400300942c410dc000c2e41910f49480c41c80c1050034007418120005100d8222034a424040007482e14100e1030385540075107181400303014588010441841e040c040c40c11409464501103010034000c0340007000c11020880c82c7e01c5100031b03007100b41d10707101a409140d41080d40ca085c020990941c4400c00e0300800c016400d1101220b0300c0541d95060000141c0d40c0c2403101e031070550b5590042c001c2c890400c1a420b0000b0110300c244c00802443d0140e942e4a02c001040581000502254951185c0700ca800c4000d90500300c02c11200007640350601d407401000c00e03115421750045110700307081d40000c2c00381046101d04841081654070516201d0001c0180c00c0040c104000e001007041241101c0e0784a21410780103004000040a03c1005102400045100907000c0d05e0310b80120b110800c00800c0 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 553373660 1250 553372410 553372429
    0xf090617060403020309010f05070516180b220e0a0c1401090b0a1805120105090c030606060f0c030409090f0c050915010e0a12080310051807050306190807050f030c 72
    0x2003807234000c4404e50b44001c01c03590341c01080f4008285014540c0b00c5810404040c0e101030135541003020f0030315414201004501124601140352f07400804845801580365070542044407030392140900440d04582c0c8030103803030801c0340301c00d41128030900c06181441028903003981c000500c007080c207240303070f0540c10004003405502503407104604120142407950400c1c106560030100030040a004a145580a607100b280641400c0b54070250f50310440314014031078540010400d000310300140815280a0320000c40303035441d5200010703040041c48100700010b9002c820307100e902c51041c003c081000861400b4604801d0303510255008920031000c1c142441002040340158051705402400d0074070004c01d0381e07804504006450390089070541352042c50441401801402503100b6110034094101042d202c0c000c0007407900054007004e4a0001c810001042c050140d0020b582001d0010403980c0000b0341c01c000b034100308100f600300b084141c0151000b004241070803031040500440440140c01d0642c4800b01050304034a = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 553374910 1250 553373660 553373677
    0xd210605150306030a08032d0f06131103070e012718140403021c090305071a131502010b0405010b070803040305070b0a0b01091d0601030e070f0906170604030203 71
    0x1c80000414207568082001c0d402599100765036035101d1401141d040d0002c0183c5081d07003144030341e440541c8035404202c15800d1141441c0c81da1b01d11951610402c0c403400291940b840710f241a40d82c00c00040d40485800694480d12840c0e48800c48250700c040010414941502c0000e4410940880560504545070800003541c022560b000200c10400715000c02401401c10306d00d0907010150140024158089010054040750070540c420b111b8002d00101e41a001d103110241094000c0e03401404074036032039019450b81510300d6035424140250006081c15840c0254003620101d035848022100854081c082d0321b5100404460030031180d85003031101c40c414811000d0040802078008005410940110292440c1c99004211400c41340f4010b690580280701600c1c04a010642c04240001d40040b0044800c0c03406000404001c070300d44500d40150003800a140500609000d44000450b90030a0007140c40b0092a000002041d00c0386442030001418ad0048441003031a040301003040046a000401c84000700c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 553376160 1250 553374910 553374949
    0x50901080a0e030d090602040906150c0b060d050f012007080f070302031e0d05250e0a1e0f0b07240212040501090b0603010b0102070b0309010e0d210605 67
    0xb055824412401c41c0725085880580c1c602d0059428203109032507000e0b0040d20707140300703040000b19200c402c081400c460341241b40001801090350400020342007111a070304034002800c0b50b050390070b00341c2d503040c02c2001181445807039030340d10360f000c1410013030032102104050140207140b498072681e5103560445100d149190441d02e140040c02c0c00030180f003041200d143c0074812107080c104160b5240c40f00e0b42980600c4c1c500150600744400f1034061644400d4a90b01041003411155940020f010181c8081c91640c100690001071600002a03260721103000220290004046103045400d2003104800080150040c5160322020b002c0d60000806000c100410745c400c52010140001c0002c80c110068481d1502620240000100748010000150441e03480c8500c0b4030a059807036900d8a051500700c55041c4130190041e4410b036004c000c60040c0c40002c41d08042c2c00000418590001c000d0240b4207120b0f1040c01d0b0001c0c90040108500c01001c05843c081e918041340c0900001c1c4c035110000344800c80d0f00e4a00e5500 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 553377410 1250 553376160 553376171
    0xf06121e150213270e030f130806060405010609120212061e010f0f031e06021605100e06070c0204110a0809060c0f030601051b070b0405040f050402030a0b06032b0f050901080a 77
    0x117101d41007096030310903224441265a60f01018019802400d0103105100c400d10524000c03a100740303801d00416060b200941e65100c0054507000c4100209103c0319002c4e40c202c01c82c0910107590480c18005148075003404a52600030207030030002ca4400b2801680f005100340079030760040c01000c40402035901180c2d0804d041d2a9420f50400010b16901580e9400400d803070710016104200d40c0035120320485640c0140d098440b0300384c0015816082ea0300c43d4001121903000200005c00190041d450301c1081c40c0050400103d41c940e0040c030b07201951040b40040701103280c01c0f0801448081c10401160300c4945910090305210848140c01c000d03001c050041070502c940400c096a14010024103806000c0103070040b42c50300366840c00e0750300c01c0741e10a0290740d020314244100011003031254094a070190303034042c000385402d94082d121071002d070708043d047c240e05004801c14650b00d8400d03541d19551203180500120100c0307100703000180c8000d040020300424410280604400c0340c1c0c111002da941300030002c802042 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 553378660 1250 553377410 553377431
    0x90b3c040602130816030b0a15060f030b0603250c0807031d060307080a0b0102010b0904061802031501061704260d1409010f06121e15021327 62
    0x5846529030022200c0c1c3c42031784c0c02c10b90611701e00104241106d00076008030102e82c0f5621854429950410b030744010a04650f042001114803a0101d4100c0e0910303440c0002d041e80e8080002039103a031040e109100390403000d8540030122000d0070f070300501c2e61550f403c1c071604441c2c03103658241260040540150501030080c10511014000c9007100509450081a10b1b9a91400c01009016500700b070301d4800e4560f1814242e10000c0d401440384c40706602c0c004007510302a66840da507c6000c0c241241168440d15400080030740141c0342007044950b00c200b200c01c8000303d036041c101d000f041c2107600781a00500003602c6091001184004410340c00d8000c01d01a6000c000001c80e12845c003074410080c0c100c2465180082c0100e14a090501090044071030400a000003805160110180c0d42d060280010804900300460000348118000320780000d800c24440007400b02c0c60312100c0108680c000e900030003c2c0c0009015502d42c0381d10180601400140440f00a00308402502180c60100c2010100c1090b560780310744070 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 553379910 1250 553378660 553378687
    0x1e021b0d0917030918040606050307050102070b1b0304030f05060f060609040203071806090315020c15070c0501110301061b030e010c080d060303182103050904090b3c040602 76
    0x18402507000c3c050403007400c003c4281817481d01088805403900c03807602c0b00c00b090a281c0841c950302180c0d0168018200e26050000400456000e405a04240b0002d0701c24400b0040c418009480154000c0c0b81030704914015040c024140300005103074074130030340120042212640da60400d4800402042e079006031250303944042038400d440030124140c1d0802400c8000140b0a80c4409200d0560748a210301d694500810b01c03150b01030313000d1802900460381150403c203201d40d17506d1007402d60114070b92034000c09110594070350740c2c01c640c441101035420982c000014050300742c00a001900310301080240c980d9606054800070300c0005440d480307d04004c0b6007230030202400000c07010b03141038150304a020410356960f80342c0a02403401320741c031442601b43c4001c0c00148400c2103000440d0060004400010b441c07120341d504849c0c0b980500a0a68016038607a4000e000c40c098590a40c41078207420342c07004000c20080301409080d01c01c041e4010085203040001030390819080280d6400a600100c0580c032900a5016203 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 553381160 1250 553379910 553379917
    0x315050a02070f0b07030e060606070222020309010632010f0c0203030c070614041a0304020a0e07020d0905040204050a031401021b010b010e040902100807031e021b0d091703 76
    0x50200c8101180d8035040c031055034802030085c41a134804210b441c8000c41010f0321410110784084d403089083c0b051b240542003130f80c02141722455441510b00308000680001c01281c20664080549030355450050000c800004503010000c1081311210704505284602d100382c080b1051440f41c1000202c03002d2100c01400780f080d0b20307201680101925102c00404c41a190398400600c503c40001d1000516001ca42c0024000c480c1561840502d00b2114081e4442d1070540b0341c0082c00803a0040100e44000070340040340060f150043c5002c0d80580030055044100070641d00301500468401c601c100420000740e51081d070600112075000c0e0140700a0311a100c2041e009000b010341804180c80042e9441c9544501035000340b000041c2600d80000c444849003c1c842240d07510310001390020024803031010501c0c096044941d01001d0351030701051442c239420384045600c0641c0c000348815a0003143c2005000f82260402d114100c94030001c003920825280001c107108000e100d511143c9016104007100307840c0c284100d = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 553382410 1250 553381160 553381163
    0x601170d1112040b071112030d09031707080910022b02120907300f02040b0a080f0f03160f031101090b04050c030a11060a17042303040315050a0207 65
    0x4540c03125915000048645d0041070110351808041c0454000f51034104407040e0540c2d4440011030414000407401001081807407015403e101c111041e0403914516080030034450304081d500c43c106401d05228861030100e68040d8140345500503c00721001007e071a802c41c44500c41362801c0341d100c104440c00c601c024821116540c118035400c00403c490f0080025460045030014800f544c2e60500000d01401c1082041c000365200401c1d51400c000801c5200c501c1d03209060005000040e42e29814000805203221a44840c032146c10040c803182c2201c0b01404a845e41c0305800c409545032090079120050007202144c8020018174428402505152060f8440282c00350072600800c5215400d05000074100412101100e4522828240004a003400320b0030a03a415401445000c10242440c2003203419005034018504201380a2440c0000800a580450055020300400460300214001c26101411048005001035108000400c0001e6000d40f514008200c8200000360740c1e118410380030040d202e160300 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 553383660 1250 553382410 553382443
    0x307032003070503090706020f0c010f030e150601020d05070b012903010f1716060305060609041803081609030f080405031c0e102a0f0c05030601170d11 67
    0x8005010b0f070028000e6004070050002c07650721540e10380040740d40d1075120740702c0300280d0461100844294056100e081c1e52041509010801010041c100d51511590030707405038240e4030710010701070701d940c0510003141410324600d400d0f850100f260b01c1e00440c008042c819007a40e280212041c010042c0720200402c110b0050502899a82d40e541c03800c940740ca44507004003041c014884114403840c0c04001f0300b80024541c03c42c004019640b401c9410b80c010f102c002c040c0c51300074100308044c142e20340e141d224002446c01e01c030b003800301c03c0c903860f0600074000200103003001c051064007c90380000fa500300c25030200300d80c0e0028a0044000042c504040c1c0b901a9500c02e82d0140b042084060356850034103001301540c0c04954440c0e84000c640b0781006403142c40b444544022030f4032050850200041411070300b8007040807141448508403580c3d07411440e100449010385081c4030f0b0190130701840c541807050900500740081c40928501d0440ca4140e242d00404c4030400a11207c2c00203d00d5102091040c102524071403003 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 553384910 1250 553383660 553383667
    0x30f180506131b0e01050a0f06080a09050c03030705100b150d02090109150c05010c0e06071704050d0305030f0606031b07020d1707051606020d080903070f06060608090109020603070320 81
    0x1001d4a451396000c1c019244200000c1201298441840f11000c0454409a607807000c552104600e0780700410804000391103600642001e0b8549890800050103460f2044e0003c1c070201084d49842c81c221104420000d11403808180d039550490b04403c25980c042400040043c0d0b40c1e4900c80041e20b2140c0305a10002141c0d80407502c440055401815104205000d00f009101299000d801103850b501c40c20740195101009016640c003203140700e00c0240d002d081c0107600502d411384400000748003d01028085000420000402010121120301c03190800c9007914401c0c250704003070300100154401da00070703851503c4000c6854400d569a43c08510003481e04150441d030174202c000701149455200c020b054440f8801e000900d0009952035500c08202c40307183e4040c06041c5501c400c200c42480e80501140c91501c414049100850a022145030207180b10300c2000410b1460300c003000e882d81c200102a80510b0340360000c01d601503200d0030200c07907201d07605140005000c40322442001da13681110010319860540030 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 553386160 1250 553384910 553384919
    0x130b010608130b07030506090a060f180f0212091b210309090103080d06050a0f0308030c222d05060912100b0306090619020a030e0d030f180506131b 65
    0x146e0005002d07020682d0240e0342d90307039241150700a40e4024840c041380030075210000c228811540001c4005009188000f142aa03034060000050b80c0103a000010106c0d681d0040c400102420000042e41500103990041c0c8003105800041d0043d40c014501020030f204440020383c4100103104884d01c1141c024115000f650b140e09200c0c4181e0840102652014079000000c60705281c03541000b004c4644806e02c1c44071003030560740c480741590809881801521414062003022140c3d40d00700c0c2482001d0418120a080d290200c180e041c10030700c1d842c00300050440d00030207070300c914000382e10b9043d1001561040e03607501081e4003059074103100d02040665409080602200f01a0581045148030011800c4070007540710400e0460b00c60f0f4055030808100581900700909035201d54029200200b01c9060000701c44808038806410103031492041d9000940d1807540b000c540e922845203558410080e5400c00035500180c1d035030f0340c0c0c17150301500914400c0304403880b0404200c08041103000040c420844d10b05003644d00c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 553387410 1250 553386160 553386167
    0x714010e030d0c0618080d020903030c1c080c04080d030c020309030109061a01020c010c0308070e130c080f0705091201090c0b130501020303040f0f03110d050a08130b010608130b07 79
    0x168100c41440c1000c0344442c010f05c1d060001c08202c0c1d008034840745004c03508080e100082d44001c1c46140c1500091015000c40c030024005039544e4000c0003000000f0788101c480051074420003c3c81903116840078481841403140001e54040001c919084c00220480c40c1c22041e4914003801c095681e041d800d200003042002444d4002c0401410a2402c8001c1c4030420b400590311000010307a00d41c0065501940003010074420318005410200b5418044e612403660f4020076082c01117114461045600d409c4180115540120580e40c46041728060100f00d01308204001d00b40d1146108840c811400d040d80c0c440b1252080d03100004107030b4403117440c4103165540c5c8010100303a0440c83c0203403404154540e0006855001008a0384201e9205051642074044c6545825001b000030303d041d020407030710103003816940108100d211001488d039112251078210445000300149001002003606d1440c080001002a0b854185c890550b003050600820603614400001c0c905030981c403001c1c214a1411060007829500b = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 553388660 1250 553387410 553387427
    0x40e1324090203011103010501020607081003060501030305030708070e060d09050c04020c011b1803080a1106180f160306050903070609030905011407020a14031e2d0714010e030d 78
    0xc03e4000f0b00c0019464407440c400340c003003441410301580201000851961207026159408014000100005a01c98590300200c642c01d80044020607000000d105846400c600c00031360003100d07840c00c0400074191001062160141c0040e00f000d075503e580f10f910420406004028881030080d00442d252060b003020103000c1c0140c0d8100d101540c0b010000215090b200710300c0950a0034980e415074010610f955030b40505584066251020010310412035002560207004030360085c0560400040481d0b038032215075042c009201a494001d034005180c15908904621482080303030340100b00000c00f80d640d50150340c294821108018003a82ca00000c0c04d04042e0800f84060135160280d072007208055440d80b4817052032084003006580800e00c40d00c1000654a0007150010010000c0c0641d822040d41c0491f241060380c240c814a00366402c14401d054a424540c0c95100703107184c4100d2010080a81c1440f416180d03000d174012040440200c1c04070f03a5191b4010081d00c0c1102501404580130040038007001000c008 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 553389910 1250 553388660 553388663
    0x1110301030b16020318150d150609060c1407030506010303020304080d03062603040b070507030515060a030611040e0a0e011b1b0c0909030f14040e132409 68
    0x1e52400803d9402e10070315408249000c5540003949000c43d000349000c406c1e0004000c40e9406400714110001c1084090040c201c1c007111540e02082d8003034828031481d506405c58110100b04408558200704696214050749803542e0800d80d03441028500c030b0421400d010650f04060700a104810001013003540c00001001243c0d0114150b1300070303011400c1d04609603442d900c00c0080c40403906981c02444c00b403000c1040d5807070106c0e0045a00e0b00740d07110002d5045070454001601c0b0b54201c00c80c10418410284001c0031020018401c940c218030b003200000b000c103481303800f010f0901c0b9910b0480c16803400c01d8030201d402600401000ca003052030200c00d00006070083c0903030b0070580e500b4040ca8400b1084029200c0760070611a03190091107035482004007900c64240042940c805419440c00500c28081d8410044024000e5443c9409126030302c03030241c0b075910542d0006110200402c002c002500007020001d80001e0010203a06d920420ba040c5103a9a0361544070310700d4420a0520040c80ca40c0c40d960010180701e = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 553391160 1250 553389910 553389923
    0xf020307031b080d08010905100f060c110306061c1a04060207050c0f150f0910050a080c0c06070e010c06050f190501031101050703020703050d050a0818120a110111030103 75
    0x3076031142d100c56204e82541c2044070216081750014000041740d40c02481d0300101c0c01d6482d16509940c0e03101c000c40d000103a405000440c6060072a0002e0008a2903620a04078080d0010115400d0039030200c0c2c0460514072400360352441d4040c0040401034030040981030340112100e1240c880c1001d05241c4001c1d84a00b0007101c0360310801100c1070b51410f20101160350702c503008001d0300c41d85002001901c4140c0c00380740d402c480000101301081d20780d40d8443e03140d08400260340d00c1c84c3c3c03103c0ea07900300074020101c0a408650004010300c050b181d40b40340020070507408055890f0491804860800594850790000801811141403008004a5211341c4c41ca0383c3c8902d5209000709080c6564110100071134800780070203094140040c19005055004800a1820034428411a500340341d99417203c90400b0140e00c0b21100107080050200c02c420362144c411034004c41e1003400c0e0154140318110301565011082c0e050f15183c5808122000081d00490001021040c1d100081c040e02c6030084003200c59174000d010444a0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 553392410 1250 553391160 553391213
    0xe01032306040203060402091f032a030c120305070614040b07050f07110a08060411010e060408100b04060801110d1d07060c0606091a030f03160209040f02030703 71
    0x46a50020710580a00c0d0064050502d0391075a40a2007511540102800e00154080c2002c02c4800c0c0181c484070700443c00303004c440300007040c1c54850030040030b003580d2508242088004140042480205030808482c9030078410304a182480c5402d5515000c0c03001c002e0f00881c6000c0c0d080300d02003110384000e4419840380300310150541e140d602c01e4880380200d00301400b00750380034060500058025034003608104001400f40d00c120380c0d140402880c00c0c2d000c43c0c0840700062508050006540c116861240d02a0b0460f8001d08180c00d0122140e50351030700e0340c40b000001d52512901c10751510f0f03075440705001e841d20100074818154031444080300d560201401c1e5240c54a0310800c813402480521800070000e61240c084c204e00c80c40c0680c1201c800f845400e01340d40e12a944c060004409541c1e00c951100e0301d03484c604c1d0740d043c41c1c9480c0405003888810300c94041a6002006440200080e04402e40700042d411204000c00d600c3c1d6040040c1c0101302030b400250107101e00e507408000d000b18030604803282c4034403d503003811 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 553393660 1250 553392410 553392473
    0x302061c0b0d120816140306060910021b060a0512131b14151902010e0d0903031719020a11010203040302010605150a0804030807021005070f021b0303030606130e0103 73
    0xe150f03090381103080006e00184126605101204011600304400400c3c85040c000e8490020b024100071124100240c0e0004011094410003034858005000084460300d08200140001038168455a60040326208040c00042c01340038003030031384003240758100c03500309540c00354001402c607210b5081c000c144c40c50745038400c1c110141c41c0580c0610b0483e204055464104180070512400c041c80000e4824195520740040c0c46d40b0035010010280c0c00c01182c0d031620540c900c0d5040240010f200060314540c0c625032002006075030140e00e64808503007046040300580c3c40c008690100c0d0002c903a85071000c190350001007800141941500300d10240c610842d900140c20f0107180c2c840350ba91082c52900703400b1030401000140443e0198184990000c0a4015150b111304407000395011101c04940c038401040c69800c0510718580d040240d0840c4c0744201c824000c840701c5090000c1c2d80c0f40001010b4610810f80000c1203052483c02920020041c01c00401d03007c802e503128a803011145046441240d81c5001c00b070307034026 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 553394910 1250 553393660 553393681
    0x7021203070f26090c092205030d0e1b030d020a112e081e0a1802041e15060903080a02160803040519140f060c070909021305010302061c0b0d1208 64
    0x18020304001f00710040e140490602d00c68215610032041d580d90102780003024020606000d01203410003032002400d02c8581b030307420403071034409100c0c001e90190340700743c62070b518841d000540c0c50560398000505118200300400080c9140e0040000d00c0b2100c100c070340e8003180c40c02e100d030a84a0140081e4581d0040ca40d107121240034042c1c5002c0703d410203801c40c1c0d8003140241c0c0302944240b1950395150080b10a12849070042010780b441004a000c040c1d1440c4d075840c0d0f41e82410310580a080120141d1100d0040c41c210004145900c0c501001d801410005001604503000704881d08103034884249038040c1030340d03500301151203400c14401d00d40900124440d107e62156008000010754143c0b100b25105454500103110341d0007282c031070b8503410603410000600302c01c500f045000300505007110003041c518404e105025046000c40f01c000b132503908000061006070354880555014800d00d54821500c0c01508140102904000c080300b45c011031440321420900c0f8165000043d50354050305c032403003543c55440400 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 553396160 1250 553394910 553394929
    0xf01050c0703090605090406260c0103060f0311060d05180f0a170c120c0a020f090405030a0c0606091b081e0106030c2a0b07021203070f26090c 63
    0x2000643c81640500c0310700c3c050800762501c080301503c000703036041d121001e8411883ca600e1408110002401c03030558200c0003007000c0102c1c84000c0c42d0a1001c545840c50300c0d03c2e00c20840c0070003030041d14250b9000ca07a54542d6410f03903003c0d5014820501660400e0301d6404072052041188010f84d0046020041c182500020200c40250b0300c4440480f041c4910380881896801501590440740030305c41c188402403e0b5100074108044407a405010000040d2041250b5a030940c606c0030300504800d81004041103020090320750742034003410030180c0700726107103040710041803903130032400c1203d11780144d544152601049000058041b0b80700d12465449a84050348111021580003454011070001400752034403070f4010031454070560401075020a1007040c80c0f0b408569611440c04403056540070b8030306100a0455041e003081440c00130780f1782c940c8008004105440001c4c0723110144603c1c40b02403d0b0651140b10300c800c640300d07081e118040725820300a03a1440141c00751035994141c1319890900002c1d00d40082d54 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 553397410 1250 553396160 553396163
    0x3070c0b032a070b190c0e0f01170105010f11060a02041a07020306010b160b0f100b0a090b0310030b07080405060121150626061608060909030405030a050f01050c07 72
    0x560341490080e07540e51103000700c0140004c140800083d40486503110b01d000c1c80300c06c1e11598840c09032090b02c03007040c8104021204d04241c104100141074152a0a01c0f40310b09056880a1038000e4860b51030b404141e80e02c1345581c44030b2107540300e130104002c4800080d50244c025a480c650114840f80c000601d0400d040c0600d007000b81d450380200c80100718000d1940010f1004968131300020807007960a0b01c60790a02c1c41d0884030000440c80700c1e0100036113a40501c039070001512841c0380080c01c0c07a02d040801081d100c0a4041c08550140006c0031400100c408a0514029070b8440d00039003942c600444020401801910121528840c0000204100c2c030b45100091031440000c080c48403030b1100e0703180e8488180b21210104003070342da01c45010440d0025030440c003c2e020410445440c40c0b0400d030040314035181c0014001111144126800e0b004180d1101c0303250f800444c221007541054840e1202c4074194459507004c01d5052203003c5403c010841c000ca100f01070004500003c0010755150a1a04014883c8080 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 553398660 1250 553397410 553397491
    0x6130e010b07080a031e230703020f04060e010c060e0c0405010b0c030a03020d06050901080703031706090c0c07080303010906030c21020909070b0703030501080616090b0c03070c0b03 80
    0xd0034110a1083e80402290b21001c4600c180448442c00030400307c881d840c22041c1c1d14045080b40045404143c03c910b50000d00c146011460310488900385070160151780503401c100f2601a5000c0c2c0140c1c0708503500d12080381c00c0b9500300304403003481014603030707400c9402c01c100e003c2c504001c000945500e0880c180c43d292210355000e14542902c13800214000d6026000c419403c50fa01e2030301040a0b00d0b0741c1314042c00303006c15500400b2242d042d81009001425a82c1c1210120f86400c020032455444851490350846102d100c62619000000c46030b034100070302d0b07030401511403101000016411419070025800c80740505140f1091603220102c09103081c44003141070001000603983c5d0001410040f030340c41e130f00a84c0d5000b80c9900c01d4568030303209050740c804074041d0002034a23080140701a2b40140005900801c1040c8170010700e4400b03c0011348041b10502c034011000300b002c81c010340840400c0c0125001e140d44804140100c5442d03404101403600143c517640c000740710642c00002d50b603403002d0503034005400719032 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 553399910 1250 553398660 553398667
    0xa030e0c0d0209270601030c170c0d290a0f0f020903060f04020a15031d0a050c040c020304050411040807062105060d06090f03030b03032703070506130e010b0708 71
    0x802d40c4010130700c003503042c0c048074954411481881d00b40305650107103200d8031001e0007807417038110f200041030f0f1050300300c065170342002c00040300c185d0303d902e00f84d0300c0c55030f00402c043c1100d24001100030301560f4040c103181203590700c8401c118080900e644208a02d03a00003500300a8040c00400c2c54049009905010344c16074000c50100d00c9907014400880d900030310040c4501c1184e510707094042c00203840b011601020030b0f1560b030b50095418880801503c003000032001840d020003e501c60b079030748442c220100d6006a81e103c40f076517400c40c0b00b8402c4a0291070701400500818520707018200307456210b0310030155180a5814045240382c421100e4003140725100e18400050842d40320710000419010b881e84d40d2105014404a0009015000f520355543c06001c030341d207042c2200e06002c1d0944090710032291017508100019a0040354504141a03031030070004c00b00055410003c0824900b000a07006550b015401283e03101c000300480c800c50b001c0d1078444d51801a940d9907202d6000103409a2180100980e4051 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 553401160 1250 553399910 553399921
    0x11b0c030e0f151903060b070305120a0b030706050c010606110a06020a0e04050c030604050601050a0c1119081f02070f06020a0c230606030606030c1c080a030e0c0d0209 74
    0x4540b00b0344180040064003082c01c1c1100509255200303043c0162110041c800201e081c1c1d40610519005083c10030b042450803501d0740d001400c40c030071b045901031920328000100d601c08042d42d0004200c940050100c1c1c004a4403203001030429003040c54030088035800c080020404c1071150050b15a00c1801b00020300114450f171f0381e5200039401400c03445080108945101e00203917a05d018141c0101c4500d0292a07507810311000b40401d0b208014803107410700c41c2c10000b070310b101c0d030703000d0415a0110b1b000010215000400320004180c041401e4140490b2101a500841c511230081509012100c14918400084010454000c140c1c000c0c540c0181c540c640508003500814010740081150007024506105008615541c0004501030310300c2954003c890111038900100c0208925908401e003100208103925080d0700003a41c5240b680a002d01606545420480482090540900d920340c0010039548400b01408000d008141d8140c10f0380c1c1911415030407514501b4001410004550050300141259544 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 553402410 1250 553401160 553401169
    0x12020f0d030f2111071101090303080615070203120c071208030a1e0c05041502070b07140304030b0405060a140906010e220807020f0a0b040302040527011b0c030e 71
    0xc45400a403420280c030700031103e10580c0e1040325036100d840e055594540b41c06042020117010a0325155040c0000040c0030700120340c000350282d92010040342e0380318140c402200003d000740107101000350984036115800186103982005003542c000054200c03480155148040f030f03030700603440c54050302c1c55104001060707015509410008410840f42520701c4080343c1480080704990800488030300240c07011500380000080d200303030b0510000c80c51005029450401308100340c144a1244000c1810740e2952002034500030a105540042d0340128250783e0a26090521948034036040b19224040f034942030100703080d8404e580b100c40c020480e9400030705c4a0307800c000116000e02c40c0544482103a85000051440c80c004510200e13000502c0b9060040d2140190b205114021850301c00492080c40e1210080c042142c0d24000c0d2011179804450108030768503068079446203294801120440e182da01c4210b11a80f840c150030a0103036040d088810999049100e40031941ca124802c07008000400466407440d2a240 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 553403660 1250 553402410 553402427
    0x9021b0d0509150c0a1a0a0b0f19030b01030b091006060c14070b0d0911030106051e06040e090a050c0405070906030e030c0313140301020a0c0201030f0e0712020f0d030f 74
    0x2110411a240030b00141130503191030708417201104c0c840940c03401d003543c00948010f250f0f00070b9000322050145081f0080000c01d89503c503900d540c0501111980c80400901ca020365000070b54200d400340540d541c6070b06001c041c041c0210340d28840c1e80320301c1750000c4200f000e5101e60003c8071fa140da03e141c0081141c0c1d64200c2c5420940088584510441c1004512010141c008000c0036103042c000060400d000c0c54200c218880d0003140900c20707450084108030649450000314084030f0f01c5a224098512003100049483c05190000e42c41c405800f0304216162400160051005001e881101c00e00e003075010401c020740e6812a0110002001c410382000482d00a800c04003501c501c2c2001d40e800c100805107a14510340050300d0048411503c40c800b0008500e82e1641c0101c8420160000e40c0303846074070400075004102e41c4000a0406948042c104400a15070340866410800c0c0c50a40b440165200c25018820401e22810b0b403107102c6140d0245007525060703022580341079040d2609080703418a03030400d6607940c6 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 553404910 1250 553403660 553403689
    0x5010e011211040b07060e0c18041a15180c0d021308031204031107030b010b09060706090b01050f04090f0f05030d050f101715090a0b0109021b0d0509 66
    0x40d1541e0002c0b52104120000d040074107040310f5211385512881c14840c1c103a9a41d5a25003440d6040102c1c250415140c030b007524206022030b003503598119200d41c6401b1098800c0c1aaa001c1080c0f6a541842482501c41919a0200d041145c3c0b40c108030280000ba048a0102560903402030501000301044c040b015401800041141a4440c10791070354640c5450f045500c5489000d40c0e001a8404220400d90000be4020184908100070f001c1d1901f10b550b00406040103004007200c9280100303003070a031076880600715410580e102c0d005200200740c0e880d0000c0d01c06c00078016140b107910708402c07403141e9003054803540070150b40007a070740041c10020791503414107041001401c3d19a800100068408425140030359405030100d2943c1c00d40616202c4c001043e101c0d00354100014200c0088030109480c000000e00104420100e100c103e00c94996402c5140307408002c020041280b03030b109000143d00c9201e54081d1400d60184405066140303050b003882d41d12074000508041c080340092120480c24144050311234403d8 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 553406160 1250 553404910 553404947
    0x2120a1113090207021002030c0c13061d4804030b131505042001230d0b030f070303230313030228030e03100c1211030105010e01 57
    0x2040806002414a41290b40e040c2d400103410030841c1012412050522440c0c0701946c28903407003200d420389950f03040048501c50155004010606101170348004010f00342c0e91044000c01d8919102060012011581c80014425008607480c2040d00186902ca0f940c10401100040c01041c6170700e2050851202820820a170040c840403000900440025006a0700c00300307644403100403442c0a1007502410a030304601a0f0401e42844009203c0c582c01d00080c6400181440f455201c07100121610a0381e98160742404e41491a1710200e0800603000340700d409241030381030002c0d41c10074090540d1014400450b8500d507108420401c0030134824603076440e8501a402c103c0003070414002400c92903803c1516882040142c5408010070180c0401c4105184c0c0c4040c0d807080d17a41c19212450016102c0091380c040e06100c00c6140b805807664080c054084d08503070310801040940c9280000409540b658613200351481d107001000b00d2040c02210a5904a8a059481e070046004050044036a5a4550030082d00b0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 553407410 1250 553406160 553406167
    0x40911040e041407080d0801030803060315131704061403090a050106090c020610050f01050c0c060a0c140a050709020f090904060209041113061407061e050106020102120a11 76
    0x32901090040ca00850180e580c0c02480c0f02000306580c00c241c82c0f980030076250b60103042117121180e081410907044036000500036859640381c030301090900640003031540500301c1c10f4080049225050f4402d17035889000750089905401b00c003070284031500c500c0c010000800d1200710050b5030103964200071640028010706072036002038541d81e0582035500036080001101c6c1c4a524810f03049070b0400000713a02a0030070000a0350f491420020503d042c7e0841612410400c00044005180200708901044400068078584d928222843c008140c0d050000c0308644005450110b0f0200c0f11b00010188000343d0000054440186040700a0b00254002c0c00d01410901c410701c4060708a0b40c81c8032003144224025180540d880040608100031100d802c2400039010070140412001e90103410525015100c01d4200000345048202000c00c1034043c80b04003c0441d824001c50354440341c8c41c4c10590781c00900c0751074288060390300e030442a4240d0044084400b003a0504030005060005036410142d0009203401d141d524 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 553408660 1250 553407410 553407419
    0x109030f0614060603041a220506070801060c330c030f05060303120a15050d14190302060f06060423120109080711030102160311060105040b0604091104 67
    0x5054004140584003590340740386070000c9440640e08641d100f0030032180c0b2403440c42e066803252441081c040140904480041c0083c000004000e160450380d094400c01602d440014602241d0319241160701c28005074010000181550090032003244c89513120014a0280d11011503400014070141420030103a8801500c1500f18102446451100031050781d0100701444041100015110042e00701c078042e5000300010000d031010140d025410820f603180200d140741151000c4150000160000b541c000d09000c2414100312401100102d0200740201791800c1c0d161414a04a619611980140160b00120300180c400c903440001d4990010780200218145070300c60794500c14000e01183c0720600c0c42e800b68001041c1e0b01d007200e20704210340807080c0284040740046d56000e16a0041c59002400800080d680340c0d1250f40a4041d42e0005131450881500480c080c103004045219103100346155006031000450760b401c0a0140d84880c04000c1c01d0a0301d41031038110f46c14028500e8003189030704000d00348000705 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 553409910 1250 553408660 553408673
    0x90a0207050102190807090e060105122e090f020301120f06110c0a1b080c0907090e15011205090d05070213090f031701150e010c0c06031b02030f0d0b010903 69
    0x4c404000a60711042da901d00b9900c003a004d25002d4010704030107001e0400308581c0d681d1000c1182c43e00d000d01c141284983d1108a0b544c50540c10401483c01003070040c0880546400e4060f0549084460300c880c24007124500e0300d00e8004a100a00802d1104440002d140001c5180102601078280c07080034005107890003c10209200e411a25250425030008011807017805241588480800f4114200d00000341c680018166584214400540514500000070300c519020780d000800500f095000d00140d07103402c80341c07180b18998601030300b40841e401c6102100001154440c2e03500c114884402007480f0b14681c1011307100707600b265400b2607202409003480d07050160030707000f400d000621411350b41031421254940a02840040c2d501224448074903801084406a444a0003042d8000303403c1884540d103d0a00480301c10700702100c044c10100d070409000441d240d05903c180070b4001e61844420541d2160f50080340c407485000d80c0121003100c01c0c040480707c0052075012800345036050401c192015a44da40b00d4 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 553411160 1250 553409910 553409947
    0x308160b0a0605101716020a1a2e21081b1c020604030c061d161703090909010b03100212010608060105030f180316110906090a0207050102 61
    0x100c940c10b460b20750401040c200505038403402c41c800d007000c1c142c1007080410620001401032080c08122a803407200c03130103a4000e01c82a84265004640d0804000e41c00e001c07400c2d54001078030045021910800e000380c1d1280100040c030a50440400300f000b8903440c1c48172104a0015004540d20034251115450001032911401040030244428529007000294180075003040900500414465000c92803403000c5940800d5030f0f5449580b6081092400550b81400c00007010081703540540000c4250b140e18140b00f000441003614a807202503003d00d1501d940300304904040381c0710000c100c1d50007403103000d10341d02e04540d009500104140001604034200b02c0040d00d050401d000e0b60785901c0e8006801c46214603088070306409400f15090110f081d082082c002071182c407008001c0d400c02d2242e0030100c0d90520203400c000209a0710442104d4450404c402800000d08843e6000c880c1007061242c1040f0710305004000324812800280708401c0e940d5081d00e020003941c0324040840c0d00355402c01190302d0510b0b2850b1017 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 553412410 1250 553411160 553411171
    0x20319080a06090905030f16060c1107050a06020c01200604080a030e16030b04031e0f0207080601060c0f051006030803090c030a0b0a0c110a06051605040308040308160b 74
    0x88405604204007184100c40d402d03081645a60308181119011503000401c0f180b000c403040f0070142c0e44e4207030702e200e0080d06411004012318050038120041c5a040c0e10200c0420181031500c1a2260381e0303514005c1040d040d03404c2c414140588c10640d6901c0196005800364902d000070b00340d2001d00190100001c90400b101120201c030b20b0b201c0030035a03040701c50f4544148921840c402e0028020160a0f030f91100c0e00141c3c03848001c20790304400c0000b508142c4100c2d040f10210f10641e80240e0b0364208034801a1182c1408009000144a0b151000542810000f50103040700c51310340719200344180070740b28011054503540702600e052003030081c0314080ca6121312400000718001c503481c613101d06010103442c3c00c248105031024440ea201c550b607400841d074400c0c9680c0d08403000090000723400071417001c25039001e00540c2114041e409880030f22820701050b44c021078818440c8250038050501d5046090715640141d0002902440c010b110600004800c07070001e1803042801a800c0c00551030030798a191801400310350 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 553413660 1250 553412410 553412417
    0x302040507030c0f0306141e043315080702160e1602030c06010b0d060b040e070305182d0a0c03030f170402090a0605191401081e07020319 61
    0x1181c00383c640c00310b004002442070780b0701030100390310f01100051400d58080e01d05100303540100c401e9180d6502e0b503201d16880c043c082c00c02c4c44500507401030700341d240a031101c4800e0043d0325814a002000b03409404002a20500310340214030022041088458500c0281070605520542100a0507801151034040080940a0b0001140c0c0350541182850b414a00b1080d42507500500c0802e00703583c800b090380b0381500d9441031540d44880640f14103502801281d03101c00741d0998001004a140242d0310000e40c4124403544050040da11940d00610000096503111100380d00400c00c26114141c00f42d09514100b000056002c0b8407034001b00c1c1140c2841400c5c0701c205d8104c01142020000c04d41c02c40080000302c140782c1084001051707640001c81c800480104006c1c0700b803400000148580010740d000c0006410007a00d034003603a01c08410b00b00300c070039080d00500702d142c007000071024020343c4107107001d42c840c041c1c0302c03980b0111820400317032858640c0011300f07032109501040c0b10000903104481020240210590b4 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 553414910 1250 553413660 553413671
    0xa05010e15071b0510020d091707020901140d0b010611071e030314120408070c0f270e03030702011e0b0d020105130e1e0f090613020a030204050703 65
    0x8500c0c1c40c102020700c03000c1d1440441c20810804941000030300c1815000162500102c0b640340c5807103800c184441d03281000291001c5403813205640705a001541440c4582a15220707160005201c440e10301031044021340c000c15400061040d01c0d890511300200420140442506800756600d850000c54260005000100a225400c0166500300b229200600c0707440c0e5420104002100b8010031000c250002a0501c0504452010071102d4501281e84500c1c0c5071502c031400d803d2501c4c050081c2d5200302d038255010003408101081456002d041e1000300c1c0e65203400c0745160443c84488500508100c1c06030551507a50352901100c80000740020b5201e4400d640c000a50b4801c0203818810f02e29aa503610480c007490017456078025155108042c02d480e40900307000c0d403210300f02806814107030301d640c20034441c803150074040c4070400d50643d5402c050724000012202403540d401c04544085a0101d07100a26640310001240645901082c2d400940d40054860541541c41e500458140e810a50380200021340d2103 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 553416160 1250 553414910 553414931
    0xf180d080a031a011b02061c050403020f0102090105040324090b18013c020a0302070b06010e15031e190e120a050d0207050a050a060606050c0327030a0501 68
    0x40c4249150340c1c0660f4400e000c80e100b0040000c001c4100e102800100a900d00c0040302075541d52801d640100a15000351000d000e4540649005444251381c00c03405032240030070f803601100c01030080d62800380040c1e59150900345952180c0902c1c451694662082c101c65400b06000000f850196030741c3d84d8040c0344d02000c00d0400400c1004000c10f108044540c0d40d240c10b114a08038607540e044100010350101001c50f0740c1064051515444440a0100d555144002800054107400d42c0283c190140142025003040e501c000040d0740614005402075441031069031020500f8555074051a00614012594103111019034405d440c048819a030f0010300e044101c55030384903080c16014120007209400080c06c4d810510401110304c0c0d01400204c0000d110300440c1c1c06a1000465056a208540010841c0c5d0070024505000f626080040e4080d0740c1181421008140c0c40c1c010030071102a21114402980351091110006c0f260b41e104824807400c1014030108816555020003070b18403042c2c0641c1c00000c3e80b130f030ba2 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 553417266 1106 553416160 553416167
    0x3091a060a0f03020112150e0117011416120b04060e0907051f05031f030615090b010c081c0e10050604111801200304051507080f180d080a 61
    0x249000011602902d00031003401402b01c2000b00400003100318030080356402245c0440b04a1900142d9010035441180d084905c8665100d00080c00150317000010265826503101520a0300e922050141c00b000900c95407008140444502000e21050030070860b07094880307014901403180101c00513244107400440c03510f2a41001c40701241e007644903e480002840c614a50920310a004400450075a0051040c2c850209058485040c5c188403907403140d080d41d008800d62026800c0207012020403e506005041100140501402907801508050f404540d0005d04c0031344901e042c061400707148a9440111049102c90820b52995650000f00690307038804802c0c0307198003901c0d50b4484107010800100191080c1d40c422a2400b420213145154010580a52440580031810070068155081e1000e00244404490b8a804001c0c20203144000f482d19244008141c0d1b6910000518440310f907030 = true := by decide +kernel

theorem cover : BRFrame.Cov 553237410 553417266 := by
  have h0 := BRFrame.cov_init 553237410
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553237410 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553237410 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553237410 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553237410 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553237410 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553237410 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553237410 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553237410 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553237410 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553237410 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553237410 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553237410 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553237410 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553237410 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553237410 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553237410 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553237410 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553237410 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553237410 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553237410 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553237410 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553237410 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553237410 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553237410 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553237410 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553237410 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553237410 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553237410 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553237410 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553237410 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553237410 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553237410 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553237410 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553237410 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553237410 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553237410 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553237410 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553237410 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553237410 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553237410 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553237410 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553237410 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553237410 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553237410 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553237410 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553237410 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553237410 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553237410 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553237410 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553237410 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553237410 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553237410 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553237410 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553237410 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553237410 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553237410 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553237410 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553237410 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553237410 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553237410 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553237410 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553237410 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553237410 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553237410 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553237410 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553237410 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553237410 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553237410 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553237410 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553237410 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553237410 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553237410 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553237410 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553237410 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553237410 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553237410 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553237410 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553237410 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553237410 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553237410 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553237410 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553237410 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553237410 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553237410 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553237410 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553237410 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553237410 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553237410 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553237410 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553237410 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553237410 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553237410 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553237410 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553237410 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553237410 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553237410 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553237410 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553237410 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553237410 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553237410 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553237410 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553237410 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553237410 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553237410 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553237410 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553237410 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553237410 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553237410 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553237410 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553237410 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553237410 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553237410 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553237410 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553237410 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553237410 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553237410 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553237410 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553237410 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553237410 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553237410 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553237410 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553237410 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553237410 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553237410 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553237410 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553237410 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553237410 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553237410 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553237410 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553237410 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553237410 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553237410 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553237410 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553237410 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553237410 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553237410 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553237410 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553237410 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553237410 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553237410 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553237410 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553237410 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553237410 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 553237410 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 553237410 ≤ n) (h2 : n < 553417266) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
